/-
  `CircuitDiagram` — the CIRCUIT functor: an arrow of an allegory, as it is ELABORATED, to the
  layout tree `diag/cpanel.typ` draws.

  IT IS A FUNCTOR, NOT A TRANSCRIPTION.  The source is the arrow's `Expr`; the target is a
  `cpanel` tree.  `≫` goes to `seq` concatenation, the relational product to `stack`, so the tree
  of a composite is the composite of the trees, and every clause below is one operator.  Nothing
  here reads a formula string, a signature table or the note: the source and target OBJECT of every
  subterm is `Meta.inferType` of it, and the WIRE COUNT of an object is its own product structure —
  which is why the Python generator's `circuit-sigs.json` has no counterpart here.

  THE MONOIDAL READING (`diag/CIRCUIT-GEN.md` §2-3).  A wire is an object, a box a morphism,
  composition runs left to right, and a product is TWO WIRES — never one wire labelled `A×B`.  A
  coproduct is the one object that stays ONE wire at a port: the tape fork is what opens it, and
  each arm's `open` generator splits or ends that wire according to its summand.

  WHERE THE WIRES COME FROM.  An object's strands are read off its CARRIER TYPE, unfolded by the
  elaborator: `⟨A × List A⟩` is two wires, `⟨Unit⟩` is none, and `⟨Unit ⊕ A × List A⟩` — a pattern
  functor at a carrier — is one wire at a port and the summand's two inside a tape.  No table
  states any of that; `whnf` does.
-/
import Lean
-- `StrDiag.split` and the rest of the elaborated-term reader: one copy of a question every picture
-- functor asks — what relation a statement states, and what its two sides are.
import diag.tool.ExprReader
-- The note's spelling of a term, shared with the string and commutative pictures.
import diag.tool.Label
import AOP.A10_1
import AOP.A7_7_MSS
import AOP.A7_7_Filter
import AOP.A5_6_ListCombinators

open Lean

namespace Freyd.CircuitDiagram

/-! ### Typst values

The tree is emitted as Typst dictionaries, the exact shape `cpanel` reads.  One value type, so the
emitter is one function and a node that forgets a field cannot typecheck. -/

inductive Val where
  | s (v : String)
  | n (v : Nat)
  | b (v : Bool)
  | nul
  | arr (xs : Array Val)
  | dict (kvs : Array (String × Val))
  deriving Inhabited

/-- Typst string literal: only `\` and `"` can end it early. -/
def tstr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

partial def Val.render : Val → String
  | .s v => tstr v
  | .n v => toString v
  | .b v => if v then "true" else "false"
  | .nul => "none"
  -- Trailing comma always: in Typst `(x)` is `x` and only `(x,)` is a one-element array, and a
  -- tree whose one-lane stack collapsed to its lane is a different picture.
  | .arr xs => "(" ++ String.join (xs.toList.map fun x => x.render ++ ", ") ++ ")"
  | .dict kvs =>
    "(" ++ String.intercalate ", " (kvs.toList.map fun (k, v) => k ++ ": " ++ v.render) ++ ")"

/-! ### Objects

An object is its label together with the shape its wires come from.  `opaq` is one wire: a base
type, a list, a power object — anything the note draws as a single strand. -/

inductive OKind where
  | one | prod | sum | opaq
  deriving Inhabited, BEq

/-- How a label JOINS under a functor's name, recorded WHERE THE LABEL IS BUILT — the note's own
    rule, `lshow` in `scripts/circuit`. -/
inductive Join where
  /-- ONE NAME the reader cannot take for a composite (`A`, `𝟏`, `Word`), or a chain of one-letter
      functors on one (`EA`, `FEA`): a ONE-LETTER functor juxtaposes with it -/
  | name
  /-- SELF-DELIMITED by the printer's own brackets (`[A]`): any functor juxtaposes with it -/
  | bracket
  /-- everything else — an application under a longer name (`bag(Job)`), a label written INFIX from
      the parts (`A×[A]`) — and applying an operator to it takes parentheses -/
  | other
  deriving Inhabited, BEq

inductive Obj where
  /-- `join` records, WHERE THE LABEL IS BUILT, how it sets under a functor's name.  Asking the
      finished STRING instead is a guess about the spelling — the kind cannot tell `F[A]` from
      `𝟏+A×[A]`, both `.sum`. -/
  | mk (label : String) (kind : OKind) (parts : Array Obj) (join : Join)
  deriving Inhabited

def Obj.label : Obj → String | .mk l _ _ _ => l
def Obj.kind : Obj → OKind | .mk _ k _ _ => k
def Obj.parts : Obj → Array Obj | .mk _ _ p _ => p
def Obj.join : Obj → Join | .mk _ _ _ j => j

/-- Two objects are the same for seam purposes when they print the same: the label IS what a seam
    would show, so a seam that would repeat its neighbour is exactly one whose label repeats it. -/
def Obj.same (a b : Obj) : Bool := a.label == b.label

/-- The strands a port at this object carries: its ×-factors, none for `𝟏`, and for a coproduct
    the strands of its one non-`𝟏` summand — the note's decision that `𝟏+` is not drawn, so
    `F([A])` at a box is the recursive branch's `A`,`[A]`.  A coproduct with two real summands has
    no port reading at all: only a tape draws it, and the tape says so itself. -/
partial def Obj.wires : Obj → Except String (Array Obj)
  | .mk _ .one _ _ => return #[]
  | .mk _ .prod ps _ => do
    let mut out := #[]
    for p in ps do out := out ++ (← p.wires)
    return out
  | o@(.mk _ .sum ps _) => do
    let ss := ps.filter fun p => p.kind != .one
    -- `𝟏+X` is not drawn, so its port is `X`'s strands.  A coproduct of two REAL summands stays
    -- ONE wire at a port: the tape fork is what opens it, and a port is where none forks.
    if h : ss.size = 1 then (ss[0]'(by omega)).wires else return #[o]
  | o@(.mk _ .opaq _ _) => return #[o]

/-! ### Labels

The label of an object or an arrow is the elaborator's own pretty printer under the repo's
notations, with the namespaces taken off — they carry no information inside a picture of the
repo's own algebra.  The book's own spellings (`cons`, `nil`, `[A]`) are structural readings of
the term, never a table of strings: `cons` is the arrow whose graph is `List.cons`. -/

def plain (e : Expr) : MetaM String := do
  let s := (toString (← Meta.ppExpr e)).replace "«" "" |>.replace "»" ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- How the printer's own spelling of a term JOINS under a functor's name.  The SYNTAX decides, not
    the term: an unexpander is exactly what turns the two-argument `ConsList Unit A` into the single
    token `[A]`, so the term's argument count answers a different question, and the finished string
    answers none.  ONE TOKEN is one name, however long (`A`, `𝟏`, `Word`); a form the printer CLOSED
    IN ITS OWN BRACKETS — first child an atom and last child an atom, which is what a bracket is —
    delimits itself; and an APPLICATION the printer wrote by juxtaposition (`Bag Job`, `list⁺ A`) is
    neither, because juxtaposition is composition and closing a functor's name up against it would
    read as one more factor of a composite. -/
partial def stxJoin : Syntax → Join
  | .ident .. | .atom .. => .name
  | .node _ _ args =>
    match (args[0]? : Option Syntax), (args.back? : Option Syntax) with
    -- A BRACKET IS A TOKEN WITH NO NAME IN IT.  `bag(Job)` and `list⁺(A)` open with an atom and
    -- close with one just as `[A]` does, but their opening token CARRIES THE FUNCTOR'S NAME, so the
    -- next functor's would close up against it (`Ebag(Job)`) and read as two things composed.  The
    -- test is on the token, not on its length: a character a name can be spelled with disqualifies.
    | some (.atom _ o), some (.atom ..) =>
      if o.any fun c => Lean.isIdFirst c || Lean.isIdRest c then .other else .bracket
    | _, _ => .other
  | .missing => .other

/-- An object with no structure of its own: the printer's label, and how that label joins under a
    functor, read off the syntax the printer built it from. -/
def opaqObj (e : Expr) : MetaM Obj :=
  return .mk (← StrDiag.appShow e) .opaq #[] (stxJoin (← PrettyPrinter.delab e))

/-- A functor's action on an OBJECT, by the repo's juxtaposition rule: juxtaposition is composition,
    so APPLYING takes parentheses (`bag(Job)`, `E(A×[A])`, `E(bag(Job))`) — `EA×[A]` would read as the
    product of `EA` with `[A]` and `E bag Job` as three things composed.  Two forms stay closed up: a
    CHAIN OF ONE-LETTER FUNCTORS on one name, which no reader can take for a composite (`EA`, `FEA`,
    `E𝟏`), and an argument the printer ALREADY DELIMITED with its own brackets (`E[A]`, `F[Char]`).

    THE ARGUMENT'S JOIN IS RECORDED WHERE IT WAS BUILT (`Obj.join`), never re-read off its name. -/
def applyLabel (f : String) (a : Obj) : String :=
  if a.join == .bracket || (f.length == 1 && a.join == .name) then f ++ a.label
  else f ++ "(" ++ a.label ++ ")"

/-- The join of what `applyLabel f` builds, which is decided by the label's OWN HEAD and nothing
    else: a one-letter functor heads what it builds, so `E(bag(Job))` juxtaposes under the next one
    exactly as `EA` does (`EF(bag(Job))`), while a longer name heads an application the next functor
    parenthesises. -/
def applyJoin (f : String) (_ : Obj) : Join :=
  if f.length == 1 then .name else .other

/-- A number as the exponent a power is written with. -/
def supNum (n : Nat) : String :=
  String.join ((toString n).toList.map fun c =>
    #["⁰", "¹", "²", "³", "⁴", "⁵", "⁶", "⁷", "⁸", "⁹"][c.toNat - '0'.toNat]!)

/-- The label of a PRODUCT of objects, and how it joins.  `n` EQUAL factors are a POWER (`A²`,
    `E[A]²`): writing one name n times says nothing the exponent does not, and the picture's n
    strands are the same either way.  A power heads with its base's own head, so it juxtaposes
    wherever the base does (`EA²`, `E[A]²`); a genuine `×` heads with nothing and takes brackets. -/
def prodObj (ps : Array Obj) : Obj :=
  match ps[0]? with
  | none => .mk "𝟏" .one #[] .name
  | some p =>
    if ps.size > 1 && ps.all fun q => q.label == p.label then
      .mk (p.label ++ supNum ps.size) .prod ps p.join
    else .mk (String.intercalate "×" (ps.toList.map Obj.label)) .prod ps .other

/-- Whether a CARRIER TYPE has a spelling of its own — the same question `isNamed` asks of an arrow,
    asked of a type, and the one that decides which of the two available names a wire wears.  `List A`
    is read structurally and `ConsList Unit A` has an unexpander setting it in the note's brackets, so
    those name the wire and the object declaring them (`dStr`, `dList A`) does not; `Quot Setoid.r`
    prints under its own constant and names nothing, and there the object the statement declared
    (`Bag Job`) is the only name in the picture. -/
def typeNamed (t : Expr) : MetaM Bool := do
  if let (``List, #[_]) := t.getAppFnArgs then return true
  let some c := t.getAppFn.constName? | return true
  let s ← PrettyPrinter.delab t
  if stxJoin s == .bracket then return true
  let some h := StrDiag.stxHead s | return true
  return h.getString! != c.getString!

mutual

/-- An object of the allegory.  Its NAME is the one the STATEMENT writes and its WIRES come from the
    carrier: `Bag Job` is one atom whose carrier is a quotient, `F.obj A` is `FA` whatever its
    carrier unfolds to, and only a carrier the picture OPENS — a product a fork splits, a coproduct
    a tape opens — overrides the name, those strands needing names of their own.  The power object is
    recognised for the same reason: its carrier is a predicate type, which says nothing. -/
partial def objOf (o : Expr) : MetaM Obj := do
  match o.getAppFnArgs with
  | (``Freyd.Alg.PowerAllegory.powerObj, args) =>
    match args.back? with
    | some b => do let a ← objOf b; return .mk (applyLabel "E" a) .opaq #[] (applyJoin "E" a)
    | none => opaqObj o
  -- A RELATOR APPLIED TO AN OBJECT is named by the relator and its argument — `F(c)`, whatever the
  -- carrier reduces to, and for however many summands.  Counting the carrier's summands answers a
  -- DIFFERENT question and gets `F` wrong wherever the base functor has two real summands
  -- (`F(x)=A+x×x`) or recurses in a slot that is not the last (`F(x)=𝟏+x×A`).
  | (``Freyd.Functor.obj, args) =>
    match StrDiag.lastTwo args with
    | some (f, b) => do
      -- The RELATOR NAMES ITSELF and its type parameters name nothing: `F(list⁺(A))`, never
      -- `TT.F A(list⁺(A))`, because those parameters are the types the wires already carry.
      let n ← do pure ((← StrDiag.relatorName? f).getD (← plain f))
      let (ob, _) ← carrierObj o
      let a ← objOf b
      return .mk (applyLabel n a) ob.kind ob.parts (applyJoin n a)
    | none => opaqObj o
  | _ => do
    let (ob, named) ← carrierObj o
    if ob.kind == .sum then
      -- A coproduct whose functor the statement never names — the carrier `Fobj L E C` written
      -- bare — still has to say `F`, and then the carrier is the factor of the one recursive
      -- summand that recurses.  Two real summands leave nothing to read, and that is a `DIFF`
      -- naming the object rather than a guess.
      let ss := ob.parts.filter fun p => p.kind != .one
      if h : ss.size = 1 then
        let s := ss[0]'(by omega)
        let c := if s.kind == .prod then (s.parts.back?).getD s else s
        return .mk (applyLabel "F" c) .sum ob.parts (applyJoin "F" c)
      return ob
    -- THE STATEMENT NAMED IT: a declared object is ONE atom where its carrier named nothing — a
    -- quotient, a structure, a bare base type is an implementation the picture never shows.  A
    -- carrier WITH a name of its own keeps it, because the note names a wire by its type (`[Char]`,
    -- not the `dStr` that declares it), and `⟨t⟩` declares no name at all.
    if ob.kind == .opaq && !named then
      if let .const n _ := o.getAppFn then
        if n != ``Freyd.Alg.RelSet.mk then return ← opaqObj o
    return ob

/-- The SHAPE an object's wires come from — its carrier, unfolded by the elaborator, and one opaque
    strand for an object it cannot reduce that far (a binder's `A`) — together with whether that
    carrier NAMED the wire (`typeNamed`); an object with no carrier to reduce to is its own name. -/
partial def carrierObj (o : Expr) : MetaM (Obj × Bool) := do
  match (← Meta.whnfD o).getAppFnArgs with
  | (``Freyd.Alg.RelSet.mk, #[t]) => return (← typeObj t, ← typeNamed t)
  | _ => return (← opaqObj o, true)

/-- A carrier TYPE.  `×` is the product of wires, `⊕` the coproduct only a tape opens, `Unit` the
    empty word, and a list its bracketed spelling. -/
partial def typeObj (t : Expr) : MetaM Obj := do
  -- A CARRIER TYPE IS ITS OBJECT, and must be read before `whnfD` for the same reason the power
  -- object is: `(E[A]).carrier` unfolds to a predicate type that says nothing, and then the second
  -- summand of `F(E[A])` no longer matches `∋`'s source, so the fused `𝟙×∋` draws `𝟙×𝟙`.
  if let (``Freyd.Alg.RelSet.carrier, #[o]) := t.getAppFnArgs then return ← objOf o
  -- The DECOMPOSITION is `StrDiag.wiringOf`'s, the one the `⊸` of a label asks too; only the
  -- LABELS are this functor's, so a type read one way here and another way there cannot happen.
  match ← StrDiag.wiringOf t with
  | .prod a b => do
    let (oa, ob) := (← typeObj a, ← typeObj b)
    -- `×` IS ASSOCIATIVE AND ITS FACTORS ARE THE STRANDS, so the parts are kept FLAT: `Obj.wires`
    -- already reads a nested product as one row, and the power below counts that same row.
    let flat (o : Obj) : Array Obj := if o.kind == .prod then o.parts else #[o]
    return prodObj (flat oa ++ flat ob)
  | .sum a b => do
    let (oa, ob) := (← typeObj a, ← typeObj b)
    return .mk (oa.label ++ "+" ++ ob.label) .sum #[oa, ob] .other
  | .one => return .mk "𝟏" .one #[] .name
  | .atom t =>
    match t.getAppFnArgs with
    | (``List, #[a]) => return .mk ("[" ++ (← typeObj a).label ++ "]") .opaq #[] .bracket
    | _ => opaqObj t

end

/-- The source and target objects of an arrow, from its own type. -/
def endsOf (e : Expr) : MetaM (Obj × Obj) := do
  -- NOT `whnf`: it goes past `Cat.Hom` into the instance's own function type and the arrow's two
  -- objects — the whole of what the picture's ports are — are gone.
  let t ← Meta.whnfR (← Meta.inferType e)
  match t.getAppFnArgs with
  | (``Cat.Hom, args) =>
    match args[args.size - 2]?, args[args.size - 1]? with
    | some a, some b => return (← objOf a, ← objOf b)
    | _, _ => throwError "not an arrow: {e}"
  | _ => throwError "not an arrow of a category: {← Meta.ppExpr t}"

/-! ### Arrow labels

Spelled the way the BOOK spells it, and read off the TERM: `est(R)` is the `est` of the note,
`∋` the epsiloff, `cons` the arrow whose graph is `List.cons`, `𝟙` the identity. -/

/-- Whether the arrow has a SPELLING OF ITS OWN: those keep their name and are never unfolded,
    because the name IS what the note writes on the box.  Two ways a constant gets one — a clause
    of `diag/tool/Label.lean`, and an `app_unexpander` beside the declaration that writes it under
    a DIFFERENT name (`thinRel` as `thin`, `editFn` as `edit`), which is the same statement made
    where the constant lives.  Read off the PRINTER: an unexpander that only drops a namespace
    leaves the name alone and says nothing, so it does not count, and a constant given a name of
    its own tomorrow stops being opened without a line being added here. -/
def isNamed (e : Expr) : MetaM Bool := do
  match e.getAppFnArgs.1 with
  | ``Cat.id | ``Freyd.Alg.PowerAllegory.eps | ``Freyd.Alg.est | ``Freyd.Alg.Λ
  | ``Freyd.Alg.cup | ``Freyd.Alg.powerRel
  | ``Freyd.Alg.Allegory.recip | ``Freyd.Alg.RelSet.graph => return true
  | .str _ s =>
    -- NO IDENTIFIER HEAD AT ALL means the printer wrote it under its own NOTATION (`thin(Q)`,
    -- `⦇S⦈`), which is a spelling of its own by the same test: the head it prints is not the
    -- constant's name.  A notation DELIMITS its operand, so the syntax opens with an atom.
    let some h := StrDiag.stxHead (← PrettyPrinter.delab e) | return true
    -- A name of its own is one the DECLARATION chose.  A head that is one of the term's own
    -- BINDERS chose nothing — `F(R)` prints under the relator variable `F`, and that relator is
    -- exactly what has to open for the fork inside it to be drawn — and an unexpander that only
    -- drops a namespace leaves the name alone, so neither counts.
    if ((← getLCtx).findFromUserName? h).isSome then return false
    return h.getString! != s
  | _ => return false

/-- Whether the term is built from an operator this functor draws — the test for unfolding a
    defined arrow: a body that is not one of these is a relation given pointwise, which has no
    circuit inside it. -/
def hasClause (e : Expr) : Bool :=
  match e.getAppFnArgs.1 with
  | ``Cat.comp | ``Cat.id | ``Freyd.Alg.Λ | ``Freyd.Alg.junc | ``Freyd.Alg.relCata
  | ``Freyd.Alg.mu
  | ``Freyd.Alg.Allegory.recip | ``Freyd.Alg.Allegory.inter
  | ``Freyd.Alg.DistributiveAllegory.union | ``Freyd.Alg.RelSet.graph
  | ``Freyd.Alg.RelSet.rprodMap | ``Freyd.Alg.prodMap | ``Freyd.Functor.map => true
  | _ => false

/-! ### The picture

Every clause answers a `Pic`: the tree node, the strands at each port, and whether the arrow is a
map — which is the whole of the chamfer decision (maps compose to maps, `%∋` is always a map). -/

structure Pic where
  val : Val
  ins : Array Obj
  outs : Array Obj
  src : Obj
  tgt : Obj
  isMap : Bool
  deriving Inhabited

def nodeOf (kind : String) (nin nout : Nat) (extra : Array (String × Val)) : Val :=
  .dict (#[("k", .s kind), ("nin", .n nin), ("nout", .n nout)] ++ extra)

def mkPic (kind : String) (ins outs : Array Obj) (src tgt : Obj) (isMap : Bool)
    (extra : Array (String × Val)) : Pic :=
  { val := nodeOf kind ins.size outs.size extra, ins, outs, src, tgt, isMap }

/-- A box spanning the strands its ports carry.  A relation's chamfer says which way it runs; a
    map is a plain rectangle, having only one direction to run in. -/
def boxPic (label : String) (ins outs : Array Obj) (src tgt : Obj) (isMap : Bool)
    (frac flip : Bool := false) : Pic :=
  mkPic "box" ins outs src tgt isMap
    #[("label", .s label), ("chamfer", .b (!isMap)), ("frac", .b frac), ("flip", .b flip)]

/-- The node kind a picture is, for the clauses that ask (a `°` flips a BOX and frames anything
    else; a run splices into the run above it). -/
def Val.kindOf : Val → Option String
  | .dict kvs => kvs.findSome? fun (k, v) =>
      if k == "k" then (match v with | Val.s t => some t | _ => none) else none
  | _ => none

/-- The same node with one field replaced — how a `def` opened for its WIRING keeps its own name,
    and how a box standing before a tape ends on one wire. -/
def Val.set (v : Val) (key : String) (x : Val) : Val :=
  match v with
  | .dict kvs => .dict (kvs.map fun (k, y) => if k == key then (k, x) else (k, y))
  | v => v

def Val.flag (v : Val) (name : String) : Bool :=
  match v with
  | .dict kvs => kvs.any fun (k, x) => k == name && (match x with | Val.b y => y | _ => false)
  | _ => false

/-- A BOX HANDS A COPRODUCT OVER WHOLE.  A port's strands are a summand's factors, and the fork is
    what opens them — so a box standing before a tape ends on the ONE wire the tape's port is, and
    only the fusion `F(R)[f,g] = [f,(𝟙×R)g]` puts a box on the summand's strands (`drawItems` draws
    that as the one fused tape).  Keyed on the two node SHAPES, so it holds for every box at every
    polynomial object, not for the `est` that found it. -/
def handOver (items : Array Pic) : Array Pic := Id.run do
  let mut out := items
  for i in [0 : items.size] do
    if i + 1 < items.size && out[i]!.val.kindOf == some "box" && out[i]!.outs.size != 1
        && items[i + 1]!.val.kindOf == some "case" && items[i + 1]!.ins.size == 1 then
      out := out.set! i { out[i]! with val := out[i]!.val.set "nout" (.n 1), outs := #[out[i]!.tgt] }
  return out

/-- A picture as a one-item RUN — what a node holding another picture (a lane, a fold's box, a
    constant's body) carries. -/
def laneVal (p : Pic) : Val :=
  if p.val.kindOf == some "seq" then p.val
  else nodeOf "seq" p.ins.size p.outs.size #[("items", .arr #[p.val]), ("seams", .arr #[])]

/-- §3 row 14: `𝟏` IS NOT A WIRE, so a run passing through it is not two pictures in series.  The
    factor that lands on `𝟏` discards its input and creates nothing; what the constant CREATES is
    the factor after it, and the two are the one `konst` node — so `⊸ zero` draws the same whether
    the declaration spells it `graph (fun _ => c)` in one term or a discard composed with `c`. -/
def constParts (items : Array Pic) : Array Pic := Id.run do
  let mut out := #[]
  let mut skip := false
  for i in [0 : items.size] do
    if skip then skip := false
    else
      let it := items[i]!
      if it.val.kindOf == some "konst" && it.outs.isEmpty && i + 1 < items.size then
        let b := items[i + 1]!
        out := out.push (mkPic "konst" it.ins b.outs it.src b.tgt b.isMap #[("body", laneVal b)])
        skip := true
      else out := out.push it
  return out

def seqPic (items₀ : Array Pic) (seams : Array (Nat × Array String)) (objs : Array Obj) : Pic :=
  let items := handOver items₀
  -- An EMPTY run is the IDENTITY, whose ports are its object's wires, not none: the `𝟙` lane of a
  -- `𝟙×∋` stack draws no box but still carries its strand, and reading the ports off the items
  -- would leave the panel one strand short of the arrow it draws.
  let bare := if h : objs.size > 0 then ((objs[0]'h).wires.toOption.getD #[]) else #[]
  let ins := if h : items.size > 0 then (items[0]'h).ins else bare
  let outs := if h : items.size > 0 then (items[items.size - 1]'(by omega)).outs else bare
  { val := nodeOf "seq" ins.size outs.size
      #[("items", .arr (items.map (·.val))),
        ("seams", .arr (seams.map fun (i, ls) => .arr #[.n i, .arr (ls.map .s)]))],
    ins, outs, src := objs[0]!, tgt := objs[objs.size - 1]!,
    isMap := items.all (·.isMap) }

/-- Which interior objects a run prints: an interior seam exactly when its object is ONE wire and
    differs from both printed neighbours (CIRCUIT-GEN §3), written with the OBJECT's own name.  A
    port of several strands is named where the strands are MADE — after the fork that makes them
    (`runSeams`), or after the generator an arm opens its summand with (`tapePic`) — never here,
    where a coproduct's factors would be named on a wire the fork has not yet opened. -/
def seamsOf (objs : Array Obj) : Array (Nat × Array String) := Id.run do
  let mut out := #[]
  let mut prev := objs[0]!
  for i in [0 : objs.size - 2] do
    let o := objs[i + 1]!
    let ws := match o.wires with | .ok ws => ws | .error _ => #[]
    if ws.size == 1 && !o.same prev && !o.same objs[i + 2]! then
      out := out.push (i, #[o.label]); prev := o
  return out

/-- A run's seams: its interior objects, and the pair a `⟨,⟩` fork leaves printed WHOLE — a pair's
    strands are typed nowhere else, its lanes ENDING at them. -/
def runSeams (items : Array Pic) (objs : Array Obj) : Array (Nat × Array String) := Id.run do
  let mut out := seamsOf objs
  for i in [0 : items.size] do
    if i + 1 < items.size && items[i]!.val.kindOf == some "fork" then
      out := out.push (i, items[i]!.outs.map (·.label))
  return out.qsort (fun a b => a.1 < b.1)

/-- The factors of a composite, flattened: `≫` is associative and the picture of a run does not
    record which way it was bracketed. -/
partial def factorList (e : Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``Cat.comp, args) =>
    if h : args.size ≥ 2 then factorList args[args.size - 2] ++ factorList args[args.size - 1]
    else #[e]
  | _ => #[e]

def lastTwo (args : Array Expr) : Option (Expr × Expr) :=
  if h : args.size ≥ 2 then some (args[args.size - 2], args[args.size - 1]) else none

/-- Whether the local context carries a `Map` hypothesis for this arrow, exactly as the reader of
    the Lean statement reads it. -/
def hasMapHyp (e : Expr) : MetaM Bool := do
  unless e.isFVar do return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    match d.type.getAppFnArgs with
    | (``Freyd.Alg.Map, args) => if args.back? == some e then return true
    | _ => pure ()
  return false

/-- Whether an arrow is a MAP, which is the whole of the chamfer decision.  Read off the term:
    a graph and an identity are maps, a transpose is a map, a composite and a product of maps are
    maps, and a hypothesis in scope says so for a variable.

    A NAMED map is a map.  `cons`, `nil`, `new`, the initial algebra `α` are `graph`s behind their
    own names, so stopping at the head constant draws every named FUNCTION as a relation; the last
    clause is one delta step — the same step `drawDecl` draws a def's body with — and the fuel is
    what a def spelled in terms of itself would otherwise cost. -/
partial def isMapOf (e : Expr) (fuel : Nat := 8) : MetaM Bool := do
  match e.getAppFnArgs with
  | (``Freyd.Alg.RelSet.graph, _) | (``Cat.id, _) | (``Freyd.Alg.Λ, _) => return true
  | (``Cat.comp, args) | (``Freyd.Alg.RelSet.rprodMap, args) =>
    match lastTwo args with
    | some (f, g) => return (← isMapOf f fuel) && (← isMapOf g fuel)
    | none => hasMapHyp e
  | _ =>
    if ← hasMapHyp e then return true
    if fuel == 0 then return false
    for n in [``Freyd.Alg.RelSet.graph, ``Cat.id, ``Freyd.Alg.Λ, ``Cat.comp,
              ``Freyd.Alg.RelSet.rprodMap] do
      if let some e' ← Meta.whnfUntil e n then return ← isMapOf e' (fuel - 1)
    -- AND AN EQUATION THE NOTE REWRITES ALONG answers this too: `arm₂` of a map is a map, and the
    -- label already writes the arm by its own name (`snoc`), so the box has to be that map's
    -- rectangle — the name and the shape are read off the same rewritten term or they disagree.
    if let some r ← StrDiag.rewriteHead? e then return ← isMapOf r (fuel - 1)
    return false

/-- The `E a` of an object: the power object as a LABEL, which is all the picture needs of it. -/
def powLabel (a : Obj) : Obj := .mk (applyLabel "E" a) .opaq #[] (applyJoin "E" a)

def wiresOf (o : Obj) : MetaM (Array Obj) :=
  match o.wires with
  | .ok ws => return ws
  | .error m => throwError m

/-- The fork's `open` generator: the coproduct arrives as ONE wire and the arm splits or ends it
    according to its summand. -/
def openPic (src s : Obj) : MetaM Pic := return mkPic "open" #[src] (← wiresOf s) src s true #[]

/-- A DEFINED arrow opened to its body, on the same test `leaf` uses: a name the labeller keeps is
    never opened, and a body with no clause has no circuit inside it.  Every clause that matches on
    a factor's HEAD must go through this, or a rule fires on `[f,g]` written out and misses the same
    junction under the name a `def` gave it. -/
def openBody (e : Expr) : MetaM Expr := do
  -- A TERM THIS FUNCTOR ALREADY DRAWS IS NOT OPENED.  `junc`'s own body is the union of its two
  -- injections, which `hasClause` also answers to, so opening it handed every rule keyed on a
  -- junction a `∪` instead — and the tape fusion `F(R)[f,g]=[f,(𝟙×R)g]` then never fired on a
  -- bracket written out.  Only a name with NO clause of its own is opened, and only into a body
  -- that has one.
  if hasClause e then return e
  match ← Meta.unfoldDefinition? e with
  | some v => let b := v.headBeta; return (if hasClause b then b else e)
  | none => return e

def openDef (e : Expr) : MetaM Expr := do
  if ← isNamed e then return e
  openBody e

/-- Whether `f` is a FOLD-FORMER, read off its own polymorphic type: `f : (a(C) ⟶ C) → (b ⟶ C)`,
    where the carrier `C` is one of `f`'s parameters, the argument is an algebra ON it, and the
    result comes out of a `b` that does NOT move with it — the initial algebra's own object.  That
    last clause is the whole test: `est(R) : E(C) ⟶ C` has the same two targets and its source
    moves with `C`, `[f,g] : a+b ⟶ c` has a fixed source and an argument that is not an algebra,
    and a fold has both.  So every carrier's own pointwise `cataR` — a `def` with no circuit in its
    body, which `hasClause` therefore refuses to open — draws the functorial box with no clause of
    its own, and so does the next carrier's. -/
def isFold (fn : Expr) : MetaM Bool := do
  let n := fn.getAppNumArgs
  let (xs, _, ty) ← Meta.forallMetaBoundedTelescope (← Meta.inferType fn.getAppFn) n
  if xs.size != n then return false
  let .forallE _ dom body _ := ty | return false
  if body.hasLooseBVars then return false
  match (← Meta.whnfR dom).getAppFnArgs, (← Meta.whnfR body).getAppFnArgs with
  | (``Cat.Hom, da), (``Cat.Hom, ba) =>
    if da.size < 2 || ba.size < 2 then return false
    let c := da[da.size - 1]!
    let .mvar cid := c | return false
    let holds (t : Expr) := (t.find? fun x => x.isMVar && x.mvarId! == cid).isSome
    return ba[ba.size - 1]! == c && holds da[da.size - 2]! && !holds ba[ba.size - 2]!
  | _, _ => return false

mutual

/-- §3 row 5: a composite is its factors' pictures, ports glued.  The factors are flattened, so a
    nested composite splices in rather than nesting, and an identity contributes NO factor — it is
    the bare wire the run already draws. -/
partial def drawItems (e : Expr) : MetaM (Array Pic) := do
  match e.getAppFnArgs with
  | (``Cat.comp, _) => do
    let fs := factorList e
    let mut out := #[]
    let mut i := 0
    while i < fs.size do
      -- Tape fusion, `F(R)[f,g] = [f,(𝟙×R)g]`: keyed on the two node SHAPES, and a theorem of the
      -- relator, so a functor handing over to a case draws the ONE tape the note draws instead of
      -- two in series.  Without it the picture is a correct but uglier equal.
      let fused ← if i + 1 < fs.size then do
          let nxt ← openDef fs[i + 1]!
          match fs[i]!.getAppFnArgs, nxt.getAppFnArgs with
          | (``Freyd.Functor.map, fa), (``Freyd.Alg.junc, ja) =>
            match fa.back?, lastTwo ja with
            | some r, some (u, v) => do
              -- The tape forks at the FUNCTOR's source `F(a)`, not at the junction's `F(b)`: the
              -- fused `𝟙×R` is drawn on the summand `R` still has to cross, and reading the arms
              -- off `F(b)` leaves no strand for `R` to sit on, so it silently drew `𝟙×𝟙`.
              let (s, _) ← endsOf fs[i]!
              let (_, t) ← endsOf fs[i + 1]!
              pure (some (← casePic u v s t (fuse := some r)))
            | _, _ => pure none
          -- A MAP GIVEN BY A MATCH IS THE SAME TAPE, so it fuses the same way: the junction
          -- `[f,g]` and the `match` on a coproduct are one node written two ways, and keying the
          -- fusion on the junction alone drew a functor box in series with the fork for every
          -- algebra whose structure map is a Lean function.
          | (``Freyd.Functor.map, fa), (``Freyd.Alg.RelSet.graph, ga) =>
            match fa.back?, ga.back? with
            | some r, some g => do
              let (s, _) ← endsOf fs[i]!
              let (_, t) ← endsOf fs[i + 1]!
              if s.kind == .sum && (← StrDiag.sumArms (← Meta.whnfD g)).isSome then
                pure (some (← graphPic g s t (fuse := some r)))
              else pure none
            | _, _ => pure none
          | _, _ => pure none
        else pure none
      match fused with
      | some p => out := out.push p; i := i + 2
      | none => out := out ++ (← drawItems fs[i]!); i := i + 1
    return out
  -- `Λ(R) = Λ(𝟙) E(R)`: the transpose of a composite factors through the transpose of the
  -- identity, which is why the note draws a fraction box and then an `E(−)` box, never one box.
  | (``Freyd.Alg.Λ, args) =>
    match args.back? with
    | some r =>
      let (a, _) ← endsOf e
      let (rs, rt) ← endsOf r
      let ws ← wiresOf rs
      let frac := boxPic "𝟙" ws #[powLabel rs] rs (powLabel rs) true (frac := true)
      if r.getAppFnArgs.1 == ``Cat.id then return #[{ frac with tgt := a }]
      return #[frac, boxPic ("E(" ++ (← StrDiag.label r) ++ ")") #[powLabel rs] #[powLabel rt]
        (powLabel rs) (powLabel rt) true]
    | none => return #[← draw e]
  | (``Cat.id, _) => return #[]
  | _ => return #[← draw e]

/-- A run: its factors and the objects between them, which is what the seam rule reads. -/
partial def drawRun (e : Expr) : MetaM Pic := do
  let (items, objs) ← runParts e
  -- A run of ONE factor IS that factor: a `seq` around it would add a port stub at each end and
  -- draw a picture wider than the arrow it draws.  Only a seamless singleton — a seam is a label
  -- the run itself carries, and a bare item has nowhere to keep it.
  let seams := runSeams items objs
  if h : items.size == 1 && seams.isEmpty then
    return items[0]'(by simp at h; omega)
  return seqPic items seams objs

partial def runParts (e : Expr) : MetaM (Array Pic × Array Obj) := do
  let items := constParts (← drawItems e)
  let (src, _) ← endsOf e
  let mut objs := #[src]
  for it in items do objs := objs.push it.tgt
  return (items, objs)

/-- One picture for one arrow. -/
partial def draw (e : Expr) : MetaM Pic := do
  let (src, tgt) ← endsOf e
  match e.getAppFnArgs with
  | (``Cat.comp, _) | (``Freyd.Alg.Λ, _) | (``Cat.id, _) => drawRun e
  -- §3 row 6: a product is a vertical stack, one lane per ×-factor.
  | (``Freyd.Alg.RelSet.rprodMap, args) | (``Freyd.Alg.prodMap, args) =>
    match lastTwo args with
    | some (f, g) => stackPic #[f, g] src tgt
    | none => leaf e src tgt
  -- §3 row 11: the `∪` region — the input arrives once and a dashed fan hands it to both bodies.
  | (``Freyd.Alg.DistributiveAllegory.union, args) =>
    match lastTwo args with
    | some (f, g) => do
      let bs := #[← lane (← drawRun f), ← lane (← drawRun g)]
      return mkPic "union" bs[0]!.ins bs[0]!.outs src tgt false
        #[("bodies", .arr (bs.map (·.val)))]
    | none => leaf e src tgt
  -- §3 row 12: `x∩y` — copy every strand, run BOTH lanes, merge.  `∇=Δ°` forces the two to carry
  -- the same value, and that is the whole of the intersection: no box says `∩`.
  | (``Freyd.Alg.Allegory.inter, args) =>
    match lastTwo args with
    | some (f, g) => do
      let bs := #[← lane (← drawRun f), ← lane (← drawRun g)]
      return mkPic "cap" bs[0]!.ins bs[0]!.outs src tgt false
        #[("lanes", .arr (bs.map (·.val)))]
    | none => leaf e src tgt
  -- §3 row 20: `⟨R,S⟩` — copy every strand, run BOTH lanes, and leave on their outputs STACKED.
  -- A `cap` with no merge: the pair's target IS the product of the lanes' targets, so the node's
  -- outputs are the lanes' outputs in order and no box says `⟨,⟩`.
  | (``Freyd.Alg.RelSet.rpair, args) | (``Freyd.Alg.RelProd.pair, args) =>
    match lastTwo args with
    | some (f, g) => do
      let bs := #[← lane (← drawRun f), ← lane (← drawRun g)]
      return mkPic "fork" bs[0]!.ins (bs.foldl (fun a b => a ++ b.outs) #[]) src tgt
        (bs.all (·.isMap)) #[("lanes", .arr (bs.map (·.val)))]
    | none => leaf e src tgt
  -- §3 row 13: the bracket at a polynomial object — tape fork, branches, tape join.
  | (``Freyd.Alg.junc, args) =>
    match lastTwo args with
    | some (f, g) => casePic f g src tgt (fuse := none)
    | none => leaf e src tgt
  -- §3 rows 7/8: the `°`.  Written on an ATOM it is the same box mirrored; over a product it
  -- distributes, one flipped box per wire; on a composite it is the cup/cap frame, which `cpanel`
  -- has no node for, so it is an error naming the term rather than a guessed box.
  | (``Freyd.Alg.Allegory.recip, args) =>
    match args.back? with
    | some r => recipPic r src tgt
    | none => leaf e src tgt
  | (``Freyd.Alg.RelSet.graph, args) =>
    match args.back? with
    | some f => graphPic f src tgt
    | none => leaf e src tgt
  -- A least fixpoint is drawn by its BODY at the recursion variable: the note's `X` inside
  -- `P(F(X)h)` IS that variable, so `μ` costs no box — the picture is the body's.
  | (``Freyd.Alg.mu, args) =>
    match args.back? with
    | some φ => Meta.lambdaTelescope φ fun _ b => drawRun b
    | none => leaf e src tgt
  | _ => do
    if e.isApp then
      if ← isFold e.appFn! then return ← cataPic e.appArg! src tgt
    leaf e src tgt

/-- §3 row 17: the fold as MELLIÈS' FUNCTORIAL BOX — the algebra's own circuit between two bars.
    Nothing crosses the LEFT pair: the input arrives at them and the algebra's strands start
    inside, and that break IS the recursion.  The carrier labels the output wire only where it
    differs from that wire's own label; a product carrier is already drawn as its wires. -/
partial def cataPic (r : Expr) (src tgt : Obj) : MetaM Pic := do
  let body ← lane (← drawRun r)
  let cw ← wiresOf tgt
  let named := cw.size == 1 && cw[0]!.label != tgt.label
  return mkPic "cata" #[src] cw src tgt body.isMap
    #[("body", body.val), ("label", if named then .s tgt.label else .nul),
      ("port", .arr (body.ins.map fun o => .s o.label))]

/-- `(R×S)° = R°×S°`: over a PRODUCT the `°` distributes, one flipped box per wire. -/
partial def recipPic (r : Expr) (src tgt : Obj) : MetaM Pic := do
  match r.getAppFnArgs with
  | (``Freyd.Alg.RelSet.rprodMap, ra) | (``Freyd.Alg.prodMap, ra) =>
    match lastTwo ra with
    | some (f, g) => do
      let ls ← #[f, g].mapM fun x => do
        let (xs, xt) ← endsOf x
        lane (← recipPic x xt xs)
      let ins := ls.foldl (fun a l => a ++ l.ins) #[]
      let outs := ls.foldl (fun a l => a ++ l.outs) #[]
      return mkPic "stack" ins outs src tgt false #[("lanes", .arr (ls.map (·.val)))]
    | none => leaf r src tgt
  | _ =>
    let p ← draw r
    if p.val.kindOf != some "box" then
      throwError "`{← StrDiag.label r}°` writes `°` on a composite, which is the cup/cap frame of \
        CIRCUIT-GEN §3 row 8 — `cpanel` has no node for it"
    return boxPic (← StrDiag.label r) p.outs p.ins src tgt false
      (frac := p.val.flag "frac") (flip := !(p.val.flag "flip"))

/-- §3 rows 1-2: an atom.  A relation's chamfer says which way it runs; a map is a rectangle.

    A DEFINED arrow is drawn by its DEFINITION when that definition is built from operators this
    functor has a clause for: `consR` is the graph of a cons cell, so it is the rectangle a map
    gets and not the chamfered box its name alone would have produced.  An arrow the labeller
    names — `est(R)`, `Λ(R)`, `∋` — is never unfolded: its own spelling is the picture's. -/
partial def leaf (e : Expr) (src tgt : Obj) : MetaM Pic := do
  if !(← isNamed e) then
    if let some v ← Meta.unfoldDefinition? e then
      if hasClause v then
        let p ← draw v
        -- THE LABEL IS THE TERM AS IT STOOD BEFORE OPENING.  Opening a `def` gives the WIRING —
        -- whether the box is a map's rectangle, how many strands it spans — and never the name: a
        -- body that draws as ONE box is that one arrow, and the note writes it by the name the
        -- definition gave it (`plus`, `glue`), not by the lambda the body happens to be.
        if p.val.kindOf == some "box" then
          return { p with val := p.val.set "label" (.s (← StrDiag.label e)) }
        return p
  return boxPic (← StrDiag.label e) (← wiresOf src) (← wiresOf tgt) src tgt (← isMapOf e)

partial def lane (p : Pic) : MetaM Pic := return { p with val := laneVal p }

partial def stackPic (fs : Array Expr) (src tgt : Obj) : MetaM Pic := do
  let ls ← fs.mapM fun f => do lane (← drawRun f)
  let ins := ls.foldl (fun a l => a ++ l.ins) #[]
  let outs := ls.foldl (fun a l => a ++ l.outs) #[]
  return mkPic "stack" ins outs src tgt (ls.all (·.isMap)) #[("lanes", .arr (ls.map (·.val)))]

/-- §3 row 13.  The coproduct arrives as ONE wire, the fork being what opens it; each arm opens
    that wire into its summand's strands, and the seam after the generator names them. -/
partial def casePic (f g : Expr) (src tgt : Obj) (fuse : Option Expr) : MetaM Pic :=
  tapePic src tgt fun i s =>
    armParts (if i == 0 then f else g) src s (if i == 1 then fuse else none) (opened := true)

/-- The tape itself: the fork, its two arms, the join.  How an arm is DRAWN is the caller's — a
    junction draws its two arrows, a map's `match` its two alternatives — and what they share is
    the fork: the coproduct arrives as one wire, the arm's `open` generator splits or ends it, and
    the seam after that generator names the summand's strands. -/
partial def tapePic (src tgt : Obj) (arm : Nat → Obj → MetaM (Array Pic × Array Obj)) :
    MetaM Pic := do
  let ss := src.parts
  if ss.size != 2 then
    throwError "a case forks {ss.size} summands, and the tape fork draws two"
  let mut bodies : Array Pic := #[]
  let mut isMap := true
  for i in [0 : 2] do
    let s := ss[i]!
    let (items, objs) ← arm i s
    let ws ← wiresOf s
    let seams := (if ws.isEmpty then #[] else #[(0, ws.map (·.label))])
      ++ (runSeams items objs).filter (·.1 != 0)
    let body := seqPic items seams objs
    bodies := bodies.push body
    isMap := isMap && body.isMap
  return mkPic "case" #[src] bodies[0]!.outs src tgt isMap
    #[("bodies", .arr (bodies.map (·.val)))]

/-- One arm of a fork: its factors and the objects between them.  `opened` says whether the
    coproduct wire ARRIVES here — inside a `case` it does, and the arm opens it into its summand's
    strands; taken alone by a `.inl`/`.inr` route the summand IS the source, and there is nothing
    to open. -/
partial def armParts (br : Expr) (src s : Obj) (fuse : Option Expr) (opened : Bool) :
    MetaM (Array Pic × Array Obj) := do
  let (items, objs) ← runParts br
  -- the fused `𝟙×R` lands on the strands the functor recurses on: the summand's factors that
  -- ARE `R`'s source, the others staying bare wire
  let (items, objs) ← match fuse with
    | some r => do let pre ← fusedStack s r; pure (#[pre] ++ items, #[s] ++ objs)
    | none => pure (items, objs)
  if !opened then return (items, objs)
  return (#[← openPic src s] ++ items, #[src] ++ objs)

/-- `.inl`/`.inr` on a route: ONE arm of the fork at the head of the run, drawn with the summand as
    the SOURCE — what a panel draws when the other arm is a constant and carries none of the law's
    content.  The rule is over the FORM of the run: a junction at its head, alone or behind the
    functor whose tape fuses into it, and every factor after the fork stays on the arm. -/
partial def armOf (e : Expr) (i : Nat) : MetaM Pic := do
  let fs := if e.isAppOf ``Cat.comp then factorList e else #[e]
  -- `openBody`, not `openDef`: naming an ARM is the statement that this panel draws the inside of
  -- the fork, so a name that keeps itself everywhere else opens here — the same `S` the note sets
  -- as one box where the panel is the whole algebra.
  let head ← openBody fs[0]!
  let nxt ← if fs.size > 1 then openBody fs[1]! else pure head
  let (j, fuse) :=
    if head.isAppOf ``Freyd.Alg.junc then (0, none)
    else if fs.size > 1 && fs[0]!.isAppOf ``Freyd.Functor.map && nxt.isAppOf ``Freyd.Alg.junc then
      (1, fs[0]!.getAppArgs.back?)
    else (fs.size, none)
  if j ≥ fs.size then
    throwError "`.inl`/`.inr` draws one arm of a fork, and this side has none at the head of its \
      run: it starts with {← StrDiag.label fs[0]!}"
  let some (u, v) := lastTwo (← openBody fs[j]!).getAppArgs
    | throwError "a junction with no arms: {← StrDiag.label fs[j]!}"
  let (src, _) ← endsOf fs[0]!
  let ss := src.parts
  if ss.size != 2 then
    throwError "the fork at {src.label} has {ss.size} summands, and `.inl`/`.inr` names two"
  let (its, objs') ← armParts (if i == 0 then u else v) src ss[i]!
    (if i == 1 then fuse else none) (opened := false)
  let mut items := its
  let mut objs := objs'
  for k in [j + 1 : fs.size] do
    let more ← drawItems fs[k]!
    items := items ++ more
    for it in more do objs := objs.push it.tgt
  return seqPic items (runSeams items objs) objs

/-- The `𝟙×R` the tape fusion puts on a branch: `R` on the strands the functor recurses on — the
    summand's factors that ARE `R`'s source — and bare wire on the rest. -/
partial def fusedStack (s : Obj) (r : Expr) : MetaM Pic := do
  let (rs, rt) ← endsOf r
  let ps := if s.kind == .prod then s.parts else #[s]
  -- The functor recurses on ONE slot — the LAST factor of the summand, the same convention that
  -- names the pattern functor in `objOf` — so `R` goes there and bare wire on the rest.  Matching
  -- EVERY factor whose object is `R`'s source draws `R×R` the moment the two agree, as they do at
  -- `F(X)=𝟏+Int×X`.
  let hit := (List.range ps.size).reverse.find? fun i => (ps[i]!).same rs
  let mut ls := #[]
  let mut outs := #[]
  for i in [0 : ps.size] do
    let p := ps[i]!
    if hit == some i then
      ls := ls.push (← lane (← draw r)); outs := outs.push rt
    else
      ls := ls.push (seqPic #[] #[] #[p]); outs := outs.push p
  let ins := ls.foldl (fun a l => a ++ l.ins) #[]
  let outw := ls.foldl (fun a l => a ++ l.outs) #[]
  let t := if outs.size == 1 then outs[0]! else prodObj outs
  return mkPic "stack" ins outw s t false #[("lanes", .arr (ls.map (·.val)))]

/-- §3 rows 2/3/14: a map given by a function.  A constant DISCARDS every input strand at a dot
    and creates its value; a projection ends the factors it drops at a dot and crosses the one it
    keeps, costing no box at all; anything else is a rectangle. -/
partial def graphPic (f : Expr) (src tgt : Obj) (fuse : Option Expr := none) : MetaM Pic := do
  let fw ← Meta.whnfD f
  -- §3 row 13 AT A MAP: a `match` on the input at a coproduct is the SAME tape `[f,g]` draws — the
  -- junction is the same object, written the other way round — so it forks here rather than
  -- collapsing to one box carrying the `def`'s name.  It takes the TAPE FUSION for the same
  -- reason: `F(R)` handing over to a match is `F(R)[f,g]`, and the caller passes `src` as the
  -- functor's source so the fork is at `F(a)` and the fused `𝟙×R` sits on the arm that crosses it.
  if src.kind == .sum then
    if let some arms ← StrDiag.sumArms fw then
      return ← tapePic src tgt fun i s => do
        match (if i == 1 then fuse else none) with
        | some r => do
          let pre ← fusedStack s r
          let p ← graphPic arms[i]! pre.tgt tgt
          return (#[← openPic src s, pre, p], #[src, s, pre.tgt, p.tgt])
        | none => do
          let p ← graphPic arms[i]! s tgt
          return (#[← openPic src s, p], #[src, s, p.tgt])
  let ws ← wiresOf src
  match fw with
  | .lam _ _ body _ =>
    if !body.hasLooseBVars then
      let bx := boxPic (← StrDiag.mapLabel f true) #[] (← wiresOf tgt) src tgt true
      if ws.isEmpty then return bx
      return mkPic "konst" ws (← wiresOf tgt) src tgt true #[("body", (← lane bx).val)]
    match StrDiag.projIndex body with
    | some i =>
      if src.kind != .prod || i ≥ src.parts.size then
        throwError "a projection out of {src.label}, which is not a product of {i + 1} factors"
      let keep ← src.parts.mapM fun p => do return (← wiresOf p).size
      return mkPic "proj" ws (← wiresOf tgt) src tgt true
        #[("at", .n i), ("label", .s (if i == 0 then "π₁" else "π₂")),
          ("keep", .arr (keep.map .n))]
    | none => return boxPic (← StrDiag.mapLabel f true) ws (← wiresOf tgt) src tgt true
  | _ => return boxPic (← StrDiag.mapLabel f true) ws (← wiresOf tgt) src tgt true

end

/-! ### The page

The emitted file calls `cpanel` — the note's own constructor, unchanged — so the generated picture
and the note's are the same drawing routine over the same tree, and any difference between them is
a difference of TREE. -/


/-- A statement whose head is a DEFINITION returning `Prop` — `MonotonicAlg S R`, `Entire R`,
    `Map f` — is the relation it unfolds to, so the picture is of the inequation the reader sees,
    not of one box carrying the predicate's name.  Delta on the HEAD CONSTANT only
    (`unfoldDefinition?`), never `whnf`: a full weak-head normalisation would keep going into the
    arrows themselves, and a `RelSet` arrow's body is a pointwise `fun x y => …` with no circuit in
    it.  It stops the moment `split` recognises the head, so nothing beyond the relation is opened. -/
partial def toRelation (e : Expr) : MetaM Expr := do
  if (StrDiag.split e).isSome then return e
  unless ← Meta.isProp e do return e
  match ← Meta.unfoldDefinition? e with
  | some e' => toRelation e'
  | none => return e

/-- The panel: the tree with its ports named, one label per STRAND — a product is two wires, so it
    is two labels, never one reading `A×[A]`. -/
def ports (p : Pic) : Val :=
  match p.val with
  | .dict kvs => .dict (kvs ++
      #[("src", .arr (p.ins.map fun o => .s o.label)),
        ("tgt", .arr (p.outs.map fun o => .s o.label))])
  | v => v

def panel (e : Expr) : MetaM Val := return ports (← drawRun e)

/-- The declaration's picture.  A `def` is unfolded ONE level and drawn by its body; a theorem is
    split by its relation symbol and the named side drawn.

    A HYPOTHESIS IS A STATEMENT TOO.  `binder` names one binder of the declaration's `∀`-telescope
    and draws ITS type instead of the conclusion, so the greedy theorem's `htrans : R°R° ⊑ R°` is
    a panel of that theorem rather than a picture with no declaration behind it.  The rule is over
    the FORM of the type — every binder of every declaration is reachable this way — not a table of
    the hypotheses somebody wanted; a `def`'s body is not unfolded when a binder is named, since
    the binder belongs to the type. -/
def drawDecl (declName : Name) (side : Option String) (binder : Option String := none)
    (branch : List Nat := []) : MetaM String := do
  let some ci := (← getEnv).find? declName
    | throwError "no such declaration: {declName}"
  StrDiag.stmtTelescope ci.type fun xs tybody => do
    let tybody ← match binder with
      | none => pure tybody
      | some h => do
        let names ← xs.mapM fun x => return (← x.fvarId!.getUserName).toString
        match ← xs.findM? fun x => return (← x.fvarId!.getUserName).toString == h with
        | some x => Meta.inferType x
        | none => throwError "`{declName}` has no binder `{h}`; its binders are \
            {String.intercalate ", " names.toList}"
    -- A `def` is unfolded ONE level and drawn by its BODY — but only when that body is built from
    -- operators this functor has a clause for.  A relation given POINTWISE (`fun x y => …`, which
    -- is how most `RelSet` arrows are written) has no circuit inside it, and the honest picture of
    -- it is the one box its own name labels.
    let isDef := binder.isNone && (match ci with | .defnInfo _ => true | _ => false)
    let body ← if isDef then
        match ci.value? with
        | some v =>
          let b := (mkAppN v xs).headBeta
          pure (if hasClause b then b
            else mkAppN (mkConst declName (ci.levelParams.map .param)) xs)
        | none => pure tybody
      else pure tybody
    let body ← toRelation body
    let e ← match StrDiag.split body, side with
      | some (_, l, _), some "lhs" => pure l
      | some (_, _, r), some "rhs" => pure r
      | some (sym, _, _), _ =>
        throwError "`{declName}` states `_ {sym} _`: name the side to draw, \
          `{declName}.lhs` or `{declName}.rhs`"
      | none, some s => throwError "`{declName}` is not an equation or containment: no `.{s}`"
      | none, _ => pure body
    let tree ← match branch with
      | [i] => pure (ports (← armOf e i))
      | [] => panel e
      -- A tape draws the fork itself, so one selector is as deep as this route goes: what a second
      -- would name — an operand of the arm — is a Hinze–Marsden panel's question.
      | _ => throwError "`{declName}` is routed with {branch.length} selectors; a circuit draws \
          ONE arm of the fork at the head of its run"
    let name := declName.toString ++ (match binder with | some h => "#" ++ h | none => "")
      ++ (match side with | some s => "." ++ s | none => "")
      ++ branch.foldl (fun s i => s ++ (if i == 0 then ".inl" else ".inr")) ""
    return "// GENERATED by `diag-export --circuit` — do not edit; regenerate with\n\
      //   ./scripts/diag-export --circuit " ++ name ++ "\n\
      #import \"../../cpanel.typ\": *\n\n\
      #let pic = cpanel(" ++ tree.render ++ ",\n  cert: (lean: " ++ tstr name ++ "))\n\n\
      #set page(width: auto, height: auto, margin: 12pt)\n\
      #set text(size: 10pt)\n\n\
      #pic\n"

end Freyd.CircuitDiagram
