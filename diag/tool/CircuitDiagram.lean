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

inductive Obj where
  | mk (label : String) (kind : OKind) (parts : Array Obj)
  deriving Inhabited

def Obj.label : Obj → String | .mk l _ _ => l
def Obj.kind : Obj → OKind | .mk _ k _ => k
def Obj.parts : Obj → Array Obj | .mk _ _ p => p

/-- Two objects are the same for seam purposes when they print the same: the label IS what a seam
    would show, so a seam that would repeat its neighbour is exactly one whose label repeats it. -/
def Obj.same (a b : Obj) : Bool := a.label == b.label

/-- The strands a port at this object carries: its ×-factors, none for `𝟏`, and for a coproduct
    the strands of its one non-`𝟏` summand — the note's decision that `𝟏+` is not drawn, so
    `F([A])` at a box is the recursive branch's `A`,`[A]`.  A coproduct with two real summands has
    no port reading at all: only a tape draws it, and the tape says so itself. -/
partial def Obj.wires : Obj → Except String (Array Obj)
  | .mk _ .one _ => return #[]
  | .mk _ .prod ps => do
    let mut out := #[]
    for p in ps do out := out ++ (← p.wires)
    return out
  | o@(.mk l .sum ps) => do
    let ss := ps.filter fun p => p.kind != .one
    if h : ss.size = 1 then (ss[0]'(by omega)).wires
    else throw s!"`{l}` sums {ss.size} summands besides `𝟏`: a case split, which only a tape \
      draws — not a port's wires ({o.label})"
  | o@(.mk _ .opaq _) => return #[o]

/-! ### Labels

The label of an object or an arrow is the elaborator's own pretty printer under the repo's
notations, with the namespaces taken off — they carry no information inside a picture of the
repo's own algebra.  The book's own spellings (`cons`, `nil`, `[A]`) are structural readings of
the term, never a table of strings: `cons` is the arrow whose graph is `List.cons`. -/

def plain (e : Expr) : MetaM String := do
  let s := toString (← Meta.ppExpr e)
  let s := s.replace "Freyd.Alg.RelSet." "" |>.replace "Freyd.Alg." "" |>.replace "Freyd." ""
    |>.replace "Alg.RelSet." "" |>.replace "Alg." "" |>.replace "RelSet." ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- The leading identifier of a label, which is what decides whether an applied functor needs a
    space: `E[A]` opens with `E`, `tree A` with `tree`. -/
def headWord (s : String) : String :=
  (s.takeWhile fun c => c.isAlphanum).toString

/-- Application of a one-letter functor to a one-letter head is juxtaposed (`EA`, `FE[A]`); a
    bracketed argument needs no space either; anything else gets one (`E tree A`). -/
def applyLabel (f a : String) : String :=
  if a.startsWith "[" then f ++ a
  else if f.length == 1 && (headWord a).length == 1 then f ++ a
  -- Only a SINGLE object name may stay bare (`F Int`); anything longer would read as a second
  -- argument, so it is parenthesised — `F(CL.ConsList Unit A)`, never `F CL.ConsList Unit A`.
  else if a.any (· == ' ') then f ++ "(" ++ a ++ ")"
  else f ++ " " ++ a

mutual

/-- An object of the allegory.  The power object is recognised BEFORE unfolding — its carrier is a
    predicate type, which says nothing — and everything else is read off the carrier. -/
partial def objOf (o : Expr) : MetaM Obj := do
  match o.getAppFnArgs with
  | (``Freyd.Alg.PowerAllegory.powerObj, args) =>
    match args.back? with
    | some b => return .mk (applyLabel "E" (← objOf b).label) .opaq #[]
    | none => return .mk (← plain o) .opaq #[]
  | _ =>
    match (← Meta.whnfD o).getAppFnArgs with
    | (``Freyd.Alg.RelSet.mk, #[t]) => do
      let ob ← typeObj t
      -- A coproduct object is a pattern functor at a carrier, and `F` is what the note calls it;
      -- the carrier is the last factor of the recursive summand, which is what recurses.
      if ob.kind == .sum then
        let ss := ob.parts.filter fun p => p.kind != .one
        if h : ss.size = 1 then
          let s := ss[0]'(by omega)
          let c := if s.kind == .prod then (s.parts.back?.map Obj.label).getD s.label else s.label
          return .mk (applyLabel "F" c) .sum ob.parts
      return ob
    | _ => return .mk (← plain o) .opaq #[]

/-- A carrier TYPE.  `×` is the product of wires, `⊕` the coproduct only a tape opens, `Unit` the
    empty word, and a list its bracketed spelling. -/
partial def typeObj (t : Expr) : MetaM Obj := do
  -- A CARRIER TYPE IS ITS OBJECT, and must be read before `whnfD` for the same reason the power
  -- object is: `(E[A]).carrier` unfolds to a predicate type that says nothing, and then the second
  -- summand of `F(E[A])` no longer matches `∋`'s source, so the fused `𝟙×∋` draws `𝟙×𝟙`.
  if let (``Freyd.Alg.RelSet.carrier, #[o]) := t.getAppFnArgs then return ← objOf o
  let t ← Meta.whnfD t
  match t.getAppFnArgs with
  | (``Prod, #[a, b]) => do
    let (oa, ob) := (← typeObj a, ← typeObj b)
    return .mk (oa.label ++ "×" ++ ob.label) .prod #[oa, ob]
  | (``Sum, #[a, b]) => do
    let (oa, ob) := (← typeObj a, ← typeObj b)
    return .mk (oa.label ++ "+" ++ ob.label) .sum #[oa, ob]
  | (``List, #[a]) => return .mk ("[" ++ (← typeObj a).label ++ "]") .opaq #[]
  | (``Unit, _) | (``PUnit, _) => return .mk "𝟏" .one #[]
  | _ => return .mk (← plain t) .opaq #[]

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

/-- Which factor of a product a projection keeps, read off the function's own body. -/
def projIndex (body : Expr) : Option Nat :=
  match body with
  | .proj ``Prod i _ => some i
  | _ => match body.getAppFnArgs with
    | (``Prod.fst, _) => some 0
    | (``Prod.snd, _) => some 1
    | _ => none

/-- Whether the labeller has a spelling of its own for this arrow: those keep their name and are
    never unfolded, because the name IS what the note writes on the box. -/
def isNamed (e : Expr) : Bool :=
  match e.getAppFnArgs.1 with
  | ``Cat.id | ``Freyd.Alg.PowerAllegory.eps | ``Freyd.Alg.est | ``Freyd.Alg.Λ
  | ``Freyd.Alg.Allegory.recip | ``Freyd.Alg.RelSet.graph => true
  | _ => false

/-- Whether the term is built from an operator this functor draws — the test for unfolding a
    defined arrow: a body that is not one of these is a relation given pointwise, which has no
    circuit inside it. -/
def hasClause (e : Expr) : Bool :=
  match e.getAppFnArgs.1 with
  | ``Cat.comp | ``Cat.id | ``Freyd.Alg.Λ | ``Freyd.Alg.junc | ``Freyd.Alg.relCata
  | ``Freyd.Alg.Allegory.recip | ``Freyd.Alg.Allegory.inter
  | ``Freyd.Alg.DistributiveAllegory.union | ``Freyd.Alg.RelSet.graph
  | ``Freyd.Alg.RelSet.rprodMap | ``Freyd.Alg.prodMap | ``Freyd.Functor.map => true
  | _ => false

mutual

partial def arrLabel (e : Expr) : MetaM String := do
  match e.getAppFnArgs with
  | (``Cat.id, _) => return "𝟙"
  | (``Freyd.Alg.PowerAllegory.eps, _) => return "∋"
  | (``Freyd.Alg.est, args) =>
    match args.back? with
    | some r => return "est(" ++ (← arrLabel r) ++ ")"
    | none => plain e
  | (``Freyd.Alg.Λ, args) =>
    match args.back? with
    | some r => return (← arrLabel r) ++ "%∋"
    | none => plain e
  | (``Freyd.Alg.Allegory.recip, args) =>
    match args.back? with
    | some r => return (← arrLabel r) ++ "°"
    | none => plain e
  | (``Freyd.Alg.RelSet.graph, args) =>
    match args.back? with
    | some f => mapLabel f
    | none => plain e
  | _ => plain e

/-- The label of a MAP given by its function.  A cons cell is `cons`, a projection its `π`, a
    constant the thing it creates — each read off the function's own body, so the next map built
    the same way gets the same name without anything being added here. -/
partial def mapLabel (f : Expr) : MetaM String := do
  let f ← Meta.whnfD f
  match f with
  | .lam _ _ body _ =>
    match projIndex body with
    | some 0 => return "π₁"
    | some _ => return "π₂"
    | none =>
      -- The book's names for the two structure maps of a list-like carrier, read off the TERM:
      -- a CONSTRUCTOR fed both factors of the input pair is `cons`, and one fed nothing from the
      -- input is `nil`.  Nothing here knows `List`: the next carrier built the same way gets the
      -- same names without a line being added.
      let isCtor ← match body.getAppFn with
        | .const n _ => match (← getEnv).find? n with
          | some (.ctorInfo _) => pure true
          | _ => pure false
        | _ => pure false
      if isCtor && !body.hasLooseBVars then return "nil"
      if isCtor && (body.find? fun x => projIndex x == some 0).isSome
          && (body.find? fun x => projIndex x == some 1).isSome then return "cons"
      if body.hasLooseBVars then plain f else plain body
  | _ =>
    match f.getAppFnArgs with
    | (``Prod.fst, _) => return "π₁"
    | (``Prod.snd, _) => return "π₂"
    | _ => plain f

end

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

def seqPic (items : Array Pic) (seams : Array (Nat × Array String)) (objs : Array Obj) : Pic :=
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

/-- Which interior objects a run prints, one label per strand: an interior seam exactly when its
    object is ONE wire and differs from both printed neighbours (CIRCUIT-GEN §3). -/
def seamsOf (objs : Array Obj) : Array (Nat × Array String) := Id.run do
  let mut out := #[]
  let mut prev := objs[0]!
  for i in [0 : objs.size - 2] do
    let o := objs[i + 1]!
    let single := match o.wires with | .ok ws => ws.size == 1 | .error _ => false
    if single && !o.same prev && !o.same objs[i + 2]! then
      out := out.push (i, #[o.label]); prev := o
  return out

/-- The node kind a picture is, for the clauses that ask (a `°` flips a BOX and frames anything
    else; a run splices into the run above it). -/
def Val.kindOf : Val → Option String
  | .dict kvs => kvs.findSome? fun (k, v) =>
      if k == "k" then (match v with | Val.s t => some t | _ => none) else none
  | _ => none

def Val.flag (v : Val) (name : String) : Bool :=
  match v with
  | .dict kvs => kvs.any fun (k, x) => k == name && (match x with | Val.b y => y | _ => false)
  | _ => false

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
    a graph and an identity are maps, a transpose is a map, and a hypothesis in scope says so for
    a variable. -/
partial def isMapOf (e : Expr) : MetaM Bool := do
  match e.getAppFnArgs with
  | (``Freyd.Alg.RelSet.graph, _) | (``Cat.id, _) | (``Freyd.Alg.Λ, _) => return true
  | (``Cat.comp, args) =>
    match lastTwo args with
    | some (f, g) => return (← isMapOf f) && (← isMapOf g)
    | none => hasMapHyp e
  | _ => hasMapHyp e

/-- The `E a` of an object: the power object as a LABEL, which is all the picture needs of it. -/
def powLabel (a : Obj) : Obj := .mk (applyLabel "E" a.label) .opaq #[]

def wiresOf (o : Obj) : MetaM (Array Obj) :=
  match o.wires with
  | .ok ws => return ws
  | .error m => throwError m

/-- A DEFINED arrow opened to its body, on the same test `leaf` uses: a name the labeller keeps is
    never opened, and a body with no clause has no circuit inside it.  Every clause that matches on
    a factor's HEAD must go through this, or a rule fires on `[f,g]` written out and misses the same
    junction under the name a `def` gave it. -/
def openDef (e : Expr) : MetaM Expr := do
  if isNamed e then return e
  match ← Meta.unfoldDefinition? e with
  | some v => let b := v.headBeta; return (if hasClause b then b else e)
  | none => return e

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
      return #[frac, boxPic ("E(" ++ (← arrLabel r) ++ ")") #[powLabel rs] #[powLabel rt]
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
  let seams := seamsOf objs
  if h : items.size == 1 && seams.isEmpty then
    return items[0]'(by simp at h; omega)
  return seqPic items seams objs

partial def runParts (e : Expr) : MetaM (Array Pic × Array Obj) := do
  let items ← drawItems e
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
  -- §3 row 17: the fold as MELLIÈS' FUNCTORIAL BOX — the algebra's own circuit between two bars.
  -- Nothing crosses the LEFT pair: the input arrives at them and the algebra's strands start
  -- inside, and that break IS the recursion.  The carrier labels the output wire only where it
  -- differs from that wire's own label; a product carrier is already drawn as its wires.
  | (``Freyd.Alg.relCata, args) =>
    match args.back? with
    | some r =>
      let body ← lane (← drawRun r)
      let cw ← wiresOf tgt
      let named := cw.size == 1 && cw[0]!.label != tgt.label
      return mkPic "cata" #[src] cw src tgt body.isMap
        #[("body", body.val), ("label", if named then .s tgt.label else .nul),
          ("port", .arr (body.ins.map fun o => .s o.label))]
    | none => leaf e src tgt
  | _ => leaf e src tgt

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
      throwError "`{← arrLabel r}°` writes `°` on a composite, which is the cup/cap frame of \
        CIRCUIT-GEN §3 row 8 — `cpanel` has no node for it"
    return boxPic (← arrLabel r) p.outs p.ins src tgt false
      (frac := p.val.flag "frac") (flip := !(p.val.flag "flip"))

/-- §3 rows 1-2: an atom.  A relation's chamfer says which way it runs; a map is a rectangle.

    A DEFINED arrow is drawn by its DEFINITION when that definition is built from operators this
    functor has a clause for: `consR` is the graph of a cons cell, so it is the rectangle a map
    gets and not the chamfered box its name alone would have produced.  An arrow the labeller
    names — `est(R)`, `Λ(R)`, `∋` — is never unfolded: its own spelling is the picture's. -/
partial def leaf (e : Expr) (src tgt : Obj) : MetaM Pic := do
  if !(isNamed e) then
    if let some v ← Meta.unfoldDefinition? e then
      if hasClause v then return ← draw v
  return boxPic (← arrLabel e) (← wiresOf src) (← wiresOf tgt) src tgt (← isMapOf e)

partial def lane (p : Pic) : MetaM Pic := do
  if p.val.kindOf == some "seq" then return p
  return { p with val := nodeOf "seq" p.ins.size p.outs.size (extra :=
    #[("items", .arr #[p.val]), ("seams", .arr #[])]) }

partial def stackPic (fs : Array Expr) (src tgt : Obj) : MetaM Pic := do
  let ls ← fs.mapM fun f => do lane (← drawRun f)
  let ins := ls.foldl (fun a l => a ++ l.ins) #[]
  let outs := ls.foldl (fun a l => a ++ l.outs) #[]
  return mkPic "stack" ins outs src tgt (ls.all (·.isMap)) #[("lanes", .arr (ls.map (·.val)))]

/-- §3 row 13.  The coproduct arrives as ONE wire, the fork being what opens it; each arm opens
    that wire into its summand's strands, and the seam after the generator names them. -/
partial def casePic (f g : Expr) (src tgt : Obj) (fuse : Option Expr) : MetaM Pic := do
  let ss := src.parts
  if ss.size != 2 then
    throwError "a case forks {ss.size} summands, and the tape fork draws two"
  let mut bodies : Array Pic := #[]
  let mut isMap := true
  let arms : Array (Expr × Obj × Bool) := #[(f, ss[0]!, false), (g, ss[1]!, true)]
  for arm in arms do
    let (br, s, last) := (arm.1, arm.2.1, arm.2.2)
    let (items, objs) ← runParts br
    let ws ← wiresOf s
    let op := mkPic "open" #[src] ws src s true #[]
    -- the fused `𝟙×R` lands on the strands the functor recurses on: the summand's factors that
    -- ARE `R`'s source, the others staying bare wire
    let (items, objs) ← match fuse with
      | some r =>
        if last then do
          let pre ← fusedStack s r
          pure (#[pre] ++ items, #[s] ++ objs)
        else pure (items, objs)
      | none => pure (items, objs)
    let items := #[op] ++ items
    let objs := #[src] ++ objs
    let seams := (if ws.isEmpty then #[] else #[(0, ws.map (·.label))])
      ++ (seamsOf objs).filter (·.1 != 0)
    let body := seqPic items seams objs
    bodies := bodies.push body
    isMap := isMap && body.isMap
  return mkPic "case" #[src] bodies[0]!.outs src tgt isMap
    #[("bodies", .arr (bodies.map (·.val)))]

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
  let t := if outs.size == 1 then outs[0]! else
    .mk (String.intercalate "×" (outs.toList.map Obj.label)) .prod outs
  return mkPic "stack" ins outw s t false #[("lanes", .arr (ls.map (·.val)))]

/-- §3 rows 2/3/14: a map given by a function.  A constant DISCARDS every input strand at a dot
    and creates its value; a projection ends the factors it drops at a dot and crosses the one it
    keeps, costing no box at all; anything else is a rectangle. -/
partial def graphPic (f : Expr) (src tgt : Obj) : MetaM Pic := do
  let ws ← wiresOf src
  let fw ← Meta.whnfD f
  match fw with
  | .lam _ _ body _ =>
    if !body.hasLooseBVars then
      let bx := boxPic (← mapLabel f) #[] (← wiresOf tgt) src tgt true
      if ws.isEmpty then return bx
      return mkPic "konst" ws (← wiresOf tgt) src tgt true #[("body", (← lane bx).val)]
    match projIndex body with
    | some i =>
      if src.kind != .prod || i ≥ src.parts.size then
        throwError "a projection out of {src.label}, which is not a product of {i + 1} factors"
      let keep ← src.parts.mapM fun p => do return (← wiresOf p).size
      return mkPic "proj" ws (← wiresOf tgt) src tgt true
        #[("at", .n i), ("label", .s (if i == 0 then "π₁" else "π₂")),
          ("keep", .arr (keep.map .n))]
    | none => return boxPic (← mapLabel f) ws (← wiresOf tgt) src tgt true
  | _ => return boxPic (← mapLabel f) ws (← wiresOf tgt) src tgt true

end

/-! ### The page

The emitted file calls `cpanel` — the note's own constructor, unchanged — so the generated picture
and the note's are the same drawing routine over the same tree, and any difference between them is
a difference of TREE. -/

/-- The relation between the two sides of a statement, and the sides. -/
def split (e : Expr) : Option (String × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Freyd.Alg.le, args) => (lastTwo args).map fun (l, r) => ("⊑", l, r)
  | (``LE.le, args) => (lastTwo args).map fun (l, r) => ("≤", l, r)
  | (``Eq, args) => (lastTwo args).map fun (l, r) => ("=", l, r)
  | _ => none

/-- A statement whose head is a DEFINITION returning `Prop` — `MonotonicAlg S R`, `Entire R`,
    `Map f` — is the relation it unfolds to, so the picture is of the inequation the reader sees,
    not of one box carrying the predicate's name.  Delta on the HEAD CONSTANT only
    (`unfoldDefinition?`), never `whnf`: a full weak-head normalisation would keep going into the
    arrows themselves, and a `RelSet` arrow's body is a pointwise `fun x y => …` with no circuit in
    it.  It stops the moment `split` recognises the head, so nothing beyond the relation is opened. -/
partial def toRelation (e : Expr) : MetaM Expr := do
  if (split e).isSome then return e
  unless ← Meta.isProp e do return e
  match ← Meta.unfoldDefinition? e with
  | some e' => toRelation e'
  | none => return e

/-- The panel: the tree with its ports named, one label per STRAND — a product is two wires, so it
    is two labels, never one reading `A×[A]`. -/
def panel (e : Expr) : MetaM Val := do
  let p ← drawRun e
  match p.val with
  | .dict kvs => return .dict (kvs ++
      #[("src", .arr (p.ins.map fun o => .s o.label)),
        ("tgt", .arr (p.outs.map fun o => .s o.label))])
  | v => return v

/-- The declaration's picture.  A `def` is unfolded ONE level and drawn by its body; a theorem is
    split by its relation symbol and the named side drawn.

    A HYPOTHESIS IS A STATEMENT TOO.  `binder` names one binder of the declaration's `∀`-telescope
    and draws ITS type instead of the conclusion, so the greedy theorem's `htrans : R°R° ⊑ R°` is
    a panel of that theorem rather than a picture with no declaration behind it.  The rule is over
    the FORM of the type — every binder of every declaration is reachable this way — not a table of
    the hypotheses somebody wanted; a `def`'s body is not unfolded when a binder is named, since
    the binder belongs to the type. -/
def drawDecl (declName : Name) (side : Option String) (binder : Option String := none) :
    MetaM String := do
  let some ci := (← getEnv).find? declName
    | throwError "no such declaration: {declName}"
  Meta.forallTelescopeReducing ci.type fun xs tybody => do
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
    let e ← match split body, side with
      | some (_, l, _), some "lhs" => pure l
      | some (_, _, r), some "rhs" => pure r
      | some (sym, _, _), _ =>
        throwError "`{declName}` states `_ {sym} _`: name the side to draw, \
          `{declName}.lhs` or `{declName}.rhs`"
      | none, some s => throwError "`{declName}` is not an equation or containment: no `.{s}`"
      | none, _ => pure body
    let tree ← panel e
    let name := declName.toString ++ (match binder with | some h => "#" ++ h | none => "")
      ++ (match side with | some s => "." ++ s | none => "")
    return "// GENERATED by `diag-export --circuit` — do not edit; regenerate with\n\
      //   ./scripts/diag-export --circuit " ++ name ++ "\n\
      #import \"../../cpanel.typ\": *\n\n\
      #let pic = cpanel(" ++ tree.render ++ ",\n  cert: (lean: " ++ tstr name ++ "))\n\n\
      #set page(width: auto, height: auto, margin: 12pt)\n\
      #set text(size: 10pt)\n\n\
      #pic\n"

end Freyd.CircuitDiagram
