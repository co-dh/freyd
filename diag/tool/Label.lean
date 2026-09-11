/-
  `Label` — a term spelled the way the NOTE spells it, for every picture that writes one.

  ONE RULE, THREE USERS.  The string, the circuit and the commutative functor each have to write a
  factor on a bead, on a box or on an arrow, and each spelled it its own way: composition came out
  `F ∋ ≫ S` on a box where the note writes `F(∋)S`, and the same `≫` survived inside `⦇…⦈` and
  `E(…)` because the label there was the raw printer's.  The spelling is decided HERE, once, and
  every label of every picture goes through `label`.

  THE PRINTER IS THE DEFAULT.  Where a constant has a spelling of its own, the fix is an
  `app_unexpander` beside it — or in `diag/StrDiagNames.lean` when the constant lives in `AOP` —
  never a clause below.  The clauses are only what no notation can express: juxtaposition for
  composition, which has no symbol left to parse back; the bracketing that makes it readable; and
  the note's own spacing.
-/
import diag.tool.ExprReader
-- The tape and first-order layers' own operators (`⨟•`, `⊥`, the four generators): `labelAt` is one
-- rule over both towers, so it has to see both.
import diag.FO
import diag.Tape
import diag.S2_124
-- `est`, the one operator of the allegory layer that lives above `ExprReader`'s own import, and the
-- type functor, whose action on an arrow is spelled here rather than by a notation (no term prints
-- its own brackets, and `T(f)` is brackets).
import AOP.A7_1
import AOP.A5_5_TypeFunctor
-- The graph of a function, the one arrow whose content is a Lean TERM and not an operator: its
-- name is read off that term, here, so every picture writes the same one.
import AOP.A6_1_RelSet

open Lean

namespace Freyd.StrDiag

/-- The note's juxtaposition spacing (`scripts/relexpr.py`'s `spell`, the same rule the note's own
    generator writes back with): a bracket already separates two factors, so `F(∋)S` and `π₂R°`
    close up where `prefix list(p)` and `S%∋ est(R°)` cannot.  A factor OPENING with `(` keeps its
    space — `pick (schedule×𝟙)snoc` closed up would read as an application of `pick`. -/
def juxt (a b : String) : String :=
  if a.isEmpty || b.isEmpty then a ++ b
  else if ")]⟩⦈}".contains a.back || "[⟨⦇{".contains b.front then a ++ b
  else a ++ " " ++ b

/-- The heads the note sets TIGHT: a relator's action on an object, the power object and the
    existential image, the product and the fork.  Lean's formatter always sets an application's
    argument off from its head (`F T`, `E A`) and an infix off from its operands (`A × B`,
    `⟨f, g⟩`) where the note closes them up; the SPELLING is untouched — it is what the
    `app_unexpander` beside the constant already printed. -/
def tightHeads : Array Name :=
  #[``Freyd.Functor.obj, ``Freyd.Alg.PowerAllegory.powerObj, ``Freyd.Alg.existsImage,
    ``Freyd.HasBinaryProducts.prod, ``Freyd.HasBinaryProducts.pair]

/-! ### A MAP, named from its own function

A relation given as the graph of a function has no operator inside it, so no clause of `labelAt`
can reach its content: its name is read off the FUNCTION'S BODY — a projection is a `π`, a
constructor fed the input's factors is the carrier's structure map, a body that ignores the input
is a discard.  One rule, so a map is named the same wherever it is spelled: on the box the circuit
draws for it, and inside the `E(…)` or `⦇…⦈` of a label. -/

/-- Which factor of a product a projection keeps, read off the function's own body. -/
def projIndex (body : Expr) : Option Nat :=
  match body with
  | .proj ``Prod i _ => some i
  | _ => match body.getAppFnArgs with
    | (``Prod.fst, _) => some 0
    | (``Prod.snd, _) => some 1
    | _ => none

/-- The name of a value computed FROM THE INPUT, in diagram order: `p(π₁ s)` is `π₁p` — first the
    projection, then the test.  The input itself is the identity and contributes nothing, and an
    argument that does not mention the input is a PARAMETER of the function, not a step of the
    computation, so it stays inside the function's own name. -/
partial def valLabel (s : FVarId) (x : Expr) : MetaM String := do
  if x == .fvar s then return ""
  match x with
  | .proj ``Prod i st => return (← valLabel s st) ++ (if i == 0 then "π₁" else "π₂")
  | _ =>
    let args := x.getAppArgs
    match x.getAppFnArgs.1, args.back? with
    | ``Prod.fst, some st => return (← valLabel s st) ++ "π₁"
    | ``Prod.snd, some st => return (← valLabel s st) ++ "π₂"
    | _, _ =>
      let deps := args.filter fun a => a.containsFVar s
      if deps.size == 1 then
        let rest := args.filter fun a => !a.containsFVar s
        return (← valLabel s deps[0]!) ++ (← plain (mkAppN x.getAppFn rest))
      plain x

/-- Beta at the head, to a fixed point.  An alternative reconstructed from a `match` arrives as a
    lambda applied to the summand's factors, and the lambda it names may itself be one; nothing
    beyond beta is reduced, because a NUMERAL delta-reduces to a constructor and would then read as
    the carrier's empty structure map. -/
partial def betaHead (e : Expr) : Expr :=
  let e' := e.headBeta
  if e' == e then e else betaHead e'

mutual

/-- The BODY of a map, named as an arrow out of the input `s`: a body that does not mention `s` is
    a constant, one that projects is a `π`, and a constructor fed the input's factors is the
    carrier's own structure map. -/
partial def bodyLabel (s : FVarId) (body₀ f : Expr) : MetaM String := do
  -- WHAT THE MAP DOES, not how it was written: an arm reconstructed from a `match` arrives as the
  -- alternative applied to the summand's factors.  The fallback still prints what was written.
  let body := betaHead body₀
  match projIndex body with
  | some 0 => return "π₁"
  | some _ => return "π₂"
  | none =>
    if let some g ← guardLabel s body then return g
    -- The book's names for the two structure maps of a list-like carrier, read off the TERM:
    -- a CONSTRUCTOR fed both factors of the input pair is `cons`, and one fed nothing from the
    -- input is `nil`.  Nothing here knows `List`: the next carrier built the same way gets the
    -- same names without a line being added.
    let isCtor ← match body.getAppFn with
      | .const n _ => match (← getEnv).find? n with
        | some (.ctorInfo _) => pure true
        | _ => pure false
      | _ => pure false
    if isCtor && !body.containsFVar s then return "nil"
    if isCtor && (body.find? fun x => projIndex x == some 0).isSome
        && (body.find? fun x => projIndex x == some 1).isSome then return "cons"
    if body₀.containsFVar s then plain f else plain body₀

/-- A `match` on a BOOLEAN test wires nothing — both arms leave on the same strands — so the note
    writes it into the box's own name: `(π₁p→cons,⊸ nil)`, the test, the arm taken when it holds,
    and the other.  The arms are read by REDUCING the matcher at each value of `Bool`, so nothing
    here depends on the order the alternatives were written in or on how the `match` compiled. -/
partial def guardLabel (s : FVarId) (body₀ : Expr) : MetaM (Option String) := do
  -- A step is a `def` around its own `match`, so the matcher is behind one delta; the ARMS are then
  -- taken by `whnfCore`, which fires the matcher without unfolding a numeral into a constructor.
  let some ma ← Meta.matchMatcherApp? (← Meta.whnfD body₀) | return none
  unless ma.discrs.size == 1 && ma.alts.size == 2 && ma.remaining.isEmpty do return none
  unless (← Meta.whnfD (← Meta.inferType ma.discrs[0]!)).isConstOf ``Bool do return none
  let hd := mkAppN (mkConst ma.matcherName ma.matcherLevels.toList) ma.params
  -- An ARM is a map like any other, and it is written INSIDE this label, so its discard is written
  -- too: one rule decides the `⊸`, and it is `mapLabel`'s.
  let arm (v : Name) : MetaM String := do
    let b ← Meta.whnfCore (mkAppN hd (#[ma.motive, mkConst v] ++ ma.alts))
    mapLabel (← Meta.mkLambdaFVars #[.fvar s] b) false
  return some ("(" ++ (← valLabel s ma.discrs[0]!) ++ "→" ++ (← arm ``Bool.true) ++ ","
    ++ (← arm ``Bool.false) ++ ")")

/-- The label of a MAP given by its function.  A cons cell is `cons`, a projection its `π`, a
    constant the thing it creates — each read off the function's own body, so the next map built
    the same way gets the same name without anything being added here.

    `wired` is whether the PICTURE carries the map's discard: a box drawn for a constant map has no
    input port, and that missing port IS the `⊸`, so the box's own label does not write one.  The
    same map written inside another label — `E(…)`, `⦇…⦈`, the arm of a guard — has no port to say
    it, so there the `⊸` is written. -/
partial def mapLabel (f : Expr) (wired : Bool) : MetaM String := do
  let f ← Meta.whnfD f
  if f.isLambda then
    return ← Meta.lambdaBoundedTelescope f 1 fun xs body => do
      let some x := xs[0]? | plain f
      let l ← bodyLabel x.fvarId! body f
      if wired || (betaHead body).containsFVar x.fvarId!
          || !(← hasStrands (← Meta.inferType x)) then return l
      return "⊸ " ++ l
  match f.getAppFnArgs with
  | (``Prod.fst, _) => return "π₁"
  | (``Prod.snd, _) => return "π₂"
  | _ => plain f

end

/-- A term, spelled the way the BOOK spells it — juxtaposition for composition, `°` for the converse
    — rather than left to the pretty printer, because it is read beside a picture, where
    `CartBicat.conv S` is noise and `S°` is the thing itself.  `°`, not the paper's `†`: these terms
    are read against Freyd throughout, and one symbol per idea beats matching two.

    PARENTHESISED BY PRECEDENCE, composition loosest and `°` tightest, so the bracketing is visible.
    That matters: several steps of a `calc` do nothing but re-bracket, and the term column is the
    only place a reader can see them happen — the picture, quite correctly, does not change.

    RECURSIVE THROUGH THE BRACKETING OPERATORS TOO.  `⦇…⦈`, `E(…)` and `…%∋` delimit their operand,
    so a composite inside one is still a composite of the note's: `⦇S%∋ est(R°)⦈`, never
    `⦇S%∋ ≫ est(R°)⦈`, which is what the raw printer hands back for the whole application. -/
partial def labelAt (prec : Nat) (e : Expr) : MetaM String := do
  -- A NAME THE NOTE DRAWS OPENED is opened wherever it is SPELLED, not only where a factor of a
  -- composite is drawn: a case study's middle bead is ONE bead `⦇Salg⦈` whose whole content is the
  -- algebra, and `@[diag_unfold]` is the statement that the note writes that algebra out.
  let e' ← openNoted e
  if e' != e then return ← labelAt prec e'
  let wrap (p : Nat) (s : String) : String := if prec > p then "(" ++ s ++ ")" else s
  -- `cp` is the precedence the OPERANDS are set at, which is not always one above the operator's:
  -- composition is written by juxtaposition, so it has no symbol to separate its operands and every
  -- operand that is itself an operator has to carry brackets or `R (S ∩ T)` comes out reading as
  -- `(R S) ∩ T`.
  -- An operand is an ARROW, picked by its TYPE and not by its position: `I.cata f hf` carries the
  -- algebra AND the proof it is one, and taking the last argument wrote `⦇hf⦈` for `⦇f⦈`.
  let arrows (args : Array Expr) : MetaM (Array Expr) :=
    args.filterM fun a => return (homObjs? (← Meta.inferType a)).isSome
  let bin (p : Nat) (op : String) (args : Array Expr) (cp : Nat := p + 1) : MetaM String := do
    match lastTwo (← arrows args) with
    | some (f, g) => return wrap p ((← labelAt cp f) ++ op ++ (← labelAt cp g))
    | none => plain e
  -- The one argument of a unary operator, at the precedence its operand is set at.
  let un (p cp : Nat) (pre post : String) (args : Array Expr) : MetaM String := do
    match (← arrows args).back? with
    | some r => return wrap p (pre ++ (← labelAt cp r) ++ post)
    | none => plain e
  match e.getAppFnArgs with
  | (``Cat.id, _) => return "𝟙"
  -- A MAP is named from its own function, wherever it is spelled: the box the circuit draws for it
  -- and the `E(…)` of a label are the same name, so the rule sits here and not beside the drawing.
  | (``Freyd.Alg.RelSet.graph, args) =>
    match args.back? with
    | some f => mapLabel f false
    | none => plain e
  | (``Freyd.Diag.CartBicat.Δ, _) => return "◁"
  | (``Freyd.Diag.CartBicat.«∇», _) => return "▷"
  | (``Freyd.Diag.CartBicat.«!», _) => return "⊸"
  | (``Freyd.Diag.CartBicat.«?», _) => return "⟜"
  -- BY THEIR DEFINITIONS, not by name.  `cap` and `cup` are `def`s over the four generators —
  -- `cap = ▷⊸`, `cup = ⟜◁` — and a term column that prints them as words introduces two more
  -- things to look up, in a note whose whole claim is that everything is built from those four.
  -- The pictures already draw them as the merge and the fork with their dot.
  | (``Freyd.Diag.CartBicat.cap, _) => return "▷⊸"
  | (``Freyd.Diag.CartBicat.cup, _) => return "⟜◁"
  | (``Freyd.Diag.top, _) | (``Freyd.Alg.topHom, _) => return "⊤"
  | (``Freyd.Diag.Biprod.bot, _) => return "⊥"
  -- The allegory's zero keeps the book's own `𝟘`; the tape layer's is `⊥` and they are different
  -- arrows of different towers, so they are not spelled alike.
  | (``Freyd.Alg.DistributiveAllegory.zero, _) => return "𝟘"
  | (``Freyd.Alg.PowerAllegory.eps, _) => return "∋"
  -- No `α`, `λ` or `ρ` cases: this branch's monoidal structure is STRICT, so the coherence arrows
  -- do not exist and no statement can mention one.
  | (``Freyd.Diag.SymMonCat.swap, _) => return "σ"
  -- Composition is JUXTAPOSITION, which is why it cannot be an unexpander: `f g` parses as an
  -- application, so only a labeller may write it.
  -- FLAT, because composition is associative and the picture cannot tell `(fg)h` from `f(gh)`: a
  -- composite operand re-bracketed by the reader's own printer (`S° (F(X)R)`) is one more thing to
  -- undo, so the whole run is written as the note writes it.
  | (``Cat.comp, args) =>
    if lastTwo args |>.isNone then plain e else do
      let fs := factors e
      let mut s := ""
      for f in fs do s := juxt s (← labelAt 2 f)
      -- JUXTAPOSITION BINDS TIGHTER THAN THE LATTICE OPERATORS, as `relexpr.py`'s own `spell` sets
      -- them: `⊸ nil ∪ (p×𝟙)cons` is a union of two composites and needs no brackets, where
      -- `old (R∩H)` does — so composition sits ABOVE `∩`/`∪` and below `°`.
      return wrap 1 s
  | (``Freyd.Diag.LinearBicat.bcomp, args) => bin 0 " ⨟• " args
  | (``Freyd.Diag.SymMonCat.tensHom, args) => bin 1 " ⊗ " args
  | (``Freyd.Alg.Allegory.inter, args) | (``Freyd.Diag.meet, args) => bin 0 "∩" args
  | (``Freyd.Diag.Biprod.union, args) | (``Freyd.Alg.DistributiveAllegory.union, args) =>
    bin 0 " ∪ " args
  | (``Freyd.Diag.ClosedLinearBicat.residual, args)
  | (``Freyd.Alg.DivisionAllegory.div, args) => bin 1 " / " args
  -- The note sets the left division TIGHT (`⦇S⦈°\X`, 11.6.4b) where `/` and `∪` keep their spaces.
  | (``Freyd.Alg.leftDiv, args) => bin 1 "\\" args
  | (``Freyd.Alg.symmDiv, args) => bin 1 " /ₛ " args
  | (``Freyd.Alg.impl, args) => bin 1 " ⇨ " args
  | (``Freyd.Alg.thenRel, args) => bin 1 " ⨾ " args
  -- A CONVERSE WITH A NAME OF ITS OWN IS WRITTEN BY THAT NAME (CLAUDE.md): the membership's is `∈`,
  -- and `∋°` makes the reader undo one level of indirection to get back to it.  Decided by the
  -- OPERAND's head constant, so every spelling of `∋` goes the same way.
  | (``Freyd.Alg.Allegory.recip, args) | (``Freyd.Diag.CartBicat.conv, args) => do
    match (← arrows args).back? with
    | some r => if r.isAppOf ``Freyd.Alg.PowerAllegory.eps then return "∈" else un 3 3 "" "°" args
    | none => plain e
  | (``Freyd.Diag.ClosedLinearBicat.perp, args) => un 3 3 "" "⊥" args
  -- `∼` binds tighter than everything but `°`, so its operand is set at `°`'s precedence.
  | (``Freyd.Alg.neg, args) => un 3 3 "∼" "" args
  -- The BRACKETING operators: their own delimiters separate the operand, so it is set at the
  -- loosest precedence and carries no brackets of its own — and, being a term like any other, it
  -- is spelled by this same rule rather than by the printer.
  | (``Freyd.Alg.est, args) => un 4 0 "est(" ")" args
  | (``Freyd.Alg.relCata, args) | (``Freyd.Alg.InitialAlgebra.cata, args) => un 4 0 "⦇" "⦈" args
  | (``Freyd.Alg.Λ, args) => un 2 3 "" "%∋" args
  -- The junction's own brackets delimit its operands (`[nil,⊸ nil ∪ cons]`, 13.3.3b): loosest
  -- precedence inside, nothing after the comma, as the note sets it.
  | (``Freyd.Alg.junc, args) => do
    match lastTwo (← arrows args) with
    | some (f, g) => return "[" ++ (← labelAt 0 f) ++ "," ++ (← labelAt 0 g) ++ "]"
    | none => plain e
  -- The TYPE FUNCTOR's action on an arrow is a relator's action like any other, so it takes the same
  -- brackets as `F(R)`: `T(f)`, never `T f`, juxtaposition being composition and nothing else.  The
  -- letter is `typeRelator`'s own unexpander's (`diag/StrDiagNames.lean`), which the lane wears too.
  | (``Freyd.Alg.typeMap, args) => un 4 0 "T(" ")" args
  -- The LEAST FIXED POINT is the note's `(μX : S°F(X)R)`.  Its body is a term of the note's like any
  -- other — the binder is an arrow the picture draws a wire for — so its composition is
  -- juxtaposition, where the printer's own `≫` survived because the label was the raw printer's.
  | (``Freyd.Alg.mu, args) =>
    match args.back? with
    | some φ => Meta.lambdaBoundedTelescope φ 1 fun xs b => do
      match xs[0]? with
      | some x => return "(μ" ++ (← x.fvarId!.getUserName).toString ++ " : " ++ (← labelAt 0 b) ++ ")"
      | none => plain e
    | none => plain e
  -- A relator's action on an ARROW is the ONE bracket no term carries: `F(⦇R⦈)`, the note's way of
  -- saying the argument is applied and not composed.
  | (``Freyd.Functor.map, _) =>
    match functorMap? e with
    | some (f, r) => return (← labelAt 4 f) ++ "(" ++ (← labelAt 0 r) ++ ")"
    | none => plain e
  | (c, args) =>
    if tightHeads.contains c then return (← plain e).replace " " "" else do
    -- A PRODUCT OF ARROWS is its two arrows and nothing else.  The head's own printer writes the
    -- OBJECT it is taken at too (`wrap × 𝟙 [[X]]`), and an object inside a bead's label is the wire
    -- under it spelled twice; read as a product map off the TYPE, so every spelling goes one way.
    if let some (x, _) := homObjs? (← Meta.inferType e) then
      if let some (φ, ψ) ← asProdMap? (← Meta.inferType x) e then
        return wrap 1 ((← labelAt 2 φ) ++ "×" ++ (← labelAt 2 ψ))
    -- EVERY OTHER HEAD KEEPS THE PRINTER'S SPELLING — a delimited notation (`thin(Q)`) is the
    -- constant's own business, and a clause here would be a second copy of it — but its ARROW
    -- arguments are terms of the note's like any other, so each is respelled HERE and handed back to
    -- the printer as a local of that name.  That is what turns the operand of a head with no clause
    -- from Lean's `≫` into juxtaposition, under whatever brackets the head already writes.
    let hom ← arrows args
    let rec go : List Expr → Expr → MetaM String
      | [], t => plain t
      | a :: rest, t => do
        let nm := Name.mkSimple (← labelAt 4 a)
        Meta.withLocalDeclD nm (← Meta.inferType a) fun x =>
          go rest (t.replace fun s => if s == a then some x else none)
    go hom.toList e

/-- A label at the top of its own picture or box: no outer parentheses. -/
def label (e : Expr) : MetaM String := labelAt 0 e

end Freyd.StrDiag
