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
      return wrap 0 s
  | (``Freyd.Diag.LinearBicat.bcomp, args) => bin 0 " ⨟• " args
  | (``Freyd.Diag.SymMonCat.tensHom, args) => bin 1 " ⊗ " args
  | (``Freyd.Alg.Allegory.inter, args) | (``Freyd.Diag.meet, args) => bin 1 "∩" args
  | (``Freyd.Diag.Biprod.union, args) | (``Freyd.Alg.DistributiveAllegory.union, args) =>
    bin 1 " ∪ " args
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
