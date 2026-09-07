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
-- `est`, the one operator of the allegory layer that lives above `ExprReader`'s own import.
import AOP.A7_1

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
  | (``Cat.comp, args) =>
    match lastTwo args with
    | some (f, g) => return wrap 0 (juxt (← labelAt 2 f) (← labelAt 2 g))
    | none => plain e
  | (``Freyd.Diag.LinearBicat.bcomp, args) => bin 0 " ⨟• " args
  | (``Freyd.Diag.SymMonCat.tensHom, args) => bin 1 " ⊗ " args
  | (``Freyd.Alg.Allegory.inter, args) | (``Freyd.Diag.meet, args) => bin 1 " ∩ " args
  | (``Freyd.Diag.Biprod.union, args) | (``Freyd.Alg.DistributiveAllegory.union, args) =>
    bin 1 " ∪ " args
  | (``Freyd.Diag.ClosedLinearBicat.residual, args)
  | (``Freyd.Alg.DivisionAllegory.div, args) => bin 1 " / " args
  -- The note sets the left division TIGHT (`⦇S⦈°\X`, 11.6.4b) where `/` and `∪` keep their spaces.
  | (``Freyd.Alg.leftDiv, args) => bin 1 "\\" args
  | (``Freyd.Alg.symmDiv, args) => bin 1 " /ₛ " args
  | (``Freyd.Alg.impl, args) => bin 1 " ⇨ " args
  | (``Freyd.Alg.thenRel, args) => bin 1 " ⨾ " args
  | (``Freyd.Alg.Allegory.recip, args) | (``Freyd.Diag.CartBicat.conv, args) => un 3 3 "" "°" args
  | (``Freyd.Diag.ClosedLinearBicat.perp, args) => un 3 3 "" "⊥" args
  -- `∼` binds tighter than everything but `°`, so its operand is set at `°`'s precedence.
  | (``Freyd.Alg.neg, args) => un 3 3 "∼" "" args
  -- The BRACKETING operators: their own delimiters separate the operand, so it is set at the
  -- loosest precedence and carries no brackets of its own — and, being a term like any other, it
  -- is spelled by this same rule rather than by the printer.
  | (``Freyd.Alg.est, args) => un 4 0 "est(" ")" args
  | (``Freyd.Alg.relCata, args) | (``Freyd.Alg.InitialAlgebra.cata, args) => un 4 0 "⦇" "⦈" args
  | (``Freyd.Alg.Λ, args) => un 2 3 "" "%∋" args
  -- A relator's action on an ARROW is the ONE bracket no term carries: `F(⦇R⦈)`, the note's way of
  -- saying the argument is applied and not composed.
  | (``Freyd.Functor.map, _) =>
    match functorMap? e with
    | some (f, r) => return (← labelAt 4 f) ++ "(" ++ (← labelAt 0 r) ++ ")"
    | none => plain e
  | (c, _) =>
    if tightHeads.contains c then return (← plain e).replace " " "" else plain e

/-- A label at the top of its own picture or box: no outer parentheses. -/
def label (e : Expr) : MetaM String := labelAt 0 e

end Freyd.StrDiag
