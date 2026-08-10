/-
  Bird & de Moor, *Algebra of Programming* §10.2  The detab–entab problem (book pp. 246-247) —
  a worked program in the Set model, over snoc-lists of characters.

  `detab` replaces tabs by the right number of blanks to reach the next tab stop (every `n`
  columns).  Naively `detab = ⦇[nil, expand]⦈`, but `expand` needs the current column, so B&dM
  TUPLE `detab` with `col` (the column counter): `(detab, col·detab) = ⦇[base, step]⦈`, a single
  snoc-list catamorphism carrying `(output, column)`, implemented as a loop.  We build that tupled
  catamorphism concretely (over `SnocList Unit Char` from `AOP.A6_SnocList`) and give its loop
  recursion; `detab` is the first component.
-/
module

public import AOP.A6_SnocList

namespace Freyd.Alg.RelSet.Detab

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.SL

-- Tab width `n`, and the tab / newline / blank characters.
variable (n : Nat) (tb nl blank : Char)

/-- The accumulator: `(output so far, current column)`. -/
@[expose] public abbrev St : RelSet.{0} := ⟨List Char × Nat⟩

/-- The tupled algebra `[base, step]` (B&dM p.247): `base = ([], 0)`, and `step` appends a
    character, resetting the column on a newline, padding with blanks to the next tab stop on a
    tab, and advancing the column by one otherwise. -/
def stepFn : (Fobj Unit Char (St)).carrier → (List Char × Nat)
  | Sum.inl _ => ([], 0)
  | Sum.inr ((x, c), a) =>
      if a = nl then (x ++ [nl], 0)
      else if a = tb then (x ++ List.replicate (n - c % n) blank, c + (n - c % n))
      else (x ++ [a], c + 1)

/-- `[base, step] : F(output×col) → (output×col)`, a map (graph of `stepFn`). -/
def detabAlg : Fobj Unit Char (St) ⟶ St := graph (stepFn n tb nl blank)

/-- **The tupled catamorphism** `(detab, col·detab) = ⦇[base, step]⦈`, carrying `(output, column)`
    through the input in one left-to-right pass (the loop of B&dM p.247). -/
def detabTupled : dSL Unit Char ⟶ St := cataR (detabAlg n tb nl blank)

/-- **§10.2 loop, base case**: on the empty input the accumulator is `([], 0)`. -/
theorem detab_wrap (r : List Char × Nat) :
    detabTupled n tb nl blank (SnocList.wrap ()) r ↔ r = ([], 0) := Iff.rfl

/-- **§10.2 loop, step case**: `⦇[base,step]⦈ (x `snoc` a) = step (⦇[base,step]⦈ x, a)` — the
    iterative loop, appending each character to the running `(output, column)`. -/
theorem detab_snoc (x : SnocList Unit Char) (a : Char) (r : List Char × Nat) :
    detabTupled n tb nl blank (SnocList.snoc x a) r ↔
      ∃ r', detabTupled n tb nl blank x r' ∧ r = stepFn n tb nl blank (Sum.inr (r', a)) :=
  Iff.rfl

/-- `detab` itself is the first component of the tupled catamorphism. -/
def detab : dSL Unit Char ⟶ (⟨List Char⟩ : RelSet.{0}) :=
  detabTupled n tb nl blank ≫ graph Prod.fst

end Freyd.Alg.RelSet.Detab
