/-
  LeetCode 303 — Range Sum Query - Immutable — DERIVED as a cons-list catamorphism.

  `leet/L303.lean` WRITES `scanlAdd a (x :: xs) = a :: scanlAdd (a + x) xs`, `scanlAdd a [] = [a]`
  — a plain hand-written structural recursion on the raw Lean `List Int` (the prefix-sum SCAN).

  This file RESHAPES `scanlAdd` onto the canonical cons-list initial algebra `ConsList Unit Int`
  (`CL.ofList`, `AOP/A6_ConsList.lean`, front-to-back: `[] ↦ wrap ()`, `x :: xs ↦ cons x
  (ofList xs)`) and produces it as the catamorphism of an EMERGENT algebra via the general-carrier
  law `CL.consFold_unique` (`AOP/A6_GenFold.lean`) — the exact same CPS-carrier shape as
  `leet/L238_derived.lean`'s prefix-product scan `preScan`:

  **CPS/continuation carrier `Int → List Int`.**  A plain cons-fold recurses on the TAIL first, so
  it has no left-accumulated running sum to hand the step; the fix is to curry the running sum INTO
  the carrier: `C := Int → List Int`, "given the running sum so far, the prefix-sums list for the
  rest, terminated by the running sum itself" (unlike `L238`'s exclusive `preScan`, `scanlAdd`'s base
  case still EMITS `a`, producing a list one longer than the input — `P.length = nums.length + 1`).
  Base/step are forced (`rfl` against `LC303.scanlAdd`):
    * base `g _   = fun a => [a]`                       `= foldScan (wrap _)`
    * step `st x k = fun a => a :: k (a + x)`            `= foldScan (cons x xs)` with `k = foldScan xs`.
  `consFold_unique` then EMITS `scanlAdd`'s own accumulator-passing recursion as
  `cataR (consScalarAlg g st)` — the accumulator threading is produced by the law, not hand-written.

  The carrier only ever CONS onto the front of a list (`a :: …`, never `acc ++ [x]`), so building
  the prefix-sum table stays `O(n)`.  Each RANGE QUERY then reads the precomputed table via
  `List.getElem?`, which is `O(i)` (`List.getElem?` walks from the head) — `O(1)` worst-case queries
  would need upgrading the carrier's output from `List Int` to `Array Int` (a routine change, not
  done here — the derivation is about the FOLD, not the read-out data structure).

  CORRECTNESS is REUSED, not re-proved (headline shape 1 — equality refinement: the answer is an
  exact function of `(nums, i, j)`, not an extremum to dominate).  The bridge `foldScan_ofList` shows
  the reshaped fold computes exactly `LC303.scanlAdd` on converted input; hence
  `derivedSumRangeFn = LC303.sumRangeFn` on the nose, and `LC303.sumRange_correct`/`solve_correct`
  transfer unchanged — no new correctness proof about prefix sums is needed.

  Mathlib-free (Lean core + `Freyd.*` only); headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L303

namespace Freyd.Alg.RelSet.LC303D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The prefix-sum scan via the CPS carrier `Int → List Int` -/

/-- The continuation carrier: given the running sum `a` accumulated so far, the prefix-sums list
    for the rest of the (unprocessed) suffix, terminated by the running sum itself. -/
abbrev ScanCarrier : Type := Int → List Int

/-- Base: an empty suffix contributes only the terminal running sum `a`. -/
def scanG : Unit → ScanCarrier := fun _ => fun a => [a]

/-- Step: prepend element `x` to the folded-tail continuation `k`.  Given the running sum `a`, EMIT
    `a` (the prefix sum up to here) and hand the updated running sum `a + x` on to `k`. -/
def scanSt : Int → ScanCarrier → ScanCarrier := fun x k => fun a => a :: k (a + x)

/-- The prefix-sum scan as a fold over the cons-list initial algebra, mirroring `LC303.scanlAdd`:
    `wrap _ ↦ (fun a => [a])`, `cons x xs ↦ scanSt x (foldScan xs)`. -/
def foldScan : ConsList Unit Int → ScanCarrier
  | ConsList.wrap _    => fun a => [a]
  | ConsList.cons x xs => scanSt x (foldScan xs)

/-- The base condition is a COMPUTATION: `foldScan (wrap d) = scanG d`. -/
theorem foldScan_wrap : ∀ d : Unit, foldScan (ConsList.wrap d) = scanG d := fun _ => rfl

/-- The step condition IS `foldScan`'s cons equation. -/
theorem foldScan_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), foldScan (ConsList.cons x xs) = scanSt x (foldScan xs) :=
  fun _ _ => rfl

/-- **The scan fold EMERGES** via the general-carrier cons-fold law: reshaped onto
    `ConsList Unit Int`, `scanlAdd` IS the catamorphism of `consScalarAlg scanG scanSt` — the
    accumulator-passing recursion was never hand-written. -/
theorem scanlAdd_emerges :
    (graph foldScan : dCL Unit Int ⟶ ⟨ScanCarrier⟩) = cataR (consScalarAlg scanG scanSt) :=
  consFold_unique scanG scanSt foldScan foldScan_wrap foldScan_cons

/-- The reshaped fold agrees with `LC303.scanlAdd` on converted input, at every running sum `a`. -/
theorem foldScan_ofList (xs : List Int) (a : Int) :
    foldScan (ofList xs) a = LC303.scanlAdd a xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      show a :: foldScan (ofList xs) (a + x) = LC303.scanlAdd a (x :: xs)
      rw [LC303.scanlAdd_cons, ih (a + x)]

/-! ## The derived program: rebuild `prefixSums`/`sumRangeFn` from the reshaped fold -/

/-- **The derived prefix-sums table**: `foldScan` started at running sum `0` — exactly
    `LC303.prefixSums`. -/
def derivedPrefixSums (nums : List Int) : List Int := foldScan (ofList nums) 0

/-- The derived table agrees with `LC303.prefixSums` on the nose. -/
theorem derivedPrefixSums_eq (nums : List Int) : derivedPrefixSums nums = LC303.prefixSums nums :=
  foldScan_ofList nums 0

/-- **The derived program**: query into the derived prefix-sums table by subtraction, exactly as
    `LC303.sumRangeFn` reads `LC303.prefixSums`. -/
def derivedSumRangeFn (nums : List Int) (i j : Nat) : Int :=
  ((derivedPrefixSums nums)[j + 1]?.getD 0) - ((derivedPrefixSums nums)[i]?.getD 0)

/-- **Equality refinement (headline shape 1)**: the derived program computes EXACTLY
    `LC303.sumRangeFn` — the answer here is an exact function, not an extremum, so no
    soundness/dominance packaging is needed, only this equality. -/
theorem derivedSumRangeFn_eq (nums : List Int) (i j : Nat) :
    derivedSumRangeFn nums i j = LC303.sumRangeFn nums i j := by
  unfold derivedSumRangeFn LC303.sumRangeFn
  rw [derivedPrefixSums_eq]

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The derived allegory program's underlying function**: LeetCode 303's solution, reshaped as a
    cons-list catamorphism, packaged as `LC303.solve`'s own function shape. -/
def derivedSolveFn (t : List Int × Nat × Nat) : Int := derivedSumRangeFn t.1 t.2.1 t.2.2

theorem derivedSolveFn_eq (t : List Int × Nat × Nat) :
    derivedSolveFn t = LC303.sumRangeFn t.1 t.2.1 t.2.2 :=
  derivedSumRangeFn_eq t.1 t.2.1 t.2.2

/-- **The derived allegory program**: LeetCode 303's solution, reshaped as a cons-list
    catamorphism, as a morphism `Query ⟶ ℤ` in `Rel(Set)`. -/
def derivedSolve : LC303.Query ⟶ LC303.dZ := graph derivedSolveFn

/-- The derived morphism equals `LC303.solve` — both are graphs of pointwise-equal functions. -/
theorem derivedSolve_eq_solve : derivedSolve = LC303.solve := by
  unfold derivedSolve LC303.solve
  rw [funext derivedSolveFn_eq]

/-! ## Headline: emergence + reused correctness -/

/-- **Headline.**  The honest bundle:

    (1) the CPS-carrier fold EMERGES from `CL.consFold_unique` (`scanlAdd_emerges`) — the
        accumulator-passing recursion in `LC303.scanlAdd` was never hand-written as a catamorphism;
    (2) the reshaped program equals `LC303.sumRangeFn` EXACTLY (`derivedSumRangeFn_eq`,
        `derivedSolve_eq_solve`) — headline shape 1, since the answer is a genuine function of the
        query; and
    (3) that answer is honestly correct — the honest slice sum `LC303.rangeSum`, for every
        well-formed in-range query — the REUSED `LC303.sumRange_correct`, not re-proved here.

    The program (the fold) is PRODUCED by the law; correctness is reused; only the DATA structure
    (front-to-back cons-list, CPS carrier) was changed. -/
theorem derived_correct :
    ((graph foldScan : dCL Unit Int ⟶ ⟨ScanCarrier⟩) = cataR (consScalarAlg scanG scanSt))
      ∧ (∀ nums i j, derivedSumRangeFn nums i j = LC303.sumRangeFn nums i j)
      ∧ (∀ nums i j, i ≤ j + 1 → j < nums.length →
          derivedSumRangeFn nums i j = LC303.rangeSum nums i j) :=
  ⟨scanlAdd_emerges, derivedSumRangeFn_eq,
    fun nums i j hij hj => (derivedSumRangeFn_eq nums i j).trans
      (LC303.sumRange_correct nums i j hij hj)⟩

/-! ## Running the derived program -/

-- LeetCode 303's own example: `nums = [-2, 0, 3, -5, 2, -1]`, `sumRange(0,2) = 1`,
-- `sumRange(2,5) = -1`.
example : derivedSumRangeFn [-2, 0, 3, -5, 2, -1] 0 2 = 1 := by decide
example : derivedSumRangeFn [-2, 0, 3, -5, 2, -1] 2 5 = -1 := by decide

end Freyd.Alg.RelSet.LC303D
