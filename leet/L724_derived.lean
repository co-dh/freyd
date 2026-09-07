/-
  LeetCode 724 — Find Pivot Index — DERIVED as a cons-list catamorphism, `O(n)`.

  `leet/L724.lean` WRITES `pivotFn nums := pivotScan nums.sum 0 0 nums` as a LEFT-TO-RIGHT scan on the
  raw `List Int`, carrying an accumulator `(i, leftSum)` — the index-so-far and the running left sum —
  against the fixed `total`.  It is a plain structural recursion on the list, but not literally a
  `cataR` as written: this file RESHAPES it onto the canonical cons-list initial algebra
  `ConsList Unit Int` (`AOP.A6_ConsList`) and shows the very same scan EMERGES from the general-carrier
  law `CL.consFold_unique`.

  A plain cons-fold `st : E → C → C` recurses on the TAIL first, so it has no left-accumulated state
  (index, running sum) to hand the step.  The fix, as in `L1_derived`'s hash reshaping, is a FUNCTION
  (continuation-passing) carrier —

    * `C := Nat → Int → Option Nat` — "given the index-so-far and the running left sum, the first pivot
       found from here on" —

  the accumulator-as-continuation (CPS) reshaping: the folded tail is a CONTINUATION awaiting the
  `(index, leftSum)` state that the still-unprocessed prefix will pass down.  The base/step are then
  ordinary and FORCED (`rfl`), mirroring `pivotScan`'s own equations:

    * base `g _        = fun _ _ => none`                                        = `foldCL total (wrap _)`
    * step `st total x k = fun i leftSum =>`
           `if leftSum = total - leftSum - x then some i else k (i + 1) (leftSum + x)`
                                                                                   = `foldCL total (cons x xs)`
                                                                                     with `k = foldCL total xs`

  Feeding `g`/`st total`/`foldCL total` to `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`)
  PRODUCES the accumulator-passing left scan as `cataR (consScalarAlg g (st total))` — the recursion is
  never hand-written, it is EMITTED by the law.

  CORRECTNESS is REUSED, not re-proved: the bridge `foldCL_go` shows the reshaped fold computes exactly
  `LC724.pivotScan` (an easy induction, both sides literally the same `if`-`then`-`else` at each step), so
  the derived program agrees with `LC724.pivotFn` and inherits `LC724.pivot_correct` (soundness, leftmost,
  none-completeness) verbatim — no re-derivation of the scan-invariant induction.

  Complexity: `foldCL` performs exactly one pass over the list — one `find?`-style comparison per element,
  `O(1)` work each — so the derived program is `O(n)`, same order as the original, now packaged as the
  catamorphism the fold-uniqueness law forces it to be.

  Mathlib-free (Lean core + `Freyd.*` only); headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L724

namespace Freyd.Alg.RelSet.LC724D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list FUNCTION (CPS) carrier and its accumulator-carrying scan

  `CL.consFold_unique` carries an arbitrary type `C`; here `C = Nat → Int → Option Nat` — a
  CONTINUATION mapping the index-so-far and the running left sum to the first pivot found from this
  point on.  Currying the left-accumulated state `(i, leftSum)` into the carrier is what lets an
  ordinary cons-fold (recursion on the tail) reproduce `pivotScan`'s left-to-right accumulator scan. -/

/-- The continuation carrier: given the index-so-far and the running left sum, the optional first
    pivot found among the elements folded so far. -/
abbrev Carrier : Type := Nat → Int → Option Nat

/-- The base of the emergent algebra: the empty suffix yields no pivot, whatever the state. -/
def g : Unit → Carrier := fun _ => fun _ _ => none

/-- The step of the emergent algebra: prepend symbol `x` to the folded-tail continuation `k`.  Given
    the index-so-far `i` and running left sum `leftSum`, `x` is a pivot iff `leftSum` equals the
    remaining right sum `total - leftSum - x`; a hit returns `some i` (the EARLY RETURN), a miss hands
    the incremented index and extended sum on to `k`. -/
def st (total : Int) : Int → Carrier → Carrier :=
  fun x k => fun i leftSum =>
    if leftSum = total - leftSum - x then some i else k (i + 1) (leftSum + x)

/-- The pivot scan as a fold over the cons-list initial algebra, mirroring `LC724.pivotScan`:
    `wrap _ ↦ (fun _ _ => none)`, `cons x xs ↦ st total x (foldCL total xs)`. -/
def foldCL (total : Int) : ConsList Unit Int → Carrier
  | ConsList.wrap _    => fun _ _ => none
  | ConsList.cons x xs => st total x (foldCL total xs)

/-- The base condition is a COMPUTATION, not a guess: `foldCL total (wrap d) = g d`. -/
theorem foldCL_wrap (total : Int) : ∀ D : Unit, foldCL total (ConsList.wrap D) = g D :=
  fun _ => rfl

/-- The step condition IS `foldCL`'s cons equation: `foldCL total (cons x xs) = st total x (…)`. -/
theorem foldCL_cons (total : Int) :
    ∀ (x : Int) (xs : ConsList Unit Int),
      foldCL total (ConsList.cons x xs) = st total x (foldCL total xs) :=
  fun _ _ => rfl

/-! ## The scan EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  For each `total`, the pivot scan, RESHAPED onto the cons-list initial algebra
    `ConsList Unit Int`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g (st total)`
    — it was never written as a fold: `graph (foldCL total)` equals `cataR (consScalarAlg g (st total))`.
    Currying the left-accumulated state `(i, leftSum)` into the function carrier is the point: an
    accumulator-passing left scan with early return is emitted by `consFold_unique`. -/
theorem pivot_emerges (total : Int) :
    (graph (foldCL total) : dCL Unit Int ⟶ ⟨Carrier⟩) = cataR (consScalarAlg g (st total)) :=
  consFold_unique g (st total) (foldCL total) (foldCL_wrap total) (foldCL_cons total)

/-! ## Bridge to the hand-written raw-`List` scan -/

/-- The reshaped fold agrees with `LC724.pivotScan` at every state `(i, leftSum)`: both sides unfold
    to the SAME `if`-`then`-`else` test at each cons step, so the bridge is a one-line induction. -/
theorem foldCL_go (total : Int) :
    ∀ (xs : List Int) (i : Nat) (leftSum : Int),
      foldCL total (CL.ofList xs) i leftSum = LC724.pivotScan total i leftSum xs
  | [],      _, _       => rfl
  | x :: xs, i, leftSum => by
      show st total x (foldCL total (CL.ofList xs)) i leftSum = LC724.pivotScan total i leftSum (x :: xs)
      simp only [st, LC724.pivotScan]
      split
      · rfl
      · exact foldCL_go total xs (i + 1) (leftSum + x)

/-- **The derived program**: run the reshaped fold at the empty state `(0, 0)` against the precomputed
    total, exactly mirroring `LC724.pivotFn`. -/
def derivedPivotFn (nums : List Int) : Option Nat := foldCL nums.sum (CL.ofList nums) 0 0

/-- The derived program computes exactly `LC724.pivotFn`. -/
theorem derivedPivotFn_eq (nums : List Int) : derivedPivotFn nums = LC724.pivotFn nums :=
  foldCL_go nums.sum nums 0 0

/-! ## Correctness carries over from `L724.lean` (no re-proof of the scan invariant) -/

/-- **Headline.**  The honest bundle:

    (1) for each `total` the pivot scan, reshaped onto the cons-list initial algebra, IS the
        catamorphism of `consScalarAlg g (st total)` — the `O(n)` accumulator-passing left scan with
        early return EMERGES from `consFold_unique` (`pivot_emerges`);
    (2) the `Map` `LC724.solve` (LeetCode 724's answer relation) relates each input `nums` to exactly
        the derived program `derivedPivotFn` (`derivedPivotFn_eq`); and
    (3) that answer is honestly SOUND, LEFTMOST, and COMPLETE against the `IsPivot` spec — the REUSED
        `LC724.pivot_correct`, not re-proved here.

    The program (the fold) is PRODUCED by the law; soundness/leftmost/completeness is reused; only the
    DATA structure (the raw list reshaped onto `ConsList`) was changed. -/
theorem pivot_derived_correct :
    (∀ total : Int,
        (graph (foldCL total) : dCL Unit Int ⟶ ⟨Carrier⟩) = cataR (consScalarAlg g (st total)))
      ∧ (∀ (nums : List Int) (a : Option Nat), LC724.solve nums a ↔ a = derivedPivotFn nums)
      ∧ (∀ nums : List Int,
            (∀ i, derivedPivotFn nums = some i → LC724.IsPivot nums i) ∧
            (∀ i, derivedPivotFn nums = some i → ∀ j, j < i → ¬ LC724.IsPivot nums j) ∧
            (derivedPivotFn nums = none → ∀ j, ¬ LC724.IsPivot nums j)) := by
  refine ⟨pivot_emerges, ?_, ?_⟩
  · intro nums a
    show (a = LC724.pivotFn nums) ↔ a = derivedPivotFn nums
    rw [derivedPivotFn_eq nums]
  · intro nums
    rw [derivedPivotFn_eq nums]
    exact LC724.pivot_correct nums

/-! ## Running the derived program -/

example : derivedPivotFn [1, 7, 3, 6, 5, 6] = some 3 := by rw [derivedPivotFn_eq]; decide
example : derivedPivotFn [1, 2, 3] = none := by rw [derivedPivotFn_eq]; decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g (st 28)) (CL.ofList [1, 7, 3, 6, 5, 6]) (foldCL 28 (CL.ofList [1, 7, 3, 6, 5, 6])) := by
  have h : (graph (foldCL 28) : dCL Unit Int ⟶ ⟨Carrier⟩)
      (CL.ofList [1, 7, 3, 6, 5, 6]) (foldCL 28 (CL.ofList [1, 7, 3, 6, 5, 6])) := rfl
  rw [pivot_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC724D
