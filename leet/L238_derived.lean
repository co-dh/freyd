/-
  LeetCode 238 — Product of Array Except Self — DERIVED as TWO cons-list catamorphisms.

  `leet/L238.lean` WRITES `solveFn nums = zipWith (·*·) (prefixProducts nums) (suffixProducts
  nums)`, where `prefixProducts` threads an accumulator DOWN the recursion (`preScan`) and
  `suffixProducts` builds its running product on the RETURN side (`sufScan`) — both hand-written
  structural recursions on the raw Lean `List Int`.

  This file RESHAPES both scans onto the canonical cons-list initial algebra `ConsList Unit Int`
  (`CL.ofList`, `AOP/A6_ConsList.lean`, front-to-back: `[] ↦ wrap ()`, `x :: xs ↦ cons x
  (ofList xs)`) and produces each as the catamorphism of an EMERGENT algebra via the general-carrier
  law `CL.consFold_unique` (`AOP/A6_GenFold.lean`), with two DIFFERENT carrier shapes:

  1. **Prefix scan — CPS/continuation carrier `Int → List Int`.**  A plain cons-fold recurses on the
     TAIL first, so it has no left-accumulated `acc` to hand the step; the fix is to curry `acc` INTO
     the carrier: `C := Int → List Int`, "given the running product so far, the prefix-products list
     for the rest".  The folded tail becomes a continuation awaiting `acc`.  Base/step are then
     forced (`rfl` against `LC238.preScan`):
       * base `preG _  = fun _ => []`                          `= foldPre (wrap _)`
       * step `preSt x k = fun acc => acc :: k (acc * x)`       `= foldPre (cons x xs)` with
                                                                  `k = foldPre xs`.
     `consFold_unique` then EMITS `preScan`'s own accumulator-passing recursion as
     `cataR (consScalarAlg preG preSt)` — the accumulator threading is produced by the law, not
     hand-written.

  2. **Suffix scan — pair carrier `List Int × Int`.**  `sufScan` already recurses on the tail FIRST
     and only combines afterwards (no accumulator to CPS-thread), so the ordinary pair carrier
     `C := List Int × Int` (`sl`, `tot`) suffices directly:
       * base `sufG _    = ([], 1)`                             `= foldSuf (wrap _)`
       * step `sufSt x c = (c.2 :: c.1, c.2 * x)`                `= foldSuf (cons x xs)`.

  Both carriers only ever CONS onto the front of a list (`acc :: …`, `tot :: sl` — never
  `acc ++ [x]`), so both scans stay `O(n)`.

  CORRECTNESS is REUSED, not re-proved (headline shape 1 — equality refinement: the answer is an
  exact function, not an extremum to dominate).  The bridges `foldPre_ofList`/`foldSuf_ofList` show
  each reshaped fold computes exactly `LC238.preScan`/`LC238.sufScan` on converted input; hence
  `derivedSolveFn = LC238.solveFn` on the nose, and `LC238.solveFn_correct`/`solve_correct`
  (`IsProductExceptSelf`) transfer unchanged — no new correctness proof about products is needed.

  Mathlib-free (Lean core + `Freyd.*` only); headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L238

namespace Freyd.Alg.RelSet.LC238D

open Freyd Freyd.Alg.RelSet.CL

/-! ## Part 1 — prefix scan via the CPS carrier `Int → List Int` -/

/-- The continuation carrier: given the running product `acc` accumulated so far, the
    prefix-products list for the rest of the (unprocessed) suffix. -/
abbrev PreCarrier : Type := Int → List Int

/-- Base: an empty suffix contributes no further prefix-product entries, whatever `acc` is. -/
def preG : Unit → PreCarrier := fun _ => fun _ => []

/-- Step: prepend element `x` to the folded-tail continuation `k`.  Given the running product
    `acc`, EMIT `acc` (the prefix product up to here) and hand the updated running product
    `acc * x` on to `k`. -/
def preSt : Int → PreCarrier → PreCarrier := fun x k => fun acc => acc :: k (acc * x)

/-- The prefix scan as a fold over the cons-list initial algebra, mirroring `LC238.preScan`:
    `wrap _ ↦ (fun _ => [])`, `cons x xs ↦ preSt x (foldPre xs)`. -/
def foldPre : ConsList Unit Int → PreCarrier
  | ConsList.wrap _    => fun _ => []
  | ConsList.cons x xs => preSt x (foldPre xs)

/-- The base condition is a COMPUTATION: `foldPre (wrap d) = preG d`. -/
theorem foldPre_wrap : ∀ d : Unit, foldPre (ConsList.wrap d) = preG d := fun _ => rfl

/-- The step condition IS `foldPre`'s cons equation. -/
theorem foldPre_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), foldPre (ConsList.cons x xs) = preSt x (foldPre xs) :=
  fun _ _ => rfl

/-- **The prefix fold EMERGES** via the general-carrier cons-fold law: reshaped onto
    `ConsList Unit Int`, the prefix scan IS the catamorphism of `consScalarAlg preG preSt` — the
    accumulator-passing recursion was never hand-written. -/
theorem preScan_emerges :
    (graph foldPre : dCL Unit Int ⟶ ⟨PreCarrier⟩) = cataR (consScalarAlg preG preSt) :=
  consFold_unique preG preSt foldPre foldPre_wrap foldPre_cons

/-- The reshaped fold agrees with `LC238.preScan` on converted input, at every running product
    `acc`. -/
theorem foldPre_ofList (xs : List Int) (acc : Int) :
    foldPre (ofList xs) acc = LC238.preScan acc xs := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      show acc :: foldPre (ofList xs) (acc * x) = LC238.preScan acc (x :: xs)
      rw [LC238.preScan_cons, ih (acc * x)]

/-! ## Part 2 — suffix scan via the pair carrier `List Int × Int` -/

/-- The pair carrier: `(suffix-products-so-far, total product folded in so far)`. -/
abbrev SufCarrier : Type := List Int × Int

/-- Base: an empty suffix has no suffix-product entries and total product `1`. -/
def sufG : Unit → SufCarrier := fun _ => ([], 1)

/-- Step: prepend `x`.  The already-folded tail's total `c.2` becomes `x`'s own suffix product
    (prepended to the list), and the new total folds `x` in. -/
def sufSt : Int → SufCarrier → SufCarrier := fun x c => (c.2 :: c.1, c.2 * x)

/-- The suffix scan as a fold over the cons-list initial algebra, mirroring `LC238.sufScan`:
    `wrap _ ↦ ([], 1)`, `cons x xs ↦ sufSt x (foldSuf xs)`. -/
def foldSuf : ConsList Unit Int → SufCarrier
  | ConsList.wrap _    => ([], 1)
  | ConsList.cons x xs => sufSt x (foldSuf xs)

/-- The base condition is a COMPUTATION: `foldSuf (wrap d) = sufG d`. -/
theorem foldSuf_wrap : ∀ d : Unit, foldSuf (ConsList.wrap d) = sufG d := fun _ => rfl

/-- The step condition IS `foldSuf`'s cons equation. -/
theorem foldSuf_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), foldSuf (ConsList.cons x xs) = sufSt x (foldSuf xs) :=
  fun _ _ => rfl

/-- **The suffix fold EMERGES** via the general-carrier cons-fold law: reshaped onto
    `ConsList Unit Int`, the suffix scan IS the catamorphism of `consScalarAlg sufG sufSt`. -/
theorem sufScan_emerges :
    (graph foldSuf : dCL Unit Int ⟶ ⟨SufCarrier⟩) = cataR (consScalarAlg sufG sufSt) :=
  consFold_unique sufG sufSt foldSuf foldSuf_wrap foldSuf_cons

/-- The reshaped fold agrees with `LC238.sufScan` on converted input. -/
theorem foldSuf_ofList (xs : List Int) : foldSuf (ofList xs) = LC238.sufScan xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show ((foldSuf (ofList xs)).2 :: (foldSuf (ofList xs)).1, (foldSuf (ofList xs)).2 * x)
          = LC238.sufScan (x :: xs)
      rw [ih, LC238.sufScan_cons]

/-! ## The derived program: zip both reshaped folds -/

/-- **The derived program**: zip the two reshaped folds — `foldPre` started at running product `1`,
    `foldSuf`'s suffix-products component — exactly as `LC238.solveFn` zips `prefixProducts`/
    `suffixProducts`. -/
def derivedSolveFn (nums : List Int) : List Int :=
  List.zipWith (· * ·) (foldPre (ofList nums) 1) (foldSuf (ofList nums)).1

/-- **Equality refinement (headline shape 1)**: the derived program computes EXACTLY
    `LC238.solveFn` — the answer here is an exact function, not an extremum, so no
    soundness/dominance packaging is needed, only this equality. -/
theorem derivedSolveFn_eq (nums : List Int) : derivedSolveFn nums = LC238.solveFn nums := by
  show List.zipWith (· * ·) (foldPre (ofList nums) 1) (foldSuf (ofList nums)).1
      = List.zipWith (· * ·) (LC238.prefixProducts nums) (LC238.suffixProducts nums)
  rw [foldPre_ofList nums 1, foldSuf_ofList nums]
  rfl

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The derived allegory program**: LeetCode 238's solution, reshaped as two cons-list
    catamorphisms, as a morphism `Nums ⟶ Nums` in `Rel(Set)`. -/
def derivedSolve : LC238.Nums ⟶ LC238.Nums := graph derivedSolveFn

/-- The derived morphism equals `LC238.solve` — both are graphs of pointwise-equal functions. -/
theorem derivedSolve_eq_solve : derivedSolve = LC238.solve := by
  unfold derivedSolve LC238.solve
  rw [funext derivedSolveFn_eq]

/-! ## Headline: emergence + reused correctness -/

/-- **Headline.**  The honest bundle:

    (1) BOTH folds — the prefix CPS-carrier fold and the suffix pair-carrier fold — EMERGE from
        `CL.consFold_unique` (`preScan_emerges`, `sufScan_emerges`), each never hand-written as a
        catamorphism;
    (2) the zipped derived program equals `LC238.solveFn` EXACTLY (`derivedSolveFn_eq`,
        `derivedSolve_eq_solve`) — headline shape 1, since the answer is a genuine function; and
    (3) that answer is honestly correct — right length, right value at every index
        (`IsProductExceptSelf`) — the REUSED `LC238.solveFn_correct`, not re-proved here.

    The programs (both folds) are PRODUCED by the law; correctness is reused; only the DATA
    structure (front-to-back cons-list, two different carrier shapes) was changed. -/
theorem derived_correct :
    ((graph foldPre : dCL Unit Int ⟶ ⟨PreCarrier⟩) = cataR (consScalarAlg preG preSt))
      ∧ ((graph foldSuf : dCL Unit Int ⟶ ⟨SufCarrier⟩) = cataR (consScalarAlg sufG sufSt))
      ∧ (∀ nums, derivedSolveFn nums = LC238.solveFn nums)
      ∧ (∀ nums, LC238.IsProductExceptSelf nums (derivedSolveFn nums)) :=
  ⟨preScan_emerges, sufScan_emerges, derivedSolveFn_eq,
    fun nums => (derivedSolveFn_eq nums) ▸ LC238.solveFn_correct nums⟩

/-! ## Running the derived program -/

-- LeetCode 238's own example: `[1,2,3,4] → [24,12,8,6]`.
example : derivedSolveFn [1, 2, 3, 4] = [24, 12, 8, 6] := by decide
-- With a zero: every OTHER output collapses to `0`, but the zero's own slot survives.
example : derivedSolveFn [0, 4, 0] = [0, 0, 0] := by decide
-- A single negative flips the sign of every other slot.
example : derivedSolveFn [-1, 1, 2] = [2, -2, -1] := by decide

end Freyd.Alg.RelSet.LC238D
