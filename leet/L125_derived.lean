/-
  LeetCode 125 — Valid Palindrome — DERIVED as a catamorphism via the general-carrier
  cons-list fold-uniqueness law `Freyd.Alg.RelSet.CL.consFold_unique`.

  `leet.L125` writes the list-reconstruction fold `toList` by hand (over the back-to-front
  `SnocList`, with the O(n) step `toList xs ++ [q]`) and then decides reverse-equality on the result.
  HERE the reconstruction fold is PRODUCED by the law, and — crucially — the reconstruction runs in
  LINEAR time: the honest structural fold uses front-to-back `cons` reconstruction, whose step is O(1),
  instead of the quadratic back-append.

  A palindrome cannot be decided by a single SCALAR fold (it must compare the two ends at once), so —
  exactly as in `L234` (Palindrome Linked List) — the honest structural fold is the list
  RECONSTRUCTION with carrier `C := List Int`, and the palindrome logic is a DECISION on the whole
  rebuilt list.  We fold over the `head :: tail` initial algebra `ConsList Unit Int`, feeding

    * `g _   := []`         (base: the empty sequence), and
    * `st x l := x :: l`    (step: cons the head onto the folded tail — O(1), the `ConsList.cons`
                             order; total reconstruction is O(n), NOT the O(n²) of `L125.toList`)

  to `consFold_unique`, which PRODUCES the reconstruction fold `toListCL` as the catamorphism
  `cataR (consScalarAlg g st)` — the recursion is never re-written (`toList_emerges`; its two
  hypotheses are `toListCL`'s own defining equations, `rfl`).  The DERIVED program is
  `derivedSolve := cataR (consScalarAlg g st) ≫ graph decideRev` (rebuild in O(n), then decide
  reverse-equality; `List.reverse` is Lean-core O(n)).

  `L125`'s data is the back-to-front `SnocList Int Int`; the linear reshape `slToCL` re-threads it
  front-to-back onto `ConsList Unit Int` with an accumulator, again with an O(1) `cons` step (never
  a back-append), so `toListCL (slToCL xs) = L125.toList xs` (identity order).  Precomposed with the
  embedding `graph slToCL`, `derivedSolve` is exactly `L125.solve` (`derivedSolve_eq_solve`).
  Correctness is the DECISION shape `b = true ↔ P`, REUSED from `L125.solve_correct` — the `iff` is
  not re-proved.

  Mathlib-free.  Sorry-free.  Axioms of the headline `palin_derived_correct` ⊆ {propext, Quot.sound}
  (the constructive `consFold_unique` route; no `cataR_eq_relCata`, hence no `Classical.choice`).
-/
import AOP.A6_GenFold
import leet.L125

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC125D

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC125

/-! ## Base and step of the reconstruction fold

`g`/`st` are the base/step of the scalar algebra fed to `consFold_unique`; `toListCL` folds by
exactly these two equations, so the law's two hypotheses hold by `rfl`.  The step is O(1) `cons`
(never a back-append `++ [·]`), so the whole reconstruction is O(n). -/

/-- Base: the empty sequence. -/
def g : Unit → List Int := fun _ => []

/-- Step: cons the head element onto the folded tail (the `ConsList.cons x xs` order) — O(1). -/
def st : Int → List Int → List Int := fun x l => x :: l

/-- The reconstruction fold, defined FROM `g`/`st` so `consFold_unique` applies by `rfl`. -/
def toListCL : ConsList Unit Int → List Int
  | ConsList.wrap d => g d
  | ConsList.cons x xs => st x (toListCL xs)

/-! ## The reconstruction fold EMERGES as the catamorphism -/

/-- **The fold is produced by the law.**  `toListCL` — the cons-list rebuilt as a plain `List Int` —
    IS the catamorphism of the scalar algebra `[g, st]`; the two hypotheses are `toListCL`'s own
    defining equations, so both are `rfl`.  The recursion is never written by hand here. -/
theorem toList_emerges :
    (graph toListCL : dCL Unit Int ⟶ (⟨List Int⟩ : RelSet.{0})) = cataR (consScalarAlg g st) :=
  consFold_unique g st toListCL (fun _ => rfl) (fun _ _ => rfl)

/-! ## The derived program: rebuild in O(n), then decide reverse-equality -/

/-- The palindrome decision on the reconstructed list: does it read the same reversed? -/
def decideRev (l : List Int) : Bool := decide (l = l.reverse)

/-- **The derived allegory program.**  Run the emergent O(n) reconstruction fold, then decide
    reverse-equality — a composite `dCL Unit Int ⟶ dBool` in `Rel(Set)`, with the fold half
    PRODUCED by `consFold_unique`, not hand-written. -/
def derivedSolve : dCL Unit Int ⟶ dBool := cataR (consScalarAlg g st) ≫ graph decideRev

/-! ## Reshaping: re-thread the back-to-front `SnocList` as a front-to-back `ConsList`

`L125`'s data is `SnocList Int Int` (elements added at the back).  `slToCL` re-threads it onto
`ConsList Unit Int` with an accumulator so every step is an O(1) `cons` (never a back-append); the
accumulator makes the result come out in INDEX order, so `toListCL (slToCL xs) = L125.toList xs`. -/

/-- Accumulating re-thread: peel the `SnocList` from the back, consing each element onto the front
    of the accumulator.  Because the back element is consed first onto the growing front, the final
    cons-list is in index order.  Every step is O(1). -/
def goCL : SL.SnocList Int Int → ConsList Unit Int → ConsList Unit Int
  | SL.SnocList.wrap x, acc => ConsList.cons x acc
  | SL.SnocList.snoc xs q, acc => goCL xs (ConsList.cons q acc)

/-- Re-thread a back-to-front `SnocList Int Int` into the front-to-back `ConsList Unit Int` initial
    algebra, in index order, with an O(1) `cons` at every step. -/
def slToCL (xs : SL.SnocList Int Int) : ConsList Unit Int := goCL xs (ConsList.wrap ())

/-- Reconstructing the re-threaded prefix, then appending the reconstructed accumulator, rebuilds
    `L125.toList xs ++ (accumulator as a list)` — the generalised bridge, by induction on the
    `SnocList` (accumulator generalised). -/
theorem toListCL_goCL (xs : SL.SnocList Int Int) (acc : ConsList Unit Int) :
    toListCL (goCL xs acc) = LC125.toList xs ++ toListCL acc := by
  induction xs generalizing acc with
  | wrap x => rfl
  | snoc xs q ih =>
      show toListCL (goCL xs (ConsList.cons q acc)) = LC125.toList xs ++ [q] ++ toListCL acc
      rw [ih (ConsList.cons q acc)]
      show LC125.toList xs ++ (q :: toListCL acc) = LC125.toList xs ++ [q] ++ toListCL acc
      rw [List.append_assoc]
      rfl

/-- The re-threaded reconstruction rebuilds the original sequence in index order:
    `toListCL (slToCL xs) = L125.toList xs`.  So the derived fold and `L125`'s hand fold agree. -/
theorem toListCL_slToCL (xs : SL.SnocList Int Int) : toListCL (slToCL xs) = LC125.toList xs := by
  show toListCL (goCL xs (ConsList.wrap ())) = LC125.toList xs
  rw [toListCL_goCL]
  show LC125.toList xs ++ [] = LC125.toList xs
  rw [List.append_nil]

/-- **Applying the derived program to a re-threaded sequence.**  Rewriting the fold back to `toListCL`
    (`toList_emerges`) and reducing the two graphs, `derivedSolve (slToCL xs)` relates `b` to `true`
    exactly by the reverse-equality decision on the rebuilt list — which, since
    `toListCL (slToCL xs) = L125.toList xs`, is `L125.palinFn xs` (both `decide (l = l.reverse)`). -/
theorem derivedSolve_slToCL (xs : SL.SnocList Int Int) (b : Bool) :
    derivedSolve (slToCL xs) b ↔ b = LC125.palinFn xs := by
  show (cataR (consScalarAlg g st) ≫ graph decideRev) (slToCL xs) b ↔ b = LC125.palinFn xs
  rw [← toList_emerges]
  constructor
  · rintro ⟨l, hl, hb⟩
    subst hl
    rw [toListCL_slToCL] at hb
    exact hb
  · intro hb
    refine ⟨toListCL (slToCL xs), rfl, ?_⟩
    rw [toListCL_slToCL]; exact hb

/-- **The derived program is `L125.solve`.**  Precomposing with the linear reshape `graph slToCL`
    and rewriting the fold back to `toListCL`, `derivedSolve` composes to `graph palinFn = L125.solve`
    — since `decideRev (toListCL (slToCL xs))` is `L125.palinFn xs`. -/
theorem derivedSolve_eq_solve :
    (graph slToCL ≫ derivedSolve : LC125.Arr ⟶ dBool) = LC125.solve := by
  apply hom_ext; intro xs b
  constructor
  · rintro ⟨cl, hcl, hb⟩
    subst hcl
    show b = LC125.palinFn xs
    exact (derivedSolve_slToCL xs b).mp hb
  · intro hb
    refine ⟨slToCL xs, rfl, ?_⟩
    exact (derivedSolve_slToCL xs b).mpr hb

/-! ## Correctness — REUSED from `L125`, not re-proved -/

/-- **LeetCode 125, derived.**  The palindrome-decision program `derivedSolve` — whose fold half is
    PRODUCED by the fold law (`toList_emerges`) with an O(1) `cons` reconstruction, and whose answer
    is the reverse-equality decision on the rebuilt list — relates a re-threaded sequence `slToCL xs`
    to `true` exactly when `xs` is a palindrome (`L125.IsPalin`).  The DECISION correctness shape
    `b = true ↔ P`, obtained via `derivedSolve_slToCL` and REUSING `L125.solve_correct` — the `iff`
    is not re-proved. -/
theorem palin_derived_correct (xs : SL.SnocList Int Int) :
    derivedSolve (slToCL xs) true ↔ IsPalin xs := by
  rw [derivedSolve_slToCL]
  constructor
  · intro h; exact (solve_correct xs).mp h.symm
  · intro h; exact ((solve_correct xs).mpr h).symm

/-! ## Running the derived program (same computations as `L125`)

  `cataR (consScalarAlg g st)` is a relational catamorphism (its `cons` case is an existential over
  the carrier), so it is not itself `decide`-computable; we `decide` the computable witness
  `decideRev (toListCL (slToCL _))` — extensionally `derivedSolve`'s value on a graph point
  (`toList_emerges`), and `L125.palinFn _` definitionally. -/

example : decideRev (toListCL (slToCL (ofList 97 [98, 97]))) = true := by decide      -- "aba"
example : decideRev (toListCL (slToCL (ofList 97 [98]))) = false := by decide         -- "ab"
example : decideRev (toListCL (slToCL (ofList 97 [98, 98, 97]))) = true := by decide  -- "abba"
example : decideRev (toListCL (slToCL (ofList 1 []))) = true := by decide             -- single char

end Freyd.Alg.RelSet.LC125D
