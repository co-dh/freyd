/-
  LeetCode 234 — Palindrome Linked List — DERIVED as a catamorphism via the general-carrier
  cons-list fold-uniqueness law `Freyd.Alg.RelSet.CL.consFold_unique`.

  `leet.L234` decides a palindrome directly on the raw `List Int` by
  `isPalinFn xs := decide (xs = revFn xs)` (`revFn = List.reverse`, reused from `L206`) — there is no
  structural fold at all.  HERE the reconstruction fold is PRODUCED by the law.

  A palindrome cannot be decided by a single SCALAR fold (it must compare the two ends at once), so —
  exactly as in `L125` (Valid Palindrome) — the honest structural fold is the list RECONSTRUCTION
  with carrier `C := List Int`, and the palindrome logic is a DECISION on the whole rebuilt list.
  Reshaping the raw `List Int` front-to-back onto `ConsList Unit Int` (the `head :: tail` initial
  algebra, embedded by `ofList`), feeding

    * `g _   := []`         (base: the empty sequence), and
    * `st x l := x :: l`    (step: cons the head onto the folded tail — the `ConsList.cons` order)

  to `consFold_unique` PRODUCES the reconstruction fold `toListCL` as the catamorphism
  `cataR (consScalarAlg g st)` — the recursion is never re-written (`toList_emerges`; its two
  hypotheses are `toListCL`'s own defining equations, `rfl`).  The DERIVED program is
  `derivedSolve := cataR (consScalarAlg g st) ≫ graph decideRev` (rebuild, then decide
  reverse-equality); precomposed with the embedding `graph ofList` it is exactly `L234.solve`
  (`derivedSolve_eq_solve`).  Correctness is the DECISION shape `b = true ↔ P`, REUSED from
  `L234.palin_correct` — the `iff` is not re-proved.

  Mathlib-free.  Sorry-free.  Axioms of the headline `palin_derived_correct` ⊆ {propext, Quot.sound}
  (the constructive `consFold_unique` route; no `cataR_eq_relCata`, hence no `Classical.choice`).
-/
import AOP.A6_GenFold
import leet.L234

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC234D

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC234

/-! ## Base and step of the reconstruction fold

`g`/`st` are the base/step of the scalar algebra fed to `consFold_unique`; `toListCL` folds by
exactly these two equations, so the law's two hypotheses hold by `rfl`. -/

/-- Base: the empty sequence. -/
def g : Unit → List Int := fun _ => []

/-- Step: cons the head element onto the folded tail (the `ConsList.cons e xs` order). -/
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

/-! ## The derived program: rebuild, then decide reverse-equality -/

/-- The palindrome decision on the reconstructed list: does it read the same reversed? -/
def decideRev (l : List Int) : Bool := decide (l = l.reverse)

/-- **The derived allegory program.**  Run the emergent reconstruction fold, then decide
    reverse-equality — a composite `dCL Unit Int ⟶ dBool` in `Rel(Set)`, with the fold half
    PRODUCED by `consFold_unique`, not hand-written. -/
def derivedSolve : dCL Unit Int ⟶ dBool := cataR (consScalarAlg g st) ≫ graph decideRev

/-! ## Reshaping: embed the raw `List Int` as a `ConsList Unit Int`

The reshaping recipe: `L234`'s program takes a raw `List Int`; the fold lives on `ConsList Unit Int`,
so we embed `ofList` (`[] ↦ wrap ()`, `x :: xs ↦ cons x (ofList xs)`) and bridge `toListCL (ofList xs)
= xs` — the reconstruction fold on the embedded list rebuilds the original list. -/

/-- Embed a raw `List Int` front-to-back into the `ConsList Unit Int` initial algebra. -/
def ofList : List Int → ConsList Unit Int
  | [] => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The reconstruction fold on the embedded list rebuilds the original list. -/
theorem toListCL_ofList (xs : List Int) : toListCL (ofList xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => show x :: toListCL (ofList xs) = x :: xs; rw [ih]

/-- **Applying the derived program to an embedded list.**  Rewriting the fold back to `toListCL`
    (`toList_emerges`) and reducing the two graphs, `derivedSolve (ofList xs)` relates `b` to `true`
    exactly by the reverse-equality decision on the rebuilt list `= decideRev xs`. -/
theorem derivedSolve_ofList (xs : List Int) (b : Bool) :
    derivedSolve (ofList xs) b ↔ b = decideRev xs := by
  show (cataR (consScalarAlg g st) ≫ graph decideRev) (ofList xs) b ↔ b = decideRev xs
  rw [← toList_emerges]
  constructor
  · rintro ⟨l, hl, hb⟩
    subst hl
    rw [toListCL_ofList] at hb
    exact hb
  · intro hb
    refine ⟨toListCL (ofList xs), rfl, ?_⟩
    rw [toListCL_ofList]; exact hb

/-- **The derived program is `L234.solve`.**  Precomposing with the embedding `graph ofList` and
    rewriting the fold back to `toListCL`, `derivedSolve` composes to `graph isPalinFn = L234.solve` —
    since `decideRev (toListCL (ofList xs))` is `isPalinFn xs` (both `decide (xs = xs.reverse)`). -/
theorem derivedSolve_eq_solve :
    (graph ofList ≫ derivedSolve : LC206.dList ⟶ dBool) = LC234.solve := by
  apply hom_ext; intro xs b
  constructor
  · rintro ⟨cl, hcl, hb⟩
    subst hcl
    show b = isPalinFn xs
    exact (derivedSolve_ofList xs b).mp hb
  · intro hb
    refine ⟨ofList xs, rfl, ?_⟩
    exact (derivedSolve_ofList xs b).mpr hb

/-! ## Correctness — REUSED from `L234`, not re-proved -/

/-- **LeetCode 234, derived.**  The palindrome-decision program `derivedSolve` — whose fold half is
    PRODUCED by the fold law (`toList_emerges`) and whose answer is the reverse-equality decision on
    the rebuilt list — relates an embedded list `ofList xs` to `true` exactly when `xs` reads the same
    reversed.  The DECISION correctness shape `b = true ↔ P`, obtained via `derivedSolve_ofList` and
    REUSING `L234.palin_correct` — the `iff` is not re-proved. -/
theorem palin_derived_correct (xs : List Int) :
    derivedSolve (ofList xs) true ↔ xs = xs.reverse := by
  rw [derivedSolve_ofList]
  constructor
  · intro h; exact (palin_correct xs).mp h.symm
  · intro h; exact ((palin_correct xs).mpr h).symm

/-! ## Running the derived program (same computations as `L234`)

  `cataR (consScalarAlg g st)` is a relational catamorphism (its `cons` case is an existential over
  the carrier), so it is not itself `decide`-computable; we `decide` the computable witness
  `decideRev (toListCL (ofList _))` — extensionally `derivedSolve`'s value on a graph point
  (`toList_emerges`), and `isPalinFn _` definitionally. -/

example : decideRev (toListCL (ofList ([1, 2, 2, 1] : List Int))) = true := by decide
example : decideRev (toListCL (ofList ([1, 2] : List Int))) = false := by decide
example : decideRev (toListCL (ofList ([1] : List Int))) = true := by decide

end Freyd.Alg.RelSet.LC234D
