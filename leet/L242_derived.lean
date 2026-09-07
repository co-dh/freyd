/-
  LeetCode 242 — Valid Anagram — DERIVED as a cons-list catamorphism (insertion sort).

  `leet/L242.lean` packages the answer via a hand-written `isort : List Int → List Int`
  (`isort [] = []`, `isort (a :: t) = linsert a (isort t)`) folded over a RAW Lean `List Int`, so as
  written it is not a `cataR`.  This file RESHAPES the data onto the canonical cons-list initial
  algebra `ConsList Unit Int` (`CL.ofList`, the SHARED `List E → ConsList Unit E` bridge) and reads
  `isort` off as an ordinary cons-fold:

    * carrier `C := List Int`             — the sorted-so-far list;
    * base    `g ()  = []`                = `isortFold (wrap ())`;
    * step    `st x k = linsert x k`      = `isortFold (cons x xs)` with `k = isortFold xs`,
      REUSING `LC242.linsert` (ordered insert) unchanged.

  Feeding `g`/`st`/`isortFold` to the general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique`
  (`AOP/A6_GenFold.lean`) PRODUCES this fold as `cataR (consScalarAlg g st)` — insertion sort is
  never written as a fold, it EMERGES from the law.  `linsert` costs O(n) per call (it walks the
  sorted prefix to find the insertion point), so folding n elements is O(n) calls × O(n) each = O(n²)
  — insertion sort is INHERENTLY quadratic; the recursion shape here gives no room to do better (a
  hash-count comparison would sidestep sorting entirely, but needs map-equality iteration, not a
  cons-fold, so it is out of scope for this derivation).

  The anagram DECISION is then read off by comparing the two emergent sorted lists, mirroring
  `LC242.anagramFn`; correctness (`solve_correct`, the `iff` shape for a decision problem) is REUSED
  from `L242.lean`, not re-proved — only the program (the sorting fold) is produced by the law.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L242

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC242D

open Freyd Freyd.Alg.RelSet.CL
open Freyd.Alg.RelSet.SL (SnocList)

/-! ## Insertion sort, RESHAPED onto the cons-list initial algebra `ConsList Unit Int`

  `LC242.isort` folds a raw `List Int` FRONT-to-back: `isort [] = []`,
  `isort (a :: t) = linsert a (isort t)` — exactly the cons-list recursion `wrap () ↦ base`,
  `cons a xs ↦ st a (fold xs)`. -/

/-- Base of the emergent algebra: the empty list sorts to the empty list. -/
def g : Unit → List Int := fun _ => []

/-- Step of the emergent algebra: insert the head into the already-sorted tail — REUSING `LC242`'s
    ordered `linsert`, not redefined. -/
def st : Int → List Int → List Int := LC242.linsert

/-- Insertion sort over the cons-list initial algebra, mirroring `LC242.isort`'s recursion:
    `wrap _ ↦ []`, `cons x xs ↦ linsert x (isortFold xs)`. -/
def isortFold : ConsList Unit Int → List Int
  | ConsList.wrap _    => g ()
  | ConsList.cons x xs => st x (isortFold xs)

/-- The base condition is a COMPUTATION, not a guess: `isortFold (wrap d) = g d`. -/
theorem isortFold_wrap : ∀ d : Unit, isortFold (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `isortFold`'s cons equation: `isortFold (cons x xs) = st x (isortFold xs)`. -/
theorem isortFold_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), isortFold (ConsList.cons x xs) = st x (isortFold xs) :=
  fun _ _ => rfl

/-! ## Insertion sort EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.** Insertion sort, RESHAPED onto the cons-list initial algebra `ConsList Unit
    Int`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g st` — it was never
    written as a fold: `graph isortFold` equals `cataR (consScalarAlg g st)`. -/
theorem isort_emerges :
    (graph isortFold : dCL Unit Int ⟶ ⟨List Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st isortFold isortFold_wrap isortFold_cons

/-! ## Bridge to `LC242.isort` (the raw-`List` recursion) via the SHARED `CL.ofList` -/

/-- The reshaped fold IS `LC242.isort`: `isortFold (ofList l) = LC242.isort l`, by induction on `l`.
    The cons step is pure computation: `isortFold (ofList (x::xs)) = linsert x (isortFold (ofList xs))`
    and `LC242.isort (x::xs) = linsert x (LC242.isort xs)`. -/
theorem isortFold_ofList : ∀ l : List Int, isortFold (ofList l) = LC242.isort l
  | []      => rfl
  | x :: xs => by
      show st x (isortFold (ofList xs)) = LC242.linsert x (LC242.isort xs)
      rw [isortFold_ofList xs]
      rfl

/-! ## The anagram decision, reshaped: compare the two EMERGED sorted lists -/

/-- The reshaped answer function: same shape as `LC242.anagramFn`, comparing the outputs of the
    EMERGED cons-fold `isortFold` (via `CL.ofList`) instead of the hand-written `LC242.isort`. -/
def derivedAnagramFn (s t : SnocList Int Int) : Bool :=
  decide (isortFold (ofList (LC242.toList s)) = isortFold (ofList (LC242.toList t)))

/-- The reshaped answer function agrees with `LC242.anagramFn` pointwise — the reshaping changes
    nothing observable, only how the sort is PRODUCED. -/
theorem derivedAnagramFn_eq_anagramFn : derivedAnagramFn = LC242.anagramFn := by
  funext s t
  show decide (isortFold (ofList (LC242.toList s)) = isortFold (ofList (LC242.toList t)))
      = decide (LC242.isort (LC242.toList s) = LC242.isort (LC242.toList t))
  rw [isortFold_ofList, isortFold_ofList]

/-! ## Correctness carries over from `L242.lean` (no re-proof)

  This is the DECISION-problem headline shape (`iff`, cf. `L217`/`L242` themselves): the reshaped
  program decides `Anagram` exactly because `LC242.anagramFn` does, via `derivedAnagramFn_eq_anagramFn`.
  Only `isort_emerges` (the program) is new; correctness is REUSED wholesale from `LC242.solve_correct`. -/

/-- **Headline.** (1) insertion sort, reshaped onto the cons-list initial algebra, IS the
    catamorphism of `consScalarAlg g st` — it EMERGES from `consFold_unique` (`isort_emerges`);
    (2) the reshaped decision function agrees with `LC242.anagramFn` pointwise
    (`derivedAnagramFn_eq_anagramFn`); and (3) it decides `Anagram` — REUSING `LC242.solve_correct`,
    not re-proved. -/
theorem anagram_derived_correct :
    ((graph isortFold : dCL Unit Int ⟶ ⟨List Int⟩) = cataR (consScalarAlg g st))
      ∧ (derivedAnagramFn = LC242.anagramFn)
      ∧ (∀ s t : SnocList Int Int, derivedAnagramFn s t = true ↔ LC242.Anagram s t) := by
  refine ⟨isort_emerges, derivedAnagramFn_eq_anagramFn, ?_⟩
  intro s t
  rw [derivedAnagramFn_eq_anagramFn]
  exact LC242.solve_correct s t

/-! ## Running / cross-checking the reshaped program -/

-- letters encoded as distinct `Int`s: a=1 n=2 g=3 r=4 m=5 c=6 t=7
example :
    derivedAnagramFn (LC242.ofList 1 [2, 1, 3, 4, 1, 5]) (LC242.ofList 2 [1, 3, 1, 4, 1, 5])
      = true := by decide  -- "anagram" / "nagaram"
example : derivedAnagramFn (LC242.ofList 4 [1, 7]) (LC242.ofList 6 [1, 4]) = false := by
  decide  -- "rat" / "car"
example : derivedAnagramFn (LC242.ofList 1 []) (LC242.ofList 1 []) = true := by decide  -- "a" / "a"

end Freyd.Alg.RelSet.LC242D
