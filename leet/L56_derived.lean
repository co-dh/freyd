/-
  LeetCode 56 — Merge Intervals — DERIVED as TWO cons-list catamorphisms, O(n²) overall
  (insertion sort is the inherent cost; the merge pass itself is O(n)).

  `leet/L56.lean` writes `mergeFn = mergeSorted ∘ isort` over a RAW Lean `List (Int × Int)`:
  `isort`/`linsert` (insertion sort by `.1`) and `mergeSorted`/`mergeRun` (a left-to-right run-
  merging scan carrying a "current running interval" `cur`).  Neither is the repo's initial-algebra
  list, so as written neither is a `cataR`.  This file RESHAPES BOTH onto the canonical cons-list
  initial algebra `ConsList Unit (Int × Int)` (the book's `list (Int × Int)`, base at `wrap ()`,
  recursion on the tail) and derives each as a `CL.consFold_unique` fold:

  1. **`isortCLFold`** — carrier `C := List (Int × Int)` (the sorted list built so far).  The step IS
     `LC56.linsert` itself (`E → C → C`, no change), so this is a direct, ordinary cons-fold —
     `isort`'s own defining equations (`isort [] = []`, `isort (iv::rest) = linsert iv (isort
     rest)`) already have exactly this shape. `linsert` is O(n) (a scan to find the insertion
     point), invoked once per element, so `isortCLFold` is INHERENTLY O(n²) — this is not an
     artifact of the reshaping, it is insertion sort's own complexity; no `acc ++ [x]` trap is
     involved.

  2. **`mergeCLFold`** — carrier `C := (Int × Int) → List (Int × Int)`, a CONTINUATION ("cur → out")
     carrier in the sense of `L206_derived`'s difference-list accumulator: `mergeRun cur rest` is
     `mergeRun` CURRIED on `cur`, and `mergeRun cur (iv :: rest)`'s recursive call passes a NEW `cur`
     down into `rest` — information a plain `st : E → C → C` step over a FIXED carrier cannot thread,
     because `ConsList`'s cons-fold computes the folded TAIL before combining with the head, so the
     tail's answer would have to be pre-committed without knowing `cur`.  (Concretely: prepending an
     interval `iv` in front of an already-merged `rest` can fuse TWO of `rest`'s own runs that did
     NOT touch on their own — e.g. `rest = [(2,3),(9,20)]` merges to itself unchanged, but prepending
     `iv = (1,10)` extends `cur` to `(1,10)` after touching `(2,3)`, which THEN reaches into `(9,20)`
     too, giving `[(1,20)]` — a fact `rest`'s own precomputed answer alone cannot recover.)  The
     continuation carrier sidesteps this: `mergeCLFold xs : (Int × Int) → List (Int × Int)` is a
     function AWAITING `cur`, so the step `stMerge iv k = fun cur => …` decides extend-vs-emit against
     the CALLER's `cur`, exactly mirroring `mergeRun`'s own recursion.  Each step still does O(1) work
     (`imax`, or one `cur ::`) before making its single recursive call — the SAME `cur :: …` (not
     `acc ++ [x]`) `mergeRun` itself uses — so `mergeCLFold` is O(n); no accumulator-plus-final-reverse
     is needed because the continuation's own `cur :: (k iv)` already returns the output in the
     correct left-to-right order as the recursion unwinds (unlike a `List.foldl`-style accumulator,
     which WOULD need a final reverse).

  Composing: `mergeFn_derived ivs := mergeSortedFold (isortCLFold (ofList ivs))` reshapes `mergeFn`
  itself; `mergeFn_derived_eq` bridges it to `LC56.mergeFn` by identifying each reshaped fold with its
  raw-`List` original (`isortCLFold_ofList`, `mergeCLFold_ofList`).  Only the DATA/fold-form is
  reshaped — `LC56.merge_correct` (coverage / sortedness / disjointness / validity) is REUSED, not
  re-proved.  Uses the SHARED `Freyd.Alg.RelSet.CL.ofList` (`AOP/A6_ConsList.lean`).

  Overall complexity: O(n²) — the emergent `isortCLFold` pass dominates; `mergeCLFold` alone is O(n).

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L56

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC56D

open Freyd Freyd.Alg.RelSet.CL

/-! ## Fold 1: insertion sort by `.1`, carrier `C := List (Int × Int)` (the sorted list so far)

  `LC56.linsert` is reused VERBATIM as the step — `isort`'s own recursion already has the
  `E → C → C` cons-fold shape. -/

/-- The base of the emergent sort algebra: the empty suffix sorts to the empty list. -/
def gSort : Unit → List (Int × Int) := fun _ => []

/-- The step of the emergent sort algebra: insert the head into the already-sorted folded tail —
    `LC56.linsert` itself, unchanged. -/
def stSort : (Int × Int) → List (Int × Int) → List (Int × Int) := LC56.linsert

/-- Insertion sort as a fold over the cons-list initial algebra, mirroring `LC56.isort`:
    `wrap _ ↦ []`, `cons iv xs ↦ stSort iv (isortCLFold xs)`. -/
def isortCLFold : ConsList Unit (Int × Int) → List (Int × Int)
  | ConsList.wrap _   => gSort ()
  | ConsList.cons iv xs => stSort iv (isortCLFold xs)

/-- The base condition is a COMPUTATION, not a guess: `isortCLFold (wrap d) = gSort d`. -/
theorem isortCLFold_wrap : ∀ d : Unit, isortCLFold (ConsList.wrap d) = gSort d := fun _ => rfl

/-- The step condition IS `isortCLFold`'s cons equation. -/
theorem isortCLFold_cons : ∀ (iv : Int × Int) (xs : ConsList Unit (Int × Int)),
    isortCLFold (ConsList.cons iv xs) = stSort iv (isortCLFold xs) := fun _ _ => rfl

/-- **The sort derivation.**  Insertion sort, RESHAPED onto `ConsList Unit (Int × Int)`, IS the
    catamorphism of `consScalarAlg gSort stSort` — it was never written as a fold. -/
theorem isort_emerges :
    (graph isortCLFold : dCL Unit (Int × Int) ⟶ ⟨List (Int × Int)⟩) = cataR (consScalarAlg gSort stSort) :=
  consFold_unique gSort stSort isortCLFold isortCLFold_wrap isortCLFold_cons

/-- The reshaped sort fold agrees with `LC56.isort` on converted input, by the same induction
    `isort` itself is defined by (both sides unfold identically, `stSort = LC56.linsert`). -/
theorem isortCLFold_ofList : ∀ l : List (Int × Int), isortCLFold (CL.ofList l) = LC56.isort l
  | []          => rfl
  | iv :: rest  => by
      show stSort iv (isortCLFold (CL.ofList rest)) = LC56.isort (iv :: rest)
      rw [isortCLFold_ofList rest]
      rfl

/-! ## Fold 2: run-merging, carrier `C := (Int × Int) → List (Int × Int)` (a continuation "cur → out")

  `mergeCLFold xs` is a function awaiting the caller's running interval `cur`; the step decides
  extend-vs-emit against that `cur`, exactly mirroring `LC56.mergeRun`'s own curried recursion. -/

/-- The base of the emergent merge algebra: an empty suffix closes the run — the caller's `cur` is
    the sole output. -/
def gMerge : Unit → ((Int × Int) → List (Int × Int)) := fun _ => fun cur => [cur]

/-- The step of the emergent merge algebra: does the head `iv` touch/overlap the caller's `cur`
    (`iv.1 ≤ cur.2`)?  EXTEND — fold the tail with `cur` widened by `imax` (O(1)); or EMIT — `cur` is
    finished (`cur :: …`, O(1) cons, not `++`), start a fresh run at `iv`. -/
def stMerge : (Int × Int) → ((Int × Int) → List (Int × Int)) → ((Int × Int) → List (Int × Int)) :=
  fun iv k => fun cur =>
    if iv.1 ≤ cur.2 then k (cur.1, LC56.imax cur.2 iv.2) else cur :: k iv

/-- Run-merging as a continuation fold over the cons-list initial algebra, mirroring `LC56.mergeRun`
    curried on `cur`: `wrap _ ↦ fun cur => [cur]`, `cons iv xs ↦ stMerge iv (mergeCLFold xs)`. -/
def mergeCLFold : ConsList Unit (Int × Int) → ((Int × Int) → List (Int × Int))
  | ConsList.wrap _      => gMerge ()
  | ConsList.cons iv xs  => stMerge iv (mergeCLFold xs)

/-- The base condition is a COMPUTATION, not a guess: `mergeCLFold (wrap d) = gMerge d`. -/
theorem mergeCLFold_wrap : ∀ d : Unit, mergeCLFold (ConsList.wrap d) = gMerge d := fun _ => rfl

/-- The step condition IS `mergeCLFold`'s cons equation. -/
theorem mergeCLFold_cons : ∀ (iv : Int × Int) (xs : ConsList Unit (Int × Int)),
    mergeCLFold (ConsList.cons iv xs) = stMerge iv (mergeCLFold xs) := fun _ _ => rfl

/-- **The merge derivation.**  Run-merging, RESHAPED onto `ConsList Unit (Int × Int)` with the
    continuation carrier, IS the catamorphism of `consScalarAlg gMerge stMerge` — it was never
    written as a fold: threading `cur` through a curried carrier is what lets `consFold_unique`
    emit an O(n) two-way (extend/emit) scan, despite the cons-fold's tail-first recursion order. -/
theorem mergeRun_emerges :
    (graph mergeCLFold : dCL Unit (Int × Int) ⟶ ⟨(Int × Int) → List (Int × Int)⟩)
      = cataR (consScalarAlg gMerge stMerge) :=
  consFold_unique gMerge stMerge mergeCLFold mergeCLFold_wrap mergeCLFold_cons

/-- The reshaped merge fold agrees with `LC56.mergeRun` on converted input, for EVERY `cur`, by the
    same induction `mergeRun` is defined by: both sides unfold to the identical `if iv.1 ≤ cur.2 then
    … else cur :: …` (`stMerge`'s body is `mergeRun`'s own body verbatim). -/
theorem mergeCLFold_ofList : ∀ (rest : List (Int × Int)) (cur : Int × Int),
    mergeCLFold (CL.ofList rest) cur = LC56.mergeRun cur rest
  | [],         cur => rfl
  | iv :: rest, cur => by
      show stMerge iv (mergeCLFold (CL.ofList rest)) cur = LC56.mergeRun cur (iv :: rest)
      show (if iv.1 ≤ cur.2 then mergeCLFold (CL.ofList rest) (cur.1, LC56.imax cur.2 iv.2)
              else cur :: mergeCLFold (CL.ofList rest) iv)
            = LC56.mergeRun cur (iv :: rest)
      simp only [mergeCLFold_ofList rest]
      rfl

/-! ## Composing the two folds, bridging to `LC56.mergeFn` -/

/-- Seed the merge continuation from the sorted list's own head — mirrors `LC56.mergeSorted`. -/
def mergeSortedFold : List (Int × Int) → List (Int × Int)
  | []         => []
  | iv :: rest => mergeCLFold (CL.ofList rest) iv

/-- `mergeSortedFold` agrees with `LC56.mergeSorted` on every list. -/
theorem mergeSortedFold_eq (l : List (Int × Int)) : mergeSortedFold l = LC56.mergeSorted l := by
  cases l with
  | nil => rfl
  | cons iv rest =>
      show mergeCLFold (CL.ofList rest) iv = LC56.mergeSorted (iv :: rest)
      rw [mergeCLFold_ofList rest iv]
      rfl

/-- **The composed derived program**: sort by `.1` (the emergent `isortCLFold`), then run-merge (the
    emergent `mergeCLFold`, seeded via `mergeSortedFold`) — both stages catamorphisms. -/
def mergeFn_derived (ivs : List (Int × Int)) : List (Int × Int) :=
  mergeSortedFold (isortCLFold (CL.ofList ivs))

/-- The composed derived program agrees with `LC56.mergeFn`, by chaining the two bridges. -/
theorem mergeFn_derived_eq (ivs : List (Int × Int)) : mergeFn_derived ivs = LC56.mergeFn ivs := by
  show mergeSortedFold (isortCLFold (CL.ofList ivs)) = LC56.mergeSorted (LC56.isort ivs)
  rw [isortCLFold_ofList ivs, mergeSortedFold_eq]

/-! ## Correctness carries over from `L56.lean` (no re-proof) -/

/-- **Headline.**  The honest bundle for the STRUCTURAL-OUTPUT case:

    (1) insertion sort, reshaped onto the cons-list initial algebra with the growing-sorted-list
        carrier, IS the catamorphism of `consScalarAlg gSort stSort` — EMERGES from
        `consFold_unique` (`isort_emerges`); O(n²) inherent (each `linsert` is O(n));
    (2) run-merging, reshaped with the continuation ("cur → out") carrier, IS the catamorphism of
        `consScalarAlg gMerge stMerge` — EMERGES from `consFold_unique` (`mergeRun_emerges`); O(n);
    (3) on a `Valid` input `ivs`, the composed derived program is a faithful merge — the REUSED
        `LC56.merge_correct`, not re-proved here.

    The two programs (the folds) are PRODUCED by the law; the correctness is reused. -/
theorem merge_derived_correct (ivs : List (Int × Int)) (hval : LC56.Valid ivs) :
    ((graph isortCLFold : dCL Unit (Int × Int) ⟶ ⟨List (Int × Int)⟩)
        = cataR (consScalarAlg gSort stSort))
      ∧ ((graph mergeCLFold : dCL Unit (Int × Int) ⟶ ⟨(Int × Int) → List (Int × Int)⟩)
          = cataR (consScalarAlg gMerge stMerge))
      ∧ LC56.IsMerge ivs (mergeFn_derived ivs) := by
  refine ⟨isort_emerges, mergeRun_emerges, ?_⟩
  rw [mergeFn_derived_eq ivs]
  exact LC56.merge_correct ivs hval

/-! ## Running / cross-checking the reshaped folds

  The relational catamorphisms `cataFold (consScalarAlg …)` are not `decide`-computable (the merge
  fold's carrier is a function type), so we `decide` the computable witnesses (`mergeFn_derived`,
  applied `List (Int × Int)` values) instead — never the function carrier itself. -/

-- LeetCode 56's own example: `[[1,3],[2,6],[8,10],[15,18]] → [[1,6],[8,10],[15,18]]`.
example : mergeFn_derived [(1, 3), (2, 6), (8, 10), (15, 18)] = [(1, 6), (8, 10), (15, 18)] := by decide
-- Touching intervals DO merge (`≤`, not `<`): `[[1,4],[4,5]] → [[1,5]]`.
example : mergeFn_derived [(1, 4), (4, 5)] = [(1, 5)] := by decide
-- Unsorted input is sorted first; same answer as the first example.
example : mergeFn_derived [(2, 6), (1, 3), (8, 10), (15, 18)] = [(1, 6), (8, 10), (15, 18)] := by decide
-- Empty input.
example : mergeFn_derived ([] : List (Int × Int)) = [] := by decide

/-- The reshaped sort fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg gSort stSort) (CL.ofList [(2, 6), (1, 3)]) (isortCLFold (CL.ofList [(2, 6), (1, 3)])) := by
  have h : (graph isortCLFold : dCL Unit (Int × Int) ⟶ ⟨List (Int × Int)⟩)
      (CL.ofList [(2, 6), (1, 3)]) (isortCLFold (CL.ofList [(2, 6), (1, 3)])) := rfl
  rw [isort_emerges] at h
  exact h

/-- The reshaped merge fold genuinely relates the converted input to the (function-valued)
    catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg gMerge stMerge) (CL.ofList [(2, 6), (8, 10)]) (mergeCLFold (CL.ofList [(2, 6), (8, 10)])) := by
  have h : (graph mergeCLFold : dCL Unit (Int × Int) ⟶ ⟨(Int × Int) → List (Int × Int)⟩)
      (CL.ofList [(2, 6), (8, 10)]) (mergeCLFold (CL.ofList [(2, 6), (8, 10)])) := rfl
  rw [mergeRun_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC56D
