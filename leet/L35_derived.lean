/-
  LeetCode 35 — Search Insert Position — DERIVED, in TWO parts: (1) the book's O(n) linear scan
  EMERGES as a `Nat`-carrier `ConsList` catamorphism, and (2) that scan is bridged to the already
  VERIFIED O(log n) `Freyd.BinSearch.lowerBound`, giving the log-time program for free.

  1. **Part 1 — emergence.**  `leet/L35.lean`'s `insertPosFn` is a front-to-back scan holding an
     external parameter `target : Int` fixed; for each `target` it is the recursion `h (wrap ()) =
     0`, `h (cons x xs) = if target ≤ x then 0 else 1 + h xs`.  Feeding base `g target` and step
     `st target` to the general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique`
     (`AOP/A6_GenFold.lean`) produces `foldFn target` as `cataR (consScalarAlg (g target)
     (st target))` — the recursion is never hand-written.  `foldFn` is bridged to `insertPosFn` on
     `CL.ofList`-reshaped input by structural induction, giving the UNCONDITIONAL equality
     `derivedSolve = LC35.solve` (Headline shape 1 — the answer is a function of the input, no
     `Sorted` precondition needed, exactly as `insertPos_correct` remarks).

  2. **Part 2 — the O(n) → O(log n) bridge.**  `AOP/A6_BinSearch.lean`'s `lowerBound` is the
     verified halving search: `lowerBound a x` is the least `i ≤ a.size` with `x ≤ a[i]`.  On a
     `Sorted` list, `insertPosFn` and `lowerBound` characterize the SAME index (the split point
     "before it `< target`, at it `≥ target`"), and that splitting index is unique.
     `lowerBound_eq_insertPosFn` proves this by the split-index uniqueness argument: trichotomy on
     the two candidate indices, each branch contradicted by pitting one search's "left of split is
     `< target`" clause against the other's "at split is `≥ target`" clause
     (`BinSearch.lt_of_lt_lowerBound`/`BinSearch.le_of_lowerBound_le` vs `insertPos_correct`'s own
     two clauses).  `LC35.insertPos_correct`'s SPEC is reused verbatim; nothing about correctness is
     re-derived.  Headline shape 1 again, now conditional on `Sorted` (binary search's own
     precondition): `derivedSolveBS = LC35.solve` pointwise on sorted inputs.  Complexity: Part 1 is
     O(n) (one comparison per element, same as the book scan); Part 2 is O(log n) (halving search on
     the sorted array) — `lowerBound`'s `go` does O(log n) comparisons (Lean verifies behaviour, not
     running time).

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import AOP.A6_BinSearch
import leet.L35

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC35D

open Freyd
open Freyd.Alg.RelSet.CL (ConsList dCL cataR consFold_unique consScalarAlg ofList)

/-! ## Part 1: the linear scan EMERGES as a `Nat`-carrier cons-list fold (one instance per
    `target`, since `target` is an external parameter, not part of the recursive structure). -/

/-- Base of the emergent algebra: the empty list scans to index `0`. -/
def g (target : Int) : Unit → Nat := fun _ => 0

/-- Step of the emergent algebra: stop (`0`) once the head is `≥ target`, otherwise recurse on the
    tail and add one — exactly `LC35.insertPosFn`'s own step. -/
def st (target : Int) : Int → Nat → Nat := fun x c => if target ≤ x then 0 else 1 + c

/-- The linear-scan fold, as structural recursion on the front-to-back `ConsList` (`target` held
    fixed).  Its own defining equations (`foldFn_wrap`/`foldFn_cons` below) are exactly `g`/`st`. -/
def foldFn (target : Int) : ConsList Unit Int → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons x xs => if target ≤ x then 0 else 1 + foldFn target xs

/-- Base condition (`rfl`): `foldFn target (wrap d) = g target d`. -/
theorem foldFn_wrap (target : Int) (d : Unit) : foldFn target (ConsList.wrap d) = g target d := rfl

/-- Step condition (`rfl`): `foldFn target (cons x xs) = st target x (foldFn target xs)`. -/
theorem foldFn_cons (target : Int) (x : Int) (xs : ConsList Unit Int) :
    foldFn target (ConsList.cons x xs) = st target x (foldFn target xs) := rfl

/-- **The program EMERGES from the general-carrier fold law.**  `foldFn target` is PRODUCED by
    `CL.consFold_unique` from the base `g target` and step `st target`; `graph (foldFn target)`
    equals the catamorphism of the emergent scalar algebra. -/
theorem foldFn_emerges (target : Int) :
    (graph (foldFn target) : dCL Unit Int ⟶ ⟨Nat⟩) = cataR (consScalarAlg (g target) (st target)) :=
  consFold_unique (g target) (st target) (foldFn target) (foldFn_wrap target) (foldFn_cons target)

/-- The `ConsList` fold agrees with `LC35.insertPosFn` on the `CL.ofList`-reshaped raw input, by
    structural induction (both sides unfold to the SAME `if target ≤ x then 0 else 1 + ⋯` step). -/
theorem foldFn_eq_insertPosFn (target : Int) : ∀ xs : List Int,
    foldFn target (ofList xs) = LC35.insertPosFn xs target
  | [] => rfl
  | x :: xs => by
      show (if target ≤ x then 0 else 1 + foldFn target (ofList xs)) =
        (if target ≤ x then 0 else 1 + LC35.insertPosFn xs target)
      rw [foldFn_eq_insertPosFn target xs]

/-- The derived allegory program (Part 1): reshape the raw list onto the initial `ConsList`
    algebra, then run the emergent linear-scan fold. -/
def derivedSolve : LC35.Input ⟶ LC35.Ans :=
  graph (fun p : List Int × Int => foldFn p.2 (ofList p.1))

/-- **Part 1 headline (equality refinement).**  The catamorphism-produced program EQUALS the
    book's `solve` — no `Sorted` hypothesis needed, matching `insertPos_correct`'s remark that the
    "first index `≥ target`" property holds of ANY list. -/
theorem derivedSolve_eq_solve : derivedSolve = LC35.solve := by
  apply hom_ext
  intro p m
  show m = foldFn p.2 (ofList p.1) ↔ m = LC35.insertPosFn p.1 p.2
  rw [foldFn_eq_insertPosFn p.2 p.1]

/-! ## Part 2: bridging to the O(log n) `Freyd.BinSearch.lowerBound` -/

/-- `LC242.Sorted` (the book's recursive "all-later-elements" form), restated as the index-pairwise
    monotonicity `BinSearch.Sorted` needs — by induction, peeling the head. -/
theorem sorted_index (xs : List Int) (hs : LC242.Sorted xs) :
    ∀ i j (hij : i < j) (hj : j < xs.length), xs[i]'(Nat.lt_trans hij hj) ≤ xs[j]'hj := by
  induction xs with
  | nil => intro i j hij hj; simp at hj
  | cons x xs ih =>
    intro i j hij hj
    obtain ⟨hhead, hs'⟩ := hs
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ jp =>
        have hjp : jp < xs.length := by simpa using hj
        have hmem : xs[jp]'hjp ∈ xs := List.getElem_mem hjp
        have hxj := hhead (xs[jp]'hjp) hmem
        simpa using hxj
    | succ ip =>
      cases j with
      | zero => omega
      | succ jp =>
        have hijp : ip < jp := by omega
        have hjp : jp < xs.length := by simpa using hj
        have hstep := ih hs' ip jp hijp hjp
        simpa using hstep

/-- `xs.toArray` is `BinSearch.Sorted` whenever `xs` is `LC242.Sorted`. -/
theorem sorted_toArray {xs : List Int} (hs : LC242.Sorted xs) :
    BinSearch.Sorted xs.toArray := by
  intro i j hij hj
  have hjp : j < xs.length := by simpa using hj
  simpa using sorted_index xs hs i j hij hjp

/-- **The split-index uniqueness argument.**  On a sorted list, the verified O(log n)
    `BinSearch.lowerBound` and the O(n) linear scan `LC35.insertPosFn` compute the SAME index:
    trichotomy on the two candidates, each strict-inequality branch contradicted by pitting one
    search's "left of the split is `< target`" clause against the other's "at the split is
    `≥ target`" clause — the two clauses cannot both hold of the SAME element. Reuses
    `LC35.insertPos_correct` and `BinSearch.lowerBound_spec`'s projections verbatim. -/
theorem lowerBound_eq_insertPosFn {xs : List Int} {target : Int} (hs : LC242.Sorted xs) :
    BinSearch.lowerBound xs.toArray target = LC35.insertPosFn xs target := by
  have hsA : BinSearch.Sorted xs.toArray := sorted_toArray hs
  obtain ⟨hc1, hc2, hc3⟩ := LC35.insertPos_correct xs target hs
  have hb1 : BinSearch.lowerBound xs.toArray target ≤ xs.toArray.size :=
    BinSearch.lowerBound_le_size xs.toArray target
  have hlen : xs.toArray.size = xs.length := by simp
  rcases Nat.lt_trichotomy (BinSearch.lowerBound xs.toArray target) (LC35.insertPosFn xs target)
      with hlt | heq | hgt
  · -- `lowerBound < insertPosFn`: the element AT `lowerBound` is both `≥ target` (BinSearch) and
    -- `< target` (it lies strictly left of `insertPosFn`, by `insertPos_correct`).
    exfalso
    have hbnd : BinSearch.lowerBound xs.toArray target < xs.toArray.size := by omega
    have hval := BinSearch.le_of_lowerBound_le hsA hbnd
    have hget : xs[BinSearch.lowerBound xs.toArray target]? =
        some (xs.toArray[BinSearch.lowerBound xs.toArray target]'hbnd) := by
      rw [← List.getElem?_toArray]
      exact getElem?_pos xs.toArray _ hbnd
    have hlt2 := hc2 (BinSearch.lowerBound xs.toArray target) _ hlt hget
    omega
  · exact heq
  · -- `insertPosFn < lowerBound`: the element AT `insertPosFn` is both `≥ target`
    -- (`insertPos_correct`) and `< target` (it lies strictly left of `lowerBound`, by BinSearch).
    exfalso
    have hidx : LC35.insertPosFn xs target < xs.toArray.size := by omega
    have hlt3 := BinSearch.lt_of_lt_lowerBound hsA (LC35.insertPosFn xs target) hgt hidx
    have hget : xs[LC35.insertPosFn xs target]? =
        some (xs.toArray[LC35.insertPosFn xs target]'hidx) := by
      rw [← List.getElem?_toArray]
      exact getElem?_pos xs.toArray _ hidx
    have hval := hc3 _ hget
    omega

/-- The derived O(log n) allegory program (Part 2): binary search on the sorted input array. -/
def derivedSolveBS : LC35.Input ⟶ LC35.Ans :=
  graph (fun p : List Int × Int => BinSearch.lowerBound p.1.toArray p.2)

/-- **Part 2 headline (equality refinement, on sorted inputs).**  On a `Sorted` list, the O(log n)
    `derivedSolveBS` computes EXACTLY the answer `LC35.solve` does.  `insertPos_correct` (the O(n)
    program's own spec) is REUSED verbatim, not re-derived — only the split-index UNIQUENESS
    (`lowerBound_eq_insertPosFn`) is new. -/
theorem derivedSolveBS_eq_solve {xs : List Int} {target : Int} (hs : LC242.Sorted xs) (m : Nat) :
    derivedSolveBS (xs, target) m ↔ LC35.solve (xs, target) m := by
  show m = BinSearch.lowerBound xs.toArray target ↔ m = LC35.insertPosFn xs target
  rw [lowerBound_eq_insertPosFn hs]

/-! ## Running the derived programs -/

example : foldFn 5 (ofList [1, 3, 5, 6]) = 2 := by decide
example : foldFn 2 (ofList [1, 3, 5, 6]) = 1 := by decide
example : foldFn 7 (ofList [1, 3, 5, 6]) = 4 := by decide

#guard BinSearch.lowerBound ([1, 3, 5, 6] : List Int).toArray 5 = 2
#guard BinSearch.lowerBound ([1, 3, 5, 6] : List Int).toArray 2 = 1
#guard BinSearch.lowerBound ([1, 3, 5, 6] : List Int).toArray 7 = 4

end Freyd.Alg.RelSet.LC35D
