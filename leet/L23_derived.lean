/-
  LeetCode 23 — Merge k Sorted Lists — an O(N log N) HEAP re-derivation (was O(k·N)).

  `leet/L23.lean` merges `k` sorted lists by RIGHT-FOLDING `L21`'s binary merge over the outer
  list, base `[]` (`mergeKFn lists = lists.foldr LC21.mergeFn []`).  That sequential fold rescans a
  growing accumulator on every one of the `k` cons steps, so it costs O(k·N) (`N` = total elements).

  This file replaces the PROGRAM with a min-heap heapsort of the flattened input and proves it
  correct Sorry-free, reusing `AOP/A6_Heap.lean` (leftist min-heap over `Int`) UNMODIFIED:

    * `heapMerge lists := drain (ofList (lists.flatten))`

    pour every element of every list into the heap (`ofList` = `N` inserts), then drain all `N`
    minima (`drain`).  With a leftist heap each `insert`/`popMin?` is O(log N), so the whole merge is
    O(N log N) — a genuine asymptotic win over O(k·N) once `k` is large.  (The complexity is
    INFORMAL, as in `A6_Heap`; only functional correctness is machine-checked.)

  This is option (b) of the task: a clean heapsort of the multiset, using `A6_Heap` as-is.  The
  further improvement to the textbook O(N log k) — keep only the `k` current heads in the heap and,
  after each `popMin?`, `insert` that list's NEXT element — needs a heap whose entries carry the
  REST of their list (`Int × List Int` keyed on the value), i.e. a small variant of `A6_Heap`; it is
  NOT done here to avoid duplicating the leftist-heap machinery.

  **The drain is certified as a HYLOMORPHISM.**  The heap drain is a divide-and-conquer UNFOLD, the
  dual of a catamorphism, so it is captured not by a fold law but by the RECURSIVE-COALGEBRA
  hylomorphism uniqueness law `Hylo.hyloFold_unique` (`AOP/A6_GenHylo.lean`).  We recast the drain
  as a `Nat`-measured recursive coalgebra and let the law EMIT it:

    * coalgebra `drainCo h` reads `popMin?` — empty ↦ `Sum.inl ()` leaf, non-empty ↦ `Sum.inr (min,rest)`;
    * measure `drainμ h := (toList h).length`, strictly dropped on every `Sum.inr` step (`drain_dec`,
      from `A6_Heap.popMin?_perm`);
    * `drain` is the well-founded recursion on `drainμ`, and `drain_emerges` proves — via
      `hyloFold_unique` — that `graph drain` IS the relational hylomorphism
      `hyloR drainCo drainμ drain_dec (fun _ => []) (· :: ·)`.

  `heapMerge lists = drain (ofList lists.flatten)` (`heapMerge_eq_drain`), so the O(N log N) merge IS
  this hylomorphism.  The efficient PROGRAM is PRODUCED by the law; correctness is reused (below).

  What is proved:
    * `drain_emerges`     — the drain IS the hylomorphism of the measured coalgebra (`hyloFold_unique`);
    * `heapMerge_eq_drain`— the merge is that drain on the heap of the flattened input;
    * `heapMerge_sorted`  — the output is `Sorted`, UNCONDITIONALLY (heapsort needs no sorted inputs);
    * `heapMerge_perm`    — the output is a permutation of `lists.flatten` (exact multiset);
    * `heapMerge_eq_mergeK` — on VALID (sorted) inputs it returns the IDENTICAL list to `L23.mergeKFn`
        (a genuine drop-in replacement), via `sorted_count_ext` (a sorted list is determined by its
        multiset);
    * `derivedSolve ⊑ LC23.spec` — the heap solver refines LeetCode 23's spec (sorted + summed
        multiplicity), the morphism-level statement analogous to `L23.solve_le_spec`.

  Correctness of the ORIGINAL `mergeKFn` (sortedness + exact summed multiplicity) is REUSED verbatim
  from `L23.merge_k_correct`, not re-proved.

  Mathlib-free (`import AOP.A6_Heap`, `AOP.A6_GenHylo`); headline axioms ⊆ {propext, Quot.sound}.
-/
import leet.L23
import AOP.A6_Heap
import AOP.A6_GenHylo

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC23D

open Freyd Freyd.Heap

/-! ## Multiset `count` facts (all elementary `List` reasoning) -/

/-- `count` is additive over `++`. -/
theorem count_append (v : Int) (a b : List Int) :
    LC21.count v (a ++ b) = LC21.count v a + LC21.count v b := by
  induction a with
  | nil => show LC21.count v b = 0 + LC21.count v b; omega
  | cons x a ih =>
      show (if x = v then (1 : Nat) else 0) + LC21.count v (a ++ b)
         = ((if x = v then (1 : Nat) else 0) + LC21.count v a) + LC21.count v b
      rw [ih]; omega

/-- The count in the flattened input is exactly `L23.totalCount`, the sum of the per-list counts. -/
theorem count_flatten (v : Int) : ∀ lists : List (List Int),
    LC21.count v lists.flatten = LC23.totalCount v lists := by
  intro lists
  induction lists with
  | nil => rfl
  | cons l rest ih =>
      show LC21.count v (l ++ rest.flatten) = LC23.totalCount v (l :: rest)
      rw [count_append, ih]
      rfl

/-- `count` is invariant under permutation (proved by induction on the `List.Perm` derivation). -/
theorem count_perm {xs ys : List Int} (hp : List.Perm xs ys) (v : Int) :
    LC21.count v xs = LC21.count v ys := by
  induction hp with
  | nil => rfl
  | cons x hp ih => simp only [LC21.count]; rw [ih]
  | swap x y l => simp only [LC21.count]; omega
  | trans hp1 hp2 ih1 ih2 => rw [ih1, ih2]

/-- The head of a list occurs at least once. -/
theorem count_self_pos (a : Int) (l : List Int) : 0 < LC21.count a (a :: l) := by
  show 0 < (if a = a then (1 : Nat) else 0) + LC21.count a l
  rw [if_pos rfl]; omega

/-- A value with positive count is a member. -/
theorem mem_of_count_pos {v : Int} : ∀ l : List Int, 0 < LC21.count v l → v ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (Nat.lt_irrefl 0)
  | cons x xs ih =>
      intro h
      by_cases hxv : x = v
      · subst hxv; exact List.mem_cons_self
      · have e : LC21.count v (x :: xs) = LC21.count v xs := by
          show (if x = v then (1 : Nat) else 0) + LC21.count v xs = LC21.count v xs
          rw [if_neg hxv]; omega
        rw [e] at h
        exact List.mem_cons_of_mem x (ih h)

/-! ## A sorted list is determined by its multiset -/

/-- In a sorted list, the head is `≤` every other element. -/
theorem sorted_head_le : ∀ (a : Int) (l : List Int), LC21.Sorted (a :: l) → ∀ z ∈ l, a ≤ z := by
  intro a l
  induction l generalizing a with
  | nil => intro _ z hz; exact absurd hz List.not_mem_nil
  | cons c l ih =>
      intro hs z hz
      obtain ⟨hac, hScl⟩ := hs
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hac
      · exact Int.le_trans hac (ih c hScl z hz')

/-- **Sorted lists with the same multiset are equal.**  The bridge that lets the heap output be
    identified with `L23.mergeKFn`'s: two sorted lists whose `count` agrees at every value coincide.
    Proof: matching heads must be equal (each is the minimum, so `≤` the other), then strip and
    recurse. -/
theorem sorted_count_ext : ∀ xs ys : List Int,
    LC21.Sorted xs → LC21.Sorted ys → (∀ v, LC21.count v xs = LC21.count v ys) → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _ hc
      cases ys with
      | nil => rfl
      | cons b ys' =>
          exfalso
          have hpos := count_self_pos b ys'
          have hnil : LC21.count b ([] : List Int) = 0 := rfl
          have heq := hc b
          omega
  | cons a xs' ih =>
      intro ys hSx hSy hc
      cases ys with
      | nil =>
          exfalso
          have hpos := count_self_pos a xs'
          have hnil : LC21.count a ([] : List Int) = 0 := rfl
          have heq := hc a
          omega
      | cons b ys' =>
          have hax : ∀ z ∈ xs', a ≤ z := sorted_head_le a xs' hSx
          have hby : ∀ z ∈ ys', b ≤ z := sorted_head_le b ys' hSy
          have ha_in : a ∈ b :: ys' := by
            apply mem_of_count_pos
            have hpos := count_self_pos a xs'
            rw [hc a] at hpos; exact hpos
          have hb_in : b ∈ a :: xs' := by
            apply mem_of_count_pos
            have hpos := count_self_pos b ys'
            rw [← hc b] at hpos; exact hpos
          have hba : b ≤ a := by
            rcases List.mem_cons.mp ha_in with rfl | ha'
            · exact Int.le_refl _
            · exact hby a ha'
          have hab : a ≤ b := by
            rcases List.mem_cons.mp hb_in with rfl | hb'
            · exact Int.le_refl _
            · exact hax b hb'
          have hab_eq : a = b := Int.le_antisymm hab hba
          subst hab_eq
          have hSx' : LC21.Sorted xs' := ((LC21.sorted_cons a xs').mp hSx).2
          have hSy' : LC21.Sorted ys' := ((LC21.sorted_cons a ys').mp hSy).2
          have hc' : ∀ v, LC21.count v xs' = LC21.count v ys' := by
            intro v
            have h := hc v
            have e1 : LC21.count v (a :: xs') = (if a = v then (1 : Nat) else 0) + LC21.count v xs' := rfl
            have e2 : LC21.count v (a :: ys') = (if a = v then (1 : Nat) else 0) + LC21.count v ys' := rfl
            rw [e1, e2] at h
            omega
          rw [ih ys' hSx' hSy' hc']

/-! ## Draining the heap: sorted + permutation, straight from `A6_Heap`'s API

  `drain` and `drain_perm` live in `A6_Heap`; sortedness needs `LC21.Sorted`, so it is proved here,
  recursing on the element count through `A6_Heap.drain_node`. -/

/-- Building a heap by repeated `insert` preserves the heap order. -/
theorem ofList_isHeap : ∀ xs : List Int, IsHeap (ofList xs)
  | [] => empty_isHeap
  | x :: xs => by
      show IsHeap (insert x (ofList xs))
      exact insert_isHeap (ofList_isHeap xs)

/-- Building a heap preserves the multiset: its elements permute the input list. -/
theorem ofList_perm : ∀ xs : List Int, List.Perm (toList (ofList xs)) xs
  | [] => List.Perm.refl _
  | x :: xs => by
      show List.Perm (toList (insert x (ofList xs))) (x :: xs)
      exact (insert_perm x (ofList xs)).trans (List.Perm.cons x (ofList_perm xs))

/-- **The drain is sorted.**  Each popped minimum `v` is `≤` everything still in the heap
    (`popMin?_is_min`), hence `≤` the head of the rest of the drain (which came from the heap by
    `drain_perm`); with the tail sorted by recursion, `sorted_cons` assembles `Sorted (v :: rest)`. -/
theorem drain_sorted : ∀ h : LHeap, IsHeap h → LC21.Sorted (drain h)
  | .empty, _ => by rw [drain_empty]; exact trivial
  | .node k v l r, hh => by
      have hpop : popMin? (LHeap.node k v l r) = some (v, merge l r) := rfl
      have hperm := popMin?_perm hpop
      rw [drain_node]
      refine (LC21.sorted_cons v _).mpr ⟨?_, drain_sorted (merge l r) (popMin?_isHeap hh hpop)⟩
      cases hd : drain (merge l r) with
      | nil => exact trivial
      | cons z t =>
          show v ≤ z
          have hz : z ∈ toList (merge l r) :=
            (drain_perm (merge l r)).mem_iff.mpr (by rw [hd]; exact List.mem_cons_self)
          exact popMin?_is_min hh hpop z (hperm.mem_iff.mpr (List.mem_cons_of_mem v hz))
termination_by h => (toList h).length
decreasing_by
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  omega

/-! ## The efficient program and its correctness -/

/-- **The O(N log N) program**: heapsort of the flattened input.  Pour every element of every list
    into a leftist min-heap (`ofList`), then drain it (`drain`). -/
def heapMerge (lists : List (List Int)) : List Int :=
  drain (ofList lists.flatten)

/-- The heap merge is sorted — UNCONDITIONALLY (heapsort needs no assumption on the inputs). -/
theorem heapMerge_sorted (lists : List (List Int)) : LC21.Sorted (heapMerge lists) :=
  drain_sorted _ (ofList_isHeap lists.flatten)

/-- The heap merge is a permutation of the flattened input (exact multiset preservation). -/
theorem heapMerge_perm (lists : List (List Int)) : List.Perm (heapMerge lists) lists.flatten :=
  (drain_perm _).symm.trans (ofList_perm lists.flatten)

/-- Consequently the heap merge realises the exact SUMMED multiplicity across all input lists. -/
theorem heapMerge_count (v : Int) (lists : List (List Int)) :
    LC21.count v (heapMerge lists) = LC23.totalCount v lists := by
  rw [count_perm (heapMerge_perm lists) v, count_flatten v lists]

/-- **Drop-in equivalence.**  On VALID (sorted) inputs the heap merge returns the IDENTICAL list to
    the original `L23.mergeKFn`: both are sorted with the same multiset, so `sorted_count_ext` forces
    them equal.  The O(N log N) heapsort is a faithful replacement for the O(k·N) sequential fold. -/
theorem heapMerge_eq_mergeK (lists : List (List Int)) (hpre : ∀ l ∈ lists, LC21.Sorted l) :
    heapMerge lists = LC23.mergeKFn lists := by
  obtain ⟨hSk, hCk⟩ := LC23.merge_k_correct lists hpre
  exact sorted_count_ext _ _ (heapMerge_sorted lists) hSk
    (fun v => (heapMerge_count v lists).trans (hCk v).symm)

/-! ## `Rel(Set)` packaging: the derived heap solver refines LeetCode 23's spec -/

/-- The derived solver as a morphism `dInput ⟶ dAns` in `Rel(Set)` — the graph of `heapMerge`. -/
def derivedSolve : LC23.dInput ⟶ LC23.dAns := graph heapMerge

/-- `derivedSolve` is a `Map` — a genuine function. -/
theorem derivedSolve_map : Map derivedSolve := graph_map heapMerge

/-- **The derived heap solver refines the LeetCode 23 specification** (the morphism-level headline,
    analogous to `L23.solve_le_spec`): every answer it returns is sorted with the summed multiplicity
    of the inputs.  In fact — heapsort — the spec's conclusion holds even without the sortedness
    precondition, so refinement is immediate from `heapMerge_sorted` and `heapMerge_count`. -/
theorem derivedSolve_refines_spec : derivedSolve ⊑ LC23.spec := by
  refine le_iff.mpr (fun lists l h => ?_)
  have hl : l = heapMerge lists := h
  subst hl
  intro _
  exact ⟨heapMerge_sorted lists, fun v => heapMerge_count v lists⟩

/-! ## The heap drain, certified as a HYLOMORPHISM (`A6_GenHylo`)

  The heap drain (`A6_Heap.drain`) is well-founded on the element count.  Its shape — pop the
  minimum, emit it, recurse on the remaining heap, stop at the empty heap — is exactly the recurrence
  of a `Nat`-measured RECURSIVE COALGEBRA (`Hylo.hyloFold`).  We recast the drain as a proper heap-hylo:

    * coalgebra `drainCo h` reads `popMin?` — empty heap ↦ `Sum.inl ()` leaf (emit `[]`), non-empty ↦
      `Sum.inr (min, rest)` node;
    * measure `drainμ h := (toList h).length`, the number of elements left;
    * every `Sum.inr` step strictly drops the measure (`drain_dec`), because `popMin?` removes exactly
      one element (`A6_Heap.popMin?_perm`);
    * algebra `[g := fun _ => [], st := (· :: ·)]` re-folds the finite call tree into the sorted output.

  `drain` is that recursion written directly (well-founded on `drainμ`'s count), and `drain_emerges` proves — via
  `Hylo.hyloFold_unique`, the recursive-coalgebra dual of the fold-uniqueness laws — that it IS the
  relational hylomorphism `hyloR drainCo drainμ drain_dec (fun _ => []) (· :: ·)`.  The efficient PROGRAM
  is thereby PRODUCED by the law, not hand-written and inductively verified. -/

/-- The drain coalgebra: an empty heap is a `Sum.inl ()` leaf (nothing more to emit); a non-empty heap
    yields its minimum and the remaining heap as a `Sum.inr` node. -/
def drainCo (h : LHeap) : Sum Unit (Int × LHeap) :=
  match popMin? h with
  | none => Sum.inl ()
  | some (m, h') => Sum.inr (m, h')

/-- The measure: the number of elements still in the heap. -/
def drainμ (h : LHeap) : Nat := (toList h).length

/-- Every `Sum.inr` step of `drainCo` strictly drops `drainμ`: `popMin?` removes exactly one element
    (`popMin?_perm` gives `toList h ~ m :: toList h'`), so `(toList h').length + 1 = (toList h).length`. -/
theorem drain_dec : ∀ h e h', drainCo h = Sum.inr (e, h') → drainμ h' < drainμ h := by
  intro h e h' hc
  cases hp : popMin? h with
  | none => simp only [drainCo, hp] at hc; nomatch hc
  | some p =>
      obtain ⟨m, hh⟩ := p
      simp only [drainCo, hp, Sum.inr.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, rfl⟩ := hc
      have hlen := (popMin?_perm hp).length_eq
      simp only [drainμ, List.length_cons] at hlen ⊢
      omega

/-- **The drain IS the hylomorphism.**  `drain` obeys the hylomorphism recurrence for the coalgebra
    `drainCo`, measure `drainμ`, algebra `[fun _ => [], (· :: ·)]`, so by `hyloFold_unique` its graph
    equals the relational hylomorphism.  The remaining `?_` is exactly that recurrence, discharged in
    place by unfolding `drain` / `drainCo` on each heap constructor (a separate recurrence lemma fails
    the matcher-aux `isDefEq`, per the `A6_GenHylo` note). -/
theorem drain_emerges :
    (graph drain : (⟨LHeap⟩ : RelSet.{0}) ⟶ ⟨List Int⟩)
      = Hylo.hyloR drainCo drainμ drain_dec (fun _ => []) (· :: ·) := by
  refine Hylo.hyloFold_unique drainCo drainμ drain_dec (fun _ => []) (· :: ·) drain ?_
  intro h
  cases h with
  | empty => rw [drain_empty]; rfl
  | node k v l r => rw [drain_node]; rfl

/-- The heap merge is the drain hylomorphism applied to the heap of the flattened input. -/
theorem heapMerge_eq_drain (lists : List (List Int)) :
    heapMerge lists = drain (ofList lists.flatten) := rfl

/-! ## Correctness headline -/

/-- **Headline** (`LC23D.merge_k_derived_correct`).  The O(N log N) heap merge:

    (1) the heap drain is a PROPER HYLOMORPHISM: `graph drain` equals the relational hylomorphism
        `hyloR drainCo drainμ drain_dec (fun _ => []) (· :: ·)` of the measured recursive coalgebra —
        the efficient PROGRAM is PRODUCED by `Hylo.hyloFold_unique`, not a hand-written fuel loop
        (`drain_emerges`);
    (2) the O(N log N) merge IS that drain applied to the heap of the flattened input, so the whole
        program is the hylomorphism (`heapMerge_eq_drain`);
    (3) it is `Sorted` UNCONDITIONALLY (heapsort — `heapMerge_sorted`);
    (4) it is a permutation of the flattened input, i.e. the EXACT multiset (`heapMerge_perm`);
    (5) on VALID (sorted) inputs it returns the IDENTICAL list to the original O(k·N) `L23.mergeKFn`, a
        genuine drop-in replacement (`heapMerge_eq_mergeK`);
    (6) as a `Rel(Set)` morphism it REFINES LeetCode 23's spec — sorted output with summed multiplicity
        (`derivedSolve_refines_spec`); and
    (7) the original program's correctness — sortedness AND exact summed multiplicity — is REUSED
        verbatim from `L23.merge_k_correct`, not re-proved.

    The efficient PROGRAM (the heap drain) is EMITTED by the hylomorphism law; the specification
    correctness is reused. -/
theorem merge_k_derived_correct :
    ((graph drain : (⟨LHeap⟩ : RelSet.{0}) ⟶ ⟨List Int⟩)
        = Hylo.hyloR drainCo drainμ drain_dec (fun _ => []) (· :: ·))
      ∧ (∀ lists : List (List Int), heapMerge lists = drain (ofList lists.flatten))
      ∧ (∀ lists : List (List Int), LC21.Sorted (heapMerge lists))
      ∧ (∀ lists : List (List Int), List.Perm (heapMerge lists) lists.flatten)
      ∧ (∀ lists : List (List Int), (∀ l ∈ lists, LC21.Sorted l) →
           heapMerge lists = LC23.mergeKFn lists)
      ∧ (derivedSolve ⊑ LC23.spec)
      ∧ (∀ lists : List (List Int), (∀ l ∈ lists, LC21.Sorted l) →
           LC21.Sorted (LC23.mergeKFn lists) ∧
           ∀ v, LC21.count v (LC23.mergeKFn lists) = LC23.totalCount v lists) :=
  ⟨drain_emerges, heapMerge_eq_drain, heapMerge_sorted, heapMerge_perm, heapMerge_eq_mergeK,
   derivedSolve_refines_spec, LC23.merge_k_correct⟩

/-! ## Running the heap merge

  `merge` in `A6_Heap` is well-founded, so `decide`/kernel `rfl` get stuck on any `heapMerge` result;
  we evaluate with the compiler (`#eval`) instead, as `A6_Heap` does.  Each `== …` prints `true`. -/

-- expect true: [[1,4,5],[1,3,4],[2,6]] → [1,1,2,3,4,4,5,6]
#eval heapMerge [[1, 4, 5], [1, 3, 4], [2, 6]] == [1, 1, 2, 3, 4, 4, 5, 6]
-- expect true: gaps / negatives  [[1],[],[-1,3]] → [-1,1,3]
#eval heapMerge [[1], [], [-1, 3]] == [-1, 1, 3]
-- expect true: empty input
#eval heapMerge ([] : List (List Int)) == []
-- expect true: agrees with the original L23 program on the LeetCode example
#eval heapMerge [[1, 4, 5], [1, 3, 4], [2, 6]] == LC23.mergeKFn [[1, 4, 5], [1, 3, 4], [2, 6]]

end Freyd.Alg.RelSet.LC23D
