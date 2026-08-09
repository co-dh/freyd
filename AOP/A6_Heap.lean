module

/-
  A mathlib-free purely functional min-priority-queue (leftist heap) over `Int`.

  This backs an O(N log k) re-derivation of "Merge k Sorted Lists": keep the current head of each
  of the `k` lists in one heap, repeatedly `popMin?` the global minimum, and `insert` that list's
  next element.  A leftist heap gives O(log n) `merge`/`insert`/`popMin?` (the complexity claim is
  INFORMAL — it is not stated or proved in Lean; only functional correctness is machine-checked).

  Representation: a leftist heap is a binary tree with a min-heap order (every node's value is ≤ all
  values below it) and the *leftist* shape invariant (the right spine is shortest, tracked by a
  stored `rank`).  Only the min-heap order and the multiset of elements matter for correctness, so
  the leftist shape is used to guide `merge` but never proved — it is pure performance bookkeeping.

  We chose a LEFTIST heap over a pairing heap because a plain binary tree gives clean *structural*
  induction for `toList`/`IsHeap`/all invariant lemmas; only `merge` needs well-founded recursion
  (on the total node count), a single standard obligation.  A pairing heap `node v (kids : List _)`
  is a *nested* inductive whose custom induction principle makes every proof fight the recursor.

  What is proved (all sorry-free; see `#print axioms` at the bottom):
  * `IsHeap`             — the min-heap order predicate.
  * `merge_isHeap`, `insert_isHeap`, `popMin?_isHeap` — the operations preserve it.
  * `merge_toList_perm`  — `merge` preserves the multiset (a `List.Perm` from Lean core).
  * `popMin?_perm`       — `popMin?` removes exactly the returned element.
  * `popMin?_is_min`     — in a heap, the popped element is the minimum.

  Mathlib-free: imports nothing outside Lean 4 core `Init`.  `List.Perm` (the `~` notation) and all
  the permutation lemmas used live in core `Init.Data.List.{Basic,Perm}`.
-/

namespace Freyd.Heap

open List  -- activates the `~` (List.Perm) notation and unqualifies the core Perm lemmas

/-! ## The leftist heap -/

/-- A leftist heap: `empty`, or a `node` carrying its `rank` (right-spine length, for `merge`),
    a value, and two child heaps. -/
public inductive LHeap where
  | empty : LHeap
  | node (rank : Nat) (v : Int) (l r : LHeap) : LHeap

/-- The empty heap — the starting point for building a heap with `insert`. -/
@[expose] public def empty : LHeap := .empty

/-- The stored rank (`0` for `empty`); the length of the right spine in a genuine leftist heap. -/
@[expose] public def rank : LHeap → Nat
  | .empty => 0
  | .node k _ _ _ => k

/-- Assemble a node from a value and two children, putting the higher-rank child on the left and
    recording the new rank.  This is the O(1) step that keeps the tree leftist. -/
@[expose] public def makeNode (v : Int) (a b : LHeap) : LHeap :=
  if rank a ≥ rank b then .node (rank b + 1) v a b else .node (rank a + 1) v b a

/-- Merge two heaps by walking down the right spines, always keeping the smaller root on top.
    Non-structural (recurses on the right child of one side), so it needs well-founded recursion on
    the total node count. -/
@[expose] public def merge : LHeap → LHeap → LHeap
  | .empty, h => h
  | h, .empty => h
  | .node k₁ v₁ l₁ r₁, .node k₂ v₂ l₂ r₂ =>
      if v₁ ≤ v₂ then makeNode v₁ l₁ (merge r₁ (.node k₂ v₂ l₂ r₂))
      else makeNode v₂ l₂ (merge (.node k₁ v₁ l₁ r₁) r₂)
termination_by a b => sizeOf a + sizeOf b

/-- A one-element heap. -/
@[expose] public def singleton (v : Int) : LHeap := .node 1 v .empty .empty

/-- Insert a value: merge in a singleton. -/
@[expose] public def insert (v : Int) (h : LHeap) : LHeap := merge (singleton v) h

/-- Remove the minimum: `empty ↦ none`; a node yields its root (the minimum, once `IsHeap` holds)
    and the merge of its two children. -/
@[expose] public def popMin? : LHeap → Option (Int × LHeap)
  | .empty => none
  | .node _ v l r => some (v, merge l r)

/-! ## Elements and the min-heap invariant -/

/-- All elements of the heap, as a list (a pre-order traversal). -/
@[expose] public def toList : LHeap → List Int
  | .empty => []
  | .node _ v l r => v :: (toList l ++ toList r)

/-- `rootLe v h`: the value `v` is ≤ every element of `h`. -/
@[expose] public def rootLe (v : Int) (h : LHeap) : Prop := ∀ x ∈ toList h, v ≤ x

/-- The min-heap order: every node's value is ≤ all values in its two subtrees, recursively. -/
@[expose] public def IsHeap : LHeap → Prop
  | .empty => True
  | .node _ v l r => rootLe v l ∧ rootLe v r ∧ IsHeap l ∧ IsHeap r

/-- `v ≤ everything` holds vacuously for the empty heap. -/
public theorem rootLe_empty (v : Int) : rootLe v .empty := fun _ h => nomatch h

/-- If `v` is ≤ the root of a heap, then (given the heap order) `v` is ≤ every element. -/
public theorem rootLe_of_le_root {v w : Int} {k : Nat} {l r : LHeap}
    (hvw : v ≤ w) (hh : IsHeap (.node k w l r)) : rootLe v (.node k w l r) := by
  obtain ⟨hl, hr, _, _⟩ := hh
  intro x hx
  simp only [toList, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx | hx
  · exact hvw
  · exact Int.le_trans hvw (hl x hx)
  · exact Int.le_trans hvw (hr x hx)

/-! ## `makeNode` characterisations -/

/-- `makeNode` reorders its two children but keeps the same multiset: its element list is a
    permutation of `v :: (elements of a ++ elements of b)`. -/
public theorem makeNode_toList_perm (v : Int) (a b : LHeap) :
    toList (makeNode v a b) ~ v :: (toList a ++ toList b) := by
  unfold makeNode
  split
  · exact Perm.refl _
  · exact Perm.cons v perm_append_comm

/-- `makeNode` preserves the heap order, given `v` bounds both children below. -/
public theorem makeNode_isHeap {v : Int} {a b : LHeap}
    (ha : rootLe v a) (hb : rootLe v b) (hia : IsHeap a) (hib : IsHeap b) :
    IsHeap (makeNode v a b) := by
  unfold makeNode
  split
  · exact ⟨ha, hb, hia, hib⟩
  · exact ⟨hb, ha, hib, hia⟩

/-! ## `merge` preserves the multiset -/

/-- A pure-list reassociation used for the `else` branch of `merge`. -/
public theorem perm_reassoc {α} (x : α) (A l r : List α) :
    x :: (l ++ (A ++ r)) ~ A ++ (x :: (l ++ r)) := by
  have inner : l ++ (A ++ r) ~ A ++ (l ++ r) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact (perm_append_comm).append_right r
  exact (Perm.cons x inner).trans perm_middle.symm

/-- `merge` preserves the multiset of elements: `toList (merge a b)` is a permutation of
    `toList a ++ toList b`.  Proved by well-founded induction following `merge`'s own recursion. -/
public theorem merge_toList_perm (a b : LHeap) : toList (merge a b) ~ toList a ++ toList b := by
  fun_induction merge a b with
  | case1 h => exact Perm.of_eq (by simp only [toList, List.nil_append])
  | case2 h => exact Perm.of_eq (by simp only [toList, List.append_nil])
  | case3 k₁ v₁ l₁ r₁ k₂ v₂ l₂ r₂ hle ih =>
      refine (makeNode_toList_perm v₁ l₁ (merge r₁ (.node k₂ v₂ l₂ r₂))).trans ?_
      refine (Perm.cons v₁ ((Perm.refl (toList l₁)).append ih)).trans ?_
      exact Perm.of_eq (by simp only [toList, List.cons_append, List.append_assoc])
  | case4 k₁ v₁ l₁ r₁ k₂ v₂ l₂ r₂ hlt ih =>
      refine (makeNode_toList_perm v₂ l₂ (merge (.node k₁ v₁ l₁ r₁) r₂)).trans ?_
      refine (Perm.cons v₂ ((Perm.refl (toList l₂)).append ih)).trans ?_
      exact perm_reassoc v₂ (toList (.node k₁ v₁ l₁ r₁)) (toList l₂) (toList r₂)

/-! ## `merge` preserves the heap order -/

public theorem merge_isHeap (a b : LHeap) : IsHeap a → IsHeap b → IsHeap (merge a b) := by
  fun_induction merge a b with
  | case1 h => intro _ hb; exact hb
  | case2 h => intro ha _; exact ha
  | case3 k₁ v₁ l₁ r₁ k₂ v₂ l₂ r₂ hle ih =>
      intro ha hb
      obtain ⟨hl1, hr1, hil1, hir1⟩ := ha
      refine makeNode_isHeap hl1 ?_ hil1 (ih hir1 hb)
      intro x hx
      rcases List.mem_append.mp ((merge_toList_perm r₁ (.node k₂ v₂ l₂ r₂)).mem_iff.mp hx) with h1 | h2
      · exact hr1 x h1
      · exact rootLe_of_le_root hle hb x h2
  | case4 k₁ v₁ l₁ r₁ k₂ v₂ l₂ r₂ hlt ih =>
      intro ha hb
      obtain ⟨hl2, hr2, hil2, hir2⟩ := hb
      have hle2 : v₂ ≤ v₁ := by omega
      refine makeNode_isHeap hl2 ?_ hil2 (ih ha hir2)
      intro x hx
      rcases List.mem_append.mp ((merge_toList_perm (.node k₁ v₁ l₁ r₁) r₂).mem_iff.mp hx) with h1 | h2
      · exact rootLe_of_le_root hle2 ha x h1
      · exact hr2 x h2

/-! ## The public API lemmas -/

/-- A singleton heap is a heap. -/
public theorem singleton_isHeap (x : Int) : IsHeap (singleton x) :=
  ⟨rootLe_empty x, rootLe_empty x, trivial, trivial⟩

/-- The empty heap is a heap. -/
public theorem empty_isHeap : IsHeap empty := trivial

/-- `insert` preserves the heap order. -/
public theorem insert_isHeap {x : Int} {h : LHeap} (hh : IsHeap h) : IsHeap (insert x h) :=
  merge_isHeap (singleton x) h (singleton_isHeap x) hh

/-- `insert` adds exactly one element: `toList (insert x h)` is a permutation of `x :: toList h`. -/
public theorem insert_perm (x : Int) (h : LHeap) : toList (insert x h) ~ x :: toList h := by
  refine (merge_toList_perm (singleton x) h).trans ?_
  exact Perm.of_eq (by simp only [singleton, toList, List.append_nil, List.nil_append,
    List.cons_append])

/-- `popMin?` removes exactly the returned element:
    if `popMin? h = some (m, h')` then `toList h` is a permutation of `m :: toList h'`. -/
public theorem popMin?_perm {h : LHeap} {m : Int} {h' : LHeap}
    (hp : popMin? h = some (m, h')) : toList h ~ m :: toList h' := by
  cases h with
  | empty => simp [popMin?] at hp
  | node k v l r =>
      simp only [popMin?, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact Perm.cons v (merge_toList_perm l r).symm

/-- `popMin?` preserves the heap order on the remainder. -/
public theorem popMin?_isHeap {h : LHeap} {m : Int} {h' : LHeap}
    (hh : IsHeap h) (hp : popMin? h = some (m, h')) : IsHeap h' := by
  cases h with
  | empty => simp [popMin?] at hp
  | node k v l r =>
      obtain ⟨_, _, hil, hir⟩ := hh
      simp only [popMin?, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨_, rfl⟩ := hp
      exact merge_isHeap l r hil hir

/-- In a heap, the popped element is the minimum of the whole heap. -/
public theorem popMin?_is_min {h : LHeap} {m : Int} {h' : LHeap}
    (hh : IsHeap h) (hp : popMin? h = some (m, h')) : ∀ x ∈ toList h, m ≤ x := by
  cases h with
  | empty => simp [popMin?] at hp
  | node k v l r =>
      obtain ⟨hl, hr, _, _⟩ := hh
      simp only [popMin?, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, _⟩ := hp
      intro x hx
      simp only [toList, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact Int.le_refl _
      · exact hl x hx
      · exact hr x hx

/-! ## Sanity checks

Kernel `decide`/`rfl` is intentionally NOT used here: `merge` is defined by well-founded recursion,
which does not reduce definitionally, so `decide` on any `merge` result gets stuck.  We evaluate with
the compiler (`#eval`) instead, which runs the extracted code.  The outputs should be sorted. -/

/-- Build a heap from a list by repeated `insert`. -/
@[expose] public def ofList (xs : List Int) : LHeap := xs.foldr insert empty

/-- Pop `n` minima (fuel-bounded so it is structurally recursive). -/
@[expose] public def popN : Nat → LHeap → List Int
  | 0, _ => []
  | n + 1, h =>
      match popMin? h with
      | none => []
      | some (m, h') => m :: popN n h'

-- expect [1, 2, 3, 5, 7, 8, 9]
#eval popN 10 (ofList [5, 3, 8, 1, 9, 2, 7])
-- expect [1, 2, 2, 4, 4] (duplicates preserved)
#eval popN 10 (ofList [4, 4, 1, 2, 2])
-- expect [-3, -1, 0, 2, 6] (negatives)
#eval popN 10 (ofList [2, -1, 6, -3, 0])

end Freyd.Heap
