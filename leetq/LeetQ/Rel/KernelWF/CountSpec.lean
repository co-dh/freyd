/-
  Counting over position lists, as `leftDiv` counts: a 0/1 term per row, and a filter's length as such a sum.
-/
namespace LeetQ.Rel.Alg

/-- At most one position below `n` meets `P` when any two that meet it are one. -/
theorem filter_range_length_le_one : ∀ {n : Nat} {P : Nat → Bool},
    (∀ j j', j < n → j' < n → P j = true → P j' = true → j = j') → ((List.range n).filter P).length ≤ 1
  | 0, _, _ => by simp
  | n + 1, P, h => by
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hn : P n = true
    · have e : (List.range n).filter P = [] := List.filter_eq_nil_iff.2 fun j hj hP => by
        have := List.mem_range.1 hj
        exact absurd (h j n (by omega) (by omega) hP hn) (by omega)
      simp [e, hn]
    · have := filter_range_length_le_one (n := n) (P := P) fun j j' hj hj' => h j j' (by omega) (by omega)
      simp [hn]; omega

/-- A sum of terms each below its partner's equals the partner's sum exactly when every term does. -/
theorem sum_map_eq_iff : ∀ {l : List Nat} {f g : Nat → Nat}, (∀ i ∈ l, f i ≤ g i) →
    (l.map f).sum ≤ (l.map g).sum ∧ ((l.map f).sum = (l.map g).sum ↔ ∀ i ∈ l, f i = g i)
  | [], _, _, _ => by simp
  | a :: t, f, g, h => by
    obtain ⟨hle, hiff⟩ := sum_map_eq_iff (l := t) (f := f) (g := g) fun i hi => h i (by simp [hi])
    have ha := h a (by simp)
    simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
    exact ⟨by omega, ⟨fun e => ⟨by omega, hiff.1 (by omega)⟩, fun ⟨e1, e2⟩ => by rw [e1, hiff.2 e2]⟩⟩

/-- Filtering a list's positions by a test on the element there, then reading the elements, filters the list. -/
theorem filter_getD_map {α : Type} (L : List α) (d : α) (Q : α → Bool) :
    ((List.range L.length).filter (fun t => Q (L.getD t d))).map (fun t => L.getD t d) = L.filter Q := by
  have hL : (List.range L.length).map (fun t => L.getD t d) = L :=
    List.ext_getElem (by simp) fun t h1 h2 => by simp [List.getElem?_eq_getElem h2]
  conv => rhs; rw [← hL]
  rw [List.filter_map]; rfl

/-- A filter's length is the sum of its 0/1 indicator. -/
theorem length_filter_sum : ∀ (l : List Nat) (p : Nat → Bool),
    (l.filter p).length = (l.map fun i => if p i then 1 else 0).sum
  | [], _ => rfl
  | a :: t, p => by cases h : p a <;> simp [h, length_filter_sum t p] <;> omega

/-- **The count of `leftDiv`**: of the pairs `(i, j)` with `e j i`, those with `p i` and `q j` are as many as
    the `i` with `p i` exactly when each such `i` has a `j` with `e j i` and `q j` — given at most one such `j`. -/
theorem count_pairs (nR nS : Nat) (e : Nat → Nat → Bool) (p q : Nat → Bool)
    (hinj : ∀ i < nR, ∀ j j', j < nS → j' < nS → e j i = true → q j = true → e j' i = true → q j' = true → j = j') :
    (((List.range nR).flatMap fun i => ((List.range nS).filter fun j => e j i).map (i, ·)).filter
        fun ij => p ij.1 && q ij.2).length = ((List.range nR).filter p).length ↔
      ∀ i < nR, p i = true → ∃ j < nS, e j i = true ∧ q j = true := by
  have hg : ∀ i, (((List.range nS).filter fun j => e j i).map (i, ·)).filter (fun ij => p ij.1 && q ij.2) =
      if p i then (((List.range nS).filter fun j => e j i && q j).map (i, ·)) else [] := fun i => by
    rw [List.filter_map]
    cases hp : p i
    · simp [Function.comp_def, hp]
    · simp only [Function.comp_def, hp, Bool.true_and, List.filter_filter, ite_true]
      congr 2; funext j; exact Bool.and_comm _ _
  rw [List.filter_flatMap, List.length_flatMap, length_filter_sum]
  simp only [hg]
  have hle : ∀ i ∈ List.range nR, (if p i then ((List.range nS).filter fun j => e j i && q j).length else 0) ≤
      (if p i then 1 else 0) := fun i hi => by
    split
    · exact filter_range_length_le_one fun j j' hj hj' h1 h2 => by
        simp only [Bool.and_eq_true] at h1 h2
        exact hinj i (List.mem_range.1 hi) j j' hj hj' h1.1 h1.2 h2.1 h2.2
    · exact Nat.le_refl 0
  simp only [apply_ite List.length, List.length_map, List.length_nil]
  rw [(sum_map_eq_iff hle).2]
  refine ⟨fun h i hi hp => ?_, fun h i hi => ?_⟩
  · have := h i (List.mem_range.2 hi)
    rw [if_pos hp, if_pos hp] at this
    obtain ⟨j, hj⟩ := List.exists_mem_of_length_pos (l := (List.range nS).filter fun j => e j i && q j) (by omega)
    obtain ⟨hj1, hj2⟩ := List.mem_filter.1 hj
    simp only [Bool.and_eq_true] at hj2
    exact ⟨j, List.mem_range.1 hj1, hj2⟩
  · split
    · rename_i hp
      obtain ⟨j, hj, h1, h2⟩ := h i (List.mem_range.1 hi) hp
      have h0 : 0 < ((List.range nS).filter fun j => e j i && q j).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨List.mem_range.2 hj, by simp [h1, h2]⟩)
      have := hle i hi
      rw [if_pos hp, if_pos hp] at this
      omega
    · rfl

end LeetQ.Rel.Alg
