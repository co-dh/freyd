/-
  `subseq`'s chain and its step's `keep` split, which `rep_subseqC` closes its fold with: the step
  `cons (pair el pend) ∪ pend`, whose `∪ pend` keeps a row's state alive past its array's end.
-/
import LeetQ.Rel.RepList

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN OpsN

/-- The chain `rep_foldBy_keep` leaves for `subseq`: rows `ys[t]` that are `xs[t] :: ys[t+1]` or `ys[t+1]`,
ending at `[]`, start at exactly the sublists of `xs`. -/
theorem subseq_chain {β : Type _} (xs w : List β) :
    (∃ ys : List (List β), ∃ hy : ys.length = xs.length + 1,
      ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm) = [] ∧
      (∀ t (ht : t < xs.length),
        ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) =
            xs[t]'ht :: ys[t+1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) ∨
          ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) =
            ys[t+1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm)) ∧
      w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.succ_pos _) hy.symm)) ↔ w.Sublist xs := by
  induction xs generalizing w with
  | nil =>
    constructor
    · rintro ⟨ys, hy, hnil, -, rfl⟩
      exact List.sublist_nil.2 hnil
    · intro h
      obtain rfl := List.sublist_nil.1 h
      exact ⟨[[]], rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩
  | cons x xs ih =>
    constructor
    · rintro ⟨ys, hy, hnil, hstep, rfl⟩
      rcases ys with _ | ⟨y, ys⟩
      · simp at hy
      have hy' : ys.length = xs.length + 1 := by simp at hy; omega
      have h := (ih (ys[0]'(by omega))).1 ⟨ys, hy', hnil, fun t ht => hstep (t + 1) (by simp; omega), rfl⟩
      rcases hstep 0 (by simp) with h0 | h0
      · show y.Sublist (x :: xs)
        rw [show y = x :: ys[0]'(by omega) from h0]
        exact h.cons₂ x
      · show y.Sublist (x :: xs)
        rw [show y = ys[0]'(by omega) from h0]
        exact h.cons x
    · intro hs
      rcases List.sublist_cons_iff.1 hs with h | ⟨w', rfl, h⟩
      · obtain ⟨ys, hy, hnil, hstep, hw⟩ := (ih w).2 h
        refine ⟨ys[0]'(by omega) :: ys, by simp [hy], hnil, fun t ht => ?_, hw⟩
        cases t with
        | zero => exact Or.inr rfl
        | succ t => exact hstep t (by simp at ht; omega)
      · obtain ⟨ys, hy, hnil, hstep, hw⟩ := (ih w').2 h
        refine ⟨(x :: w') :: ys, by simp [hy], hnil, fun t ht => ?_, rfl⟩
        cases t with
        | zero => exact Or.inl (congrArg (x :: ·) hw)
        | succ t => exact hstep t (by simp at ht; omega)

/-- **`subseq`'s step in `rep_foldBy_keep`'s form**: a step that takes row `r`'s element `e` and list `u` to
    `e :: u` and keeps every list `U` holds splits into the rows with an element (`e :: u` or `u`) and the kept
    rows with none. -/
theorem subseq_keep {β : Type _} (E : β → Prop) (U : List β → Prop) (v : List β) (A : Prop)
    (hA : A ↔ (∃ e u, E e ∧ U u ∧ v = e :: u) ∨ U v) :
    A ↔ (∃ e u, E e ∧ U u ∧ (v = e :: u ∨ v = u)) ∨ (True ∧ (¬ ∃ e, E e) ∧ U v) := by
  rw [hA]
  constructor
  · rintro (⟨e, u, he, hu, rfl⟩ | hu)
    · exact Or.inl ⟨e, u, he, hu, Or.inl rfl⟩
    · by_cases hx : ∃ e, E e
      · obtain ⟨e, he⟩ := hx
        exact Or.inl ⟨e, v, he, hu, Or.inr rfl⟩
      · exact Or.inr ⟨trivial, hx, hu⟩
  · rintro (⟨e, u, he, hu, rfl | rfl⟩ | ⟨-, -, hu⟩)
    · exact Or.inl ⟨e, u, he, hu, rfl⟩
    · exact Or.inr hu
    · exact Or.inr hu

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.subseq_chain
