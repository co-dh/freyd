/-
  `mergeOn` read back. `mergeOn q P` runs rounds of `iter` on states `((x, y), acc)` per key: with both arrays
  non-empty the head `a` of `x` goes to `acc` when `(a, b)` passes the test, else the head `b` of `y`; with either
  empty the state ends as `acc ++ x ++ y`. Each round shortens `x` or `y` by one and no array of `P` is longer
  than its side's payload, so the fuel (both payloads plus one) always suffices: the result is core's
  `List.merge` of each pair of `P`, at the test.
-/
import LeetQ.Rel.RepPerm
import LeetQ.Rel.RepLoop

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN Prim

/-- **The states of a merge, in `Set`**: `st i k` holds the states key `k` reaches after `i` rounds, `out i k` the
    arrays flushed before round `i`. A round takes `((a :: x, b :: y), acc)` to `((x, b :: y), acc ++ [a])` when
    `le a b`, else to `((a :: x, y), acc ++ [b])` (`hst`), and flushes a state with an empty side as
    `acc ++ x ++ y` (`hout`); the seeds `st 0` are the pairs of `seed` with `acc = []`. At a stop `j` past every
    seed's total length (`N < j`), or with no state left, `out j` is exactly the merges of the seeds. -/
theorem merge_chain {K B : Type} (le : B → B → Bool) (seed : K → List B × List B → Prop)
    (st : Nat → K → (List B × List B) × List B → Prop) (out : Nat → K → List B → Prop) (M : Nat)
    (h0 : ∀ k x y acc, st 0 k ((x, y), acc) ↔ seed k (x, y) ∧ acc = [])
    (hst : ∀ i, i < M → ∀ k s', st (i + 1) k s' ↔ ∃ a x b y acc, st i k ((a :: x, b :: y), acc) ∧
      (le a b = true ∧ s' = ((x, b :: y), acc ++ [a]) ∨ le a b = false ∧ s' = ((a :: x, y), acc ++ [b])))
    (ho0 : ∀ k z, ¬ out 0 k z)
    (hout : ∀ i, i < M → ∀ k z, out (i + 1) k z ↔
      out i k z ∨ ∃ x y acc, st i k ((x, y), acc) ∧ (x = [] ∨ y = []) ∧ z = acc ++ x ++ y)
    (N j : Nat) (hjM : j ≤ M) (hN : ∀ k s, seed k s → s.1.length + s.2.length ≤ N)
    (hj : N < j ∨ ∀ k s, ¬ st j k s) :
    ∀ k z, out j k z ↔ ∃ xs ys, seed k (xs, ys) ∧ z = List.merge xs ys le := by
  -- a flushed state: one side empty, so `x ++ y` is their merge
  have flush : ∀ x y : List B, (x = [] ∨ y = []) → x ++ y = List.merge x y le := by
    rintro x y (rfl | rfl)
    · simp
    · simp
  -- every state after `i` rounds: `acc` then the merge of its sides is the merge of its seed, `i` cells moved
  have sound : ∀ i, i ≤ M → ∀ k x y acc, st i k ((x, y), acc) → ∃ xs ys, seed k (xs, ys) ∧
      acc ++ List.merge x y le = List.merge xs ys le ∧ x.length + y.length + i = xs.length + ys.length := by
    intro i
    induction i with
    | zero =>
      intro _ k x y acc h
      obtain ⟨hs, rfl⟩ := (h0 k x y acc).1 h
      exact ⟨x, y, hs, by simp, by simp⟩
    | succ i ih =>
      intro hi k x y acc h
      obtain ⟨a, x0, b, y0, acc0, hs, hc⟩ := (hst i (by omega) k _).1 h
      obtain ⟨xs, ys, hseed, he, hl⟩ := ih (by omega) k _ _ _ hs
      refine ⟨xs, ys, hseed, ?_⟩
      rcases hc with ⟨hab, e⟩ | ⟨hab, e⟩
      · simp only [Prod.mk.injEq] at e
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
        refine ⟨?_, ?_⟩
        · rw [← he, List.cons_merge_cons, if_pos hab]; simp
        · simp at hl ⊢; omega
      · simp only [Prod.mk.injEq] at e
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
        refine ⟨?_, ?_⟩
        · rw [← he, List.cons_merge_cons, if_neg (by simp [hab])]; simp
        · simp at hl ⊢; omega
  -- every seed has, after `i` rounds, its merge flushed or a state carrying it
  have complete : ∀ i, i ≤ M → ∀ k xs ys, seed k (xs, ys) → out i k (List.merge xs ys le) ∨
      ∃ x y acc, st i k ((x, y), acc) ∧ acc ++ List.merge x y le = List.merge xs ys le := by
    intro i
    induction i with
    | zero => intro _ k xs ys hs; exact Or.inr ⟨xs, ys, [], (h0 k xs ys []).2 ⟨hs, rfl⟩, by simp⟩
    | succ i ih =>
      intro hi k xs ys hs
      rcases ih (by omega) k xs ys hs with ho | ⟨x, y, acc, hst', he⟩
      · exact Or.inl ((hout i (by omega) k _).2 (Or.inl ho))
      · match x, y, hst', he with
        | [], y, hst', he =>
          exact Or.inl ((hout i (by omega) k _).2 (Or.inr ⟨[], y, acc, hst', Or.inl rfl, by rw [← he]; simp⟩))
        | a :: x, [], hst', he =>
          exact Or.inl ((hout i (by omega) k _).2 (Or.inr ⟨a :: x, [], acc, hst', Or.inr rfl, by rw [← he]; simp⟩))
        | a :: x, b :: y, hst', he =>
          refine Or.inr ?_
          cases hab : le a b
          · refine ⟨a :: x, y, acc ++ [b], (hst i (by omega) k _).2 ⟨a, x, b, y, acc, hst', Or.inr ⟨hab, rfl⟩⟩, ?_⟩
            rw [← he, List.cons_merge_cons, if_neg (by simp [hab])]; simp
          · refine ⟨x, b :: y, acc ++ [a], (hst i (by omega) k _).2 ⟨a, x, b, y, acc, hst', Or.inl ⟨hab, rfl⟩⟩, ?_⟩
            rw [← he, List.cons_merge_cons, if_pos hab]; simp
  have osound : ∀ i, i ≤ M → ∀ k z, out i k z → ∃ xs ys, seed k (xs, ys) ∧ z = List.merge xs ys le := by
    intro i
    induction i with
    | zero => intro _ k z h; exact absurd h (ho0 k z)
    | succ i ih =>
      intro hi k z h
      rcases (hout i (by omega) k z).1 h with h | ⟨x, y, acc, hs, he, rfl⟩
      · exact ih (by omega) k z h
      · obtain ⟨xs, ys, hseed, hm, -⟩ := sound i (by omega) k x y acc hs
        exact ⟨xs, ys, hseed, by rw [← hm, List.append_assoc, flush x y he]⟩
  intro k z
  refine ⟨osound j hjM k z, ?_⟩
  rintro ⟨xs, ys, hs, rfl⟩
  rcases complete j hjM k xs ys hs with ho | ⟨x, y, acc, hst', -⟩
  · exact ho
  · exfalso
    rcases hj with hj | hj
    · obtain ⟨xs', ys', hs', -, hl⟩ := sound j hjM k x y acc hst'
      have := hN k _ hs'
      simp at this
      omega
    · exact hj k _ hst'

#print axioms merge_chain

end LeetQ.Rel.Rep
