/-
  `join l r` read back, from the content lemmas of `JoinContent`: the class ids `Code.groupIds` answers are
  `groupOf` of the codes, the count column `expand` reads is the number of right rows matching each left
  row, and the pairs are every matching `(i, j)` once, by `i` then `j`.
-/
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.MemberSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-- **`Code.groupIds`' class ids are `groupOf` of the codes**, read at the width of the class count: row
    `i`'s class is the position of its code's first row among the first rows (`groupIds_firsts`), and the
    payload holds all `n` of them. Hypotheses as `groupIds_firsts`. -/
theorem groupIds_groupOf (c : Code)
    (hw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcard : c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) :
    Column.idsCap c.groupIds.1 (Column.idWidthOf (len c.groupIds.2)) c.n.toNat = c.n.toNat ∧
      ∀ i < c.n.toNat, Column.idAt c.groupIds.1 (Column.idWidthOf (len c.groupIds.2)) i =
        Verify.groupOf (Column.idAt c.b c.w) c.n.toNat i := by
  rw [len_eq_ids, groupIds_firsts c hw hs hcard]
  have hW := laneWidth_cases (Column.widthFor ((firstsOf (Column.idAt c.b c.w) c.n.toNat).length - 1))
  simp only [show ∀ x, Column.laneWidth (Column.widthFor (x - 1)) = Column.idWidthOf x from fun _ => rfl] at hW
  have hL : (firstsOf (Column.idAt c.b c.w) c.n.toNat).length ≤ 2 ^ 64 := by
    have := List.length_filter_le (fun i => (List.range i).all fun j =>
      !decide (Column.idAt c.b c.w j = Column.idAt c.b c.w i)) (List.range c.n.toNat)
    rw [List.length_range] at this
    exact Nat.le_trans this (Nat.le_of_lt (usize_lt c.n))
  -- a payload `packIds` of `groupOf g n`, `g` grouping as the codes do, is the claim
  have hP : ∀ {α : Type} [DecidableEq α] (g : Nat → α) (G : ByteArray),
      (∀ i < c.n.toNat, ∀ j < c.n.toNat, (g i = g j ↔ Column.idAt c.b c.w i = Column.idAt c.b c.w j)) →
      G = Column.packIds (Column.idWidthOf (firstsOf g c.n.toNat).length) c.n.toNat (Verify.groupOf g c.n.toNat) →
      Column.idsCap G (Column.idWidthOf (firstsOf (Column.idAt c.b c.w) c.n.toNat).length) c.n.toNat = c.n.toNat ∧
        ∀ i < c.n.toNat, Column.idAt G (Column.idWidthOf (firstsOf (Column.idAt c.b c.w) c.n.toNat).length) i =
          Verify.groupOf (Column.idAt c.b c.w) c.n.toNat i := by
    intro α _ g G hg hG
    obtain ⟨hf, -, hgo⟩ := groups_congr g c.n.toNat hg
    rw [hG, hf]
    refine ⟨idsCap_packIds _ _ hW, fun i hi => ?_⟩
    rw [idAt_packIds hW hi (by rw [hgo i hi]; exact lt_two_pow_idWidthOf hL (groupOf_lt hi))]; exact hgo i hi
  unfold Code.groupIds Code.kind
  split
  · rename_i k hk
    rcases laneKind_some hk with ⟨rfl, e⟩ | ⟨-, e, hq, hki⟩
    · have hm : min c.n.toNat (Scan.Kind.avail .bit c.b) = c.n.toNat := by
        simp only [Scan.Kind.avail, hs, e]; omega
      refine hP _ _ (fun i _ j _ => ?_) (by rw [(groupIds_spec .bit c.n c.b).1, hm])
      simp only [Order.keyAt, Order.rank, Scan.Kind.bitsAt, e, idAt_one]
      cases Column.bitAt c.b i <;> cases Column.bitAt c.b j <;> decide
    · have hk0 : 0 < k.width := by rcases hki with rfl | rfl | rfl | rfl | rfl <;> decide
      have hk8 : k.width ≤ 8 := by omega
      have hav : Scan.Kind.avail k c.b = c.b.size / k.width := by
        rcases hki with rfl | rfl | rfl | rfl | rfl <;> rfl
      have hm : min c.n.toNat (Scan.Kind.avail k c.b) = c.n.toNat := by
        rw [hav, hs, e, show c.n.toNat * (8 * k.width) + 7 = 8 * (c.n.toNat * k.width) + 7 by
          rw [Nat.mul_left_comm], show (8 * (c.n.toNat * k.width) + 7) / 8 = c.n.toNat * k.width by omega,
          Nat.mul_div_cancel _ hk0, Nat.min_self]
      refine hP _ _ (fun i _ j _ => ?_) (by rw [(groupIds_spec k c.n c.b).1, hm])
      rw [keyAt_eq_iff hki, e, idAt_lane _ hk8, idAt_lane _ hk8]
      exact ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.1 h⟩
  · rename_i hk
    have h24 := laneKind_none hk hw
    obtain ⟨hcU, hlt⟩ := hcard (by omega)
    have hd : c.card.toUSize.toNat = c.card := USize.toNat_ofNat_of_lt' hcU
    have hwn : c.w.toUSize.toNat = c.w := lane_toNat (by omega)
    have hb : ∀ a e : Nat, (a == e) = decide (a = e) := fun a e => Bool.eq_iff_iff.2 (by rw [beq_iff_eq, decide_eq_true_iff])
    have hF : Order.idFirsts c.card.toUSize.toNat c.n.toNat c.w.toUSize.toNat c.b =
        firstsOf (Order.idKey c.card.toUSize.toNat c.b c.w.toUSize.toNat) c.n.toNat := by
      simp only [Order.idFirsts, firstsOf, bne, hb]
    refine hP _ _ (fun i hi j hj => ?_) (by simp only [Order.idGroups, hF, hb]; rfl)
    simp only [Order.idKey, hd, hwn, Nat.min_eq_left (Nat.le_of_lt (hlt i hi)),
      Nat.min_eq_left (Nat.le_of_lt (hlt j hj))]

/-- **Position `p` of the lists `g t`, `t < m`, end to end** is entry `p - Σ_{s<t} |g s|` of the `g t` whose
    span covers it. -/
theorem flatMap_get {β : Type} (g : Nat → List β) (m p : Nat)
    (hp : p < ((List.range m).map fun t => (g t).length).sum) :
    ∃ t < m, ((List.range t).map fun s => (g s).length).sum ≤ p ∧
      p < ((List.range t).map fun s => (g s).length).sum + (g t).length ∧
      ((List.range m).flatMap g)[p]? = (g t)[p - ((List.range t).map fun s => (g s).length).sum]? := by
  induction m with
  | zero => simp at hp
  | succ m ih =>
    have hlen : ((List.range m).flatMap g).length = ((List.range m).map fun s => (g s).length).sum := by
      simp [List.length_flatMap]
    rw [List.range_succ, List.map_append] at hp
    simp at hp
    rw [List.range_succ, List.flatMap_append]
    by_cases h : p < ((List.range m).map fun s => (g s).length).sum
    · obtain ⟨t, ht, h1, h2, h3⟩ := ih h
      exact ⟨t, by omega, h1, h2, by rw [List.getElem?_append_left (by rw [hlen]; exact h)]; exact h3⟩
    · refine ⟨m, by omega, by omega, by omega, ?_⟩
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp

#print axioms groupIds_groupOf
#print axioms flatMap_get

end LeetQ.Rel.Alg
