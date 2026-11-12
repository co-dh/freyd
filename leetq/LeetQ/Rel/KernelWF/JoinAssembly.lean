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

/-- A code payload of exactly `⌈n·w/8⌉` bytes at a lane holds its `n` codes, exactly at a byte lane: the size
    hypotheses `find_spec` and `gather_spec` take. -/
theorem code_size {w n s : Nat} (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (hs : s = (n * w + 7) / 8) : w * n ≤ 8 * s ∧ (8 ≤ w → 8 * s = w * n) := by
  subst hs; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **`join`'s count column, read back**: row `i` of `l` is counted once for every row of `r` holding its
    code — `classSizes` of the class `find` names in `r`'s first rows, `0` where `find` misses. Hypotheses:
    both codes at a lane, payloads of exactly their codes, `r`'s codes below its `card` (a `USize`) at
    `2`/`4` bits. -/
theorem join_count (l r : Code)
    (hrw : r.w = 1 ∨ r.w = 2 ∨ r.w = 4 ∨ r.w = 8 ∨ r.w = 16 ∨ r.w = 32 ∨ r.w = 64)
    (hrs : r.b.size = (r.n.toNat * r.w + 7) / 8)
    (hrc : r.w < 8 → r.card < USize.size ∧ ∀ i < r.n.toNat, Column.idAt r.b r.w i < r.card)
    (hlw : l.w = 1 ∨ l.w = 2 ∨ l.w = 4 ∨ l.w = 8 ∨ l.w = 16 ∨ l.w = 32 ∨ l.w = 64)
    (hls : l.b.size = (l.n.toNat * l.w + 7) / 8) {i : Nat} (hi : i < l.n.toNat) :
    (Column.bitsAt (gather 8 (classSizes r.n r.groupIds) ((r.gather r.groupIds.2).find l)) (i * 8) 8).toNat =
      ((List.range r.n.toNat).filter fun j => Column.idAt r.b r.w j == Column.idAt l.b l.w i).length := by
  have hF := groupIds_firsts r hrw hrs hrc
  obtain ⟨hcap, hγ⟩ := groupIds_groupOf r hrw hrs hrc
  have hK : len r.groupIds.2 = (firstsOf (Column.idAt r.b r.w) r.n.toNat).length := by rw [len_eq_ids, hF]
  have hFn : (firstsOf (Column.idAt r.b r.w) r.n.toNat).length ≤ r.n.toNat := by
    have := List.length_filter_le (fun i => (List.range i).all fun j =>
      !decide (Column.idAt r.b r.w j = Column.idAt r.b r.w i)) (List.range r.n.toNat)
    rw [List.length_range] at this; exact this
  have hKU : len r.groupIds.2 < USize.size := by rw [hK]; exact Nat.lt_of_le_of_lt hFn r.n.toNat_lt_size
  have hFi : ∀ j (hj : j < len r.groupIds.2), (Column.bitsAt r.groupIds.2 (j * 8) 8).toNat =
      (firstsOf (Column.idAt r.b r.w) r.n.toNat)[j]'(by rw [← hK]; exact hj) := fun j hj => ids_get hF _
  obtain ⟨hgw, hgn, -, hgc⟩ := gather_spec r r.groupIds.2 hKU hrw (code_size hrw hrs).2
    fun j hj => by rw [hFi j hj]; exact firsts_lt _ _ (List.getElem_mem _)
  have hGs := gather_size r r.groupIds.2 hKU hrw
  obtain ⟨hfl, hfv⟩ := find_spec (r.gather r.groupIds.2) l (by rw [hgw]; exact hrw) hlw
    (by rw [hgw, hgn]; exact (code_size hrw hGs).1) (code_size hlw hls).1
    (by rw [hgw, hgn]; exact (code_size hrw hGs).2) (code_size hlw hls).2
  have hlist : (List.range (r.gather r.groupIds.2).n.toNat).map
      (Column.idAt (r.gather r.groupIds.2).b (r.gather r.groupIds.2).w) =
      (firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w) := by
    rw [hgn, hgw]
    apply List.ext_getElem (by simp [hK])
    intro j h1 _
    simp only [List.getElem_map, List.getElem_range]
    rw [List.length_map, List.length_range] at h1
    rw [hgc j h1, hFi j h1]
  have hv := hfv i hi
  rw [hlist] at hv
  generalize hc : ((firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w)).idxOf
    (Column.idAt l.b l.w i) = c at hv
  have hS := classSizes_ids r.n r.groupIds hKU
  have hsz : len (classSizes r.n r.groupIds) = len r.groupIds.2 := by rw [len_eq_ids, hS]; simp
  have h8 : (Nat.toUSize 8).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  have hgb := (gatherBytes_spec (Nat.toUSize 8) (by rw [h8]; decide) 0 (classSizes r.n r.groupIds)
    ((r.gather r.groupIds.2).find l)).2 i (by have := hfl; simp only [len] at this; omega)
  rw [h8] at hgb
  unfold gather; rw [hgb, hv]
  by_cases hcF : c < (firstsOf (Column.idAt r.b r.w) r.n.toNat).length
  · -- a hit: the rows of class `c`, whose first row holds `l`'s code
    rw [if_pos (show c < (classSizes r.n r.groupIds).size / 8 by rw [show (classSizes r.n r.groupIds).size / 8 = len (classSizes r.n r.groupIds) from rfl, hsz, hK]; exact hcF),
      ids_get hS (by simp [hK, hcF])]
    simp only [List.getElem_map, List.getElem_range, idsW, hcap, List.countP_eq_length_filter, List.filter_map,
      List.length_map]
    have hfc : Column.idAt r.b r.w ((firstsOf (Column.idAt r.b r.w) r.n.toNat)[c]) = Column.idAt l.b l.w i := by
      have hlt : ((firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w)).idxOf
          (Column.idAt l.b l.w i) < ((firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w)).length := by
        rw [hc, List.length_map]; exact hcF
      have e := beq_iff_eq.1 (List.findIdx_getElem (p := fun x => x == Column.idAt l.b l.w i) (w := hlt))
      have hc' : List.findIdx (fun x => x == Column.idAt l.b l.w i)
          ((firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w)) = c := hc
      simp only [hc', List.getElem_map] at e; exact e
    congr 1
    refine List.filter_congr fun j hj => ?_
    have hj' := List.mem_range.1 hj
    simp only [Function.comp_def, hγ j hj']
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, groupOf_eq_iff hj' hcF, hfc]
  · -- a miss: no row of `r` holds `l`'s code
    rw [if_neg (show ¬ c < (classSizes r.n r.groupIds).size / 8 by rw [show (classSizes r.n r.groupIds).size / 8 = len (classSizes r.n r.groupIds) from rfl, hsz, hK]; exact hcF)]
    have hnm : Column.idAt l.b l.w i ∉ (firstsOf (Column.idAt r.b r.w) r.n.toNat).map (Column.idAt r.b r.w) :=
      fun hm => hcF (by rw [← hc, ← List.length_map (f := Column.idAt r.b r.w)]; exact List.idxOf_lt_length_iff.2 hm)
    rw [List.length_eq_zero_iff.2 (List.filter_eq_nil_iff.2 fun j hj => by
      have hj' := List.mem_range.1 hj
      simp only [beq_iff_eq]
      exact fun e => hnm (List.mem_map.2 ⟨_, List.getElem_mem (groupOf_lt hj'), by rw [groupOf_get (g := Column.idAt r.b r.w) hj', e]⟩))]
    simp

#print axioms join_count
#print axioms groupIds_groupOf
#print axioms flatMap_get

end LeetQ.Rel.Alg
