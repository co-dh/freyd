/-
  `setIds vc s`, read back.
-/
import LeetQ.Rel.KernelWF.SegSpec
import LeetQ.Rel.KernelWF.DivSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

-- the long `i` of a column `seg`, the key `gradeBy` sorts by first
set_option hygiene false in
local notation "S(" i ")" => UInt64.toNat (Column.bitsAt seg (i * 8) 8)

/-- Below the top bit, setting it adds it. -/
theorem xor_top {x : Nat} (hx : x < 2 ^ 63) : x ^^^ 2 ^ 63 = 2 ^ 63 + x := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy i 63 with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [Nat.ne_of_gt h]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hx]; simp
  · have h1 : x < 2 ^ i := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h))
    have h2 : 2 ^ 63 + x < 2 ^ i :=
      Nat.lt_of_lt_of_le (show 2 ^ 63 + x < 2 ^ 64 by omega) (Nat.pow_le_pow_right (by decide) h)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]; simp [Nat.ne_of_lt h]

/-- A non-negative long's `i64` sort key is the long shifted up by `2⁶³`, so the keys order as the longs. -/
theorem rank_i64_toNat {x : UInt64} (hx : x.toNat < 2 ^ 63) : (Order.rank .i64 x).toNat = 2 ^ 63 + x.toNat := by
  show (x ^^^ 0x8000000000000000).toNat = _
  rw [UInt64.toNat_xor]; exact xor_top hx

/-- **`gradeBy` on a long column `seg` then a code `vc` sorts lexicographically**: a permutation of the rows,
    ascending in `seg`, and within one `seg` value ascending in a key `κ` that agrees exactly where `vc`'s codes
    do. Hypotheses: `vc` well formed (lane, exact payload size), `seg` exactly `vc.n` longs, each below `2⁶³`. -/
theorem gradeBy_lex (seg : ByteArray) (vc : Code)
    (hw : vc.w = 1 ∨ vc.w = 2 ∨ vc.w = 4 ∨ vc.w = 8 ∨ vc.w = 16 ∨ vc.w = 32 ∨ vc.w = 64)
    (hs : vc.b.size = (vc.n.toNat * vc.w + 7) / 8) (hn : seg.size = 8 * vc.n.toNat)
    (h63 : ∀ i < vc.n.toNat, S(i) < 2 ^ 63) :
    (ids (gradeBy vc.n #[Code.ofLongs seg, vc])).Perm (List.range vc.n.toNat) ∧ ∃ κ : Nat → Nat,
      (∀ i j, i < vc.n.toNat → j < vc.n.toNat → (κ i = κ j ↔ Column.idAt vc.b vc.w i = Column.idAt vc.b vc.w j)) ∧
      (ids (gradeBy vc.n #[Code.ofLongs seg, vc])).Pairwise fun i j => S(i) < S(j) ∨ (S(i) = S(j) ∧ κ i ≤ κ j) := by
  have lane : ∀ (b : ByteArray) a, Column.idAt b 64 a = (Column.bitsAt b (a * 8) 8).toNat :=
    fun b a => idAt_lane b (c := 8) (by decide) a
  have hid : ids (tilLongs vc.n) = List.range vc.n.toNat := by
    rw [← tilLongs_spec vc.n]; simp only [ids, elemsW, List.map_map, Function.comp_def]
  have htl : len (tilLongs vc.n) = vc.n.toNat := by rw [len_eq_ids, hid, List.length_range]
  have hl : len (tilLongs vc.n) < USize.size := by rw [htl]; exact vc.n.toNat_lt_size
  have hcb : 8 ≤ vc.w → 8 * vc.b.size = vc.w * vc.n.toNat := fun h8 => by
    rcases hw with h | h | h | h | h | h | h <;> rw [h] at hs ⊢ <;> omega
  rw [show gradeBy vc.n #[Code.ofLongs seg, vc] = gather 8 (gather 8 (tilLongs vc.n) (vc.gather (tilLongs vc.n)).grade)
    ((Code.ofLongs seg).gather (gather 8 (tilLongs vc.n) (vc.gather (tilLongs vc.n)).grade)).grade from rfl]
  -- the code grade `g` of `vc` (at `til n`, so its rows are `vc`'s)
  obtain ⟨hGw, hGn, -, hGid⟩ := gather_spec vc (tilLongs vc.n) hl hw hcb
    fun j hj => by rw [tilLongs_get (by rw [htl] at hj; exact hj)]; rw [htl] at hj; exact hj
  have hGs := gather_size vc (tilLongs vc.n) hl hw
  generalize hG : vc.gather (tilLongs vc.n) = G at hGw hGn hGid hGs ⊢
  have hw' := hw
  rw [← hGw] at hw'
  rw [← hGn, ← hGw] at hGs
  obtain ⟨hgp, κ, hκ, hsrt⟩ := grade_code G hw' hGs
  rw [hGn, htl] at hgp hκ
  rw [hGw] at hκ
  have hgm : ∀ t ∈ ids G.grade, t < vc.n.toNat := fun t ht => List.mem_range.1 (hgp.mem_iff.1 ht)
  have hP : ids (gather 8 (tilLongs vc.n) G.grade) = ids G.grade := by
    rw [ids_gather8 (fun t ht => by rw [htl]; exact hgm t ht), hid]
    exact (List.map_congr_left fun t ht => by simp [hgm t ht]).trans (List.map_id _)
  generalize hPd : gather 8 (tilLongs vc.n) G.grade = P at hP ⊢
  rw [← hP] at hgp hsrt
  have hPl : (ids P).length = vc.n.toNat := by rw [hgp.length_eq, List.length_range]
  have hlP : len P = vc.n.toNat := by rw [len_eq_ids, hPl]
  have hPv : ∀ a (ha : a < vc.n.toNat), (ids P)[a]'(by rw [hPl]; exact ha) < vc.n.toNat := fun a ha =>
    List.mem_range.1 (hgp.mem_iff.1 (List.getElem_mem _))
  -- the seg grade of the long column `seg@P`
  have hsl : len seg = vc.n.toNat := by show seg.size / 8 = _; omega
  have hsl' : len seg < USize.size := by rw [hsl]; exact vc.n.toNat_lt_size
  have hC : (Code.ofLongs seg).w = 64 ∧ (Code.ofLongs seg).n.toNat = len seg ∧ (Code.ofLongs seg).b = seg := by
    unfold Code.ofLongs longCount; simp only [need, dif_pos hsl']; exact ⟨trivial, USize.toNat_ofNat_of_lt' hsl', trivial⟩
  have hCw : (Code.ofLongs seg).w = 1 ∨ (Code.ofLongs seg).w = 2 ∨ (Code.ofLongs seg).w = 4 ∨
      (Code.ofLongs seg).w = 8 ∨ (Code.ofLongs seg).w = 16 ∨ (Code.ofLongs seg).w = 32 ∨
      (Code.ofLongs seg).w = 64 := by rw [hC.1]; simp
  have hlP' : len P < USize.size := by rw [hlP]; exact vc.n.toNat_lt_size
  obtain ⟨hHw, hHn, -, hHid⟩ := gather_spec (Code.ofLongs seg) P hlP' hCw
    (fun _ => by rw [hC.1, hC.2.1, hC.2.2]; show 8 * seg.size = 64 * (seg.size / 8); omega)
    fun j hj => by
      rw [hlP] at hj; rw [hC.2.1, hsl, ← ids_getElem (by rw [hPl]; exact hj)]; exact hPv j hj
  have hHs := gather_size (Code.ofLongs seg) P hlP' hCw
  rw [hC.1, hC.2.2] at hHid
  rw [hC.1] at hHs hHw
  generalize hH : (Code.ofLongs seg).gather P = H at hHw hHn hHid hHs ⊢
  have hgr : H.grade = Order.grade .i64 false H.n H.b := by
    unfold Code.grade Code.kind; rw [hHw]; rfl
  obtain ⟨hgp2, hgs2⟩ := grade_spec .i64 false H.n H.b
  rw [← hgr] at hgp2 hgs2
  have hm : min H.n.toNat (Scan.Kind.i64.avail H.b) = vc.n.toNat := by
    show min _ (H.b.size / 8) = _; rw [hHs, hHn, hlP]; omega
  rw [hm] at hgp2
  have hgm2 : ∀ t ∈ ids H.grade, t < vc.n.toNat := fun t ht => List.mem_range.1 (hgp2.mem_iff.1 ht)
  have key : ∀ a (ha : a < vc.n.toNat),
      (Order.keyAt .i64 H.b a).toNat = 2 ^ 63 + S((ids P)[a]'(by rw [hPl]; exact ha)) := fun a ha => by
    have e1 : Order.keyAt .i64 H.b a = Order.rank .i64 (Column.bitsAt H.b (a * 8) 8) := rfl
    have e2 : (Column.bitsAt H.b (a * 8) 8).toNat = S((ids P)[a]'(by rw [hPl]; exact ha)) := by
      rw [← lane H.b a, hHid a (by rw [hlP]; exact ha), lane seg, ids_getElem]
    rw [e1, rank_i64_toNat (by rw [e2]; exact h63 _ (hPv a ha)), e2]
  refine ⟨(gather_perm (by rw [hlP]; exact hgp2)).trans hgp, κ, fun i j hi hj => ?_, ?_⟩
  · rw [hκ i j hi hj, hGid i (by rw [htl]; exact hi), hGid j (by rw [htl]; exact hj), tilLongs_get hi,
      tilLongs_get hj]
  · rw [ids_gather8 (fun t ht => by rw [hlP]; exact hgm2 t ht)]
    refine List.pairwise_map.2 (hgs2.imp_of_mem fun {a b} ha hb ⟨h1, h2⟩ => ?_)
    have ha' := hgm2 a ha
    have hb' := hgm2 b hb
    simp only [keyOrd, Bool.false_eq_true, ↓reduceIte] at h1 h2
    have h1' := UInt64.le_iff_toNat_le.1 h1
    rw [key a ha', key b hb'] at h1'
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show a < (ids P).length by rw [hPl]; exact ha'),
      List.getElem?_eq_getElem (show b < (ids P).length by rw [hPl]; exact hb'), Option.getD_some]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_add_le_add_left h1') with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      have hab := h2 (UInt64.le_iff_toNat_le.2 (by rw [key a ha', key b hb', heq]; exact Nat.le_refl _))
      exact List.pairwise_iff_getElem.1 hsrt a b (by rw [hPl]; exact ha') (by rw [hPl]; exact hb') hab

#print axioms gradeBy_lex

end LeetQ.Rel.Alg
