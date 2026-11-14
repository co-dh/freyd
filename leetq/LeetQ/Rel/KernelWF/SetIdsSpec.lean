/-
  `setIds vc s`, read back.
-/
import LeetQ.Rel.KernelWF.SegSpec
import LeetQ.Rel.KernelWF.DivSpec
import LeetQ.Rel.KernelWF.CodesRec

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

-- the long `j` of the offsets `o`, and the slice `groupOf o n` puts row `i` in
set_option hygiene false in
local notation "O(" j ")" => UInt64.toNat (Column.bitsAt o (j * 8) 8)
set_option hygiene false in
local notation "G(" i ")" => UInt64.toNat (Column.bitsAt (groupOf o n) (i * 8) 8)

/-- A word whose signed reading is a natural number `k` is `k`. -/
theorem toNat_of_toInt64 {x : UInt64} {k : Nat} (h : x.toInt64.toInt = (k : Int)) : x.toNat = k := by
  have e : x.toInt64.toInt = x.toBitVec.toInt := rfl
  have e2 : x.toNat = x.toBitVec.toNat := rfl
  have hl := x.toBitVec.isLt
  rw [e, BitVec.toInt_eq_toNat_cond] at h
  split at h <;> omega

/-- A long below `2⁶³` keyed as `bin` keys a signed 8-byte element: shifted up by `2⁶³`. -/
theorem ordKey_long {b : ByteArray} {i : Nat} (h : (Column.bitsAt b (i * 8) 8).toNat < 2 ^ 63) :
    (ordKey 8 false true (Column.bitsAt b (i * 8) 8)).toNat = 2 ^ 63 + (Column.bitsAt b (i * 8) 8).toNat :=
  (congrArg UInt64.toNat (ordKey_keyAt (k := .i64) (s := true) (Or.inr ⟨Or.inr (Or.inr rfl), rfl⟩) b i)).trans
    (rank_i64_toNat h)

/-- **`groupOf o n` puts each row in its slice**: over `m + 1` ascending offsets from `0` to `n`, row `i < n`
    goes to the slice `j < m` with `o[j] ≤ i < o[j+1]`, one long per row. Hypotheses: true size bounds and the
    shape of the offsets (`0` first, ascending, `n` last). -/
theorem groupOf_spec (o : ByteArray) (n : USize) {m : Nat} (ho : o.size = 8 * (m + 1)) (hn : n.toNat < 2 ^ 63)
    (hm : m + 1 < 2 ^ 63) (h0 : O(0) = 0) (hasc : ∀ j < m, O(j) ≤ O(j + 1)) (hlast : O(m) = n.toNat) :
    (groupOf o n).size = 8 * n.toNat ∧ ∀ i < n.toNat, G(i) < m ∧ O(G(i)) ≤ i ∧ i < O(G(i) + 1) := by
  have h8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hid : ids (tilLongs n) = List.range n.toNat := by
    rw [← tilLongs_spec n]; simp only [ids, elemsW, List.map_map, Function.comp_def]
  have htl : (tilLongs n).size / 8 = n.toNat := by
    show len (tilLongs n) = _; rw [len_eq_ids, hid, List.length_range]
  have hmono : ∀ a b, a ≤ b → b ≤ m → O(a) ≤ O(b) := by
    intro a b hab hb
    induction b with
    | zero => cases Nat.le_zero.1 hab; exact Nat.le_refl _
    | succ b ih =>
      rcases Nat.lt_or_eq_of_le hab with h | rfl
      · exact Nat.le_trans (ih (by omega) (by omega)) (hasc b (by omega))
      · exact Nat.le_refl _
  have hO : ∀ j ≤ m, O(j) < 2 ^ 63 := fun j hj => by have := hmono j m hj (Nat.le_refl _); omega
  have hsize : (groupOf o n).size = 8 * n.toNat := by
    simp only [groupOf, binBytes, h8]
    rw [(foldl_pushBits _ 8 (by decide) _ _).1, List.length_range, htl]; simp
  refine ⟨hsize, fun i hi => ?_⟩
  have hb := binBytes_last 8 false true o (tilLongs n)
  rw [h8] at hb
  rw [show o.size / 8 = m + 1 by omega] at hb
  obtain ⟨r, hr, hv, hlo, hhi⟩ := hb (by omega)
    (fun a b hab hb' => UInt64.le_iff_toNat_le.2 (by
      rw [ordKey_long (hO a (by omega)), ordKey_long (hO b (by omega))]
      have := hmono a b hab (by omega); omega)) i (by rw [htl]; exact hi)
  have hk : (Column.bitsAt (tilLongs n) (i * 8) 8).toNat = i := tilLongs_get hi
  have hkey : (ordKey 8 false true (Column.bitsAt (tilLongs n) (i * 8) 8)).toNat = 2 ^ 63 + i := by
    rw [ordKey_long (by rw [hk]; omega), hk]
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · have := UInt64.lt_iff_toNat_lt.1 (hhi 0 (by omega) (by omega))
      rw [hkey, ordKey_long (hO 0 (by omega)), h0] at this; omega
    · exact h
  have hrm : r ≤ m := by
    rcases Nat.lt_or_eq_of_le hr with h | h
    · omega
    · have := UInt64.le_iff_toNat_le.1 (hlo m (by omega))
      rw [hkey, ordKey_long (hO m (Nat.le_refl _)), hlast] at this; omega
  have hG : G(i) = r - 1 := toNat_of_toInt64 (by unfold groupOf; rw [Nat.mul_comm i 8, hv]; omega)
  rw [hG]
  refine ⟨by omega, ?_, ?_⟩
  · have := UInt64.le_iff_toNat_le.1 (hlo (r - 1) (by omega))
    rw [hkey, ordKey_long (hO _ (by omega))] at this; omega
  · have := UInt64.lt_iff_toNat_lt.1 (hhi (r - 1 + 1) (by omega) (by omega))
    rw [hkey, ordKey_long (hO _ (by omega))] at this; omega

/-- **Below a first row `b`, the first rows are those numbered below `b`'s group**: the first rows ascend, and
    `b`'s group is numbered by `b`'s own place among them. -/
theorem firsts_lt_iff {α : Type} [DecidableEq α] {g : Nat → α} {m b : Nat} (hb : b ∈ firstsOf g m) {r : Nat}
    (hr : r < (firstsOf g m).length) : (firstsOf g m)[r] < b ↔ r < Verify.groupOf g m b := by
  have hbm := firsts_lt g m hb
  obtain ⟨k', hk', e⟩ := List.getElem_of_mem hb
  have hkk : Verify.groupOf g m b = k' :=
    firsts_inj (groupOf_lt (g := g) hbm) hk' (by rw [groupOf_get (g := g) hbm, e])
  have hF : (firstsOf g m).Pairwise (· < ·) := by unfold firstsOf; exact (pairwise_range m).filter _
  rw [hkk, ← e]
  constructor
  · intro h
    rcases Nat.lt_or_ge r k' with h' | h'
    · exact h'
    · rcases Nat.lt_or_eq_of_le h' with h'' | rfl
      · exact absurd (List.pairwise_iff_getElem.1 hF k' r hk' hr h'') (by omega)
      · exact absurd h (Nat.lt_irrefl _)
  · exact List.pairwise_iff_getElem.1 hF r k' hr hk'

/-- **Two ascending lists with one set of members are one list.** -/
theorem eq_of_lt_mem : ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 (by simp)) with e | ha
      · exact e
      · rcases List.mem_cons.1 ((h b).2 (by simp)) with e | hb
        · exact e.symm
        · have := List.rel_of_pairwise_cons h₂ ha; have := List.rel_of_pairwise_cons h₁ hb; omega
    subst hab
    have h₁' := List.pairwise_cons.1 h₁
    have h₂' := List.pairwise_cons.1 h₂
    rw [eq_of_lt_mem h₁'.2 h₂'.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩]
    · have := h₁'.1 x hx
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · omega
      · exact e
    · have := h₂'.1 x hx
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · omega
      · exact e

/-- **`idsBy` read back by position**: its first rows are `firstsOf`, and row `i`'s id, read at the width the
    first-row count gives, is `groupOf`. -/
theorem idsBy_read {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] {m : Nat} (hm : m < 2 ^ 64) (key : Nat → α) :
    ids (Order.idsBy m key).2 = firstsOf key m ∧ (∀ i < m,
      Column.idAt (Order.idsBy m key).1 (Column.idWidthOf ((Order.idsBy m key).2.size / 8)) i =
        Verify.groupOf key m i) ∧
      Column.idsCap (Order.idsBy m key).1 (Column.idWidthOf ((Order.idsBy m key).2.size / 8)) m = m := by
  obtain ⟨h1, h2⟩ := idsBy_spec m key
  have hb : ∀ a b : α, (a == b) = decide (a = b) := fun a b => Bool.eq_iff_iff.2 (by
    rw [beq_iff_eq, decide_eq_true_iff])
  have hf : Order.firstsBy m key = firstsOf key m := by unfold Order.firstsBy firstsOf; simp only [bne, hb]
  refine ⟨?_, fun i hi => ?_, ?_⟩
  · show ids (Order.indices (Order.firstsBy m key)) = _
    rw [hf, ids_indices _ fun i hi => Nat.lt_trans (firsts_lt key m hi) hm]
  · rw [h1, h2, Nat.mul_div_cancel_left _ (by decide)]
    exact idAt_packIds (by unfold Column.idWidthOf; exact laneWidth_cases _) hi
      (lt_idWidthOf (groupOf_lt hi) (Nat.le_of_lt (Nat.lt_of_le_of_lt (firstsOf_length_le key m) hm)))
  · rw [h1, h2, Nat.mul_div_cancel_left _ (by decide)]
    exact idsCap_packIds m _ (by unfold Column.idWidthOf; exact laneWidth_cases _)

-- the (slice, code) key of row `t`: the long `t` of `A`, the code `t` of `B`
set_option hygiene false in
local notation "PK(" A ", " B ")" => fun t => (UInt64.toNat (Column.bitsAt A (t * 8) 8), Column.idAt (Code.b B) (Code.w B) t)

/-- **`setIds`' pair grouping read back**: on a long column `A` and a well-formed code `B` of `n` rows, the pair
    kernel `setIds` picks by `B`'s lane answers the first rows of the pairs `(A[t], B[t])` and, at each row, the
    number of its pair among them (`groupOf`). Hypotheses: `B` well formed (lane, exact payload size), `A` and `B`
    exactly `n` rows. -/
theorem pairIds_read (A : ByteArray) (B : Code) (n : USize)
    (hw : B.w = 1 ∨ B.w = 2 ∨ B.w = 4 ∨ B.w = 8 ∨ B.w = 16 ∨ B.w = 32 ∨ B.w = 64)
    (hs : B.b.size = (B.n.toNat * B.w + 7) / 8) (hBn : B.n.toNat = n.toNat) (hA : A.size = 8 * n.toNat)
    (r : ByteArray × ByteArray) (hr : r = match B.kind with
      | some k => Order.groupIdsPair .i64 k n A B.b
      | none => Order.groupIdsPairIds 64 B.w.toUSize n A B.b) :
    ids r.2 = firstsOf PK(A, B) n.toNat ∧ (∀ t < n.toNat,
      Column.idAt r.1 (Column.idWidthOf (r.2.size / 8)) t = Verify.groupOf PK(A, B) n.toNat t) ∧
      Column.idsCap r.1 (Column.idWidthOf (r.2.size / 8)) n.toNat = n.toNat := by
  have lane : ∀ (b : ByteArray) a, Column.idAt b 64 a = (Column.bitsAt b (a * 8) 8).toNat :=
    fun b a => idAt_lane b (c := 8) (by decide) a
  suffices h : ∃ key : Nat → UInt64 × UInt64, r = Order.idsBy n.toNat key ∧
      ∀ i < n.toNat, ∀ j < n.toNat, (key i = key j ↔ PK(A, B) i = PK(A, B) j) by
    obtain ⟨key, rfl, hk⟩ := h
    obtain ⟨hf, -, hg⟩ := groups_congr key n.toNat hk
    obtain ⟨h1, h2, h3⟩ := idsBy_read (usize_lt n) key
    exact ⟨h1.trans hf, fun t ht => (h2 t ht).trans (hg t ht), h3⟩
  have hAv : Scan.Kind.i64.avail A = n.toNat := by show A.size / 8 = _; omega
  rcases hk : B.kind with _ | k
  · rw [hk] at hr
    have h8 : 8 * (8 : USize).toNat = 64 := by
      rw [show (8 : USize).toNat = 8 from USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    have h64 : (64 : USize).toNat = 64 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have hwB : B.w.toUSize.toNat = B.w := lane_toNat (by omega)
    have capA : Column.idsCap A 64 n.toNat = n.toNat := idsCap_full (by decide) (by rw [hA]; omega)
    have capB : Column.idsCap B.b B.w n.toNat = n.toNat := idsCap_full (by omega) (by
      rw [hs, hBn]; rcases hw with h | h | h | h | h | h | h <;> rw [h] <;> omega)
    have hM : min n.toNat (min (Scan.Kind.i64.avail (idsOperand 8 64 A n))
        (Scan.Kind.i64.avail (idsOperand 8 B.w.toUSize B.b n))) = n.toNat := by
      rw [idsOperand, idsOperand, h8, (keyAt_packIds64 _ _).1, (keyAt_packIds64 _ _).1, h64, hwB, capA, capB]
      simp
    refine ⟨fun i => (Order.keyAt .i64 (idsOperand 8 64 A n) i, Order.keyAt .i64 (idsOperand 8 B.w.toUSize B.b n) i),
      ?_, fun i hi j hj => ?_⟩
    · rw [hr]; simp only; unfold Order.groupIdsPairIds Order.groupIdsPair; rw [hM]
    · have hc : ∀ x < n.toNat, x < min n.toNat (min (Column.idsCap A (64 : USize).toNat n.toNat)
          (Column.idsCap B.b B.w.toUSize.toNat n.toNat)) := fun x hx => by rw [h64, hwB, capA, capB]; simpa using hx
      have e := groupIdsPairIds_iff 64 B.w.toUSize n A B.b (hc i hi) (hc j hj)
      unfold Order.groupIdsPairIds Order.groupIdsPair at e
      rw [hM, (idsBy_read (usize_lt n) _).2.1 i hi, (idsBy_read (usize_lt n) _).2.1 j hj, groupOf_iff hi hj, h64, hwB,
        lane A i, lane A j] at e
      refine e.trans ?_
      simp only [Prod.mk.injEq]
  · rw [hk] at hr
    have hM : min n.toNat (min (Scan.Kind.i64.avail A) (k.avail B.b)) = n.toNat := by
      have := avail_lane hk hs; rw [hAv]; omega
    refine ⟨fun i => (Order.keyAt .i64 A i, Order.keyAt k B.b i), ?_, fun i hi j hj => ?_⟩
    · rw [hr]; simp only; unfold Order.groupIdsPair; rw [hM]
    · simp only [Prod.mk.injEq]
      exact and_congr ((keyAt_eq_iff (k := .i64) (by simp) A i j).trans UInt64.toNat_inj.symm)
        (keyAt_iff_idAt hk B.b i j)

/-- **`groupLongs` of `setIds`' pair grouping** widens it to one long per row: row `t`'s pair number. Hypotheses
    as `pairIds_read`. -/
theorem groupLongs_read (A : ByteArray) (B : Code) (n : USize)
    (hw : B.w = 1 ∨ B.w = 2 ∨ B.w = 4 ∨ B.w = 8 ∨ B.w = 16 ∨ B.w = 32 ∨ B.w = 64)
    (hs : B.b.size = (B.n.toNat * B.w + 7) / 8) (hBn : B.n.toNat = n.toNat) (hA : A.size = 8 * n.toNat)
    (r : ByteArray × ByteArray) (hr : r = match B.kind with
      | some k => Order.groupIdsPair .i64 k n A B.b
      | none => Order.groupIdsPairIds 64 B.w.toUSize n A B.b) :
    ids (groupLongs n r) = (List.range n.toNat).map (Verify.groupOf PK(A, B) n.toNat) := by
  obtain ⟨-, hg, hcap⟩ := pairIds_read A B n hw hs hBn hA r hr
  have hW : Column.idWidthOf (r.2.size / 8) ≤ 64 := by
    unfold Column.idWidthOf
    rcases laneWidth_cases (Column.widthFor (r.2.size / 8 - 1)) with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  show ids (Order.idLongs n (Column.idWidthOf (r.2.size / 8)).toUSize r.1) = _
  rw [ids_idLongs, lane_toNat hW, hcap]
  exact List.map_congr_left fun t ht => hg t (List.mem_range.1 ht)

/-- **`concatBytes #[a, one v]` read back**: `a`'s `m` longs, then `v`. -/
theorem concat_one (a : ByteArray) (v : UInt64) {m : Nat} (ha : a.size = 8 * m) :
    (concatBytes #[a, one v]).size = 8 * (m + 1) ∧
      (∀ j < m, Column.bitsAt (concatBytes #[a, one v]) (j * 8) 8 = Column.bitsAt a (j * 8) 8) ∧
      Column.bitsAt (concatBytes #[a, one v]) (m * 8) 8 = v := by
  have h1 : (one v).size = 8 := by simp [one, Column.pushBits_size]
  have e : concatBytes #[a, one v] = (ByteArray.empty ++ a) ++ one v := rfl
  have hX : (ByteArray.empty ++ a).size = 8 * m := by rw [ByteArray.size_append]; simp [ha]
  rw [e]
  refine ⟨by rw [ByteArray.size_append, hX, h1]; omega, fun j hj => bitsAt_shift _ _ _ _ _ fun k hk => ?_, ?_⟩
  · rw [ba_append_left _ _ _ (by rw [hX]; omega), ba_append_right' _ _ _ (by simp)]; simp
  · refine (bitsAt_shift _ _ _ _ _ fun k hk => ?_).trans (bitsAt_one v)
    rw [show m * 8 + k = (ByteArray.empty ++ a).size + k by rw [hX]; omega, ba_append_right, Nat.zero_add]

-- the `j`-th representative's code along the sorted rows `L`, over the slice `j` of the first rows
set_option hygiene false in
local notation "SEQ(" φ ", " j ")" =>
  (List.range (off (j + 1) - off j)).map (fun x => φ (L ((firstsOf K N).getD (off j + x) 0)))

/-- **Sorted slices compare as sets**: rows `[O j, O (j+1))` form slice `j` (`G`), `L` lists the rows slice by
    slice (`G (L t) = G t`), within a slice ascending in a key `κ` that agrees exactly where the codes `c` do.
    The first rows `F` of the pairs `K t = (G t, c (L t))`, cut at `off j` (the pair number at `O j`), give each
    slice its representatives' codes; two slices have equal representatives exactly when they hold one set of
    codes. Hypotheses: the starts ascend to `N`; `G`, `L`, `κ` as `groupOf_spec`/`gradeBy_lex` give them. -/
theorem slices_core {N m : Nat} {O G L c κ : Nat → Nat} {K : Nat → Nat × Nat} {off : Nat → Nat}
    (hO : ∀ a b, a ≤ b → b ≤ m → O a ≤ O b) (hOm : O m = N)
    (hG : ∀ i < N, G i < m ∧ O (G i) ≤ i ∧ i < O (G i + 1))
    (hL : ∀ t < N, L t < N) (hLs : ∀ i < N, ∃ t < N, L t = i) (hGL : ∀ t < N, G (L t) = G t)
    (hκ : ∀ i j, i < N → j < N → (κ i = κ j ↔ c i = c j))
    (hsrt : ∀ t t', t < t' → t' < N → G t = G t' → κ (L t) ≤ κ (L t'))
    (hK : ∀ t, K t = (G t, c (L t)))
    (hoff : ∀ j ≤ m, off j = if O j < N then Verify.groupOf K N (O j) else (firstsOf K N).length) :
    (∀ j ≤ m, off j ≤ (firstsOf K N).length) ∧ (∀ a b, a ≤ b → b ≤ m → off a ≤ off b) ∧
      off m = (firstsOf K N).length ∧ ∀ j < m, ∀ j' < m, (SEQ(c, j) = SEQ(c, j') ↔
        ∀ x, (∃ i, O j ≤ i ∧ i < O (j + 1) ∧ c i = x) ↔ (∃ i, O j' ≤ i ∧ i < O (j' + 1) ∧ c i = x)) := by
  have hON : ∀ j ≤ m, O j ≤ N := fun j hj => by have := hO j m hj (Nat.le_refl _); omega
  -- a row is past start `j` exactly when its slice is at least `j`
  have hb : ∀ i < N, ∀ j ≤ m, (O j ≤ i ↔ j ≤ G i) := fun i hi j hj => by
    obtain ⟨h1, h2, h3⟩ := hG i hi
    constructor
    · intro h; apply Nat.not_lt.1; intro hlt
      have := hO (G i + 1) j hlt hj; omega
    · intro h; exact Nat.le_trans (hO j (G i) h (Nat.le_of_lt h1)) h2
  have hin : ∀ i < N, ∀ j < m, (O j ≤ i ∧ i < O (j + 1) ↔ G i = j) := fun i hi j hj => by
    have e1 := hb i hi j (Nat.le_of_lt hj); have e2 := hb i hi (j + 1) hj
    constructor
    · intro ⟨a, b⟩
      have := e1.1 a
      have : ¬ (j + 1 ≤ G i) := fun h => absurd (e2.2 h) (by omega)
      omega
    · intro h; refine ⟨e1.2 (by omega), Nat.lt_of_not_le fun h' => ?_⟩; have := e2.1 h'; omega
  have hFpw : (firstsOf K N).Pairwise (· < ·) := by unfold firstsOf; exact (pairwise_range N).filter _
  -- the first rows below start `j` are those numbered below `off j`
  have hc : ∀ j ≤ m, ∀ r (hr : r < (firstsOf K N).length), ((firstsOf K N)[r] < O j ↔ r < off j) := by
    intro j hj r hr
    rw [hoff j hj]
    split
    · rename_i hlt
      have hmem : O j ∈ firstsOf K N := by
        unfold firstsOf
        simp only [List.mem_filter, List.mem_range, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
        refine ⟨hlt, fun q hq e => ?_⟩
        rw [hK, hK] at e
        have h1 : ¬ j ≤ G q := fun h => absurd ((hb q (by omega) j hj).2 h) (by omega)
        have h2 := (hb (O j) hlt j hj).1 (Nat.le_refl _)
        have := (Prod.mk.inj e).1; omega
      exact firsts_lt_iff hmem hr
    · rename_i hge
      have := Verify.firsts_lt K N (List.getElem_mem hr)
      have : O j = N := by have := hON j hj; omega
      constructor <;> intro _ <;> omega
  have hoffle : ∀ j ≤ m, off j ≤ (firstsOf K N).length := fun j hj => by
    rw [hoff j hj]; split
    · exact Nat.le_of_lt (Verify.groupOf_lt ‹_›)
    · exact Nat.le_refl _
  have hmono : ∀ a b, a ≤ b → b ≤ m → off a ≤ off b := fun a b hab hbm => by
    refine Nat.not_lt.1 fun hlt => ?_
    have hr : off b < (firstsOf K N).length := Nat.lt_of_lt_of_le hlt (hoffle a (by omega))
    have h1 := (hc a (by omega) (off b) hr).2 hlt
    have h2 := (hc b hbm (off b) hr).1 (Nat.lt_of_lt_of_le h1 (hO a b hab hbm))
    exact Nat.lt_irrefl _ h2
  have hoffm : off m = (firstsOf K N).length := by rw [hoff m (Nat.le_refl _), if_neg (by omega)]
  -- the representatives numbered `[off j, off (j+1))` are the first rows in slice `j`
  have hblk : ∀ j < m, ∀ r (hr : r < (firstsOf K N).length),
      (off j ≤ r ∧ r < off (j + 1) ↔ G (firstsOf K N)[r] = j) := fun j hj r hr => by
    have hFN := Verify.firsts_lt K N (List.getElem_mem hr)
    rw [← hin _ hFN j hj]
    have e1 := hc j (by omega) r hr; have e2 := hc (j + 1) hj r hr
    constructor
    · intro ⟨a, b⟩; exact ⟨Nat.not_lt.1 fun h => absurd (e1.1 h) (by omega), e2.2 b⟩
    · intro ⟨a, b⟩; exact ⟨Nat.not_lt.1 fun h => absurd (e1.2 h) (by omega), e2.1 b⟩
  have hgetD : ∀ r (hr : r < (firstsOf K N).length), (firstsOf K N).getD r 0 = (firstsOf K N)[r] := fun r hr => by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  have hLF : ∀ r < (firstsOf K N).length, L ((firstsOf K N).getD r 0) < N := fun r hr => by
    rw [hgetD r hr]; exact hL _ (Verify.firsts_lt K N (List.getElem_mem hr))
  -- a slice's representatives carry its codes, read through any `φ` that `c` determines
  have hset : ∀ j < m, ∀ (φ : Nat → Nat), (∀ a b, a < N → b < N → c a = c b → φ a = φ b) → ∀ x,
      ((∃ r, off j ≤ r ∧ r < off (j + 1) ∧ φ (L ((firstsOf K N).getD r 0)) = x) ↔
        (∃ i, O j ≤ i ∧ i < O (j + 1) ∧ φ i = x)) := fun j hj φ hφ x => by
    constructor
    · rintro ⟨r, h1, h2, e⟩
      have hr : r < (firstsOf K N).length := Nat.lt_of_lt_of_le h2 (hoffle _ hj)
      have hFN := Verify.firsts_lt K N (List.getElem_mem hr)
      rw [hgetD r hr] at e
      have hg : G (L (firstsOf K N)[r]) = j := by rw [hGL _ hFN]; exact (hblk j hj r hr).1 ⟨h1, h2⟩
      have hh := (hin _ (hL _ hFN) j hj).2 hg
      exact ⟨_, hh.1, hh.2, e⟩
    · rintro ⟨i, h1, h2, e⟩
      have hiN : i < N := Nat.lt_of_lt_of_le h2 (hON _ hj)
      obtain ⟨t, ht, rfl⟩ := hLs i hiN
      have hg := (hin _ hiN j hj).1 ⟨h1, h2⟩
      rw [hGL t ht] at hg
      have hr := Verify.groupOf_lt (g := K) ht
      have hkt := Verify.groupOf_get (g := K) ht
      rw [hK, hK] at hkt
      obtain ⟨e1, e2⟩ := Prod.mk.inj hkt
      have hFN := Verify.firsts_lt K N (List.getElem_mem hr)
      have hh := (hblk j hj _ hr).2 (e1.trans hg)
      refine ⟨_, hh.1, hh.2, ?_⟩
      rw [hgetD _ hr, ← e]; exact hφ _ _ (hL _ hFN) (hL _ ht) e2
  have hmemseq : ∀ j < m, ∀ (φ : Nat → Nat) y, (y ∈ SEQ(φ, j) ↔
      ∃ r, off j ≤ r ∧ r < off (j + 1) ∧ φ (L ((firstsOf K N).getD r 0)) = y) := fun j hj φ y => by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨x, hx, e⟩; exact ⟨off j + x, by omega, by omega, e⟩
    · rintro ⟨r, h1, h2, e⟩; exact ⟨r - off j, by omega, by rw [Nat.add_sub_cancel' h1]; exact e⟩
  -- within a slice the representatives' keys strictly rise
  have hstrict : ∀ j < m, (SEQ(κ, j)).Pairwise (· < ·) := fun j hj => by
    refine List.pairwise_map.2 ((pairwise_range _).imp_of_mem fun {a b} ha hb hab => ?_)
    have ha := List.mem_range.1 ha; have hb := List.mem_range.1 hb
    have hbF : off j + b < (firstsOf K N).length := by have := hoffle (j + 1) hj; omega
    have haF : off j + a < (firstsOf K N).length := by omega
    rw [hgetD _ haF, hgetD _ hbF]
    have hFa := Verify.firsts_lt K N (List.getElem_mem haF)
    have hFb := Verify.firsts_lt K N (List.getElem_mem hbF)
    have hF : (firstsOf K N)[off j + a] < (firstsOf K N)[off j + b] :=
      List.pairwise_iff_getElem.1 hFpw _ _ haF hbF (by omega)
    have hga := (hblk j hj _ haF).1 ⟨by omega, by omega⟩
    have hgb := (hblk j hj _ hbF).1 ⟨by omega, by omega⟩
    have hle := hsrt _ _ hF hFb (hga.trans hgb.symm)
    refine Nat.lt_of_le_of_ne hle fun e => ?_
    have ec := (hκ _ _ (hL _ hFa) (hL _ hFb)).1 e
    have := Verify.firsts_inj (g := K) haF hbF (by rw [hK, hK, ec, hga, hgb])
    omega
  have hφκ : ∀ a b, a < N → b < N → c a = c b → κ a = κ b := fun a b ha hb e => (hκ a b ha hb).2 e
  refine ⟨hoffle, hmono, hoffm, fun j hj j' hj' => ⟨fun h x => ?_, fun h => ?_⟩⟩
  · rw [← hset j hj c (fun _ _ _ _ e => e) x, ← hset j' hj' c (fun _ _ _ _ e => e) x, ← hmemseq j hj c x,
      ← hmemseq j' hj' c x, h]
  · have hk : SEQ(κ, j) = SEQ(κ, j') := eq_of_lt_mem (hstrict j hj) (hstrict j' hj') fun y => by
      rw [hmemseq j hj κ y, hmemseq j' hj' κ y, hset j hj κ hφκ y, hset j' hj' κ hφκ y]
      constructor
      · rintro ⟨i, h1, h2, rfl⟩
        obtain ⟨i', h1', h2', e⟩ := (h (c i)).1 ⟨i, h1, h2, rfl⟩
        exact ⟨i', h1', h2', (hκ i' i (Nat.lt_of_lt_of_le h2' (hON _ hj')) (Nat.lt_of_lt_of_le h2 (hON _ hj))).2 e⟩
      · rintro ⟨i, h1, h2, rfl⟩
        obtain ⟨i', h1', h2', e⟩ := (h (c i)).2 ⟨i, h1, h2, rfl⟩
        exact ⟨i', h1', h2', (hκ i' i (Nat.lt_of_lt_of_le h2' (hON _ hj)) (Nat.lt_of_lt_of_le h2 (hON _ hj'))).2 e⟩
    have hl := congrArg List.length hk
    simp only [List.length_map, List.length_range] at hl
    apply List.ext_getElem (by simp only [List.length_map, List.length_range]; exact hl)
    intro x h1 h2
    have e := List.getElem_of_eq hk (by simpa using h1)
    simp only [List.getElem_map, List.getElem_range] at e ⊢
    simp only [List.length_map, List.length_range] at h1 h2
    exact (hκ _ _ (hLF _ (by have := hoffle (j + 1) hj; omega)) (hLF _ (by have := hoffle (j' + 1) hj'; omega))).1 e

-- the long `j` of the starts `s` (with `segments`' classes, `SegN`), and the row the grade `p` puts at sorted
-- position `t`
namespace SegN
set_option hygiene false in
scoped notation "T(" j ")" => UInt64.toNat (Column.bitsAt s (j * 8) 8)
end SegN
open SegN
set_option hygiene false in
local notation "LP(" t ")" => UInt64.toNat (Column.bitsAt p (t * 8) 8)
-- the (slice, code) key of sorted position `t`
set_option hygiene false in
local notation "KP" => fun t => (UInt64.toNat (Column.bitsAt seg (t * 8) 8), Column.idAt vc.b vc.w (LP(t)))

/-- **`setIds` numbers the slices by their sets of codes**: over a well-formed code `vc` and `m` ascending starts
    `s` from `0`, slice `j` being the rows `i < n` from `s[j]` up to the next start, slices `j` and `j'` get one
    id exactly when they hold the same set of codes, and slice `j`'s id is at most `j`. Hypotheses: `vc` well
    formed (lane, exact payload size), true size bounds, and the shape of the starts (`0` first, ascending,
    at most `n`). -/
theorem setIds_spec (vc : Code) (s : ByteArray) {m : Nat}
    (hw : vc.w = 1 ∨ vc.w = 2 ∨ vc.w = 4 ∨ vc.w = 8 ∨ vc.w = 16 ∨ vc.w = 32 ∨ vc.w = 64)
    (hs : vc.b.size = (vc.n.toNat * vc.w + 7) / 8) (hsz : s.size = 8 * m) (hn : vc.n.toNat < 2 ^ 63)
    (hm : m + 1 < 2 ^ 63) (h0 : 0 < m → T(0) = 0) (hasc : ∀ j, j + 1 < m → T(j) ≤ T(j + 1))
    (hle : ∀ j < m, T(j) ≤ vc.n.toNat) {j j' : Nat} (hj : j < m) (hj' : j' < m) :
    (Column.bitsAt (setIds vc s) (8 * j) 8 = Column.bitsAt (setIds vc s) (8 * j') 8 ↔
      ∀ c, (∃ i < vc.n.toNat, T(j) ≤ i ∧ (j + 1 < m → i < T(j + 1)) ∧ Column.idAt vc.b vc.w i = c) ↔
        (∃ i < vc.n.toNat, T(j') ≤ i ∧ (j' + 1 < m → i < T(j' + 1)) ∧ Column.idAt vc.b vc.w i = c)) ∧
      (Column.bitsAt (setIds vc s) (8 * j) 8).toNat ≤ j := by
  have h8 : (Nat.toUSize 8).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  have hg8 : ∀ src idx : ByteArray, (gather 8 src idx).size = 8 * len idx := fun src idx => by
    simp only [gather, KernelWF.gatherBytes_size, h8, len]; omega
  have hw64 : vc.w ≤ 64 := by omega
  have hw0 : 0 < vc.w := by omega
  have hcb : 8 ≤ vc.w → 8 * vc.b.size = vc.w * vc.n.toNat := fun h8 => by
    rcases hw with h | h | h | h | h | h | h <;> rw [h] at hs ⊢ <;> omega
  unfold setIds
  dsimp only
  -- the offsets `o = s, n`
  obtain ⟨hosz, hoget, holast⟩ := concat_one s vc.n.toUInt64 hsz
  generalize concatBytes #[s, one vc.n.toUInt64] = o at hosz hoget holast ⊢
  have hOl : O(m) = vc.n.toNat := by rw [holast]; simp
  have hOT : ∀ j < m, O(j) = T(j) := fun j hj => by rw [hoget j hj]
  have hOs : ∀ j < m, O(j) ≤ O(j + 1) := fun j hj => by
    rw [hOT j hj]
    rcases Nat.lt_or_ge (j + 1) m with h | h
    · rw [hOT _ h]; exact hasc j h
    · rw [show j + 1 = m by omega, hOl]; exact hle j hj
  have hO : ∀ a b, a ≤ b → b ≤ m → O(a) ≤ O(b) := by
    intro a b hab hb
    induction b with
    | zero => cases Nat.le_zero.1 hab; exact Nat.le_refl _
    | succ b ih =>
      rcases Nat.lt_or_eq_of_le hab with h | rfl
      · exact Nat.le_trans (ih (by omega) (by omega)) (hOs b (by omega))
      · exact Nat.le_refl _
  have hol : len o = m + 1 := by simp only [len]; omega
  -- the slice of each row
  obtain ⟨hsegsz, hG⟩ := groupOf_spec o vc.n hosz hn hm (by rw [hOT 0 (by omega)]; exact h0 (by omega))
    hOs hOl
  generalize groupOf o vc.n = seg at hsegsz hG ⊢
  have hsl : len seg = vc.n.toNat := by simp only [len]; omega
  -- the grade `p`: slice, then code
  obtain ⟨hperm, κ, hκ, hsrt⟩ := gradeBy_lex seg vc hw hs hsegsz fun i hi => by have := (hG i hi).1; omega
  generalize gradeBy vc.n #[Code.ofLongs seg, vc] = p at hperm hsrt ⊢
  have hlenp : (ids p).length = vc.n.toNat := by rw [hperm.length_eq, List.length_range]
  have hpl : len p = vc.n.toNat := by rw [len_eq_ids, hlenp]
  have hL : ∀ t < vc.n.toNat, LP(t) < vc.n.toNat := fun t ht => by
    rw [← ids_getElem (by omega)]; exact List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem _))
  have hLs : ∀ i < vc.n.toNat, ∃ t < vc.n.toNat, LP(t) = i := fun i hi => by
    obtain ⟨t, ht, e⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 hi))
    exact ⟨t, by omega, (ids_getElem ht).symm.trans e⟩
  have hGmono : ∀ a b, a ≤ b → b < vc.n.toNat → S(a) ≤ S(b) := fun a b hab hb => by
    refine Nat.not_lt.1 fun hlt => ?_
    have ha := hG a (by omega); have hb' := hG b hb
    have := hO (S(b) + 1) (S(a)) hlt (by omega); omega
  have hsort : ((ids p).map fun i => S(i)).Pairwise (· ≤ ·) :=
    List.pairwise_map.2 (hsrt.imp fun h => by rcases h with h | ⟨h, -⟩ <;> omega)
  have hrng : ((List.range vc.n.toNat).map fun i => S(i)).Pairwise (· ≤ ·) :=
    List.pairwise_map.2 ((pairwise_range _).imp_of_mem fun _ hb hab =>
      hGmono _ _ (Nat.le_of_lt hab) (List.mem_range.1 hb))
  have heq := List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2) hsort hrng (hperm.map _)
  have hGL : ∀ t < vc.n.toNat, S(LP(t)) = S(t) := fun t ht => by
    have e := List.getElem_of_eq heq (i := t) (by simp only [List.length_map]; omega)
    simp only [List.getElem_map, List.getElem_range] at e
    rw [ids_getElem (by omega)] at e; exact e
  -- the sorted (slice, code) pairs and their grouping
  have hpl' : len p < USize.size := by rw [hpl]; exact vc.n.toNat_lt_size
  have hpi : ∀ t < len p, (Column.bitsAt p (t * 8) 8).toNat < vc.n.toNat := fun t ht => hL t (by omega)
  obtain ⟨hBw, hBn, -, hBid⟩ := gather_spec vc p hpl' hw hcb hpi
  have hBs := gather_size vc p hpl' hw
  have hkind : (vc.gather p).kind = vc.kind := by unfold Code.kind; rw [hBw]
  have hBw' : (vc.gather p).w = 1 ∨ (vc.gather p).w = 2 ∨ (vc.gather p).w = 4 ∨ (vc.gather p).w = 8 ∨
      (vc.gather p).w = 16 ∨ (vc.gather p).w = 32 ∨ (vc.gather p).w = 64 := by rw [hBw]; exact hw
  have hBs' : (vc.gather p).b.size = ((vc.gather p).n.toNat * (vc.gather p).w + 7) / 8 := by rw [hBs, hBn, hBw]
  have hBn' : (vc.gather p).n.toNat = vc.n.toNat := by rw [hBn, hpl]
  have hA : (gather 8 seg p).size = 8 * vc.n.toNat := by rw [hg8, hpl]
  have hPK : ∀ t < vc.n.toNat, PK(gather 8 seg p, vc.gather p) t = (S(t), Column.idAt vc.b vc.w (LP(t))) :=
    fun t ht => by
      simp only
      rw [gather8_get (by omega) (by rw [hsl]; exact hL t ht), hGL t ht, hBw, hBid t (by omega)]
  -- the matcher `setIds` elaborated its lane match to (shared with `Code.eqAt`); a `match` written here
  -- elaborates to another one, which `generalize` would not find in the goal
  generalize hX : Code.eqAt.match_1 (fun _ => ByteArray × ByteArray) vc.kind
    (fun k => Order.groupIdsPair .i64 k vc.n (gather 8 seg p) (vc.gather p).b)
    (fun _ => Order.groupIdsPairIds 64 vc.w.toUSize vc.n (gather 8 seg p) (vc.gather p).b) = r
  obtain ⟨q, fs⟩ := r
  have hr' : (q, fs) = match (vc.gather p).kind with
      | some k => Order.groupIdsPair .i64 k vc.n (gather 8 seg p) (vc.gather p).b
      | none => Order.groupIdsPairIds 64 (vc.gather p).w.toUSize vc.n (gather 8 seg p) (vc.gather p).b := by
    rw [hkind, hBw]; exact hX.symm
  obtain ⟨hfs, -, hqcap⟩ := pairIds_read _ _ vc.n hBw' hBs' hBn' hA _ hr'
  have hgl := groupLongs_read _ _ vc.n hBw' hBs' hBn' hA _ hr'
  simp only at hfs hqcap
  obtain ⟨hFeq, -, hGeq⟩ := groups_congr (PK(gather 8 seg p, vc.gather p)) vc.n.toNat
    (g' := KP) fun a ha b hb => by rw [hPK a ha, hPK b hb]
  rw [hFeq] at hfs
  have hFN := firstsOf_length_le KP vc.n.toNat
  have hfl : len fs = (firstsOf KP vc.n.toNat).length := by rw [len_eq_ids, hfs]
  -- the pair numbers widened to longs, then `len fs` appended
  have hglsz : (groupLongs vc.n (q, fs)).size = 8 * vc.n.toNat := by
    have hW : Column.idWidthOf (fs.size / 8) ≤ 64 := by
      unfold Column.idWidthOf
      rcases laneWidth_cases (Column.widthFor (fs.size / 8 - 1)) with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    show (Order.indices _).size = _
    simp only [KernelWF.indices_size, List.length_map, List.length_range, lane_toNat hW, hqcap]; omega
  have hglget : ∀ t < vc.n.toNat, (Column.bitsAt (groupLongs vc.n (q, fs)) (t * 8) 8).toNat =
      Verify.groupOf KP vc.n.toNat t := fun t ht => by
    rw [ids_get hgl (by simpa using ht)]; simp only [List.getElem_map, List.getElem_range]; exact hGeq t ht
  obtain ⟨hc2sz, hc2get, hc2last⟩ := concat_one (groupLongs vc.n (q, fs)) (len fs).toUInt64 hglsz
  generalize concatBytes #[groupLongs vc.n (q, fs), one (len fs).toUInt64] = C2 at hc2sz hc2get hc2last ⊢
  have hc2l : len C2 = vc.n.toNat + 1 := by simp only [len]; omega
  generalize hO'D : gather 8 C2 o = O' at ⊢
  have hO'sz : O'.size = 8 * (m + 1) := by rw [← hO'D, hg8, hol]
  have hoff : ∀ j ≤ m, (Column.bitsAt O' (8 * j) 8).toNat = if O(j) < vc.n.toNat then
      Verify.groupOf KP vc.n.toNat (O(j)) else (firstsOf KP vc.n.toNat).length := fun j hj => by
    have hOj : O(j) ≤ vc.n.toNat := by have := hO j m hj (Nat.le_refl _); omega
    rw [← hO'D, Nat.mul_comm, gather8_get (by omega) (by omega)]
    split
    · rename_i h; rw [hc2get _ h, hglget _ h]
    · rename_i h
      rw [show O(j) = vc.n.toNat by omega, hc2last, ← hfl]; exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hsrtc : ∀ t t', t < t' → t' < vc.n.toNat → S(t) = S(t') → κ (LP(t)) ≤ κ (LP(t')) := fun t t' htt ht' e => by
    have h := List.pairwise_iff_getElem.1 hsrt t t' (by omega) (by omega) htt
    rw [ids_getElem (by omega), ids_getElem (by omega), hGL t (by omega), hGL t' ht'] at h
    rcases h with h | ⟨-, h⟩
    · omega
    · exact h
  obtain ⟨hoffle, hmono, hoffm, hcore⟩ := slices_core (N := vc.n.toNat) (m := m) (O := fun j => O(j))
    (G := fun i => S(i)) (L := fun t => LP(t)) (c := Column.idAt vc.b vc.w) (κ := κ) (K := KP)
    (off := fun j => (Column.bitsAt O' (8 * j) 8).toNat) hO hOl hG hL hLs hGL hκ hsrtc (fun _ => rfl) hoff
  -- the payload: one representative code per pair
  have hidxl : len (gather 8 p fs) = (firstsOf KP vc.n.toNat).length := by rw [gather_len, hfl]
  have hidxget : ∀ r (hr : r < (firstsOf KP vc.n.toNat).length),
      (Column.bitsAt (gather 8 p fs) (r * 8) 8).toNat = LP((firstsOf KP vc.n.toNat)[r]) := fun r hr => by
    have hf := ids_get hfs hr
    rw [gather8_get (by omega) (by rw [hf, hpl]; exact Verify.firsts_lt KP _ (List.getElem_mem hr)), hf]
  have hil : len (gather 8 p fs) < USize.size := by have := vc.n.toNat_lt_size; omega
  obtain ⟨-, -, -, hVid⟩ := gather_spec vc (gather 8 p fs) hil hw hcb fun r hr => by
    rw [hidxget r (by omega)]; exact hL _ (Verify.firsts_lt KP _ (List.getElem_mem _))
  have hVs := gather_size vc (gather 8 p fs) hil hw
  generalize (vc.gather (gather 8 p fs)).b = v at hVid hVs ⊢
  have hrep : ∀ r < (firstsOf KP vc.n.toNat).length, (Column.resAt v 0 vc.w r).toNat =
      Column.idAt vc.b vc.w (LP((firstsOf KP vc.n.toNat).getD r 0)) := fun r hr => by
    show Column.idAt v vc.w r = _
    rw [hVid r (by omega), hidxget r hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  -- `rankSlices`' guards
  have hlt63 : ∀ j ≤ m, (Column.bitsAt O' (8 * j) 8).toNat < 2 ^ 63 := fun j hj => by
    have : (Column.bitsAt O' (8 * j) 8).toNat ≤ _ := hoffle j hj; omega
  have hI : ∀ j ≤ m, (Column.bitsAt O' (8 * j) 8).toInt64.toInt = ((Column.bitsAt O' (8 * j) 8).toNat : Int) :=
    fun j hj => toInt64_toInt (hlt63 j hj)
  have hm8 : O'.size / 8 - 1 = m := by omega
  have hwt : vc.w.toUSize.toNat = vc.w := lane_toNat hw64
  have gw : vc.w.toUSize.toNat ≤ 64 := by rw [hwt]; exact hw64
  have go : 8 ≤ O'.size := by omega
  have g0 : 0 ≤ (Column.bitsAt O' 0 8).toInt64.toInt := by
    have := hI 0 (Nat.zero_le _); rw [Nat.mul_zero] at this; rw [this]; omega
  have gcap : (Column.bitsAt O' (8 * (O'.size / 8 - 1)) 8).toInt64.toInt ≤
      (Column.idsCap v vc.w.toUSize.toNat (Column.bitsAt O' (8 * (O'.size / 8 - 1)) 8).toInt64.toInt.toNat : Int) := by
    rw [hm8, hI m (Nat.le_refl _), Int.toNat_natCast, hwt, idsCap_full hw0]
    · exact Int.le_refl _
    · have e : (Column.bitsAt O' (8 * m) 8).toNat = _ := hoffm
      rw [e, hVs, hidxl, Nat.mul_comm vc.w]
      generalize (firstsOf KP vc.n.toNat).length * vc.w = X; omega
  have gasc : ∀ k, k < O'.size / 8 - 1 →
      (Column.bitsAt O' (8 * k) 8).toInt64.toInt ≤ (Column.bitsAt O' (8 * (k + 1)) 8).toInt64.toInt := fun k hk => by
    rw [hm8] at hk
    rw [hI k (by omega), hI (k + 1) (by omega)]; exact Int.ofNat_le.2 (hmono k (k + 1) (by omega) (by omega))
  have hsize : (Order.rankSlices vc.w.toUSize v O').size = 8 * len s := by
    rw [rankSlices_size _ _ _ gw go g0 gcap gasc, hm8]; simp only [len]; omega
  obtain ⟨hR, hRle⟩ := rankSlices_get _ _ _ gw go g0 gcap gasc (by omega) (j := j) (j' := j')
    (by omega) (by omega)
  simp only [hI j (by omega), hI (j + 1) (by omega), hI j' (by omega), hI (j' + 1) (by omega), Int.toNat_natCast,
    hwt] at hR
  have harr : ∀ (a b : Nat) (f g : Nat → UInt64), (Array.range a).map f = (Array.range b).map g ↔
      (List.range a).map (fun t => (f t).toNat) = (List.range b).map (fun t => (g t).toNat) := fun a b f g => by
    rw [← Array.toList_inj, Array.toList_map, Array.toList_map, Array.toList_range, Array.toList_range]
    constructor
    · intro h; have := congrArg (List.map UInt64.toNat) h; simpa [List.map_map, Function.comp_def] using this
    · intro h
      have hl := congrArg List.length h
      simp only [List.length_map, List.length_range] at hl
      apply List.ext_getElem (by simp only [List.length_map, List.length_range]; exact hl)
      intro x h1 h2
      have e := List.getElem_of_eq h (i := x) (by simpa using h1)
      simp only [List.getElem_map, List.getElem_range] at e ⊢
      exact UInt64.toNat_inj.1 e
  have hseq : ∀ j < m, (List.range ((Column.bitsAt O' (8 * (j + 1)) 8).toNat - (Column.bitsAt O' (8 * j) 8).toNat)).map
      (fun t => (Column.resAt v 0 vc.w ((Column.bitsAt O' (8 * j) 8).toNat + t)).toNat) =
      (List.range ((Column.bitsAt O' (8 * (j + 1)) 8).toNat - (Column.bitsAt O' (8 * j) 8).toNat)).map
      (fun t => Column.idAt vc.b vc.w (LP((firstsOf KP vc.n.toNat).getD ((Column.bitsAt O' (8 * j) 8).toNat + t) 0))) :=
    fun j hj => List.map_congr_left fun t ht => hrep _ (by
      have := List.mem_range.1 ht
      have : (Column.bitsAt O' (8 * (j + 1)) 8).toNat ≤ _ := hoffle (j + 1) hj
      omega)
  have hex : ∀ j < m, ∀ x, (∃ i, O(j) ≤ i ∧ i < O(j + 1) ∧ Column.idAt vc.b vc.w i = x) ↔
      (∃ i < vc.n.toNat, T(j) ≤ i ∧ (j + 1 < m → i < T(j + 1)) ∧ Column.idAt vc.b vc.w i = x) := fun j hj x => by
    rw [hOT j hj]
    have hnext : j + 1 < m → O(j + 1) = T(j + 1) := hOT (j + 1)
    have hON : O(j + 1) ≤ vc.n.toNat := by have := hO (j + 1) m hj (Nat.le_refl _); omega
    constructor
    · rintro ⟨i, h1, h2, e⟩
      exact ⟨i, by omega, h1, fun h => by rw [← hnext h]; exact h2, e⟩
    · rintro ⟨i, hi, h1, h2, e⟩
      refine ⟨i, h1, ?_, e⟩
      by_cases h : j + 1 < m
      · rw [hnext h]; exact h2 h
      · rw [show j + 1 = m by omega, hOl]; exact hi
  have hc := hcore j hj j' hj'
  simp only [need]
  split
  · refine ⟨hR.trans ((harr _ _ _ _).trans ?_), hRle⟩
    dsimp only
    rw [hseq j hj, hseq j' hj']
    exact hc.trans (forall_congr' fun x => iff_congr (hex j hj x) (hex j' hj' x))
  · exact absurd hsize ‹_›

#print axioms setIds_spec
#print axioms concat_one
#print axioms slices_core
#print axioms gradeBy_lex
#print axioms groupOf_spec
#print axioms groupLongs_read
#print axioms idsBy_read
#print axioms pairIds_read
#print axioms firsts_lt_iff
#print axioms eq_of_lt_mem

end LeetQ.Rel.Alg
