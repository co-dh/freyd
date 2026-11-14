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

#print axioms gradeBy_lex
#print axioms groupOf_spec
#print axioms groupLongs_read
#print axioms idsBy_read
#print axioms pairIds_read
#print axioms firsts_lt_iff
#print axioms eq_of_lt_mem

end LeetQ.Rel.Alg
