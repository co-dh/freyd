/-
  Reading a Frame-of-Reference pack, and the append read back: `appendFoR` writes the second part's elements
  as residuals into the first part's last block, and the join lists the first part's elements then the
  second's. The pack is the first part's with one block's residual bytes replaced (`splice_reads`); the patch
  list and the frames read only bytes past the last block (`foRExc_congr`, `foRFrame_congr`), the residuals
  below `lo` read back as they were (`resAt_lt`), and an appended residual adds back to its element.
-/
import LeetQ.Rel.KernelWF.RazeEnc
import QLean.Verify.Alp
import QLean.Verify.Group

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel LeetQ.Rel

/-! ### Reading a pack without a patch list -/

/-- `foRBits` with no hoisted table: the block's start is summed. -/
theorem foRBits_nil (md pk : ByteArray) (i : Nat) : Column.foRBits md pk #[] i =
    match Column.foRExc md pk i with
    | some v => v
    | none => Column.baseAt md (i / Column.blk md) + Column.foRFrame md pk (i / Column.blk md) +
        Column.resAt pk (Column.blockStart md (i / Column.blk md)) (Column.widthAt md (i / Column.blk md)) (i % Column.blk md) := by
  unfold Column.foRBits; cases Column.foRExc md pk i <;> simp

/-- A pack that ends by its last block's residuals has no patch list. -/
theorem foRExc_none {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (i : Nat) :
    Column.foRExc md pk i = none := by unfold Column.foRExc; simp [h]

/-- A pack that ends by its last block's residuals has no frames. -/
theorem foRFrame_zero {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (b : Nat) :
    Column.foRFrame md pk b = 0 := by unfold Column.foRFrame; simp [h]

/-- With no patch list, element `i` is its block's base plus its residual. -/
theorem foRBits_plain {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (i : Nat) :
    Column.foRBits md pk (Column.blockStarts md) i = Column.baseAt md (i / Column.blk md) +
      Column.resAt pk (Column.blockStart md (i / Column.blk md)) (Column.widthAt md (i / Column.blk md)) (i % Column.blk md) := by
  rw [← foRBits_starts, foRBits_nil, foRExc_none h, foRFrame_zero h]; simp

theorem blockStart_succ (md : ByteArray) (b : Nat) :
    Column.blockStart md (b + 1) = Column.blockStart md b + Column.blk md * Column.widthAt md b / 8 := by
  simp [Column.blockStart, Nat.fold_succ]

theorem blockStart_mono (md : ByteArray) {a b : Nat} (h : a ≤ b) : Column.blockStart md a ≤ Column.blockStart md b := by
  induction b with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [blockStart_succ]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · exact Nat.le_refl _

/-- Blocks `a, a+1, …` of `M` laid out as `m`'s, at `m`'s block size: their starts are `m`'s, shifted by `M`'s start of block `a`. -/
theorem blockStart_shift {M m : ByteArray} (a : Nat) (hB : Column.blk M = Column.blk m) : ∀ b, (∀ c < b, Column.widthAt M (a + c) = Column.widthAt m c) →
    Column.blockStart M (a + b) = Column.blockStart M a + Column.blockStart m b
  | 0, _ => by simp [Column.blockStart]
  | b + 1, h => by
    rw [← Nat.add_assoc, blockStart_succ, blockStart_succ, blockStart_shift a hB b (fun c hc => h c (by omega)),
      h b (by omega), hB, Nat.add_assoc]

/-- `resAt` reads only the bytes its field overlaps. -/
theorem resAt_congr {P Q : ByteArray} {s s' w j : Nat}
    (h : ∀ k < (j * w + w + 7) / 8, P[s + k]? = Q[s' + k]?) : Column.resAt P s w j = Column.resAt Q s' w j := by
  unfold Column.resAt
  have key : ∀ {f g : UInt64 → Nat → UInt64} (l : List Nat) (a : UInt64), (∀ k ∈ l, ∀ acc, f acc k = g acc k) →
      l.foldl f a = l.foldl g a := by
    intro f g l; induction l with
    | nil => intro a _; rfl
    | cons k l ih =>
      intro a hl; simp only [List.foldl_cons]; rw [hl k (by simp)]
      exact ih _ (fun k' hk' => hl k' (by simp [hk']))
  exact key _ _ fun k hk acc => by
    simp [List.mem_range'] at hk; simp only [h k (by omega)]

/-- A field of a residual `j < B` lies inside its block's `B * w / 8` bytes, `B` a multiple of eight. -/
theorem resAt_reach {B w j : Nat} (hB : 8 ∣ B) (hj : j < B) : (j * w + w + 7) / 8 ≤ B * w / 8 := by
  have : j * w + w ≤ B * w := by
    have := Nat.mul_le_mul_right w (show j + 1 ≤ B by omega); rwa [Nat.succ_mul] at this
  obtain ⟨c, hc⟩ := Nat.dvd_trans hB (Nat.dvd_mul_right B w)
  rw [hc] at this ⊢; omega

/-- `n` not on a block boundary: its block count rounded up is one past the block it lies in. -/
theorem div_ceil_of_mod {B n : Nat} (hB : 0 < B) (h : n % B ≠ 0) : (n + B - 1) / B = n / B + 1 := by
  have := Nat.mod_lt n hB
  have e : n + B - 1 = (n % B - 1) + B * (n / B + 1) := by
    have := Nat.mod_add_div n B; rw [Nat.mul_succ]; omega
  rw [e, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (by omega), Nat.zero_add]

/-- `k` more than `n` inside `n`'s block: same block, `k` further in. -/
theorem div_mod_add {B n k : Nat} (h : n % B + k < B) : (n + k) / B = n / B ∧ (n + k) % B = n % B + k := by
  have hB : 0 < B := by omega
  have e : n + k = (n % B + k) + B * (n / B) := by have := Nat.mod_add_div n B; omega
  constructor
  · rw [e, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h, Nat.zero_add]
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

/-- `i < n` in no earlier block than `n`'s: the same block, `i` before `n` in it. -/
theorem div_eq_mod_lt {B i n : Nat} (hlt : i < n) (hc : ¬ i / B < n / B) : i / B = n / B ∧ i % B < n % B := by
  have hle : i / B ≤ n / B := Nat.div_le_div_right (Nat.le_of_lt hlt)
  have e : i / B = n / B := by omega
  refine ⟨e, ?_⟩
  have h1 := Nat.mod_add_div i B; have h2 := Nat.mod_add_div n B
  rw [e] at h1; omega

/-- A residual read at width `w` is under `2 ^ w`: each byte's share is cut to `w` bits. -/
theorem resAt_lt (P : ByteArray) (s w j : Nat) : (Column.resAt P s w j).toNat < 2 ^ w := by
  unfold Column.resAt
  have key : ∀ (l : List Nat) (a : UInt64), a.toNat < 2 ^ w → (l.foldl (fun acc k =>
      acc ||| (((P[s + k]?.getD 0).toNat * 2 ^ (8 * k) / 2 ^ (j * w) : Nat) % 2 ^ w).toUInt64) a).toNat < 2 ^ w := by
    intro l; induction l with
    | nil => intro a h; exact h
    | cons k l ih =>
      intro a ha; rw [List.foldl_cons]; apply ih
      rw [UInt64.toNat_or]
      refine Nat.or_lt_two_pow ha ?_
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  exact key _ 0 (by simp [Nat.two_pow_pos])

/-! ### What reads past the last block -/

/-- The patch list reads only the pack's size and its bytes from the end of the last block on. -/
theorem foRExc_congr {md P Q : ByteArray} (hs : P.size = Q.size)
    (h : ∀ k, P[Column.blockStart md (Column.nblk md) + k]? = Q[Column.blockStart md (Column.nblk md) + k]?)
    (i : Nat) : Column.foRExc md P i = Column.foRExc md Q i := by
  have hb0 : ∀ w, Column.bitsAt P (Column.blockStart md (Column.nblk md)) w =
      Column.bitsAt Q (Column.blockStart md (Column.nblk md)) w := fun w =>
    Verify.bitsAt_shift P Q _ _ w fun k _ => h k
  have hb : ∀ x w, Column.bitsAt P (Column.blockStart md (Column.nblk md) + x) w =
      Column.bitsAt Q (Column.blockStart md (Column.nblk md) + x) w := fun x w =>
    Verify.bitsAt_shift P Q _ _ w fun k _ => by rw [Nat.add_assoc]; exact h _
  unfold Column.foRExc
  simp only [hs, Nat.add_assoc, hb, hb0]

/-- The frames read only the pack's size and its bytes from the end of the last block on. -/
theorem foRFrame_congr {md P Q : ByteArray} (hs : P.size = Q.size)
    (h : ∀ k, P[Column.blockStart md (Column.nblk md) + k]? = Q[Column.blockStart md (Column.nblk md) + k]?)
    (b : Nat) : Column.foRFrame md P b = Column.foRFrame md Q b := by
  have hb0 : ∀ w, Column.bitsAt P (Column.blockStart md (Column.nblk md)) w =
      Column.bitsAt Q (Column.blockStart md (Column.nblk md)) w := fun w =>
    Verify.bitsAt_shift P Q _ _ w fun k _ => h k
  have hb : ∀ x w, Column.bitsAt P (Column.blockStart md (Column.nblk md) + x) w =
      Column.bitsAt Q (Column.blockStart md (Column.nblk md) + x) w := fun x w =>
    Verify.bitsAt_shift P Q _ _ w fun k _ => by rw [Nat.add_assoc]; exact h _
  unfold Column.foRFrame
  simp only [hs, Nat.add_assoc, hb, hb0]

/-! ### The append -/

/-- `packRes` lays out a whole block, `B * w / 8` bytes. -/
theorem packRes_size (B w : Nat) (R : Nat → UInt64) : (Coc.packRes B w R).size = B * w / 8 := by
  unfold Coc.packRes
  split
  · rename_i h; subst h; simp
  · exact (Verify.fold_push_getElem? _ _ _).1.trans (Nat.zero_add _)

/-- A pack with the bytes `[s, s + L)` replaced by `B`: its size, the bytes before `s` and from `s + L` on are the
    old pack's, and the ones between are `B`'s. -/
theorem splice_reads {p0 B P : ByteArray} {s L : Nat}
    (hP : P = p0.extract 0 s ++ B ++ p0.extract (s + L) p0.size) (hB : B.size = L) (hL : s + L ≤ p0.size) :
    P.size = p0.size ∧ (∀ k < s, P[k]? = p0[k]?) ∧ (∀ k < L, P[s + k]? = B[k]?) ∧
      ∀ k, P[s + L + k]? = p0[s + L + k]? := by
  subst hP
  have hx : ∀ a e k, (p0.extract a e)[k]? = if k < min e p0.size - a then p0[a + k]? else none := fun a e k => by
    rw [show (p0.extract a e)[k]? = (p0.extract a e).data[k]? from rfl, ByteArray.data_extract,
      Verify.extract_getElem?]; rfl
  have hA : (p0.extract 0 s).size = s := by rw [ByteArray.size_extract]; omega
  have hAB : (p0.extract 0 s ++ B).size = s + L := by rw [ByteArray.size_append, hA, hB]
  refine ⟨by rw [ByteArray.size_append, hAB, ByteArray.size_extract]; omega, fun k hk => ?_, fun k hk => ?_,
    fun k => ?_⟩
  · rw [Verify.ba_append_left _ _ _ (by rw [hAB]; omega), Verify.ba_append_left _ _ _ (by rw [hA]; omega), hx,
      if_pos (by omega), Nat.zero_add]
  · rw [Verify.ba_append_left _ _ _ (by rw [hAB]; omega), Verify.ba_append_right' _ _ _ (by rw [hA]; omega), hA,
      Nat.add_sub_cancel_left]
  · rw [Verify.ba_append_right' _ _ _ (by rw [hAB]; omega), hAB, Nat.add_sub_cancel_left, hx]
    split
    · rfl
    · rename_i hk
      show none = p0.data[s + L + k]?
      rw [Array.getElem?_eq_none (by have : p0.data.size = p0.size := rfl; omega)]

theorem add_sub_u64 (a v : UInt64) : a + (v - a) = v := by rw [UInt64.add_comm, UInt64.sub_add_cancel]

/-- **The appended join** reads the first part's elements, then the second's: below `n0` the pack is the first
    part's but for residuals `lo ..` of its last block, which no element below `n0` reads; from `n0` on the element
    is its block's base and frame plus `v - (base + frame)`, which is `v`, the tail's eight-byte element. -/
theorem append_reads {n0 : USize} {n1 : Nat} {m0 p0 D M P : ByteArray}
    (h : appendFoR n0 m0 p0 D = some (M, P)) (hTm : D.size / 8 = n1) {i : Nat}
    (hi : i < n0.toNat + n1) :
    Column.foRBits M P (Column.blockStarts M) i =
      if i < n0.toNat then Column.foRBits m0 p0 (Column.blockStarts m0) i
      else Column.bitsAt D ((i - n0.toNat) * 8) 8 := by
  unfold appendFoR at h
  dsimp only at h
  simp only [hTm] at h
  split at h
  · cases h
  rename_i hc1
  split at h
  · cases h
  rename_i hc2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hM, hP⟩ := h
  subst m0
  have hlo : n0.toNat % Column.blk M ≠ 0 := fun h0 => hc1 (by simp [h0])
  have hm : n0.toNat % Column.blk M + n1 ≤ Column.blk M := Nat.not_lt.1 fun h0 => hc1 (by simp [h0])
  have hstd : Coc.foRStd n0 M p0 = true := by
    cases h0 : Coc.foRStd n0 M p0
    · exact (hc1 (by simp [h0])).elim
    · rfl
  have hexc : ∀ x < Column.blk M - n0.toNat % Column.blk M, Column.foRExc M p0 (n0.toNat + x) = none := by
    intro x hx
    cases h0 : Column.foRExc M p0 (n0.toNat + x)
    · rfl
    · exact (hc1 (by
        simp only [Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.2 ⟨x, List.mem_range.2 hx, by simp [h0]⟩))).elim
  have hres : ∀ x < n1, (Column.bitsAt D (x * 8) 8 -
      (Column.baseAt M (n0.toNat / Column.blk M) + Column.foRFrame M p0 (n0.toNat / Column.blk M))).toNat <
      2 ^ Column.widthAt M (n0.toNat / Column.blk M) := fun x hx =>
    Nat.not_le.1 fun h0 => hc2 (List.any_eq_true.2 ⟨x, List.mem_range.2 hx, by simp [h0]⟩)
  have w0 := Verify.foRStd_iff.1 hstd
  have hnb : Column.nblk M = n0.toNat / Column.blk M + 1 := by
    rw [w0.nblk]; exact div_ceil_of_mod (Verify.blk_pos M) hlo
  have hw64 : Column.widthAt M (n0.toNat / Column.blk M) ≤ 64 := w0.width _ (by omega)
  have hE : Column.blockStart M (Column.nblk M) = Column.blockStart M (n0.toNat / Column.blk M) +
      Column.blk M * Column.widthAt M (n0.toNat / Column.blk M) / 8 := by rw [hnb, blockStart_succ]
  have hsz : Column.blockStart M (Column.nblk M) ≤ p0.size := by
    rcases w0.size with h0 | h0
    · omega
    · cases hT' : Coc.foRTail (Column.nblk M) p0 (Column.blockStart M (Column.nblk M)) <;> simp [hT'] at h0; omega
  obtain ⟨hPs, hP0, hPB, hPE⟩ := splice_reads hP.symm (packRes_size _ _ _) (by omega)
  have hPE' : ∀ k, P[Column.blockStart M (Column.nblk M) + k]? = p0[Column.blockStart M (Column.nblk M) + k]? :=
    fun k => by rw [hE]; exact hPE k
  have hb := Nat.mod_lt i (Verify.blk_pos M)
  rw [← foRBits_starts M P, foRBits_nil, foRExc_congr hPs hPE' i, foRFrame_congr hPs hPE']
  by_cases hlt : i < n0.toNat
  · rw [if_pos hlt, ← foRBits_starts M p0, foRBits_nil]
    have hR : Column.resAt P (Column.blockStart M (i / Column.blk M)) (Column.widthAt M (i / Column.blk M))
        (i % Column.blk M) =
        Column.resAt p0 (Column.blockStart M (i / Column.blk M)) (Column.widthAt M (i / Column.blk M)) (i % Column.blk M) := by
      by_cases hc : i / Column.blk M < n0.toNat / Column.blk M
      · apply resAt_congr; intro k hk
        have hr := resAt_reach (w := Column.widthAt M (i / Column.blk M)) (Verify.blk_dvd8 M) hb
        have hle := blockStart_mono M (Nat.succ_le_of_lt hc)
        rw [blockStart_succ] at hle
        exact hP0 _ (by omega)
      · obtain ⟨hcb, hj⟩ := div_eq_mod_lt hlt hc
        rw [hcb, Verify.resAt_packRes _ _ (Verify.blk_dvd8 M) hw64 _ P _ hPB _ hb]
        try dsimp only
        rw [if_neg (by simp [Nat.not_le.2 hj]), Nat.mod_eq_of_lt (resAt_lt _ _ _ _), Nat.toUInt64_eq,
          UInt64.ofNat_toNat]
    rw [hR]
  · rw [if_neg hlt]
    have hi' : i - n0.toNat < n1 := by omega
    have hdm := div_mod_add (B := Column.blk M) (n := n0.toNat) (k := i - n0.toNat) (by omega)
    rw [show n0.toNat + (i - n0.toNat) = i by omega] at hdm
    obtain ⟨hcb, hj⟩ := hdm
    have hx := hexc (i - n0.toNat) (by omega)
    rw [show n0.toNat + (i - n0.toNat) = i by omega] at hx
    rw [hx, hcb]
    dsimp only
    rw [Verify.resAt_packRes _ _ (Verify.blk_dvd8 M) hw64 _ P _ hPB _ hb]
    try dsimp only
    rw [if_pos (by simp only [hj, Bool.and_eq_true, decide_eq_true_eq]; omega), hj, Nat.add_sub_cancel_left,
      Nat.mod_eq_of_lt (hres _ hi'), Nat.toUInt64_eq, UInt64.ofNat_toNat, add_sub_u64]

end LeetQ.Rel.KernelWF
