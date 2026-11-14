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
    | none => Column.baseAt md (i / Column.blk) + Column.foRFrame md pk (i / Column.blk) +
        Column.resAt pk (Column.blockStart md (i / Column.blk)) (Column.widthAt md (i / Column.blk)) (i % Column.blk) := by
  unfold Column.foRBits; cases Column.foRExc md pk i <;> simp

/-- A pack that ends by its last block's residuals has no patch list. -/
theorem foRExc_none {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (i : Nat) :
    Column.foRExc md pk i = none := by unfold Column.foRExc; simp [h]

/-- A pack that ends by its last block's residuals has no frames. -/
theorem foRFrame_zero {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (b : Nat) :
    Column.foRFrame md pk b = 0 := by unfold Column.foRFrame; simp [h]

/-- With no patch list, element `i` is its block's base plus its residual. -/
theorem foRBits_plain {md pk : ByteArray} (h : pk.size ≤ Column.blockStart md (Column.nblk md)) (i : Nat) :
    Column.foRBits md pk (Column.blockStarts md) i = Column.baseAt md (i / Column.blk) +
      Column.resAt pk (Column.blockStart md (i / Column.blk)) (Column.widthAt md (i / Column.blk)) (i % Column.blk) := by
  rw [← foRBits_starts, foRBits_nil, foRExc_none h, foRFrame_zero h]; simp

theorem blockStart_succ (md : ByteArray) (b : Nat) :
    Column.blockStart md (b + 1) = Column.blockStart md b + Column.blk * Column.widthAt md b / 8 := by
  simp [Column.blockStart, Nat.fold_succ]

theorem blockStart_mono (md : ByteArray) {a b : Nat} (h : a ≤ b) : Column.blockStart md a ≤ Column.blockStart md b := by
  induction b with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [blockStart_succ]; exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · exact Nat.le_refl _

/-- Blocks `a, a+1, …` of `M` laid out as `m`'s: their starts are `m`'s, shifted by `M`'s start of block `a`. -/
theorem blockStart_shift {M m : ByteArray} (a : Nat) : ∀ b, (∀ c < b, Column.widthAt M (a + c) = Column.widthAt m c) →
    Column.blockStart M (a + b) = Column.blockStart M a + Column.blockStart m b
  | 0, _ => by simp [Column.blockStart]
  | b + 1, h => by
    rw [← Nat.add_assoc, blockStart_succ, blockStart_succ, blockStart_shift a b (fun c hc => h c (by omega)),
      h b (by omega), Nat.add_assoc]

theorem blockStart_congr {M m : ByteArray} : ∀ b, (∀ c < b, Column.widthAt M c = Column.widthAt m c) →
    Column.blockStart M b = Column.blockStart m b
  | 0, _ => by simp [Column.blockStart]
  | b + 1, h => by rw [blockStart_succ, blockStart_succ, blockStart_congr b (fun c hc => h c (by omega)), h b (by omega)]

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

/-- A field of a residual `j < blk` lies inside its block's `blk * w / 8` bytes. -/
theorem resAt_reach {w j : Nat} (hj : j < Column.blk) : (j * w + w + 7) / 8 ≤ Column.blk * w / 8 := by
  have : j * w + w ≤ Column.blk * w := by
    have := Nat.mul_le_mul_right w (show j + 1 ≤ Column.blk by omega); rwa [Nat.succ_mul] at this
  unfold Column.blk at *; omega

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

/-- `packRes` lays out a whole block, `blk * w / 8` bytes. -/
theorem packRes_size (w : Nat) (R : Nat → UInt64) : (Coc.packRes w R).size = Column.blk * w / 8 := by
  unfold Coc.packRes
  split
  · rename_i h; subst h; rfl
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
    is its block's base and frame plus `v - (base + frame)`, which is `v`, the second part's decoded element. -/
theorem append_reads {n0 n1 : USize} {m0 p0 m1 p1 M P : ByteArray}
    (h : appendFoR n0 m0 p0 (concatBytes #[Coc.decode 8 m1 p1 n1]) = some (M, P)) {i : Nat}
    (hi : i < n0.toNat + n1.toNat) :
    Column.foRBits M P (Column.blockStarts M) i =
      if i < n0.toNat then Column.foRBits m0 p0 (Column.blockStarts m0) i
      else Column.foRBits m1 p1 (Column.blockStarts m1) (i - n0.toNat) := by
  have h8 : (8 : USize).toNat = 8 := toUSize_toNat_le8 (w := 8) (Nat.le_refl _)
  obtain ⟨hD, hDv⟩ := Verify.decodeW 8 (Nat.le_of_eq h8) m1 p1 n1
  rw [h8] at hD hDv
  generalize Coc.decode 8 m1 p1 n1 = D at h hD hDv
  have hX : concatBytes #[D] = D := by
    simp only [concatBytes, List.foldl_toArray', List.foldl_cons, List.foldl_nil, ByteArray.empty_append]
  rw [hX] at h
  have hTm : D.size / 8 = n1.toNat := by rw [hD]; omega
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
  have hlo : n0.toNat % Column.blk ≠ 0 := fun h0 => hc1 (by simp [h0])
  have hm : n0.toNat % Column.blk + n1.toNat ≤ Column.blk := Nat.not_lt.1 fun h0 => hc1 (by simp [h0])
  have hstd : Coc.foRStd n0 M p0 = true := by
    cases h0 : Coc.foRStd n0 M p0
    · exact (hc1 (by simp [h0])).elim
    · rfl
  have hexc : ∀ x < Column.blk - n0.toNat % Column.blk, Column.foRExc M p0 (n0.toNat + x) = none := by
    intro x hx
    cases h0 : Column.foRExc M p0 (n0.toNat + x)
    · rfl
    · exact (hc1 (by
        simp only [Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.2 ⟨x, List.mem_range.2 hx, by simp [h0]⟩))).elim
  have hres : ∀ x < n1.toNat, (Column.bitsAt D (x * 8) 8 -
      (Column.baseAt M (n0.toNat / Column.blk) + Column.foRFrame M p0 (n0.toNat / Column.blk))).toNat <
      2 ^ Column.widthAt M (n0.toNat / Column.blk) := fun x hx =>
    Nat.not_le.1 fun h0 => hc2 (List.any_eq_true.2 ⟨x, List.mem_range.2 hx, by simp [h0]⟩)
  have w0 := Verify.foRStd_iff.1 hstd
  have hnb : Column.nblk M = n0.toNat / Column.blk + 1 := by
    rw [w0.nblk]; unfold Column.blk at hlo ⊢; omega
  have hw64 : Column.widthAt M (n0.toNat / Column.blk) ≤ 64 := w0.width _ (by omega)
  have hE : Column.blockStart M (Column.nblk M) = Column.blockStart M (n0.toNat / Column.blk) +
      Column.blk * Column.widthAt M (n0.toNat / Column.blk) / 8 := by rw [hnb, blockStart_succ]
  have hsz : Column.blockStart M (Column.nblk M) ≤ p0.size := by
    rcases w0.size with h0 | h0
    · omega
    · cases hT' : Coc.foRTail (Column.nblk M) p0 (Column.blockStart M (Column.nblk M)) <;> simp [hT'] at h0; omega
  obtain ⟨hPs, hP0, hPB, hPE⟩ := splice_reads hP.symm (packRes_size _ _) (by omega)
  have hPE' : ∀ k, P[Column.blockStart M (Column.nblk M) + k]? = p0[Column.blockStart M (Column.nblk M) + k]? :=
    fun k => by rw [hE]; exact hPE k
  have hb := Nat.mod_lt i (show 0 < Column.blk by decide)
  rw [← foRBits_starts M P, foRBits_nil, foRExc_congr hPs hPE' i, foRFrame_congr hPs hPE']
  by_cases hlt : i < n0.toNat
  · rw [if_pos hlt, ← foRBits_starts M p0, foRBits_nil]
    have hR : Column.resAt P (Column.blockStart M (i / Column.blk)) (Column.widthAt M (i / Column.blk))
        (i % Column.blk) =
        Column.resAt p0 (Column.blockStart M (i / Column.blk)) (Column.widthAt M (i / Column.blk)) (i % Column.blk) := by
      by_cases hc : i / Column.blk < n0.toNat / Column.blk
      · apply resAt_congr; intro k hk
        have hr := resAt_reach (w := Column.widthAt M (i / Column.blk)) hb
        have hle := blockStart_mono M (Nat.succ_le_of_lt hc)
        rw [blockStart_succ] at hle
        exact hP0 _ (by omega)
      · have hcb : i / Column.blk = n0.toNat / Column.blk := by unfold Column.blk at hc ⊢; omega
        have hj : i % Column.blk < n0.toNat % Column.blk := by unfold Column.blk at hc ⊢; omega
        rw [hcb, Verify.resAt_packRes _ hw64 _ P _ hPB _ hb]
        try dsimp only
        rw [if_neg (by simp [Nat.not_le.2 hj]), Nat.mod_eq_of_lt (resAt_lt _ _ _ _), Nat.toUInt64_eq,
          UInt64.ofNat_toNat]
    rw [hR]
  · rw [if_neg hlt]
    have hi' : i - n0.toNat < n1.toNat := by omega
    have hcb : i / Column.blk = n0.toNat / Column.blk := by unfold Column.blk at hm ⊢; omega
    have hj : i % Column.blk = n0.toNat % Column.blk + (i - n0.toNat) := by unfold Column.blk at hm ⊢; omega
    have hx := hexc (i - n0.toNat) (by omega)
    rw [show n0.toNat + (i - n0.toNat) = i by omega] at hx
    rw [hx, hcb]
    dsimp only
    rw [Verify.resAt_packRes _ hw64 _ P _ hPB _ hb]
    try dsimp only
    rw [if_pos (by simp only [hj, Bool.and_eq_true, decide_eq_true_eq]; omega), hj, Nat.add_sub_cancel_left,
      Nat.mod_eq_of_lt (hres _ hi'), Nat.toUInt64_eq, UInt64.ofNat_toNat, add_sub_u64,
      hDv _ hi', Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from UInt64.toNat_lt_size _), UInt64.ofNat_toNat]

end LeetQ.Rel.KernelWF
