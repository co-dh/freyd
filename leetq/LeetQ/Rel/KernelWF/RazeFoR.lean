/-
  The Frame-of-Reference join read back: two atom parts that `razeColumn` joins through `concatFoR` list their
  elements one part after the other. Each of `concatFoR`'s three answers — the blocks moved whole (`moveFoR`),
  the second part's residuals written into the first part's last block (`appendFoR`), the parts decoded,
  joined and encoded again — keeps element `i`'s low `8w` bits, which is all `atomOfBits` reads.
-/
import LeetQ.Rel.KernelWF.AppendFoR

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- A type Frame of Reference encodes is two to eight bytes wide, and neither `boolean` nor `guid`. -/
theorem foR_width {t : QAtomicType} {w : Nat} (he : Column.encodes t = true) (hw : t.width = some w) :
    1 < w ∧ w ≤ 8 ∧ t ≠ .boolean ∧ t ≠ .guid := by
  cases t <;> simp_all [Column.encodes, QAtomicType.width] <;> (try subst hw) <;> decide

/-- A `UInt64` cut to its low `8w` bits, `w ≤ 8`, keeps that value as a `Nat`. -/
theorem ofNat_mod_toNat {w : Nat} (hw8 : w ≤ 8) (v : UInt64) :
    (UInt64.ofNat (v.toNat % 2 ^ (8 * w))).toNat = v.toNat % 2 ^ (8 * w) := by
  have h : v.toNat % 2 ^ (8 * w) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
  simp [Nat.mod_eq_of_lt h]

/-- **`Enc.answer` of a Frame-of-Reference payload keeps its elements**: kept, it is `foRBits`; decoded, it is
    `foRBits`' low `8w` bits (`decodeW`), which `atomOfBits` reads alike (`atomOfBits_mod`). No count bound. -/
theorem get_answer_foR {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) (hg : t ≠ .guid)
    {N : USize} (M P : ByteArray) {i : Nat} (hi : i < N.toNat) :
    Enc.get t N (Enc.answer t N (.foR M P)) i =
      some (Column.atomOfBits t (Column.foRBits M P (Column.blockStarts M) i) (QAtomicType.ne_general_of_width hw)) := by
  have hw8 := width_le8 hw hg
  have hwu := toUSize_toNat_le8 hw8
  have hd := (Verify.decodeW w.toUSize (by rw [hwu]; exact hw8) M P N).2 i hi
  rw [hwu] at hd
  have h1 : Enc.get t N (.bytes (Coc.decode w.toUSize M P N)) i =
      some (Column.atomOfBits t (Column.foRBits M P (Column.blockStarts M) i) (QAtomicType.ne_general_of_width hw)) := by
    rw [get_bytes_eq hw hb hg _ hi, hd, Verify.atomOfBits_mod hw hb hg]
  have h2 : Enc.get t N (.foR M P) i =
      some (Column.atomOfBits t (Column.foRBits M P (Column.blockStarts M) i) (QAtomicType.ne_general_of_width hw)) := by
    rw [get_foR_eq hw hb hg _ _ hi, foRBits_starts]
  have hbo : Enc.bytesOf t N (.foR M P) = some (Coc.decode w.toUSize M P N) := by simp [Enc.bytesOf, hw]
  have hw' := hw
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw' <;> (try subst hw') <;>
    first | exact absurd rfl hg | exact absurd rfl hb |
      (simp only [Enc.answer, QAtomicType.width, hbo] <;> split <;> first | exact h2 | exact h1)

/-- **A part a Frame-of-Reference join reads**, its own payload or its `Enc.encode`: element `i` is the payload's
    `foRBits`. -/
theorem foR_part {t : QAtomicType} {w : Nat} (hen : Column.encodes t = true) (hw : t.width = some w)
    {n : USize} {e : Enc} (hwf : Enc.WF t n e) {md pk : ByteArray}
    (he : e = .foR md pk ∨ Enc.encode t n e = .foR md pk) :
    ∀ i < n.toNat, Enc.get t n e i =
      some (Column.atomOfBits t (Column.foRBits md pk (Column.blockStarts md) i) (QAtomicType.ne_general_of_width hw)) := by
  obtain ⟨hw1, hw8, hb, hg⟩ := foR_width hen hw
  rcases he with rfl | he
  · intro i hi; rw [get_foR_eq hw hb hg _ _ hi, foRBits_starts]
  · obtain ⟨b, hbo, hbs⟩ := bytesOf_size hb hw hwf
    have hE : Coc.encode w.toUSize b = (md, pk) := by
      unfold Enc.encode at he
      simp only [hw, hen, ↓reduceIte, hbo] at he
      rcases hX : Coc.encode w.toUSize b with ⟨m', p'⟩
      simp only [hX, Enc.foR.injEq] at he
      obtain ⟨rfl, rfl⟩ := he; rfl
    intro i hi
    have hib : i < b.size / w := by rw [hbs, Nat.mul_div_cancel _ (by omega)]; exact hi
    have H := Verify.foRBits_encode_bits w hw1 hw8 b i hib
    simp only [hE] at H
    rw [← get_bytesOf hw hb hwf hbo hi, get_bytes_eq hw hb hg _ hi,
      ← Verify.atomOfBits_mod hw hb hg (Column.foRBits md pk _ i), H, UInt64.ofNat_toNat]

/-- At a Frame-of-Reference type, `encodedParts`' `k`-th `(meta, pack)` is part `k`'s own payload or its
    `Enc.encode` (`encodedParts_alp` at flag `false`). -/
theorem encodedParts_foR {t : QAtomicType} (ht : Column.alpEncodes t = false) {cs : Array (USize × Enc)} {N : Nat}
    {ns : Array USize} {ms ps as : Array ByteArray} (hE : encodedParts t cs = some (false, N, ns, ms, ps, as))
    (k : Nat) (hk : k < cs.size) :
    ∃ (hm : k < ms.size) (hp : k < ps.size), cs[k].2 = .foR ms[k] ps[k] ∨
      Enc.encode t cs[k].1 cs[k].2 = .foR ms[k] ps[k] := by
  unfold encodedParts at hE
  dsimp only at hE
  split at hE
  · cases hE
  simp only [bind, Option.bind] at hE
  split at hE
  · cases hE
  rename_i qs hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hE
  obtain ⟨-, -, -, rfl, rfl, rfl⟩ := hE
  obtain ⟨hs, hf⟩ := mapM_getElem hq
  have hqk := hf k hk
  refine ⟨by simp [hs, hk], by simp [hs, hk], ?_⟩
  simp only [Array.getElem_map]
  rcases hc : cs[k] with ⟨nk, ek⟩
  rw [hc] at hqk
  cases ek
  case foR m p =>
    simp only [ht, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hqk
    left; simp only [← hqk]
  case alp m p a => simp [ht] at hqk
  all_goals
    right
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at hqk
    split at hqk
    · rename_i m p hen
      simp only [Option.some.injEq] at hqk
      simp only [← hqk]; exact hen
    · cases hqk

/-- `razeColumn`'s Frame-of-Reference join: the vector of the parts' total count whose payload is `Enc.answer`
    of `concatFoR`'s. -/
theorem razeColumn_foR {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hen : Column.encodes t = true)
    {cs : Array (USize × Enc)} {N : Nat} {ns : Array USize} {ms ps as : Array ByteArray}
    (hE : encodedParts t cs = some (false, N, ns, ms, ps, as))
    (hC : denseCheaper 5 N w (straddles (ns.map (·.toNat))) = false)
    {M P : ByteArray} (hX : concatFoR w.toUSize (countBytes ns) ms ps = (M, P))
    {v : QValue} (hv : razeColumn t cs = some v) :
    ∃ _ : N < USize.size, v = .vector t N.toUSize (Enc.answer t N.toUSize (.foR M P)) none := by
  obtain ⟨-, -, -, hsz, -, -, -⟩ := encodedParts_spec hE
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases t
  all_goals first | (simp [Column.encodes] at hen; done) | skip
  all_goals
    simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
    simp only [QAtomicType.width, hE, Bool.false_eq_true, ↓reduceIte, hC] at hv
    obtain ⟨hc, hv⟩ := needSize_some hv
    simp only [need, hsz, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, hX] at hv
    cases hv; exact ⟨hc, rfl⟩

/-- `concatFoR` at two parts, its three answers in turn. -/
theorem concatFoR_two (ew n0 n1 : USize) (m0 m1 p0 p1 : ByteArray) :
    concatFoR ew (countBytes #[n0, n1]) #[m0, m1] #[p0, p1] =
      match moveFoR #[((n0, m0), p0), ((n1, m1), p1)] with
      | some out => out
      | none => match appendFoR n0 m0 p0 (concatBytes #[Coc.decode 8 m1 p1 n1]) with
        | some out => out
        | none => Coc.encode ew (concatBytes #[Coc.decode ew m0 p0 n0, Coc.decode ew m1 p1 n1]) := by
  have hu : ∀ u : USize, u.toUInt64.toUSize = u := fun u => by simp
  have h0 : Column.bitsAt (countBytes #[n0, n1]) 0 8 = n0.toUInt64 := by
    simpa using countBytes_get #[n0, n1] 0 (by simp)
  have h1 : Column.bitsAt (countBytes #[n0, n1]) 8 8 = n1.toUInt64 := by
    simpa using countBytes_get #[n0, n1] 1 (by simp)
  have hr : Array.range (min ((countBytes #[n0, n1]).size / 8)
      (min (#[m0, m1] : Array ByteArray).size (#[p0, p1] : Array ByteArray).size)) = #[0, 1] := by
    rw [countBytes_size]; show Array.range (min (8 * 2 / 8) (min 2 2)) = #[0, 1]; decide
  have hx : ∀ {α : Type} (a b : α), (#[a, b] : Array α).extract 1 = #[b] := fun _ _ => rfl
  unfold concatFoR
  simp only [hr, List.map_toArray, List.map_cons, List.map_nil, Nat.mul_zero, Nat.mul_one, h0, h1, hu]
  simp only [hx, List.map_toArray, List.map_cons, List.map_nil]
  rfl

/-- **The re-encoded join** keeps element `i`'s low `8w` bits: `Coc.encode` reads back the joined decodes
    (`foRBits_encode_bits`), the join lists the first decode then the second (`elemsW_append`), and a decode's
    element is its payload's `foRBits` cut to `8w` bits (`decodeW`). -/
theorem reencode_reads {w : Nat} (hw1 : 1 < w) (hw8 : w ≤ 8) (n0 n1 : USize) (m0 p0 m1 p1 : ByteArray)
    {i : Nat} (hi : i < n0.toNat + n1.toNat) :
    (Column.foRBits
      (Coc.encode w.toUSize (concatBytes #[Coc.decode w.toUSize m0 p0 n0, Coc.decode w.toUSize m1 p1 n1])).1
      (Coc.encode w.toUSize (concatBytes #[Coc.decode w.toUSize m0 p0 n0, Coc.decode w.toUSize m1 p1 n1])).2
      (Column.blockStarts
        (Coc.encode w.toUSize (concatBytes #[Coc.decode w.toUSize m0 p0 n0, Coc.decode w.toUSize m1 p1 n1])).1)
      i).toNat % 2 ^ (8 * w) =
    if i < n0.toNat then (Column.foRBits m0 p0 (Column.blockStarts m0) i).toNat % 2 ^ (8 * w)
    else (Column.foRBits m1 p1 (Column.blockStarts m1) (i - n0.toNat)).toNat % 2 ^ (8 * w) := by
  have hwu := toUSize_toNat_le8 hw8
  have hw0 : 0 < w := by omega
  obtain ⟨hs0, hd0⟩ := Verify.decodeW w.toUSize (by rw [hwu]; exact hw8) m0 p0 n0
  obtain ⟨hs1, hd1⟩ := Verify.decodeW w.toUSize (by rw [hwu]; exact hw8) m1 p1 n1
  rw [hwu] at hs0 hs1 hd0 hd1
  generalize Coc.decode w.toUSize m0 p0 n0 = D0 at hs0 hd0 ⊢
  generalize Coc.decode w.toUSize m1 p1 n1 = D1 at hs1 hd1 ⊢
  have hX : concatBytes #[D0, D1] = ByteArray.empty ++ D0 ++ D1 := by
    simp only [concatBytes, List.foldl_toArray', List.foldl_cons, List.foldl_nil]
  rw [hX]
  have hsz : (ByteArray.empty ++ D0 ++ D1).size = w * (n0.toNat + n1.toNat) := by
    simp [ByteArray.size_append, hs0, hs1, Nat.mul_add]
  have hi' : i < (ByteArray.empty ++ D0 ++ D1).size / w := by
    rw [hsz, Nat.mul_div_cancel_left _ hw0]; exact hi
  rw [Verify.foRBits_encode_bits w hw1 hw8 _ i hi']
  have hE := Verify.elemsW_append w hw0 (ByteArray.empty ++ D0) D1 (by simp [ByteArray.size_append, hs0])
  rw [Verify.elemsW_append w hw0 ByteArray.empty D0 (by simp)] at hE
  have hl : ∀ (D : ByteArray) k (h : k < (Verify.elemsW w D).length),
      (Verify.elemsW w D)[k] = Column.bitsAt D (k * w) w := by
    intro D k h; simp [Verify.elemsW]
  have hlen : ∀ (D : ByteArray) (k : Nat), D.size = w * k → (Verify.elemsW w D).length = k := by
    intro D k h; simp [Verify.elemsW, h, Nat.mul_div_cancel_left _ hw0]
  have he0 : Verify.elemsW w ByteArray.empty = [] := by simp [Verify.elemsW]
  rw [he0, List.nil_append] at hE
  have hiX : i < (Verify.elemsW w (ByteArray.empty ++ D0 ++ D1)).length := by rw [hlen _ _ hsz]; exact hi
  have hL0 := hlen D0 n0.toNat hs0
  rw [← hl _ i hiX, List.getElem_of_eq hE hiX, List.getElem_append]
  split
  · rename_i h
    have h' : i < n0.toNat := hL0 ▸ h
    rw [if_pos h', hl, hd0 i h', ofNat_mod_toNat hw8]
  · rename_i h
    have h' : ¬ i < n0.toNat := hL0 ▸ h
    rw [if_neg h', hl, hL0, hd1 _ (by omega), ofNat_mod_toNat hw8]

/-! ### The move -/

/-- What `moveFoR` claims at two parts: the first fills its blocks, both are in the writer's form with no patch
    list, the pack is the two packs end to end, and the metadata is `foRMeta` of the first part's blocks then the
    second's. -/
theorem moveFoR_two {n0 n1 : USize} {m0 p0 m1 p1 M P : ByteArray}
    (h : moveFoR #[((n0, m0), p0), ((n1, m1), p1)] = some (M, P)) :
    n0.toNat % Column.blk = 0 ∧ Coc.foRStd n0 m0 p0 = true ∧ Coc.foRStd n1 m1 p1 = true ∧
    p0.size ≤ Column.blockStart m0 (Column.nblk m0) ∧ p1.size ≤ Column.blockStart m1 (Column.nblk m1) ∧
    P = ByteArray.empty ++ p0 ++ p1 ∧
    ∃ nul sumn T, M = Coc.foRMeta nul sumn T ∧ T.size = Column.nblk m0 + Column.nblk m1 ∧
      ∀ b (hb : b < T.size),
        T[b].1 = (if b < Column.nblk m0 then Column.baseAt m0 b else Column.baseAt m1 (b - Column.nblk m0)) ∧
        T[b].2.2.2 = (if b < Column.nblk m0 then Column.widthAt m0 b else Column.widthAt m1 (b - Column.nblk m0)) := by
  unfold moveFoR at h
  split at h
  · cases h
  rename_i hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hM, hP⟩ := h
  simp only [List.foldl_toArray', List.foldl_cons, List.foldl_nil, Array.empty_append] at hM
  simp at hc
  obtain ⟨hz, ⟨s0, z0⟩, s1, z1⟩ := hc
  refine ⟨hz, s0, s1, z0, z1, ?_, _, _, _, hM.symm, by simp, fun b hb => ?_⟩
  · rw [← hP]
    simp only [concatBytes, List.map_toArray, List.map_cons, List.map_nil, List.foldl_toArray', List.foldl_cons,
      List.foldl_nil]
  · simp only [Array.getElem_append, Array.size_map, Array.size_range, Array.getElem_map, Array.getElem_range]
    split <;> rename_i hh <;> simp [hh]

/-- **The moved join** keeps every element: the first part's blocks then the second's, each block's base, width
    and residuals carried over (`foRMeta_reads`). -/
theorem move_reads {n0 n1 : USize} {m0 p0 m1 p1 M P : ByteArray}
    (h : moveFoR #[((n0, m0), p0), ((n1, m1), p1)] = some (M, P)) {i : Nat} (hi : i < n0.toNat + n1.toNat) :
    Column.foRBits M P (Column.blockStarts M) i = if i < n0.toNat then Column.foRBits m0 p0 (Column.blockStarts m0) i
      else Column.foRBits m1 p1 (Column.blockStarts m1) (i - n0.toNat) := by
  obtain ⟨hz, s0, s1, z0, z1, rfl, nul, sumn, T, rfl, hTs, hTb⟩ := moveFoR_two h
  have w0 := Verify.foRStd_iff.1 s0
  have w1 := Verify.foRStd_iff.1 s1
  have e0 : p0.size = Column.blockStart m0 (Column.nblk m0) := by
    rcases w0.size with h | h
    · exact h
    · cases hT : Coc.foRTail (Column.nblk m0) p0 (Column.blockStart m0 (Column.nblk m0)) <;> simp [hT] at h; omega
  have e1 : p1.size = Column.blockStart m1 (Column.nblk m1) := by
    rcases w1.size with h | h
    · exact h
    · cases hT : Coc.foRTail (Column.nblk m1) p1 (Column.blockStart m1 (Column.nblk m1)) <;> simp [hT] at h; omega
  obtain ⟨hnb, hRb⟩ := Verify.foRMeta_reads nul sumn T (fun b hb => by
    rw [(hTb b hb).2]; split
    · exact Nat.lt_of_le_of_lt (w0.width b (by omega)) (by decide)
    · exact Nat.lt_of_le_of_lt (w1.width _ (by omega)) (by decide))
  have hbase : ∀ b < Column.nblk m0 + Column.nblk m1, Column.baseAt (Coc.foRMeta nul sumn T) b =
      if b < Column.nblk m0 then Column.baseAt m0 b else Column.baseAt m1 (b - Column.nblk m0) := fun b hb => by
    rw [(hRb b (by omega)).1, (hTb b (by omega)).1]
  have hwid : ∀ b < Column.nblk m0 + Column.nblk m1, Column.widthAt (Coc.foRMeta nul sumn T) b =
      if b < Column.nblk m0 then Column.widthAt m0 b else Column.widthAt m1 (b - Column.nblk m0) := fun b hb => by
    rw [(hRb b (by omega)).2, (hTb b (by omega)).2]
  have hbs0 : ∀ b ≤ Column.nblk m0, Column.blockStart (Coc.foRMeta nul sumn T) b = Column.blockStart m0 b := by
    intro b hb
    exact blockStart_congr b (fun c hc => by rw [hwid c (by omega), if_pos (by omega)])
  have hbs1 : ∀ b ≤ Column.nblk m1, Column.blockStart (Coc.foRMeta nul sumn T) (Column.nblk m0 + b) =
      Column.blockStart m0 (Column.nblk m0) + Column.blockStart m1 b := by
    intro b hb
    rw [blockStart_shift (M := Coc.foRMeta nul sumn T) (m := m1) (Column.nblk m0) b (fun c hc => by
      rw [hwid _ (by omega), if_neg (by omega), Nat.add_sub_cancel_left]), hbs0 _ (Nat.le_refl _)]
  have hs0 : (ByteArray.empty ++ p0).size = p0.size := by simp [ByteArray.size_append]
  have hP0 : ∀ k < p0.size, (ByteArray.empty ++ p0 ++ p1)[k]? = p0[k]? := fun k hk => by
    rw [Verify.ba_append_left _ _ _ (by rw [hs0]; exact hk), Verify.ba_append_right' _ _ _ (Nat.zero_le _)]; rfl
  have hP1 : ∀ k, (ByteArray.empty ++ p0 ++ p1)[p0.size + k]? = p1[k]? := fun k => by
    rw [← hs0, Verify.ba_append_right]
  have hPs : (ByteArray.empty ++ p0 ++ p1).size ≤
      Column.blockStart (Coc.foRMeta nul sumn T) (Column.nblk (Coc.foRMeta nul sumn T)) := by
    rw [hnb, hTs, hbs1 _ (Nat.le_refl _)]; simp [ByteArray.size_append]; omega
  have hn0 : n0.toNat = Column.blk * Column.nblk m0 := by rw [w0.nblk]; unfold Column.blk at *; omega
  have hn1 : n1.toNat ≤ Column.blk * Column.nblk m1 := by rw [w1.nblk]; unfold Column.blk; omega
  rw [foRBits_plain hPs, foRBits_plain z0, foRBits_plain z1]
  split
  · rename_i h0
    have hb : i / Column.blk < Column.nblk m0 := by unfold Column.blk at *; omega
    have hb' : i / Column.blk < Column.nblk m0 + Column.nblk m1 := Nat.lt_of_lt_of_le hb (Nat.le_add_right _ _)
    rw [hbase _ hb', if_pos hb, hwid _ hb', if_pos hb, hbs0 _ (Nat.le_of_lt hb)]
    congr 1
    apply resAt_congr; intro k hk
    have hr := resAt_reach (w := Column.widthAt m0 (i / Column.blk)) (Nat.mod_lt i (by unfold Column.blk; decide))
    have hle := blockStart_mono m0 (Nat.succ_le_of_lt hb)
    rw [blockStart_succ] at hle
    exact hP0 _ (by omega)
  · rename_i h0
    have hq : i / Column.blk = Column.nblk m0 + (i - n0.toNat) / Column.blk := by unfold Column.blk at *; omega
    have hr' : i % Column.blk = (i - n0.toNat) % Column.blk := by unfold Column.blk at *; omega
    have hb : (i - n0.toNat) / Column.blk < Column.nblk m1 := by unfold Column.blk at *; omega
    have hb' := Nat.add_lt_add_left hb (Column.nblk m0)
    have hn : ¬ Column.nblk m0 + (i - n0.toNat) / Column.blk < Column.nblk m0 := Nat.not_lt.2 (Nat.le_add_right _ _)
    rw [hq, hr', hbase _ hb', if_neg hn, hwid _ hb', if_neg hn, Nat.add_sub_cancel_left,
      hbs1 _ (Nat.le_of_lt hb), ← e0]
    congr 1
    apply resAt_congr; intro k hk
    rw [Nat.add_assoc]; exact hP1 _

/-! ### The join -/

/-- **The Frame-of-Reference join keeps both parts' elements** to their low `8w` bits, on each of `concatFoR`'s
    three answers: the move, the append, the re-encode. -/
theorem concatFoR_reads {w : Nat} (hw1 : 1 < w) (hw8 : w ≤ 8) {n0 n1 : USize} {m0 p0 m1 p1 M P : ByteArray}
    (hX : concatFoR w.toUSize (countBytes #[n0, n1]) #[m0, m1] #[p0, p1] = (M, P)) {i : Nat}
    (hi : i < n0.toNat + n1.toNat) :
    (Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (8 * w) =
      if i < n0.toNat then (Column.foRBits m0 p0 (Column.blockStarts m0) i).toNat % 2 ^ (8 * w)
      else (Column.foRBits m1 p1 (Column.blockStarts m1) (i - n0.toNat)).toNat % 2 ^ (8 * w) := by
  obtain ⟨rfl, rfl⟩ : M = _ ∧ P = _ := ⟨congrArg Prod.fst hX.symm, congrArg Prod.snd hX.symm⟩
  rw [concatFoR_two]
  split
  · rename_i out hm
    obtain ⟨M, P⟩ := out
    rw [move_reads hm hi]; split <;> rfl
  · split
    · rename_i out ha
      obtain ⟨M, P⟩ := out
      rw [append_reads ha hi]; split <;> rfl
    · exact reencode_reads hw1 hw8 n0 n1 m0 p0 m1 p1 hi

/-- **Two parts' `razeTo` list on the Frame-of-Reference join** (`encodedParts` flag `false`, `denseCheaper =
    false`): the join's elements are the parts' elements to their low `8w` bits (`concatFoR_reads`), which is all
    `atomOfBits` reads (`atomOfBits_mod`). -/
theorem razeTo2_join_foR {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    {w : Nat} {r} (hw : t.width = some w)
    (hE : encodedParts t #[x.part, y.part] = some r) (hr : r.1 = false)
    (hC : denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = false) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  obtain ⟨alp, N, ns, ms, ps, as⟩ := r
  dsimp only at hr; subst hr
  have hC' : denseCheaper 5 N w (straddles (ns.map (·.toNat))) = false := hC
  obtain ⟨hal, hns, hNv, hms, hps, -, hor⟩ := encodedParts_spec hE
  have ht : Column.alpEncodes t = false := hal.symm
  have hen : Column.encodes t = true := by simpa [ht] using hor
  obtain ⟨hw1, hw8, hb, hg8⟩ := foR_width hen hw
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  have hns' : ns = #[n, m] := by rw [hns]; simp [Arr.part]
  subst hns'
  have hNv' : N = n.toNat + m.toNat := by rw [hNv]; simp
  have hNlt : N < USize.size := by rw [hNv']; simpa using hN
  have hNU : N.toUSize.toNat = N := USize.toNat_ofNat_of_lt' hNlt
  obtain ⟨hk0, hp0, he0⟩ := encodedParts_foR ht hE 0 (by simp)
  obtain ⟨hk1, hp1, he1⟩ := encodedParts_foR ht hE 1 (by simp)
  have he0' : x.enc = .foR ms[0] ps[0] ∨ Enc.encode t n x.enc = .foR ms[0] ps[0] := he0
  have he1' : y.enc = .foR ms[1] ps[1] ∨ Enc.encode t m y.enc = .foR ms[1] ps[1] := he1
  have hx0 := foR_part hen hw x.wf he0'
  have hx1 := foR_part hen hw y.wf he1'
  have hms2 : ms = #[ms[0], ms[1]] := Array.ext (by simp [hms]) fun k h1 _ => by
    rcases (by simp [hms] at h1; omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl
  have hps2 : ps = #[ps[0], ps[1]] := Array.ext (by simp [hps]) fun k h1 _ => by
    rcases (by simp [hps] at h1; omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl
  rcases hX : concatFoR w.toUSize (countBytes #[n, m]) ms ps with ⟨M, P⟩
  have hX2 := hX
  rw [hms2, hps2] at hX2
  have hl : ∀ {k : USize} (e : Enc) (f : Nat → UInt64), (∀ i < k.toNat, Enc.get t k e i =
      some (Column.atomOfBits t (f i) (QAtomicType.ne_general_of_width hw))) →
      (List.range k.toNat).map (fun i => ((Enc.get t k e i).bind fun a => Carrier.of? t (.atom a)).getD default) =
        ((List.range k.toNat).map f).map fun b =>
          ((some (Column.atomOfBits t b (QAtomicType.ne_general_of_width hw))).bind
            fun a => Carrier.of? t (.atom a)).getD default := by
    intro k e f h; rw [List.map_map]; apply List.map_congr_left; intro i hi; rw [h i (List.mem_range.1 hi)]; rfl
  have hA : ∀ u v : UInt64, u.toNat % 2 ^ (8 * w) = v.toNat % 2 ^ (8 * w) →
      Column.atomOfBits t u (QAtomicType.ne_general_of_width hw) =
        Column.atomOfBits t v (QAtomicType.ne_general_of_width hw) := by
    intro u v huv
    rw [← Verify.atomOfBits_mod hw hb hg8 u, huv, Verify.atomOfBits_mod hw hb hg8]
  refine razeTo_toList_of hg _ rfl hN (by simp) ?_
  intro c E a hv hc
  rw [show ((#[⟨n, x⟩, ⟨m, y⟩] : Array ((k : USize) × Arr t k)).map (·.2.part)) = #[x.part, y.part] by simp] at hv
  obtain ⟨-, hv⟩ := razeColumn_foR hw hen hE hC' hX hv
  simp only [QValue.vector.injEq] at hv
  obtain ⟨-, rfl, rfl, rfl⟩ := hv
  rw [← hc, hl _ (fun i => Column.foRBits M P (Column.blockStarts M) i) (fun i hi => get_answer_foR hw hb hg8 M P hi),
    hNU, toList_get x hg, toList_get y hg, hl _ _ hx0, hl _ _ hx1, hNv', List.range_add]
  simp only [List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.1 hi
    have h := concatFoR_reads hw1 hw8 hX2 (i := i) (by omega)
    rw [if_pos hi'] at h
    simp only [Function.comp_apply]; rw [hA _ _ h]
  · apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.1 hi
    have h := concatFoR_reads hw1 hw8 hX2 (i := n.toNat + i) (by omega)
    rw [if_neg (by omega), Nat.add_sub_cancel_left] at h
    simp only [Function.comp_apply]; rw [hA _ _ h]

/-- The encoded join `hJ` of `hat_of_join`, at every input. -/
theorem join_foR_all : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y → ∀ w r, t.width = some w →
    encodedParts t #[x.part, y.part] = some r → r.1 = false →
    denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = false →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  intro t n m x y hN _ w r hW hE hr hC
  exact razeTo2_join_foR x y hN hW hE hr hC

/-- **`raze_row`'s `hat` at every type and encoding.** -/
theorem hat_all : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  hat_of_join join_foR_all

/-- **Row read-back of `raze` at every side**, no hypothesis on the encoding. -/
theorem raze_row_full (A : Obj) {n m : USize} (x : Vals A n) (y : Vals A m) (hF : Vals.RazeFits A x y)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part A)).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (k : Nat) (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part A)).toList.map
      fun c : Part A => c.1.toNat).sum.toUSize.toNat) :
    Vals.row (A.raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x ⟨k, h⟩
      else Vals.row y ⟨k - n.toNat, by have := raze2_cnt x y hN; omega⟩ :=
  raze_row hat_all A x y hF hN k hk

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B C : Obj}

/-! `∪`'s notations, one home: `open UnionN` in every file that states a `∪` read-back. They take as arguments
    what they read (the relations, the raze's count proofs), so a use site's names do not leak in. -/
namespace UnionN
-- a one-part code `c` of the `m` values `x` faithful and well formed, `rep_nub`'s `hK` form
set_option hygiene false in
scoped notation "cOK(" c ", " m ", " x ")" => ((∀ {i j : Nat} (hi : i < USize.toNat m) (hj : j < USize.toNat m),
    Column.idAt (c).b (c).w i = Column.idAt (c).b (c).w j ↔ Vals.row x ⟨i, hi⟩ = Vals.row x ⟨j, hj⟩) ∧
  laneOK((c).w) ∧ (c).n = m ∧
    (c).b.size = ((c).n.toNat * (c).w + 7) / 8 ∧
    ((c).w < 8 → (c).card < USize.size ∧ ∀ i < (c).n.toNat, Column.idAt (c).b (c).w i < (c).card))
-- `rep_nub`'s codes of a relation `R`, and the rows `nub` keeps
set_option hygiene false in
scoped notation "kcR(" R ")" => (Obj.codes _ (#v[⟨Rel.n R, Rel.key R⟩] : Vector (Part _) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "vcR(" R ")" => (Obj.codes _ (#v[⟨Rel.n R, Rel.val R⟩] : Vector (Part _) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "nubR(" R ")" => (tuples.tupleIds (kcR(R)) #[vcR(R)]).2
-- `∪`'s two key parts and two value parts, and their raze, `hk`, `hv` the raze's count proofs
set_option hygiene false in
scoped notation "pk(" R ", " S ")" => (#[⟨Rel.n R, Rel.key R⟩, ⟨Rel.n S, Rel.key S⟩] : Array (Part _))
set_option hygiene false in
scoped notation "pv(" R ", " S ")" => (#[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n S, Rel.val S⟩] : Array (Part _))
set_option hygiene false in
scoped notation "Uc(" R ", " S ", " hk ", " hv ")" =>
  (⟨_, Obj.raze _ (pk(R, S)) hk, Obj.raze _ (pv(R, S)) hv⟩ : Rel _ _)
end UnionN
open UnionN

/-- **`rep (R ∪ S) = rep R ∪ rep S`**, no hypothesis on the encoding. -/
theorem rep_union_full (R S : Rel A B) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hNk : ((pk(R, S)).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (hNv : ((pv(R, S)).toList.map fun c : Part B => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits A R.key S.key) (hFv : Vals.RazeFits B R.val S.val)
    (hK : cOK(kcR(Uc(R, S, hNk, hNv)), Rel.n (Uc(R, S, hNk, hNv)), Rel.key (Uc(R, S, hNk, hNv))))
    (hV : cOK(vcR(Uc(R, S, hNk, hNv)), Rel.n (Uc(R, S, hNk, hNv)), Rel.val (Uc(R, S, hNk, hNv))))
    (hk : Vals.PickFits A (Rel.key (Uc(R, S, hNk, hNv))) (ids nubR(Uc(R, S, hNk, hNv))))
    (hv : Vals.PickFits B (Rel.val (Uc(R, S, hNk, hNv))) (ids nubR(Uc(R, S, hNk, hNv)))) :
    rep (R ∪ S) = rep R ∪ rep S :=
  rep_union R S hN hNk hNv (raze_row_full A R.key S.key hFk hNk) (raze_row_full B R.val S.val hFv hNv) hK hV hk hv

/-- **`rep (junc R S)`**, no hypothesis on the encoding. -/
theorem rep_junc_full (R : Rel A C) (S : Rel B C) (hN : R.n.toNat + S.n.toNat < USize.size)
    (h63 : R.n.toNat + S.n.toNat ≤ 2 ^ 63) (hF : Vals.RazeFits C R.val S.val) :
    rep (LeetQ.Rel.Alg.junc R S) = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R) (rep S) :=
  rep_junc R S hN h63 (raze_row_full C R.val S.val hF)

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.KernelWF.append_reads
#print axioms LeetQ.Rel.KernelWF.concatFoR_reads
#print axioms LeetQ.Rel.KernelWF.join_foR_all
#print axioms LeetQ.Rel.KernelWF.razeTo2_join_foR
#print axioms LeetQ.Rel.KernelWF.hat_all
#print axioms LeetQ.Rel.KernelWF.raze_row_full
#print axioms LeetQ.Rel.Rep.rep_union_full
#print axioms LeetQ.Rel.Rep.rep_junc_full
