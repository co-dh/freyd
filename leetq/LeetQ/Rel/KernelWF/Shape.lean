/-
  Totality of the shape kernels `take`, `drop`, `rotate`, `reverse`, the prior's shift and the symbol
  amend read a payload through, under the payload's `Enc.WF`: each `_isSome` names the inputs the
  kernel answers, each `_wf` that its answer holds the count the caller's `Arr` claims.
  A count passed to a kernel as a `USize` (`cycleBits`, `cycleIds`, the encoded moves) is asked to fit
  one, because past it the kernel truncates the count, which is a wrong size rather than a decline.
-/
import LeetQ.Rel.KernelWF.Gather
import QLean.Verify.Assign
import QLean.Verify.Structural

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify

theorem toNat_toUSize {k : Nat} (h : k < USize.size) : k.toUSize.toNat = k := by
  simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt h

/-- `q`'s padding source: one well-formed element of `t`'s null. -/
theorem nullColumn_wf (t : QAtomicType) (hg : t ≠ .general) :
    Enc.WF t 1 (nullColumn t hg) ∧ countFits 1 (nullColumn t hg) := by
  cases t <;> first | exact absurd rfl hg | exact ⟨rfl, trivial⟩ | simp [nullColumn, Enc.WF, QAtomicType.width, Column.pushBits_size, countFits]

/-- A cycling slice of a dense payload of `n > 0` elements holds its `m` at the type's width. -/
theorem sliceDense_wf {t : QAtomicType} {n w : Nat} {e : Enc} {b : ByteArray} (hb : t ≠ .boolean)
    (hW : t.width = some w) (hw : Enc.WF t n e) (hc : countFits n e) (h0 : 0 < n)
    (hbo : Enc.bytesOf t n e = some b) (off m : Nat) :
    Enc.WF t m (.bytes (cycleBytes (· * w) n off m b)) := by
  obtain ⟨b', hb', hs⟩ := bytesOf_size hb hW hw hc
  rw [hbo] at hb'; cases hb'
  exact wf_bytes hb hW (cycleBytes_size w n off m b hs h0)

/-- `cycleFoR` re-encodes the `m * w` sliced bytes: its blocks cover `m`. -/
theorem cycleFoR_wf {t : QAtomicType} {w n off m : Nat} (md pk : ByteArray) (hW : t.width = some w)
    (hb : t ≠ .boolean) (hg : t ≠ .guid) (hn : n < USize.size) (hm : m < USize.size) (h0 : 0 < n) :
    Enc.WF t m (.foR (cycleFoR w.toUSize md pk n.toUSize off.toUSize m.toUSize).1
      (cycleFoR w.toUSize md pk n.toUSize off.toUSize m.toUSize).2) := by
  have h8 : 0 < w ∧ w ≤ 8 := by cases t <;> simp_all [QAtomicType.width] <;> subst hW <;> decide
  have hwu : w.toUSize.toNat = w := toNat_toUSize (Nat.lt_of_le_of_lt h8.2 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  refine wf_foR (by simp [hW]) hb hg ?_
  unfold cycleFoR
  rw [Verify.nblk_encode w h8.1 h8.2, hwu, toNat_toUSize hn, toNat_toUSize hm,
    cycleBytes_size w n _ m _ (by rw [decode_size, hwu, toNat_toUSize hn]) h0, Nat.mul_div_cancel _ h8.1]
  simp only [Column.blk]; omega

/-- `cycleALP` re-encodes the sliced elements at the blob's own width: its blocks cover `m`. -/
theorem cycleALP_wf {t : QAtomicType} {n off m : Nat} {md pk a : ByteArray} (hw : Enc.WF t n (.alp md pk a))
    (hn : n < USize.size) (hm : m < USize.size) (h0 : 0 < n) :
    Enc.WF t m (.alp (cycleALP md pk a n.toUSize off.toUSize m.toUSize).1
      (cycleALP md pk a n.toUSize off.toUSize m.toUSize).2.1 (cycleALP md pk a n.toUSize off.toUSize m.toUSize).2.2) := by
  obtain ⟨ht, hf⟩ : (t = .real ∨ t = .float ∨ t = .datetime) ∧ Column.alpF32 a = (t.width == some 4) := by
    cases t <;> simp_all [Enc.WF]
  have h4 : (4 : USize).toNat = 4 := toNat_small 4 (by decide)
  have h8 : (8 : USize).toNat = 8 := toNat_small 8 (by decide)
  have hA : Column.alpEncodes t = true := by rcases ht with rfl | rfl | rfl <;> rfl
  unfold cycleALP alpMove
  cases hF : Column.alpF32 a <;> simp only [hF] at hf ⊢ <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    refine alpEncodeAt_wf _ hA ?_ _ ?_
  · rcases ht with rfl | rfl | rfl <;> simp_all [QAtomicType.width]
  · rw [h8, toNat_toUSize hn, toNat_toUSize hm, cycleBytes_size 8 n _ m _ ?_ h0]
    · simp only [Bool.false_eq_true, if_false]; rw [Nat.mul_div_cancel _ (by decide)]; exact Nat.le_refl _
    · have hs := alpDecode_size 8 (by rw [h8]; exact Nat.le_refl _) md pk a n.toUSize
      rw [h8, toNat_toUSize hn] at hs; rw [hs, Nat.mul_comm]
  · rcases ht with rfl | rfl | rfl <;> first | rfl | simp [QAtomicType.width] at hf
  · rw [h4, toNat_toUSize hn, toNat_toUSize hm, cycleBytes_size 4 n _ m _ ?_ h0]
    · simp only [if_true]; rw [Nat.mul_div_cancel _ (by decide)]; exact Nat.le_refl _
    · have hs := alpDecode_size 4 (by rw [h4]; decide) md pk a n.toUSize
      rw [h4, toNat_toUSize hn] at hs; rw [hs, Nat.mul_comm]

/-- **`sliceColumn` answers `m` well-formed elements** of the source's type, `m` fitting a `USize`. -/
theorem sliceColumn_wf {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hc : countFits n e)
    {off m : Nat} (hm : m < USize.size) {e' : Enc} (h : sliceColumn t n e off m = some e') : Enc.WF t m e' := by
  unfold sliceColumn at h
  split at h
  · cases h
  rename_i hg
  obtain ⟨n', e0, hp, hw', hc', h0⟩ : ∃ n' e0, (if (n == 0) = true then (1, nullColumn t hg) else (n, e)) = (n', e0) ∧
      Enc.WF t n' e0 ∧ countFits n' e0 ∧ 0 < n' := by
    split
    · exact ⟨1, _, rfl, (nullColumn_wf t hg).1, (nullColumn_wf t hg).2, by decide⟩
    · rename_i hz; exact ⟨n, e, rfl, hw, hc, Nat.pos_of_ne_zero (by simpa using hz)⟩
  rw [hp] at h
  dsimp only at h
  have hdense : ∀ {enc : Bool} {r : Enc}, (match t.width, Enc.bytesOf t n' e0 with
      | some w, some b =>
        if b.size < n' * w then none else
        some (if enc then Enc.answer t m (.bytes (cycleBytes (· * w) n' off m b)) else .bytes (cycleBytes (· * w) n' off m b))
      | _, _ => none) = some r → Enc.WF t m r := by
    intro enc r hr
    split at hr
    · rename_i w b hW hbo
      have hb : t ≠ .boolean := by rintro rfl; cases e0 <;> simp_all [Enc.WF, Enc.bytesOf]
      split at hr
      · cases hr
      cases hr
      have hd := sliceDense_wf hb hW hw' hc' h0 hbo off m
      split
      · exact answer_wf hd hm
      · exact hd
    · cases hr
  split at h
  · cases h; simp only [Enc.WF, cycleBits_size, toNat_toUSize hm]
  · cases h; exact sliceSyms_wf ..
  · cases h; exact cycleIds_wf _ _ _ _ hm _
  · split at h
    · exact hdense h
    · cases h; exact answer_wf (cycleALP_wf hw' hc' hm h0) hm
  · split at h
    · rename_i nn md pk w hF hW
      obtain ⟨rfl, rfl⟩ := foRColumn_some hF
      split at h
      · exact hdense h
      · cases h
        have hb : t ≠ .boolean ∧ t ≠ .guid := by simp only [Enc.WF] at hw'; exact ⟨hw'.2.1, hw'.2.2.1⟩
        exact answer_wf (cycleFoR_wf md pk hW hb.1 hb.2 hc' hm h0) hm
    · exact hdense h

/-! ## `n#x`, `n_x`, `n rotate x`: one slice each -/

theorem takeColumn_isSome {t : QAtomicType} {len : Nat} {e : Enc} (hw : Enc.WF t len e) (hg : t ≠ .general)
    (hc : countFits len e) (n : Int) : (takeColumn t len e n).isSome := by
  simpa [takeColumn] using sliceColumn_isSome hw hg hc (takeFrom n len) n.natAbs

/-- **`n#x` answers `|n|` well-formed elements**. -/
theorem takeColumn_wf {t : QAtomicType} {len : Nat} {e : Enc} (hw : Enc.WF t len e) (hc : countFits len e)
    {n : Int} (hn : n.natAbs < USize.size) {v : QValue} (h : takeColumn t len e n = some v) :
    ∃ e', v = .vector t n.natAbs e' none ∧ Enc.WF t n.natAbs e' := by
  simp only [takeColumn, Option.map_eq_some_iff] at h
  obtain ⟨e', he, rfl⟩ := h
  exact ⟨e', rfl, sliceColumn_wf hw hc hn he⟩

theorem dropColumn_isSome {t : QAtomicType} {len : Nat} {e : Enc} (hw : Enc.WF t len e) (hg : t ≠ .general)
    (hc : countFits len e) (n : Int) : (dropColumn t len e n).isSome := by
  simpa [dropColumn] using sliceColumn_isSome hw hg hc _ _

/-- **`n_x` answers `len - |n|` well-formed elements**. -/
theorem dropColumn_wf {t : QAtomicType} {len : Nat} {e : Enc} (hw : Enc.WF t len e) (hl : len < USize.size)
    {n : Int} {v : QValue} (h : dropColumn t len e n = some v) :
    ∃ e', v = .vector t (len - n.natAbs) e' none ∧ Enc.WF t (len - n.natAbs) e' := by
  simp only [dropColumn, Option.map_eq_some_iff] at h
  obtain ⟨e', he, rfl⟩ := h
  have hk : len - min n.natAbs len = len - n.natAbs := by omega
  rw [hk] at he ⊢
  exact ⟨e', rfl, sliceColumn_wf hw (countFits_of_lt hl) (by omega) he⟩

theorem rotateColumn_isSome {t : QAtomicType} {m : Nat} {e : Enc} (hw : Enc.WF t m e) (hg : t ≠ .general)
    (hc : countFits m e) (n : Int) : (rotateColumn t n m e).isSome :=
  sliceColumn_isSome hw hg hc _ _

/-- **`n rotate x` answers its `m` well-formed elements**. -/
theorem rotateColumn_wf {t : QAtomicType} {m : Nat} {e : Enc} (hw : Enc.WF t m e) (hm : m < USize.size)
    {n : Int} {e' : Enc} (h : rotateColumn t n m e = some e') : Enc.WF t m e' :=
  sliceColumn_wf hw (countFits_of_lt hm) hm h

end LeetQ.Rel.KernelWF
