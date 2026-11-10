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

/-! ## The encoded moves: every one re-encodes `m * w` moved bytes -/

theorem width_le8 {t : QAtomicType} {w : Nat} (hW : t.width = some w) (hg : t ≠ .guid) : 0 < w ∧ w ≤ 8 := by
  cases t <;> simp_all [QAtomicType.width] <;> subst hW <;> decide

/-- `Coc.encode` of `m` elements at the type's width is a Frame-of-Reference payload covering `m`. -/
theorem encode_wf {t : QAtomicType} {w m : Nat} {x : ByteArray} (hW : t.width = some w) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) (hx : x.size = m * w) :
    Enc.WF t m (.foR (Coc.encode w.toUSize x).1 (Coc.encode w.toUSize x).2) := by
  have h8 := width_le8 hW hg
  refine wf_foR (by simp [hW]) hb hg ?_
  rw [Verify.nblk_encode w h8.1 h8.2, hx, Nat.mul_div_cancel _ h8.1]
  simp only [Column.blk]; omega

theorem toUSize_width {t : QAtomicType} {w : Nat} (hW : t.width = some w) : w.toUSize.toNat = w :=
  toNat_toUSize (Nat.lt_of_le_of_lt (by cases t <;> simp_all [QAtomicType.width] <;> omega)
    (Nat.lt_of_lt_of_le (by decide : 16 < 2 ^ 32) USize.le_size))

/-- `cycleFoR` re-encodes the `m * w` sliced bytes: its blocks cover `m`. -/
theorem cycleFoR_wf {t : QAtomicType} {w n off m : Nat} (md pk : ByteArray) (hW : t.width = some w)
    (hb : t ≠ .boolean) (hg : t ≠ .guid) (hn : n < USize.size) (hm : m < USize.size) (h0 : 0 < n) :
    Enc.WF t m (.foR (cycleFoR w.toUSize md pk n.toUSize off.toUSize m.toUSize).1
      (cycleFoR w.toUSize md pk n.toUSize off.toUSize m.toUSize).2) := by
  have hwu := toUSize_width hW
  unfold cycleFoR
  exact encode_wf hW hb hg (by
    rw [hwu, toNat_toUSize hn, toNat_toUSize hm]
    exact cycleBytes_size w n _ m _ (by rw [decode_size, hwu, toNat_toUSize hn]) h0)

/-- `alpMove f` of a well-formed ALP payload of `n`, `f` answering `m` elements at the width it is handed,
    re-encodes them at the blob's own width: its blocks cover `m`. -/
theorem alpMove_wf {t : QAtomicType} {n m : Nat} {md pk a : ByteArray} (hw : Enc.WF t n (.alp md pk a))
    (hn : n < USize.size) (f : USize → ByteArray → ByteArray)
    (hf : ∀ (w : USize) (b : ByteArray), b.size = w.toNat * n → (f w b).size = m * w.toNat) :
    Enc.WF t m (.alp (alpMove f md pk a n.toUSize).1 (alpMove f md pk a n.toUSize).2.1
      (alpMove f md pk a n.toUSize).2.2) := by
  obtain ⟨ht, hF'⟩ : (t = .real ∨ t = .float ∨ t = .datetime) ∧ Column.alpF32 a = (t.width == some 4) := by
    cases t <;> simp_all [Enc.WF]
  have h4 : (4 : USize).toNat = 4 := toNat_small 4 (by decide)
  have h8 : (8 : USize).toNat = 8 := toNat_small 8 (by decide)
  have hA : Column.alpEncodes t = true := by rcases ht with rfl | rfl | rfl <;> rfl
  unfold alpMove
  cases hF : Column.alpF32 a <;> simp only [hF] at hF' ⊢ <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
    refine alpEncodeAt_wf _ hA ?_ _ ?_
  · rcases ht with rfl | rfl | rfl <;> first | rfl | simp [QAtomicType.width] at hF'
  · rw [hf 8 _ (by rw [alpDecode_size _ (by rw [h8]; exact Nat.le_refl _), toNat_toUSize hn]), h8]
    simp only [Bool.false_eq_true, if_false]; rw [Nat.mul_div_cancel _ (by decide)]; exact Nat.le_refl _
  · rcases ht with rfl | rfl | rfl <;> first | rfl | simp [QAtomicType.width] at hF'
  · rw [hf 4 _ (by rw [alpDecode_size _ (by rw [h4]; decide), toNat_toUSize hn]), h4]
    simp only [if_true]; rw [Nat.mul_div_cancel _ (by decide)]; exact Nat.le_refl _

/-- `cycleALP` re-encodes the sliced elements at the blob's own width: its blocks cover `m`. -/
theorem cycleALP_wf {t : QAtomicType} {n off m : Nat} {md pk a : ByteArray} (hw : Enc.WF t n (.alp md pk a))
    (hn : n < USize.size) (hm : m < USize.size) (h0 : 0 < n) :
    Enc.WF t m (.alp (cycleALP md pk a n.toUSize off.toUSize m.toUSize).1
      (cycleALP md pk a n.toUSize off.toUSize m.toUSize).2.1 (cycleALP md pk a n.toUSize off.toUSize m.toUSize).2.2) := by
  unfold cycleALP
  exact alpMove_wf hw hn _ fun w b hb => by
    simp only [toNat_toUSize hn, toNat_toUSize hm]
    exact cycleBytes_size w.toNat n _ m b (by rw [hb, Nat.mul_comm]) h0

/-- A move that writes `w` bytes for each of the `b.size / w` elements it reads keeps the count. -/
theorem move_size {f : USize → ByteArray → ByteArray} (hf : ∀ w b, (f w b).size = b.size / w.toNat * w.toNat)
    (w : USize) (b : ByteArray) {n : Nat} (hb : b.size = w.toNat * n) : (f w b).size = n * w.toNat := by
  rw [hf, hb]
  rcases Nat.eq_zero_or_pos w.toNat with h | h
  · simp [h]
  · rw [Nat.mul_div_cancel_left _ h, Nat.mul_comm]

theorem reverseBytes_size (w : USize) (b : ByteArray) : (reverseBytes w b).size = b.size / w.toNat * w.toNat := by
  unfold reverseBytes
  rw [foldl_size ByteArray.size _ w.toNat (fun _ _ => Column.pushBits_size ..)]; simp

theorem shiftBytes_size (fill : UInt64) (k : Int64) (w : USize) (b : ByteArray) :
    (shiftBytes w fill k b).size = b.size / w.toNat * w.toNat := by
  unfold shiftBytes
  rw [foldl_size ByteArray.size _ w.toNat (fun _ _ => Column.pushBits_size ..)]; simp

/-- A dense move of a well-formed payload's bytes keeps its `n` elements. -/
theorem denseMove_wf {t : QAtomicType} {n w : Nat} {e : Enc} {b : ByteArray} (hb : t ≠ .boolean)
    (hW : t.width = some w) (hw : Enc.WF t n e) (hc : countFits n e) (hbo : Enc.bytesOf t n e = some b)
    {f : USize → ByteArray → ByteArray} (hf : ∀ w b, (f w b).size = b.size / w.toNat * w.toNat) :
    Enc.WF t n (.bytes (f w.toUSize b)) := by
  obtain ⟨b', hb', hs⟩ := bytesOf_size hb hW hw hc
  rw [hbo] at hb'; cases hb'
  have hwu := toUSize_width hW
  exact wf_bytes hb hW (by rw [move_size hf _ _ (by rw [hs, hwu, Nat.mul_comm]), hwu])

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

/-! ## `|x`: `reverseColumn` -/

theorem idWidth_toNat (dof : Array Nat) : (Column.idWidth dof).toUSize.toNat = Column.idWidth dof :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by
    rcases Verify.laneWidth_cases (Column.widthFor (dof.size - 1 - 1)) with h | h | h | h | h | h | h | h <;>
      simp only [Column.idWidth, Column.idWidthOf, h] <;> decide) USize.le_size)

/-- `packIds` at the dictionary's width holds all `n` ids. -/
theorem packIds_wf (dict : ByteArray) (dof : Array Nat) (n : Nat) (f : Nat → Nat) :
    Enc.WF .symbol n (.enum dict dof (Column.packIds (Column.idWidth dof) n f)) :=
  Verify.idsCap_packIds _ _ (Verify.laneWidth_cases (Column.widthFor (dof.size - 1 - 1)))

/-- `reverseFoR` keeps every block, moved or re-encoded: its blocks cover `n`. -/
theorem reverseFoR_wf {t : QAtomicType} {w n : Nat} {md pk : ByteArray} (hW : t.width = some w)
    (hb : t ≠ .boolean) (hg : t ≠ .guid) (hn : n < USize.size) (hcov : n ≤ Column.blk * Column.nblk md) :
    Enc.WF t n (.foR (reverseFoR w.toUSize md pk n.toUSize).1 (reverseFoR w.toUSize md pk n.toUSize).2) := by
  have hwu := toUSize_width hW
  unfold reverseFoR
  split
  · rename_i out hmv
    unfold reverseMoveFoR at hmv
    split at hmv
    · cases hmv
    cases hmv
    refine wf_foR (by simp [hW]) hb hg ?_
    rw [Column.nblk, foRMeta_size, show ∀ k, (33 * k + 16) / 33 = k from fun k => by omega]
    simpa using hcov
  · exact encode_wf hW hb hg (by
      rw [move_size reverseBytes_size _ _ (by rw [decode_size, toNat_toUSize hn, hwu, Nat.mul_comm]), hwu])

/-- `reverseColumn` answers every well-formed column but a general list and a `syms` blob (no arm:
    `reverseColumn`'s dense fallback finds no `rowWidth` at `symbol`). -/
theorem reverseColumn_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general)
    (hs : ∀ b o, e ≠ .syms b o) (hc : countFits n e) : (reverseColumn t n e).isSome := by
  rcases hR : rowWidth t with _ | w
  · cases t <;> simp [rowWidth, denseWidth, QAtomicType.width] at hR hg <;> cases e <;>
      simp_all [Enc.WF, reverseColumn, QAtomicType.width]
  · obtain ⟨hW, hb⟩ : t.width = some w ∧ t ≠ .boolean := by
      cases t <;> simp_all [rowWidth, denseWidth, QAtomicType.width]
    obtain ⟨b, hB, hz⟩ := bytesOf_size hb hW hw hc
    have hz : ¬ b.size < n * w := by omega
    unfold reverseColumn
    cases e <;> cases t <;> simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, foRColumn, rowWidth, denseWidth] <;>
      (repeat' split) <;> simp_all [-Nat.not_lt]

/-- **`|x` answers its `n` well-formed elements**. -/
theorem reverseColumn_wf {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hn : n < USize.size)
    {e' : Enc} (h : reverseColumn t n e = some e') : Enc.WF t n e' := by
  have hc := countFits_of_lt (e := e) hn
  have hdense : ∀ {r : Enc}, (match rowWidth t, Enc.bytesOf t n e with
      | some w, some b => if b.size < n * w then none else some (Enc.bytes (reverseBytes w.toUSize b))
      | _, _ => none) = some r → Enc.WF t n r := by
    intro r hr
    split at hr
    · rename_i w b hR hbo
      split at hr
      · cases hr
      cases hr
      obtain ⟨hW, hb⟩ : t.width = some w ∧ t ≠ .boolean := by
        cases t <;> simp_all [rowWidth, denseWidth, QAtomicType.width]
      exact denseMove_wf hb hW hw hc hbo reverseBytes_size
    · cases hr
  unfold reverseColumn at h
  dsimp only at h
  split at h
  · cases h; simp only [Enc.WF, reverseBits, packOf_size, toNat_toUSize hn]
  · cases h; simp only [reverseIds, idWidth_toNat, toNat_toUSize hn]; exact packIds_wf ..
  · split at h
    · exact hdense h
    · cases h; exact answer_wf (alpMove_wf hw hn _ fun w b hb => move_size reverseBytes_size w b hb) hn
  · split at h
    · rename_i nn md pk w hF hW
      obtain ⟨rfl, rfl⟩ := foRColumn_some hF
      simp only [Enc.WF] at hw
      -- the grid test inside `denseCheaper`'s argument is the first `if` `split` finds
      split at h <;> split at h
      all_goals first | exact hdense h | (cases h; exact answer_wf (reverseFoR_wf hW hw.2.1 hw.2.2.1 hn hw.2.2.2) hn)
    · exact hdense h

/-! ## The prior's operand: `shiftColumn` -/

/-- The index a non-dense shift gathers through holds `n` longs. -/
theorem shiftIndex_size (k : Int64) {n : Nat} (hn : n < USize.size) :
    (shiftBytes 8 Int64.minValue.toUInt64 k (tilLongs n.toUSize)).size / 8 = n := by
  have h8 : (8 : USize).toNat = 8 := toNat_small 8 (by decide)
  have ht := tilLongs_wf n.toUSize
  simp only [Enc.WF, QAtomicType.width] at ht
  rw [shiftBytes_size, h8, ht, toNat_toUSize hn]; omega

/-- `shiftColumn` answers every well-formed column but a general list. -/
theorem shiftColumn_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general)
    (hn : n < USize.size) (k : Int64) (fill : UInt64) : (shiftColumn t k fill n e).isSome := by
  have hc := countFits_of_lt (e := e) hn
  have hG := gatherColumn_isSome hw hg (shiftBytes 8 Int64.minValue.toUInt64 k (tilLongs n.toUSize)) (m := n)
    (by have := shiftIndex_size k hn; omega)
  rcases hD : denseWidth t with _ | w
  · cases t <;> simp [denseWidth, QAtomicType.width] at hD hg <;> cases e <;>
      simp_all [Enc.WF, shiftColumn, foRColumn, denseWidth, Column.encodes, QAtomicType.width]
  · obtain ⟨-, hW, hb, -, -, -, -⟩ := denseWidth_facts hD
    obtain ⟨b, hB, hz⟩ := bytesOf_size hb hW hw hc
    have hz : ¬ b.size < n * w := by omega
    unfold shiftColumn
    cases e <;> cases t <;> simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, foRColumn, denseWidth] <;>
      (repeat' split) <;> simp_all [-Nat.not_lt]

/-- **The shifted operand holds its `n` well-formed elements**. -/
theorem shiftColumn_wf {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hn : n < USize.size)
    {k : Int64} {fill : UInt64} {e' : Enc} (h : shiftColumn t k fill n e = some e') : Enc.WF t n e' := by
  have hc := countFits_of_lt (e := e) hn
  have hdense : ∀ {r : Enc}, (match denseWidth t, Enc.bytesOf t n e with
      | some w, some b => if b.size < n * w then none else some (Enc.bytes (shiftBytes w.toUSize fill k b))
      | _, _ => gatherColumn t n e n (.bytes (shiftBytes 8 Int64.minValue.toUInt64 k (tilLongs n.toUSize)))) =
      some r → Enc.WF t n r := by
    intro r hr
    split at hr
    · rename_i w b hD hbo
      split at hr
      · cases hr
      cases hr
      obtain ⟨-, hW, hb, -, -, -, -⟩ := denseWidth_facts hD
      exact denseMove_wf (f := fun w b => shiftBytes w fill k b) hb hW hw hc hbo (shiftBytes_size fill k)
    · have hi := shiftIndex_size k hn
      have := gatherColumn_wf hw _ (by rw [hi]; exact hr)
      rwa [hi] at this
  unfold shiftColumn at h
  dsimp only at h
  split at h
  · cases h; simp only [Enc.WF, shiftBits, packOf_size, toNat_toUSize hn]
  · split at h
    · exact hdense h
    · cases h; exact answer_wf (alpMove_wf hw hn _ fun w b hb => move_size (shiftBytes_size fill k) w b hb) hn
  · split at h
    · rename_i nn md pk w hF hW
      obtain ⟨rfl, rfl⟩ := foRColumn_some hF
      split at h
      · exact hdense h
      · cases h
        simp only [Enc.WF] at hw
        exact answer_wf (encode_wf hW hw.2.1 hw.2.2.1 (by
          rw [move_size (shiftBytes_size fill k) _ _
            (by rw [decode_size, toNat_toUSize hn, toUSize_width hW, Nat.mul_comm]), toUSize_width hW])) hn
    · exact hdense h

/-! ## `:` of symbols: `assignSyms` -/

/-- A scatter writes inside its destination and never past it: the size is kept, at every width. -/
theorem scatterPacked_size (wb : USize) (dst idx src : ByteArray) (soff : USize) (bcast : Bool) :
    (scatterPacked wb dst idx src soff bcast).size = dst.size := by
  unfold scatterPacked
  dsimp only
  split
  · rfl
  rename_i hw0
  rw [foldl_size ByteArray.size _ 0 (fun acc k => ?_)]
  · simp
  dsimp only
  split
  · simp
  rename_i hu
  split
  · rename_i h8
    have hlt : (Column.bitsAt idx (k * 8) 8).toNat < acc.size * 8 / wb.toNat := by omega
    have h1 : ((Column.bitsAt idx (k * 8) 8).toNat + 1) * wb.toNat ≤ acc.size * 8 :=
      Nat.le_trans (Nat.mul_le_mul_right _ hlt) (Nat.div_mul_le_self _ _)
    have h2 : (wb.toNat / 8) * 8 ≤ wb.toNat := Nat.div_mul_le_self _ _
    have h3 : ((Column.bitsAt idx (k * 8) 8).toNat + 1) * (wb.toNat / 8) * 8 ≤ acc.size * 8 := by
      rw [Nat.mul_assoc]; exact Nat.le_trans (Nat.mul_le_mul_left _ h2) h1
    have h4 := Nat.le_of_mul_le_mul_right h3 (by decide)
    rw [Nat.add_mul, Nat.one_mul] at h4
    simp only [ByteArray.copySlice, ByteArray.size, Array.size_append, Array.size_extract]
    simp only [ByteArray.size] at h4
    omega
  · rcases acc with ⟨bs⟩
    simp only [ByteArray.set!, ByteArray.size, Nat.add_zero]
    first | simp [Array.set!] | simp [Array.setIfInBounds] | (unfold Array.set!; split <;> simp)

/-- `Column.intern` of a well-formed symbol payload is an interned one holding its `n` ids. -/
theorem intern_wf {n : Nat} {e : Enc} (hw : Enc.WF .symbol n e) :
    ∃ d o ids, Column.intern e = .enum d o ids ∧ Column.idsCap ids (Column.idWidth o) n = n := by
  cases e with
  | syms b o =>
    simp only [Enc.WF] at hw
    obtain rfl : n = o.size - 1 := by omega
    exact ⟨_, _, _, rfl, packIds_wf (Order.distinctSyms b o).1 (Order.distinctSyms b o).2 _ _⟩
  | enum d o ids => exact ⟨d, o, ids, rfl, hw⟩
  | _ => simp [Enc.WF, QAtomicType.width] at hw

/-- An interned gather over `til n` holds `n` ids at its answer dictionary's width. -/
theorem gatherIdsTil_wf (dict : ByteArray) (dof : Array Nat) (inRange : Unit → Bool) (m : USize) (ids : ByteArray)
    {n : Nat} (hn : n < USize.size) :
    Enc.WF .symbol n
      (.enum (gatherIds dict dof inRange fun w wo e => gatherPacked m w wo e ids (tilLongs n.toUSize)).1
        (gatherIds dict dof inRange fun w wo e => gatherPacked m w wo e ids (tilLongs n.toUSize)).2.1
        (gatherIds dict dof inRange fun w wo e => gatherPacked m w wo e ids (tilLongs n.toUSize)).2.2) := by
  have key := gatherIds_wf (inRange := inRange) (n := m) (ids := ids) (ix := tilLongs n.toUSize)
    (db := (gatherIds dict dof inRange fun w wo e => gatherPacked m w wo e ids (tilLongs n.toUSize)).1) rfl
  have ht := tilLongs_wf n.toUSize
  simp only [Enc.WF, QAtomicType.width] at ht
  rw [ht, toNat_toUSize hn, Nat.mul_div_cancel _ (by decide)] at key
  exact key

/-- **`:` of symbols answers `n` well-formed elements** for any well-formed symbol payloads `e` of `n`
    and `ye` of `ny`, whatever the indices: two blobs scatter as a blob, an interned meeting widens
    `e`'s ids to the joined dictionary and scatters in place, and the `concatEnum` fallback gathers the
    scattered join over `til n`. -/
theorem assignSyms_wf {n ny : Nat} {e ye : Enc} (hw : Enc.WF .symbol n e) (hy : Enc.WF .symbol ny ye)
    (hn : n < USize.size) (ix : ByteArray) (bcast : Bool) {e' : Enc}
    (h : assignSyms n e ny ye ix bcast = some e') : Enc.WF .symbol n e' := by
  by_cases hs : ∃ b o yb yo, e = .syms b o ∧ ye = .syms yb yo
  · obtain ⟨b, o, yb, yo, rfl, rfl⟩ := hs
    obtain ⟨b', o', h', ho, -⟩ := assignSyms_syms n b o yb yo ix bcast ny
    rw [h'] at h; cases h
    simp only [Enc.WF] at hw ⊢; omega
  obtain ⟨d, o, ids, hc, hcap⟩ := intern_wf hw
  obtain ⟨yd, yo, yi, hyc, -⟩ := intern_wf hy
  unfold assignSyms at h
  split at h
  · exact absurd ⟨_, _, _, _, rfl, rfl⟩ hs
  rw [hc, hyc] at h
  dsimp only at h
  split at h
  · rename_i db dbo yids hh
    cases h
    simp only [Enc.WF, scatterIds]
    rw [Column.idsCap, scatterPacked_size, ← Column.idsCap]
    split
    · rename_i heq
      have hwe : Column.idWidth o = Column.idWidth dbo := by
        rw [← idWidth_toNat o, ← idWidth_toNat dbo, beq_iff_eq.1 heq]
      rw [← hwe]; exact hcap
    · rw [idWidth_toNat, toNat_toUSize hn]; exact packIds_wf db dbo _ _
  · split at h
    · cases h; exact gatherIdsTil_wf _ _ _ _ _ hn
    · cases h

/-- **`:` of symbols answers** on well-formed symbol payloads: both of `Column.intern`'s answers are
    interned, and `concatEnum`'s payload is interned whichever way `hashConcat` goes. -/
theorem assignSyms_isSome {n ny : Nat} {e ye : Enc} (hw : Enc.WF .symbol n e) (hy : Enc.WF .symbol ny ye)
    (ix : ByteArray) (bcast : Bool) : (assignSyms n e ny ye ix bcast).isSome := by
  by_cases hs : ∃ b o yb yo, e = .syms b o ∧ ye = .syms yb yo
  · obtain ⟨b, o, yb, yo, rfl, rfl⟩ := hs
    obtain ⟨b', o', h', -, -⟩ := assignSyms_syms n b o yb yo ix bcast ny
    rw [h']; rfl
  obtain ⟨d, o, ids, hc, -⟩ := intern_wf hw
  obtain ⟨yd, yo, yi, hyc, -⟩ := intern_wf hy
  unfold assignSyms
  split
  · exact absurd ⟨_, _, _, _, rfl, rfl⟩ hs
  rw [hc, hyc]
  dsimp only
  split
  · rfl
  · simp only [concatEnum]
    split
    · rfl
    · rename_i hne
      generalize hashConcat _ = r at hne
      rcases r with _ | ⟨db, dbo, ids⟩
      · exact (hne _ _ _ _ _ _ rfl).elim
      · exact (hne _ _ _ _ _ _ rfl).elim

end LeetQ.Rel.KernelWF
