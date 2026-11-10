/-
  Totality of the kernels a `Rel` op reads a payload through, under the payload's `Enc.WF`: the facts
  that let `pick`, `Parted.box`, `longBytes` and `gens` drop their `Except`. Each hypothesis is one a
  caller holding an `Arr` already has: `x.wf`, an index `.bytes i` of `i.size / 8` longs.
-/
import QLean.Kernel.Structural
import QLean.Verify.Gather
import QLean.Verify.Raw
import QLean.Verify.Alp

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify

/-- A `long` payload is dense bytes or Frame of Reference: `WF` admits no other layout at `long`. -/
theorem long_cases {n : Nat} {e : Enc} (hw : Enc.WF .long n e) :
    (∃ b, e = .bytes b) ∨ ∃ M P, e = .foR M P := by
  cases e <;> simp_all [Enc.WF, QAtomicType.width]

/-- A general list's payload is a `gen` column of its `n` elements. -/
theorem general_cases {n : Nat} {e : Enc} (hw : Enc.WF .general n e) : ∃ xs, e = .gen xs ∧ xs.size = n := by
  cases e <;> simp_all [Enc.WF, QAtomicType.width]

/-- `bytesOf` answers at every fixed-width type but `boolean`, whose payload is a bitmap. -/
theorem bytesOf_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hb : t ≠ .boolean)
    (hs : t.width.isSome) : (Enc.bytesOf t n e).isSome := by
  cases e <;> cases t <;> simp_all [Enc.WF, Enc.bytesOf, QAtomicType.width]

/-- `bytesOf`'s answer holds the `n` elements: at least `n * w` bytes. An encoded count must fit a
    machine word (`countFits`), the count the decoders are handed. -/
theorem bytesOf_size {t : QAtomicType} {n w : Nat} {e : Enc} (hw : Enc.WF t n e) (hb : t ≠ .boolean)
    (ht : t.width = some w) (hc : countFits n e) {b : ByteArray} (h : Enc.bytesOf t n e = some b) :
    n * w ≤ b.size := by
  by_cases hg : t = .guid
  · subst hg; cases ht; cases e <;> simp_all [Enc.WF, Enc.bytesOf, QAtomicType.width]
  have hw8 : 0 < w ∧ w ≤ 8 := by cases t <;> simp_all [QAtomicType.width] <;> subst ht <;> decide
  have hs : t ≠ .symbol := by rintro rfl; cases ht
  have hl := congrArg List.length (elemsW_bytesOf ht hb hg hw8.1 hw8.2 n e hw hc b h)
  change (elemsW w b).length = _ at hl
  simp only [Array.length_toList, List.length_map,
    size_raw n e hw hb hg hs (QAtomicType.ne_general_of_width ht), elemsW, List.length_range] at hl
  rw [← hl]; exact Nat.div_mul_le_self _ _

/-- **`x@i` answers** for every well-formed column but a general list, and every dense index of at
    least `m` longs. -/
theorem gatherColumn_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general)
    {m : Nat} (i : ByteArray) (hm : m * 8 ≤ i.size) : (gatherColumn t n e m (.bytes i)).isSome := by
  have hz : ¬ i.size < m * 8 := by omega
  unfold gatherColumn
  cases e <;> cases t <;>
    simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
      Column.alpEncodes] <;> split <;> simp_all [-Nat.not_lt]

/-! ## The answer's size: what `Enc.WF` asks of each gather's payload -/

/-- A fold that adds `k` bytes a step adds `k` per element. -/
theorem foldl_size {γ : Type} (f : ByteArray → γ → ByteArray) (k : Nat) (hf : ∀ a j, (f a j).size = a.size + k)
    (l : List γ) (a : ByteArray) : (l.foldl f a).size = a.size + l.length * k := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih => simp only [List.foldl, ih, hf, List.length_cons]; rw [Nat.succ_mul]; omega

theorem packOf_size (n : Nat) (f : Nat → Bool) : (packOf n f).size = (n + 7) / 8 := by
  unfold packOf; rw [foldl_size _ 1 (fun a _ => Verify.ba_size_push ..)]; simp

theorem gatherBits_size (n : USize) (b ix : ByteArray) : (gatherBits n b ix).size = (ix.size / 8 + 7) / 8 :=
  packOf_size ..

/-- `gatherBytes` writes `w` bytes an index element, hit or miss. -/
theorem gatherBytes_size (w : USize) (fill : UInt64) (src ix : ByteArray) :
    (gatherBytes w fill src ix).size = ix.size / 8 * w.toNat := by
  unfold gatherBytes
  rw [foldl_size _ w.toNat, List.length_range]; · simp
  intro a j
  split
  · rename_i i hi
    have hlt : i < src.size / w.toNat := by
      unfold gatherAt at hi; dsimp only at hi; split at hi
      · cases hi; assumption
      · cases hi
    have hle : (i + 1) * w.toNat ≤ src.size := Nat.le_trans (Nat.mul_le_mul_right _ hlt) (Nat.div_mul_le_self _ _)
    rw [Nat.succ_mul] at hle
    split
    · exact Column.pushBits_size ..
    · simp only [ByteArray.size_append, ByteArray.size_extract]; omega
  · exact Column.pushBits_size ..

/-- A fold that pushes one offset a step pushes one per element. -/
theorem foldl_snd_size {α β γ : Type} (f : α × Array β → γ → α × Array β) (hf : ∀ p j, (f p j).2.size = p.2.size + 1)
    (l : List γ) (p : α × Array β) : (l.foldl f p).2.size = p.2.size + l.length := by
  induction l generalizing p with
  | nil => simp
  | cons j l ih => simp only [List.foldl, ih, hf, List.length_cons]; omega

theorem gatherSyms_size (blob : ByteArray) (offs : Array Nat) (ix : ByteArray) :
    (gatherSyms blob offs ix).2.size = ix.size / 8 + 1 := by
  unfold gatherSyms
  rw [foldl_snd_size _ (fun p j => by cases p; simp)]; simp; omega

/-- An interned gather's ids hold all `m` of its answer's elements at the answer dictionary's width. -/
theorem gatherIds_wf {dict : ByteArray} {dof : Array Nat} {inRange : Unit → Bool} {n : USize} {ids ix : ByteArray}
    {db : ByteArray} {dbo : Array Nat} {nids : ByteArray}
    (hG : (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix) = (db, dbo, nids)) :
    Column.idsCap nids (Column.idWidth dbo) (ix.size / 8) = ix.size / 8 := by
  suffices key : Column.idsCap (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix).2.2
      (Column.idWidth (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix).2.1)
      (ix.size / 8) = ix.size / 8 by rw [hG] at key; exact key
  have hl := fun o : Array Nat => Verify.laneWidth_cases (Column.widthFor (o.size - 1 - 1))
  have hU : ∀ o : Array Nat, (Column.idWidth o).toUSize.toNat = Column.idWidth o := fun o =>
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by rcases hl o with h | h | h | h | h | h | h | h <;>
      simp only [Column.idWidth, Column.idWidthOf, h] <;> decide) USize.le_size)
  simp only [gatherIds, gatherPacked]
  split <;> (rw [hU]; exact Verify.idsCap_packIds _ _ (hl _))

theorem gatherAlp_size (fill : UInt64) (md pk a : ByteArray) (n : USize) (ix : ByteArray) :
    (gatherAlp fill md pk a n ix).size = ix.size / 8 * (if Column.alpF32 a then 4 else 8) := by
  unfold gatherAlp; rw [gatherBytes_size]; split <;> simp_all

theorem small_mod (k : Nat) (h : k ≤ 64) : k % 2 ^ System.Platform.numBits = k :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : k < 2 ^ 32)
    (Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> simp [h])))

theorem toNat_small (k : Nat) (h : k ≤ 64) : (USize.ofNat k).toNat = k :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega) USize.le_size)

/-- **`x@i` answers `m` well-formed elements** of the source's type, for a dense index of `m` longs. An
    ALP payload's float width must be its type's (`ha`): `Enc.WF` does not say it, and `gatherAlp`
    writes at the payload's width. -/
theorem gatherColumn_wf {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e)
    (ha : ∀ M P a, e = .alp M P a → Column.alpF32 a = (t.width == some 4)) (i : ByteArray) {e' : Enc}
    (h : gatherColumn t n e (i.size / 8) (.bytes i) = some e') : Enc.WF t (i.size / 8) e' := by
  unfold gatherColumn at h
  generalize hm : i.size / 8 = m at h ⊢
  have hz : ¬ i.size < m * 8 := by omega
  cases e with
  | foR M P =>
    by_cases hc : Column.encodes t = true ∧ M.isEmpty = false <;> cases t <;>
      simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
        Column.encodes, gatherBytes_size, gatherFoR, toNat_small, small_mod] <;> obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := h <;>
      simp [gatherBytes_size, toNat_small, small_mod, hm]
  | enum d o ids =>
    cases t <;> simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, foRColumn, Enc.bytesOf]
    split at h <;> cases h <;> simp only [Enc.WF] at *
    · simp_all
    · subst hm
      exact gatherIds_wf (inRange := fun _ => allBelow (USize.ofNat n) i) (n := USize.ofNat n) (ids := ids)
        (db := (gatherIds d o (fun _ => allBelow (USize.ofNat n) i) fun w wo e =>
          gatherPacked (USize.ofNat n) w wo e ids i).1) rfl
  | _ => cases t <;>
      simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
        Column.alpEncodes, gatherBits_size, gatherBytes_size, gatherAlp_size, gatherSyms_size, gatherIds_wf,
        toNat_small, small_mod] <;> (try subst h) <;>
      simp_all [gatherBits_size, gatherBytes_size, gatherAlp_size, gatherSyms_size, gatherIds_wf, toNat_small,
        small_mod]

/-! ## The slice's answer: sizes and block counts -/

theorem cycleBits_size (n off m : USize) (b : ByteArray) : (cycleBits n off m b).size = (m.toNat + 7) / 8 :=
  packOf_size ..

/-- A cycling symbol slice holds `m + 1` offsets: `Enc.WF`'s count for `syms`. -/
theorem sliceSyms_wf (blob : ByteArray) (offs : Array Nat) (off m : Nat) :
    Enc.WF .symbol m (sliceSyms blob offs off m) := by
  simp only [sliceSyms, Enc.WF]
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.fold_succ, Array.size_push, ih]

/-- An interned slice's ids hold all `m` at the dictionary's width. -/
theorem cycleIds_wf (dict : ByteArray) (dof : Array Nat) (n off : USize) {m : Nat} (hm : m < USize.size)
    (ids : ByteArray) :
    Enc.WF .symbol m (.enum dict dof (cycleIds n off m.toUSize (Column.idWidth dof).toUSize ids)) := by
  have hl := Verify.laneWidth_cases (Column.widthFor (dof.size - 1 - 1))
  have hU : (Column.idWidth dof).toUSize.toNat = Column.idWidth dof :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by rcases hl with h | h | h | h | h | h | h | h <;>
      simp only [Column.idWidth, Column.idWidthOf, h] <;> decide) USize.le_size)
  simp only [Enc.WF, cycleIds, hU, USize.toNat_ofNat_of_lt' hm]
  exact Verify.idsCap_packIds _ _ hl

/-- `alpEncodeAt` lays out a block for every `blk` of its elements: `Enc.WF`'s cover condition. -/
theorem nblk_alpEncodeAt (f32 : Bool) (x : ByteArray) :
    x.size / (if f32 then 4 else 8) ≤ Column.blk * Column.nblk (Coc.alpEncodeAt f32 x).1 := by
  unfold Coc.alpEncodeAt
  simp only []
  rw [show (8 : USize) = (8 : Nat).toUSize from rfl, Verify.nblk_encode 8 (by decide) (by decide),
    Verify.blocks_size]
  simp only [Array.toList_map, Array.toList_range, List.map_map, Function.comp_def, Coc.alpBlockOf,
    Array.size_map, Array.size_range]
  rw [Verify.sum_blocks]
  generalize x.size / (if f32 then 4 else 8) = n
  simp only [Column.blk] at *
  omega
theorem sliceColumn_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general)
    (hc : countFits n e) (off m : Nat) : (sliceColumn t n e off m).isSome := by
  unfold sliceColumn
  rw [dif_neg hg]
  by_cases hbs : t = .boolean ∨ t = .symbol
  · rcases hbs with rfl | rfl <;> by_cases h0 : n = 0 <;> cases e <;> simp_all [Enc.WF, QAtomicType.width, nullColumn]
  have hb : t ≠ .boolean := fun h => hbs (.inl h)
  obtain ⟨w, ht⟩ : ∃ w, t.width = some w := by cases t <;> simp_all [QAtomicType.width]
  by_cases h0 : n = 0
  · subst h0
    have hp := Column.pushBits_size .empty ((nullBits t).getD 0) w
    have hz : ¬ (Column.pushBits .empty ((nullBits t).getD 0) w).size < 1 * w := by simp [hp]
    cases t <;> simp_all [-Nat.not_lt, nullColumn, foRColumn, Enc.bytesOf, QAtomicType.width]
  obtain ⟨b, hB⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome hw hb (by simp [ht]))
  have hz : ¬ b.size < n * w := Nat.not_lt.2 (bytesOf_size hw hb ht hc hB)
  have hn : (n == 0) = false := by simpa using h0
  cases e <;> cases t <;> simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, foRColumn] <;>
    (repeat' split) <;> simp_all [-Nat.not_lt]

end LeetQ.Rel.KernelWF
