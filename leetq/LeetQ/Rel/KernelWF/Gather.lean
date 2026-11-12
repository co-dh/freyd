/-
  Totality of the kernels a `Rel` op reads a payload through, under the payload's `Enc.WF`: the facts
  that let `pick`, `longBytes` and `gens` drop their `Except`. Each hypothesis is one a
  caller holding an `Arr` already has: `x.wf`, an index `.bytes i` of `i.size / 8` longs.
-/
import QLean.Kernel.Structural
import QLean.Verify.Gather
import QLean.Verify.Raw
import QLean.Verify.Alp
import LeetQ.Rel.KernelWF.Raze

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify

/-- A `long` payload is dense bytes or Frame of Reference: `WF` admits no other layout at `long`. -/
theorem long_cases {n : USize} {e : Enc} (hw : Enc.WF .long n e) :
    (∃ b, e = .bytes b) ∨ ∃ M P, e = .foR M P := by
  cases e <;> simp_all [Enc.WF, QAtomicType.width]

/-- A general list's payload is a `gen` column of its `n` elements. -/
theorem general_cases {n : USize} {e : Enc} (hw : Enc.WF .general n e) :
    ∃ xs, e = .gen xs ∧ xs.size = n.toNat := by
  cases e <;> simp_all [Enc.WF, QAtomicType.width]

/-- **`x@i` answers** for every well-formed column but a general list, and every dense index of at
    least `m` longs. -/
theorem gatherColumn_isSome {t : QAtomicType} {n : USize} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general)
    {m : USize} (i : ByteArray) (hm : m.toNat * 8 ≤ i.size) : (gatherColumn t n e m (.bytes i)).isSome := by
  have hz : ¬ i.size < m.toNat * 8 := by omega
  unfold gatherColumn
  cases e <;> cases t <;>
    simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
      Column.alpEncodes] <;> split <;> simp_all [-Nat.not_lt]

/-! ## The answer's size: what `Enc.WF` asks of each gather's payload -/

theorem gatherBits_size (n : USize) (b ix : ByteArray) : (gatherBits n b ix).size = (ix.size / 8 + 7) / 8 :=
  packOf_size ..

/-- `gatherBytes` writes `w` bytes an index element, hit or miss. -/
theorem gatherBytes_size (w : USize) (fill : UInt64) (src ix : ByteArray) :
    (gatherBytes w fill src ix).size = ix.size / 8 * w.toNat := by
  unfold gatherBytes
  rw [foldl_size ByteArray.size _ w.toNat, List.length_range]; · simp
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

/-- An interned gather's dictionary ends at its blob with no offset past it, where the source's does: the
    empty symbol it may append is one NUL past the old end. -/
theorem gatherIds_dict {dict : ByteArray} {dof : Array Nat} {inRange : Unit → Bool}
    {g : USize → USize → UInt64 → ByteArray}
    (hl : dof[dof.size - 1]! = dict.size) (hle : ∀ k < dof.size, dof[k]! ≤ dict.size) :
    (gatherIds dict dof inRange g).2.1[(gatherIds dict dof inRange g).2.1.size - 1]! =
        (gatherIds dict dof inRange g).1.size ∧
      ∀ k < (gatherIds dict dof inRange g).2.1.size,
        (gatherIds dict dof inRange g).2.1[k]! ≤ (gatherIds dict dof inRange g).1.size := by
  unfold gatherIds
  dsimp only
  split
  · exact ⟨hl, hle⟩
  · show (dof.push (dict.size + 1))[(dof.push (dict.size + 1)).size - 1]! = (dict.push 0).size ∧
      ∀ k < (dof.push (dict.size + 1)).size, (dof.push (dict.size + 1))[k]! ≤ (dict.push 0).size
    have hs : (dof.push (dict.size + 1)).size = dof.size + 1 := Array.size_push ..
    have hp : (dict.push 0).size = dict.size + 1 := by simp only [ByteArray.size, ByteArray.push, Array.size_push]
    have hlast : (dof.push (dict.size + 1))[dof.size]! = dict.size + 1 := by
      rw [getElem!_pos _ dof.size (by omega), Array.getElem_push_eq]
    refine ⟨by rw [hs, Nat.add_sub_cancel, hlast, hp], fun k hk => ?_⟩
    rw [hp]
    rcases Nat.lt_or_ge k dof.size with h | h
    · rw [getElem!_pos _ k (by omega), Array.getElem_push_lt h, ← getElem!_pos dof k h]
      exact Nat.le_succ_of_le (hle k h)
    · rw [show k = dof.size by omega, hlast]; exact Nat.le_refl _

theorem gatherAlp_size (fill : UInt64) (md pk a : ByteArray) (n : USize) (ix : ByteArray) :
    (gatherAlp fill md pk a n ix).size = ix.size / 8 * (if Column.alpF32 a then 4 else 8) := by
  unfold gatherAlp; rw [gatherBytes_size]; split <;> simp_all

theorem small_mod (k : Nat) (h : k ≤ 64) : k % 2 ^ System.Platform.numBits = k :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : k < 2 ^ 32)
    (Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> simp [h])))

theorem toNat_small (k : Nat) (h : k ≤ 64) : (USize.ofNat k).toNat = k :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega) USize.le_size)

/-- **`x@i` answers `m` well-formed elements** of the source's type, for a dense index of `m` longs. -/
theorem gatherColumn_wf {t : QAtomicType} {n : USize} {e : Enc} (hw : Enc.WF t n e)
    (i : ByteArray) {m : USize} (hm : m.toNat = i.size / 8) {e' : Enc}
    (h : gatherColumn t n e m (.bytes i) = some e') : Enc.WF t m e' := by
  unfold gatherColumn at h
  have hz : ¬ i.size < m.toNat * 8 := by omega
  cases e with
  | foR M P =>
    by_cases hc : Column.encodes t = true ∧ M.isEmpty = false <;> cases t <;>
      simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
        Column.encodes, gatherBytes_size, gatherFoR, toNat_small, small_mod] <;> obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := h <;>
      simp [gatherBytes_size, toNat_small, small_mod, hm]
  | enum d o ids =>
    cases t <;> try (exfalso; simp [Enc.WF] at hw; done)
    obtain ⟨-, hl, hle⟩ := id hw
    have key := gatherIds_dict (inRange := fun _ => allBelow n i)
      (g := fun w wo e => gatherPacked n w wo e ids i) hl hle
    simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, foRColumn, Enc.bytesOf]
    split at h <;> cases h <;> simp only [Enc.WF] at *
    · simp_all
    · exact ⟨gatherIds_wf (inRange := fun _ => allBelow n i) (n := n) (ids := ids)
        (db := (gatherIds d o (fun _ => allBelow n i) fun w wo e => gatherPacked n w wo e ids i).1) rfl, key⟩
  | _ => cases t <;>
      simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
        Column.alpEncodes, gatherBits_size, gatherBytes_size, gatherAlp_size, gatherSyms_size, gatherIds_wf,
        toNat_small, small_mod] <;> (try subst h) <;>
      simp_all [gatherBits_size, gatherBytes_size, gatherAlp_size, gatherSyms_size, gatherIds_wf, toNat_small,
        small_mod]

end LeetQ.Rel.KernelWF
