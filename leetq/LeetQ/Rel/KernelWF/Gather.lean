/-
  Totality of the kernels a `Rel` op reads a payload through, under the payload's `Enc.WF`: the facts
  that let `pick`, `Parted.box`, `longBytes` and `gens` drop their `Except`. Each hypothesis is one a
  caller holding an `Arr` already has: `x.wf`, an index `.bytes i` of `i.size / 8` longs.
-/
import QLean.Kernel.Structural
import QLean.Verify.Gather
import QLean.Verify.Raw

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

/-- **`m` elements from `off`, cycling, answer** for every well-formed column but a general list. -/
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
