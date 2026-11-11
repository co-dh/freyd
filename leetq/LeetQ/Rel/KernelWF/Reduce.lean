/-
  Totality and well-formedness of the grade kernel behind `Ops.rank` (`gradeColumn`), and the count
  `razeColumn` answers (`raze_len`). Each `_isSome` names the weakest hypothesis under which the kernel
  body answers; each declining input is a hypothesis.
-/
import LeetQ.Rel.KernelWF.Raze
import QLean.Kernel.Scan
import QLean.Kernel.Search
import QLean.Dep.Table

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Kernel.Order LeetQ.Rel

private theorem toUSize_small {k : Nat} (h : k ≤ 64) : k.toUSize.toNat = k := by
  simp only [Nat.toUSize]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h (by decide)) USize.le_size)

/-! ## Sizes of the grade family -/

/-- `indices` writes one long per index. -/
theorem indices_size (is : List Nat) : (indices is).size = is.length * 8 := by
  simp only [indices]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

/-- `grade` answers one long per element it reads: `n` clamped to what the payload holds. -/
theorem grade_size (k : Scan.Kind) (desc : Bool) (n : USize) (b : ByteArray) :
    (grade k desc n b).size = min n.toNat (k.avail b) * 8 := by
  simp [grade, indices_size]

/-- `invert` answers one long per long of the permutation. -/
theorem invert_size (p : ByteArray) : (invert p).size = p.size / 8 * 8 := by
  simp [invert, indices_size]

theorem ranks_size (k : Scan.Kind) (n : USize) (b : ByteArray) :
    (ranks k n b).size = min n.toNat (k.avail b) * 8 := by
  simp only [ranks, invert_size, grade_size]; omega

theorem gradeSyms_size (desc : Bool) (blob : ByteArray) (offs : Array Nat) :
    (gradeSyms desc blob offs).size = (offs.size - 1) * 8 := by
  simp [gradeSyms, indices_size]

theorem gradeGuid_size (desc : Bool) (b : ByteArray) : (gradeGuid desc b).size = b.size / 16 * 8 := by
  simp [gradeGuid, indices_size]

/-- A kind other than the bitmap's holds a whole element in `width` bytes. -/
private theorem avail_of_ne_bit {k : Scan.Kind} (hk : k ≠ .bit) (b : ByteArray) :
    k.avail b = b.size / k.width := by
  cases k <;> simp_all [Scan.Kind.avail]

private theorem width_pos (k : Scan.Kind) : 0 < k.width ∧ k.width ≤ 8 := by
  cases k <;> simp [Scan.Kind.width]

/-- `n` elements of `width` bytes are all `grade` reads. -/
private theorem min_avail {k : Scan.Kind} (hk : k ≠ .bit) {n : Nat} {b : ByteArray}
    (hb : n * k.width ≤ b.size) : min n (k.avail b) = n := by
  rw [avail_of_ne_bit hk]
  have := (Nat.le_div_iff_mul_le (width_pos k).1).2 hb
  omega

theorem gradeIds_size (desc : Bool) (n : USize) (dict : ByteArray) (dof : Array Nat) (ids : ByteArray) :
    (gradeIds desc n dict dof ids).size = n.toNat * 8 := by
  simp only [gradeIds, grade_size]
  rw [min_avail (by decide)]
  rw [foldl_size ByteArray.size _ 4 (fun _ _ => Column.pushBits_size ..)]; simp [Scan.Kind.width]

/-- The decoded Frame-of-Reference column `gradeFoR`/`ranksFoR` read holds all `n` elements. -/
private theorem min_avail_decode {k : Scan.Kind} (hk : k ≠ .bit) {n : USize}
    (md pk : ByteArray) : min n.toNat (k.avail (Coc.decode k.width.toUSize md pk n)) = n.toNat :=
  min_avail hk (by
    rw [decode_size, toUSize_small (by have := (width_pos k).2; omega)]; exact Nat.le_refl _)

/-! ## `gradeColumn`: `<x`, `>x`, `rank x` -/

/-- **`gradeColumn` answers `n` longs** on a well-formed payload. -/
theorem gradeColumn_wf {t : QAtomicType} {desc rank : Bool} {n : USize} {e v : Enc}
    (hw : Enc.WF t n e) (h : gradeColumn t desc n e rank = some v) :
    Enc.WF .long n v := by
  have key : ∀ b : ByteArray, b.size = n.toNat * 8 → Enc.WF .long n (.bytes b) :=
    fun b hb => wf_bytes (w := 8) (by decide) rfl hb
  unfold gradeColumn at h
  cases rank <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> split at h
  all_goals first
    | (cases h; apply key; simp only [Enc.WF] at hw; simp only [invert_size, gradeSyms_size] <;> omega)
    | (cases h; apply key; simp only [invert_size, gradeIds_size] <;> omega)
    | (cases h; apply key; simp only [Enc.WF] at hw
       simp only [ranks_size, grade_size, Scan.Kind.avail] <;> omega)
    | (obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
       obtain ⟨b', hb', hs⟩ := bytesOf_size (w := 16) (by decide) rfl hw
       rw [hb] at hb'; cases hb'
       apply key; simp only [invert_size, gradeGuid_size, hs] <;> omega)
    | (split at h
       · cases h
       rename_i k hk
       split at h
       · cases h
       rename_i hbit
       have hk' : k ≠ .bit := fun e => by simp [e] at hbit
       split at h
       · cases h; apply key
         simp only [ranksFoR, gradeFoR, ranks_size, grade_size, min_avail_decode hk']
       · split at h
         · rename_i b hb
           split at h
           · cases h
           rename_i hlt
           cases h; apply key
           simp only [ranks_size, grade_size, min_avail hk' (Nat.le_of_not_lt hlt)]
         · cases h)

/-- **`gradeColumn` answers** every well-formed payload, except a general list's: `orderKind` has no
    key for it. -/
theorem gradeColumn_isSome {t : QAtomicType} {desc rank : Bool} {n : USize} {e : Enc}
    (hw : Enc.WF t n e) (hg : t ≠ .general) :
    (gradeColumn t desc n e rank).isSome := by
  unfold gradeColumn
  cases rank <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split
  all_goals first
    | rfl
    | (obtain ⟨b, hb, -⟩ := bytesOf_size (w := 16) (by decide) rfl hw; simp [hb])
    | (split
       · rename_i hk
         rcases orderKind_eq_none.1 hk with rfl | rfl | rfl
         · cases e <;> simp_all [Enc.WF, QAtomicType.width]
         · simp_all
         · exact absurd rfl hg
       rename_i k hk
       split
       · rename_i hbit
         have : t = .boolean := by cases t <;> simp_all [orderKind]
         subst this
         cases e <;> simp_all [Enc.WF]
       rename_i hbit
       have hk' : k ≠ .bit := fun e => by simp [e] at hbit
       have hwk : t.width = some k.width := by
         cases t <;> simp [orderKind] at hk <;> subst hk <;> rfl
       have htb : t ≠ .boolean := by rintro rfl; simp [orderKind] at hk; exact hk' hk.symm
       split
       · rfl
       · obtain ⟨b, hb, hs⟩ := bytesOf_size htb hwk hw
         simp [hb, hs])

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Ops

open QLean QLean.Dep QLean.Kernel

variable {t : QAtomicType}

/-- `rank x` = `<<x`, key kept: the place of each element in the ascending order, on the domain
    `gradeColumn` orders by value (every atom but a general list, the witness `hg`). -/
def rank {n : USize} (R : Arr t n) (hg : t ≠ .general) : Arr .long n :=
  Arr.mk ((gradeColumn t false n R.enc (rank := true)).get (KernelWF.gradeColumn_isSome R.wf hg))
    (KernelWF.gradeColumn_wf R.wf (Option.some_get _).symm)

end LeetQ.Rel.Ops
