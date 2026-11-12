/-
  The lane facts every code spec reads: which layout `laneKind` names, a lane width as a `USize`, a code
  at a byte lane as its little-endian field, and a payload that holds all its ids.
-/
import LeetQ.Rel.Code
import QLean.Verify.Ids
import QLean.Verify.Encoding

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel LeetQ.Rel

/-- A lane `laneKind` names is the bitmap at `1`, or an integral byte layout at `8 ×` its width. -/
theorem laneKind_some {w : Nat} {k : Scan.Kind} (h : laneKind w = some k) :
    (k = .bit ∧ w = 1) ∨
      (k ≠ .bit ∧ w = 8 * k.width ∧ (k.width = 1 ∨ k.width = 2 ∨ k.width = 4 ∨ k.width = 8) ∧
        (k = .u8 ∨ k = .c8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64)) := by
  unfold laneKind at h
  split at h <;> (try cases h) <;> simp [Scan.Kind.width]

/-- A lane width as a `USize` keeps its value. -/
theorem lane_toNat {w : Nat} (hw : w ≤ 64) : w.toUSize.toNat = w := KernelWF.toNat_small w hw

/-- At a whole-byte lane `8c` a code is the `c` bytes from `c·i` (`resAt_lane`). -/
theorem idAt_lane (b : ByteArray) {c : Nat} (hc : c ≤ 8) (i : Nat) :
    Column.idAt b (8 * c) i = (Column.bitsAt b (i * c) c).toNat := by
  rw [Column.idAt, Verify.resAt_lane b c i hc, Nat.mul_comm]

/-- A payload holding `n` codes at `w ≠ 0` bits holds all of them: `idsCap` clamps nothing. -/
theorem idsCap_full {b : ByteArray} {w n : Nat} (hw : 0 < w) (hs : w * n ≤ 8 * b.size) :
    Column.idsCap b w n = n := by
  unfold Column.idsCap
  rw [if_neg (by omega), Nat.min_eq_left ((Nat.le_div_iff_mul_le hw).2 (by rw [Nat.mul_comm]; omega))]

end LeetQ.Rel.Alg
