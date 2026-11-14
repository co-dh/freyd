/-
  `bitRowsOver` read back: bit `j` of row `g` of the answer is the `∃` (`∨`) or `∀` (`∧`) over the positions
  `k` of segment `g` of bit `j` of row `idx[k]` of the matrix. The rule `Bits.comp` and `Bits.ldiv` stand on.
-/
import QLean.Kernel.Reduce
import QLean.Verify.Gather

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify

/-- **`bitRowsOver`, one bit**: for `g` below the segment count and `j < w`, bit `g·w + j` is set iff some
    (`all = false`), resp. every (`all = true`), position `k` of segment `g` (`segRange`) has bit
    `idx[k]·w + j` of `m` set. -/
theorem bitRowsOver_spec (all : Bool) (w : USize) (offs idx m : ByteArray) (g j lo hi : Nat)
    (hg : g < offs.size / 8 - 1) (hj : j < w.toNat) (hs : segRange offs (idx.size / 8) g = (lo, hi)) :
    (Column.bitAt (bitRowsOver all w offs idx m) (g * w.toNat + j) = true ↔
      if all then ∀ k, lo ≤ k → k < hi → Column.bitAt m ((atI64 idx k).toNatClampNeg * w.toNat + j) = true
      else ∃ k, lo ≤ k ∧ k < hi ∧ Column.bitAt m ((atI64 idx k).toNatClampNeg * w.toNat + j) = true) := by
  -- segment `g` is `[lo, hi)`
  have hb : g * w.toNat + j < (offs.size / 8 - 1) * w.toNat := by
    have := Nat.mul_le_mul_right w.toNat (show g + 1 ≤ offs.size / 8 - 1 by omega)
    rw [Nat.succ_mul] at this; omega
  have hq : (g * w.toNat + j) / w.toNat = g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hr : (g * w.toNat + j) % w.toNat = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  unfold bitRowsOver
  rw [bitAt_packOf _ _ _ hb]
  simp only [hq, hr, hs]
  cases all
  · simp only [Bool.false_eq_true, if_false, List.any_eq_true, List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨k, ⟨i, hk, rfl⟩, h⟩; exact ⟨lo + i, by omega, by omega, h⟩
    · rintro ⟨k, h1, h2, h⟩; exact ⟨k, ⟨k - lo, by omega, by omega⟩, h⟩
  · simp only [if_true, List.all_eq_true, List.mem_range', Nat.one_mul]
    constructor
    · intro h k h1 h2; exact h k ⟨k - lo, by omega, by omega⟩
    · rintro h k ⟨i, hk, rfl⟩; exact h _ (by omega) (by omega)

end LeetQ.Rel.Alg
