/-
  Kernel content the primitive read-backs of `RepPrim` use: `Ew.val lesser` on longs is their minimum.
-/
import LeetQ.Rel.RepArith
import LeetQ.Rel.KernelWF.JoinContent

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep

/-- **`Ew.val lesser` on longs, long `i`**: the lesser of the two longs `i`, both below `2^63`. -/
theorem lesser_get {n : USize} {a b : ByteArray} {i : Nat} (hi : i < n.toNat)
    (ha : (Column.bitsAt a (i * 8) 8).toNat < 2 ^ 63) (hb : (Column.bitsAt b (i * 8) 8).toNat < 2 ^ 63) :
    (Column.bitsAt (Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul a b n) (i * 8) 8).toNat =
      min (Column.bitsAt a (i * 8) 8).toNat (Column.bitsAt b (i * 8) 8).toNat := by
  rw [val_vv_get _ _ _ _ hi]
  generalize Column.bitsAt a (i * 8) 8 = x at ha ⊢
  generalize Column.bitsAt b (i * 8) 8 = y at hb ⊢
  have h := valStep_i64 Ew.lesser x.toInt64 y.toInt64
  rw [show x.toInt64.toUInt64 = x from rfl, show y.toInt64.toUInt64 = y from rfl] at h
  rw [h]
  have hx := toInt64_toInt ha
  have hy := toInt64_toInt hb
  unfold Ew.intStep
  simp only [show (Ew.lesser == Ew.add) = false from rfl, show (Ew.lesser == Ew.sub) = false from rfl,
    show (Ew.lesser == Ew.mul) = false from rfl, show (Ew.lesser == Ew.fill) = false from rfl,
    show (Ew.lesser == Ew.lesser) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i h'
    have := Int64.lt_iff_toInt_lt.1 h'
    show x.toNat = _
    omega
  · rename_i h'
    have := mt Int64.lt_iff_toInt_lt.2 h'
    show y.toNat = _
    omega

#print axioms lesser_get

end LeetQ.Rel.KernelWF
