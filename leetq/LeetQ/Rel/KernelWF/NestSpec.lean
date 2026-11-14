/-
  The slice columns `inits` and `tails` hand `nest`, read back: a `gather`ed start (`longsN`) and a `gather`ed
  start plus a rank (`valCol add`), each as an `Int`.
-/
import LeetQ.Rel.KernelWF.PickRow
import LeetQ.Rel.KernelWF.JoinContent

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-- **A gathered long, as an `Int`**: row `d` of `longsN` over `gather 8 a i` is `a`'s long at `i`'s row `d`,
    that long below `2^63`. -/
theorem gather_longsN_toInt {m : USize} {a i : ByteArray} (hh : m.toNat ≤ len (gather 8 a i)) {d : Nat}
    (hd : d < m.toNat) (hl : len i = m.toNat) (hs : (Column.bitsAt i (d * 8) 8).toNat < len a)
    (h63 : (Column.bitsAt a ((Column.bitsAt i (d * 8) 8).toNat * 8) 8).toNat < 2 ^ 63) :
    ((longsN m (gather 8 a i) hh).get ⟨d, hd⟩).toInt =
      ((Column.bitsAt a ((Column.bitsAt i (d * 8) 8).toNat * 8) 8).toNat : Int) := by
  rw [longsN_get, gather8_get (Nat.lt_of_lt_of_eq hd hl.symm) hs]; exact toInt64_toInt h63

/-- **A gathered long plus a rank, as an `Int`**: row `d` of `valCol add` over `gather 8 a i` and `r` is `a`'s
    long at `i`'s row `d` plus `r`'s long `d`, the sum below `2^63`. -/
theorem gather_add_toInt {m : USize} {a i r : ByteArray} {d : Nat} (hd : d < m.toNat) (hl : len i = m.toNat)
    (hs : (Column.bitsAt i (d * 8) 8).toNat < len a)
    (h63 : (Column.bitsAt a ((Column.bitsAt i (d * 8) 8).toNat * 8) 8).toNat + (Column.bitsAt r (d * 8) 8).toNat <
      2 ^ 63) :
    ((valCol (n := m) Ew.add Ew.vv (gather 8 a i) r).get ⟨d, hd⟩).toInt =
      (((Column.bitsAt a ((Column.bitsAt i (d * 8) 8).toNat * 8) 8).toNat + (Column.bitsAt r (d * 8) 8).toNat : Nat) :
        Int) := by
  have hg := gather8_get (src := a) (Nat.lt_of_lt_of_eq hd hl.symm) hs
  have hb : (Column.bitsAt (gather 8 a i) (d * 8) 8).toNat + (Column.bitsAt r (d * 8) 8).toNat < 2 ^ 63 := by
    rw [hg]; exact h63
  rw [Arr.get_long_bytes _ rfl]
  show (Column.bitsAt (add m (gather 8 a i) r) (d * 8) 8).toInt64.toInt = _
  rw [toInt64_toInt (by rw [add_get hd hb]; exact hb), add_get hd hb, hg]

end LeetQ.Rel.Alg

#print axioms LeetQ.Rel.Alg.gather_longsN_toInt
#print axioms LeetQ.Rel.Alg.gather_add_toInt
