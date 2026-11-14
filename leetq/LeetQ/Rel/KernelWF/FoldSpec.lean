/-
  The kernels `foldRows` reads round `k`'s elements with, read back: `slicesOf`'s start and count at a row,
  the rows whose count is greater than `k` (`whereBits` of `Ew.cmp gt`), and `Ew.val sub` of a long less a
  constant.
-/
import LeetQ.Rel.KernelWF.SliceSpec
import LeetQ.Rel.KernelWF.RowsSpec
import LeetQ.Rel.KernelWF.MemberSpec
import LeetQ.Rel.KernelWF.SortSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

open SliceN

/-- **Row `i` of an array side, read at its slice**: start plus count within the payload, the row as long as
    the count, its element `j` the payload's at the start plus `j`. -/
theorem slicesOf_row {B : Obj} {n : USize} (x : Vals (.arr B) n) (hp : x.1.toNat < 2 ^ 63) {i : Nat}
    (hi : i < n.toNat) :
    (Column.bitsAt (slicesOf x).1 (i * 8) 8).toNat + (Column.bitsAt (slicesOf x).2 (i * 8) 8).toNat ≤ x.1.toNat ∧
      (Vals.row x ⟨i, hi⟩).length = (Column.bitsAt (slicesOf x).2 (i * 8) 8).toNat ∧
      ∀ j (hj : j < (Vals.row x ⟨i, hi⟩).length)
        (hl : (Column.bitsAt (slicesOf x).1 (i * 8) 8).toNat + j < x.1.toNat),
        (Vals.row x ⟨i, hi⟩)[j] = Vals.row x.2.2.2 ⟨_, hl⟩ := by
  obtain ⟨hL, hC⟩ := slicesOf_get x hp hi
  have hH : sH(x, i, hi) ≤ x.1.toNat := Nat.min_le_right _ _
  refine ⟨by rw [hL, hC]; omega, by rw [arr_row, hC, List.length_map, List.length_range], fun j hj hl => ?_⟩
  rw [List.getElem_of_eq (arr_row x ⟨i, hi⟩), List.getElem_map, List.getElem_range,
    dif_pos (by rw [← hL]; exact hl)]
  exact congrArg (Vals.row x.2.2.2) (Fin.ext (show _ + j = _ + j by rw [hL]))

/-- **`whereBits` of `Ew.cmp gt` against the constant `k`, read back**: the ascending positions below `n`
    whose long is greater than `k`, every long and `k` below `2^63`. -/
theorem whereGt_ids (n : USize) (c : ByteArray) {k : Nat} (hk : k < 2 ^ 63)
    (hc : ∀ i < n.toNat, (Column.bitsAt c (i * 8) 8).toNat < 2 ^ 63) :
    ids (whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va c (one k.toUInt64) n)) =
      (List.range n.toNat).filter fun i => decide (k < (Column.bitsAt c (i * 8) 8).toNat) := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have hs : ∀ i, Ew.shapeIdx Ew.va i = (i, 0) := fun i => by simp (config := {decide := true}) [Ew.shapeIdx]
  have ek : (k.toUInt64).toInt64.toInt = k :=
    (toInt64_toInt (x := k.toUInt64) (by rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hk (by decide))]; exact hk)).trans
      (by rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hk (by decide))])
  rw [(whereBits_ids n _).1]
  refine List.filter_congr fun i hi => ?_
  have hi := List.mem_range.1 hi
  rw [(Verify.cmp_bitAt _ _ _ _ _ n).2 i (by omega)]
  simp only [Ew.elem, hw, hs, decide_eq_true hi, Bool.true_and, Nat.zero_mul, LeetQ.Rel.bitsAt_one]
  have ex := toInt64_toInt (hc i hi)
  generalize Column.bitsAt c (i * 8) 8 = x at ex ⊢
  simp (config := {decide := true}) only [Ew.cmpStep, Ew.signed, ↓reduceIte]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  show compareOfLessAndEq _ _ = _ ↔ _
  unfold compareOfLessAndEq
  by_cases h1 : x.toInt64 < (k.toUInt64).toInt64
  · rw [if_pos h1]; rw [Int64.lt_iff_toInt_lt, ex, ek] at h1
    exact ⟨fun h => (by cases h), fun h => absurd h (by omega)⟩
  · rw [if_neg h1]; rw [Int64.lt_iff_toInt_lt, ex, ek] at h1
    by_cases h2 : x.toInt64 = (k.toUInt64).toInt64
    · rw [if_pos h2]
      have e := congrArg Int64.toInt h2
      rw [ex, ek] at e
      exact ⟨fun h => (by cases h), fun h => absurd h (by omega)⟩
    · rw [if_neg h2]
      have e : x.toInt64.toInt ≠ (k.toUInt64).toInt64.toInt := fun e => h2 (Int64.toInt_inj.1 e)
      rw [ex, ek] at e
      exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- **`Ew.val sub` of a long less the constant `v`**, at element `q` below the count: the natural difference,
    the long below `2^63` and not below `v`. -/
theorem subConst_get {g : ByteArray} {m : USize} {v q : Nat} (hq : q < m.toNat)
    (hg : (Column.bitsAt g (q * 8) 8).toNat < 2 ^ 63) (hv : v ≤ (Column.bitsAt g (q * 8) 8).toNat) :
    (Column.bitsAt (Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul g (one v.toUInt64) m) (q * 8) 8).toNat =
      (Column.bitsAt g (q * 8) 8).toNat - v := by
  have ev : (v.toUInt64).toNat = v := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (Nat.lt_of_le_of_lt hv hg) (by decide))
  rw [val_va_get _ _ _ _ hq, LeetQ.Rel.bitsAt_one, (valStep_add_sub hg (by rw [ev]; omega)).2 (by rw [ev]; exact hv), ev]
  exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_trans hg (by decide)))

end LeetQ.Rel.Alg

#print axioms LeetQ.Rel.Alg.slicesOf_get
#print axioms LeetQ.Rel.Alg.slicesOf_row
#print axioms LeetQ.Rel.Alg.whereGt_ids
#print axioms LeetQ.Rel.Alg.subConst_get
