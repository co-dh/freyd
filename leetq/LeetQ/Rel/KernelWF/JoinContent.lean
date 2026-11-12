/-
  The long arithmetic `join` runs on its count and index columns, read back: `add`/`sub` of two longs
  below `2^63`, `sums` as the running total, and `classSizes` as the rows of each class.
-/
import LeetQ.Rel.KernelWF.JoinSpec
import QLean.Verify.Chain
import QLean.Verify.ScanOver
import QLean.Verify.BinWin

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-- A long below `2^63` reads as its own value at `i64`. -/
theorem toInt64_toInt {x : UInt64} (hx : x.toNat < 2 ^ 63) : x.toInt64.toInt = x.toNat :=
  calc x.toInt64.toInt = (UInt64.ofNat x.toNat).toInt64.toInt := by rw [UInt64.ofNat_toNat]
    _ = x.toNat := Int64.toInt_ofNat_of_lt hx

/-- An `Int64` whose value is the natural `q < 2^63` is `Int64.ofNat q`. -/
theorem int64_eq_ofNat {a : Int64} {q : Nat} (hq : q < 2 ^ 63) (h : a.toInt = q) : a = Int64.ofNat q :=
  Int64.toInt_inj.1 (by rw [h, Int64.toInt_ofNat_of_lt hq])

/-- **`valStep` of `+` and `-` on two longs below `2^63`** is the natural sum, and the natural difference
    where it is not negative: neither operand is q's null `0N`, and nothing wraps. -/
theorem valStep_add_sub {x y : UInt64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    (x.toNat + y.toNat < 2 ^ 63 →
      Ew.valStep Ew.add Ew.i64 nul.toUInt64 x y = UInt64.ofNat (x.toNat + y.toNat)) ∧
    (y.toNat ≤ x.toNat →
      Ew.valStep Ew.sub Ew.i64 nul.toUInt64 x y = UInt64.ofNat (x.toNat - y.toNat)) := by
  have ex := toInt64_toInt hx; have ey := toInt64_toInt hy
  have hxn : x.toInt64 ≠ Int64.minValue := fun e => by rw [e] at ex; simp at ex
  have hyn : y.toInt64 ≠ Int64.minValue := fun e => by rw [e] at ey; simp at ey
  have hnul : (nul.toUInt64).toInt64 = Int64.minValue := rfl
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.add, Ew.sub, hnul]
  simp only [↓reduceIte]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [if_neg (by simp; exact ⟨hxn, hyn⟩)]
  · rw [int64_eq_ofNat (a := x.toInt64 + y.toInt64) h
      (by rw [Int64.toInt_add, ex, ey]; simp only [Int.bmod]; split <;> omega)]; rfl
  · rw [int64_eq_ofNat (a := x.toInt64 - y.toInt64) (q := x.toNat - y.toNat) (by omega)
      (by rw [Int64.toInt_sub, ex, ey]; simp only [Int.bmod]; split <;> omega)]; rfl

/-- `Ew.val` on longs at `vv`, element `i` below the count: `valStep` of the two operands' longs `i`. -/
theorem val_vv_get (op : UInt8) (a b : ByteArray) (n : USize) {i : Nat} (hi : i < n.toNat) :
    Column.bitsAt (Kernel.Ew.val op Ew.i64 Ew.vv nul a b n) (i * 8) 8 =
      Ew.valStep op Ew.i64 nul.toUInt64 (Column.bitsAt a (i * 8) 8) (Column.bitsAt b (i * 8) 8) := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have h := congrArg (·[i]?) (elemsW_val op Ew.i64 Ew.vv nul a b n)
  have hs : (Kernel.Ew.val op Ew.i64 Ew.vv nul a b n).size / 8 = n.toNat := by
    have := len_val op Ew.vv a b n; simpa [len] using this
  simp only [elemsW, hw, hs, List.getElem?_map, List.getElem?_range, hi, Option.map_some,
    Option.some.injEq] at h
  rw [h]
  simp (config := {decide := true}) only [Ew.shapeIdx, Ew.elem, hw, ↓reduceIte]
  generalize Ew.valStep op Ew.i64 nul.toUInt64 _ _ = v
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ (8 * 8) from v.toNat_lt), UInt64.ofNat_toNat]

/-- **`add n a b`'s long `i`** is the sum of the two longs `i`, all three below `2^63`. -/
theorem add_get {n : USize} {a b : ByteArray} {i : Nat} (hi : i < n.toNat) (h : (Column.bitsAt a (i * 8) 8).toNat + (Column.bitsAt b (i * 8) 8).toNat < 2 ^ 63) :
    (Column.bitsAt (add n a b) (i * 8) 8).toNat = (Column.bitsAt a (i * 8) 8).toNat + (Column.bitsAt b (i * 8) 8).toNat := by
  unfold add; rw [val_vv_get _ _ _ _ hi, ((valStep_add_sub (by omega) (by omega)).1 h), UInt64.toNat_ofNat_of_lt' (Nat.lt_trans h (by decide))]

/-- **`sub n a b`'s long `i`** is the difference of the two longs `i`, both below `2^63`, `b`'s no greater. -/
theorem sub_get {n : USize} {a b : ByteArray} {i : Nat} (hi : i < n.toNat) (ha : (Column.bitsAt a (i * 8) 8).toNat < 2 ^ 63)
    (h : (Column.bitsAt b (i * 8) 8).toNat ≤ (Column.bitsAt a (i * 8) 8).toNat) : (Column.bitsAt (sub n a b) (i * 8) 8).toNat = (Column.bitsAt a (i * 8) 8).toNat - (Column.bitsAt b (i * 8) 8).toNat := by
  unfold sub; rw [val_vv_get _ _ _ _ hi, ((valStep_add_sub ha (by omega)).2 h),
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_trans ha (by decide)))]

/-- The `sums` fold over longs whose running total stays below `2^63`: no element is `0N`, nothing
    wraps, and the accumulator is the natural total. -/
theorem foldl_sums (l : List UInt64) (s : Nat) (h : s + (l.map UInt64.toNat).sum < 2 ^ 63) :
    l.foldl (fun a x => if Scan.Kind.isNull .i64 x then a else a + Scan.Kind.signed .i64 x) (Int64.ofNat s) =
      Int64.ofNat (s + (l.map UInt64.toNat).sum) := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have ex := toInt64_toInt (x := x) (by omega)
    have hn : Scan.Kind.isNull .i64 x = false := by
      simp only [Scan.Kind.isNull, beq_eq_false_iff_ne]
      exact fun e => by rw [e] at ex; simp at ex
    rw [List.foldl_cons, hn, if_neg Bool.false_ne_true, Scan.Kind.signed,
      int64_eq_ofNat (a := Int64.ofNat s + x.toInt64) (q := s + x.toNat) (by omega) (by
        rw [Int64.toInt_add, ex, Int64.toInt_ofNat_of_lt (by omega)]; simp only [Int.bmod]; split <;> omega),
      ih _ (by omega), Nat.add_assoc]

/-- **`sums n b`'s long `j`** is the total of `b`'s longs `0 … j`, `j` below `n` and `b`'s count, that
    total below `2^63`. -/
theorem sums_get {n : USize} {b : ByteArray} {j : Nat} (hj : j < n.toNat) (hb : j < len b)
    (h : ((List.range (j + 1)).map fun i => (Column.bitsAt b (i * 8) 8).toNat).sum < 2 ^ 63) :
    (Column.bitsAt (sums n b) (j * 8) 8).toNat = ((List.range (j + 1)).map fun i => (Column.bitsAt b (i * 8) 8).toNat).sum := by
  have hm : j < min n.toNat (Scan.Kind.avail .i64 b) := by
    simp only [Scan.Kind.avail, Scan.Kind.width]; simp only [len] at hb; omega
  have hf : sums n b = Scan.scanOf (min n.toNat (Scan.Kind.avail .i64 b)) 8 (Scan.Kind.bitsAt .i64 b)
      (Scan.Kind.isNull .i64) (0 : Int64) (fun a x => a + Scan.Kind.signed .i64 x) (Scan.narrow 8) := rfl
  rw [hf, scanOf_get _ 8 (by decide) _ _ _ _ _ j hm]
  have hl : (List.range (j + 1)).map (Scan.Kind.bitsAt .i64 b) = (List.range (j + 1)).map fun i => Column.bitsAt b (i * 8) 8 := rfl
  have h' : 0 + (((List.range (j + 1)).map fun i => Column.bitsAt b (i * 8) 8).map UInt64.toNat).sum < 2 ^ 63 := by
    rw [List.map_map]; exact (Nat.zero_add _).symm ▸ h
  rw [hl, show (0 : Int64) = Int64.ofNat 0 from rfl, foldl_sums _ 0 h', Nat.zero_add, List.map_map]
  simp only [Scan.narrow, show (8 = 4) = False by decide, ↓reduceIte]
  rw [show (Int64.ofNat _).toUInt64 = UInt64.ofNat _ from rfl]
  have hS : (List.map (UInt64.toNat ∘ fun i => Column.bitsAt b (i * 8) 8) (List.range (j + 1))).sum =
      ((List.range (j + 1)).map fun i => (Column.bitsAt b (i * 8) 8).toNat).sum := rfl
  rw [hS]; revert h; generalize ((List.range (j + 1)).map fun i => (Column.bitsAt b (i * 8) 8).toNat).sum = S; intro h
  rw [UInt64.toNat_ofNat_of_lt' (show S < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show S < 2 ^ (8 * 8) by omega),
    UInt64.toNat_ofNat_of_lt' (show S < 2 ^ 64 by omega)]

/-- A class count's width is a lane: at most `64` bits. -/
theorem idWidthOf_le (n : Nat) : Column.idWidthOf n ≤ 64 := by
  rcases laneWidth_cases (Column.widthFor (n - 1)) with h | h | h | h | h | h | h | h <;>
    simp only [Column.idWidthOf, h] <;> omega

/-- **`classSizes n g`, read back**: one long per class of `g` (`len g.2` of them), the count of the
    first `n` ids of `g.1`, read at their width `idWidthOf (len g.2)`, equal to that class. -/
theorem classSizes_ids (n : USize) (g : ByteArray × ByteArray) (hg : len g.2 < USize.size) :
    ids (classSizes n g) = (List.range (len g.2)).map fun c =>
      (idsW (Column.idWidthOf (len g.2)) n.toNat g.1).countP (· == c) := by
  unfold classSizes longCount
  simp only [need, dif_pos hg]
  rw [groupSizes_spec, USize.toNat_ofNat_of_lt' hg, lane_toNat (idWidthOf_le _)]

#print axioms add_get
#print axioms sub_get
#print axioms sums_get
#print axioms classSizes_ids

end LeetQ.Rel.Alg
