/-
  `bagify`'s two grades read back: `gradeColumn .long false` lists the rows in a stable ascending sort by
  value, and the grade of `Code.ofLongs` of longs below `2^63` lists them in a stable sort by those longs — at
  row numbers, each row's cells in one block, rows ascending, the incoming order kept inside a block.
-/
import LeetQ.Rel.KernelWF.PlaceSpec
import LeetQ.Rel.KernelWF.PickRow
import LeetQ.Rel.KernelWF.CodesRec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- The `long` key `Order.keyAt .i64` sorts by, read as a number: `2^63` above the value. -/
theorem key_i64 (a : Int64) : ((a.toUInt64 ^^^ 0x8000000000000000).toNat : Int) = a.toInt + 2 ^ 63 := by
  rw [UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl]
  have hlt := a.toUInt64.toNat_lt
  have ht : a.toInt = if 2 * a.toUInt64.toNat < 2 ^ 64 then (a.toUInt64.toNat : Int)
      else (a.toUInt64.toNat : Int) - 2 ^ 64 := by
    rw [Int64.toInt, BitVec.toInt_eq_toNat_cond]; rfl
  rw [ht]
  by_cases h : a.toUInt64.toNat < 2 ^ 63
  · rw [xor_pow63 h, if_pos (by omega)]; omega
  · obtain ⟨y, hy, hx⟩ : ∃ y, y < 2 ^ 63 ∧ a.toUInt64.toNat = y ^^^ 2 ^ 63 :=
      ⟨a.toUInt64.toNat - 2 ^ 63, by omega, by rw [xor_pow63 (by omega)]; omega⟩
    rw [if_neg (by omega), hx, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, xor_pow63 hy]; omega

/-- **`Order.grade .i64` ascending is a stable sort by key**: every row below the count once, each before every
    later row of a greater key and before every later tie. -/
theorem grade_i64 (n : USize) (B : ByteArray) :
    (ids (Order.grade .i64 false n B)).Perm (List.range (min n.toNat (len B))) ∧
      (ids (Order.grade .i64 false n B)).Pairwise fun i j =>
        (Order.keyAt .i64 B i).toNat < (Order.keyAt .i64 B j).toNat ∨
          ((Order.keyAt .i64 B i).toNat = (Order.keyAt .i64 B j).toNat ∧ i < j) := by
  obtain ⟨hperm, hsort⟩ := grade_spec .i64 false n B
  refine ⟨hperm, hsort.imp fun {i j} ⟨h1, h2⟩ => ?_⟩
  simp only [keyOrd, Bool.false_eq_true, ↓reduceIte] at h1 h2
  rcases UInt64.lt_or_eq_of_le h1 with hl | he
  · exact .inl (UInt64.lt_iff_toNat_lt.1 hl)
  · exact .inr ⟨congrArg UInt64.toNat he, h2 (by rw [he]; exact UInt64.le_refl _)⟩

/-- `gradeColumn` at `long` is the kernel's `grade` (or `ranks`) over the column's dense payload, on either
    encoding. -/
theorem gradeColumn_long {n : USize} (x : Arr .long n) (rank : Bool) :
    gradeColumn .long false n x.enc rank = some (.bytes
      (if rank then Order.ranks .i64 n (longsOf x) else Order.grade .i64 false n (longsOf x))) := by
  rcases long_cases x.wf with ⟨b, hb⟩ | ⟨M, P, hb⟩
  · have hs : b.size / 8 = n.toNat := Arr.n_long_bytes x hb
    have hl : longsOf x = b := by unfold longsOf; simp only [hb, longBytes]; rfl
    rw [hl]
    unfold gradeColumn
    simp only [hb, orderKind, Enc.bytesOf]
    rw [if_neg (by decide), if_neg (by simp only [Scan.Kind.width]; omega)]
  · have hl : longsOf x = Coc.decode 8 M P n := by unfold longsOf; simp only [hb, longBytes]; rfl
    rw [hl]
    unfold gradeColumn
    simp only [hb, orderKind]
    rw [if_neg (by decide)]
    cases rank <;> rfl

/-- **`gradeColumn .long` ascending, read back**: the grade lists every row below the count once, each before
    every later row of a greater value and before every later tie — q's `iasc`, a stable ascending sort, null
    `0N` (the least `Int64`) first. -/
theorem grade_long {n : USize} (x : Arr .long n) :
    (ids (Order.grade .i64 false n (longsOf x))).Perm (List.range n.toNat) ∧
      (ids (Order.grade .i64 false n (longsOf x))).Pairwise fun i j => ∀ (hi : i < n.toNat) (hj : j < n.toNat),
        x.get ⟨i, hi⟩ < x.get ⟨j, hj⟩ ∨ (x.get ⟨i, hi⟩ = x.get ⟨j, hj⟩ ∧ i < j) := by
  obtain ⟨hp, hs⟩ := grade_i64 n (longsOf x)
  rw [len_longsOf, Nat.min_self] at hp
  refine ⟨hp, hs.imp fun {i j} h hi hj => ?_⟩
  have hv : ∀ k (hk : k < n.toNat),
      ((Order.keyAt .i64 (longsOf x) k).toNat : Int) = (x.get ⟨k, hk⟩).toInt + 2 ^ 63 := fun k hk => by
    rw [← key_i64, ← longsOf_get x hk]; rfl
  have e1 := hv i hi; have e2 := hv j hj
  simp only [Int64.lt_iff_toInt_lt, ← Int64.toInt_inj]
  omega

/-- **The grade of `Code.ofLongs b`, `b`'s longs below `2^63`, is a stable sort by them**: every position of
    `b` once, each before every later position of a greater long and before every later tie — at row numbers,
    each row's positions in one block, rows ascending, the incoming order kept inside a block. -/
theorem grade_ofLongs (b : ByteArray) (hN : len b < USize.size)
    (h63 : ∀ i, i < len b → (Column.bitsAt b (i * 8) 8).toNat < 2 ^ 63) :
    (ids (Code.ofLongs b).grade).Perm (List.range (len b)) ∧
      (ids (Code.ofLongs b).grade).Pairwise fun i j =>
        (Column.bitsAt b (i * 8) 8).toNat < (Column.bitsAt b (j * 8) 8).toNat ∨
          ((Column.bitsAt b (i * 8) 8).toNat = (Column.bitsAt b (j * 8) 8).toNat ∧ i < j) := by
  have hm : ((len b).toUSize).toNat = len b := USize.toNat_ofNat_of_lt' hN
  have hc : Code.ofLongs b = ⟨64, (len b).toUSize, 2 ^ 64, b⟩ := by
    unfold Code.ofLongs longCount need; rw [dif_pos hN]
  have hg : (Code.ofLongs b).grade = Order.grade .i64 false (len b).toUSize b := by rw [hc]; rfl
  obtain ⟨hp, hs⟩ := grade_i64 (len b).toUSize b
  rw [hm, Nat.min_self] at hp
  rw [← hg] at hp hs
  have hkey : ∀ i, i < len b → (Order.keyAt .i64 b i).toNat = 2 ^ 63 + (Column.bitsAt b (i * 8) 8).toNat := by
    intro i hi
    show (Column.bitsAt b (i * 8) 8 ^^^ 0x8000000000000000).toNat = _
    rw [UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl]
    exact xor_pow63 (h63 i hi)
  refine ⟨hp, hs.imp_of_mem fun {i j} hi hj h => ?_⟩
  rw [hkey i (List.mem_range.1 (hp.mem_iff.1 hi)), hkey j (List.mem_range.1 (hp.mem_iff.1 hj))] at h
  omega

#print axioms key_i64
#print axioms grade_i64
#print axioms gradeColumn_long
#print axioms grade_long
#print axioms grade_ofLongs

end LeetQ.Rel.Alg
