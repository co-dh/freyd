/-
  `rep` of `mem` (`∋`) and `num`: each executable op read in `Rel(Set)`, as `RepOps` does the first group.
-/
import LeetQ.Rel.Rep
import LeetQ.Rel.KernelWF.SliceSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-! ## `mem`: each array to each of its elements -/

section Mem

variable {B : Obj}

open Alg.SliceN

/-- **`rep (mem X) xs x ↔ xs is a cell of X ∧ x ∈ xs`**: `∋` on the arrays `X`, read in `Rel(Set)` as membership
    of the cell's elements (`slicesOf_copies`: each copy `mem` makes is an element of a cell, each element a copy).
    Hypotheses: `Vals.PickFits` of `X` at every row (the values `mem` picks) and at each row repeated once per
    element (the keys `mem` picks, each a copy of its cell). -/
theorem rep_mem {n : USize} (X : Vals (.arr B) n) (hv : Vals.PickFits (.arr B) X (List.range n.toNat))
    (hk : Vals.PickFits (.arr B) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    (xs : (Obj.arr B).El) (x : B.El) :
    rep (Alg.mem X) xs x ↔ (∃ i, X.row i = xs) ∧ x ∈ xs := by
  have hEU := (slicesOf_copies X hv).1
  have hkf := (copies_rows X hv).symm ▸ hk
  have hvf := (copies_pos X hv).symm ▸ (pickFits_payload X hv).2
  have hle : ∀ r (hr : r < n.toNat), sH(X, r, hr) ≤ X.1.toNat := fun _ _ => Nat.min_le_right _ _
  rw [rep_apply]
  simp only [Alg.mem, expand, need]
  rw [dif_pos hEU]
  simp only [Rel.Holds]
  constructor
  · rintro ⟨t, hkey, hval⟩
    have ht : t.1 < len (expandBytes 8 0 (tilLongs n) (slicesOf X).2) :=
      Nat.lt_of_lt_of_eq t.2 (USize.toNat_ofNat_of_lt' hEU)
    obtain ⟨r, hr, j, hj, e1, e2⟩ := copy_row X hv ht
    have hrj : sL(X, r, hr) + j < X.1.toNat := by have := hle r hr; omega
    rw [pick_row (.arr B) X _ _ _ hkf t, dif_pos (by rw [e1]; exact hr)] at hkey
    rw [pick_row B X.2.2.2 _ _ _ hvf t, dif_pos (by rw [e2]; exact hrj)] at hval
    have hkey2 : X.row ⟨r, hr⟩ = xs := by rw [← hkey]; exact congrArg X.row (Fin.ext e1.symm)
    have hval2 : X.2.2.2.row ⟨_, hrj⟩ = x := by rw [← hval]; exact congrArg X.2.2.2.row (Fin.ext e2.symm)
    subst hkey2 hval2
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [arr_row]
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, by rw [dif_pos hrj]⟩
  · rintro ⟨⟨⟨r, hr⟩, rfl⟩, hx⟩
    rw [arr_row] at hx
    obtain ⟨j, hj, hjx⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hj
    have hrj : sL(X, r, hr) + j < X.1.toNat := by have := hle r hr; omega
    rw [dif_pos hrj] at hjx
    obtain ⟨z, hz, e1, e2⟩ := row_copy X hv hr hj
    have hz' : z < (len (expandBytes 8 0 (tilLongs n) (slicesOf X).2)).toUSize.toNat := by
      rw [USize.toNat_ofNat_of_lt' hEU]; exact hz
    refine ⟨⟨z, hz'⟩, ?_, ?_⟩
    · rw [pick_row (.arr B) X _ _ _ hkf ⟨z, hz'⟩, dif_pos (by rw [e1]; exact hr)]
      exact congrArg X.row (Fin.ext e1)
    · rw [pick_row B X.2.2.2 _ _ _ hvf ⟨z, hz'⟩, dif_pos (by rw [e2]; exact hrj), ← hjx]
      exact congrArg X.2.2.2.row (Fin.ext e2)

end Mem

/-! ## `num`: the rows numbered from `k` -/

/-- **`rep (num R k) a y ↔ ∃ i, a = k + i ∧ R.val[i] = y`**: row `i` of `R` keyed by `k + i`, its value kept
    (`val_va_get` of `Ew.add` at the scalar `k` on `til`, `pick_row` at `til`). Hypotheses: `k + |R|` below
    `2^63`, so no key wraps or reads q's null; `Vals.PickFits` of `R.val` at its rows. -/
theorem rep_num {A B : Obj} (R : Rel A B) (k : USize) (hk : k.toNat + R.n.toNat < 2 ^ 63)
    (hv : Vals.PickFits B R.val (List.range R.n.toNat)) (a : Obj.long.El) (y : B.El) :
    rep (num R k) a y ↔ ∃ i : Fin R.n.toNat, a = Int64.ofNat (k.toNat + i.1) ∧ R.val.row i = y := by
  have hkey : ∀ i : Fin R.n.toNat,
      (valCol (n := R.n) Ew.add Ew.va (tilLongs R.n) (one k.toUInt64)).get i = Int64.ofNat (k.toNat + i.1) :=
    fun i => by
      have ht := tilLongs_get (m := R.n) i.2
      have hk64 : k.toUInt64.toNat = k.toNat := by
        rw [usize_toUInt64, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (by omega : k.toNat < 2 ^ 63) (by decide))]
      rw [Arr.get_long_bytes _ rfl, val_va_get _ _ _ _ i.2, bitsAt_one,
        (valStep_add_sub (x := Column.bitsAt (tilLongs R.n) (i.1 * 8) 8) (y := k.toUInt64) (by rw [ht]; omega)
          (by rw [hk64]; omega)).1 (by rw [ht, hk64]; omega), ht, hk64, Nat.add_comm]
      have hs : (UInt64.ofNat (k.toNat + i.1)).toNat = k.toNat + i.1 :=
        UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (by omega : k.toNat + i.1 < 2 ^ 63) (by decide))
      exact int64_eq_ofNat (by omega) ((toInt64_toInt (by rw [hs]; omega)).trans (by rw [hs]))
  have hl : (List.range R.n.toNat).map (fun q => (Column.bitsAt (tilLongs R.n) (q * 8) 8).toNat) =
      List.range R.n.toNat := by
    conv => rhs; rw [← List.map_id (List.range R.n.toNat)]
    exact List.map_congr_left fun q hq => tilLongs_get (List.mem_range.1 hq)
  have hval : ∀ i : Fin R.n.toNat, (Vals.pick B R.val (tilLongs R.n) R.n (len_tilLongs R.n)).row i = R.val.row i :=
    fun i => by
      rw [pick_row B R.val _ _ _ (by rw [hl]; exact hv) i, dif_pos (by rw [tilLongs_get i.2]; exact i.2)]
      exact congrArg R.val.row (Fin.ext (tilLongs_get i.2))
  rw [rep_apply]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, h1.symm.trans (hkey i), (hval i).symm.trans h2⟩
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨i, hkey i, hval i⟩

/-- **The empty array fits at any rows**: its payload count is `0`, so every window clamps to nothing. -/
theorem pickFits_nilVal (B : Obj) (ps : List Nat) : Vals.PickFits (.arr B) (nilVal B) ps := by
  have hw : ∀ (w : Nat → List Nat), (∀ k, w k = []) → ps.flatMap w = [] := fun w h =>
    List.flatMap_eq_nil_iff.2 fun k _ => h k
  simp only [nilVal, Vals.PickFits]
  rw [hw _ fun k => by split <;> simp]
  exact ⟨by simp, by decide, USize.size_pos, pickFits_empty B⟩

#print axioms rep_mem
#print axioms rep_num
#print axioms pickFits_nilVal

end LeetQ.Rel.Rep
