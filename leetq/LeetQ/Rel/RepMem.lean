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

-- dup of SliceSpec's local notations: a row's clamped window, `expand`'s index column and the copies' positions
set_option hygiene false in
local notation "sL(" x ", " r ", " h ")" => min (max (Int64.toInt (Arr.get x.2.1 ⟨r, h⟩)) 0).toNat x.1.toNat
set_option hygiene false in
local notation "sH(" x ", " r ", " h ")" => min (max (Int64.toInt (Arr.get x.2.2.1 ⟨r, h⟩)) 0).toNat x.1.toNat

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

/-- **`rep_mem` on arrays of atoms (booleans, longs, …), from sizes alone**: the payload below `2^63`, and the
    total of the squared cell lengths below `2^63` and `USize.size` — `mem`'s keys copy each cell once per
    element (`Σ |cell|²` values), its values each element once (`Σ |cell| ≤ Σ |cell|²`). -/
theorem rep_mem_atom {t : QAtomicType} {n : USize} (X : Vals (.arr (.atom t)) n) (hp : X.1.toNat < 2 ^ 63)
    (hq : ((List.range n.toNat).map fun r => if h : r < n.toNat then (X.row ⟨r, h⟩).length ^ 2 else 0).sum < 2 ^ 63)
    (hqU : ((List.range n.toNat).map fun r => if h : r < n.toNat then (X.row ⟨r, h⟩).length ^ 2 else 0).sum <
      USize.size)
    (xs : (Obj.arr (.atom t)).El) (x : (Obj.atom t).El) :
    rep (Alg.mem X) xs x ↔ (∃ i, X.row i = xs) ∧ x ∈ xs := by
  have hmono : ∀ (l : List Nat) (f g : Nat → Nat), (∀ a ∈ l, f a ≤ g a) → (l.map f).sum ≤ (l.map g).sum := by
    intro l f g h
    induction l with
    | nil => exact Nat.le_refl _
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))
  have h1 : ((List.range n.toNat).map fun r => if h : r < n.toNat then (X.row ⟨r, h⟩).length else 0).sum ≤
      ((List.range n.toNat).map fun r => if h : r < n.toNat then (X.row ⟨r, h⟩).length ^ 2 else 0).sum :=
    hmono _ _ _ fun r _ => by
      by_cases h : r < n.toNat
      · rw [dif_pos h, dif_pos h, Nat.pow_two]; exact Nat.le_mul_self _
      · rw [dif_neg h, dif_neg h]; exact Nat.le_refl _
  have hrep : ∀ a b : Nat, (List.replicate a b).sum = a * b := fun a b => by
    induction a with
    | zero => rw [Nat.zero_mul]; rfl
    | succ a ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]
  have hflat : ∀ (l : List Nat) (f : Nat → List Nat) (g : Nat → Nat),
      ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
    intro l f g
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append_nat, List.map_cons, List.sum_cons, ih]
  have h2 : (((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []).map
        fun r => if h : r < n.toNat then (X.row ⟨r, h⟩).length else 0).sum =
      ((List.range n.toNat).map fun r => if h : r < n.toNat then (X.row ⟨r, h⟩).length ^ 2 else 0).sum := by
    rw [hflat]; congr 1; apply List.map_congr_left; intro r _
    by_cases h : r < n.toNat
    · rw [dif_pos h, dif_pos h, List.map_replicate, dif_pos h, hrep, Nat.pow_two]
    · rw [dif_neg h, dif_neg h]; rfl
  exact rep_mem X (pickFits_arr_atom X _ hp (Nat.lt_of_le_of_lt h1 hq) (Nat.lt_of_le_of_lt h1 hqU))
    (pickFits_arr_atom X _ hp (h2 ▸ hq) (h2 ▸ hqU)) xs x

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

/-- `rep_num` with atom values: `til` picks rows below the count, so the values fit outright (`pickFits_atom`). -/
theorem rep_num_atom {A : Obj} {t : QAtomicType} (R : Rel A (.atom t)) (k : USize) (hk : k.toNat + R.n.toNat < 2 ^ 63)
    (a : Obj.long.El) (y : (Obj.atom t).El) :
    rep (num R k) a y ↔ ∃ i : Fin R.n.toNat, a = Int64.ofNat (k.toNat + i.1) ∧ R.val.row i = y :=
  rep_num R k hk (pickFits_atom _ fun _ h => List.mem_range.1 h) a y

#print axioms rep_mem
#print axioms rep_mem_atom
#print axioms rep_num
#print axioms rep_num_atom

end LeetQ.Rel.Rep
