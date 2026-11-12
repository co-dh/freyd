/-
  More `Alg` ops read in `Rel(Set)`: each `rep_<op>` says `rep` of the executable op is the allegory op on the
  `rep`s, under true size bounds, the codes' faithfulness where the op compares codes, and `Vals.PickFits` where
  it picks.
-/
import LeetQ.Rel.RepComp
import LeetQ.Rel.KernelWF.NubSpec
import LeetQ.Rel.KernelWF.CrossSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B C D : Obj}

/-! ## The sum side: `R + S`, `inl`, `inr` -/

section Sum

/-- **`rep (R + S) = ι₁° rep R ι₁ ∪ ι₂° rep S ι₂`**, `ι₁`, `ι₂` the injections of `Rel(Set)`'s coproduct
    (`sumCop`). The key side is `sumVals R.key S.key` and the value side shares its tags and positions, so it is
    `sumVals R.val S.val`: `sumVals_row` reads both. `hN`: the row count fits a `USize` (past it `R + S` answers
    `𝟘`); `h63`: it is at most `2^63`, where the tags and positions read `til` as nonnegative longs. -/
theorem rep_sum (R : Rel A C) (S : Rel B D) (hN : R.n.toNat + S.n.toNat < USize.size)
    (h63 : R.n.toNat + S.n.toNat ≤ 2 ^ 63) :
    rep (LeetQ.Rel.Alg.sum R S) =
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁° ≫ rep R ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₁) ∪
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂° ≫ rep S ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₂) := by
  have e : LeetQ.Rel.Alg.sum R S = ⟨R.n + S.n, sumVals R.key S.key hN, sumVals R.val S.val hN⟩ := by
    unfold LeetQ.Rel.Alg.sum need; rw [dif_pos hN]; rfl
  rw [e]
  refine hom_ext fun s t => ?_
  show (∃ k, Vals.row (A := .sum A B) (sumVals R.key S.key hN) k = s ∧
      Vals.row (A := .sum C D) (sumVals R.val S.val hN) k = t) ↔
    (∃ a, s = Sum.inl a ∧ ∃ c, R.Holds a c ∧ t = Sum.inl c) ∨
      (∃ b, s = Sum.inr b ∧ ∃ d, S.Holds b d ∧ t = Sum.inr d)
  have hk2 : ∀ k : Nat, k < R.n.toNat + S.n.toNat → k < (R.n + S.n).toNat := fun k h => by
    rw [toNat_add_fits hN]; exact h
  constructor
  · rintro ⟨k, hs, ht⟩
    rw [sumVals_row _ _ hN h63] at hs ht
    by_cases hk : k.1 < R.n.toNat
    · rw [dif_pos hk] at hs ht
      exact Or.inl ⟨_, hs.symm, _, ⟨⟨k.1, hk⟩, rfl, rfl⟩, ht.symm⟩
    · rw [dif_neg hk] at hs ht
      exact Or.inr ⟨_, hs.symm, _, ⟨_, rfl, rfl⟩, ht.symm⟩
  · rintro (⟨a, rfl, c, ⟨i, rfl, rfl⟩, rfl⟩ | ⟨b, rfl, d, ⟨j, rfl, rfl⟩, rfl⟩)
    · refine ⟨⟨i.1, hk2 _ (by omega)⟩, ?_, ?_⟩ <;> rw [sumVals_row _ _ hN h63, dif_pos i.2]
    · have hj : ¬ (R.n.toNat + j.1 < R.n.toNat) := by omega
      refine ⟨⟨R.n.toNat + j.1, hk2 _ (by omega)⟩, ?_, ?_⟩ <;> rw [sumVals_row _ _ hN h63, dif_neg hj] <;>
        simp only [Nat.add_sub_cancel_left]

/-- `rep_sum` at boolean atoms, both counts below `2^31`: the two bounds hold on every platform. -/
theorem rep_sum_boolean (R S : Rel (.atom .boolean) (.atom .boolean)) (hR : R.n.toNat < 2 ^ 31)
    (hS : S.n.toNat < 2 ^ 31) :
    rep (LeetQ.Rel.Alg.sum R S) =
      ((sumCop (⟨(Obj.atom .boolean).El⟩ : RelSet.{0}) ⟨(Obj.atom .boolean).El⟩).u₁° ≫ rep R ≫ (sumCop (⟨(Obj.atom .boolean).El⟩ : RelSet.{0}) ⟨(Obj.atom .boolean).El⟩).u₁) ∪
      ((sumCop (⟨(Obj.atom .boolean).El⟩ : RelSet.{0}) ⟨(Obj.atom .boolean).El⟩).u₂° ≫ rep S ≫ (sumCop (⟨(Obj.atom .boolean).El⟩ : RelSet.{0}) ⟨(Obj.atom .boolean).El⟩).u₂) :=
  rep_sum R S (by rcases USize.size_eq with h | h <;> omega) (by omega)

/-- A one-part tag column `tags #[(n, x)]` reads `x` at each of its `n ≤ 2^63` rows. -/
theorem tags_one_get (x : Bool) {n : USize} (h63 : n.toNat ≤ 2 ^ 63) (i : Fin n.toNat) :
    (tags #[(n, x)] n).get i = x := by
  rw [tags_get _ _ _ (fun p hp => by simp at hp; subst hp; exact h63) i]
  simp [List.getD_eq_getElem?_getD, i.2]

/-- `tilCol n`'s element `i`, clamped into `[0, n)`, is `i`, for `n ≤ 2^63`. -/
theorem clampFin_til {n : USize} (h63 : n.toNat ≤ 2 ^ 63) (i : Fin n.toNat) (h : 0 < n.toNat) :
    clampFin ((tilCol n).get i) n.toNat h = i :=
  Fin.ext (by simp only [clampFin, tilCol_get, Int64.toInt_ofNat_of_lt (show i.1 < 2 ^ 63 by omega)]; omega)

/-- `inl X`'s value at row `i` is `inl` of `X`'s row `i`. -/
theorem inl_row {n : USize} (X : Vals A n) (h63 : n.toNat ≤ 2 ^ 63) (i : Fin n.toNat) :
    Vals.row (A := .sum A B) (inl (B := B) X).val i = .inl (X.row i) := by
  have h : 0 < n.toNat := by have := i.2; omega
  simp only [inl, Vals.row, tags_one_get false h63 i, Bool.false_eq_true, ↓reduceIte, dif_pos h,
    clampFin_til h63 i h]

/-- `inr Y`'s value at row `i` is `inr` of `Y`'s row `i`. -/
theorem inr_row {n : USize} (Y : Vals B n) (h63 : n.toNat ≤ 2 ^ 63) (i : Fin n.toNat) :
    Vals.row (A := .sum A B) (inr (A := A) Y).val i = .inr (Y.row i) := by
  have h : 0 < n.toNat := by have := i.2; omega
  simp only [inr, Vals.row, tags_one_get true h63 i, ↓reduceIte, dif_pos h, clampFin_til h63 i h]

/-- **`rep (inl X) = X? ι₁`**: the coreflexive on the elements `X` lists, then `Rel(Set)`'s first injection — `ι₁`
    itself when `X` lists every element of `A`, as `rep_idU`. `h63`: `X`'s count is at most `2^63`, where the
    tag and position columns read `til` as nonnegative longs. -/
theorem rep_inl {n : USize} (X : Vals A n) (h63 : n.toNat ≤ 2 ^ 63) :
    rep (inl (B := B) X) = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun x => ∃ i, X.row i = x) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁ :=
  hom_ext fun x s => by
    show (∃ i, Vals.row (inl (B := B) X).key i = x ∧ Vals.row (A := .sum A B) (inl (B := B) X).val i = s) ↔
      ∃ y, (x = y ∧ ∃ i, X.row i = x) ∧ s = Sum.inl y
    constructor
    · rintro ⟨i, hx, hs⟩
      rw [inl_row X h63 i] at hs
      exact ⟨x, ⟨rfl, i, hx⟩, hs.symm.trans (congrArg Sum.inl hx)⟩
    · rintro ⟨y, ⟨rfl, i, hx⟩, rfl⟩
      exact ⟨i, hx, by rw [inl_row X h63 i]; exact congrArg Sum.inl hx⟩

/-- **`rep (inr Y) = Y? ι₂`**, as `rep_inl`. -/
theorem rep_inr {n : USize} (Y : Vals B n) (h63 : n.toNat ≤ 2 ^ 63) :
    rep (inr (A := A) Y) = corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun y => ∃ i, Y.row i = y) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂ :=
  hom_ext fun y s => by
    show (∃ i, Vals.row (inr (A := A) Y).key i = y ∧ Vals.row (A := .sum A B) (inr (A := A) Y).val i = s) ↔
      ∃ z, (y = z ∧ ∃ i, Y.row i = y) ∧ s = Sum.inr z
    constructor
    · rintro ⟨i, hy, hs⟩
      rw [inr_row Y h63 i] at hs
      exact ⟨y, ⟨rfl, i, hy⟩, hs.symm.trans (congrArg Sum.inr hy)⟩
    · rintro ⟨z, ⟨rfl, i, hy⟩, rfl⟩
      exact ⟨i, hy, by rw [inr_row Y h63 i]; exact congrArg Sum.inr hy⟩

/-- `rep_inl` on a long universe below `2^31` values. -/
theorem rep_inl_long {n : USize} (X : Vals (.atom .long) n) (hn : n.toNat < 2 ^ 31) :
    rep (inl (B := B) X) = corefl (A := (⟨(Obj.atom .long).El⟩ : RelSet.{0})) (fun x => ∃ i, X.row i = x) ≫
      (sumCop (⟨(Obj.atom .long).El⟩ : RelSet.{0}) ⟨B.El⟩).u₁ :=
  rep_inl X (by omega)

/-- `rep_inr` on a long universe below `2^31` values. -/
theorem rep_inr_long {n : USize} (Y : Vals (.atom .long) n) (hn : n.toNat < 2 ^ 31) :
    rep (inr (A := A) Y) = corefl (A := (⟨(Obj.atom .long).El⟩ : RelSet.{0})) (fun y => ∃ i, Y.row i = y) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨(Obj.atom .long).El⟩).u₂ :=
  rep_inr Y (by omega)

end Sum

#print axioms rep_sum
#print axioms rep_inl
#print axioms rep_inr

end LeetQ.Rel.Rep
