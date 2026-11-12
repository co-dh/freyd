/-
  More `Alg` ops read in `Rel(Set)`: each `rep_<op>` says `rep` of the executable op is the allegory op on the
  `rep`s, under true size bounds, the codes' faithfulness where the op compares codes, and `Vals.PickFits` where
  it picks.
-/
import LeetQ.Rel.RepComp
import LeetQ.Rel.KernelWF.NubSpec
import LeetQ.Rel.KernelWF.CrossSpec
import LeetQ.Rel.KernelWF.MemberSpec

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

/-! ## `dom`, `ran`: the coreflexive on the distinct elements of a side -/

section Distinct

open QLean.Verify

-- the one-part code `distinctCorefl` groups, named as it names it
set_option hygiene false in
local notation "dc" => (Obj.codes _ (#v[⟨n, x⟩] : Vector (Part _) 1))[0]

/-- `distinctCorefl`'s pairs at its first rows `I`, a plain byte array, so nothing can try to compute them: the
    rows `I` names are rows of `x` (`hlt`) and reach every row of `x` up to `g`, along which `x` is constant
    (`hex`, `hF`). -/
theorem distinct_holds (t : Obj) {n : USize} (x : Vals t n) (I : ByteArray) (g : Nat → Nat)
    (hlen : len I < USize.size) (hlt : ∀ f ∈ ids I, f < n.toNat) (hex : ∀ i < n.toNat, ∃ f ∈ ids I, g f = g i)
    (hF : ∀ {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat), g i = g j → x.row ⟨i, hi⟩ = x.row ⟨j, hj⟩)
    (hp : Vals.PickFits t x (ids I)) (a b : t.El) :
    (longCount "distinct" I fun m h => let d := Vals.pick t x I m h; (⟨m, d, d⟩ : Rel t t)).Holds a b ↔
      a = b ∧ ∃ i, x.row i = a := by
  unfold longCount need
  rw [dif_pos hlen]
  suffices H : ∀ (m : USize) (hm : len I = m.toNat),
      (⟨m, Vals.pick t x I m hm, Vals.pick t x I m hm⟩ : Rel t t).Holds a b ↔ a = b ∧ ∃ i, x.row i = a from H _ _
  intro m hm
  have e : ((List.range m.toNat).map fun q => (Column.bitsAt I (q * 8) 8).toNat) = ids I := by rw [← hm]; rfl
  have hrow : ∀ q : Fin m.toNat, ∃ hin : (Column.bitsAt I (q.1 * 8) 8).toNat < n.toNat,
      (Vals.pick t x I m hm).row q = x.row ⟨_, hin⟩ := fun q => by
    have hq : (Column.bitsAt I (q.1 * 8) 8).toNat ∈ ids I := by
      rw [← e]; exact List.mem_map.2 ⟨q.1, List.mem_range.2 q.2, rfl⟩
    have hin : (Column.bitsAt I (q.1 * 8) 8).toNat < n.toNat := hlt _ hq
    exact ⟨hin, by rw [pick_row t x _ m hm (e ▸ hp) q, dif_pos hin]⟩
  simp only [Rel.Holds]
  constructor
  · rintro ⟨q, ha, hb⟩
    obtain ⟨hin, hr⟩ := hrow q
    exact ⟨ha.symm.trans hb, ⟨_, hin⟩, hr ▸ ha⟩
  · rintro ⟨rfl, i, rfl⟩
    obtain ⟨f, hf, he⟩ := hex i.1 i.2
    rw [← e] at hf
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hf
    obtain ⟨hin, hr⟩ := hrow ⟨q, List.mem_range.1 hq⟩
    have hx : x.row ⟨_, hin⟩ = x.row i := hF hin i.2 he
    exact ⟨⟨q, List.mem_range.1 hq⟩, hr.trans hx, hr.trans hx⟩

/-- **`rep (distinctCorefl t x) = x?`**, the coreflexive on the elements `x` lists. `groupIds` answers the first
    row of each code (`groupIds_classes`), every one a row of `x`, and every row of `x` shares its code with
    one of them, so with the code faithful (`hK`, in `rep_nub`'s form) each picked row is a row of `x` and each
    row of `x` is picked. `hp`: `x` picks back at those first rows (`pick_row`). -/
theorem rep_distinctCorefl (t : Obj) {n : USize} (x : Vals t n)
    (hK : (∀ {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat),
        Column.idAt (dc).b (dc).w i = Column.idAt (dc).b (dc).w j ↔ Vals.row x ⟨i, hi⟩ = Vals.row x ⟨j, hj⟩) ∧
      ((dc).w = 1 ∨ (dc).w = 2 ∨ (dc).w = 4 ∨ (dc).w = 8 ∨ (dc).w = 16 ∨ (dc).w = 32 ∨ (dc).w = 64) ∧ (dc).n = n ∧
        (dc).b.size = ((dc).n.toNat * (dc).w + 7) / 8 ∧
        ((dc).w < 8 → (dc).card < USize.size ∧ ∀ i < (dc).n.toNat, Column.idAt (dc).b (dc).w i < (dc).card))
    (hp : Vals.PickFits t x (ids (dc).groupIds.2)) :
    rep (distinctCorefl t x) = corefl (A := (⟨t.El⟩ : RelSet.{0})) fun a => ∃ i, x.row i = a := by
  obtain ⟨hF, hw, hn, hs, hcard⟩ := hK
  obtain ⟨hlt, -, hex⟩ := groupIds_classes (dc) hw hs hcard
  rw [hn] at hlt hex
  have hle : (ids (dc).groupIds.2).length ≤ n.toNat := by
    rw [groupIds_firsts (dc) hw hs hcard, hn]
    exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_range ..))
  have hlen : len (dc).groupIds.2 < USize.size := by rw [len_eq_ids]; exact Nat.lt_of_le_of_lt hle n.toNat_lt_size
  exact hom_ext fun a b => distinct_holds t x _ _ hlen hlt hex (fun hi hj h => (hF hi hj).1 h) hp a b

/-- `rep_distinctCorefl` at an atom side, where every first row is below the count, so `x` fits outright. -/
theorem rep_distinctCorefl_atom {t : QAtomicType} {n : USize} (x : Vals (.atom t) n)
    (hK : (∀ {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat),
        Column.idAt (dc).b (dc).w i = Column.idAt (dc).b (dc).w j ↔ Vals.row x ⟨i, hi⟩ = Vals.row x ⟨j, hj⟩) ∧
      ((dc).w = 1 ∨ (dc).w = 2 ∨ (dc).w = 4 ∨ (dc).w = 8 ∨ (dc).w = 16 ∨ (dc).w = 32 ∨ (dc).w = 64) ∧ (dc).n = n ∧
        (dc).b.size = ((dc).n.toNat * (dc).w + 7) / 8 ∧
        ((dc).w < 8 → (dc).card < USize.size ∧ ∀ i < (dc).n.toNat, Column.idAt (dc).b (dc).w i < (dc).card)) :
    rep (distinctCorefl (.atom t) x) = corefl (A := (⟨(Obj.atom t).El⟩ : RelSet.{0})) fun a => ∃ i, x.row i = a :=
  rep_distinctCorefl _ x hK (pickFits_atom x fun f hf =>
    hK.2.2.1 ▸ (groupIds_classes (dc) hK.2.1 hK.2.2.2.1 hK.2.2.2.2).1 f hf)

/-- `rep_distinctCorefl` at a boolean side: its code is its bits (`codes_boolean_faithful`/`_wf`). -/
theorem rep_distinctCorefl_boolean {n : USize} (x : Vals (.atom .boolean) n) :
    rep (distinctCorefl (.atom .boolean) x) =
      corefl (A := (⟨(Obj.atom .boolean).El⟩ : RelSet.{0})) fun a => ∃ i, x.row i = a :=
  rep_distinctCorefl_atom x ⟨fun hi hj => codes_boolean_faithful _ (k := 0) (l := 0) (by decide) (by decide) hi hj,
    by have h := codes_boolean_wf (#v[⟨n, x⟩] : Vector (Part _) 1) (k := 0) (by decide)
       exact ⟨Or.inl h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩

/-- **`rep (dom R) = dom (rep R)`**, `dom S = {(a, a) ∣ ∃ b, S(a, b)}` (`= 𝟙 ∩ S S°`): `dom R` is
    `distinctCorefl` of the keys, whose elements are the `a` with a pair. Hypotheses: `rep_distinctCorefl`'s
    at `R.key`. -/
theorem rep_dom (R : Rel A B)
    (hK : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
        Column.idAt (Obj.codes _ (#v[⟨R.n, R.key⟩] : Vector (Part _) 1))[0].b
            (Obj.codes _ (#v[⟨R.n, R.key⟩] : Vector (Part _) 1))[0].w i =
          Column.idAt (Obj.codes _ (#v[⟨R.n, R.key⟩] : Vector (Part _) 1))[0].b
            (Obj.codes _ (#v[⟨R.n, R.key⟩] : Vector (Part _) 1))[0].w j ↔
        Vals.row R.key ⟨i, hi⟩ = Vals.row R.key ⟨j, hj⟩) ∧
      (let c := (Obj.codes _ (#v[⟨R.n, R.key⟩] : Vector (Part _) 1))[0]
       (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = R.n ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)))
    (hp : Vals.PickFits A R.key (ids (Obj.codes _ (#v[⟨R.n, R.key⟩] : Vector (Part _) 1))[0].groupIds.2)) :
    rep (dom R) = corefl (A := (⟨A.El⟩ : RelSet.{0})) fun a => ∃ b, rep R a b := by
  rw [show dom R = distinctCorefl A R.key from rfl, rep_distinctCorefl A R.key hK hp]
  exact congrArg corefl (funext fun a => propext ⟨fun ⟨i, h⟩ => ⟨_, i, h, rfl⟩, fun ⟨_, i, h, _⟩ => ⟨i, h⟩⟩)

/-- **`rep (ran R) = ran (rep R)`**, `ran S = {(b, b) ∣ ∃ a, S(a, b)}`: `distinctCorefl` of the values. -/
theorem rep_ran (R : Rel A B)
    (hK : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
        Column.idAt (Obj.codes _ (#v[⟨R.n, R.val⟩] : Vector (Part _) 1))[0].b
            (Obj.codes _ (#v[⟨R.n, R.val⟩] : Vector (Part _) 1))[0].w i =
          Column.idAt (Obj.codes _ (#v[⟨R.n, R.val⟩] : Vector (Part _) 1))[0].b
            (Obj.codes _ (#v[⟨R.n, R.val⟩] : Vector (Part _) 1))[0].w j ↔
        Vals.row R.val ⟨i, hi⟩ = Vals.row R.val ⟨j, hj⟩) ∧
      (let c := (Obj.codes _ (#v[⟨R.n, R.val⟩] : Vector (Part _) 1))[0]
       (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = R.n ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)))
    (hp : Vals.PickFits B R.val (ids (Obj.codes _ (#v[⟨R.n, R.val⟩] : Vector (Part _) 1))[0].groupIds.2)) :
    rep (ran R) = corefl (A := (⟨B.El⟩ : RelSet.{0})) fun b => ∃ a, rep R a b := by
  rw [show ran R = distinctCorefl B R.val from rfl, rep_distinctCorefl B R.val hK hp]
  exact congrArg corefl (funext fun b => propext ⟨fun ⟨i, h⟩ => ⟨_, i, rfl, h⟩, fun ⟨_, i, _, h⟩ => ⟨i, h⟩⟩)

/-- `rep_dom` with boolean keys: no hypothesis left. -/
theorem rep_dom_boolean (R : Rel (.atom .boolean) B) :
    rep (dom R) = corefl (A := (⟨(Obj.atom .boolean).El⟩ : RelSet.{0})) fun a => ∃ b, rep R a b := by
  rw [show dom R = distinctCorefl _ R.key from rfl, rep_distinctCorefl_boolean]
  exact congrArg corefl (funext fun a => propext ⟨fun ⟨i, h⟩ => ⟨_, i, h, rfl⟩, fun ⟨_, i, h, _⟩ => ⟨i, h⟩⟩)

/-- `rep_ran` with boolean values: no hypothesis left. -/
theorem rep_ran_boolean (R : Rel A (.atom .boolean)) :
    rep (ran R) = corefl (A := (⟨(Obj.atom .boolean).El⟩ : RelSet.{0})) fun b => ∃ a, rep R a b := by
  rw [show ran R = distinctCorefl _ R.val from rfl, rep_distinctCorefl_boolean]
  exact congrArg corefl (funext fun b => propext ⟨fun ⟨i, h⟩ => ⟨_, i, rfl, h⟩, fun ⟨_, i, _, h⟩ => ⟨i, h⟩⟩)

end Distinct

/-! ## `⊤` on two universes -/

section Top

open QLean.Verify

section Cross

variable {ma mb : USize}

/-- `cross ma mb`'s two index columns read back: row `k` of the `ma · mb` pairs is `(k / mb, k % mb)`
    (`cross_elems`, under its bounds). -/
theorem cross_ids (hN : ma.toNat * mb.toNat < USize.size) (h63 : ma.toNat * mb.toNat < 2 ^ 63) :
    ids (cross ma mb).1 = (List.range (ma.toNat * mb.toNat)).map (· / mb.toNat) ∧
      ids (cross ma mb).2 = (List.range (ma.toNat * mb.toNat)).map (· % mb.toNat) := by
  obtain ⟨h1, h2⟩ := cross_elems hN h63
  have hid : ∀ d, ids d = (elemsW 8 d).map UInt64.toNat := fun d => by
    simp only [ids, elemsW, List.map_map, Function.comp_def]
  refine ⟨?_, ?_⟩
  · rw [hid, h1, List.map_map]; refine List.map_congr_left fun k hk => ?_
    have := List.mem_range.1 hk; have := Nat.div_le_self k mb.toNat
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show _ < 2 ^ 63 by omega) (by decide))
  · rw [hid, h2, List.map_map]; refine List.map_congr_left fun k hk => ?_
    have := List.mem_range.1 hk; have := Nat.mod_le k mb.toNat
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show _ < 2 ^ 63 by omega) (by decide))

/-- `cross ma mb`'s index columns are `ma · mb` long. -/
theorem cross_count (hN : ma.toNat * mb.toNat < USize.size) (h63 : ma.toNat * mb.toNat < 2 ^ 63) {m : USize}
    (hm : len (cross ma mb).1 = m.toNat) : m.toNat = ma.toNat * mb.toNat := by
  rw [← hm, len_eq_ids, (cross_ids hN h63).1]; simp

/-- A side of `ma` rows picked at `cross`'s left column: row `q` is row `q / mb`. -/
theorem pick_cross_left {X : Obj} (x : Vals X ma) (hN : ma.toNat * mb.toNat < USize.size)
    (h63 : ma.toNat * mb.toNat < 2 ^ 63)
    (hx : Vals.PickFits X x ((List.range (ma.toNat * mb.toNat)).map (· / mb.toNat)))
    {m : USize} (hm : len (cross ma mb).1 = m.toNat) (q : Nat) (hq : q < m.toNat) :
    ∃ hin : q / mb.toNat < ma.toNat, (Vals.pick X x (cross ma mb).1 m hm).row ⟨q, hq⟩ = x.row ⟨_, hin⟩ := by
  have e : ((List.range m.toNat).map fun q => (Column.bitsAt (cross ma mb).1 (q * 8) 8).toNat) =
      (List.range (ma.toNat * mb.toNat)).map (· / mb.toNat) := by rw [← (cross_ids hN h63).1, ← hm]; rfl
  have hmn := cross_count hN h63 hm
  have v : (Column.bitsAt (cross ma mb).1 (q * 8) 8).toNat = q / mb.toNat := by
    simpa [hq, hmn ▸ hq] using congrArg (fun l => l[q]?) e
  have hin : q / mb.toNat < ma.toNat := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hmn]; exact hq)
  have hin' : (Column.bitsAt (cross ma mb).1 (q * 8) 8).toNat < ma.toNat := by rw [v]; exact hin
  refine ⟨hin, ?_⟩
  rw [pick_row X x _ m hm (e ▸ hx) ⟨q, hq⟩, dif_pos hin']; exact congrArg x.row (Fin.ext v)

/-- A side of `mb` rows picked at `cross`'s right column: row `q` is row `q % mb`. -/
theorem pick_cross_right {X : Obj} (y : Vals X mb) (hN : ma.toNat * mb.toNat < USize.size)
    (h63 : ma.toNat * mb.toNat < 2 ^ 63)
    (hy : Vals.PickFits X y ((List.range (ma.toNat * mb.toNat)).map (· % mb.toNat)))
    {m : USize} (hm : len (cross ma mb).2 = m.toNat) (q : Nat) (hq : q < m.toNat) :
    ∃ hin : q % mb.toNat < mb.toNat, (Vals.pick X y (cross ma mb).2 m hm).row ⟨q, hq⟩ = y.row ⟨_, hin⟩ := by
  have e : ((List.range m.toNat).map fun q => (Column.bitsAt (cross ma mb).2 (q * 8) 8).toNat) =
      (List.range (ma.toNat * mb.toNat)).map (· % mb.toNat) := by rw [← (cross_ids hN h63).2, ← hm]; rfl
  have hmn := cross_count hN h63 ((cross_len ma mb).symm.trans hm)
  have v : (Column.bitsAt (cross ma mb).2 (q * 8) 8).toNat = q % mb.toNat := by
    simpa [hq, hmn ▸ hq] using congrArg (fun l => l[q]?) e
  have hin : q % mb.toNat < mb.toNat :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero fun e => by rw [hmn, e, Nat.mul_zero] at hq; omega)
  have hin' : (Column.bitsAt (cross ma mb).2 (q * 8) 8).toNat < mb.toNat := by rw [v]; exact hin
  refine ⟨hin, ?_⟩
  rw [pick_row X y _ m hm (e ▸ hy) ⟨q, hq⟩, dif_pos hin']; exact congrArg y.row (Fin.ext v)

/-- The pair `(i, j)` is `cross`'s row `i · mb + j`. -/
theorem cross_at {i j : Nat} (hi : i < ma.toNat) (hj : j < mb.toNat) :
    i * mb.toNat + j < ma.toNat * mb.toNat ∧ (i * mb.toNat + j) / mb.toNat = i ∧
      (i * mb.toNat + j) % mb.toNat = j := by
  refine ⟨?_, ?_, ?_⟩
  · calc i * mb.toNat + j < i * mb.toNat + mb.toNat := by omega
      _ = (i + 1) * mb.toNat := by rw [Nat.succ_mul]
      _ ≤ ma.toNat * mb.toNat := Nat.mul_le_mul_right _ (by omega)
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

end Cross

/-- **`rep (top Ua Ub) = Ua? ⊤ Ub?`**: every pair of an element `Ua` lists with one `Ub` lists — `⊤` itself when the
    two universes list every element. `cross` answers row `k` of the `ma · mb` pairs as `(k / mb, k % mb)`
    (`cross_ids`), each side picked there (`pick_cross_left`/`_right`). Hypotheses: the pair count fits a `USize`
    and is below `2^63` (`cross_elems`'s), and each side picks back at its rows (`Vals.PickFits`). -/
theorem rep_top {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) (hN : ma.toNat * mb.toNat < USize.size)
    (h63 : ma.toNat * mb.toNat < 2 ^ 63)
    (hA : Vals.PickFits A Ua ((List.range (ma.toNat * mb.toNat)).map (· / mb.toNat)))
    (hB : Vals.PickFits B Ub ((List.range (ma.toNat * mb.toNat)).map (· % mb.toNat))) :
    rep (LeetQ.Rel.Alg.top Ua Ub) = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun a => ∃ i, Ua.row i = a) ≫
      relTop ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun b => ∃ j, Ub.row j = b) := by
  have hlen : len (cross ma mb).1 < USize.size := by rw [len_eq_ids, (cross_ids hN h63).1]; simpa using hN
  refine hom_ext fun a b => ?_
  show (longCount "⊤" (cross ma mb).1 fun m h => (⟨m, Vals.pick A Ua (cross ma mb).1 m h,
      Vals.pick B Ub (cross ma mb).2 m ((cross_len ma mb).trans h)⟩ : Rel A B)).Holds a b ↔
    ∃ a', (a = a' ∧ ∃ i, Ua.row i = a) ∧ ∃ b', True ∧ (b' = b ∧ ∃ j, Ub.row j = b')
  unfold longCount need
  rw [dif_pos hlen]
  suffices H : ∀ (m : USize) (hm : len (cross ma mb).1 = m.toNat),
      (⟨m, Vals.pick A Ua (cross ma mb).1 m hm, Vals.pick B Ub (cross ma mb).2 m ((cross_len ma mb).trans hm)⟩ :
        Rel A B).Holds a b ↔ ∃ a', (a = a' ∧ ∃ i, Ua.row i = a) ∧ ∃ b', True ∧ (b' = b ∧ ∃ j, Ub.row j = b')
    from H _ _
  intro m hm
  have hmn := cross_count hN h63 hm
  simp only [Rel.Holds]
  constructor
  · rintro ⟨⟨q, hq⟩, ha, hb⟩
    obtain ⟨_, hr1⟩ := pick_cross_left Ua hN h63 hA hm q hq
    obtain ⟨_, hr2⟩ := pick_cross_right Ub hN h63 hB ((cross_len ma mb).trans hm) q hq
    exact ⟨a, ⟨rfl, _, hr1 ▸ ha⟩, b, trivial, rfl, _, hr2 ▸ hb⟩
  · rintro ⟨_, ⟨rfl, i, rfl⟩, _, -, rfl, j, rfl⟩
    obtain ⟨hq, hdiv, hmod⟩ := cross_at i.2 j.2
    rw [← hmn] at hq
    obtain ⟨_, hr1⟩ := pick_cross_left Ua hN h63 hA hm _ hq
    obtain ⟨_, hr2⟩ := pick_cross_right Ub hN h63 hB ((cross_len ma mb).trans hm) _ hq
    exact ⟨⟨_, hq⟩, hr1.trans (congrArg Ua.row (Fin.ext hdiv)), hr2.trans (congrArg Ub.row (Fin.ext hmod))⟩

/-- **`rep (R × S) = rep R × rep S`** (`rprodMap`): `prod` answers each pair of a row of `R` with a row of `S`, row
    `k` of `cross R.n S.n` the pair `(k / S.n, k % S.n)`. Hypotheses: `rep_top`'s at the counts `R.n`, `S.n`, each
    of the four columns picking back at its rows. -/
theorem rep_prod (R : Rel A B) (S : Rel C D) (hN : R.n.toNat * S.n.toNat < USize.size)
    (h63 : R.n.toNat * S.n.toNat < 2 ^ 63)
    (hA : Vals.PickFits A R.key ((List.range (R.n.toNat * S.n.toNat)).map (· / S.n.toNat)))
    (hB : Vals.PickFits B R.val ((List.range (R.n.toNat * S.n.toNat)).map (· / S.n.toNat)))
    (hC : Vals.PickFits C S.key ((List.range (R.n.toNat * S.n.toNat)).map (· % S.n.toNat)))
    (hD : Vals.PickFits D S.val ((List.range (R.n.toNat * S.n.toNat)).map (· % S.n.toNat))) :
    rep (LeetQ.Rel.Alg.prod R S) = rprodMap (rep R) (rep S) := by
  have hlen : len (cross R.n S.n).1 < USize.size := by rw [len_eq_ids, (cross_ids hN h63).1]; simpa using hN
  refine hom_ext fun p p' => ?_
  show (longCount "×" (cross R.n S.n).1 fun m h => (⟨m,
      (Vals.pick A R.key (cross R.n S.n).1 m h, Vals.pick C S.key (cross R.n S.n).2 m ((cross_len R.n S.n).trans h)),
      (Vals.pick B R.val (cross R.n S.n).1 m h, Vals.pick D S.val (cross R.n S.n).2 m ((cross_len R.n S.n).trans h))⟩ :
        Rel (.prod A C) (.prod B D))).Holds p p' ↔ R.Holds p.1 p'.1 ∧ S.Holds p.2 p'.2
  unfold longCount need
  rw [dif_pos hlen]
  suffices H : ∀ (m : USize) (hm : len (cross R.n S.n).1 = m.toNat), (⟨m,
      (Vals.pick A R.key (cross R.n S.n).1 m hm, Vals.pick C S.key (cross R.n S.n).2 m ((cross_len R.n S.n).trans hm)),
      (Vals.pick B R.val (cross R.n S.n).1 m hm, Vals.pick D S.val (cross R.n S.n).2 m ((cross_len R.n S.n).trans hm))⟩ :
        Rel (.prod A C) (.prod B D)).Holds p p' ↔ R.Holds p.1 p'.1 ∧ S.Holds p.2 p'.2 from H _ _
  intro m hm
  have hmn := cross_count hN h63 hm
  have hm2 := (cross_len R.n S.n).trans hm
  constructor
  · rintro ⟨⟨q, hq⟩, hk, hv⟩
    obtain ⟨hi, a1⟩ := pick_cross_left R.key hN h63 hA hm q hq
    obtain ⟨_, a2⟩ := pick_cross_left R.val hN h63 hB hm q hq
    obtain ⟨hj, c1⟩ := pick_cross_right S.key hN h63 hC hm2 q hq
    obtain ⟨_, c2⟩ := pick_cross_right S.val hN h63 hD hm2 q hq
    subst hk hv
    exact ⟨⟨⟨_, hi⟩, a1.symm, a2.symm⟩, ⟨⟨_, hj⟩, c1.symm, c2.symm⟩⟩
  · rintro ⟨⟨i, hi1, hi2⟩, ⟨j, hj1, hj2⟩⟩
    obtain ⟨hq, hdiv, hmod⟩ := cross_at i.2 j.2
    rw [← hmn] at hq
    obtain ⟨_, a1⟩ := pick_cross_left R.key hN h63 hA hm _ hq
    obtain ⟨_, a2⟩ := pick_cross_left R.val hN h63 hB hm _ hq
    obtain ⟨_, c1⟩ := pick_cross_right S.key hN h63 hC hm2 _ hq
    obtain ⟨_, c2⟩ := pick_cross_right S.val hN h63 hD hm2 _ hq
    refine ⟨⟨_, hq⟩, Prod.ext ?_ ?_, Prod.ext ?_ ?_⟩
    · exact (a1.trans (congrArg R.key.row (Fin.ext hdiv))).trans hi1
    · exact (c1.trans (congrArg S.key.row (Fin.ext hmod))).trans hj1
    · exact (a2.trans (congrArg R.val.row (Fin.ext hdiv))).trans hi2
    · exact (c2.trans (congrArg S.val.row (Fin.ext hmod))).trans hj2

/-- `rep_prod` at atom sides, the pair count below `2^31`: every pick is below its side's count (`pickFits_atom`). -/
theorem rep_prod_atoms {t₁ t₂ t₃ t₄ : QAtomicType} (R : Rel (.atom t₁) (.atom t₂)) (S : Rel (.atom t₃) (.atom t₄))
    (h : R.n.toNat * S.n.toNat < 2 ^ 31) : rep (LeetQ.Rel.Alg.prod R S) = rprodMap (rep R) (rep S) :=
  have hl : ∀ k ∈ (List.range (R.n.toNat * S.n.toNat)).map (· / S.n.toNat), k < R.n.toNat := fun k hk => by
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact List.mem_range.1 hk')
  have hr : ∀ k ∈ (List.range (R.n.toNat * S.n.toNat)).map (· % S.n.toNat), k < S.n.toNat := fun k hk => by
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero fun e => by
      have := List.mem_range.1 hk'; rw [e, Nat.mul_zero] at this; omega)
  rep_prod R S (by rcases USize.size_eq with e | e <;> omega) (by omega) (pickFits_atom _ hl) (pickFits_atom _ hl)
    (pickFits_atom _ hr) (pickFits_atom _ hr)

/-- `rep_top` on atom universes, whose pair count is below `2^31`: every pick is below its side's count, so both
    sides fit outright (`pickFits_atom`). -/
theorem rep_top_atoms {t t' : QAtomicType} {ma mb : USize} (Ua : Vals (.atom t) ma) (Ub : Vals (.atom t') mb)
    (h : ma.toNat * mb.toNat < 2 ^ 31) :
    rep (LeetQ.Rel.Alg.top Ua Ub) = corefl (A := (⟨(Obj.atom t).El⟩ : RelSet.{0})) (fun a => ∃ i, Ua.row i = a) ≫
      relTop ≫ corefl (A := (⟨(Obj.atom t').El⟩ : RelSet.{0})) (fun b => ∃ j, Ub.row j = b) :=
  rep_top Ua Ub (by rcases USize.size_eq with e | e <;> omega) (by omega)
    (pickFits_atom Ua fun k hk => by
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact List.mem_range.1 hk'))
    (pickFits_atom Ub fun k hk => by
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
      exact Nat.mod_lt _ (Nat.pos_of_ne_zero fun e => by
        have := List.mem_range.1 hk'; rw [e, Nat.mul_zero] at this; omega))

end Top

#print axioms rep_top
#print axioms rep_prod

#print axioms rep_dom
#print axioms rep_ran
#print axioms rep_sum
#print axioms rep_inl
#print axioms rep_inr

end LeetQ.Rel.Rep
