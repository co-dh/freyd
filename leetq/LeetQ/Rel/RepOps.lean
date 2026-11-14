/-
  More `Alg` ops read in `Rel(Set)`: each `rep_<op>` says `rep` of the executable op is the allegory op on the
  `rep`s, under true size bounds, the codes' faithfulness where the op compares codes, and `Vals.PickFits` where
  it picks.
-/
import LeetQ.Rel.RepComp
import LeetQ.Rel.KernelWF.NubSpec
import LeetQ.Rel.KernelWF.CrossSpec
import LeetQ.Rel.KernelWF.MemberSpec
import LeetQ.Rel.KernelWF.CodesProdFaithful

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
local notation "dc" => ((Obj.codes _ (#v[⟨n, x⟩] : Vector (Part _) 1))[0]'Nat.zero_lt_one)

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
      laneOK((dc).w) ∧ (dc).n = n ∧
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

namespace OpsN
-- the one-part code `distinctCorefl` groups, and `rep_dom`'s hypothesis on it. The index proof is a term: a bare
-- `[0]` postpones `get_elem_tactic` to the end of the header that uses it, where it runs against every hypothesis
set_option hygiene false in
scoped notation "c1(" X ", " n ", " x ")" => (Obj.codes X (#v[⟨n, x⟩] : Vector (Part X) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "oneOK(" X ", " n ", " x ")" => ((∀ {i j : Nat} (hi : i < USize.toNat n) (hj : j < USize.toNat n),
    Column.idAt (c1(X, n, x)).b (c1(X, n, x)).w i = Column.idAt (c1(X, n, x)).b (c1(X, n, x)).w j ↔
      Vals.row x ⟨i, hi⟩ = Vals.row x ⟨j, hj⟩) ∧
  (let c := c1(X, n, x)
   laneOK(c.w) ∧ c.n = n ∧
    c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
    (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)))
end OpsN
open OpsN

/-- `dom S ≜ 𝟙 ∩ S S°` (§2.122) in `Rel(Set)` is the coreflexive on the `a` with a pair. -/
theorem dom_corefl {X Y : RelSet.{0}} (S : X ⟶ Y) : 𝟙 X ∩ S ≫ S° = corefl fun a => ∃ b, S a b :=
  hom_ext fun _ _ => ⟨fun ⟨e, b, h, _⟩ => ⟨e, b, h⟩, fun ⟨e, b, h⟩ => ⟨e, b, h, by subst e; exact h⟩⟩

/-- **`rep (dom R) = 𝟙 ∩ rep R (rep R)°`**, the allegory's `dom` (§2.122): `dom R` is `distinctCorefl` of the
    keys, whose elements are the `a` with a pair (`dom_corefl`). Hypotheses: `rep_distinctCorefl`'s at `R.key`. -/
theorem rep_dom (R : Rel A B) (hK : oneOK(A, R.n, R.key))
    (hp : Vals.PickFits A R.key (ids (c1(A, R.n, R.key)).groupIds.2)) :
    rep (dom R) = 𝟙 _ ∩ rep R ≫ (rep R)° := by
  rw [dom_corefl, show dom R = distinctCorefl A R.key from rfl, rep_distinctCorefl A R.key hK hp]
  exact congrArg corefl (funext fun a => propext ⟨fun ⟨i, h⟩ => ⟨_, i, h, rfl⟩, fun ⟨_, i, h, _⟩ => ⟨i, h⟩⟩)

/-- **`rep (ran R) = 𝟙 ∩ (rep R)° (rep R)°°`**, the allegory's `ran S ≜ dom S°`: `ran R` is `dom R°`, so
    `rep_dom` at `R°` read through `rep_conv`. Hypotheses: `rep_dom`'s at `R°`, whose keys are `R.val`. -/
theorem rep_ran (R : Rel A B) (hK : oneOK(B, R.n, R.val))
    (hp : Vals.PickFits B R.val (ids (c1(B, R.n, R.val)).groupIds.2)) :
    rep (ran R) = 𝟙 _ ∩ (rep R)° ≫ (rep R)°° := by
  rw [← rep_conv]; exact rep_dom (R°) hK hp

/-- `rep_dom` read pointwise, `{(a, a) ∣ ∃ b, rep R(a, b)}` (`dom_corefl`). -/
theorem rep_dom_corefl (R : Rel A B) (hK : oneOK(A, R.n, R.key))
    (hp : Vals.PickFits A R.key (ids (c1(A, R.n, R.key)).groupIds.2)) :
    rep (dom R) = corefl (A := (⟨A.El⟩ : RelSet.{0})) fun a => ∃ b, rep R a b :=
  (rep_dom R hK hp).trans (dom_corefl _)

/-- `rep_ran` read pointwise, `{(b, b) ∣ ∃ a, rep R(a, b)}` (`dom_corefl`). -/
theorem rep_ran_corefl (R : Rel A B) (hK : oneOK(B, R.n, R.val))
    (hp : Vals.PickFits B R.val (ids (c1(B, R.n, R.val)).groupIds.2)) :
    rep (ran R) = corefl (A := (⟨B.El⟩ : RelSet.{0})) fun b => ∃ a, rep R a b :=
  (rep_ran R hK hp).trans (dom_corefl _)

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

/-! ## `∩`, `⊑`, `==`: `member` on the joint pair codes -/

section Pairs

open QLean.Verify

namespace OpsN
-- codes `cs` of two parts `ps` faithful and well formed, in `rep_comp`'s `hc` form (`codes_prod_faithful_wf`'s)
set_option hygiene false in
scoped notation "codesOK(" cs ", " ps ")" => ((∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat}
    (hi : i < (ps[k]'hk).1.toNat) (hj : j < (ps[l]'hl).1.toNat),
    Column.idAt (cs[k]'hk).b (cs[k]'hk).w i = Column.idAt (cs[l]'hl).b (cs[l]'hl).w j ↔
      Vals.row (ps[k]'hk).2 ⟨i, hi⟩ = Vals.row (ps[l]'hl).2 ⟨j, hj⟩) ∧
  ∀ {k : Nat} (hk : k < 2),
    laneOK((cs[k]'hk).w) ∧
    (cs[k]'hk).n = (ps[k]'hk).1 ∧ (cs[k]'hk).b.size = ((cs[k]'hk).n.toNat * (cs[k]'hk).w + 7) / 8 ∧
    ((cs[k]'hk).w < 8 → (cs[k]'hk).card < USize.size ∧
      ∀ i < (cs[k]'hk).n.toNat, Column.idAt (cs[k]'hk).b (cs[k]'hk).w i < (cs[k]'hk).card))
-- the two relations as parts of a product side, the sides read off `R`, `S` (the fields are applied, not
-- projected: `R.n` would be one identifier, not the parameter `R`)
set_option hygiene false in
scoped notation "pcs(" R ", " S ")" =>
  (#v[⟨Rel.n R, (Rel.key R, Rel.val R)⟩, ⟨Rel.n S, (Rel.key S, Rel.val S)⟩] : Vector (Part (.prod _ _)) 2)
-- the joint pair codes `pairs #v[R, S]` faithful and well formed
set_option hygiene false in
scoped notation "pairsOK(" R ", " S ")" => codesOK(pairs #v[R, S], pcs(R, S))
-- the rows of `R` whose pair is no pair of `S`, as `−` computes them
set_option hygiene false in
scoped notation "misses(" R ", " S ")" =>
  anti ((pairs #v[R, S])[0]'Nat.zero_lt_two) ((pairs #v[R, S])[1]'Nat.one_lt_two)
end OpsN
open OpsN

-- the rows of `R` whose pair is a pair of `S`, as `∩` and `⊑` compute them
set_option hygiene false in
local notation "hits" => whereBits R.n (((pairs #v[R, S])[0]'Nat.zero_lt_two).member ((pairs #v[R, S])[1]'Nat.one_lt_two))

/-- Row `i` of `R` is marked by `member` exactly when its pair is a pair of `S` (`member_bit`, the codes faithful). -/
theorem pairs_member (R S : Rel A B) (hc : pairsOK(R, S)) {i : Nat} (hi : i < R.n.toNat) :
    Column.bitAt (((pairs #v[R, S])[0]'Nat.zero_lt_two).member ((pairs #v[R, S])[1]'Nat.one_lt_two)) i = true ↔
      ∃ j, S.key.row j = R.key.row ⟨i, hi⟩ ∧ S.val.row j = R.val.row ⟨i, hi⟩ := by
  obtain ⟨hF, hW⟩ := hc
  obtain ⟨hw0, hn0, hs0, -⟩ := hW (k := 0) (by decide)
  obtain ⟨hw1, hn1, hs1, -⟩ := hW (k := 1) (by decide)
  rw [member_bit _ _ hw0 hw1 hs0 hs1 (by rw [hn0]; exact hi)]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' : j < S.n.toNat := by rw [hn1] at hj; exact hj
    have e := (hF (k := 1) (l := 0) (by decide) (by decide) hj' hi).1 he
    exact ⟨⟨j, hj'⟩, (Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
  · rintro ⟨j, h1, h2⟩
    refine ⟨j.1, by rw [hn1]; exact j.2, (hF (k := 1) (l := 0) (by decide) (by decide) j.2 hi).2 ?_⟩
    show (S.key.row j, S.val.row j) = (R.key.row ⟨i, hi⟩, R.val.row ⟨i, hi⟩)
    rw [h1, h2]

/-- `R.rows I`, `I` the ascending rows of `R` a bit `f` keeps, holds `R`'s pairs at those rows — what `∩`
    (`member`) and `−` (`anti`) read back to, by `rows_spec`. Hypotheses: `R`'s columns pick back at the rows. -/
theorem rows_keep (R : Rel A B) (I : ByteArray) (f : Nat → Bool) (hI : ids I = (List.range R.n.toNat).filter f)
    (hk : Vals.PickFits A R.key (ids I)) (hv : Vals.PickFits B R.val (ids I)) (a : A.El) (b : B.El) :
    (R.rows I).Holds a b ↔ ∃ i : Fin R.n.toNat, R.key.row i = a ∧ R.val.row i = b ∧ f i.1 = true := by
  have hmemI : ∀ i, i ∈ ids I ↔ i < R.n.toNat ∧ f i = true := fun i => by
    rw [hI, List.mem_filter, List.mem_range]
  have hlen : len I < USize.size := by
    rw [len_eq_ids, hI]
    exact Nat.lt_of_le_of_lt (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_range ..)))
      R.n.toNat_lt_size
  obtain ⟨hn, hrow⟩ := rows_spec R _ hlen hk hv
  have hids : ∀ q (hq : q < (ids I).length), (ids I)[q] = (Column.bitsAt I (q * 8) 8).toNat :=
    fun q hq => by simp [ids]
  constructor
  · rintro ⟨⟨q, hq⟩, ha, hb⟩
    have hq' : q < (ids I).length := by rw [← len_eq_ids, ← hn]; exact hq
    have hp : (Column.bitsAt I (q * 8) 8).toNat ∈ ids I := by
      rw [← hids q hq']; exact List.getElem_mem hq'
    obtain ⟨hpn, hbit⟩ := (hmemI _).1 hp
    have e := hrow q hq
    rw [dif_pos hpn] at e
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    exact ⟨⟨_, hpn⟩, e1.symm.trans ha, e2.symm.trans hb, hbit⟩
  · rintro ⟨i, hia, hib, hbit⟩
    obtain ⟨q, hq', hqe⟩ := List.getElem_of_mem ((hmemI _).2 ⟨i.2, hbit⟩)
    have hq : q < (R.rows I).n.toNat := by rw [hn, len_eq_ids]; exact hq'
    have hv' : (Column.bitsAt I (q * 8) 8).toNat = i.1 := by rw [← hids q hq', hqe]
    have hpn : (Column.bitsAt I (q * 8) 8).toNat < R.n.toNat := by rw [hv']; exact i.2
    have e := hrow q hq
    rw [dif_pos hpn] at e
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    exact ⟨⟨q, hq⟩, e1.trans ((congrArg R.key.row (Fin.ext hv')).trans hia),
      e2.trans ((congrArg R.val.row (Fin.ext hv')).trans hib)⟩

/-- **`rep (R ∩ S) = rep R ∩ rep S`**: `∩` keeps the rows of `R` whose pair `S` holds (`pairs_member`,
    `whereBits_ids`), read back by `rows_keep`. Hypotheses: the joint pair codes faithful and well formed (`hc`),
    and `R`'s two columns picking back at the kept rows. -/
theorem rep_inter (R S : Rel A B) (hc : pairsOK(R, S)) (hk : Vals.PickFits A R.key (ids (hits)))
    (hv : Vals.PickFits B R.val (ids (hits))) : rep (R ∩ S) = rep R ∩ rep S :=
  hom_ext fun a b => by
    show (R.rows (hits)).Holds a b ↔ R.Holds a b ∧ S.Holds a b
    rw [rows_keep R _ _ (whereBits_ids R.n _).1 hk hv]
    constructor
    · rintro ⟨i, hia, hib, hbit⟩
      obtain ⟨j, hj1, hj2⟩ := (pairs_member R S hc i.2).1 hbit
      exact ⟨⟨i, hia, hib⟩, ⟨j, hj1.trans hia, hj2.trans hib⟩⟩
    · rintro ⟨⟨i, hia, hib⟩, ⟨j, hja, hjb⟩⟩
      exact ⟨i, hia, hib, (pairs_member R S hc i.2).2 ⟨j, hja.trans hia.symm, hjb.trans hib.symm⟩⟩

/-- **`rep (R − S) = rep R − rep S`**, pointwise (`Rel(Set)` names no difference): `−` keeps the rows of `R` whose
    pair `S` does not hold (`anti_ids`, `pairs_member`), read back by `rows_keep` as `∩`. Hypotheses: `rep_inter`'s,
    at the rows `anti` keeps. -/
theorem rep_diff (R S : Rel A B) (hc : pairsOK(R, S)) (hk : Vals.PickFits A R.key (ids (misses(R, S))))
    (hv : Vals.PickFits B R.val (ids (misses(R, S)))) (a : A.El) (b : B.El) :
    rep (R \ S) a b ↔ rep R a b ∧ ¬ rep S a b := by
  obtain ⟨hw0, hn0, hs0, -⟩ := hc.2 (k := 0) (by decide)
  obtain ⟨hw1, -, hs1, -⟩ := hc.2 (k := 1) (by decide)
  have hI := (anti_ids _ _ hw0 hw1 hs0 hs1).1
  replace hn0 : ((pairs #v[R, S])[0]'Nat.zero_lt_two).n = R.n := hn0
  rw [hn0] at hI
  show (R.rows (misses(R, S))).Holds a b ↔ R.Holds a b ∧ ¬ S.Holds a b
  rw [rows_keep R _ _ hI hk hv]
  have hnot : ∀ x : Bool, (!x) = true ↔ ¬ x = true := by decide
  constructor
  · rintro ⟨i, hia, hib, hbit⟩
    exact ⟨⟨i, hia, hib⟩, fun ⟨j, hja, hjb⟩ =>
      (hnot _).1 hbit ((pairs_member R S hc i.2).2 ⟨j, hja.trans hia.symm, hjb.trans hib.symm⟩)⟩
  · rintro ⟨⟨i, hia, hib⟩, hS⟩
    refine ⟨i, hia, hib, (hnot _).2 fun hbit => hS ?_⟩
    obtain ⟨j, hj1, hj2⟩ := (pairs_member R S hc i.2).1 hbit
    exact ⟨j, hj1.trans hia, hj2.trans hib⟩

/-- `rep_inter` at atom sides: the kept rows are rows of `R` (`whereBits_ids`), so both columns fit outright. -/
theorem rep_inter_atoms {t t' : QAtomicType} (R S : Rel (.atom t) (.atom t'))
    (hc : (∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat}
        (hi : i < ((#v[⟨R.n, (R.key, R.val)⟩, ⟨S.n, (S.key, S.val)⟩] : Vector (Part (.prod (.atom t) (.atom t'))) 2)[k]'hk).1.toNat)
        (hj : j < ((#v[⟨R.n, (R.key, R.val)⟩, ⟨S.n, (S.key, S.val)⟩] : Vector (Part (.prod (.atom t) (.atom t'))) 2)[l]'hl).1.toNat),
        Column.idAt ((pairs #v[R, S])[k]'hk).b
            ((pairs #v[R, S])[k]'hk).w i =
          Column.idAt ((pairs #v[R, S])[l]'hl).b
            ((pairs #v[R, S])[l]'hl).w j ↔
        Vals.row (A := .prod (.atom t) (.atom t'))
            ((#v[⟨R.n, (R.key, R.val)⟩, ⟨S.n, (S.key, S.val)⟩] : Vector (Part (.prod (.atom t) (.atom t'))) 2)[k]'hk).2 ⟨i, hi⟩ =
          Vals.row (A := .prod (.atom t) (.atom t'))
            ((#v[⟨R.n, (R.key, R.val)⟩, ⟨S.n, (S.key, S.val)⟩] : Vector (Part (.prod (.atom t) (.atom t'))) 2)[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < 2),
        let c := (pairs #v[R, S])[k]'hk
        laneOK(c.w) ∧
        c.n = ((#v[⟨R.n, (R.key, R.val)⟩, ⟨S.n, (S.key, S.val)⟩] : Vector (Part (.prod (.atom t) (.atom t'))) 2)[k]'hk).1 ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) :
    rep (R ∩ S) = rep R ∩ rep S :=
  have hlt : ∀ f ∈ ids (whereBits R.n (((pairs #v[R, S])[0]'Nat.zero_lt_two).member ((pairs #v[R, S])[1]'Nat.one_lt_two))),
      f < R.n.toNat := fun f hf => by
    obtain ⟨hI, -, hmemI⟩ := whereBits_ids R.n (((pairs #v[R, S])[0]'Nat.zero_lt_two).member ((pairs #v[R, S])[1]'Nat.one_lt_two))
    rw [hI] at hf; exact ((hmemI _).1 hf).1
  rep_inter R S hc (pickFits_atom _ hlt) (pickFits_atom _ hlt)

/-- **`(R ⊑ S) = true ↔ rep R ⊑ rep S`**: `⊑` counts the rows of `R` whose pair `S` holds (`pairs_member`), all
    `R.n` of them exactly when every pair of `R` is one of `S`. Hypothesis: the joint pair codes (`hc`); nothing is
    picked. -/
theorem rep_le (R S : Rel A B) (hc : pairsOK(R, S)) : (R ⊑ S) = true ↔ rep R ⊑ rep S := by
  obtain ⟨hI, -, -⟩ := whereBits_ids R.n (((pairs #v[R, S])[0]'Nat.zero_lt_two).member ((pairs #v[R, S])[1]'Nat.one_lt_two))
  show (len (hits) == R.n.toNat) = true ↔ _
  rw [beq_iff_eq, len_eq_ids, hI, le_iff]
  constructor
  · rintro h a b ⟨i, hia, hib⟩
    have hall := List.filter_eq_self.1 (List.filter_sublist.eq_of_length (by simpa using h)) i.1
      (List.mem_range.2 i.2)
    obtain ⟨j, h1, h2⟩ := (pairs_member R S hc i.2).1 hall
    exact ⟨j, h1.trans hia, h2.trans hib⟩
  · intro h
    rw [List.filter_eq_self.2 fun i hi => (pairs_member R S hc (List.mem_range.1 hi)).2
      (h _ _ ⟨⟨i, List.mem_range.1 hi⟩, rfl, rfl⟩), List.length_range]

/-- **`(R == S) = true ↔ rep R = rep S`**: `==` is `⊑` both ways (`rep_le` twice). Hypotheses: the joint pair codes
    in both orders, `pairs #v[R, S]` and `pairs #v[S, R]` — two code spaces, neither a permutation of the other. -/
theorem rep_eq (R S : Rel A B) (hc : pairsOK(R, S)) (hc' : pairsOK(S, R)) : (R == S) = true ↔ rep R = rep S := by
  show ((R ⊑ S) && (S ⊑ R)) = true ↔ _
  rw [Bool.and_eq_true, rep_le R S hc, rep_le S R hc', le_iff, le_iff]
  exact ⟨fun ⟨h1, h2⟩ => hom_ext fun a b => ⟨h1 a b, h2 a b⟩,
    fun h => by rw [h]; exact ⟨fun _ _ x => x, fun _ _ x => x⟩⟩

/-! ### The joint pair codes from the keys' and the values' codes -/

/-- `pairs` is the product side's codes (`Obj.codes`) of the relations' pairs. -/
theorem pairs_eq_codes {p : Nat} (ds : Vector (Rel A B) p) :
    pairs ds = Obj.codes (.prod A B) (ds.map fun R => (⟨R.n, (R.key, R.val)⟩ : Part (.prod A B))) := by
  simp only [pairs, Obj.codes, Vector.map_map]; rfl

/-! ### `⟨R, S⟩`: the join on the keys -/

-- the keys `⟨R, S⟩` joins on, their codes, and the pairs the join answers, named as `pair` names them
set_option hygiene false in
local notation "kp(" R ", " S ")" => (#v[⟨Rel.n R, Rel.key R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part A) 2)
set_option hygiene false in
local notation "kc" => Obj.codes A kp(R, S)
set_option hygiene false in
local notation "kpairs" => ((List.range R.n.toNat).flatMap fun i => ((List.range S.n.toNat).filter fun j =>
  Column.idAt (kc[1]'Nat.one_lt_two).b (kc[1]'Nat.one_lt_two).w j ==
    Column.idAt (kc[0]'Nat.zero_lt_two).b (kc[0]'Nat.zero_lt_two).w i).map (i, ·))

/-- **`rep ⟨R, S⟩ = ⟨rep R, rep S⟩`** (`rpair`): `pair` joins the keys (`join_rows`) and picks `R.key`, `R.val` at
    the left rows, `S.val` at the right ones. Hypotheses: `rep_comp`'s, at the keys' joint codes (`hc`) and the
    three picked columns. -/
theorem rep_pair (R : Rel A B) (S : Rel A C) (hc : codesOK(kc, kp(R, S))) (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (kc[1]'Nat.one_lt_two).b (kc[1]'Nat.one_lt_two).w j ==
        Column.idAt (kc[0]'Nat.zero_lt_two).b (kc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (kc[1]'Nat.one_lt_two).b (kc[1]'Nat.one_lt_two).w j ==
        Column.idAt (kc[0]'Nat.zero_lt_two).b (kc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hA : Vals.PickFits A R.key ((kpairs).map Prod.fst)) (hB : Vals.PickFits B R.val ((kpairs).map Prod.fst))
    (hC : Vals.PickFits C S.val ((kpairs).map Prod.snd)) :
    rep (LeetQ.Rel.Alg.pair R S) = rpair (rep R) (rep S) := by
  obtain ⟨hF, hW⟩ := hc
  obtain ⟨hlw, hln, hls, -⟩ := hW (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hW (k := 1) (by decide)
  replace hln : (kc[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : (kc[1]'Nat.one_lt_two).n = S.n := hrn'
  obtain ⟨hlt, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
    (by rw [hln, hrn']; exact hMU)
  have hP := mem_joinPairs (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)
  rw [hln, hrn'] at hP
  refine hom_ext fun a p => ?_
  show (longCount "⟨R,S⟩" (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 fun m hm =>
      (⟨m, Vals.pickN A R.key (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1 m
          (hm ▸ join_len (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)),
        (Vals.pickN B R.val (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1 m
          (hm ▸ join_len (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)),
         Vals.pick C S.val (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 m hm)⟩ :
        Rel A (.prod B C))).Holds a p ↔ R.Holds a p.1 ∧ S.Holds a p.2
  unfold longCount need
  rw [dif_pos hlt]
  suffices H : ∀ (m : USize) (hmJ : len (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 = m.toNat),
      (⟨m, Vals.pickN A R.key (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1 m
          (hmJ ▸ join_len (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)),
        (Vals.pickN B R.val (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1 m
          (hmJ ▸ join_len (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)),
         Vals.pick C S.val (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 m hmJ)⟩ :
        Rel A (.prod B C)).Holds a p ↔ R.Holds a p.1 ∧ S.Holds a p.2 from H _ _
  intro m hmJ
  have e := hZ m hmJ
  rw [hln, hrn'] at e
  have hf1 : Vals.PickFits A R.key ((List.range m.toNat).map fun q =>
      (Column.bitsAt (fit m.toNat (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1) (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q =>
      (Column.bitsAt (fit m.toNat (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1) (q * 8) 8).toNat) =
        (kpairs).map Prod.fst by rw [e, List.map_map]; rfl]
    exact hA
  have hf2 : Vals.PickFits B R.val ((List.range m.toNat).map fun q =>
      (Column.bitsAt (fit m.toNat (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1) (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q =>
      (Column.bitsAt (fit m.toNat (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1) (q * 8) 8).toNat) =
        (kpairs).map Prod.fst by rw [e, List.map_map]; rfl]
    exact hB
  have hf3 : Vals.PickFits C S.val ((List.range m.toNat).map fun q =>
      (Column.bitsAt (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q =>
      (Column.bitsAt (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 (q * 8) 8).toNat) =
        (kpairs).map Prod.snd by rw [e, List.map_map]; rfl]
    exact hC
  -- row `q` of each picked column, at the pair `q` names
  have rk : ∀ (q : Fin m.toNat) (hin : (Column.bitsAt (fit m.toNat (join (kc[0]'Nat.zero_lt_two)
      (kc[1]'Nat.one_lt_two)).1) (q.1 * 8) 8).toNat < R.n.toNat),
      (Vals.pickN A R.key (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1 m
        (hmJ ▸ join_len (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two))).row q = R.key.row ⟨_, hin⟩ ∧
      (Vals.pickN B R.val (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1 m
        (hmJ ▸ join_len (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two))).row q = R.val.row ⟨_, hin⟩ :=
    fun q hin => by
      unfold Vals.pickN
      exact ⟨by rw [pick_row A R.key _ m _ hf1 q, dif_pos hin], by rw [pick_row B R.val _ m _ hf2 q, dif_pos hin]⟩
  have rs : ∀ (q : Fin m.toNat)
      (hin : (Column.bitsAt (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 (q.1 * 8) 8).toNat < S.n.toNat),
      (Vals.pick C S.val (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 m hmJ).row q = S.val.row ⟨_, hin⟩ :=
    fun q hin => by rw [pick_row C S.val _ m hmJ hf3 q, dif_pos hin]
  constructor
  · rintro ⟨q, ha, rfl⟩
    have hq : ((Column.bitsAt (fit m.toNat (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).1) (q.1 * 8) 8).toNat,
        (Column.bitsAt (join (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)).2 (q.1 * 8) 8).toNat) ∈ kpairs := by
      rw [e]; exact List.mem_map.2 ⟨q.1, List.mem_range.2 q.2, rfl⟩
    obtain ⟨hi, hj, he⟩ := (hP _ _).1 hq
    obtain ⟨k1, k2⟩ := rk q hi
    have hk := (hF (k := 1) (l := 0) (by decide) (by decide) hj hi).1 he
    exact ⟨⟨⟨_, hi⟩, k1.symm.trans ha, k2.symm⟩, ⟨_, hj⟩, hk.trans (k1.symm.trans ha), (rs q hj).symm⟩
  · rintro ⟨⟨i, hia, hib⟩, ⟨j, hja, hjc⟩⟩
    have he := (hF (k := 1) (l := 0) (by decide) (by decide) j.2 i.2).2 (hja.trans hia.symm)
    have hm := (hP i.1 j.1).2 ⟨i.2, j.2, he⟩
    rw [e] at hm
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hm
    obtain ⟨h1, h2⟩ := Prod.mk.inj hqe
    have hq' := List.mem_range.1 hq
    obtain ⟨k1, k2⟩ := rk ⟨q, hq'⟩ (by rw [h1]; exact i.2)
    refine ⟨⟨q, hq'⟩, k1.trans ((congrArg R.key.row (Fin.ext h1)).trans hia), Prod.ext ?_ ?_⟩
    · exact k2.trans ((congrArg R.val.row (Fin.ext h1)).trans hib)
    · exact (rs ⟨q, hq'⟩ (by rw [h2]; exact j.2)).trans ((congrArg S.val.row (Fin.ext h2)).trans hjc)

end Pairs

#print axioms rep_pair
#print axioms rep_inter
#print axioms rep_le

#print axioms rep_top
#print axioms rep_prod

#print axioms dom_corefl
#print axioms rep_dom
#print axioms rep_ran
#print axioms rep_dom_corefl
#print axioms rep_ran_corefl
#print axioms rep_sum
#print axioms rep_inl
#print axioms rep_inr

/-! ### union and junc -/

section UnionJunc

/-- Two parts' summed count, at its `USize`, is the two counts added. -/
theorem raze2_cnt {X : Obj} {n m : USize} (x : Vals X n) (y : Vals X m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part X)).toList.map fun c : Part X => c.1.toNat).sum < USize.size) :
    ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part X)).toList.map fun c : Part X => c.1.toNat).sum.toUSize.toNat =
      n.toNat + m.toNat := by
  rw [USize.toNat_ofNat_of_lt' hN]; simp

/-- Rows of heterogeneously equal sides, at one position, are equal: a side moved along a count equation, by
    whatever cast, keeps its rows. -/
theorem row_heq {X : Obj} {a b : USize} (v : Vals X a) (w : Vals X b) (i : Fin a.toNat) (j : Fin b.toNat)
    (hab : a = b) (hvw : HEq v w) (hij : i.1 = j.1) : Vals.row v i = Vals.row w j := by
  subst hab; cases hvw; obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j; simp only at hij; subst hij; rfl

/-- A relation whose key and value columns read, row by row, `R`'s rows and then `S`'s holds exactly the pairs
    of `R` and of `S`. -/
theorem holds_two {N : USize} (K : Vals A N) (V : Vals B N) (R S : Rel A B) (hn : N.toNat = R.n.toNat + S.n.toNat)
    (hK : ∀ k (hk : k < N.toNat), Vals.row K ⟨k, hk⟩ =
      if h : k < R.n.toNat then Vals.row R.key ⟨k, h⟩ else Vals.row S.key ⟨k - R.n.toNat, by omega⟩)
    (hV : ∀ k (hk : k < N.toNat), Vals.row V ⟨k, hk⟩ =
      if h : k < R.n.toNat then Vals.row R.val ⟨k, h⟩ else Vals.row S.val ⟨k - R.n.toNat, by omega⟩)
    (a : A.El) (b : B.El) : (⟨N, K, V⟩ : Rel A B).Holds a b ↔ R.Holds a b ∨ S.Holds a b := by
  constructor
  · rintro ⟨⟨k, hk⟩, ha, hb⟩
    rw [hK k hk] at ha; rw [hV k hk] at hb
    by_cases h : k < R.n.toNat
    · rw [dif_pos h] at ha hb; exact Or.inl ⟨_, ha, hb⟩
    · rw [dif_neg h] at ha hb; exact Or.inr ⟨_, ha, hb⟩
  · rintro (⟨i, ha, hb⟩ | ⟨j, ha, hb⟩)
    · refine ⟨⟨i.1, show i.1 < N.toNat by omega⟩, ?_, ?_⟩
      · rw [hK, dif_pos i.2]; exact ha
      · rw [hV, dif_pos i.2]; exact hb
    · have hj : ¬ (R.n.toNat + j.1 < R.n.toNat) := by omega
      refine ⟨⟨R.n.toNat + j.1, show R.n.toNat + j.1 < N.toNat by omega⟩, ?_, ?_⟩
      · rw [hK, dif_neg hj]; simp only [Nat.add_sub_cancel_left]; exact ha
      · rw [hV, dif_neg hj]; simp only [Nat.add_sub_cancel_left]; exact hb

/-- **`rep [R, S] = [rep R, rep S]`**, the mediating relation of `Rel(Set)`'s coproduct (`sumCop`). The keys are
    `sumVals R.key S.key` (`sumVals_row`), the values `C.raze` of `R.val` and `S.val`, read back by `hC`
    (`RazeRow`). `hN`: the row count fits a `USize` (past it `[R, S]` answers `𝟘`); `h63`: it is at most `2^63`. -/
theorem rep_junc (R : Rel A C) (S : Rel B C) (hN : R.n.toNat + S.n.toNat < USize.size)
    (h63 : R.n.toNat + S.n.toNat ≤ 2 ^ 63)
    (hC : ∀ hN' k hk, Vals.row (C.raze #[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] hN') ⟨k, hk⟩ =
      if h : k < R.n.toNat then Vals.row R.val ⟨k, h⟩
      else Vals.row S.val ⟨k - R.n.toNat, by have := raze2_cnt R.val S.val hN'; omega⟩) :
    rep (LeetQ.Rel.Alg.junc R S) =
      Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R) (rep S) := by
  have hN' : ((#[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] : Array (Part C)).toList.map fun c : Part C => c.1.toNat).sum <
      USize.size := by simpa using hN
  have e : LeetQ.Rel.Alg.junc R S = ⟨R.n + S.n, sumVals R.key S.key hN,
      toUSize_eq (by rw [toNat_add_fits hN]) ▸ C.raze #[⟨_, R.val⟩, ⟨_, S.val⟩] hN'⟩ := by
    unfold LeetQ.Rel.Alg.junc need; rw [dif_pos hN]
  rw [e]
  refine hom_ext fun s c => ?_
  have hval : ∀ k : Fin (R.n + S.n).toNat, Vals.row (toUSize_eq (by rw [toNat_add_fits hN]) ▸
      C.raze #[⟨_, R.val⟩, ⟨_, S.val⟩] hN' : Vals C (R.n + S.n)) k =
      if h : k.1 < R.n.toNat then Vals.row R.val ⟨k.1, h⟩
      else Vals.row S.val ⟨k.1 - R.n.toNat, by have := Nat.lt_of_lt_of_eq k.2 (toNat_add_fits hN); omega⟩ :=
    fun k => by
      have hk' : k.1 < ((#[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] : Array (Part C)).toList.map
          fun c : Part C => c.1.toNat).sum.toUSize.toNat := by
        rw [raze2_cnt _ _ hN']; exact Nat.lt_of_lt_of_eq k.2 (toNat_add_fits hN)
      refine Eq.trans ?_ (hC hN' k.1 hk')
      apply row_heq
      all_goals first | rfl | exact eqRec_heq _ _ | exact eq_mpr_heq _ _ | exact cast_heq _ _ |
        exact (toUSize_eq (by rw [toNat_add_fits hN])).symm | simp
  show (∃ k, Vals.row (A := .sum A B) (sumVals R.key S.key hN) k = s ∧ Vals.row _ k = c) ↔
    (∃ a, s = Sum.inl a ∧ R.Holds a c) ∨ (∃ b, s = Sum.inr b ∧ S.Holds b c)
  constructor
  · rintro ⟨k, hs, hc⟩
    rw [sumVals_row _ _ hN h63] at hs; rw [hval] at hc
    by_cases hk : k.1 < R.n.toNat
    · rw [dif_pos hk] at hs hc; exact Or.inl ⟨_, hs.symm, ⟨k.1, hk⟩, rfl, hc⟩
    · rw [dif_neg hk] at hs hc; exact Or.inr ⟨_, hs.symm, _, rfl, hc⟩
  · have hk2 : ∀ k : Nat, k < R.n.toNat + S.n.toNat → k < (R.n + S.n).toNat := fun k h => by
      rw [toNat_add_fits hN]; exact h
    rintro (⟨a, rfl, i, rfl, rfl⟩ | ⟨b, rfl, j, rfl, rfl⟩)
    · refine ⟨⟨i.1, hk2 _ (by omega)⟩, ?_, ?_⟩
      · rw [sumVals_row _ _ hN h63, dif_pos i.2]
      · rw [hval, dif_pos i.2]
    · have hj : ¬ (R.n.toNat + j.1 < R.n.toNat) := by omega
      refine ⟨⟨R.n.toNat + j.1, hk2 _ (by omega)⟩, ?_, ?_⟩
      · rw [sumVals_row _ _ hN h63, dif_neg hj]; simp only [Nat.add_sub_cancel_left]
      · rw [hval, dif_neg hj]; simp only [Nat.add_sub_cancel_left]


end UnionJunc

#print axioms rep_junc

end LeetQ.Rel.Rep
