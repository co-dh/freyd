/-
  The sum, order and arithmetic ops under the run-time bit, as `CRel` does for `≫`, `∩`, `∪`: each twin
  `inlC`/`inrC`/`juncC`/`sumC`/`ltC`/`leqC`/`succC`/`bagifyC` answers its relation and a bit deciding every count
  bound its read-back theorem takes, so `rep_<op>C` holds under that one bit.
-/
import LeetQ.Rel.CRel
import LeetQ.Rel.RepOrd

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open OpsN UnionN

variable {A B C D : Obj}

/-- **`rep (inl X) = X? ι₁` under `inlC`'s bit**: the bit is `rep_inl`'s `h63`. -/
theorem rep_inlC {n : USize} (X : Vals A n) (hb : (inlC (B := B) X).2 = true) :
    rep (inlC (B := B) X).1 = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun x => ∃ i, X.row i = x) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁ :=
  rep_inl X (of_decide_eq_true hb)

/-- **`rep (inr Y) = Y? ι₂` under `inrC`'s bit**: the bit is `rep_inr`'s `h63`. -/
theorem rep_inrC {n : USize} (Y : Vals B n) (hb : (inrC (A := A) Y).2 = true) :
    rep (inrC (A := A) Y).1 = corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun y => ∃ i, Y.row i = y) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂ :=
  rep_inr Y (of_decide_eq_true hb)

/-- **`rep [R, S] = [rep R, rep S]` under `juncC`'s bit**: `need`'s guard is `rep_junc_full`'s `hN`, the decided
    bound its `h63`, the raze's bit its `hF` (`razeC_fits`). -/
theorem rep_juncC (R : Rel A C) (S : Rel B C) (hb : (juncC R S).2 = true) :
    rep (juncC R S).1 = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R) (rep S) := by
  unfold juncC need at hb
  split at hb
  · rename_i hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact rep_junc_full R S hN hb.1 (Obj.razeC_fits C R.val S.val _ rfl _ hb.2)
  · exact absurd hb Bool.false_ne_true

/-- **`rep (R + S) = ι₁° rep R ι₁ ∪ ι₂° rep S ι₂` under `sumC`'s bit**: the bit is `rep_sum`'s `hN` and `h63`. -/
theorem rep_sumC (R : Rel A C) (S : Rel B D) (hb : (sumC R S).2 = true) :
    rep (sumC R S).1 =
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁° ≫ rep R ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₁) ∪
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂° ≫ rep S ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₂) := by
  simp only [sumC, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact rep_sum R S hb.1 hb.2

/-- **`rep (lt U)` under `ltC`'s bit**: the decided bounds are `rep_lt`'s `hN`, `h63`, the diff's pair codes' bit
    its `hc` (`codesC_fits`, `codes_faithful_wf`, `pairs_eq_codes`), the `fitsN` bits its `hk`, `hv`
    (`pickFits_of_fitsN`). -/
theorem rep_ltC {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general)
    (hb : (ltC U h).2 = true) (a b : Int64) :
    rep (ltC U h).1 a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a < b := by
  simp only [ltC, diffC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨hcb, hk⟩, hv⟩, hN⟩, h63⟩ := hb
  have hc := (codes_faithful_wf (.prod _ _) _ (Obj.codesC_fits (.prod _ _) _ hcb)).1
  have e : ∀ {α β : Type} (f : α → β) (a b : α), #v[a, b].map f = #v[f a, f b] := fun _ _ _ => by simp
  exact rep_lt U h hN h63 (ltRows U h) rfl (by rw [pairs_eq_codes, e]; exact hc)
    (pickFits_of_fitsN _ _ _ hk _ (by simp)) (pickFits_of_fitsN _ _ _ hv _ (by simp)) a b

/-- **`rep (leq U)` under `leqC`'s bit**: `ltC`'s bit gives `rep_leq`'s `rep_lt` hypotheses as in `rep_ltC`;
    `unionC`'s guard its `hNU`, its codes' bits `huK`, `huV` (`codesC_fits`, `codes_faithful_wf`), its `fitsN`
    bits `huk`, `huv`. The razes' bits go unused: `rep_leq` razes atoms, which fit by their count. -/
theorem rep_leqC {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general)
    (hb : (leqC U h).2 = true) (a b : Int64) :
    rep (leqC U h).1 a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a ≤ b := by
  change ((ltC U h).2 && (unionC (lt U h) (idU U)).2) = true at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨hl, hu⟩ := hb
  simp only [ltC, diffC, Bool.and_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨⟨⟨hcb, hk⟩, hv⟩, hN⟩, h63⟩ := hl
  have hc := (codes_faithful_wf (.prod _ _) _ (Obj.codesC_fits (.prod _ _) _ hcb)).1
  have e : ∀ {α β : Type} (f : α → β) (a b : α), #v[a, b].map f = #v[f a, f b] := fun _ _ _ => by simp
  unfold unionC need at hu
  split at hu
  · rename_i hNU
    simp only [Bool.and_eq_true] at hu
    obtain ⟨⟨⟨⟨⟨-, -⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hu
    -- a raze twin's `.1` is `raze` at each constructor of the side
    have hr : ∀ (X : Obj) (cs : Array (Part X)) h, (X.razeC cs h).1 = X.raze cs h := by
      intro X; cases X <;> intros <;> rfl
    simp only [hr] at hkc hvc hkf hvf
    have hK := (codes_faithful_wf _ _ (Obj.codesC_fits _ _ hkc)).1
    have hV := (codes_faithful_wf _ _ (Obj.codesC_fits _ _ hvc)).1
    exact rep_leq U h hN h63 (ltRows U h) rfl (by rw [pairs_eq_codes, e]; exact hc)
      (pickFits_of_fitsN _ _ _ hk _ (by simp)) (pickFits_of_fitsN _ _ _ hv _ (by simp)) hNU _ rfl
      ⟨fun hi hj => hK.1 (k := 0) (l := 0) Nat.zero_lt_one Nat.zero_lt_one hi hj, hK.2 (k := 0) Nat.zero_lt_one⟩
      ⟨fun hi hj => hV.1 (k := 0) (l := 0) Nat.zero_lt_one Nat.zero_lt_one hi hj, hV.2 (k := 0) Nat.zero_lt_one⟩
      (pickFits_of_fitsN _ _ _ hkf _ (by simp)) (pickFits_of_fitsN _ _ _ hvf _ (by simp)) a b
  · exact absurd hu Bool.false_ne_true

/-- **`rep (succ U)` under `succC`'s bit**: the codes' bit gives `rep_succ`'s `hc` (`codesC_fits`,
    `codes_faithful_wf`, less its `w < 8` clause). -/
theorem rep_succC {n : USize} (U : Vals (.atom .long) n) (hb : (succC U).2 = true) (u w : Int64) :
    rep (succC U).1 u w ↔ (∃ i, U.row i = u) ∧ w = Ew.intStep Ew.add nul u 1 ∧ ∃ j, U.row j = w := by
  have hc := (codes_faithful_wf (.atom .long) #v[⟨n, valCol Ew.add Ew.va (longsOf U) (one 1)⟩, ⟨n, U⟩]
    (Obj.codesC_fits (.atom .long) _ hb)).1
  exact rep_succ U _ rfl _ rfl
    ⟨@fun _ _ hk hl _ _ hi hj => hc.1 hk hl hi hj, fun hk => ⟨(hc.2 hk).1, (hc.2 hk).2.1, (hc.2 hk).2.2.1⟩⟩ u w

/-- **`expand`'s copies' count is the counts summed**, each count below `2^63` (`expand_idx`): the `O(1)` length a
    twin decides a count bound on, in place of folding the counts. -/
theorem len_expand_sum {n : USize} {cnt : ByteArray} (hl : len cnt = n.toNat)
    (hc : ∀ t < n.toNat, (Column.bitsAt cnt (t * 8) 8).toNat < 2 ^ 63) :
    len (expandBytes 8 0 (tilLongs n) cnt) =
      ((List.range n.toNat).map fun r => (Column.bitsAt cnt (r * 8) 8).toNat).sum := by
  rw [len_eq_ids, expand_idx (Nat.le_of_eq hl) (fun t ht => hc t (hl ▸ ht)), List.length_flatMap, hl]
  simp only [List.length_replicate]

/-- `expand` of an array side's counts copies their sum, the payload count below `2^63` (`slicesOf_row`). -/
theorem len_expand_slicesOf {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63) :
    len (expandBytes 8 0 (tilLongs n) (slicesOf X).2) =
      ((List.range n.toNat).map fun r => (Column.bitsAt (slicesOf X).2 (r * 8) 8).toNat).sum :=
  len_expand_sum (len_slices _ _ _ _).2 fun t ht => by have := (slicesOf_row X hp ht).1; omega

/-- **`rep (bagify X)` under `bagifyC`'s bit**: the decided bounds are `rep_bagify`'s `hp`, `hn`; inside `expand`
    the copies' count decided its `hS`, `expand`'s guard its `hU`, both through `len_expand_slicesOf`. -/
theorem rep_bagifyC {n : USize} (X : Vals (.arr (.atom .long)) n) (hb : (bagifyC X).2 = true) :
    ∀ xs ys, rep (bagifyC X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys.Perm xs ∧ ys.Pairwise (· ≤ ·) := by
  simp only [bagifyC, expand, need, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hp, hn⟩, hb⟩ := hb
  split at hb
  · rename_i hx
    simp only [decide_eq_true_eq] at hb
    rw [USize.toNat_ofNat_of_lt' hx, len_expand_slicesOf X hp] at hb
    rw [len_expand_slicesOf X hp] at hx
    exact rep_bagify X hp hn hb hx
  · exact absurd hb Bool.false_ne_true

#print axioms rep_juncC
#print axioms rep_ltC
#print axioms rep_leqC
#print axioms rep_succC
#print axioms rep_bagifyC

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ.Rel.Rep

variable {A B C D : Obj}

/-- `inl` on the universe `X`, ok where `inlC` ran within capacity. -/
def inl {n : USize} (X : Vals A n) : CRel A (.sum A B) := let r := inlC X; ⟨r.1, r.2⟩

/-- `inr` on the universe `Y`, ok where `inrC` ran within capacity. -/
def inr {n : USize} (Y : Vals B n) : CRel B (.sum A B) := let r := inrC Y; ⟨r.1, r.2⟩

/-- `[R, S]`, ok where both inputs are and `juncC` ran within capacity. -/
def junc (R : CRel A C) (S : CRel B C) : CRel (.sum A B) C := let r := juncC R.rel S.rel; ⟨r.1, R.ok && S.ok && r.2⟩

/-- `R + S`, ok where both inputs are and `sumC` ran within capacity. -/
def sum (R : CRel A C) (S : CRel B D) : CRel (.sum A B) (.sum C D) :=
  let r := sumC R.rel S.rel; ⟨r.1, R.ok && S.ok && r.2⟩

/-- `<` on `U`, ok where `ltC` ran within capacity. -/
def lt {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide) :
    CRel (.atom t) (.atom t) := let r := ltC U h; ⟨r.1, r.2⟩

/-- `≤` on `U`, ok where `leqC` ran within capacity. -/
def leq {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide) :
    CRel (.atom t) (.atom t) := let r := leqC U h; ⟨r.1, r.2⟩

/-- `succ` on `U`, ok where `succC` ran within capacity. -/
def succ {n : USize} (U : Vals (.atom .long) n) : CRel (.atom .long) (.atom .long) := let r := succC U; ⟨r.1, r.2⟩

/-- `bagify` on the arrays `X`, ok where `bagifyC` ran within capacity. -/
def bagify {B : Obj} {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := bagifyC X; ⟨r.1, r.2⟩

theorem rep_inl {n : USize} (X : Vals A n) (hb : (inl (B := B) X).ok = true) :
    rep (inl (B := B) X).rel = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun x => ∃ i, X.row i = x) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁ :=
  rep_inlC X hb

theorem rep_inr {n : USize} (Y : Vals B n) (hb : (inr (A := A) Y).ok = true) :
    rep (inr (A := A) Y).rel = corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun y => ∃ i, Y.row i = y) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂ :=
  rep_inrC Y hb

theorem rep_junc (R : CRel A C) (S : CRel B C) (hb : (R.junc S).ok = true) :
    rep (R.junc S).rel = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R.rel) (rep S.rel) :=
  rep_juncC R.rel S.rel (by simp only [junc, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_sum (R : CRel A C) (S : CRel B D) (hb : (R.sum S).ok = true) :
    rep (R.sum S).rel =
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁° ≫ rep R.rel ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₁) ∪
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂° ≫ rep S.rel ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₂) :=
  rep_sumC R.rel S.rel (by simp only [sum, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_lt {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general) (hb : (lt U h).ok = true)
    (a b : Int64) : rep (lt U h).rel a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a < b :=
  rep_ltC U h hb a b

theorem rep_leq {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general) (hb : (leq U h).ok = true)
    (a b : Int64) : rep (leq U h).rel a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a ≤ b :=
  rep_leqC U h hb a b

theorem rep_succ {n : USize} (U : Vals (.atom .long) n) (hb : (succ U).ok = true) (u w : Int64) :
    rep (succ U).rel u w ↔ (∃ i, U.row i = u) ∧ w = Ew.intStep Ew.add nul u 1 ∧ ∃ j, U.row j = w :=
  rep_succC U hb u w

theorem rep_bagify {n : USize} (X : Vals (.arr (.atom .long)) n) (hb : (bagify X).ok = true) :
    ∀ xs ys, rep (bagify X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys.Perm xs ∧ ys.Pairwise (· ≤ ·) :=
  rep_bagifyC X hb

end CRel

end LeetQ.Rel
