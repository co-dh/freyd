/-
  M3-cov ingredient (dual): `objIncl i` preserves binary COPRODUCTS.

  The exact dual of `objIncl_preserves_products` (CatColimitRegular).  Given
  per-stage binary coproducts (`hcop`) and the transition-preservation hypotheses
  (`hcoppres`, `hcoppres_case`) that build `colimitHasBinaryCoproducts`, the
  canonical comparison `case (homInclObj inl) (homInclObj inr) :
  coprod (objIncl i a) (objIncl i b) ⟶ objIncl i (a + b)` is an iso in
  `colimitCat`.  Everything here is the formal dual of the products development:
  products `pair/fst/snd` ↦ coproducts `case/inl/inr`, and the joint-MONO of two
  same-domain germs (`colimHom_monicPair_of_rep`) becomes the joint-EPI of two
  same-codomain germs (`colimHom_epiCase_of_rep`).
-/

module

public import Freyd.S1_543_CatColimitRegular

open Freyd

namespace Freyd.Colim

universe u w

variable {ι : Type u} {D : Directed ι}

/-- **Generic comparison-iso from a coproduct universal property** (dual of
    `isIso_of_product_up`).  In a category with binary coproducts, if a cocone
    `(P, i₁, i₂)` under `A, B` is universal (`hup`: unique mediator out of `P` for
    every competitor), then the canonical comparison `case i₁ i₂ : coprod A B ⟶ P`
    is an isomorphism.  The inverse is the mediator of `(inl, inr)`; the two
    round-trips collapse by `case_uniq` (on the `coprod A B` side) and the UP
    uniqueness (on the `P` side). -/
public theorem isIso_of_coproduct_up {𝒞 : Type w} [Cat.{w} 𝒞] [HasBinaryCoproducts 𝒞]
    {A B P : 𝒞} (i₁ : A ⟶ P) (i₂ : B ⟶ P)
    (hup : ∀ {Z : 𝒞} (f : A ⟶ Z) (g : B ⟶ Z),
      ∃ u : P ⟶ Z, (i₁ ≫ u = f ∧ i₂ ≫ u = g) ∧
        ∀ v : P ⟶ Z, i₁ ≫ v = f → i₂ ≫ v = g → v = u) :
    IsIso (HasBinaryCoproducts.case i₁ i₂ : HasBinaryCoproducts.coprod A B ⟶ P) := by
  obtain ⟨u, ⟨hu₁, hu₂⟩, _⟩ :=
    hup (HasBinaryCoproducts.inl (A := A) (B := B)) (HasBinaryCoproducts.inr (A := A) (B := B))
  refine ⟨u, ?_, ?_⟩
  · -- `case i₁ i₂ ≫ u = id (coprod A B)`: both copairing-determined, compare via `case_uniq`
    have e1 : HasBinaryCoproducts.inl ≫ (HasBinaryCoproducts.case i₁ i₂ ≫ u)
        = HasBinaryCoproducts.inl := by rw [← Cat.assoc, HasBinaryCoproducts.case_inl, hu₁]
    have e2 : HasBinaryCoproducts.inr ≫ (HasBinaryCoproducts.case i₁ i₂ ≫ u)
        = HasBinaryCoproducts.inr := by rw [← Cat.assoc, HasBinaryCoproducts.case_inr, hu₂]
    rw [HasBinaryCoproducts.case_uniq _ _ (HasBinaryCoproducts.case i₁ i₂ ≫ u) e1 e2,
        HasBinaryCoproducts.case_uniq _ _ (Cat.id (HasBinaryCoproducts.coprod A B))
          (Cat.comp_id _) (Cat.comp_id _)]
  · -- `u ≫ case i₁ i₂ = id P`: both identity-like on `P`, compare via the UP uniqueness
    obtain ⟨_, _, huniq⟩ := hup i₁ i₂
    have e1 : i₁ ≫ (u ≫ HasBinaryCoproducts.case i₁ i₂) = i₁ := by
      rw [← Cat.assoc, hu₁, HasBinaryCoproducts.case_inl]
    have e2 : i₂ ≫ (u ≫ HasBinaryCoproducts.case i₁ i₂) = i₂ := by
      rw [← Cat.assoc, hu₂, HasBinaryCoproducts.case_inr]
    rw [huniq (u ≫ HasBinaryCoproducts.case i₁ i₂) e1 e2,
        huniq (Cat.id P) (Cat.comp_id _) (Cat.comp_id _)]

/-- **Two same-codomain germs are jointly EPIC in `colimitCat` when jointly
    cancellable under transitions** (joint dual of `colimHom_monicPair_of_rep`).
    Both germs `f₀ : A → P`, `f₁ : B → P` share the codomain rep `xP` at carrier
    `L`; if every pair of stage maps agreeing after `f₀` and after `f₁` (on the
    LEFT) is already equal (`hcancel`), then the two `homIncl`-germs are jointly
    right-cancellable.  Push the two competitors `s, t : P → W` to a common stage,
    where both leg-equations become stage equations, and apply `hcancel`. -/
public theorem colimHom_epiCase_of_rep (C : CatSystem ι D) (hC : C.Coherent)
    {P A B : C.Obj} {L : ι}
    (hpd : D.le (colimOut C P).1 L) (hca : D.le (colimOut C A).1 L) (hcb : D.le (colimOut C B).1 L)
    (f₀ : C.F hca (colimOut C A).2 ⟶ C.F hpd (colimOut C P).2)
    (f₁ : C.F hcb (colimOut C B).2 ⟶ C.F hpd (colimOut C P).2)
    (hcancel : ∀ {j : ι} (hjk : D.le L j) (z : C.A j)
        (u v : C.F hjk (C.F hpd (colimOut C P).2) ⟶ z),
        C.Fmap hjk f₀ ≫ u = C.Fmap hjk f₀ ≫ v →
        C.Fmap hjk f₁ ≫ u = C.Fmap hjk f₁ ≫ v → u = v)
    {W : C.Obj}
    (s t : colimHom C hC P W)
    (hf : colimComp C hC (homIncl C hC (colimOut C A).2 (colimOut C P).2 ⟨L, hca, hpd⟩ f₀) s
        = colimComp C hC (homIncl C hC (colimOut C A).2 (colimOut C P).2 ⟨L, hca, hpd⟩ f₀) t)
    (hs : colimComp C hC (homIncl C hC (colimOut C B).2 (colimOut C P).2 ⟨L, hcb, hpd⟩ f₁) s
        = colimComp C hC (homIncl C hC (colimOut C B).2 (colimOut C P).2 ⟨L, hcb, hpd⟩ f₁) t) :
    s = t := by
  letI : Cat C.Obj := colimitCat C hC
  let xP := (colimOut C P).2; let xA := (colimOut C A).2; let xB := (colimOut C B).2
  let xW : C.A (colimOut C W).1 := (colimOut C W).2
  revert hf hs
  refine Quotient.inductionOn₂ s t (fun pr qr hf hs => ?_)
  obtain ⟨ap, p₀⟩ := pr
  obtain ⟨aq, q₀⟩ := qr
  -- reduce both leg-equations to common-stage germ equations (germ `f₀`/`f₁` on the LEFT)
  change homCompRaw C hC xA xP xW ⟨L, hca, hpd⟩ f₀ ap p₀
       = homCompRaw C hC xA xP xW ⟨L, hca, hpd⟩ f₀ aq q₀ at hf
  change homCompRaw C hC xB xP xW ⟨L, hcb, hpd⟩ f₁ ap p₀
       = homCompRaw C hC xB xP xW ⟨L, hcb, hpd⟩ f₁ aq q₀ at hs
  obtain ⟨P1, hapP1, haqP1⟩ := D.bound ap.1 aq.1
  obtain ⟨Q, hP1Q, hLQ⟩ := D.bound P1 L
  have hapQ : D.le ap.1 Q := D.trans hapP1 hP1Q
  have haqQ : D.le aq.1 Q := D.trans haqP1 hP1Q
  rw [homCompRaw_eq_compAt C hC xA xP xW ⟨L, hca, hpd⟩ f₀ ap p₀ Q hLQ hapQ,
      homCompRaw_eq_compAt C hC xA xP xW ⟨L, hca, hpd⟩ f₀ aq q₀ Q hLQ haqQ] at hf
  rw [homCompRaw_eq_compAt C hC xB xP xW ⟨L, hcb, hpd⟩ f₁ ap p₀ Q hLQ hapQ,
      homCompRaw_eq_compAt C hC xB xP xW ⟨L, hcb, hpd⟩ f₁ aq q₀ Q hLQ haqQ] at hs
  obtain ⟨Rf, hRfp, hRfq, hRfeq⟩ := Quotient.exact hf
  obtain ⟨Rs, hRsp, hRsq, hRseq⟩ := Quotient.exact hs
  dsimp only [homSystem] at hRfeq hRseq
  obtain ⟨Lf, hRfL, hRsL⟩ := D.bound Rf.1 Rs.1
  have keyf := congrArg (homTr C xA xW Rf ⟨Lf, D.trans Rf.2.1 hRfL, D.trans Rf.2.2 hRfL⟩ hRfL) hRfeq
  have keys := congrArg (homTr C xB xW Rs ⟨Lf, D.trans Rs.2.1 hRsL, D.trans Rs.2.2 hRsL⟩ hRsL) hRseq
  rw [← homTr_trans C hC, ← homTr_trans C hC] at keyf
  rw [← homTr_trans C hC, ← homTr_trans C hC] at keys
  rw [homTr_comp C, homTr_comp C] at keyf
  rw [homTr_comp C, homTr_comp C] at keys
  rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at keyf
  rw [← homTr_trans C hC, ← homTr_trans C hC, ← homTr_trans C hC] at keys
  -- push f₀ (via Rf) and f₁ (via Rs) to the common stage Lf
  have hLLf : D.le L Lf := D.trans hLQ (D.trans hRfp hRfL)
  have hiAL : D.le (colimOut C A).1 Lf := D.trans hca hLLf
  have hiBL : D.le (colimOut C B).1 Lf := D.trans hcb hLLf
  have hiPL : D.le (colimOut C P).1 Lf := D.trans hpd hLLf
  have hHcA : C.F hLLf (C.F hpd xP) = C.F hiPL xP := (C.F_trans hpd hLLf xP).symm
  have hHcA2 : C.F hLLf (C.F hca xA) = C.F hiAL xA := (C.F_trans hca hLLf xA).symm
  have hHcB2 : C.F hLLf (C.F hcb xB) = C.F hiBL xB := (C.F_trans hcb hLLf xB).symm
  have hpush_f0 : homTr C xA xP ⟨L, hca, hpd⟩ ⟨Lf, hiAL, hiPL⟩ hLLf f₀
      = castHom hHcA2 hHcA (C.Fmap hLLf f₀) := rfl
  have hpush_f1 : homTr C xB xP ⟨L, hcb, hpd⟩ ⟨Lf, hiBL, hiPL⟩ hLLf f₁
      = castHom hHcB2 hHcA (C.Fmap hLLf f₁) := rfl
  rw [hpush_f0] at keyf
  rw [hpush_f1] at keys
  -- cast slides (dual: domain/codomain swapped vs. the products `cR`/`cT`)
  have cR : ∀ {U V V' Wq : C.A Lf} (he : V = V') (c : U ⟶ V') (m : V ⟶ Wq),
      c ≫ castHom he rfl m = castHom rfl he.symm c ≫ m := by
    intro _ _ _ _ he c m; subst he; rfl
  have cT : ∀ {U U' V Wq : C.A Lf} (he : U = U') (b : U ⟶ V) (c : V ⟶ Wq),
      castHom he rfl (b ≫ c) = castHom he rfl b ≫ c := by
    intro _ _ _ _ he b c; subst he; rfl
  have hbig : D.le ap.1 Lf := D.trans hapQ (D.trans hRfp hRfL)
  have hbig' : D.le aq.1 Lf := D.trans haqQ (D.trans hRfp hRfL)
  refine Quotient.sound ⟨⟨Lf, D.trans ap.2.1 hbig, D.trans ap.2.2 hbig⟩, hbig, hbig', ?_⟩
  dsimp only [homSystem]
  have hu := hcancel hLLf (C.F (D.trans ap.2.2 hbig) xW)
    (castHom hHcA.symm rfl (homTr C xP xW ap ⟨Lf, D.trans ap.2.1 hbig, D.trans ap.2.2 hbig⟩ hbig p₀))
    (castHom hHcA.symm rfl (homTr C xP xW aq ⟨Lf, D.trans aq.2.1 hbig', D.trans aq.2.2 hbig'⟩ hbig' q₀))
    (by
      rw [cR, cR]
      have hh := congrArg (castHom hHcA2.symm rfl) keyf
      rw [cT, cT, castHom_castHom] at hh
      exact hh)
    (by
      rw [cR, cR]
      have hh := congrArg (castHom hHcB2.symm rfl) keys
      rw [cT, cT, castHom_castHom] at hh
      exact hh)
  have hu2 := congrArg (castHom hHcA rfl) hu
  rw [castHom_castHom, castHom_castHom] at hu2
  exact hu2

/-- **`objIncl i` preserves binary coproducts** (M3-cov ingredient, dual of
    `objIncl_preserves_products`).  Given per-stage coproducts (`hcop`) and the
    transition-preservation hypotheses (`hcoppres`, `hcoppres_case`) that build
    `colimitHasBinaryCoproducts`, the canonical comparison
    `case (homInclObj inl) (homInclObj inr) : coprod (objIncl a) (objIncl b) ⟶
    objIncl (a + b)` is an iso in `colimitCat`. -/
public theorem objIncl_preserves_coproducts (C : CatSystem ι D) (hC : C.Coherent)
    (hcop : ∀ i, HasBinaryCoproducts (C.A i))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hcop i).coprod a b) ⟶ z),
        C.Fmap hij (hcop i).inl ≫ u = C.Fmap hij (hcop i).inl ≫ v →
        C.Fmap hij (hcop i).inr ≫ u = C.Fmap hij (hcop i).inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hcop i).coprod a b) ⟶ z,
          C.Fmap hij (hcop i).inl ≫ r = p ∧ C.Fmap hij (hcop i).inr ≫ r = q)
    (i : ι) (a b : C.A i) :
    @IsIso C.Obj (colimitCat C hC) _ _
      (@HasBinaryCoproducts.case C.Obj (colimitCat C hC)
        (colimitHasBinaryCoproducts C hC hcop hcoppres hcoppres_case)
        (C.objIncl i ((hcop i).coprod a b)) (C.objIncl i a) (C.objIncl i b)
        (homInclObj C hC ((hcop i).inl (A := a) (B := b)))
        (homInclObj C hC ((hcop i).inr (A := a) (B := b)))) := by
  letI : Cat C.Obj := colimitCat C hC
  letI : HasBinaryCoproducts C.Obj := colimitHasBinaryCoproducts C hC hcop hcoppres hcoppres_case
  let P0 : C.A i := (hcop i).coprod a b
  let inlS : a ⟶ P0 := (hcop i).inl
  let inrS : b ⟶ P0 := (hcop i).inr
  let xa : C.A (colimOut C (C.objIncl i a)).1 := (colimOut C (C.objIncl i a)).2
  let xb : C.A (colimOut C (C.objIncl i b)).1 := (colimOut C (C.objIncl i b)).2
  let xcop : C.A (colimOut C (C.objIncl i P0)).1 := (colimOut C (C.objIncl i P0)).2
  show @IsIso C.Obj (colimitCat C hC) _ _
    (@HasBinaryCoproducts.case C.Obj (colimitCat C hC)
      (colimitHasBinaryCoproducts C hC hcop hcoppres hcoppres_case)
      (C.objIncl i P0) (C.objIncl i a) (C.objIncl i b)
      (homInclObj C hC inlS) (homInclObj C hC inrS))
  obtain ⟨ka, hpa, hia, heqa⟩ := Quotient.exact (colimOut_spec C (C.objIncl i a))
  obtain ⟨kb, hpb, hib, heqb⟩ := Quotient.exact (colimOut_spec C (C.objIncl i b))
  obtain ⟨kP, hpP, hiP, heqP⟩ := Quotient.exact (colimOut_spec C (C.objIncl i P0))
  dsimp only [CatSystem.objSystem] at heqa heqb heqP
  obtain ⟨m1, hkam, hkbm⟩ := D.bound ka kb
  obtain ⟨L, hm1L, hkPL⟩ := D.bound m1 kP
  have hkaL : D.le ka L := D.trans hkam hm1L
  have hkbL : D.le kb L := D.trans hkbm hm1L
  have hiL : D.le i L := D.trans hia hkaL
  have hgaL : C.F (D.trans hpa hkaL) xa = C.F hiL a := by
    rw [C.F_trans hpa hkaL, heqa, ← C.F_trans hia hkaL]
  have hgbL : C.F (D.trans hpb hkbL) xb = C.F hiL b := by
    rw [C.F_trans hpb hkbL, heqb, show hiL = D.trans hib hkbL from Subsingleton.elim _ _,
        ← C.F_trans hib hkbL]
  have hgPL : C.F (D.trans hpP hkPL) xcop = C.F hiL P0 := by
    rw [C.F_trans hpP hkPL, heqP, show hiL = D.trans hiP hkPL from Subsingleton.elim _ _,
        ← C.F_trans hiP hkPL]
  let wF : HioWitness C a P0 := ⟨L, D.trans hpa hkaL, D.trans hpP hkPL, hiL, hgaL, hgPL⟩
  let wS : HioWitness C b P0 := ⟨L, D.trans hpb hkbL, D.trans hpP hkPL, hiL, hgbL, hgPL⟩
  -- joint epimorphy of the two injections (uniqueness half)
  have hEC : ∀ {W : C.Obj} (s t : C.objIncl i P0 ⟶ W),
      homInclObj C hC inlS ≫ s = homInclObj C hC inlS ≫ t →
      homInclObj C hC inrS ≫ s = homInclObj C hC inrS ≫ t → s = t := by
    intro W s t h1 h2
    rw [homInclObj_eq C hC inlS wF] at h1
    rw [homInclObj_eq C hC inrS wS] at h2
    refine colimHom_epiCase_of_rep C hC (D.trans hpP hkPL) (D.trans hpa hkaL) (D.trans hpb hkbL)
      (wF.germ inlS) (wS.germ inrS) (fun {j} hjk z u v hu hv => ?_) s t h1 h2
    -- reduce both germ maps to `castHom ∘ functF.map`, apply `hcoppres`
    have e_P : C.F hjk (C.F (D.trans hpP hkPL) xcop) = C.F (D.trans hiL hjk) P0 :=
      (congrArg (C.F hjk) hgPL).trans (C.F_trans hiL hjk P0).symm
    have e_a : C.F hjk (C.F (D.trans hpa hkaL) xa) = C.F (D.trans hiL hjk) a :=
      (congrArg (C.F hjk) hgaL).trans (C.F_trans hiL hjk a).symm
    have e_b : C.F hjk (C.F (D.trans hpb hkbL) xb) = C.F (D.trans hiL hjk) b :=
      (congrArg (C.F hjk) hgbL).trans (C.F_trans hiL hjk b).symm
    have hmapF : C.Fmap hjk (wF.germ inlS)
        = castHom e_a.symm e_P.symm (C.Fmap (D.trans hiL hjk) inlS) := by
      dsimp only [HioWitness.germ]
      rw [C.Fmap_castHom hjk]
      exact castHom_heq_congr _ _ e_a.symm e_P.symm (hC.trans_map hiL hjk inlS).symm
    have hmapS : C.Fmap hjk (wS.germ inrS)
        = castHom e_b.symm e_P.symm (C.Fmap (D.trans hiL hjk) inrS) := by
      dsimp only [HioWitness.germ]
      rw [C.Fmap_castHom hjk]
      exact castHom_heq_congr _ _ e_b.symm e_P.symm (hC.trans_map hiL hjk inrS).symm
    have cR : ∀ {U V V' R : C.A j} (he : V = V') (c : U ⟶ V') (m : V ⟶ R),
        c ≫ castHom he rfl m = castHom rfl he.symm c ≫ m := by
      intro _ _ _ _ he c m; subst he; rfl
    have cT : ∀ {U U' V R : C.A j} (he : U = U') (b : U ⟶ V) (c : V ⟶ R),
        castHom he rfl (b ≫ c) = castHom he rfl b ≫ c := by
      intro _ _ _ _ he b c; subst he; rfl
    rw [hmapF] at hu
    rw [hmapS] at hv
    have huu : C.Fmap (D.trans hiL hjk) inlS ≫ (castHom e_P rfl u)
        = C.Fmap (D.trans hiL hjk) inlS ≫ (castHom e_P rfl v) := by
      apply castHom_injective e_a.symm rfl
      rw [cT, cT, cR, cR, castHom_castHom]; exact hu
    have hvv : C.Fmap (D.trans hiL hjk) inrS ≫ (castHom e_P rfl u)
        = C.Fmap (D.trans hiL hjk) inrS ≫ (castHom e_P rfl v) := by
      apply castHom_injective e_b.symm rfl
      rw [cT, cT, cR, cR, castHom_castHom]; exact hv
    exact castHom_injective e_P rfl
      (hcoppres (D.trans hiL hjk) a b z (castHom e_P rfl u) (castHom e_P rfl v) huu hvv)
  -- existence half: build the mediator at stage N
  refine isIso_of_coproduct_up _ _ (fun {Z} f g => ?_)
  refine Quotient.inductionOn f (fun ⟨af, fa⟩ => ?_)
  refine Quotient.inductionOn g (fun ⟨bg, ga⟩ => ?_)
  let z : C.A (colimOut C Z).1 := (colimOut C Z).2
  obtain ⟨m2, hafm, hbgm⟩ := D.bound af.1 bg.1
  obtain ⟨N, hm2N, hLN⟩ := D.bound m2 L
  have hafN : D.le af.1 N := D.trans hafm hm2N
  have hbgN : D.le bg.1 N := D.trans hbgm hm2N
  have hiN : D.le i N := D.trans hiL hLN
  have hgaN : C.F (D.trans (D.trans hpa hkaL) hLN) xa = C.F hiN a := by
    rw [C.F_trans (D.trans hpa hkaL) hLN, hgaL, ← C.F_trans hiL hLN]
  have hgbN : C.F (D.trans (D.trans hpb hkbL) hLN) xb = C.F hiN b := by
    rw [C.F_trans (D.trans hpb hkbL) hLN, hgbL, ← C.F_trans hiL hLN]
  have hgPN : C.F (D.trans (D.trans hpP hkPL) hLN) xcop = C.F hiN P0 := by
    rw [C.F_trans (D.trans hpP hkPL) hLN, hgPL, ← C.F_trans hiL hLN]
  let wFN : HioWitness C a P0 :=
    ⟨N, D.trans (D.trans hpa hkaL) hLN, D.trans (D.trans hpP hkPL) hLN, hiN, hgaN, hgPN⟩
  let wSN : HioWitness C b P0 :=
    ⟨N, D.trans (D.trans hpb hkbL) hLN, D.trans (D.trans hpP hkPL) hLN, hiN, hgbN, hgPN⟩
  -- competitor germs at N (now from `objIncl a`/`objIncl b` OUT to `Z`)
  let fL_raw : C.F (D.trans af.2.1 hafN) xa ⟶ C.F (D.trans af.2.2 hafN) z :=
    homTr C xa z af ⟨N, D.trans af.2.1 hafN, D.trans af.2.2 hafN⟩ hafN fa
  let gL_raw : C.F (D.trans bg.2.1 hbgN) xb ⟶ C.F (D.trans bg.2.2 hbgN) z :=
    homTr C xb z bg ⟨N, D.trans bg.2.1 hbgN, D.trans bg.2.2 hbgN⟩ hbgN ga
  have hzeq : C.F (D.trans bg.2.2 hbgN) z = C.F (D.trans af.2.2 hafN) z :=
    C.F_proof_irrel _ _ z
  have hfa_tgt : C.F (D.trans af.2.1 hafN) xa = C.F hiN a := by
    rw [show D.trans af.2.1 hafN = D.trans (D.trans hpa hkaL) hLN from Subsingleton.elim _ _]
    exact hgaN
  have hgb_tgt : C.F (D.trans bg.2.1 hbgN) xb = C.F hiN b := by
    rw [show D.trans bg.2.1 hbgN = D.trans (D.trans hpb hkbL) hLN from Subsingleton.elim _ _]
    exact hgbN
  let pL : C.F hiN a ⟶ C.F (D.trans af.2.2 hafN) z := castHom hfa_tgt rfl fL_raw
  let qL : C.F hiN b ⟶ C.F (D.trans af.2.2 hafN) z := castHom hgb_tgt hzeq gL_raw
  obtain ⟨r, hr_inl, hr_inr⟩ := hcoppres_case hiN a b (C.F (D.trans af.2.2 hafN) z) pL qL
  let rgerm : C.F (D.trans (D.trans hpP hkPL) hLN) xcop ⟶ C.F (D.trans af.2.2 hafN) z :=
    castHom hgPN.symm rfl r
  let u : C.objIncl i P0 ⟶ Z :=
    homIncl C hC xcop z ⟨N, D.trans (D.trans hpP hkPL) hLN, D.trans af.2.2 hafN⟩ rgerm
  have hux : homInclObj C hC inlS ≫ u = Quotient.mk _ ⟨af, fa⟩ := by
    show colimComp C hC (homInclObj C hC inlS) u = _
    rw [homInclObj_eq C hC inlS wFN]
    show homCompRaw C hC xa xcop z ⟨wFN.K, wFN.hpx, wFN.hpy⟩ (wFN.germ inlS)
        ⟨N, D.trans (D.trans hpP hkPL) hLN, D.trans af.2.2 hafN⟩ rgerm
      = homIncl C hC xa z af fa
    refine homCompRaw_eq_of_stage C hC xa xcop z
      ⟨wFN.K, wFN.hpx, wFN.hpy⟩ (wFN.germ inlS)
      ⟨N, D.trans (D.trans hpP hkPL) hLN, D.trans af.2.2 hafN⟩ rgerm af fa N (D.refl N) (D.refl N) hafN ?_
    rw [homTr_refl C hC, homTr_refl C hC]
    show castHom hgaN.symm hgPN.symm (C.Fmap hiN inlS) ≫ rgerm
      = homTr C xa z af ⟨N, D.trans af.2.1 hafN, D.trans af.2.2 hafN⟩ hafN fa
    show castHom hgaN.symm hgPN.symm (C.Fmap hiN inlS) ≫ castHom hgPN.symm rfl r = fL_raw
    rw [castHom_comp]
    rw [show C.Fmap hiN inlS ≫ r = pL from hr_inl]
    show castHom hgaN.symm rfl (castHom hfa_tgt rfl fL_raw) = fL_raw
    rw [castHom_castHom]
    exact castHom_of_heq _ rfl HEq.rfl
  have huy : homInclObj C hC inrS ≫ u = Quotient.mk _ ⟨bg, ga⟩ := by
    show colimComp C hC (homInclObj C hC inrS) u = _
    rw [homInclObj_eq C hC inrS wSN]
    show homCompRaw C hC xb xcop z ⟨wSN.K, wSN.hpx, wSN.hpy⟩ (wSN.germ inrS)
        ⟨N, D.trans (D.trans hpP hkPL) hLN, D.trans af.2.2 hafN⟩ rgerm
      = homIncl C hC xb z bg ga
    refine homCompRaw_eq_of_stage C hC xb xcop z
      ⟨wSN.K, wSN.hpx, wSN.hpy⟩ (wSN.germ inrS)
      ⟨N, D.trans (D.trans hpP hkPL) hLN, D.trans af.2.2 hafN⟩ rgerm bg ga N (D.refl N) (D.refl N) hbgN ?_
    rw [homTr_refl C hC, homTr_refl C hC]
    show castHom hgbN.symm hgPN.symm (C.Fmap hiN inrS) ≫ castHom hgPN.symm rfl r
      = homTr C xb z bg ⟨N, D.trans bg.2.1 hbgN, D.trans bg.2.2 hbgN⟩ hbgN ga
    rw [castHom_comp]
    rw [show C.Fmap hiN inrS ≫ r = qL from hr_inr]
    show castHom hgbN.symm rfl (castHom hgb_tgt hzeq gL_raw) = gL_raw
    rw [castHom_castHom]
    exact castHom_of_heq _ hzeq HEq.rfl
  -- assemble: mediator `u`, its two factorisations, uniqueness via `hEC`
  exact ⟨u, ⟨hux, huy⟩, fun v hv₁ hv₂ => hEC v u (hv₁.trans hux.symm) (hv₂.trans huy.symm)⟩

end Freyd.Colim
