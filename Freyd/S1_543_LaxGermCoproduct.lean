/-
  §1.543 (lax) — `objIncl i` PRESERVES BINARY COPRODUCTS in the FILTERED lax colimit.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the LAX port of `Colim.objIncl_preserves_coproducts` (`ColimitCoproductGerm.lean`), and
  the EXACT COPRODUCT DUAL of `LaxColim.objInclL_preserves_products` (`LaxGermProducts.lean`).

  Given a `LaxCatSystem L` with `Coherent L` and the lax binary-coproduct preservation bundle
  `LaxCoproductData L` (per-fibre coproducts + transition joint-epic preservation `pres` + transition
  copairing preservation `presCase`), the canonical comparison

      `case (stageInclL inl) (stageInclL inr) : ⟨i,a⟩ +_lax ⟨i,b⟩ ⟶ ⟨i, a+b⟩`

  INTO the INCLUDED stage coproduct `objIncl i (a+b) = ⟨i, (hcop i).coprod a b⟩` is an ISO in
  `laxColimCat L hL`.  (Here `+_lax` is the colimit coproduct `coprObj L data a b` at the common bound
  `prK D i i`, built by `laxColimHasBinaryCoproducts`.)

  PROOF (via the generic `Colim.isIso_of_coproduct_up`).  The cocone `(⟨i,a+b⟩, stageInclL inl,
  stageInclL inr)` is itself a universal coproduct cocone:

    * UNIQUENESS (joint epimorphy) — `homInclL_epiCase_of_stage`, the lax mirror of
      `Colim.colimHom_epiCase_of_rep`, built here.  Two competitor germs agreeing after BOTH
      injections (on the LEFT) are pushed to a common bound where `data.pres` (the fibre's joint-epic
      preservation) forces them equal; the leading coherence isos (`prUnit`/`transApp`/`reflApp`) are
      stripped by pre-composition.  This generic helper is the joint dual of
      `LaxColim.homInclL_monicPair_of_stage`.

    * EXISTENCE — push the competitors `f,g` to a common stage `N ≥ i`, pre-compose with the inverse
      unit conjugator `isoInv prUnit` (the lax analogue of the strict castHom that lands the
      competitor SOURCE in `F hiN a`), apply `data.presCase` to get the mediator germ `r`, and bake
      `prUnit` into the included representative so the injection's trailing `isoInv prUnit` factor
      cancels.  This mirrors `LaxColim.coprCaseExists` (the lax coproduct's copairing), specialised to
      the cocone whose coproduct object is the stage coproduct `⟨i, a+b⟩` rather than the colimit
      coproduct `coprObj`.

  Mirrors `objInclL_preserves_products` line-by-line, flipping product→coproduct
  (pair/fst/snd → case/inl/inr; isIso_of_product_up → isIso_of_coproduct_up; monicPair/joint-mono →
  epiCase/joint-epi; mediator OUT of coproduct via `presCase`).  Mathlib-free.
-/
module

public import Freyd.S1_543_RatCapHcanon
public import Freyd.S1_543_LaxColimitCoproduct
public import Freyd.S1_543_ColimitCoproductGerm

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}
variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) (data : LaxCoproductData L)

/-! ## Joint epimorphy of two single-stage injection germs (lax `colimHom_epiCase_of_rep`)

  Two germs `xP ⟶ W`, `xP ⟶ W` out of the reflexive-codomain bound `⟨k0, hia, refl k0⟩` into a
  common coproduct-stage object `xP : L.A k0` are jointly right-cancellable, PROVIDED every pair of
  stage maps out of `L.F hk0n xP` agreeing after `(functF hk0n).map injA` and after
  `(functF hk0n).map injB` (on the LEFT) is already equal (`hcancel`).  This is the joint dual of
  `LaxColim.homInclL_monicPair_of_stage`, and the lax mirror of `Colim.colimHom_epiCase_of_rep`.

  PROOF.  Reduce both injection-composites of two competitor germs to single germs (`coprCompProj`),
  extract a common bound from the two germ equalities, fold the level pushes by `coprPsi_push`, strip
  the leading `transApp` by pre-composition, and apply `hcancel` to the `isoInv prUnit`-conjugated
  representatives; cancel `isoInv prUnit` to obtain the germ witness.  This is `coprJointEpi`'s
  argument with the per-fibre `data.pres` abstracted to the hypothesis `hcancel` and the coproduct
  object left generic. -/
public theorem homInclL_epiCase_of_stage
    {k0 ia ib : ι} (xP : L.A k0) (xa : L.A ia) (xb : L.A ib)
    (hia : D.le ia k0) (hib : D.le ib k0)
    (injA : L.F hia xa ⟶ xP) (injB : L.F hib xb ⟶ xP)
    (hcancel : ∀ {n : ι} (hk0n : D.le k0 n) (Zt : L.A n)
        (u v : L.F hk0n xP ⟶ Zt),
        (L.functF hk0n).map injA ≫ u = (L.functF hk0n).map injA ≫ v →
        (L.functF hk0n).map injB ≫ u = (L.functF hk0n).map injB ≫ v → u = v)
    {W : Obj L} (h₁ h₂ : homL L hL ⟨k0, xP⟩ W)
    (hf : @compL _ _ L hL ⟨ia, xa⟩ ⟨k0, xP⟩ W
        (homInclL L hL xa xP ⟨k0, hia, D.refl k0⟩ (injA ≫ isoInv (reflApp_isIso L xP))) h₁
      = @compL _ _ L hL ⟨ia, xa⟩ ⟨k0, xP⟩ W
        (homInclL L hL xa xP ⟨k0, hia, D.refl k0⟩ (injA ≫ isoInv (reflApp_isIso L xP))) h₂)
    (hs : @compL _ _ L hL ⟨ib, xb⟩ ⟨k0, xP⟩ W
        (homInclL L hL xb xP ⟨k0, hib, D.refl k0⟩ (injB ≫ isoInv (reflApp_isIso L xP))) h₁
      = @compL _ _ L hL ⟨ib, xb⟩ ⟨k0, xP⟩ W
        (homInclL L hL xb xP ⟨k0, hib, D.refl k0⟩ (injB ≫ isoInv (reflApp_isIso L xP))) h₂) :
    h₁ = h₂ := by
  letI : Cat (Obj L) := laxColimCat L hL
  revert hf hs
  refine Quotient.inductionOn₂ h₁ h₂ (fun rh₁ rh₂ hf hs => ?_)
  obtain ⟨a₁, m₁⟩ := rh₁
  obtain ⟨a₂, m₂⟩ := rh₂
  -- reduce both injection composites to single germs at a common bound `e ≥ a₁.1, a₂.1, k0`.
  obtain ⟨w0, hw0a, hw0b⟩ := D.bound a₁.1 a₂.1
  obtain ⟨e, hew, hek⟩ := D.bound w0 k0
  have ha₁e : D.le a₁.1 e := D.trans hw0a hew
  have ha₂e : D.le a₂.1 e := D.trans hw0b hew
  rw [coprCompProj L hL xa xP W.2 hia injA a₁ m₁ e hek ha₁e,
      coprCompProj L hL xa xP W.2 hia injA a₂ m₂ e hek ha₂e] at hf
  rw [coprCompProj L hL xb xP W.2 hib injB a₁ m₁ e hek ha₁e,
      coprCompProj L hL xb xP W.2 hib injB a₂ m₂ e hek ha₂e] at hs
  -- extract germ relations from `hf`/`hs`, then a common bound `n`.
  obtain ⟨cf, hcf1, hcf2, eqf⟩ := Quotient.exact hf
  obtain ⟨cs, hcs1, hcs2, eqs⟩ := Quotient.exact hs
  obtain ⟨n, hcfn, hcsn⟩ := D.bound cf.1 cs.1
  simp only [homSystemL] at eqf eqs
  -- fold the pushes of `coprPsi` to the level `cf.1`/`cs.1`, then on to `n`.
  rw [coprPsi_push L hL xa xP W.2 hia injA a₁ m₁ e cf.1 hek ha₁e hcf1,
      coprPsi_push L hL xa xP W.2 hia injA a₂ m₂ e cf.1 hek ha₂e hcf2] at eqf
  rw [coprPsi_push L hL xb xP W.2 hib injB a₁ m₁ e cs.1 hek ha₁e hcs1,
      coprPsi_push L hL xb xP W.2 hib injB a₂ m₂ e cs.1 hek ha₂e hcs2] at eqs
  have eqf' := congrArg (pushHom L xa W.2 (D.trans hia (D.trans hek hcf1))
      (D.trans a₁.2.2 (D.trans ha₁e hcf1)) hcfn) eqf
  have eqs' := congrArg (pushHom L xb W.2 (D.trans hib (D.trans hek hcs1))
      (D.trans a₁.2.2 (D.trans ha₁e hcs1)) hcsn) eqs
  rw [coprPsi_push L hL xa xP W.2 hia injA a₁ m₁ cf.1 n _ _ hcfn,
      coprPsi_push L hL xa xP W.2 hia injA a₂ m₂ cf.1 n _ _ hcfn] at eqf'
  rw [coprPsi_push L hL xb xP W.2 hib injB a₁ m₁ cs.1 n _ _ hcsn,
      coprPsi_push L hL xb xP W.2 hib injB a₂ m₂ cs.1 n _ _ hcsn] at eqs'
  -- unfold `coprPsi` and fold the injection germ to `transApp ≫ map inj ≫ isoInv prUnit`.
  unfold coprPsi at eqf' eqs'
  rw [pushHom_inj L xa xP hia _ injA] at eqf'
  rw [pushHom_inj L xb xP hib _ injB] at eqs'
  -- level data at `n`.
  have hkn : D.le k0 n := D.trans hek (D.trans hcf1 hcfn)
  have ha₁n : D.le a₁.1 n := D.trans ha₁e (D.trans hcf1 hcfn)
  have ha₂n : D.le a₂.1 n := D.trans ha₂e (D.trans hcf1 hcfn)
  -- the `isoInv prUnit`-conjugated reps `u₁,u₂ : F(k0≤n) xP ⟶ F(W.1≤n) W.2`.
  let u₁ : L.F hkn xP ⟶ L.F (D.trans a₁.2.2 ha₁n) W.2 :=
    isoInv (prUnit_isIso L xP hkn) ≫ pushHom L xP W.2 a₁.2.1 a₁.2.2 ha₁n m₁
  let u₂ : L.F hkn xP ⟶ L.F (D.trans a₂.2.2 ha₂n) W.2 :=
    isoInv (prUnit_isIso L xP hkn) ≫ pushHom L xP W.2 a₂.2.1 a₂.2.2 ha₂n m₂
  -- cancel the leading `transApp` (pre-compose with `isoInv transApp`).
  have hinl : (L.functF hkn).map injA ≫ u₁ = (L.functF hkn).map injA ≫ u₂ := by
    have := congrArg (isoInv (transApp_isIso L hia hkn xa) ≫ ·) eqf'
    simp only [← Cat.assoc, inv_isoInv_comp, Cat.id_comp] at this
    simpa only [u₁, u₂, Cat.assoc] using this
  have hinr : (L.functF hkn).map injB ≫ u₁ = (L.functF hkn).map injB ≫ u₂ := by
    have := congrArg (isoInv (transApp_isIso L hib hkn xb) ≫ ·) eqs'
    simp only [← Cat.assoc, inv_isoInv_comp, Cat.id_comp] at this
    simpa only [u₁, u₂, Cat.assoc] using this
  -- joint cancellation gives `u₁ = u₂`; cancel `isoInv prUnit` to get the germ witness.
  have huv : u₁ = u₂ :=
    hcancel hkn (L.F (D.trans a₁.2.2 ha₁n) W.2) u₁ u₂ hinl hinr
  have hmm : pushHom L xP W.2 a₁.2.1 a₁.2.2 ha₁n m₁ = pushHom L xP W.2 a₂.2.1 a₂.2.2 ha₂n m₂ := by
    have h2 := congrArg (prUnit L xP hkn ≫ ·) huv
    simpa only [u₁, u₂, ← Cat.assoc, isoInv_comp, Cat.id_comp] using h2
  exact Quotient.sound ⟨⟨n, hkn, D.trans a₁.2.2 ha₁n⟩, ha₁n, ha₂n, hmm⟩

/-! ## `objIncl i` preserves the stage coproduct `(hcop i).coprod a b`

  Mirrors `Colim.objIncl_preserves_coproducts`; the coproduct dual of `objInclL_preserves_products`. -/
public theorem objInclL_preserves_coproducts (i : ι) (a b : L.A i) :
    @IsIso (Obj L) (laxColimCat L hL) _ _
      (@HasBinaryCoproducts.case (Obj L) (laxColimCat L hL) (laxColimHasBinaryCoproducts L hL data)
        (objIncl L i ((data.hcop i).coprod a b)) (objIncl L i a) (objIncl L i b)
        (stageInclL L hL ((data.hcop i).inl (A := a) (B := b)))
        (stageInclL L hL ((data.hcop i).inr (A := a) (B := b)))) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasBinaryCoproducts (Obj L) := laxColimHasBinaryCoproducts L hL data
  let P0 : L.A i := (data.hcop i).coprod a b
  let inlS : a ⟶ P0 := (data.hcop i).inl
  let inrS : b ⟶ P0 := (data.hcop i).inr
  -- joint epimorphy (uniqueness half) of the two stage injections.  The hcancel hypothesis is the
  -- helper's `map injA`-cancellation, reduced to the fibre's `data.pres` by stripping the leading
  -- `reflApp` alignment iso (dual of the products consumer's trailing-iso strip).
  have hcancel : ∀ {n : ι} (hk0n : D.le i n) (Zt : L.A n)
      (u v : L.F hk0n P0 ⟶ Zt),
      (L.functF hk0n).map (reflApp L a ≫ inlS) ≫ u = (L.functF hk0n).map (reflApp L a ≫ inlS) ≫ v →
      (L.functF hk0n).map (reflApp L b ≫ inrS) ≫ u = (L.functF hk0n).map (reflApp L b ≫ inrS) ≫ v →
      u = v := by
    intro n hk0n Zt u v hu hv
    refine data.pres hk0n a b Zt u v ?_ ?_
    · have key := congrArg ((L.functF hk0n).map (isoInv (reflApp_isIso L a)) ≫ ·) hu
      rw [(L.functF hk0n).map_comp (reflApp L a) inlS] at key
      simp only [← Cat.assoc] at key
      rw [← (L.functF hk0n).map_comp (isoInv (reflApp_isIso L a)) (reflApp L a),
          inv_isoInv_comp, (L.functF hk0n).map_id, Cat.id_comp] at key
      exact key
    · have key := congrArg ((L.functF hk0n).map (isoInv (reflApp_isIso L b)) ≫ ·) hv
      rw [(L.functF hk0n).map_comp (reflApp L b) inrS] at key
      simp only [← Cat.assoc] at key
      rw [← (L.functF hk0n).map_comp (isoInv (reflApp_isIso L b)) (reflApp L b),
          inv_isoInv_comp, (L.functF hk0n).map_id, Cat.id_comp] at key
      exact key
  -- joint epimorphy over the two `stageInclL` injections, from the generic helper.  `hbrL`/`hbrR`
  -- re-associate the `stageInclL` germ `reflApp ≫ inj ≫ isoInv reflApp` into the helper's
  -- `(reflApp ≫ inj) ≫ isoInv reflApp` form (the products consumer needed no such bridge because its
  -- alignment iso is the LEADING `reflApp`).
  have hbrL : stageInclL L hL inlS
      = homInclL L hL a P0 ⟨i, D.refl i, D.refl i⟩
        ((reflApp L a ≫ inlS) ≫ isoInv (reflApp_isIso L P0)) := by
    unfold stageInclL; rw [← Cat.assoc]
  have hbrR : stageInclL L hL inrS
      = homInclL L hL b P0 ⟨i, D.refl i, D.refl i⟩
        ((reflApp L b ≫ inrS) ≫ isoInv (reflApp_isIso L P0)) := by
    unfold stageInclL; rw [← Cat.assoc]
  have hEC : ∀ {W : Obj L} (s t : homL L hL ⟨i, P0⟩ W),
      @compL _ _ L hL ⟨i, a⟩ ⟨i, P0⟩ W (stageInclL L hL inlS) s
        = @compL _ _ L hL ⟨i, a⟩ ⟨i, P0⟩ W (stageInclL L hL inlS) t →
      @compL _ _ L hL ⟨i, b⟩ ⟨i, P0⟩ W (stageInclL L hL inrS) s
        = @compL _ _ L hL ⟨i, b⟩ ⟨i, P0⟩ W (stageInclL L hL inrS) t → s = t := by
    intro W s t h1 h2
    rw [hbrL] at h1
    rw [hbrR] at h2
    exact homInclL_epiCase_of_stage L hL P0 a b (D.refl i) (D.refl i)
      (reflApp L a ≫ inlS) (reflApp L b ≫ inrS) hcancel s t h1 h2
  refine isIso_of_coproduct_up _ _ (fun {Z} f g => ?_)
  -- existence half: build the case mediator OUT of `⟨i,P0⟩` at a common stage `N ≥ i`.
  refine Quotient.inductionOn f (fun rf => ?_)
  refine Quotient.inductionOn g (fun rg => ?_)
  obtain ⟨af, fa⟩ := rf
  obtain ⟨bg, ga⟩ := rg
  obtain ⟨e1, he1a, he1b⟩ := D.bound af.1 bg.1
  obtain ⟨N, hNe, hiN⟩ := D.bound e1 i
  have hafN : D.le af.1 N := D.trans he1a hNe
  have hbgN : D.le bg.1 N := D.trans he1b hNe
  -- competitor legs at `N`, pre-composed with the inverse unit conjugator `isoInv prUnit` (lands the
  -- SOURCE in `F hiN a/b`).
  let p_case : L.F hiN a ⟶ L.F (D.trans af.2.2 hafN) Z.2 :=
    isoInv (prUnit_isIso L a hiN) ≫ pushHom L a Z.2 af.2.1 af.2.2 hafN fa
  let q_case : L.F hiN b ⟶ L.F (D.trans af.2.2 hafN) Z.2 :=
    isoInv (prUnit_isIso L b hiN) ≫ pushHom L b Z.2 bg.2.1 bg.2.2 hbgN ga
  obtain ⟨r, hr_inl, hr_inr⟩ := data.presCase hiN a b (L.F (D.trans af.2.2 hafN) Z.2) p_case q_case
  let u : @homL _ _ L hL ⟨i, P0⟩ Z :=
    homInclL L hL P0 Z.2 ⟨N, hiN, D.trans af.2.2 hafN⟩ (prUnit L P0 hiN ≫ r)
  -- `coprCaseExists.leg`, specialised: an injection composite of `u` reduces to the pushed competitor.
  have leg : ∀ (w : L.A i) (injS : w ⟶ P0)
      (aw : UpperBound D i Z.1) (wa : L.F aw.2.1 w ⟶ L.F aw.2.2 Z.2) (hawN : D.le aw.1 N),
      (L.functF hiN).map (reflApp L w ≫ injS) ≫ r
          = isoInv (transApp_isIso L (D.refl i) hiN w) ≫ pushHom L w Z.2 aw.2.1 aw.2.2 hawN wa →
      @compL _ _ L hL ⟨i, w⟩ ⟨i, P0⟩ Z (stageInclL L hL injS) u
        = Quotient.mk (setoid (homSystemL L hL w Z.2)) ⟨aw, wa⟩ := by
    intro w injS aw wa hawN hcomp
    have hbr : stageInclL L hL injS
        = homInclL L hL w P0 ⟨i, D.refl i, D.refl i⟩
          ((reflApp L w ≫ injS) ≫ isoInv (reflApp_isIso L P0)) := by
      unfold stageInclL; rw [← Cat.assoc]
    rw [hbr]
    show homCompRawL L hL w P0 Z.2 ⟨i, D.refl i, D.refl i⟩
        ((reflApp L w ≫ injS) ≫ isoInv (reflApp_isIso L P0))
        ⟨N, hiN, D.trans af.2.2 hafN⟩ (prUnit L P0 hiN ≫ r)
      = homInclL L hL w Z.2 aw wa
    rw [homCompRawL_eq_compAtL L hL w P0 Z.2 ⟨i, D.refl i, D.refl i⟩
          ((reflApp L w ≫ injS) ≫ isoInv (reflApp_isIso L P0))
          ⟨N, hiN, D.trans af.2.2 hafN⟩ (prUnit L P0 hiN ≫ r) N hiN (D.refl N)]
    unfold compAtL
    rw [hL.push_refl P0 Z.2 hiN (D.trans af.2.2 hafN) (prUnit L P0 hiN ≫ r),
        pushHom_inj L w P0 (D.refl i) hiN (reflApp L w ≫ injS)]
    rw [Cat.assoc, Cat.assoc, ← Cat.assoc (isoInv (prUnit_isIso L P0 hiN)),
        inv_isoInv_comp, Cat.id_comp, hcomp, ← Cat.assoc, isoInv_comp, Cat.id_comp]
    exact homInclL_compat L hL w Z.2 (a := aw)
      (b := ⟨N, D.trans aw.2.1 hawN, D.trans aw.2.2 hawN⟩) hawN wa
  -- the alignment identity `map reflApp ≫ isoInv prUnit = isoInv transApp` (dual of products `hpu`).
  have hpu : ∀ (w : L.A i),
      (L.functF hiN).map (reflApp L w) ≫ isoInv (prUnit_isIso L w hiN)
        = isoInv (transApp_isIso L (D.refl i) hiN w) := by
    intro w
    rw [isoInv_prUnit L w hiN, ← Cat.assoc,
        ← (L.functF hiN).map_comp (reflApp L w) (isoInv (reflApp_isIso L w)),
        isoInv_comp, (L.functF hiN).map_id, Cat.id_comp]
  have hcomp_inl : (L.functF hiN).map (reflApp L a ≫ inlS) ≫ r
      = isoInv (transApp_isIso L (D.refl i) hiN a) ≫ pushHom L a Z.2 af.2.1 af.2.2 hafN fa := by
    rw [(L.functF hiN).map_comp (reflApp L a) inlS, Cat.assoc, hr_inl]
    show (L.functF hiN).map (reflApp L a)
        ≫ (isoInv (prUnit_isIso L a hiN) ≫ pushHom L a Z.2 af.2.1 af.2.2 hafN fa) = _
    rw [← Cat.assoc, hpu a]
  have hcomp_inr : (L.functF hiN).map (reflApp L b ≫ inrS) ≫ r
      = isoInv (transApp_isIso L (D.refl i) hiN b) ≫ pushHom L b Z.2 bg.2.1 bg.2.2 hbgN ga := by
    rw [(L.functF hiN).map_comp (reflApp L b) inrS, Cat.assoc, hr_inr]
    show (L.functF hiN).map (reflApp L b)
        ≫ (isoInv (prUnit_isIso L b hiN) ≫ pushHom L b Z.2 bg.2.1 bg.2.2 hbgN ga) = _
    rw [← Cat.assoc, hpu b]
  have hux : @compL _ _ L hL ⟨i, a⟩ ⟨i, P0⟩ Z (stageInclL L hL inlS) u = Quotient.mk _ ⟨af, fa⟩ :=
    leg a inlS af fa hafN hcomp_inl
  have huy : @compL _ _ L hL ⟨i, b⟩ ⟨i, P0⟩ Z (stageInclL L hL inrS) u = Quotient.mk _ ⟨bg, ga⟩ :=
    leg b inrS bg ga hbgN hcomp_inr
  exact ⟨u, ⟨hux, huy⟩, fun v hv₁ hv₂ => hEC v u (hv₁.trans hux.symm) (hv₂.trans huy.symm)⟩

end Freyd.LaxColim
