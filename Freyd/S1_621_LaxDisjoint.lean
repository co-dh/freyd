/-
  §1.621/§1.623 (lax) — the binary coproduct injections of the FILTERED lax colimit are MONIC and
  DISJOINT.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the LAX port of `Colim.colimit_inl_monic` / `colimit_inr_monic` / `colimit_inl_inter_inr`
  (`Freyd/ColimitPositive.lean`).  Together with the GENERIC constructor
  `disjointBinaryCoproduct_of_disjoint` (same file) — which derives the §1.621 union field
  `inl ∪ inr = ⊤` automatically — these three facts upgrade the lax colimit's binary coproducts
  (`laxColimHasBinaryCoproducts`, `Freyd/LaxColimitCoproduct.lean`) to a `DisjointBinaryCoproduct`,
  the positive-pre-logos rung the §2.218 regular capitalization tower needs.

  KEY DIFFERENCE FROM THE STRICT TEMPLATE.  The lax colimit's objects are the BARE Σ-type
  `Obj L = Σ i, L.A i` — NOT a quotient.  So the strict `objIncl_pair_commonStage` + `subst`
  (which made arbitrary `A, B` literally equal to `objIncl k`-objects) does NOT port: two objects
  `⟨iA, xA⟩` and `⟨k, F xA⟩` are only ISOMORPHIC, never equal.  We bridge this with the canonical
  inclusion germ `coprStageIncl x hik : ⟨i,x⟩ ≅ ⟨k, F hik x⟩` and the factorization

      `coprInl L hL data xA xB  =  coprStageIncl xA hik  ≫  stageInclL (hcop k).inl`             (★)

  (`homInclL_refl_factor`), which expresses the colimit injection `coprInl` (into the common-bound
  coproduct object `coprObj = ⟨k, (hcop k).coprod (F xA) (F xB)⟩ = objIncl k P0`) as the canonical
  iso followed by the SAME-STAGE germ injection `stageInclL (hcop k).inl`.  With (★):

    * MONIC — `coprStageIncl` is iso (`coprStageIncl_isIso`), `stageInclL (hcop k).inl` is monic
      (`stageInclL_mono_of_stage` + the per-stage `(hdisj k).inl_monic`); a monic pre-composed with an
      iso is monic (`mono_precomp_iso'`).

    * DISJOINT — the intersection's domain is the lax-colimit pullback `pbC` of `(coprInl, coprInr)`.
      Via (★) and `pbC`'s square, `(pbC.π₁ ≫ ν_A, pbC.π₂ ≫ ν_B)` is a cone over the germ cospan
      `(stageInclL inlS, stageInclL inrS)`; the keystone `stageInclFunctorL_preservesPullbacks`
      (`Freyd/RatCapHcanon.lean`) gives a mediator `m₁ : pbC.pt ⟶ objIncl k pdqₖ.pt` into the
      §1.432 stage pullback's `objIncl`.  That stage pullback is INITIAL (`disjoint_pullback_initial`,
      imported, from the per-stage §1.621 disjointness), so `m₁` followed by `stageInclL` of its
      universal map lands `pbC.pt` in the lax strict initial `objIncl k 0_k`
      (`laxColimStrictInitial`, `Freyd/LaxStrictInitial.lean`), a STRICT coterminator; hence the
      composite is iso and `pbC.pt` is initial.

  The genuinely generic helpers — `monic_inl/inr_of_factor`,
  `subobject_le_of_initial_dom`, `isInitial_of_iso`, `prelogos_bottom_strict/_initial`,
  `disjoint_pullback_initial` — are IMPORTED from `Freyd.ColimitPositive` (they mention no colimit).
  Mathlib-free; single universe `{w,w}` (forced by the pullback germ `stageInclFunctorL_preservesPullbacks`).
-/
import Freyd.S1_621_ColimitPositive
import Freyd.S1_543_LaxColimitCoproduct
import Freyd.S1_543_LaxGermImages
import Freyd.S1_61_LaxStrictInitial

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe w

variable {ι : Type w} {D : Directed ι}
variable (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L)

/-! ## The canonical inclusion germ `⟨i,x⟩ ≅ ⟨k, F hik x⟩` and the factorization (★) -/

/-- The canonical inclusion germ of `x : L.A i` into its push `F hik x : L.A k`: the germ of
    `isoInv reflApp : F hik x ⟶ F (refl k) (F hik x)` at the bound `⟨k, hik, refl k⟩`.  (It is the
    `inl`-side dual of the stage inclusion; an iso by `coprStageIncl_isIso`.) -/
noncomputable def coprStageIncl {i k : ι} (x : L.A i) (hik : D.le i k) :
    letI : Cat (Obj L) := laxColimCat L hL
    (⟨i, x⟩ : Obj L) ⟶ (⟨k, L.F hik x⟩ : Obj L) :=
  homInclL L hL x (L.F hik x) ⟨k, hik, D.refl k⟩ (isoInv (reflApp_isIso L (L.F hik x)))

/-- `coprStageIncl` is an isomorphism in `laxColimCat L hL`: its germ `isoInv reflApp` has the stage
    two-sided inverse `reflApp`, lifted by `homInclL_isIso_of_rep`. -/
theorem coprStageIncl_isIso {i k : ι} (x : L.A i) (hik : D.le i k) :
    @IsIso (Obj L) (laxColimCat L hL) _ _ (coprStageIncl L hL x hik) := by
  unfold coprStageIncl
  exact homInclL_isIso_of_rep L hL x (L.F hik x) ⟨k, hik, D.refl k⟩
    (isoInv (reflApp_isIso L (L.F hik x))) (reflApp L (L.F hik x))
    (inv_isoInv_comp _) (isoInv_comp _)

/-- **The factorization (★) at the reflexive bound.**  A germ of `g ≫ isoInv reflApp` (a stage-`k`
    map `g : F hik x ⟶ y` post-composed with the unit-collapse iso) at the bound `⟨k, hik, refl k⟩`
    equals the canonical inclusion `coprStageIncl x hik` followed by the same-stage germ inclusion
    `stageInclL g`.  PROOF: compose the two `homInclL` legs at the common bound `k`
    (`compL_homInclL_compAtL`); both pushes are along `refl k` (identity, `push_refl`); the middle
    `isoInv reflApp ≫ reflApp = id` cancels, leaving `g ≫ isoInv reflApp` at a defeq bound. -/
theorem homInclL_refl_factor {i k : ι} (x : L.A i) (y : L.A k) (hik : D.le i k)
    (g : L.F hik x ⟶ y) :
    letI : Cat (Obj L) := laxColimCat L hL
    homInclL L hL x y ⟨k, hik, D.refl k⟩ (g ≫ isoInv (reflApp_isIso L y))
      = (coprStageIncl L hL x hik) ≫ stageInclL L hL g := by
  letI : Cat (Obj L) := laxColimCat L hL
  show homInclL L hL x y ⟨k, hik, D.refl k⟩ (g ≫ isoInv (reflApp_isIso L y))
      = @compL _ _ L hL ⟨i, x⟩ ⟨k, L.F hik x⟩ ⟨k, y⟩
          (coprStageIncl L hL x hik) (stageInclL L hL g)
  unfold coprStageIncl stageInclL
  rw [compL_homInclL_compAtL L hL x (L.F hik x) y
        ⟨k, hik, D.refl k⟩ (isoInv (reflApp_isIso L (L.F hik x)))
        ⟨k, D.refl k, D.refl k⟩ (reflApp L (L.F hik x) ≫ g ≫ isoInv (reflApp_isIso L y))
        k (D.refl k) (D.refl k)]
  rw [hL.push_refl x (L.F hik x) hik (D.refl k) (isoInv (reflApp_isIso L (L.F hik x))),
      hL.push_refl (L.F hik x) y (D.refl k) (D.refl k)
        (reflApp L (L.F hik x) ≫ g ≫ isoInv (reflApp_isIso L y)),
      ← Cat.assoc (isoInv (reflApp_isIso L (L.F hik x))) (reflApp L (L.F hik x)),
      inv_isoInv_comp (reflApp_isIso L (L.F hik x)), Cat.id_comp]

/-- (★) for the LEFT injection: `coprInl L hL data xA xB = ν_A ≫ stageInclL (hcop k).inl`. -/
theorem coprInl_factor (data : LaxCoproductData L) {iA iB : ι} (xA : L.A iA) (xB : L.A iB) :
    letI : Cat (Obj L) := laxColimCat L hL
    coprInl L hL data xA xB
      = (coprStageIncl L hL xA (prK_le D iA iB).1)
          ≫ stageInclL L hL ((data.hcop (prK D iA iB)).inl
              (A := L.F (prK_le D iA iB).1 xA) (B := L.F (prK_le D iA iB).2 xB)) :=
  homInclL_refl_factor L hL xA
    ((data.hcop (prK D iA iB)).coprod (L.F (prK_le D iA iB).1 xA) (L.F (prK_le D iA iB).2 xB))
    (prK_le D iA iB).1
    ((data.hcop (prK D iA iB)).inl (A := L.F (prK_le D iA iB).1 xA) (B := L.F (prK_le D iA iB).2 xB))

/-- (★) for the RIGHT injection: `coprInr L hL data xA xB = ν_B ≫ stageInclL (hcop k).inr`. -/
theorem coprInr_factor (data : LaxCoproductData L) {iA iB : ι} (xA : L.A iA) (xB : L.A iB) :
    letI : Cat (Obj L) := laxColimCat L hL
    coprInr L hL data xA xB
      = (coprStageIncl L hL xB (prK_le D iA iB).2)
          ≫ stageInclL L hL ((data.hcop (prK D iA iB)).inr
              (A := L.F (prK_le D iA iB).1 xA) (B := L.F (prK_le D iA iB).2 xB)) :=
  homInclL_refl_factor L hL xB
    ((data.hcop (prK D iA iB)).coprod (L.F (prK_le D iA iB).1 xA) (L.F (prK_le D iA iB).2 xB))
    (prK_le D iA iB).2
    ((data.hcop (prK D iA iB)).inr (A := L.F (prK_le D iA iB).1 xA) (B := L.F (prK_le D iA iB).2 xB))

/-! ## The lax coproduct data sourced from per-stage DISJOINT coproducts -/

/-- The lax binary-coproduct preservation bundle `LaxCoproductData` built from per-stage disjoint
    coproducts: `hcop i := (hdisj i).toHasBinaryCoproducts`, with the transition joint-epic
    preservation (`hcoppres`) and copairing preservation (`hcoppres_case`) supplied by the tower.
    Lax mirror of `Colim.colimitCoprodOfDisjoint`'s `fun i => (hdisj i).toHasBinaryCoproducts`. -/
noncomputable def laxCoprodDataOfDisjoint
    (hdisj : ∀ i, DisjointBinaryCoproduct (L.A i))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (u v : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (p : L.F hij a ⟶ z) (q : L.F hij b ⟶ z),
        ∃ r : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q) :
    LaxCoproductData L where
  hcop i := (hdisj i).toHasBinaryCoproducts
  pres := hcoppres
  presCase := hcoppres_case

/-- The lax colimit's binary coproducts, sourced from the per-stage DISJOINT coproducts.  Lax mirror
    of `Colim.colimitCoprodOfDisjoint`. -/
noncomputable def laxColimCoprodOfDisjoint
    (hdisj : ∀ i, DisjointBinaryCoproduct (L.A i))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (u v : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (p : L.F hij a ⟶ z) (q : L.F hij b ⟶ z),
        ∃ r : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q) :
    @HasBinaryCoproducts (Obj L) (laxColimCat L hL) :=
  laxColimHasBinaryCoproducts L hL (laxCoprodDataOfDisjoint L hdisj hcoppres hcoppres_case)

/-! ## The lax colimit injections are monic -/

/-- **The lax colimit's left injection is monic.**  For arbitrary `A = ⟨iA,xA⟩`, `B = ⟨iB,xB⟩`, the
    injection `inl` is `coprInl`, which by (★) factors as `coprStageIncl ≫ stageInclL (hcop k).inl`;
    `coprStageIncl` is iso and `stageInclL (hcop k).inl` is monic (per-stage `(hdisj k).inl_monic`),
    so the composite is monic.  Lax port of `Colim.colimit_inl_monic`. -/
theorem laxColim_inl_monic
    (hdisj : ∀ i, DisjointBinaryCoproduct (L.A i))
    (hmono : ∀ {i j : ι} (hij : D.le i j),
        @PreservesMono _ (L.catA i) _ (L.catA j) (L.functF hij))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (u v : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (p : L.F hij a ⟶ z) (q : L.F hij b ⟶ z),
        ∃ r : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q) :
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
    ∀ {A B : Obj L}, Monic (HasBinaryCoproducts.inl (A := A) (B := B)) := by
  letI iCat : Cat (Obj L) := laxColimCat L hL
  letI : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
  intro A B
  obtain ⟨iA, xA⟩ := A
  obtain ⟨iB, xB⟩ := B
  show @Monic (Obj L) iCat _ _ (coprInl L hL (laxCoprodDataOfDisjoint L hdisj hcoppres hcoppres_case) xA xB)
  rw [coprInl_factor L hL (laxCoprodDataOfDisjoint L hdisj hcoppres hcoppres_case) xA xB]
  exact mono_precomp_iso' (coprStageIncl_isIso L hL xA (prK_le D iA iB).1)
    (stageInclL_mono_of_stage L hL hmono _ ((hdisj (prK D iA iB)).inl_monic))

/-- **The lax colimit's right injection is monic** (dual of `laxColim_inl_monic`). -/
theorem laxColim_inr_monic
    (hdisj : ∀ i, DisjointBinaryCoproduct (L.A i))
    (hmono : ∀ {i j : ι} (hij : D.le i j),
        @PreservesMono _ (L.catA i) _ (L.catA j) (L.functF hij))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (u v : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (p : L.F hij a ⟶ z) (q : L.F hij b ⟶ z),
        ∃ r : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q) :
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
    ∀ {A B : Obj L}, Monic (HasBinaryCoproducts.inr (A := A) (B := B)) := by
  letI iCat : Cat (Obj L) := laxColimCat L hL
  letI : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
  intro A B
  obtain ⟨iA, xA⟩ := A
  obtain ⟨iB, xB⟩ := B
  show @Monic (Obj L) iCat _ _ (coprInr L hL (laxCoprodDataOfDisjoint L hdisj hcoppres hcoppres_case) xA xB)
  rw [coprInr_factor L hL (laxCoprodDataOfDisjoint L hdisj hcoppres hcoppres_case) xA xB]
  exact mono_precomp_iso' (coprStageIncl_isIso L hL xB (prK_le D iA iB).2)
    (stageInclL_mono_of_stage L hL hmono _ ((hdisj (prK D iA iB)).inr_monic))

/-! ## The lax colimit injections are disjoint -/

/-- **The lax colimit injections are disjoint:** `inl ∩ inr ≤ ⊥`.

    For arbitrary `A = ⟨iA,xA⟩`, `B = ⟨iB,xB⟩` the intersection's domain is the lax-colimit pullback
    `pbC` of `(inl, inr) = (coprInl, coprInr)` into `coprObj = ⟨k, P0⟩`.  By the factorization (★),
    `(pbC.π₁ ≫ ν_A, pbC.π₂ ≫ ν_B)` is a cone over the germ cospan `(stageInclL inlS, stageInclL inrS)`
    (`inlS/inrS` the stage injections `(hcop k).inl/inr`), so the keystone `stageInclFunctorL_preservesPullbacks`
    yields a mediator `m₁ : pbC.pt ⟶ objIncl k pdqₖ.pt` into the §1.432 stage pullback's `objIncl`.
    That stage pullback `pdqₖ.pt` is INITIAL (`disjoint_pullback_initial`, from per-stage §1.621
    disjointness), so `m₁ ≫ stageInclL (pdqₖ.pt → 0_k)` lands `pbC.pt` in the strict-initial
    `objIncl k 0_k` (`laxColimStrictInitial`); hence `pbC.pt` is initial.  Lax port of
    `Colim.colimit_inl_inter_inr`. -/
theorem laxColim_inl_inter_inr [Nonempty ι]
    (hdisj : ∀ i, DisjointBinaryCoproduct (L.A i))
    (_hmono : ∀ {i j : ι} (hij : D.le i j),
        @PreservesMono _ (L.catA i) _ (L.catA j) (L.functF hij))
    (hbot : ∀ i, PreLogos (L.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j),
      @StrictCoterminator (L.A j) (L.catA j) (L.F hij (stageZero L hbot i)))
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L)
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (u v : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (p : L.F hij a ⟶ z) (q : L.F hij b ⟶ z),
        ∃ r : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q)
    [hPL : @PreLogos (Obj L) (laxColimCat L hL)]
    (hl : letI : Cat (Obj L) := laxColimCat L hL
          letI : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
          ∀ {A B : Obj L}, Monic (HasBinaryCoproducts.inl (A := A) (B := B)))
    (hr : letI : Cat (Obj L) := laxColimCat L hL
          letI : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
          ∀ {A B : Obj L}, Monic (HasBinaryCoproducts.inr (A := A) (B := B))) :
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
    ∀ {A B : Obj L},
      Subobject.le (Subobject.inter (inlSub (𝒞 := Obj L) (A := A) (B := B) hl)
                                    (inrSub (𝒞 := Obj L) (A := A) (B := B) hr))
                   (PreLogos.bottom (HasBinaryCoproducts.coprod A B)) := by
  letI iCat : Cat (Obj L) := laxColimCat L hL
  letI iCop : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
  letI iBP : HasBinaryProducts (Obj L) := hPL.toHasBinaryProducts
  intro A B
  refine subobject_le_of_initial_dom ?_
  obtain ⟨iA, xA⟩ := A
  obtain ⟨iB, xB⟩ := B
  -- the lax coproduct data; the common bound `k` and the stage injections
  let data := laxCoprodDataOfDisjoint L hdisj hcoppres hcoppres_case
  let inlS := (data.hcop (prK D iA iB)).inl
    (A := L.F (prK_le D iA iB).1 xA) (B := L.F (prK_le D iA iB).2 xB)
  let inrS := (data.hcop (prK D iA iB)).inr
    (A := L.F (prK_le D iA iB).1 xA) (B := L.F (prK_le D iA iB).2 xB)
  -- the lax-colimit pullback underlying the intersection
  let pbC := HasPullbacks.has (𝒞 := Obj L)
    (HasBinaryCoproducts.inl (A := (⟨iA, xA⟩ : Obj L)) (B := (⟨iB, xB⟩ : Obj L)))
    (HasBinaryCoproducts.inr (A := (⟨iA, xA⟩ : Obj L)) (B := (⟨iB, xB⟩ : Obj L)))
  show IsInitial pbC.cone.pt
  -- the two factorizations (★)
  have hfacL : coprInl L hL data xA xB
      = (coprStageIncl L hL xA (prK_le D iA iB).1) ≫ stageInclL L hL inlS :=
    coprInl_factor L hL data xA xB
  have hfacR : coprInr L hL data xA xB
      = (coprStageIncl L hL xB (prK_le D iA iB).2) ≫ stageInclL L hL inrS :=
    coprInr_factor L hL data xA xB
  have hw : pbC.cone.π₁ ≫ coprInl L hL data xA xB = pbC.cone.π₂ ≫ coprInr L hL data xA xB :=
    pbC.cone.w
  -- the germ-cospan pullback keystone, and a cone over it with apex `pbC.pt`
  have hgermPB := stageInclFunctorL_preservesPullbacks L hL tData pData eqData (prK D iA iB) inlS inrS
  let interCone' : Cone (stageInclL L hL inlS) (stageInclL L hL inrS) :=
    { pt := pbC.cone.pt
      π₁ := pbC.cone.π₁ ≫ coprStageIncl L hL xA (prK_le D iA iB).1
      π₂ := pbC.cone.π₂ ≫ coprStageIncl L hL xB (prK_le D iA iB).2
      w := by
        rw [Cat.assoc, Cat.assoc, ← hfacL, ← hfacR]; exact hw }
  obtain ⟨m1, _, _⟩ := hgermPB interCone'
  -- the §1.432 stage pullback of `(inlS, inrS)` is initial, and the lax strict initial separates it
  have hpdqInit := disjoint_pullback_initial (hdisj (prK D iA iB)) (pData.hp (prK D iA iB))
    (eqData.he (prK D iA iB)) (A := L.F (prK_le D iA iB).1 xA) (B := L.F (prK_le D iA iB).2 xB)
  have hZk : StrictCoterminator (objIncl L (prK D iA iB) (stageZero L hbot (prK D iA iB))) :=
    laxColimStrictInitial L hL hbot hinitpres (prK D iA iB)
  exact isInitial_of_iso (m1 ≫ stageInclL L hL (hpdqInit.out (stageZero L hbot (prK D iA iB))))
    (hZk _) hZk.isInitial

end Freyd.LaxColim
