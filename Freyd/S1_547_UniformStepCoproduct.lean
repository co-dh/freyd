/-
  §1.547 (coproduct analog) — the uniform capitalization-step embedding preserves BINARY COPRODUCTS.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the coproduct dual of `uniformStep`'s `stepProds` field (`Freyd/UniformCapStep.lean`),
  needed (externally) for the §2.218 POSITIVE tower: each capitalization rung must carry binary
  coproducts forward, exactly as `stepProds` carries binary products.

  The successor functor `uniformStepObj W = stageInclNil W ∘ terminalSliceObj W` (UniformCapStep)
  factors as

    F = terminalSliceObj W : S → Over (listProd (chain base))   (= S → S/1, base stage product = 1)
    G = stageInclNil W      : Over (listProd (chain base)) → uniformTargetTy W   (lax stage inclusion).

  We dualize the three product-preservation ingredients of `stepProds`:

    1.  `preservesBinaryCoproducts_comp`   — coproduct preservation composes (dual of
        `preservesBinaryProducts_comp`, `Freyd/CatColimitRegular.lean`).
    2.  `terminalSlicePresCoprods`         — `terminalSliceObj` preserves binary coproducts.  The base
        stage product `listProd (chain base) = 1` is the terminal, so the slice is `S/1`, which is `S`;
        the comparison is the `S`-coproduct comparison (iso, `isIso_of_coproduct_up`).  No
        distributivity is needed — `terminalSliceObj` is the underlying-identity slice equivalence,
        not a general `P × (−)`.
    3.  `stageInclFunctorL_preservesCoproducts` — the lax stage inclusion preserves binary coproducts
        (dual of `stageInclFunctorL_preservesProducts`, `Freyd/RatCapHcanon.lean`), straight from the
        committed germ `objInclL_preserves_coproducts` (`Freyd/LaxGermCoproduct.lean`).

  The lax coproduct bundle `ratLaxCoproductData` is the coproduct mirror of `ratLaxProductData`
  (`Freyd/RatCapPreReg.lean`): per-fibre `overHasBinaryCoproducts`, transition joint-epi / copairing
  preservation from the committed base-change facts `baseChange_coprod_jointEpi` /
  `baseChange_coprod_copair` (`Freyd/RatCapPositive.lean`).

  Mathlib-free.  Single universe (forced by the lax stage-inclusion machinery).
-/
module

public import Freyd.S1_547_UniformCapStep
public import Freyd.S2_218_RatCapPositive
public import Freyd.S1_543_LaxGermCoproduct
public import Freyd.S1_543_RatCapHcanon

open Freyd
open Freyd.Colim
open Freyd.LaxColim

/-! ## The binary-coproduct preservation predicate (dual of `PreservesBinaryProducts`) -/

namespace Freyd

universe u₁ u₂ v

/-- A functor `F : 𝒞 → 𝒟` PRESERVES BINARY COPRODUCTS if the canonical map
    `F A + F B → F(A + B)` (given by `case (F inl) (F inr)`) is an isomorphism.  Dual of
    `PreservesBinaryProducts`; note the comparison runs `F A + F B → F(A + B)` (the opposite
    direction to the product comparison `F(A × B) → F A × F B`). -/
@[expose] public def PreservesBinaryCoproducts {𝒞 : Type u₁} {𝒟 : Type u₂} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F : Functor 𝒞 𝒟) [HasBinaryCoproducts 𝒞] [HasBinaryCoproducts 𝒟] : Prop :=
  ∀ {A B : 𝒞},
    IsIso (HasBinaryCoproducts.case (F.map (HasBinaryCoproducts.inl (A := A) (B := B)))
             (F.map (HasBinaryCoproducts.inr (A := A) (B := B))) :
             HasBinaryCoproducts.coprod (F.obj A) (F.obj B) ⟶ F.obj (HasBinaryCoproducts.coprod A B))

end Freyd

/-! ## §1 — binary-coproduct preservation composes (dual of `preservesBinaryProducts_comp`) -/

namespace Freyd.Colim

universe u

variable {𝒜 ℬ ℰ : Type u} [Cat.{u} 𝒜] [Cat.{u} ℬ] [Cat.{u} ℰ]

/-- **Binary-coproduct preservation composes.**  If `F` and `G` each make their coproduct comparison
    an iso, so does `G ∘ F`: the composite comparison factors as `φG ≫ G(φF)` (`φF`, `φG` the rung
    comparisons), a composite of isos (`φF` iso ⟹ `G φF` iso by `functor_preserves_iso`).  Dual of
    `preservesBinaryProducts_comp` (the factor order flips because the coproduct comparison runs the
    opposite way). -/
public theorem preservesBinaryCoproducts_comp [HasBinaryCoproducts 𝒜] [HasBinaryCoproducts ℬ]
    [HasBinaryCoproducts ℰ] (F : Functor 𝒜 ℬ) (G : Functor ℬ ℰ)
    (hpcF : PreservesBinaryCoproducts F) (hpcG : PreservesBinaryCoproducts G) :
    PreservesBinaryCoproducts (compFunctor F G) := by
  intro A B
  -- φF : FA+FB → F(A+B) iso; φG : GFA+GFB → G(FA+FB) iso; composite = φG ≫ G(φF).
  let φF : HasBinaryCoproducts.coprod (F.obj A) (F.obj B) ⟶ F.obj (HasBinaryCoproducts.coprod A B) :=
    HasBinaryCoproducts.case (F.map (HasBinaryCoproducts.inl (A := A) (B := B)))
      (F.map (HasBinaryCoproducts.inr (A := A) (B := B)))
  let φG : HasBinaryCoproducts.coprod (G.obj (F.obj A)) (G.obj (F.obj B)) ⟶ G.obj (HasBinaryCoproducts.coprod (F.obj A) (F.obj B)) :=
    HasBinaryCoproducts.case (G.map (HasBinaryCoproducts.inl (A := F.obj A) (B := F.obj B)))
      (G.map (HasBinaryCoproducts.inr (A := F.obj A) (B := F.obj B)))
  have hGφF_iso : IsIso (G.map φF) := functor_preserves_iso (F := G) φF (hpcF (A := A) (B := B))
  have hcomp_iso : IsIso (φG ≫ G.map φF) := isIso_comp (hpcG (A := F.obj A) (B := F.obj B)) hGφF_iso
  -- the `G∘F`-comparison equals `φG ≫ G(φF)`: agree after `inl` and after `inr` (jointly epic).
  have hinl : HasBinaryCoproducts.inl ≫ (φG ≫ G.map φF)
      = (compFunctor F G).map (HasBinaryCoproducts.inl (A := A) (B := B)) := by
    rw [← Cat.assoc, HasBinaryCoproducts.case_inl, ← G.map_comp, HasBinaryCoproducts.case_inl]; rfl
  have hinr : HasBinaryCoproducts.inr ≫ (φG ≫ G.map φF)
      = (compFunctor F G).map (HasBinaryCoproducts.inr (A := A) (B := B)) := by
    rw [← Cat.assoc, HasBinaryCoproducts.case_inr, ← G.map_comp, HasBinaryCoproducts.case_inr]; rfl
  have hkey : HasBinaryCoproducts.case
      ((compFunctor F G).map (HasBinaryCoproducts.inl (A := A) (B := B)))
      ((compFunctor F G).map (HasBinaryCoproducts.inr (A := A) (B := B)))
      = φG ≫ G.map φF :=
    (HasBinaryCoproducts.case_uniq _ _ _ hinl hinr).symm
  rw [hkey]; exact hcomp_iso

end Freyd.Colim

/-! ## §3 — the lax stage-inclusion functor preserves binary coproducts -/

namespace Freyd.LaxColim

universe u w

variable {ι : Type w} {D : Directed ι} (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L)

/-- **`stageInclFunctorL i` preserves binary coproducts** (for the colimit's
    `laxColimHasBinaryCoproducts`).  The comparison `case (F inl) (F inr)` is iso — this IS the germ
    `objInclL_preserves_coproducts` (its target object `objIncl L i ((data.hcop i).coprod a b)` is
    `(fun x => ⟨i,x⟩) (a + b)` and its legs are `stageInclL inl|inr = stageInclFunctorL.map inl|inr`).
    Dual of `stageInclFunctorL_preservesProducts`. -/
public theorem stageInclFunctorL_preservesCoproducts (data : LaxCoproductData L) (i : ι) :
    @PreservesBinaryCoproducts (L.A i) (Obj L) (L.catA i) (laxColimCat L hL)
      (stageInclFunctorL L hL i) (data.hcop i)
      (laxColimHasBinaryCoproducts L hL data) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasBinaryCoproducts (Obj L) := laxColimHasBinaryCoproducts L hL data
  intro A B
  exact objInclL_preserves_coproducts L hL data i A B

end Freyd.LaxColim

/-! ## The lax coproduct bundle for a base-change projection system (mirror of `ratLaxProductData`) -/

namespace Freyd.LaxColim

universe u'

variable {ι : Type u'} {D : Directed ι} {𝒞 : Type u'} [Cat.{u'} 𝒞] [DisjointBinaryCoproduct 𝒞]

/-- **`LaxCoproductData (laxOfProjSystem' P)`.**  Per-fibre coproducts `overHasBinaryCoproducts`;
    `pres` (joint-epi preservation) and `presCase` (copairing preservation) are the committed
    base-change coproduct facts `baseChange_coprod_jointEpi` / `baseChange_coprod_copair` applied to
    the projection `g = P.proj hij`.  Coproduct mirror of `ratLaxProductData`. -/
@[expose] public noncomputable def ratLaxCoproductData (P : ProjSystem ι D 𝒞) :
    LaxCoproductData (laxOfProjSystem' P) where
  hcop i := overHasBinaryCoproducts (P.pr i)
  pres {_i _j} hij a b z u v hl hr := baseChange_coprod_jointEpi (P.proj hij) a b z u v hl hr
  presCase {_i _j} hij a b z p q := baseChange_coprod_copair (P.proj hij) a b z p q

end Freyd.LaxColim

/-! ## §2 + §4 — `terminalSliceObj` preserves coproducts; the assembled successor preservation -/

namespace Freyd.UniformCap

open Freyd.Colim
open Freyd.LaxColim
open Freyd.CofinalProj

universe u

-- INSTANCE-DIAMOND DISCIPLINE (§1.543): take `PreRegularCategory S` DERIVED from
-- `[DisjointBinaryCoproduct S]` (NOT as a separate hypothesis).  UniformCapStep's terms
-- (`uniformTargetTy`/`uniformStepFunctor`) and `ratLaxCoproductData (cofinalProjSystem …)` both bake
-- `PreRegularCategory.toHasPullbacks`; with a SEPARATE `[PreRegularCategory S]` the two
-- `PreRegularCategory S` provenances (direct vs `RegularCategory.toPreRegularCategory`) diverge and
-- the lax-coproduct argument reports a `HasPullbacks` type mismatch.  A single positive root makes
-- every `laxOfProjSystem' (cofinalProjSystem …)` resolve identically.
variable {S : Type u} [Cat.{u} S] [DisjointBinaryCoproduct S]
variable [DecidableEq S]
variable (W : WSCover S)

/-- **`terminalSliceObj` preserves binary coproducts.**  The slice coproduct comparison is iso iff its
    underlying `S`-arrow is; `terminalSliceObj` is the underlying-identity slice equivalence
    (`S ≅ S/1`, the base stage product `listProd (chain base) = 1` being terminal), so the comparison
    is the `S`-coproduct comparison — an iso by `isIso_of_coproduct_up`.  Dual of
    `terminalSlicePresProds`; built with `case` in place of `pair`. -/
public theorem terminalSlicePresCoprods :
    letI : HasBinaryCoproducts (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) :=
      overHasBinaryCoproducts _
    @PreservesBinaryCoproducts S (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) _ _
      (terminalSliceFunctor W)
      _ (overHasBinaryCoproducts _) := by
  letI : HasBinaryCoproducts (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) :=
    overHasBinaryCoproducts _
  intro A B
  -- the cocone `(terminalSliceObj (A+B), map inl, map inr)` has the slice coproduct universal
  -- property: underlying it is the `S`-coproduct of `A, B`, and slice maps are determined by their
  -- underlying arrows.
  refine isIso_of_coproduct_up (𝒞 := Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd)))
    (terminalSliceFunctor W |>.map (HasBinaryCoproducts.inl (A := A) (B := B)))
    (terminalSliceFunctor W |>.map (HasBinaryCoproducts.inr (A := A) (B := B))) ?_
  intro Z f g
  -- mediator: copair the underlying arrows in `S`, lift to the slice (term-uniqueness over `pr base`).
  refine ⟨⟨HasBinaryCoproducts.case f.f g.f, base_hom_uniq W _ _⟩,
      ⟨OverHom.ext (HasBinaryCoproducts.case_inl f.f g.f),
       OverHom.ext (HasBinaryCoproducts.case_inr f.f g.f)⟩, ?_⟩
  intro v hv₁ hv₂
  -- uniqueness: underlying `v.f` equals `case f.f g.f` by `case_uniq` (its `inl`/`inr` legs are `f.f`/`g.f`).
  exact OverHom.ext (HasBinaryCoproducts.case_uniq f.f g.f v.f
    (congrArg OverHom.f hv₁) (congrArg OverHom.f hv₂))

set_option maxHeartbeats 1000000 in
/-- **(coproduct analog of `stepProds`) The §1.547 successor functor preserves binary coproducts.**
    Composite of the base embedding's coproduct preservation (`terminalSlicePresCoprods`, the slice
    `S/1` is `S`) and the lax stage-inclusion's coproduct preservation
    (`stageInclFunctorL_preservesCoproducts` on the §1.547 lax coproduct bundle
    `ratLaxCoproductData`).  Sorry-free. -/
public theorem uniformStep_preservesBinaryCoproducts :
    letI : HasBinaryCoproducts (uniformTargetTy W) :=
      laxColimHasBinaryCoproducts (laxOfProjSystem' (cofinalProjSystem (S := S)))
        (coherentProj (cofinalProjSystem (S := S))) (ratLaxCoproductData (cofinalProjSystem (S := S)))
    @PreservesBinaryCoproducts S (uniformTargetTy W) _ (uniformTargetCat W)
      (uniformStepFunctor W) _
      (laxColimHasBinaryCoproducts (laxOfProjSystem' (cofinalProjSystem (S := S)))
        (coherentProj (cofinalProjSystem (S := S))) (ratLaxCoproductData (cofinalProjSystem (S := S)))) := by
  letI : HasBinaryCoproducts (uniformTargetTy W) :=
    laxColimHasBinaryCoproducts (laxOfProjSystem' (cofinalProjSystem (S := S)))
      (coherentProj (cofinalProjSystem (S := S))) (ratLaxCoproductData (cofinalProjSystem (S := S)))
  letI : HasBinaryCoproducts (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) :=
    overHasBinaryCoproducts _
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  intro A B
  exact preservesBinaryCoproducts_comp (𝒜 := S)
    (ℬ := Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) (ℰ := uniformTargetTy W)
    (F := terminalSliceFunctor W) (G := stageInclNil W)
    (terminalSlicePresCoprods W)
    (stageInclFunctorL_preservesCoproducts (laxOfProjSystem' (cofinalProjSystem (S := S)))
      (coherentProj (cofinalProjSystem (S := S))) (ratLaxCoproductData (cofinalProjSystem (S := S))) W.base)

end Freyd.UniformCap
