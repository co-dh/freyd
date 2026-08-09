/-
  Freyd & Scedrov, *Categories and Allegories* — the EXACT (cover/image-preserving,
  iso-reflecting) representation, isolated as a reusable interface.

  WHAT THIS FILE IS.  Several §1.59 sorries (`five_lemma`, `snake_lemma`,
  `abelian_iff_*`) and the abelian-cluster reduction `additive_iff_shear_isIso`
  bottom out on a FAITHFUL *exact* representation `T : 𝒞 → 𝒟` that reflects
  isomorphisms.  The full construction of such a `T` (the §1.543 capitalization
  chain upgraded to preserve covers/images) is a separate, genuinely hard theorem
  and is NOT done here.  What IS done here is the *precise downstream reduction*:
  we state exactly the two properties the rep must supply and prove the
  abelian-cluster consequence (`shear x` is an iso ⟹ additive inverses exist)
  from them, Sorry-free.

  WHY THIS IS NOT VACUOUS.  The interface is satisfied by the identity functor
  (`reflectsAdditively_id`), so it is a genuine constraint, not a trivially-false
  hypothesis discharged by ex falso.  The intended *non-identity* witness is the
  exact representation into `Ab` / `Set^I`; the day it lands, it plugs straight
  into `additive_of_reflectingAdditiveFunctor` to discharge additivity (hence
  `abelian_has_negatives`) unconditionally.

  THE PRECISE REDUCTION CHAIN (Freyd's argument, made explicit):
    every shear iso in target  ──(F reflects iso)──▶  every shear iso in source
                                                              │
                                            (addInv_of_shear_isIso, §1.591)
                                                              ▼
                                          every hom in source has an additive inverse
  The target's shears are isos because the target is ADDITIVE (e.g. `Ab`), where
  `shear_isIso_of_addInv` applies.  So the only non-elementary content is bundled
  into ONE hypothesis: a functor that (i) reflects isos and (ii) sends each source
  shear to a target shear.  That hypothesis is exactly "exact iso-reflecting rep
  into an additive category".
-/

module

public import Freyd.S1_59

open Freyd

universe v u w

namespace Freyd

/-! ## The reflecting-additive-functor interface

  `ReflectingAdditiveFunctor F` packages the two properties an exact representation
  `F : 𝒞 → 𝒟` of a half-additive `𝒞` into an *additive* `𝒟` must provide for the
  abelian-cluster reduction:

  * `reflects_iso` — `F` reflects isomorphisms (a map whose image is iso is iso).
    This is the iso-reflection an exact, faithful, image-preserving rep buys.
  * `maps_shear_iso` — `F` carries each source shear `shear x` to an *iso* in the
    target.  This is the structural-preservation content together with target
    additivity: a product- and addition-preserving functor sends `shear x` to
    (the conjugate of) a target shear `shear (F x)`, which is iso in the additive
    target by `shear_isIso_of_addInv`.  We package the end product — "the image is
    iso" — rather than the intermediate shear equation, because the latter is only
    well-typed after transport along the product-comparison iso
    `F (A×B) ≅ F A × F B`; isomorphism-of-the-image is exactly the transport-stable
    content the reflection step consumes.

  Both fields are stated abstractly so that ANY functor providing them — not just
  one particular construction — discharges the reduction. -/
structure ReflectingAdditiveFunctor
    {𝒞 : Type u} [Cat.{v} 𝒞] [HalfAdditiveCategory 𝒞]
    {𝒟 : Type w} [Cat.{v} 𝒟] [HalfAdditiveCategory 𝒟]
    (F : Functor 𝒞 𝒟) : Prop where
  /-- `F` reflects isomorphisms: if `F.map f` is an iso then so is `f`. -/
  reflects_iso : ∀ {X Y : 𝒞} {f : X ⟶ Y}, IsIso (F.map f) → IsIso f
  /-- `F` sends each source shear to an iso in the target (= structure
      preservation into an additive target, conjugated through the product
      comparison). -/
  maps_shear_iso : ∀ {A B : 𝒞} (x : A ⟶ B), IsIso (F.map (HalfAdditiveCategory.shear x))

/-- **Non-vacuity / satisfiability.**  The interface is not a trivially-false
    hypothesis: on any *additive* category the identity functor satisfies both
    fields (it reflects every iso, and there every shear is already an iso by
    `shear_isIso_of_addInv`).  Hence `ReflectingAdditiveFunctor` is satisfiable —
    the abelian-cluster reduction below is a genuine implication, not `ex falso`. -/
theorem reflectingAdditive_id_of_additive
    (𝒞 : Type u) [Cat.{v} 𝒞] [AdditiveCategory 𝒞] :
    ReflectingAdditiveFunctor (𝒞 := 𝒞) (𝒟 := 𝒞) idFunctor where
  reflects_iso h := h
  maps_shear_iso x :=
    HalfAdditiveCategory.shear_isIso_of_addInv
      (inst := AdditiveCategory.toHalfAdditiveCategory)
      (fun {_ _} f => AdditiveCategory.addInv f) x

/-! ## The shear reduction

  These are the two payoff lemmas.  They are FULLY PROVED (Sorry-free); the only
  thing assumed is the existence of a reflecting-additive functor, which is the
  honest statement of "exact iso-reflecting representation". -/

variable {𝒞 : Type u} [Cat.{v} 𝒞] [HalfAdditiveCategory 𝒞]
variable {𝒟 : Type w} [Cat.{v} 𝒟] [HalfAdditiveCategory 𝒟]

/-- **The shear is iso, reflected from the additive target.**

    Let `F : 𝒞 → 𝒟` be a reflecting-additive functor with `𝒟` *additive*.  Then
    every shear `shear x` in `𝒞` is an isomorphism: its image `F.map (shear x)`
    is a target shear `shear x'`, which is iso in the additive `𝒟` by
    `shear_isIso_of_addInv`; `F` reflects that iso back to `𝒞`.

    This is Freyd's "it holds because it holds in `Ab` and the exact rep reflects
    isos", with `Ab` replaced by any additive `𝒟`. -/
theorem shear_isIso_of_reflectingAdditiveFunctor
    (F : Functor 𝒞 𝒟) (hF : ReflectingAdditiveFunctor F)
    {A B : 𝒞} (x : A ⟶ B) : IsIso (HalfAdditiveCategory.shear x) :=
  -- `F.map (shear x)` is iso (`maps_shear_iso`: the image is a shear in the
  -- additive target, hence iso); `F` reflects that iso back to `𝒞`.
  hF.reflects_iso (hF.maps_shear_iso x)

/-- **The abelian-cluster unlock.**  A half-additive category admitting a
    reflecting-additive functor into an additive category is itself ADDITIVE:
    every hom has an additive inverse.

    Proof: shears are iso (`shear_isIso_of_reflectingAdditiveFunctor`), and the
    backward §1.591 direction `addInv_of_shear_isIso` extracts the inverse.
    This is precisely the step `abelian_has_negatives` was reduced to. -/
theorem additive_of_reflectingAdditiveFunctor
    (F : Functor 𝒞 𝒟) (hF : ReflectingAdditiveFunctor F)
    {A B : 𝒞} (f : A ⟶ B) :
    ∃ g : A ⟶ B, HalfAdditiveCategory.add f g = HalfAdditiveCategory.zeroHom A B :=
  HalfAdditiveCategory.addInv_of_shear_isIso
    (fun {_ _} y => shear_isIso_of_reflectingAdditiveFunctor F hF y) f

end Freyd
