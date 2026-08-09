/-
  §1.635 — THE FAITHFUL STALK REPRESENTATION of a capital positive pre-logos.

  Assembling the three preceding files: `Tstar = ∏_F̂ T_F̂ : 𝒞 → (StalkIndex 𝒞 → Type)` is a
  `RegularFunctor` (`Tstar_regularFunctor`), it SEPARATES MAPS and REFLECTS COVERS
  (`Tstar_separates`/`Tstar_reflects_cover`, both from `stalk_detects_proper_mono`), hence it
  REFLECTS ISOS (`Tstar_reflects_iso`: a power-iso is fibrewise bijective, so `f` is a cover and a
  mono, hence iso by `monic_cover_iso`).  Feeding this into the §2.218 packager
  `relAllegoryHom_faithful_of_reflects` (with split power-covers, `power_cover_splits`) gives a
  FAITHFUL allegory representation `Rel(𝒞) → Rel(Set)^StalkIndex` — Freyd's §1.635, the heart of
  §2.218, with NO single-stalk-reflects-isos assumption (the family is COLLECTIVELY faithful). -/
module

public import Freyd.S1_634_TstarRegular
public import Freyd.S1_635_TstarConservative

namespace Freyd
open PreLogosHorn.Stalk

variable {𝒞 : Type u} [Cat.{u} 𝒞] [DisjointBinaryCoproduct 𝒞]

/-- **`Tstar` REFLECTS ISOS** (collective conservativity).  An iso `Tstar f` is fibrewise bijective
    (its power-inverse restricts to a two-sided inverse of each `T_F̂(f)`); the surjectivity gives
    `f` a cover (`Tstar_reflects_cover`) and the injectivity gives `f` a mono (`Tstar_separates`),
    so `f` is an iso by `monic_cover_iso`.  NO single stalk reflects isos — the family does. -/
public theorem Tstar_reflects_iso (hcap : Capital (𝒞 := 𝒞)) {X Y : 𝒞} (f : X ⟶ Y)
    (hiso : IsIso (TstarFunctor.map f)) : IsIso f := by
  -- A power-iso is fibrewise an iso of sets (`power_isIso_iff`).
  have hfib : ∀ F : StalkIndex 𝒞,
      @IsIso (Type u) _ (TF F.val X) (TF F.val Y) (TF.map F.val f) := by
    intro F; exact (power_isIso_iff (TstarFunctor.map f)).mp hiso F
  -- fibrewise surjective: the fibre inverse is a section of `T_F̂(f)`.
  have hsurj : ∀ F : StalkIndex 𝒞, Function.Surjective (TF.map F.val f) := by
    intro F y
    obtain ⟨inv, _, h2⟩ := hfib F
    exact ⟨inv y, congrFun h2 y⟩
  -- fibrewise injective: the fibre inverse is a retraction of `T_F̂(f)`.
  have hinj : ∀ F : StalkIndex 𝒞, Function.Injective (TF.map F.val f) := by
    intro F a b hab
    obtain ⟨inv, h1, _⟩ := hfib F
    have ha : inv (TF.map F.val f a) = a := congrFun h1 a
    have hb : inv (TF.map F.val f b) = b := congrFun h1 b
    rw [← ha, ← hb, hab]
  have hcov : Cover f := Tstar_reflects_cover hcap f hsurj
  have hmon : Monic f := by
    intro Z g h hgh
    refine Tstar_separates hcap g h (fun F => ?_)
    funext z
    refine hinj F ?_
    rw [← TF.map_comp F.val g f z, ← TF.map_comp F.val h f z, hgh]
  exact monic_cover_iso f hcov hmon

/-- **§1.635 — THE FAITHFUL STALK REPRESENTATION.**  Every (small) CAPITAL positive pre-logos `𝒞`
    has a FAITHFUL allegory representation `Rel(𝒞) → Rel(StalkIndex 𝒞 → Type)` — relations in the
    power of sets indexed by the ultra-filters of complemented subterminators.

    This is Freyd's §1.635, the core of §2.218: the representation `Rel(Tstar)` is faithful because
    the stalk FAMILY collectively detects every proper subobject (`stalk_detects_proper_mono`,
    powered by the relative ultra-filter construction), via the §2.218 packager
    `relAllegoryHom_faithful_of_reflects` — `Tstar` reflects isos and power-covers split. -/
theorem relStalk_repr_faithful (hcap : Capital (𝒞 := 𝒞)) :
    (Tstar_regularFunctor hcap).relAllegoryHom.Faithful :=
  (Tstar_regularFunctor hcap).relAllegoryHom_faithful_of_reflects
    (fun f hiso => Tstar_reflects_iso hcap f hiso)
    (fun e he => power_cover_splits e he)

end Freyd
