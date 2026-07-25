/-
  §1.543 (lax) — `objIncl i` PRESERVES IMAGES in the FILTERED lax colimit.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the LAX port of `Colim.objIncl_preserves_images` (`CatColimitRegular.lean:2358`), the
  image analogue of `LaxGermProducts.objInclL_preserves_products`.

  Given a `LaxCatSystem L` with `Coherent L`, per-fibre images (`hi`), faithful (`hfaith`) /
  mono-preserving (`hmono`) / image-preserving (`himgpres`) transitions, and the colimit pullbacks
  (`[hpull]`), the `objIncl i`-image of the stage image factorization of a single-fibre morphism
  `f : a ⟶ b` is an image in `laxColimCat L hL`: the subobject

      `⟨objIncl i (image f).dom, stageInclL (image f).arr⟩`

  is the image of `stageInclL f`.

  PROOF (mirrors the strict assembly line-by-line).  Factor `f = image.lift f ≫ (image f).arr` at
  stage `i` (`image.lift_fac`).  Include both legs through the stage inclusion `stageInclL`
  (= `homInclL` at the reflexive bound, `RatCapHcanon`):

    * COVER leg — `stageInclL (image.lift f)` is a colimit COVER (`homInclL_cover_of_stage`; each
      transition keeps `image.lift f` a cover via `preservesImage_lift_cover` from `himgpres`).
    * MONO leg — `stageInclL (image f).arr` is a colimit MONO (`stageInclL_mono_of_stage`, built
      here; `(image f).arr` is monic and preserved by every transition via `hmono`, the flanking
      coherence isos `reflApp`/`transApp` strip off).
    * COMPOSITE — `stageInclL (image.lift f) ⊚ stageInclL (image f).arr = stageInclL f`
      (`stageInclL_comp` + `image.lift_fac`).

  A cover-then-mono factorization is an image (`coverMono_isImage`, needs only `HasPullbacks`).

  This is the per-stage germ-preservation lemma extracted from `LaxColimitImages.laxColimHasImages`
  (which builds the SAME image factorization inline for an arbitrary germ), specialised to the
  single-fibre `stageInclL` case so it is reusable downstream (the lax mirror of the role
  `objIncl_preserves_images` plays in the §1.543/§2.218 strict tower).  Mathlib-free. -/
import Freyd.S1_543_RatCapHcanon
import Freyd.S1_543_CatColimitRegular

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}
variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)

/-! ## Monicity of a stage mono through the stage inclusion (lax `homInclObj_mono_of_stage`)

  A stage mono `m : x ⟶ y` in `L.A i` includes to a colimit mono `stageInclL m`.  This is the mono
  half of `RatCapHcanon.homInclL_cover_reflects` (lines 522–547), packaged as a reusable lemma.
  PROOF.  `stageInclL m = homInclL ⟨i,refl,refl⟩ (reflApp x ≫ m ≫ isoInv reflApp)`, so by
  `homInclL_mono_of_stage` it suffices that every transition push of that germ is left-cancellable.
  The push is `transApp ≫ map(reflApp ≫ m ≫ isoInv) ≫ isoInv transApp`; all factors but `map m`
  are isos (`functor_preserves_iso`/`transApp_isIso`), and `map m` is monic by `hmono`, so the
  whole composite is monic (mono preserved by iso pre/post-composition). -/
/-! ## `objIncl i` preserves images

  Mirrors `Colim.objIncl_preserves_images`. -/
theorem objInclL_preserves_images
    (hi : ∀ i, @HasImages (L.A i) (L.catA i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        L.Fmap hij p = L.Fmap hij q → p = q)
    (hmono : ∀ {i j : ι} (hij : D.le i j),
        @PreservesMono _ (L.catA i) _ (L.catA j) (L.functF hij))
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {X Y : L.A i} (f : X ⟶ Y),
        @IsImage (L.A j) (L.catA j) _ _ (L.Fmap hij f)
          (@Subobject.map _ _ (L.catA i) (L.catA j) (L.functF hij) (hmono hij) _
            (@image _ (L.catA i) (hi i) _ _ f)))
    [hpull : @HasPullbacks (Obj L) (laxColimCat L hL)]
    (i : ι) {a b : L.A i} (f : a ⟶ b) :
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasImages (L.A i) := hi i
    IsImage (stageInclL L hL f)
      (Subobject.mk (objIncl L i (image f).dom) (stageInclL L hL (image f).arr)
        (stageInclL_mono_of_stage L hL hmono (image f).arr (image f).monic)) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasImages (L.A i) := hi i
  -- stage factorization `image.lift f ≫ (image f).arr = f`.
  have hfac_stage : image.lift f ≫ (image f).arr = f := image.lift_fac f
  -- the cover leg: `stageInclL (image.lift f)` is a colimit cover.
  have hcov : @Cover (Obj L) (laxColimCat L hL) _ _ (stageInclL L hL (image.lift f)) :=
    homInclL_cover_of_stage L hL hfaith a (image f).dom (image.lift f)
      (fun {e} hie => preservesImage_lift_cover (L.functF hie) (hmono hie) f
        (himgpres hie f))
  -- the composite `stageInclL (image.lift f) ⊚ stageInclL (image f).arr = stageInclL f`.
  have hcomp : @compL _ _ L hL (objIncl L i a) (objIncl L i (image f).dom) (objIncl L i b)
      (stageInclL L hL (image.lift f)) (stageInclL L hL (image f).arr)
      = stageInclL L hL f := by
    rw [← stageInclL_comp L hL (image.lift f) (image f).arr, hfac_stage]
  -- cover-then-mono factorization is an image.
  exact coverMono_isImage
    (stageInclL_mono_of_stage L hL hmono (image f).arr (image f).monic)
    hcov hcomp

end Freyd.LaxColim
