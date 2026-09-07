/-
  §1.543 (lax) — `objIncl i` PRESERVES EQUALIZERS in the FILTERED lax colimit.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the LAX port of `Colim.objIncl_preserves_equalizers` (`CatColimitRegular.lean:2059`).

  Given a `LaxCatSystem L` with `Coherent L` and the lax equalizer-preservation bundle
  `LaxEqualizerData L` (per-fibre equalizers `he` + transition `eqMap` joint-monicity `pres` +
  transition equalizer-lift preservation `presLift`), for a stage-`i` parallel pair `f g : a ⟶ b`
  the `objIncl i`-image of the FIBRE equalizer cone

      `(⟨i, eqObj f g⟩, stageInclL (eqMap f g))`

  is an EQUALIZER cone of `stageInclL f`, `stageInclL g` in `laxColimCat L hL` (the
  `EqualizerCone.IsEqualizer` universal-property form).

  PROOF.  The cone EQUALIZES because `stageInclL` is functorial (`stageInclL_comp`) and
  `eqMap f g ≫ f = eqMap f g ≫ g` in the fibre (`eqMap_eq`).  The UNIVERSAL PROPERTY is exactly
  `RatCapHcanon.stageInclL_equalizer_up`: a competitor `d` whose map equalizes `stageInclL f`,
  `stageInclL g` factors uniquely through `stageInclL (eqMap f g)` — existence via `eqData.presLift`
  (push the competitor to a common stage, lift there), uniqueness because `eqMap` is jointly
  cancellable (`eqData.pres`, the single-leg `homInclL_mono_of_stage`).

  Mirrors the strict `objIncl_preserves_equalizers` (the largest germ lemma) line-for-line in shape;
  the lax `pushHom`/coherence-iso bookkeeping is already discharged inside `stageInclL_equalizer_up`,
  the lax counterpart of the strict `castHom`/object-equality assembly.  Mathlib-free.
-/
module

public import Freyd.S1_543_RatCapHcanon

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

-- Single universe (`ι` and the fibres share universe `w`): matches `RatCapHcanon`'s
-- `SingleUniverse` section, the home of the reused `stageInclL_equalizer_up` and its sibling
-- stage-functor preservation result `stageInclFunctorL_preservesEqualizers`.
universe w

variable {ι : Type w} {D : Directed ι}
variable (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L)

/-! ## `objIncl i` preserves the stage equalizer `eqObj f g`

  Mirrors `Colim.objIncl_preserves_equalizers`. -/
theorem objInclL_preserves_equalizers (eqData : LaxEqualizerData L)
    (i : ι) {a b : L.A i} (f g : a ⟶ b) :
    @EqualizerCone.IsEqualizer (Obj L) (laxColimCat L hL)
      (objIncl L i a) (objIncl L i b) (stageInclL L hL f) (stageInclL L hL g)
      (@EqualizerCone.mk (Obj L) (laxColimCat L hL) _ _ (stageInclL L hL f) (stageInclL L hL g)
        (objIncl L i (@eqObj _ _ (eqData.he i) a b f g))
        (stageInclL L hL (@eqMap _ _ (eqData.he i) a b f g))
        (by
          letI : Cat (Obj L) := laxColimCat L hL
          letI : HasEqualizers (L.A i) := eqData.he i
          show @compL _ _ L hL ⟨i, eqObj f g⟩ ⟨i, a⟩ ⟨i, b⟩
                (stageInclL L hL (eqMap f g)) (stageInclL L hL f)
             = @compL _ _ L hL ⟨i, eqObj f g⟩ ⟨i, a⟩ ⟨i, b⟩
                (stageInclL L hL (eqMap f g)) (stageInclL L hL g)
          rw [← stageInclL_comp L hL (eqMap f g) f, ← stageInclL_comp L hL (eqMap f g) g,
              eqMap_eq f g])) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasEqualizers (L.A i) := eqData.he i
  -- the universal property is the stage germ-equalizer lemma: a competitor `d` equalizing
  -- `stageInclL f`/`stageInclL g` factors uniquely through `stageInclL (eqMap f g)`.
  intro d
  obtain ⟨u, hu, huniq⟩ := stageInclL_equalizer_up L hL eqData i f g d.map d.eq
  exact ⟨u, hu, huniq⟩

end Freyd.LaxColim
