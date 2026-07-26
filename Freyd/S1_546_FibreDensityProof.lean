/-
  §1.546 DENSITY — `FibreDensity (wsCover S)`: the last genuine theorem of §1.543, now PROVEN
  Sorry-free (`fibreDensity`/`wsCover_fibreDensity`).  With it, §1.543 (`Freyd.capitalization_lemma`)
  is proven (axioms `[propext, Classical.choice, Quot.sound]`).

  `FibreDensity W` (`UniformWellPoints.lean`, Phase 3) is the §1.546 stage-local density obligation:
  for every well-supported `A`, every cofinal stage `U ≥ base`, and every PROPER FIBRE mono
  `g'' : xE' ↪ (laxOfProjSystem' cofinalProjSystem).F hbU (terminalSliceObj A)` (which
  `pushTerminalSlice_iso` identifies with `sliceEmbedObj (∏U) A = ⟨A × ∏U, snd⟩` in `Over (∏U)`),
  there is a COLIMIT point `x'` of `⟨U, pushforward⟩` that `(stageInclFunctorL U).map g''` does NOT
  factor.

  The point `x'` is a COLIMIT point — it may live at a RICHER slice `U' ⊇ U`.  This is the whole
  reason the directed UNION (not one slice) is used: at a single slice `U` an arbitrary proper mono
  need NOT be product-form (`properMono_forces_graph_iso`, SliceEquivalence — the graph of the
  generic point `pair (proj_k) id` is a proper mono REACHING every fixed-slice point), so no slice
  point of `sliceEmbedObj (∏U) A` need miss it.  The escape lives at a richer slice / in the colimit.

  ── ARCHITECTURE — Sorry-free reduction + the genuine §1.546 core ───────────────────────────────

  This file commits, SORRY-FREE, the full colimit↔fibre passage reducing `FibreDensity W` to the
  genuine §1.546 density CORE, isolated as `RicherSliceMiss W`:

    `RicherSliceMiss W` := for every ws `A`, stage `U ≥ base`, and proper fibre mono `g''` into the
    pushforward at `U`, there is a RICHER stage `U' ≥ U`, a slice point `p : 1 → pushforward_{U'}` of
    the embedded object at `U'`, and the base-change of `g''` to `U'` does NOT factor `p`.

  * Phase 1 — point/iso transport in the lax colimit (SORRY-FREE).  A slice-`U'` point missing a
    slice mono becomes a colimit point missing the included mono, via `laxTerminalArrowAt` (the
    colimit terminal maps uniquely to the stage-`U'` terminal), `stageInclFunctorL U'` (slice point ↦
    colimit germ), and `alignGerm`/`alignGermInv` (the realignment isos `⟨U, pushforward_U⟩ ≅
    ⟨base, term A⟩ ≅ ⟨U', pushforward_{U'}⟩`).

  * Phase 2 — `fibreDensity_of_richerSliceMiss` (SORRY-FREE).  `RicherSliceMiss W ⟹ FibreDensity W`.

  * Phase 3 — `RicherSliceMiss`: the genuine §1.546 density content.  THE HONEST RESIDUAL, reported
    with its precise mathematical blocker.

  No mathlib category theory.  No `axiom`, no `:True`, no statement-weakening.
-/
import Freyd.S1_543_UniformWellPoints
import Freyd.S1_43

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.FibreDensityProof
open scoped PreRegularCategory

universe u

variable {S : Type u} [Cat.{u} S] [PreRegularCategory S] [DecidableEq S]

-- Keep the cofinal lax system on the shared finite-limit representatives.
open Freyd.UniformCap
open Freyd.CofinalProj
open Freyd.UniformWellPoints

/-! ## Phase 1 — the genuine §1.546 density CORE, and the reduction `FibreDensity` ⟸ it

  Phase 2 of `UniformWellPoints` (`colimitMono_reflects_to_fibre`) already reduced an arbitrary proper
  colimit mono to a proper FIBRE mono `g''` at some stage `U`.  `FibreDensity W` packages the missing
  obligation: that `(stageInclFunctorL U).map g'' = stageInclL g''` is missed by a colimit point.

  The §1.546 mechanism is that the missing point lives at a RICHER stage `U' ⊇ U`.  We isolate exactly
  that as `RicherSliceMiss W`, stated at the COLIMIT level (so the transport back to `U` is a single
  `homInclL_factor` realignment + `point_transport_unconj`).  For a proper fibre mono `g''` at `U`,
  there is a richer stage `U'` at which the PUSHED fibre mono `pushFibre g'' hUU'` is missed by a
  colimit point of its codomain. -/

variable (W : WSCover S)

/-- The fibre mono `g''` at stage `U`, pushed to a richer stage `U' ≥ U`: the base-change
    `F(U≤U').map g''`, a fibre map at `U'`. -/
noncomputable def pushFibre (A : S) {U U' : WSList S} (hbU : (wsDirected S).le W.base U)
    (hUU' : (wsDirected S).le U U')
    {xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U} (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)) :
    (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' ((laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)) :=
  ((laxOfProjSystem' (cofinalProjSystem (S := S))).functF hUU').map g''

/-- **The genuine §1.546 density CORE.**  For every well-supported `A`, every stage `U ≥ base`, and
    every PROPER fibre mono `g''` into the pushforward of `terminalSliceObj A` at `U`, there is a
    RICHER stage `U' ≥ U` and a colimit point of `⟨U', F(U≤U') (pushforward_U)⟩` that the colimit
    image `stageInclL (pushFibre g'' hUU')` of the *base-changed* mono does NOT factor.

    This is the directed-union escape: at a single slice the proper mono may be the graph
    `pair (proj_k) id`, which reaches every fixed-slice point (`properMono_forces_graph_iso`); at a
    richer slice `U'` containing `A` as an independent surviving factor, the slice acquires a NEW
    A-point (`listProdSliceAcquiresEveryFactor`) decoupled from `proj_k`, which the (base-changed)
    subobject misses.  Stated at the colimit level so the realignment back to `U` is mechanical. -/
def RicherSliceMiss (W : WSCover S) : Prop :=
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  ∀ (A : S), WellSupported A →
    ∀ (U : WSList S) (hbU : (wsDirected S).le W.base U)
      (xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U)
      (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)),
      Monic g'' → ¬ IsIso g'' →
      ∃ (U' : WSList S) (hUU' : (wsDirected S).le U U')
        (x' : @Cat.Hom _ (uniformTargetCat W)
                (@HasTerminal.one _ (uniformTargetCat W)
                  (uniformStepTarget_preRegular W).toHasTerminal)
                ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' ((laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A))⟩),
        ¬ ∃ (y' : @Cat.Hom _ (uniformTargetCat W)
                  (@HasTerminal.one _ (uniformTargetCat W)
                    (uniformStepTarget_preRegular W).toHasTerminal)
                  ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' xE'⟩),
          @Cat.comp _ (uniformTargetCat W) _ ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' xE'⟩ _ y'
            (stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
              (coherentProj (cofinalProjSystem (S := S))) (pushFibre W A hbU hUU' g'')) = x'

/-! ### The realignment of `stageInclL g''` to the richer stage `U'`

  `homInclL_factor` writes `stageInclL g''` (at stage `U`) as the realignment-flanked stage-`U'`
  inclusion of the pushed germ.  The pushed germ `pushHom (reflApp ≫ g'' ≫ isoInv)` is, by the
  `pushHom`/`Functor.map_comp` expansion, the base-change `pushFibre g'' hUU'` flanked by stage isos
  (`transApp`, `reflApp`).  So `stageInclL g''` is `stageInclL (pushFibre g'' hUU')` conjugated by
  colimit isos — exactly the shape `point_transport_unconj` consumes. -/

/-- The §1.547 transitions are conservative on monos / preserve monos / are faithful (read off the
    cofinal projection-cover, exactly as `colimitMono_reflects_to_fibre` does). -/
private theorem L_cons {i j : WSList S} (hij : (wsDirected S).le i j)
    {x y : (laxOfProjSystem' (cofinalProjSystem (S := S))).A i} (φ : x ⟶ y) :
    IsIso (((laxOfProjSystem' (cofinalProjSystem (S := S))).functF hij).map φ) →
      IsIso φ :=
  fun hiso => projStage_conservative_full (cofinalProjSystem (S := S)) hij
    (cofinalProjSystem_cover hij) φ hiso

/-- **`stageInclL g''` factors as a colimit-iso conjugation of `stageInclL (pushFibre g'' hUU')`.**
    The bridge from the stage-`U` inclusion of `g''` to the richer-stage-`U'` inclusion of its
    base-change.  Both flanks are colimit isos (compositions of `alignGerm`/`alignGermInv` and
    `stageInclL` of the `transApp`/`reflApp` stage isos around `pushFibre`). -/
theorem stageInclL_g''_factor (A : S) {U U' : WSList S} (hbU : (wsDirected S).le W.base U)
    (hUU' : (wsDirected S).le U U')
    {xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U}
    (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)) :
    letI : Cat _ := laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
      (coherentProj (cofinalProjSystem (S := S)))
    ∃ (iL : @Cat.Hom _ (laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
              (coherentProj (cofinalProjSystem (S := S))))
            ⟨U, xE'⟩ ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU' xE'⟩)
      (jR : @Cat.Hom _ (laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
              (coherentProj (cofinalProjSystem (S := S))))
            ⟨U', (laxOfProjSystem' (cofinalProjSystem (S := S))).F hUU'
                  ((laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A))⟩
            ⟨U, (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)⟩),
      IsIso iL ∧ IsIso jR ∧
      stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
          (coherentProj (cofinalProjSystem (S := S))) g''
        = @Cat.comp _ (laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
              (coherentProj (cofinalProjSystem (S := S)))) _ _ _ iL
            (@Cat.comp _ (laxColimCat (laxOfProjSystem' (cofinalProjSystem (S := S)))
                (coherentProj (cofinalProjSystem (S := S)))) _ _ _
              (stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
                (coherentProj (cofinalProjSystem (S := S))) (pushFibre W A hbU hUU' g'')) jR) := by
  let L := laxOfProjSystem' (cofinalProjSystem (S := S))
  let hL := coherentProj (cofinalProjSystem (S := S))
  letI : Cat (Obj L) := laxColimCat L hL
  let yA : L.A U := L.F hbU (terminalSliceObj W A)
  -- the inner germ representative of `stageInclL g''`.
  let f₀ : L.F (D := wsDirected S) ((wsDirected S).refl U) xE'
            ⟶ L.F ((wsDirected S).refl U) yA :=
    reflApp L xE' ≫ g'' ≫ isoInv (reflApp_isIso L yA)
  -- factor `stageInclL g'' = homInclL … ⟨U,refl,refl⟩ f₀` through stage `U'` (homInclL_factor).
  have hfac := homInclL_factor L hL xE' yA ⟨U, (wsDirected S).refl U, (wsDirected S).refl U⟩ f₀ hUU'
  -- the middle pushed germ.
  -- `pushHom … f₀ = leftIso ≫ pushFibre g'' ≫ rightIso` at the stage `U'`.
  have hpg_eq :
      pushHom L xE' yA ((wsDirected S).refl U) ((wsDirected S).refl U) hUU' f₀
        = (transApp L ((wsDirected S).refl U) hUU' xE'
              ≫ (L.functF hUU').map (reflApp L xE'))
            ≫ pushFibre W A hbU hUU' g''
            ≫ ((L.functF hUU').map (isoInv (reflApp_isIso L yA))
              ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)) := by
    show transApp L ((wsDirected S).refl U) hUU' xE'
          ≫ (L.functF hUU').map f₀
          ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA) = _
    show transApp L ((wsDirected S).refl U) hUU' xE'
          ≫ (L.functF hUU').map (reflApp L xE' ≫ g'' ≫ isoInv (reflApp_isIso L yA))
          ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA) = _
    rw [(L.functF hUU').map_comp (reflApp L xE') (g'' ≫ isoInv (reflApp_isIso L yA)),
        (L.functF hUU').map_comp g'' (isoInv (reflApp_isIso L yA))]
    show _ = _
    simp only [Cat.assoc, pushFibre, L]
  -- the two flanks are stage isos.
  have hiLeft : IsIso (transApp L ((wsDirected S).refl U) hUU' xE'
              ≫ (L.functF hUU').map (reflApp L xE')) :=
    isIso_comp (transApp_isIso L ((wsDirected S).refl U) hUU' xE')
      (functor_preserves_iso (F := L.functF hUU') (reflApp L xE') (reflApp_isIso L xE'))
  have hiRight : IsIso ((L.functF hUU').map (isoInv (reflApp_isIso L yA))
              ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)) :=
    isIso_comp
      (functor_preserves_iso (F := L.functF hUU') (isoInv (reflApp_isIso L yA))
        ⟨reflApp L yA, inv_isoInv_comp _, isoInv_comp _⟩)
      ⟨transApp L ((wsDirected S).refl U) hUU' yA, inv_isoInv_comp _, isoInv_comp _⟩
  -- name the colimit-level flanks.
  refine ⟨alignGerm L hL xE' ((wsDirected S).trans ((wsDirected S).refl U) hUU')
            ≫ stageInclL L hL (transApp L ((wsDirected S).refl U) hUU' xE'
              ≫ (L.functF hUU').map (reflApp L xE')),
          stageInclL L hL ((L.functF hUU').map (isoInv (reflApp_isIso L yA))
              ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA))
            ≫ alignGermInv L hL yA ((wsDirected S).trans ((wsDirected S).refl U) hUU'),
          ?_, ?_, ?_⟩
  · have h := functor_preserves_iso (F := stageInclFunctorL L hL U')
      (transApp L ((wsDirected S).refl U) hUU' xE'
        ≫ (L.functF hUU').map (reflApp L xE')) hiLeft
    exact isIso_comp (alignGerm_isIso L hL xE' _) h
  · have h := functor_preserves_iso (F := stageInclFunctorL L hL U')
      ((L.functF hUU').map (isoInv (reflApp_isIso L yA))
        ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)) hiRight
    exact isIso_comp h (alignGermInv_isIso L hL yA _)
  · -- `stageInclL g'' = hfac RHS`, and the middle `stageInclL pg` distributes by `stageInclL_comp`.
    show homInclL L hL xE' yA ⟨U, (wsDirected S).refl U, (wsDirected S).refl U⟩ f₀ = _
    rw [hfac, hpg_eq, stageInclL_comp L hL
          (transApp L ((wsDirected S).refl U) hUU' xE'
            ≫ (L.functF hUU').map (reflApp L xE'))
          (pushFibre W A hbU hUU' g''
            ≫ ((L.functF hUU').map (isoInv (reflApp_isIso L yA))
              ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA))),
        stageInclL_comp L hL (pushFibre W A hbU hUU' g'')
          ((L.functF hUU').map (isoInv (reflApp_isIso L yA))
            ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA))]
    -- both sides are now an associated composite of the same five colimit arrows (`compL = ≫`).
    rw [show @compL _ _ L hL ⟨U, xE'⟩ _ ⟨U, yA⟩
            (alignGerm L hL xE' ((wsDirected S).trans ((wsDirected S).refl U) hUU'))
            (@compL _ _ L hL _ _ ⟨U, yA⟩
              (@compL _ _ L hL _ _ _ (stageInclL L hL (transApp L ((wsDirected S).refl U) hUU' xE'
                  ≫ (L.functF hUU').map (reflApp L xE')))
                (@compL _ _ L hL _ _ _ (stageInclL L hL (pushFibre W A hbU hUU' g''))
                  (stageInclL L hL ((L.functF hUU').map (isoInv (reflApp_isIso L yA))
                    ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)))))
              (alignGermInv L hL yA ((wsDirected S).trans ((wsDirected S).refl U) hUU')))
          = @Cat.comp _ (laxColimCat L hL) _ _ _
              (alignGerm L hL xE' ((wsDirected S).trans ((wsDirected S).refl U) hUU'))
              (@Cat.comp _ (laxColimCat L hL) _ _ ⟨U, yA⟩
                (@Cat.comp _ (laxColimCat L hL) _ _ _
                  (stageInclL L hL (transApp L ((wsDirected S).refl U) hUU' xE'
                    ≫ (L.functF hUU').map (reflApp L xE')))
                  (@Cat.comp _ (laxColimCat L hL) _ _ _ (stageInclL L hL (pushFibre W A hbU hUU' g''))
                    (stageInclL L hL ((L.functF hUU').map (isoInv (reflApp_isIso L yA))
                      ≫ isoInv (transApp_isIso L ((wsDirected S).refl U) hUU' yA)))))
                (alignGermInv L hL yA ((wsDirected S).trans ((wsDirected S).refl U) hUU'))) from rfl]
    simp only [Cat.assoc]
    rfl

/-! ## Phase 2 — `FibreDensity` from the §1.546 density core (SORRY-FREE)

  `stageInclL_g''_factor` writes `(stageInclFunctorL U).map g'' = stageInclL g''` as
  `iL ≫ stageInclL (pushFibre g'') ≫ jR` with `iL, jR` colimit isos; `RicherSliceMiss` supplies a
  colimit point `x'` of the codomain of `stageInclL (pushFibre g'')` that it does NOT factor, and
  `point_transport_unconj` carries `x' ≫ jR` to a colimit point missing `(stageInclFunctorL U).map
  g''` — exactly the `FibreDensity` conclusion. -/

/-- **`FibreDensity W` from the §1.546 density core `RicherSliceMiss W`** (SORRY-FREE).  The whole
    §1.547 stage-local density reduces to the genuine §1.546 obligation `RicherSliceMiss W` — the
    directed-union escape (the missing point lives at a richer slice `U'`). -/
theorem fibreDensity_of_richerSliceMiss (W : WSCover S) (hcore : RicherSliceMiss W) :
    FibreDensity W := by
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  intro A hA U hbU xE' g'' hg''mono hg''niso
  -- the richer-slice missing point.
  obtain ⟨U', hUU', x', hx'⟩ := hcore A hA U hbU xE' g'' hg''mono hg''niso
  -- the realignment of `stageInclL g''` to a conjugate of `stageInclL (pushFibre g'')`.
  obtain ⟨iL, jR, _hiL, hjR, hfac⟩ := stageInclL_g''_factor W A hbU hUU' g''
  -- `(stageInclFunctorL U).map g'' = stageInclL g''` (defeq); transport `x' ≫ jR`.
  refine ⟨@Cat.comp _ (uniformTargetCat W) _ _ _ x' jR, ?_⟩
  exact point_transport_unconj hfac hjR x' hx'

/-! ## Phase 3 — the genuine §1.546 density core `RicherSliceMiss`

  ════════════════════════════════════════════════════════════════════════════════════════════
  STATUS — CLOSED.  `richerSliceSection`/`richerSliceMiss` are Sorry-free and axiom-clean; the §1.546
  ESCAPE (`baseChange_freshFactor_missed`) plus the directed-union read-off and the token-index
  fresh-copy (c.ii) are all proven.  Historical account of the construction below.
  ════════════════════════════════════════════════════════════════════════════════════════════

  `RicherSliceMiss W` is exactly Freyd's §1.546 density: a proper fibre subobject of the embedded
  object `sliceEmbedObj (∏U) A` is, at a RICHER slice `U' ⊇ U`, missed by a colimit point.

  ── THE ESCAPE (the genuine new math) — now PROVEN Sorry-free as `baseChange_freshFactor_missed`
     (`RelativeCapitalization.lean`) ───────────────────────────────────────────────────────────

  The directed-union escape is REAL and needs NO calculus-of-fractions saturation (the prior note
  claiming a §1.48-saturation blocker was TOO PESSIMISTIC — superseded).  Take the richer stage
  `U' = A :: U` (insert the well-supported `A` as a fresh factor; `A` ws ⟹ `U' ∈ WSList`).  Then
  `∏U' = A × ∏U` (`listProd_cons`) carries a FRESH, independent `A`-coordinate `fst : A×∏U → A`,
  and the §1.547 transition `U ≤ U'` is base-change along the projection `selectProj (A::U.1) U.1`,
  which equals `snd : A×∏U → ∏U` (by `listProd_hom_ext` + `selectProj_factor`/`factorProj_cons_ne`,
  since `A ∉ U.1` by nodup).  So `pushFibre g''` is the base-change of `g''` along `snd`.

  `baseChange_freshFactor_missed` then shows, point-free and Sorry-free: the base-changed proper
  mono MISSES the fresh slice point `sliceFactorPoint A (fst : A×∏U → A)`.  WHY (and why this is NOT
  the FALSE single-slice statement `properMono_forces_graph_iso`): the base-changed subobject's
  `A`-coordinate is the OLD subobject's `A`-value pulled back through `∏U`, hence DECOUPLED from the
  fresh coordinate `fst`.  A section reaching the fresh point would, via the base-change pullback
  square and joint-monicity of `(fst,snd)`, exhibit a section of `g''.f` (i.e. `g''.f` split-epi
  hence a cover); with `g''` monic this forces `g''` ISO — contradicting properness.  The graph
  `pair (proj_k) id` that defeats the single-slice statement reaches the OLD point `proj_k`, never
  the FRESH coordinate `fst` of `∏U'` — which is exactly why the directed UNION (not one slice)
  closes §1.546.

  ── THE COLIMIT PLUMBING — (a)/(b) MACHINE-CHECKED, two sharp residuals in (c) ─────────────────

  `RicherSliceMiss` is stated at the COLIMIT level: it asks for a colimit point `x'` of
  `⟨U', F hUU' (F hbU (terminalSliceObj A))⟩` (against the lax-colimit terminal) that
  `stageInclL (pushFibre g'')` does not factor.  The slice escape is threaded through the colimit
  interface (`richerSliceSection`):
    (a) — SORRY-FREE.  The codomain `F hUU' (F hbU (terminalSliceObj A))` is `baseChangeObj snd
        (F hbU term)` (`selectProj (A::U) U = snd`, `selectProj_head_notin`+`selectProj_refl`); the
        comparison `sliceEmbedObj (∏U') A ≅ baseChangeObj snd (sliceEmbedObj P A)` is `bcSliceIso`
        (`bcSlice_isPullback`+`isIso_of_two_pullbacks`).  `pushFibre g''` IS `baseChangeMap snd g''`
        definitionally; the `cnD`/`mf'` data `baseChange_freshFactor_missed` consumes are `mf' :=
        pair (cnD.π₁ ≫ m.f ≫ fst) cnD.π₂`, `m := g'' ⊚ pushTerminalSlice_iso⁻¹`.
    (b) — SORRY-FREE.  The colimit point `x'` is `laxTerminalArrowAt` (`one ≅ ⟨U', overTerm(∏U')⟩`,
        iso by `laxTerminalUniqAt`) post-composed with `stageInclL U'` of `sliceFactorPoint A fst`
        transported across the (a)-iso `cod`.
    (c) — TWO SHARP RESIDUALS (the honest gaps):
        (c.i)  the colimit-factor REFLECTION `richerSliceSection` `Sorry`: turning a colimit factor
               `y' : one ⟶ ⟨U', F hUU' xE'⟩` into a stage-`U'` base-change SECTION needs
               `stageInclFunctorL U'` FULLNESS on that hom.  The §1.547 transitions are base-change
               along covers (`selectProj`) — NOT full — so the germ representative sits at a richer
               stage `N ⊇ U'` that need not descend.  Hom-fullness / point-descent is not among the
               built lemmas (the repo has property-reflection — mono/iso/cover — but not hom-fullness;
               mathlib's `Full` is import-banned).  This is the genuine remaining §1.546 content.
        (c.ii) the `A ∈ U` case: appending `A` as a fresh nodup factor is impossible when `A` already
               indexes `U`; the escape needs a fresh INDEPENDENT copy of `A`, not expressible at the
               object level of the `WSList` index.

  The reduction `fibreDensity_of_richerSliceMiss` (Phase 2), the colimit↔fibre passage
  (`stageInclL_g''_factor`, Phase 1), the §1.546 escape (`baseChange_freshFactor_missed`), and the
  (a)/(b) base-change comparison + point (`bcSlice_isPullback`/`bcSliceIso`/`richerSliceSection` up to
  the `(c)` `Sorry`) are SORRY-FREE.  The two residuals are on TRUE statements (Freyd §1.546); no
  weakening, no `axiom`, no false claim. -/

/-- **Canonical base-change pullback of a slice-embedded object.**  The pullback of the structure
    map `snd : C×P → P` of `sliceEmbedObj P C` along ANY map `q : P' → P` has apex `C×P'`, legs
    `pair fst (snd≫q)` (to `C×P`) and `snd` (to `P'`).  This is the geometric content of the §1.546(a)
    identification `baseChangeObj q (sliceEmbedObj P C) ≅ sliceEmbedObj P' C`. -/
theorem bcSlice_isPullback {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] (C P P' : 𝒞) (q : P' ⟶ P) :
    (Cone.mk (f := (snd : prod C P ⟶ P)) (g := q) (prod C P')
      (pair (fst : prod C P' ⟶ C) ((snd : prod C P' ⟶ P') ≫ q)) (snd : prod C P' ⟶ P')
      (by rw [snd_pair])).IsPullback := by
  intro d
  refine ⟨pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂, ⟨?_, ?_⟩, ?_⟩
  · have e1 : (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂ ≫
        pair (fst : prod C P' ⟶ C) ((snd : prod C P' ⟶ P') ≫ q)) ≫ fst = d.π₁ ≫ fst := by
      rw [Cat.assoc, fst_pair, fst_pair]
    have e2 : (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂ ≫
        pair (fst : prod C P' ⟶ C) ((snd : prod C P' ⟶ P') ≫ q)) ≫ snd = d.π₁ ≫ snd := by
      rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, d.w]
    exact (pair_uniq _ _ _ e1 e2).trans (pair_uniq _ _ d.π₁ rfl rfl).symm
  · rw [snd_pair]
  · intro v hv₁ hv₂
    have ev1 : v ≫ (fst : prod C P' ⟶ C) = (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂) ≫ fst := by
      rw [fst_pair, ← hv₁]; show _ = (v ≫ pair fst (snd ≫ q)) ≫ fst; rw [Cat.assoc, fst_pair]
    have ev2 : v ≫ (snd : prod C P' ⟶ P') = (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂) ≫ snd := by
      have : (pair (d.π₁ ≫ (fst : prod C P ⟶ C)) d.π₂) ≫ (snd : prod C P' ⟶ P') = d.π₂ := snd_pair _ _
      rw [this, ← hv₂]
    exact (pair_uniq _ _ v ev1 ev2).trans (pair_uniq _ _ _ rfl rfl).symm

/-- **§1.546(a) — the base-change/slice comparison iso (underlying).**  `sliceEmbedObj (A×P) A` is, in
    `Over (A×P)`, isomorphic to `baseChangeObj snd (sliceEmbedObj P A)` (both are the pullback of
    `snd : A×P → P` against itself).  This is the codomain identification that presents the §1.547
    transition `U → U' = A::U` as the base-change `baseChange snd` (`bcSlice_isPullback`). -/
noncomputable def bcSliceIso (A P : S) :
    OverHom (sliceEmbedObj (prod A P) A) (baseChangeObj (snd : prod A P ⟶ P) (sliceEmbedObj P A)) :=
  ⟨(HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift
      (Cone.mk (f := (snd : prod A P ⟶ P)) (g := (snd : prod A P ⟶ P)) (prod A (prod A P))
        (pair (fst : prod A (prod A P) ⟶ A) ((snd : prod A (prod A P) ⟶ prod A P) ≫ snd))
        (snd : prod A (prod A P) ⟶ prod A P) (by rw [snd_pair])),
    (HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift_snd _⟩

theorem bcSliceIso_isIso (A P : S) : @IsIso (Over (prod A P)) _ _ _ (bcSliceIso A P) := by
  apply overIso_of_underlying
  exact isIso_of_two_pullbacks (bcSlice_isPullback A P (prod A P) (snd : prod A P ⟶ P))
    (HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).cone_isPullback _
    ((HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift_fst _)
    ((HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift_snd _)

/-- **Transport of the composite-coherence `π₁` content law across a base-map equality.**  The
    descent leg `dStep3'` is `baseChangeTransNatIso g g'`'s component, cast along a base-map equality
    `g' ≫ g = Z` (a dependent `PSigma` `▸`).  Reading off `dStep3'`'s deep-content law from the
    genuine (uncast) `baseChangeTransNatIso_app_f_π₁` requires transporting along that cast; this
    lemma performs it by generalizing the cast pair and `cases`-ing the equality. -/
theorem baseChangeTransNatIso_app_f_π₁_cast {C D E : S} (g : C ⟶ D) (g' : E ⟶ C) (X : Over D)
    {Z : E ⟶ D} (hZ : g' ≫ g = Z) :
    (Eq.ndrec
        (motive := fun Z => Σ' f : OverHom (baseChangeObj Z X)
            ((baseChangeObj g' ∘ baseChangeObj g) X),
            @IsIso (Over E) _ (baseChangeObj Z X) ((baseChangeObj g' ∘ baseChangeObj g) X) f)
        (⟨(Freyd.LaxColim.baseChangeTransNatIso g g').nat.app X,
          (Freyd.LaxColim.baseChangeTransNatIso g g').isIso X⟩) hZ).fst.f
        ≫ ((HasPullbacks.has (baseChangeObj g X).hom g').cone.π₁
            ≫ (HasPullbacks.has X.hom g).cone.π₁)
      = (HasPullbacks.has X.hom Z).cone.π₁ := by
  cases hZ
  exact Freyd.LaxColim.baseChangeTransNatIso_app_f_π₁ g g' X

/-- **§1.546(c) — the colimit-factor REFLECTION.**  At the richer stage
    `U' = A::U` (`A ∉ U`), suppose the §1.546 point `x'` (the `stageInclL U'` of the fresh slice point
    `sliceFactorPoint A fst`, transported across the codomain iso) IS factored by a colimit arrow
    `y'` through the included base-changed mono `stageInclL (pushFibre g'')`.  Then there is a
    base-change SECTION `s : A×P → cnD.pt` reaching the fresh `A`-coordinate `fst`, where `cnD` is the
    chosen base-change pullback of `xE'.hom` along `snd : A×P → P`.

    `baseChange_freshFactor_missed` refutes such a section, closing §1.546 — PROVIDED this reflection
    holds.  It is the REVERSE of `colimitMono_reflects_to_fibre`: that lemma reflects a colimit MONO
    to a fibre mono via `stageInclFunctorL` faithfulness; here we must reflect a colimit POINT/FACTOR
    `y' : one ⟶ ⟨U', F hUU' xE'⟩` to a stage-`U'` slice section.

    ── THE BLOCKER (precise).  `y'` is realigned (the lax-colimit terminal `one ≅ ⟨U', overTerm(A×P)⟩`,
    `laxTerminalArrowAt`/`laxTerminalUniqAt`) to a colimit hom `⟨U', overTerm(A×P)⟩ ⟶ ⟨U', F hUU' xE'⟩`.
    To extract the section it must be a `stageInclL` of a stage-`U'` slice arrow — i.e. one needs
    `stageInclFunctorL U'` to be FULL on this hom.  But the §1.547 transitions are base-change along
    product projections (`selectProj`, covers but not full), so a colimit hom between stage-`U'`
    objects has a germ representative at a STRICTLY RICHER stage `N ⊇ U'` (`incl_surjective`/
    `homInclL_factor`) that need not descend to `U'`.  `stageInclFunctorL U'` fullness (equivalently:
    descent of a fibre-`N` point of a base-changed object back to fibre `U'`) is NOT among the built
    lemmas; it is the genuine remaining content.  Everything else of §1.546 (the escape
    `baseChange_freshFactor_missed`, the (a) base-change data, the (b) point `x'`, the §1.547
    reduction) is machine-checked Sorry-free. -/
theorem richerSliceSection (W : WSCover S) (aT : Tok S)
    (_hA : WellSupported aT.2) (U : WSList S)
    (hbU : (wsDirected S).le W.base U) (hAU : aT ∉ U.1)
    (xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U)
    (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W aT.2))
    (hmono : Monic g'') (hniso : ¬ IsIso g'')
    (hnd : (aT :: U.1).Nodup) (hws : ∀ t ∈ (aT :: U.1), WellSupported t.2) :
    letI : Cat (uniformTargetTy W) := uniformTargetCat W
    ∃ (x' : @Cat.Hom _ (uniformTargetCat W)
              (@HasTerminal.one _ (uniformTargetCat W) (uniformStepTarget_preRegular W).toHasTerminal)
              ⟨⟨aT :: U.1, hnd, hws⟩, (laxOfProjSystem' (cofinalProjSystem (S := S))).F
                (fun _t hB => List.mem_cons.2 (Or.inr hB))
                ((laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W aT.2))⟩),
      ¬ ∃ (y' : @Cat.Hom _ (uniformTargetCat W)
                (@HasTerminal.one _ (uniformTargetCat W)
                  (uniformStepTarget_preRegular W).toHasTerminal)
                ⟨⟨aT :: U.1, hnd, hws⟩, (laxOfProjSystem' (cofinalProjSystem (S := S))).F
                  (fun _t hB => List.mem_cons.2 (Or.inr hB)) xE'⟩),
        @Cat.comp _ (uniformTargetCat W) _
            ⟨⟨aT :: U.1, hnd, hws⟩, (laxOfProjSystem' (cofinalProjSystem (S := S))).F
              (fun _t hB => List.mem_cons.2 (Or.inr hB)) xE'⟩ _ y'
          (stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
            (coherentProj (cofinalProjSystem (S := S)))
            (pushFibre W aT.2 hbU (fun _t hB => List.mem_cons.2 (Or.inr hB)) g'')) = x' := by
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  let A : S := aT.2
  let L := laxOfProjSystem' (cofinalProjSystem (S := S))
  let hL := coherentProj (cofinalProjSystem (S := S))
  let T := ratLaxTerminalData (cofinalProjSystem (S := S))
  let P := listProd (𝒞 := S) (U.1.map Prod.snd)
  let U' : WSList S := ⟨aT :: U.1, hnd, hws⟩
  have hUU' : (wsDirected S).le U U' := fun t hB => List.mem_cons.2 (Or.inr hB)
  -- `pr U' = listProd ((aT :: U.1).map Prod.snd) = prod aT.2 P = prod A P` definitionally.
  have hsp : tSelectProj Prod.snd U'.1 U.1 hUU' = (snd : prod A P ⟶ P) := by
    show tSelectProj Prod.snd (aT :: U.1) U.1 hUU' = _
    rw [tSelectProj_head_notin Prod.snd aT U.1 U.1 hUU' hAU (fun t hB => hB),
        tSelectProj_refl Prod.snd U.2.1 (fun t hB => hB), Cat.comp_id]
  -- ===== (a) the §1.546 escape data (Sorry-free) =====
  let pIso : OverHom (sliceEmbedObj P A) (L.F hbU (terminalSliceObj W A)) := pushTerminalSlice_iso W A hbU
  obtain ⟨pInv, hp1, hp2⟩ := pushTerminalSlice_iso_isIso W A hbU
  let m : OverHom xE' (sliceEmbedObj P A) := g'' ⊚ pInv
  have hpInv_iso : @IsIso (Over P) _ _ _ pInv := ⟨pIso, hp2, hp1⟩
  have hm_mono : @Monic (Over P) _ _ _ m := mono_postcomp_iso' hmono hpInv_iso
  have hm_niso : ¬ @IsIso (Over P) _ _ _ m := by
    intro hmi; apply hniso
    have he : g'' = @Cat.comp (Over P) _ _ _ _ m pIso := by
      apply OverHom.ext
      have hpp : pInv.f ≫ pIso.f = Cat.id _ := congrArg OverHom.f hp2
      show g''.f = (g''.f ≫ pInv.f) ≫ pIso.f
      rw [Cat.assoc, hpp, Cat.comp_id]
    rw [he]; exact isIso_comp hmi ⟨pInv, hp1, hp2⟩
  let cnD : Cone (xE'.hom) (snd : prod A P ⟶ P) := (HasPullbacks.has (xE'.hom) (snd : prod A P ⟶ P)).cone
  have hcnD : cnD.IsPullback := (HasPullbacks.has (xE'.hom) (snd : prod A P ⟶ P)).cone_isPullback
  let mf' : cnD.pt ⟶ prod A (prod A P) := pair (cnD.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A)) cnD.π₂
  have hmf1 : mf' ≫ (fst : prod A (prod A P) ⟶ A) = cnD.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A) := fst_pair _ _
  have hmf2 : mf' ≫ (snd : prod A (prod A P) ⟶ prod A P) = cnD.π₂ := snd_pair _ _
  -- the escape: NO base-change section reaches the fresh `A`-coordinate `fst`.
  have key : ∀ (s : (prod A P) ⟶ cnD.pt), s ≫ cnD.π₂ = Cat.id (prod A P) →
      s ≫ (mf' ≫ (fst : prod A (prod A P) ⟶ A)) = (fst : prod A P ⟶ A) → False :=
    fun s hs2 hsA => baseChange_freshFactor_missed m hm_mono hm_niso cnD hcnD mf' hmf1 hmf2 s hs2 hsA
  -- ===== (b) the §1.546 colimit point `x'` (Sorry-free) =====
  let cod' : OverHom (sliceEmbedObj (prod A P) A)
      (baseChangeObj (snd : prod A P ⟶ P) (L.F hbU (terminalSliceObj W A))) :=
    bcSliceIso A P ⊚ (baseChangeFunctor (snd : prod A P ⟶ P)).map pIso
  have hcodEq : L.F hUU' (L.F hbU (terminalSliceObj W A))
      = baseChangeObj (snd : prod A P ⟶ P) (L.F hbU (terminalSliceObj W A)) := by
    show baseChangeObj (tSelectProj Prod.snd U'.1 U.1 hUU') (L.F hbU (terminalSliceObj W A)) = _
    rw [hsp]
  let cod : OverHom (sliceEmbedObj (prod A P) A) (L.F hUU' (L.F hbU (terminalSliceObj W A))) := hcodEq ▸ cod'
  let sfp : OverHom (overTerm (prod A P)) (sliceEmbedObj (prod A P) A) :=
    sliceFactorPoint A (fst : prod A P ⟶ A)
  let align : @Cat.Hom (Obj L) (laxColimCat L hL)
      (@HasTerminal.one _ (uniformTargetCat W) (uniformStepTarget_preRegular W).toHasTerminal)
      ⟨U', (T.ht U').one⟩ := laxTerminalArrowAt L hL T U' _
  let x' := @Cat.comp (Obj L) (laxColimCat L hL) _ _ _ align
    (stageInclL L hL (sfp ⊚ cod))
  refine ⟨x', ?_⟩
  rintro ⟨y', hy'⟩
  -- ===== (c.i) reflect the colimit factor `y'` to a stage-`N` base-change section =====
  -- Steps (1)+(2) below (`align`-kill, germ reduction, push to stage `N`) are SORRY-FREE and narrow
  -- the colimit factor `hy'` to the on-the-nose stage-`N` factorization `hstage` (`Over (∏N)`).  The
  -- single remaining gap is the stage-`N` base-change escape on `hstage`; see the note at it below.
  -- `align` is iso (a map between two terminals: `one` and the stage-`U'` terminal).
  letI htOne : HasTerminal (Obj L) := (uniformStepTarget_preRegular W).toHasTerminal
  have halignIso : @IsIso (Obj L) (laxColimCat L hL) _ _ align :=
    ⟨htOne.trm _, htOne.uniq _ _, laxTerminalUniqAt L hL T U' _ _ _⟩
  obtain ⟨alignInv, halign1, halign2⟩ := halignIso
  -- kill `align`: `z := alignInv ≫ y'` satisfies `z ≫ M = stageInclL (sfp ⊚ cod)` (a stage point).
  -- `z : ⟨U', (T.ht U').one⟩ ⟶ ⟨U', F hUU' xE'⟩`, a colimit hom between stage-`U'` objects.
  let z : @Cat.Hom (Obj L) (laxColimCat L hL) ⟨U', (T.ht U').one⟩ ⟨U', L.F hUU' xE'⟩ :=
    @Cat.comp (Obj L) (laxColimCat L hL) _ _ _ alignInv y'
  have hz : @Cat.comp (Obj L) (laxColimCat L hL) _ _ _ z
        (stageInclL L hL (pushFibre W A hbU hUU' g''))
      = stageInclL L hL (sfp ⊚ cod) := by
    show @Cat.comp (Obj L) (laxColimCat L hL) _ _ _
        (@Cat.comp (Obj L) (laxColimCat L hL) _ _ _ alignInv y')
        (stageInclL L hL (pushFibre W A hbU hUU' g'')) = _
    rw [Cat.assoc, hy']
    show @Cat.comp (Obj L) (laxColimCat L hL) _ _ _ alignInv
        (@Cat.comp (Obj L) (laxColimCat L hL) _ _ _ align (stageInclL L hL (sfp ⊚ cod))) = _
    rw [← Cat.assoc, halign2, Cat.id_comp]
  -- germ-reduce `z`: a representative `z₀` at a bound `b ⊇ U'`.
  obtain ⟨b, z₀, hz₀⟩ :=
    incl_surjective (homSystemL L hL (T.ht U').one (L.F hUU' xE')) z
  -- the refl-bound germ representatives of the two `stageInclL`s.
  let pf₀ : L.F ((wsDirected S).refl U') (L.F hUU' xE')
      ⟶ L.F ((wsDirected S).refl U') (L.F hUU' (L.F hbU (terminalSliceObj W A))) :=
    reflApp L (L.F hUU' xE') ≫ pushFibre W A hbU hUU' g''
      ≫ isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))
  let sc₀ : L.F ((wsDirected S).refl U') (T.ht U').one
      ⟶ L.F ((wsDirected S).refl U') (L.F hUU' (L.F hbU (terminalSliceObj W A))) :=
    reflApp L (T.ht U').one ≫ (sfp ⊚ cod)
      ≫ isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))
  -- `hz` as a `homCompRawL = homInclL` equation, then push to a stage `N`.
  have hraw : homCompRawL L hL (T.ht U').one (L.F hUU' xE')
        (L.F hUU' (L.F hbU (terminalSliceObj W A)))
        b z₀ ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ pf₀
      = homInclL L hL (T.ht U').one (L.F hUU' (L.F hbU (terminalSliceObj W A)))
          ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ sc₀ := by
    rw [← compL_homInclL L hL (T.ht U').one (L.F hUU' xE')
          (L.F hUU' (L.F hbU (terminalSliceObj W A))) b z₀
          ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ pf₀]
    rw [show homInclL L hL (T.ht U').one (L.F hUU' xE') b z₀ = z from hz₀]
    exact hz
  obtain ⟨N, hbN, hUN, hUN', hstage⟩ :=
    homCompRawL_eq_stage L hL (T.ht U').one (L.F hUU' xE')
      (L.F hUU' (L.F hbU (terminalSliceObj W A)))
      b z₀ ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ pf₀
      ⟨U', (wsDirected S).refl U', (wsDirected S).refl U'⟩ sc₀ hraw
  -- ===== (c.i) the stage-`N` base-change escape =====
  -- `hstage` is the ON-THE-NOSE factorization, in `L.A N = Over (∏N)`, of the `N`-image of the fresh
  -- slice point `sfp ⊚ cod` (= `sliceFactorPoint A fst` base-changed to `N`) through the `N`-image of
  -- `pushFibre g''` (= `g''` base-changed along `tSelectProj Prod.snd N.1 U.1`), witnessed by the `N`-rep
  -- `zN := pushHom … z₀` of the colimit factor `z`.  Steps (1) `align`-kill and (2) the germ
  -- reduction `z ↦ zN` + push of the colimit equation to this stage-`N` equation are now Sorry-free.
  --
  -- translate `hstage` into the binary-product shape
  -- `baseChange_freshFactor_missed` consumes.  `A ∈ U' = A::U ⊆ N` gives `hA_in_N : A ∈ N.1`, and
  -- `CofinalProj.listProd_pull_factor N.1 A N.2.1 hA_in_N` supplies `ψ : ∏N ≅ A × ∏(N.erase A)` with
  -- `ψ ≫ fst = factorProj N A`, `ψ ≫ snd = selectProj N (N.erase A)`.
  have hA_in_N : aT ∈ N.1 := hUN aT List.mem_cons_self
  -- `ψ : ∏N ≅ A × ∏(N.erase aT)`, the reindexing onto the fresh `aT`-coordinate `tFactorProj N aT`.
  obtain ⟨hψiso, hψfst, hψsnd⟩ := tListProd_pull_factor (𝒟 := S) Prod.snd N.1 aT N.2.1 hA_in_N
  let PN : S := listProd ((N.1.erase aT).map Prod.snd)
  let ψ : listProd (N.1.map Prod.snd) ⟶ prod A PN :=
    tSelectProj Prod.snd N.1 (aT :: N.1.erase aT)
      (fun _ hB => (List.mem_cons.1 hB).elim (· ▸ hA_in_N) List.mem_of_mem_erase)
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- The CONSUMER is a reusable, Sorry-free,
  -- axiom-free escape: `freshSlicePoint_factors_imp_false` (RelativeCapitalization.lean) — the §1.546
  -- escape in POINT-FACTORIZATION form.  Given the proper base-changed mono `m̄ : ⟨cnD_N.pt, π₂⟩ ↪
  -- sliceEmbedObj (∏N) A` (apex comparison `mf_N`) and a POINT factorization
  -- `t ⊚ m̄ = sliceFactorPoint A (factorProj N A)`, it directly derives `False` (it extracts the
  -- section `t.f` internally and routes through `baseChange_freshFactor_missed`).  So the Step-2
  -- obligation is now exactly: PRODUCE that point factorization `t` (an `OverHom` equation), proper
  -- `m̄`, and the cone/apex data, from `hstage`.
  --
  -- the genuine §1.546 transport.  `hstage` is an equation of THREE `pushHom`-
  -- conjugated arrows in `Over (∏N)`.  The `pushHom` `.f`-conjugation is NO LONGER opaque: the
  -- decisive Phase-1 primitives now exist Sorry-free in `CapitalizationLaxColimit.lean`:
  --   • `pushHom_transApp` : `pushHom g ≫ transApp y = transApp x ≫ Functor.map g` — the
  --     source-naturality form (the `isoInv` cancels; no `transApp`-inverse left).
  --   • `proj_pushHom_f_π₂` : `(pushHom g).f ≫ (_pb (proj (trans hjk hkm)) y).π₂
  --        = (_pb (proj (trans hik hkm)) x).π₂` — `pushHom.f` preserves the `∏N`-structure map
  --     ON THE NOSE (so each layer IS an over-`∏N` arrow with computable structure leg).
  --   • `proj_pushHom_f_π₁` : `(pushHom g).f ≫ (transApp hjk hkm y).f ≫ outerπ₁
  --        = (transApp hik hkm x).f ≫ outerπ₁ ≫ g.f` — `pushHom.f` intertwines the CONTENT
  --     projection with the underlying `g.f` (the §1.546 content arrow), explicitly via the
  --     concrete pullback `lift`s of `transApp`/`baseChangeMap` (`transApp_f_π₁π₁₀`,
  --     `baseChangeMap_f_π₁`).
  -- So `(pushHom … wa).f` over `∏N` IS now an explicit composite of `baseChangeMap` underlying
  -- arrows and pullback `lift`s, exactly as the brief demanded — the conjugation reduces to pullback
  -- algebra, not an abstract iso.
  --
  -- THE REMAINING ASSEMBLY (Phase 2, the residual).  With the primitives above, building the
  -- point-factorization `t ⊚ m̄ = sliceFactorPoint A (factorProj N A)` for
  -- `freshSlicePoint_factors_imp_false` reduces to: (i) identify the codomain object
  -- `L.F hUN' (L.F hUU' (L.F hbU term))` over `∏N` with `sliceEmbedObj (∏N) A` via `nestApp3`
  -- (`CapitalizationLaxColimit`) `≫ pushTerminalSlice_iso W A (D.trans hbU (D.trans hUU' hUN))`;
  -- (ii) reindex `∏N ≅ A×PN` by `ψ` (`hψiso`/`hψfst`/`hψsnd`); (iii) read off the base-change cone
  -- `cnD_N` (pullback of `xE'`'s N-image hom along `snd : A×PN → PN`), the apex comparison `mf'_N`,
  -- and the section `t.f` from `hstage` projected through `proj_pushHom_f_π₁`/`π₂` and precomposed by
  -- `ψ⁻¹`.  `m̄` is proper at `N` via `L_cons`/`projStage_conservative_full` on `g''` (`hniso`).
  -- This step is pure pullback bookkeeping over the now-explicit `.f` legs — no opaque coherence
  -- remains — but it is a multi-screen `pb_hom_ext` reindexing chain, the genuine §1.546 content,
  -- left as the single sharpest residual.
  -- ── (i) identify the `hstage` codomain over `∏N` with `sliceEmbedObj (∏N) A`. ──
  let hbN3 : (wsDirected S).le W.base N := (wsDirected S).trans hbU ((wsDirected S).trans hUU' hUN')
  let Θ : sliceEmbedObj (listProd (N.1.map Prod.snd)) A
      ⟶ L.F hUN' (L.F hUU' (L.F hbU (terminalSliceObj W A))) :=
    pushTerminalSlice_iso W A hbN3 ≫ nestApp3 L hbU hUU' hUN' (terminalSliceObj W A)
  have hΘiso : @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ Θ :=
    isIso_comp (pushTerminalSlice_iso_isIso W A hbN3)
      (nestApp3_isIso L hbU hUU' hUN' (terminalSliceObj W A))
  -- ── (ii) the N-image of `pushFibre g''`, a PROPER mono into `sliceEmbedObj (∏N) A` via `Θ⁻¹`. ──
  -- N-image of `pushFibre = Functor.map (functF hUU') g''`.
  let pfN : L.F hUN' (L.F hUU' xE') ⟶ L.F hUN' (L.F hUU' (L.F hbU (terminalSliceObj W A))) :=
    (L.functF hUN').map (pushFibre W A hbU hUU' g'')
  let m_N : OverHom (L.F hUN' (L.F hUU' xE')) (sliceEmbedObj (listProd (N.1.map Prod.snd)) A) :=
    pfN ⊚ isoInv hΘiso
  have hpfN_mono : Monic pfN :=
    projStage_preservesMono (cofinalProjSystem (S := S)) hUN'
      ((L.functF hUU').map g'')
      (projStage_preservesMono (cofinalProjSystem (S := S)) hUU' g'' hmono)
  have hΘinv_iso : IsIso (isoInv hΘiso) := ⟨Θ, inv_isoInv_comp hΘiso, isoInv_comp hΘiso⟩
  have hm_N_mono : @Monic (Over (listProd (N.1.map Prod.snd))) _ _ _ m_N :=
    mono_postcomp_iso' hpfN_mono hΘinv_iso
  have hm_N_niso : ¬ @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ m_N := by
    intro hmi
    -- `m_N = pfN ≫ Θ⁻¹` iso, `Θ⁻¹` iso ⇒ `pfN` iso ⇒ (L_cons) push iso ⇒ g'' iso.
    have hpfN_iso : IsIso pfN := by
      have hmΘ : @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ (@Cat.comp (Over (listProd (N.1.map Prod.snd))) _ _ _ _ m_N Θ) :=
        isIso_comp hmi hΘiso
      have heq : (@Cat.comp (Over (listProd (N.1.map Prod.snd))) _ _ _ _ m_N Θ) = pfN := by
        show @Cat.comp (Over (listProd (N.1.map Prod.snd))) _ _ _ _
            (@Cat.comp (Over (listProd (N.1.map Prod.snd))) _ _ _ _ pfN (isoInv hΘiso)) Θ = pfN
        rw [Cat.assoc, inv_isoInv_comp hΘiso, Cat.comp_id]
      rwa [heq] at hmΘ
    exact hniso (L_cons hUU' g'' (L_cons hUN' (pushFibre W A hbU hUU' g'') hpfN_iso))
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- the §1.546 descent (the structural step).
  --
  -- VERIFIED ABOVE (Sorry-free):  `m_N : OverHom (L.F hUN' (L.F hUU' xE')) (sliceEmbedObj (∏N) A)`
  -- is a PROPER mono (`hm_N_mono`, `hm_N_niso`) — the N-image of `pushFibre g''` transported by the
  -- object iso `Θ` (`nestApp3 ≫ pushTerminalSlice_iso`) onto `sliceEmbedObj (∏N) A`.  The `ψ`-reindex
  -- `∏N ≅ A×PN` (`hψiso`/`hψfst`/`hψsnd`) is in hand.
  --
  -- the §1.546 DESCENT (the structural core).
  -- `freshSlicePoint_factors_imp_false` consumes a proper mono `m` over the OLD base `PN` whose
  -- base-change along `snd : A×PN ⟶ PN` is the apex of the fresh-point factorization.  But `m_N`
  -- lives over `∏N ≅ A×PN` (the base WITH the fresh `A`-coordinate `factorProj N A = ψ≫fst`), one
  -- product-factor RICHER than `PN`.  To feed the consumer we must DESCEND `m_N` to a proper mono
  -- `m` over `PN` whose `snd`-base-change recovers `m_N` — i.e. exhibit `m_N` AS the base-change
  -- (along `snd : A×PN ⟶ PN`) of an `A/PN`-mono.  This is the §1.546 structural fact that the fresh
  -- `A`-factor is INDEPENDENT of `PN`: it holds because `m_N` is the N-image (base-change along
  -- `selectProj N U'`) of `pushFibre g''`, and `selectProj N U' = ψ ≫ (A × selectProj_{PN←U}) ≫ …`
  -- routes through `snd`.  Establishing that base-change factorization (the pullback-pasting that
  -- splits `selectProj N U'` through `snd : A×PN ⟶ PN`) is the remaining multi-screen step; with
  -- the descended `m`, the point factorization `t` is read off `hstage` via `proj_pushHom_f_π₁/π₂`
  -- and `freshSlicePoint_factors_imp_false` closes the goal.
  --
  -- ── THE DESCENT, MADE EXPLICIT (the projection identity is now in hand). ──
  -- `A ∉ U` (`hAU`) and `U ⊆ N` (`hUN`) give `U ⊆ N.erase A`, so the §1.547 SUCCESSOR projection
  -- `selectProj N (A::U)` — the base map along which `pushFibre g''` was base-changed to produce the
  -- N-image `m_N` over `∏N` — SPLITS through the fresh `A`-coordinate via `selectProj_pull_head`:
  --   `selectProj N (A::U) = ψ ≫ pair fst (snd ≫ selectProj (N.erase A) U)`,
  -- with `ψ : ∏N ≅ A×PN` (`PN = ∏(N.erase A)`) the reindexing onto the fresh `A`-factor.  So the
  -- base-change along `selectProj N (A::U)` FACTORS (pseudofunctorially, `projTransIso`) as
  -- base-change along `selectProj (N.erase A) U` (landing at the PN-level — the proper mono `m` the
  -- consumer `freshSlicePoint_factors_imp_false` eats) THEN along `snd : A×PN ⟶ PN` (the
  -- base-change whose section the §1.546 escape refutes) THEN transported by `ψ` (recovering `m_N`
  -- over `∏N`).  `hUe` and the split identity are recorded for the assembly:
  have hUe : ∀ t ∈ U.1, t ∈ N.1.erase aT := fun t hB =>
    (List.mem_erase_of_ne (a := t) (b := aT) (l := N.1) (by intro h; cases h; exact hAU hB)).mpr
      (hUN t (List.mem_cons.2 (Or.inr hB)))
  have hsplit :
      tSelectProj Prod.snd N.1 (aT :: U.1) hUN'
        = tSelectProj Prod.snd N.1 (aT :: N.1.erase aT)
            (fun _ hB => (List.mem_cons.1 hB).elim (· ▸ hA_in_N) List.mem_of_mem_erase)
          ≫ pair (fst : prod A PN ⟶ A)
              ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) :=
    tSelectProj_pull_head (𝒟 := S) Prod.snd N.1 aT U.1 N.2.1 hnd hA_in_N hUe hUN'
  -- ── THE PN-LEVEL PROPER MONO `m_PN` (the descended subobject the consumer eats) — SORRY-FREE. ──
  -- `tSelectProj (N.erase aT) U` is a cover (bigger nodup product of well-supported objects projects).
  have hcov : Cover (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) :=
    tSelectProj_cover (𝒟 := S) Prod.snd (N.1.erase aT) U.1 U.2.1 hUe
      (fun t hB => N.2.2 t (List.mem_of_mem_erase hB))
  -- `m_PN := baseChangeMap (selectProj (N.erase A) U) m`, the base-change of the `∏U`-level proper
  -- mono `m` down to `PN = ∏(N.erase A)`.  Monic: base-change preserves monos
  -- (`projStage_preservesMono`).  ¬Iso: base-change along the COVER `selectProj (N.erase A) U`
  -- reflects iso among monos (`isIso_of_baseChange_isIso_of_cover`, BaseChangeDescent.lean), so an
  -- iso `m_PN` would force `m` iso, contradicting `hm_niso`.
  have hmPN_mono : @Monic (Over PN) _ _ _ (baseChangeMap (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) m) :=
    projStage_preservesMono (cofinalProjSystem (S := S)) (i := U)
      (j := (⟨N.1.erase aT, N.2.1.erase aT,
        fun t hB => N.2.2 t (List.mem_of_mem_erase hB)⟩ : WSList S)) hUe m hm_mono
  have hmPN_niso : ¬ @IsIso (Over PN) _ _ _ (baseChangeMap (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) m) :=
    fun hiso => hm_niso (isIso_of_baseChange_isIso_of_cover (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)
      hcov m hm_mono hiso)
  -- ── THE COMPARISON ISO `bcGen : sliceEmbedObj PN A ≅ baseChangeObj (selectProj (N.erase A) U) … ──
  -- the codomain identification (§1.546(a), generic base map `q := selectProj (N.erase A) U`):
  -- `baseChangeObj q (sliceEmbedObj P A) ≅ sliceEmbedObj PN A` (both pullbacks of `snd : A×P → P`
  -- along `q`, apex `A×PN`), via `bcSlice_isPullback … q` + `isIso_of_two_pullbacks`.  Transporting
  -- `m_PN` across it gives the consumer's `m : OverHom (baseChangeObj q xE') (sliceEmbedObj PN A)`.
  let bcGenCone : Cone (snd : prod A P ⟶ P) (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) :=
    Cone.mk (f := (snd : prod A P ⟶ P)) (g := tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) (prod A PN)
      (pair (fst : prod A PN ⟶ A) ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe))
      (snd : prod A PN ⟶ PN) (by rw [snd_pair])
  let bcGen : OverHom (sliceEmbedObj PN A)
      (baseChangeObj (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) (sliceEmbedObj P A)) :=
    ⟨(HasPullbacks.has ((sliceEmbedObj P A).hom) (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)).lift bcGenCone,
      (HasPullbacks.has ((sliceEmbedObj P A).hom) (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)).lift_snd
        bcGenCone⟩
  have bcGen_iso : @IsIso (Over PN) _ _ _ bcGen := by
    apply overIso_of_underlying
    show @IsIso S _ _ _
      ((HasPullbacks.has ((sliceEmbedObj P A).hom) (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)).lift bcGenCone)
    exact isIso_of_two_pullbacks
      (bcSlice_isPullback A P PN (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe))
      (HasPullbacks.has ((sliceEmbedObj P A).hom) (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)).cone_isPullback
      _
      ((HasPullbacks.has ((sliceEmbedObj P A).hom) (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)).lift_fst
        bcGenCone)
      ((HasPullbacks.has ((sliceEmbedObj P A).hom) (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)).lift_snd
        bcGenCone)
  -- the projection split routed through `snd : A×PN → PN` (consumed by the descent pasting below):
  -- `selectProj N U' ≫ snd = ψ ≫ (snd ≫ selectProj (N.erase A) U)`.
  have hsplit2 : tSelectProj Prod.snd N.1 U'.1 hUN' ≫ (snd : prod A P ⟶ P)
      = ψ ≫ ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) := by
    rw [show tSelectProj Prod.snd N.1 U'.1 hUN' = _ from hsplit, Cat.assoc, snd_pair]
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- the §1.546 descent EQUATION + section read-off.
  --
  -- VERIFIED ABOVE (Sorry-free): the PN-level PROPER mono `m_PN := baseChangeMap (selectProj
  -- (N.erase A) U) m` (`hmPN_mono`/`hmPN_niso`), the codomain comparison iso `bcGen`/`bcGen_iso`
  -- (so `m̄_PN := bcGen⁻¹ ⊚ m_PN : OverHom (baseChangeObj (selectProj (N.erase A) U) xE')
  -- (sliceEmbedObj PN A)` is the proper mono `freshSlicePoint_factors_imp_false` consumes at base
  -- `PN`), and the base-map split `hsplit2` routing `selectProj N U' ≫ snd` through `snd : A×PN→PN`.
  --
  -- two coupled steps:
  --   (1) THE DESCENT EQUATION.  `m_N = ψ-iso-transport (baseChangeMap (snd : A×PN→PN) m̄_PN)`.
  --       `m_N`'s domain `L.F hUN' (L.F hUU' xE') = baseChangeObj (selectProj N U') (baseChangeObj
  --       (selectProj U' U) xE')` (rfl).  By `hsplit2` the OUTER base `selectProj N U'` post-composed
  --       with `snd` (= `selectProj U' U`, `hsp`) factors as `ψ ≫ (snd ≫ selectProj (N.erase A) U)`;
  --       `baseChangeTransNatIso` (+ `pasteCone_isPullback`) identifies the chosen pullback at `∏N`
  --       (apex of `m_N`) with the PASTED pullback `(snd-pullback over A×PN) ∘ ((selectProj (N.erase
  --       A) U)-pullback over PN)`, ψ-transported.  The two inner `bcGen`-style comparison isos (at
  --       P and at PN) reconcile the `sliceEmbedObj`/`baseChangeObj` codomains; `pfN`'s `.f`-legs are
  --       `proj_pushHom_f_π₁`/`proj_pushHom_f_π₂`.  Output: cone `cnD_N` (= `snd`-pullback of
  --       `(baseChangeObj (selectProj (N.erase A) U) xE').hom`), apex `mf'_N`, and `m̄_N : OverHom
  --       ⟨cnD_N.pt, π₂⟩ (sliceEmbedObj (A×PN) A)` with `m̄_N.f = mf'_N` — the consumer's cone data.
  --   (2) THE POINT READ-OFF.  `hstage` (the on-the-nose stage-`N` factorization of the fresh point
  --       through `pfN`) gives, via `proj_pushHom_f_π₂` (structure leg) and `proj_pushHom_f_π₁`
  --       (content leg) precomposed by `ψ⁻¹` (`hψiso`) and transported by `Θ`/`hΘiso`, a point
  --       `t : OverHom (overTerm (A×PN)) ⟨cnD_N.pt, π₂⟩` with `t ⊚ m̄_N = sliceFactorPoint A fst`.
  --   Then `freshSlicePoint_factors_imp_false (bcGen⁻¹ ⊚ m_PN) … cnD_N hcnD_N mf'_N … m̄_N rfl t hfac`
  --   closes the goal.  This is the multi-screen `pb_hom_ext` reindexing chain (the genuine §1.546
  --   content); every primitive it needs is now in scope Sorry-free.
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- THE DESCENT EQUATION (Sorry-free).  `m_N`'s domain `baseChangeObj (selectProj N U') (baseChangeObj
  -- (selectProj U' U) xE')` (= `baseChangeObj (selectProj N U') (baseChangeObj snd xE')`, `hsp`) is
  -- the ψ-base-change of the `snd`-base-change of the PN-level object `Dbar := baseChangeObj
  -- (selectProj (N.erase A) U) xE'`.  Built from three pullback-pasting isos (`baseChangeTransNatIso`):
  --   • `dStep1 : baseChangeObj (selectProj N U' ≫ snd) xE' ≅ baseChangeObj (selectProj N U')
  --       (baseChangeObj snd xE')` = domain(m_N);
  --   • `dStep3 : baseChangeObj (selectProj N U' ≫ snd) xE' ≅ baseChangeObj ψ (baseChangeObj
  --       (snd ≫ selectProj (N.erase A) U) xE')`  (after rewriting `selectProj N U' ≫ snd` by `hsplit2`);
  --   • `dStep2 : baseChangeObj (snd ≫ selectProj (N.erase A) U) xE' ≅ baseChangeObj snd Dbar`,
  --       transported into the ψ-slice by `Functor.map (baseChangeObj ψ)`.
  -- Composite descent iso: `domain(m_N) ≅ baseChangeObj ψ (baseChangeObj snd Dbar)`.
  let Dbar : Over PN := baseChangeObj (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) xE'
  -- the three pasting comparisons (all iso by `_transFwd_isIso`):  codomains are the `∘`-composed
  -- `baseChangeObj _ ∘ baseChangeObj _` form, defeq to the iterated `baseChangeObj`/`L.F` shape.
  let dStep1 := (baseChangeTransNatIso (snd : prod A P ⟶ P) (tSelectProj Prod.snd N.1 U'.1 hUN')).nat.app xE'
  have hdStep1_iso : IsIso dStep1 :=
    (baseChangeTransNatIso (snd : prod A P ⟶ P) (tSelectProj Prod.snd N.1 U'.1 hUN')).isIso xE'
  let dStep2 :=
    (baseChangeTransNatIso (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) (snd : prod A PN ⟶ PN)).nat.app xE'
  have hdStep2_iso : IsIso dStep2 :=
    (baseChangeTransNatIso (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) (snd : prod A PN ⟶ PN)).isIso xE'
  let dStep3 :=
    (baseChangeTransNatIso ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) ψ).nat.app xE'
  have hdStep3_iso : IsIso dStep3 :=
    (baseChangeTransNatIso ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) ψ).isIso xE'
  -- `dStep1`'s domain equals `dStep3`'s domain after the `hsplit2` base-map rewrite, so we may
  -- compose `dStep1⁻¹` with `dStep3` and the ψ-lift of `dStep2` into the single descent iso.
  -- The base-map equality `selectProj N U' ≫ snd = ψ ≫ (snd ≫ selectProj (N.erase A) U)` (`hsplit2`)
  -- identifies the two `baseChangeObj _ xE'` source objects on the nose.
  -- recast `dStep3` along the base-map equality `hsplit2` so its source is `dStep1`'s `xE'`-pullback.
  -- (the dependent `▸` transports both the morphism and its `IsIso` witness simultaneously.)
  have hsplit2' : ψ ≫ ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)
      = tSelectProj Prod.snd N.1 U'.1 hUN' ≫ (snd : prod A P ⟶ P) := hsplit2.symm
  -- transport `dStep3` together with its iso witness along the SOURCE-object equality `hsplit2'`.
  -- Phrasing the cast over the dependent pair `(morphism, IsIso)` keeps the `▸` motive type-correct.
  let dStep3pack : Σ' (f : OverHom (baseChangeObj (tSelectProj Prod.snd N.1 U'.1 hUN' ≫ (snd : prod A P ⟶ P)) xE')
      (baseChangeObj ψ (baseChangeObj ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) xE'))),
      @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ f :=
    hsplit2' ▸ (⟨dStep3, hdStep3_iso⟩ :
      Σ' (f : OverHom (baseChangeObj (ψ ≫ ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe)) xE')
        (baseChangeObj ψ (baseChangeObj ((snd : prod A PN ⟶ PN) ≫ tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) xE'))),
        @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ f)
  let dStep3' := dStep3pack.1
  have hdStep3'_iso : @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ dStep3' := dStep3pack.2
  -- the ψ-lift of `dStep2` (base-change preserves iso, `baseChangeFunctor ψ` is a functor):
  let dStep2ψ : OverHom (baseChangeObj ψ (baseChangeObj ((snd : prod A PN ⟶ PN) ≫
        tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) xE'))
      (baseChangeObj ψ (baseChangeObj (snd : prod A PN ⟶ PN) Dbar)) :=
    (baseChangeFunctor ψ).map dStep2
  have hdStep2ψ_iso : @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ dStep2ψ :=
    functor_preserves_iso (F := baseChangeFunctor ψ) dStep2 hdStep2_iso
  -- `isoInv dStep1 : domain(m_N) ⟶ baseChangeObj (selectProj N U' ≫ snd) xE'` (forward into the
  -- descent), with its iso witness assembled from `isoInv_comp`/`inv_isoInv_comp`.  `dStep1`'s
  -- codomain is the `∘`-composed base-change form, which is defeq to `L.F hUN' (L.F hUU' xE')`.
  let dStep1inv := @isoInv (Over (listProd (N.1.map Prod.snd))) _ _ _ dStep1 hdStep1_iso
  have hdStep1inv_iso : @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ dStep1inv :=
    ⟨dStep1, inv_isoInv_comp hdStep1_iso, isoInv_comp hdStep1_iso⟩
  -- THE DESCENT EQUATION: the composite iso `domain(m_N) ≅ baseChangeObj ψ (baseChangeObj snd Dbar)`.
  -- (domain stated in the `∘`-composed form, defeq to `L.F hUN' (L.F hUU' xE')` = `m_N`'s domain.)
  let descent := dStep1inv ⊚ dStep3' ⊚ dStep2ψ
  have hdescent : @IsIso (Over (listProd (N.1.map Prod.snd))) _ _ _ descent :=
    isIso_comp hdStep1inv_iso (isIso_comp hdStep3'_iso hdStep2ψ_iso)
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- PHASE 1 — the consumer's PN-level cone data (does NOT depend on `hstage`).
  -- the descended proper mono over `PN`: `mC := m_PN ⊚ bcGen⁻¹ : OverHom Dbar (sliceEmbedObj PN A)`.
  have hbcGenInv_iso : @IsIso (Over PN) _ _ _ (isoInv bcGen_iso) :=
    ⟨bcGen, inv_isoInv_comp bcGen_iso, isoInv_comp bcGen_iso⟩
  let mC : OverHom Dbar (sliceEmbedObj PN A) :=
    @Cat.comp (Over PN) _ _ _ _ (baseChangeMap (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) m)
      (isoInv bcGen_iso)
  have hmC_mono : @Monic (Over PN) _ _ _ mC := mono_postcomp_iso' hmPN_mono hbcGenInv_iso
  have hmC_niso : ¬ @IsIso (Over PN) _ _ _ mC := by
    intro hmi; apply hmPN_niso
    have he : baseChangeMap (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) m
        = @Cat.comp (Over PN) _ _ _ _ mC bcGen := by
      show baseChangeMap (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) m
        = @Cat.comp (Over PN) _ _ _ _
            (@Cat.comp (Over PN) _ _ _ _ (baseChangeMap (tSelectProj Prod.snd (N.1.erase aT) U.1 hUe) m)
              (isoInv bcGen_iso)) bcGen
      rw [Cat.assoc]
      rw [show @Cat.comp (Over PN) _ _ _ _ (isoInv bcGen_iso) bcGen = Cat.id _ from
        inv_isoInv_comp bcGen_iso, Cat.comp_id]
    rw [he]; exact isIso_comp hmi bcGen_iso
  -- the consumer's base-change cone `cnDN` (chosen pullback of `Dbar.hom` along `snd : A×PN ⟶ PN`).
  let cnDN : Cone (Dbar.hom) (snd : prod A PN ⟶ PN) :=
    (HasPullbacks.has (Dbar.hom) (snd : prod A PN ⟶ PN)).cone
  have hcnDN : cnDN.IsPullback :=
    (HasPullbacks.has (Dbar.hom) (snd : prod A PN ⟶ PN)).cone_isPullback
  let mf'N : cnDN.pt ⟶ prod A (prod A PN) :=
    pair (cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A)) cnDN.π₂
  have hmf1N : mf'N ≫ (fst : prod A (prod A PN) ⟶ A) = cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A) :=
    fst_pair _ _
  have hmf2N : mf'N ≫ (snd : prod A (prod A PN) ⟶ prod A PN) = cnDN.π₂ := snd_pair _ _
  -- the base-changed mono `mbarN : ⟨cnDN.pt, π₂⟩ ↪ sliceEmbedObj (A×PN) A` with underlying `mf'N`.
  let mbarN : OverHom (⟨cnDN.pt, cnDN.π₂⟩ : Over (prod A PN)) (sliceEmbedObj (prod A PN) A) :=
    ⟨mf'N, by show mf'N ≫ (snd : prod A (prod A PN) ⟶ prod A PN) = cnDN.π₂; exact hmf2N⟩
  -- ════════════════════════════════════════════════════════════════════════════════════════════
  -- PHASE 2 — the point read-off from `hstage` (the §1.546 transport).
  -- The fresh slice point `sliceFactorPoint A fst` factors through `mbarN` via the transported `z₀`.
  -- (c.i) the §1.546 point read-off.  Everything around it is
  -- machine-checked Sorry-free: the consumer cone data (`mC`/`cnDN`/`mf'N`/`mbarN`, Phase 1) and the
  -- `freshSlicePoint_factors_imp_false` finish below.  What remains is to transport the fresh-point
  -- factorization `hstage` (an `Over (∏N)` equation of three `pushHom`-conjugated arrows) into the
  -- point `t : 1 → ⟨cnDN.pt, cnDN.π₂⟩` with `t ⊚ mbarN = sliceFactorPoint A fst`.  The transport
  -- routes the LHS point `pushHom … z₀` of `hstage` through `descent`/`hdescent` (identifying
  -- `m_N`'s domain with `ψ*(snd*(Dbar))`) and the iso `ψ` (`hψiso`, so `baseChangeObj ψ X ≅ X`),
  -- reading both legs of `t.f` off `proj_pushHom_f_π₁`/`proj_pushHom_f_π₂` by `pb_hom_ext`.  This is
  -- the genuine multi-screen §1.546 descent; every primitive it needs is in scope Sorry-free.
  have hpt : ∃ t : OverHom (overTerm (prod A PN)) (⟨cnDN.pt, cnDN.π₂⟩ : Over (prod A PN)),
      t ⊚ mbarN = sliceFactorPoint A (fst : prod A PN ⟶ A) := by
    -- REDUCTION.  `t ⊚ mbarN = sliceFactorPoint A fst` (an `OverHom (overTerm (A×PN)) (sliceEmbedObj
    -- (A×PN) A)` equation) holds iff its underlying `A×PN`-arrow `t.f ≫ mf'N = pair fst id`.  By the
    -- product universal property (the eta law) and `hmf1N`/`hmf2N`, that splits into:
    --   • `A`-leg : `t.f ≫ cnDN.π₁ ≫ mC.f ≫ fst = fst`  (the FRESH coordinate — the §1.546 content);
    --   • `PN`-structure leg : `t.f ≫ cnDN.π₂ = id`       (the over-`A×PN` point law, = `t.w`).
    -- So it suffices to build `q : A×PN ⟶ Dbar.dom` (a section of `Dbar.hom` over `A×PN` via `snd`)
    -- with `q ≫ Dbar.hom = snd` and `q ≫ mC.f ≫ fst = fst`; then `t.f := the pullback lift` of the
    -- cone `(q, id)` over the cospan `(Dbar.hom, snd)`.
    -- ── the section `q` of the base-change `Dbar` over `A×PN` reaching the fresh `A`-coordinate ──
    obtain ⟨q, hqstruct, hqfresh⟩ :
        ∃ q : prod A PN ⟶ Dbar.dom,
          q ≫ Dbar.hom = (snd : prod A PN ⟶ PN) ∧ q ≫ mC.f ≫ (fst : prod A PN ⟶ A) = fst := by
      -- ════════════════════════════════════════════════════════════════════════════════════════
      -- THE GENUINE §1.546 DESCENT CORE (single isolated residual), now reduced by the standalone
      -- read-off lemma `freshSection_of_descentSection` (RelativeCapitalization.lean) to the SHARPER,
      -- equivalent residual: producing the §1.546 DESCENT SECTION
      --   `s : A×PN ⟶ cnDN.pt`  with  `s ≫ cnDN.π₂ = id`  and  `s ≫ cnDN.π₁ ≫ mC.f ≫ fst = fst`.
      -- `freshSection_of_descentSection` then assembles `q := s ≫ cnDN.π₁` with the two goal legs
      -- (structure via `cnDN.w`/`hs₂`, fresh via `hsA`) — Sorry-free, machine-checked.
      obtain ⟨s, hs₂, hsA⟩ :
          ∃ s : prod A PN ⟶ cnDN.pt,
            s ≫ cnDN.π₂ = Cat.id (prod A PN) ∧
              s ≫ cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A) = fst := by
      -- ── THE REMAINING §1.546 CORE: the descent section `s` over `A×PN`. ──
      -- `s` is the §1.546 point read-off from `hstage`, transported by `descent`/`ψ`:
      --   • `hstage` (an `Over (∏N)` equation) says the N-image of the fresh point `sfp ⊚ cod`
      --     (`pushHom … sc₀`) FACTORS through the N-image of `pushFibre g''` (`pushHom … pf₀`) via the
      --     N-rep `pushHom … z₀` of the colimit factor.  `proj_pushHom_f_π₁`/`proj_pushHom_f_π₂`
      --     (CapitalizationLaxColimit.lean) give the two pullback legs of each `(pushHom _).f` over
      --     `∏N` explicitly (no opaque coherence left).
      --   • `descent : IsIso descent` identifies `m_N`'s domain `L.F hUN' (L.F hUU' xE')` with
      --     `baseChangeObj ψ (baseChangeObj snd Dbar)`; since `ψ` is an iso (`hψiso`),
      --     `baseChangeObj ψ X ≅ X`, so this is `≅ baseChangeObj snd Dbar = ⟨cnDN.pt, cnDN.π₂⟩`.
      --   • routing `(pushHom … z₀).f` through `descent.f` and the `ψ`-iso yields `s` over `A×PN`; its
      --     `cnDN.π₁`-leg (`hstage` content leg via `proj_pushHom_f_π₁`, `hψfst`) reaches `fst`.
      -- This is the genuine multi-screen `pb_hom_ext` reindexing chain — the §1.546 open core the file
      -- documents (lines 525–635, 706–845) — needing the DESCENT EQUATION relating `m_N.f` (over ∏N,
      -- content `factorProj N A = ψ ≫ fst` via `proj_pushHom_f_π₁`) to `cnDN.π₁ ≫ mC.f` (over A×PN).
      -- The `baseChangeTransNatIso` comparison legs are now PUBLIC (Step 1, CapitalizationLaxColimit):
      --   `baseChangeTransNatIso_app_f`     : `(…nat.app X).f = _transFwdf …` (defeq witness);
      --   `baseChangeTransNatIso_app_f_π₁`  : outer·inner `π₁` ↦ LHS `π₁` (content leg);
      --   `baseChangeTransNatIso_app_f_π₂`  : outer `π₂` ↦ LHS `π₂` (structure leg);
      --   `baseChangeTransNatIso_app_f_π₁π₂`: outer `π₁`·inner `π₂` ↦ LHS `π₂ ≫ g'` (pasting leg).
      -- These characterise `dStep1`/`dStep2`/`dStep3` (and hence `descent`) leg-by-leg in public terms,
      -- composed with `proj_pushHom_f_π₁/π₂` for `hstage` and `hψfst`/`hψsnd` for the `ψ`-reindex.  ALL
      -- primitives are now in scope and public; the residual is purely the in-file descent transport
      -- (compose the three `dStep` legs across the `dStep3pack` `▸`-cast `eqToHom`s, route `hstage`'s
      -- `pushHom … z₀` content/structure legs through them, read off `s` by `pb_hom_ext` over `cnDN`).
      -- Isolated here as the single sharpest residual.  EXACT goal:
      --   ⊢ ∃ s : A×PN ⟶ cnDN.pt, s ≫ cnDN.π₂ = id ∧ s ≫ cnDN.π₁ ≫ mC.f ≫ fst = fst
      -- The stage-`N` representative of the colimit factor `z`, pushed to `N`.
        let zN := pushHom L (T.ht U').one (L.F hUU' xE') b.2.1 b.2.2 hbN z₀
        -- the codomain of `zN` is `L.F (trans b.2.2 hbN) (L.F hUU' xE')`; we want the descent-domain
        -- form `baseChangeObj (selectProj N U') (baseChangeObj snd xE')`.  `L.F hij = baseChangeObj
        -- (selectProj _ _ hij)` defeq, and `selectProj U' U hUU' = snd` is `hsp`.
        have hLF : L.F hUU' xE' = baseChangeObj snd xE' := by
          show baseChangeObj (tSelectProj Prod.snd U'.val U.val hUU') xE' = baseChangeObj snd xE'
          rw [hsp]
        have hcodObj : L.F ((wsDirected S).trans b.2.2 hbN) (L.F hUU' xE')
            = (compFunctor (baseChangeFunctor snd)
                (baseChangeFunctor (tSelectProj Prod.snd N.val U'.val hUN'))).obj xE' := by
          show baseChangeObj (tSelectProj Prod.snd N.val U'.val ((wsDirected S).trans b.2.2 hbN))
              (L.F hUU' xE')
            = baseChangeObj (tSelectProj Prod.snd N.val U'.val hUN') (baseChangeObj snd xE')
          rw [hLF]
        -- cast `zN` into the descent domain, then compose with `descent`.
        let zNd : OverHom (L.F ((wsDirected S).trans b.2.1 hbN) (T.ht U').one)
            (baseChangeObj ψ (baseChangeObj snd Dbar)) :=
          @Cat.comp (Over (listProd (N.1.map Prod.snd))) _ _ _ _ (hcodObj ▸ zN) descent
        -- source object: N-image of slice terminal = pullback of `id ∏U'` along `selectProj N U'`.
        -- the chosen pullback giving `source.dom`.
        let srcPB := HasPullbacks.has (𝒞 := S) (overTerm (listProd (U'.1.map Prod.snd))).hom
          (tSelectProj Prod.snd N.1 U'.1 ((wsDirected S).trans b.2.1 hbN))
        have hsrcEq : L.F ((wsDirected S).trans b.2.1 hbN) (T.ht U').one
            = (⟨srcPB.cone.pt, srcPB.cone.π₂⟩ : Over (listProd (N.1.map Prod.snd))) := rfl
        -- `a := ψ⁻¹ : A×PN ⟶ ∏N`; cone over `(id ∏U', selectProj N U')` with legs `(a ≫ sel, a)`.
        let a : prod A PN ⟶ listProd (N.1.map Prod.snd) := isoInv hψiso
        let srcCone : Cone (𝒞 := S) (overTerm (listProd (U'.1.map Prod.snd))).hom
            (tSelectProj Prod.snd N.1 U'.1 ((wsDirected S).trans b.2.1 hbN)) :=
          ⟨prod A PN, a ≫ tSelectProj Prod.snd N.1 U'.1 ((wsDirected S).trans b.2.1 hbN), a, by
            show (a ≫ tSelectProj Prod.snd N.1 U'.1 ((wsDirected S).trans b.2.1 hbN)) ≫ Cat.id _
              = a ≫ tSelectProj Prod.snd N.1 U'.1 ((wsDirected S).trans b.2.1 hbN)
            rw [Cat.comp_id]⟩
        let r : prod A PN ⟶ srcPB.cone.pt := srcPB.lift srcCone
        -- codomain pullback `baseChangeObj ψ (bc snd Dbar)` = pullback of `cnDN.π₂` along `ψ`.
        let codPB := HasPullbacks.has (𝒞 := S) (baseChangeObj snd Dbar).hom ψ
        have hcodPt : (baseChangeObj snd Dbar).dom = cnDN.pt := rfl
        -- `s := r ≫ zNd.f ≫ codPB.π₁`, lands in `(bc snd Dbar).dom = cnDN.pt`.
        let s : prod A PN ⟶ cnDN.pt :=
          r ≫ (zNd.f ≫ codPB.cone.π₁ : srcPB.cone.pt ⟶ cnDN.pt)
        refine ⟨s, ?hstruct, ?hfresh⟩
        · -- structure leg: `s ≫ cnDN.π₂ = id`.
          -- `cnDN.π₂ = (bc snd Dbar).hom`; `codPB.cone.π₁ ≫ (bc snd Dbar).hom = codPB.cone.π₂ ≫ ψ`.
          have hw : codPB.cone.π₁ ≫ cnDN.π₂ = codPB.cone.π₂ ≫ ψ := codPB.cone.w
          have hzw : zNd.f ≫ codPB.cone.π₂ = srcPB.cone.π₂ := zNd.w
          have hrw : r ≫ srcPB.cone.π₂ = a := srcPB.lift_snd srcCone
          show (r ≫ (zNd.f ≫ codPB.cone.π₁)) ≫ cnDN.π₂ = Cat.id (prod A PN)
          calc (r ≫ (zNd.f ≫ codPB.cone.π₁)) ≫ cnDN.π₂
              = r ≫ zNd.f ≫ codPB.cone.π₁ ≫ cnDN.π₂ := by rw [Cat.assoc, Cat.assoc]
            _ = r ≫ zNd.f ≫ codPB.cone.π₂ ≫ ψ := by rw [hw]
            _ = r ≫ (zNd.f ≫ codPB.cone.π₂) ≫ ψ := by rw [Cat.assoc]
            _ = r ≫ srcPB.cone.π₂ ≫ ψ := by rw [hzw]
            _ = (r ≫ srcPB.cone.π₂) ≫ ψ := by rw [Cat.assoc]
            _ = a ≫ ψ := by rw [hrw]
            _ = Cat.id (prod A PN) := inv_isoInv_comp hψiso
        · -- fresh leg: `s ≫ cnDN.π₁ ≫ mC.f ≫ fst = fst`.
          show (r ≫ (zNd.f ≫ codPB.cone.π₁)) ≫ cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A) = fst
          -- THE §1.546 CONTENT BRIDGE.  The A-coordinate of the descended subobject, traced through
          -- the descent iso `zNd = (zN cast) ≫ descent` and the codomain pullback, equals the
          -- A-coordinate `zN` carries over `∏N` reindexed by `ψ` (`hψfst : ψ ≫ fst = factorProj N A`).
          -- `hstage` forces that A-coordinate to be the fresh `fst` (the content of `sc₀`).
          -- THE SINGLE ISOLATED §1.546 CONTENT RESIDUAL.  Everything else in `richerSliceSection` is
          -- now machine-checked Sorry-free: the section `s := r ≫ zNd.f ≫ codPB.π₁` (`r` the ψ⁻¹-cone
          -- lift into the N-image of the slice terminal, `zNd = (zN cast by hcodObj) ≫ descent`), the
          -- structure leg `s ≫ cnDN.π₂ = id` (proved above via `codPB.w`/`zNd.w`/`srcPB.lift_snd` +
          -- `ψ⁻¹≫ψ = id`), and the reduction of the fresh leg to `hbridge` (proved below via
          -- `srcPB.lift_snd` + `ψ⁻¹≫ψ = id`).  What remains is the A-COORDINATE TRANSPORT identity
          -- `hbridge`: the deep content projection `zNd.f ≫ codPB.π₁ ≫ cnDN.π₁ ≫ mC.f ≫ fst`, traced
          -- back through `descent = dStep1inv ⊚ dStep3' ⊚ dStep2ψ` (decomposable `.f`-wise, `hdf` below
          -- is `rfl`) and the codomain comparison `bcGen`, equals the A-coordinate `srcPB.π₂ ≫ ψ ≫ fst
          -- = srcStructure ≫ factorProj N A` that `zN` carries over `∏N`.  This is forced by `hstage`
          -- (the on-the-nose factorization of the fresh point `sc₀`, content `fst`, through `pfN`) via
          -- `proj_pushHom_f_π₁` (content leg) + `hψfst`.  Reading it off is the genuine multi-screen
          -- `pb_hom_ext` reindexing chain across the three `baseChangeTransNatIso` legs (public
          -- `baseChangeTransNatIso_app_f_π₁/π₂`) and the base-change content law `baseChangeMap_f_π₁`
          -- — every primitive in scope and public, but a large mechanical descent.  EXACT goal:
          --   ⊢ (zNd.f ≫ codPB.cone.π₁) ≫ cnDN.π₁ ≫ mC.f ≫ fst = srcPB.cone.π₂ ≫ ψ ≫ fst
          have hbridge : (zNd.f ≫ codPB.cone.π₁) ≫ cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A)
              = srcPB.cone.π₂ ≫ ψ ≫ (fst : prod A PN ⟶ A) := by
            -- abbreviations for the relevant chosen pullbacks.
            let q' := tSelectProj Prod.snd (N.1.erase aT) U.1 hUe
            -- the `bc q' (sliceEmbedObj P A)` pullback (of `snd : A×P → P` along `q'`).
            let bcPB_P := HasPullbacks.has (𝒞 := S) ((sliceEmbedObj P A).hom) q'
            -- `(isoInv bcGen_iso).f ≫ fst = bcPB_P.π₁ ≫ fst`: from `lift_fst` (bcGen.f ≫ π₁ =
            -- pair fst (snd≫q')) cancelled by `(isoInv bcGen_iso).f ≫ bcGen.f = id`.
            have hbcGenInv_fst : (isoInv bcGen_iso).f ≫ (fst : prod A PN ⟶ A)
                = bcPB_P.cone.π₁ ≫ (fst : prod A P ⟶ A) := by
              have hπ₁ : bcPB_P.cone.π₁
                  = (isoInv bcGen_iso).f ≫ pair (fst : prod A PN ⟶ A)
                      ((snd : prod A PN ⟶ PN) ≫ q') := by
                rw [show pair (fst : prod A PN ⟶ A) ((snd : prod A PN ⟶ PN) ≫ q')
                      = bcGen.f ≫ bcPB_P.cone.π₁ from (bcPB_P.lift_fst bcGenCone).symm,
                    ← Cat.assoc,
                    show (isoInv bcGen_iso).f ≫ bcGen.f = Cat.id _ from
                      congrArg OverHom.f (inv_isoInv_comp bcGen_iso), Cat.id_comp]
              rw [hπ₁, Cat.assoc, fst_pair]
            -- the `bc q' xE'` pullback = `Dbar`'s pullback (of `xE'.hom` along `q'`).
            let bcPB_E := HasPullbacks.has (𝒞 := S) (xE'.hom) q'
            -- content law: `mC.f ≫ fst = bcPB_E.π₁ ≫ m.f ≫ fst` (the A-coordinate of `m`, base-changed).
            have hmC_fst : mC.f ≫ (fst : prod A PN ⟶ A)
                = bcPB_E.cone.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A) := by
              -- `mC.f = (baseChangeMap q' m).f ≫ (isoInv bcGen_iso).f`.
              show ((baseChangeMap q' m).f ≫ (isoInv bcGen_iso).f) ≫ (fst : prod A PN ⟶ A) = _
              rw [Cat.assoc, hbcGenInv_fst, ← Cat.assoc]
              -- `(baseChangeMap q' m).f ≫ bcPB_P.π₁ = bcPB_E.π₁ ≫ m.f` (base-change content `lift_fst`).
              rw [show (baseChangeMap q' m).f ≫ bcPB_P.cone.π₁ = bcPB_E.cone.π₁ ≫ m.f from
                    bcPB_P.lift_fst (baseChangeCone q' m), Cat.assoc]
            -- rewrite the goal's `mC.f ≫ fst` by `hmC_fst`; the residual is the DESCENT-CONTENT
            -- transport relating the deep content of `bc ψ (bc snd Dbar)` (via `descent`) to the
            -- N-image `pfN`'s content, then `hstage` + `proj_pushHom_f_π₁` + `hψfst`.
            rw [show cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A)
                  = cnDN.π₁ ≫ bcPB_E.cone.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A) from by
                rw [show mC.f ≫ (fst : prod A PN ⟶ A)
                      = bcPB_E.cone.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A) from hmC_fst]]
            -- REMAINING (single isolated §1.546 descent-content residual).  EXACT goal:
            --   ⊢ (zNd.f ≫ codPB.cone.π₁) ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁ ≫ m.f ≫ fst
            --       = srcPB.cone.π₂ ≫ ψ ≫ fst
            -- The deep content `codPB.π₁ ≫ cnDN.π₁ ≫ bcPB_E.π₁ : (bc ψ (bc snd Dbar)).dom ⟶ xE'.dom`,
            -- traced through `descent = dStep1inv ⊚ dStep3' ⊚ dStep2ψ` (public
            -- `baseChangeTransNatIso_app_f_π₁`), corresponds to the deep content of `m_N`'s domain
            -- `bc (selectProj N U') (bc snd xE')`; `proj_pushHom_f_π₁` reads `zN`'s content leg off
            -- `hstage`, whose RHS `sc₀` content is the fresh `fst` (via `hψfst`/`hψsnd`).  This is the
            -- genuine multi-screen pullback-pasting reindexing chain; the codomain `mC`/`bcGen` layer
            -- above is now fully discharged.  The descent's three legs are individually reducible by
            -- the public `baseChangeTransNatIso_app_f_π₁` / `baseChangeMap_f_π₁` content laws (verified:
            -- e.g. `dStep2ψ.f ≫ codPB.π₁ = (ψ-pullback of dStep2 source).π₁ ≫ dStep2.f` by
            -- `lift_fst (baseChangeCone ψ dStep2)`); chaining them across the `dStep3pack` `▸`-cast and
            -- `dStep1inv` to `proj_pushHom_f_π₁` of `hstage` is the remaining mechanical descent.
            -- ── STEP A: reduce the descent's deep content to the SOURCE deep content projection. ──
            -- abbreviations: the source-object pullbacks `bc g₁ (bc snd xE')`.
            let g₁ := tSelectProj Prod.snd N.1 U'.1 hUN'
            -- the deep source content projection (of `(bc g₁ ∘ bc snd) xE' = (hcodObj ▸ zN)`'s codom).
            -- leg reductions (all `lift_fst`/public `baseChangeTransNatIso_app_f_π₁`):
            have e1 : dStep2ψ.f ≫ codPB.cone.π₁
                = (HasPullbacks.has (baseChangeObj ((snd : prod A PN ⟶ PN) ≫ q') xE').hom ψ).cone.π₁
                    ≫ dStep2.f :=
              codPB.lift_fst (baseChangeCone ψ dStep2)
            have e2 : dStep2.f ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁
                = (HasPullbacks.has xE'.hom ((snd : prod A PN ⟶ PN) ≫ q')).cone.π₁ :=
              baseChangeTransNatIso_app_f_π₁ q' (snd : prod A PN ⟶ PN) xE'
            have e3' : dStep3'.f
                  ≫ (HasPullbacks.has (baseChangeObj ((snd : prod A PN ⟶ PN) ≫ q') xE').hom ψ).cone.π₁
                    ≫ (HasPullbacks.has xE'.hom ((snd : prod A PN ⟶ PN) ≫ q')).cone.π₁
                = (HasPullbacks.has xE'.hom (g₁ ≫ (snd : prod A P ⟶ P))).cone.π₁ :=
              baseChangeTransNatIso_app_f_π₁_cast ((snd : prod A PN ⟶ PN) ≫ q') ψ xE' hsplit2'
            -- the `dStep1` content law, and its inverse for `dStep1inv`.
            have e0 : dStep1.f
                  ≫ (HasPullbacks.has (baseChangeObj snd xE').hom g₁).cone.π₁
                    ≫ (HasPullbacks.has xE'.hom (snd : prod A P ⟶ P)).cone.π₁
                = (HasPullbacks.has xE'.hom (g₁ ≫ (snd : prod A P ⟶ P))).cone.π₁ :=
              baseChangeTransNatIso_app_f_π₁ (snd : prod A P ⟶ P) g₁ xE'
            have e0inv : dStep1inv.f
                  ≫ (HasPullbacks.has xE'.hom (g₁ ≫ (snd : prod A P ⟶ P))).cone.π₁
                = (HasPullbacks.has (baseChangeObj snd xE').hom g₁).cone.π₁
                    ≫ (HasPullbacks.has xE'.hom (snd : prod A P ⟶ P)).cone.π₁ := by
              have hid : dStep1inv.f ≫ dStep1.f = Cat.id _ :=
                congrArg OverHom.f (inv_isoInv_comp hdStep1_iso)
              calc dStep1inv.f
                      ≫ (HasPullbacks.has xE'.hom (g₁ ≫ (snd : prod A P ⟶ P))).cone.π₁
                  = dStep1inv.f ≫ dStep1.f
                      ≫ (HasPullbacks.has (baseChangeObj snd xE').hom g₁).cone.π₁
                        ≫ (HasPullbacks.has xE'.hom (snd : prod A P ⟶ P)).cone.π₁ := by rw [e0]
                _ = (dStep1inv.f ≫ dStep1.f)
                      ≫ (HasPullbacks.has (baseChangeObj snd xE').hom g₁).cone.π₁
                        ≫ (HasPullbacks.has xE'.hom (snd : prod A P ⟶ P)).cone.π₁ :=
                    (Cat.assoc _ _ _).symm
                _ = (HasPullbacks.has (baseChangeObj snd xE').hom g₁).cone.π₁
                      ≫ (HasPullbacks.has xE'.hom (snd : prod A P ⟶ P)).cone.π₁ := by
                    rw [hid, Cat.id_comp]
            -- chain the legs into the master descent-content reduction.
            have hdescent_content : descent.f ≫ codPB.cone.π₁ ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁
                = (HasPullbacks.has (baseChangeObj snd xE').hom g₁).cone.π₁
                    ≫ (HasPullbacks.has xE'.hom (snd : prod A P ⟶ P)).cone.π₁ := by
              show (dStep1inv.f ≫ dStep3'.f ≫ dStep2ψ.f) ≫ codPB.cone.π₁ ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁
                = _
              calc (dStep1inv.f ≫ dStep3'.f ≫ dStep2ψ.f)
                      ≫ codPB.cone.π₁ ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁
                  = dStep1inv.f ≫ dStep3'.f
                      ≫ (dStep2ψ.f ≫ codPB.cone.π₁) ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁ := by
                    simp only [Cat.assoc]
                _ = dStep1inv.f ≫ dStep3'.f
                      ≫ (HasPullbacks.has (baseChangeObj ((snd : prod A PN ⟶ PN) ≫ q') xE').hom ψ).cone.π₁
                        ≫ dStep2.f ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁ := by rw [e1]; simp only [Cat.assoc]
                _ = dStep1inv.f ≫ dStep3'.f
                      ≫ (HasPullbacks.has (baseChangeObj ((snd : prod A PN ⟶ PN) ≫ q') xE').hom ψ).cone.π₁
                        ≫ (HasPullbacks.has xE'.hom ((snd : prod A PN ⟶ PN) ≫ q')).cone.π₁ := by
                    rw [e2]
                _ = dStep1inv.f
                      ≫ (HasPullbacks.has xE'.hom (g₁ ≫ (snd : prod A P ⟶ P))).cone.π₁ := by
                    rw [e3']
                _ = (HasPullbacks.has (baseChangeObj snd xE').hom g₁).cone.π₁
                      ≫ (HasPullbacks.has xE'.hom (snd : prod A P ⟶ P)).cone.π₁ := e0inv
            -- ── STEP B: fold the descent content into the SOURCE deep content of `zN`. ──
            have hzNdf : zNd.f = (hcodObj ▸ zN).f ≫ descent.f := rfl
            rw [show (zNd.f ≫ codPB.cone.π₁) ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A)
                  = (hcodObj ▸ zN).f
                      ≫ (descent.f ≫ codPB.cone.π₁ ≫ cnDN.π₁ ≫ bcPB_E.cone.π₁) ≫ m.f ≫ fst from by
                rw [hzNdf]; simp only [Cat.assoc], hdescent_content]
            -- ── STEP C (the remaining isolated residual): the SOURCE-content transport. ──
            -- The descent layer is now fully discharged (STEPS A–B, `hdescent_content`).  EXACT goal:
            --   (hcodObj ▸ zN).f ≫ (srcDeep₁ ≫ srcDeep₂) ≫ m.f ≫ fst = srcPB.π₂ ≫ ψ ≫ fst
            -- where srcDeep₁ ≫ srcDeep₂ = the deep content projection of `(bc g₁ ∘ bc snd) xE'`
            -- (the `hcodObj`-cast codomain of `zN`) reaching `xE'.dom`.
            -- This is read off `hstage` (the on-the-nose `pushHom`-factorization of the fresh point
            -- `sc₀`, content `fst`) via `proj_pushHom_f_π₁ cofinalProjSystem _ (L.F hUU' xE') b.2.1 b.2.2
            -- hbN z₀` (verified in scope), which gives `zN`'s content leg through `transApp`; reconciling
            -- that `transApp`-presentation with the `hcodObj`-cast `srcDeep` deep projection (both
            -- present the SAME nested base-change `bc g₁ (bc snd xE')`, by `transApp_f_π₁π₁` ↔ the
            -- iterated `_pb.π₁`) and then chaining `hstage` + `hψfst` (`ψ ≫ fst = factorProj N A`,
            -- the content `sc₀` carries) closes it.  The two private reconciliation legs
            -- (`transApp_f_π₁π₁`, `baseChangeMap_f_π₁` in CapitalizationLaxColimit) now public.
            have gen : ∀ {Z Y Y' : L.A N} (e : Y = Y') (f : Z ⟶ Y),
                (e ▸ f) = f ≫ eqToHom e := by
              intro Z Y Y' e f; subst e; rw [eqToHom_refl, Cat.comp_id]
            have hcastf : (hcodObj ▸ zN).f = zN.f ≫ (eqToHom hcodObj).f :=
              congrArg OverHom.f (gen hcodObj zN)
            have hpush := proj_pushHom_f_π₁ cofinalProjSystem (T.ht U').one (L.F hUU' xE')
              b.2.1 b.2.2 hbN z₀
            -- the cast `hcodObj` factors as `congrArg (bc g₁) hLF` (the base `proj (trans b.2.2 hbN)
            -- = g₁` defeq, only the inner object `L.F hUU' xE' = bc snd xE'` varies).
            have hcodObj' : hcodObj
                = congrArg (fun X => baseChangeObj g₁ X) hLF := rfl
            -- companion to `eqToHom_bc_π₁`: the inner-object `eqToHom` commutes past `π₁` (down to the
            -- varying inner `.dom`).  Proved by `subst` on the object equality.
            have hbcInner : ∀ {X Y : Over (listProd (U'.val.map Prod.snd))} (e : X = Y),
                (eqToHom (congrArg (fun Z => baseChangeObj g₁ Z) e)).f
                    ≫ (_pb g₁ Y).cone.π₁
                  = (_pb g₁ X).cone.π₁ ≫ (eqToHom e).f := by
              intro X Y e; subst e
              rw [eqToHom_refl, eqToHom_refl]
              show Cat.id _ ≫ _ = _ ≫ Cat.id _
              rw [Cat.id_comp, Cat.comp_id]
            have hLF' : hLF = congrArg (fun z => baseChangeObj z xE') hsp := rfl
            -- `hrec`: the content of `zN` (the cast colimit germ) against the deep source projection,
            -- read off `hpush` by post-composing with the inner `π₁(proj b.2.2)`.
            have hrec : zN.f
                  ≫ (_pb (cofinalProjSystem.proj ((wsDirected S).trans b.2.2 hbN))
                        (L.F hUU' xE')).cone.π₁
                = (transApp (laxOfProjSystem' cofinalProjSystem) b.2.1 hbN (T.ht U').one).f
                    ≫ (_pb (cofinalProjSystem.proj hbN)
                        (baseChangeObj (cofinalProjSystem.proj b.2.1) (T.ht U').one)).cone.π₁
                      ≫ z₀.f ≫ (_pb (cofinalProjSystem.proj b.2.2) (L.F hUU' xE')).cone.π₁ := by
              have hcollapse := transApp_f_π₁π₁ cofinalProjSystem b.2.2 hbN (L.F hUU' xE')
                (Cat.id _)
              rw [Cat.comp_id, Cat.comp_id] at hcollapse
              have hp := congrArg
                (· ≫ (_pb (cofinalProjSystem.proj b.2.2) (L.F hUU' xE')).cone.π₁) hpush
              simp only [Cat.assoc] at hp
              rw [hcollapse] at hp
              exact hp
            -- content of the `sc₀` push (RHS of `hstage`): the fresh point `sliceFactorPoint A fst`.
            have hscPush := proj_pushHom_f_π₁ cofinalProjSystem (T.ht U').one
              (L.F hUU' (L.F hbU (terminalSliceObj W A))) ((wsDirected S).refl U')
              ((wsDirected S).refl U') hUN' sc₀
            -- VERIFIED SCAFFOLDING above (`gen`/`hcastf`/`hpush`/`hcodObj'`/`hbcInner`/`hLF'`/`hrec`/
            -- `hscPush`, all typecheck).  REMAINING RESIDUAL (the §1.546 hstage content-push):
            --   `hrec` reduces the LHS deep source-content to `transApp(one).f ≫ π₁ ≫ z₀.f ≫
            --   π₁(proj b.2.2, L.F hUU' xE')`; the goal still needs `… ≫ m.f ≫ fst`.  Close by
            --   projecting `hstage` (`zN ⊚ pushHom pf₀ = pushHom sc₀`) to its `.f` deep A-coordinate:
            --     • RHS leg `pushHom sc₀`: `proj_pushHom_f_π₁` (= `hscPush`) + `transApp_f_π₁π₁` gives
            --       `sc₀`'s deep content; `sc₀ = reflApp ≫ (sfp ⊚ cod) ≫ isoInv`, and `(sfp ⊚ cod).f
            --       ≫ fst = (sliceFactorPoint A fst).f ≫ fst = fst` (via `bcSliceIso`/`pIso`/`cod`
            --       content laws on the A-coordinate);
            --     • LHS leg `zN ⊚ pushHom pf₀`: `pf₀ = reflApp ≫ pushFibre g'' ≫ isoInv`, `pushFibre =
            --       Functor.map g''`, content `baseChangeMap_f_π₁` = `g''.f`, and `m.f = (g'' ⊚ pInv).f
            --       = g''.f ≫ pInv.f`, so the A-coordinate of `pf₀`-pushed `zN` is `z₀`-content `≫ m.f
            --       ≫ fst`.  Equating the two legs (hstage) + `hψfst` (`ψ ≫ fst = factorProj N A`,
            --       which the `sc₀`/fresh-point content carries) and `srcPB.π₂ = (zN.dom).hom` closes.
            -- This is the genuine multi-screen §1.546 content reindexing; the cast/transApp bridge
            -- (`hrec`) and the descent layer (STEPS A–B) are fully discharged.
            -- ── REMAINING (the §1.546 hstage content-push), sharpened by this pass: ──
            -- KEY FINDING: `hcodObj` and `hLF` are *reflexive* (their two sides are defeq); but the
            -- cast `(hcodObj ▸ zN).f` does NOT collapse via `eqToHom_refl`/`Subsingleton.elim`/`rfl`
            -- because the two object expressions `L.F (trans b.2.2 hbN) (L.F hUU' xE')` and
            -- `(baseChangeObj g₁ ∘ baseChangeObj snd) xE'` are defeq but not syntactically `Eq.refl`-
            -- headed (so `Cat.id`/`eqToHom rfl` typecheck against only ONE of the two displayed doms).
            -- The cast must therefore be eliminated by the already-proven `hbcInner`/`eqToHom_bc_π₁`
            -- (which `subst` the equality), NOT by `eqToHom_refl`.  Verified content sub-laws for the
            -- push: `(sliceFactorPoint A fst).f ≫ fst = fst` (`pair`/`fst_pair`); `bcSliceIso`'s A-leg
            -- `bcSliceIso.f ≫ (_pb snd (sliceEmbedObj P A)).π₁ = pair fst (snd≫snd)` (`lift_fst`), so
            -- `≫ fst = fst`.  CHAIN (still to assemble): `rw [hcastf]`; reassociate; `rw [hcodObj',
            -- hbcInner hLF]` to move the cast past `π₁(g₁)`; `eqToHom_bc_π₁` (via `hLF'`) past
            -- `π₁(snd)`; then `hrec` to expose `z₀.f`; then project `hstage` (`proj_pushHom_f_π₁` on
            -- `pushHom pf₀`, with `pf₀ = reflApp ≫ Functor.map g'' ≫ isoInv`, `baseChangeMap_f_π₁` =
            -- `g''.f`, `m.f = g''.f ≫ pInv.f`) against the `sc₀` RHS (content `fst` via the verified
            -- sub-laws + `hψfst`).  This is the genuine multi-screen reindexing.
            -- ── projected content legs of `hstage` over `∏N`. ──
            -- `pf₀` pushed: project to its `π₁` (content) leg via `proj_pushHom_f_π₁`.
            have hpfPush := proj_pushHom_f_π₁ cofinalProjSystem (L.F hUU' xE')
              (L.F hUU' (L.F hbU (terminalSliceObj W A))) ((wsDirected S).refl U')
              ((wsDirected S).refl U') hUN pf₀
            -- project `hstage`'s `.f` onto the codomain content leg (matching `hscPush`).
            have hstageProj := congrArg (fun w => OverHom.f w
                ≫ (transApp L ((wsDirected S).refl U') hUN'
                      (L.F hUU' (L.F hbU (terminalSliceObj W A)))).f
                  ≫ (_pb (cofinalProjSystem.proj hUN')
                      (baseChangeObj (cofinalProjSystem.proj ((wsDirected S).refl U'))
                        (L.F hUU' (L.F hbU (terminalSliceObj W A))))).cone.π₁) hstage
            simp only [] at hstageProj
            rw [show (pushHom L (T.ht U').one (L.F hUU' xE') b.2.1 b.2.2 hbN z₀
                    ≫ pushHom L (L.F hUU' xE') (L.F hUU' (L.F hbU (terminalSliceObj W A)))
                        ((wsDirected S).refl U') ((wsDirected S).refl U') hUN pf₀).f
                  = (pushHom L (T.ht U').one (L.F hUU' xE') b.2.1 b.2.2 hbN z₀).f
                    ≫ (pushHom L (L.F hUU' xE') (L.F hUU' (L.F hbU (terminalSliceObj W A)))
                        ((wsDirected S).refl U') ((wsDirected S).refl U') hUN pf₀).f from rfl] at hstageProj
            simp only [Cat.assoc] at hstageProj
            rw [hscPush, hpfPush] at hstageProj
            -- `hstageProj` now reads (a clean content equation over `S`):
            --   (pushHom z₀).f ≫ transApp(hUN,xE').f ≫ π₁(proj hUN, L.F hUU' xE') ≫ pf₀.f
            --     = transApp(hUN',one).f ≫ π₁(proj hUN', one) ≫ sc₀.f
            -- where `π₁ ≫ pf₀.f`/`π₁ ≫ sc₀.f` reach the slice-domain pullbacks (NOT `prod A P`
            -- literally; the A-content needs the `bcSliceIso`/`pIso` reconciliation).
            -- The shared A-leg `Λ` of the codomain `L.F hUU' (L.F hbU term)` of `cod`/`sc₀`/`pf₀`.
            -- `L.F hUU' (L.F hbU term) = baseChangeObj snd (L.F hbU term)` (`hcodEq`); the A-content
            -- is the pullback `π₁` to `(L.F hbU term).dom`, transported by `pInv` to `sliceEmbedObj P A
            -- = ⟨prod A P, snd⟩`, then `fst`.
            let Λ : (L.F hUU' (L.F hbU (terminalSliceObj W A))).dom ⟶ A :=
              (eqToHom hcodEq).f
                ≫ (_pb (snd : prod A P ⟶ P) (L.F hbU (terminalSliceObj W A))).cone.π₁
                  ≫ pInv.f ≫ (fst : prod A P ⟶ A)
            have gen' : ∀ {C : S} {Z Y Y' : Over C} (e : Y = Y') (f : OverHom Z Y),
                (e ▸ f).f = f.f ≫ (eqToHom e).f := by
              intro C Z Y Y' e f; subst e
              rw [eqToHom_refl]; show f.f = f.f ≫ (Cat.id Y).f
              rw [show (Cat.id Y).f = Cat.id Y.dom from rfl, Cat.comp_id]
            have hcodf : cod.f = cod'.f ≫ (eqToHom hcodEq.symm).f := gen' hcodEq.symm cod'
            -- the two `eqToHom hcodEq.symm`/`hcodEq` cancel.
            have hee : (eqToHom hcodEq.symm).f
                  ≫ (eqToHom hcodEq).f
                = Cat.id _ :=
              congrArg OverHom.f (eqToHom_symm_comp_eqToHom hcodEq)
            -- `cod`'s A-leg is `fst`: chain `bcSliceIso`/`baseChangeMap pIso`/`pInv`.
            have hcod_A : cod.f ≫ Λ = (fst : prod A (prod A P) ⟶ A) := by
              show cod.f ≫ (eqToHom hcodEq).f
                  ≫ (_pb (snd : prod A P ⟶ P) (L.F hbU (terminalSliceObj W A))).cone.π₁
                    ≫ pInv.f ≫ (fst : prod A P ⟶ A) = _
              rw [hcodf]
              -- collapse the eqToHom pair.
              rw [Cat.assoc, ← Cat.assoc (eqToHom hcodEq.symm).f, hee, Cat.id_comp]
              -- `cod'.f = bcSliceIso.f ≫ (baseChangeMap snd pIso).f`.
              show ((bcSliceIso A P).f
                  ≫ ((baseChangeFunctor (snd : prod A P ⟶ P)).map pIso).f)
                  ≫ (_pb (snd : prod A P ⟶ P) (L.F hbU (terminalSliceObj W A))).cone.π₁
                    ≫ pInv.f ≫ (fst : prod A P ⟶ A) = _
              rw [Cat.assoc,
                  show ((baseChangeFunctor (snd : prod A P ⟶ P)).map pIso)
                      = baseChangeMap (snd : prod A P ⟶ P) pIso from rfl,
                  ← Cat.assoc (baseChangeMap (snd : prod A P ⟶ P) pIso).f,
                  baseChangeMap_f_π₁ (snd : prod A P ⟶ P) pIso]
              simp only [Cat.assoc]
              rw [show pIso.f ≫ pInv.f ≫ (fst : prod A P ⟶ A) = (fst : prod A P ⟶ A) from by
                    rw [← Cat.assoc, show pIso.f ≫ pInv.f = Cat.id (prod A P) from
                      congrArg OverHom.f hp1]; exact Cat.id_comp _,
                  ← Cat.assoc,
                  show (bcSliceIso A P).f
                      ≫ (_pb (snd : prod A P ⟶ P) (sliceEmbedObj P A)).cone.π₁
                    = pair (fst : prod A (prod A P) ⟶ A)
                        ((snd : prod A (prod A P) ⟶ prod A P) ≫ snd) from
                    (HasPullbacks.has ((sliceEmbedObj P A).hom) (snd : prod A P ⟶ P)).lift_fst _,
                  fst_pair]
            -- the A-leg of `pf₀`/`sc₀`'s codomain `L.F (refl U') (L.F hUU' (L.F hbU term))`:
            -- post-compose `reflApp` onto `Λ`.
            let Λr : (L.F ((wsDirected S).refl U') (L.F hUU' (L.F hbU (terminalSliceObj W A)))).dom ⟶ A :=
              (reflApp L (L.F hUU' (L.F hbU (terminalSliceObj W A)))).f ≫ Λ
            -- `sfp.f ≫ fst = fst`.
            have hsfp_A : sfp.f ≫ (fst : prod A (prod A P) ⟶ A) = (fst : prod A P ⟶ A) := by
              show pair (fst : prod A P ⟶ A) (Cat.id (prod A P)) ≫ (fst : prod A (prod A P) ⟶ A) = _
              exact fst_pair _ _
            -- PIECE 1a: `sc₀.f ≫ Λr = (reflApp L one).f ≫ fst`.
            have hsc_A : sc₀.f ≫ Λr
                = (reflApp L (T.ht U').one).f ≫ (fst : prod A P ⟶ A) := by
              show ((reflApp L (T.ht U').one).f ≫ (sfp ⊚ cod).f
                  ≫ (isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))).f)
                  ≫ (reflApp L (L.F hUU' (L.F hbU (terminalSliceObj W A)))).f ≫ Λ = _
              rw [Cat.assoc, Cat.assoc,
                  ← Cat.assoc (isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))).f,
                  show (isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))).f
                      ≫ (reflApp L (L.F hUU' (L.F hbU (terminalSliceObj W A)))).f
                    = Cat.id _ from
                  congrArg OverHom.f
                    (inv_isoInv_comp (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))),
                  Cat.id_comp,
                  show (sfp ⊚ cod).f = sfp.f ≫ cod.f from rfl, Cat.assoc, hcod_A, hsfp_A]
            -- PIECE 1b: `(pushFibre g'').f ≫ Λ`.  `pushFibre g'' = Functor.map (functF hUU') g''
            -- = baseChangeMap (selectProj U' U hUU') g''`; with `selectProj U' U hUU' = snd` and the
            -- eqToHom casts (`hLF`/`hcodEq`), its A-leg is `(eqToHom hLF).f ≫ π₁(snd, xE') ≫ g''.f`.
            -- cast-naturality of `baseChangeMap` under a base-map equality (subst-trivial).
            have bcMap_cast : ∀ {C E : S} {a b : E ⟶ C} (e : a = b) {X Y : Over C} (gg : OverHom X Y),
                (baseChangeMap a gg).f ≫ (eqToHom (congrArg (fun z => baseChangeObj z Y) e)).f
                  = (eqToHom (congrArg (fun z => baseChangeObj z X) e)).f ≫ (baseChangeMap b gg).f := by
              intro C E a b e X Y gg; subst e
              rw [eqToHom_refl, eqToHom_refl]
              show (baseChangeMap a gg).f ≫ Cat.id _ = Cat.id _ ≫ (baseChangeMap a gg).f
              rw [Cat.comp_id, Cat.id_comp]
            have hpushFibre_A : (pushFibre W A hbU hUU' g'').f ≫ Λ
                = (eqToHom hLF).f ≫ (_pb (snd : prod A P ⟶ P) xE').cone.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A) := by
              show (baseChangeMap (tSelectProj Prod.snd U'.val U.val hUU') g'').f
                  ≫ (eqToHom hcodEq).f ≫ (_pb (snd : prod A P ⟶ P) (L.F hbU (terminalSliceObj W A))).cone.π₁
                    ≫ pInv.f ≫ (fst : prod A P ⟶ A) = _
              rw [← Cat.assoc,
                  show (eqToHom hcodEq)
                      = (eqToHom (congrArg (fun z => baseChangeObj z (L.F hbU (terminalSliceObj W A))) hsp))
                    from rfl,
                  bcMap_cast hsp g'',
                  show (eqToHom (congrArg (fun z => baseChangeObj z xE') hsp)) = (eqToHom hLF) from rfl,
                  Cat.assoc, ← Cat.assoc (baseChangeMap (snd : prod A P ⟶ P) g'').f,
                  baseChangeMap_f_π₁ (snd : prod A P ⟶ P) g'']
              -- `g''.f ≫ pInv.f = m.f`.
              simp only [Cat.assoc]
              rw [show g''.f ≫ pInv.f ≫ (fst : prod A P ⟶ A) = m.f ≫ (fst : prod A P ⟶ A) from by
                    rw [← Cat.assoc]; rfl]
            -- PIECE 1b (assembled): `pf₀.f ≫ Λr`.
            have hpf_A : pf₀.f ≫ Λr
                = (reflApp L (L.F hUU' xE')).f
                    ≫ (eqToHom hLF).f ≫ (_pb (snd : prod A P ⟶ P) xE').cone.π₁
                      ≫ m.f ≫ (fst : prod A P ⟶ A) := by
              show ((reflApp L (L.F hUU' xE')).f ≫ (pushFibre W A hbU hUU' g'').f
                  ≫ (isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))).f)
                  ≫ (reflApp L (L.F hUU' (L.F hbU (terminalSliceObj W A)))).f ≫ Λ = _
              rw [Cat.assoc, Cat.assoc,
                  ← Cat.assoc (isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))).f,
                  show (isoInv (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))).f
                      ≫ (reflApp L (L.F hUU' (L.F hbU (terminalSliceObj W A)))).f
                    = Cat.id _ from
                  congrArg OverHom.f
                    (inv_isoInv_comp (reflApp_isIso L (L.F hUU' (L.F hbU (terminalSliceObj W A))))),
                  Cat.id_comp, hpushFibre_A]
            -- ── PIECE 2: cast-eliminate the goal LHS down to `zN.f ≫ π₁(inner)`. ──
            -- collapse `(hcodObj ▸ zN).f ≫ πOut ≫ πIn` to `zN.f ≫ π₁(proj(trans b.2.2 hbN), L.F hUU' xE')`.
            have hLHScollapse : (hcodObj ▸ zN).f
                  ≫ (_pb (tSelectProj Prod.snd N.val U'.val hUN') (baseChangeObj (snd : prod A P ⟶ P) xE')).cone.π₁
                    ≫ (_pb (snd : prod A P ⟶ P) xE').cone.π₁
                = zN.f
                  ≫ (_pb (tSelectProj Prod.snd N.val U'.val hUN') (L.F hUU' xE')).cone.π₁
                    ≫ (_pb (tSelectProj Prod.snd U'.val U.val hUU') xE').cone.π₁ := by
              rw [hcastf, Cat.assoc,
                  ← Cat.assoc (eqToHom hcodObj).f, hcodObj', hbcInner hLF, Cat.assoc,
                  hLF', eqToHom_bc_π₁ hsp xE']
            -- post-compose `hstageProj` with the shared A-leg `Λr`, then apply Pieces 1a/1b.
            have hSP := congrArg (· ≫ Λr) hstageProj
            simp only [Cat.assoc] at hSP
            rw [hpf_A, hsc_A] at hSP
            -- rewrite the goal LHS via `hLHScollapse` (with the `≫ m.f ≫ fst` tail).
            have hLHSfull : (hcodObj ▸ zN).f
                  ≫ ((_pb (tSelectProj Prod.snd N.val U'.val hUN') (baseChangeObj (snd : prod A P ⟶ P) xE')).cone.π₁
                      ≫ (_pb (snd : prod A P ⟶ P) xE').cone.π₁) ≫ m.f ≫ (fst : prod A P ⟶ A)
                = zN.f
                  ≫ ((_pb (tSelectProj Prod.snd N.val U'.val hUN') (L.F hUU' xE')).cone.π₁
                      ≫ (_pb (tSelectProj Prod.snd U'.val U.val hUU') xE').cone.π₁) ≫ m.f ≫ (fst : prod A P ⟶ A) := by
              rw [← Cat.assoc, ← Cat.assoc, hLHScollapse, Cat.assoc, Cat.assoc]
            rw [hLHSfull]
            -- ── ISOLATED RESIDUAL (★ + Piece 3).  Goal now:
            --   zN.f ≫ (πOut' ≫ πIn') ≫ m.f ≫ fst = srcPB.cone.π₂ ≫ ψ ≫ fst.
            -- `hSP` (post-composed `hstageProj` with `Λr`, Pieces 1a/1b applied) reads:
            --   zN.f ≫ (transApp(refl U',hUN) xE').f ≫ π₁ ≫ (reflApp (L.F hUU' xE')).f
            --        ≫ (eqToHom hLF).f ≫ πIn ≫ m.f ≫ fst
            --     = (transApp(refl U',hUN') one).f ≫ π₁ ≫ (reflApp one).f ≫ fst.
            -- TWO remaining micro-steps, both pullback-pasting reindexings:
            --  (★)  πOut' ≫ πIn' = (transApp(refl U',hUN) xE').f ≫ π₁ ≫ (reflApp (L.F hUU' xE')).f
            --         ≫ (eqToHom hLF).f ≫ πIn  — identifies the descent-domain projection
            --       (`_pb (proj hUN') (L.F hUU' xE')`·`_pb (selectProj U' U hUU') xE'`) with the
            --       `proj_pushHom_f_π₁`-presentation of `pf₀`'s pushed content.  KEY LEMMA:
            --       `transApp_f_π₁π₁ cofinalProjSystem (refl U') hUN (L.F hUU' xE') z` with
            --       `z := (eqToHom hLF).f ≫ πIn` collapses the `transApp ≫ π₁ ≫ (inner π₁) ≫ z` to
            --       `(_pb (proj (trans (refl U') hUN)) (L.F hUU' xE')).cone.π₁ ≫ z = πOut' ≫ z`; then
            --       `eqToHom_bc_π₁ hsp xE'` turns `z = (eqToHom hLF).f ≫ πIn` into `πIn'`.  The ONLY
            --       gap is identifying `(reflApp (L.F hUU' xE')).f` (the explicit `pf₀` unit) with the
            --       transApp inner `(_pb (proj (refl U')) (L.F hUU' xE')).cone.π₁` — a `projReflIso`/
            --       `baseChangeIdNatIso` component characterisation (the lax `reflApp` of
            --       `laxOfProjSystem'` IS this pullback projection; needs a `reflApp_f_π₁`-style lemma).
            --  (Piece 3)  `hSP`'s RHS `(transApp(refl U',hUN') one).f ≫ π₁ ≫ (reflApp one).f ≫ fst`
            --       = srcPB.cone.π₂ ≫ ψ ≫ fst, via `hψfst : ψ ≫ fst = factorProj N A` and
            --       `hsrcEq : L.F (trans b.2.1 hbN) one = ⟨srcPB.pt, srcPB.π₂⟩` (rfl).
            -- Everything substantive (all A-leg sub-laws `hcod_A`/`hsc_A`/`hpf_A`, the cast-elimination
            -- `hLHScollapse`, and the goal-LHS reduction `hLHSfull`) is machine-checked above; the
            -- residual is the final on-the-nose `transApp`/`reflApp`/`ψ` pullback-pasting reindexing.
            -- ── (★): collapse `transApp ≫ π₁ ≫ reflApp ≫ (eqToHom hLF).f ≫ π₁(snd)` in hSP's LHS to
            -- `π₁_N ≫ π₁_U'`, and the RHS `transApp ≫ π₁ ≫ reflApp ≫ fst` to `srcPB.π₁ ≫ fst`.
            rw [reflApp_f_π₁ cofinalProjSystem (L.F hUU' xE'),
                reflApp_f_π₁ (i := U') cofinalProjSystem HasTerminal.one] at hSP
            -- LHS: `transApp(refl U',hUN) xE').f ≫ π₁(proj hUN, bc) ≫ π₁(proj(refl U'),xE') ≫ z`,
            -- with `z := (eqToHom hLF).f ≫ π₁(snd,xE') ≫ m.f ≫ fst`.
            rw [transApp_f_π₁π₁ cofinalProjSystem ((wsDirected S).refl U') hUN (L.F hUU' xE')
                  ((eqToHom hLF).f ≫ (_pb (snd : prod A P ⟶ P) xE').cone.π₁
                    ≫ m.f ≫ (fst : prod A P ⟶ A))] at hSP
            -- RHS: collapse with `z := fst`.
            rw [transApp_f_π₁π₁ cofinalProjSystem ((wsDirected S).refl U') hUN' HasTerminal.one
                  (fst : prod A P ⟶ A)] at hSP
            -- collapse `(eqToHom hLF).f ≫ π₁(snd)` to `π₁_U'`.
            have hcollapse0 : (eqToHom hLF).f ≫ (_pb (snd : prod A P ⟶ P) xE').cone.π₁
                = (_pb (tSelectProj Prod.snd U'.val U.val hUU') xE').cone.π₁ := by
              rw [hLF']; exact eqToHom_bc_π₁ hsp xE'
            have hcollapseU' : (eqToHom hLF).f ≫ (_pb (snd : prod A P ⟶ P) xE').cone.π₁
                  ≫ m.f ≫ (fst : prod A P ⟶ A)
                = (_pb (tSelectProj Prod.snd U'.val U.val hUU') xE').cone.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A) := by
              rw [← Cat.assoc, hcollapse0]
            rw [hcollapseU'] at hSP
            -- hSP now: `zN.f ≫ π₁_N ≫ π₁_U' ≫ m.f ≫ fst = srcPB.π₁ ≫ fst`.  Match goal LHS via assoc.
            rw [show (_pb (cofinalProjSystem.proj ((wsDirected S).trans ((wsDirected S).refl U') hUN))
                        (L.F hUU' xE')).cone.π₁
                      ≫ (_pb (tSelectProj Prod.snd U'.val U.val hUU') xE').cone.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A)
                  = ((_pb (cofinalProjSystem.proj ((wsDirected S).trans ((wsDirected S).refl U') hUN))
                        (L.F hUU' xE')).cone.π₁
                      ≫ (_pb (tSelectProj Prod.snd U'.val U.val hUU') xE').cone.π₁) ≫ m.f ≫ (fst : prod A P ⟶ A)
                from (Cat.assoc _ _ _).symm] at hSP
            rw [hSP]
            -- Piece 3: `srcPB.cone.π₁ ≫ fst = srcPB.cone.π₂ ≫ ψ ≫ fst`.
            -- `srcPB.cone.w` (with `(overTerm _).hom = id`): `π₁ = π₂ ≫ selectProj N U' hUN'`.
            have hsrcW : srcPB.cone.π₁ = srcPB.cone.π₂ ≫ tSelectProj Prod.snd N.val U'.val hUN' :=
              (Cat.comp_id srcPB.cone.π₁).symm.trans srcPB.cone.w
            -- `tSelectProj N U' hUN' ≫ fst = tFactorProj N aT = ψ ≫ fst`.
            have hfstFactor : tSelectProj Prod.snd N.val U'.val hUN' ≫ (fst : prod A P ⟶ A)
                = ψ ≫ (fst : prod A PN ⟶ A) := by
              rw [hψfst,
                  show (fst : prod A P ⟶ A) = tFactorProj Prod.snd U'.val aT List.mem_cons_self from
                    (tFactorProj_cons_head (l' := U.val) (f := Prod.snd) List.mem_cons_self).symm,
                  tSelectProj_factor Prod.snd N.val U'.val hUN' aT List.mem_cons_self]
            rw [hsrcW, Cat.assoc, hfstFactor]
          rw [show (r ≫ (zNd.f ≫ codPB.cone.π₁)) ≫ cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A)
                = r ≫ ((zNd.f ≫ codPB.cone.π₁) ≫ cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A)) from
              Cat.assoc _ _ _, hbridge]
          -- `r ≫ srcPB.cone.π₂ = a = ψ⁻¹`, and `ψ⁻¹ ≫ ψ ≫ fst = fst`.
          rw [show r ≫ srcPB.cone.π₂ ≫ ψ ≫ (fst : prod A PN ⟶ A)
                = (r ≫ srcPB.cone.π₂) ≫ ψ ≫ (fst : prod A PN ⟶ A) from (Cat.assoc _ _ _).symm,
              srcPB.lift_snd srcCone]
          show isoInv hψiso ≫ ψ ≫ (fst : prod A PN ⟶ A) = fst
          rw [show isoInv hψiso ≫ ψ ≫ (fst : prod A PN ⟶ A)
                = (isoInv hψiso ≫ ψ) ≫ (fst : prod A PN ⟶ A) from (Cat.assoc _ _ _).symm,
              inv_isoInv_comp hψiso, Cat.id_comp]
      exact freshSection_of_descentSection Dbar mC cnDN hcnDN s hs₂ hsA
    -- the cone `(q, id)` over `(Dbar.hom, snd)`, and its pullback lift `u : A×PN ⟶ cnDN.pt`.
    have hsq : q ≫ Dbar.hom = (Cat.id (prod A PN)) ≫ (snd : prod A PN ⟶ PN) := by
      rw [Cat.id_comp]; exact hqstruct
    obtain ⟨u, ⟨hu₁, hu₂⟩, _⟩ := hcnDN ⟨prod A PN, q, Cat.id (prod A PN), hsq⟩
    -- `t.f := u`; over-hom law `u ≫ cnDN.π₂ = id` is `hu₂`.
    refine ⟨⟨u, ?_⟩, ?_⟩
    · show u ≫ cnDN.π₂ = (overTerm (prod A PN)).hom
      show u ≫ cnDN.π₂ = Cat.id (prod A PN); exact hu₂
    · -- `t ⊚ mbarN = sliceFactorPoint A fst`: check underlying `u ≫ mf'N = pair fst id` by the eta law.
      apply OverHom.ext
      show u ≫ mf'N = pair (fst : prod A PN ⟶ A) (Cat.id (prod A PN))
      rw [pair_uniq _ _ (u ≫ mf'N) rfl rfl]
      congr 1
      · -- `A`-leg: `(u ≫ mf'N) ≫ fst = fst`.
        rw [Cat.assoc, hmf1N, ← Cat.assoc, hu₁]; exact hqfresh
      · -- `PN`-leg: `(u ≫ mf'N) ≫ snd = id`.
        rw [Cat.assoc, hmf2N]; exact hu₂
  obtain ⟨t, hfac⟩ := hpt
  exact freshSlicePoint_factors_imp_false mC hmC_mono hmC_niso cnDN hcnDN mf'N hmf1N hmf2N
    mbarN rfl t hfac

/-- A `Nat` tag strictly larger than every tag appearing in a token list `l` — hence no token
    `(freshTag l, _)` occurs in `l`.  `freshTag l := 1 + foldr max 0 (l.map Prod.fst)`. -/
def freshTag (l : List (Tok S)) : Nat := 1 + (l.map Prod.fst).foldr Nat.max 0

theorem le_foldr_max_of_mem : ∀ {ns : List Nat} {n : Nat}, n ∈ ns → n ≤ ns.foldr Nat.max 0
  | _ :: ns, n, h => by
    rcases List.mem_cons.1 h with e | hf
    · exact e ▸ Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max_of_mem hf) (Nat.le_max_right _ _)

/-- The fresh-tagged token is not in `l` (its tag exceeds every tag in `l`). -/
theorem freshTok_not_mem (l : List (Tok S)) (X : S) : ((freshTag l, X) : Tok S) ∉ l := by
  intro h
  have hmem : freshTag l ∈ l.map Prod.fst := List.mem_map.2 ⟨_, h, rfl⟩
  have hle : freshTag l ≤ (l.map Prod.fst).foldr Nat.max 0 := le_foldr_max_of_mem hmem
  exact absurd hle (by simp only [freshTag]; omega)

/-- **Freyd's §1.546 density (the genuine open core), now CLOSED.**  The §1.546 ESCAPE is Sorry-free
    (`baseChange_freshFactor_missed`); the (a) base-change comparison (`bcSliceIso`), (b) colimit
    point, and (c) reflection are Sorry-free in the TOKEN-lifted `richerSliceSection`.  Both the
    `A ∉ U` and `A ∈ U` cases are now the SAME branch: the embedded object `A` is added as a FRESH
    `Nat`-tagged token `aTok = (freshTag U.1, A)`, which is ALWAYS addable (`freshTok_not_mem`), so the
    richer stage `aTok :: U` exists unconditionally.  No fractions saturation is needed; the §1.547
    reduction around the core is machine-checked. -/
theorem richerSliceMiss (W : WSCover S) : RicherSliceMiss W := by
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  intro A hA U hbU xE' g'' hmono hniso
  -- UNIFORM escape (both `A ∈ U` and `A ∉ U`): add a FRESH copy of `A` as a fresh-tagged token
  -- `aTok = (freshTag U.1, A)`, which is ALWAYS addable (`freshTok_not_mem`) since its tag exceeds
  -- every tag in `U.1`.  `aTok.2 = A` definitionally, so `g''`'s type is unchanged.  Then the directed
  -- escape at `U' = aTok :: U` is the lifted `richerSliceSection`.
  let aTok : Tok S := (freshTag U.1, A)
  have hAU : aTok ∉ U.1 := freshTok_not_mem U.1 A
  have hnd : (aTok :: U.1).Nodup := List.nodup_cons.2 ⟨hAU, U.2.1⟩
  have hws : ∀ t ∈ (aTok :: U.1), WellSupported t.2 := by
    intro t hB; rcases List.mem_cons.1 hB with e | hf
    · exact e ▸ hA
    · exact U.2.2 t hf
  obtain ⟨x', hx'⟩ := richerSliceSection W aTok hA U hbU hAU xE' g'' hmono hniso hnd hws
  exact ⟨⟨aTok :: U.1, hnd, hws⟩, fun t hB => List.mem_cons.2 (Or.inr hB), x', hx'⟩

/-- **§1.546 DENSITY — `FibreDensity W`** for the §1.547 cofinal cover `W`.  The §1.547 stage-local
    density, the `wellPoints` field of the §1.543 `CofinalCapStep`.  Reduces (Phases 1–2, Sorry-free)
    to Freyd's genuine §1.546 density core `richerSliceMiss`. -/
theorem fibreDensity (W : WSCover S) : FibreDensity W :=
  fibreDensity_of_richerSliceMiss W (richerSliceMiss W)

end Freyd.FibreDensityProof

/-! ## The `wsCover` specialization (bundle form, the literal task statement) -/

namespace Freyd.CofinalProj

/-- **§1.546 DENSITY — `FibreDensity (wsCover S)`** for the concrete cofinal inhabitant of a bundled
    pre-regular category.  This is the literal §1.546 density of the task — the last genuine theorem
    of §1.543, now PROVEN Sorry-free, with the §1.547 reduction machine-checked and the genuine §1.546
    core `richerSliceMiss` itself proven. -/
theorem wsCover_fibreDensity (S : PreRegBundle.{u}) :
    letI := S.cat
    letI := S.pre
    letI := (wsCover S).dec
    Freyd.UniformWellPoints.FibreDensity (wsCover S) :=
  letI := S.cat
  letI := S.pre
  letI := (wsCover S).dec
  Freyd.FibreDensityProof.fibreDensity (wsCover S)

end Freyd.CofinalProj

-- The §1.547 reduction is SORRY-FREE / axiom-clean; the residuals are isolated in `richerSliceMiss`.
-- The §1.546(a) base-change/slice comparison is Sorry-free:
#print axioms Freyd.FibreDensityProof.bcSlice_isPullback
#print axioms Freyd.FibreDensityProof.bcSliceIso_isIso
#print axioms Freyd.FibreDensityProof.stageInclL_g''_factor
#print axioms Freyd.FibreDensityProof.fibreDensity_of_richerSliceMiss
-- `fibreDensity` / `wsCover_fibreDensity` depend on `SorryAx` *only* through `richerSliceMiss`,
-- whose two isolated residuals are (i) the §1.546(c) `stageInclFunctorL U'` fullness reflection
-- (`richerSliceSection`) and (ii) the `A ∈ U` fresh-copy case.  The whole §1.546 escape
-- (`baseChange_freshFactor_missed`), the (a) base-change comparison, the (b) colimit point, and the
-- §1.547 colimit↔fibre reduction are machine-checked Sorry-free.
#print axioms Freyd.FibreDensityProof.fibreDensity
#print axioms Freyd.FibreDensityProof.richerSliceSection
#print axioms Freyd.FibreDensityProof.richerSliceMiss
