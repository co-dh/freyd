/-
  §1.543 / §1.547 — `StepWellPoints (uniformStep W)`: the uniform successor POINTS every
  well-supported object.

  This file proves the `wellPoints` field of the §1.547 `CofinalCapStep` for the uniform
  successor `uniformStep W` (`UniformCapStep.lean`).  `StepWellPoints (uniformStep W)`
  (`CapitalizationTransfinite.lean`) asks, for every well-supported `A : S`, that the image
  `uniformStep.step A = ⟨W.base, terminalSliceObj A⟩` is `WellPointed` in `ratCapCat
  (cofinalProjSystem (S := S))` — the FULL directed union `⋃_U  S/(∏U)`.

  ── WHY full `WellPointed` holds here (and NOT at a single slice) ─────────────────────────────
  At one fixed slice `S/(∏U)` the embedded `sliceEmbedObj (∏U) A` is NOT well-pointed: a proper
  mono need not be product-form (`graph_satisfies_hyps` refutes; `properMono_forces_graph_iso`).
  But `ratCapCat` is the directed COLIMIT of all the slices.  An arbitrary proper colimit mono
  `m : E ↪ ⟨base, terminalSliceObj A⟩` is, at some stage `U`, a proper FIBRE mono
  `g : E_U ↪ (push of terminalSliceObj A) ≅ sliceEmbedObj (∏(chain U)) A`
  (`homInclL_factor` + the embedding `stageInclFunctorL` reflects mono/iso).  At a LATER stage the
  §1.546 DENSITY makes that fibre mono product-form, so `prodFormMono_wellPointed` supplies a slice
  g-point (`sliceFactorPoint`) missing it — a point that lives at that later slice, hence IS a point
  of `ratCapCat` and misses `m`.

  ── STRUCTURE ────────────────────────────────────────────────────────────────────────────────
  * Phase 1 — `pushTerminalSlice_iso`: the pushforward of `terminalSliceObj A` to stage `U` is
    `≅ sliceEmbedObj (∏(chain U)) A` (both are pullbacks of `(A→1, ∏U→1)`, i.e. the product
    `A × ∏U`; `isIso_of_two_pullbacks`).  SORRY-FREE.
  * Phase 2 — `colimitMono_reflects_to_fibre`: an arbitrary proper colimit mono into
    `⟨base, terminalSliceObj A⟩` reflects, via `homInclL_factor` + `stageInclFunctorL` embedding,
    to a proper fibre mono into the pushforward at some stage.  SORRY-FREE (uses only the existing
    lax reflection lemmas).
  * Phase 3 — `StageDensity`: the §1.546 density obligation, stated precisely as a `Prop`; the
    genuine mathematical heart.  `stepWellPoints_of_density` derives `StepWellPoints (uniformStep W)`
    from `StageDensity W` SORRY-FREE.  `StageDensity`/`FibreDensity` itself is now PROVEN in
    `FibreDensityProof.lean` (`fibreDensity`/`wsCover_fibreDensity`), so §1.543 is proven.

  No mathlib category theory; the lax colimit is on this repo's own `Cat`.  This file is Sorry-free
  (it defines and reduces to the density Prop, proven downstream); no `axiom`, no `:True`, no
  statement-weakening.
-/
module

public import Freyd.S1_547_UniformCapStep
public import Freyd.S1_543_SliceEquivalence

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.UniformWellPoints

universe u

variable {S : Type u} [Cat.{u} S] [PreRegularCategory S]

open Freyd.UniformCap
open Freyd.CofinalProj

-- The COFINAL index's positional `selectProj` needs object equality (the §1.543 `Classical.decEq`
-- exception, supplied via `WSCover.dec`); carried ambient, exactly as in `UniformCapStep.lean`.
variable [DecidableEq S]

/-! ## Generic iso-conjugation reflection (any `Cat`) -/

section IsoConj
variable {𝒜 : Type u} [Cat.{u} 𝒜]

/-- **Point-transport across iso conjugation.**  If `m = i ≫ s ≫ j` with `j` iso, and `x'` is a point
    of `cod s` that `s` does not factor (`¬∃ y', y' ≫ s = x'`), then `x' ≫ j` is a point of `cod m`
    that `m` does not factor.  (Post-compose a hypothetical factor by `j⁻¹` to factor `x'` through
    `s` — contradiction.)  This lifts a missing slice/stage point to a missing colimit point. -/
public theorem point_transport_unconj {one E T E' T' : 𝒜} {m : E ⟶ T} {i : E ⟶ E'} {s : E' ⟶ T'}
    {j : T' ⟶ T} (hfac : m = i ≫ s ≫ j) (hj : IsIso j)
    (x' : one ⟶ T') (hx' : ¬ ∃ y' : one ⟶ E', y' ≫ s = x') :
    ¬ ∃ y : one ⟶ E, y ≫ m = x' ≫ j := by
  rintro ⟨y, hy⟩
  apply hx'
  obtain ⟨jinv, hj1, _hj2⟩ := hj
  refine ⟨y ≫ i, ?_⟩
  have h2 : (y ≫ m) ≫ jinv = (x' ≫ j) ≫ jinv := by rw [hy]
  rw [hfac] at h2
  have hL : (y ≫ (i ≫ s ≫ j)) ≫ jinv = (y ≫ i) ≫ s := by
    rw [Cat.assoc y, Cat.assoc i, Cat.assoc s, hj1, Cat.comp_id, ← Cat.assoc y i]
  have hR : (x' ≫ j) ≫ jinv = x' := by rw [Cat.assoc, hj1, Cat.comp_id]
  rw [hL, hR] at h2
  exact h2

/-- `Monic` is reflected across pre-composition with an iso: `Monic (e ≫ s)` with `e` iso ⟹ `Monic s`. -/
public theorem mono_of_iso_comp_mono {X Y Z : 𝒜} {e : X ⟶ Y} {s : Y ⟶ Z}
    (he : IsIso e) (h : Monic (e ≫ s)) : Monic s := by
  obtain ⟨einv, he1, he2⟩ := he
  intro W u v huv
  -- `(u ≫ einv) ≫ (e ≫ s) = u ≫ s`; same for `v`; mono cancels to `u ≫ einv = v ≫ einv`.
  have hkey : (u ≫ einv) ≫ (e ≫ s) = (v ≫ einv) ≫ (e ≫ s) := by
    rw [Cat.assoc, ← Cat.assoc einv, he2, Cat.id_comp,
        Cat.assoc, ← Cat.assoc einv, he2, Cat.id_comp, huv]
  have h2 := h _ _ hkey
  -- cancel the iso `einv` on the right: post-compose with `e`.
  have := congrArg (fun t => t ≫ e) h2
  simpa only [Cat.assoc, he2, Cat.comp_id] using this

/-- `Monic` is reflected across post-composition with an iso: `Monic (s ≫ e)` with `e` iso ⟹ `Monic s`. -/
public theorem mono_of_mono_comp_iso {X Y Z : 𝒜} {s : X ⟶ Y} {e : Y ⟶ Z}
    (_he : IsIso e) (h : Monic (s ≫ e)) : Monic s := by
  intro W u v huv
  apply h
  rw [← Cat.assoc, ← Cat.assoc, huv]

/-- `Monic` is reflected across iso conjugation: `Monic (i ≫ s ≫ j)` with `i, j` iso ⟹ `Monic s`. -/
public theorem mono_unconj {W X Y Z : 𝒜} {i : W ⟶ X} {s : X ⟶ Y} {j : Y ⟶ Z}
    (hi : IsIso i) (hj : IsIso j) (h : Monic (i ≫ s ≫ j)) : Monic s :=
  mono_of_mono_comp_iso hj (mono_of_iso_comp_mono hi h)

end IsoConj

/-! ## Phase 1 — the pushforward of `terminalSliceObj A` is `sliceEmbedObj (∏(chain U)) A`

  `L.F (base≤U) (terminalSliceObj A) = baseChangeObj (proj) (terminalSliceObj A)` (definitionally),
  the chosen pullback of `(term A : A → ∏[] = 1)` along `proj : ∏(chain U) → ∏[]`.  Since the base
  `∏(chain base) = ∏[] = 1` is terminal, the product cone `(A × ∏(chain U), fst, snd)` is ALSO a
  pullback of that cospan; `isIso_of_two_pullbacks` makes the comparison an iso, and its `π₂`-leg is
  `snd`, so it is an `Over`-iso onto `sliceEmbedObj (∏(chain U)) A = ⟨A × ∏(chain U), snd⟩`. -/

variable (W : WSCover S)

/-- The product cone `(A × ∏(chain U), fst, snd)` is a pullback of the cospan
    `((terminalSliceObj A).hom, proj)` — both legs end in the terminal-equal base `∏(chain base)`. -/
private theorem prod_isPullback_of_terminalBase (A : S) {i : WSList S} (h : (wsDirected S).le W.base i) :
    (Cone.mk (f := (terminalSliceObj W A).hom) (g := (cofinalProjSystem (S := S)).proj h)
      (prod A (listProd (𝒞 := S) (i.1.map Prod.snd)))
      (fst : prod A (listProd (𝒞 := S) (i.1.map Prod.snd)) ⟶ A)
      (snd : prod A (listProd (𝒞 := S) (i.1.map Prod.snd)) ⟶ listProd (𝒞 := S) (i.1.map Prod.snd))
      (base_hom_uniq W (fst ≫ (terminalSliceObj W A).hom)
        (snd ≫ (cofinalProjSystem (S := S)).proj h))).IsPullback := by
  intro d
  refine ⟨pair d.π₁ d.π₂, ⟨fst_pair _ _, snd_pair _ _⟩, ?_⟩
  intro v hv₁ hv₂
  exact pair_uniq d.π₁ d.π₂ v hv₁ hv₂

/-- The chosen base-change pullback `baseChangeObj (proj h) (terminalSliceObj A)` is a pullback of
    the same cospan (`HasPullback.cone_isPullback`). -/
private theorem baseChange_isPullback (A : S) {i : WSList S} (h : (wsDirected S).le W.base i) :
    ((HasPullbacks.has (terminalSliceObj W A).hom ((cofinalProjSystem (S := S)).proj h)).cone).IsPullback :=
  (HasPullbacks.has (terminalSliceObj W A).hom ((cofinalProjSystem (S := S)).proj h)).cone_isPullback

/-- The product cone over the cospan, as a `Cone`. -/
private def prodCone (A : S) {i : WSList S} (h : (wsDirected S).le W.base i) :
    Cone (terminalSliceObj W A).hom ((cofinalProjSystem (S := S)).proj h) :=
  Cone.mk (f := (terminalSliceObj W A).hom) (g := (cofinalProjSystem (S := S)).proj h)
    (prod A (listProd (𝒞 := S) (i.1.map Prod.snd))) fst snd
    (base_hom_uniq W (fst ≫ (terminalSliceObj W A).hom) (snd ≫ (cofinalProjSystem (S := S)).proj h))

/-- The underlying `S`-arrow `A × ∏(chain U) ⟶ pushforward.dom`: the comparison `pair fst snd` from
    the product cone into the chosen base-change pullback. -/
public noncomputable def pushTerminalSlice_cmp (A : S) {i : WSList S} (h : (wsDirected S).le W.base i) :
    prod A (listProd (𝒞 := S) (i.1.map Prod.snd)) ⟶
      ((laxOfProjSystem' (cofinalProjSystem (S := S))).F h (terminalSliceObj W A)).dom :=
  (HasPullbacks.has (terminalSliceObj W A).hom ((cofinalProjSystem (S := S)).proj h)).lift (prodCone W A h)

/-- `pushTerminalSlice_cmp` is iso (`isIso_of_two_pullbacks`: the product cone and the chosen
    base-change pullback are both pullbacks of the same cospan). -/
public theorem pushTerminalSlice_cmp_isIso (A : S) {i : WSList S} (h : (wsDirected S).le W.base i) :
    IsIso (pushTerminalSlice_cmp W A h) :=
  isIso_of_two_pullbacks (prod_isPullback_of_terminalBase W A h) (baseChange_isPullback W A h) _
    ((HasPullbacks.has (terminalSliceObj W A).hom ((cofinalProjSystem (S := S)).proj h)).lift_fst (prodCone W A h))
    ((HasPullbacks.has (terminalSliceObj W A).hom ((cofinalProjSystem (S := S)).proj h)).lift_snd (prodCone W A h))

/-- The comparison commutes with the slice structure maps: `cmp ≫ pushforward.hom = snd`
    (`lift_snd`, since `pushforward.hom = π₂` and `(prodCone).π₂ = snd`). -/
public theorem pushTerminalSlice_cmp_hom (A : S) {i : WSList S} (h : (wsDirected S).le W.base i) :
    pushTerminalSlice_cmp W A h ≫ ((laxOfProjSystem' (cofinalProjSystem (S := S))).F h (terminalSliceObj W A)).hom
      = (sliceEmbedObj (listProd (𝒞 := S) (i.1.map Prod.snd)) A).hom :=
  (HasPullbacks.has (terminalSliceObj W A).hom ((cofinalProjSystem (S := S)).proj h)).lift_snd (prodCone W A h)

/-- **Phase 1 result.**  The pushforward of `terminalSliceObj A` to stage `U` is iso, in
    `Over (∏(chain U))`, to `sliceEmbedObj (∏(chain U)) A`.  Underlying arrow `pushTerminalSlice_cmp`
    (iso, commuting with the `snd` structure map). -/
@[expose] public noncomputable def pushTerminalSlice_iso (A : S) {i : WSList S} (h : (wsDirected S).le W.base i) :
    OverHom (sliceEmbedObj (listProd (𝒞 := S) (i.1.map Prod.snd)) A)
      ((laxOfProjSystem' (cofinalProjSystem (S := S))).F h (terminalSliceObj W A)) :=
  ⟨pushTerminalSlice_cmp W A h, pushTerminalSlice_cmp_hom W A h⟩

public theorem pushTerminalSlice_iso_isIso (A : S) {i : WSList S} (h : (wsDirected S).le W.base i) :
    @IsIso (Over (listProd (𝒞 := S) (i.1.map Prod.snd))) _ _ _ (pushTerminalSlice_iso W A h) :=
  overIso_of_underlying _ (pushTerminalSlice_cmp_isIso W A h)

/-! ## Phase 2 — an arbitrary proper colimit mono reflects to a proper fibre mono

  `homInclL_factor` writes any colimit hom `m = homInclL xE (terminalSliceObj A) a g` as
  `alignGerm ⊚ stageInclL g'' ⊚ alignGermInv` (the two aligns iso); `Monic`/`¬IsIso` of `m` transfer
  to `stageInclL g''` (`mono_unconj`/`isIso_unconj`), and the embedding `stageInclFunctorL` reflects
  them to the FIBRE map `g'' : · ⟶ L.F (base≤U) (terminalSliceObj A)` at stage `U = a.1`. -/

/-- Transition faithfulness of the §1.547 system (the `hfaith` hypothesis the lax reflection
    lemmas need), read off `projStage_faithful`. -/
private theorem projFaithful :
    ∀ {i j : WSList S} (hij : (wsDirected S).le i j)
      {x y : (laxOfProjSystem' (cofinalProjSystem (S := S))).A i} (p q : x ⟶ y),
      (laxOfProjSystem' (cofinalProjSystem (S := S))).Fmap hij p
        = (laxOfProjSystem' (cofinalProjSystem (S := S))).Fmap hij q → p = q :=
  fun {_ _} hij {_ _} p q heq =>
    projStage_faithful (cofinalProjSystem (S := S)) hij (cofinalProjSystem_cover hij) p q heq

/-- Transition conservativity (mono-restricted) of the §1.547 system. -/
private theorem projCons :
    ∀ {i j : WSList S} (hij : (wsDirected S).le i j)
      {x y : (laxOfProjSystem' (cofinalProjSystem (S := S))).A i} (φ : x ⟶ y),
      IsIso ((laxOfProjSystem' (cofinalProjSystem (S := S))).Fmap hij φ) →
        IsIso φ :=
  fun {_ _} hij {_ _} φ hiso =>
    projStage_conservative_full (cofinalProjSystem (S := S)) hij (cofinalProjSystem_cover hij) φ hiso

/-- The stage-`i` inclusion functor of the §1.547 lax colimit is faithful (`Embedding` + reflects
    iso), via `stageInclFunctorL_faithful` with `projFaithful`/`projCons`. -/
public theorem stageInclFaithful (i : WSList S) :
    @Faithful ((laxOfProjSystem' (cofinalProjSystem (S := S))).A i) _ (uniformTargetTy W) (uniformTargetCat W)
      (stageInclFunctorL _ (coherentProj (cofinalProjSystem (S := S))) i) :=
  stageInclFunctorL_faithful (laxOfProjSystem' (cofinalProjSystem (S := S))) (coherentProj (cofinalProjSystem (S := S)))
    (projFaithful (S := S)) (projCons (S := S)) i

/-- **Phase 2 — colimit mono reflects to a proper FIBRE mono into the pushforward.**  Given a proper
    colimit mono `m : ⟨iE, xE⟩ ↪ ⟨base, terminalSliceObj A⟩`, there is a stage `U ≥ base`, a fibre
    object `xE'`, and a fibre map `g'' : xE' ⟶ L.F (base≤U) (terminalSliceObj A)` that is a PROPER
    mono in `Over (∏(chain U))`.  (`homInclL_factor` strips `m` to a stage inclusion flanked by the
    iso realignments; conjugation + the faithful embedding reflect `Monic`/`¬IsIso`.) -/
public theorem colimitMono_reflects_to_fibre (A : S)
    {iE : WSList S} {xE : (laxOfProjSystem' (cofinalProjSystem (S := S))).A iE}
    (m : @Cat.Hom _ (uniformTargetCat W) ⟨iE, xE⟩ ⟨W.base, terminalSliceObj W A⟩)
    (hm : @Monic _ (uniformTargetCat W) _ _ m) (hniso : ¬ @IsIso _ (uniformTargetCat W) _ _ m) :
    ∃ (U : WSList S) (hbU : (wsDirected S).le W.base U)
      (xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U)
      (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A))
      (i : @Cat.Hom _ (uniformTargetCat W) ⟨iE, xE⟩ ⟨U, xE'⟩)
      (j : @Cat.Hom _ (uniformTargetCat W)
        ⟨U, (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)⟩
        ⟨W.base, terminalSliceObj W A⟩),
      Monic g'' ∧ ¬ IsIso g'' ∧
      @IsIso _ (uniformTargetCat W) _ _ i ∧ @IsIso _ (uniformTargetCat W) _ _ j ∧
      m = @Cat.comp _ (uniformTargetCat W) _ _ _ i
            (@Cat.comp _ (uniformTargetCat W) ⟨U, xE'⟩
              ⟨U, (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)⟩
              ⟨W.base, terminalSliceObj W A⟩
              (stageInclL (laxOfProjSystem' (cofinalProjSystem (S := S)))
                (coherentProj (cofinalProjSystem (S := S))) g'') j) := by
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  let L := laxOfProjSystem' (cofinalProjSystem (S := S))
  let hL := coherentProj (cofinalProjSystem (S := S))
  -- The base fibre `L.A W.base` is `Over (listProd W.base.1)` (defeq, `fibre_base_eq`); ascribe the
  -- embedded object at that stage so the germ machinery infers stage `j = W.base` (the `pr i =
  -- listProd i.1` projection index does not infer the stage from `Over (listProd W.base.1)` alone).
  let yA : L.A W.base := terminalSliceObj W A
  -- represent `m` as a germ `homInclL xE yA a g`.
  obtain ⟨a, g, hag⟩ := incl_surjective (homSystemL L hL xE yA) m
  -- `m = homInclL … a g`; factor through the iso realignments at `U := a.1`.
  have hmrep : m = homInclL L hL xE yA a g := hag.symm
  -- the stage-`a.1` germ `g'' := pushHom … (refl a.1) g`.
  have haU : (wsDirected S).le a.1 a.1 := (wsDirected S).refl a.1
  let g'' := pushHom L xE yA a.2.1 a.2.2 haU g
  -- `homInclL_factor`: `m = alignGerm ⊚ stageInclL g'' ⊚ alignGermInv`.
  have hfac := homInclL_factor L hL xE yA a g haU
  rw [hmrep] at hm hniso ⊢
  rw [hfac] at hm hniso
  -- the two realignments are isos.
  have hi_align : @IsIso _ (laxColimCat L hL) _ _ (alignGerm L hL xE ((wsDirected S).trans a.2.1 haU)) :=
    alignGerm_isIso L hL xE ((wsDirected S).trans a.2.1 haU)
  have hi_alignInv : @IsIso _ (laxColimCat L hL) _ _
      (alignGermInv L hL yA ((wsDirected S).trans a.2.2 haU)) :=
    alignGermInv_isIso L hL yA ((wsDirected S).trans a.2.2 haU)
  -- transfer `Monic`/`¬IsIso` to `stageInclL g''`.
  have hm_stage : @Monic _ (laxColimCat L hL) _ _ (stageInclL L hL g'') :=
    mono_unconj hi_align hi_alignInv hm
  have hniso_stage : ¬ @IsIso _ (laxColimCat L hL) _ _ (stageInclL L hL g'') := by
    intro h
    exact hniso (isIso_comp hi_align (isIso_comp h hi_alignInv))
  -- reflect to the FIBRE map `g''` via the faithful embedding.
  obtain ⟨hemb, _hcons⟩ := stageInclFaithful W a.1
  let hSF := stageInclFunctorL L hL a.1
  -- `Monic g''`: faithful (embedding) reflects monos (`stageInclL g'' = hSF.map g''`).
  have hg''_mono : Monic g'' := by
    intro Z u v huv
    apply hemb
    show hSF.map u = hSF.map v
    apply hm_stage
    show hSF.map u ≫ hSF.map g'' = hSF.map v ≫ hSF.map g''
    rw [← hSF.map_comp, ← hSF.map_comp, huv]
  -- `¬IsIso g''`: a functor preserves iso, so `IsIso g'' ⟹ IsIso (stageInclL g'')`.
  have hg''_niso : ¬ IsIso g'' := by
    intro h
    exact hniso_stage (functor_preserves_iso (F := hSF) g'' h)
  -- `m = alignGerm ⊚ (stageInclL g'' ⊚ alignGermInv)` (= `i ≫ s ≫ j`): `i = alignGerm`,
  -- `s = stageInclL g'' = (stageInclFunctorL).map g''`, `j = alignGermInv`, both flanks iso.
  exact ⟨a.1, a.2.2, L.F ((wsDirected S).trans a.2.1 haU) xE, g'',
    alignGerm L hL xE ((wsDirected S).trans a.2.1 haU),
    alignGermInv L hL yA ((wsDirected S).trans a.2.2 haU),
    hg''_mono, hg''_niso, hi_align, hi_alignInv, hfac⟩

/-! ## Phase 3 — the §1.546 DENSITY obligation and the reduction to it

  Phase 2 reduces `WellPointed ⟨base, terminalSliceObj A⟩` to: every proper FIBRE mono `g''` into the
  pushforward `L.F hbU (terminalSliceObj A)` (which is `≅ sliceEmbedObj (∏(chain U)) A`) is missed by
  a colimit point of `⟨base, terminalSliceObj A⟩`.  `StageDensity` packages exactly this missing-point
  obligation — the genuine §1.546 density content.

  WHY it is the honest §1.546 wall (and TRUE).  At one fixed stage `U` the fibre mono need NOT be
  product-form (`properMono_forces_graph_iso`), so no slice point of `sliceEmbedObj (∏(chain U)) A`
  need miss it.  But `ratCapCat` is the directed COLIMIT; the §1.546 DENSITY (`pairDense_*`,
  `pairDense_pb_canonical_dense`, already closed in `RationalCapitalization.lean`) makes the mono
  product-form at a LATER stage `U'`, where `prodFormMono_wellPointed` (`SliceEquivalence.lean`,
  Sorry-free, under `SpecialHere`) supplies a slice g-point of `sliceEmbedObj (∏(chain U')) A`
  missing the pushed mono.  That slice point, included at stage `U'` and transported back to
  `⟨base, terminalSliceObj A⟩` along the realignment iso `alignGerm` (the pushforward is iso to the
  base object in the colimit), is the missing COLIMIT point.  The density-driven product-form
  reduction + this point transport is isolated entirely inside `StageDensity`, which the reduction
  below consumes Sorry-free — and `StageDensity` is now PROVEN in `FibreDensityProof.lean`. -/

/-- **The §1.546 density obligation for the uniform successor at `A`.**  For every proper FIBRE mono
    `g''` into the pushforward `L.F hbU (terminalSliceObj A)` of `terminalSliceObj A` at any stage `U`,
    there is a colimit point of `⟨base, terminalSliceObj A⟩` that the colimit image of `g''` (the
    germ `homInclL` of `g''`, realigned to land in `⟨base, terminalSliceObj A⟩`) does NOT factor.

    This is precisely the content the directed-union density supplies (product-form at a later stage
    + slice g-point + realignment transport); it is the genuine §1.546 mathematical heart, isolated
    here as a single named Prop and PROVEN in `FibreDensityProof.lean`.  Stated against the book's
    `WellPointed` shape — no
    weakening: the conclusion is "∃ point, ¬∃ y factoring it through the colimit mono". -/
@[expose] public def StageDensity (W : WSCover S) : Prop :=
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  ∀ (A : S), WellSupported A →
    ∀ {E : uniformTargetTy W} (m : @Cat.Hom _ (uniformTargetCat W) E ⟨W.base, terminalSliceObj W A⟩),
      @Monic _ (uniformTargetCat W) _ _ m → ¬ @IsIso _ (uniformTargetCat W) _ _ m →
      ∃ (x : @Cat.Hom _ (uniformTargetCat W)
              (@HasTerminal.one _ (uniformTargetCat W) (uniformStepTarget_preRegular W).toHasTerminal)
              ⟨W.base, terminalSliceObj W A⟩),
        ¬ ∃ (y : @Cat.Hom _ (uniformTargetCat W)
                  (@HasTerminal.one _ (uniformTargetCat W)
                    (uniformStepTarget_preRegular W).toHasTerminal) E),
          @Cat.comp _ (uniformTargetCat W) _ _ _ y m = x

/-- **The SHARPER, stage-local §1.546 obligation.**  For every well-supported `A`, stage `U ≥ base`,
    fibre object `xE'`, and PROPER FIBRE mono `g'' : xE' ↪ L.F hbU (terminalSliceObj A)` (which is
    `≅ sliceEmbedObj (∏(chain U)) A`), the colimit image `(stageInclFunctorL U).map g''` is missed by
    a colimit point of its codomain `⟨U, pushforward⟩`.

    This is the GENUINE §1.546 content, now isolated at the exact stage where the directed-union
    density applies: `g''` becomes product-form at a later stage and `prodFormMono_wellPointed` gives
    the slice g-point.  Strictly sharper than `StageDensity` (no realignment bookkeeping — the point
    lives at the SAME object as the reflected mono).  `StageDensity` follows from it Sorry-free via
    Phase 2's factorization + `point_transport_unconj`. -/
@[expose] public def FibreDensity (W : WSCover S) : Prop :=
  letI : Cat (uniformTargetTy W) := uniformTargetCat W
  ∀ (A : S), WellSupported A →
    ∀ (U : WSList S) (hbU : (wsDirected S).le W.base U)
      (xE' : (laxOfProjSystem' (cofinalProjSystem (S := S))).A U)
      (g'' : xE' ⟶ (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)),
      Monic g'' → ¬ IsIso g'' →
      ∃ (x' : @Cat.Hom _ (uniformTargetCat W)
                (@HasTerminal.one _ (uniformTargetCat W)
                  (uniformStepTarget_preRegular W).toHasTerminal)
                ⟨U, (laxOfProjSystem' (cofinalProjSystem (S := S))).F hbU (terminalSliceObj W A)⟩),
        ¬ ∃ (y' : @Cat.Hom _ (uniformTargetCat W)
                  (@HasTerminal.one _ (uniformTargetCat W)
                    (uniformStepTarget_preRegular W).toHasTerminal) ⟨U, xE'⟩),
          @Cat.comp _ (uniformTargetCat W) _ ⟨U, xE'⟩ _ y'
            (stageInclFunctorL _ (coherentProj (cofinalProjSystem (S := S))) U |>.map g'') = x'

/-- **`StageDensity` from the sharper `FibreDensity`** (SORRY-FREE).  A proper colimit mono `m`
    reflects (Phase 2) to a proper fibre mono `g''` with `m = i ≫ (stageInclL g'') ≫ j`, `i, j` iso;
    `FibreDensity` supplies a point `x'` of the fibre-mono codomain missing `stageInclL g''`, and
    `point_transport_unconj` carries `x' ≫ j` to a colimit point missing `m`. -/
public theorem stageDensity_of_fibreDensity (W : WSCover S) (hfd : FibreDensity W) : StageDensity W := by
  intro A hA E m hm hniso
  obtain ⟨U, hbU, xE', g'', i, j, hg''mono, hg''niso, hi_iso, hj_iso, hfac⟩ :=
    colimitMono_reflects_to_fibre W A m hm hniso
  obtain ⟨x', hx'⟩ := hfd A hA U hbU xE' g'' hg''mono hg''niso
  refine ⟨@Cat.comp _ (uniformTargetCat W) _ _ _ x' j, ?_⟩
  exact point_transport_unconj hfac hj_iso x' hx'

/-- **The reduction.**  `StageDensity W` implies `StepWellPoints (uniformStep W)` — full
    well-pointedness of every `uniformStep.step A = ⟨base, terminalSliceObj A⟩`, the book's
    `WellPointed`.  SORRY-FREE: `StageDensity` is exactly the unfolded `WellPointed` conclusion for
    the embedded objects (every proper colimit mono is missed by a colimit point). -/
public theorem stepWellPoints_of_density (W : WSCover S) (hdens : StageDensity W) :
    StepWellPoints (uniformStep W) := by
  intro A hA
  show @WellPointed (uniformTargetTy W) (uniformTargetCat W)
    (uniformStepTarget_preRegular W).toHasTerminal (uniformStepObj W A)
  intro E m hm hniso
  exact hdens A hA m hm hniso

/-- **`StepWellPoints (uniformStep W)` from the sharper stage-local `FibreDensity`** (SORRY-FREE
    composite).  This is the cleanest interface: the whole §1.543 `wellPoints` field reduces to the
    genuine §1.546 stage-local density `FibreDensity W`. -/
public theorem stepWellPoints_of_fibreDensity (W : WSCover S) (hfd : FibreDensity W) :
    StepWellPoints (uniformStep W) :=
  stepWellPoints_of_density W (stageDensity_of_fibreDensity W hfd)

end Freyd.UniformWellPoints
