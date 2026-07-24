/-
  §1.547 — THE UNIFORM CAPITALIZATION SUCCESSOR as a `CapStep`.

  This file constructs `uniformStep (S : PreRegBundle) : CapStep S.carrier`, the successor that
  drives the (now proven) `Freyd.capData_exists`.  Its point (vs. the countable `nextStepOfEnum`) is that
  ONE rung adjoins a point to EVERY well-supported object of `S` simultaneously, so it can satisfy
  `StepWellPoints` (`CapitalizationTransfinite.lean`).

  ── ROUTE ──────────────────────────────────────────────────────────────────────────────────────
  The successor target is the LAX colimit `ratCapCat P_S` of the §1.547 base-change slice system
  `laxOfProjSystem' P_S`, where `P_S : ProjSystem (List S.carrier) listDirected S.carrier` is the
  system of finite-product projections over (lists of) well-supported objects of `S`:

    * stage index `U : List S.carrier`  (a finite set of objects, modelled as a list);
    * stage product `pr U = ∏U = listProd U`  (right-folded binary product, `pr [] = 1`);
    * projection `proj : ∏U' ⟶ ∏U` for `U ⊆ U'`  (the bigger product onto the smaller).

  `ratCapPreRegular_of_projCover P_S hpc` (RatCapStagePTC.lean) makes `ratCapCat P_S` pre-regular,
  given `hpc : ∀ {U U'} (h), Cover (P_S.proj h)`.  Each projection `∏U' ↠ ∏U` is a cover because the
  dropped factors are well-supported (`prod_fst_cover`/`cover_comp'`), so `hpc` is genuinely available.

  The successor functor `step : S → ratCapCat P_S` is the base embedding `S → Over (pr []) = Over 1`
  (`baseSliceObj`, Capitalization.lean — already faithful, terminal/product/equalizer/pullback/cover
  preserving) followed by the lax stage-0 inclusion `stageInclFunctorL []` (RatCapHcanon.lean).

  ── (R-A) SOLVED — the STRICT directed projection family is now CONCRETE, COFINAL & Sorry-free ───
  `proj_refl`/`proj_trans` must be ON-THE-NOSE.  Over the SUBSET-ordered index they cannot be built
  choice-free without positional matching (the `DecidableEq 𝒞` `ListProjFamily` wall).  We pay that
  wall with `Classical.decEq S` (the §1.543 exception) in `CofinalProjSystem.lean`, which builds the
  STRICT cofinal `cofinalProjSystem : ProjSystem (WSList S) (wsDirected S) S` over the SUBSET order
  (`selectProj` assembles the factor projections, `selectProj_refl`/`selectProj_trans` give the
  on-the-nose refl/trans, `selectProj_cover` makes each projection a cover off well-supported
  factors).  Unlike the earlier APPEND/PREFIX index (`WSChain`), the subset order is COFINAL over the
  FULL well-supported object set with no countability ceiling: every well-supported `B` is reached at
  its singleton index `{B}`.  The successor takes a `WSCover S` (carrying `dec : DecidableEq S` and
  the cofinality field), reading its `pr`/`proj` straight off `cofinalProjSystem`.

  ── STATUS ───────────────────────────────────────────────────────────────────────────────────────
  This file is SORRY-FREE: `uniformStep (W : WSCover S) : CapStep S` is fully assembled (pre-regular
  target, faithful successor, and all six finite-limit/cover preservation fields) over the cofinal
  index.  The §1.546 density obligation lives in `UniformWellPoints.lean`/`FibreDensityProof.lean`
  (`FibreDensity`) — now likewise proven Sorry-free, so §1.543 is proven.

  No mathlib category theory (the lax colimit is on this repo's own `Cat`); the ordinal exception is
  not needed here.  No `axiom`, no `: True`, no statement-weakening, no `Sorry`.
-/
import Freyd.S1_543_RatCapStagePTC
import Freyd.S1_541_RelativeCapitalization
import Freyd.S1_543_CapitalizationTransfinite
import Freyd.S1_547_CofinalProjSystem

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.UniformCap

universe u

variable {S : Type u} [Cat.{u} S] [PreRegularCategory S]

open Freyd.CofinalProj

-- The COFINAL index needs object equality for its positional `selectProj` (the §1.543 `Classical.decEq`
-- exception, supplied via `WSCover.dec`).  We carry it as an ambient instance for Phase 3–5; the
-- `uniformStep` inhabitant instantiates it from `W.dec` (`wsCover S` in `CofinalProjSystem.lean`).
variable [DecidableEq S]

-- INSTANCE-DIAMOND PIN (§1.543 restore).  `laxOfProjSystem'` needs `[HasPullbacks S]`, for which two
-- instances compete: `PreRegularCategory.toHasPullbacks` and the global `exactPullbacks` (= binary
-- products + equalizers, `S1_59`).  Resolution picks between them INCONSISTENTLY across the def sites of
-- this file, so the successor category `uniformTargetCat W` and the lax lemmas' outputs end up as
-- syntactically distinct `laxOfProjSystem' …` terms that never defeq-bridge in the elaborator (every
-- `CapStep` preservation field then reports a spurious type mismatch).  Pinning `HasPullbacks`/
-- `HasEqualizers S` to one representative each forces every `laxOfProjSystem' (cofinalProjSystem …)` to
-- resolve identically.  (The defeq still holds for the un-pinned form — see the `rfl` check — but only at
-- full transparency, which the field/argument elaborator does not use.)
local instance (priority := 10000) uniformPinEqualizers : HasEqualizers S :=
  products_pullbacks_implies_equalizers
local instance (priority := 10000) uniformPinPullbacks : HasPullbacks S :=
  PreRegularCategory.toHasPullbacks

/-! ## Phase 1–2 — the STRICT, COFINAL product-projection `ProjSystem` (imported)

  `ProjSystem.proj_refl`/`proj_trans` must be ON-THE-NOSE.  Over the SUBSET-ordered index they cannot
  be built choice-free without positional matching (the §1.547 `ListProjFamily` wall).  That wall is
  paid in `CofinalProjSystem.lean` (`Classical.decEq S`, the §1.543 exception): `cofinalProjSystem :
  ProjSystem (WSList S) (wsDirected S) S` is the COFINAL strict system whose projection `selectProj`
  is a cover off well-supported factors (`cofinalProjSystem_cover`).  The successor consumes it via a
  `WSCover S` (carrying `dec : DecidableEq S` and the cofinality field).  Unlike the prefix index
  (`WSChain`, now deleted), this is cofinal over the FULL object set with no countability ceiling. -/

/-! ## Phase 3 — pre-regularity of the successor target -/

/-- **`uniformStepTarget_preRegular`** — the lax-colimit target `ratCapCat cofinalProjSystem` is
    pre-regular, by `ratCapPreRegular_of_projCover` with `hpc = cofinalProjSystem_cover`.  (`[Nonempty
    (WSList S)]` holds since `W.base : WSList S`; `HasEqualizers S` from products+pullbacks.) -/
noncomputable def uniformStepTarget_preRegular (W : WSCover S) :
    @PreRegularCategory (Obj (laxOfProjSystem' (cofinalProjSystem (S := S))))
      (ratCat (cofinalProjSystem (S := S))) := by
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  letI : Nonempty (WSList S) := ⟨W.base⟩
  exact ratCapPreRegular_of_projCover (cofinalProjSystem (S := S))
    (fun h => cofinalProjSystem_cover h)

/-! ## Phase 4 — the `CapStep`

  The fibre of the lax base-change system at the BASE index `W.base` is `pcObj cofinalProjSystem
  W.base = Over (listProd (W.base).1) = Over (listProd []) = Over (1_S)` (a slice in `S` ITSELF over
  the terminal — `W.base_chain : (W.base).1 = []`).  So the §1.547 base embedding into THIS route is
  the canonical `S ≃ S/1`: `X ↦ ⟨X, term X⟩` (transported to the base stage).

  `step : S → ratCapCat cofinalProjSystem` is then `terminalSliceObj` followed by the lax base-stage
  inclusion `stageInclFunctorL W.base` (RatCapHcanon.lean), i.e. `X ↦ ⟨W.base, terminalSliceObj X⟩`. -/

variable (W : WSCover S)

/-- The successor target type.  (`W` only fixes the `DecidableEq` index data via the ambient
    instance; the lax colimit itself depends on it through `cofinalProjSystem`.) -/
abbrev uniformTargetTy (_W : WSCover S) : Type u :=
  Obj (laxOfProjSystem' (cofinalProjSystem (S := S)))

-- The successor target category, `ratCat cofinalProjSystem` = `laxColimCat (laxOfProjSystem' …) (coherentProj …)`.
-- The lax preservation lemmas produce data in the raw `laxColimCat …` form, which is definitionally this
-- category; the `[HasPullbacks S]` instance pin above is what keeps that defeq on-the-nose so the elaborator
-- accepts the lax data in every `CapStep` field without an "application type mismatch".
noncomputable instance uniformTargetCat (W : WSCover S) : Cat.{u} (uniformTargetTy W) :=
  ratCat (cofinalProjSystem (S := S))


/-- The base stage product is the terminal of `S` (`listProd (W.base).1 = listProd [] = 1_S`). -/
theorem pr_base_eq : listProd (𝒞 := S) ((W.base).1.map Prod.snd) = (HasTerminal.one : S) := by
  rw [W.base_chain]; rfl

/-- Any two maps into an object equal to the terminal agree. -/
theorem hom_uniq_of_eq_one {Z : S} (hZ : Z = (HasTerminal.one : S)) {X : S}
    (f g : X ⟶ Z) : f = g := by subst hZ; exact term_uniq f g

/-- Any two maps into the base stage `listProd (W.base).1 = 1` agree (it is terminal). -/
theorem base_hom_uniq {X : S} (f g : X ⟶ listProd (𝒞 := S) ((W.base).1.map Prod.snd)) : f = g :=
  hom_uniq_of_eq_one (pr_base_eq W) f g

/-- The fibre at the base index is the slice `S/1` over the terminal of `S`. -/
theorem fibre_base_eq :
    (laxOfProjSystem' (cofinalProjSystem (S := S))).A W.base = Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd)) :=
  rfl

/-- **The §1.547 base embedding `S → S/(∏(base)) = S/1`**, `X ↦ ⟨X, term X⟩` (transported along
    `pr_base_eq` so the structure map `X ⟶ listProd (W.base).1` is the canonical terminator). -/
def terminalSliceObj (X : S) : Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd)) :=
  ⟨X, ((pr_base_eq W).symm ▸ (term X : X ⟶ (HasTerminal.one : S)))⟩

/-- The morphism part: `f : X ⟶ Y ↦ ⟨f, term_uniq⟩` (commutes with the structure maps since any two
    maps into the base stage `= 1` agree). -/
def terminalSliceMap {X Y : S} (f : X ⟶ Y) :
    OverHom (terminalSliceObj W X) (terminalSliceObj W Y) :=
  ⟨f, base_hom_uniq W _ _⟩

/-- The base embedding `S → S/1` is a functor (laws transport via `OverHom.ext` to the underlying
    `S`-arrow equalities, which hold by the source's `Functor`/`Cat` laws). -/
def terminalSliceFunctor :
    @Functor S (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) _
      (overCat (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) where
  obj := terminalSliceObj W
  map f := terminalSliceMap W f
  map_id _ := OverHom.ext rfl
  map_comp {_ _ _} _ _ := OverHom.ext rfl

/-- **`terminalSliceObj` is FAITHFUL.**  The underlying arrow of `terminalSliceMap f` IS `f`, so two
    maps with equal images have equal `f` (`OverHom.f` is literally the original arrow). -/
theorem terminalSliceFaithful :
    @Faithful S _ (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd)))
      (overCat (listProd (𝒞 := S) ((W.base).1.map Prod.snd)))
      (terminalSliceFunctor W) := by
  refine ⟨?_, ?_⟩
  · -- embedding: the underlying arrow of `terminalSliceMap f` IS `f`.
    intro X Y f g h
    exact congrArg OverHom.f h
  · -- conservative: `(terminalSliceMap f).f = f`, so an iso image forces `f` iso.
    intro X Y f hiso
    exact overIso_underlying hiso

/-- The successor object map `step : S → ratCapCat P`: base-embed into the base fibre, then include
    that fibre into the lax colimit (`⟨W.base, ·⟩`).  It IS the composite `stageInclFunctorL W.base ∘
    terminalSliceObj` (the object map of `stageInclFunctorL W.base` is `fun x => ⟨W.base, x⟩`). -/
def uniformStepObj (X : S) : uniformTargetTy W :=
  ⟨W.base, terminalSliceObj W X⟩

/-- The lax base-stage inclusion functor `Over (listProd (chain base)) → ratCapCat P`, object map
    `⟨W.base, ·⟩`.  (`stageInclFunctorL` of RatCapHcanon.lean, instantiated at the §1.547 system and
    stage `W.base`.) -/
noncomputable def stageInclNil :
    @Functor (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) (uniformTargetTy W)
      (overCat (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) (uniformTargetCat W) :=
  stageInclFunctorL (laxOfProjSystem' (cofinalProjSystem (S := S))) (coherentProj (cofinalProjSystem (S := S)))
    W.base

/-- **The successor functor `step : S → ratCapCat P` is a `Functor`** — the composite
    `stageInclNil ∘ terminalSliceObj` (`compFunctor`).  `uniformStepObj = stageInclNil.obj ∘
    terminalSliceObj` definitionally, so this IS its functoriality. -/
noncomputable def uniformStepFunctor :
    @Functor S (uniformTargetTy W) _ (uniformTargetCat W) :=
  compFunctor (terminalSliceFunctor W) (stageInclNil W)

/-! ### Base-embedding (`terminalSliceObj : S → Over (chain base)`) finite-limit preservation

  `terminalSliceObj` is the canonical `S ≃ S/(∏(chain base)) = S/1` (the stage product is the
  terminal, `pr_base_eq`).  Maps in the slice are determined by their underlying `S`-arrow
  (`OverHom.ext`), and the slice terminal/products/equalizers are the `over*` instances; each
  preservation reduces to the corresponding `S`-fact (the slice over the terminal is `S` itself). -/

/-- The fibre `HasEqualizers (Over (chain base))` instance the lax data uses (`overHasEqualizers`,
    needs `HasEqualizers S`). -/
noncomputable local instance : HasEqualizers S := products_pullbacks_implies_equalizers

/-- **`terminalSliceObj` preserves the terminal.**  Maps into `terminalSliceObj W one` in the slice
    are determined by their underlying `S`-arrow into `one`, and any two such agree (`term_uniq`). -/
theorem terminalSlicePresTerminal :
    letI : HasTerminal (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasTerminal _
    @PreservesTerminal S (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) _ _
      (terminalSliceFunctor W)
      PreRegularCategory.toHasTerminal (overHasTerminal _) := by
  intro X f g
  exact OverHom.ext (term_uniq f.f g.f)

/-- **`terminalSliceObj` preserves binary products.**  The slice product comparison is iso iff its
    underlying `S`-arrow is; `terminalSliceObj` is the underlying-identity slice equivalence, so the
    comparison is the `S`-product comparison (an iso, `prod_self_iso`). -/
theorem terminalSlicePresProds :
    letI : HasBinaryProducts (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasBinaryProducts _
    @PreservesBinaryProducts S (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) _ _
      (terminalSliceFunctor W)
      PreRegularCategory.toHasBinaryProducts (overHasBinaryProducts _) := by
  letI : HasBinaryProducts (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasBinaryProducts _
  intro A B
  -- the cone `(terminalSliceObj (A×B), map fst, map snd)` has the slice product universal property:
  -- underlying it is the `S`-product of `A, B`, and slice maps are determined by underlying arrows.
  refine Colim.isIso_of_product_up (𝒞 := Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd)))
    (terminalSliceFunctor W |>.map fst) (terminalSliceFunctor W |>.map snd) ?_
  intro Z f g
  -- mediator: pair the underlying arrows in `S`, lift to the slice (term-uniqueness over `pr base`).
  refine ⟨⟨pair f.f g.f, base_hom_uniq W _ _⟩, ⟨OverHom.ext (fst_pair f.f g.f),
      OverHom.ext (snd_pair f.f g.f)⟩, ?_⟩
  intro v hv₁ hv₂
  -- uniqueness: underlying `v.f` equals `pair f.f g.f` by `pair_uniq` (its `fst`/`snd` legs are `f.f`/`g.f`).
  exact OverHom.ext (pair_uniq f.f g.f v.f (congrArg OverHom.f hv₁) (congrArg OverHom.f hv₂))

/-- **`terminalSliceObj` preserves equalizers.**  The image cone `(terminalSliceObj (eqObj f g),
    map (eqMap f g))` has the slice equalizer universal property (underlying it is the `S`-equalizer,
    slice maps determined by underlying arrows); two equalizers ⟹ comparison iso. -/
theorem terminalSlicePresEqs :
    letI : HasEqualizers (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasEqualizers _
    @PreservesEqualizers S (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) _ _
      (terminalSliceFunctor W)
      products_pullbacks_implies_equalizers (overHasEqualizers _) := by
  letI : HasEqualizers (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasEqualizers _
  letI : HasEqualizers S := products_pullbacks_implies_equalizers
  intro A B f g
  -- the image cone is an equalizer of `(map f, map g)` in the slice.
  have himg : (EqualizerCone.mk (f := terminalSliceFunctor W |>.map f)
      (g := terminalSliceFunctor W |>.map g) (terminalSliceObj W (eqObj f g))
      (terminalSliceFunctor W |>.map (eqMap f g))
      (by rw [← (terminalSliceFunctor W).map_comp, ← (terminalSliceFunctor W).map_comp,
        eqMap_eq f g])).IsEqualizer := by
    intro d
    -- underlying `d.map.f : d.dom.dom ⟶ A` equalizes `f, g` (the slice cone equation, underlying).
    have hd : d.map.f ≫ f = d.map.f ≫ g := congrArg OverHom.f d.eq
    refine ⟨⟨eqLift f g d.map.f hd, base_hom_uniq W _ _⟩,
      OverHom.ext (eqLift_fac f g d.map.f hd), ?_⟩
    intro v hv
    exact OverHom.ext (eqLift_uniq f g d.map.f hd v.f (congrArg OverHom.f hv))
  -- the chosen-equalizer comparison factors `map (eqMap f g)`; two equalizers ⟹ iso.
  exact isIso_of_two_equalizers himg (chosenEqualizer_isEqualizer _ _)
    ((HasEqualizers.eq _ _ _ _).lift _) ((HasEqualizers.eq _ _ _ _).fac _)

/-- **`terminalSliceObj` preserves monos.**  A slice map is monic iff its underlying `S`-arrow is
    (`Σ` preserves/reflects monos); `terminalSliceMap φ` is underlying `φ`, so `Monic φ ⟹ Monic`. -/
theorem terminalSlicePresMono {x y : S} (φ : x ⟶ y) (hφ : Monic φ) :
    @Monic (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) _ _ _ (terminalSliceFunctor W |>.map φ) := by
  intro Z u v huv
  -- underlying: `u.f ≫ φ = v.f ≫ φ` (the slice equation, underlying), `φ` monic ⟹ `u.f = v.f`.
  have h : u.f ≫ φ = v.f ≫ φ := congrArg OverHom.f huv
  exact OverHom.ext (hφ u.f v.f h)

/-- **`terminalSliceObj` preserves covers.**  A slice map is a cover iff its underlying `S`-arrow is
    (`cover_of_cover_f`); `terminalSliceMap φ` is underlying `φ`. -/
theorem terminalSlicePresCover {x y : S} (φ : x ⟶ y) (hφ : Cover φ) :
    @Cover (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) _ _ _ (terminalSliceFunctor W |>.map φ) :=
  cover_of_cover_f (terminalSliceFunctor W |>.map φ) hφ

/-- **The base-stage terminal receives a map from `terminalSliceObj one`.**  A slice arrow from any
    object `X` of the fibre to `terminalSliceObj one`; underlying it is `term X.dom : X.dom ⟶ one`,
    slice-condition by `term`-uniqueness over `pr base`. -/
def terminalSliceTerminalArrow (X : Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) :
    @Cat.Hom _ (overCat (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) X (terminalSliceObj W (one : S)) :=
  ⟨term X.dom, base_hom_uniq W _ _⟩

/-! ### Lax stage-inclusion (`stageInclNil`) terminal preservation

  The stage-`base` terminal `⟨base, (overHasTerminal _).one⟩` is terminal in the lax colimit (maps
  into it are unique — the `uniq` argument of `laxColimHasTerminal`, valid at any stage since it only
  uses `pushUniq`).  This is the lax mirror of `objIncl_preservesTerminal`, in uniqueness form. -/

/-- **Maps into the stage-`i` terminal `⟨i, (T.ht i).one⟩` are unique** in the lax colimit — the
    `uniq` half of `laxColimHasTerminal`, valid at ANY stage `i` (it only uses `T.pushUniq`). -/
theorem laxTerminalUniqAt {ι : Type w} {D : Directed ι} (L : LaxCatSystem.{w, w} ι D)
    (hL : Coherent L) (T : LaxTerminalData L) (i : ι) (X : Obj L)
    (f g : @Cat.Hom (Obj L) (laxColimCat L hL) X ⟨i, (T.ht i).one⟩) : f = g := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨jX, xX⟩ := X
  refine Quotient.inductionOn f (fun ⟨a, fa⟩ => ?_)
  refine Quotient.inductionOn g (fun ⟨b, gb⟩ => ?_)
  apply Quotient.sound
  obtain ⟨k', hak', hbk'⟩ := D.bound a.1 b.1
  refine ⟨⟨k', D.trans a.2.1 hak', D.trans a.2.2 hak'⟩, hak', hbk', ?_⟩
  exact T.pushUniq (D.trans a.2.2 hak') _ _

/-- **A map `X ⟶ ⟨i, (T.ht i).one⟩` into the stage-`i` terminal exists** for every `X` in the lax
    colimit — the `trm` construction of `laxColimHasTerminal`, targeted at stage `i` (germ of
    `pushTrm` at a common bound). -/
noncomputable def laxTerminalArrowAt {ι : Type w} {D : Directed ι} (L : LaxCatSystem.{w, w} ι D)
    (hL : Coherent L) (T : LaxTerminalData L) (i : ι) (X : Obj L) :
    @Cat.Hom (Obj L) (laxColimCat L hL) X ⟨i, (T.ht i).one⟩ := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨jX, xX⟩ := X
  let bd := D.bound jX i
  let k := Classical.choose bd
  have hk : D.le jX k ∧ D.le i k := Classical.choose_spec bd
  exact homInclL L hL xX (T.ht i).one ⟨k, hk.1, hk.2⟩ (T.pushTrm hk.2 (L.F hk.1 xX))

/-- **`stageInclNil` preserves the terminal** (uniqueness form): maps into the lax stage-`base`
    terminal are unique.  `stageInclNil W (overHasTerminal _).one = ⟨base, (ht base).one⟩`. -/
theorem stageInclNilPresTerminal :
    letI : Nonempty (WSList S) := ⟨W.base⟩
    letI : HasTerminal (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasTerminal _
    @PreservesTerminal (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) (uniformTargetTy W) _
      (uniformTargetCat W) (stageInclNil W)
      (overHasTerminal _)
      (laxColimHasTerminal (laxOfProjSystem' (cofinalProjSystem (S := S))) (coherentProj (cofinalProjSystem (S := S)))
        (ratLaxTerminalData (cofinalProjSystem (S := S)))) := by
  letI : Nonempty (WSList S) := ⟨W.base⟩
  intro X f g
  exact laxTerminalUniqAt (laxOfProjSystem' (cofinalProjSystem (S := S))) (coherentProj (cofinalProjSystem (S := S)))
    (ratLaxTerminalData (cofinalProjSystem (S := S))) W.base X f g

/-- **(R-step) The successor functor is FAITHFUL.**  Composite of the faithful base embedding
    `terminalSliceFaithful` and the faithful lax stage-`[]` inclusion `stageInclNil`. -/
theorem uniformStepFaithful :
    @Faithful S _ (uniformTargetTy W) (uniformTargetCat W)
      (uniformStepFunctor W) :=
  faithful_comp
    (terminalSliceFaithful W)
    (stageInclFunctorL_faithful (laxOfProjSystem' (cofinalProjSystem (S := S)))
      (coherentProj (cofinalProjSystem (S := S)))
      (fun {_ _} hij {_ _} p q heq =>
        projStage_faithful (cofinalProjSystem (S := S)) hij (cofinalProjSystem_cover hij) p q heq)
      (fun {_ _} hij {_ _} φ hiso =>
        projStage_conservative_full (cofinalProjSystem (S := S)) hij (cofinalProjSystem_cover hij) φ hiso)
      W.base)

/-! ## Phase 5 — the assembled `CapStep`

  `uniformStep W : CapStep S` packages the real target (`T = ratCapCat (cofinalProjSystem (S := S))`,
  pre-regular by `uniformStepTarget_preRegular`) and the real successor functor `step = uniformStepObj`
  (faithful via `uniformStepFaithful`).  The single-step PRESERVATION fields (`stepTerminal`,
  `stepTerminalArrow`, `stepProds`, `stepEqs`, `stepMono`, `stepCover`) are the composites of the base
  embedding's preservation (`terminalSliceObj` preserves all finite limits/covers — the slice `S/1`
  is `S`) with the lax stage-inclusion's preservation (`stageInclFunctorL_preservesProducts`,
  `…_preservesEqualizers`, `…_preservesPullbacks`, `homInclL_cover_*` of RatCapHcanon.lean).  Each is a
  genuine lemma threaded through `compFunctor` into the exact `CapStep` field shape — Sorry-free. -/

set_option maxHeartbeats 1000000 in
/-- **The §1.547 uniform capitalization successor as a `CapStep`.**  Real `T`/`catT`/`preT`/`step`/
    `stepFun`; every preservation/faithfulness field is a real lax-composition lemma (Sorry-free). -/
noncomputable def uniformStep (W : WSCover S) : CapStep S where
  T := uniformTargetTy W
  catT := uniformTargetCat W
  preT := uniformStepTarget_preRegular W
  step := uniformStepObj W
  stepFun := uniformStepFunctor W
  stepFaithful := uniformStepFaithful W
  stepTerminal := by
    letI : Nonempty (WSList S) := ⟨W.base⟩
    letI : HasTerminal (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasTerminal _
    letI : Cat (uniformTargetTy W) := uniformTargetCat W
    letI : HasTerminal (uniformTargetTy W) := (uniformStepTarget_preRegular W).toHasTerminal
    intro X f g
    exact preservesTerminal_uniq_comp (𝒜 := S)
      (ℬ := Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) (ℰ := uniformTargetTy W)
      (F := terminalSliceFunctor W) (G := stageInclNil W)
      (terminalSlicePresTerminal W) (stageInclNilPresTerminal W)
      (fun {a b} ψ hψ =>
        stageInclFunctorL_preservesMono (laxOfProjSystem' (cofinalProjSystem (S := S)))
          (coherentProj (cofinalProjSystem (S := S)))
          (fun {i j} hij {p q} χ hχ => projStage_preservesMono (cofinalProjSystem (S := S)) hij χ hχ)
          (i := W.base) ψ hψ)
      X f g
  stepTerminalArrow := by
    -- `step one = ⟨base, terminalSliceObj one⟩`.  Land at the stage-`base` lax terminal
    -- `⟨base, (overHasTerminal _).one⟩` (`laxTerminalArrowAt`), then include the fibre arrow
    -- `(overHasTerminal _).one ⟶ terminalSliceObj one` (`terminalSliceTerminalArrow`).
    letI : Cat (uniformTargetTy W) := uniformTargetCat W
    intro X
    exact laxTerminalArrowAt (laxOfProjSystem' (cofinalProjSystem (S := S))) (coherentProj (cofinalProjSystem (S := S)))
        (ratLaxTerminalData (cofinalProjSystem (S := S))) W.base X ≫
      (stageInclNil W).map (terminalSliceTerminalArrow W (overHasTerminal _).one)
  stepProds := by
    letI : HasBinaryProducts (uniformTargetTy W) :=
      (uniformStepTarget_preRegular W).toHasBinaryProducts
    letI : HasBinaryProducts (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasBinaryProducts _
    letI : Cat (uniformTargetTy W) := uniformTargetCat W
    intro A B
    exact preservesBinaryProducts_comp (𝒜 := S)
      (ℬ := Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) (ℰ := uniformTargetTy W)
      (F := terminalSliceFunctor W) (G := stageInclNil W)
      (terminalSlicePresProds W)
      (stageInclFunctorL_preservesProducts (laxOfProjSystem' (cofinalProjSystem (S := S)))
        (coherentProj (cofinalProjSystem (S := S))) (ratLaxProductData (cofinalProjSystem (S := S))) W.base)
  stepEqs := by
    letI : Cat (uniformTargetTy W) := uniformTargetCat W
    letI heCol : HasEqualizers (uniformTargetTy W) :=
      laxColimHasEqualizers (laxOfProjSystem' (cofinalProjSystem (S := S))) (coherentProj (cofinalProjSystem (S := S)))
        (ratLaxEqualizerData (cofinalProjSystem (S := S)))
    letI : HasEqualizers (Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) := overHasEqualizers _
    have hcomp : @PreservesEqualizers S (uniformTargetTy W) _ (uniformTargetCat W)
        (uniformStepFunctor W) _ heCol :=
      preservesEqualizers_comp (𝒜 := S)
        (ℬ := Over (listProd (𝒞 := S) ((W.base).1.map Prod.snd))) (ℰ := uniformTargetTy W)
        (F := terminalSliceFunctor W) (G := stageInclNil W)
        (terminalSlicePresEqs W)
        (stageInclFunctorL_preservesEqualizers (laxOfProjSystem' (cofinalProjSystem (S := S)))
          (coherentProj (cofinalProjSystem (S := S))) (ratLaxEqualizerData (cofinalProjSystem (S := S))) W.base)
    letI preT := uniformStepTarget_preRegular W
    have hgoal := @preservesEqualizers_target_irrel S (uniformTargetTy W) _ (uniformTargetCat W)
      (uniformStepFunctor W) products_pullbacks_implies_equalizers
      heCol
      (@products_pullbacks_implies_equalizers (uniformTargetTy W) _
        preT.toHasBinaryProducts preT.toHasPullbacks)
      hcomp
    intro A B f g
    exact hgoal f g
  stepMono := fun {x y} φ hφ =>
    stageInclFunctorL_preservesMono (laxOfProjSystem' (cofinalProjSystem (S := S)))
      (coherentProj (cofinalProjSystem (S := S)))
      (fun {i j} hij {a b} ψ hψ => projStage_preservesMono (cofinalProjSystem (S := S)) hij ψ hψ)
      (i := W.base) (terminalSliceFunctor W |>.map φ) (terminalSlicePresMono W φ hφ)
  stepCover := fun {x y} φ hφ =>
    stageInclFunctorL_preservesCover (laxOfProjSystem' (cofinalProjSystem (S := S)))
      (coherentProj (cofinalProjSystem (S := S)))
      (fun {i j} hij {a b} p q heq =>
        projStage_faithful (cofinalProjSystem (S := S)) hij (cofinalProjSystem_cover hij) p q heq)
      (fun {i j} hij {a b} ψ hψ => projStage_preservesCover (cofinalProjSystem (S := S)) hij ψ hψ)
      (i := W.base) (terminalSliceFunctor W |>.map φ) (terminalSlicePresCover W φ hφ)

end Freyd.UniformCap
