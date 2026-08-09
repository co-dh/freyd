module

public import Freyd.S1_48_RationalCapitalization
public import Freyd.S1_546_SliceWellPointed
public import Freyd.S1_47
public import Freyd.S1_36

/-! # §1.543 C — the §1.547 slice equivalence interface, and the precise well-pointedness gap

  This file packages the §1.547 factor-slice bridge `Â → Σ U, A/(∏U)` (committed Sorry-free in
  `RationalCapitalization.lean` as `pairHomToSlice`/`pairHomOfSlice`/`pairSliceObj`) into a clean
  **two-sided equivalence interface** at a FIXED base, and uses it to pin the EXACT remaining gap of
  Freyd's §1.543 capitalization endgame: well-pointedness of the structured slice.

  ## What this file establishes (all Sorry-free; the residual is NAMED, never faked)

  Route assessment (Step 0 of the brief), then the reusable interface.

  ### Route decision: NEITHER route closes §1.543 — both reduce to the SAME single open fact

  The brief proposes Route 1 (direct `listDirected` colimit of structured slices) and Route 2 (via
  `A* = pairRatCat`).  After reading the committed infrastructure, the determination is:

  * **`pairRatCat` / `pairPreRegular` are NOT Sorry-free.**  `PreRegularCategory (PairObj 𝒞)`
    (`pairPreRegular`) rests on `pairPullbacksTransferCovers`, which is a genuine `Sorry`
    (`RationalCapitalization.lean:3080`).  So Route 2's *first* premise ("`A*` is pre-regular") is
    itself open, and Route 1's structured-slice transitions (the `PairObj`-pullbacks
    `pairHasPullbacks`) feed the same cover-transfer obligation.

  * **The well-pointedness obligation is ONE fact, identical in both routes.**  Both routes must
    discharge: a *proper* mono into the structured embedded object `sliceEmbedObj (∏U) A` is missed
    by some point.  R15 (`prodFormMono_misses_point`, Sorry-free, axiom-free) escapes any
    **product-form** proper mono `id_A × (i : B'↪P)`.  The gap is the reduction "arbitrary proper
    mono ⟹ product form", which `sliceEmbed_factor_wellPointed` (`RationalCapitalization.lean:4544`)
    leaves as its lone `Sorry`, with the long note explaining WHY it is not elementary in the plain
    slice and `graph_satisfies_hyps` proving the naive "generic point escapes" is FALSE.

  * **`PairDense` does NOT supply the reduction.**  `PairDense` is the class of *dense* maps (covers
    / epis: `pairDense_cover`/`pairDense_epi`); the well-pointedness obligation is about proper
    *monos* (the opposite extreme).  There is NO committed theorem "proper `Â`-mono ⟹ product form",
    and the file headers (`StepWellPointed.lean`, the `sliceEmbed_factor_wellPointed` note) record
    this as the genuine open content of §1.546/547.  Hence the brief's premise "subobjects in the
    `A*` layer are product-form" is the unproven goal, not an available lemma.

  CONCLUSION.  The cleanest Sorry-free deliverable is the slice-equivalence INTERFACE itself
  (the bridge, packaged as a fixed-base equivalence) plus the EXACT reduction of structured-slice
  well-pointedness to the product-form escape, so the single missing fact is isolated as a named
  hypothesis (`ProperMonoIsProductForm`) and everything around it is machine-checked.

  ### The committed interface

  * `SliceBridge` — the fixed-base, two-sided bridge: at base `∏Y°`, `pairHomToSlice`/`pairHomOfSlice`
    are mutually inverse on underlying arrows (a `PairHom X → Y` is THE SAME DATA as a slice map
    `reindexObj (listProdRestrict X° Y°) (pairSliceObj X) → pairSliceObj Y`).
  * `bridge_roundtrip_g` / `bridge_roundtrip_f` — the round-trips, Sorry-free.
  * `ProperMonoIsProductForm` — the single missing §1.547 fact, named as a `Prop` over a base.
  * `wellPointed_of_productForm` — GIVEN `ProperMonoIsProductForm`, the structured embedded object is
    `WellPointed` (the R15 escape applied uniformly).  This is the Sorry-free reduction; the only
    open input is the named hypothesis, exactly Freyd's §1.546 reduction. -/

namespace Freyd

universe u

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
  [DecidableEq 𝒞]

/-! ## The fixed-base slice bridge, packaged as a two-sided correspondence

  At the codomain base `∏Y.targets`, `pairHomToSlice` and `pairHomOfSlice` are inverse bijections on
  underlying arrows.  This is the §1.547 "`Â`-morphism = slice morphism over the common base"
  equivalence, recorded as explicit round-trips. -/

/-- The slice-side target subset of a `PairHom`'s codomain into its domain (`Y° ⊆ X°`). -/
abbrev pairTargetSub {X Y : PairObj 𝒞} (m : PairHom X Y) : ∀ T ∈ Y.targets, T ∈ X.targets :=
  pairHom_targets_subset m

/-- **The bridge round-trip `Â → slice → Â`** preserves the underlying arrow.  `pairHomOfSlice`
    applied to `pairHomToSlice m` recovers a `PairHom` with the SAME underlying `.g` as `m`.  Since a
    `PairHom` is determined by its `.g` (`PairHom.ext`), the round-trip is the identity. -/
theorem bridge_roundtrip_g {X Y : PairObj 𝒞} (m : PairHom X Y) :
    (pairHomOfSlice (pairHom_targets_subset m) (pairHomToSlice m)).g = m.g := rfl

/-- **The bridge round-trip `slice → Â → slice`** preserves the underlying arrow `.f`.  Given a slice
    map `φ` over `∏Y°` from the reindexed `pairSliceObj X` to `pairSliceObj Y`, `pairHomToSlice` of
    `pairHomOfSlice hsub φ` has the SAME underlying `.f = φ.f`.  (Equality as `OverHom`s then follows
    from `OverHom.ext`, the slice-hom extensionality.) -/
public theorem bridge_roundtrip_f {X Y : PairObj 𝒞} (hsub : ∀ T ∈ Y.targets, T ∈ X.targets)
    (φ : OverHom (reindexObj (listProdRestrict X.targets Y.targets hsub) (pairSliceObj X))
                 (pairSliceObj Y)) :
    (pairHomToSlice (pairHomOfSlice hsub φ)).f = φ.f := rfl

/-! ## The well-pointedness reduction: from product-form to the R15 escape

  This is the genuine §1.546/547 content, isolated so the single missing fact is a NAMED
  hypothesis and the escape around it is machine-checked.  Freyd's §1.546 escape
  (`prodFormMono_misses_point`, Sorry-free, axiom-free) handles any *product-form* proper mono
  `id_A × (i : B'↪P)`.  The open content (`sliceEmbed_factor_wellPointed`'s `Sorry`) is the
  reduction of an *arbitrary* proper mono to product form.  We name exactly that reduction as
  `ProperMonoIsProductForm` and prove the well-pointedness payoff from it Sorry-free. -/

variable [PullbacksTransferCovers 𝒞]

/-- **The single missing §1.546/547 fact, named.**  Every proper mono `m : D ↪ sliceEmbedObj P A`
    in the slice `Over P` factors as an iso of its domain followed by a PRODUCT-FORM mono
    `prodFormMono i` (for a proper base mono `i : B' ↪ P`): there is a proper monic `i : B' ↪ P` and
    a slice iso `e : D ≅ ⟨A×B', snd≫i⟩` with `e ≫ prodFormMono i = m`.  This is Freyd's §1.546
    reduction — "every subobject of `AB` is of the form `AB'`" — which is NOT elementary in the plain
    slice (`graph_satisfies_hyps` refutes the naive form; the genuine reduction lives in the
    localization layer).  Naming it makes the well-pointedness payoff machine-checkable. -/
@[expose] public def ProperMonoIsProductForm (P A : 𝒞) : Prop :=
  ∀ {D : Over P} (m : D ⟶ sliceEmbedObj P A), OverMono m → ¬ OverIso m →
    ∃ (B' : 𝒞) (i : B' ⟶ P) (_ : Monic i) (_ : ¬ IsIso i)
      (e : D ⟶ (⟨prod A B', snd ≫ i⟩ : Over P)),
      OverIso e ∧ e ⊚ prodFormMono (A := A) i = m

/-- **Well-pointedness from the product-form reduction (the R15 escape, applied uniformly).**
    GIVEN the named §1.546 reduction `ProperMonoIsProductForm P A`, the structured embedded object
    `sliceEmbedObj P A` is `WellPointed` in `Over P` whenever some `g : P → A` exists (the witness
    g-point).  Proof: a proper mono `m` is, by `hpf`, `e ≫ prodFormMono i` with `e` a slice iso and
    `i : B' ↪ P` proper; `prodFormMono_misses_slicePoint` gives a g-point missed by `prodFormMono i`;
    any factorization through `m` would, post-composed with `e⁻¹`, factor through `prodFormMono i`,
    contradiction.  This is the Sorry-free half — the only open input is `hpf`. -/
public theorem wellPointed_of_productForm {P A : 𝒞} (g : P ⟶ A) (hpf : ProperMonoIsProductForm P A) :
    @WellPointed (Over P) _ (overHasTerminal P) (sliceEmbedObj P A) := by
  intro D m hm hniso
  obtain ⟨B', i, hi_mono, hi_proper, e, he_iso, hfac⟩ := hpf m hm hniso
  -- the g-point missed by the product-form mono `prodFormMono i`
  refine ⟨sliceFactorPoint A g, ?_⟩
  rintro ⟨y, hy⟩
  -- `y ≫ m = point`, and `m = e ≫ prodFormMono i`, so `(y ≫ e) ≫ prodFormMono i = point`.
  refine prodFormMono_misses_slicePoint (A := A) i hi_mono hi_proper g ⟨y ≫ e, ?_⟩
  rw [Cat.assoc, show e ≫ prodFormMono (A := A) i = m from hfac]; exact hy

/-- **Well-pointedness of the structured factor object (the §1.547 payoff under the named gap).**
    For `A = U.get k` a well-supported factor of a finite set `U`, the embedded object
    `sliceEmbedObj (∏U) A` is `WellPointed` in `Over (∏U)`, GIVEN the §1.546 reduction
    `ProperMonoIsProductForm`.  This is exactly `sliceEmbed_factor_wellPointed`
    (`RationalCapitalization.lean`) — byte-for-byte the book's `WellPointed` — with its lone `Sorry`
    replaced by the honest named hypothesis.  The g-point witness is the projection
    `listProdProj U k : ∏U → U.get k`. -/
public theorem sliceEmbed_factor_wellPointed_of_productForm (U : List 𝒞) (k : Fin U.length)
    (hpf : ProperMonoIsProductForm (listProd U) (U.get k)) :
    @WellPointed (Over (listProd U)) _ (overHasTerminal (listProd U))
      (sliceEmbedObj (listProd U) (U.get k)) :=
  wellPointed_of_productForm (listProdProj U k) hpf

/-! ## §1.546 — the DETERMINATION: `ProperMonoIsProductForm` as stated is FALSE; the genuine
    relative-cap content is product-form well-pointedness (Sorry-free, this section)

  `ProperMonoIsProductForm P A` (above) asks that EVERY proper *plain-slice* mono into
  `sliceEmbedObj P A` be product-form.  That is not merely hard — it is **provably false**, by two
  independent Sorry-free witnesses imported here:

  * `properMono_forces_graph_iso` — the "graph of the generic point" (`graph_satisfies_hyps`,
    `RationalCapitalization.lean`) is a proper plain-slice mono that is NOT product-form: assuming
    `ProperMonoIsProductForm` forces it to be a slice-iso, i.e. forces
    `IsIso (pair (proj_k) id)`, which fails whenever the factor `U.get k` is not `≅ 1`.
  * `properMono_one_forces_wellPointed` — at base `P = 1`, `ProperMonoIsProductForm 1 A` together
    with any point `g : 1 → A` gives, via `wellPointed_of_productForm` then `factorWP_imp_wp`
    (`SliceWellPointed.lean`, Sorry-free), that `A` is `WellPointed` *downstairs*.  Since
    `WellSupported A` does NOT imply `WellPointed A` in a non-`Capital` category, the hypothesis
    cannot hold in general — it would presuppose the very capitalization it is meant to build.

  CONCLUSION.  `wellPointed_of_productForm`'s hypothesis is unprovable; chasing it is a dead end.
  Freyd's §1.546 never asks for it.  The relative-capitalization step (§1.545,
  `IsRelativeCapitalization`) only ranges over *downstairs* proper subobjects `i : B' ↪ P`, whose
  slice image is the PRODUCT-FORM mono `prodFormMono i` — and THAT is missed by every point
  (`prodFormMono_misses_slicePoint`, Sorry-free).  The corrected, true, and sufficient statement is
  therefore "every *proper product-form* mono misses a point", built Sorry-free below as
  `prodFormMono_wellPointed`.  Its properness ingredient is exactly Freyd's §1.472 specialness
  (`IsSpecial`) — properness of `id_A × i` from properness of `i` is FALSE without specialness
  (§1.475 Z-sets, recorded at `prodEndo_faithful_of_embedding`), so `IsSpecial` is the honest,
  load-bearing hypothesis, not a fake. -/

/-- **`ProperMonoIsProductForm` is FALSE — witness 1 (the graph).**  If
    `ProperMonoIsProductForm (∏U) (U.get k)` held, the proper plain-slice mono
    `graph_satisfies_hyps U k` (underlying `pair (proj_k) id`) — which is NOT product-form — would be
    forced to be a slice-iso, i.e. `pair (listProdProj U k) (id)` would be iso.  This fails for any
    factor `U.get k` not isomorphic to `1`, refuting the hypothesis.  (A product-form decomposition
    `e ⊚ prodFormMono i = m` with `e` iso would give `e.f ≫ snd` a section of `i`, forcing the proper
    base mono `i` to be iso — the contradiction inside the proof.) -/
public theorem properMono_forces_graph_iso (U : List 𝒞) (k : Fin U.length)
    (hpf : ProperMonoIsProductForm (listProd U) (U.get k)) :
    IsIso (pair (listProdProj U k) (Cat.id (listProd U))) := by
  obtain ⟨m, hmf, hmono, _hsec⟩ := graph_satisfies_hyps U k
  have hOverMono : OverMono m := hmono
  by_cases hiso : OverIso m
  · have := overIso_underlying hiso
    rwa [hmf] at this
  · obtain ⟨B', i, hi_mono, hi_proper, e, _he_iso, hfac⟩ := hpf m hOverMono hiso
    exfalso
    apply hi_proper
    have hunder : e.f ≫ pair (fst : prod (U.get k) B' ⟶ U.get k) (snd ≫ i) = m.f := by
      have := congrArg OverHom.f hfac
      simpa [prodFormMono] using this
    have hsnd : (e.f ≫ snd) ≫ i = Cat.id (listProd U) := by
      have h2 : e.f ≫ pair (fst : prod (U.get k) B' ⟶ U.get k) (snd ≫ i) ≫ snd
              = pair (listProdProj U k) (Cat.id (listProd U)) ≫ snd := by
        rw [← Cat.assoc, hunder, hmf]
      rw [snd_pair, snd_pair] at h2
      rw [Cat.assoc]; exact h2
    have hleft : i ≫ (e.f ≫ snd) = Cat.id B' := by
      apply hi_mono
      rw [Cat.assoc, hsnd, Cat.comp_id, Cat.id_comp]
    exact ⟨e.f ≫ snd, hleft, hsnd⟩

/-- **`ProperMonoIsProductForm` is FALSE — witness 2 (forces Capital).**  At base `P = 1`, the
    hypothesis `ProperMonoIsProductForm 1 A` together with any global point `g : 1 → A` makes `A`
    itself `WellPointed`: `wellPointed_of_productForm g hpf` gives `WellPointed (sliceEmbedObj 1 A)`,
    and `factorWP_imp_wp` (Sorry-free, `SliceWellPointed.lean`) descends that to `WellPointed A`.
    Since `WellSupported A` does not imply `WellPointed A` outside a `Capital` category, the
    hypothesis cannot hold for a generic well-supported `A` — it presupposes capitalization.  This
    pins `ProperMonoIsProductForm` as the WRONG statement (over-strong), exactly as Freyd's §1.546
    (which uses only *downstairs* subobjects) avoids. -/
public theorem properMono_one_forces_wellPointed (A : 𝒞) (g : (one : 𝒞) ⟶ A)
    (hpf : ProperMonoIsProductForm (one : 𝒞) A) : WellPointed A :=
  factorWP_imp_wp A (wellPointed_of_productForm g hpf)

/-! ### The corrected, true statement: product-form well-pointedness (§1.546, Sorry-free)

  Freyd's §1.546 missed-point argument concerns only PRODUCT-FORM subobjects `id_A × i` (the slice
  images of downstairs proper monos `i : B' ↪ P`).  For those, well-pointedness is fully provable.
  Properness of `id_A × i` from properness of `i` is the §1.472 specialness content (`IsSpecial`),
  honest and load-bearing; monicity and the missed-point are the Sorry-free
  `prodFormMono_mono` / `prodFormMono_misses_slicePoint`. -/

section ProductForm

/-- The §1.472 specialness condition, phrased directly over the in-scope products (avoiding the
    `CartesianCategory` instance-coherence clash of `IsSpecial`): the right-hand product `m × id_B`
    of a proper mono `m` with witnessing proper base subobject is again proper.  `IsSpecial 𝒞`
    (`S1_47.lean`) supplies exactly this when the ambient products are the `CartesianCategory` ones. -/
@[expose] public def SpecialHere : Prop :=
  ∀ {A' A B' B : 𝒞} (m : A' ⟶ A) (n : B' ⟶ B), ProperMono m → ProperMono n →
    ProperMono (pair (fst (A := A') (B := B) ≫ m) (snd (A := A') (B := B)))

/-- **§1.472 — the product-form mono `id_A × i` is PROPER when `i` is** (under specialness).  Given
    `SpecialHere 𝒞`, a proper base mono `i : B' ↪ P`, and any proper subobject `j : A'' ↪ A` of the
    factor `A`, the product-form slice mono `prodFormMono i` is not a slice-iso.  Its underlying arrow
    is `id_A × i = (prodEndo A).map i`; `isIso_prod_mono_iff` swaps that to `i × id_A`, whose
    properness is exactly the specialness instance at `(i, j)`.  NOTE properness here is NOT free —
    without specialness it FAILS (§1.475 Z-sets, `prodEndo_faithful_of_embedding`); specialness + a
    proper subobject of `A` is the genuine hypothesis. -/
public theorem prodFormMono_proper (hSp : SpecialHere (𝒞 := 𝒞)) {A P B' : 𝒞} (i : B' ⟶ P)
    (hi : ProperMono i) {A'' : 𝒞} (j : A'' ⟶ A) (hj : ProperMono j) :
    ¬ OverIso (prodFormMono (A := A) i) := by
  intro hiso
  have hf : IsIso (prodFormMono (A := A) i).f := overIso_underlying hiso
  have hform : (prodFormMono (A := A) i).f = (prodEndoIsFunctor A).map i := by
    rw [prodEndo_map]
    show pair (fst : prod A B' ⟶ A) (snd ≫ i) = pair (fst ≫ Cat.id A) (snd ≫ i)
    rw [Cat.comp_id]
  rw [hform, ← isIso_prod_mono_iff A i] at hf
  exact (hSp i j hi hj).2 hf

variable [PullbacksTransferCovers 𝒞]

/-- **§1.546 — product-form well-pointedness (the CORRECTED, Sorry-free payoff).**  In `Over P`, the
    embedded object `sliceEmbedObj P A` is `WellPointed` *against product-form subobjects*: every
    PROPER PRODUCT-FORM mono `prodFormMono i` (for a proper base mono `i : B' ↪ P`) is a genuine
    proper slice mono (`prodFormMono_mono` + `prodFormMono_proper`) that misses the slice point
    `sliceFactorPoint A g` for EVERY `g : P → A` (`prodFormMono_misses_slicePoint`).  This is exactly
    the content Freyd's §1.545 relative-capitalization step consumes (downstairs subobjects only) —
    the honest replacement for the false `ProperMonoIsProductForm`. -/
public theorem prodFormMono_wellPointed (hSp : SpecialHere (𝒞 := 𝒞)) {A P B' : 𝒞} (i : B' ⟶ P)
    (hi : ProperMono i)
    {A'' : 𝒞} (j : A'' ⟶ A) (hj : ProperMono j) (g : P ⟶ A) :
    OverMono (prodFormMono (A := A) i) ∧ ¬ OverIso (prodFormMono (A := A) i) ∧
      ¬ ∃ y : overTerm P ⟶ (⟨prod A B', snd ≫ i⟩ : Over P),
          y ≫ prodFormMono (A := A) i = sliceFactorPoint A g :=
  ⟨prodFormMono_mono i hi.1, prodFormMono_proper hSp i hi j hj,
   prodFormMono_misses_slicePoint i hi.1 hi.2 g⟩

end ProductForm

/-! ## §1.547 — the FIXED-`U` slice equivalence `A*|U ≃ A/(∏U)`

  Freyd (§1.547, lines 4958-4961): for a finite list `U` of well-supported objects, `A*|U` is the
  full subcategory of the rational category `A*` on objects `(A,F)` with `F° ⊆ U`, and it is
  EQUIVALENT to the slice `A/(∏U) = Over (listProd U)`.  This is the FIXED-base equivalence — NO
  colimit; the directed union `A* = ⋃_U A*|U` comes later.

  ### The design (chosen given this repo's vocabulary)

  The repo has NO bundled `Equivalence` record; its functor-equivalence notion is
  `EquivalenceFunctor F := Embedding F ∧ Full F ∧ HasRepresentativeImage F` (S1_31), i.e. fully
  faithful + essentially surjective.  So we express `A*|U ≃ A/(∏U)` as an `EquivalenceFunctor`.

  Freyd's `F° ⊆ U` subcategory has objects sitting over DIFFERENT bases `∏(F°)`, so the object map
  into the single slice `Over (∏U)` is not literal.  We follow Freyd's own padding: work with the
  full subcategory `PairOnU U` on objects whose targets are EXACTLY `U` (in order), where every
  object sits over the common base `∏U` and `pairSliceObj` is an HONEST object map into `Over(∏U)`.
  The bridge (`pairHomToSlice`/`pairHomOfSlice`, Sorry-free in `RationalCapitalization.lean`) makes
  the resulting functor fully faithful; representative-image is the slice→pair construction (every
  `⟨A,h:A→∏U⟩` is `pairSliceObj` of the padded `(A, {h ≫ proj_k})`).  The padding `A*|U ≃ PairOnU U`
  (every `F° ⊆ U` is iso to one with `F'° = U`) is the remaining inclusion; the equivalence
  `PairOnU U ≃ A/(∏U)` is what is built Sorry-free below.

  Morphisms of `PairOnU U` are plain `PairHom`s (the subcategory is FULL), so the category structure
  is inherited from `pairsCat`. -/

section FixedU

variable (U : List 𝒞)

/-- **§1.547 — `A*|U` on the nose: the full subcategory of `Â` on objects with `F° = U`.**  An
    object bundles a `PairObj` together with a proof that its target list is exactly `U` (in order),
    so it sits over the common base `∏U`.  Morphisms are inherited from `pairsCat` (the subcategory
    is FULL: a `PairOnU`-map is just a `PairHom` of the underlying objects). -/
public structure PairOnU where
  obj : PairObj 𝒞
  htgt : obj.targets = U

/-- Homs of `PairOnU U` are the `PairHom`s of underlying objects (full subcategory). -/
@[expose] public instance : Cat.{u} (PairOnU U) where
  Hom X Y := PairHom X.obj Y.obj
  id X := PairHom.id X.obj
  comp f g := f.comp g
  id_comp f := PairHom.ext (Cat.id_comp f.g)
  comp_id f := PairHom.ext (Cat.comp_id f.g)
  assoc f g h := PairHom.ext (Cat.assoc f.g g.g h.g)

/-- **The object map `A*|U → A/(∏U)`.**  `X = ⟨(A,F), F° = U⟩ ↦ ⟨A, factorMap : A → ∏U⟩`.  This is
    `pairSliceObj` of the underlying object, whose base `∏(F°)` is rewritten to `∏U` along `X.htgt`.
    Concretely `⟨X.obj.A, X.htgt ▸ pairFactorMap X.obj⟩ : Over (listProd U)`. -/
@[expose] public def pairOnUSlice {U : List 𝒞} (X : PairOnU U) : Over (listProd U) :=
  ⟨X.obj.A, pairFactorMap X.obj ≫ eqToHom (congrArg listProd X.htgt)⟩

@[simp] theorem pairOnUSlice_hom {U : List 𝒞} (X : PairOnU U) :
    (pairOnUSlice X).hom = pairFactorMap X.obj ≫ eqToHom (congrArg listProd X.htgt) := rfl

@[simp] theorem pairOnUSlice_dom {U : List 𝒞} (X : PairOnU U) :
    (pairOnUSlice X).dom = X.obj.A := rfl

/-- **The factor map is FIXED by the self base-restriction.**  `pairFactorMap X` post-composed with
    `listProdRestrict X° X°` (the §1.547 base projection of `∏X°` onto itself) is `pairFactorMap X`
    again.  Projection-extensionality: at coordinate `k`, the LHS is `factorTuple X.F ≫ findProj
    (X°.get k) X°` = some factor `f` of target `X°.get k` (`factorTuple_findProj`), the RHS is the
    positional factor `X.F.get k'` of the same target (`factorTuple_proj`); `X.distinct` pins them
    equal.  (This is exactly why `listProdRestrict U U` acts as the identity on factor maps even when
    `U` has repeated targets — the decidable search may pick a different coordinate, but distinctness
    makes all coordinates of a given target carry the same arrow.) -/
public theorem pairFactorMap_restrict_self [HasPullbacks 𝒞] (X : PairObj 𝒞)
    (h : ∀ T ∈ X.targets, T ∈ X.targets) :
    pairFactorMap X ≫ listProdRestrict X.targets X.targets h = pairFactorMap X := by
  apply listProd_hom_ext X.targets
  intro k
  rw [Cat.assoc, listProdRestrict_proj X.targets X.targets h k]
  -- RHS coordinate: factor map ≫ proj_k = (X.F.get k').2 (positional)
  have hk' : k.1 < X.F.length := by simpa [PairObj.targets] using k.2
  have htgt : X.targets.get k = (X.F.get ⟨k.1, hk'⟩).1 := by
    simp only [PairObj.targets, List.get_eq_getElem, List.getElem_map]
  rw [show k = ⟨k.1, k.2⟩ from rfl, pairFactorMap_proj X k.1 k.2 hk' htgt]
  -- LHS coordinate: factor map ≫ findProj = (f).2 for some X-factor f of target X°.get k
  obtain ⟨f, hf, hfh, hfe⟩ := factorTuple_findProj (X.targets.get k) X.F
    ⟨X.targets.get k, h _ (List.get_mem _ _), rfl⟩
  rw [(show pairFactorMap X = factorTuple X.F from rfl),
      show findProj (X.targets.get k) X.targets ⟨X.targets.get k, h _ (List.get_mem _ _), rfl⟩
          = findProj (X.targets.get k) (X.F.map (·.1)) _ from rfl, hfe]
  -- both factors target X°.get k; X.distinct pins their arrows equal
  have hqf : f.1 = (X.F.get ⟨k.1, hk'⟩).1 := hfh.trans htgt
  have hqf2 : hqf ▸ f.2 = (X.F.get ⟨k.1, hk'⟩).2 :=
    X.distinct f hf (X.F.get ⟨k.1, hk'⟩) (List.get_mem _ _) hqf
  clear hfe hf h
  revert hfh htgt hqf hqf2
  obtain ⟨fT, fa⟩ := f
  generalize X.F.get ⟨k.1, hk'⟩ = yp
  obtain ⟨yT, ya⟩ := yp
  generalize X.targets.get k = T
  intro htgt hfh hqf hqf2
  simp only at htgt hfh hqf hqf2 ⊢
  subst hfh; subst htgt; exact hqf2

/-- **Self base-restriction as `eqToHom`, under the factor map.**  When the target list `l` equals
    `Xo.targets`, `pairFactorMap Xo ≫ listProdRestrict Xo.targets l h` is `pairFactorMap Xo ≫
    eqToHom`.  `l` is a free variable, so `cases e` reduces this to `pairFactorMap_restrict_self`. -/
public theorem pairFactorMap_restrict_eqToHom [HasPullbacks 𝒞] (Xo : PairObj 𝒞) (l : List 𝒞)
    (h : ∀ T ∈ l, T ∈ Xo.targets) (e : Xo.targets = l) :
    pairFactorMap Xo ≫ listProdRestrict Xo.targets l h
      = pairFactorMap Xo ≫ eqToHom (congrArg listProd e) := by
  cases e
  rw [pairFactorMap_restrict_self Xo h, eqToHom_refl, Cat.comp_id]

/-- The morphism map: a `PairOnU`-hom `m` (a `PairHom X.obj → Y.obj`) gives the slice triangle
    `m.g ≫ (pairOnUSlice Y).hom = (pairOnUSlice X).hom`.  After `subst`ing both `htgt` proofs, this
    is `pairHom_commutes_restrict` plus `pairFactorMap_restrict_self` (both targets are `U`, so the
    base restriction is the identity on factor maps). -/
@[expose] public def pairOnUSliceMap [HasPullbacks 𝒞] {U : List 𝒞} {X Y : PairOnU U} (m : PairHom X.obj Y.obj) :
    OverHom (pairOnUSlice X) (pairOnUSlice Y) :=
  ⟨m.g, by
    simp only [pairOnUSlice_hom]
    -- LHS: m.g ≫ pairFactorMap Y.obj ≫ eqToHom Y.htgt.  Re-associate, apply `pairHom_commutes_restrict`,
    -- collapse the base restriction via `restrict_eqToHom`, fuse the two `eqToHom`s.
    rw [show m.g ≫ pairFactorMap Y.obj ≫ eqToHom (congrArg listProd Y.htgt)
          = (m.g ≫ pairFactorMap Y.obj) ≫ eqToHom (congrArg listProd Y.htgt) from (Cat.assoc _ _ _).symm,
       pairHom_commutes_restrict m,
       show pairFactorMap X.obj ≫ listProdRestrict X.obj.targets Y.obj.targets (pairHom_targets_subset m)
            = pairFactorMap X.obj ≫ eqToHom (congrArg listProd (X.htgt.trans Y.htgt.symm)) from
         pairFactorMap_restrict_eqToHom X.obj Y.obj.targets _ (X.htgt.trans Y.htgt.symm),
       Cat.assoc, eqToHom_trans]
    -- both sides now `pairFactorMap X.obj ≫ eqToHom (·)`; the two equalities `X° = U` coincide (proof
    -- irrelevance), so `eqToHom_trans` already closed the goal.
    ⟩

/-- **§1.547 — the functor `Φ : A*|U → A/(∏U)`.**  Objects `↦ pairOnUSlice` (the factor-slice over
    the common base `∏U`); morphisms `↦ pairOnUSliceMap` (the underlying arrow `m.g`, the slice
    triangle from the bridge).  Functoriality is `OverHom.ext` on underlying arrows (`id ↦ id`,
    `m.g₁ ≫ m.g₂ ↦ (m₁ ≫ m₂).g`). -/
@[expose] public def pairOnUToSlice [HasPullbacks 𝒞] {U : List 𝒞} :
    Functor (PairOnU U) (Over (listProd U)) where
  obj X := pairOnUSlice X
  map (m : PairHom _ _) := pairOnUSliceMap m
  map_id _X := OverHom.ext rfl
  map_comp _m _n := OverHom.ext rfl

@[simp] theorem pairOnUToSlice_map_f [HasPullbacks 𝒞] {U : List 𝒞} {X Y : PairOnU U}
    (m : PairHom X.obj Y.obj) :
    ((pairOnUToSlice (U := U)).map m : OverHom (pairOnUSlice X) (pairOnUSlice Y)).f = m.g := rfl

/-! ### The functor `Φ` is an `EquivalenceFunctor` (fully faithful + essentially surjective)

  `Embedding Φ`: `Φ` is injective on homs (a `PairOnU`-map is its underlying `.g`, recovered as the
  slice map's `.f`).  `Full Φ`: every slice map `φ : pairOnUSlice X → pairOnUSlice Y` is `Φ` of a
  `PairHom` — exactly the bridge fullness `pairHomOfSlice` (the slice triangle over `∏U` re-presents
  the reindexed commuting square the bridge needs).  `HasRepresentativeImage Φ`: every slice object
  `⟨A, h : A → ∏U⟩` is iso to `Φ` of the padded pair `(A, {h ≫ proj_k})` (Freyd's padding). -/

/-- **`Φ : A*|U → A/(∏U)` is an `Embedding`** (injective on homs).  A `PairOnU`-hom is determined by
    its underlying `𝒞`-arrow `m.g`, which is `Φ.map`'s `.f`; equality of `.f` gives equality of `m`
    by `PairHom.ext`. -/
public theorem pairOnUToSlice_embedding [HasPullbacks 𝒞] (U : List 𝒞) :
    Embedding (pairOnUToSlice (U := U)) := by
  intro X Y m₁ m₂ h
  exact PairHom.ext (congrArg OverHom.f h)

/-- For `X Y : PairOnU U`, `Y°` is a subset of `X°` (both equal `U`).  The bridge's `hsub`. -/
public theorem pairOnU_targets_sub {U : List 𝒞} (X Y : PairOnU U) :
    ∀ T ∈ Y.obj.targets, T ∈ X.obj.targets := by
  intro T hT; rw [X.htgt]; rw [Y.htgt] at hT; exact hT

/-- **The slice triangle over `∏U` re-presents the reindexed bridge square.**  Given a slice map
    `φ : pairOnUSlice X → pairOnUSlice Y` over `∏U` (triangle `φ.f ≫ pairFactorMap Y ≫ eqToHom hY =
    pairFactorMap X ≫ eqToHom hX`), the underlying `φ.f` satisfies the bridge's reindexed commuting
    square `φ.f ≫ pairFactorMap Y.obj = pairFactorMap X.obj ≫ listProdRestrict X° Y° hsub`.  Proof:
    cancel the (iso) `eqToHom hY` on the right, fuse `eqToHom hX ≫ eqToHom hY⁻¹ = eqToHom (X°=Y°)`,
    and apply `pairFactorMap_restrict_eqToHom` to turn that into the base restriction. -/
public theorem pairOnUSlice_triangle_to_bridge [HasPullbacks 𝒞] {U : List 𝒞} {X Y : PairOnU U}
    (φ : OverHom (pairOnUSlice X) (pairOnUSlice Y)) :
    φ.f ≫ pairFactorMap Y.obj
      = pairFactorMap X.obj
          ≫ listProdRestrict X.obj.targets Y.obj.targets (pairOnU_targets_sub X Y) := by
  have hw : φ.f ≫ (pairFactorMap Y.obj ≫ eqToHom (congrArg listProd Y.htgt))
      = pairFactorMap X.obj ≫ eqToHom (congrArg listProd X.htgt) := by
    have := φ.w; simpa [pairOnUSlice_hom] using this
  -- right-cancel the iso `eqToHom (congrArg listProd Y.htgt)` from `hw`
  have hiso : φ.f ≫ pairFactorMap Y.obj
      = pairFactorMap X.obj ≫ eqToHom (congrArg listProd (X.htgt.trans Y.htgt.symm)) := by
    have h2 := congrArg (· ≫ eqToHom (congrArg listProd Y.htgt).symm) hw
    -- LHS: cancel `eqToHom hY ≫ eqToHom hY.symm = id`; RHS: fuse the two `eqToHom`s.
    simp only [Cat.assoc] at h2
    rw [eqToHom_comp_eqToHom_symm, Cat.comp_id, eqToHom_trans] at h2
    exact h2
  rw [hiso, ← pairFactorMap_restrict_eqToHom X.obj Y.obj.targets _ (X.htgt.trans Y.htgt.symm)]

/-- **`Φ : A*|U → A/(∏U)` is FULL.**  Every slice map `φ : pairOnUSlice X → pairOnUSlice Y` is `Φ`
    of a `PairHom`.  The bridge fullness `pairHomOfSlice` builds that `PairHom` from the reindexed
    square `pairOnUSlice_triangle_to_bridge`; its underlying `.g` is `φ.f`, so `Φ.map` of it is `φ`
    (`OverHom.ext`). -/
public theorem pairOnUToSlice_full [HasPullbacks 𝒞] (U : List 𝒞) :
    Full (pairOnUToSlice (U := U)) := by
  intro X Y φ
  refine ⟨pairHomOfSlice (pairOnU_targets_sub X Y) ⟨φ.f, ?_⟩, OverHom.ext rfl⟩
  show φ.f ≫ (pairSliceObj Y.obj).hom
      = pairFactorMap X.obj ≫ listProdRestrict X.obj.targets Y.obj.targets (pairOnU_targets_sub X Y)
  rw [pairSliceObj_hom]
  exact pairOnUSlice_triangle_to_bridge φ

/-! ### Essential surjectivity (Freyd's padding)

  Every slice object `⟨A, h : A → ∏U⟩` is `pairOnUSlice` of a padded pair `(A, F)` with `F° = U`:
  take `F` to record, for each coordinate of `∏U`, the component `h ≫ projₖ` of `h`.  Built by
  recursion on `U` (decomposing `∏(T::U) = T × ∏U` via `fst`/`snd`), so `F° = U` definitionally and
  `factorTuple F = h` by the product eta law (`pair_uniq _ _ h rfl rfl`).  Well-supportedness of
  the factors needs each `T ∈ U` well supported; the `distinct` field needs `U` to have NO
  repeated target (`U.Nodup`) — otherwise two
  coordinates of `∏U` with the same target carry the (possibly different) components `h ≫ projₖ`,
  which `PairObj.distinct` would force equal.  (For a SET `U` of well-supported objects, exactly
  Freyd's hypothesis, both hold.) -/

/-- The padding factor list of `h : A → ∏U`: the components `h ≫ projₖ`, one per coordinate of
    `∏U`, recursing through `∏(T::U) = T × ∏U`.  `targets = U` definitionally; `factorTuple = h`. -/
@[expose] public def padFactors : ∀ (U : List 𝒞) {A : 𝒞}, (A ⟶ listProd U) → List (Σ T : 𝒞, A ⟶ T)
  | [],     _, _ => []
  | T :: U, _, h => ⟨T, h ≫ (fst : prod T (listProd U) ⟶ T)⟩
                      :: padFactors U (h ≫ (snd : prod T (listProd U) ⟶ listProd U))

/-- The padding factor list's targets are exactly `U`. -/
public theorem padFactors_targets : ∀ (U : List 𝒞) {A : 𝒞} (h : A ⟶ listProd U),
    (padFactors U h).map (·.1) = U
  | [],     _, _ => rfl
  | T :: U, _, h =>
      congrArg (T :: ·) (padFactors_targets U (h ≫ (snd : prod T (listProd U) ⟶ listProd U)))

/-- `eqToHom` along a `listProd` of a `T :: ·` congruence splits as `pair fst (snd ≫ eqToHom)`.
    Proof: `cases` the list equality `e₀` (its LHS `l` is free), then both sides are `id` /
    `pair fst snd`. -/
public theorem eqToHom_listProd_cons {T : 𝒞} {l : List 𝒞} {U : List 𝒞} (e₀ : l = U) :
    eqToHom (congrArg listProd (congrArg (T :: ·) e₀))
      = pair (fst : prod T (listProd l) ⟶ T) (snd ≫ eqToHom (congrArg listProd e₀)) := by
  cases e₀; simp only [eqToHom_refl, Cat.comp_id]; exact pair_fst_snd.symm

/-- The padding factor list reconstructs `h`: composing `factorTuple (padFactors U h)` with the
    `eqToHom` re-typing its codomain `∏((padFactors U h)°)` to `∏U` recovers `h`.  By the product
    eta law: each step is `pair (h≫fst) (h≫snd) = h`. -/
public theorem padFactors_factorTuple : ∀ (U : List 𝒞) {A : 𝒞} (h : A ⟶ listProd U),
    factorTuple (padFactors U h) ≫ eqToHom (congrArg listProd (padFactors_targets U h)) = h
  | [],     _, h => by
      simp only [padFactors, factorTuple_nil]
      exact (HasTerminal.uniq _ _)
  | T :: U, _, h => by
      -- `factorTuple (padFactors (T::U) h) = pair (h≫fst) (factorTuple (padFactors U (h≫snd)))`.
      -- The codomain re-typing splits as `prod T (eqToHom …)`; `pair`-functoriality + IH + eta law.
      show (pair (h ≫ fst) (factorTuple (padFactors U (h ≫ snd))))
            ≫ eqToHom (congrArg listProd (padFactors_targets (T :: U) h)) = h
      have hsub := padFactors_factorTuple U (h ≫ (snd : prod T (listProd U) ⟶ listProd U))
      -- the `T::U` re-typing is `pair fst (snd ≫ (U re-typing))` (`eqToHom_listProd_cons`); the
      -- equality `padFactors_targets (T::U) h` is defeq to `congrArg (T::·) (…U…)`.
      rw [show (eqToHom (congrArg listProd (padFactors_targets (T :: U) h))
              : prod T (listProd ((padFactors U (h ≫ snd)).map (·.1))) ⟶ listProd (T :: U))
            = pair (fst : prod T (listProd ((padFactors U (h ≫ snd)).map (·.1))) ⟶ T)
                (snd ≫ eqToHom (congrArg listProd (padFactors_targets U (h ≫ snd)))) from
          eqToHom_listProd_cons (padFactors_targets U (h ≫ snd))]
      -- project both sides: fst gives `h≫fst`, snd gives `FT ≫ e = h≫snd` (IH); conclude by the eta law.
      have hfst : (pair (h ≫ fst) (factorTuple (padFactors U (h ≫ snd)))
          ≫ pair (fst : prod T (listProd ((padFactors U (h ≫ snd)).map (·.1))) ⟶ T)
              (snd ≫ eqToHom (congrArg listProd (padFactors_targets U (h ≫ snd))))) ≫ fst
          = h ≫ fst := by rw [Cat.assoc, fst_pair, fst_pair]
      have hsnd : (pair (h ≫ fst) (factorTuple (padFactors U (h ≫ snd)))
          ≫ pair (fst : prod T (listProd ((padFactors U (h ≫ snd)).map (·.1))) ⟶ T)
              (snd ≫ eqToHom (congrArg listProd (padFactors_targets U (h ≫ snd))))) ≫ snd
          = h ≫ snd := by rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, hsub]
      rw [pair_uniq _ _ (pair (h ≫ fst) (factorTuple (padFactors U (h ≫ snd))) ≫ _) rfl rfl,
        hfst, hsnd, ← pair_uniq _ _ h rfl rfl]

/-- A member of `padFactors U h` has its target IN `U` (its factors record `U`'s coordinates). -/
public theorem padFactors_mem_target {U : List 𝒞} {A : 𝒞} (h : A ⟶ listProd U)
    {r : Σ T : 𝒞, A ⟶ T} (hr : r ∈ padFactors U h) : r.1 ∈ U := by
  have : r.1 ∈ (padFactors U h).map (·.1) := List.mem_map.2 ⟨r, hr, rfl⟩
  rwa [padFactors_targets] at this

/-- **The padding factor list is `distinct`** (under `U.Nodup`): two factors of the same target are
    equal.  By induction on `U`: a head factor `⟨T, h≫fst⟩` and a tail factor (target `∈ U`) cannot
    share a target (`T ∉ U` by `Nodup`); two tail factors are handled by the IH. -/
public theorem padFactors_distinct : ∀ (U : List 𝒞), U.Nodup → ∀ {A : 𝒞} (h : A ⟶ listProd U)
    (r : Σ T : 𝒞, A ⟶ T), r ∈ padFactors U h → ∀ (r' : Σ T : 𝒞, A ⟶ T), r' ∈ padFactors U h →
    ∀ (heq : r.1 = r'.1), heq ▸ r.2 = r'.2
  | [], _, _, _, _, hr, _, _, _ => absurd hr (by simp [padFactors])
  | T :: U, hnd, _, h, r, hr, r', hr', heq => by
      rw [List.nodup_cons] at hnd
      simp only [padFactors, List.mem_cons] at hr hr'
      rcases hr with rfl | hr <;> rcases hr' with rfl | hr'
      · -- both the head factor
        cases heq; rfl
      · -- r = head (target T), r' tail (target ∈ U): T ∈ U, contradiction
        dsimp only at heq
        exact absurd (show T ∈ U by rw [heq]; exact padFactors_mem_target (h ≫ snd) hr') hnd.1
      · -- symmetric: r tail, r' head (target T)
        dsimp only at heq
        exact absurd (show T ∈ U by rw [← heq]; exact padFactors_mem_target (h ≫ snd) hr) hnd.1
      · -- both tail: IH
        exact padFactors_distinct U hnd.2 (h ≫ snd) r hr r' hr' heq

/-- **The padded `PairObj` over the base `∏U`** (needs each `T ∈ U` well-supported and `U.Nodup`). -/
@[expose] public def padPairObj (U : List 𝒞) (hws : ∀ T ∈ U, WellSupported T) (hnd : U.Nodup)
    {A : 𝒞} (h : A ⟶ listProd U) : PairOnU U where
  obj :=
    { A := A
      F := padFactors U h
      wsupp := fun p hp => hws p.1 (padFactors_mem_target h hp)
      distinct := fun r hr r' hr' heq => padFactors_distinct U hnd h r hr r' hr' heq }
  htgt := padFactors_targets U h

/-- **The padded pair recovers the slice object on the nose.**  `pairOnUSlice (padPairObj U _ _ h)`
    is literally `⟨A, h⟩`: its structure map is `factorTuple (padFactors U h) ≫ eqToHom = h`
    (`padFactors_factorTuple`).  So no nontrivial iso is needed — the representative is exact. -/
public theorem pairOnUSlice_padPairObj [HasPullbacks 𝒞] (U : List 𝒞) (hws : ∀ T ∈ U, WellSupported T)
    (hnd : U.Nodup) {A : 𝒞} (h : A ⟶ listProd U) :
    pairOnUSlice (padPairObj U hws hnd h) = (⟨A, h⟩ : Over (listProd U)) := by
  show (⟨A, factorTuple (padFactors U h) ≫ eqToHom (congrArg listProd (padFactors_targets U h))⟩
        : Over (listProd U)) = ⟨A, h⟩
  rw [padFactors_factorTuple]

/-- **§1.547 — `Φ : A*|U → A/(∏U)` is essentially surjective** (has a representative image): for a
    SET `U` of well-supported objects (`U.Nodup`, each `T ∈ U` well-supported), every slice object
    `Z : Over (∏U)` is `Φ` of a `PairOnU`-object (the padded `padPairObj` of `Z.hom`), and in fact
    EQUAL to it (`pairOnUSlice_padPairObj`), so the witnessing iso is the identity. -/
public theorem pairOnUToSlice_representativeImage [HasPullbacks 𝒞] (U : List 𝒞)
    (hws : ∀ T ∈ U, WellSupported T) (hnd : U.Nodup) :
    HasRepresentativeImage (pairOnUToSlice (U := U)) := by
  intro Z
  have heq : pairOnUSlice (padPairObj U hws hnd Z.hom) = Z := by
    rw [pairOnUSlice_padPairObj]
  exact ⟨padPairObj U hws hnd Z.hom, eqToHom heq,
    ⟨eqToHom heq.symm, eqToHom_comp_eqToHom_symm _, eqToHom_symm_comp_eqToHom _⟩⟩

/-- **§1.547 — the fixed-`U` slice equivalence `A*|U ≃ A/(∏U)`.**  For a SET `U` of well-supported
    objects (`U.Nodup`, each well-supported), the factor-slice functor `Φ : A*|U → A/(∏U)` is an
    `EquivalenceFunctor` (an embedding, full, with representative image — i.e. fully faithful and
    essentially surjective).  This is Freyd §1.547 (lines 4958-4961) at a FIXED base, packaging the
    Sorry-free bridge `pairHomToSlice`/`pairHomOfSlice` plus the padding `padPairObj`. -/
public theorem pairOnUToSlice_equivalence [HasPullbacks 𝒞] (U : List 𝒞)
    (hws : ∀ T ∈ U, WellSupported T) (hnd : U.Nodup) :
    EquivalenceFunctor (pairOnUToSlice (U := U)) :=
  ⟨pairOnUToSlice_embedding U, pairOnUToSlice_full U,
   pairOnUToSlice_representativeImage U hws hnd⟩

end FixedU

end Freyd

