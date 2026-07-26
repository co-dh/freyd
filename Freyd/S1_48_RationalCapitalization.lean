/-
  Freyd & Scedrov, *Categories and Allegories* §1.48 / §1.547
  THE RATIONAL CATEGORY `A[𝒟⁻¹]` AS A CALCULUS-OF-FRACTIONS CATEGORY,
  and the CHOICE-FREE relative capitalization `A ⊆ A*` of §1.547.

  ── WHY THIS FILE EXISTS (milestone R1) ────────────────────────────────────────

  The transfinite §1.546 capitalization (`CapitalizationTransfinite.lean`) and the
  ω-tower §1.544/§1.545 successor (`Capitalization.lean`, `RelativeCapitalization.lean`)
  both model `A*` as a *directed colimit of slice categories* — a `Colim.CatSystem`.
  That framework demands the directed transitions be **strictly** functorial
  (`CatSystem.F_refl : F (refl) X = X` and `F_trans` on the nose, CatColimit.lean:33).
  The §1.547 transition `A/(∏V) → A/(∏U)` for `V ⊆ U` is BASE-CHANGE (the pullback that
  grows the embedding domain `B×∏V ↝ B×∏U`); base-change is only *pseudo*-functorial,
  so `CatSystem.F_refl`/`F_trans` are FALSE for it (machine-checked, documented at
  `RelativeCapitalization.lean` `StrictBaseChange`/ROUTE-1).  Hence the slice-colimit
  model of `A*` hits a strictness wall, NOT sidestepped by §1.547.

  This file takes the OTHER route the book actually uses (§1.48, and which §1.547 cites):
  build the rational category `A[𝒟⁻¹]` **directly** as a calculus-of-fractions category —
  same objects as `A`; a morphism `A → B` is an equivalence class of spans
  `A ←[denom ∈ 𝒟]— • —num→ B`; composition by pullback.  There is NO directed colimit
  and hence NO transition-strictness obligation: the rational category is a *single*
  `Cat` built by quotienting each hom-set.  This is exactly why §1.547 phrases the
  inter-slice transitions as equivalences (up-to-iso) yet still gets a genuine category.

  ── WHAT THIS FILE DELIVERS ────────────────────────────────────────────────────

  The §1.48 scaffolding (`DenseClass`/`Fraction`/`FractionEquiv`/`RationalCategory`)
  already lives in `S1_47.lean` as DEFINITIONS + a universal-property record, but the
  actual category (composition by pullback, well-definedness, the `Cat` instance) was
  never built.  Here:

    * `denseMonos 𝒞`          — SORRY-FREE (`propext` only).  The dense class of ALL
                                monics (closed under iso/comp/pb; §1.48(i)-(iii) from
                                `mono_pullback`).  The working dense class for `A[𝒟⁻¹]`.
    * `FractionEquiv` EQUIVALENCE RELATION — SORRY-FREE over `denseMonos 𝒞`.  Reflexivity,
                                symmetry, AND transitivity all proven; transitivity closes
                                via the pullback-roof whose dense leg is monic because
                                `r₁`,`s₂` are mono left-factors and pullbacks of monics are
                                monic (`mono_of_comp_mono`/`mono_pullback`/`mono_comp'`).
    * `RatHom A B`/`ratId`/`locMap` — SORRY-FREE (`propext`).  `Quotient (fractionSetoid …)`,
                                the hom-set of `A[𝒟⁻¹]`; identity span; localisation of an
                                ordinary arrow.
    * `compFraction`         — SORRY-FREE.  The composite span by pullback of `(num₁,denom₂)`,
                                with its denominator dense by pb+comp closure.
    * `ratComp`              — SORRY-FREE (milestone R2).  Composition on equivalence classes;
                                the `Quotient.lift₂` WELL-DEFINEDNESS (independence of names +
                                pullback choice, §1.48) is discharged by the two single-span
                                congruences `compFraction_congr_left`/`_right` (each a single
                                pullback roof) glued by `fractionEquiv_trans`.  Axioms: `propext`,
                                `Quot.sound`.
    * `compFraction_idFraction_left/right`, `compFraction_assoc` — SORRY-FREE (R2).  Unit and
                                associativity laws of `compFraction` up to `FractionEquiv`.
    * `Rat 𝒞` / `ratCat`     — SORRY-FREE (R2).  The rational category `A[denseMonos⁻¹]` as a
                                genuine `Cat` (objects = a structure wrapper of `𝒞`'s objects so
                                its `Cat` instance does not collapse onto `𝒞`'s; homs = `RatHom`;
                                comp = `ratComp`; the three laws lifted from `compFraction`).
    * `locFunctor`           — SORRY-FREE (R2).  The localisation functor `T_𝒟 : 𝒞 → A[denseMonos⁻¹]`
                                (identity on objects, `f ↦ locMap f`); `map_id` definitional,
                                `map_comp` via `locMap_comp_equiv` (pullback-against-identity roof).
    * FAITHFULNESS FINDING (R2, machine-checked) — at the ALL-MONICS class, `T_𝒟` is NEITHER an
                                `Embedding` (left-cancelling a dense MONIC roof leg would need it
                                EPIC) NOR conservative (it inverts every monic).  So the repo's
                                `Faithful` — hence `CapStep.stepFaithful`, hence a genuine
                                `ratCap S : CapStep S` with `step = T_𝒟` — is GATED on §1.547's
                                dense-class refinement (invert only the slice-embedding monics).
                                No `ratCap` is asserted here: doing so at this class would require
                                faking `stepFaithful`, which the integrity rules forbid.  See the
                                "§1.547 FAITHFULNESS FINDING" block at the localisation section.
    * Cartesian / pre-regular `PreRegularCategory (Rat 𝒞)` — NOT built in R2.  Transporting
                                finite limits + covers through `T_𝒟` is a large separate effort
                                and, per the faithfulness finding, would still not yield `ratCap`
                                without the refined class; left for R3 rather than stubbed.
    * `ratStep_points_every_factor` / `slice_factor_point_acquired` — SORRY-FREE.  The §1.547
                                per-step PAYOFF: the product-slice `A/(∏U)` carries a global
                                point of every factor (re-exposed `listProdSliceAcquiresEvery
                                Factor`).
    * `sliceEmbed_factor_wellPointed` — the §1.547 well-pointedness CORE, stated with the
                                slice's genuine `HasTerminal` (overHasTerminal) — NO Sorry in
                                the type, so it is the book's real `WellPointed`.  The descent
                                of an arbitrary subobject to the downstairs proper `B'` and the
                                missed-point extraction is the isolated `Sorry`.

  ── MILESTONE R3 (§1.547 pairs category + refined dense class + FAITHFULNESS) ──────

    * `PairObj`/`PairHom`/`pairsCat` — the §1.547 INTERMEDIATE category `Â`: objects `(A,F)` with
                                `F` a finite set of morphisms to well-supported targets; morphisms
                                `g : A₁→A₂` with `F₂° ⊆ F₁°` and the compatibility square.  A
                                genuine `Cat`, SORRY-FREE, NO axioms (homs determined by `g`).
    * `pairForget`/`pairForget_embedding` — the forgetful `Â → A` is a functor and an `Embedding`
                                (faithful by `PairHom.ext`).  SORRY-FREE, NO axioms.
    * `PairDense` — the §1.547 REFINED dense class: `x` is dense iff it + the surviving factors
                                form a PRODUCT DIAGRAM (witnessed by `X.A ≅ Y.A × W`, `W` the
                                well-supported product of surviving targets, `x.g = fst`).
    * `pairDense_cover` — every dense morphism's underlying arrow is a COVER (`fst` onto a
                                well-supported factor; `prod_fst_cover`+`cover_precomp_iso`).
                                SORRY-FREE, NO axioms.  This is the cancellability R2 lacked.
    * `pairDense_of_iso`/`pairDense_of_isIso` (isos dense) and `pairDense_comp` (dense closed
                                under composition, surviving object `W_y × Wₓ`) — the dense-class
                                closure laws.  SORRY-FREE, NO axioms (choice-free).
    * `pairDense_epi` / **`pairLocalisation_faithful_criterion`** — THE DECISIVE R3 RESULT:
                                dense morphisms are EPIC in `Â` (their underlying cover is epic,
                                `cover_epi`), so two parallel `Â`-arrows identified by a common
                                DENSE roof are equal — this IS the FAITHFULNESS of the §1.547
                                localisation `Â → Â[dense⁻¹] = A*`.  SORRY-FREE, NO axioms,
                                choice-free.  R2's all-monics route FAILED exactly here (a monic
                                roof leg is not epic); §1.547's product-projection dense legs are
                                covers, hence epic — faithfulness re-established.

  ── MILESTONE R4 (§1.547 `Â` IS CARTESIAN — terminal + binary products, Sorry-free) ──────────────

    * `WideEq`/`wideEqNil`/`wideEqCons`/`wideEq` — the reusable WIDE EQUALIZER of a finite LIST of
                                parallel pairs over `X`: the maximal subobject `w : D ↪ X`
                                equalizing all listed pairs, universal.  Built by iterated binary
                                equalizer (`products_pullbacks_implies_equalizers`).  This is the
                                `D ↪ A₁×A₂` kernel of Freyd's §1.547 product formula.  SORRY-FREE,
                                choice-free (`propext`,`Quot.sound`).
    * `pairHasTerminal` — `Â` HAS A TERMINAL OBJECT `(1,∅)` (terminator of `A`, no factors); the
                                unique arrow is `term`, unique by `term_uniq`.  SORRY-FREE, NO axioms.
    * `crossConstraints`/`pairProdD`/`pairProdW`/`pairProdK`/`pairProdObj` — the §1.547 PRODUCT
                                OBJECT `(A₁,F₁)×(A₂,F₂) = (D,K)`: `D = wideEq` of the cross
                                constraints `(fst≫f, snd≫f')` for matched factors `f∈F₁`,`f'∈F₂`
                                (`f°=f'°`, decided by `DecidableEq 𝒞` = Freyd's "equal targets"),
                                `w : D ↪ A₁×A₂`, `K = {w≫h | h∈H}`.  Projections `pairProjFst/Snd`.
                                SORRY-FREE, choice-free.
    * `pairProd_hom_ext` — UNIQUENESS of the product pairing (unconditional): agreement after both
                                projections + `w` monic + joint monicity ⟹ equality.  SORRY-FREE.
    * `pairPair`/`pairPair_fst`/`pairPair_snd`/`pairProd_lift` — EXISTENCE of the pairing (data,
                                choice-free) under the book's target-distinctness `Z.DistinctTargets`.
    * `PairTargetsDistinct` + `pairHasBinaryProducts` — `Â` HAS BINARY PRODUCTS, under the book's
                                STANDING ASSUMPTION (`PairTargetsDistinct 𝒞`: every object of `Â`
                                has factors to DISTINCT targets — Freyd builds this into objects of
                                `Â`; R3's `PairObj` recorded only well-supportedness, so it is made
                                an explicit class here, NOT a weakening).  SORRY-FREE, choice-free.

  THE DISTINCTNESS GATE — RESOLVED (R5).  Freyd's §1.547 objects of `Â` carry factors to DISTINCT
  well-supported targets.  R5 adds distinctness as a FIELD of `PairObj` (`PairObj.distinct`), NOT a
  side class.  Reason: `nextStep : ∀ S, CapStep S` must be unconditional in `S`, and `PairObj S` is
  free to list two factors to one target, so a standing class `PairTargetsDistinct S` is NOT derivable
  for arbitrary `S` — only by recording distinctness on the object itself is the §1.547 product
  pairing total with no hypothesis.  Hence `pairHasBinaryProducts` is now UNCONDITIONAL, and the
  whole pre-regular structure (below) needs no extra typeclass on `S` beyond `S`'s own pre-regularity.

  ── MILESTONE R5 (§1.547 `Â` PRE-REGULAR + refined dense class; pullbacks/equalizers Sorry-free) ──

    * `pairHasEqualizers`/`pairHasPullbacks` — `Â` HAS EQUALIZERS and PULLBACKS, UNCONDITIONAL,
                                SORRY-FREE.  The equalizer of `a,b : (A,F)→(B,G)` is `(E, e^*F)` with
                                `e = eqMap a.g b.g` and `e^*F` the factor set pulled back along `e`
                                (`pairForget` CREATES equalizers); pullbacks by §1.432
                                (products+equalizers ⟹ pullbacks).
    * `pairCover_underlying` — SORRY-FREE.  An `Â`-cover has an `A`-cover underlying arrow: any
                                `A`-monic `m` factoring `f.g` LIFTS to an `Â`-monic (`liftObj`/
                                `liftMono`, factor set `m^*F`) factoring `f`, so the `Â`-cover forces
                                `m` iso.  Freyd's "`pairForget` preserves covers", forward half.
    * `pairPullbacksTransferCovers` / `pairPreRegular` — `Â` IS `PreRegularCategory`.  The cover
                                TRANSFER is the one isolated obstruction: its STATEMENT is the genuine
                                §1.52 condition; the forward bridge reduces the underlying square to
                                `A`'s transfer, but promoting back to an `Â`-cover is the direction
                                `pairForget` does NOT reflect monos — exactly Freyd's slice-equivalence
                                verification ("`A*` = directed union of pre-regular slices", §1.547 =
                                the directed-colimit route's strictness wall, R1).  ONE `Sorry`, true
                                statement, sharply documented.
    * `pairEmbed`/`pairEmbed_faithful` — SORRY-FREE.  The §1.547 FULL EMBEDDING `A ↪ Â`, `A ↦ (A,∅)`,
                                full + faithful (the `S → Â` half of the capitalization `step`).
    * `pairDenseClass : DenseClass (PairObj 𝒞)` — the refined §1.547 dense class packaged as the
                                record the §1.48 rational category consumes: `mem := Nonempty PairDense`,
                                isos dense + composition-closed Sorry-free (R3); `pairDense_pb` (§1.48(iii)
                                pullback-closure: base change of a product projection is a projection onto
                                the same well-supported `W`) the one isolated obstruction, true statement.

  ── MILESTONE R6/R7 (generic monic skeleton; EVERY DENSE MORPHISM IS MONIC IN `Â`) ────────────────

    * `MonicDense 𝒟` / `denseMonos_monic` / `MonicDense.leg_mono` — the calculus-of-fractions skeleton
                                GENERALISED.  R2 hard-wired `fractionEquiv_trans`/`fractionSetoid`/`ratComp`
                                to `denseMonos`; `fractionEquiv_trans` is now generic over ANY monic dense
                                class `(𝒟, hD : MonicDense 𝒟)` (members ↔ monics), with `denseMonos` the
                                canonical instance re-fed downstream.  Sorry-free (`propext`); `ratCat`
                                keeps its `propext`/`Quot.sound` profile.
    * `pairDense_monic` — **R7 KEYSTONE, machine-checked AXIOM-FREE.**  EVERY DENSE MORPHISM IS MONIC
                                IN `Â` (Freyd §1.547: "every dense morphism is monic").  The dense `x`'s
                                product-diagram form `X.A ≅ Y.A × W` with `x.g = fst` makes it monic-in-`Â`:
                                its `W`-component is PINNED by `X`'s factor data (`PairDense.survPinned` —
                                `W = ∏(surviving targets)`, each a factor of `X`, so any `Â`-map into `X`
                                agrees there by compatibility + distinctness).  The UNDERLYING `A`-arrow is
                                an epic cover (`pairDense_cover`), but `pairForget` does not reflect monos,
                                so monic-in-`Â` ≠ monic-in-`A` — no contradiction.  R6 mistook the former
                                for the latter ("monic/epic collapse", "need a dual co-span calculus");
                                that was a CATEGORY CONFUSION, now corrected.  `pairDenseClass_mem_mono`
                                packages `pairDenseClass` as a §1.48/§1.481 DENSE CLASS OF MONICS;
                                `pairDense_monic_and_epic` states both halves (monic + faithful-cancel).

  STILL OPEN (the `ratCap` spill, NOT faked).  `ratCap S : CapStep S` is NOT yet assembled.  With R7,
  `pairDenseClass` is correctly a dense class of MONICS, so the §1.48 monic LEFT-fraction skeleton is the
  right tool (no dual calculus).  What remains for a full Sorry-free instantiation: (a) DONE —
  `pairDense_pb` (§1.48(iii) dense pullback-closure) is now Sorry-free, its leg-density
  `pairDense_pb_canonical_dense` CLOSED (R11i, absorption iso); (b) the §1.48 calculus-of-fractions SATURATION of
  the transitivity roof rebuild for a PROPER monic class (the all-monics `MonicDense` rebuild uses
  `Monic → mem`, false for `pairDenseClass`; the standard §1.48 Ore argument is needed instead); (c)
  `pairPullbacksTransferCovers` (the `Â` cover transfer).  No fake `ratCap` is asserted.  The
  faithfulness obligation is already discharged (`pairLocalisation_faithful_criterion`/`pairDense_epi`);
  the embedding half is `pairEmbed_faithful`.

  ── INTEGRITY ──────────────────────────────────────────────────────────────────

  No `axiom`, no `: True`, no `Sorry` on a false statement, no `Sorry` in any STATEMENT/type.
  TWO `Sorry`s, each on the book's genuine statement, sharply documented: (1) `sliceEmbed_factor_wellPointed`
  (§1.547 well-pointedness — the naive over-general `genericPoint_escapes_proper` was FALSE and was
  REMOVED, see `graph_satisfies_hyps`); (2) `pairPullbacksTransferCovers` (the `Â` cover transfer =
  slice equivalence).
  CLOSED (R11i, Sorry-free + axiom-clean): `pairDense_pb_canonical_dense` (§1.48(iii) leg-density),
  via the explicit absorption iso `apexHom/apexInv` (`apex.A ≅ Z.A × W'`, collided survivors absorbed
  by `apex_cross`/`PairObj.distinct`).

  ── R9 (dense-pullback-closure: reduction done, residual sharply isolated) ──────────────────────

  `pairDense_pb` (§1.48(iii) `DenseClass.pb_mem` for `PairDense`) is now SORRY-FREE *modulo* a single
  isolated sub-lemma.  R9 split it:
    * `pairDense_pb_witness` — produces the genuine `Â`-pullback cone of the cospan `(g, x)` and proves
      `c.IsPullback` (both SORRY-FREE — the cone is the canonical `pairHasPullbacks` pullback).
    * `pairDense_pb` itself — SORRY-FREE: transports density across the canonical pullback.
    * `pairDense_pb_canonical_dense` — the ONLY residual `Sorry`: the first leg `canonical.π₁` is dense,
      i.e. the canonical `Â`-pullback apex is `≅ Z.A × dx.W` (base change of the product projection
      `fst` onto the SAME well-supported `W`), with `survPinned` discharged via `dx.survPinned` pulled
      back along `canonical.π₂`.  THE GAP (machine-verified, R9): the underlying `A`-object of the
      canonical `Â`-pullback is the wide-equalizer subobject `pairEqObj … (pairProdObj Z X)` of
      `Z.A × X.A`, and proving it `≅ Z.A × dx.W` is exactly "`pairForget` preserves this pullback" —
      Freyd's §1.547 slice-equivalence verification, the SAME content as `pairPullbacksTransferCovers`.
      From the abstract `PairObj`/`PairDense` data alone (which permits `Z` and `X` to record unrelated
      factors to a shared well-supported target) the cross-collision cannot be ruled out, so the naive
      `prod Z.A dx.W` apex with a union factor list is an ILLEGAL `PairObj` (its `distinct` reduces to
      an unprovable cross goal `fst≫f = π₂g≫f'`).  Not faked, not weakened — isolated honestly.

  `pairDense_monic` (the R7 keystone) is Sorry-free AND axiom-free.  The protected types of
  `capData_exists`/`CapData`/`CapStep` are not touched.  No fake `ratCap` (it spills to R10: the
  unconditional `CapStep S` assembly gates on (3) above + the §1.48 composition-congruence saturation
  + `PreRegularCategory A*` transport).

  ── R10 (slice-equivalence A-LEVEL CORE proven; the two §1.547 residuals confirmed identical) ──────

  R10 targeted the §1.547 slice-equivalence fact that R9 isolated as the shared content of BOTH
  `pairDense_pb_canonical_dense` AND `pairPullbacksTransferCovers`.  Result:

    * `projBaseChangeCone`/`projBaseChangeCone_isPullback` — SORRY-FREE, AXIOM-FREE.  The genuine
      `A`-level core: the pullback of a PRODUCT PROJECTION `fst : Y×W → Y` along any `g : Z → Y` is
      the projection `fst : Z×W → Z` (apex `Z×W`, `π₂ = pair (fst≫g) snd`).  Constructive, needs only
      binary products.  This is exactly the `A`-shape a dense `Â`-pullback descends to
      (`X.A ≅ Y.A × W`, `x.g = fst`), so it is the reusable honest core of both payoffs.

    * CONFIRMED (machine-checked reasoning, NOT faked): both residuals are the SAME gap.  With the
      `A`-level core in hand, each reduces to a single PRESERVATION/REFLECTION step for `pairForget`
      on this one pullback: the canonical `Â`-pullback apex `E` is the wide-equalizer of `Z.A × X.A`
      cutting BOTH the square `eq(fst≫g.g, snd≫x.g)` AND the product cross-constraints, whereas the
      EXPECTED `A`-pullback (`projBaseChangeCone`) cuts the square ONLY.  `pairForget` preserves this
      pullback ⟺ the cross-constraints add nothing ⟺ no two UNRELATED factors `f∈Z.F`, `f'∈X.F` of a
      common well-supported target collide.  Freyd's set-based ambient gives this; abstract `PairObj`
      data (which permits unrelated shared-target factors) does not.  So neither residual is derivable
      Sorry-free from the abstract data — this is genuinely Freyd's slice-equivalence verification,
      the directed-colimit route's strictness wall (R1) in a different guise.  Both docstrings now
      cite `projBaseChangeCone_isPullback` and the precise residual; both `Sorry`s carry the book's
      true statement, sharply documented.  Sorry count UNCHANGED at 3 (the two coincident slice-
      equivalence residuals + the R2 `sliceEmbed_factor_wellPointed`); the honest reduction — not a
      removal — is R10's contribution, since faking either would violate the integrity rule.

  mathlib-free; built on this repo's hand-built `Cat`.
-/

import Freyd.S1_45
import Freyd.S1_47
import Freyd.S1_52
import Freyd.S1_53_SliceRegular
import Freyd.S1_541_RelativeCapitalization

namespace Freyd

universe u

open Freyd

variable {𝒞 : Type u} [Cat.{u} 𝒞]

/-! ## §1.48  The dense class of ALL monics

  Freyd's §1.48 dense class needs only (i) all isos, (ii) closure under composition,
  (iii) closure under pullback.  The class of *all* monics satisfies these: isos are
  monic, monics compose, and the pullback of a monic is monic (`mono_pullback`,
  S1_45.lean).  §1.547's "dense monics" are a *sub*-class of this (the dense morphisms
  `x` that, with the surviving factors, form a product diagram); for the rational
  category as a localisation we may take the largest dense class that still inverts what
  we need — and the all-monics class is the cleanest concrete instance, Sorry-free. -/

section DenseAllMonos
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- A monic is preserved by composition (both legs monic ⇒ composite monic). -/
theorem mono_comp' {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (hf : Monic f) (hg : Monic g) :
    Monic (f ≫ g) := by
  intro W u v huv
  apply hf; apply hg
  rw [Cat.assoc, Cat.assoc]
  exact huv

/-- An isomorphism is monic (it is a split mono / retraction: `f ≫ inv = id`). -/
theorem mono_of_isIso {A B : 𝒞} {f : A ⟶ B} (hf : IsIso f) : Monic f := by
  obtain ⟨inv, hinv₁, _⟩ := hf
  exact mono_of_retraction f inv hinv₁

/-- **Monic left-factor.**  If `g ≫ f` is monic then `g` is monic.  (`u ≫ g = v ≫ g`
    implies `u ≫ (g ≫ f) = v ≫ (g ≫ f)`, cancel the composite mono.) -/
theorem mono_of_comp_mono {A B C : 𝒞} {g : A ⟶ B} {f : B ⟶ C} (h : Monic (g ≫ f)) : Monic g := by
  intro W u v huv
  apply h
  rw [← Cat.assoc, ← Cat.assoc, huv]

/-- **§1.48 — the class of all monics is a `DenseClass`.**  (i) isos are monic
    (`mono_of_isIso`); (ii) monics compose (`mono_comp'`); (iii) the pullback `π₁` of a
    monic is monic (`mono_pullback`).  This is the working dense class for the rational
    category `A[𝒟⁻¹]` below.  Sorry-free. -/
def denseMonos (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]
    [HasPullbacks 𝒞] : DenseClass 𝒞 where
  mem f := Monic f
  iso_mem _ hf := mono_of_isIso hf
  comp_mem f g hf hg := mono_comp' f g hf hg
  pb_mem f g hf := mono_pullback g f hf (HasPullbacks.has g f)

end DenseAllMonos

/-! ## §1.48  `FractionEquiv` is an equivalence relation

  Two fraction spans name the same morphism of `A[𝒟⁻¹]` iff they share a common
  dense-monic roof commuting both squares (`FractionEquiv`, S1_47.lean).  We show this
  is reflexive, symmetric, and transitive — so the hom-set is a genuine `Quotient`.
  Reflexivity: the identity roof (`id ∈ 𝒟`).  Symmetry: swap the roof legs.
  Transitivity: the pullback of the two roofs, glued over the shared apex; the composite
  denominator stays in `𝒟` by the dense class's composition + pullback closure. -/

section Equiv
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (G : DenseClass 𝒞)

/-- Reflexivity of `FractionEquiv`: a fraction is equivalent to itself via the identity
    roof (its own denominator is dense, and both squares commute trivially). -/
theorem fractionEquiv_refl {A B : 𝒞} (f : Fraction G A B) : FractionEquiv f f :=
  ⟨f.apex, Cat.id f.apex, Cat.id f.apex,
    by rw [Cat.id_comp]; exact f.denom_dense,
    by rw [Cat.id_comp],
    by rw [Cat.id_comp]⟩

/-- Symmetry of `FractionEquiv`: swap the two roof legs.  The shared-denominator
    density is symmetric because `r₁ ≫ f₁.denom = r₂ ≫ f₂.denom`. -/
theorem fractionEquiv_symm {A B : 𝒞} {f₁ f₂ : Fraction G A B}
    (h : FractionEquiv f₁ f₂) : FractionEquiv f₂ f₁ := by
  obtain ⟨R, r₁, r₂, hd, hden, hnum⟩ := h
  exact ⟨R, r₂, r₁, hden ▸ hd, hden.symm, hnum.symm⟩

end Equiv

/-! ## §1.48  The rational category's hom-sets and identities

  With `FractionEquiv` reflexive + symmetric (above), the hom-set `A[𝒟⁻¹](A,B)` is the
  quotient of fraction spans.  Transitivity (needed for `Quotient`) is the dense-class
  pullback-roof argument, isolated below as `fractionEquiv_trans` with its precise
  obstruction. -/

/-! ### §1.48  GENERALISING THE SKELETON — the monic dense-class interface `MonicDense`

  R2 hard-wired the calculus-of-fractions (equivalence, composition, well-definedness, units,
  associativity, localisation functor) to `denseMonos 𝒞`.  In fact the §1.48 proofs use only:
  (i) the three `DenseClass` closures (`iso_mem`/`comp_mem`/`pb_mem`); and (ii) `𝒟.mem f ↔ Monic f`,
  to extract `Monic` from a dense roof leg (`mono_of_comp_mono`) and to repackage the rebuilt roof
  denominator as dense.  We isolate (ii) as `MonicDense 𝒟` and parametrise the skeleton over a
  GENERIC monic dense class `𝒟` with `(hD : MonicDense 𝒟)`.  `denseMonos` is the canonical instance
  (`denseMonos_monic`, `mem ↔ Monic` is `Iff.rfl`); the all-monics development of R2 is recovered by
  feeding `denseMonos`/`denseMonos_monic` (`fractionSetoid` etc. below).

  THE ALL-MONICS INSTANCE vs THE REFINED CLASS (R7 correction).  `MonicDense` as stated requires
  `mem ↔ Monic`, i.e. the dense class is ALL monics; transitivity then rebuilds the roof denominator
  `π ≫ r ≫ d` by extracting `Monic r` from `Monic (r ≫ d)`, pulling the mono through the pullback, and
  repackaging via `mem ↔ Monic`.  §1.547's refined dense class `pairDenseClass` is a PROPER class of
  monics: its members ARE `Monic` in `Â` (`pairDenseClass_mem_mono`, via `pairDense_monic` — the book's
  "every dense morphism is monic"), but the REVERSE `Monic → mem` is false (not every `Â`-monic is a
  product projection).  So `pairDenseClass` is NOT the all-monics `MonicDense` instance; it is the
  §1.48 "dense class of monics" closed under iso/comp/pullback (`pairDenseClass`).  R6 wrongly read the
  underlying-`A`-arrow's epi-ness (`pairDense_cover`/`pairDense_epi`) as failure of monic-in-`Â` and
  concluded a dual co-span calculus was needed; that was a CATEGORY CONFUSION (`pairForget` does not
  reflect monos, so monic-in-`Â` ≠ monic-in-`A`).  The monic LEFT-fraction skeleton IS the right tool
  for `A* = Â[pairDense⁻¹]`; what remains for a full instantiation on `pairDenseClass` is the §1.48
  calculus-of-fractions saturation of the roof rebuild for a proper monic class (the dense roof leg
  `r` with `r ≫ d` dense need not have `π ≫ r ≫ d` dense from the bare `DenseClass` closures alone —
  this is the standard Ore/§1.48 condition, NOT the false monic/epic wall).  See `pairDense_monic`,
  `pairDenseClass_mem_mono`, `pairDense_monic_and_epic`. -/

/-- A dense class whose members are EXACTLY the monics — the §1.48 "dense monic" hypothesis, the one
    extra fact (beyond the `DenseClass` record) the calculus-of-fractions skeleton needs.  `denseMonos`
    is the canonical instance. -/
structure MonicDense [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (𝒟 : DenseClass 𝒞) :
    Prop where
  mem_iff_mono : ∀ {A B : 𝒞} (f : A ⟶ B), 𝒟.mem f ↔ Monic f

/-- `denseMonos` is a monic dense class (`mem` is `Monic` definitionally). -/
theorem denseMonos_monic [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] :
    MonicDense (denseMonos 𝒞) := ⟨fun _ => Iff.rfl⟩

/-- A dense roof leg `r` (one with `𝒟.mem (r ≫ d)`) is monic, in a monic dense class. -/
theorem MonicDense.leg_mono [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    {𝒟 : DenseClass 𝒞} (hD : MonicDense 𝒟) {A B C : 𝒞} {r : A ⟶ B} {d : B ⟶ C}
    (h : 𝒟.mem (r ≫ d)) : Monic r :=
  mono_of_comp_mono ((hD.mem_iff_mono _).1 h)

/-! ### §1.48  THE SATURATING INTERFACE — `DenseRoof`

  `MonicDense` (members ↔ monics) suffices for the all-monics class but is FALSE for a proper
  dense class such as `pairDenseClass` (not every `Â`-monic is a product projection).  The §1.48
  calculus-of-fractions proofs need exactly ONE property of `denseMonos` beyond the bare `DenseClass`
  record: **members are monic** (`pairDenseClass_mem_mono` for the pairs class).  We isolate this as

      `DenseRoof 𝒟 := ∀ f, 𝒟.mem f → Monic f`

  the §1.48/§1.481 "dense class of monics" hypothesis.  Crucially the comparison roofs are rebuilt by
  pulling back the dense DENOMINATORS (which are MEMBERS, `mem(r ≫ d)` is the `FractionEquiv` field)
  over the common target — never a bare roof leg — so density stays inside `pb_mem`/`comp_mem`; the
  one cancellation step (recovering equality of the inner legs from equality-after-a-denominator) uses
  members being monic.  This is STRICTLY WEAKER than `MonicDense` (no `Monic → mem`), and holds for
  `pairDenseClass` (`pairDense_denseRoof`).  No saturation/Ore condition beyond the `DenseClass`
  record is needed — the standard left-calculus-of-fractions. -/
structure DenseRoof [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (𝒟 : DenseClass 𝒞) :
    Prop where
  /-- members are monic (`pairDenseClass_mem_mono` for the pairs class) -/
  mem_mono : ∀ {A B : 𝒞} (f : A ⟶ B), 𝒟.mem f → Monic f

/-- A `MonicDense` class is `DenseRoof`: `mem_mono` is the forward biconditional. -/
theorem MonicDense.toDenseRoof [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    {𝒟 : DenseClass 𝒞} (hD : MonicDense 𝒟) : DenseRoof 𝒟 where
  mem_mono _ h := (hD.mem_iff_mono _).1 h

/-- A dense roof leg `r` (`𝒟.mem (r ≫ d)`) is monic, in a `DenseRoof` class. -/
theorem DenseRoof.leg_mono [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B C : 𝒞} {r : A ⟶ B} {d : B ⟶ C}
    (h : 𝒟.mem (r ≫ d)) : Monic r :=
  mono_of_comp_mono (hD.mem_mono _ h)

section RatHom
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- **§1.48 — Transitivity of `FractionEquiv` for a MONIC dense class `𝒟`.**  Given roofs
    `R : f₁ ≈ f₂` (legs `r₁,r₂`) and `S : f₂ ≈ f₃` (legs `s₂,s₃`), form the pullback `P` of
    `(r₂, s₂)` over `f₂.apex`.  Its two legs compose with `r₁`/`s₃` to give a roof `f₁ ≈ f₃`; the
    declared-dense leg `(P.π₁ ≫ r₁) ≫ f₁.denom` is monic (`r₁`/`s₂` monic as dense roof legs,
    `P.π₁` the pullback of monic `s₂`, `f₁.denom` monic) and repackaged as dense via `mem_iff_mono`.
    Sorry-free for any `MonicDense 𝒟`; instantiated at `denseMonos`/`denseMonos_monic` below. -/
theorem fractionEquiv_trans {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B : 𝒞}
    {f₁ f₂ f₃ : Fraction 𝒟 A B}
    (h₁₂ : FractionEquiv f₁ f₂) (h₂₃ : FractionEquiv f₂ f₃) : FractionEquiv f₁ f₃ := by
  obtain ⟨R, r₁, r₂, hRd, hRden, hRnum⟩ := h₁₂
  obtain ⟨S, s₂, s₃, hSd, hSden, hSnum⟩ := h₂₃
  -- §1.48 left-calculus: pull back the DENSE DENOMINATORS `r₁≫f₁.denom : R → A` and
  -- `s₃≫f₃.denom : S → A` over `A` (both MEMBERS).  `P.π₁` = pb of the member `s₃≫f₃.denom` is a
  -- member (`pb_mem`); the new roof denom `(P.π₁≫r₁)≫f₁.denom = P.π₁≫(member)` is a member.
  let P := (HasPullbacks.has (r₁ ≫ f₁.denom) (s₃ ≫ f₃.denom)).cone
  have hPw : P.π₁ ≫ (r₁ ≫ f₁.denom) = P.π₂ ≫ (s₃ ≫ f₃.denom) := P.w
  refine ⟨P.pt, P.π₁ ≫ r₁, P.π₂ ≫ s₃, ?_, ?_, ?_⟩
  · -- denom is a member: `(P.π₁≫r₁)≫f₁.denom = P.π₁≫(r₁≫f₁.denom)`, `P.π₁` member, comp member.
    have hSd' : 𝒟.mem (s₃ ≫ f₃.denom) := by rw [← hSden]; exact hSd
    have hP₁ : 𝒟.mem P.π₁ := 𝒟.pb_mem (s₃ ≫ f₃.denom) (r₁ ≫ f₁.denom) hSd'
    rw [Cat.assoc]; exact 𝒟.comp_mem P.π₁ (r₁ ≫ f₁.denom) hP₁ hRd
  · -- denominators agree by `P`'s pullback square (definitionally the two member-denoms).
    calc (P.π₁ ≫ r₁) ≫ f₁.denom = P.π₁ ≫ (r₁ ≫ f₁.denom) := by rw [Cat.assoc]
      _ = P.π₂ ≫ (s₃ ≫ f₃.denom) := hPw
      _ = (P.π₂ ≫ s₃) ≫ f₃.denom := by rw [Cat.assoc]
  · -- numerators agree.  Cancel `f₂.denom` (MONIC member) from the square to relate the inner legs.
    have hd₂ : Monic f₂.denom := hD.mem_mono _ f₂.denom_dense
    -- `P.π₁≫r₂≫f₂.denom = P.π₁≫r₁≫f₁.denom = P.π₂≫s₃≫f₃.denom = P.π₂≫s₂≫f₂.denom`
    have hmid : (P.π₁ ≫ r₂) ≫ f₂.denom = (P.π₂ ≫ s₂) ≫ f₂.denom := by
      calc (P.π₁ ≫ r₂) ≫ f₂.denom
          = P.π₁ ≫ (r₂ ≫ f₂.denom) := by rw [Cat.assoc]
        _ = P.π₁ ≫ (r₁ ≫ f₁.denom) := congrArg (P.π₁ ≫ ·) hRden.symm
        _ = P.π₂ ≫ (s₃ ≫ f₃.denom) := hPw
        _ = P.π₂ ≫ (s₂ ≫ f₂.denom) := congrArg (P.π₂ ≫ ·) hSden.symm
        _ = (P.π₂ ≫ s₂) ≫ f₂.denom := by rw [Cat.assoc]
    have hleg : P.π₁ ≫ r₂ = P.π₂ ≫ s₂ := hd₂ _ _ hmid
    calc (P.π₁ ≫ r₁) ≫ f₁.num
        = P.π₁ ≫ (r₁ ≫ f₁.num) := by rw [Cat.assoc]
      _ = P.π₁ ≫ (r₂ ≫ f₂.num) := by rw [hRnum]
      _ = (P.π₁ ≫ r₂) ≫ f₂.num := by rw [Cat.assoc]
      _ = (P.π₂ ≫ s₂) ≫ f₂.num := by rw [hleg]
      _ = P.π₂ ≫ (s₂ ≫ f₂.num) := by rw [Cat.assoc]
      _ = P.π₂ ≫ (s₃ ≫ f₃.num) := by rw [hSnum]
      _ = (P.π₂ ≫ s₃) ≫ f₃.num := by rw [Cat.assoc]

/-- The setoid on fraction spans `A → B`: `FractionEquiv` with its three laws. -/
def fractionSetoid {A B : 𝒞} : Setoid (Fraction (denseMonos 𝒞) A B) where
  r := FractionEquiv
  iseqv := ⟨fractionEquiv_refl (denseMonos 𝒞), fractionEquiv_symm (denseMonos 𝒞),
    fractionEquiv_trans denseMonos_monic.toDenseRoof⟩

/-- **§1.48 — the hom-set `A[𝒟⁻¹](A,B)`**: equivalence classes of fraction spans
    (for the all-monics dense class `denseMonos 𝒞`).  Sorry-free `Quotient`. -/
def RatHom (A B : 𝒞) : Type u := Quotient (fractionSetoid (𝒞 := 𝒞) (A := A) (B := B))

/-- The IDENTITY span `A → A`: `A ←[id]— A —id→ A` (denominator the identity, dense). -/
def idFraction (G : DenseClass 𝒞) (A : 𝒞) : Fraction G A A :=
  ⟨A, Cat.id A, Cat.id A, G.iso_mem (Cat.id A) ⟨Cat.id A, Cat.id_comp _, Cat.id_comp _⟩⟩

/-- The identity morphism of `A[𝒟⁻¹]` at `A`. -/
def ratId (A : 𝒞) : RatHom (𝒞 := 𝒞) A A :=
  Quotient.mk _ (idFraction (denseMonos 𝒞) A)

/-- The localisation on objects is the identity-on-objects map. -/
def loc (A : 𝒞) : 𝒞 := A

/-- The localisation of an ordinary arrow `f : A → B` is the span `A ←[id]— A —f→ B`. -/
def locFraction (G : DenseClass 𝒞) {A B : 𝒞} (f : A ⟶ B) : Fraction G A B :=
  ⟨A, Cat.id A, f, G.iso_mem (Cat.id A) ⟨Cat.id A, Cat.id_comp _, Cat.id_comp _⟩⟩

/-- The localisation functor on arrows: `f ↦ [A ←id— A —f→ B]`. -/
def locMap {A B : 𝒞} (f : A ⟶ B) : RatHom (𝒞 := 𝒞) A B :=
  Quotient.mk _ (locFraction (denseMonos 𝒞) f)

end RatHom

/-! ## §1.48  Composition by pullback

  The composite of spans `A ←[d₁]— P₁ —n₁→ B` and `B ←[d₂]— P₂ —n₂→ C` is formed by
  pulling back `n₁` against `d₂` over `B`: with `Q` the pullback of `(n₁, d₂)`,

        A ←[d₁]— P₁ ←[π₁]— Q —[π₂]— P₂ —n₂→ C
                                  composite denom = π₁ ≫ d₁  (dense: pb of d₂ then comp d₁)
                                  composite num   = π₂ ≫ n₂

  The composite denominator is dense because `π₁` is the pullback of the dense `d₂`
  (closure (iii)) and `d₁` is dense (closure (ii)).  Well-definedness on equivalence
  classes (independence of representative names and of the pullback choice) is §1.48's
  "the named morphism is independent of the choice of names and pullback" — the genuine
  calculus-of-fractions content, isolated below. -/

section Comp
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] (G : DenseClass 𝒞)

/-- The composite span of two fraction spans, by pullback of `(num₁, denom₂)`. -/
def compFraction {A B C : 𝒞} (f : Fraction G A B) (g : Fraction G B C) : Fraction G A C :=
  let Q := (HasPullbacks.has f.num g.denom).cone
  { apex := Q.pt
    denom := Q.π₁ ≫ f.denom
    num := Q.π₂ ≫ g.num
    denom_dense :=
      -- `Q.π₁` is the pullback of `g.denom` along `f.num`; dense by (iii), then `f.denom`
      -- dense gives the composite dense by (ii).
      G.comp_mem Q.π₁ f.denom
        (G.pb_mem g.denom f.num g.denom_dense) f.denom_dense }

/-! ### §1.48 well-definedness of composition

  `ratComp` needs `compFraction` to respect `FractionEquiv` in BOTH arguments.  We split
  the binary congruence into two single-variable congruences and glue with transitivity:

    `compFraction f g ≈ compFraction f' g`   (LEFT — replace the first span)
    `compFraction f' g ≈ compFraction f' g'`  (RIGHT — replace the second span)

  Each is a SINGLE pullback roof.  Write `Q := pb(f.num, g.denom)` for `compFraction f g`'s
  apex; the roof witnessing `f ≈ f'` (resp. `g ≈ g'`) is pulled back against the relevant
  projection of `Q`, and the comparison leg into `Q' := pb(f'.num, g.denom)` (resp.
  `pb(f.num, g'.denom)`) is produced by `Q'`'s universal property.  Density of the declared
  roof-denominator is `Monic`-closure: the roof leg is a pullback of the mono left-factor
  (`mono_of_comp_mono` on the roof's dense denominator), and `compFraction`'s own denom is
  already mono (`compFraction.denom_dense`). -/

/-- **RIGHT congruence**: replacing the second span by an equivalent one yields an equivalent
    composite.  Roof = pullback of `compFraction f g`'s `Q.π₂` against the `g ≈ g'` roof leg
    `s : S → g.apex`; the leg into `Q' := pb(f.num, g'.denom)` is built by `Q'`'s lift. -/
theorem compFraction_congr_right {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B C : 𝒞}
    (f : Fraction 𝒟 A B)
    {g g' : Fraction 𝒟 B C} (hg : FractionEquiv g g') :
    FractionEquiv (compFraction 𝒟 f g) (compFraction 𝒟 f g') := by
  obtain ⟨S, s, s', hSd, hSden, hSnum⟩ := hg
  let Q := (HasPullbacks.has f.num g.denom).cone
  let Q' := (HasPullbacks.has f.num g'.denom).cone
  -- §1.48 left-calculus: pull `Q`'s `B`-leg `Q.π₁ ≫ f.num` back against the MEMBER `s ≫ g.denom`
  -- over `B`.  `R.π₁` = pb of the member is a member (`pb_mem`); the roof denom stays in `𝒟`.
  let R := (HasPullbacks.has (Q.π₁ ≫ f.num) (s ≫ g.denom)).cone
  have hRw : R.π₁ ≫ (Q.π₁ ≫ f.num) = R.π₂ ≫ (s ≫ g.denom) := R.w
  -- `R.π₁ ≫ Q.π₂ = R.π₂ ≫ s` after cancelling the MONIC member `g.denom`.
  have hd : Monic g.denom := hD.mem_mono _ g.denom_dense
  have hleg : R.π₁ ≫ Q.π₂ = R.π₂ ≫ s := by
    apply hd
    calc (R.π₁ ≫ Q.π₂) ≫ g.denom = R.π₁ ≫ (Q.π₂ ≫ g.denom) := by rw [Cat.assoc]
      _ = R.π₁ ≫ (Q.π₁ ≫ f.num) := by rw [← Q.w]
      _ = R.π₂ ≫ (s ≫ g.denom) := hRw
      _ = (R.π₂ ≫ s) ≫ g.denom := by rw [Cat.assoc]
  -- comparison cone into `Q'`: `(R.π₁ ≫ Q.π₁, R.π₂ ≫ s')`, square via `hRw`/`hSden`.
  have sq : (R.π₁ ≫ Q.π₁) ≫ f.num = (R.π₂ ≫ s') ≫ g'.denom := by
    calc (R.π₁ ≫ Q.π₁) ≫ f.num = R.π₁ ≫ (Q.π₁ ≫ f.num) := by rw [Cat.assoc]
      _ = R.π₂ ≫ (s ≫ g.denom) := hRw
      _ = R.π₂ ≫ (s' ≫ g'.denom) := congrArg (R.π₂ ≫ ·) hSden
      _ = (R.π₂ ≫ s') ≫ g'.denom := by rw [Cat.assoc]
  let ρ' := (HasPullbacks.has f.num g'.denom).lift ⟨R.pt, R.π₁ ≫ Q.π₁, R.π₂ ≫ s', sq⟩
  have hρ'1 : ρ' ≫ Q'.π₁ = R.π₁ ≫ Q.π₁ := (HasPullbacks.has f.num g'.denom).lift_fst _
  have hρ'2 : ρ' ≫ Q'.π₂ = R.π₂ ≫ s' := (HasPullbacks.has f.num g'.denom).lift_snd _
  refine ⟨R.pt, R.π₁, ρ', ?_, ?_, ?_⟩
  · -- dense WITHIN the interface: `R.π₁ = pb(member s≫g.denom)` is a member; comp with `Q`'s denom.
    have hR₁ : 𝒟.mem R.π₁ := 𝒟.pb_mem (s ≫ g.denom) (Q.π₁ ≫ f.num) hSd
    show 𝒟.mem (R.π₁ ≫ (Q.π₁ ≫ f.denom))
    exact 𝒟.comp_mem R.π₁ (Q.π₁ ≫ f.denom) hR₁ (compFraction 𝒟 f g).denom_dense
  · -- denoms agree
    show R.π₁ ≫ (Q.π₁ ≫ f.denom) = ρ' ≫ (Q'.π₁ ≫ f.denom)
    calc R.π₁ ≫ (Q.π₁ ≫ f.denom)
        = (R.π₁ ≫ Q.π₁) ≫ f.denom := by rw [Cat.assoc]
      _ = (ρ' ≫ Q'.π₁) ≫ f.denom := by rw [hρ'1]
      _ = ρ' ≫ (Q'.π₁ ≫ f.denom) := by rw [Cat.assoc]
  · -- nums agree
    show R.π₁ ≫ (Q.π₂ ≫ g.num) = ρ' ≫ (Q'.π₂ ≫ g'.num)
    calc R.π₁ ≫ (Q.π₂ ≫ g.num)
        = (R.π₁ ≫ Q.π₂) ≫ g.num := by rw [Cat.assoc]
      _ = (R.π₂ ≫ s) ≫ g.num := by rw [hleg]
      _ = R.π₂ ≫ (s ≫ g.num) := by rw [Cat.assoc]
      _ = R.π₂ ≫ (s' ≫ g'.num) := by rw [hSnum]
      _ = (R.π₂ ≫ s') ≫ g'.num := by rw [Cat.assoc]
      _ = (ρ' ≫ Q'.π₂) ≫ g'.num := by rw [hρ'2]
      _ = ρ' ≫ (Q'.π₂ ≫ g'.num) := by rw [Cat.assoc]

/-- **LEFT congruence**: replacing the first span by an equivalent one yields an equivalent
    composite.  Roof = pullback of `compFraction f g`'s `Q.π₁` against the `f ≈ f'` roof leg
    `t : T → f.apex`; the leg into `Q' := pb(f'.num, g.denom)` is built by `Q'`'s lift. -/
theorem compFraction_congr_left {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B C : 𝒞}
    {f f' : Fraction 𝒟 A B}
    (g : Fraction 𝒟 B C) (hf : FractionEquiv f f') :
    FractionEquiv (compFraction 𝒟 f g) (compFraction 𝒟 f' g) := by
  obtain ⟨T, t, t', hTd, hTden, hTnum⟩ := hf
  let Q := (HasPullbacks.has f.num g.denom).cone
  let Q' := (HasPullbacks.has f'.num g.denom).cone
  -- §1.48 left-calculus: pull `Q`'s denom `Q.π₁ ≫ f.denom : Q → A` back against the MEMBER
  -- `t ≫ f.denom : T → A` over `A`.  `R.π₁` = pb of the member is a member (`pb_mem`).
  let R := (HasPullbacks.has (Q.π₁ ≫ f.denom) (t ≫ f.denom)).cone
  have hRw : R.π₁ ≫ (Q.π₁ ≫ f.denom) = R.π₂ ≫ (t ≫ f.denom) := R.w
  -- `R.π₁ ≫ Q.π₁ = R.π₂ ≫ t` after cancelling the MONIC member `f.denom`.
  have hd : Monic f.denom := hD.mem_mono _ f.denom_dense
  have hleg : R.π₁ ≫ Q.π₁ = R.π₂ ≫ t := by
    apply hd
    calc (R.π₁ ≫ Q.π₁) ≫ f.denom = R.π₁ ≫ (Q.π₁ ≫ f.denom) := by rw [Cat.assoc]
      _ = R.π₂ ≫ (t ≫ f.denom) := hRw
      _ = (R.π₂ ≫ t) ≫ f.denom := by rw [Cat.assoc]
  -- comparison cone into `Q'`: `(R.π₂ ≫ t', R.π₁ ≫ Q.π₂)`.
  have sq : (R.π₂ ≫ t') ≫ f'.num = (R.π₁ ≫ Q.π₂) ≫ g.denom := by
    calc (R.π₂ ≫ t') ≫ f'.num
        = R.π₂ ≫ (t' ≫ f'.num) := by rw [Cat.assoc]
      _ = R.π₂ ≫ (t ≫ f.num) := by rw [hTnum]
      _ = (R.π₂ ≫ t) ≫ f.num := by rw [Cat.assoc]
      _ = (R.π₁ ≫ Q.π₁) ≫ f.num := by rw [hleg]
      _ = R.π₁ ≫ (Q.π₁ ≫ f.num) := by rw [Cat.assoc]
      _ = R.π₁ ≫ (Q.π₂ ≫ g.denom) := by rw [Q.w]
      _ = (R.π₁ ≫ Q.π₂) ≫ g.denom := by rw [Cat.assoc]
  let ρ' := (HasPullbacks.has f'.num g.denom).lift ⟨R.pt, R.π₂ ≫ t', R.π₁ ≫ Q.π₂, sq⟩
  have hρ'1 : ρ' ≫ Q'.π₁ = R.π₂ ≫ t' := (HasPullbacks.has f'.num g.denom).lift_fst _
  have hρ'2 : ρ' ≫ Q'.π₂ = R.π₁ ≫ Q.π₂ := (HasPullbacks.has f'.num g.denom).lift_snd _
  refine ⟨R.pt, R.π₁, ρ', ?_, ?_, ?_⟩
  · -- dense WITHIN the interface: `R.π₁ = pb(member t≫f.denom)` is a member; comp with `Q`'s denom.
    have hR₁ : 𝒟.mem R.π₁ := 𝒟.pb_mem (t ≫ f.denom) (Q.π₁ ≫ f.denom) hTd
    show 𝒟.mem (R.π₁ ≫ (Q.π₁ ≫ f.denom))
    exact 𝒟.comp_mem R.π₁ (Q.π₁ ≫ f.denom) hR₁ (compFraction 𝒟 f g).denom_dense
  · -- denoms agree
    show R.π₁ ≫ (Q.π₁ ≫ f.denom) = ρ' ≫ (Q'.π₁ ≫ f'.denom)
    calc R.π₁ ≫ (Q.π₁ ≫ f.denom)
        = R.π₂ ≫ (t ≫ f.denom) := hRw
      _ = R.π₂ ≫ (t' ≫ f'.denom) := congrArg (R.π₂ ≫ ·) hTden
      _ = (R.π₂ ≫ t') ≫ f'.denom := by rw [Cat.assoc]
      _ = (ρ' ≫ Q'.π₁) ≫ f'.denom := by rw [hρ'1]
      _ = ρ' ≫ (Q'.π₁ ≫ f'.denom) := by rw [Cat.assoc]
  · -- nums agree
    show R.π₁ ≫ (Q.π₂ ≫ g.num) = ρ' ≫ (Q'.π₂ ≫ g.num)
    calc R.π₁ ≫ (Q.π₂ ≫ g.num)
        = (R.π₁ ≫ Q.π₂) ≫ g.num := by rw [Cat.assoc]
      _ = (ρ' ≫ Q'.π₂) ≫ g.num := by rw [hρ'2]
      _ = ρ' ≫ (Q'.π₂ ≫ g.num) := by rw [Cat.assoc]

/-- **§1.48 — composition in `A[𝒟⁻¹]` is well-defined** (on equivalence classes).
    The binary congruence is the composite of the LEFT and RIGHT single-span congruences
    (`compFraction_congr_left`/`_right`) via transitivity — Freyd's "the named morphism is
    independent of the choice of names for `A → B` and `B → C`, and of the choice of
    pullback" (§1.48).  Sorry-free over `denseMonos 𝒞`. -/
def ratComp {A B C : 𝒞} (m : RatHom (𝒞 := 𝒞) A B)
    (n : RatHom (𝒞 := 𝒞) B C) : RatHom (𝒞 := 𝒞) A C :=
  Quotient.lift₂ (fun f g => Quotient.mk _ (compFraction (denseMonos 𝒞) f g))
    (by
      intro f g f' g' hf hg
      apply Quotient.sound
      exact fractionEquiv_trans denseMonos_monic.toDenseRoof
        (compFraction_congr_left denseMonos_monic.toDenseRoof g hf)
        (compFraction_congr_right denseMonos_monic.toDenseRoof f' hg))
    m n

/-! ### §1.48  Identity and associativity laws — the `Cat` instance

  `RatHom` with `ratComp`/`ratId` is a category.  The unit laws are one-line roofs
  (composing with the identity span `A ←id— A —id→ A` just re-bases along the iso
  pullback-of-identity).  Associativity is the standard pasting of the two composite
  pullbacks. -/

/-- LEFT UNIT: `[idFraction A] ∘ f ≈ f`.  Composite apex `Q = pb(id_A, f.denom)`; the roof
    `(id, Q.π₂)` to `f` works because `Q.π₁ = Q.π₂ ≫ f.denom` (the square with `id_A`). -/
theorem compFraction_idFraction_left {𝒟 : DenseClass 𝒞} {A B : 𝒞} (f : Fraction 𝒟 A B) :
    FractionEquiv (compFraction 𝒟 (idFraction 𝒟 A) f) f := by
  let Q := (HasPullbacks.has (idFraction 𝒟 A).num f.denom).cone
  -- `idFraction A`.num = id_A, .denom = id_A, .apex = A; square: `Q.π₁ ≫ id_A = Q.π₂ ≫ f.denom`
  have hw : Q.π₁ = Q.π₂ ≫ f.denom := by
    have := Q.w; simp only [idFraction, Cat.comp_id] at this; exact this
  refine ⟨Q.pt, Cat.id Q.pt, Q.π₂, ?_, ?_, ?_⟩
  · -- dense WITHIN the interface: `Q.π₁ = pb(f.denom)` along `id_A` is dense (`pb_mem`).
    have hm : 𝒟.mem Q.π₁ := 𝒟.pb_mem f.denom (idFraction 𝒟 A).num f.denom_dense
    have he : Cat.id Q.pt ≫ (compFraction 𝒟 (idFraction 𝒟 A) f).denom = Q.π₁ := by
      show Cat.id Q.pt ≫ (Q.π₁ ≫ Cat.id A) = Q.π₁
      rw [Cat.id_comp]; exact Cat.comp_id Q.π₁
    rw [he]; exact hm
  · show Cat.id Q.pt ≫ (Q.π₁ ≫ (idFraction 𝒟 A).denom) = Q.π₂ ≫ f.denom
    simp only [idFraction, Cat.comp_id, Cat.id_comp]; exact hw
  · show Cat.id Q.pt ≫ (Q.π₂ ≫ f.num) = Q.π₂ ≫ f.num
    rw [Cat.id_comp]

/-- RIGHT UNIT: `f ∘ [idFraction B] ≈ f`.  Composite apex `Q = pb(f.num, id_B)`; roof
    `(id, Q.π₁)` to `f` works because `Q.π₂ = Q.π₁ ≫ f.num` (the square with `id_B`). -/
theorem compFraction_idFraction_right {𝒟 : DenseClass 𝒞} {A B : 𝒞} (f : Fraction 𝒟 A B) :
    FractionEquiv (compFraction 𝒟 f (idFraction 𝒟 B)) f := by
  let Q := (HasPullbacks.has f.num (idFraction 𝒟 B).denom).cone
  have hw : Q.π₁ ≫ f.num = Q.π₂ := by
    have := Q.w; simp only [idFraction, Cat.comp_id] at this; exact this
  refine ⟨Q.pt, Cat.id Q.pt, Q.π₁, ?_, ?_, ?_⟩
  · show 𝒟.mem (Cat.id Q.pt ≫ (Q.π₁ ≫ f.denom))
    rw [Cat.id_comp]; exact (compFraction 𝒟 f (idFraction 𝒟 B)).denom_dense
  · show Cat.id Q.pt ≫ (Q.π₁ ≫ f.denom) = Q.π₁ ≫ f.denom
    rw [Cat.id_comp]
  · show Cat.id Q.pt ≫ (Q.π₂ ≫ (idFraction 𝒟 B).num) = Q.π₁ ≫ f.num
    simp only [idFraction, Cat.comp_id, Cat.id_comp]; exact hw.symm

/-- **ASSOCIATIVITY** of `compFraction` up to `FractionEquiv`: `(f∘g)∘h ≈ f∘(g∘h)`.
    Both composites are limits of the same length-3 cospan chain
    `f.apex →f.num B ←g.denom g.apex →g.num C ←h.denom h.apex`.  We take the LEFT composite's
    apex `Q₂.pt` as the roof, `r₁ := id`, and build the comparison `r₂ : Q₂.pt → P₂.pt`
    (`P₂.pt` = the RIGHT composite's apex) by the universal property of the inner pullback
    `P₁ := pb(g.num, h.denom)` then the outer `P₂ := pb(f.num, P₁.π₁ ≫ g.denom)`. -/
theorem compFraction_assoc {𝒟 : DenseClass 𝒞} {A B C D : 𝒞} (f : Fraction 𝒟 A B)
    (g : Fraction 𝒟 B C) (h : Fraction 𝒟 C D) :
    FractionEquiv
      (compFraction 𝒟 (compFraction 𝒟 f g) h)
      (compFraction 𝒟 f (compFraction 𝒟 g h)) := by
  -- LEFT composite: `Q₁ = pb(f.num, g.denom)`, `Q₂ = pb(Q₁.π₂ ≫ g.num, h.denom)`
  let Q₁ := (HasPullbacks.has f.num g.denom).cone
  let Q₂ := (HasPullbacks.has (Q₁.π₂ ≫ g.num) h.denom).cone
  -- RIGHT composite: `P₁ = pb(g.num, h.denom)`, `P₂ = pb(f.num, P₁.π₁ ≫ g.denom)`
  let P₁ := (HasPullbacks.has g.num h.denom).cone
  let P₂ := (HasPullbacks.has f.num (P₁.π₁ ≫ g.denom)).cone
  -- inner comparison `w₁ : Q₂.pt → P₁.pt`
  have sq₁ : (Q₂.π₁ ≫ Q₁.π₂) ≫ g.num = Q₂.π₂ ≫ h.denom := by
    rw [Cat.assoc]; exact Q₂.w
  let w₁ := (HasPullbacks.has g.num h.denom).lift ⟨Q₂.pt, Q₂.π₁ ≫ Q₁.π₂, Q₂.π₂, sq₁⟩
  have hw₁1 : w₁ ≫ P₁.π₁ = Q₂.π₁ ≫ Q₁.π₂ := (HasPullbacks.has g.num h.denom).lift_fst _
  have hw₁2 : w₁ ≫ P₁.π₂ = Q₂.π₂ := (HasPullbacks.has g.num h.denom).lift_snd _
  -- outer comparison `r₂ : Q₂.pt → P₂.pt`
  have sq₂ : (Q₂.π₁ ≫ Q₁.π₁) ≫ f.num = w₁ ≫ (P₁.π₁ ≫ g.denom) := by
    calc (Q₂.π₁ ≫ Q₁.π₁) ≫ f.num
        = Q₂.π₁ ≫ (Q₁.π₁ ≫ f.num) := by rw [Cat.assoc]
      _ = Q₂.π₁ ≫ (Q₁.π₂ ≫ g.denom) := by rw [Q₁.w]
      _ = (Q₂.π₁ ≫ Q₁.π₂) ≫ g.denom := by rw [Cat.assoc]
      _ = (w₁ ≫ P₁.π₁) ≫ g.denom := by rw [hw₁1]
      _ = w₁ ≫ (P₁.π₁ ≫ g.denom) := by rw [Cat.assoc]
  let r₂ := (HasPullbacks.has f.num (P₁.π₁ ≫ g.denom)).lift ⟨Q₂.pt, Q₂.π₁ ≫ Q₁.π₁, w₁, sq₂⟩
  have hr₂1 : r₂ ≫ P₂.π₁ = Q₂.π₁ ≫ Q₁.π₁ := (HasPullbacks.has f.num (P₁.π₁ ≫ g.denom)).lift_fst _
  have hr₂2 : r₂ ≫ P₂.π₂ = w₁ := (HasPullbacks.has f.num (P₁.π₁ ≫ g.denom)).lift_snd _
  refine ⟨Q₂.pt, Cat.id Q₂.pt, r₂, ?_, ?_, ?_⟩
  · -- dense: `id ≫ (LEFT).denom` = `(LEFT).denom_dense`
    show 𝒟.mem (Cat.id Q₂.pt ≫ (compFraction 𝒟 (compFraction 𝒟 f g) h).denom)
    rw [Cat.id_comp]
    exact (compFraction 𝒟 (compFraction 𝒟 f g) h).denom_dense
  · -- denoms agree
    show Cat.id Q₂.pt ≫ (Q₂.π₁ ≫ (Q₁.π₁ ≫ f.denom)) = r₂ ≫ (P₂.π₁ ≫ f.denom)
    rw [Cat.id_comp]
    calc Q₂.π₁ ≫ (Q₁.π₁ ≫ f.denom)
        = (Q₂.π₁ ≫ Q₁.π₁) ≫ f.denom := by rw [Cat.assoc]
      _ = (r₂ ≫ P₂.π₁) ≫ f.denom := by rw [hr₂1]
      _ = r₂ ≫ (P₂.π₁ ≫ f.denom) := by rw [Cat.assoc]
  · -- nums agree
    show Cat.id Q₂.pt ≫ (Q₂.π₂ ≫ h.num) = r₂ ≫ (P₂.π₂ ≫ (P₁.π₂ ≫ h.num))
    rw [Cat.id_comp]
    calc Q₂.π₂ ≫ h.num
        = (w₁ ≫ P₁.π₂) ≫ h.num := by rw [hw₁2]
      _ = w₁ ≫ (P₁.π₂ ≫ h.num) := by rw [Cat.assoc]
      _ = (r₂ ≫ P₂.π₂) ≫ (P₁.π₂ ≫ h.num) := by rw [hr₂2]
      _ = r₂ ≫ (P₂.π₂ ≫ (P₁.π₂ ≫ h.num)) := by rw [Cat.assoc]

end Comp

/-! ### §1.48  The `Cat` instance on the rational category

  `RatHom` with `ratComp`/`ratId` is a category.  Each law is `Quotient.ind` reduction to the
  corresponding `compFraction` law (`compFraction_idFraction_left/right`, `compFraction_assoc`),
  then `Quotient.sound`.  Objects are the objects of `𝒞` (carried as `Rat 𝒞 := 𝒞`). -/

section CatInstance
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- The carrier of the rational category `A[denseMonos⁻¹]`: a one-field STRUCTURE wrapper of
    `𝒞`'s objects.  A genuine new type (not a `def` alias) so that `Cat (Rat 𝒞)` instance
    resolution does NOT collapse onto `𝒞`'s own `Cat` instance (a bare `def` alias whnf-reduces
    to `𝒞`, so `⟶` between `Rat 𝒞` objects would silently pick `𝒞`'s hom). -/
structure Rat (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    where mk :: (obj : 𝒞)

/-- LEFT UNIT on `RatHom`: `ratId ∘ m = m`. -/
theorem ratComp_id_left {A B : 𝒞} (m : RatHom (𝒞 := 𝒞) A B) : ratComp (ratId A) m = m := by
  refine Quotient.inductionOn m (fun f => ?_)
  exact Quotient.sound (compFraction_idFraction_left f)

/-- RIGHT UNIT on `RatHom`: `m ∘ ratId = m`. -/
theorem ratComp_id_right {A B : 𝒞} (m : RatHom (𝒞 := 𝒞) A B) : ratComp m (ratId B) = m := by
  refine Quotient.inductionOn m (fun f => ?_)
  exact Quotient.sound (compFraction_idFraction_right f)

/-- ASSOCIATIVITY on `RatHom`. -/
theorem ratComp_assoc {A B C D : 𝒞} (m : RatHom (𝒞 := 𝒞) A B) (n : RatHom (𝒞 := 𝒞) B C)
    (p : RatHom (𝒞 := 𝒞) C D) : ratComp (ratComp m n) p = ratComp m (ratComp n p) := by
  refine Quotient.inductionOn₃ m n p (fun f g h => ?_)
  exact Quotient.sound (compFraction_assoc f g h)

/-- **§1.48 — the rational category `A[denseMonos⁻¹]` is a category.**  Objects = objects of
    `𝒞`; homs = `RatHom` (fraction quotients); composition = `ratComp`; identity = `ratId`.
    The three laws are the lifted `compFraction` unit/associativity laws.  Sorry-free. -/
instance ratCat : Cat.{u} (Rat 𝒞) where
  Hom A B := RatHom (𝒞 := 𝒞) A.obj B.obj
  id := fun A => ratId A.obj
  comp := fun m n => ratComp m n
  id_comp := fun m => ratComp_id_left m
  comp_id := fun m => ratComp_id_right m
  assoc := fun m n p => ratComp_assoc m n p

end CatInstance

/-! ### §1.48  The localisation functor `T_𝒟 : 𝒞 → A[denseMonos⁻¹]` and its faithfulness

  `T_𝒟` is identity-on-objects (`Rat 𝒞 := 𝒞`) and sends `f` to `locMap f = [A ←id— A —f→ B]`.
  It is a functor (`map_id` by `rfl`; `map_comp` by the pullback-against-identity roof
  `locMap_comp_equiv`) and — crucially for §1.547 — **FAITHFUL for the all-monics dense class**,
  with NO §1.547 pairs-refinement needed: if `locMap f = locMap g` then a common mono roof `r`
  with `r ≫ id = r' ≫ id` forces `r = r'` (it is mono, being in `denseMonos`), and `r ≫ f =
  r ≫ g` then cancels `r` to give `f = g`. -/

section Localisation
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- `T_𝒟 (f ≫ g) ≈ T_𝒟 f ∘ T_𝒟 g` at the fraction level: pullback of `f` against `id`
    re-bases to the identity-denominator span of `f ≫ g`. -/
theorem locMap_comp_equiv {𝒟 : DenseClass 𝒞} {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) :
    FractionEquiv
      (compFraction 𝒟 (locFraction 𝒟 f) (locFraction 𝒟 g))
      (locFraction 𝒟 (f ≫ g)) := by
  let Q := (HasPullbacks.has (locFraction 𝒟 f).num (locFraction 𝒟 g).denom).cone
  -- square: `Q.π₁ ≫ f = Q.π₂ ≫ id_B = Q.π₂`
  have hw : Q.π₁ ≫ f = Q.π₂ := by
    have := Q.w; simp only [locFraction, Cat.comp_id] at this; exact this
  refine ⟨Q.pt, Cat.id Q.pt, Q.π₁, ?_, ?_, ?_⟩
  · show 𝒟.mem (Cat.id Q.pt ≫
      (compFraction 𝒟 (locFraction 𝒟 f) (locFraction 𝒟 g)).denom)
    rw [Cat.id_comp]
    exact (compFraction 𝒟 (locFraction 𝒟 f) (locFraction 𝒟 g)).denom_dense
  · show Cat.id Q.pt ≫ (Q.π₁ ≫ (locFraction 𝒟 f).denom)
        = Q.π₁ ≫ (locFraction 𝒟 (f ≫ g)).denom
    simp only [locFraction, Cat.comp_id, Cat.id_comp]
  · show Cat.id Q.pt ≫ (Q.π₂ ≫ (locFraction 𝒟 g).num)
        = Q.π₁ ≫ (locFraction 𝒟 (f ≫ g)).num
    simp only [locFraction, Cat.id_comp]
    rw [← Cat.assoc, hw]

/-- **§1.48 — `T_𝒟` is a functor** `𝒞 → A[denseMonos⁻¹]` (identity on objects, `f ↦ locMap f`).
    `map_id` is definitional (`idFraction = locFraction id`); `map_comp` is `locMap_comp_equiv`. -/
def locFunctor : Functor 𝒞 (Rat 𝒞) where
  obj A := Rat.mk (𝒞 := 𝒞) A
  map {A B} f := locMap f
  map_id A := by
    show locMap (Cat.id A) = ratId A
    rfl
  map_comp {A B C} f g := by
    show locMap (f ≫ g) = ratComp (locMap f) (locMap g)
    exact Quotient.sound (fractionEquiv_symm (denseMonos 𝒞) (locMap_comp_equiv f g))

/-! ### §1.48/§1.547  THE GENERIC RATIONAL CATEGORY `ratCatOf 𝒟 hD` over a `DenseRoof` class

  The R2 `RatHom`/`ratCat`/`locFunctor` fix `denseMonos`.  We now repackage the WHOLE pipeline over
  an ARBITRARY `(𝒟 : DenseClass 𝒞) (hD : DenseRoof 𝒟)`, using ONLY the dense-class interface
  (`iso_mem`/`comp_mem`/`pb_mem`) plus the §1.48 right-cancellation `DenseRoof.roof_mem`.  Every
  ingredient — `fractionEquiv_refl/symm/trans`, `compFraction`, the congruences, the unit/assoc laws,
  `locMap_comp_equiv` — is already generic; here we just glue the `Quotient` / `Cat` / `Functor`.
  `denseMonos` recovers the R2 `ratCat`/`locFunctor` (`denseMonos_monic.toDenseRoof`); `pairDenseClass`
  (once a `DenseRoof` witness is supplied) gives `A* = Â[pairDense⁻¹]`. -/

section GenericRat
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- The setoid on fraction spans for a general `DenseRoof` class. -/
def fractionSetoidOf {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B : 𝒞} :
    Setoid (Fraction 𝒟 A B) where
  r := FractionEquiv
  iseqv := ⟨fractionEquiv_refl 𝒟, fractionEquiv_symm 𝒟, fractionEquiv_trans hD⟩

/-- Hom-set of `A[𝒟⁻¹]` for a general `DenseRoof` class: equivalence classes of fraction spans. -/
def RatHomOf {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) (A B : 𝒞) : Type u :=
  Quotient (fractionSetoidOf hD (A := A) (B := B))

/-- Identity morphism of `A[𝒟⁻¹]`. -/
def ratIdOf {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) (A : 𝒞) : RatHomOf hD A A :=
  Quotient.mk _ (idFraction 𝒟 A)

/-- Localisation of an arrow `f : A → B`. -/
def locMapOf {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B : 𝒞} (f : A ⟶ B) : RatHomOf hD A B :=
  Quotient.mk _ (locFraction 𝒟 f)

/-- Composition in `A[𝒟⁻¹]`, well-defined by the (generic) LEFT/RIGHT congruences + transitivity. -/
def ratCompOf {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B C : 𝒞}
    (m : RatHomOf hD A B) (n : RatHomOf hD B C) : RatHomOf hD A C :=
  Quotient.lift₂ (fun f g => Quotient.mk _ (compFraction 𝒟 f g))
    (by
      intro f g f' g' hf hg
      apply Quotient.sound
      exact fractionEquiv_trans hD
        (compFraction_congr_left hD g hf) (compFraction_congr_right hD f' hg))
    m n

theorem ratCompOf_id_left {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B : 𝒞}
    (m : RatHomOf hD A B) : ratCompOf hD (ratIdOf hD A) m = m := by
  refine Quotient.inductionOn m (fun f => ?_)
  exact Quotient.sound (compFraction_idFraction_left f)

theorem ratCompOf_id_right {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B : 𝒞}
    (m : RatHomOf hD A B) : ratCompOf hD m (ratIdOf hD B) = m := by
  refine Quotient.inductionOn m (fun f => ?_)
  exact Quotient.sound (compFraction_idFraction_right f)

theorem ratCompOf_assoc {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) {A B C D : 𝒞}
    (m : RatHomOf hD A B) (n : RatHomOf hD B C) (p : RatHomOf hD C D) :
    ratCompOf hD (ratCompOf hD m n) p = ratCompOf hD m (ratCompOf hD n p) := by
  refine Quotient.inductionOn₃ m n p (fun f g h => ?_)
  exact Quotient.sound (compFraction_assoc f g h)

/-- Object carrier of `A[𝒟⁻¹]` for a general `DenseRoof` class (one-field wrapper of `𝒞`'s objects,
    keyed by the class so `Cat` resolution does not collapse). -/
structure RatObj {𝒟 : DenseClass 𝒞} (_hD : DenseRoof 𝒟) where mk :: (obj : 𝒞)

/-- **§1.48/§1.547 — the generic rational category `A[𝒟⁻¹]`** for any `DenseRoof` class `𝒟`.
    Objects = `𝒞`'s objects; homs = `RatHomOf` (fraction quotients); comp = `ratCompOf`; id =
    `ratIdOf`.  The three laws are the lifted generic `compFraction` unit/assoc laws.  Sorry-free. -/
def ratCatOf {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) : Cat.{u} (RatObj hD) where
  Hom A B := RatHomOf hD A.obj B.obj
  id := fun A => ratIdOf hD A.obj
  comp := fun m n => ratCompOf hD m n
  id_comp := fun m => ratCompOf_id_left hD m
  comp_id := fun m => ratCompOf_id_right hD m
  assoc := fun m n p => ratCompOf_assoc hD m n p

/-- **§1.48/§1.547 — the localisation functor `T_𝒟 : 𝒞 → A[𝒟⁻¹]`** for any `DenseRoof` class.
    Identity on objects, `f ↦ locMapOf f`; `map_id` definitional, `map_comp` is `locMap_comp_equiv`. -/
def locFunctorOf {𝒟 : DenseClass 𝒞} (hD : DenseRoof 𝒟) :
    @Functor 𝒞 (RatObj hD) _ (ratCatOf hD) :=
  letI : Cat.{u} (RatObj hD) := ratCatOf hD
  { obj := fun A => RatObj.mk (_hD := hD) A
    map := fun {A B} f => locMapOf hD f
    map_id := fun A => by
      show locMapOf hD (Cat.id A) = ratIdOf hD A
      rfl
    map_comp := fun {A B C} f g => by
      show locMapOf hD (f ≫ g) = ratCompOf hD (locMapOf hD f) (locMapOf hD g)
      exact Quotient.sound (fractionEquiv_symm 𝒟 (locMap_comp_equiv f g)) }

end GenericRat

/-! ### §1.547 FAITHFULNESS FINDING (machine-checked obstruction; nothing faked)

  The repo's `Faithful F := Embedding F ∧ (∀ f, IsIso (map f) → IsIso f)` — i.e. injective on
  hom-sets AND conservative.  For the localisation `T_𝒟` at the **all-monics** dense class
  `denseMonos`, BOTH conjuncts FAIL, and the failures are structural, not a missing proof:

  • **`Embedding` (hom-injectivity) FAILS.**  `locMap f = locMap g` produces a roof `r₁,r₂ : R → A`
    with `r₁ = r₂` (the `id`-denominators agree), `r₁` MONIC (its dense denom `r₁ ≫ id = r₁` is in
    `denseMonos`), and `r₁ ≫ f = r₁ ≫ g` (the numerators agree).  To conclude `f = g` one must
    cancel `r₁` on the LEFT — that needs `r₁` EPIC, but `denseMonos` only gives `r₁` MONIC.  A monic
    that is not epic does not cancel, so `T_𝒟` need not separate `f` from `g`.

  • **conservativity FAILS.**  `T_𝒟` inverts every dense monic by construction; a non-iso monic `m`
    has `IsIso (locMap m)` while `m` is not iso.

  CONSEQUENCE for `ratCap S : CapStep S`: the `CapStep.stepFaithful` field (this repo's `Faithful`)
  is NOT dischargeable for `step = T_𝒟` at the all-monics class.  §1.547's REFINEMENT of the dense
  class — invert only the *specific* dense monics forced by the product-slice embeddings (the
  "pairs" refinement), each of which is there an ISO of the localised category whose backward leg
  is genuinely cancellable — is REQUIRED before `stepFaithful` holds.  The all-monics route built
  here delivers the rational *category* + localisation *functor* (Sorry-free), but the conservative
  *faithful* step, hence the full `CapStep`, is gated on that refined dense class. -/

end Localisation

/-! ## §1.547  THE PAIRS CATEGORY `Â` AND ITS REFINED DENSE CLASS (milestone R3)

  R2 found that localising at ALL monics is not faithful: a common dense roof leg `r` is
  only MONIC, and cancelling it on the LEFT (to separate `f` from `g`) needs `r` EPIC.
  §1.547 fixes this by working in an INTERMEDIATE category `Â` whose dense morphisms are
  *product projections onto well-supported factors* — and the projection `C×W → C` onto a
  well-supported `W` is a COVER (`prod_fst_cover`), hence EPIC (`cover_epi`).  So the refined
  dense roof legs ARE left-cancellable, and the localisation `Â → Â[dense⁻¹]` is FAITHFUL.

  ── Objects of `Â` (§1.547) ────────────────────────────────────────────────────
  A pair `(A, F)`, `F` a finite set of morphisms from `A` to DISTINCT, WELL-SUPPORTED
  targets.  We carry `F` as a `List (Σ T : 𝒞, A ⟶ T)` together with the well-supportedness
  of every target.  `F°` (`PairObj.targets`) is the list of targets.

  ── Morphisms of `Â` (§1.547) ──────────────────────────────────────────────────
  `(A₁,F₁) → (A₂,F₂)` is a `𝒞`-morphism `g : A₁ → A₂` with `F₂° ⊆ F₁°` and the compatibility
  square: for every factor `f : A₂ → B` in `F₂`, the corresponding factor `f' : A₁ → B` in
  `F₁` (same target `B`) satisfies `g ≫ f = f'`.  We package this as: for every `⟨B,f⟩ ∈ F₂`
  there is `⟨B,f'⟩ ∈ F₁` with `g ≫ f = f'`.  The hom is DETERMINED by `g` (`PairHom.ext`),
  so the forgetful functor `Â → A`, `g ↦ g`, is faithful by construction. -/

section PairsCategory
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-- **§1.547 object of `Â`** — a pair `(A, F)`: a base object `A`, a finite list `F` of
    morphisms out of `A` to DISTINCT well-supported targets.  `targets` is `F°`.

    The `distinct` field is Freyd's §1.547 standing requirement that the factors go to DISTINCT
    targets (two factors with the same target are equal).  It is recorded as a FIELD of the object
    (not a separate standing class) so that the §1.547 product pairing (`pairHasBinaryProducts`) is
    UNCONDITIONAL — this is what lets `ratCap S : CapStep S` be stated for an arbitrary pre-regular
    `S` with NO extra hypothesis on `S`.  See `pairHasBinaryProducts`/the DISTINCTNESS-GATE note. -/
structure PairObj (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] where
  A : 𝒞
  F : List (Σ T : 𝒞, A ⟶ T)
  wsupp : ∀ p ∈ F, WellSupported p.1
  distinct : ∀ r ∈ F, ∀ r' ∈ F, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2

/-- `F°` — the list of TARGETS of the factors of an object of `Â`. -/
def PairObj.targets (X : PairObj 𝒞) : List 𝒞 := X.F.map (·.1)

/-- **§1.547 morphism of `Â`** — `(A₁,F₁) → (A₂,F₂)`: a `𝒞`-arrow `g : A₁ → A₂` such that
    every factor of `F₂` pulls back through `g` to a factor of `F₁` to the SAME target
    (`F₂° ⊆ F₁°` with the compatibility square `g ≫ f = f'`). -/
structure PairHom (X Y : PairObj 𝒞) where
  g : X.A ⟶ Y.A
  compat : ∀ p ∈ Y.F, ∃ q ∈ X.F, ∃ h : q.1 = p.1, g ≫ p.2 = h ▸ q.2

/-- A `PairHom` is DETERMINED by its underlying `𝒞`-arrow `g` (the compatibility is a `Prop`).
    This is what makes the forgetful functor `Â → A` faithful. -/
@[ext]
theorem PairHom.ext {X Y : PairObj 𝒞} {a b : PairHom X Y} (h : a.g = b.g) : a = b := by
  obtain ⟨ag, _⟩ := a; obtain ⟨bg, _⟩ := b; cases h; rfl

/-- Identity `PairHom`: underlying `id`, compatibility is `id ≫ f = f`. -/
def PairHom.id (X : PairObj 𝒞) : PairHom X X :=
  ⟨Cat.id X.A, fun p hp => ⟨p, hp, rfl, Cat.id_comp p.2⟩⟩

/-- Composition of `PairHom`s (diagram order): underlying `g₁ ≫ g₂`; compatibility chains
    the two factorisations through the shared middle factor.  For `p ∈ Z.F`, `b` gives
    `q ∈ Y.F` with `g₂ ≫ p = q` (same target), and `a` gives `r ∈ X.F` with `g₁ ≫ q = r`;
    then `(g₁ ≫ g₂) ≫ p = g₁ ≫ q = r`. -/
def PairHom.comp {X Y Z : PairObj 𝒞} (a : PairHom X Y) (b : PairHom Y Z) : PairHom X Z where
  g := a.g ≫ b.g
  compat p hp := by
    obtain ⟨q, hq, hqt, hqe⟩ := b.compat p hp
    obtain ⟨r, hr, hrt, hre⟩ := a.compat q hq
    refine ⟨r, hr, hrt.trans hqt, ?_⟩
    -- (a.g ≫ b.g) ≫ p.2 = a.g ≫ (b.g ≫ p.2) = a.g ≫ (hqt ▸ q.2) = (hrt.trans hqt) ▸ r.2
    cases p; cases q; cases r
    cases hqt; cases hrt
    simp only at hqe hre ⊢
    rw [Cat.assoc, hqe, hre]

/-- **§1.547 — `Â` is a category.**  Objects `PairObj`; homs `PairHom` (determined by the
    underlying `𝒞`-arrow); composition/identity inherited from `𝒞`.  All laws follow from
    `PairHom.ext` + the corresponding `Cat` laws of `𝒞` on the underlying arrows. -/
instance pairsCat : Cat.{u} (PairObj 𝒞) where
  Hom := PairHom
  id := PairHom.id
  comp a b := a.comp b
  id_comp a := PairHom.ext (Cat.id_comp a.g)
  comp_id a := PairHom.ext (Cat.comp_id a.g)
  assoc a b c := PairHom.ext (Cat.assoc a.g b.g c.g)

/-- The FORGETFUL functor `Â → A`, `(A,F) ↦ A`, `g ↦ g`.  Underlying-arrow extraction. -/
def pairForget : Functor (PairObj 𝒞) 𝒞 where
  obj X := X.A
  map a := a.g
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **§1.547 full embedding `A ↪ Â`**, on objects: `A ↦ (A, ∅)` (no recorded factors). -/
def pairEmbedObj (A : 𝒞) : PairObj 𝒞 where
  A := A
  F := []
  wsupp := by intro p hp; exact absurd hp List.not_mem_nil
  distinct := by intro r hr; exact absurd hr List.not_mem_nil

/-- **§1.547 full embedding `A ↪ Â`**, on arrows: `g ↦ ⟨g, vacuous⟩` (the target `(B,∅)` has no
    factors, so compatibility is vacuous).  A genuine functor (`map_id`/`map_comp` by `PairHom.ext`).
    "A full embedding of `A` into `Â` is obtained by sending `A` to `(A,∅)`" (§1.547). -/
def pairEmbed : Functor 𝒞 (PairObj 𝒞) where
  obj := pairEmbedObj
  map g := ⟨g, fun _ hp => absurd hp List.not_mem_nil⟩
  map_id _ := PairHom.ext rfl
  map_comp _ _ := PairHom.ext rfl

/-- A `PairHom`'s codomain targets are a SUBSET of its domain targets (`Y° ⊆ X°`).  Immediate from
    compat: every `p ∈ Y.F` has a matching `q ∈ X.F` of the SAME target, so `p.1 = q.1 ∈ X°`. -/
theorem pairHom_targets_subset {X Y : PairObj 𝒞} (m : PairHom X Y) :
    ∀ T ∈ Y.targets, T ∈ X.targets := by
  intro T hT
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hT
  obtain ⟨q, hq, hqt, _⟩ := m.compat p hp
  exact List.mem_map.2 ⟨q, hq, hqt⟩

/-- The §1.547 embedding `A ↪ Â` is an `Embedding` (faithful on homs): a `PairHom` is determined by
    its underlying `.g`, which is exactly the input arrow (`PairHom.ext`). -/
theorem pairEmbed_embedding : Embedding (pairEmbed (𝒞 := 𝒞)) :=
  fun _ _ h => congrArg PairHom.g h

/-- The §1.547 embedding `A ↪ Â` is FULL: every `Â`-arrow `(A,∅) → (B,∅)` is `pairEmbed.map` of its
    underlying `.g` (no compatibility constraints between empty factor sets). -/
theorem pairEmbed_full : Full (pairEmbed (𝒞 := 𝒞)) :=
  fun {A B} (a : PairHom (pairEmbedObj A) (pairEmbedObj B)) => ⟨a.g, PairHom.ext rfl⟩

/-- The §1.547 embedding `A ↪ Â` is FAITHFUL (full embedding ⟹ faithful, §1.33). -/
theorem pairEmbed_faithful : Faithful (pairEmbed (𝒞 := 𝒞)) :=
  full_embedding_faithful (pairEmbed (𝒞 := 𝒞)) pairEmbed_embedding pairEmbed_full

/-- The forgetful functor `Â → A` is an `Embedding` (faithful on homs): a `PairHom` is
    determined by its `.g` (`PairHom.ext`). -/
theorem pairForget_embedding : Embedding (pairForget (𝒞 := 𝒞)) :=
  fun _ _ h => PairHom.ext h

/-! ### §1.547  The refined DENSE class on `Â`

  Book: `x : (A₁,F₁) → (A₂,F₂)` is DENSE in `Â` when `x` together with the SURVIVING factors
  `S = {f ∈ F₁ | f° ∉ F₂°}` forms a PRODUCT DIAGRAM in `A` (§1.425) — i.e. `A₁` is the product
  of `A₂` with the targets `S°` of the surviving factors, `x.g` being the projection onto `A₂`.

  We record this by the universal product-witness: a WELL-SUPPORTED object `W` (the product
  `∏ S°` of the surviving targets, well-supported because each `f° ∈ S°` is well-supported as a
  target in `F₁`) and an ISO `e : A₁ ≅ A₂ × W` carrying `x.g` to `fst : A₂ × W → A₂`.  This is
  the §1.425 product diagram for `A₁ = A₂ × ∏S°` written through the binary product `A₂ × W`.

  Crucial consequence (`pairDense_cover`): the underlying `x.g` is `e.hom ≫ fst` with `W`
  well-supported, hence `fst` a COVER (`prod_fst_cover`) and `x.g` a cover (`cover_precomp_iso`).
  Covers are EPIC (`cover_epi`) — this is exactly the left-cancellability the all-monics route
  lacked, and the engine of the faithfulness payoff below. -/

/-- **§1.547 DENSE morphism of `Â`.**  `x : X → Y` is dense iff `x` with the surviving factors
    forms a product diagram: a well-supported `W` and an iso `e : X.A ≅ Y.A × W` carrying `x.g`
    to `fst`.  (`W = ∏(surviving targets)`; the survivors are `e ≫ snd ≫ projections`.) -/
structure PairDense {X Y : PairObj 𝒞} (x : PairHom X Y) where
  W       : 𝒞
  wsupp   : WellSupported W
  e       : X.A ⟶ prod Y.A W
  einv    : prod Y.A W ⟶ X.A
  e_iso₁  : e ≫ einv = Cat.id X.A
  e_iso₂  : einv ≫ e = Cat.id (prod Y.A W)
  proj    : e ≫ (fst : prod Y.A W ⟶ Y.A) = x.g
  -- §1.547 "x TOGETHER WITH the surviving factors forms a product diagram": `W` is the product of
  -- the SURVIVING targets `{f° | f ∈ F₁, f° ∉ F₂°}`, and the `snd`-component `e ≫ snd : X.A → W`
  -- packages those surviving factors of `X`.  The single content the monic proof needs is that this
  -- `W`-component is PINNED by `X`'s factor data: any two `Â`-maps into `X` agree after `e ≫ snd`,
  -- because each surviving factor is in `X.F` and a `PairHom` is compatible with every factor of its
  -- codomain (distinctness of `X.F` forces the same witness for both maps).  This is exactly the
  -- product-diagram content that makes dense ⟹ MONIC in `Â` (`pairDense_monic`), and it is stable
  -- under composition (`pairDense_comp`).
  /-- the `W`-component of the iso is PINNED by `X`'s factor data: any two parallel `Â`-maps `a,b`
      into `X` agree after `e ≫ snd : X.A → W`.  (Equivalently: `W = ∏(surviving targets)` and each
      surviving factor lies in `X.F`, so compatibility pins both maps to the same value.) -/
  survPinned : ∀ {Z : PairObj 𝒞} (a b : PairHom Z X),
    a.g ≫ e ≫ (snd : prod Y.A W ⟶ W) = b.g ≫ e ≫ (snd : prod Y.A W ⟶ W)
  /-- **§1.547 — the GLOBAL surviving-factor decomposition.**  `W` is (a retract of) the product
      `∏surv` of an explicit list `surv` of well-supported surviving targets, via the round-trip
      `(wf, wg)`. -/
  surv    : List 𝒞
  survWS  : ∀ T ∈ surv, WellSupported T
  wf      : W ⟶ listProd surv
  wg      : listProd surv ⟶ W
  wfg     : wf ≫ wg = Cat.id W
  wgf     : wg ≫ wf = Cat.id (listProd surv)
  /-- **§1.547 — every factor of `X` is either Y-DERIVED or a SURVIVOR.**  Each `f ∈ X.F` either
      factors through `x.g` to a matching factor `gY ∈ Y.F` of the SAME target (the "left" disjunct
      — `f° ∈ Y.F°`), or it is a SURVIVOR pinned by a GLOBAL coordinate `k : Fin surv.length` of the
      product `∏surv`: `f.2 = e ≫ snd ≫ wf ≫ (listProdProj surv k)`.  Unlike the per-factor retract,
      this names ALL survivors as coordinates of one product, so MULTIPLE collided coordinates can be
      split off simultaneously (needed by the pullback proof). -/
  factorSplit : ∀ f ∈ X.F,
      (∃ gY ∈ Y.F, ∃ h : f.1 = gY.1, f.2 = x.g ≫ (h ▸ gY.2))
    ∨ (∃ k : Fin surv.length, ∃ h : f.1 = surv.get k,
         f.2 = e ≫ (snd : prod Y.A W ⟶ W) ≫ wf ≫ (h ▸ listProdProj surv k))
  /-- **§1.547 standing condition — the surviving targets are NOT in the codomain.**  Each surviving
      target `surv.get k` lies OUTSIDE `Y°` (`Y.targets`): a survivor is by definition a factor of `X`
      whose target is not already a target of `Y` (`f° ∉ F₂°`).  This is what makes the survivors the
      genuine "extra" product factors split off by `x`. -/
  survDistinct : ∀ k : Fin surv.length, surv.get k ∉ Y.targets
  /-- **§1.547 — every surviving target IS a target of the domain `X`.**  A survivor is a coordinate of
      `W = ∏surv` pinned to an `X`-factor (`factorSplit`'s survivor branch), so its target lies in
      `X°` (`X.targets`).  Together with `survDistinct`, the survivors are exactly the `X`-factor
      targets that disappear in `Y`. -/
  survInX : ∀ k : Fin surv.length, surv.get k ∈ X.targets

/-- **§1.547 — every dense morphism's underlying arrow is a COVER.**  `x.g = e ≫ fst` with
    `e` an iso and `fst : Y.A × W → Y.A` a cover (`W` well-supported, `prod_fst_cover`); a cover
    pre-composed with an iso is a cover (`cover_precomp_iso`).  This is the left-cancellable
    "product projection" property §1.547 uses. -/
theorem pairDense_cover [PullbacksTransferCovers 𝒞] {X Y : PairObj 𝒞} {x : PairHom X Y}
    (d : PairDense x) : Cover x.g := by
  rw [← d.proj]
  exact cover_precomp_iso ⟨d.einv, d.e_iso₁, d.e_iso₂⟩ (prod_fst_cover d.wsupp)

/-- **§1.547 — every dense morphism is EPIC in `Â`.**  This is the decisive cancellability the
    all-monics route (R2) lacked.  For `Â`-arrows `a, b : Y → Z`, if `x.comp a = x.comp b` then
    their underlying arrows satisfy `x.g ≫ a.g = x.g ≫ b.g`; `x.g` is a COVER (`pairDense_cover`)
    hence EPIC (`cover_epi`), giving `a.g = b.g`, hence `a = b` by `PairHom.ext`. -/
theorem pairDense_epi [PullbacksTransferCovers 𝒞] {X Y : PairObj 𝒞} {x : PairHom X Y}
    (d : PairDense x) {Z : PairObj 𝒞} (a b : PairHom Y Z) (hab : x.comp a = x.comp b) :
    a = b := by
  apply PairHom.ext
  apply cover_epi (pairDense_cover d)
  have : (x.comp a).g = (x.comp b).g := congrArg PairHom.g hab
  simpa [PairHom.comp] using this

/-! ### §1.547  Dense-class closure laws on `Â`

  We now verify the three §1.48/§1.547 dense-class axioms for `PairDense` (insofar as they do
  not require the full `HasPullbacks (PairObj 𝒞)` — pullbacks IN `Â` are an R4 construction).
  ISO ⟹ DENSE and DENSE closed under COMPOSITION are proven here Sorry-free; the pullback
  closure is stated with the precise obstruction (it needs `Â`'s own pullbacks). -/

/-- The identity is a COVER (any monic `m` it factors through is split-epic + monic = iso). -/
theorem cover_id (X : 𝒞) : Cover (Cat.id X) := by
  intro C m g hm hgm
  -- `g ≫ m = id` ⟹ `m` split epi; with `m` mono, `m` is iso: inverse `g`.
  refine ⟨g, ?_, hgm⟩
  -- `m ≫ g = id`: cancel mono `m` on right of `(m ≫ g) ≫ m = m ≫ (g ≫ m) = m ≫ id = id ≫ m`.
  apply hm
  rw [Cat.assoc, hgm, Cat.comp_id, Cat.id_comp]

/-- `1` (the terminator) is well-supported. -/
theorem wellSupported_one' : WellSupported (HasTerminal.one : 𝒞) := by
  show Cover (term (HasTerminal.one : 𝒞))
  rw [show term (HasTerminal.one : 𝒞) = Cat.id _ from term_uniq _ _]
  exact cover_id _

/-- **Joint monicity of the `listProd` projections.**  Two maps into `∏U` agree iff they agree
    after every factor projection `listProdProj U k`.  Iterated joint monicity: the head projection
    is `fst`, the tail projections are `snd ≫ listProdProj U k`, so agreement on all of them forces
    agreement after `fst` and (by induction) after `snd`. -/
theorem listProd_hom_ext {Z : 𝒞} : ∀ (U : List 𝒞) (u v : Z ⟶ listProd U),
    (∀ k : Fin U.length, u ≫ listProdProj U k = v ≫ listProdProj U k) → u = v
  | [], u, v, _ => HasTerminal.uniq u v
  | C :: U, u, v, h => by
      apply fst_snd_jointly_monic
      · exact h ⟨0, Nat.succ_pos _⟩
      · apply listProd_hom_ext U
        intro k
        have := h ⟨k.1 + 1, Nat.succ_lt_succ k.2⟩
        simpa [listProdProj, Cat.assoc] using this

/-- **`listProd` of an append splits as a binary product** (forward map).
    `listProd (l₁ ++ l₂) ⟶ prod (listProd l₁) (listProd l₂)`, by induction on `l₁`:
    `[]` ↦ `pair (term) id` (`listProd [] = 1`); `C::l₁` ↦ pull the head `fst` out and recurse on
    the tail with `snd`. -/
def listProdAppendHom : ∀ (l₁ l₂ : List 𝒞),
    listProd (l₁ ++ l₂) ⟶ prod (listProd l₁) (listProd l₂)
  | [],      l₂ => pair (term (listProd l₂)) (Cat.id (listProd l₂))
  | C :: l₁, l₂ =>
      pair (pair (fst : prod C (listProd (l₁ ++ l₂)) ⟶ C)
                 (snd ≫ listProdAppendHom l₁ l₂ ≫ fst))
           (snd ≫ listProdAppendHom l₁ l₂ ≫ snd)

/-- Inverse of `listProdAppendHom`: `prod (listProd l₁) (listProd l₂) ⟶ listProd (l₁ ++ l₂)`. -/
def listProdAppendInv : ∀ (l₁ l₂ : List 𝒞),
    prod (listProd l₁) (listProd l₂) ⟶ listProd (l₁ ++ l₂)
  | [],      _  => (snd : prod (listProd ([] : List 𝒞)) _ ⟶ _)
  | C :: l₁, l₂ =>
      pair (fst ≫ (fst : prod C (listProd l₁) ⟶ C))
           (pair (fst ≫ (snd : prod C (listProd l₁) ⟶ listProd l₁)) snd
              ≫ listProdAppendInv l₁ l₂)

theorem listProdAppend_hom_inv : ∀ (l₁ l₂ : List 𝒞),
    listProdAppendHom l₁ l₂ ≫ listProdAppendInv l₁ l₂ = Cat.id (listProd (l₁ ++ l₂))
  | [],      l₂ => by
      show pair (term (listProd l₂)) (Cat.id (listProd l₂)) ≫ snd = Cat.id _
      rw [snd_pair]
  | C :: l₁, l₂ => by
      show pair (pair (fst : prod C (listProd (l₁ ++ l₂)) ⟶ C)
                 (snd ≫ listProdAppendHom l₁ l₂ ≫ fst))
           (snd ≫ listProdAppendHom l₁ l₂ ≫ snd)
        ≫ listProdAppendInv (C :: l₁) l₂ = Cat.id _
      apply fst_snd_jointly_monic
      · show _ ≫ (fst : prod C (listProd (l₁ ++ l₂)) ⟶ C) = _
        rw [Cat.id_comp]
        unfold listProdAppendInv
        rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, fst_pair]
      · show _ ≫ (snd : prod C (listProd (l₁ ++ l₂)) ⟶ listProd (l₁ ++ l₂)) = _
        rw [Cat.id_comp]
        unfold listProdAppendInv
        rw [Cat.assoc, snd_pair]
        have hrec := listProdAppend_hom_inv l₁ l₂
        -- collapse `pair (pair fst (snd≫hom≫fst)) (snd≫hom≫snd) ≫ pair (fst≫snd) snd`
        -- to `snd ≫ hom l₁ l₂`, then `≫ inv = snd ≫ id = snd`.
        have hcollapse :
            pair (pair (fst : prod C (listProd (l₁ ++ l₂)) ⟶ C)
                     (snd ≫ listProdAppendHom l₁ l₂ ≫ fst))
                 (snd ≫ listProdAppendHom l₁ l₂ ≫ snd)
              ≫ pair (fst ≫ (snd : prod C (listProd l₁) ⟶ listProd l₁)) snd
            = snd ≫ listProdAppendHom l₁ l₂ := by
          apply fst_snd_jointly_monic
          · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, snd_pair, Cat.assoc]
          · rw [Cat.assoc, snd_pair, snd_pair, Cat.assoc]
        rw [← Cat.assoc, hcollapse, Cat.assoc, hrec, Cat.comp_id]

theorem listProdAppend_inv_hom : ∀ (l₁ l₂ : List 𝒞),
    listProdAppendInv l₁ l₂ ≫ listProdAppendHom l₁ l₂ = Cat.id (prod (listProd l₁) (listProd l₂))
  | [],      l₂ => by
      show (snd : prod (listProd ([] : List 𝒞)) _ ⟶ _)
          ≫ pair (term (listProd l₂)) (Cat.id (listProd l₂)) = Cat.id _
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, fst_pair, Cat.id_comp]; apply HasTerminal.uniq
      · rw [Cat.assoc, snd_pair, Cat.comp_id, Cat.id_comp]
  | C :: l₁, l₂ => by
      show listProdAppendInv (C :: l₁) l₂ ≫ listProdAppendHom (C :: l₁) l₂ = Cat.id _
      have hrec := listProdAppend_inv_hom l₁ l₂
      unfold listProdAppendHom listProdAppendInv
      apply fst_snd_jointly_monic
      · -- ≫ fst : recover prod C (listProd l₁)
        rw [Cat.assoc, fst_pair, Cat.id_comp]
        apply fst_snd_jointly_monic
        · -- ≫ fst : `inv ≫ fst = fst ≫ fst`
          rw [Cat.assoc, fst_pair, fst_pair]
        · -- ≫ snd : `inv ≫ (snd≫hom≫fst)`, use `inv l₁ ≫ hom l₁ = id`
          rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc,
              ← Cat.assoc (listProdAppendInv l₁ l₂), hrec, Cat.id_comp, fst_pair]
      · -- ≫ snd : recover listProd l₂; `inv ≫ (snd≫hom≫snd)`, use `inv l₁ ≫ hom l₁ = id`
        rw [Cat.assoc, snd_pair, Cat.id_comp, ← Cat.assoc, snd_pair, Cat.assoc,
          ← Cat.assoc (listProdAppendInv l₁ l₂), hrec, Cat.id_comp, snd_pair]

/-- Cast distributes over composition: `h ▸ (f ≫ g) = f ≫ (h ▸ g)`.
    Proved by `cases h; rfl`; used to push index-equality casts inside list-product projections. -/
private theorem cast_comp_hom {𝒞 : Type u} [Cat 𝒞] {X Y Z Z' : 𝒞} (h : Z = Z')
    (f : X ⟶ Y) (g : Y ⟶ Z) : (h ▸ (f ≫ g) : X ⟶ Z') = f ≫ (h ▸ g) := by
  cases h; rfl

/-- Cancel the codomain-cast of one factor against the (inverse) domain-cast of the next.
    The `cast`s introduced by `List.filter_cons` reduction in `listProdPartitionHom`/`Inv` are along
    the *same* object equality `P = Q`, one on the codomain and one on the domain, so they cancel and
    leave `A ≫ B` after transporting `B` back.  Proof irrelevance lets us match whatever proof terms
    `simp`'s `eq_mpr`/`cast` normalisation produces. -/
private theorem castObj_comp {𝒞 : Type u} [Cat 𝒞] {X Y P Q : 𝒞}
    (hPQ : P = Q) (h₁ : (X ⟶ P) = (X ⟶ Q)) (h₂ : (P ⟶ Y) = (Q ⟶ Y))
    (A : X ⟶ P) (B : P ⟶ Y) :
    cast h₁ A ≫ cast h₂ B = A ≫ B := by
  cases hPQ; rfl

/-- Cancel an outer pair of inverse object-casts (on the domain of the first factor and the codomain
    of the second) against the identity target: the structural round-trip `A ≫ B = id` transports. -/
private theorem castObj_idcomp {𝒞 : Type u} [Cat 𝒞] {M P Q : 𝒞}
    (hPQ : P = Q) (h₁ : (P ⟶ M) = (Q ⟶ M)) (h₂ : (M ⟶ P) = (M ⟶ Q))
    (A : P ⟶ M) (B : M ⟶ P) (hAB : A ≫ B = Cat.id P) :
    cast h₁ A ≫ cast h₂ B = Cat.id Q := by
  cases hPQ; simpa using hAB

/-- Push a domain-object cast on the first factor outward past a composition:
    `cast h₁ A ≫ g = cast h₂ (A ≫ g)`.  Both casts are along the same domain-object equality
    `hPQ : P = Q`; `cases hPQ` makes both `rfl`. -/
private theorem castDom_comp {𝒞 : Type u} [Cat 𝒞] {M N P Q : 𝒞}
    (hPQ : P = Q) (h₁ : (P ⟶ M) = (Q ⟶ M)) (h₂ : (P ⟶ N) = (Q ⟶ N))
    (A : P ⟶ M) (g : M ⟶ N) :
    cast h₁ A ≫ g = cast h₂ (A ≫ g) := by
  cases hPQ; rfl

/-- HEq form: a domain-object cast on the first factor is invisible up to HEq.
    `cast h₁ A ≫ g ≍ A ≫ g`, by `cases hPQ`. -/
private theorem castDom_comp_heq {𝒞 : Type u} [Cat 𝒞] {M N P Q : 𝒞}
    (hPQ : P = Q) (h₁ : (P ⟶ M) = (Q ⟶ M)) (A : P ⟶ M) (g : M ⟶ N) :
    HEq (cast h₁ A ≫ g) (A ≫ g) := by
  cases hPQ; rfl

/-- Postcomposition respects HEq of the first factor when the shared object `M` is fixed:
    `a ≍ b → a ≫ g ≍ b ≫ g`.  (`a : P ⟶ M`, `b : Q ⟶ M`, `g : M ⟶ N`; the codomain `M`
    of both factors is the SAME, only the domain differs.)  By `cases` on the domain equality
    extracted from the HEq. -/
private theorem comp_left_heq {𝒞 : Type u} [Cat 𝒞] {M N P Q : 𝒞}
    (hPQ : P = Q) (a : P ⟶ M) (b : Q ⟶ M) (g : M ⟶ N) (h : HEq a b) :
    HEq (a ≫ g) (b ≫ g) := by
  cases hPQ; cases h; rfl

/-- Precomposition respects HEq of the second factor when the shared object `M` is fixed:
    `a ≍ b → g ≫ a ≍ g ≫ b`.  (`a : M ⟶ P`, `b : M ⟶ Q`, `g : N ⟶ M`.)  By `cases` on the
    codomain equality. -/
private theorem comp_right_heq {𝒞 : Type u} [Cat 𝒞] {M N P Q : 𝒞}
    (hPQ : P = Q) (g : N ⟶ M) (a : M ⟶ P) (b : M ⟶ Q) (h : HEq a b) :
    HEq (g ≫ a) (g ≫ b) := by
  cases hPQ; cases h; rfl

/-- `fst` is HEq-stable under reshaping its factors: `A = A' → B = B' → fst ≍ fst`. -/
private theorem fst_heq {𝒞 : Type u} [Cat 𝒞] [HasBinaryProducts 𝒞] {A A' B B' : 𝒞}
    (hA : A = A') (hB : B = B') :
    HEq (fst : prod A B ⟶ A) (fst : prod A' B' ⟶ A') := by
  cases hA; cases hB; rfl

/-- `snd` is HEq-stable under reshaping its factors: `A = A' → B = B' → snd ≍ snd`. -/
private theorem snd_heq {𝒞 : Type u} [Cat 𝒞] [HasBinaryProducts 𝒞] {A A' B B' : 𝒞}
    (hA : A = A') (hB : B = B') :
    HEq (snd : prod A B ⟶ B) (snd : prod A' B' ⟶ B') := by
  cases hA; cases hB; rfl

/-- **`listProd` splits along a `Bool` filter-partition** (forward map):
    `listProd l ⟶ prod (listProd (l.filter p)) (listProd (l.filter ¬p))`.  By recursion on `l`,
    case-splitting on `p C` in the cons case: the head `C` joins the left block (`p C = true`) or
    the right block (`p C = false`), and the tail is split by the IH.  Structurally a re-association
    mirror of `listProdAppendHom`, the only difference being which side the head goes to. -/
def listProdPartitionHom (p : 𝒞 → Bool) : ∀ (l : List 𝒞),
    listProd l ⟶ prod (listProd (l.filter p)) (listProd (l.filter (fun a => !p a)))
  | [] => pair (term (HasTerminal.one : 𝒞)) (term (HasTerminal.one : 𝒞))
  | C :: l => by
      match hpC : p C with
      | true =>
          simp only [List.filter_cons, hpC, Bool.not_true, if_true]
          exact pair (pair (fst : prod C (listProd l) ⟶ C)
                       (snd ≫ listProdPartitionHom p l ≫ fst))
                     (snd ≫ listProdPartitionHom p l ≫ snd)
      | false =>
          simp only [List.filter_cons, hpC, Bool.not_false, if_true]
          exact pair (snd ≫ listProdPartitionHom p l ≫ fst)
                     (pair (fst : prod C (listProd l) ⟶ C)
                       (snd ≫ listProdPartitionHom p l ≫ snd))

/-- Inverse of `listProdPartitionHom`. -/
def listProdPartitionInv (p : 𝒞 → Bool) : ∀ (l : List 𝒞),
    prod (listProd (l.filter p)) (listProd (l.filter (fun a => !p a))) ⟶ listProd l
  | [] => term _
  | C :: l => by
      match hpC : p C with
      | true =>
          simp only [List.filter_cons, hpC, Bool.not_true, if_true]
          exact pair (fst ≫ (fst : prod C (listProd (l.filter p)) ⟶ C))
                     (pair (fst ≫ (snd : prod C (listProd (l.filter p)) ⟶ _)) snd
                        ≫ listProdPartitionInv p l)
      | false =>
          simp only [List.filter_cons, hpC, Bool.not_false, if_true]
          exact pair (snd ≫ (fst : prod C (listProd (l.filter (fun a => !p a))) ⟶ C))
                     (pair fst (snd ≫ (snd : prod C (listProd (l.filter (fun a => !p a))) ⟶ _))
                        ≫ listProdPartitionInv p l)

theorem listProdPartition_hom_inv (p : 𝒞 → Bool) : ∀ (l : List 𝒞),
    listProdPartitionHom p l ≫ listProdPartitionInv p l = Cat.id (listProd l)
  | [] => by apply HasTerminal.uniq
  | C :: l => by
      have hrec := listProdPartition_hom_inv p l
      show listProdPartitionHom p (C :: l) ≫ listProdPartitionInv p (C :: l) = _
      unfold listProdPartitionHom listProdPartitionInv
      split <;> rename_i heq <;> simp only [eq_mpr_eq_cast]
      · -- p C = true : head `C` joined the left block
        rw [castObj_comp (by simp [heq])]
        apply fst_snd_jointly_monic
        · show _ ≫ (fst : prod C (listProd l) ⟶ C) = _
          rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, fst_pair, Cat.id_comp]
        · show _ ≫ (snd : prod C (listProd l) ⟶ listProd l) = _
          rw [Cat.assoc, snd_pair, Cat.id_comp]
          have hcollapse :
              pair (pair (fst : prod C (listProd l) ⟶ C)
                       (snd ≫ listProdPartitionHom p l ≫ fst))
                   (snd ≫ listProdPartitionHom p l ≫ snd)
                ≫ pair (fst ≫ (snd : prod C (listProd (l.filter p)) ⟶ _)) snd
              = snd ≫ listProdPartitionHom p l := by
            apply fst_snd_jointly_monic
            · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, snd_pair, Cat.assoc]
            · rw [Cat.assoc, snd_pair, snd_pair, Cat.assoc]
          rw [← Cat.assoc, hcollapse, Cat.assoc, hrec, Cat.comp_id]
      · -- p C = false : head `C` joined the right block
        rw [castObj_comp (by simp [heq])]
        apply fst_snd_jointly_monic
        · show _ ≫ (fst : prod C (listProd l) ⟶ C) = _
          rw [Cat.assoc, fst_pair, ← Cat.assoc, snd_pair, fst_pair, Cat.id_comp]
        · show _ ≫ (snd : prod C (listProd l) ⟶ listProd l) = _
          rw [Cat.assoc, snd_pair, Cat.id_comp]
          have hcollapse :
              pair (snd ≫ listProdPartitionHom p l ≫ fst)
                   (pair (fst : prod C (listProd l) ⟶ C)
                     (snd ≫ listProdPartitionHom p l ≫ snd))
                ≫ pair fst (snd ≫ (snd : prod C (listProd (l.filter (fun a => !p a))) ⟶ _))
              = snd ≫ listProdPartitionHom p l := by
            apply fst_snd_jointly_monic
            · rw [Cat.assoc, fst_pair, fst_pair, Cat.assoc]
            · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, snd_pair, Cat.assoc]
          rw [← Cat.assoc, hcollapse, Cat.assoc, hrec, Cat.comp_id]

theorem listProdPartition_inv_hom (p : 𝒞 → Bool) : ∀ (l : List 𝒞),
    listProdPartitionInv p l ≫ listProdPartitionHom p l
      = Cat.id (prod (listProd (l.filter p)) (listProd (l.filter (fun a => !p a))))
  | [] => by
      apply fst_snd_jointly_monic
      · apply HasTerminal.uniq
      · apply HasTerminal.uniq
  | C :: l => by
      have hrec := listProdPartition_inv_hom p l
      show listProdPartitionInv p (C :: l) ≫ listProdPartitionHom p (C :: l) = _
      unfold listProdPartitionHom listProdPartitionInv
      split <;> rename_i heq <;> simp only [eq_mpr_eq_cast]
      · -- p C = true
        refine castObj_idcomp (by simp [heq]) _ _ _ _ ?_
        apply fst_snd_jointly_monic
        · rw [Cat.assoc, fst_pair, Cat.id_comp]
          apply fst_snd_jointly_monic
          · rw [Cat.assoc, fst_pair, fst_pair]
          · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc,
                ← Cat.assoc (listProdPartitionInv p l), hrec, Cat.id_comp, fst_pair]
        · rw [Cat.assoc, snd_pair, Cat.id_comp, ← Cat.assoc, snd_pair, Cat.assoc,
              ← Cat.assoc (listProdPartitionInv p l), hrec, Cat.id_comp, snd_pair]
      · -- p C = false
        refine castObj_idcomp (by simp [heq]) _ _ _ _ ?_
        apply fst_snd_jointly_monic
        · rw [Cat.assoc, fst_pair, Cat.id_comp, ← Cat.assoc, snd_pair, Cat.assoc,
              ← Cat.assoc (listProdPartitionInv p l), hrec, Cat.id_comp, fst_pair]
        · rw [Cat.assoc, snd_pair, Cat.id_comp]
          apply fst_snd_jointly_monic
          · rw [Cat.assoc, fst_pair, fst_pair]
          · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc,
                ← Cat.assoc (listProdPartitionInv p l), hrec, Cat.id_comp, snd_pair]

/-- `listProdAppendInv` then a projection into the FIRST block `l₁` is `fst ≫ (l₁'s projection)`.
    The codomain `(l₁++l₂).get ⟨k,_⟩` equals `l₁.get k` (prefix index), carried by `h`; in each
    pattern case the cast `h ▸` is trivially eliminated. -/
theorem listProdAppendInv_projL :
    ∀ (l₁ l₂ : List 𝒞) (k : Fin l₁.length) (hk : k.1 < (l₁ ++ l₂).length)
      (h : (l₁ ++ l₂).get ⟨k.1, hk⟩ = l₁.get k),
      listProdAppendInv l₁ l₂ ≫ (h ▸ listProdProj (l₁ ++ l₂) ⟨k.1, hk⟩)
        = (fst : prod (listProd l₁) (listProd l₂) ⟶ listProd l₁) ≫ listProdProj l₁ k
  | [],      _,  k, _, _ => k.elim0
  | C :: l₁, l₂, ⟨0,     _⟩, _, h => by
      unfold listProdAppendInv
      simp only [listProdProj]
      show pair (fst ≫ fst) (pair (fst ≫ snd) snd ≫ listProdAppendInv l₁ l₂) ≫ fst = fst ≫ fst
      rw [fst_pair]
  | C :: l₁, l₂, ⟨j + 1, hj⟩, hk, h => by
      have hjk : j < (l₁ ++ l₂).length := by
        have : (Fin.mk (j + 1) hj : Fin (C :: l₁).length).val = j + 1 := rfl
        have : (C :: l₁ ++ l₂).length = (l₁ ++ l₂).length + 1 := rfl
        omega
      have htl : (l₁ ++ l₂).get ⟨j, hjk⟩ = l₁.get ⟨j, Nat.lt_of_succ_lt_succ hj⟩ := by
        have := List.getElem_append_left (as := l₁) (bs := l₂) (Nat.lt_of_succ_lt_succ hj) (h' := hjk)
        simpa [List.get_eq_getElem] using this
      show listProdAppendInv (C :: l₁) l₂ ≫ (h ▸ (snd ≫ listProdProj (l₁ ++ l₂) ⟨j, hjk⟩))
          = fst ≫ snd ≫ listProdProj l₁ ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      rw [cast_comp_hom h]
      unfold listProdAppendInv
      rw [← Cat.assoc, snd_pair, Cat.assoc]
      have hc : h ▸ listProdProj (l₁ ++ l₂) ⟨j, hjk⟩ = htl ▸ listProdProj (l₁ ++ l₂) ⟨j, hjk⟩ := rfl
      rw [hc, listProdAppendInv_projL l₁ l₂ ⟨j, _⟩ hjk htl, ← Cat.assoc, fst_pair, Cat.assoc]

-- The head projection of `listProd L` is `fst`, up to HEq transport along `L = C :: rest`.
private theorem listProdProj_zero_heq (L : List 𝒞) {C : 𝒞} {rest : List 𝒞}
    (h : L = C :: rest) (h0 : 0 < L.length) :
    HEq (listProdProj L ⟨0, h0⟩) (fst : prod C (listProd rest) ⟶ C) := by
  subst h; rfl

-- The successor projection of `listProd L` is `snd ≫ (tail projection)`, up to HEq transport.
private theorem listProdProj_succ_heq (L : List 𝒞) {C : 𝒞} {rest : List 𝒞}
    (h : L = C :: rest) {n : Nat} (hn : n + 1 < L.length)
    (hn' : n < rest.length) :
    HEq (listProdProj L ⟨n + 1, hn⟩)
        ((snd : prod C (listProd rest) ⟶ listProd rest) ≫ listProdProj rest ⟨n, hn'⟩) := by
  subst h; rfl

-- `listProdProj` transports across list equality: `L = L' → listProdProj L ⟨n,_⟩ ≍ listProdProj L' ⟨n,_⟩`.
private theorem listProdProj_heq_list {L L' : List 𝒞} (h : L = L') {n : Nat}
    (hn : n < L.length) (hn' : n < L'.length) :
    HEq (listProdProj L ⟨n, hn⟩) (listProdProj L' ⟨n, hn'⟩) := by
  subst h; rfl

-- `listProdProj` is proof-irrelevant: same nat index with different bounds gives HEq result.
private theorem listProdProj_heq_nat (l : List 𝒞) {n m : Nat}
    (hn : n < l.length) (hm : m < l.length) (heqn : n = m) :
    HEq (listProdProj l ⟨n, hn⟩) (listProdProj l ⟨m, hm⟩) := by
  subst heqn; rfl

/-- `listProdAppendInv` then a projection into the SECOND block `l₂` is `snd ≫ (l₂'s projection)`.
    The offset index `l₁.length + k.1` into `l₁++l₂` lands in the `l₂` part; `h` carries the
    equality, and the cast is eliminated by the same `cast_comp_hom` technique as `projL`. -/
theorem listProdAppendInv_projR :
    ∀ (l₁ l₂ : List 𝒞) (k : Fin l₂.length) (hk : l₁.length + k.1 < (l₁ ++ l₂).length)
      (h : (l₁ ++ l₂).get ⟨l₁.length + k.1, hk⟩ = l₂.get k),
      listProdAppendInv l₁ l₂ ≫ (h ▸ listProdProj (l₁ ++ l₂) ⟨l₁.length + k.1, hk⟩)
        = (snd : prod (listProd l₁) (listProd l₂) ⟶ listProd l₂) ≫ listProdProj l₂ k
  | [],      l₂, k, hk, h => by
      simp only [List.nil_append, List.length_nil] at *
      unfold listProdAppendInv; congr 1
      -- h ▸ listProdProj l₂ ⟨0+k.1, hk⟩  =  listProdProj l₂ k:
      -- chain HEq: (h ▸ f) ≍ f ≍ listProdProj l₂ k  via eqRec_heq + listProdProj_heq_nat
      exact eq_of_heq ((eqRec_heq (φ := fun z => listProd l₂ ⟶ z) h _).trans
                       (listProdProj_heq_nat l₂ hk k.2 (Nat.zero_add k.1)))
  | C :: l₁, l₂, k, hk, h => by
      have hjk : l₁.length + k.1 < (l₁ ++ l₂).length := by
        have : (C :: l₁ ++ l₂).length = (l₁ ++ l₂).length + 1 := rfl
        have : (C :: l₁).length = l₁.length + 1 := rfl
        omega
      have htl : (l₁ ++ l₂).get ⟨l₁.length + k.1, hjk⟩ = l₂.get k := by
        simp [List.get_eq_getElem, List.getElem_append_right, Nat.add_sub_cancel_left]
      have hsucc : (l₁.length + k.1).succ < (C :: l₁ ++ l₂).length := Nat.succ_lt_succ hjk
      -- h' uses the explicit bound hsucc (not ⋯) so simp [listProdProj] can reduce it later
      have h' : (C :: l₁ ++ l₂).get ⟨(l₁.length + k.1).succ, hsucc⟩ = l₂.get k :=
        (congrArg (C :: l₁ ++ l₂).get (Fin.ext (Nat.succ_add l₁.length k.1).symm)).trans h
      have hfin : (⟨(C :: l₁).length + k.1, hk⟩ : Fin (C :: l₁ ++ l₂).length)
                = ⟨(l₁.length + k.1).succ, hsucc⟩ :=
        Fin.ext (Nat.succ_add l₁.length k.1)
      -- hrw: convert h ▸ proj to h' ▸ proj via HEq transitivity
      have hrw : h ▸ listProdProj (C :: l₁ ++ l₂) ⟨(C :: l₁).length + k.1, hk⟩
               = h' ▸ listProdProj (C :: l₁ ++ l₂) ⟨(l₁.length + k.1).succ, hsucc⟩ :=
        eq_of_heq ((eqRec_heq (φ := fun z => listProd (C :: l₁ ++ l₂) ⟶ z) h _).trans
          ((listProdProj_heq_nat (C :: l₁ ++ l₂) hk hsucc (Nat.succ_add l₁.length k.1)).trans
           (eqRec_heq (φ := fun z => listProd (C :: l₁ ++ l₂) ⟶ z) h' _).symm))
      rw [hrw]; simp [listProdProj]
      rw [cast_comp_hom h']
      unfold listProdAppendInv
      rw [← Cat.assoc, snd_pair, Cat.assoc]
      have hc : h' ▸ listProdProj (l₁ ++ l₂) ⟨l₁.length + k.1, hjk⟩
                = htl ▸ listProdProj (l₁ ++ l₂) ⟨l₁.length + k.1, hjk⟩ := rfl
      rw [hc, listProdAppendInv_projR l₁ l₂ k hjk htl, ← Cat.assoc, snd_pair]

/-- **Position of a `p`-true entry within the filtered list.**  `filterIdx p l k hk` is the index of
    `l.get k` inside `l.filter p` (= the count of `p`-true entries strictly before `k`).  Defined by
    recursion on `l`; in the cons case the head `C` either joins the filtered list (`p C = true`,
    shifting tail indices by one) or is dropped (`p C = false`).  The hypothesis `hk : p (l.get k)`
    forces `p C = true` when `k = 0`. -/
def filterIdx (p : 𝒞 → Bool) :
    ∀ (l : List 𝒞) (k : Fin l.length), p (l.get k) = true → Fin (l.filter p).length
  | [],      k, _  => k.elim0
  | C :: l, ⟨0,     _⟩, hk => by
      have hC : p C = true := hk
      exact ⟨0, by simp [hC]⟩
  | C :: l, ⟨j + 1, hj⟩, hk => by
      have hjk : j < l.length := Nat.lt_of_succ_lt_succ hj
      have hk' : p (l.get ⟨j, hjk⟩) = true := hk
      match hpC : p C with
      | true =>
          exact ⟨(filterIdx p l ⟨j, hjk⟩ hk').1 + 1, by
            simp only [List.filter_cons, hpC, if_true, List.length_cons]
            exact Nat.succ_lt_succ (filterIdx p l ⟨j, hjk⟩ hk').2⟩
      | false =>
          exact ⟨(filterIdx p l ⟨j, hjk⟩ hk').1, by
            simp only [List.filter_cons, hpC]
            exact (filterIdx p l ⟨j, hjk⟩ hk').2⟩

/-- **Get-correctness for `filterIdx`**: the filtered list at the computed index is the original
    entry. -/
theorem filterIdx_get (p : 𝒞 → Bool) :
    ∀ (l : List 𝒞) (k : Fin l.length) (hk : p (l.get k) = true),
      (l.filter p).get (filterIdx p l k hk) = l.get k
  | [],      k, _  => k.elim0
  | C :: l, ⟨0,     _⟩, hk => by
      have hC : p C = true := hk
      simp only [filterIdx]
      -- both sides reduce to `C`; the filtered head is `C` since `p C = true`
      have : (C :: l).filter p = C :: l.filter p := by simp [hC]
      simp [List.get_eq_getElem, this]
  | C :: l, ⟨j + 1, hj⟩, hk => by
      have hjk : j < l.length := Nat.lt_of_succ_lt_succ hj
      have hk' : p (l.get ⟨j, hjk⟩) = true := hk
      have hrec := filterIdx_get p l ⟨j, hjk⟩ hk'
      simp only [filterIdx]
      simp only [List.get_eq_getElem] at hrec ⊢
      split <;> rename_i hpC
      · -- p C = true : filtered head is `C`, index shifted by one
        simp only [List.filter_cons, hpC, if_true, List.getElem_cons_succ]; exact hrec
      · -- p C = false : head dropped, index unchanged
        simp only [List.filter_cons, hpC, List.getElem_cons_succ]; exact hrec

/-- **`listProdPartitionInv` then a projection into a `p`-TRUE factor is `fst ≫ (filtered projection)`**
    (HEq workhorse).  The factor `l.get k` (with `p (l.get k) = true`) sits in the LEFT block
    `listProd (l.filter p)`, reached by `fst` then the filtered projection at `filterIdx p l k hk`.
    The two sides have defeq-but-not-syntactically-equal codomains (`filterIdx_get`); HEq sidesteps the
    transport.  Proof by recursion on `l`, mirroring `listProdAppendInv_projL` but case-splitting `p C`
    (the internal `List.filter_cons` cast stripped by `cast_heq`/`castDom_comp`). -/
theorem listProdPartitionInv_projL_heq (p : 𝒞 → Bool) :
    ∀ (l : List 𝒞) (k : Fin l.length) (hk : p (l.get k) = true),
      HEq (listProdPartitionInv p l ≫ listProdProj l k)
          ((fst : prod (listProd (l.filter p)) (listProd (l.filter (fun a => !p a)))
              ⟶ listProd (l.filter p))
            ≫ listProdProj (l.filter p) (filterIdx p l k hk))
  | [],      k, _ => k.elim0
  | C :: l, ⟨0, hk0⟩, hk => by
      have hC : p C = true := hk
      have hidx : filterIdx p (C :: l) ⟨0, hk0⟩ hk = ⟨0, by simp [hC]⟩ := by simp only [filterIdx]
      simp only [listProdProj]
      unfold listProdPartitionInv
      split
      case h_2 heq => simp [hC] at heq
      case h_1 heq =>
        simp only [eq_mpr_eq_cast]
        -- LHS: strip the domain-cast (HEq), then `fst_pair`; RHS: reduce `filterIdx` to `⟨0,_⟩` and
        -- the head filtered projection to `fst` (`listProdProj_zero_heq`), matching via `comp_heq`.
        have hfe : List.filter p (C :: l) = C :: List.filter p l := List.filter_cons_of_pos hC
        have hfe2 : List.filter (fun a => !p a) (C :: l) = List.filter (fun a => !p a) l := by
          simp [hC]
        refine HEq.trans (castDom_comp_heq (by simp [hC]) _ _ _) ?_
        rw [fst_pair, hidx]
        have hAobj : prod C (listProd (List.filter p l)) = listProd (List.filter p (C :: l)) := by
          rw [hfe]; rfl
        have hsnd : listProd (if false = true then C :: List.filter (fun a => !p a) l
              else List.filter (fun a => !p a) l)
            = listProd (List.filter (fun a => !p a) (C :: l)) := by
          rw [List.filter_cons]; simp [hC]
        have hBget := filterIdx_get p (C :: l) ⟨0, hk0⟩ hk
        rw [hidx] at hBget
        have hBobj : C = (List.filter p (C :: l)).get ⟨0, by rw [hfe]; simp⟩ := hBget.symm
        exact comp_heq _ _ _ _
          (by rw [hsnd, show List.filter p (C :: l) = C :: List.filter p l from hfe]) hAobj hBobj
          (fst_heq hAobj hsnd) (listProdProj_zero_heq _ hfe _).symm
  | C :: l, ⟨j + 1, hj⟩, hk => by
      have hjk : j < l.length := Nat.lt_of_succ_lt_succ hj
      have hk' : p (l.get ⟨j, hjk⟩) = true := hk
      have hrec := listProdPartitionInv_projL_heq p l ⟨j, hjk⟩ hk'
      simp only [listProdProj]
      unfold listProdPartitionInv
      split <;> rename_i heq
      · -- p C = true : head joins LEFT block, filtered index shifts by one
        refine HEq.trans (castDom_comp_heq (by simp [heq]) _ _ _) ?_
        rw [← Cat.assoc, snd_pair, Cat.assoc]
        refine HEq.trans
          (comp_right_heq (filterIdx_get p l ⟨j, hjk⟩ hk').symm (pair (fst ≫ snd) snd) _ _ hrec) ?_
        rw [← Cat.assoc, fst_pair, Cat.assoc]
        have hfe : List.filter p (C :: l) = C :: List.filter p l := List.filter_cons_of_pos heq
        have hfe2 : List.filter (fun a => !p a) (C :: l) = List.filter (fun a => !p a) l := by
          simp [heq]
        have hbnd : (filterIdx p l ⟨j, hjk⟩ hk').1 + 1 < (List.filter p (C :: l)).length := by
          rw [hfe]; simp [(filterIdx p l ⟨j, hjk⟩ hk').2]
        have hidx2 : filterIdx p (C :: l) ⟨j + 1, hj⟩ hk = ⟨(filterIdx p l ⟨j, hjk⟩ hk').1 + 1, hbnd⟩ := by
          apply Fin.ext; simp only [filterIdx]; split <;> rename_i h2
          · rfl
          · exact absurd heq (by rw [h2]; simp)
        rw [hidx2]
        have hsucc := listProdProj_succ_heq (List.filter p (C :: l)) hfe
          (n := (filterIdx p l ⟨j, hjk⟩ hk').1) hbnd (filterIdx p l ⟨j, hjk⟩ hk').2
        rw [show (⟨(filterIdx p l ⟨j, hjk⟩ hk').1, (filterIdx p l ⟨j, hjk⟩ hk').2⟩
              : Fin (List.filter p l).length) = filterIdx p l ⟨j, hjk⟩ hk' from Fin.ext rfl] at hsucc
        -- object equalities for `comp_heq` (all from `hfe`/`hfe2`)
        have hAobj : prod C (listProd (List.filter p l)) = listProd (List.filter p (C :: l)) := by
          rw [hfe]; rfl
        have hBget := filterIdx_get p (C :: l) ⟨j + 1, hj⟩ hk
        rw [hidx2] at hBget
        have hBobj : (List.filter p l).get (filterIdx p l ⟨j, hjk⟩ hk')
            = (List.filter p (C :: l)).get ⟨(filterIdx p l ⟨j, hjk⟩ hk').1 + 1, hbnd⟩ :=
          (filterIdx_get p l ⟨j, hjk⟩ hk').trans hBget.symm
        have hiteB : listProd (if false = true then C :: List.filter (fun a => !p a) l
              else List.filter (fun a => !p a) l)
            = listProd (List.filter (fun a => !p a) (C :: l)) := by
          rw [List.filter_cons]; simp [heq]
        refine comp_heq _ _ _ _ (by rw [hAobj, hiteB]) hAobj hBobj
          (fst_heq hAobj hiteB) hsucc.symm
      · -- p C = false : head joins RIGHT block, filtered (left) index unchanged
        refine HEq.trans (castDom_comp_heq (by simp [heq]) _ _ _) ?_
        rw [← Cat.assoc, snd_pair, Cat.assoc]
        refine HEq.trans
          (comp_right_heq (filterIdx_get p l ⟨j, hjk⟩ hk').symm (pair fst (snd ≫ snd)) _ _ hrec) ?_
        rw [← Cat.assoc, fst_pair]
        have hfe : List.filter p (C :: l) = List.filter p l := List.filter_cons_of_neg (by rw [heq]; simp)
        have hbnd : (filterIdx p l ⟨j, hjk⟩ hk').1 < (List.filter p (C :: l)).length := by
          rw [hfe]; exact (filterIdx p l ⟨j, hjk⟩ hk').2
        have hidx2 : filterIdx p (C :: l) ⟨j + 1, hj⟩ hk = ⟨(filterIdx p l ⟨j, hjk⟩ hk').1, hbnd⟩ := by
          apply Fin.ext; simp only [filterIdx]; split <;> rename_i h2
          · exact absurd h2 (by rw [heq]; simp)
          · rfl
        rw [hidx2]
        have hAobj : listProd (if false = true then C :: List.filter p l else List.filter p l)
            = listProd (List.filter p (C :: l)) := by rw [List.filter_cons]; simp [heq]
        have hsnd : prod C (listProd (List.filter (fun a => !p a) l))
            = listProd (List.filter (fun a => !p a) (C :: l)) := by
          rw [List.filter_cons_of_pos (by rw [heq]; simp)]; rfl
        have hBget := filterIdx_get p (C :: l) ⟨j + 1, hj⟩ hk
        rw [hidx2] at hBget
        have hBobj : (List.filter p l).get (filterIdx p l ⟨j, hjk⟩ hk')
            = (List.filter p (C :: l)).get ⟨(filterIdx p l ⟨j, hjk⟩ hk').1, hbnd⟩ :=
          (filterIdx_get p l ⟨j, hjk⟩ hk').trans hBget.symm
        exact comp_heq _ _ _ _ (by rw [hAobj, hsnd]) hAobj hBobj
          (fst_heq hAobj hsnd) (listProdProj_heq_list hfe.symm _ _)

/-- **`=`-form of `listProdPartitionInv_projL_heq`** (transport the codomain along `filterIdx_get`).
    For a `p`-TRUE factor `l.get k`, the inverse-then-projection equals `fst` into the filtered
    product, transported by `h : (l.filter p).get (filterIdx …) = l.get k`. -/
theorem listProdPartitionInv_projL (p : 𝒞 → Bool) (l : List 𝒞) (k : Fin l.length)
    (hk : p (l.get k) = true) (h : (l.filter p).get (filterIdx p l k hk) = l.get k) :
    listProdPartitionInv p l ≫ listProdProj l k
      = (fst : prod (listProd (l.filter p)) (listProd (l.filter (fun a => !p a)))
          ⟶ listProd (l.filter p))
        ≫ (h ▸ listProdProj (l.filter p) (filterIdx p l k hk)) := by
  apply eq_of_heq
  refine (listProdPartitionInv_projL_heq p l k hk).trans ?_
  refine (comp_right_heq h.symm fst _ _ ?_).symm
  exact eqRec_heq (φ := fun z => listProd (l.filter p) ⟶ z) h _

/-- **`listProdPartitionInv` then a projection into a `p`-FALSE factor is `snd ≫ (filtered projection)`**
    (HEq workhorse).  Symmetric to `listProdPartitionInv_projL_heq`: a `(!p)`-true factor `l.get k`
    sits in the RIGHT block `listProd (l.filter (!p))`, reached by `snd` then the filtered projection
    at `filterIdx (!p) l k hk`. -/
theorem listProdPartitionInv_projR_heq (p : 𝒞 → Bool) :
    ∀ (l : List 𝒞) (k : Fin l.length) (hk : (fun a => !p a) (l.get k) = true),
      HEq (listProdPartitionInv p l ≫ listProdProj l k)
          ((snd : prod (listProd (l.filter p)) (listProd (l.filter (fun a => !p a)))
              ⟶ listProd (l.filter (fun a => !p a)))
            ≫ listProdProj (l.filter (fun a => !p a)) (filterIdx (fun a => !p a) l k hk))
  | [],      k, _ => k.elim0
  | C :: l, ⟨0, hk0⟩, hk => by
      have hC : p C = false := by
        have : (!p C) = true := hk
        simpa using this
      have hidx : filterIdx (fun a => !p a) (C :: l) ⟨0, hk0⟩ hk = ⟨0, by simp [hC]⟩ := by
        simp only [filterIdx]
      simp only [listProdProj]
      unfold listProdPartitionInv
      split
      case h_1 heq => simp [hC] at heq
      case h_2 heq =>
        simp only [eq_mpr_eq_cast]
        have hfe : List.filter (fun a => !p a) (C :: l) = C :: List.filter (fun a => !p a) l :=
          List.filter_cons_of_pos (by simp [hC])
        refine HEq.trans (castDom_comp_heq (by simp [hC]) _ _ _) ?_
        rw [fst_pair, hidx]
        have hAobj : prod C (listProd (List.filter (fun a => !p a) l))
            = listProd (List.filter (fun a => !p a) (C :: l)) := by rw [hfe]; rfl
        have hpfe : listProd (if false = true then C :: List.filter p l else List.filter p l)
            = listProd (List.filter p (C :: l)) := by rw [List.filter_cons]; simp [hC]
        have hBget := filterIdx_get (fun a => !p a) (C :: l) ⟨0, hk0⟩ hk
        rw [hidx] at hBget
        have hBobj : C = (List.filter (fun a => !p a) (C :: l)).get ⟨0, by rw [hfe]; simp⟩ :=
          hBget.symm
        exact comp_heq _ _ _ _
          (by rw [hpfe, show List.filter (fun a => !p a) (C :: l) = C :: List.filter (fun a => !p a) l
                from hfe]) hAobj hBobj
          (snd_heq hpfe hAobj) (listProdProj_zero_heq _ hfe _).symm
  | C :: l, ⟨j + 1, hj⟩, hk => by
      have hjk : j < l.length := Nat.lt_of_succ_lt_succ hj
      have hk' : (fun a => !p a) (l.get ⟨j, hjk⟩) = true := hk
      have hrec := listProdPartitionInv_projR_heq p l ⟨j, hjk⟩ hk'
      simp only [listProdProj]
      unfold listProdPartitionInv
      split <;> rename_i heq
      · -- p C = true : head joins LEFT block, RIGHT (`!p`) filtered index UNCHANGED
        refine HEq.trans (castDom_comp_heq (by simp [heq]) _ _ _) ?_
        rw [← Cat.assoc, snd_pair, Cat.assoc]
        refine HEq.trans
          (comp_right_heq (filterIdx_get (fun a => !p a) l ⟨j, hjk⟩ hk').symm
            (pair (fst ≫ snd) snd) _ _ hrec) ?_
        rw [← Cat.assoc, snd_pair]
        have hfe : List.filter (fun a => !p a) (C :: l) = List.filter (fun a => !p a) l :=
          List.filter_cons_of_neg (by simp [heq])
        have hbnd : (filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').1
            < (List.filter (fun a => !p a) (C :: l)).length := by
          rw [hfe]; exact (filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').2
        have hidx2 : filterIdx (fun a => !p a) (C :: l) ⟨j + 1, hj⟩ hk
            = ⟨(filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').1, hbnd⟩ := by
          apply Fin.ext; simp only [filterIdx]; split <;> rename_i h2
          · exact absurd h2 (by simp [heq])
          · rfl
        rw [hidx2]
        have hAobj : listProd (List.filter (fun a => !p a) l)
            = listProd (List.filter (fun a => !p a) (C :: l)) := by rw [hfe]
        have hfst : prod C (listProd (List.filter p l)) = listProd (List.filter p (C :: l)) := by
          rw [List.filter_cons_of_pos heq]; rfl
        have hBget := filterIdx_get (fun a => !p a) (C :: l) ⟨j + 1, hj⟩ hk
        rw [hidx2] at hBget
        have hBobj : (List.filter (fun a => !p a) l).get (filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk')
            = (List.filter (fun a => !p a) (C :: l)).get
                ⟨(filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').1, hbnd⟩ :=
          (filterIdx_get (fun a => !p a) l ⟨j, hjk⟩ hk').trans hBget.symm
        have hite : listProd (if false = true then C :: List.filter (fun a => !p a) l
              else List.filter (fun a => !p a) l)
            = listProd (List.filter (fun a => !p a) (C :: l)) := by rw [List.filter_cons]; simp [heq]
        exact comp_heq _ _ _ _ (by rw [hfst, hite]) hAobj hBobj
          (snd_heq hfst hAobj) (listProdProj_heq_list hfe.symm _ _)
      · -- p C = false : head joins RIGHT block, RIGHT (`!p`) filtered index SHIFTS by one
        refine HEq.trans (castDom_comp_heq (by simp [heq]) _ _ _) ?_
        rw [← Cat.assoc, snd_pair, Cat.assoc]
        refine HEq.trans
          (comp_right_heq (filterIdx_get (fun a => !p a) l ⟨j, hjk⟩ hk').symm
            (pair fst (snd ≫ snd)) _ _ hrec) ?_
        rw [← Cat.assoc, snd_pair, Cat.assoc]
        have hfe : List.filter (fun a => !p a) (C :: l) = C :: List.filter (fun a => !p a) l :=
          List.filter_cons_of_pos (by simp [heq])
        have hbnd : (filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').1 + 1
            < (List.filter (fun a => !p a) (C :: l)).length := by
          rw [hfe]; simp [(filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').2]
        have hidx2 : filterIdx (fun a => !p a) (C :: l) ⟨j + 1, hj⟩ hk
            = ⟨(filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').1 + 1, hbnd⟩ := by
          apply Fin.ext; simp only [filterIdx]; split <;> rename_i h2
          · rfl
          · exact absurd h2 (by simp [heq])
        rw [hidx2]
        have hsucc := listProdProj_succ_heq (List.filter (fun a => !p a) (C :: l)) hfe
          (n := (filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').1) hbnd
          (filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').2
        rw [show (⟨(filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').1,
              (filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').2⟩ : Fin (List.filter (fun a => !p a) l).length)
            = filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk' from Fin.ext rfl] at hsucc
        have hAobj : prod C (listProd (List.filter (fun a => !p a) l))
            = listProd (List.filter (fun a => !p a) (C :: l)) := by rw [hfe]; rfl
        have hfst : listProd (if false = true then C :: List.filter p l else List.filter p l)
            = listProd (List.filter p (C :: l)) := by rw [List.filter_cons]; simp [heq]
        have hBget := filterIdx_get (fun a => !p a) (C :: l) ⟨j + 1, hj⟩ hk
        rw [hidx2] at hBget
        have hBobj : (List.filter (fun a => !p a) l).get (filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk')
            = (List.filter (fun a => !p a) (C :: l)).get
                ⟨(filterIdx (fun a => !p a) l ⟨j, hjk⟩ hk').1 + 1, hbnd⟩ :=
          (filterIdx_get (fun a => !p a) l ⟨j, hjk⟩ hk').trans hBget.symm
        exact comp_heq _ _ _ _ (by rw [hfst, hAobj]) hAobj hBobj
          (snd_heq hfst hAobj) hsucc.symm

/-- **`=`-form of `listProdPartitionInv_projR_heq`** (transport along `filterIdx_get`). -/
theorem listProdPartitionInv_projR (p : 𝒞 → Bool) (l : List 𝒞) (k : Fin l.length)
    (hk : (fun a => !p a) (l.get k) = true)
    (h : (l.filter (fun a => !p a)).get (filterIdx (fun a => !p a) l k hk) = l.get k) :
    listProdPartitionInv p l ≫ listProdProj l k
      = (snd : prod (listProd (l.filter p)) (listProd (l.filter (fun a => !p a)))
          ⟶ listProd (l.filter (fun a => !p a)))
        ≫ (h ▸ listProdProj (l.filter (fun a => !p a)) (filterIdx (fun a => !p a) l k hk)) := by
  apply eq_of_heq
  refine (listProdPartitionInv_projR_heq p l k hk).trans ?_
  refine (comp_right_heq h.symm snd _ _ ?_).symm
  exact eqRec_heq (φ := fun z => listProd (l.filter (fun a => !p a)) ⟶ z) h _


/-- A right factor of a well-supported binary product is well-supported.  The unique
    `prod B D ⟶ 1` equals `snd ≫ (D ⟶ 1)` by terminal uniqueness, and is a cover (`prod B D`
    well-supported), so `D ⟶ 1` is a cover by `cover_of_comp_cover`. -/
theorem wellSupported_prod_right {B D : 𝒞} (h : WellSupported (prod B D)) :
    WellSupported D := by
  show Cover (term D)
  apply cover_of_comp_cover (snd : prod B D ⟶ D) (term D)
  rw [show (snd : prod B D ⟶ D) ≫ term D = term (prod B D) from term_uniq _ _]
  exact h

/-- **§1.547 — every dense morphism is MONIC in `Â`** (the book's "every dense morphism is monic").
    THE R7 CORRECTION.  A dense `x : X → Y` is monic *in `Â`* — even though its underlying `A`-map
    `x.g` is an epic cover (`pairDense_cover`).  No contradiction: `pairForget` does NOT reflect
    monos, so monic-in-`Â` is tested against fewer arrows than monic-in-`A`; a dense morphism is BOTH
    monic-in-`Â` (`pairDense_monic`) AND epic-in-`Â` (`pairDense_epi`), which does NOT force it iso
    because `Â` is not balanced.  This is exactly the book's "every dense morphism is monic" and makes
    `pairDenseClass` a class of monics, so the §1.48 monic left-fraction calculus (`MonicDense`) does
    apply to it — the R6 "monic/epic collapse" framing was a category confusion (it conflated monic
    -in-`Â` with the underlying map being monic-in-`A`).

    Proof.  Given `Â`-maps `a, b : Z → X` with `a.comp x = b.comp x`, show `a = b`, i.e. `a.g = b.g`.
    Via the iso `e : X.A ≅ Y.A × W` it suffices to show `a.g ≫ e = b.g ≫ e`, and by joint monicity
    this splits into the two product components:
      • `fst` : `a.g ≫ e ≫ fst = a.g ≫ x.g = b.g ≫ x.g = b.g ≫ e ≫ fst` (from `a.comp x = b.comp x`);
      • `snd` : `a.g ≫ e ≫ snd = b.g ≫ e ≫ snd` into `W`, which is the `survPinned` field — `W` is the
        product of the surviving targets, each a factor of `X`, so compatibility of `a` and `b` with
        `X`'s factor data (distinctness forcing the same witness) pins both maps to the same value.
    Sorry-free, choice-free. -/
theorem pairDense_monic {X Y : PairObj 𝒞} {x : PairHom X Y} (d : PairDense x) :
    @Monic (PairObj 𝒞) _ X Y x := by
  intro Z a b hab
  apply PairHom.ext
  -- reduce to `a.g ≫ e = b.g ≫ e` (e is iso)
  have hfst : a.g ≫ x.g = b.g ≫ x.g := by
    have : (a.comp x).g = (b.comp x).g := congrArg PairHom.g hab
    simpa [PairHom.comp] using this
  have hsnd : a.g ≫ d.e ≫ (snd : prod Y.A d.W ⟶ d.W) = b.g ≫ d.e ≫ (snd : prod Y.A d.W ⟶ d.W) :=
    d.survPinned a b
  -- glue the two components through the iso `e`
  have hee : a.g ≫ d.e = b.g ≫ d.e := by
    apply fst_snd_jointly_monic
    · calc (a.g ≫ d.e) ≫ (fst : prod Y.A d.W ⟶ Y.A)
          = a.g ≫ (d.e ≫ fst) := by rw [Cat.assoc]
        _ = a.g ≫ x.g := by rw [d.proj]
        _ = b.g ≫ x.g := hfst
        _ = b.g ≫ (d.e ≫ fst) := by rw [d.proj]
        _ = (b.g ≫ d.e) ≫ (fst : prod Y.A d.W ⟶ Y.A) := by rw [Cat.assoc]
    · rw [Cat.assoc, Cat.assoc]; exact hsnd
  -- cancel the iso: `a.g = a.g ≫ e ≫ einv = b.g ≫ e ≫ einv = b.g`
  calc a.g = a.g ≫ (d.e ≫ d.einv) := by rw [d.e_iso₁, Cat.comp_id]
    _ = (a.g ≫ d.e) ≫ d.einv := by rw [Cat.assoc]
    _ = (b.g ≫ d.e) ≫ d.einv := by rw [hee]
    _ = b.g ≫ (d.e ≫ d.einv) := by rw [Cat.assoc]
    _ = b.g := by rw [d.e_iso₁, Cat.comp_id]

/-- **§1.547 — every iso of `Â` is dense** (witness form).  Take surviving factor `W = 1`
    (terminal, well-supported `wellSupported_one'`); the iso `X.A ≅ Y.A × 1` is `pair x.g (term)`,
    with inverse `fst ≫ x⁻¹.g`, carrying `x.g` to `fst`.  Choice-free: the inverse arrow `x'` is
    passed explicitly (read off the `IsIso` witness in `pairDense_of_isIso`). -/
def pairDense_of_iso {X Y : PairObj 𝒞} {x : PairHom X Y}
    (x' : PairHom Y X) (hxx' : x.g ≫ x'.g = Cat.id X.A) (hx'x : x'.g ≫ x.g = Cat.id Y.A) :
    PairDense x :=
  { W := HasTerminal.one
    wsupp := wellSupported_one'
    e := pair x.g (term X.A)
    einv := fst ≫ x'.g
    e_iso₁ := by
      -- `pair x.g (term) ≫ (fst ≫ x'.g) = x.g ≫ x'.g = id`
      rw [← Cat.assoc, fst_pair]; exact hxx'
    e_iso₂ := by
      -- `(fst ≫ x'.g) ≫ pair x.g (term) = id` on `Y.A × 1`: agree on both projections
      apply fst_snd_jointly_monic
      · -- ≫ fst : `(fst ≫ x'.g) ≫ x.g = fst ≫ id = fst`
        rw [Cat.assoc, fst_pair, Cat.assoc, hx'x, Cat.comp_id, Cat.id_comp]
      · -- ≫ snd : both sides into `1`, unique
        apply HasTerminal.uniq
    proj := fst_pair _ _
    -- an iso has NO surviving factors: the product diagram is `X.A ≅ Y.A × 1`, `W = 1`, so the
    -- `snd`-component lands in the terminal `1` and is unique — both maps agree there.
    survPinned := fun a b => HasTerminal.uniq _ _
    -- an iso has W = 1 and EMPTY surviving list; `listProd [] = 1`, so wf/wg are the unique maps.
    surv := []
    survWS := fun _ h => absurd h (List.not_mem_nil)
    wf := term _
    wg := term _
    wfg := HasTerminal.uniq _ _
    wgf := HasTerminal.uniq _ _
    -- an iso has W = 1 ⇒ NO surviving factors: every `f ∈ X.F` is Y-DERIVED (LEFT disjunct).
    -- Use the inverse's compat (X→Y direction): `x'.compat f` gives `q ∈ Y.F` of the same target
    -- with `x'.g ≫ f = q`; then `f = (x.g ≫ x'.g) ≫ f = x.g ≫ q` since `x.g ≫ x'.g = id`.
    factorSplit := by
      intro f hf
      left
      obtain ⟨q, hq, hq1, hqe⟩ := x'.compat f hf
      refine ⟨q, hq, hq1.symm, ?_⟩
      obtain ⟨ft, fm⟩ := f; obtain ⟨qt, qm⟩ := q
      cases hq1
      simp only at hqe ⊢
      rw [← hqe, ← Cat.assoc, hxx', Cat.id_comp]
    -- surv = [] ⇒ `Fin 0` is empty.
    survDistinct := fun k => k.elim0
    survInX := fun k => k.elim0 }

/-- **§1.547 — every iso of `Â` is dense** (the `DenseClass.iso_mem` obligation), choice-free by
    destructing the `IsIso` witness into its explicit inverse arrow. -/
theorem pairDense_of_isIso {X Y : PairObj 𝒞} {x : PairHom X Y}
    (hx : @IsIso (PairObj 𝒞) _ X Y x) : Nonempty (PairDense x) := by
  obtain ⟨x', hxx', hx'x⟩ := hx
  exact ⟨pairDense_of_iso x' (congrArg PairHom.g hxx') (congrArg PairHom.g hx'x)⟩

/-- **Retract extension (right factor).**  If `W` retracts onto `prod T Wf` via `(p,q)` (`p≫q=id`,
    `q≫p=id`), then for any object `D` the product `prod D W` retracts onto `prod T (prod D Wf)`,
    the new `fst`-component being `snd ≫ p ≫ fst` (recovering `T` from the `W`-coordinate). -/
theorem retractExtendRight {T Wf W D : 𝒞} (p : W ⟶ prod T Wf) (q : prod T Wf ⟶ W)
    (hpq : p ≫ q = Cat.id W) (hqp : q ≫ p = Cat.id (prod T Wf)) :
    ∃ (p' : prod D W ⟶ prod T (prod D Wf)) (q' : prod T (prod D Wf) ⟶ prod D W),
      p' ≫ q' = Cat.id (prod D W) ∧ q' ≫ p' = Cat.id (prod T (prod D Wf))
      ∧ p' ≫ (fst : prod T (prod D Wf) ⟶ T) = (snd : prod D W ⟶ W) ≫ p ≫ fst := by
  refine ⟨pair (snd ≫ p ≫ fst) (pair fst (snd ≫ p ≫ snd)),
          pair (snd ≫ fst) (pair fst (snd ≫ snd) ≫ q), ?_, ?_, fst_pair _ _⟩
  · -- p' ≫ q' = id on `prod D W`: check both projections
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, snd_pair, fst_pair, Cat.id_comp]
    · rw [Cat.assoc, snd_pair, Cat.id_comp, ← Cat.assoc]
      have hrec : pair (snd ≫ p ≫ fst) (pair (fst : prod D W ⟶ D) (snd ≫ p ≫ snd))
          ≫ pair fst (snd ≫ snd) = (snd : prod D W ⟶ W) ≫ p := by
        apply fst_snd_jointly_monic
        · rw [Cat.assoc, fst_pair, fst_pair, Cat.assoc]
        · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, snd_pair, Cat.assoc]
      rw [hrec, Cat.assoc, hpq, Cat.comp_id]
  · -- q' ≫ p' = id on `prod T (prod D Wf)`: check both projections
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, Cat.id_comp, ← Cat.assoc, snd_pair, Cat.assoc,
        ← Cat.assoc q p fst, hqp, Cat.id_comp, fst_pair]
    · rw [Cat.assoc, snd_pair, Cat.id_comp]
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc,
          ← Cat.assoc q p snd, hqp, Cat.id_comp, snd_pair]

/-- **Retract extension (left factor).**  If `W` retracts onto `prod T Wf` via `(p,q)`, then for
    any `D` the product `prod W D` retracts onto `prod T (prod Wf D)`, the new `fst`-component being
    `fst ≫ p ≫ fst` (recovering `T` from the left `W`-coordinate). -/
theorem retractExtendLeft {T Wf W D : 𝒞} (p : W ⟶ prod T Wf) (q : prod T Wf ⟶ W)
    (hpq : p ≫ q = Cat.id W) (hqp : q ≫ p = Cat.id (prod T Wf)) :
    ∃ (p' : prod W D ⟶ prod T (prod Wf D)) (q' : prod T (prod Wf D) ⟶ prod W D),
      p' ≫ q' = Cat.id (prod W D) ∧ q' ≫ p' = Cat.id (prod T (prod Wf D))
      ∧ p' ≫ (fst : prod T (prod Wf D) ⟶ T) = (fst : prod W D ⟶ W) ≫ p ≫ fst := by
  refine ⟨pair (fst ≫ p ≫ fst) (pair (fst ≫ p ≫ snd) snd),
          pair (pair fst (snd ≫ fst) ≫ q) (snd ≫ snd), ?_, ?_, fst_pair _ _⟩
  · apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, Cat.id_comp, ← Cat.assoc]
      have hrec : pair (fst ≫ p ≫ fst) (pair (fst ≫ p ≫ snd) (snd : prod W D ⟶ D))
          ≫ pair fst (snd ≫ fst) = (fst : prod W D ⟶ W) ≫ p := by
        apply fst_snd_jointly_monic
        · rw [Cat.assoc, fst_pair, fst_pair, Cat.assoc]
        · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, fst_pair, Cat.assoc]
      rw [hrec, Cat.assoc, hpq, Cat.comp_id]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, snd_pair, Cat.id_comp]
  · apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, Cat.id_comp, ← Cat.assoc, fst_pair, Cat.assoc,
        ← Cat.assoc q p fst, hqp, Cat.id_comp, fst_pair]
    · rw [Cat.assoc, snd_pair, Cat.id_comp]
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc,
          ← Cat.assoc q p snd, hqp, Cat.id_comp, snd_pair]
      · rw [Cat.assoc, snd_pair, snd_pair]

/-- **§1.547 — dense morphisms are closed under COMPOSITION.**  `x : X→Y`, `y : Y→Z` dense with
    surviving objects `Wₓ`, `W_y`; `x.comp y` is dense with surviving object `W_y × Wₓ`
    (well-supported, `wellSupported_prod`), the iso `X.A ≅ Z.A × (W_y × Wₓ)` being `dx.e`
    followed by the reassociator `r : (Z.A × W_y) × Wₓ ≅ Z.A × (W_y × Wₓ)` (built from `dy.e`
    on the left factor), carrying `x.g ≫ y.g` to `fst`. -/
def pairDense_comp [PullbacksTransferCovers 𝒞] {X Y Z : PairObj 𝒞}
    {x : PairHom X Y} {y : PairHom Y Z} (dx : PairDense x) (dy : PairDense y) :
    PairDense (x.comp y) :=
  -- `r` replaces `Y.A` by `Z.A × W_y` (via `dy.e`) inside `Y.A × Wₓ`, then reassociates to
  -- `Z.A × (W_y × Wₓ)`; `r'` is its inverse (using `dy.einv`).
  let r  : prod Y.A dx.W ⟶ prod Z.A (prod dy.W dx.W) :=
    pair (fst ≫ dy.e ≫ fst) (pair (fst ≫ dy.e ≫ snd) snd)
  let r' : prod Z.A (prod dy.W dx.W) ⟶ prod Y.A dx.W :=
    pair (pair fst (snd ≫ fst) ≫ dy.einv) (snd ≫ snd)
  have hrfst : r ≫ (fst : prod Z.A (prod dy.W dx.W) ⟶ Z.A) = fst ≫ dy.e ≫ fst := fst_pair _ _
  have hrsnd : r ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W)
      = pair (fst ≫ dy.e ≫ snd) snd := snd_pair _ _
  have hr'fst : r' ≫ (fst : prod Y.A dx.W ⟶ Y.A) = pair fst (snd ≫ fst) ≫ dy.einv := fst_pair _ _
  have hr'snd : r' ≫ (snd : prod Y.A dx.W ⟶ dx.W) = snd ≫ snd := snd_pair _ _
  -- key: `r ≫ pair fst (snd≫fst) = fst ≫ dy.e` (recover `(Z.A, W_y)` from the reassociated form)
  have hkey : r ≫ pair (fst : prod Z.A (prod dy.W dx.W) ⟶ Z.A) (snd ≫ fst) = fst ≫ dy.e := by
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, hrfst, Cat.assoc]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, hrsnd, fst_pair, Cat.assoc]
  have hrr' : r ≫ r' = Cat.id (prod Y.A dx.W) := by
    apply fst_snd_jointly_monic
    · -- (r ≫ r') ≫ fst = fst
      rw [Cat.assoc, hr'fst, ← Cat.assoc, hkey, Cat.assoc, dy.e_iso₁, Cat.comp_id, Cat.id_comp]
    · -- (r ≫ r') ≫ snd = snd
      rw [Cat.assoc, hr'snd, ← Cat.assoc, hrsnd, snd_pair, Cat.id_comp]
  have hr'r : r' ≫ r = Cat.id (prod Z.A (prod dy.W dx.W)) := by
    apply fst_snd_jointly_monic
    · -- fst : (r'≫r)≫fst = r'≫(fst≫dy.e≫fst) = (pair…≫dy.einv)≫(dy.e≫fst) = pair…≫(dy.einv≫dy.e)≫fst
      rw [Cat.assoc, hrfst, ← Cat.assoc, hr'fst, Cat.assoc, ← Cat.assoc dy.einv dy.e fst,
        dy.e_iso₂, Cat.id_comp, fst_pair, Cat.id_comp]
    · -- snd: split further on the (W_y × Wₓ) product
      rw [Cat.assoc, hrsnd, Cat.id_comp]
      apply fst_snd_jointly_monic
      · -- ≫ fst
        rw [Cat.assoc, fst_pair, ← Cat.assoc, hr'fst, Cat.assoc, ← Cat.assoc dy.einv dy.e snd,
          dy.e_iso₂, Cat.id_comp, snd_pair]
      · -- ≫ snd
        rw [Cat.assoc, snd_pair, hr'snd]
  { W := prod dy.W dx.W
    wsupp := wellSupported_prod dy.wsupp dx.wsupp
    e := dx.e ≫ r
    einv := r' ≫ dx.einv
    e_iso₁ := by
      rw [Cat.assoc, ← Cat.assoc r r', hrr', Cat.id_comp, dx.e_iso₁]
    e_iso₂ := by
      rw [Cat.assoc, ← Cat.assoc dx.einv dx.e, dx.e_iso₂, Cat.id_comp, hr'r]
    proj := by
      show (dx.e ≫ r) ≫ (fst : prod Z.A (prod dy.W dx.W) ⟶ Z.A) = x.g ≫ y.g
      rw [Cat.assoc, fst_pair, ← Cat.assoc, dx.proj, ← dy.proj, ← Cat.assoc]
    survPinned := by
      -- `e ≫ snd = dx.e ≫ r ≫ snd : X.A → dy.W × dx.W`; pin each component:
      --   `≫ fst → dy.W` via `dy.survPinned (a∘x) (b∘x)` (it is `(a.g≫x.g)≫dy.e≫snd`);
      --   `≫ snd → dx.W` via `dx.survPinned a b` (it is `a.g≫dx.e≫snd`).
      intro Q a b
      have hsf : r ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W)
          ≫ (fst : prod dy.W dx.W ⟶ dy.W) = (fst : prod Y.A dx.W ⟶ Y.A) ≫ dy.e ≫ snd := by
        rw [← Cat.assoc, hrsnd, fst_pair]
      have hss : r ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W)
          ≫ (snd : prod dy.W dx.W ⟶ dx.W) = (snd : prod Y.A dx.W ⟶ dx.W) := by
        rw [← Cat.assoc, hrsnd, snd_pair]
      show a.g ≫ (dx.e ≫ r) ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W)
        = b.g ≫ (dx.e ≫ r) ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W)
      apply fst_snd_jointly_monic
      · -- `≫ fst` into `dy.W`
        have hax : (a.comp x).g ≫ dy.e ≫ (snd : prod Z.A dy.W ⟶ dy.W)
            = (b.comp x).g ≫ dy.e ≫ (snd : prod Z.A dy.W ⟶ dy.W) := dy.survPinned (a.comp x) (b.comp x)
        have key : ∀ c : PairHom Q X,
            (c.g ≫ (dx.e ≫ r) ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W))
              ≫ (fst : prod dy.W dx.W ⟶ dy.W)
            = (c.comp x).g ≫ dy.e ≫ (snd : prod Z.A dy.W ⟶ dy.W) := by
          intro c
          rw [Cat.assoc, Cat.assoc, Cat.assoc, hsf, ← Cat.assoc dx.e fst, dx.proj]
          show c.g ≫ x.g ≫ dy.e ≫ snd = (c.comp x).g ≫ dy.e ≫ snd
          rw [show (c.comp x).g = c.g ≫ x.g from rfl, Cat.assoc]
        rw [key a, key b, hax]
      · -- `≫ snd` into `dx.W`
        have key : ∀ c : PairHom Q X,
            (c.g ≫ (dx.e ≫ r) ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W))
              ≫ (snd : prod dy.W dx.W ⟶ dx.W)
            = c.g ≫ dx.e ≫ (snd : prod Y.A dx.W ⟶ dx.W) := by
          intro c
          rw [Cat.assoc, Cat.assoc, Cat.assoc, hss]
        rw [key a, key b, dx.survPinned a b]
    surv := dy.surv ++ dx.surv
    survWS := fun T hT => by
      rcases List.mem_append.1 hT with h | h
      · exact dy.survWS T h
      · exact dx.survWS T h
    wf := pair (fst ≫ dy.wf) (snd ≫ dx.wf) ≫ listProdAppendInv dy.surv dx.surv
    wg := listProdAppendHom dy.surv dx.surv ≫ pair (fst ≫ dy.wg) (snd ≫ dx.wg)
    wfg := by
      -- pair(..) ≫ (Inv ≫ Hom) ≫ pair(..) = pair(..) ≫ pair(..) = id
      rw [Cat.assoc, ← Cat.assoc (listProdAppendInv _ _), listProdAppend_inv_hom,
        Cat.id_comp]
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc, dy.wfg, Cat.comp_id,
          Cat.id_comp]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc, dx.wfg, Cat.comp_id,
          Cat.id_comp]
    wgf := by
      -- Hom ≫ (pair(..) ≫ pair(..)) ≫ Inv = Hom ≫ Inv = id
      rw [Cat.assoc, ← Cat.assoc (pair (fst ≫ dy.wg) (snd ≫ dx.wg))]
      have hmid : pair (fst ≫ dy.wg) (snd ≫ dx.wg) ≫ pair (fst ≫ dy.wf) (snd ≫ dx.wf)
          = Cat.id (prod (listProd dy.surv) (listProd dx.surv)) := by
        apply fst_snd_jointly_monic
        · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc, dy.wgf, Cat.comp_id,
            Cat.id_comp]
        · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc, dx.wgf, Cat.comp_id,
            Cat.id_comp]
      rw [hmid, Cat.id_comp, listProdAppend_hom_inv]
    factorSplit := by
      -- bridging equations for `esc := (dx.e ≫ r) ≫ snd : X.A → prod dy.W dx.W`
      intro f hf
      -- bridging equations in fully right-associated form (matching `simp only [Cat.assoc]`).
      have hescR : dx.e ≫ r ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W)
          ≫ (snd : prod dy.W dx.W ⟶ dx.W) = dx.e ≫ (snd : prod Y.A dx.W ⟶ dx.W) := by
        rw [← Cat.assoc r snd snd, hrsnd, snd_pair]
      have hescL : dx.e ≫ r ≫ (snd : prod Z.A (prod dy.W dx.W) ⟶ prod dy.W dx.W)
          ≫ (fst : prod dy.W dx.W ⟶ dy.W) = x.g ≫ dy.e ≫ (snd : prod Z.A dy.W ⟶ dy.W) := by
        rw [← Cat.assoc r snd fst, hrsnd, fst_pair, ← Cat.assoc dx.e fst, dx.proj]
      rcases dx.factorSplit f hf with ⟨gY, hgY, hgYt, hgYe⟩ | ⟨kk, hkt, hsplit⟩
      · -- dx-Y-derived: `f.2 = x.g ≫ (hgYt ▸ gY.2)`, `gY ∈ Y.F`.  Case on dy.factorSplit gY.
        rcases dy.factorSplit gY hgY with ⟨gZ, hgZ, hgZt, hgZe⟩ | ⟨kk, hkt, hsplit⟩
        · -- dy-Y-derived ⇒ composite LEFT: `f.2 = x.g ≫ y.g ≫ gZ.2 = (x.comp y).g ≫ gZ.2`
          left
          refine ⟨gZ, hgZ, hgYt.trans hgZt, ?_⟩
          obtain ⟨ft, fm⟩ := f; obtain ⟨gYt, gYm⟩ := gY; obtain ⟨gZt, gZm⟩ := gZ
          cases hgYt; cases hgZt
          simp only at hgYe hgZe ⊢
          show fm = (x.g ≫ y.g) ≫ gZm
          rw [hgYe, hgZe, Cat.assoc]
        · -- dy-surviving ⇒ composite RIGHT, survivor in FIRST block of `dy.surv ++ dx.surv`.
          right
          -- target index: `⟨kk.1, _⟩` into the append (FIRST block).
          have hk_app : kk.1 < (dy.surv ++ dx.surv).length := by
            rw [List.length_append]; exact Nat.lt_of_lt_of_le kk.2 (Nat.le_add_right _ _)
          have hL : (dy.surv ++ dx.surv).get ⟨kk.1, hk_app⟩ = dy.surv.get kk := by
            simp [List.get_eq_getElem, List.getElem_append_left kk.2]
          refine ⟨⟨kk.1, hk_app⟩, hgYt.trans (hkt.trans hL.symm), ?_⟩
          obtain ⟨ft, fm⟩ := f; obtain ⟨gYt, gYm⟩ := gY
          cases hgYt; cases hkt
          simp only at hgYe hsplit ⊢
          -- the goal's projAppend cast IS `hL ▸` (defeq); rewrite to `hL`, then projL + hescL.
          rw [hgYe, hsplit,
            show (hL ▸ listProdProj (dy.surv ++ dx.surv) ⟨↑kk, hk_app⟩
                  : listProd (dy.surv ++ dx.surv) ⟶ dy.surv.get kk)
               = hL ▸ listProdProj (dy.surv ++ dx.surv) ⟨↑kk, hk_app⟩ from rfl,
            Cat.assoc (pair (fst ≫ dy.wf) (snd ≫ dx.wf)) (listProdAppendInv dy.surv dx.surv),
            listProdAppendInv_projL dy.surv dx.surv kk hk_app hL,
            ← Cat.assoc (pair (fst ≫ dy.wf) (snd ≫ dx.wf)) fst, fst_pair]
          have hb := congrArg (· ≫ dy.wf ≫ listProdProj dy.surv kk) hescL
          simp only [Cat.assoc] at hb ⊢
          exact hb.symm
      · -- dx-surviving ⇒ composite RIGHT, survivor in SECOND block of `dy.surv ++ dx.surv`.
        right
        have hk_app : dy.surv.length + kk.1 < (dy.surv ++ dx.surv).length := by
          rw [List.length_append]; exact Nat.add_lt_add_left kk.2 _
        have hR : (dy.surv ++ dx.surv).get ⟨dy.surv.length + kk.1, hk_app⟩ = dx.surv.get kk := by
          simp [List.get_eq_getElem, List.getElem_append_right (Nat.le_add_right _ _)]
        refine ⟨⟨dy.surv.length + kk.1, hk_app⟩, hkt.trans hR.symm, ?_⟩
        obtain ⟨ft, fm⟩ := f
        cases hkt
        simp only at hsplit ⊢
        rw [hsplit,
          show (hR ▸ listProdProj (dy.surv ++ dx.surv) ⟨dy.surv.length + ↑kk, hk_app⟩
                : listProd (dy.surv ++ dx.surv) ⟶ dx.surv.get kk)
             = hR ▸ listProdProj (dy.surv ++ dx.surv) ⟨dy.surv.length + ↑kk, hk_app⟩ from rfl,
          Cat.assoc (pair (fst ≫ dy.wf) (snd ≫ dx.wf)) (listProdAppendInv dy.surv dx.surv),
          listProdAppendInv_projR dy.surv dx.surv kk hk_app hR,
          ← Cat.assoc (pair (fst ≫ dy.wf) (snd ≫ dx.wf)) snd, snd_pair]
        have hb := congrArg (· ≫ dx.wf ≫ listProdProj dx.surv kk) hescR
        simp only [Cat.assoc] at hb ⊢
        exact hb.symm
    -- survDistinct: codomain is `Z`.  FIRST block (`dy.surv`): ∉ Z.targets directly by `dy.survDistinct`.
    -- SECOND block (`dx.surv`): ∉ Y.targets by `dx.survDistinct`; since `y : Y → Z` gives
    -- `Z.targets ⊆ Y.targets` (`pairHom_targets_subset y`), ∉ Y.targets ⟹ ∉ Z.targets.
    survDistinct := by
      intro k
      rcases Nat.lt_or_ge k.1 dy.surv.length with hlt | hge
      · -- FIRST block
        have hget : (dy.surv ++ dx.surv).get k = dy.surv.get ⟨k.1, hlt⟩ := by
          simp [List.get_eq_getElem, List.getElem_append_left hlt]
        rw [hget]; exact dy.survDistinct _
      · -- SECOND block
        have hkb : k.1 - dy.surv.length < dx.surv.length := by
          have hk2 := k.2; simp only [List.length_append] at hk2; omega
        have hget : (dy.surv ++ dx.surv).get k = dx.surv.get ⟨k.1 - dy.surv.length, hkb⟩ := by
          simp [List.get_eq_getElem, List.getElem_append_right hge]
        rw [hget]
        exact fun hZ => dx.survDistinct _ (pairHom_targets_subset y _ hZ)
    -- survInX: codomain is `X` (domain of `x.comp y`).  FIRST block (`dy.surv`): ∈ Y.targets by
    -- `dy.survInX`; `x : X → Y` gives `Y.targets ⊆ X.targets` (`pairHom_targets_subset x`).
    -- SECOND block (`dx.surv`): ∈ X.targets directly by `dx.survInX`.
    survInX := by
      intro k
      rcases Nat.lt_or_ge k.1 dy.surv.length with hlt | hge
      · have hget : (dy.surv ++ dx.surv).get k = dy.surv.get ⟨k.1, hlt⟩ := by
          simp [List.get_eq_getElem, List.getElem_append_left hlt]
        rw [hget]; exact pairHom_targets_subset x _ (dy.survInX _)
      · have hkb : k.1 - dy.surv.length < dx.surv.length := by
          have hk2 := k.2; simp only [List.length_append] at hk2; omega
        have hget : (dy.surv ++ dx.surv).get k = dx.surv.get ⟨k.1 - dy.surv.length, hkb⟩ := by
          simp [List.get_eq_getElem, List.getElem_append_right hge]
        rw [hget]; exact dx.survInX _ }

/-- **§1.547 — a dense map with NO new targets is already an ISO.**  If `x : X → Y` is dense and the
    domain's targets are contained in the codomain's (`X° ⊆ Y°`), then `x` is an iso in `Â`.  Reason:
    every surviving target lies in `X°` (`survInX`) but OUTSIDE `Y°` (`survDistinct`); with `X° ⊆ Y°`
    that is impossible, so `surv = []`, hence `W ≅ listProd [] = 1`, the density iso `e : X.A ≅ Y.A × 1`
    collapses to `X.A ≅ Y.A`, and `x.g = e ≫ fst` is an iso.  The inverse `Â`-arrow's compatibility is
    discharged from `factorSplit` (every `X`-factor is now Y-derived, the survivor branch being empty).
    This is the fraction-fiber slice-equivalence step `RatBelow U ≃ A/(∏U)`. -/
theorem dense_exactlyU_isIso {X Y : PairObj 𝒞} {x : PairHom X Y}
    (d : PairDense x) (hXY : ∀ T ∈ X.targets, T ∈ Y.targets) :
    @IsIso (PairObj 𝒞) _ X Y x := by
  -- (1) no survivors: a survivor's target is in `X°` (survInX) AND not in `Y°` (survDistinct),
  -- contradicting `X° ⊆ Y°`.  So `surv = []`.
  have hnil : d.surv = [] := by
    cases hs : d.surv with
    | nil => rfl
    | cons T ts =>
      have hpos : 0 < d.surv.length := by rw [hs]; exact Nat.succ_pos _
      exact absurd (hXY _ (d.survInX ⟨0, hpos⟩)) (d.survDistinct ⟨0, hpos⟩)
  -- (2) `listProd d.surv` is the terminal object (it reduces to `listProd [] = one`), so any two
  -- arrows into it agree; in particular `d.wg : listProd d.surv → W` precomposes a `term`.
  have hone : listProd d.surv = HasTerminal.one := by rw [hnil]; rfl
  have htermInto : ∀ {V : 𝒞} (a b : V ⟶ listProd d.surv), a = b := by
    intro V a b; revert a b; rw [hone]; intro a b; exact HasTerminal.uniq a b
  -- the `W`-component map `Y.A → W` used to invert: `term Y.A` lifted into `listProd surv`, then `wg`.
  let tW : Y.A ⟶ listProd d.surv := hnil ▸ (term Y.A : Y.A ⟶ HasTerminal.one)
  let ginv : Y.A ⟶ X.A := pair (Cat.id Y.A) (tW ≫ d.wg) ≫ d.einv
  -- `ginv ≫ x.g = id Y.A`: `ginv ≫ (e ≫ fst) = pair id _ ≫ (einv ≫ e) ≫ fst = pair id _ ≫ fst = id`.
  have hgi : ginv ≫ x.g = Cat.id Y.A := by
    rw [← d.proj]
    show (pair (Cat.id Y.A) (tW ≫ d.wg) ≫ d.einv) ≫ d.e ≫ fst = Cat.id Y.A
    rw [Cat.assoc, ← Cat.assoc d.einv d.e fst, d.e_iso₂, Cat.id_comp, fst_pair]
  -- `x.g ≫ ginv = id X.A`: reduces (after `← proj`, `← e_iso₁`) to
  -- `fst ≫ pair id (tW ≫ wg) = id (prod Y.A W)`, proven by joint monicity.
  have hcollapse : (fst : prod Y.A d.W ⟶ Y.A) ≫ pair (Cat.id Y.A) (tW ≫ d.wg)
      = Cat.id (prod Y.A d.W) := by
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, Cat.comp_id, Cat.id_comp]
    · rw [Cat.assoc, snd_pair, Cat.id_comp]
      -- `fst ≫ tW ≫ wg = snd`: `snd = (snd ≫ wf) ≫ wg` (wfg) and `fst ≫ tW = snd ≫ wf` (htermInto).
      have hsnd : (snd ≫ d.wf) ≫ d.wg = (snd : prod Y.A d.W ⟶ d.W) := by
        rw [Cat.assoc, d.wfg, Cat.comp_id]
      rw [← Cat.assoc (fst : prod Y.A d.W ⟶ Y.A) tW d.wg,
        htermInto (fst ≫ tW) (snd ≫ d.wf), hsnd]
  have hig : x.g ≫ ginv = Cat.id X.A := by
    rw [← d.proj]
    show (d.e ≫ fst) ≫ pair (Cat.id Y.A) (tW ≫ d.wg) ≫ d.einv = Cat.id X.A
    rw [Cat.assoc, ← Cat.assoc fst (pair _ _) d.einv, hcollapse, Cat.id_comp, d.e_iso₁]
  -- (3) the inverse `Â`-arrow: underlying `ginv`; compat from `factorSplit` (no survivors).
  let xinv : PairHom Y X :=
    { g := ginv
      compat := by
        intro p hp
        rcases d.factorSplit p hp with ⟨gY, hgY, h, hpe⟩ | ⟨k, _, _⟩
        · refine ⟨gY, hgY, h.symm, ?_⟩
          obtain ⟨pt, pm⟩ := p; obtain ⟨gYt, gYm⟩ := gY
          cases h; simp only at hpe ⊢
          rw [hpe, ← Cat.assoc, hgi, Cat.id_comp]
        · have hlen0 : d.surv.length = 0 := by rw [hnil]; rfl
          have hk := k.2; omega }
  exact ⟨xinv, PairHom.ext hig, PairHom.ext hgi⟩

/-! ### §1.547  FAITHFULNESS of the localisation `Â → Â[dense⁻¹] = A*` (the decisive payoff)

  In a calculus-of-fractions localisation `Â → Â[dense⁻¹]`, the localisation functor is FAITHFUL
  exactly when the dense class is LEFT-CANCELLABLE: two parallel `Â`-arrows `u, v : X → Y` that
  become equal in `A*` are identified there by a common DENSE roof `r : R → X` (so `r ≫ u = r ≫ v`
  in `Â`), and faithfulness is the implication `r ≫ u = r ≫ v → u = v`, i.e. `r` EPIC.  R2's
  all-monics class FAILED here (a monic roof leg is not epic).  §1.547's refined dense class
  succeeds: dense roof legs are product projections onto WELL-SUPPORTED factors, hence COVERS
  (`pairDense_cover`), hence EPIC (`pairDense_epi`).  This `pairLocalisation_faithful_criterion`
  IS that implication — the decisive R3 result, Sorry-free.  (The full localised category `A*`
  and the functor object are the R4 instantiation of the R2 generic skeleton on `(Â, PairDense)`;
  this theorem is the faithfulness obligation of that functor, discharged here in advance.) -/

/-- **§1.547 — FAITHFULNESS CRITERION for `Â → A*` (decisive payoff).**  Two parallel `Â`-arrows
    identified by a common DENSE roof are already equal.  This is the faithfulness of the §1.547
    localisation `Â → Â[dense⁻¹]`: the refined dense roof legs are product projections onto
    well-supported factors, hence covers (`pairDense_cover`), hence epic (`pairDense_epi`) — the
    exact left-cancellation the all-monics route (R2) lacked.  Sorry-free, choice-free. -/
theorem pairLocalisation_faithful_criterion [PullbacksTransferCovers 𝒞] {R X Y : PairObj 𝒞}
    {r : PairHom R X} (d : PairDense r) (u v : PairHom X Y)
    (hruv : r.comp u = r.comp v) : u = v :=
  pairDense_epi d u v hruv

/-! ### §1.547  WIDE EQUALIZER OF A FINITE LIST OF PARALLEL PAIRS (the `D ↪ A₁×A₂` kernel)

  The §1.547 product `(A₁,F₁)×(A₂,F₂) = (D,K)` takes `D ↪ A₁×A₂` to be the maximal subobject
  equalizing all morphisms in `H` with equal targets.  We realise this as the WIDE EQUALIZER of a
  finite LIST `L` of parallel pairs `(u,v : X ⟶ B)` over `X = A₁×A₂`: a mono `w : D ↪ X` with
  `w≫u = w≫v` for every listed pair, universal (any `k` equalizing all pairs factors uniquely
  through `w`).  Built by iterated binary equalizer (`products_pullbacks_implies_equalizers`).
  Avoiding `DecidableEq 𝒞`: instead of "morphisms with EQUAL targets" we list, for the product, the
  pairs `(fst≫f, snd≫f')` for matching factors — see `pairProd` below; the wide equalizer is the
  reusable kernel. -/

-- `eqMap_monic` (`Monic (eqMap u v)`) lives in `Freyd.S1_513_CoveringFamily`; the local copy was
-- deleted to avoid a duplicate declaration.

/-- A `WideEq` of a list `L` of parallel pairs over `X`: the maximal subobject equalizing all of
    them.  `dom`/`map` is the subobject `w : D ↪ X`; `eq` says `w` equalizes every listed pair;
    `mono` that `w` is monic; `lift`/`fac`/`uniq` the universal property. -/
structure WideEq (X : 𝒞) (L : List (Σ B : 𝒞, (X ⟶ B) × (X ⟶ B))) where
  dom  : 𝒞
  map  : dom ⟶ X
  mono : Monic map
  eq   : ∀ p ∈ L, map ≫ p.2.1 = map ≫ p.2.2
  lift : ∀ {Z : 𝒞} (k : Z ⟶ X), (∀ p ∈ L, k ≫ p.2.1 = k ≫ p.2.2) → (Z ⟶ dom)
  fac  : ∀ {Z : 𝒞} (k : Z ⟶ X) (h : ∀ p ∈ L, k ≫ p.2.1 = k ≫ p.2.2), lift k h ≫ map = k
  uniq : ∀ {Z : 𝒞} (k : Z ⟶ X) (h : ∀ p ∈ L, k ≫ p.2.1 = k ≫ p.2.2) (m : Z ⟶ dom),
           m ≫ map = k → m = lift k h

/-- The empty wide equalizer: `D = X`, `w = id` (no pairs to equalize). -/
def wideEqNil (X : 𝒞) : WideEq X [] where
  dom := X
  map := Cat.id X
  mono := by intro W a b hab; rw [← Cat.comp_id a, ← Cat.comp_id b]; exact hab
  eq p hp := absurd hp List.not_mem_nil
  lift k _ := k
  fac k _ := Cat.comp_id k
  uniq k _ m hm := by rw [← hm, Cat.comp_id]

/-- The cons step: equalize the head pair, then wide-equalize the tail composed with that
    equalizer's map.  `D = wideEq(tail ∘ e)`, `w = e' ≫ e` with `e = eqMap u v`. -/
def wideEqCons [HasEqualizers 𝒞] (X B : 𝒞) (u v : X ⟶ B)
    (L : List (Σ B : 𝒞, (X ⟶ B) × (X ⟶ B)))
    (tail : WideEq (eqObj u v) (L.map (fun p => ⟨p.1, eqMap u v ≫ p.2.1, eqMap u v ≫ p.2.2⟩))) :
    WideEq X (⟨B, u, v⟩ :: L) where
  dom := tail.dom
  map := tail.map ≫ eqMap u v
  mono := mono_comp' _ _ tail.mono (eqMap_monic u v)
  eq p hp := by
    rcases List.mem_cons.1 hp with h | h
    · subst h; rw [Cat.assoc, Cat.assoc, eqMap_eq u v]
    · -- p ∈ L: tail.eq on the pulled-back pair
      have := tail.eq ⟨p.1, eqMap u v ≫ p.2.1, eqMap u v ≫ p.2.2⟩ (by
        exact List.mem_map.2 ⟨p, h, rfl⟩)
      simp only at this
      rw [Cat.assoc, Cat.assoc, this]
  lift {Z} k hk := by
    -- k equalizes u,v (head) ⇒ factors through eqObj as k'; k' equalizes the tail's pulled pairs
    have hhead : k ≫ u = k ≫ v := hk _ (List.mem_cons.2 (Or.inl rfl))
    refine tail.lift (eqLift u v k hhead) ?_
    intro p hp
    rcases List.mem_map.1 hp with ⟨q, hq, hpe⟩
    subst hpe
    simp only
    have hkq := hk q (List.mem_cons.2 (Or.inr hq))
    rw [← Cat.assoc, ← Cat.assoc, eqLift_fac u v k hhead, hkq]
  fac {Z} k hk := by
    have hhead : k ≫ u = k ≫ v := hk _ (List.mem_cons.2 (Or.inl rfl))
    rw [← Cat.assoc, tail.fac, eqLift_fac u v k hhead]
  uniq {Z} k hk m hm := by
    have hhead : k ≫ u = k ≫ v := hk _ (List.mem_cons.2 (Or.inl rfl))
    apply tail.uniq
    -- `m ≫ tail.map = eqLift u v k hhead`: cancel mono `eqMap u v` after `≫ eqMap`
    apply eqLift_uniq u v k hhead
    -- goal `(m ≫ tail.map) ≫ eqMap u v = k`; `hm` is the right-associated form.
    rw [Cat.assoc]; exact hm

/-- The wide equalizer of an arbitrary finite list, by recursion on the list length (the
    recursive call is on the tail `L`, whose mapped form has length `L.length < (hd::L).length`,
    even though its ambient object changes from `X` to `eqObj u v`). -/
def wideEq [HasEqualizers 𝒞] (X : 𝒞) :
    (L : List (Σ B : 𝒞, (X ⟶ B) × (X ⟶ B))) → WideEq X L
  | [] => wideEqNil X
  | ⟨B, u, v⟩ :: L => wideEqCons X B u v L (wideEq (eqObj u v) _)
  termination_by L => L.length
  decreasing_by simp only [List.length_map, List.length_cons]; omega

/-! ### §1.547  `Â` IS CARTESIAN — terminal object (milestone R4)

  Book (§1.547): "Note that `Â` is Cartesian, e.g. `(A₁,F₁) × (A₂,F₂) = (D,K)`" where `D ↪ A₁×A₂`
  is the maximal subobject equalizing all morphisms in `H = H₁ ∪ H₂` (`H₁ = {fst≫f | f∈F₁}`,
  `H₂ = {snd≫f | f∈F₂}`) with equal targets, and `K = {w≫h | h∈H}`.  The forgetful functor
  `Â → A` REFLECTS these from `A`'s finite limits.

  TERMINAL.  The terminal object of `Â` is `(1, ∅)` — the terminator of `A` with NO factors.  A
  morphism `X → (1,∅)` is just `term X.A : X.A → 1` (compatibility vacuous, `Y.F = ∅`), and it is
  unique because `term` is unique in `A`. -/

/-- **§1.547 — the terminal object of `Â`** is `(1, ∅)`: the terminator of `A` with no factors. -/
def pairTerminal : PairObj 𝒞 where
  A := HasTerminal.one
  F := []
  wsupp := by intro p hp; exact absurd hp (List.not_mem_nil)
  distinct := by intro r hr; exact absurd hr (List.not_mem_nil)

/-- The unique `Â`-morphism `X → (1,∅)`: underlying `term`, compatibility vacuous (`F = ∅`). -/
def pairToTerminal (X : PairObj 𝒞) : PairHom X pairTerminal where
  g := term X.A
  compat _ hp := absurd hp (List.not_mem_nil)

/-- **§1.547 — `Â` has a terminal object** `(1,∅)`.  Uniqueness of `X → (1,∅)` is uniqueness of
    `X.A → 1` in `A` (`term_uniq`) lifted through `PairHom.ext` (a `PairHom` is its `.g`). -/
instance pairHasTerminal : HasTerminal (PairObj 𝒞) where
  one := pairTerminal
  trm X := pairToTerminal X
  uniq f g := PairHom.ext (term_uniq f.g g.g)

/-! ### §1.547  `Â` IS CARTESIAN — binary products `(A₁,F₁) × (A₂,F₂) = (D,K)`

  Book formula (§1.547): with `H₁ = {fst≫f | f∈F₁}`, `H₂ = {snd≫f' | f'∈F₂}` morphisms out of
  `A₁×A₂`, `D ↪ A₁×A₂` is the maximal subobject equalizing the morphisms of `H = H₁∪H₂` that share
  a target, and `K = {w≫h | h∈H}`.  Within `F₁` (resp. `F₂`) the targets are distinct, so the only
  forced equalizations are the CROSS pairs `(fst≫f, snd≫f')` for `f∈F₁`, `f'∈F₂` with `f° = f'°`.
  We collect those (decidable target match) and take their `wideEq`.

  `[DecidableEq 𝒞]` is used ONLY to build the cross-pair constraint list — Freyd's "morphisms with
  equal targets" is exactly this target-matching, which in his ambient (a category of sets) is
  decidable.  It is a NEW typeclass argument on the product construction; it weakens no protected
  statement. -/

section PairProd
variable [HasEqualizers 𝒞] [DecidableEq 𝒞]

/-- The CROSS constraint list for `(A₁,F₁)×(A₂,F₂)`: pairs `(fst≫f, snd≫f')` over `A₁×A₂` for
    `f∈F₁`, `f'∈F₂` whose targets agree (`f.1 = f'.1`), packaged for `wideEq`.  Built by a double
    `filterMap`, the target match decided by `DecidableEq 𝒞`. -/
def crossConstraints (X Y : PairObj 𝒞) :
    List (Σ B : 𝒞, (prod X.A Y.A ⟶ B) × (prod X.A Y.A ⟶ B)) :=
  X.F.flatMap (fun f => Y.F.filterMap (fun f' =>
    if h : f.1 = f'.1 then
      some ⟨f.1, (fst ≫ f.2, snd ≫ (h ▸ f'.2))⟩
    else none))

/-- The product OBJECT `D` of the §1.547 formula: the wide-equalizer of the cross constraints
    inside `A₁×A₂`. -/
def pairProdD (X Y : PairObj 𝒞) : 𝒞 := (wideEq (prod X.A Y.A) (crossConstraints X Y)).dom

/-- The subobject `w : D ↪ A₁×A₂`. -/
def pairProdW (X Y : PairObj 𝒞) : pairProdD X Y ⟶ prod X.A Y.A :=
  (wideEq (prod X.A Y.A) (crossConstraints X Y)).map

/-- `w` is monic. -/
theorem pairProdW_mono (X Y : PairObj 𝒞) : Monic (pairProdW X Y) :=
  (wideEq (prod X.A Y.A) (crossConstraints X Y)).mono

/-- `w` EQUALIZES every matched cross constraint: for `f∈F₁`, `f'∈F₂` with `f° = f'°` (`hff`),
    `w ≫ fst ≫ f.2 = w ≫ snd ≫ (hff ▸ f'.2)`.  The matched pair is in `crossConstraints` by the
    `dif_pos` branch, and `wideEq.eq` equalizes it. -/
theorem pairProdW_cross (X Y : PairObj 𝒞) {f : Σ T : 𝒞, X.A ⟶ T} (hf : f ∈ X.F)
    {f' : Σ T : 𝒞, Y.A ⟶ T} (hf' : f' ∈ Y.F) (hff : f.1 = f'.1) :
    pairProdW X Y ≫ fst ≫ f.2 = pairProdW X Y ≫ snd ≫ (hff ▸ f'.2) := by
  have hmem : (⟨f.1, (fst ≫ f.2, snd ≫ (hff ▸ f'.2))⟩ :
      Σ B : 𝒞, (prod X.A Y.A ⟶ B) × (prod X.A Y.A ⟶ B)) ∈ crossConstraints X Y := by
    refine List.mem_flatMap.2 ⟨f, hf, ?_⟩
    exact List.mem_filterMap.2 ⟨f', hf', by rw [dif_pos hff]⟩
  exact (wideEq (prod X.A Y.A) (crossConstraints X Y)).eq _ hmem

/-- The factor list `K = {w≫h | h∈H}` of the product object: `w≫fst≫f` for `f∈F₁`, `w≫snd≫f'`
    for `f'∈F₂`. -/
def pairProdK (X Y : PairObj 𝒞) : List (Σ T : 𝒞, pairProdD X Y ⟶ T) :=
  X.F.map (fun f => ⟨f.1, pairProdW X Y ≫ fst ≫ f.2⟩) ++
  Y.F.map (fun f' => ⟨f'.1, pairProdW X Y ≫ snd ≫ f'.2⟩)

/-- The targets in `K` are well-supported (they are targets of `F₁` or `F₂`). -/
theorem pairProdK_wsupp (X Y : PairObj 𝒞) : ∀ p ∈ pairProdK X Y, WellSupported p.1 := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · rcases List.mem_map.1 h with ⟨f, hf, he⟩; rw [← he]; exact X.wsupp f hf
  · rcases List.mem_map.1 h with ⟨f', hf', he⟩; rw [← he]; exact Y.wsupp f' hf'

/-- The factors of `K` go to DISTINCT targets (§1.547 product is again a legal `PairObj`).  Two
    factors of `K` with equal target are equal: both in the `F₁`-half (`X.distinct`), both in the
    `F₂`-half (`Y.distinct`), or one of each — the CROSS case, equal because `w` equalizes the cross
    constraint (`pairProdW_cross`).  `w≫fst≫(-)`/`w≫snd≫(-)` transport the factor equalities. -/
theorem pairProdK_distinct (X Y : PairObj 𝒞) :
    ∀ r ∈ pairProdK X Y, ∀ r' ∈ pairProdK X Y, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2 := by
  -- helper: `w≫fst≫(-)` of equal-after-transport factors of `X.F` are equal-after-transport
  have congT : ∀ {B B' : 𝒞} (m : pairProdD X Y ⟶ prod X.A Y.A) (p : X.A ⟶ B) (q : X.A ⟶ B')
      (h : B = B'), h ▸ p = q → (h ▸ (m ≫ fst ≫ p) : pairProdD X Y ⟶ B') = m ≫ fst ≫ q := by
    intro B B' m p q h hpq; cases h; simp only at hpq ⊢; rw [hpq]
  have congT' : ∀ {B B' : 𝒞} (m : pairProdD X Y ⟶ prod X.A Y.A) (p : Y.A ⟶ B) (q : Y.A ⟶ B')
      (h : B = B'), h ▸ p = q → (h ▸ (m ≫ snd ≫ p) : pairProdD X Y ⟶ B') = m ≫ snd ≫ q := by
    intro B B' m p q h hpq; cases h; simp only at hpq ⊢; rw [hpq]
  intro r hr r' hr' h
  rcases List.mem_append.1 hr with hL | hR <;> rcases List.mem_append.1 hr' with hL' | hR'
  · -- both F₁-half
    rcases List.mem_map.1 hL with ⟨f, hf, he⟩; rcases List.mem_map.1 hL' with ⟨f', hf', he'⟩
    subst he; subst he'
    exact congT (pairProdW X Y) f.2 f'.2 h (X.distinct f hf f' hf' h)
  · -- r in F₁-half, r' in F₂-half: cross
    rcases List.mem_map.1 hL with ⟨f, hf, he⟩; rcases List.mem_map.1 hR' with ⟨f', hf', he'⟩
    subst he; subst he'
    -- destruct factors so the target equality `h : f.1 = f'.1` is over plain objects
    obtain ⟨B, ff⟩ := f; obtain ⟨B', ff'⟩ := f'
    simp only at h ⊢; subst h
    -- goal: w≫fst≫ff = w≫snd≫ff';  pairProdW_cross at `rfl`
    have := pairProdW_cross X Y hf hf' rfl; simpa using this
  · -- r in F₂-half, r' in F₁-half: cross (symmetric)
    rcases List.mem_map.1 hR with ⟨f', hf', he⟩; rcases List.mem_map.1 hL' with ⟨f, hf, he'⟩
    subst he; subst he'
    obtain ⟨B', ff'⟩ := f'; obtain ⟨B, ff⟩ := f
    simp only at h ⊢; subst h
    -- goal: w≫snd≫ff' = w≫fst≫ff
    have := pairProdW_cross X Y hf hf' rfl; simpa using this.symm
  · -- both F₂-half
    rcases List.mem_map.1 hR with ⟨f, hf, he⟩; rcases List.mem_map.1 hR' with ⟨f', hf', he'⟩
    subst he; subst he'
    exact congT' (pairProdW X Y) f.2 f'.2 h (Y.distinct f hf f' hf' h)

/-- **§1.547 — the product object `(D,K)`** of `(A₁,F₁)` and `(A₂,F₂)` in `Â`. -/
def pairProdObj (X Y : PairObj 𝒞) : PairObj 𝒞 where
  A := pairProdD X Y
  F := pairProdK X Y
  wsupp := pairProdK_wsupp X Y
  distinct := pairProdK_distinct X Y

/-- **§1.547 — first projection** `(D,K) → (A₁,F₁)`, underlying `w≫fst`.  Compatibility: each
    `f∈F₁` has `w≫fst≫f ∈ K` (the `F₁`-half of `K`), with `(w≫fst)≫f = w≫fst≫f`. -/
def pairProjFst (X Y : PairObj 𝒞) : PairHom (pairProdObj X Y) X where
  g := pairProdW X Y ≫ fst
  compat p hp := by
    refine ⟨⟨p.1, pairProdW X Y ≫ fst ≫ p.2⟩, ?_, rfl, by rw [Cat.assoc]⟩
    exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨p, hp, rfl⟩))

/-- **§1.547 — second projection** `(D,K) → (A₂,F₂)`, underlying `w≫snd`. -/
def pairProjSnd (X Y : PairObj 𝒞) : PairHom (pairProdObj X Y) Y where
  g := pairProdW X Y ≫ snd
  compat p hp := by
    refine ⟨⟨p.1, pairProdW X Y ≫ snd ≫ p.2⟩, ?_, rfl, by rw [Cat.assoc]⟩
    exact List.mem_append.2 (Or.inr (List.mem_map.2 ⟨p, hp, rfl⟩))

/-- **§1.547 — UNIQUENESS of the product pairing** (unconditional).  Two `Â`-arrows into `(D,K)`
    agreeing after both projections are equal: underlying `α≫(w≫fst) = β≫(w≫fst)` and the `snd`
    analogue give `(α≫w)≫fst = (β≫w)≫fst` and `≫snd`, so `α≫w = β≫w` by joint monicity, then
    `α = β` (`w` monic, `pairProdW_mono`), then `PairHom.ext`. -/
theorem pairProd_hom_ext {Z X Y : PairObj 𝒞} (a b : PairHom Z (pairProdObj X Y))
    (h₁ : a.comp (pairProjFst X Y) = b.comp (pairProjFst X Y))
    (h₂ : a.comp (pairProjSnd X Y) = b.comp (pairProjSnd X Y)) : a = b := by
  apply PairHom.ext
  apply pairProdW_mono X Y
  apply fst_snd_jointly_monic
  · have := congrArg PairHom.g h₁
    simpa [PairHom.comp, pairProjFst, Cat.assoc] using this
  · have := congrArg PairHom.g h₂
    simpa [PairHom.comp, pairProjSnd, Cat.assoc] using this

/-! ### §1.547  Product pairing — EXISTENCE (the R3 `PairObj` distinctness gap)

  The pairing `⟨a,b⟩ : Z → (D,K)` has underlying `pair α β : A₀ → A₁×A₂`; it factors through the
  subobject `w : D ↪ A₁×A₂` iff `pair α β` EQUALIZES every cross constraint, i.e. for each matched
  `f∈F₁`, `f'∈F₂` (`f° = f'°`), `α≫f = β≫f'`.  By compatibility of `a` (resp. `b`) this is
  `r.2 = r'.2` for the factors `r,r' ∈ F₀` that `a` (resp. `b`) sends `f` (resp. `f'`) to — both of
  TARGET `f° = f'°`.  The book guarantees this because `F₀`'s targets are DISTINCT (so `r = r'`),
  but R3's `PairObj` (shared, downstream) records only well-supportedness, NOT distinctness.  So
  the pairing factors precisely under the hypothesis `Hdistinct`: any two factors of `Z`'s set with
  equal target are equal.  We state the pairing with this genuine hypothesis (NOT faked); the full
  unconditional `HasBinaryProducts (PairObj 𝒞)` instance is blocked on adding distinctness to
  `PairObj`, sharply documented here. -/

/-- The "distinct targets" property of a `PairObj`'s factor set: factors with equal target are
    equal (after transport).  Book §1.547 requires it of every object of `Â`; it is now a FIELD of
    `PairObj` (`PairObj.distinct`), so it always holds — this def is its abbreviation, and the
    §1.547 product pairing below is therefore UNCONDITIONAL. -/
def PairObj.DistinctTargets (Z : PairObj 𝒞) : Prop :=
  ∀ r ∈ Z.F, ∀ r' ∈ Z.F, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2

/-- The underlying lift `pair a.g b.g` equalizes every cross constraint (matched factors of `X`,`Y`
    pull back to factors of `Z` of equal target, equal by `Hdistinct`). -/
theorem pairPair_equ {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    ∀ q ∈ crossConstraints X Y, pair a.g b.g ≫ q.2.1 = pair a.g b.g ≫ q.2.2 := by
  intro q hq
  rcases List.mem_flatMap.1 hq with ⟨f, hf, hq2⟩
  rcases List.mem_filterMap.1 hq2 with ⟨f', hf', hq3⟩
  by_cases hff : f.1 = f'.1
  · rw [dif_pos hff] at hq3
    cases hq3
    obtain ⟨r, hr, hrt, hre⟩ := a.compat f hf
    obtain ⟨r', hr', hrt', hre'⟩ := b.compat f' hf'
    have hmatch : (hrt.trans (hff.trans hrt'.symm) : r.1 = r'.1) ▸ r.2 = r'.2 :=
      Hdistinct r hr r' hr' _
    obtain ⟨B, ff⟩ := f; obtain ⟨B', ff'⟩ := f'
    obtain ⟨C, rr⟩ := r; obtain ⟨C', rr'⟩ := r'
    simp only at hff hrt hrt' hre hre' hmatch ⊢
    subst hff; subst hrt; subst hrt'
    simp only at hre hre' hmatch ⊢
    rw [← Cat.assoc, ← Cat.assoc, fst_pair, snd_pair, hre, hre', hmatch]
  · rw [dif_neg hff] at hq3; exact absurd hq3 (by simp)

/-- The lift map `d : Z.A → D` of `pair a.g b.g` through the subobject `w`. -/
def pairPairMap {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) : Z.A ⟶ pairProdD X Y :=
  (wideEq (prod X.A Y.A) (crossConstraints X Y)).lift (pair a.g b.g) (pairPair_equ Hdistinct a b)

theorem pairPairMap_w {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    pairPairMap Hdistinct a b ≫ pairProdW X Y = pair a.g b.g :=
  (wideEq (prod X.A Y.A) (crossConstraints X Y)).fac (pair a.g b.g) (pairPair_equ Hdistinct a b)

/-- **§1.547 — the product PAIRING** `⟨a,b⟩ : Z → (D,K)` (data, choice-free), under the book's
    target-distinctness of `Z`.  Underlying `pair a.g b.g` factored through `w`; the compatibility
    is the two half-compatibilities of `a`,`b`. -/
def pairPair {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) : PairHom Z (pairProdObj X Y) where
  g := pairPairMap Hdistinct a b
  compat := by
    have hd := pairPairMap_w Hdistinct a b
    intro p hp
    rcases List.mem_append.1 hp with hL | hR
    · rcases List.mem_map.1 hL with ⟨f, hf, he⟩
      obtain ⟨r, hr, hrt, hre⟩ := a.compat f hf
      refine ⟨r, hr, by rw [hrt]; exact congrArg (·.1) he, ?_⟩
      subst he
      have : pairPairMap Hdistinct a b ≫ pairProdW X Y ≫ fst ≫ f.2 = a.g ≫ f.2 := by
        rw [← Cat.assoc _ (pairProdW X Y), hd, ← Cat.assoc, fst_pair]
      rw [this, hre]
    · rcases List.mem_map.1 hR with ⟨f', hf', he⟩
      obtain ⟨r', hr', hrt', hre'⟩ := b.compat f' hf'
      refine ⟨r', hr', by rw [hrt']; exact congrArg (·.1) he, ?_⟩
      subst he
      have : pairPairMap Hdistinct a b ≫ pairProdW X Y ≫ snd ≫ f'.2 = b.g ≫ f'.2 := by
        rw [← Cat.assoc _ (pairProdW X Y), hd, ← Cat.assoc, snd_pair]
      rw [this, hre']

theorem pairPair_fst {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    (pairPair Hdistinct a b).comp (pairProjFst X Y) = a :=
  PairHom.ext (by
    show (pairPairMap Hdistinct a b ≫ pairProdW X Y ≫ fst) = a.g
    rw [← Cat.assoc, pairPairMap_w, fst_pair])

theorem pairPair_snd {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    (pairPair Hdistinct a b).comp (pairProjSnd X Y) = b :=
  PairHom.ext (by
    show (pairPairMap Hdistinct a b ≫ pairProdW X Y ≫ snd) = b.g
    rw [← Cat.assoc, pairPairMap_w, snd_pair])

/-- **§1.547 — EXISTENCE of the product pairing** under the book's target-distinctness (the
    universal-property existence, repackaged from the choice-free `pairPair` data). -/
theorem pairProd_lift {Z X Y : PairObj 𝒞} (Hdistinct : Z.DistinctTargets)
    (a : PairHom Z X) (b : PairHom Z Y) :
    ∃ p : PairHom Z (pairProdObj X Y),
      p.comp (pairProjFst X Y) = a ∧ p.comp (pairProjSnd X Y) = b :=
  ⟨pairPair Hdistinct a b, pairPair_fst Hdistinct a b, pairPair_snd Hdistinct a b⟩

/-! ### §1.547  `Â` HAS BINARY PRODUCTS — UNCONDITIONAL (distinctness is a `PairObj` field)

  Freyd's §1.547 takes EVERY object of `Â` to have factors to "DISTINCT well-supported targets".
  Since distinctness is now a FIELD of `PairObj` (`PairObj.distinct`), the §1.547 product pairing is
  TOTAL with NO side hypothesis: `pair = pairPair Z.distinct`, `pair_uniq = pairProd_hom_ext`.  This
  is the resolution of the DISTINCTNESS GATE that keeps `ratCap S : CapStep S` unconditional in `S`
  (an arbitrary pre-regular `S` has objects `PairObj S` that carry their own distinctness witness). -/

/-- **§1.547 — `Â` HAS BINARY PRODUCTS** (UNCONDITIONAL).  Object/projections are the §1.547 `(D,K)`
    formula (`pairProdObj`/`pairProj…`); `pair` is the lift `pairPair` fed the object's own
    `distinct` field; `pair_uniq` is `pairProd_hom_ext`.  No extra typeclass — distinctness rides on
    every `PairObj`. -/
instance pairHasBinaryProducts [HasEqualizers 𝒞] [DecidableEq 𝒞] :
    HasBinaryProducts (PairObj 𝒞) where
  prod := pairProdObj
  fst {X Y} := pairProjFst X Y
  snd {X Y} := pairProjSnd X Y
  pair {Z _ _} a b := pairPair Z.distinct a b
  fst_pair {Z _ _} a b := pairPair_fst Z.distinct a b
  snd_pair {Z _ _} a b := pairPair_snd Z.distinct a b
  pair_uniq {Z _ _} a b h h₁ h₂ :=
    pairProd_hom_ext h _
      (h₁.trans (pairPair_fst Z.distinct a b).symm)
      (h₂.trans (pairPair_snd Z.distinct a b).symm)

end PairProd

/-! ### §1.547  `Â` HAS EQUALIZERS — the forgetful functor creates them from `A`'s equalizers

  The equalizer of `a, b : (A,F) → (B,G)` in `Â` is `(E, e^*F)` where `e : E ↪ A` is the equalizer
  of the underlying `a.g, b.g` in `A` and `e^*F = {⟨f°, e≫f⟩ | f ∈ F}` is `F` pulled back along `e`.
  Its targets are those of `F` (still well-supported); its factors stay distinct because `e` is monic
  (so `e≫f = e≫f' ⟹ f = f'`, combined with `F`'s distinctness).  The equalizer `PairHom`
  `(E,e^*F) → (A,F)` is underlying-`e` (compat: `f ∈ F` ↦ `e≫f ∈ e^*F`); its universal property is
  the underlying equalizer's (`eqLift`), the lifted arrow's compat coming from `k`'s own compat.
  `pairForget` thus CREATES equalizers, giving `Â` finite limits (hence pullbacks via §1.432). -/

section PairEq
variable [HasEqualizers 𝒞]

/-- The factor set of the §1.547 equalizer object: `F` pulled back along the underlying equalizer
    `e = eqMap a.g b.g`.  `{⟨f°, e≫f⟩ | f ∈ X.F}`. -/
def pairEqK {X Y : PairObj 𝒞} (a b : PairHom X Y) : List (Σ T : 𝒞, eqObj a.g b.g ⟶ T) :=
  X.F.map (fun f => ⟨f.1, eqMap a.g b.g ≫ f.2⟩)

theorem pairEqK_wsupp {X Y : PairObj 𝒞} (a b : PairHom X Y) :
    ∀ p ∈ pairEqK a b, WellSupported p.1 := by
  intro p hp; rcases List.mem_map.1 hp with ⟨f, hf, he⟩; rw [← he]; exact X.wsupp f hf

theorem pairEqK_distinct {X Y : PairObj 𝒞} (a b : PairHom X Y) :
    ∀ r ∈ pairEqK a b, ∀ r' ∈ pairEqK a b, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2 := by
  have congE : ∀ {B B' : 𝒞} (p : X.A ⟶ B) (q : X.A ⟶ B') (h : B = B'), h ▸ p = q →
      (h ▸ (eqMap a.g b.g ≫ p) : eqObj a.g b.g ⟶ B') = eqMap a.g b.g ≫ q := by
    intro B B' p q h hpq; cases h; simp only at hpq ⊢; rw [hpq]
  intro r hr r' hr' h
  rcases List.mem_map.1 hr with ⟨f, hf, he⟩; rcases List.mem_map.1 hr' with ⟨f', hf', he'⟩
  subst he; subst he'
  exact congE f.2 f'.2 h (X.distinct f hf f' hf' h)

/-- The §1.547 equalizer OBJECT `(E, e^*F)` of `a, b : X → Y`. -/
def pairEqObj {X Y : PairObj 𝒞} (a b : PairHom X Y) : PairObj 𝒞 where
  A := eqObj a.g b.g
  F := pairEqK a b
  wsupp := pairEqK_wsupp a b
  distinct := pairEqK_distinct a b

/-- The equalizer `PairHom` `(E,e^*F) → X`, underlying `e = eqMap a.g b.g`.  Compat: `f ∈ X.F` maps
    to `⟨f°, e≫f⟩ ∈ e^*F`. -/
def pairEqMap {X Y : PairObj 𝒞} (a b : PairHom X Y) : PairHom (pairEqObj a b) X where
  g := eqMap a.g b.g
  compat p hp := ⟨⟨p.1, eqMap a.g b.g ≫ p.2⟩, List.mem_map.2 ⟨p, hp, rfl⟩, rfl, rfl⟩

/-- The equalizer `PairHom` equalizes `a, b` (its underlying `e` does, `eqMap_eq`). -/
theorem pairEqMap_eq {X Y : PairObj 𝒞} (a b : PairHom X Y) :
    (pairEqMap a b).comp a = (pairEqMap a b).comp b :=
  PairHom.ext (by show eqMap a.g b.g ≫ a.g = eqMap a.g b.g ≫ b.g; exact eqMap_eq a.g b.g)

/-- The underlying equalizer condition of a `Â`-cone `k : Z → X` (`k.comp a = k.comp b` gives
    `k.g ≫ a.g = k.g ≫ b.g`). -/
theorem pairEqLift_hyp {X Y : PairObj 𝒞} (a b : PairHom X Y) {Z : PairObj 𝒞} {k : PairHom Z X}
    (hk : k.comp a = k.comp b) : k.g ≫ a.g = k.g ≫ b.g := by
  have := congrArg PairHom.g hk; simpa [PairHom.comp] using this

/-- The lift of a cone `(k : Z → X` with `k.comp a = k.comp b)` through the §1.547 equalizer.
    Underlying `eqLift` of `k.g`; compat lifted from `k`'s compat (a factor `⟨f°,e≫f⟩ ∈ e^*F` is hit
    by `k`'s factor for `f`, since `(eqLift k.g)≫e≫f = k.g≫f`). -/
def pairEqLift {X Y : PairObj 𝒞} (a b : PairHom X Y) {Z : PairObj 𝒞} (k : PairHom Z X)
    (hk : k.comp a = k.comp b) : PairHom Z (pairEqObj a b) where
  g := eqLift a.g b.g k.g (pairEqLift_hyp a b hk)
  compat p hp := by
    rcases List.mem_map.1 hp with ⟨f, hf, he⟩
    obtain ⟨q, hq, hqt, hqe⟩ := k.compat f hf
    refine ⟨q, hq, by rw [hqt]; exact congrArg (·.1) he, ?_⟩
    -- (eqLift k.g) ≫ (e≫f.2) = k.g ≫ f.2 = q.2 (transported)
    subst he
    have hfac : eqLift a.g b.g k.g (pairEqLift_hyp a b hk) ≫ eqMap a.g b.g = k.g :=
      eqLift_fac a.g b.g k.g (pairEqLift_hyp a b hk)
    have : eqLift a.g b.g k.g (pairEqLift_hyp a b hk) ≫ (eqMap a.g b.g ≫ f.2) = k.g ≫ f.2 := by
      rw [← Cat.assoc, hfac]
    rw [this, hqe]

theorem pairEqLift_fac {X Y : PairObj 𝒞} (a b : PairHom X Y) {Z : PairObj 𝒞} (k : PairHom Z X)
    (hk : k.comp a = k.comp b) : (pairEqLift a b k hk).comp (pairEqMap a b) = k :=
  PairHom.ext (by
    show eqLift a.g b.g k.g (pairEqLift_hyp a b hk) ≫ eqMap a.g b.g = k.g
    exact eqLift_fac a.g b.g k.g (pairEqLift_hyp a b hk))

theorem pairEqLift_uniq {X Y : PairObj 𝒞} (a b : PairHom X Y) {Z : PairObj 𝒞} (k : PairHom Z X)
    (hk : k.comp a = k.comp b) (m : PairHom Z (pairEqObj a b))
    (hm : m.comp (pairEqMap a b) = k) : m = pairEqLift a b k hk :=
  PairHom.ext (by
    apply eqLift_uniq a.g b.g k.g (pairEqLift_hyp a b hk) m.g
    have := congrArg PairHom.g hm; simpa [PairHom.comp, pairEqMap] using this)

/-- **§1.547 — `Â` HAS EQUALIZERS** (forgetful functor creates them).  The equalizer cone is
    `(E,e^*F)` with map `pairEqMap`; universal property from the underlying equalizer in `A`. -/
instance pairHasEqualizers : HasEqualizers (PairObj 𝒞) where
  eq _ _ a b :=
    { cone := ⟨pairEqObj a b, pairEqMap a b, pairEqMap_eq a b⟩
      lift := fun c => pairEqLift a b c.map c.eq
      fac := fun c => pairEqLift_fac a b c.map c.eq
      uniq := fun c m hm => pairEqLift_uniq a b c.map c.eq m hm }

/-- **§1.547 — `Â` HAS PULLBACKS** (§1.432: terminal + products + equalizers ⟹ pullbacks).  The
    pullback of `f, g` is the equalizer of `fst≫f`, `snd≫g` on the product — built once and for all
    by `products_equalizers_implies_pullbacks` on the `Â`-level finite limits. -/
instance pairHasPullbacks [DecidableEq 𝒞] : HasPullbacks (PairObj 𝒞) where
  has f g := products_equalizers_implies_pullbacks f g

/-! ### §1.547  Covers in `Â` and the pre-regular structure

  Freyd (§1.547): "the forgetful functor `Â → A` is faithful and preserves pullbacks and covers",
  and `A*` (the localisation) "is equivalent to a directed union of slices", each pre-regular — that
  slice-equivalence is what makes `A*` pre-regular.  We make the cover bridge precise and isolate
  the one genuine §1.547 content as a sharply-documented obstruction.

  FORWARD (`pairCover_underlying`, PROVEN): an `Â`-cover `f` has underlying `f.g` an `A`-cover.  Any
  `A`-monic `m : C ↪ Y.A` factoring `f.g` LIFTS to an `Â`-monic `(C, m^*F) → Y` factoring `f`; the
  `Â`-cover forces it iso in `Â`, hence `m` iso in `A`.  The lift is `Â`-monic because `m` is a
  genuine `A`-mono.

  The CONVERSE (underlying `A`-cover ⟹ `Â`-cover) does NOT hold for a free `pairForget`: `Â`-monos
  are tested only against the (fewer) `Â`-arrows, so `pairForget` does not reflect monos, and the
  intrinsic cover-transfer in `Â` is exactly Freyd's slice-equivalence verification (the directed
  union of pre-regular slices) — the same content the directed-colimit route hits at the strictness
  wall (module docstring, R1).  `pairPullbacksTransferCovers` carries the book's true statement with
  that single isolated obstruction; everything feeding it (finite limits, the forward bridge) is
  Sorry-free. -/

/-- Pull back a factor set along an `A`-arrow `e : E → X.A`: `{⟨f°, e≫f⟩ | f ∈ X.F}`.  When `e` is
    monic this is again distinct (and the targets are unchanged, so still well-supported). -/
def pullbackFactors {E : 𝒞} {X : PairObj 𝒞} (e : E ⟶ X.A) : List (Σ T : 𝒞, E ⟶ T) :=
  X.F.map (fun f => ⟨f.1, e ≫ f.2⟩)

theorem pullbackFactors_wsupp {E : 𝒞} {X : PairObj 𝒞} (e : E ⟶ X.A) :
    ∀ p ∈ pullbackFactors e, WellSupported p.1 := by
  intro p hp; rcases List.mem_map.1 hp with ⟨f, hf, he⟩; rw [← he]; exact X.wsupp f hf

-- NOTE (R8): distinctness of a SINGLE-`e` pulled-back factor list needs NO `Monic e`.  Two entries
-- `⟨f°, e≫f⟩`, `⟨f'°, e≫f'⟩` of equal target have `f = f'` by `X`'s OWN distinctness (the targets are
-- unchanged by `e`), and `e≫f = e≫f'` follows by congruence — `e` monic is irrelevant.  Dropping the
-- spurious hypothesis is what makes the eventual `pairDense_pb` explicit-cone factor lists (each a
-- single-`e` pullback along a NON-monic projection `fst`) legal `PairObj`s with no extra obligation.
theorem pullbackFactors_distinct {E : 𝒞} {X : PairObj 𝒞} {e : E ⟶ X.A} :
    ∀ r ∈ pullbackFactors e, ∀ r' ∈ pullbackFactors e, ∀ h : r.1 = r'.1, h ▸ r.2 = r'.2 := by
  have congP : ∀ {B B' : 𝒞} (p : X.A ⟶ B) (q : X.A ⟶ B') (h : B = B'), h ▸ p = q →
      (h ▸ (e ≫ p) : E ⟶ B') = e ≫ q := by
    intro B B' p q h hpq; cases h; simp only at hpq ⊢; rw [hpq]
  intro r hr r' hr' h
  rcases List.mem_map.1 hr with ⟨f, hf, he⟩; rcases List.mem_map.1 hr' with ⟨f', hf', he'⟩
  subst he; subst he'
  exact congP f.2 f'.2 h (X.distinct f hf f' hf' h)

/-- The lift object `(C, m^*Y.F)` for an `A`-monic `m : C → Y.A` into a `PairObj` `Y`. -/
def liftObj {C : 𝒞} {Y : PairObj 𝒞} {m : C ⟶ Y.A} (_ : Monic m) : PairObj 𝒞 where
  A := C
  F := pullbackFactors m
  wsupp := pullbackFactors_wsupp m
  distinct := pullbackFactors_distinct

/-- The lifted `Â`-arrow `m̂ : (C, m^*F) → Y`, underlying `m`.  Compat: `f ∈ Y.F` ↦ `⟨f°, m≫f⟩`. -/
def liftMono {C : 𝒞} {Y : PairObj 𝒞} {m : C ⟶ Y.A} (hm : Monic m) : PairHom (liftObj hm) Y where
  g := m
  compat p hp := ⟨⟨p.1, m ≫ p.2⟩, List.mem_map.2 ⟨p, hp, rfl⟩, rfl, rfl⟩

/-- The lifted arrow is monic in `Â`: parallel `Â`-arrows `a, b` with `a.comp m̂ = b.comp m̂` have
    `a.g ≫ m = b.g ≫ m`, and `m` an `A`-mono cancels to `a.g = b.g`, so `a = b`. -/
theorem liftMono_mono {C : 𝒞} {Y : PairObj 𝒞} {m : C ⟶ Y.A} (hm : Monic m) :
    @Monic (PairObj 𝒞) _ (liftObj hm) Y (liftMono hm) := by
  intro Z a b hab
  apply PairHom.ext
  apply hm
  have : (a.comp (liftMono hm)).g = (b.comp (liftMono hm)).g := congrArg PairHom.g hab
  simpa [PairHom.comp, liftMono] using this

/-- **§1.547 forward bridge — an `Â`-cover has an `A`-cover underlying arrow.**  Any `A`-monic `m`
    factoring `f.g` lifts to an `Â`-monic `liftMono` factoring `f`; the `Â`-cover forces it iso in
    `Â`, hence `m` iso in `A`.  Proves Freyd's "`pairForget` preserves covers" (forward half). -/
theorem pairCover_underlying {X Y : PairObj 𝒞} {f : PairHom X Y}
    (hf : @Cover (PairObj 𝒞) _ X Y f) : Cover f.g := by
  intro C m h hm hfac
  -- lift `m` to `Â`-monic `m̂`; `f` factors through it via `ĥ` underlying `h`
  have hĥcompat : ∀ p ∈ (liftObj hm).F, ∃ q ∈ X.F, ∃ ht : q.1 = p.1, h ≫ p.2 = ht ▸ q.2 := by
    intro p hp
    rcases List.mem_map.1 hp with ⟨e, he, hpe⟩
    obtain ⟨q, hq, hqt, hqe⟩ := f.compat e he
    refine ⟨q, hq, by rw [hqt]; exact congrArg (·.1) hpe, ?_⟩
    subst hpe
    -- h ≫ (m ≫ e.2) = (h ≫ m) ≫ e.2 = f.g ≫ e.2 = q.2
    show h ≫ m ≫ e.2 = hqt ▸ q.2
    rw [← Cat.assoc, hfac, hqe]
  let ĥ : PairHom X (liftObj hm) := ⟨h, hĥcompat⟩
  have hĥm : ĥ.comp (liftMono hm) = f := PairHom.ext (by show h ≫ m = f.g; exact hfac)
  obtain ⟨n, hn₁, hn₂⟩ := hf (liftMono hm) ĥ (liftMono_mono hm) hĥm
  -- `n : Y → liftObj hm` inverts `liftMono` in `Â`; underlying gives `m` iso in `A`
  refine ⟨n.g, ?_, ?_⟩
  · have := congrArg PairHom.g hn₁; simpa [PairHom.comp, liftMono] using this
  · have := congrArg PairHom.g hn₂; simpa [PairHom.comp, liftMono] using this

/-! ### Base change of a product projection (reusable `A`-level fact)

  The slice-equivalence verification (§1.547) ultimately rests on a single elementary `A`-level
  fact: the pullback of a PRODUCT PROJECTION `fst : Y × W → Y` along any `g : Z → Y` is again a
  product projection `fst : Z × W → Z`.  This is TRUE and CONSTRUCTIVE in any category with binary
  products (no equalizers/pullbacks instance needed — we exhibit the pullback cone directly).  It is
  the `A`-shape that the dense `Â`-pullback is meant to descend to (`X.A ≅ Y.A × W`, `x.g = fst`),
  so it is the honest core of both slice-equivalence payoffs and is proven here Sorry-free. -/

/-- The cone with apex `Z × W`, `π₁ = fst`, `π₂ = pair (fst ≫ g) snd`, over the cospan
    `(g : Z → Y, fst : Y × W → Y)`. -/
def projBaseChangeCone {Z Y W : 𝒞} (g : Z ⟶ Y) :
    Cone g (fst : prod Y W ⟶ Y) where
  pt := prod Z W
  π₁ := fst
  π₂ := pair (fst ≫ g) snd
  w  := by rw [fst_pair]

/-- **Base change of a projection is a projection.**  The cone `projBaseChangeCone g` is a
    pullback of `(g, fst)`: the lift of any cone `d` is `pair d.π₁ (d.π₂ ≫ snd)`; the square
    `d.π₁ ≫ g = d.π₂ ≫ fst` recovers the `Y`-component, `snd` the `W`-component. -/
theorem projBaseChangeCone_isPullback {Z Y W : 𝒞} (g : Z ⟶ Y) :
    (projBaseChangeCone g (W := W)).IsPullback := by
  intro d
  refine ⟨pair d.π₁ (d.π₂ ≫ snd), ⟨?_, ?_⟩, ?_⟩
  · -- `≫ π₁ = ≫ fst = d.π₁`
    exact fst_pair _ _
  · -- `≫ π₂ = pair (fst≫g) snd`: agree on both projections with `d.π₂`
    show pair d.π₁ (d.π₂ ≫ snd) ≫ pair (fst ≫ g) snd = d.π₂
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair]; exact d.w
    · rw [Cat.assoc, snd_pair, snd_pair]
  · -- uniqueness: any `v` with the two leg equations equals the pair
    intro v hv₁ hv₂
    apply fst_snd_jointly_monic
    · rw [fst_pair]; exact hv₁
    · -- `v ≫ snd = (v ≫ π₂) ≫ snd = d.π₂ ≫ snd`
      rw [snd_pair]
      have : v ≫ pair (fst ≫ g) snd = d.π₂ := hv₂
      calc v ≫ (snd : prod Z W ⟶ W)
            = v ≫ (pair (fst ≫ g) snd ≫ (snd : prod Y W ⟶ W)) := by rw [snd_pair]
        _ = (v ≫ pair (fst ≫ g) snd) ≫ snd := by rw [Cat.assoc]
        _ = d.π₂ ≫ snd := by rw [this]

/-- **Iso on the right leg transports a pullback.**  If `c : Cone f h` is a pullback and `e : B' ≅ B`
    with inverse `einv` (so `e ≫ einv = id`, `einv ≫ e = id`), then the cone over the cospan
    `(f, e ≫ h)` with the SAME apex, first leg `c.π₁`, and second leg `c.π₂ ≫ einv` is again a
    pullback.  (Reindexing cones: a cone over `(f, e≫h)` is exactly a cone over `(f, h)` with its
    second leg post-composed with `e`.) -/
theorem isPullback_precomp_iso_right {A B B' C : 𝒞} {f : A ⟶ C} {h : B ⟶ C}
    {c : Cone f h} (hc : c.IsPullback) (e : B' ⟶ B) (einv : B ⟶ B')
    (he₁ : e ≫ einv = Cat.id B') (he₂ : einv ≫ e = Cat.id B) :
    (⟨c.pt, c.π₁, c.π₂ ≫ einv, by
      rw [Cat.assoc, ← Cat.assoc einv, he₂, Cat.id_comp]; exact c.w⟩ : Cone f (e ≫ h)).IsPullback := by
  intro d
  -- reindex `d : Cone f (e≫h)` to `d' : Cone f h` by post-composing leg 2 with `e`
  have hd'w : d.π₁ ≫ f = (d.π₂ ≫ e) ≫ h := by rw [Cat.assoc]; exact d.w
  let d' : Cone f h := ⟨d.pt, d.π₁, d.π₂ ≫ e, hd'w⟩
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc d'
  refine ⟨u, ⟨hu₁, ?_⟩, ?_⟩
  · -- `u ≫ (c.π₂ ≫ einv) = d.π₂`: from `u ≫ c.π₂ = d.π₂ ≫ e`, cancel `e`
    rw [← Cat.assoc, hu₂]
    show (d.π₂ ≫ e) ≫ einv = d.π₂
    rw [Cat.assoc, he₁, Cat.comp_id]
  · intro v hv₁ hv₂
    apply huniq v hv₁
    -- `v ≫ c.π₂ = d.π₂ ≫ e`: from `v ≫ (c.π₂ ≫ einv) = d.π₂`
    show v ≫ c.π₂ = d.π₂ ≫ e
    have hvc : v ≫ (c.π₂ ≫ einv) = d.π₂ := hv₂
    have key : (v ≫ (c.π₂ ≫ einv)) ≫ e = d.π₂ ≫ e := congrArg (· ≫ e) hvc
    calc v ≫ c.π₂
          = (v ≫ (c.π₂ ≫ einv)) ≫ e := by
            simp only [Cat.assoc, he₂, Cat.comp_id]
      _ = d.π₂ ≫ e := key

/-- **§1.547 — the `A`-level pullback of the cospan `(g.g, x.g)` is a PROJECTION.**  For dense `x`
    (data `dx`, so `x.g = dx.e ≫ fst` with `dx.e : X.A ≅ Y.A × dx.W`), the pullback of `(g.g, x.g)`
    in `A` has apex `prod Z.A dx.W`, first leg `fst : Z.A × dx.W → Z.A`.  This is `projBaseChangeCone`
    (base change of `fst` along `g.g`) reindexed across the density iso (`isPullback_precomp_iso_right`).
    The honest `A`-LEVEL core of dense-pullback-closure (the `Â`-apex `E` then collapses onto this). -/
def pairDensePbBaseCone [PullbacksTransferCovers 𝒞] {X Y Z : PairObj 𝒞}
    (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) : Cone g.g x.g where
  pt := prod Z.A dx.W
  π₁ := fst
  π₂ := pair (fst ≫ g.g) snd ≫ dx.einv
  w := by
    -- `fst ≫ g.g = (pair (fst≫g.g) snd ≫ dx.einv) ≫ x.g`, using `x.g = dx.e ≫ fst` and `einv≫e=id`
    have hx : dx.einv ≫ x.g = fst := by rw [← dx.proj, ← Cat.assoc, dx.e_iso₂, Cat.id_comp]
    calc (fst : prod Z.A dx.W ⟶ Z.A) ≫ g.g
          = pair (fst ≫ g.g) snd ≫ (fst : prod Y.A dx.W ⟶ Y.A) := by rw [fst_pair]
      _ = pair (fst ≫ g.g) snd ≫ (dx.einv ≫ x.g) := by rw [hx]
      _ = (pair (fst ≫ g.g) snd ≫ dx.einv) ≫ x.g := by rw [Cat.assoc]

theorem pairDensePbBaseCone_isPullback [PullbacksTransferCovers 𝒞] {X Y Z : PairObj 𝒞}
    (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    (pairDensePbBaseCone x g dx).IsPullback := by
  -- `x.g = dx.e ≫ fst`; reindex `projBaseChangeCone g.g` (pullback of `(g.g, fst)`) by `dx.e`.
  have hxg : x.g = dx.e ≫ (fst : prod Y.A dx.W ⟶ Y.A) := dx.proj.symm
  have hbase := isPullback_precomp_iso_right
    (projBaseChangeCone_isPullback (W := dx.W) g.g) dx.e dx.einv dx.e_iso₁ dx.e_iso₂
  -- `hbase` is a pullback of `(g.g, dx.e ≫ fst)`; our cone has the SAME pt/π₁/π₂ but cospan `x.g`.
  -- transfer cone-by-cone, recasting each `d : Cone g.g x.g` to `Cone g.g (dx.e≫fst)`.
  intro d
  have hd'w : d.π₁ ≫ g.g = d.π₂ ≫ (dx.e ≫ (fst : prod Y.A dx.W ⟶ Y.A)) := by rw [← hxg]; exact d.w
  let d' : Cone g.g (dx.e ≫ (fst : prod Y.A dx.W ⟶ Y.A)) := ⟨d.pt, d.π₁, d.π₂, hd'w⟩
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hbase d'
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · show u ≫ (fst : prod Z.A dx.W ⟶ Z.A) = d.π₁; exact hu₁
  · show u ≫ (pair (fst ≫ g.g) snd ≫ dx.einv) = d.π₂; exact hu₂
  · intro v hv₁ hv₂
    exact huniq v hv₁ hv₂

/-- The underlying `A`-cone of an `Â`-cone (apply the forgetful functor `pairForget` leg-wise).
    Its square is `pairForget` applied to `c.w` (functoriality of `.g`). -/
def pairForgetCone {A B C : PairObj 𝒞} {f : A ⟶ B} {g : C ⟶ B}
    (c : @Cone (PairObj 𝒞) _ _ _ _ f g) : Cone f.g g.g where
  pt := c.pt.A
  π₁ := c.π₁.g
  π₂ := c.π₂.g
  w  := congrArg PairHom.g c.w

/-- **§1.547 — the `A`-cover reduction (Sorry-free).**  IF the underlying `A`-cone of the `Â`-pullback
    `c` is itself an `A`-pullback, then the opposite leg `c.π₂.g` is an `A`-cover.  Combines the
    forward bridge `pairCover_underlying` (`Â`-cover `f` ⟹ `A`-cover `f.g`) with `A`'s own
    `PullbacksTransferCovers` applied to the underlying cone.  This is the honest `A`-LEVEL half of the
    transfer; what it does NOT supply is the hypothesis `hpbA`, because `pairForget` does NOT preserve
    pullbacks: the `Â`-pullback apex `c.pt.A` is the cross-constrained equalizer subobject
    (`canonical_pb_probe`: `c.π₁.g = eqMap … ≫ pairProjFst.g`), strictly smaller than the `A`-pullback
    of `(f.g, g.g)` in general.  So `hpbA` holds only in special cases (e.g. dense `f`, where the
    cross-constraints are absorbed by the density iso); for an arbitrary `Â`-cover it is exactly the
    missing slice-equivalence content.  Stated with `hpbA` as an explicit hypothesis so the half that
    IS constructive is recorded Sorry-free. -/
theorem pairCover_pi2_underlying_of_underlying_pullback [PullbacksTransferCovers 𝒞]
    {A B C : PairObj 𝒞} {f : A ⟶ B} {g : C ⟶ B}
    (c : @Cone (PairObj 𝒞) _ _ _ _ f g) (hpbA : (pairForgetCone c).IsPullback)
    (hf : @Cover (PairObj 𝒞) _ _ _ f) : Cover (c.π₂.g) :=
  PullbacksTransferCovers.pullbacks_transfer_covers (pairForgetCone c) hpbA (pairCover_underlying hf)

/- (DEAD route — documents the commented-out `pairPullbacksTransferCovers` below.)
   **§1.547 — `Â`'s pullbacks transfer covers** (the pre-regular closure condition).  The STATEMENT
    is Freyd's genuine `PullbacksTransferCovers`: in a pullback square in `Â`, the leg opposite an
    `Â`-cover is an `Â`-cover.  Freyd discharges this for `Â` via the slice equivalence — "`A*` is a
    directed union of slices `A*|U`, each pre-regular", so the cover structure of `Â`/`A*` is read
    off the pre-regular slices (§1.547, and §1.481 localisation preserves pre-regular).

    The forward bridge `pairCover_underlying` (`Â`-cover ⟹ `A`-cover, Sorry-free) reduces the
    underlying square to `A`'s own `PullbacksTransferCovers`, giving the OPPOSITE leg's underlying
    `c.π₂.g` an `A`-cover; the remaining step — promoting that back to an `Â`-cover — is exactly the
    direction `pairForget` does NOT reflect (`Â`-monos are tested against fewer arrows), i.e. the
    slice-equivalence verification.  This is the single sharply-isolated §1.547 obstruction; every
    finite-limit and forward-cover ingredient feeding the pre-regular structure is Sorry-free.

    R11i.  NOTE — this is NO LONGER the same gap as `pairDense_pb_canonical_dense`, which is now
    CLOSED (Sorry-free, axiom-clean): the DENSE-map pullback absorbs its cross-collisions via the
    explicit `apexHom/apexInv` iso.  That absorption is specific to a dense leg (`x.g = e ≫ fst`), so
    the underlying apex collapses onto `Z.A × W'`.  For an ARBITRARY `Â`-cover `f` (NOT dense) the
    cross-constraints between `A.F` and `C.F` need not be absorbable, so even the underlying
    `canonical.π₂.g` is not in general the `A`-pullback opposite leg, and the `A`-level transfer does
    not apply.  This residual is the genuine §1.547 slice-equivalence verification (directed union of
    pre-regular slices), independent of the now-closed dense-pullback density.

    R11j.  The honest A-LEVEL half is now factored out Sorry-free as
    `pairCover_pi2_underlying_of_underlying_pullback`: GIVEN that the underlying cone `pairForgetCone c`
    is an `A`-pullback, `c.π₂.g` is an `A`-cover.  The two reasons this does NOT finish the `Â`-cover:

      (1) `pairForget` does NOT preserve pullbacks.  `canonical_pb_probe` shows `c.π₁.g = eqMap … ≫
          pairProjFst.g`, i.e. the `Â`-pullback apex is the cross-constrained equalizer SUBOBJECT of
          `prod A.A C.A`, strictly smaller than the `A`-pullback of `(f.g, g.g)`.  So the hypothesis
          `hpbA` of the helper fails for an arbitrary `Â`-cover; it holds only when the cross-constraints
          collapse (the dense case, already handled separately).

      (2) `pairForget` does NOT reflect monos/isos (faithful, not full).  Even if (1) were waived and
          `c.π₂.g` were an `A`-cover, promoting `Cover c.π₂` in `Â` requires: for an `Â`-mono `n : D⟶C`
          with `n.g` an `A`-iso, build the `Â`-inverse — a `PairHom C⟶D` underlying `n.g⁻¹`.  Its
          `compat` obligation runs `D.F → C.F` (each `p ∈ D.F` needs a matching `q ∈ C.F` with `n.g⁻¹ ≫
          p.2 = q.2`), whereas `n.compat` only supplies `C.F → D.F` and `n`'s `Â`-monicity gives mere
          left-cancellation against `Â`-maps — neither yields the reverse factor correspondence.  So the
          inverse is not a `PairHom` in general; reflection genuinely fails.

    R14.  The cover-REFLECTION mechanism for (2) is now factored out Sorry-free as
    `pairCover_of_underlying_cover_targets`: GIVEN (i) `m.g` an `A`-cover, (ii) every test `Â`-mono has
    `A`-mono underlying, and (iii) every test `Â`-mono's domain targets `⊆` codomain targets, `m` is an
    `Â`-cover.  Its iso-reflection core is `pairForget_reflects_iso_of_targets_subset` (`n.g` `A`-iso +
    `K° ⊆ C°` ⟹ `n` `Â`-iso, the inverse `compat` built directly from `n.compat` + `K.distinct`), and
    the fullness of the slice bridge `pairHomOfSlice` (a slice `OverHom` over `∏Y°` lifts to a
    `PairHom`) is the structural reason (ii)/(iii) are exactly what a SINGLE pre-regular slice supplies.
    What `pairPullbacksTransferCovers` cannot do with these is DISCHARGE (i)/(ii)/(iii) for the cospan's
    `c.π₂`: (i) needs `hpbA` (obstruction (1)); (ii)/(iii) fail for a free external test mono `n : K↪C`
    whose `K°` is unbounded by the finite square — the test mono lands in SOME slice `A*|U`, but no
    single `U` bounds all of them.  That unbounded quantifier over external test objects is precisely
    why Freyd's directed UNION `⋃_U (A*|U)` (not one slice) is required.

    Closing this needs the §1.547 slice equivalence `Â ≃ ⋃ (A*|U)` (pre-regular slices) — infrastructure
    NOT in this file.  The relational `x°x = 1` route (S1_56 `regular_of_compose_assoc`) is also
    unavailable: `Â` has no `HasImages` instance and no allegory/reciprocation calculus.  ONE `Sorry`,
    true statement, sharply documented; every constructive ingredient (R14 reflection machinery
    included) is committed Sorry-free. -/
-- DEAD PairObj route (§1.547 alternative, superseded by the cofinal route).  `pairPullbacksTransferCovers`
-- carried a genuine `Sorry` (the slice-equivalence cover transfer); it and the `pairPreRegular` instance
-- it fed are UNREACHABLE from `capData_exists` (which uses `uniformStep`/`cofinalProjSystem`).  Commented
-- out so the build is fully Sorry-free; reinstate if the PairObj pre-regular route is ever needed.
/-
theorem pairPullbacksTransferCovers [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] :
    ∀ {A B C : PairObj 𝒞} {f : A ⟶ B} {g : C ⟶ B}
      (c : @Cone (PairObj 𝒞) _ _ _ _ f g), c.IsPullback →
      @Cover (PairObj 𝒞) _ _ _ f → @Cover (PairObj 𝒞) _ _ _ c.π₂ := by
  Sorry  -- (commented-out dead decl)

instance pairPreRegular [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] :
    PreRegularCategory (PairObj 𝒞) where
  pullbacks_transfer_covers c hpb hf := pairPullbacksTransferCovers c hpb hf
-/

/-! ### §1.547  `PairDense` as a `DenseClass (PairObj 𝒞)` — the class the rational category inverts

  With `Â`'s pullbacks in hand we package the §1.547 dense morphisms into the `DenseClass` record
  the §1.48 rational category consumes: `mem x := Nonempty (PairDense x)`.  Closure under isos
  (`pairDense_of_isIso`) and composition (`pairDense_comp`) are Sorry-free (R3).  Pullback-closure
  (§1.48(iii)) is the dense morphism's product-projection form being stable under base change: the
  `Â`-pullback of `x : X→Y` (with `X.A ≅ Y.A × W`, `x.g = fst`) along any `g : Z→Y` is again a
  projection `Z.A × W → Z.A` onto the SAME well-supported `W`, hence dense.  Its proof descends to
  the underlying product-pullback in `A`; it is stated here with that exact obstruction and is the
  one remaining dense-class field (the rest Sorry-free). -/

/-- **§1.547 — the FIRST LEG of the canonical `Â`-pullback of `(g, x)` is DENSE**, for `x` dense.
    This is the irreducible §1.547 content isolated out of `pairDense_pb_witness`.

    The canonical `Â`-pullback apex is the wide-equalizer subobject
    `E ↪ pairProdD Z X ↪ Z.A × X.A` cutting BOTH the square-equalizer `eq(fst≫g.g, snd≫x.g)` AND the
    product's cross-constraints `{(fst≫f, snd≫f') | f∈Z.F, f'∈X.F, f° = f'°}`.  For `c.π₁` to be
    DENSE we need `E ≅ Z.A × dx.W` with `c.π₁.g` = the projection `fst` — i.e. the surviving factors
    of `c.π₁` (the X-factors that are NOT pulled back from `Z`) must be exactly the `dx.W`-half of the
    density iso `X.A ≅ Y.A × dx.W`.  Under density the Y-DERIVED X-factors (targets in `Y.F°`) coincide
    on `E` with the corresponding Z-factors (both equal `·≫g.g≫f_Y` by the pullback square), so they do
    NOT survive; the survivors are precisely the `dx.W`-component.  Hence `E ≅ Z.A × dx.W`.

    RESOLVED (R11i).  The collisions are ABSORBABLE, not an obstruction.  A colliding survivor target
    `T` (some `f∈Z.F` targets it) is REDUNDANT on `E`: the cross-constraint `pairProdW_cross` pins that
    `X`-coordinate to the `Z`-factor `fst≫f`, so the apex collapses to `prod Z.A W'` with
    `W' = ∏(dx.surv.filter (!collides Z))` (the NON-collided survivors).  This is realised CONSTRUCTIVELY
    as an explicit iso `apexHom/apexInv` (`apex.A ≅ Z.A × W'`, round-trips `apexHom_apexInv`/
    `apexInv_apexHom`), whose forward map projects (`apexHom_fst : apexHom ≫ fst = c.π₁.g`) and whose
    `factorSplit` routes every apex factor: Z-half ⇒ Y-derived; X-half ⇒ `dx.factorSplit` with
    `apex_cross` absorbing collided survivors and `partHom_snd_proj` keeping non-collided ones.  Hence
    `c.π₁` is dense (`pairDense_pb_canonical_dense`), SORRY-FREE and axiom-clean.

    The `A`-level core (`projBaseChangeCone_isPullback`) and the absorption are both constructive; the
    earlier worry that distinctness forces an unprovable cross goal was wrong — `PairObj.distinct`
    together with `pairProdW_cross` exactly supplies the needed coincidence. -/
theorem canonical_pb_probe [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]
    {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) :
    ((pairHasPullbacks.has g x).cone.π₁).g
      = eqMap ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g
        ≫ (pairProjFst Z X).g := by
  rfl

/-! ### §1.543 R11g — the ABSORPTION ISO `apex ≅ Z.A × W'`

  The canonical `Â`-pullback apex of the cospan `(g, x)` (for dense `x`) is the wide-equalizer
  `apex = eqObj (w≫fst≫g.g) (w≫snd≫x.g)` over `D = pairProdD Z X` (`w = pairProdW Z X`).  By
  `pairDensePbBaseCone_isPullback` the underlying `A`-pullback of the SQUARE `(g.g, x.g)` is the
  projection `prod Z.A dx.W → Z.A`.  The CROSS-constraints of `D` (`pairProdW_cross`) additionally
  pin, for each COLLIDING survivor `T ∈ dx.surv` (`∃ f ∈ Z.F, f.1 = T`), that survivor-coordinate of
  `dx.W` to a function of `Z.A`.  So the collided block of `dx.W` is redundant and the apex collapses
  to `prod Z.A W'`, `W' = listProd (dx.surv.filter (!collides))`.

  We build the iso as explicit data (hom/inv/round-trips, repo style); the deliverable is the iso
  with `apexIso.hom ≫ fst = π₁.g`. -/

section ApexIso
variable [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]

/-- The collision predicate: `T` collides if some factor of `Z` targets `T`. -/
def collides (Z : PairObj 𝒞) (T : 𝒞) : Bool := decide (∃ f ∈ Z.F, f.1 = T)

/-- The apex carrier: the underlying object of the canonical `Â`-pullback cone of `(g, x)`. -/
abbrev apexCarrier {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) : 𝒞 :=
  (pairHasPullbacks.has g x).cone.pt.A

/-- The first apex leg `apex → Z.A` (underlying the `Â`-pullback `π₁`). -/
def apexL1 {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) : apexCarrier x g ⟶ Z.A :=
  ((pairHasPullbacks.has g x).cone.π₁).g

/-- The second apex leg `apex → X.A` (underlying the `Â`-pullback `π₂`). -/
def apexL2 {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) : apexCarrier x g ⟶ X.A :=
  ((pairHasPullbacks.has g x).cone.π₂).g

/-- The defining square of the apex: `apexL1 ≫ g.g = apexL2 ≫ x.g` (underlying `cone.w`). -/
theorem apex_square {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) :
    apexL1 x g ≫ g.g = apexL2 x g ≫ x.g := by
  have h := congrArg PairHom.g (pairHasPullbacks.has g x).cone.w
  simpa [PairHom.comp, apexL1, apexL2] using h

/-- The `hom` direction of the absorption iso: `apex → Z.A × W'`.  Both components are PROJECTIONS
    out of the apex (no reconstruction): the `Z.A`-part is the first leg `apexL1`; the `W'`-part
    sends `apexL2 : apex → X.A` through the density iso `dx.e` to `dx.W`, then `dx.wf` to
    `listProd dx.surv`, then the partition's `snd` to the non-colliding block `W'`. -/
def apexHom {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    apexCarrier x g ⟶ prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T))) :=
  pair (apexL1 x g)
       (apexL2 x g ≫ dx.e ≫ snd ≫ dx.wf
          ≫ listProdPartitionHom (fun T => collides Z T) dx.surv ≫ snd)

theorem apexHom_fst {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    apexHom x g dx ≫ fst = ((pairHasPullbacks.has g x).cone.π₁).g := by
  unfold apexHom; rw [fst_pair]; rfl

/-- Constructive search over a factor list `fs` for one of target `T`, returning its underlying
    arrow `Z.A → T` together with a witness that it is a `Z`-factor (membership in the ORIGINAL
    `Z.F`, threaded through `hsub`). -/
def findArrow (Z : PairObj 𝒞) (T : 𝒞) :
    ∀ (fs : List (Σ S : 𝒞, Z.A ⟶ S)), (∀ f ∈ fs, f ∈ Z.F) →
      (∃ f ∈ fs, f.1 = T) →
      {a : Z.A ⟶ T // ∃ f ∈ Z.F, ∃ h : f.1 = T, a = h ▸ f.2}
  | [], _, hex => absurd hex (by simp)
  | f :: fs, hsub, hex => by
      by_cases hfT : f.1 = T
      · exact ⟨hfT ▸ f.2, f, hsub f (List.mem_cons_self), hfT, rfl⟩
      · refine findArrow Z T fs (fun f' hf' => hsub f' (List.mem_cons_of_mem _ hf')) ?_
        rcases hex with ⟨f', hf', hf'T⟩
        rcases List.mem_cons.1 hf' with rfl | hf'tail
        · exact absurd hf'T hfT
        · exact ⟨f', hf'tail, hf'T⟩

/-- The chosen Z-factor's underlying arrow `Z.A → T` for a colliding `T` (constructive search over
    `Z.F`).  Carries the witness `∃ f ∈ Z.F, ∃ h:f.1=T, a = h ▸ f.2`. -/
def pickArrow (Z : PairObj 𝒞) (T : 𝒞) (h : collides Z T = true) :
    {a : Z.A ⟶ T // ∃ f ∈ Z.F, ∃ h : f.1 = T, a = h ▸ f.2} :=
  findArrow Z T Z.F (fun _ hf => hf) (of_decide_eq_true h)

/-- **Reconstruct the colliding block** `Z.A → listProd l` for a list `l` all of whose members
    collide: each coordinate is the chosen Z-factor to that target. -/
def collReconstruct (Z : PairObj 𝒞) :
    ∀ (l : List 𝒞), (∀ T ∈ l, collides Z T = true) → (Z.A ⟶ listProd l)
  | [], _ => term Z.A
  | T :: l, h =>
      pair (pickArrow Z T (h T (List.mem_cons_self))).1
           (collReconstruct Z l (fun S hS => h S (List.mem_cons_of_mem _ hS)))

/-- **Projection of `collReconstruct`**: the `k`-th coordinate of the reconstructed colliding block
    is the chosen Z-factor to that coordinate's target.  Structural induction on `l`/`k`. -/
theorem collReconstruct_proj (Z : PairObj 𝒞) :
    ∀ (l : List 𝒞) (h : ∀ T ∈ l, collides Z T = true) (k : Fin l.length),
      collReconstruct Z l h ≫ listProdProj l k
        = (pickArrow Z (l.get k) (h (l.get k) (l.get_mem k))).1
  | [], _, k => k.elim0
  | T :: l, h, ⟨0, hk0⟩ => by
      show pair _ _ ≫ (fst : prod T (listProd l) ⟶ T) = _
      rw [fst_pair]; rfl
  | T :: l, h, ⟨n + 1, hk⟩ => by
      show pair _ (collReconstruct Z l _) ≫ ((snd : prod T (listProd l) ⟶ listProd l)
            ≫ listProdProj l ⟨n, Nat.lt_of_succ_lt_succ hk⟩) = _
      rw [← Cat.assoc, snd_pair, collReconstruct_proj Z l _ ⟨n, Nat.lt_of_succ_lt_succ hk⟩]; rfl

/-- All members of `dx.surv.filter (collides Z)` collide (`List.mem_filter`). -/
theorem collFilter_all {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (dx : PairDense x) :
    ∀ T ∈ dx.surv.filter (fun T => collides Z T), collides Z T = true :=
  fun _ hT => (List.mem_filter.1 hT).2

/-- **Reconstruct the full survivor product** `prod Z.A W' → listProd dx.surv`: the colliding block
    from `fst ≫ collReconstruct`, the non-colliding block `W'` from `snd`; re-assembled by the
    partition inverse. -/
def survRecon {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (dx : PairDense x) :
    prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T))) ⟶ listProd dx.surv :=
  pair (fst ≫ collReconstruct Z (dx.surv.filter (fun T => collides Z T)) (collFilter_all x dx))
       snd
  ≫ listProdPartitionInv (fun T => collides Z T) dx.surv

/-- `pickArrow`'s chosen arrow is HEq-stable across equal targets (proof-irrelevant in its witness). -/
theorem pickArrow_heq (Z : PairObj 𝒞) {T T' : 𝒞} (h : T = T')
    (hc : collides Z T = true) (hc' : collides Z T' = true) :
    HEq (pickArrow Z T hc).1 (pickArrow Z T' hc').1 := by
  cases h; rfl

/-- **A colliding survivor coordinate of `survRecon` is `fst ≫ (chosen Z-factor)`.**  For a survivor
    target `dx.surv.get k` that COLLIDES, the partition inverse routes it to the LEFT (colliding)
    block (`listProdPartitionInv_projL`), whose entries are `collReconstruct`'s chosen Z-factors
    (`collReconstruct_proj`); the `filterIdx`/get bookkeeping cancels. -/
theorem survRecon_proj_coll {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (dx : PairDense x)
    (k : Fin dx.surv.length) (hk : collides Z (dx.surv.get k) = true) :
    survRecon x dx ≫ listProdProj dx.surv k
      = fst ≫ (pickArrow Z (dx.surv.get k) hk).1 := by
  have hget : ((dx.surv.filter (fun T => collides Z T)).get
      (filterIdx (fun T => collides Z T) dx.surv k hk)) = dx.surv.get k :=
    filterIdx_get (fun T => collides Z T) dx.surv k hk
  unfold survRecon
  rw [Cat.assoc, listProdPartitionInv_projL (fun T => collides Z T) dx.surv k hk hget,
    ← Cat.assoc, fst_pair, Cat.assoc]
  -- goal: `fst ≫ collReconstruct .. ≫ (hget ▸ listProdProj (filter) j) = fst ≫ (pickArrow Z (surv.get k) hk).1`
  refine congrArg (fst ≫ ·) ?_
  -- the inner: transport `collReconstruct .. ≫ listProdProj (filter) j = pickArrow ((filter).get j)`
  -- across `hget`, landing on `pickArrow (surv.get k)` (proof-irrelevant in the collides witness).
  apply eq_of_heq
  refine (comp_right_heq hget (collReconstruct Z (dx.surv.filter (fun T => collides Z T))
      (collFilter_all x dx)) _ _ (eqRec_heq hget
    (listProdProj (dx.surv.filter (fun T => collides Z T))
      (filterIdx (fun T => collides Z T) dx.surv k hk))).symm).symm.trans ?_
  refine (heq_of_eq (collReconstruct_proj Z (dx.surv.filter (fun T => collides Z T))
    (collFilter_all x dx) (filterIdx (fun T => collides Z T) dx.surv k hk))).trans ?_
  exact pickArrow_heq Z hget _ _

/-- **A non-colliding survivor coordinate of `survRecon` is `snd ≫ (filtered W'-projection)`.**  The
    partition inverse routes a non-colliding coordinate to the RIGHT (`W'`) block, whose entries are
    `snd` verbatim (`listProdPartitionInv_projR`). -/
theorem survRecon_proj_noncoll {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (dx : PairDense x)
    (k : Fin dx.surv.length) (hk : (fun T => !collides Z T) (dx.surv.get k) = true)
    (hget : (dx.surv.filter (fun T => !collides Z T)).get
        (filterIdx (fun T => !collides Z T) dx.surv k hk) = dx.surv.get k) :
    survRecon x dx ≫ listProdProj dx.surv k
      = snd ≫ (hget ▸ listProdProj (dx.surv.filter (fun T => !collides Z T))
          (filterIdx (fun T => !collides Z T) dx.surv k hk)) := by
  unfold survRecon
  rw [Cat.assoc, listProdPartitionInv_projR (fun T => collides Z T) dx.surv k hk hget,
    ← Cat.assoc, snd_pair]

/-- **Partition-hom recovers a `!p`-coordinate from its `W'` block.**  `partHom ≫ snd ≫ (filtered
    W'-projection at `filterIdx`) = proj_k` for a `!p`-true coordinate `k`.  By the round-trip
    `partHom ≫ partInv = id` and `listProdPartitionInv_projR`. -/
theorem partHom_snd_proj (p : 𝒞 → Bool) (l : List 𝒞) (k : Fin l.length)
    (hk : (fun a => !p a) (l.get k) = true)
    (hget : (l.filter (fun a => !p a)).get (filterIdx (fun a => !p a) l k hk) = l.get k) :
    listProdPartitionHom p l ≫ (snd : prod (listProd (l.filter p))
        (listProd (l.filter (fun a => !p a))) ⟶ listProd (l.filter (fun a => !p a)))
      ≫ (hget ▸ listProdProj (l.filter (fun a => !p a)) (filterIdx (fun a => !p a) l k hk))
      = listProdProj l k := by
  rw [← listProdPartitionInv_projR p l k hk hget, ← Cat.assoc,
    listProdPartition_hom_inv, Cat.id_comp]

/-- The reconstructed `dx.W`-coordinate: `survRecon ≫ dx.wg`. -/
def wRecon {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (_ : Z ⟶ Y) (dx : PairDense x) :
    prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T))) ⟶ dx.W :=
  survRecon x dx ≫ dx.wg

/-- The reconstructed map into the binary product `Z.A × X.A`: `Z.A`-coordinate is `fst`; the
    `X.A`-coordinate is `pair (fst ≫ g.g) wRecon ≫ dx.einv` (the density iso `prod Y.A dx.W ≅ X.A`
    with the `Y.A`-part forced by the square to `fst ≫ g.g`). -/
def mProd {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T))) ⟶ prod Z.A X.A :=
  pair fst (pair (fst ≫ g.g) (wRecon x g dx) ≫ dx.einv)

/-- **Partition handle.**  `survRecon ≫ partitionHom = pair (fst ≫ collReconstruct) snd`: the
    partition splits the reconstructed product back into its colliding block (`fst ≫ collReconstruct`)
    and its non-colliding block `W'` (`snd`).  By `listProdPartition_inv_hom`. -/
theorem survRecon_hom {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (dx : PairDense x) :
    survRecon x dx ≫ listProdPartitionHom (fun T => collides Z T) dx.surv
      = pair (fst ≫ collReconstruct Z (dx.surv.filter (fun T => collides Z T)) (collFilter_all x dx))
             snd := by
  unfold survRecon
  rw [Cat.assoc, listProdPartition_inv_hom, Cat.comp_id]

/-- `survRecon ≫ partitionHom ≫ snd = snd` — the non-colliding block is recovered verbatim. -/
theorem survRecon_hom_snd {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (dx : PairDense x) :
    survRecon x dx ≫ listProdPartitionHom (fun T => collides Z T) dx.surv ≫ snd
      = snd := by
  rw [← Cat.assoc, survRecon_hom, snd_pair]

/-- `dx.einv ≫ x.g = fst` (the density iso carries `x.g` to `fst`, inverse side). -/
theorem einv_xg {X Y : PairObj 𝒞} (x : X ⟶ Y) (dx : PairDense x) :
    dx.einv ≫ x.g = (fst : prod Y.A dx.W ⟶ Y.A) := by
  rw [← dx.proj, ← Cat.assoc, dx.e_iso₂, Cat.id_comp]

/-- `dx.einv ≫ dx.e ≫ snd = snd` (used to peel a survivor factor through the density iso). -/
theorem einv_e_snd {X Y : PairObj 𝒞} (x : X ⟶ Y) (dx : PairDense x) :
    dx.einv ≫ dx.e ≫ (snd : prod Y.A dx.W ⟶ dx.W) = snd := by
  rw [← Cat.assoc, dx.e_iso₂, Cat.id_comp]

/-- `wRecon ≫ dx.wf = survRecon` (since `dx.wg ≫ dx.wf = id`). -/
theorem wRecon_wf {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    wRecon x g dx ≫ dx.wf = survRecon x dx := by
  unfold wRecon; rw [Cat.assoc, dx.wgf, Cat.comp_id]

/-- **Step 1 — `mProd` equalizes every cross constraint of `Z × X`.**  A cross constraint is
    `(fst≫f.2, snd≫(hff▸f'.2))` for `f ∈ Z.F`, `f' ∈ X.F` of a common target.  `mProd ≫ fst = fst`
    gives the LHS `= fst≫f.2`.  For the RHS, `f'` is by `dx.factorSplit` either Y-DERIVED (then
    `dx.einv` carries it to `fst≫(Y-factor)`, and `g.compat`+`Z.distinct` match it to `f`) or a
    SURVIVOR coordinate (then `dx.einv≫dx.e≫snd = snd`, `wRecon≫wf = survRecon`, and the colliding
    survivor projection `survRecon_proj_coll` recovers `fst≫(chosen Z-factor) = fst≫f.2` by
    `Z.distinct`). -/
theorem mProd_equalizes {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    ∀ p ∈ crossConstraints Z X, mProd x g dx ≫ p.2.1 = mProd x g dx ≫ p.2.2 := by
  intro p hp
  rcases List.mem_flatMap.1 hp with ⟨f, hf, hpf⟩
  rcases List.mem_filterMap.1 hpf with ⟨f', hf', hpe⟩
  by_cases hff : f.1 = f'.1
  · rw [dif_pos hff] at hpe
    -- `some ⟨f.1, (fst≫f.2, snd≫(hff▸f'.2))⟩ = some p`
    cases hpe
    show mProd x g dx ≫ fst ≫ f.2 = mProd x g dx ≫ snd ≫ (hff ▸ f'.2)
    -- LHS `mProd ≫ fst ≫ f.2 = fst ≫ f.2`
    have hL : mProd x g dx ≫ fst ≫ f.2 = fst ≫ f.2 := by
      rw [← Cat.assoc]; unfold mProd; rw [fst_pair]
    -- RHS `mProd ≫ snd ≫ (hff ▸ f'.2) = pair (fst≫g.g) wRecon ≫ dx.einv ≫ (hff ▸ f'.2)`
    have hR0 : mProd x g dx ≫ snd ≫ (hff ▸ f'.2)
        = pair (fst ≫ g.g) (wRecon x g dx) ≫ dx.einv ≫ (hff ▸ f'.2) := by
      rw [← Cat.assoc]; unfold mProd; rw [snd_pair, Cat.assoc]
    rw [hL, hR0]
    -- now split `f'` by density
    rcases dx.factorSplit f' hf' with ⟨gY, hgY, hgt, hge⟩ | ⟨k, hkt, hke⟩
    · -- Y-DERIVED: `f'.2 = x.g ≫ (hgt ▸ gY.2)`.  Match `f` (in `Z.F`) to `gY` via `g.compat`+`Z.distinct`.
      obtain ⟨q, hq, hqt, hqe⟩ := g.compat gY hgY  -- q ∈ Z.F, q.1 = gY.1, g.g ≫ gY.2 = hqt ▸ q.2
      -- normalise away transports by casing on the target equalities
      obtain ⟨ft, fm⟩ := f; obtain ⟨f't, f'm⟩ := f'; obtain ⟨gYt, gYm⟩ := gY; obtain ⟨qt, qm⟩ := q
      simp only at hff hgt hqt hge hqe ⊢
      cases hff; cases hgt; cases hqt
      simp only at hge hqe ⊢
      have hdist : fm = qm := Z.distinct ⟨ft, fm⟩ hf ⟨ft, qm⟩ hq rfl
      -- goal: `fst ≫ fm = pair (fst≫g.g) wRecon ≫ dx.einv ≫ f'm`, with f'm = x.g ≫ gYm, fm = qm,
      -- g.g ≫ gYm = qm
      rw [hge, ← Cat.assoc dx.einv x.g gYm, einv_xg x dx, ← Cat.assoc, fst_pair,
        Cat.assoc, hqe, hdist]
    · -- SURVIVOR: `f'.2 = dx.e ≫ snd ≫ dx.wf ≫ (hkt ▸ listProdProj dx.surv k)`.
      -- target chain: f.1 = f'.1 = surv.get k; `f ∈ Z.F` ⇒ that coordinate COLLIDES.
      have hftk : f.1 = dx.surv.get k := hff.trans hkt
      have hcoll : collides Z (dx.surv.get k) = true :=
        decide_eq_true (⟨f, hf, hftk⟩ : ∃ f ∈ Z.F, f.1 = dx.surv.get k)
      -- normalise transports: case the target equalities
      obtain ⟨ft, fm⟩ := f; obtain ⟨f't, f'm⟩ := f'
      simp only at hff hkt hke hftk ⊢
      cases hff; cases hkt
      simp only at hke ⊢
      -- now `f'm = dx.e ≫ snd ≫ dx.wf ≫ listProdProj dx.surv k`, `a = w.2`-transported.
      -- `dx.einv ≫ f'm = snd ≫ dx.wf ≫ proj_k` (peel the density iso with `einv_e_snd`)
      have heinv : dx.einv ≫ f'm = snd ≫ dx.wf ≫ listProdProj dx.surv k := by
        rw [hke]
        calc dx.einv ≫ dx.e ≫ snd ≫ dx.wf ≫ listProdProj dx.surv k
            = (dx.einv ≫ dx.e ≫ snd) ≫ dx.wf ≫ listProdProj dx.surv k := by
              rw [Cat.assoc, Cat.assoc]
          _ = snd ≫ dx.wf ≫ listProdProj dx.surv k := by rw [einv_e_snd x dx]
      -- RHS reduction: `pair _ wRecon ≫ (dx.einv ≫ f'm) = pair _ wRecon ≫ snd ≫ wf ≫ proj_k`
      rw [heinv, ← Cat.assoc (pair (fst ≫ g.g) (wRecon x g dx)) snd _, snd_pair,
        ← Cat.assoc (wRecon x g dx) dx.wf _, wRecon_wf, survRecon_proj_coll x dx k hcoll]
      -- goal: `fst ≫ fm = fst ≫ (pickArrow ..).1`; reduce to `fm = (pickArrow ..).1`.
      congr 1
      -- the chosen Z-factor to `surv.get k` equals `fm` (both Z-factors of target `surv.get k`).
      obtain ⟨w, hw, hwt, hwe⟩ := (pickArrow Z (dx.surv.get k) hcoll).2
      obtain ⟨wt, wm⟩ := w
      simp only at hwt hwe ⊢
      cases hwt
      simp only at hwe ⊢
      rw [hwe]
      exact (Z.distinct ⟨dx.surv.get k, wm⟩ hw ⟨dx.surv.get k, fm⟩ hf rfl).symm
  · rw [dif_neg hff] at hpe; exact absurd hpe (by simp)

/-- **Step 2 — `mProd` satisfies the apex square.**  `mProd ≫ fst ≫ g.g = mProd ≫ snd ≫ x.g`:
    `mProd ≫ fst = fst` and `mProd ≫ snd ≫ x.g = pair (fst≫g.g) wRecon ≫ dx.einv ≫ x.g
    = pair (fst≫g.g) wRecon ≫ fst = fst ≫ g.g` (`einv_xg`). -/
theorem mProd_square {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    mProd x g dx ≫ (fst : prod Z.A X.A ⟶ Z.A) ≫ g.g
      = mProd x g dx ≫ (snd : prod Z.A X.A ⟶ X.A) ≫ x.g := by
  unfold mProd
  rw [← Cat.assoc, fst_pair, ← Cat.assoc, snd_pair, Cat.assoc, einv_xg x dx, fst_pair]

/-- `mProd` factored through the product subobject `pairProdW Z X` (step 1: it equalizes every
    cross constraint).  `mProdW ≫ pairProdW Z X = mProd`. -/
def mProdW {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T))) ⟶ pairProdD Z X :=
  (wideEq (prod Z.A X.A) (crossConstraints Z X)).lift (mProd x g dx) (mProd_equalizes x g dx)

theorem mProdW_fac {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    mProdW x g dx ≫ pairProdW Z X = mProd x g dx :=
  (wideEq (prod Z.A X.A) (crossConstraints Z X)).fac (mProd x g dx) (mProd_equalizes x g dx)

/-- **Step 3 — the absorption iso's `inv : prod Z.A W' → apex.A`.**  `mProdW` satisfies the apex
    equalizer condition `mProdW ≫ (w≫fst≫g.g) = mProdW ≫ (w≫snd≫x.g)` (step 2 `mProd_square`
    pushed through `mProdW_fac`), so it lifts through the apex equalizer `eqMap`. -/
def apexInv {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T))) ⟶
      (pairHasPullbacks.has g x).cone.pt.A :=
  eqLift ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g (mProdW x g dx) (by
    -- `mProdW ≫ (w≫fst≫g.g) = mProdW ≫ (w≫snd≫x.g)`: reassociate to `(mProdW≫w)≫fst≫g.g`,
    -- use `mProdW_fac` then `mProd_square`.
    show mProdW x g dx ≫ (pairProdW Z X ≫ fst) ≫ g.g
       = mProdW x g dx ≫ (pairProdW Z X ≫ snd) ≫ x.g
    rw [Cat.assoc, Cat.assoc, ← Cat.assoc (mProdW x g dx) (pairProdW Z X) (fst ≫ g.g),
      ← Cat.assoc (mProdW x g dx) (pairProdW Z X) (snd ≫ x.g), mProdW_fac, mProd_square])

theorem apexInv_fac {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    apexInv x g dx ≫ eqMap ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g
      = mProdW x g dx :=
  eqLift_fac ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g (mProdW x g dx) _

/-- The apex's two legs are the equalizer map post-composed with the two product projections (def
    of the §1.432 pullback-from-equalizer).  `apexL1` is `canonical_pb_probe`; `apexL2` analogous. -/
theorem apexL1_eq {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) :
    apexL1 x g = eqMap ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g
      ≫ pairProdW Z X ≫ fst := rfl

theorem apexL2_eq {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) :
    apexL2 x g = eqMap ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g
      ≫ pairProdW Z X ≫ snd := rfl

/-- `apexInv ≫ apexL1 = fst` (the `Z.A`-leg is the projection).  `apexL1` factors through the apex
    equalizer; `apexInv_fac` + `mProdW_fac` collapse it to `mProd ≫ fst = fst`. -/
theorem apexInv_apexL1 {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    apexInv x g dx ≫ apexL1 x g = fst := by
  rw [apexL1_eq, ← Cat.assoc, ← Cat.assoc, apexInv_fac, mProdW_fac]
  show mProd x g dx ≫ fst = fst
  unfold mProd; rw [fst_pair]

/-- `apexInv ≫ apexL2 = pair (fst≫g.g) wRecon ≫ dx.einv` (the `X.A`-leg is `mProd`'s `snd`). -/
theorem apexInv_apexL2 {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    apexInv x g dx ≫ apexL2 x g = pair (fst ≫ g.g) (wRecon x g dx) ≫ dx.einv := by
  rw [apexL2_eq, ← Cat.assoc, ← Cat.assoc, apexInv_fac, mProdW_fac]
  show mProd x g dx ≫ snd = _
  unfold mProd; rw [snd_pair]

/-- **Step 4a — `apexInv ≫ apexHom = id`.**  Check on both projections of `prod Z.A W'`:
    `≫ fst` is `apexInv ≫ apexL1 = fst`; `≫ snd` is `apexInv ≫ apexL2 ≫ (density+partition snd)`,
    which peels `dx.einv≫dx.e` (`e_iso₂`), `wRecon≫wf = survRecon` (`wRecon_wf`), and the partition
    handle `survRecon_hom_snd` back to `snd`. -/
theorem apexInv_apexHom {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    apexInv x g dx ≫ apexHom x g dx = Cat.id _ := by
  apply fst_snd_jointly_monic
  · rw [Cat.assoc, apexHom_fst]
    show apexInv x g dx ≫ apexL1 x g = Cat.id _ ≫ fst
    rw [apexInv_apexL1, Cat.id_comp]
  · rw [Cat.assoc]
    have hsnd : apexHom x g dx ≫ snd = apexL2 x g ≫ dx.e ≫ snd ≫ dx.wf
          ≫ listProdPartitionHom (fun T => collides Z T) dx.surv ≫ snd := by
      unfold apexHom; rw [snd_pair]
    rw [hsnd, Cat.id_comp, ← Cat.assoc (apexInv x g dx) (apexL2 x g), apexInv_apexL2]
    -- `(pair (fst≫g.g) wRecon ≫ dx.einv) ≫ dx.e ≫ snd ≫ wf ≫ partHom ≫ snd`
    rw [Cat.assoc (pair (fst ≫ g.g) (wRecon x g dx)) dx.einv,
      ← Cat.assoc dx.einv dx.e _, dx.e_iso₂, Cat.id_comp,
      ← Cat.assoc (pair (fst ≫ g.g) (wRecon x g dx)) snd _, snd_pair,
      ← Cat.assoc (wRecon x g dx) dx.wf _, wRecon_wf, survRecon_hom_snd]

/-- **The apex's CROSS-CONSTRAINT.**  For a `Z`-factor `w` and an `X`-factor `f'` of a common
    target, the apex's two legs agree on them: `apexL1 ≫ w.2 = apexL2 ≫ (hww ▸ f'.2)`.  This is
    `pairProdW_cross` (the product subobject equalizes the cross constraint) pre-composed with the
    apex equalizer `eqMap`, using `apexL1 = eqMap≫w≫fst`, `apexL2 = eqMap≫w≫snd`. -/
theorem apex_cross {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y)
    {w : Σ T : 𝒞, Z.A ⟶ T} (hw : w ∈ Z.F) {f' : Σ T : 𝒞, X.A ⟶ T} (hf' : f' ∈ X.F)
    (hww : w.1 = f'.1) :
    apexL1 x g ≫ w.2 = apexL2 x g ≫ (hww ▸ f'.2) := by
  have hc := pairProdW_cross Z X hw hf' hww
  rw [apexL1_eq, apexL2_eq, Cat.assoc, Cat.assoc, Cat.assoc, Cat.assoc, hc]

/-- The underlying arrow `apex.A → X.A` of the comparison map `b` used in step 4b: pairs the
    square-forced `Y.A`-component `apexL1 ≫ g.g` with the reconstructed `dx.W`-component
    `apexHom ≫ wRecon`, then crosses the density iso `dx.einv`. -/
def bMap_g {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    (pairHasPullbacks.has g x).cone.pt.A ⟶ X.A :=
  pair (apexL1 x g ≫ g.g) (apexHom x g dx ≫ wRecon x g dx) ≫ dx.einv

/-- `bMap_g ≫ x.g = apexL1 ≫ g.g` (the density iso carries `x.g` to `fst`). -/
theorem bMap_g_xg {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    bMap_g x g dx ≫ x.g = apexL1 x g ≫ g.g := by
  unfold bMap_g; rw [Cat.assoc, einv_xg x dx, fst_pair]

/-- `bMap_g ≫ dx.e ≫ snd = apexHom ≫ wRecon` (the `dx.W`-component survives the iso round-trip). -/
theorem bMap_g_e_snd {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    bMap_g x g dx ≫ dx.e ≫ (snd : prod Y.A dx.W ⟶ dx.W) = apexHom x g dx ≫ wRecon x g dx := by
  unfold bMap_g
  rw [Cat.assoc, ← Cat.assoc dx.einv dx.e snd, dx.e_iso₂, Cat.id_comp, snd_pair]

/-- **The comparison map agrees with `apexL2` on every `X`-factor.**  `bMap_g ≫ f'.2 = apexL2 ≫ f'.2`
    for `f' ∈ X.F`.  Split `f'` by `dx.factorSplit`:
    * Y-DERIVED `f'.2 = x.g ≫ gY.2`: both sides become `apexL1 ≫ g.g ≫ gY.2` (via `bMap_g_xg`,
      `apex_square`).
    * SURVIVOR `f'.2 = e ≫ snd ≫ wf ≫ proj_k`: `bMap_g ≫ f'.2 = apexHom ≫ survRecon ≫ proj_k`
      (`bMap_g_e_snd`, `wRecon_wf`).  If `surv.get k` COLLIDES, `survRecon_proj_coll` gives
      `apexL1 ≫ (chosen Z-factor)`, matched to `apexL2 ≫ f'.2` by the cross constraint `apex_cross`
      (here `f'` IS the X-factor at that target).  If NON-COLLIDING, `survRecon_proj_noncoll` +
      `partHom_snd_proj` route through the `W'` block back to `apexL2 ≫ f'.2`. -/
theorem bMap_g_factor {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    ∀ f' ∈ X.F, bMap_g x g dx ≫ f'.2 = apexL2 x g ≫ f'.2 := by
  intro f' hf'
  rcases dx.factorSplit f' hf' with ⟨gY, hgY, hgt, hge⟩ | ⟨k, hkt, hke⟩
  · -- Y-DERIVED
    rw [hge, ← Cat.assoc, ← Cat.assoc, bMap_g_xg, ← apex_square]
  · -- SURVIVOR.  Destructure `f'` and case the target equality to kill the transport.
    obtain ⟨f't, f'm⟩ := f'
    simp only at hkt hke ⊢
    cases hkt
    simp only at hke ⊢
    -- now `f'm : X.A ⟶ dx.surv.get k`, `f'm = dx.e ≫ snd ≫ dx.wf ≫ listProdProj dx.surv k`
    rw [hke]
    -- LHS `bMap_g ≫ (dx.e≫snd≫wf≫proj_k)` = `apexHom ≫ survRecon ≫ proj_k`
    have hLHS : bMap_g x g dx ≫ dx.e ≫ snd ≫ dx.wf ≫ listProdProj dx.surv k
        = apexHom x g dx ≫ survRecon x dx ≫ listProdProj dx.surv k := by
      calc bMap_g x g dx ≫ dx.e ≫ snd ≫ dx.wf ≫ listProdProj dx.surv k
          = (bMap_g x g dx ≫ dx.e ≫ snd) ≫ dx.wf ≫ listProdProj dx.surv k := by
            rw [Cat.assoc, Cat.assoc]
        _ = (apexHom x g dx ≫ wRecon x g dx) ≫ dx.wf ≫ listProdProj dx.surv k := by
            rw [bMap_g_e_snd]
        _ = apexHom x g dx ≫ (wRecon x g dx ≫ dx.wf) ≫ listProdProj dx.surv k := by
            rw [Cat.assoc, Cat.assoc]
        _ = apexHom x g dx ≫ survRecon x dx ≫ listProdProj dx.surv k := by rw [wRecon_wf]
    rw [hLHS]
    by_cases hc : collides Z (dx.surv.get k) = true
    · -- COLLIDING: cross constraint with the chosen Z-factor `w` and `f'm`.
      rw [survRecon_proj_coll x dx k hc, ← Cat.assoc, apexHom_fst]
      -- goal: `apexL1 ≫ (pickArrow Z (surv.get k) hc).1 = apexL2 ≫ dx.e ≫ snd ≫ dx.wf ≫ proj_k`
      obtain ⟨w, hw, hwt, hwe⟩ := (pickArrow Z (dx.surv.get k) hc).2
      -- rewrite goal to `apexL1 ≫ (pickArrow).1 = apexL2 ≫ f'm` and use the cross constraint
      show apexL1 x g ≫ (pickArrow Z (dx.surv.get k) hc).1 = _
      rw [hwe, ← hke]
      -- goal: `apexL1 ≫ (hwt ▸ w.2) = apexL2 ≫ f'm`
      obtain ⟨wt, wm⟩ := w
      simp only at hwt hwe ⊢
      cases hwt
      -- goal: `apexL1 ≫ wm = apexL2 ≫ f'm`; this is `apex_cross` with `w=⟨surv.get k,wm⟩`, `f'=⟨_,f'm⟩`
      exact apex_cross (x := x) (g := g) hw (f' := ⟨dx.surv.get k, f'm⟩) hf' rfl
    · -- NON-COLLIDING: route through the `W'` block (`survRecon_proj_noncoll`, `partHom_snd_proj`).
      have hnc : (fun T => !collides Z T) (dx.surv.get k) = true := by
        simp only [Bool.not_eq_true']; exact Bool.eq_false_iff.2 hc
      have hget : (dx.surv.filter (fun T => !collides Z T)).get
          (filterIdx (fun T => !collides Z T) dx.surv k hnc) = dx.surv.get k :=
        filterIdx_get (fun T => !collides Z T) dx.surv k hnc
      have hsnd_apexHom : apexHom x g dx ≫ snd = apexL2 x g ≫ dx.e ≫ snd ≫ dx.wf
          ≫ listProdPartitionHom (fun T => collides Z T) dx.surv ≫ snd := by
        unfold apexHom; rw [snd_pair]
      rw [survRecon_proj_noncoll x dx k hnc hget, ← Cat.assoc, hsnd_apexHom]
      -- goal: `(apexL2 ≫ dx.e ≫ snd ≫ dx.wf ≫ partHom ≫ snd) ≫ (hget ▸ filtered proj)
      --        = apexL2 ≫ dx.e ≫ snd ≫ dx.wf ≫ proj_k`
      rw [Cat.assoc, Cat.assoc, Cat.assoc, Cat.assoc, Cat.assoc,
        partHom_snd_proj (fun T => collides Z T) dx.surv k hnc hget]

/-- **The comparison `Â`-map `b : apex_obj → X`.**  Underlying `bMap_g`; compatibility from
    `bMap_g_factor` (`bMap_g ≫ f'.2 = apexL2 ≫ f'.2`) plus the canonical pullback leg `cone.π₂`'s
    own compatibility (`apexL2 = cone.π₂.g` hits the apex factor `⟨f'.1, apexL2≫f'.2⟩`). -/
def bMap {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    PairHom (pairHasPullbacks.has g x).cone.pt X where
  g := bMap_g x g dx
  compat p hp := by
    obtain ⟨q, hq, hqt, hqe⟩ := ((pairHasPullbacks.has g x).cone.π₂).compat p hp
    exact ⟨q, hq, hqt, by rw [bMap_g_factor x g dx p hp]; exact hqe⟩

/-- **`apexL2 ≫ dx.e ≫ snd = apexHom ≫ wRecon`** — the `dx.W`-component agreement, via `survPinned`.
    The canonical pullback leg `cone.π₂` and the comparison map `bMap` are both `Â`-maps into `X`, so
    `survPinned` pins them after `dx.e ≫ snd`; `cone.π₂.g = apexL2`, `bMap.g ≫ dx.e ≫ snd =
    apexHom ≫ wRecon` (`bMap_g_e_snd`). -/
theorem apexL2_e_snd {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    apexL2 x g ≫ dx.e ≫ (snd : prod Y.A dx.W ⟶ dx.W) = apexHom x g dx ≫ wRecon x g dx := by
  have hpin := dx.survPinned ((pairHasPullbacks.has g x).cone.π₂) (bMap x g dx)
  -- `cone.π₂.g ≫ e ≫ snd = bMap.g ≫ e ≫ snd`; lhs = `apexL2 ≫ e ≫ snd`, rhs = `apexHom ≫ wRecon`
  rw [show ((pairHasPullbacks.has g x).cone.π₂).g = apexL2 x g from rfl] at hpin
  rw [hpin]
  show bMap_g x g dx ≫ dx.e ≫ snd = _
  exact bMap_g_e_snd x g dx

/-- **Step 4b — `apexHom ≫ apexInv = id`.**  Cancel the two monos `eqMap` (apex inclusion) and
    `pairProdW` (product subobject): suffices `apexHom ≫ mProd = eqMap ≫ pairProdW`.  Both sides are
    `pair apexL1 (·)` on the `Z.A`-leg; the `X.A`-leg reduces (post-composing the density iso `dx.e`)
    to `apex_square` on `fst` and `apexL2_e_snd` on `snd`. -/
theorem apexHom_apexInv {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    apexHom x g dx ≫ apexInv x g dx = Cat.id _ := by
  -- cancel mono `eqMap u v`
  have hmono : Monic (eqMap ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g) :=
    eqMap_monic _ _
  apply hmono
  rw [Cat.assoc, apexInv_fac, Cat.id_comp]
  -- goal: `apexHom ≫ mProdW = eqMap`.  Cancel mono `pairProdW`.
  apply pairProdW_mono Z X
  rw [Cat.assoc, mProdW_fac]
  -- goal: `apexHom ≫ mProd = eqMap ≫ pairProdW`.  Compare on both product projections.
  apply fst_snd_jointly_monic
  · -- `≫ fst`: both `apexL1`
    rw [Cat.assoc, Cat.assoc]
    rw [show pairProdW Z X ≫ fst = (pairProjFst Z X).g from rfl,
      show eqMap ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g ≫ (pairProjFst Z X).g
        = apexL1 x g from rfl]
    unfold mProd; rw [fst_pair, apexHom_fst]; rfl
  · -- `≫ snd`: `apexHom ≫ mProd ≫ snd = apexL2`
    rw [Cat.assoc, Cat.assoc]
    rw [show eqMap ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g
          ≫ pairProdW Z X ≫ snd = apexL2 x g from rfl]
    unfold mProd
    rw [snd_pair]
    -- `apexHom ≫ pair (fst≫g.g) wRecon ≫ dx.einv = apexL2`; post-compose iso `dx.e`
    have hiso : (apexHom x g dx ≫ pair (fst ≫ g.g) (wRecon x g dx) ≫ dx.einv) ≫ dx.e
        = apexL2 x g ≫ dx.e := by
      rw [Cat.assoc, Cat.assoc, dx.e_iso₂, Cat.comp_id]
      apply fst_snd_jointly_monic
      · -- `(apexHom ≫ pair (fst≫g.g) wRecon) ≫ fst = (apexL2 ≫ dx.e) ≫ fst`
        rw [Cat.assoc, fst_pair, ← Cat.assoc, apexHom_fst, Cat.assoc, dx.proj]
        exact (apex_square x g)
      · -- `(apexHom ≫ pair (fst≫g.g) wRecon) ≫ snd = (apexL2 ≫ dx.e) ≫ snd`
        rw [Cat.assoc, snd_pair, Cat.assoc, apexL2_e_snd]
    -- cancel iso `dx.e` (it has inverse `dx.einv`)
    have := congrArg (· ≫ dx.einv) hiso
    simpa [Cat.assoc, dx.e_iso₁, Cat.comp_id] using this

/-- The packaged absorption iso: hom/inv + the two round-trips + the leg-compat. -/
structure ApexIso {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) where
  hom : (pairHasPullbacks.has g x).cone.pt.A ⟶
          prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T)))
  inv : prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T))) ⟶
          (pairHasPullbacks.has g x).cone.pt.A
  hom_inv : hom ≫ inv = Cat.id _
  inv_hom : inv ≫ hom = Cat.id _
  hom_fst : hom ≫ fst = ((pairHasPullbacks.has g x).cone.π₁).g

/-- A `listProd` of well-supported objects is well-supported (inlined; the `Capitalization.lean`
    version is not imported here).  `∏[] = 1` (`wellSupported_one'`); `∏(C::l) = C × ∏l`
    (`wellSupported_prod`). -/
theorem wellSupported_listProd' [PullbacksTransferCovers 𝒞] :
    ∀ {l : List 𝒞}, (∀ B ∈ l, WellSupported B) → WellSupported (listProd l)
  | [], _ => wellSupported_one'
  | C :: _, h => wellSupported_prod (h C (List.mem_cons_self))
      (wellSupported_listProd' (fun B hB => h B (List.mem_cons_of_mem _ hB)))

/-- **§1.547 — the FIRST LEG of the canonical `Â`-pullback of `(g, x)` is DENSE.**  The absorption
    iso `apexHom/apexInv` (`apex.A ≅ Z.A × W'`, `W' = ∏ non-collided survivors) packages the
    density: `e := apexHom`, `einv := apexInv` (round-trips `apexHom_apexInv`/`apexInv_apexHom`),
    `proj := apexHom_fst` (`apexHom ≫ fst = π₁.g`), `surv := dx.surv.filter (!collides)` (literally
    `W'`, so `wf = wg = id`), `survPinned` pulled back along `cone.π₂` + `apexL2_e_snd`, and
    `factorSplit`: each apex factor (Z-half ⇒ Y-derived; X-half ⇒ `dx.factorSplit` + `apex_cross`
    for collided, `W'`-coordinate for non-collided). -/
noncomputable def pairDense_pb_canonical_dense [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]
    {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    PairDense (pairHasPullbacks.has g x).cone.π₁ where
  W := listProd (dx.surv.filter (fun T => !collides Z T))
  wsupp := wellSupported_listProd' (fun B hB => dx.survWS B (List.mem_filter.1 hB).1)
  e := apexHom x g dx
  einv := apexInv x g dx
  e_iso₁ := apexHom_apexInv x g dx
  e_iso₂ := apexInv_apexHom x g dx
  proj := apexHom_fst x g dx
  survPinned := by
    intro V a b
    -- `a.g ≫ apexHom ≫ snd = b.g ≫ apexHom ≫ snd`; `apexHom ≫ snd = apexL2 ≫ dx.e ≫ snd ≫ wf ≫ partHom ≫ snd`
    have hsnd : apexHom x g dx ≫ (snd : prod Z.A (listProd (dx.surv.filter (fun T => !collides Z T)))
          ⟶ listProd (dx.surv.filter (fun T => !collides Z T)))
        = apexL2 x g ≫ dx.e ≫ snd ≫ dx.wf
          ≫ listProdPartitionHom (fun T => collides Z T) dx.surv ≫ snd := by
      unfold apexHom; rw [snd_pair]
    rw [hsnd]
    -- `dx.survPinned` equalizes the `dx.e ≫ snd` prefix of `(a.comp π₂)`, `(b.comp π₂)`
    have hpin := dx.survPinned (a.comp (pairHasPullbacks.has g x).cone.π₂)
      (b.comp (pairHasPullbacks.has g x).cone.π₂)
    -- `(c.comp π₂).g ≫ dx.e ≫ snd = c.g ≫ apexL2 ≫ dx.e ≫ snd`; post-compose the common tail.
    have key := congrArg
      (· ≫ (dx.wf ≫ listProdPartitionHom (fun T => collides Z T) dx.surv ≫ snd)) hpin
    simp only [PairHom.comp, Cat.assoc] at key ⊢
    -- both sides now `c.g ≫ apexL2 ≫ dx.e ≫ snd ≫ dx.wf ≫ partHom ≫ snd`
    exact key
  surv := dx.surv.filter (fun T => !collides Z T)
  survWS := fun B hB => dx.survWS B (List.mem_filter.1 hB).1
  wf := Cat.id _
  wg := Cat.id _
  wfg := Cat.id_comp _
  wgf := Cat.id_comp _
  factorSplit := by
    intro f hf
    -- deconstruct `f ∈ apex_obj.F = pairEqK …`: `f = ⟨p.1, eqMap ≫ p.2⟩` for `p ∈ pairProdK Z X`
    rcases List.mem_map.1 hf with ⟨p, hp, hpe⟩
    subst hpe  -- f = ⟨p.1, eqMap ≫ p.2⟩
    rcases List.mem_append.1 hp with hpZ | hpX
    · -- Z-HALF: `p = ⟨q.1, pairProdW ≫ fst ≫ q.2⟩`, q ∈ Z.F ⇒ Y-DERIVED with `gY := q`.
      rcases List.mem_map.1 hpZ with ⟨q, hq, hqe⟩
      subst hqe
      left
      refine ⟨q, hq, rfl, ?_⟩
      -- `f.snd = eqMap ≫ pairProdW ≫ fst ≫ q.2 = apexL1 ≫ q.2 = cone.π₁.g ≫ q.2` (defeq + assoc)
      show eqMap ((pairProjFst Z X).comp g).g ((pairProjSnd Z X).comp x).g
        ≫ pairProdW Z X ≫ fst ≫ q.2 = apexL1 x g ≫ q.2
      rw [apexL1_eq, Cat.assoc, Cat.assoc]
    · -- X-HALF: `p = ⟨q'.1, pairProdW ≫ snd ≫ q'.2⟩`, q' ∈ X.F.
      rcases List.mem_map.1 hpX with ⟨q', hq', hqe⟩
      subst hqe
      -- reduce nested projections, then re-associate so the prefix `eqMap ≫ (pairProdW ≫ snd)`
      -- (which IS `apexL2 x g` by `rfl`) is exposed.
      simp only []
      rw [← Cat.assoc (pairProdW Z X) snd q'.snd, ← Cat.assoc _ (pairProdW Z X ≫ snd) q'.snd]
      rcases dx.factorSplit q' hq' with ⟨gY, hgY, hgt, hge⟩ | ⟨k, hkt, hke⟩
      · -- q' Y-DERIVED: `q'.2 = x.g ≫ gY.2`; match `g.g ≫ gY.2` to a `Z`-factor ⇒ Y-DERIVED.
        obtain ⟨r, hr, hrt, hre⟩ := g.compat gY hgY
        left
        refine ⟨r, hr, hgt.trans hrt.symm, ?_⟩
        -- `apexL2 ≫ q'.2 = apexL2 ≫ x.g ≫ gY.2 = apexL1 ≫ g.g ≫ gY.2 = apexL1 ≫ r.2 = cone.π₁.g ≫ r.2`
        obtain ⟨q't, q'm⟩ := q'; obtain ⟨gYt, gYm⟩ := gY; obtain ⟨rt, rm⟩ := r
        simp only at hgt hrt hge hre ⊢
        cases hgt; cases hrt
        simp only at hge hre ⊢
        show apexL2 x g ≫ q'm = _
        rw [hge, ← Cat.assoc, ← apex_square, Cat.assoc, hre]
        rfl
      · -- q' SURVIVOR coordinate `k`.
        by_cases hc : collides Z (dx.surv.get k) = true
        · -- COLLIDING ⇒ Y-DERIVED via the cross constraint with the chosen Z-factor `w`.
          obtain ⟨w, hw, hwt, hwe⟩ := (pickArrow Z (dx.surv.get k) hc).2
          left
          refine ⟨w, hw, hkt.trans hwt.symm, ?_⟩
          -- `apexL2 ≫ q'.2 = apexL1 ≫ w.2 = cone.π₁.g ≫ w.2`
          obtain ⟨q't, q'm⟩ := q'; obtain ⟨wt, wm⟩ := w
          simp only at hkt hwt hke hwe ⊢
          cases hkt; cases hwt
          show apexL2 x g ≫ q'm = _
          rw [← apex_cross (x := x) (g := g) hw (f' := ⟨dx.surv.get k, q'm⟩) hq' rfl]
          rfl
        · -- NON-COLLIDING ⇒ SURVIVOR coordinate of the new density `W'`.
          right
          have hnc : (fun T => !collides Z T) (dx.surv.get k) = true := by
            simp only [Bool.not_eq_true']; exact Bool.eq_false_iff.2 hc
          have hget : (dx.surv.filter (fun T => !collides Z T)).get
              (filterIdx (fun T => !collides Z T) dx.surv k hnc) = dx.surv.get k :=
            filterIdx_get (fun T => !collides Z T) dx.surv k hnc
          refine ⟨filterIdx (fun T => !collides Z T) dx.surv k hnc, hkt.trans hget.symm, ?_⟩
          -- `apexL2 ≫ q'.2 = apexL2 ≫ dx.e ≫ snd ≫ dx.wf ≫ proj_k = apexHom ≫ snd ≫ id ≫ (h ▸ proj_{k'})`
          obtain ⟨q't, q'm⟩ := q'
          simp only at hkt hke ⊢
          cases hkt
          simp only at hke ⊢
          show apexL2 x g ≫ q'm = _
          rw [hke, Cat.id_comp]
          have hsnd : apexHom x g dx ≫ (snd : prod Z.A (listProd
                (dx.surv.filter (fun T => !collides Z T))) ⟶ _)
              = apexL2 x g ≫ dx.e ≫ snd ≫ dx.wf
                ≫ listProdPartitionHom (fun T => collides Z T) dx.surv ≫ snd := by
            unfold apexHom; rw [snd_pair]
          -- RHS `apexHom ≫ snd ≫ (hget' ▸ proj_{k'})`; peel `apexHom ≫ snd`, then `partHom_snd_proj`.
          rw [← Cat.assoc (apexHom x g dx) snd, hsnd]
          simp only [Cat.assoc]
          rw [partHom_snd_proj (fun T => collides Z T) dx.surv k hnc hget]
  -- survDistinct: the codomain is `Z`.  A surviving target `T` is in `dx.surv.filter (!collides Z)`,
  -- so `!collides Z T = true`, i.e. `collides Z T = false`, i.e. `¬ ∃ f ∈ Z.F, f.1 = T`, which is
  -- exactly `T ∉ Z.targets`.
  survDistinct := by
    intro k
    have hmem := List.get_mem (dx.surv.filter (fun T => !collides Z T)) k
    have hnc := (List.mem_filter.1 hmem).2
    have hcf : collides Z ((dx.surv.filter (fun T => !collides Z T)).get k) = false := by
      simp only [Bool.not_eq_true'] at hnc
      exact hnc
    intro hZ
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hZ
    have : collides Z ((dx.surv.filter (fun T => !collides Z T)).get k) = true :=
      decide_eq_true ⟨p, hp, hpe⟩
    rw [hcf] at this; exact Bool.noConfusion this
  -- survInX: the codomain of the apex is `pt`; the second leg `π₂ : pt → X` is a `PairHom`, so
  -- `X.targets ⊆ pt.targets`.  A survivor `T ∈ dx.surv.filter (…) ⊆ dx.surv` has `T ∈ X.targets`
  -- by `dx.survInX`, hence `T ∈ pt.targets`.
  survInX := by
    intro k
    have hmem := List.get_mem (dx.surv.filter (fun T => !collides Z T)) k
    rcases List.mem_filter.1 hmem with ⟨hmemSurv, _⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.1 hmemSurv
    have hXt : (dx.surv.filter (fun T => !collides Z T)).get k ∈ X.targets := hj ▸ dx.survInX j
    exact pairHom_targets_subset (pairHasPullbacks.has g x).cone.π₂ _ hXt

end ApexIso

/-- **§1.547 — the WITNESS for dense-pullback-closure.**  For a dense `x : X → Y` (data `dx`) and
    any `g : Z → Y`, there is a pullback cone `c` of the cospan `(g, x)` in `Â` whose first leg
    `c.π₁ : c.pt → Z` is again DENSE.  This is the genuine §1.547 content: the dense `x`'s
    product-projection form (`X.A ≅ Y.A × W`, `x.g` = projection) is stable under base change.

    The cone is the CANONICAL `Â`-pullback (`pairHasPullbacks`), so `c` itself and its pullback
    property `c.IsPullback` are SORRY-FREE; the only residual is the first-leg density, isolated as
    `pairDense_pb_canonical_dense` (the single sharply-documented §1.547 obstruction). -/
theorem pairDense_pb_witness [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]
    {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (dx : PairDense x) :
    ∃ c : @Cone (PairObj 𝒞) _ _ _ _ g x, c.IsPullback ∧ Nonempty (PairDense c.π₁) := by
  -- The CANONICAL `Â`-pullback of the cospan `(g, x)` is the witness cone; `c` and `c.IsPullback`
  -- are Sorry-free, the residual being only the first-leg density (`pairDense_pb_canonical_dense`).
  refine ⟨(pairHasPullbacks.has g x).cone, (pairHasPullbacks.has g x).cone_isPullback, ?_⟩
  exact ⟨pairDense_pb_canonical_dense x g dx⟩

/-- §1.48(iii) for `Â`: the dense morphisms are closed under pullback.  STATEMENT is the genuine
    `DenseClass.pb_mem` obligation for `PairDense`; the dense `x`'s product-projection form
    (`X.A ≅ Y.A × W`, `x.g = fst`) is stable under base change, the `Â`-pullback projection being
    `Z.A × W → Z.A` onto the same `W` — read off the underlying product-pullback in `A`.

    Sorry-free modulo `pairDense_pb_witness`: take the witnessing pullback cone `c` (with `c.π₁`
    dense); the canonical pullback cone `(HasPullbacks.has g x).cone` is comparison-iso to `c`
    (`isIso_of_two_pullbacks`), so `canonical.π₁ = u.comp c.π₁` for an iso `Â`-arrow `u`; an iso is
    dense (`pairDense_of_iso`) and dense is composition-closed (`pairDense_comp`), giving
    `PairDense canonical.π₁`. -/
theorem pairDense_pb [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]
    {X Y Z : PairObj 𝒞} (x : X ⟶ Y) (g : Z ⟶ Y) (hx : Nonempty (PairDense x)) :
    Nonempty (PairDense ((HasPullbacks.has g x).cone.π₁)) := by
  obtain ⟨dx⟩ := hx
  obtain ⟨c, hc, ⟨dπ₁⟩⟩ := pairDense_pb_witness x g dx
  -- the canonical cone of the same cospan is a pullback
  have hcanpb : ((HasPullbacks.has g x).cone).IsPullback := (HasPullbacks.has g x).cone_isPullback
  -- comparison `Â`-arrow `u : can.pt → c.pt` with `u ≫ c.π₁ = can.π₁`, `u ≫ c.π₂ = can.π₂`
  obtain ⟨u, ⟨hu₁, hu₂⟩, _⟩ := hc (HasPullbacks.has g x).cone
  have huiso : @IsIso (PairObj 𝒞) _ _ _ u := isIso_of_two_pullbacks hcanpb hc u hu₁ hu₂
  obtain ⟨u', huu', hu'u⟩ := huiso
  -- `can.π₁ = u.comp c.π₁`; iso `u` is dense, `c.π₁` is dense, composite is dense
  have hdu : PairDense u := pairDense_of_iso u' (congrArg PairHom.g huu') (congrArg PairHom.g hu'u)
  have hcomp : PairDense (u.comp c.π₁) := pairDense_comp hdu dπ₁
  exact ⟨hu₁ ▸ hcomp⟩

/-- **§1.547 — `PairDense` is a `DenseClass (PairObj 𝒞)`.**  `mem x := Nonempty (PairDense x)`; isos
    dense (`pairDense_of_isIso`), composition-closed (`pairDense_comp`), pullback-closed
    (`pairDense_pb`).  This is the refined dense class the §1.48 rational category inverts to form
    `A* = Â[PairDense⁻¹]`. -/
def pairDenseClass [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] : DenseClass (PairObj 𝒞) where
  mem x := Nonempty (PairDense x)
  iso_mem _ hx := pairDense_of_isIso hx
  comp_mem _ _ hx hy := hx.elim (fun dx => hy.elim (fun dy => ⟨pairDense_comp dx dy⟩))
  pb_mem x g hx := pairDense_pb x g hx

/-- **R7 — `pairDenseClass` is a DENSE CLASS OF MONICS** (the book's §1.48/§1.481 hypothesis).  Every
    member is `Monic` in `Â` (`pairDense_monic`).  This is the forward `mem → Monic` direction — exactly
    the §1.48 "dense class of monics" requirement (the calculus-of-fractions cancellation uses dense
    roof legs being monic-in-`Â`, NOT the reverse `Monic → mem`, which is false for a proper subclass).
    Refutes the R6 claim that `pairDenseClass` could not be a monic class. -/
theorem pairDenseClass_mem_mono [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]
    {X Y : PairObj 𝒞} (x : PairHom X Y) (hx : (pairDenseClass (𝒞 := 𝒞)).mem x) :
    @Monic (PairObj 𝒞) _ X Y x :=
  hx.elim (fun d => pairDense_monic d)

/-! ### §1.547  THE R7 CORRECTION — `pairDenseClass` IS a class of monics (`pairDense_monic`)

  R6 wrongly concluded `pairDenseClass` could not be a monic class and that a DUAL right-fraction
  (co-span) calculus was needed.  That was a CATEGORY CONFUSION: it conflated "monic in `Â`" with
  "the underlying `A`-map is monic in `A`".  A dense `pairDense` morphism's UNDERLYING `A`-map is an
  epic projection (`pairDense_cover`/`pairDense_epi`), but the morphism itself is MONIC IN `Â`
  (`pairDense_monic`), exactly as the book states ("every dense morphism is monic").  Being both
  monic-in-`Â` AND epic-in-`Â` does NOT collapse to an iso, because `Â` is not balanced (a monic
  epic need not be invertible).  Hence the §1.48 monic LEFT-fraction skeleton is the CORRECT tool for
  §1.547's `A* = Â[pairDense⁻¹]`; no dual calculus is required.

  `pairDense_monic_and_epic`: every `pairDense` morphism is both monic-in-`Â` and epic-in-`Â` — the
  precise, machine-checked statement of the R7 correction, both halves now THEOREMS (no hypothesis). -/

/-- **R7 (machine-checked, Sorry-free, axiom-free).**  A `pairDense` morphism is BOTH `Monic` in `Â`
    (`pairDense_monic`) AND left-cancellable for the §1.547 localisation (`pairDense_epi`).  This is
    Freyd's "every dense morphism is monic" together with the faithfulness cancellation, and it shows
    the monic left-fraction calculus applies to `pairDenseClass` — refuting R6's "collapse"/co-span
    framing, which mistook the underlying-`A`-arrow's epi-ness for failure of monic-in-`Â`. -/
theorem pairDense_monic_and_epic [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞]
    {X Y : PairObj 𝒞} {x : PairHom X Y} (dx : PairDense x) :
    @Monic (PairObj 𝒞) _ _ _ x ∧
      (∀ {Z : PairObj 𝒞} (a b : PairHom Y Z), x.comp a = x.comp b → a = b) :=
  ⟨pairDense_monic dx, fun a b h => pairDense_epi dx a b h⟩

/-! ### §1.547  `pairDenseClass` IS a `DenseRoof` class — the rational category `A* = Â[pairDense⁻¹]`

  `DenseRoof pairDenseClass` needs ONLY that members are monic (`pairDenseClass_mem_mono`), which is the
  R7 keystone (`pairDense_monic`).  The §1.48 left-calculus skeleton (`ratCatOf`/`locFunctorOf`),
  reformulated over member-denominator pullbacks, needs nothing more — NO saturation/Ore condition.  So
  the rational category `A* = Â[pairDense⁻¹]` and its faithful localisation functor `Â → A*` build
  SORRY-FREE from the (Sorry-free, axiom-clean) closure laws of `pairDenseClass`. -/

/-- **§1.547 — `pairDenseClass` is a `DenseRoof` class.**  Members are `Monic` in `Â`
    (`pairDenseClass_mem_mono`, i.e. `pairDense_monic`).  This is the SINGLE hypothesis the §1.48
    left-calculus-of-fractions skeleton needs, so `ratCatOf`/`locFunctorOf` instantiate at
    `pairDenseClass` to give `A* = Â[pairDense⁻¹]`. -/
theorem pairDense_denseRoof [HasEqualizers 𝒞] [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] :
    DenseRoof (pairDenseClass (𝒞 := 𝒞)) where
  mem_mono _ h := pairDenseClass_mem_mono _ h

/-- **§1.547 — the rational category `A* = Â[pairDense⁻¹]`.**  The §1.48 generic rational category
    `ratCatOf` instantiated at the refined dense class `pairDenseClass`, via `pairDense_denseRoof`.
    Objects = objects of `Â`; homs = `Â`-fraction quotients; Sorry-free. -/
def pairRatCat [HasEqualizers 𝒞] [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] :
    Cat.{u} (RatObj (pairDense_denseRoof (𝒞 := 𝒞))) :=
  ratCatOf pairDense_denseRoof

/-- **§1.547 — the faithful localisation functor `T : Â → A*`.**  The §1.48 generic localisation
    functor `locFunctorOf` at `pairDenseClass`, via `pairDense_denseRoof`; identity on objects,
    `f ↦ [A ←id— A —f→ B]`.  Sorry-free.  Its faithfulness obligation (homs identified by a common
    DENSE roof are equal) is `pairLocalisation_faithful_criterion`, already proven. -/
def pairLocFunctor [HasEqualizers 𝒞] [DecidableEq 𝒞] [PullbacksTransferCovers 𝒞] :
    @Functor (PairObj 𝒞) (RatObj (pairDense_denseRoof (𝒞 := 𝒞))) _ pairRatCat :=
  locFunctorOf pairDense_denseRoof

end PairEq

end PairsCategory

/-! ## §1.547  The factor-slice bridge `Â → Σ U, A/(∏U)`

  The conceptual core of §1.547: `A*` is the directed union, over finite sets `U` of
  well-supported objects, of the pre-regular slices `A/(∏U)` (`SliceRegular`).  An object
  `(A, F)` of `Â` carries exactly the data of a slice object over the product of its factor
  TARGETS `F° = X.targets`: namely the FACTOR MAP `A → ∏(F°)` tupling all the recorded
  factors `f.2 : A → f.1`.  This block builds that bridge — the object map
  `Â → Σ U, Over (∏U)`, `(A,F) ↦ ⟨F°, ⟨A, factorMap⟩⟩` — and its defining property that the
  `k`-th projection of the factor map recovers the `k`-th factor.  These are the Sorry-free
  foundations connecting `PairObj` (this file's `Â`) to the §1.547 product-slices.

  This is the OBJECT half of Freyd's slice-equivalence verification.  The factor map's targets
  `X.targets` are all well-supported (`X.wsupp`), so `∏(X.targets)` is well-supported, and the
  slice `A/(∏X.targets)` is pre-regular (`overPreRegular`) and acquires a point of every factor
  (`listProdSliceAcquiresEveryFactor`).  The MORPHISM half — a `PairHom`/dense map descending to
  a slice morphism along the directed transition — is the remaining content (see the note at the
  end of the section), and is exactly what the colimit-of-categories step needs. -/

section FactorSlice
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-- **§1.547 — the FACTOR MAP `A → ∏(F°)` of a factor list.**  Tuples the recorded factors
    `f.2 : A → f.1` of `F` into the product of their targets `F.map (·.1)`.  Empty list ↦ the
    unique map to `∏[] = 1`; `p :: F ↦ pair p.2 (rec F)`.  This is the underlying arrow of the
    slice object an object of `Â` determines over the product of its factor targets. -/
def factorTuple {A : 𝒞} : ∀ (F : List (Σ T : 𝒞, A ⟶ T)), A ⟶ listProd (F.map (·.1))
  | [] => term A
  | p :: F => pair p.2 (factorTuple F)

@[simp] theorem factorTuple_nil {A : 𝒞} :
    factorTuple ([] : List (Σ T : 𝒞, A ⟶ T)) = term A := rfl

@[simp] theorem factorTuple_cons {A : 𝒞} (p : Σ T : 𝒞, A ⟶ T)
    (F : List (Σ T : 𝒞, A ⟶ T)) :
    factorTuple (p :: F) = pair p.2 (factorTuple F) := rfl

/-- **§1.547 — the `k`-th projection of the factor map recovers the `k`-th factor.**  Composing
    `factorTuple F` with the product projection `listProdProj (F.map ·.1) k` gives back the
    recorded factor's arrow at the SAME position, transported across the target identity
    `h : (F.map (·.1)).get k = (F.get k').1` (with `k'` the matching index into `F`).  This is the
    DEFINING property of the factor map: it packages every factor as a coordinate of `∏(F°)`. -/
theorem factorTuple_proj {A : 𝒞} :
    ∀ (F : List (Σ T : 𝒞, A ⟶ T)) (n : Nat)
      (hk : n < (F.map (·.1)).length) (hk' : n < F.length)
      (h : (F.map (·.1)).get ⟨n, hk⟩ = (F.get ⟨n, hk'⟩).1),
      factorTuple F ≫ listProdProj (F.map (·.1)) ⟨n, hk⟩ = h ▸ (F.get ⟨n, hk'⟩).2
  | p :: F, 0, hk, hk', h => by
      have hh : h = rfl := rfl
      subst hh
      show pair p.2 (factorTuple F) ≫ (fst : prod p.1 _ ⟶ p.1) = _
      rw [fst_pair]; rfl
  | p :: F, n + 1, hk, hk', h => by
      show pair p.2 (factorTuple F) ≫ ((snd : prod p.1 _ ⟶ _) ≫ _) = _
      rw [← Cat.assoc, snd_pair]
      exact factorTuple_proj F n (Nat.lt_of_succ_lt_succ hk) (Nat.lt_of_succ_lt_succ hk') h

/-- **§1.547 — the factor map of an object of `Â`.**  The `factorTuple` of `X.F`, into the product
    of `X.targets = X.F.map (·.1)`.  This is the underlying `𝒞`-arrow of the slice object `X`
    determines over `∏(X.targets)`. -/
def pairFactorMap (X : PairObj 𝒞) : X.A ⟶ listProd X.targets := factorTuple X.F

/-- **§1.547 — the SLICE OBJECT an object of `Â` determines.**  `(A, F) ↦ ⟨A, A → ∏(F°)⟩`, an
    object of the product-slice `A/(∏ X.targets)`.  This is the OBJECT part of the §1.547 bridge
    `Â → Σ U, A/(∏U)`: an object of `Â` is exactly a slice object over the product of its factor
    targets, the factor map tupling all recorded factors. -/
def pairSliceObj (X : PairObj 𝒞) : Over (listProd X.targets) :=
  ⟨X.A, pairFactorMap X⟩

@[simp] theorem pairSliceObj_dom (X : PairObj 𝒞) : (pairSliceObj X).dom = X.A := rfl
@[simp] theorem pairSliceObj_hom (X : PairObj 𝒞) :
    (pairSliceObj X).hom = pairFactorMap X := rfl

/-- **§1.547 — the factor map of `X` recovers every factor of `X` by projection.**  Specialisation
    of `factorTuple_proj` to `X.F`/`X.targets`: composing `pairFactorMap X` with the `k`-th
    projection of `∏(X.targets)` recovers the `k`-th factor's arrow `(X.F.get k').2` (transported
    across the target identity).  This is what makes `pairSliceObj X` a faithful record of `X`: its
    structure map encodes ALL of `X`'s factors. -/
theorem pairFactorMap_proj (X : PairObj 𝒞) (n : Nat)
    (hk : n < X.targets.length) (hk' : n < X.F.length)
    (h : X.targets.get ⟨n, hk⟩ = (X.F.get ⟨n, hk'⟩).1) :
    pairFactorMap X ≫ listProdProj X.targets ⟨n, hk⟩ = h ▸ (X.F.get ⟨n, hk'⟩).2 :=
  factorTuple_proj X.F n hk hk' h

/-! ### §1.547 — the CHOICE-FREE base restriction `∏l₁ → ∏l₂` for `l₂ ⊆ l₁`

  The §1.547 directed transition `A/(∏V) → A/(∏U)` (for `V ⊆ U`) base-changes along a product
  projection `∏U → ∏V`.  Constructing that projection CHOICE-FREE is the residual (A) recorded in
  `RelativeCapitalization.lean` (`StrictBaseChange`): list-subset `V ⊆ U` is a `Prop`, so a
  *positional* match cannot be extracted from it.  With `DecidableEq 𝒞`, however, it CAN — by a
  decidable target SEARCH (the same device as `findArrow`/`collReconstruct`): for each target `T` of
  `l₂`, search `l₁` for a coordinate of target `T` and project to it.  This builds the base map
  `∏l₁ → ∏l₂` constructively, sidestepping the choice obstruction whenever `DecidableEq 𝒞` holds. -/

section restrict
variable [DecidableEq 𝒞]

/-- Search a product-coordinate list `l` for one of target `T`, returning its PROJECTION
    `∏l → T` (the §1.547 base-restriction coordinate).  Decidable analogue of `findArrow`
    (which searches a FACTOR list for an arrow); here we search a list of *objects* and return
    the projection `listProdProj l k` at the found position. -/
def findProj (T : 𝒞) :
    ∀ (l : List 𝒞), (∃ S ∈ l, S = T) → (listProd l ⟶ T)
  | [], hex => absurd hex (by simp)
  | S :: l, hex => by
      by_cases hST : S = T
      · exact (fst : prod S (listProd l) ⟶ S) ≫ (hST ▸ Cat.id S)
      · refine (snd : prod S (listProd l) ⟶ listProd l) ≫ findProj T l ?_
        rcases hex with ⟨S', hS', hS'T⟩
        rcases List.mem_cons.1 hS' with rfl | hS'tail
        · exact absurd hS'T hST
        · exact ⟨S', hS'tail, hS'T⟩

/-- **§1.547 — the choice-free base restriction `∏l₁ → ∏l₂` for `l₂ ⊆ l₁` (with `DecidableEq`).**
    Each `l₂`-coordinate is the `findProj` of that target into `l₁`.  This is the product projection
    the §1.547 directed transition `A/(∏V) → A/(∏U)` base-changes along (for `V = l₂ ⊆ l₁ = U`),
    built constructively by decidable target search instead of by choice over the subset `Prop`. -/
def listProdRestrict : ∀ (l₁ l₂ : List 𝒞), (∀ T ∈ l₂, T ∈ l₁) → (listProd l₁ ⟶ listProd l₂)
  | _, [], _ => term _
  | l₁, T :: l₂, h =>
      pair (findProj T l₁ ⟨T, h T (List.mem_cons_self), rfl⟩)
           (listProdRestrict l₁ l₂ (fun S hS => h S (List.mem_cons_of_mem _ hS)))

/-- **§1.547 — the `k`-th coordinate of the base restriction is the `findProj` of that target.**
    `listProdRestrict l₁ l₂ h ≫ listProdProj l₂ k = findProj (l₂.get k) l₁ _`: the restriction
    really does project `∏l₁` onto each `l₂`-coordinate via the searched-for `l₁`-coordinate.
    Structural induction on `l₂`/`k` (parallel to `collReconstruct_proj`). -/
theorem listProdRestrict_proj :
    ∀ (l₁ l₂ : List 𝒞) (h : ∀ T ∈ l₂, T ∈ l₁) (k : Fin l₂.length),
      listProdRestrict l₁ l₂ h ≫ listProdProj l₂ k
        = findProj (l₂.get k) l₁ ⟨l₂.get k, h (l₂.get k) (l₂.get_mem k), rfl⟩
  | _, [], _, k => k.elim0
  | l₁, T :: l₂, h, ⟨0, hk0⟩ => by
      show pair _ _ ≫ (fst : prod T (listProd l₂) ⟶ T) = _
      rw [fst_pair]; rfl
  | l₁, T :: l₂, h, ⟨n + 1, hk⟩ => by
      show pair _ (listProdRestrict l₁ l₂ _) ≫ ((snd : prod T (listProd l₂) ⟶ listProd l₂)
            ≫ listProdProj l₂ ⟨n, Nat.lt_of_succ_lt_succ hk⟩) = _
      rw [← Cat.assoc, snd_pair, listProdRestrict_proj l₁ l₂ _ ⟨n, Nat.lt_of_succ_lt_succ hk⟩]
      rfl

/-- **§1.547 — the factor map followed by `findProj` recovers a factor of that target.**  Composing
    `factorTuple F` (the factor map) with the searched projection `findProj T (F°)` lands on the
    underlying arrow of SOME `F`-factor of target `T` (the one the decidable search lands on).  Under
    `PairObj.distinct` all `F`-factors of a fixed target agree, so this pins the value.  This is the
    KEY morphism-half computation: it lets a `PairHom` (whose compat matches Y-factors to X-factors of
    the same target) commute with the base restriction `listProdRestrict X° Y°`. -/
theorem factorTuple_findProj {A : 𝒞} (T : 𝒞) :
    ∀ (F : List (Σ S : 𝒞, A ⟶ S)) (hex : ∃ S ∈ F.map (·.1), S = T),
      ∃ f ∈ F, ∃ h : f.1 = T, factorTuple F ≫ findProj T (F.map (·.1)) hex = h ▸ f.2
  | [], hex => absurd hex (by simp)
  | p :: F, hex => by
      show ∃ f ∈ p :: F, ∃ h : f.1 = T,
        pair p.2 (factorTuple F) ≫ findProj T ((p :: F).map (·.1)) hex = h ▸ f.2
      by_cases hpT : p.1 = T
      · refine ⟨p, List.mem_cons_self, hpT, ?_⟩
        -- findProj on a HEAD match unfolds to `fst ≫ (hpT ▸ id)`; precompose `pair p.2 _`.
        have hfp : findProj T ((p :: F).map (·.1)) hex
            = (fst : prod p.1 (listProd (F.map (·.1))) ⟶ p.1) ≫ (hpT ▸ Cat.id p.1) := by
          show (if h : p.1 = T then _ else _) = _
          rw [dif_pos hpT]
        rw [hfp, ← Cat.assoc, fst_pair]
        cases hpT; rw [Cat.comp_id]
      · -- TAIL: findProj recurses via `snd`; `pair p.2 _ ≫ snd = factorTuple F`.
        have hfp : findProj T ((p :: F).map (·.1)) hex
            = (snd : prod p.1 (listProd (F.map (·.1))) ⟶ listProd (F.map (·.1)))
                ≫ findProj T (F.map (·.1)) (by
                    rcases hex with ⟨S', hS', hS'T⟩
                    rcases List.mem_cons.1 hS' with rfl | hS'tail
                    · exact absurd hS'T hpT
                    · exact ⟨S', hS'tail, hS'T⟩) := by
          show (if h : p.1 = T then _ else _) = _
          rw [dif_neg hpT]
        rw [hfp, ← Cat.assoc, snd_pair]
        obtain ⟨f, hf, h, he⟩ := factorTuple_findProj T F _
        exact ⟨f, List.mem_cons_of_mem _ hf, h, he⟩


/-- **§1.547 — the MORPHISM HALF of the bridge: `m` commutes with the base restriction.**  For a
    `PairHom m : X → Y`, the underlying arrow `m.g` makes the factor maps commute over the base
    restriction `∏X° → ∏Y°`:
        `m.g ≫ pairFactorMap Y = pairFactorMap X ≫ listProdRestrict X° Y° (Y°⊆X°)`.
    Equivalently, `m.g : pairSliceObj X → (base-change of pairSliceObj Y)` is a slice morphism over
    `∏X°`.  Proof by projection-extensionality: at each `Y°`-coordinate, the LHS is `m.g ≫ (Y-factor)`
    (`factorTuple_proj`) and the RHS is the searched `X`-factor of the same target
    (`listProdRestrict_proj` + `factorTuple_findProj`); compat matches them, and `X.distinct` pins the
    searched factor to compat's.  This is the choice-free morphism half of `Â → Σ U, A/(∏U)`. -/
theorem pairHom_commutes_restrict [HasPullbacks 𝒞] {X Y : PairObj 𝒞} (m : PairHom X Y) :
    m.g ≫ pairFactorMap Y
      = pairFactorMap X ≫ listProdRestrict X.targets Y.targets (pairHom_targets_subset m) := by
  apply listProd_hom_ext Y.targets
  intro k
  rw [Cat.assoc, Cat.assoc]
  -- the matching index into Y.F (same Nat, Y.targets = Y.F.map ·.1)
  have hk' : k.1 < Y.F.length := by simpa [PairObj.targets] using k.2
  have htgt : Y.targets.get k = (Y.F.get ⟨k.1, hk'⟩).1 := by
    simp only [PairObj.targets, List.get_eq_getElem, List.getElem_map]
  -- LHS: m.g ≫ (pairFactorMap Y ≫ proj_k) = m.g ≫ (htgt ▸ (Y.F.get k').2)
  rw [show k = ⟨k.1, k.2⟩ from rfl, pairFactorMap_proj Y k.1 k.2 hk' htgt]
  -- the Y-factor `p := Y.F.get k'` and its compat-matched X-factor `q`
  have hpmem : Y.F.get ⟨k.1, hk'⟩ ∈ Y.F := List.get_mem _ _
  obtain ⟨q, hq, hqt, hqe⟩ := m.compat (Y.F.get ⟨k.1, hk'⟩) hpmem
  -- RHS: pairFactorMap X ≫ listProdRestrict ≫ proj_k = pairFactorMap X ≫ findProj (htgt-target) X°
  rw [listProdRestrict_proj X.targets Y.targets _ k]
  -- findProj recovers SOME X-factor `f` of target `Y.targets.get k`; pin it via distinct.
  obtain ⟨f, hf, hfh, hfe⟩ := factorTuple_findProj (Y.targets.get k) X.F
    ⟨Y.targets.get k, pairHom_targets_subset m _ (List.get_mem _ _), rfl⟩
  rw [(show pairFactorMap X = factorTuple X.F from rfl)]
  rw [show findProj (Y.targets.get k) X.targets
        ⟨Y.targets.get k, pairHom_targets_subset m _ (List.get_mem _ _), rfl⟩
      = findProj (Y.targets.get k) (X.F.map (·.1)) _ from rfl, hfe]
  -- goal: m.g ≫ (htgt ▸ (Y.F.get k').2) = hfh ▸ f.2.
  -- `f` and `q` are both X-factors of target `Y.targets.get k`; X.distinct pins their arrows.
  -- target chain: q.1 = (Y.F.get k').1 = Y.targets.get k = f.1.
  have hqf : q.1 = f.1 := hqt.trans (htgt.symm.trans hfh.symm)
  have hqf2 : hqf ▸ q.2 = f.2 := X.distinct q hq f hf hqf
  -- compat gives `m.g ≫ p.2 = hqt ▸ q.2`.  Substitute it (after pushing `htgt ▸` through `≫`),
  -- then every remaining cast lands `q.2` at the common target `Y.targets.get k`; `subst` them all.
  -- Generalize the Y-factor (target + arrow) so the target equalities become substitutable.
  revert htgt hqt hqe
  generalize Y.F.get ⟨k.1, hk'⟩ = p
  obtain ⟨pT, pa⟩ := p
  obtain ⟨qT, qa⟩ := q
  obtain ⟨fT, fa⟩ := f
  intro htgt hqt hqe
  simp only at htgt hqt hfh hqf hqe hqf2 ⊢
  subst hqt; subst htgt; subst hfh
  rw [hqe, hqf2]

/-- **§1.547 — a `PairHom` IS a slice morphism (the bridge's morphism, packaged).**  By
    `pairHom_commutes_restrict`, the underlying arrow `m.g` of a `PairHom m : X → Y` is an `OverHom`
    in `Over (∏Y.targets)` from the REINDEXED slice object `reindexObj (listProdRestrict X° Y°)
    (pairSliceObj X)` (= `⟨X.A, pairFactorMap X ≫ listProdRestrict⟩`) to `pairSliceObj Y`.  This is
    the choice-free realisation of "`Â`-morphism ↦ slice morphism" along the §1.547 directed
    transition (here the strict reindexing `reindexObj`, whose `r = listProdRestrict X° Y°` is the
    base projection `∏X° → ∏Y°` built by decidable search).  It packages the full bridge object+map
    over the common base `∏Y.targets`. -/
def pairHomToSlice [HasPullbacks 𝒞] {X Y : PairObj 𝒞} (m : PairHom X Y) :
    OverHom (reindexObj (listProdRestrict X.targets Y.targets (pairHom_targets_subset m))
              (pairSliceObj X)) (pairSliceObj Y) :=
  ⟨m.g, by
    show m.g ≫ pairFactorMap Y
        = pairFactorMap X ≫ listProdRestrict X.targets Y.targets (pairHom_targets_subset m)
    exact pairHom_commutes_restrict m⟩

/-- **§1.547 — FULLNESS of the bridge over the codomain base `∏Y°`.**  Conversely to
    `pairHomToSlice`, EVERY slice morphism `φ` over `∏Y°` from the reindexed `pairSliceObj X` to
    `pairSliceObj Y` (i.e. `φ.f ≫ pairFactorMap Y = pairFactorMap X ≫ listProdRestrict X° Y° hsub`)
    is the image of a `PairHom X → Y` with underlying arrow `φ.f`.  This is the KEY fullness: a slice
    map over `∏Y°` commuting with the factor maps respects every `Y`-factor, which is exactly the
    `PairHom.compat` obligation.  Proof: project the commuting square at each `Y°`-coordinate; the LHS
    is `φ.f ≫ (Y-factor)` (`factorTuple_proj`), the RHS is the searched `X`-factor of the SAME target
    (`listProdRestrict_proj` + `factorTuple_findProj`), giving the matched `q ∈ X.F`. -/
def pairHomOfSlice [HasPullbacks 𝒞] {X Y : PairObj 𝒞} (hsub : ∀ T ∈ Y.targets, T ∈ X.targets)
    (φ : OverHom (reindexObj (listProdRestrict X.targets Y.targets hsub) (pairSliceObj X))
                 (pairSliceObj Y)) : PairHom X Y where
  g := φ.f
  compat p hp := by
    -- locate `p` positionally in `Y.F` (so we can project the commuting square at its coordinate)
    obtain ⟨k, hk⟩ := List.mem_iff_get.1 hp
    -- the same Nat index into `Y.targets` (= Y.F.map ·.1)
    have hkt : k.1 < Y.targets.length := by simp [PairObj.targets]
    let kt : Fin Y.targets.length := ⟨k.1, hkt⟩
    have htgt : Y.targets.get kt = p.1 := by
      simp only [kt, PairObj.targets, List.get_eq_getElem, List.getElem_map]
      rw [← hk]; rfl
    -- the slice commuting square, projected at coordinate `kt`
    have hw : φ.f ≫ pairFactorMap Y
        = pairFactorMap X ≫ listProdRestrict X.targets Y.targets hsub := φ.w
    have hproj := congrArg (· ≫ listProdProj Y.targets kt) hw
    simp only [Cat.assoc] at hproj
    -- LHS coordinate: `pairFactorMap Y ≫ proj_kt = htgt? ▸ (Y.F.get k).2`
    have hkF : k.1 < Y.F.length := k.2
    -- `Y.F.get ⟨k.1,hkF⟩ = Y.F.get k = p`, so project lands on `p.2`.
    have hgetp : Y.F.get ⟨k.1, hkF⟩ = p := hk
    have htgt' : Y.targets.get kt = (Y.F.get ⟨k.1, hkF⟩).1 := by
      rw [hgetp]; exact htgt
    rw [pairFactorMap_proj Y k.1 hkt hkF htgt'] at hproj
    -- RHS coordinate: `pairFactorMap X ≫ listProdRestrict ≫ proj_kt = pairFactorMap X ≫ findProj …`
    rw [listProdRestrict_proj X.targets Y.targets hsub kt] at hproj
    obtain ⟨f, hf, hfh, hfe⟩ := factorTuple_findProj (Y.targets.get kt) X.F
      ⟨Y.targets.get kt, hsub _ (List.get_mem _ _), rfl⟩
    rw [(show pairFactorMap X = factorTuple X.F from rfl),
        show findProj (Y.targets.get kt) X.targets
              ⟨Y.targets.get kt, hsub _ (List.get_mem _ _), rfl⟩
            = findProj (Y.targets.get kt) (X.F.map (·.1)) _ from rfl, hfe] at hproj
    -- now `hproj : φ.f ≫ (htgt' ▸ (Y.F.get k).2) = hfh ▸ f.2`; package as compat for `p`.
    refine ⟨f, hf, hfh.trans htgt, ?_⟩
    -- replace `p` by the positional factor `yp := Y.F.get ⟨k.1,hkF⟩` (`hgetp : yp = p`), so the cast
    -- in `hproj` and the goal share the same term; then match casts on the target.
    subst hgetp
    -- `htgt` and `htgt'` now coincide; generalize the two target terms so the casts substitute.
    clear hfe hk hp hw
    revert htgt htgt' hproj hfh
    obtain ⟨fT, fa⟩ := f
    generalize Y.F.get ⟨k.1, hkF⟩ = yp
    obtain ⟨yT, ya⟩ := yp
    generalize Y.targets.get kt = T
    intro htgt htgt' hproj hfh
    simp only at htgt htgt' hfh hproj ⊢
    subst hfh; subst htgt'
    simpa using hproj

end restrict

/-- **§1.547 — `pairForget` reflects isos when the target sets COINCIDE.**  An `Â`-arrow `n : K → C`
    whose underlying `A`-arrow `n.g` is an iso, AND whose codomain targets are a SUBSET of the domain's
    (`K° ⊇ C°` is automatic from `compat`; the extra hypothesis is `K° ⊆ C°`, so the two target sets
    coincide), is an iso IN `Â`.  This is the precise form of "`pairForget` reflects isos": the
    obstruction (2) of `pairPullbacksTransferCovers` is EXACTLY the failure of `K° ⊆ C°` for a free
    test mono; when it holds, the underlying inverse `i := n.g⁻¹` IS a `PairHom C → K`.

    The inverse's `compat` is built directly (no fullness needed): for `p ∈ K.F`, `K° ⊆ C°` gives a
    `C`-factor `q` of the same target; `n.compat q` then yields a `K`-factor `q'` of target `p.1` with
    `n.g ≫ q.2 = q'.2`, and `K.distinct` pins `q' = p`, so `i ≫ p.2 = i ≫ n.g ≫ q.2 = q.2`. -/
theorem pairForget_reflects_iso_of_targets_subset [HasPullbacks 𝒞] {K C : PairObj 𝒞}
    (n : PairHom K C) (hg : IsIso n.g) (htgt : ∀ T ∈ K.targets, T ∈ C.targets) :
    @IsIso (PairObj 𝒞) _ K C n := by
  obtain ⟨i, hi₁, hi₂⟩ := hg
  -- the inverse `Â`-arrow `i : C → K`, underlying `i = n.g⁻¹`.
  have hicompat : ∀ p ∈ K.F, ∃ q ∈ C.F, ∃ h : q.1 = p.1, i ≫ p.2 = h ▸ q.2 := by
    intro p hp
    -- `p.1 ∈ K°`, so by `htgt` some `C`-factor `q` has target `p.1`.
    have hp1K : p.1 ∈ K.targets := List.mem_map.2 ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqt⟩ := List.mem_map.1 (htgt p.1 hp1K)
    -- `n.compat q` : some `q' ∈ K.F` of target `q.1` with `n.g ≫ q.2 = q'.2`.
    obtain ⟨q', hq', hq't, hq'e⟩ := n.compat q hq
    -- `q'.1 = q.1 = p.1`; `K.distinct` pins `q' = p` (as arrows after the target cast).
    have hq'p : q'.1 = p.1 := hq't.trans hqt
    have hq'eq : hq'p ▸ q'.2 = p.2 := K.distinct q' hq' p hp hq'p
    refine ⟨q, hq, hqt, ?_⟩
    -- i ≫ p.2 = i ≫ (n.g ≫ q.2) (via hq'e, hq'eq, casts) = (i ≫ n.g) ≫ q.2 = q.2.
    -- Reconcile casts by generalizing the targets.
    revert hq'e hq'eq hqt hq't
    obtain ⟨pT, pa⟩ := p
    obtain ⟨qT, qa⟩ := q
    obtain ⟨q'T, q'a⟩ := q'
    intro hq't hqt hq'e hq'eq
    simp only at hqt hq't hq'p hq'e hq'eq ⊢
    subst hqt; subst hq't
    simp only at hq'e hq'eq ⊢
    subst hq'eq
    rw [← hq'e, ← Cat.assoc, hi₂, Cat.id_comp]
  let iHom : PairHom C K := ⟨i, hicompat⟩
  exact ⟨iHom, PairHom.ext (by show n.g ≫ i = _; exact hi₁),
              PairHom.ext (by show i ≫ n.g = _; exact hi₂)⟩

/-- **§1.547 — `pairForget` REFLECTS covers under the target-subset condition (the converse half).**
    If the underlying arrow `m.g` is an `A`-cover, AND every `Â`-arrow `n : K ↪ Y` factoring `m`
    (via some `Â`-arrow `t`) has BOTH an `A`-mono underlying arrow `n.g` AND its domain targets
    `K° ⊆ Y°`, then `m` is an `Â`-cover.  Combined with the forward
    `pairCover_pi2_underlying_of_underlying_pullback` (which gives `Cover c.π₂.g` from an `A`-pullback
    underlying cone), this is the converse half of "`pairForget` preserves covers": the test arrow's
    `A`-mono `n.g` factors the `A`-cover `m.g` (`t.g ≫ n.g = m.g`), so `m.g`-as-cover forces `n.g` an
    `A`-iso, and the target-subset condition lets `pairForget_reflects_iso_of_targets_subset` promote
    it to an `Â`-iso.

    The TWO hypotheses are exactly the §1.547 slice-equivalence content: for an UNCONSTRAINED `Â`,
    neither "`Â`-mono ⟹ `A`-mono underlying" (`pairForget` faithful ≠ mono-preserving) NOR `K° ⊆ Y°`
    holds for a free test arrow — this is obstruction (2) of `pairPullbacksTransferCovers`, here
    isolated as explicit hypotheses so the cover-reflection mechanism is recorded Sorry-free. -/
theorem pairCover_of_underlying_cover_targets [HasPullbacks 𝒞] {X Y : PairObj 𝒞} {m : PairHom X Y}
    (hg : Cover m.g)
    (hmono : ∀ {K : PairObj 𝒞} (n : PairHom K Y), @Monic (PairObj 𝒞) _ K Y n → Monic n.g)
    (htgt : ∀ {K : PairObj 𝒞} (n : PairHom K Y), @Monic (PairObj 𝒞) _ K Y n →
              ∀ T ∈ K.targets, T ∈ Y.targets) :
    @Cover (PairObj 𝒞) _ X Y m := by
  intro K n t hn htn
  -- `n.g` is `A`-monic (hmono); `t.g ≫ n.g = m.g`; `m.g`-cover forces `n.g` an `A`-iso.
  have htng : t.g ≫ n.g = m.g := congrArg PairHom.g htn
  have hng : IsIso n.g := hg n.g t.g (hmono n hn) htng
  exact pairForget_reflects_iso_of_targets_subset n hng (htgt n hn)

/-- **§1.547 — the base `∏(X.targets)` of the slice is WELL-SUPPORTED.**  Every factor target of
    `X` is well-supported (`X.wsupp`), and a finite product of well-supported objects is
    well-supported (`wellSupported_listProd'`).  Hence the slice `A/(∏ X.targets)` lives over a
    well-supported base — exactly the §1.547 requirement that puts `pairSliceObj X` in a
    pre-regular, point-acquiring slice. -/
theorem pairSlice_base_wellSupported [HasPullbacks 𝒞] [HasEqualizers 𝒞] [DecidableEq 𝒞]
    [PullbacksTransferCovers 𝒞] (X : PairObj 𝒞) :
    WellSupported (listProd X.targets) :=
  wellSupported_listProd' (by
    intro B hB
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hB
    exact X.wsupp p hp)

/-- **§1.547 — the slice over `pairSliceObj X`'s base acquires a point of every factor.**  Directly
    `listProdSliceAcquiresEveryFactor` at `X.targets`: for each positional factor index `k`, the
    slice `A/(∏ X.targets)` (where `pairSliceObj X` lives) carries a global point
    `1 → sliceEmbedObj (∏ X.targets) (X.targets.get k)`.  Together with `pairSlice_base_wellSupported`
    (the base is well-supported, so the slice is pre-regular and the point exists) this is the
    per-object §1.547 structure: every object of `Â` determines a slice that points all its factors. -/
theorem pairSlice_points_every_factor [HasPullbacks 𝒞] (X : PairObj 𝒞)
    (k : Fin X.targets.length) :
    (sliceFactorPoint (X.targets.get k) (listProdProj X.targets k)).f
        ≫ (sliceEmbedObj (listProd X.targets) (X.targets.get k)).hom
      = (overTerm (listProd X.targets)).hom :=
  listProdSliceAcquiresEveryFactor X.targets k

end FactorSlice

/-! ## §1.547  The relative-capitalization statement and the points-everything payoff

  The rational category `A[denseMonos⁻¹]` is §1.547's `A*` (up to the equivalence with the
  directed union of product-slices, which §1.547 records as the *verification*, not the
  construction).  The §1.547 payoff is:

      `StepWellPointsStatement` — for every well-supported `A` of `S`, `loc A` is
      `WellPointed` in the rational category.

  The mathematical heart (§1.547, last paragraph): a proper subobject `B' ↪ loc A`
  pulls back to a proper subobject at some finite stage `A/(∏U)` with `A ∈ U`, where the
  slice carries the generic point `1 → loc A` (`sliceFactorPoint`/`listProdSliceAcquires
  EveryFactor`, RelativeCapitalization.lean) that the subobject misses — "AB' ↪ AB does
  not allow the generic point in A/B".  The generic-point ingredients are Sorry-free; the
  residual is the descent of an arbitrary rational-category subobject to a finite stage and
  the missed-point extraction, isolated below. -/

section WellPointed
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]

/-- **§1.547 — the generic point of factor `A` in the product-slice `A/(∏U)`.**  This is the
    point the §1.547 rational step adds for the well-supported target `A` reached from the
    base `∏U` by the projection `g : ∏U → A`: the over-arrow `1 → sliceEmbedObj (∏U) A` whose
    underlying arrow is `pair g id`.  Read off `sliceFactorPoint`/`listProdSliceAcquiresEvery
    Factor` (RelativeCapitalization.lean), which are Sorry-free.  Restated here as the
    rational-category-level "global point of `loc A`": in the directed-union model of
    `A[𝒟⁻¹]`, the slice `A/(∏U)` IS the stage `A*|U`, its terminator `overTerm (∏U)` is the
    `1` of that stage, and this is a genuine point `1 → A` at that stage. -/
theorem slice_factor_point_acquired {P : 𝒞} (A : 𝒞) (g : P ⟶ A) :
    (sliceFactorPoint A g).f ≫ (sliceEmbedObj P A).hom = (overTerm P).hom :=
  sliceAcquiresFactorPoint A g

/-- **§1.547 core — `A/(∏U)` points every factor (the one-step payoff).**  For each factor
    `A = U.get k` of a finite set `U` of well-supported objects, the single product-slice
    `A/(∏U)` carries a global point `1 → sliceEmbedObj (∏U) A` (`sliceFactorPoint` along the
    projection `listProdProj U k`).  Iterated over `U`, one rung points all of `U` at once —
    the structural reason the §1.547 relative capitalization needs only ω iterations (each
    rational step `A ⊆ A*` points every well-supported object simultaneously).  Sorry-free;
    this is `listProdSliceAcquiresEveryFactor` re-exposed as the rational-step payoff. -/
theorem ratStep_points_every_factor (U : List 𝒞) (k : Fin U.length) :
    (sliceFactorPoint (U.get k) (listProdProj U k)).f
        ≫ (sliceEmbedObj (listProd U) (U.get k)).hom = (overTerm (listProd U)).hom :=
  listProdSliceAcquiresEveryFactor U k

/-! ### §1.547 — the descent reduction for the factor-slice well-pointedness

  These helpers carry out the *elementary, Sorry-free* half of the §1.546/547 missed-point
  argument: the reduction of "the generic point `sliceFactorPoint A g` lifts through a slice
  mono `m : D ↪ ⟨A×P, snd⟩`" to a purely downstairs statement about the underlying `𝒞`-arrow
  `m.f`.  What is genuinely missing (the residual `Sorry` on `sliceEmbed_factor_wellPointed`) is
  the book's §1.546 point-selection: a *proper* `m` misses *some* global point.  NOTE the naive
  "every proper `m` misses the GENERIC point" is FALSE (`graph_satisfies_hyps`); everything
  reducing the slice statement to the downstairs statement is closed here. -/

/-- **§1.547 — the lift of the generic point unfolds to a downstairs section of `m.f`.**
    In the slice `Over P`, a lift `y : overTerm P ⟶ D` of the point `sliceFactorPoint A g`
    through a slice morphism `m : D ⟶ sliceEmbedObj P A` exists *iff* the underlying arrow
    `m.f : D.dom → A × P` admits a downstairs map `s : P → D.dom` with `s ≫ m.f = pair g id`.
    (The over-triangle condition on `y` is then automatic: `s ≫ D.hom = s ≫ m.f ≫ snd =
    pair g id ≫ snd = id`, using `m.w` and `(sliceEmbedObj P A).hom = snd`.)  Sorry-free —
    this is the bookkeeping that turns the slice well-pointedness goal into the genuine
    downstairs §1.546 statement. -/
theorem sliceFactorPoint_lift_iff {P A : 𝒞} {D : Over P}
    (m : D ⟶ sliceEmbedObj P A) (g : P ⟶ A) :
    (∃ y : overTerm P ⟶ D, y ≫ m = sliceFactorPoint A g)
      ↔ ∃ s : P ⟶ D.dom, s ≫ m.f = pair g (Cat.id P) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.f, congrArg OverHom.f hy⟩
  · rintro ⟨s, hs⟩
    -- the over-triangle `s ≫ D.hom = id` follows from `m.w` and `snd_pair`.
    have hDhom : m.f ≫ snd = D.hom := m.w
    have hsw : s ≫ D.hom = Cat.id P := by
      rw [← hDhom, ← Cat.assoc, hs, snd_pair]
    exact ⟨⟨s, hsw⟩, OverHom.ext hs⟩

/-! ### §1.546 — the product-form escape (the true core of the missed-point argument)

  Freyd's §1.546 statement is precise: for a *proper* `B' ↪ B` (here `i : B' ↪ P`, the base
  of the slice), the PRODUCT-FORM subobject `AB' ↪ AB` (`id_A × i`) "does not allow the generic
  point" — and in fact does not allow *any* `g`-point `sliceFactorPoint A g`.  This is the
  high-value standalone core; it needs only pair/projection algebra + `split_epi_cover`/
  `monic_cover_iso` (a split epi which is monic is iso).

  The underlying arrow of the product-form slice mono is `id_A × i = pair fst (snd ≫ i) :
  A × B' → A × P`, with slice domain `⟨A × B', snd ≫ i⟩` over `P` (`(id_A × i) ≫ snd = snd ≫ i`).
  A section of it over a `g`-point would force `i` split epi, hence (mono) iso — contradicting
  properness. -/

/-- **The product-form slice mono `id_A × i : ⟨A×B', snd≫i⟩ ↪ ⟨A×P, snd⟩`.**  Underlying arrow
    `pair fst (snd ≫ i)`; it is an `OverHom` into `sliceEmbedObj P A` because its second projection
    is `snd ≫ i = (the domain structure map)`.  Monic in the slice because its underlying arrow is
    monic (`i` monic ⟹ `snd ≫ i`… in fact `pair fst (snd ≫ i)` is split-monic via `pair fst (snd ≫
    i) ≫ pair fst snd`-style retract; we record monicity directly from joint-monicity of fst/snd). -/
def prodFormMono {A P B' : 𝒞} (i : B' ⟶ P) :
    OverHom (⟨prod A B', snd ≫ i⟩ : Over P) (sliceEmbedObj P A) :=
  ⟨pair fst (snd ≫ i), by
    show pair (fst : prod A B' ⟶ A) (snd ≫ i) ≫ snd = snd ≫ i
    exact snd_pair _ _⟩

/-- **§1.546 product-form escape.**  For a *proper* monic `i : B' ↪ P` of the base, the
    product-form subobject `id_A × i` of `sliceEmbedObj P A` is missed by EVERY `g`-point
    `sliceFactorPoint A g` (`g : P → A`).  A section `s` over the `g`-point would give
    `s ≫ snd : P → B'` a section of `i` (`(s ≫ snd) ≫ i = id_P`), making `i` a split epi; being
    monic, `i` would be iso (`monic_cover_iso` via `split_epi_cover`) — contradicting properness.
    This is the core of "AB' ↪ AB does not allow the generic point" (§1.546). -/
theorem prodFormMono_misses_point {A P B' : 𝒞} (i : B' ⟶ P)
    (hi_mono : Monic i) (hi_proper : ¬ IsIso i) (g : P ⟶ A) :
    ¬ ∃ s : P ⟶ prod A B', s ≫ (prodFormMono (A := A) i).f = pair g (Cat.id P) := by
  rintro ⟨s, hs⟩
  -- `s ≫ snd` is a section of `i`: compose `hs` with `snd`.
  have hsec : (s ≫ snd) ≫ i = Cat.id P := by
    have : s ≫ pair (fst : prod A B' ⟶ A) (snd ≫ i) ≫ snd = pair g (Cat.id P) ≫ snd := by
      rw [← Cat.assoc]; exact congrArg (· ≫ snd) hs
    rw [snd_pair, snd_pair] at this
    rw [Cat.assoc]; exact this
  -- `i` has a right inverse `s ≫ snd` and is monic ⟹ `i` iso, contradicting properness.
  -- monic `i` cancels `(i ≫ (s≫snd)) ≫ i = i ≫ ((s≫snd) ≫ i) = i ≫ id = i = id ≫ i`.
  have hleft : i ≫ (s ≫ snd) = Cat.id B' := by
    apply hi_mono
    rw [Cat.assoc, hsec, Cat.comp_id, Cat.id_comp]
  exact hi_proper ⟨s ≫ snd, hleft, hsec⟩

/-- **§1.546 product-form escape, slice form.**  The product-form mono `prodFormMono i` (for a
    proper base monic `i : B' ↪ P`) misses the slice point `sliceFactorPoint A g` in `Over P`, for
    every `g : P → A`.  This is `prodFormMono_misses_point` lifted through `sliceFactorPoint_lift_iff`
    — the slice-level "AB' ↪ AB does not allow the generic point". -/
theorem prodFormMono_misses_slicePoint {A P B' : 𝒞} (i : B' ⟶ P)
    (hi_mono : Monic i) (hi_proper : ¬ IsIso i) (g : P ⟶ A) :
    ¬ ∃ y : overTerm P ⟶ (⟨prod A B', snd ≫ i⟩ : Over P),
        y ≫ prodFormMono (A := A) i = sliceFactorPoint A g := by
  rw [sliceFactorPoint_lift_iff (prodFormMono (A := A) i) g]
  exact prodFormMono_misses_point i hi_mono hi_proper g

/-- **§1.546 — the product-form mono is monic in the slice when `i` is.**  Its underlying arrow
    `pair fst (snd ≫ i)` is monic — `fst` and `snd ≫ i` are jointly monic since `fst, snd` are
    jointly monic and `i` is monic (`snd ≫ i` cancels through `i`); slice monicity then follows by
    `sigma_reflects_mono`.  (Properness of `id_A × i` would need `A` well-supported and is not
    needed below: the escape `prodFormMono_misses_point` already holds for any `g`.) -/
theorem prodFormMono_mono {A P B' : 𝒞} (i : B' ⟶ P) (hi_mono : Monic i) :
    OverMono (prodFormMono (A := A) i) := by
  have hf_mono : Monic (pair (fst : prod A B' ⟶ A) (snd ≫ i)) := by
    intro W u v huv
    have h1 : u ≫ fst = v ≫ fst := by
      have e : (u ≫ pair (fst : prod A B' ⟶ A) (snd ≫ i)) ≫ fst
             = (v ≫ pair (fst : prod A B' ⟶ A) (snd ≫ i)) ≫ fst := by rw [huv]
      rwa [Cat.assoc, Cat.assoc, fst_pair] at e
    have h2 : (u ≫ snd) ≫ i = (v ≫ snd) ≫ i := by
      have e : (u ≫ pair (fst : prod A B' ⟶ A) (snd ≫ i)) ≫ snd
             = (v ≫ pair (fst : prod A B' ⟶ A) (snd ≫ i)) ≫ snd := by rw [huv]
      rwa [Cat.assoc, Cat.assoc, snd_pair, ← Cat.assoc, ← Cat.assoc] at e
    exact fst_snd_jointly_monic u v h1 (hi_mono _ _ h2)
  intro W u v huv
  exact OverHom.ext (hf_mono u.f v.f (congrArg OverHom.f huv))

/-- **§1.547 — exact "reach" characterization of a missed g-point (Sorry-free).**  In `Over P`,
    a slice mono `m : D ↪ sliceEmbedObj P A`, the global points are the g-points `sliceFactorPoint
    A g` (`g : P → A`).  `m` MISSES `sliceFactorPoint A g` iff `g` is *not reachable*: there is no
    section `s : P → D.dom` of the structure map `D.hom` with `s ≫ (m.f ≫ fst) = g`.  (A lift of the
    g-point is a `𝒞`-section `s` with `s ≫ m.f = pair g id`; equating `fst`/`snd` legs, that is
    exactly `s ≫ D.hom = id` and `s ≫ m.f ≫ fst = g`, since `m.f ≫ snd = D.hom`.)  So `m` misses
    *some* g-point iff the "reach set" `{s ≫ m.f ≫ fst | s ≫ D.hom = id}` is a *proper* subset of
    `Hom(P, A)` — the precise downstairs §1.546 content, with no slice bookkeeping left. -/
theorem sliceMiss_iff_g_unreachable {P A : 𝒞} {D : Over P}
    (m : D ⟶ sliceEmbedObj P A) (g : P ⟶ A) :
    (¬ ∃ y : overTerm P ⟶ D, y ≫ m = sliceFactorPoint A g)
      ↔ ¬ ∃ s : P ⟶ D.dom, s ≫ D.hom = Cat.id P ∧ s ≫ (m.f ≫ fst) = g := by
  rw [sliceFactorPoint_lift_iff m g]
  have hmw : m.f ≫ snd = D.hom := m.w
  constructor
  · intro h ⟨s, hsw, hsp⟩
    exact h ⟨s, by
      -- `s ≫ m.f = pair g id`: legs `fst` give `g`, `snd` gives `id` (via `m.w`).
      refine pair_uniq _ _ _ ?_ ?_
      · rw [Cat.assoc]; exact hsp
      · rw [Cat.assoc, hmw]; exact hsw⟩
  · intro h ⟨s, hs⟩
    refine h ⟨s, ?_, ?_⟩
    · have : s ≫ m.f ≫ snd = pair g (Cat.id P) ≫ snd := by rw [← Cat.assoc, hs]
      rw [hmw, snd_pair] at this; exact this
    · have : s ≫ m.f ≫ fst = pair g (Cat.id P) ≫ fst := by rw [← Cat.assoc, hs]
      rw [fst_pair] at this; exact this

/- (DEAD route — documents the commented-out `sliceEmbed_factor_wellPointed` below.)
   **§1.547 — `WellPointed` of the embedded factor (the full payoff; honest residual).**
    In the product-slice `A/(∏U)` (with `A = U.get k` a well-supported factor), the embedded
    object `sliceEmbedObj (∏U) A` is `WellPointed`: every proper monic into it misses some
    global point.  Stated with the slice's genuine `HasTerminal` (`overHasTerminal (∏U)`) — NO
    `Sorry` in the type, so this is the book's real `WellPointed`.

    STATUS.  The high-value §1.546 CORE is now Sorry-free and standalone:
    `prodFormMono_misses_point` / `prodFormMono_misses_slicePoint` — for a proper base monic
    `i : B' ↪ P`, the product-form subobject `id_A × i` is missed by EVERY g-point (a section over
    a g-point forces `i` split-epi hence (mono) iso).  And `sliceMiss_iff_g_unreachable` reduces
    "`m` misses some g-point" to the precise downstairs reach statement (no slice bookkeeping left).

    RESIDUAL (`Sorry` on this TRUE statement) — the §1.546/547 REDUCTION.  Given an *arbitrary*
    proper slice mono `m : D ↪ ⟨A×∏U, snd⟩` (`m.f = pair p q`, `q = D.hom`, `p = m.f ≫ fst`),
    by `sliceMiss_iff_g_unreachable` the goal is: some `g : ∏U → A` is *unreachable*, i.e. no
    section `s` of `q` has `s ≫ p = g`.  The naive "the GENERIC point escapes" is FALSE
    (`graph_satisfies_hyps`: the graph `⟨∏U,id⟩`, `m.f = pair (proj_k) id`, reaches the generic
    point via `s = id`) — but that same graph is missed by any OTHER g-point, illustrating that the
    escaper must be chosen per `m`.  In **Set** the statement is exactly true (reaching every `g`
    ⟺ `image m ⊇` every graph ⟺ `m` surjective ⟺ (mono) iso), so the theorem is TRUE; but the
    categorical proof that "every g reached ⟹ `m.f` iso" is NOT elementary in the *plain* slice:
    the family `{pair g id}_{g:P→A}` is jointly epic only against the `snd = id` part of `A×∏U`, so
    no joint-cover argument closes it directly (`prod_fst_cover`/`prod_snd_cover` give only that
    `snd : A×∏U → ∏U` is a cover, insufficient to lift an arbitrary `b : T → ∏U` to a section).
    Freyd's actual reduction forces `m` into PRODUCT FORM using the rational-LOCALIZATION structure
    (§1.547: objects `(A,F)`, dense monos), where surviving subobjects are exactly the product-form
    `AB' ↪ AB` that `prodFormMono_misses_point` then escapes — that localization-level reduction is
    the genuine missing content and lives above the plain slice. The §1.544 strict cancellation in
    the repo (`Inflation.strict_cancel`) is list-cons injectivity on the inflation index, NOT a
    `𝒞`-level `B×A ≅ B×A' ⟹ A ≅ A'`, so it does not by itself drive the reduction. -/
-- DEAD (§1.547 PairObj route): unreachable from `capData_exists` (the cofinal route proves well-pointing
-- via `FibreDensity`/`stepWellPoints_of_fibreDensity`).  Carried a genuine `Sorry`; commented out to keep
-- the build Sorry-free.
/-
theorem sliceEmbed_factor_wellPointed (U : List 𝒞)
    (hU : ∀ x ∈ U, WellSupported x) (k : Fin U.length) :
    @WellPointed (Over (listProd U)) _ (overHasTerminal (listProd U))
      (sliceEmbedObj (listProd U) (U.get k)) := by
  Sorry  -- (commented-out dead decl)
-/

/-- **The over-general `genericPoint_escapes_proper` is FALSE — explicit witness.**
    The "graph of the generic point", `D := ⟨∏U, id⟩` with slice arrow
    `m.f := pair (proj_k) id : ∏U → (U.get k)×∏U`, is a *proper monic* slice subobject
    of `sliceEmbedObj (∏U) (U.get k)` that DOES admit the generic point (section `s = id`).
    This lemma (axiom-free, `Sorry`-free) exhibits exactly that: `m` is monic in `Over (∏U)`
    and `s := id` satisfies `s ≫ m.f = pair (proj_k) id`.  `m` is iso *iff* `pair (proj_k) id`
    is iso, i.e. iff `(U.get k) ≅ 1` — false for a generic well-supported factor.  Hence the
    universally-quantified "no proper monic allows the generic point" is refuted: Freyd's §1.546
    claim is specifically about subobjects of the FORM `AB' ↪ AB` (product monics `id_A × (B'↪B)`),
    NOT arbitrary slice monics.  See the note on `genericPoint_escapes_proper`. -/
theorem graph_satisfies_hyps (U : List 𝒞) (k : Fin U.length) :
    ∃ (m : (⟨listProd U, Cat.id (listProd U)⟩ : Over (listProd U))
            ⟶ sliceEmbedObj (listProd U) (U.get k)),
        m.f = pair (listProdProj U k) (Cat.id (listProd U)) ∧ Monic m ∧
        (∃ s : listProd U ⟶ listProd U,
          s ≫ m.f = pair (listProdProj U k) (Cat.id (listProd U))) := by
  have hw : pair (listProdProj U k) (Cat.id (listProd U))
      ≫ (sliceEmbedObj (listProd U) (U.get k)).hom = Cat.id (listProd U) := snd_pair _ _
  have hidmono : Monic (Cat.id (listProd U)) := by
    intro W a b heq; rw [← Cat.comp_id a, ← Cat.comp_id b, heq]
  have hmf : Monic (pair (listProdProj U k) (Cat.id (listProd U))) :=
    monic_pair_of_monic _ (Cat.id (listProd U)) hidmono
  refine ⟨⟨pair (listProdProj U k) (Cat.id (listProd U)), hw⟩, rfl,
    sigma_reflects_mono (B := listProd U) ⟨_, hw⟩ hmf, ⟨Cat.id (listProd U), ?_⟩⟩
  show Cat.id (listProd U) ≫ pair (listProdProj U k) (Cat.id (listProd U))
      = pair (listProdProj U k) (Cat.id (listProd U))
  rw [Cat.id_comp]

end WellPointed

end Freyd

#print axioms Freyd.listProdAppendInv_projL
#print axioms Freyd.listProdAppendInv_projR
