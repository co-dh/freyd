/-
  Freyd & Scedrov, *Categories and Allegories* §1.541/§1.542/§1.544/§1.545
  RELATIVE CAPITALIZATION — the genuine core of the capitalization successor step.

  This file builds the *slice rung* of Freyd's relative capitalization `A ⊆ A*`
  (§1.544/§1.545) as an honest `CapStep` (the successor interface of
  `Capitalization.lean`), for a *single* well-supported object `B`:

      A  →  A/B          ( C ↦ (C×B → B),  f ↦ (f×B) )

  The book (§1.544) writes this embedding as `A ↦ A×B` and shows it "separates
  objects and, if `B` is well-supported, separates morphisms."  The slice `A/B`
  is pre-regular (`overPreRegular`, SliceRegular.lean), the embedding is faithful
  (`slice_embedding_separates`, S1_54.lean — repackaged here as a faithful functor
  *into `Over B`*), so it packages as a `CapStep A`.

  WHAT THIS FILE DELIVERS (all Sorry-free):
    * `sliceEmbedObj` / `sliceEmbedMap` / `sliceEmbedFunctor`
                            — the functor `A → A/B`, `C ↦ ⟨C×B, snd⟩`, `f ↦ f×B`
    * `sliceEmbedFaithful`  — it is FAITHFUL when `B` is well-supported
                              (embedding from `slice_embedding_separates`;
                               reflects-iso from `f×B` iso ⟹ `f` mono+cover ⟹ iso)
    * (§1.545 rung `A → A/B` is the faithful pre-regular extension above; the `CapStep`
       the ω-tower iterates is the §1.547 colimit `nextStepOfEnum`, not a single slice)
    * `sliceAcquiresPoint`  — `A/B` ACQUIRES A POINT of `sliceEmbed B B`: the
                               terminator-to-image diagonal `⟨diag B, …⟩ : 1 → B×B`
                               is a point of `sliceEmbedObj B B`.  This is §1.546's
                               "generic point" `1 → A(B)` for the chosen `B`.
    * `sliceFactorPoint` / `sliceAcquiresFactorPoint`
                            — §1.547 generalization: along ANY `g : P → B`, the slice
                               `A/P` acquires a point of `sliceEmbedObj P B`
                               (underlying arrow `pair g id_P`).  With `P = ∏U`,
                               `g = projection`, this is the point the product-slice
                               rung adds for a factor `B ∈ U`.
    * `prodSliceAcquiresBothFactors`
                            — the two-factor crux: the SINGLE slice `A/(B×B')` points
                               BOTH factors at once, so one rung over `∏U` points every
                               member of `U` simultaneously.
    * `listProd` / `listProdProj` / `listSubset` / `listDirected`
                            — the §1.547 FINITE-SET INDEX (mathlib-free): finite sets of
                               objects modelled as `List 𝒞`, `⊆`-ordered into a `Directed`
                               (bound = `++`); `∏U` = right-folded binary product (`∏[]=1`);
                               `listProdProj U k : ∏U → U.get k` the factor projection
                               (`Fin`-indexed — a `Prop`-membership `B ∈ U` cannot large-
                               eliminate into a morphism).
    * `listProdSliceAcquiresEveryFactor`
                            — the §1.547 payoff: `A/(∏U)` acquires a point of EVERY factor
                               `U.get k` at once (one rung points all of `U`).

  STATUS: §1.543 is now PROVEN Sorry-free (`Freyd.capitalization_lemma`, in
  `Freyd/CapDataWiring.lean`).  The uniform successor was ultimately built by the
  COFINAL (object-indexed) route — `uniformStep` (`Freyd/UniformCapStep.lean`) over the
  `cofinalProjSystem` (`Freyd/CofinalProjSystem.lean`), using `Classical.decEq` — NOT by
  closing the `innerCatSystem` route this header explored.  The discussion below is the
  historical exploration of the per-`B` slice rung that this file delivers (Sorry-free) and
  feeds into that solution; the "residual wall" / "STILL OPEN" framing it uses is superseded.

  THE GENUINE STRENGTHENING (recorded for context).
  The *uniform* successor `nextStep : ∀ S, CapStep S` is
  STRONGER than a single slice rung: in ONE category `S*` it must add a point for
  *every* well-supported `B` simultaneously (Freyd's §1.547 rational category / the
  directed union of the `A* | U = A/(∏U)` product-slices over finite sets `U` of
  well-supported objects).  This file delivers the per-`B`/per-factor points AND the
  finite-set index (`listDirected`/`listProd`/`listProdProj`/`listProdSliceAcquiresEveryFactor`)
  Sorry-free (above).

  INNER-SYSTEM SCAFFOLDING (this session, all Sorry-free — see the `innerCatSystem` block):
    * the TRANSITION FUNCTOR now EXISTS: `baseChangeFunctor (g : C ⟶ D) : Functor (Over D → Over C)`
      (SliceRegular.lean), the genuine slice→slice base-change `A/(∏V) → A/(∏U)` by pullback along
      `∏U → ∏V` — NOT the slice embedding (which is `A → A/B`, base→one-slice).
    * `innerObj U = Over (listProd U)`, `innerCat`, `innerF P h = baseChangeObj (P.proj h)`,
      `innerFunctF P h = baseChangeFunctor (P.proj h)` — the inner system's object family, `Cat`
      instances, transition object map and per-rung functoriality.
    * `innerCatSystem P hS : CatSystem (List 𝒞) listDirected` — the inner system, GIVEN its two
      residuals as honest inputs (no false `Sorry`):
        (A) `P : ListProjFamily` — a choice-free product projection `∏U ⟶ ∏V` per `V ⊆ U` with
            strict unit/composition.  NOT yet constructible: `listSubset V U` is a `Prop`, so a
            positional factor-match needs `DecidableEq 𝒞` (the same `Prop`-no-large-elim wall that
            forced `listProdProj` to be `Fin`-indexed).
        (B-strict) `hS : StrictBaseChange P` — the on-the-nose `F_refl`/`F_trans`.  RAW base-change
            is only PSEUDO-functorial (`baseChangeObj (Cat.id) X = X×_D D`, iso to `X` but NOT equal),
            so these are FALSE for raw base-change and are declared as a hypothesis (a real theorem to
            prove = base-change strictification), never asserted by `Sorry`.

  ROUTE-1 (strict reindexing) INVESTIGATION — settled NEGATIVELY for §1.547, see the
  `strictReindexSystem` block + `Freyd.reindexFunctor` (SliceRegular.lean):
    * the STRICT transition EXISTS — `reindexFunctor m` (Σ / post-composition along `m : C → D`) is
      strictly functorial AND `reindexObj_id`/`reindexObj_comp` give `CatSystem.F_refl`/`F_trans` ON
      THE NOSE (Sorry-free, axiom-free).  `strictReindexSystem R` is a genuine `CatSystem` with those
      laws as THEOREMS, no `StrictBaseChange` needed.
    * but it is the WRONG transition for §1.547: variance `A/(∏V) → A/(∏U)` needs base map `∏V → ∏U`
      (Σ-direction), not choice-free for `V ⊆ U` (would manufacture the missing factors' points); and
      Σ keeps the slice DOMAIN fixed (`B×∏V`), so it cannot connect the stage embeddings whose domain
      must GROW to `B×∏U`.  Only base-change (pullback) grows the domain — hence pseudo-functorial.
      Strictness and the growing-product embedding are mutually exclusive; route 1 does not close
      `hwall_step`.
  (This `innerCatSystem` route was NOT the one taken to close `S*`.  The actual uniform
  successor is the cofinal `uniformStep` / `cofinalProjSystem` route — see the STATUS note
  above — which sidesteps both the (B-package) coherence/preservation obligations for
  `innerCatSystem` and the (B-import) cycle, by living downstream in
  `Freyd/CapDataWiring.lean`.  §1.543 is proven there.)

  No mathlib (the category theory stays on this repo's own `Cat`).
-/

import Freyd.S1_10
import Freyd.S1_26
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_54
import Freyd.S1_56
import Freyd.S1_53_SliceRegular
import Freyd.S1_543_Capitalization

open Freyd
open Freyd.Colim

universe u

namespace Freyd

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]

/-! ## §1.544  The slice embedding `A → A/B` as a functor

  Object part: `C ↦ ⟨C×B, snd⟩` — the product `C×B` viewed as an object over `B`
  via the second projection.  Morphism part: `f : C → D` maps to `f×B = pair (fst≫f) snd`,
  which is an `OverHom` because `pair (fst≫f) snd ≫ snd = snd` (`snd_pair`).

  The underlying `𝒞`-arrow of `(sliceEmbed B).map f` is exactly `(prodRightFunctor B).map f`,
  so all functor laws and faithfulness reduce to the already-proven `prodRightFunctor` /
  `slice_embedding_separates`. -/

/-- The object part of the slice embedding `A → A/B`: `C ↦ (C×B ──snd──▶ B)`. -/
def sliceEmbedObj (B : 𝒞) (C : 𝒞) : Over B := ⟨prod C B, snd⟩

/-- The morphism part of the slice embedding: `f : C → D` becomes the over-hom whose
    underlying arrow is `f×B = pair (fst≫f) snd : C×B → D×B`.  It commutes with the
    structure map `snd` by `snd_pair`. -/
def sliceEmbedMap (B : 𝒞) {C D : 𝒞} (f : C ⟶ D) :
    OverHom (sliceEmbedObj B C) (sliceEmbedObj B D) :=
  ⟨pair (fst ≫ f) snd, snd_pair (fst ≫ f) snd⟩

/-- The underlying arrow of `sliceEmbedMap B f` is `(prodRightFunctor B).map f` — the
    bridge to the already-proven product-embedding facts of §1.544. -/
theorem sliceEmbedMap_f (B : 𝒞) {C D : 𝒞} (f : C ⟶ D) :
    (sliceEmbedMap B f).f = (prodRightFunctor B).map f := rfl

/-- The slice embedding `A → A/B` is a functor.  Underlying arrows are `prodRightFunctor B`'s,
    so the laws transport along `OverHom.ext` (a slice equation is its underlying equation). -/
def sliceEmbedFunctor (B : 𝒞) : Functor 𝒞 (Over B) where
  obj := sliceEmbedObj B
  map f := sliceEmbedMap B f
  map_id C := OverHom.ext (by
    show (sliceEmbedMap B (Cat.id C)).f = (Cat.id (sliceEmbedObj B C)).f
    rw [sliceEmbedMap_f, (prodRightFunctor B).map_id]; rfl)
  map_comp {C D E} f g := OverHom.ext (by
    show (sliceEmbedMap B (f ≫ g)).f = ((sliceEmbedMap B f) ⊚ (sliceEmbedMap B g)).f
    rw [sliceEmbedMap_f, (prodRightFunctor B).map_comp]; rfl)

/-- The slice embedding's `.map` agrees (underlying-arrow) with `prodRightFunctor`. -/
theorem sliceEmbedFunctor_map_f (B : 𝒞) {C D : 𝒞} (f : C ⟶ D) :
    ((sliceEmbedFunctor B).map f).f = (prodRightFunctor B).map f := rfl

/-! ### Faithfulness of the slice embedding (§1.544)

  Embedding: equality of slice-images gives equality of underlying `f×B`, which
  `slice_embedding_separates` (cover-cancellation of `fst`, needs `B` well-supported)
  turns into `f = g`.

  Reflects-iso: from `f×B` iso we get `f` *mono* (image `f×B` mono, then the embedding
  + functoriality descend monicity to `f`) and `f` a *cover* (`fst_C ≫ f = (f×B) ≫ fst_D`
  is iso∘cover hence a cover, and a cover right-factor is a cover); `monic_cover_iso`
  then makes `f` iso. -/

/-- The slice embedding separates morphisms (the embedding half of faithfulness), for
    well-supported `B`.  This is `slice_embedding_separates` read through the underlying-arrow
    identification `sliceEmbedFunctor_map_f`. -/
theorem sliceEmbed_embedding (B : 𝒞) [PullbacksTransferCovers 𝒞] (hws : WellSupported B) :
    @Embedding 𝒞 _ (Over B) _ (sliceEmbedFunctor B) := by
  intro C D f g h
  exact slice_embedding_separates B hws f g (congrArg OverHom.f h)

/-- **Cover right-factor.**  If `g ≫ f` is a cover then `f` is a cover.  (Any monic `m`
    that `f` factors through, `g ≫ f` also factors through; `g ≫ f` a cover forces `m` iso.) -/
theorem cover_of_comp_cover {X Y Z : 𝒞} (g : X ⟶ Y) (f : Y ⟶ Z) (hgf : Cover (g ≫ f)) :
    Cover f := by
  intro C m h hm hfac
  refine hgf m (g ≫ h) hm ?_
  rw [Cat.assoc, hfac]

/-- **§1.544 — the slice embedding is FAITHFUL** for well-supported `B`. -/
theorem sliceEmbedFaithful (B : 𝒞) [PullbacksTransferCovers 𝒞] (hws : WellSupported B) :
    @Faithful 𝒞 _ (Over B) _ (sliceEmbedFunctor B) := by
  refine ⟨sliceEmbed_embedding B hws, ?_⟩
  intro C D f hiso
  -- the underlying arrow `f×B : C×B → D×B` is iso in `𝒞`
  have hfBiso : IsIso ((sliceEmbedFunctor B).map f).f := overIso_underlying hiso
  rw [sliceEmbedFunctor_map_f] at hfBiso
  -- `f×B` mono (from its inverse as a retraction)
  obtain ⟨inv, hinv1, _hinv2⟩ := hfBiso
  have hfBmono : Monic ((prodRightFunctor B).map f) := mono_of_retraction _ inv hinv1
  -- `f` mono: descend monicity through the embedding functor.
  have hfmono : Monic f := by
    intro Z u v huv
    -- functoriality: `(u≫f)×B = (v≫f)×B`, i.e. `(u×B)≫(f×B) = (v×B)≫(f×B)`
    have h1 : (prodRightFunctor B).map (u ≫ f) = (prodRightFunctor B).map (v ≫ f) := by
      rw [huv]
    rw [(prodRightFunctor B).map_comp, (prodRightFunctor B).map_comp] at h1
    -- cancel the mono `f×B`, then use that the embedding separates `(-)×B`.
    have h2 : (prodRightFunctor B).map u = (prodRightFunctor B).map v := hfBmono _ _ h1
    exact slice_embedding_separates B hws u v h2
  -- `f` cover: `fst_C ≫ f = (f×B) ≫ fst_D`, iso∘cover = cover, right-factor is cover.
  have hfcover : Cover f := by
    have hstep : (fst : prod C B ⟶ C) ≫ f = (prodRightFunctor B).map f ≫ (fst : prod D B ⟶ D) :=
      (fst_pair ((fst : prod C B ⟶ C) ≫ f) snd).symm
    have hcov : Cover ((fst : prod C B ⟶ C) ≫ f) := by
      rw [hstep]
      exact cover_precomp_iso ⟨inv, hinv1, _hinv2⟩ (prod_fst_cover hws)
    -- right-factor of a cover is a cover (inlined to avoid an implicit-binder elaboration quirk):
    intro K m h hm hfac
    exact hcov m ((fst : prod C B ⟶ C) ≫ h) hm (by rw [Cat.assoc, hfac])
  exact monic_cover_iso f hfcover hfmono

/-! ## §1.545  The slice rung as a faithful pre-regular extension

  `A → A/B` is one rung of Freyd's relative capitalization — a faithful pre-regular extension
  of `A`: target `A/B` (pre-regular by `overPreRegular`), functor `sliceEmbedFunctor`, faithful
  by `sliceEmbedFaithful`.  (A `CapStep`-packaged form is no longer materialised here: `CapStep`
  now additionally carries the five limit- and cover-preservation fields the ω-tower consumes, and the
  successor the tower actually iterates is the §1.547 enumeration colimit `nextStepOfEnum` — into
  `A/(∏U)` over a chain of finite factor-sets — not a single slice `A/B`.  The §1.545 content used
  downstream is exactly `sliceEmbedFaithful`/`overPreRegular`/`sliceAcquiresPoint`.) -/

/-! ## §1.546  The slice rung acquires the generic point of `B`

  In `A/B`, the terminator is `overTerm B = ⟨B, id_B⟩` (S1_44).  Freyd's "generic point"
  of `A(B) = sliceEmbedObj B B = ⟨B×B, snd⟩` is the slice-arrow `1 → A(B)` whose underlying
  `𝒞`-arrow is the diagonal `diag B : B → B×B` (`diag B ≫ snd = id_B` makes it an over-hom
  from the terminator).  This is the point that §1.546's relative capitalization adds for `B`. -/

/-- The **generic point** of `sliceEmbedObj B B` in `A/B`: the over-arrow from the terminator
    `⟨B, id_B⟩` whose underlying arrow is the diagonal `diag B : B → B×B`.  It is an `OverHom`
    because `diag B ≫ snd = id_B` (the second projection of the diagonal is the identity). -/
def sliceGenericPoint (B : 𝒞) :
    OverHom (overTerm B) (sliceEmbedObj B B) :=
  ⟨diag B, by show diag B ≫ snd = Cat.id B; exact snd_pair _ _⟩

/-- **§1.546 — `A/B` acquires a point of `A(B)`.**  `sliceGenericPoint B` is a point
    `1 → sliceEmbedObj B B` in `A/B` (its source is the terminator `overTerm B`, which is the
    `1` of `A/B`).  This is the generic point Freyd's relative capitalization adds for the
    chosen well-supported `B`. -/
theorem sliceAcquiresPoint (B : 𝒞) :
    (sliceGenericPoint B).f ≫ (sliceEmbedObj B B).hom = (overTerm B).hom := by
  show diag B ≫ snd = Cat.id B
  exact snd_pair _ _

/-! ## §1.547  Product slices acquire a point of every factor

  Freyd's choice-free relative capitalization (§1.547) is the directed union of the
  slices `A* | U = A / (∏ U)` over finite sets `U` of well-supported objects, with the
  transition `A/(∏V) → A/(∏U)` (for `V ⊆ U`) being the slice embedding.  The point that
  the rung over `U` must add for a *factor* `B ∈ U` is read off the slice over the product:
  the projection `g : ∏U → B` is a map to a well-supported target, and `A/(∏U)` acquires a
  point of `sliceEmbedObj (∏U) B` along `g`.  The two-factor case `∏U = B × B'` below is the
  crux: ONE slice (over the product) simultaneously points BOTH factors, which is exactly why
  the finite-product directed union pins down a point per well-supported object at once.

  This generalizes `sliceGenericPoint`/`sliceAcquiresPoint` (the `B = ∏U` self-point case)
  to an arbitrary projection `g : ∏U → B`.  Below, `g` is any map into a (well-supported)
  target `B` from the base `P = ∏U`; the point's underlying arrow is `pair g (Cat.id P)`. -/

/-- **Generic point of a factor in a product slice (§1.547).**  For any base `P` and any
    map `g : P → B`, the slice `A/P` acquires a point of `sliceEmbedObj P B = ⟨B × P, snd⟩`:
    the over-arrow from the terminator `⟨P, id_P⟩` whose underlying `𝒞`-arrow is
    `pair g (id_P) : P → B × P`.  It is an `OverHom` because its second projection is `id_P`
    (`snd_pair`).  Taking `g = fst : B × B' → B` points the factor `B` of `B × B'`; taking
    `P = B`, `g = id_B` recovers `sliceGenericPoint B` (the diagonal). -/
def sliceFactorPoint {P : 𝒞} (B : 𝒞) (g : P ⟶ B) :
    OverHom (overTerm P) (sliceEmbedObj P B) :=
  ⟨pair g (Cat.id P), by show pair g (Cat.id P) ≫ snd = Cat.id P; exact snd_pair g (Cat.id P)⟩

/-- **§1.547 — `A/P` acquires a point of `sliceEmbedObj P B` along `g : P → B`.**
    `sliceFactorPoint B g` is a point `1 → sliceEmbedObj P B` in `A/P` (source = the
    terminator `overTerm P`).  This is the generic point the product-slice rung adds for the
    well-supported target `B` reached from the base `P` by `g`. -/
theorem sliceAcquiresFactorPoint {P : 𝒞} (B : 𝒞) (g : P ⟶ B) :
    (sliceFactorPoint B g).f ≫ (sliceEmbedObj P B).hom = (overTerm P).hom := by
  show pair g (Cat.id P) ≫ snd = Cat.id P
  exact snd_pair g (Cat.id P)

/-- **Both factors of a binary product slice are pointed (§1.547, two-factor crux).**
    The single slice `A/(B × B')` acquires, from its own base, a point of the factor `B`
    (along `fst`) AND a point of the factor `B'` (along `snd`).  This is the elementary fact
    behind "the slice over the *product* of `U` points every member of `U` simultaneously":
    iterating it over a finite `U` (its product carries a projection to each member) gives one
    rung that points all of `U` at once, the content of the directed-union construction. -/
theorem prodSliceAcquiresBothFactors (B B' : 𝒞) :
    (sliceFactorPoint B (fst : prod B B' ⟶ B)).f ≫ (sliceEmbedObj (prod B B') B).hom
        = (overTerm (prod B B')).hom
      ∧ (sliceFactorPoint B' (snd : prod B B' ⟶ B')).f ≫ (sliceEmbedObj (prod B B') B').hom
        = (overTerm (prod B B')).hom :=
  ⟨sliceAcquiresFactorPoint B (fst : prod B B' ⟶ B),
   sliceAcquiresFactorPoint B' (snd : prod B B' ⟶ B')⟩

/-! ## §1.547  The finite-set index and the product over a finite set

  Freyd's choice-free relative capitalization (§1.547) is the directed union of the slices
  `A* | U = A/(∏U)` over *finite sets* `U` of (well-supported) objects, with transition
  `A/(∏V) → A/(∏U)` for `V ⊆ U`.  The repo is mathlib-free, so we model a "finite set of
  objects" as a `List 𝒞` and the order `V ⊆ U` as list-membership inclusion.  This is a
  genuine `Directed` index (`bound` = append), and `∏U` is the right-folded binary product
  of the members of `U` (with `∏[] = 1`, the terminator).  These are the concrete, reusable
  ingredients of the inner directed system; everything below is Sorry-free. -/

-- `listProd`/`listProd_nil`/`listProd_cons` now live upstream in `Freyd.SliceRegular`
-- (imported above) so that `Freyd.Inflation` can use them without importing `Capitalization`.

/-- The projection `∏U → B` for the factor at a positional index `k : Fin U.length` (so
    `B = U.get k`).  Positional indexing (rather than a `Prop`-valued membership `B ∈ U`) is
    forced: `B ∈ U` lives in `Prop`, so a *morphism* `∏U → B` cannot be extracted from it by
    recursion (large elimination of a `Prop` into `Type` is barred).  `Fin`-indexing carries
    the data: head index projects by `fst`; a successor index projects by `snd` then recurses.
    This is the map `g : ∏U → U.get k` along which the slice `A/(∏U)` acquires a point of that
    factor (`sliceFactorPoint`/`sliceAcquiresFactorPoint`). -/
def listProdProj : ∀ (U : List 𝒞) (k : Fin U.length), (listProd U ⟶ U.get k)
  | C :: U, ⟨0,     _⟩ => (fst : prod C (listProd U) ⟶ C)
  | C :: U, ⟨k + 1, hk⟩ =>
      (snd : prod C (listProd U) ⟶ listProd U) ≫ listProdProj U ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- The list-subset order: `V ⊆ U` means every member of `V` is a member of `U`. -/
def listSubset (V U : List 𝒞) : Prop := ∀ x ∈ V, x ∈ U

/-- **The finite-set index is `Directed`** (subset order, `bound` = append).  This is the
    inner directed system's index (§1.547): finite sets of objects ordered by inclusion. -/
def listDirected : Directed (List 𝒞) where
  le := listSubset
  refl _ _ h := h
  trans hVU hUW x hx := hUW x (hVU x hx)
  bound V U := ⟨V ++ U, fun _ hx => List.mem_append.2 (Or.inl hx),
    fun _ hx => List.mem_append.2 (Or.inr hx)⟩

/-- **§1.547 — the product-slice `A/(∏U)` acquires a point of EVERY factor.**  For each
    positional index `k`, `sliceFactorPoint (U.get k) (listProdProj U k)` is a point
    `1 → sliceEmbedObj (∏U) (U.get k)` in `A/(∏U)`: the slice over the product of `U` points
    every member of `U` simultaneously (one rung pins a point per element of `U`).  This is the
    uniform §1.547 payoff of the index above, a direct instance of `sliceAcquiresFactorPoint`
    along the projection `listProdProj`.  Sorry-free. -/
theorem listProdSliceAcquiresEveryFactor (U : List 𝒞) (k : Fin U.length) :
    (sliceFactorPoint (U.get k) (listProdProj U k)).f
        ≫ (sliceEmbedObj (listProd U) (U.get k)).hom
      = (overTerm (listProd U)).hom :=
  sliceAcquiresFactorPoint (U.get k) (listProdProj U k)

/-! ## §1.546 — the directed-union escape: base-change to a FRESH factor misses its point

  The genuine §1.546 density content, isolated as a single Sorry-free SLICE lemma.

  Freyd's §1.546: a proper subobject of the embedded object `AB ↪ B` is, at a RICHER slice, missed
  by a point.  At a single fixed slice this is FALSE (`properMono_forces_graph_iso`,
  SliceEquivalence): the graph `pair (proj_k) id` of the generic slice point is a proper mono
  reaching every fixed-slice point.  The escape is the directed union: pass to a richer base
  `P' = A × P` carrying a FRESH, independent `A`-coordinate `c : P' → A` (the new projection), and
  base-change the subobject along the projection `q : P' → P`.  The base-changed subobject's
  `A`-value is the OLD subobject's `A`-value pulled back through `P`, so it is DECOUPLED from the
  fresh coordinate `c`; reaching the fresh point `sliceFactorPoint A c` would force the old
  subobject to contain its whole graph, i.e. force the proper mono to be a cover — contradiction.

  This is the precise, point-free reason the directed UNION (not a single slice) closes §1.546, and
  it needs NO fractions-saturation: only the two base-change pullback squares and joint-monicity of
  `(fst, snd)`.  The lemma is stated against the explicit pullback cones so it is reusable for any
  base map `q` and any fresh coordinate `c` with `c`'s `P`-shadow factoring as `q`. -/

/-- **§1.546 base-change escape (the genuine directed-union escape, Sorry-free).**  Let
    `m : D ↪ sliceEmbedObj P A` be a PROPER slice mono (`D.dom ↪ A×P` with structure `snd`).
    Base-change along the SECOND PROJECTION `q := snd : A×P ⟶ P` (so the richer base is `P' = A×P`,
    carrying the FRESH `A`-coordinate `fst : A×P ⟶ A`).  Suppose:

      * `cnD : Cone D.hom (snd : prod A P ⟶ P)` is a pullback (the base-change of `D`);
      * `mf' : cnD.pt ⟶ prod A (prod A P)` is the induced map on the base-changed embedded apex —
        we take that apex to be the canonical `A × (A×P)` product cone of the cospan
        `(snd, snd)`, with legs `fst`, `snd`.  So `mf'` satisfies
        `mf' ≫ fst = cnD.π₁ ≫ m.f ≫ fst` (the `A`-leg of `D ↪ A×P`) and `mf' ≫ snd = cnD.π₂`
        (the base leg, landing in `A×P = P'`).

    Then there is NO section `s : (prod A P) ⟶ cnD.pt` of the base-change structure map `cnD.π₂`
    (`s ≫ cnD.π₂ = id`) whose `A`-coordinate is the FRESH coordinate `fst`
    (`s ≫ mf' ≫ fst = fst`).  For such a section makes `(s ≫ cnD.π₁) : A×P → D.dom` a SECTION of
    `m.f` (`(s ≫ cnD.π₁) ≫ m.f = pair fst snd = id_{A×P}`), so `m.f` is split-epi hence a cover;
    being monic (`m` mono), `m.f` is then iso, so `m` is a slice-iso — contradicting properness.

    This is the precise point-free directed-union escape; no fractions saturation is used. -/
theorem baseChange_freshFactor_missed {P A : 𝒞} {D : Over P}
    (m : OverHom D (sliceEmbedObj P A)) (hmono : OverMono m) (hproper : ¬ OverIso m)
    (cnD : Cone D.hom (snd : prod A P ⟶ P)) (_hcnD : cnD.IsPullback)
    (mf' : cnD.pt ⟶ prod A (prod A P))
    (hmf'₁ : mf' ≫ (fst : prod A (prod A P) ⟶ A) = cnD.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A))
    (_hmf'₂ : mf' ≫ (snd : prod A (prod A P) ⟶ prod A P) = cnD.π₂)
    (s : (prod A P) ⟶ cnD.pt) (hs₂ : s ≫ cnD.π₂ = Cat.id (prod A P))
    (hsA : s ≫ (mf' ≫ (fst : prod A (prod A P) ⟶ A)) = (fst : prod A P ⟶ A)) : False := by
  -- `D.hom = m.f ≫ snd` (the over-hom law, since `(sliceEmbedObj P A).hom = snd`).
  have hmw : m.f ≫ (snd : prod A P ⟶ P) = D.hom := m.w
  -- `t := s ≫ cnD.π₁ : A×P → D.dom`.  Show `t ≫ m.f = id_{A×P}` via joint-monicity of `(fst, snd)`.
  -- `A`-leg: `s ≫ cnD.π₁ ≫ m.f ≫ fst = s ≫ mf' ≫ fst = fst`.
  have hAleg : s ≫ cnD.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A) = (fst : prod A P ⟶ A) := by
    rw [← hmf'₁]; rw [← Cat.assoc] at hsA ⊢; exact hsA
  -- `P`-leg: `s ≫ cnD.π₁ ≫ m.f ≫ snd = s ≫ cnD.π₁ ≫ D.hom = s ≫ cnD.π₂ ≫ snd = snd`.
  have hPleg : s ≫ cnD.π₁ ≫ m.f ≫ (snd : prod A P ⟶ P) = (snd : prod A P ⟶ P) := by
    rw [hmw, cnD.w, ← Cat.assoc s, hs₂, Cat.id_comp]
  -- hence `t ≫ m.f = pair fst snd = id_{A×P}`.
  have htmf : (s ≫ cnD.π₁) ≫ m.f = Cat.id (prod A P) := by
    have hpair : (s ≫ cnD.π₁) ≫ m.f = pair (fst : prod A P ⟶ A) (snd : prod A P ⟶ P) :=
      pair_uniq _ _ _
        (by rw [Cat.assoc, Cat.assoc]; exact hAleg)
        (by rw [Cat.assoc, Cat.assoc]; exact hPleg)
    rw [hpair, pair_fst_snd]
  -- `m.f` is split-epi (right inverse `s ≫ cnD.π₁`), hence a cover; monic ⟹ iso ⟹ `m` slice-iso.
  have hfmono : Monic m.f := sigma_preserves_mono m hmono
  have hcover : Cover m.f := by
    intro K n h hn hfac
    -- `n` mono, `h ≫ n = m.f`; the right inverse of `n` is `(s ≫ cnD.π₁) ≫ h`.
    have hni : ((s ≫ cnD.π₁) ≫ h) ≫ n = Cat.id (prod A P) := by
      rw [Cat.assoc, hfac, htmf]
    refine ⟨(s ≫ cnD.π₁) ≫ h, ?_, hni⟩
    -- `n ≫ ((s≫cnD.π₁)≫h) = id`: cancel `n` mono on `(… ≫ n) = (id ≫ n)`.
    apply hn
    rw [Cat.assoc, hni]; rw [Cat.id_comp]; exact Cat.comp_id n
  have hfiso : IsIso m.f := monic_cover_iso m.f hcover hfmono
  exact hproper (overIso_of_underlying m hfiso)

/-- **§1.546 base-change escape — POINT-FACTORIZATION form (Sorry-free, axiom-free).**  The same
    §1.546 directed-union escape as `baseChange_freshFactor_missed`, but stated to consume a
    *point factorization* directly: at the richer base `P' = A×P` (the fresh `A`-coordinate is
    `fst : A×P ⟶ A`), if the FRESH slice point `sliceFactorPoint A (fst : A×P ⟶ A)` factors through
    a PROPER slice mono `m̄ : D̄ ↪ sliceEmbedObj (A×P) A` whose domain `D̄` is the base-change of the
    proper mono `m : D ↪ sliceEmbedObj P A` along `snd : A×P ⟶ P`, then `False`.

    Concretely the hypotheses present the base-change by its pullback cone `cnD` of `D.hom` along
    `snd` (so `D̄.dom = cnD.pt`, `D̄.hom = cnD.π₂`) and the embedded-apex comparison `m̄.f = mf'` with
    `mf' ≫ fst = cnD.π₁ ≫ m.f ≫ fst`, `mf' ≫ snd = cnD.π₂` — exactly the data
    `baseChange_freshFactor_missed` consumes.  A point factorization `t ⊚ m̄ = sliceFactorPoint A fst`
    yields its underlying `t.f : A×P ⟶ cnD.pt` AS the missing section: `t.f ≫ cnD.π₂ = id` (it is a
    point over `A×P`, the over-hom law `t.w`) reaching the fresh coordinate
    `t.f ≫ mf' ≫ fst = fst` (the underlying `A`-leg of `t ⊚ m̄ = sliceFactorPoint A fst`).  Then
    `baseChange_freshFactor_missed` refutes it.

    This is the reusable consumer of a POINT factorization (an `OverHom` equation), the shape a
    slice-point density argument actually produces, rather than the raw cone arrows; the section
    extraction is internal here. -/
theorem freshSlicePoint_factors_imp_false {P A : 𝒞} {D : Over P}
    (m : OverHom D (sliceEmbedObj P A)) (hmono : OverMono m) (hproper : ¬ OverIso m)
    (cnD : Cone D.hom (snd : prod A P ⟶ P)) (hcnD : cnD.IsPullback)
    -- the base-changed mono `m̄ : ⟨cnD.pt, cnD.π₂⟩ ↪ sliceEmbedObj (A×P) A`, underlying `mf'`.
    (mf' : cnD.pt ⟶ prod A (prod A P))
    (hmf'₁ : mf' ≫ (fst : prod A (prod A P) ⟶ A) = cnD.π₁ ≫ m.f ≫ (fst : prod A P ⟶ A))
    (hmf'₂ : mf' ≫ (snd : prod A (prod A P) ⟶ prod A P) = cnD.π₂)
    (mbar : OverHom (⟨cnD.pt, cnD.π₂⟩ : Over (prod A P)) (sliceEmbedObj (prod A P) A))
    (hmbar : mbar.f = mf')
    -- the FRESH slice point factors through `m̄`.
    (t : OverHom (overTerm (prod A P)) (⟨cnD.pt, cnD.π₂⟩ : Over (prod A P)))
    (hfac : t ⊚ mbar = sliceFactorPoint A (fst : prod A P ⟶ A)) : False := by
  -- the underlying point-factorization arrow: `t.f ≫ mbar.f = (sliceFactorPoint A fst).f = pair fst id`.
  have hfacf : t.f ≫ mbar.f = pair (fst : prod A P ⟶ A) (Cat.id (prod A P)) :=
    congrArg OverHom.f hfac
  -- `t.f : A×P ⟶ cnD.pt` is a section of `cnD.π₂` (the over-hom law `t.w`, since `D̄.hom = cnD.π₂`).
  have hs₂ : t.f ≫ cnD.π₂ = Cat.id (prod A P) := t.w
  -- and it reaches the fresh coordinate `fst`: `t.f ≫ (mf' ≫ fst) = (t.f ≫ mbar.f) ≫ fst = fst`.
  have hsA : t.f ≫ (mf' ≫ (fst : prod A (prod A P) ⟶ A)) = (fst : prod A P ⟶ A) := by
    rw [← hmbar, ← Cat.assoc, hfacf, fst_pair]
  exact baseChange_freshFactor_missed m hmono hproper cnD hcnD mf' hmf'₁ hmf'₂ t.f hs₂ hsA

/-- **§1.546 fresh-section read-off (the consumer-facing half of the descent).**  The §1.546 escape
    consumer `freshSlicePoint_factors_imp_false` needs, at base `A×PN`, an arrow
    `q : A×PN ⟶ Dbar.dom` with `q ≫ Dbar.hom = snd` (a section of the base-change structure map) whose
    fresh `A`-coordinate is `fst` (`q ≫ mC.f ≫ fst = fst`).  This lemma BUILDS that `q` from the more
    primitive datum produced by the lax-colimit descent: a section `s : A×PN ⟶ cnDN.pt` of the
    base-change pullback `cnDN` (chosen pullback of `Dbar.hom` along `snd : A×PN ⟶ PN`) that is a
    point over `A×PN` (`s ≫ cnDN.π₂ = id`) reaching the fresh coordinate
    (`s ≫ cnDN.π₁ ≫ mC.f ≫ fst = fst`).  The witness is `q := s ≫ cnDN.π₁`: the structure leg uses the
    pullback square `cnDN.w` (`cnDN.π₁ ≫ Dbar.hom = cnDN.π₂ ≫ snd`) and `s ≫ cnDN.π₂ = id`; the fresh
    leg is `hsA` verbatim.  This isolates the EASY half of the §1.546 descent so the read-off is a
    standalone, small-context lemma; the genuine §1.546 content (producing the section `s` itself,
    transported from the stage-`N` colimit factor through the descent iso and the `ψ`-reindex) is the
    remaining core. -/
theorem freshSection_of_descentSection {PN A : 𝒞} (Dbar : Over PN)
    (mC : OverHom Dbar (sliceEmbedObj PN A))
    (cnDN : Cone Dbar.hom (snd : prod A PN ⟶ PN)) (_hcnDN : cnDN.IsPullback)
    (s : prod A PN ⟶ cnDN.pt) (hs₂ : s ≫ cnDN.π₂ = Cat.id (prod A PN))
    (hsA : s ≫ cnDN.π₁ ≫ mC.f ≫ (fst : prod A PN ⟶ A) = (fst : prod A PN ⟶ A)) :
    ∃ q : prod A PN ⟶ Dbar.dom,
      q ≫ Dbar.hom = (snd : prod A PN ⟶ PN) ∧
        q ≫ mC.f ≫ (fst : prod A PN ⟶ A) = (fst : prod A PN ⟶ A) := by
  refine ⟨s ≫ cnDN.π₁, ?_, ?_⟩
  · rw [Cat.assoc, cnDN.w, ← Cat.assoc, hs₂, Cat.id_comp]
  · rw [Cat.assoc]; exact hsA

/-! ## §1.547  Assembling the inner finite-product-slice `CatSystem` (residual (A)/(B))

  This block builds the inner directed system of slices `A/(∏U)` over `listDirected`, the
  one `hwall_step` (Capitalization.lean) consumes.  The OBJECTS (`Over (listProd U)`), the
  INDEX (`listDirected`), and the per-rung POINTS (`listProdSliceAcquiresEveryFactor`) are all
  in hand Sorry-free above.  Two concrete primitives remain, isolated here as the interface
  `ListProjFamily` (and an `import` obstruction that keeps the assembly in *this* file rather
  than in `Capitalization.lean`):

  ════ residual (A) — the choice-free TRANSITION BASE MORPHISM ════
  The transition `A/(∏V) → A/(∏U)` for `V ⊆ U` is BASE-CHANGE (`baseChangeObj`/`baseChangeFunctor`,
  SliceRegular.lean) along a product projection `listProd U ⟶ listProd V`.  That projection is
  NOT constructible choice-free over the present index: `listSubset V U` is `∀ x ∈ V, x ∈ U`, a
  `Prop`, so a *positional* match "factor `k` of `V` = factor `?` of `U`" cannot be extracted
  without `DecidableEq 𝒞` (object equality) — exactly the same `Prop`-can't-large-eliminate wall
  that forced `listProdProj` to be `Fin`-indexed rather than `(B ∈ U)`-indexed.  The honest
  abstraction is therefore to take the projection family as DATA (`ListProjFamily` below); the
  genuine missing primitive is one constructive instance of it.

  ════ residual (B-strict) — base-change is only PSEUDO-functorial ════
  `CatSystem.F_refl`/`F_trans` demand ON-THE-NOSE equalities `F (refl) X = X` and
  `F (trans) X = F hjk (F hij X)`.  Base-change along `1` is `X ×_D D → D`, equal to `X` only up
  to iso, and base-change along a composite re-associates pullbacks — both hold only up to
  canonical iso, never definitionally (probed: `baseChangeObj (Cat.id D) X = X` does not reduce).
  The outer ω-tower sidestepped this by transporting via `transN` (literal iterated composition,
  strictly functorial).  The inner system needs the same strictification of base-change (or a
  strictly-functorial replacement transition), which is a standalone construction.

  ════ residual (B-import) — the assembly cannot live in `Capitalization.lean` ════
  `RelativeCapitalization` imports `Capitalization` (for `CapStep`), so the ingredients
  `listDirected`/`baseChangeFunctor`/`listProd`/`listProdSliceAcquiresEveryFactor` are visible
  ONLY here, downstream of `hwall_step`.  Discharging it in place would require moving
  the inner-system ingredients up into a file that `Capitalization` imports (e.g. `SliceRegular`),
  or relocating `capData_exists` down here.

  RESOLUTION (since written): the relocation route was taken — `capData_exists` lives downstream
  in `Freyd/CapDataWiring.lean`, and residual (A) was discharged by accepting `Classical.decEq`
  for the positional projection (the §1.543 exception, `Freyd/CofinalProjSystem.lean`).  §1.543 is
  now PROVEN Sorry-free; this block records the obstructions of the *abandoned* in-place route. -/

/-- **The transition base-morphism family (residual (A), as data).**  A choice-free assignment,
    for every inclusion `V ⊆ U` of finite object-sets, of a product projection
    `listProd U ⟶ listProd V` (the bigger product projects onto the smaller), STRICTLY coherent:
    the identity inclusion gives `Cat.id`, and a composite inclusion gives the composite
    projection.  This is exactly the data missing from residual (A); one constructive instance of
    it (needing `DecidableEq 𝒞` or a positional refinement of the index) closes residual (A).

    Given such a family, the inner system's transition is `baseChangeFunctor (proj h)`; its strict
    coherence laws are residual (B-strict) — base-change is only pseudo-functorial, so even with a
    strict `ListProjFamily` the `CatSystem.F_refl`/`F_trans` need base-change strictification. -/
structure ListProjFamily where
  /-- the product projection `∏U → ∏V` for each `V ⊆ U`. -/
  proj : ∀ {V U : List 𝒞}, listSubset V U → (listProd U ⟶ listProd V)
  /-- strict unit: the projection along the reflexive inclusion is the identity. -/
  proj_refl : ∀ (U : List 𝒞), proj (listDirected.refl U) = Cat.id (listProd U)
  /-- strict composition: the projection along a composite inclusion is the composite. -/
  proj_trans : ∀ {V U W : List 𝒞} (hVU : listSubset V U) (hUW : listSubset U W),
    proj (listDirected.trans hVU hUW) = proj hUW ≫ proj hVU

/-- **The inner finite-product-slice object map.**  Stage `U` of the inner system is the slice
    `A/(∏U) = Over (listProd U)`.  This is residual-(A)/(B)-free (it is just the object family). -/
def innerObj (U : List 𝒞) : Type u := Over (listProd U)

instance innerCat (U : List 𝒞) : Cat.{u} (innerObj (𝒞 := 𝒞) U) := overCat (listProd U)

/-- **The inner transition functor**, *given* a projection family `P` (residual (A)): for `V ⊆ U`,
    base-change `A/(∏V) → A/(∏U)` along `P.proj : ∏U → ∏V`.  The OBJECT map is `baseChangeObj`,
    the functoriality (in the slice variable) is `baseChangeFunctor` — both Sorry-free.  What is
    NOT yet available (residual (B-strict)) are the `CatSystem`-level strict laws `F_refl`/`F_trans`
    relating different inclusions, because base-change is only pseudo-functorial in the base. -/
def innerF (P : ListProjFamily (𝒞 := 𝒞)) {V U : List 𝒞} (h : listSubset V U) :
    innerObj (𝒞 := 𝒞) V → innerObj (𝒞 := 𝒞) U :=
  baseChangeObj (P.proj h)

/-- The inner transition is a functor in the slice variable (base-change functoriality).  This is
    Sorry-free — it is exactly `baseChangeFunctor` along `P.proj h`. -/
def innerFunctF (P : ListProjFamily (𝒞 := 𝒞)) {V U : List 𝒞} (h : listSubset V U) :
    @Functor (innerObj (𝒞 := 𝒞) V) (innerObj (𝒞 := 𝒞) U) (innerCat V) (innerCat U) :=
  baseChangeFunctor (P.proj h)

/-- **The strict-functoriality obligation for the inner transition (residual (B-strict)), AS A
    HYPOTHESIS — NOT asserted.**  A `CatSystem` demands the transitions be functorial *on the nose*:
    `F_refl : F (refl) X = X` and `F_trans : F (trans) X = F hjk (F hij X)`.  For RAW base-change
    these equations are **false** (`baseChangeObj (Cat.id (∏U)) X = X ×_{∏U} ∏U → ∏U`, canonically
    iso to `X` but NOT equal; the composite re-associates the iterated pullback).  We therefore
    DECLARE the strict laws as a hypothesis bundle rather than discharge them with a false `Sorry`:
    a witness of `StrictBaseChange P` is exactly the base-change strictification (or a strictly
    functorial replacement transition) needed before `innerObj`/`innerF` form a `CatSystem`.

    This is residual (B-strict) stated honestly: providing `StrictBaseChange P` is a real theorem
    (it does NOT hold for raw base-change), so there is no false-statement-with-`Sorry` here. -/
structure StrictBaseChange (P : ListProjFamily (𝒞 := 𝒞)) : Prop where
  F_refl : ∀ {U : List 𝒞} (X : innerObj (𝒞 := 𝒞) U), innerF P (listDirected.refl U) X = X
  F_trans : ∀ {V U W : List 𝒞} (hVU : listSubset V U) (hUW : listSubset U W)
    (X : innerObj (𝒞 := 𝒞) V),
    innerF P (listDirected.trans hVU hUW) X = innerF P hUW (innerF P hVU X)

/-- **The inner `CatSystem` over `listDirected`, GIVEN the residuals as inputs.**  Objects
    `A/(∏U)`, transitions base-change along a projection family `P` (residual (A)), with the strict
    laws supplied by `hS : StrictBaseChange P` (residual (B-strict)).  Sorry-free: every field is a
    real construction or a fed-in hypothesis — no false equation is asserted.  Discharging the two
    inputs `P`/`hS` (one constructive `ListProjFamily`, one base-change strictification) plus the 9
    `colimitPreRegular` preservation hypotheses and `Coherent` (residual (B-package), mirroring the
    OUTER `towerSystem`/`towerCoherent`/`capData_of_tower`) closes the inner construction.

    ROUTE-1 NOTE (see the `strictReindexSystem` block below).  `hS : StrictBaseChange P` is a GENUINE
    obligation — base-change is irreducibly pseudo-functorial.  The natural strict alternative (Σ /
    post-composition, `strictReindexSystem`) discharges the strict `F_refl`/`F_trans` on the nose but
    runs the WRONG variance and keeps the slice domain fixed, so it cannot carry §1.547's growing
    embedding.  Hence `StrictBaseChange` cannot be replaced by route-1 reindexing; it stays. -/
noncomputable def innerCatSystem (P : ListProjFamily (𝒞 := 𝒞)) (hS : StrictBaseChange P) :
    Colim.CatSystem (List 𝒞) listDirected where
  A := innerObj (𝒞 := 𝒞)
  catA := innerCat
  F := fun h => innerF P h
  Fmap := fun h => (innerFunctF P h).map
  Fmap_id := fun h => (innerFunctF P h).map_id
  Fmap_comp := fun h => (innerFunctF P h).map_comp
  F_refl := fun X => hS.F_refl X
  F_trans := fun hVU hUW X => hS.F_trans hVU hUW X

/-! ## ROUTE 1 — strict reindexing: the strict laws hold, but the variance is wrong

  Investigation of the §1.543 task "replace the pseudo-functorial base-change transition with a
  STRICTLY functorial one so `CatSystem.F_refl`/`F_trans` hold on the nose."

  RESULT (machine-checked, Sorry-free below).  The honest strict transition is the dependent-sum /
  post-composition functor `reindexFunctor` (SliceRegular.lean): along a FIXED base map `m : C ⟶ D`,
  `Σ_m : A/C → A/D`, `⟨X, x⟩ ↦ ⟨X, x ≫ m⟩`.  It is STRICTLY functorial and — unlike base-change —
  satisfies the `CatSystem` object laws DEFINITIONALLY:

    * `reindexObj_id   : reindexObj (Cat.id C) X = X`                           (strict `F_refl`)
    * `reindexObj_comp : reindexObj (m ≫ m') X = reindexObj m' (reindexObj m X)` (strict `F_trans`)

  both proven by `rfl`-level rewriting (`Cat.comp_id` / `Cat.assoc`).  So a `CatSystem` built on
  `reindexFunctor` needs NO `StrictBaseChange` hypothesis: `strictReindexSystem` below has its
  `F_refl`/`F_trans` as PROVEN theorems, not fed-in inputs.  This is the route-1 strict win, in hand.

  WHY ROUTE 1 NEVERTHELESS CANNOT CARRY §1.547 (the two-fold obstruction, both `rfl`-confirmed):

   (i) WRONG VARIANCE.  `reindexFunctor` runs `A/C → A/D` ALONG a base map `m : C → D`.  The §1.547
       directed transition is `A/(∏V) → A/(∏U)` for `V ⊆ U`, whose canonical, choice-free base map is
       the PROJECTION `listProdProj`-style `∏U → ∏V` (bigger product onto smaller) — pointing the
       WRONG way for Σ.  A Σ-usable `∏V → ∏U` would have to MANUFACTURE the extra factors of `U∖V`,
       i.e. supply points `1 → B` for the new well-supported `B`; choice-free, no such map exists
       (that is precisely the point the construction is trying to ADD, not assume).  Hence the strict
       family `ReindexFamily` (the Σ analogue of `ListProjFamily`) carries data `∏V ⟶ ∏U` that is NOT
       constructible — strictly worse than `ListProjFamily`'s `∏U ⟶ ∏V`, which at least IS a genuine
       projection (blocked only by `Prop`-no-large-elim / `DecidableEq 𝒞`).

  (ii) BREAKS THE EMBEDDING.  Even granting such a family, Σ keeps the DOMAIN fixed:
       `(reindexObj m (sliceEmbedObj (∏V) B)).dom = (∏V).dom`-shape `= prod B (listProd V)`, NEVER
       `prod B (listProd U)` (confirmed by `rfl`).  But the slice embedding at stage `U` is
       `sliceEmbedObj (∏U) B = ⟨B × ∏U, snd⟩`, whose domain GREW to `B × ∏U`.  The colimit must
       identify `objIncl V (embed B) = objIncl U (embed B)`, i.e. the transition must connect
       `⟨B×∏V, snd⟩` to `⟨B×∏U, snd⟩` — a domain CHANGE `B×∏V ↝ B×∏U`.  Only the pullback/base-change
       direction does this (`X ↦ X ×_{∏V} ∏U`); Σ cannot, since it never touches the domain.  This is
       the structural reason §1.547's directed union is the pullback (rational-category) construction,
       NOT a strict reindexing — and is exactly why Freyd phrases the `A*|U`-to-`A*|V` transitions as
       *equivalences of full subcategories of the rational category*, i.e. up-to-iso, never on the nose.

  CONCLUSION.  Route 1 produces a genuine, hypothesis-free strict `CatSystem` (`strictReindexSystem`)
  but on the WRONG variance and WITHOUT the embedding/point-acquisition §1.547 needs.  The base-change
  inner system (`innerCatSystem`) keeps the correct variance and embedding but is irreducibly
  pseudo-functorial (its `StrictBaseChange` is a real, non-trivial strictification obligation).  The
  two cannot be merged: strictness and the growing-product embedding pull in opposite directions.  So
  route-1 reindexing does NOT close the successor here; the way it WAS closed (now PROVEN Sorry-free,
  §1.543) is the rational-category route: a directed-union-of-full-subcategories model whose
  inclusions are up-to-iso, built as `uniformStep` over the cofinal `cofinalProjSystem`
  (`Freyd/UniformCapStep.lean`, `Freyd/CofinalProjSystem.lean`, `Freyd/CapDataWiring.lean`). -/

/-- **The strict reindexing transition base-map family (the Σ analogue of `ListProjFamily`).**  Data
    of a base map `∏V ⟶ ∏U` per inclusion `V ⊆ U`, strictly coherent.  NOTE the direction `∏V → ∏U`:
    this is what `Σ` (post-composition) requires, and is NOT choice-free constructible — a map
    `∏V → ∏U` for `V ⊆ U` must supply the missing factors `U∖V` (points `1 → B`), the very data the
    capitalization is meant to ADD.  Carried as a structure to make the obstruction explicit. -/
structure ReindexFamily where
  /-- the (non-constructible, choice-laden) base map `∏V → ∏U` for each `V ⊆ U`. -/
  base : ∀ {V U : List 𝒞}, listSubset V U → (listProd V ⟶ listProd U)
  /-- strict unit. -/
  base_refl : ∀ (U : List 𝒞), base (listDirected.refl U) = Cat.id (listProd U)
  /-- strict composition. -/
  base_trans : ∀ {V U W : List 𝒞} (hVU : listSubset V U) (hUW : listSubset U W),
    base (listDirected.trans hVU hUW) = base hVU ≫ base hUW

/-- **The strict reindexing inner object map.**  Stage `U` is the slice `A/(∏U) = Over (listProd U)`,
    same objects as `innerObj`; the transition will be Σ (post-composition), not base-change. -/
def reindexObjStage (R : ReindexFamily (𝒞 := 𝒞)) {V U : List 𝒞} (h : listSubset V U) :
    innerObj (𝒞 := 𝒞) V → innerObj (𝒞 := 𝒞) U :=
  reindexObj (R.base h)

/-- The strict reindexing transition is a functor — STRICTLY (it is `reindexFunctor`). -/
def reindexFunctStage (R : ReindexFamily (𝒞 := 𝒞)) {V U : List 𝒞} (h : listSubset V U) :
    @Functor (innerObj (𝒞 := 𝒞) V) (innerObj (𝒞 := 𝒞) U) (innerCat V) (innerCat U) :=
  reindexFunctor (R.base h)

/-- **The strict reindexing inner `CatSystem` — route 1, Sorry-free, NO strictness hypothesis.**
    Given a (route-1) base-map family `R`, the Σ-transition system over `listDirected` is a genuine
    `CatSystem` whose `F_refl`/`F_trans` are PROVEN — `reindexObj_id` and `reindexObj_comp` (modulo
    `R.base_refl`/`R.base_trans`), NOT supplied as `StrictBaseChange`-style hypotheses.  This is the
    concrete route-1 deliverable: strict laws ARE dischargeable on the nose for the reindexing
    transition.  Its limitation (wrong variance + fixed domain, so it does NOT carry the §1.547
    embedding/point-acquisition) is documented above and is why this route was abandoned in favour
    of the rational-category `uniformStep` that actually closes §1.543 (now proven). -/
def strictReindexSystem (R : ReindexFamily (𝒞 := 𝒞)) :
    Colim.CatSystem (List 𝒞) listDirected where
  A := innerObj (𝒞 := 𝒞)
  catA := innerCat
  F := fun {V U} h => reindexObjStage R h
  Fmap := fun {V U} h => (reindexFunctStage R h).map
  Fmap_id := fun {V U} h => (reindexFunctStage R h).map_id
  Fmap_comp := fun {V U} h => (reindexFunctStage R h).map_comp
  F_refl := fun {U} X => by
    show reindexObj (R.base (listDirected.refl U)) X = X
    rw [R.base_refl, reindexObj_id]
  F_trans := fun {V U W} hVU hUW X => by
    show reindexObj (R.base (listDirected.trans hVU hUW)) X
      = reindexObj (R.base hUW) (reindexObj (R.base hVU) X)
    rw [R.base_trans, reindexObj_comp]

/-! ## §1.546/§1.547  The uniform relative-capitalization successor `nextStep`

  This block assembles Freyd's relative-capitalization successor `S ↦ S*` as a single
  uniform `CapStep S` (the keystone the outer ω-tower iterates).  The pieces:

    * `wellSupported_one`/`wellSupported_prod`/`wellSupported_listProd` — `WellSupported (∏U)`
      whenever every member of the list `U` is well-supported.
    * The faithful BASE EMBEDDING `S → innerSliceObj ([] : Infl S)` — `X ↦ ⟨[X], term⟩`,
      `f ↦ inflFunctor.map f`.  Faithful because the inflation cross-section `infl`
      (`prodRight 1`) separates morphisms (`fst : X×1 → X` is a cover, `1` well-supported)
      and the slice over the terminal of `Infl S` forgets nothing (its hom is `term`).
    * The COFINAL ENUMERATION — Classical-well-order the well-supported objects of `S`
      and build the `take`-prefix `PrefixChain`, so each appended suffix is a list of
      well-supported objects, hence `hwsuf` (every appended `∏d` well-supported) holds and
      `chainSlicePreRegularWS` makes the inner colimit `S* = (chainSliceSystem P).Obj`
      a concrete `PreRegularCategory`.
    * `nextStep S : CapStep S.carrier` = ⟨S*, base-embed ≫ stage-0 inclusion, faithful⟩. -/

variable [PullbacksTransferCovers 𝒞]

/-! ### RELOCATED to `Freyd.Capitalization`

  `wellSupported_one`/`cover_comp'`/`wellSupported_prod`/`wellSupported_listProd`, the faithful base
  embedding `baseSliceObj`/`baseSliceMap`/`baseSliceFunctor`/`infl_separates`/`inflMap_reflects_iso`/
  `baseSliceFaithful`, the enumeration `enumPrefix`/`enumChain`/`enumChain_hwsuf`, and the successor
  `nextStepOfEnum`/`exists_wellSupported_enum`/`nextStep` itself now live UPSTREAM in
  `Freyd.Capitalization` (after `CapStep`, before `capData_exists`), so `capData_exists`/`hwall_step`
  can NAME the §1.546/§1.547 successor in place.  They are still in scope HERE via the `Capitalization`
  import (`open Freyd`), used by `enumChain_stage_acquires` below.  Pure relocation; no semantics changed. -/

section BaseSliceCartesian
variable [HasEqualizers 𝒞]

-- `innerSliceCartesianNil` (a `CartesianCategory (innerSliceObj [])` instance) used to live here;
-- it is now `innerSliceCartesianNilLoc` upstream in `S1_543_Capitalization` (in scope via the
-- `Capitalization` import above), so the duplicate local copy was removed (unused by name, an
-- `instance` found only via typeclass search — the upstream one already resolves it).

-- `baseCartesian𝒞` (a `CartesianCategory 𝒞` instance) used to live here; it is the same instance as
-- `baseCartesianSelfLoc` upstream in `S1_543_Capitalization`, which already resolves it — same
-- situation as `innerSliceCartesianNil` above.

end BaseSliceCartesian

/-! ### The §1.547 point-acquisition payoff `enumChain_stage_acquires`

  The enumeration `PrefixChain` infrastructure (`enumPrefix`/`enumPrefix_succ`/`enumChain`/
  `enumPrefix_suffix_mem`/`enumChain_hwsuf`) now lives UPSTREAM in `Freyd.Capitalization` (in scope
  here via the import).  Below is the §1.546 point-acquisition payoff, which needs the per-factor
  slice points (`sliceFactorPoint`/`listProdSliceAcquiresEveryFactor`) defined ONLY in this file. -/

/-- **§1.547 point acquisition at the chain stage.**  The stage-`(n+1)` slice of the enumeration
    chain, `innerSliceObj (enumPrefix enum (n+1)) = Over (∏[enum 0,…,enum n])`, acquires a point of
    the factor `enum n` (the freshly-appended object): the over-arrow `sliceFactorPoint (enum n)
    (listProdProj …)` from the terminator, whose composite with the slice structure map is the
    terminator's (`sliceAcquiresFactorPoint`).  This is the §1.546 generic point the chain adds for
    `enum n`, read off via `listProdSliceAcquiresEveryFactor`; pushing it along the stage-inclusion
    into `S* = (chainSliceSystem (enumChain enum)).Obj` gives the colimit point (the WALL 2 input). -/
theorem enumChain_stage_acquires (enum : Nat → 𝒞) (n : Nat)
    (k : Fin (enumPrefix enum (n + 1)).length) :
    (sliceFactorPoint ((enumPrefix enum (n + 1)).get k)
        (listProdProj (enumPrefix enum (n + 1)) k)).f
      ≫ (sliceEmbedObj (listProd (enumPrefix enum (n + 1))) ((enumPrefix enum (n + 1)).get k)).hom
      = (overTerm (listProd (enumPrefix enum (n + 1)))).hom :=
  listProdSliceAcquiresEveryFactor (enumPrefix enum (n + 1)) k

/-! ### `enumChain_hwsuf` and the uniform successor `nextStep` — RELOCATED to `Freyd.Capitalization`

  `enumChain_hwsuf` (the well-supported-suffix precondition) and the §1.546/§1.547 successor
  `nextStepOfEnum`/`exists_wellSupported_enum`/`nextStep : ∀ (S : PreRegBundle), CapStep S.carrier`
  now live UPSTREAM in `Freyd.Capitalization` (after `CapStep`/`PreRegBundle`, before
  `capData_exists`), so `capData_exists`/`hwall_step` can NAME the successor in place.  They remain
  in scope here via the `Capitalization` import.  Pure relocation; the TYPE and proof of `nextStep`
  are unchanged. -/

end Freyd
