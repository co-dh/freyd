/-
  Freyd & Scedrov, *Categories and Allegories* §1.544 — the INFLATION `A′` of a
  category `A`, and the STRICT slice-append functor `A′ → A′/B`.

  Freyd's §1.544 strictification of the relative-capitalization slice rung.  The
  pseudo-functoriality wall of §1.547 (base-change `A/(∏V) → A/(∏U)` is only
  pseudo-functorial, so the inner directed system cannot be a *strict* `CatSystem`)
  is sidestepped exactly as in the book: replace `A` by its inflation `A′`, whose
  binary product is *concatenation of lists* and is therefore STRICTLY associative
  and unital.  Concretely:

    * **Infl `A′`** (`Infl 𝒞 := List 𝒞`): objects are finite sequences
      (lists) of objects of `A`; a morphism `s ⟶ t` in `A′` IS a morphism
      `∏s ⟶ ∏t` in `A` (`listProd`, RelativeCapitalization.lean).  The forgetful
      functor `A′ → A` is `listProd`.  Composition and identity are those of `A`,
      so the category laws hold DEFINITIONALLY (`rfl`).  `A′ ≃ A` but its binary
      product is list concatenation.

    * **Cross-section `A → A′`** (`infl`): `A ↦ [A]`, on `f : A ⟶ A'` the arrow
      `∏[A] ⟶ ∏[A']`, i.e. `A×1 ⟶ A'×1` (via `prodRightFunctor 1`).  Full and
      faithful (the inflation's hom `[A] ⟶ [A']` is `A×1 ⟶ A'×1`, iso to
      `A ⟶ A'` since `1` is terminal; `prodRight 1` is a faithful embedding).

    * **Strict slice-append `A′ → A′/B`** (`appendFunctor B`): the KEY map.
      `s ↦ (s ++ [B], proj_B)` where `proj_B : ∏(s ++ [B]) ⟶ B` is the chosen
      projection onto the appended factor, and on `f : ∏s ⟶ ∏t` the arrow
      `appendMap f : ∏(s++[B]) ⟶ ∏(t++[B])`.  Because the product of `A′` IS
      concatenation, *appending* `[B]` and *appending* the structure map are
      a strict (`rfl`-level) operation on lists — so `appendFunctor` is a genuine
      strict functor, not a base-change-up-to-iso.  This realizes the slice
      inclusion `A → A/B` STRICTLY, which is the whole point of §1.544.

  THIS FILE IS FULLY SORRY-FREE (axioms = `propext`).  It delivers: the inflation category
  (`inflationCat`), the forgetful functor (`inflForget`), the cross-section (`inflFunctor`, with
  full/faithful), the strict slice-append functor (`appendFunctor`) with its `Functor` laws holding
  definitionally from list concatenation; `strict_cancel`/`concat_assoc`/`concat_nil` (the strict
  cancellation / concatenation facts: list-cons injectivity; `(s++d)++e = s++(d++e)`; `s++[] = s`);
  the whole-suffix strict slice base-change `sliceCatFunctor d : A′/V → A′/(V++d)` (the §1.547 inner
  transition by concatenation); and BOTH strict inner-system laws — `F_refl` (`innerSliceTr_refl`)
  AND `F_trans` (`innerSliceTr_trans`, with its core `catMap_append_heq`), the dependent `▸`/`HEq`
  transport across `List.append_assoc` now fully discharged.

  THE DIRECTED STRICT `CatSystem`.  The strict `innerSliceTr` lives on the PREFIX order
  `<+:`, which is NOT directed.  We lift it to a genuine `Directed` index in TWO flavors, the second
  generalizing the first (the proofs are shared — DRY):

    * `chainSliceSystem (P : PrefixChain)` — the ω-chain `ℕ` (`uliftNatDirected`, `bound = max`) along any
      increasing prefix-chain `ℕ → Infl 𝒞`, a Sorry-free directed strict `Colim.CatSystem` whose
      `F_refl`/`F_trans` ARE `innerSliceTr_refl`/`innerSliceTr_trans`.

    * `ordChainSliceSystem (O : OrdChain D)` — the TRANSFINITE generalization over an ARBITRARY directed
      index `(ι, D : Colim.Directed ι)` with a `prefixLe`-monotone chain `chain : ι → Infl 𝒞`.  §1.544-546
      runs the inner relative-capitalization by transfinite recursion over the (possibly uncountable)
      well-supported objects of an arbitrary small category — `ℕ` cannot enumerate an uncountable object
      set.  The whole system/coherence/preservation layer (`ordChainSliceFunctor`/`ordChainSliceSystem`/
      `ordChainSliceCoherent`/`ordChainHas*`/`ordChainH*pres*`/`ordChainSlicePreRegular`) uses its index
      ONLY through `D.refl`/`D.trans`/`D.bound` and `Prop`-irrelevance of `D.le`, so it holds over any
      directed index.  The ℕ `chain*` names are the `uliftNatDirected` specialization (`P.toOrdChain`).
      Supplying a `Colim.Directed` from mathlib's `Ordinal` (or any `LinearOrder + WellFoundedLT`) — done
      in a SEPARATE file so this one stays mathlib-free/fast — plus a cofinal `OrdChain` over it points
      EVERY well-supported object simultaneously, which is the transfinite input `hwall_step` needs.

  See the final block for what the single ω-chain sacrifices vs §1.547's full finite-subset index, and
  why the strict (concatenation) transition cannot be made directed over the set-union index directly.

  This is the reusable keystone; `RelativeCapitalization.lean` consumes it to give the
  §1.547 inner directed system a strict transition functor.

  No mathlib (the directed index is abstract `Colim.Directed`; the category theory stays on this repo's
  own `Cat`).  A mathlib `Ordinal`-backed `Colim.Directed` instance, if used, is confined to a future
  inner-colimit file per the §1.543 CLAUDE.md exception — it is NOT needed to build this file.
-/

import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_26
import Freyd.S1_31
import Freyd.S1_33
import Freyd.S1_42
import Freyd.S1_44
import Freyd.S1_53_SliceRegular
import Freyd.S1_65_SlicePreTopos
import Freyd.S1_543_CatColimitRegular

open Freyd

universe u

namespace Freyd

variable {𝒞 : Type u} [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞]

/-! ## §1.544  The inflation `A′`

  Objects are finite sequences of objects of `A` (`List 𝒞`); a morphism `s ⟶ t`
  IS a morphism `∏s ⟶ ∏t` in `A`.  Composition and identity are inherited from `A`,
  so the `Cat` laws are definitional. -/

/-- The **inflation** `A′` of `A`: objects are finite sequences (`List 𝒞`) of objects
    of `A`.  A morphism `s ⟶ t` is a morphism `∏s ⟶ ∏t` in `A` (the forgetful functor
    sends a sequence to its right-folded product `listProd`).  `A′ ≃ A` but its binary
    product is concatenation. -/
abbrev Infl (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] : Type u := List 𝒞

/-- The inflation category structure: `Hom s t := ∏s ⟶ ∏t`, identity and composition
    inherited from `A` — so the three `Cat` laws hold DEFINITIONALLY. -/
instance inflationCat : Cat.{u} (Infl 𝒞) where
  Hom s t := listProd (𝒞 := 𝒞) s ⟶ listProd t
  id s := Cat.id (listProd s)
  comp f g := f ≫ g
  id_comp f := Cat.id_comp f
  comp_id f := Cat.comp_id f
  assoc f g h := Cat.assoc f g h

/-- A morphism of the inflation `s ⟶ t` is *definitionally* a `𝒞`-morphism `∏s ⟶ ∏t`. -/
theorem inflHom_eq (s t : Infl 𝒞) : (s ⟶ t) = (listProd (𝒞 := 𝒞) s ⟶ listProd t) := rfl

/-- The **forgetful functor** `A′ → A`, `s ↦ ∏s`, identity on the underlying `𝒞`-arrows
    (a morphism of `A′` already IS a `𝒞`-arrow between the products). -/
def inflForgetObj (s : Infl 𝒞) : 𝒞 := listProd s

def inflForget : Functor (Infl 𝒞) 𝒞 where
  obj := inflForgetObj
  map {_s _t} f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## §1.544  The cross-section `A → A′`

  `A ↦ [A]` (the length-1 sequence).  On `f : A ⟶ A'` the arrow `∏[A] ⟶ ∏[A']`, i.e.
  `A×1 ⟶ A'×1` (the `prodRight 1` functor, since `listProd [A] = prod A 1`).  This is
  the "obvious cross-section" `A ⟶ A′` of §1.544. -/

/-- The cross-section object map `A ↦ [A]`. -/
def infl (A : 𝒞) : Infl 𝒞 := [A]

/-- `∏[A] = A × 1` — the underlying product of a singleton sequence. -/
theorem listProd_singleton (A : 𝒞) :
    listProd (𝒞 := 𝒞) [A] = prod A HasTerminal.one := rfl

/-- The cross-section `A → A′` is a functor: on `f : A ⟶ A'`, the inflation arrow
    `[A] ⟶ [A']` is `f × 1` (`A×1 ⟶ A'×1`), i.e. `pair (fst ≫ f) snd`.  (This is the §1.544
    "product with `1`" embedding `prodRight 1` of `S1_54`; inlined here so that `Inflation` sits
    UPSTREAM of `Capitalization` — `S1_54` imports `Capitalization`, which would cycle.) -/
def inflFunctor : Functor 𝒞 (Infl 𝒞) where
  obj := infl
  map {A A'} f := pair (fst ≫ f) snd
  map_id A := by
    show pair (fst ≫ Cat.id A) snd = Cat.id (prod A HasTerminal.one)
    rw [Cat.comp_id]
    exact (pair_uniq fst snd (Cat.id (prod A HasTerminal.one))
      (Cat.id_comp fst) (Cat.id_comp snd)).symm
  map_comp {A A' A''} f g := by
    show pair (fst ≫ f ≫ g) snd = pair (fst ≫ f) snd ≫ pair (fst ≫ g) snd
    symm
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc]
    · rw [Cat.assoc, snd_pair, snd_pair]

/-- Terminal object of `A′`: the empty sequence (`∏[] = 1`).  (Products/equalizers come after the
    `catForget`/`catTail`/`catArrange` machinery they are built from — see `inflHasBinaryProducts`,
    `inflHasEqualizers` below.) -/
instance inflHasTerminal : HasTerminal (Infl 𝒞) where
  one := ([] : List 𝒞)
  trm s := (term (listProd (𝒞 := 𝒞) s) : listProd s ⟶ listProd ([] : List 𝒞))
  uniq {_s} f g := term_uniq (𝒞 := 𝒞) f g

/-! ## §1.544  The STRICT slice-append functor `A′ → A′/B`

  The crux of §1.544.  In the inflation, the binary product IS concatenation, so the
  slice inclusion `A → A/B` is realized STRICTLY (not up to iso) by *appending* `[B]`.

  `appendProj s B : ∏(s ++ [B]) ⟶ B` — the projection onto the appended last factor,
  defined by recursion on `s` (so it is a fixed, choice-free `𝒞`-arrow):
    * `s = []`:  `∏([] ++ [B]) = ∏[B] = B × 1`, project by `fst`.
    * `s = a::s'`: `∏((a::s') ++ [B]) = a × ∏(s' ++ [B])`, project by `snd ≫ appendProj s' B`.

  `appendMap f : ∏(s ++ [B]) ⟶ ∏(t ++ [B])` for `f : ∏s ⟶ ∏t` — extends `f` by the
  identity on the appended `B` factor, also by recursion on the list shape.  Because both
  are list-recursions, all functor laws (`map_id`, `map_comp`) and the over-hom triangle
  (`appendMap f ≫ appendProj t B = appendProj s B`) hold; the unit/composition of the
  appended factor are STRICT (definitional on list cons). -/

/-- Projection `∏(s ++ [B]) ⟶ B` onto the appended last factor (recursion on `s`). -/
def appendProj : ∀ (s : List 𝒞) (B : 𝒞), listProd (𝒞 := 𝒞) (s ++ [B]) ⟶ B
  | [],      B => (fst : prod B HasTerminal.one ⟶ B)
  | _ :: s', B => (snd : prod _ (listProd (s' ++ [B])) ⟶ listProd (s' ++ [B])) ≫ appendProj s' B

/-- The "rest" projection `∏(s ++ [B]) ⟶ ∏s`, forgetting the appended factor (recursion on `s`):
    `s=[]` ↦ `term`-into-`1` precomposed... actually we keep `∏s` and drop `B` via the structure
    of the product.  Used to assemble `appendMap` as a `pair`. -/
def appendForget : ∀ (s : List 𝒞) (B : 𝒞), listProd (𝒞 := 𝒞) (s ++ [B]) ⟶ listProd s
  | [],      _ => (term _ : prod _ HasTerminal.one ⟶ HasTerminal.one)
  | a :: s', B =>
      pair ((fst : prod a (listProd (s' ++ [B])) ⟶ a))
           ((snd : prod a (listProd (s' ++ [B])) ⟶ listProd (s' ++ [B])) ≫ appendForget s' B)

/-- Assemble an arrow into `∏(t ++ [B])` from its `∏t`-part `g` and its `B`-part `b`
    (recursion on `t`).  This is the `pair` that makes the appended factor strict. -/
def appendArrange : ∀ (t : List 𝒞) (B : 𝒞) {X : 𝒞}
    (_g : X ⟶ listProd (𝒞 := 𝒞) t) (_b : X ⟶ B), X ⟶ listProd (𝒞 := 𝒞) (t ++ [B])
  | [],      _, _, _, b => pair b (term _)
  | _ :: t', B, _, g, b => pair (g ≫ fst) (appendArrange t' B (g ≫ snd) b)

/-- The append map `∏(s ++ [B]) ⟶ ∏(t ++ [B])` extending `f : ∏s ⟶ ∏t` by the identity on the
    appended `B` factor.  Assembled from its `∏t`-part `appendForget s B ≫ f` and its `B`-part
    `appendProj s B` (the appended factor kept identical). -/
def appendMap {s t : List 𝒞} (B : 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    listProd (𝒞 := 𝒞) (s ++ [B]) ⟶ listProd (t ++ [B]) :=
  appendArrange t B (appendForget s B ≫ f) (appendProj s B)

/-! ### `appendArrange` is the product pairing into `∏(t ++ [B])`

  The two projection laws (recursion on `t`): `appendArrange` recovers its `B`-part by
  `appendProj` and its `∏t`-part by `appendForget`, and is the UNIQUE such arrow.  These
  reduce all `appendMap`/`appendProj` reasoning to `pair`-algebra. -/

/-- `appendArrange` recovers its `B`-part: `appendArrange t B g b ≫ appendProj t B = b`. -/
theorem appendArrange_proj : ∀ (t : List 𝒞) (B : 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ B),
    appendArrange t B g b ≫ appendProj t B = b
  | [],      B, X, g, b => by
      show pair b (term _) ≫ (fst : prod B HasTerminal.one ⟶ B) = b
      exact fst_pair _ _
  | a :: t', B, X, g, b => by
      show appendArrange (a :: t') B g b
          ≫ ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendProj t' B) = b
      show pair (g ≫ fst) (appendArrange t' B (g ≫ snd) b)
          ≫ ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendProj t' B) = b
      rw [← Cat.assoc, snd_pair]; exact appendArrange_proj t' B (g ≫ snd) b

/-- `appendArrange` recovers its `∏t`-part: `appendArrange t B g b ≫ appendForget t B = g`. -/
theorem appendArrange_forget : ∀ (t : List 𝒞) (B : 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ B),
    appendArrange t B g b ≫ appendForget t B = g
  | [],      B, X, g, b => by
      -- `∏[] = 1`, so `g : X ⟶ 1` is forced to be `term X`; both sides are `term X`.
      show appendArrange [] B g b ≫ (term _ : prod B HasTerminal.one ⟶ HasTerminal.one) = g
      exact term_uniq _ g
  | a :: t', B, X, g, b => by
      show pair (g ≫ fst) (appendArrange t' B (g ≫ snd) b)
          ≫ pair (fst : prod a (listProd (t' ++ [B])) ⟶ a)
                 ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B) = g
      refine (pair_uniq (g ≫ fst) (g ≫ snd) _ ?_ ?_).trans (pair_uniq _ _ g rfl rfl).symm
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair]
        exact appendArrange_forget t' B (g ≫ snd) b

/-- `appendProj`/`appendForget` are JOINTLY MONIC: two arrows into `∏(t ++ [B])` agreeing on
    both the appended factor (`appendProj`) and the rest (`appendForget`) are equal.  (Recursion
    on `t`; the product `∏(t++[B])` is a table on `(∏t, B)` via these two arrows.) -/
theorem append_jointly_monic : ∀ (t : List 𝒞) (B : 𝒞) {X : 𝒞}
    (p q : X ⟶ listProd (𝒞 := 𝒞) (t ++ [B]))
    (_hf : p ≫ appendForget t B = q ≫ appendForget t B)
    (_hb : p ≫ appendProj t B = q ≫ appendProj t B), p = q
  | [],      B, X, p, q, _, hb => by
      -- `∏([]++[B]) = B×1`; `appendProj [] B = fst`, and the `1`-component is forced by `term`.
      apply fst_snd_jointly_monic
      · exact hb
      · exact term_uniq _ _
  | a :: t', B, X, p, q, hf, hb => by
      -- `∏((a::t')++[B]) = a × ∏(t'++[B])`; recurse on the `snd` component.
      have hforget : appendForget (a :: t') B
          = pair (fst : prod a (listProd (t' ++ [B])) ⟶ a)
                 ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B) := rfl
      rw [hforget] at hf
      -- read off the `fst`- and `snd`-components of `hf` (the `appendForget`-equation).
      have hfst : (p ≫ pair (fst : prod a (listProd (t' ++ [B])) ⟶ a)
                    ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B)) ≫ fst
                  = (q ≫ pair fst ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B)) ≫ fst :=
        congrArg (· ≫ fst) hf
      have hsnd : (p ≫ pair (fst : prod a (listProd (t' ++ [B])) ⟶ a)
                    ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B)) ≫ snd
                  = (q ≫ pair fst ((snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendForget t' B)) ≫ snd :=
        congrArg (· ≫ snd) hf
      simp only [Cat.assoc, fst_pair, snd_pair] at hfst hsnd
      simp only [← Cat.assoc] at hsnd
      -- and the `snd`-component of `hb` (the `appendProj`-equation).
      have hproj : appendProj (a :: t') B
          = (snd : prod a (listProd (t' ++ [B])) ⟶ _) ≫ appendProj t' B := rfl
      rw [hproj] at hb; simp only [← Cat.assoc] at hb
      apply fst_snd_jointly_monic
      · exact hfst
      · exact append_jointly_monic t' B _ _ hsnd hb

/-! ### `appendMap` is a strict functor and gives the over-hom triangle

  From the two `appendArrange` projection laws: `appendMap B f` keeps the appended `B`-factor
  (`appendMap_proj`, the slice-triangle) and acts as `f` on the rest (`appendMap_forget`).
  Joint monicity then gives `map_id`/`map_comp` (the appended factor and the rest are each
  strictly preserved). -/

/-- `appendMap` keeps the appended `B`-factor: `appendMap B f ≫ appendProj t B = appendProj s B`.
    This IS the over-hom triangle of the slice-append functor (structure maps are the projections). -/
@[simp] theorem appendMap_proj {s t : List 𝒞} (B : 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    appendMap B f ≫ appendProj t B = appendProj s B :=
  appendArrange_proj t B (appendForget s B ≫ f) (appendProj s B)

/-- `appendMap` acts as `f` on the rest: `appendMap B f ≫ appendForget t B = appendForget s B ≫ f`. -/
@[simp] theorem appendMap_forget {s t : List 𝒞} (B : 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    appendMap B f ≫ appendForget t B = appendForget s B ≫ f :=
  appendArrange_forget t B (appendForget s B ≫ f) (appendProj s B)

/-- `appendMap` preserves identities: `appendMap B (id) = id`.  (Joint monicity: both sides agree
    on `appendProj` and `appendForget`.) -/
theorem appendMap_id (s : List 𝒞) (B : 𝒞) :
    appendMap B (Cat.id (listProd (𝒞 := 𝒞) s)) = Cat.id (listProd (s ++ [B])) := by
  apply append_jointly_monic s B
  · rw [appendMap_forget, Cat.comp_id, Cat.id_comp]
  · rw [appendMap_proj, Cat.id_comp]

/-- `appendMap` preserves composition: `appendMap B (f ≫ g) = appendMap B f ≫ appendMap B g`. -/
theorem appendMap_comp {s t r : List 𝒞} (B : 𝒞)
    (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) (g : listProd t ⟶ listProd r) :
    appendMap B (f ≫ g) = appendMap B f ≫ appendMap B g := by
  apply append_jointly_monic r B
  · simp only [Cat.assoc, appendMap_forget]
    rw [← Cat.assoc (f := appendMap B f), appendMap_forget, Cat.assoc]
  · simp only [Cat.assoc, appendMap_proj]

/-! ## §1.544  The strict slice-append functor `A′ → A′/[B]`

  Packaged as a genuine `Functor` into the slice `A′/[B] = Over (infl B)` (the slice of the
  inflation over the singleton object `[B]`).  Object map `s ↦ ⟨s ++ [B], structure⟩` where
  the structure map `(s ++ [B]) ⟶ [B]` in `A′` is `pair (appendProj s B) (term _) : ∏(s++[B]) ⟶ B×1`;
  morphism map `appendMap B f`, whose over-hom triangle is `appendMap_proj` (the appended factor
  is preserved).  Functor laws are `appendMap_id`/`appendMap_comp` — STRICT (the append operation
  on lists is definitional). -/

/-- The structure map `(s ++ [B]) ⟶ [B]` in `A′`: as a `𝒞`-arrow `∏(s++[B]) ⟶ ∏[B] = B × 1`,
    it is `⟨appendProj s B, term⟩`.  Its `fst`-component is the appended-factor projection.  Typed
    as an `inflationCat`-hom `(s++[B]) ⟶ infl B` (which IS this `𝒞`-arrow definitionally). -/
def appendStruct (s : List 𝒞) (B : 𝒞) :
    @Cat.Hom (Infl 𝒞) inflationCat (s ++ [B]) (infl B) :=
  (pair (appendProj s B) (term _) : listProd (𝒞 := 𝒞) (s ++ [B]) ⟶ prod B HasTerminal.one)

/-- The slice-append object map `s ↦ ⟨s ++ [B], appendStruct⟩ : A′ → A′/[B]`. -/
def appendObj (B : 𝒞) (s : Infl 𝒞) : Over (B := infl B) :=
  { dom := (s ++ [B] : List 𝒞), hom := appendStruct s B }

/-- The slice-append morphism map: `f : ∏s ⟶ ∏t` becomes the over-hom `appendMap B f`, which
    commutes with the structure maps because `appendMap_proj` keeps the appended factor (and the
    `1`-component is forced by `term`). -/
def appendOverHom (B : 𝒞) {s t : Infl 𝒞} (f : s ⟶ t) :
    OverHom (appendObj B s) (appendObj B t) :=
  { f := appendMap B f,
    w := by
      show appendMap B f ≫ appendStruct t B = appendStruct s B
      -- jointly monic on `B×1` via `fst`/`snd`; `fst`-component is `appendMap_proj`, `snd` is `term`.
      apply fst_snd_jointly_monic
      · show (appendMap B f ≫ pair (appendProj t B) (term _)) ≫ fst
            = pair (appendProj s B) (term _) ≫ fst
        rw [Cat.assoc, fst_pair, fst_pair]; exact appendMap_proj B f
      · exact term_uniq _ _ }

/-- **§1.544 — the STRICT slice-append functor `A′ → A′/[B]`.**  Realizes the slice inclusion
    `A → A/B` on the inflation *strictly* (not up to iso): the product of `A′` is concatenation,
    so `appendObj`/`appendOverHom` are definitional list operations and the functor laws are the
    strict `appendMap_id`/`appendMap_comp`. -/
def appendFunctor (B : 𝒞) :
    @Functor (Infl 𝒞) (Over (B := infl B)) inflationCat (overCat (infl B)) where
  obj := appendObj B
  map {s t} f := appendOverHom B f
  map_id s := OverHom.ext (by
    show appendMap B (Cat.id (listProd s)) = Cat.id (listProd (s ++ [B]))
    exact appendMap_id s B)
  map_comp {s t r} f g := OverHom.ext (by
    show appendMap B (f ≫ g) = appendMap B f ≫ appendMap B g
    exact appendMap_comp B f g)

/-! ## §1.547  Strict cancellation and the concatenation order on the inflation

  Freyd (§1.544): "the binary product operation on `A′` can now be taken as concatenation.  We
  obtain a strict cancellation property: if `B × A = B × A'` then `A = A'`."  In the inflation,
  `B × s` is `B :: s` (cons), so cancellation is `List.cons` injectivity — DEFINITIONAL.  More
  generally concatenation is STRICTLY associative and unital: `(s++d)++e = s++(d++e)` and `s++[] = s`
  hold as genuine equalities of LIST objects (`List.append_assoc`/`List.append_nil`), so the §1.547
  inner directed-system laws `F_refl`/`F_trans` are honest theorems — UNLIKE raw base-change, where
  `baseChangeObj (Cat.id) X` is iso to `X` but NOT EQUAL, so the laws are simply false.  That object
  equality (not mere iso) is the strictness the inner `CatSystem` requires. -/

/-- Concatenation is STRICTLY associative on `A′` (equality of list objects). -/
theorem concat_assoc (s d e : Infl 𝒞) : (s ++ d) ++ e = s ++ (d ++ e) :=
  List.append_assoc s d e

/-- Concatenation is STRICTLY right-unital on `A′` (equality of list objects). -/
theorem concat_nil (s : Infl 𝒞) : s ++ ([] : List 𝒞) = s := List.append_nil s

/-! ## §1.547  The STRICT inner directed system of inflation slices

  The §1.547 inner system: stage `w` (a finite factor-sequence) is the slice `A′/w`, and the
  transition `A′/V → A′/U` for `V ⊑ U` (`U = V ++ d`) is BASE-CHANGE along the strict projection
  `∏U ⟶ ∏V`, realized by *appending* the suffix `d`.  Because concatenation is strict (above), the
  refl/trans laws hold DEFINITIONALLY — no pseudo-functoriality.

  We model the index by `List 𝒞` with the prefix order `V ⊑ U := ∃ d, V ++ d = U` carried as data
  `Suffix V U` (the witnessing suffix `d` with `V ++ d = U`).  The transition functor base-changes
  by appending `d`; its object/morphism maps iterate the single-factor `appendObj`/`appendMap`.

  The base-change object map `A′/V → A′/(V++d)` on the inflation: `⟨s, h : s ⟶ V⟩ ↦
  ⟨s ++ d, appendMap-style⟩` where the structure map appends `d` to both `s` and `V` and `h`
  becomes `h ⊗ id_{∏d}`.  For a SINGLE appended factor `[B]` this is `appendMap B h` (below); the
  multi-factor (whole-`d`) version iterates it, re-bracketing by the strict `concat_assoc`. -/

/-- The explicit suffix witness `V ++ d = U` (the §1.547 prefix order, carried as data so the
    transition functor — "append the suffix `d`" — is canonical). -/
structure Suffix (V U : Infl 𝒞) where
  d : List 𝒞
  eq : V ++ d = U

-- `appendList d s := s ++ d` (a swapped-argument alias of `++`) and its two lemmas used to live
-- here.  The lemmas were `concat_nil` and `concat_assoc` above with the alias unfolded — same
-- statements, and literally the same proof terms, `List.append_nil` and `List.append_assoc`.
-- Nothing referenced any of the three.

/-! ### Whole-suffix concatenation maps `concat*` (generalizing `append*` from `[B]` to a list `d`)

  To build the §1.547 inner transition for a multi-factor suffix `d` (not just one factor), we
  generalize the single-factor `appendProj`/`appendForget`/`appendArrange`/`appendMap` from `[B]`
  to an arbitrary appended list `d` (with `∏[B] = B×1` replaced by `∏d`).  Recursion is on the base
  list `s`; the appended `d` is fixed.  These give the whole-suffix slice base-change and the strict
  inner directed system. -/

/-- Tail projection `∏(s ++ d) ⟶ ∏d` onto the appended suffix `d` (recursion on `s`). -/
def catTail : ∀ (s d : List 𝒞), listProd (𝒞 := 𝒞) (s ++ d) ⟶ listProd d
  | [],      _ => Cat.id _
  | _ :: s', d => (snd : prod _ (listProd (s' ++ d)) ⟶ listProd (s' ++ d)) ≫ catTail s' d

/-- Rest projection `∏(s ++ d) ⟶ ∏s`, forgetting the appended suffix `d` (recursion on `s`). -/
def catForget : ∀ (s d : List 𝒞), listProd (𝒞 := 𝒞) (s ++ d) ⟶ listProd s
  | [],      d => (term _ : listProd (𝒞 := 𝒞) ([] ++ d) ⟶ HasTerminal.one)
  | a :: s', d =>
      pair (fst : prod a (listProd (s' ++ d)) ⟶ a)
           ((snd : prod a (listProd (s' ++ d)) ⟶ listProd (s' ++ d)) ≫ catForget s' d)

/-- Assemble an arrow into `∏(t ++ d)` from its `∏t`-part `g` and its `∏d`-part `b` (recursion on `t`). -/
def catArrange : ∀ (t d : List 𝒞) {X : 𝒞}
    (_g : X ⟶ listProd (𝒞 := 𝒞) t) (_b : X ⟶ listProd d), X ⟶ listProd (𝒞 := 𝒞) (t ++ d)
  | [],      _, _, _, b => b
  | _ :: t', d, _, g, b => pair (g ≫ fst) (catArrange t' d (g ≫ snd) b)

/-- The concatenation map `∏(s ++ d) ⟶ ∏(t ++ d)` extending `f : ∏s ⟶ ∏t` by the identity on the
    appended suffix `∏d`.  (Whole-`d` generalization of `appendMap`.) -/
def catMap {s t : List 𝒞} (d : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    listProd (𝒞 := 𝒞) (s ++ d) ⟶ listProd (t ++ d) :=
  catArrange t d (catForget s d ≫ f) (catTail s d)

/-- `catArrange` recovers its `∏d`-part: `catArrange t d g b ≫ catTail t d = b`. -/
theorem catArrange_tail : ∀ (t d : List 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd d),
    catArrange t d g b ≫ catTail t d = b
  | [],      d, X, g, b => Cat.comp_id b
  | a :: t', d, X, g, b => by
      show catArrange (a :: t') d g b ≫ ((snd : _) ≫ catTail t' d) = b
      show pair (g ≫ fst) (catArrange t' d (g ≫ snd) b) ≫ ((snd : _) ≫ catTail t' d) = b
      rw [← Cat.assoc, snd_pair]; exact catArrange_tail t' d (g ≫ snd) b

/-- `catArrange` recovers its `∏t`-part: `catArrange t d g b ≫ catForget t d = g`. -/
theorem catArrange_forget : ∀ (t d : List 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd d),
    catArrange t d g b ≫ catForget t d = g
  | [],      d, X, g, b => term_uniq _ g
  | a :: t', d, X, g, b => by
      show pair (g ≫ fst) (catArrange t' d (g ≫ snd) b)
          ≫ pair (fst : prod a (listProd (t' ++ d)) ⟶ a)
                 ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d) = g
      refine (pair_uniq (g ≫ fst) (g ≫ snd) _ ?_ ?_).trans (pair_uniq _ _ g rfl rfl).symm
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair]
        exact catArrange_forget t' d (g ≫ snd) b

/-- `catTail`/`catForget` are JOINTLY MONIC into `∏(t ++ d)`. -/
theorem cat_jointly_monic : ∀ (t d : List 𝒞) {X : 𝒞}
    (p q : X ⟶ listProd (𝒞 := 𝒞) (t ++ d))
    (_hf : p ≫ catForget t d = q ≫ catForget t d)
    (_hb : p ≫ catTail t d = q ≫ catTail t d), p = q
  | [],      d, X, p, q, _, hb => by
      -- `∏([]++d) = ∏d`; `catTail [] d = id`, so `hb : p = q` directly.
      rw [catTail, Cat.comp_id, Cat.comp_id] at hb; exact hb
  | a :: t', d, X, p, q, hf, hb => by
      have hforget : catForget (a :: t') d
          = pair (fst : prod a (listProd (t' ++ d)) ⟶ a)
                 ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d) := rfl
      rw [hforget] at hf
      have hfst : (p ≫ pair (fst : prod a (listProd (t' ++ d)) ⟶ a)
                    ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d)) ≫ fst
                  = (q ≫ pair fst ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d)) ≫ fst :=
        congrArg (· ≫ fst) hf
      have hsnd : (p ≫ pair (fst : prod a (listProd (t' ++ d)) ⟶ a)
                    ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d)) ≫ snd
                  = (q ≫ pair fst ((snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catForget t' d)) ≫ snd :=
        congrArg (· ≫ snd) hf
      simp only [Cat.assoc, fst_pair, snd_pair] at hfst hsnd
      simp only [← Cat.assoc] at hsnd
      have hproj : catTail (a :: t') d
          = (snd : prod a (listProd (t' ++ d)) ⟶ _) ≫ catTail t' d := rfl
      rw [hproj] at hb; simp only [← Cat.assoc] at hb
      apply fst_snd_jointly_monic
      · exact hfst
      · exact cat_jointly_monic t' d _ _ hsnd hb

@[simp] theorem catMap_tail {s t : List 𝒞} (d : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    catMap d f ≫ catTail t d = catTail s d :=
  catArrange_tail t d (catForget s d ≫ f) (catTail s d)

@[simp] theorem catMap_forget {s t : List 𝒞} (d : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    catMap d f ≫ catForget t d = catForget s d ≫ f :=
  catArrange_forget t d (catForget s d ≫ f) (catTail s d)

theorem catMap_id (s d : List 𝒞) :
    catMap d (Cat.id (listProd (𝒞 := 𝒞) s)) = Cat.id (listProd (s ++ d)) := by
  apply cat_jointly_monic s d
  · rw [catMap_forget, Cat.comp_id, Cat.id_comp]
  · rw [catMap_tail, Cat.id_comp]

theorem catMap_comp {s t r : List 𝒞} (d : List 𝒞)
    (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) (g : listProd t ⟶ listProd r) :
    catMap d (f ≫ g) = catMap d f ≫ catMap d g := by
  apply cat_jointly_monic r d
  · simp only [Cat.assoc, catMap_forget]
    rw [← Cat.assoc (f := catMap d f), catMap_forget, Cat.assoc]
  · simp only [Cat.assoc, catMap_tail]

/-! ### `catMap d f` is a PULLBACK of `f` along the projection `catForget t d`

  The §1.547 inner transition `sliceCatFunctor d` is base-change by concatenation; the key fact that
  makes it transfer covers and preserve monos is that `catMap d f` is a genuine pullback of `f` along
  the projection `catForget t d : ∏(t++d) ⟶ ∏t`.  The square
    `catMap d f ≫ catForget t d = catForget s d ≫ f` (`catMap_forget`)
  is universal: the unique lift of a cone `(p : W → ∏s, q : W → ∏(t++d))` (with `p ≫ f = q ≫
  catForget t d`) is `catArrange s d p (q ≫ catTail t d)` — its `∏s`-part is `p` (`catArrange_forget`)
  and its image under `catMap d f` agrees with `q` on both `catForget t d` and `catTail t d`, so
  `cat_jointly_monic` clinches it; uniqueness rides `cat_jointly_monic s d`. -/

/-- The pullback cone of `f` along `catForget t d`: apex `∏(s++d)`, legs `(catForget s d, catMap d f)`. -/
def catMapCone {s t : List 𝒞} (d : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    Cone (𝒞 := Infl 𝒞) (f : (s : Infl 𝒞) ⟶ t) (catForget t d : (t ++ d : List 𝒞) ⟶ t) :=
  { pt := (s ++ d : List 𝒞)
    π₁ := (catForget s d : (s ++ d : List 𝒞) ⟶ s)
    π₂ := (catMap d f : (s ++ d : List 𝒞) ⟶ (t ++ d : List 𝒞))
    w := (catMap_forget d f).symm }

/-- **`catMap d f` is a pullback of `f` along `catForget t d`.**  The unique lift of a cone
    `(p, q)` is `catArrange s d p (q ≫ catTail t d)`. -/
theorem catMap_isPullback {s t : List 𝒞} (d : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    (catMapCone d f).IsPullback (𝒞 := Infl 𝒞) := by
  intro c
  -- name the cone legs as `A`-arrows out of the apex `∏c.pt`.
  let p : listProd (𝒞 := 𝒞) c.pt ⟶ listProd s := c.π₁
  let q : listProd (𝒞 := 𝒞) c.pt ⟶ listProd (t ++ d) := c.π₂
  have hcw : p ≫ f = q ≫ catForget t d := c.w
  let u : listProd (𝒞 := 𝒞) c.pt ⟶ listProd (s ++ d) := catArrange s d p (q ≫ catTail t d)
  have hu1 : u ≫ catForget s d = p := catArrange_forget s d p (q ≫ catTail t d)
  have hu2 : u ≫ catMap d f = q := by
    apply cat_jointly_monic t d
    · -- forget-part: `u ≫ catMap d f ≫ catForget t d = u ≫ catForget s d ≫ f = p ≫ f = q ≫ catForget t d`
      rw [Cat.assoc, catMap_forget, ← Cat.assoc, hu1, hcw]
    · -- tail-part: `u ≫ catMap d f ≫ catTail t d = u ≫ catTail s d = q ≫ catTail t d`
      rw [Cat.assoc, catMap_tail]
      exact catArrange_tail s d p (q ≫ catTail t d)
  refine ⟨u, ⟨hu1, hu2⟩, ?_⟩
  intro v0 hv1 hv2
  -- uniqueness: `v` agrees with `u` on both projections of `∏(s++d)`.
  let v : listProd (𝒞 := 𝒞) c.pt ⟶ listProd (s ++ d) := v0
  have hv1' : v ≫ catForget s d = p := hv1
  have hv2' : v ≫ catMap d f = q := hv2
  show v = u
  apply cat_jointly_monic s d (X := listProd (𝒞 := 𝒞) c.pt)
  · -- forget-part: both equal `p`.
    rw [hv1', hu1]
  · -- tail-part: both equal `q ≫ catTail t d` (via `catMap d f ≫ catTail t d = catTail s d`).
    rw [← catMap_tail (d := d) f, ← Cat.assoc, ← Cat.assoc, hv2', hu2]


/-! ### §1.544  `A′` is Cartesian: binary products and equalizers

  With `catForget`/`catTail`/`catArrange` in hand the inflation's binary product is concatenation
  and its equalizer is the singleton of the underlying `A`-equalizer (rode through the `E ≅ E×1`
  unitor).  Together with `inflHasTerminal` this makes `A′` Cartesian, hence (via
  `products_equalizers_implies_pullbacks`) it has pullbacks. -/

/-- Binary products of `A′`: concatenation `s ++ t`, with projections `catForget`/`catTail`,
    pairing `catArrange`.  The three product laws are `catArrange_forget`/`catArrange_tail`
    (projections) and `cat_jointly_monic` (uniqueness). -/
instance inflHasBinaryProducts : HasBinaryProducts (Infl 𝒞) where
  prod s t := (s ++ t : List 𝒞)
  fst {s t} := (catForget s t : listProd (s ++ t) ⟶ listProd s)
  snd {s t} := (catTail s t : listProd (s ++ t) ⟶ listProd t)
  pair {x s t} g h := (catArrange s t g h : listProd x ⟶ listProd (s ++ t))
  fst_pair {x s t} g h := catArrange_forget s t g h
  snd_pair {x s t} g h := catArrange_tail s t g h
  pair_uniq {x s t} g h k h₁ h₂ :=
    cat_jointly_monic s t k (catArrange s t g h)
      (by rw [catArrange_forget]; exact h₁) (by rw [catArrange_tail]; exact h₂)

/-- The equalizer of `f g : s ⟶ t` in `A′` (i.e. of `f g : ∏s ⟶ ∏t` in `A`): the SINGLETON `[E]`
    of the `A`-equalizer object `E := eqObj f g` (`∏[E] = E × 1`), equalizing map `fst ≫ eqMap`.
    Lift wraps the `A`-lift through the unitor `prodOneRightInv E : E ⟶ E×1`; the factorisation and
    uniqueness ride the unitor projection laws (`E ≅ E×1`) plus `eqLift_uniq`. -/
instance inflHasEqualizers [HasEqualizers 𝒞] : HasEqualizers (Infl 𝒞) where
  eq s t f g :=
    -- `f g : s ⟶ t` in `A′` ARE `A`-arrows `∏s ⟶ ∏t`; force the `A`-reading so `eqObj`/`eqMap`/`eqLift`
    -- resolve in `A` (not recursively in `A′`).
    let f' : listProd (𝒞 := 𝒞) s ⟶ listProd t := f
    let g' : listProd (𝒞 := 𝒞) s ⟶ listProd t := g
    let E : 𝒞 := eqObj (𝒞 := 𝒞) f' g'
    { cone :=
        { dom := ([E] : List 𝒞),
          map := ((fst : prod E one ⟶ E) ≫ eqMap f' g' :
            listProd (𝒞 := 𝒞) [E] ⟶ listProd s),
          eq := by
            show ((fst : prod E one ⟶ E) ≫ eqMap f' g') ≫ f'
                = ((fst : prod E one ⟶ E) ≫ eqMap f' g') ≫ g'
            rw [Cat.assoc, Cat.assoc, eqMap_eq] }
      lift c :=
        (eqLift f' g' c.map c.eq ≫ prodOneRightInv E :
          listProd (𝒞 := 𝒞) c.dom ⟶ listProd [E])
      fac c := by
        show (eqLift f' g' c.map c.eq ≫ prodOneRightInv E)
            ≫ ((fst : prod E one ⟶ E) ≫ eqMap f' g') = c.map
        rw [← Cat.assoc, Cat.assoc (eqLift f' g' c.map c.eq),
          show prodOneRightInv E ≫ fst = Cat.id E from fst_pair _ _, Cat.comp_id,
          eqLift_fac]
      uniq c m hm := by
        -- `m : ∏c.dom ⟶ E×1`; `m ≫ (fst ≫ eqMap) = c.map`.  `m ≫ fst` is the unique `A`-lift.
        let cmap : listProd (𝒞 := 𝒞) c.dom ⟶ listProd s := c.map
        have hmfst : @Eq (listProd (𝒞 := 𝒞) c.dom ⟶ listProd s)
            ((m ≫ (fst : prod E one ⟶ E)) ≫ eqMap f' g') cmap := by
          rw [Cat.assoc]; exact hm
        have hceq : cmap ≫ f' = cmap ≫ g' := c.eq
        have hlift : @Eq (listProd (𝒞 := 𝒞) c.dom ⟶ E)
            (m ≫ (fst : prod E one ⟶ E)) (eqLift f' g' cmap hceq) :=
          eqLift_uniq f' g' cmap hceq _ hmfst
        -- `m = (m ≫ fst) ≫ unitor⁻¹`, and `m ≫ fst = eqLift` (the unique `A`-lift).
        have key : @Eq (listProd (𝒞 := 𝒞) c.dom ⟶ prod E one)
            ((m ≫ (fst : prod E one ⟶ E)) ≫ prodOneRightInv E) m := by
          rw [Cat.assoc, fst_prodOneRightInv]; exact Cat.comp_id m
        rw [← key, hlift] }

/-- `A′` has pullbacks (Cartesian ⟹ pullbacks, `products_equalizers_implies_pullbacks`). -/
instance inflHasPullbacks [HasEqualizers 𝒞] : HasPullbacks (Infl 𝒞) where
  has f g := products_equalizers_implies_pullbacks f g

/-! ### §1.544  `A′` is pre-regular: cover transfer across `A′ ≃ A`

  `A′ ≃ A` via the forgetful `inflForget : s ↦ ∏s` (full + faithful), with essential surjectivity
  witnessed by the unitor `∏[X] = X×1 ≅ X` (`prod_one_iso_right`).  We transfer
  `PullbacksTransferCovers` across this equivalence.  Three ingredients, each riding the `X ≅ X×1`
  unitor `prodOneRightInv`:
    * `inflMono_to_mono`: an `A′`-mono is an `A`-mono (ess.-surj. supplies the missing test objects).
    * `inflCover_to_cover` / `coverC_to_inflCover`: `Cover` transfers both ways on the SAME underlying
      `A`-arrow.
    * `inflIsPullback_to_isPullback`: an `A′`-pullback square is an `A`-pullback square.
  Then `PullbacksTransferCovers (Infl 𝒞)` is `A`'s instance conjugated by the equivalence. -/

/-- An `A′`-mono `m : ∏C ⟶ ∏t` is an `A`-mono.  `A′`'s test objects are the products `∏W`; every
    `A`-object `W` is `∏[W] = W×1` up to the unitor `fst`, so left-cancellability against all `∏W`
    upgrades to all `W` (precompose with the iso `prodOneRightInv W`, cancel the iso `fst`). -/
theorem inflMono_to_mono {C t : Infl 𝒞} {m : listProd (𝒞 := 𝒞) C ⟶ listProd t}
    (hm : Monic (𝒞 := Infl 𝒞) m) : Monic (𝒞 := 𝒞) m := by
  -- `A′`-mono restated on `A`-arrows: cancellable against every product `∏V` (Infl test objects).
  have hm' : ∀ {V : Infl 𝒞} (g h : listProd (𝒞 := 𝒞) V ⟶ listProd C),
      g ≫ m = h ≫ m → g = h := fun {V} g h => hm (W := V) g h
  intro W p q hpq
  -- lift `p q : W ⟶ ∏C` to `A`-arrows out of `∏[W] = W×1` via the unitor `fst`.
  have hlift : ((fst : prod W one ⟶ W) ≫ p) ≫ m = ((fst : prod W one ⟶ W) ≫ q) ≫ m := by
    rw [Cat.assoc, Cat.assoc, hpq]
  have hC : (fst : prod W one ⟶ W) ≫ p = (fst : prod W one ⟶ W) ≫ q :=
    hm' (V := ([W] : List 𝒞)) ((fst : prod W one ⟶ W) ≫ p) ((fst : prod W one ⟶ W) ≫ q) hlift
  -- cancel the iso `fst : W×1 ⟶ W` on the left (precompose `prodOneRightInv W`).
  have := congrArg (fun u => prodOneRightInv W ≫ u) hC
  simpa only [← Cat.assoc, show prodOneRightInv W ≫ fst = Cat.id W from fst_pair _ _,
    Cat.id_comp] using this

/-- `Cover` carries from `A′` to `A` (same underlying arrow `∏s ⟶ ∏t`).  An `A`-mono `m : C ⟶ ∏t`
    that the underlying `f` factors through is wrapped to the `A′`-mono `fst ≫ m : [C] ⟶ t` (`fst`
    iso ⟹ `inflMono_to_mono` gives it mono in `A′`); `Cover(A′) f` forces it iso, and `fst` iso then
    forces `m` iso. -/
theorem inflCover_to_cover {s t : Infl 𝒞} {f : listProd (𝒞 := 𝒞) s ⟶ listProd t}
    (hf : Cover (𝒞 := Infl 𝒞) f) : Cover (𝒞 := 𝒞) f := by
  intro C m g hm hgm
  -- the `A′`-mono `fst ≫ m : [C] ⟶ t` (underlying `C×1 ⟶ ∏t`).  Monic in `A` (cancel the iso `fst`).
  have hm𝒞 : Monic (𝒞 := 𝒞) ((fst : prod C one ⟶ C) ≫ m) := by
    intro W p q hpq
    have h1 : (p ≫ (fst : prod C one ⟶ C)) ≫ m = (q ≫ (fst : prod C one ⟶ C)) ≫ m := by
      rw [Cat.assoc, Cat.assoc]; exact hpq
    have h2 : p ≫ (fst : prod C one ⟶ C) = q ≫ (fst : prod C one ⟶ C) := hm _ _ h1
    have := congrArg (fun u => u ≫ prodOneRightInv C) h2
    simpa only [Cat.assoc, fst_prodOneRightInv, Cat.comp_id] using this
  -- `[C] : Infl`, `∏[C] = C×1`; bind the underlying `A`-arrow `M := fst ≫ m : C×1 ⟶ ∏t`, which IS
  -- the `A′`-arrow `[C] ⟶ t` (defeq).  Stating the `A′`-mono over `M` avoids the `A′`-vs-`A` `≫` clash.
  let M : listProd (𝒞 := 𝒞) ([C] : List 𝒞) ⟶ listProd t := (fst : prod C one ⟶ C) ≫ m
  have hmInfl : Monic (𝒞 := Infl 𝒞) (X := ([C] : List 𝒞)) (Y := t) M :=
    fun {V} p q hpq => hm𝒞 (W := listProd (𝒞 := 𝒞) V) p q hpq
  -- `g' := g ≫ prodOneRightInv C : s ⟶ [C]` factors `f` through it.
  let g' : listProd (𝒞 := 𝒞) s ⟶ listProd ([C] : List 𝒞) := g ≫ prodOneRightInv C
  have hfac : g' ≫ M = f := by
    show (g ≫ prodOneRightInv C) ≫ ((fst : prod C one ⟶ C) ≫ m) = f
    rw [← Cat.assoc, Cat.assoc g, show prodOneRightInv C ≫ fst = Cat.id C from fst_pair _ _,
      Cat.comp_id, hgm]
  have hiso : IsIso (𝒞 := Infl 𝒞) (X := ([C] : List 𝒞)) (Y := t) M :=
    hf (C := ([C] : List 𝒞)) M g' hmInfl hfac
  -- `IsIso(A′) (fst ≫ m) = IsIso(A) (fst ≫ m)`; `m = prodOneRightInv C ≫ (fst ≫ m)`, iso∘iso.
  have hiso𝒞 : IsIso (𝒞 := 𝒞) ((fst : prod C one ⟶ C) ≫ m) := hiso
  have hmeq : m = prodOneRightInv C ≫ ((fst : prod C one ⟶ C) ≫ m) := by
    rw [← Cat.assoc, show prodOneRightInv C ≫ fst = Cat.id C from fst_pair _ _, Cat.id_comp]
  have hinvIso : IsIso (𝒞 := 𝒞) (prodOneRightInv C) :=
    ⟨(fst : prod C one ⟶ C), fst_pair _ _, fst_prodOneRightInv⟩
  rw [hmeq]; exact isIso_comp (𝒞 := 𝒞) hinvIso hiso𝒞

/-- `Cover` carries from `A` back to `A′` (same underlying arrow).  An `A′`-mono is an `A`-mono
    (`inflMono_to_mono`), so `Cover(A) f` discharges the `A′` cover obligation directly. -/
theorem coverC_to_inflCover {s t : Infl 𝒞} {f : listProd (𝒞 := 𝒞) s ⟶ listProd t}
    (hf : Cover (𝒞 := 𝒞) f) : Cover (𝒞 := Infl 𝒞) f := by
  intro C m g hm hgm
  -- `m : C ⟶ t` in `A′` IS `M : ∏C ⟶ ∏t` in `A`, mono by `inflMono_to_mono`.
  have hm𝒞 : Monic (𝒞 := 𝒞) (m : listProd (𝒞 := 𝒞) C ⟶ listProd t) := inflMono_to_mono hm
  have hiso𝒞 : IsIso (𝒞 := 𝒞) (m : listProd (𝒞 := 𝒞) C ⟶ listProd t) :=
    hf (C := listProd (𝒞 := 𝒞) C) m g hm𝒞 hgm
  exact hiso𝒞

/-! ### §1.544  `A′`-pullback squares are `A`-pullback squares

  An `A′`-pullback cone (universal among `A′` cones) is universal among `A` cones too: any `A`-cone
  with apex `W` factors through `[W]` (`∏[W] = W×1`) into an `A′`-cone, whose `A′`-lift, precomposed
  with the unitor `prodOneRightInv W`, is the required `A`-lift; uniqueness rides the same unitor. -/

/-- The underlying `A`-cone of an `A′`-cone `c` over `f g`: apex `∏c.pt`, same legs. -/
def inflConeForget {a b cc : Infl 𝒞}
    {f : listProd (𝒞 := 𝒞) a ⟶ listProd b} {g : listProd (𝒞 := 𝒞) cc ⟶ listProd b}
    (c : Cone (𝒞 := Infl 𝒞) f g) :
    Cone (𝒞 := 𝒞) (f : listProd a ⟶ listProd b) (g : listProd cc ⟶ listProd b) :=
  { pt := listProd (𝒞 := 𝒞) c.pt, π₁ := c.π₁, π₂ := c.π₂, w := c.w }

/-- An `A′`-pullback cone `c` over `f g` is an `A`-pullback cone over the same underlying cospan. -/
theorem inflIsPullback_to_isPullback {a b cc : Infl 𝒞}
    {f : listProd (𝒞 := 𝒞) a ⟶ listProd b} {g : listProd (𝒞 := 𝒞) cc ⟶ listProd b}
    (c : Cone (𝒞 := Infl 𝒞) f g) (hc : c.IsPullback (𝒞 := Infl 𝒞)) :
    Cone.IsPullback (𝒞 := 𝒞) (inflConeForget c) := by
  intro d
  -- `d : A`-cone, apex `∏d.pt`... here `d.pt` is an `A`-object `W`.  Wrap to an `A′`-cone over `[W]`.
  let W : 𝒞 := d.pt
  let dInfl : Cone (𝒞 := Infl 𝒞) f g :=
    { pt := ([W] : List 𝒞),
      π₁ := ((fst : prod W one ⟶ W) ≫ d.π₁ : listProd (𝒞 := 𝒞) [W] ⟶ listProd a),
      π₂ := ((fst : prod W one ⟶ W) ≫ d.π₂ : listProd (𝒞 := 𝒞) [W] ⟶ listProd cc),
      w := by
        show ((fst : prod W one ⟶ W) ≫ d.π₁) ≫ f = ((fst : prod W one ⟶ W) ≫ d.π₂) ≫ g
        rw [Cat.assoc, Cat.assoc, d.w] }
  obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ := hc dInfl
  -- `u : ∏[W] ⟶ c.pt`, i.e. `W×1 ⟶ ∏c.pt`.  The `A`-lift is `prodOneRightInv W ≫ u : W ⟶ ∏c.pt`.
  -- Bind the legs/lift as `A`-arrows so `hu1`/`hu2`'s compositions are read in `A` (avoiding the
  -- `A′`-vs-`A` `≫`-instance clash with the goal).
  let cπ₁ : listProd (𝒞 := 𝒞) c.pt ⟶ listProd a := c.π₁
  let cπ₂ : listProd (𝒞 := 𝒞) c.pt ⟶ listProd cc := c.π₂
  let u𝒞 : listProd (𝒞 := 𝒞) ([W] : List 𝒞) ⟶ listProd c.pt := u
  have huc1 : u𝒞 ≫ cπ₁ = (fst : prod W one ⟶ W) ≫ d.π₁ := hu1
  have huc2 : u𝒞 ≫ cπ₂ = (fst : prod W one ⟶ W) ≫ d.π₂ := hu2
  refine ⟨(prodOneRightInv W ≫ u𝒞 : W ⟶ listProd c.pt), ⟨?_, ?_⟩, ?_⟩
  · -- `(prodOneRightInv W ≫ u) ≫ c.π₁ = d.π₁`
    show (prodOneRightInv W ≫ u𝒞) ≫ cπ₁ = d.π₁
    calc (prodOneRightInv W ≫ u𝒞) ≫ cπ₁
          = prodOneRightInv W ≫ (u𝒞 ≫ cπ₁) := Cat.assoc _ _ _
      _ = prodOneRightInv W ≫ ((fst : prod W one ⟶ W) ≫ d.π₁) := by rw [huc1]
      _ = (prodOneRightInv W ≫ (fst : prod W one ⟶ W)) ≫ d.π₁ := (Cat.assoc _ _ _).symm
      _ = d.π₁ := by rw [show prodOneRightInv W ≫ fst = Cat.id W from fst_pair _ _, Cat.id_comp]
  · show (prodOneRightInv W ≫ u𝒞) ≫ cπ₂ = d.π₂
    calc (prodOneRightInv W ≫ u𝒞) ≫ cπ₂
          = prodOneRightInv W ≫ (u𝒞 ≫ cπ₂) := Cat.assoc _ _ _
      _ = prodOneRightInv W ≫ ((fst : prod W one ⟶ W) ≫ d.π₂) := by rw [huc2]
      _ = (prodOneRightInv W ≫ (fst : prod W one ⟶ W)) ≫ d.π₂ := (Cat.assoc _ _ _).symm
      _ = d.π₂ := by rw [show prodOneRightInv W ≫ fst = Cat.id W from fst_pair _ _, Cat.id_comp]
  · -- uniqueness: any `A`-lift `v : W ⟶ ∏c.pt` agreeing on both legs equals `prodOneRightInv W ≫ u`.
    intro v hv1 hv2
    have hvc1 : (v : W ⟶ listProd c.pt) ≫ cπ₁ = d.π₁ := hv1
    have hvc2 : (v : W ⟶ listProd c.pt) ≫ cπ₂ = d.π₂ := hv2
    -- wrap `v` to the `A′`-lift `vInfl : [W] ⟶ c.pt` (underlying `fst ≫ v`); `huniq` forces `= u`.
    let vInfl : listProd (𝒞 := 𝒞) ([W] : List 𝒞) ⟶ listProd c.pt := (fst : prod W one ⟶ W) ≫ v
    have hvInfl : vInfl = u𝒞 := by
      refine huniq vInfl ?_ ?_
      · show ((fst : prod W one ⟶ W) ≫ v) ≫ cπ₁ = (fst : prod W one ⟶ W) ≫ d.π₁
        calc ((fst : prod W one ⟶ W) ≫ v) ≫ cπ₁
              = (fst : prod W one ⟶ W) ≫ (v ≫ cπ₁) := Cat.assoc _ _ _
          _ = (fst : prod W one ⟶ W) ≫ d.π₁ := by rw [hvc1]
      · show ((fst : prod W one ⟶ W) ≫ v) ≫ cπ₂ = (fst : prod W one ⟶ W) ≫ d.π₂
        calc ((fst : prod W one ⟶ W) ≫ v) ≫ cπ₂
              = (fst : prod W one ⟶ W) ≫ (v ≫ cπ₂) := Cat.assoc _ _ _
          _ = (fst : prod W one ⟶ W) ≫ d.π₂ := by rw [hvc2]
    -- cancel the unitor: `v = prodOneRightInv W ≫ (fst ≫ v) = prodOneRightInv W ≫ u`.
    calc v = prodOneRightInv W ≫ ((fst : prod W one ⟶ W) ≫ v) := by
            rw [← Cat.assoc, show prodOneRightInv W ≫ fst = Cat.id W from fst_pair _ _,
              Cat.id_comp]
      _ = prodOneRightInv W ≫ vInfl := rfl
      _ = prodOneRightInv W ≫ u𝒞 := by rw [hvInfl]

/-- **§1.544 — `A′` is pre-regular** (pullbacks transfer covers), conjugating `A`'s instance across
    `A′ ≃ A`: forget the cover to `A` (`inflCover_to_cover`), forget the `A′`-pullback square to an
    `A`-pullback square (`inflIsPullback_to_isPullback`), transfer in `A`, reflect back to `A′`
    (`coverC_to_inflCover`). -/
instance inflPullbacksTransferCovers [HasEqualizers 𝒞] [PullbacksTransferCovers 𝒞] :
    PullbacksTransferCovers (Infl 𝒞) where
  pullbacks_transfer_covers {a b cc} {f} {g} c hpb hf := by
    -- `f g : ∏a ⟶ ∏b`, `∏cc ⟶ ∏b`; the underlying `A`-cone and its pullback-square / cover.
    have hf𝒞 : Cover (𝒞 := 𝒞) (f : listProd (𝒞 := 𝒞) a ⟶ listProd b) := inflCover_to_cover hf
    have hpb𝒞 : Cone.IsPullback (𝒞 := 𝒞) (inflConeForget c) :=
      inflIsPullback_to_isPullback c hpb
    have hcov𝒞 : Cover (𝒞 := 𝒞) (c.π₂ : listProd (𝒞 := 𝒞) c.pt ⟶ listProd cc) :=
      PullbacksTransferCovers.pullbacks_transfer_covers (inflConeForget c) hpb𝒞 hf𝒞
    -- `(inflConeForget c).π₂ = c.π₂`; reflect the `A`-cover back to `A′`.
    intro C m h hm hhm
    exact coverC_to_inflCover (s := c.pt) (t := cc)
      (f := (c.π₂ : listProd (𝒞 := 𝒞) c.pt ⟶ listProd cc)) hcov𝒞 m h hm hhm

/-! ### §1.544  The cross-section `infl : 𝒞 → A′` PRESERVES pullbacks (forward direction)

  Dual to `inflIsPullback_to_isPullback`: a `𝒞`-pullback cone `c` over `(f, g)`, embedded by
  `infl` (apex `[c.pt]`, legs `inflFunctor.map c.π₁/π₂`, cospan `inflFunctor.map f/g`), is an
  `A′`-pullback.  An `A′`-cone `d` over `(infl f, infl g)` is projected to `𝒞` by the unitor `fst`
  (`infl h ≫ fst = fst ≫ h`, naturality of `prodRight 1`); `c`'s `𝒞`-universal property lifts it,
  and the `A′`-lift is `u ≫ prodOneRightInv c.pt`.  The leg/uniqueness equations ride
  `fst_snd_jointly_monic` on `c.pt × 1` (the `1`-component collapses by `term_uniq`). -/

/-- Unitor naturality for the cross-section, as a `𝒞`-equation on the underlying arrow:
    `(infl h : X×1 ⟶ Y×1) ≫ fst = fst ≫ h`.  `infl h = pair (fst≫h) snd`, so this is `fst_pair`.
    The `≫` is forced to `𝒞`'s by binding `infl h` as the `𝒞`-arrow `mf`. -/
theorem inflMap_fst {X Y : 𝒞} (h : X ⟶ Y) :
    ∀ mf : prod X one ⟶ prod Y one, mf = (inflFunctor.map h : (infl X : Infl 𝒞) ⟶ infl Y) →
      mf ≫ (fst : prod Y one ⟶ Y) = (fst : prod X one ⟶ X) ≫ h := by
  intro mf hmf; subst hmf; exact fst_pair (fst ≫ h) snd

/-- The `infl`-image cone of a `𝒞`-cone `c` over `(f, g)`: apex `[c.pt]`, legs `infl c.π₁/π₂`,
    over the inflated cospan `(infl f, infl g)`. -/
def inflEmbedCone {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} (c : Cone f g) :
    Cone (𝒞 := Infl 𝒞) (inflFunctor.map f : (infl A : Infl 𝒞) ⟶ infl C)
      (inflFunctor.map g : (infl B : Infl 𝒞) ⟶ infl C) :=
  { pt := (infl c.pt : Infl 𝒞)
    π₁ := inflFunctor.map c.π₁
    π₂ := inflFunctor.map c.π₂
    w  := by rw [← inflFunctor.map_comp, ← inflFunctor.map_comp, c.w] }

/-- **`infl` preserves pullbacks (forward).**  A `𝒞`-pullback cone `c` maps to an `A′`-pullback.

    `A′`-cone `d` over `(infl f, infl g)`: legs `d.π₁ : ∏d.pt ⟶ A×1`, `d.π₂ : ∏d.pt ⟶ B×1`.  Bind
    everything as `𝒞`-arrows (`∏[X] = X×1`), project to `𝒞` by `fst` to a `𝒞`-cone over `(f, g)`,
    lift by `c`, and re-inflate the lift through `prodOneRightInv c.pt`.  All leg/uniqueness equations
    are `fst_snd_jointly_monic` on `_×1` (the `snd`/`1`-component collapses by `term_uniq`). -/
theorem infl_preserves_isPullback {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C}
    (c : Cone f g) (hc : c.IsPullback (𝒞 := 𝒞)) :
    (inflEmbedCone c).IsPullback (𝒞 := Infl 𝒞) := by
  intro d
  -- Bind cospan and legs as `𝒞`-arrows so every `≫` reads in `𝒞`.
  let If : prod A one ⟶ prod C one := inflFunctor.map f
  let Ig : prod B one ⟶ prod C one := inflFunctor.map g
  let dπ₁ : listProd (𝒞 := 𝒞) d.pt ⟶ prod A one := d.π₁
  let dπ₂ : listProd (𝒞 := 𝒞) d.pt ⟶ prod B one := d.π₂
  have hIf : If ≫ (fst : prod C one ⟶ C) = (fst : prod A one ⟶ A) ≫ f := inflMap_fst f If rfl
  have hIg : Ig ≫ (fst : prod C one ⟶ C) = (fst : prod B one ⟶ B) ≫ g := inflMap_fst g Ig rfl
  let p₁ : listProd (𝒞 := 𝒞) d.pt ⟶ A := dπ₁ ≫ (fst : prod A one ⟶ A)
  let p₂ : listProd (𝒞 := 𝒞) d.pt ⟶ B := dπ₂ ≫ (fst : prod B one ⟶ B)
  have hdw : dπ₁ ≫ If = dπ₂ ≫ Ig := d.w
  have hpw : p₁ ≫ f = p₂ ≫ g := by
    show (dπ₁ ≫ fst) ≫ f = (dπ₂ ≫ fst) ≫ g
    rw [Cat.assoc, Cat.assoc, ← hIf, ← hIg, ← Cat.assoc, ← Cat.assoc, hdw]
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc ⟨listProd (𝒞 := 𝒞) d.pt, p₁, p₂, hpw⟩
  -- The `A′`-lift is `U := u ≫ prodOneRightInv c.pt : ∏d.pt ⟶ c.pt×1`.
  let U : listProd (𝒞 := 𝒞) d.pt ⟶ prod c.pt one := u ≫ prodOneRightInv c.pt
  have hUfst : U ≫ (fst : prod c.pt one ⟶ c.pt) = u := by
    show (u ≫ prodOneRightInv c.pt) ≫ (fst : prod c.pt one ⟶ c.pt) = u
    rw [Cat.assoc, show prodOneRightInv c.pt ≫ fst = Cat.id c.pt from fst_pair _ _, Cat.comp_id]
  -- `U ≫ infl c.π_i = d.π_i` by joint monicity on `_×1`: `fst`-leg is `u ≫ c.π_i = p_i`, `snd`→`term`.
  have hUleg : ∀ {Z : 𝒞} (k : c.pt ⟶ Z) (Ik : prod c.pt one ⟶ prod Z one)
      (e : listProd (𝒞 := 𝒞) d.pt ⟶ prod Z one),
      Ik = (inflFunctor.map k : (infl c.pt : Infl 𝒞) ⟶ infl Z) →
      u ≫ k = e ≫ (fst : prod Z one ⟶ Z) → U ≫ Ik = e := by
    intro Z k Ik e hIk hk
    apply fst_snd_jointly_monic
    · -- `fst`: `(U ≫ Ik) ≫ fst = (U ≫ fst) ≫ k = u ≫ k = e ≫ fst`.
      rw [Cat.assoc, inflMap_fst k Ik hIk, ← Cat.assoc, hUfst, hk]
    · exact term_uniq _ _
  refine ⟨U, ⟨hUleg c.π₁ (inflFunctor.map c.π₁) dπ₁ rfl hu₁,
              hUleg c.π₂ (inflFunctor.map c.π₂) dπ₂ rfl hu₂⟩, ?_⟩
  -- uniqueness: any `A′`-lift `v` agreeing on both legs equals `U` (its `fst`-part is the unique `𝒞`-lift).
  intro v hv₁ hv₂
  let v𝒞 : listProd (𝒞 := 𝒞) d.pt ⟶ prod c.pt one := v
  let Iπ₁ : prod c.pt one ⟶ prod A one := inflFunctor.map c.π₁
  let Iπ₂ : prod c.pt one ⟶ prod B one := inflFunctor.map c.π₂
  have hvI₁ : v𝒞 ≫ Iπ₁ = dπ₁ := hv₁
  have hvI₂ : v𝒞 ≫ Iπ₂ = dπ₂ := hv₂
  have hIπ₁ : Iπ₁ ≫ (fst : prod A one ⟶ A) = (fst : prod c.pt one ⟶ c.pt) ≫ c.π₁ :=
    inflMap_fst c.π₁ Iπ₁ rfl
  have hIπ₂ : Iπ₂ ≫ (fst : prod B one ⟶ B) = (fst : prod c.pt one ⟶ c.pt) ≫ c.π₂ :=
    inflMap_fst c.π₂ Iπ₂ rfl
  have hvfst₁ : (v𝒞 ≫ (fst : prod c.pt one ⟶ c.pt)) ≫ c.π₁ = p₁ := by
    rw [Cat.assoc, ← hIπ₁, ← Cat.assoc, hvI₁]
  have hvfst₂ : (v𝒞 ≫ (fst : prod c.pt one ⟶ c.pt)) ≫ c.π₂ = p₂ := by
    rw [Cat.assoc, ← hIπ₂, ← Cat.assoc, hvI₂]
  have hvu : v𝒞 ≫ (fst : prod c.pt one ⟶ c.pt) = u := huniq _ hvfst₁ hvfst₂
  -- `v = U` by joint monicity: `fst`-leg is `v ≫ fst = u = U ≫ fst`, `snd`-leg forced by `term`.
  show v𝒞 = U
  apply fst_snd_jointly_monic
  · show v𝒞 ≫ (fst : prod c.pt one ⟶ c.pt) = U ≫ (fst : prod c.pt one ⟶ c.pt)
    rw [hvu, hUfst]
  · exact term_uniq _ _

/-- **The §1.547 inner transition preserves covers** (`hcovpres`): the concatenation map `catMap d f`
    is a cover whenever `f` is, since `catMap d f` is a pullback of `f` (`catMap_isPullback`) and `A′`
    transfers covers (`inflPullbacksTransferCovers`). -/
theorem catMap_cover [HasEqualizers 𝒞] [PullbacksTransferCovers 𝒞] {s t : List 𝒞} (d : List 𝒞)
    {f : listProd (𝒞 := 𝒞) s ⟶ listProd t} (hf : Cover (𝒞 := Infl 𝒞) f) :
    Cover (𝒞 := Infl 𝒞) (catMap d f) :=
  inflPullbacksTransferCovers.pullbacks_transfer_covers (catMapCone d f)
    (catMap_isPullback d f) hf

/-- **The §1.547 inner transition preserves monos**: `catMap d` carries an `A′`-mono to an `A′`-mono.
    Forgetting to `A` (`inflMono_to_mono`), `cat_jointly_monic s d` reduces `Monic (catMap d m)` to
    cancelling `m` on the `catForget t d`-part (via `catMap_forget`) and the trivial `catTail` part. -/
theorem catMap_mono {s t : List 𝒞} (d : List 𝒞) {m : listProd (𝒞 := 𝒞) s ⟶ listProd t}
    (hm : Monic (𝒞 := Infl 𝒞) m) : Monic (𝒞 := Infl 𝒞) (catMap d m) := by
  -- work entirely in `A`: forget the `A′`-mono to an `A`-mono (`inflMono_to_mono`).
  have hm𝒞 : Monic (𝒞 := 𝒞) m := inflMono_to_mono hm
  intro W p0 q0 hpq
  -- bind the legs as `A`-arrows so all compositions read in `A` (avoid the `A′`/`A` `≫` clash).
  let p : listProd (𝒞 := 𝒞) W ⟶ listProd (s ++ d) := p0
  let q : listProd (𝒞 := 𝒞) W ⟶ listProd (s ++ d) := q0
  have hpq' : p ≫ catMap d m = q ≫ catMap d m := hpq
  show p = q
  apply cat_jointly_monic s d (X := listProd (𝒞 := 𝒞) W)
  · -- forget: cancel `m` (mono in `A`) after post-composing `catForget t d`.
    refine hm𝒞 (W := listProd (𝒞 := 𝒞) W) (p ≫ catForget s d) (q ≫ catForget s d) ?_
    rw [Cat.assoc, Cat.assoc, ← catMap_forget d m, ← Cat.assoc, ← Cat.assoc, hpq']
  · -- tail: post-compose `catTail t d`, which `catMap d m` carries to `catTail s d`.
    show p ≫ catTail s d = q ≫ catTail s d
    rw [← catMap_tail (d := d) m, ← Cat.assoc, ← Cat.assoc, hpq']

/-- **§1.544 — `A′` is pre-regular** (Cartesian + pullbacks transfer covers).  `PreRegularCategory 𝒞`
    supplies products + pullbacks, hence equalizers (`products_pullbacks_implies_equalizers`), which
    `A′`'s pullback / transfer instances consume.  This is the instance `RelativeCapitalization` /
    `Capitalization` consume to run `overPreRegular` per inflation stage. -/
instance inflPreRegular [PreRegularCategory 𝒞] : PreRegularCategory (Infl 𝒞) :=
  letI : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
  { toHasTerminal := inflHasTerminal
    toHasBinaryProducts := inflHasBinaryProducts
    toHasPullbacks := inflHasPullbacks
    toPullbacksTransferCovers := inflPullbacksTransferCovers }

/-! ### `A′` has images

  The objects of `A′ = List 𝒞` are the finite products `∏s`, but EVERY `A`-object `J` is itself
  `∏[J] = J × 1` up to the unitor `fst : J×1 ≅ J` (`prod_one_iso_right`).  So the `A`-image
  `∏s ─image.lift→ J ─(image f).arr↣ ∏t` of `f : ∏s ⟶ ∏t` becomes an `A′`-image with object the
  SINGLETON `[J]`: the `A′`-mono is `fst ≫ (image f).arr : ∏[J] = J×1 ⟶ ∏t` (mono in `A` ⟹ mono in
  `A′`, `A′`'s test objects being a subset of `A`'s), and the cover leg is
  `image.lift f ≫ prodOneRightInv J : ∏s ⟶ J×1`
  (a cover post-composed with the iso `prodOneRightInv J`).  Mirrors `inflHasEqualizers`' singleton
  pattern; cover-then-mono is an image (`coverMono_isImage`, needs only `A′`-pullbacks). -/

/-- The `A`-arrow `fst ≫ m` (`J×1 ⟶ ∏t`) is monic when `m : J ↣ ∏t` is (`fst` iso, cancel via
    `prodOneRightInv J`).  Same unitor-cancellation as `inflCover_to_cover`'s `hm𝒞`. -/
theorem fst_comp_monic {J : 𝒞} {Z : 𝒞} {m : J ⟶ Z} (hm : Monic m) :
    Monic ((fst : prod J one ⟶ J) ≫ m) := by
  intro W p q hpq
  have h1 : (p ≫ (fst : prod J one ⟶ J)) ≫ m = (q ≫ (fst : prod J one ⟶ J)) ≫ m := by
    rw [Cat.assoc, Cat.assoc]; exact hpq
  have h2 : p ≫ (fst : prod J one ⟶ J) = q ≫ (fst : prod J one ⟶ J) := hm _ _ h1
  have := congrArg (fun u => u ≫ prodOneRightInv J) h2
  simpa only [Cat.assoc, fst_prodOneRightInv, Cat.comp_id] using this

/-- The image of `f : s ⟶ t` in `A′` (i.e. of `f : ∏s ⟶ ∏t` in `A`): the SINGLETON `[J]` of the
    `A`-image object `J := (image f).dom`, with `A′`-mono `fst ≫ (image f).arr : ∏[J] = J×1 ⟶ ∏t`. -/
noncomputable def inflImage [RegularCategory 𝒞] {s t : Infl 𝒞}
    (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) : Subobject (Infl 𝒞) t :=
  let f' : listProd (𝒞 := 𝒞) s ⟶ listProd t := f
  let J : 𝒞 := (image (𝒞 := 𝒞) f').dom
  Subobject.mk (𝒞 := Infl 𝒞) ([J] : List 𝒞)
    ((fst : prod J one ⟶ J) ≫ (image (𝒞 := 𝒞) f').arr :
      listProd (𝒞 := 𝒞) ([J] : List 𝒞) ⟶ listProd t)
    (by
      intro V p q hpq
      exact fst_comp_monic (image (𝒞 := 𝒞) f').monic (W := listProd (𝒞 := 𝒞) V) p q hpq)

/-- `inflImage f` is the image of `f` in `A′`: cover-then-mono factorization (`coverMono_isImage`).
    Cover leg `image.lift f ≫ prodOneRightInv J : ∏s ⟶ J×1` (cover · iso = cover, `cover_comp_iso_cat`),
    mono leg `fst ≫ (image f).arr`; their composite is `f` (the unitor projection law). -/
theorem inflImage_isImage [RegularCategory 𝒞] {s t : Infl 𝒞}
    (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    IsImage (𝒞 := Infl 𝒞) (A := s) (B := t) f (inflImage f) := by
  letI : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
  letI : HasPullbacks (Infl 𝒞) := inflHasPullbacks
  let f' : listProd (𝒞 := 𝒞) s ⟶ listProd t := f
  let J : 𝒞 := (image (𝒞 := 𝒞) f').dom
  -- cover leg in `A` (= in `A′`, same underlying arrow): `image.lift f ≫ prodOneRightInv J`.
  let e : listProd (𝒞 := 𝒞) s ⟶ listProd ([J] : List 𝒞) :=
    image.lift (𝒞 := 𝒞) f' ≫ prodOneRightInv J
  -- `e` is an `A`-cover (cover `image.lift` post-composed with the iso `prodOneRightInv J`),
  -- hence an `A′`-cover on the same underlying arrow (`coverC_to_inflCover`).
  have hcov𝒞 : Cover (𝒞 := 𝒞) e :=
    cover_comp_iso_cat (Colim.image_lift_cover_local f')
      ⟨_, fst_pair _ _, fst_prodOneRightInv⟩
  have hcov : Cover (𝒞 := Infl 𝒞) (X := s) (Y := ([J] : List 𝒞)) e :=
    coverC_to_inflCover (s := s) (t := ([J] : List 𝒞)) (f := e) hcov𝒞
  -- `e ≫ m = f` (the singleton mono `m = fst ≫ (image f).arr`), via the unitor projection law.
  have hfac : @Eq (listProd (𝒞 := 𝒞) s ⟶ listProd t) (e ≫ (inflImage f).arr) f := by
    show (image.lift (𝒞 := 𝒞) f' ≫ prodOneRightInv J)
        ≫ ((fst : prod J one ⟶ J) ≫ (image (𝒞 := 𝒞) f').arr) = f'
    rw [← Cat.assoc, Cat.assoc (image.lift (𝒞 := 𝒞) f'),
      show prodOneRightInv J ≫ fst = Cat.id J from fst_pair _ _, Cat.comp_id,
      image.lift_fac]
  exact Colim.coverMono_isImage (𝒞 := Infl 𝒞) (inflImage f).monic hcov hfac

/-- **`A′` has images** when `A` is regular.  See `inflImage`. -/
noncomputable instance inflHasImages [RegularCategory 𝒞] : HasImages (Infl 𝒞) where
  image f := inflImage f
  isImage f := inflImage_isImage f

/-- **`A′` is regular** when `A` is.  Pre-regular (`inflPreRegular`) plus images (`inflHasImages`). -/
noncomputable instance inflRegular [RegularCategory 𝒞] : RegularCategory (Infl 𝒞) where

/-! ### The single-factor slice base-change `A′/V → A′/(V ++ [B])`

  The §1.547 inner transition for appending ONE factor `B`.  On the inflation it is STRICT: an
  object `⟨s, h : ∏s ⟶ ∏V⟩` of `A′/V` maps to `⟨s ++ [B], appendMap B h⟩` of `A′/(V++[B])` — `h`
  extended by the identity on the appended `B` (`appendMap`), with the over-hom triangle and functor
  laws coming straight from `appendMap_proj`/`appendMap_id`/`appendMap_comp`.  This is base-change
  along the strict projection `∏(V++[B]) ⟶ ∏V`, realized by concatenation — no pullback, no iso. -/

/-- The single-factor slice base-change object map `A′/V → A′/(V++[B])`, `⟨s,h⟩ ↦ ⟨s++[B], appendMap B h⟩`.
    The structure map `appendMap B h : ∏(s++[B]) ⟶ ∏(V++[B])` extends `h` by `id` on the `B`-factor. -/
def sliceAppendObj (B : 𝒞) {V : Infl 𝒞} (X : Over (B := V)) : Over (B := (V ++ [B] : List 𝒞)) :=
  { dom := (X.dom ++ [B] : List 𝒞),
    hom := (appendMap B X.hom : listProd (𝒞 := 𝒞) (X.dom ++ [B]) ⟶ listProd (V ++ [B])) }

/-- The single-factor slice base-change morphism map: an over-hom `g : X ⟶ Y` (i.e. `g.f ≫ Y.hom =
    X.hom`) maps to `appendMap B g.f`, whose triangle `appendMap B g.f ≫ appendMap B Y.hom =
    appendMap B X.hom` is `appendMap_comp` applied to `g.f ≫ Y.hom = X.hom`. -/
def sliceAppendMap (B : 𝒞) {V : Infl 𝒞} {X Y : Over (B := V)} (g : OverHom X Y) :
    OverHom (sliceAppendObj B X) (sliceAppendObj B Y) :=
  { f := appendMap B g.f,
    w := by
      show appendMap B g.f ≫ appendMap B Y.hom = appendMap B X.hom
      rw [← appendMap_comp]; exact congrArg (appendMap B) g.w }

/-- **The single-factor slice base-change is a STRICT functor `A′/V → A′/(V++[B])`.**  Object map
    `sliceAppendObj B`, morphism map `sliceAppendMap B`; laws from `appendMap_id`/`appendMap_comp`. -/
def sliceAppendFunctor (B : 𝒞) (V : Infl 𝒞) :
    @Functor (Over (B := V)) (Over (B := (V ++ [B] : List 𝒞))) (overCat V)
      (overCat (V ++ [B] : List 𝒞)) where
  obj := sliceAppendObj B
  map {X Y} g := sliceAppendMap B g
  map_id X := OverHom.ext (by
    show appendMap B (Cat.id (listProd X.dom)) = Cat.id (listProd (X.dom ++ [B]))
    exact appendMap_id X.dom B)
  map_comp {X Y Z} g h := OverHom.ext (by
    show appendMap B (g.f ≫ h.f) = appendMap B g.f ≫ appendMap B h.f
    exact appendMap_comp B g.f h.f)

/-! ### The whole-suffix slice base-change `A′/V → A′/(V ++ d)` (the §1.547 inner transition)

  The genuine multi-factor §1.547 inner transition: for a finite suffix `d` (the factors of `U`
  not in `V`, when `U = V ++ d`), base-change `A′/V → A′/(V++d)` realized by concatenating `d` —
  `⟨s, h⟩ ↦ ⟨s ++ d, catMap d h⟩`.  STRICT (concatenation, not pullback): the over-hom triangle and
  functor laws are `catMap_tail`/`catMap_id`/`catMap_comp`.  This is the building block of the strict
  inner directed system; the transition for `V ⊑ U` takes `d := U.drop V.length` (computable suffix
  DATA from the objects — this is what dissolves residual (A), the `Prop`-no-large-elim wall, since
  the suffix comes from the list objects, not from the inclusion proof). -/

/-- The whole-suffix slice base-change object map `A′/V → A′/(V++d)`, `⟨s,h⟩ ↦ ⟨s++d, catMap d h⟩`. -/
def sliceCatObj (d : List 𝒞) {V : Infl 𝒞} (X : Over (B := V)) : Over (B := (V ++ d : List 𝒞)) :=
  { dom := (X.dom ++ d : List 𝒞),
    hom := (catMap d X.hom : listProd (𝒞 := 𝒞) (X.dom ++ d) ⟶ listProd (V ++ d)) }

/-- The whole-suffix slice base-change morphism map: `g ↦ catMap d g.f`, triangle from `catMap_comp`. -/
def sliceCatMap (d : List 𝒞) {V : Infl 𝒞} {X Y : Over (B := V)} (g : OverHom X Y) :
    OverHom (sliceCatObj d X) (sliceCatObj d Y) :=
  { f := catMap d g.f,
    w := by
      show catMap d g.f ≫ catMap d Y.hom = catMap d X.hom
      rw [← catMap_comp]; exact congrArg (catMap d) g.w }

/-- **The whole-suffix slice base-change is a STRICT functor `A′/V → A′/(V++d)`.**  The §1.547 inner
    directed transition realized by concatenation; laws from `catMap_id`/`catMap_comp`.  Sorry-free. -/
def sliceCatFunctor (d : List 𝒞) (V : Infl 𝒞) :
    @Functor (Over (B := V)) (Over (B := (V ++ d : List 𝒞))) (overCat V)
      (overCat (V ++ d : List 𝒞)) where
  obj := sliceCatObj d
  map {X Y} g := sliceCatMap d g
  map_id X := OverHom.ext (by
    show catMap d (Cat.id (listProd X.dom)) = Cat.id (listProd (X.dom ++ d))
    exact catMap_id X.dom d)
  map_comp {X Y Z} g h := OverHom.ext (by
    show catMap d (g.f ≫ h.f) = catMap d g.f ≫ catMap d h.f
    exact catMap_comp d g.f h.f)

/-- **The strict slice transition PRESERVES the terminal object** (a down-payment on the (B-package)
    preservation hyps).  The slice terminal of `A′/V` is `⟨V, id V⟩` (`overTerm`); the append functor
    sends it to `⟨V++d, catMap d (id V)⟩ = ⟨V++d, id (V++d)⟩` (`catMap_id`), the slice terminal of
    `A′/(V++d)`.  So `sliceCatFunctor d V` carries `1_{A′/V}` to `1_{A′/(V++d)}` on the nose. -/
theorem sliceCatObj_terminal (d : List 𝒞) (V : Infl 𝒞) :
    sliceCatObj d (overTerm V) = overTerm (V ++ d : List 𝒞) := by
  show (⟨(V ++ d : List 𝒞), catMap d (Cat.id (listProd V))⟩ : Over (B := (V ++ d : List 𝒞)))
      = ⟨(V ++ d : List 𝒞), Cat.id (listProd (V ++ d))⟩
  rw [catMap_id]

/-! ## §1.547  The STRICT inner directed system of inflation slices

  The §1.547 inner directed system, now STRICT thanks to the inflation.  Index: `List 𝒞` (factor
  sequences) under the prefix order `V ⊑ U` (`List.IsPrefix`, a `Prop`).  Stage `w` is the slice
  `A′/w`; the transition `A′/V → A′/U` for `V ⊑ U` appends the suffix `d := U.drop V.length` (DATA
  recovered from the objects by `List.drop` — dissolving residual (A), the old `Prop`-no-large-elim
  wall, since the suffix comes from the list `U`, not from the inclusion proof) via the strict
  `sliceCatObj`/`sliceCatFunctor`.

  STRICTNESS STATUS.  The transition functor `sliceCatFunctor d`/`sliceCatObj d` is Sorry-free and
  STRICT (no pullback, no iso — concatenation).  The `CatSystem` LAWS reduce to the propositional
  list identities `V ++ [] = V` (`List.append_nil`) and `(V++d)++e = V++(d++e)` (`List.append_assoc`):
  these are genuine equalities of list OBJECTS — exactly the strictness raw base-change LACKS (where
  `baseChangeObj (id) X` is only iso to `X`) — but, because list append is not *definitionally*
  unital/associative for variable lists, the stage objects `A′/(V++d)` must be TRANSPORTED along them.

    * `F_refl` — `innerSliceTr_refl` — PROVEN Sorry-free (only `propext`): the empty-suffix
      transition is the identity on `A′/V`, via `over_transport_ext` + `catMap_nil_heq` (the latter a
      full `HEq` discharge of the `append_nil` reindexing through `catForget`/`catArrange`).
    * `F_trans` — `innerSliceTr_trans` — PROVEN Sorry-free (only `propext`): reduces to
      `prefixSuffix_trans` plus `catMap_append_heq` (the `(s++d)++e = s++(d++e)` reindexing of `catMap`,
      also PROVEN), the doubled-`▸` nested transport across `List.append_assoc` fully discharged.

  So residual (A) (the `Prop`→suffix DATA wall) is DISSOLVED here by `List.drop`/`prefixSuffix`, and
  residual (B-strict) (strictness) is supplied by the inflation's object-level `concat_assoc`/
  `concat_nil` — the genuine §1.544 advance over base-change.  BOTH inner-system laws are now closed;
  the directed lift is `chainSliceSystem` (final block). -/

/-- The §1.547 inner index: `List 𝒞` ordered by the prefix relation `V ⊑ U` (`List.IsPrefix`).
    Directed: the common bound of `V, U` is... not generally a prefix-bound — so we restrict to
    the sub-order generated by appends from a common base, but for the index `Directed` we use the
    append-prefix structure with bound `V ++ U`-style only when comparable.  Here we expose the
    prefix preorder; directedness on the relevant sub-poset (chains of appends) is immediate. -/
def prefixLe (V U : List 𝒞) : Prop := V <+: U

/-- The appended suffix `d` with `V ++ d = U`, recovered as DATA from the objects (`List.drop`),
    valid given the prefix proof.  This is the choice-free transition base (residual (A) dissolved). -/
def prefixSuffix (V U : List 𝒞) : List 𝒞 := U.drop V.length

theorem prefixSuffix_eq {V U : List 𝒞} (h : prefixLe V U) : V ++ prefixSuffix V U = U :=
  List.prefix_iff_eq_append.mp h

/-- The inner stage object family: stage `w` is the slice `A′/w`. -/
def innerSliceObj (w : List 𝒞) : Type u := Over (B := (w : Infl 𝒞))

instance innerSliceCat (w : List 𝒞) : Cat.{u} (innerSliceObj (𝒞 := 𝒞) w) := overCat (w : Infl 𝒞)

/-- The inner transition object map `A′/V → A′/U` for `V ⊑ U`: append the suffix `U.drop V.length`
    (`sliceCatObj`), then TRANSPORT along `V ++ suffix = U` to land in `A′/U`.  Strict (concatenation). -/
def innerSliceTr {V U : List 𝒞} (h : prefixLe V U) (X : innerSliceObj (𝒞 := 𝒞) V) :
    innerSliceObj (𝒞 := 𝒞) U :=
  (prefixSuffix_eq h) ▸ (sliceCatObj (prefixSuffix V U) X)

/-- `catMap [] f` is `f` modulo the (propositional) `s ++ [] = s` reindexing: `catMap [] f`,
    transported along `append_nil` on both ends, is `f`.  Component lemma for `F_refl`. -/
theorem catTail_nil (s : List 𝒞) : catTail (𝒞 := 𝒞) s [] = term _ := by
  induction s with
  | nil => exact term_uniq _ _
  | cons a s' ih =>
      show (snd : prod a (listProd (s' ++ [])) ⟶ _) ≫ catTail s' [] = term _
      rw [ih]; exact term_uniq _ _

/-- `listProd (s ++ []) = listProd s` as a TYPE-level equality (from `s ++ [] = s`). -/
theorem listProd_append_nil (s : List 𝒞) : listProd (𝒞 := 𝒞) (s ++ []) = listProd s := by
  rw [List.append_nil]

/-- Cons-step kernel for `catForget_nil_heq`: GIVEN a product reindexing `P = ∏s'` and a forget map
    `cf : P ⟶ ∏s'` that is HEq the identity, the `pair fst (snd ≫ cf)` is HEq `id (∏(a::s'))`.
    Stated with `P`, `cf` abstract so the dependent reindexing can be `subst`-ed cleanly. -/
theorem catForget_cons_kernel {a : 𝒞} {s' : List 𝒞} {P : 𝒞} (hP : P = listProd (𝒞 := 𝒞) s')
    (cf : P ⟶ listProd (𝒞 := 𝒞) s') (hcf : HEq cf (Cat.id (listProd (𝒞 := 𝒞) s'))) :
    HEq (pair (fst : prod a P ⟶ a) ((snd : prod a P ⟶ P) ≫ cf))
        (Cat.id (listProd (𝒞 := 𝒞) (a :: s'))) := by
  subst hP
  rw [eq_of_heq hcf, Cat.comp_id]
  exact heq_of_eq pair_fst_snd

/-- Pairing kernel: given `P = B` and a second component `c : X ⟶ P` HEq `g ≫ snd : X ⟶ B`, the pair
    `pair (g ≫ fst) c` is HEq `g` (after `subst`, `c = g ≫ snd`, so `pair (g≫fst)(g≫snd) = g`). -/
theorem pair_snd_kernel {X A B P : 𝒞} (hP : P = B) (g1 : X ⟶ A)
    (c : X ⟶ P) (g2 : X ⟶ B) (hc : HEq c g2) :
    HEq (pair g1 c) (pair g1 g2) := by
  subst hP; cases hc; rfl

/-- Kernel for `catForget_comp_nil_heq`: given `P = ∏s` and `cf : P ⟶ ∏s` HEq `id`, the composite
    `cf ≫ f` is HEq `f` (after `subst`, `cf = id`, so `cf ≫ f = id ≫ f = f`). -/
theorem catForget_comp_kernel {s t : List 𝒞} {P : 𝒞} (hP : P = listProd (𝒞 := 𝒞) s)
    (cf : P ⟶ listProd (𝒞 := 𝒞) s) (hcf : HEq cf (Cat.id (listProd (𝒞 := 𝒞) s)))
    (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) : HEq (cf ≫ f) f := by
  subst hP
  rw [eq_of_heq hcf, Cat.id_comp]

/-- `catForget s []` HEq `id` — forgetting an empty suffix is the identity (up to `s++[]=s`).
    Induction; the cons step delegates the dependent reindexing to `catForget_cons_kernel`. -/
theorem catForget_nil_heq : ∀ (s : List 𝒞),
    HEq (catForget (𝒞 := 𝒞) s []) (Cat.id (listProd (𝒞 := 𝒞) s))
  | [] => by
      have : catForget (𝒞 := 𝒞) [] [] = Cat.id (listProd (𝒞 := 𝒞) []) := term_uniq _ _
      rw [this]
  | a :: s' => by
      have hf : catForget (𝒞 := 𝒞) (a :: s') []
          = pair (fst : prod a (listProd (s' ++ [])) ⟶ a)
                 ((snd : prod a (listProd (s' ++ [])) ⟶ _) ≫ catForget s' []) := rfl
      rw [hf]
      exact catForget_cons_kernel (listProd_append_nil s') (catForget s' []) (catForget_nil_heq s')

/-- `catArrange t [] g b` HEq `g` — assembling into `∏(t++[])` with an empty appended suffix is the
    `∏t`-part `g` (the `b : X ⟶ ∏[] = X ⟶ 1` part is the forced terminator).  Induction on `t`. -/
theorem catArrange_nil_heq : ∀ (t : List 𝒞) {X : 𝒞}
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd (𝒞 := 𝒞) ([] : List 𝒞)),
    HEq (catArrange t [] g b) g
  | [],      X, g, b => by
      -- `catArrange [] [] g b = b : X ⟶ ∏[] = X ⟶ 1`; and `g : X ⟶ ∏[] = X ⟶ 1`; both into `1`.
      show HEq b g; rw [term_uniq b g]
  | a :: t', X, g, b => by
      -- `catArrange (a::t') [] g b = pair (g≫fst) (catArrange t' [] (g≫snd) b)`; IH on the tail.
      have hf : catArrange (a :: t') [] g b
          = pair (g ≫ (fst : prod a (listProd t') ⟶ a))
                 (catArrange t' [] (g ≫ (snd : prod a (listProd t') ⟶ listProd t')) b) := rfl
      rw [hf]
      -- second component HEq `g ≫ snd` (across `∏(t'++[]) = ∏t'`); kernel-substitute then the eta law.
      refine HEq.trans (pair_snd_kernel (listProd_append_nil t') (g ≫ fst)
        (catArrange t' [] (g ≫ snd) b) (g ≫ snd) (catArrange_nil_heq t' (g ≫ snd) b)) ?_
      rw [← pair_uniq _ _ _ rfl rfl]

/-- `catForget s [] ≫ f` HEq `f` (`catForget s [] ≍ id`, so the composite is `id ≫ f = f`).
    Generalizes the reindexed domain of `catForget s []` and substitutes, as in the cons kernel. -/
theorem catForget_comp_nil_heq {s t : List 𝒞} (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    HEq (catForget (𝒞 := 𝒞) s [] ≫ f) f :=
  catForget_comp_kernel (listProd_append_nil s) (catForget s []) (catForget_nil_heq s) f

/-- **`catMap [] f` HEq `f`** — the empty appended suffix changes nothing (up to `s++[]=s`, `t++[]=t`).
    `catMap [] f = catArrange t [] (catForget s [] ≫ f) (catTail s [])`; `catArrange_nil_heq` strips
    the empty assemble, `catForget_nil_heq` makes `catForget s [] ≍ id`, leaving `id ≫ f = f`. -/
theorem catMap_nil_heq {s t : List 𝒞} (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    HEq (catMap [] f) f := by
  show HEq (catArrange t [] (catForget s [] ≫ f) (catTail s [])) f
  refine HEq.trans (catArrange_nil_heq t (catForget s [] ≫ f) (catTail s [])) ?_
  -- `catForget s [] ≫ f ≍ id ≫ f = f`; thread `catForget_nil_heq` through `≫ f`.
  exact catForget_comp_nil_heq f

/-- Generic `Over`-transport (in ANY category `𝒟`): if `e : B = B'`, `hd : X.dom = Y.dom`, and the
    homs agree (`HEq`), then `e ▸ X = Y`.  Componentwise extensionality for the inner-system laws. -/
theorem over_transport_ext {𝒟 : Type u} [Cat.{u} 𝒟] {B B' : 𝒟} (e : B = B')
    {X : Over B} {Y : Over B'} (hd : X.dom = Y.dom) (hh : HEq X.hom Y.hom) : e ▸ X = Y := by
  subst e
  obtain ⟨xd, xh⟩ := X; obtain ⟨yd, yh⟩ := Y
  cases hd; cases hh; rfl

/-- **`F_refl` for the strict inner system** — the empty-suffix transition is the identity on `A′/V`
    (modulo `V ++ [] = V`).  Reduces to `over_transport_ext` + `catMap_nil_heq`. -/
theorem innerSliceTr_refl {V : List 𝒞} (X : innerSliceObj (𝒞 := 𝒞) V) :
    innerSliceTr (List.prefix_refl V) X = X := by
  unfold innerSliceTr
  apply over_transport_ext
  · -- dom: `(sliceCatObj suffix X).dom = X.dom`, i.e. `X.dom ++ V.drop V.length = X.dom`.
    show X.dom ++ prefixSuffix V V = X.dom
    rw [prefixSuffix, List.drop_length, List.append_nil]
  · -- hom: `catMap (V.drop V.length) X.hom` HEq `X.hom`.
    show HEq (catMap (prefixSuffix V V) X.hom) X.hom
    rw [prefixSuffix, List.drop_length]
    exact catMap_nil_heq X.hom

/-- Suffix concatenation: for `V ⊑ U ⊑ W`, the `V`→`W` suffix is the `V`→`U` suffix appended with
    the `U`→`W` suffix.  (From `W = V ++ dVU ++ dUW`, so `W.drop V.length = dVU ++ dUW`.) -/
theorem prefixSuffix_trans {V U W : List 𝒞} (hVU : prefixLe V U) (hUW : prefixLe U W) :
    prefixSuffix V W = prefixSuffix V U ++ prefixSuffix U W := by
  have e1 : V ++ prefixSuffix V U = U := prefixSuffix_eq hVU
  have e2 : U ++ prefixSuffix U W = W := prefixSuffix_eq hUW
  have e3 : V ++ (prefixSuffix V U ++ prefixSuffix U W) = W := by
    rw [← List.append_assoc, e1, e2]
  -- `prefixSuffix V W = W.drop V.length`; with `W = V ++ (dVU++dUW)`, `drop` strips the `V`-prefix.
  have key : W.drop V.length = (V ++ (prefixSuffix V U ++ prefixSuffix U W)).drop V.length := by
    rw [e3]
  show W.drop V.length = _
  rw [key, List.drop_left]

/-! ### Associativity bridges for `catForget`/`catTail`/`catArrange` across `(x++d)++e = x++(d++e)`

  The §1.547 `F_trans` law needs `catMap (d++e) f ≍ catMap e (catMap d f)`: appending the suffix
  `d++e` equals appending `d` then `e`, modulo the strict-but-not-definitional reindexing
  `(x++d)++e = x++(d++e)` (`List.append_assoc`).  We discharge it through three HEq "bridges" — one
  per recursive concatenation map — each proved by induction on the BASE list `x`/`t`, delegating the
  dependent product reindexing to a `subst`-kernel exactly as `catForget_nil_heq` did for `append_nil`.
  All three are honest theorems (the equation holds on the nose; only the `HEq`/`▸` bookkeeping is
  nontrivial). -/

/-- Generic cons-step kernel: `pair fst (snd ≫ ·)` preserves HEq across a domain reindexing `Q = P`.
    Given `u : P ⟶ R`, `v : Q ⟶ R` with `u ≍ v`, the cons-pairs over `prod a P` / `prod a Q` are HEq.
    `subst`s the reindexing so both `snd`s land in the same type, then the HEq becomes plain. -/
theorem pair_fst_snd_heq {a R P Q : 𝒞} (hPQ : Q = P)
    (u : P ⟶ R) (v : Q ⟶ R) (huv : HEq u v) :
    HEq (pair (fst : prod a P ⟶ a) ((snd : prod a P ⟶ P) ≫ u))
        (pair (fst : prod a Q ⟶ a) ((snd : prod a Q ⟶ Q) ≫ v)) := by
  subst hPQ; cases huv; rfl

/-- **Bridge A.**  `catForget x (d++e) ≍ catForget (x++d) e ≫ catForget x d` — forgetting the suffix
    `d++e` in one go equals forgetting `e` then `d` (modulo `(x++d)++e = x++(d++e)`).  Induction on `x`. -/
theorem catForget_append_heq : ∀ (x d e : List 𝒞),
    HEq (catForget (𝒞 := 𝒞) x (d ++ e))
        (catForget (𝒞 := 𝒞) (x ++ d) e ≫ catForget (𝒞 := 𝒞) x d)
  | [],      d, e => by
      -- both sides `∏(d++e) ⟶ 1` (since `[]++(d++e) = ([]++d)++e = d++e`); into terminal.
      show HEq (catForget (𝒞 := 𝒞) [] (d ++ e))
               (catForget (𝒞 := 𝒞) ([] ++ d) e ≫ catForget (𝒞 := 𝒞) [] d)
      rw [term_uniq (catForget [] (d ++ e)) (catForget ([] ++ d) e ≫ catForget [] d)]
  | a :: x', d, e => by
      -- LHS unfolds to a cons-`pair`; RHS composite unfolds to one too; bridge the two via the IH.
      have hf : catForget (𝒞 := 𝒞) (a :: x') (d ++ e)
          = pair (fst : prod a (listProd (x' ++ (d ++ e))) ⟶ a)
                 ((snd : prod a (listProd (x' ++ (d ++ e))) ⟶ _) ≫ catForget x' (d ++ e)) := rfl
      have hg : catForget (𝒞 := 𝒞) ((a :: x') ++ d) e ≫ catForget (𝒞 := 𝒞) (a :: x') d
          = pair (fst : prod a (listProd ((x' ++ d) ++ e)) ⟶ a)
                 ((snd : prod a (listProd ((x' ++ d) ++ e)) ⟶ _)
                   ≫ (catForget (𝒞 := 𝒞) (x' ++ d) e ≫ catForget (𝒞 := 𝒞) x' d)) := by
        show pair (fst : prod a (listProd ((x' ++ d) ++ e)) ⟶ a)
                  ((snd : _) ≫ catForget (x' ++ d) e)
              ≫ pair (fst : prod a (listProd (x' ++ d)) ⟶ a) ((snd : _) ≫ catForget x' d)
            = _
        refine pair_uniq _ _ _ ?_ ?_
        · rw [Cat.assoc, fst_pair, fst_pair]
        · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]
      rw [hf, hg]
      exact pair_fst_snd_heq (by rw [List.append_assoc]) _ _ (catForget_append_heq x' d e)

/-- `catArrange` is natural in its source: `h ≫ catArrange t d g b = catArrange t d (h≫g) (h≫b)`.
    (Precomposition distributes over the `pair`-assembly; induction on `t`.) -/
theorem catArrange_snd_comp : ∀ (t d : List 𝒞) {W X : 𝒞} (h : W ⟶ X)
    (g : X ⟶ listProd (𝒞 := 𝒞) t) (b : X ⟶ listProd d),
    h ≫ catArrange t d g b = catArrange t d (h ≫ g) (h ≫ b)
  | [],      d, W, X, h, g, b => rfl
  | a :: t', d, W, X, h, g, b => by
      show h ≫ pair (g ≫ fst) (catArrange t' d (g ≫ snd) b)
          = pair ((h ≫ g) ≫ fst) (catArrange t' d ((h ≫ g) ≫ snd) (h ≫ b))
      refine pair_uniq _ _ _ ?_ ?_
      · rw [Cat.assoc, fst_pair, Cat.assoc]
      · rw [Cat.assoc, snd_pair, catArrange_snd_comp t' d h (g ≫ snd) b, Cat.assoc]

/-- Generic cons-step kernel for `catTail`: `snd ≫ ·` preserves HEq across a domain reindexing `Q = P`.
    Given `u : P ⟶ R`, `v : Q ⟶ R` with `u ≍ v`, `snd ≫ u` (over `prod a P`) is HEq `snd ≫ v`. -/
theorem snd_comp_heq {a R P Q : 𝒞} (hPQ : Q = P)
    (u : P ⟶ R) (v : Q ⟶ R) (huv : HEq u v) :
    HEq ((snd : prod a P ⟶ P) ≫ u) ((snd : prod a Q ⟶ Q) ≫ v) := by
  subst hPQ; cases huv; rfl

/-- **Bridge B.**  `catTail x (d++e) ≍ catTail (x++d) e ≫ catTail x d` — projecting onto the suffix
    `d++e` equals projecting onto `e` then... wait: the suffix `d++e` is recovered from `(x++d)++e` by
    `catArrange d e` of its `d`-part (`catForget(x++d) e ≫ catTail x d`) and `e`-part (`catTail(x++d) e`).
    Induction on `x`; cons step bridges via the IH. -/
theorem catTail_append_heq : ∀ (x d e : List 𝒞),
    HEq (catTail (𝒞 := 𝒞) x (d ++ e))
        (catArrange (𝒞 := 𝒞) d e (catForget (𝒞 := 𝒞) (x ++ d) e ≫ catTail (𝒞 := 𝒞) x d)
                                  (catTail (𝒞 := 𝒞) (x ++ d) e))
  | [],      d, e => by
      -- LHS `= id (∏(d++e))`; RHS `= catArrange d e (catForget d e) (catTail d e) = catMap e id = id`.
      show HEq (catTail (𝒞 := 𝒞) [] (d ++ e))
               (catArrange (𝒞 := 𝒞) d e (catForget (𝒞 := 𝒞) ([] ++ d) e ≫ catTail (𝒞 := 𝒞) [] d)
                                         (catTail (𝒞 := 𝒞) ([] ++ d) e))
      have hL : catTail (𝒞 := 𝒞) [] (d ++ e) = Cat.id (listProd (d ++ e)) := rfl
      have hR : catArrange (𝒞 := 𝒞) d e (catForget (𝒞 := 𝒞) ([] ++ d) e ≫ catTail (𝒞 := 𝒞) [] d)
                  (catTail (𝒞 := 𝒞) ([] ++ d) e) = Cat.id (listProd (d ++ e)) := by
        show catArrange d e (catForget d e ≫ Cat.id _) (catTail d e) = _
        exact catMap_id d e
      rw [hL, hR]
  | a :: x', d, e => by
      -- LHS `= snd ≫ catTail x' (d++e)`; RHS's `catArrange` over `(a::x')++d = a::(x'++d)` unfolds to a
      -- cons-`pair`, whose `snd`-part is the IH'd `catArrange`; bridge the two `snd ≫ ·`s.
      have hL : catTail (𝒞 := 𝒞) (a :: x') (d ++ e)
          = (snd : prod a (listProd (x' ++ (d ++ e))) ⟶ _) ≫ catTail (𝒞 := 𝒞) x' (d ++ e) := rfl
      have hR : catArrange (𝒞 := 𝒞) d e
              (catForget (𝒞 := 𝒞) ((a :: x') ++ d) e ≫ catTail (𝒞 := 𝒞) (a :: x') d)
              (catTail (𝒞 := 𝒞) ((a :: x') ++ d) e)
          = (snd : prod a (listProd ((x' ++ d) ++ e)) ⟶ _)
            ≫ catArrange (𝒞 := 𝒞) d e (catForget (𝒞 := 𝒞) (x' ++ d) e ≫ catTail (𝒞 := 𝒞) x' d)
                                       (catTail (𝒞 := 𝒞) (x' ++ d) e) := by
        -- `catForget (a::(x'++d)) e ≫ catTail (a::x') d = snd ≫ (catForget(x'++d) e ≫ catTail x' d)`,
        -- and `catTail (a::(x'++d)) e = snd ≫ catTail(x'++d) e`; then `catArrange` is `snd ≫`-natural.
        have hb : catForget (𝒞 := 𝒞) ((a :: x') ++ d) e ≫ catTail (𝒞 := 𝒞) (a :: x') d
            = (snd : prod a (listProd ((x' ++ d) ++ e)) ⟶ _)
              ≫ (catForget (𝒞 := 𝒞) (x' ++ d) e ≫ catTail (𝒞 := 𝒞) x' d) := by
          show pair (fst : prod a (listProd ((x' ++ d) ++ e)) ⟶ a) ((snd : _) ≫ catForget (x' ++ d) e)
                ≫ ((snd : prod a (listProd (x' ++ d)) ⟶ _) ≫ catTail x' d) = _
          rw [← Cat.assoc, snd_pair, Cat.assoc]
        have ht : catTail (𝒞 := 𝒞) ((a :: x') ++ d) e
            = (snd : prod a (listProd ((x' ++ d) ++ e)) ⟶ _) ≫ catTail (𝒞 := 𝒞) (x' ++ d) e := rfl
        rw [hb, ht]
        exact (catArrange_snd_comp d e _ _ _).symm
      rw [hL, hR]
      exact snd_comp_heq (by rw [List.append_assoc]) _ _ (catTail_append_heq x' d e)

/-- Full heterogeneous congruence for composition (all three objects may differ).  Local copy
    (S1_49 has the same lemma but is not imported here). -/
theorem comp_heq {X X' A A' Bo Bo' : 𝒞} (f : X ⟶ A) (f' : X' ⟶ A')
    (s : A ⟶ Bo) (s' : A' ⟶ Bo') (hX : X = X') (hA : A = A') (hB : Bo = Bo')
    (hf : HEq f f') (hs : HEq s s') : HEq (f ≫ s) (f' ≫ s') := by
  cases hX; cases hA; cases hB; cases hf; cases hs; rfl

/-- Double-transport HEq: an arrow is HEq its transport along domain `hX` and codomain `hB`. -/
theorem transport_heq {X X' Bo Bo' : 𝒞} (hX : X = X') (hB : Bo = Bo') (R : X ⟶ Bo) :
    HEq R (hB ▸ hX ▸ R : X' ⟶ Bo') := by
  subst hX; subst hB; rfl

/-- **`catMap (d ++ e) f` HEq `catMap e (catMap d f)`** — appending the concatenated suffix `d++e`
    equals appending `d` then `e`, modulo the `(s++d)++e = s++(d++e)` reindexing.  (`F_trans` core.)
    `R := catMap e (catMap d f)` and `catMap (d++e) f` satisfy the SAME joint-monic characterization
    (over `catForget t (d++e)`/`catTail t (d++e)`): the bridges `catForget_append_heq`/`catTail_append_heq`
    convert `R`'s `catMap e`/`catMap d` projection laws into the `d++e` ones (each equation collapses
    from `HEq` to `Eq` because both sides share the type), and `cat_jointly_monic` finishes. -/
theorem catMap_append_heq {s t : List 𝒞} (d e : List 𝒞) (f : listProd (𝒞 := 𝒞) s ⟶ listProd t) :
    HEq (catMap (d ++ e) f) (catMap e (catMap d f)) := by
  have hS : listProd (𝒞 := 𝒞) ((s ++ d) ++ e) = listProd (s ++ (d ++ e)) := by rw [List.append_assoc]
  have hT : listProd (𝒞 := 𝒞) ((t ++ d) ++ e) = listProd (t ++ (d ++ e)) := by rw [List.append_assoc]
  let R := catMap (𝒞 := 𝒞) e (catMap d f)
  -- transport `R` into the `d++e`-typed slot; `R ≍ R'`.
  let R' : listProd (𝒞 := 𝒞) (s ++ (d ++ e)) ⟶ listProd (t ++ (d ++ e)) := hT ▸ hS ▸ R
  show HEq (catMap (d ++ e) f) R
  have hRR' : HEq R R' := transport_heq hS hT R
  -- `R`'s two projection laws (for the outer suffix `e`):
  have hRf : R ≫ catForget (𝒞 := 𝒞) (t ++ d) e = catForget (𝒞 := 𝒞) (s ++ d) e ≫ catMap d f :=
    catMap_forget e (catMap d f)
  have hRt : R ≫ catTail (𝒞 := 𝒞) (t ++ d) e = catTail (𝒞 := 𝒞) (s ++ d) e :=
    catMap_tail e (catMap d f)
  -- the FORGET equation `R' ≫ catForget t (d++e) = catForget s (d++e) ≫ f`.
  have hForget : R' ≫ catForget (𝒞 := 𝒞) t (d ++ e)
      = catForget (𝒞 := 𝒞) s (d ++ e) ≫ f := by
    apply eq_of_heq
    -- `R' ≫ catForget t (d++e) ≍ R ≫ (catForget(t++d)e ≫ catForget t d)`  (bridge A at t, `R ≍ R'`).
    refine HEq.trans (comp_heq R' R _ _ hS.symm hT.symm rfl hRR'.symm
      (catForget_append_heq t d e)) ?_
    -- compute `R ≫ (catForget(t++d)e ≫ catForget t d) = (catForget(s++d)e ≫ catForget s d) ≫ f`.
    have hcomp : R ≫ (catForget (𝒞 := 𝒞) (t ++ d) e ≫ catForget (𝒞 := 𝒞) t d)
        = (catForget (𝒞 := 𝒞) (s ++ d) e ≫ catForget (𝒞 := 𝒞) s d) ≫ f := by
      rw [← Cat.assoc, hRf, Cat.assoc, catMap_forget, ← Cat.assoc]
    rw [hcomp]
    -- `(catForget(s++d)e ≫ catForget s d) ≫ f ≍ catForget s (d++e) ≫ f`  (bridge A at s).
    exact comp_heq _ _ f f hS rfl rfl (catForget_append_heq s d e).symm (HEq.refl f)
  -- the TAIL equation `R' ≫ catTail t (d++e) = catTail s (d++e)`.
  have hTail : R' ≫ catTail (𝒞 := 𝒞) t (d ++ e) = catTail (𝒞 := 𝒞) s (d ++ e) := by
    apply eq_of_heq
    -- `R' ≫ catTail t (d++e) ≍ R ≫ catArrange d e (catForget(t++d)e ≫ catTail t d) (catTail(t++d)e)`.
    refine HEq.trans (comp_heq R' R _ _ hS.symm hT.symm rfl hRR'.symm
      (catTail_append_heq t d e)) ?_
    -- pull `R` inside the `catArrange`, simplify each leg, land on bridge B at `s`.
    rw [catArrange_snd_comp]
    have hleg1 : R ≫ (catForget (𝒞 := 𝒞) (t ++ d) e ≫ catTail (𝒞 := 𝒞) t d)
        = catForget (𝒞 := 𝒞) (s ++ d) e ≫ catTail (𝒞 := 𝒞) s d := by
      rw [← Cat.assoc, hRf, Cat.assoc, catMap_tail]
    have hleg2 : R ≫ catTail (𝒞 := 𝒞) (t ++ d) e = catTail (𝒞 := 𝒞) (s ++ d) e := hRt
    rw [hleg1, hleg2]
    exact (catTail_append_heq s d e).symm
  -- both equations hold ⟹ `R' = catMap (d++e) f` by joint monicity; transport back.
  have hR'eq : R' = catMap (𝒞 := 𝒞) (d ++ e) f := by
    apply cat_jointly_monic t (d ++ e)
    · rw [hForget, catMap_forget]
    · rw [hTail, catMap_tail]
  rw [← hR'eq]; exact hRR'.symm

/-- Transporting an `Over` along a base equality `e : B = B'` leaves its `dom` unchanged. -/
theorem over_transport_dom {𝒟 : Type u} [Cat.{u} 𝒟] {B B' : 𝒟} (e : B = B') (X : Over B) :
    (e ▸ X : Over B').dom = X.dom := by subst e; rfl

/-- Transporting an `Over` along a base equality `e : B = B'` leaves its `hom` HEq the original. -/
theorem over_transport_hom_heq {𝒟 : Type u} [Cat.{u} 𝒟] {B B' : 𝒟} (e : B = B') (X : Over B) :
    HEq (e ▸ X : Over B').hom X.hom := by subst e; rfl

/-- `catMap` respects HEq of its structure arrow across a LIST reindexing: if `s = s'`, `t = t'` as
    lists and `g ≍ g'`, then `catMap d g ≍ catMap d g'`.  (`subst`s the list equalities, then `cases`.) -/
theorem catMap_heq_congr {s t s' t' : List 𝒞} (d : List 𝒞)
    (hs : s = s') (ht : t = t')
    (g : listProd (𝒞 := 𝒞) s ⟶ listProd t) (g' : listProd (𝒞 := 𝒞) s' ⟶ listProd t')
    (hg : HEq g g') :
    HEq (catMap (𝒞 := 𝒞) d g) (catMap (𝒞 := 𝒞) d g') := by
  subst hs; subst ht; cases hg; rfl

/-- **`F_trans` for the strict inner system** — the composite suffix-transition equals appending the
    concatenated suffix (modulo `(V++d)++e = V++(d++e)`).  `innerSliceTr` of a prefix step transports
    `sliceCatObj (suffix)` along `V++suffix = U`; the composite over `V ⊑ U ⊑ W` therefore has `dom`
    `(X.dom ++ dVU) ++ dUW` and structure `catMap dUW (catMap dVU X.hom)`, while the direct `V ⊑ W`
    step has `dom` `X.dom ++ (dVU++dUW)` and `catMap (dVU++dUW) X.hom`.  `prefixSuffix_trans`
    (`dVW = dVU++dUW`) reconciles the doms (`append_assoc`) and `catMap_append_heq` the structures. -/
theorem innerSliceTr_trans {V U W : List 𝒞} (hVU : prefixLe V U) (hUW : prefixLe U W)
    (X : innerSliceObj (𝒞 := 𝒞) V) :
    innerSliceTr (hVU.trans hUW) X = innerSliceTr hUW (innerSliceTr hVU X) := by
  -- abbreviations for the three suffixes; `prefixSuffix_trans` gives `dVW = dVU ++ dUW`.
  have hdVW : prefixSuffix V W = prefixSuffix V U ++ prefixSuffix U W := prefixSuffix_trans hVU hUW
  -- intermediate `Y := innerSliceTr hVU X : Over U`, with computed `dom`/`hom`.
  have hYdom : (innerSliceTr hVU X).dom = X.dom ++ prefixSuffix V U := by
    unfold innerSliceTr; rw [over_transport_dom]; rfl
  have hYhom : HEq (innerSliceTr hVU X).hom (catMap (prefixSuffix V U) X.hom) := by
    unfold innerSliceTr; exact over_transport_hom_heq _ _
  -- the RHS `innerSliceTr hUW Y` dom/hom, peeling its outer transport.
  have hRdom : (innerSliceTr hUW (innerSliceTr hVU X)).dom
      = (X.dom ++ prefixSuffix V U) ++ prefixSuffix U W := by
    unfold innerSliceTr
    rw [over_transport_dom]
    show (innerSliceTr hVU X).dom ++ prefixSuffix U W = _
    rw [hYdom]
  -- reduce the goal (LHS) by `over_transport_ext` to dom-eq + hom-HEq.
  unfold innerSliceTr
  apply over_transport_ext
  · -- dom: `X.dom ++ dVW = (X.dom ++ dVU) ++ dUW`  (via `dVW = dVU++dUW` + `append_assoc`).
    show X.dom ++ prefixSuffix V W = (innerSliceTr hUW (innerSliceTr hVU X)).dom
    rw [hRdom, hdVW, List.append_assoc]
  · -- hom: `catMap dVW X.hom ≍ (innerSliceTr hUW Y).hom ≍ catMap dUW (catMap dVU X.hom)`.
    show HEq (catMap (prefixSuffix V W) X.hom) (innerSliceTr hUW (innerSliceTr hVU X)).hom
    -- peel the RHS outer transport, then its `sliceCatObj` (= `catMap dUW Y.hom`), then `hYhom`.
    refine HEq.trans ?_ (over_transport_hom_heq (prefixSuffix_eq hUW)
      (sliceCatObj (prefixSuffix U W) (innerSliceTr hVU X))).symm
    show HEq (catMap (prefixSuffix V W) X.hom)
             (catMap (prefixSuffix U W) (innerSliceTr hVU X).hom)
    -- replace `Y.hom` by `catMap dVU X.hom` (HEq), then `catMap_append_heq` does `dVW = dVU++dUW`.
    refine HEq.trans ?_ (catMap_heq_congr (prefixSuffix U W) hYdom.symm (prefixSuffix_eq hVU)
      (catMap (prefixSuffix V U) X.hom) (innerSliceTr hVU X).hom hYhom.symm)
    rw [hdVW]
    exact catMap_append_heq (prefixSuffix V U) (prefixSuffix U W) X.hom

/-! ## §1.547  A genuinely DIRECTED strict `CatSystem` from a prefix-chain (option (b))

  The strict inner transition `innerSliceTr` lives on the PREFIX order `V <+: U`, which is NOT
  directed: `[A]` and `[B]` have no common prefix-extension (a common upper bound would have to begin
  with both `A` and `B`).  So the strict system cannot be indexed by `(List 𝒞, <+:)` directly.

  Freyd's §1.547 index is finite SETS of well-supported objects under inclusion, directed by union.
  Making the *strict* (concatenation) transition directed over that index would require reconciling
  suffix-append `catMap` with set-union — needing both `V → V++U` AND `U → V++U`, but the second is a
  PREPEND, not an append; `catMap` only appends.  (Quotienting `List 𝒞` by permutation to a canonical
  product would restore append-only directedness, but the quotient destroys the strict *object*-level
  `(s++d)++e = s++(d++e)` that `catMap_append_heq` relies on — the whole point of the inflation.)  So the
  set-indexed directed system genuinely cannot be made strict with `catMap` alone.

  We therefore take option (b): the **ω-chain**.  Fix any increasing prefix-chain `V : ℕ → Infl 𝒞`
  (`V n <+: V (n+1)`).  `ℕ` under `≤` IS directed (`natDirected`, `bound = max`), and `i ≤ j ⟹ V i <+:
  V j` (`PrefixChain.prefix`), so the strict `innerSliceTr` becomes a genuine **directed strict
  `CatSystem`** over `natDirected` — `F_refl`/`F_trans` are the already-proven `innerSliceTr_refl`/
  `innerSliceTr_trans` (proof-irrelevant in the `<+:` witness since `List.IsPrefix` is a `Prop`).
  Sorry-free and propext-only.

  WHAT (b) SACRIFICES vs §1.547's "all finite subsets" coverage.  A single chain only reaches the
  factor-sets that appear as some `V n` — one cofinal tower of finite sets, not the full directed poset
  of *all* finite subsets.  To point *every* well-supported `B` simultaneously the chain must be cofinal
  among finite sets (enumerate well-supported objects `B₀, B₁, …` and take `V n := [B₀,…,Bₙ₋₁]`, so every
  finite set is a prefix-suffix-subset of some `V n`); the colimit over the chain then has the SAME germs
  as the colimit over all finite subsets, because every finite subset is dominated by a chain stage.  The
  chain does NOT see two incomparable finite sets `U₁, U₂` as a span — it linearises them through a later
  `V n ⊇ U₁ ∪ U₂` — sound for the directed *colimit* but a genuine restriction of the index *shape*
  (linear, not the full subset lattice).  Building the chain cofinal needs an enumeration `ℕ → 𝒞` of
  well-supported objects, which is the residual `hwall_step` input this construction is parameterised
  over (the `PrefixChain` is supplied by such an enumeration). -/

/-! ### The TRANSFINITE generalization: a prefix chain over an ARBITRARY directed index

  §1.544-546 (Freyd) runs the inner relative-capitalization by *transfinite recursion* over the
  (possibly uncountable) well-supported objects of an arbitrary small category — `ℕ` cannot enumerate
  an uncountable object set.  But the whole strict `CatSystem` machinery below uses its index ONLY
  through (a) a `Colim.Directed ι` instance `D` (`refl`/`trans`/`bound`, and `Prop`-irrelevance of
  `D.le`), and (b) a monotone map `chain : ι → Infl 𝒞` with `D.le i j ⟹ chain i <+: chain j` — i.e.
  a `prefixLe`-monotone chain over the directed index.  So we abstract that data as `OrdChain D` and
  re-derive the ENTIRE chain layer (`ordChainSliceFunctor`/`ordChainSliceSystem`/`ordChainSliceCoherent`/
  the preservation package/`ordChainSlicePreRegular`) generically over any `Directed ι`.  Instantiating
  `D := uliftNatDirected` recovers the ℕ-chain (`PrefixChain`, below) as a thin special case — the SAME
  proofs serve both (DRY).  Instantiating `D` by mathlib's `Ordinal`/any `LinearOrder + WellFoundedLT`
  (carried as a `Colim.Directed` via its `≤`, `bound = max`) gives the transfinite cofinal chain
  `hwall_step` needs over an uncountable object set.  No category theory leaves the repo's own `Cat`. -/

/-- A `prefixLe`-monotone chain of factor-sequences over a directed index `(ι, D)`: `chain : ι → Infl 𝒞`
    with `D.le i j ⟹ chain i <+: chain j`.  The data the strict inner `CatSystem` is built over,
    generalized from the ω-chain (`ℕ`) to an ARBITRARY directed index so the §1.544-546 inner system can
    be cofinal over an uncountable object set (transfinite recursion).  Cofinality among finite sets —
    needed to recover §1.547's full coverage — is an *additional* property of the chain (the chain being
    cofinal in the index), not required to build the system. -/
structure OrdChain {ι : Type u} (D : Colim.Directed ι)
    (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] where
  chain : ι → Infl 𝒞
  /-- the chain is `prefixLe`-monotone along the directed order -/
  mono : ∀ {i j : ι}, D.le i j → chain i <+: chain j

/-- A prefix-chain of factor-sequences: `chain n <+: chain (n+1)` for every `n`.  The data an ω-chain
    strict `CatSystem` is built over (option (b)).  Cofinality among finite sets — needed to recover
    §1.547's full coverage — is an *additional* property of the chain, not required to build the system. -/
structure PrefixChain (𝒞 : Type u) [Cat.{u} 𝒞] [HasTerminal 𝒞] [HasBinaryProducts 𝒞] where
  chain : Nat → Infl 𝒞
  step : ∀ n, chain n <+: chain (n + 1)

/-- `i ≤ j ⟹ chain i <+: chain j` — the chain is monotone under the prefix order.  Induction on the
    `≤`-witness, composing the single-step prefixes `step` by `List.IsPrefix.trans`. -/
theorem PrefixChain.prefix (P : PrefixChain 𝒞) : ∀ {i j : Nat}, i ≤ j → P.chain i <+: P.chain j
  | _, _, Nat.le.refl => List.prefix_refl _
  | _, _, Nat.le.step (m := m) h => (P.prefix h).trans (P.step m)

/-- The ℕ-`PrefixChain` viewed as an `OrdChain` over `uliftNatDirected` — the bridge that makes the
    generic `ordChain*` machinery specialize back to the ℕ-chain (DRY: one set of proofs). -/
def PrefixChain.toOrdChain (P : PrefixChain 𝒞) : OrdChain (uliftNatDirected.{u}) 𝒞 where
  chain n := P.chain n.down
  mono {_i _j} hij := P.prefix hij

/-- Transport a slice-valued functor along a base equality.  For a source category `𝒟` and a base
    category `ℰ` with `e : B = B'` (`B B' : ℰ`) and a functor `G : 𝒟 → Over B`, the map
    `X ↦ e ▸ G X : 𝒟 → Over B'` is again a functor.  (`subst e` collapses the transport, leaving the
    original functor — a definitional repackaging.)  Used to transport `sliceCatFunctor d` (a functor
    `A′/V → A′/(V++d)`, source `Over V`, base object `V++d`) along `V++d = U` to land in `A′/U`. -/
def transportSliceFunctor {𝒟 : Type u} [Cat.{u} 𝒟] {ℰ : Type u} [Cat.{u} ℰ] {B B' : ℰ} (e : B = B')
    (FG : @Functor 𝒟 (Over B) _ (overCat B)) :
    @Functor 𝒟 (Over B') _ (overCat B') where
  -- object/morphism actions given POINTWISE (`e ▸ …`) so `.obj` is syntactically `e ▸ FG.obj X`,
  -- matching `innerSliceTr`'s `prefixSuffix_eq ▸ sliceCatObj` (needed for the `CatSystem` `Fmap` fields).
  obj X := e ▸ FG.obj X
  map {X Y} g := by subst e; exact FG.map g
  map_id X := by subst e; exact FG.map_id X
  map_comp {X Y Z} f g := by subst e; exact FG.map_comp f g

/-- **GENERIC** per-transition functor of the chain system over ANY directed index: for an `OrdChain D O`
    and `hij : D.le i j`, `innerSliceTr (O.mono hij) : A′/(chain i) → A′/(chain j)` is a functor —
    `sliceCatFunctor (suffix)` transported along `chain i ++ suffix = chain j` (`transportSliceFunctor`).
    Object map is `innerSliceTr` by `rfl`.  The `Nat` `chainSliceFunctor` is its `uliftNatDirected`
    specialization. -/
noncomputable def ordChainSliceFunctor {ι : Type u} {D : Colim.Directed ι} (O : OrdChain D 𝒞)
    {i j : ι} (hij : D.le i j) :
    @Functor (innerSliceObj (𝒞 := 𝒞) (O.chain i)) (innerSliceObj (𝒞 := 𝒞) (O.chain j))
      (innerSliceCat (O.chain i)) (innerSliceCat (O.chain j)) :=
  transportSliceFunctor (𝒟 := Over (B := (O.chain i : Infl 𝒞)))
    (B := O.chain i ++ prefixSuffix (O.chain i) (O.chain j))
    (prefixSuffix_eq (O.mono hij))
    (sliceCatFunctor (prefixSuffix (O.chain i) (O.chain j)) (O.chain i))

/-- **GENERIC §1.544-546 — the DIRECTED strict `CatSystem` of inflation slices along an `OrdChain` over
    ANY directed index `(ι, D)`.**  Stage `i` is the slice `A′/(chain i)`, transition for `hij : D.le i j`
    the strict suffix-append `innerSliceTr (O.mono hij)`.  The `CatSystem` laws are the already-proven
    strict `innerSliceTr_refl`/`innerSliceTr_trans` (proof-irrelevant in the `<+:` witness, a `Prop`) — so
    they hold over ANY index, not just `ℕ`.  This is the transfinite-ready directed strict system the
    §1.544-546 inner relative-capitalization needs cofinal over an uncountable object set; the ω-chain
    `chainSliceSystem` is its `uliftNatDirected` specialization.  Sorry-free, propext-only. -/
noncomputable def ordChainSliceSystem {ι : Type u} {D : Colim.Directed ι} (O : OrdChain D 𝒞) :
    Colim.CatSystem.{u, u} ι D where
  A i := innerSliceObj (𝒞 := 𝒞) (O.chain i)
  catA i := innerSliceCat (O.chain i)
  F {i j} hij X := innerSliceTr (O.mono hij) X
  Fmap {i j} hij := (ordChainSliceFunctor O hij).map
  Fmap_id {i j} hij := (ordChainSliceFunctor O hij).map_id
  Fmap_comp {i j} hij := (ordChainSliceFunctor O hij).map_comp
  F_refl {i} X := by
    show innerSliceTr (O.mono (D.refl i)) X = X
    exact innerSliceTr_refl X
  F_trans {i j k} hij hjk X := by
    show innerSliceTr (O.mono (D.trans hij hjk)) X
        = innerSliceTr (O.mono hjk) (innerSliceTr (O.mono hij) X)
    exact innerSliceTr_trans (O.mono hij) (O.mono hjk) X

/-- The per-transition functor of the ℕ-chain system — the `uliftNatDirected` specialization of the
    generic `ordChainSliceFunctor`. -/
noncomputable def chainSliceFunctor (P : PrefixChain 𝒞) {i j : Nat} (hij : i ≤ j) :
    @Functor (innerSliceObj (𝒞 := 𝒞) (P.chain i)) (innerSliceObj (𝒞 := 𝒞) (P.chain j))
      (innerSliceCat (P.chain i)) (innerSliceCat (P.chain j)) :=
  ordChainSliceFunctor P.toOrdChain (i := ⟨i⟩) (j := ⟨j⟩) hij

/-- **§1.547 (option (b)) — the DIRECTED strict `CatSystem` of inflation slices along an ℕ-prefix-chain.**
    The `uliftNatDirected` specialization of the generic `ordChainSliceSystem` (`P.toOrdChain`): stage `n`
    is the slice `A′/(chain n)`, transition the strict suffix-append `innerSliceTr (P.prefix hij)`.  Sorry-
    free, propext-only. -/
noncomputable def chainSliceSystem (P : PrefixChain 𝒞) :
    Colim.CatSystem.{u, u} (ULift.{u} Nat) uliftNatDirected :=
  ordChainSliceSystem P.toOrdChain

/-! ### Morphism-level coherence of `chainSliceSystem` (`Coherent`)

  `chainSliceSystem`'s `functF` is `chainSliceFunctor = transportSliceFunctor e (sliceCatFunctor d)`,
  whose underlying object map is `innerSliceTr`.  The two `Coherent` fields are the MORPHISM-level
  analogs of `innerSliceTr_refl`/`innerSliceTr_trans` (which are the OBJECT-level laws): an identity
  transition acts as the identity *functor* and composites compose, both `HEq` (the endpoint objects
  shift by `F_refl`/`F_trans`).  Everything reduces to the underlying `.f = catMap (suffix)` together
  with `catMap_nil_heq` (refl) and `catMap_append_heq` (trans) — exactly the arrows used at the object
  level — threaded through the transport via `transportSliceFunctor_map_f_heq`. -/

/-- The underlying arrow of a transported slice morphism.  For `e : B = B'` and a slice functor
    `FG : 𝒟 → Over B`, the `.f` of `(transportSliceFunctor e FG).map g` is `HEq` the `.f` of the
    original `FG.map g` (the transport only re-types the base; the underlying arrow is unchanged).
    `subst e` collapses the transport to `FG.map g` definitionally. -/
theorem transportSliceFunctor_map_f_heq {𝒟 : Type u} [Cat.{u} 𝒟] {ℰ : Type u} [Cat.{u} ℰ]
    {B B' : ℰ} (e : B = B')
    (FG : @Functor 𝒟 (Over B) _ (overCat B)) {X Y : 𝒟} (g : X ⟶ Y) :
    HEq ((transportSliceFunctor e FG).map g).f (FG.map g).f := by
  subst e; rfl

/-- **GENERIC** — `catMap d g.f` for the suffix `d = prefixSuffix (chain i) (chain j)` is the `.f` of
    `(ordChainSliceFunctor O hij).map g` up to `HEq`, over ANY directed index.  Peels the transport
    (`transportSliceFunctor_map_f_heq`) then `sliceCatMap`'s `.f = catMap d g.f` definitionally. -/
theorem ordChainSliceFunctor_map_f_heq {ι : Type u} {D : Colim.Directed ι} (O : OrdChain D 𝒞)
    {i j : ι} (hij : D.le i j)
    {X Y : innerSliceObj (𝒞 := 𝒞) (O.chain i)} (g : X ⟶ Y) :
    HEq ((ordChainSliceFunctor O hij).map g).f (catMap (prefixSuffix (O.chain i) (O.chain j)) g.f) :=
  transportSliceFunctor_map_f_heq _ _ g

/-- `catMap d g.f` is the `.f` of `(chainSliceFunctor P hij).map g` up to `HEq` (the ℕ specialization of
    `ordChainSliceFunctor_map_f_heq`). -/
theorem chainSliceFunctor_map_f_heq (P : PrefixChain 𝒞) {i j : Nat} (hij : i ≤ j)
    {X Y : innerSliceObj (𝒞 := 𝒞) (P.chain i)} (g : X ⟶ Y) :
    HEq ((chainSliceFunctor P hij).map g).f (catMap (prefixSuffix (P.chain i) (P.chain j)) g.f) :=
  transportSliceFunctor_map_f_heq _ _ g

/-- Two slice morphisms over (possibly different, but equal) bases are `HEq` once their endpoints are
    `HEq` as `Over`-objects and their underlying arrows are `HEq`.  Componentwise `HEq` extensionality
    for `OverHom` (the `w` field is a `Prop`, so proof-irrelevant once `f` and the endpoints match);
    `subst e` aligns the base types so the endpoint `HEq`s become genuine `Eq`s. -/
theorem overHom_heq {ℰ : Type u} [Cat.{u} ℰ] {B B' : ℰ} (e : B = B')
    {X Y : Over B} {X' Y' : Over B'} (hX : HEq X X') (hY : HEq Y Y')
    {a : OverHom X Y} {b : OverHom X' Y'} (hf : HEq a.f b.f) : HEq a b := by
  subst e; cases hX; cases hY; exact heq_of_eq (OverHom.ext (eq_of_heq hf))

/-- **GENERIC `Coherent` for the directed strict chain system over ANY index.**  The morphism-level mate
    of `innerSliceTr_refl`/`innerSliceTr_trans`.  `refl_map`: the empty-suffix transition's functor is the
    identity on arrows (underlying `catMap [] g.f ≍ g.f`, `catMap_nil_heq`).  `trans_map`: the composite
    transition's functor splits (underlying `catMap (dVU++dUW) g.f ≍ catMap dUW (catMap dVU g.f)`,
    `catMap_append_heq`).  Both threaded through the base-transport by `overHom_heq` on the now-`HEq`
    endpoints (`innerSliceTr_refl`/`_trans` at the OBJECT level).  Index-agnostic — uses only `D.refl`/
    `D.trans` and `Prop`-irrelevance of the `<+:` witness.  Sorry-free, propext-only. -/
theorem ordChainSliceCoherent {ι : Type u} {D : Colim.Directed ι} (O : OrdChain D 𝒞) :
    (ordChainSliceSystem O).Coherent where
  refl_map {i x x'} g := by
    -- underlying `.f`: `catMap (prefixSuffix (chain i) (chain i)) g.f`, and the suffix is `[]`.
    refine overHom_heq rfl ?_ ?_ ?_
    · exact heq_of_eq (innerSliceTr_refl x)
    · exact heq_of_eq (innerSliceTr_refl x')
    · refine (ordChainSliceFunctor_map_f_heq O (D.refl i) g).trans ?_
      show HEq (catMap (prefixSuffix (O.chain i) (O.chain i)) g.f) g.f
      rw [prefixSuffix, List.drop_length]
      exact catMap_nil_heq g.f
  trans_map {i j k} hij hjk x x' g := by
    -- underlying `.f`: `catMap (prefixSuffix (chain i) (chain k)) g.f` vs the composite.
    have hVU : prefixLe (O.chain i) (O.chain j) := O.mono hij
    have hUW : prefixLe (O.chain j) (O.chain k) := O.mono hjk
    refine overHom_heq rfl ?_ ?_ ?_
    · exact heq_of_eq (innerSliceTr_trans hVU hUW x)
    · exact heq_of_eq (innerSliceTr_trans hVU hUW x')
    · -- LHS underlying = `catMap dVW g.f`; RHS = `((functF hjk).map ((functF hij).map g)).f`.
      refine (ordChainSliceFunctor_map_f_heq O (D.trans hij hjk) g).trans ?_
      refine HEq.symm (HEq.trans (ordChainSliceFunctor_map_f_heq O hjk _) ?_)
      -- the inner `((functF hij).map g).f ≍ catMap dVU g.f`; `catMap_heq_congr` lifts through `catMap dUW`.
      have hinner : HEq ((ordChainSliceFunctor O hij).map g).f (catMap (prefixSuffix (O.chain i)
          (O.chain j)) g.f) := ordChainSliceFunctor_map_f_heq O hij g
      refine HEq.trans (catMap_heq_congr (prefixSuffix (O.chain j) (O.chain k))
        (over_transport_dom _ _) (over_transport_dom _ _) _ _ hinner) ?_
      -- now `catMap dUW (catMap dVU g.f) ≍ catMap dVW g.f` via `prefixSuffix_trans` + `catMap_append_heq`.
      refine HEq.symm ?_
      rw [show prefixSuffix (O.chain i) (O.chain k)
          = prefixSuffix (O.chain i) (O.chain j)
            ++ prefixSuffix (O.chain j) (O.chain k) from prefixSuffix_trans hVU hUW]
      exact catMap_append_heq (prefixSuffix (O.chain i) (O.chain j))
        (prefixSuffix (O.chain j) (O.chain k)) g.f

/-- **`Coherent` for the ℕ directed strict chain system** — the `uliftNatDirected` specialization of the
    generic `ordChainSliceCoherent`. -/
theorem chainSliceCoherent (P : PrefixChain 𝒞) : (chainSliceSystem P).Coherent :=
  ordChainSliceCoherent P.toOrdChain

/-! ## §1.547  Preservation package for the inner chain-slice colimit

  The inner colimit `S* = colim_n A′/(chain n)` is pre-regular iff the strict suffix-append
  transition `innerSliceTr`/`chainSliceFunctor` carries the chosen finite-limit data of each slice
  to compatible data in the next.  These are the `colimitPreRegular` hypotheses for
  `chainSliceSystem`, mirroring the OUTER tower's `capData_of_tower` package.

  The transition `innerSliceTr h = (prefixSuffix_eq h) ▸ sliceCatObj d` (suffix `d`).  The transport
  `▸` is an iso (it is `Eq.rec` on the base object), so every preservation fact reduces to the
  corresponding fact for the *untransported* strict functor `sliceCatObj d : A′/V → A′/(V++d)`.  The
  terminal case is the down-payment `sliceCatObj_terminal`; the rest are genuine slice-base-change
  preservation facts (`sliceCatObj d` is base-change along the product projection `∏(V++d) → ∏V`,
  realized strictly by concatenation, so it preserves all finite limits and reflects/transfers covers). -/

/-- **Terminal preservation for the inner transition.**  `innerSliceTr h` carries the slice terminal
    `overTerm V` of `A′/V` to the slice terminal `overTerm U` of `A′/U`.  The untransported
    `sliceCatObj d` does it on the nose (`sliceCatObj_terminal`); the base-transport of `overTerm (V++d)`
    along `V++d = U` is `overTerm U` (`over_transport_ext`: dom `V++d = U`, hom `id ≍ id`). -/
theorem innerSliceTr_terminal {V U : List 𝒞} (h : prefixLe V U) :
    innerSliceTr h (overTerm (V : Infl 𝒞)) = overTerm (U : Infl 𝒞) := by
  unfold innerSliceTr
  have he : V ++ prefixSuffix V U = U := prefixSuffix_eq h
  rw [sliceCatObj_terminal]
  -- transport `overTerm (V++d)` along `V++d = U` is `overTerm U`.
  apply over_transport_ext
  · show (V ++ prefixSuffix V U : List 𝒞) = U; exact he
  · show HEq (Cat.id (listProd (𝒞 := 𝒞) (V ++ prefixSuffix V U))) (Cat.id (listProd (𝒞 := 𝒞) U))
    rw [he]

/-! ### Product / equalizer preservation reduced to the strict `sliceCatObj d`

  `chainSliceFunctor P hij = transportSliceFunctor e (sliceCatFunctor d)` with `d = prefixSuffix
  (chain i) (chain j)` and `e : chain i ++ d = chain j`.  Its `.map` is `HEq` the `.f` of `sliceCatMap
  d` (`chainSliceFunctor_map_f_heq`), whose underlying arrow is `catMap d`.  So a preservation fact
  about `chainSliceFunctor` reduces — after stripping the transport, which only re-types the base — to
  the strict statement about `catMap d` / `sliceCatObj d`.  We carry the underlying-`A′` form (in terms
  of `catMap`) since the slice product/equalizer of `Over V` is computed from the `Infl 𝒞`
  product/pullback. -/

/-- **Joint monicity of the base pullback projections** `overProdFst.f`/`overProdSnd.f` of the slice
    product `overProdPt X Y` (which is the `Infl 𝒞`-pullback of `X.hom, Y.hom`).  Two base maps into the
    product point agreeing after both projections are equal — pullback `lift_uniq`. -/
theorem overProdJointlyMonic [HasEqualizers 𝒞] {V : Infl 𝒞} (X Y : Over (B := V))
    {Z : Infl 𝒞} (p q : listProd (𝒞 := 𝒞) Z ⟶ listProd (𝒞 := 𝒞) (overProdPt X Y).dom)
    (h₁ : p ≫ (overProdFst X Y).f = q ≫ (overProdFst X Y).f)
    (h₂ : p ≫ (overProdSnd X Y).f = q ≫ (overProdSnd X Y).f) : p = q := by
  let PB := (inflHasPullbacks (𝒞 := 𝒞)).has X.hom Y.hom
  -- `overProdFst.f = PB.cone.π₁`, `overProdSnd.f = PB.cone.π₂` definitionally.
  have e₁ : p ≫ PB.cone.π₁ = q ≫ PB.cone.π₁ := h₁
  have e₂ : p ≫ PB.cone.π₂ = q ≫ PB.cone.π₂ := h₂
  -- both `p` and `q` lift the cone `⟨Z, q ≫ π₁, q ≫ π₂, …⟩`; uniqueness gives `p = q`.
  have hw : (q ≫ PB.cone.π₁) ≫ X.hom = (q ≫ PB.cone.π₂) ≫ Y.hom := by
    rw [Cat.assoc, Cat.assoc]; exact congrArg (q ≫ ·) PB.cone.w
  have hp := PB.lift_uniq ⟨_, q ≫ PB.cone.π₁, q ≫ PB.cone.π₂, hw⟩ p e₁ e₂
  have hq := PB.lift_uniq ⟨_, q ≫ PB.cone.π₁, q ≫ PB.cone.π₂, hw⟩ q rfl rfl
  exact hp.trans hq.symm

/-- The base-change `sliceCatObj d` preserves the slice **binary product** `overProdPt` jointly with
    `overProdFst`/`overProdSnd`: the images of the two projections are jointly monic.  This is the
    monic half of product-preservation; it descends to `hppres` for `chainSliceSystem`.

    Mathematically `sliceCatObj d = (-) × ∏d` realized by concatenation, base-change along the product
    projection `∏(V++d) → ∏V`, which preserves all finite limits — in particular the slice product
    (a base pullback).  RESIDUAL: the concrete `Infl 𝒞`-pullback computation. -/
theorem sliceCatObj_prod_jointly_monic [HasEqualizers 𝒞] (d : List 𝒞) {V : Infl 𝒞} (X Y : Over (B := V))
    (z : Over (B := (V ++ d : List 𝒞)))
    (u v : z ⟶ sliceCatObj d (overProdPt X Y))
    (hf : u ≫ (sliceCatFunctor d V).map (overProdFst X Y)
        = v ≫ (sliceCatFunctor d V).map (overProdFst X Y))
    (hs : u ≫ (sliceCatFunctor d V).map (overProdSnd X Y)
        = v ≫ (sliceCatFunctor d V).map (overProdSnd X Y)) : u = v := by
  apply OverHom.ext
  show u.f = v.f
  -- `.f` of the over-hom hyps: `u.f ≫ catMap d π_i = v.f ≫ catMap d π_i`.
  have hff : u.f ≫ catMap d (overProdFst X Y).f = v.f ≫ catMap d (overProdFst X Y).f :=
    congrArg OverHom.f hf
  have hss : u.f ≫ catMap d (overProdSnd X Y).f = v.f ≫ catMap d (overProdSnd X Y).f :=
    congrArg OverHom.f hs
  apply cat_jointly_monic (overProdPt X Y).dom d
  · -- forget leg: post-compose with `catForget`, use base joint-monicity of `(π₁, π₂)`.
    apply (overProdJointlyMonic X Y)
    · have t1 := catMap_forget (s := (overProdPt X Y).dom) (t := X.dom) d (overProdFst X Y).f
      rw [Cat.assoc, Cat.assoc, ← t1, ← Cat.assoc, ← Cat.assoc]
      exact congrArg (· ≫ catForget X.dom d) hff
    · have t2 := catMap_forget (s := (overProdPt X Y).dom) (t := Y.dom) d (overProdSnd X Y).f
      rw [Cat.assoc, Cat.assoc, ← t2, ← Cat.assoc, ← Cat.assoc]
      exact congrArg (· ≫ catForget Y.dom d) hss
  · -- tail leg: post-compose `hff` with `catTail`, use `catMap_tail`.
    have t := catMap_tail (s := (overProdPt X Y).dom) (t := X.dom) d (overProdFst X Y).f
    rw [← t, ← Cat.assoc, ← Cat.assoc]
    exact congrArg (· ≫ catTail X.dom d) hff

/-- Pairing half of product-preservation for `sliceCatObj d`: a map `p` into `F X` and `q` into `F Y`
    (over `V++d`) factor through `F (X ×_V Y)` compatibly with the two projections.  Descends to
    `hppres_pair`.  RESIDUAL: the concrete `Infl 𝒞`-pullback lift. -/
theorem sliceCatObj_prod_pair [HasEqualizers 𝒞] (d : List 𝒞) {V : Infl 𝒞} (X Y : Over (B := V))
    (z : Over (B := (V ++ d : List 𝒞)))
    (p : z ⟶ sliceCatObj d X) (q : z ⟶ sliceCatObj d Y) :
    ∃ r : z ⟶ sliceCatObj d (overProdPt X Y),
      r ≫ (sliceCatFunctor d V).map (overProdFst X Y) = p ∧
      r ≫ (sliceCatFunctor d V).map (overProdSnd X Y) = q := by
  let PB := (inflHasPullbacks (𝒞 := 𝒞)).has X.hom Y.hom
  -- triangle data from `p`, `q`: their base projections over `V`.
  have hpw : p.f ≫ catMap d X.hom = z.hom := p.w
  have hqw : q.f ≫ catMap d Y.hom = z.hom := q.w
  -- `p`/`q` agree on the `∏d`-tail (both equal `z.hom ≫ catTail V d`).  `rw` is unreliable on these
  -- `catMap`-fold lemmas (a hidden implicit mismatch in `≫`), so we chain `Eq.trans` term-side.
  have hpt : p.f ≫ catTail X.dom d = z.hom ≫ catTail V d :=
    (congrArg (p.f ≫ ·) (catMap_tail d X.hom).symm).trans
      ((Cat.assoc p.f (catMap d X.hom) (catTail V d)).symm.trans
        (congrArg (· ≫ catTail V d) hpw))
  have hqt : q.f ≫ catTail Y.dom d = z.hom ≫ catTail V d :=
    (congrArg (q.f ≫ ·) (catMap_tail d Y.hom).symm).trans
      ((Cat.assoc q.f (catMap d Y.hom) (catTail V d)).symm.trans
        (congrArg (· ≫ catTail V d) hqw))
  have htail : p.f ≫ catTail X.dom d = q.f ≫ catTail Y.dom d := hpt.trans hqt.symm
  -- `p`/`q` agree on the base over `V` after forgetting `d` (the pullback square).
  have hpf : (p.f ≫ catForget X.dom d) ≫ X.hom = z.hom ≫ catForget V d :=
    (Cat.assoc p.f (catForget X.dom d) X.hom).trans
      ((congrArg (p.f ≫ ·) (catMap_forget d X.hom).symm).trans
        ((Cat.assoc p.f (catMap d X.hom) (catForget V d)).symm.trans
          (congrArg (· ≫ catForget V d) hpw)))
  have hqf : (q.f ≫ catForget Y.dom d) ≫ Y.hom = z.hom ≫ catForget V d :=
    (Cat.assoc q.f (catForget Y.dom d) Y.hom).trans
      ((congrArg (q.f ≫ ·) (catMap_forget d Y.hom).symm).trans
        ((Cat.assoc q.f (catMap d Y.hom) (catForget V d)).symm.trans
          (congrArg (· ≫ catForget V d) hqw)))
  have hsq : (p.f ≫ catForget X.dom d) ≫ X.hom = (q.f ≫ catForget Y.dom d) ≫ Y.hom :=
    hpf.trans hqf.symm
  -- the base lift into the pullback point `P`, and the assembled `r.f`.
  let base := PB.lift ⟨z.dom, p.f ≫ catForget X.dom d, q.f ≫ catForget Y.dom d, hsq⟩
  have hbf : base ≫ PB.cone.π₁ = p.f ≫ catForget X.dom d := PB.lift_fst _
  have hbs : base ≫ PB.cone.π₂ = q.f ≫ catForget Y.dom d := PB.lift_snd _
  let rf := catArrange (overProdPt X Y).dom d base (p.f ≫ catTail X.dom d)
  have hrforget : rf ≫ catForget (overProdPt X Y).dom d = base :=
    catArrange_forget _ _ _ _
  have hrtail : rf ≫ catTail (overProdPt X Y).dom d = p.f ≫ catTail X.dom d :=
    catArrange_tail _ _ _ _
  -- a `catMap`-projection through `rf`: `rf ≫ catMap d g ≫ catForget = base ≫ g` (term-side).
  have rfForget : ∀ {t : List 𝒞} (g : listProd (𝒞 := 𝒞) (overProdPt X Y).dom ⟶ listProd t),
      rf ≫ (catMap d g ≫ catForget t d) = base ≫ g := fun g =>
    (congrArg (rf ≫ ·) (catMap_forget d g)).trans
      ((Cat.assoc rf (catForget (overProdPt X Y).dom d) g).symm.trans
        (congrArg (· ≫ g) hrforget))
  have rfTail : ∀ {t : List 𝒞} (g : listProd (𝒞 := 𝒞) (overProdPt X Y).dom ⟶ listProd t),
      rf ≫ (catMap d g ≫ catTail t d) = p.f ≫ catTail X.dom d := fun g =>
    (congrArg (rf ≫ ·) (catMap_tail d g)).trans hrtail
  -- the over-hom law `rf ≫ catMap d (π₁ ≫ X.hom) = z.hom`.
  have hrw : rf ≫ catMap d (overProdPt X Y).hom = z.hom := by
    apply cat_jointly_monic V d
    · rw [Cat.assoc, rfForget (overProdPt X Y).hom]
      show base ≫ (PB.cone.π₁ ≫ X.hom) = z.hom ≫ catForget V d
      rw [← Cat.assoc, hbf]; exact hpf
    · rw [Cat.assoc, rfTail (overProdPt X Y).hom]; exact hpt
  refine ⟨⟨rf, hrw⟩, ?_, ?_⟩
  · -- `r ≫ Fst = p` reduces to `rf ≫ catMap d π₁ = p.f`.
    apply OverHom.ext
    show rf ≫ catMap d (overProdFst X Y).f = p.f
    apply cat_jointly_monic X.dom d
    · rw [Cat.assoc, rfForget (overProdFst X Y).f]
      show base ≫ PB.cone.π₁ = p.f ≫ catForget X.dom d; exact hbf
    · rw [Cat.assoc]; exact rfTail (overProdFst X Y).f
  · -- `r ≫ Snd = q` reduces to `rf ≫ catMap d π₂ = q.f`.
    apply OverHom.ext
    show rf ≫ catMap d (overProdSnd X Y).f = q.f
    apply cat_jointly_monic Y.dom d
    · rw [Cat.assoc, rfForget (overProdSnd X Y).f]
      show base ≫ PB.cone.π₂ = q.f ≫ catForget Y.dom d; exact hbs
    · rw [Cat.assoc, rfTail (overProdSnd X Y).f]; exact htail

/-- Monic half of **equalizer**-preservation for `sliceCatObj d`: the image of the slice equalizer map
    is monic (`hepres`).  RESIDUAL: equalizer-of-singletons computation. -/
theorem sliceCatObj_eq_mono [HasEqualizers 𝒞] (d : List 𝒞) {V : Infl 𝒞} {X Y : Over (B := V)} (f g : X ⟶ Y)
    (z : Over (B := (V ++ d : List 𝒞)))
    (u v : z ⟶ sliceCatObj d (eqObj f g))
    (h : u ≫ (sliceCatFunctor d V).map (eqMap f g) = v ≫ (sliceCatFunctor d V).map (eqMap f g)) :
    u = v := by
  apply OverHom.ext
  show u.f = v.f
  -- abbreviations: `E = (eqObj f g).dom` (a `List 𝒞`), `em = (eqMap f g).f` (its base arrow).
  -- `(eqMap f g).f` is `eqMap f.f g.f` in `Infl 𝒞` (defeq), so `eqMap_eq`/`eqLift_uniq` apply.
  have hh : u.f ≫ catMap d (eqMap f g).f = v.f ≫ catMap d (eqMap f g).f := congrArg OverHom.f h
  -- the base equalizer map `(eqMap f g).f` is monic (inline, via `eqLift_uniq` in `Infl 𝒞`).
  have em_mono : ∀ {W : Infl 𝒞} (a b : W ⟶ (eqObj f g).dom),
      a ≫ (eqMap f g).f = b ≫ (eqMap f g).f → a = b := by
    intro W a b hab
    have hk : (a ≫ (eqMap f g).f) ≫ f.f = (a ≫ (eqMap f g).f) ≫ g.f := by
      rw [Cat.assoc, Cat.assoc]
      exact congrArg (a ≫ ·) (congrArg OverHom.f (eqMap_eq f g))
    rw [eqLift_uniq f.f g.f (a ≫ (eqMap f g).f) hk a rfl,
        eqLift_uniq f.f g.f (a ≫ (eqMap f g).f) hk b hab.symm]
  apply cat_jointly_monic (eqObj f g).dom d
  · -- forget leg: post-compose with `catForget`, then `em`-mono.
    apply em_mono
    -- `(w ≫ catForget E d) ≫ em = (w ≫ catMap d em) ≫ catForget X.dom d` term-side.
    have key : ∀ (w : listProd (𝒞 := 𝒞) z.dom ⟶ listProd (𝒞 := 𝒞) ((eqObj f g).dom ++ d)),
        (w ≫ catForget (eqObj f g).dom d) ≫ (eqMap f g).f
          = (w ≫ catMap d (eqMap f g).f) ≫ catForget X.dom d := fun w =>
      ((Cat.assoc w (catForget (eqObj f g).dom d) (eqMap f g).f).trans
        (congrArg (w ≫ ·) (catMap_forget d (eqMap f g).f).symm)).trans
          (Cat.assoc w (catMap d (eqMap f g).f) (catForget X.dom d)).symm
    exact (key u.f).trans ((congrArg (· ≫ catForget X.dom d) hh).trans (key v.f).symm)
  · -- tail leg: post-compose with `catTail`, use `catMap_tail` term-side.
    have key : ∀ (w : listProd (𝒞 := 𝒞) z.dom ⟶ listProd (𝒞 := 𝒞) ((eqObj f g).dom ++ d)),
        w ≫ catTail (eqObj f g).dom d
          = (w ≫ catMap d (eqMap f g).f) ≫ catTail X.dom d := fun w =>
      (congrArg (w ≫ ·) (catMap_tail d (eqMap f g).f).symm).trans
        (Cat.assoc w (catMap d (eqMap f g).f) (catTail X.dom d)).symm
    exact (key u.f).trans ((congrArg (· ≫ catTail X.dom d) hh).trans (key v.f).symm)

/-- Lift half of equalizer-preservation for `sliceCatObj d` (`hepres_lift`).  RESIDUAL. -/
theorem sliceCatObj_eq_lift [HasEqualizers 𝒞] (d : List 𝒞) {V : Infl 𝒞} {X Y : Over (B := V)} (f g : X ⟶ Y)
    (z : Over (B := (V ++ d : List 𝒞)))
    (k : z ⟶ sliceCatObj d X)
    (hk : k ≫ (sliceCatFunctor d V).map f = k ≫ (sliceCatFunctor d V).map g) :
    ∃ r : z ⟶ sliceCatObj d (eqObj f g), r ≫ (sliceCatFunctor d V).map (eqMap f g) = k := by
  -- triangle datum from `k`, and `hk` projected to the base over `V`.
  have hkw : k.f ≫ catMap d X.hom = z.hom := k.w
  have hhk : k.f ≫ catMap d f.f = k.f ≫ catMap d g.f := congrArg OverHom.f hk
  -- `k.f ≫ catForget X.dom d` equalizes `f.f, g.f` (base), so it lifts through `eqMap f.f g.f`.
  have heq : (k.f ≫ catForget X.dom d) ≫ f.f = (k.f ≫ catForget X.dom d) ≫ g.f := by
    have lhs : (k.f ≫ catForget X.dom d) ≫ f.f = k.f ≫ (catMap d f.f ≫ catForget Y.dom d) :=
      (Cat.assoc k.f (catForget X.dom d) f.f).trans
        (congrArg (k.f ≫ ·) (catMap_forget d f.f).symm)
    have rhs : (k.f ≫ catForget X.dom d) ≫ g.f = k.f ≫ (catMap d g.f ≫ catForget Y.dom d) :=
      (Cat.assoc k.f (catForget X.dom d) g.f).trans
        (congrArg (k.f ≫ ·) (catMap_forget d g.f).symm)
    rw [lhs, rhs, ← Cat.assoc, ← Cat.assoc, hhk]
  let base := eqLift f.f g.f (k.f ≫ catForget X.dom d) heq
  have hbase : base ≫ (eqMap f g).f = k.f ≫ catForget X.dom d := eqLift_fac f.f g.f _ heq
  let rf := catArrange (eqObj f g).dom d base (k.f ≫ catTail X.dom d)
  have hrforget : rf ≫ catForget (eqObj f g).dom d = base := catArrange_forget _ _ _ _
  have hrtail : rf ≫ catTail (eqObj f g).dom d = k.f ≫ catTail X.dom d := catArrange_tail _ _ _ _
  -- term-side projections of `rf` through `catMap d g`.
  have rfForget : ∀ {t : List 𝒞} (g' : listProd (𝒞 := 𝒞) (eqObj f g).dom ⟶ listProd t),
      rf ≫ (catMap d g' ≫ catForget t d) = base ≫ g' := fun g' =>
    (congrArg (rf ≫ ·) (catMap_forget d g')).trans
      ((Cat.assoc rf (catForget (eqObj f g).dom d) g').symm.trans
        (congrArg (· ≫ g') hrforget))
  have rfTail : ∀ {t : List 𝒞} (g' : listProd (𝒞 := 𝒞) (eqObj f g).dom ⟶ listProd t),
      rf ≫ (catMap d g' ≫ catTail t d) = k.f ≫ catTail X.dom d := fun g' =>
    (congrArg (rf ≫ ·) (catMap_tail d g')).trans hrtail
  -- `k.f` projected over `V` after forgetting/tailing `d` (both pulled from `k.w`).
  have hkf : (k.f ≫ catForget X.dom d) ≫ X.hom = z.hom ≫ catForget V d :=
    (Cat.assoc k.f (catForget X.dom d) X.hom).trans
      ((congrArg (k.f ≫ ·) (catMap_forget d X.hom).symm).trans
        ((Cat.assoc k.f (catMap d X.hom) (catForget V d)).symm.trans
          (congrArg (· ≫ catForget V d) hkw)))
  have hkt : k.f ≫ catTail X.dom d = z.hom ≫ catTail V d :=
    (congrArg (k.f ≫ ·) (catMap_tail d X.hom).symm).trans
      ((Cat.assoc k.f (catMap d X.hom) (catTail V d)).symm.trans
        (congrArg (· ≫ catTail V d) hkw))
  -- the over-hom law `rf ≫ catMap d ((eqObj f g).hom) = z.hom`.
  have hrw : rf ≫ catMap d (eqObj f g).hom = z.hom := by
    apply cat_jointly_monic V d
    · rw [Cat.assoc, rfForget (eqObj f g).hom]
      show base ≫ ((eqMap f g).f ≫ X.hom) = z.hom ≫ catForget V d
      rw [← Cat.assoc, hbase]; exact hkf
    · rw [Cat.assoc, rfTail (eqObj f g).hom]; exact hkt
  refine ⟨⟨rf, hrw⟩, ?_⟩
  -- `r ≫ map(eqMap f g) = k` reduces to `rf ≫ catMap d em = k.f`.
  apply OverHom.ext
  show rf ≫ catMap d (eqMap f g).f = k.f
  apply cat_jointly_monic X.dom d
  · rw [Cat.assoc, rfForget (eqMap f g).f]; exact hbase
  · rw [Cat.assoc]; exact rfTail (eqMap f g).f

/-! ### The strict slice transition PRESERVES covers and monos

  The §1.547 transition functor `sliceCatFunctor d` is base-change by concatenation, hence sends slice
  covers/monos to slice covers/monos.  Both reduce, on underlying `Infl`-arrows (`.f`), to the
  `catMap`-level facts `catMap_cover`/`catMap_mono` via the §1.531 slice⟷base correspondence
  (`cover_f_of_cover`/`cover_of_cover_f`, `sigma_preserves_mono`/`cover_of_cover_f`).  These are the
  per-transition `hcovpres`/`hmono` ingredients the generic `colimitCanonicalCover` bridge consumes. -/

/-- **`sliceCatFunctor d` preserves covers**: a slice cover `φ : X ⟶ Y` of `A′/V` maps to a slice
    cover of `A′/(V++d)`.  Underlying: `(sliceCatMap d φ).f = catMap d φ.f`, and `catMap d` preserves
    covers (`catMap_cover`), bridged by the §1.531 cover correspondence. -/
theorem sliceCatObj_cover [HasEqualizers 𝒞] [PullbacksTransferCovers 𝒞] (d : List 𝒞) {V : Infl 𝒞}
    {X Y : Over (B := V)} (φ : X ⟶ Y) (hφ : Cover (𝒞 := Over (B := V)) φ) :
    Cover (𝒞 := Over (B := (V ++ d : List 𝒞))) (sliceCatMap d φ) :=
  letI : HasPullbacks (Infl 𝒞) := inflHasPullbacks
  cover_of_cover_f (𝒞 := Infl 𝒞) (B := V ++ d) (sliceCatMap d φ)
    (catMap_cover d (cover_f_of_cover (𝒞 := Infl 𝒞) (B := V) φ hφ))

/-- **`sliceCatFunctor d` preserves monos**: a slice mono `φ` of `A′/V` maps to a slice mono of
    `A′/(V++d)`.  Underlying: `catMap d` preserves monos (`catMap_mono`), bridged by the §1.531
    mono correspondence (`sigma_preserves_mono` / `cover_of_cover_f`-style mono reflection). -/
theorem sliceCatObj_mono [HasEqualizers 𝒞] (d : List 𝒞) {V : Infl 𝒞} {X Y : Over (B := V)}
    (φ : X ⟶ Y) (hφ : OverMono (B := V) φ) :
    OverMono (B := (V ++ d : List 𝒞)) (sliceCatMap d φ) := by
  letI : HasPullbacks (Infl 𝒞) := inflHasPullbacks
  -- underlying mono of `catMap d φ.f` (`catMap_mono` + `sigma_preserves_mono`), then reflect to the slice.
  have hf : Monic (𝒞 := Infl 𝒞) (catMap d φ.f) := catMap_mono d (sigma_preserves_mono φ hφ)
  -- `(sliceCatMap d φ).f = catMap d φ.f`, so a slice mono follows from `sigma_reflects_mono`.
  intro W g h hgh
  exact sigma_reflects_mono (𝒞 := Infl 𝒞) (B := V ++ d) (sliceCatMap d φ) hf g h hgh

/-! ### Lifting the strict `sliceCatObj` preservation through the chain transition

  `(chainSliceSystem P).F hij = innerSliceTr (P.prefix hij)` and `.functF hij = chainSliceFunctor P hij
  = transportSliceFunctor e (sliceCatFunctor d)` with `d = prefixSuffix (chain i) (chain j)`,
  `e : chain i ++ d = chain j`.  The transport `e ▸ -` is an iso (it re-types the base only); so the
  package hypotheses `colimitPreRegular` consumes — stated with `F`/`functF` — follow from the strict
  `sliceCatObj_*`/`innerSliceTr_terminal` facts after transporting.  We assemble the colimit's
  `PreRegularCategory` for `chainSliceSystem`.  RESIDUAL (`hcanon`): the canonical-pullback cover
  transfer in the colimit — the same part the OUTER tower defers, here from per-stage
  `PullbacksTransferCovers (Over (chain n))` (`overPreRegular`) + cover reflection. -/

section InnerPackage
variable [PreRegularCategory 𝒞] [HasEqualizers 𝒞]
  {ι : Type u} {D : Colim.Directed ι} (O : OrdChain D 𝒞)

/-- **GENERIC** per-stage terminal of the inner system over ANY directed index: each stage `Over (chain i)`
    has the slice terminal. -/
def ordChainHasTerminal (i : ι) : HasTerminal ((ordChainSliceSystem O).A i) :=
  overHasTerminal (O.chain i)

/-- **GENERIC** terminal preservation (`htpres`) — `innerSliceTr_terminal`, any index. -/
theorem ordChainHtpres {i j : ι} (hij : D.le i j) :
    (ordChainSliceSystem O).F hij (ordChainHasTerminal O i).one = (ordChainHasTerminal O j).one :=
  innerSliceTr_terminal (O.mono hij)

/-- **GENERIC** per-stage binary products. -/
def ordChainHasProducts (i : ι) : HasBinaryProducts ((ordChainSliceSystem O).A i) :=
  overHasBinaryProducts (O.chain i)

/-- **GENERIC** per-stage equalizers. -/
def ordChainHasEqualizers (i : ι) : HasEqualizers ((ordChainSliceSystem O).A i) :=
  overHasEqualizers (O.chain i)

/-! ### §1.546  Transition cover-reflection: `catForget` is a cover for a well-supported suffix

  The strict suffix-append transition `catMap d` (§1.547, `chainSliceFunctor`'s underlying arrow) is a
  pullback of its argument along the projection `catForget t d : ∏(t++d) ⟶ ∏t` (`catMap_isPullback`).
  That projection is a COVER exactly when the appended suffix `∏d` is WELL-SUPPORTED — the §1.546
  precondition the relative-capitalization successor supplies.  Cover-of-`catForget` is the KEY UNLOCK
  that discharges the transition faithfulness / conservativity (`hfaith`/`hcons`) `colimitCanonicalCover`
  needs: `catMap d f = catMap d g ⟹ catForget s d ≫ f = catForget s d ≫ g ⟹ f = g` (`cover_epi`). -/

/-- The left-product map `id_B × x = pair fst (snd ≫ x) : B×A₁ ⟶ B×A₂` is a cover when `x` is.
    It is the pullback of `x` along `snd : B×A₂ ⟶ A₂` (`prod_pullback`, with the cone swapped so the
    transferred leg is `π₂`); pre-regular pullbacks transfer the cover `x`. -/
theorem prodLeftMap_cover {B A1 A2 : 𝒞} (x : A1 ⟶ A2) (hx : Cover x) :
    Cover (pair (fst : prod B A1 ⟶ B) (snd ≫ x)) := by
  -- the §1.532 product-pullback square with `(x, snd)` as the cospan, `pair fst (snd≫x)` the leg
  -- parallel to `x`; pre-regular pullbacks transfer the cover `x` to this `π₂`.
  let c : Cone x (snd (A:=B) (B:=A2)) := ⟨prod B A1, snd, pair fst (snd ≫ x), by rw [snd_pair]⟩
  have hpb : c.IsPullback := by
    intro d
    refine ⟨pair (d.π₂ ≫ fst) d.π₁, ⟨?_, ?_⟩, ?_⟩
    · show pair (d.π₂ ≫ fst) d.π₁ ≫ snd = d.π₁; rw [snd_pair]
    · show pair (d.π₂ ≫ fst) d.π₁ ≫ pair fst (snd ≫ x) = d.π₂
      apply fst_snd_jointly_monic
      · rw [Cat.assoc, fst_pair, fst_pair]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, d.w]
    · intro v hv1 hv2
      apply fst_snd_jointly_monic
      · rw [fst_pair]
        have hh : v ≫ pair (fst : prod B A1 ⟶ B) (snd ≫ x) = d.π₂ := hv2
        have := congrArg (· ≫ (fst : prod B A2 ⟶ B)) hh
        simpa [Cat.assoc, fst_pair] using this
      · rw [snd_pair]; exact hv1
  show Cover c.π₂
  exact PullbacksTransferCovers.pullbacks_transfer_covers c hpb hx

/-- **§1.546 — `catForget s d` is a cover when the suffix product `∏d` is well-supported.**
    Induction on `s`: base `catForget [] d = term (∏d)` is a cover by `WellSupported`; step
    `catForget (a::s') d = pair fst (snd ≫ catForget s' d) = id_a × (catForget s' d)` is a cover by
    `prodLeftMap_cover` of the inductive cover. -/
theorem catForget_cover {d : List 𝒞} (hws : WellSupported (listProd (𝒞 := 𝒞) d)) :
    ∀ (s : List 𝒞), Cover (catForget (𝒞 := 𝒞) s d)
  | [] => hws
  | _a :: s' => prodLeftMap_cover (catForget s' d) (catForget_cover hws s')

/-- **§1.546 transition faithfulness (`hfaith`, underlying arrow).**  For a well-supported suffix
    `∏d`, the strict suffix-append `catMap d` is faithful on underlying arrows: `catMap d f =
    catMap d g ⟹ f = g`.  Post-compose with `catForget t d` (`catMap_forget`) to get
    `catForget s d ≫ f = catForget s d ≫ g`, then cancel the cover `catForget s d` (`cover_epi`). -/
theorem catMap_faithful {d : List 𝒞} (hws : WellSupported (listProd (𝒞 := 𝒞) d)) {s t : List 𝒞}
    (f g : listProd (𝒞 := 𝒞) s ⟶ listProd t) (h : catMap d f = catMap d g) : f = g := by
  apply cover_epi (catForget_cover (𝒞 := 𝒞) (d := d) hws s)
  rw [← catMap_forget d f, ← catMap_forget d g, h]

/-- **§1.546 transition conservativity (`hcons`, underlying arrow).**  For a well-supported suffix
    `∏d`, the strict suffix-append `catMap d` reflects isos on underlying arrows: `catMap d φ` iso
    ⟹ `φ` iso.  `φ` is MONO (`mono_of_comp_left` on the cover-square: from a cover `g`, if `φ ≫ ?`…
    — here proved via `catMap d φ` mono pulled back through the joint-monicity of `catForget`/`catTail`)
    and a COVER (`catForget s d ≫ φ = catMap d φ ≫ catForget t d` is iso∘cover, hence a cover, whose
    right factor `φ` is a cover); `monic_cover_iso` then makes `φ` iso.  Mirrors `sliceEmbedFaithful`. -/
theorem catMap_conservative {d : List 𝒞} (hws : WellSupported (listProd (𝒞 := 𝒞) d)) {s t : List 𝒞}
    (φ : listProd (𝒞 := 𝒞) s ⟶ listProd t) (hiso : IsIso (catMap d φ)) : IsIso φ := by
  obtain ⟨inv, hinv1, hinv2⟩ := hiso
  -- `φ` is a cover: `catForget s d ≫ φ = catMap d φ ≫ catForget t d` is `iso ∘ cover`, a cover; its
  -- right factor `φ` is a cover (a cover through `φ` factors `φ` as a cover too).
  have hφcover : Cover φ := by
    have hstep : catForget s d ≫ φ = catMap d φ ≫ catForget t d := (catMap_forget d φ).symm
    have hcov : Cover (catForget s d ≫ φ) := by
      rw [hstep]
      exact cover_precomp_iso ⟨inv, hinv1, hinv2⟩ (catForget_cover (𝒞 := 𝒞) (d := d) hws t)
    intro K m h hm hfac
    exact hcov m (catForget s d ≫ h) hm (by rw [Cat.assoc, hfac])
  -- `φ` is mono: `catMap d φ` mono (it is iso).  Given `u≫φ = v≫φ` (`u v : Z → ∏s`), lift each to
  -- `Z×∏d → ∏(s+d)` via `catArrange (fst≫u/v) snd` (forget-part `fst≫u`, tail-part `snd`).  Both lifts
  -- agree under `catMap d φ` (forget-parts `fst≫u≫φ = fst≫v≫φ`, tails `snd`), so `catMap d φ`-mono
  -- pins them equal; their forget-parts give `fst≫u = fst≫v`, and `fst : Z×∏d → Z` is a cover (`∏d`
  -- well-supported), hence epic, so `u = v`.  (No point on `∏d` is needed — only `fst` epic.)
  have hφmono : Monic φ := by
    have hcfMono : Monic (catMap d φ) := mono_of_retraction (catMap d φ) inv hinv1
    intro Z u v huv
    let p : prod Z (listProd (𝒞 := 𝒞) d) ⟶ listProd (s ++ d) := catArrange s d (fst ≫ u) snd
    let q : prod Z (listProd (𝒞 := 𝒞) d) ⟶ listProd (s ++ d) := catArrange s d (fst ≫ v) snd
    have hpq : p ≫ catMap d φ = q ≫ catMap d φ := by
      apply cat_jointly_monic t d
      · show (p ≫ catMap d φ) ≫ catForget t d = (q ≫ catMap d φ) ≫ catForget t d
        rw [Cat.assoc, catMap_forget, Cat.assoc, catMap_forget, ← Cat.assoc, ← Cat.assoc]
        show (catArrange s d (fst ≫ u) snd ≫ catForget s d) ≫ φ
            = (catArrange s d (fst ≫ v) snd ≫ catForget s d) ≫ φ
        rw [catArrange_forget s d (fst ≫ u) snd, catArrange_forget s d (fst ≫ v) snd,
            Cat.assoc, Cat.assoc, huv]
      · show (p ≫ catMap d φ) ≫ catTail t d = (q ≫ catMap d φ) ≫ catTail t d
        rw [Cat.assoc, catMap_tail, Cat.assoc, catMap_tail]
        show catArrange s d (fst ≫ u) snd ≫ catTail s d = catArrange s d (fst ≫ v) snd ≫ catTail s d
        rw [catArrange_tail s d (fst ≫ u) snd, catArrange_tail s d (fst ≫ v) snd]
    have heq := hcfMono p q hpq
    have hfst : (fst : prod Z (listProd (𝒞 := 𝒞) d) ⟶ Z) ≫ u
        = (fst : prod Z (listProd (𝒞 := 𝒞) d) ⟶ Z) ≫ v := by
      have := congrArg (· ≫ catForget s d) heq
      simpa [p, q, catArrange_forget] using this
    exact cover_epi (prod_fst_cover hws) hfst
  exact monic_cover_iso φ hφcover hφmono

/-- **`sliceCatFunctor d` is CONSERVATIVE** (reflects slice isos) when `∏d` is well-supported.  From a
    slice iso of `sliceCatMap d φ` take the underlying `IsIso (catMap d φ.f)` (`overIso_underlying`),
    reflect it to `IsIso φ.f` (`catMap_conservative`), then re-wrap to a slice iso
    (`overIso_of_underlying`).  The slice-level mate of `catMap_conservative` — the per-transition
    `hcons` ingredient. -/
theorem sliceCatObj_conservative (d : List 𝒞) (hws : WellSupported (listProd (𝒞 := 𝒞) d))
    {V : Infl 𝒞} {X Y : Over (B := V)} (φ : OverHom X Y)
    (hiso : OverIso (B := (V ++ d : List 𝒞)) (sliceCatMap d φ)) : OverIso (B := V) φ :=
  overIso_of_underlying φ (catMap_conservative (d := d) hws φ.f (overIso_underlying hiso))

/-- **GENERIC** product joint-monicity preservation (`hppres`) — lifts `sliceCatObj_prod_jointly_monic`
    through the base-transport of `ordChainSliceFunctor`, any index. -/
theorem ordChainHppres {i j : ι} (hij : D.le i j)
    (a b : (ordChainSliceSystem O).A i) (z : (ordChainSliceSystem O).A j)
    (u v : z ⟶ (ordChainSliceSystem O).F hij ((ordChainHasProducts O i).prod a b))
    (hf : u ≫ ((ordChainSliceSystem O).functF hij).map (ordChainHasProducts O i).fst
        = v ≫ ((ordChainSliceSystem O).functF hij).map (ordChainHasProducts O i).fst)
    (hs : u ≫ ((ordChainSliceSystem O).functF hij).map (ordChainHasProducts O i).snd
        = v ≫ ((ordChainSliceSystem O).functF hij).map (ordChainHasProducts O i).snd) : u = v := by
  -- Unfold the system pieces so `z`, `u`, `v` mention only `innerSliceTr`/`ordChainSliceFunctor`.
  revert z u v hf hs
  show ∀ (z : Over (B := (O.chain j : Infl 𝒞)))
      (u v : z ⟶ innerSliceTr (O.mono hij) (overProdPt a b)),
      u ≫ (ordChainSliceFunctor O hij).map (overProdFst a b)
        = v ≫ (ordChainSliceFunctor O hij).map (overProdFst a b) →
      u ≫ (ordChainSliceFunctor O hij).map (overProdSnd a b)
        = v ≫ (ordChainSliceFunctor O hij).map (overProdSnd a b) →
      u = v
  -- `innerSliceTr h = e ▸ sliceCatObj d`; `ordChainSliceFunctor = transportSliceFunctor e (sliceCatFunctor d)`.
  unfold innerSliceTr ordChainSliceFunctor
  -- generalise the suffix `d`, codomain base `W` and the transport proof `e`; `cases e` collapses every
  -- transport, reducing to the strict `sliceCatObj_prod_jointly_monic` over `chain i ++ d`.
  have gen : ∀ (d : List 𝒞) (W : Infl 𝒞) (e : (O.chain i : List 𝒞) ++ d = W) (z : Over W)
      (u v : z ⟶ e ▸ sliceCatObj d (overProdPt a b)),
      u ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (overProdFst a b)
        = v ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (overProdFst a b) →
      u ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (overProdSnd a b)
        = v ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (overProdSnd a b) →
      u = v := by
    intro d W e; cases e; exact sliceCatObj_prod_jointly_monic d a b
  exact gen _ _ (prefixSuffix_eq (O.mono hij))

/-- **GENERIC** product pairing preservation (`hppres_pair`), any index. -/
theorem ordChainHppresPair {i j : ι} (hij : D.le i j)
    (a b : (ordChainSliceSystem O).A i) (z : (ordChainSliceSystem O).A j)
    (p : z ⟶ (ordChainSliceSystem O).F hij a) (q : z ⟶ (ordChainSliceSystem O).F hij b) :
    ∃ r : z ⟶ (ordChainSliceSystem O).F hij ((ordChainHasProducts O i).prod a b),
      r ≫ ((ordChainSliceSystem O).functF hij).map (ordChainHasProducts O i).fst = p ∧
      r ≫ ((ordChainSliceSystem O).functF hij).map (ordChainHasProducts O i).snd = q := by
  revert z p q
  show ∀ (z : Over (B := (O.chain j : Infl 𝒞)))
      (p : z ⟶ innerSliceTr (O.mono hij) a) (q : z ⟶ innerSliceTr (O.mono hij) b),
      ∃ r : z ⟶ innerSliceTr (O.mono hij) (overProdPt a b),
        r ≫ (ordChainSliceFunctor O hij).map (overProdFst a b) = p ∧
        r ≫ (ordChainSliceFunctor O hij).map (overProdSnd a b) = q
  unfold innerSliceTr ordChainSliceFunctor
  -- generalise the suffix `d`, codomain base `W`, transport `e`; `cases e` reduces to `sliceCatObj_prod_pair`.
  have gen : ∀ (d : List 𝒞) (W : Infl 𝒞) (e : (O.chain i : List 𝒞) ++ d = W) (z : Over W)
      (p : z ⟶ e ▸ sliceCatObj d a) (q : z ⟶ e ▸ sliceCatObj d b),
      ∃ r : z ⟶ e ▸ sliceCatObj d (overProdPt a b),
        r ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (overProdFst a b) = p ∧
        r ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (overProdSnd a b) = q := by
    intro d W e; cases e; exact sliceCatObj_prod_pair d a b
  exact gen _ _ (prefixSuffix_eq (O.mono hij))

/-- **GENERIC** equalizer-mono preservation (`hepres`), any index. -/
theorem ordChainHepres {i j : ι} (hij : D.le i j)
    {A B : (ordChainSliceSystem O).A i} (f g : A ⟶ B) (z : (ordChainSliceSystem O).A j)
    (u v : z ⟶ (ordChainSliceSystem O).F hij
      (@eqObj _ ((ordChainSliceSystem O).catA i) (ordChainHasEqualizers O i) _ _ f g))
    (h : u ≫ ((ordChainSliceSystem O).functF hij).map
          (@eqMap _ ((ordChainSliceSystem O).catA i) (ordChainHasEqualizers O i) _ _ f g)
        = v ≫ ((ordChainSliceSystem O).functF hij).map
          (@eqMap _ ((ordChainSliceSystem O).catA i) (ordChainHasEqualizers O i) _ _ f g)) : u = v := by
  revert z u v h
  -- `(ordChainSliceSystem O).catA i`/`ordChainHasEqualizers O i` are defeq `overCat`/`overHasEqualizers`,
  -- so the `@eqObj`/`@eqMap` here ARE the plain `Over`-equalizer used by `sliceCatObj_eq_mono`.
  letI E := ordChainHasEqualizers O i
  show ∀ (z : Over (B := (O.chain j : Infl 𝒞)))
      (u v : z ⟶ innerSliceTr (O.mono hij) (@eqObj _ _ E _ _ f g)),
      u ≫ (ordChainSliceFunctor O hij).map (@eqMap _ _ E _ _ f g)
        = v ≫ (ordChainSliceFunctor O hij).map (@eqMap _ _ E _ _ f g) → u = v
  unfold innerSliceTr ordChainSliceFunctor
  -- generalise the suffix `d`, codomain base `W`, transport `e`; `cases e` reduces to `sliceCatObj_eq_mono`.
  have gen : ∀ (d : List 𝒞) (W : Infl 𝒞) (e : (O.chain i : List 𝒞) ++ d = W) (z : Over W)
      (u v : z ⟶ e ▸ sliceCatObj d (@eqObj _ _ E _ _ f g)),
      u ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (@eqMap _ _ E _ _ f g)
        = v ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (@eqMap _ _ E _ _ f g) →
      u = v := by
    intro d W e; cases e; exact sliceCatObj_eq_mono d f g
  exact gen _ _ (prefixSuffix_eq (O.mono hij))

/-- **GENERIC** equalizer-lift preservation (`hepres_lift`), any index. -/
theorem ordChainHepresLift {i j : ι} (hij : D.le i j)
    {A B : (ordChainSliceSystem O).A i} (f g : A ⟶ B) (z : (ordChainSliceSystem O).A j)
    (k : z ⟶ (ordChainSliceSystem O).F hij A)
    (hk : k ≫ ((ordChainSliceSystem O).functF hij).map f
        = k ≫ ((ordChainSliceSystem O).functF hij).map g) :
    ∃ r : z ⟶ (ordChainSliceSystem O).F hij
        (@eqObj _ ((ordChainSliceSystem O).catA i) (ordChainHasEqualizers O i) _ _ f g),
      r ≫ ((ordChainSliceSystem O).functF hij).map
        (@eqMap _ ((ordChainSliceSystem O).catA i) (ordChainHasEqualizers O i) _ _ f g) = k := by
  revert z k hk
  -- `(ordChainSliceSystem O).catA i`/`ordChainHasEqualizers O i` are defeq `overCat`/`overHasEqualizers`,
  -- so the `@eqObj`/`@eqMap` here ARE the plain `Over`-equalizer used by `sliceCatObj_eq_lift`.
  letI E := ordChainHasEqualizers O i
  show ∀ (z : Over (B := (O.chain j : Infl 𝒞))) (k : z ⟶ innerSliceTr (O.mono hij) A),
      k ≫ (ordChainSliceFunctor O hij).map f = k ≫ (ordChainSliceFunctor O hij).map g →
      ∃ r : z ⟶ innerSliceTr (O.mono hij) (@eqObj _ _ E _ _ f g),
        r ≫ (ordChainSliceFunctor O hij).map (@eqMap _ _ E _ _ f g) = k
  unfold innerSliceTr ordChainSliceFunctor
  -- generalise the suffix `d`, codomain base `W`, transport `e`; `cases e` reduces to `sliceCatObj_eq_lift`.
  have gen : ∀ (d : List 𝒞) (W : Infl 𝒞) (e : (O.chain i : List 𝒞) ++ d = W) (z : Over W)
      (k : z ⟶ e ▸ sliceCatObj d A),
      k ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map f
        = k ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map g →
      ∃ r : z ⟶ e ▸ sliceCatObj d (@eqObj _ _ E _ _ f g),
        r ≫ (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map (@eqMap _ _ E _ _ f g)
          = k := by
    intro d W e; cases e; exact sliceCatObj_eq_lift d f g
  exact gen _ _ (prefixSuffix_eq (O.mono hij))

/-! ### Cover-preservation / mono-preservation / per-stage PTC for the inner system

  The remaining ingredients the generic `colimitCanonicalCover` bridge consumes for `ordChainSliceSystem`:
  every transition preserves covers (`hcovpres`) and monos (`hmono`), and every stage is a
  `PullbacksTransferCovers` (`hstagePTC`).  The first two lift the strict `sliceCatObj_cover` /
  `sliceCatObj_mono` through the base-transport (the `unfold`/`cases e` pattern of `ordChainHppres`);
  the last is `overPullbacksTransferCovers` on `Over (chain i : Infl 𝒞)` (each stage is the slice of the
  pre-regular inflation `A′`, `inflPullbacksTransferCovers`). -/

/-- **GENERIC** cover-preservation (`hcovpres`) — the inner transition `ordChainSliceFunctor O hij` sends
    covers to covers, lifting `sliceCatObj_cover` through the base-transport, any index. -/
theorem ordChainHcovpres {i j : ι} (hij : D.le i j) {x y : (ordChainSliceSystem O).A i}
    (φ : x ⟶ y) (hφ : Cover (𝒞 := (ordChainSliceSystem O).A i) φ) :
    Cover (𝒞 := (ordChainSliceSystem O).A j) ((ordChainSliceFunctor O hij).map φ) := by
  -- reduce to the strict `sliceCatObj_cover` over `chain i ++ d` by collapsing the transport.
  revert hφ
  unfold ordChainSliceFunctor
  have gen : ∀ (d : List 𝒞) (W : Infl 𝒞) (e : (O.chain i : List 𝒞) ++ d = W),
      Cover (𝒞 := Over (B := (O.chain i : Infl 𝒞))) φ →
      Cover (𝒞 := Over W) ((transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map φ) := by
    intro d W e; cases e; exact fun hφ => sliceCatObj_cover d φ hφ
  exact gen _ _ (prefixSuffix_eq (O.mono hij))

/-- **GENERIC** mono-preservation (`hmono`) — the inner transition sends monos to monos, lifting
    `sliceCatObj_mono` through the base-transport, any index. -/
theorem ordChainHmono {i j : ι} (hij : D.le i j) {x y : (ordChainSliceSystem O).A i}
    (φ : x ⟶ y) (hφ : Monic (𝒞 := (ordChainSliceSystem O).A i) φ) :
    Monic (𝒞 := (ordChainSliceSystem O).A j) ((ordChainSliceFunctor O hij).map φ) := by
  revert hφ
  unfold ordChainSliceFunctor
  have gen : ∀ (d : List 𝒞) (W : Infl 𝒞) (e : (O.chain i : List 𝒞) ++ d = W),
      OverMono (B := (O.chain i : Infl 𝒞)) φ →
      OverMono (B := W) ((transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map φ) := by
    intro d W e; cases e; exact fun hφ => sliceCatObj_mono d φ hφ
  exact gen _ _ (prefixSuffix_eq (O.mono hij))

/-- **GENERIC** transition FAITHFULNESS (`hfaith`) — the inner transition separates slice morphisms,
    lifting `sliceCatObj_faithful` through the base-transport, GIVEN the appended suffix product
    `∏(prefixSuffix (chain i) (chain j))` is well-supported (the §1.546 precondition).  The `cases e`
    collapse reduces to the strict `sliceCatObj_faithful` over `chain i ++ d`. -/
theorem ordChainHfaith {i j : ι} (hij : D.le i j)
    (hws : WellSupported (listProd (𝒞 := 𝒞) (prefixSuffix (O.chain i) (O.chain j))))
    {x y : (ordChainSliceSystem O).A i} (p q : x ⟶ y)
    (h : ((ordChainSliceFunctor O hij).map p) = ((ordChainSliceFunctor O hij).map q)) : p = q := by
  revert h
  unfold ordChainSliceFunctor
  have gen : ∀ (d : List 𝒞) (W : Infl 𝒞) (e : (O.chain i : List 𝒞) ++ d = W)
      (hwsd : WellSupported (listProd (𝒞 := 𝒞) d)),
      (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map p
        = (transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map q → p = q := by
    intro d W e hwsd; cases e
    exact fun h => OverHom.ext (catMap_faithful (d := d) hwsd p.f q.f (congrArg OverHom.f h))
  exact gen _ _ (prefixSuffix_eq (O.mono hij)) hws

/-- **GENERIC** transition CONSERVATIVITY (`hcons`) — the inner transition reflects slice isos, lifting
    `sliceCatObj_conservative` through the base-transport, GIVEN the appended suffix product is
    well-supported.  Mate of `ordChainHfaith`. -/
theorem ordChainHcons {i j : ι} (hij : D.le i j)
    (hws : WellSupported (listProd (𝒞 := 𝒞) (prefixSuffix (O.chain i) (O.chain j))))
    {x y : (ordChainSliceSystem O).A i} (φ : x ⟶ y)
    (hiso : IsIso (𝒞 := (ordChainSliceSystem O).A j) ((ordChainSliceFunctor O hij).map φ)) :
    IsIso (𝒞 := (ordChainSliceSystem O).A i) φ := by
  revert hiso
  unfold ordChainSliceFunctor
  have gen : ∀ (d : List 𝒞) (W : Infl 𝒞) (e : (O.chain i : List 𝒞) ++ d = W)
      (hwsd : WellSupported (listProd (𝒞 := 𝒞) d)),
      OverIso (B := W) ((transportSliceFunctor e (sliceCatFunctor d (O.chain i))).map φ) →
      OverIso (B := (O.chain i : Infl 𝒞)) φ := by
    intro d W e hwsd; cases e; exact fun hiso => sliceCatObj_conservative d hwsd φ hiso
  exact gen _ _ (prefixSuffix_eq (O.mono hij)) hws

/-- **GENERIC** per-stage `PullbacksTransferCovers` (`hstagePTC`) — each stage `Over (chain i : A′)` is
    the slice of the pre-regular inflation `A′` (`inflPullbacksTransferCovers`), hence pre-regular by the
    §1.53 slice lemma (`overPullbacksTransferCovers`). -/
def ordChainStagePTC (i : ι) :
    PullbacksTransferCovers ((ordChainSliceSystem O).A i) :=
  letI : HasPullbacks (Infl 𝒞) := inflHasPullbacks
  overPullbacksTransferCovers (O.chain i : Infl 𝒞)

open Freyd.Colim in
/-- **GENERIC §1.544-546 (B-package) — the inner `OrdChain`-slice colimit is PRE-REGULAR over ANY directed
    index.**  Assembles `colimitPreRegular` for `ordChainSliceSystem O` from the strict suffix-append
    preservation facts (`innerSliceTr_terminal`, `sliceCatObj_prod_*`, `sliceCatObj_eq_*`) lifted through
    the base-transport, plus the canonical cover-transfer `hcanon`.  This is the transfinite-ready
    relative-capitalization successor `S → S*` (§1.543) at the level of pre-regular structure: index by a
    well-ordered set (`Ordinal`/`WellFoundedLT` as a `Colim.Directed`) and a cofinal `OrdChain` to point
    EVERY well-supported object of an uncountable object set.  The ω-chain `chainSlicePreRegular` is its
    `uliftNatDirected` specialization. -/
noncomputable def ordChainSlicePreRegular [Nonempty ι]
    (hcanon : letI : Cat (ordChainSliceSystem O).Obj := colimitCat _ (ordChainSliceCoherent O)
        letI : HasPullbacks (ordChainSliceSystem O).Obj :=
          colimitHasPullbacks _ (ordChainSliceCoherent O)
            (ordChainHasTerminal O) (ordChainHtpres O) (ordChainHasProducts O)
            (ordChainHppres O) (ordChainHppresPair O)
            (ordChainHasEqualizers O) (ordChainHepres O) (ordChainHepresLift O)
      ∀ {X Y Z : (ordChainSliceSystem O).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
          Cover f → Cover (HasPullbacks.has f g).cone.π₂) :
    @PreRegularCategory (ordChainSliceSystem O).Obj (colimitCat _ (ordChainSliceCoherent O)) :=
  colimitPreRegular (ordChainSliceSystem O) (ordChainSliceCoherent O)
    (ordChainHasTerminal O) (ordChainHtpres O) (ordChainHasProducts O)
    (ordChainHppres O) (ordChainHppresPair O)
    (ordChainHasEqualizers O) (ordChainHepres O) (ordChainHepresLift O)
    hcanon

/-! ### `HasImages` of the inner slice colimit (the regular upgrade of `ordChainSlicePreRegular`)

  When `𝒞` is REGULAR (`inflRegular` ⟹ `RegularCategory (Infl 𝒞)`), every inner stage
  `Over (chain i : Infl 𝒞)` has images (`overHasImages`), the inner transitions preserve monos
  (`ordChainHmono`) and covers (`ordChainHcovpres`) hence images (`transitions_preserve_images`),
  and the transitions are faithful (`ordChainHfaith`, given the WS suffix).  So the colimit
  `(ordChainSliceSystem O).Obj` has images by `Colim.colimitHasImages`.  This is the per-rung
  HasImages the §1.543 successor (`nextStepOfEnum`) carries to make each tower stage regular. -/

/-- Per-inner-stage images: each stage `Over (chain i : Infl 𝒞)` is a slice of the regular
    inflation `Infl 𝒞` (`inflRegular`), hence has images (`overHasImages`). -/
noncomputable def ordChainStageHasImages [RegularCategory 𝒞] (i : ι) :
    @HasImages ((ordChainSliceSystem O).A i) ((ordChainSliceSystem O).catA i) :=
  overHasImages (𝒞 := Infl 𝒞) ((O.chain i : Infl 𝒞))

/-- The inner transitions preserve monos as a `PreservesMono` (packaging `ordChainHmono`). -/
theorem ordChainPreservesMono {i j : ι} (hij : D.le i j) :
    PreservesMono ((ordChainSliceSystem O).functF hij) :=
  fun {_ _ _} hφ => ordChainHmono O hij _ hφ

open Freyd.Colim in
/-- **GENERIC** `HasImages` of the inner slice colimit over ANY directed index, `𝒞` regular.
    Given the WS-suffix faithfulness precondition (`hwsuf`) and the colimit pullbacks (`hpull`),
    every colimit morphism has an image (`Colim.colimitHasImages`): per-stage images
    (`ordChainStageHasImages`), mono-preserving transitions (`ordChainPreservesMono`), and
    image-preserving transitions (`Colim.transitions_preserve_images` from mono+cover preservation). -/
noncomputable def ordChainSliceHasImages [RegularCategory 𝒞]
    (hwsuf : ∀ {i j : ι} (_hij : D.le i j),
        WellSupported (listProd (𝒞 := 𝒞) (prefixSuffix (O.chain i) (O.chain j))))
    [hpull : @HasPullbacks (ordChainSliceSystem O).Obj (colimitCat _ (ordChainSliceCoherent O))] :
    @HasImages (ordChainSliceSystem O).Obj (colimitCat _ (ordChainSliceCoherent O)) :=
  Colim.colimitHasImages (ordChainSliceSystem O) (ordChainSliceCoherent O)
    (fun i => ordChainStageHasImages O i)
    (fun {_i _j} hij {_x _y} p q h => ordChainHfaith O hij (hwsuf hij) p q h)
    (fun {_i _j} hij => ordChainPreservesMono O hij)
    (fun {i j} hij {_A _B} f =>
      letI : @HasImages ((ordChainSliceSystem O).A i) ((ordChainSliceSystem O).catA i) :=
        ordChainStageHasImages O i
      letI : @HasPullbacks ((ordChainSliceSystem O).A j) ((ordChainSliceSystem O).catA j) :=
        overHasPullbacks (𝒞 := Infl 𝒞) ((O.chain j : Infl 𝒞))
      Colim.transitions_preserve_images ((ordChainSliceSystem O).functF hij)
        (ordChainPreservesMono O hij)
        (fun {_ _} φ hφ => ordChainHcovpres O hij φ hφ) f)

end InnerPackage

/-! ### ℕ-chain specializations of the generic `ordChain*` preservation package

  Each `chain*` name is the `uliftNatDirected` instance (`P.toOrdChain`) of its `ordChain*` generic — the
  SAME proofs serve both ℕ and the transfinite index (DRY).  `Capitalization.lean`'s `hwall_step`
  commentary consumes these ℕ-named facts verbatim. -/

section InnerPackageNat
variable [PreRegularCategory 𝒞] [HasEqualizers 𝒞] (P : PrefixChain 𝒞)

/-- The inner system's per-stage terminal (ℕ specialization of `ordChainHasTerminal`). -/
def chainHasTerminal (i : ULift.{u} Nat) : HasTerminal ((chainSliceSystem P).A i) :=
  ordChainHasTerminal P.toOrdChain i

/-- Terminal preservation (`htpres`) for the ℕ-chain (specialization of `ordChainHtpres`). -/
theorem chainHtpres {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j) :
    (chainSliceSystem P).F hij (chainHasTerminal P i).one = (chainHasTerminal P j).one :=
  ordChainHtpres P.toOrdChain hij

/-- Per-stage binary products (ℕ specialization). -/
def chainHasProducts (i : ULift.{u} Nat) : HasBinaryProducts ((chainSliceSystem P).A i) :=
  ordChainHasProducts P.toOrdChain i

/-- Per-stage equalizers (ℕ specialization). -/
def chainHasEqualizers (i : ULift.{u} Nat) : HasEqualizers ((chainSliceSystem P).A i) :=
  ordChainHasEqualizers P.toOrdChain i

/-- Product joint-monicity preservation (`hppres`) for the ℕ-chain. -/
theorem chainHppres {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    (a b : (chainSliceSystem P).A i) (z : (chainSliceSystem P).A j)
    (u v : z ⟶ (chainSliceSystem P).F hij ((chainHasProducts P i).prod a b))
    (hf : u ≫ ((chainSliceSystem P).functF hij).map (chainHasProducts P i).fst
        = v ≫ ((chainSliceSystem P).functF hij).map (chainHasProducts P i).fst)
    (hs : u ≫ ((chainSliceSystem P).functF hij).map (chainHasProducts P i).snd
        = v ≫ ((chainSliceSystem P).functF hij).map (chainHasProducts P i).snd) : u = v :=
  ordChainHppres P.toOrdChain hij a b z u v hf hs

/-- Product pairing preservation (`hppres_pair`) for the ℕ-chain. -/
theorem chainHppresPair {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    (a b : (chainSliceSystem P).A i) (z : (chainSliceSystem P).A j)
    (p : z ⟶ (chainSliceSystem P).F hij a) (q : z ⟶ (chainSliceSystem P).F hij b) :
    ∃ r : z ⟶ (chainSliceSystem P).F hij ((chainHasProducts P i).prod a b),
      r ≫ ((chainSliceSystem P).functF hij).map (chainHasProducts P i).fst = p ∧
      r ≫ ((chainSliceSystem P).functF hij).map (chainHasProducts P i).snd = q :=
  ordChainHppresPair P.toOrdChain hij a b z p q

/-- Equalizer-mono preservation (`hepres`) for the ℕ-chain. -/
theorem chainHepres {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {A B : (chainSliceSystem P).A i} (f g : A ⟶ B) (z : (chainSliceSystem P).A j)
    (u v : z ⟶ (chainSliceSystem P).F hij
      (@eqObj _ ((chainSliceSystem P).catA i) (chainHasEqualizers P i) _ _ f g))
    (h : u ≫ ((chainSliceSystem P).functF hij).map
          (@eqMap _ ((chainSliceSystem P).catA i) (chainHasEqualizers P i) _ _ f g)
        = v ≫ ((chainSliceSystem P).functF hij).map
          (@eqMap _ ((chainSliceSystem P).catA i) (chainHasEqualizers P i) _ _ f g)) : u = v :=
  ordChainHepres P.toOrdChain hij (f := f) (g := g) z u v h

/-- Transition FAITHFULNESS (`hfaith`) for the ℕ-chain — the `uliftNatDirected` specialization of
    `ordChainHfaith`, GIVEN the appended suffix product `∏(prefixSuffix (chain i) (chain j))` is
    well-supported (§1.546 precondition; for the relative-capitalization chain the appended objects
    ARE the well-supported `B`'s, so this discharges). -/
theorem chainHfaith {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    (hws : WellSupported
      (listProd (𝒞 := 𝒞) (prefixSuffix (P.toOrdChain.chain i) (P.toOrdChain.chain j))))
    {x y : (chainSliceSystem P).A i} (p q : x ⟶ y)
    (h : ((chainSliceSystem P).functF hij).map p = ((chainSliceSystem P).functF hij).map q) : p = q :=
  ordChainHfaith P.toOrdChain hij hws p q h

/-- Transition CONSERVATIVITY (`hcons`) for the ℕ-chain — the specialization of `ordChainHcons`,
    GIVEN the appended suffix product is well-supported. -/
theorem chainHcons {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    (hws : WellSupported
      (listProd (𝒞 := 𝒞) (prefixSuffix (P.toOrdChain.chain i) (P.toOrdChain.chain j))))
    {x y : (chainSliceSystem P).A i} (φ : x ⟶ y)
    (hiso : IsIso (((chainSliceSystem P).functF hij).map φ)) : IsIso φ :=
  ordChainHcons P.toOrdChain hij hws φ hiso

/-- Equalizer-lift preservation (`hepres_lift`) for the ℕ-chain. -/
theorem chainHepresLift {i j : ULift.{u} Nat} (hij : uliftNatDirected.le i j)
    {A B : (chainSliceSystem P).A i} (f g : A ⟶ B) (z : (chainSliceSystem P).A j)
    (k : z ⟶ (chainSliceSystem P).F hij A)
    (hk : k ≫ ((chainSliceSystem P).functF hij).map f
        = k ≫ ((chainSliceSystem P).functF hij).map g) :
    ∃ r : z ⟶ (chainSliceSystem P).F hij
        (@eqObj _ ((chainSliceSystem P).catA i) (chainHasEqualizers P i) _ _ f g),
      r ≫ ((chainSliceSystem P).functF hij).map
        (@eqMap _ ((chainSliceSystem P).catA i) (chainHasEqualizers P i) _ _ f g) = k :=
  ordChainHepresLift P.toOrdChain hij f g z k hk

open Freyd.Colim in
/-- **§1.547 (B-package) — the inner ℕ-chain-slice colimit is PRE-REGULAR** (the `uliftNatDirected`
    specialization of the generic `ordChainSlicePreRegular`).  The relative-capitalization successor
    `S → S*` (§1.543) at the level of pre-regular structure. -/
noncomputable def chainSlicePreRegular
    (hcanon : letI : Cat (chainSliceSystem P).Obj := colimitCat _ (chainSliceCoherent P)
        letI : HasPullbacks (chainSliceSystem P).Obj :=
          colimitHasPullbacks _ (chainSliceCoherent P)
            (chainHasTerminal P) (chainHtpres P) (chainHasProducts P)
            (chainHppres P) (chainHppresPair P)
            (chainHasEqualizers P) (chainHepres P) (chainHepresLift P)
      ∀ {X Y Z : (chainSliceSystem P).Obj} (f : X ⟶ Z) (g : Y ⟶ Z),
          Cover f → Cover (HasPullbacks.has f g).cone.π₂) :
    @PreRegularCategory (chainSliceSystem P).Obj (colimitCat _ (chainSliceCoherent P)) :=
  colimitPreRegular (chainSliceSystem P) (chainSliceCoherent P)
    (chainHasTerminal P) (chainHtpres P) (chainHasProducts P)
    (chainHppres P) (chainHppresPair P)
    (chainHasEqualizers P) (chainHepres P) (chainHepresLift P)
    hcanon

open Freyd.Colim in
/-- **§1.547 (B-package, REGULAR) — the inner ℕ-chain-slice colimit HAS IMAGES** (the
    `uliftNatDirected` specialization of `ordChainSliceHasImages`), `𝒞` regular.  Given the colimit
    pullbacks (`hpull`) and the WS-suffix faithfulness precondition (`hwsuf`).  This is the per-rung
    `HasImages` upgrade of `chainSlicePreRegular`, the regular half of the §1.543 successor. -/
noncomputable def chainSliceHasImages [RegularCategory 𝒞]
    (hwsuf : ∀ {i j : ULift.{u} Nat} (_hij : uliftNatDirected.le i j),
        WellSupported (listProd (𝒞 := 𝒞)
          (prefixSuffix (P.toOrdChain.chain i) (P.toOrdChain.chain j))))
    [hpull : @HasPullbacks (chainSliceSystem P).Obj (colimitCat _ (chainSliceCoherent P))] :
    @HasImages (chainSliceSystem P).Obj (colimitCat _ (chainSliceCoherent P)) :=
  letI : @HasPullbacks (ordChainSliceSystem P.toOrdChain).Obj
      (colimitCat _ (ordChainSliceCoherent P.toOrdChain)) := hpull
  ordChainSliceHasImages P.toOrdChain (fun {_i _j} hij => hwsuf hij)

end InnerPackageNat

end Freyd
