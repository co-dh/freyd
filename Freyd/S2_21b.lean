import Freyd.S2_218_CapDataPositiveTower
import Freyd.S1_635_StalkRepr
import Freyd.S2_147_MapCat
import Freyd.S2_216_MatrixAllegory
import Freyd.S2_217_PositiveRepr

universe u u₁ u₂ u₃ v

/-
  Freyd & Scedrov, *Categories and Allegories* — §2.218 (the headline representation theorem).

  **Every small TABULAR unitary distributive allegory `𝒜` is faithfully representable in a power of
  the allegory of sets.**

  This is the FINAL assembly of the formalization.  The route (all bricks built elsewhere):

    1. `Map 𝒜` is a small POSITIVE pre-logos (`mapDisjointBinaryCoproduct`), regular by
       `mapRegularCategory`.
    2. CAPITALIZE: `capitalization_lemma_regular_positive_strong` (`CapDataPositiveTower`) gives a
       CAPITAL positive pre-logos `Ā` with a faithful embedding `F : Map 𝒜 → Ā` that is ALSO a
       `RegularFunctor` and REFLECTS ALL ISOS.
    3. STALK FAMILY: `Tstar : Ā → (StalkIndex Ā → Type)` is a `RegularFunctor`
       (`Tstar_regularFunctor`, §1.635) that reflects isos (`Tstar_reflects_iso`, the ultra-filter
       family is collectively conservative).
    4. COMPOSE: `G = Tstar ∘ F : Map 𝒜 → Set^I` is a `RegularFunctor` (cross-universe composition,
       `regularFunctor_comp`) reflecting isos.  Power-covers split (`power_cover_splits`), so the
       §2.218 packager `relAllegoryHom_faithful_of_reflects` makes `Rel(G)` FAITHFUL — WITHOUT
       needing covers to split in `Ā` (the §1.543 capital case is bypassed by landing in `Set^I`).
    5. BRIDGE: `bridgeFunctor 𝒜 : 𝒜 → Rel(Map 𝒜)` is faithful (`bridgeFunctor_faithful`, §2.148).
    6. RESULT: `bridge ⋙ Rel(G) : 𝒜 → Rel(Set^I)` is faithful (`AllegoryFunctor.Faithful.comp`),
       i.e. `𝒜` is faithfully represented in `Rel(Set^I)`, the allegory of relations in a power of
       sets, with `I = StalkIndex Ā`.
-/


namespace Freyd

open Cat RelFunctor PreLogosHorn.Stalk

/-! ## Cross-universe `RegularFunctor` composition

  The reusable `preservesBinaryProducts_comp` and `regularFunctor_comp` lemmas are universe
  polymorphic.  Thus the §2.218 composite `Tstar ∘ F : Map 𝒜 → Set^I`, whose target lies one
  object universe higher, uses the same canonical composition theorem as every other regular
  functor composite. -/

/-! ## §2.218 — the faithful representation in a power of the allegory of sets -/

/-- **§2.218 — every small TABULAR unitary POSITIVE allegory is faithfully representable in a
    power of the allegory of sets.**  `I = StalkIndex Ā` indexes the ultra-filters of complemented
    subterminators of the capital positive pre-logos `Ā` produced by capitalizing `Map 𝒜`; the
    representation is `bridge ⋙ Rel(Tstar ∘ F)` (see the module docstring for the six steps).

    Positivity (`TabularUnitaryPositiveAllegory`, which `extends TabularUnitaryDistributiveAllegory`)
    is what makes `Map 𝒜` a positive pre-logos (`mapDisjointBinaryCoproduct`), so the capital target
    `Ā` is positive and Freyd's §1.635 ultra-filter STALK family `Tstar : Ā → Set^I` applies — the
    stalk route needs `[DisjointBinaryCoproduct Ā]`. -/
theorem tabular_repr_in_power_of_sets {𝒜 : Type u}
    [Alg.TabularUnitaryPositiveAllegory.{u, u} 𝒜] :
    ∃ (I : Type u) (rep : Alg.AllegoryFunctor 𝒜 (RelObj (I → Type u))), rep.Faithful := by
  -- (1) `Map 𝒜` is a small positive pre-logos; pin its `Cat`/`RegularCategory` to the `map*` ones.
  letI : Cat.{u} (Alg.MapObj 𝒜) := Alg.mapCat
  letI : RegularCategory (Alg.MapObj 𝒜) := Alg.mapRegularCategory
  -- (2) capitalize: faithful regular iso-reflecting `F : Map 𝒜 → Ā`, `Ā` capital positive.
  obtain ⟨Ā, hCĀ, hDĀ, hcap, F, hfaithF, hRegF, hreflF⟩ :=
    capitalization_lemma_regular_positive_strong (Alg.MapObj 𝒜)
  letI : Cat.{u} Ā := hCĀ
  letI : DisjointBinaryCoproduct Ā := hDĀ
  -- (3) the stalk family of `Ā` (regular, reflects isos via the family's collective conservativity).
  have hRegTstar : RegularFunctor (TstarFunctor (𝒞 := Ā)) := Tstar_regularFunctor hcap
  -- (4) the composite `G = Tstar ∘ F : Map 𝒜 → Set^I` is regular (cross-universe) and reflects isos.
  have hRegG := regularFunctor_comp hRegF hRegTstar
  have hGfaithful : (hRegG.relAllegoryHom).Faithful :=
    hRegG.relAllegoryHom_faithful_of_reflects
      (fun {_ _} f hiso => hreflF f (Tstar_reflects_iso hcap (F.map f) hiso))
      (fun {_ _} e he => power_cover_splits e he)
  -- (5)+(6) bridge through `Rel(Map 𝒜)` and compose with the faithful `Rel(G)`.
  exact ⟨StalkIndex Ā, (bridgeFunctor 𝒜).comp hRegG.relAllegoryHom,
    Alg.AllegoryFunctor.Faithful.comp (bridgeFunctor_faithful 𝒜) hGfaithful⟩

/-! ## §2.216 + §2.217 — removing positivity: the FULLY-GENERAL distributive case

  Freyd §2.216/§2.217: a distributive allegory `𝒜` embeds FULL+FAITHFULLY in its POSITIVE REFLECTION
  `Mat 𝒜` — the finite-sequence / matrix construction (`Freyd/MatrixAllegory.lean`), which is a
  tabular unitary POSITIVE allegory (`instTabularAllegoryMat`/`instUnitaryAllegoryMat`/
  `instPositiveAllegoryMat`, the §2.342/§2.215 matrix instances).  Applying the positive case
  `tabular_repr_in_power_of_sets` to `Mat 𝒜` and composing with the faithful `𝒜 ↪ Mat 𝒜`
  (`embed1`, the `α ↦ ⟨α⟩` 1×1-matrix wrapper) removes the positivity hypothesis — the bare
  *distributive* §2.218. -/

-- `matEmbed` (the FULL+FAITHFUL `𝒜 ↪ Mat 𝒜` allegory functor, `α ↦ ⟨α⟩`) and
-- `matEmbed_faithful` now live in `Freyd/S2_217_PositiveRepr.lean` over a BARE
-- `[DistributiveAllegory 𝒜]` (with fullness `matEmbed_full` and order-reflection
-- `matEmbed_le_iff`); they apply here through the `TabularUnitaryDistributiveAllegory` parent.

open Alg Alg.Mat in
/-- **§2.218 (FULLY GENERAL).**  Every small TABULAR unitary DISTRIBUTIVE allegory `𝒜` is faithfully
    representable in a power of the allegory of sets.  Positivity is removed via the §2.216/§2.217
    positive reflection: `Mat 𝒜` is a tabular unitary POSITIVE allegory (the three matrix instances,
    bundled as in `RelCat.matRelTabularUnitaryPositiveAllegory`; the §2.342 `Tabular`/`Unitary`
    hypothesis classes come from the §2.212 parents), so `tabular_repr_in_power_of_sets` applies to
    `Mat 𝒜`; composing with the faithful `matEmbed : 𝒜 ↪ Mat 𝒜` gives the representation of `𝒜`. -/
theorem tabular_repr_in_power_of_sets_distributive {𝒜 : Type u}
    [Alg.TabularUnitaryDistributiveAllegory.{u, u} 𝒜] :
    ∃ (I : Type u) (rep : Alg.AllegoryFunctor 𝒜 (RelObj (I → Type u))), rep.Faithful := by
  -- `Mat 𝒜` is tabular unitary POSITIVE (`matTabularUnitaryPositive`, S2_217_PositiveRepr).
  letI iTUP : Alg.TabularUnitaryPositiveAllegory (MatObj 𝒜) := matTabularUnitaryPositive 𝒜
  obtain ⟨I, rep, hrep⟩ := tabular_repr_in_power_of_sets (𝒜 := MatObj 𝒜)
  exact ⟨I, (matEmbed 𝒜).comp rep,
    Alg.AllegoryFunctor.Faithful.comp (matEmbed_faithful (𝒜 := 𝒜)) hrep⟩

end Freyd

#print axioms Freyd.tabular_repr_in_power_of_sets
#print axioms Freyd.tabular_repr_in_power_of_sets_distributive
