/-
  §1.438  General functor-reflection theorems.

  This file collects the general versions of §1.438's reflection results
  and makes existing special cases thin corollaries.

  Contents (proved here):
  - `faithful_reflectsMono` : Embedding F → Monic (F m) → Monic m     [§1.438]
  - `embedding_reflectsMono` : same, restated as `ReflectsMono F`

  Already in S1_43 (re-exported as aliases here for convenience):
  - `reflects_equalizers_reflects_isos` : ReflectsEqualizers F → reflects isos [§1.438]
  - `iso_reflecting_eq_preserving_faithful` : iso-reflecting + pres-eq → Embedding [§1.438]

  Not refactored (deliberately): `homInclObj_mono_reflects` (ColimitInvImageUnion) could be
  forwarded to `faithful_reflectsMono`, but its faithfulness hypothesis is a bespoke predicate
  on transition maps (not `Embedding` of one functor), so the adaptor is not worth the risk to
  that large file. `ReflectingAdditiveFunctor.reflects_iso` (ExactRepresentation) is a hypothesis
  field, not a theorem, so it cannot be derived. Both left as-is.
-/

module

public import Freyd.S1_18
public import Freyd.S1_31
public import Freyd.S1_41
public import Freyd.S1_43

open Freyd

universe v u u₁ u₂

namespace Freyd

/-! ## §1.438 Faithful functor reflects monics -/

section FaithfulReflects

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]
variable {F : Functor 𝒞 𝒟}

/-- **§1.438**: A faithful functor (`Embedding`) reflects monics.

  If `F.map m` is monic in `𝒟` and `F` is injective on homs (`Embedding`), then `m` is
  monic in `𝒞`.

  PROOF: given `g ≫ m = h ≫ m`, functoriality gives `F(g) ≫ F(m) = F(h) ≫ F(m)`,
  the monic `F(m)` cancels to `F(g) = F(h)`, and `Embedding` gives `g = h`. -/
theorem faithful_reflectsMono (hemb : Embedding F) {X Y : 𝒞} {m : X ⟶ Y}
    (hm : Monic (F.map m)) : Monic m := by
  intro W g h hgh
  apply hemb
  apply hm
  calc F.map g ≫ F.map m = F.map (g ≫ m) := (F.map_comp g m).symm
    _ = F.map (h ≫ m)     := by rw [hgh]
    _ = F.map h ≫ F.map m := F.map_comp h m

/-- `faithful_reflectsMono` rephrased as `ReflectsMono F`. -/
theorem embedding_reflectsMono (hemb : Embedding F) : ReflectsMono F :=
  fun hm => faithful_reflectsMono hemb hm

/-! ## §1.438 — re-exported from S1_43 for discoverability

  The two core §1.438 theorems are already proved in S1_43; import this file to get them:
  - `reflects_equalizers_reflects_isos` : `ReflectsEqualizers F → IsIso (F f) → IsIso f`
  - `iso_reflecting_eq_preserving_faithful` : iso-reflecting + pres-equalizers → `Embedding F`
-/

end FaithfulReflects

end Freyd
