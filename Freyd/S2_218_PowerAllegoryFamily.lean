/-
  §2.218 / §1.635 — assembling a FAMILY of allegory representations into the allegory POWER.

  Freyd's §1.635 represents a (capital positive pre-logos / its allegory) in a POWER of the allegory
  of sets, `Rel(Set)^I`, by the FAMILY of stalk functors `{Rel(T_F̂)}` over all ultra-filters `F̂`.
  The representation is FAITHFUL not because any single stalk reflects isos, but because the family is
  COLLECTIVELY faithful (some `F̂` separates any two distinct relations — Freyd's ultra-filter
  construction, `exists_ultrafilter_excluding`).

  This file provides the abstract glue: a family `I → AllegoryFunctor 𝒜 ℬ` assembles, pointwise, into
  one `AllegoryFunctor 𝒜 (PowerObj I ℬ)` (`familyAllegoryHom`), which is FAITHFUL exactly when the
  family is jointly faithful (`familyAllegoryHom_faithful`).  The stalk-family instance then needs only
  the joint faithfulness, which is the §1.635 collective-faithfulness statement — NOT single-stalk
  iso-reflection. -/
module

public import Freyd.S2_111_RelCat

namespace Freyd.Alg

open Freyd.PowerAllegory

universe u₁ u₂ v₁ v₂ w

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ] {I : Type w}

/-- **Assemble a family of allegory functors `𝒜 → ℬ` into one `𝒜 → ℬ^I`** (the allegory power
    `PowerObj I ℬ`), all operations pointwise. -/
def familyAllegoryHom (F : I → AllegoryFunctor 𝒜 ℬ) :
    AllegoryFunctor 𝒜 (PowerObj I ℬ) where
  obj a := fun i => (F i).obj a
  map {_ _} R := fun i => (F i).map R
  map_id a := funext fun i => (F i).map_id a
  map_comp R S := funext fun i => (F i).map_comp R S
  map_recip R := funext fun i => (F i).map_recip R
  map_inter R S := funext fun i => (F i).map_inter R S

/-- **The family map is faithful ⟺ the family is JOINTLY faithful.**  This is the abstract carrier
    of Freyd's §1.635 collective faithfulness: a power representation separates `R ≠ S` as soon as
    SOME coordinate `i` does — no single coordinate need reflect isos. -/
theorem familyAllegoryHom_faithful (F : I → AllegoryFunctor 𝒜 ℬ)
    (hjoint : ∀ {a b : 𝒜} (R S : a ⟶ b), (∀ i, (F i).map R = (F i).map S) → R = S) :
    (familyAllegoryHom F).Faithful :=
  fun {_ _} R S h => hjoint R S (fun i => congrFun h i)

end Freyd.Alg
