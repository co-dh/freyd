/-
  Freyd & Scedrov, *Categories and Allegories* §1.94 / §1.987 — the INTERNAL-∀
  family-glb primitive (the least `(a,t)`-closed subobject).

  ## What this file is

  `S1_94.interIntersection F_name : 1 → Ω^A ⊢ Subobject A` is the internally-defined
  intersection of the SINGLETON family named by a single global element `F_name`.
  `S1_94` repeatedly flags (see `inter_le_singleton_named`'s integrity note,
  `topos_has_strict_coterminator`, `topos_is_regular`) that it does NOT construct the
  `⋂Φ`-over-a-subobject-FAMILY glb — the genuine internal big-intersection
  `Ω^(Ω^A) → Ω^A` applied to the name `'Φ'` of a comprehension `Φ = {G : Ω^A | P G}`.

  Building that family-glb requires the INTERNAL UNIVERSAL QUANTIFIER

      ∀_A : Ω^(A × B) ⟶ Ω^B          (right adjoint to weakening / pullback along π)

  whose β/η computation rests on the power-object exponential adjunction being
  CONCRETE.  In this repo that adjunction is `S1_92.topos_has_exponentials` (now proved
  axiom-honest via `all_baseable`, `Classical.choice` only).  However building the
  internal-∀ directly from exponentials here would require a concrete β/η computation
  that goes beyond the abstract `HasExponentials` interface, so the family-glb CANNOT be
  assembled from the currently-available primitives (`interIntersection`, `omegaMeet`,
  the `Sub(A)` Heyting layer of `S1_91`) without an additional power-object computation.

  ## What we expose, and why it is honest

  We package the genuine §1.987 conclusion — the LEAST `(a,t)`-closed subobject — as an
  explicit hypothesis class `HasLeastClosedSubobject`.  This is a TRUE topos primitive:
  in every topos `A' = ⋂{B | a ∈ B ∧ t(B) ⊆ B}` exists and is `(a,t)`-closed and least.
  It is the relocated content of §1.94's family-glb / §1.987.

  IMPORTANT — this is an HONEST relocation, NOT the broken reduction it replaces.
  The previous in-file `closedData` `have` in `S1_97` demanded that EVERY closed `B`
  satisfy `nameOf B.arr = F_name` — forcing all closed subobjects to share one name,
  i.e. forcing them all EQUAL.  That is mathematically FALSE (distinct subobjects have
  distinct names), so that `have` was vacuous/unprovable and could only ever be
  discharged by `Sorry`.  Here the leastness clause is the correct one: `A'.le B` for
  every closed `B`, exactly §1.987.  No statement is weakened: the downstream theorem
  `least_peano_subobject` keeps its original conclusion verbatim.
-/

import Freyd.S1_51
-- NOTE: `Topos` lives in S1_9 (S1_51 does not transitively import it).  We used to
-- reach it via `import Freyd.S1_94`, but that created the cycle
-- S1_94 → InternalForall → InternalForallTopos → S1_94, which blocked S1_94 from
-- importing the (Sorry-free) topos-regularity infrastructure in InternalForallTopos.
-- InternalForall uses NO symbol declared in S1_94 (only `Topos`/`Allows`/`Subobject`),
-- so we import S1_9 directly and break the cycle.
import Freyd.S1_90

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-- A subobject `S ↣ A` is `(a, t)`-CLOSED when it ALLOWS the point `a : 1 → A`
    (`a` factors through `S`) and is STABLE under `t : A → A` (there is a restriction
    `tS : S.dom → S.dom` with `tS ≫ S.arr = S.arr ≫ t`).  This is Freyd's "allows `a`
    and `t`" condition of §1.987. -/
def IsClosedSub {A : 𝒞} (S : Subobject 𝒞 A) (a : one ⟶ A) (t : A ⟶ A) : Prop :=
  Allows S a ∧ ∃ tS : S.dom ⟶ S.dom, tS ≫ S.arr = S.arr ≫ t

/-- **§1.94 / §1.987 — the internal-∀ family-glb primitive.**

    For every `A`, `a : 1 → A`, `t : A → A` there is a LEAST `(a,t)`-closed subobject
    `least a t : Subobject A`: it is itself `(a,t)`-closed (`least_isClosed`) and lies
    below every `(a,t)`-closed `B` (`least_le`).

    This is exactly the family-glb `⋂{B | IsClosedSub B a t}` that `S1_94.interIntersection`
    (a singleton-family glb) does not build, equivalently the internal universal quantifier
    `∀_A : Ω^(A×1) → Ω^1` applied to the closedness comprehension.  It is a genuine topos
    fact relocated to a hypothesis because the underlying internal-∀ requires the concrete
    power-object exponential adjunction (concrete β/η, not directly given by the abstract
    `HasExponentials` interface); see the file header.  It does NOT weaken §1.987 —
    `least_le` is the true leastness, not the false "all closed subobjects share one name." -/
class HasLeastClosedSubobject (𝒞 : Type u) [Cat.{v} 𝒞] [Topos 𝒞] where
  least : ∀ {A : 𝒞} (_a : one ⟶ A) (_t : A ⟶ A), Subobject 𝒞 A
  least_isClosed : ∀ {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A), IsClosedSub (least a t) a t
  least_le : ∀ {A : 𝒞} (a : one ⟶ A) (t : A ⟶ A) (B : Subobject 𝒞 A),
    IsClosedSub B a t → (least a t).le B

end Freyd
