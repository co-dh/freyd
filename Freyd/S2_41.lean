/-
  Freyd & Scedrov, *Categories and Allegories* §2.414  (forward direction).

  §2.414  "If A is an object in a topos C, let ∋ ⊆ [A]×A be its universal relation.
           The uniqueness condition in the definition of universal relations forces ∋
           to be straight [1.9].  Using the last section [§2.413] we may infer the
           thickness condition."

  We build `relPowerAllegory : PowerAllegory (RelObj 𝒞)` for a logos `𝒞` whose objects
  have power objects (the two ingredients a topos supplies: a logos is a division
  allegory `relDivisionAllegory` (§1.784/§2.32), and each `[C]` carries the universal
  relation `∈_C` (§1.9)).  The membership relation `∈_C : [C] → C`, read as a `Rel(C)`
  morphism, is the epsilon `∋_C`.

  * `eps ⟨b⟩ = [∈_b]`           — the universal relation as a `Rel(C)` morphism.
  * `eps_thick`                 — Freyd's §2.413 thickness: the transpose `Λ(R)` (a map)
                                  satisfies `Λ(R) ≫ ∋ = R` (discharged for EVERY `R`,
                                  the box guard ignored, strictly stronger than the field
                                  asks — exactly the §2.434 `globalScPrePower` pattern).
  * `eps_straight`              — Freyd's "uniqueness forces ∋ straight": from the
                                  uniqueness of classifying maps (`univHomExt923`) every
                                  symmetric congruence `T ⊚ ∈ = ∈` is the diagonal.

  Hypotheses are `[Logos 𝒞] [∀ C : 𝒞, HasPowerObject C]` rather than `[Topos 𝒞]`: this is
  the minimal honest combination (division allegory + power objects), and it shares the
  SINGLE ambient `HasPullbacks` of the logos, sidestepping the `Topos`/`Logos`
  HasPullbacks instance diamond — exactly as `Baseable923` deliberately does.
-/

import Freyd.S2_111_RelCat
import Freyd.S2_40
import Freyd.S1_923_Baseable

universe v u

namespace Freyd

open Freyd.Alg

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Logos 𝒞] [HasEqualizers 𝒞] [∀ C : 𝒞, HasPowerObject C]

/-! ## §2.414  The relational pullback is a `Rel(C)` composite

  Freyd writes `fU` for "the pullback of `U` along `f`" (§1.9).  In `Rel(C)` that is the
  composite `[graph f] ⊚ U`.  This bridge identifies the two, letting the §1.9 universal
  property (stated with `relPullback`) drive the allegory-level `∋` laws. -/

/-- **§2.414 bridge**: `relPullback f U ≅ graph f ⊚ U` (mutual `RelLe`).  Chain
    `relPullback f U ≅ relPullback f (graph 1 ⊚ U) ≅ (relPullback f (graph 1)) ⊚ U
    ≅ graph f ⊚ U`, using `relPullback_compose_dist` (distribution over `⊚`) and
    `relPullback_graph_id` (`graph f ≅ relPullback f (graph 1)`). -/
theorem relPullback_graphComp {A P C : 𝒞} (f : A ⟶ P) (U : BinRel 𝒞 P C) :
    RelLe (relPullback f U) (graph f ⊚ U) ∧ RelLe (graph f ⊚ U) (relPullback f U) := by
  obtain ⟨hgid_fwd⟩ : RelLe (graph (Cat.id P) ⊚ U) U := graph_id_comp U
  obtain ⟨hgid_bwd⟩ : RelLe U (graph (Cat.id P) ⊚ U) := comp_graph_id_left U
  obtain ⟨hdist1, hdist2⟩ := relPullback_compose_dist f (graph (Cat.id P)) U
  obtain ⟨hgrf_fwd, hgrf_bwd⟩ := relPullback_graph_id f
  refine ⟨?_, ?_⟩
  · -- relPullback f U ⊑ graph f ⊚ U
    have h1 : RelHom (relPullback f U) (relPullback f (graph (Cat.id P) ⊚ U)) :=
      relHom_pullback923 f hgid_bwd
    have h2 : RelHom (relPullback f U) ((relPullback f (graph (Cat.id P))) ⊚ U) :=
      relHom_trans923 h1 hdist1
    have h3 : RelLe ((relPullback f (graph (Cat.id P))) ⊚ U) (graph f ⊚ U) :=
      compose_le_left ⟨hgrf_bwd⟩ U
    exact rel_le_trans ⟨h2⟩ h3
  · -- graph f ⊚ U ⊑ relPullback f U
    have h1 : RelLe (graph f ⊚ U) ((relPullback f (graph (Cat.id P))) ⊚ U) :=
      compose_le_left ⟨hgrf_fwd⟩ U
    have h2 : RelHom (relPullback f (graph (Cat.id P) ⊚ U)) (relPullback f U) :=
      relHom_pullback923 f hgid_fwd
    exact rel_le_trans h1 (rel_le_trans ⟨hdist2⟩ ⟨h2⟩)

/-! ## §2.413 / §2.414  Thickness of `∋`

  Freyd: "Using the last section [§2.413] we may infer the thickness condition."  For
  every relation `R₀ : c → b`, the transpose `Λ(R₀) : c → [b]` (the §1.9 classifying map)
  is a `C`-map whose graph is a `Rel(C)`-map with `[graph Λ(R₀)] ≫ [∈_b] = [R₀]`.  This is
  the §2.413 EXISTENTIAL thickness for the unrestricted `R₀` (box guard ignored, hence
  strictly stronger than the `eps_thick` field needs — the §2.434 `globalScPrePower`
  pattern). -/

/-- The §1.9 transpose `Λ(R₀) : c → [b]` of a relation `R₀ : c → b`. -/
noncomputable def memTranspose (b : 𝒞) {c : 𝒞} (R₀ : BinRel 𝒞 c b) :
    c ⟶ HasPowerObject.powerObj (C := b) :=
  univClassify923 (HasPowerObject.is_universal (C := b)) R₀

/-- **§2.413 thickness**: `[graph Λ(R₀)]` is a `Rel(C)`-map with `[graph Λ(R₀)] ≫ [∈_b] = [R₀]`. -/
theorem mem_thick (b : 𝒞) {c : 𝒞} (R₀ : BinRel 𝒞 c b) :
    Freyd.Alg.Map (𝒜 := RelObj 𝒞) (a := ⟨c⟩) (b := ⟨HasPowerObject.powerObj (C := b)⟩)
        (relClass (graph (memTranspose b R₀))) ∧
    relClass (graph (memTranspose b R₀) ⊚ HasPowerObject.mem (C := b)) = relClass R₀ := by
  refine ⟨relClass_graph_map (memTranspose b R₀), ?_⟩
  -- reduce to `graph Λ ⊚ ∈ ≈ R₀`.
  obtain ⟨hbr1, hbr2⟩ := relPullback_graphComp (memTranspose b R₀) (HasPowerObject.mem (C := b))
  obtain ⟨hiso1, hiso2⟩ :=
    univClassifyIso923 (HasPowerObject.is_universal (C := b)) R₀
  exact Quotient.sound
    ⟨rel_le_trans hbr2 ⟨hiso2⟩, rel_le_trans ⟨hiso1⟩ hbr1⟩

/-! ## §2.414  Straightness of `∋`

  Freyd: "The uniqueness condition in the definition of universal relations forces ∋ to
  be straight."  The BinRel core: any endo-relation `T₀` on a power object `P` that
  satisfies `T₀ ⊚ U ⊑ U` and `T₀° ⊚ U ⊑ U` (a symmetric `U`-congruence) is contained in
  the diagonal — because its two legs `p = T₀.colA`, `q = T₀.colB` then classify the same
  relation (`relPullback p U ≅ relPullback q U`), so `p = q` by uniqueness, and
  `T₀ ⊑ (graph p)° ⊚ graph p ⊑ 1`. -/

/-- **§2.414 core**: a symmetric `U`-congruence on `P` is contained in the diagonal, for a
    universal `U : BinRel P C`.  This is Freyd's "uniqueness forces straight," at the
    `BinRel`/relation-iso level. -/
theorem straight_of_universal {P C : 𝒞} (U : BinRel 𝒞 P C) (hU : IsUniversalRel U)
    (T₀ : BinRel 𝒞 P P)
    (h1 : RelLe (T₀ ⊚ U) U) (h2 : RelLe (T₀° ⊚ U) U) :
    RelLe T₀ (graph (Cat.id P)) := by
  -- adjunction: `((graph x)° ⊚ graph y) ⊚ U ⊑ U` forces `graph y ⊚ U ⊑ graph x ⊚ U`.
  have adj : ∀ {S : 𝒞} (x y : S ⟶ P),
      RelLe (((graph x)° ⊚ graph y) ⊚ U) U → RelLe (graph y ⊚ U) (graph x ⊚ U) := by
    intro S x y hxy
    have a3 : RelLe ((graph x)° ⊚ (graph y ⊚ U)) U :=
      rel_le_trans (compose_assoc' (graph x)° (graph y) U) hxy
    calc graph y ⊚ U
        ⊂ graph (Cat.id S) ⊚ (graph y ⊚ U) := comp_graph_id_left _
      _ ⊂ (graph x ⊚ (graph x)°) ⊚ (graph y ⊚ U) := compose_le_left (graph_is_map x).1 _
      _ ⊂ graph x ⊚ ((graph x)° ⊚ (graph y ⊚ U)) := compose_assoc (graph x) (graph x)° (graph y ⊚ U)
      _ ⊂ graph x ⊚ U := compose_le (rel_le_refl (graph x)) a3
  -- `graph q ⊚ U ⊑ graph p ⊚ U` from `h1` (reconstitute `T₀`).
  have step1 : RelLe (graph T₀.colB ⊚ U) (graph T₀.colA ⊚ U) :=
    adj T₀.colA T₀.colB (rel_le_trans (compose_le_left (reconstitute_le T₀) U) h1)
  -- `graph p ⊚ U ⊑ graph q ⊚ U` from `h2` (reconstitute `T₀°`, legs swapped).
  have step2 : RelLe (graph T₀.colA ⊚ U) (graph T₀.colB ⊚ U) :=
    adj T₀.colB T₀.colA (rel_le_trans (compose_le_left (reconstitute_le T₀°) U) h2)
  -- bridge to relation pullbacks and force `colA = colB` by uniqueness.
  obtain ⟨bp1, bp2⟩ := relPullback_graphComp T₀.colA U
  obtain ⟨bq1, bq2⟩ := relPullback_graphComp T₀.colB U
  obtain ⟨hf⟩ : RelLe (relPullback T₀.colA U) (relPullback T₀.colB U) :=
    rel_le_trans bp1 (rel_le_trans step2 bq2)
  obtain ⟨hb⟩ : RelLe (relPullback T₀.colB U) (relPullback T₀.colA U) :=
    rel_le_trans bq1 (rel_le_trans step1 bp2)
  have hpq : T₀.colA = T₀.colB := univHomExt923 hU T₀.colA T₀.colB ⟨hf, hb⟩
  -- `T₀ ⊑ (graph colA)° ⊚ graph colB = (graph colB)° ⊚ graph colB ⊑ 1`.
  have hrec : RelLe T₀ ((graph T₀.colA)° ⊚ graph T₀.colB) := le_reconstitute T₀
  rw [hpq] at hrec
  exact rel_le_trans hrec (graph_is_map T₀.colB).2

/-- **§2.414 (straightness of `∋`)**: the universal relation `[∈_b]` is straight in `Rel(C)`.
    `∈/ₛ∈ ⊑ 1` because every symmetric `∈`-congruence is the diagonal (`straight_of_universal`),
    Freyd's "uniqueness forces ∋ straight." -/
theorem mem_straight (b : 𝒞) :
    Straight (𝒜 := RelObj 𝒞) (relClass (HasPowerObject.mem (C := b))) := by
  -- For every `D` with `D ≫ ∈ ⊑ ∈` and `D° ≫ ∈ ⊑ ∈`, `D ⊑ 1`; apply to `D = ∈/ₛ∈`.
  have key : ∀ (D : (⟨HasPowerObject.powerObj (C := b)⟩ : RelObj 𝒞) ⟶
                    ⟨HasPowerObject.powerObj (C := b)⟩),
      D ≫ relClass (HasPowerObject.mem (C := b)) ⊑ relClass (HasPowerObject.mem (C := b)) →
      D° ≫ relClass (HasPowerObject.mem (C := b)) ⊑ relClass (HasPowerObject.mem (C := b)) →
      D ⊑ Cat.id _ := by
    intro D
    refine Quotient.inductionOn D (fun T₀ => ?_)
    intro hD1 hD2
    have h1 : RelLe (T₀ ⊚ HasPowerObject.mem (C := b)) (HasPowerObject.mem (C := b)) :=
      (quotLe_iff_algLe _ _).mpr hD1
    have h2 : RelLe (T₀° ⊚ HasPowerObject.mem (C := b)) (HasPowerObject.mem (C := b)) :=
      (quotLe_iff_algLe _ _).mpr hD2
    exact (quotLe_iff_algLe _ _).mp
      (straight_of_universal (HasPowerObject.mem (C := b)) (HasPowerObject.is_universal (C := b))
        T₀ h1 h2)
  show relClass (HasPowerObject.mem (C := b)) /ₛ relClass (HasPowerObject.mem (C := b))
      ⊑ Cat.id (⟨HasPowerObject.powerObj (C := b)⟩ : RelObj 𝒞)
  apply key
  · exact ((le_symmDiv_iff _ _ _).mp (le_refl _)).1
  · exact ((le_symmDiv_iff _ _ _).mp (le_refl _)).2

/-! ## §2.414  `Rel(C)` is a power allegory

  Assembling `eps`, `eps_straight` (§2.414 straightness), and `eps_thick` (§2.413) on top
  of the §1.784/§2.32 division allegory `relDivisionAllegory`.  Delivered as a `def` (not
  an `instance`) so its `toDivisionAllegory` projection is defeq to the existing
  `relDivisionAllegory` and does not compete with it during instance resolution. -/

/-- **§2.414 (forward)**: if `𝒞` is a logos whose objects have power objects (the two
    properties a topos supplies), then `Rel(C)` is a POWER ALLEGORY.  `∋_b = [∈_b]` is the
    membership relation; straightness is "uniqueness forces ∋ straight" (`mem_straight`),
    thickness is the §2.413 transpose (`mem_thick`). -/
noncomputable def relPowerAllegory : PowerAllegory (RelObj 𝒞) :=
  { relDivisionAllegory with
    powerObj := fun b => ⟨HasPowerObject.powerObj (C := b.carrier)⟩
    eps := fun b => relClass (HasPowerObject.mem (C := b.carrier))
    eps_straight := fun b => mem_straight b.carrier
    eps_thick := fun {b c} R _hbox => by
      refine Quotient.inductionOn R (fun R₀ => ?_)
      refine ⟨relClass (graph (memTranspose b.carrier R₀)), (mem_thick b.carrier R₀).1, ?_⟩
      show relClass (graph (memTranspose b.carrier R₀) ⊚ HasPowerObject.mem (C := b.carrier))
          = relClass R₀
      exact (mem_thick b.carrier R₀).2 }

/-- **§2.414 forward (full)**: `Rel(C)` of a topos is an UNGUARDED power allegory — its
    membership `∋` classifies EVERY relation (the §2.413 transpose `mem_thick` is unguarded,
    discharged for all `R`).  This is the genuine power allegory Freyd's converse-side theorems
    use, and the witness for `UnguardedPowerAllegory`'s non-vacuity. -/
noncomputable def relUnguardedPowerAllegory : UnguardedPowerAllegory (RelObj 𝒞) :=
  { relPowerAllegory with
    eps_thick_all := fun {b c} R => by
      refine Quotient.inductionOn R (fun R₀ => ?_)
      refine ⟨relClass (graph (memTranspose b.carrier R₀)), (mem_thick b.carrier R₀).1, ?_⟩
      show relClass (graph (memTranspose b.carrier R₀) ⊚ HasPowerObject.mem (C := b.carrier))
          = relClass R₀
      exact (mem_thick b.carrier R₀).2 }

end Freyd
