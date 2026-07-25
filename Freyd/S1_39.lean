/-
  Freyd & Scedrov, *Categories and Allegories* §1.34–§1.39 — remaining TOC entries.
  Adjoint pair, Skeleton/Coskeleton (§1.28/§1.281 — Idempotent/Split idempotent — in S1_28),
  Equivalent categories, Exact sequence, Complete measure, Atomic measure.
-/


import Freyd.S1_01
import Freyd.S1_18
import Freyd.S1_28
import Freyd.S1_31
import Freyd.S1_34
import Freyd.S1_38b
import Freyd.S1_41
import Freyd.S1_43
import Freyd.S1_51
import Freyd.S1_59

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

-- ADJOINT PAIR / LEFT ADJOINT / RIGHT ADJOINT (§1.81, §1.373) are defined canonically
-- in S1_8 (`Adjunction`, `LeftAdjoint`, `RightAdjoint`, with the triangle identities).
-- The earlier ad-hoc versions here were superseded and removed to keep one definition.

/-- EQUIVALENT CATEGORIES (§1.363): two categories are EQUIVALENT if
    there exist isomorphic inflations.  (Existence of an equivalence functor
    implies equivalence.) -/
def EquivalentCategories (𝒜 ℬ : Type u) [Cat.{v} 𝒜] [Cat.{v} ℬ] : Prop :=
  ∃ F : Functor 𝒜 ℬ, EquivalenceFunctor F

/-! ## §1.399 Conjugation invariance of diagrammatic properties

  Book §1.399: Properties on diagrams preserved and reflected by equivalence
  functors are invariant under conjugation (natural isomorphism).
  That is, if F₁ and F₂ : A → B are conjugate (NatIso F₁ F₂), and P is any
  diagrammatic property preserved and reflected by every equivalence functor,
  then F₁ satisfies P iff F₂ does.

  Proof strategy: induction on the Q-sequence telescope.  At each ∀-step we
  convert a witness for F₂ to one for F₁ via the NatIso component θ_{A'};
  naturality makes the triangle equations match.  `satisfies_iff_postcomp_iso`
  (§1.395 Thm 1) handles the initial codomain mismatch `θ_B`. -/

/-- Helper: for `α : NatIso F₁ F₂`, if `h₁ = θ_A ≫ h₂` then `Satisfies (s.map F₁) h₁ ↔
    Satisfies (s.map F₂) h₂`.  Proved by induction on `s`; each quantifier step is handled
    by conjugating the witness with the NatIso component and using naturality. -/
private theorem satisfies_map_natIso
    {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟}
    (α : NatIso F₁ F₂) :
    ∀ {A : 𝒞} (s : QSeq 𝒞 A) {D : 𝒟} (h₁ : F₁.obj A ⟶ D) (h₂ : F₂.obj A ⟶ D),
      h₁ = α.nat.app A ≫ h₂ →
      (Satisfies (s.map F₁) h₁ ↔ Satisfies (s.map F₂) h₂)
  | _, .nil _ q, _, _, _, _ => Iff.rfl
  | _, .cons q α_step rest, D, h₁, h₂, hcompat => by
    obtain ⟨θA_inv, hθA1, hθA2⟩ := α.isIso _
    obtain ⟨θA'_inv, hθA'1, hθA'2⟩ := α.isIso _
    have nat_step := α.nat.naturality α_step
    -- derived: F₂.map α_step ≫ θ_{A'}⁻¹ = θ_A⁻¹ ≫ F₁.map α_step
    have nat_inv : F₂.map α_step ≫ θA'_inv = θA_inv ≫ F₁.map α_step :=
      calc F₂.map α_step ≫ θA'_inv
          = Cat.id _ ≫ F₂.map α_step ≫ θA'_inv           := by rw [Cat.id_comp]
        _ = (θA_inv ≫ α.nat.app _) ≫ F₂.map α_step ≫ θA'_inv := by rw [hθA2]
        _ = θA_inv ≫ (α.nat.app _ ≫ F₂.map α_step) ≫ θA'_inv := by simp [Cat.assoc]
        _ = θA_inv ≫ (F₁.map α_step ≫ α.nat.app _) ≫ θA'_inv := by rw [nat_step]
        _ = θA_inv ≫ F₁.map α_step ≫ (α.nat.app _ ≫ θA'_inv) := by simp [Cat.assoc]
        _ = θA_inv ≫ F₁.map α_step ≫ Cat.id _             := by rw [hθA'1]
        _ = θA_inv ≫ F₁.map α_step                         := by rw [Cat.comp_id]
    simp only [QSeq.map]
    -- θ_{A'} ≫ θ_{A'}⁻¹ = id, so g₁ = θ_{A'} ≫ (θ_{A'}⁻¹ ≫ g₁)
    have θ_cancel : ∀ (g₁ : F₁.obj _ ⟶ D), g₁ = α.nat.app _ ≫ (θA'_inv ≫ g₁) := fun g₁ => by
      rw [← Cat.assoc, hθA'1, Cat.id_comp]
    cases q with
    | all =>
      simp only [satisfies_cons_all]
      exact ⟨
        fun hL g₂ htri₂ => by
          have htri₁ : F₁.map α_step ≫ (α.nat.app _ ≫ g₂) = h₁ := by
            rw [← Cat.assoc, nat_step, Cat.assoc, htri₂, ← hcompat]
          exact (satisfies_map_natIso α rest (α.nat.app _ ≫ g₂) g₂ rfl).mp (hL _ htri₁),
        fun hL g₁ htri₁ => by
          have htri₂ : F₂.map α_step ≫ (θA'_inv ≫ g₁) = h₂ := by
            rw [← Cat.assoc, nat_inv, Cat.assoc, htri₁, hcompat, ← Cat.assoc, hθA2, Cat.id_comp]
          exact (satisfies_map_natIso α rest g₁ (θA'_inv ≫ g₁) (θ_cancel g₁)).mpr
                (hL _ htri₂)⟩
    | ex =>
      simp only [satisfies_cons_ex]
      exact ⟨
        fun ⟨g₁, htri₁, hrest₁⟩ => by
          refine ⟨θA'_inv ≫ g₁, ?_, ?_⟩
          · rw [← Cat.assoc, nat_inv, Cat.assoc, htri₁, hcompat, ← Cat.assoc, hθA2, Cat.id_comp]
          · exact (satisfies_map_natIso α rest g₁ (θA'_inv ≫ g₁) (θ_cancel g₁)).mp hrest₁,
        fun ⟨g₂, htri₂, hrest₂⟩ => by
          refine ⟨α.nat.app _ ≫ g₂, ?_, ?_⟩
          · rw [← Cat.assoc, nat_step, Cat.assoc, htri₂, ← hcompat]
          · exact (satisfies_map_natIso α rest (α.nat.app _ ≫ g₂) g₂ rfl).mpr hrest₂⟩

/-- §1.399 CONJUGATION INVARIANCE (Q-sequence formulation).

    If `α : NatIso F₁ F₂` then for any Q-sequence `s` in the source category 𝒞 and
    any morphism `f : A ⟶ B`, `F₁` satisfies `s` (via `F₁.map f`) iff `F₂` does
    (via `F₂.map f`).

    Proof: `satisfies_iff_postcomp_iso` (§1.395 Thm 1) converts the LHS to the form
    `θ_A ≫ F₂.map f` via naturality; then `satisfies_map_natIso` transfers along the
    telescope by induction. -/
theorem conjugation_invariant_satisfies
    {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟}
    (α : NatIso F₁ F₂) {A B : 𝒞} (s : QSeq 𝒞 A) (f : A ⟶ B) :
    Satisfies (s.map F₁) (F₁.map f) ↔ Satisfies (s.map F₂) (F₂.map f) := by
  rw [satisfies_iff_postcomp_iso (s.map F₁) (F₁.map f) (α.isIso B)]
  rw [α.nat.naturality f]
  exact satisfies_map_natIso α s (α.nat.app A ≫ F₂.map f) (F₂.map f) rfl

/-- SKELETAL category (§1.364): isomorphic objects are equal. -/
def IsSkeletal (𝒞 : Type u) [Cat.{v} 𝒞] : Prop :=
  ∀ (A B : 𝒞), Isomorphic A B → A = B

/-- SKELETON of A: a skeletal category A' with an equivalence A' → A. -/
def Skeleton (𝒜 : Type u) [Cat.{v} 𝒜] : Prop :=
  ∃ (A' : Type u) (_ : Cat.{v} A'), IsSkeletal A' ∧ EquivalentCategories A' 𝒜

/-- COSKELETON of A: a skeletal category A' with an equivalence A → A'. -/
def CoSkeleton (𝒜 : Type u) [Cat.{v} 𝒜] : Prop :=
  ∃ (A' : Type u) (_ : Cat.{v} A'), IsSkeletal A' ∧ EquivalentCategories 𝒜 A'

/-- EXACT AT (§1.599): a composable pair `A —f→ B —g→ C` is EXACT at `B` when the
    image of `f` coincides (is isomorphic, as a subobject of `B`) with the kernel of `g`.
    A full exact sequence is a family of objects/maps that is `ExactAt` at every
    interior node; we give the local condition, which carries all the content. -/
def ExactAt [HasImages 𝒞] [HasEqualizers 𝒞] [HasZeroObject 𝒞]
    {A B C : 𝒞} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  Isomorphic (image f).dom (Kernel g)

-- A subset of `I` is encoded mathlib-free as a predicate `I → Prop`, and a family
-- of subsets as `(I → Prop) → Prop`.

/-- COMPLETE MEASURE (§1.648): an ultrafilter on `I` closed under countable
    intersections — every `ℕ`-indexed family of members has its intersection in `F`. -/
def CompleteMeasure (I : Type u) (F : (I → Prop) → Prop) : Prop :=
  -- ultrafilter:
  (F (fun _ => True)) ∧ ¬ F (fun _ => False) ∧
  (∀ S T, F S → (∀ i, S i → T i) → F T) ∧
  (∀ S, F S ∨ F (fun i => ¬ S i)) ∧
  -- closed under countable (ℕ-indexed) intersection:
  (∀ A : Nat → (I → Prop), (∀ n, F (A n)) → F (fun i => ∀ n, A n i))

/-- ATOMIC MEASURE (§1.648): the principal ultrafilter at `i` — the members are
    exactly the subsets containing `i`. -/
def AtomicMeasure (I : Type u) (F : (I → Prop) → Prop) (i : I) : Prop :=
  F = fun J => J i

end Freyd
