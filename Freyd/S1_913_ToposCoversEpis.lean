/-
  Freyd & Scedrov, *Categories and Allegories* §1.913 — COVERS = EPICS.

  "In any cartesian category with a subobject classifier, covers coincide with epics."
  (Book §1.913, the statement just before §1.914.)

  The book's argument: every subobject `A' ↪ A` appears as the equalizer of `χ_{A'}` and
  `(A → 1 → Ω)` (the classifier square is a pullback, hence an equalizer once the right leg
  is the universal point).  Consequently:

    * COVER ⟹ EPIC: a cover is right-cancellable (`cover_epi`, S1_52, needs only finite
      products + pullbacks — independent of the classifier).
    * EPIC ⟹ COVER: an epic `f` that factors `g ≫ m = f` through a monic `m` makes `m`
      epic; an epic monic in a category with a subobject classifier is an isomorphism
      (`epi_mono_is_iso` below), so `m` is iso and `f` is a cover.

  This is the §1.913 building block the §1.933 route to `PullbacksTransferCovers` rests on
  ("covers coincide with epics; any functor with a right adjoint preserves epics").  It is
  ADDITIVE: a single new file, no existing proof touched.  It needs ONLY the topos's
  `HasSubobjectClassifier` (terminal + pullbacks + classifier) and `HasBinaryProducts`,
  all of which a `Topos` supplies — no power objects, no exponentials, no §1.54.
-/

import Freyd.S1_09
import Freyd.S1_52

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

open HasSubobjectClassifier

/-- **§1.913 key lemma: an epic monic is an isomorphism**, in any cartesian category with a
    subobject classifier.

    `m : C ↪ Y` is the pullback of the universal point `true : 1 → Ω` along its characteristic
    map `χ_m`.  Since `term C = m ≫ term Y` (terminal uniqueness), the classifier square reads
    `m ≫ χ_m = m ≫ (term Y ≫ true)`; `m` epic cancels it to `χ_m = term Y ≫ true`.  Then
    `id_Y` together with `term Y` is a cone over `(χ_m, true)`, so the pullback UMP yields a
    section `r : Y → C` with `r ≫ m = id_Y`.  `m` monic upgrades this to a two-sided inverse. -/
theorem epi_mono_is_iso [HasSubobjectClassifier 𝒞] {C Y : 𝒞} (m : C ⟶ Y) (hm : Monic m)
    (hepi : ∀ {Z : 𝒞} (a b : Y ⟶ Z), m ≫ a = m ≫ b → a = b) : IsIso m := by
  -- classifier data: χ_m and the pullback square `m ≫ χ_m = term C ≫ true`.
  let χ : Y ⟶ omega (𝒞 := 𝒞) := classify m hm
  have hsq : m ≫ χ = term C ≫ true := classify_sq m hm
  -- `term C = m ≫ term Y`, so the square is `m ≫ χ = m ≫ (term Y ≫ true)`.
  have hsq' : m ≫ χ = m ≫ (term Y ≫ true) := by
    rw [hsq, ← Cat.assoc]; rw [term_uniq (term C) (m ≫ term Y)]
  -- `m` epic ⟹ `χ = term Y ≫ true`.
  have hχ : χ = term Y ≫ true := hepi χ (term Y ≫ true) hsq'
  -- `(Y, id_Y, term Y)` is a cone over the cospan `(χ, true)`.
  have hcone : Cat.id Y ≫ χ = term Y ≫ true := by rw [Cat.id_comp, hχ]
  let d : Cone χ true := ⟨Y, Cat.id Y, term Y, hcone⟩
  -- the classifier square is a pullback; lift `d` through it to get `r : Y → C`.
  obtain ⟨r, ⟨hr₁, _⟩, _⟩ := classify_pullback m hm d
  -- `hr₁ : r ≫ m = id_Y` (π₁ of the classifier cone is `m`).
  refine ⟨r, ?_, hr₁⟩
  -- `m` monic upgrades the section to a retraction: `m ≫ r ≫ m = m = id_C ≫ m`.
  exact hm (m ≫ r) (Cat.id C) (by rw [Cat.assoc, hr₁, Cat.comp_id, Cat.id_comp])

/-- **§1.913 (epic ⟹ cover)**: in a cartesian category with a subobject classifier, every
    epimorphism is a cover.  If `f` factors `g ≫ m = f` through a monic `m`, then `m` is epic
    (right-cancel `f` epic), hence iso by `epi_mono_is_iso`; so every monic `f` factors through
    is iso, i.e. `f` is a cover. -/
theorem cover_of_epi [HasSubobjectClassifier 𝒞] {X Y : 𝒞} {f : X ⟶ Y}
    (hf : ∀ {Z : 𝒞} (a b : Y ⟶ Z), f ≫ a = f ≫ b → a = b) : Cover f := by
  intro C m g hm hgm
  -- `m` is epic: from `g ≫ m = f` and `f` epic, `m ≫ a = m ≫ b ⟹ a = b`.
  refine epi_mono_is_iso m hm (fun {Z} a b hab => ?_)
  apply hf a b
  calc f ≫ a = (g ≫ m) ≫ a := by rw [hgm]
    _ = g ≫ (m ≫ a) := Cat.assoc _ _ _
    _ = g ≫ (m ≫ b) := by rw [hab]
    _ = (g ≫ m) ≫ b := (Cat.assoc _ _ _).symm
    _ = f ≫ b := by rw [hgm]

/-- **§1.913 (covers = epics)**: in a cartesian category with a subobject classifier, a map is
    a cover iff it is epic.  Forward is `cover_epi` (S1_52); backward is `cover_of_epi`. -/
theorem cover_iff_epi [HasSubobjectClassifier 𝒞] [HasBinaryProducts 𝒞] {X Y : 𝒞} (f : X ⟶ Y) :
    Cover f ↔ (∀ {Z : 𝒞} (a b : Y ⟶ Z), f ≫ a = f ≫ b → a = b) := by
  constructor
  · intro hc Z a b hab; exact cover_epi hc hab
  · intro hf; exact cover_of_epi hf

end Freyd
