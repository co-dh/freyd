/-
  Port of AoPA `Relations/MonoFactor.agda`: ranges and the two "monotype factors" of
  Doornbos & Backhouse, in `Rel(Set)`.

  A subset `P : ℙ B` is `P : b.carrier → Prop`; AoPA's coreflexive `P ¿ : B ← B` becomes the
  partial identity `corefl P : b ⟶ b`, `corefl P x y := (x = y ∧ P x)`.  Composition reverses
  (`X ○ Y ↦ Y ≫ X`), so `P ¿ ○ R ↦ R ≫ corefl P` and `R ○ P ¿ ↦ corefl P ≫ R`.

  Mathlib-free; axioms ⊆ {propext} (via `le_iff`/`hom_ext`).
-/
module

import AOP.A6_1_RelSet

universe u

namespace Freyd.Alg
namespace RelSet

variable {A B : RelSet.{u}}

/-- Subset inclusion of `ℙ B` predicates. -/
def Incl (s t : B.carrier → Prop) : Prop := ∀ x, s x → t x

/-! ### Ranges (AoPA `ran`) -/

/-- The range of `R` (AoPA `ran`): `ran R y` iff some `x` has `R x y`. -/
def ran (R : A ⟶ B) : B.carrier → Prop := fun y => ∃ x, R x y

/-- AoPA `ran-universal-⇒`: `ran R ⊆ P → R ⊑ P ¿ ○ R`. -/
theorem ran_universal_mp (R : A ⟶ B) (P : B.carrier → Prop)
    (h : Incl (ran R) P) : R ⊑ R ≫ corefl P := by
  rw [le_iff]; intro x y hR
  exact ⟨y, hR, rfl, h y ⟨x, hR⟩⟩

/-- AoPA `ran-universal-⇐`: `R ⊑ P ¿ ○ R → ran R ⊆ P`. -/
theorem ran_universal_mpr (R : A ⟶ B) (P : B.carrier → Prop)
    (h : R ⊑ R ≫ corefl P) : Incl (ran R) P := by
  rintro y ⟨x, hR⟩
  obtain ⟨z, _, hzy, hPz⟩ := le_iff.mp h x y hR
  exact hzy ▸ hPz

/-- AoPA `ran-universal`: the two directions combined. -/
theorem ran_universal (R : A ⟶ B) (P : B.carrier → Prop) :
    Incl (ran R) P ↔ R ⊑ R ≫ corefl P :=
  ⟨ran_universal_mp R P, ran_universal_mpr R P⟩

/-- AoPA `ran-cancellation`: `R ⊑ (ran R) ¿ ○ R`. -/
theorem ran_cancellation (R : A ⟶ B) : R ⊑ R ≫ corefl (ran R) :=
  ran_universal_mp R (ran R) (fun _ h => h)

/-! ### The monotype factor `⍀` (AoPA `_⍀_`) -/

/-- AoPA `R ⍀ P`: `(R ⍀ P) x = ∀ y, R x y → P y`. -/
def monoFactor (R : A ⟶ B) (P : B.carrier → Prop) : A.carrier → Prop :=
  fun x => ∀ y, R x y → P y

/-- AoPA `⍀-universal-⇒`: `Q ⊆ R ⍀ P → ran (R ○ Q ¿) ⊆ P`. -/
theorem monoFactor_universal_mp (R : A ⟶ B) (Q : A.carrier → Prop) (P : B.carrier → Prop)
    (h : Incl Q (monoFactor R P)) : Incl (ran (corefl Q ≫ R)) P := by
  rintro y ⟨x, z, ⟨hxz, hQx⟩, hRzy⟩
  exact h x hQx y (hxz ▸ hRzy)

/-- AoPA `⍀-universal-⇐`: `ran (R ○ Q ¿) ⊆ P → Q ⊆ R ⍀ P`. -/
theorem monoFactor_universal_mpr (R : A ⟶ B) (Q : A.carrier → Prop) (P : B.carrier → Prop)
    (h : Incl (ran (corefl Q ≫ R)) P) : Incl Q (monoFactor R P) := by
  intro x hQx y hRxy
  exact h y ⟨x, x, ⟨rfl, hQx⟩, hRxy⟩

/-- AoPA `⍀-universal`. -/
theorem monoFactor_universal (R : A ⟶ B) (Q : A.carrier → Prop) (P : B.carrier → Prop) :
    Incl Q (monoFactor R P) ↔ Incl (ran (corefl Q ≫ R)) P :=
  ⟨monoFactor_universal_mp R Q P, monoFactor_universal_mpr R Q P⟩

/-- AoPA `⍀-cancellation`: `R ○ (R ⍀ P) ¿ ⊑ P ¿ ○ R`. -/
theorem monoFactor_cancellation (R : A ⟶ B) (P : B.carrier → Prop) :
    corefl (monoFactor R P) ≫ R ⊑ R ≫ corefl P := by
  rw [le_iff]; intro x y
  rintro ⟨z, ⟨hxz, hmf⟩, hRzy⟩
  -- `hmf : ∀ w, R x w → P w`; `hxz : x = z`; so `R x y` and `P y`.
  have hRxy : R x y := hxz ▸ hRzy
  exact ⟨y, hRxy, rfl, hmf y hRxy⟩

/-! ### The second factor `⋱` (AoPA `_⋱_`, Doornbos & Backhouse 1995) -/

/-- AoPA `R ⋱ S`: `(R ⋱ S) x = ∀ y, R x y → S x y`. -/
def secondFactor (R S : A ⟶ B) : A.carrier → Prop :=
  fun x => ∀ y, R x y → S x y

/-- AoPA `⋱-universal-⇒`: `P ⊆ R ⋱ S → R ○ P ¿ ⊑ S`. -/
theorem secondFactor_universal_mp (P : A.carrier → Prop) (R S : A ⟶ B)
    (h : Incl P (secondFactor R S)) : corefl P ≫ R ⊑ S := by
  rw [le_iff]; intro x y
  rintro ⟨z, ⟨hxz, hPx⟩, hRzy⟩
  exact h x hPx y (hxz ▸ hRzy)

/-- AoPA `⋱-universal-⇐`: `R ○ P ¿ ⊑ S → P ⊆ R ⋱ S`. -/
theorem secondFactor_universal_mpr (P : A.carrier → Prop) (R S : A ⟶ B)
    (h : corefl P ≫ R ⊑ S) : Incl P (secondFactor R S) := by
  intro x hPx y hRxy
  exact le_iff.mp h x y ⟨x, ⟨rfl, hPx⟩, hRxy⟩

/-- AoPA `⋱-universal`. -/
theorem secondFactor_universal (P : A.carrier → Prop) (R S : A ⟶ B) :
    Incl P (secondFactor R S) ↔ corefl P ≫ R ⊑ S :=
  ⟨secondFactor_universal_mp P R S, secondFactor_universal_mpr P R S⟩

/-- AoPA `⋱-cancellation`: `R ○ (R ⋱ S) ¿ ⊑ S`. -/
theorem secondFactor_cancellation (R S : A ⟶ B) :
    corefl (secondFactor R S) ≫ R ⊑ S :=
  secondFactor_universal_mp (secondFactor R S) R S (fun _ h => h)

end RelSet
end Freyd.Alg
