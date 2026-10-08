/-
  Bird & de Moor, *Algebra of Programming* §5.4  The power relator: the definition and its
  agreement with the existential image on maps.

  Split from `AOP.A5_4` so that a user of `powerRel`/`powerRel_map` alone (`AOP.A5_6`) does not
  wait for the rest of §5.4; `AOP.A5_4` re-exports it.
-/

module

public import AOP.A4_6
import AOP.A4_2
import Freyd.S1_56

universe u

namespace Freyd.Alg
open PowerAllegory

section PowerRelDef

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- **B&dM §5.4 p.119** (the POWER RELATOR `PR`, mirrored to Freyd's diagram order): for
    `R : a ⟶ b`, `powerRel R : [a] ⟶ [b]` relates `X` to `Y` (the Egli–Milner order) when
    EVERY element of `X` `R`-reaches into `Y` (term₁, via left division `\`: "each element
    of the input set `R`-reaches into the output set") AND every element of `Y` is
    `R`-reachable from some element of `X` (term₂, via right division `/`: "each element of
    the output set is `R`-reachable from the input set").

    Universal properties used to verify the definition (`le_leftDiv_iff`/`le_div_iff`):
    `X ⊑ ((∋a)° \ (R≫(∋b)°)) ↔ (∋a)°≫X ⊑ R≫(∋b)°` (term₁) and
    `X ⊑ (∋a≫R)/∋b ↔ X≫∋b ⊑ ∋a≫R` (term₂). -/
@[expose] public def powerRel {A B : 𝒜} (R : A ⟶ B) :
    P A ⟶ P B :=
  ((∋ A)° \ (R ≫ (∋ B)°)) ∩ ((∋ A ≫ R) / ∋ B)

/-- B&dM's own spelling of the power relator's action on an arrow: `P(R)`.  Its own brackets, like
    a relator's `F(R)`, because juxtaposition in this repo is composition. -/
notation:max "P(" R ")" => powerRel R

/-- **B&dM §5.4 p.119 top** (`P` and `E` agree on maps): for a map `f`, `powerRel f`
    coincides with the existential image `existsImage f` of `AOP.A4_6`.  The term₂
    components already match on the nose (both are `(∋a≫f)/∋b`); the term₁ component is
    identified with the reciprocal of the OTHER division component of `existsImage f`'s
    `symmDiv` unfolding via an indirect (Yoneda-style) argument using `map_shunt_left`. -/
public theorem powerRel_map {A B : 𝒜} {f : A ⟶ B} (hf : Map f) : powerRel f = existsImage f := by
  have hterm1 : ((∋ A)° \ (f ≫ (∋ B)°)) = (∋ B / (∋ A ≫ f))° := by
    have dir1 : ((∋ A)° \ (f ≫ (∋ B)°)) ⊑ (∋ B / (∋ A ≫ f))° := by
      have step1 : (∋ A)° ≫ ((∋ A)° \ (f ≫ (∋ B)°)) ⊑ f ≫ (∋ B)° := leftDiv_comp_le _ _
      have step2 : f° ≫ ((∋ A)° ≫ ((∋ A)° \ (f ≫ (∋ B)°))) ⊑ (∋ B)° :=
        (map_shunt_left hf _ _).mpr step1
      have step3 : (∋ A ≫ f)° ≫ ((∋ A)° \ (f ≫ (∋ B)°)) ⊑ (∋ B)° := by
        have e : (∋ A ≫ f)° = f° ≫ (∋ A)° := Allegory.recip_comp _ _
        rw [e, Cat.assoc]; exact step2
      have step4 := recip_mono step3
      simp only [Allegory.recip_comp, Allegory.recip_recip] at step4
      have step5 : ((∋ A)° \ (f ≫ (∋ B)°))° ⊑ ∋ B / (∋ A ≫ f) := (le_div_iff _ _ _).mpr step4
      have step6 := recip_mono step5
      rwa [Allegory.recip_recip] at step6
    have dir2 : (∋ B / (∋ A ≫ f))° ⊑ ((∋ A)° \ (f ≫ (∋ B)°)) := by
      have step1 : (∋ B / (∋ A ≫ f)) ≫ (∋ A ≫ f) ⊑ ∋ B := DivisionAllegory.div_comp_le _ _
      have step2 := recip_mono step1
      simp only [Allegory.recip_comp] at step2
      have step3 : f° ≫ ((∋ A)° ≫ (∋ B / (∋ A ≫ f))°) ⊑ (∋ B)° := by
        rw [Cat.assoc] at step2; exact step2
      have step4 : (∋ A)° ≫ (∋ B / (∋ A ≫ f))° ⊑ f ≫ (∋ B)° :=
        (map_shunt_left hf _ _).mp step3
      exact (le_leftDiv_iff _ _ _).mpr step4
    exact le_antisymm dir1 dir2
  show ((∋ A)° \ (f ≫ (∋ B)°)) ∩ ((∋ A ≫ f) / ∋ B)
      = ((∋ A ≫ f) / ∋ B) ∩ ((∋ B / (∋ A ≫ f))°)
  rw [hterm1]
  exact Allegory.inter_comm _ _

end PowerRelDef

end Freyd.Alg
