/-
  Freyd & Scedrov, *Categories and Allegories* §1.817–§1.818
  Representability condition for adjoints (§1.817),
  contravariant adjunctions on the right / on the left (§1.818).

  Note: The full representability theorem (§1.817) needs a `Cat` instance on `Type`
  for set-valued functors.  We defer that to a later file when it is needed
  (the General Adjoint Functor Theorem, §1.83).
-/

import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_80
import Freyd.S1_14


universe v u₁ u₂

namespace Freyd

variable {𝒞 : Type u₁} [Cat.{v} 𝒞] {𝒟 : Type u₂} [Cat.{v} 𝒟]

/-! ## §1.818  Contravariant adjunctions

  A pair of contravariant functors F : 𝒞 → 𝒟, G : 𝒟 → 𝒞 are ADJOINT ON THE RIGHT
  if (B, FA) ≅ (A, GB) naturally in both variables.  They are ADJOINT ON THE LEFT
  if (FA, B) ≅ (GB, A) naturally (§1.818).

  The book notes that this reduces to covariant adjoints by composing with
  opposite categories.  We give the direct definitions. -/

-- (CONTRAVARIANT FUNCTOR `ContraFunctor` is defined canonically in S1_14 §1.182; reused here.)

/-- F, G are ADJOINT ON THE RIGHT: (B, FA) ≅ (A, GB) naturally (§1.818).
    The naturality conditions encode contravariance of both F and G. -/
structure AdjointOnRight (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞) [ContraFunctor F] [ContraFunctor G] where
  φ {A : 𝒞} {B : 𝒟} : (B ⟶ F A) → (A ⟶ G B)
  ψ {A : 𝒞} {B : 𝒟} : (A ⟶ G B) → (B ⟶ F A)
  φψ : ∀ {A B} (f : A ⟶ G B), φ (ψ f) = f
  ψφ : ∀ {A B} (f : B ⟶ F A), ψ (φ f) = f
  φ_nat_𝒞 : ∀ {A' A B} (a : A' ⟶ A) (h : B ⟶ F A),
    φ (h ≫ ContraFunctor.map a) = a ≫ φ h
  φ_nat_𝒟 : ∀ {A B B'} (h : B ⟶ F A) (b : B' ⟶ B),
    φ (b ≫ h) = φ h ≫ ContraFunctor.map b

/-- F, G are ADJOINT ON THE LEFT: (FA, B) ≅ (GB, A) naturally (§1.818). -/
structure AdjointOnLeft (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞) [ContraFunctor F] [ContraFunctor G] where
  φ {A : 𝒞} {B : 𝒟} : (F A ⟶ B) → (G B ⟶ A)
  ψ {A : 𝒞} {B : 𝒟} : (G B ⟶ A) → (F A ⟶ B)
  φψ : ∀ {A B} (f : G B ⟶ A), φ (ψ f) = f
  ψφ : ∀ {A B} (f : F A ⟶ B), ψ (φ f) = f
  φ_nat_𝒞 : ∀ {A' A B} (a : A ⟶ A') (h : F A ⟶ B),
    φ (ContraFunctor.map a ≫ h) = φ h ≫ a
  φ_nat_𝒟 : ∀ {A B B'} (h : F A ⟶ B) (b : B ⟶ B'),
    φ (h ≫ b) = ContraFunctor.map b ≫ φ h

end Freyd
