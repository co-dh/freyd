/-
  **Generic relational hylomorphism** — a port of the fixed-point core of AoPA's `Data.Generic.Hylo`.

  For algebras `R : ⟦F⟧ A B ⟶ B`, `S : ⟦F⟧ A C ⟶ C`, the *hylomorphism* is `⦇R⦈ ○ ⦇S⦈˘`
  (`(foldRel F S)° ≫ foldRel F R`).  aopa proves it is the LEAST PREFIXED POINT of the recursion body
  `X ↦ R ○ ⟦F⟧X ○ S˘` (`hylo-lpfp`).  Here we prove the stronger, fully constructive fact that it is a
  genuine FIXED POINT (`hylo_fixed`): the prefixed-point inequality `hylo_pfp` is one half of it.  Both
  come by equational rewriting from `foldR_computation`, `fmapR_functor` and `fmapR_recip` — no
  well-foundedness, no division.

  * `foldR_computation_recip` — the converse computation `⦇S⦈˘ = S˘ ○ ⟦F⟧⦇S⦈˘ ○ In`.
  * `hylo_fixed` — `⦇R⦈ ○ ⦇S⦈˘ = R ○ ⟦F⟧(⦇R⦈ ○ ⦇S⦈˘) ○ S˘` (aopa `proj₁ hylo-lfp`, as an equality).
  * `hylo_pfp` — the `⊑` half (aopa `proj₁ hylo-lpfp`).

  BLOCKED (needs infrastructure absent from the repo): the LEASTNESS half `proj₂ hylo-lpfp`
  (`hylo-post⊑pre`/`hylo-unique`/`hylo-refine` and the functional `hylo`) requires relational
  well-founded recursion — `Acc`/`acc-fold` over `ε F ○ g` (Membership's `ε_wpre_*`), the factor
  `⋱`/`⍀`, and the coreflexive-based induction of `Relations.WellFound`.  None of that transfinite
  machinery exists in this mathlib-free repo (only `Freyd.WellOrdering`, for a different purpose), so
  those items are precise infrastructure gaps, not proof difficulties.  Composition is diagram order.
-/
import AOP.A6_PolyFold

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Poly

open Freyd Freyd.Alg.RelSet

/-- The converse computation rule `⦇S⦈˘ = S˘ ○ ⟦F⟧⦇S⦈˘ ○ In` (aopa `⦇S⦈˘-computation`, as an
    equality; obtained by reciprocating `foldR_computation'`). -/
theorem foldR_computation_recip (F : PolyF) {A C : Type} (S : Fo F ⟨A⟩ ⟨C⟩ ⟶ (⟨C⟩ : RelSet.{0})) :
    (foldRel F S)° = S° ≫ fmapR F ((foldRel F S)°) ≫ inGraph F A := by
  have h : (foldRel F S)° = ((inGraph F A)° ≫ fmapR F (foldRel F S) ≫ S)° :=
    congrArg (fun t : (⟨Mu F A⟩ : RelSet.{0}) ⟶ ⟨C⟩ => t°) (foldR_computation' F S)
  rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, fmapR_recip, Cat.assoc] at h
  exact h

/-- aopa `proj₁ hylo-lfp` (as an equality): `⦇R⦈ ○ ⦇S⦈˘` is a fixed point of `X ↦ R ○ ⟦F⟧X ○ S˘`. -/
theorem hylo_fixed (F : PolyF) {A B C : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (S : Fo F ⟨A⟩ ⟨C⟩ ⟶ (⟨C⟩ : RelSet.{0})) :
    (foldRel F S)° ≫ foldRel F R
      = S° ≫ fmapR F ((foldRel F S)° ≫ foldRel F R) ≫ R :=
  calc (foldRel F S)° ≫ foldRel F R
      = (S° ≫ fmapR F ((foldRel F S)°) ≫ inGraph F A) ≫ foldRel F R :=
        congrArg (· ≫ foldRel F R) (foldR_computation_recip F S)
    _ = S° ≫ fmapR F ((foldRel F S)°) ≫ (inGraph F A ≫ foldRel F R) := by
        rw [Cat.assoc, Cat.assoc]
    _ = S° ≫ fmapR F ((foldRel F S)°) ≫ (fmapR F (foldRel F R) ≫ R) := by
        rw [foldR_computation F R]
    _ = S° ≫ (fmapR F ((foldRel F S)°) ≫ fmapR F (foldRel F R)) ≫ R := by
        rw [Cat.assoc]
    _ = S° ≫ fmapR F ((foldRel F S)° ≫ foldRel F R) ≫ R := by
        rw [fmapR_functor F ⟨A⟩ ((foldRel F S)°) (foldRel F R)]

/-- aopa `proj₁ hylo-lpfp`: the prefixed-point inequality `R ○ ⟦F⟧H ○ S˘ ⊑ H`. -/
theorem hylo_pfp (F : PolyF) {A B C : Type} (R : Fo F ⟨A⟩ ⟨B⟩ ⟶ (⟨B⟩ : RelSet.{0}))
    (S : Fo F ⟨A⟩ ⟨C⟩ ⟶ (⟨C⟩ : RelSet.{0})) :
    S° ≫ fmapR F ((foldRel F S)° ≫ foldRel F R) ≫ R ⊑ (foldRel F S)° ≫ foldRel F R :=
  le_of_eq (hylo_fixed F R S).symm

end Freyd.Alg.RelSet.Poly
