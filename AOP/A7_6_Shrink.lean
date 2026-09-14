/-
  The **shrink** operator `S ↾ R` — a port of AoPA `Relations/Shrink.agda`
  (Mu, Ko, Jansson; used in Mu–Oliveira "Programming from Galois connections").

  `S ↾ R` is the largest sub-relation of `S` all of whose outputs are `R`-optimal: at each
  source point it keeps only those `S`-images that `R`-dominate every other `S`-image.  It is
  the relational backbone of every "best solution under a preference order" derivation
  (`takeWhile`, greedy coin change, …).

  TRANSLATION (AoPA → this repo).  Composition is DIAGRAM order here, so every AoPA chain is
  read right-to-left: `X ○ Y ↦ Y ≫ X`, `R ˘ ↦ R°`, and AoPA right division `R / S`
  (`X ⊑ R / S ⟺ X ○ S ⊑ R`) mirrors to repo LEFT division `S \ R = leftDiv S R`
  (`le_leftDiv_iff : X ⊑ (S \ R) ⟺ S ≫ X ⊑ R`, `Freyd.S2_3`).  Hence the AoPA definition
  `S ↾ R = S ⊓ (R / S˘)` becomes `S ∩ (S° \ R)`.

  COHERENCE with §7.  In an `UnguardedPowerLCDA` the shrink is exactly Bird & de Moor's
  (7.5) `min R · Λ S`:  `S ↾ R = Λ S ≫ est R`  (`shrink_eq_Λ_comp_est`, from
  `A7_1.Λ_comp_est`).  So the whole `min`/`Λ` machinery of `AOP.A7_1`/`A7_4` and the shrink
  calculus are one and the same operator — the AoPA universal property of `↾` is literally the
  repo's `le_Λ_comp_est_iff`.

  Mathlib-free; the pure shrink calculus lives at the `DivisionAllegory` level.
-/
module

public import AOP.A7_1
public import AOP.A6_1_RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg

universe u
variable {𝒜 : Type u}

/-! ## The shrink operator and its calculus (any `DivisionAllegory`) -/

section Division
variable [DivisionAllegory 𝒜] {A B C : 𝒜}

/-- AoPA `_↾_`: `S ↾ R = S ⊓ (R / S˘)`, mirrored to `S ∩ (S° \ R)`.  The `R`-optimal part of
    `S`: an `S`-image kept only if it `R`-dominates every other `S`-image of the same point. -/
@[expose] public def shrink (S : B ⟶ A) (R : A ⟶ A) : B ⟶ A := S ∩ (S° \ R)

@[inherit_doc] scoped infixl:65 " ↾ " => shrink

variable {S : B ⟶ A} {R : A ⟶ A} {X : B ⟶ A}

/-! ### Universal property (AoPA `↾-universal-*`)

  `X ⊑ S ↾ R  ⟺  X ⊑ S  ∧  S° ≫ X ⊑ R`
  (AoPA `X ⊑ S ∧ X ○ S˘ ⊑ R`; the second conjunct reads right-to-left). -/

/-- AoPA `↾-universal-⇒₁`. -/
theorem shrink_universal_mp₁ (h : X ⊑ S ↾ R) : X ⊑ S :=
  le_trans h (inter_lb_left _ _)                          -- proj₁ ∘ ⊓-universal-⇒

/-- AoPA `↾-universal-⇒₂`: `X ⊑ S↾R → X ○ S˘ ⊑ R`. -/
theorem shrink_universal_mp₂ (h : X ⊑ S ↾ R) : S° ≫ X ⊑ R :=
  (le_leftDiv_iff X (S°) R).mp                            -- /-universal-⇒
    (le_trans h (inter_lb_right _ _))                     -- proj₂ ∘ ⊓-universal-⇒

/-- AoPA `↾-universal-⇒`. -/
theorem shrink_universal_mp (h : X ⊑ S ↾ R) : (X ⊑ S) ∧ (S° ≫ X ⊑ R) :=
  ⟨shrink_universal_mp₁ h, shrink_universal_mp₂ h⟩

/-- AoPA `↾-universal-⇐`. -/
theorem shrink_universal_mpr (h : (X ⊑ S) ∧ (S° ≫ X ⊑ R)) : X ⊑ S ↾ R :=
  le_inter h.1                                            -- ⊓-universal-⇐
    ((le_leftDiv_iff X (S°) R).mpr h.2)                   -- /-universal-⇐

/-- AoPA `↾-universal`. -/
theorem shrink_universal : X ⊑ S ↾ R ↔ (X ⊑ S) ∧ (S° ≫ X ⊑ R) :=
  ⟨shrink_universal_mp, shrink_universal_mpr⟩

/-! ### Derived inclusions (AoPA `S↾R⊑S`, `S↾RS˘⊑R`) -/

/-- AoPA `S↾R⊑S`. -/
theorem shrink_le_left : S ↾ R ⊑ S := shrink_universal_mp₁ (le_refl _)

/-- AoPA `S↾RS˘⊑R`: `(S↾R) ○ S˘ ⊑ R`, mirrored. -/
theorem recip_comp_shrink_le : S° ≫ (S ↾ R) ⊑ R := shrink_universal_mp₂ (le_refl _)

/-! ### Absorption (AoPA `↾-simple-absorption`, `↾-fun-absorption`) -/

/-- AoPA `↾-simple-absorption`.  For a SIMPLE `T` (`T ○ T˘ ⊑ idR`, i.e. `T° ≫ T ⊑ 1`),
    `(S ↾ R) ○ T ⊑ (S ○ T) ↾ R`, mirrored to `T ≫ (S ↾ R) ⊑ (T ≫ S) ↾ R`. -/
theorem shrink_simple_absorption (S : B ⟶ A) (T : C ⟶ B) (R : A ⟶ A)
    (hT : T° ≫ T ⊑ Cat.id B) : T ≫ (S ↾ R) ⊑ (T ≫ S) ↾ R := by
  refine shrink_universal_mpr ⟨comp_mono_left T shrink_le_left, ?_⟩  -- ○-monotonic-l S↾R⊑S
  -- The AoPA chain for `((S↾R) ○ T) ○ (S ○ T)˘ ⊑ R`, mirrored right-to-left:
  --   (T≫S)° ≫ (T≫(S↾R))  =  S° ≫ (T°≫T) ≫ (S↾R)   (˘-○-distr, ○-assoc)
  --                       ⊑  S° ≫ 1 ≫ (S↾R)          (T-simple)
  --                       =  S° ≫ (S↾R)  ⊑  R         (id-intro-l, S↾RS˘⊑R)
  have e1 : (T ≫ S)° ≫ (T ≫ (S ↾ R)) = S° ≫ ((T° ≫ T) ≫ (S ↾ R)) := by
    rw [Allegory.recip_comp]; simp only [Cat.assoc]
  rw [e1]
  refine le_trans (comp_mono_left _ (comp_mono_right hT _)) ?_          -- T-simple
  rw [Cat.id_comp]                                                      -- id-intro-l
  exact recip_comp_shrink_le                                            -- S↾RS˘⊑R

/-! ### Monotonicity in the order (AoPA `↾-ord-monotonic`)

  If the preference order is more liberal, the shrink may return more. -/

/-- AoPA `↾-ord-monotonic`. -/
theorem shrink_ord_monotonic (S : B ⟶ A) (R T : A ⟶ A) (h : R ⊑ T) : S ↾ R ⊑ S ↾ T :=
  shrink_universal_mpr
    ⟨shrink_le_left,                                      -- S↾R⊑S
     le_trans recip_comp_shrink_le h⟩                     -- S↾RS˘⊑R then R⊑T

end Division

/-! ## Coherence with §7.1: shrink IS `min R · Λ S` -/

section Power
variable [UnguardedPowerLCDA 𝒜] {A B : 𝒜}

/-- **(7.5) as a coherence law.**  `S ↾ R° = Λ S ≫ est R`.  The shrink operator is exactly
    Bird & de Moor's `min R° · Λ S`; this is `A7_1.Λ_comp_est` read backwards, unfolding the
    definition `S ↾ R° = S ∩ (S° \ R°)`.  So a shrink headline `X = S ↾ R°` and an optimization
    headline `X = Λ S ≫ est R` are literally the same statement. -/
public theorem shrink_eq_Λ_comp_est (S : B ⟶ A) (R : A ⟶ A) : S ↾ R° = Λ S ≫ est R :=
  (Λ_comp_est S R).symm

end Power

/-! ## The concrete `Rel(Set)` corollary of absorption (AoPA `↾-fun-absorption`) -/

namespace RelSet

open Freyd

/-- AoPA `↾-fun-absorption`: `↾-simple-absorption` at a graph `fun f`, which is simple
    (`graph_simple`).  `(graph f) ≫ (S ↾ R) ⊑ ((graph f) ≫ S) ↾ R`. -/
theorem shrink_graph_absorption {A B C : RelSet.{0}} (S : B ⟶ A) (f : C.carrier → B.carrier)
    (R : A ⟶ A) : graph f ≫ (S ↾ R) ⊑ (graph f ≫ S) ↾ R :=
  shrink_simple_absorption S (graph f) R (graph_simple f)

end RelSet
end Freyd.Alg
