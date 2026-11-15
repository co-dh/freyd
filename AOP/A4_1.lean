/-
  Bird & de Moor, *Algebra of Programming* §4.1  Allegories.

  Only the facts NOT already present in Freyd §2.1 (`Freyd.S2_1`) are added here.
  Composition, reciprocation, intersection and the order are exactly Freyd's
  (`≫`, `°`, `∩`, `⊑`); B&dM's right-to-left composition has already been mirrored
  into this diagram-order convention by the caller — every statement below is
  taken over verbatim, not re-derived from the book's own notation.
-/

module

public import Freyd.S2_10
public import Freyd.S1_38

universe v u

namespace Freyd.Alg

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ## §4.1  Order form of semi-distributivity (B&dM p.83)

  Freyd states semi-distributivity as an equation (`Allegory.semidistrib`); B&dM works
  with its two order consequences directly.  Both are immediate from `comp_mono_left`/
  `comp_mono_right` plus `le_inter`, so no use of the equational axiom is needed. -/

/-- Order form of semi-distributivity (B&dM p.83): `R(S∩T) ⊑ RS ∩ RT`. -/
public theorem comp_inter_le {A B C : 𝒜} (R : A ⟶ B) (S T : B ⟶ C) :
    R ≫ (S ∩ T) ⊑ (R ≫ S) ∩ (R ≫ T) :=
  le_inter (comp_mono_left R (inter_lb_left S T)) (comp_mono_left R (inter_lb_right S T))

/-- Order form of semi-distributivity, other side (B&dM p.83): `(S∩T)R ⊑ SR ∩ TR`. -/
public theorem inter_comp_le {A B C : 𝒜} (S T : A ⟶ B) (R : B ⟶ C) :
    (S ∩ T) ≫ R ⊑ (S ≫ R) ∩ (T ≫ R) :=
  le_inter (comp_mono_right (inter_lb_left S T) R) (comp_mono_right (inter_lb_right S T) R)

/-! ## §4.1  Symmetric modular law (B&dM 4.8) -/

/-- **Symmetric modular law** (B&dM 4.8): `(R≫S) ∩ T ⊑ (R∩T≫S°) ≫ (S∩R°≫T)`.
    Book proof: `(R≫S)∩T ⊑ ((R∩T≫S°)≫S)∩T` (`modular_le` plus `T` on the nose), then
    `modular_le_right` on `U := R∩T≫S°` gives `U≫S ∩ T ⊑ U≫(S∩U°≫T)`, and `U°≫T ⊑ R°≫T`
    since `U ⊑ R`. -/
public theorem modular_sym {A B C : 𝒜} (R : A ⟶ B) (S : B ⟶ C) (T : A ⟶ C) :
    (R ≫ S) ∩ T ⊑ (R ∩ T ≫ S°) ≫ (S ∩ R° ≫ T) := by
  have step1 : (R ≫ S) ∩ T ⊑ ((R ∩ T ≫ S°) ≫ S) ∩ T :=
    le_inter (modular_le R S T) (inter_lb_right _ _)
  have step2 : ((R ∩ T ≫ S°) ≫ S) ∩ T ⊑ (R ∩ T ≫ S°) ≫ (S ∩ (R ∩ T ≫ S°)° ≫ T) :=
    modular_le_right (R ∩ T ≫ S°) S T
  have step3 : (R ∩ T ≫ S°)° ≫ T ⊑ R° ≫ T :=
    comp_mono_right (recip_mono (inter_lb_left R (T ≫ S°))) T
  have step4 : S ∩ (R ∩ T ≫ S°)° ≫ T ⊑ S ∩ R° ≫ T :=
    le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) step3)
  exact le_trans step1 (le_trans step2 (comp_mono_left (R ∩ T ≫ S°) step4))

/-! ## §4.1  Consequences of the symmetric modular law (B&dM 4.9, 4.10) -/

/-- **B&dM 4.9**: `(R°≫S) ∩ id_b ⊑ (R∩S)°≫(R∩S)`, for `R S : a ⟶ b`.
    Instantiate `modular_sym` with `(R°, S, id_b)` and simplify. -/
theorem recip_comp_inter_id_le {A B : 𝒜} (R S : A ⟶ B) :
    (R° ≫ S) ∩ Cat.id B ⊑ (R ∩ S)° ≫ (R ∩ S) := by
  have h := modular_sym R° S (Cat.id B)
  simp only [Cat.id_comp, Allegory.recip_recip, Cat.comp_id] at h
  rw [← Allegory.recip_inter, Allegory.inter_comm S R] at h
  exact h

/-! ## §4.1  Refinement of an intersection through a factor (B&dM Exercise 4.5) -/

/-- **Ex 4.5**: `R ∩ (U≫V) = R ∩ ((U∩R≫V°)≫V)`, for `U : a ⟶ b`, `V : b ⟶ c`, `R : a ⟶ c`.
    `⊒` by monotonicity (`U∩R≫V° ⊑ U`); `⊑` by `modular_le` (`R∩(U≫V) = (U≫V)∩R ⊑ (U∩RV°)V`). -/
theorem inter_comp_refine {A B C : 𝒜} (U : A ⟶ B) (V : B ⟶ C) (R : A ⟶ C) :
    R ∩ (U ≫ V) = R ∩ ((U ∩ R ≫ V°) ≫ V) := by
  apply le_antisymm
  · have h1 : R ∩ (U ≫ V) ⊑ (U ∩ R ≫ V°) ≫ V := by
      have h := modular_le U V R
      rwa [Allegory.inter_comm (U ≫ V) R] at h
    exact le_inter (inter_lb_left _ _) h1
  · have hmono : (U ∩ R ≫ V°) ≫ V ⊑ U ≫ V :=
      comp_mono_right (inter_lb_left U (R ≫ V°)) V
    exact le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) hmono)

/-! ## §4.1  Product allegory (B&dM Exercise 4.7)

  Relational reasoning on pairs `(R,S)` — the componentwise ⊑ order and the fact that
  pairing preserves allegory structure — is what lets B&dM calculate with two relations
  at once during program derivation.  Builds on the `S1_38.prodCat` category structure;
  the `toCat` field of `Allegory` is filled automatically by instance search (the same
  pattern as every other `instance … : Allegory X where` in this repo that already has
  a separate `Cat X` instance in scope). -/

/-- **Ex 4.7**: the product of two allegories is an allegory, with `°` and `∩` componentwise. -/
@[expose] public instance prodAllegory {𝒜 ℬ : Type u} [Allegory.{v} 𝒜] [Allegory.{v} ℬ] : Allegory (𝒜 × ℬ) where
  recip R := (R.1°, R.2°)
  inter R S := (R.1 ∩ S.1, R.2 ∩ S.2)
  recip_recip R := Prod.ext (Allegory.recip_recip R.1) (Allegory.recip_recip R.2)
  recip_comp R S := Prod.ext (Allegory.recip_comp R.1 S.1) (Allegory.recip_comp R.2 S.2)
  recip_inter R S := Prod.ext (Allegory.recip_inter R.1 S.1) (Allegory.recip_inter R.2 S.2)
  inter_idem R := Prod.ext (Allegory.inter_idem R.1) (Allegory.inter_idem R.2)
  inter_comm R S := Prod.ext (Allegory.inter_comm R.1 S.1) (Allegory.inter_comm R.2 S.2)
  inter_assoc R S T := Prod.ext (Allegory.inter_assoc R.1 S.1 T.1) (Allegory.inter_assoc R.2 S.2 T.2)
  semidistrib R S T := Prod.ext (Allegory.semidistrib R.1 S.1 T.1) (Allegory.semidistrib R.2 S.2 T.2)
  modular R S T := Prod.ext (Allegory.modular R.1 S.1 T.1) (Allegory.modular R.2 S.2 T.2)

/-- **Ex 4.7**: order in the product allegory is componentwise. -/
theorem prod_le_iff {𝒜 ℬ : Type u} [Allegory.{v} 𝒜] [Allegory.{v} ℬ]
    {p q : 𝒜 × ℬ} (R S : p ⟶ q) :
    R ⊑ S ↔ R.1 ⊑ S.1 ∧ R.2 ⊑ S.2 := by
  constructor
  · intro h
    dsimp [le] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    dsimp [le] at h1 h2 ⊢
    exact Prod.ext h1 h2

end Freyd.Alg
