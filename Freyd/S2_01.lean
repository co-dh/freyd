/-
  Freyd & Scedrov, *Categories and Allegories* §2.1  Basic definitions.

  §2.1  RECIPROCATION, COMPOSITION, INTERSECTION, semidistributivity, law of modularity
  §2.11 ALLEGORY
  §2.111 For any regular category C, Rel(C) is an allegory
  §2.12 REFLEXIVE, SYMMETRIC, TRANSITIVE, COREFLEXIVE
  §2.122 DOMAIN
  §2.13 ENTIRE, SIMPLE, MAP
  §2.14 TABULATES, TABULAR ALLEGORY
  §2.15 PARTIAL UNIT, UNIT, UNITARY ALLEGORY
  §2.16 PRE-TABULAR, EFFECTIVE, SEMI-SIMPLE
-/

import Freyd.S1_01
import Freyd.S1_41


universe v u

namespace Freyd.Alg

/-! ## §2.11  Allegory

  An ALLEGORY is a category with a unary operation R° (reciprocation)
  and a binary partial operation R ∩ S (intersection) defined whenever
  □R = □S and R□ = S□.

  The equational axioms: monoid for composition, semi-lattice for
  intersection, anti-involution for reciprocation, semi-distributivity,
  and the law of modularity. -/

/-- An ALLEGORY (§2.11): category with reciprocation (°), intersection (∩),
    semi-distributivity, and the modular law. -/
class Allegory (𝒜 : Type u) extends Cat.{v} 𝒜 where
  /-- RECIPROCATION: R° : b → a when R : a → b. -/
  recip {a b : 𝒜} (R : a ⟶ b) : b ⟶ a
  /-- INTERSECTION: R ∩ S : a → b when R, S : a → b. -/
  inter {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b

  /-- (R°)° = R (§2.11). -/
  recip_recip {a b : 𝒜} (R : a ⟶ b) : recip (recip R) = R
  /-- (RS)° = S°R° (§2.11). -/
  recip_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) : recip (R ≫ S) = recip S ≫ recip R
  /-- (R ∩ S)° = R° ∩ S° (§2.11). -/
  recip_inter {a b : 𝒜} (R S : a ⟶ b) : recip (inter R S) = inter (recip R) (recip S)

  /-- R ∩ R = R (§2.11). -/
  inter_idem {a b : 𝒜} (R : a ⟶ b) : inter R R = R
  /-- R ∩ S = S ∩ R (§2.11). -/
  inter_comm {a b : 𝒜} (R S : a ⟶ b) : inter R S = inter S R
  /-- R ∩ (S ∩ T) = (R ∩ S) ∩ T (§2.11). -/
  inter_assoc {a b : 𝒜} (R S T : a ⟶ b) : inter R (inter S T) = inter (inter R S) T

  /-- SEMI-DISTRIBUTIVITY: R(S ∩ T) = RS ∩ R(S ∩ T) ∩ RT (§2.11).
      Equivalent to R(S ∩ T) ⊑ RS ∩ RT. -/
  semidistrib {a b c : 𝒜} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ inter S T = inter (inter (R ≫ S) (R ≫ inter S T)) (R ≫ T)

  /-- MODULAR LAW: RS ∩ T = (RS ∩ T) ∩ (R ∩ TS°)S (§2.11).
      Equivalent to RS ∩ T ⊑ (R ∩ TS°)S. -/
  modular {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    inter (R ≫ S) T = inter (inter (R ≫ S) T) ((inter R (T ≫ recip S)) ≫ S)

/-! ### Notation for allegory operations -/

/-- Reciprocation notation R° -/
postfix:max (name := allegoryRecip) "°" => Allegory.recip

/-- Intersection notation R ∩ S -/
infixl:70 " ∩ " => Allegory.inter

/-- The ALLEGORY ORDER: R ⊑ S iff R = R ∩ S (§2.11).
    In the book, this is denoted R ⊂ S. -/
def le {a b : 𝒜} [Allegory 𝒜] (R S : a ⟶ b) : Prop :=
  R ∩ S = R

infix:50 " ⊑ " => le

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ### Order properties derived from semi-lattice equations -/

theorem inter_eq_left {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) : R ∩ S = R := h

theorem le_refl {a b : 𝒜} (R : a ⟶ b) : R ⊑ R := by
  dsimp [le]; rw [Allegory.inter_idem]

theorem le_trans {a b : 𝒜} {R S T : a ⟶ b} (hRS : R ⊑ S) (hST : S ⊑ T) : R ⊑ T := by
  dsimp [le] at hRS hST ⊢
  calc
    R ∩ T = (R ∩ S) ∩ T := by rw [hRS]
    _ = R ∩ (S ∩ T) := by rw [Allegory.inter_assoc]
    _ = R ∩ S := by rw [hST]
    _ = R := hRS

theorem le_antisymm {a b : 𝒜} {R S : a ⟶ b} (hRS : R ⊑ S) (hSR : S ⊑ R) : R = S := by
  dsimp [le] at hRS hSR
  calc
    R = R ∩ S := by rw [hRS]
    _ = S ∩ R := by rw [Allegory.inter_comm]
    _ = S := by rw [hSR]

theorem inter_lb_left {a b : 𝒜} (R S : a ⟶ b) : R ∩ S ⊑ R := by
  dsimp [le]
  calc
    (R ∩ S) ∩ R = R ∩ (R ∩ S) := by
      rw [Allegory.inter_comm (R ∩ S) R, Allegory.inter_comm R S]
    _ = (R ∩ R) ∩ S := by rw [Allegory.inter_assoc]
    _ = R ∩ S := by rw [Allegory.inter_idem]

theorem inter_lb_right {a b : 𝒜} (R S : a ⟶ b) : R ∩ S ⊑ S := by
  rw [Allegory.inter_comm R S]; exact inter_lb_left S R

theorem le_inter {a b : 𝒜} {R S T : a ⟶ b} (hRS : R ⊑ S) (hRT : R ⊑ T) : R ⊑ S ∩ T := by
  dsimp [le] at hRS hRT ⊢
  calc
    R ∩ (S ∩ T) = (R ∩ S) ∩ T := by rw [Allegory.inter_assoc]
    _ = R ∩ T := by rw [hRS]
    _ = R := hRT

/-! ### Derived order properties for reciprocation and composition -/

/-- Reciprocation preserves order: R ⊑ S → R° ⊑ S° (§2.11). -/
theorem recip_mono {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) : R° ⊑ S° := by
  dsimp [le] at h ⊢
  calc
    R° ∩ S° = (R ∩ S)° := by rw [← Allegory.recip_inter]
    _ = R° := by rw [h]

/-- Reciprocation is its own Galois adjoint: R° ⊑ S ↔ R ⊑ S° (§2.11). -/
theorem recip_le_iff {a b : 𝒜} {R : a ⟶ b} {S : b ⟶ a} : R° ⊑ S ↔ R ⊑ S° :=
  ⟨fun h => by simpa [Allegory.recip_recip] using recip_mono h,
   fun h => by simpa [Allegory.recip_recip] using recip_mono h⟩

/-- Composition preserves order in the second argument (Horn sentence, §2.11). -/
theorem comp_mono_left {a b c : 𝒜} {S T : b ⟶ c} (R : a ⟶ b) (hST : S ⊑ T) : R ≫ S ⊑ R ≫ T := by
  dsimp [le] at hST ⊢
  have h := Allegory.semidistrib R S T
  -- h: R ≫ (S ∩ T) = (R ≫ S ∩ R ≫ (S ∩ T)) ∩ R ≫ T
  -- hST: S ∩ T = S
  calc
    (R ≫ S) ∩ (R ≫ T) = (R ≫ (S ∩ T)) ∩ (R ≫ T) := by rw [hST]
    _ = R ≫ (S ∩ T) := by
      rw [h]
      -- (R ≫ S ∩ R ≫ (S ∩ T)) ∩ R ≫ T ∩ R ≫ T = (R ≫ S ∩ R ≫ (S ∩ T)) ∩ R ≫ T
      -- by idempotence of ∩ on (R ≫ T)
      rw [← Allegory.inter_assoc, Allegory.inter_idem, h]
    _ = R ≫ S := by rw [hST]

/-- Composition preserves order in the first argument. -/
theorem comp_mono_right {a b c : 𝒜} {R₁ R₂ : a ⟶ b} (h : R₁ ⊑ R₂) (S : b ⟶ c) : R₁ ≫ S ⊑ R₂ ≫ S := by
  have h_recip : R₁° ⊑ R₂° := recip_mono h
  have h_comp : S° ≫ R₁° ⊑ S° ≫ R₂° := comp_mono_left S° h_recip
  -- (R₁ ≫ S)°° = R₁ ≫ S, similarly for R₂
  -- (R₁ ≫ S)° = S° ≫ R₁°, similarly for R₂
  -- So: R₁ ≫ S = (S° ≫ R₁°)° ⊑ (S° ≫ R₂°)° = R₂ ≫ S
  have h_eq1 : R₁ ≫ S = (S° ≫ R₁°)° := by
    rw [← Allegory.recip_recip (R₁ ≫ S), Allegory.recip_comp R₁ S]
  have h_eq2 : R₂ ≫ S = (S° ≫ R₂°)° := by
    rw [← Allegory.recip_recip (R₂ ≫ S), Allegory.recip_comp R₂ S]
  rw [h_eq1, h_eq2]
  exact recip_mono h_comp

/-! ### The modular law in its order form -/

/-- The modular law in order form: RS ∩ T ⊑ (R ∩ TS°)S (§2.11). -/
theorem modular_le {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) :
    (R ≫ S) ∩ T ⊑ (R ∩ T ≫ S°) ≫ S := by
  dsimp [le]
  rw [Allegory.modular R S T, ← Allegory.inter_assoc, Allegory.inter_idem]

/-! ## §2.12  Reflexive, symmetric, transitive, coreflexive -/

/-- R is REFLEXIVE if 1 ⊑ R (§2.12). -/
def Reflexive {a : 𝒜} (R : a ⟶ a) : Prop := Cat.id a ⊑ R

/-- R is SYMMETRIC if R° ⊑ R (§2.12).  Equivalent to R = R°. -/
def Symmetric {a : 𝒜} (R : a ⟶ a) : Prop := R° ⊑ R

/-- R is TRANSITIVE if RR ⊑ R (§2.12). -/
def Transitive {a : 𝒜} (R : a ⟶ a) : Prop := R ≫ R ⊑ R

/-- R is COREFLEXIVE if R ⊑ 1 (§2.12). -/
def Coreflexive {a : 𝒜} (R : a ⟶ a) : Prop := R ⊑ Cat.id a

/-! ### Symmetric iff R = R° -/

theorem symmetric_eq {a : 𝒜} {R : a ⟶ a} (hSym : Symmetric R) : R° = R :=
  le_antisymm hSym <| by
    calc
      R = (R°)° := by rw [Allegory.recip_recip]
      _ ⊑ R° := recip_mono hSym

theorem symmetric_iff {a : 𝒜} (R : a ⟶ a) : Symmetric R ↔ R° = R := by
  constructor
  · exact symmetric_eq
  · intro h; dsimp [Symmetric, le]; rw [h, Allegory.inter_idem]

/-- Reflexive and transitive imply idempotent (§2.12). -/
theorem reflexive_transitive_idempotent {a : 𝒜} {R : a ⟶ a}
    (hR : Reflexive R) (hT : Transitive R) : R ≫ R = R := by
  apply le_antisymm hT
  dsimp [Reflexive, le] at hR
  calc
    R = (Cat.id a) ≫ R := by rw [Cat.id_comp]
    _ ⊑ R ≫ R := comp_mono_right hR R

/-! ### Identity is self-reciprocal -/

/-- 1° = 1: derived from `recip_comp` and `recip_recip` (§2.11). -/
theorem recip_id {a : 𝒜} : (Cat.id a)° = Cat.id a := by
  calc
    (Cat.id a)° = ((Cat.id a)°)°° := by rw [Allegory.recip_recip]
    _ = ((Cat.id a ≫ (Cat.id a)°)°)° := by rw [Cat.id_comp]
    _ = (((Cat.id a)°)° ≫ (Cat.id a)°)° := by rw [Allegory.recip_comp]
    _ = (Cat.id a ≫ (Cat.id a)°)° := by rw [Allegory.recip_recip]
    _ = ((Cat.id a)°)° := by rw [Cat.id_comp]
    _ = Cat.id a := by rw [Allegory.recip_recip]

/-! ### Coreflexive properties -/

/-- Coreflexive implies symmetric idempotent (§2.12).
    Proof chain: R ⊑ RR°R (modular law) ⊑ R° (since R ⊑ 1), so R ⊑ R°.
    Taking ° gives R° ⊑ R, hence symmetric.  Idempotent: R = R° gives
    R ⊑ R²R ⊑ R² (from modular law + R⊑1) and R² ⊑ 1R = R. -/
theorem coreflexive_symmetric_idempotent {a : 𝒜} {R : a ⟶ a} (h : Coreflexive R) :
    Symmetric R ∧ R ≫ R = R := by
  -- h: R ⊑ 1
  have h_le_one : R ⊑ Cat.id a := h
  -- Step 1: R ⊑ RR°R via modular law
  have hR_le_RRrecipR : R ⊑ (R ≫ R°) ≫ R := by
    have h_mod := modular_le (Cat.id a) R R
    -- h_mod: (1≫R)∩R ⊑ (1 ∩ RR°)≫R, simplify using id_comp, inter_idem
    have h1 : R ⊑ (Cat.id a ∩ R ≫ R°) ≫ R := by
      simpa [Cat.id_comp, Allegory.inter_idem] using h_mod
    -- (1∩RR°) ⊑ RR°, so (1∩RR°)R ⊑ RR°R by comp_mono_right
    have h2 : (Cat.id a ∩ R ≫ R°) ≫ R ⊑ (R ≫ R°) ≫ R :=
      comp_mono_right (inter_lb_right (Cat.id a) (R ≫ R°)) R
    exact le_trans h1 h2
  -- Step 2: RR°R ⊑ R° (using R ⊑ 1)
  have hRRrecipR_le_Rrecip : (R ≫ R°) ≫ R ⊑ R° := by
    -- R ⊑ 1 ⇒ RR° ⊑ 1R° (comp_mono_right R°)
    have h_RRrecip_le_1Rrecip : R ≫ R° ⊑ (Cat.id a) ≫ R° := comp_mono_right h_le_one R°
    -- RR°R ⊑ (1R°)R
    have h1 : (R ≫ R°) ≫ R ⊑ ((Cat.id a) ≫ R°) ≫ R :=
      comp_mono_right h_RRrecip_le_1Rrecip R
    -- (1R°)R = 1(R°R) ⊑ 1(R°1) = 1R° = R° (since R ⊑ 1)
    have h2 : ((Cat.id a) ≫ R°) ≫ R ⊑ R° := by
      calc
        ((Cat.id a) ≫ R°) ≫ R = (Cat.id a) ≫ (R° ≫ R) := by rw [Cat.assoc]
        _ ⊑ (Cat.id a) ≫ (R° ≫ Cat.id a) :=
          comp_mono_left (Cat.id a) (comp_mono_left R° h_le_one)
        _ = (Cat.id a) ≫ R° := by rw [Cat.comp_id]
        _ = R° := by rw [Cat.id_comp]
    exact le_trans h1 h2
  -- Step 3: R ⊑ R°, hence symmetric
  have h_symm : Symmetric R := by
    have hR_le_Rrecip : R ⊑ R° := le_trans hR_le_RRrecipR hRRrecipR_le_Rrecip
    -- Apply recip_mono: R° ⊑ R°° = R
    have hRrecip_le_R : R° ⊑ R := recip_le_iff.mpr hR_le_Rrecip
    exact hRrecip_le_R
  -- Step 4: Idempotent R² = R
  have h_idem : R ≫ R = R := by
    -- From symmetry: R° = R
    have h_eq : R° = R := symmetric_eq h_symm
    -- R ⊑ R²R (from step 1, substituting R°=R)
    have hR_le_RR_R : R ⊑ (R ≫ R) ≫ R := by
      simpa [h_eq] using hR_le_RRrecipR
    -- R²R ⊑ R² (since R ⊑ 1)
    have hRRR_le_RR : (R ≫ R) ≫ R ⊑ R ≫ R := by
      calc
        (R ≫ R) ≫ R = R ≫ (R ≫ R) := by rw [Cat.assoc]
        _ ⊑ R ≫ (R ≫ Cat.id a) := comp_mono_left R (comp_mono_left R h_le_one)
        _ = R ≫ R := by rw [Cat.comp_id]
    -- So R ⊑ R²
    have hR_le_RR : R ⊑ R ≫ R := le_trans hR_le_RR_R hRRR_le_RR
    -- R² ⊑ R (since R ⊑ 1)
    have hRR_le_R : R ≫ R ⊑ R := by
      calc
        R ≫ R ⊑ (Cat.id a) ≫ R := comp_mono_right h_le_one R
        _ = R := by rw [Cat.id_comp]
    exact le_antisymm hRR_le_R hR_le_RR
  exact ⟨h_symm, h_idem⟩

/-! ## §2.121  Coreflexive composition

  For coreflexive morphisms, AB = A ∩ B (§2.121). -/
theorem coreflexive_comp_eq_inter {a : 𝒜} {A B : a ⟶ a} (hA : Coreflexive A) (hB : Coreflexive B) :
    A ≫ B = A ∩ B := by
  -- A∩B is also coreflexive (it's below A which is below 1)
  have h_inter_coref : Coreflexive (A ∩ B) := by
    dsimp [Coreflexive]
    -- A∩B ⊑ A ⊑ 1, so A∩B ⊑ 1 by transitivity (but we need the equation: (A∩B)∩1 = A∩B)
    -- Actually A∩B ⊑ 1 because inter_lb_left gives A∩B ⊑ A and hA: A ⊑ 1
    apply le_trans (inter_lb_left A B) hA
  -- A∩B is idempotent by the previous theorem
  have h_inter_idem : (A ∩ B) ≫ (A ∩ B) = A ∩ B :=
    (coreflexive_symmetric_idempotent h_inter_coref).2
  apply le_antisymm
  · -- AB ⊑ A∩B: AB ⊑ A (since B⊑1) and AB ⊑ B (since A⊑1)
    -- AB ⊑ A: B ⊑ 1 ⇒ A≫B ⊑ A≫1 = A
    have h_AB_le_A : A ≫ B ⊑ A :=
      le_trans (comp_mono_left A hB) (by rw [Cat.comp_id]; exact le_refl A)
    have h_AB_le_B : A ≫ B ⊑ B :=
      le_trans (comp_mono_right hA B) (by rw [Cat.id_comp]; exact le_refl B)
    exact le_inter h_AB_le_A h_AB_le_B
  · -- A∩B ⊑ AB: A∩B = (A∩B)(A∩B) ⊑ AB
    have h1 : A ∩ B ⊑ A ≫ (A ∩ B) := by
      simpa [h_inter_idem] using comp_mono_right (inter_lb_left A B) (A ∩ B)
    have h2 : A ≫ (A ∩ B) ⊑ A ≫ B := comp_mono_left A (inter_lb_right A B)
    exact le_trans h1 h2
    -- Note: inter_lb_left A B: A∩B ⊑ A.  inter_lb_right A B: A∩B ⊑ B.

/-! ## §2.122  Domain -/

/-- The DOMAIN of R, denoted %mR in the book: 1 ∩ RR° (§2.122). -/
def dom {a b : 𝒜} (R : a ⟶ b) : a ⟶ a := Cat.id a ∩ R ≫ R°

/-- Domain is coreflexive (§2.122). -/
theorem dom_coreflexive {a b : 𝒜} (R : a ⟶ b) : Coreflexive (dom R) :=
  inter_lb_left (Cat.id a) (R ≫ R°)

/-- dom is symmetric: (dom R)° = dom R. -/
theorem dom_recip {a b : 𝒜} (R : a ⟶ b) : (dom R)° = dom R :=
  symmetric_eq (coreflexive_symmetric_idempotent (dom_coreflexive R)).1

/-! ## §2.124  Domain of intersection -/

/-- dom(R ∩ S) = 1 ∩ SR° (§2.124).
    Proof uses modular law: 1 ∩ (R∩S)(R∩S)° ⊑ 1 ∩ RS°, and
    1 ∩ SR° ⊑ 1 ∩ (R∩S)(R∩S)°. -/
theorem dom_inter {a b : 𝒜} (R S : a ⟶ b) : dom (R ∩ S) = Cat.id a ∩ S ≫ R° := by
  apply le_antisymm
  · -- dom(R∩S) ⊑ 1 ∩ S R°
    dsimp [dom]
    rw [Allegory.recip_inter]
    have h : (R ∩ S) ≫ (R° ∩ S°) ⊑ S ≫ R° := by
      refine le_trans (comp_mono_right (inter_lb_right R S) (R° ∩ S°)) ?_
      exact comp_mono_left S (inter_lb_left R° S°)
    apply le_inter
    · exact inter_lb_left _ _
    · exact le_trans (inter_lb_right _ _) h
  · -- 1 ∩ S R° ⊑ dom(R∩S)
    dsimp [dom]
    rw [Allegory.recip_inter]
    -- Goal: 1 ∩ S R° ⊑ 1 ∩ (R∩S)(R°∩S°)
    -- Step 1: 1 ∩ S R° = 1 ∩ (R∩S) R°
    have h_eq1 : Cat.id a ∩ S ≫ R° = Cat.id a ∩ ((R ∩ S) ≫ R°) := by
      apply le_antisymm
      · -- 1 ∩ S R° ⊑ 1 ∩ (R∩S) R° via modular law
        have h_m : Cat.id a ∩ S ≫ R° ⊑ (R ∩ S) ≫ R° := by
          calc
            Cat.id a ∩ S ≫ R° = (S ≫ R°) ∩ Cat.id a := by rw [Allegory.inter_comm]
            _ ⊑ (S ∩ (Cat.id a ≫ R)) ≫ R° := by
              have h := modular_le S R° (Cat.id a)
              rw [Allegory.recip_recip] at h
              exact h
            _ = (S ∩ R) ≫ R° := by rw [Cat.id_comp]
            _ = (R ∩ S) ≫ R° := by rw [Allegory.inter_comm S R]
        apply le_inter (inter_lb_left _ _) h_m
      · -- 1 ∩ (R∩S) R° ⊑ 1 ∩ S R° by monotonicity (R∩S ⊑ S)
        have h : (R ∩ S) ≫ R° ⊑ S ≫ R° := comp_mono_right (inter_lb_right R S) R°
        exact le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) h)
    rw [h_eq1]
    -- Step 2: 1 ∩ (R∩S) R° = 1 ∩ R (R°∩S°)  (via recip symmetry of coreflexives)
    have h_eq2 : Cat.id a ∩ ((R ∩ S) ≫ R°) = Cat.id a ∩ (R ≫ (R° ∩ S°)) := by
      have h_coref : Coreflexive (Cat.id a ∩ (R ≫ (R° ∩ S°))) :=
        inter_lb_left _ _
      have h_symm : Symmetric (Cat.id a ∩ (R ≫ (R° ∩ S°))) :=
        (coreflexive_symmetric_idempotent h_coref).1
      have h_self_recip : (Cat.id a ∩ (R ≫ (R° ∩ S°)))° = Cat.id a ∩ (R ≫ (R° ∩ S°)) :=
        symmetric_eq h_symm
      -- LHS° = RHS (computed via recip_inter, recip_comp, recip_recip)
      -- So LHS = LHS°° = RHS° = RHS (by symmetry of coreflexive RHS)
      have h_recip_eq : (Cat.id a ∩ ((R ∩ S) ≫ R°))° = Cat.id a ∩ (R ≫ (R° ∩ S°)) := by
        simp [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip, recip_id]
      calc
        Cat.id a ∩ ((R ∩ S) ≫ R°) = (Cat.id a ∩ ((R ∩ S) ≫ R°))°° := by
          simp [Allegory.recip_recip]
        _ = (Cat.id a ∩ (R ≫ (R° ∩ S°)))° := by rw [h_recip_eq]
        _ = Cat.id a ∩ (R ≫ (R° ∩ S°)) := h_self_recip
    rw [h_eq2]
    -- Step 3: 1 ∩ R (R°∩S°) ⊑ (R∩S)(R°∩S°) via modular law
    have h_m2 : Cat.id a ∩ (R ≫ (R° ∩ S°)) ⊑ (R ∩ S) ≫ (R° ∩ S°) := by
      calc
        Cat.id a ∩ (R ≫ (R° ∩ S°)) = (R ≫ (R° ∩ S°)) ∩ Cat.id a := by rw [Allegory.inter_comm]
        _ ⊑ (R ∩ (Cat.id a ≫ ((R° ∩ S°)°))) ≫ (R° ∩ S°) :=
          modular_le R (R° ∩ S°) (Cat.id a)
        _ = (R ∩ (R ∩ S)) ≫ (R° ∩ S°) := by
          simp [Allegory.recip_inter, Allegory.recip_recip, Cat.id_comp]
        _ = (R ∩ S) ≫ (R° ∩ S°) := by
          rw [Allegory.inter_assoc, Allegory.inter_idem]
    -- Combine: 1 ∩ S R° = ... ⊑ (R∩S)(R°∩S°), and also ⊑ 1
    apply le_inter (inter_lb_left _ _) h_m2

/-! ## §2.13  Entire, simple, map

  R : a → b is entire if dom R = 1_a.
  R is simple if R°R ⊑ 1_b (note: target b, since R°R : b → b).
  R is a map if it is entire and simple.  §2.13. -/

/-- R is ENTIRE if dom R = 1_a; equivalently 1_a ⊑ RR° (§2.13). -/
def Entire {a b : 𝒜} (R : a ⟶ b) : Prop := dom R = Cat.id a

/-- An entire morphism satisfies the equivalent inequality `1 ⊑ R ≫ R°` (§2.13). -/
theorem entire_id_le {a b : 𝒜} {R : a ⟶ b} (hR : Entire R) : 𝟙 a ⊑ R ≫ R° := by
  rw [← hR]
  exact inter_lb_right _ _

/-- R is SIMPLE if R°R ⊑ 1_b (§2.13).
    Note: R°R : b → b, so we compare to id_b. -/
def Simple {a b : 𝒜} (R : a ⟶ b) : Prop := R° ≫ R ⊑ Cat.id b

/-- R is a MAP if it is entire and simple (§2.13). -/
def Map {a b : 𝒜} (R : a ⟶ b) : Prop := Entire R ∧ Simple R

/-! ## §2.133  Order on maps is discrete -/

theorem map_order_discrete {a b : 𝒜} {f g : a ⟶ b} (hf : Map f) (hg : Map g) (h : f ⊑ g) : f = g := by
  rcases hf with ⟨hf_entire, hf_simple⟩
  rcases hg with ⟨hg_entire, hg_simple⟩
  -- Entire means dom = 1, so 1 = 1 ∩ f f°
  have h_one_f_eq : Cat.id a ∩ (f ≫ f°) = Cat.id a := by
    dsimp [Entire, dom] at hf_entire; exact hf_entire
  -- From f ⊑ g we have f° ⊑ g°
  have h_recip : f° ⊑ g° := recip_mono h
  -- Show g ⊑ f
  have h_g_le_f : g ⊑ f := by
    -- g = (1 ∩ f f°) g ⊑ (f f°) g = f (f° g) ⊑ f (g° g) ⊑ f 1 = f
    have h1 : g = (Cat.id a ∩ (f ≫ f°)) ≫ g := by rw [h_one_f_eq, Cat.id_comp]
    have h2 : (Cat.id a ∩ (f ≫ f°)) ≫ g ⊑ f := by
      have h2a : (Cat.id a ∩ (f ≫ f°)) ≫ g ⊑ (f ≫ f°) ≫ g :=
        comp_mono_right (inter_lb_right (Cat.id a) (f ≫ f°)) g
      have h2b : (f ≫ f°) ≫ g ⊑ f := by
        rw [Cat.assoc]
        -- f (f° g) ⊑ f (g° g)
        have h_fog : f° ≫ g ⊑ g° ≫ g := comp_mono_right h_recip g
        have h_f_le : f ≫ (f° ≫ g) ⊑ f ≫ (g° ≫ g) := comp_mono_left f h_fog
        -- f (g° g) ⊑ f 1 = f
        simpa [Cat.comp_id] using le_trans h_f_le (comp_mono_left f hg_simple)
      exact le_trans h2a h2b
    rw [h1]; exact h2
  exact le_antisymm h h_g_le_f

/-! ## §2.134  Reciprocation on maps -/

theorem map_recip_is_inverse {a b : 𝒜} {f : a ⟶ b} (hf : Map f) (hfo : Map (f°)) :
    f ≫ f° = Cat.id a ∧ f° ≫ f = Cat.id b := by
  rcases hf with ⟨hf_entire, hf_simple⟩
  rcases hfo with ⟨hfo_entire, hfo_simple⟩
  -- Entire f: 1_a ∩ f f° = 1_a → 1_a ⊑ f f°
  have h_id_le_ff : Cat.id a ⊑ f ≫ f° := by
    dsimp [Entire, dom] at hf_entire
    dsimp [le]; rw [hf_entire]
  -- Simple (f°): (f°)° f° ⊑ 1_a, i.e., f f° ⊑ 1_a
  have h_ff_le_id : f ≫ f° ⊑ Cat.id a := by
    dsimp [Simple] at hfo_simple
    simpa [Allegory.recip_recip] using hfo_simple
  -- Entire (f°): 1_b ∩ f° (f°)° = 1_b → 1_b ⊑ f° f
  have h_id_le_ffr : Cat.id b ⊑ f° ≫ f := by
    dsimp [Entire, dom] at hfo_entire
    dsimp [le]
    simpa [Allegory.recip_recip] using hfo_entire
  -- Simple f: f° f ⊑ 1_b
  have h_ffr_le_id : f° ≫ f ⊑ Cat.id b := by
    dsimp [Simple] at hf_simple; exact hf_simple
  exact ⟨le_antisymm h_ff_le_id h_id_le_ff, le_antisymm h_ffr_le_id h_id_le_ffr⟩

-- §2.136: If F is simple then F(R ∩ S) = FR ∩ FS.  (Stated here, ahead of §2.14, since
-- the §2.141 monic-pair proof uses it.)
theorem simple_dist_inter {a b c : 𝒜} {F : a ⟶ b} (hF : Simple F) (R S : b ⟶ c) :
    F ≫ (R ∩ S) = (F ≫ R) ∩ (F ≫ S) := by
  apply le_antisymm
  · exact le_inter (comp_mono_left F (inter_lb_left R S)) (comp_mono_left F (inter_lb_right R S))
  · have hgoal : ((F ≫ R) ∩ (F ≫ S))° ⊑ (F ≫ (R ∩ S))° := by
      rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp,
          Allegory.recip_comp, Allegory.recip_inter]
      refine le_trans (modular_le R° F° (S° ≫ F°)) ?_
      apply comp_mono_right
      apply le_inter (inter_lb_left _ _)
      refine le_trans (inter_lb_right _ _) ?_
      rw [Allegory.recip_recip, Cat.assoc]
      calc S° ≫ (F° ≫ F) ⊑ S° ≫ Cat.id b := comp_mono_left S° hF
        _ = S° := Cat.comp_id S°
    have := recip_mono hgoal
    rwa [Allegory.recip_recip, Allegory.recip_recip] at this

/-! ## §2.14  Tabulation

  A pair of maps f : c → a, g : c → b (common SOURCE / apex c) TABULATES
  R : a → b if f°g = R and ff° ∩ gg° = 1_c.  §2.14.

  (The legs are maps FROM the apex; this is Freyd's source-apex convention.) -/

/-- A pair of maps f : c → a, g : c → b (common apex c) TABULATES
    R : a → b if R = f° ≫ g and f ≫ f° ∩ g ≫ g° = id_c (§2.14). -/
def Tabulates {a b c : 𝒜} (f : c ⟶ a) (g : c ⟶ b) (R : a ⟶ b) : Prop :=
  Map f ∧ Map g ∧ R = f° ≫ g ∧ f ≫ f° ∩ g ≫ g° = Cat.id c

/-- R is TABULAR if it has a tabulation (§2.14). -/
def Tabular {a b : 𝒜} (R : a ⟶ b) : Prop :=
  ∃ (c : 𝒜) (f : c ⟶ a) (g : c ⟶ b), Tabulates f g R

/-- A TABULAR ALLEGORY is one where every morphism is tabular (§2.14). -/
class TabularAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  tabular {a b : 𝒜} (R : a ⟶ b) : Tabular R

/-! ## §2.141  Monic pair in Map(A)

  If f, g : a → c are maps and ff° ∩ gg° = 1, then (f, g) is a monic pair in Map(A):
  any maps h₁, h₂ : w → a with h₁f = h₂f and h₁g = h₂g are equal. -/

/-- **§2.141**: If ff° ∩ gg° = 1 for maps f, g : a → c, then (f, g) is a monic pair
    in Map(A).  For any maps h₁, h₂ : w → a, h₁f = h₂f ∧ h₁g = h₂g ⇒ h₁ = h₂.
    Book proof: h₁ = h₁(ff°∩gg°) = h₁ff° ∩ h₁gg° = h₂ff° ∩ h₂gg° = h₂(ff°∩gg°) = h₂. -/
theorem tabulates_monic_pair {w a c₁ c₂ : 𝒜} {f : a ⟶ c₁} {g : a ⟶ c₂}
    (_hf : Map f) (_hg : Map g)
    (h : f ≫ f° ∩ g ≫ g° = Cat.id a) :
    ∀ (h₁ h₂ : w ⟶ a), Map h₁ → Map h₂ → h₁ ≫ f = h₂ ≫ f → h₁ ≫ g = h₂ ≫ g → h₁ = h₂ := by
  intro h₁ h₂ h₁_map h₂_map hf_eq hg_eq
  -- h_i (ff° ∩ gg°) = (h_i f)f° ∩ (h_i g)g°  (simple distributes over ∩, §2.136).
  have hdist : ∀ (hₖ : w ⟶ a), Map hₖ →
      hₖ ≫ (f ≫ f° ∩ g ≫ g°) = (hₖ ≫ f) ≫ f° ∩ (hₖ ≫ g) ≫ g° := by
    intro hₖ hₖm
    rw [simple_dist_inter hₖm.2 (f ≫ f°) (g ≫ g°)]
    rw [← Cat.assoc, ← Cat.assoc]
  calc h₁ = h₁ ≫ (f ≫ f° ∩ g ≫ g°) := by rw [h, Cat.comp_id]
    _ = (h₁ ≫ f) ≫ f° ∩ (h₁ ≫ g) ≫ g° := hdist h₁ h₁_map
    _ = (h₂ ≫ f) ≫ f° ∩ (h₂ ≫ g) ≫ g° := by rw [hf_eq, hg_eq]
    _ = h₂ ≫ (f ≫ f° ∩ g ≫ g°) := (hdist h₂ h₂_map).symm
    _ = h₂ := by rw [h, Cat.comp_id]

/-! ## §2.15  Unit -/

/-- T is a PARTIAL UNIT if 1_T is the maximum endomorphism on T (§2.15). -/
def PartialUnit (T : 𝒜) : Prop := ∀ (R : T ⟶ T), R ⊑ Cat.id T

/-- T is a UNIT if it is a partial unit and every object is the source of
    an entire morphism to T (§2.15). -/
def IsUnit (T : 𝒜) : Prop :=
  PartialUnit T ∧ ∀ (a : 𝒜), ∃ (R : a ⟶ T), Entire R

/-- A UNITARY ALLEGORY has a unit (§2.15). -/
class UnitaryAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  unit_obj : 𝒜
  unit_prop : IsUnit unit_obj

/-! ## §2.16  Pre-tabular, effective, semi-simple -/

/-- A PRE-TABULAR allegory: every morphism is contained in a tabular one (§2.165). -/
class PreTabularAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  pre_tabular {a b : 𝒜} (R : a ⟶ b) : ∃ (S : a ⟶ b), R ⊑ S ∧ Tabular S

/-- An EFFECTIVE ALLEGORY: tabular + every EQUIVALENCE RELATION splits (§2.167, §2.169).
    Freyd §2.169: "An effective allegory is one in which all equivalence relations split."
    §2.163: an equivalence relation `E : a → a` (reflexive, symmetric, idempotent) is a split
    idempotent iff there is a map `f` with `f ≫ f° = E`, `f° ≫ f = id_c` — i.e. iff `E` is
    effective.  The leg can only be a MAP (entire) when `E` is REFLEXIVE: a non-reflexive
    symmetric idempotent splits with a partial-map leg, never an entire one (`dom f = E ≠ id`).
    Hence the field is stated for equivalence relations, as the book has it. -/
class EffectiveAllegory (𝒜 : Type u) extends TabularAllegory 𝒜 where
  split_symmetric_idempotent {a : 𝒜} (E : a ⟶ a) :
    Reflexive E → Symmetric E → E ≫ E = E →
      ∃ (c : 𝒜) (f : a ⟶ c), Map f ∧ f ≫ f° = E ∧ f° ≫ f = Cat.id c

/-- A SEMI-SIMPLE morphism factors as F° ≫ G with F, G simple (§2.16(10)).
    F : c → a, G : c → b have a common source (apex) c, so F° ≫ G : a → b — exactly
    the form `R = F°G` of a tabulation (§2.143).  (Note: this is NOT the reciprocal
    `F ≫ G°`; simplicity is not preserved under reciprocation, so the apex must be the
    common *source*.) -/
def SemiSimple {a b : 𝒜} (R : a ⟶ b) : Prop :=
  ∃ (c : 𝒜) (F : c ⟶ a) (G : c ⟶ b), Simple F ∧ Simple G ∧ R = F° ≫ G

/-- A SEMI-SIMPLE ALLEGORY: every morphism is semi-simple (§2.16(10)). -/
class SemiSimpleAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  semi_simple {a b : 𝒜} (R : a ⟶ b) : SemiSimple R

/-- **§2.16(10)**: every TABULAR allegory is SEMI-SIMPLE.  A tabulation `R = f°≫g` with
    `f, g` MAPS (entire+simple) is in particular a semi-simple factoring `F°≫G` with
    `F = f`, `G = g` simple — semi-simplicity drops the entireness, keeping only simplicity.
    (Fresh type variable `ℬ` avoids a diamond with the file-level `variable [Allegory 𝒜]`.) -/
theorem tabular_is_semiSimple {ℬ : Type u} [TabularAllegory ℬ] {a b : ℬ} (R : a ⟶ b) :
    SemiSimple R := by
  obtain ⟨c, f, g, hf, hg, hRfg, _⟩ := TabularAllegory.tabular R
  exact ⟨c, f, g, hf.2, hg.2, hRfg⟩

/-- **§2.16(10)**: a tabular allegory, viewed as a semi-simple allegory.  Provided as a `def`
    (not a global instance) to avoid surprising typeclass resolution; apply via `letI`. -/
def semiSimpleAllegory_of_tabular {ℬ : Type u} [TabularAllegory ℬ] : SemiSimpleAllegory ℬ where
  toAllegory := (inferInstance : TabularAllegory ℬ).toAllegory
  semi_simple := tabular_is_semiSimple

/-! ## Missing propositions from §2.12–§2.16(13) -/

-- §2.12: Symmetric and transitive imply idempotent.
-- Already formalized as `symmetric_transitive_idempotent` in S2_22.lean (UnionAllegory).

/-\! ### §2.122 Domain characterization and §2.123 -/

/-- §2.122 helper: R ⊑ dom R ≫ R always.
    modular_le 1 R R: (1≫R)∩R ⊑ (1∩RR°)≫R = dom(R)≫R, and LHS = R∩R = R. -/
theorem le_dom_comp {a b : 𝒜} (R : a ⟶ b) : R ⊑ dom R ≫ R := by
  have h := modular_le (Cat.id a) R R
  simp only [Cat.id_comp, Allegory.inter_idem] at h
  exact h

/-- §2.123: dom (R ≫ S) ⊑ dom R.
    Apply modular_le (R≫S≫S°, R°, dom(R≫S)):
    LHS = (RS)(RS)°∩dom(RS) = dom(RS) (since dom(RS)⊑(RS)(RS)°);
    RHS ⊑ R≫R° (since RSS°∩dom(RS)≫R ⊑ dom(RS)≫R ⊑ R). -/
theorem dom_comp_le {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    dom (R ≫ S) ⊑ dom R := by
  -- Expand (RS)(RS)° = R≫S≫S°≫R°.
  have hexp : (R ≫ S) ≫ (R ≫ S)° = R ≫ S ≫ S° ≫ R° := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  -- dom(RS) ⊑ (RS)(RS)° = RSS°R°.
  have hd_le : dom (R ≫ S) ⊑ (R ≫ S) ≫ (R ≫ S)° := inter_lb_right _ _
  -- Apply modular_le (R≫S≫S°) R° (dom(R≫S)).
  have h_mod := modular_le (R ≫ S ≫ S°) R° (dom (R ≫ S))
  -- Rewrite LHS of modular conclusion: (RSS°)≫R° = (RS)(RS)°.
  have hLHS_eq : (R ≫ S ≫ S°) ≫ R° = (R ≫ S) ≫ (R ≫ S)° := by
    rw [hexp]; simp [Cat.assoc]
  -- (RS)(RS)°∩dom(RS) = dom(RS).
  have hLHS : (R ≫ S ≫ S°) ≫ R° ∩ dom (R ≫ S) = dom (R ≫ S) := by
    rw [hLHS_eq, Allegory.inter_comm]
    exact inter_eq_left hd_le
  -- dom(RS) ⊑ (RSS°∩dom(RS)≫R)≫R°.
  -- modular_le leaves R°° unsimplified; fix with recip_recip, then use hLHS to get dom(RS).
  have h_mod_simp : (R ≫ S ≫ S°) ≫ R° ∩ dom (R ≫ S)
      ⊑ (R ≫ S ≫ S° ∩ dom (R ≫ S) ≫ R) ≫ R° := by
    rwa [Allegory.recip_recip] at h_mod
  -- dom(RS) = (RSS°R°)∩dom(RS) (by hLHS.symm), so dom(RS) ⊑ (via h_mod_simp).
  have h1 : dom (R ≫ S) ⊑ (R ≫ S ≫ S° ∩ dom (R ≫ S) ≫ R) ≫ R° := by
    have := hLHS ▸ h_mod_simp
    exact this
  -- dom(RS)≫R ⊑ R (dom(RS) coreflexive).
  have h2 : dom (R ≫ S) ≫ R ⊑ R := by
    calc dom (R ≫ S) ≫ R ⊑ Cat.id a ≫ R := comp_mono_right (dom_coreflexive _) R
      _ = R := Cat.id_comp _
  -- RSS°∩dom(RS)≫R ⊑ dom(RS)≫R ⊑ R.
  have h3 : R ≫ S ≫ S° ∩ dom (R ≫ S) ≫ R ⊑ R :=
    le_trans (inter_lb_right _ _) h2
  -- dom(RS) ⊑ R≫R° and dom(RS) ⊑ 1.
  exact le_inter (dom_coreflexive _) (le_trans h1 (comp_mono_right h3 R°))

-- §2.131: R and S entire/simple/maps implies RS is entire/simple/a map;
-- RS entire implies R entire.
-- §2.131: simples compose — already formalized as `simple_comp` in S2_4.lean.

theorem entire_comp {a b c : 𝒜} {R : a ⟶ b} {S : b ⟶ c} (hR : Entire R) (hS : Entire S) :
    Entire (R ≫ S) := by
  -- 1 ⊑ RR°; 1 ⊑ SS°.  Then 1 ⊑ RR° = R·1·R° ⊑ R(SS°)R° = (RS)(RS)°.
  have hfe : Cat.id a ⊑ R ≫ R° := by
    dsimp [Entire, dom] at hR; rw [← hR]; exact inter_lb_right _ _
  have hge : Cat.id b ⊑ S ≫ S° := by
    dsimp [Entire, dom] at hS; rw [← hS]; exact inter_lb_right _ _
  have hstep : R ≫ R° ⊑ R ≫ (S ≫ S°) ≫ R° := by
    calc R ≫ R° = R ≫ Cat.id b ≫ R° := by rw [Cat.id_comp]
      _ ⊑ R ≫ (S ≫ S°) ≫ R° := comp_mono_left R (comp_mono_right hge R°)
  have heq : R ≫ (S ≫ S°) ≫ R° = (R ≫ S) ≫ (R ≫ S)° := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  dsimp [Entire, dom]
  exact le_antisymm (inter_lb_left _ _)
    (le_inter (le_refl _) (heq ▸ le_trans hfe hstep))

/-- §2.131: simples compose.  `(fg)°(fg) = g°(f°f)g ⊑ g°g ⊑ 1`. -/
theorem simple_comp {a b c : 𝒜} {f : a ⟶ b} {g : b ⟶ c} (hf : Simple f) (hg : Simple g) :
    Simple (f ≫ g) := by
  dsimp [Simple] at hf hg ⊢
  rw [Allegory.recip_comp]
  have hrw : (g° ≫ f°) ≫ (f ≫ g) = g° ≫ (f° ≫ f) ≫ g := by simp [Cat.assoc]
  rw [hrw]
  have h1 : g° ≫ (f° ≫ f) ≫ g ⊑ g° ≫ g := by
    calc g° ≫ (f° ≫ f) ≫ g ⊑ g° ≫ Cat.id b ≫ g := comp_mono_left _ (comp_mono_right hf _)
      _ = g° ≫ g := by rw [Cat.id_comp]
  exact le_trans h1 hg

/-- §2.131: composition of maps is a map. -/
theorem map_comp {a b c : 𝒜} {f : a ⟶ b} {g : b ⟶ c} (hf : Map f) (hg : Map g) :
    Map (f ≫ g) :=
  ⟨entire_comp hf.1 hg.1, simple_comp hf.2 hg.2⟩

theorem entire_of_comp_entire {a b c : 𝒜} {R : a ⟶ b} {S : b ⟶ c} (h : Entire (R ≫ S)) :
    Entire R := by
  -- 1 ⊑ (RS)(RS)° = R(SS°)R°.
  -- modular_le (RSS°) R° 1: (RSS°·R°) ∩ 1 ⊑ (RSS° ∩ R)·R° ⊑ R·R°.
  have h_one_le : Cat.id a ⊑ (R ≫ S) ≫ (R ≫ S)° := by
    dsimp [Entire, dom] at h; rw [← h]; exact inter_lb_right _ _
  have heq : (R ≫ S) ≫ (R ≫ S)° = R ≫ S ≫ S° ≫ R° := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  have h_rss_r : Cat.id a ⊑ R ≫ S ≫ S° ≫ R° := heq ▸ h_one_le
  -- h_mod: ((RSS°)≫R°) ∩ 1 ⊑ ((RSS°) ∩ R)≫R°
  have h_mod := modular_le (R ≫ S ≫ S°) R° (Cat.id a)
  simp only [Cat.id_comp, Allegory.recip_recip] at h_mod
  -- LHS of h_mod is (RSS°)·R° ∩ 1; match to R(SS°R°) using associativity
  have hrw : (R ≫ S ≫ S°) ≫ R° = R ≫ S ≫ S° ≫ R° := by simp [Cat.assoc]
  -- h_rss_r gives 1 ⊑ (RSS°)R°; combine with 1 ⊑ 1 to get 1 ⊑ (RSS°)R° ∩ 1
  have h_in : Cat.id a ⊑ (R ≫ S ≫ S°) ≫ R° ∩ Cat.id a :=
    le_inter (hrw ▸ h_rss_r) (le_refl _)
  -- Apply h_mod: 1 ⊑ (RSS° ∩ R)·R°
  have h3 : Cat.id a ⊑ (R ≫ S ≫ S° ∩ R) ≫ R° := le_trans h_in h_mod
  -- RSS° ∩ R ⊑ R
  have h_one_le_rr : Cat.id a ⊑ R ≫ R° :=
    le_trans h3 (comp_mono_right (inter_lb_right _ _) R°)
  dsimp [Entire, dom]
  exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) h_one_le_rr)

-- §2.135: If R is an isomorphism (§1.41 IsIso) then R is a map and R⁻¹ = R°.
theorem iso_is_map {a b : 𝒜} {R : a ⟶ b} (hR : Freyd.IsIso R) : Map R := by
  obtain ⟨g, h1, h2⟩ := hR
  -- h1 : R ≫ g = id_a, h2 : g ≫ R = id_b.
  -- g°≫R° = (R≫g)° = id_a.
  have hg_recip : g° ≫ R° = Cat.id a := by
    rw [← Allegory.recip_comp, h1, recip_id]
  -- R°≫g° = (g≫R)° = id_b.
  have hR_recip : R° ≫ g° = Cat.id b := by
    rw [← Allegory.recip_comp, h2, recip_id]
  -- id_a ⊑ g°≫g.  modular_le R g id_a, R≫g = id_a: id_a ⊑ (R∩g°)≫g ⊑ g°≫g.
  have h_id_g : Cat.id a ⊑ g° ≫ g := by
    have h_mod := modular_le R g (Cat.id a)
    rw [Cat.id_comp, h1, Allegory.inter_idem] at h_mod
    -- h_mod : Cat.id a ⊑ (R ∩ g°) ≫ g  (recip_recip already applied g°° → g)
    exact le_trans h_mod (comp_mono_right (inter_lb_right _ _) g)
  -- Entire: id_a ⊑ R≫R°.  modular_le g° R° id_a, g°≫R° = id_a: id_a ⊑ (g°∩R°°)≫R° = (g°∩R)≫R° ⊑ R≫R°.
  have h_entire : Entire R := by
    have h_mod := modular_le g° R° (Cat.id a)
    rw [Cat.id_comp, hg_recip, Allegory.inter_idem, Allegory.recip_recip] at h_mod
    -- h_mod : Cat.id a ⊑ (g° ∩ R) ≫ R°
    dsimp [Entire, dom]
    exact le_antisymm (inter_lb_left _ _)
      (le_inter (le_refl _) (le_trans h_mod (comp_mono_right (inter_lb_right _ _) R°)))
  -- Simple: R°≫R ⊑ id_b.  Chain: R°≫R ⊑ R°≫(g°≫g)≫R = (R°≫g°)≫(g≫R) = id_b≫id_b = id_b.
  have h_simple : Simple R := by
    dsimp [Simple]
    calc R° ≫ R
        ⊑ R° ≫ (g° ≫ g) ≫ R := by
          have h := comp_mono_left R° (comp_mono_right h_id_g R)
          rwa [Cat.id_comp] at h
      _ = (R° ≫ g°) ≫ (g ≫ R) := by simp [Cat.assoc]
      _ = Cat.id b ≫ Cat.id b := by rw [hR_recip, h2]
      _ = Cat.id b := Cat.id_comp _
  exact ⟨h_entire, h_simple⟩

-- §2.135: The inverse of an iso equals its reciprocal.
-- If Rinv is the inverse of iso R (i.e. R ≫ Rinv = 1 ∧ Rinv ≫ R = 1), then Rinv = R°.
theorem iso_inv_eq_recip {a b : 𝒜} {R : a ⟶ b} (hR : Freyd.IsIso R)
    {Rinv : b ⟶ a} (h1 : R ≫ Rinv = Cat.id a) (h2 : Rinv ≫ R = Cat.id b) :
    Rinv = R° := by
  -- R°≫R = id_b (Simple R already proved; need equality, not just ⊑).
  -- id_b ⊑ R°≫R by modular_le Rinv R id_b with Rinv≫R = id_b.
  -- R°≫R ⊑ id_b (Simple R from iso_is_map).
  have hR_map := iso_is_map hR
  have h_simple : R° ≫ R ⊑ Cat.id b := hR_map.2
  -- id_b ⊑ R°≫R from modular_le with h2 (Rinv≫R = id_b):
  -- modular_le Rinv R id_b: (Rinv≫R)∩id_b ⊑ (Rinv∩R°)≫R. LHS=id_b⊑(Rinv∩R°)≫R⊑R°≫R.
  have h_refl : Cat.id b ⊑ R° ≫ R := by
    have h_mod := modular_le Rinv R (Cat.id b)
    rw [Cat.id_comp, h2, Allegory.inter_idem] at h_mod
    -- h_mod : Cat.id b ⊑ (Rinv ∩ R°) ≫ R
    exact le_trans h_mod (comp_mono_right (inter_lb_right _ _) R)
  -- R°≫R = id_b
  have h_RoR : R° ≫ R = Cat.id b := le_antisymm h_simple h_refl
  -- Rinv = id_b ≫ Rinv = (R°≫R) ≫ Rinv = R° ≫ (R ≫ Rinv) = R° ≫ id_a = R°.
  calc Rinv = Cat.id b ≫ Rinv := (Cat.id_comp _).symm
    _ = (R° ≫ R) ≫ Rinv := by rw [h_RoR]
    _ = R° ≫ (R ≫ Rinv) := Cat.assoc _ _ _
    _ = R° ≫ Cat.id a := by rw [h1]
    _ = R° := Cat.comp_id _

-- §2.136: `simple_dist_inter` is proved before §2.14 (it is used by §2.141).

/-- `Cat.id` is a map (entire + simple). -/
theorem id_is_map_local (a : 𝒜) : Map (Cat.id a) :=
  ⟨by simp [Entire, dom, recip_id, Cat.comp_id, Allegory.inter_idem],
   by simp only [Simple, recip_id, Cat.id_comp]; exact le_refl _⟩

/-! ## §2.143  Universal property of tabulation

  If `f, g` tabulates `R` then `x°y ⊑ R` iff there exists a (necessarily unique) map
  `h` with `x = hf`, `y = hg`.  In the source-apex convention `f : c→a`, `g : c→b`,
  `R = f°g`, the maps are `x : p→a`, `y : p→b` and `h : p→c`.  The mediating map is
  `H = xf° ∩ yg°` (book §2.143). -/

/-- §2.143 backward: if `h` is a map with `h≫f=x` and `h≫g=y`, then `x°≫y ⊑ R`.
    `x°y = (hf)°(hg) = f°(h°h)g ⊑ f°g = R`. -/
theorem tabulation_UP_backward {a b c p : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) {x : p ⟶ a} {y : p ⟶ b} {h : p ⟶ c}
    (hh : Map h) (hf_eq : h ≫ f = x) (hg_eq : h ≫ g = y) :
    x° ≫ y ⊑ R := by
  obtain ⟨_, _, hR, _⟩ := ht
  rw [hR, ← hf_eq, ← hg_eq, Allegory.recip_comp]
  simp only [Cat.assoc]
  -- Goal: f° ≫ h° ≫ h ≫ g ⊑ f° ≫ g
  apply comp_mono_left
  -- Goal: h° ≫ h ≫ g ⊑ g
  calc h° ≫ h ≫ g = (h° ≫ h) ≫ g := (Cat.assoc h° h g).symm
    _ ⊑ Cat.id _ ≫ g := comp_mono_right hh.2 g
    _ = g := Cat.id_comp g

/-- §2.143 entire: `H = x≫f° ∩ y≫g°` is entire when `x°y ⊑ R = f°g`.
    `1 ⊑ (xx°)(yy°) ⊑ x(x°y)y° ⊑ x f° g y° = (xf°)(yg°)° ⊑ dom H`. -/
private theorem tab_UP_H_entire {a b c p : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) {x : p ⟶ a} {y : p ⟶ b}
    (hx : Map x) (hy : Map y) (hxy : x° ≫ y ⊑ R) :
    Entire (x ≫ f° ∩ y ≫ g°) := by
  obtain ⟨_, _, hR, _⟩ := ht
  rw [hR] at hxy
  rw [Entire, Allegory.inter_comm (x ≫ f°) (y ≫ g°), dom_inter]
  apply le_antisymm (inter_lb_left _ _)
  apply le_inter (le_refl _)
  -- Goal: id_p ⊑ (x≫f°) ≫ (y≫g°)° = x≫f°≫g≫y°
  have hxx : Cat.id p ⊑ x ≫ x° := by
    have := hx.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hyy : Cat.id p ⊑ y ≫ y° := by
    have := hy.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have step1 : Cat.id p ⊑ (x ≫ x°) ≫ (y ≫ y°) :=
    le_trans hxx (by have h := comp_mono_left (x ≫ x°) hyy; rwa [Cat.comp_id] at h)
  have step2 : (x ≫ x°) ≫ (y ≫ y°) = x ≫ (x° ≫ y) ≫ y° := by simp [Cat.assoc]
  have step3 : x ≫ (x° ≫ y) ≫ y° ⊑ x ≫ (f° ≫ g) ≫ y° :=
    comp_mono_left x (comp_mono_right hxy y°)
  have step4 : x ≫ (f° ≫ g) ≫ y° = (x ≫ f°) ≫ (y ≫ g°)° := by
    rw [Allegory.recip_comp, Allegory.recip_recip]; simp [Cat.assoc]
  exact step4 ▸ le_trans step1 (step2.symm ▸ step3)

/-- §2.143 simple: `H = x≫f° ∩ y≫g°` is simple when `ff° ∩ gg° = id_c` — needs only `x, y`
    SIMPLE (not full maps): the entire/totality of `x, y` is only used to show `H` is entire
    (`tab_UP_H_entire`), never here.  Public: also the canonical "pairing of simples is
    simple" fact reused for `RelProd.pair` (`AOP.A5_2`, e.g. Prop 9.3's context rule). -/
theorem tabulation_simple_of_simple {a b c p : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) {x : p ⟶ a} {y : p ⟶ b}
    (hx : Simple x) (hy : Simple y) :
    Simple (x ≫ f° ∩ y ≫ g°) := by
  obtain ⟨_, _, _, htab⟩ := ht
  rw [Simple, show (x ≫ f° ∩ y ≫ g°)° = f ≫ x° ∩ g ≫ y° from by
        rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp,
            Allegory.recip_recip, Allegory.recip_recip]]
  -- Goal: (f x° ∩ g y°)(x f° ∩ y g°) ⊑ 1_c
  have step1 : (f ≫ x° ∩ g ≫ y°) ≫ (x ≫ f° ∩ y ≫ g°) ⊑
      (f ≫ x°) ≫ (x ≫ f°) ∩ (g ≫ y°) ≫ (y ≫ g°) :=
    le_inter
      (le_trans (comp_mono_right (inter_lb_left _ _) _) (comp_mono_left _ (inter_lb_left _ _)))
      (le_trans (comp_mono_right (inter_lb_right _ _) _) (comp_mono_left _ (inter_lb_right _ _)))
  have h_fst : (f ≫ x°) ≫ (x ≫ f°) ⊑ f ≫ f° := by
    have eq1 : (f ≫ x°) ≫ (x ≫ f°) = f ≫ (x° ≫ x) ≫ f° := by simp [Cat.assoc]
    rw [eq1]
    exact le_trans (comp_mono_left _ (comp_mono_right hx _)) (by rw [Cat.id_comp]; exact le_refl _)
  have h_snd : (g ≫ y°) ≫ (y ≫ g°) ⊑ g ≫ g° := by
    have eq2 : (g ≫ y°) ≫ (y ≫ g°) = g ≫ (y° ≫ y) ≫ g° := by simp [Cat.assoc]
    rw [eq2]
    exact le_trans (comp_mono_left _ (comp_mono_right hy _)) (by rw [Cat.id_comp]; exact le_refl _)
  refine le_trans step1 ?_
  rw [← htab]
  exact le_inter (le_trans (inter_lb_left _ _) h_fst) (le_trans (inter_lb_right _ _) h_snd)

/-- §2.143 forward: if `x°y ⊑ R` then there is a map `h = x≫f° ∩ y≫g°` with `h≫f=x`, `h≫g=y`.
    `Hf = (xf° ∩ yg°)f ⊑ xf°f ⊑ x`, and `Hf = x` by [2.133]; similarly `Hg = y`. -/
theorem tabulation_UP_forward {a b c p : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) {x : p ⟶ a} {y : p ⟶ b}
    (hx : Map x) (hy : Map y) (hxy : x° ≫ y ⊑ R) :
    ∃ (h : p ⟶ c), Map h ∧ h ≫ f = x ∧ h ≫ g = y := by
  have hf_map : Map f := ht.1
  have hg_map : Map g := ht.2.1
  have hH : Map (x ≫ f° ∩ y ≫ g°) :=
    ⟨tab_UP_H_entire ht hx hy hxy, tabulation_simple_of_simple ht hx.2 hy.2⟩
  refine ⟨x ≫ f° ∩ y ≫ g°, hH, ?_, ?_⟩
  · apply map_order_discrete (map_comp hH hf_map) hx
    have h1 : (x ≫ f° ∩ y ≫ g°) ≫ f ⊑ x ≫ Cat.id a := by
      refine le_trans (comp_mono_right (inter_lb_left _ _) f) ?_
      rw [Cat.assoc]; exact comp_mono_left x hf_map.2
    rwa [Cat.comp_id] at h1
  · apply map_order_discrete (map_comp hH hg_map) hy
    have h2 : (x ≫ f° ∩ y ≫ g°) ≫ g ⊑ y ≫ Cat.id b := by
      refine le_trans (comp_mono_right (inter_lb_right _ _) g) ?_
      rw [Cat.assoc]; exact comp_mono_left y hg_map.2
    rwa [Cat.comp_id] at h2

/-- §2.143 forward, EXPLICIT witness: the mediating map is exactly `x≫f° ∩ y≫g°`. -/
theorem tabulation_UP_forward_witness {a b c p : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) {x : p ⟶ a} {y : p ⟶ b}
    (hx : Map x) (hy : Map y) (hxy : x° ≫ y ⊑ R) :
    Map (x ≫ f° ∩ y ≫ g°) ∧ (x ≫ f° ∩ y ≫ g°) ≫ f = x ∧ (x ≫ f° ∩ y ≫ g°) ≫ g = y := by
  have hf_map : Map f := ht.1
  have hg_map : Map g := ht.2.1
  have hH : Map (x ≫ f° ∩ y ≫ g°) :=
    ⟨tab_UP_H_entire ht hx hy hxy, tabulation_simple_of_simple ht hx.2 hy.2⟩
  refine ⟨hH, ?_, ?_⟩
  · apply map_order_discrete (map_comp hH hf_map) hx
    have h1 : (x ≫ f° ∩ y ≫ g°) ≫ f ⊑ x ≫ Cat.id a := by
      refine le_trans (comp_mono_right (inter_lb_left _ _) f) ?_
      rw [Cat.assoc]; exact comp_mono_left x hf_map.2
    rwa [Cat.comp_id] at h1
  · apply map_order_discrete (map_comp hH hg_map) hy
    have h2 : (x ≫ f° ∩ y ≫ g°) ≫ g ⊑ y ≫ Cat.id b := by
      refine le_trans (comp_mono_right (inter_lb_right _ _) g) ?_
      rw [Cat.assoc]; exact comp_mono_left y hg_map.2
    rwa [Cat.comp_id] at h2

/-- §2.143 uniqueness: two maps `h, h'` mediating the same factorization are equal.
    If `h≫f=x=h'≫f` then `h = h(f f° … )`; more directly `h = h(ff°∩gg°)…` is not needed —
    we use `h≫f=h'≫f` and `h≫g=h'≫g` and §2.141 joint-monicity of `(f,g)`. -/
theorem tabulation_UP_unique {a b c p : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) {h h' : p ⟶ c}
    (hh : Map h) (hh' : Map h')
    (hf : h ≫ f = h' ≫ f) (hg : h ≫ g = h' ≫ g) : h = h' := by
  obtain ⟨hf_map, hg_map, _, htab⟩ := ht
  exact tabulates_monic_pair hf_map hg_map htab h h' hh hh' hf hg

-- §2.144: Tabulations unique up to unique iso.
/-- §2.144: if `(f,g)` and `(f',g')` both tabulate `R`, there is a unique isomorphism
    `u : c' → c` (a map with map inverse) such that `f' = u f`, `g' = u g`.
    Existence: apply §2.143 forward to `(f',g')` viewed via `f'°g' = R ⊑ R`, giving `u`
    with `u f = f'`, `u g = g'`; the reverse tabulation gives the inverse. -/
theorem tabulation_unique_iso {a b c c' : 𝒜} {f : c ⟶ a} {g : c ⟶ b}
    {f' : c' ⟶ a} {g' : c' ⟶ b} {R : a ⟶ b}
    (ht : Tabulates f g R) (ht' : Tabulates f' g' R) :
    ∃ (u : c' ⟶ c), Map u ∧ Freyd.IsIso u ∧ f' = u ≫ f ∧ g' = u ≫ g := by
  -- u : c'→c with u≫f = f', u≫g = g', from forward UP applied at apex c' with x=f', y=g'.
  have hxy : f'° ≫ g' ⊑ R := by rw [← ht'.2.2.1]; exact le_refl _
  obtain ⟨u, hu, huf, hug⟩ := tabulation_UP_forward ht ht'.1 ht'.2.1 hxy
  -- v : c→c' with v≫f' = f, v≫g' = g, from forward UP applied at apex c with x=f, y=g.
  have hyx : f° ≫ g ⊑ R := by rw [← ht.2.2.1]; exact le_refl _
  obtain ⟨v, hv, hvf, hvg⟩ := tabulation_UP_forward ht' ht.1 ht.2.1 hyx
  -- u≫v : c'→c' satisfies (uv)f' = u(vf') = u f = f', so uv = id by uniqueness on (f',g').
  have huv_id : u ≫ v = Cat.id c' := by
    apply tabulation_UP_unique ht' (map_comp hu hv) (id_is_map_local c')
    · rw [Cat.assoc, hvf, huf, Cat.id_comp]
    · rw [Cat.assoc, hvg, hug, Cat.id_comp]
  have hvu_id : v ≫ u = Cat.id c := by
    apply tabulation_UP_unique ht (map_comp hv hu) (id_is_map_local c)
    · rw [Cat.assoc, huf, hvf, Cat.id_comp]
    · rw [Cat.assoc, hug, hvg, Cat.id_comp]
  exact ⟨u, hu, ⟨v, huv_id, hvu_id⟩, huf.symm, hug.symm⟩

-- §2.145: If a coreflexive morphism A is tabular then ∃ monic map h with A = h°h.
/-- §2.145: if a coreflexive `A` is tabular by `(f,g)` then `g = f` (by [2.133]) and `f` is
    a monic map with `A = f°f`.  (`g ⊑ ff°g ⊑ fA ⊑ f`, so `g = f`; clearly `ff° = 1`.) -/
theorem coreflexive_tabular_monic {a : 𝒜} {A : a ⟶ a} (hA : Coreflexive A) (hTab : Tabular A) :
    ∃ (c : 𝒜) (h : c ⟶ a), Map h ∧ Freyd.Monic h ∧ A = h° ≫ h ∧ h ≫ h° = Cat.id c := by
  obtain ⟨c, f, g, hf_map, hg_map, hA_eq, h_tab_eq⟩ := hTab
  have hidff : Cat.id c ⊑ f ≫ f° := h_tab_eq ▸ inter_lb_left _ _
  -- g ⊑ f: g ⊑ (ff°)g = f(f°g) = f A ⊑ f (since A ⊑ 1).
  have hg_le_f : g ⊑ f := by
    have h1 : g ⊑ (f ≫ f°) ≫ g := by
      have := comp_mono_right hidff g; rwa [Cat.id_comp] at this
    have h2 : (f ≫ f°) ≫ g = f ≫ A := by rw [Cat.assoc, ← hA_eq]
    have h3 : f ≫ A ⊑ f := by
      have := comp_mono_left f hA; rwa [Cat.comp_id] at this
    exact le_trans h1 (h2 ▸ h3)
  -- f = g by discreteness of the order on maps.
  have hfg : f = g := (map_order_discrete hg_map hf_map hg_le_f).symm
  -- A = f°≫f.
  have hA_id : A = f° ≫ f := by rw [hA_eq, hfg]
  -- ff° = 1_c (since g = f, the joint-monicity equation collapses to ff° = 1_c).
  have hff_id : f ≫ f° = Cat.id c := by
    have heq : f ≫ f° ∩ g ≫ g° = Cat.id c := h_tab_eq
    rw [← hfg, Allegory.inter_idem] at heq; exact heq
  refine ⟨c, f, hf_map, Freyd.mono_of_retraction f f° hff_id, hA_id, hff_id⟩

-- §2.147: If A is a tabular allegory then Map(A) has pullbacks, equalizers, images
-- and pullbacks transfer images.  PROVED in MapCat.lean via the source-apex UMP
-- (mapHasPullbacks / mapHasEqualizers / mapHasImages / mapPullbacksTransferCovers).

-- §2.148: If A is a tabular allegory then A ≅ Rel(Map(A)).  PROVED in MapCat.lean
-- as `relMap_allegoryEquiv` (RelMap 𝒜 ≅ 𝒜).

/-! ## §2.151  Dom isomorphism onto an ideal for partial units -/

/-- §2.151: Dom is order-preserving on (α,π). -/
theorem dom_mono_of_le {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) : dom R ⊑ dom S := by
  dsimp [dom]
  apply le_inter (inter_lb_left _ _)
  -- Goal: id ∩ RR° ⊑ SS°. Since R⊑S and R°⊑S°: RR° ⊑ SR° ⊑ SS°.
  exact le_trans (inter_lb_right _ _)
    (le_trans (comp_mono_right h R°) (comp_mono_left S (recip_mono h)))

/-- §2.151: For a partial unit π, Dom is injective on (α,π):
    `dom R ⊑ dom S → R ⊑ S`. -/
theorem dom_injective_partial_unit {a T : 𝒜} (hPU : PartialUnit T)
    {R S : a ⟶ T} (h : dom R ⊑ dom S) : R ⊑ S := by
  -- R ⊑ dom(R)≫R ⊑ dom(S)≫R ⊑ SS°≫R ⊑ S·id_T = S.
  -- SS°R: S°R : T→T, and by PartialUnit T: S°R ⊑ id_T.
  -- R ⊑ domR≫R ⊑ domS≫R ⊑ (SS°)≫R = S≫(S°≫R) ⊑ S≫id = S.
  have h1 : R ⊑ dom S ≫ R := le_trans (le_dom_comp R) (comp_mono_right h R)
  have h2 : dom S ≫ R ⊑ (S ≫ S°) ≫ R :=
    comp_mono_right (inter_lb_right _ _) R
  have h3 : (S ≫ S°) ≫ R ⊑ S := by
    rw [Cat.assoc]
    have := comp_mono_left S (hPU (S° ≫ R))
    rwa [Cat.comp_id] at this
  exact le_trans h1 (le_trans h2 h3)

/-- §2.151: For a partial unit π, `dom R = dom S ↔ R = S`.
    (Dom is a semi-lattice isomorphism onto its image.) -/
theorem dom_eq_iff_eq_of_partial_unit {a T : 𝒜} (hPU : PartialUnit T)
    {R S : a ⟶ T} : dom R = dom S ↔ R = S := by
  constructor
  · intro h
    exact le_antisymm
      (dom_injective_partial_unit hPU (h ▸ le_refl _))
      (dom_injective_partial_unit hPU (h ▸ le_refl _))
  · intro h; rw [h]

-- §2.152: The unique entire morphism p_α : α → λ (for unit λ) is a map.
-- (Stated in its own section so the only `Allegory` instance is the one coming from
-- `UnitaryAllegory`; otherwise the file-level `variable [Allegory 𝒜]` would supply a
-- *second*, universe-distinct allegory and the entire morphism to `unit_obj` would not
-- typecheck against the goal's `Map`.)
section UnitProj
variable {𝒜 : Type u} [UnitaryAllegory 𝒜]

theorem unit_proj_is_map (a : 𝒜) :
    ∃ (p : a ⟶ UnitaryAllegory.unit_obj (𝒜 := 𝒜)), Map p := by
  obtain ⟨hPU, hEntire⟩ := UnitaryAllegory.unit_prop (𝒜 := 𝒜)
  obtain ⟨p, hp_entire⟩ := hEntire a
  exact ⟨p, hp_entire, hPU (p° ≫ p)⟩

/-- §2.152: If λ is a unit then p_α(p_β)° is maximum in (α,β):
    for any R:α→β, `R ⊑ p_α ≫ (p_β)°`.
    Proof: R ⊑ Rp_β(p_β)° ⊑ p_α(p_β)° (using PartialUnit gives Rp_β⊑p_α). -/
theorem unit_proj_max {α β : 𝒜} (p_α : α ⟶ UnitaryAllegory.unit_obj (𝒜 := 𝒜))
    (hp_α : Map p_α) (p_β : β ⟶ UnitaryAllegory.unit_obj (𝒜 := 𝒜))
    (hp_β : Map p_β) (R : α ⟶ β) :
    R ⊑ p_α ≫ p_β° := by
  obtain ⟨hPU, _⟩ := UnitaryAllegory.unit_prop (𝒜 := 𝒜)
  -- R ⊑ R≫p_β≫p_β°: from Entire(p_β): 1_β ⊑ p_β≫p_β°, so R = R≫1_β ⊑ R≫p_β≫p_β°.
  -- id_β ⊑ p_β≫p_β° from Entire p_β.
  have h_ent : Cat.id β ⊑ p_β ≫ p_β° := by
    have := hp_β.1  -- Entire p_β : dom p_β = id_β
    rw [Entire, dom] at this
    exact this ▸ inter_lb_right _ _
  -- R ⊑ R≫p_β≫p_β°.
  have h1 : R ⊑ (R ≫ p_β) ≫ p_β° := by
    rw [Cat.assoc]
    have := comp_mono_left R h_ent
    rwa [Cat.comp_id] at this
  -- p_α°≫R≫p_β : λ→λ, so ⊑ id_λ by PartialUnit.
  have hPU_app : p_α° ≫ R ≫ p_β ⊑ Cat.id _ := hPU (p_α° ≫ R ≫ p_β)
  -- R≫p_β ⊑ p_α: 1_α ⊑ p_α≫p_α° (Entire p_α), so R≫p_β ⊑ p_α≫p_α°≫R≫p_β ⊑ p_α.
  have h_pα_ent : Cat.id α ⊑ p_α ≫ p_α° := by
    have := hp_α.1
    rw [Entire, dom] at this
    exact this ▸ inter_lb_right _ _
  have h2 : R ≫ p_β ⊑ p_α := by
    have step1 : R ≫ p_β ⊑ (p_α ≫ p_α°) ≫ (R ≫ p_β) := by
      have := comp_mono_right h_pα_ent (R ≫ p_β)
      rwa [Cat.id_comp] at this
    have step2 : (p_α ≫ p_α°) ≫ (R ≫ p_β) = p_α ≫ (p_α° ≫ R ≫ p_β) := by
      simp [Cat.assoc]
    have step3 : p_α ≫ (p_α° ≫ R ≫ p_β) ⊑ p_α := by
      have := comp_mono_left p_α hPU_app
      rwa [Cat.comp_id] at this
    exact le_trans step1 (step2 ▸ step3)
  -- Combine.
  exact le_trans h1 (comp_mono_right h2 p_β°)

end UnitProj

-- §2.152: If λ is a unit then for any α,β, the morphism p_α(p_β)° is maximum in (α,β).
-- PROVED above as `unit_proj_max` (UnitProj section).

-- BOOK §2.154: The category of small regular categories is isomorphic to the
-- category of small unitary tabular allegories.

-- BOOK §2.154: A small unitary tabular allegory may be faithfully represented
-- in a power of the allegory of sets.

-- §2.162: If R,S splits a symmetric idempotent T (RS = T, SR = 1) then S = R°.
theorem split_symm_idem_recip {a c : 𝒜} {R : a ⟶ c} {S : c ⟶ a} {T : a ⟶ a}
    (hRS : R ≫ S = T) (hSR : S ≫ R = Cat.id c) (hSymm : Symmetric T) :
    S = R° := by
  -- R°≫S° = (S≫R)° = id_c
  have h_ro_so : R° ≫ S° = Cat.id c := by
    rw [← Allegory.recip_comp, hSR, recip_id]
  -- S°≫R° = (R≫S)° = T° = T
  have h_so_ro : S° ≫ R° = T := by
    rw [← Allegory.recip_comp, hRS, symmetric_eq hSymm]
  -- R°≫T = (R°≫S°)≫R° = id_c≫R° = R°
  have h_ro_T : R° ≫ T = R° := by
    rw [← h_so_ro, ← Cat.assoc, h_ro_so, Cat.id_comp]
  -- S≫T = S≫(R≫S) = (S≫R)≫S = id_c≫S = S
  have h_S_T : S ≫ T = S := by
    rw [← hRS, ← Cat.assoc, hSR, Cat.id_comp]
  -- id_c ⊑ R°≫R  (modular law on S≫R = id_c)
  have h_id_le_ror : Cat.id c ⊑ R° ≫ R := by
    have h_mod := modular_le S R (Cat.id c)
    rw [Cat.id_comp, hSR, Allegory.inter_idem] at h_mod
    exact le_trans h_mod (comp_mono_right (inter_lb_right _ _) R)
  -- id_c ⊑ S≫S°  (modular law on R°≫S° = id_c)
  have h_id_le_sso : Cat.id c ⊑ S ≫ S° := by
    have h_mod := modular_le R° S° (Cat.id c)
    rw [Cat.id_comp, h_ro_so, Allegory.inter_idem, Allegory.recip_recip] at h_mod
    exact le_trans h_mod (comp_mono_right (inter_lb_right _ _) S°)
  -- S ⊑ R°
  have h_s_le_ro : S ⊑ R° := by
    calc S = Cat.id c ≫ S := (Cat.id_comp _).symm
      _ ⊑ (R° ≫ R) ≫ S := comp_mono_right h_id_le_ror S
      _ = R° ≫ (R ≫ S) := Cat.assoc _ _ _
      _ = R° ≫ T := by rw [hRS]
      _ = R° := h_ro_T
  -- R° ⊑ S
  have h_ro_le_s : R° ⊑ S := by
    calc R° = Cat.id c ≫ R° := (Cat.id_comp _).symm
      _ ⊑ (S ≫ S°) ≫ R° := comp_mono_right h_id_le_sso R°
      _ = S ≫ (S° ≫ R°) := Cat.assoc _ _ _
      _ = S ≫ T := by rw [h_so_ro]
      _ = S := h_S_T
  exact le_antisymm h_s_le_ro h_ro_le_s

-- §2.163: A coreflexive morphism A is a split idempotent iff A is tabular.
-- Split form (source-apex): ∃ map h : c → a with h°≫h = A and h≫h° = id_c.
theorem coreflexive_split_iff_tabular {a : 𝒜} {A : a ⟶ a} (hA : Coreflexive A) :
    (∃ (c : 𝒜) (h : c ⟶ a), Map h ∧ h° ≫ h = A ∧ h ≫ h° = Cat.id c) ↔ Tabular A := by
  constructor
  · -- Split ⟹ Tabular: tabulate A by the pair (h, h).
    rintro ⟨c, h, hh_map, hhh, hhh_id⟩
    refine ⟨c, h, h, hh_map, hh_map, ?_, ?_⟩
    · rw [hhh]
    · rw [hhh_id, Allegory.inter_idem]
  · -- Tabular ⟹ Split: `coreflexive_tabular_monic` already produces the split map.
    intro hTab
    obtain ⟨c, h, hh_map, _, hA_eq, hhh_id⟩ := coreflexive_tabular_monic hA hTab
    exact ⟨c, h, hh_map, hA_eq.symm, hhh_id⟩

-- §2.163: An equivalence relation E is a split idempotent iff it is effective
-- (∃ map f with ff° = E, f°f = 1).
def EquivalenceRel {a : 𝒜} (E : a ⟶ a) : Prop :=
  Reflexive E ∧ Symmetric E ∧ Transitive E

theorem equiv_rel_split_iff_effective {a : 𝒜} {E : a ⟶ a} (hE : EquivalenceRel E) :
    (∃ (c : 𝒜) (f : a ⟶ c), Map f ∧ f ≫ f° = E ∧ f° ≫ f = Cat.id c) ↔
    ∃ (c : 𝒜) (R : a ⟶ c) (S : c ⟶ a), R ≫ S = E ∧ S ≫ R = Cat.id c := by
  obtain ⟨hRefl, hSymm, _⟩ := hE
  constructor
  · -- Effective ⟹ split: take R = f, S = f°.
    rintro ⟨c, f, _, hff, hffr⟩
    exact ⟨c, f, f°, hff, hffr⟩
  · -- Split ⟹ effective: split_symm_idem_recip gives S = R°, then R is the map.
    rintro ⟨c, R, S, hRS, hSR⟩
    have hS : S = R° := split_symm_idem_recip hRS hSR hSymm
    subst hS
    -- Now R≫R° = E and R°≫R = id_c; R is a map.
    refine ⟨c, R, ⟨?_, ?_⟩, hRS, hSR⟩
    · -- Entire R: dom R = id_a, i.e. id_a ∩ R≫R° = id_a, from id_a ⊑ E = R≫R°.
      show Cat.id a ∩ R ≫ R° = Cat.id a
      have h_id_le : Cat.id a ⊑ R ≫ R° := by rw [hRS]; exact hRefl
      -- id_a ⊑ R≫R° means id_a ∩ R≫R° = id_a.
      dsimp [le] at h_id_le; exact h_id_le
    · -- Simple R: R°≫R ⊑ id_c, in fact = id_c.
      show R° ≫ R ⊑ Cat.id c
      rw [hSR]; exact le_refl _

-- BOOK §2.165: If A is pre-tabular then Spl(Cor(A)) remains pre-tabular.

-- BOOK §2.166: An allegory is tabular iff it is pre-tabular and all coreflexive morphisms split.

-- §2.167: For a pre-tabular allegory A, Spl(Cor(A)) is its tabular reflection.
--   TABULARITY PROVED: `SplCorObj.tabular_of_preTabular` (Freyd/Spl.lean) — TabularAllegory
--   (SplCorObj A) for [PreTabularAllegory A]. (Full "reflection" universal property still open.)

-- BOOK §2.16(10): Let A be an allegory, SI its class of symmetric idempotents.
-- Spl(SI) is tabular iff A is semi-simple.

-- BOOK §2.16(13): If C is an AC regular category and Ĉ its effective reflection,
-- then C is equivalent to the full subcategory of projective objects in Ĉ;
-- hence if Ĉ is not effective then C is not AC.

end Freyd.Alg
