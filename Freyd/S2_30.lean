/-
  Freyd & Scedrov, *Categories and Allegories* §2.3  Division allegories.

  §2.31 DIVISION ALLEGORY — right division R/S
  §2.331 SYMMETRIC DIVISION R/ₛS
  §2.35  STRAIGHT morphism, simple part, domain of simplicity
-/

module

public import Freyd.S1_10
public import Freyd.S2_10
public import Freyd.S2_20
public import AOP.A4_1  -- modular_le_right (dual modular law)


universe v u

namespace Freyd.Alg

/-! ## §2.31  Division allegory

  A DIVISION ALLEGORY is a distributive allegory with a binary partial
  operation R/S (right division) defined when R□ = S□, characterized by:
  T ⊑ R/S  iff  TS ⊑ R.

  Equivalently: (R/S)S ⊑ R (semi-commutative triangle) and R/S is
  maximal among such morphisms. -/

/-- A DIVISION ALLEGORY (§2.31): distributive allegory with right division R/S,
    the right adjoint to composition (-) ≫ S. -/
public class DivisionAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- Right division R/S : □R → □S, defined when R□ = S□. -/
  div {A B C : 𝒜} (R : A ⟶ C) (S : B ⟶ C) : A ⟶ B

  /-- The semi-commutative triangle: (R/S)S ⊑ R (§2.31). -/
  div_comp_le {A B C : 𝒜} (R : A ⟶ C) (S : B ⟶ C) : (div R S ≫ S) ⊑ R

  /-- The adjointness: if TS ⊑ R then T ⊑ R/S (§2.31). -/
  le_div {A B C : 𝒜} (T : A ⟶ B) (R : A ⟶ C) (S : B ⟶ C) (h : T ≫ S ⊑ R) : T ⊑ div R S

/-! ### Notation -/

/-- Right division notation R / S -/
infixl:70 " / " => DivisionAllegory.div

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ### Derived properties of division -/

/-- The defining equivalence: T ⊑ R/S iff TS ⊑ R (§2.31). -/
public theorem le_div_iff {A B C : 𝒜} (X : A ⟶ B) (R : A ⟶ C) (S : B ⟶ C) :
    X ⊑ R / S ↔ X ≫ S ⊑ R := by
  constructor
  · intro h
    -- X ⊑ R/S → XS ⊑ (R/S)S ⊑ R
    apply le_trans ?_ (DivisionAllegory.div_comp_le R S)
    exact comp_mono_right h S
  · exact DivisionAllegory.le_div X R S

/-- (R ∩ R')/S = (R/S) ∩ (R'/S) (§2.31, full equality).

    Book §2.31: "The first containment may be replaced with an equality:
    (R₁/S ∩ R₂/S) ⊑ (R₁∩R₂)/S because (R₁/S ∩ R₂/S)S ⊑ (R₁/S)S ∩ (R₂/S)S ⊑ (R₁∩R₂)." -/
public theorem div_inter_eq {A B C : 𝒜} (R R' : A ⟶ C) (S : B ⟶ C) :
    (R ∩ R') / S = (R / S) ∩ (R' / S) := by
  apply le_antisymm
  · -- ⊑ : (R∩R')/S ⊑ R/S and ⊑ R'/S
    apply le_inter
    · apply (le_div_iff _ _ _).mpr
      -- ((R ∩ R') / S) ≫ S ⊑ R ∩ R' ⊑ R
      apply le_trans (DivisionAllegory.div_comp_le _ _)
      exact inter_lb_left _ _
    · apply (le_div_iff _ _ _).mpr
      apply le_trans (DivisionAllegory.div_comp_le _ _)
      exact inter_lb_right _ _
  · -- ⊒ : (R/S ∩ R'/S) ⊑ (R∩R')/S, since (R/S ∩ R'/S)S ⊑ (R/S)S ∩ (R'/S)S ⊑ R∩R'
    apply (le_div_iff _ _ _).mpr
    apply le_inter
    · exact le_trans (comp_mono_right (inter_lb_left _ _) S) (DivisionAllegory.div_comp_le R S)
    · exact le_trans (comp_mono_right (inter_lb_right _ _) S) (DivisionAllegory.div_comp_le R' S)

/-- (R ∩ R')/S ⊑ (R/S) ∩ (R'/S) (§2.31, the ⊑ direction of `div_inter_eq`). -/
theorem div_inter_le {A B C : 𝒜} (R R' : A ⟶ C) (S : B ⟶ C) :
    (R ∩ R') / S ⊑ (R / S) ∩ (R' / S) := by
  rw [div_inter_eq]; exact le_refl _

/-- R/1 = R (§2.314). -/
public theorem div_one {A B : 𝒜} (R : A ⟶ B) : R / Cat.id B = R := by
  apply le_antisymm
  · -- (R/1) ⊑ R: DivisionAllegory.div_comp_le gives (R/1)≫1 ⊑ R, and (R/1)≫1 = R/1
    have h := DivisionAllegory.div_comp_le R (Cat.id B)
    simpa [Cat.comp_id] using h
  · -- R ⊑ R/1: by le_div_iff, this is equivalent to R≫1 ⊑ R
    rw [le_div_iff]
    simpa [Cat.comp_id] using le_refl R

/-- 1 ⊑ R/R (§2.314). -/
public theorem one_le_div_self {A B : 𝒜} (R : A ⟶ B) : Cat.id A ⊑ R / R := by
  apply (le_div_iff _ _ _).mpr
  rw [Cat.id_comp]
  exact le_refl _

/-- (R/R)R ⊑ R (§2.314). -/
public theorem div_self_comp_le {A B : 𝒜} (R : A ⟶ B) : (R / R) ≫ R ⊑ R :=
  DivisionAllegory.div_comp_le R R

/-- Division is monotone in the numerator: R ⊑ R' → R/S ⊑ R'/S. -/
public theorem div_mono_left {A B C : 𝒜} {R R' : A ⟶ C} (h : R ⊑ R') (S : B ⟶ C) :
    R / S ⊑ R' / S :=
  (le_div_iff _ _ _).mpr (le_trans (DivisionAllegory.div_comp_le R S) h)

/-- (R/S)(S/W) ⊑ R/W (§2.314).
    `W`, not the book's `T`: `diag/allegory-axioms.typ` §8 exports its picture from this
    statement, and reads the third relation as what a guest **wants**. -/
public theorem div_comp {A B C D : 𝒜} (R : A ⟶ D) (S : B ⟶ D) (W : C ⟶ D) :
    (R / S) ≫ (S / W) ⊑ R / W := by
  apply (le_div_iff _ _ _).mpr
  apply le_trans ?_ (DivisionAllegory.div_comp_le R S)
  rw [Cat.assoc]
  exact comp_mono_left (R / S) (DivisionAllegory.div_comp_le S W)

/-- R/(S₁∪S₂) = (R/S₁) ∩ (R/S₂) (§2.314). -/
public theorem div_union {A B C : 𝒜} (R : A ⟶ C) (S₁ S₂ : B ⟶ C) :
    R / (S₁ ∪ S₂) = (R / S₁) ∩ (R / S₂) := by
  apply le_antisymm
  · -- R/(S₁∪S₂) ⊑ R/S₁: by le_div_iff, (R/(S₁∪S₂))(S₁) ⊑ (R/(S₁∪S₂))(S₁∪S₂) ⊑ R
    apply le_inter
    · apply (le_div_iff _ _ _).mpr
      exact le_trans (comp_mono_left _ (le_union_left S₁ S₂)) (DivisionAllegory.div_comp_le R _)
    · apply (le_div_iff _ _ _).mpr
      exact le_trans (comp_mono_left _ (le_union_right S₁ S₂)) (DivisionAllegory.div_comp_le R _)
  · -- R/S₁ ∩ R/S₂ ⊑ R/(S₁∪S₂): need T(S₁∪S₂) ⊑ R whenever TS₁ ⊑ R and TS₂ ⊑ R
    apply (le_div_iff _ _ _).mpr
    rw [DistributiveAllegory.comp_union_distrib]
    exact union_lub
      (le_trans (comp_mono_right (inter_lb_left _ _) S₁) (DivisionAllegory.div_comp_le R S₁))
      (le_trans (comp_mono_right (inter_lb_right _ _) S₂) (DivisionAllegory.div_comp_le R S₂))

/-- R/(S₁≫S₂) = (R/S₂)/S₁ (§2.314). -/
public theorem div_comp_assoc {A B C D : 𝒜} (R : A ⟶ D) (S₁ : B ⟶ C) (S₂ : C ⟶ D) :
    R / (S₁ ≫ S₂) = (R / S₂) / S₁ := by
  apply le_antisymm
  · -- R/(S₁S₂) ⊑ (R/S₂)/S₁: need ((R/(S₁S₂)) ≫ S₁) ≫ S₂ ⊑ R
    apply (le_div_iff _ _ _).mpr
    apply (le_div_iff _ _ _).mpr
    -- goal: ((R / (S₁ ≫ S₂)) ≫ S₁) ≫ S₂ ⊑ R
    -- ((R/(S₁S₂))S₁)S₂ = (R/(S₁S₂))(S₁S₂) ⊑ R
    have : ((R / (S₁ ≫ S₂)) ≫ S₁) ≫ S₂ = (R / (S₁ ≫ S₂)) ≫ (S₁ ≫ S₂) := by
      rw [Cat.assoc]
    rw [this]; exact DivisionAllegory.div_comp_le R (S₁ ≫ S₂)
  · -- (R/S₂)/S₁ ⊑ R/(S₁S₂): need ((R/S₂)/S₁)(S₁S₂) ⊑ R
    apply (le_div_iff _ _ _).mpr
    -- ((R/S₂)/S₁)(S₁S₂) = ((R/S₂)/S₁)S₁ · S₂ ⊑ (R/S₂) · S₂ ⊑ R
    have step1 : ((R / S₂) / S₁) ≫ (S₁ ≫ S₂) = (((R / S₂) / S₁) ≫ S₁) ≫ S₂ := by
      rw [Cat.assoc]
    rw [step1]
    exact le_trans (comp_mono_right (DivisionAllegory.div_comp_le (R / S₂) S₁) S₂) (DivisionAllegory.div_comp_le R S₂)

/-! ## §2.316  Heyting algebra structure on (a,a)

  For an object a in a division allegory, the hom-set (a,a) is a Heyting
  algebra.  Given A, B ∈ (a,a) the Heyting implication is defined as
  A ⊃ B := 1 ∩ B/A  (§2.316). -/

/-- Heyting implication in (a,a): A ⊃ B := 1 ∩ B/A (§2.316). -/
@[expose] public def heytingImpl {a : 𝒜} (A B : a ⟶ a) : a ⟶ a :=
  Cat.id a ∩ (B / A)

-- Note: the book's §2.316 Heyting algebra is on coreflexive morphisms (subidentities).
-- The general adjointness A ∩ C ⊑ B ↔ C ⊑ 1 ∩ B/A does NOT hold for arbitrary morphisms;
-- it requires A, C coreflexive (so A∩C = A≫C in the poset sense).
-- See heyting_adj_coref below for the correct statement.

/-- Heyting adjointness for coreflexive morphisms (§2.316):
    if A, B, C : a → a are coreflexive, then A ≫ C ⊑ B ↔ C ⊑ 1 ∩ B/A. -/
public theorem heyting_adj_coref {a : 𝒜} {A B C : a ⟶ a}
    (hA : Coreflexive A) (hC : Coreflexive C) :
    A ≫ C ⊑ B ↔ C ⊑ heytingImpl A B := by
  -- Coreflexive morphisms commute: A≫C = A∩C = C∩A = C≫A
  have hac_comm : A ≫ C = C ≫ A :=
    (coreflexive_comp_eq_inter hA hC).trans
      ((Allegory.inter_comm A C).trans (coreflexive_comp_eq_inter hC hA).symm)
  dsimp [heytingImpl]
  constructor
  · intro h
    apply le_inter
    · exact hC
    · -- C ⊑ B/A: use le_div_iff, need C ≫ A ⊑ B
      apply (le_div_iff _ _ _).mpr
      rwa [← hac_comm]
  · intro h
    -- A ≫ C = C ≫ A ⊑ (B/A) ≫ A ⊑ B
    rw [hac_comm]
    exact le_trans (comp_mono_right (le_trans h (inter_lb_right _ _)) A) (DivisionAllegory.div_comp_le B A)

/-! ## §2.331  Symmetric division

  R/ₛS = (R/S) ∩ (S/R)° (§2.35).  Characterized by:
  T ⊑ R/ₛS  iff  TS ⊑ R and T°R ⊑ S. -/

/-- SYMMETRIC DIVISION: R/ₛS = (R/S) ∩ (S/R)° (§2.35, §2.331). -/
@[expose] public def symmDiv {A B C : 𝒜} (R : A ⟶ C) (S : B ⟶ C) : A ⟶ B :=
  (R / S) ∩ ((S / R)°)

infixl:70 " /ₛ " => symmDiv

/-- Characterizing property of symmetric division (§2.35). -/
public theorem le_symmDiv_iff {A B C : 𝒜} (T : A ⟶ B) (R : A ⟶ C) (S : B ⟶ C) :
    T ⊑ R /ₛ S ↔ T ≫ S ⊑ R ∧ T° ≫ R ⊑ S := by
  dsimp [symmDiv]
  constructor
  · intro h
    have h1 : T ⊑ R / S := le_trans h (inter_lb_left _ _)
    have h2 : T ⊑ (S / R)° := le_trans h (inter_lb_right _ _)
    constructor
    · exact ((le_div_iff _ _ _).mp h1)
    · -- T ⊑ (S/R)° → T° ⊑ S/R → T°R ⊑ S
      have h2' : T° ⊑ S / R := by
        -- T ⊑ (S/R)° → T° ⊑ (S/R)°° = S/R
        calc
          T° ⊑ ((S / R)°)° := recip_mono h2
          _ = S / R := by rw [Allegory.recip_recip]
      exact ((le_div_iff _ _ _).mp h2')
  · intro ⟨hTS, hTR⟩
    apply le_inter
    · exact ((le_div_iff _ _ _).mpr hTS)
    · -- T ⊑ (S/R)° ↔ T° ⊑ S/R
      have hTR_div : T° ⊑ S / R := (le_div_iff _ _ _).mpr hTR
      calc
        T = (T°)° := by rw [Allegory.recip_recip]
        _ ⊑ (S / R)° := recip_mono hTR_div

/-! ### Properties of symmetric division (§2.35) -/

/-- Symmetric division satisfies (R/ₛS)° = S/ₛR (§2.35). -/
public theorem symmDiv_recip {A B C : 𝒜} (R : A ⟶ C) (S : B ⟶ C) :
    (R /ₛ S)° = S /ₛ R := by
  apply le_antisymm
  · -- (R/ₛS)° ⊑ S/ₛR.  R:a→c, S:b→c, R/ₛS:a→b, (R/ₛS)°:b→a, S/ₛR:b→a.
    -- le_symmDiv_iff: (R/ₛS)° ⊑ S/ₛR ↔ (R/ₛS)°≫R ⊑ S ∧ ((R/ₛS)°)°≫S ⊑ R.
    rw [le_symmDiv_iff]
    have h := (le_symmDiv_iff (R /ₛ S) R S).mp (le_refl _)
    exact ⟨h.2, by rw [Allegory.recip_recip]; exact h.1⟩
  · -- S/ₛR ⊑ (R/ₛS)°.  Equivalently (S/ₛR)° ⊑ R/ₛS (by recip_le_iff).
    rw [← recip_le_iff]
    apply (le_symmDiv_iff _ R S).mpr
    have h := (le_symmDiv_iff (S /ₛ R) S R).mp (le_refl _)
    -- goal: (S/ₛR)°≫S ⊑ R ∧ (S/ₛR)°°≫R ⊑ S
    -- h.2 : (S/ₛR)°≫S ⊑ R; h.1 : (S/ₛR)≫R ⊑ S, and (S/ₛR)°° = S/ₛR
    exact ⟨h.2, by rw [Allegory.recip_recip]; exact h.1⟩

/-- Symmetric division is transitive: (R/ₛS)(S/ₛW) ⊑ R/ₛW (§2.35).
    `W` for the third relation, as in `div_comp`. -/
public theorem symmDiv_comp {A B C D : 𝒜} (R : A ⟶ D) (S : B ⟶ D) (W : C ⟶ D) :
    (R /ₛ S) ≫ (S /ₛ W) ⊑ R /ₛ W := by
  rw [le_symmDiv_iff]
  have hRS := (le_symmDiv_iff (R /ₛ S) R S).mp (le_refl _)
  have hSW := (le_symmDiv_iff (S /ₛ W) S W).mp (le_refl _)
  constructor
  · -- ((R/ₛS)(S/ₛW)) ≫ W ⊑ R
    rw [Cat.assoc]
    exact le_trans (comp_mono_left _ hSW.1) hRS.1
  · -- ((R/ₛS)(S/ₛW))° ≫ R ⊑ W
    -- = (S/ₛW)°(R/ₛS)° ≫ R ⊑ W
    rw [Allegory.recip_comp, Cat.assoc]
    -- (R/ₛS)° = S/ₛR, and (S/ₛW)° = W/ₛS
    have h_rs_rec : (R /ₛ S)° ≫ R ⊑ S := hRS.2
    exact le_trans (comp_mono_left _ h_rs_rec) hSW.2

-- Note: "R/ₛS ⊑ R" is listed in the book as a containment (§2.35) but only for the
-- case where the objects match (S = 1), i.e. simplePart R ⊑ R. See simplePart_le.
-- For general S the containment R/ₛS ⊑ R does not hold (R and R/ₛS have different types
-- in general: R : a→c, R/ₛS : a→b; the book notation is in the endomorphism case only).

/-! ## §2.35  Straight morphism, simple part

  R is STRAIGHT if R/ₛR ⊑ 1 (§2.351).
  In a division allegory, for any R, R/(R/ₛR) is the simple part. -/

/-- R is STRAIGHT if R/ₛR ⊑ 1 (§2.351). -/
@[expose] public def Straight {A B : 𝒜} (R : A ⟶ B) : Prop := R /ₛ R ⊑ Cat.id A

/-- In a division allegory, (R/R)R = R (§2.314). -/
public theorem div_self_comp {A B : 𝒜} (R : A ⟶ B) : (R / R) ≫ R = R := by
  apply le_antisymm (DivisionAllegory.div_comp_le R R)
  -- R ⊑ (R/R)R: since 1 ⊑ R/R, we have R = 1R ⊑ (R/R)R
  have h : R ⊑ (R / R) ≫ R := by
    calc
      R = (Cat.id A) ≫ R := by rw [Cat.id_comp]
      _ ⊑ (R / R) ≫ R := comp_mono_right (one_le_div_self R) R
  exact h

/-- R/ₛR is reflexive: 1 ⊑ R/ₛR (§2.351). -/
-- The `.mpr` term, not `rw [le_symmDiv_iff]`: rewriting by an Iff drags in `propext`,
-- and this way the proof — and `symmDiv_self_comp` below — stays axiom-free.
public theorem symmDiv_self_reflexive {A B : 𝒜} (R : A ⟶ B) : Reflexive (R /ₛ R) :=
  (le_symmDiv_iff (Cat.id A) R R).mpr
    ⟨by rw [Cat.id_comp]; exact le_refl R,
     by rw [recip_id, Cat.id_comp]; exact le_refl R⟩

/-- In a division allegory, (R/ₛR)R = R (§2.314).
    The book's list has only `(R/ₛR)R ⊑ R`; it is an equality because 1 ⊑ R/ₛR. -/
theorem symmDiv_self_comp {A B : 𝒜} (R : A ⟶ B) : (R /ₛ R) ≫ R = R := by
  apply le_antisymm
  · -- (R/ₛR)R ⊑ (R/R)R = R, since R/ₛR is an intersection with R/R as its left factor
    have h : (R /ₛ R) ≫ R ⊑ (R / R) ≫ R :=
      comp_mono_right (show R /ₛ R ⊑ R / R from inter_lb_left _ _) R
    rw [div_self_comp R] at h
    exact h
  · -- R ⊑ (R/ₛR)R: since 1 ⊑ R/ₛR, we have R = 1R ⊑ (R/ₛR)R
    calc
      R = (Cat.id A) ≫ R := by rw [Cat.id_comp]
      _ ⊑ (R /ₛ R) ≫ R := comp_mono_right (symmDiv_self_reflexive R) R

/-! ## §2.312  Left division

  S\R := (R°/S°)°, defined when codomain(S) = source(R).
  S : a ⟶ b, R : a ⟶ c gives S\R : b ⟶ c.
  Characterization: T ⊑ S\R iff ST ⊑ R. -/

/-- LEFT DIVISION: S\R := (R°/S°)° (§2.312).
    S : a ⟶ b, R : a ⟶ c, result S\R : b ⟶ c. -/
@[expose] public def leftDiv {A B C : 𝒜} (S : A ⟶ B) (R : A ⟶ C) : B ⟶ C :=
  (R° / S°)°

/-- Left division notation `S \ R` (§2.312), mirroring the `R / S` of §2.31.
    Argument order matches the book and `leftDiv`: the divisor `S` comes first. -/
infixl:70 " \\ " => leftDiv

/-- The defining equivalence: T ⊑ S\R iff ST ⊑ R (§2.312). -/
public theorem le_leftDiv_iff {A B C : 𝒜} (X : B ⟶ C) (S : A ⟶ B) (R : A ⟶ C) :
    X ⊑ (S \ R) ↔ S ≫ X ⊑ R := by
  dsimp [leftDiv]
  -- X ⊑ (R°/S°)° ↔ X° ⊑ R°/S° ↔ X°S° ⊑ R° ↔ (SX)° ⊑ R° ↔ SX ⊑ R
  rw [← recip_le_iff, le_div_iff, ← Allegory.recip_comp, recip_le_iff,
      Allegory.recip_recip]

/-- The semi-commutative triangle for left division: S(S\R) ⊑ R (§2.312). -/
public theorem leftDiv_comp_le {A B C : 𝒜} (S : A ⟶ B) (R : A ⟶ C) : S ≫ (S \ R) ⊑ R :=
  (le_leftDiv_iff _ S R).mp (le_refl _)

/-- Left division is monotone in the numerator: R ⊑ R' → S\R ⊑ S\R'. -/
public theorem leftDiv_mono_right {A B C : 𝒜} (S : A ⟶ B) {R R' : A ⟶ C} (h : R ⊑ R') :
    (S \ R) ⊑ (S \ R') :=
  (le_leftDiv_iff _ _ _).mpr (le_trans (leftDiv_comp_le S R) h)

/-- Division by the identity is trivial: `1\R = R`. -/
public theorem leftDiv_id {A B : 𝒜} (R : A ⟶ B) : ((Cat.id A) \ R) = R := by
  apply le_antisymm
  · have h := leftDiv_comp_le (Cat.id A) R; rwa [Cat.id_comp] at h
  · apply (le_leftDiv_iff _ _ _).mpr; rw [Cat.id_comp]; exact le_refl R

/-- Left division composes: `(ST)\R = T\(S\R)`, by the double universal property. -/
public theorem leftDiv_comp {A B C D : 𝒜} (S₁ : A ⟶ B) (S₂ : B ⟶ C) (R : A ⟶ D) :
    ((S₁ ≫ S₂) \ R) = (S₂ \ (S₁ \ R)) := by
  apply le_antisymm
  · apply (le_leftDiv_iff _ S₂ _).mpr
    apply (le_leftDiv_iff _ S₁ _).mpr
    rw [← Cat.assoc]
    exact leftDiv_comp_le (S₁ ≫ S₂) R
  · apply (le_leftDiv_iff _ (S₁ ≫ S₂) _).mpr
    rw [Cat.assoc]
    exact le_trans (comp_mono_left S₁ (leftDiv_comp_le S₂ (S₁ \ R))) (leftDiv_comp_le S₁ R)

/-- Numerator meets distribute over left division: `S\(R∩R') = (S\R)∩(S\R')`. -/
public theorem leftDiv_inter {A B C : 𝒜} (S : A ⟶ B) (R R' : A ⟶ C) :
    (S \ (R ∩ R')) = (S \ R) ∩ (S \ R') := by
  show ((R ∩ R')° / S°)° = (R° / S°)° ∩ (R'° / S°)°
  rw [Allegory.recip_inter, div_inter_eq, Allegory.recip_inter]

/-! ## §2.314  The equation S\(R/T) = (S\R)/T -/

/-- S\(R/W) = (S\R)/W (§2.314).
    S : a ⟶ b, R : a ⟶ d, W : c ⟶ d.
    LHS: (S \ (R/W)) where R/W : a ⟶ c, so (S \ (R/W)) : b ⟶ c.
    RHS: (S \ R) / W where (S \ R) : b ⟶ d, W : c ⟶ d, so result : b ⟶ c. ✓
    -/
public theorem leftDiv_div {A B C D : 𝒜} (S : A ⟶ B) (R : A ⟶ D) (W : C ⟶ D) :
    (S \ (R / W)) = (S \ R) / W := by
  apply le_antisymm
  · -- S\(R/W) ⊑ (S\R)/W: show S ≫ ((S \ (R/W)) ≫ W) ⊑ R
    apply (le_div_iff _ _ _).mpr
    apply (le_leftDiv_iff _ S R).mpr
    have h1 : (S ≫ (S \ (R / W))) ≫ W ⊑ (R / W) ≫ W :=
      comp_mono_right (leftDiv_comp_le S (R / W)) W
    have h2 : (R / W) ≫ W ⊑ R := DivisionAllegory.div_comp_le R W
    rw [← Cat.assoc]; exact le_trans h1 h2
  · -- (S\R)/W ⊑ S\(R/W): show (S ≫ (S\R)/W) ≫ W ⊑ R
    apply (le_leftDiv_iff _ S _).mpr
    apply (le_div_iff _ _ _).mpr
    -- goal: (S ≫ (S \ R)/W) ≫ W ⊑ R
    have step1 : ((S \ R) / W) ≫ W ⊑ (S \ R) := DivisionAllegory.div_comp_le (S \ R) W
    have step2 : S ≫ (((S \ R) / W) ≫ W) ⊑ S ≫ (S \ R) :=
      comp_mono_left S step1
    have step3 : S ≫ (S \ R) ⊑ R := leftDiv_comp_le S R
    have step4 : S ≫ (((S \ R) / W) ≫ W) ⊑ R := le_trans step2 step3
    rwa [← Cat.assoc] at step4

/-- **§2.314**: `(R/R)² ⊑ R/R`.  Immediate instance of `div_comp` with `S = W = R`. -/
public theorem div_self_idem {A B : 𝒜} (R : A ⟶ B) : (R / R) ≫ (R / R) ⊑ R / R :=
  div_comp R R R

/-- `(R/R)² = R/R`.  Freyd states §2.314 as two containments, `1 ⊑ R/R` and `(R/R)² ⊑ R/R` — that
    `R/R` is a preorder — but the two together give the equality: reflexivity turns `R/R = 1(R/R)`
    into `⊑ (R/R)(R/R)`, which is the missing direction.  A preorder is idempotent under
    composition. -/
public theorem div_self_comp_self {A B : 𝒜} (R : A ⟶ B) : (R / R) ≫ (R / R) = R / R := by
  apply le_antisymm (div_self_idem R)
  calc R / R = (Cat.id A) ≫ (R / R) := by rw [Cat.id_comp]
    _ ⊑ (R / R) ≫ (R / R) := comp_mono_right (one_le_div_self R) (R / R)

/-- **§2.314**: `(S\R/T)° = T°\R°/S°`.  With `(S \ X) = (X°/S°)°`, both sides reduce
    by `recip_recip` to `(R/T)°/S°` (the LHS unfolds directly; the RHS via `R°° = R`, `T°° = T`).
    This is what makes the two-sided division `S\R/T` self-dual under reciprocation. -/
theorem leftDiv_div_recip {A B C D : 𝒜} (S : A ⟶ B) (R : A ⟶ D) (T : C ⟶ D) :
    (S \ (R / T))° = (T° \ R°) / S° := by
  simp only [leftDiv, Allegory.recip_recip]

/-- **§2.351**: `S` is STRAIGHT iff every symmetric `T` with `TS ⊑ S` is coreflexive.
    Forward: such a `T` lies in `S/ₛS` (`le_symmDiv_iff`, using `T° = T`), and `S/ₛS ⊑ 1`.
    Backward: `S/ₛS` is itself symmetric (`symmDiv_recip`) and satisfies `(S/ₛS)S ⊑ S`, so the
    hypothesis forces `S/ₛS ⊑ 1`, i.e. `S` is straight. -/
theorem straight_iff_symmetric_invariant_coreflexive {A B : 𝒜} (S : A ⟶ B) :
    Straight S ↔ ∀ (T : A ⟶ A), Symmetric T → T ≫ S ⊑ S → Coreflexive T := by
  constructor
  · intro hstr T hsym hTS
    have hTsd : T ⊑ S /ₛ S :=
      (le_symmDiv_iff T S S).mpr ⟨hTS, by rw [symmetric_eq hsym]; exact hTS⟩
    exact le_trans hTsd hstr
  · intro h
    exact h (S /ₛ S) ((symmetric_iff _).mpr (symmDiv_recip S S))
      (((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1)

/-! ## §2.351  R/ₛR is an equivalence relation

  The book's §2.351 states that R/ₛR is an equivalence relation. -/

/-- R/ₛR is symmetric (§2.351).
    (R/ₛR)° = ((R/R) ∩ (R/R)°)° = (R/R)° ∩ (R/R)°° = (R/R)° ∩ (R/R) = R/ₛR. -/
public theorem symmDiv_self_symmetric {A B : 𝒜} (R : A ⟶ B) : Symmetric (R /ₛ R) := by
  -- R/ₛR = (R/R) ∩ (R/R)°. Show (R/ₛR)° ⊑ R/ₛR.
  -- (R/ₛR)° ⊑ R/ₛR = (R/R) ∩ (R/R)°. Check each component:
  -- (R/ₛR)° ⊑ R/R: (R/ₛR)° ⊑ ((R/R)°)° = R/R. ✓
  -- (R/ₛR)° ⊑ (R/R)°: (R/ₛR)° ⊑ ((R/R))° = (R/R)°... wait need (R/ₛR)° ⊑ (R/R)°.
  -- (R/ₛR) ⊑ R/R, so (R/ₛR)° ⊑ (R/R)°. ✓
  dsimp [Symmetric, le, symmDiv]
  -- goal: ((R/R) ∩ (R/R)°)° ∩ ((R/R) ∩ (R/R)°) = ((R/R) ∩ (R/R)°)°
  rw [Allegory.recip_inter, Allegory.recip_recip]
  -- goal: ((R/R)° ∩ (R/R)) ∩ ((R/R) ∩ (R/R)°) = (R/R)° ∩ (R/R)
  rw [show Allegory.inter (R / R) (Allegory.recip (R / R)) =
        Allegory.inter (Allegory.recip (R / R)) (R / R) from Allegory.inter_comm _ _]
  apply Allegory.inter_idem

/-- R/ₛR is transitive: (R/ₛR)(R/ₛR) ⊑ R/ₛR (§2.351). -/
public theorem symmDiv_self_transitive {A B : 𝒜} (R : A ⟶ B) : Transitive (R /ₛ R) := by
  dsimp [Transitive]
  rw [le_symmDiv_iff ((R /ₛ R) ≫ (R /ₛ R)) R R]
  have h1 : (R /ₛ R) ≫ R ⊑ R := ((le_symmDiv_iff (R /ₛ R) R R).mp (le_refl _)).1
  have h_sym : (R /ₛ R)° ⊑ R /ₛ R := symmDiv_self_symmetric R
  constructor
  · -- ((R/ₛR)(R/ₛR)) ≫ R ⊑ R
    -- ((R/ₛR)(R/ₛR)) ≫ R = (R/ₛR) ≫ ((R/ₛR) ≫ R) by assoc; ⊑ (R/ₛR) ≫ R ⊑ R
    have : ((R /ₛ R) ≫ (R /ₛ R)) ≫ R = (R /ₛ R) ≫ (R /ₛ R) ≫ R := Cat.assoc _ _ _
    rw [this]
    exact le_trans (comp_mono_left (R /ₛ R) h1) h1
  · -- ((R/ₛR)(R/ₛR))° ≫ R ⊑ R: = (R/ₛR)°(R/ₛR)° ≫ R ⊑ ... ⊑ R
    rw [Allegory.recip_comp]
    have step1 : (R /ₛ R)° ≫ (R /ₛ R)° ≫ R ⊑ (R /ₛ R) ≫ (R /ₛ R)° ≫ R :=
      comp_mono_right h_sym ((R /ₛ R)° ≫ R)
    have step2 : (R /ₛ R) ≫ (R /ₛ R)° ≫ R ⊑ (R /ₛ R) ≫ (R /ₛ R) ≫ R :=
      comp_mono_left (R /ₛ R) (comp_mono_right h_sym R)
    have step3 : (R /ₛ R) ≫ (R /ₛ R) ≫ R = ((R /ₛ R) ≫ (R /ₛ R)) ≫ R := (Cat.assoc _ _ _).symm
    have step4 : ((R /ₛ R) ≫ (R /ₛ R)) ≫ R ⊑ R := by
      rw [Cat.assoc]; exact le_trans (comp_mono_left (R /ₛ R) h1) h1
    rw [Cat.assoc]
    exact le_trans step1 (le_trans step2 (step3 ▸ step4))

/-- R/ₛR is an EQUIVALENCE RELATION (§2.351). -/
theorem symmDiv_self_equiv {A B : 𝒜} (R : A ⟶ B) :
    Reflexive (R /ₛ R) ∧ Symmetric (R /ₛ R) ∧ Transitive (R /ₛ R) :=
  ⟨symmDiv_self_reflexive R, symmDiv_self_symmetric R, symmDiv_self_transitive R⟩

/-! ## §2.352  Left cancellation for straight morphisms -/

/-- If S is straight, F and G are simple with same source, and FS = GS, then (dom F)G = (dom G)F (§2.352). -/
public theorem straight_cancel_simple {A B C : 𝒜} {S : A ⟶ B} (hS : Straight S)
    {F G : C ⟶ A} (hF : Simple F) (hG : Simple G)
    (h : F ≫ S = G ≫ S) :
    dom F ≫ G = dom G ≫ F := by
  -- G°FS ⊑ G°GS ⊑ S and (G°F)°S = F°GS ⊑ F°FS ⊑ S, so G°F ⊑ S/ₛS ⊑ 1.
  have hGF1 : G° ≫ F ⊑ Cat.id A := by
    refine le_trans ?_ hS
    rw [le_symmDiv_iff (G° ≫ F) S S]
    refine ⟨?_, ?_⟩
    · have eq1 : (G° ≫ F) ≫ S = (G° ≫ G) ≫ S := by rw [Cat.assoc, h, ← Cat.assoc]
      rw [eq1]; exact le_trans (comp_mono_right hG S) (by rw [Cat.id_comp]; exact le_refl S)
    · have heq : (G° ≫ F)° = F° ≫ G := by rw [Allegory.recip_comp, Allegory.recip_recip]
      rw [heq]
      have eq2 : (F° ≫ G) ≫ S = (F° ≫ F) ≫ S := by rw [Cat.assoc, ← h, ← Cat.assoc]
      rw [eq2]; exact le_trans (comp_mono_right hF S) (by rw [Cat.id_comp]; exact le_refl S)
  have hFG1 : F° ≫ G ⊑ Cat.id A := by
    have key : (G° ≫ F)° = F° ≫ G := by rw [Allegory.recip_comp, Allegory.recip_recip]
    calc F° ≫ G = (G° ≫ F)° := key.symm
      _ ⊑ (Cat.id A)° := recip_mono hGF1
      _ = Cat.id A := recip_id
  -- dom F ⊑ F F° and dom G ⊑ G G° (coreflexive part of domain).
  have hdomF : dom F ⊑ F ≫ F° := inter_lb_right _ _
  have hdomG : dom G ⊑ G ≫ G° := inter_lb_right _ _
  -- dom F and dom G are coreflexive, hence commute under composition.
  have hcF := dom_coreflexive F
  have hcG := dom_coreflexive G
  have hcomm : dom F ≫ dom G = dom G ≫ dom F :=
    (coreflexive_comp_eq_inter hcF hcG).trans
      ((Allegory.inter_comm _ _).trans (coreflexive_comp_eq_inter hcG hcF).symm)
  -- Forward chain: (dom F)G ⊑ (dom F)(dom G)G ⊑ (dom G)(dom F)G ⊑ (dom G)F F°G ⊑ (dom G)F.
  apply le_antisymm
  · -- (dom F)G ⊑ (dom F)(dom G)G = (dom G)(dom F)G ⊑ (dom G)F F°G ⊑ (dom G)F.
    have s1 : dom F ≫ G ⊑ dom G ≫ (dom F ≫ G) := by
      have h1 : dom F ≫ G ⊑ dom F ≫ (dom G ≫ G) := comp_mono_left _ (le_dom_comp G)
      have h2 : dom F ≫ (dom G ≫ G) = dom G ≫ (dom F ≫ G) := by
        rw [← Cat.assoc, hcomm, Cat.assoc]
      rwa [h2] at h1
    have s2 : dom G ≫ (dom F ≫ G) ⊑ dom G ≫ F := by
      have h3 : dom F ≫ G ⊑ (F ≫ F°) ≫ G := comp_mono_right hdomF G
      have h4 : (F ≫ F°) ≫ G ⊑ F := by
        rw [Cat.assoc]; have := comp_mono_left F hFG1; rwa [Cat.comp_id] at this
      exact comp_mono_left _ (le_trans h3 h4)
    exact le_trans s1 s2
  · have s1 : dom G ≫ F ⊑ dom F ≫ (dom G ≫ F) := by
      have h1 : dom G ≫ F ⊑ dom G ≫ (dom F ≫ F) := comp_mono_left _ (le_dom_comp F)
      have h2 : dom G ≫ (dom F ≫ F) = dom F ≫ (dom G ≫ F) := by
        rw [← Cat.assoc, ← hcomm, Cat.assoc]
      rwa [h2] at h1
    have s2 : dom F ≫ (dom G ≫ F) ⊑ dom F ≫ G := by
      have h3 : dom G ≫ F ⊑ (G ≫ G°) ≫ F := comp_mono_right hdomG F
      have h4 : (G ≫ G°) ≫ F ⊑ G := by
        rw [Cat.assoc]; have := comp_mono_left G hGF1; rwa [Cat.comp_id] at this
      exact comp_mono_left _ (le_trans h3 h4)
    exact le_trans s1 s2

/-- Helper: from map f, 1 ⊑ f ≫ f° (entireness unfold). -/
private theorem map_entire_le {A B : 𝒜} {f : A ⟶ B} (hf : Map f) : Cat.id A ⊑ f ≫ f° := by
  have := hf.1
  dsimp [Entire, dom] at this
  exact this ▸ inter_lb_right _ _

/-- If S is straight and f, g are maps with fS = gS then f = g (§2.352). -/
theorem straight_cancel {A B C : 𝒜} {S : A ⟶ B} (hS : Straight S)
    {f g : C ⟶ A} (hf : Map f) (hg : Map g) (h : f ≫ S = g ≫ S) : f = g := by
  -- g°f ⊑ S/ₛS ⊑ 1. (g°f)S = g°(fS) = g°(gS) ⊑ (g°g)S ⊑ S; and ((g°f)°)S ⊑ S similarly.
  have hgf_ss : g° ≫ f ⊑ S /ₛ S := by
    rw [le_symmDiv_iff (g° ≫ f) S S]
    constructor
    · -- (g°f)S ⊑ S
      have eq1 : (g° ≫ f) ≫ S = (g° ≫ g) ≫ S := by rw [Cat.assoc, h, ← Cat.assoc]
      rw [eq1]; exact le_trans (comp_mono_right hg.2 S) (by rw [Cat.id_comp]; exact le_refl S)
    · -- (g°f)°S ⊑ S: (g°f)° = f°g°° = f°g
      have heq : (g° ≫ f)° = f° ≫ g := by rw [Allegory.recip_comp, Allegory.recip_recip]
      rw [heq]
      have eq2 : (f° ≫ g) ≫ S = (f° ≫ f) ≫ S := by rw [Cat.assoc, ← h, ← Cat.assoc]
      rw [eq2]; exact le_trans (comp_mono_right hf.2 S) (by rw [Cat.id_comp]; exact le_refl S)
  have hgf1 : g° ≫ f ⊑ Cat.id A := le_trans hgf_ss hS
  have hfg1 : f° ≫ g ⊑ Cat.id A := by
    have key : (g° ≫ f)° = f° ≫ g := by rw [Allegory.recip_comp, Allegory.recip_recip]
    calc f° ≫ g = (g° ≫ f)° := key.symm
        _ ⊑ (Cat.id A)° := recip_mono hgf1
        _ = Cat.id A := recip_id
  apply le_antisymm
  · -- f ⊑ g: 1f ⊑ (gg°)f = g(g°f) ⊑ g1 = g
    have h_id : f ⊑ Cat.id C ≫ f := by dsimp [le]; rw [Cat.id_comp]; exact Allegory.inter_idem f
    have h1 : f ⊑ (g ≫ g°) ≫ f := le_trans h_id (comp_mono_right (map_entire_le hg) f)
    have h2 : g ≫ g° ≫ f ⊑ g ≫ Cat.id A := comp_mono_left g hgf1
    exact Cat.comp_id g ▸ le_trans h1 ((Cat.assoc g g° f).symm ▸ h2)
  · -- g ⊑ f: 1g ⊑ (ff°)g = f(f°g) ⊑ f1 = f
    have h_id : g ⊑ Cat.id C ≫ g := by dsimp [le]; rw [Cat.id_comp]; exact Allegory.inter_idem g
    have h1 : g ⊑ (f ≫ f°) ≫ g := le_trans h_id (comp_mono_right (map_entire_le hf) g)
    have h2 : f ≫ f° ≫ g ⊑ f ≫ Cat.id A := comp_mono_left f hfg1
    exact Cat.comp_id f ▸ le_trans h1 ((Cat.assoc f f° g).symm ▸ h2)

/-! ## §2.353  Converse characterization of straightness -/

/-! ### Domain algebra used by §2.353

  The §2.353 construction sets F' = (dom G)F, G' = (dom F)G for simple F, G with
  the same source and target.  The four lemmas below are the pure
  division-allegory facts the book uses silently:
  `dom F' = dom G'`, `F'°G' = F°G`, `Simple F'`, and `dom R ≫ R = R`. -/

omit [DivisionAllegory 𝒜] in
/-- `dom R ≫ R = R` (the domain restricts nothing): one half is `dom R ⊑ 1`,
    the other is `le_dom_comp`.  Needs only `[Allegory]` (the ambient `[DivisionAllegory]` is
    dropped so `[Allegory]`-only call sites can invoke this directly). -/
public theorem dom_comp_self [Allegory 𝒜] {A B : 𝒜} (R : A ⟶ B) : dom R ≫ R = R :=
  le_antisymm (le_trans (comp_mono_right (dom_coreflexive R) R)
    (by rw [Cat.id_comp]; exact le_refl R)) (le_dom_comp R)

/-- `Simple (E ≫ F)` when `E` is coreflexive and `F` simple
    (E°E ⊑ 1 so (EF)°(EF) = F°(E°E)F ⊑ F°F ⊑ 1). -/
public theorem simple_coref_comp {A C : 𝒜} {E : C ⟶ C} {F : C ⟶ A}
    (hE : Coreflexive E) (hF : Simple F) : Simple (E ≫ F) := by
  dsimp [Simple]
  have hErec : E° ⊑ Cat.id C := by have := recip_mono hE; rwa [recip_id] at this
  have hEE : E° ≫ E ⊑ Cat.id C := by
    have h1 := comp_mono_right hErec E
    rw [Cat.id_comp] at h1
    exact le_trans h1 hE
  have hstep : (E ≫ F)° ≫ (E ≫ F) ⊑ F° ≫ F := by
    have e1 : (E ≫ F)° ≫ (E ≫ F) = F° ≫ ((E° ≫ E) ≫ F) := by
      rw [Allegory.recip_comp, Cat.assoc, ← Cat.assoc E° E F]
    rw [e1]
    calc F° ≫ ((E° ≫ E) ≫ F)
        ⊑ F° ≫ (Cat.id C ≫ F) := comp_mono_left F° (comp_mono_right hEE F)
      _ = F° ≫ F := by rw [Cat.id_comp]
  exact le_trans hstep hF

/-- `R° ≫ dom R = R°` (recip of `dom_comp_self`). -/
theorem recip_comp_dom {A B : 𝒜} (R : A ⟶ B) : R° ≫ dom R = R° := by
  have := congrArg (·°) (dom_comp_self R)
  simpa [Allegory.recip_comp, dom_recip] using this

/-- Domains commute: dom F ≫ dom G = dom G ≫ dom F. -/
theorem dom_comm {A b₁ b₂ : 𝒜} (F : A ⟶ b₁) (G : A ⟶ b₂) :
    dom F ≫ dom G = dom G ≫ dom F :=
  (coreflexive_comp_eq_inter (dom_coreflexive F) (dom_coreflexive G)).trans
    ((Allegory.inter_comm _ _).trans
      (coreflexive_comp_eq_inter (dom_coreflexive G) (dom_coreflexive F)).symm)

/-- Coreflexive sandwich: for coreflexive `E`, `1 ∩ (E ≫ X ≫ E°) = E ∩ X`. -/
theorem coref_sandwich {C : 𝒜} (E : C ⟶ C) (X : C ⟶ C) (hE : Coreflexive E) :
    Cat.id C ∩ (E ≫ X ≫ E°) = E ∩ X := by
  have hEsym : E° = E := symmetric_eq (coreflexive_symmetric_idempotent hE).1
  have hEidem : E ≫ E = E := (coreflexive_symmetric_idempotent hE).2
  apply le_antisymm
  · apply le_inter
    · -- ⊑ E : modular on (E≫X) ≫ E°  ⟹  ((E≫X) ∩ E) ≫ E° ⊑ E≫E° = E
      have hm := modular_le (E ≫ X) E° (Cat.id C)
      have heq : Cat.id C ∩ (E ≫ X ≫ E°) = (E ≫ X) ≫ E° ∩ Cat.id C := by
        rw [Allegory.inter_comm, ← Cat.assoc]
      rw [heq]
      refine le_trans hm ?_
      have hEE' : E ≫ E° = E := by rw [hEsym, hEidem]
      have hfac : (E ≫ X ∩ Cat.id C ≫ E°°) ⊑ E := by
        refine le_trans (inter_lb_right _ _) ?_
        rw [Cat.id_comp, Allegory.recip_recip]; exact le_refl E
      exact le_trans (comp_mono_right hfac E°) (by rw [hEE']; exact le_refl E)
    · -- ⊑ X : E X E° ⊑ 1·X·1 = X
      refine le_trans (inter_lb_right _ _) ?_
      calc E ≫ X ≫ E°
          ⊑ Cat.id C ≫ X ≫ Cat.id C := by
            refine le_trans (comp_mono_right hE _) ?_
            exact comp_mono_left _ (comp_mono_left X (by rw [hEsym]; exact hE))
        _ = X := by rw [Cat.id_comp, Cat.comp_id]
  · apply le_inter
    · exact le_trans (inter_lb_left _ _) hE
    · -- E ∩ X ⊑ E X E°: C := E∩X coreflexive, C = C C C ⊑ E X E°
      have hC : Coreflexive (E ∩ X) := le_trans (inter_lb_left _ _) hE
      have hCidem : (E ∩ X) ≫ (E ∩ X) = E ∩ X := (coreflexive_symmetric_idempotent hC).2
      calc E ∩ X
          = (E ∩ X) ≫ (E ∩ X) ≫ (E ∩ X) := by rw [hCidem, hCidem]
        _ ⊑ E ≫ X ≫ E° := by
            refine le_trans (comp_mono_right (inter_lb_left _ _) _) ?_
            refine comp_mono_left E ?_
            refine le_trans (comp_mono_right (inter_lb_right _ _) _) ?_
            refine comp_mono_left X ?_
            rw [hEsym]; exact inter_lb_left _ _

/-- `dom (E ≫ F) = E ∩ dom F` for coreflexive `E` (instance of `coref_sandwich`). -/
theorem dom_coref_comp {A C : 𝒜} (E : C ⟶ C) (F : C ⟶ A) (hE : Coreflexive E) :
    dom (E ≫ F) = E ∩ dom F := by
  have hEsym : E° = E := symmetric_eq (coreflexive_symmetric_idempotent hE).1
  -- RHS: E ∩ dom F = E ∩ (F ≫ F°), since E ⊑ 1
  have hrhs : E ∩ dom F = E ∩ (F ≫ F°) := by
    have hE1 : E ∩ Cat.id C = E := le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hE)
    dsimp [dom]; rw [Allegory.inter_assoc, hE1]
  rw [hrhs]
  -- LHS: dom(E≫F) = 1 ∩ E≫(F≫F°)≫E°
  dsimp [dom]
  have lhs_eq : (E ≫ F) ≫ (E ≫ F)° = E ≫ (F ≫ F°) ≫ E° := by
    rw [Allegory.recip_comp, Cat.assoc, ← Cat.assoc F F° E°]
  rw [lhs_eq]
  exact coref_sandwich E (F ≫ F°) hE

/-- §2.225 property (faithful to Freyd §2.16(10): "R is SEMI-SIMPLE if there
    exist simple F, G such that R = F°G").  A morphism `R` is the UNION of the
    semisimple morphisms it contains, encoded by its universal property: any `X`
    (parallel to `R`) dominating every book-semisimple piece `F° ≫ G` (F, G
    simple) contained in `R` also dominates `R`.  (`R` is the least upper bound
    of its semisimple parts.)

    Freyd states §2.353 only "for division allegories in which every morphism is
    the union of the semisimple morphisms it contains [2.225]"; this is the
    exact hypothesis, taken as a parameter because arbitrary unions / local
    completeness are not part of the bare `DivisionAllegory` interface.

    NOTE: the §2.16(10) book definition of semisimple is `F°G` (F, G simple),
    which is what the §2.353 reduction quantifies over; we use that form here
    directly. -/
def UnionOfSemiSimple {A : 𝒜} (R : A ⟶ A) : Prop :=
  ∀ X : A ⟶ A,
    (∀ {C : 𝒜} (F G : C ⟶ A), Simple F → Simple G → F° ≫ G ⊑ R → F° ≫ G ⊑ X) →
    R ⊑ X

/-- Converse of `straight_cancel` (§2.353).  Given the §2.225 hypothesis that
    `S /ₛ S` is the union of the (book-)semisimple morphisms it contains, and
    that `FS = GS → (dom F)G = (dom G)F` for all simple F, G of the same source
    and target, then `S` is straight.

    Proof (Freyd §2.353).  By §2.225 it suffices to show `F°G ⊑ 1` for all
    simple F, G with `F°G ⊑ S/ₛS`.  Set `F' = (dom G)F`, `G' = (dom F)G`.  Then
    `dom F' = dom G'` (`dom_coref_comp` + `dom_comm`), `F'°G' = F°G`, and
    `F'S = G'S` (using `F°G ⊑ S/ₛS`).  The hypothesis `h` gives
    `(dom F')G' = (dom G')F'`; with `dom F' = dom G'` this forces `F' = G'`,
    whence `F°G = F'°G' = F'°F' ⊑ 1` by simplicity of `F'`. -/
theorem straight_of_cancel {A B : 𝒜} {S : A ⟶ B}
    (hUnion : UnionOfSemiSimple (S /ₛ S))
    (h : ∀ {C : 𝒜} (F G : C ⟶ A),
        Simple F → Simple G → F ≫ S = G ≫ S → dom F ≫ G = dom G ≫ F) :
    Straight S := by
  -- §2.225 reduction: suffices F°G ⊑ 1 for all simple F, G with F°G ⊑ S/ₛS.
  refine hUnion (Cat.id A) ?_
  intro C F G hF hG hFGle
  -- F' = (dom G) F, G' = (dom F) G.  Both simple.
  -- (no `set`/`let`: this file is mathlib-free; use explicit abbreviations.)
  obtain ⟨F', hF'⟩ : ∃ F', F' = dom G ≫ F := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G', G' = dom F ≫ G := ⟨_, rfl⟩
  have hF'simple : Simple F' := hF' ▸ simple_coref_comp (dom_coreflexive G) hF
  have hG'simple : Simple G' := hG' ▸ simple_coref_comp (dom_coreflexive F) hG
  -- dom F' = dom G' = dom F ∩ dom G.
  have hdomF' : dom F' = dom G ∩ dom F := by rw [hF', dom_coref_comp _ _ (dom_coreflexive G)]
  have hdomG' : dom G' = dom F ∩ dom G := by rw [hG', dom_coref_comp _ _ (dom_coreflexive F)]
  have hdomEq : dom F' = dom G' := by rw [hdomF', hdomG', Allegory.inter_comm]
  -- F'°G' = F°G.
  have hF'G' : F'° ≫ G' = F° ≫ G := by
    rw [hF', hG', Allegory.recip_comp, dom_recip]
    calc (F° ≫ dom G) ≫ (dom F ≫ G)
        = F° ≫ (dom G ≫ dom F) ≫ G := by
          rw [Cat.assoc, Cat.assoc, ← Cat.assoc (dom G) (dom F) G]
      _ = F° ≫ (dom F ≫ dom G) ≫ G := by rw [dom_comm]
      _ = (F° ≫ dom F) ≫ (dom G ≫ G) := by
          rw [Cat.assoc, Cat.assoc, ← Cat.assoc (dom F) (dom G) G]
      _ = F° ≫ G := by rw [recip_comp_dom, dom_comp_self]
  -- F'S = G'S, using F°G ⊑ S/ₛS.
  -- (S/ₛS)S ⊑ S.
  have hssS : (S /ₛ S) ≫ S ⊑ S := ((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1
  -- F'°G' ⊑ S/ₛS and G'°F' ⊑ S/ₛS (the latter by symmetry of S/ₛS).
  have hF'G'le : F'° ≫ G' ⊑ S /ₛ S := by rw [hF'G']; exact hFGle
  have hG'F'le : G'° ≫ F' ⊑ S /ₛ S := by
    have hsym : (S /ₛ S)° ⊑ S /ₛ S := symmDiv_self_symmetric (S)
    have : (F'° ≫ G')° ⊑ (S /ₛ S)° := recip_mono hF'G'le
    rw [Allegory.recip_comp, Allegory.recip_recip] at this
    exact le_trans this hsym
  -- domain restriction: G' = dom F' ≫ G' ⊑ (F' ≫ F'°) ≫ G'.
  have hdomle : dom F' ⊑ F' ≫ F'° := inter_lb_right _ _
  have hG'restrict : G' ⊑ (F' ≫ F'°) ≫ G' :=
    calc G' = dom F' ≫ G' := by rw [hdomEq, dom_comp_self]
      _ ⊑ (F' ≫ F'°) ≫ G' := comp_mono_right hdomle G'
  have hF'restrict : F' ⊑ (G' ≫ G'°) ≫ F' :=
    calc F' = dom G' ≫ F' := by rw [← hdomEq, dom_comp_self]
      _ ⊑ (G' ≫ G'°) ≫ F' := comp_mono_right (inter_lb_right _ _) F'
  have hF'S : F' ≫ S = G' ≫ S := by
    apply le_antisymm
    · -- F'S ⊑ G'S : F'S ⊑ (G'G'°)F'S = G'(G'°F')S ⊑ G'(S/ₛS)S ⊑ G'S
      have c1 : F' ≫ S ⊑ ((G' ≫ G'°) ≫ F') ≫ S := comp_mono_right hF'restrict S
      have c2 : ((G' ≫ G'°) ≫ F') ≫ S = G' ≫ ((G'° ≫ F') ≫ S) := by
        rw [Cat.assoc, Cat.assoc, ← Cat.assoc G'° F' S]
      have c3 : G' ≫ ((G'° ≫ F') ≫ S) ⊑ G' ≫ ((S /ₛ S) ≫ S) :=
        comp_mono_left G' (comp_mono_right hG'F'le S)
      have c4 : G' ≫ ((S /ₛ S) ≫ S) ⊑ G' ≫ S := comp_mono_left G' hssS
      exact le_trans c1 (by rw [c2]; exact le_trans c3 c4)
    · -- G'S ⊑ F'S : symmetric
      have c1 : G' ≫ S ⊑ ((F' ≫ F'°) ≫ G') ≫ S := comp_mono_right hG'restrict S
      have c2 : ((F' ≫ F'°) ≫ G') ≫ S = F' ≫ ((F'° ≫ G') ≫ S) := by
        rw [Cat.assoc, Cat.assoc, ← Cat.assoc F'° G' S]
      have c3 : F' ≫ ((F'° ≫ G') ≫ S) ⊑ F' ≫ ((S /ₛ S) ≫ S) :=
        comp_mono_left F' (comp_mono_right hF'G'le S)
      have c4 : F' ≫ ((S /ₛ S) ≫ S) ⊑ F' ≫ S := comp_mono_left F' hssS
      exact le_trans c1 (by rw [c2]; exact le_trans c3 c4)
  -- By h: dom F' ≫ G' = dom G' ≫ F'.  With dom F' = dom G', get F' = G'.
  have hcancel := h F' G' hF'simple hG'simple hF'S
  have hFG'eq : F' = G' := by
    have e1 : F' = dom F' ≫ F' := (dom_comp_self F').symm
    have e2 : G' = dom G' ≫ G' := (dom_comp_self G').symm
    calc F' = dom F' ≫ F' := e1
      _ = dom G' ≫ F' := by rw [hdomEq]
      _ = dom F' ≫ G' := by rw [← hcancel, hdomEq]
      _ = dom G' ≫ G' := by rw [hdomEq]
      _ = G' := e2.symm
  -- F°G = F'°G' = F'°F' ⊑ 1 (F' simple).
  calc F° ≫ G = F'° ≫ G' := hF'G'.symm
    _ = F'° ≫ F' := by rw [hFG'eq]
    _ ⊑ Cat.id A := hF'simple

/-! ## §2.355  If SR is straight then S is straight -/

/-- If SR is straight then S is straight (§2.355).
    Proof: S/ₛS ⊑ (SR)/ₛ(SR) ⊑ 1. -/
public theorem straight_of_comp_straight {A B C : 𝒜} {S : A ⟶ B} {R : B ⟶ C}
    (h : Straight (S ≫ R)) : Straight S := by
  apply le_trans _ h
  -- Show S/ₛS ⊑ (SR)/ₛ(SR): need (S/ₛS)(SR) ⊑ SR and (S/ₛS)°(SR) ⊑ SR.
  rw [le_symmDiv_iff (S /ₛ S) (S ≫ R) (S ≫ R)]
  have hss_le : (S /ₛ S) ≫ S ⊑ S := ((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1
  constructor
  · -- (S/ₛS)(SR) = ((S/ₛS)S)R ⊑ SR
    rw [← Cat.assoc]; exact comp_mono_right hss_le R
  · -- (S/ₛS)°(SR) ⊑ SR: (S/ₛS)° ⊑ S/ₛS so (S/ₛS)°S ⊑ (S/ₛS)S ⊑ S
    have h_sym : (S /ₛ S)° ⊑ S /ₛ S := symmDiv_self_symmetric S
    have hss_sym_le : (S /ₛ S)° ≫ S ⊑ S := le_trans (comp_mono_right h_sym S) hss_le
    rw [← Cat.assoc]; exact comp_mono_right hss_sym_le R

/-- Right-invertible morphisms are straight (§2.355). -/
public theorem rightInvertible_straight {A B : 𝒜} {S : A ⟶ B} {T : B ⟶ A}
    (h : S ≫ T = Cat.id A) : Straight S := by
  -- S(ST) = (SS)T? No. Use: ST = 1, so straight_of_comp_straight with R=T.
  -- Need Straight (S ≫ T). Since S ≫ T = Cat.id a and Cat.id a is straight, done.
  have h1_straight : Straight (S ≫ T) := by
    rw [h]
    -- Straight (Cat.id a): 1/ₛ1 = (1/1) ∩ (1/1)° = 1 ∩ 1° = 1 ∩ 1 ⊑ 1
    dsimp [Straight, le, symmDiv]
    rw [div_one, recip_id]
    simp [Allegory.inter_idem]
  exact straight_of_comp_straight h1_straight

/-! ## §2.356  If S is straight then R/ₛS is simple -/

/-- If S is straight then R/ₛS is simple (§2.356).
    Proof: (R/ₛS)°(R/ₛS) ⊑ S/ₛS ⊑ 1. -/
public theorem straight_symmDiv_simple {A B C : 𝒜} {S : B ⟶ C} (hS : Straight S)
    (R : A ⟶ C) : Simple (R /ₛ S) := by
  dsimp [Simple]
  apply le_trans _ hS
  rw [le_symmDiv_iff]
  -- Let T := (R/ₛS)°(R/ₛS). T° = T (symmetric). TS ⊑ S.
  -- (R/ₛS)S ⊑ R and (R/ₛS)°R ⊑ S, from le_symmDiv for T = R/ₛS.
  have hRS_le : (R /ₛ S) ≫ S ⊑ R := ((le_symmDiv_iff _ _ _).mp (le_refl _)).1
  have hRS_rec : (R /ₛ S)° ≫ R ⊑ S := ((le_symmDiv_iff _ _ _).mp (le_refl _)).2
  constructor
  · -- ((R/ₛS)°(R/ₛS))S ⊑ (R/ₛS)°R ⊑ S
    rw [Cat.assoc]; exact le_trans (comp_mono_left _ hRS_le) hRS_rec
  · -- ((R/ₛS)°(R/ₛS))° ≫ S ⊑ S.
    -- T := (R/ₛS)°(R/ₛS). T° = (R/ₛS)°(R/ₛS)°° = (R/ₛS)°(R/ₛS) = T.
    -- So T° ≫ S = T ≫ S ⊑ S (same as first bullet).
    -- In Lean, ((R/ₛS)° ≫ R/ₛS)° = (R/ₛS)° ≫ (R/ₛS)°° = (R/ₛS)° ≫ R/ₛS.
    -- After rw [recip_comp, recip_recip], goal: (R/ₛS)° ≫ (R/ₛS) ≫ S ⊑ S.
    -- That IS the first bullet (same expression, just associativity).
    rw [Allegory.recip_comp, Allegory.recip_recip]
    -- goal: ((R/ₛS)° ≫ R/ₛS) ≫ S ⊑ S (same as first bullet after assoc)
    exact le_trans (Cat.assoc (R /ₛ S)° (R /ₛ S) S ▸ comp_mono_left _ hRS_le) hRS_rec

/-! ## §2.357  Simple part and domain of simplicity -/

/-- The SIMPLE PART of R: R/ₛ1 (§2.357).
    T ⊑ R/ₛ1 iff T ⊑ R and T°R ⊑ 1 (simplicity of T, contained in R). -/
@[expose] public def simplePart {A B : 𝒜} (R : A ⟶ B) : A ⟶ B := R /ₛ Cat.id B

/-- The DOMAIN OF SIMPLICITY of R: dom(R/ₛ1) (§2.357). -/
@[expose] public def domSimplicity {A B : 𝒜} (R : A ⟶ B) : A ⟶ A := dom (simplePart R)

/-- The simple part is simple (§2.357).
    1_b is straight (right-invertible), so R/ₛ1 is simple by §2.356. -/
theorem simplePart_simple {A B : 𝒜} (R : A ⟶ B) : Simple (simplePart R) := by
  apply straight_symmDiv_simple
  exact rightInvertible_straight (Cat.comp_id (Cat.id B))

/-- The simple part is contained in R: R/ₛ1 ⊑ R (§2.357). -/
public theorem simplePart_le {A B : 𝒜} (R : A ⟶ B) : simplePart R ⊑ R := by
  dsimp [simplePart, symmDiv]
  calc (R / Cat.id B) ∩ ((Cat.id B / R)°) ⊑ R / Cat.id B := inter_lb_left _ _
      _ = R := div_one R

/-- `1 ∩ M = 1 ∩ M°`: the intersection-with-identity is coreflexive, hence symmetric, so it
    equals its own reciprocal `1 ∩ M°` (`(1∩M)° = 1° ∩ M° = 1 ∩ M°`). -/
theorem one_inter_eq_one_inter_recip {A : 𝒜} (M : A ⟶ A) :
    Cat.id A ∩ M = Cat.id A ∩ M° := by
  have hsym : (Cat.id A ∩ M)° = Cat.id A ∩ M :=
    symmetric_eq (coreflexive_symmetric_idempotent (inter_lb_left (Cat.id A) M)).1
  rw [Allegory.recip_inter, recip_id] at hsym
  exact hsym.symm

/-- **§2.357**: `Dom(R/ₛS) = 1 ∩ (R/S)(S/R)`.  Unfold `R/ₛS = (R/S) ∩ (S/R)°`, apply `dom_inter`,
    then `(S/R)°(R/S)° = ((R/S)(S/R))°` (`recip_comp`) and `1 ∩ X° = 1 ∩ X`. -/
theorem dom_symmDiv {A B C : 𝒜} (R : A ⟶ C) (S : B ⟶ C) :
    dom (R /ₛ S) = Cat.id A ∩ (R / S) ≫ (S / R) := by
  dsimp only [symmDiv]
  rw [dom_inter, ← Allegory.recip_comp, ← one_inter_eq_one_inter_recip]

/-- **§2.357**: `Dom(R/ₛ1) = 1 ∩ R(1/R)` — the DOMAIN OF SIMPLICITY of `R`.  The `S = 1` case of
    `dom_symmDiv`, simplified by `R/1 = R`. -/
theorem domSimplicity_eq {A B : 𝒜} (R : A ⟶ B) :
    domSimplicity R = Cat.id A ∩ R ≫ (Cat.id B / R) := by
  dsimp only [domSimplicity, simplePart]
  rw [dom_symmDiv, div_one]

/-- R/ₛ1 is the largest simple AR with A coreflexive (§2.357).
    Here the "simple" condition on AR is expressed directly as the
    symmDiv characterization: AR ⊑ R and (AR)°R ⊑ 1.
    (The book's proof of the equivalence with Simple uses A°A = A for coreflexive A.) -/
public theorem simplePart_largest {a B : 𝒜} (R : a ⟶ B) (A : a ⟶ a)
    (hA : Coreflexive A) (hAR : (A ≫ R)° ≫ R ⊑ Cat.id B) :
    A ≫ R ⊑ simplePart R := by
  dsimp [simplePart]
  rw [le_symmDiv_iff (A ≫ R) R (Cat.id B)]
  constructor
  · -- (AR) ≫ 1 ⊑ R: AR ⊑ R since A ⊑ 1
    rw [Cat.comp_id]
    exact le_trans (comp_mono_right hA R) (by rw [Cat.id_comp]; exact le_refl R)
  · exact hAR

/-! ## §2.315(a)  Every locally complete distributive allegory is a division allegory

  In a `LocallyCompleteDistributiveAllegory` the right adjoint to `(-) ≫ S`
  exists as a supremum: `R / S := ⊔ {T | T ≫ S ⊑ R}`.  The two `DivisionAllegory`
  fields then follow from `Sup_le`/`le_Sup`.  (`div_comp_le` needs that composition
  on the *right* distributes over `Sup`; we get that by reciprocating the left
  distributivity `comp_Sup_distrib`.) -/

section LCDADivision

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]

/-- Reciprocation commutes with `Sup`: `(Sup P)° = Sup {R° | P R}`.
    Reciprocation is an order-isomorphism, so it carries suprema to suprema. -/
public theorem recip_Sup {A B : 𝒜} (P : (A ⟶ B) → Prop) :
    (Sup P)° = Sup (fun T : B ⟶ A => ∃ R, P R ∧ T = R°) := by
  apply le_antisymm
  · -- (Sup P)° ⊑ Sup Pᵒ  ↔  Sup P ⊑ (Sup Pᵒ)°  (recip adjoint); then Sup_le pointwise.
    apply recip_le_iff.mpr
    apply Sup_le; intro R hR
    -- R ⊑ (Sup Pᵒ)°  ↔  R° ⊑ Sup Pᵒ, and R° is a member of Pᵒ.
    exact recip_le_iff.mp (le_Sup ⟨R, hR, rfl⟩)
  · -- Sup Pᵒ ⊑ (Sup P)°: each member R° ⊑ (Sup P)° since R ⊑ Sup P.
    apply Sup_le; intro T ⟨R, hR, hT⟩
    subst hT; exact recip_mono (le_Sup hR)

/-- Composition on the right distributes over `Sup`: `(Sup P) ≫ S = ⊔ {T ≫ S | P T}`.
    Derived from the left law `comp_Sup_distrib` by reciprocation. -/
public theorem Sup_comp_distrib {A B C : 𝒜} (P : (A ⟶ B) → Prop) (S : B ⟶ C) :
    Sup P ≫ S = Sup (fun T : A ⟶ C => ∃ R, P R ∧ T = R ≫ S) := by
  apply le_antisymm
  · -- (Sup P)S ⊑ ⊔{RS}.  Reciprocate both sides: ((Sup P)S)° ⊑ (⊔{RS})°, i.e.
    -- S°(Sup P)° ⊑ (⊔{RS})°.
    have key : (Sup P ≫ S)° ⊑ (Sup (fun T : A ⟶ C => ∃ R, P R ∧ T = R ≫ S))° := by
      rw [Allegory.recip_comp, recip_Sup, comp_Sup_distrib]
      apply Sup_le; intro U ⟨T, ⟨R, hR, hT⟩, hU⟩
      subst hT; subst hU
      -- S° ≫ R° = (R ≫ S)° ⊑ (⊔{RS})°  since R ≫ S is a member.
      rw [← Allegory.recip_comp]
      have hmem : (fun T : A ⟶ C => ∃ R', P R' ∧ T = R' ≫ S) (R ≫ S) := ⟨R, hR, rfl⟩
      exact recip_mono (le_Sup hmem)
    have := recip_mono key
    rwa [Allegory.recip_recip, Allegory.recip_recip] at this
  · -- ⊔{RS} ⊑ (Sup P)S: each RS ⊑ (Sup P)S since R ⊑ Sup P.
    apply Sup_le; intro T ⟨R, hR, hT⟩
    subst hT; exact comp_mono_right (le_Sup hR) S

/-- Right division in a locally complete distributive allegory: `R / S := ⊔ {T | T ≫ S ⊑ R}`. -/
@[expose] public def lcdaDiv {A B C : 𝒜} (R : A ⟶ C) (S : B ⟶ C) : A ⟶ B :=
  Sup (fun T : A ⟶ B => T ≫ S ⊑ R)

/-- The semi-commutative triangle `(R / S) ≫ S ⊑ R` (§2.31 field). -/
public theorem lcdaDiv_comp_le {A B C : 𝒜} (R : A ⟶ C) (S : B ⟶ C) : lcdaDiv R S ≫ S ⊑ R := by
  rw [lcdaDiv, Sup_comp_distrib]
  apply Sup_le; intro T ⟨U, hU, hT⟩
  subst hT; exact hU

/-- The adjointness `T ≫ S ⊑ R → T ⊑ R / S` (§2.31 field). -/
public theorem le_lcdaDiv {A B C : 𝒜} (T : A ⟶ B) (R : A ⟶ C) (S : B ⟶ C) (h : T ≫ S ⊑ R) :
    T ⊑ lcdaDiv R S :=
  le_Sup h

/-- (§2.315a) A locally complete distributive allegory is a division allegory, with
    `R / S = ⊔ {T | T ≫ S ⊑ R}`.  Provided as a `def` (not a global instance) to avoid a
    typeclass-resolution loop: `DivisionAllegory` extends `DistributiveAllegory`, so a global
    instance here would give `DistributiveAllegory X` two derivations (direct, and via this).
    Apply with `letI`/`@`. -/
@[expose] public def divisionAllegoryLCDA : DivisionAllegory 𝒜 :=
  { (inferInstance : LocallyCompleteDistributiveAllegory 𝒜).toDistributiveAllegory with
    div         := fun R S => lcdaDiv R S
    div_comp_le := fun R S => lcdaDiv_comp_le R S
    le_div      := fun T R S h => le_lcdaDiv T R S h }

end LCDADivision

/-! ## §2.315  Division allegory → locally complete distributive allegory

  Any division allegory is faithfully representable in a locally complete
  distributive allegory, and thus in a globally complete allegory.

  (Proof sketch: R/S is constructible as ⊔{T | TS ⊑ R} in the local completion;
  the local-completion embedding A → Â is faithful; and a globally complete
  allegory subsumes locally complete.) -/

-- BOOK §2.315: Any division allegory is faithfully representable in a locally complete
-- distributive allegory, and thus in a globally complete allegory.
-- STATUS: DONE.
-- The local completion `Â = Downdeal 𝒜` (ideals of A-homs, S2_2.lean) is a
-- `LocallyCompleteDistributiveAllegory`; by §2.315(a) every LCDA is a `DivisionAllegory`.
-- The principal-ideal embedding `R ↦ ↓R = DowndealHom.prin R` preserves ≫/°/∩/∪/𝟘 and is
-- injective (`DowndealHom.prin_*`).  The headline `divisionAllegory_faithful_in_lcda`
-- packages this.

section Representation

/-- (§2.315) **Any division allegory is faithfully representable in a locally complete
    distributive allegory** (which is, by §2.315(a), itself a division allegory).

    Concretely: for any `DistributiveAllegory ℬ` — in particular any `DivisionAllegory` —
    the local completion `B̂ = Downdeal ℬ` is a `LocallyCompleteDistributiveAllegory` (hence a
    `DivisionAllegory` via `divisionAllegoryLCDA`), and the principal-ideal embedding
    `R ↦ ↓R` is a faithful homomorphism: injective and preserving `≫`, `°`, `∩`, `∪`, `𝟘`.
    (Fresh type variable `ℬ` avoids the file-level `[DivisionAllegory 𝒜]`, which would make
    the base `DistributiveAllegory` ambiguous.) -/
theorem divisionAllegory_faithful_in_lcda {ℬ : Type u} [hℬ : DistributiveAllegory.{u, u} ℬ] :
    -- B̂ is locally complete distributive (and so a division allegory):
    Nonempty (LocallyCompleteDistributiveAllegory.{u, u} (Downdeal ℬ)) ∧
    Nonempty (DivisionAllegory.{u, u} (Downdeal ℬ)) ∧
    -- the embedding R ↦ ↓R is faithful:
    (∀ {A B : ℬ} {R S : A ⟶ B}, DowndealHom.prin R = DowndealHom.prin S → R = S) ∧
    -- and preserves every operation:
    (∀ {A B C : ℬ} (R : A ⟶ B) (S : B ⟶ C),
      DowndealHom.prin (R ≫ S) = DowndealHom.comp (DowndealHom.prin R) (DowndealHom.prin S)) ∧
    (∀ {A B : ℬ} (R : A ⟶ B), DowndealHom.prin (R°) = DowndealHom.recip (DowndealHom.prin R)) ∧
    (∀ {A B : ℬ} (R S : A ⟶ B),
      DowndealHom.prin (R ∩ S) = DowndealHom.inter (DowndealHom.prin R) (DowndealHom.prin S)) ∧
    (∀ {A B : ℬ} (R S : A ⟶ B),
      DowndealHom.prin (R ∪ S) = DowndealHom.union (DowndealHom.prin R) (DowndealHom.prin S)) :=
  by
  letI inst : LocallyCompleteDistributiveAllegory (Downdeal ℬ) :=
    @instLocallyCompleteDistributiveAllegoryDowndealHom ℬ hℬ
  exact ⟨⟨inst⟩, ⟨@divisionAllegoryLCDA (Downdeal ℬ) inst⟩,
    DowndealHom.prin_injective, DowndealHom.prin_comp, DowndealHom.prin_recip,
    DowndealHom.prin_inter, DowndealHom.prin_union⟩

end Representation

/-! ## §2.316 (final paragraph)  The full hom-poset `(a,a)` is a Heyting algebra

  In a TABULAR UNITARY division allegory, tabulate the maximal morphism `⊤ : a → a`
  by maps `ℓ₁, ℓ₂ : γ → a`.  Then `(a,a) ≅ Cor(γ)` via `R ↦ 1_γ ∩ ℓ₁ R ℓ₂°`, with
  inverse `c ↦ ℓ₁° c ℓ₂`.  Transporting the Cor(γ) Heyting arrow (`heyting_adj_coref`)
  across this order-iso makes `(a,a)` a Heyting algebra.  We need exactly the special
  arrow `1 → A` (largest `H` with `H ∩ 1 ⊑ A`), used in §2.32 to right-adjoin `f#`. -/

/-- A **TABULAR UNITARY DIVISION ALLEGORY** (§2.316/§2.32): combines `TabularAllegory`,
    `UnitaryAllegory` and `DivisionAllegory` in a SINGLE class so their shared `Allegory`
    grandparent is merged into ONE `toAllegory` field (the diamond-safe inheritance pattern;
    `DivisionAllegory` brings `DistributiveAllegory`, hence `∪`/`𝟘`).  This is exactly the
    hypothesis under which `Mσn(𝒜)` is a logos (§2.32). -/
public class TabularUnitaryDivisionAllegory (𝒜 : Type u) extends
    TabularAllegory 𝒜, UnitaryAllegory 𝒜, DivisionAllegory 𝒜

section HeytingHom
variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜]

-- Named by DIVISION, not by the book's `p_a ≫ p_b°` (§2.152): the unit projection exists only
-- as `∃`, so choosing one would put `Classical.choice` under every `RelProd`-typed statement.
/-- The maximal morphism `⊤ : a → b`: `𝟘/𝟘`, which by §2.31's adjointness is above every
    `R : a ⟶ b`, since `R ≫ 𝟘 = 𝟘`.  It equals the book's `p_a ≫ p_b°` by `unit_proj_max`. -/
@[expose] public def topMor (A B : 𝒜) : A ⟶ B := (𝟘 : A ⟶ B) / (𝟘 : B ⟶ B)

public theorem topMor_max {A B : 𝒜} (R : A ⟶ B) : R ⊑ topMor A B :=
  (le_div_iff R _ _).mpr (by rw [DistributiveAllegory.comp_zero]; exact le_refl _)

/-- A chosen tabulation `(ℓ₁, ℓ₂) : γ → a` of the maximal morphism `⊤ : a → a`. -/
@[expose] public noncomputable def topTab (A : 𝒜) : Σ γ : 𝒜, (γ ⟶ A) × (γ ⟶ A) :=
  ⟨(TabularAllegory.tabular (topMor A A)).choose,
   ((TabularAllegory.tabular (topMor A A)).choose_spec.choose,
    (TabularAllegory.tabular (topMor A A)).choose_spec.choose_spec.choose)⟩

/-- `Φ : (a,a) → Cor(γ)` sends `R` to `1_γ ∩ ℓ₁ R ℓ₂°`. -/
@[expose] public noncomputable def phiCor {A : 𝒜} (R : A ⟶ A) : (topTab A).1 ⟶ (topTab A).1 :=
  Cat.id (topTab A).1 ∩ ((topTab A).2.1 ≫ R ≫ (topTab A).2.2°)

/-- `Ψ : Cor(γ) → (a,a)` sends `c` to `ℓ₁° c ℓ₂`. -/
@[expose] public noncomputable def psiCor {A : 𝒜} (c : (topTab A).1 ⟶ (topTab A).1) : A ⟶ A :=
  (topTab A).2.1° ≫ c ≫ (topTab A).2.2

-- (The dual modular law `(R≫S) ∩ T ⊑ R ≫ (S ∩ R°≫T)` is `modular_le_right` from A4_1,
--  which needs only `[Allegory 𝒜]`; the over-scoped local copy `modular_le'` was deduped.)

/-- **Tabulation recovery**: if `(f, g)` are maps from `γ` with `f° ≫ g` maximal
    (so `R ⊑ f° ≫ g` for all `R : a → a`), then `R = f° ≫ (1_γ ∩ f ≫ R ≫ g°) ≫ g`.
    This is the recovery half of the order-iso `(a,a) ≅ Cor(γ)`. -/
public theorem tab_recover {A γ : 𝒜} {R : A ⟶ A} {f g : γ ⟶ A} (hfm : Map f) (hgm : Map g)
    (htop : R ⊑ f° ≫ g) :
    f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) ≫ g = R := by
  have hfs : f° ≫ f ⊑ Cat.id A := hfm.2
  have hgs : g° ≫ g ⊑ Cat.id A := hgm.2
  apply le_antisymm
  · -- upper: f°(1∩fRg°)g ⊑ f°(fRg°)g = (f°f)R(g°g) ⊑ R
    have u1 : f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) ≫ g ⊑ f° ≫ (f ≫ R ≫ g°) ≫ g :=
      comp_mono_left _ (comp_mono_right (inter_lb_right _ _) g)
    have u2 : f° ≫ (f ≫ R ≫ g°) ≫ g = (f° ≫ f) ≫ R ≫ (g° ≫ g) := by simp [Cat.assoc]
    have u3 : (f° ≫ f) ≫ R ≫ (g° ≫ g) ⊑ R := by
      have := le_trans (comp_mono_right hfs _) (comp_mono_left _ (comp_mono_left R hgs))
      rwa [Cat.id_comp, Cat.comp_id] at this
    exact le_trans u1 (u2 ▸ u3)
  · -- lower: R ⊑ R ∩ f°g ⊑ (f° ∩ Rg°)g ⊑ f°(1∩fRg°)g
    have hReq : R = (f° ≫ g) ∩ R := by
      rw [Allegory.inter_comm]; exact (le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) htop)).symm
    have step2 : (f° ≫ g) ∩ R ⊑ (f° ∩ R ≫ g°) ≫ g := modular_le f° g R
    have step3 : (f° ∩ R ≫ g°) ⊑ f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) := by
      have h := modular_le_right f° (Cat.id γ) (R ≫ g°)
      rw [Cat.comp_id, Allegory.recip_recip] at h
      exact h
    have step4 : (f° ∩ R ≫ g°) ≫ g ⊑ (f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°)) ≫ g :=
      comp_mono_right step3 g
    have step5 : (f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°)) ≫ g = f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) ≫ g := by
      rw [Cat.assoc]
    calc R = (f° ≫ g) ∩ R := hReq
      _ ⊑ f° ≫ (Cat.id γ ∩ f ≫ R ≫ g°) ≫ g := le_trans step2 (step5 ▸ step4)

/-- **§2.316 crux**: `ψ(φ(R)) = R`. -/
public theorem psi_phi {A : 𝒜} (R : A ⟶ A) : psiCor (phiCor R) = R :=
  tab_recover (R := R)
    (TabularAllegory.tabular (topMor A A)).choose_spec.choose_spec.choose_spec.1
    (TabularAllegory.tabular (topMor A A)).choose_spec.choose_spec.choose_spec.2.1
    ((TabularAllegory.tabular (topMor A A)).choose_spec.choose_spec.choose_spec.2.2.1
      ▸ topMor_max R)

/-- **Tabulation co-recovery**: `φ(ψ(c)) = c` for coreflexive `c` on the apex `γ`, when
    `(f, g)` are maps with `f ≫ f° ∩ g ≫ g° = 1_γ` (jointly monic).  I.e.
    `1_γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g° = c`. -/
public theorem tab_corecover {A γ : 𝒜} {c : γ ⟶ γ} {f g : γ ⟶ A} (hfm : Map f) (hgm : Map g)
    (hjm : f ≫ f° ∩ g ≫ g° = Cat.id γ) (hc : Coreflexive c) :
    Cat.id γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g° = c := by
  have hfe : Cat.id γ ⊑ f ≫ f° := by
    have := hfm.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have hge : Cat.id γ ⊑ g ≫ g° := by
    have := hgm.1; rw [Entire, dom] at this; exact this ▸ inter_lb_right _ _
  have htab : Tabulates f g (f° ≫ g) := ⟨hfm, hgm, rfl, hjm⟩
  apply le_antisymm
  · -- 1 ∩ f(f°cg)g° ⊑ c.  Split c = e°e (e map, ee°=1), set x=ef, y=eg.
    obtain ⟨D, e, hem, hee, hee'⟩ := coreflexive_splits hc
    -- ψ(c) = f°cg = (ef)°(eg)
    have hpsi : f° ≫ c ≫ g = (e ≫ f)° ≫ (e ≫ g) := by
      rw [← hee, Allegory.recip_comp]; simp [Cat.assoc]
    -- mediating map H with Hf = ef, Hg = eg; by uniqueness H = e.
    have hxy : (e ≫ f)° ≫ (e ≫ g) ⊑ f° ≫ g := by
      rw [← hpsi]
      -- f°cg ⊑ f°g since c ⊑ 1
      have h1 : f° ≫ c ≫ g ⊑ f° ≫ Cat.id γ ≫ g := comp_mono_left f° (comp_mono_right hc g)
      rwa [Cat.id_comp] at h1
    obtain ⟨hHm, hHf, hHg⟩ :=
      tabulation_UP_forward_witness htab (map_comp hem hfm) (map_comp hem hgm) hxy
    -- explicit mediating map K = (ef)f° ∩ (eg)g°; K = e by uniqueness.
    have hKe : ((e ≫ f) ≫ f° ∩ (e ≫ g) ≫ g°) = e :=
      tabulation_UP_unique htab hHm hem hHf hHg
    -- recip: f(ef)° ∩ g(eg)° = e°.
    have hKrecip : (f ≫ (e ≫ f)° ∩ g ≫ (e ≫ g)°) = e° := by
      have := congrArg (·°) hKe
      simpa [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
        using this
    -- D = 1 ∩ (f(ef)°)≫((eg)g°);  modular ⟹ D ⊑ (f(ef)° ∩ g(eg)°)≫((eg)g°) = e°≫(eg≫g°).
    have hDle : Cat.id γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g° ⊑ c ≫ g ≫ g° := by
      have hgrp : f ≫ (f° ≫ c ≫ g) ≫ g° = (f ≫ (e ≫ f)°) ≫ ((e ≫ g) ≫ g°) := by
        rw [hpsi]; simp [Cat.assoc]
      rw [hgrp, Allegory.inter_comm]
      have hm := modular_le (f ≫ (e ≫ f)°) ((e ≫ g) ≫ g°) (Cat.id γ)
      -- hm : (f(ef)°)((eg)g°) ∩ 1 ⊑ (f(ef)° ∩ 1≫((eg)g°)°)≫((eg)g°)
      have hpr : Cat.id γ ≫ ((e ≫ g) ≫ g°)° = g ≫ (e ≫ g)° := by
        rw [Cat.id_comp, Allegory.recip_comp, Allegory.recip_recip]
      rw [hpr, hKrecip] at hm
      have hKval : e° ≫ ((e ≫ g) ≫ g°) = c ≫ g ≫ g° := by
        rw [← hee]; simp [Cat.assoc]
      rw [hKval] at hm
      exact hm
    -- D ⊑ 1 and D ⊑ c≫g≫g° ⟹ D ⊑ 1 ∩ c≫g≫g° ⊑ c≫(g≫g° ∩ c) = c≫c = c.
    have hfin : (Cat.id γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g°) ⊑ c := by
      have hD1 : (Cat.id γ ∩ f ≫ (f° ≫ c ≫ g) ≫ g°) ⊑ Cat.id γ := inter_lb_left _ _
      have hmeet := modular_le_right c (g ≫ g°) (Cat.id γ)
      -- (c≫gg°) ∩ 1 ⊑ c≫(gg° ∩ c°≫1) = c≫(gg° ∩ c)
      have hcc : g ≫ g° ∩ c° ≫ Cat.id γ = c := by
        have hcsym : c° = c := symmetric_eq (coreflexive_symmetric_idempotent hc).1
        rw [Cat.comp_id, hcsym, Allegory.inter_comm]
        exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) (le_trans hc hge))
      rw [hcc] at hmeet
      have hidem : c ≫ c = c := (coreflexive_symmetric_idempotent hc).2
      rw [hidem] at hmeet
      exact le_trans (le_inter hDle hD1) hmeet
    exact hfin
  · -- c ⊑ 1 ∩ f(f°cg)g° : c ⊑ 1 (coref) and c ⊑ f f° c g g° (entirety both sides).
    apply le_inter hc
    have l1 : c ⊑ (f ≫ f°) ≫ c := by
      have := comp_mono_right hfe c; rwa [Cat.id_comp] at this
    have l2 : (f ≫ f°) ≫ c ⊑ (f ≫ f°) ≫ c ≫ (g ≫ g°) := by
      apply comp_mono_left
      have := comp_mono_left c hge; rwa [Cat.comp_id] at this
    have hassoc : (f ≫ f°) ≫ c ≫ (g ≫ g°) = f ≫ (f° ≫ c ≫ g) ≫ g° := by
      simp [Cat.assoc]
    exact hassoc ▸ le_trans l1 l2

/-- `φ` is monotone. -/
public theorem phiCor_mono {A : 𝒜} {R S : A ⟶ A} (h : R ⊑ S) : phiCor R ⊑ phiCor S :=
  le_inter (inter_lb_left _ _)
    (le_trans (inter_lb_right _ _) (comp_mono_left _ (comp_mono_right h _)))

/-- `ψ` is monotone. -/
public theorem psiCor_mono {A : 𝒜} {c d : (topTab A).1 ⟶ (topTab A).1} (h : c ⊑ d) :
    psiCor c ⊑ psiCor d :=
  comp_mono_left _ (comp_mono_right h _)

/-- `φ(ψ(c)) = c` for coreflexive `c` (specialization of `tab_corecover` to the chosen
    tabulation of `⊤_a`). -/
public theorem phi_psi {A : 𝒜} {c : (topTab A).1 ⟶ (topTab A).1} (hc : Coreflexive c) :
    phiCor (psiCor c) = c :=
  tab_corecover
    (TabularAllegory.tabular (topMor A A)).choose_spec.choose_spec.choose_spec.1
    (TabularAllegory.tabular (topMor A A)).choose_spec.choose_spec.choose_spec.2.1
    (TabularAllegory.tabular (topMor A A)).choose_spec.choose_spec.choose_spec.2.2.2 hc

/-- `φ` reflects order: `φ(X) ⊑ φ(Y) ↔ X ⊑ Y` (an order-iso onto `Cor(γ)`). -/
public theorem phiCor_le_iff {A : 𝒜} (X Y : A ⟶ A) : phiCor X ⊑ phiCor Y ↔ X ⊑ Y := by
  constructor
  · intro h
    have := psiCor_mono h
    rwa [psi_phi, psi_phi] at this
  · exact phiCor_mono

/-- `ψ`-`φ` Galois iff for coreflexive targets: `Z ⊑ ψ(c) ↔ φ(Z) ⊑ c`. -/
public theorem le_psiCor_iff {A : 𝒜} (Z : A ⟶ A) {c : (topTab A).1 ⟶ (topTab A).1}
    (hc : Coreflexive c) : Z ⊑ psiCor c ↔ phiCor Z ⊑ c := by
  constructor
  · intro h
    have := phiCor_mono h
    rwa [phi_psi hc] at this
  · intro h
    have := psiCor_mono h
    rwa [psi_phi] at this

/-- `φ` preserves meets: `φ(X ∩ Y) = φ(X) ∩ φ(Y)`. -/
public theorem phiCor_inter {A : 𝒜} (X Y : A ⟶ A) : phiCor (X ∩ Y) = phiCor X ∩ phiCor Y := by
  apply le_antisymm
  · exact le_inter (phiCor_mono (inter_lb_left _ _)) (phiCor_mono (inter_lb_right _ _))
  · -- φX ∩ φY ⊑ φ(X∩Y): both coreflexive; transport back via ψ and the meet-on-Cor.
    have hle : phiCor X ∩ phiCor Y ⊑ phiCor (X ∩ Y) := by
      -- ψ(φX ∩ φY) ⊑ X and ⊑ Y, so ⊑ X∩Y; then φ-monotone + φψ.
      have hcor : Coreflexive (phiCor X ∩ phiCor Y) :=
        le_trans (inter_lb_left _ _) (inter_lb_left _ _)
      have hX : psiCor (phiCor X ∩ phiCor Y) ⊑ X := by
        have := psiCor_mono (inter_lb_left (phiCor X) (phiCor Y)); rwa [psi_phi] at this
      have hY : psiCor (phiCor X ∩ phiCor Y) ⊑ Y := by
        have := psiCor_mono (inter_lb_right (phiCor X) (phiCor Y)); rwa [psi_phi] at this
      have hXY : psiCor (phiCor X ∩ phiCor Y) ⊑ X ∩ Y := le_inter hX hY
      have := phiCor_mono hXY
      rwa [phi_psi hcor] at this
    exact hle

-- ⊤ → A : the largest H with H ∩ 1 ⊑ A.
/-- The Heyting special arrow `1 → A` on the full poset `(a,a)`: `Ψ(Φ(1) ⟹ Φ(A))`,
    where `⟹` is the Cor(γ) Heyting arrow. -/
@[expose] public noncomputable def oneHeyting {a : 𝒜} (A : a ⟶ a) : a ⟶ a :=
  psiCor (heytingImpl (phiCor (Cat.id a)) (phiCor A))

/-- **§2.316 / §2.32 adjunction**: for coreflexive `A`, `oneHeyting A` is the largest
    `Z : (a,a)` whose coreflexive part lies under `A`:  `Z ∩ 1 ⊑ A ↔ Z ⊑ oneHeyting A`. -/
public theorem oneHeyting_adj {a : 𝒜} (A : a ⟶ a) (Z : a ⟶ a) :
    Z ∩ Cat.id a ⊑ A ↔ Z ⊑ oneHeyting A := by
  have hP : Coreflexive (heytingImpl (phiCor (Cat.id a)) (phiCor A)) := inter_lb_left _ _
  rw [oneHeyting, le_psiCor_iff Z hP]
  -- φZ ⊑ (φ1 ⟹ φA)  ↔  φ1 ≫ φZ ⊑ φA   (heyting_adj_coref)
  rw [← heyting_adj_coref (show Coreflexive (phiCor (Cat.id a)) from inter_lb_left _ _)
      (show Coreflexive (phiCor Z) from inter_lb_left _ _)]
  -- φ1 ≫ φZ = φ1 ∩ φZ = φ(1 ∩ Z); and ⊑ φA ↔ 1 ∩ Z ⊑ A.
  rw [coreflexive_comp_eq_inter (show Coreflexive (phiCor (Cat.id a)) from inter_lb_left _ _)
      (show Coreflexive (phiCor Z) from inter_lb_left _ _),
      Allegory.inter_comm (phiCor (Cat.id a)) (phiCor Z), ← phiCor_inter,
      phiCor_le_iff, Allegory.inter_comm Z (Cat.id a)]

end HeytingHom

/-! ## §2.32  Tabular unitary division allegory ↔ Mσn(A) is a logos

  The MAP CATEGORY Mσn(A) of a tabular unitary allegory A has:
  - objects = objects of A
  - morphisms = maps (entire + simple morphisms) of A
  The book's §2.32 states: A is a tabular unitary division allegory iff Mσn(A)
  is a logos.

  (One direction was shown in §1.784: Rel(C) is a division allegory when C is a
  logos.  The other direction: construct the right adjoint to f# using f\(-)/f°.) -/

/-- **§2.32 lower-function form.** For a map `f : a → b` and a coreflexive `c` on `b`, the
    book's "domain of `fB`" lower function is `dom (f ≫ c) = 1 ∩ f c f°` (using `c° = c`,
    `c ≫ c = c`).  This is the coreflexive on `a` that `corOf_invImage` (MapCat) computes for the
    inverse image `f#` once the subobject `B` of `b` is read as the coreflexive `c = corOf B`. -/
theorem dom_comp_coref {A B : 𝒜} (f : A ⟶ B) {c : B ⟶ B} (hc : Coreflexive c) :
    dom (f ≫ c) = Cat.id A ∩ (f ≫ c ≫ f°) := by
  have hcsym : c° = c := symmetric_eq (coreflexive_symmetric_idempotent hc).1
  have hcidem : c ≫ c = c := (coreflexive_symmetric_idempotent hc).2
  unfold dom
  rw [Allegory.recip_comp, hcsym, Cat.assoc, ← Cat.assoc c c f°, hcidem]

/-- **§2.32, the coreflexive `dom` of a map-conjugate is its plain `1 ∩`-meet.**  For a map
    `f : a → b` and a coreflexive `c` on `b`, `dom (f ≫ c ≫ f°) = 1 ∩ f c f°`.  (The general
    `dom R = 1 ∩ R R°` collapses because `R := f c f°` is symmetric and `f° f ⊑ 1` makes
    `R R° ⊑ R`, while `R` is itself a meet of symmetric idempotents.)  Together with
    `dom_comp_coref` this says `dom (f ≫ c) = dom (f ≫ c ≫ f°) = 1 ∩ f c f°`. -/
public theorem dom_map_coref {A B : 𝒜} (f : A ⟶ B) (hf : Map f) {c : B ⟶ B} (hc : Coreflexive c) :
    dom (f ≫ c ≫ f°) = Cat.id A ∩ (f ≫ c ≫ f°) := by
  have hsym : (f ≫ c ≫ f°)° = f ≫ c ≫ f° := by
    have hCsym : c° = c := symmetric_eq (coreflexive_symmetric_idempotent hc).1
    rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hCsym, Cat.assoc]
  have hCidem : c ≫ c = c := (coreflexive_symmetric_idempotent hc).2
  have hidem_le : (f ≫ c ≫ f°) ≫ (f ≫ c ≫ f°) ⊑ f ≫ c ≫ f° := by
    have hmid : c ≫ (f° ≫ f) ≫ c ⊑ c := by
      calc c ≫ (f° ≫ f) ≫ c ⊑ c ≫ Cat.id B ≫ c := comp_mono_left c (comp_mono_right hf.2 c)
        _ = c ≫ c := by rw [Cat.id_comp]
        _ = c := hCidem
    calc (f ≫ c ≫ f°) ≫ (f ≫ c ≫ f°)
        = f ≫ (c ≫ (f° ≫ f) ≫ c) ≫ f° := by
          rw [Cat.assoc, Cat.assoc, Cat.assoc, Cat.assoc, Cat.assoc]
      _ ⊑ f ≫ c ≫ f° := comp_mono_left f (comp_mono_right hmid f°)
  unfold dom
  rw [hsym]
  apply le_antisymm
  · exact le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) hidem_le)
  · apply le_inter (inter_lb_left _ _)
    have hKcor : Coreflexive (Cat.id A ∩ (f ≫ c ≫ f°)) := inter_lb_left _ _
    have hKidem : (Cat.id A ∩ (f ≫ c ≫ f°)) ≫ (Cat.id A ∩ (f ≫ c ≫ f°))
        = Cat.id A ∩ (f ≫ c ≫ f°) := (coreflexive_symmetric_idempotent hKcor).2
    rw [← hKidem]
    exact le_trans (comp_mono_right (inter_lb_right _ _) _)
      (comp_mono_left _ (inter_lb_right _ _))

-- BOOK §2.32: A is a tabular unitary division allegory iff Mσn(A) is a logos.
-- STATUS: BOTH directions DONE.
-- BACKWARD direction DONE (`Logos (MapObj A)` in MapCat.lean, `mapLogos`, axiom-clean
--   `[propext, Classical.choice]`).
-- FORWARD (logos → division allegory) — DONE (§1.784):
--   • `DivisionAllegory (RelObj 𝒞)` for `[Logos 𝒞]` = `relDivisionAllegory` (RelCat.lean,
--     axioms `[propext, Classical.choice, Quot.sound]`).  S1_77 proves the two special
--     quotients — by a graph (`relQuotByMap`) and by the reciprocal of a graph
--     (`relQuotByMapRecip`, the `f##` right-adjoint image).  The general `R/S` for an arbitrary
--     relation `S` is `relQuotGen R S = (R/graph(S.colB))/(graph S.colA)°`, using the span
--     factorisation `S ≈ (graph S.colA)° ⊚ graph S.colB` (`reconstitute_le`/`le_reconstitute`) and
--     §1.783 associativity.  `qDiv` descends it to the `RelLe`-quotient; both adjunction laws are
--     `relQuotGen.le`/`.maximal` across the `quotLe ↔ ⊑` bridge.  This unblocks §2.343.
-- BACKWARD (division allegory → logos on Map(𝒜)) — DONE.  The construction (Freyd §2.316 final
--   paragraph + §2.32) is split between THIS file (the §2.316 Heyting machinery) and MapCat.lean
--   (the subobject bridge + the `Logos` instance):
--   • §2.316 HOM-POSET HEYTING ARROW (this file, `section HeytingHom`):
--     - `topMor`/`topMor_max`: the maximal morphism `⊤_{a,b} = 𝟘/𝟘`, the book's `p_a ≫ p_b°`.
--     - `topTab`: a chosen tabulation `(ℓ₁,ℓ₂) : γ → a` of `⊤_a` (via `TabularAllegory.tabular`).
--     - `phiCor R := 1_γ ∩ ℓ₁ R ℓ₂°`,  `psiCor c := ℓ₁° c ℓ₂`:  the ORDER-ISO `(a,a) ≅ Cor(γ)`.
--       `psi_phi : ψ(φ R) = R` (via `tab_recover`) and `phi_psi : φ(ψ c) = c` for coreflexive `c`
--       (via `tab_corecover`, joint-monicity + `tabulation_UP_*`); `phiCor_le_iff`, `phiCor_inter`,
--       `le_psiCor_iff` are the order/meet/Galois consequences.
--     - `oneHeyting A := ψ(φ1 ⟹ φA)` (the §2.316 arrow `1 → A` on `(a,a)`, NOT on `Cor(a)`), with
--       `oneHeyting_adj : Z ∩ 1 ⊑ A ↔ Z ⊑ oneHeyting A`  (the relative pseudocomplement of `∩`).
--   • §2.32 RIGHT ADJOINT TO `f#` (MapCat.lean, `section MapLogos`):  under the subobject bridge
--     `Sub(Map A) X ≅ Cor(X)`, `corOf_invImage` + `dom_map_coref` give `corOf (f# B') = 1 ∩ f c f°`.
--     `rightAdjCor f A := 1_b ∩ f \ (oneHeyting A) / f°` is its right adjoint
--     (`rightAdjCor_adj`: `1 ∩ f c f° ⊑ A ↔ c ⊑ rightAdjCor f A`, via `le_leftDiv_iff`/`le_div_iff`
--     ∘ `oneHeyting_adj`).  `mapHasRightAdjointImage` = `splitSub ∘ rightAdjCor`; `mapLogos` then
--     bundles it with `mapPreLogos`.  (`D = f\A/f°` would be WRONG: its adjunction `f c f° ⊑ A` is
--     strictly stronger than `1 ∩ f c f° ⊑ A` — hence the genuine §2.316 `oneHeyting` is needed.)

/-! ## §2.331  Moerdijk representation theorems

  These results about faithful representation in O(X)-valued sets are classical
  topology / locale theory results (Ieke Moerdijk).  They require the locale
  O(X) of open sets of a metrizable space X (without isolated points) and the
  allegory of O(X)-valued sets [§2.227]. -/

-- BOOK §2.331 (i): Let X be a metrizable space without isolated points, O(X) the locale
-- of open subsets thereof.  Any countable tabular unitary division allegory may be
-- faithfully represented in a countable power of the allegory of O(X)-valued sets.

-- BOOK §2.331 (ii): Any countable tabular unitary division allegory may be faithfully
-- represented in a countable power of the allegory of O(X)-valued sets.

-- BOOK §2.331 (iii): Any countable logos may be faithfully represented in a countable
-- power of H(X).

-- BOOK §2.331 (iv): Any countable logos with a coprime terminator may be faithfully
-- represented in H(X).

-- STATUS: DONE-conditional, in `Freyd/S2_33.lean` (`repr_in_oset_of_tabular`,
--   `repr_in_oset_via_frameHom`).  The two former blockers are CLOSED:
--
--   (1) THE ALLEGORY OF `O`-VALUED SETS IS NOW A FULL `Allegory`.  `Freyd/Locale.lean` registers
--       `Freyd.instOSetAllegory : Allegory (OValuedSet F)` for any `Frame F` (§2.16(12)/§2.227
--       COMPLETE): beyond `recip`/`inter` + the involution/lattice laws, the two
--       composition-interaction laws `semidistrib` and `modular` are PROVED
--       (`OSetHom.osetAlleg_semidistrib`, `OSetHom.osetAlleg_modular`) by elementary frame
--       meet/`sSup` algebra over the `⨆`-colimit composition.  OSet is also functorial in the
--       frame: a `FrameHom f` induces `OSetFrameHom.functor : AllegoryFunctor (OValuedSet F)
--       (OValuedSet G)` (`OSetFrameHom.{obj,map,map_comp,…}` in Locale; bundled in S2_33).
--
--   (2) IMPORT CYCLE avoided by HOSTING the conditional theorem in the new downstream file
--       `Freyd/S2_33.lean` (imports `Locale` + `S2_218` + `MapCat` + `RelCat`), not here.
--
--   THE REDUCTION (S2_33) is PROVED: a tabular unitary distributive allegory `𝒜` (the abstract
--   stand-in for a *countable tabular unitary division allegory*) is faithfully represented in
--   `OValuedSet O` by composing the §2.218 representation `repr_in_power_of_sets_of_tabular`
--   (target `Rel(Set^|Ā|)`, given the §1.543 capital data `Ā`/`hproj`/`cap`) with a faithful
--   `moerdijk : Rel(Set^|Ā|) ⟶ OValuedSet O`.
--
--   REMAINING NAMED HYPOTHESES (genuinely space-specific, NOT algebraic):
--     • the §1.543 CAPITAL data `Ā`/`hproj`/`cap`/`hcap` (the precisely-isolated R3 residual of
--       §2.218 — shared with the whole representation program, not special to §2.331);
--     • `moerdijk` faithful — Moerdijk's embedding of `Rel(Set^|Ā|)` into `OValuedSet O`, for
--       `O := O(X)`, `X` metrizable without isolated points.  The metric space `X` enters ONLY
--       here, as an explicit functor; no point-set-topology type is fabricated.  Via
--       `repr_in_oset_via_frameHom`, `moerdijk` factors as `embed ⋙ OSetFrameHom.functor h` with
--       `h : FrameHom O(2^ω) ⟶ O(X)` — Moerdijk's locale embedding made concrete.
--     • parts (iii)/(iv): `logos`/`coprime terminator` have no repo class; carried as
--       `𝒜 := Rel(Map logos)` with the §1.74 focal datum threaded like `moerdijk` — see the
--       end-of-file marker in `S2_33.lean`.

/-! ## §2.34  Split allegory PRel(E) is a division allegory -/

-- BOOK §2.34: Let A be a division allegory, E a class of symmetric idempotents.
-- Then PRel(E) (the E-split completion of A) is a division allegory.
-- If |A| ⊂ E (all objects are in E) then A → PRel(E) is a faithful embedding of
-- division allegories.
-- STATUS: DONE for the full-Spl case (E = all symmetric idempotents); see below.
-- AVAILABLE: `SplObj 𝒜` (S2_21.lean) = the case E = all symmetric idempotents, with
--   `instAllegorySpl`, `instDistributiveSpl`, `instUnitarySpl`, `instPositiveSpl`,
--   `instTabularAllegorySplCor` (Spl.lean), `splObj_tabular_of_semiSimple`.
-- FULL-Spl case (E = all symmetric idempotents) DONE: `DivisionAllegory (SplObj 𝒜)` for
--   `[DivisionAllegory 𝒜]` is PROVED as `instDivisionSpl` (Spl.lean) — pointwise division
--   `splDiv = E.e ≫ (R.R/S.R) ≫ F.e`, both §2.31 laws via SplHom.fixed + base div_comp_le/le_div.
-- MISSING: (2) For restricted PRel(E) with E ⊊ all-sym-idempotents: not yet
--   needed; the full-Spl case subsumes the faithful-embedding claim when |A| ⊂ E.

/-! ## §2.342  Positive reflection of a division allegory

  **PROVED** in `Freyd.MatrixAllegory` (imported below is impossible due to the import cycle
  `MatrixAllegory → S2_3`; the result lives in the downstream file by necessity).

  The POSITIVE REFLECTION A⁺ of a division allegory A is the matrix allegory `MatObj 𝒜`:
  - Objects are finite-index families of A-objects (`Fin n → 𝒜`).
  - Morphisms are `n×m` matrices of A-morphisms.
  - Composition: `(MN)_{ik} = ⨆_j M_{ij} ≫ N_{jk}` (finite join).
  - Division: `(R/S)_{ij} = ⋀_k R_{ik}/S_{jk}` (finite meet over the codomain index).

  The key adjointness check — `T ⊑ R/S ↔ T≫S ⊑ R` — reduces to `le_div_iff` entrywise:
  the join in the composition pairs with the meet in the division via `listJoin'_le`/`le_finMeet`.

  The 1×1 embedding `embed1 : 𝒜 → MatObj 𝒜` is faithful and preserves ≫, °, ∩, ∪, 𝟘, /.

  Relevant declarations in `Freyd.MatrixAllegory` (namespace `Freyd.Alg.Mat`):
    `instDivisionAllegoryMat`  : `DivisionAllegory (MatObj 𝒜)` [noncomputable, §2.342]
    `embed1_injective`, `embed1_div` : faithfulness + division preservation -/

/-! ## §2.343  Every logos faithfully and fully embeds in a positive effective logos -/

-- BOOK §2.343: Every logos C embeds faithfully and fully in a positive effective logos via
-- C → Mσn(H̃(Eq(Rel(C))⁺)) = Map(SplObj(Mat(Rel C))), using §2.32, §2.216, §2.169 (Spl).
-- STATUS: DONE — assembled in `Freyd/RelCat.lean` (this file cannot import RelCat/MapCat without a
-- cycle, so the theorems live there; their statements/names are recorded here).
--
-- The target `D := Map(SplObj(Mat(Rel C)))` and the embedding `embed217_2 : C → D` (already FAITHFUL
-- from §2.217(2)) are reused; over `[Logos C]` they upgrade to the §2.343 headline:
--
--   PART A (structure) — `D` is a POSITIVE EFFECTIVE LOGOS (`Freyd.s343_positive_effective_logos`):
--     • `Freyd.splMatRelTUDiv` : `TabularUnitaryDivisionAllegory (SplObj (Mat (Rel C)))`, assembling
--       `relDivisionAllegory` (§1.784/§2.32 fwd, `RelObj C`) → `instDivisionAllegoryMat` (§2.342) →
--       `instDivisionSpl` (§2.31) for division, with tabular+unitary from `splMatRelTUP`.
--     • `Freyd.s343_logos`            : `Logos D`             (`mapLogos`, §2.32 backward);
--     • positivity                    : `s217_2_target_positivePreLogos.toHasBinaryCoproducts`;
--     • `Freyd.s343_effectiveRegular` : `EffectiveRegular D`  (`mapEffectiveRegular`, §2.217(2) split).
--
--   PART B (fullness) — `Freyd.embed217_2_full`: every `D`-morphism `embed217_2Obj a ⟶ embed217_2Obj b`
--   is `embed217_2 f` for a unique `f`.  The collapse runs down the tower
--     Spl (`embHom_full` + `embHom_reflects_map`) → Mat 1×1 (`Fin 1` + `embed1_reflects_map`) →
--     Rel (`embedRel_full`, every Map is the graph of a unique C-morphism).
--
--   HEADLINE: `Freyd.s343_full_faithful_embed_into_positive_effective_logos` — there is a positive
--   effective logos structure on `D` plus a FULL+FAITHFUL embedding `C ↪ D`.  Bare `[Logos C]`.
--   Axioms: [propext, Classical.choice, Quot.sound], no `sorryAx`.

end Freyd.Alg
