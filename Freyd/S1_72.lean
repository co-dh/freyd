/-
  Freyd & Scedrov, *Categories and Allegories* §1.72–§1.76
  Heyting algebras, Negation, Focal logoi, Representation theorems.

  §1.72  Heyting algebra: lattice with implication → (right adjoint to ∧).
  §1.723 Locale: complete lattice with finite-meet/arbitrary-join distributivity.
  §1.724 Double-arrow x⟺y = (x→y)∧(y→x), commutative with unit 1.
  §1.725 Equational theory of Heyting algebras.
  §1.726 Derived equations (x→y covariant in y, contravariant in x; distributivity).
  §1.727 Negation: ¬x = x→0, double negation, De Morgan.
  §1.728 Law of excluded middle ⇒ Boolean algebra.
  §1.73  ℱ(T) filter, A/ℱ quotient logos.
  §1.733 Coprime object, connected object, FOCAL LOGOS (1 is coprime projective).
  §1.734 Focal representation, representation theorems.
-/


import Freyd.S1_10
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_57
import Freyd.S1_60
import Freyd.S1_64
import Freyd.S1_70
import Freyd.S1_85


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.72 Heyting algebra

  A HEYTING ALGEBRA is a lattice with a binary → such that
  z ≤ x → y  ⇔  x ∧ z ≤ y  (→ is right adjoint to ∧, fixing x).
  The underlying poset must be a lattice, so meet satisfies the standard
  lattice axioms (meet_le_left, meet_le_right, le_meet). -/

/-- A HEYTING ALGEBRA: lattice with implication satisfying the adjunction
    z ≤ (x→y) ↔ x∧z ≤ y  (book §1.72).

    ONE concept (§1.72), THREE carriers — kept separate because the carrier's
    equality differs, so no single typeclass covers them:
    * this `HeytingAlgebra` — carrier `Sub(A)` per category, a preorder of
      subobject representatives (`Subobject.le`, NO antisymmetry), laws as mutual `.le`;
    * `HasHeytingArrow` (S1_85) — carrier = objects of a thin category, preorder via
      `Nonempty (· ⟶ ·)`, meet = categorical product (used for §1.852 exponentials);
    * `HeytingLattice` (S1_85) — an honest carrier `Type` WITH `le_antisymm` (a real
      poset, `=`-laws), used for the closure-operator/locale algebra. -/
class HeytingAlgebra (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞]
    extends HasSubobjectUnions 𝒞 where
  /-- Binary meet (∧) of subobjects. -/
  meet : ∀ {A : 𝒞} (_x _y : Subobject 𝒞 A), Subobject 𝒞 A
  /-- meet is a lower bound: x∧y ≤ x. -/
  meet_le_left  : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject.le (meet x y) x
  /-- meet is a lower bound: x∧y ≤ y. -/
  meet_le_right : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject.le (meet x y) y
  /-- meet is the greatest lower bound: z ≤ x → z ≤ y → z ≤ x∧y. -/
  le_meet : ∀ {A : 𝒞} (x y z : Subobject 𝒞 A),
    Subobject.le z x → Subobject.le z y → Subobject.le z (meet x y)
  /-- Implication x → y. -/
  imp  : ∀ {A : 𝒞} (_x _y : Subobject 𝒞 A), Subobject 𝒞 A
  /-- The adjunction: z ≤ (x→y) ↔ x∧z ≤ y. -/
  adjunction : ∀ {A : 𝒞} (x y z : Subobject 𝒞 A),
    Subobject.le z (imp x y) ↔ Subobject.le (meet x z) y

/-! ## §1.725-§1.726 Derived laws in a Heyting algebra

  Derived laws from the double-Horn characterization (§1.725–§1.726):
  monotonicity of → in each argument, and finite-meet distributivity. -/

section HeytingLaws

variable [HasImages 𝒞] [HeytingAlgebra 𝒞] {A : 𝒞}

/-- Modus ponens: x∧(x→y) ≤ y  (from adjunction, taking z := x→y). -/
theorem heyting_mp (x y : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x (HeytingAlgebra.imp x y)) y :=
  (HeytingAlgebra.adjunction x y (HeytingAlgebra.imp x y)).mp (Subobject.le_refl _)

/-- meet is monotone in the left argument: w ≤ x → w∧z ≤ x∧z. -/
theorem meet_mono_left {w x z : Subobject 𝒞 A} (h : Subobject.le w x) :
    Subobject.le (HeytingAlgebra.meet w z) (HeytingAlgebra.meet x z) :=
  HeytingAlgebra.le_meet _ _ _
    (Subobject.le_trans (HeytingAlgebra.meet_le_left _ _) h)
    (HeytingAlgebra.meet_le_right _ _)

/-- meet is symmetric: x∧y ≤ y∧x. -/
theorem meet_comm_le (x y : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x y) (HeytingAlgebra.meet y x) :=
  HeytingAlgebra.le_meet _ _ _
    (HeytingAlgebra.meet_le_right _ _)
    (HeytingAlgebra.meet_le_left _ _)

/-- (§1.726) x→y is covariant in y: y ≤ z → (x→y) ≤ (x→z). -/
theorem imp_mono_right {x y z : Subobject 𝒞 A} (h : Subobject.le y z) :
    Subobject.le (HeytingAlgebra.imp x y) (HeytingAlgebra.imp x z) := by
  rw [HeytingAlgebra.adjunction]
  -- x∧(x→y) ≤ y ≤ z
  exact Subobject.le_trans (heyting_mp x y) h

/-- (§1.726) x→y is contravariant in x: w ≤ x → (x→y) ≤ (w→y). -/
theorem imp_mono_left_contra {x w y : Subobject 𝒞 A} (h : Subobject.le w x) :
    Subobject.le (HeytingAlgebra.imp x y) (HeytingAlgebra.imp w y) := by
  rw [HeytingAlgebra.adjunction]
  -- w∧(x→y) ≤ x∧(x→y) ≤ y
  exact Subobject.le_trans (meet_mono_left h) (heyting_mp x y)

end HeytingLaws

/-! ## §1.723 Locale

  A LOCALE is a complete lattice in which finite meets distribute over
  arbitrary joins: x ∧ (⨆ S) = ⨆ {x ∧ s | s ∈ S}  (§1.723).
  Every locale is a Heyting algebra. -/

/-- A LOCALE: locally complete lattice with meet distributing over
    arbitrary joins (§1.723). -/
class Locale (𝒞 : Type u) [Cat.{v} 𝒞] [HasImages 𝒞]
    extends LocallyComplete 𝒞 where
  /-- Binary meet (∧). -/
  meet : ∀ {A : 𝒞} (_x _y : Subobject 𝒞 A), Subobject 𝒞 A
  /-- meet_le_left: x∧y ≤ x. -/
  meet_le_left  : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject.le (meet x y) x
  /-- meet_le_right: x∧y ≤ y. -/
  meet_le_right : ∀ {A : 𝒞} (x y : Subobject 𝒞 A), Subobject.le (meet x y) y
  /-- le_meet: greatest lower bound. -/
  le_meet : ∀ {A : 𝒞} (x y z : Subobject 𝒞 A),
    Subobject.le z x → Subobject.le z y → Subobject.le z (meet x y)
  /-- meet distributes over arbitrary joins:
      x ∧ sup S = sup { x ∧ s | s ∈ S }. -/
  meet_sup_distrib : ∀ {A : 𝒞} (x : Subobject 𝒞 A) (S : Subobject 𝒞 A → Prop),
    meet x (LocallyComplete.sup S) =
    LocallyComplete.sup (fun s => ∃ t, S t ∧ s = meet x t)

/-- Every locale is a Heyting algebra (§1.723):
    define x → y = sup {z | x∧z ≤ y}. -/
noncomputable def locale_is_heyting [HasImages 𝒞] [Locale 𝒞] :
    HeytingAlgebra 𝒞 where
  toHasSubobjectUnions := {
    union := fun S T => LocallyComplete.sup (fun U => U = S ∨ U = T)
    union_left := fun S T =>
      (LocallyComplete.sup_isSup _).upper S (Or.inl rfl)
    union_right := fun S T =>
      (LocallyComplete.sup_isSup _).upper T (Or.inr rfl)
    union_min := fun S T U hS hT =>
      (LocallyComplete.sup_isSup _).least U
        (fun s hs => hs.elim (fun h => h ▸ hS) (fun h => h ▸ hT))
  }
  meet := Locale.meet
  meet_le_left  := Locale.meet_le_left
  meet_le_right := Locale.meet_le_right
  le_meet       := Locale.le_meet
  imp := fun x y => LocallyComplete.sup (fun z => Subobject.le (Locale.meet x z) y)
  adjunction := fun x y z => by
    constructor
    · -- z ≤ sup{w | x∧w ≤ y} → x∧z ≤ y; use meet_sup_distrib
      intro hz
      have h1 : Subobject.le (Locale.meet x z)
                    (Locale.meet x (LocallyComplete.sup fun w => Subobject.le (Locale.meet x w) y)) :=
        Locale.le_meet _ _ _ (Locale.meet_le_left _ _)
          (Subobject.le_trans (Locale.meet_le_right _ _) hz)
      have h2 := Locale.meet_sup_distrib x (fun w => Subobject.le (Locale.meet x w) y)
      have h3 : Subobject.le
          (LocallyComplete.sup (fun s => ∃ t, Subobject.le (Locale.meet x t) y ∧ s = Locale.meet x t)) y :=
        (LocallyComplete.sup_isSup _).least y (fun s ⟨t, ht, hs⟩ => hs ▸ ht)
      exact Subobject.le_trans (h2 ▸ h1) h3
    · -- x∧z ≤ y → z ≤ sup{w | x∧w ≤ y}  (z witnesses itself)
      intro hxz; exact (LocallyComplete.sup_isSup _).upper z hxz

/-! ## §1.724 Double-arrow (biimplication)

  Define x ⟺ y = (x→y) ∧ (y→x).  The book characterizes it by
  the double-Horn sentence: z ≤ x⟺y iff z∧x = z∧y  (§1.724).
  Properties: commutative, unit is 1, every element is its own inverse
  (x⟺x = 1), and x∧(x⟺y) = x∧y. -/

/-- Double-arrow: x ⟺ y = (x→y) ∧ (y→x)  (§1.724). -/
def hiff [HasImages 𝒞] [HeytingAlgebra 𝒞] {A : 𝒞}
    (x y : Subobject 𝒞 A) : Subobject 𝒞 A :=
  HeytingAlgebra.meet (HeytingAlgebra.imp x y) (HeytingAlgebra.imp y x)

section HiffLaws

variable [HasImages 𝒞] [HeytingAlgebra 𝒞] {A : 𝒞}

/-- (§1.724) Double-arrow is commutative: x⟺y ≤ y⟺x. -/
theorem hiff_comm_le (x y : Subobject 𝒞 A) :
    Subobject.le (hiff x y) (hiff y x) := by
  unfold hiff
  exact HeytingAlgebra.le_meet _ _ _
    (HeytingAlgebra.meet_le_right _ _)
    (HeytingAlgebra.meet_le_left _ _)

/-- (§1.724) x∧(x⟺y) ≤ x∧y.
    Key step: x∧(x⟺y) ≤ x∧(x→y) and x∧(x→y) ≤ y by modus ponens. -/
theorem meet_hiff_le (x y : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x (hiff x y))
                 (HeytingAlgebra.meet x y) := by
  unfold hiff
  -- x∧((x→y)∧(y→x)) ≤ x∧(x→y) by meet_le_left
  have h1 : Subobject.le (HeytingAlgebra.meet x
      (HeytingAlgebra.meet (HeytingAlgebra.imp x y) (HeytingAlgebra.imp y x)))
      (HeytingAlgebra.meet x (HeytingAlgebra.imp x y)) :=
    HeytingAlgebra.le_meet _ _ _
      (HeytingAlgebra.meet_le_left _ _)
      (Subobject.le_trans (HeytingAlgebra.meet_le_right _ _)
        (HeytingAlgebra.meet_le_left _ _))
  -- x∧(x→y) ≤ y by modus ponens
  have h2 : Subobject.le (HeytingAlgebra.meet x (HeytingAlgebra.imp x y)) y :=
    heyting_mp x y
  exact HeytingAlgebra.le_meet _ _ _
    (HeytingAlgebra.meet_le_left _ _)
    (Subobject.le_trans h1 h2)

end HiffLaws

/-! ## §1.727 Negation

  Define ¬x = x → 0 (§1.727).  ¬x is the largest element disjoint from x.
  Laws: ¬(x∨y) = ¬x∧¬y, ¬1=0, ¬0=1, x ≤ ¬¬x, ¬x = ¬¬¬x,
        x ≤ y → ¬y ≤ ¬x.  Double negation preserves meets. -/

/-- Negation in a Heyting algebra with a bottom element: ¬x = x → ⊥ (§1.727). -/
def hneg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) : Subobject 𝒞 A :=
  HeytingAlgebra.imp x (PreLogos.bottom A)

/-- x∧¬x ≤ ⊥  (disjointness of x and its negation). -/
theorem meet_neg_le_bot [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet x (hneg x)) (PreLogos.bottom A) :=
  heyting_mp x (PreLogos.bottom A)

/-- x ≤ ¬¬x  (§1.727).
    Proof: apply the adjunction for ¬¬x; need (¬x)∧x ≤ ⊥, which is meet_neg_le_bot + comm. -/
theorem le_double_neg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le x (hneg (hneg x)) := by
  rw [show Subobject.le x (hneg (hneg x)) ↔
      Subobject.le (HeytingAlgebra.meet (hneg x) x) (PreLogos.bottom A) from
    HeytingAlgebra.adjunction (hneg x) (PreLogos.bottom A) x]
  -- Need: (¬x)∧x ≤ ⊥.  We have x∧(¬x) ≤ ⊥; use commutativity of meet.
  exact Subobject.le_trans (meet_comm_le (hneg x) x) (meet_neg_le_bot x)

/-- Negation is contravariant: x ≤ y → ¬y ≤ ¬x  (§1.727).
    Proof: ¬y ≤ ¬x iff x∧¬y ≤ ⊥; since x ≤ y, x∧¬y ≤ y∧¬y ≤ ⊥. -/
theorem hneg_antitone [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} {x y : Subobject 𝒞 A} (h : Subobject.le x y) :
    Subobject.le (hneg y) (hneg x) := by
  rw [show Subobject.le (hneg y) (hneg x) ↔
      Subobject.le (HeytingAlgebra.meet x (hneg y)) (PreLogos.bottom A) from
    HeytingAlgebra.adjunction x (PreLogos.bottom A) (hneg y)]
  -- x∧(¬y) ≤ y∧(¬y) ≤ ⊥
  exact Subobject.le_trans (meet_mono_left h) (meet_neg_le_bot y)

/-- ¬x ≤ ¬¬¬x  (from le_double_neg applied to ¬x). -/
theorem neg_le_triple_neg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (hneg x) (hneg (hneg (hneg x))) :=
  le_double_neg (hneg x)

/-- ¬¬¬x ≤ ¬x  (apply hneg_antitone to x ≤ ¬¬x). -/
theorem triple_neg_le_neg [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (hneg (hneg (hneg x))) (hneg x) :=
  hneg_antitone (le_double_neg x)

/-- ¬¬¬x and ¬x are mutually ≤ (book's ¬¬¬x = ¬x, §1.727).
    In the subobject setting we get mutual le; propositional eq needs extensionality. -/
theorem triple_neg_equiv [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A) :
    Subobject.le (hneg (hneg (hneg x))) (hneg x) ∧
    Subobject.le (hneg x) (hneg (hneg (hneg x))) :=
  ⟨triple_neg_le_neg x, neg_le_triple_neg x⟩

/-- De Morgan: ¬(x∨y) ≤ ¬x∧¬y  (§1.726/§1.727).
    Proof: ¬(x∨y) ≤ ¬x because x ≤ x∨y; similarly for y; use le_meet. -/
theorem hneg_union_le [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x y : Subobject 𝒞 A) :
    Subobject.le (hneg (HasSubobjectUnions.union x y))
                 (HeytingAlgebra.meet (hneg x) (hneg y)) :=
  HeytingAlgebra.le_meet _ _ _
    (hneg_antitone (HasSubobjectUnions.union_left x y))
    (hneg_antitone (HasSubobjectUnions.union_right x y))

/-- Double negation preserves meets: ¬¬(x∧y) ≤ ¬¬x∧¬¬y  (§1.727, ≤ direction).
    Proof: x∧y ≤ x and x∧y ≤ y give ¬¬(x∧y) ≤ ¬¬x and ¬¬(x∧y) ≤ ¬¬y by hneg_antitone.
    The reverse inequality ¬¬x∧¬¬y ≤ ¬¬(x∧y) is `double_neg_meet_ge` (proven below). -/
theorem double_neg_meet_le [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x y : Subobject 𝒞 A) :
    Subobject.le (hneg (hneg (HeytingAlgebra.meet x y)))
                 (HeytingAlgebra.meet (hneg (hneg x)) (hneg (hneg y))) := by
  -- ¬¬(x∧y) ≤ ¬¬x: apply hneg_antitone twice to x∧y ≤ x
  apply HeytingAlgebra.le_meet
  · exact hneg_antitone (hneg_antitone (HeytingAlgebra.meet_le_left x y))
  · exact hneg_antitone (hneg_antitone (HeytingAlgebra.meet_le_right x y))

/-- ¬¬x∧¬¬y ≤ ¬¬(x∧y)  (the harder direction, §1.727).
    Book argument: x∧y∧¬(x∧y)=0 → ¬(x∧y)∧x ≤ ¬y → ¬¬y ≤ ¬(¬(x∧y)∧x)
    → ¬(x∧y)∧¬¬y ≤ ¬x → ¬¬x ≤ ¬(¬(x∧y)∧¬¬y) → ¬(x∧y)∧¬¬x∧¬¬y ≤ 0. -/
theorem double_neg_meet_ge [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x y : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet (hneg (hneg x)) (hneg (hneg y)))
                 (hneg (hneg (HeytingAlgebra.meet x y))) := by
  -- A: y ∧ (¬(x∧y) ∧ x) ≤ ⊥
  have hA : Subobject.le
      (HeytingAlgebra.meet y (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) x))
      (PreLogos.bottom A) := by
    apply Subobject.le_trans _ (meet_neg_le_bot (HeytingAlgebra.meet x y))
    apply HeytingAlgebra.le_meet
    · apply Subobject.le_trans _ (meet_comm_le y x)
      exact HeytingAlgebra.le_meet _ _ _ (HeytingAlgebra.meet_le_left _ _)
        (Subobject.le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_right _ _))
    · exact Subobject.le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_left _ _)
  -- B: ¬(x∧y)∧x ≤ ¬y; D: x∧(¬(x∧y)∧¬¬y) ≤ ⊥; E: ¬(x∧y)∧¬¬y ≤ ¬x; F: ¬¬x ≤ ¬(¬(x∧y)∧¬¬y)
  have hB : Subobject.le _ (hneg y) := (HeytingAlgebra.adjunction y (PreLogos.bottom A) _).mpr hA
  have hD : Subobject.le
      (HeytingAlgebra.meet x (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) (hneg (hneg y))))
      (PreLogos.bottom A) := by
    apply Subobject.le_trans _ (meet_neg_le_bot (hneg y))
    apply Subobject.le_trans (HeytingAlgebra.le_meet _ _ _
      (HeytingAlgebra.le_meet _ _ _
        (Subobject.le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_left _ _))
        (HeytingAlgebra.meet_le_left _ _))
      (Subobject.le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_right _ _)))
    exact meet_mono_left hB
  have hE : Subobject.le _ (hneg x) := (HeytingAlgebra.adjunction x (PreLogos.bottom A) _).mpr hD
  have hF := hneg_antitone hE
  -- Conclude: ¬(x∧y) ∧ (¬¬x ∧ ¬¬y) ≤ ⊥, i.e. ¬¬x∧¬¬y ≤ ¬¬(x∧y)
  apply (HeytingAlgebra.adjunction (hneg (HeytingAlgebra.meet x y)) (PreLogos.bottom A) _).mpr
  apply Subobject.le_trans _ (Subobject.le_trans
    (meet_comm_le
      (hneg (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) (hneg (hneg y))))
      (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) (hneg (hneg y))))
    (meet_neg_le_bot (HeytingAlgebra.meet (hneg (HeytingAlgebra.meet x y)) (hneg (hneg y)))))
  apply HeytingAlgebra.le_meet
  · exact Subobject.le_trans
      (Subobject.le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_left _ _))
      hF
  · exact HeytingAlgebra.le_meet _ _ _
      (HeytingAlgebra.meet_le_left _ _)
      (Subobject.le_trans (HeytingAlgebra.meet_le_right _ _) (HeytingAlgebra.meet_le_right _ _))

/-- Meet distributes over union: z∧(a∨b) ≤ (z∧a)∨(z∧b)  (§1.726).
    A Heyting algebra is distributive because meet has a right adjoint (imp):
    by the adjunction this reduces to a∨b ≤ z→((z∧a)∨(z∧b)), and each
    disjunct a, b lands there since z∧a, z∧b ≤ (z∧a)∨(z∧b).  The reverse
    inequality is automatic in any lattice, so this is genuine distributivity. -/
theorem meet_union_le_distrib [HasImages 𝒞] [HeytingAlgebra 𝒞]
    {A : 𝒞} (z a b : Subobject 𝒞 A) :
    Subobject.le (HeytingAlgebra.meet z (HasSubobjectUnions.union a b))
                 (HasSubobjectUnions.union (HeytingAlgebra.meet z a)
                                           (HeytingAlgebra.meet z b)) := by
  -- z∧(a∨b) ≤ W  ↔  a∨b ≤ z→W, with W = (z∧a)∨(z∧b)
  rw [← HeytingAlgebra.adjunction]
  apply HasSubobjectUnions.union_min
  · -- a ≤ z→W  ↔  z∧a ≤ W; and z∧a ≤ (z∧a)∨(z∧b)
    rw [HeytingAlgebra.adjunction]; exact HasSubobjectUnions.union_left _ _
  · rw [HeytingAlgebra.adjunction]; exact HasSubobjectUnions.union_right _ _

/-! ## §1.728 Law of excluded middle

  If we adjoin x ∨ ¬x = 1 (law of excluded middle), every element has a
  complement, and since Heyting algebras are distributive lattices, we get
  a Boolean algebra (§1.728).
  Alternatively: x = ¬¬x suffices: x ∨ ¬x = ¬¬(x ∨ ¬x) = ¬(¬x ∧ ¬¬x) = ¬0 = 1. -/

/-- Every subobject is ≤ the entire (top) subobject. -/
theorem le_entire {A : 𝒞} (S : Subobject 𝒞 A) : Subobject.le S (Subobject.entire A) :=
  ⟨S.arr, by simp [Subobject.entire, Cat.comp_id]⟩

/-- Under excluded middle, double negation is the identity: ¬¬x ≤ x
    (the converse `x ≤ ¬¬x` is `le_double_neg`, so ¬¬x = x).  (§1.728)
    Proof (Boolean): ¬¬x = ¬¬x ∧ 1 = ¬¬x ∧ (x∨¬x) ≤ (¬¬x∧x) ∨ (¬¬x∧¬x) ≤ x∨⊥ = x,
    using meet-over-union distributivity and ¬¬x∧¬x ≤ ⊥. -/
theorem double_neg_le_of_em [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A)
    (hem : Subobject.le (Subobject.entire A)
            (HasSubobjectUnions.union x (hneg x))) :
    Subobject.le (hneg (hneg x)) x := by
  -- ¬¬x ≤ ¬¬x ∧ (x∨¬x)
  have step1 : Subobject.le (hneg (hneg x))
      (HeytingAlgebra.meet (hneg (hneg x)) (HasSubobjectUnions.union x (hneg x))) :=
    HeytingAlgebra.le_meet _ _ _ (Subobject.le_refl _)
      (Subobject.le_trans (le_entire _) hem)
  -- ¬¬x ∧ (x∨¬x) ≤ (¬¬x∧x) ∨ (¬¬x∧¬x)
  have step2 := meet_union_le_distrib (hneg (hneg x)) x (hneg x)
  -- (¬¬x∧x) ∨ (¬¬x∧¬x) ≤ x
  have step3 : Subobject.le
      (HasSubobjectUnions.union (HeytingAlgebra.meet (hneg (hneg x)) x)
                                (HeytingAlgebra.meet (hneg (hneg x)) (hneg x))) x :=
    HasSubobjectUnions.union_min _ _ _
      (HeytingAlgebra.meet_le_right _ _)
      -- ¬¬x∧¬x ≤ ¬x∧¬¬x ≤ ⊥ ≤ x
      (Subobject.le_trans (meet_comm_le _ _)
        (Subobject.le_trans (meet_neg_le_bot (hneg x)) (PreLogos.bottom_min x)))
  exact Subobject.le_trans step1 (Subobject.le_trans step2 step3)

/-- Excluded middle ⇒ double negation is the identity (§1.728).
    Records both halves: `x ≤ ¬¬x` (always) and `¬¬x ≤ x` (under EM). -/
theorem double_neg_eq_self [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A)
    (hem : Subobject.le (Subobject.entire A)
            (HasSubobjectUnions.union x (hneg x))) :
    Subobject.le (hneg (hneg x)) x ∧ Subobject.le x (hneg (hneg x)) :=
  ⟨double_neg_le_of_em x hem, le_double_neg x⟩

/-- In a Heyting algebra (with bottom), excluded middle x∨¬x = 1 implies
    x has a complement in the sense of §1.631.  (§1.728)
    Here "complement" is (¬x), with x∧¬x = ⊥ and x∨¬x = 1. -/
theorem em_implies_complemented [HasImages 𝒞] [HeytingAlgebra 𝒞] [PreLogos 𝒞]
    {A : 𝒞} (x : Subobject 𝒞 A)
    (hem : Subobject.le (Subobject.entire A)
            (HasSubobjectUnions.union x (hneg x))) :
    ∃ (nx : Subobject 𝒞 A),
      (∀ S, Subobject.le S x → Subobject.le S nx →
        Subobject.le S (PreLogos.bottom A)) ∧
      Subobject.le (Subobject.entire A) (HasSubobjectUnions.union x nx) :=
  ⟨hneg x,
    fun _S hSx hSnx =>
      Subobject.le_trans
        (HeytingAlgebra.le_meet _ _ _ hSx hSnx)
        (meet_neg_le_bot x),
    hem⟩

/-! ## §1.73 Filter ℱ(T) and quotient A/ℱ

  For a representation T: A → B of logoi, ℱ(T) = {U⊆1 | T(U)=1}.
  ℱ(T) is a filter.  For any filter ℱ, there's a quotient logos A/ℱ
  with a representation T_ℱ: A → A/ℱ (§1.731). -/

/-- The filter of a representation: subterminators sent to 1. -/
def repFilter {𝒟 : Type u} [Cat.{v} 𝒟] [Logos 𝒞] [Logos 𝒟]
    (T : Functor 𝒞 𝒟) : (Subobject 𝒞 one) → Prop :=
  λ U => @Isomorphic 𝒟 _ (T.obj U.dom) one

/-! ### §1.73 the double-sharp filter bridge `A' = A  ↔  pA##(A') = 1`

  The book's §1.73 argument hinges on a *pure* property of the right-adjoint
  pA## = `rightAdj (term A)`, with no functor `T` involved:

    *"Given A' ⊆ A, consider pA##(A') ⊆ 1.  Note that A' = A iff pA##(A') = 1."*

  We formalize this fact in full.  It is the half of §1.73 that the repo's
  infrastructure (`HasRightAdjointImage.rightAdj`, `InverseImage`, `IsEntire`)
  supports faithfully; the bridge to a functor `T`'s action on subobjects
  (`T(A') ⊊ T(A) ↔ pA##(A') ∉ ℱ(T)`, hence the full `faithful_iff_trivial_filter`)
  still needs a `LogosMap` carrying `T`'s action on `Sub`, recorded MISSING below.

  First a reusable lemma: a subobject is entire iff the top subobject factors
  through it (a split-epi-and-mono is iso). -/

/-- A subobject `S ↣ A` is entire iff the entire subobject is `≤` it, i.e. iff
    its mono `S.arr` is split epic (and, being monic, then iso). -/
theorem isEntire_iff_entire_le {A : 𝒞} (S : Subobject 𝒞 A) :
    Subobject.IsEntire S ↔ Subobject.le (Subobject.entire A) S := by
  constructor
  · -- iso ⇒ its inverse witnesses entire ≤ S
    rintro ⟨g, _h1, h2⟩
    exact ⟨g, by simpa [Subobject.entire] using h2⟩
  · -- entire ≤ S gives a section h of S.arr; mono cancels to make h a 2-sided inverse
    rintro ⟨h, hsec⟩
    have hsec' : h ≫ S.arr = Cat.id A := by simpa [Subobject.entire] using hsec
    refine ⟨h, ?_, hsec'⟩
    -- (S.arr ≫ h) ≫ S.arr = id ≫ S.arr, cancel the mono S.arr on the right
    apply S.monic
    rw [Cat.assoc, hsec', Cat.comp_id, Cat.id_comp]

/-- **§1.73 double-sharp bridge.** For any object `A` in a logos and any
    subobject `A' ⊆ A`, writing `pA = term A : A → 1` for the unique map to the
    terminator and `pA## = rightAdj (term A)`:

        `A' = A   ↔   pA##(A') = 1`.

    (Book §1.73: *"A' = A iff pA##(A') = 1."*)  Proof: `pA##(A')` is entire iff
    `1 ≤ pA##(A')`, iff (adjunction) `pA#(1) ≤ A'`, and `pA#(1) = 1_A` is the top
    of `Sub A`, so this says `1_A ≤ A'`, iff `A'` is entire. -/
theorem isEntire_rightAdj_term_iff [Logos 𝒞] {A : 𝒞} (A' : Subobject 𝒞 A) :
    Subobject.IsEntire (HasRightAdjointImage.rightAdj (term A) A') ↔
    Subobject.IsEntire A' := by
  rw [isEntire_iff_entire_le, isEntire_iff_entire_le]
  -- entire 1 ≤ pA##(A')  ↔  pA#(entire 1) ≤ A'  ↔  entire A ≤ A'
  rw [← HasRightAdjointImage.adjunction (term A) (Subobject.entire one) A']
  constructor
  · -- entire A ≤ pA#(entire 1) ≤ A'
    intro h
    exact Subobject.le_trans (entire_le_inverseImage_entire (term A)) h
  · -- pA#(entire 1) ≤ entire A ≤ A'
    intro h
    exact Subobject.le_trans (le_entire _) h

-- §1.73 (MISSING, narrowed): `faithful_iff_trivial_filter`.
-- With the double-sharp bridge above proven, the only remaining gap is the
-- functor side.  The book reads: *"T(A') ⊆ T(A) iff pA##(A') ∈ ℱ(T)"*, hence
--   T faithful  ⟺  T preserves properness of subobjects  (§1.453)
--               ⟺  ℱ(T) = {1}  (via the bridge `isEntire_rightAdj_term_iff`).
-- The repo's `Functor`/`Faithful` (S1_33) carries only T's action on objects and
-- morphisms; it has NO action `T : Sub A → Sub (T A)` on subobjects, so the
-- premise *"T preserves/reflects properness of subobjects"* and the value
-- `T(A') : Sub (T A)` cannot even be written.  `repFilter` above only inspects
-- `T U.dom` (an object), not a subobject of `T one`.  Stating
-- `faithful_iff_trivial_filter` faithfully therefore requires a `LogosMap T`
-- structure (a CartesianFunctor preserving images, giving `T : Sub A → Sub (T A)`
-- compatibly with `pA##`).  That infra is not in the repo, so the full theorem
-- stays MISSING — but its mathematical core (the pA## ↔ entire bridge) is now
-- proven above.  Per the integrity rule we emit no Sorry on the unstatable form.

/-! ## §1.733 Coprime and Connected

  An object A in a pre-logos is COPRIME if the functor (A,-) preserves
  finite unions, i.e. any finite collection of subobjects of A whose union
  is A must already contain A (§1.733).

  A is CONNECTED if it has exactly two complemented subobjects (§1.733). -/

/-- A is COPRIME (§1.733): the functor (A,-) preserves finite unions,
    meaning any two subobjects whose union covers A must include A itself
    (i.e. one of them must be entire). -/
def Coprime [HasImages 𝒞] [HasSubobjectUnions 𝒞] (A : 𝒞) : Prop :=
  ∀ (U V : Subobject 𝒞 A),
    Subobject.le (Subobject.entire A) (HasSubobjectUnions.union U V) →
    Subobject.IsEntire U ∨ Subobject.IsEntire V

/-- A is CONNECTED (§1.733): it has exactly two complemented subobjects,
    i.e. the only complemented subobjects are ⊥ (bottom) and A (entire).

    "`U` is the bottom subobject" is rendered as `U ≤ ⊥` (subobject order); the
    reverse `⊥ ≤ U` is `PreLogos.bottom_min`, so the two together say `U` and `⊥`
    are the same subobject (mutual `≤`).  We use the order form rather than a raw
    structural `U = ⊥`, since `Subobject` is a structure and structural equality of
    its `dom`/`arr` is strictly stronger than "is the minimal subobject". -/
def Connected [HasImages 𝒞] [PreLogos 𝒞] (A : 𝒞) : Prop :=
  ∀ (U : Subobject 𝒞 A),
    IsComplemented U → Subobject.IsEntire U ∨ Subobject.le U (PreLogos.bottom A)

/-- A FOCAL LOGOS (§1.733): its terminator is a coprime projective.
    Equivalently, r = (1,-) is a representation of pre-logoi. -/
class FocalLogos (𝒞 : Type u) [Cat.{v} 𝒞] extends Logos 𝒞 where
  one_coprime    : Coprime (𝒞 := 𝒞) (one)
  one_projective : Projective (𝒞 := 𝒞) (one)

/-! ## §1.722 Poset is a logos iff Heyting algebra

  "A poset, when viewed as a category, is a logos iff it is a Heyting algebra."
  (Freyd §1.722, combining §1.721 and §1.613.)

  Both directions are proved, now using `HeytingLattice` (§1.85) as the carrier:
  - `(⟹)` = `heytingLattice_is_logos`: any `HeytingLattice` gives a `Logos` on its carrier.
  - `(⟸)` = `thinLogos_is_heytingLattice`: any thin logos (at universe 0) whose underlying
    preorder is antisymmetric (skeletal) produces a `HeytingLattice`. -/

/-- The thin category structure on a Heyting lattice: `Hom a b = PLift (le a b)`. -/
instance heytingLatticeCat (L : HeytingLattice) : Cat.{0} L.carrier where
  Hom x y  := PLift (L.le x y)
  id x     := ⟨L.le_refl x⟩
  comp h k := ⟨L.le_trans h.down k.down⟩
  id_comp _ := rfl; comp_id _ := rfl; assoc _ _ _ := rfl

/-- All parallel morphisms are equal in a Heyting-lattice thin category. -/
theorem hl_thin (L : HeytingLattice) {a b : L.carrier} (f g : a ⟶ b) : f = g := by
  cases f; cases g; rfl

/-- In a Heyting-lattice thin category, covers = isos. -/
theorem hl_cover_iff_iso (L : HeytingLattice) {a b : L.carrier} (f : a ⟶ b) :
    Cover f ↔ IsIso f :=
  ⟨fun hcov => hcov f (Cat.id a) (fun {_W} p q _ => hl_thin L p q) (Cat.id_comp f),
   fun hiso _C m h _hmono _hgm => by
     rw [show IsIso m ↔ L.le b _C from
       ⟨fun ⟨finv, _, _⟩ => finv.down, fun hba => ⟨⟨hba⟩, hl_thin L _ _, hl_thin L _ _⟩⟩]
     exact L.le_trans
       ((⟨fun ⟨finv, _, _⟩ => finv.down, fun hba => ⟨⟨hba⟩, hl_thin L _ _, hl_thin L _ _⟩⟩ :
         IsIso f ↔ L.le b a).mp hiso) h.down⟩

/-- Pullbacks in the Heyting-lattice thin category are binary meets. -/
instance hl_hasPullbacks (L : HeytingLattice) : HasPullbacks L.carrier where
  has := fun {a b _c} _f _g =>
    { cone :=
        { pt := L.meet a b
          π₁ := ⟨L.meet_le_left a b⟩
          π₂ := ⟨L.meet_le_right a b⟩
          w := hl_thin L _ _ }
      lift := fun d => ⟨L.le_meet d.π₁.down d.π₂.down⟩
      lift_fst := fun _ => hl_thin L _ _
      lift_snd := fun _ => hl_thin L _ _
      lift_uniq := fun _c _u _h1 _h2 => hl_thin L _ _ }

/-- Images in the Heyting-lattice thin category: image of `f : a → b` is `a` itself
    (the domain, viewed as a subobject of `b` via `f`). -/
instance hl_hasImages (L : HeytingLattice) : HasImages L.carrier where
  image := fun {a _b} f => { dom := a, arr := f, monic := fun p q _ => hl_thin L p q }
  isImage := fun f => ⟨⟨Cat.id _, Cat.id_comp f⟩, fun _S ⟨g, hg⟩ => ⟨g, hg⟩⟩

/-- §1.722 (⟹): every Heyting algebra, viewed as a thin category, is a logos.

    Construction:
    - Terminator = top element; binary products = meets; pullbacks = meets.
    - Images: image of `f : a → b` is `a ↪ b` (domain as subobject).
    - Covers = isos = equivalences; `PullbacksTransferCovers` follows from
      the pullback square being an isomorphism whenever one leg is.
    - Subobject unions = joins; right-adjoint image `f##(A')` has domain `b ∧ (a → A'.dom)`
      (via the Heyting adjunction `c ≤ a → b ↔ a ∧ c ≤ b`).
    - Bottom subobject of any `A` is `bot ↪ A`. -/
noncomputable def heytingLattice_is_logos (L : HeytingLattice) : Logos L.carrier :=
  letI := hl_hasPullbacks L
  letI := hl_hasImages L
  { toRegularCategory := {
      toHasTerminal := {
        one := L.top
        trm x := ⟨L.le_top x⟩
        uniq f g := hl_thin L f g
      }
      toHasBinaryProducts := {
        prod a b := L.meet a b
        fst := ⟨L.meet_le_left _ _⟩
        snd := ⟨L.meet_le_right _ _⟩
        pair f g := ⟨L.le_meet f.down g.down⟩
        fst_pair _ _ := hl_thin L _ _
        snd_pair _ _ := hl_thin L _ _
        pair_uniq _ _ _ _ _ := hl_thin L _ _
      }
      toHasPullbacks := hl_hasPullbacks L
      toHasImages := hl_hasImages L
      toPullbacksTransferCovers := {
        pullbacks_transfer_covers := by
          intro a b c f g cone hIsPB hCoverF
          rw [hl_cover_iff_iso L] at hCoverF; rw [hl_cover_iff_iso L]
          -- f : a → b iso (b ≤ a), g : c → b; want π₂ : cone.pt → c iso.
          -- Build a cone from c: use g.down ≫ f-iso to get c → a, and id_c.
          have hca : L.le c a := L.le_trans g.down
            ((⟨fun ⟨finv, _, _⟩ => finv.down, fun hba => ⟨⟨hba⟩, hl_thin L _ _, hl_thin L _ _⟩⟩ :
              IsIso f ↔ L.le b a).mp hCoverF)
          let cCone : Cone f g := Cone.mk c ⟨hca⟩ (Cat.id c) (hl_thin L _ _)
          -- The universal property gives a map from c into cone.pt = meet a c.
          -- Its π₂-component is a left-inverse of cone.π₂, making π₂ iso.
          exact (⟨fun ⟨finv, _, _⟩ => finv.down, fun hba => ⟨⟨hba⟩, hl_thin L _ _, hl_thin L _ _⟩⟩ :
            IsIso cone.π₂ ↔ L.le c cone.pt).mpr ((hIsPB cCone).choose.down)
      }
    }
    toHasSubobjectUnions := {
      union := fun {_b} S T =>
        { dom := L.join S.dom T.dom
          arr := ⟨L.join_le S.arr.down T.arr.down⟩
          monic := fun p q _ => hl_thin L p q }
      union_left := fun {_b} S T => ⟨⟨L.le_join_left S.dom T.dom⟩, hl_thin L _ _⟩
      union_right := fun {_b} S T => ⟨⟨L.le_join_right S.dom T.dom⟩, hl_thin L _ _⟩
      union_min := fun {_b} _S _T U hS hT => by
        obtain ⟨hs, _⟩ := hS; obtain ⟨ht, _⟩ := hT
        exact ⟨⟨L.join_le hs.down ht.down⟩, hl_thin L _ _⟩
    }
    -- f## : Sub(A) → Sub(B) given f : A → B; f##(A') has dom = B ∧ (A → A'.dom).
    rightAdj := fun {a b} f A' =>
      { dom := L.meet b (L.imp a A'.dom)
        arr := ⟨L.meet_le_left b (L.imp a A'.dom)⟩
        monic := fun p q _ => hl_thin L p q }
    -- f#(B') ≤ A' ↔ B' ≤ f##(A'): use Heyting adjunction + fact that
    -- InverseImage f B' has dom = meet a B'.dom (definitionally).
    adjunction := fun {a b} f B' A' => by
      simp only [Subobject.le]
      constructor
      · intro ⟨h, _⟩
        -- h.down : L.le (meet a B'.dom) A'.dom
        exact ⟨⟨L.le_meet B'.arr.down ((L.imp_adj (x := B'.dom) (a := a) (b := A'.dom)).mp h.down)⟩, hl_thin L _ _⟩
      · intro ⟨h, _⟩
        -- h.down : L.le B'.dom (meet b (imp a A'.dom))
        have hle_imp := L.le_trans h.down (L.meet_le_right b (L.imp a A'.dom))
        exact ⟨⟨(L.imp_adj (x := B'.dom) (a := a) (b := A'.dom)).mpr hle_imp⟩, hl_thin L _ _⟩
    bottom := fun A =>
      { dom := L.bot, arr := ⟨L.bot_le A⟩, monic := fun p q _ => hl_thin L p q }
    bottom_min := fun {_A} S => ⟨⟨L.bot_le S.dom⟩, hl_thin L _ _⟩
    -- All bottom subobjects have domain L.bot, which is isomorphic to itself.
    bottom_dom_iso := fun _A _B =>
      ⟨⟨L.le_refl L.bot⟩, ⟨⟨L.le_refl L.bot⟩, hl_thin L _ _, hl_thin L _ _⟩⟩
  }

/-! ## §1.722 (⟸): thin logos ⟹ Heyting algebra

  **§1.722 (⟸)**:  A thin category that is a Logos carries a Heyting-algebra structure on
  its object poset: `le a b := Nonempty (a ⟶ b)`, meet = binary product, top = terminator,
  join = domain of the union of the corresponding subterminators, bot = domain of
  `Logos.bottom one`, and implication `a → b` = domain of `rightAdj (term a) (f#b)`
  where `f = term a : a → 1` (Freyd §1.721: `(A₁ → A₂) = f##(A₁ ∩ A₂)` with `f` the
  inclusion of `A₁`).

  The key adjunction `c ≤ (a → b) ↔ a ∧ c ≤ b` is the logos adjunction
  `f#(cSub) ≤ f#(bSub) ↔ cSub ≤ rightAdj f (f#(bSub))` under the canonical
  identification of objects with subterminators of `one`.  -/

/-- §1.722 (⟸): a thin logos (universe 0) induces a Heyting-lattice structure on its
    object type.

    Extraction dictionary:
    - `le a b`   := `Nonempty (a ⟶ b)` (the hom is a Prop in a thin cat)
    - `top`      := `one` (terminator)
    - `meet a b` := `prod a b` (binary product = meet in a thin cat)
    - `join a b` := domain of `union (thinSub a) (thinSub b)` in `Sub(one)`
    - `bot`      := domain of `Logos.bottom one`
    - `imp a b`  := domain of `rightAdj (term a) (f#(thinSub b))`
                    where `f = term a : a → one`  (§1.721 construction)

    The Heyting adjunction `c ≤ (a → b) ↔ a ∧ c ≤ b` follows from the logos
    adjunction `f# ⊣ f##` via the pullback = product identification in a thin cat.

    Axioms: `[Classical.choice]` only (no Sorry).  -/
noncomputable def thinLogos_is_heytingLattice
    {𝒞 : Type} [Cat.{0} 𝒞] [ThinCategory 𝒞] [Logos 𝒞]
    (hskeletal : ∀ {a b : 𝒞}, Nonempty (a ⟶ b) → Nonempty (b ⟶ a) → a = b) :
    HeytingLattice :=
  -- Every object viewed as a subterminator of `one`
  let thinSub : 𝒞 → Subobject 𝒞 one := fun a =>
    ⟨a, term a, fun p q _ => ThinCategory.thin p q⟩
  { carrier       := 𝒞
    le            := fun a b => Nonempty (a ⟶ b)
    le_refl       := fun a   => ⟨Cat.id a⟩
    le_trans      := fun ⟨f⟩ ⟨g⟩ => ⟨f ≫ g⟩
    le_antisymm   := hskeletal
    top           := one
    le_top        := fun a   => ⟨term a⟩
    meet          := fun a b => prod a b
    meet_le_left  := fun _a _b => ⟨fst⟩
    meet_le_right := fun _a _b => ⟨snd⟩
    le_meet       := fun ⟨f⟩ ⟨g⟩ => ⟨pair f g⟩
    join          := fun a b => (HasSubobjectUnions.union (thinSub a) (thinSub b)).dom
    le_join_left  := fun a b =>
      ⟨(HasSubobjectUnions.union_left (thinSub a) (thinSub b)).choose⟩
    le_join_right := fun a b =>
      ⟨(HasSubobjectUnions.union_right (thinSub a) (thinSub b)).choose⟩
    join_le       := fun {_a _b _c} ⟨ha⟩ ⟨hb⟩ =>
      have h := HasSubobjectUnions.union_min (thinSub _) (thinSub _) (thinSub _)
        ⟨ha, ThinCategory.thin _ _⟩ ⟨hb, ThinCategory.thin _ _⟩
      ⟨h.choose⟩
    imp           := fun a b =>
      (Logos.rightAdj (term a) (InverseImage (term a) (thinSub b))).dom
    imp_adj := fun {x a b} => by
      -- R := f##(f#(thinSub b)) in Sub(one), imp a b = R.dom
      let R := Logos.rightAdj (term a) (InverseImage (term a) (thinSub b))
      constructor
      · -- (⟹) Nonempty (prod a x ⟶ b) → Nonempty (x ⟶ R.dom)
        intro ⟨f⟩
        let pb_x := HasPullbacks.has (term a) (thinSub x).arr
        let pb_b := HasPullbacks.has (term a) (thinSub b).arr
        have hle : (InverseImage (term a) (thinSub x)).le (InverseImage (term a) (thinSub b)) :=
          ⟨pb_b.lift ⟨pb_x.cone.pt, pb_x.cone.π₁,
              pair pb_x.cone.π₁ pb_x.cone.π₂ ≫ f, ThinCategory.thin _ _⟩,
           ThinCategory.thin _ _⟩
        exact ⟨((Logos.adjunction (term a) (thinSub x)
          (InverseImage (term a) (thinSub b))).mp hle).choose⟩
      · -- (⟸) Nonempty (x ⟶ R.dom) → Nonempty (prod a x ⟶ b)
        intro ⟨f⟩
        have hxR : (thinSub x).le R := ⟨f, ThinCategory.thin _ _⟩
        obtain ⟨h, _⟩ := (Logos.adjunction (term a) (thinSub x)
          (InverseImage (term a) (thinSub b))).mpr hxR
        let pb_x := HasPullbacks.has (term a) (thinSub x).arr
        let pb_b := HasPullbacks.has (term a) (thinSub b).arr
        exact ⟨pb_x.lift ⟨prod a x, fst, snd, ThinCategory.thin _ _⟩ ≫ h ≫ pb_b.cone.π₂⟩
    bot           := (Logos.bottom (one : 𝒞)).dom
    bot_le        := fun a =>
      ⟨(Logos.bottom_min (thinSub a)).choose⟩ }

/-! ### §1.722 combined: the iff

  **§1.722**: A poset (thin category), when viewed as a category, is a logos iff it is a
  Heyting algebra.

  Both directions are now proved:
  - `(⟹)` = `heytingLattice_is_logos`: any `HeytingLattice` gives a `Logos` on its carrier.
  - `(⟸)` = `thinLogos_is_heytingLattice`: any thin logos (at universe 0) whose preorder
    is antisymmetric (skeletal) produces a `HeytingLattice`.

  These two lemmas state the iff as a round-trip: -/

-- §1.722 forward: every HeytingLattice gives a Logos on its carrier.
noncomputable def section_1722_fwd (L : HeytingLattice) : Logos L.carrier :=
  heytingLattice_is_logos L

-- §1.722 reverse: every thin logos (universe 0, skeletal) gives a HeytingLattice.
noncomputable def section_1722_rev
    {𝒞 : Type} [Cat.{0} 𝒞] [ThinCategory 𝒞] [Logos 𝒞]
    (hskeletal : ∀ {a b : 𝒞}, Nonempty (a ⟶ b) → Nonempty (b ⟶ a) → a = b) :
    HeytingLattice :=
  @thinLogos_is_heytingLattice 𝒞 _ _ _ hskeletal

/-! ## §1.733 Positive pre-logos focal iff connected projective terminator

  "A positive pre-logos is focal iff its terminator is a connected projective."
  (Freyd §1.733.)

  STATEMENT CHOICE.  The book's subject is a *positive pre-logos*; the repo's faithful
  rendering of that is `DisjointBinaryCoproduct` (§1.621/§1.623 — a positive pre-logos
  whose coproduct injections are a disjoint complemented pair).  "Focal" means the
  terminator `1` is *coprime* and *projective* — these are exactly the two extra fields
  `one_coprime`, `one_projective` that `FocalLogos` adds over its `Logos`.  We therefore
  state §1.733 over `[DisjointBinaryCoproduct 𝒞]` with "focal" rendered as the property
  `Coprime one ∧ Projective one`, rather than as `Nonempty (FocalLogos 𝒞)`.

  Why not `Nonempty (FocalLogos 𝒞)`?  `FocalLogos extends Logos`, so that phrasing
  bundles a *fresh* `Logos` instance (hence a fresh `HasTerminal`, fresh `one`, fresh
  `Cover`) independent of the ambient one — `hfl.one_projective` would then be about
  `hfl`'s terminator, not the ambient `one`, an instance mismatch that makes the iff
  unprovable.  Phrasing "focal" as a property of the *ambient* positive pre-logos keeps
  one coherent instance chain on both sides.  (It is also closer to Freyd: a positive
  pre-logos needs no right-adjoint `f##` for this statement.) -/

/-- §1.733 (⟹), coprime ⟹ connected.  If `1` is coprime then every complemented
    subterminator is entire or bottom: a complement pair `U, U₂` with `U ∪ U₂` entire
    forces (coprimeness) `U` entire or `U₂` entire; in the latter case `U ≤ U₂`, so the
    disjointness clause gives `U ≤ ⊥`. -/
theorem coprime_one_implies_connected_one
    [DisjointBinaryCoproduct 𝒞] (hcop : Coprime (𝒞 := 𝒞) one) :
    Connected (𝒞 := 𝒞) one := by
  intro U hU
  obtain ⟨U₂, hdisj, hcover⟩ := hU
  rcases hcop U U₂ hcover with hUe | hU₂e
  · exact Or.inl hUe
  · right
    have hUleU₂ : Subobject.le U U₂ :=
      Subobject.le_trans (le_entire U) ((isEntire_iff_entire_le U₂).mp hU₂e)
    exact hdisj U (Subobject.le_refl U) hUleU₂

/-- §1.733 (⟸), connected + projective ⟹ coprime (Freyd's §1.625 argument).
    Given `U, V ⊆ 1` with `U ∪ V` entire, the copairing `q = case U.arr V.arr :
    U.dom + V.dom → 1` is a cover (its image is `U ∪ V`, entire).  Projectivity of `1`
    splits it: `s ≫ q = id`.  The injections `inl, inr` are a *disjoint complemented*
    pair (positivity), so their inverse images `s#inl, s#inr ⊆ 1` are complemented
    subterminators covering `1`.  Connectedness sends `s#inl` to entire or bottom:
    if entire, `s` factors through `inl` and `U` is entire; if bottom, the cover forces
    `s#inr` entire and `V` is entire. -/
theorem connected_projective_one_implies_coprime_one
    [DisjointBinaryCoproduct 𝒞]
    (hconn : Connected (𝒞 := 𝒞) one) (hproj : Projective (𝒞 := 𝒞) one) :
    Coprime (𝒞 := 𝒞) one := by
  intro U V hcov
  -- q := case U.arr V.arr : U.dom + V.dom → 1 is a cover (image = U ∪ V = entire).
  let q : HasBinaryCoproducts.coprod U.dom V.dom ⟶ one :=
    HasBinaryCoproducts.case U.arr V.arr
  have hq_cover : Cover q := by
    refine (cover_iff_image_entire q).2 (entire_of_entire_le ?_)
    have hUle : U.le (image U.arr) := ⟨image.lift U.arr, image.lift_fac U.arr⟩
    have hVle : V.le (image V.arr) := ⟨image.lift V.arr, image.lift_fac V.arr⟩
    have hmono : (HasSubobjectUnions.union U V).le
        (HasSubobjectUnions.union (image U.arr) (image V.arr)) :=
      HasSubobjectUnions.union_min _ _ _
        (Subobject.le_trans hUle (HasSubobjectUnions.union_left _ _))
        (Subobject.le_trans hVle (HasSubobjectUnions.union_right _ _))
    have huac : (HasSubobjectUnions.union (image U.arr) (image V.arr)).le (image q) :=
      (union_via_coproduct_image U.arr V.arr).2 (image q) (image_allows q)
    exact Subobject.le_trans hcov (Subobject.le_trans hmono huac)
  -- projective 1 splits q:  s ≫ q = id.
  obtain ⟨s, hs⟩ := hproj q hq_cover
  -- inl, inr are a disjoint complemented pair on U.dom + V.dom (positivity).
  have hinl_comp : IsComplementedSub (inlSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inl_mono) :=
    ⟨inrSub inr_mono, inl_inter_inr_le_bottom, inl_union_inr_entire⟩
  have hinr_comp : IsComplementedSub (inrSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inr_mono) :=
    ⟨inlSub inl_mono,
      Subobject.le_trans (Subobject.le_inter (Subobject.inter_le_right _ _)
        (Subobject.inter_le_left _ _)) inl_inter_inr_le_bottom,
      Subobject.le_trans inl_union_inr_entire
        (HasSubobjectUnions.union_min _ _ _
          (HasSubobjectUnions.union_right _ _) (HasSubobjectUnions.union_left _ _))⟩
  -- pull back along s: complemented subterminators of 1.
  have hPl : IsComplemented (InverseImage s (inlSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inl_mono)) :=
    (isComplemented_iff_sub _).2 (invImage_complementedSub s hinl_comp)
  -- factorization: if s#⟨w.dom,e⟩ is entire and e ≫ q = w.arr then w is entire (w = U or V).
  have factor : ∀ (w : Subobject 𝒞 one) (e : w.dom ⟶ HasBinaryCoproducts.coprod U.dom V.dom)
      (he : Monic e) (heq : e ≫ q = w.arr),
      Subobject.IsEntire (InverseImage s ⟨w.dom, e, he⟩) → Subobject.IsEntire w := by
    intro w e he heq hent
    obtain ⟨g0, hg0⟩ := (isEntire_iff_entire_le _).1 hent
    let pb := HasPullbacks.has s (⟨w.dom, e, he⟩ : Subobject 𝒞 _).arr
    have hg0' : g0 ≫ pb.cone.π₁ = Cat.id one := by
      have : (InverseImage s ⟨w.dom, e, he⟩).arr = pb.cone.π₁ := rfl
      simpa [Subobject.entire, this] using hg0
    refine entire_of_entire_le ⟨g0 ≫ pb.cone.π₂, ?_⟩
    show (g0 ≫ pb.cone.π₂) ≫ w.arr = (Subobject.entire one).arr
    have hπ₂ : pb.cone.π₂ ≫ w.arr = pb.cone.π₁ ≫ (s ≫ q) := by
      rw [← heq, ← Cat.assoc, ← pb.cone.w, Cat.assoc]
    calc (g0 ≫ pb.cone.π₂) ≫ w.arr
        = g0 ≫ (pb.cone.π₂ ≫ w.arr) := Cat.assoc _ _ _
      _ = g0 ≫ (pb.cone.π₁ ≫ (s ≫ q)) := by rw [hπ₂]
      _ = g0 ≫ (pb.cone.π₁ ≫ Cat.id one) := by rw [hs]
      _ = (g0 ≫ pb.cone.π₁) ≫ Cat.id one := (Cat.assoc _ _ _).symm
      _ = Cat.id one ≫ Cat.id one := by rw [hg0']
      _ = (Subobject.entire one).arr := by
            show Cat.id one ≫ Cat.id one = Cat.id one
            rw [Cat.id_comp]
  have hinl_eq : (inlSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inl_mono).arr ≫ q = U.arr :=
    HasBinaryCoproducts.case_inl U.arr V.arr
  have hinr_eq : (inrSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inr_mono).arr ≫ q = V.arr :=
    HasBinaryCoproducts.case_inr U.arr V.arr
  rcases hconn _ hPl with hUe | hUbot
  · exact Or.inl (factor U _ inl_mono hinl_eq hUe)
  · -- s#inl ≤ ⊥, so the cover gives s#inr entire, hence V entire.
    right
    have hcover_lr : (Subobject.entire one).le
        (HasSubobjectUnions.union
          (InverseImage s (inlSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inl_mono))
          (InverseImage s (inrSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inr_mono))) :=
      Subobject.le_trans (entire_le_inverseImage_entire s)
        (Subobject.le_trans
          (inverseImage_mono s inl_union_inr_entire)
          (PreLogos.invImage_preserves_union s _ _).1)
    have hle : (HasSubobjectUnions.union
          (InverseImage s (inlSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inl_mono))
          (InverseImage s (inrSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inr_mono))).le
        (InverseImage s (inrSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inr_mono)) :=
      HasSubobjectUnions.union_min _ _ _
        (Subobject.le_trans hUbot (PreLogos.bottom_min _))
        (Subobject.le_refl _)
    have hVe : Subobject.IsEntire
        (InverseImage s (inrSub (𝒞 := 𝒞) (A := U.dom) (B := V.dom) inr_mono)) :=
      entire_of_entire_le (Subobject.le_trans hcover_lr hle)
    exact factor V _ inr_mono hinr_eq hVe

/-- **§1.733**: a *positive pre-logos* is FOCAL iff its terminator is a CONNECTED
    PROJECTIVE.  "Focal" = terminator coprime ∧ projective (the two fields a `FocalLogos`
    adds over its `Logos`); the iff reduces to `Coprime one ↔ Connected one` since
    `Projective one` is common to both sides.  Forward: `coprime_one_implies_connected_one`.
    Backward: `connected_projective_one_implies_coprime_one` (Freyd §1.625). -/
theorem focal_iff_connected_projective [DisjointBinaryCoproduct 𝒞] :
    (Coprime (𝒞 := 𝒞) one ∧ Projective (𝒞 := 𝒞) one) ↔
    (Connected (𝒞 := 𝒞) one ∧ Projective (𝒞 := 𝒞) one) :=
  ⟨fun ⟨hcop, hproj⟩ => ⟨coprime_one_implies_connected_one hcop, hproj⟩,
   fun ⟨hconn, hproj⟩ => ⟨connected_projective_one_implies_coprime_one hconn hproj, hproj⟩⟩

-- §1.734 FOCAL REPRESENTATION THEOREM (every small logos has a collectively faithful
-- family of focal representations) and §1.74 GEOMETRIC REPRESENTATION THEOREM (countable
-- logos faithfully represented in a power of sheaves on ℝ) are recorded MISSING in
-- S1_72.md: stating them faithfully needs the focal-representation / sheaf-on-ℝ
-- infrastructure not yet in the repo. Per the integrity rule we do NOT emit vacuous
-- `: True` stubs for them.

-- BOOK §1.734: Any small (positive) logos has a small, collectively faithful family of
-- focal representations.

-- BOOK §1.734: A logos may be faithfully represented in a single focal logos iff its
-- terminator is coprime.

-- BOOK §1.735: Any countable (positive) logos has a countable, collectively faithful
-- family of focal representations.

-- BOOK §1.735: Any countable logos with a coprime terminator may be faithfully
-- represented in a countable focal logos.

-- BOOK §1.72(10): Every Heyting algebra can be covered by a Heyting algebra for which the
-- functor T = (1,_) is a representation of bicartesian categories.
-- (Via the scone construction; §1.72(11): a free Heyting algebra is a retract of its scone.)

end Freyd
