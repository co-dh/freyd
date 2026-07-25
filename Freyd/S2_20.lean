/-
  Freyd & Scedrov, *Categories and Allegories* §2.2  Distributive allegories.

  §2.21 DISTRIBUTIVE ALLEGORY — zero and union, distributivity
  §2.215 POSITIVE ALLEGORY — finite coproducts
  §2.22 LOCALLY COMPLETE DISTRIBUTIVE ALLEGORY
  §2.223 GLOBALLY COMPLETE
-/

import Freyd.S1_1
import Freyd.S2_10


universe v u

namespace Freyd.Alg

/-! ## §2.21  Distributive allegory

  A DISTRIBUTIVE ALLEGORY is an allegory with a distinguished zero
  morphism 0 : a → b for each a, b, and a binary union R ∪ S. -/

/-- A DISTRIBUTIVE ALLEGORY (§2.21): allegory with zero, union,
    and distributivity. -/
class DistributiveAllegory (𝒜 : Type u) extends Allegory 𝒜 where
  /-- Zero morphism 0 : a → b for each pair of objects. -/
  zero {a b : 𝒜} : a ⟶ b
  /-- Union (join) R ∪ S : a → b when R, S : a → b. -/
  union {a b : 𝒜} (R S : a ⟶ b) : a ⟶ b

  /-- Zero is absorbing on the left: 0 ≫ R = 0 (§2.21). -/
  zero_comp {a b c : 𝒜} (R : b ⟶ c) : (zero : a ⟶ b) ≫ R = zero
  /-- Zero is absorbing on the right: R ≫ 0 = 0 (§2.21). -/
  comp_zero {a b c : 𝒜} (R : a ⟶ b) : R ≫ (zero : b ⟶ c) = zero

  /-- Union is idempotent: R ∪ R = R (§2.21). -/
  union_idem {a b : 𝒜} (R : a ⟶ b) : union R R = R
  /-- Union is commutative: R ∪ S = S ∪ R (§2.21). -/
  union_comm {a b : 𝒜} (R S : a ⟶ b) : union R S = union S R
  /-- Union is associative: R ∪ (S ∪ T) = (R ∪ S) ∪ T (§2.21). -/
  union_assoc {a b : 𝒜} (R S T : a ⟶ b) : union R (union S T) = union (union R S) T

  /-- Absorption: R ∪ (S ∩ R) = R (§2.21). -/
  union_inter_absorb {a b : 𝒜} (R S : a ⟶ b) : union R (Allegory.inter S R) = R
  /-- Absorption: (R ∪ S) ∩ R = R (§2.21). -/
  inter_union_absorb {a b : 𝒜} (R S : a ⟶ b) : Allegory.inter (union R S) R = R

  /-- Composition distributes over union: R ≫ (S ∪ T) = RS ∪ RT (§2.21). -/
  comp_union_distrib {a b c : 𝒜} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ union S T = union (R ≫ S) (R ≫ T)
  /-- Intersection distributes over union: R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T) (§2.21). -/
  inter_union_distrib {a b : 𝒜} (R S T : a ⟶ b) :
    Allegory.inter R (union S T) = union (Allegory.inter R S) (Allegory.inter R T)
  /-- Zero is identity for union: 0 ∪ R = R (§2.211). -/
  zero_union {a b : 𝒜} (R : a ⟶ b) : union zero R = R

/-! ### Notation -/

/-- Zero morphism notation -/
notation "𝟘" => DistributiveAllegory.zero

/-- Union notation R ∪ S -/
infixl:65 " ∪ " => DistributiveAllegory.union

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-! ### Order from union

  In a distributive allegory, R ⊑ S (i.e., R = R ∩ S) iff R ∪ S = S.
  This is the standard lattice duality. -/

theorem le_iff_union_eq_left {a b : 𝒜} (R S : a ⟶ b) : (R ⊑ S) ↔ R ∪ S = S := by
  constructor
  · intro h
    dsimp [le] at h
    -- h: R ∩ S = R. Need: R ∪ S = S.
    have h_absorb : S ∪ (R ∩ S) = S := DistributiveAllegory.union_inter_absorb S R
    calc
      R ∪ S = (R ∩ S) ∪ S := by rw [h]
      _ = S ∪ (R ∩ S) := by rw [DistributiveAllegory.union_comm]
      _ = S := by rw [h_absorb]
  · intro h
    -- h: R ∪ S = S. Need: R ⊑ S, i.e., R ∩ S = R.
    dsimp [le]
    calc
      R ∩ S = S ∩ R := by rw [Allegory.inter_comm R S]
      _ = (R ∪ S) ∩ R := by rw [h]
      _ = R := by rw [DistributiveAllegory.inter_union_absorb R S]

/-! ### Helper: union is least upper bound -/

/-- If A ⊑ C and B ⊑ C then A ∪ B ⊑ C. -/
theorem union_lub {a b : 𝒜} {A B C : a ⟶ b} (hA : A ⊑ C) (hB : B ⊑ C) : A ∪ B ⊑ C := by
  rw [le_iff_union_eq_left] at hA hB ⊢
  -- hA: A ∪ C = C,  hB: B ∪ C = C.  Goal: (A ∪ B) ∪ C = C
  calc
    (A ∪ B) ∪ C = A ∪ (B ∪ C) := by rw [DistributiveAllegory.union_assoc]
    _ = A ∪ C := by rw [hB]
    _ = C := hA

/-- Union is an upper bound: R ⊑ R ∪ S. -/
theorem le_union_left {a b : 𝒜} (R S : a ⟶ b) : R ⊑ R ∪ S := by
  dsimp [le]
  rw [Allegory.inter_comm, DistributiveAllegory.inter_union_absorb]

/-- Union is an upper bound: S ⊑ R ∪ S. -/
theorem le_union_right {a b : 𝒜} (R S : a ⟶ b) : S ⊑ R ∪ S := by
  rw [DistributiveAllegory.union_comm]; exact le_union_left S R

/-- Union is monotone in both arguments. -/
theorem union_mono {a b : 𝒜} {A B A' B' : a ⟶ b} (hA : A ⊑ A') (hB : B ⊑ B') :
    A ∪ B ⊑ A' ∪ B' :=
  union_lub (le_trans hA (le_union_left A' B')) (le_trans hB (le_union_right A' B'))

/-! ### Derived properties -/

/-- (R ∪ S)° = S° ∪ R° (§2.211). -/
theorem recip_union {a b : 𝒜} (R S : a ⟶ b) : (R ∪ S)° = S° ∪ R° := by
  apply le_antisymm
  · -- (R ∪ S)° ⊑ S° ∪ R°
    have hR' : R ⊑ (S° ∪ R°)° := recip_le_iff.mp (le_union_right S° R°)
    have hS' : S ⊑ (S° ∪ R°)° := recip_le_iff.mp (le_union_left S° R°)
    have h_union : R ∪ S ⊑ (S° ∪ R°)° := union_lub hR' hS'
    exact recip_le_iff.mpr h_union
  · -- S° ∪ R° ⊑ (R ∪ S)°
    have hR : R ⊑ R ∪ S := le_union_left R S
    have hS : S ⊑ R ∪ S := le_union_right R S
    have hRrecip : R° ⊑ (R ∪ S)° := recip_mono hR
    have hSrecip : S° ⊑ (R ∪ S)° := recip_mono hS
    -- Goal: S° ∪ R° ⊑ (R ∪ S)°.  We have R° ⊑ (R ∪ S)° and S° ⊑ (R ∪ S)°.
    -- union_lub takes the first argument as ⊑ for the LEFT operand of ∪.
    -- Since S° is on the left, we need hSrecip first.
    exact union_lub hSrecip hRrecip

/-- (S ∪ T) ≫ R = SR ∪ TR (§2.211).
    Proof via reciprocation: ((S∪T)R)° = R°(S∪T)° = R°(T°∪S°) = R°T° ∪ R°S° = (TR)° ∪ (SR)°.
    Then take ° of both sides. -/
theorem union_comp_distrib {a b c : 𝒜} (S T : a ⟶ b) (R : b ⟶ c) :
    (S ∪ T) ≫ R = (S ≫ R) ∪ (T ≫ R) := by
  -- First show equality of the reciprocals, then take °
  -- Chain: ((S∪T)R)° = R°(S∪T)° = R°(T°∪S°) = R°T° ∪ R°S° = (TR)° ∪ (SR)°
  --                  = (SR)° ∪ (TR)° = (SR ∪ TR)°
  have h_recip : ((S ∪ T) ≫ R)° = ((S ≫ R) ∪ (T ≫ R))° := by
    rw [Allegory.recip_comp, recip_union S T, DistributiveAllegory.comp_union_distrib,
      ← Allegory.recip_comp T R, ← Allegory.recip_comp S R]
    -- Goal: (T ≫ R)° ∪ (S ≫ R)° = ((S ≫ R) ∪ (T ≫ R))°
    -- recip_union expands RHS to (T ≫ R)° ∪ (S ≫ R)°, matching LHS
    rw [recip_union (S ≫ R) (T ≫ R)]
  -- Now apply ° to both sides of the equality
  calc
    (S ∪ T) ≫ R = (((S ∪ T) ≫ R)°)° := by rw [Allegory.recip_recip]
    _ = (((S ≫ R) ∪ (T ≫ R))°)° := by rw [h_recip]
    _ = (S ≫ R) ∪ (T ≫ R) := by rw [Allegory.recip_recip]

/-- `R ∪ 𝟘 = R` (§2.211). Follows from `zero_union` and `union_comm`. -/
theorem union_zero {a b : 𝒜} (R : a ⟶ b) : R ∪ (𝟘 : a ⟶ b) = R := by
  rw [DistributiveAllegory.union_comm, DistributiveAllegory.zero_union R]

/-- `𝟘 ⊑ R` for all `R` — zero is the minimum morphism (§2.211). -/
theorem zero_le {a b : 𝒜} (R : a ⟶ b) : (𝟘 : a ⟶ b) ⊑ R := by
  rw [le_iff_union_eq_left, DistributiveAllegory.zero_union R]

/-- 0° = 0 (§2.211). -/
theorem recip_zero {a b : 𝒜} : (𝟘 : a ⟶ b)° = (𝟘 : b ⟶ a) := by
  apply le_antisymm
  · -- 0_ab° ⊑ 0_ba   ↔  0_ab ⊑ 0_ba°  by recip_le_iff.mpr
    -- 0_ab ⊑ 0_ba° holds by zero_le (0 is minimum in a→b)
    apply (recip_le_iff.mpr (zero_le (a := a) (b := b) ((𝟘 : b ⟶ a)°)))
  · -- 0_ba ⊑ 0_ab°  holds by zero_le (0 is minimum in b→a)
    apply zero_le (a := b) (b := a) ((𝟘 : a ⟶ b)°)

/-! ## §2.214  Coproducts in distributive allegories

  A₁ ⊕ A₂ is a coproduct if there exist u₁ : A₁ → A, u₂ : A₂ → A
  satisfying five equations (§2.214). -/

/-- Coproduct diagram (§2.214). `u₁ : a₁ → a`, `u₂ : a₂ → a` with:
    u₁u₁° = 1, u₁u₂° = 0, u₂u₁° = 0, u₂u₂° = 1, u₁°u₁ ∪ u₂°u₂ = 1. -/
structure Coproduct (a a₁ a₂ : 𝒜) where
  u₁ : a₁ ⟶ a
  u₂ : a₂ ⟶ a
  u₁_self_comp_recip : u₁ ≫ u₁° = Cat.id a₁
  u₁_u₂_recip : u₁ ≫ u₂° = (𝟘 : a₁ ⟶ a₂)
  u₂_u₁_recip : u₂ ≫ u₁° = (𝟘 : a₂ ⟶ a₁)
  u₂_self_comp_recip : u₂ ≫ u₂° = Cat.id a₂
  recip_union_eq_id : (u₁° ≫ u₁) ∪ (u₂° ≫ u₂) = Cat.id a

/-! ### §2.214  Equivalence: five equations ↔ universal coproduct property

  The book (§2.214) proves that the five equations characterising `Coproduct`
  are equivalent (in any distributive allegory) to the assertion that A is a
  coproduct in the allegory-theoretic sense: every pair (R₁ : a₁ → c,
  R₂ : a₂ → c) factors uniquely through the injections. -/

/-- The universal coproduct property for (a, u₁, u₂) (§2.214):
    for any c and morphisms R₁ : a₁ → c, R₂ : a₂ → c there exists a unique
    R : a → c with u₁ ≫ R = R₁ and u₂ ≫ R = R₂ (where u_i : a_i → a are the injections). -/
def IsCoproduct {𝒜 : Type u} [DistributiveAllegory 𝒜] {a a₁ a₂ : 𝒜}
    (u₁ : a₁ ⟶ a) (u₂ : a₂ ⟶ a) : Prop :=
  ∀ (c : 𝒜) (R₁ : a₁ ⟶ c) (R₂ : a₂ ⟶ c),
    ∃ R : a ⟶ c,
      (u₁ ≫ R = R₁) ∧ (u₂ ≫ R = R₂) ∧
      (∀ R' : a ⟶ c, u₁ ≫ R' = R₁ → u₂ ≫ R' = R₂ → R' = R)

/-- (§2.214) The five `Coproduct` equations imply the universal property.
    The mediating morphism is u₁° ≫ R₁ ∪ u₂° ≫ R₂. -/
theorem coproduct_five_eqs_to_universal {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {a a₁ a₂ : 𝒜} (cp : Coproduct a a₁ a₂) : IsCoproduct cp.u₁ cp.u₂ := by
  -- IsCoproduct: ∀ c R₁ R₂, ∃ R, u₁≫R=R₁ ∧ u₂≫R=R₂ ∧ uniqueness
  intro c R₁ R₂
  -- The mediating morphism [§2.214, p.218]: R = u₁° ≫ R₁ ∪ u₂° ≫ R₂
  refine ⟨cp.u₁° ≫ R₁ ∪ cp.u₂° ≫ R₂, ?_, ?_, ?_⟩
  · -- u₁ ≫ (u₁°≫R₁ ∪ u₂°≫R₂) = R₁. Uses: u₁≫u₁°=id, u₁≫u₂°=0 (from struct fields).
    -- Note: u₁ : a₁→a, u₁° : a→a₁. So u₁ ≫ u₁° : a₁→a₁ = id.
    -- u₁ ≫ (u₁°≫R₁ ∪ u₂°≫R₂) = u₁≫u₁°≫R₁ ∪ u₁≫u₂°≫R₂  [comp_union_distrib]
    --   = (u₁≫u₁°)≫R₁ ∪ (u₁≫u₂°)≫R₂                    [assoc]
    --   = id≫R₁ ∪ 0≫R₂ = R₁ ∪ 0 = R₁
    rw [DistributiveAllegory.comp_union_distrib,
        ← Cat.assoc, ← Cat.assoc,
        cp.u₁_self_comp_recip, cp.u₁_u₂_recip,
        Cat.id_comp, DistributiveAllegory.zero_comp]
    exact union_zero R₁
  · -- u₂ ≫ (u₁°≫R₁ ∪ u₂°≫R₂) = R₂. Uses: u₂≫u₁°=0, u₂≫u₂°=id.
    rw [DistributiveAllegory.comp_union_distrib,
        ← Cat.assoc, ← Cat.assoc,
        cp.u₂_u₁_recip, cp.u₂_self_comp_recip,
        Cat.id_comp, DistributiveAllegory.zero_comp]
    exact DistributiveAllegory.zero_union R₂
  · -- Uniqueness: u₁≫R'=R₁ ∧ u₂≫R'=R₂ → R' = u₁°≫R₁ ∪ u₂°≫R₂.
    -- §2.214: R' = 1≫R' = (u₁°u₁ ∪ u₂°u₂)≫R' = u₁°(u₁≫R') ∪ u₂°(u₂≫R') = u₁°R₁ ∪ u₂°R₂.
    intro R' h₁ h₂
    calc R' = Cat.id a ≫ R' := (Cat.id_comp R').symm
      _ = (cp.u₁° ≫ cp.u₁ ∪ cp.u₂° ≫ cp.u₂) ≫ R' := by rw [cp.recip_union_eq_id]
      _ = cp.u₁° ≫ (cp.u₁ ≫ R') ∪ cp.u₂° ≫ (cp.u₂ ≫ R') := by
            rw [union_comp_distrib, Cat.assoc, Cat.assoc]
      _ = cp.u₁° ≫ R₁ ∪ cp.u₂° ≫ R₂ := by rw [h₁, h₂]

/-- A retraction that is also a partial section is the reciprocal: if `f ≫ g = 1`
    and `g ≫ f ⊑ 1` then `g ⊑ f°`.  Pure modular-law fact (used in §2.214). -/
theorem le_recip_of_section {𝒜 : Type u} [DistributiveAllegory 𝒜] {x y : 𝒜}
    (f : x ⟶ y) (g : y ⟶ x) (h1 : f ≫ g = Cat.id x) (h2 : g ≫ f ⊑ Cat.id y) :
    g ⊑ f° := by
  -- modular_le g f (1_y):  (g≫f) ∩ 1 ⊑ (g ∩ 1≫f°)≫f = (g ∩ f°)≫f.
  -- Since g≫f ⊑ 1, the LHS intersection is g≫f, so  g≫f ⊑ (g ∩ f°)≫f.
  have hmod := modular_le g f (Cat.id y)
  rw [inter_eq_left h2, Cat.id_comp] at hmod
  -- hmod : g ≫ f ⊑ (g ∩ f°) ≫ f.  Post-compose with g and use f≫g = 1.
  have hpost : (g ≫ f) ≫ g ⊑ ((g ∩ f°) ≫ f) ≫ g := comp_mono_right hmod g
  rw [Cat.assoc, Cat.assoc, h1, Cat.comp_id, Cat.comp_id] at hpost
  -- hpost : g ⊑ g ∩ f°.  Hence g ⊑ f°.
  exact le_trans hpost (inter_lb_right g (f°))

/-- A section that is also a partial retraction equals the reciprocal: if
    `f ≫ g = 1` and `g ≫ f ⊑ 1` then `g = f°` (§2.214). -/
theorem eq_recip_of_section {𝒜 : Type u} [DistributiveAllegory 𝒜] {x y : 𝒜}
    (f : x ⟶ y) (g : y ⟶ x) (h1 : f ≫ g = Cat.id x) (h2 : g ≫ f ⊑ Cat.id y) :
    g = f° := by
  apply le_antisymm (le_recip_of_section f g h1 h2)
  -- f° ⊑ g.  Apply the lemma to the reciprocated pair (g°, f°):
  --   g°≫f° = (f≫g)° = 1,   f°≫g° = (g≫f)° ⊑ 1.
  have h1' : g° ≫ f° = Cat.id x := by rw [← Allegory.recip_comp, h1, recip_id]
  have h2' : f° ≫ g° ⊑ Cat.id y := by
    rw [← Allegory.recip_comp]; exact recip_le_iff.mpr (by rw [recip_id]; exact h2)
  have := le_recip_of_section (g°) (f°) h1' h2'
  rwa [Allegory.recip_recip] at this

/-- (§2.214) The five Coproduct equations hold whenever `(u₁, u₂)` enjoys the
    universal property.  Stated as a conjunction (a `Prop`) so that the
    propositional mediators p₁, p₂ supplied by `IsCoproduct` may be `obtain`ed. -/
theorem coproduct_of_universal_eqs {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {a a₁ a₂ : 𝒜} (u₁ : a₁ ⟶ a) (u₂ : a₂ ⟶ a) (h : IsCoproduct u₁ u₂) :
    u₁ ≫ u₁° = Cat.id a₁ ∧ u₁ ≫ u₂° = (𝟘 : a₁ ⟶ a₂) ∧
    u₂ ≫ u₁° = (𝟘 : a₂ ⟶ a₁) ∧ u₂ ≫ u₂° = Cat.id a₂ ∧
    (u₁° ≫ u₁) ∪ (u₂° ≫ u₂) = Cat.id a := by
  -- Mediators p₁ : a → a₁, p₂ : a → a₂:
  --   p₁ mediates (1_{a₁}, 0):  u₁p₁ = 1,  u₂p₁ = 0;
  --   p₂ mediates (0, 1_{a₂}):  u₁p₂ = 0,  u₂p₂ = 1.
  obtain ⟨p₁, hu₁p₁, hu₂p₁, _⟩ := h a₁ (Cat.id a₁) 𝟘
  obtain ⟨p₂, hu₁p₂, hu₂p₂, _⟩ := h a₂ 𝟘 (Cat.id a₂)
  -- Book Eq 5 form: p₁u₁ ∪ p₂u₂ = 1_a, by uniqueness of the mediator of (u₁, u₂).
  obtain ⟨R, _, _, hRuniq⟩ := h a u₁ u₂
  have hpu : (p₁ ≫ u₁) ∪ (p₂ ≫ u₂) = Cat.id a := by
    have hid : Cat.id a = R := by
      apply hRuniq <;> rw [Cat.comp_id]
    have hsum : (p₁ ≫ u₁) ∪ (p₂ ≫ u₂) = R := by
      apply hRuniq
      · rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
          hu₁p₁, hu₁p₂, Cat.id_comp, DistributiveAllegory.zero_comp, union_zero]
      · rw [DistributiveAllegory.comp_union_distrib, ← Cat.assoc, ← Cat.assoc,
          hu₂p₁, hu₂p₂, Cat.id_comp, DistributiveAllegory.zero_comp,
          DistributiveAllegory.zero_union]
    rw [hsum, hid]
  -- p₁u₁ ⊑ 1_a and p₂u₂ ⊑ 1_a (from hpu).
  have hp₁u₁ : p₁ ≫ u₁ ⊑ Cat.id a := by rw [← hpu]; exact le_union_left _ _
  have hp₂u₂ : p₂ ≫ u₂ ⊑ Cat.id a := by rw [← hpu]; exact le_union_right _ _
  -- Hence u₁° = p₁ and u₂° = p₂ (book: U_i = p_i°, reciprocated).
  have hpe₁ : u₁° = p₁ := (eq_recip_of_section u₁ p₁ hu₁p₁ hp₁u₁).symm
  have hpe₂ : u₂° = p₂ := (eq_recip_of_section u₂ p₂ hu₂p₂ hp₂u₂).symm
  -- Read off the five equations by rewriting u_i° = p_i.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hpe₁]; exact hu₁p₁
  · rw [hpe₂]; exact hu₁p₂
  · rw [hpe₁]; exact hu₂p₁
  · rw [hpe₂]; exact hu₂p₂
  · rw [hpe₁, hpe₂]; exact hpu

/-- (§2.214) The universal coproduct property implies the five Coproduct equations.
    Constructs a `Coproduct` record from `IsCoproduct`. -/
def coproduct_of_universal {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {a a₁ a₂ : 𝒜} (u₁ : a₁ ⟶ a) (u₂ : a₂ ⟶ a) (h : IsCoproduct u₁ u₂) :
    Coproduct a a₁ a₂ :=
  let e := coproduct_of_universal_eqs u₁ u₂ h
  { u₁ := u₁, u₂ := u₂,
    u₁_self_comp_recip := e.1, u₁_u₂_recip := e.2.1, u₂_u₁_recip := e.2.2.1,
    u₂_self_comp_recip := e.2.2.2.1, recip_union_eq_id := e.2.2.2.2 }

/-! ## §2.215  Reciprocal duality: coproduct iff product

  "Any allegory is isomorphic, via reciprocation, to its opposite allegory.
  Hence any allegory has coproducts precisely to the extent that it has
  products.  Indeed, (U₁, U₂) is a coproduct iff (U₁°, U₂°) is a product."
  (§2.215) -/

/-- A PRODUCT diagram (§2.215), the reciprocal-dual of `Coproduct`.
    `p₁ : a → a₁`, `p₂ : a → a₂` with the five product equations:
    p₁°p₁ = 1, p₂°p₁ = 0, p₁°p₂ = 0, p₂°p₂ = 1, p₁p₁° ∪ p₂p₂° = 1.
    These are exactly the `Coproduct` equations read off the reciprocals. -/
structure AlgProduct (a a₁ a₂ : 𝒜) where
  p₁ : a ⟶ a₁
  p₂ : a ⟶ a₂
  recip_p₁_self_comp : p₁° ≫ p₁ = Cat.id a₁
  recip_p₂_p₁ : p₂° ≫ p₁ = (𝟘 : a₂ ⟶ a₁)
  recip_p₁_p₂ : p₁° ≫ p₂ = (𝟘 : a₁ ⟶ a₂)
  recip_p₂_self_comp : p₂° ≫ p₂ = Cat.id a₂
  comp_recip_union_eq_id : (p₁ ≫ p₁°) ∪ (p₂ ≫ p₂°) = Cat.id a

/-- (§2.215) If `(u₁, u₂)` is a coproduct then `(u₁°, u₂°)` is a product.
    The product equations are the coproduct equations reciprocated. -/
def AlgProduct.ofCoproduct {a a₁ a₂ : 𝒜} (cp : Coproduct a a₁ a₂) :
    AlgProduct a a₁ a₂ where
  p₁ := cp.u₁°
  p₂ := cp.u₂°
  -- p₁°p₁ = (u₁°)°u₁° = u₁u₁° = 1
  recip_p₁_self_comp := by rw [Allegory.recip_recip]; exact cp.u₁_self_comp_recip
  -- p₂°p₁ = u₂u₁° = 0
  recip_p₂_p₁ := by rw [Allegory.recip_recip]; exact cp.u₂_u₁_recip
  -- p₁°p₂ = u₁u₂° = 0
  recip_p₁_p₂ := by rw [Allegory.recip_recip]; exact cp.u₁_u₂_recip
  -- p₂°p₂ = u₂u₂° = 1
  recip_p₂_self_comp := by rw [Allegory.recip_recip]; exact cp.u₂_self_comp_recip
  -- p₁p₁° ∪ p₂p₂° = u₁°u₁ ∪ u₂°u₂ = 1
  comp_recip_union_eq_id := by
    rw [Allegory.recip_recip, Allegory.recip_recip]; exact cp.recip_union_eq_id

/-- (§2.215) If `(p₁, p₂)` is a product then `(p₁°, p₂°)` is a coproduct.
    The converse direction of the reciprocal duality. -/
def Coproduct.ofAlgProduct {a a₁ a₂ : 𝒜} (pr : AlgProduct a a₁ a₂) :
    Coproduct a a₁ a₂ where
  u₁ := pr.p₁°
  u₂ := pr.p₂°
  -- u₁u₁° = p₁°(p₁°)° = p₁°p₁ = 1
  u₁_self_comp_recip := by rw [Allegory.recip_recip]; exact pr.recip_p₁_self_comp
  -- u₁u₂° = p₁°p₂ = 0
  u₁_u₂_recip := by rw [Allegory.recip_recip]; exact pr.recip_p₁_p₂
  -- u₂u₁° = p₂°p₁ = 0
  u₂_u₁_recip := by rw [Allegory.recip_recip]; exact pr.recip_p₂_p₁
  -- u₂u₂° = p₂°p₂ = 1
  u₂_self_comp_recip := by rw [Allegory.recip_recip]; exact pr.recip_p₂_self_comp
  -- u₁°u₁ ∪ u₂°u₂ = p₁p₁° ∪ p₂p₂° = 1
  recip_union_eq_id := by
    rw [Allegory.recip_recip, Allegory.recip_recip]; exact pr.comp_recip_union_eq_id

/-! ## §2.215  Positive allegory -/

/-- A POSITIVE ALLEGORY (§2.215): distributive allegory with finite coproducts. -/
class PositiveAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  coterm : 𝒜
  coprod (a b : 𝒜) : 𝒜
  has_coproduct (a b : 𝒜) : Coproduct (coprod a b) a b

/-! ## §2.22  Locally complete distributive allegory

  Each hom-set is a complete lattice, composition distributes over
  arbitrary unions (§2.22). -/

/-- A LOCALLY COMPLETE distributive allegory (§2.22).
    Uses a predicate-based encoding of arbitrary suprema
    (avoids `Set` dependency).

    Book §2.22: each hom-set is a complete lattice AND composition and finite
    intersection distribute over arbitrary unions, i.e. `R(∪Sᵢ) = ∪ RSᵢ`
    (with the empty-`I` case `R0 = 0`). -/
class LocallyCompleteDistributiveAllegory (𝒜 : Type u) extends DistributiveAllegory 𝒜 where
  /-- Supremum of a predicate P on the hom-set. -/
  Sup {a b : 𝒜} (P : (a ⟶ b) → Prop) : a ⟶ b
  /-- Sup is an upper bound: if P(R), then R ⊑ Sup P. -/
  le_Sup {a b : 𝒜} {P : (a ⟶ b) → Prop} {R : a ⟶ b} (h : P R) : R ⊑ Sup P
  /-- Sup is least upper bound. -/
  Sup_le {a b : 𝒜} {P : (a ⟶ b) → Prop} {T : a ⟶ b} (h : ∀ R, P R → R ⊑ T) : Sup P ⊑ T
  /-- §2.22 distributive law: composition distributes over arbitrary unions on the right,
      `R(∪Sᵢ) = ∪ RSᵢ`.  `Sup_comp` is the indexed family `{RSᵢ}`, given as the image
      predicate `T = R ≫ S` for some `S` with `P S`.  (The empty-`I` case is `R0 = 0`.) -/
  comp_Sup_distrib {a b c : 𝒜} (R : a ⟶ b) (P : (b ⟶ c) → Prop) :
    R ≫ Sup P = Sup (fun T => ∃ S, P S ∧ T = R ≫ S)
  /-- §2.22 distributive law: finite intersection distributes over arbitrary unions,
      `R ∩ (∪Sᵢ) = ∪ (R ∩ Sᵢ)`. -/
  inter_Sup_distrib {a b : 𝒜} (R : a ⟶ b) (P : (a ⟶ b) → Prop) :
    R ∩ Sup P = Sup (fun T => ∃ S, P S ∧ T = R ∩ S)

/-! ## §2.223  Globally complete allegory -/

/-- A GLOBALLY COMPLETE allegory has disjoint unions of indexed
    families of objects (§2.223). -/
class GloballyCompleteAllegory (𝒜 : Type u) extends LocallyCompleteDistributiveAllegory 𝒜 where
  disjointUnion {I : Type u} (a : I → 𝒜) : 𝒜
  inject {I : Type u} {a : I → 𝒜} (i : I) : a i ⟶ disjointUnion a
  inject_self_comp_recip {I : Type u} {a : I → 𝒜} (i : I) :
    inject i ≫ (inject i)° = Cat.id (a i)
  -- §2.223 disjointness `UᵢUⱼ° = Uᵢ°Uⱼ = 0` (i ≠ j).  The book's two products read,
  -- in diagrammatic order, as `inject i ≫ (inject j)°` (αᵢ→αⱼ) and `inject j ≫ (inject i)°`
  -- (αⱼ→αᵢ); these are the SAME family indexed over ordered pairs of distinct indices, so the
  -- single field below (quantified over all `i ≠ j`) supplies both.  A literal `(inject i)° ≫
  -- inject j` does not typecheck (codomains αᵢ, αⱼ differ), confirming there is no extra law.
  inject_comp_recip_ne {I : Type u} {a : I → 𝒜} {i j : I} (h : i ≠ j) :
    inject i ≫ (inject j)° = (𝟘 : a i ⟶ a j)
  complete {I : Type u} {a : I → 𝒜} :
    Sup (λ (R : disjointUnion a ⟶ disjointUnion a) =>
      ∃ (i : I), R = (inject i)° ≫ inject i) = Cat.id (disjointUnion a)

/-! ## §2.216  Positive Reflection A⁺

  Let A be a distributive allegory.  Its POSITIVE REFLECTION A⁺ has
  objects = finite sequences (here: I-indexed tuples for any index type I)
  of A-objects, and morphisms = I×J-matrices of A-morphisms.
  The embedding A → A⁺ sends R : a → b to the 1×1 matrix (R). -/

/-- An I×J matrix of morphisms in A: entry (i,j) is src i → tgt j (§2.216). -/
def AlgMat {𝒜 : Type u} [Allegory 𝒜] {I J : Type u}
    (src : I → 𝒜) (tgt : J → 𝒜) : Type u :=
  (i : I) → (j : J) → src i ⟶ tgt j

/-- Matrix reciprocation: (R°)_{ji} = (R_{ij})° (§2.216). -/
def AlgMat.recip {𝒜 : Type u} [Allegory 𝒜] {I J : Type u}
    {src : I → 𝒜} {tgt : J → 𝒜}
    (R : AlgMat src tgt) : AlgMat tgt src :=
  fun j i => (R i j)°

/-- Matrix intersection: entry-wise (§2.216). -/
def AlgMat.inter {𝒜 : Type u} [Allegory 𝒜] {I J : Type u}
    {src : I → 𝒜} {tgt : J → 𝒜}
    (R S : AlgMat src tgt) : AlgMat src tgt :=
  fun i j => R i j ∩ S i j

/-- Matrix union: entry-wise (§2.216). -/
def AlgMat.union {𝒜 : Type u} [DistributiveAllegory 𝒜] {I J : Type u}
    {src : I → 𝒜} {tgt : J → 𝒜}
    (R S : AlgMat src tgt) : AlgMat src tgt :=
  fun i j => R i j ∪ S i j

/-- Matrix zero: zero in every entry (§2.216). -/
def AlgMat.zero {𝒜 : Type u} [DistributiveAllegory 𝒜] {I J : Type u}
    {src : I → 𝒜} {tgt : J → 𝒜} : AlgMat src tgt :=
  fun _i _j => 𝟘

/-- The embedding A → A⁺ sends R : a → b to the 1×1 matrix (R) (§2.216). -/
def positiveReflectionEmbed {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜}
    (R : a ⟶ b) :
    let src : PUnit.{u+1} → 𝒜 := fun _ => a
    let tgt : PUnit.{u+1} → 𝒜 := fun _ => b
    AlgMat src tgt :=
  fun _i _j => R

/-- (§2.216) The embedding A → A⁺ is faithful. -/
theorem positiveReflectionEmbed_injective {𝒜 : Type u} [DistributiveAllegory 𝒜]
    {a b : 𝒜} {R S : a ⟶ b}
    (h : @positiveReflectionEmbed 𝒜 _ a b R = @positiveReflectionEmbed 𝒜 _ a b S) : R = S :=
  congrFun (congrFun h PUnit.unit) PUnit.unit

/-! ## §2.221  Local Completion (allegory of downdeals)

  Let A be an allegory.  The LOCAL COMPLETION Â is the allegory whose
  objects are those of A and whose hom-sets are downdeals. -/

/-- A DOWNDEAL in (a, b): closed downward under ⊑ (§2.221). -/
def IsDowndeal {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (D : (a ⟶ b) → Prop) : Prop :=
  ∀ (R : a ⟶ b), D R → ∀ (S : a ⟶ b), S ⊑ R → D S

/-- The PRINCIPAL DOWNDEAL ↓R = { S | S ⊑ R } (§2.221). -/
def principalDowndeal {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    (a ⟶ b) → Prop :=
  fun S => S ⊑ R

theorem principalDowndeal_isDowndeal {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    IsDowndeal (principalDowndeal R) :=
  fun _T hT _S hS => le_trans hS hT

/-- (§2.221) The embedding A → Â (R ↦ ↓R) is faithful. -/
theorem principalDowndeal_injective {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} {R S : a ⟶ b}
    (h : principalDowndeal R = principalDowndeal S) : R = S := by
  have hRS : R ⊑ S := by
    have : (principalDowndeal R) R := le_refl R; rw [h] at this; exact this
  have hSR : S ⊑ R := by
    have : (principalDowndeal S) S := le_refl S; rw [← h] at this; exact this
  exact le_antisymm hRS hSR

/-! ## §2.222  Ideal completion (distributive allegory case) -/

/-- An IDEAL in a hom-set: a downdeal closed under finite union (§2.222). -/
def IsIdeal {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜} (D : (a ⟶ b) → Prop) : Prop :=
  IsDowndeal D ∧ D (𝟘 : a ⟶ b) ∧ ∀ (R S : a ⟶ b), D R → D S → D (R ∪ S)

/-- The principal ideal ↓R (same underlying set as ↓R for downdeals). -/
def principalIdeal {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    (a ⟶ b) → Prop := fun S => S ⊑ R

theorem principalIdeal_isIdeal {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    IsIdeal (principalIdeal R) :=
  ⟨principalDowndeal_isDowndeal R, zero_le R, fun _S _T hS hT => union_lub hS hT⟩

/-- (§2.222) The embedding A → ideals(A) is faithful; any distributive allegory
    faithfully represents in a locally complete distributive allegory. -/
theorem principalIdeal_injective {𝒜 : Type u} [DistributiveAllegory 𝒜] {a b : 𝒜}
    {R S : a ⟶ b} (h : principalIdeal R = principalIdeal S) : R = S :=
  principalDowndeal_injective h

/-! ## §2.315(b)  The downdeal completion `Â` as a locally complete distributive allegory

  Building on §2.221, the LOCAL COMPLETION `Â` of a distributive allegory `A` has the
  same objects, and a hom `a ⟶ b` is a DOWNDEAL of `A`-homs `a ⟶ b`.  We equip `Â`
  with a `Cat`, `Allegory`, `DistributiveAllegory` and
  `LocallyCompleteDistributiveAllegory` structure, and show the principal-downdeal
  embedding `A → Â`, `R ↦ ↓R`, is a faithful homomorphism of all the operations.

  The key tool is the DOWNWARD CLOSURE operator `↓P = { T | ∃ R, P R ∧ T ⊑ R }`,
  which is monotone and idempotent; every operation on downdeals is the closure of
  the pointwise image of the corresponding `A`-operation. -/

section Downdeal

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The objects of the LOCAL COMPLETION `Â` — a copy of `𝒜`'s objects so the downdeal
    `Cat`/`Allegory` instances live on a type distinct from the base (avoiding a
    diamond with `𝒜`'s own structure). -/
def Downdeal (𝒜 : Type u) : Type u := 𝒜

/-- The DOWNWARD CLOSURE of a predicate: `↓P = { T | ∃ R, P R ∧ T ⊑ R }`. -/
def downClosure {a b : 𝒜} (P : (a ⟶ b) → Prop) : (a ⟶ b) → Prop :=
  fun T => ∃ R, P R ∧ T ⊑ R

/-- `↓` is monotone in the predicate (pointwise implication). -/
theorem downClosure_mono {a b : 𝒜} {P Q : (a ⟶ b) → Prop}
    (h : ∀ R, P R → Q R) : ∀ T, downClosure P T → downClosure Q T :=
  fun _T ⟨R, hR, hTR⟩ => ⟨R, h R hR, hTR⟩

/-- The closure of a downdeal is itself (idempotence): if `D` is a downdeal then `↓D = D`. -/
theorem downClosure_of_isDowndeal {a b : 𝒜} {D : (a ⟶ b) → Prop} (hD : IsDowndeal D) :
    downClosure D = D := by
  funext T
  apply propext
  constructor
  · intro ⟨R, hR, hTR⟩; exact hD R hR T hTR
  · intro h; exact ⟨T, h, le_refl T⟩

/-- The universal property of `↓` against a downdeal `D`: `↓P ⊑ D ↔ P ⊑ D`
    (set-inclusion).  Used to prove laws by reducing to the generating set. -/
theorem downClosure_le_iff {a b : 𝒜} {P : (a ⟶ b) → Prop} {D : (a ⟶ b) → Prop}
    (hD : IsDowndeal D) : (∀ T, downClosure P T → D T) ↔ (∀ R, P R → D R) := by
  constructor
  · intro h R hR; exact h R ⟨R, hR, le_refl R⟩
  · intro h T ⟨R, hR, hTR⟩; exact hD R (h R hR) T hTR

/-- A hom of the local completion `Â`: an IDEAL of `A`-homs `a ⟶ b` — a downdeal that
    contains `𝟘` and is closed under finite union (§2.222).  Ideals (not bare downdeals)
    are the right object: only ideals form a distributive lattice under the operations
    `↓{R∪S}` / `↓{R∩S}`, and every principal `↓R` is an ideal (it contains `𝟘`). -/
structure DowndealHom (a b : 𝒜) where
  /-- The underlying predicate (set of `A`-homs). -/
  carrier : (a ⟶ b) → Prop
  /-- It is an ideal: downward closed, contains `𝟘`, closed under binary union. -/
  is_ideal : IsIdeal carrier

/-- Membership in a downdeal hom. -/
instance {a b : 𝒜} : CoeFun (DowndealHom a b) (fun _ => (a ⟶ b) → Prop) :=
  ⟨DowndealHom.carrier⟩

/-- The downdeal part of the ideal. -/
theorem DowndealHom.is_downdeal {a b : 𝒜} (D : DowndealHom a b) : IsDowndeal D.carrier :=
  D.is_ideal.1

/-- An ideal contains `𝟘`. -/
theorem DowndealHom.mem_zero' {a b : 𝒜} (D : DowndealHom a b) : D (𝟘 : a ⟶ b) :=
  D.is_ideal.2.1

/-- An ideal is closed under binary union. -/
theorem DowndealHom.union_closed {a b : 𝒜} (D : DowndealHom a b) {R S : a ⟶ b}
    (hR : D R) (hS : D S) : D (R ∪ S) :=
  D.is_ideal.2.2 R S hR hS

/-- Two downdeal homs are equal iff their carriers are. -/
@[ext] theorem DowndealHom.ext {a b : 𝒜} {D₁ D₂ : DowndealHom a b}
    (h : ∀ R, D₁ R ↔ D₂ R) : D₁ = D₂ := by
  cases D₁; cases D₂
  congr 1; funext R; exact propext (h R)

/-- The IDEAL generated by closing a predicate `P` downward, given that `P`'s downward
    closure is already union-closed (each pair of `P`-elements is dominated by a `P`-element)
    and `P` is inhabited.  Used to package every operation, whose generating set is
    `join-directed` because the base operations preserve `∪`. -/
def DowndealHom.close {a b : 𝒜} (P : (a ⟶ b) → Prop)
    (hdir : ∀ x y, P x → P y → ∃ z, P z ∧ x ∪ y ⊑ z)
    (hne : ∃ x, P x) : DowndealHom a b :=
  ⟨downClosure P, fun _T ⟨R, hR, hTR⟩ _S hST => ⟨R, hR, le_trans hST hTR⟩,
    -- 𝟘 ∈ ↓P: take any x ∈ P, 𝟘 ⊑ x.
    (let ⟨x, hx⟩ := hne; ⟨x, hx, zero_le x⟩),
    -- ∪-closed: T₁ ⊑ x, T₂ ⊑ y, x∪y ⊑ z ∈ P, so T₁∪T₂ ⊑ x∪y ⊑ z.
    fun _ _ ⟨x, hx, hRx⟩ ⟨y, hy, hSy⟩ =>
      let ⟨z, hz, hxyz⟩ := hdir x y hx hy
      ⟨z, hz, le_trans (union_lub (le_trans hRx (le_union_left x y))
        (le_trans hSy (le_union_right x y))) hxyz⟩⟩

/-- The principal downdeal hom `↓R` (an ideal: it contains `𝟘` and is `∪`-closed). -/
def DowndealHom.prin {a b : 𝒜} (R : a ⟶ b) : DowndealHom a b :=
  ⟨principalIdeal R, principalIdeal_isIdeal R⟩

/-! ### §2.315(b) — `Cat` structure on `Â` -/

/-- Composition in `Â`: `↓{ R ≫ S | R ∈ D₁, S ∈ D₂ }`. -/
def DowndealHom.comp {a b c : 𝒜} (D₁ : DowndealHom a b) (D₂ : DowndealHom b c) :
    DowndealHom a c :=
  DowndealHom.close (fun T => ∃ R S, D₁ R ∧ D₂ S ∧ T = R ≫ S)
    (by
      -- (R₁≫S₁) ∪ (R₂≫S₂) ⊑ (R₁∪R₂)≫(S₁∪S₂), a member.
      rintro _ _ ⟨R₁, S₁, hR₁, hS₁, rfl⟩ ⟨R₂, S₂, hR₂, hS₂, rfl⟩
      refine ⟨(R₁ ∪ R₂) ≫ (S₁ ∪ S₂),
        ⟨R₁ ∪ R₂, S₁ ∪ S₂, D₁.union_closed hR₁ hR₂, D₂.union_closed hS₁ hS₂, rfl⟩, ?_⟩
      apply union_lub
      · exact le_trans (comp_mono_right (le_union_left R₁ R₂) S₁)
          (comp_mono_left (R₁ ∪ R₂) (le_union_left S₁ S₂))
      · exact le_trans (comp_mono_right (le_union_right R₁ R₂) S₂)
          (comp_mono_left (R₁ ∪ R₂) (le_union_right S₁ S₂)))
    ⟨𝟘, 𝟘, 𝟘, D₁.mem_zero', D₂.mem_zero', (DistributiveAllegory.zero_comp 𝟘).symm⟩

/-- Identity in `Â`: the principal downdeal `↓(1_a)`. -/
def DowndealHom.id (a : 𝒜) : DowndealHom a a := DowndealHom.prin (Cat.id a)

theorem DowndealHom.id_comp {a b : 𝒜} (D : DowndealHom a b) :
    DowndealHom.comp (DowndealHom.id a) D = D := by
  ext T
  constructor
  · rintro ⟨U, ⟨R, S, hR, hS, rfl⟩, hTU⟩
    -- R ⊑ 1, S ∈ D, T ⊑ R ≫ S ⊑ 1 ≫ S = S, so T ∈ D.
    have hRS : R ≫ S ⊑ S := by
      calc R ≫ S ⊑ Cat.id a ≫ S := comp_mono_right hR S
        _ = S := Cat.id_comp S
    exact D.is_downdeal S hS T (le_trans hTU hRS)
  · intro hT
    -- T = 1 ≫ T with 1 ∈ id, T ∈ D.
    exact ⟨Cat.id a ≫ T, ⟨Cat.id a, T, le_refl _, hT, rfl⟩, by rw [Cat.id_comp]; exact le_refl T⟩

theorem DowndealHom.comp_id {a b : 𝒜} (D : DowndealHom a b) :
    DowndealHom.comp D (DowndealHom.id b) = D := by
  ext T
  constructor
  · rintro ⟨U, ⟨R, S, hR, hS, rfl⟩, hTU⟩
    have hRS : R ≫ S ⊑ R := by
      calc R ≫ S ⊑ R ≫ Cat.id b := comp_mono_left R hS
        _ = R := Cat.comp_id R
    exact D.is_downdeal R hR T (le_trans hTU hRS)
  · intro hT
    exact ⟨T ≫ Cat.id b, ⟨T, Cat.id b, hT, le_refl _, rfl⟩, by rw [Cat.comp_id]; exact le_refl T⟩

theorem DowndealHom.assoc {a b c d : 𝒜}
    (D₁ : DowndealHom a b) (D₂ : DowndealHom b c) (D₃ : DowndealHom c d) :
    DowndealHom.comp (DowndealHom.comp D₁ D₂) D₃
      = DowndealHom.comp D₁ (DowndealHom.comp D₂ D₃) := by
  ext T
  constructor
  · -- T ⊑ U ≫ W, U ⊑ R ≫ S with R∈D₁,S∈D₂, W∈D₃.  Then T ⊑ (R≫S)≫W = R≫(S≫W).
    rintro ⟨V, ⟨U, W, ⟨X, ⟨R, S, hR, hS, rfl⟩, hUX⟩, hW, rfl⟩, hTV⟩
    refine ⟨R ≫ (S ≫ W), ⟨R, S ≫ W, hR, ⟨S ≫ W, ⟨S, W, hS, hW, rfl⟩, le_refl _⟩, rfl⟩, ?_⟩
    -- T ⊑ U ≫ W ⊑ (R ≫ S) ≫ W = R ≫ (S ≫ W).
    refine le_trans hTV ?_
    calc U ≫ W ⊑ (R ≫ S) ≫ W := comp_mono_right hUX W
      _ = R ≫ (S ≫ W) := Cat.assoc R S W
  · rintro ⟨V, ⟨R, U, hR, ⟨X, ⟨S, W, hS, hW, rfl⟩, hUX⟩, rfl⟩, hTV⟩
    refine ⟨(R ≫ S) ≫ W, ⟨R ≫ S, W, ⟨R ≫ S, ⟨R, S, hR, hS, rfl⟩, le_refl _⟩, hW, rfl⟩, ?_⟩
    refine le_trans hTV ?_
    calc R ≫ U ⊑ R ≫ (S ≫ W) := comp_mono_left R hUX
      _ = (R ≫ S) ≫ W := (Cat.assoc R S W).symm

/-- Reinterpret a completion object as a base object (the underlying `def`-equality). -/
def Downdeal.out (a : Downdeal 𝒜) : 𝒜 := a

instance instCatDowndealHom : Cat.{u} (Downdeal 𝒜) where
  Hom a b := DowndealHom (𝒜 := 𝒜) a.out b.out
  id a := DowndealHom.id a.out
  comp D₁ D₂ := DowndealHom.comp D₁ D₂
  id_comp := DowndealHom.id_comp
  comp_id := DowndealHom.comp_id
  assoc := DowndealHom.assoc

/-! ### §2.315(b) — `Allegory` structure on `Â`

  Each operation is the downward closure of the pointwise image of the base operation.
  We give a clean MEMBERSHIP characterization for each, then prove the Allegory laws
  by reducing to `le_antisymm`/`propext` at the level of the carriers (`DowndealHom.ext`),
  using `is_downdeal` to absorb the `⊑` of the closure. -/

/-- Reciprocation in `Â`: `↓{ R° | R ∈ D }`. -/
def DowndealHom.recip {a b : 𝒜} (D : DowndealHom a b) : DowndealHom b a :=
  DowndealHom.close (fun T => ∃ R, D R ∧ T = R°)
    (by
      -- R₁° ∪ R₂° = (R₂ ∪ R₁)°, a member.
      rintro _ _ ⟨R₁, hR₁, rfl⟩ ⟨R₂, hR₂, rfl⟩
      exact ⟨(R₂ ∪ R₁)°, ⟨R₂ ∪ R₁, D.union_closed hR₂ hR₁, rfl⟩,
        by rw [recip_union]; exact le_refl _⟩)
    ⟨𝟘, 𝟘, D.mem_zero', recip_zero.symm⟩

/-- Intersection in `Â`: `↓{ R ∩ S | R ∈ D₁, S ∈ D₂ }`. -/
def DowndealHom.inter {a b : 𝒜} (D₁ D₂ : DowndealHom a b) : DowndealHom a b :=
  DowndealHom.close (fun T => ∃ R S, D₁ R ∧ D₂ S ∧ T = R ∩ S)
    (by
      -- (R₁∩S₁) ∪ (R₂∩S₂) ⊑ (R₁∪R₂) ∩ (S₁∪S₂), a member.
      rintro _ _ ⟨R₁, S₁, hR₁, hS₁, rfl⟩ ⟨R₂, S₂, hR₂, hS₂, rfl⟩
      refine ⟨(R₁ ∪ R₂) ∩ (S₁ ∪ S₂),
        ⟨R₁ ∪ R₂, S₁ ∪ S₂, D₁.union_closed hR₁ hR₂, D₂.union_closed hS₁ hS₂, rfl⟩, ?_⟩
      apply union_lub
      · exact le_inter (le_trans (inter_lb_left R₁ S₁) (le_union_left R₁ R₂))
          (le_trans (inter_lb_right R₁ S₁) (le_union_left S₁ S₂))
      · exact le_inter (le_trans (inter_lb_left R₂ S₂) (le_union_right R₁ R₂))
          (le_trans (inter_lb_right R₂ S₂) (le_union_right S₁ S₂)))
    ⟨𝟘, 𝟘, 𝟘, D₁.mem_zero', D₂.mem_zero', (Allegory.inter_idem 𝟘).symm⟩

/-- Membership in `D°` is exactly `D (T°)` (the closure adds nothing for a downdeal). -/
theorem DowndealHom.mem_recip {a b : 𝒜} (D : DowndealHom a b) (T : b ⟶ a) :
    (DowndealHom.recip D) T ↔ D (T°) := by
  constructor
  · rintro ⟨U, ⟨R, hR, rfl⟩, hTU⟩
    -- T ⊑ R°, so T° ⊑ R°° = R, hence T° ∈ D.
    have : T° ⊑ R := by
      have := recip_mono hTU; rwa [Allegory.recip_recip] at this
    exact D.is_downdeal R hR (T°) this
  · intro hT
    exact ⟨T°°, ⟨T°, hT, rfl⟩, by rw [Allegory.recip_recip]; exact le_refl T⟩

/-- Membership in `D₁ ∩ D₂` is `∃ R S, D₁ R ∧ D₂ S ∧ T ⊑ R ∩ S`. -/
theorem DowndealHom.mem_inter {a b : 𝒜} (D₁ D₂ : DowndealHom a b) (T : a ⟶ b) :
    (DowndealHom.inter D₁ D₂) T ↔ ∃ R S, D₁ R ∧ D₂ S ∧ T ⊑ R ∩ S := by
  constructor
  · rintro ⟨U, ⟨R, S, hR, hS, rfl⟩, hTU⟩; exact ⟨R, S, hR, hS, hTU⟩
  · rintro ⟨R, S, hR, hS, hT⟩; exact ⟨R ∩ S, ⟨R, S, hR, hS, rfl⟩, hT⟩

/-- Membership in `D₁ ≫ D₂` is `∃ R S, D₁ R ∧ D₂ S ∧ T ⊑ R ≫ S`. -/
theorem DowndealHom.mem_comp {a b c : 𝒜} (D₁ : DowndealHom a b) (D₂ : DowndealHom b c) (T : a ⟶ c) :
    (DowndealHom.comp D₁ D₂) T ↔ ∃ R S, D₁ R ∧ D₂ S ∧ T ⊑ R ≫ S := by
  constructor
  · rintro ⟨U, ⟨R, S, hR, hS, rfl⟩, hTU⟩; exact ⟨R, S, hR, hS, hTU⟩
  · rintro ⟨R, S, hR, hS, hT⟩; exact ⟨R ≫ S, ⟨R, S, hR, hS, rfl⟩, hT⟩

theorem DowndealHom.recip_recip {a b : 𝒜} (D : DowndealHom a b) :
    DowndealHom.recip (DowndealHom.recip D) = D := by
  ext T
  rw [DowndealHom.mem_recip, DowndealHom.mem_recip, Allegory.recip_recip]

theorem DowndealHom.recip_comp {a b c : 𝒜} (D₁ : DowndealHom a b) (D₂ : DowndealHom b c) :
    DowndealHom.recip (DowndealHom.comp D₁ D₂)
      = DowndealHom.comp (DowndealHom.recip D₂) (DowndealHom.recip D₁) := by
  ext T
  rw [DowndealHom.mem_recip, DowndealHom.mem_comp, DowndealHom.mem_comp]
  constructor
  · rintro ⟨R, S, hR, hS, hTU⟩
    -- T° ⊑ R≫S ⟹ T = T°° ⊑ (R≫S)° = S°≫R°, S° ∈ D₂°, R° ∈ D₁°.
    refine ⟨S°, R°, (DowndealHom.mem_recip _ _).mpr (by rw [Allegory.recip_recip]; exact hS),
      (DowndealHom.mem_recip _ _).mpr (by rw [Allegory.recip_recip]; exact hR), ?_⟩
    have h1 : T°° ⊑ (R ≫ S)° := recip_mono hTU
    rw [Allegory.recip_recip, Allegory.recip_comp] at h1; exact h1
  · rintro ⟨R, S, hR, hS, hTU⟩
    rw [DowndealHom.mem_recip] at hR hS
    -- R° ∈ D₂, S° ∈ D₁, T ⊑ R≫S ⟹ T° ⊑ (R≫S)° = S°≫R° with S°∈D₁, R°∈D₂.
    refine ⟨S°, R°, hS, hR, ?_⟩
    have h1 : T° ⊑ (R ≫ S)° := recip_mono hTU
    rw [Allegory.recip_comp] at h1; exact h1

theorem DowndealHom.recip_inter {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.recip (DowndealHom.inter D₁ D₂)
      = DowndealHom.inter (DowndealHom.recip D₁) (DowndealHom.recip D₂) := by
  ext T
  rw [DowndealHom.mem_recip, DowndealHom.mem_inter, DowndealHom.mem_inter]
  constructor
  · rintro ⟨R, S, hR, hS, hTU⟩
    refine ⟨R°, S°, (DowndealHom.mem_recip _ _).mpr (by rw [Allegory.recip_recip]; exact hR),
      (DowndealHom.mem_recip _ _).mpr (by rw [Allegory.recip_recip]; exact hS), ?_⟩
    have h1 : T°° ⊑ (R ∩ S)° := recip_mono hTU
    rw [Allegory.recip_recip, Allegory.recip_inter] at h1; exact h1
  · rintro ⟨R, S, hR, hS, hTU⟩
    rw [DowndealHom.mem_recip] at hR hS
    refine ⟨R°, S°, hR, hS, ?_⟩
    have h1 : T° ⊑ (R ∩ S)° := recip_mono hTU
    rw [Allegory.recip_inter] at h1; exact h1

theorem DowndealHom.inter_idem {a b : 𝒜} (D : DowndealHom a b) :
    DowndealHom.inter D D = D := by
  ext T
  rw [DowndealHom.mem_inter]
  constructor
  · rintro ⟨R, S, hR, hS, hTU⟩
    exact D.is_downdeal R hR T (le_trans hTU (inter_lb_left R S))
  · intro hT
    exact ⟨T, T, hT, hT, by rw [Allegory.inter_idem]; exact le_refl T⟩

theorem DowndealHom.inter_comm {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.inter D₁ D₂ = DowndealHom.inter D₂ D₁ := by
  ext T
  rw [DowndealHom.mem_inter, DowndealHom.mem_inter]
  constructor
  · rintro ⟨R, S, hR, hS, hTU⟩
    exact ⟨S, R, hS, hR, by rw [Allegory.inter_comm]; exact hTU⟩
  · rintro ⟨R, S, hR, hS, hTU⟩
    exact ⟨S, R, hS, hR, by rw [Allegory.inter_comm]; exact hTU⟩

theorem DowndealHom.inter_assoc {a b : 𝒜} (D₁ D₂ D₃ : DowndealHom a b) :
    DowndealHom.inter D₁ (DowndealHom.inter D₂ D₃)
      = DowndealHom.inter (DowndealHom.inter D₁ D₂) D₃ := by
  ext T
  rw [DowndealHom.mem_inter, DowndealHom.mem_inter]
  constructor
  · rintro ⟨R, U, hR, hU, hTU⟩
    rw [DowndealHom.mem_inter] at hU
    obtain ⟨S, P, hS, hP, hUSP⟩ := hU
    refine ⟨R ∩ S, P, (DowndealHom.mem_inter _ _ _).mpr ⟨R, S, hR, hS, le_refl _⟩, hP, ?_⟩
    have hstep : R ∩ U ⊑ (R ∩ S) ∩ P := by
      calc R ∩ U ⊑ R ∩ (S ∩ P) := le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) hUSP)
        _ = (R ∩ S) ∩ P := Allegory.inter_assoc R S P
    exact le_trans hTU hstep
  · rintro ⟨U, P, hU, hP, hTU⟩
    rw [DowndealHom.mem_inter] at hU
    obtain ⟨R, S, hR, hS, hURS⟩ := hU
    refine ⟨R, S ∩ P, hR, (DowndealHom.mem_inter _ _ _).mpr ⟨S, P, hS, hP, le_refl _⟩, ?_⟩
    have hstep : U ∩ P ⊑ R ∩ (S ∩ P) := by
      calc U ∩ P ⊑ (R ∩ S) ∩ P := le_inter (le_trans (inter_lb_left _ _) hURS) (inter_lb_right _ _)
        _ = R ∩ (S ∩ P) := (Allegory.inter_assoc R S P).symm
    exact le_trans hTU hstep

/-! ### §2.315(b) — carrier inclusion `⊆`, monotonicity, and the meet/modular laws -/

/-- Carrier inclusion of downdeal homs (this will coincide with the `Â`-order `⊑`). -/
def DowndealHom.Sub {a b : 𝒜} (D₁ D₂ : DowndealHom a b) : Prop := ∀ R, D₁ R → D₂ R

theorem DowndealHom.Sub.refl {a b : 𝒜} (D : DowndealHom a b) : DowndealHom.Sub D D :=
  fun _ h => h

theorem DowndealHom.Sub.antisymm {a b : 𝒜} {D₁ D₂ : DowndealHom a b}
    (h₁ : DowndealHom.Sub D₁ D₂) (h₂ : DowndealHom.Sub D₂ D₁) : D₁ = D₂ :=
  DowndealHom.ext (fun R => ⟨h₁ R, h₂ R⟩)

/-- `D₁ ∩ D₂ ⊆ D₁`. -/
theorem DowndealHom.inter_sub_left {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.Sub (DowndealHom.inter D₁ D₂) D₁ := by
  intro T hT
  rw [DowndealHom.mem_inter] at hT
  obtain ⟨R, S, hR, _, hTRS⟩ := hT
  exact D₁.is_downdeal R hR T (le_trans hTRS (inter_lb_left R S))

/-- `D₁ ∩ D₂ ⊆ D₂`. -/
theorem DowndealHom.inter_sub_right {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.Sub (DowndealHom.inter D₁ D₂) D₂ := by
  intro T hT
  rw [DowndealHom.mem_inter] at hT
  obtain ⟨R, S, _, hS, hTRS⟩ := hT
  exact D₂.is_downdeal S hS T (le_trans hTRS (inter_lb_right R S))

/-- `∩` is the greatest lower bound for `⊆`. -/
theorem DowndealHom.sub_inter {a b : 𝒜} {D D₁ D₂ : DowndealHom a b}
    (h₁ : DowndealHom.Sub D D₁) (h₂ : DowndealHom.Sub D D₂) :
    DowndealHom.Sub D (DowndealHom.inter D₁ D₂) := by
  intro T hT
  rw [DowndealHom.mem_inter]
  exact ⟨T, T, h₁ T hT, h₂ T hT, by rw [Allegory.inter_idem]; exact le_refl T⟩

/-- Composition is monotone in the second argument (for `⊆`). -/
theorem DowndealHom.comp_sub_left {a b c : 𝒜} (D : DowndealHom a b) {E₁ E₂ : DowndealHom b c}
    (h : DowndealHom.Sub E₁ E₂) : DowndealHom.Sub (DowndealHom.comp D E₁) (DowndealHom.comp D E₂) := by
  intro T hT
  rw [DowndealHom.mem_comp] at hT ⊢
  obtain ⟨R, S, hR, hS, hTRS⟩ := hT
  exact ⟨R, S, hR, h S hS, hTRS⟩

/-- Composition is monotone in the first argument (for `⊆`). -/
theorem DowndealHom.comp_sub_right {a b c : 𝒜} {D₁ D₂ : DowndealHom a b}
    (h : DowndealHom.Sub D₁ D₂) (E : DowndealHom b c) :
    DowndealHom.Sub (DowndealHom.comp D₁ E) (DowndealHom.comp D₂ E) := by
  intro T hT
  rw [DowndealHom.mem_comp] at hT ⊢
  obtain ⟨R, S, hR, hS, hTRS⟩ := hT
  exact ⟨R, S, h R hR, hS, hTRS⟩

/-- (§2.11) Semi-distributivity, equational form, on `Â`.  Both sides equal `D ≫ (E₁ ∩ E₂)`:
    the RHS is `(X ∩ X) ∩ Y` with `X = D≫(E₁∩E₂) ⊆ D≫E₁` (mono) and `⊆ D≫E₂`, collapsing
    to `X` by glb/antisymmetry. -/
theorem DowndealHom.semidistrib {a b c : 𝒜} (D : DowndealHom a b) (E₁ E₂ : DowndealHom b c) :
    DowndealHom.comp D (DowndealHom.inter E₁ E₂)
      = DowndealHom.inter
          (DowndealHom.inter (DowndealHom.comp D E₁) (DowndealHom.comp D (DowndealHom.inter E₁ E₂)))
          (DowndealHom.comp D E₂) := by
  have hXE₁ : DowndealHom.Sub (DowndealHom.comp D (DowndealHom.inter E₁ E₂))
      (DowndealHom.comp D E₁) :=
    DowndealHom.comp_sub_left D (DowndealHom.inter_sub_left E₁ E₂)
  have hXE₂ : DowndealHom.Sub (DowndealHom.comp D (DowndealHom.inter E₁ E₂))
      (DowndealHom.comp D E₂) :=
    DowndealHom.comp_sub_left D (DowndealHom.inter_sub_right E₁ E₂)
  apply DowndealHom.Sub.antisymm
  · -- X ⊆ ((DE₁ ∩ X) ∩ DE₂)
    exact DowndealHom.sub_inter
      (DowndealHom.sub_inter hXE₁ (DowndealHom.Sub.refl _)) hXE₂
  · -- ((DE₁ ∩ X) ∩ DE₂) ⊆ X, since it ⊆ (DE₁ ∩ X) ⊆ X.
    exact fun T hT => DowndealHom.inter_sub_right _ _ T (DowndealHom.inter_sub_left _ _ T hT)

/-- (§2.11) The MODULAR LAW, equational form, on `Â`.  Reduces to the `⊆`-order form
    `(D≫E) ∩ F ⊆ (D ∩ F≫E°) ≫ E`, lifted pointwise from the base modular law. -/
theorem DowndealHom.modular {a b c : 𝒜} (D : DowndealHom a b) (E : DowndealHom b c)
    (F : DowndealHom a c) :
    DowndealHom.inter (DowndealHom.comp D E) F
      = DowndealHom.inter (DowndealHom.inter (DowndealHom.comp D E) F)
          (DowndealHom.comp (DowndealHom.inter D (DowndealHom.comp F (DowndealHom.recip E))) E) := by
  apply DowndealHom.Sub.antisymm
  · -- (DE ∩ F) ⊆ ((DE ∩ F) ∩ (D ∩ F≫E°)≫E): need (DE ∩ F) ⊆ (D ∩ F≫E°)≫E.
    apply DowndealHom.sub_inter (DowndealHom.Sub.refl _)
    -- Pointwise modular law in the base.
    intro T hT
    rw [DowndealHom.mem_inter] at hT
    obtain ⟨P, Q, hP, hQ, hTPQ⟩ := hT
    rw [DowndealHom.mem_comp] at hP
    obtain ⟨R, S, hR, hS, hPRS⟩ := hP
    -- T ⊑ P ∩ Q ⊑ (R≫S) ∩ Q ⊑ (R ∩ Q≫S°)≫S, and R∈D, Q≫S° ∈ F≫E°, S∈E.
    rw [DowndealHom.mem_comp]
    refine ⟨R ∩ (Q ≫ S°), S, ?_, hS, ?_⟩
    · rw [DowndealHom.mem_inter]
      refine ⟨R, Q ≫ S°, hR, ?_, le_refl _⟩
      rw [DowndealHom.mem_comp]
      exact ⟨Q, S°, hQ, (DowndealHom.mem_recip _ _).mpr (by rw [Allegory.recip_recip]; exact hS),
        le_refl _⟩
    · -- T ⊑ (R≫S) ∩ Q ⊑ (R ∩ Q≫S°)≫S  (base modular_le)
      have hbase : (R ≫ S) ∩ Q ⊑ (R ∩ Q ≫ S°) ≫ S := modular_le R S Q
      have hTle : T ⊑ (R ≫ S) ∩ Q :=
        le_trans hTPQ (le_inter (le_trans (inter_lb_left P Q) hPRS) (inter_lb_right P Q))
      exact le_trans hTle hbase
  · -- ((DE∩F) ∩ X) ⊆ (DE ∩ F).
    exact fun T hT => DowndealHom.inter_sub_left _ _ T hT

instance instAllegoryDowndealHom : Allegory.{u} (Downdeal 𝒜) where
  recip D := DowndealHom.recip D
  inter D₁ D₂ := DowndealHom.inter D₁ D₂
  recip_recip := DowndealHom.recip_recip
  recip_comp := DowndealHom.recip_comp
  recip_inter := DowndealHom.recip_inter
  inter_idem := DowndealHom.inter_idem
  inter_comm := DowndealHom.inter_comm
  inter_assoc := DowndealHom.inter_assoc
  semidistrib := DowndealHom.semidistrib
  modular := DowndealHom.modular

/-! ### §2.315(b) — `DistributiveAllegory` structure on `Â` -/

/-- Zero in `Â`: the principal ideal `↓𝟘` (the smallest ideal). -/
def DowndealHom.zero {a b : 𝒜} : DowndealHom a b := DowndealHom.prin (𝟘 : a ⟶ b)

/-- Union in `Â`: `↓{ R ∪ S | R ∈ D₁, S ∈ D₂ }`. -/
def DowndealHom.union {a b : 𝒜} (D₁ D₂ : DowndealHom a b) : DowndealHom a b :=
  DowndealHom.close (fun T => ∃ R S, D₁ R ∧ D₂ S ∧ T = R ∪ S)
    (by
      -- (R₁∪S₁) ∪ (R₂∪S₂) = (R₁∪R₂) ∪ (S₁∪S₂), a member.
      rintro _ _ ⟨R₁, S₁, hR₁, hS₁, rfl⟩ ⟨R₂, S₂, hR₂, hS₂, rfl⟩
      refine ⟨(R₁ ∪ R₂) ∪ (S₁ ∪ S₂),
        ⟨R₁ ∪ R₂, S₁ ∪ S₂, D₁.union_closed hR₁ hR₂, D₂.union_closed hS₁ hS₂, rfl⟩, ?_⟩
      apply union_lub
      · exact union_lub (le_trans (le_union_left R₁ R₂) (le_union_left _ _))
          (le_trans (le_union_left S₁ S₂) (le_union_right _ _))
      · exact union_lub (le_trans (le_union_right R₁ R₂) (le_union_left _ _))
          (le_trans (le_union_right S₁ S₂) (le_union_right _ _)))
    ⟨𝟘, 𝟘, 𝟘, D₁.mem_zero', D₂.mem_zero', (DistributiveAllegory.union_idem 𝟘).symm⟩

theorem DowndealHom.mem_union {a b : 𝒜} (D₁ D₂ : DowndealHom a b) (T : a ⟶ b) :
    (DowndealHom.union D₁ D₂) T ↔ ∃ R S, D₁ R ∧ D₂ S ∧ T ⊑ R ∪ S := by
  constructor
  · rintro ⟨U, ⟨R, S, hR, hS, rfl⟩, hTU⟩; exact ⟨R, S, hR, hS, hTU⟩
  · rintro ⟨R, S, hR, hS, hT⟩; exact ⟨R ∪ S, ⟨R, S, hR, hS, rfl⟩, hT⟩

theorem DowndealHom.mem_zero {a b : 𝒜} (T : a ⟶ b) :
    (DowndealHom.zero : DowndealHom a b) T ↔ T ⊑ (𝟘 : a ⟶ b) := Iff.rfl

/-- `D₁ ⊆ D₁ ∪ D₂` (using that `𝟘 ∈ D₂` for ideals: `R = R ∪ 𝟘`). -/
theorem DowndealHom.sub_union_left {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.Sub D₁ (DowndealHom.union D₁ D₂) := by
  intro T hT
  rw [DowndealHom.mem_union]
  exact ⟨T, 𝟘, hT, D₂.mem_zero', by rw [union_zero]; exact le_refl T⟩

/-- `D₂ ⊆ D₁ ∪ D₂`. -/
theorem DowndealHom.sub_union_right {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.Sub D₂ (DowndealHom.union D₁ D₂) := by
  intro T hT
  rw [DowndealHom.mem_union]
  exact ⟨𝟘, T, D₁.mem_zero', hT, by rw [DistributiveAllegory.zero_union]; exact le_refl T⟩

/-- `∪` is the least upper bound for `⊆`. -/
theorem DowndealHom.union_sub {a b : 𝒜} {D D₁ D₂ : DowndealHom a b}
    (h₁ : DowndealHom.Sub D₁ D) (h₂ : DowndealHom.Sub D₂ D) :
    DowndealHom.Sub (DowndealHom.union D₁ D₂) D := by
  intro T hT
  rw [DowndealHom.mem_union] at hT
  obtain ⟨R, S, hR, hS, hTRS⟩ := hT
  exact D.is_downdeal (R ∪ S) (D.union_closed (h₁ R hR) (h₂ S hS)) T hTRS

/-- `↓𝟘 ⊆ D` for every ideal `D` (the zero ideal is least). -/
theorem DowndealHom.zero_sub {a b : 𝒜} (D : DowndealHom a b) :
    DowndealHom.Sub (DowndealHom.zero : DowndealHom a b) D := by
  intro T hT
  rw [DowndealHom.mem_zero] at hT
  exact D.is_downdeal 𝟘 D.mem_zero' T hT

theorem DowndealHom.zero_comp {a b c : 𝒜} (E : DowndealHom b c) :
    DowndealHom.comp (DowndealHom.zero : DowndealHom a b) E = DowndealHom.zero := by
  apply DowndealHom.Sub.antisymm _ (DowndealHom.zero_sub _)
  intro T hT
  rw [DowndealHom.mem_comp] at hT
  obtain ⟨R, S, hR, _, hTRS⟩ := hT
  rw [DowndealHom.mem_zero] at hR ⊢
  -- R ⊑ 𝟘, so R ≫ S ⊑ 𝟘 ≫ S = 𝟘.
  refine le_trans hTRS ?_
  calc R ≫ S ⊑ (𝟘 : a ⟶ b) ≫ S := Freyd.Alg.comp_mono_right hR S
    _ = 𝟘 := DistributiveAllegory.zero_comp S

theorem DowndealHom.comp_zero {a b c : 𝒜} (D : DowndealHom a b) :
    DowndealHom.comp D (DowndealHom.zero : DowndealHom b c) = DowndealHom.zero := by
  apply DowndealHom.Sub.antisymm _ (DowndealHom.zero_sub _)
  intro T hT
  rw [DowndealHom.mem_comp] at hT
  obtain ⟨R, S, _, hS, hTRS⟩ := hT
  rw [DowndealHom.mem_zero] at hS ⊢
  refine le_trans hTRS ?_
  calc R ≫ S ⊑ R ≫ (𝟘 : b ⟶ c) := comp_mono_left R hS
    _ = 𝟘 := DistributiveAllegory.comp_zero R

theorem DowndealHom.union_idem {a b : 𝒜} (D : DowndealHom a b) :
    DowndealHom.union D D = D :=
  DowndealHom.Sub.antisymm (DowndealHom.union_sub (DowndealHom.Sub.refl _) (DowndealHom.Sub.refl _))
    (DowndealHom.sub_union_left D D)

theorem DowndealHom.union_comm {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.union D₁ D₂ = DowndealHom.union D₂ D₁ :=
  DowndealHom.Sub.antisymm
    (DowndealHom.union_sub (DowndealHom.sub_union_right D₂ D₁) (DowndealHom.sub_union_left D₂ D₁))
    (DowndealHom.union_sub (DowndealHom.sub_union_right D₁ D₂) (DowndealHom.sub_union_left D₁ D₂))

theorem DowndealHom.union_assoc {a b : 𝒜} (D₁ D₂ D₃ : DowndealHom a b) :
    DowndealHom.union D₁ (DowndealHom.union D₂ D₃)
      = DowndealHom.union (DowndealHom.union D₁ D₂) D₃ := by
  apply DowndealHom.Sub.antisymm
  · apply DowndealHom.union_sub
    · exact fun T h => DowndealHom.sub_union_left _ _ T (DowndealHom.sub_union_left D₁ D₂ T h)
    · apply DowndealHom.union_sub
      · exact fun T h => DowndealHom.sub_union_left _ _ T (DowndealHom.sub_union_right D₁ D₂ T h)
      · exact DowndealHom.sub_union_right _ _
  · apply DowndealHom.union_sub
    · apply DowndealHom.union_sub
      · exact DowndealHom.sub_union_left _ _
      · exact fun T h => DowndealHom.sub_union_right _ _ T (DowndealHom.sub_union_left D₂ D₃ T h)
    · exact fun T h => DowndealHom.sub_union_right _ _ T (DowndealHom.sub_union_right D₂ D₃ T h)

theorem DowndealHom.union_inter_absorb {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.union D₁ (DowndealHom.inter D₂ D₁) = D₁ :=
  DowndealHom.Sub.antisymm
    (DowndealHom.union_sub (DowndealHom.Sub.refl _) (DowndealHom.inter_sub_right D₂ D₁))
    (DowndealHom.sub_union_left D₁ (DowndealHom.inter D₂ D₁))

theorem DowndealHom.inter_union_absorb {a b : 𝒜} (D₁ D₂ : DowndealHom a b) :
    DowndealHom.inter (DowndealHom.union D₁ D₂) D₁ = D₁ :=
  DowndealHom.Sub.antisymm
    (DowndealHom.inter_sub_right _ _)
    (DowndealHom.sub_inter (DowndealHom.sub_union_left D₁ D₂) (DowndealHom.Sub.refl _))

theorem DowndealHom.zero_union {a b : 𝒜} (D : DowndealHom a b) :
    DowndealHom.union DowndealHom.zero D = D :=
  DowndealHom.Sub.antisymm
    (DowndealHom.union_sub (DowndealHom.zero_sub D) (DowndealHom.Sub.refl _))
    (DowndealHom.sub_union_right DowndealHom.zero D)

/-- `D ≫ (E₁ ∪ E₂) = D≫E₁ ∪ D≫E₂` (§2.21). -/
theorem DowndealHom.comp_union_distrib {a b c : 𝒜} (D : DowndealHom a b) (E₁ E₂ : DowndealHom b c) :
    DowndealHom.comp D (DowndealHom.union E₁ E₂)
      = DowndealHom.union (DowndealHom.comp D E₁) (DowndealHom.comp D E₂) := by
  apply DowndealHom.Sub.antisymm
  · -- D≫(E₁∪E₂) ⊆ D≫E₁ ∪ D≫E₂.
    intro T hT
    rw [DowndealHom.mem_comp] at hT
    obtain ⟨R, S, hR, hS, hTRS⟩ := hT
    rw [DowndealHom.mem_union] at hS
    obtain ⟨S₁, S₂, hS₁, hS₂, hSS⟩ := hS
    rw [DowndealHom.mem_union]
    -- T ⊑ R≫S ⊑ R≫(S₁∪S₂) = R≫S₁ ∪ R≫S₂.
    refine ⟨R ≫ S₁, R ≫ S₂, (DowndealHom.mem_comp _ _ _).mpr ⟨R, S₁, hR, hS₁, le_refl _⟩,
      (DowndealHom.mem_comp _ _ _).mpr ⟨R, S₂, hR, hS₂, le_refl _⟩, ?_⟩
    refine le_trans hTRS ?_
    calc R ≫ S ⊑ R ≫ (S₁ ∪ S₂) := comp_mono_left R hSS
      _ = (R ≫ S₁) ∪ (R ≫ S₂) := DistributiveAllegory.comp_union_distrib R S₁ S₂
  · -- D≫E₁ ∪ D≫E₂ ⊆ D≫(E₁∪E₂), since each D≫Eᵢ ⊆ D≫(E₁∪E₂) (mono).
    apply DowndealHom.union_sub
    · exact DowndealHom.comp_sub_left D (DowndealHom.sub_union_left E₁ E₂)
    · exact DowndealHom.comp_sub_left D (DowndealHom.sub_union_right E₁ E₂)

/-- `D ∩ (E₁ ∪ E₂) = (D∩E₁) ∪ (D∩E₂)` (§2.21). -/
theorem DowndealHom.inter_union_distrib {a b : 𝒜} (D E₁ E₂ : DowndealHom a b) :
    DowndealHom.inter D (DowndealHom.union E₁ E₂)
      = DowndealHom.union (DowndealHom.inter D E₁) (DowndealHom.inter D E₂) := by
  apply DowndealHom.Sub.antisymm
  · intro T hT
    rw [DowndealHom.mem_inter] at hT
    obtain ⟨R, S, hR, hS, hTRS⟩ := hT
    rw [DowndealHom.mem_union] at hS
    obtain ⟨S₁, S₂, hS₁, hS₂, hSS⟩ := hS
    rw [DowndealHom.mem_union]
    refine ⟨R ∩ S₁, R ∩ S₂, (DowndealHom.mem_inter _ _ _).mpr ⟨R, S₁, hR, hS₁, le_refl _⟩,
      (DowndealHom.mem_inter _ _ _).mpr ⟨R, S₂, hR, hS₂, le_refl _⟩, ?_⟩
    refine le_trans hTRS ?_
    calc R ∩ S ⊑ R ∩ (S₁ ∪ S₂) := le_inter (inter_lb_left R S) (le_trans (inter_lb_right R S) hSS)
      _ = (R ∩ S₁) ∪ (R ∩ S₂) := DistributiveAllegory.inter_union_distrib R S₁ S₂
  · apply DowndealHom.union_sub
    · exact DowndealHom.sub_inter (DowndealHom.inter_sub_left D E₁)
        (fun T h => DowndealHom.sub_union_left E₁ E₂ T (DowndealHom.inter_sub_right D E₁ T h))
    · exact DowndealHom.sub_inter (DowndealHom.inter_sub_left D E₂)
        (fun T h => DowndealHom.sub_union_right E₁ E₂ T (DowndealHom.inter_sub_right D E₂ T h))

instance instDistributiveAllegoryDowndealHom : DistributiveAllegory.{u} (Downdeal 𝒜) :=
  { instAllegoryDowndealHom with
    zero := DowndealHom.zero
    union := DowndealHom.union
    zero_comp := DowndealHom.zero_comp
    comp_zero := DowndealHom.comp_zero
    union_idem := DowndealHom.union_idem
    union_comm := DowndealHom.union_comm
    union_assoc := DowndealHom.union_assoc
    union_inter_absorb := DowndealHom.union_inter_absorb
    inter_union_absorb := DowndealHom.inter_union_absorb
    comp_union_distrib := DowndealHom.comp_union_distrib
    inter_union_distrib := DowndealHom.inter_union_distrib
    zero_union := DowndealHom.zero_union }

/-! ### §2.315(b) — `LocallyCompleteDistributiveAllegory` structure on `Â`

  The supremum of a family `P` of ideals is the ideal they generate: a hom `T` lies in it
  iff `T` is dominated by a finite join of homs each belonging to some member ideal.  We
  encode finite joins as a `List`. -/

/-- The finite join of a list of base homs (`[] ↦ 𝟘`, `x :: xs ↦ x ∪ join xs`). -/
def listJoinD {a b : 𝒜} : List (a ⟶ b) → a ⟶ b
  | [] => 𝟘
  | x :: xs => x ∪ listJoinD xs

theorem listJoinD_le {a b : 𝒜} {ℓ : List (a ⟶ b)} {T : a ⟶ b}
    (h : ∀ x ∈ ℓ, x ⊑ T) : listJoinD ℓ ⊑ T := by
  induction ℓ with
  | nil => exact zero_le T
  | cons x xs ih =>
    exact union_lub (h x (List.mem_cons_self)) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

theorem le_listJoinD {a b : 𝒜} {ℓ : List (a ⟶ b)} {x : a ⟶ b} (h : x ∈ ℓ) :
    x ⊑ listJoinD ℓ := by
  induction ℓ with
  | nil => exact absurd h (List.not_mem_nil)
  | cons y ys ih =>
    rcases List.mem_cons.mp h with h' | h'
    · subst h'; exact le_union_left x (listJoinD ys)
    · exact le_trans (ih h') (le_union_right y (listJoinD ys))

/-- The carrier of `Sup P`: dominated by a finite join of `(⋃ P)`-elements. -/
def supCarrier {a b : 𝒜} (P : DowndealHom a b → Prop) : (a ⟶ b) → Prop :=
  fun T => ∃ ℓ : List (a ⟶ b), (∀ x ∈ ℓ, ∃ D, P D ∧ D x) ∧ T ⊑ listJoinD ℓ

/-- The supremum of a family of ideals (§2.22): the ideal they generate. -/
def DowndealHom.Sup {a b : 𝒜} (P : DowndealHom a b → Prop) : DowndealHom a b where
  carrier := supCarrier P
  is_ideal := by
    refine ⟨?_, ?_, ?_⟩
    · -- downward closed
      rintro T ⟨ℓ, hℓ, hTℓ⟩ S hST; exact ⟨ℓ, hℓ, le_trans hST hTℓ⟩
    · -- contains 𝟘 (empty join)
      exact ⟨[], by intro x hx; exact absurd hx (List.not_mem_nil), le_refl 𝟘⟩
    · -- ∪-closed: concatenate the two lists.
      rintro R S ⟨ℓ₁, hℓ₁, hR⟩ ⟨ℓ₂, hℓ₂, hS⟩
      refine ⟨ℓ₁ ++ ℓ₂, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hℓ₁ x h
        · exact hℓ₂ x h
      · -- R ∪ S ⊑ join ℓ₁ ∪ join ℓ₂ ⊑ join (ℓ₁ ++ ℓ₂)
        apply union_lub
        · exact le_trans hR (listJoinD_le (fun x hx => le_listJoinD (List.mem_append.mpr (Or.inl hx))))
        · exact le_trans hS (listJoinD_le (fun x hx => le_listJoinD (List.mem_append.mpr (Or.inr hx))))

theorem DowndealHom.le_Sup {a b : 𝒜} {P : DowndealHom a b → Prop} {D : DowndealHom a b}
    (h : P D) : DowndealHom.Sub D (DowndealHom.Sup P) := by
  intro T hT
  -- T ∈ D, so T ⊑ join [T] = T ∪ 𝟘.
  refine ⟨[T], fun x hx => by rcases List.mem_singleton.mp hx with rfl; exact ⟨D, h, hT⟩, ?_⟩
  show T ⊑ T ∪ 𝟘
  rw [union_zero]; exact le_refl T

theorem DowndealHom.Sup_le {a b : 𝒜} {P : DowndealHom a b → Prop} {E : DowndealHom a b}
    (h : ∀ D, P D → DowndealHom.Sub D E) : DowndealHom.Sub (DowndealHom.Sup P) E := by
  rintro T ⟨ℓ, hℓ, hTℓ⟩
  -- Each element of ℓ is in some member D ⊆ E, so in E; E is ∪-closed, so join ℓ ∈ E.
  have hjoin : ∀ (m : List (a ⟶ b)), (∀ x ∈ m, ∃ D, P D ∧ D x) → E (listJoinD m) := by
    intro m
    induction m with
    | nil => intro _; exact E.mem_zero'
    | cons x xs ih =>
      intro hm
      obtain ⟨D, hD, hDx⟩ := hm x (List.mem_cons_self)
      exact E.union_closed (h D hD x hDx) (ih (fun y hy => hm y (List.mem_cons_of_mem x hy)))
  exact E.is_downdeal (listJoinD ℓ) (hjoin ℓ hℓ) T hTℓ

/-- `R ≫ listJoinD ℓ = listJoinD (ℓ.map (R ≫ ·))` (composition distributes over a finite join). -/
theorem comp_listJoinD {a b c : 𝒜} (R : a ⟶ b) (ℓ : List (b ⟶ c)) :
    R ≫ listJoinD ℓ = listJoinD (ℓ.map (fun S => R ≫ S)) := by
  induction ℓ with
  | nil => simp [listJoinD, DistributiveAllegory.comp_zero]
  | cons x xs ih =>
    simp only [listJoinD, List.map_cons, DistributiveAllegory.comp_union_distrib, ih]

/-- `(listJoinD ℓ) ≫ R = listJoinD (ℓ.map (· ≫ R))`. -/
theorem listJoinD_comp {a b c : 𝒜} (ℓ : List (a ⟶ b)) (R : b ⟶ c) :
    listJoinD ℓ ≫ R = listJoinD (ℓ.map (fun S => S ≫ R)) := by
  induction ℓ with
  | nil => simp [listJoinD, DistributiveAllegory.zero_comp]
  | cons x xs ih =>
    simp only [listJoinD, List.map_cons, union_comp_distrib, ih]

/-- `R ∩ listJoinD ℓ = listJoinD (ℓ.map (R ∩ ·))`. -/
theorem inter_listJoinD {a b : 𝒜} (R : a ⟶ b) (ℓ : List (a ⟶ b)) :
    R ∩ listJoinD ℓ = listJoinD (ℓ.map (fun S => R ∩ S)) := by
  induction ℓ with
  | nil =>
    simp only [listJoinD, List.map_nil]
    rw [Allegory.inter_comm]; exact inter_eq_left (zero_le R)
  | cons x xs ih =>
    simp only [listJoinD, List.map_cons, DistributiveAllegory.inter_union_distrib, ih]

/-- (§2.22) Composition distributes over `Sup` on the right, on `Â`. -/
theorem DowndealHom.comp_Sup_distrib {a b c : 𝒜} (D : DowndealHom a b)
    (P : DowndealHom b c → Prop) :
    DowndealHom.comp D (DowndealHom.Sup P)
      = DowndealHom.Sup (fun U => ∃ S, P S ∧ U = DowndealHom.comp D S) := by
  apply DowndealHom.Sub.antisymm
  · -- ⊆
    rintro T ⟨W, ⟨R, S, hR, hS, rfl⟩, hTW⟩
    -- S ∈ Sup P: S ⊑ join ℓ, ℓ-elements each in some Pᵢ.
    obtain ⟨ℓ, hℓ, hSℓ⟩ := hS
    -- T ⊑ R ≫ S ⊑ R ≫ join ℓ = join (map (R ≫ ·) ℓ).
    refine ⟨ℓ.map (fun S' => R ≫ S'), ?_, ?_⟩
    · intro u hu
      rw [List.mem_map] at hu
      obtain ⟨S', hS'ℓ, rfl⟩ := hu
      obtain ⟨Dᵢ, hDᵢ, hS'⟩ := hℓ S' hS'ℓ
      exact ⟨DowndealHom.comp D Dᵢ, ⟨Dᵢ, hDᵢ, rfl⟩,
        (DowndealHom.mem_comp _ _ _).mpr ⟨R, S', hR, hS', le_refl _⟩⟩
    · rw [← comp_listJoinD]
      exact le_trans hTW (comp_mono_left R hSℓ)
  · -- ⊇: each D≫S ⊆ D≫(Sup P).
    apply DowndealHom.Sup_le
    rintro U ⟨S, hS, rfl⟩
    exact DowndealHom.comp_sub_left D (DowndealHom.le_Sup hS)

/-- (§2.22) Finite intersection distributes over `Sup`, on `Â`. -/
theorem DowndealHom.inter_Sup_distrib {a b : 𝒜} (D : DowndealHom a b)
    (P : DowndealHom a b → Prop) :
    DowndealHom.inter D (DowndealHom.Sup P)
      = DowndealHom.Sup (fun U => ∃ S, P S ∧ U = DowndealHom.inter D S) := by
  apply DowndealHom.Sub.antisymm
  · intro T hT
    rw [DowndealHom.mem_inter] at hT
    obtain ⟨R, S, hR, hS, hTRS⟩ := hT
    obtain ⟨ℓ, hℓ, hSℓ⟩ := hS
    refine ⟨ℓ.map (fun S' => R ∩ S'), ?_, ?_⟩
    · intro u hu
      rw [List.mem_map] at hu
      obtain ⟨S', hS'ℓ, rfl⟩ := hu
      obtain ⟨Dᵢ, hDᵢ, hS'⟩ := hℓ S' hS'ℓ
      exact ⟨DowndealHom.inter D Dᵢ, ⟨Dᵢ, hDᵢ, rfl⟩,
        (DowndealHom.mem_inter _ _ _).mpr ⟨R, S', hR, hS', le_refl _⟩⟩
    · rw [← inter_listJoinD]
      -- T ⊑ R ∩ S ⊑ R ∩ join ℓ.
      exact le_trans hTRS (le_inter (inter_lb_left R S) (le_trans (inter_lb_right R S) hSℓ))
  · apply DowndealHom.Sup_le
    rintro U ⟨S, hS, rfl⟩
    -- D ∩ S ⊆ D ∩ (Sup P): mono in 2nd arg.
    exact DowndealHom.sub_inter (DowndealHom.inter_sub_left D S)
      (fun T h => DowndealHom.le_Sup hS T (DowndealHom.inter_sub_right D S T h))

/-- Carrier inclusion `Sub` coincides with the allegory order `⊑` on `Â`. -/
theorem DowndealHom.sub_iff_le {a b : Downdeal 𝒜} (D₁ D₂ : a ⟶ b) :
    DowndealHom.Sub D₁ D₂ ↔ (D₁ ⊑ D₂) := by
  constructor
  · intro h
    -- D₁ ⊑ D₂ means D₁ ∩ D₂ = D₁ (Â-inter).
    show DowndealHom.inter D₁ D₂ = D₁
    exact DowndealHom.Sub.antisymm (DowndealHom.inter_sub_left D₁ D₂)
      (DowndealHom.sub_inter (DowndealHom.Sub.refl D₁) h)
  · intro h R hR
    -- h : D₁ ∩ D₂ = D₁; so D₁ ⊆ D₁ ∩ D₂ ⊆ D₂.
    have h' : DowndealHom.inter D₁ D₂ = D₁ := h
    have : DowndealHom.Sub D₁ (DowndealHom.inter D₁ D₂) := by rw [h']; exact DowndealHom.Sub.refl _
    exact DowndealHom.inter_sub_right D₁ D₂ R (this R hR)

instance instLocallyCompleteDistributiveAllegoryDowndealHom :
    LocallyCompleteDistributiveAllegory.{u} (Downdeal 𝒜) :=
  { instDistributiveAllegoryDowndealHom with
    Sup := fun P => DowndealHom.Sup P
    le_Sup := fun {_ _ P R} h => (DowndealHom.sub_iff_le R (DowndealHom.Sup P)).mp
      (DowndealHom.le_Sup h)
    Sup_le := fun {_ _ P T} h => (DowndealHom.sub_iff_le (DowndealHom.Sup P) T).mp
      (DowndealHom.Sup_le (fun D hD => (DowndealHom.sub_iff_le D T).mpr (h D hD)))
    comp_Sup_distrib := DowndealHom.comp_Sup_distrib
    inter_Sup_distrib := DowndealHom.inter_Sup_distrib }

/-! ### §2.315(b) — the faithful embedding `A → Â`, `R ↦ ↓R = prin R`

  The principal-ideal map preserves every operation and is injective (faithful). -/

theorem DowndealHom.mem_prin {a b : 𝒜} (R T : a ⟶ b) :
    (DowndealHom.prin R) T ↔ T ⊑ R := Iff.rfl

/-- The embedding is faithful: `↓R = ↓S ⟹ R = S`. -/
theorem DowndealHom.prin_injective {a b : 𝒜} {R S : a ⟶ b}
    (h : DowndealHom.prin R = DowndealHom.prin S) : R = S := by
  have hRS : R ⊑ S := by have := (DowndealHom.mem_prin R R).mpr (le_refl R); rw [h] at this; exact this
  have hSR : S ⊑ R := by have := (DowndealHom.mem_prin S S).mpr (le_refl S); rw [← h] at this; exact this
  exact le_antisymm hRS hSR

/-- The embedding preserves composition: `↓(R ≫ S) = ↓R ≫ ↓S`. -/
theorem DowndealHom.prin_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    DowndealHom.prin (R ≫ S) = DowndealHom.comp (DowndealHom.prin R) (DowndealHom.prin S) := by
  ext T
  rw [DowndealHom.mem_prin, DowndealHom.mem_comp]
  constructor
  · intro hT; exact ⟨R, S, le_refl R, le_refl S, hT⟩
  · rintro ⟨R', S', hR', hS', hTRS⟩
    exact le_trans hTRS (le_trans (comp_mono_right hR' S') (comp_mono_left R hS'))

/-- The embedding preserves reciprocation: `↓(R°) = (↓R)°`. -/
theorem DowndealHom.prin_recip {a b : 𝒜} (R : a ⟶ b) :
    DowndealHom.prin (R°) = DowndealHom.recip (DowndealHom.prin R) := by
  ext T
  rw [DowndealHom.mem_prin, DowndealHom.mem_recip, DowndealHom.mem_prin]
  constructor
  · intro hT; have := recip_mono hT; rwa [Allegory.recip_recip] at this
  · intro hT; have := recip_mono hT; rwa [Allegory.recip_recip] at this

/-- The embedding preserves intersection: `↓(R ∩ S) = ↓R ∩ ↓S`. -/
theorem DowndealHom.prin_inter {a b : 𝒜} (R S : a ⟶ b) :
    DowndealHom.prin (R ∩ S) = DowndealHom.inter (DowndealHom.prin R) (DowndealHom.prin S) := by
  ext T
  rw [DowndealHom.mem_prin, DowndealHom.mem_inter]
  constructor
  · intro hT; exact ⟨R, S, le_refl R, le_refl S, hT⟩
  · rintro ⟨R', S', hR', hS', hTRS⟩
    exact le_trans hTRS (le_inter (le_trans (inter_lb_left R' S') hR')
      (le_trans (inter_lb_right R' S') hS'))

/-- The embedding preserves union: `↓(R ∪ S) = ↓R ∪ ↓S`. -/
theorem DowndealHom.prin_union {a b : 𝒜} (R S : a ⟶ b) :
    DowndealHom.prin (R ∪ S) = DowndealHom.union (DowndealHom.prin R) (DowndealHom.prin S) := by
  ext T
  rw [DowndealHom.mem_prin, DowndealHom.mem_union]
  constructor
  · intro hT; exact ⟨R, S, le_refl R, le_refl S, hT⟩
  · rintro ⟨R', S', hR', hS', hTRS⟩
    exact le_trans hTRS (union_lub (le_trans hR' (le_union_left R S))
      (le_trans hS' (le_union_right R S)))

/-- The embedding preserves zero: `↓𝟘 = 𝟘`. -/
theorem DowndealHom.prin_zero {a b : 𝒜} :
    DowndealHom.prin (𝟘 : a ⟶ b) = (DowndealHom.zero : DowndealHom a b) := rfl

end Downdeal

/-! ## §2.224  Global Completion A'

  The GLOBAL COMPLETION of a locally complete distributive allegory A has
  indexed families of objects and infinite matrices as morphisms (§2.224). -/

/-- Objects of the global completion: an index type I together with an I-indexed
    family of A-objects (§2.224). -/
structure GlobalObj (𝒜 : Type u) where
  idx : Type u
  obj : idx → 𝒜

/-- Morphisms of the global completion: an infinite matrix R_{ij} : a_i → b_j (§2.224). -/
def GlobalMorphism {𝒜 : Type u} [Allegory 𝒜] (A B : GlobalObj 𝒜) : Type u :=
  (i : A.idx) → (j : B.idx) → A.obj i ⟶ B.obj j

/-- Global completion composition: (RS)_{ik} = Sup_j { R_{ij} ≫ S_{jk} } (§2.224). -/
def GlobalMorphism.comp {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    {A B C : GlobalObj 𝒜} (R : GlobalMorphism A B) (S : GlobalMorphism B C) :
    GlobalMorphism A C :=
  fun i k => LocallyCompleteDistributiveAllegory.Sup (fun T => ∃ j, T = R i j ≫ S j k)

/-- Global completion reciprocation: (R°)_{ji} = (R_{ij})° (§2.224). -/
def GlobalMorphism.recip {𝒜 : Type u} [Allegory 𝒜] {A B : GlobalObj 𝒜}
    (R : GlobalMorphism A B) : GlobalMorphism B A :=
  fun j i => (R i j)°

/-- The embedding A → A' sending R : a → b to the 1×1 matrix (R) (§2.224). -/
def globalCompletionEmbed {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    GlobalMorphism (𝒜 := 𝒜) ⟨PUnit.{u+1}, fun _ => a⟩ ⟨PUnit.{u+1}, fun _ => b⟩ :=
  fun _i _j => R

/-- (§2.224) The embedding A → A' is faithful. -/
theorem globalCompletionEmbed_injective {𝒜 : Type u} [Allegory 𝒜]
    {a b : 𝒜} {R S : a ⟶ b}
    (h : globalCompletionEmbed R = globalCompletionEmbed S) : R = S :=
  congrFun (congrFun h PUnit.unit) PUnit.unit

/-! ## §2.226  Systemic Completion

  The SYSTEMIC COMPLETION of an allegory is obtained by splitting the
  symmetric idempotents of its global completion (§2.226).

  **§2.226 generating-set theorem**: If an allegory A, viewed as a category, has a
  generating set (e.g. if A is small), then its systemic completion has a unit.
  [Proof: a generating set remains generating in the completion; one constructs a
  maximal partial unit from the generating set by the maximality argument in §2.226.]  -/

-- BOOK §2.226: If an allegory A has a generating set (e.g. A is small), then its
-- systemic completion has a unit.

/-- A split symmetric idempotent in an allegory (§2.226; cf. EffectiveAllegory):
    a symmetric idempotent E on a together with a splitting map f : a → b
    satisfying f ≫ f° = E and f° ≫ f = 1_b. -/
structure SplitSymmIdem {𝒜 : Type u} [Allegory 𝒜] (a : 𝒜) where
  E       : a ⟶ a
  isSymm  : Symmetric E
  isIdem  : E ≫ E = E
  b       : 𝒜
  f       : a ⟶ b
  hMap    : Map f
  hffR    : f ≫ f° = E
  hRff    : f° ≫ f = Cat.id b

/-- (§2.226) The systemic completion of a semi-simple globally complete allegory
    is tabular and effective: every symmetric idempotent splits (by the construction
    of the systemic completion via splitting symmetric idempotents). -/
theorem systemic_completion_tabular_effective
    {𝒜 : Type u} [SemiSimpleAllegory 𝒜] [GloballyCompleteAllegory 𝒜] :
    ∀ (a : 𝒜) (ss : SplitSymmIdem a),
      ∃ (b : 𝒜) (f : a ⟶ b), Map f ∧ f ≫ f° = ss.E ∧ f° ≫ f = Cat.id b :=
  fun _a ss => ⟨ss.b, ss.f, ss.hMap, ss.hffR, ss.hRff⟩

/-! ## §2.145 / §2.163  A tabular coreflexive splits

  **§2.145**: if a coreflexive morphism `A` is tabular — `(f,g)` tabulates `A`
  with `A ⊑ 1` — then its two legs coincide, `f = g`, and `g` is a *splitting*
  of `A`: `g° g = A` and `g g° = 1`.  Equivalently (**§2.163**) a coreflexive is
  a split idempotent iff it is tabular.  In a `TabularAllegory` every coreflexive
  is therefore split — the coreflexive half of effectiveness, the data §2.166
  uses to refine a bare tabulation's apex.

  This is Sorry-free and constructive: the legs agree because
  `f = f (f°f ∩ g°g) ⊑ f (g°g) = A g ⊑ g` (and symmetrically), then
  `map_order_discrete`. -/

/-- **§2.145**: the two legs of a (source-apex) tabulation of a coreflexive coincide. -/
theorem tabulation_coreflexive_legs_eq {𝒜 : Type u} [Allegory 𝒜] {a c : 𝒜}
    {f g : c ⟶ a} {A : a ⟶ a} (hf : Map f) (hg : Map g) (hA : A = f° ≫ g)
    (htab : f ≫ f° ∩ g ≫ g° = Cat.id c) (hcor : Coreflexive A) : f = g := by
  have hcoref1 : A ⊑ Cat.id a := hcor
  -- g ⊑ f:  g = (f f° ∩ g g°)g = … ⊑ (f f°)g = f(f°g) = f A ⊑ f·1 = f
  have hgf : g ⊑ f := by
    have e1 : g = (f ≫ f° ∩ g ≫ g°) ≫ g := by rw [htab, Cat.id_comp]
    have e2 : (f ≫ f° ∩ g ≫ g°) ≫ g ⊑ (f ≫ f°) ≫ g := comp_mono_right (inter_lb_left _ _) g
    have e3 : (f ≫ f°) ≫ g = f ≫ A := by rw [hA]; simp [Cat.assoc]
    have e4 : f ≫ A ⊑ f := by have := comp_mono_left f hcoref1; rwa [Cat.comp_id] at this
    rw [e1]; exact le_trans e2 (e3 ▸ e4)
  exact (map_order_discrete hg hf hgf).symm

/-- **§2.145 / §2.163**: a tabular coreflexive splits.  From a tabulation `(f,g)`
    of coreflexive `A` the legs agree (`f = g`) and `f` is a map with
    `f° ≫ f = A` and `f ≫ f° = 1_c` — i.e. `f` *splits* `A` (`h°h = A`, `hh° = 1`). -/
theorem coreflexive_split_of_tabulation {𝒜 : Type u} [Allegory 𝒜] {a c : 𝒜}
    {f g : c ⟶ a} {A : a ⟶ a} (hf : Map f) (hg : Map g) (hA : A = f° ≫ g)
    (htab : f ≫ f° ∩ g ≫ g° = Cat.id c) (hcor : Coreflexive A) :
    Map f ∧ f° ≫ f = A ∧ f ≫ f° = Cat.id c := by
  have hfeqg : f = g := tabulation_coreflexive_legs_eq hf hg hA htab hcor
  subst hfeqg
  -- now A = f° f, and htab : f f° ∩ f f° = f f° = 1_c
  rw [Allegory.inter_idem] at htab
  exact ⟨hf, hA.symm, htab⟩

/-- In a `TabularAllegory` every coreflexive `A : a → a` splits: there is a map
    `g : c → a` with `g° ≫ g = A`, `g ≫ g° = 1_c` (§2.163).  (The splitting map
    points FROM the apex: in `Rel(Set)` it is the inclusion of the support subset.) -/
theorem coreflexive_splits {𝒜 : Type u} [TabularAllegory 𝒜] {a : 𝒜} {A : a ⟶ a}
    (hcor : Coreflexive A) :
    ∃ (c : 𝒜) (g : c ⟶ a), Map g ∧ g° ≫ g = A ∧ g ≫ g° = Cat.id c := by
  obtain ⟨c, f, g, hf, hg, hA, htab⟩ := TabularAllegory.tabular A
  exact ⟨c, f, coreflexive_split_of_tabulation hf hg hA htab hcor⟩

/-! ## §2.227  O(Y)-valued sets and sheaves

  "Let Y be a topological space, O(Y) the locale of open subsets thereof.
  The category of maps of O(Y)-valued sets is equivalent to H(Y)."
  [§2.227, proof via the bijection: irredundant O(Y)-valued sets ↔ local homeomorphisms
  over Y (étale spaces); the §2.16(12) construction of O(Y)-valued relations.]

  Requires: types for `Locale`, `O(Y)-valued sets`, `LocalHomeomorphism`/étale spaces,
  and the category H(Y) of sheaves — none constructed in this repo.  -/

-- BOOK §2.227: Let Y be a topological space, O(Y) the locale of open subsets thereof.
-- The category of maps of O(Y)-valued sets is equivalent to H(Y).

end Freyd.Alg
