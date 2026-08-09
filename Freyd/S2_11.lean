module

public import Freyd.S2_10
public import Freyd.S2_30

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories*.

  §2.113  A lattice-ordered commutative monoid as a one-object allegory.
  §2.351  Characterisation of `R/ₛR` among symmetric morphisms.
  §2.357  The simple part `R/ₛ1` equals `(Dom R/ₛ1)·R` (the converse making it
          the LARGEST simple morphism of the form `A·R`, `A` coreflexive).

  ----------------------------------------------------------------------------
  §2.113.  "Let M be a lattice-ordered commutative monoid and define
            ◯x = x□ = 1, x° = x.  Except for the modular identity M is an
            allegory.  Not even the above consequence x ⊑ x x° x need hold
            (consider the unit interval under multiplication)."

  We build a single object `*` with hom-set `M`, composition `=` the monoid
  multiplication, identity `=` 1, reciprocation `=` the identity map, and
  intersection `=` the lattice meet `⊓`.  Every allegory axiom EXCEPT the
  modular law follows from "lattice-ordered commutative monoid":
    · category laws            ← commutative monoid;
    · `(R°)° = R`, `(R∩S)° = R°∩S°`  ← reciprocation is the identity;
    · `(RS)° = S°R°`           ← COMMUTATIVITY of multiplication;
    · semi-lattice for `∩`     ← meet is idempotent/commutative/associative;
    · semi-distributivity      ← multiplication is MONOTONE.
  The MODULAR law genuinely fails for a general l-monoid (book: the unit
  interval `[0,1]` under multiplication already breaks the weaker consequence
  `x ⊑ x·x°·x = x³`, since `x³ ⩽ x` there).  So the full `Allegory` instance
  requires ONE extra hypothesis — the modular identity itself — packaged as
  `ModularLOCMonoid`.  This is exactly the hypothesis the book isolates.
-/



namespace Freyd.Alg

/-! ## §2.113  Lattice-ordered commutative monoid -/

/-- A **LATTICE-ORDERED COMMUTATIVE MONOID** (Freyd §2.113): a commutative
    monoid `(M, ·, 1)` together with a lattice `(⊓, ⊔)`, in which the order
    `a ⩽ b :⇔ a ⊓ b = a` makes multiplication monotone.  No modular law. -/
public class LOCMonoid (M : Type u) where
  /-- Monoid multiplication. -/
  mul  : M → M → M
  /-- Monoid identity. -/
  one  : M
  /-- Lattice meet. -/
  meet : M → M → M
  /-- Lattice join. -/
  join : M → M → M
  -- commutative monoid
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul   : ∀ a, mul one a = a
  mul_one   : ∀ a, mul a one = a
  mul_comm  : ∀ a b, mul a b = mul b a
  -- meet semi-lattice
  meet_idem  : ∀ a, meet a a = a
  meet_comm  : ∀ a b, meet a b = meet b a
  meet_assoc : ∀ a b c, meet a (meet b c) = meet (meet a b) c
  -- join semi-lattice
  join_idem  : ∀ a, join a a = a
  join_comm  : ∀ a b, join a b = join b a
  join_assoc : ∀ a b c, join a (join b c) = join (join a b) c
  -- absorption laws make `(⊓, ⊔)` a lattice
  meet_absorb : ∀ a b, meet a (join a b) = a
  join_absorb : ∀ a b, join a (meet a b) = a
  -- multiplication is MONOTONE: `a ⩽ b → a·c ⩽ b·c`, with `a ⩽ b :⇔ a⊓b = a`.
  mul_mono : ∀ a b c, meet a b = a → meet (mul a c) (mul b c) = mul a c

/-- A **MODULAR** lattice-ordered commutative monoid: an `LOCMonoid` that in
    addition satisfies the allegory modular identity (`x° = x`, so `T S° = T S`):
    `(R S) ⊓ T = ((R S) ⊓ T) ⊓ (R ⊓ (T S))·S`.  This single extra equation is
    the ONLY thing a general l-monoid lacks (book §2.113). -/
public class ModularLOCMonoid (M : Type u) extends LOCMonoid M where
  modular : ∀ R S T : M,
    LOCMonoid.meet (LOCMonoid.mul R S) T
      = LOCMonoid.meet (LOCMonoid.meet (LOCMonoid.mul R S) T)
          (LOCMonoid.mul (LOCMonoid.meet R (LOCMonoid.mul T S)) S)

/-- The single object `*` of the one-object allegory built on `M`.  Keeping `M`
    as a parameter lets the `Cat`/`Allegory` instances recover the hom-set. -/
public inductive LMonObj (M : Type u) : Type u where
  | star : LMonObj M

section LMonObjLOCMonoid

variable {M : Type u} [LOCMonoid M]

local infixl:75 " ⊙ " => LOCMonoid.mul
local infixl:70 " ⊓ "  => LOCMonoid.meet

/-- The single object carries `M` as its endo-hom-set; composition is the monoid
    multiplication and the identity is `1`.  A genuine `Cat` (§1.1). -/
@[expose] public instance instCatLMonObj : Cat (LMonObj M) where
  Hom _ _ := M
  id _    := LOCMonoid.one
  comp f g := f ⊙ g
  id_comp f := LOCMonoid.one_mul f
  comp_id f := LOCMonoid.mul_one f
  assoc f g h := LOCMonoid.mul_assoc f g h

/-- `a ⊓ b ⩽ a`: the meet is a lower bound (left). -/
public theorem meet_le_left (a b : M) : (a ⊓ b) ⊓ a = a ⊓ b := by
  rw [LOCMonoid.meet_comm (a ⊓ b) a, LOCMonoid.meet_assoc, LOCMonoid.meet_idem]

/-- `a ⊓ b ⩽ b`: the meet is a lower bound (right). -/
public theorem meet_le_right (a b : M) : (a ⊓ b) ⊓ b = a ⊓ b := by
  rw [← LOCMonoid.meet_assoc, LOCMonoid.meet_idem]

/-- **Semi-distributivity** for the one-object l-monoid allegory, in the exact
    equational shape `Allegory.semidistrib` demands:
    `R·(S ⊓ T) = ((R·S) ⊓ (R·(S ⊓ T))) ⊓ (R·T)`.
    It holds because multiplication is monotone, so `R·(S⊓T)` lies below both
    `R·S` and `R·T`. -/
public theorem lmonObj_semidistrib (R S T : M) :
    R ⊙ (S ⊓ T) = ((R ⊙ S) ⊓ (R ⊙ (S ⊓ T))) ⊓ (R ⊙ T) := by
  -- `R·(S⊓T) ⩽ R·S`
  have m1 : (R ⊙ (S ⊓ T)) ⊓ (R ⊙ S) = R ⊙ (S ⊓ T) := by
    rw [LOCMonoid.mul_comm R (S ⊓ T), LOCMonoid.mul_comm R S]
    exact LOCMonoid.mul_mono (S ⊓ T) S R (meet_le_left S T)
  -- `R·(S⊓T) ⩽ R·T`
  have m2 : (R ⊙ (S ⊓ T)) ⊓ (R ⊙ T) = R ⊙ (S ⊓ T) := by
    rw [LOCMonoid.mul_comm R (S ⊓ T), LOCMonoid.mul_comm R T]
    exact LOCMonoid.mul_mono (S ⊓ T) T R (meet_le_right S T)
  rw [LOCMonoid.meet_comm (R ⊙ S) (R ⊙ (S ⊓ T)), m1, m2]

end LMonObjLOCMonoid

/-! ### The one-object `Allegory` (under the modular hypothesis)

  Every allegory axiom except `modular` was discharged above from the bare
  `LOCMonoid` structure (`instCatLMonObj`, `lmonObj_semidistrib`, the meet
  semi-lattice laws, `mul_comm`).  Adding the modular identity completes a
  genuine allegory. -/

@[expose] public instance instAllegoryLMonObj {M : Type u} [ModularLOCMonoid M] : Allegory (LMonObj M) where
  toCat := instCatLMonObj
  recip R := R
  inter R S := LOCMonoid.meet R S
  recip_recip _ := rfl
  recip_comp R S := LOCMonoid.mul_comm R S
  recip_inter _ _ := rfl
  inter_idem R := LOCMonoid.meet_idem R
  inter_comm R S := LOCMonoid.meet_comm R S
  inter_assoc R S T := LOCMonoid.meet_assoc R S T
  semidistrib R S T := lmonObj_semidistrib R S T
  modular R S T := ModularLOCMonoid.modular R S T

/-! ### A concrete witness: the two-element Boolean algebra

  `Bool` with `· = ⊓ = and`, `1 = true`, `⊔ = or` is a (distributive, hence
  modular) lattice-ordered commutative monoid, so `LMonObj Bool` is a genuine
  one-object allegory.  Shows the construction is not vacuous. -/

@[expose] public instance : ModularLOCMonoid Bool where
  mul := Bool.and
  one := true
  meet := Bool.and
  join := Bool.or
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  meet_idem := by decide
  meet_comm := by decide
  meet_assoc := by decide
  join_idem := by decide
  join_comm := by decide
  join_assoc := by decide
  meet_absorb := by decide
  join_absorb := by decide
  mul_mono := by decide
  modular := by decide

/-- The construction fires: `LMonObj Bool` is a one-object allegory. -/
example : Allegory (LMonObj Bool) := inferInstance

/-! ## §2.351 / §2.357  Leftover characterisations in division allegories -/

section Division

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- **§2.351**: `R/ₛR` is characterised among SYMMETRIC morphisms by
    `T ⊑ R/ₛR ↔ T R ⊑ R`.  (The general `le_symmDiv_iff` adds the condition
    `T° R ⊑ R`, which collapses to `T R ⊑ R` once `T° = T`.) -/
theorem symmetric_le_symmDiv_self_iff {a b : 𝒜} (T : a ⟶ a) (R : a ⟶ b)
    (hT : Symmetric T) : T ⊑ R /ₛ R ↔ T ≫ R ⊑ R := by
  rw [le_symmDiv_iff]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, by rw [symmetric_eq hT]; exact h⟩

/-- **§2.357**: the simple part is reconstructible from its domain of simplicity,
    `R/ₛ1 = (Dom R/ₛ1)·R`.  This is the converse half of §2.357 that makes `R/ₛ1`
    the LARGEST simple morphism of the form `A·R` with `A ⊑ 1`: it exhibits
    `R/ₛ1` itself in that form (with `A = Dom R/ₛ1`).

    `⊒`: `R/ₛ1 = (Dom R/ₛ1)(R/ₛ1) ⊑ (Dom R/ₛ1)·R` by `dom_comp_self` and `R/ₛ1 ⊑ R`.
    `⊑`: by `simplePart_largest` it suffices that `(Dom R/ₛ1)·R` be a simple,
    coreflexive-restricted `A·R`.  Coreflexivity is `dom_coreflexive`; for
    simplicity, with `P := R/ₛ1` and `D := Dom P`, `(D·R)°·R = R°·D·R ⊑
    R°·(P P°)·R = (R°P)(P°R) ⊑ 1·1 = 1`, using `P° R ⊑ 1` (`P ⊑ R/ₛ1`) and its
    reciprocal `R° P ⊑ 1`. -/
theorem simplePart_eq_domSimplicity_comp {a b : 𝒜} (R : a ⟶ b) :
    simplePart R = domSimplicity R ≫ R := by
  show simplePart R = dom (simplePart R) ≫ R
  apply le_antisymm
  · -- `R/ₛ1 ⊑ (Dom R/ₛ1)·R`: `R/ₛ1 = (Dom R/ₛ1)(R/ₛ1) ⊑ (Dom R/ₛ1)·R`.
    have step : dom (simplePart R) ≫ simplePart R ⊑ dom (simplePart R) ≫ R :=
      comp_mono_left _ (simplePart_le R)
    rwa [dom_comp_self] at step
  · -- `(Dom R/ₛ1)·R ⊑ R/ₛ1`, via `simplePart_largest`
    apply simplePart_largest R (dom (simplePart R)) (dom_coreflexive _)
    -- remaining: `(dom (R/ₛ1) ≫ R)° ≫ R ⊑ 1`
    have hPR : (simplePart R)° ≫ R ⊑ Cat.id b :=
      ((le_symmDiv_iff (simplePart R) R (Cat.id b)).mp (le_refl _)).2
    have hRP : R° ≫ simplePart R ⊑ Cat.id b := by
      have h := recip_mono hPR
      rwa [Allegory.recip_comp, Allegory.recip_recip, recip_id] at h
    have hDP : dom (simplePart R) ⊑ simplePart R ≫ (simplePart R)° := inter_lb_right _ _
    have hid : Cat.id b ≫ Cat.id b ⊑ Cat.id b := by rw [Cat.id_comp]; exact le_refl _
    have e1 : (dom (simplePart R) ≫ R)° ≫ R = (R° ≫ dom (simplePart R)) ≫ R := by
      rw [Allegory.recip_comp, dom_recip]
    rw [e1]
    have hstep1 : (R° ≫ dom (simplePart R)) ≫ R
        ⊑ (R° ≫ (simplePart R ≫ (simplePart R)°)) ≫ R :=
      comp_mono_right (comp_mono_left _ hDP) R
    have e2 : (R° ≫ (simplePart R ≫ (simplePart R)°)) ≫ R
        = (R° ≫ simplePart R) ≫ ((simplePart R)° ≫ R) := by
      rw [← Cat.assoc R° (simplePart R) (simplePart R)°,
          Cat.assoc (R° ≫ simplePart R) (simplePart R)° R]
    rw [e2] at hstep1
    exact le_trans hstep1
      (le_trans (comp_mono_right hRP _) (le_trans (comp_mono_left _ hPR) hid))

end Division

end Freyd.Alg
