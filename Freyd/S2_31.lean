import Freyd.S2_03

universe u v

/-
  Freyd & Scedrov, *Categories and Allegories* §2.316.

  This file completes the two §2.316 items that `S2_3.lean` left partial:

  TASK 1 (bundled instance).  `S2_3.lean` proves the *raw* Heyting adjunction
  `heyting_adj_coref` / `oneHeyting_adj` on the coreflexives `Cor(a)` of a
  division allegory, but never packages them into an order/lattice typeclass.
  Here we provide a *bundled* Heyting-algebra instance `corHeytAlg` on the
  subtype `Cor a := {R : a ⟶ a // Coreflexive R}`.

  TASK 2 (the converse).  Freyd: "a Heyting algebra may be construed as a
  one-object division allegory", with
      x ∩ y = x ∧ y,  x y = x ∧ y,  x° = x,  x ∪ y = x ∨ y,  x / y = y → x.
  Given a Heyting algebra `H` we build the one-object allegory `OneObj H`
  (single object, hom-set `H`) and prove it is an `Allegory`, a
  `DistributiveAllegory`, and a `DivisionAllegory`.

  Why a *local* Heyting class.  The repo already has a `HeytingAlgebra`
  (`S1_72.lean`), but it is a `Cat`-with-images / `Subobject.le` class, not an
  order on a bare `Type`; and `Frame` (`Locale.lean`) demands *complete* joins
  `sSup` that `Cor(a)` of a general division allegory need not have.  Neither
  fits, so we define the minimal order-theoretic Heyting algebra `HeytAlg`
  (meet, join, top, bot, implication with the adjunction `c ≤ a⇨b ↔ c⊓a ≤ b`)
  and reuse it for BOTH tasks.  STRICTLY MATHLIB-FREE.
-/



namespace Freyd

/-! ## A minimal order-theoretic Heyting algebra

  A bounded lattice `(≤, ⊓, ⊔, ⊤, ⊥)` with a binary implication `⇨` whose
  defining adjunction is `c ≤ a ⇨ b  ↔  c ⊓ a ≤ b`.  This is exactly what is
  needed to (i) bundle `Cor(a)` and (ii) build the one-object allegory. -/

/-- A Heyting algebra on a bare `Type` (order-theoretic, no completeness). -/
class HeytAlg (H : Type u) where
  le : H → H → Prop
  le_refl    : ∀ a, le a a
  le_trans   : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  /-- meet (greatest lower bound) -/
  meet : H → H → H
  meet_le_left  : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  le_meet : ∀ {a b c}, le c a → le c b → le c (meet a b)
  /-- join (least upper bound) -/
  join : H → H → H
  le_join_left  : ∀ a b, le a (join a b)
  le_join_right : ∀ a b, le b (join a b)
  join_le : ∀ {a b c}, le a c → le b c → le (join a b) c
  /-- top -/
  top : H
  le_top : ∀ a, le a top
  /-- bottom -/
  bot : H
  bot_le : ∀ a, le bot a
  /-- Heyting implication -/
  himp : H → H → H
  /-- the defining adjunction: `c ≤ a ⇨ b  ↔  c ⊓ a ≤ b`. -/
  himp_adj : ∀ a b c, le c (himp a b) ↔ le (meet c a) b

namespace HeytAlg

variable {H : Type u} [HeytAlg H]

local infix:50 " ≼ "  => HeytAlg.le
local infixl:70 " ⊓ "  => HeytAlg.meet
local infixl:65 " ⊔ "  => HeytAlg.join
local infixr:60 " ⇨ "  => HeytAlg.himp

/-! ### Derived lattice facts -/

theorem meet_comm (a b : H) : a ⊓ b = b ⊓ a :=
  le_antisymm (le_meet (meet_le_right a b) (meet_le_left a b))
              (le_meet (meet_le_right b a) (meet_le_left b a))

theorem meet_assoc (a b c : H) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) :=
  le_antisymm
    (le_meet (le_trans (meet_le_left _ _) (meet_le_left _ _))
      (le_meet (le_trans (meet_le_left _ _) (meet_le_right _ _)) (meet_le_right _ _)))
    (le_meet (le_meet (meet_le_left _ _) (le_trans (meet_le_right _ _) (meet_le_left _ _)))
      (le_trans (meet_le_right _ _) (meet_le_right _ _)))

theorem meet_idem (a : H) : a ⊓ a = a :=
  le_antisymm (meet_le_left a a) (le_meet (le_refl a) (le_refl a))

theorem meet_le_meet {a b c d : H} (h1 : a ≼ c) (h2 : b ≼ d) : a ⊓ b ≼ c ⊓ d :=
  le_meet (le_trans (meet_le_left _ _) h1) (le_trans (meet_le_right _ _) h2)

theorem join_comm (a b : H) : a ⊔ b = b ⊔ a :=
  le_antisymm (join_le (le_join_right b a) (le_join_left b a))
              (join_le (le_join_right a b) (le_join_left a b))

theorem join_assoc (a b c : H) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) :=
  le_antisymm
    (join_le (join_le (le_join_left _ _) (le_trans (le_join_left _ _) (le_join_right _ _)))
      (le_trans (le_join_right _ _) (le_join_right _ _)))
    (join_le (le_trans (le_join_left _ _) (le_join_left _ _))
      (join_le (le_trans (le_join_right _ _) (le_join_left _ _)) (le_join_right _ _)))

theorem join_idem (a : H) : a ⊔ a = a :=
  le_antisymm (join_le (le_refl a) (le_refl a)) (le_join_left a a)

/-- `a ⊓ b = a ↔ a ≤ b` (the order is recoverable from meet). -/
theorem meet_eq_left_iff_le {a b : H} : a ⊓ b = a ↔ a ≼ b := by
  constructor
  · intro h; exact h ▸ meet_le_right a b
  · intro h; exact le_antisymm (meet_le_left a b) (le_meet (le_refl a) h)

theorem meet_top (a : H) : a ⊓ top = a :=
  le_antisymm (meet_le_left _ _) (le_meet (le_refl _) (le_top _))

theorem top_meet (a : H) : top ⊓ a = a := by rw [meet_comm]; exact meet_top a

theorem meet_bot (a : H) : a ⊓ bot = bot :=
  le_antisymm (meet_le_right _ _) (bot_le _)

theorem bot_meet (a : H) : bot ⊓ a = bot := by rw [meet_comm]; exact meet_bot a

theorem bot_join (a : H) : bot ⊔ a = a :=
  le_antisymm (join_le (bot_le _) (le_refl _)) (le_join_right _ _)

/-- absorption `R ∪ (S ∩ R) = R`. -/
theorem join_meet_absorb (a b : H) : a ⊔ (b ⊓ a) = a :=
  le_antisymm (join_le (le_refl _) (meet_le_right _ _)) (le_join_left _ _)

/-- absorption `(R ∪ S) ∩ R = R`. -/
theorem meet_join_absorb (a b : H) : (a ⊔ b) ⊓ a = a :=
  le_antisymm (meet_le_right _ _) (le_meet (le_join_left _ _) (le_refl _))

/-- Heyting ⟹ distributive: `a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)` (uses `⇨`). -/
theorem meet_join_distrib (a b c : H) : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  apply le_antisymm
  · -- key: `b ⊔ c ≤ a ⇨ d`, then transpose by the adjunction.
    have hb : b ≼ a ⇨ ((a ⊓ b) ⊔ (a ⊓ c)) :=
      (himp_adj a _ b).mpr (by rw [meet_comm]; exact le_join_left _ _)
    have hc : c ≼ a ⇨ ((a ⊓ b) ⊔ (a ⊓ c)) :=
      (himp_adj a _ c).mpr (by rw [meet_comm]; exact le_join_right _ _)
    have hfin := (himp_adj a ((a ⊓ b) ⊔ (a ⊓ c)) (b ⊔ c)).mp (join_le hb hc)
    rw [meet_comm a (b ⊔ c)]; exact hfin
  · exact join_le (meet_le_meet (le_refl _) (le_join_left _ _))
                  (meet_le_meet (le_refl _) (le_join_right _ _))

/-! ### The two equational facts the allegory axioms reduce to

  In the one-object allegory composition = intersection = meet, so both the
  semidistributive law and the modular law become identities of nested meets. -/

/-- `R(S∩T) = (RS ∩ R(S∩T)) ∩ RT`, with composition and intersection = meet. -/
theorem semidistrib_eq (R S T : H) :
    R ⊓ (S ⊓ T) = ((R ⊓ S) ⊓ (R ⊓ (S ⊓ T))) ⊓ (R ⊓ T) := by
  apply le_antisymm
  · refine le_meet (le_meet (le_meet (meet_le_left _ _) ?_) (le_refl _))
      (le_meet (meet_le_left _ _) ?_)
    · exact le_trans (meet_le_right _ _) (meet_le_left _ _)
    · exact le_trans (meet_le_right _ _) (meet_le_right _ _)
  · exact le_trans (meet_le_left _ _) (meet_le_right _ _)

/-- `(RS ∩ T) = (RS ∩ T) ∩ ((R ∩ TS°)S)`, with composition/intersection = meet
    and reciprocation = identity (`TS° = T ⊓ S`). -/
theorem modular_eq (R S T : H) :
    (R ⊓ S) ⊓ T = ((R ⊓ S) ⊓ T) ⊓ ((R ⊓ (T ⊓ S)) ⊓ S) := by
  apply le_antisymm
  · refine le_meet (le_refl _) (le_meet (le_meet ?_ ?_) ?_)
    · exact le_trans (meet_le_left _ _) (meet_le_left _ _)
    · exact le_meet (meet_le_right _ _)
        (le_trans (meet_le_left _ _) (meet_le_right _ _))
    · exact le_trans (meet_le_left _ _) (meet_le_right _ _)
  · exact meet_le_left _ _

end HeytAlg

/-! ## TASK 2.  A Heyting algebra as a one-object division allegory (§2.316) -/

open Freyd.Alg

/-- The single object of the one-object allegory built from `H`.  The `H`
    parameter makes `OneObj H` carry the algebra, so instance resolution can
    recover it. -/
inductive OneObj (H : Type u) : Type u
  | pt

namespace OneObj

variable {H : Type u} [HeytAlg H]

/-- Hom-set is `H`; identity = `⊤`; composition = meet `⊓`. -/
instance instCat : Cat.{u} (OneObj H) where
  Hom _ _ := H
  id _ := HeytAlg.top
  comp f g := HeytAlg.meet f g
  id_comp f := HeytAlg.top_meet f
  comp_id f := HeytAlg.meet_top f
  assoc f g h := HeytAlg.meet_assoc f g h

/-- §2.316: reciprocation = identity, intersection = meet. -/
instance instAllegory : Allegory.{u} (OneObj H) where
  recip f := f
  inter f g := HeytAlg.meet f g
  recip_recip _ := rfl
  recip_comp R S := HeytAlg.meet_comm R S
  recip_inter _ _ := rfl
  inter_idem := HeytAlg.meet_idem
  inter_comm := HeytAlg.meet_comm
  inter_assoc R S T := (HeytAlg.meet_assoc R S T).symm
  semidistrib := HeytAlg.semidistrib_eq
  modular := HeytAlg.modular_eq

/-- §2.316: zero = `⊥`, union = join `⊔`; distributivity is Heyting. -/
instance instDistributiveAllegory : DistributiveAllegory (OneObj H) :=
  { instAllegory with
    zero := HeytAlg.bot
    union := HeytAlg.join
    zero_comp := HeytAlg.bot_meet
    comp_zero := HeytAlg.meet_bot
    union_idem := HeytAlg.join_idem
    union_comm := HeytAlg.join_comm
    union_assoc := fun R S T => (HeytAlg.join_assoc R S T).symm
    union_inter_absorb := HeytAlg.join_meet_absorb
    inter_union_absorb := HeytAlg.meet_join_absorb
    comp_union_distrib := fun R S T => HeytAlg.meet_join_distrib R S T
    inter_union_distrib := fun R S T => HeytAlg.meet_join_distrib R S T
    zero_union := fun R => HeytAlg.bot_join R }

/-- §2.316: right division `R / S := S ⇨ R` (Heyting implication).
    The division adjunction `T ⊑ R/S ↔ T≫S ⊑ R` is exactly `himp_adj`. -/
instance instDivisionAllegory : DivisionAllegory (OneObj H) :=
  { instDistributiveAllegory with
    div := fun R S => HeytAlg.himp S R
    div_comp_le := fun R S =>
      -- `(S⇨R) ⊓ S ≤ R` is the counit of `himp_adj S R` applied to `le_refl`.
      HeytAlg.meet_eq_left_iff_le.mpr ((HeytAlg.himp_adj S R (HeytAlg.himp S R)).mp (HeytAlg.le_refl _))
    le_div := fun T R S h =>
      -- transpose `T⊓S ≤ R` (= `h`) to `T ≤ S⇨R` via `himp_adj`.
      HeytAlg.meet_eq_left_iff_le.mpr
        ((HeytAlg.himp_adj S R T).mpr (HeytAlg.meet_eq_left_iff_le.mp h)) }

end OneObj

/-! ## TASK 1.  The bundled Heyting algebra on the coreflexives `Cor(a)`

  For an object `a` of a division allegory, `S2_3.lean` proves the raw
  adjunction `heyting_adj_coref`.  We package the coreflexives
  `Cor a = {R : a ⟶ a // Coreflexive R}` into a `HeytAlg` instance, with
  meet/join/top/bot = `∩`/`∪`/`1`/`𝟘` and implication `1 ∩ B/A` (`heytingImpl`). -/

/-- The coreflexives (subidentities) on `a`: `{R : a ⟶ a // R ⊑ 1}`. -/
def Cor {𝒜 : Type u} [DivisionAllegory 𝒜] (a : 𝒜) : Type v :=
  {R : a ⟶ a // Coreflexive R}

namespace Cor

variable {𝒜 : Type u} [DivisionAllegory 𝒜] {a : 𝒜}

/-- §2.316: `Cor(a)` is a Heyting algebra.  Order = allegory order `⊑`;
    meet/join = `∩`/`∪`; top/bot = `1`/`𝟘`; implication = `heytingImpl`. -/
instance instHeytAlg : HeytAlg (Cor a) where
  le A B := A.1 ⊑ B.1
  le_refl A := Freyd.Alg.le_refl A.1
  le_trans h1 h2 := Freyd.Alg.le_trans h1 h2
  le_antisymm h1 h2 := Subtype.ext (Freyd.Alg.le_antisymm h1 h2)
  meet A B := ⟨A.1 ∩ B.1, le_trans (inter_lb_left A.1 B.1) A.2⟩
  meet_le_left A B := inter_lb_left A.1 B.1
  meet_le_right A B := inter_lb_right A.1 B.1
  le_meet h1 h2 := le_inter h1 h2
  join A B := ⟨A.1 ∪ B.1, union_lub A.2 B.2⟩
  le_join_left A B := le_union_left A.1 B.1
  le_join_right A B := le_union_right A.1 B.1
  join_le h1 h2 := union_lub h1 h2
  top := ⟨Cat.id a, Freyd.Alg.le_refl _⟩
  le_top A := A.2
  bot := ⟨𝟘, zero_le _⟩
  bot_le A := zero_le A.1
  himp A B := ⟨heytingImpl A.1 B.1, inter_lb_left _ _⟩
  himp_adj A B C := by
    -- goal: `C.1 ⊑ heytingImpl A.1 B.1 ↔ (C.1 ∩ A.1) ⊑ B.1`
    show C.1 ⊑ heytingImpl A.1 B.1 ↔ (C.1 ∩ A.1) ⊑ B.1
    rw [← heyting_adj_coref A.2 C.2, coreflexive_comp_eq_inter A.2 C.2,
        Allegory.inter_comm A.1 C.1]

end Cor

end Freyd
