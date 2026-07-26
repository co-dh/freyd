/-
  `diag.Tape` — the second monoidal structure: `∪` and `⊥`.

  Phase 8 of `diag/PLAN.md`.  `diag/CB.lean`'s `⊗` carries a special Frobenius structure whose
  comonoid/monoid pair yields `∩` and `⊤` (`diag/CB_Derived.lean`).  Union is the same story told
  about a SECOND structure, `⊕` — this is the layer `TapeDiagrams.pdf` draws as tapes.

  WHY `⊕` IS NOT ANOTHER `CartBicat`.  The obvious economy — reuse `CartBicat` at `⊕` and get every
  `∩` proof over again as a `∪` proof — does not work, and it is worth recording why.  `Rel(Set)`'s
  `⊕` is `Sum`, and there `Δ⊕;∇⊕ = 𝟙` while `∇⊕;Δ⊕ ≥ 𝟙`: the bubble is BIGGER than the identity,
  because `∇⊕;Δ⊕` sends `inl x` to both `inl x` and `inr x`.  Def. 4.1's inequation (37), `∇;Δ ≤ 𝟙`,
  therefore fails at `⊕`.  The two structures are genuinely different: `⊗` is special Frobenius, `⊕`
  is a biproduct.

  WHAT IS ASSUMED, AND WHY THIS PRESENTATION.  `TapeDiagrams` Def. 7.1 presents `⊕` as the second
  half of a rig category, which brings a second set of associators, unitors and symmetries plus the
  distributors relating them.  None of that coherence is consumed by the `∪`/`⊥` derivation, so `⊕`
  is presented here by its UNIVERSAL PROPERTY instead — injections, a copairing, and uniqueness —
  which is equivalent and costs no coherence lemmas at all.  `pair` is then the converse of a
  copairing, so the product half is free.

  The payoff is that `∪` is proved to be the JOIN of the hom order, after which idempotence,
  commutativity, associativity, the two absorption laws and `⊥ ∪ R = R` are lattice facts about a
  join and the meet `diag/CB_Derived.lean` already established — not eleven separate derivations.
-/
import diag.CB_Allegory
import Freyd.S2_20

universe v u

namespace Freyd.Diag

open Freyd
open scoped SymMonCat
open CartBicat

/-! ### The biproduct -/

/-- A cartesian bicategory of relations whose objects also carry a BIPRODUCT `⊕` and a zero object.

    `copair` is the coproduct's mediating arrow; the product half comes free through `conv`, so no
    separate `pair` field is needed.  `copair_mono` is what makes `⊕` interact with the hom order at
    all — without it `∪` would be an operation with no relation to `≤`. -/
class Biprod (𝒞 : Type u) extends CartBicat.{v} 𝒞 where
  /-- The biproduct object. -/
  sum (a b : 𝒞) : 𝒞
  /-- The two injections. -/
  inl (a b : 𝒞) : a ⟶ sum a b
  inr (a b : 𝒞) : b ⟶ sum a b
  /-- The coproduct's mediating arrow, `[R, S]`. -/
  copair {a b c : 𝒞} (R : a ⟶ c) (S : b ⟶ c) : sum a b ⟶ c
  inl_copair {a b c : 𝒞} (R : a ⟶ c) (S : b ⟶ c) : inl a b ≫ copair R S = R
  inr_copair {a b c : 𝒞} (R : a ⟶ c) (S : b ⟶ c) : inr a b ≫ copair R S = S
  /-- The injections are jointly epic. -/
  copair_uniq {a b c : 𝒞} {X Y : sum a b ⟶ c} :
    inl a b ≫ X = inl a b ≫ Y → inr a b ≫ X = inr a b ≫ Y → X = Y
  /-- The mediating arrow is monotone — the clause that ties `⊕` to the poset enrichment. -/
  copair_mono {a b c : 𝒞} {R R' : a ⟶ c} {S S' : b ⟶ c} :
    R ≤ R' → S ≤ S' → copair R S ≤ copair R' S'
  /-- Each injection is a partial identity read backwards, i.e. injective as a relation. -/
  conv_inl_le (a b : 𝒞) : (conv (inl a b) ≫ inl a b) ≤ 𝟙 (sum a b)
  conv_inr_le (a b : 𝒞) : (conv (inr a b) ≫ inr a b) ≤ 𝟙 (sum a b)
  /-- The `⊕`-special law: copy into both summands, then merge, and nothing has happened.  This is
      `Δ⊕;∇⊕ = 𝟙`, the one equation of the `⊕` structure that is not universal-property bookkeeping. -/
  diag_codiag (a : 𝒞) :
    conv (copair (𝟙 a) (𝟙 a)) ≫ copair (𝟙 a) (𝟙 a) = 𝟙 a
  /-- The zero object: initial, hence — through `conv` — terminal too. -/
  zero : 𝒞
  toZero (a : 𝒞) : a ⟶ zero
  toZero_uniq {a : 𝒞} (X : a ⟶ zero) : X = toZero a
  /-- The zero arrow is the bottom of every hom order. -/
  bot_le {a b : 𝒞} (R : a ⟶ b) : (toZero a ≫ conv (toZero b)) ≤ R

namespace Biprod

variable {𝒞 : Type u} [Biprod.{v} 𝒞]

/-- `⟨R, S⟩`, the product's mediating arrow — the converse of a copairing.  `Rel` is self-dual, and
    this is where that is spent: the whole product half of the biproduct is one `conv`. -/
def pair {a b c : 𝒞} (R : c ⟶ a) (S : c ⟶ b) : c ⟶ sum a b :=
  conv (copair (conv R) (conv S))

/-- `R ∪ S = ⟨R, S⟩ ; [𝟙, 𝟙]`: offer both, then forget which was taken. -/
def union {a b : 𝒞} (R S : a ⟶ b) : a ⟶ b := pair R S ≫ copair (𝟙 b) (𝟙 b)

/-- `⊥`, the zero arrow, routed through the zero object. -/
def bot (a b : 𝒞) : a ⟶ b := toZero a ≫ conv (toZero (𝒞 := 𝒞) b)

/-! ### The product half, for free through `conv` -/

theorem pair_conv_inl {a b c : 𝒞} (R : c ⟶ a) (S : c ⟶ b) :
    pair R S ≫ conv (inl a b) = R := by
  dsimp [pair]; rw [← conv_comp, inl_copair, conv_conv]

theorem pair_conv_inr {a b c : 𝒞} (R : c ⟶ a) (S : c ⟶ b) :
    pair R S ≫ conv (inr a b) = S := by
  dsimp [pair]; rw [← conv_comp, inr_copair, conv_conv]

/-- The projections are jointly monic — `copair_uniq` read through `conv`. -/
theorem pair_uniq {a b c : 𝒞} {X Y : c ⟶ sum a b}
    (hl : X ≫ conv (inl a b) = Y ≫ conv (inl a b))
    (hr : X ≫ conv (inr a b) = Y ≫ conv (inr a b)) : X = Y := by
  have hc : conv X = conv Y := by
    refine copair_uniq ?_ ?_
    · have h := congrArg conv hl; rwa [conv_comp, conv_comp, conv_conv] at h
    · have h := congrArg conv hr; rwa [conv_comp, conv_comp, conv_conv] at h
  have h := congrArg conv hc; rwa [conv_conv, conv_conv] at h

theorem comp_pair {a b c d : 𝒞} (X : d ⟶ c) (R : c ⟶ a) (S : c ⟶ b) :
    X ≫ pair R S = pair (X ≫ R) (X ≫ S) := by
  refine pair_uniq ?_ ?_
  · rw [Cat.assoc, pair_conv_inl, pair_conv_inl]
  · rw [Cat.assoc, pair_conv_inr, pair_conv_inr]

theorem copair_comp {a b c d : 𝒞} (R : a ⟶ c) (S : b ⟶ c) (W : c ⟶ d) :
    copair R S ≫ W = copair (R ≫ W) (S ≫ W) := by
  refine copair_uniq ?_ ?_
  · rw [← Cat.assoc, inl_copair, inl_copair]
  · rw [← Cat.assoc, inr_copair, inr_copair]

theorem pair_mono {a b c : 𝒞} {R R' : c ⟶ a} {S S' : c ⟶ b} (hR : R ≤ R') (hS : S ≤ S') :
    pair R S ≤ pair R' S' :=
  conv_mono (copair_mono (conv_mono hR) (conv_mono hS))

/-! ### `∪` is the join

Everything below this point is lattice theory: once `∪` is shown to be the least upper bound of the
hom order — of which `∩` is already the greatest lower bound (`meet_glb`, `diag/CB_Derived.lean`) —
idempotence, commutativity, associativity, both absorption laws and `⊥ ∪ R = R` are consequences,
not eleven separate diagram derivations. -/

theorem pair_id_id (a : 𝒞) : pair (𝟙 a) (𝟙 a) = conv (copair (𝟙 a) (𝟙 a)) := by
  dsimp [pair]; rw [conv_id]

theorem union_idem {a b : 𝒞} (R : a ⟶ b) : union R R = R := by
  have h : pair R R = R ≫ pair (𝟙 b) (𝟙 b) := by rw [comp_pair, Cat.comp_id]
  dsimp [union]
  rw [h, Cat.assoc, pair_id_id, diag_codiag, Cat.comp_id]

/-- Half of `𝟙 = ⟨inl, inr⟩`: the left projection is below the codiagonal.  This is the one step
    that spends `conv_inl_le`, i.e. that the injection is injective. -/
theorem conv_inl_le_codiag (b : 𝒞) : conv (inl b b) ≤ copair (𝟙 b) (𝟙 b) := by
  have h := OrderedCat.comp_mono (conv_inl_le b b) (OrderedCat.le_refl (copair (𝟙 b) (𝟙 b)))
  rwa [Cat.assoc, inl_copair, Cat.comp_id, Cat.id_comp] at h

theorem conv_inr_le_codiag (b : 𝒞) : conv (inr b b) ≤ copair (𝟙 b) (𝟙 b) := by
  have h := OrderedCat.comp_mono (conv_inr_le b b) (OrderedCat.le_refl (copair (𝟙 b) (𝟙 b)))
  rwa [Cat.assoc, inr_copair, Cat.comp_id, Cat.id_comp] at h

theorem le_union_left {a b : 𝒞} (R S : a ⟶ b) : R ≤ union R S := by
  have h := OrderedCat.comp_mono (OrderedCat.le_refl (pair R S)) (conv_inl_le_codiag b)
  rwa [pair_conv_inl] at h

theorem le_union_right {a b : 𝒞} (R S : a ⟶ b) : S ≤ union R S := by
  have h := OrderedCat.comp_mono (OrderedCat.le_refl (pair R S)) (conv_inr_le_codiag b)
  rwa [pair_conv_inr] at h

theorem union_le {a b : 𝒞} {R S T : a ⟶ b} (hR : R ≤ T) (hS : S ≤ T) : union R S ≤ T := by
  have h : union R S ≤ union T T :=
    OrderedCat.comp_mono (pair_mono hR hS) (OrderedCat.le_refl _)
  rwa [union_idem] at h

theorem union_mono {a b : 𝒞} {R R' S S' : a ⟶ b} (hR : R ≤ R') (hS : S ≤ S') :
    union R S ≤ union R' S' :=
  union_le (OrderedCat.le_trans hR (le_union_left R' S'))
    (OrderedCat.le_trans hS (le_union_right R' S'))

theorem union_comm {a b : 𝒞} (R S : a ⟶ b) : union R S = union S R :=
  OrderedCat.le_antisymm (union_le (le_union_right S R) (le_union_left S R))
    (union_le (le_union_right R S) (le_union_left R S))

theorem union_assoc {a b : 𝒞} (R S T : a ⟶ b) :
    union R (union S T) = union (union R S) T := by
  refine OrderedCat.le_antisymm (union_le ?_ ?_) (union_le ?_ ?_)
  · exact OrderedCat.le_trans (le_union_left R S) (le_union_left _ T)
  · exact union_le (OrderedCat.le_trans (le_union_right R S) (le_union_left _ T))
      (le_union_right _ T)
  · exact union_le (le_union_left R _)
      (OrderedCat.le_trans (le_union_left S T) (le_union_right R _))
  · exact OrderedCat.le_trans (le_union_right S T) (le_union_right R _)

/-! ### `∪` against `∩`, `≫`, `°` and `⊥` -/

theorem union_meet_absorb {a b : 𝒞} (R S : a ⟶ b) : union R (meet S R) = R :=
  OrderedCat.le_antisymm (union_le (OrderedCat.le_refl R) (meet_le_right S R))
    (le_union_left R (meet S R))

theorem meet_union_absorb {a b : 𝒞} (R S : a ⟶ b) : meet (union R S) R = R :=
  OrderedCat.le_antisymm (meet_le_right (union R S) R)
    (meet_glb (le_union_left R S) (OrderedCat.le_refl R))

theorem bot_union {a b : 𝒞} (R : a ⟶ b) : union (bot a b) R = R :=
  OrderedCat.le_antisymm (union_le (bot_le R) (OrderedCat.le_refl R))
    (le_union_right (bot a b) R)

theorem comp_union {a b c : 𝒞} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ union S T = union (R ≫ S) (R ≫ T) := by
  dsimp [union]; rw [← Cat.assoc, comp_pair]

theorem conv_union {a b : 𝒞} (R S : a ⟶ b) :
    conv (union R S) = union (conv R) (conv S) := by
  refine OrderedCat.le_antisymm ?_ (union_le (conv_mono (le_union_left R S))
    (conv_mono (le_union_right R S)))
  have h : union R S ≤ conv (union (conv R) (conv S)) := by
    refine union_le ?_ ?_
    · have := conv_mono (le_union_left (conv R) (conv S)); rwa [conv_conv] at this
    · have := conv_mono (le_union_right (conv R) (conv S)); rwa [conv_conv] at this
  have := conv_mono h; rwa [conv_conv] at this

theorem union_comp {a b c : 𝒞} (R S : a ⟶ b) (T : b ⟶ c) :
    union R S ≫ T = union (R ≫ T) (S ≫ T) := by
  have h : conv (union R S ≫ T) = conv (union (R ≫ T) (S ≫ T)) := by
    rw [conv_comp, conv_union, conv_union, comp_union, conv_comp, conv_comp]
  have := congrArg conv h; rwa [conv_conv, conv_conv] at this

theorem bot_comp {a b c : 𝒞} (R : b ⟶ c) : bot a b ≫ R = bot a c := by
  have h : conv R ≫ toZero (𝒞 := 𝒞) b = toZero (𝒞 := 𝒞) c := toZero_uniq _
  have h' := congrArg conv h
  rw [conv_comp, conv_conv] at h'
  dsimp [bot]
  rw [Cat.assoc, h']

theorem conv_bot (a b : 𝒞) : conv (bot a b) = bot b a := by
  dsimp [bot]; rw [conv_comp, conv_conv]

theorem comp_bot {a b c : 𝒞} (R : a ⟶ b) : R ≫ bot b c = bot a c := by
  have h : conv (R ≫ bot b c) = conv (bot a c) := by
    rw [conv_comp, conv_bot, conv_bot, bot_comp]
  have := congrArg conv h; rwa [conv_conv, conv_conv] at this

end Biprod

/-! ### The rig: `⊗` distributes over `⊕`

The one axiom the biproduct alone does not give.  `∩` is `Δ;(R ⊗ S);∇`, so `R ∩ (S ∪ T)` reduces to
`(R ∩ S) ∪ (R ∩ T)` exactly when `⊗` carries `∪` through — which is what makes the two structures a
RIG rather than two unrelated monoidal products.  `TapeDiagrams.pdf` Def. 7.1 packages it as the
distributors of a rig category; here it is stated where it is used. -/

open Biprod in
/-- A cartesian bicategory of relations with a biproduct that its tensor distributes over. -/
class FbCbRig (𝒞 : Type u) extends Biprod.{v} 𝒞 where
  tensHom_union {a a' b b' : 𝒞} (R : a ⟶ a') (S T : b ⟶ b') :
    (R ⊗ₕ union S T) = union (R ⊗ₕ S) (R ⊗ₕ T)

namespace FbCbRig

open Biprod

variable {𝒞 : Type u} [FbCbRig.{v} 𝒞]

/-- The distributive law, `R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)`.  `∩` is `Δ;(R ⊗ −);∇`, so this is
    `tensHom_union` with a copy in front and a merge behind, and the two composition-distributes-over-
    union laws carry `∪` past each. -/
theorem meet_union_distrib {a b : 𝒞} (R S T : a ⟶ b) :
    meet R (union S T) = union (meet R S) (meet R T) := by
  dsimp [meet]
  rw [tensHom_union, union_comp, comp_union]

/-- **Every fb-cb rig category is a distributive allegory.**  `∪ := union`, `𝟘 := bot`; the
    `Allegory` half is phase 5's `allegoryOfCartBicat`, so this file supplies only the six laws
    that mention `∪` or `𝟘`.

    A `def`, NOT a global instance — the same precedent as `allegoryOfCartBicat`, so that it cannot
    form a diamond with the hand-built `DistributiveAllegory RelSet` (`AOP/A6_1_RelSet.lean`). -/
def distributiveAllegoryOfFbCb (𝒞 : Type u) [FbCbRig.{v} 𝒞] :
    Freyd.Alg.DistributiveAllegory 𝒞 :=
  { allegoryOfCartBicat 𝒞 with
    zero := fun {a b} => bot a b
    union := union
    zero_comp := fun R => bot_comp R
    comp_zero := fun R => comp_bot R
    union_idem := union_idem
    union_comm := union_comm
    union_assoc := union_assoc
    union_inter_absorb := union_meet_absorb
    inter_union_absorb := meet_union_absorb
    comp_union_distrib := comp_union
    inter_union_distrib := meet_union_distrib
    zero_union := bot_union }

end FbCbRig

end Freyd.Diag
