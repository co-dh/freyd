/-
  `diag.Tape` — the second monoidal structure: `∪` and `⊥`.

  Phase 8 of `diag/PLAN.md`.  `diag/CB.lean`'s `⊗` carries a special Frobenius structure whose
  comonoid/monoid pair yields `∩` and `⊤` (`diag/CB_Derived.lean`).  Union is the same story told
  about a SECOND structure, `⊕` — this is the layer `TapeDiagrams.pdf` draws as tapes.

  WHY `⊕` IS NOT ANOTHER `CartBicat`.  The obvious economy — reuse `CartBicat` at `⊕` and get every
  `∩` proof over again as a `∪` proof — does not work, and it is worth recording why.  `Rel(Set)`'s
  `⊕` is `Sum`, and there `Δ⊕;∇⊕ = 𝟙` while `∇⊕;Δ⊕ ≥ 𝟙`: the bubble is BIGGER than the identity,
  because `∇⊕;Δ⊕` sends `inl x` to both `inl x` and `inr x`.  Def. 4.1's inequation (37), `▷;◁ ≤ 𝟙`,
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
open scoped Word SymMonCat
open CartBicat

/-! ### The biproduct -/

/-- A cartesian bicategory of relations whose objects also carry a BIPRODUCT `⊕` and a zero object.

    `copair` is the coproduct's mediating arrow; the product half comes free through `conv`, so no
    separate `pair` field is needed.  `copair_mono` is what makes `⊕` interact with the hom order at
    all — without it `∪` would be an operation with no relation to `≤`. -/
class Biprod (O : Type u) extends CartBicat.{v} O where
  /-- The biproduct object. -/
  sum (a b : Word O) : Word O
  /-- The two injections. -/
  inl (a b : Word O) : a ⟶ sum a b
  inr (a b : Word O) : b ⟶ sum a b
  /-- The coproduct's mediating arrow, `[R, S]`. -/
  copair {a b c : Word O} (R : a ⟶ c) (S : b ⟶ c) : sum a b ⟶ c
  inl_copair {a b c : Word O} (R : a ⟶ c) (S : b ⟶ c) : inl a b ≫ copair R S = R
  inr_copair {a b c : Word O} (R : a ⟶ c) (S : b ⟶ c) : inr a b ≫ copair R S = S
  /-- The injections are jointly epic. -/
  copair_uniq {a b c : Word O} {X Y : sum a b ⟶ c} :
    inl a b ≫ X = inl a b ≫ Y → inr a b ≫ X = inr a b ≫ Y → X = Y
  /-- The mediating arrow is monotone — the clause that ties `⊕` to the poset enrichment. -/
  copair_mono {a b c : Word O} {R R' : a ⟶ c} {S S' : b ⟶ c} :
    R ≤ R' → S ≤ S' → copair R S ≤ copair R' S'
  /-- Each injection is a partial identity read backwards, i.e. injective as a relation. -/
  conv_inl_le (a b : Word O) : (conv (inl a b) ≫ inl a b) ≤ 𝟙 (sum a b)
  conv_inr_le (a b : Word O) : (conv (inr a b) ≫ inr a b) ≤ 𝟙 (sum a b)
  /-- The `⊕`-special law: copy into both summands, then merge, and nothing has happened.  This is
      `Δ⊕;∇⊕ = 𝟙`, the one equation of the `⊕` structure that is not universal-property bookkeeping. -/
  diag_codiag (a : Word O) :
    conv (copair (𝟙 a) (𝟙 a)) ≫ copair (𝟙 a) (𝟙 a) = 𝟙 a
  /-- The zero object: initial, hence — through `conv` — terminal too. -/
  zero : Word O
  toZero (a : Word O) : a ⟶ zero
  toZero_uniq {a : Word O} (X : a ⟶ zero) : X = toZero a
  /-- The zero arrow is the bottom of every hom order. -/
  bot_le {a b : Word O} (R : a ⟶ b) : (toZero a ≫ conv (toZero b)) ≤ R

namespace Biprod

variable {O : Type u} [Biprod.{v} O]

/-- `⟨R, S⟩`, the product's mediating arrow — the converse of a copairing.  `Rel` is self-dual, and
    this is where that is spent: the whole product half of the biproduct is one `conv`. -/
def pair {a b c : Word O} (R : c ⟶ a) (S : c ⟶ b) : c ⟶ sum a b :=
  conv (copair (conv R) (conv S))

/-- `R ∪ S = ⟨R, S⟩ [𝟙, 𝟙]`: offer both, then forget which was taken. -/
def union {a b : Word O} (R S : a ⟶ b) : a ⟶ b := pair R S ≫ copair (𝟙 b) (𝟙 b)

/-- `⊥`, the zero arrow, routed through the zero object. -/
def bot (a b : Word O) : a ⟶ b := toZero a ≫ conv (toZero (O := O) b)

/-! ### The product half, for free through `conv` -/

theorem pair_conv_inl {a b c : Word O} (R : c ⟶ a) (S : c ⟶ b) :
    pair R S ≫ conv (inl a b) = R := by
  dsimp [pair]; rw [← conv_comp, inl_copair, conv_conv]

theorem pair_conv_inr {a b c : Word O} (R : c ⟶ a) (S : c ⟶ b) :
    pair R S ≫ conv (inr a b) = S := by
  dsimp [pair]; rw [← conv_comp, inr_copair, conv_conv]

/-- The projections are jointly monic — `copair_uniq` read through `conv`. -/
theorem pair_uniq {a b c : Word O} {X Y : c ⟶ sum a b}
    (hl : X ≫ conv (inl a b) = Y ≫ conv (inl a b))
    (hr : X ≫ conv (inr a b) = Y ≫ conv (inr a b)) : X = Y := by
  have hc : conv X = conv Y := by
    refine copair_uniq ?_ ?_
    · have h := congrArg conv hl; rwa [conv_comp, conv_comp, conv_conv] at h
    · have h := congrArg conv hr; rwa [conv_comp, conv_comp, conv_conv] at h
  have h := congrArg conv hc; rwa [conv_conv, conv_conv] at h

theorem comp_pair {a b c d : Word O} (X : d ⟶ c) (R : c ⟶ a) (S : c ⟶ b) :
    X ≫ pair R S = pair (X ≫ R) (X ≫ S) := by
  refine pair_uniq ?_ ?_
  · rw [Cat.assoc, pair_conv_inl, pair_conv_inl]
  · rw [Cat.assoc, pair_conv_inr, pair_conv_inr]

theorem copair_comp {a b c d : Word O} (R : a ⟶ c) (S : b ⟶ c) (W : c ⟶ d) :
    copair R S ≫ W = copair (R ≫ W) (S ≫ W) := by
  refine copair_uniq ?_ ?_
  · rw [← Cat.assoc, inl_copair, inl_copair]
  · rw [← Cat.assoc, inr_copair, inr_copair]

theorem pair_mono {a b c : Word O} {R R' : c ⟶ a} {S S' : c ⟶ b} (hR : R ≤ R') (hS : S ≤ S') :
    pair R S ≤ pair R' S' :=
  conv_mono (copair_mono (conv_mono hR) (conv_mono hS))

/-! ### `∪` is the join

Everything below this point is lattice theory: once `∪` is shown to be the least upper bound of the
hom order — of which `∩` is already the greatest lower bound (`meet_glb`, `diag/CB_Derived.lean`) —
idempotence, commutativity, associativity, both absorption laws and `⊥ ∪ R = R` are consequences,
not eleven separate diagram derivations. -/

theorem pair_id_id (a : Word O) : pair (𝟙 a) (𝟙 a) = conv (copair (𝟙 a) (𝟙 a)) := by
  dsimp [pair]; rw [conv_id]

theorem union_idem {a b : Word O} (R : a ⟶ b) : union R R = R := by
  have h : pair R R = R ≫ pair (𝟙 b) (𝟙 b) := by rw [comp_pair, Cat.comp_id]
  dsimp [union]
  rw [h, Cat.assoc, pair_id_id, diag_codiag, Cat.comp_id]

/-- Half of `𝟙 = ⟨inl, inr⟩`: the left projection is below the codiagonal.  This is the one step
    that spends `conv_inl_le`, i.e. that the injection is injective. -/
theorem «conv_inl_≤_codiag» (b : Word O) : conv (inl b b) ≤ copair (𝟙 b) (𝟙 b) := by
  have h := OrderedCat.comp_mono (conv_inl_le b b) (OrderedCat.«≤_refl» (copair (𝟙 b) (𝟙 b)))
  rwa [Cat.assoc, inl_copair, Cat.comp_id, Cat.id_comp] at h

theorem «conv_inr_≤_codiag» (b : Word O) : conv (inr b b) ≤ copair (𝟙 b) (𝟙 b) := by
  have h := OrderedCat.comp_mono (conv_inr_le b b) (OrderedCat.«≤_refl» (copair (𝟙 b) (𝟙 b)))
  rwa [Cat.assoc, inr_copair, Cat.comp_id, Cat.id_comp] at h

theorem «≤_union_left» {a b : Word O} (R S : a ⟶ b) : R ≤ union R S := by
  have h := OrderedCat.comp_mono (OrderedCat.«≤_refl» (pair R S)) («conv_inl_≤_codiag» b)
  rwa [pair_conv_inl] at h

theorem «≤_union_right» {a b : Word O} (R S : a ⟶ b) : S ≤ union R S := by
  have h := OrderedCat.comp_mono (OrderedCat.«≤_refl» (pair R S)) («conv_inr_≤_codiag» b)
  rwa [pair_conv_inr] at h

theorem «union_≤» {a b : Word O} {R S T : a ⟶ b} (hR : R ≤ T) (hS : S ≤ T) : union R S ≤ T := by
  have h : union R S ≤ union T T :=
    OrderedCat.comp_mono (pair_mono hR hS) (OrderedCat.«≤_refl» _)
  rwa [union_idem] at h

theorem union_mono {a b : Word O} {R R' S S' : a ⟶ b} (hR : R ≤ R') (hS : S ≤ S') :
    union R S ≤ union R' S' :=
  «union_≤» (OrderedCat.«≤_trans» hR («≤_union_left» R' S'))
    (OrderedCat.«≤_trans» hS («≤_union_right» R' S'))

theorem union_comm {a b : Word O} (R S : a ⟶ b) : union R S = union S R :=
  OrderedCat.«≤_antisymm» («union_≤» («≤_union_right» S R) («≤_union_left» S R))
    («union_≤» («≤_union_right» R S) («≤_union_left» R S))

theorem union_assoc {a b : Word O} (R S T : a ⟶ b) :
    union R (union S T) = union (union R S) T := by
  refine OrderedCat.«≤_antisymm» («union_≤» ?_ ?_) («union_≤» ?_ ?_)
  · exact OrderedCat.«≤_trans» («≤_union_left» R S) («≤_union_left» _ T)
  · exact «union_≤» (OrderedCat.«≤_trans» («≤_union_right» R S) («≤_union_left» _ T))
      («≤_union_right» _ T)
  · exact «union_≤» («≤_union_left» R _)
      (OrderedCat.«≤_trans» («≤_union_left» S T) («≤_union_right» R _))
  · exact OrderedCat.«≤_trans» («≤_union_right» S T) («≤_union_right» R _)

/-! ### `∪` against `∩`, `≫`, `°` and `⊥` -/

theorem union_meet_absorb {a b : Word O} (R S : a ⟶ b) : union R (meet S R) = R :=
  OrderedCat.«≤_antisymm» («union_≤» (OrderedCat.«≤_refl» R) («meet_≤_right» S R))
    («≤_union_left» R (meet S R))

theorem meet_union_absorb {a b : Word O} (R S : a ⟶ b) : meet (union R S) R = R :=
  OrderedCat.«≤_antisymm» («meet_≤_right» (union R S) R)
    (meet_glb («≤_union_left» R S) (OrderedCat.«≤_refl» R))

theorem bot_union {a b : Word O} (R : a ⟶ b) : union (bot a b) R = R :=
  OrderedCat.«≤_antisymm» («union_≤» (bot_le R) (OrderedCat.«≤_refl» R))
    («≤_union_right» (bot a b) R)

theorem comp_union {a b c : Word O} (R : a ⟶ b) (S T : b ⟶ c) :
    R ≫ union S T = union (R ≫ S) (R ≫ T) := by
  dsimp [union]; rw [← Cat.assoc, comp_pair]

theorem conv_union {a b : Word O} (R S : a ⟶ b) :
    conv (union R S) = union (conv R) (conv S) := by
  refine OrderedCat.«≤_antisymm» ?_ («union_≤» (conv_mono («≤_union_left» R S))
    (conv_mono («≤_union_right» R S)))
  have h : union R S ≤ conv (union (conv R) (conv S)) := by
    refine «union_≤» ?_ ?_
    · have := conv_mono («≤_union_left» (conv R) (conv S)); rwa [conv_conv] at this
    · have := conv_mono («≤_union_right» (conv R) (conv S)); rwa [conv_conv] at this
  have := conv_mono h; rwa [conv_conv] at this

theorem union_comp {a b c : Word O} (R S : a ⟶ b) (T : b ⟶ c) :
    union R S ≫ T = union (R ≫ T) (S ≫ T) := by
  have h : conv (union R S ≫ T) = conv (union (R ≫ T) (S ≫ T)) := by
    rw [conv_comp, conv_union, conv_union, comp_union, conv_comp, conv_comp]
  have := congrArg conv h; rwa [conv_conv, conv_conv] at this

theorem bot_comp {a b c : Word O} (R : b ⟶ c) : bot a b ≫ R = bot a c := by
  have h : conv R ≫ toZero (O := O) b = toZero (O := O) c := toZero_uniq _
  have h' := congrArg conv h
  rw [conv_comp, conv_conv] at h'
  dsimp [bot]
  rw [Cat.assoc, h']

theorem conv_bot (a b : Word O) : conv (bot a b) = bot b a := by
  dsimp [bot]; rw [conv_comp, conv_conv]

theorem comp_bot {a b c : Word O} (R : a ⟶ b) : R ≫ bot b c = bot a c := by
  have h : conv (R ≫ bot b c) = conv (bot a c) := by
    rw [conv_comp, conv_bot, conv_bot, bot_comp]
  have := congrArg conv h; rwa [conv_conv, conv_conv] at this

end Biprod

/-! ### The rig: `⊗` distributes over `⊕`

The one axiom the biproduct alone does not give.  `∩` is `◁;(R ⊗ S);▷`, so `R ∩ (S ∪ T)` reduces to
`(R ∩ S) ∪ (R ∩ T)` exactly when `⊗` carries `∪` through — which is what makes the two structures a
RIG rather than two unrelated monoidal products.  `TapeDiagrams.pdf` Def. 7.1 packages it as the
distributors of a rig category; here it is stated where it is used. -/

open Biprod in
/-- A cartesian bicategory of relations with a biproduct that its tensor distributes over. -/
class FbCbRig (O : Type u) extends Biprod.{v} O where
  tensHom_union {a a' b b' : Word O} (R : a ⟶ a') (S T : b ⟶ b') :
    (R ⊗ₕ union S T) = union (R ⊗ₕ S) (R ⊗ₕ T)

namespace FbCbRig

open Biprod

variable {O : Type u} [FbCbRig.{v} O]

/-- The distributive law, `R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)`.  `∩` is `◁;(R ⊗ −);▷`, so this is
    `tensHom_union` with a copy in front and a merge behind, and the two composition-distributes-over-
    union laws carry `∪` past each. -/
theorem meet_union_distrib {a b : Word O} (R S T : a ⟶ b) :
    meet R (union S T) = union (meet R S) (meet R T) := by
  dsimp [meet]
  rw [tensHom_union, union_comp, comp_union]

/-- **Every fb-cb rig category is a distributive allegory.**  `∪ := union`, `𝟘 := bot`; the
    `Allegory` half is phase 5's `allegoryOfCartBicat`, so this file supplies only the six laws
    that mention `∪` or `𝟘`.

    A `def`, NOT a global instance — the same precedent as `allegoryOfCartBicat`. -/
def distributiveAllegoryOfFbCb (O : Type u) [FbCbRig.{v} O] :
    Freyd.Alg.DistributiveAllegory (Word O) :=
  { allegoryOfCartBicat O with
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
