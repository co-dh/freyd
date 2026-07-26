/-
  `diag.FO` — the fo layer: a second composition, linear adjoints, and residuals.

  Phase 9 of `diag/PLAN.md`, from `DiagrammaticAlgebraOfFirstOrderLogic.pdf` §5–6.

  WHY THERE IS A SECOND COMPOSITION.  Everything in `diag/CB.lean` and `diag/Tape.lean` is
  monotone: `≫`, `⊗`, `∩`, `∪` all preserve `≤` in every hole.  Division does not — `R / S` is
  ANTITONE in `S` — so no combinator built from those generators can be it.  The paper's way out is
  not to add a division box but to add a second composition `⨟•` alongside `⨟°` (Def. 5.1) together
  with an order-reversing `(−)⊥` (Def. 5.5); the residual is then the composite `R ⨟• S⊥`, monotone
  in `R` and antitone in `S` because `(−)⊥` is.

  WHAT `⨟•` IS.  In `Rel(Set)`, `⨟°` is the usual `∃`-composition and `⨟•` is its de Morgan dual,
  `(R ⨟• S) x z := ∀ y, R x y ∨ S y z`; the black identity `id•` is the INEQUALITY relation, not
  the identity, and `R⊥` is the complement of the converse.  `diag/RelSetFO.lean` carries that
  instance — and, because complement is `¬`, it is the one file in `diag/` that uses
  `Classical.choice`.  Everything in THIS file needs NO axioms at all — not even `propext`, because
  Lemma 5.4 and the residual are pure inequational rewriting.

  WHAT IS ASSUMED, AND WHY THIS PRESENTATION.  Definition 5.1 defines a linear bicategory (two
  poset enriched categories sharing objects, arrows and order, with `⨟°` linearly distributing over
  `⨟•`) and then a SYMMETRIC MONOIDAL linear bicategory on top (a second tensor `⊗•`, its own
  associators/unitors/symmetry, linear strengths, and the two `id`-preservation inequations).  The
  results phase 9 actually wants — Lemma 5.4 and the residual — consume only the first half: their
  proofs are four rewrites with `δ_l`/`δ_r` and the two unit laws, and never mention a tensor.  So
  `LinearBicat` below is Def. 5.1's linear-bicategory half alone, and the monoidal half is added
  where it is first needed, in `MonLinearBicat` (Def. 5.1.1–2) for `CocartBicat` and `FOBicat`.
  Same trade, and the same reason, as `diag/Tape.lean`'s biproduct: state the coherence where a
  proof consumes it, not one layer earlier.

  A DEAD END WORTH RECORDING.  The paper says Fig. 3 (cocartesian bicategories) "can also be
  obtained from Fig. 2 by inverting both the colours and the order", which invites defining
  `CocartBicat 𝒞 := CartBicat (Co 𝒞)` for a type synonym `Co 𝒞` carrying `⨟•` and `≥`, and getting
  every Fig. 3 law plus all of `diag/CB_Derived.lean` for free.  It does not work here: `CartBicat`
  `extends SymMonCat extends OrderedCat extends Cat`, so `CartBicat (Co 𝒞)` supplies its OWN
  `Cat (Co 𝒞)` — in particular its own `Hom` — whereas Def. 5.1 requires the two structures to have
  literally the same arrows.  Forcing that agreement needs either an equality of `Hom` types as a
  field or unbundling `CartBicat`'s parents into instance arguments, and both cost more than the
  transcription saves.  The black composition is therefore a FIELD on `𝒞`, not a second `Cat`.
-/
import diag.CB_Derived

universe v u

namespace Freyd.Diag

open Freyd
open scoped SymMonCat

/-! ### Definition 5.1 — the linear bicategory -/

/-- A LINEAR BICATEGORY (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` Def. 5.1): two poset enriched
    categories with THE SAME objects, arrows and ordering but different identities and
    compositions, the white `(⨟°, id°)` — which is `Cat`'s own `≫` and `𝟙` — and the black
    `(⨟•, id•)`, such that `⨟°` linearly distributes over `⨟•`.

    Note what is NOT here: `id•` is not required to be `𝟙`, and `⨟•` is not required to agree with
    `≫` anywhere.  In `Rel(Set)` they are as different as `∃` and `∀`. -/
class LinearBicat (𝒞 : Type u) extends OrderedCat.{v} 𝒞 where
  /-- `id•_a`, the black identity.  In `Rel(Set)` this is the INEQUALITY relation. -/
  bid (a : 𝒞) : a ⟶ a
  /-- `⨟•`, the black composition. -/
  bcomp {a b c : 𝒞} (R : a ⟶ b) (S : b ⟶ c) : a ⟶ c
  bid_bcomp {a b : 𝒞} (R : a ⟶ b) : bcomp (bid a) R = R
  bcomp_bid {a b : 𝒞} (R : a ⟶ b) : bcomp R (bid b) = R
  bcomp_assoc {a b c d : 𝒞} (R : a ⟶ b) (S : b ⟶ c) (T : c ⟶ d) :
    bcomp (bcomp R S) T = bcomp R (bcomp S T)
  /-- Poset enrichment of the black composition — "the same … orderings". -/
  bcomp_mono {a b c : 𝒞} {R R' : a ⟶ b} {S S' : b ⟶ c} :
    R ≤ R' → S ≤ S' → bcomp R S ≤ bcomp R' S'
  /-- (δ_l), Fig. 4: `c ⨟° (d ⨟• e) ≤ (c ⨟° d) ⨟• e`.  Linear distributivity — this and (δ_r) are
      the ONLY laws relating the two compositions, and are what makes the pair a linear bicategory
      rather than two unrelated categories on the same arrows. -/
  linDistrib_left {a b c d : 𝒞} (R : a ⟶ b) (S : b ⟶ c) (T : c ⟶ d) :
    (R ≫ bcomp S T) ≤ bcomp (R ≫ S) T
  /-- (δ_r), Fig. 4: `(c ⨟• d) ⨟° e ≤ c ⨟• (d ⨟° e)`. -/
  linDistrib_right {a b c d : 𝒞} (R : a ⟶ b) (S : b ⟶ c) (T : c ⟶ d) :
    (bcomp R S ≫ T) ≤ bcomp R (S ≫ T)

namespace LinearBicat

variable {𝒞 : Type u} [LinearBicat.{v} 𝒞]

@[inherit_doc] scoped infixr:80 " ≫• " => LinearBicat.bcomp
/-- The black identity `id•_a`, written to mirror the book's `𝟙 a` for `id°`. -/
scoped notation:max "𝟙•" a:max => LinearBicat.bid a

/-! ### Linear adjoints (p. 7, before Def. 5.5) -/

/-- `S` is a RIGHT LINEAR ADJOINT of `R`, the paper's `S ⊪ R`
    (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` p. 7): `id°_a ≤ R ⨟• S` and `S ⨟° R ≤ id•_b`.

    Read as an adjunction whose unit lands in the BLACK composite and whose counit leaves the WHITE
    one: that mismatch is the whole point, and is why a linear adjoint reverses the order
    (`perp_mono` below) while an ordinary one does not. -/
structure RightLinAdj {a b : 𝒞} (R : a ⟶ b) (S : b ⟶ a) : Prop where
  /-- The unit, `id°_a ≤ R ⨟• S`. -/
  unit : (𝟙 a) ≤ (R ≫• S)
  /-- The counit, `S ⨟° R ≤ id•_b`. -/
  counit : (S ≫ R) ≤ (𝟙• b)

/-- **Lemma 5.3**: a right linear adjoint is unique.  `S' = S' ⨟° id° ≤ S' ⨟° (R ⨟• S)` by the
    unit, `≤ (S' ⨟° R) ⨟• S` by (δ_l), `≤ id• ⨟• S = S` by the other counit — the ordinary
    two-adjunctions argument, with the two compositions doing one job each. -/
theorem lemma_5_3_uniq {a b : 𝒞} {R : a ⟶ b} {S S' : b ⟶ a}
    (h : RightLinAdj R S) (h' : RightLinAdj R S') : S = S' := by
  have key : ∀ {T T' : b ⟶ a}, RightLinAdj R T → RightLinAdj R T' → T' ≤ T := by
    intro T T' hT hT'
    have h1 : T' ≤ (T' ≫ (R ≫• T)) := by
      have := OrderedCat.comp_mono (OrderedCat.le_refl T') hT.unit
      rwa [Cat.comp_id] at this
    have h2 : (T' ≫ (R ≫• T)) ≤ ((T' ≫ R) ≫• T) := linDistrib_left _ _ _
    have h3 : ((T' ≫ R) ≫• T) ≤ ((𝟙• b) ≫• T) := bcomp_mono hT'.counit (OrderedCat.le_refl T)
    rw [bid_bcomp] at h3
    exact OrderedCat.le_trans h1 (OrderedCat.le_trans h2 h3)
  exact OrderedCat.le_antisymm (key h' h) (key h h')

end LinearBicat

/-! ### Definition 5.5 — closedness -/

open LinearBicat in
/-- A CLOSED linear bicategory (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` Def. 5.5): every arrow
    has both a left and a right linear adjoint.  `perp R` is the paper's `R⊥`, THE right linear
    adjoint (unique by `lemma_5_3_uniq`); `lperp R` is the left one, i.e. the arrow of which `R` is
    the right linear adjoint.

    Def. 5.5 additionally requires the white symmetry to be both left and right linear adjoint to
    the black symmetry — (τσ°), (γσ°), (τσ•), (γσ•) of Fig. 4.  That clause needs both tensors, so
    it is `swap_linAdj` in `MonLinearBicat` below; nothing before that point can even state it. -/
class ClosedLinearBicat (𝒞 : Type u) extends LinearBicat.{v} 𝒞 where
  /-- `R⊥`, the right linear adjoint. -/
  perp {a b : 𝒞} (R : a ⟶ b) : b ⟶ a
  perp_adj {a b : 𝒞} (R : a ⟶ b) : RightLinAdj R (perp R)
  /-- The left linear adjoint.  In `Rel` it coincides with `perp` (paper p. 7, "in the categories
      of interest left and right linear adjoint coincide"), but Def. 5.5 asks only that both
      exist. -/
  lperp {a b : 𝒞} (R : a ⟶ b) : b ⟶ a
  lperp_adj {a b : 𝒞} (R : a ⟶ b) : RightLinAdj (lperp R) R

namespace ClosedLinearBicat

open LinearBicat

variable {𝒞 : Type u} [ClosedLinearBicat.{v} 𝒞]

/-! ### The residual

The paper (p. 7): "one can write the LEFT RESIDUAL of `b : Z → Y` by `a : X → Y` as `b ⨟• a⊥`.  The
left residual is the greatest arrow `Z → X` making the diagram commute laxly in `C°`, namely if
`c ⨟° a ≤ b` then `c ≤ b ⨟• a⊥`."  `le_residual_iff` is that sentence, both directions; it is the
same Galois connection Freyd's `le_div_iff` (`Freyd/S2_30.lean`) states for `R / S`, which is what
lets `diag/RelSetFO.lean` identify the two without unfolding either.

Lemma 5.4 is that connection at `T := id°`, so it comes after it rather than before: the paper
states the lemma first and reads the residual off it, but here the general statement is the one
carrying the calculation and the lemma is its instance. -/

/-- The LEFT RESIDUAL of `R : Z ⟶ Y` by `S : X ⟶ Y`
    (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` p. 7): `R ⨟• S⊥`. -/
def residual {X Y Z : 𝒞} (R : Z ⟶ Y) (S : X ⟶ Y) : Z ⟶ X := R ≫• perp S

/-- The residual's universal property: `T ⨟° S ≤ R` iff `T ≤ R ⨟• S⊥`.  Freyd writes the same
    adjunction as `le_div_iff` for `R / S` (`Freyd/S2_30.lean`).

    The one calculation this layer exists for.  Forwards weakens `T` by the unit of `S ⊣ S⊥` and
    reassociates with (δ_l).  Backwards is
    `T ⨟° S ≤ (R ⨟• S⊥) ⨟° S ≤ R ⨟• (S⊥ ⨟° S) ≤ R ⨟• id• = R`, whose middle step is (δ_r) — the
    ONLY place the two compositions meet. -/
theorem le_residual_iff {X Y Z : 𝒞} (T : Z ⟶ X) (R : Z ⟶ Y) (S : X ⟶ Y) :
    (T ≫ S) ≤ R ↔ T ≤ residual R S := by
  constructor
  · intro h
    have h1 : T ≤ (T ≫ (S ≫• perp S)) := by
      have := OrderedCat.comp_mono (OrderedCat.le_refl T) (perp_adj S).unit
      rwa [Cat.comp_id] at this
    exact OrderedCat.le_trans h1
      (OrderedCat.le_trans (linDistrib_left _ _ _) (bcomp_mono h (OrderedCat.le_refl _)))
  · intro h
    have h1 : (T ≫ S) ≤ ((R ≫• perp S) ≫ S) :=
      OrderedCat.comp_mono h (OrderedCat.le_refl S)
    have h2 : ((R ≫• perp S) ≫ S) ≤ (R ≫• (perp S ≫ S)) := linDistrib_right _ _ _
    have h3 : (R ≫• (perp S ≫ S)) ≤ (R ≫• (𝟙• Y)) :=
      bcomp_mono (OrderedCat.le_refl R) (perp_adj S).counit
    rw [bcomp_bid] at h3
    exact OrderedCat.le_trans h1 (OrderedCat.le_trans h2 h3)

/-- `T ⨟° S ≤ R` at `T := R ⨟• S⊥`: the residual is a lower bound of the arrows it is the greatest
    of.  Freyd's `div_comp_le`. -/
theorem residual_comp_le {X Y Z : 𝒞} (R : Z ⟶ Y) (S : X ⟶ Y) : (residual R S ≫ S) ≤ R :=
  (le_residual_iff _ R S).mpr (OrderedCat.le_refl _)

/-- The residual is MONOTONE in the numerator and ANTITONE in the denominator — the variance no
    combinator of `diag/CB.lean`'s monotone generators could have had, and the reason this layer
    exists.  Antitonicity is the denominator standing on the SMALL side of the universal property:
    shrinking `S` weakens the hypothesis `T ⨟° S ≤ R`, so it admits more `T`. -/
theorem residual_mono {X Y Z : 𝒞} {R R' : Z ⟶ Y} {S S' : X ⟶ Y}
    (hR : R ≤ R') (hS : S' ≤ S) : residual R S ≤ residual R' S' :=
  (le_residual_iff _ _ _).mp
    (OrderedCat.le_trans (OrderedCat.comp_mono (OrderedCat.le_refl _) hS)
      (OrderedCat.le_trans (residual_comp_le R S) hR))

/-- **Lemma 5.4 (Residuation)** (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` §5):
    `a ≤ b` iff `id°_X ≤ b ⨟• a⊥`.

    Residuation at `T := id°`, since `id° ⨟° a` is `a`: the lemma is not a second argument but the
    same one read with the identity in the numerator. -/
theorem lemma_5_4_residuation {X Y : 𝒞} (a b : X ⟶ Y) :
    a ≤ b ↔ (𝟙 X) ≤ (b ≫• perp a) := by
  have h := le_residual_iff (𝟙 X) b a
  rw [Cat.id_comp] at h
  exact h

end ClosedLinearBicat

/-! ### Definition 5.1.1–2 — the monoidal half

Def. 5.1's second sentence: a SYMMETRIC MONOIDAL linear bicategory carries two poset enriched
symmetric monoidal structures `(C, ⊗, I)` and `(C, ⊗•, I)` that AGREE ON OBJECTS and share the unit
— so `⊗•` adds no object-level operation, only a second action on arrows with its own coherence
isos — plus (1) the four linear strengths and (2) the two `id`-preservation inequations.

The black structural isos really are separate arrows, not the white ones reused: in `Rel(Set)` the
black identity is the inequality relation, so an arrow is a black iso exactly when its COMPLEMENT
is a white one, and the black associator is the complement of the white associator. -/

open LinearBicat in
/-- A SYMMETRIC MONOIDAL LINEAR BICATEGORY (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` Def. 5.1,
    second half, with Fig. 4's (ν) and (⊗) inequations).

    The black monoidal fields mirror `SymMonCat`'s white ones one for one, with `≫•` for `≫`, `𝟙•`
    for `𝟙` and `⊗•ₕ` for `⊗ₕ` — which is exactly what "two symmetric monoidal categories on the
    same objects and arrows" means once the object level is shared. -/
class MonLinearBicat (𝒞 : Type u) extends SymMonCat.{v} 𝒞, LinearBicat.{v} 𝒞 where
  /-- `⊗•` on arrows.  Def. 5.1: `X ⊗ Y = X ⊗• Y`, so the object level is the white `⊗`. -/
  btensHom {a a' b b' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') : a ⊗ b ⟶ a' ⊗ b'
  btensHom_bid (a b : 𝒞) : btensHom (𝟙• a) (𝟙• b) = 𝟙• (a ⊗ b)
  btensHom_bcomp {a a' a'' b b' b'' : 𝒞} (R : a ⟶ a') (R' : a' ⟶ a'') (S : b ⟶ b') (S' : b' ⟶ b'') :
    btensHom (R ≫• R') (S ≫• S') = btensHom R S ≫• btensHom R' S'
  btensHom_mono {a a' b b' : 𝒞} {R R' : a ⟶ a'} {S S' : b ⟶ b'} :
    R ≤ R' → S ≤ S' → (btensHom R S) ≤ (btensHom R' S')

  /-- The black associator `α•`.  Invertible for `≫•`/`𝟙•`, not for `≫`/`𝟙`. -/
  bassoc (a b c : 𝒞) :
    (a ⊗ b) ⊗ c ⟶ a ⊗ (b ⊗ c)
  bassocInv (a b c : 𝒞) :
    a ⊗ (b ⊗ c) ⟶ (a ⊗ b) ⊗ c
  bassoc_inv (a b c : 𝒞) :
    bassoc a b c ≫• bassocInv a b c = 𝟙• ((a ⊗ b) ⊗ c)
  inv_bassoc (a b c : 𝒞) :
    bassocInv a b c ≫• bassoc a b c = 𝟙• (a ⊗ (b ⊗ c))
  bassoc_nat {a a' b b' c c' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') (T : c ⟶ c') :
    btensHom (btensHom R S) T ≫• bassoc a' b' c' = bassoc a b c ≫• btensHom R (btensHom S T)

  /-- The black left unitor `λ•`. -/
  blunit (a : 𝒞) : 𝕀 ⊗ a ⟶ a
  blunitInv (a : 𝒞) : a ⟶ 𝕀 ⊗ a
  blunit_inv (a : 𝒞) :
    blunit a ≫• blunitInv a = 𝟙• (𝕀 ⊗ a)
  inv_blunit (a : 𝒞) : blunitInv a ≫• blunit a = 𝟙• a
  blunit_nat {a b : 𝒞} (R : a ⟶ b) :
    btensHom (𝟙• 𝕀) R ≫• blunit b = blunit a ≫• R

  /-- The black right unitor `ρ•`. -/
  brunit (a : 𝒞) : a ⊗ 𝕀 ⟶ a
  brunitInv (a : 𝒞) : a ⟶ a ⊗ 𝕀
  brunit_inv (a : 𝒞) :
    brunit a ≫• brunitInv a = 𝟙• (a ⊗ 𝕀)
  inv_brunit (a : 𝒞) : brunitInv a ≫• brunit a = 𝟙• a
  brunit_nat {a b : 𝒞} (R : a ⟶ b) :
    btensHom R (𝟙• 𝕀) ≫• brunit b = brunit a ≫• R

  /-- The black symmetry `σ•`. -/
  bswap (a b : 𝒞) : a ⊗ b ⟶ b ⊗ a
  bswap_bswap (a b : 𝒞) : bswap a b ≫• bswap b a = 𝟙• (a ⊗ b)
  bswap_nat {a a' b b' : 𝒞} (R : a ⟶ a') (S : b ⟶ b') :
    btensHom R S ≫• bswap a' b' = bswap a b ≫• btensHom S R
  bswap_blunit (a : 𝒞) : bswap a 𝕀 ≫• blunit a = brunit a

  bpentagon (a b c d : 𝒞) :
    btensHom (bassoc a b c) (𝟙• d) ≫• bassoc a (b ⊗ c) d
        ≫• btensHom (𝟙• a) (bassoc b c d)
      = bassoc (a ⊗ b) c d ≫• bassoc a b (c ⊗ d)
  btriangle (a b : 𝒞) :
    bassoc a 𝕀 b ≫• btensHom (𝟙• a) (blunit b) = btensHom (brunit a) (𝟙• b)
  bhexagon (a b c : 𝒞) :
    bassoc a b c ≫• bswap a (b ⊗ c) ≫• bassoc b c a
      = btensHom (bswap a b) (𝟙• c) ≫• bassoc b a c ≫• btensHom (𝟙• b) (bswap a c)

  /-- (ν_l°), Fig. 4: `(a ⨟• b) ⊗ (c ⨟• d) ≤ (a ⊗ c) ⨟• (b ⊗• d)`.  The first of the four LINEAR
      STRENGTHS of Def. 5.1.1 — the pair `(⊗, ⊗•)` seen as a linear functor.  The paper notes
      (Remark 2) that the two `(⊗)` inequations below are, to its authors' knowledge, novel, and
      that all six are what Lemma 5.2 rests on. -/
  strength_lw {a b c a' b' c' : 𝒞} (R : a ⟶ b) (S : b ⟶ c) (T : a' ⟶ b') (U : b' ⟶ c') :
    (((R ≫• S) ⊗ₕ (T ≫• U)))
      ≤ ((R ⊗ₕ T) ≫• btensHom S U)
  /-- (ν_r°), Fig. 4: `(a ⨟• b) ⊗ (c ⨟• d) ≤ (a ⊗• c) ⨟• (b ⊗ d)`. -/
  strength_rw {a b c a' b' c' : 𝒞} (R : a ⟶ b) (S : b ⟶ c) (T : a' ⟶ b') (U : b' ⟶ c') :
    (((R ≫• S) ⊗ₕ (T ≫• U)))
      ≤ (btensHom R T ≫• (S ⊗ₕ U))
  /-- (ν_l•), Fig. 4: `(a ⊗• c) ⨟° (b ⊗ d) ≤ (a ⨟° b) ⊗• (c ⨟° d)`. -/
  strength_lb {a b c a' b' c' : 𝒞} (R : a ⟶ b) (S : b ⟶ c) (T : a' ⟶ b') (U : b' ⟶ c') :
    (btensHom R T ≫ (S ⊗ₕ U)) ≤ (btensHom (R ≫ S) (T ≫ U))
  /-- (ν_r•), Fig. 4: `(a ⊗ c) ⨟° (b ⊗• d) ≤ (a ⨟° b) ⊗• (c ⨟° d)`. -/
  strength_rb {a b c a' b' c' : 𝒞} (R : a ⟶ b) (S : b ⟶ c) (T : a' ⟶ b') (U : b' ⟶ c') :
    ((R ⊗ₕ T) ≫ btensHom S U) ≤ (btensHom (R ≫ S) (T ≫ U))

  /-- (⊗•), Fig. 4: `⊗` preserves `id•` LAXLY — `id•_X ⊗ id•_Y ≤ id•_{X⊗Y}` (Def. 5.1.2).  In
      `Rel(Set)`: `x ≠ y ∧ z ≠ w` implies `(x,z) ≠ (y,w)`, and not conversely. -/
  tens_bid_lax (a b : 𝒞) :
    ((𝟙• a ⊗ₕ 𝟙• b)) ≤ (𝟙• (a ⊗ b))
  /-- (⊗°), Fig. 4: `⊗•` preserves `id°` COLAXLY — `id°_{X⊗Y} ≤ id°_X ⊗• id°_Y` (Def. 5.1.2).  In
      `Rel(Set)`: `x = y ∧ z = w` implies `x = y ∨ z = w`. -/
  btens_id_colax (a b : 𝒞) :
    (𝟙 (a ⊗ b)) ≤ (btensHom (𝟙 a) (𝟙 b))

namespace MonLinearBicat

@[inherit_doc] scoped infixr:70 " ⊗•ₕ " => MonLinearBicat.btensHom

end MonLinearBicat

/-! ### Figure 3 — cocartesian bicategories

The paper (§4, p. 6): the axioms of cocartesian bicategories "can also be obtained from Fig. 2 by
inverting both the colours and the order".  Fig. 2 is `diag/CB.lean`'s `CartBicat` field for field,
so every field below is a `CartBicat` field with `≫` ↦ `≫•`, `𝟙` ↦ `𝟙•`, `⊗ₕ` ↦ `⊗•ₕ`, the white
structural isos ↦ the black ones, and every `≤` turned around.  The four generators keep the paper's
`◀•`, `!•`, `▶•`, `¡•` under the repo's diagram names, prefixed `b` for black.

NOT a field, for the same reason as in `diag/CB.lean`: Fig. 3's special law (S•), `◀•;•▶• = 𝟙•`.  It
is `bineq_38` one way and `bineq_39` plus the two unit laws the other, exactly as `CartBicat.special`
is derived from (38) and (40).  No proof here consumes it, so it is left underived rather than
stated. -/

open LinearBicat MonLinearBicat in
/-- A COCARTESIAN BICATEGORY (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` Fig. 3): `CartBicat` with
    the colours and the order inverted.  Read every field against the `CartBicat` field of the same
    name in `diag/CB.lean`. -/
class CocartBicat (𝒞 : Type u) extends MonLinearBicat.{v} 𝒞 where
  /-- `◀•`, the black comultiplication. -/
  bdelta (n : 𝒞) : n ⟶ n ⊗ n
  /-- `!•`, the black counit. -/
  bbang (n : 𝒞) : n ⟶ 𝕀
  /-- `▶•`, the black multiplication. -/
  bnabla (n : 𝒞) : n ⊗ n ⟶ n
  /-- `¡•`, the black unit. -/
  bunitR (n : 𝒞) : 𝕀 ⟶ n

  /-- (◀•-as), the mirror of `delta_assoc`. -/
  bdelta_assoc (n : 𝒞) :
    bdelta n ≫• (bdelta n ⊗•ₕ 𝟙• n) ≫• bassoc n n n = bdelta n ≫• (𝟙• n ⊗•ₕ bdelta n)
  /-- (◀•-co), the mirror of `delta_comm`. -/
  bdelta_comm (n : 𝒞) : bdelta n ≫• bswap n n = bdelta n
  /-- (◀•-un), the mirror of `delta_counit`. -/
  bdelta_counit (n : 𝒞) : bdelta n ≫• (𝟙• n ⊗•ₕ bbang n) ≫• brunit n = 𝟙• n

  /-- (▶•-as), the mirror of `nabla_assoc`. -/
  bnabla_assoc (n : 𝒞) :
    (bnabla n ⊗•ₕ 𝟙• n) ≫• bnabla n = bassoc n n n ≫• (𝟙• n ⊗•ₕ bnabla n) ≫• bnabla n
  /-- (▶•-co), the mirror of `nabla_comm`. -/
  bnabla_comm (n : 𝒞) : bswap n n ≫• bnabla n = bnabla n
  /-- (▶•-un), the mirror of `nabla_unit`. -/
  bnabla_unit (n : 𝒞) : brunitInv n ≫• (𝟙• n ⊗•ₕ bunitR n) ≫• bnabla n = 𝟙• n

  /-- (η▶•): `𝟙• ≤ ▶•;•◀•`, the mirror of (37) — the order is inverted, so the bubble is now ABOVE
      the identity.  This is precisely why `⊕` could not be a second `CartBicat` in
      `diag/Tape.lean`, and the same asymmetry surfaces here as the reason Fig. 3 is not Fig. 2. -/
  bineq_37 (n : 𝒞) : (𝟙• (n ⊗ n)) ≤ (bnabla n ≫• bdelta n)
  /-- (ε▶•): `◀•;•▶• ≤ 𝟙•`, the mirror of (38). -/
  bineq_38 (n : 𝒞) : (bdelta n ≫• bnabla n) ≤ (𝟙• n)
  /-- (η¡•), the mirror of (39). -/
  bineq_39 (n : 𝒞) :
    (𝟙• (𝕀 : 𝒞)) ≤ (bunitR n ≫• bbang n)
  /-- (ε¡•), the mirror of (40). -/
  bineq_40 (n : 𝒞) : (bbang n ≫• bunitR n) ≤ (𝟙• n)

  /-- (F•), the mirror of `frob_left`. -/
  bfrob_left (n : 𝒞) :
    (𝟙• n ⊗•ₕ bdelta n) ≫• bassocInv n n n ≫• (bnabla n ⊗•ₕ 𝟙• n) = bnabla n ≫• bdelta n
  /-- (F•), the mirror of `frob_right`. -/
  bfrob_right (n : 𝒞) :
    (bdelta n ⊗•ₕ 𝟙• n) ≫• bassoc n n n ≫• (𝟙• n ⊗•ₕ bnabla n) = bnabla n ≫• bdelta n

  /-- (◀•-nat), the mirror of `lax_delta`: every arrow is a COLAX black comonoid homomorphism. -/
  blax_delta {m n : 𝒞} (R : m ⟶ n) : (bdelta m ≫• (R ⊗•ₕ R)) ≤ (R ≫• bdelta n)
  /-- (!•-nat), the mirror of `lax_bang`. -/
  blax_bang {m n : 𝒞} (R : m ⟶ n) : (bbang m) ≤ (R ≫• bbang n)

/-! ### Definition 6.1 — first order bicategories

`DiagrammaticAlgebraOfFirstOrderLogic.pdf` Def. 6.1, itemised exactly as printed:

  1. a closed linear bicategory `(C, ⊗, ⊗•, I)`   — `ClosedLinearBicat` + `MonLinearBicat`, plus
                                                    Def. 5.5's symmetry clause, `swap_linAdj` below
  2. a cartesian bicategory `(C, ⊗, I, ◀°, !°, ▶°, ¡°)`      — `CartBicat`
  3. a cocartesian bicategory `(C, ⊗•, I, ◀•, !•, ▶•, ¡•)`   — `CocartBicat`
  4. the white comonoid `(◀°, !°)` is left AND right linear adjoint to the black monoid `(▶•, ¡•)`,
     and `(▶°, ¡°)` is left and right linear adjoint to `(◀•, !•)` — the sixteen inequalities on the
     left of Fig. 5, packaged as eight `RightLinAdj`s
  5. the white and black (co)monoids satisfy the LINEAR FROBENIUS laws — the four equalities on the
     right of Fig. 5.

Deliberately NOT attempted here, per `diag/PLAN.md`'s open problems: any statement equating
fo-bicategories with division or Peirce allegories.  `DiagrammaticAlgebraOfFirstOrderLogic.pdf` §10
only *suggests* the connection to Peirce allegories, and the cartesian-bicategory ↔ unitary
pretabular allegory correspondence it does cite is not that statement. -/

open LinearBicat MonLinearBicat CartBicat CocartBicat in
/-- A FIRST ORDER BICATEGORY (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` Def. 6.1). -/
class FOBicat (𝒞 : Type u) extends
    CocartBicat.{v} 𝒞, CartBicat.{v} 𝒞, ClosedLinearBicat.{v} 𝒞 where
  /-- Def. 5.5's remaining clause, hence part of Def. 6.1.1: the white symmetry is LEFT linear
      adjoint to the black one — (τσ°) and (γσ°) of Fig. 4. -/
  swap_linAdj (a b : 𝒞) :
    RightLinAdj (SymMonCat.swap a b) (bswap b a)
  /-- Def. 5.5, continued: and RIGHT linear adjoint to it — (τσ•) and (γσ•). -/
  bswap_linAdj (a b : 𝒞) :
    RightLinAdj (bswap a b) (SymMonCat.swap b a)

  /-- Def. 6.1.4, (τ◀°)/(γ◀°): `◀°` is left linear adjoint to `▶•`. -/
  delta_linAdj (n : 𝒞) : RightLinAdj (CartBicat.delta n) (CocartBicat.bnabla n)
  /-- (τ!°)/(γ!°): `!°` is left linear adjoint to `¡•`. -/
  bang_linAdj (n : 𝒞) : RightLinAdj (CartBicat.bang n) (CocartBicat.bunitR n)
  /-- (τ▶°)/(γ▶°): `▶°` is left linear adjoint to `◀•`. -/
  nabla_linAdj (n : 𝒞) : RightLinAdj (CartBicat.nabla n) (CocartBicat.bdelta n)
  /-- (τ¡°)/(γ¡°): `¡°` is left linear adjoint to `!•`. -/
  unitR_linAdj (n : 𝒞) : RightLinAdj (CartBicat.unitR n) (CocartBicat.bbang n)
  /-- (τ◀•)/(γ◀•): `◀•` is left linear adjoint to `▶°` — the "and right" half of Def. 6.1.4. -/
  bdelta_linAdj (n : 𝒞) : RightLinAdj (CocartBicat.bdelta n) (CartBicat.nabla n)
  /-- (τ!•)/(γ!•): `!•` is left linear adjoint to `¡°`. -/
  bbang_linAdj (n : 𝒞) : RightLinAdj (CocartBicat.bbang n) (CartBicat.unitR n)
  /-- (τ▶•)/(γ▶•): `▶•` is left linear adjoint to `◀°`. -/
  bnabla_linAdj (n : 𝒞) : RightLinAdj (CocartBicat.bnabla n) (CartBicat.delta n)
  /-- (τ¡•)/(γ¡•): `¡•` is left linear adjoint to `!°`. -/
  bunitR_linAdj (n : 𝒞) : RightLinAdj (CocartBicat.bunitR n) (CartBicat.bang n)

  /-- Def. 6.1.5, `(F^•_∘)`: the LINEAR FROBENIUS law in the white structure, with the black
      comultiplication copying and the white multiplication merging.  Compare `frob_right`: the
      shape is the same, one dot each has changed colour.

      Fig. 5 tells its four Frobenius laws apart by WHERE the two colour marks sit, not just by
      their order — `(F^•_∘)`, `(F^°_•)`, `(F_•^°)`, `(F_∘^•)` — and `°` and `∘` are the same glyph,
      so dropping the sub/superscript positions makes two pairs of labels collide.  Keep them. -/
  linfrob_bw (n : 𝒞) :
    (bdelta n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ nabla n)
      = (𝟙 n ⊗ₕ delta n) ≫ SymMonCat.tensAssocInv n n n ≫ (bnabla n ⊗ₕ 𝟙 n)
  /-- `(F^°_•)`: the mirror of `linfrob_bw`, white copying and black merging. -/
  linfrob_wb (n : 𝒞) :
    (delta n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ bnabla n)
      = (𝟙 n ⊗ₕ bdelta n) ≫ SymMonCat.tensAssocInv n n n ≫ (nabla n ⊗ₕ 𝟙 n)
  /-- `(F_•^°)`: `linfrob_wb` said in the BLACK structure — same four generators, `⨟•`/`⊗•`/`α•`
      for `⨟°`/`⊗`/`α`.  Its `Rel(Set)` proof is nonetheless the COMPLEMENT of `linfrob_bw`'s,
      because complementing swaps the generators' colours as well as the composition's. -/
  blinfrob_wb (n : 𝒞) :
    (delta n ⊗•ₕ 𝟙• n) ≫• bassoc n n n ≫• (𝟙• n ⊗•ₕ bnabla n)
      = (𝟙• n ⊗•ₕ bdelta n) ≫• bassocInv n n n ≫• (nabla n ⊗•ₕ 𝟙• n)
  /-- `(F_∘^•)`: `linfrob_bw` said in the black structure. -/
  blinfrob_bw (n : 𝒞) :
    (bdelta n ⊗•ₕ 𝟙• n) ≫• bassoc n n n ≫• (𝟙• n ⊗•ₕ nabla n)
      = (𝟙• n ⊗•ₕ delta n) ≫• bassocInv n n n ≫• (bnabla n ⊗•ₕ 𝟙• n)

end Freyd.Diag
