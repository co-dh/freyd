/-
  `diag.RelSetFO` — SOUNDNESS for phase 9: `Rel(Set)` is a closed linear bicategory, and the fo
  layer's residual is the repo's own division.

  ⚠ **THE CLASSICAL FILE.**  This is the ONE place in `diag/` where `Classical.choice` appears, and
  it is unavoidable rather than incidental: `DiagrammaticAlgebraOfFirstOrderLogic.pdf` p. 7 fixes
  the linear adjoint of a relation as `R⊥ = {(y,x) | (x,y) ∉ R}`, so the axiom `id° ≤ R ⨟• R⊥` IS
  excluded middle at `R x y`, and the black identity's unit law is decidability of equality.  Every
  declaration in `diag/FO.lean` depends on NO axioms at all; every `instance` below is
  `[propext, Classical.choice, Quot.sound]`, and `Freyd/S2_30.lean`'s constructive `div`
  (`AOP/A6_1_RelSet.lean`, a direct `∀`) remains the canonical division for AOP work.

  THE DICTIONARY, all three de Morgan duals of the white structure:

      id•_a x y   ↔  x ≠ y                    the INEQUALITY relation, not the identity
      (R ⨟• S) x z ↔ ∀ y, R x y ∨ S y z       `∀`/`∨` where `≫` has `∃`/`∧`
      R⊥ y x      ↔  ¬ R x y                  the complement of the converse

  `residual_eq_div` is the payoff: `R ⨟• S⊥` and `R / S` are proved equal WITHOUT unfolding either,
  purely because they satisfy the same Galois connection (`«≤_residual_iff»` and `le_div_iff`) and
  the hom order is a partial order.
-/
import diag.FO
import diag.RelSetCB
import Freyd.S2_30

universe u

namespace Freyd.Diag

open Freyd
open Freyd.Alg
open LinearBicat
open scoped SymMonCat

/-- `⨟•` on `Rel(Set)`: the de Morgan dual of composition — `∀`/`∨` where `≫` has `∃`/`∧`. -/
def relBcomp {a b c : RelSet.{u}} (R : a ⟶ b) (S : b ⟶ c) : a ⟶ c :=
  fun x z => ∀ y, R x y ∨ S y z

/-- `id•` on `Rel(Set)`: the INEQUALITY relation, the complement of `𝟙`. -/
def relBid (a : RelSet.{u}) : a ⟶ a := fun x y => x ≠ y

/-- `R⊥` on `Rel(Set)`: the complement of the converse
    (`DiagrammaticAlgebraOfFirstOrderLogic.pdf` p. 7, "`R̄† = {(y,x) | (x,y) ∉ R}`").  The paper
    notes that in `Rel` this single arrow is BOTH the left and the right linear adjoint, so
    `lperp` below is the same function. -/
def relPerp {a b : RelSet.{u}} (R : a ⟶ b) : b ⟶ a := fun y x => ¬ R x y

instance : LinearBicat RelSet.{u} :=
  { (inferInstance : OrderedCat RelSet.{u}) with
    bid := relBid
    bcomp := relBcomp
    bid_bcomp := fun R => RelSet.hom_ext fun x z =>
      ⟨fun h => (h x).resolve_left (fun hne => hne rfl),
       fun hR y => (Classical.em (x = y)).elim (fun he => Or.inr (he ▸ hR)) Or.inl⟩
    bcomp_bid := fun {_ b} R => RelSet.hom_ext fun x z =>
      ⟨fun h => (h z).resolve_right (fun hne => hne rfl),
       fun hR y => (Classical.em (y = z)).elim (fun he => Or.inl (he ▸ hR)) Or.inr⟩
    -- Both sides say `∀ y z, R x y ∨ S y z ∨ T z w`; the two bracketings differ only in which
    -- quantifier is pushed inside the disjunction, and excluded middle on the OTHER disjunct
    -- ("either `T z w` already holds, or it never will") is what pushes it back out.
    bcomp_assoc := fun {_ _ _ _} R S T => RelSet.hom_ext fun x w => by
      constructor
      · intro h y
        refine (Classical.em (R x y)).elim Or.inl (fun hR => Or.inr (fun z => ?_))
        exact (h z).elim (fun hRS => Or.inl ((hRS y).resolve_left hR)) Or.inr
      · intro h z
        refine (Classical.em (T z w)).elim Or.inr (fun hT => Or.inl (fun y => ?_))
        exact (h y).elim Or.inl (fun hST => Or.inr ((hST z).resolve_right hT))
    bcomp_mono := fun {_ _ _ _ _ _ _} hR hS => RelSet.le_iff.mpr fun x z h y =>
      (h y).elim (fun hr => Or.inl (RelSet.le_iff.mp hR x y hr))
        (fun hs => Or.inr (RelSet.le_iff.mp hS y z hs))
    linDistrib_left := fun R S T => RelSet.le_iff.mpr fun x w h z => by
      obtain ⟨y, hR, hST⟩ := h
      exact (hST z).elim (fun hS => Or.inl ⟨y, hR, hS⟩) Or.inr
    linDistrib_right := fun R S T => RelSet.le_iff.mpr fun x w h y => by
      obtain ⟨z, hRS, hT⟩ := h
      exact (hRS y).elim Or.inl (fun hS => Or.inr ⟨z, hS, hT⟩) }

instance : ClosedLinearBicat RelSet.{u} :=
  { (inferInstance : LinearBicat RelSet.{u}) with
    perp := relPerp
    -- The unit `𝟙 ≤ R ⨟• R⊥` IS excluded middle at `R x y`; the counit is the observation that
    -- `¬R x y` and `R x y'` force `y ≠ y'`.
    perp_adj := fun {_ _} R =>
      { unit := RelSet.le_iff.mpr fun x x' hx y =>
          (Classical.em (R x y)).elim Or.inl (fun hn => Or.inr (hx ▸ hn))
        counit := RelSet.le_iff.mpr fun y y' h he => by
          obtain ⟨x, hn, hp⟩ := h; exact hn (he ▸ hp) }
    lperp := relPerp
    lperp_adj := fun {_ _} R =>
      { unit := RelSet.le_iff.mpr fun y y' hy x =>
          (Classical.em (R x y)).elim (fun hp => Or.inr (hy ▸ hp)) Or.inl
        counit := RelSet.le_iff.mpr fun x x' h he => by
          obtain ⟨y, hp, hn⟩ := h; exact hn (he ▸ hp) } }

/-! ### What the abstract operations compute to

The same check phases 4 and 8 make: the class fields are not merely inhabited, they are the
concrete operations the paper names. -/

theorem bid_apply {a : RelSet.{u}} (x y : a.carrier) : (𝟙• a) x y ↔ x ≠ y := Iff.rfl

theorem bcomp_apply {a b c : RelSet.{u}} (R : a ⟶ b) (S : b ⟶ c) (x : a.carrier) (z : c.carrier) :
    (R ≫• S) x z ↔ ∀ y, R x y ∨ S y z := Iff.rfl

theorem perp_apply {a b : RelSet.{u}} (R : a ⟶ b) (y : b.carrier) (x : a.carrier) :
    ClosedLinearBicat.perp R y x ↔ ¬ R x y := Iff.rfl

/-- `R⊥` really is the complement of the converse: it is `¬` applied to the phase-3 `conv`. -/
theorem perp_eq_not_conv {a b : RelSet.{u}} (R : a ⟶ b) (y : b.carrier) (x : a.carrier) :
    ClosedLinearBicat.perp R y x ↔ ¬ CartBicat.conv R y x := by
  rw [conv_eq_recip]; exact Iff.rfl

/-! ### The residual is the repo's division

`AOP/A6_1_RelSet.lean` builds `R / S := fun x y => ∀ z, S y z → R x z` — a direct `∀`, with no
complement and no excluded middle, and that stays the canonical division for AOP work.  The fo
layer arrives at the same relation from the other side, as `R ⨟• S⊥`. -/

/-- **The fo-layer residual is Freyd's division.**  Proved from the two universal properties alone:
    `«≤_residual_iff»` and `le_div_iff` are the same Galois connection, and a right adjoint to
    `(−) ≫ S` is unique.  Neither definition is unfolded. -/
theorem residual_eq_div {a b c : RelSet.{u}} (R : a ⟶ c) (S : b ⟶ c) :
    ClosedLinearBicat.residual R S = R / S :=
  OrderedCat.«≤_antisymm»
    ((le_div_iff _ R S).mpr (ClosedLinearBicat.«residual_comp_≤» R S))
    ((ClosedLinearBicat.«≤_residual_iff» _ R S).mp (DivisionAllegory.div_comp_le R S))

/-- The same statement pointwise: `R ⨟• S⊥` unfolds to `∀ z, S y z → R x z`.  This is where the
    classical step is visible — `¬ S y z ∨ R x z` is `S y z → R x z` only with excluded middle. -/
theorem residual_apply {a b c : RelSet.{u}} (R : a ⟶ c) (S : b ⟶ c)
    (x : a.carrier) (y : b.carrier) :
    ClosedLinearBicat.residual R S x y ↔ ∀ z, S y z → R x z := by
  rw [residual_eq_div]; exact Iff.rfl

/-! ### The complement, and the transport it induces

`DiagrammaticAlgebraOfFirstOrderLogic.pdf` p. 8 defines the complement as `c̄ = ((c)⊥)†`; at
`Rel(Set)` that is `¬ R x y`.  The four lemmas below say complement is an order-REVERSING bijection
carrying `(≫, 𝟙, ⊗ₕ)` to `(≫•, 𝟙•, ⊗•ₕ)`.  That is the whole content of the paper's remark (§4,
p. 6) that Fig. 3 is Fig. 2 "with both the colours and the order inverted": every black law below is
`congrArg compl` of the white law of the same name, so `diag/CB.lean`'s axioms are re-used rather
than re-proved, and the black structural isos are the complements of the white ones. -/

/-- The COMPLEMENT of a relation. -/
def compl {a b : RelSet.{u}} (R : a ⟶ b) : a ⟶ b := fun x y => ¬ R x y

theorem compl_compl {a b : RelSet.{u}} (R : a ⟶ b) : compl (compl R) = R :=
  RelSet.hom_ext fun _ _ => ⟨Classical.byContradiction, fun h hn => hn h⟩

theorem compl_inj {a b : RelSet.{u}} {R S : a ⟶ b} (h : compl R = compl S) : R = S := by
  rw [← compl_compl R, ← compl_compl S, h]

/-- Complement REVERSES the hom order — the "inverting the order" half of the paper's remark. -/
theorem «compl_≤_iff» {a b : RelSet.{u}} {R S : a ⟶ b} : compl R ≤ compl S ↔ S ≤ R := by
  constructor
  · exact fun h => RelSet.le_iff.mpr fun x y hS =>
      Classical.byContradiction fun hn => RelSet.le_iff.mp h x y hn hS
  · exact fun h => RelSet.le_iff.mpr fun x y hR hS => hR (RelSet.le_iff.mp h x y hS)

theorem compl_bid (a : RelSet.{u}) : compl (𝟙• a) = 𝟙 a :=
  RelSet.hom_ext fun _ _ => ⟨Classical.byContradiction, fun h hn => hn h⟩

theorem compl_bcomp {a b c : RelSet.{u}} (R : a ⟶ b) (S : b ⟶ c) :
    compl (R ≫• S) = compl R ≫ compl S :=
  RelSet.hom_ext fun x _ =>
    ⟨fun h => Classical.byContradiction fun hn =>
        h fun y => (Classical.em (R x y)).elim Or.inl fun hnR =>
          Or.inr (Classical.byContradiction fun hnS => hn ⟨y, hnR, hnS⟩),
     fun ⟨y, hnR, hnS⟩ h => (h y).elim hnR hnS⟩


/-- `⊗•` at `Rel(Set)`: the de Morgan dual of the product action, i.e. `⊗ₕ` conjugated by
    complement.  Pointwise `(R ⊗• S) p q ↔ R p.1 q.1 ∨ S p.2 q.2`. -/
def relBtensHom {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b') :
    (a ⊗ b : RelSet.{u}) ⟶ (a' ⊗ b') :=
  compl (compl R ⊗ₕ compl S)

theorem compl_relBtensHom {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b') :
    compl (relBtensHom R S) = compl R ⊗ₕ compl S := compl_compl _

theorem relBtensHom_apply {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b')
    (p : a.carrier × b.carrier) (q : a'.carrier × b'.carrier) :
    relBtensHom R S p q ↔ (R p.1 q.1 ∨ S p.2 q.2) := by
  refine ⟨fun h => (Classical.em (R p.1 q.1)).elim Or.inl fun hnR =>
    Or.inr (Classical.byContradiction fun hnS => h ⟨hnR, hnS⟩), ?_⟩
  exact fun h hn => h.elim hn.1 hn.2

/-- The `≤`-facing form of the transport, used by every inequational field below. -/
theorem compl_tensHom_mono {a a' b b' : RelSet.{u}} {R R' : a ⟶ a'} {S S' : b ⟶ b'}
    (hR : R ≤ R') (hS : S ≤ S') : relBtensHom R S ≤ relBtensHom R' S' :=
  «compl_≤_iff».mpr (SymMonCat.tensHom_mono («compl_≤_iff».mpr hR) («compl_≤_iff».mpr hS))

/-! ### Definition 5.1 at `Rel(Set)`

Every black monoidal iso is the complement of the white one, and every law is `compl_inj` applied to
the white law.  The six mixed-colour inequations — the four linear strengths and (⊗°)/(⊗•) — are the
only ones that cannot be transported, because they mention both colours at once; those go
pointwise. -/

instance : MonLinearBicat RelSet.{u} :=
  { (inferInstance : SymMonCat RelSet.{u}), (inferInstance : LinearBicat RelSet.{u}) with
    btensHom := relBtensHom
    btensHom_bid := fun a b => compl_inj <| by
      simp only [compl_relBtensHom, compl_bid]; exact SymMonCat.tensHom_id a b
    btensHom_bcomp := fun R R' S S' => compl_inj <| by
      simp only [compl_relBtensHom, compl_bcomp]; exact SymMonCat.tensHom_comp _ _ _ _
    btensHom_mono := compl_tensHom_mono

    bassoc := fun a b c => compl (SymMonCat.tensAssoc a b c)
    bassocInv := fun a b c => compl (SymMonCat.tensAssocInv a b c)
    bassoc_inv := fun a b c => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_bid]; exact SymMonCat.tensAssoc_inv a b c
    inv_bassoc := fun a b c => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_bid]; exact SymMonCat.inv_tensAssoc a b c
    bassoc_nat := fun R S T => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_relBtensHom]; exact SymMonCat.tensAssoc_nat _ _ _

    blunit := fun a => compl (SymMonCat.lunit a)
    blunitInv := fun a => compl (SymMonCat.lunitInv a)
    blunit_inv := fun a => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_bid]; exact SymMonCat.lunit_inv a
    inv_blunit := fun a => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_bid]; exact SymMonCat.inv_lunit a
    blunit_nat := fun R => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_relBtensHom, compl_bid]
      exact SymMonCat.lunit_nat _

    brunit := fun a => compl (SymMonCat.runit a)
    brunitInv := fun a => compl (SymMonCat.runitInv a)
    brunit_inv := fun a => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_bid]; exact SymMonCat.runit_inv a
    inv_brunit := fun a => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_bid]; exact SymMonCat.inv_runit a
    brunit_nat := fun R => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_relBtensHom, compl_bid]
      exact SymMonCat.runit_nat _

    bswap := fun a b => compl (SymMonCat.swap a b)
    bswap_bswap := fun a b => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_bid]; exact SymMonCat.swap_swap a b
    bswap_nat := fun R S => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_relBtensHom]; exact SymMonCat.swap_nat _ _
    bswap_blunit := fun a => compl_inj <| by
      simp only [compl_bcomp, compl_compl]; exact SymMonCat.swap_lunit a

    bpentagon := fun a b c d => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_relBtensHom, compl_bid]
      exact SymMonCat.pentagon a b c d
    btriangle := fun a b => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_relBtensHom, compl_bid]
      exact SymMonCat.triangle a b
    bhexagon := fun a b c => compl_inj <| by
      simp only [compl_bcomp, compl_compl, compl_relBtensHom, compl_bid]
      exact SymMonCat.hexagon a b c

    -- (ν_l°): fix the middle pair `m`; either both left factors fire, or one of the right ones
    -- does, and a right one is exactly what the black `⊗•` on the right needs.
    strength_lw := fun R S T U => RelSet.le_iff.mpr fun p q h m => by
      rcases h with ⟨h1, h2⟩
      rcases h1 m.1 with hR | hS
      · rcases h2 m.2 with hT | hU
        · exact Or.inl ⟨hR, hT⟩
        · exact Or.inr ((relBtensHom_apply _ _ m q).mpr (Or.inr hU))
      · exact Or.inr ((relBtensHom_apply _ _ m q).mpr (Or.inl hS))
    strength_rw := fun R S T U => RelSet.le_iff.mpr fun p q h m => by
      rcases h with ⟨h1, h2⟩
      rcases h1 m.1 with hR | hS
      · exact Or.inl ((relBtensHom_apply _ _ p m).mpr (Or.inl hR))
      · rcases h2 m.2 with hT | hU
        · exact Or.inl ((relBtensHom_apply _ _ p m).mpr (Or.inr hT))
        · exact Or.inr ⟨hS, hU⟩
    -- (ν_l•)/(ν_r•): the conclusion is a black `⊗•`, i.e. a disjunction; the witness `m` supplies
    -- whichever disjunct the hypothesis' own disjunction chose.
    strength_lb := fun R S T U => RelSet.le_iff.mpr fun p q h => by
      obtain ⟨m, hRT, hS, hU⟩ := h
      refine (relBtensHom_apply _ _ p q).mpr ?_
      rcases (relBtensHom_apply R T p m).mp hRT with hR | hT
      · exact Or.inl ⟨m.1, hR, hS⟩
      · exact Or.inr ⟨m.2, hT, hU⟩
    strength_rb := fun R S T U => RelSet.le_iff.mpr fun p q h => by
      obtain ⟨m, ⟨hR, hT⟩, hSU⟩ := h
      refine (relBtensHom_apply _ _ p q).mpr ?_
      rcases (relBtensHom_apply S U m q).mp hSU with hS | hU
      · exact Or.inl ⟨m.1, hR, hS⟩
      · exact Or.inr ⟨m.2, hT, hU⟩

    -- (⊗•): `x ≠ y ∧ z ≠ w` forces `(x,z) ≠ (y,w)` — one component already differs.
    tens_bid_lax := fun a b => RelSet.le_iff.mpr fun p q h he =>
      h.1 (congrArg Prod.fst he)
    -- (⊗°): `p = q` forces `p.1 = q.1 ∨ p.2 = q.2`.
    btens_id_colax := fun a b => RelSet.le_iff.mpr fun p q he =>
      (relBtensHom_apply _ _ p q).mpr (Or.inl (congrArg Prod.fst he)) }

/-! ### The transport, as one tactic

A structure projection is opaque to `simp`, so a Fig. 3 or Fig. 5 goal arrives reading
`MonLinearBicat.bassoc n n n` rather than the `compl (α)` that was supplied for it.  The ten `rfl`
lemmas below expose the chosen field values (and, for `bcomp`/`bid`, record that the two projection
paths to `LinearBicat` agree — Lean flattens `LinearBicat` into `MonLinearBicat`, whose subobject is
`SymMonCat`).  `black_transport` then bundles them with the four complement lemmas, so every black
law is one tactic call followed by the white law of the same name. -/

theorem mbcomp_eq {a b c : RelSet.{u}} (R : a ⟶ b) (S : b ⟶ c) :
    MonLinearBicat.bcomp R S = R ≫• S := rfl

theorem mbid_eq (a : RelSet.{u}) : MonLinearBicat.bid a = 𝟙• a := rfl

theorem btensHom_eq {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b') :
    MonLinearBicat.btensHom R S = relBtensHom R S := rfl

theorem bassoc_eq (a b c : RelSet.{u}) :
    MonLinearBicat.bassoc a b c = compl (SymMonCat.tensAssoc a b c) := rfl

theorem bassocInv_eq (a b c : RelSet.{u}) :
    MonLinearBicat.bassocInv a b c = compl (SymMonCat.tensAssocInv a b c) := rfl

theorem blunit_eq (a : RelSet.{u}) : MonLinearBicat.blunit a = compl (SymMonCat.lunit a) := rfl

theorem blunitInv_eq (a : RelSet.{u}) :
    MonLinearBicat.blunitInv a = compl (SymMonCat.lunitInv a) := rfl

theorem brunit_eq (a : RelSet.{u}) : MonLinearBicat.brunit a = compl (SymMonCat.runit a) := rfl

theorem brunitInv_eq (a : RelSet.{u}) :
    MonLinearBicat.brunitInv a = compl (SymMonCat.runitInv a) := rfl

theorem bswap_eq (a b : RelSet.{u}) : MonLinearBicat.bswap a b = compl (SymMonCat.swap a b) := rfl

/-- Rewrite a BLACK law into the WHITE law it is the complement of. -/
scoped macro "black_transport" : tactic =>
  `(tactic| simp only [mbcomp_eq, mbid_eq, btensHom_eq, bassoc_eq, bassocInv_eq, blunit_eq,
      blunitInv_eq, brunit_eq, brunitInv_eq, bswap_eq, compl_bcomp, compl_relBtensHom, compl_bid,
      compl_compl])

/-! ### Figure 3 at `Rel(Set)` -/

instance : CocartBicat RelSet.{u} :=
  { (inferInstance : MonLinearBicat RelSet.{u}) with
    bdelta := fun n => compl (ΔRel n)
    bbang := fun n => compl («!Rel» n)
    bnabla := fun n => compl ((ΔRel n)°)
    bunitR := fun n => compl ((«!Rel» n)°)

    bdelta_assoc := fun n => compl_inj <| by
      black_transport
      exact CartBicat.Δ_assoc n
    bdelta_comm := fun n => compl_inj <| by
      black_transport; exact CartBicat.Δ_comm n
    bdelta_counit := fun n => compl_inj <| by
      black_transport
      exact CartBicat.Δ_counit n
    bnabla_assoc := fun n => compl_inj <| by
      black_transport
      exact CartBicat.«∇_assoc» n
    bnabla_comm := fun n => compl_inj <| by
      black_transport; exact CartBicat.«∇_comm» n
    bnabla_unit := fun n => compl_inj <| by
      black_transport
      exact CartBicat.«∇_unit» n

    bineq_37 := fun n => «compl_≤_iff».mp <| by
      black_transport; exact CartBicat.«∇Δ_≤_𝟙» n
    bineq_38 := fun n => «compl_≤_iff».mp <| by
      black_transport; exact CartBicat.«𝟙_≤_Δ∇» n
    bineq_39 := fun n => «compl_≤_iff».mp <| by
      black_transport; exact CartBicat.«?!_≤_𝟙» n
    bineq_40 := fun n => «compl_≤_iff».mp <| by
      black_transport; exact CartBicat.«𝟙_≤_!?» n

    bfrob_left := fun n => compl_inj <| by
      black_transport
      exact CartBicat.frob_left n
    bfrob_right := fun n => compl_inj <| by
      black_transport
      exact CartBicat.frob_right n

    blax_delta := fun R => «compl_≤_iff».mp <| by
      black_transport; exact CartBicat.lax_Δ _
    blax_bang := fun R => «compl_≤_iff».mp <| by
      black_transport; exact CartBicat.lax_! _ }

/-! ### Definition 6.1 at `Rel(Set)`

The sixteen inequalities of Fig. 5 collapse to eight applications of `perp_adj`, because at
`Rel(Set)` every black generator IS the linear adjoint of a white one: `perp R = compl (R°)`, and
`▶• = compl ▶° = compl (◀°)°`, which is `(◀°)⊥` on the nose.  That is the concrete reason Def. 6.1.4
is the right axiom rather than an extra assumption. -/

theorem perp_compl {a b : RelSet.{u}} (R : a ⟶ b) :
    ClosedLinearBicat.perp (compl R) = R° := by
  refine RelSet.hom_ext fun y x => ?_
  exact ⟨Classical.byContradiction, fun h hn => hn h⟩

/-- The two black merges/copies are the complements of the white ones — `rfl` the one way, double
    negation the other.  Needed only to line Fig. 5's black Frobenius laws up with the white ones. -/
theorem compl_bdelta (n : RelSet.{u}) :
    compl (CocartBicat.bdelta n) = CartBicat.Δ n := compl_compl _

theorem compl_bnabla (n : RelSet.{u}) :
    compl (CocartBicat.bnabla n) = CartBicat.«∇» n := compl_compl _

/-- `σ°`'s converse is `σ°` the other way round — needed so that `σ•` is `(σ°)⊥`. -/
theorem swap_recip (a b : RelSet.{u}) :
    (SymMonCat.swap a b : (a ⊗ b : RelSet.{u}) ⟶ (b ⊗ a))° = SymMonCat.swap b a :=
  RelSet.hom_ext fun m p => by
    simp only [swap_eq, RelSet.recip_apply, RelSet.graph_apply]
    exact ⟨fun h => by subst h; rfl, fun h => by subst h; rfl⟩

/-- `(F^•_∘)`, the mixed-colour Frobenius law: both sides relate `(x₁,x₂)` to `(y₁,y₂)` exactly when
    `x₂ = y₂` and not both coordinates of the OTHER strand collapse onto `x₁`.  Stated outside the
    instance because Fig. 5's black law `(F_•^°)` is its complement, so the same proof serves
    twice. -/
theorem relLinfrob_bw (n : RelSet.{u}) :
    (compl (ΔRel n) ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ (ΔRel n)°)
      = (𝟙 n ⊗ₕ ΔRel n) ≫ SymMonCat.tensAssocInv n n n ≫ (compl ((ΔRel n)°) ⊗ₕ 𝟙 n) :=
  RelSet.hom_ext fun p q => by
    simp only [tensHom_eq, tensAssoc_eq, tensAssocInv_eq, RelSet.comp_apply,
      RelSet.rprodMap_apply, RelSet.graph_apply, RelSet.id_apply, compl, ΔRel,
      RelSet.recip_apply]
    constructor
    · rintro ⟨m, ⟨hd, hx⟩, r, rfl, hy1, hy2⟩
      have e2 : m.1.2 = q.2 := (Prod.ext_iff.mp hy2).1
      have e3 : m.2 = q.2 := (Prod.ext_iff.mp hy2).2
      refine ⟨(p.1, (p.2, p.2)), ⟨rfl, rfl⟩, ((p.1, p.2), p.2), rfl, ?_, hx.trans e3⟩
      intro he
      have f1 : p.1 = q.1 := (Prod.ext_iff.mp he).1
      have f2 : p.2 = q.1 := (Prod.ext_iff.mp he).2
      exact hd (Prod.ext_iff.mpr ⟨hy1.trans f1.symm,
        e2.trans ((hx.trans e3).symm.trans (f2.trans f1.symm))⟩)
    · rintro ⟨r, ⟨h1, h2⟩, m, rfl, hd2, hx2⟩
      have g1 : r.2.1 = p.2 := (Prod.ext_iff.mp h2).1
      have g2 : r.2.2 = p.2 := (Prod.ext_iff.mp h2).2
      refine ⟨((q.1, q.2), q.2), ⟨?_, g2.symm.trans hx2⟩, (q.1, (q.2, q.2)), rfl, rfl, rfl⟩
      intro he
      have f1 : q.1 = p.1 := (Prod.ext_iff.mp he).1
      have f2 : q.2 = p.1 := (Prod.ext_iff.mp he).2
      exact hd2 (Prod.ext_iff.mpr ⟨h1.symm.trans f1.symm,
        g1.trans ((g2.symm.trans hx2).trans (f2.trans f1.symm))⟩)

/-- `(F^°_•)`, the other mixed-colour Frobenius law; Fig. 5's `(F_∘^•)` is its complement. -/
theorem relLinfrob_wb (n : RelSet.{u}) :
    (ΔRel n ⊗ₕ 𝟙 n) ≫ SymMonCat.tensAssoc n n n ≫ (𝟙 n ⊗ₕ compl ((ΔRel n)°))
      = (𝟙 n ⊗ₕ compl (ΔRel n)) ≫ SymMonCat.tensAssocInv n n n ≫ ((ΔRel n)° ⊗ₕ 𝟙 n) :=
  RelSet.hom_ext fun p q => by
    simp only [tensHom_eq, tensAssoc_eq, tensAssocInv_eq, RelSet.comp_apply,
      RelSet.rprodMap_apply, RelSet.graph_apply, RelSet.id_apply, compl, ΔRel,
      RelSet.recip_apply]
    constructor
    · rintro ⟨m, ⟨hd, hx⟩, r, rfl, hy1, hy2⟩
      have d1 : m.1.1 = p.1 := (Prod.ext_iff.mp hd).1
      have d2 : m.1.2 = p.1 := (Prod.ext_iff.mp hd).2
      refine ⟨(p.1, (q.1, q.2)), ⟨rfl, ?_⟩, ((p.1, q.1), q.2), rfl,
        Prod.ext_iff.mpr ⟨d1.symm.trans hy1, rfl⟩, rfl⟩
      intro he
      have k1 : q.1 = p.2 := (Prod.ext_iff.mp he).1
      have k2 : q.2 = p.2 := (Prod.ext_iff.mp he).2
      exact hy2 (Prod.ext_iff.mpr
        ⟨d2.trans ((d1.symm.trans hy1).trans (k1.trans k2.symm)), hx.symm.trans k2.symm⟩)
    · rintro ⟨r, ⟨h1, hnr⟩, m, rfl, hm1, hm2⟩
      have j1 : r.1 = q.1 := (Prod.ext_iff.mp hm1).1
      have j2 : r.2.1 = q.1 := (Prod.ext_iff.mp hm1).2
      refine ⟨((p.1, p.1), p.2), ⟨rfl, rfl⟩, (p.1, (p.1, p.2)), rfl, h1.trans j1, ?_⟩
      intro he
      have k1 : p.1 = q.2 := (Prod.ext_iff.mp he).1
      have k2 : p.2 = q.2 := (Prod.ext_iff.mp he).2
      exact hnr (Prod.ext_iff.mpr
        ⟨j2.trans ((h1.trans j1).symm.trans (k1.trans k2.symm)), hm2.trans k2.symm⟩)

instance : FOBicat RelSet.{u} :=
  { (inferInstance : CocartBicat RelSet.{u}), (inferInstance : CartBicat RelSet.{u}),
    (inferInstance : ClosedLinearBicat RelSet.{u}) with
    -- Def. 5.5's symmetry clause: `σ• = compl σ°`, so `σ• = (σ°)⊥` by `swap_recip`.
    swap_linAdj := fun a b => by
      have h := ClosedLinearBicat.perp_adj (SymMonCat.swap a b : (a ⊗ b : RelSet.{u}) ⟶ (b ⊗ a))
      rwa [show ClosedLinearBicat.perp (SymMonCat.swap a b) = compl (SymMonCat.swap b a) from by
        rw [← swap_recip a b]; rfl] at h
    bswap_linAdj := fun a b => by
      have h := ClosedLinearBicat.perp_adj (compl (SymMonCat.swap a b))
      rwa [perp_compl, swap_recip] at h

    delta_linAdj := fun n => ClosedLinearBicat.perp_adj (ΔRel n)
    bang_linAdj := fun n => ClosedLinearBicat.perp_adj («!Rel» n)
    nabla_linAdj := fun n => by
      have h := ClosedLinearBicat.perp_adj ((ΔRel n)°)
      rwa [show ClosedLinearBicat.perp ((ΔRel n)°) = compl (ΔRel n) from rfl] at h
    unitR_linAdj := fun n => by
      have h := ClosedLinearBicat.perp_adj ((«!Rel» n)°)
      rwa [show ClosedLinearBicat.perp ((«!Rel» n)°) = compl («!Rel» n) from rfl] at h
    bdelta_linAdj := fun n => by
      have h := ClosedLinearBicat.perp_adj (compl (ΔRel n))
      rwa [perp_compl] at h
    bbang_linAdj := fun n => by
      have h := ClosedLinearBicat.perp_adj (compl («!Rel» n))
      rwa [perp_compl] at h
    bnabla_linAdj := fun n => by
      have h := ClosedLinearBicat.perp_adj (compl ((ΔRel n)°))
      rwa [perp_compl, Allegory.recip_recip] at h
    bunitR_linAdj := fun n => by
      have h := ClosedLinearBicat.perp_adj (compl ((«!Rel» n)°))
      rwa [perp_compl, Allegory.recip_recip] at h

    linfrob_bw := relLinfrob_bw
    linfrob_wb := relLinfrob_wb
    -- `(F_•^°)` and `(F_∘^•)`, the two black-structure laws, ARE the complements of the two above —
    -- crosswise, because complementing swaps the generators' colours as well as the composition's.
    blinfrob_wb := fun n => compl_inj <| by
      black_transport
      simp only [compl_bdelta, compl_bnabla]
      exact relLinfrob_bw n
    blinfrob_bw := fun n => compl_inj <| by
      black_transport
      simp only [compl_bdelta, compl_bnabla]
      exact relLinfrob_wb n }

end Freyd.Diag
