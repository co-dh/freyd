/-
  `diag.RelSetTape` — SOUNDNESS for phase 8: `Rel(Set)`'s `Sum` is the biproduct `diag/Tape.lean`
  axiomatises, so the class is inhabited and its `∪` is the ordinary union of relations.

  This is the same falsification oracle phase 4 was for phase 3: abstract axioms are only worth
  deriving from once something satisfies them.  `Sum` is the obvious candidate — `copair` is
  `Sum.rec`, the injections are the graphs of the constructors, and the zero object is `PEmpty`,
  whose only relation to or from anything is the empty one.
-/
import diag.Tape
import diag.RelSetCB

universe u

namespace Freyd.Diag

open Freyd
open Freyd.Alg
open scoped SymMonCat

/-- `[R, S]` on `Rel(Set)`: case on the summand. -/
def sumCopair {a b c : RelSet.{u}} (R : a ⟶ c) (S : b ⟶ c) :
    (⟨a.carrier ⊕ b.carrier⟩ : RelSet.{u}) ⟶ c :=
  fun s z => Sum.rec (fun x => R x z) (fun y => S y z) s

instance : Biprod RelSet.{u} :=
  { (inferInstance : CartBicat RelSet.{u}) with
    sum := fun a b => ⟨a.carrier ⊕ b.carrier⟩
    inl := fun a b => RelSet.graph (Sum.inl : a.carrier → a.carrier ⊕ b.carrier)
    inr := fun a b => RelSet.graph (Sum.inr : b.carrier → a.carrier ⊕ b.carrier)
    copair := sumCopair
    inl_copair := fun _ _ => by rw [RelSet.graph_comp_left]; rfl
    inr_copair := fun _ _ => by rw [RelSet.graph_comp_left]; rfl
    copair_uniq := fun {_ _ _ _ _} hl hr => by
      rw [RelSet.graph_comp_left, RelSet.graph_comp_left] at hl hr
      apply RelSet.hom_ext
      rintro (x | y) z
      · exact congrFun (congrFun hl x) z ▸ Iff.rfl
      · exact congrFun (congrFun hr y) z ▸ Iff.rfl
    copair_mono := fun {_ _ _ _ _ _ _} hR hS => RelSet.le_iff.mpr <| by
      rintro (x | y) z h
      · exact RelSet.le_iff.mp hR x z h
      · exact RelSet.le_iff.mp hS y z h
    conv_inl_le := fun _ _ => by
      rw [conv_eq_recip]
      exact RelSet.le_iff.mpr fun s s' ⟨_, hs, hs'⟩ => hs ▸ hs' ▸ rfl
    conv_inr_le := fun _ _ => by
      rw [conv_eq_recip]
      exact RelSet.le_iff.mpr fun s s' ⟨_, hs, hs'⟩ => hs ▸ hs' ▸ rfl
    diag_codiag := fun a => by
      rw [conv_eq_recip]
      refine RelSet.hom_ext fun x z => ⟨?_, fun h => ⟨Sum.inl x, rfl, h⟩⟩
      rintro ⟨s, hs, h⟩
      cases s <;> exact hs.symm.trans h
    zero := ⟨PEmpty⟩
    toZero := fun _ => fun _ e => PEmpty.elim e
    toZero_uniq := fun _ => RelSet.hom_ext fun _ e => e.elim
    bot_le := fun _ => RelSet.le_iff.mpr fun _ _ ⟨e, _, _⟩ => e.elim }

/-! ### What the abstract `∪` and `⊥` compute to

The point of the phase: `union`, assembled out of a pairing and a copairing with no mention of `∨`,
IS disjunction — and `bot`, routed through the empty object, IS the empty relation. -/

theorem union_apply {a b : RelSet.{u}} (R S : a ⟶ b) (x : a.carrier) (y : b.carrier) :
    Biprod.union R S x y ↔ (R x y ∨ S x y) := by
  dsimp [Biprod.union, Biprod.pair]
  simp only [conv_eq_recip]
  constructor
  · rintro ⟨s, hs, h⟩
    cases s with
    | inl w => exact Or.inl (h ▸ hs)
    | inr w => exact Or.inr (h ▸ hs)
  · rintro (h | h)
    · exact ⟨Sum.inl y, h, rfl⟩
    · exact ⟨Sum.inr y, h, rfl⟩

theorem bot_apply {a b : RelSet.{u}} (x : a.carrier) (y : b.carrier) :
    ¬ Biprod.bot a b x y := fun ⟨e, _, _⟩ => e.elim

/-- The product action carries `∪` through, which is the rig law: `∧` distributes over `∨`. -/
theorem rprodMap_union {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S T : b ⟶ b') :
    RelSet.rprodMap R (Biprod.union S T)
      = Biprod.union (RelSet.rprodMap R S) (RelSet.rprodMap R T) :=
  RelSet.hom_ext fun p q => by
    simp only [union_apply, RelSet.rprodMap_apply]
    constructor
    · rintro ⟨hR, hS | hT⟩
      · exact Or.inl ⟨hR, hS⟩
      · exact Or.inr ⟨hR, hT⟩
    · rintro (⟨hR, hS⟩ | ⟨hR, hT⟩)
      · exact ⟨hR, Or.inl hS⟩
      · exact ⟨hR, Or.inr hT⟩

instance : FbCbRig RelSet.{u} :=
  { (inferInstance : Biprod RelSet.{u}) with
    tensHom_union := fun R S T => rprodMap_union R S T }

/-! ### Agreement — the composite check for phase 8

Phase 5's `allegoryOfCartBicat` lands on the `Allegory RelSet` the repo already had
(`diag/RelSetAllegory.lean`); these say the same of the two operations phase 8 adds. -/

/-- The bridge's `∪` on `Rel(Set)` is the union the repo already had. -/
theorem distributiveAllegoryOfFbCb_union {a b : RelSet.{u}} (R S : a ⟶ b) :
    (FbCbRig.distributiveAllegoryOfFbCb RelSet.{u}).union R S = R ∪ S :=
  RelSet.hom_ext fun x y => union_apply R S x y

/-- The bridge's `𝟘` on `Rel(Set)` is the empty relation. -/
theorem distributiveAllegoryOfFbCb_zero {a b : RelSet.{u}} :
    (FbCbRig.distributiveAllegoryOfFbCb RelSet.{u}).zero = (𝟘 : a ⟶ b) :=
  RelSet.hom_ext fun x y => ⟨fun h => (bot_apply x y h).elim, fun h => h.elim⟩

end Freyd.Diag
