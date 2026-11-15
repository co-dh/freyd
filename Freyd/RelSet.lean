module

public import Freyd.S2_20

section
set_option linter.unusedVariables false
universe u v
namespace Freyd.Alg
open Freyd

/-- An object of the allegory `Rel(Set)`: a bundled Lean type.  Bundled (not a bare `Type u`)
    so these instances attach here and do NOT collide with the ambient category on `Type u`. -/
public structure RelSet : Type (u + 1) where
  carrier : Type u

end Freyd.Alg
end

section
set_option linter.unusedVariables false
universe u v
namespace Freyd.Alg
open Freyd
namespace RelSet

@[expose] public instance : Cat RelSet.{u} where
  Hom A B := A.carrier → B.carrier → Prop
  id _ := fun x y => x = y
  comp R S := fun x z => ∃ y, R x y ∧ S y z
  id_comp R := funext fun x => funext fun y => propext ⟨fun ⟨_, h, hR⟩ => h ▸ hR,
    fun hR => ⟨x, rfl, hR⟩⟩
  comp_id R := funext fun x => funext fun y => propext ⟨fun ⟨_, hR, h⟩ => h ▸ hR,
    fun hR => ⟨y, hR, rfl⟩⟩
  assoc R S T := funext fun x => funext fun w => propext
    ⟨fun ⟨y, ⟨z, hR, hS⟩, hT⟩ => ⟨z, hR, y, hS, hT⟩, fun ⟨z, hR, y, hS, hT⟩ => ⟨y, ⟨z, hR, hS⟩, hT⟩⟩

@[simp] public theorem comp_apply {A B C : RelSet.{u}} (R : A ⟶ B) (S : B ⟶ C) (x : A.carrier)
    (z : C.carrier) : (R ≫ S) x z = ∃ y, R x y ∧ S y z := rfl

/-- Extensionality for `Rel(Set)` morphisms: relations are equal iff pointwise equivalent. -/
public theorem hom_ext {A B : RelSet.{u}} {R S : A ⟶ B} (h : ∀ x y, R x y ↔ S x y) : R = S :=
  funext fun x => funext fun y => propext (h x y)

@[expose] public instance : Allegory RelSet.{u} where
  recip R := fun y x => R x y
  inter R S := fun x y => R x y ∧ S x y
  recip_recip _ := rfl
  recip_comp R S := hom_ext fun z x => ⟨fun ⟨y, hR, hS⟩ => ⟨y, hS, hR⟩, fun ⟨y, hS, hR⟩ => ⟨y, hR, hS⟩⟩
  recip_inter _ _ := hom_ext fun _ _ => Iff.rfl
  inter_idem _ := hom_ext fun _ _ => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  inter_comm _ _ := hom_ext fun _ _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  inter_assoc _ _ _ := hom_ext fun _ _ => ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
  semidistrib R S T := hom_ext fun x z =>
    ⟨fun ⟨y, hR, hS, hT⟩ => ⟨⟨⟨y, hR, hS⟩, ⟨y, hR, hS, hT⟩⟩, ⟨y, hR, hT⟩⟩,
     fun ⟨⟨_, ⟨y, hR, hS, hT⟩⟩, _⟩ => ⟨y, hR, hS, hT⟩⟩
  modular R S T := hom_ext fun x z =>
    ⟨fun ⟨⟨y, hR, hS⟩, hT⟩ => ⟨⟨⟨y, hR, hS⟩, hT⟩, ⟨y, ⟨hR, ⟨z, hT, hS⟩⟩, hS⟩⟩,
     fun ⟨⟨hRS, hT⟩, _⟩ => ⟨hRS, hT⟩⟩

@[simp] public theorem inter_apply {A B : RelSet.{u}} (R S : A ⟶ B) (x : A.carrier)
    (y : B.carrier) : (R ∩ S) x y = (R x y ∧ S x y) := rfl

/-- The allegory order is exactly relational inclusion. -/
public theorem le_iff {A B : RelSet.{u}} {R S : A ⟶ B} : R ⊑ S ↔ ∀ x y, R x y → S x y := by
  constructor
  · intro h x y hR
    have e : (R x y ∧ S x y) = R x y := congrFun (congrFun h x) y
    have hand : R x y ∧ S x y := by rw [e]; exact hR
    exact hand.2
  · intro h
    exact hom_ext fun x y => ⟨fun hRS => hRS.1, fun hR => ⟨hR, h x y hR⟩⟩

/-- The graph relation `y = f x` of an ordinary function `f`. -/
@[expose] public def graph {A B : RelSet.{u}} (f : A.carrier → B.carrier) : A ⟶ B := fun x y => y = f x

/-- The coreflexive of a predicate, `{(a,a)∣P(a)}`: a `def`, so a relation built from it prints
    this name where Lean's pointwise lambda would print. -/
@[expose] public def corefl {A : RelSet.{u}} (P : A.carrier → Prop) : A ⟶ A := fun x y => x = y ∧ P x

@[simp] public theorem recip_apply {A B : RelSet.{u}} (R : A ⟶ B) (y : B.carrier) (x : A.carrier) :
    R° y x = R x y := rfl

@[expose] public instance : DistributiveAllegory RelSet.{u} :=
  { (inferInstance : Allegory RelSet) with
    zero := fun _ _ => False
    union := fun R S => fun x y => R x y ∨ S x y
    zero_comp := fun R => hom_ext fun x z => ⟨fun ⟨_, hf, _⟩ => hf, fun hf => hf.elim⟩
    comp_zero := fun R => hom_ext fun x z => ⟨fun ⟨_, _, hf⟩ => hf, fun hf => hf.elim⟩
    union_idem := fun R => hom_ext fun x y => ⟨fun h => h.elim id id, fun h => Or.inl h⟩
    union_comm := fun R S => hom_ext fun x y => ⟨fun h => h.elim Or.inr Or.inl,
      fun h => h.elim Or.inr Or.inl⟩
    union_assoc := fun R S T => hom_ext fun x y =>
      ⟨fun h => h.elim (fun hR => Or.inl (Or.inl hR)) (fun h' => h'.elim (fun hS => Or.inl (Or.inr hS)) Or.inr),
       fun h => h.elim (fun h' => h'.elim Or.inl (fun hS => Or.inr (Or.inl hS))) (fun hT => Or.inr (Or.inr hT))⟩
    union_inter_absorb := fun R S => hom_ext fun x y =>
      ⟨fun h => h.elim id (fun h2 => h2.2), fun hR => Or.inl hR⟩
    inter_union_absorb := fun R S => hom_ext fun x y => ⟨fun h => h.2, fun hR => ⟨Or.inl hR, hR⟩⟩
    comp_union_distrib := fun R S T => hom_ext fun x z =>
      ⟨fun ⟨y, hR, hST⟩ => hST.elim (fun hS => Or.inl ⟨y, hR, hS⟩) (fun hT => Or.inr ⟨y, hR, hT⟩),
       fun h => h.elim (fun ⟨y, hR, hS⟩ => ⟨y, hR, Or.inl hS⟩) (fun ⟨y, hR, hT⟩ => ⟨y, hR, Or.inr hT⟩)⟩
    inter_union_distrib := fun R S T => hom_ext fun x y =>
      ⟨fun ⟨hR, hST⟩ => hST.elim (fun hS => Or.inl ⟨hR, hS⟩) (fun hT => Or.inr ⟨hR, hT⟩),
       fun h => h.elim (fun ⟨hR, hS⟩ => ⟨hR, Or.inl hS⟩) (fun ⟨hR, hT⟩ => ⟨hR, Or.inr hT⟩)⟩
    zero_union := fun R => hom_ext fun x y => ⟨fun h => h.elim (fun hf => hf.elim) id, fun hR => Or.inr hR⟩ }

@[simp] public theorem union_apply {A B : RelSet.{u}} (R S : A ⟶ B) (x : A.carrier)
    (y : B.carrier) : (R ∪ S) x y = (R x y ∨ S x y) := rfl

/-- The product action `R × S` in `Rel(Set)`: `(x,y) ~ (x',y')` iff `R x x'` and `S y y'`. -/
@[expose] public def rprodMap {A a' B b' : RelSet.{u}} (R : A ⟶ a') (S : B ⟶ b') :
    (⟨A.carrier × B.carrier⟩ : RelSet.{u}) ⟶ ⟨a'.carrier × b'.carrier⟩ :=
  fun p q => R p.1 q.1 ∧ S p.2 q.2

/-- The sum type `a ⊕ b` with the injection graphs satisfies the five coproduct equations of
    §2.214 — Rel(Set)'s concrete coproducts, feeding the `junc`/`sumMap` calculus of `A5_3`. -/
@[expose] public def sumCop (A B : RelSet.{u}) : Coproduct (⟨A.carrier ⊕ B.carrier⟩ : RelSet.{u}) A B where
  u₁ := graph Sum.inl
  u₂ := graph Sum.inr
  u₁_self_comp_recip := hom_ext fun x x' =>
    ⟨fun ⟨_, h1, h2⟩ => Sum.inl.inj (h1.symm.trans h2),
     fun h => ⟨Sum.inl x, rfl, congrArg Sum.inl h⟩⟩
  u₁_u₂_recip := hom_ext fun x y =>
    ⟨fun ⟨_, h1, h2⟩ => (nomatch h1.symm.trans h2), False.elim⟩
  u₂_u₁_recip := hom_ext fun y x =>
    ⟨fun ⟨_, h1, h2⟩ => (nomatch h1.symm.trans h2), False.elim⟩
  u₂_self_comp_recip := hom_ext fun y y' =>
    ⟨fun ⟨_, h1, h2⟩ => Sum.inr.inj (h1.symm.trans h2),
     fun h => ⟨Sum.inr y, rfl, congrArg Sum.inr h⟩⟩
  recip_union_eq_id := hom_ext fun s s' =>
    ⟨fun h => h.elim (fun ⟨x, h1, h2⟩ => h1.trans h2.symm) (fun ⟨y, h1, h2⟩ => h1.trans h2.symm),
     fun h => by
      have h' : s = s' := h
      subst h'
      cases s with
      | inl x => exact Or.inl ⟨x, rfl, rfl⟩
      | inr y => exact Or.inr ⟨y, rfl, rfl⟩⟩

/-- Rel(Set) is POSITIVE (§2.215): `PEmpty` is the coterminator and `⊕` the chosen coproduct.
    Extends the `DistributiveAllegory` instance above so there is one `Allegory RelSet` underneath. -/
@[expose] public instance : PositiveAllegory RelSet.{u} :=
  { (inferInstance : DistributiveAllegory RelSet) with
    coterm := ⟨PEmpty.{u + 1}⟩
    coprod := fun A B => ⟨A.carrier ⊕ B.carrier⟩
    has_coproduct := sumCop }

/-- `⊤ : a ⟶ b` in `Rel(Set)`, constructively: a hom here IS a predicate, so the greatest one
    is the predicate that holds everywhere.  The abstract `topMor` of a unitary allegory picks
    the two unit projections with `Exists.choose` and is therefore noncomputable; this one costs
    no choice, so a statement that names `⊤` stays axiom-clean. -/
@[expose] public def relTop {A B : RelSet.{u}} : A ⟶ B := fun _ _ => True

/-- Relational pairing `⟨R,S⟩` in `Rel(Set)`: `x ↦ (y,z)` iff `R x y` and `S x z` — the
    graph-level form of (5.1), free of the abstract `topMor` inside `RelProd.tab`
    (which `pair_eq_rpair` below shows it equals). -/
@[expose] public def rpair {C A B : RelSet.{u}} (R : C ⟶ A) (S : C ⟶ B) :
    C ⟶ (⟨A.carrier × B.carrier⟩ : RelSet.{u}) :=
  fun x p => R x p.1 ∧ S x p.2

end RelSet
end Freyd.Alg
end
