/-
  The concrete allegory **Rel(Set)** — the SET MODEL in which Bird & de Moor's relational
  programs actually live and run.

  An object is a Lean type (bundled as `RelSet.mk` so it is a genuinely distinct type from
  `Type u` — otherwise the ambient `Cat (Type u)` instance would shadow this one), and a morphism
  `a ⟶ b` is an ordinary binary relation `a.carrier → b.carrier → Prop`.  Composition is in
  DIAGRAM ORDER (`R ≫ S` = first `R` then `S`), matching the whole Freyd/AoP development.

  This file assembles Rel(Set) as an instance of the full allegory stack the concrete case
  studies need — `Allegory`, `DistributiveAllegory`, `DivisionAllegory`,
  `LocallyCompleteDistributiveAllegory`, `PowerAllegory`, `UnguardedPowerAllegory`,
  `UnguardedPowerLCDA`, `TabularAllegory`, `UnitaryAllegory`,
  `TabularUnitaryDivisionAllegory` — so that every abstract theorem of chapters 4–10
  (catamorphisms, `min`/`thin`, dynamic programming, greedy) can be instantiated on real
  datatypes.  Everything here is mathlib-free: pure `Prop`, `∧`, `∨`, `∃`, `∀`, `=`.
-/
module

public import AOP.A6_2
public import AOP.A5_5

-- The pointwise instance proofs name the relation/element they quantify (documenting each law)
-- even where the term-mode witness does not reference the binder; silence that lint file-wide.
set_option linter.unusedVariables false

universe u v

namespace Freyd.Alg

open Freyd

/-- An object of the allegory `Rel(Set)`: a bundled Lean type.  Bundled (not a bare `Type u`)
    so these instances attach here and do NOT collide with the ambient category on `Type u`. -/
public structure RelSet : Type (u + 1) where
  carrier : Type u

namespace RelSet

@[expose] public instance : Cat RelSet.{u} where
  Hom a b := a.carrier → b.carrier → Prop
  id _ := fun x y => x = y
  comp R S := fun x z => ∃ y, R x y ∧ S y z
  id_comp R := funext fun x => funext fun y => propext ⟨fun ⟨_, h, hR⟩ => h ▸ hR,
    fun hR => ⟨x, rfl, hR⟩⟩
  comp_id R := funext fun x => funext fun y => propext ⟨fun ⟨_, hR, h⟩ => h ▸ hR,
    fun hR => ⟨y, hR, rfl⟩⟩
  assoc R S T := funext fun x => funext fun w => propext
    ⟨fun ⟨y, ⟨z, hR, hS⟩, hT⟩ => ⟨z, hR, y, hS, hT⟩, fun ⟨z, hR, y, hS, hT⟩ => ⟨y, ⟨z, hR, hS⟩, hT⟩⟩

@[simp] public theorem comp_apply {a b c : RelSet.{u}} (R : a ⟶ b) (S : b ⟶ c) (x : a.carrier)
    (z : c.carrier) : (R ≫ S) x z = ∃ y, R x y ∧ S y z := rfl

@[simp] public theorem id_apply {a : RelSet.{u}} (x y : a.carrier) : (Cat.id a) x y = (x = y) := rfl

/-- Extensionality for `Rel(Set)` morphisms: relations are equal iff pointwise equivalent. -/
public theorem hom_ext {a b : RelSet.{u}} {R S : a ⟶ b} (h : ∀ x y, R x y ↔ S x y) : R = S :=
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

/-- The allegory order is exactly relational inclusion. -/
public theorem le_iff {a b : RelSet.{u}} {R S : a ⟶ b} : R ⊑ S ↔ ∀ x y, R x y → S x y := by
  constructor
  · intro h x y hR
    have e : (R x y ∧ S x y) = R x y := congrFun (congrFun h x) y
    have hand : R x y ∧ S x y := by rw [e]; exact hR
    exact hand.2
  · intro h
    exact hom_ext fun x y => ⟨fun hRS => hRS.1, fun hR => ⟨hR, h x y hR⟩⟩

/-! ### Graph of a function — the source of every `Map` used below

  In `Rel(Set)` a MAP (entire + simple relation) is exactly the graph of a function.  The power
  classifier and the two tabulation legs are all graphs, so `graph_map` discharges every `Map`
  obligation in one place. -/

/-- The graph relation `y = f x` of an ordinary function `f`. -/
@[expose] public def graph {a b : RelSet.{u}} (f : a.carrier → b.carrier) : a ⟶ b := fun x y => y = f x

theorem graph_apply {a b : RelSet.{u}} (f : a.carrier → b.carrier) (x : a.carrier)
    (y : b.carrier) : graph f x y = (y = f x) := rfl

theorem recip_apply {a b : RelSet.{u}} (R : a ⟶ b) (y : b.carrier) (x : a.carrier) :
    R° y x = R x y := rfl

public theorem graph_simple {a b : RelSet.{u}} (f : a.carrier → b.carrier) : Simple (graph f) := by
  show (graph f)° ≫ graph f ⊑ Cat.id b
  rw [le_iff]; intro y y' h
  obtain ⟨x, hy, hy'⟩ := h
  exact hy.trans hy'.symm

public theorem graph_entire {a b : RelSet.{u}} (f : a.carrier → b.carrier) : Entire (graph f) := by
  show dom (graph f) = Cat.id a
  apply hom_ext; intro x x'
  exact ⟨fun h => h.1, fun h => ⟨h, f x, rfl, congrArg f h⟩⟩

public theorem graph_map {a b : RelSet.{u}} (f : a.carrier → b.carrier) : Map (graph f) :=
  ⟨graph_entire f, graph_simple f⟩

/-- Diagram-order composition of two graphs is the graph of the composite function. -/
public theorem graph_comp {a b c : RelSet.{u}} (f : a.carrier → b.carrier) (g : b.carrier → c.carrier) :
    graph f ≫ graph g = graph (fun x => g (f x)) :=
  hom_ext fun x z => ⟨fun ⟨y, hy, hz⟩ => hz.trans (congrArg g hy), fun hz => ⟨f x, rfl, hz⟩⟩

/-- Precomposing an ARBITRARY relation with a graph just renames the source point. -/
public theorem graph_comp_left {a b c : RelSet.{u}} (f : a.carrier → b.carrier) (S : b ⟶ c) :
    graph f ≫ S = fun x z => S (f x) z :=
  hom_ext fun x z => ⟨fun ⟨y, hy, hS⟩ => hy ▸ hS, fun h => ⟨f x, rfl, h⟩⟩

/-- The graph of the identity function is the identity relation.  Not `rfl`: `graph` orients its
    equation as `y = f x` and the identity as `x = y`. -/
theorem graph_id (a : RelSet.{u}) : graph (fun x : a.carrier => x) = 𝟙 a :=
  hom_ext fun _ _ => ⟨Eq.symm, Eq.symm⟩

/-! ### Distributive structure: `𝟘` = empty relation, `∪` = union -/

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

/-! ### Division: `R / S` = the right residual `∀ z, S y z → R x z` -/

@[expose] public instance : DivisionAllegory RelSet.{u} :=
  { (inferInstance : DistributiveAllegory RelSet) with
    div := fun R S => fun x y => ∀ z, S y z → R x z
    div_comp_le := fun R S => le_iff.mpr fun x z h => by
      obtain ⟨y, hd, hs⟩ := h; exact hd z hs
    le_div := fun T R S h => le_iff.mpr fun x y hT z hSyz => le_iff.mp h x z ⟨y, hT, hSyz⟩ }

/-! ### Local completeness: arbitrary joins are existentials -/

@[expose] public instance : LocallyCompleteDistributiveAllegory RelSet.{u} :=
  { (inferInstance : DistributiveAllegory RelSet) with
    Sup := fun P => fun x y => ∃ R, P R ∧ R x y
    le_Sup := fun h => le_iff.mpr fun x y hR => ⟨_, h, hR⟩
    Sup_le := fun h => le_iff.mpr fun x y hs => by
      obtain ⟨R, hPR, hR⟩ := hs; exact le_iff.mp (h R hPR) x y hR
    comp_Sup_distrib := fun R P => hom_ext fun x z =>
      ⟨fun ⟨y, hR, S, hPS, hS⟩ => ⟨R ≫ S, ⟨S, hPS, rfl⟩, y, hR, hS⟩,
       fun ⟨T, ⟨S, hPS, hTeq⟩, hTxz⟩ => by
        subst hTeq; obtain ⟨y, hR, hS⟩ := hTxz; exact ⟨y, hR, S, hPS, hS⟩⟩
    inter_Sup_distrib := fun R P => hom_ext fun x y =>
      ⟨fun ⟨hR, S, hPS, hS⟩ => ⟨R ∩ S, ⟨S, hPS, rfl⟩, hR, hS⟩,
       fun ⟨T, ⟨S, hPS, hTeq⟩, hTxy⟩ => by
        subst hTeq; exact ⟨hTxy.1, S, hPS, hTxy.2⟩⟩ }

/-! ### Power objects: `[b]` = the powerset `b → Prop`, `∋` = membership -/

/-- The power object of `b`: its carrier is the powerset `b.carrier → Prop`. -/
@[expose] public def pow (b : RelSet.{u}) : RelSet.{u} := ⟨b.carrier → Prop⟩

/-- Membership `∋_b : [b] ⟶ b` in `Rel(Set)`: `P ∋ y` iff `y ∈ P`. -/
@[expose] public def epsRel (b : RelSet.{u}) : pow b ⟶ b := fun P y => P y

/-- The classifier of a relation `R : c ⟶ b` — the graph of `x ↦ {y | R x y}`; this is the
    transpose `ΛR`, and it witnesses that `∋` classifies EVERY relation. -/
@[expose] public def classifier {b c : RelSet.{u}} (R : c ⟶ b) : c ⟶ pow b := graph fun x => fun y => R x y

public theorem classifier_comp_eps {b c : RelSet.{u}} (R : c ⟶ b) : classifier R ≫ epsRel b = R := by
  apply hom_ext; intro x y
  exact ⟨fun ⟨P, hP, hPy⟩ => by rw [hP] at hPy; exact hPy, fun hR => ⟨fun y => R x y, rfl, hR⟩⟩

@[expose] public instance : PowerAllegory RelSet.{u} :=
  { (inferInstance : DivisionAllegory RelSet) with
    powerObj := pow
    eps := epsRel
    eps_straight := fun b => by
      show epsRel b /ₛ epsRel b ⊑ Cat.id (pow b)
      rw [le_iff]; intro P Q h
      obtain ⟨h1, h2⟩ := h
      funext y; exact propext ⟨h2 y, h1 y⟩
    eps_thick := fun R _ => ⟨classifier R, graph_map _, classifier_comp_eps R⟩ }

@[expose] public instance : UnguardedPowerAllegory RelSet.{u} :=
  { (inferInstance : PowerAllegory RelSet) with
    eps_thick_all := fun R => ⟨classifier R, graph_map _, classifier_comp_eps R⟩ }

@[expose] public instance : UnguardedPowerLCDA RelSet.{u} :=
  { (inferInstance : LocallyCompleteDistributiveAllegory RelSet),
    (inferInstance : UnguardedPowerAllegory RelSet) with }

/-! ### Tabularity: every relation is the joint image of its graph-as-a-set -/

@[expose] public instance : TabularAllegory RelSet.{u} :=
  { (inferInstance : Allegory RelSet) with
    tabular := fun {a b} R =>
      ⟨⟨{ p : a.carrier × b.carrier // R p.1 p.2 }⟩, graph (fun p => p.1.1), graph (fun p => p.1.2),
        graph_map _, graph_map _,
        (by
          apply hom_ext; intro x y
          exact ⟨fun hR => ⟨⟨(x, y), hR⟩, rfl, rfl⟩,
            fun h => by obtain ⟨p, hx, hy⟩ := h; subst hx; subst hy; exact p.2⟩),
        (by
          apply hom_ext; intro p p'
          constructor
          · intro h
            obtain ⟨⟨x, hx1, hx2⟩, ⟨y, hy1, hy2⟩⟩ := h
            exact Subtype.ext (Prod.ext_iff.mpr ⟨hx1.symm.trans hx2, hy1.symm.trans hy2⟩)
          · intro h; subst h; exact ⟨⟨p.1.1, rfl, rfl⟩, ⟨p.1.2, rfl, rfl⟩⟩)⟩ }

/-! ### A unit: `PUnit` is a partial unit and every object maps entirely onto it -/

@[expose] public instance : UnitaryAllegory RelSet.{u} :=
  { (inferInstance : Allegory RelSet) with
    unit_obj := ⟨PUnit⟩
    unit_prop :=
      ⟨fun R => le_iff.mpr fun x y _ => Subsingleton.elim x y,
       fun a => ⟨fun _ _ => True, by
        show dom (fun _ _ => True) = Cat.id a
        apply hom_ext; intro x x'
        exact ⟨fun h => h.1, fun h => ⟨h, PUnit.unit, trivial, trivial⟩⟩⟩⟩ }

@[expose] public instance : Freyd.Alg.TabularUnitaryDivisionAllegory RelSet.{u} :=
  { (inferInstance : TabularAllegory RelSet),
    (inferInstance : UnitaryAllegory RelSet),
    (inferInstance : DivisionAllegory RelSet) with }

/-! ### Two elementary `Rel(Set)` map facts + the product action, shared by every datatype engine

  `entire_total`/`simple_uniq`/`rprodMap` were re-proved verbatim in `A6_ConsList`, `A6_SnocList` and
  `A6_1_Digits`; hoisted here (the base each engine imports) so a single copy serves all three. -/

/-- An entire relation relates every point to something. -/
public theorem entire_total {a b : RelSet.{u}} {R : a ⟶ b} (h : Entire R) (x : a.carrier) :
    ∃ y, R x y := by
  have hd : (dom R) x x := by
    have e : (dom R) x x = (Cat.id a) x x := congrFun (congrFun h x) x
    rw [e]; rfl
  obtain ⟨_, y, hy, _⟩ := hd
  exact ⟨y, hy⟩

/-- A simple relation is single-valued. -/
public theorem simple_uniq {a b : RelSet.{u}} {R : a ⟶ b} (h : Simple R) {x : a.carrier}
    {y y' : b.carrier} (hy : R x y) (hy' : R x y') : y = y' :=
  le_iff.mp h y y' ⟨x, hy, hy'⟩

/-- The product action `R × S` in `Rel(Set)`: `(x,y) ~ (x',y')` iff `R x x'` and `S y y'`. -/
@[expose] public def rprodMap {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b') :
    (⟨a.carrier × b.carrier⟩ : RelSet.{u}) ⟶ ⟨a'.carrier × b'.carrier⟩ :=
  fun p q => R p.1 q.1 ∧ S p.2 q.2

theorem rprodMap_apply {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b')
    (p : a.carrier × b.carrier) (q : a'.carrier × b'.carrier) :
    rprodMap R S p q = (R p.1 q.1 ∧ S p.2 q.2) := rfl

/-- Converse acts componentwise on the product action: `(R × S)° = R° × S°`. -/
public theorem rprodMap_recip {a a' b b' : RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b') :
    (rprodMap R S)° = rprodMap R° S° := rfl

/-- The product action on two graphs is the graph of the product function — the fact that makes
    every structural isomorphism of the cartesian product a graph, hence a map. -/
theorem rprodMap_graph {a a' b b' : RelSet.{u}} (f : a.carrier → a'.carrier)
    (g : b.carrier → b'.carrier) :
    rprodMap (graph f) (graph g)
      = (graph (fun p : a.carrier × b.carrier => (f p.1, g p.2))
          : (⟨a.carrier × b.carrier⟩ : RelSet.{u}) ⟶ (⟨a'.carrier × b'.carrier⟩ : RelSet.{u})) := by
  apply hom_ext; intro p q
  exact ⟨fun h => Prod.ext_iff.mpr ⟨h.1, h.2⟩,
    fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- The sum type `a ⊕ b` with the injection graphs satisfies the five coproduct equations of
    §2.214 — Rel(Set)'s concrete coproducts, feeding the `junc`/`sumMap` calculus of `A5_3`. -/
@[expose] public def sumCop (a b : RelSet.{u}) : Coproduct (⟨a.carrier ⊕ b.carrier⟩ : RelSet.{u}) a b where
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

end RelSet
end Freyd.Alg
