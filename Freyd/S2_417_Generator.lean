/-
  Freyd & Scedrov, *Categories and Allegories* §2.417
  "A generator (as opposed to a progenitor) is not good enough."

  Freyd modifies the §1.96(10) counterexample to produce a complete effective
  distributive allegory `Rel(C)` that HAS a generator yet is NOT a power allegory.

  This file formalizes the reachable *core*:

    (1)  The category `C`  (§2.417, generalizing §1.96(10)).
         Objects are quadruples `⟨S, s : S → S, A ⊆ L, f : L → S → S⟩` over a fixed
         "label universe" `L`.  Writing `xᵃ` (`exp X x a`) for `f a x` when `a ∈ A` and
         `s x` otherwise, a map `g : S → S'` is one that commutes with every exponent:
         `g (xᵃ) = (g x)ᵃ`.  We prove `Cat (Obj L)`.

    (2)  The GENERATOR witness and the separation argument.
         `G = ⟨{u,v}, s, ∅, ∅⟩` with `s u = s v = v`.  For equivariant relations
         `R, R' : S → S'` in `Rel(C)` with `R ⊄ R'`, pick `x,y` with `xRy`, `¬xR'y` and
         set `T : G → S`, `w T z  ⟺  (w = v ∨ z = x)`.  Then `u (T⊚R) y` but `¬ u (T⊚R') y`,
         so the relations out of `G` separate `R` from `R'`: `G` generates `Rel(C)`.
         Headline: `S2_417.G_generates`.

  On the map condition.  §1.96(10) quantifies "for all `s` in the universe"; there the
  default (`a ∉ A`) is the identity, so labels outside `A ∪ A'` impose nothing.  §2.417
  replaces the identity default by a chosen endomap `s`, and the printed "`a ∈ A ∪ A'`" is
  completed here to "for all labels `a ∈ L`" (the §1.96(10) reading): for `a ∉ A ∪ A'` this
  says `g (s x) = s' (g x)`, which is exactly what makes composition preserve the map
  condition, i.e. what makes `C` a category.

  On relations.  A morphism `S → S'` of `Rel(C)` is a subobject of the product `S × S'` in
  `C`, i.e. a relation on the carriers CLOSED under the joint action
  `(x,y) ↦ (xᵃ, yᵃ)` (`CRel.equiv`).  We work with these equivariant relations directly
  (as the task permits) rather than reconstructing products; the book's `T` is equivariant
  because `G`'s exponents are constantly `v`.

  Target (3) — "the only object of `C` with a power object is the coterminator, hence
  `Rel(C)` is not a power allegory" — is left OPEN: the repo has a `PowerAllegory` class but
  no `Progenitor`/generator class, and the refutation needs power objects in `C` plus the
  full `Rel(C)` allegory, out of this file's scope.

  MATHLIB-FREE.  Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

import Freyd.S1_1

namespace Freyd.S2_417
open Freyd

-- Classical decidability so `exp` can branch on the Prop-valued membership `A a`.
attribute [local instance] Classical.propDecidable

variable {L : Type}

/-- An object of `C` (§2.417): a carrier `S`, an endomap `s`, a subset `A ⊆ L` of active
    labels, and operations `f a : S → S`.  `f a` is read only for `a ∈ A`; off `A` it is junk. -/
structure Obj (L : Type) where
  S : Type
  s : S → S
  A : L → Prop
  f : L → S → S

/-- The exponent `xᵃ`: `f a x` when the label `a` is active (`a ∈ A`), else the default `s x`. -/
noncomputable def exp (X : Obj L) (x : X.S) (a : L) : X.S :=
  if X.A a then X.f a x else X.s x

/-- A map of `C`: a carrier function commuting with every exponent
    (`g (xᵃ) = (g x)ᵃ` for all labels `a ∈ L`; see the header on the quantifier). -/
structure CHom (X Y : Obj L) where
  g : X.S → Y.S
  equiv : ∀ (a : L) (x : X.S), g (exp X x a) = exp Y (g x) a

@[ext] theorem CHom.ext {X Y : Obj L} {φ ψ : CHom X Y} (h : φ.g = ψ.g) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

/-- **§2.417 (target 1).**  `C` is a category. -/
instance catC : Cat (Obj L) where
  Hom X Y := CHom X Y
  id X := ⟨fun x => x, fun _ _ => rfl⟩
  comp := fun {X _ _} φ ψ => ⟨fun x => ψ.g (φ.g x), fun a x => by
    show ψ.g (φ.g (exp X x a)) = exp _ (ψ.g (φ.g x)) a
    rw [φ.equiv, ψ.equiv]⟩
  id_comp _ := CHom.ext rfl
  comp_id _ := CHom.ext rfl
  assoc _ _ _ := CHom.ext rfl

/-! ## §2.417  Relations of `Rel(C)` and the generator -/

/-- A morphism `X → Y` of `Rel(C)`: an equivariant relation, i.e. a subobject of the product
    `X × Y` in `C`.  Concretely a relation on the carriers closed under the joint action
    `(x,y) ↦ (xᵃ, yᵃ)`. -/
structure CRel (X Y : Obj L) where
  rel   : X.S → Y.S → Prop
  equiv : ∀ (a : L) (x : X.S) (y : Y.S), rel x y → rel (exp X x a) (exp Y y a)

/-- Relational composition in diagram order (`R⊚S`: first `R : X → Y`, then `S : Y → Z`);
    the composite is again equivariant. -/
def CRel.comp {X Y Z : Obj L} (R : CRel X Y) (S : CRel Y Z) : CRel X Z where
  rel x z := ∃ y, R.rel x y ∧ S.rel y z
  equiv a x z := by
    rintro ⟨y, hxy, hyz⟩
    exact ⟨exp Y y a, R.equiv a x y hxy, S.equiv a y z hyz⟩

/-- Containment of relations (`R ⊆ R'`). -/
def CRel.le {X Y : Obj L} (R R' : CRel X Y) : Prop := ∀ x y, R.rel x y → R'.rel x y

/-- The two-element carrier `{u, v}` of the generator. -/
inductive GCar | u | v

/-- The generator object `G = ⟨{u,v}, s, ∅, ∅⟩` with `s u = s v = v` (§2.417). -/
def G (L : Type) : Obj L where
  S := GCar
  s := fun _ => GCar.v
  A := fun _ => False
  f := fun _ x => x

/-- Every exponent in `G` is constantly `v` (since `G` has no active labels). -/
theorem exp_G (a : L) (w : GCar) : exp (G L) w a = GCar.v := by
  have hna : ¬ (G L).A a := fun h => h
  rw [exp, if_neg hna]; rfl

/-- Given `x₀ ∈ S`, the separating relation `T : G → S`, `w T z ⟺ (w = v ∨ z = x₀)` (§2.417).
    Equivariant because `wᵃ = v` for every label, and `v` relates to everything. -/
def sepRel {X : Obj L} (x₀ : X.S) : CRel (G L) X where
  rel w z := w = GCar.v ∨ z = x₀
  equiv a w z := by
    intro _; exact Or.inl (exp_G a w)

/-- Classical extraction of a separating pair from `¬ R ⊆ R'`. -/
theorem exists_witness {X Y : Obj L} {R R' : CRel X Y} (h : ¬ R.le R') :
    ∃ x y, R.rel x y ∧ ¬ R'.rel x y := by
  apply Classical.byContradiction
  intro hcon
  apply h
  intro x y hxy
  apply Classical.byContradiction
  intro hy
  exact hcon ⟨x, y, hxy, hy⟩

/-- **§2.417 separation.**  For equivariant `R, R' : X → Y` with `R ⊄ R'`, some relation `T`
    out of `G` distinguishes them: `¬ (T⊚R) ⊆ (T⊚R')`. -/
theorem generator_separates {X Y : Obj L} (R R' : CRel X Y) (h : ¬ R.le R') :
    ∃ T : CRel (G L) X, ¬ (T.comp R).le (T.comp R') := by
  obtain ⟨x₀, y₀, hRxy, hnR'xy⟩ := exists_witness h
  refine ⟨sepRel x₀, fun hle => ?_⟩
  have hTR : ((sepRel x₀).comp R).rel GCar.u y₀ := ⟨x₀, Or.inr rfl, hRxy⟩
  obtain ⟨z, hz, hzR'⟩ := hle GCar.u y₀ hTR
  rcases hz with hv | hzx
  · exact GCar.noConfusion hv
  · exact hnR'xy (hzx ▸ hzR')

/-- `Gobj` generates `Rel(C)`: `R ⊆ R'` is detected by the relations out of `Gobj`. -/
def Generates (Gobj : Obj L) : Prop :=
  ∀ {X Y : Obj L} (R R' : CRel X Y),
    (∀ T : CRel Gobj X, (T.comp R).le (T.comp R')) → R.le R'

/-- **§2.417 (target 2, headline).**  `G` is a generator for `Rel(C)`. -/
theorem G_generates : Generates (G L) := by
  intro X Y R R' hT
  apply Classical.byContradiction
  intro h
  obtain ⟨T, hTneg⟩ := generator_separates R R' h
  exact hTneg (hT T)
