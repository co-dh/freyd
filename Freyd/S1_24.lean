/-
  Freyd & Scedrov, *Categories and Allegories* §1.24  Basic examples and constructions.

  §1.242  CATEGORY OF GROUPS: objects are groups; morphisms are group homomorphisms.
  §1.245  PRE-ORDERING as a category: objects = elements, at most one morphism x→y iff x ≤ y;
          functors between such categories = order-preserving maps.
  §1.263  POINTED SETS = counter-slice 1/𝒮; the category whose objects are functions
          from a one-element set.
  §1.271  RIGHT A-SETS: covariant functors A → 𝒮 in single-sorted concrete form.
  §1.273  LEFT A-SETS: contravariant functors A → 𝒮 (= right A^op-sets).
  §1.283  STRONGLY CONNECTED category: every ordered pair of objects admits a morphism.
  §1.284  PREFUNCTOR: preserves composition, not necessarily identities.
-/

import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_26
import Freyd.S1_41
import Freyd.S1_55

open Freyd

universe v u w

namespace Freyd

/-! ## §1.242  Category of groups -/

/-- A group structure (over a carrier type): multiplication, inverse, unit,
    with the usual axioms.  We avoid clashing with Lean's built-in `Group`. -/
structure GroupObj where
  carrier  : Type u
  mul      : carrier → carrier → carrier
  one      : carrier
  inv      : carrier → carrier
  mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c)
  one_mul  : ∀ a : carrier, mul one a = a
  mul_one  : ∀ a : carrier, mul a one = a
  mul_inv  : ∀ a : carrier, mul (inv a) a = one

/-- A group homomorphism between two `GroupObj`s. -/
structure GroupHom (G H : GroupObj) where
  toFun    : G.carrier → H.carrier
  map_mul  : ∀ a b : G.carrier, toFun (G.mul a b) = H.mul (toFun a) (toFun b)
  map_one  : toFun G.one = H.one

/-- Composition of group homomorphisms. -/
def GroupHom.comp {G H K : GroupObj} (f : GroupHom G H) (g : GroupHom H K) : GroupHom G K where
  toFun a := g.toFun (f.toFun a)
  map_mul a b := by rw [f.map_mul, g.map_mul]
  map_one := by rw [f.map_one, g.map_one]

/-- Identity group homomorphism. -/
def GroupHom.id (G : GroupObj) : GroupHom G G where
  toFun := fun a => a
  map_mul _ _ := rfl
  map_one := rfl

@[ext]
theorem GroupHom.ext {G H : GroupObj} {f g : GroupHom G H} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; simp at h; subst h; rfl

/-- **§1.242** The CATEGORY OF GROUPS: objects = `GroupObj`, morphisms = `GroupHom`. -/
instance groupCat : Cat.{u} GroupObj where
  Hom G H := GroupHom G H
  id G := GroupHom.id G
  comp f g := f.comp g
  id_comp _ := GroupHom.ext rfl
  comp_id _ := GroupHom.ext rfl
  assoc _ _ _ := GroupHom.ext rfl

/-! ## §1.245  Pre-ordered set as a category -/

/-- A pre-ordering on a type: reflexive and transitive relation. -/
structure PreOrd where
  carrier  : Type u
  le       : carrier → carrier → Prop
  le_refl  : ∀ a : carrier, le a a
  le_trans : ∀ {a b c : carrier}, le a b → le b c → le a c

/-- The unique morphism type x→y in a pre-order category (a proof that x ≤ y). -/
def PreOrdHom (P : PreOrd) (x y : P.carrier) : Type := PLift (P.le x y)

/-- **§1.245** The pre-ordered set P as a category: one morphism x→y iff x ≤ y. -/
instance preOrderCat (P : PreOrd) : Cat.{0} P.carrier where
  Hom x y := PLift (P.le x y)
  id x := ⟨P.le_refl x⟩
  comp h k := ⟨P.le_trans h.down k.down⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- An order-preserving map between pre-orders is a functor between their categories (§1.245). -/
def orderPreservingFunctor (P Q : PreOrd) (f : P.carrier → Q.carrier)
    (hf : ∀ {a b : P.carrier}, P.le a b → Q.le (f a) (f b)) :
    @Functor P.carrier Q.carrier (preOrderCat P) (preOrderCat Q) where
  obj := f
  map h := ⟨hf h.down⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## §1.263  Pointed sets (the counter-slice 1/𝒮) -/

/-- A pointed set: a set together with a distinguished element (the "base point").
    This is the counter-slice 1/𝒮: an object of 1/𝒮 is a function 1 → S, i.e., a choice of
    base point in S. (§1.263) -/
structure PointedSet where
  carrier   : Type u
  basePoint : carrier

/-- A morphism of pointed sets: a function preserving the base point. -/
structure PointedHom (X Y : PointedSet) where
  toFun     : X.carrier → Y.carrier
  map_point : toFun X.basePoint = Y.basePoint

@[ext]
theorem PointedHom.ext {X Y : PointedSet} {f g : PointedHom X Y} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; simp at h; subst h; rfl

/-- **§1.263** The category of POINTED SETS (= counter-slice 1/𝒮). -/
instance pointedSetCat : Cat.{u} PointedSet where
  Hom X Y := PointedHom X Y
  id X := ⟨fun a => a, rfl⟩
  comp f g := ⟨fun a => g.toFun (f.toFun a), by simp [f.map_point, g.map_point]⟩
  id_comp _ := PointedHom.ext rfl
  comp_id _ := PointedHom.ext rfl
  assoc _ _ _ := PointedHom.ext rfl

/-! ## §1.271  Right A-sets -/

/-- A RIGHT A-SET (§1.271): a set X with a "source" map X → |A| and a partial action
    x · a defined when x□ = □a, i.e. src x = the codomain of a.
    Axioms: x(id_{src x}) = x, src(xa) = src_of_a, x(ab) = (xa)b. -/
structure RightASet (A : Type u) [Cat.{v} A] where
  carrier   : Type (max u v)
  /-- Source map X → |A|: assigns to each point its "current object". -/
  src       : carrier → A
  /-- Partial action: given x : carrier and a morphism a : A' → src x, produce a new point. -/
  act       : ∀ (x : carrier) {A' : A}, (A' ⟶ src x) → carrier
  /-- x · id = x. -/
  act_id    : ∀ (x : carrier), act x (Cat.id (src x)) = x
  /-- src(x · a) = domain of a. -/
  act_src   : ∀ (x : carrier) {A' : A} (a : A' ⟶ src x), src (act x a) = A'
  /-- x · (b ≫ a) = (x · a) · b  (diagram-order: b then a). -/
  act_comp  : ∀ (x : carrier) {A' B' : A} (a : A' ⟶ src x) (b : B' ⟶ A'),
      act x (b ≫ a) = act (act x a) (act_src x a ▸ b)

/-- A morphism of right A-sets: a function respecting source and action. -/
structure RightASetHom (A : Type u) [Cat.{v} A] (X Y : RightASet A) where
  toFun    : X.carrier → Y.carrier
  map_src  : ∀ x : X.carrier, Y.src (toFun x) = X.src x
  map_act  : ∀ (x : X.carrier) {A' : A} (a : A' ⟶ X.src x),
      toFun (X.act x a) = Y.act (toFun x) (map_src x ▸ a)

/-! ## §1.273  Left A-sets -/

/-- A LEFT A-SET (§1.273): the contravariant version; equivalently, a right A^op-set.
    A set X with a "target" map O: X → |A| and a partial action a · x defined
    when tgt x = domain of a (i.e. O(ax) = Oa holds after the action).
    Axioms: id · x = x, tgt(a · x) = codomain(a), (a ≫ b) · x = b · (a · x). -/
structure LeftASet (A : Type u) [Cat.{v} A] where
  carrier   : Type (max u v)
  /-- Target map X → |A|: the object "labelling" a point. -/
  tgt       : carrier → A
  /-- Partial action: given x : carrier and morphism a : tgt x → A', produce a new point. -/
  act       : ∀ (x : carrier) {A' : A}, (tgt x ⟶ A') → carrier
  /-- id · x = x. -/
  act_id    : ∀ (x : carrier), act x (Cat.id (tgt x)) = x
  /-- tgt(a · x) = codomain of a. -/
  act_tgt   : ∀ (x : carrier) {A' : A} (a : tgt x ⟶ A'), tgt (act x a) = A'
  /-- Associativity in diagram order: (a ≫ b) · x = b · (a · x). -/
  act_comp  : ∀ (x : carrier) {A' B' : A} (a : tgt x ⟶ A') (b : A' ⟶ B'),
      act x (a ≫ b) = act (act x a) (act_tgt x a ▸ b)

/-- A morphism of left A-sets: a function respecting target and action. -/
structure LeftASetHom (A : Type u) [Cat.{v} A] (X Y : LeftASet A) where
  toFun    : X.carrier → Y.carrier
  map_tgt  : ∀ x : X.carrier, Y.tgt (toFun x) = X.tgt x
  map_act  : ∀ (x : X.carrier) {A' : A} (a : X.tgt x ⟶ A'),
      toFun (X.act x a) = Y.act (toFun x) (map_tgt x ▸ a)

/-! ## §1.283  Strongly connected category -/

/-- **§1.283** A category is STRONGLY CONNECTED if for every ordered pair of objects
    (A, B) there exists a morphism A → B.  (Note: this does not require uniqueness.) -/
def StronglyConnected (𝒞 : Type u) [Cat.{v} 𝒞] : Prop :=
  ∀ (A B : 𝒞), Nonempty (A ⟶ B)

/-! ## §1.284  Prefunctor -/

/-- **§1.284** A PREFUNCTOR F : A → B preserves composition but not necessarily identities.
    The forgetful functor 𝒴#(𝒵) → A is a prefunctor. -/
class Prefunctor {C : Type u} [Cat.{v} C] {D : Type u} [Cat.{v} D] (F : C → D) where
  map      : {X Y : C} → (X ⟶ Y) → (F X ⟶ F Y)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- Every functor is a prefunctor (it additionally preserves identities). -/
def functorIsPrefunctor {C : Type u} [Cat.{v} C] {D : Type u} [Cat.{v} D]
    (F : Functor C D) : Prefunctor F.obj where
  map := F.map
  map_comp := F.map_comp

end Freyd
