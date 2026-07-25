/-
  Freyd & Scedrov, *Categories and Allegories* §1.14–§1.1(10)

  §1.14   MONOID as a one-object category (and back).
  §1.15   DISCRETE CATEGORY.
  §1.17   LEFT-INVERTIBLE, RIGHT-INVERTIBLE, uniqueness of two-sided inverse,
          GROUPOID (all morphisms iso), GROUP (one-object groupoid).
  §1.182  CONTRAVARIANT FUNCTOR and the OPPOSITE CATEGORY A°.
  §1.1(10) ISOMORPHISM OF CATEGORIES (functor with a two-sided inverse functor).
-/

import Freyd.S1_1
import Freyd.S1_41
import Freyd.S1_18

namespace Freyd

universe v u u₁ u₂

-- ---------------------------------------------------------------------------
-- §1.14  MONOID as a one-object category
-- ---------------------------------------------------------------------------

/-- §1.14  A monoid: a set with a unit and an associative binary operation. -/
class Monoid' (M : Type u) where
  one  : M
  mul  : M → M → M
  one_mul   : ∀ x : M, mul one x = x
  mul_one   : ∀ x : M, mul x one = x
  mul_assoc : ∀ x y z : M, mul (mul x y) z = mul x (mul y z)

/-- §1.14  Every monoid gives a one-object category (unique object = `PUnit`). -/
def monoidToCat (M : Type u) [mn : Monoid' M] : Cat.{u, 0} PUnit where
  Hom _ _  := M
  id  _    := mn.one
  comp     := fun f g => mn.mul f g
  id_comp  := fun f => mn.one_mul f
  comp_id  := fun f => mn.mul_one f
  assoc    := fun f g h => mn.mul_assoc f g h

/-- §1.14  A one-object category is a monoid (take `Hom star star` as carrier). -/
def catToMonoid' {𝒞 : Type u} [C : Cat.{v} 𝒞] (star : 𝒞) : Monoid' (C.Hom star star) where
  one       := C.id star
  mul f g   := C.comp f g
  one_mul f := C.id_comp f
  mul_one f := C.comp_id f
  mul_assoc := fun f g h => C.assoc f g h

-- ---------------------------------------------------------------------------
-- §1.15  DISCRETE CATEGORY
-- ---------------------------------------------------------------------------

/-- §1.15  Any type `α` becomes a discrete category: the only morphism `a ⟶ b`
    is a proof that `a = b`. -/
def discreteCat (α : Type u) : Cat.{0, u} α where
  Hom a b  := PLift (a = b)
  id a     := ⟨rfl⟩
  comp     := fun ⟨h⟩ ⟨k⟩ => ⟨h.trans k⟩
  id_comp  := fun ⟨h⟩ => by cases h; rfl
  comp_id  := fun ⟨h⟩ => by cases h; rfl
  assoc    := fun ⟨h⟩ ⟨k⟩ ⟨l⟩ => by cases h; cases k; cases l; rfl

/-- §1.15  A category is DISCRETE if `Hom a b` is non-empty only when `a = b`. -/
def IsDiscreteCategory {𝒞 : Type u} [Cat.{v} 𝒞] : Prop :=
  ∀ {a b : 𝒞}, (a ⟶ b) → a = b

-- ---------------------------------------------------------------------------
-- §1.17  LEFT-INVERTIBLE, RIGHT-INVERTIBLE, ISOMORPHISM
-- ---------------------------------------------------------------------------

-- `IsIso` from S1_41: `IsIso f = ∃ g, f ≫ g = Cat.id X ∧ g ≫ f = Cat.id Y`

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- §1.17  Any left-inverse equals any right-inverse:
    book's proof `y = y(xz) = (yx)z = z`. -/
theorem left_inv_eq_right_inv {X Y : 𝒞} {f : X ⟶ Y}
    {y : Y ⟶ X} (hy : y ≫ f = Cat.id Y)
    {z : Y ⟶ X} (hz : f ≫ z = Cat.id X) : y = z :=
  calc y = y ≫ Cat.id X  := (Cat.comp_id y).symm
    _ = y ≫ (f ≫ z)      := by rw [hz]
    _ = (y ≫ f) ≫ z      := (Cat.assoc y f z).symm
    _ = Cat.id Y ≫ z     := by rw [hy]
    _ = z                := Cat.id_comp z

/-- §1.17  `f` is an isomorphism iff it is both left- and right-invertible. -/
theorem isIso_iff_leftInv_and_rightInv {X Y : 𝒞} (f : X ⟶ Y) :
    IsIso f ↔ LeftInvertible f ∧ RightInvertible f := by
  constructor
  · intro ⟨g, hfg, hgf⟩; exact ⟨⟨g, hgf⟩, ⟨g, hfg⟩⟩
  · intro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    have heq : y = z := left_inv_eq_right_inv hy hz
    exact ⟨y, heq ▸ hz, hy⟩

/-- §1.17  An isomorphism has a UNIQUE left-inverse. -/
theorem unique_left_inv {X Y : 𝒞} {f : X ⟶ Y} (hf : IsIso f)
    {y z : Y ⟶ X} (hy : y ≫ f = Cat.id Y) (hz : z ≫ f = Cat.id Y) : y = z := by
  obtain ⟨g, hfg, hgf⟩ := hf
  exact (left_inv_eq_right_inv hy hfg).trans (left_inv_eq_right_inv hz hfg).symm

/-- §1.17  An isomorphism has a UNIQUE right-inverse. -/
theorem unique_right_inv {X Y : 𝒞} {f : X ⟶ Y} (hf : IsIso f)
    {y z : Y ⟶ X} (hy : f ≫ y = Cat.id X) (hz : f ≫ z = Cat.id X) : y = z := by
  obtain ⟨g, hfg, hgf⟩ := hf
  exact (left_inv_eq_right_inv hgf hy).symm.trans (left_inv_eq_right_inv hgf hz)

/-- §1.17  The INVERSE of an isomorphism is an isomorphism (and its unique inverse is f):
    if `⟨g, hfg, hgf⟩ : IsIso f`, then `IsIso g` with witness `f`. -/
theorem isIso_inv {X Y : 𝒞} {f : X ⟶ Y} (hf : IsIso f) : ∃ g : Y ⟶ X, IsIso g :=
  let ⟨g, hfg, hgf⟩ := hf; ⟨g, f, hgf, hfg⟩

-- ---------------------------------------------------------------------------
-- §1.17  GROUPOID and GROUP
-- ---------------------------------------------------------------------------

/-- §1.17  A GROUPOID is a category in which every morphism is an isomorphism. -/
class Groupoid (𝒢 : Type u) extends Cat.{v} 𝒢 where
  iso_all : ∀ {X Y : 𝒢} (f : Hom X Y),
              ∃ g : Hom Y X, comp f g = id X ∧ comp g f = id Y

/-- §1.17  A GROUP is a one-object groupoid: a groupoid with a single object. -/
class Group' (G : Type u) extends Monoid' G where
  inv     : G → G
  mul_inv : ∀ x : G, mul x (inv x) = one
  inv_mul : ∀ x : G, mul (inv x) x = one

/-- A `Group'` gives a one-object `Groupoid`. -/
def group'ToGroupoid (G : Type u) [gr : Group' G] : Groupoid.{u, 0} PUnit where
  Hom _ _  := G
  id  _    := gr.one
  comp     := fun f g => gr.mul f g
  id_comp  := fun f => gr.one_mul f
  comp_id  := fun f => gr.mul_one f
  assoc    := fun f g h => gr.mul_assoc f g h
  iso_all f := ⟨gr.inv f, gr.mul_inv f, gr.inv_mul f⟩

-- ---------------------------------------------------------------------------
-- §1.182  OPPOSITE CATEGORY and CONTRAVARIANT FUNCTOR
-- ---------------------------------------------------------------------------

/-- §1.182  A CONTRAVARIANT FUNCTOR `F : C → D` reverses direction and swaps
    composition.  Freyd §1.182: `F(xy) = (Fy)(Fx)`. -/
class ContraFunctor {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D] (F : C → D) where
  map      : {X Y : C} → (X ⟶ Y) → (F Y ⟶ F X)
  map_id   : ∀ (X : C), map (Cat.id X) = Cat.id (F X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
               map (f ≫ g) = map g ≫ map f

/-- §1.182  A contravariant functor `F : C → D` is the same as a covariant
    functor `Cᵒᵖ → D`.  We give the covariant functor explicitly. -/
def contraToCovar {C : Type u₁} [cat_C : Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    (F : C → D) [hF : ContraFunctor F] : Functor (OppCat C) D where
  obj X := F X
  map {X Y} (f : @Cat.Hom (OppCat C) (oppCatInst C) X Y) := hF.map f
  map_id   X  := hF.map_id X
  map_comp {X Y Z} (f : @Cat.Hom (OppCat C) (oppCatInst C) X Y)
                   (g : @Cat.Hom (OppCat C) (oppCatInst C) Y Z) := hF.map_comp g f

/-- §1.182  The identity `C → Cᵒᵖ` is a contravariant functor. -/
def toOpContra (C : Type u) [cat : Cat.{v} C] :
    @ContraFunctor C cat (OppCat C) (oppCatInst C) (fun X : C => (X : OppCat C)) where
  map {X Y} (f : cat.Hom X Y) : @Cat.Hom (OppCat C) (oppCatInst C) Y X := f
  map_id _ := rfl
  map_comp _ _ := rfl

-- ---------------------------------------------------------------------------
-- §1.1(10)  ISOMORPHISM OF CATEGORIES
-- ---------------------------------------------------------------------------

/-- §1.1(10)  A CATEGORY ISOMORPHISM from `C` to `D`: a functor `F : C → D`
    together with an inverse functor `G : D → C` such that
    `G ∘ F = Id_C` and `F ∘ G = Id_D` on objects.
    (The book's §1.1(10): a one-to-one onto functor; equivalently, a functor with
    a functor inverse.) -/
structure CatIso {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D] (F : Functor C D) where
  inv      : Functor D C
  left_id  : ∀ X : C, inv.obj (F.obj X) = X
  right_id : ∀ Y : D, F.obj (inv.obj Y) = Y

/-- §1.1(10)  The identity functor is a self-isomorphism. -/
def catIsoId (C : Type u₁) [Cat.{v} C] : CatIso (idFunctor : Functor C C) :=
  ⟨idFunctor, fun _ => rfl, fun _ => rfl⟩

/-- §1.1(10)  Isomorphisms of categories compose. -/
def catIsoComp {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    {E : Type _} [Cat.{v} E]
    (F : Functor C D) (G : Functor D E)
    (hFi : CatIso F) (hGi : CatIso G) : CatIso (compFunctor F G) where
  inv      := compFunctor hGi.inv hFi.inv
  left_id  := fun X => by simp only [compFunctor_obj]; rw [hGi.left_id (F.obj X), hFi.left_id X]
  right_id := fun Y => by simp only [compFunctor_obj]; rw [hFi.right_id (hGi.inv.obj Y), hGi.right_id Y]

end Freyd
