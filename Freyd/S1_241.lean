/-
  Freyd & Scedrov, *Categories and Allegories* §1.241
  The category of sets.
-/

import Freyd.S1_10

universe v u

namespace Freyd

/-! ## §1.241 The category of sets -/

/-- “To define the CATEGORY OF SETS, S, we take the objects to be sets” (§1.241). -/
instance setCat : Cat.{v} (Type v) where
  Hom A B := A → B
  id _ := fun a => a
  comp f g := fun a => g (f a)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem set_comp {A B C : Type v} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := rfl

@[simp] theorem set_id {A : Type v} (a : A) : (Cat.id A) a = a := rfl

end Freyd
