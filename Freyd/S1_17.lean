module

public import Freyd.S1_10

/-!
  Freyd & Scedrov, *Categories and Allegories* §1.17.

  Left-invertible and right-invertible morphisms.
-/

open Freyd

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- §1.17  `f : X ⟶ Y` is LEFT-INVERTIBLE if some `y : Y ⟶ X` satisfies `y ≫ f = id_Y`. -/
@[expose] public def LeftInvertible {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∃ y : Y ⟶ X, y ≫ f = 𝟙 Y

/-- §1.17  `f : X ⟶ Y` is RIGHT-INVERTIBLE if some `z : Y ⟶ X` satisfies `f ≫ z = id_X`. -/
@[expose] public def RightInvertible {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∃ z : Y ⟶ X, f ≫ z = 𝟙 X

end Freyd
