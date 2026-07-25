/-
  Freyd & Scedrov, *Categories and Allegories* §1.28–§1.281
  Idempotent, Splits, Split idempotent.
-/

import Freyd.S1_1

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.28 Idempotent -/

/-- IDEMPOTENT (§1.28): a morphism `e : A ⟶ A` such that `e² = e`.
    The book's "necessarily `□e = e□`" is forced by the type `A ⟶ A`. -/
def Idempotent {A : 𝒞} (e : A ⟶ A) : Prop := e ≫ e = e

/-! ## §1.281 Split idempotent -/

/-- SPLITS (§1.281): the pair `⟨x : A ⟶ B, y : B ⟶ A⟩` SPLITS the idempotent `e : A ⟶ A`
    if `x ≫ y = e` and `y ≫ x = 𝟙 B`. -/
def Splits {A B : 𝒞} (x : A ⟶ B) (y : B ⟶ A) (e : A ⟶ A) : Prop := x ≫ y = e ∧ y ≫ x = 𝟙 B

/-- SPLIT IDEMPOTENT (§1.281): there exist `B`, `x : A ⟶ B`, `y : B ⟶ A` that split `e`. -/
def SplitIdempotent {A : 𝒞} (e : A ⟶ A) : Prop :=
  ∃ (B : 𝒞) (x : A ⟶ B) (y : B ⟶ A), Splits x y e

/-- Idempotency is a consequence of splitting, not a side condition:
    `e = xy = x(yx)y = x1y = xy = e`.  This is why §1.281 needs no idempotency conjunct. -/
theorem Splits.idempotent {A B : 𝒞} {x : A ⟶ B} {y : B ⟶ A} {e : A ⟶ A}
    (h : Splits x y e) : Idempotent e := by
  rcases h with ⟨hxy, hyx⟩
  calc
    e ≫ e = (x ≫ y) ≫ (x ≫ y) := by rw [hxy]
    _ = x ≫ (y ≫ x) ≫ y := by simp only [Cat.assoc]
    _ = x ≫ 𝟙 B ≫ y := by rw [hyx]
    _ = x ≫ y := by rw [Cat.id_comp y]
    _ = e := by rw [hxy]

end Freyd
