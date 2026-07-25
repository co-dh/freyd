/-
  Freyd & Scedrov, *Categories and Allegories* §1.13

  §1.13  IDENTITY MORPHISM — six equivalent characterisations.

  The book states: the following are equivalent properties on a morphism e —
    (i)   there exists x such that e = □x  (e is a source of something)
    (ii)  there exists x such that e = x□  (e is a target of something)
    (iii) e = □e
    (iv)  e = e□
    (v)   for all x, ex ≍ x  (e is a left unit wherever it acts)
    (vi)  for all x, xe ≍ x  (e is a right unit wherever it acts)

  In our typed `Cat` the source/target operations are encoded in the type of each
  morphism: `id X : X ⟶ X` is the unique identity at object `X`.  Conditions
  (i)–(iv) become definitionally trivial.  The non-trivial content is:

    A morphism `e : X ⟶ X` satisfying the left-unit law (v) or the right-unit
    law (vi) must equal `Cat.id X`.
-/

import Freyd.S1_1

namespace Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- §1.13: A morphism `e : X ⟶ X` that acts as a left unit on all morphisms out
    of `X` must be the identity.  (Condition (v) of the book's equivalence.) -/
theorem left_unit_is_id {X : 𝒞} (e : X ⟶ X)
    (h : ∀ {Y : 𝒞} (f : X ⟶ Y), e ≫ f = f) : e = Cat.id X := by
  -- h (id X) : e ≫ id X = id X; comp_id gives e ≫ id X = e; so e = id X
  have := h (Cat.id X)
  rw [Cat.comp_id] at this
  exact this

/-- §1.13: A morphism `e : X ⟶ X` that acts as a right unit on all morphisms into
    `X` must be the identity.  (Condition (vi) of the book's equivalence.) -/
theorem right_unit_is_id {X : 𝒞} (e : X ⟶ X)
    (h : ∀ {W : 𝒞} (f : W ⟶ X), f ≫ e = f) : e = Cat.id X := by
  -- h (id X) : id X ≫ e = id X; id_comp gives id X ≫ e = e; so e = id X
  have := h (Cat.id X)
  rw [Cat.id_comp] at this
  exact this

/-- §1.13: The six-way equivalence, stated as `IsIdentity`.
    In the typed setting only conditions (v) and (vi) are non-trivial; (i)–(iv)
    hold definitionally for `e = Cat.id X`.

    We define `IsIdentity e` as `e = Cat.id X` and prove it equivalent to the
    left-unit and right-unit conditions. -/
def IsIdentity {X : 𝒞} (e : X ⟶ X) : Prop := e = Cat.id X

theorem isIdentity_iff_left_unit {X : 𝒞} (e : X ⟶ X) :
    IsIdentity e ↔ ∀ {Y : 𝒞} (f : X ⟶ Y), e ≫ f = f := by
  constructor
  · intro h; unfold IsIdentity at h; subst h; intro Y f; exact Cat.id_comp f
  · intro h; unfold IsIdentity; exact left_unit_is_id e h

theorem isIdentity_iff_right_unit {X : 𝒞} (e : X ⟶ X) :
    IsIdentity e ↔ ∀ {W : 𝒞} (f : W ⟶ X), f ≫ e = f := by
  constructor
  · intro h; unfold IsIdentity at h; subst h; intro W f; exact Cat.comp_id f
  · intro h; unfold IsIdentity; exact right_unit_is_id e h

end Freyd
