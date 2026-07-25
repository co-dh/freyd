/-
  Freyd & Scedrov, *Categories and Allegories* §1.1  Basic definitions.

  The `Cat` typeclass: objects, typed Hom-sets, identity, composition,
  and the three axioms (id_comp, comp_id, assoc).
-/


class Cat.{w, z} (𝒞 : Type z) : Type (max z (w + 1)) where
  Hom     : 𝒞 → 𝒞 → Type w
  id      : (X : 𝒞) → Hom X X
  comp    : {X Y Z : 𝒞} → Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : 𝒞} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : 𝒞} (f : Hom X Y), comp f (id Y) = f
  assoc   : ∀ {W X Y Z : 𝒞} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
              comp (comp f g) h = comp f (comp g h)

-- `scoped` in `Freyd` (active only under `open Freyd`, which every Freyd file does) so a bridge
-- file MAY import `Mathlib.CategoryTheory` without the `«term_⟶_»` global-notation clash against
-- mathlib's `Quiver` `⟶`. Keeps the §1.543 mathlib route's bridge file possible. (`Cat` is at
-- `_root_`; the notation just lives in the `Freyd` scope.)
namespace Freyd
scoped infixr:25 " ⟶ "  => Cat.Hom
scoped infixr:80 " ≫ "  => Cat.comp
/-- The book's identity morphism `1_A`, with the object explicit for reliable elaboration. -/
scoped notation:max "𝟙" A:max => Cat.id A
end Freyd

