/-!
The shared predicate-set type used throughout the Freyd and AOP developments.
This module is dependency-free so early book sections and later set constructions use the same type.
-/

namespace Freyd

universe u



/-- A subset of `α`, as a predicate.  We avoid any library `Set` to stay self-contained. -/
abbrev Sub (α : Type u) := α → Prop
end Freyd
