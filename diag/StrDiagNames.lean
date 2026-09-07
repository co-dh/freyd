/-
  The PICTURE's own spelling of the relators a string-diagram lane can be.  A lane's label decides
  the panel's geometry — `columns` reserves room west of a lane for its own name — so a wire the
  note writes `F` cannot print as `BiRelator.toRelator F` and still land where the note draws it.

  Printing only: every declaration here is an unexpander, nothing is proved and nothing is used.
  They live in `diag` rather than beside their declarations because they are the DIAGRAM's
  vocabulary, not the algebra's — `T` is what the note calls the type functor's relator, and the
  `AOP` module already spells the same functor's action on arrows `T(R)`.
-/
import AOP.A5_5_TypeFunctor
import AOP.A5_5

namespace Freyd.Alg

-- WHICH ARROWS A PICTURE DASHES.  Each is the arrow a universal property produces: the fold from
-- the initial algebra's, the fork from the product's, the transpose from the power object's.  The
-- attribute is `AOP.A5_1`'s; the tags are here because dashing is the DIAGRAM's vocabulary.
attribute [diag_induced] relCata InitialAlgebra.cata Freyd.HasBinaryProducts.pair Λ

open Lean PrettyPrinter in
/-- The bifunctor's unary form is still the same bifunctor: the note's lane is `F`. -/
@[app_unexpander BiRelator.toRelator] def unexpandToRelator : Unexpander
  | `($_ $F) => `($F)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The type functor AS A RELATOR is the note's lane `T`, the same letter its action on arrows
    already prints with (`T(R)`); which initial algebras it is built from is not part of the name. -/
@[app_unexpander typeRelator] def unexpandTypeRelator : Unexpander
  | `($_ $_) => `($(mkIdent `T))
  | _ => throw ()

end Freyd.Alg
