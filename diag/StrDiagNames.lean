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
-- The case studies whose beads the note names in its own words: each is here only because an
-- unexpander below keys on one of its constants.
import AOP.A7_7_MSS
import AOP.A8_1
import AOP.A8_4_Knapsack
import AOP.A8_5_Paragraph
import AOP.A9_2_Edit
import AOP.A9_3_Bracket
import AOP.A9_4_Code
import AOP.A10_2_Detab
import AOP.A10_3_Tardy
-- `tour`, whose body the note draws: a tag names a constant, so its module has to be in scope.
import AOP.A8_6_Tour
-- `diag_unfold`, declared where it is read: an attribute is usable only below the module declaring it.
import diag.tool.ExprReader

namespace Freyd.Alg

-- WHICH ARROWS A PICTURE DASHES.  Each is the arrow a universal property produces: the fold from
-- the initial algebra's, the fork from the product's, the transpose from the power object's.  The
-- attribute is `AOP.A5_1`'s; the tags are here because dashing is the DIAGRAM's vocabulary.
attribute [diag_induced] relCata InitialAlgebra.cata Freyd.HasBinaryProducts.pair Λ

-- WHICH DEFINITIONS A PICTURE OPENS: the `AOP` constants the note draws opened — `tour%∋` against
-- the note's `⦇listcp(F)⟨g₁,g₂⟩cat thinlist(Q)⦈`.  `diag_unfold` is `diag/tool/ExprReader.lean`'s,
-- the mirror of `diag_induced`; the tags are here for the same reason `diag_induced`'s are, that
-- the note's spelling is the DIAGRAM's vocabulary and not the algebra's.
attribute [diag_unfold] RelSet.Tour.tour

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

-- The note's `thin(Q)` is a DELIMITED operator, like `est(R)` (`AOP.A7_1`) and `P(R)` (`AOP.A5_4`)
-- which are declared this same way: an unexpander returns a term, and no term prints its own brackets.
notation:max "thin(" Q ")" => thinRel Q

open Lean PrettyPrinter in
/-- A map's GRAPH is written by the map's own name — the note's `edit`, `cons`, `nil` are all
    `graph f` — and the two projections have names of their own, B&dM's `π₁`/`π₂`. -/
@[app_unexpander RelSet.graph] def unexpandGraph : Unexpander
  | `($_ Prod.fst) => `($(mkIdent `π₁))
  | `($_ Prod.snd) => `($(mkIdent `π₂))
  -- Only a map with a NAME: `graph (fun _ => 0)` keeps `AOP.A6_1_RelSet`'s own `⊸ 0`, which this
  -- clause would otherwise shadow with the lambda.
  | `($_ $f:ident) => `($f)
  | _ => throw ()

-- THE SECTION'S OWN ORDERING IS THE NOTE'S BEAD `R`.  Which cost function it ranks by — the volume,
-- the line width, the due dates — is the section's context and not part of the name, exactly as
-- `AOP.A9_3_Bracket.R`'s own unexpander already has it.  One per constant: the attribute keys on one.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.R] def unexpandEditR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.R] def unexpandDetabR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.R] def unexpandTardyR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Knapsack.R] def unexpandKnapsackR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.R] def unexpandParagraphR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.R] def unexpandCodeR : Unexpander | _ => `($(mkIdent `R))

-- THE MAP A SECTION IS NAMED AFTER.  The note draws the specification's own name, not the Lean
-- function the graph is taken of: `edit`, `detab`, `flatten` are `editFn`, `detabR`, `flattenFn`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.editFn] def unexpandEditFn : Unexpander | _ => `($(mkIdent `edit))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.detabR] def unexpandDetabFn : Unexpander | _ => `($(mkIdent `detab))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.flattenFn] def unexpandFlattenFn : Unexpander
  | _ => `($(mkIdent `flatten))

open Lean PrettyPrinter in
/-- The maximum-segment-sum step is the note's `⊕`, which is no Lean identifier: the formatter
    escapes it and `diag/tool/ExprReader` unescapes, as it already does for `≥`. -/
@[app_unexpander RelSet.MSS.oplus] def unexpandOplus : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "⊕")))

open Lean PrettyPrinter in
/-- The least fixed point is the note's bead `(μX : S°F(X)R)` — the binder and the body it binds,
    which is what a TYPE ASCRIPTION already spells, so no new notation is needed for the brackets. -/
@[app_unexpander mu] def unexpandMu : Unexpander
  | `($_ fun $x:ident => $b) => `(($(mkIdent (Name.mkSimple ("μ" ++ x.getId.toString))) : $b))
  | _ => throw ()

-- WHAT THE CASE STUDIES' MIDDLE BEAD OPENS.  The note draws each algebra's own coproduct —
-- `⦇[nil,cons](within(w)) ∪ [nil,π₂]⦈`, `⦇[wrap wrap,new ∪ (glue (ok w))]⦈` — where the name
-- `Salg` says nothing; `diag_unfold` is `diag/tool/ExprReader.lean`'s, as for `tour` above.
attribute [diag_unfold] RelSet.Knapsack.Salg RelSet.Paragraph.Salg

end Freyd.Alg
