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
import AOP.A7_2_RelSet
import AOP.A7_3_Party
import AOP.A7_4_Cylinder
import AOP.A7_4_CylinderVecRel
import AOP.A7_5_Van
import AOP.A7_7_MSS
import AOP.A7_7_TakeWhile
import AOP.A8_1
import AOP.A8_2
import AOP.A8_4_Knapsack
import AOP.A8_5_Paragraph
import AOP.A9_2_Edit
import AOP.A9_3_Bracket
import AOP.A9_4_Code
import AOP.A10_2_Detab
import AOP.A10_3_Tardy
import AOP.A10_4_Tex
-- `tour`, whose body the note draws: a tag names a constant, so its module has to be in scope.
import AOP.A8_6_Tour
-- `diag_unfold`, declared where it is read: an attribute is usable only below the module declaring it.
import diag.tool.ExprReader

namespace Freyd.Alg

-- WHICH ARROWS A PICTURE DASHES.  Each is the arrow a universal property produces: the fold from
-- the initial algebra's, the fork from the product's, the transpose from the power object's.  The
-- attribute is `AOP.A5_1`'s; the tags are here because dashing is the DIAGRAM's vocabulary.
-- The allegory's own fork and product map are induced for the same reason the category's `pair`
-- is: `⟨R,S⟩` is what the tabulation of `⊤` gives from `R` and `S`, and `R×S` is that fork taken
-- at the two projections.  A statement about `R×S` against a projection is therefore a statement
-- about ITS TWO COMPONENTS, which is what `Face.components` reads off an induced head.
-- The type functor's action is the fold `T(R) = ⦇F(R,𝟙)α⦈` (`typeMap_defn`), so the initial
-- algebra's universal property produces it exactly as it produces any other fold.
attribute [diag_induced] relCata InitialAlgebra.cata Freyd.HasBinaryProducts.pair Λ
  RelProd.pair prodMap typeMap junc

-- WHICH EQUATION PRODUCED ONE.  `relCata_cancel` IS the initial algebra's universal property read
-- as a square, so a picture that has to say what produced a fold draws it; the drawer instantiates
-- it by unifying its `⦇R⦈` with the fold in hand, never by this name.
attribute [diag_defines] relCata_cancel

-- WHICH DEFINITIONS A PICTURE OPENS: the `AOP` constants the note draws opened — `tour%∋` against
-- the note's `⦇listcp(F)⟨g₁,g₂⟩cat thinlist(Q)⦈`.  `diag_unfold` is `diag/tool/ExprReader.lean`'s,
-- the mirror of `diag_induced`; the tags are here for the same reason `diag_induced`'s are, that
-- the note's spelling is the DIAGRAM's vocabulary and not the algebra's.
attribute [diag_unfold] RelSet.Tour.tour

-- THE DUPLICATION RELATOR IS WRITTEN OUT AS THE PRODUCT IT IS: the note's corner is `A×A` and its
-- side `R×R`, never `Δ(A)` — `Δ` is `Relator.prod` of two identities (`AOP.A5_2`), and a bundle
-- built out of bundles has no name of its own, which is what every other product relator already
-- draws by (`openBuiltField?`).
attribute [diag_unfold] Δ

open Lean PrettyPrinter Delaborator SubExpr in
/-- A `RelProd a b`'s apex IS the product of `a` and `b` — that is what tabulating `⊤ : a ⟶ b`
    says — so the note writes it `a×b`, never by the field's own name.  A DELABORATOR and not an
    unexpander: the two objects are the `RelProd` argument's TYPE, which an unexpander, seeing only
    the syntax the elaborator produced, does not have.  One rule for every product apex the
    statements name, the abstract `P.p` of `prodMap` included. -/
@[delab app.Freyd.Alg.RelProd.p] def delabRelProdApex : Delab := do
  guard ((← getExpr).getAppNumArgs == 5)
  let a ← withNaryArg 2 delab
  let b ← withNaryArg 3 delab
  `($a × $b)

open Lean PrettyPrinter in
/-- The bifunctor's unary form is still the same bifunctor: the note's lane is `F`. -/
@[app_unexpander BiRelator.toRelator] def unexpandToRelator : Unexpander
  | `($_ $F) => `($F)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The CHOSEN COPRODUCT OBJECT is the note's `a+b`, never the class field's own name — `RelProd.p`'s
    `a×b` mirrored.  An unexpander and not a delaborator: both objects are arguments here, where a
    product apex has to read them off its `RelProd`'s type. -/
@[app_unexpander PositiveAllegory.coprod] def unexpandCoprod : Unexpander
  | `($_ $a $b) => `($a + $b)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The type functor AS A RELATOR is the note's lane `T`, the same letter its action on arrows
    already prints with (`T(R)`); which initial algebras it is built from is not part of the name. -/
@[app_unexpander typeRelator] def unexpandTypeRelator : Unexpander
  | `($_ $_) => `($(mkIdent `T))
  | _ => throw ()

open Lean PrettyPrinter in
/-- The path count is the note's `3^m`; `pow3` is only the spelling that makes the index reduce. -/
@[app_unexpander Vec.pow3] def unexpandPow3 : Unexpander
  | `($_ $m) => `(3 ^ $m)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The pairing that packs a bifunctor's two arguments is the note's lane `⟨𝟙,T⟩` — what it does
    to an arrow, `R ↦ (R,T(R))`, IS its name; which initial algebras `T` comes from is not. -/
@[app_unexpander typePair] def unexpandTypePair : Unexpander
  | `($_ $_) => `($(mkIdent (Name.mkSimple "⟨𝟙,T⟩")))
  | _ => throw ()

open Lean PrettyPrinter in
/-- The rose-tree relator is the note's lane `tree`, the letter its action on arrows already
    prints with — so `dRose A` and the initial algebra's carrier draw as the one lane. -/
@[app_unexpander RelSet.RT.roseRelator] def unexpandRoseRelator : Unexpander
  | `($_:ident) => `($(mkIdent `tree))
  | _ => throw ()

open Lean PrettyPrinter in
/-- The tip-tree relator is the note's lane `tree` as much as the rose tree's is: which of the two
    datatypes a section's trees are is the section's business, not the wire's. -/
@[app_unexpander RelSet.TT.treeRelator] def unexpandTreeRelator : Unexpander
  | `($_:ident) => `($(mkIdent `tree))
  | _ => throw ()

open Lean PrettyPrinter in
/-- The category of relations on sets is the note's REGION `𝒜`, the letter every panel over it is
    drawn in.  An `app_unexpander` and not a `notation`: a token would make every binder the repo
    already names `𝒜` (`AOP.A5_3`'s `{s A B : 𝒜}`) print escaped. -/
@[app_unexpander RelSet] def unexpandRelSet : Unexpander
  | `($_:ident) => `($(mkIdent `𝒜))
  | _ => throw ()

open Lean PrettyPrinter in
/-- The rose tree's BASE relator is the note's `F`, the letter §13.4.3 writes on both objects of
    `party-mono` — which datatype's base it is, and at which leaf type, is the section's context and
    not part of the name, exactly as `typeRelator`'s `T` is. -/
@[app_unexpander RelSet.RT.F] def unexpandRTF : Unexpander
  | `($_ $_) => `($(mkIdent `F))
  | _ => throw ()

open Lean PrettyPrinter Delaborator SubExpr in
/-- THE LEAF TYPE IS AN ARGUMENT WHERE THE NOTE WRITES IT: §13.4.3's `F(A,B) = A×[B]` is a
    two-argument functor and Lean's `RT.F A` is that functor at the leaf `A`, so its ACTION ON AN
    OBJECT writes both — `F(A,[A]×[A])`.  The LANE keeps the one letter (`unexpandRTF`): a panel
    carries its leaf type in the section's context, where a type cell states it. -/
@[delab app.Freyd.Functor.obj] def delabRoseFObj : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let f := e.getArg! 4
  guard (f.isAppOfArity ``Freyd.Alg.Relator.toFunctor 5
    && (f.getArg! 4).isAppOfArity ``Freyd.Alg.RelSet.RT.F 1)
  `($(mkIdent `F) $(← withNaryArg 4 (withNaryArg 4 (withNaryArg 0 delab)))
      $(← withNaryArg 5 delab))

/-- THE NOTE SETS A PRODUCT TIGHT — `[A]×[A]`, `A×[B]` — and an ATOM carries its own spacing into
    the printer: core's `" × "` writes the formatter's spaces wherever a label is read off the
    SYNTAX (`F(A,[A]×[A])`) rather than built from the term, where `labelTree`'s own product clause
    closes them up. -/
infixr:35 "×" => Prod

open Lean PrettyPrinter Delaborator SubExpr in
/-- The abbreviation is a SEAM, the one `unexpandNEListType` names: `dBranch A` keeps its own
    constant in every statement, so the object action above never sees it and a cell would print
    the Lean name.  Delaborate what it abbreviates, which IS that action. -/
@[delab app.Freyd.Alg.RelSet.Party.dBranch] def delabDBranch : Delab := do
  let some e ← Meta.unfoldDefinition? (← getExpr) | failure
  PrettyPrinter.delab e

open Lean PrettyPrinter in
/-- The snoc-list relator is the note's lane `list`, at whatever leaf type — `unexpandDSL` already
    writes every snoc list `[E]`, and this is that object's wire. -/
@[app_unexpander RelSet.SL.snocRelator] def unexpandSnocRelator : Unexpander
  | `($_ $_) => `($(mkIdent `list))
  | _ => throw ()

open Lean PrettyPrinter in
/-- The bag relator is the note's lane `bag`; `bag(Job)` is that lane over the `Job` wire. -/
@[app_unexpander RelSet.Tardy.bagRelator] def unexpandBagRelator : Unexpander
  | `($_:ident) => `($(mkIdent `bag))
  | _ => throw ()

-- A DATATYPE'S CARRIER IS THE NOTE'S OBJECT, under the note's own name for it: `tree(A)`,
-- `list⁺(A)`.  The unexpander writes the NAME, applied; the BRACKETS are the label printer's
-- (`appShow`), which puts them round the operand of every juxtaposed application, because
-- juxtaposition is composition and `tree A` reads as two things composed (CLAUDE.md).  One clause
-- per carrier, keyed on the constant — the tree the note draws is the tip-tree as much as the rose
-- tree, and the element type is the one argument either takes.
open Lean PrettyPrinter in
@[app_unexpander RelSet.RT.dRose] def unexpandDRose : Unexpander
  | `($_ $A) => `($(mkIdent `tree) $A)
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander RelSet.TT.dTree] def unexpandDTree : Unexpander
  | `($_ $A) => `($(mkIdent `tree) $A)
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander RelSet.TT.Tree] def unexpandTreeType : Unexpander
  | `($_ $A) => `($(mkIdent `tree) $A)
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.dNE] def unexpandDNE : Unexpander
  | `($_ $A) => `($(mkIdent (Name.mkSimple "list⁺")) $A)
  | _ => throw ()

-- The CARRIER needs the clause as much as the object: `NEList A` is an `abbrev`, so the term keeps
-- the abbreviation and the `ConsList A A` delaborator below never sees it — a seam between two
-- declared objects is labelled from the carrier and would print the Lean name.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.NEList] def unexpandNEListType : Unexpander
  | `($_ $A) => `($(mkIdent (Name.mkSimple "list⁺")) $A)
  | _ => throw ()

-- THE LEAF TYPE SAYS WHICH LIST A CONS-LIST IS, and a leaf carrying an ELEMENT is a one-element
-- list: `ConsList A A` is the note's `list⁺(A)`, where `ConsList Unit A` is its `[A]`
-- (`AOP.A6_ConsList`).  A DELABORATOR, because the two differ only in a TYPE the syntax repeats
-- and an unexpander comparing the two spellings would compare names, not types; and it reaches the
-- object too, because a wire's label is read off the carrier the elaborator reduced to.  The OBJECT
-- `dCL L E` is an `abbrev` and keeps its own constant, so it is keyed here as well.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Freyd.Alg.RelSet.CL.ConsList, delab app.Freyd.Alg.RelSet.CL.dCL]
def delabConsList : Delab := do
  let args := (← getExpr).getAppArgs
  if args.size != 2 then failure
  -- The EMPTY leaf decides first: at `ConsList Unit Unit` both tests hold, and a leaf carrying
  -- nothing is a list of units and not a non-empty list of them.
  if ← Meta.isDefEq args[0]! (mkConst ``Unit) then `([$(← withAppArg delab)])
  else if ← Meta.isDefEq args[0]! args[1]! then
    `($(mkIdent (Name.mkSimple "list⁺")) $(← withAppArg delab))
  else failure

open Lean PrettyPrinter Delaborator SubExpr in
/-- The LEAF object is the leaf type itself — `dL L` names no former — and the EMPTY leaf is the
    note's terminal object `𝟏`, the source `nil` comes out of.  `isDefEq` and not a syntactic
    `Unit`, for the reason the cons-list delaborator above gives. -/
@[delab app.Freyd.Alg.RelSet.CL.dL] def delabDL : Delab := do
  let args := (← getExpr).getAppArgs
  if args.size != 1 then failure
  -- `Name.mkSimple`: `𝟏` is a digit to Lean's parser, so no name literal can spell it.
  if ← Meta.isDefEq args[0]! (mkConst ``Unit) then `($(mkIdent (Name.mkSimple "𝟏")))
  else withAppArg delab

-- The note's `thin(Q)` is a DELIMITED operator, like `est(R)` (`AOP.A7_1`) and `P(R)` (`AOP.A5_4`)
-- which are declared this same way: an unexpander returns a term, and no term prints its own brackets.
notation:max "thin(" Q ")" => thinRel Q

-- THE SET OF SUMS IS SPELLED AS THE SET IT IS.  `sums xs ys` is the note's `{x+y∣x∈xs∧y∈ys}`,
-- built from the two arguments the term carries; a name says what the point is called and the
-- set-builder says what is IN it, which is what the corner of a distributivity square is read for.
-- A NOTATION for the reason `thin(` is one: no term prints its own brackets.
notation:max "{x+y∣x∈" xs "∧y∈" ys "}" => RelSet.sums xs ys

-- A DATATYPE'S OBJECT IS SPELLED THE WAY THE NOTE'S OBJECT LANGUAGE SPELLS IT: lower case, and
-- bracketed where the argument is applied — `tree A`, `list⁺ A`, `bag(Job)`.  A NOTATION and not an
-- unexpander, for the reason `thin(` is one above: no term prints its own brackets.
notation:max "bag(" J ")" => RelSet.Tardy.Bag J

open Lean PrettyPrinter in
/-- A map's GRAPH is written by the map's own name — the note's `edit`, `cons`, `nil` are all
    `graph f` — and the two projections have names of their own, B&dM's `π₁`/`π₂`. -/
@[app_unexpander RelSet.graph] def unexpandGraph : Unexpander
  | `($_ Prod.fst) => `($(mkIdent `π₁))
  | `($_ Prod.snd) => `($(mkIdent `π₂))
  -- Eta-expanded, which is how a `fun p => p.2` written at the use site comes back out.
  | `($_ fun $_:ident => Prod.fst $_) => `($(mkIdent `π₁))
  | `($_ fun $_:ident => Prod.snd $_) => `($(mkIdent `π₂))
  -- Only a map with a NAME: `graph (fun _ => 0)` keeps `AOP.A6_1_RelSet`'s own `⊸ 0`, which this
  -- clause would otherwise shadow with the lambda.
  | `($_ $f:ident) => `($f)
  | _ => throw ()

open Lean PrettyPrinter in
/-- A PREDICATE'S COREFLEXIVE is written by the predicate's own name, for the reason a map's graph
    is: the note's `p` box and its `(p×𝟙)` lane are this partial identity, and `pcor` is the Lean
    spelling of the same arrow. -/
@[app_unexpander RelSet.GCTakeWhile.pcor] def unexpandPcor : Unexpander
  | `($_ $p) => `($p)
  | _ => throw ()

-- A RELATION NAMED AFTER THE MAP IT IS THE GRAPH OF drops the `R` the Lean name needs to tell the
-- two apart: the note's region has only the arrow, and `consR`/`concatR` already print that way.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.includeR] def unexpandIncludeR : Unexpander
  | _ => `($(mkIdent `«include»))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.excludeR] def unexpandExcludeR : Unexpander
  | _ => `($(mkIdent `exclude))

-- AN ARITHMETIC RELATION IS WRITTEN BY ITS OWN OPERATOR, the way the note writes it: `+` for the
-- addition's graph, `≤` for the ordering, so `est(leRel)` reads `est(≤)`.  The `Rel` the Lean name
-- carries tells the relation from the function and is no part of what the note spells.
open Lean PrettyPrinter in
@[app_unexpander RelSet.plusRel] def unexpandPlusRel : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "+")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.leRel] def unexpandLeRel : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≤")))

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
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.R] def unexpandPartyR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.R] def unexpandTourR : Unexpander | _ => `($(mkIdent `R))

-- `lenLE` is the same thing under its definition's name: the length preorder IS §13.4.2's ordering,
-- and the note draws `R` on that box and `est(R°)` on the greedy step.
open Lean PrettyPrinter in
@[app_unexpander RelSet.GCTakeWhile.lenLE] def unexpandLenLE : Unexpander | _ => `($(mkIdent `R))

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

open Lean PrettyPrinter Delaborator in
/-- The TeX problem's index object is the note's `[0,2¹⁶)`, which is no Lean identifier: the
    formatter escapes it and `diag/tool/ExprReader` unescapes, as it already does for `⊕`.  An
    OBJECT NEEDS A `delab`, not an unexpander: it prints as a bare constant, never as an
    application. -/
@[delab app.Freyd.Alg.RelSet.Tex.Ix, delab const.Freyd.Alg.RelSet.Tex.Ix]
def delabTexIx : Delab := `($(mkIdent (Name.mkSimple "[0,2¹⁶)")))

-- `[zero, ⊸ zero ∪ plus]`'s two leaves are named in the note, so the box carries the note's word
-- and not the namespace the Lean constant happens to live in.
open Lean PrettyPrinter in
@[app_unexpander RelSet.MSS.zero] def unexpandMSSZero : Unexpander | _ => `($(mkIdent `zero))
open Lean PrettyPrinter in
@[app_unexpander RelSet.MSS.plus] def unexpandMSSPlus : Unexpander | _ => `($(mkIdent `plus))

open Lean PrettyPrinter in
/-- The power relator's lane is the note's `E`, the letter its object action already prints with
    (`E A`) and the only lane the note draws over a power object — 113 of them, and no `P` lane. -/
@[app_unexpander powerRelator] def unexpandPowerRelator : Unexpander
  | _ => `($(mkIdent `E))

open Lean PrettyPrinter in
/-- The existential-image functor is the same `E` lane: it has the power relator's object action
    and is the only `E` an abstract region has, where `powerRelator` needs tabularity. -/
@[app_unexpander existsImageFunctor] def unexpandExistsImageFunctor : Unexpander
  | _ => `($(mkIdent `E))

open Lean PrettyPrinter in
/-- The diagonal relator's lane is `Δ`: the category it is taken over is the panel's region, which
    the lane already sits in, so `Δ 𝒜` writes it twice. -/
@[app_unexpander Δ] def unexpandDiagonalRelator : Unexpander
  | _ => `($(mkIdent `Δ))

open Lean PrettyPrinter in
/-- The least fixed point is the note's bead `(μX : S°F(X)R)` — the binder and the body it binds,
    which is what a TYPE ASCRIPTION already spells, so no new notation is needed for the brackets. -/
@[app_unexpander mu] def unexpandMu : Unexpander
  | `($_ fun $x:ident => $b) => `(($(mkIdent (Name.mkSimple ("μ" ++ x.getId.toString))) : $b))
  | _ => throw ()

open Lean PrettyPrinter in
/-- `H≜⦇T⦈°⦇h⦈` is the note's ONE bead `H`: which coalgebra and algebra it is built from is what
    the definition above the table states, not what the wire is labelled with. -/
@[app_unexpander H] def unexpandH : Unexpander | _ => `($(mkIdent `H))

-- A SECTION'S PARAMETERS ARE THE PANEL'S REGION, NOT PART OF THE BEAD'S NAME.  `gen`, `Q` and
-- `paths` are stated over the cylinder's fixed data (`I`, `moves`, `trans`, `zip`, …), which every
-- panel of §17.3 sits in, so spelling it in the label writes the section's context on every bead.
open Lean PrettyPrinter in
@[app_unexpander Cylinder.gen] def unexpandCylinderGen : Unexpander | _ => `($(mkIdent `gen))
open Lean PrettyPrinter in
@[app_unexpander Cylinder.Q] def unexpandCylinderQ : Unexpander | _ => `($(mkIdent `Q))
open Lean PrettyPrinter in
@[app_unexpander Cylinder.paths] def unexpandCylinderPaths : Unexpander | _ => `($(mkIdent `paths))

-- THE CONCRETE CYLINDER WEARS THE SAME NAMES AS THE ABSTRACT ONE, for the same reason: `n`, `p`,
-- `m` and the ordering `R` are the PANEL'S REGION, not part of the bead's name, and a bead's index
-- is the wire under it.  A FOLD IS WRITTEN `⦇algebra⦈`, never by the name of the recursion that
-- computes it: `genFold` is the fold of `gen` and `Qfold` the fold of `Q` — `cons_genFold` and
-- `cons_Qfold` are the two defining equations `α⦇a⦈ = F(𝟙,⦇a⦈)a` that say so.  Delaborators and not
-- unexpanders because `gen` and `paths` take only implicit arguments and so print as bare
-- constants, which `app_unexpander` cannot fire on.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.gen, delab const.Freyd.Alg.Vec.gen]
def delabVecGen : Delab := `($(mkIdent `gen))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.genFold, delab const.Freyd.Alg.Vec.genFold]
def delabVecGenFold : Delab := `(⦇$(mkIdent `gen)⦈)
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.paths, delab const.Freyd.Alg.Vec.paths]
def delabVecPaths : Delab := `($(mkIdent `paths))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.Rel.Q, delab const.Freyd.Alg.Vec.Rel.Q]
def delabVecRelQ : Delab := `($(mkIdent `Q))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.Rel.Qfold, delab const.Freyd.Alg.Vec.Rel.Qfold]
def delabVecRelQfold : Delab := `(⦇$(mkIdent `Q)⦈)
-- A section's thinning preorder is the note's `Q`, for the reason its ordering is `R`: which
-- relation it is, is the `code-defn` line above the table, not what the box is labelled with.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.Q] def unexpandCodeQ : Unexpander | _ => `($(mkIdent `Q))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.Q] def unexpandDetabQ : Unexpander | _ => `($(mkIdent `Q))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.Q] def unexpandTardyQ : Unexpander | _ => `($(mkIdent `Q))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.Q'] def unexpandTardyQ' : Unexpander | _ => `($(mkIdent `Q'))
-- The same holds of the two ORDERS the thinning preorder is built from: `V` on the output string,
-- `U` on the character, both stated over the section's tab width and its three characters.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.V] def unexpandDetabV : Unexpander | _ => `($(mkIdent `V))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.U] def unexpandDetabU : Unexpander | _ => `($(mkIdent `U))
-- And of the section's ARROWS: `expand` is one box on the note's row, and the tab width and the
-- three characters it is stated over are the section's, not part of the name the picture writes.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.expand] def unexpandDetabExpand : Unexpander
  | _ => `($(mkIdent `expand))

open Lean PrettyPrinter in
/-- The note's bead for the maximum-segment-sum step algebra is `k`; `Kalg` is only the Lean name. -/
@[app_unexpander RelSet.MSS.Kalg] def unexpandKalg : Unexpander | _ => `($(mkIdent `k))

open Lean PrettyPrinter in
/-- `Van.bmax` keeps its namespace only because `RelSet.Tardy.bmax` shares the name; a picture of
    one section's algebra has no second `bmax` to tell this one from. -/
@[app_unexpander RelSet.Van.bmax] def unexpandVanBmax : Unexpander | _ => `($(mkIdent `bmax))

-- ONE BEAD, `R∩H`.  A meet is a bead's LABEL and never a wiring, and the note writes it TIGHT —
-- which is what `Label.lean`'s `∩` clause already writes, off the head constant.  So the label is
-- taken from the DEFINITION rather than from a name of its own: an unexpander would have to spell
-- the meet as Lean's own notation prints it, spaced, and `R ∩ H` is not what the note draws.
attribute [diag_unfold] RelSet.Van.RinterH
-- §7.5's algebra the same way: the note draws the arms, `⦇[nil,(ok→glue,new)]⦈`, and `progAlg` is
-- a Lean name for them — a name in the label says nothing the picture can be read against.
attribute [diag_unfold] RelSet.Van.progAlg

open Lean PrettyPrinter in
/-- §7.5's ordering and its prefix condition are the note's `R` and `H`; the object they are taken
    at is the wire under the bead, as it is for every other section's `R`. -/
@[app_unexpander RelSet.Van.R] def unexpandVanR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Van.Hrel] def unexpandVanH : Unexpander | _ => `($(mkIdent `H))

open Lean PrettyPrinter in
/-- The note draws the union of a set of sets as `union`: which of the many `union`s of the book it
    is, is the panel's region, and `big` says nothing a picture of `E(E A) ⟶ E A` does not. -/
@[app_unexpander bigUnion] def unexpandBigUnion : Unexpander | _ => `($(mkIdent `union))

open Lean PrettyPrinter in
/-- AN INDEX FUNCTOR IS THE NOTE'S `[k]`, and the length it indexes is the whole of its name — one
    lane per AXIS, which is what lets `fcol` (`diag/draw.typ`) give each dimension of a matrix its
    own colour.  Both spellings of the one functor go through this: `Vec k` on functions, and the
    relator `[k]` bundles on relations, so the LANE and the OBJECT under it are written the same way
    and a cut reads as one composite instead of `Alg.Vec n` over `dTuple n A`. -/
@[app_unexpander Vec] def unexpandVec : Unexpander
  | `($_ $n) => `([$n])
  | _ => throw ()

open Lean PrettyPrinter in
/-- `Vec(n)` on relations is the same lane `[n]`, for the same reason. -/
@[app_unexpander Vec.Rel.tupleRelator] def unexpandTupleRelator : Unexpander
  | `($_ $n) => `([$n])
  | _ => throw ()

open Lean PrettyPrinter in
/-- One more index bracket on the BASE object, never at the end of the name: `A[m][n]` is
    `[m]([n](A))`, so the brackets read left to right in the order the wires of a cut do, and the
    bracket a nest adds goes in front of the ones already there. -/
private partial def spliceIndex {m} [Monad m] [MonadQuotation m] (s i : Term) : m Term := do
  match s with
  | `($b[$j]) => let b ← spliceIndex b i; `($b[$j])
  | _ => `($s[$i])

open Lean PrettyPrinter Delaborator SubExpr in
/-- AN INDEXED OBJECT IS THE NOTE'S `A[n]`, one bracket per index functor over it — the same
    spelling as the LANE `[n]` that carries it, which is what lets a cut be read as one composite
    (`scripts/scanline`) instead of a lane called one thing standing over an object called another.
    A delaborator and not an unexpander: the outermost bracket is written FIRST, so the nest has to
    be walked, and the syntax the elaborator produced for the inner object is what is spliced. -/
@[delab app.Freyd.Alg.RelSet.Tuple.dTuple] def delabDTuple : Delab := do
  guard ((← getExpr).getAppNumArgs == 2)
  let i ← withNaryArg 0 delab
  let inner ← withNaryArg 1 delab
  spliceIndex inner i

open Lean PrettyPrinter Delaborator SubExpr in
/-- `Vec(n)`'s object is the same `A[n]`: the object the lane `[n]` carries is spelled like the
    tuple object, or a product wire over it prints `Vec(A)×−` with the index gone. -/
@[delab app.Freyd.Functor.obj] def delabVecObj : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 6 && (e.getArg! 4).isAppOfArity ``Freyd.Alg.Vec 1)
  let i ← withNaryArg 4 (withNaryArg 0 delab)
  let inner ← withNaryArg 5 delab
  spliceIndex inner i

-- WHAT THE CASE STUDIES' MIDDLE BEAD OPENS.  The note draws each algebra's own coproduct —
-- `⦇[nil,cons](within(w)) ∪ [nil,π₂]⦈`, `⦇[wrap wrap,new ∪ (glue (ok w))]⦈` — where the name
-- `Salg` says nothing; `diag_unfold` is `diag/tool/ExprReader.lean`'s, as for `tour` above.
attribute [diag_unfold] RelSet.Knapsack.Salg RelSet.Paragraph.Salg
-- The prefix algebra is drawn written out, `⦇[nil,⊸ nil ∪ cons]⦈` (13.3.3b), never as its name.
attribute [diag_unfold] RelSet.ListRel.prefAlg
-- The take-while section's algebras the same way: the note draws what each arm DOES — `prefix`,
-- `cons`, `p`, `(π₁p→cons,⊸ nil)` — and `prefConsAlg`, `consScalarAlg` and the step `twStep` are
-- Lean names for those arms, so opened they are read off their own `match`.
attribute [diag_unfold] RelSet.GCTakeWhile.prefConsAlg
  RelSet.GCTakeWhile.twStep RelSet.CL.consScalarAlg
-- Each arm of that algebra with one `p` on it: the note writes what the arm DOES — `⊸ nil`,
-- `(p×𝟙)cons` — and the definition's own name says nothing, which is the whole of `diag_unfold`.
attribute [diag_unfold] RelSet.GCTakeWhile.discNil RelSet.GCTakeWhile.pcons
-- A DEFINITION THAT HIDES A COMPOSITE IS OPENED IN THE LABEL TOO.  `zeroPlus` is the union the note
-- writes `⊸ zero ∪ plus`, `mssPre` the inner specification `(prefix sum)%∋ est(≥)`; the structural
-- reader already opens both to draw them, so without the tag a row's picture and the label beside
-- it said different things.
attribute [diag_unfold] RelSet.MSS.zeroPlus RelSet.MSS.mssPre
-- `nilR` is the same story one step down: the note's `nil` is read off the CONSTANT the map creates
-- (`diag/tool/Label.lean`), and the arrow's own Lean name says nothing a picture of `𝟏⟼[E]` does not.
attribute [diag_unfold] RelSet.SL.nilR
-- The bag's algebra is the coproduct the note writes out, `[nil,snag]`, never its Lean name: the
-- arms are read off the `match` by `diag/tool/Label.lean` once the name is opened, and `arm₂` of it
-- is then the arm alone.
attribute [diag_unfold] RelSet.Tardy.bagAlg
-- `Λ S` is drawn as the unit bead and `E(S)` (13.3.2a, 13.4.4a): the spine is rewritten by the
-- transpose's factorisation, and `Λ 𝟙` folds back to the unit alone through `existsImage_id` and
-- the identity law.
attribute [diag_rewrite] Λ_eq_singleton_existsImage existsImage_id Cat.comp_id
-- An ARM is written by its own name (`snoc`, `snag`), never as the algebra restricted: `arm₂` of a
-- map is a map, and `diag/tool/Label.lean` then reads the name off the restricted function.
attribute [diag_rewrite] RelSet.SL.arm₂_graph
-- And the relator SLIDES INTO THE BRACKET: `F(X)[T,U]` is the note's `[T,(X×𝟙)U]`, one tape whose
-- second arm carries the `X`, never a box `F(X)` in front of the junction.
attribute [diag_rewrite] RelSet.SL.Fmap_comp_junc
-- The same slide at the tip-tree, where the relator is `𝟙+X²`: `F(X)[tip,bin] = [tip,(X×X)bin]`.
-- The RULE is the generator's — rewrite at a composite — and each polynomial functor states the
-- equation for its OWN shape, because the shape is what says which slots the `X` lands in.
attribute [diag_rewrite] RelSet.TT.Fmap_comp_con
-- The rose tree's `F` keeps its LETTER on the objects (`F([A]×[A])`) and is SPELLED OUT on the
-- arrows (`𝟙×list((R×R)°)`, §13.4.3a): one equation says which, and the object side never sees it.
attribute [diag_rewrite] RelSet.RT.F_map_eq
-- The unit bead is `singletonMap = Λ 𝟙`; opened, the `Λ` label case prints it `𝟙%∋`.
attribute [diag_unfold] singletonMap

-- A JOIN IS ONE PANEL PER OPERAND, with its own symbol set between them: the note's `∪` row of
-- `<lax-closure>` is two squares, where the MEET — the same type to the letter, and absent from
-- this line — is one bead on one panel (`laxNatural_inter_false`).  The tag lives here, not beside
-- the allegory's `∪`: the exe imports `diag` and `AOP`, so a tag in the drawer's own module reaches
-- no drawing.
attribute [diag_join "∪"] DistributiveAllegory.union

-- THE PARAMETRISED ALGEBRA'S `α` IS A FAMILY OVER ITS PARAMETER (§2.7), and its own notation writes
-- the letter alone: the note sets the parameter beneath it (`α`#sub[`A`], `α`#sub[`B`]), which is
-- the only thing that tells the two algebras of one naturality square apart.
attribute [diag_indexed] alphaT InitialAlgebra.α

-- A RE-BRACKETING DRAWS NOTHING.  `×` is flat in both calculi — the picture is the lanes `A×−`,
-- `B×−` over the rest, whichever way the product was bracketed — so an arrow that only moves the
-- brackets runs between two ends the peel reads as the ONE stack and there is no bead for it.
-- Tagged and never matched, like the join above: an arrow between two equal stacks is a bead like
-- any other, and only the constant says which arrows are the coherence of `×`.
attribute [diag_coherence] RelSet.Van.assoclR

-- THE VECTOR RELATOR IS THE NOTE'S `Vec(n)`, and its action on an arrow is that operator APPLIED:
-- `Vec(n)(cons)`, curried, because the length is the operator's own parameter and the arrow is what
-- it acts on — `Vec(n,cons)` would read as one operator of two arguments.  The printer's own
-- brackets say the currying and the label spells them by its one application rule.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tuple.tupleP] public meta def unexpandTupleP : Unexpander
  | `($_ $n $R) => `(($(mkIdent `Vec) $n) $R)
  | _ => throw ()

-- THE VERDICT THE ALGEBRA OF `AOP.A8_2.thinning_paths_alg` NEEDS: the note draws what sits inside
-- the `⦇ ⦈` rather than the whole fold, so its source is the bifunctor at two DIFFERENT arguments.
section
universe u
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {A B : 𝒜} {F : BiRelator 𝒜}

/-- `F(∋,∋)` IS LAX NATURAL in the first argument, for EVERY binary relator and every second
    argument: `F.map_comp` collapses the two composites to `F` of one relation, and what is left
    is `E(R)∋⊑∋R` under `F`.  The exporter needs a verdict for the family it cannot split, and
    `laxNatural_outside` only covers the one-argument steps `F(∋,𝟙)`, `F(𝟙,∋)`. -/
theorem laxNatural_birel_eps_eps (F : BiRelator 𝒜) (B : 𝒜) :
    LaxNatural (Relator.comp (Relator.idRelator 𝒜) (F.appr B))
      (Relator.comp (Relator.comp (Relator.idRelator 𝒜) powerRelator)
        (F.appr (PowerAllegory.powerObj B)))
      (fun a => F.map (∋ a) (∋ B)) := by
  intro a b R
  show F.map (powerRel R) (𝟙 (PowerAllegory.powerObj B)) ≫ F.map (∋ b) (∋ B)
      ⊑ F.map (∋ a) (∋ B) ≫ F.map R (𝟙 B)
  rw [← F.map_comp, ← F.map_comp, Cat.id_comp, Cat.comp_id]
  exact F.map_mono (powerRel_eps_lax R) (le_refl _)

end

end Freyd.Alg
