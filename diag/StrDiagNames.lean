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
import AOP.A5_5_AlgCat
-- `laxNatural_birel_eps_eps`, the verdict the exporter reads for the bifunctor family at `(∋,∋)`:
-- proved beside the other power beads, in scope here because the exporter looks it up by name.
import AOP.A5_7_PowerBeads
-- The case studies whose beads the note names in its own words: each is here only because an
-- unexpander below keys on one of its constants.
import AOP.A7_2_RelSet
import AOP.A7_3_Party
import AOP.A7_4_Cylinder
import AOP.A7_4_CylinderVecRel
import AOP.A7_5_Van
import AOP.A7_7_MSS
import AOP.A7_7_TakeWhile
import AOP.A7_7_Filter
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
-- THE ENVIRONMENT A CELL IS DRAWN FROM IS THIS IMPORT BLOCK, so a book section the note cites a law
-- of has to be in it: `inter_zero` (`T∩𝟘=𝟘`) is §2.50's, and a section the exporter cannot see is a
-- row it cannot draw.
import Freyd.S2_50
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

-- WHICH NAMES THE NOTE WRITES AS LEAN DECLARES THEM.  A predicate the note names in its own tables
-- (`R` entire, `R` a map, `R` symmetric), the domain and range operators, and a case study's own
-- relation are already the note's words, so there is nothing for a printing rule to rewrite — the
-- tag says so once per name, where an identity unexpander would say it in five lines each.  A
-- constant NOT here is still refused, which is what keeps `BiRelator.appl` out of a cell.
attribute [diag_noted] dom ran Entire Simple Map Symmetric subset simplePart codBox
  BiRelator.PreservesRecip Relator.PreservesRecip RelSet.Bracket.Assoc RelSet.Knapsack.Q
  RelSet.Paragraph.Q RelSet.Van.secureP RelSet.Tour.dTour Coreflexive Monotonic MonotonicAlg
  RelSet.CL.ConsList.cons RelSet.Tour.Qc RelSet.Tour.start
  RelSet.ListRel.zero RelSet.ListRel.plus RelSet.ListRel.succ RelSet.ListRel.div
  RelSet.ListRel.zeros RelSet.ListRel.pluss
  RelSet.Edit.mle RelSet.Edit.column RelSet.Edit.fstcol RelSet.Edit.nextcol RelSet.Edit.head RelSet.Edit.base
  RelSet.Edit.empty RelSet.Code.null

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
/-- The bifunctor with its FIRST argument fixed is the lane `F(A,−)`, the slot that still varies
    marked as CLAUDE.md marks it in `B×−`: two such lanes over one region (`F(A,−)`, `F(NA,−)`)
    differ by the argument, which the one letter `F` would hide. -/
@[app_unexpander BiRelator.appl] def unexpandAppl : Unexpander
  | `($_ $F $A) => `($F $A $(mkIdent (Name.mkSimple "−")))
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
/-- B&dM Ex 5.10's `unzip(F)`: the two objects are the wires' own, so the label names the relator. -/
@[app_unexpander unzip] def unexpandUnzip : Unexpander
  | `($_ $F $_ $_) => `($(mkIdent `unzip) $F)
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
/-- The rose-tree relator's action on an arrow is the note's `tree(f)` (ch. 7): the head is the
    note's word and the label rule brackets the operand of a longer-named operator. -/
@[app_unexpander RelSet.RT.tree] def unexpandRTTree : Unexpander
  | `($_ $args*) => `($(mkIdent `tree) $args*)
  | _ => `($(mkIdent `tree))

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

-- The snoc-list leaf object is the same object as the cons-list one, so it prints by the same rule.
attribute [delab app.Freyd.Alg.RelSet.SL.dL] delabDL

-- The note's `thin(Q)` is a DELIMITED operator, like `est(R)` (`AOP.A7_1`) and `P(R)` (`AOP.A5_4`)
-- which are declared this same way: an unexpander returns a term, and no term prints its own brackets.
notation:max "thin(" Q ")" => thinRel Q

-- THE SET OF SUMS IS SPELLED AS THE SET IT IS.  `sums xs ys` is the note's `{x+y∣x∈xs∧y∈ys}`,
-- built from the two arguments the term carries; a name says what the point is called and the
-- set-builder says what is IN it, which is what the corner of a distributivity square is read for.
-- A NOTATION for the reason `thin(` is one: no term prints its own brackets.
notation:max "{x+y∣x∈" xs "∧y∈" ys "}" => RelSet.sums xs ys

-- THE LEAST MEMBER IS SPELLED AS THE OPERATOR IT IS — an operator applied takes brackets, so
-- `minOf xs m` is the note's `min(xs)`.  Its second argument is the WITNESS that `xs` has a least
-- member, which the note does not write, so the unexpander drops it and the parser takes it as the
-- hole it is; a notation cannot do that, since a notation supplies every argument.
syntax:max "min(" term ")" : term
macro_rules | `(min($xs)) => `(RelSet.minOf $xs _)

open Lean PrettyPrinter in
@[app_unexpander RelSet.minOf] def unexpandMinOf : Unexpander
  | `($_ $xs $_m) => `(min($xs))
  | _ => throw ()

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
-- The party's `cost` drops its `rating` for the same reason `R` does: it is the section's context.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.costFn] def unexpandPartyCostFn : Unexpander | _ => `($(mkIdent `cost))
-- The list sum is the note's `sum`; the `c` only tells the cons-list function from the relation.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.csum] def unexpandCsum : Unexpander | _ => `($(mkIdent `sum))
-- The list length is the note's `length`, for the reason `csum` is `sum`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.clen] def unexpandClen : Unexpander | _ => `($(mkIdent `length))
-- The edit lanes are the base functor `F` of the section; the carrier is the wire under it.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.opF] def unexpandEditOpF : Unexpander | _ => `($(mkIdent `F))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.pairF] def unexpandEditPairF : Unexpander | _ => `($(mkIdent `F))
-- The section's order on lengths is written by its operator, as `leRel` is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.leqN] def unexpandEditLeqN : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≤")))
-- The section's own integer ordering is written by its operator, as `leRel` is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.leq] def unexpandPartyLeq : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≤")))
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
@[app_unexpander RelSet.Edit.unstepFn] def unexpandEditUnstepFn : Unexpander
  | _ => `($(mkIdent `unstep))
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
/-- `IsFHom f g h` is the note's F-homomorphism statement `h : f⟶g` — an arrow of `Alg(F)` from the
    algebra `f` to the algebra `g`, which a type ascription already spells. -/
@[app_unexpander IsFHom] def unexpandIsFHom : Unexpander
  | `($_ $f $g $h) => `(($h : $f ⟶ $g))
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
@[app_unexpander RelSet.Tuple.tupleRelator] def unexpandTupleRelator : Unexpander
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
/-- THE INDEXED OBJECT'S CARRIER IS THE INDEXED OBJECT.  `dTuple n A` is `⟨Fin n → A⟩`, so a TYPE
    that is a pi over `Fin n` whose codomain does not use the index IS that object's carrier and has
    to print the way the object does — `Fin n → X` is `X[n]`, through `spliceIndex` and not a second
    rule, so a numeric index, a compound one and a nest `Fin m → Fin n → X` all come out as the
    object forms do.  A pi whose codomain USES its argument indexes nothing and is left alone. -/
@[delab forallE] def delabFinPi : Delab := do
  let .forallE _ d b _ ← getExpr | failure
  guard (d.isAppOfArity ``Fin 1 && !b.hasLooseBVars)
  let i ← withBindingDomain (withNaryArg 0 delab)
  let inner ← withBindingBody `i delab
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

-- EVERY CONSTANT A LABEL MAY BE MADE OF IS REGISTERED HERE, spelling included.  `checkSpelled`
-- (`diag/tool/ExprReader.lean`) refuses a label carrying a constant no printing rule rewrote, so
-- the note's vocabulary is this file and nothing else: a constant added to a case study draws
-- nothing until its spelling is written down.  THE HEAD IS THE NAME, THE OPERANDS ARE THE
-- PRINTER'S — the clause keeps `$args*` where `gen` and `Q` above drop theirs, because a section
-- parameter is the panel's region and an ARGUMENT is part of what the arrow is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.party] def unexpandPartyParty : Unexpander
  | `($_ $args*) => `($(mkIdent `party) $args*)
  | _ => `($(mkIdent `party))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.choose] def unexpandPartyChoose : Unexpander
  | `($_ $args*) => `($(mkIdent `choose) $args*)
  | _ => `($(mkIdent `choose))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.interval] def unexpandTexInterval : Unexpander
  | `($_ $args*) => `($(mkIdent `interval) $args*)
  | _ => `($(mkIdent `interval))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.intern] def unexpandTexIntern : Unexpander
  | `($_ $args*) => `($(mkIdent `intern) $args*)
  | _ => `($(mkIdent `intern))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.bagify] def unexpandTardyBagify : Unexpander
  | `($_ $args*) => `($(mkIdent `bagify) $args*)
  | _ => `($(mkIdent `bagify))
open Lean PrettyPrinter in
@[app_unexpander RelSet.SL.arm₂] def unexpandSLArm2 : Unexpander
  | `($_ $args*) => `($(mkIdent `arm₂) $args*)
  | _ => `($(mkIdent `arm₂))
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.subseq] def unexpandListRelSubseq : Unexpander
  | `($_ $args*) => `($(mkIdent `subseq) $args*)
  | _ => `($(mkIdent `subseq))
open Lean PrettyPrinter in
@[app_unexpander RelSet.MSS.mss] def unexpandMSSmss : Unexpander
  | `($_ $args*) => `($(mkIdent `mss) $args*)
  | _ => `($(mkIdent `mss))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.partition] def unexpandParagraphPartition : Unexpander
  | `($_ $args*) => `($(mkIdent `partition) $args*)
  | _ => `($(mkIdent `partition))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.splits] def unexpandBracketSplits : Unexpander
  | `($_ $args*) => `($(mkIdent `splits) $args*)
  | _ => `($(mkIdent `splits))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.Op] def unexpandEditOp : Unexpander
  | `($_ $args*) => `($(mkIdent `Op) $args*)
  | _ => `($(mkIdent `Op))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.step] def unexpandEditStep : Unexpander
  | `($_ $args*) => `($(mkIdent `step) $args*)
  | _ => `($(mkIdent `step))
-- The tip-tree section's own bifunctor is the note's `F`, the letter every `F(R,S)` beside the
-- picture already uses; `RelSet.RT.F` above is the rose tree's, spelled the same for the same
-- reason.
open Lean PrettyPrinter in
@[app_unexpander RelSet.TT.F] def unexpandTTF : Unexpander
  | `($_ $args*) => `($(mkIdent `F) $args*)
  | _ => `($(mkIdent `F))
-- A SECTION'S STEP ALGEBRA IS THE NOTE'S `S`, the letter its `#leant` row is headed by — `Salg` is
-- only the Lean name, as `Kalg` is for the maximum-segment-sum step's `k`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.Salg] def unexpandParagraphSalg : Unexpander
  | _ => `($(mkIdent `S))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Knapsack.Salg] def unexpandKnapsackSalg : Unexpander
  | _ => `($(mkIdent `S))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.S] def unexpandPartyS : Unexpander
  | _ => `($(mkIdent `S))
-- The note's `cp` is the copy-and-pair map; `cpMap` is the Lean name.
open Lean PrettyPrinter in
@[app_unexpander cpMap] def unexpandCpMap : Unexpander
  | `($_ $args*) => `($(mkIdent `cp) $args*)
  | _ => `($(mkIdent `cp))
-- THE NAMES THE NOTE NEVER WRITES ITSELF: the suffix is Lean's disambiguator (`Fn`, `Rel`, `Alg`,
-- `Relator`, as `editFn` is `edit` above). The author's decision (2026-09-22): the algebras and
-- `sortRel` keep the Lean name; a bundled relator prints as the type it bundles (`op`, `Journey`).
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.wrapCatFn] def unexpandBracketWrapCat : Unexpander
  | `($_ $args*) => `($(mkIdent `wrapCatFn) $args*)
  | _ => `($(mkIdent `wrapCatFn))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.opRelator] def unexpandEditOpRelator : Unexpander
  | `($_ $args*) => `($(mkIdent `op) $args*)
  | _ => `($(mkIdent `op))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.editAlg] def unexpandEditAlg : Unexpander
  | `($_ $args*) => `($(mkIdent `editAlg) $args*)
  | _ => `($(mkIdent `editAlg))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.journeyRelator] def unexpandTourJourney : Unexpander
  | `($_ $args*) => `($(mkIdent `Journey) $args*)
  | _ => `($(mkIdent `Journey))
open Lean PrettyPrinter in
@[app_unexpander sortRel] def unexpandSortRel : Unexpander
  | `($_ $args*) => `($(mkIdent `sortRel) $args*)
  | _ => `($(mkIdent `sortRel))
-- The note's word for the arrow is `path`; the `R` is Lean's, as `detabR`'s is.
open Lean PrettyPrinter in
@[app_unexpander pathR] def unexpandPathR : Unexpander
  | `($_ $args*) => `($(mkIdent `path) $args*)
  | _ => `($(mkIdent `path))
-- B&dM p.198 writes `step`; the `path` prefix only keeps Lean's name apart from `Edit`'s step.
open Lean PrettyPrinter in
@[app_unexpander pathStep] def unexpandPathStep : Unexpander
  | `($_ $args*) => `($(mkIdent `step) $args*)
  | _ => `($(mkIdent `step))
-- THE CONCRETE CYLINDER'S ARROWS, for the reason `gen` and `paths` beside them are delaborators:
-- they take only implicit arguments and so print as bare constants, which no `app_unexpander`
-- fires on.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.moves, delab const.Freyd.Alg.Vec.moves]
def delabVecMoves : Delab := `($(mkIdent `moves))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.cons, delab const.Freyd.Alg.Vec.cons]
def delabVecCons : Delab := `($(mkIdent `cons))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.concat, delab const.Freyd.Alg.Vec.concat]
def delabVecConcat : Delab := `($(mkIdent `concat))
open Lean PrettyPrinter in
/-- §7.13's cylinder `est` IS §7.1's operator (`AOP.A7_1`) at a tuple, so it is written the way
    every DELIMITED operator is — `est(R)`, `thin(Q)`, `P(R)` — WITH ITS OPERAND: an operator
    applied to nothing is a constant, and dropping the relation left the cell claiming one where
    the statement has an argument.  The length is implicit and no factor of the name. -/
@[app_unexpander Freyd.Alg.Vec.Rel.est] def unexpandVecRelEst : Unexpander
  | `($_ $S) => `(est($S))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.Interval] def unexpandTexIntervalType : Unexpander
  | `($_ $args*) => `($(mkIdent `Interval) $args*)
  | _ => `($(mkIdent `Interval))
open Lean PrettyPrinter in
@[app_unexpander RelSet.SL.armQ₂] def unexpandSLArmQ2 : Unexpander
  | `($_ $args*) => `($(mkIdent `armQ₂) $args*)
  | _ => `($(mkIdent `armQ₂))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Knapsack.within] def unexpandKnapsackWithin : Unexpander
  | `($_ $args*) => `($(mkIdent `within) $args*)
  | _ => `($(mkIdent `within))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.tour] def unexpandTourTour : Unexpander
  | `($_ $args*) => `($(mkIdent `tour) $args*)
  | _ => `($(mkIdent `tour))
open Lean PrettyPrinter in
@[app_unexpander RelSet.pow] def unexpandRelSetPow : Unexpander
  | `($_ $args*) => `($(mkIdent `pow) $args*)
  | _ => `($(mkIdent `pow))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.ok] def unexpandParagraphOk : Unexpander
  | `($_ $args*) => `($(mkIdent `ok) $args*)
  | _ => `($(mkIdent `ok))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.fits] def unexpandParagraphFits : Unexpander
  | `($_ $args*) => `($(mkIdent `fits) $args*)
  | _ => `($(mkIdent `fits))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.unstep] def unexpandEditUnstep : Unexpander
  | `($_ $args*) => `($(mkIdent `unstep) $args*)
  | _ => `($(mkIdent `unstep))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.reduce] def unexpandCodeReduce : Unexpander
  | `($_ $args*) => `($(mkIdent `reduce) $args*)
  | _ => `($(mkIdent `reduce))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.decode] def unexpandCodeDecode : Unexpander
  | `($_ $args*) => `($(mkIdent `decode) $args*)
  | _ => `($(mkIdent `decode))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.Code] def unexpandCodeType : Unexpander
  | `($_ $args*) => `($(mkIdent `Code) $args*)
  | _ => `($(mkIdent `Code))
-- The edit section's thinning preorder joins `Code`'s, `Detab`'s and `Tardy`'s above: the note's
-- `Q`, stated over the section's own data.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.Q] def unexpandEditQ : Unexpander | _ => `($(mkIdent `Q))
-- The section's GRAPH OF THE SNOC LIST'S EMPTY CASE is the note's `nil`; the `R` is Lean's, as
-- `detabR`'s is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.SL.nilR] def unexpandSLNilR : Unexpander
  | `($_ $args*) => `($(mkIdent `nil) $args*)
  | _ => `($(mkIdent `nil))
-- THE TOP RELATION IS THE NOTE'S `⊤` — `thin(prefix°×(⊤+⊤))` is how its tables write it, and
-- `topMor` is the Lean name.  No Lean identifier, so it goes through the same escape `⊕` does.
open Lean PrettyPrinter in
@[app_unexpander topMor] def unexpandTopMor : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "⊤")))
-- The concrete cylinder's transition, beside its `moves` and `cons`.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.trans, delab const.Freyd.Alg.Vec.trans]
def delabVecTrans : Delab := `($(mkIdent `trans))

-- A SECTION'S RELATION, ORDER AND HELPER wear the note's letters, as `Party.R`, `Detab.V` and
-- `Van.Hrel` above do: which relation it is, is the definition line over the table.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.R] def unexpandTexR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.H] def unexpandTexH : Unexpander | _ => `($(mkIdent `H))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.Q] def unexpandTexQ : Unexpander | _ => `($(mkIdent `Q))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.Real] def unexpandTexReal : Unexpander
  | `($_ $args*) => `($(mkIdent `Real) $args*)
  | _ => `($(mkIdent `Real))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.V] def unexpandEditV : Unexpander | _ => `($(mkIdent `V))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.inrange] def unexpandTexInrange : Unexpander
  | `($_ $args*) => `($(mkIdent `inrange) $args*)
  | _ => `($(mkIdent `inrange))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.val] def unexpandTexVal : Unexpander
  | `($_ $args*) => `($(mkIdent `val) $args*)
  | _ => `($(mkIdent `val))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.step] def unexpandTexStep : Unexpander
  | `($_ $args*) => `($(mkIdent `step) $args*)
  | _ => `($(mkIdent `step))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.arb] def unexpandTexArb : Unexpander
  | `($_ $args*) => `($(mkIdent `arb) $args*)
  | _ => `($(mkIdent `arb))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.tourAlg] def unexpandTourAlg : Unexpander
  | `($_ $args*) => `($(mkIdent `tourAlg) $args*)
  | _ => `($(mkIdent `tourAlg))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.zip, delab const.Freyd.Alg.Vec.zip]
def delabVecZip : Delab := `($(mkIdent `zip))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.cp, delab const.Freyd.Alg.Vec.cp]
def delabVecCp : Delab := `($(mkIdent `cp))
-- THE PRODUCT OF TWO MAPS IS THE NOTE'S `f×g`, the same spelling the allegory's own `prodMap`
-- wears; `Prod.map` is the underlying function's Lean name.  No fallback: a shape this clause does
-- not match is one nobody has written a spelling for, and the label gate says so.
open Lean PrettyPrinter in
@[app_unexpander Prod.map] def unexpandCoreProdMap : Unexpander
  | `($_ $f $g) => `($f × $g)
  | _ => throw ()
-- THE SUM OF TWO ARROWS IS THE NOTE'S `R+S` (B&dM 5.10).  A delaborator, not an unexpander: the two
-- coproducts `sumMap` runs between are explicit arguments, and only the last two are the arrows.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.sumMap] def delabSumMap : Delab := do
  let n := (← SubExpr.getExpr).getAppNumArgs
  guard (n ≥ 4)
  let r ← SubExpr.withNaryArg (n - 2) delab
  let s ← SubExpr.withNaryArg (n - 1) delab
  `($r + $s)

-- THE BIFUNCTOR ON OBJECTS is the note's `F(A,B)`, the brackets the label printer's own comma
-- list — `BiRelator.appl` above writes the one-argument lane the same way.
open Lean PrettyPrinter in
@[app_unexpander BiRelator.obj] def unexpandBiRelObj : Unexpander
  | `($_ $F $A $B) => `($F $A $B)
  | _ => throw ()
-- A DATATYPE'S OWN Lean carrier is the note's object, as its `d…` wrapper above already is: the
-- rose tree is the note's `tree`, and which of the two tree datatypes a section uses is the
-- section's business.
open Lean PrettyPrinter in
@[app_unexpander RelSet.RT.Rose] def unexpandRoseType : Unexpander
  | `($_ $args*) => `($(mkIdent `tree) $args*)
  | _ => `($(mkIdent `tree))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.Journey] def unexpandJourneyType : Unexpander
  | `($_ $args*) => `($(mkIdent `Journey) $args*)
  | _ => `($(mkIdent `Journey))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.Iv] def unexpandTexIv : Unexpander
  | `($_ $args*) => `($(mkIdent `Iv) $args*)
  | _ => `($(mkIdent `Iv))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.Digit] def unexpandTexDigit : Unexpander
  | `($_ $args*) => `($(mkIdent `Digit) $args*)
  | _ => `($(mkIdent `Digit))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Sub] def unexpandRelSetSub : Unexpander
  | `($_ $args*) => `($(mkIdent `Sub) $args*)
  | _ => `($(mkIdent `Sub))
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.segment] def unexpandListRelSegment : Unexpander
  | `($_ $args*) => `($(mkIdent `segment) $args*)
  | _ => `($(mkIdent `segment))
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.catR] def unexpandListRelCatR : Unexpander
  | `($_ $args*) => `($(mkIdent `cat) $args*)
  | _ => `($(mkIdent `cat))
-- The note writes `partition≜concat°` and says in the row beside it that this `concat` is the one
-- restricted to non-empty segments, so the restriction is the note's words, not a second name.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.concatNE] def unexpandListRelConcatNE : Unexpander
  | `($_ $args*) => `($(mkIdent `concat) $args*)
  | _ => `($(mkIdent `concat))
-- THE GRAPH AND THE FUNCTION IT IS TAKEN OF SHARE THE NOTE'S NAME, as `edit` does above: one
-- arrow, drawn as a map in one panel and as a relation in another.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.reduceFn] def unexpandCodeReduceFn : Unexpander
  | `($_ $args*) => `($(mkIdent `reduce) $args*)
  | _ => `($(mkIdent `reduce))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.splitsFn] def unexpandBracketSplitsFn : Unexpander
  | `($_ $args*) => `($(mkIdent `splits) $args*)
  | _ => `($(mkIdent `splits))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Filter.filter] def unexpandFilterFilter : Unexpander
  | `($_ $args*) => `($(mkIdent `filter) $args*)
  | _ => `($(mkIdent `filter))
open Lean PrettyPrinter in
@[app_unexpander RelSet.GCTakeWhile.takewhile] def unexpandTakewhile : Unexpander
  | `($_ $args*) => `($(mkIdent `takewhile) $args*)
  | _ => `($(mkIdent `takewhile))
-- The party section's two branches are the note's `include` and `exclude`; `includeR` above is the
-- same arrow taken as a relation.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.include] def unexpandPartyInclude : Unexpander
  | `($_ $args*) => `($(mkIdent `include) $args*)
  | _ => `($(mkIdent `include))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.intervalFn] def unexpandTexIntervalFn : Unexpander
  | `($_ $args*) => `($(mkIdent `interval) $args*)
  | _ => `($(mkIdent `interval))
-- THE IDENTITY LANE IS THE NOTE'S `𝟙`, the same letter the identity arrow wears; which category
-- it is the identity of is the region the lane runs in.
open Lean PrettyPrinter in
@[app_unexpander Relator.idRelator] def unexpandIdRelator : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "𝟙")))
-- A CONSTANT LANE IS THE OBJECT IT IS CONSTANTLY: the wire carries `𝟏`, and `Relator.const` is
-- only how Lean says the wire does not vary.
open Lean PrettyPrinter in
@[app_unexpander Relator.const] def unexpandRelatorConst : Unexpander
  | `($_ $A) => `($A)
  | _ => throw ()
open Lean PrettyPrinter Delaborator SubExpr in
/-- A COMBINATOR RELATOR'S ACTION ON AN OBJECT IS THE OBJECT IT REDUCES TO: `(const V).obj X` is
    `V` and `(V×𝟙).obj X` is `V×X`, so the label is that object and the wire is `E(V×list⁺(V))`.
    Spelling the relator and applying it to the argument (`V(list⁺(V))`, `(V×𝟙)(list⁺(V))`) writes
    an action nothing performs, and `EV(list⁺(V))` reads as two functors composed.  The reduction
    and the list of combinators are `StrDiag.relatorObj?`'s, the one the label and the wire stack
    ask too, so every other relator keeps its `F(X)`/`FX` in all three. -/
@[delab app.Freyd.Functor.obj] def delabRelatorObj : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 6)
  let some v ← StrDiag.relatorObj? (e.getArg! 4) e | failure
  PrettyPrinter.delab v
-- THE PRODUCT OF TWO RELATORS IS THE NOTE'S `F×G`, the coproduct's `F+G` mirrored.
open Lean PrettyPrinter in
@[app_unexpander Relator.prod] def unexpandRelatorProd : Unexpander
  | `($_ $F $G) => `($F × $G)
  | _ => throw ()
-- The bag's quotient is taken of the note's `perm`, the permutation relation `16-greedy` defines
-- as `bagify bagify°`; `permSetoid` is the Lean bundle carrying it.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.permSetoid] def unexpandPermSetoid : Unexpander
  | `($_ $args*) => `($(mkIdent `perm) $args*)
  | _ => `($(mkIdent `perm))

-- THE CORE TYPES THE NOTE WRITES AS LEAN DOES — `[[Int]]⟶[[Int]]` is a type cell, not a Lean
-- spelling that leaked.  They are registered here for the same reason every other name is: the
-- vocabulary is this file, and a type nobody wrote down draws nothing.
open Lean PrettyPrinter Delaborator in
@[delab app.Int, delab const.Int] def delabIntName : Delab := `($(mkIdent `Int))
open Lean PrettyPrinter Delaborator in
@[delab app.Char, delab const.Char] def delabCharName : Delab := `($(mkIdent `Char))
open Lean PrettyPrinter Delaborator in
@[delab app.Nat, delab const.Nat] def delabNatName : Delab := `($(mkIdent `Nat))
-- The counterexample's objects and relation are the note's `A`, `B`, `R`; which sets they are, is
-- the paragraph above the panel.  Delaborators, because they take no explicit argument.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.MeetCounterex.A, delab const.Freyd.Alg.MeetCounterex.A]
def delabMeetCounterexA : Delab := `($(mkIdent `A))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.MeetCounterex.B, delab const.Freyd.Alg.MeetCounterex.B]
def delabMeetCounterexB : Delab := `($(mkIdent `B))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.MeetCounterex.R, delab const.Freyd.Alg.MeetCounterex.R]
def delabMeetCounterexR : Delab := `($(mkIdent `R))
open Lean PrettyPrinter Delaborator in
@[delab app.Unit, delab const.Unit] def delabUnitName : Delab := `($(mkIdent `Unit))
open Lean PrettyPrinter in
@[app_unexpander Quotient] def unexpandQuotientName : Unexpander
  | `($_ $args*) => `($(mkIdent `Quotient) $args*)
  | _ => `($(mkIdent `Quotient))
-- `Fin` KEEPS ITS ARGUMENT — `Fin n` is the object, where `Int` and `Char` are whole names; an
-- unexpander and not a delaborator, so the index the printer already wrote stands.
open Lean PrettyPrinter in
@[app_unexpander Fin] def unexpandFinName : Unexpander
  | `($_ $args*) => `($(mkIdent `Fin) $args*)
  | _ => `($(mkIdent `Fin))

end Freyd.Alg
