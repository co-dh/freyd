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
import AOP.A2_6
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
import AOP.A8_2_Exec
import AOP.A8_4_Knapsack
import AOP.A8_5_Paragraph
import AOP.A9_2_Edit
import AOP.A9_3_Bracket
import AOP.A9_4_Code
-- §9.1's worked example, segmenting a list: its `T`, `h` and the table of `h`'s values.
import AOP.A9_0_SegmentExample
import AOP.A10_2_Detab
import AOP.A10_3_Tardy
import AOP.A10_4_Tex
-- §6.5's membership, which Theorem 6.4's claim draws as a bead.
import AOP.A6_5
-- `tour`, whose body the note draws: a tag names a constant, so its module has to be in scope.
import AOP.A8_6_Tour
-- `star`, `sub`'s chains and `theta` (§6.7), whose beads the closure displays draw.
import AOP.A6_7
-- §6.6's sorting calculations, which the note's chapter 6 draws step by step.
import AOP.A6_6b_SortConcrete
import AOP.A6_6e_Quicksort
import AOP.A6_6c_ISort
-- B&dM §6.1 and §6.4's worked programs, whose derivations chapter 6 of the companion note draws.
import AOP.A6_1_Digits
import AOP.A6_4_FastExp
-- THE ENVIRONMENT A CELL IS DRAWN FROM IS THIS IMPORT BLOCK, so a book section the note cites a law
-- of has to be in it: `inter_zero` (`T∩𝟘=𝟘`) is §2.50's, and a section the exporter cannot see is a
-- row it cannot draw.
import Freyd.S2_50
-- `diag_unfold`, declared where it is read: an attribute is usable only below the module declaring it.
import diag.tool.Tags

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
attribute [diag_noted] dom ran Entire Simple Map Symmetric simplePart codBox
  BiRelator.PreservesRecip Relator.PreservesRecip RelSet.Bracket.Assoc RelSet.Knapsack.Q
  RelSet.Paragraph.Q Coreflexive Monotonic Freyd.Alg.Inductive Freyd.Alg.ThinCondition
  RelSet.CL.ConsList.cons RelSet.Tour.start
  RelSet.ListRel.zero RelSet.ListRel.plus RelSet.ListRel.succ RelSet.ListRel.div
  RelSet.ListRel.zeros RelSet.ListRel.pluss
  RelSet.Bracket.gR RelSet.Bracket.zeroFn RelSet.Bracket.opbFn
  RelSet.Edit.mle RelSet.Edit.column RelSet.Edit.fstcol RelSet.Edit.nextcol RelSet.Edit.head RelSet.Edit.base
  RelSet.Edit.empty RelSet.Code.null RelSet.corefl RelSet.leOn
attribute [diag_noted] RelSet.Poly.listcp RelSet.Poly.listcpFn RelSet.Poly.linear RelSet.Poly.hasArg₂
  RelSet.Poly.relator RelSet.Poly.PolyF RelSet.Poly.PolyC RelSet.Poly.PolyC.zer RelSet.Poly.PolyC.one
  RelSet.Poly.PolyC.const RelSet.Poly.PolyC.arg₁ RelSet.Poly.PolyC.arg₂ RelSet.CL.clF RelSet.ListRel.cppFn RelSet.ListRel.cprFn RelSet.ListRel.cplFn
  RelSet.CL.bumpFold RelSet.ListRel.thinlist
-- A map's type cell labels its ends (`TypeRender.funPieces`), and B&dM write the integers `Int`.
attribute [diag_noted] _root_.Int
attribute [diag_noted] RelSet.RT.tree RelSet.TB.tree RelSet.Party.party RelSet.Party.choose RelSet.Tex.interval RelSet.Tex.intern RelSet.Tardy.bagify RelSet.ListRel.subseq RelSet.MSS.mss RelSet.Paragraph.partition RelSet.Bracket.splits RelSet.Edit.step RelSet.TT.F RelSet.Bracket.wrapCatFn RelSet.Tex.Interval RelSet.Knapsack.within RelSet.Tour.tour RelSet.pow RelSet.Paragraph.ok RelSet.Paragraph.fits RelSet.Edit.unstep RelSet.Code.reduce RelSet.Code.decode RelSet.Code.Code RelSet.Tex.Real RelSet.Tex.inrange RelSet.Tex.val RelSet.Tex.step RelSet.Tex.arb RelSet.Tex.f RelSet.Tex.Prog.Reach RelSet.Tour.Journey RelSet.Tex.Iv RelSet.Tex.Digit RelSet.Sub RelSet.ListRel.segment RelSet.Filter.filter RelSet.GCTakeWhile.takewhile RelSet.Party.include Quotient RelSet.Knapsack.g₁ RelSet.Knapsack.g₂ RelSet.Paragraph.g₁ RelSet.Paragraph.g₂ RelSet.Tour.g₁ RelSet.Tour.g₂ RelSet.ListRel.listcp
-- The case studies' own words, every explicit argument printed as Lean has it.
attribute [diag_noted] RelSet.Detab.R RelSet.Tardy.add RelSet.ListRel.total RelSet.Tour.next2
  RelSet.Tour.head2 RelSet.Tour.Tour RelSet.Paragraph.glue RelSet.Paragraph.new RelSet.Paragraph.sqr
  RelSet.Paragraph.start RelSet.MSS.zero RelSet.MSS.plus RelSet.Digits.wrap RelSet.Digits.snoc
  RelSet.Digits.val RelSet.Digits.embed RelSet.Digits.op RelSet.Digits.Digit RelSet.Digits.Decimal
  RelSet.FastExp.Bit RelSet.FastExp.zero RelSet.FastExp.one RelSet.FastExp.shift RelSet.FastExp.convert
  RelSet.FastExp.exp RelSet.FastExp.mod RelSet.FastExp.Exp.op RelSet.FastExp.Modulus.op RelSet.Code.Q
  RelSet.Detab.tb RelSet.Detab.nl RelSet.Detab.blank RelSet.Van.bmax RelSet.Party.S wrapz
  RelSet.Tex.R RelSet.Tex.H RelSet.Tex.Q RelSet.Tex.l RelSet.Tex.r RelSet.Tex.zero RelSet.Tex.shift
  RelSet.Tex.w RelSet.Tex.extern RelSet.Bracket.nonsingle RelSet.Bracket.loop RelSet.TT.Tree.tip
  RelSet.TT.Tree.bin RelSet.Code.Code.sym RelSet.Code.Code.ptr RelSet.Bracket.cat RelSet.SL.arm₂
  _root_.Fin RelSet.Edit.Op.cpy RelSet.Edit.Op.ins RelSet.ListRel.perm
  RelSet.Sort.flatten RelSet.Sort.join RelSet.Sort.fork RelSet.Sort.null RelSet.Sort.embed
  RelSet.Sort.base RelSet.ISort.add
-- Renamed to the book's word (B&dM p.86 "preorder", Ex 6.35 "monotonic", §6.4 `Bin`, §7.3 `exclude`).
attribute [diag_noted] preorder monotonic RelSet.Tardy.bag RelSet.FastExp.Bin RelSet.Party.exclude

open Lean PrettyPrinter Delaborator SubExpr in
/-- AN OBJECT THE NOTE HAS NO WORD FOR IS THE SET IT WRAPS: a `def` whose body is a one-field record
    (`dRose A ≜ ⟨Rose A⟩`) prints as that field, so `dRose A` is `tree A` by `Rose`'s own rule.  A
    constant the note does name (`diag_noted`, or a rule of its own) keeps its name. -/
@[delab app] def delabWrapperObject : Delab := do
  let e ← getExpr
  let .const c ls := e.getAppFn | failure
  let env ← getEnv
  let some (.defnInfo d) := env.find? c | failure
  if !(appUnexpanderAttribute.getEntries env c).isEmpty || (← labelled `diag_noted).contains c then failure
  let v := (d.value.instantiateLevelParams d.levelParams ls).beta e.getAppArgs
  let .const k _ := v.getAppFn | failure
  let some (.ctorInfo ci) := env.find? k | failure
  let some (.inductInfo ii) := env.find? ci.induct | failure
  unless ci.numFields == 1 && ii.ctors.length == 1 && v.getAppNumArgs == ci.numParams + 1 do failure
  withTheReader SubExpr (fun s => { s with expr := v.appArg! }) delab

-- THE ARMS WHOSE BODY IS POINTWISE.  `gArmFn`/`sizeArmFn` (and `kStep`/`bagPenalty` below) compute
-- on points, so their body prints no arrow; the spelling stays until each is restated point-free.
open Lean PrettyPrinter in
/-- The path count is the note's `3^m`; `pow3` sits inside a `Vec` type index, where the label
    printer opens no `diag_unfold`. -/
@[app_unexpander Vec.pow3] def unexpandPow3 : Unexpander
  | `($_ $m) => `(3 ^ $m)
  | _ => throw ()
-- The constructor map is `[nil,cons]` only at the empty leaf; a leaf carrying a value is B&dM's
-- `list⁺` and its map is `[wrap,cons]`.  A DELABORATOR: the leaf type is implicit, so only the term has it.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Freyd.Alg.RelSet.CL.con] def delabCLCon : Delab := do
  let args := (← getExpr).getAppArgs
  if args.size < 2 || args.size > 3 then failure
  let leaf := if ← Meta.isDefEq args[0]! (mkConst ``Unit) then "nil" else "wrap"
  let f := mkIdent (Name.mkSimple s!"[{leaf},cons]")
  if args.size == 2 then `($f) else `($f $(← withAppArg delab))
-- The node arm of `g≜[zero,(𝟙×sz)² opb π₁]`, and of the size algebra `[zero,distr [𝟙×c,𝟙×p] plus]`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.gArmFn] def unexpandBracketGArmFn : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "(𝟙×sz)² opb π₁")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.sizeArmFn] def unexpandCodeSizeArmFn : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "distr [𝟙×c,𝟙×p] plus")))
-- The algebras a section names but the note writes by their body: a union of two graphs, or the
-- graph of a map given by a `match` on a coproduct, whose arms `mapLabel` reads as the junction.
attribute [diag_unfold] RelSet.Edit.editAlg RelSet.Paragraph.partAlg RelSet.Tour.tourAlg
  RelSet.Knapsack.dropFn RelSet.Tour.droplAlgFn RelSet.Tour.droprAlgFn RelSet.Paragraph.newAlgFn
  RelSet.Paragraph.glueAlgFn RelSet.Edit.baseStepFn
-- `Op.del` shares its last component with another `del`, so the printer would qualify it; the
-- edit operation is the book's bare `del a` (p.225).
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.Op.del] def unexpandEditDel : Unexpander
  | `($_ $a) => `($(mkIdent `del) $a)
  | `($_:ident) => `($(mkIdent `del))
  | _ => throw ()
-- `dNE A ≜ dCL A A` is no record but `list⁺`'s own name, the note's `L`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.dNE] def unexpandDNE : Unexpander
  | `($_ $A) => `($(mkIdent (Name.mkSimple "L")) $A)
  | _ => throw ()

-- WHICH DEFINITIONS A PICTURE OPENS: the `AOP` constants the note draws opened — `tour%∋` against
-- the note's `⦇listcp(F)⟨g₁,g₂⟩cat thinlist(Q)⦈`.  `diag_unfold` is `diag/tool/Tags.lean`'s,
-- the mirror of `diag_induced`; the tags are here for the same reason `diag_induced`'s are, that
-- the note's spelling is the DIAGRAM's vocabulary and not the algebra's.
attribute [diag_unfold] RelSet.Tour.tour
-- "`S` preserves `Q`" is DRAWN by its inequation `F(Q)S⊑SQ`, as B&dM's (7.2) is; the formula keeps `Pres(S,Q)`.
attribute [diag_drawn_open] Pres

-- THE DUPLICATION RELATOR IS WRITTEN OUT AS THE PRODUCT IT IS: the note's corner is `A×A` and its
-- side `R×R`, never `Δ(A)` — `Δ` is `Relator.prod` of two identities (`AOP.A5_2`), and a bundle
-- built out of bundles has no name of its own, which is what every other product relator already
-- draws by (`openBuiltField?`).
attribute [diag_unfold] Δ

-- A naturality premise is the note's adjective on the family (§5.7: `φ` is "lax", "oplax", "strictly
-- natural"); `F`, `G` are `φ`'s own type, which the picture beside the formula already draws.
open Lean PrettyPrinter in
@[app_unexpander LaxNatural] def unexpandLaxNatural : Unexpander
  | `($_ $_ $_ $φ) => `($(mkIdent `lax) $φ)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander StrictNatural] def unexpandStrictNatural : Unexpander
  | `($_ $_ $_ $φ) => `($(mkIdent `strict) $φ)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander OpLaxNatural] def unexpandOpLaxNatural : Unexpander
  | `($_ $_ $_ $φ) => `($(mkIdent `oplax) $φ)
  | _ => throw ()

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
/-- A Bool test read as a predicate is still the test: the note writes `corefl(p)`, never the
    coercion between `Bool` and `Prop`. -/
@[app_unexpander RelSet.GCTakeWhile.holds] def unexpandHolds : Unexpander
  | `($_ $p) => `($p)
  | _ => throw ()

open Lean PrettyPrinter in
/-- B&dM's `head : Line ⟵ Para`, the first line of a paragraph (§8.5). -/
@[app_unexpander RelSet.Paragraph.head] def unexpandHeadLine : Unexpander
  | `($_:ident) => `($(mkIdent `head))
  | `($_ $p) => `($(mkIdent `head) $p)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The preorder a measure induces is the note's `length≤length°`. -/
@[app_unexpander RelSet.leOn] def unexpandLeOn : Unexpander
  | `($_ $f) => `($f ≤ $f°)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The carrier of `F X = L + E×X`, written as the sum it is (B&dM's `FX=𝟏+A×X`). -/
@[app_unexpander RelSet.CL.Fobj] def unexpandCLFobj : Unexpander
  | `($_ $L $E $C) => `($L + $E × $C)
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
/-- The cost order on paths is the note's `R ≜ sum≤sum°`; the length is the wire's own type. -/
@[app_unexpander Vec.Rel.costLE] def unexpandCostLE : Unexpander
  | `($_ $_) => `($(mkIdent `R))
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



-- A DATATYPE'S CARRIER IS THE NOTE'S OBJECT, under the note's own name for it: `tree(A)`,
-- `list⁺(A)`.  The unexpander writes the NAME, applied; the BRACKETS are the label printer's
-- (`appShow`), which puts them round the operand of every juxtaposed application, because
-- juxtaposition is composition and `tree A` reads as two things composed (CLAUDE.md).  One clause
-- per carrier, keyed on the constant — the tree the note draws is the tip-tree as much as the rose
-- tree, and the element type is the one argument either takes.


open Lean PrettyPrinter in
@[app_unexpander RelSet.TT.Tree] def unexpandTreeType : Unexpander
  | `($_ $A) => `($(mkIdent `tree) $A)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The binary-tree relator (§6.6 quicksort) is the note's lane `tree` as much as the tip tree's. -/
@[app_unexpander RelSet.TB.treeRelator] def unexpandTBTreeRelator : Unexpander
  | `($_:ident) => `($(mkIdent `tree))
  | _ => throw ()



open Lean PrettyPrinter in
@[app_unexpander RelSet.TB.Tree] def unexpandTBTree : Unexpander
  | `($_ $A) => `($(mkIdent `tree) $A)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The binary tree's BASE relator is the book's `F` (p.154 `F f = f×id×f`), as `RT.F` is. -/
@[app_unexpander RelSet.TB.F] def unexpandTBF : Unexpander
  | `($_ $_) => `($(mkIdent `F))
  | _ => throw ()

-- `pow` is `Rel(Set)`'s power object, the object the note writes `P` (`P A` in `S2_40`).
open Lean PrettyPrinter in
@[app_unexpander RelSet.pow] def unexpandRelSetPow : Unexpander
  | `($_ $A) => `($(mkIdent `P) $A)
  | _ => throw ()


-- The relator's ACTION on an arrow is the same letter applied: `nelist R` is `L(R)`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.nelist] def unexpandNEListMap : Unexpander
  | `($_ $R) => `($(mkIdent (Name.mkSimple "L")) $R)
  | _ => throw ()

-- The NATURAL NUMBERS are the note's `ℕ`.  Keyed `app.Nat`: the delaborator files a bare constant as a
-- nullary application, so a `const.Nat` key alone never fires and the label printed `Nat`.
open Lean PrettyPrinter Delaborator in
@[delab app.Nat] def delabNat : Delab := `($(mkIdent (Name.mkSimple "ℕ")))

-- The CARRIER needs the clause as much as the object: `NEList A` is an `abbrev`, so the term keeps
-- the abbreviation and the `ConsList A A` delaborator below never sees it — a seam between two
-- declared objects is labelled from the carrier and would print the Lean name.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.NEList] def unexpandNEListType : Unexpander
  | `($_ $A) => `($(mkIdent (Name.mkSimple "L")) $A)
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
    `($(mkIdent (Name.mkSimple "L")) $(← withAppArg delab))
  -- Any other leaf (§8.6's `City×City`, or a leaf left general) names no list the note has a word
  -- for: the type is the carrier of the base functor `F`'s initial algebra, which is `μF`.
  else `($(mkIdent (Name.mkSimple "μF")))

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

-- THE NOTE'S ARITHMETIC, as B&dM sets it (p.263: `⌊10b⌋`, `10a−d`, `[d]⧺x`): closed up, a product
-- by juxtaposition.  A category of its own, so no source file parses these (`f(x)` would be a product).
declare_syntax_cat noteArith
syntax:70 (name := noteMul) term:70 noWs term:71 : noteArith
syntax:70 (name := noteDot) term:70 "·" term:71 : noteArith
syntax:70 (name := noteDiv) term:70 "/" term:71 : noteArith
syntax:65 (name := noteSub) term:65 "−" term:66 : noteArith
syntax:65 (name := noteCat) term:66 "⧺" term:65 : noteArith
syntax:max (name := noteFloor) "⌊" term "⌋" : noteArith
syntax:max (name := noteTuple) "(" term "," term ")" : noteArith

open Lean in
/-- The first (`last = false`) or last token of a printed term. -/
partial def stxLeaf (last : Bool) : Syntax → Option Syntax
  | s@(.atom ..) | s@(.ident ..) => some s
  | .node _ _ args => (if last then args.reverse else args).findSome? (stxLeaf last)
  | .missing => none

open Lean in
/-- `ab`, or `a·b` where juxtaposition would weld two tokens into another one: a numeral after
    anything (`n·3`, `3·2^m`), or anything after a name of two letters or more. -/
def mulStx (a b : Syntax) : Syntax :=
  let num := match stxLeaf false b with | some (.atom _ v) => v.front.isDigit | _ => false
  let word := match stxLeaf true a with
    | some (.ident _ _ n _) => !(n.toString.drop 1).all (· == '\'')
    | _ => false
  if num || word then .node .none ``noteDot #[a, mkAtom "·", b] else .node .none ``noteMul #[a, b]

open Lean PrettyPrinter in
@[app_unexpander HMul.hMul] def unexpandNoteMul : Unexpander
  | `($_ $a $b) => pure (mulStx a b)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander HSub.hSub] def unexpandNoteSub : Unexpander
  | `($_ $a $b) => pure (.node .none ``noteSub #[a, mkAtom "−", b])
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander HDiv.hDiv] def unexpandNoteDiv : Unexpander
  | `($_ $a $b) => pure (.node .none ``noteDiv #[a, mkAtom "/", b])
  | _ => throw ()

-- A COERCION PRINTS AS WHAT IT COERCES: a digit used as a number is `d`, never `↑↑d`.  Read off the
-- `@[coe]` registry, so every coercion Lean knows of goes the same way.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app] def delabNoteCoe : Delab := do
  let e ← getExpr
  let .const c _ := e.getAppFn | failure
  let some info ← Meta.getCoeFnInfo? c | failure
  unless info.type == .coe && e.getAppNumArgs == info.numArgs do failure
  withNaryArg info.coercee delab

-- A SUBTYPE'S VALUE IS ITS COERCION, `↑p`, as Mathlib registers it; core Lean leaves `Subtype.val`
-- out of the `@[coe]` registry, so a legal interval's bound `p.1.lo` printed `lo(Subtype.val p)`.
attribute [coe] Subtype.val

-- A cons-list VALUE is written as the list it is: `cons a (cons b [])` is `[a,b]`, and a variable
-- tail is the book's `[a]⧺x`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.CL.ConsList.cons] def unexpandConsLit : Unexpander
  | `($_ $x []) => `([$x])
  | `($_ $x [$xs,*]) => `([$x, $xs,*])
  | `($_ $x $xs) => do pure (.node .none ``noteCat #[← `([$x]), mkAtom "⧺", xs])
  | _ => throw ()

-- A cons-list's LEAF prints by what the leaf is, read off the type arguments `L E`: a leaf of the
-- element type is the one-element list `[x]`, a `Unit` leaf the empty list `[]`; any other leaf
-- keeps the constructor's own name.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Freyd.Alg.RelSet.CL.ConsList.wrap] def delabConsWrap : Delab := do
  let e ← getExpr
  unless e.getAppNumArgs == 3 do failure
  let args := e.getAppArgs
  if (← Meta.isDefEq args[0]! args[1]!) then
    let x ← withAppArg delab
    `([$x])
  else if (← Meta.isDefEq args[0]! (.const ``Unit [])) then `([])
  else failure

-- The segmenting example's `T` and `h` are the note's letters; implicit-only, so delaborators.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.RelSet.Segment.T, delab const.Freyd.Alg.RelSet.Segment.T]
def delabSegmentT : Delab := `($(mkIdent `T))
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.RelSet.Segment.h, delab const.Freyd.Alg.RelSet.Segment.h] def delabSegmentH : Delab := `($(mkIdent `h))

-- The coproduct injections applied to a point are applications, so they take parentheses.
notation:max "l(" x ")" => Sum.inl x
notation:max "r(" x ")" => Sum.inr x
-- …and a TUPLE operand is that application's own comma list, `r(e,x)`: the tuple's brackets beside
-- the injection's would print `r((e, x))`.  Print-only syntax, read by no elaborator.
syntax:max "l(" term "," term,+ ")" : term
syntax:max "r(" term "," term,+ ")" : term
open Lean PrettyPrinter in
@[app_unexpander Sum.inl] def unexpandInlTuple : Unexpander
  | `($_ ($a, $bs,*)) => `(l($a,$bs,*))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Sum.inr] def unexpandInrTuple : Unexpander
  | `($_ ($a, $bs,*)) => `(r($a,$bs,*))
  | _ => throw ()

-- `tail(x)` inside a `⧺` keeps its brackets, which a plain application loses there.
syntax:max "tail(" term ")" : term

-- The projections' graphs are `π₁`/`π₂` only when the map IS the projection — the bare constant or
-- its eta-expansion `fun p => p.1` — read off the term, so `fun p => (f p).1` is not taken for one.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Freyd.Alg.RelSet.graph] def delabGraphProj : Delab := do
  let e ← getExpr
  unless e.getAppNumArgs == 3 do failure
  let i ← match e.appArg!.eta with
    | .lam _ _ (.proj ``Prod i (.bvar 0)) _ => pure i
    | g => match g.getAppFn.constName?, g.getAppNumArgs with
      | some ``Prod.fst, 2 => pure 0
      | some ``Prod.snd, 2 => pure 1
      | _, _ => failure
  `($(mkIdent (if i == 0 then `π₁ else `π₂)))

open Lean PrettyPrinter in
/-- A map's GRAPH is written by the map's own name — the note's `edit`, `cons`, `nil` are all
    `graph f` — and the two projections have names of their own, B&dM's `π₁`/`π₂`. -/
@[app_unexpander RelSet.graph] def unexpandGraph : Unexpander
  -- Only a map with a NAME: `graph (fun _ => 0)` keeps `AOP.A6_1_RelSet`'s own `⊸ 0`, which this
  -- clause would otherwise shadow with the lambda.
  | `($_ $f:ident) => `($f)
  | _ => throw ()

-- A RELATION NAMED AFTER THE MAP IT IS THE GRAPH OF drops the `R` the Lean name needs to tell the
-- two apart: the note's region has only the arrow, and `consR`/`concatR` already print that way.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.includeR] def unexpandIncludeR : Unexpander
  | _ => `($(mkIdent `«include»))

-- AN ARITHMETIC RELATION IS WRITTEN BY ITS OWN OPERATOR, the way the note writes it: `+` for the
-- addition's graph, `≤` for the ordering, so `est(leRel)` reads `est(≤)`.  The `Rel` the Lean name
-- carries tells the relation from the function and is no part of what the note spells.
open Lean PrettyPrinter in
@[app_unexpander RelSet.plusRel] def unexpandPlusRel : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "+")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.leRel] def unexpandLeRel : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≤")))

-- THE INCLUSION ORDER ON A POWER OBJECT IS WRITTEN BY ITS OWN SYMBOL, for the reason `≤` is: the
-- note's `⊆ ≜ ∈\∈` and its converse `⊇ ≜ ∋/∋`, never the Lean names that tell the two apart.
open Lean PrettyPrinter in
@[app_unexpander subset] def unexpandSubset : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "⊆")))
open Lean PrettyPrinter in
@[app_unexpander supset] def unexpandSupset : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "⊇")))

-- THE SECTION'S OWN ORDERING IS THE NOTE'S BEAD `R`.  Which cost function it ranks by — the volume,
-- the line width, the due dates — is the section's context and not part of the name, exactly as
-- `AOP.A9_3_Bracket.R`'s own unexpander already has it.  One per constant: the attribute keys on one.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.R] def unexpandEditR : Unexpander | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.R] def unexpandTardyR : Unexpander | _ => `($(mkIdent `R))
-- §10.3's arrows drop the job quantities `ct dt wt` as `R` does; `costR`/`penaltyR`/`bmaxR` only
-- tell the arrow from the Int function of the same name.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.costR] def unexpandTardyCostR : Unexpander | _ => `($(mkIdent `cost))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.penaltyR] def unexpandTardyPenaltyR : Unexpander
  | _ => `($(mkIdent `penalty))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.bmaxR] def unexpandTardyBmaxR : Unexpander | _ => `($(mkIdent `bmax))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.g] def unexpandTardyG : Unexpander | _ => `($(mkIdent `g))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.m] def unexpandTardyM : Unexpander | _ => `($(mkIdent `m))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.k] def unexpandTardyK : Unexpander | _ => `($(mkIdent `k))
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
-- The section's own integer ordering is written by its operator, as `leRel` is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.leq] def unexpandPartyLeq : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≤")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.R] def unexpandTourR : Unexpander | _ => `($(mkIdent `R))
-- The note's tour `Q` already carries the `head2` conjunct; Lean's `Q` without it is never drawn.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.Qc] def unexpandTourQc : Unexpander | _ => `($(mkIdent `Q))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.droplFn] def unexpandDroplFn : Unexpander | _ => `($(mkIdent `dropl))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.droprFn] def unexpandDroprFn : Unexpander | _ => `($(mkIdent `dropr))
-- §8.4–8.6 under the book's names (B&dM pp.205–215).  The cost function (`tc`, `len`) is the
-- section's context and is dropped, as `R` drops it; `w` and the list stay, as the book writes them.
-- `suffixP` is the book's `suffix`, read pointwise.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.suffixP] def unexpandSuffixP : Unexpander
  | `($_ $x $y) => `($(mkIdent `suffix) $x $y)
  | _ => `($(mkIdent `suffix))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.head] def unexpandTourHd : Unexpander
  | `($_ $x) => `($(mkIdent `head) $x)
  | _ => `($(mkIdent `head))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.next] def unexpandTourNxt : Unexpander
  | `($_ $x) => `($(mkIdent `next) $x)
  | _ => `($(mkIdent `next))
open Lean PrettyPrinter in
-- B&dM name no function for "the head replaced": `dropl(a,([b]⧺x,y))=([a]⧺x,…)` writes it as the
-- new head before the old tail, so the note does too.
@[app_unexpander RelSet.Tour.replaceHead] def unexpandTourReplaceHead : Unexpander
  | `($_ $a $x) => do pure (.node .none ``noteCat #[← `([$a]), mkAtom "⧺", ← `(tail($x))])
  | `($_ $a) => do pure (.node .none ``noteCat #[← `([$a]), mkAtom "⧺", ← `(tail(·))])
  | _ => throw ()
-- §10.2's `expand(xs,a)` (B&dM p.246); tab size and the three characters are the section's context.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.expandFn] def unexpandDetabExpandFn : Unexpander
  | `($_ $_ $_ $_ $_ $x $a) => `($(mkIdent `expand) $x $a)
  | `($_ $_ $_ $_ $_ $x) => `($(mkIdent `expand) $x)
  | _ => `($(mkIdent `expand))
-- `k`'s second arm as B&dM p.256 write it, in diagram order; costs and due dates are context.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.kStep] def unexpandTardyKStep : Unexpander
  | `($_ $_ $_ $_ $p) => `($(mkIdent (Name.mkSimple "assocr (𝟙×((bagify°×𝟙) penalty)) bmax")) $p)
  | _ => `($(mkIdent (Name.mkSimple "assocr (𝟙×((bagify°×𝟙) penalty)) bmax")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.outcost] def unexpandTourOutcost : Unexpander
  | `($_ $_ $x) => `($(mkIdent `outcost) $x)
  | _ => `($(mkIdent `outcost))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.incost] def unexpandTourIncost : Unexpander
  | `($_ $_ $x) => `($(mkIdent `incost) $x)
  | _ => `($(mkIdent `incost))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.cost] def unexpandTourCost : Unexpander
  | `($_ $_ $t) => `($(mkIdent `cost) $t)
  | _ => `($(mkIdent `cost))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.widthFn] def unexpandParaWidth : Unexpander
  | `($_ $_ $x) => `($(mkIdent `width) $x)
  | _ => `($(mkIdent `width))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.wasteFn] def unexpandParaWaste : Unexpander
  | `($_ $_ $w $p) => `($(mkIdent `waste) $w $p)
  | `($_ $_ $w) => `($(mkIdent `waste) $w)
  | _ => `($(mkIdent `waste))
-- The predicate under the coreflexive `fits(w)` is written `fits`, as `secureP` is `secure`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.allFitP] def unexpandParaAllFitP : Unexpander
  | `($_ $_ $w $p) => `($(mkIdent `fits) $w $p)
  | `($_ $_ $w) => `($(mkIdent `fits) $w)
  | _ => `($(mkIdent `fits))
-- B&dM's `y subseq x` (p.123) is the predicate under the relation `subseq`, as `allFitP` is `fits`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.subseqP] def unexpandSubseqP : Unexpander
  | `($_ $y $x) => `($(mkIdent `subseq) $y $x)
  | `($_ $y) => `($(mkIdent `subseq) $y)
  | _ => `($(mkIdent `subseq))
-- The list map on a function is B&dM's `list f` (p.205: `value = sum·list val`), the relator's letter.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.cmap] def unexpandCmap : Unexpander
  | `($_ $f $x) => `($(mkIdent `list) $f $x)
  | `($_ $f) => `($(mkIdent `list) $f)
  | _ => `($(mkIdent `list))
-- "`x` is secure" is the note's word for the predicate under the coreflexive `secure`; `amount` and
-- `N` are the section's context, dropped as `R` drops its own.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Van.secureP] def unexpandSecureP : Unexpander
  | `($_ $_ $_ $x) => `($(mkIdent `secure) $x)
  | _ => `($(mkIdent `secure))

-- `lenLE` is the same thing under its definition's name: the length preorder IS §13.4.2's ordering,
-- and the note draws `R` on that box and `est(R°)` on the greedy step.
open Lean PrettyPrinter in
@[app_unexpander RelSet.GCTakeWhile.R] def unexpandLenLE : Unexpander | _ => `($(mkIdent `R))

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
-- §9.3's fold components and `g` drop the leaf map, split cost and combine cost, as `R` does.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.costFn] def unexpandBracketCostFn : Unexpander
  | _ => `($(mkIdent `cost))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.sizeFn] def unexpandBracketSizeFn : Unexpander
  | _ => `($(mkIdent `size))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.szFn] def unexpandBracketSzFn : Unexpander
  | _ => `($(mkIdent `sz))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.zeroFn] def unexpandBracketZeroFn : Unexpander
  | _ => `($(mkIdent `zero))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.opbFn] def unexpandBracketOpbFn : Unexpander
  | _ => `($(mkIdent `opb))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.gR] def unexpandBracketGR : Unexpander
  | _ => `($(mkIdent `g))
-- The label summand of `F X = A + X²` is the label type itself; `≤` on `Int` is its operator.
open Lean PrettyPrinter in
@[app_unexpander RelSet.TT.dA] def unexpandTTdA : Unexpander
  | `($_ $a) => `($a)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.leq] def unexpandListRelLeq : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≤")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.geq] def unexpandListRelGeq : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≥")))
open Lean PrettyPrinter in
@[app_unexpander mem] def unexpandMem : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "∈")))

-- A CONVERSE WITH A NAME OF ITS OWN (CLAUDE.md): each theorem `Q = P°` names `P°` as `Q` and `Q°`
-- as `P` (`diag/tool/Label.lean`, `namedRecip?`), both spelled by their unexpanders above.
attribute [diag_opposite] mem_eq_recip_eps subset_eq_recip_supset RelSet.ListRel.geq_eq_recip_leq

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

-- `Real`'s carrier is a quotient, so a circuit opening `Digit×Real` reaches `Quotient realSetoid`:
-- the setoid argument, read off the `Expr`, says it is the TeX problem's `Real`.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Quotient]
def delabTexRealCarrier : Delab := do
  unless (← getExpr).appArg!.isConstOf ``Freyd.Alg.RelSet.Tex.realSetoid do failure
  `($(mkIdent `Real))

-- `Interval`'s carrier is the subtype cut out by (10.9), so a circuit opening `Digit×Interval`
-- reaches `{p // Legal p}`: the predicate, read off the `Expr`, says it is the TeX `Interval`.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Subtype]
def delabTexIntervalCarrier : Delab := do
  unless (← getExpr).appArg!.eta.isConstOf ``Freyd.Alg.RelSet.Tex.Legal do failure
  `($(mkIdent `Interval))

-- `[zero, ⊸ zero ∪ plus]`'s two leaves are named in the note, so the box carries the note's word
-- and not the namespace the Lean constant happens to live in.

open Lean PrettyPrinter in
/-- The power relator's lane is `P`: on arrows it is `powerRel`, a relation, where `E`'s is
    `existsImage`, a function, so a `P` lane around `R` reads `P(R)` and an `E` lane `E(R)`.  Its
    OBJECTS print `P A` (`unexpandPowerObj`); a lane prints the letter of the ARROW it gives. -/
@[app_unexpander powerRelator] def unexpandPowerRelator : Unexpander
  | _ => `($(mkIdent `P))

open Lean PrettyPrinter in
/-- The existential-image functor's lane is `E`: it has the power relator's object action but
    acts on arrows by `existsImage`, so the two lanes print different letters. -/
@[app_unexpander existsImageFunctor] def unexpandExistsImageFunctor : Unexpander
  | _ => `($(mkIdent `E))

open Lean PrettyPrinter in
/-- The subset `R` reaches from `s` is B&dM's `(ER)x` (p.32): the existential image `E(R)` at `s`. -/
@[app_unexpander RelSet.img] def unexpandImg : Unexpander
  | `($_ $R $s) => `(($(mkIdent `E) $R) $s)
  | _ => throw ()

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
/-- The hypothesis of B&dM p.158 in the book's word (p.147): `R` is inductive. -/
@[app_unexpander Inductive] def unexpandInductive : Unexpander
  | `($_ $r) => `($(mkIdent `inductive) $r)
  | _ => throw ()

/-- The book's closure `R*` (6.7), postfix like `°`. -/
postfix:max "*" => star

open Lean PrettyPrinter in
/-- `theta R P Q` is the book's `θ(P,Q)` (6.9): `R` is the section's fixed relation, which the
    region already carries, so the label writes only the two arguments that change. -/
@[app_unexpander theta] def unexpandTheta : Unexpander
  | `($_ $_ $p $q) => `($(mkIdent `θ) $p $q)
  | _ => throw ()

open Lean PrettyPrinter in
/-- The greatest fixed point, `(νX : α°F(X)R)`, spelled as its least twin above. -/
@[app_unexpander nu] def unexpandNu : Unexpander
  | `($_ fun $x:ident => $b) => `(($(mkIdent (Name.mkSimple ("ν" ++ x.getId.toString))) : $b))
  | _ => throw ()

-- B&dM §6.1's datatype `Decimal = wrap Digit⁺ | snoc (Decimal, Digit)`: its constructor map is the
-- book's `α`, its base relator the section's `F`, its objects the book's `Digit⁺`, `Digit`, `Decimal`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Digits.con] def unexpandDigitsCon : Unexpander
  | _ => `($(mkIdent `α))

open Lean PrettyPrinter in
@[app_unexpander RelSet.Digits.cataR] def unexpandDigitsCata : Unexpander
  | `($_ $φ) => `(⦇$φ⦈)
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander RelSet.Digits.timesDigit] def unexpandDigitsTimes : Unexpander
  | `($_ $args*) => `($(mkIdent (Name.mkSimple "−×Digit")) $args*)
  | _ => `($(mkIdent (Name.mkSimple "−×Digit")))

open Lean PrettyPrinter in
@[app_unexpander RelSet.Digits.plusDigitP] def unexpandDigitsPlus : Unexpander
  | `($_ $args*) => `($(mkIdent (Name.mkSimple "Digit⁺+−")) $args*)
  | _ => `($(mkIdent (Name.mkSimple "Digit⁺+−")))

-- B&dM §6.4's vocabulary: `Bin = listl Bit`, `convert = ⦇[zero,shift]⦈`, the specifications `exp(a)`
-- and `mod(b)`, and the two algebras' `op`, each applied to its parameter as the book writes it.
open Lean PrettyPrinter in
/-- `IsFHom f g h` is the note's F-homomorphism statement `h : f⟶g` — an arrow of `Alg(F)` from the
    algebra `f` to the algebra `g`, which a type ascription already spells. -/
@[app_unexpander IsFHom] def unexpandIsFHom : Unexpander
  | `($_ $f $g $h) => `(($h : $f ⟶ $g))
  | _ => throw ()

-- B&dM pp.46–47 write `Nat`'s functor `F`, its constructors `zero`, `succ`, and the unit `1`.
open Lean PrettyPrinter in
@[app_unexpander natF] def unexpandNatF : Unexpander | _ => `($(mkIdent `F))
open Lean PrettyPrinter in
@[app_unexpander zero] def unexpandNatZero : Unexpander | _ => `($(mkIdent `zero))
open Lean PrettyPrinter in
@[app_unexpander succ] def unexpandNatSucc : Unexpander | _ => `($(mkIdent `succ))
open Lean PrettyPrinter in
@[app_unexpander UnitaryAllegory.unit_obj] def unexpandUnitObj : Unexpander | _ => `(1)

open Lean PrettyPrinter in
/-- `H≜⦇T⦈°⦇h⦈` is the note's ONE bead `H`: which coalgebra and algebra it is built from is what
    the definition above the table states, not what the wire is labelled with. -/
-- Applied to points, `H` keeps them: `H([a,b,c],ys)` is a claim about one input, not about `H`.
@[app_unexpander H] def unexpandH : Unexpander
  | `($_ $_ $_ $x $args*) => `($(mkIdent `H) $x $args*)
  | _ => `($(mkIdent `H))

open Lean PrettyPrinter in
-- `M≜Λ(H) est(R)` is the note's one bead `M`, for `H`'s reason.
@[app_unexpander Freyd.Alg.M] def unexpandM : Unexpander
  | `($_ $_ $_ $_ $x $args*) => `($(mkIdent `M) $x $args*)
  | _ => `($(mkIdent `M))

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
@[app_unexpander RelSet.MSS.k] def unexpandKalg : Unexpander | _ => `($(mkIdent `k))


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
@[app_unexpander union] def unexpandBigUnion : Unexpander | _ => `($(mkIdent `union))

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
/-- THE POWER OBJECT'S CARRIER IS THE POWER OBJECT.  `pow B` is `⟨Sub B⟩`, `Sub B = B → Prop`, so a
    TYPE that is a non-dependent pi into `Prop` is that object's carrier and prints as `pow` does,
    `P A` — `list⁺(V → Prop)` is `list⁺(PV)`.  Read off the pi's codomain, not a printed string. -/
@[delab forallE] def delabPowCarrier : Delab := do
  let .forallE _ _ b _ ← getExpr | failure
  guard (b.isProp && !b.hasLooseBVars)
  let a ← withBindingDomain delab
  `($(mkIdent `P) $a)

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
-- `Salg` says nothing; `diag_unfold` is `diag/tool/Tags.lean`'s, as for `tour` above.
attribute [diag_unfold] RelSet.Knapsack.Salg RelSet.Paragraph.Salg
-- The prefix algebra is drawn written out, `⦇[nil,⊸ nil ∪ cons]⦈` (13.3.3b), never as its name.
attribute [diag_unfold] RelSet.ListRel.prefAlg
-- The take-while section's algebras the same way: the note draws what each arm DOES — `prefix`,
-- `cons`, `p`, `(π₁p→cons,⊸ nil)` — and `prefConsAlg` and `consScalarAlg` are Lean names for those
-- arms, so they are opened; a step (`twStep`, `fStep`) is read as the guard its `if` is.
attribute [diag_unfold] RelSet.GCTakeWhile.prefConsAlg
  RelSet.CL.consScalarAlg
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
attribute [diag_unfold] RelSet.SL.nil
-- The bag's algebra is the coproduct the note writes out, `[nil,snag]`, never its Lean name: the
-- arms are read off the `match` by `diag/tool/Label.lean` once the name is opened, and `arm₂` of it
-- is then the arm alone.
attribute [diag_unfold] RelSet.Tardy.bagAlg
-- `Λ S` is drawn as the unit bead and `E(S)` (13.3.2a, 13.4.4a): the spine is rewritten by the
-- transpose's factorisation, and `Λ 𝟙` folds back to the unit alone through `existsImage_id` and
-- the identity law.
attribute [diag_rewrite] Λ_eq_singleton_existsImage existsImage_id Cat.comp_id
-- `∈\Z` is an APPLICATION of `∈\−`, which is no relator and so no wire; opened to the composite
-- `⊆ Λ(Z°)°` it is beads on the lanes like `Λ` is, `Z` then drawn by the transpose's own rule.
attribute [diag_rewrite] mem_leftDiv_eq
-- An ARM is written by its own name (`snoc`, `snag`), never as the algebra restricted: `arm₂` of a
-- map is a map, and `diag/tool/Label.lean` then reads the name off the restricted function.
attribute [diag_rewrite] RelSet.SL.arm₂_graph-- And the relator SLIDES INTO THE BRACKET: `F(X)[T,U]` is the note's `[T,(X×𝟙)U]`, one tape whose
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
@[app_unexpander RelSet.Edit.Op] def unexpandEditOp : Unexpander
  -- B&dM p.225 writes the type `Op` alone: the alphabet is the section's one `Char`.
  | _ => `($(mkIdent `Op))
-- The tip-tree section's own bifunctor is the note's `F`, the letter every `F(R,S)` beside the
-- picture already uses; `RelSet.RT.F` above is the rose tree's, spelled the same for the same
-- reason.
-- A SECTION'S STEP ALGEBRA PRINTS `S`, as `Party.S` does: it is drawn opened (`diag_unfold` below),
-- so the letter shows only where a label names it whole.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Paragraph.Salg] def unexpandParagraphSalg : Unexpander
  | _ => `($(mkIdent `S))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Knapsack.Salg] def unexpandKnapsackSalg : Unexpander
  | _ => `($(mkIdent `S))
-- The note's `cp(F)` (B&dM §5.6) is `cpMap F A`: the relator is its argument and the object `A` is
-- the wire under the bead, so only `F` is printed (`$args*` here matched nothing and wrote bare `cp`).
open Lean PrettyPrinter in
@[app_unexpander cpMap] def unexpandCpMap : Unexpander
  | `($_ $F $_) => `($(mkIdent `cp) $F)
  | `($_ $F) => `($(mkIdent `cp) $F)
  | _ => `($(mkIdent `cp))
-- THE NAMES THE NOTE NEVER WRITES ITSELF: the suffix is Lean's disambiguator (`Fn`, `Rel`, `Alg`,
-- `Relator`, as `editFn` is `edit` above). The author's decision (2026-09-22): a bundled relator
-- prints as the type it bundles (`op`, `Journey`).  Algebras kept the Lean name until 2026-10-04,
-- when the rule became that Lean follows the note: an algebra prints as the junction the note writes.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.op] def unexpandEditOpRelator : Unexpander
  | `($_ $args*) => `($(mkIdent `op) $args*)
  | _ => `($(mkIdent `op))
open Lean PrettyPrinter in
-- The cons-list `setify` is the note's `setify` (`setifyCL_eq_setify`): `CL` says which file.
@[app_unexpander RelSet.CL.setifyCL] def unexpandSetifyCL : Unexpander
  | `($_ $args*) => `($(mkIdent `setify) $args*)
  | _ => `($(mkIdent `setify))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tour.journeyRelator] def unexpandTourJourney : Unexpander
  | `($_ $args*) => `($(mkIdent `Journey) $args*)
  | _ => `($(mkIdent `Journey))
open Lean PrettyPrinter in
-- `sortRel L setify ordered ≼` is the book's `sort(≼)`: `L`, `setify` and `ordered` are what its
-- definition `setify° ordered(≼)` is made of, and the note writes only the order it sorts by.
@[app_unexpander sortRel] def unexpandSortRel : Unexpander
  | `($_ $_ $_ $_ $o) => `($(mkIdent `sort) $o)
  | _ => `($(mkIdent `sortRel))
-- B&dM p.196 names the cost order `R` and p.197 its refinement `Q`; `path` is only Lean's prefix,
-- and the note's `path-defn` lines print these from the defs' values.
open Lean PrettyPrinter in
@[app_unexpander pathR] def unexpandPathR : Unexpander
  | `($_ $args*) => `($(mkIdent `R) $args*)
  | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander pathQ] def unexpandPathQ : Unexpander
  | `($_ $args*) => `($(mkIdent `Q) $args*)
  | _ => `($(mkIdent `Q))
-- B&dM p.196 writes `cost` and `head`; the weight `wt` is the section's one parameter and no
-- argument the note writes.
open Lean PrettyPrinter in
@[app_unexpander costOf] def unexpandCostOf : Unexpander
  | `($_ $_ $args*) => `($(mkIdent `cost) $args*)
  | _ => `($(mkIdent `cost))
open Lean PrettyPrinter in
@[app_unexpander headOf] def unexpandHeadOf : Unexpander
  | `($_ $args*) => `($(mkIdent `head) $args*)
  | _ => `($(mkIdent `head))
open Lean PrettyPrinter in
@[app_unexpander head] def unexpandHeadRel : Unexpander
  | _ => `($(mkIdent `head))
-- B&dM p.196 writes `minpath`; the weight `wt` is the section's one parameter, as for `cost`.
open Lean PrettyPrinter in
@[app_unexpander minpath] def unexpandMinpath : Unexpander
  | `($_ $_ $args*) => `($(mkIdent `minpath) $args*)
  | _ => `($(mkIdent `minpath))
-- B&dM p.198 writes `step`; the `path` prefix only keeps Lean's name apart from `Edit`'s step.
open Lean PrettyPrinter in
@[app_unexpander pathStep] def unexpandPathStep : Unexpander
  | `($_ $args*) => `($(mkIdent `step) $args*)
  | _ => `($(mkIdent `step))
-- B&dM p.196 writes `F(A,X)=A+A×X` for the network's bifunctor.
open Lean PrettyPrinter in
@[app_unexpander pathF] def unexpandPathF : Unexpander
  | _ => `($(mkIdent `F))
-- B&dM p.126 writes `cpr`/`cpl` for the cross product at `A×−`/`−×A`; the objects are the wires.
open Lean PrettyPrinter in
@[app_unexpander cprMap] def unexpandCprMap : Unexpander
  | _ => `($(mkIdent `cpr))
open Lean PrettyPrinter in
@[app_unexpander cplMap] def unexpandCplMap : Unexpander
  | _ => `($(mkIdent `cpl))
-- B&dM p.201's `listcp(F)`; the functor is the wire's, as for `cp`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.listcp] def unexpandListcp : Unexpander
  | _ => `($(mkIdent `listcp))
-- B&dM's connected order; the full name is only Lean's way past §1.72's object-level `Connected`.
open Lean PrettyPrinter in
@[app_unexpander _root_.Freyd.Alg.connected] def unexpandConnected : Unexpander
  | `($_ $R) => `($(mkIdent `connected) $R)
  | _ => throw ()
-- The same connectedness, on a pointwise relation `A → A → Prop` (§6.6's sorts).
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.connected] def unexpandConnectedP : Unexpander
  | `($_ $R) => `($(mkIdent `connected) $R)
  | _ => throw ()
-- B&dM p.196's `zero`, `consw` and `cost`; the weight `wt` is the section's parameter, as for `costOf`.
open Lean PrettyPrinter in
@[app_unexpander zeroCost] def unexpandZeroCost : Unexpander
  | _ => `($(mkIdent `zero))
open Lean PrettyPrinter in
@[app_unexpander conswFn] def unexpandConswFn : Unexpander
  | `($_ $_ $args*) => `($(mkIdent `consw) $args*)
  | _ => `($(mkIdent `consw))
open Lean PrettyPrinter in
@[app_unexpander consw] def unexpandConsw : Unexpander
  | `($_ $_ $args*) => `($(mkIdent `consw) $args*)
  | _ => `($(mkIdent `consw))
open Lean PrettyPrinter in
@[app_unexpander pathCost] def unexpandPathCost : Unexpander
  | `($_ $_ $args*) => `($(mkIdent `cost) $args*)
  | _ => `($(mkIdent `cost))
-- `S ≜ F(𝟙,∋)α`, the letter of the 8.2d side condition `R∩(S°S)⊑Q` only.
open Lean PrettyPrinter in
@[app_unexpander algSplit] def unexpandAlgSplit : Unexpander
  | _ => `($(mkIdent `S))
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
-- The edit section's thinning preorder joins `Code`'s, `Detab`'s and `Tardy`'s above: the note's
-- `Q`, stated over the section's own data.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.Q] def unexpandEditQ : Unexpander | _ => `($(mkIdent `Q))
-- The section's GRAPH OF THE SNOC LIST'S EMPTY CASE is the note's `nil`; the `R` is Lean's, as
-- `detabR`'s is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.SL.nil] def unexpandSLNilR : Unexpander
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
@[app_unexpander RelSet.Tex.bang] def unexpandTexBang : Unexpander | _ => `($(mkIdent (Name.mkSimple "!")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.V] def unexpandEditV : Unexpander | _ => `($(mkIdent `V))
-- B&dM p.263 on points: `Real`'s order, constants and `10a−d` wear the book's arithmetic, a
-- representative `(p,0)` is `p/w`, and the rational `f` and the program's `f` share the book's letter.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.rlt] def unexpandTexRlt : Unexpander
  | `($_ $a $b) => `($a < $b)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.zeroR] def unexpandTexZeroR : Unexpander | _ => `(0)
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.oneR] def unexpandTexOneR : Unexpander | _ => `(1)
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.unshift] def unexpandTexUnshift : Unexpander
  | `($_ $d $a) => pure (.node .none ``noteSub #[mulStx (Syntax.mkNumLit "10") a, mkAtom "−", d])
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.mkR] def unexpandTexMkR : Unexpander
  | `($_ ($p, 0)) => pure (.node .none ``noteDiv #[p, mkAtom "/", mkIdent `w])
  | `($_ $x) => pure x
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.IsDigit] def unexpandTexIsDigit : Unexpander
  | `($_ $d $b) =>
    `($d = $(⟨.node .none ``noteFloor #[mkAtom "⌊", mulStx (Syntax.mkNumLit "10") b, mkAtom "⌋"]⟩))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.fR] def unexpandTexFR : Unexpander
  | `($_ $args*) => `($(mkIdent `f) $args*)
  | _ => `($(mkIdent `f))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.Prog.f] def unexpandTexProgF : Unexpander
  | `($_ ($p, $q)) => `($(mkIdent `f) $p $q)
  | _ => throw ()
-- A SUBTYPE'S POINT IS ITS VALUE: `⟨(a,b),h⟩` is the interval `(a,b)`, the proof `h` a statement
-- about it that no formula of the note writes.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Subtype.mk] def delabSubtypeMk : Delab := do
  guard ((← getExpr).getAppNumArgs == 4)
  withNaryArg 2 delab
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.Prog.dig] def unexpandTexProgDig : Unexpander
  | `($_ $d $_) => `($d)
  | _ => throw ()
open Lean PrettyPrinter Delaborator SubExpr in
/-- An interval `(a,b)` is the pair it is, not a structure instance with field names. -/
@[delab app.Freyd.Alg.RelSet.Tex.Iv.mk] def delabTexIvMk : Delab := do
  guard ((← getExpr).getAppNumArgs == 2)
  let a ← withNaryArg 0 delab
  let b ← withNaryArg 1 delab
  pure ⟨.node .none ``noteTuple #[mkAtom "(", a, mkAtom ",", b, mkAtom ")"]⟩
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
-- THE IDENTITY FUNCTION IS THE NOTE'S `𝟙`: in §1.241's category of types the identity arrow is core's
-- `id`, the factor `Prod.map id f` keeps unchanged.  Applied to a point it is no arrow, so no rule.
open Lean PrettyPrinter in
@[app_unexpander id] def unexpandCoreId : Unexpander
  | `($_:ident) => `($(mkIdent (Name.mkSimple "𝟙")))
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
  -- Element type first: a catch-all clause matched the bare head and the `A` was lost.
  | `($_ $A) => `($(mkIdent `tree) $A)
  | `($_:ident) => `($(mkIdent `tree))
  | _ => throw ()
-- The non-zero digits `{d // d ≠ 0}` are B&dM's `Digit⁺`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Digits.DigitP] def unexpandDigitP : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "Digit⁺")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.cat] def unexpandListRelCatR : Unexpander
  | `($_ $args*) => `($(mkIdent `cat) $args*)
  | _ => `($(mkIdent `cat))
-- B&dM writes `partition = concat°` with `concat` restricted to non-empty segments; the restriction
-- is no second name.  Not `cat`: that is `catR`'s, the binary join, and `cat°` splits in two.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.concat] def unexpandListRelConcatNE : Unexpander
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
-- §9.3's tabulation: the list functions by the book's names, `row`/`col` without the `mct` they
-- are taken of, `mix`/`next` without the leaf map, split cost and combine cost, as `R` does.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.initFn] def unexpandBracketInitFn : Unexpander
  | _ => `($(mkIdent `init))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.tailFn] def unexpandBracketTailFn : Unexpander
  | _ => `($(mkIdent `tail))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.neInitsFn] def unexpandBracketInitsFn : Unexpander
  | _ => `($(mkIdent `inits))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.neTailsFn] def unexpandBracketTailsFn : Unexpander
  | _ => `($(mkIdent `tails))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.initsPFn] def unexpandBracketInitsPFn : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "inits⁺")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.tailsPFn] def unexpandBracketTailsPFn : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "tails⁺")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.zipFn] def unexpandBracketZipFn : Unexpander
  | _ => `($(mkIdent `zip))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.snocFn] def unexpandBracketSnocFn : Unexpander
  | _ => `($(mkIdent `snoc))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.row] def unexpandBracketRow : Unexpander
  | _ => `($(mkIdent `row))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.col] def unexpandBracketCol : Unexpander
  | _ => `($(mkIdent `col))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.mct] def unexpandBracketMct : Unexpander
  | _ => `($(mkIdent `mct))
-- B&dM's `minlist(R)`, the function folded from `bmin`, in `CL.minlist`'s own spelling.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.minlistFn] def unexpandBracketMinlistFn : Unexpander
  | `($_ $q) => `(minlist($q))
  | _ => throw ()
-- The constructor `wrap` as a relation is `wrap`, as `consR` is `cons`; a delaborator, since
-- `wrapR` takes only implicit arguments and prints as a bare constant no `app_unexpander` fires on.
-- Out of the EMPTY leaf `𝟏` it is the list's `nil`, the name `Label.lean` gives every map out of a
-- source with no strands; `isDefEq`, as `delabDL` above tests the same leaf.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Freyd.Alg.RelSet.CL.wrapR, delab const.Freyd.Alg.RelSet.CL.wrapR]
def delabCLWrapR : Delab := do
  let args := (← getExpr).getAppArgs
  if let some l := args[0]? then
    if ← Meta.isDefEq l (mkConst ``Unit) then return ← `($(mkIdent `nil))
  `($(mkIdent `wrap))
-- The book's `tic≜cons inits tail` (p. 235), implicit-only like `wrapR`.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.RelSet.Bracket.tic, delab const.Freyd.Alg.RelSet.Bracket.tic]
def delabBracketTic : Delab := `($(mkIdent `tic))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.mix] def unexpandBracketMix : Unexpander
  | _ => `($(mkIdent `mix))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.next] def unexpandBracketNext : Unexpander
  | _ => `($(mkIdent `next))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.array] def unexpandBracketArray : Unexpander
  | _ => `($(mkIdent `array))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.process] def unexpandBracketProcess : Unexpander
  | _ => `($(mkIdent `process))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.addcol] def unexpandBracketAddcol : Unexpander
  | _ => `($(mkIdent `addcol))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.step] def unexpandBracketStep : Unexpander
  | _ => `($(mkIdent `step))
-- Our own names for §9.3's long composites (not the book's): `graft`, `tops`, `rests`, `newrows`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.graft] def unexpandBracketGraft : Unexpander
  | _ => `($(mkIdent `graft))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.tops] def unexpandBracketTops : Unexpander
  | _ => `($(mkIdent `tops))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.rests] def unexpandBracketRests : Unexpander
  | _ => `($(mkIdent `rests))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.newrows] def unexpandBracketNewrows : Unexpander
  | _ => `($(mkIdent `newrows))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Bracket.listTailFn] def unexpandBracketListTailFn : Unexpander
  | _ => `($(mkIdent `tail))
-- `prefixS x y` is "`x` is a prefix of `y`", the note's `prefix°` (`Q≜F(⊤+⊤,prefix°)`).
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.prefixS] def unexpandCodePrefixS : Unexpander
  | `($_ $args*) => `($(mkIdent (Name.mkSimple "prefix°")) $args*)
  | _ => `($(mkIdent (Name.mkSimple "prefix°")))
-- Its proper part is the book's `init⁺` (p. 226).
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.properPrefixS] def unexpandCodeProperPrefixS : Unexpander
  | `($_ $args*) => `($(mkIdent (Name.mkSimple "init⁺")) $args*)
  | _ => `($(mkIdent (Name.mkSimple "init⁺")))
-- A relation given by cases holds outright on a case as `true`, the Boolean spelling beside it.
open Lean PrettyPrinter in
@[app_unexpander True] def unexpandTrue : Unexpander
  | `($_:ident) => `($(mkIdent `true))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander False] def unexpandFalse : Unexpander
  | `($_:ident) => `($(mkIdent `false))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Code.sappend] def unexpandCodeSappend : Unexpander
  | `($_ $args*) => `($(mkIdent `cat) $args*)
  | _ => `($(mkIdent `cat))
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.cons] def unexpandConsAtUnit : Unexpander
  | _ => `($(mkIdent `cons))
-- The edit operations are the note's `cpy`/`del`/`ins`; `inlistP xs q` is membership `q∈xs`.
open Lean PrettyPrinter in
-- The arm of a preorder `Q` is the note's `Q₂` (chapter 10 writes `est(Qᵢ)`): the preorder's own
-- name, subscripted, never `armQ₂` — the Lean name only says which arm the declaration takes.
@[app_unexpander RelSet.SL.armQ₂] def unexpandSLArmQ2 : Unexpander
  | `($_ $q:ident) =>
    `($(mkIdent (Name.mkSimple (q.getId.eraseMacroScopes.toString (escape := false) ++ "₂"))))
  | _ => `($(mkIdent `Q₂))
-- The edit algebra's arms are declarations of their own (`baseFn`, `stepFn`), so a term at one arm
-- is spelled by that arm and no rule here guesses it.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.stepFn] def unexpandEditStepFn : Unexpander | _ => `($(mkIdent `step))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Edit.baseFn] def unexpandEditBaseFn : Unexpander | _ => `($(mkIdent `base))
-- A projection applied to a point is the note's `π₁`/`π₂` applied to it: `V(π₂(p),π₂(q))`.
open Lean PrettyPrinter in
@[app_unexpander Prod.fst] def unexpandProdFst : Unexpander
  | `($_ $x) => `($(mkIdent `π₁) $x)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Prod.snd] def unexpandProdSnd : Unexpander
  | `($_ $x) => `($(mkIdent `π₂) $x)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.inlistP] def unexpandInlistP : Unexpander
  | `($_ $xs $q) => `($q ∈ $xs)
  | _ => throw ()
-- The party section's two branches are the note's `include` and `exclude`; `includeR` above is the
-- same arrow taken as a relation.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.intervalFn] def unexpandTexIntervalFn : Unexpander
  | `($_ $args*) => `($(mkIdent `interval) $args*)
  | _ => `($(mkIdent `interval))
-- THE IDENTITY LANE IS THE NOTE'S `𝟙`, the same letter the identity arrow wears; which category
-- it is the identity of is the region the lane runs in.
open Lean PrettyPrinter in
@[app_unexpander Relator.idRelator] def unexpandIdRelator : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "𝟙")))
-- A COMPOSITE LANE IS JUXTAPOSITION in diagram order: `Relator.comp F G` is first `F` then `G`.
open Lean PrettyPrinter in
@[app_unexpander Relator.comp] def unexpandRelatorComp : Unexpander
  | `($_ $F $G) => `($F $G)
  | _ => throw ()
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
-- THE SUM RELATOR ON A GIVEN COPRODUCT FAMILY IS THE NOTE'S `G+H`, as `Relator.sum` is.  A
-- delaborator: `G`, `H` are implicit, read off the coproduct family's type; the family is last.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Relator.sumOn] def delabRelatorSumOn : Delab := do
  let n := (← SubExpr.getExpr).getAppNumArgs
  guard (n ≥ 4)
  let g ← SubExpr.withNaryArg (n - 4) delab
  let h ← SubExpr.withNaryArg (n - 3) delab
  `($g + $h)
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
-- B&dM's own name for the booleans (§1.7, the answers of `p` in `filter`).
open Lean PrettyPrinter Delaborator in
@[delab app.Bool, delab const.Bool] def delabBoolName : Delab := `($(mkIdent `Bool))
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
-- B&dM p.148 writes `member(F)`; the bead's `F` and object are the wires it joins, so the label is bare.
open Lean PrettyPrinter in
@[app_unexpander LaxMembership.mem] def unexpandMember : Unexpander
  | `($_ $_ $_) => `($(mkIdent `member))
  | _ => throw ()
-- `Fin` KEEPS ITS ARGUMENT — `Fin n` is the object, where `Int` and `Char` are whole names; an
-- unexpander and not a delaborator, so the index the printer already wrote stands.

-- §6.6's sorting relations under the book's names: the preorder `R` is fixed for the whole
-- section, so `ordered` and `ok` are written without it (B&dM p.151).
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.ordered] def unexpandOrdered : Unexpander
  | `($_ $_) => `($(mkIdent `ordered))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.orderedP] def unexpandOrderedP : Unexpander
  | `($_ $_ $x) => `(orderedP $x)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Sort.ok] def unexpandOk : Unexpander
  | `($_ $_) => `($(mkIdent `ok))
  | _ => throw ()
-- §6.6 quicksort (B&dM pp.154-155): the tree fold's arrows under the book's names.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Sort.inordered] def unexpandInordered : Unexpander
  | `($_ $_) => `($(mkIdent `inordered))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Sort.check] def unexpandCheck : Unexpander
  | `($_ $_) => `($(mkIdent `check))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander RelSet.Sort.check'] def unexpandCheck' : Unexpander
  | `($_ $_) => `($(mkIdent `check'))
  | _ => throw ()
-- §6.6 `split` as a fold on non-empty lists (B&dM p.155).
open Lean PrettyPrinter in
@[app_unexpander RelSet.Sort.step] def unexpandStep : Unexpander
  | `($_ $_) => `($(mkIdent `step))
  | _ => throw ()
-- The Boolean test `leb` of a sort's comparison states its hypotheses with `true`/`false`.
open Lean PrettyPrinter in
@[app_unexpander Bool.true] def unexpandBoolTrue : Unexpander
  | `($_:ident) => `($(mkIdent `true))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Bool.false] def unexpandBoolFalse : Unexpander
  | `($_:ident) => `($(mkIdent `false))
  | _ => throw ()
-- A QUOTIENT IS WRITTEN BY ITS REPRESENTATIVES, as a coercion is by what it coerces: the class of `x`
-- is `x` — a bag is its list — and the label reads a lift as the function it lifts (`labelTreeCore`).
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Quotient.mk] def delabNoteQuotMk : Delab := do
  unless (← getExpr).getAppNumArgs == 3 do failure
  withNaryArg 2 delab
-- §10.2/§10.4 (B&dM pp.246, 258): a string's or a decimal's `length`, and the `prefix` order.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.length] def unexpandDetabSlen : Unexpander
  | `($_ $x) => `($(mkIdent `length) $x)
  | _ => `($(mkIdent `length))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.length] def unexpandTexLen : Unexpander
  | `($_ $x) => `($(mkIdent `length) $x)
  | _ => `($(mkIdent `length))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Detab.prefixS] def unexpandDetabPrefix : Unexpander
  | `($_ $x $y) => `($(mkIdent `prefix) $x $y)
  | _ => `($(mkIdent `prefix))
-- §10.3: `add`'s inductive statement is `add` itself, and the penalty of a bag is the book's
-- `(bagify°×𝟙) penalty`, the penalty of putting the job last after any ordering of the bag; both
-- drop the job quantities `ct dt wt`, as the section's arrows do.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.AddP] def unexpandTardyAddP : Unexpander
  | `($_ $x $j $w) => `($(mkIdent `add) ($x, $j) $w)
  | _ => `($(mkIdent `add))
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tardy.bagPenalty] def unexpandTardyBagPenalty : Unexpander
  | `($_ $_ $_ $_ $p) => `($(mkIdent (Name.mkSimple "(bagify°×𝟙) penalty")) $p)
  | _ => `($(mkIdent (Name.mkSimple "(bagify°×𝟙) penalty")))
-- B&dM p.258: `shift(d,r)=(d+r)/10`, the representative `shiftPre` computes; the class `mkR x` of
-- any other representative is `x`, as `Quotient.mk`'s is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.shiftPre] def unexpandTexShiftPre : Unexpander
  | `($_ $d $x) => do pure (.node .none ``noteDiv #[← `(($d + $x)), mkAtom "/", Syntax.mkNumLit "10"])
  | _ => throw ()
-- Ex 6.30 insertion sort (B&dM p.157).
open Lean PrettyPrinter in
@[app_unexpander RelSet.ISort.insertR] def unexpandInsertR : Unexpander
  | `($_ $_) => `($(mkIdent `insert))
  | _ => throw ()

-- B&dM's conditional `(p→f,g)` (§5.6), so `cond`'s definition prints as the note writes it; the
-- coproduct `C` is context.
syntax:max (name := noteCond) "(" term "→" term "," term ")" : noteArith
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.cond] def unexpandCond : Unexpander
  | `($_ $_ $x $r $s) =>
    pure (.node .none ``noteCond #[mkAtom "(", x.raw, mkAtom "→", r.raw, mkAtom ",", s.raw, mkAtom ")"])
  | _ => throw ()

end Freyd.Alg
