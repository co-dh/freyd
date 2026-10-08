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
-- Appendix `wrap` (B&dM p.267), which §8.5's paragraph table defines.
import AOP.A8_4_KnapsackProgram
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
attribute [diag_noted] RelSet.Poly.cpL RelSet.Poly.cpLFn RelSet.Poly.linear RelSet.Poly.hasArg₂
  RelSet.Poly.relator RelSet.Poly.PolyF RelSet.Poly.PolyC RelSet.Poly.PolyC.zer RelSet.Poly.PolyC.one
  RelSet.Poly.PolyC.const RelSet.Poly.PolyC.arg₁ RelSet.Poly.PolyC.arg₂ RelSet.CL.clF RelSet.ListRel.cppFn RelSet.ListRel.cprFn RelSet.ListRel.cplFn
  RelSet.CL.bumpFold RelSet.ListRel.thinL
-- A map's type cell labels its ends (`TypeRender.funPieces`), and B&dM write the integers `Int`.
attribute [diag_noted] _root_.Int
attribute [diag_noted] RelSet.RT.tree RelSet.TB.tree RelSet.Party.party RelSet.Party.choose RelSet.Tex.interval RelSet.Tex.intern RelSet.Tardy.bagify RelSet.ListRel.subseq RelSet.MSS.mss RelSet.Paragraph.partition RelSet.Bracket.splits RelSet.Edit.step RelSet.TT.F RelSet.Bracket.wrapCatFn RelSet.Tex.Interval RelSet.Knapsack.within RelSet.Tour.tour RelSet.pow RelSet.Paragraph.ok RelSet.Paragraph.fits RelSet.Edit.unstep RelSet.Code.reduce RelSet.Code.decode RelSet.Code.Code RelSet.Tex.Real RelSet.Tex.inrange RelSet.Tex.val RelSet.Tex.step RelSet.Tex.arb RelSet.Tex.f RelSet.Tex.Prog.Reach RelSet.Tour.Journey RelSet.Tex.Iv RelSet.Tex.Digit RelSet.Sub RelSet.ListRel.segment RelSet.Filter.filter RelSet.GCTakeWhile.takewhile RelSet.Party.include Quotient RelSet.Knapsack.g₁ RelSet.Knapsack.g₂ RelSet.Paragraph.g₁ RelSet.Paragraph.g₂ RelSet.Tour.g₁ RelSet.Tour.g₂ RelSet.ListRel.cpL
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
-- B&dM p.267 Appendix: `wrap = cons . pair (id, nil)`.
attribute [diag_noted] Knap207.wrap Knap207.cons Knap207.nil Knap207.pair
attribute [diag_noted] RelSet.Bracket.init RelSet.Bracket.tail RelSet.Bracket.inits RelSet.Bracket.tails
  RelSet.Bracket.flatten

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
-- The constructor map is `[nil,cons]` only at the empty leaf; a leaf carrying a value is B&dM's
-- `list⁺` and its map is `[wrap,cons]`.  A DELABORATOR: the leaf type is implicit, so only the term has it.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Freyd.Alg.RelSet.CL.con] def delabCLCon : Delab := do
  let args := (← getExpr).getAppArgs
  if args.size < 2 || args.size > 3 then failure
  let leaf := if ← Meta.isDefEq args[0]! (mkConst ``Unit) then "nil" else "wrap"
  let f := mkIdent (Name.mkSimple s!"[{leaf},cons]")
  if args.size == 2 then `($f) else `($f $(← withAppArg delab))
-- The algebras a section names but the note writes by their body: a union of two graphs, or the
-- graph of a map given by a `match` on a coproduct, whose arms `mapLabel` reads as the junction.
attribute [diag_unfold] RelSet.Edit.editAlg RelSet.Paragraph.partAlg RelSet.Tour.tourAlg
  RelSet.Knapsack.dropFn RelSet.Tour.droplAlgFn RelSet.Tour.droprAlgFn RelSet.Paragraph.newAlgFn
  RelSet.Paragraph.glueAlgFn RelSet.Edit.baseStepFn

-- WHICH DEFINITIONS A PICTURE OPENS: the `AOP` constants the note draws opened — `tour%∋` against
-- the note's `⦇cpL(F)⟨g₁,g₂⟩cat thinL(Q)⦈`.  `diag_unfold` is `diag/tool/Tags.lean`'s,
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
/-- Binary max is B&dM's `bmax` (p.185), applied to the pair it takes. -/
@[app_unexpander Max.max] def unexpandMax : Unexpander
  | `($_ $a $b) => `($(mkIdent `bmax) $a $b)
  | _ => throw ()




open Lean PrettyPrinter in
/-- The category of relations on sets is the note's REGION `𝒜`, the letter every panel over it is
    drawn in.  An `app_unexpander` and not a `notation`: a token would make every binder the repo
    already names `𝒜` (`AOP.A5_3`'s `{s A B : 𝒜}`) print escaped. -/
@[app_unexpander RelSet] def unexpandRelSet : Unexpander
  | `($_:ident) => `($(mkIdent `𝒜))
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




-- A DATATYPE'S CARRIER IS THE NOTE'S OBJECT, under the note's own name for it: `tree(A)`,
-- `list⁺(A)`.  The unexpander writes the NAME, applied; the BRACKETS are the label printer's
-- (`appShow`), which puts them round the operand of every juxtaposed application, because
-- juxtaposition is composition and `tree A` reads as two things composed (CLAUDE.md).  One clause
-- per carrier, keyed on the constant — the tree the note draws is the tip-tree as much as the rose
-- tree, and the element type is the one argument either takes.








-- `pow` is `Rel(Set)`'s power object, the object the note writes `P` (`P A` in `S2_40`).
open Lean PrettyPrinter in
@[app_unexpander RelSet.pow] def unexpandRelSetPow : Unexpander
  | `($_ $A) => `($(mkIdent `P) $A)
  | _ => throw ()



-- The NATURAL NUMBERS are the note's `ℕ`.  Keyed `app.Nat`: the delaborator files a bare constant as a
-- nullary application, so a `const.Nat` key alone never fires and the label printed `Nat`.
open Lean PrettyPrinter Delaborator in
@[delab app.Nat] def delabNat : Delab := `($(mkIdent (Name.mkSimple "ℕ")))


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
-- by juxtaposition.  In the print-only category `noteArith` (`AOP.A5_3`), so no source file parses
-- these (`f(x)` would be a product).
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
-- Lists concatenate with the note's `⧺`, never Lean's `++`.
open Lean PrettyPrinter in
@[app_unexpander HAppend.hAppend] def unexpandNoteCat : Unexpander
  | `($_ $a $b) => pure (.node .none ``noteCat #[a, mkAtom "⧺", b])
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander HDiv.hDiv] def unexpandNoteDiv : Unexpander
  | `($_ $a $b) => pure (.node .none ``noteDiv #[a, mkAtom "/", b])
  | _ => throw ()
-- Lean's `List α` is the note's `[α]` (B&dM's list type), the spelling `delabConsList` gives `ConsList Unit α`.
open Lean PrettyPrinter in
@[app_unexpander List] def unexpandNoteList : Unexpander
  | `($_ $a) => `([$a])
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

-- The section's own integer ordering is written by its operator, as `leRel` is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Party.leq] def unexpandPartyLeq : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≤")))
-- KEPT: it builds `noteCat`, the note-arithmetic syntax declared in this file, which no `AOP`
-- module can import (`diag` imports `AOP`).
open Lean PrettyPrinter in
-- B&dM name no function for "the head replaced": `dropl(a,([b]⧺x,y))=([a]⧺x,…)` writes it as the
-- new head before the old tail, so the note does too.
@[app_unexpander RelSet.Tour.replaceHead] def unexpandTourReplaceHead : Unexpander
  | `($_ $a $x) => do pure (.node .none ``noteCat #[← `([$a]), mkAtom "⧺", ← `(tail($x))])
  | `($_ $a) => do pure (.node .none ``noteCat #[← `([$a]), mkAtom "⧺", ← `(tail(·))])
  | _ => throw ()
-- B&dM's `y subseq x` (p.123) is the predicate under the relation `subseq`, as `allFitP` is `fits`.
-- A rule, not a rename: the arrow `ListRel.subseq` already holds the name in `ListRel`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.subseqP] def unexpandSubseqP : Unexpander
  | `($_ $y $x) => `($(mkIdent `subseq) $y $x)
  | `($_ $y) => `($(mkIdent `subseq) $y)
  | _ => `($(mkIdent `subseq))
-- The list map on a function is B&dM's `list f` (p.205: `value = sum·list val`), printed as the
-- relator's own `f′` (`ListRel.list`'s notation), so a map and its graph read alike.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.cmap] def unexpandCmap : Unexpander
  | `($_ $f $x) => `($f′ $x)
  | `($_ $f) => `($f′)
  | _ => `($(mkIdent `list))


open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.leq] def unexpandListRelLeq : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≤")))
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.geq] def unexpandListRelGeq : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "≥")))

-- A CONVERSE WITH A NAME OF ITS OWN (CLAUDE.md): each theorem `Q = P°` names `P°` as `Q` and `Q°`
-- as `P` (`diag/tool/Label.lean`, `namedRecip?`), both spelled by their unexpanders (`Freyd.S2_40`, above).
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



open Lean PrettyPrinter in
/-- The greatest fixed point, `(νX : α°F(X)R)`, spelled as its least twin above. -/
@[app_unexpander nu] def unexpandNu : Unexpander
  | `($_ fun $x:ident => $b) => `(($(mkIdent (Name.mkSimple ("ν" ++ x.getId.toString))) : $b))
  | _ => throw ()









-- THE CONCRETE CYLINDER WEARS THE SAME NAMES AS THE ABSTRACT ONE (`AOP.A7_4_Cylinder`): `n`, `p`,
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


-- ONE BEAD, `R∩H`.  A meet is a bead's LABEL and never a wiring, and the note writes it TIGHT —
-- which is what `Label.lean`'s `∩` clause already writes, off the head constant.  So the label is
-- taken from the DEFINITION rather than from a name of its own: an unexpander would have to spell
-- the meet as Lean's own notation prints it, spaced, and `R ∩ H` is not what the note draws.
attribute [diag_unfold] RelSet.Van.RinterH
-- §7.5's algebra the same way: the note draws the arms, `⦇[nil,(ok→glue,new)]⦈`, and `progAlg` is
-- a Lean name for them — a name in the label says nothing the picture can be read against.
attribute [diag_unfold] RelSet.Van.progAlg



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

-- EVERY CONSTANT A LABEL MAY BE MADE OF IS REGISTERED HERE, spelling included.  `checkSpelled`
-- (`diag/tool/ExprReader.lean`) refuses a label carrying a constant no printing rule rewrote, so
-- the note's vocabulary is this file and nothing else: a constant added to a case study draws
-- nothing until its spelling is written down.  THE HEAD IS THE NAME, THE OPERANDS ARE THE
-- PRINTER'S — the clause keeps `$args*` where `gen` and `Q` above drop theirs, because a section
-- parameter is the panel's region and an ARGUMENT is part of what the arrow is.
-- THE NAMES THE NOTE NEVER WRITES ITSELF: the suffix is Lean's disambiguator (`Fn`, `Rel`, `Alg`,
-- `Relator`, as `editFn` is `edit` above). The author's decision (2026-09-22): a bundled relator
-- prints as the type it bundles (`op`, `Journey`).  Algebras kept the Lean name until 2026-10-04,
-- when the rule became that Lean follows the note: an algebra prints as the junction the note writes.
open Lean PrettyPrinter in
-- A rule, not a rename: the type `Tour.Journey` already holds the name in `Tour`.
@[app_unexpander RelSet.Tour.journeyRelator] def unexpandTourJourney : Unexpander
  | `($_ $args*) => `($(mkIdent `Journey) $args*)
  | _ => `($(mkIdent `Journey))
-- B&dM p.201's `cpL(F)`; the functor is the wire's, as for `cp`.
open Lean PrettyPrinter in
@[app_unexpander RelSet.ListRel.cpL] def unexpandCpL : Unexpander
  | _ => `($(mkIdent `cpL))
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
-- The concrete cylinder's transition, beside its `moves` and `cons`.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Vec.trans, delab const.Freyd.Alg.Vec.trans]
def delabVecTrans : Delab := `($(mkIdent `trans))

-- A SECTION'S RELATION, ORDER AND HELPER wear the note's letters, as `Party.R`, `Detab.V` and
-- `Van.Hrel` above do: which relation it is, is the definition line over the table.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.bang] def unexpandTexBang : Unexpander | _ => `($(mkIdent (Name.mkSimple "!")))
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
@[app_unexpander RelSet.Tex.Prog.f] def unexpandTexProgF : Unexpander
  | `($_ ($p, $q)) => `($(mkIdent `f) $p $q)
  | _ => throw ()
-- A SUBTYPE'S POINT IS ITS VALUE: `⟨(a,b),h⟩` is the interval `(a,b)`, the proof `h` a statement
-- about it that no formula of the note writes.
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.Subtype.mk] def delabSubtypeMk : Delab := do
  guard ((← getExpr).getAppNumArgs == 4)
  withNaryArg 2 delab
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
-- A relation given by cases holds outright on a case as `true`, the Boolean spelling beside it.
open Lean PrettyPrinter in
@[app_unexpander True] def unexpandTrue : Unexpander
  | `($_:ident) => `($(mkIdent `true))
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander False] def unexpandFalse : Unexpander
  | `($_:ident) => `($(mkIdent `false))
  | _ => throw ()
-- A projection applied to a point is the note's `π₁`/`π₂` applied to it: `V(π₂(p),π₂(q))`.
open Lean PrettyPrinter in
@[app_unexpander Prod.fst] def unexpandProdFst : Unexpander
  | `($_ $x) => `($(mkIdent `π₁) $x)
  | _ => throw ()
open Lean PrettyPrinter in
@[app_unexpander Prod.snd] def unexpandProdSnd : Unexpander
  | `($_ $x) => `($(mkIdent `π₂) $x)
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
-- THE SUM RELATOR ON A GIVEN COPRODUCT FAMILY IS THE NOTE'S `G+H`, as `Relator.sum` is.  A
-- delaborator: `G`, `H` are implicit, read off the coproduct family's type; the family is last.
open Lean PrettyPrinter Delaborator in
@[delab app.Freyd.Alg.Relator.sumOn] def delabRelatorSumOn : Delab := do
  let n := (← SubExpr.getExpr).getAppNumArgs
  guard (n ≥ 4)
  let g ← SubExpr.withNaryArg (n - 4) delab
  let h ← SubExpr.withNaryArg (n - 3) delab
  `($g + $h)

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
-- B&dM p.258: `shift(d,r)=(d+r)/10`, the representative `shiftPre` computes; the class `mkR x` of
-- any other representative is `x`, as `Quotient.mk`'s is.
open Lean PrettyPrinter in
@[app_unexpander RelSet.Tex.shiftPre] def unexpandTexShiftPre : Unexpander
  | `($_ $d $x) => do pure (.node .none ``noteDiv #[← `(($d + $x)), mkAtom "/", Syntax.mkNumLit "10"])
  | _ => throw ()

-- THE LEAN NAME IS THE BOOK'S WORD, so the printer needs no rule: a namespace tells two `head`s apart.
attribute [diag_noted] connected head Nat.F Nat.zero Nat.succ union RelSet.Detab.length RelSet.Tex.length RelSet.Edit.op
  RelSet.GCTakeWhile.R RelSet.ListRel.cat RelSet.ListRel.concat RelSet.ListRel.connected RelSet.ListRel.cons
  RelSet.MSS.k RelSet.Paragraph.head RelSet.Tour.head RelSet.Tour.next RelSet.Edit.Pair.F
  RelSet.Tardy.snag RelSet.Tardy.bmax RelSet.Digits.«Digit⁺»

/-- The book's closure `R*` (6.7), postfix like `°`.  LAST IN THE FILE: below it every quotation's
    splice `$args*` parses as `star $args`, so a clause `($_ $args*)` matched nothing.  KEPT here, not
    beside `star`: `*` is core's splice suffix (`Init/Notation.lean`, `stx "*"`), and every module
    importing `AOP.A6_7` would lose its `$args*`. -/
postfix:max "*" => star

end Freyd.Alg
