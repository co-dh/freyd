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
import AOP.A7_3_Party
import AOP.A7_4_Cylinder
import AOP.A7_4_CylinderVecRel
import AOP.A7_5_Van
import AOP.A7_7_MSS
import AOP.A7_7_TakeWhile
import AOP.A8_1
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
attribute [diag_induced] relCata InitialAlgebra.cata Freyd.HasBinaryProducts.pair Λ
  RelProd.pair prodMap

-- WHICH DEFINITIONS A PICTURE OPENS: the `AOP` constants the note draws opened — `tour%∋` against
-- the note's `⦇listcp(F)⟨g₁,g₂⟩cat thinlist(Q)⦈`.  `diag_unfold` is `diag/tool/ExprReader.lean`'s,
-- the mirror of `diag_induced`; the tags are here for the same reason `diag_induced`'s are, that
-- the note's spelling is the DIAGRAM's vocabulary and not the algebra's.
attribute [diag_unfold] RelSet.Tour.tour

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
/-- The type functor AS A RELATOR is the note's lane `T`, the same letter its action on arrows
    already prints with (`T(R)`); which initial algebras it is built from is not part of the name. -/
@[app_unexpander typeRelator] def unexpandTypeRelator : Unexpander
  | `($_ $_) => `($(mkIdent `T))
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
@[app_unexpander RelSet.Bracket.dNE] def unexpandDNE : Unexpander
  | `($_ $A) => `($(mkIdent (Name.mkSimple "list⁺")) $A)
  | _ => throw ()

-- The note's `thin(Q)` is a DELIMITED operator, like `est(R)` (`AOP.A7_1`) and `P(R)` (`AOP.A5_4`)
-- which are declared this same way: an unexpander returns a term, and no term prints its own brackets.
notation:max "thin(" Q ")" => thinRel Q

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

-- WHAT THE CASE STUDIES' MIDDLE BEAD OPENS.  The note draws each algebra's own coproduct —
-- `⦇[nil,cons](within(w)) ∪ [nil,π₂]⦈`, `⦇[wrap wrap,new ∪ (glue (ok w))]⦈` — where the name
-- `Salg` says nothing; `diag_unfold` is `diag/tool/ExprReader.lean`'s, as for `tour` above.
attribute [diag_unfold] RelSet.Knapsack.Salg RelSet.Paragraph.Salg
-- The prefix algebra is drawn written out, `⦇[nil,⊸ nil ∪ cons]⦈` (13.3.3b), never as its name.
attribute [diag_unfold] RelSet.ListRel.prefAlg
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
-- The unit bead is `singletonMap = Λ 𝟙`; opened, the `Λ` label case prints it `𝟙%∋`.
attribute [diag_unfold] singletonMap

end Freyd.Alg
