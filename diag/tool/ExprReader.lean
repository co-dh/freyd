/-
  `ExprReader` — the Expr side of the theorem visualizer: a declaration's ELABORATED TYPE read as
  the 2-categorical data a picture is drawn from.  Nothing here reads a formula string, a signature
  table or the note; the types come from the environment, which is the only place they are true.

  THE SOURCE 2-CATEGORY.  A 0-cell is an allegory `𝒜`, a 1-cell a `Relator 𝒜 ℬ`, a 2-cell a family
  `φ : ∀ a, G.obj a ⟶ F.obj a` together with a proof that it is natural.  An OBJECT `a : 𝒜` is the
  1-cell `𝟏 → 𝒜` and an ARROW `R : a ⟶ b` a 2-cell between two such, which is why a factor that is a
  fixed arrow — not a family in the region's object — can only ride the object wire.

  THE DOT IS A THEOREM, NOT A FIELD.  `dot` builds `StrictNatural F G φ`, `LaxNatural F G φ` and
  `¬ LaxNatural G F φ` and looks for a declaration in the environment proving one; nothing is
  inferred from the family's shape or its name.  No declaration, no dot.
-/
import Lean
import AOP.A5_7
-- The BIFUNCTOR, for the one test that says which bundles are lanes the picture names: a binary
-- relator is one, and its partial application is what `openBuiltField?` opens.
import AOP.A5_5_TypeFunctor

open Lean

/-- WHICH DEFINITIONS A PICTURE OPENS.  The mirror of a name kept: where the NOTE writes a `def`'s
    BODY and Lean prints its name, the picture is of the body, so the exporter opens it before
    drawing.  Registered HERE, in the file that reads it — an attribute is only usable in a module
    that imports the one declaring it, so the tags go in `diag/StrDiagNames.lean`. -/
register_label_attr diag_unfold

/-- WHICH EQUATIONS A SIDE IS REWRITTEN ALONG before it is drawn.  The mirror of a name opened: where
    the NOTE draws a factor as two beads and Lean's statement names it as one, the side is rewritten
    by the declaration that says so, so the picture is of the note's form.  Registered here, tagged
    in `diag/StrDiagNames.lean`, for the same reason as `diag_unfold`. -/
register_label_attr diag_rewrite

/-- WHICH EQUATION DEFINES AN INDUCED ARROW.  The mirror of `diag_induced`: that attribute says a
    constant's application is what a universal property GIVES, this one says which theorem is the
    equation it gives it BY — `relCata_cancel`, `α⦇R⦈=F(⦇R⦈)R`.  A commutative diagram draws that
    square where the picture has to say what produced the arrow
    (`diag/tool/CommutativeDiagram.lean`, `definingFace`), finding it by UNIFYING the law's own
    induced arrow with the one in hand, so one tag answers every instance.  Registered here rather
    than beside `diag_induced` because the tags live in `diag/StrDiagNames.lean`, which imports this
    module and not the drawer. -/
register_label_attr diag_defines

/-- WHICH BINARY OPERATION ON ONE HOM IS A JOIN, and the symbol that stands between the panels it
    draws.  An assertion about a JOIN is ONE PANEL PER OPERAND — the note's `∪` row of
    `<lax-closure>` is two squares with `∪` between them — where a MEET is one bead and one panel,
    which is what `laxNatural_inter_false` makes it.  The two have the SAME type, so nothing but the
    operator itself separates them: it is TAGGED and never matched, and the tag CARRIES ITS SYMBOL
    (`@[diag_join "∪"]`), so no drawer spells an operator and a new join costs one line beside its
    declaration.  Registered here, tagged in the module that reads it, like `diag_defines`. -/
syntax (name := diagJoin) "diag_join " str : attr

/-- The tagged operators, each with its symbol.  An EXTENSION and not a `ParametricAttribute`
    because the operator is in an imported module — the allegory's `∪` is not the picture's to
    edit — and a parametric attribute refuses those. -/
initialize diagJoinExt : SimplePersistentEnvExtension (Name × String) (NameMap String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, s) => m.insert n s
    addImportedFn := fun es => es.foldl (fun m a => a.foldl (fun m (n, s) => m.insert n s) m) {} }

initialize registerBuiltinAttribute {
  name := `diagJoin
  descr := "a binary operation on one hom drawn as one panel per operand, with this symbol between"
  add := fun decl stx _ => do
    let sym ← match stx with
      | `(attr| diag_join $s:str) => pure s.getString
      | _ => throwError "diag_join takes the symbol the panels are separated by, as in \
          `@[diag_join \"∪\"]`"
    modifyEnv (diagJoinExt.addEntry · (decl, sym)) }

namespace Freyd.StrDiag

/-- Every namespace of the repo, for a printing context's `openDecls`.  A NAME IS SHORTENED BY THE
    PRINTER: it knows which namespaces are open and keeps exactly the qualification two constants
    sharing a name need to be told apart, where cutting namespaces off the printed string knows
    only the ones someone wrote into the chain and leaves `MSS.geq` for every one it does not.
    Read off the environment, so a namespace added tomorrow needs no edit here. -/
def repoNamespaces (env : Environment) : List Name :=
  env.getNamespaceSet.toList.filter fun n => n.getRoot == `Freyd

/-- THE PRINTING CONTEXT OF ONE DRAWN DECLARATION: it prints as its own source file reads it, so it
    is built per declaration and `currNamespace` is that declaration's namespace.  Which is what
    breaks a tie: every namespace of the repo is open, so `R` names a constant in a dozen chapters
    and the printer keeps `Tex.R` to tell them apart — but name resolution takes the CURRENT
    namespace's longest prefix first and never reaches the open ones, so inside `…RelSet.Tex` the
    bare `R` is that file's `R` and prints bare, while `segment`, which `…RelSet.Tex` does not
    declare, still comes out of the open namespaces unqualified. -/
def declCtx (env : Environment) (opts : Options) (scopes : List Name) (decl : Name) : Core.Context :=
  { fileName := "<diag-export>", fileMap := default, options := opts,
    currNamespace := decl.getPrefix,
    openDecls := (scopes ++ repoNamespaces env).map (.simple · []) }

/-- A one-field record IS its field as far as a picture is concerned: the object `⟨X⟩` of a
    category of sets is the set `X`, and printing the wrapper makes every lane label unreadable.
    Generic over the environment — any constructor with exactly one field, no list of names.

    A RECORD is a type with ONE constructor.  Without that test the leaf `wrap ()` of a cons-list —
    a one-field constructor of a type that has another — prints as `()`, and the note's `nil`
    disappears from the label of an algebra that is about nothing else. -/
def unwrapRecord? (x : Expr) : MetaM (Option Expr) := do
  let .const n _ := x.getAppFn | return none
  let some (.ctorInfo ci) := (← getEnv).find? n | return none
  if ci.numFields != 1 then return none
  let some (.inductInfo ii) := (← getEnv).find? ci.induct | return none
  if ii.ctors.length != 1 then return none
  let args := x.getAppArgs
  if args.size != ci.numParams + 1 then return none
  return some args[args.size - 1]!

/-- The INVERSE peel: the one FIELD of a one-field record IS that record.  `⟨X⟩.carrier` is the
    object `X`, so a product of carriers is the product of the objects the picture draws
    (`A×E[A]`, never `A×E([A])`), and a projection Lean wrote only because `×` is a type former
    says nothing a reader can use.  Both spellings of a projection — the `proj` node and the
    projection FUNCTION — because either can reach a label. -/
def unprojRecord? (e : Expr) : MetaM (Option Expr) := do
  let oneField (ctor : Name) : MetaM Bool := do
    let some (.ctorInfo ci) := (← getEnv).find? ctor | return false
    if ci.numFields != 1 then return false
    let some (.inductInfo ii) := (← getEnv).find? ci.induct | return false
    return ii.ctors.length == 1
  match e with
  | .proj s _ x =>
    let some (.inductInfo ii) := (← getEnv).find? s | return none
    let some c := ii.ctors.head? | return none
    return if (← oneField c) then some x else none
  | _ =>
    let .const n _ := e.getAppFn | return none
    let some pi := (← getEnv).getProjectionFnInfo? n | return none
    unless ← oneField pi.ctorName do return none
    let args := e.getAppArgs
    return if h : args.size > pi.numParams then some args[pi.numParams] else none

/-- A POSITIONAL `.proj` WRITTEN THROUGH ITS OWN PROJECTION FUNCTION.  Lean leaves a field access on
    a term whose structure it inferred as a positional node, which prints `inst✝.1` — and with the
    field's name out of reach so is every notation and delaborator keyed on it, so the repo's own
    `a×b` for a tabulation's apex never fires and the label leaks the elaborator's internals.  One
    rule for every structure, read off the environment: the `i`-th field has a name, and the same
    term written with it prints as the picture's own spelling. -/
def namedProj? (e : Expr) : MetaM (Option Expr) := do
  let .proj s i x := e | return none
  let some fi := (getStructureInfo? (← getEnv) s).bind (·.fieldNames[i]?) | return none
  unless (← Meta.whnf (← Meta.inferType x)).isAppOf s do return none
  return some (← Meta.mkProjection x fi)

/-- The head IDENTIFIER the printer writes an application under, and `none` where the printer's own
    notation DELIMITS the operand instead (`est(R)`, `⦇S⦈`) — those open with an ATOM, which is what
    a bracket is. -/
partial def stxHead : Syntax → Option Name
  | .ident _ _ n _ => some n
  | .node _ _ args => args[0]?.bind stxHead
  | _ => none

/-- Whether a bundle is a LANE THE PICTURE NAMES — a functor between the categories it draws.  The
    rule below is about lanes and nothing else: a CLASS INSTANCE is a bundle assembled from bundles
    too, and its fields are drawn by the notation each carries of its own (`∋`, `EA`), never by
    opening the instance it was assembled from. -/
def isLaneBundle (s : Expr) : MetaM Bool := do
  let t ← Meta.whnfD (← Meta.inferType s)
  return t.isAppOf ``Freyd.Alg.Relator || t.isAppOf ``Freyd.Functor
      || t.isAppOf ``Freyd.Alg.BiRelator

/-- A BUNDLE ASSEMBLED FROM BUNDLES THAT CARRY THE FIELD HAS NO NAME OF ITS OWN.  `relatorName?`
    writes a relator's printed head and drops its arguments, because they are the TYPES the picture
    already draws on the wires — but an argument that is ITSELF A BUNDLE WITH THAT FIELD is another
    lane of the same picture, so `Relator.prod G G'` and `Relator.prod F F'` both come out `prod`,
    and `BiRelator.appl F A` comes out `appl` where the note writes what `F` does.  The test is the
    FIELD, not the kind: the assembled bundle need not be of its parts' type (a bifunctor at a fixed
    argument is a unary relator), only built from something the field could have come from. -/
def builtOfFieldCarrier (fld : Name) (s : Expr) : MetaM Bool := do
  s.getAppArgs.anyM fun a => do
    let some c := (← Meta.whnfD (← Meta.inferType a)).getAppFn.constName? | return false
    -- Only a structure has fields — the length `m : Nat` of `[m]` carries none — and `findField?`
    -- on anything else panics and answers from an empty default instead of saying so.
    return isStructure (← getEnv) c && (findField? (← getEnv) c fld).isSome

/-- THE BUNDLE ITSELF, under the PARENT projections Lean writes to reach an inherited field: a
    relator and its `toFunctor` are one lane, and only the relator says what it was built from. -/
partial def bundleCore (s : Expr) : MetaM Expr := do
  let .const n _ := s.getAppFn | return s
  let some pi := (← getEnv).getProjectionFnInfo? n | return s
  let some (.ctorInfo ci) := (← getEnv).find? pi.ctorName | return s
  let some f := (getStructureInfo? (← getEnv) ci.induct).bind (·.fieldNames[pi.i]?) | return s
  let some _ := isSubobjectField? (← getEnv) ci.induct f | return s
  let args := s.getAppArgs
  if h : args.size > pi.numParams then bundleCore args[pi.numParams] else return s

/-- The bundle AS A CONSTRUCTOR APPLICATION, opening the definition it was built by and, above it,
    the parent projections Lean wrote to reach an inherited field (`Relator.toFunctor`). -/
partial def builtCtor? (s : Expr) : MetaM (Option Expr) := do
  let .const n _ := s.getAppFn | return none
  if let some (.ctorInfo _) := (← getEnv).find? n then return some s
  let args := s.getAppArgs
  if let some pi := (← getEnv).getProjectionFnInfo? n then
    unless args.size > pi.numParams do return none
    let some c ← builtCtor? args[pi.numParams]! | return none
    let some v ← Meta.project? c pi.i | return none
    return some (mkAppN v (args.extract (pi.numParams + 1) args.size)).headBeta
  let some s' ← Meta.unfoldDefinition? s | return none
  builtCtor? s'

/-- A FIELD OF SUCH A BUNDLE, opened to the field's OWN DEFINITION at that bundle: what the picture
    is of, since the name is not available.  `(G×G').obj A` is `GA×G'A` and `(G×G').map R` is
    `G(R)×G'(R)`, which is the note's own row.  Only where the field is APPLIED — the exact case
    `concreteProj?` excludes, and there because a relator with a NAME (`T`, `E`, `list`) is drawn by
    it and never by the object map inside it; a bundle with an argument of its own type has none. -/
partial def openBuiltField? (e : Expr) : MetaM (Option Expr) := do
  let .const n _ := e.getAppFn | return none
  let some pi := (← getEnv).getProjectionFnInfo? n | return none
  let args := e.getAppArgs
  unless args.size > pi.numParams + 1 do return none
  let s := args[pi.numParams]!
  let some (.ctorInfo ci) := (← getEnv).find? pi.ctorName | return none
  let some fld := (getStructureInfo? (← getEnv) ci.induct).bind (·.fieldNames[pi.i]?) | return none
  let core ← bundleCore s
  unless ← isLaneBundle core do return none
  unless ← builtOfFieldCarrier fld core do return none
  -- The DEFINITION is taken off the constructor and nothing further is reduced: `whnf` would go on
  -- to unfold the object or arrow the field lands on and print its implementation.
  let some c ← builtCtor? s | return none
  let some v ← Meta.project? c pi.i | return none
  pointwise (mkAppN v (args.extract (pi.numParams + 1) args.size)).headBeta
where
  /-- THE OPENED FIELD READ AT ITS ARGUMENTS.  A field written POINT-FREE — `Relator.comp`'s
      `obj := L.obj ∘ G.obj` — is the same function written pointwise, and only the pointwise form
      names the two lanes: `L(GA)`, where the composition itself says `(Functor.obj L ∘ Functor.obj
      G) A`.  `∘` is APPLICATION COMPOSED and the picture draws applications, so it is read through;
      every other head stands, because unfolding it would print the implementation the note draws by
      name. -/
  pointwise (x : Expr) : MetaM (Option Expr) := do
    unless x.getAppFn.isConstOf ``Function.comp do return some x
    let some v ← Meta.unfoldDefinition? x | return some x
    pointwise v.headBeta

partial def unwrapRecords (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    match ← unwrapRecord? x with
    | some y => return .done y
    | none =>
      match ← namedProj? x with
      | some y => return .visit y
      | none =>
        match ← openBuiltField? x with
        | some y => return .visit y
        | none => return .continue)

/-- Lean's pretty printer on one line, the repo's own namespaces off: inside a picture of the
    repo's algebra `Freyd.Alg.relCata R` is noise and `⦇R⦈` is the thing itself. -/
def unlabelled? (e : Expr) : MetaM (Option String) := do
  let env ← getEnv
  for n in e.getUsedConstants do
    if ← Meta.isMatcher n then return some s!"the matcher `{n}`"
    if isAuxRecursor env n then return some s!"the auxiliary recursor `{n}`"
    if n.isInternal then return some s!"the internal name `{n}`"
  return none

/-- Lean's pretty printer on one line, the repo's own namespaces off — and the KINDS a label may
    never be made of refused rather than printed.  A matcher, an auxiliary recursor, an internal
    name and a local bound as an instance are Lean's own compilation artefacts: `cons.match_1` and
    `est(RinstHAdd)` are what they spell, which is a picture of the elaborator and not of the
    statement.  The test is the KIND — `isMatcher`, `isAuxRecursor`, `Name.isInternal`, the binder
    — never the text of the name, so a matcher spelled any other way is refused too, and the panel
    comes back a CANNOT-DRAW naming the kind instead of a drawing nobody can read. -/
def plain (e : Expr) : MetaM String := do
  let e ← unwrapRecords e
  if let some k ← unlabelled? e then
    throwError "a label is the note's own spelling of an arrow, and `{← Meta.ppExpr e}` is made of \
      {k}, which is Lean's own elaboration and names no arrow the note writes"
  -- A label is the note's spelling, not Lean syntax: a name the parser would need escaped (`prefix`
  -- is a keyword) prints bare, so the `«»` the formatter wraps it in are dropped.
  let s := (toString (← Meta.ppExpr e)).replace "«" "" |>.replace "»" ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- A PROJECTION of a bundle the statement names OUTRIGHT, reduced to what it projects: the carrier
    of `initial Unit A` is the list object `[A]`, where a bundle the statement BINDS — the `I` of
    `α⦇f⦈=F(⦇f⦈)f`, or the `[inst]` an abstract allegory's `∋` and `EA` come from — has nothing to
    reduce and keeps the structure's own letter.  Only the STRUCTURE argument is reduced, to its
    constructor, and the projection then taken: `whnf` on the whole term would go on to unfold the
    object it lands on and print the list's implementation where the note writes `[A]`. -/
def concreteProj? (x : Expr) : MetaM (Option Expr) := do
  let some b ← onBundle x | return none
  -- The field access is one delta step and `whnfCore` then takes the field off the constructor and
  -- stops, where `whnf` would go on to unfold the object it lands on.
  let y ← Meta.whnfCore ((← Meta.unfoldDefinition? b).getD b)
  return if y == x then none else some y
where
  /-- The same term with the BUNDLE it READS A FIELD OFF reduced to its constructor: `none` when it
      reads none, when the bundle is one the statement binds, or when the field is APPLIED to
      something — `F.obj X` is the functor's action, which the note writes by the functor's own name
      and never by the object map inside it. -/
  onBundle (x : Expr) : MetaM (Option Expr) := do
    match x with
    | .proj _ _ s =>
      if s.getAppFn.isFVar then return none
      return some (x.updateProj! (← Meta.whnf s))
    | _ =>
      let .const n _ := x.getAppFn | return none
      let some pi := (← getEnv).getProjectionFnInfo? n | return none
      let args := x.getAppArgs
      if args.size != pi.numParams + 1 then return none
      let s := args[pi.numParams]!
      if s.getAppFn.isFVar then return none
      return some (mkAppN x.getAppFn (args.set! pi.numParams (← Meta.whnf s)))

/-- An OBJECT as the picture must say what it IS: every sub-expression that is ITSELF AN OBJECT of
    the same category and is a field of a bundle the statement names outright, replaced by the object
    that field is.  The type test is what keeps it to objects: the `F` of `F T` is a field of a
    bundle too, and a relator is drawn by its own name, never by the object map inside it — as an
    arrow of a named bundle is drawn `α`. -/
def objSpelling (e : Expr) : MetaM Expr := do
  let cat ← Meta.inferType e
  Meta.transform e (post := fun x => do
    unless ← Meta.isDefEq (← Meta.inferType x) cat do return .continue
    match ← concreteProj? x with
    | some y => return .visit y
    | none => return .continue)

/-- The source and target of a hom type `a ⟶ b`. -/
def homObjs? (t : Expr) : Option (Expr × Expr) :=
  match t.getAppFnArgs with
  | (``Cat.Hom, #[_, _, a, b]) => some (a, b)
  | _ => none

/-- Whether a type is the OBJECTS of a category — it carries a `Cat` instance.  The class decides,
    not a list of carriers: `Allegory` extends `Cat`, so every category the book builds answers yes
    without a clause, and a hom, a relator or a datum answers no.

    The HOM universe is the instance's to choose — `Cat.{w} 𝒞` fixes the homs' universe, which the
    objects' type does not name — so the class is built with fresh levels and synthesis assigns
    them; `mkAppM` refuses the same expression for having them unassigned. -/
def isObjType (ty : Expr) : MetaM Bool := do
  let cls ← Meta.mkConstWithFreshMVarLevels ``Cat
  return (← Meta.synthInstance? (mkApp cls ty)).isSome

/-- Whether the term is ONE COMPONENT of a family of arrows the statement BINDS: an application
    whose head is a free variable and whose own type is a hom, `φ A` for `φ : ∀ A, G A ⟶ F A`.  The
    test is the TYPE and not a name: a bound family has no constant to list, and the whole point of
    it is that the statement, not the library, is what hands the family over.

    AN INDEX IS AN OBJECT, and that is what makes the note set the component tight: `φA` is `φ` at
    the wire under it, one name.  Every OTHER argument makes the term an operator APPLIED, which
    takes parentheses like every other application (`thin(Q)`, `est(R)`, `sort(P)`, `listcp(F)`) —
    so the test is on the arguments' TYPES: an object of SOME category, which is `isObjType`, and an
    arrow index or a relator index goes the other way without a clause of its own.

    WHOSE category is not the hom's business.  A family between two relators `F G : Relator 𝒜 ℬ` is
    indexed by `𝒜` and valued in `ℬ`, so measuring the index against the object type the hom names
    calls `φ A` an application wherever the two categories differ — which is every lax-naturality
    square the note draws. -/
def isComponent (e : Expr) : MetaM Bool := do
  unless e.isApp && e.getAppFn.isFVar do return false
  unless (homObjs? (← Meta.inferType e)).isSome do return false
  e.getAppArgs.allM fun a => do
    let ty ← Meta.inferType a
    -- AN ARROW IS NEVER AN OBJECT INDEX, whatever instance its hom type carries: `sort P` is `sort`
    -- applied to a relation, which takes the brackets of every application, so the hom test comes
    -- first and `isObjType` never gets to answer for it.
    if (homObjs? ty).isSome then return false else isObjType ty

/-- The last two arguments of an application. -/
def lastTwo (args : Array Expr) : Option (Expr × Expr) :=
  if h : args.size ≥ 2 then some (args[args.size - 2], args[args.size - 1]) else none

/-- The WIRES a functor expression is: `Relator.comp F G` is not one wire but two NESTED, `G`
    outside `F`, and the identity relator is no wire at all.  Outermost first, as a wire stack is
    read left to right in the picture. -/
partial def wiresOf (f : Expr) : Array Expr :=
  match f.getAppFnArgs with
  | (``Freyd.Alg.Relator.toFunctor, args) => match args.back? with
    | some r => wiresOf r
    | none => #[f]
  | (``Freyd.Alg.Relator.comp, args) => match lastTwo args with
    | some (a, b) => wiresOf b ++ wiresOf a
    | none => #[f]
  -- A COMPOSITE OF FUNCTORS IS THE SAME STACK: the function category's lanes are `Freyd.Functor`s
  -- and compose by `compFunctor`, so a reading that flattened only the relator composite left the
  -- whole stack standing as one wire labelled `compFunctor …`.
  | (``Freyd.compFunctor, args) => match lastTwo args with
    | some (a, b) => wiresOf b ++ wiresOf a
    | none => #[f]
  | (``Freyd.Alg.Relator.idRelator, _) => #[]
  | (``Freyd.idFunctor, _) => #[]
  | _ => #[f]

/-- How a carrier TYPE decomposes into the strands a port at it carries: the unit, a product of
    two, a coproduct of two, or an atom — a base type, a list, a power object's predicate type.
    The elaborator answers it (`whnfD`), no table does, and the `.atom` carries the REDUCED term so
    a reader that labels it labels what it decomposed. -/
inductive Wiring where
  | one | prod (a b : Expr) | sum (a b : Expr) | atom (t : Expr)

def wiringOf (t : Expr) : MetaM Wiring := do
  let t ← Meta.whnfD t
  match t.getAppFnArgs with
  | (``Prod, #[a, b]) => return .prod a b
  | (``Sum, #[a, b]) => return .sum a b
  | (``Unit, _) | (``PUnit, _) => return .one
  | _ => return .atom t

/-- Whether a port at this TYPE carries any strand at all — the whole of what `⊸` asks, since
    discarding nothing is not a discard.  Stated on the TYPE, so the question does not have to
    build a labelled object first.  A COPRODUCT always carries one: `𝟏+X` is drawn as `X`'s
    strands, which a summand of a pattern functor has, and any other coproduct stays the one wire
    a tape opens. -/
partial def hasStrands (t : Expr) : MetaM Bool := do
  match ← wiringOf t with
  | .one => return false
  | .prod a b => return (← hasStrands a) || (← hasStrands b)
  | .sum .. | .atom _ => return true

/-! ### A region built as a ONE-FIELD STRUCTURE over its index

  `RelSet` is `⟨carrier : Type⟩`, so a theorem about it quantifies over the INDEX — `A : Type` —
  and speaks of the objects `dE A`, `dList A`.  Such a binder IS an object variable of the region:
  the object is `a : 𝒞` and the index is its field, and `⟨𝒞.field a⟩` is `a` by structure eta, so
  the two readings are the same term.  Read off `getStructureInfo?`, so any region built that way
  works and no wrapper, projection or abbreviation is named here. -/

/-- The region's ONE field, or `none` where the region is not a one-field structure. -/
def regionField? (regionTy : Expr) : MetaM (Option Name) := do
  let some C := regionTy.getAppFn.constName? | return none
  let some info := getStructureInfo? (← getEnv) C | return none
  if info.fieldNames.size == 1 then return info.fieldNames[0]? else return none

/-- The type an INDEX binder must have to name an object of the region: the type the region's one
    field has.  `none` where the region is not a one-field structure, or where that field's type
    mentions the object itself — an index could not then stand for it. -/
def regionIndexType? (regionTy : Expr) : MetaM (Option Expr) := do
  let some f ← regionField? regionTy | return none
  Meta.withLocalDeclD `a regionTy fun a => do
    let t ← instantiateMVars (← Meta.inferType (← Meta.mkProjection a f))
    if t.containsFVar a.fvarId! then return none else return some t

/-- A family as a function of an OBJECT of the region.  A statement quantifying over the object
    itself abstracts that binder; one quantifying over the region's INDEX abstracts a fresh object
    `a` after `A := 𝒞.field a`, which is the same family read through the structure's constructor
    and is well typed because `F.obj ⟨𝒞.field a⟩` IS `F.obj a`. -/
def familyOf (regionTy v core : Expr) : MetaM Expr := do
  if ← Meta.isDefEq (← Meta.inferType v) regionTy then return ← Meta.mkLambdaFVars #[v] core
  let some f ← regionField? regionTy
    | throwError "the family {← Meta.ppExpr core} is indexed by {← Meta.ppExpr v}, which is \
        neither an object of the region {← Meta.ppExpr regionTy} nor its index — that region is \
        not a one-field structure, so it has no index"
  Meta.withLocalDeclD `a regionTy fun a => do
    Meta.mkLambdaFVars #[a] (core.replaceFVar v (← Meta.mkProjection a f))

/-- The head of a statement's CONCLUSION, under whatever `∀` binders it carries. -/
partial def concHead : Expr → Name
  | .forallE _ _ b _ => concHead b
  | .mdata _ b => concHead b
  | t => (t.getAppFn.constName?).getD Name.anonymous

/-! ### The wire stack of an OBJECT, asked of the environment

  §13.6's objects are records and defs — `dSched X`, `⟨X × Sched X⟩` — not `F.obj X`, so a
  syntactic peel finds nothing in them.  What a picture needs is the RELATORS whose action they
  are, and the environment is where those live: every constant whose type is `Relator 𝒜 𝒜` is a
  candidate wire, and `X` carries that wire when `R.obj ?a` unifies with `X`.  No list of relator
  names in the tool. -/

/-- One wire of a stack: a relator, or the LEFT FACTOR of a product — `A×−` is a wire whose label
    names the factor, and the rest of the stack is what the product's right factor peels to. -/
inductive Wire where
  | rel (r : Expr)
  | timesL (l : Expr)
  deriving Inhabited

/-- Does the wire mention `v`?  A lane is a relator of the WHOLE region, so a wire built over an
    object the statement quantifies over is a different functor at each object and carries no bead. -/
def Wire.mentions (v : FVarId) : Wire → Bool
  | .rel r | .timesL r => r.containsFVar v

/-- A relator's own spelling as a LANE, in the NOTE's notation and not the pretty printer's.  A
    pairing, an identity, a composite and the product bifunctor have no name of their own, so they
    are written structurally — `⟨𝟙,T⟩`, `𝟙`, `list list`, `×` — and the length of that string is
    what reserves the lane's room, which is why it cannot be left to `Relator.comp list list`.
    Every head here is matched as an `Expr` head, so nothing rests on how a name prints.
    A composite is juxtaposition in DIAGRAM order — `comp F G` is `F` then `G` — and it is read off
    `wiresOf`, which is what drops the identity factors and flattens the nesting. -/
partial def relLabel (r : Expr) : MetaM String := do
  match r.getAppFnArgs with
  | (``Freyd.Alg.Relator.pair, args) =>
    match lastTwo args with
    | some (f, g) => return "⟨" ++ (← relLabel f) ++ "," ++ (← relLabel g) ++ "⟩"
    | none => plain r
  | (``Freyd.Alg.Relator.prod, args) =>
    match lastTwo args with
    | some (f, g) => return (← relLabel f) ++ "×" ++ (← relLabel g)
    | none => plain r
  | (``Freyd.Alg.Relator.comp, _) =>
    -- `wiresOf` is OUTERMOST first; juxtaposition is diagram order, so it is read back to front.
    let ws := wiresOf r
    if ws.isEmpty then return "𝟙"
    return " ".intercalate (← ws.toList.reverse.mapM relLabel)
  | (``Freyd.Alg.timesRel, _) => return "×"
  | (``Freyd.Alg.Relator.idRelator, _) => return "𝟙"
  | _ => plain r

/-- `n` applied to fresh universe and argument metavariables, the LAST arguments unified with the
    ones given and the instance arguments synthesised afterwards, when the category they mention is
    known.  `mkAppM` cannot do this: it refuses a result that still holds a metavariable, and a peel
    is precisely an application whose remaining argument is what unification has to find. -/
def mkAppMeta (n : Name) (last : Array Expr) : MetaM (Expr × Array Expr) := do
  let some ci := (← getEnv).find? n | throwError "no constant {n}"
  let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
  let (args, bis, _) ← Meta.forallMetaTelescope (ci.type.instantiateLevelParams ci.levelParams lvls)
  unless args.size ≥ last.size do throwError "{n} takes fewer than {last.size} arguments"
  for i in [0 : last.size] do
    unless ← Meta.isDefEq args[args.size - last.size + i]! last[i]! do
      throwError "{n} does not apply to {← Meta.ppExpr last[i]!}"
  -- WHICH arguments are instances is the declaration's own binder info; `isClass?` on the argument
  -- TYPE is a guess, and a guess that says "no" leaves the application stuck with no error at all.
  for i in [0 : args.size] do
    unless bis[i]! == .instImplicit do continue
    let .mvar id := args[i]! | continue
    if ← id.isAssigned then continue
    let t ← instantiateMVars (← id.getType)
    unless (← Meta.isClass? t).isSome do throwError "{n} arg {i} not a class: {← Meta.ppExpr t}"
    let .some v ← Meta.trySynthInstance t | throwError "no instance for {← Meta.ppExpr t}"
    unless ← Meta.isDefEq args[i]! v do throwError "{n}: instance mismatch at {← Meta.ppExpr t}"
  return (mkAppN (mkConst n lvls) args, args)

/-- A lane's action as a FUNCTOR: a relator's is its underlying functor, and a functor lane — `E`,
    which is no relator — is its own.  Read off the lane's TYPE, never its name. -/
def laneFunctor (R : Expr) : MetaM Expr := do
  if (← Meta.inferType R).isAppOf ``Freyd.Alg.Relator then
    return (← mkAppMeta ``Freyd.Alg.Relator.toFunctor #[R]).1
  return R

/-- Two lanes are one wire when they have the same OBJECT ACTION — or the same left factor, that
    lane being pinned to its object.  A lane's geometry is its object action, so the power relator
    and the existential-image functor, which agree on objects (`E A`) and differ only on arrows,
    are the one `E` lane the note draws; asked by `isDefEq` on a fresh object of the region. -/
def Wire.beq (a b : Wire) : MetaM Bool :=
  match a, b with
  | .rel x, .rel y => do
    if ← Meta.isDefEq x y then return true
    let some region := (← Meta.inferType x).getAppArgs[0]? | return false
    Meta.withLocalDeclD `a region fun o => do
      let (ox, _) ← mkAppMeta ``Freyd.Functor.obj #[← laneFunctor x, o]
      let (oy, _) ← mkAppMeta ``Freyd.Functor.obj #[← laneFunctor y, o]
      Meta.isDefEq ox oy
  | .timesL x, .timesL y => Meta.isDefEq x y
  | _, _ => return false

/-- The `Allegory` instance of a region, LOCAL one first.  A statement quantified over its own
    `[Allegory 𝒜]` has no global instance to find, and synthesising one with the hom universe still
    a level metavariable is what made `idRelator` unbuildable for an empty wire stack. -/
def allegoryInst (regionTy : Expr) : MetaM Expr := do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Freyd.Alg.Allegory 1 then
      if ← Meta.isDefEq t.appArg! regionTy then return d.toExpr
  -- Built with `mkAppMeta`, not `mkAppM`: an allegory's HOM universe is not fixed by its object
  -- type, so the class application still holds a level metavariable that instance search is the
  -- thing to solve — `mkAppM` refuses to hand back a term holding one.
  Meta.synthInstance (← mkAppMeta ``Freyd.Alg.Allegory #[regionTy]).1

/-- The `Cat` instance of a region, LOCAL one first — the same rule and the same reason as
    `allegoryInst`'s, a category quantified over in the statement having no global instance. -/
def catInst (regionTy : Expr) : MetaM Expr := do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Cat 1 then
      if ← Meta.isDefEq t.appArg! regionTy then return d.toExpr
  Meta.synthInstance (← mkAppMeta ``Cat #[regionTy]).1

/-- WHICH ALGEBRA OF LANES A REGION'S NATURALITY IS STATED IN, read off the region's own instances
    and never off a name.  An `Allegory` region's lanes are `Relator`s and its naturality is the
    `⊑`-graded family `StrictNatural`/`LaxNatural`/`OpLaxNatural`; a region that is only a `Cat` —
    §1.241's function category, where the `Vec` beads live — has `Freyd.Functor` lanes and exactly
    one naturality statement, the square, there being no `⊑` to grade it by. -/
inductive LaneAlg where | relator | functor
  deriving Inhabited, BEq

def laneAlgOf (regionTy : Expr) : MetaM LaneAlg :=
  try let _ ← allegoryInst regionTy; return .relator catch _ => return .functor

/-- What a lane of this algebra IS: the type a wire's own type must be headed by for the wire to be
    a lane of the region at all. -/
def LaneAlg.head : LaneAlg → Name
  | .relator => ``Freyd.Alg.Relator
  | .functor => ``Freyd.Functor

/-- Two lanes composed, in DIAGRAM order — `comp F G` is `F` then `G`, so `(comp F G).obj A` is
    `G.obj (F.obj A)` in both algebras. -/
def LaneAlg.comp (alg : LaneAlg) (F G : Expr) : MetaM Expr :=
  Meta.mkAppM (match alg with
    | .relator => ``Freyd.Alg.Relator.comp
    | .functor => ``Freyd.compFunctor) #[F, G]

/-- The identity lane of a region, built with the region's OWN instance rather than a level
    metavariable — the empty wire stack is a lane like any other and has to be nameable. -/
def LaneAlg.id (alg : LaneAlg) (regionTy : Expr) : MetaM Expr := do match alg with
  | .relator =>
    Meta.mkAppOptM ``Freyd.Alg.Relator.idRelator #[regionTy, some (← allegoryInst regionTy)]
  | .functor => Meta.mkAppOptM ``Freyd.idFunctor #[regionTy, some (← catInst regionTy)]

/-- The two halves of a PRODUCT region. -/
def prodRegions? (ty : Expr) : Option (Expr × Expr) :=
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) => some (a, b)
  | _ => none

/-- A fresh OBJECT of a region — a PAIR of fresh objects where the region is a product, because a
    projection out of a metavariable does not reduce and the unifier then cannot see through
    `(a,b).1` at all: it fails with no error, which is the peel that finds nothing. -/
partial def freshObj (ty : Expr) : MetaM Expr := do
  match prodRegions? ty with
  | some (a, b) => Meta.mkAppM ``Prod.mk #[← freshObj a, ← freshObj b]
  | none => Meta.mkFreshExprMVar (some ty)

/-- The two factors of a product object: `X` is `a × b` when the region's own product apex
    `relProd ?a ?b` unifies with it.  `none` where the region has no products at all.

    A `RelProd a b` GIVEN as a hypothesis is a product apex just as much as the region's chosen
    one — a tabulation of `⊤ : a ⟶ b` is what "product" means here — and it does not unify with
    `relProd ?a ?b`, being an arbitrary one.  Its factors are its TYPE's two arguments, which is
    the same rule the apex's delaborator prints by, so a statement quantified over `P : RelProd a b`
    reads as a product square everywhere rather than only where the chosen product was written. -/
def splitTimes? (regionTy X : Expr) : MetaM (Option (Expr × Expr)) := do
  if X.isAppOfArity ``Freyd.Alg.RelProd.p 5 then
    let t ← Meta.whnf (← Meta.inferType X.appArg!)
    if t.isAppOfArity ``Freyd.Alg.RelProd 4 then
      let args := t.getAppArgs
      return some (args[2]!, args[3]!)
  let s ← Meta.saveState
  try
    let a ← Meta.mkFreshExprMVar (some regionTy)
    let b ← Meta.mkFreshExprMVar (some regionTy)
    let (prod, _) ← mkAppMeta ``Freyd.Alg.HasRelProd.relProd #[a, b]
    let (apex, _) ← mkAppMeta ``Freyd.Alg.RelProd.p #[prod]
    if ← Meta.isDefEq apex X then
      let a ← instantiateMVars a
      let b ← instantiateMVars b
      if !a.hasExprMVar && !b.hasExprMVar then return some (a, b)
    s.restore; return none
  catch _ => s.restore; return none

def Wire.label : Wire → MetaM String
  | .rel r => relLabel r
  -- `(A×B)×−`, never `A×B×−`: a left factor that is itself a product must be bracketed or the
  -- label names a different lane.  The test is the product READER, not the printed string.
  | .timesL l => do
    let s ← plain l
    let par := (← splitTimes? (← Meta.inferType l) l).isSome
    return (if par then "(" ++ s ++ ")" else s) ++ "×−"

/-- The constants of the environment that ARE one `head` — a relator, a functor — and are a thing of
    the region rather than a COMBINATOR over the region: one that takes a `head` as an argument is
    excluded by its own type (`comp`, `prod`, `pair`, `Functor.comp`, `Relator.toFunctor`), so
    peeling with it would peel with an unknown, and `const`/`idRelator`/`idFunctor` are excluded at
    the peel by the progress test.  ONE copy of the sweep: the catalogues differ only in the heads. -/
def catalogueOf (head : Name) (excluded : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants do
    if n.isInternal || ci.isUnsafe || concHead ci.type != head then continue
    let s ← Meta.saveState
    let ok : Bool ← try
      let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
      let (args, _, concl) ← Meta.forallMetaTelescope
        (ci.type.instantiateLevelParams ci.levelParams lvls)
      let mut good := true
      for a in args do
        let ty ← instantiateMVars (← Meta.inferType a)
        if excluded.any ty.isAppOf then good := false
      pure (good && concl.getAppArgs.size ≥ 2)
    catch _ => pure false
    s.restore
    if ok then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

/-- The LANES the environment names: the relators of a region, and its functors.  A lane is a
    functor between regions with a bead for each arrow it carries, and a relator is one that is
    also monotone; `E` is the case that is not — `existsImage` has no `map_mono`, so the power
    object's lane in a region where `powerRelator` cannot be instantiated (an abstract allegory that
    is not tabular) is `existsImageFunctor` itself, and the note's `E` lane.  ONE sweep over the
    environment, threaded down: the read asks at every level of the term. -/
def catalogue : MetaM (Array Name) :=
  return (← catalogueOf ``Freyd.Alg.Relator #[``Freyd.Alg.Relator])
    ++ (← catalogueOf ``Freyd.Functor #[``Freyd.Functor, ``Freyd.Alg.Relator])

/-- The catalogue entry `n` instantiated at the region: fresh level metavariables, its argument
    telescope opened with metavariables, and every INSTANCE argument synthesised — one left standing
    is an unknown no later test can see, and the peel that silently finds nothing rather than
    failing.  `ends` is the test on the region arguments, asked FIRST because the instances are
    synthesised from those regions.  The state is the caller's: every refusal is `none` here and
    rolled back there. -/
def instCatalogue (n : Name) (ends : Array Expr → MetaM Bool) :
    MetaM (Option (Expr × Array Expr)) := do
  let some ci := (← getEnv).find? n | return none
  let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
  let (args, bis, concl) ← Meta.forallMetaTelescope
    (ci.type.instantiateLevelParams ci.levelParams lvls)
  let cargs := concl.getAppArgs
  unless ← ends cargs do return none
  for i in [0 : args.size] do
    unless bis[i]! == .instImplicit do continue
    let .mvar id := args[i]! | continue
    if ← id.isAssigned then continue
    let .some v ← Meta.trySynthInstance (← instantiateMVars (← id.getType)) | return none
    unless ← Meta.isDefEq args[i]! v do return none
  return some (mkAppN (mkConst n lvls) args, cargs)

/-- `X` as `R.obj a` for the catalogue entry `n`, or `none`.  Progress is required — a relator
    that gives back `X` itself peels nothing — and so is a fully determined answer, which is what
    keeps a relator with an undetermined parameter from matching anything. -/
def peelWith? (n : Name) (objVars : Array Expr) (regionTy X : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let s ← Meta.saveState
  try
    -- Only the wire's TARGET is the region being peeled: a wire is a functor between regions, and
    -- a bifunctor's is `𝒜×𝒜 ⟶ 𝒜`, so the peel goes on in whatever region the wire comes from.
    let some (R, cargs) ← instCatalogue n (fun c => Meta.isDefEq c[1]! regionTy)
      | s.restore; return none
    let src ← instantiateMVars cargs[0]!
    let inner ← freshObj src
    let (app, _) ← mkAppMeta ``Freyd.Functor.obj #[← laneFunctor R, inner]
    if ← Meta.isDefEq app X then
      let inner ← instantiateMVars inner
      let R ← instantiateMVars R
      let src ← instantiateMVars src
      -- A wire is a relator of the REGION, so it cannot mention an object the statement quantifies
      -- over: `F(A,−)` is a different functor at each `A` and no lane can carry it.
      if objVars.any (fun v => R.containsFVar v.fvarId!) then s.restore; return none
      if !inner.hasExprMVar && !R.hasExprMVar && !src.hasExprMVar && !(← Meta.isDefEq inner X) then
        return some (R, src, inner)
    s.restore; return none
  catch _ => s.restore; return none

/-- `e` as `G.map r` for the functor `g`, with `r` the arrow underneath.  The functor is the FIRST
    explicit argument of the projection, so the application is built with it already in place: an
    all-metavariable one cannot synthesise `Cat ?𝒞` and throws.  `none` ROLLS THE STATE BACK, so a
    candidate that does not fit leaves nothing for the next one.  Progress is required: `idFunctor`
    gives back `e` and peels nothing. -/
def mapOfFunctor? (g : Expr) (regionTy e : Expr) : MetaM (Option Expr) := do
  let s ← Meta.saveState
  try
    let x ← Meta.mkFreshExprMVar (some regionTy)
    let y ← Meta.mkFreshExprMVar (some regionTy)
    let r ← Meta.mkFreshExprMVar (some (← Meta.mkAppM ``Cat.Hom #[x, y]))
    let app ← Meta.mkAppM ``Freyd.Functor.map #[g, r]
    unless ← Meta.isDefEq app e do s.restore; return none
    let r ← instantiateMVars r
    if r.hasExprMVar || (← Meta.isDefEq r e) then s.restore; return none
    return some r
  catch _ => s.restore; return none

/-- The ARROW analogue of `peelWith?`: `e` as `F(r)` for the catalogue entry `n`, or `none`.  A
    lane's action on arrows has a name of its own in the environment — `list R`, `existsImage R`
    — and a picture must read those the way it reads `F.map R`, one wire running past a bead, or a
    whole composite under `F` comes out as one bead nobody can slide anything past.  Asked by
    `isDefEq` against `F.map ?r`, so every spelling of the action answers, and progress is required
    for the same reason it is there: `idRelator.map` gives back `e` and peels nothing.
    `Λ S = 𝟙%∋ ≫ E(S)` is B&dM's factorisation, drawn as the unit bead and `S`'s own bead on `E`. -/
def peelMapWith? (n : Name) (objVars : Array Expr) (regionTy e : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let s ← Meta.saveState
  try
    -- An ENDOFUNCTOR of the region, both ends: the bead's own lanes are what runs past it, and a
    -- wire out of another region has none of them to run on.  A relator's and a functor's two type
    -- arguments alike are its two regions.
    let ends : Array Expr → MetaM Bool := fun c => do
      let lo ← Meta.isDefEq c[0]! regionTy
      let hi ← Meta.isDefEq c[1]! regionTy
      return lo && hi
    let some (R, _) ← instCatalogue n ends | s.restore; return none
    let R ← instantiateMVars R
    if R.hasExprMVar || objVars.any (fun v => R.containsFVar v.fvarId!) then s.restore; return none
    if let some r ← mapOfFunctor? (← laneFunctor R) regionTy e then return some (R, r)
    s.restore; return none
  catch _ => s.restore; return none

/-- The first catalogue lane `e` is the action of, and the arrow underneath. -/
def peelMap? (cat : Array Name) (objVars : Array Expr) (regionTy e : Expr) :
    MetaM (Option (Expr × Expr)) :=
  cat.findSomeM? fun n => peelMapWith? n objVars regionTy e

/-- An object peeled into its wire stack (outermost first), each wire with the OBJECT UNDER IT, and
    the object underneath them all.  The object under a wire is what a bead taken there is a family
    AT: `𝟙%∋` at `F A` is `singletonMap (F A)`, and `F A` is the cut the `F` lane stands over.

    A PRODUCT `A×Y` is the ONE lane `A×−` over the lanes of `Y`, whatever `A` is.  `×` is a functor
    out of `𝒜×𝒜` and Hinze–Marsden has no wire for one, so the left factor cannot be drawn as a
    bundle beside its sibling; it is pinned into the endofunctor `A×−` at that object, and only the
    right factor goes on being peeled. -/
partial def peelCuts (objVars : Array Expr) (cat : Array Name) (regionTy X : Expr) :
    MetaM (Array (Wire × Expr) × Expr) := do
  match X.getAppFnArgs with
  | (``Freyd.Functor.obj, args) =>
    if let some (f, x) := lastTwo args then
      let (cs, o) ← peelCuts objVars cat regionTy x
      -- `wiresOf` is outermost first, so the objects are built from the inside out: under the
      -- innermost wire is `x`, under the next is that wire applied to it.
      let ws := wiresOf f
      let mut under := x
      let mut acc : Array (Wire × Expr) := #[]
      for i in [0 : ws.size] do
        let w := ws[ws.size - 1 - i]!
        acc := acc.push (Wire.rel w, under)
        if i + 1 < ws.size then
          under := (← mkAppMeta ``Freyd.Functor.obj #[← laneFunctor w, under]).1
      return (acc.reverse ++ cs, o)
  | _ => pure ()
  if let some (a, b) ← splitTimes? regionTy X then
    let (cs, o) ← peelCuts objVars cat regionTy b
    return (#[(Wire.timesL a, b)] ++ cs, o)
  for n in cat do
    if let some (R, src, inner) ← peelWith? n objVars regionTy X then
      let (cs, o) ← peelCuts objVars cat src inner
      return (#[(Wire.rel R, inner)] ++ cs, o)
  return (#[], X)

/-- An OBJECT read as a RELATOR in `v` — the one reader every naturality statement is built from.

    A bead's naturality is a statement about the family `fun v => core`, so its two relators are
    that family's two END OBJECTS as functions of `v`, and nothing else: a LANE LABEL is never
    consulted.  The reading is structural, and total on the object formers the peel knows:

    * `X` free of `v` — `Relator.const X`, whose `map` is `𝟙 X`.  A bead with a CONSTANT end (`nil`,
      whose source is the one-point schedule) is a family like any other; it is not the identity
      relator, and reading it as one is what left `nil` with no statement to look for.
    * `v` itself — the identity relator.
    * `A × B` — the product of the two readings, so a left factor that MENTIONS `v` (`[v]×[[v]]`,
      the source of `cons`) is read too, where pinning it into a constant `A×−` could not be.
    * `F(X)` — `F` after the reading of `X`, `F` peeled off by the same catalogue the lanes use.

    WHICH ALGEBRA THE READING IS BUILT IN IS THE REGION'S, `laneAlgOf`: an allegory's lanes are
    `Relator`s, a bare category's are `Freyd.Functor`s, and the two compose by their own `comp`.
    `Vec n` is a functor of §1.241's function category and no relator, so a reading fixed to
    `Relator.comp` failed on `(Vec n).obj A` and demoted every `Vec` family to an object-wire bead.
    Only `𝟙` and composition are named in the functor algebra — the repo has no constant or product
    functor — so a constant or product end has no reading THERE, exactly as an end no relator spells
    has none here.

    Anything else mentioning `v` has no reading, and the bead it belongs to gets no verdict: it is
    refused here rather than being silently read as something it is not. -/
partial def relatorOfObj (alg : LaneAlg) (cat : Array Name) (regionTy v X : Expr) : MetaM Expr := do
  let .fvar vid := v | throwError "the family variable {← Meta.ppExpr v} is not a local"
  if !X.containsFVar vid then
    unless alg == .relator do
      throwError "the end {← Meta.ppExpr X} does not vary with {← Meta.ppExpr v} and \
        {← Meta.ppExpr regionTy} is no allegory, so there is no constant lane to read it as"
    let inst ← allegoryInst regionTy
    return ← Meta.mkAppOptM ``Freyd.Alg.Relator.const
      #[some regionTy, some regionTy, some inst, some inst, some X]
  -- `isDefEq`, not `==`: where the region is a one-field structure over an index, the object comes
  -- back rebuilt from its projection (`⟨a.f⟩`), which is `a` only up to eta.
  if ← Meta.isDefEq X v then return ← alg.id regionTy
  if let some (a, b) ← splitTimes? regionTy X then
    unless alg == .relator do
      throwError "the end {← Meta.ppExpr X} is a product and {← Meta.ppExpr regionTy} is no \
        allegory, so there is no product lane to read it as"
    return ← Meta.mkAppM ``Freyd.Alg.Relator.prod
      #[← relatorOfObj alg cat regionTy v a, ← relatorOfObj alg cat regionTy v b]
  match X.getAppFnArgs with
  | (``Freyd.Functor.obj, args) =>
    if let some (f, x) := lastTwo args then
      let ws := wiresOf f
      if ws.any (·.containsFVar vid) then
        throwError "the wire {← Meta.ppExpr f} varies with {← Meta.ppExpr v}, so it is no lane \
          of the region and {← Meta.ppExpr X} has no reading"
      let mut acc ← relatorOfObj alg cat regionTy v x
      for i in [0 : ws.size] do
        acc ← alg.comp acc ws[ws.size - 1 - i]!
      return acc
  | _ => pure ()
  -- `#[v]`: the wire peeled off has to be a lane of the REGION, so one that mentions `v` is no
  -- reading of `X` at all — refusing it here is both the correctness rule and what keeps the peel
  -- from ranging over the whole catalogue at every level.  A FUNCTOR lane (`E`) is no relator, so
  -- in an allegory a family under it states no naturality in the relator sense and is refused
  -- below; in the function category the functor IS the lane and the same test admits it.
  for n in cat do
    if let some (R, src, inner) ← peelWith? n #[v] regionTy X then
      unless (← Meta.inferType R).isAppOf alg.head do continue
      return ← alg.comp (← relatorOfObj alg cat src v inner) R
  throwError "the object {← Meta.ppExpr X} varies with {← Meta.ppExpr v} in a way no lane of \
    {← Meta.ppExpr regionTy} spells, so the bead over it states no naturality"

/-- HOW THE TWO SIDES OF A NATURALITY SQUARE ARE JOINED: an equality (`StrictNatural`), `⊑`
    (`LaxNatural`), or `⊑` the other way round (`OpLaxNatural`).  The three a family can be graded
    by, and nothing else — a spider is the absence of all three, not a fourth. -/
inductive Grade where | strict | lax | oplax
  deriving Inhabited, BEq

/-- THE NATURALITY SQUARE OF A FAMILY BETWEEN LANES, as a proposition.  `φ a : G.obj a ⟶ F.obj a`,
    so naturality is `G.map f ≫ φ y ∼ φ x ≫ F.map f` for every arrow `f : x ⟶ y` of the region,
    with `∼` the `grade` — the very statement `gen_natural`, `genFold_natural`, `moves_lax_natural`
    and their siblings are written in.  Built and not named, so any pair of lanes states it in
    either algebra: an allegory's lanes are relators and act by `Relator.map`, a bare category's
    are functors and act by `Functor.map`, and a category has only `.strict` to grade a square by.

    `onMaps` restricts `f` to the MAPS, which is the same square read in the sub-category the maps
    of an allegory form.  A FUNCTOR lane in an allegory (`E`, the existential image) carries
    families that are natural there and nowhere else — `singletonMap_natural` is `f ≫ 𝟙%∋ =
    𝟙%∋ ≫ E(f)` for a map `f`, and at a relation both directions fail — so the square without the
    hypothesis is the wrong question to ask of them, not a stronger one they happen to miss. -/
def laneSquare (alg : LaneAlg) (regionTy F G φ : Expr) (grade : Grade := .strict)
    (onMaps : Bool := false) : MetaM Expr := do
  -- A STACK'S ACTION IS ITS WIRES' ACTIONS, INNERMOST FIRST — `(Vec(m+1)).map ((Vec n).map f)`,
  -- `tupleP 3 (tupleP n S)`, the very spelling every naturality theorem in the repo is written in.
  -- Composing the stack into one `compFunctor`/`Relator.comp` and taking ITS `map` is the same
  -- arrow but a different TERM, and the unification then has to see through the composite at every
  -- level, which is where the searches for `genFold_natural` and for every `RelSet.graph` bead of
  -- the cylinder came back empty.  `wiresOf` is outermost first, so it is applied in reverse.
  -- A RELATOR ACTS BY THE FUNCTOR IT EXTENDS: `Relator` has no `map` of its own, so `F.map R` IS
  -- `Functor.map F.toFunctor R` — the spelling `LaxNatural`'s own body elaborates to.
  let act (w f : Expr) : MetaM Expr := do
    let w ← match alg with
      | .relator => Meta.mkAppM ``Freyd.Alg.Relator.toFunctor #[w]
      | .functor => pure w
    Meta.mkAppM ``Freyd.Functor.map #[w, f]
  let apply (ws : Array Expr) (f : Expr) : MetaM Expr := do
    let mut acc := f
    for i in [0 : ws.size] do acc ← act ws[ws.size - 1 - i]! acc
    return acc
  Meta.withLocalDeclD `x regionTy fun x => Meta.withLocalDeclD `y regionTy fun y => do
    Meta.withLocalDeclD `f (← Meta.mkAppM ``Cat.Hom #[x, y]) fun f => do
      let l ← Meta.mkAppM ``Cat.comp #[← apply (wiresOf G) f, (mkApp φ y).headBeta]
      let r ← Meta.mkAppM ``Cat.comp #[(mkApp φ x).headBeta, ← apply (wiresOf F) f]
      let sq ← match grade with
        | .strict => Meta.mkEq l r
        | .lax => Meta.mkAppM ``Freyd.Alg.le #[l, r]
        | .oplax => Meta.mkAppM ``Freyd.Alg.le #[r, l]
      if !onMaps then return ← Meta.mkForallFVars #[x, y, f] sq
      Meta.withLocalDeclD `hf (← Meta.mkAppM ``Freyd.Alg.Map #[f]) fun hf =>
        Meta.mkForallFVars #[x, y, f, hf] sq

/-- The two ends of an arrow.

    A CONCRETE REGION'S HOM IS A FUNCTION TYPE, so an arrow built from a core combinator — the
    product bifunctor's arrow part `Prod.map f g`, `id`, anything else typed before the category
    was — carries `α → β` and no `Cat.Hom` for `homObjs?` to read.  Its ends are then the function
    type's, and only where that type IS the region's own hom: the `Cat` instance decides, by
    `isDefEq` against `Cat.Hom`, so every such arrow answers rather than a listed few. -/
def homEnds (e : Expr) : MetaM (Expr × Expr) := do
  let t ← Meta.inferType e
  if let some p := homObjs? t then return p
  if let .forallE _ a b _ := t then
    if !b.hasLooseBVars && (← isObjType (← Meta.inferType a)) then
      if ← Meta.isDefEq t (← Meta.mkAppM ``Cat.Hom #[a, b]) then return (a, b)
  throwError "not an arrow of a category: {← Meta.ppExpr e}"

/-- A declaration's binders and its STATEMENT — `Meta.forallTelescopeReducing`, stopped at an arrow.
    A hom of `RelSet` is definitionally `A → B → Prop`, so reducing walks straight through the arrow
    an arrow-valued `def` IS and hands back `Prop`, with the def's own two elements as binders; the
    walk stops where `homObjs?` reads a hom off the head constant, before anything unfolds it.  A
    statement is no hom, so a theorem's telescope is the reducing one's, binder for binder. -/
partial def stmtTelescope [Inhabited α] (ty : Expr) (k : Array Expr → Expr → MetaM α)
    (xs : Array Expr := #[]) : MetaM α := do
  if (homObjs? ty).isSome then return ← k xs ty
  -- `whnf` only where the walk is STUCK, and hand `k` the type it was stuck on — both as
  -- `forallTelescopeReducing` does.  Reducing a statement that is already a `∀`, or the statement
  -- the walk ends on, unfolds the named predicate the panel is drawn from.
  let peeled ← if ty.isForall then pure ty else Meta.whnf ty
  match peeled with
  | .forallE n d b bi =>
    Meta.withLocalDecl n bi d fun x => stmtTelescope (b.instantiate1 x) k (xs.push x)
  | _ => k xs ty

/-- Is this arrow an identity? -/
def isIdArrow (e : Expr) : MetaM Bool := do
  let (x, y) ← homEnds e
  if !(← Meta.isDefEq x y) then return false
  Meta.isDefEq e (← Meta.mkAppM ``Cat.id #[x])

/-- A PRODUCT MAP, recognised by its TYPE and nothing else: a constant applied to exactly two
    arrows `φ : a ⟶ a'`, `ψ : b ⟶ b'` whose own two ends are the products of those ends.  That
    type has only one inhabitant a picture can mean, so no name is needed — and it is what says
    which lanes the factor touches, where comparing the two wire stacks cannot: `cons` and
    `secure×𝟙` have the same stacks below them and eat wholly different wires. -/
def asProdMap? (regionTy : Expr) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let .const _ _ := e.getAppFn | return none
  let args := e.getAppArgs
  let mut arrows : Array Expr := #[]
  for a in args do
    if (homObjs? (← Meta.inferType a)).isSome then arrows := arrows.push a
  unless arrows.size == 2 do return none
  let (x, y) ← homEnds e
  let some (a, b) ← splitTimes? regionTy x | return none
  let some (a', b') ← splitTimes? regionTy y | return none
  let (φa, φa') ← homEnds arrows[0]!
  let (ψb, ψb') ← homEnds arrows[1]!
  unless (← Meta.isDefEq a φa) && (← Meta.isDefEq a' φa')
      && (← Meta.isDefEq b ψb) && (← Meta.isDefEq b' ψb') do return none
  return some (arrows[0]!, arrows[1]!)

/-- A factor with the relators it runs UNDER stripped off: `F.map (G.map R)` is `R` with the wires
    `F`, `G` running past it.  Outermost first. -/
partial def peelMap (e : Expr) : Array Expr × Expr :=
  match e.getAppFnArgs with
  | (``Freyd.Functor.map, args) =>
    if args.size ≥ 6 then
      let (ws, r) := peelMap args[args.size - 1]!
      (wiresOf args[4]! ++ ws, r)
    else (#[], e)
  | _ => (#[], e)

/-- The two OPERANDS of a binary operation on ONE hom — a union, a meet.  Recognised by its TYPE:
    an application whose last two arguments are arrows of the same hom as the whole.  A composite
    is not one, its own ends being the two OUTER objects rather than either factor's. -/
def binOperands? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let t ← Meta.inferType e
  if (homObjs? t).isNone || e.isAppOf ``Cat.comp then return none
  let some (l, r) := lastTwo e.getAppArgs | return none
  unless (← Meta.isDefEq (← Meta.inferType l) t) && (← Meta.isDefEq (← Meta.inferType r) t) do
    return none
  return some (l, r)

/-- The SYMBOL and the two operands of a JOIN: a `@[diag_join]` operator applied to two arrows of
    the whole's own hom.  Both halves are needed — the attribute says which operator draws as two
    panels, `binOperands?` that this application of it is the binary one and not a section of it —
    and the MEET, whose type is the same to the letter, is not tagged and stays one bead. -/
def joinOperands? (e : Expr) : MetaM (Option (String × Expr × Expr)) := do
  let some n := e.getAppFn.constName? | return none
  let some sym := (diagJoinExt.getState (← getEnv)).find? n | return none
  let some (l, r) ← binOperands? e | return none
  return some (sym, l, r)

/-- A composite flattened into its factors, in diagram order. -/
partial def factors (e : Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``Cat.comp, args) => match lastTwo args with
    | some (f, g) => factors f ++ factors g
    | none => #[e]
  | _ => #[e]

/-- A term whose head the NOTE writes as its BODY, opened; anything else unchanged.  Which heads is
    `@[diag_unfold]`'s answer — set beside the declaration, or in `diag/StrDiagNames.lean` where the
    declaration is not the diagram's to edit — so no picture functor carries a list of names.  The
    mirror of `diag_induced`: that one says a name is KEPT and dashed, this one that it is opened. -/
def openNoted (e : Expr) : MetaM Expr := do
  let .const n _ := e.getAppFn | return e
  unless (← Lean.labelled `diag_unfold).contains n do return e
  match ← Meta.unfoldDefinition? e with
  | some v => return v.headBeta
  | none => return e

/-- The same answer WHEREVER the name is spelled, not only at the head: an operator applied to a
    definition the note writes out — `arm₂ β`, the algebra restricted to one summand — leaves the
    name nested, and a name left standing there is the same defect as one left standing on top. -/
def openNotedAll (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    let x' ← openNoted x
    return if x' == x then .continue else .done x')

/-- One `diag_rewrite` step: `e` rewritten to the right side of the first equation whose left side it
    IS, or `none`; the state is threaded by the caller.  THE HEAD TEST IS THE TERMINATION ARGUMENT:
    matching is `isDefEq`, which UNFOLDS, so `Λ ?R =?= singletonMap` would unfold `singletonMap` to
    `Λ (𝟙 a)` and rewrite for ever — while the equation fires only where the node's head constant is
    the left side's, the left sides' heads being different from one another. -/
def rewriteHead? (e : Expr) : MetaM (Option Expr) := do
  let some n := e.getAppFn.constName? | return none
  for thm in (← Lean.labelled `diag_rewrite) do
    let some ci := (← getEnv).find? thm | continue
    let s ← Meta.saveState
    let mut out : Option Expr := none
    try
      let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
      let (_, _, concl) ← Meta.forallMetaTelescope
        (ci.type.instantiateLevelParams ci.levelParams lvls)
      let cargs := concl.getAppArgs
      if concl.isAppOf ``Eq && cargs.size ≥ 3 && cargs[1]!.getAppFn.constName? == some n then
        if ← Meta.withReducible (Meta.isDefEq cargs[1]! e) then
          -- An equation whose right side the match leaves undetermined says nothing about `e`: a
          -- metavariable left in the picture is a wire with no object under it.
          let rhs ← instantiateMVars cargs[2]!
          if !rhs.hasMVar then out := some rhs
    catch _ => pure ()
    s.restore
    if let some x := out then return some x
  return none

/-- A side rewritten along its composite SPINE by the `diag_rewrite` equations: `Λ S` is drawn as the
    unit bead `𝟙%∋` and `S` on the `E` lane, but a `Λ` inside a fold's body is that bead's own label
    and stays.  The spine is what `Cat.comp` joins; a fold's body, a junction's arms and an `est(R)`
    argument are LEAVES of it and are never entered.

    `fuel` bounds the rewrites at ONE node, each of which yields a fresh node to rewrite (`Λ S` yields
    `singletonMap ≫ E(S)`, a composite), and the head test above is what stops the run: the fuel only
    makes that stop something stated rather than hoped for. -/
partial def rewriteSpine (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  -- The operands first, so a `Λ 𝟙` anywhere on the spine folds back to the unit bead like one at
  -- its head.  Nothing below a `Cat.comp` node is entered.
  let e ← match e.getAppFnArgs with
    | (``Cat.comp, args) =>
      if let some (f, g) := lastTwo args then
        let f' ← rewriteSpine f fuel
        let g' ← rewriteSpine g fuel
        pure (mkAppN e.getAppFn ((args.extract 0 (args.size - 2)).push f' |>.push g'))
      else pure e
    | _ => pure e
  match ← rewriteHead? e with
  | none => return e
  | some r =>
    if fuel == 0 then throwError "diag_rewrite does not terminate on {← Meta.ppExpr e}"
    else rewriteSpine r (fuel - 1)

/-- A statement built from two STATEMENTS, and those two.  A different question from `split`, which
    reads the relation between two ARROWS: a side of one of these is itself a statement, so it
    draws no panel of its own and a selector has to go on through it. -/
def conn? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Iff, args) | (``And, args) => lastTwo args
  | _ => none

/-- The relation between the two sides of a statement, and the sides.  ONE copy: the string, the
    circuit and the commutative functors and the proof walk all ask this same question of a head. -/
def split (e : Expr) : Option (String × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Freyd.Alg.le, args) => (lastTwo args).map fun (l, r) => ("⊑", l, r)
  | (``LE.le, args) => (lastTwo args).map fun (l, r) => ("≤", l, r)
  | (``Eq, args) => (lastTwo args).map fun (l, r) => ("=", l, r)
  | _ => none

/-- `split`, retrying once through the definition of a named predicate.  `Total (R ∩ S)` is a `Prop`
    with no sides until `Total` is unfolded; then it is `𝟙 ≤ (R ∩ S);(R ∩ S)°` and draws.

    ONE delta step, never `whnf`: `whnf` keeps going past `LE.le` into the `OrderedCat` projection it
    is a field of, and the whole inequation collapses into one opaque box. -/
def splitM (e : Expr) : MetaM (Option (String × Expr × Expr)) := do
  if let some r := split e then return some r
  let .const n us := e.getAppFn | return none
  let some ci := (← getEnv).find? n | return none
  let some v := ci.value? | return none
  return split ((mkAppN (v.instantiateLevelParams ci.levelParams us) e.getAppArgs).headBeta)

/-! ### One branch of a side

  A statement's side can be a BINARY OPERATION on arrows, and then a panel may draw one operand of
  it: `.inl`/`.inr` on a route names which.  Which operation it is is read off the run's own type —
  a union or a meet by its two arrows of the SAME hom, a junction by the `Coproduct` it is over. -/

/-- A factor as a JUNCTION over a coproduct: `junc C X Y`, under whatever definition spells it —
    `sumMap C D R S` is `junc C (R ≫ D.u₁) (S ≫ D.u₂)`, the same fork behind another name.  Delta
    on the head constant only, so nothing below the junction is opened. -/
partial def juncOf? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if e.isAppOf ``Freyd.Alg.junc then
    let args := e.getAppArgs
    if args.size ≥ 3 then
      return some (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)
  match ← Meta.unfoldDefinition? e with
  | some e' => juncOf? e'
  | none => return none

/-- The apex and the two SUMMANDS of a coproduct, read off the TYPE `Coproduct s a₁ a₂` of its
    structure — the only place they are written, and no argument of the junction. -/
def summands? (C : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let t ← Meta.inferType C
  unless t.isAppOf ``Freyd.Alg.Coproduct do return none
  let args := t.getAppArgs
  if args.size < 3 then return none
  return some (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)

/-- A SUM MAP, recognised by its TYPE exactly as `asProdMap?` recognises a product map: a constant
    applied to exactly two arrows and exactly two coproducts, each arrow running from a summand of
    the first to the matching summand of the second.  That type has only one inhabitant a picture
    can mean, so no name is needed, and the note writes it `R+S`.  The co-fork `junc C X Y` is not
    one — it stands over ONE coproduct, its two arrows running into a single object. -/
def asSumMap? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let .const _ _ := e.getAppFn | return none
  let mut arrows : Array Expr := #[]
  let mut cops : Array Expr := #[]
  for a in e.getAppArgs do
    let t ← Meta.inferType a
    if (homObjs? t).isSome then arrows := arrows.push a
    else if t.isAppOf ``Freyd.Alg.Coproduct then cops := cops.push a
  unless arrows.size == 2 && cops.size == 2 do return none
  let some (_, a₁, a₂) ← summands? cops[0]! | return none
  let some (_, b₁, b₂) ← summands? cops[1]! | return none
  let (φa, φb) ← homEnds arrows[0]!
  let (ψa, ψb) ← homEnds arrows[1]!
  unless (← Meta.isDefEq a₁ φa) && (← Meta.isDefEq b₁ φb)
      && (← Meta.isDefEq a₂ ψa) && (← Meta.isDefEq b₂ ψb) do return none
  return some (arrows[0]!, arrows[1]!)

/-- A factor as a functor's action on an arrow, `F.map R`. -/
def functorMap? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Freyd.Functor.map, args) =>
    if args.size ≥ 6 then some (args[4]!, args[args.size - 1]!) else none
  | _ => none

/-- What a functor does to ONE summand.  The summand's own PRODUCT structure says it, and nothing
    else has to be known about the functor: the summand IS `R`'s source and the action is `R`, or it
    is a product and the action is `𝟙×` the action on its right factor — the slot the recursion sits
    in.  `𝟏` and any other summand not built over `R`'s source is untouched, and the answer is
    `none`: that arm carries no action at all, which is what leaves the leaf arm bare.

    The product map is the ALLEGORY's own `prodMap` over the region's own products, so which lanes
    it touches is settled where every other factor's are — by `asProdMap?`, off the type. -/
partial def summandAction (regionTy a R : Expr) : MetaM (Option Expr) := do
  let (rs, _) ← homEnds R
  if ← Meta.isDefEq a rs then return some R
  let some (l, r) ← splitTimes? regionTy a | return none
  let some act ← summandAction regionTy r R | return none
  let (_, aTgt) ← homEnds act
  let (P, _) ← mkAppMeta ``Freyd.Alg.HasRelProd.relProd #[l, r]
  let (Q, _) ← mkAppMeta ``Freyd.Alg.HasRelProd.relProd #[l, aTgt]
  return some (← instantiateMVars
    (← Meta.mkAppM ``Freyd.Alg.prodMap #[P, Q, ← Meta.mkAppM ``Cat.id #[l], act]))

/-- A run rebuilt from its factors, in diagram order. -/
def compose (fs : Array Expr) : MetaM Expr := do
  let mut acc := fs[0]!
  for i in [1 : fs.size] do acc ← Meta.mkAppM ``Cat.comp #[acc, fs[i]!]
  return acc

/-- ONE OPERAND of the binary operation a side is, `i` naming which.  What that operation is comes
    from the run's own type, never from a spelling:

    * the last factor is a UNION or a MEET — two arrows of the same hom as itself — and the operand
      keeps the run before it: `X ≫ (U ∪ V)` selects `X ≫ V`, a bare `U ∪ V` selects `V`;
    * the run starts at the apex of a COPRODUCT and ends in a junction over it, and the operand is
      one ARM.  The whole run is precomposed with that summand's injection, and
      `uᵢ ≫ F.map R ≫ junc C g h` is `Fᵢ(R) ≫ hᵢ`: the injection slides through the functor into
      the summand's own action, and the junction absorbs it.

    Selectors chain — `.inr.inr` is the arm, and then that arm's operand. -/
def branchOf (regionTy e : Expr) (i : Nat) : MetaM Expr := do
  let fs := factors e
  if let some (l, r) ← binOperands? fs[fs.size - 1]! then
    return ← compose ((fs.extract 0 (fs.size - 1)).push (if i == 0 then l else r))
  let (src, _) ← homEnds e
  let mut hit : Option (Nat × Expr × Expr × Expr × Expr) := none
  for k in [0 : fs.size] do
    if hit.isNone then
      if let some (C, X, Y) ← juncOf? fs[k]! then
        if let some (s, a₁, a₂) ← summands? C then
          if ← Meta.isDefEq s src then hit := some (k, a₁, a₂, X, Y)
  let some (j, a₁, a₂, X, Y) := hit
    | throwError "`.inl`/`.inr` names one operand of a union or a meet, or one arm of a junction \
        over a coproduct at the source of the run, and `{← plain e}` runs into neither"
  let mut parts : Array Expr := #[]
  let mut obj := if i == 0 then a₁ else a₂
  for k in [0 : j] do
    let some (_, R) := functorMap? fs[k]!
      | throwError "the arm is behind `{← plain fs[k]!}`, which is not a functor acting on an \
          arrow, so the injection has nothing to slide through"
    if let some act ← summandAction regionTy obj R then
      parts := parts.push act
      obj := (← homEnds act).2
  let arm := if i == 0 then X else Y
  let (armSrc, _) ← homEnds arm
  unless ← Meta.isDefEq armSrc obj do
    throwError "the arm `{← plain arm}` starts at `{← plain armSrc}`, and the run carries the \
      summand `{← plain obj}` into it"
  parts := parts.push arm
  for k in [j + 1 : fs.size] do parts := parts.push fs[k]!
  compose parts

/-! ### The dot

  A bead between the wire stack `G` (what it eats) and `F` (what it makes) is a 2-cell only if a
  DECLARATION says so.  The search is over the environment: a constant whose type, under its `∀`
  binders, is one of the three propositions the bead could satisfy, unified against the wanted one.
  Filtering first on the constants the family mentions keeps it to a handful of candidates. -/

/-- Every constant a term is built from — the cheap filter that says which declarations could
    possibly be about this bead. -/
partial def consts (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .app f a => consts a (consts f acc)
  | .lam _ t b _ | .forallE _ t b _ => consts b (consts t acc)
  | .const n _ => acc.insert n
  | .mdata _ b | .proj _ _ b => consts b acc
  | .letE _ t v b _ => consts b (consts v (consts t acc))
  | _ => acc

/-- THE CANDIDATE INDEX: for each conclusion head, the declarations concluding in it and the
    constants each one's statement uses — the two things a search selects candidates by.  Built
    once per head and held for the life of the process, because the environment does not grow
    while the exporter draws: a walk over `env.constants` per lookup redoes this work on every
    call, and the walk alone measured 5.8M of the 8.1M heartbeats one `Membership.mem` search
    spent (190180 constants examined to reach 275 candidates), with a dozen such calls per bead. -/
initialize headBuckets : IO.Ref (NameMap (Array (Name × NameSet))) ← IO.mkRef {}

/-- The declarations that could prove a statement headed by `head`, each with the constants its own
    statement uses.  The environment is asked for the Expr itself (`env.find?` at the one candidate
    being tried), never for the enumeration. -/
def candidates (head : Name) : MetaM (Array (Name × NameSet)) := do
  if let some b := (← headBuckets.get).find? head then return b
  let env ← getEnv
  let mut b : Array (Name × NameSet) := #[]
  for (n, ci) in env.constants do
    if n.isInternal || ci.isUnsafe || concHead ci.type != head then continue
    b := b.push (n, consts ci.type)
  headBuckets.modify (·.insert head b)
  return b

/-- One candidate's share of the search. Unifying a square against a concrete region unfolds every
    relator on both sides, which costs more than a whole default budget, so this is twice the
    default rather than a fraction of it; the head and `must` filters are what keep the scan short. -/
def CANDIDATE_HEARTBEATS : Nat := 400000

/-- The SPELLING BRIDGES, read by their ATTRIBUTE and never by a lemma name: `@[diag_bridge]` is
    what the repo declares an equation between two spellings of one arrow with, and the tool asks
    the environment which those are.  A closure theorem written in the abstract `prodMap` and a
    van square written in the book's `R×S` are then one statement to the search — and the proof it
    builds is carried back across the same bridge, so nothing is believed that is not proved. -/
def bridges : MetaM Meta.Simp.Context := do
  let some ext ← Meta.getSimpExtension? `diag_bridge
    | throwError "no `diag_bridge` simp set — the spelling bridges are declared by that attribute \
        (`register_simp_attr diag_bridge`, AOP/A5_1.lean); without it a bead's statement and a \
        candidate's cannot be compared"
  Meta.Simp.mkContext (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← Meta.getSimpCongrTheorems)

/-- One proposition normalised through the bridges: the rewritten form, and the proof that it is
    the one asked for. -/
def bridge (br : Meta.Simp.Context) (e : Expr) : MetaM Meta.Simp.Result := Prod.fst <$> Meta.simp e br

/-- What a candidate for a naturality proposition must MENTION: the constants of the family it is
    about, ACROSS THE BRIDGES — the same normal form the two propositions are compared in, because
    a filter read in the panel's spelling (`Λ 𝟙`) and a candidate written in the theorem's
    (`singletonMap`) never overlap, and the candidate is dropped before the comparison that would
    have seen through them. The region's own projections and every INSTANCE go: a term carries the
    path typeclass resolution took to the region's structure and a theorem's context takes another,
    so requiring either is requiring what no theorem can have.

    KEEPING THE OBJECTS IS WHAT MAKES THE SEARCH FINITE IN PRACTICE.  Narrowing this to the ARROWS
    of the family — dropping the objects they are taken at, which is what a naturality theorem is
    general in — is the reading the statement wants, and it opens the square search to every
    equation of the environment: on `prefix_cancel.lhs` that reaches the 12 GB the exporter runs
    under (`scripts/cap`) and the process dies.

    WHAT IS DROPPED IS DECIDED BY THE CONSTANT'S OWN CONCLUSION, NOT BY ITS KIND.  Dropping every
    PROJECTION dropped the field that names the arrow along with the path: `∋` is the three
    constants `UnguardedPowerLCDA.toUnguardedPowerAllegory`, `UnguardedPowerAllegory.toPowerAllegory`
    and `PowerAllegory.eps`, and the last of those IS `∋` — the one name every theorem about `∋`
    must carry.  With it gone `must` was EMPTY, so the square search ran over every `Eq`-headed
    declaration in the environment and `discharge` ran another over every one of those: measured at
    85M heartbeats for the first level and 91M for the second, past the budget before the third.
    A conclusion that is a CLASS is the resolution path, which each declaration takes its own way;
    a conclusion that is no constant at all is a type former, carried in types a statement never
    prints.  Everything else a theorem can be asked for by name. -/
def mustOfFamily (br : Meta.Simp.Context) (φ : Expr) : MetaM NameSet := do
  let env ← getEnv
  let mut out : NameSet := {}
  for n in (consts (← bridge br φ).expr).toList do
    if let some ci := env.find? n then
      let h := concHead ci.type
      if h.isAnonymous || Lean.isClass env h then continue
    out := out.insert n
  return out

/-- The same filter for a naturality PROPOSITION: its last argument is the family, and a `¬` is
    stripped first — refuting a family is a statement about that same family. -/
def mustOf (br : Meta.Simp.Context) (want : Expr) : MetaM NameSet := do
  let p := match want.getAppFnArgs with | (``Not, #[q]) => q | _ => want
  let some φ := p.getAppArgs.back? | return consts want
  mustOfFamily br φ

/-- A candidate becomes a VERDICT only as a proof that CHECKS.  `pf` proves the candidate's own
    conclusion `rc.expr`; `rw` is the wanted proposition's own trip across the bridges, so
    `mkEqMPR` lands the term back on `want` itself, and `check` re-elaborates it from nothing. -/
def checked (want : Expr) (rw rc : Meta.Simp.Result) (n : Name) (pf : Expr) :
    MetaM (Option (Name × Expr)) := do
  let proof ← instantiateMVars (← rw.mkEqMPR (← rc.mkEqMP pf))
  if proof.hasExprMVar then return none
  Meta.check proof
  unless ← Meta.isDefEq (← Meta.inferType proof) want do return none
  return some (n, proof)

/-- `a = b` read the other way round.  Not `Eq.symm` applied to a proof — the STATEMENT, so the
    search can look for the mirrored square; anything but an equation has no mirror. -/
def flipEq? (e : Expr) : MetaM (Option Expr) := do
  let some (_, l, r) := e.eq? | return none
  return some (← Meta.mkEq r l)

/-- Whether a head may be searched with NO filter: a DEFINED predicate (`StrictNatural`,
    `PreservesRecip`, `Map`), whose bucket is the theorems about it.  A type former or a class
    operation (`=`, `↔`, `∈`) concludes every library's theorems (33k for `=`), and a defined
    RELATION between two terms of one type (`⊑`) every inclusion of the repo — and a hypothesis of
    one of those is a relation again, so an unfiltered scan there nests `FUEL` deep. -/
def unfiltered (h : Name) : MetaM Bool := do
  let env ← getEnv
  let some ci := env.find? h | throwError "the search head `{h}` is no constant of the environment"
  unless ci matches .defnInfo _ do return false
  if env.isProjectionFn h then return false
  Meta.forallTelescope ci.type fun xs _ => do
    let ex ← xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    if ex.size < 2 then return true
    return !(← Meta.isDefEq (← Meta.inferType ex[ex.size - 2]!) (← Meta.inferType ex[ex.size - 1]!))

mutual

/-- Is `want` PROVED by some declaration of the environment — and what is the proof?  Candidates
    are the constants whose conclusion is headed by `head` and whose statement mentions everything
    the family does; each one's type is opened at FRESH UNIVERSES with metavariables, both its
    conclusion and `want` are normalised through the spelling bridges, and the two are unified.
    Every argument the unification left open must then be answered in its own right, and what comes
    back is the candidate applied to those arguments — a term, checked before it is believed. -/
partial def findProof (br : Meta.Simp.Context) (want : Expr) (head : Name) (must : NameSet) (fuel : Nat)
    (seen : Array Expr := #[]) : MetaM (Option (Name × Expr)) := do
  -- AN EMPTY FILTER IS NO SEARCH where the head needs one: a family the match unfolded to a bare
  -- lambda (`prefix` read as `(φ A)°`) names no constant, and every equation passes that filter.
  if must.isEmpty && !(← unfiltered head) then return none
  let env ← getEnv
  let rw ← bridge br want
  let mut hit : Option (Name × Expr) := none
  for (n, has) in ← candidates head do
    if hit.isSome then break
    -- THE SEARCH IS BOUNDED FROM ITS OWN START, and the check sits OUTSIDE the candidate's own
    -- `tryCatchRuntimeEx` below: a budget spent inside one candidate is caught as that candidate's
    -- failure and the scan walks on to the next, so this loop is the only place a whole search can
    -- end.  Without it a goal nothing proves is a full scan of the environment at every step of
    -- `discharge`, which is the environment cubed and never returns (`Freyd.Alg.Cylinder.Q`).
    Core.checkMaxHeartbeats "the naturality search"
    if must.any (fun m => !has.contains m) then continue
    let some ci := env.find? n | continue
    let s ← Meta.saveState
    let attempt : MetaM (Option (Name × Expr)) := do
      -- Fresh LEVEL metavariables, as `mkAppMeta` takes them: a candidate's own universe
      -- parameters are rigid, so a polymorphic closure theorem could never match a concrete
      -- region and the search would silently pass it over.
      let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
      let (args, bis, body) ← Meta.forallMetaTelescope
        (ci.type.instantiateLevelParams ci.levelParams lvls)
      let rc ← bridge br body
      -- THE MATCH IS THE ONE BOUNDED STEP, and it is bounded FROM ITS OWN START.  Unifying a
      -- relator metavariable applied to an object has no most general solution and can diverge, so
      -- it gets a budget of its own; what follows — discharging the factors' squares, checking the
      -- assembled term — is more searching, and a budget there is a dot lost to a timeout.
      unless ← Core.withCurrHeartbeats (withTheReader Core.Context
        (fun c => { c with maxHeartbeats := CANDIDATE_HEARTBEATS })
        (Meta.isDefEq rc.expr rw.expr)) do return none
      unless ← discharge br args bis fuel (seen.push want) do return none
      checked want rw rc n (mkAppN (.const n lvls) args)
    -- `tryCatchRuntimeEx`, not `try`: a heartbeat timeout is a RUNTIME exception, and plain
    -- `try`/`catch` in `MetaM` rethrows those, so the budget above would end the panel instead of
    -- ending the candidate.  It also ends a candidate whose assembled term fails `Meta.check`.
    let ok : Option (Name × Expr) ← tryCatchRuntimeEx attempt (fun _ => pure none)
    if ok.isSome then hit := ok else s.restore
  return hit

/-- Every argument the match left open has to be ANSWERED — and answered with a term, which is
    what assigns the metavariable and so what makes the assembled application a proof.  A closure
    theorem — `strictNatural_prod`, `strictNatural_recip`, `laxNatural_inside` — states a compound
    family's square out of its factors' squares, so this is what makes a compound bead's dot
    exactly its factors' dots and never more.  An instance argument is synthesised; a non-`Prop`
    argument left open means the match itself pinned nothing down, and is a refusal. -/
partial def discharge (br : Meta.Simp.Context) (args : Array Expr) (bis : Array BinderInfo) (fuel : Nat)
    (seen : Array Expr) : MetaM Bool := do
  for i in [0 : args.size] do
    let .mvar id := args[i]! | continue
    if ← id.isAssigned then continue
    let t ← instantiateMVars (← id.getType)
    if bis[i]! == .instImplicit then
      let .some v ← Meta.trySynthInstance t | return false
      unless ← Meta.isDefEq args[i]! v do return false
      continue
    unless ← Meta.isProp t do return false
    -- A HYPOTHESIS THE SQUARE ITSELF BINDS answers before the environment is scanned: a square
    -- restricted to the maps opens `hf : Map f` as a local, and `singletonMap_natural` asks for
    -- exactly that — searching the environment for it instead finds nothing, because `f` is a free
    -- variable no declaration is about.
    if let some fv ← Meta.findLocalDeclWithType? t then
      unless ← Meta.isDefEq args[i]! (.fvar fv) do return false
      continue
    if fuel == 0 then return false
    let some (_, pf) ← findAnyProof br t (fuel - 1) seen | return false
    unless ← Meta.isDefEq args[i]! pf do return false
  return true

/-- The search for ONE naturality proposition, under both the head it is written with and the head
    of the SQUARE it unfolds to.  `StrictNatural`/`LaxNatural` are exposed definitions, so
    unfolding one and opening its binders gives the very equation (or inclusion) a hand-written
    declaration states, and its own head is what to search under. -/
partial def findAnyProof (br : Meta.Simp.Context) (want : Expr) (fuel : Nat) (seen : Array Expr) :
    MetaM (Option (Name × Expr)) := do
  let some h := want.getAppFn.constName? | return none
  -- A GOAL AMONG ITS OWN ANCESTORS IS NO NEW GOAL: `strictNatural_recip` twice asks again for the
  -- family it started from (`φ°° ≡ φ`), and a proof through that loop has a shorter one without it.
  if ← seen.anyM fun s => Meta.withNewMCtxDepth (Meta.isDefEq s want) then return none
  -- The CLASS-headed search takes no `must`: a closure theorem names `prodMap` where the bead
  -- names `rprodMap`, so a filter drawn from the bead's own constants would drop exactly the
  -- declarations a compound bead's verdict comes from.  Few declarations conclude in the class,
  -- so the filter buys nothing there, nor at any other defined predicate (`PreservesRecip`); any
  -- other hypothesis (`=`, `⊑`, `↔`) is asked for by the constants it names, as a square is.
  let must ← if ← unfiltered h then pure {} else mustOfFamily br want
  if let some r ← findProof br want h must fuel seen then return some r
  -- Only a naturality CLASS is unfolded to its square.  Unfolding anything else lands on a head
  -- like `False`, which every refutation in the environment matches with its own hypotheses
  -- left to be found — a search that answers the question it was not asked.
  unless h == ``Freyd.Alg.StrictNatural || h == ``Freyd.Alg.LaxNatural
      || h == ``Freyd.Alg.OpLaxNatural do return none
  findSquare br want (← mustOf br want) fuel (seen.push want)

/-- The same search, for a naturality stated as the SQUARE ITSELF rather than through the class.
    The binders are opened as FREE VARIABLES, not metavariables: the square is then the very
    equation a hand-written declaration states, and the proof found for it closes back over `a`,
    `b`, `R` — `mkLambdaFVars` — into a proof of the class the bead asked about.  A square stated
    the other way round is the SAME square: `Eq.symm` is a proof term like any other, so the
    mirrored form is searched for too rather than the direction a declaration happens to be
    written in deciding whether a bead has a dot. -/
partial def findSquare (br : Meta.Simp.Context) (prop : Expr) (must : NameSet) (fuel : Nat)
    (seen : Array Expr) : MetaM (Option (Name × Expr)) := do
  let some body ← Meta.unfoldDefinition? prop | return none
  findTelescoped br body must fuel seen

/-- The same search for a square GIVEN as its own `∀`-statement rather than reached by unfolding a
    naturality class — the function category's `funSquare`, which no class in the repo wraps. -/
partial def findTelescoped (br : Meta.Simp.Context) (body : Expr) (must : NameSet) (fuel : Nat)
    (seen : Array Expr := #[]) : MetaM (Option (Name × Expr)) := do
  Meta.forallTelescope body fun xs sq => do
    let .const h _ := sq.getAppFn | return none
    if let some (n, pf) ← findProof br sq h must fuel seen then
      return some (n, ← Meta.mkLambdaFVars xs pf)
    let some sqm ← flipEq? sq | return none
    let some (n, pf) ← findProof br sqm h must fuel seen | return none
    return some (n, ← Meta.mkLambdaFVars xs (← Meta.mkEqSymm pf))

end

end Freyd.StrDiag
