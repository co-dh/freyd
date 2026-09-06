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

open Lean

namespace Freyd.StrDiag

/-- A one-field record IS its field as far as a picture is concerned: the object `⟨Tx⟩` of a
    category of sets is the set `Tx`, and printing the wrapper makes every lane label unreadable.
    Generic over the environment — any constructor with exactly one field, no list of names. -/
partial def unwrapRecords (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    let .const n _ := x.getAppFn | return .continue
    let some (.ctorInfo ci) := (← getEnv).find? n | return .continue
    if ci.numFields != 1 then return .continue
    let args := x.getAppArgs
    if args.size != ci.numParams + 1 then return .continue
    return .done args[args.size - 1]!)

/-- Lean's pretty printer on one line, the repo's own namespaces off: inside a picture of the
    repo's algebra `Freyd.Alg.relCata R` is noise and `⦇R⦈` is the thing itself. -/
def plain (e : Expr) : MetaM String := do
  -- A label is the note's spelling, not Lean syntax: a name the parser would need escaped (`prefix`
  -- is a keyword) prints bare, so the `«»` the formatter wraps it in are dropped.
  let s := (toString (← Meta.ppExpr (← unwrapRecords e))).replace "«" "" |>.replace "»" ""
  let s := s.replace "Freyd.Alg.RelSet." "" |>.replace "Freyd.Alg." "" |>.replace "Freyd." ""
    |>.replace "Alg." ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- The source and target of a hom type `a ⟶ b`. -/
def homObjs? (t : Expr) : Option (Expr × Expr) :=
  match t.getAppFnArgs with
  | (``Cat.Hom, #[_, _, a, b]) => some (a, b)
  | _ => none

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
  | (``Freyd.Alg.Relator.idRelator, _) => #[]
  | (``Freyd.idFunctor, _) => #[]
  | _ => #[f]

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

  §13.6's objects are records and defs — `dSched Tx`, `⟨Tx × Sched Tx⟩` — not `F.obj X`, so a
  syntactic peel finds nothing in them.  What a picture needs is the RELATORS whose action they
  are, and the environment is where those live: every constant whose type is `Relator 𝒜 𝒜` is a
  candidate wire, and `X` carries that wire when `R.obj ?a` unifies with `X`.  No list of relator
  names in the tool. -/

/-- One wire of a stack: a relator, or the LEFT FACTOR of a product — `A×−` is a wire whose label
    names the factor, and the rest of the stack is what the product's right factor peels to. -/
inductive Wire where
  | rel (r : Expr)
  | timesL (l : Expr)
  /-- A PAIRING `⟨F,G⟩ : 𝒜 ⟶ 𝒜×𝒜`: the lane an object of a product region opens, which no single
      constant names. -/
  | pairW (p : Expr)
  deriving Inhabited

def Wire.expr : Wire → Expr
  | .rel r => r
  | .timesL l => l
  | .pairW p => p

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

def Wire.label : Wire → MetaM String
  | .rel r => relLabel r
  | .timesL l => return (← plain l) ++ "×−"
  | .pairW p => relLabel p

/-- Is this lane a CONSTANT left factor?  That is the one lane a product map can act underneath. -/
def Wire.isTimesL : Wire → Bool
  | .timesL _ => true
  | _ => false

def Wire.beq (a b : Wire) : MetaM Bool :=
  match a, b with
  | .rel x, .rel y => Meta.isDefEq x y
  | .timesL x, .timesL y => Meta.isDefEq x y
  | .pairW x, .pairW y => Meta.isDefEq x y
  | _, _ => return false

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

/-- The identity relator of a region, built with the region's OWN instance rather than a level
    metavariable — the empty wire stack is a relator like any other and has to be nameable. -/
def idRelatorOf (regionTy : Expr) : MetaM Expr := do
  Meta.mkAppOptM ``Freyd.Alg.Relator.idRelator #[regionTy, some (← allegoryInst regionTy)]

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

/-- A lane as a RELATOR: `A×−` is the product of the constant `A` with the identity, which is the
    relator the note's label names and the one a naturality statement has to be about. -/
def wireRelator (regionTy : Expr) : Wire → MetaM Expr
  | .rel r => return r
  | .pairW p => return p
  | .timesL l => do
    let inst ← allegoryInst regionTy
    Meta.mkAppM ``Freyd.Alg.Relator.prod
      #[← Meta.mkAppOptM ``Freyd.Alg.Relator.const
          #[some regionTy, some regionTy, some inst, some inst, some l],
        ← idRelatorOf regionTy]

/-- The composite relator a wire stack is, outermost first: `[W₀,W₁]` is `comp W₁ W₀`, whose object
    map is `W₀.obj ∘ W₁.obj`. -/
def stackRelator (regionTy : Expr) (ws : Array Wire) : MetaM Expr := do
  if ws.isEmpty then return ← idRelatorOf regionTy
  let mut acc ← wireRelator regionTy ws[ws.size - 1]!
  for i in [0 : ws.size - 1] do
    acc ← Meta.mkAppM ``Freyd.Alg.Relator.comp #[acc, ← wireRelator regionTy ws[ws.size - 2 - i]!]
  return acc

/-- The two factors of a product object: `X` is `a × b` when the region's own product apex
    `relProd ?a ?b` unifies with it.  `none` where the region has no products at all. -/
def splitTimes? (regionTy X : Expr) : MetaM (Option (Expr × Expr)) := do
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

/-- The endorelators of a region the environment NAMES.  A combinator — `comp`, `prod`, `pair` —
    is excluded by its own type: it takes a relator as an argument, so peeling with it would peel
    with an unknown, and `const`/`idRelator` are excluded at the peel by the progress test. -/
def relatorCatalogue : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants do
    if n.isInternal || ci.isUnsafe || concHead ci.type != ``Freyd.Alg.Relator then continue
    let s ← Meta.saveState
    let ok : Bool ← try
      let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
      let (args, _, concl) ← Meta.forallMetaTelescope
        (ci.type.instantiateLevelParams ci.levelParams lvls)
      let mut good := true
      for a in args do
        if (← instantiateMVars (← Meta.inferType a)).isAppOf ``Freyd.Alg.Relator then good := false
      pure (good && concl.getAppArgs.size ≥ 2)
    catch _ => pure false
    s.restore
    if ok then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

/-- `X` as `R.obj a` for the catalogue entry `n`, or `none`.  Progress is required — a relator
    that gives back `X` itself peels nothing — and so is a fully determined answer, which is what
    keeps a relator with an undetermined parameter from matching anything. -/
def peelWith? (n : Name) (objVars : Array Expr) (regionTy X : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let some ci := (← getEnv).find? n | return none
  let s ← Meta.saveState
  try
    let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
    let (args, bis, concl) ← Meta.forallMetaTelescope
      (ci.type.instantiateLevelParams ci.levelParams lvls)
    let cargs := concl.getAppArgs
    -- Only the wire's TARGET is the region being peeled: a wire is a functor between regions, and
    -- a bifunctor's is `𝒜×𝒜 ⟶ 𝒜`, so the peel goes on in whatever region the wire comes from.
    unless (← Meta.isDefEq cargs[1]! regionTy) do s.restore; return none
    -- Instance arguments can only be synthesised once the regions are known, and left unsolved
    -- they leave the relator holding a metavariable that the `hasExprMVar` test then drops with no
    -- error — the peel that silently finds nothing.
    for i in [0 : args.size] do
      unless bis[i]! == .instImplicit do continue
      let .mvar id := args[i]! | continue
      if ← id.isAssigned then continue
      let .some v ← Meta.trySynthInstance (← instantiateMVars (← id.getType))
        | s.restore; return none
      unless ← Meta.isDefEq args[i]! v do s.restore; return none
    let src ← instantiateMVars cargs[0]!
    let R := mkAppN (mkConst n lvls) args
    let inner ← freshObj src
    let (fR, _) ← mkAppMeta ``Freyd.Alg.Relator.toFunctor #[R]
    let (app, _) ← mkAppMeta ``Freyd.Functor.obj #[fR, inner]
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

/-- A product's LEFT factor as lanes.  `(A×B)×C` and `A×(B×C)` are the same stack of lanes, which
    is why an associativity re-bracketing is invisible in a picture. -/
partial def peelLefts (regionTy a : Expr) : MetaM (Array Wire) := do
  match ← splitTimes? regionTy a with
  | some (x, y) => return (← peelLefts regionTy x) ++ (← peelLefts regionTy y)
  | none => return #[Wire.timesL a]

/-- An object peeled into its wire stack (outermost first) and the object underneath. -/
partial def peelObj (objVars : Array Expr) (cat : Array Name) (regionTy X : Expr) :
    MetaM (Array Wire × Expr) := do
  match X.getAppFnArgs with
  | (``Freyd.Functor.obj, args) =>
    if let some (f, x) := lastTwo args then
      let (ws, o) ← peelObj objVars cat regionTy x
      return ((wiresOf f).map Wire.rel ++ ws, o)
  | (``Prod.mk, args) =>
    -- An object of a PRODUCT region IS a pair, and the pair of the two halves' stacks is the
    -- PAIRING relator — ONE lane, with the product region on its outside.  Both halves have to
    -- stand over the same object: that is what makes the pairing a functor of one variable.
    if let some (l, r) := prodRegions? regionTy then
      if args.size == 4 then
        let (wsx, ox) ← peelObj objVars cat l args[2]!
        let (wsy, oy) ← peelObj objVars cat r args[3]!
        if ← Meta.isDefEq ox oy then
          let bot ← Meta.inferType ox
          let p ← Meta.mkAppM ``Freyd.Alg.Relator.pair
            #[← stackRelator bot wsx, ← stackRelator bot wsy]
          return (#[Wire.pairW p], ox)
  | _ => pure ()
  if let some (a, b) ← splitTimes? regionTy X then
    let la ← peelLefts regionTy a
    -- `A×−` is a lane only while `A` is CONSTANT.  A left factor that mentions an object the
    -- statement quantifies over varies with the wire underneath it, so the product is the bifunctor
    -- `×` fed by a pairing — which the catalogue's own `timesRel` peels, over the product region.
    unless la.any (fun w => objVars.any fun v => (Wire.expr w).containsFVar v.fvarId!) do
      let (ws, o) ← peelObj objVars cat regionTy b
      return (la ++ ws, o)
  for n in cat do
    if let some (R, src, inner) ← peelWith? n objVars regionTy X then
      let (ws, o) ← peelObj objVars cat src inner
      return (#[Wire.rel R] ++ ws, o)
  return (#[], X)

/-- The two ends of an arrow. -/
def homEnds (e : Expr) : MetaM (Expr × Expr) := do
  let some p := homObjs? (← Meta.inferType e)
    | throwError "not an arrow of a category: {← Meta.ppExpr e}"
  return p

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

/-- A composite flattened into its factors, in diagram order. -/
partial def factors (e : Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``Cat.comp, args) => match lastTwo args with
    | some (f, g) => factors f ++ factors g
    | none => #[e]
  | _ => #[e]

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

/-- What a candidate for a naturality proposition must MENTION: the constants of the family it is
    about — the proposition's last argument — with the region's own projections dropped, those
    being where the object variable was substituted in rather than anything the bead is built
    from.  A `¬` is stripped first: refuting a family is a statement about that same family.

    KEEPING THE OBJECTS IS WHAT MAKES THE SEARCH FINITE IN PRACTICE.  Narrowing this to the ARROWS
    of the family — dropping the objects they are taken at, which is what a naturality theorem is
    general in — is the reading the statement wants, and it opens the square search to every
    equation of the environment: on `prefix_cancel.lhs` that reaches the 12 GB the exporter runs
    under (`scripts/cap`) and the process dies. -/
def mustOf (want : Expr) : MetaM NameSet := do
  let p := match want.getAppFnArgs with | (``Not, #[q]) => q | _ => want
  let some φ := p.getAppArgs.back? | return consts want
  let env ← getEnv
  return (consts φ).toList.foldl
    (fun acc n => if env.isProjectionFn n then acc else acc.insert n) {}

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

mutual

/-- Is `want` PROVED by some declaration of the environment — and what is the proof?  Candidates
    are the constants whose conclusion is headed by `head` and whose statement mentions everything
    the family does; each one's type is opened at FRESH UNIVERSES with metavariables, both its
    conclusion and `want` are normalised through the spelling bridges, and the two are unified.
    Every argument the unification left open must then be answered in its own right, and what comes
    back is the candidate applied to those arguments — a term, checked before it is believed. -/
partial def findProof (br : Meta.Simp.Context) (want : Expr) (head : Name) (must : NameSet) (fuel : Nat) :
    MetaM (Option (Name × Expr)) := do
  let env ← getEnv
  let rw ← bridge br want
  let mut hit : Option (Name × Expr) := none
  for (n, ci) in env.constants do
    if hit.isSome then break
    if n.isInternal || ci.isUnsafe || concHead ci.type != head then continue
    let has := consts ci.type
    if must.any (fun m => !has.contains m) then continue
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
      unless ← discharge br args bis fuel do return none
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
partial def discharge (br : Meta.Simp.Context) (args : Array Expr) (bis : Array BinderInfo) (fuel : Nat) :
    MetaM Bool := do
  for i in [0 : args.size] do
    let .mvar id := args[i]! | continue
    if ← id.isAssigned then continue
    let t ← instantiateMVars (← id.getType)
    if bis[i]! == .instImplicit then
      let .some v ← Meta.trySynthInstance t | return false
      unless ← Meta.isDefEq args[i]! v do return false
      continue
    unless ← Meta.isProp t do return false
    if fuel == 0 then return false
    let some (_, pf) ← findAnyProof br t (fuel - 1) | return false
    unless ← Meta.isDefEq args[i]! pf do return false
  return true

/-- The search for ONE naturality proposition, under both the head it is written with and the head
    of the SQUARE it unfolds to.  `StrictNatural`/`LaxNatural` are exposed definitions, so
    unfolding one and opening its binders gives the very equation (or inclusion) a hand-written
    declaration states, and its own head is what to search under. -/
partial def findAnyProof (br : Meta.Simp.Context) (want : Expr) (fuel : Nat) :
    MetaM (Option (Name × Expr)) := do
  let some h := want.getAppFn.constName? | return none
  -- The CLASS-headed search takes no `must`: a closure theorem names `prodMap` where the bead
  -- names `rprodMap`, so a filter drawn from the bead's own constants would drop exactly the
  -- declarations a compound bead's verdict comes from.  Few declarations conclude in the class,
  -- so the filter buys nothing there; the SQUARE search, headed by `=` or `⊑`, keeps it.
  if let some r ← findProof br want h {} fuel then return some r
  -- Only a naturality CLASS is unfolded to its square.  Unfolding anything else lands on a head
  -- like `False`, which every refutation in the environment matches with its own hypotheses left
  -- to be found — a search that answers the question it was not asked.
  unless h == ``Freyd.Alg.StrictNatural || h == ``Freyd.Alg.LaxNatural do return none
  findSquare br want (← mustOf want) fuel

/-- The same search, for a naturality stated as the SQUARE ITSELF rather than through the class.
    The binders are opened as FREE VARIABLES, not metavariables: the square is then the very
    equation a hand-written declaration states, and the proof found for it closes back over `a`,
    `b`, `R` — `mkLambdaFVars` — into a proof of the class the bead asked about.  A square stated
    the other way round is the SAME square: `Eq.symm` is a proof term like any other, so the
    mirrored form is searched for too rather than the direction a declaration happens to be
    written in deciding whether a bead has a dot. -/
partial def findSquare (br : Meta.Simp.Context) (prop : Expr) (must : NameSet) (fuel : Nat) :
    MetaM (Option (Name × Expr)) := do
  let some body ← Meta.unfoldDefinition? prop | return none
  Meta.forallTelescope body fun xs sq => do
    let .const h _ := sq.getAppFn | return none
    if let some (n, pf) ← findProof br sq h must fuel then
      return some (n, ← Meta.mkLambdaFVars xs pf)
    let some sqm ← flipEq? sq | return none
    let some (n, pf) ← findProof br sqm h must fuel | return none
    return some (n, ← Meta.mkLambdaFVars xs (← Meta.mkEqSymm pf))

end

end Freyd.StrDiag
