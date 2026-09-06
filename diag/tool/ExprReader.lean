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
  let s := toString (← Meta.ppExpr (← unwrapRecords e))
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
  deriving Inhabited

def Wire.expr : Wire → Expr
  | .rel r => r
  | .timesL l => l

def Wire.label : Wire → MetaM String
  | .rel r => plain r
  | .timesL l => return (← plain l) ++ "×−"

def Wire.beq (a b : Wire) : MetaM Bool :=
  match a, b with
  | .rel x, .rel y => Meta.isDefEq x y
  | .timesL x, .timesL y => Meta.isDefEq x y
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
  Meta.synthInstance (← Meta.mkAppM ``Freyd.Alg.Allegory #[regionTy])

/-- The identity relator of a region, built with the region's OWN instance rather than a level
    metavariable — the empty wire stack is a relator like any other and has to be nameable. -/
def idRelatorOf (regionTy : Expr) : MetaM Expr := do
  Meta.mkAppOptM ``Freyd.Alg.Relator.idRelator #[regionTy, some (← allegoryInst regionTy)]

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
def relatorCatalogue (regionTy : Expr) : MetaM (Array Name) := do
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
      let cargs := concl.getAppArgs
      if !good || cargs.size < 2 then pure false
      else pure ((← Meta.isDefEq cargs[0]! regionTy) && (← Meta.isDefEq cargs[1]! regionTy))
    catch _ => pure false
    s.restore
    if ok then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

/-- `X` as `R.obj a` for the catalogue entry `n`, or `none`.  Progress is required — a relator
    that gives back `X` itself peels nothing — and so is a fully determined answer, which is what
    keeps a relator with an undetermined parameter from matching anything. -/
def peelWith? (n : Name) (regionTy X : Expr) : MetaM (Option (Expr × Expr)) := do
  let some ci := (← getEnv).find? n | return none
  let s ← Meta.saveState
  try
    let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
    let (args, _, concl) ← Meta.forallMetaTelescope
      (ci.type.instantiateLevelParams ci.levelParams lvls)
    let cargs := concl.getAppArgs
    unless (← Meta.isDefEq cargs[0]! regionTy) && (← Meta.isDefEq cargs[1]! regionTy) do
      s.restore; return none
    let R := mkAppN (mkConst n lvls) args
    let inner ← Meta.mkFreshExprMVar (some regionTy)
    let (fR, _) ← mkAppMeta ``Freyd.Alg.Relator.toFunctor #[R]
    let (app, _) ← mkAppMeta ``Freyd.Functor.obj #[fR, inner]
    if ← Meta.isDefEq app X then
      let inner ← instantiateMVars inner
      let R ← instantiateMVars R
      if !inner.hasExprMVar && !R.hasExprMVar && !(← Meta.isDefEq inner X) then
        return some (R, inner)
    s.restore; return none
  catch _ => s.restore; return none

/-- A product's LEFT factor as lanes.  `(A×B)×C` and `A×(B×C)` are the same stack of lanes, which
    is why an associativity re-bracketing is invisible in a picture. -/
partial def peelLefts (regionTy a : Expr) : MetaM (Array Wire) := do
  match ← splitTimes? regionTy a with
  | some (x, y) => return (← peelLefts regionTy x) ++ (← peelLefts regionTy y)
  | none => return #[Wire.timesL a]

/-- An object peeled into its wire stack (outermost first) and the object underneath. -/
partial def peelObj (regionTy : Expr) (cat : Array Name) (X : Expr) :
    MetaM (Array Wire × Expr) := do
  match X.getAppFnArgs with
  | (``Freyd.Functor.obj, args) =>
    if let some (f, x) := lastTwo args then
      let (ws, o) ← peelObj regionTy cat x
      return ((wiresOf f).map Wire.rel ++ ws, o)
  | _ => pure ()
  if let some (a, b) ← splitTimes? regionTy X then
    let la ← peelLefts regionTy a
    let (ws, o) ← peelObj regionTy cat b
    return (la ++ ws, o)
  for n in cat do
    if let some (R, inner) ← peelWith? n regionTy X then
      let (ws, o) ← peelObj regionTy cat inner
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

/-- Is `want` proved by some declaration of the environment?  Candidates are the constants whose
    conclusion is headed by `head` and whose statement mentions everything the family does; each
    one's type is opened with metavariables and unified with `want`. -/
def findProof (want : Expr) (head : Name) (must : NameSet) : MetaM (Option Name) := do
  let env ← getEnv
  let mut hit : Option Name := none
  for (n, ci) in env.constants do
    if hit.isSome then break
    if n.isInternal || ci.isUnsafe || concHead ci.type != head then continue
    let has := consts ci.type
    if must.any (fun m => !has.contains m) then continue
    let (_, _, body) ← Meta.forallMetaTelescope ci.type
    if ← Meta.isDefEq body want then hit := some n
  return hit

end Freyd.StrDiag
