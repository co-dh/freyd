/-
  `FormulaRender` — a declaration's STATEMENT, written the way the note writes it, beside the
  picture drawn from the same declaration.

  Every picture in the note is drawn from a Lean declaration (`--string`/`--circuit`), but every
  FORMULA beside it is typed by hand.  `lean:<decl>@<key>` pins the declaration, not the
  transcription, so nothing checks that the words beside a picture say what the declaration says.
  This mode prints the STATEMENT — not the type (`TypeRender`) — through the same `label` the
  string, circuit and commutative functors already write every box and bead with, so a row's words
  come from the same place as its picture.

  WHAT IS PRINTED.  `<decl>` alone is the whole statement: `label(lhs) <sym> label(rhs)`, the
  symbol read off the statement's OWN HEAD CONSTANT (`ExprReader.split`), never guessed from a
  printed string.  `<decl>.lhs` / `.rhs` is one side alone, chaining through a connective
  (`↔`, `∧`) exactly as `StrDiag.drawString`'s `reqParts` does, so `.lhs.lhs` is the left
  statement's own left side.  A declaration whose type is NOT a proposition defines rather than
  states, and prints as its definition — `<name>(<args>)≜<body>`, the head applied to its own
  binders and the value beside it.  A statement that is not a relation between two arrows still
  prints what `label` can make of it — a bound hypothesis — and never crashes; a term
  `label` cannot read fails naming the declaration and the sub-term, and the run exits nonzero
  through the same stub-file machinery every other route already uses.
-/
import diag.tool.TypeRender
import AOP.CalcSteps

open Lean

namespace Freyd.FormulaRender

open Freyd.StrDiag

/-- THE LINE'S BREAK OPPORTUNITY, after the statement's relation: a zero-width space stands between the
    statement's two parts.  A raw is one unbreakable word, so a cell too narrow for
    a closed-up statement is CUT by the paper edge where a hand-typed neighbour breaks after its
    relation symbol; `#sym.zws` is invisible when the line does not break, and `#h(0pt, weak: true)`
    in its place gives no break opportunity at all. -/
def relBreak : String := "#sym.zws"

/-- Chase `.lhs`/`.rhs` down through statements built from statements (`↔`, `∧`), the same walk
    `StrDiag.drawString`'s `reqParts` does: a step lands on a CONNECTIVE and keeps chasing, or on a
    RELATION and picks a side there, after which nothing may follow — a side has no sides of its
    own.  `.arg` then takes the argument that side is APPLIED to: `f(x)=y`'s `.lhs.arg` is `x`, so a
    table of a map can put its input and output in two columns read off one equation. -/
partial def descend (declName : Name) (path : List String) (body : Expr) : MetaM Expr := do
  match path with
  | [] => return body
  | "arg" :: rest =>
    if (← Meta.isProp body) || !body.isApp then
      throwError "{declName}: `.arg` takes the argument of an applied side, and \
        {← Meta.ppExpr body} is {if ← Meta.isProp body then "a statement — name a side first" else "no application"}"
    descend declName rest body.appArg!
  | s :: rest =>
    match conn? body with
    | some (l, r) => descend declName rest (if s == "lhs" then l else r)
    | none =>
      match ← splitM body with
      | some (_, l, r) =>
        let side := if s == "lhs" then l else r
        if rest.all (· == "arg") then descend declName rest side
        else throwError "{declName}: `.{rest.head!}` follows `.{s}`, which already names a side \
          of {← Meta.ppExpr body} — a side has no sides of its own"
      | none => throwError "{declName}: `.{s}` finds no side to take of {← Meta.ppExpr body}, \
          which is neither a connective (`↔`, `∧`, `Imp`) nor a relation between two arrows"

/-- `.body`, the one branch selector a formula opens: it instantiates a least fixed point's binder
    with a local of that binder's own name — the same local `StrDiag.withSel` opens for the
    picture, so the formula names it the same way the wire beside it does.  `.inl`/`.inr` name an
    ARM of a fork or an OPERAND of a union or meet, a restriction of the PICTURE only: the step
    still states the WHOLE side, so the formula prints that side — as a `branches` group's does. -/
partial def withBody {α : Type} [Inhabited α] (declName : Name) (branch : List StrDiag.Sel) (e : Expr)
    (k : Expr → MetaM α) : MetaM α := do
  match branch with
  | [] => k e
  | .body :: rest =>
    let some φ := StrDiag.muArg? e
      | throwError "{declName}: `.body` names the body of a least fixed point, and \
          {← Meta.ppExpr e} is not one"
    Meta.lambdaBoundedTelescope φ 1 fun xs b => do
      unless xs.size == 1 do
        throwError "{declName}: `{← Meta.ppExpr φ}` binds no arrow, so `.body` opens no wire to \
          write the formula on"
      withBody declName rest b k
  | .inl :: _ | .inr :: _ => k e

/-- A FIELD'S STRUCTURE ARGUMENT under the name the library gives a value of that structure.  Lean
    calls it `self`, which is no word of the note's (`self(R)` for `F(R)`); the structure's own
    namespace is where its values are named, so the binder takes the name its sibling declarations
    give an argument of that type most often.  A type is no string: the binder is found by the
    projection's parameter count and the siblings by their binder type's head constant. -/
def nameSelf (declName : Name) (ty : Expr) : MetaM Expr := do
  let env ← getEnv
  let some pi := env.getProjectionFnInfo? declName | return ty
  let some s := env.getProjectionStructureName? declName | return ty
  let rec binderNames : Expr → Array Name
    | .forallE n t b _ =>
      let rest := binderNames b
      if t.getAppFn.constName? == some s && !n.isAnonymous && !n.hasMacroScopes && n != `self
        then rest.push n else rest
    | _ => #[]
  noteRead (.pre s)
  let counts := env.constants.fold (init := (∅ : Std.HashMap Name Nat)) fun m c ci =>
    if c.getPrefix != s || (env.getProjectionFnInfo? c).isSome then m
    else (binderNames ci.type).foldl (fun m n => m.insert n (m.getD n 0 + 1)) m
  let some (best, _) := counts.toList.foldl (fun acc (n, k) => match acc with
      | some (b, kb) => if k > kb || (k == kb && n.toString < b.toString) then some (n, k) else acc
      | none => some (n, k)) none
    | throwError "{declName}: no declaration in `{s}` binds an argument of type `{s}`, so its \
        field's `self` has no library name to print under"
  let rec go : Nat → Expr → Expr
    | 0, .forallE _ t b bi => .forallE best t b bi
    | k + 1, .forallE n t b bi => .forallE n t (go k b) bi
    | _, e => e
  return go pi.numParams ty

/-- The declaration's statement, or the one side `path`/`branch` names, in the note's own
    spelling: `label` is the one spelling the string, circuit and commutative functors already
    write every box and bead with, so this prints from the same place their pictures are drawn
    from.  `sp` IS THE PRINT MODE (`StrDiag.withSpaced`), the caller's: a formula set as text has the
    room and is SPACED, and the same statement inside a drawn panel is not. -/
def render (sp : Bool) (declName : Name) (binder : Option String) (path : List String)
    (branch : List StrDiag.Sel) : MetaM (Array Lbl) :=
  withDeclScope declName do withSpaced sp do
  let some ci := (← getEnv).find? declName | throwError "no such declaration: {declName}"
  Meta.forallTelescope (← nameSelf declName ci.type) fun xs body => do
    -- A DECLARATION WHOSE TYPE IS NOT A PROPOSITION STATES NOTHING — it DEFINES — so its formula is
    -- the definition itself: the name under its own arguments, `≜`, and the VALUE.  Read off the
    -- type, so every `def` a table heads with prints this way and none is named here.
    if binder.isNone && !(← Meta.isProp body) then
      unless path.isEmpty do
        throwError "{declName}: `.{path.head!}` takes a side of a statement, and a definition has \
          none — its formula is `<name>≜<body>`"
      let head ← labelT (mkAppN (.const declName (ci.levelParams.map Level.param)) xs)
      -- A STRUCTURE OF PROPOSITIONS (a `Prop` class) has no value but its FIELDS: what it states is
      -- their conjunction, read off the constructor at these arguments.
      if ci.value?.isNone && isStructure (← getEnv) declName then
        let ctor := getStructureCtor (← getEnv) declName
        let cty ← Meta.instantiateForall (← Meta.inferType
          (mkConst ctor.name (ci.levelParams.map Level.param))) xs
        return ← Meta.forallTelescope cty fun fs _ => do
          let tys ← fs.mapM Meta.inferType
          let some c := tys.foldr (fun t acc => some (match acc with | some a => mkAnd t a | none => t)) none
            | throwError "{declName}: a structure with no fields states nothing"
          return #[head ++ spaced "≜" sp ++ (← labelT c)]
      let some val := ci.value? | throwError "{declName}: a definition with no value — \
        --formula writes `<name>≜<body>` and there is no body to write"
      return ← withBody declName branch (val.beta xs) fun v => return #[head ++ spaced "≜" sp ++ (← labelT v)]
    let body ← match binder with
      | some h =>
        match ← xs.findM? fun x => return (← x.fvarId!.getUserName).toString == h with
        | some x => Meta.inferType x
        | none =>
          let names ← xs.mapM fun x => return (← x.fvarId!.getUserName).toString
          throwError "{declName} has no binder `{h}`; its binders are \
            {String.intercalate ", " names.toList}"
      | none => pure body
    -- EVERY EXPLICIT HYPOTHESIS PRINTS, joined by `∧` and followed by `⟹`.  A conditional law with
    -- its condition dropped is a DIFFERENT law — `dom(R S)=𝟙` for `R,S` entire came out as the
    -- claim that every composite is entire — and no gate downstream can tell that cell from a right
    -- one.  EXPLICITNESS IS THE TEST: an instance, a `Decidable` and a typeclass reach the
    -- telescope as instance binders, and an object or an arrow is not a `Prop`.  The conjunction is
    -- built as a TERM and handed to the label, so the `∧`, its spacing and the brackets round an
    -- operand are the one table's and not a second spelling here.  A NATURALITY HYPOTHESIS is the one
    -- exception: the panel's bead dot already states it (`markOfNatPredicate`, by head constant).
    let cond ← if binder.isNone && path.isEmpty && branch.isEmpty then do
        let hyps ← xs.filterM fun x => do
          let t ← Meta.inferType x
          return (← x.fvarId!.getDecl).binderInfo.isExplicit && (← Meta.isProp t)
            && (t.getAppFn.constName?.bind StrDiag.markOfNatPredicate).isNone
        let tys ← hyps.mapM fun x => Meta.inferType x
        pure (tys.foldr (fun t acc => some (match acc with | some a => mkAnd t a | none => t)) none)
      else pure none
    -- THE HYPOTHESES ARE A PART OF THEIR OWN, cut before `⟹` like the relation: a conditional law
    -- in a narrow reason cell breaks there (7.4.4a), not inside a hypothesis.
    let (pre, ante) ← match cond with
      | some c => pure (#[(← labelTree (Prec.impl + 1) c) ++ Lbl.text " "], Lbl.text implArrow.trimLeft)
      | none => pure (#[], Lbl.text "")
    let target ← descend declName path body
    withBody declName branch target fun target' => do
      -- A PREDICATE THE NOTE WRITES BY NAME IS NOT UNFOLDED HERE.  `splitM`'s delta step is there so
      -- a statement with no sides still has two ends to DRAW; a formula has the note's own word for
      -- it, and unfolding wrote `dom(R S)=𝟙` as the conclusion of a hypothesis that said
      -- `Entire(R)` — one predicate in two vocabularies inside one cell.  `diag_noted` is the
      -- declaration that the name IS the note's, so it is also the declaration that there is
      -- nothing under it to open.
      let noted ← Lean.labelled `diag_noted
      let sides ← match target'.getAppFn.constName? with
        | some c => if noted.contains c then pure (split target') else splitM target'
        | none => splitM target'
      match sides with
      | some (sym, l, r) => return pre ++ #[ante ++ (← labelT l (some r)) ++ spaced sym sp, ← labelT r (some l)]
      | none => return pre ++ #[ante ++ (← labelT target')]

/-- The file a note cell `#include`s: the statement as typst content (`Lbl.typst`, a division the
    fraction wherever it stands), cut after its relation by
    `relBreak` so the cell has somewhere to wrap.  The `lean:<decl>@<key>` marker above it is
    `DiagExport.certLine`'s, written for every route at the one place the file is.  SPACED: this is
    the formula set as text, the caller with the room — unless the note's own call says it has none
    (`leanf(sel, compact: true)`, the selector step `.compact`: a formula fitted above a panel). -/
def file (declName : Name) (binder : Option String) (path : List String)
    (branch : List StrDiag.Sel) : MetaM String := do
  let ls ← render (!path.contains "compact") declName binder (path.filter (· != "compact")) branch
  return relBreak.intercalate (ls.toList.map fun l => "#" ++ l.bare.typst) ++ "\n"

/-- The side `path` names of `declName`'s statement, its binders opened with METAVARIABLES, so two
    panels read off two declarations meet in one theorem by unification rather than by binder name.
    `.inl`/`.inr` restrict the picture only (`withBody`); a step relates WHOLE sides. -/
abbrev Side := Name × Option String × List String × List StrDiag.Sel

/-- The binder names of a statement's telescope, outermost first. -/
def binderNames : Expr → List Name
  | .forallE n _ t _ => n :: binderNames t
  | _ => []

/-- The side `d` names, under its declaration's binders `xs` (named `ns`) and statement `body`: a
    `#h` selector reads the binder `h`'s own statement, as `render` does. -/
def sideIn (d : Side) (xs : Array Expr) (ns : List Name) (body : Expr) : MetaM Expr := do
  let (declName, binder, path, branch) := d
  if branch.any (· matches .body) then
    throwError "{declName}: a chain step relates whole sides, and `.body` names a fixed point's body"
  let st ← match binder with
    | none => pure body
    | some h => match (xs.toList.zip ns).find? (·.2.toString == h) with
      | some (x, _) => instantiateMVars (← Meta.inferType x)
      | none => throwError "{declName} has no binder `{h}`"
  descend declName path st

def sideM (d : Side) : MetaM (Array Expr × Expr) := do
  let some ci := (← getEnv).find? d.1 | throwError "no such declaration: {d.1}"
  let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
  let (ms, _, body) ← Meta.forallMetaTelescope (ci.type.instantiateLevelParams ci.levelParams lvls)
  return (ms, ← sideIn d ms (binderNames ci.type) body)

/-- The relation read with its two sides swapped: what `B sym A` says of `A` and `B`. -/
def converseSym (sym : String) : MetaM String :=
  match sym with
  | "=" => pure "=" | "⊑" => pure "⊒" | "≤" => pure "≥"
  | s => throwError "a chain step's relation `{s}` has no converse in the note's notation"

/-- Opens the statement `t` under the locals `xs` already in scope, one binder at a time so each
    type sees the values chosen before it.  ONE VARIABLE PER BINDER NAME, as `canon` reads a chain's
    peers: `t`'s `X` IS `xs`'s `X` when their types agree (names compared without macro scopes, since
    an anonymous `inst✝` has a different hygiene scope in each declaration); an instance is what
    resolution in that context gives; any other binder is a fresh RIGID local — never a metavariable,
    which would absorb a composite and make two different panels the same term. -/
partial def openUnder {α} (xs : Array Expr) (t : Expr) (vs : Array Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α := do
  match t with
  | .forallE n d body bi =>
    let d := d.instantiateRev vs
    let hit ← xs.findM? fun x => do
      if (← x.fvarId!.getUserName).eraseMacroScopes != n.eraseMacroScopes then return false
      let s ← Meta.saveState
      if ← Meta.isDefEq d (← Meta.inferType x) then return true else s.restore; return false
    if let some x := hit then return ← openUnder xs body (vs.push x) k
    if bi.isInstImplicit then
      if let some v ← Meta.synthInstance? d then return ← openUnder xs body (vs.push v) k
    Meta.withLocalDecl n bi d fun y => openUnder xs body (vs.push y) k
  | _ => k vs (t.instantiateRev vs)

/-- THE DEFINITIONS A STEP OPENS: the `def`s on one side of the step and not the other that a panel
    draws as a bead — an arrow, so no object (`dCL`, `Unit`), instance, projection or auxiliary. -/
def opened (A B : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let a := (← instantiateMVars A).getUsedConstants
  let b := (← instantiateMVars B).getUsedConstants
  (a.filter (!b.contains ·) ++ b.filter (!a.contains ·)).filterM fun c => do
    let some ci@(.defnInfo _) := env.find? c | return false
    if c.isInternal || (← Meta.isInstance c) || (← isProjectionFn c) || isAuxRecursor env c
      || Meta.isMatcherCore env c then return false
    -- NOT `forallTelescopeReducing`: at a concrete category it unfolds `X ⟶ Y` itself (in `RelSet`
    -- to `X → Y → Prop`) and opens the arrow's own arguments, so `takewhile`, `paths` read as no arrow.
    Meta.forallTelescope ci.type fun _ t => return (homObjs? t).isSome || (homObjs? (← Meta.whnfR t)).isSome

/-- One term up to instances, the bracketing of `≫` and identity factors, which no panel draws. -/
partial def sameDrawn (a b : Expr) : MetaM Bool := do
  let (a, b) := (dropUnits (← instantiateMVars a), dropUnits (← instantiateMVars b))
  let s ← Meta.saveState
  let r ← Meta.withTransparency .instances (Meta.isDefEq a b)
  s.restore
  if r then return true
  let (fa, fb) := (factorList a, factorList b)
  if fa.size > 1 || fb.size > 1 then
    return fa.size == fb.size && (← (fa.zip fb).allM fun (x, y) => sameDrawn x y)
  let (xs, ys) := (a.getAppArgs, b.getAppArgs)
  if xs.size == 0 || xs.size != ys.size then return false
  return (← sameDrawn a.getAppFn b.getAppFn) && (← (xs.zip ys).allM fun (x, y) => sameDrawn x y)

/-- Two terms the note DRAWS alike: one term by `sameDrawn`, or two whose labels are one.  A
    coercion the label does not print is no step a reader can see: `graph (f g)` and `graph f graph g`
    both print `f g`, and a law between them read as the tautology `f g = f g`. -/
def drawnAlike (a b : Expr) : MetaM Bool := do
  if ← sameDrawn a b then return true
  return (← labelT a).bare.typst == (← labelT b).bare.typst

/-- Whether `B` is `A` with the definitions `ds` opened (or closed) and nothing else: both sides
    delta-expanded at `ds` (`deltaExpand` beta-reduces) draw one term. -/
def unfoldsTo (ds : Array Name) (A B : Expr) : MetaM Bool := do
  let a ← Meta.deltaExpand (← instantiateMVars A) ds.contains
  let b ← Meta.deltaExpand (← instantiateMVars B) ds.contains
  -- Opening `ds` must leave no bead on one side only, before any picture is compared: `Λ` opened
  -- beside `takewhile` leaves `takewhile`, and a raw `fun xs ys => …` that has no label.
  if !(← opened a b).isEmpty then return false
  -- Printing alike stands in for one term only around ONE body (`graph` unprinted round `paths`'s);
  -- several bodies opened at once must be one term, and may hold lambdas no label writes.
  if ds.size == 1 then drawnAlike a b else sameDrawn a b

/-- THE RELATION LEAN PROVES FROM PANEL `a` TO PANEL `b` OF A CHAIN: a theorem whose statement's
    head (`split`: `Eq`, `⊑`, `≤`) relates the two sides, read in either direction and oriented by
    which side each panel unifies with.  The candidates are `rfl`, the panels' own declarations, then
    every theorem of their modules — where a chain's step lemmas live — ranked below.  No candidate
    proves the step: an error naming both sides, never a default. -/
def stepRel (a b : Side) : MetaM (Name × String) := do
  let env ← getEnv
  let mods := [a.1, b.1].filterMap env.getModuleIdxFor?
  let near := env.constants.fold (init := #[]) fun acc n ci =>
    if (ci matches .thmInfo _) && !n.isInternal && n != a.1 && n != b.1
      && (env.getModuleIdxFor? n).any mods.contains then acc.push n else acc
  for m in mods do if let some mn := env.header.moduleNames[m.toNat]? then noteRead (.module mn)
  -- and the theorems the panels' own proofs cite, wherever they live (`Λ(R∪S)=⟨Λ(R),Λ(S)⟩cup`).
  let cited := [a.1, b.1].foldl (fun acc d => ((env.find? d).bind (·.value?)).elim acc fun v =>
    v.getUsedConstants.foldl (fun acc n =>
      if (env.find? n).any (· matches .thmInfo _) && !acc.contains n && !near.contains n
        && n != a.1 && n != b.1 then acc.push n else acc) acc) #[]
  let cands := #[a.1, b.1] ++ near.qsort (·.toString < ·.toString) ++ cited
  -- BOTH panels' binders are LOCALS, rigid: a metavariable unifies with whatever a theorem asks, so
  -- a binder only `b` has would absorb a composite and read `X ⊑ Y` as `X = X`.
  let some ca := env.find? a.1 | throwError "no such declaration: {a.1}"
  let some cb := env.find? b.1 | throwError "no such declaration: {b.1}"
  Meta.forallTelescope ca.type fun xs bodyA => do
  openUnder xs cb.type #[] fun ys bodyB => do
  let A ← sideIn a xs (binderNames ca.type) bodyA
  let B ← sideIn b ys (binderNames cb.type) bodyB
  -- A STEP THAT ONLY OPENS A DEFINITION IS `≜`: the beads on one side alone, unfolded, leave the two
  -- sides one picture.  Asked before `rfl`, which would answer the same step `=`.
  -- ONE of them may be the step: `genFold concat ≜ paths` has `genFold` and `concat` on one side
  -- only, and opening them as well as `paths` leaves no picture to compare.
  -- The answer names the ONE definition opened, the step's reason; several at once have no one name.
  let ds ← opened A B
  if let some d ← ds.findM? fun d => unfoldsTo #[d] A B then
    noteRead (.decl d)
    return (d, "≜")
  if !ds.isEmpty && (← unfoldsTo ds A B) then
    for d in ds do noteRead (.decl d)
    return (`delta, "≜")
  -- The hypotheses the step may use: either panel's declaration assumes them.
  let given ← (xs ++ ys).filterMapM fun h => do
    let t ← Meta.inferType h
    return if ← Meta.isProp t then some t else none
  -- THE SAME TERM, however spelled, is `=` by `rfl`: no theorem states it.
  let s0 ← Meta.saveState
  if ← Meta.isDefEq A B then return (`rfl, "=")
  s0.restore
  -- A HYPOTHESIS A PANEL'S DECLARATION ASSUMES is a step of its own (`S°F(X)R ⊑ X`, the prefixed
  -- point a fold is below), answered outright like the declaration.
  for g in given do
    let some (sym, l, r) := split g | continue
    for rev in [false, true] do
      let s ← Meta.saveState
      let (x, y) := if rev then (B, A) else (A, B)
      if (← Meta.isDefEq l x) && (← Meta.isDefEq r y) then
        return (`hypothesis, ← if rev then converseSym sym else pure sym)
      s.restore
  let attempt (c : Name) : MetaM (Option (String × Bool)) := do
    let some ci := env.find? c | return none
    let lvls ← ci.levelParams.mapM fun _ => Meta.mkFreshLevelMVar
    let (ms, _, body) ← Meta.forallMetaTelescope (ci.type.instantiateLevelParams ci.levelParams lvls)
    let some (sym, l, r) := split body | return none
    -- Whether every hypothesis the sides leave open is one either panel's declaration assumes.
    let hyps : MetaM Bool := ms.allM fun m => do
      if ← m.mvarId!.isAssigned then return true
      let t ← instantiateMVars (← Meta.inferType m)
      unless ← Meta.isProp t do return true
      given.anyM fun g => do
        let s ← Meta.saveState
        if ← Meta.isDefEq t g then return true else s.restore; return false
    for rev in [false, true] do
      let s ← Meta.saveState
      let (x, y) := if rev then (B, A) else (A, B)
      if (← Meta.isDefEq l x) && (← Meta.isDefEq r y) then
        let ok ← hyps
        s.restore
        return some (← if rev then converseSym sym else pure sym, ok)
      s.restore
    return none
  -- THE RANK OF AN ANSWER.  A panel's OWN declaration is the step the note draws, and answers
  -- outright; of the other theorems an `=` wins over a `⊑`.  A theorem needing a hypothesis neither
  -- panel assumes proves nothing here (`Eq.symm` would "prove" any `=`), so it is no answer at all.
  let rank (own : Bool) (s : String) : Nat := if own then 4 else if s == "=" then 3 else 2
  let mut best : Option (Nat × Name × String) := none
  let mut cut : Array Name := #[]
  for c in cands do
    let saved ← Meta.saveState
    let r ← tryCatchRuntimeEx (Core.withCurrHeartbeats <| withTheReader Core.Context
        (fun ctx => { ctx with maxHeartbeats := SEARCH_HEARTBEATS }) (Except.ok <$> attempt c))
      fun e => pure (.error e)
    saved.restore
    match r with
    | .ok (some (s, ok)) =>
      if !ok then continue
      let k := rank (c == a.1 || c == b.1) s
      if k ≥ 3 then noteRead (.stmt c); return (c, s)
      if best.all (·.1 < k) then best := some (k, c, s)
    | .ok none => pure ()
    | .error _ => cut := cut.push c
  -- A candidate cut short might have outranked what was found: that is not the answer.
  unless cut.isEmpty do
    throwError "the step from {a.1}.{".".intercalate a.2.2.1} to {b.1}.{".".intercalate b.2.2.1}: the \
      search was cut short at {cut.toList}, which might prove it; raise SEARCH_HEARTBEATS"
  let some (_, c, s) := best
    | throwError "no theorem of {a.1}, {b.1} or their modules relates {a.1}.{".".intercalate a.2.2.1} \
        to {b.1}.{".".intercalate b.2.2.1} by `=`, `⊑` or `≤` in either direction — prove the step \
        in Lean"
  noteRead (.stmt c)
  return (c, s)

/-- A STEP'S LAW: a theorem it applies, or a hypothesis of the step it rewrites with — which prints
    as that hypothesis's own statement. -/
inductive Law where
  | thm (c : Name)
  | hyp (h : Name)
  deriving BEq

/-- Whether theorem `c` is LOGIC rather than a law of arrows: its generic conclusion relates no two
    arrows (`Eq.mpr`, `id`), or relates terms of a type it quantifies over (`Eq.symm`, `congrArg`).
    Reducing, because a conclusion named by a definition (`F.PreservesRecip`) quantifies inside it. -/
def isLogic (c : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? c | return true
  Meta.forallTelescopeReducing ci.type fun _ t => do
    let some (_, l, _) ← splitM t | return true
    return (← Meta.inferType l).getAppFn.isFVar

/-- Whether `c`'s premise `i`, a relation between arrows, is rewritten INSIDE its conclusion: in
    `c`'s own generic statement each side of the conclusion contains a side of the premise
    (`comp_mono_left : R ⊑ S → T;R ⊑ T;S`), so applying `c` is monotonicity or congruence around
    that premise, not a law with it as its condition.  Read off the generic statement, where the
    sides are bound variables, because the instantiated ones match only up to unfolding. -/
def around (c : Name) (i : Nat) : MetaM Bool := do
  let some ci := (← getEnv).find? c | return false
  Meta.forallTelescope ci.type fun xs concl => do
    let some x := xs[i]? | return false
    let some (_, pl, pr) ← splitM (← Meta.inferType x) | return false
    let some (_, cl, cr) ← splitM concl | return false
    return (pl.occurs cl && pr.occurs cr) || (pr.occurs cl && pl.occurs cr)

/-- Whether law `c`, as its reason cell prints it, reads as a tautology: its two sides one label,
    as `graph_comp`'s `f g = f g`, the `graph` coercion unprinted.  Such a law is no reason. -/
def readsAlike (c : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? c | throwError "no such declaration: {c}"
  -- In the scope and spacing `render` prints the reason cell with.
  withDeclScope c do withSpaced true do
  Meta.forallTelescope (← nameSelf c ci.type) fun _ b => do
    let some (_, l, r) := split b | return false
    return (← labelT l (some r)).bare.typst == (← labelT r (some l)).bare.typst

/-- THE LAWS A STEP'S PROOF APPLIES.  A theorem application counts when its statement relates two
    arrows and no proof argument is rewritten inside it: one handed a proof that applies a theorem,
    or a hypothesis it carries to both sides, is congruence or monotonicity around that law
    (`congrArg`, `comp_mono_left`), and one whose two sides draw as one picture (`Cat.assoc`, `rfl`)
    is bracketing no panel shows.  Logic (`Eq.symm`, `Eq.mpr`, `id`) is no law; a hypothesis
    relating two arrows that logic or congruence passes on IS the step's law, and an instantiated
    one (`htrans (m+1)`) applies none.  `coerced`: the STEP's two sides print alike, so a law whose
    sides only PRINT alike (`graph_comp`, `graph` unprinted) is that coercion; on a step whose sides
    differ on the page the law printing alike is the label dropping a factor (`X 𝟙 = X` by
    `Cat.comp_id`), and it is the step's reason. -/
partial def lawsIn (coerced : Bool) (e : Expr) : MetaM (Array Law) := do
  match e with
  | .lam .. => Meta.lambdaTelescope e fun _ b => lawsIn coerced b
  | .letE _ _ v b _ => return (← lawsIn coerced v) ++ (← lawsIn coerced (b.instantiate1 v))
  | .mdata _ b => lawsIn coerced b
  | .fvar f =>
    unless ← Meta.isProof e do return #[]
    let n ← f.getUserName
    return if (← splitM (← instantiateMVars (← Meta.inferType e))).isSome then #[.hyp n]
      else #[]
  | .app .. | .const .. =>
    let args := e.getAppArgs
    let env ← getEnv
    let concl ← instantiateMVars (← Meta.inferType e)
    let law ← match e.getAppFn.constName? with
      | some c => pure ((env.find? c).any (· matches .thmInfo _) && !(← isLogic c))
      | none => pure false
    -- A PROOF argument applying ANY theorem, law or bracketing (`graph_comp` under `congrArg`), makes
    -- this application congruence around it.
    let isThm (x : Expr) := x.getAppFn.constName?.any fun n => (env.find? n).any (· matches .thmInfo _)
    let mut inner := #[]
    let mut built := false
    for (a, i) in args.toList.zipIdx do
      unless a.isFVar do
        let l ← lawsIn coerced a
        let applies := (a.find? isThm).isSome && (← Meta.isProof a)
        inner := inner ++ l; built := built || !l.isEmpty || applies
        continue
      -- A hypothesis is a law the step rewrites with unless a law takes it as its premise.
      if !law || (← e.getAppFn.constName?.elim (pure false) (around · i)) then
        let l ← lawsIn coerced a
        inner := inner ++ l; built := built || !l.isEmpty
    let some c := e.getAppFn.constName? | return inner
    unless law && !built do return inner
    -- A law applied short of its premise (`relCata_le_of_prefixed I`, a `⟹` step) concludes under it.
    Meta.forallTelescope concl fun _ concl => do
      let some (_, l, r) ← splitM concl | return inner
      let alike ← if coerced then pure ((← drawnAlike l r) || (← readsAlike c)) else sameDrawn l r
      return if alike then inner else inner.push (.thm c)
  | _ => return #[]

/-- THE FILE `lean-calc` READS, one row per term of the `calc` proving `declName`: the panel
    selector, the relation into it and the law of the step that reaches it.  The steps are
    `calc_steps`' `<decl>.step_i` theorems, so every panel is a side of a statement like any other;
    the relation is `stepRel`'s between the two panels the chain shows, so `lean-chain`'s own check
    reads the same answer; a step whose proof applies more than one law is refused, naming them. -/
def calcFile (declName : Name) : MetaM String := do
  let env ← getEnv
  let step (i : Nat) := declName ++ Name.mkSimple s!"step_{i + 1}"
  let n := (List.range 1000).find? (fun i => !env.contains (step i)) |>.getD 1000
  if n == 0 then
    throwError "{declName}: no `{step 0}` — write `calc_steps {declName}` after its `calc` proof"
  let side (i : Nat) (s : String) : Side := (step i, none, [s], [])
  let some ci := env.find? declName | throwError "{declName}: no such declaration"
  let some v := ci.value? | throwError "{declName} has no proof term to read the calc off"
  Meta.lambdaTelescope v fun _ body => do
  let spine ← Freyd.Alg.CalcSteps.leaves body (← Meta.inferType body)
  -- A leaf's stated type is `r a b`: `a` is the term the step leaves from.
  let lhsOf (ty : Expr) : MetaM Expr := do
    let as := ty.getAppArgs
    unless as.size ≥ 2 do throwError "{declName}: a calc step states {ty}, no relation of two terms"
    return as[as.size - 2]!
  let first := s!"{step 0}.lhs"
  let first ← match spine[0]? with
    | some (_, ty) => pure (if ← Meta.isProp (← lhsOf (← instantiateMVars ty)) then s!"({first.quote},)" else first.quote)
    | none => pure first.quote
  let mut rows := #[s!"(sel: {first}, rel: none, law: none)"]
  for i in List.range n do
    let some v := (env.find? (step i)).bind (·.value?) | throwError "{step i} has no proof to read"
    noteRead (.decl (step i))
    let (a, b) := if i + 1 < n then (side i "lhs", side (i + 1) "lhs") else (side i "lhs", side i "rhs")
    -- The relation is the calc's own: `↔` and `→` between statements are read off the type its spine
    -- states for the step; between arrows `stepRel` names the theorem relating the two panels.
    let some (_, ty) := spine[i]? | throwError "{declName}: step {i + 1} is no calc step"
    let ty ← instantiateMVars ty
    let t ← lhsOf ty
    let (c?, rel) ← match ty.getAppFn with
      | .const ``Iff _ => pure (none, "⟺")
      | .const ``Freyd.Alg.Imp _ => pure (none, "⟹")
      | _ => do let (c, r) ← stepRel a b; pure (some c, r)
    -- A step opening ONE definition has that definition as its reason, whatever bracketing the
    -- proof does around it (`graph_comp` then `rfl` to reach `paths`).
    let laws ← if c?.any (rel == "≜" && env.contains ·) then pure (c?.toArray.map Law.thm) else do
      -- A step between statements has no two pictures a coercion could make alike.
      let coerced ← if c?.isNone then pure false else do
        let (_, st) ← sideM (step i, none, [], [])
        let some (_, l, r) := split st | throwError "{step i}: its statement relates no two sides"
        drawnAlike l r
      pure (← lawsIn coerced v).toList.eraseDups.toArray
    -- A hypothesis prints as its own statement: the `#h` selector of the step that binds it.
    let lawSel : Law → String | .thm c => c.toString | .hyp h => s!"{step i}#{h}"
    if laws.size > 1 then
      throwError "{step i}: a step applies one law under congruence, and its proof applies \
        {laws.toList.map lawSel} — split it into one `calc` step per law"
    for l in laws do if let .thm c := l then noteRead (.stmt c)
    let sel := if i + 1 < n then s!"{step (i + 1)}.lhs" else s!"{step i}.rhs"
    -- A term that is a statement draws whole: lean-chain's statement selector is a 1-tuple.
    let sel := if ← Meta.isProp t then s!"({sel.quote},)" else sel.quote
    let law := laws[0]?.elim "none" fun l => (lawSel l).quote
    rows := rows.push s!"(sel: {sel}, rel: {rel.quote}, law: {law})"
  return "#let steps = (\n  " ++ ",\n  ".intercalate rows.toList ++ ",\n)\n"

/-- The file a chain step's `lean-rel` imports: the relation `stepRel` reads off Lean. -/
def relFile (a b : Side) : MetaM String := do
  let (c, s) ← stepRel a b
  return "// proved by " ++ c.toString ++ "\n#let rel = \"" ++ s ++ "\"\n"

end Freyd.FormulaRender
