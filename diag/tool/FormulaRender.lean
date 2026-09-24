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
    own. -/
partial def descend (declName : Name) (path : List String) (body : Expr) : MetaM Expr := do
  match path with
  | [] => return body
  | s :: rest =>
    match conn? body with
    | some (l, r) => descend declName rest (if s == "lhs" then l else r)
    | none =>
      match ← splitM body with
      | some (_, l, r) =>
        let side := if s == "lhs" then l else r
        if rest.isEmpty then return side
        else throwError "{declName}: `.{rest.head!}` follows `.{s}`, which already names a side \
          of {← Meta.ppExpr body} — a side has no sides of its own"
      | none => throwError "{declName}: `.{s}` finds no side to take of {← Meta.ppExpr body}, \
          which is neither a connective (`↔`, `∧`) nor a relation between two arrows"

/-- `.body`, the one branch selector a formula opens: it instantiates a least fixed point's binder
    with a local of that binder's own name — the same local `StrDiag.withSel` opens for the
    picture, so the formula names it the same way the wire beside it does.  `.inl`/`.inr` name an
    ARM of a fork or an OPERAND of a union or meet, which is a restriction of the PICTURE the
    formula has no counterpart of: the statement itself has no such part to print, so this fails
    rather than guess at what the fork's other side would have said. -/
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
  | .inl :: _ | .inr :: _ =>
    throwError "{declName}: --formula draws no `.inl`/`.inr` branch of a side — the statement has \
      no such part to print"

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
    from. -/
def render (declName : Name) (binder : Option String) (path : List String)
    (branch : List StrDiag.Sel) : MetaM (Array Lbl) :=
  withDeclScope declName do
  let some ci := (← getEnv).find? declName | throwError "no such declaration: {declName}"
  Meta.forallTelescope (← nameSelf declName ci.type) fun xs body => do
    -- A DECLARATION WHOSE TYPE IS NOT A PROPOSITION STATES NOTHING — it DEFINES — so its formula is
    -- the definition itself: the name under its own arguments, `≜`, and the VALUE.  Read off the
    -- type, so every `def` a table heads with prints this way and none is named here.
    if binder.isNone && !(← Meta.isProp body) then
      unless path.isEmpty do
        throwError "{declName}: `.{path.head!}` takes a side of a statement, and a definition has \
          none — its formula is `<name>≜<body>`"
      let some val := ci.value? | throwError "{declName}: a definition with no value — \
        --formula writes `<name>≜<body>` and there is no body to write"
      let head ← labelT (mkAppN (.const declName (ci.levelParams.map Level.param)) xs)
      return ← withBody declName branch (val.beta xs) fun v => return #[head ++ "≜" ++ (← labelT v)]
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
    -- operand are the one table's and not a second spelling here.
    let cond ← if binder.isNone && path.isEmpty && branch.isEmpty then do
        let hyps ← xs.filterM fun x => do
          return (← x.fvarId!.getDecl).binderInfo.isExplicit
            && (← Meta.isProp (← Meta.inferType x))
        let tys ← hyps.mapM fun x => Meta.inferType x
        pure (tys.foldr (fun t acc => some (match acc with | some a => mkAnd t a | none => t)) none)
      else pure none
    let ante ← match cond with
      | some c => pure ((← labelTree (Prec.impl + 1) c) ++ implArrow)
      | none => pure (Lbl.text "")
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
      | some (sym, l, r) => return #[ante ++ (← labelT l) ++ sym, ← labelT r]
      | none => return #[ante ++ (← labelT target')]

/-- The file a note cell `#include`s: the statement as typst content (`Lbl.typst`, a division the
    fraction wherever it stands), cut after its relation by
    `relBreak` so the cell has somewhere to wrap.  The `lean:<decl>@<key>` marker above it is
    `DiagExport.certLine`'s, written for every route at the one place the file is. -/
def file (declName : Name) (binder : Option String) (path : List String)
    (branch : List StrDiag.Sel) : MetaM String := do
  return relBreak.intercalate ((← render declName binder path branch).toList.map fun l => "#" ++ l.bare.typst) ++ "\n"

end Freyd.FormulaRender
