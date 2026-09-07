/-
  `TypeRender` — a declaration's TYPE, written the way the note writes it.

  The note's tables carry a *type* column beside every definition, hand-typed today: `[[Int]]⟶[[Int]]`
  beside `R≜length≤length°`.  A hand-typed cell is a claim nobody checks, and it is exactly the claim
  the environment can settle — `R X`'s hom type IS `dSched X ⟶ dSched X`, and the printing-only
  unexpanders of `AOP` are what turn that into the note's brackets.  So the cell is GENERATED from the
  declaration the row already cites, and carries a `lean:<decl>@<key>` marker of its own: a statement
  that moves under the note fails `cite-check` here too.

  WHAT "THE TYPE" IS.  Three shapes of declaration have one, read off the ELABORATED statement and
  nothing else: an arrow-valued `def` has its hom, an (in)equation between arrows has the hom its two
  sides share, and a relator-valued `def` runs between two categories.  Anything else — a `def`
  returning `Type`, a `Prop` that is not a relation between arrows — gets an error naming the
  statement, never a guessed cell.

  NO STRING SURGERY ON THE PRINTED TYPE.  The spelling is whatever the delaborator and the repo's
  unexpanders give (`dList A` ⇝ `[A]`, `Sched X` ⇝ `[[X]]`, a `RelSet.mk` wrapper peeled), so a
  head with no unexpander prints as its raw Lean name and is a DEFECT to fix where those live —
  never here.
-/
import diag.tool.StringDiagram

open Lean

namespace Freyd.TypeRender

open Freyd.StrDiag

/-! ### The `@key` a `lean:` marker carries

  `cite-check` takes the low 32 bits of `decl_info.stmt_key`, which `lean-refactor`'s indexer computes
  from the alpha- and universe-normalised statement.  That tool is its own repository and is not a
  dependency of this one, so its rule is restated here rather than shelled out to: alpha invariance is
  `Expr.hash`'s own (it mixes the depth at a binder), universe parameters are renamed positionally,
  and `mdata` — source positions and elaborator residue — is dropped. -/

/-- `mdata` hashes as a node of its own and says nothing about the statement. -/
private partial def stripMData : Expr → Expr
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .lam n t b bi     => .lam n (stripMData t) (stripMData b) bi
  | .letE n t v b nd  => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .app f a          => .app (stripMData f) (stripMData a)
  | .mdata _ e        => stripMData e
  | .proj s i e       => .proj s i (stripMData e)
  | e                 => e

/-- A theorem or axiom keys on its TYPE alone — proof irrelevance makes the same statement the same
    fact; anything carrying a value keys on both, many definitions sharing one type.  An inductive
    keys on its constructors instead and is refused rather than keyed wrongly: it has neither a hom
    nor a relator type, so nothing that renders can reach this. -/
def stmtKey (ci : ConstantInfo) : MetaM UInt64 := do
  let canon (e : Expr) : UInt64 :=
    (stripMData (e.instantiateLevelParams ci.levelParams
      (ci.levelParams.mapIdx fun i _ => .param (.mkSimple s!"u{i}")))).hash
  match ci with
  | .thmInfo _ | .axiomInfo _ => return canon ci.type
  | .inductInfo _ => throwError "{ci.name} is an inductive type; its `stmt_key` is keyed on its \
      constructors, which this tool does not compute — cite a declaration ABOUT it instead"
  | _ => return mixHash (canon ci.type) ((ci.value?.map canon).getD 0)

/-- The low 32 bits as `cite-check` spells them: 8 hex digits, zero-padded. -/
def hex8 (k : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 (k.toNat % 4294967296))
  "".pushn '0' (8 - s.length) ++ s

/-! ### The type -/

/-- The declaration's type in the note's spelling.  Run under `withDeclScope` and printed by
    `plain`, so the same delaborator, namespaces and unexpanders the string route draws its labels
    with print this cell. -/
def render (declName : Name) : MetaM String := withDeclScope declName do
  let some ci := (← getEnv).find? declName | throwError "no such declaration: {declName}"
  -- NOT `forallTelescopeReducing`: a hom of `RelSet` reduces to `A → B → Prop`, so reducing walks
  -- straight through the arrow this is here to print and leaves `Prop` as the body of every def.
  Meta.forallTelescope ci.type fun _ body => do
    -- An (in)equation is a statement ABOUT arrows, and its two sides share one hom: read it off the
    -- left, which is the side the note's `definition` column spells.
    match ← splitM body with
    | some (sym, l, r) =>
      let t ← Meta.inferType l
      if (homObjs? t).isNone then
        throwError "{declName} states {← Meta.ppExpr l} {sym} {← Meta.ppExpr r}, whose sides are \
          {← Meta.ppExpr t} and not arrows of a category — it has no hom type to render"
      plain t
    | none =>
      if (homObjs? body).isSome then plain body else
      match body.getAppFnArgs with
      -- A relator is a 1-cell like an arrow is, and the note writes it with the same `⟶`: the two
      -- categories it runs between, source first, as `Relator`'s own parameters order them.
      | (``Freyd.Alg.Relator, args) =>
        if h : args.size ≥ 2 then return (← plain args[0]) ++ " ⟶ " ++ (← plain args[1])
        else throwError "{declName} : {← Meta.ppExpr body} is a partially applied relator"
      | _ => throwError "{declName} : {← Meta.ppExpr body} is neither an arrow's hom type, a \
          relator between two categories, nor an (in)equation between arrows — it has no one type \
          to render"

/-- The file a note cell `#include`s: the type as typst inline raw, under the same
    `lean:<decl>@<key>` marker the row citing that declaration carries. -/
def file (declName : Name) : MetaM String := do
  let ty ← render declName
  let some ci := (← getEnv).find? declName | throwError "no such declaration: {declName}"
  return "// GENERATED by `diag-export --type` — do not edit; regenerate with\n\
    //   ./scripts/diag-export --type " ++ declName.toString ++ "\n\
    // cert: (lean: \"" ++ declName.toString ++ "@" ++ hex8 (← stmtKey ci) ++ "\")\n`"
    ++ ty ++ "`\n"

end Freyd.TypeRender
