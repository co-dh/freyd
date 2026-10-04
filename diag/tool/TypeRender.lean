/-
  `TypeRender` — a declaration's TYPE, written the way the note writes it.

  The note's tables carry a *type* column beside every definition, written by `#leant`:
  `[[Int]]⟶[[Int]]` beside `R≜length≤length°`.  A hand-typed cell is a claim nobody checks, and it is exactly the claim
  the environment can settle — `R X`'s hom type IS `dSched X ⟶ dSched X`, and the printing-only
  unexpanders of `AOP` are what turn that into the note's brackets.  So the cell is GENERATED from the
  declaration the row already cites, and carries a `lean:<decl>@<key>` marker of its own: a statement
  that moves under the note fails `cite-check` here too.

  WHAT "THE TYPE" IS, read off the ELABORATED statement and nothing else: an arrow-valued `def` has
  its hom, an (in)equation between arrows has the hom its two sides share, a relator-valued `def`
  runs between two categories, and any other non-theorem — a plain function, a `Type`, a `Prop`
  predicate — has the Lean type of the name cell's term.  A theorem that is no (in)equation gets an
  error naming the statement, never a guessed cell.

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
  -- An inductive keys on its CONSTRUCTORS, as `lean-refactor`'s `statementKey` does (the index
  -- this key is checked against): its own block replaced by positional markers, and each
  -- constructor's name and binder names mixed in.
  | .inductInfo ind =>
    let deSelf (e : Expr) : Expr := e.replace fun
      | .const n _ => (ind.all.idxOf? n).map fun i => .const (.mkSimple s!"#self{i}") []
      | _ => none
    let rec names : Expr → List Name
      | .forallE n _ b _ => n :: names b
      | _ => []
    let env ← getEnv
    ind.ctors.foldlM (init := mixHash (hash ind.numParams) (canon (deSelf ci.type))) fun h c => do
      let some cc := env.find? c | throwError "{ci.name}: constructor {c} is not in the environment"
      let ty := deSelf cc.type
      let ctorName := match c with | .str _ s => s | _ => ""
      return mixHash (mixHash h (mixHash (hash ctorName) (hash (names ty)))) (canon ty)
  | _ => return mixHash (canon ci.type) ((ci.value?.map canon).getD 0)

/-- The low 32 bits as `cite-check` spells them: 8 hex digits, zero-padded. -/
def hex8 (k : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 (k.toNat % 4294967296))
  "".pushn '0' (8 - s.length) ++ s

/-! ### The type -/

/-- A hom in the note's spelling: each end through `label`, the rule every route's text goes
    through, and the arrow set tight as the note sets it, `[A]⟶[B]`. -/
private def hom? (t : Expr) : MetaM (Option String) := do
  let some (a, b) := homObjs? t | return none
  return some ((← label a) ++ "⟶" ++ (← label b))

/-- A FACTOR STEP `f<k>`, `k ≥ 1`: the k-th factor of the composite the step follows. -/
def factorIdx? (s : String) : Option Nat :=
  if s.startsWith "f" then (String.toNat? (toString (s.drop 1))).filter (· ≥ 1) else none

/-- The declaration's type in the note's spelling.  Run under `withDeclScope` and printed by
    `plain`, so the same delaborator, namespaces and unexpanders the string route draws its labels
    with print this cell. -/
def render (declName : Name) (sides : List String := []) : MetaM String := withDeclScope declName do
  let nameOnly := sides.contains "name"
  let some ci := (← getEnv).find? declName | throwError "no such declaration: {declName}"
  -- NOT `forallTelescopeReducing`: a hom of `RelSet` reduces to `A → B → Prop`, so reducing walks
  -- straight through the arrow this is here to print and leaves `Prop` as the body of every def.
  Meta.forallTelescope ci.type fun xs body => do
    -- `nameOnly`: the TERM the type belongs to instead of the type — an (in)equation's left side,
    -- else the declaration at its own binders — printed by `labelT`, the formula route's printer, so
    -- the name cell reads as the formula beside it (`Λ(F(∋,𝟙))`, `step`); typst content, since a
    -- `Λ` sets as a fraction.
    let name (t : Expr) (ty : String) : MetaM String := do
      if nameOnly then return "#" ++ (← labelT t).bare.typst else return ty
    -- A SUBTERM's type: `.lhs`/`.rhs` a side, then `.f<k>` its k-th factor in diagram order — so a
    -- table walking a composite stage by stage reads every stage's type off the one statement.
    let steps := sides.filter (· != "name")
    if let s₀ :: rest := steps then
      let some (_, l, r) ← splitM body |
        throwError "{declName}: `.{s₀}` selects a side, but {← Meta.ppExpr body} is no (in)equation"
      let side ← match s₀ with
        | "lhs" => pure l | "rhs" => pure r
        | s => throwError "{declName}: a subterm selector starts at `.lhs` or `.rhs`, not `.{s}`"
      let t ← rest.foldlM (init := side) fun (u : Expr) (s : String) => do
        let some k := factorIdx? s |
          throwError "{declName}: selector step `.{s}` is not a factor `.f<k>` (k ≥ 1)"
        let fs := compFactors u
        let some f := fs[k - 1]? |
          throwError "{declName}: `.{s}` asks for factor {k} of {← Meta.ppExpr u}, which has {fs.size}"
        pure f
      let ty ← Meta.inferType t
      let some s ← hom? ty |
        throwError "{declName}: the selected subterm {← Meta.ppExpr t} has type {← Meta.ppExpr ty}, \
          not an arrow of a category"
      return ← name t s
    -- An (in)equation is a statement ABOUT arrows, and its two sides share one hom: read it off the
    -- left, which is the side the note's `definition` column spells.
    match ← splitM body with
    | some (sym, l, r) =>
      -- An equation states its type as `Eq`'s first argument, which an ascription in the statement
      -- sets; the left side's inferred type forgets it.
      let t ← match body.eq? with | some (ty, _, _) => pure ty | none => Meta.inferType l
      let some s ← hom? t |
        throwError "{declName} states {← Meta.ppExpr l} {sym} {← Meta.ppExpr r}, whose sides are \
          {← Meta.ppExpr t} and not arrows of a category — it has no hom type to render"
      name l s
    | none =>
      let self := mkAppN (.const declName (ci.levelParams.map .param)) xs
      if let some s ← hom? body then name self s else
      match body.getAppFnArgs with
      | (``Freyd.Alg.Relator, args) =>
        if h : args.size ≥ 2 then name self ((← plain args[0]) ++ "⟶" ++ (← plain args[1]))
        else throwError "{declName} : {← Meta.ppExpr body} is a partially applied relator"
      -- A binary relator runs from the square of its category: `F : 𝒜×𝒜⟶𝒜`.
      | (``Freyd.Alg.BiRelator, args) =>
        if h : args.size ≥ 1 then
          let c ← plain args[0]
          name self (c ++ "×" ++ c ++ "⟶" ++ c)
        else throwError "{declName} : {← Meta.ppExpr body} is a partially applied binary relator"
      -- A THEOREM's body is a statement, not a type: printing it here would repeat the formula cell.
      | _ => do
        if ci matches .thmInfo _ then
          throwError "{declName} : {← Meta.ppExpr body} is a theorem but neither an (in)equation \
            between arrows nor about a hom — it has no type to render"
        -- ANY OTHER DECLARATION has the type Lean gave it: `sqr(n) : Int`, `Para(Word) : Type`,
        -- `IsThinlist(Q,thinlist) : Prop`.  The name cell applies it to its OWN binders only; an
        -- arrow the signature wrote `A → B` has a hygienic binder and stays in the type (`hd : J → C`).
        -- An INSTANCE binder is hygienic too, but is a constraint and no arrow: it is passed over,
        -- never left in the type as `[inst : …] →`.
        let rec named : Expr → Nat
          | .forallE n _ b bi => if n.hasMacroScopes && !bi.isInstImplicit then 0 else named b + 1
          | _ => 0
        Meta.forallBoundedTelescope ci.type (named ci.type) fun ys ty =>
          do name (mkAppN (.const declName (ci.levelParams.map .param)) ys) (← plain ty)

/-- The file a note cell `#include`s: the type as typst inline raw.  The `lean:<decl>@<key>` marker
    above it is `DiagExport.certLine`'s, written for every route at the one place the file is. -/
def file (declName : Name) (sides : List String := []) : MetaM String := do
  let r ← render declName sides
  return (if sides.contains "name" then r else "`" ++ r ++ "`") ++ "\n"

end Freyd.TypeRender
