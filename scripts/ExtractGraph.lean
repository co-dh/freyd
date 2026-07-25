/- Extract the declaration graph of the Freyd library.
   Run from repo root:  lake env lean --run scripts/ExtractGraph.lean
   Output: graph/decls.tsv    (name  kind  file  line  type  doc-first-line  key  size)
           graph/inline.tsv   (decl  lemma-it-restates  statement-nodes  proof-nodes  proof-shape)
           graph/deps.tsv     (src  dst)
           graph/imports.tsv  (module  imported-module)
   The doc column is the decl's own `/-- -/` first line; when it has none (≈26% of decls, mostly
   lemmas grouped under a shared header), we fall back to the nearest `/-! ### … -/` section-header
   title scraped from source — group context, not a per-decl doc, but far better than blank.
   The `key` column is the alpha/universe-normalised statement hash: equal keys = duplicate
   declarations (see `declKey`), which is what `scripts/dep_dup.py` groups on.
   Names have the ubiquitous `Freyd.` prefix stripped (8794/8802 decls carry it); the
   only root-level names left as-is are the `Cat` typeclass fields and the tool `main`.
   Edges are true proof-level dependencies (constants of the elaborated type + proof term,
   the same data `#print axioms` walks), not import-level or syntactic references.
   Orphan modules (not imported by the root `Freyd`) are loaded each in its own
   environment — two orphans may define the same constant name, so they cannot
   share one environment. Core-only: reads the already-built .olean files. -/
import Lean
open Lean

def kindOf : ConstantInfo → Option String
  | .thmInfo _    => some "thm"
  | .defnInfo _   => some "def"
  | .axiomInfo _  => some "axiom"
  | .inductInfo _ => some "ind"
  | .opaqueInfo _ => some "opaque"
  | _             => none   -- ctors/recursors are folded into their inductive below

def modToPath (m : Name) (ext : String) : System.FilePath :=
  System.FilePath.mk (m.toString.replace "." "/" ++ "." ++ ext)

/-- All module names under dir (source of truth = .lean files, so orphans count too). -/
partial def collectMods (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then
      out := out ++ (← collectMods e.path (pre.str e.fileName))
    else if e.path.extension == some "lean" then
      out := out.push (pre.str (e.path.fileStem.getD ""))
  return out

/-- Drop the ubiquitous `Freyd.` namespace prefix so graph node names read short.
    Both endpoints of every edge and every decl name go through this, keeping the two
    files join-consistent. `Cat.*` and `main` don't start with `Freyd.`, so they're untouched. -/
def shortName (n : Name) : String :=
  let s := n.toString
  if s.take 6 == "Freyd." then (s.drop 6).toString else s

abbrev Row := Name × String × Name × Nat            -- name, kind, module, line

/-- The columns that need the environment: the pretty-printed type and docstring (a `MetaM` run),
    plus the duplicate key and term size (pure). -/
structure Ann where
  type : String
  doc : String
  key : UInt64
  size : Nat

/-- Drop `mdata` (source positions and elaborator residue): it hashes as a node of its own but says
    nothing about the statement. Binder names need no erasing — `Expr.hash` mixes only the depth and
    the child hashes at a binder, so a hash is alpha-invariant already. -/
partial def stripMData : Expr → Expr
  | .forallE n t b bi => .forallE n (stripMData t) (stripMData b) bi
  | .lam n t b bi     => .lam n (stripMData t) (stripMData b) bi
  | .letE n t v b nd  => .letE n (stripMData t) (stripMData v) (stripMData b) nd
  | .app f a          => .app (stripMData f) (stripMData a)
  | .mdata _ e        => stripMData e
  | .proj s i e       => .proj s i (stripMData e)
  | e                 => e

/-- The binder names of `e`'s leading `∀` telescope. For a constructor type these are the structure's
    field names, and since `Expr.hash` cannot see them they must be mixed into an inductive's key
    separately: `RelObj.carrier` and `Alg.RelMapObj.obj` are both one-field wrappers over `Type u`,
    and only the field name distinguishes them. -/
partial def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- `e` with universe parameters renamed to positional `u0, u1, …`, so that a lemma generalised over
    `{u v}` and its copy over `{v u}` still compare equal. -/
def normLevels (levelParams : List Name) (e : Expr) : Expr :=
  e.instantiateLevelParams levelParams
    (levelParams.mapIdx fun i _ => .param (.mkSimple s!"u{i}"))

/-- Number of *distinct* nodes in `e`'s DAG. Counting structurally would re-walk shared subterms and
    blow up exponentially on proof terms, so nodes already seen are skipped (`Expr`'s cached hash and
    pointer-fast `BEq` make the set cheap). Reported as the `size` column and used to tell a real
    duplicated body from a one-constant alias. -/
partial def dagSize (root : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack := [root]
  let mut n := 0
  while true do
    match stack with
    | [] => break
    | e :: rest =>
      stack := rest
      if seen.contains e then continue
      seen := seen.insert e
      n := n + 1
      match e with
      | .app f a => stack := f :: a :: stack
      | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
      | .letE _ t v b _ => stack := t :: v :: b :: stack
      | .mdata _ x | .proj _ _ x => stack := x :: stack
      | _ => pure ()
  return n

/-! ### Statements a proof re-proves inline

The elaborator compiles `have h : T := e; body` into `(fun h : T => body) e`, and `let` into `.letE`.
So every intermediate statement a proof establishes on its way is sitting in its proof term, and can
be compared against the top-level theorems: a match means the proof re-derived a lemma the library
already has.  This finds INDEPENDENT re-derivations — the proofs need not resemble each other at all,
which is why neither the statement-key pass nor a literal clone hash can see them. -/

/-- Positions in `ctx` (indices from the innermost binder outward) that `e` refers to, where `e` sits
    under `depth` binders of its own. -/
private partial def ctxRefs (ctx depth : Nat) (e : Expr) (acc : Std.HashSet Nat) : Std.HashSet Nat :=
  if !e.hasLooseBVars then acc else
  match e with
  | .bvar d => if d ≥ depth && d - depth < ctx then acc.insert (d - depth) else acc
  | .app f a => ctxRefs ctx depth a (ctxRefs ctx depth f acc)
  | .lam _ t b _ | .forallE _ t b _ => ctxRefs ctx (depth + 1) b (ctxRefs ctx depth t acc)
  | .letE _ t v b _ => ctxRefs ctx (depth + 1) b (ctxRefs ctx depth v (ctxRefs ctx depth t acc))
  | .mdata _ x | .proj _ _ x => ctxRefs ctx depth x acc
  | _ => acc

/-- Renumber `e`'s references to the binder context after the unused binders have been dropped.
    `rank p` is the position `p` binder's index among the kept ones; `dropped` is how many kept
    binders are already bound outside `e`. `none` if `e` reaches a binder that was not kept. -/
private partial def remapRefs (ctx : Nat) (rank : Nat → Option Nat) (base dropped depth : Nat)
    (e : Expr) : Option Expr :=
  if !e.hasLooseBVars then some e else
  match e with
  | .bvar d =>
    if d < depth then some (.bvar d)
    else if d - depth ≥ ctx then some e
    else do
      let k ← rank (base + (d - depth))
      guard (k ≥ dropped)
      some (.bvar (depth + k - dropped))
  | .app f a => return .app (← remapRefs ctx rank base dropped depth f)
                           (← remapRefs ctx rank base dropped depth a)
  | .lam n t b bi => return .lam n (← remapRefs ctx rank base dropped depth t)
                               (← remapRefs ctx rank base dropped (depth + 1) b) bi
  | .forallE n t b bi => return .forallE n (← remapRefs ctx rank base dropped depth t)
                                   (← remapRefs ctx rank base dropped (depth + 1) b) bi
  | .letE n t v b nd => return .letE n (← remapRefs ctx rank base dropped depth t)
                                  (← remapRefs ctx rank base dropped depth v)
                                  (← remapRefs ctx rank base dropped (depth + 1) b) nd
  | .mdata m x => return .mdata m (← remapRefs ctx rank base dropped depth x)
  | .proj s i x => return .proj s i (← remapRefs ctx rank base dropped depth x)
  | _ => some e

/-- Close a sub-statement over exactly the enclosing binders it uses, so it can be compared with a
    top-level theorem's type.  `ctx` runs innermost-LAST.  Binders it does not mention are dropped —
    keeping them would make the closed statement strictly more general than the lemma it restates,
    and the two would never match. -/
private def closeStatement (ctx : Array (Name × Expr)) (t : Expr) : Option Expr := Id.run do
  let size := ctx.size
  let at? (p : Nat) : Option (Name × Expr) := ctx[size - 1 - p]?
  -- A used binder's own type may mention outer binders, so grow the set to a fixpoint.
  let mut used := ctxRefs size 0 t {}
  let mut changed := true
  while changed do
    changed := false
    for p in used.toList do
      if let some (_, ty) := at? p then
        for q in (ctxRefs size 0 ty {}).toList do
          let q := p + 1 + q                       -- `ty` sits one binder outside position `p`
          if q < size && !used.contains q then used := used.insert q; changed := true
  let kept := (used.toList.filter (· < size)).mergeSort (· < ·)
  let rank (p : Nat) : Option Nat := kept.idxOf? p
  let some body := remapRefs size rank 0 0 0 t | return none
  let mut result := body
  for (p, j) in kept.zipIdx do
    let some (name, ty) := at? p | return none
    let some domain := remapRefs size rank (p + 1) (j + 1) 0 ty | return none
    result := .forallE name domain result .default
  return some result

/-- Statement hash identifying duplicates: two declarations with the same key state the same thing.

    Theorems and axioms key on the type alone: proof irrelevance means the same statement IS the same
    fact however it was proved — which is exactly the case `dep_dup.py`'s dependency-similarity pass
    cannot see, since two independent proofs have disjoint dependency rows. Definitions key on type
    AND value: a shared type is weak evidence for a `def` (many share one), an identical body is a
    copy-paste.

    An inductive has no value, and its *former's* type says nothing about its fields — keying on that
    collided every class of the same arity (41 of them at `(𝒞 : Type u) → [Cat 𝒞] → Type (max u v)`,
    from `HasTerminal` to `Topos`). Key on the constructor types instead, with references to the
    mutual block replaced by positional markers so that two structures are compared by their fields
    rather than separated by their own names — and on the constructor and field *names* too, which no
    `Expr` hash sees, without which every pair of equal-arity enumerations (`Quant` with `Alg.Two`)
    and every pair of like-typed wrappers (`RelObj` with `Alg.RelMapObj`) merged. -/
def declKey (env : Environment) (ci : ConstantInfo) : UInt64 :=
  let canon (e : Expr) : UInt64 := (stripMData (normLevels ci.levelParams e)).hash
  match ci with
  | .thmInfo _ | .axiomInfo _ => canon ci.type
  | .inductInfo ind =>
    let deSelf (e : Expr) : Expr := e.replace fun
      | .const n _ => (ind.all.idxOf? n).map fun i => .const (.mkSimple s!"#self{i}") []
      | _ => none
    let ctorKey (h : UInt64) (c : Name) : UInt64 :=
      let ty := deSelf ((env.find? c).map (·.type) |>.getD default)
      let ctorName := match c with | .str _ s => s | _ => ""
      mixHash (mixHash h (mixHash (hash ctorName) (hash (binderNames ty)))) (canon ty)
    ind.ctors.foldl ctorKey (mixHash (hash ind.numParams) (canon (deSelf ci.type)))
  | _ => mixHash (canon ci.type) ((ci.value?.map canon).getD 0)

def oneLine (s : String) : String := Id.run do
  let mut out := ""
  let mut sp := false
  for c in s.toList do
    if c == ' ' || c == '\t' || c == '\n' then sp := true
    else
      if sp && !out.isEmpty then out := out.push ' '
      out := out.push c
      sp := false
  return out

-- Char-level string helpers (dodge the String/Slice deprecation churn in this Lean version).
private def isWs (c : Char) : Bool := c == ' ' || c == '\t'
private def trimC (cs : List Char) : List Char :=
  (cs.dropWhile isWs).reverse.dropWhile isWs |>.reverse

/-- The title of a `/-! … -/` module-doc block on `line` (with `next` its following source line),
    or `none` if `line` is not such a block. Strips the `/-!` / trailing `-/` / leading `### `. -/
def cleanHeader (line next : String) : Option String :=
  let cs := trimC line.toList
  if cs.take 3 == ['/','-','!'] then
    let body := trimC (cs.drop 3)
    let body := if body.isEmpty then trimC next.toList else body     -- bare `/-!` → use next line
    let body := if body.reverse.take 2 == ['/','-'] then trimC (body.dropLast.dropLast) else body
    let body := body.dropWhile (fun c => c == '#' || isWs c)          -- markdown `### `
    if body.isEmpty then none else some (String.ofList body)
  else none

/-- Nearest `/-! ### … -/` section-header title at or above 1-indexed `line` in `lines`.
    Freyd documents groups of lemmas with these blocks rather than a per-lemma `/-- -/`, so this
    recovers the section context for the ~26% of decls that carry no docstring of their own. -/
partial def sectionHeader (lines : Array String) (line : Nat) : Option String :=
  let rec go (i : Nat) : Option String :=
    match cleanHeader (lines[i]?.getD "") (lines[i+1]?.getD "") with
    | some h => some h
    | none   => if i == 0 then none else go (i - 1)
  if lines.isEmpty || line < 2 then none else go (min (line - 2) (lines.size - 1))

/-- What a sub-proof looks like, which is what decides whether a hit is worth acting on.  Node count
    cannot decide it: an elaborated `rfl` embeds the whole statement and so weighs as much as a real
    derivation (50 nodes for `sigmaRel_sliceMem_colA`, against 28 for a genuine one).  A `rfl` or a
    single call has nothing to collapse — the statement is duplicated, the proof is not. -/
private def proofShape (proof : Expr) : String := Id.run do
  let mut binder := false
  let mut seen : Std.HashSet Expr := {}
  let mut stack := [proof]
  while true do
    match stack with
    | [] => break
    | e :: rest =>
      stack := rest
      if seen.contains e then continue
      seen := seen.insert e
      match e with
      | .lam .. | .letE .. => binder := true; break
      | .app f a => stack := f :: a :: stack
      | .mdata _ x | .proj _ _ x => stack := x :: stack
      | .forallE _ t b _ => stack := t :: b :: stack
      | _ => pure ()
  if binder then return "derivation"
  match proof.getAppFn with
  | .const n _ => return if n == ``rfl || n == ``Eq.refl then "rfl" else "call"
  | _ => return "call"

/-- Statements `ci`'s proof establishes inline that the library already has as a theorem: for each
    `have`/`let`, close its type over the binders it uses, key it exactly as a theorem type is keyed,
    and look it up.  A hit whose sub-proof actually calls that theorem is the declaration USING it —
    only the others re-proved it.  Returns (lemma, statement size, sub-proof size) per hit.

    Sizes gate the report: below the floor the inline proof is cheaper than the call, and rewriting it
    to one would be churn, not de-duplication. -/
private def inlineRestatements (thms : Std.HashMap UInt64 Name) (self : Name) (ci : ConstantInfo)
    (minStatement := 15) (minProof := 10) : Array (Name × Nat × Nat × String) := Id.run do
  let some value := ci.value? | return #[]
  let mut hits := #[]
  let mut seen : Std.HashSet Expr := {}
  let mut stack := [(#[], value)]
  while true do
    match stack with
    | [] => break
    | (ctx, e) :: rest =>
      stack := rest
      if seen.contains e then continue
      seen := seen.insert e
      -- The three shapes an intermediate statement takes in a proof term.  A tactic-mode `have` is
      -- the third: it compiles to `letFun v (fun h : t => body)`, NOT to a beta-redex, so matching
      -- only the redex finds almost nothing (one hit across the whole library).
      let sub? : Option (Name × Expr × Expr × Expr) := match e with
        | .app (.lam n t b _) proof => some (n, t, proof, b)
        | .letE n t proof b _ => some (n, t, proof, b)
        | _ => match e.getAppFn, e.getAppArgs with
          | .const ``letFun _, #[_, _, proof, .lam n t b _] => some (n, t, proof, b)
          | _, _ => none
      match sub? with
      | some (n, t, proof, body) =>
        if let some closed := closeStatement ctx t then
          if let some lemmaName := thms[(stripMData (normLevels ci.levelParams closed)).hash]? then
            if lemmaName != self && !(proof.getUsedConstants.contains lemmaName) then
              let statementSize := dagSize closed
              let proofSize := dagSize proof
              if statementSize ≥ minStatement && proofSize ≥ minProof then
                hits := hits.push (lemmaName, statementSize, proofSize, proofShape proof)
        stack := (ctx, t) :: (ctx, proof) :: (ctx.push (n, t), body) :: stack
      | none =>
        match e with
        | .app f a => stack := (ctx, f) :: (ctx, a) :: stack
        | .lam n t b _ | .forallE n t b _ => stack := (ctx, t) :: (ctx.push (n, t), b) :: stack
        | .mdata _ x | .proj _ _ x => stack := (ctx, x) :: stack
        | _ => pure ()
  return hits

/-- Pretty-printed type, first docstring line and duplicate key for each row (needs a MetaM run).
    Strip the ubiquitous `Freyd.` prefix from the printed type and doc text (same reason
    `shortName` strips it from the decl/edge names) so the whole tsv reads prefix-free. These
    columns are display-only, so a blunt substring strip is fine and also catches names the
    pretty-printer leaves fully qualified (inaccessible `✝` auxiliaries) and literal docstrings. -/
def annotate (env : Environment) (rows : Array Row) : IO (Array (Row × Ann)) := do
  let ctx : Core.Context := { fileName := "<extract>", fileMap := default }
  -- ONE `CoreM.toIO` PER decl. Batching many decls into a single CoreM run (a `mapM` inside one
  -- `toIO`) accumulates per-decl residue in `Core.State` (delaborator/pp caches) that is freed only
  -- when the run ends — that pile-up was the whole OOM: ~800 decls in one run peaked at 24 GB. A
  -- fresh run per decl releases the residue immediately (Lean is refcounted), holding the pass flat
  -- at ~3.2 GB. Verified by bisection: import+extract+edge-DFS+all-9317-ppExpr, one toIO each, 3.2 GB.
  rows.mapM fun row@(n, _, _, _) => do
    let one : CoreM Ann := do
      let ci := (env.find? n).get!
      let ty ← try
          pure ((oneLine (toString (← Meta.MetaM.run' (Meta.ppExpr ci.type)))).replace "Freyd." "")
        catch _ => pure ""
      let doc := (((← findDocString? env n).getD "").splitOn "\n" |>.headD "").replace "Freyd." ""
      return { type := ty, doc := oneLine doc, key := declKey env ci,
               size := (ci.value?.map dagSize).getD 0 }
    Prod.mk row <$> Prod.fst <$> one.toIO ctx { env }

/-- Rows and edges for the declarations of `env` living in modules satisfying `wanted`. -/
def extract (env : Environment) (wanted : Name → Bool) :
    Array Row × Array (Name × Name) := Id.run do
  let freydMod? (n : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if `Freyd |>.isPrefixOf m then some m else none
  -- pass 1: user-written declarations in Freyd modules (targets for edges). Fold directly over the
  -- constant `SMap` instead of `env.constants.toList` — that list (~100k entries, core Lean
  -- included) was a needless transient allocation built once per imported environment.
  let kept : Std.HashMap Name (String × Name × Nat) :=
    env.constants.fold (fun kept n ci => Id.run do
      if n.isInternalDetail then return kept
      let some kind := kindOf ci | return kept
      let some m := freydMod? n | return kept
      -- compiler-generated helpers (injEq, noConfusion, …) carry no declaration range
      let some r := declRangeExt.find? env n | return kept
      -- `instance` and `abbrev` declarations are `.defnInfo` too (kindOf → "def"); relabel from the
      -- instance-attribute and reducibility extensions so they're distinguishable in the graph. An
      -- `abbrev` naming an existing term is a deliberate alias, not duplication, so the report needs
      -- to tell the two apart.
      let kind :=
        if kind != "def" then kind
        else if Meta.isInstanceCore env n then "instance"
        else match getReducibilityStatusCore env n with
          | .reducible => "abbrev"
          | _ => "def"
      return kept.insert n (kind, m, r.range.pos.line)) {}
  -- pass 2: rows for wanted modules; edges routed through generated/internal constants. Iterate the
  -- ~9k `kept` decls directly (was: a second full scan of all ~100k constants), `env.find?`ing each
  -- `ConstantInfo` on demand.
  let mut rows := #[]
  let mut edges := #[]
  for (src, kind, m, line) in kept do
    unless wanted m do continue
    rows := rows.push (src, kind, m, line)
    let some ci := env.find? src | continue
    let raw := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut stack := raw.toList
    let mut visited : Std.HashSet Name := {}
    while true do
      match stack with
      | [] => break
      | n :: rest =>
        stack := rest
        if visited.contains n || n == src then continue
        visited := visited.insert n
        if kept.contains n then
          edges := edges.push (src, n)
        else if let some ci' := env.find? n then
          match ci' with
          | .ctorInfo _ | .recInfo _ => stack := n.getPrefix :: stack
          | _ =>
            -- expand aux constants (match_, proof_, eq lemmas, …) but only inside Freyd
            if (freydMod? n).isSome then
              stack := (ci'.type.getUsedConstants
                ++ (ci'.value?.map (·.getUsedConstants)).getD #[]).toList ++ stack
  return (rows, edges)

-- loadExts := true on the imports below: without it, environment-extension state (incl. the
-- instance registry `Meta.instanceExtension` used by `isInstanceCore` in `extract`) is left unloaded.

/-- Import the root `Freyd` closure, extract its rows/edges, annotate. Wrapped in its own function
    so `envRoot` (the whole-library environment — the single biggest object here) is freed when this
    returns, BEFORE the orphan loop imports anything. Previously `envRoot` stayed live as a `main`
    local across the whole orphan loop, so root + orphan environments coexisted — roughly doubling
    peak memory, a direct OOM contributor. -/
def processRoot : IO (Array (Row × Ann) × Array (Name × Name) × Std.HashSet Name ×
    Array (Name × Name × Nat × Nat × String)) := do
  let envRoot ← importModules #[{ module := `Freyd }] {} (trustLevel := 1024) (loadExts := true)
  let done : Std.HashSet Name :=
    .ofArray (envRoot.header.moduleNames.filter (`Freyd |>.isPrefixOf ·))
  let (rows, edges) := extract envRoot done.contains
  let annotated ← annotate envRoot rows
  -- The inline scan runs on the root closure only (223 of 224 modules): a `have` can only restate a
  -- theorem the file can see, and the whole closure is in this one environment.
  let thms : Std.HashMap UInt64 Name := annotated.foldl (init := {}) fun table ((n, kind, _, _), a) =>
    if kind == "thm" then table.insert a.key n else table
  let mut inline := #[]
  for ((n, _, _, _), _) in annotated do
    if let some ci := envRoot.find? n then
      for (lemmaName, statementSize, proofSize, shape) in inlineRestatements thms n ci do
        inline := inline.push (n, lemmaName, statementSize, proofSize, shape)
  return (annotated, edges, done, inline)

/-- Same, for one orphan module (each in its own environment, since two orphans may define the same
    constant name). The function boundary frees each orphan environment before the next import. -/
def processOrphan (m : Name) (done : Std.HashSet Name) :
    IO (Array (Row × Ann) × Array (Name × Name) × Array Name) := do
  let env ← importModules #[{ module := m }] {} (trustLevel := 1024) (loadExts := true)
  let mods := env.header.moduleNames.filter fun x =>
    (`Freyd |>.isPrefixOf x) && !done.contains x
  let (r, e) := extract env (Std.HashSet.ofArray mods).contains
  return (← annotate env r, e, mods)

/-- Parse `import Freyd.X failed, environment already contains …` → the module `Freyd.X` to isolate. -/
def parseOffender (msg : String) : Option Name :=
  match (msg.splitOn " ").dropWhile (· != "import") with
  | _ :: modStr :: _ => some modStr.toName
  | _ => none

/-- Import all `mods` in ONE `importModules` call, returning that environment plus the modules that
    had to be peeled out. `importModules` retains ~350 MB per call that is never freed, so calling it
    once per orphan (46×) leaked ~16 GB and OOM-killed the process; one combined call keeps it flat.
    The rare module that redefines a constant already in another's closure (e.g. `S1_49`'s
    `comp_heq`) makes the combined import throw — peel that module out and retry the rest. -/
partial def importOrphans (mods : Array Name) : IO (Environment × Array Name) := do
  let mut batch := mods
  let mut isolated : Array Name := #[]
  while true do
    try
      let env ← importModules (batch.map fun m => { module := m }) {}
        (trustLevel := 1024) (loadExts := true)
      return (env, isolated)
    catch e =>
      match parseOffender (toString e) with
      | some bad => if batch.contains bad then
                      isolated := isolated.push bad; batch := batch.filter (· != bad)
                    else throw e
      | none => throw e
  throw (IO.userError "importOrphans: unreachable")

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let all ← collectMods "Freyd" `Freyd
  let mut built := #[]
  let mut skipped := #[]
  for m in all do
    if (← (".lake/build/lib/lean" / modToPath m "olean").pathExists)
    then built := built.push m else skipped := skipped.push m
  unless skipped.isEmpty do
    IO.eprintln s!"warning: {skipped.size} modules have no .olean (run lake build): {skipped.toList}"
  -- root closure first, then ALL orphans (modules with an olean not reached by the root import) in a
  -- single combined import. `importModules` retains ~350 MB per call permanently, so the old
  -- one-env-per-orphan loop leaked ~16 GB over 46 orphans → OOM. `importOrphans` does it in one call
  -- (peeling out the few name-colliders to import singly), holding the whole run to ~5 GB.
  let (rows₀, edges₀, done₀, inline) ← processRoot
  let mut rows := rows₀
  let mut edges := edges₀
  let mut done := done₀
  let orphanMods := built.filter (!done.contains ·)
  let mut orphans := 0
  unless orphanMods.isEmpty do
    let (batchEnv, isolated) ← importOrphans orphanMods
    orphans := 1
    let fresh : Std.HashSet Name := .ofArray
      (batchEnv.header.moduleNames.filter fun x => (`Freyd |>.isPrefixOf x) && !done.contains x)
    let (r, e) := extract batchEnv fresh.contains
    rows := rows ++ (← annotate batchEnv r)
    edges := edges ++ e
    done := batchEnv.header.moduleNames.foldl
      (fun d x => if `Freyd |>.isPrefixOf x then d.insert x else d) done
    -- the few isolated (name-colliding) orphans, each in its own environment
    for m in isolated do
      if done.contains m then continue
      orphans := orphans + 1
      let (r, e, mods) ← processOrphan m done
      rows := rows ++ r
      edges := edges ++ e
      done := mods.foldl (·.insert ·) done
  IO.FS.createDirAll "graph"
  let sorted := (rows.map fun ((n, k, m, l), a) =>
      ((modToPath m "lean").toString, l, shortName n, k, a))
    |>.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  -- Fill empty docs with the nearest `/-! ### … -/` section header scraped from source (94% of
  -- undocumented decls sit under one). Group-level context, not a per-decl doc, but far better than
  -- blank; only decls with no header above (and auto parent-projections) stay empty. Each source
  -- file is read at most once via `srcCache`.
  let mut srcCache : Std.HashMap String (Array String) := {}
  let mut filled := 0
  let mut withHdr := #[]
  for (f, l, n, k, a) in sorted do
    if !a.doc.isEmpty then withHdr := withHdr.push (f, l, n, k, a); continue
    let ls ← match srcCache.get? f with
      | some ls => pure ls
      | none =>
        let ls ← try pure (← IO.FS.lines f) catch _ => pure #[]
        srcCache := srcCache.insert f ls
        pure ls
    let doc' := (sectionHeader ls l).getD ""
    if !doc'.isEmpty then filled := filled + 1
    withHdr := withHdr.push (f, l, n, k, { a with doc := doc' })
  let sorted := withHdr
  IO.FS.withFile "graph/decls.tsv" .write fun h => do
    for (f, l, n, k, a) in sorted do
      h.putStrLn s!"{n}\t{k}\t{f}\t{l}\t{a.type}\t{a.doc}\t{a.key}\t{a.size}"
  -- module → directly imported module: lets the report say whether a proposed forward target is
  -- upstream of its caller (safe) or downstream (would need the move the skill warns about).
  IO.FS.withFile "graph/imports.tsv" .write fun h => do
    for m in built do
      for line in ← IO.FS.lines (modToPath m "lean") do
        let l := line.trimAscii.toString
        if l.startsWith "import " then h.putStrLn s!"{m}\t{(l.drop 7).trimAscii}"
  -- declaration whose proof re-proves `lemma` inline, with the sizes and the sub-proof's shape
  -- (only a `derivation` has a proof to collapse; `rfl`/`call` duplicate the statement alone)
  IO.FS.withFile "graph/inline.tsv" .write fun h => do
    for (decl, lemmaName, statementSize, proofSize, shape) in inline do
      h.putStrLn s!"{shortName decl}\t{shortName lemmaName}\t{statementSize}\t{proofSize}\t{shape}"
  let es := (edges.map fun (s, t) => s!"{shortName s}\t{shortName t}") |>.qsort (· < ·) |>.toList.eraseReps.toArray
  IO.FS.withFile "graph/deps.tsv" .write fun h => do
    for e in es do h.putStrLn e
  IO.println s!"{sorted.size} declarations, {es.size} edges ({done.size} modules, {orphans} orphan roots); {filled} docs recovered from section headers"
