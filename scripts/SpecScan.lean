/- Find theorems that are SPECIAL CASES of other theorems (the dedup skill's kind 2).
   Run from repo root:  lake env lean --run scripts/SpecScan.lean
   Outputs:
   * graph/spec.tsv          — direct theorem specializations
   * graph/spec-derived.tsv  — theorem matches requiring local-context search
   * graph/spec-defs.tsv     — exact definition signature/value matches

   Each file has columns:
     specialized  general  discharge  specialized-module  general-module

   The statement-key pass in `ExtractGraph` finds theorems whose types are EQUAL. A specialization
   has a DIFFERENT type — it fixes a parameter, takes a stronger typeclass, or discharges a
   hypothesis — so hashing cannot see it. The check is semantic: unify the two conclusions, then try
   to discharge whatever of the general lemma's binders that leaves, from the special one's context.

   Precision comes from the last filter: `A is an instance of B` is also what "A was PROVED using B"
   looks like, and that is the overwhelming majority of pairs. Only pairs where A's proof never
   mentions B are reported — those are the ones that re-derived what B already says.

   CANDIDATE GENERATION is a `DiscrTree` over conclusions: each theorem is indexed with its binders as
   metavariables, i.e. as a pattern, so `getMatch goal` returns exactly the lemmas that could `apply`
   to that goal. It replaced a hand-rolled (conclusion head, first-argument head) bucket with a
   `bucketCap`, which had two MEASURED recall holes: the cap discarded 1990 of 6003 theorems
   unexamined (`(Eq, Cat.Hom)` alone was a 1225-member bucket, because the refinement key looked at
   the `Eq`'s TYPE argument), and the surviving buckets were checked under ONE bucket-wide heartbeat
   budget that a quadratic pair loop exhausts — after which `catch` dropped that whole bucket's
   findings silently. `DiscrTree` fixes the key (its `star` keys handle "matches anything", so no cap
   is needed) and the budget is now strictly per candidate pair, so a pathological pair costs one
   pair, never a batch of results.

   DISCHARGE of the general lemma's leftover binders: `synthInstance` for instance binders, then a
   hypothesis of the special one. Matches needing `solveByElim` over the local context are retained
   in `spec-derived.tsv`: they are useful evidence, but are not direct specializations and frequently
   compare unrelated injectivity or order lemmas merely because the local context can derive the
   requested binder. Exact definition matches likewise go to `spec-defs.tsv`; they are aliases or
   shared-shape candidates, not theorem specializations.

   Core-only: reads the already-built .olean files. -/
import Freyd
import Lean
open Lean Meta LibrarySearch

/-- Strip a proof's leading binders: `theorem foo (a b) := rfl` elaborates to `fun a b => rfl`, so
    the head constant is only visible underneath them. -/
partial def proofHead : Expr → Expr
  | .lam _ _ b _ => proofHead b
  | .mdata _ e => proofHead e
  | e => e.getAppFn

structure Thm where
  name : Name
  mod : Name
  kind : String
  type : Expr
  value : Expr
  levelParams : List Name
  usedInProof : Std.HashSet Name
  /-- Proved by `rfl`.  Such a statement reduces to reflexivity, so ANY lemma that reduces the same
      way "proves" it and the scan matches it against unrelated siblings — `gs2 A B 0 = A` against
      `gs2 A B 1 = B`, both `rfl`, both `A = A` once reduced.  There is also nothing to save by
      rewriting one into a call. Excluded from both sides of a pair. -/
  provedByRfl : Bool
  /-- Compiler-generated, so never a place to remove duplication.  Two kinds, both MEASURED as
      pure noise here: a `Prop`-valued structure/class field elaborates to a projection THEOREM, so
      the scan reads typeclass inheritance as specialization (`SubclassFoo.bar ⇐ ClassFoo.bar`, or
      `A ⇐ OverHom.w` when `A` restates a field); and constructor injectivity lemmas (`Foo.mk.inj`,
      `Foo.injEq`) are closed by `solveByElim` for almost any equality-of-constructors goal — 114
      of 267 rows before this filter, every one of them from the `solveByElim` step.
      Excluded from both sides. -/
  isGenerated : Bool
  deriving Inhabited

def generatedDeclName (env : Environment) (name : Name) : Bool :=
  let parts := name.toString.splitOn "."
  let tail := parts.getLastD ""
  let compilerTail :=
    ["inj", "injEq", "noConfusion", "noConfusionType", "sizeOf_spec"].contains tail
  let compilerFragment :=
    ["match_", "proof_", "eq_def", ".mk."].any fun needle =>
      (name.toString.splitOn needle).length > 1
  env.isProjectionFn name || compilerTail || compilerFragment ||
    parts.any (·.startsWith "_")

/-- Can `general` be applied to prove `special`?  Unify the conclusions under fresh metavariables for
    `general`'s binders, then discharge the leftovers: instance binders by synthesis, the rest by
    matching a hypothesis of `special` or by `solveByElim` over those hypotheses.  Returns a note
    naming what had to be discharged. -/
structure SpecMatch where
  note : String
  isDef : Bool
  usedDerivation : Bool

def specializes (special general : Thm) : MetaM (Option SpecMatch) := do
  unless special.kind == general.kind do return none
  let generalLevels ← general.levelParams.mapM fun _ => mkFreshLevelMVar
  let generalType := general.type.instantiateLevelParams general.levelParams generalLevels
  forallTelescopeReducing special.type fun hypotheses specialConcl => do
    let (mvars, binderInfos, generalConcl) ← forallMetaTelescopeReducing generalType
    unless ← isDefEq specialConcl generalConcl do return none
    let mut synthesized := 0
    let mut assumed := 0
    let mut derived := 0
    for (mvar, info) in mvars.zip binderInfos do
      if ← mvar.mvarId!.isAssigned then continue
      let wanted ← inferType mvar
      if info == .instImplicit then
        match ← tryCatchRuntimeEx (some <$> synthInstance wanted) (fun _ => pure none) with
        | some inst => unless ← isDefEq mvar inst do return none
                       synthesized := synthesized + 1
        | none => return none
      else
        -- a leftover ordinary binder must come from `special`'s own hypotheses: one of them
        -- directly, or a short elimination search over them.
        let mut found := false
        for hypothesis in hypotheses do
          unless found do
            if ← isDefEq mvar hypothesis then found := true; assumed := assumed + 1
        unless found do
          let ok ← tryCatchRuntimeEx
              (do let goal ← mkFreshExprMVar wanted
                  let remaining ← solveByElim [] false [goal.mvarId!] 4
                  pure (remaining.isEmpty && !(← instantiateMVars goal).hasExprMVar
                        && (← isDefEq mvar goal)))
              (fun _ => pure false)
          unless ok do return none
          derived := derived + 1
    if special.kind == "def" then
      let generalValue := general.value.instantiateLevelParams general.levelParams generalLevels
      unless ← isDefEq special.value generalValue do return none
    let matchKind := if special.kind == "def" then "def signature+value" else "theorem specialization"
    return some {
      note := s!"{matchKind}; {synthesized} instance(s), {assumed} hypothesis(es), {derived} solveByElim"
      isDef := special.kind == "def"
      usedDerivation := derived > 0
    }

/-- Index every theorem's conclusion as a PATTERN (binders → metavariables → `Key.star`), so that
    `getMatch goal` returns the lemmas applicable to `goal`.  A conclusion indexed as a bare `*` is a
    single variable, matches everything, and is dropped as noise. -/
def buildIndex (thms : Array Thm) : MetaM (DiscrTree Name) := do
  let mut tree : DiscrTree Name := {}
  for t in thms do
    let keys ← tryCatchRuntimeEx
        (withoutModifyingState do
          let (_, _, concl) ← forallMetaTelescopeReducing t.type
          DiscrTree.mkPath concl)
        (fun _ => pure #[])
    if keys.isEmpty || keys == #[.star] then continue
    tree := tree.insertKeyValue keys t.name
  return tree

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Freyd }] {} (trustLevel := 1024) (loadExts := true)
  let mut thms : Array Thm := #[]
  for (name, ci) in env.constants.toList do
    if name.isInternalDetail then continue
    let some (kind, type, value, levelParams) := (match ci with
      | .thmInfo info => some ("thm", info.type, info.value, info.levelParams)
      | .defnInfo info => some ("def", info.type, info.value, info.levelParams)
      | _ => none)
      | continue
    let some idx := env.getModuleIdxFor? name | continue
    unless `Freyd |>.isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    let provedByRfl := match proofHead value with
      | .const c _ => c == ``rfl || c == ``Eq.refl
      | _ => false
    let generated := generatedDeclName env name
    thms := thms.push { name, mod := env.header.moduleNames[idx.toNat]!, kind, type, value,
                        levelParams, isGenerated := generated,
                        usedInProof := .ofArray value.getUsedConstants, provedByRfl }
  let byName : Std.HashMap Name Thm := .ofList (thms.toList.map fun t => (t.name, t))
  -- `maxHeartbeats := 0`: the budget is per candidate pair (below) and never shared, so one
  -- pathological pair can no longer exhaust — and silently discard — a whole batch of results.
  let ctx : Core.Context := { fileName := "<spec>", fileMap := default, maxHeartbeats := 0 }
  let tree ← Prod.fst <$> ((buildIndex thms).run' : CoreM _).toIO ctx { env }
  IO.eprintln s!"{thms.size} theorems/definitions indexed"
  let mut rows : Array (Name × Name × String) := #[]
  let mut derivedRows : Array (Name × Name × String) := #[]
  let mut defRows : Array (Name × Name × String) := #[]
  let mut pairs := 0
  -- One `CoreM.toIO` per batch keeps the per-run metavariable/instance-cache residue bounded, the
  -- same discipline ExtractGraph's `annotate` needs.
  let batch := 64
  for lo in [0:thms.size:batch] do
    let hi := min (lo + batch) thms.size
    let action : MetaM
        (Array (Name × Name × String) × Array (Name × Name × String) ×
          Array (Name × Name × String) × Nat) := do
      let mut found := #[]
      let mut derivedFound := #[]
      let mut defFound := #[]
      let mut seen := 0
      for special in thms.extract lo hi do
        if special.provedByRfl || special.isGenerated then continue
        let candidates ← tryCatchRuntimeEx
            (forallTelescopeReducing special.type fun _ concl => tree.getMatch concl)
            (fun _ => pure #[])
        for candidate in candidates do
          if candidate == special.name then continue
          let some general := byName[candidate]? | continue
          if general.provedByRfl || general.isGenerated then continue
          -- "A is an instance of B" is also what "A was proved from B" looks like; only the pairs
          -- where the proof never mentions B are re-derivations of something already stated.
          -- BOTH directions matter. `special.usedInProof` catches "A was proved from B"; the
          -- reverse catches the far commoner shape where the general lemma is proved FROM the
          -- special one (`all_baseable` from `baseable_omega`, `evalPred` from `evalPred_aux`).
          -- Rewriting A as a call to B would then be circular, not a de-duplication.
          if special.usedInProof.contains general.name then continue
          if general.usedInProof.contains special.name then continue
          seen := seen + 1
          -- `tryCatchRuntimeEx`, not `try`: a heartbeat timeout is a RUNTIME exception, which plain
          -- `try/catch` deliberately does not catch — that is precisely how the old bucket loop lost
          -- whole buckets of findings to one slow pair.
          let outcome ← tryCatchRuntimeEx
              (withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 })
                (Core.withCurrHeartbeats (withNewMCtxDepth (specializes special general))))
              (fun _ => pure none)
          if let some result := outcome then
            let row := (special.name, general.name,
              s!"{result.note}\t{special.mod}\t{general.mod}")
            if result.isDef then
              defFound := defFound.push row
            else if result.usedDerivation then
              derivedFound := derivedFound.push row
            else
              found := found.push row
      return (found, derivedFound, defFound, seen)
    let (found, derivedFound, defFound, seen) ←
      try Prod.fst <$> (action.run' : CoreM _).toIO ctx { env }
      catch e => IO.eprintln s!"  batch at {lo} FAILED: {e}"; pure (#[], #[], #[], 0)
    rows := rows ++ found
    derivedRows := derivedRows ++ derivedFound
    defRows := defRows ++ defFound
    pairs := pairs + seen
    IO.eprintln (s!"  … {hi}/{thms.size}  ({pairs} pairs, {rows.size} direct, " ++
      s!"{derivedRows.size} derived, {defRows.size} definitions)")
  IO.FS.createDirAll "graph"
  let writeRows (path : System.FilePath) (items : Array (Name × Name × String)) : IO Unit :=
    IO.FS.withFile path .write fun h => do
      for (special, general, note) in items do
        h.putStrLn s!"{special}\t{general}\t{note}"
  writeRows "graph/spec.tsv" rows
  writeRows "graph/spec-derived.tsv" derivedRows
  writeRows "graph/spec-defs.tsv" defRows
  IO.println (s!"{pairs} candidate pairs; {rows.size} direct specialization(s), " ++
    s!"{derivedRows.size} derived match(es), {defRows.size} definition match(es) written")
