/- Find theorems that are SPECIAL CASES of other theorems (the dedup skill's kind 2).
   Run from repo root:  lake env lean --run scripts/SpecScan.lean
   Output: graph/spec.tsv  (specialized  general  discharge)

   The statement-key pass in `ExtractGraph` finds theorems whose types are EQUAL. A specialization
   has a DIFFERENT type — it fixes a parameter, takes a stronger typeclass, or discharges a
   hypothesis — so hashing cannot see it. The check is semantic: unify the two conclusions, then try
   to discharge whatever of the general lemma's binders that leaves, from the special one's context.

   Precision comes from the last filter: `A is an instance of B` is also what "A was PROVED using B"
   looks like, and that is the overwhelming majority of pairs. Only pairs where A's proof never
   mentions B are reported — those are the ones that re-derived what B already says.

   Candidate generation is a two-level bucket on the conclusion (head constant, plus the head of its
   first argument) rather than a `DiscrTree`: head alone leaves a 600+ member `Cat.comp` bucket, and
   the pair count is quadratic in bucket size. Buckets past `bucketCap` are skipped outright.

   Core-only: reads the already-built .olean files. -/
import Lean
open Lean Meta

/-- Buckets bigger than this are skipped: the work is quadratic and the big buckets are equation
    lemmas about one head symbol, where a specialization would be an equation rewriting to itself. -/
def bucketCap : Nat := 250

/-- Strip a proof's leading binders: `theorem foo (a b) := rfl` elaborates to `fun a b => rfl`, so
    the head constant is only visible underneath them. -/
partial def proofHead : Expr → Expr
  | .lam _ _ b _ => proofHead b
  | .mdata _ e => proofHead e
  | e => e.getAppFn

/-- Conclusion of a `∀`-telescope, without instantiating anything. -/
partial def conclusionOf : Expr → Expr
  | .forallE _ _ b _ => conclusionOf b
  | .mdata _ e => conclusionOf e
  | e => e

/-- Bucket key: the conclusion's head constant, refined by the head of its first argument. Two
    statements that can possibly unify agree on both. -/
def bucketKey (type : Expr) : Option (Name × Name) :=
  let concl := conclusionOf type
  match concl.getAppFn with
  | .const head _ =>
    let refine := match concl.getAppArgs[0]? with
      | some arg => match arg.getAppFn with | .const c _ => c | _ => `_
      | none => `_
    some (head, refine)
  | _ => none

structure Thm where
  name : Name
  type : Expr
  levelParams : List Name
  usedInProof : Std.HashSet Name
  /-- Proved by `rfl`.  Such a statement reduces to reflexivity, so ANY lemma that reduces the same
      way "proves" it and the scan matches it against unrelated siblings — `gs2 A B 0 = A` against
      `gs2 A B 1 = B`, both `rfl`, both `A = A` once reduced.  There is also nothing to save by
      rewriting one into a call. Excluded from both sides of a pair. -/
  provedByRfl : Bool

/-- Can `general` be applied to prove `special`?  Unify the conclusions under fresh metavariables for
    `general`'s binders, then discharge the leftovers: instance binders by synthesis, the rest by
    matching a hypothesis of `special`.  Returns a note naming what had to be discharged. -/
def specializes (special general : Thm) : MetaM (Option String) := do
  let generalType := general.type.instantiateLevelParams general.levelParams
    (← general.levelParams.mapM fun _ => mkFreshLevelMVar)
  forallTelescopeReducing special.type fun hypotheses specialConcl => do
    let (mvars, binderInfos, generalConcl) ← forallMetaTelescopeReducing generalType
    unless ← isDefEq specialConcl generalConcl do return none
    let mut synthesized := 0
    let mut assumed := 0
    for (mvar, info) in mvars.zip binderInfos do
      if ← mvar.mvarId!.isAssigned then continue
      let wanted ← inferType mvar
      if info == .instImplicit then
        match ← (do try pure (some (← synthInstance wanted)) catch _ => pure none) with
        | some inst => unless ← isDefEq mvar inst do return none
                       synthesized := synthesized + 1
        | none => return none
      else
        -- a leftover ordinary binder must come from one of `special`'s own hypotheses
        let mut found := false
        for hypothesis in hypotheses do
          unless found do
            if ← isDefEq mvar hypothesis then found := true; assumed := assumed + 1
        unless found do return none
    return some s!"{synthesized} instance(s), {assumed} hypothesis(es)"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Freyd }] {} (trustLevel := 1024) (loadExts := true)
  let mut buckets : Std.HashMap (Name × Name) (Array Thm) := {}
  let mut total := 0
  for (name, ci) in env.constants.toList do
    if name.isInternalDetail then continue
    let .thmInfo info := ci | continue
    let some idx := env.getModuleIdxFor? name | continue
    unless `Freyd |>.isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    let some key := bucketKey info.type | continue
    total := total + 1
    let provedByRfl := match proofHead info.value with
      | .const c _ => c == ``rfl || c == ``Eq.refl
      | _ => false
    let thm : Thm := { name, type := info.type, levelParams := info.levelParams,
                       usedInProof := .ofArray info.value.getUsedConstants, provedByRfl }
    buckets := buckets.insert key ((buckets.getD key #[]).push thm)
  let considered := buckets.fold (init := 0) fun n _ b => if b.size ≤ bucketCap then n + b.size else n
  IO.eprintln s!"{total} theorems, {buckets.size} buckets, {considered} in buckets ≤ {bucketCap}"
  -- One `CoreM.toIO` per bucket keeps the per-run metavariable/instance-cache residue bounded, the
  -- same discipline ExtractGraph's `annotate` needs.
  let ctx : Core.Context := { fileName := "<spec>", fileMap := default, maxHeartbeats := 400000 }
  let mut rows : Array (Name × Name × String) := #[]
  for (_, bucket) in buckets do
    if bucket.size < 2 || bucket.size > bucketCap then continue
    let action : MetaM (Array (Name × Name × String)) := do
      let mut found := #[]
      for special in bucket do
        for general in bucket do
          if special.name == general.name then continue
          -- "A is an instance of B" is also what "A was proved from B" looks like; only the pairs
          -- where the proof never mentions B are re-derivations of something already stated.
          -- BOTH directions matter. `special.usedInProof` catches "A was proved from B"; the
          -- reverse catches the far commoner shape where the general lemma is proved FROM the
          -- special one (`all_baseable` from `baseable_omega`, `evalPred` from `evalPred_aux`).
          -- Rewriting A as a call to B would then be circular, not a de-duplication.
          if special.usedInProof.contains general.name then continue
          if general.usedInProof.contains special.name then continue
          if special.provedByRfl || general.provedByRfl then continue
          -- Each pair gets its own small budget: one pathological `isDefEq` must not consume the
          -- bucket's, and a timeout is a "no", not a failure of the run.
          let outcome ← try
              withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 })
                (Core.withCurrHeartbeats (withNewMCtxDepth (specializes special general)))
            catch _ => pure none
          if let some note := outcome then found := found.push (special.name, general.name, note)
      return found
    let found ← try Prod.fst <$> (action.run' : CoreM _).toIO ctx { env }
      catch _ => pure #[]
    rows := rows ++ found
  IO.FS.createDirAll "graph"
  IO.FS.withFile "graph/spec.tsv" .write fun h => do
    for (special, general, note) in rows do
      h.putStrLn s!"{special}\t{general}\t{note}"
  IO.println s!"{rows.size} specialization(s) written to graph/spec.tsv"
