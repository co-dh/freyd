/- Proof-skeleton duplicate detector (Kind-3 / copy-pasted-proof finder).
   Run from the worktree root:  lake env lean --run scripts/ProofSkeleton.lean

   The exact-key / defeq / specialization / dep-embedding passes all key on the THEOREM TYPE. A
   copy-pasted-then-adapted proof (e.g. a lemma re-proved under a weaker hypothesis) has a DIFFERENT
   type but the SAME proof term shape — invisible to every type-based pass. This keys on the proof
   VALUE instead: abstract the value `Expr` to its structural skeleton (keep the app/lam/forall tree
   and the CALLED CONSTANTS, blank binder names / fvars / literals / universes), hash it, and bucket.
   Same skeleton across two theorems = the same proof, whatever the statements say.

   Precision note: `rfl`-proved and tiny proofs collide en masse and say nothing, so we drop proofs
   whose head is `rfl`/`Eq.refl` and whose skeleton has fewer than `minNodes` distinct nodes.
   Core-only: reads the already-built .olean files. -/
import Freyd
import Lean
open Lean

/-- Structural skeleton of a proof term. `Expr.hash` already ignores binder names + `BinderInfo`, so
    we only normalise what it still distinguishes: fvars/mvars (closed proofs have none, but `let`s can
    surface them), sorts, universe levels on constants, and literals. Constant HEADS are KEPT — "which
    lemmas this proof calls, in what tree shape" is exactly the copy-paste signal. -/
partial def skeleton : Expr → Expr
  | .bvar i           => .bvar i
  | .fvar _           => .bvar 0
  | .mvar _           => .bvar 0
  | .sort _           => .sort .zero
  | .const c _        => .const c []
  | .app f a          => .app (skeleton f) (skeleton a)
  | .lam _ t b bi     => .lam `_ (skeleton t) (skeleton b) bi
  | .forallE _ t b bi => .forallE `_ (skeleton t) (skeleton b) bi
  | .letE _ t v b nd  => .letE `_ (skeleton t) (skeleton v) (skeleton b) nd
  | .lit _            => .lit (.natVal 0)
  | .mdata _ e        => skeleton e
  | .proj s i e       => .proj s i (skeleton e)

/-- Head of a proof after stripping leading binders/mdata (to spot `rfl`-shaped proofs). -/
partial def proofHead : Expr → Expr
  | .lam _ _ b _ => proofHead b
  | .mdata _ e   => proofHead e
  | e            => e.getAppFn

/-- The SET of subtree hashes of a skeleton (its distinct DAG nodes). Two proofs that are structurally
    near-identical have near-identical subtree-hash sets; `Jaccard` of the two sets measures how much of
    the proof STRUCTURE is shared, so it catches copy-pasted-then-adapted proofs the exact hash misses. -/
partial def subtreeHashes (e : Expr) : Std.HashSet UInt64 := Id.run do
  let rec go (e : Expr) : StateM (Std.HashSet UInt64) Unit := do
    let h := e.hash
    if (← get).contains h then return
    modify (·.insert h)
    match e with
    | .app f a          => go f; go a
    | .lam _ t b _      => go t; go b
    | .forallE _ t b _  => go t; go b
    | .letE _ t v b _   => go t; go v; go b
    | .mdata _ e        => go e
    | .proj _ _ e       => go e
    | _                 => pure ()
  let ((), s) := (go e).run {}
  return s

def jaccard (a b : Std.HashSet UInt64) : Float :=
  let inter := a.fold (init := 0) fun n h => if b.contains h then n + 1 else n
  let uni := a.size + b.size - inter
  if uni == 0 then 0.0 else inter.toFloat / uni.toFloat

def minNodes : Nat := 12
def minJaccard : Float := 0.75
def bucketCap : Nat := 300

structure Thm where
  name : Name
  mod : Name
  hs : Std.HashSet UInt64
  sz : Nat
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

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Freyd }] {} (trustLevel := 1024)
  -- bucket by proof-head const; within a bucket, near-clones share most of their subtree-hash set.
  let mut buckets : Std.HashMap Name (Array Thm) := {}
  let mut scanned := 0
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    let some value := (match ci with
      | .thmInfo info => some info.value
      | .defnInfo info => some info.value
      | _ => none)
      | continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless `Freyd |>.isPrefixOf mod do continue
    if generatedDeclName env n then continue
    let head := match proofHead value with | .const c _ => c | _ => `_lam
    if head == ``rfl || head == ``Eq.refl then continue
    let hs := subtreeHashes (skeleton value)
    if hs.size < minNodes then continue
    scanned := scanned + 1
    buckets := buckets.insert head ((buckets.getD head #[]).push ⟨n, mod, hs, hs.size⟩)
  -- pairwise near-clone check within each (bounded) bucket; CROSS-FILE pairs only.
  let mut pairs : Array (Float × Name × Name × Name × Name × Nat) := #[]
  for (_, arr) in buckets do
    if arr.size > bucketCap then continue
    for i in [0:arr.size] do
      for j in [i+1:arr.size] do
        let a := arr[i]!; let b := arr[j]!
        if a.mod == b.mod then continue
        let jac := jaccard a.hs b.hs
        if jac ≥ minJaccard then
          pairs := pairs.push (jac, a.name, a.mod, b.name, b.mod, min a.sz b.sz)
  let sorted := pairs.qsort (fun x y => if x.1 == y.1 then x.2.2.2.2.2 > y.2.2.2.2.2 else x.1 > y.1)
  IO.println s!"scanned {scanned} theorem/definition values; {sorted.size} cross-file near-clone pairs (Jaccard ≥ {minJaccard})\n"
  for (jac, na, ma, nb, mb, sz) in sorted do
    let j100 := (jac * 100.0).toUInt64
    IO.println s!"J={j100}%  ~{sz}n   {na} ({ma})  ~  {nb} ({mb})"
