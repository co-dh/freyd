/- Proof-skeleton duplicate detector (Kind-3 / copy-pasted-proof finder).
   Run from the worktree root:  lake env lean --run scripts/ProofSkeleton.lean
   Optional focused scan:
     lake env lean --run scripts/ProofSkeleton.lean --min-nodes 100 --min-jaccard 0.60 \
       --output /tmp/proof-near-clones-60.tsv

   The exact-key / defeq / specialization / dep-embedding passes all key on the THEOREM TYPE. A
   copy-pasted-then-adapted proof (e.g. a lemma re-proved under a weaker hypothesis) has a DIFFERENT
   type but the SAME proof term shape — invisible to every type-based pass. This keys on the proof
   VALUE instead: abstract the value `Expr` to its structural skeleton (keep the app/lam/forall tree
   and the CALLED CONSTANTS, blank binder names / fvars / literals / universes), hash it, and bucket.
   Same skeleton across two theorems = the same proof, whatever the statements say.

   Precision note: `rfl`-proved and tiny proofs collide en masse and say nothing, so we drop proofs
   whose head is `rfl`/`Eq.refl` and whose skeleton has fewer than `minNodes` distinct nodes.
   Core-only: reads the already-built .olean files.

   Besides the human-readable stdout report, this writes `graph/proof-near-clones.tsv` so the full
   candidate set survives the agent/session that ran the scan. -/
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

structure Config where
  minNodes : Nat := 12
  minJaccard : Float := 0.75
  bucketCap : Nat := 300
  output : String := "graph/proof-near-clones.tsv"

private def parseDecimal (text : String) : Option Float := do
  match text.splitOn "." with
  | [whole] => return (← whole.toNat?).toFloat
  | [whole, fraction] =>
      let lhs ← whole.toNat?
      let rhs ← fraction.toNat?
      let scale := 10 ^ fraction.length
      return lhs.toFloat + rhs.toFloat / scale.toFloat
  | _ => none

private def parseConfig : List String → Except String Config
  | [] => pure {}
  | "--min-nodes" :: value :: rest => do
      let some n := value.toNat? | throw s!"invalid --min-nodes value `{value}`"
      return { (← parseConfig rest) with minNodes := n }
  | "--min-jaccard" :: value :: rest => do
      let some n := parseDecimal value | throw s!"invalid --min-jaccard value `{value}`"
      unless 0.0 ≤ n && n ≤ 1.0 do throw "--min-jaccard must be between 0 and 1"
      return { (← parseConfig rest) with minJaccard := n }
  | "--bucket-cap" :: value :: rest => do
      let some n := value.toNat? | throw s!"invalid --bucket-cap value `{value}`"
      return { (← parseConfig rest) with bucketCap := n }
  | "--output" :: value :: rest =>
      return { (← parseConfig rest) with output := value }
  | option :: _ => throw s!"unknown or incomplete option `{option}`"

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

def notationOrParserDecl (name : Name) : Bool :=
  let tail := (name.toString.splitOn ".").getLastD ""
  tail.startsWith "term" || tail.startsWith "«term" ||
    ["relCompose", "underHomComp", "overHomComp", "relUnionNotation", "allegoryRecip"].contains tail

def main (args : List String) : IO Unit := do
  let config ← IO.ofExcept (parseConfig args)
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
    if hs.size < config.minNodes then continue
    scanned := scanned + 1
    buckets := buckets.insert head ((buckets.getD head #[]).push ⟨n, mod, hs, hs.size⟩)
  -- pairwise near-clone check within each (bounded) bucket; CROSS-FILE pairs only.
  let mut pairs : Array (Float × Name × Name × Name × Name × Nat) := #[]
  for (_, arr) in buckets do
    if arr.size > config.bucketCap then continue
    for i in [0:arr.size] do
      for j in [i+1:arr.size] do
        let a := arr[i]!; let b := arr[j]!
        if a.mod == b.mod then continue
        let jac := jaccard a.hs b.hs
        if jac ≥ config.minJaccard then
          pairs := pairs.push (jac, a.name, a.mod, b.name, b.mod, min a.sz b.sz)
  let sorted := pairs.qsort fun x y =>
    if x.1 != y.1 then x.1 > y.1
    else if x.2.2.2.2.2 != y.2.2.2.2.2 then x.2.2.2.2.2 > y.2.2.2.2.2
    else
      let xKey := s!"{x.2.1}\t{x.2.2.1}\t{x.2.2.2.1}\t{x.2.2.2.2.1}"
      let yKey := s!"{y.2.1}\t{y.2.2.1}\t{y.2.2.2.1}\t{y.2.2.2.2.1}"
      xKey < yKey
  IO.println s!"scanned {scanned} theorem/definition values; {sorted.size} cross-file near-clone pairs (Jaccard ≥ {config.minJaccard})\n"
  let mut tsv := #["jaccard\tmin_nodes\tleft\tleft_module\tright\tright_module\tclass"]
  for (jac, na, ma, nb, mb, sz) in sorted do
    let j100 := (jac * 100.0).toUInt64
    IO.println s!"J={j100}%  ~{sz}n   {na} ({ma})  ~  {nb} ({mb})"
    let kind := if notationOrParserDecl na || notationOrParserDecl nb then
      "notation/parser" else "ordinary"
    tsv := tsv.push s!"{jac}\t{sz}\t{na}\t{ma}\t{nb}\t{mb}\t{kind}"
  IO.FS.writeFile config.output (String.intercalate "\n" tsv.toList ++ "\n")
  IO.println s!"\nwrote {sorted.size} pair(s) to {config.output}"
