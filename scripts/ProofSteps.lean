/- ProofSteps — the ⊑/=-chain a PROOF factors into, read off its term.

   A display of the note is a proof CHAIN: one `#disp` holds several panels, and the note cites ONE
   theorem for the whole chain.  `diag-export` draws a declaration's two SIDES, so a chain's
   intermediate terms have no selector — this asks whether those terms are in the proof term at all,
   which is what a `<Name>.step<n>` selector would have to read them from.

     env LEAN_PATH=<main checkout>/.lake/build/lib/lean lean --run scripts/ProofSteps.lean \
       Freyd.Alg.relCata_fusion Freyd.Alg.thinning

   One block per declaration: the step count, then `lhs <rel> rhs` per step, pretty-printed under the
   declaration's own binders so the note's unexpanders apply.  A proof with no spine prints
   `no-chain: <head constant>`.

   The spine walk is `Freyd.DiagExport.transChain`/`bestChain` again rather than a call to it: that
   module declares a root `main`, so importing it makes this script's `main` undeclarable and
   `lean --run` has nowhere to start.  `SPINE` below must therefore stay in step with that file's own
   list; everything else the two share — `splitM`, `repoNamespaces` — is imported from
   `diag/tool/ExprReader.lean`, the module underneath both. -/
import diag.tool.ExprReader

open Lean Meta

/-- The transitivity constants a proof's spine is made of.  From the index, not from guessing:
    `Freyd.Alg.le_trans` (`Freyd/S2_10.lean`) is the allegory's `⊑` transitivity and
    `Freyd.Diag.OrderedCat.«≤_trans»` the diagrammatic tower's; `calc` itself always elaborates to
    `Trans.trans`, and `Eq.trans` closes a rewritten equation. -/
def SPINE : List Name :=
  [``Trans.trans, ``Eq.trans, `Freyd.Alg.le_trans, `Freyd.Diag.OrderedCat.«≤_trans»]

/-- One step: the relation symbol and the two sides. -/
abbrev Step := String × Expr × Expr

/-- The two proofs a binary transitivity is applied to, whatever its implicit prefix. -/
def lastTwo (args : Array Expr) : Option (Expr × Expr) :=
  if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none

mutual

/-- Flatten a trans spine, or fail. -/
partial def transChain (e : Expr) : MetaM (Option (Array Step)) := do
  let (f, args) := e.getAppFnArgs
  if SPINE.contains f then
    match lastTwo args with
    | some (a, b) => return some ((← chainOrLeaf a) ++ (← chainOrLeaf b))
    | none => return none
  else return none

/-- The chain a proof contributes: its spine if it has one, else the single step it proves. -/
partial def chainOrLeaf (e : Expr) : MetaM (Array Step) := do
  match ← transChain e with
  | some c => return c
  | none =>
    let t ← (do pure (some (← Meta.inferType e))) <|> pure none
    match ← t.mapM Freyd.StrDiag.splitM with
    | some (some st) => return #[st]
    | _ => return #[]

end

/-- The longest spine anywhere in `e`: the outermost `calc` is not always at the top, since a proof
    may wrap it in `(… ?_).symm` or in a stack of `have`s. -/
partial def bestChain (e : Expr) : MetaM (Array Step) := do
  if let some c ← transChain e then return c
  if let (``letFun, #[t, _, _, f]) := e.getAppFnArgs then
    return ← Meta.withLocalDeclD (match f with | .lam n .. => n | _ => `h) t fun x =>
      bestChain (mkApp f x).headBeta
  match e with
  -- Not descended into: the leaves would carry free variables of a scope that is gone by the time
  -- they print.  The caller opens the declaration's own binders and walks inside them.
  | .lam .. => return #[]
  -- A proof `have` is opened as a HYPOTHESIS, never substituted: substituted, a thirteen-line
  -- reshaping lemma standing under a three-line argument comes out as the thirteen lines.
  | .letE n t v b _ =>
    if ← Meta.isProof v then Meta.withLocalDeclD n t fun x => bestChain (b.instantiate1 x)
    else bestChain (b.instantiate1 v)
  | .mdata _ b | .proj _ _ b => bestChain b
  | .app f a => do
    let cf ← bestChain f
    let ca ← bestChain a
    return if ca.size > cf.size then ca else cf
  | _ => return #[]

/-- What a chainless proof is, in one word the reader can act on: the constant that closed it. -/
partial def headOf : Expr → String
  | .mdata _ e => headOf e
  | .lam _ _ b _ | .letE _ _ _ b _ => headOf b
  | e => match e.getAppFn with
    | .const n _ => n.toString
    | .fvar _ => "a local hypothesis"
    | f => f.ctorName

/-- Every `.lean` under `dir`, as module names — the whole AOP layer, so a declaration of any
    chapter file resolves without naming its module.  `diag/tool` and `diag/generated` are skipped:
    the tool is what is running, and `generated` holds Typst. -/
partial def libModules (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then
      if e.fileName != "tool" && e.fileName != "generated" then
        out := out ++ (← libModules e.path (pre.str e.fileName))
    else if e.path.extension == some "lean" then
      out := out.push (pre.str (e.path.fileStem.getD ""))
  return out

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: ProofSteps <declaration-name> [<declaration-name> ...]"; return 2
  Lean.initSearchPath (← Lean.findSysroot)
  let mods := #[`Freyd] ++ (← libModules "diag" `diag) ++ (← libModules "AOP" `AOP)
  -- `loadExts`: without it the environment carries the CONSTANTS but no extension state, so not one
  -- `notation` in the repo is applied and every step prints in raw `Cat.comp` form.
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
    (loadExts := true)
  let scopes := [`Freyd, `Freyd.Diag.SymMonCat, `Freyd.Diag.Word]
  let exts ← scopedEnvExtensionsRef.get
  let env := scopes.foldl (fun env ns => exts.foldl (fun env ext => ext.activateScoped env ns) env) env
  let opts : Options :=
    ((Options.empty.setBool `pp.fieldNotation false).setBool `pp.fieldNotation.generalized false)
      |>.insert `maxHeartbeats (.ofNat 1000000)
  let ctx : Core.Context :=
    { fileName := "<proof-steps>", fileMap := default, options := opts,
      openDecls := (scopes ++ Freyd.StrDiag.repoNamespaces env).map (.simple · []) }
  let mut status : UInt32 := 0
  for arg in args do
    let some ci := env.find? arg.toName
      | IO.eprintln s!"ProofSteps: {arg}: no such declaration"; status := 1; continue
    let some val := ci.value?
      | IO.eprintln s!"ProofSteps: {arg}: no value — an axiom or an opaque constant"
        status := 1; continue
    -- The binders are OPENED, not stripped: the steps mention them, and outside the telescope every
    -- one of them prints as `_fvar.N`.
    let run : CoreM Unit := Meta.MetaM.run' <| Meta.lambdaTelescope val fun _ body => do
      let chain ← bestChain body
      if chain.isEmpty then
        IO.println s!"{arg}\tno-chain: {headOf body}"
      else
        IO.println s!"{arg}\t{chain.size} step(s)"
        for (sym, l, r) in chain do
          IO.println s!"  {(← ppExpr l).pretty 160} {sym} {(← ppExpr r).pretty 160}"
    match ← (Prod.fst <$> run.toIO ctx { env }).toBaseIO with
    | .error ex => IO.eprintln s!"ProofSteps: {arg}: {ex}"; status := 1
    | .ok _ => pure ()
  return status
