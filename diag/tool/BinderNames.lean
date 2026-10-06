import Lean
/-! # BinderNames — a collection is named `xs`, one of its elements `x`

    `lake env lean --run diag/tool/BinderNames.lean <selector list>…` reads the note's selector
    lists (`diag-export --list` output), imports every `AOP` module and, for each declaration a
    selector names, walks the binders of its type — and of its value, for a `def`, which is what a
    def row unfolds to — and reports
    * a binder whose type is a collection whose name is not a plural (`xs`, `ys₁`, `zs'`),
    * a binder whose elements are collections whose name does not end in `ss` (`xss`; its element is `xs`), and
    * an application taking a collection binder `c` and an element binder `e` of it where `e`'s name
      plus `s` is not `c`'s (`inlistP x b` is reported: `b` should be `x`, `x` should be `xs`).
    A type is a collection when a head constant met while unfolding it is one of `collHeads`; its
    element type is that head's last argument (the carrier of it, for a `RelSet` object). -/
open Lean Meta

/-- The collection type formers: lists, arrays, trees, bags and the power object. -/
def collHeads : List Name :=
  [``List, ``Array, `Freyd.Alg.RelSet.CL.ConsList, `Freyd.Alg.RelSet.SL.SnocList,
   `Freyd.Alg.RelSet.RT.Rose, `Freyd.Alg.RelSet.TB.Tree, `Freyd.Alg.RelSet.TT.Tree,
   `Freyd.Alg.RelSet.Tardy.Bag, `Freyd.Alg.RelSet.pow]

/-- The collection application met while unfolding `t`, if any: head constants are read at each
    step of `whnfCore` + one delta, and inside a `carrier` projection, whose object is unfolded too. -/
partial def collApp? (t : Expr) (fuel : Nat := 16) : MetaM (Option Expr) := do
  let t := t.consumeMData
  if collHeads.contains t.getAppFn.constName then return some t
  -- Any other inductive (a `String` is a word, a pair is a pair) is not a collection.
  if let some (.inductInfo _) := (← getEnv).find? t.getAppFn.constName then return none
  let s? := match t with
    | .proj _ _ s => some s
    | _ => if t.getAppFn.constName == `Freyd.Alg.RelSet.carrier then t.getAppArgs.back? else none
  if let some s := s? then if let some c ← collApp? s fuel then return some c
  if fuel == 0 then return none
  let t' ← whnfCore t
  if t' != t then return ← collApp? t' (fuel - 1)
  match ← unfoldDefinition? t with
  | some t' => collApp? t' (fuel - 1)
  | none => return none

/-- `xs₁'` ↦ `xs`: the name without its trailing indices and primes. -/
def base (n : Name) : String :=
  (n.eraseMacroScopes.toString.dropEndWhile fun (c : Char) => c.isDigit || c == '\'' || c == '_' ||
    ('₀' ≤ c && c ≤ '₉')).copy

def plural (n : Name) : Bool := let b := base n; b.length ≥ 2 && b.endsWith "s"

/-- Is `e`'s type the element type of the collection `c`? -/
def elemOf (c e : Expr) : MetaM Bool := do
  let some a ← collApp? (← inferType c) | return false
  let some el := a.getAppArgs.back? | return false
  let te ← inferType e
  if ← isDefEq te el then return true
  try isDefEq te (mkApp (mkConst `Freyd.Alg.RelSet.carrier [levelZero]) el) catch _ => return false

/-- Every offending binder of `e`, as `binder : reason`. -/
partial def walk (e : Expr) : StateT (Array String) MetaM Unit := do
  match e with
  | .forallE n t b bi | .lam n t b bi =>
    walk t
    let skip := n.hasMacroScopes || n.isInternal || bi.isInstImplicit
    if !skip then if let some a ← collApp? t then
      if !plural n then
        modify (·.push s!"{n} : {← ppExpr t} — a collection, not a plural")
      else if let some el := a.getAppArgs.back? then
        if (← collApp? el).isSome && !(base n).endsWith "ss" then
          modify (·.push s!"{n} : {← ppExpr t} — a collection of collections is named `xss`")
    withLocalDecl n bi t fun x => walk (b.instantiate1 x)
  | .letE n t v b _ => walk t; walk v; withLetDecl n t v fun x => walk (b.instantiate1 x)
  | .mdata _ b => walk b
  | .proj _ _ s => walk s
  | .app .. =>
    let args := e.getAppArgs
    -- A MEMBERSHIP: a proposition whose head constant takes exactly a collection and an element of
    -- it as its explicit arguments (`inlistP xs x`, `x ∈ xs`); `cons x xs` is no claim about `x`.
    let expl ← if e.getAppFn.isConst && (← isProp e) then
        (do let bis := (← getFunInfoNArgs e.getAppFn args.size).paramInfo
            pure ((args.zip bis).filterMap fun (a, i) => if i.isExplicit then some a else none))
      else pure #[]
    let fvs := if expl.size == 2 && expl.all (·.isFVar) then expl else #[]
    for c in fvs do
      for x in fvs do
        if c != x && (← elemOf c x) then
          let (cn, xn) := ((← c.fvarId!.getUserName), (← x.fvarId!.getUserName))
          unless cn.hasMacroScopes || xn.hasMacroScopes || base cn == base xn ++ "s" do
            modify (·.push s!"{xn} ∈ {cn} — the element of `{cn}` is not named after it")
    unless e.getAppFn.isApp do walk e.getAppFn
    for a in args do walk a
  | _ => pure ()

/-- The declaration a selector names: its longest prefix the environment has. -/
def declOf (env : Environment) (sel : String) : Option Name :=
  let rec go : Name → Option Name
    | .anonymous => none
    | n@(.str p _) | n@(.num p _) => if env.contains n then some n else go p
  go ((sel.splitOn "#").head!.toName)

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let olean := System.FilePath.mk ".lake/build/lib/lean/AOP"
  let mods := (← olean.readDir).filterMap fun f =>
    if f.path.extension == some "olean" then some (`AOP ++ (f.path.fileStem.get!).toName) else none
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := true)
  let mut decls : Std.HashSet Name := {}
  for f in args do
    for l in (← IO.FS.lines f) do
      for s in l.splitOn "+" do
        if let some n := declOf env s.trimAscii.copy then decls := decls.insert n
  let mut bad := 0
  for n in decls.toArray.qsort (·.toString < ·.toString) do
    let some ci := env.find? n | continue
    -- A def row unfolds to the value; a theorem's proof is not printed, so only its statement counts.
    let es := match ci with | .defnInfo d => #[d.type, d.value] | c => #[c.type]
    let ctx : Core.Context := { fileName := "<BinderNames>", fileMap := default, maxHeartbeats := 0 }
    let ((_, out), _) ← (((es.forM walk).run #[]).run'.toIO ctx { env })
    for o in out.toList.eraseDups do IO.println s!"{n}: {o}"; bad := bad + 1
  IO.eprintln s!"{decls.size} declarations, {bad} binders misnamed"
  return if bad == 0 then 0 else 1
