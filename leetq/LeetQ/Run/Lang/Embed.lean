import LeetQ.Run.Lang.Grammar
import LeetQ.Run.Lang.Expand
import Lean

/-! The command `rel_program n where`: it reads the grammar (`Grammar`) into the AST and defines `n : Program`;
    `Expand.emit` defines what it reads. -/

namespace LeetQ.Rel.Lang.Embed

open Lean Parser Elab Command
open LeetQ.Rel.Lang
open LeetQ.Rel.Lang.Parse (P)
/-- The parameters `ps` of the definition or theorem `w`, each a name no builtin takes, each once. -/
def params (s : Syntax) (w : String) (ps : Array Syntax) : C (List Param) := do
  let ps ← ps.toList.mapM fun q => do
    let n ← wordOf q[0]
    if (Parse.builtin n).isSome then failAt q s!"`{n}` is a builtin; choose another name"
    pure (⟨n, ← q[1].getOptional?.mapM typeOf⟩ : Param)
  let _ ← ps.foldlM (fun (seen : List String) q => do
    if seen.contains q.name then failAt s s!"`{q.name}` is already a parameter of `{w}`"
    pure (q.name :: seen)) []
  pure ps

/-- A definition: `w` its name, `key` it or its infix key `_w_`. -/
def defn (s : Syntax) (w key : String) (ps : Array Syntax) (ty body test wh : Syntax) : C Decl := do
  let p ← posOf s
  Parse.fresh p w (← get).taken
  let ps ← params s w ps
  if key != w && ps.length != 2 then
    failAt s s!"the infix operator `{w}` takes two parameters, `{key}(R, S)`, found {ps.length}"
  let ty ← ty.getOptional?.mapM typeOf
  let outer := (← get).known
  modify fun st => { st with known := ps.map (fun q => (q.name, 0)) ++ st.known }
  -- the `where` items first: each in scope in the items after it and in the body (§c)
  let σ ← (if wh.getNumArgs == 0 then #[] else wh[1].getSepArgs).foldlM (init := []) fun σ i => do
    let q ← posOf i
    let n ← wordOf i[0]
    Parse.fresh q n ((key, Parse.at_ p) :: (← get).taken)
    if ps.any (·.name == n) then failAt i s!"`{n}` is already a parameter of `{w}`"
    if σ.any (·.1 == n) then failAt i s!"`{n}` is already an item of this `where`"
    let σ := σ ++ [(n, (← expr i[2]).subst σ)]
    modify fun st => { st with known := (n, 0) :: st.known }
    pure σ
  let e := (← expr body).subst σ
  let b ← if test.getNumArgs == 0 then pure (Body.rel e) else do pure (Body.test e ((← expr test[1]).subst σ))
  if let (.test .., some t) := (b, ty) then
    failAt s s!"the test `{w}` has no type of its own: drop ': {OExp.arrow t}' (§e)"
  modify fun st => { st with known := outer }
  pure (.defn p key ps b ty)

def stmt (s : Syntax) : C Decl := do
  let p ← posOf s
  let objName : C String := do
    let n ← wordOf s[1]
    if let some r := (← get).taken.lookup n then failAt s[1] s!"`{n}` is already defined {r}"
    pure n
  let objDecl (d : C ObjDef) : C Decl := do let n ← objName; pure (.obj p n (← d))
  let num (w : Syntax) : C Int := do onText w[0] (← wordOf w) Parse.num
  let opt (o : Syntax) := if o.getNumArgs == 0 then #[] else o[1].getSepArgs
  match s.getKind with
  | ``sElems => objDecl do pure (.elems (← s[4].getSepArgs.toList.mapM wordOf))
  | ``sRange => objDecl do
    let lo ← num s[3]; let hi ← num s[5]
    if hi < lo then failAt s[5] s!"the range {lo}…{hi} is empty: {hi} is below {lo}"
    pure (.range lo hi)
  | ``sAlias => objDecl do pure (.alias (← obj s[3]))
  | ``sPrint => pure (.print p (← expr s[1]))
  | ``sCheck => pure (.check p (← expr s[1]) (← expr s[3]) (atomIn s[2] == "="))
  | ``sDefn =>
    -- `_on_` is one Lean identifier: its text read as a head, `_n_` the infix `n`
    let (w, key) ← onText s[0] (tokText s[0][0] ++ (if s[0].getKind == ``wNeg then tokText s[0][1] else "")) do
      let w ← Parse.word
      if w != "_" then pure (w, w) else do
        let n ← Parse.word
        if (← Parse.peek) != some '_' then Parse.expected s!"'_' closing the infix operator `_{n}_`"
        Parse.adv; pure (n, Parse.infixKey n)
    defn s w key (opt s[1]) s[2] s[4] s[5] s[6]
  | ``sInfix => do let n ← wordOf s[1]; defn s n (Parse.infixKey n) s[4].getSepArgs s[6] s[8] s[9] s[10]
  | ``sTheorem => do
    let n ← wordOf s[1]
    Parse.fresh p n (← get).taken
    let ps ← params s n (opt s[2])
    if s[3].getNumArgs != 0 && !ps.isEmpty then
      failAt s[3] s!"`on` evaluates a theorem with no parameters; `{n}` has {ps.length}"
    let outer := (← get).known
    modify fun st => { st with known := ps.map (fun q => (q.name, 0)) ++ st.known }
    let on ← if s[3].getNumArgs == 0 then pure none else some <$> expr s[3][1]
    let hyps ← (opt s[4]).toList.mapM fun h => do
      let a ← expr h[0]
      if h[1].getNumArgs == 0 then pure (a, none) else pure (a, some (atomIn h[1][0] == "=", ← expr h[1][1]))
    let e ← expr s[6]; let f ← expr s[8]; let eq := atomIn s[7] == "="
    -- a reason is the program's theorem or definition, else the registry's one the resolver gives
    let steps ← (if s[9].getNumArgs == 0 then #[] else s[9][2].getArgs).toList.mapM fun t => do
      unless t.getKind == ``cStep do failAt t "expected a step `_ = e := n`"
      let q ← posOf t; let x ← expr t[2]; let r ← posOf t[5]
      -- a qualified reason, `laws.estMap`, is read as a term reads `m.x`; a bare one is one word
      let m ← match t[5][0] with
        | .ident _ _ c _ => if c.isAtomic then wordOf t[5] else onText t[5] (tokText t[5][0]) Parse.name
        | _ => wordOf t[5]
      let st ← get
      -- a name not the program's is the registry's, through the resolver (§2.3), whose refusal (ambiguous) is the error
      let own := st.known.any (fun k => k.1 == m || k.1 == Parse.infixKey m) || st.thms.contains m
      let ex ← if own || ps.any (·.name == m) then pure none else match st.res m with
        | .ext e => pure (some e)
        | .bad _ msg => failAt t[5] msg
        | .none => pure none
      if let some e := ex then modify fun st => { st with used := e.const :: st.used }
      let isDef := (st.known.any (fun k => k.1 == m || k.1 == Parse.infixKey m) && !ps.any (·.name == m)) ||
        ex.any (fun e => !e.obj && !e.thm)
      let isThm := st.thms.contains m || ex.any (·.thm)
      let args ← if t[6].getNumArgs == 0 then pure [] else t[6][1].getSepArgs.toList.mapM expr
      if t[4].getNumArgs != 0 && !args.isEmpty then failAt t[6] s!"`≜ {m}` unfolds a definition: it takes no arguments"
      let why ← if t[4].getNumArgs == 0 then
          if isThm then pure (Why.thm r m (if st.thms.contains m then none else ex.map (·.const)) args)
          else failAt t[5] (if isDef then s!"`{m}` is a definition; write `≜ {m}`" else s!"unknown theorem '{m}'")
        else if isDef then pure (Why.unfold r m)
          else failAt t[5] (if isThm then s!"`{m}` is a theorem, not a definition"
            else s!"unknown definition '{m}'")
      if eq && atomIn t[1] != "=" then failAt t s!"`{n}` states `=`: a step `⊑` proves only `⊑`"
      pure (q, atomIn t[1] == "=", x, why)
    -- the chain starts at the left side (`_`) and must end at the right one, compared as the parser reads both
    if let some (q, _, x, _) := steps.getLast? then
      if x.render 0 true != f.render 0 true then
        throw ⟨q, s!"the chain of `{n}` ends at {x.show}, not at its right side {f.show}"⟩
    modify fun st => { st with known := outer }
    pure (.«theorem» p n ps e f eq on hyps steps)
  | _ => failAt s "expected a declaration"

/-- The program of the statements `ss`, read in the scope `s₀`, each statement in the scope those before it leave
    (`Parse.after`); and the scope it leaves. -/
def program (fm : FileMap) (s₀ : Parse.S) (ss : Array Syntax) : Except Err (Program × Parse.S) :=
  (ss.toList.mapM (fun x => do let d ← stmt x; modify (Parse.after · [d]); pure d) |>.run fm).run s₀

unsafe def programOfUnsafe (n : Name) : CommandElabM Program := do
  match (← getEnv).evalConstCheck Program (← getOptions) ``Program n with
  | .ok p => pure p
  | .error e => throwError "cannot read the program `{n}`: {e}"

/-- The value of the program `n`, a `rel_program` elaborated before. -/
@[implemented_by programOfUnsafe] opaque programOf (n : Name) : CommandElabM Program

def defConst (n : Name) (v : Lean.Expr) : CoreM Unit :=
  addAndCompile <| .defnDecl
    { name := n, levelParams := [], type := mkConst ``Program, value := v, hints := .abbrev, safety := .safe }

/-- The constant `c : Decl` of a declaration not built to a constant of its own (not yet elaborated once). -/
def declConst (c : Name) (d : Decl) : CoreM Unit :=
  addAndCompile <| .defnDecl
    { name := c, levelParams := [], type := mkConst ``Decl, value := toExpr d, hints := .abbrev, safety := .safe }

/-- The resolver in the namespace `ns` with the `open`s `opens` (module design §2.3): Lean's `resolveGlobalName`
    gives the candidates of a written name, the registry keeps its own; and whether a written prefix is a
    namespace. -/
def resolverAt (env : Environment) (opts : Options) (reg : Expand.Registry) (ns : Name) (opens : List OpenDecl) :
    (String → Found) × (String → Bool) :=
  let id (t : String) : Name := (Parse.parts t).foldl Name.str .anonymous
  let at_ (ns : Name) (t : String) : List Name := ((ResolveName.resolveGlobalName env opts ns opens (id t)).filterMap
    fun (c, fs) => if fs.isEmpty then some c else none).eraseDups
  -- Lean's resolution from the namespace `ns` outwards, where a constant that is no Rel definition shadows nothing:
  -- the first namespace level whose resolution has Rel definitions gives them
  let levels := (ns.components.length + 1 |> List.range).map fun k => ns.components.take (ns.components.length - k)
  (fun t =>
    let es := (levels.map fun c => (at_ (c.foldl (· ++ ·) .anonymous) t).filterMap (reg.exts[·]?)).find? (!·.isEmpty)
    match es with
    | some [(e, _)] => .ext e
    | some es => .bad true s!"ambiguous name `{t}`: it is {es.map (·.1.const)}"
    | none => match at_ ns t with
      | [] => .none
      | cs => .bad false s!"`{t}` is not a Rel definition: Lean resolves it to {cs}",
   fun t => !(ResolveName.resolveNamespace env ns opens (id t)).isEmpty)

/-- The scope of a program read here: the current namespace and `open`s. -/
def scopeHere : CommandElabM Parse.S := do
  let (res, ns) := resolverAt (← getEnv) (← getOptions) (Expand.relRegistry.getState (← getEnv)) (← getCurrNamespace) (← getOpenDecls)
  pure { cs := #[], res, ns }

/-- The programs the constants `used` reach, each after the programs its own names reach, in the order they were
    defined (an import's before the importer's). -/
def homesOf (reg : Expand.Registry) (used : List Name) : List Name :=
  let hs := used.filterMap fun c => (reg.exts[c]?).map (·.2)
  let all := hs.flatMap fun h => ((reg.chains.lookup h).getD []) ++ [h]
  (reg.progs.toList.map (·.1)).filter all.contains

/-- The program `n` named by `id`, read in the scope `s` that left `used`, what it reads (`Expand.emit`): each closed
    definition as the Lean definition `n.x`, its prints, its checks; then its definitions and objects registered,
    each a constant (`n.x : Decl`, its declaration, where it is not built once), with its scope and homes; the doc
    comment `stx[0]`, when written, is `n`'s. -/
def define (stx id : Syntax) (prog : Program) (used : List Name) (more : List Name := [])
    (scope : Option (Name × List OpenDecl) := none) : CommandElabM Unit := do
  let n := (← getCurrNamespace) ++ id.getId
  let (ns, os) := scope.getD (← getCurrNamespace, ← getOpenDecls)
  liftTermElabM do
    defConst n (toExpr (α := List Decl) prog)
    addDocString' n mkNullNode (stx[0].getOptional?.map (⟨·⟩))
    Term.addTermInfo' id (mkConst n) (isBinder := true)
  addDeclarationRangesFromSyntax n stx id
  let env ← getEnv
  let opts ← getOptions
  let reg := Expand.relRegistry.getState env
  -- `nil` starts at the `1` in scope (`Env.one`) though no token names it, so its home is read too
  let one := match (resolverAt env opts reg ns os).1 "1" with | .ext e => [e.const] | _ => []
  let homes := (reg.progs.toList.map (·.1)).filter ((more ++ homesOf reg (one ++ used)).contains ·)
  let progs ← homes.mapM fun m => return (m, ← programOf m)
  let resOf (h : Name) : String → Found :=
    if h == n then (resolverAt env opts reg ns os).1 else
    match reg.progs.find? (·.1 == h) with
    | some (_, ns, os) => (resolverAt env opts reg ns os).1
    | none => fun _ => .none
  match ← liftTermElabM (Expand.read (reg.calls.lookup ·) progs prog n resOf).run with
  | .error e => throwErrorAt stx "{e}"
  | .ok r =>
    liftTermElabM (Expand.emit n r)
    for d in prog do
      if let some (_, e) := Parse.extOf n d then
        unless (← getEnv).contains e.const do
          liftCoreM (declConst e.const d)
        modifyEnv (Expand.relRegistry.addEntry · (.ext e n))
    modifyEnv (Expand.relRegistry.addEntry · (.prog n ns os))
    modifyEnv (Expand.relRegistry.addEntry · (.chain n homes))

/-- `rel_program n where …`, read in the current namespace and `open`s (module design §2.3): no program is in
    scope that is not `open`ed or written qualified. -/
@[command_elab relProgram] def elabRelProgram : CommandElab := fun stx => do
  match program (← getFileMap) (← scopeHere) stx[4].getArgs with
  | .error e => throwErrorAt stx "{e}"
  | .ok (prog, s) => define stx stx[2] prog s.used

/-- `rel_program n from base upto x where …`: the replacements read in `base`'s scope and objects. -/
@[command_elab relVariant] def elabRelVariant : CommandElab := fun stx => do
  let b ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[4])
  let base ← programOf b
  let reg := Expand.relRegistry.getState (← getEnv)
  let some (_, bns, bos) := reg.progs.find? (·.1 == b) | throwErrorAt stx[4] "`{b}` is no rel_program"
  let (res, ns) := resolverAt (← getEnv) (← getOptions) reg bns bos
  let s := Parse.after { cs := #[], res, ns } (base.filter fun | .obj .. => true | _ => false)
  let named : Decl → Option String := fun | .defn _ x .. => some x | _ => none
  match program (← getFileMap) s stx[7].getArgs with
  | .error e => throwErrorAt stx "{e}"
  | .ok (news, s') => do
    for d in news do
      match named d with
      | some x => unless base.any (named · == some x) do throwErrorAt stx "`{x}` is no definition of `{b}`"
      | none => throwErrorAt stx "a variant only replaces definitions"
    let kept := base.filter fun | .check .. | .«theorem» .. => false | _ => true
    let kept ← if stx[5].getNumArgs == 0 then pure kept else do
      let x ← match (wordOf stx[5][1]).run (← getFileMap) |>.run' s with
        | .ok x => pure x
        | .error e => throwErrorAt stx[5] "{e}"
      match kept.findIdx? (named · == some x) with
      | some k => pure (kept.take (k + 1))
      | none => throwErrorAt stx[5] "`{x}` is no definition of `{b}`"
    define stx stx[2] (kept.map fun d => ((named d).bind fun x => news.find? (named · == some x)).getD d) s'.used
      ((reg.chains.lookup b).getD []) (some (bns, bos))

/-- `decl_line% c`: the line the declaration `c` is named at, so a test writes a position in `c`'s text as `c`'s line
    plus an offset, which holds wherever `c` moves in its file. -/
elab "decl_line% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let some r ← findDeclarationRanges? n | throwErrorAt c "`{n}` has no declaration range to read its line from"
  pure (mkNatLit r.selectionRange.pos.line)

end LeetQ.Rel.Lang.Embed
