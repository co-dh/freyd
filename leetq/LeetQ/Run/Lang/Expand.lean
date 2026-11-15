import Lean
import LeetQ.Run.Lang.Gen
import LeetQ.Run.Lang.Elab
import LeetQ.Run.Lang.Parse

/-! The expander of `rel_program n`: each closed definition `x ≜ …` becomes the Lean definition `n.x : CRel A B`,
    a composition of `CRel` ops (`Gen`), so its ok bit is the `&&` of the ops it runs. At elaboration time the
    program is elaborated (`elabE`, `build`) to its core term `Tm`, as a run does; the term is then read into a
    Lean `Expr` constructor by constructor. Every closed sub-term (no keys, no fixed-point variable) becomes one
    constant `n.c.<i>`, structurally equal ones the same constant, so it is computed once; a fixed point's body is a Lean `fun X => …`; a closed `≫`/`∩`/`−`/`\` runs as a bit-matrix plan. -/

namespace LeetQ.Rel.Lang

open LeetQ.Rel LeetQ.Rel.Alg

/-- An object variable left in an object. -/
def OTy.poly : OTy → Bool
  | .mv _ => true
  | .prod a b | .sum a b => a.poly || b.poly
  | .arr a => a.poly
  | .base _ => false

def objInfo (env : Env) (n : String) : ObjDef → Except Err ObjInfo
  | .elems ws => pure { ty := .base n, elems := ws, uni := some ⟨_, col ((List.range ws.length).map Int64.ofNat)⟩ }
  | .range lo hi =>
    pure { ty := .base n, range := some (lo, hi), uni := some ⟨_, col ((List.range (hi + 1 - lo).toNat).map fun k : Nat => Int64.ofInt (lo + k))⟩ }
  | .alias o => do let (t, _) ← (oty env [] o).run {}; pure { ty := t }

/-- The definition `d` whose constant is `c`, as a use sees it. `prelude.perm` is its own converse, the one converse
    rule kept for a definition (`Tm.own`): `perm° = perm` is a theorem the language cannot derive from the fold
    `perm` is. `prelude.tails`, `prefix`, `suffix`, `concat` run as their slice forms, each read back against
    the list function the prelude's fold is (`rep_tailsC`, `rep_prefixC`, `rep_suffixC`, `rep_concatC`); `filter(p)`, `takewhile(p)` (given
    one relation, not a family) as their mask forms, whose read-back theorems (`rep_filterC`, `rep_takewhileC`) are
    not proved yet. `imported`: `d` is another program's, so an error its body raises at a use names `c` and its
    line there, at the use; one about the arguments (at the use) passes as it is. -/
def useDef (c : Lean.Name) (imported : Bool) (d : Def) : Def :=
  { d with apply := fun p as => do
      let reword (e : Err) : M Arg :=
        throw (if e.pos == p then e else ⟨p, s!"in `{c}` (its line {e.pos.line}): {e.msg}"⟩)
      let r ← if imported then tryCatch (d.apply p as) reword else d.apply p as
      -- the body's positions are its program's: at the use, so what `build` raises later is at the use
      match c, r with
      | `LeetQ.Rel.Programs.prelude.perm, .rel q s t => pure (.rel (.own (q.at p)) s t)
      | `LeetQ.Rel.Programs.prelude.tails, .rel _ s@(.arr b) t => pure (.rel (.tails b) s t)
      | `LeetQ.Rel.Programs.prelude.prefix, .rel _ s@(.arr b) t => pure (.rel (.«prefix» b) s t)
      | `LeetQ.Rel.Programs.prelude.suffix, .rel _ s@(.arr b) t => pure (.rel (.suffix b) s t)
      | `LeetQ.Rel.Programs.prelude.concat, .rel _ s t@(.arr b) => pure (.rel (.concat b) s t)
      | `LeetQ.Rel.Programs.prelude.filter, .rel q s t =>
        pure (.rel (match as with | [.rel a _ _] => .filter a | _ => if imported then q.at p else q) s t)
      | `LeetQ.Rel.Programs.prelude.takewhile, .rel q s t =>
        pure (.rel (match as with | [.rel a _ _] => .takewhile a | _ => if imported then q.at p else q) s t)
      | _, .rel q s t => pure (.rel (if imported then q.at p else q) s t)
      | _, .fam q i a b => pure (.fam (if imported then q.at p else q) i a b) }

/-! ### Printing a relation with the program's names -/

/-- An array of the printed elements `xs`, as a literal's side reads it (§c): two or more juxtaposed, else
    bracketed; `item`: it stands next to others (in an array, after `inl`), so it is always bracketed. -/
def arrText (item : Bool) (xs : List String) : String :=
  Tup.render item (.arr (xs.map .leaf))

/-- An element printed with the program's names, as a literal's side reads it (§c): a named element by its name,
    a number as itself, an array by `arrText`, its elements as items. -/
def showEl (objs : Objs) (item : Bool) : OTy → (A : Obj) → A.El → String
  | .base n, .atom .long, x =>
    let v : Int64 := x
    match objs.lookup n with
    | some i => if i.range.isSome then toString v else (i.elems[v.toInt.toNat]?).getD (toString v)
    | none => toString v
  | .prod a b, .prod A B, (x, y) => s!"({showEl objs false a A x}, {showEl objs false b B y})"
  | .sum a _, .sum A _, .inl x => s!"inl {showEl objs true a A x}"
  | .sum _ b, .sum _ B, .inr y => s!"inr {showEl objs true b B y}"
  | .arr a, .arr A, xs => arrText item (xs.map (showEl objs true a A))
  | _, _, _ => "?"

/-- The order a print lists elements in: a number by its value (`-2` before `-1`, `2` before `10`), a named
    element by its name, a pair and an array lexicographically, `inl` before `inr`. -/
def cmpEl (objs : Objs) : OTy → (A : Obj) → A.El → A.El → Ordering
  | .base n, .atom .long, x, y =>
    let (v, w) : Int64 × Int64 := (x, y)
    if ((objs.lookup n).bind (·.range)).isSome then compare v.toInt w.toInt
    else compare (showEl objs false (.base n) (.atom .long) x) (showEl objs false (.base n) (.atom .long) y)
  | .prod a b, .prod A B, (x, y), (x', y') => (cmpEl objs a A x x').then (cmpEl objs b B y y')
  | .sum a _, .sum A _, .inl x, .inl y => cmpEl objs a A x y
  | .sum _ b, .sum _ B, .inr x, .inr y => cmpEl objs b B x y
  | .sum _ _, .sum _ _, .inl _, .inr _ => .lt
  | .sum _ _, .sum _ _, .inr _, .inl _ => .gt
  | .arr a, .arr A, xs, ys =>
    let (xs, ys) : List A.El × List A.El := (xs, ys)
    ((xs.zip ys).foldl (fun (o : Ordering) (x, y) => o.then (cmpEl objs a A x y)) Ordering.eq).then (compare xs.length ys.length)
  | s, A, x, y => compare (showEl objs false s A x) (showEl objs false s A y)

/-- A relation printed as its set of pairs, sorted by `cmpEl`. -/
def showRel (objs : Objs) (s t : OTy) {A B : Obj} (R : Rel A B) : String :=
  let ps := R.nub.toList.mergeSort fun (x, y) (x', y') => ((cmpEl objs s A x x').then (cmpEl objs t B y y')) != .gt
  "{" ++ ", ".intercalate (ps.map fun (x, y) => s!"({showEl objs false s A x}, {showEl objs false t B y})") ++ "}"

/-- A declared object as a print reads it: its names and range, no universe. -/
def infoOf (ty : OTy) (elems : List String) (range : Option (Int × Int)) : ObjInfo := { ty, elems, range }

/-- A `print`'s line, the term's text `x` and its value; and the value's ok bit. -/
def printText (A B : Obj) (objs : Objs) (x : String) (s t : OTy) (c : CRel A B) : String × Bool :=
  (s!"{x} = {showRel objs s t c.rel}", c.ok)

/-- A `check` at `p` that does not hold, `x ⊑ y` (and `y ⊑ x` for `=`), as its error; and the sides' ok bits. -/
def checkErr (A B : Obj) (objs : Objs) (p : Pos) (x y : String) (eq : Bool) (s t : OTy) (R S : CRel A B) :
    Option Err × Bool :=
  (if R.rel ⊑ S.rel && (!eq || S.rel ⊑ R.rel) then none
   else some ⟨p, s!"check failed: {x} = {showRel objs s t R.rel}, {y} = {showRel objs s t S.rel}"⟩, R.ok && S.ok)

/-- A program's failures: each `check` that does not hold, and an op out of capacity anywhere in its definitions,
    prints or checks (an ok bit false), which no value of the program can be trusted after; each definition not
    ok is named with the `μ`s it holds (`ms`), whose rounds reaching their cap also clear the bit. -/
def failures (ds : List (String × Gen.Gv)) (ms : List (String × List String)) (ps : List (String × Bool))
    (cs : List (Option Err × Bool)) : List Err :=
  cs.filterMap (·.1) ++ if ds.all (·.2.2.2.ok) && ps.all (·.2) && cs.all (·.2) then [] else
    let bad := (ds.filter (!·.2.2.2.ok)).map fun (x, _) =>
      s!"; in {x}" ++ String.join (((ms.lookup x).getD []).map (s!", or {·}"))
    [⟨{}, "an op ran out of capacity (its twin's ok bit is false)" ++ String.join bad⟩]

namespace Expand

/-- A top-level term, a `print`'s or a `check` side's: closed, with its objects as the program names them. -/
abbrev Top := ((A : Obj) × (B : Obj) × Tm A B false) × OTy × OTy

/-- A `check`: where, both sides' texts, `=` (else `⊑`), the objects as named, both sides at one type. -/
abbrev Chk := Pos × String × String × Bool × OTy × OTy × ((A : Obj) × (B : Obj) × Tm A B false × Tm A B false)

/-- A definition elaborated once (`once`): its name, its count `n` of object variables (whose universes are the
    variables `0 … n-1`), its parameters' objects (the variables from `n` on), its body. -/
abbrev Once := String × Nat × List (Obj × Obj) × Res

/-- What a program reads: its closed definitions, its prints (text and term), its checks, its objects, and its
    definitions elaborated once. -/
abbrev Read := List (String × Res) × List (String × Top) × List Chk × Objs × List Once × List (String × String) ×
  List (String × String)

/-- The object variables of a definition, in order, each once: its parameters' then its type's. -/
def varsOf (qs : List Param) (ty : OExp × OExp) : List String :=
  (qs.flatMap (fun P => match P.ty with | some (x, y) => x.vars ++ y.vars | none => []) ++ ty.1.vars ++ ty.2.vars).eraseDups

/-- `n(qs) ≜ e : ty` built once, its object variables `vs` rigid: each an object of its own whose universe is the
    variable of its place, each parameter the variable after them (`Once`). A body that does not build so (it
    needs keys, or a universe of an object made of variables) is an error, which names `n`. -/
def once (env : Env) (p : Pos) (n : String) (qs : List Param) (e : Expr) (ty : OExp × OExp) (vs : List String) :
    Except Err (Once × List (String × String)) := do
  let nv := vs.length
  let objs := vs.zipIdx.map (fun (v, k) => (v, ({ ty := .base v, uniVar := some k } : ObjInfo))) ++ env.objs
  let rigid := vs.map fun v => (v, OTy.base v)
  let ((r, os), st) ← (do
    let mut params : List (String × Arg) := []
    let mut os : List (Obj × Obj) := []
    for (P, j) in qs.zipIdx do
      let some (x, y) := P.ty | throw ⟨p, s!"parameter '{P.name}' declares no type"⟩
      let s ← oty env rigid x; let t ← oty env rigid y
      params := params ++ [(P.name, .rel (.var p (nv + j) s t) s t)]
      os := os ++ [(← objOf p s, ← objOf p t)]
    let env' := { env with objs, params }
    let r ← elabE env' none e
    let (q, s, t) := r.plain
    declared env' p n rigid ty s t
    settleNil env'.one p q
    pure (r, os) : M (Arg × List (Obj × Obj))).run { fixes := nv + qs.length }
  -- a body that needs keys is read on its source's universe, a variable's when the source is one, as a top-level
  -- term is (`top`): the constant returns a closed relation (decision M)
  let (q, s, _) := r.plain
  match ← build objs st p (.close p q s s!"`{n}` is elaborated once, to a constant returning a closed relation") with
  | ⟨A, B, false, t⟩ => pure ((n, nv, os, ⟨A, B, false, t⟩), st.expanded)
  | _ => throw ⟨p, s!"internal: `{n}` closed still needs keys"⟩

/-- `n` elaborated once to the constant `c` (`once`), its object variables `vs`, declared `ty`: each use is the
    call `c(…)` (`Pre.call`); the expansion `d` gives its type and is what the analyses read. A family argument is
    refused here, a non-declared object or an argument that needs keys at `build` (decision M). -/
def callDef (env : Env) (qs : List Param) (ty : OExp × OExp) (vs : List String) (c : Lean.Name) (d : Def) : Def :=
  { d with apply := fun p as => do
      let r ← d.apply p as
      let (bs, m) ← (qs.zip as).foldlM (fun (bs, m) (P, a) => do
        let (b, j, m) ← bind env p P a m; pure (bs ++ [(P, b.2, j)], m)) (([], []) : List (Param × Arg × Option OTy) × List (String × OTy))
      -- a use the constant cannot take expands the body, recorded (decision M, until step 5)
      let expand (why : String) : M Arg := do
        modify fun st => { st with expanded := st.expanded ++ [(c.toString, s!"{p}: {why}")] }; pure r
      if let some (P, _) := bs.find? (·.2.2.isSome) then return ← expand s!"'{P.name}' is given a family"
      let .rel q s t := r | throw ⟨p, s!"internal: `{c}` given relations is a family"⟩
      -- a variable only the declared result names is fixed by the result's type, as `declared` fixes it
      let m ← vs.foldlM (fun m v => do if (m.lookup v).isSome then pure m else return (v, ← fresh) :: m) m
      unify p "" s (← oty env m ty.1); unify p "" t (← oty env m ty.2)
      let some us := vs.mapM (m.lookup ·) | throw ⟨p, s!"internal: `{c}` has an object variable no type names"⟩
      -- an object made of others is no declared object; one still open is checked at `build`
      let st ← get
      if let some u := us.find? (fun u => match zonk st u with | .base _ | .mv _ => false | _ => true) then
        return ← expand s!"an object variable is {zonk st u}, not a declared object"
      -- an argument that needs keys (`≠`) is read on its source's universe, as a top-level term is (`top`); the
      -- universe is looked up at `build`, in the objects of the program making the call, not of the one defining `n`
      let why := s!"`{c}` takes only closed relations (decision M)"
      pure (.rel (.call p c us (bs.map fun (_, b, _) => let (x, a, _) := b.plain; Pre.close p x a why) q s t) s t) }

/-- A top-level term, `r` its elaboration `e` with the objects `st`: closed on its source's universe when it needs
    keys, refused where that object has none. -/
def top (env : Env) (st : St) (p : Pos) (e : Expr) (r : Arg) : Except Err Top := do
  let (q, s, t) := r.plain
  let ⟨A, B, d, tm⟩ ← build env.objs st p (.close p q s noLeft)
  match d, tm with
  | false, tm => pure (⟨A, B, tm⟩, zonk st s, zonk st t)
  | true, _ => throw ⟨p, s!"{e.show}: {zonk st s} has no universe; compose a set of its elements before it (§a)"⟩

/-- `check e = f` at `p` (`⊑` when `eq` is false), with the uses of a constant that expanded its body: the two sides
    elaborated together, one type, an object one side leaves open being the other's (§c). -/
def checkOf (env : Env) (p : Pos) (e f : Expr) (eq : Bool) : Except Err (Chk × List (String × String)) := do
  let ((r, r'), st) ← (do
    let r ← elabE env none e; let r' ← elabE env none f
    let (_, s, t) := r.plain; let (_, s', t') := r'.plain
    let st ← get
    try unify p "" s' s; unify p "" t' t
    catch _ => throw ⟨p, s!"check: the sides have types {zonk st s} ⟶ {zonk st t} and {zonk st s'} ⟶ {zonk st t'}"⟩
    settleNil env.one p r.plain.1; settleNil env.one p r'.plain.1
    pure (r, r') : M (Arg × Arg)).run {}
  let (⟨A, B, R⟩, s, t) ← top env st p e r
  let (⟨A', B', S⟩, s', t') ← top env st p f r'
  if h : A' = A ∧ B' = B then pure ((p, e.show, f.show, eq, s, t, ⟨A, B, R, h.1 ▸ h.2 ▸ S⟩), st.expanded)
  else throw ⟨p, s!"check: the sides have types {s} ⟶ {t} and {s'} ⟶ {t'}"⟩

/-- The declarations of `prog`, in order, from the environment `env`: each closed definition (no keys) with its
    core term, each `print` and `check` with its terms; nothing evaluated: a definition is in scope as its built
    term. A parametric definition is called where `calls` holds its constant `own.x`; else, when `emitting`, it is
    built once for `emit` (`once`), and expanded at each use here, where its constant does not exist yet. -/
def walk (prog : Program) (env : Env) (wrap : String → Def → Def) (own : Lean.Name) (calls : Lean.Name → Bool)
    (emitting : Bool) (imported : Bool := false) :
    Except Err (Env × List (String × Res) × List (String × Top) × List Chk × List Once × List (String × String) ×
      List (String × String)) := do
  let mut env := env
  let mut os : List Once := []
  let mut xs : List (String × String) := []
  let mut ex : List (String × String) := []
  let mut ds : List (String × Res) := []
  let mut pr : List (String × Top) := []
  let mut cs : List Chk := []
  for d in prog do
    -- an imported program's prints, checks and theorems ran where it was defined; only its scope is read here
    if imported && (match d with | .print .. | .check .. | .«theorem» .. => true | _ => false) then continue
    match d with
    | .obj _ n od =>
      -- an imported program's object is its constant's, so the importer's types name the same object (§2.3);
      -- an alias stays the object it stands for
      if imported then
        let c := (Parse.constOf own n).toString
        let i ← objInfo env c od
        env := { env with objs := (n, i) :: (c, i) :: env.objs }
      else env := { env with objs := (n, ← objInfo env n od) :: env.objs }
    | .defn p n ps b ty =>
      let missing := ps.any (·.ty.isNone) || match b with | .rel _ => ty.isNone | .test .. => false
      if missing then throw ⟨p, s!"`{n}` has no type; it is {← (inferSig env n ps b).run' {}}"⟩
      match ps, b, ty with
      | [], .rel e, ty =>
        let rigid := match ty with | some (a, b) => (a.vars ++ b.vars).map fun v => (v, OTy.base v) | none => []
        let (r, st) ← (do
          let r ← elabE env none e
          if let some ty := ty then let (_, s, t) := r.plain; declared env p n rigid ty s t
          settleNil env.one p r.plain.1
          pure r).run {}
        ex := ex ++ st.expanded
        let (q, s, t) := r.plain
        let s := zonk st s; let t := zonk st t
        let each := wrap n (mkDef env n p [] (.rel e) ty)
        if !rigid.isEmpty || s.poly || t.poly then env := { env with defs := (n, each) :: env.defs }; continue
        let q := if (uniOf env.objs s).isSome then Pre.close p q s noLeft else q
        let res@⟨_, _, dm, _⟩ ← match build env.objs st p q, test env.objs st p q with
          | .ok r, _ => pure r
          | .error _, .ok _ => env := { env with defs := (n, each) :: env.defs }; continue
          | .error e, .error _ => throw e
        env := { env with defs := (n, wrap n { arity := 0, apply := fun _ _ => pure (.rel (.tm res) s t) }) :: env.defs }
        if !dm then ds := ds ++ [(n, res)]
      | qs, b, ty =>
        let d := mkDef env n p qs b ty
        match b, ty with
        | .rel e, some ty =>
          let vs := varsOf qs ty
          let c := Parse.constOf own n
          if calls c then env := { env with defs := (n, wrap n (callDef env qs ty vs c d)) :: env.defs }; continue
          if emitting then
            -- a body the spike cannot make a constant (arithmetic or a universe on an object variable: step 5) stays
            -- expanded at each use, as before; the reason is kept, emitted as `n.notOnce`
            match once env p n qs e ty vs with
            | .ok (o, e) => os := os ++ [o]; ex := ex ++ e
            | .error e => xs := xs ++ [(n, s!"{e.pos}: {e.msg}")]
        | _, _ => pure ()
        env := { env with defs := (n, wrap n d) :: env.defs }
    | .print p e =>
      let (r, st) ← (do let r ← elabE env none e; settleNil env.one p r.plain.1; pure r).run {}
      ex := ex ++ st.expanded
      pr := pr ++ [(e.show, ← top env st p e r)]
    | .check p e f eq => let (c, e') ← checkOf env p e f eq; cs := cs ++ [c]; ex := ex ++ e'
    | .«theorem» p n ps e f eq on steps =>
      -- every term of the chain at the statement's type, the parameters at their declared ones (§3)
      let _ ← (do
        let (_, env') ← bindSig env ps
        let (_, s, t) := (← elabE env' none e).plain
        for (q, x, what) in (p, f, "its right side") :: steps.map fun (q, _, x, _) => (q, x, "this step") do
          let (_, s', t') := (← elabE env' none x).plain
          let st ← get
          try unify q "" s' s; unify q "" t' t
          catch _ => throw ⟨q, s!"theorem `{n}`: {what} {x.show} is {zonk st s'} ⟶ {zonk st t'}, " ++
            s!"the statement's {e.show} is {zonk st s} ⟶ {zonk st t}"⟩
        : M Unit).run {}
      -- `on A`: each link of the chain (the statement itself when there is none) evaluated as a `check`
      if let some a := on then
        let mut x := e
        for (q, k, y) in if steps.isEmpty then [(p, eq, f)] else steps.map fun (q, k, y, _) => (q, k, y) do
          let (c, e') ← checkOf env q (.comp a x) (.comp a y) k
          cs := cs ++ [c]; ex := ex ++ e'; x := y
  pure (env, ds, pr, cs, os, xs, ex)

/-- What the program `own` declares, `prog`, read after the programs `homes` its names reach (their definitions
    and objects), each read in order with its own resolver `res h` (module design §2.3), its definitions in scope
    for the next by constant. A definition whose constant `calls` holds is called, not expanded. With no `res`, a
    text read outside any Lean scope: each program sees those before it unqualified (`Parse.openAll`). -/
def read (calls : Lean.Name → Bool) (homes : List (Lean.Name × Program)) (prog : Program)
    (own : Lean.Name := .anonymous)
    (res : Lean.Name → String → Found := fun h => Parse.openAll (homes.takeWhile (·.1 != h))) : Except Err Read := do
  let mut ext : List (Lean.Name × Def) := []
  let mut xo : List (Lean.Name × ObjInfo) := []
  for (h, hp) in homes do
    let env : Env := { res := res h, ext, extObjs := xo, objs := xo.map fun (c, i) => (c.toString, i) }
    let e := (← (walk hp env (fun k => useDef (Parse.constOf h k) true) h calls false true).mapError
      (Err.inProg h.toString)).1
    for d in hp do
      if let some (k, x) := Parse.extOf h d then
        match x.obj, e.objs.lookup x.const.toString, e.defs.lookup k with
        | true, some i, _ => xo := (x.const, i) :: xo
        | false, _, some df => ext := (x.const, df) :: ext
        | _, _, _ => pure ()
  let env : Env := { res := res own, ext, extObjs := xo, objs := xo.map fun (c, i) => (c.toString, i) }
  let (e, ds, ps, cs, os, xs, ex) ← walk prog env (fun k => useDef (Parse.constOf own k) false) own calls true
  pure (ds, ps, cs, e.objs, os, xs, ex)

/-! ### The core term as an `Expr` -/

open Lean Meta

deriving instance ToExpr for QLean.QAtomicType
deriving instance ToExpr for LeetQ.Rel.Obj
deriving instance ToExpr for Lang.Pos
deriving instance ToExpr for OTy

/-- The fixed-point variables `t` reads unbound. -/
def fv : {A B : Obj} → {d : Bool} → Tm A B d → List Nat
  | _, _, _, .top V => fv V
  | _, _, _, .comp R S | _, _, _, .meet R S | _, _, _, .join R S | _, _, _, .diff R S => fv R ++ fv S
  | _, _, _, .pair R S | _, _, _, .prod R S | _, _, _, .junc R S | _, _, _, .arg R S => fv R ++ fv S
  | _, _, _, .conv R | _, _, _, .dom R | _, _, _, .ran R | _, _, _, .lam R | _, _, _, .E R | _, _, _, .map R => fv R
  | _, _, _, .filter R | _, _, _, .takewhile R => fv R
  | _, _, _, .est R | _, _, _, .thin R | _, _, _, .own R | _, _, _, .thinL R | _, _, _, .merge R => fv R
  | _, _, _, .loop R | _, _, _, .flat R => fv R
  | _, _, _, .ldiv R S U V | _, _, _, .rdiv R S U V => fv R ++ fv S ++ fv U ++ fv V
  | _, _, _, .fold e S | _, _, _, .foldI e S => fv e ++ fv S
  | _, _, _, .var k => [k]
  | _, _, _, .nu k S b => fv S ++ (fv b).filter (· != k)
  | _, _, _, .mu k _ _ b => (fv b).filter (· != k)
  | _, _, _, .refold k _ ch b => fv ch ++ (fv b).filter (· != k)
  | _, _, _, .juncD R S => fv R ++ fv S
  | _, _, _, _ => []

/-- The `μ`s in `t`, each as the failure it reports when its rounds reach the cap. -/
def mus : {A B : Obj} → {d : Bool} → Tm A B d → List String
  | _, _, _, .top V => mus V
  | _, _, _, .comp R S | _, _, _, .meet R S | _, _, _, .join R S | _, _, _, .diff R S => mus R ++ mus S
  | _, _, _, .pair R S | _, _, _, .prod R S | _, _, _, .junc R S | _, _, _, .arg R S => mus R ++ mus S
  | _, _, _, .conv R | _, _, _, .dom R | _, _, _, .ran R | _, _, _, .lam R | _, _, _, .E R | _, _, _, .map R => mus R
  | _, _, _, .est R | _, _, _, .thin R | _, _, _, .own R | _, _, _, .thinL R | _, _, _, .merge R => mus R
  | _, _, _, .loop R | _, _, _, .flat R => mus R
  | _, _, _, .ldiv R S U V | _, _, _, .rdiv R S U V => mus R ++ mus S ++ mus U ++ mus V
  | _, _, _, .fold e S | _, _, _, .foldI e S => mus e ++ mus S
  | _, _, _, .nu _ S b => mus S ++ mus b
  | _, _, _, .mu _ w n b => s!"{w} ran its cap of {n} rounds without reaching a fixed point" :: mus b
  | _, _, _, .refold _ w ch b =>
    s!"{w} met a cycle: a node its coalgebra c reaches from itself, so c is not well-founded there" :: mus ch ++ mus b
  | _, _, _, .juncD R S => mus R ++ mus S
  | _, _, _, _ => []

/-- A term that needs no keys and reads no fixed-point variable: computed once, its own constant (`share`). -/
def closed {A B : Obj} {d : Bool} (t : Tm A B d) : Bool := !d && (fv t).isEmpty

/-- `t` with each closed sub-term `R` wrapped as `.share k R`, `k` the next number: `code` keeps each number's
    code and `fv` stops there (a share is closed), so building and proving a closed sub-term never rebuilds it. -/
def number : {A B : Obj} → {d : Bool} → Tm A B d → StateM Nat (Tm A B d)
  | _, _, _, .top V => do w (.top (← number V))
  | _, _, _, .comp R S => do w (.comp (← number R) (← number S))
  | _, _, _, .conv R => do w (.conv (← number R))
  | _, _, _, .meet R S => do w (.meet (← number R) (← number S))
  | _, _, _, .join R S => do w (.join (← number R) (← number S))
  | _, _, _, .diff R S => do w (.diff (← number R) (← number S))
  | _, _, _, .dom R => do w (.dom (← number R))
  | _, _, _, .ran R => do w (.ran (← number R))
  | _, _, _, .ldiv R S U V => do w (.ldiv (← number R) (← number S) (← number U) (← number V))
  | _, _, _, .rdiv R S U V => do w (.rdiv (← number R) (← number S) (← number U) (← number V))
  | _, _, _, .pair R S => do w (.pair (← number R) (← number S))
  | _, _, _, .prod R S => do w (.prod (← number R) (← number S))
  | _, _, _, .junc R S => do w (.junc (← number R) (← number S))
  | _, _, _, .lam R => do w (.lam (← number R))
  | _, _, _, .E R => do w (.E (← number R))
  | _, _, _, .map R => do w (.map (← number R))
  | _, _, _, .filter R => do w (.filter (← number R))
  | _, _, _, .takewhile R => do w (.takewhile (← number R))
  | _, _, _, .est Q => do w (.est (← number Q))
  | _, _, _, .thin Q => do w (.thin (← number Q))
  | _, _, _, .own R => do w (.own (← number R))
  | _, _, _, .thinL Q => do w (.thinL (← number Q))
  | _, _, _, .merge Q => do w (.merge (← number Q))
  | _, _, _, .loop F => do w (.loop (← number F))
  | _, _, _, .fold e S => do w (.fold (← number e) (← number S))
  | _, _, _, .share _ R => number R
  | _, _, _, .foldI e S => do w (.foldI (← number e) (← number S))
  | _, _, _, .flat R => do w (.flat (← number R))
  | _, _, _, .nu k S b => do w (.nu k (← number S) (← number b))
  | _, _, _, .mu k s n b => do w (.mu k s n (← number b))
  | _, _, _, .refold k s ch b => do w (.refold k s (← number ch) (← number b))
  | _, _, _, .juncD R S => do w (.juncD (← number R) (← number S))
  | _, _, _, .arg f x => do w (.arg (← number f) (← number x))
  | _, _, _, t => w t
where w {A B : Obj} {d : Bool} (t : Tm A B d) : StateM Nat (Tm A B d) :=
  if closed t then modifyGet fun k => (.share k t, k + 1) else pure t

/-- `t` needs no keys and does not read the variable `k`: fixed across the rounds of `k`'s fixed point, though it
    may read a parameter of a definition elaborated once or an enclosing fixed point's variable. -/
def free (k : Nat) {A B : Obj} {d : Bool} (t : Tm A B d) : Bool := !d && !(fv t).contains k

/-- `X C`, `X` the variable `k`, `C` free of it: `C`. -/
def varComp (k : Nat) : {A B : Obj} → {d : Bool} → Tm A B d → Option ((D : Obj) × Tm D B false)
  | _, _, _, .comp (B := D) (e := false) (.var k') C => if k' == k && free k C then some ⟨D, C⟩ else none
  | _, _, _, .share _ R => varComp k R
  | _, _, _, _ => none

/-- The arcs of an AC-3 body `S ∩ ⋂ₖ Aₖ\(X Cₖ)` over the variable `k`, its conjuncts free of `k` skipped (they
    are `S`); `none` for any other body. -/
def arcs (k : Nat) : {V D : Obj} → {d : Bool} → Tm V D d →
    Option (List (Tm V V false × Tm D D false × Tm V V false × Tm D D false))
  | _, _, _, .share _ R => arcs k R
  | _, _, _, .meet R S => return (← arcs k R) ++ (← arcs k S)
  | V, D, _, .ldiv (A := V') R S UB UC =>
    if free k R && free k S && free k UB && free k UC then some [] else do
    let ⟨D', C⟩ ← varComp k S
    unless free k R && free k UB && free k UC do none
    if h : V' = V ∧ D' = D then some [(h.1 ▸ R, h.2 ▸ C, UB, UC)] else none
  | _, _, _, t => if free k t then some [] else none

/-- The constant of each closed value, and the code of each numbered sub-term (`number`). -/
abbrev RM := StateT (Std.HashMap Lean.Expr Name × Std.HashMap Nat Lean.Expr) MetaM

/-- The constant `c : ty := v`, compiled, with the heartbeats a `def` command of its own would have: one
    `rel_program` command adds them all, and a program's count of constants is no measure of any one's cost.
    Regular hints, as `def` gives: an opaque `c` makes the kernel unfold the other side of `c =?= v` first. -/
def addConst (c : Name) (ty v : Lean.Expr) : MetaM Unit := withCurrHeartbeats do
  let hints := .regular (getMaxHeight (← getEnv) v + 1)
  addAndCompile (.defnDecl { name := c, levelParams := [], type := ty, value := v, hints, safety := .safe })

def oE (A : Obj) : Lean.Expr := toExpr A
def uE (n : USize) : Lean.Expr := mkApp (mkConst ``USize.ofNat) (toExpr n.toNat)
def bE (b : Bool) : Lean.Expr := toExpr b
def g (n : Name) (as : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) as

/-- The bytes `b` as hex text, two lowercase digits a byte (`Gen.unhex` reads it back). -/
def hex (b : ByteArray) : String :=
  -- ASCII bytes then one UTF-8 check: `String.push` per digit dominated the expansion's profile
  let d (x : UInt8) : UInt8 := if x < 10 then 48 + x else 87 + x
  String.fromUTF8! (b.foldl (fun o x => (o.push (d (x / 16))).push (d (x % 16))) (.emptyWithCapacity (2 * b.size)))

/-- An atom column rebuilt from its payload (`Gen.atom`): a fixed-width or boolean one; a symbol, general,
    Frame-of-Reference or ALP payload is not rebuilt, and says so. -/
def atomE (t : QLean.QAtomicType) (n : USize) (x : Arr t n) : Except String Lean.Expr :=
  match x.enc with
  | .bytes b => pure (g ``Gen.atom #[toExpr t, uE n, toExpr false, mkStrLit (hex b)])
  | .bits b => pure (g ``Gen.atom #[toExpr t, uE n, toExpr true, mkStrLit (hex b)])
  | _ => throw s!"a column of {n} rows in a symbol, general, Frame-of-Reference or ALP payload cannot be rebuilt"

/-- A column rebuilt from its parts: each atom column from its payload (`atomE`), the rest by `Vals`'s shape. -/
def valsE : (A : Obj) → (n : USize) → Vals A n → Except String Lean.Expr
  | .atom t, n, x => atomE t n x
  | .prod a b, n, x => do
    pure (g ``Gen.pairV #[oE a, oE b, uE n, ← valsE a n x.1, ← valsE b n x.2])
  | .arr b, n, ⟨m, lo, hi, p⟩ => do
    pure (g ``Gen.arrV #[oE b, uE n, uE m, ← atomE .long n lo, ← atomE .long n hi, ← valsE b m p])
  | .sum a b, n, ⟨l, r, tag, idx, x, y⟩ => do
    pure (g ``Gen.sumV #[oE a, oE b, uE n, uE l, uE r, ← atomE .boolean n tag, ← atomE .long n idx,
      ← valsE a l x, ← valsE b r y])

def relE {A B : Obj} (R : Rel A B) : Except String Lean.Expr := do
  pure (g ``Gen.relV #[oE A, oE B, uE R.n, ← valsE A R.n R.key, ← valsE B R.n R.val])

def liftE {α : Type} (x : Except String α) : RM α := match x with
  | .ok a => pure a
  | .error e => throwError "rel_program expansion: {e}"

mutual

/-- `t`'s code, `Gen.Fn d A B`: a closed `t` is its constant (`share`), any other its node; a numbered sub-term's
    is built once. -/
partial def code (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM Lean.Expr := do
  if let .share k R := t then
    if let some e := (← get).2[k]? then return e
    let e ← code pre ρ R
    modify fun (m, cs) => (m, cs.insert k e); return e
  if closed t then
    let c ← share pre A B (mkApp (← node pre ρ t) (mkConst ``Unit.unit))
    pure (g ``Gen.const #[oE A, oE B, mkConst c])
  else node pre ρ t

/-- The constant of the closed value `v : CRel A B`: one per structurally equal value. -/
partial def share (pre : Name) (A B : Obj) (v : Lean.Expr) : RM Name := do
  if let some c := (← get).1[v]? then return c
  let i := (← get).1.size
  let c := pre ++ `c ++ Name.mkSimple s!"c{i}"
  addConst c (mkApp2 (mkConst ``CRel) (oE A) (oE B)) v
  modify fun (m, cs) => (m.insert v c, cs); pure c

/-- The plan of `t` (`Gen.Pl d A B`) where its node has a bit rule. -/
partial def plan? (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM (Option Lean.Expr) := do
  if closed t then return some (g ``Gen.pleaf #[oE A, oE B, bE d, ← code pre ρ t])
  match A, B, d, t with
  | A, B, _, .val _ | A, B, _, .var _ => return some (g ``Gen.pleaf #[oE A, oE B, bE false, ← node pre ρ t])
  | A, _, _, .uni _ => return some (g ``Gen.pleaf #[oE A, oE A, bE false, ← node pre ρ t])
  | _, _, _, .share _ R | _, _, _, .own R => plan? pre ρ R
  | A, C, _, .comp (B := B) (d := d) (e := e) R S =>
    return some (g ``Gen.pcomp #[oE A, oE B, oE C, bE d, bE e, ← planOr pre ρ R, ← planOr pre ρ S])
  | B, A, _, .conv R => return some (g ``Gen.pconv #[oE A, oE B, ← planOr pre ρ R])
  | A, B, _, .meet (d := d) (e := e) R S =>
    return some (g ``Gen.pmeet #[oE A, oE B, bE d, bE e, ← planOr pre ρ R, ← planOr pre ρ S])
  | A, B, _, .join (d := d) (e := e) R S =>
    return some (g ``Gen.pjoin #[oE A, oE B, bE d, bE e, ← planOr pre ρ R, ← planOr pre ρ S])
  | A, B, _, .diff (d := d) (e := e) R S =>
    return some (g ``Gen.pdiff #[oE A, oE B, bE d, bE e, ← planOr pre ρ R, ← planOr pre ρ S])
  | B, C, _, .ldiv (A := A) R S UB UC => return some (g ``Gen.pldiv
      #[oE A, oE B, oE C, ← planOr pre ρ R, ← planOr pre ρ S, ← code pre ρ UB, ← code pre ρ UC])
  | _, _, _, _ => return none

/-- The plan of `t`, or its table as a leaf (`Gen.pleaf`). -/
partial def planOr (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM Lean.Expr := do
  match ← plan? pre ρ t with
  | some p => pure p
  | none => pure (g ``Gen.pleaf #[oE A, oE B, bE d, ← code pre ρ t])

/-- A call's head and its arguments before the last, applied: a partial application is never a constant. -/
partial def spine (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} : Tm A B false → RM Lean.Expr
  | .share _ f => spine pre ρ f
  | .arg f x => return mkApp (← spine pre ρ f) (← code pre ρ x)
  | .call c => return mkConst c
  | t => node pre ρ t

/-- `φ`'s body as `fun X : CRel A B => …`, the variable `k` read as `X`. -/
partial def body (pre : Name) (ρ : List (Nat × Lean.Expr)) (A B : Obj) (k : Nat) {d : Bool} (b : Tm A B d) :
    RM Lean.Expr :=
  withLocalDeclD `X (mkApp2 (mkConst ``CRel) (oE A) (oE B)) fun x => do
    mkLambdaFVars #[x] (← code pre ((k, x) :: ρ) b)

/-- `t`'s own node, its parts by `code` (or `planOr` where they run as bit matrices). -/
partial def node (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM Lean.Expr := do
  let c {X Y : Obj} {e : Bool} (u : Tm X Y e) := code pre ρ u
  let p {X Y : Obj} {e : Bool} (u : Tm X Y e) := planOr pre ρ u
  match A, B, d, t with
  | A, B, _, .val R => return g ``Gen.val #[oE A, oE B, ← liftE (relE R)]
  | A, _, _, .uni (m := m) U => return g ``Gen.uni #[oE A, uE m, ← liftE (valsE A m U)]
  | A, B, _, .zero => return g ``Gen.zero #[oE A, oE B]
  | A, _, _, .id => return g ``Gen.id #[oE A]
  | A, B, _, .top V => return g ``Gen.top #[oE A, oE B, ← c V]
  | _, B, _, .mem => return g ``Gen.mem #[oE B]
  | .prod A B, _, _, .outl => return g ``Gen.outl #[oE A, oE B]
  | .prod A B, _, _, .outr => return g ``Gen.outr #[oE A, oE B]
  | A, .sum _ B, _, .inl => return g ``Gen.inl #[oE A, oE B]
  | B, .sum A _, _, .inr => return g ``Gen.inr #[oE A, oE B]
  | A, C, true, .comp (B := B) (e := e) R S => return g ``Gen.comp #[oE A, oE B, oE C, bE e, ← c R, ← c S]
  | A, C, false, .comp (B := B) (e := e) R S => return g ``Gen.compB #[oE A, oE B, oE C, bE e, ← p R, ← p S]
  | B, A, _, .conv R => return g ``Gen.conv #[oE A, oE B, ← c R]
  | A, B, _, .meet (d := false) (e := false) R S => return g ``Gen.meetB #[oE A, oE B, ← p R, ← p S]
  | A, B, _, .diff (d := false) (e := false) R S => return g ``Gen.diffB #[oE A, oE B, ← p R, ← p S]
  | A, B, _, .meet (d := d) (e := e) R S => return g ``Gen.meet #[oE A, oE B, bE d, bE e, ← c R, ← c S]
  | A, B, _, .join (d := d) (e := e) R S => return g ``Gen.join #[oE A, oE B, bE d, bE e, ← c R, ← c S]
  | A, B, _, .diff (d := d) (e := e) R S => return g ``Gen.diff #[oE A, oE B, bE d, bE e, ← c R, ← c S]
  | A, _, d, .dom (B := B) R => return g ``Gen.dom #[oE A, oE B, bE d, ← c R]
  | B, _, _, .ran (A := A) R => return g ``Gen.ran #[oE A, oE B, ← c R]
  | B, C, _, .ldiv (A := A) R S UB UC => return g ``Gen.ldivB #[oE A, oE B, oE C, ← p R, ← p S, ← c UB, ← c UC]
  | A, B, _, .rdiv (C := C) R S UA UB => return g ``Gen.rdiv #[oE A, oE B, oE C, ← c R, ← c S, ← c UA, ← c UB]
  | A, .prod B C, _, .pair (d := d) (e := e) R S => return g ``Gen.pair #[oE A, oE B, oE C, bE d, bE e, ← c R, ← c S]
  | .prod A C, .prod B D, _, .prod R S => return g ``Gen.prod #[oE A, oE B, oE C, oE D, ← c R, ← c S]
  | .sum A B, C, _, .junc R S => return g ``Gen.junc #[oE A, oE B, oE C, ← c R, ← c S]
  | A, .arr B, _, .lam (d := d) R => return g ``Gen.lam #[oE A, oE B, bE d, ← c R]
  | .arr A, .arr B, _, .E (d := d) R => return g ``Gen.E #[oE A, oE B, bE d, ← c R]
  | .arr A, .arr B, _, .map (d := d) R => return g ``Gen.map #[oE A, oE B, bE d, ← c R]
  | .arr B, _, _, .filter (d := d) R => return g ``Gen.filter #[oE B, bE d, ← c R]
  | .arr B, _, _, .takewhile (d := d) R => return g ``Gen.takewhile #[oE B, bE d, ← c R]
  | _, B, _, .est Q => return g ``Gen.est #[oE B, ← c Q]
  | _, .arr B, _, .thin Q => return g ``Gen.thin #[oE B, ← c Q]
  | A, _, _, .tau => return g ``Gen.tau #[oE A]
  | A, .arr B, _, .nil => return g ``Gen.nil #[oE A, oE B]
  | _, .arr B, _, .cons => return g ``Gen.cons #[oE B]
  | .arr B, _, _, .uncons => return g ``Gen.uncons #[oE B]
  | .arr B, _, _, .length => return g ``Gen.length #[oE B]
  | _, _, _, .total => return mkConst ``Gen.total
  | .arr B, _, _, .inits => return g ``Gen.inits #[oE B]
  | .arr B, _, _, .tails => return g ``Gen.tails #[oE B]
  | .arr B, _, _, .«prefix» => return g ``Gen.«prefix» #[oE B]
  | .arr B, _, _, .suffix => return g ``Gen.suffix #[oE B]
  | _, .arr B, _, .concat => return g ``Gen.concat #[oE B]
  | _, .arr B, _, .cat => return g ``Gen.cat #[oE B]
  | .arr B, _, _, .uncat => return g ``Gen.uncat #[oE B]
  | .prod (.arr A) (.arr B), _, _, .zip => return g ``Gen.zip #[oE A, oE B]
  | _, .arr B, _, .snoc => return g ``Gen.snoc #[oE B]
  | .arr B, _, _, .unsnoc => return g ``Gen.unsnoc #[oE B]
  | .arr B, _, _, .atPos k => return g ``Gen.atPos #[oE B, toExpr k]
  | _, _, _, .own R => c R
  | .arr B, _, _, .setify => return g ``Gen.setify #[oE B]
  | .arr B, _, _, .bagify => return g ``Gen.bagify #[oE B]
  | _, .arr (.arr B), _, .tic => return g ``Gen.tic #[oE B]
  | .arr B, _, _, .thinL Q => return g ``Gen.thinL #[oE B, ← c Q]
  | _, .arr B, _, .merge Q => return g ``Gen.merge #[oE B, ← c Q]
  | .prod X (.arr Y), _, _, .loop (d := d) F => return g ``Gen.loop #[oE X, oE Y, bE d, ← c F]
  | _, _, _, .succ (m := m) U => return g ``Gen.succ #[uE m, ← liftE (valsE .long m U)]
  | _, _, _, .arith (m := m) k U => return g ``Gen.arith #[toExpr k, uE m, ← liftE (valsE .long m U)]
  | _, _, _, .leq (m := m) U => return g ``Gen.leq #[uE m, ← liftE (valsE .long m U)]
  | _, _, _, .lt (m := m) U => return g ``Gen.lt #[uE m, ← liftE (valsE .long m U)]
  | .arr E, V, _, .fold (d := d) e S => return g ``Gen.fold #[oE E, oE V, bE d, ← c e, ← c S]
  | _, _, _, .share _ R => c R
  | .prod I (.arr E), V, _, .foldI (d := d) (d' := d') e S =>
    return g ``Gen.foldI #[oE I, oE E, oE V, bE d, bE d', ← c e, ← c S]
  | .prod I A, B, _, .flat (d := d) R => return g ``Gen.flat #[oE I, oE A, oE B, bE d, ← c R]
  | A, B, _, .var k => match ρ.lookup k with
    | some x => return g ``Gen.const #[oE A, oE B, x]
    | none => throwError "rel_program expansion: internal: the fixed-point variable {k} is not bound here"
  | A, B, _, .nu k S b => match arcs k b with
    | some (a :: as) =>
      let arc (x : Tm A A false × Tm B B false × Tm A A false × Tm B B false) : RM Lean.Expr := do
        let (r, s, u, v) := x
        let ty (X Y : Obj) := mkApp3 (mkConst ``Gen.Fn) (bE false) (oE X) (oE Y)
        pure (mkApp4 (mkConst ``Prod.mk [0, 0]) (ty A A)
          (mkApp2 (mkConst ``Prod [0, 0]) (ty B B) (mkApp2 (mkConst ``Prod [0, 0]) (ty A A) (ty B B)))
          (← c r) (mkApp4 (mkConst ``Prod.mk [0, 0]) (ty B B) (mkApp2 (mkConst ``Prod [0, 0]) (ty A A) (ty B B))
            (← c s) (mkApp4 (mkConst ``Prod.mk [0, 0]) (ty A A) (ty B B) (← c u) (← c v))))
      let arcTy := mkApp2 (mkConst ``Gen.Arc) (oE A) (oE B)
      return g ``Gen.nuAC #[oE A, oE B, ← c S, ← arc a, ← mkListLit arcTy (← as.mapM arc)]
    | _ => return g ``Gen.nu #[oE A, oE B, ← c S, ← body pre ρ A B k b]
  | A, B, _, .mu k _ n b => return g ``Gen.mu #[oE A, oE B, toExpr n, ← body pre ρ A B k b]
  | A, B, _, .refold (d := d) (e := e) k _ ch b =>
    return g ``Gen.refold #[oE A, oE B, bE d, bE e, ← c ch, ← body pre ρ A B k b]
  | .sum A B, C, _, .juncD (d := d) (e := e) R S => return g ``Gen.juncD #[oE A, oE B, oE C, bE d, bE e, ← c R, ← c S]
  | _, _, _, .call c => return mkConst c
  | _, _, _, t@(.arg ..) => spine pre ρ t

end

/-! ### The proof that the code computes the term (`GenSpec`) -/

/-- The theorem of each shared constant (`n.c.c<i>.rep`), and the first combinator met with no lemma. -/
abbrev PM := StateT (Std.HashMap Name Name × Option Name) RM

/-- The constant `n`, which the proofs cite by name: the expander runs as native code, so it does not import the
    proof modules (`GenSpec`); the module running `rel_program` does, through `Programs.Prelude`. -/
def need (n : Name) : MetaM Name := do
  unless (← getEnv).contains n do
    throwError "rel_program expansion: `{n}` is not in scope; import `LeetQ.Rel.Lang.GenSpec`, which brings it"
  pure n

/-- The `GenSpec` lemma `Gen.s` (`need`). -/
def gs (s : Name) : MetaM Name := need (`LeetQ.Rel.Lang.Gen ++ s)

/-- The lemma `Gen.n` at the proofs `hs` of its parts, its objects inferred from them; none where a part has none. -/
def lem (n : Name) (hs : List (Option Lean.Expr)) : PM (Option Lean.Expr) := do
  let some as := hs.mapM id | return none
  some <$> mkAppM (← gs n) as.toArray

/-- A leaf lemma `Gen.n` whose objects only the term gives. -/
def lemO (n : Name) (as : Array (Option Lean.Expr)) : PM (Option Lean.Expr) := do some <$> mkAppOptM (← gs n) as

mutual

/-- A proof of `Gen.Sound (code t) T`, `T` the allegory's term; a closed `t` cites its constant's theorem. -/
partial def prf (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  if !closed t then return ← prfNode pre ρ t
  let cd ← code pre ρ t
  let c := cd.appArg!.constName!
  if let some h := (← get).1[c]? then return some (mkConst h)
  let h := c ++ `rep
  -- under its number, `t`'s node: proving `.share k R` by `R`'s own `prf` would add `h` twice
  let some p ← (match t with | .share _ R => prfNode pre ρ R | t => prfNode pre ρ t) | return none
  -- `const_sound` at `c` itself, so the kernel meets `c =?= node(t) ()` and unfolds `c`, never the data
  let T := (← inferType p).appArg!
  let some (.defnInfo ci) := (← getEnv).find? c | throwError "rel_program expansion: internal: no definition `{c}`"
  let hb := g (← gs `Sound.eq) #[oE A, oE B, ci.value.appFn!, T, p]
  let ty := g (← gs `Sound) #[bE false, oE A, oE B, cd, T]
  addDecl (.thmDecl { name := h, levelParams := [], type := ty, value := g (← gs `const_sound) #[oE A, oE B, mkConst c, T, hb] })
  modify fun (m, g) => (m.insert c h, g)
  pure (some (mkConst h))

/-- A proof of `Gen.PSound (planOr t) T`, following `planOr`. -/
partial def pprf (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  let p {X Y : Obj} {e : Bool} (u : Tm X Y e) := prf pre ρ u
  let q {X Y : Obj} {e : Bool} (u : Tm X Y e) := pprf pre ρ u
  if closed t then return ← lem `pleaf_sound [← p t]
  match A, B, d, t with
  | _, _, _, .val _ | _, _, _, .uni _ | _, _, _, .var _ => lem `pleaf_sound [← prfNode pre ρ t]
  | _, _, _, .share _ R | _, _, _, .own R => q R
  | _, _, _, .comp R S => lem `pcomp_sound [← q R, ← q S]
  | _, _, _, .conv R => lem `pconv_sound [← q R]
  | _, _, _, .meet R S => lem `pmeet_sound [← q R, ← q S]
  | _, _, _, .join R S => lem `pjoin_sound [← q R, ← q S]
  | _, _, _, .diff R S => lem `pdiff_sound [← q R, ← q S]
  | _, _, _, .ldiv R S UB UC => lem `pldiv_sound [← q R, ← q S, ← p UB, ← p UC]
  | _, _, _, _ => lem `pleaf_sound [← p t]

/-- A proof of `Gen.Sound (node t) T`, one `GenSpec` lemma per node, following `node`. -/
partial def prfNode (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  let p {X Y : Obj} {e : Bool} (u : Tm X Y e) := prf pre ρ u
  let q {X Y : Obj} {e : Bool} (u : Tm X Y e) := pprf pre ρ u
  match A, B, d, t with
  | _, _, _, .val R => lem `val_sound [some (← liftE (relE R))]
  | A, _, _, .uni (m := m) U => lemO `uni_sound #[oE A, uE m, ← liftE (valsE A m U)]
  | A, B, _, .zero => lemO `zero_sound #[oE A, oE B]
  | A, _, _, .id => lemO `id_sound #[oE A]
  | A, _, _, .top V => match ← p V with
    | some h => lemO `top_sound #[oE A, none, none, none, h]
    | none => pure none
  | _, B, _, .mem => lemO `mem_sound #[oE B]
  | .prod A B, _, _, .outl => lemO `outl_sound #[oE A, oE B]
  | .prod A B, _, _, .outr => lemO `outr_sound #[oE A, oE B]
  | A, .sum _ B, _, .inl => lemO `inl_sound #[oE A, oE B]
  | B, .sum A _, _, .inr => lemO `inr_sound #[oE A, oE B]
  | _, _, true, .comp R S => lem `comp_sound [← p R, ← p S]
  | _, _, false, .comp R S => lem `compB_sound [← q R, ← q S]
  | _, _, _, .conv R => lem `conv_sound [← p R]
  | _, _, _, .meet (d := false) (e := false) R S => lem `meetB_sound [← q R, ← q S]
  | _, _, _, .diff (d := false) (e := false) R S => lem `diffB_sound [← q R, ← q S]
  | _, _, _, .meet R S => lem `meet_sound [← p R, ← p S]
  | _, _, _, .join R S => lem `join_sound [← p R, ← p S]
  | _, _, _, .diff R S => lem `diff_sound [← p R, ← p S]
  | _, _, _, .dom R => lem `dom_sound [← p R]
  | _, _, _, .ran R => lem `ran_sound [← p R]
  | _, _, _, .ldiv R S UB UC => lem `ldivB_sound [← q R, ← q S, ← p UB, ← p UC]
  | _, _, _, .rdiv R S UA UB => lem `rdiv_sound [← p R, ← p S, ← p UA, ← p UB]
  | _, _, _, .pair R S => lem `pair_sound [← p R, ← p S]
  | _, _, _, .prod R S => lem `prod_sound [← p R, ← p S]
  | _, _, _, .junc R S => lem `junc_sound [← p R, ← p S]
  | _, _, _, .own R | _, _, _, .share _ R => p R
  | _, _, _, _ =>
    let f := (← node pre ρ t).getAppFn.constName?
    modify fun (m, g) => (m, g <|> f); pure none

end

/-- `k` under one local of each type `tys`, closed over them: `(∀ xs, ty, fun xs => v)` of `k`'s `(ty, v)`. -/
def lams (tys : List Lean.Expr) (k : Array Lean.Expr → PM (Lean.Expr × Lean.Expr)) (xs : Array Lean.Expr := #[]) :
    PM (Lean.Expr × Lean.Expr) :=
  match tys with
  | [] => do let (t, v) ← k xs; pure (← mkForallFVars xs t, ← mkLambdaFVars xs v)
  | ty :: tys => withLocalDeclD `x ty fun x => lams tys k (xs.push x)

/-- An entry of the registry (module design §2.3): a definition elaborated once, its constant (`once`); a program's
    homes, the programs its names reach, in the order they are read (`read`); a program's scope, its namespace and
    `open`s, which its names resolve in; a definition or object of the program `home`. -/
inductive RegEntry
  | call (c : Name)
  | chain (n : Name) (ns : List Name)
  | prog (n : Name) (ns : Name) (opens : List OpenDecl)
  | ext (e : Ext) (home : Name)
  deriving Inhabited

/-- The registry, written only by `rel_program`: the constants a use may call (`walk`), each program's homes,
    the programs in the order they were defined (imported ones first) with their scopes, and every definition and
    object by its constant, with its program. -/
structure Registry where
  calls : List Name := []
  chains : List (Name × List Name) := []
  progs : Array (Name × Name × List OpenDecl) := #[]
  exts : Std.HashMap Name (Ext × Name) := {}

instance : Inhabited Registry := ⟨{}⟩

def Registry.add (r : Registry) : RegEntry → Registry
  | .call c => { r with calls := c :: r.calls }
  | .chain n ns => { r with chains := (n, ns) :: r.chains }
  | .prog n ns os => { r with progs := r.progs.push (n, ns, os) }
  | .ext e h => { r with exts := r.exts.insert e.const (e, h) }

initialize relRegistry : SimplePersistentEnvExtension RegEntry Registry ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Registry.add
    addImportedFn := fun ess => ess.foldl (fun r es => es.foldl Registry.add r) {} }

def pairT (a b : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``Prod [0, 0]) a b
def listT (a : Lean.Expr) : Lean.Expr := mkApp (mkConst ``List [0]) a

/-- The objects `objs` as a print reads them (`infoOf`). -/
def objsE (objs : Objs) : MetaM Lean.Expr := do
  let ty := pairT (mkConst ``String) (mkConst ``ObjInfo)
  mkListLit ty (objs.map fun (x, i) => mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``ObjInfo)
    (toExpr x) (g ``infoOf #[toExpr i.ty, toExpr i.elems, toExpr i.range]))

/-- The Lean definitions of what the program `n` reads (`read`): `n.x` for each closed definition, its
    sub-terms' constants `n.c.c<i>`, `n.expanded` (the definitions with their objects), `n.objs`, `n.printed`
    (each `print`'s line and ok bit), `n.prints` (the lines), `n.failures` (`failures`: each `check` that does not
    hold, and an op out of capacity) and `n.ok`, that there is none. -/
def emit (n : Name) (r : Read) : MetaM Unit := do
  let (ds, ps, cs, objs, os, xs, ex) := r
  -- read before `number`, which hides a closed `μ` inside a `share`
  let ms : List (String × List String) := ds.map fun (x, ⟨_, _, _, t⟩) => (x, mus t)
  -- one numbering over the whole program, as the code of each number is kept across it
  let ((ds, ps, cs), fs) := Prod.fst <| (do
    let fs ← os.mapM fun (x, nv, qs, ⟨A, B, d, t⟩) => return (x, nv, qs, (⟨A, B, d, ← number t⟩ : Res))
    let ds ← ds.mapM fun (x, ⟨A, B, d, t⟩) => return (x, ⟨A, B, d, ← number t⟩)
    let ps ← ps.mapM fun (x, ⟨A, B, t⟩, s, u) => return (x, ⟨A, B, ← number t⟩, s, u)
    let cs ← cs.mapM fun (p, x, y, eq, s, u, ⟨A, B, R, S⟩) =>
      return (p, x, y, eq, s, u, ⟨A, B, ← number R, ← number S⟩)
    pure ((ds, ps, cs), fs) : StateM Nat ((List (String × Res) × List (String × Top) × List Chk) × List Once)).run 0
  addConst (n ++ `objs) (mkConst ``Objs) (← objsE objs)
  let os := mkConst (n ++ `objs)
  let app (t : Lean.Expr) := mkApp t (mkConst ``Unit.unit)
  let (entries, printed, checked, unproved) ← (do
    -- each definition elaborated once: `n.x : Fn U₁ → … → Fn R₁ → … → Fn A B`, the universes of its object
    -- variables then its parameters, each read as `x ()` where the body reads its variable
    for (x, nv, qs, ⟨A, B, _, t⟩) in fs do
      let fn (X Y : Obj) := mkApp3 (mkConst ``Gen.Fn) (bE false) (oE X) (oE Y)
      let tys := (List.replicate nv ((.long : Obj), (.long : Obj)) ++ qs).map fun (X, Y) => fn X Y
      let (ty, v) ← lams tys fun xs => do
        let ρ := xs.toList.zipIdx.map fun (x, k) => (k, mkApp x (mkConst ``Unit.unit))
        pure (fn A B, ← code n ρ t)
      addConst (Parse.constOf n x) ty v
      modifyEnv (relRegistry.addEntry · (.call (Parse.constOf n x)))
    let mut gaps : List (String × String) := []
    let mut es := []
    for (x, ⟨A, B, d, t⟩) in ds do
      let v ← code n [] t
      let k := Parse.constOf n x
      unless !d do throwError "rel_program expansion: internal: `{x}` needs keys"
      addConst k (mkApp2 (mkConst ``CRel) (oE A) (oE B)) (app v)
      -- `n.rep_x : (n.x).ok = true → rep (n.x).rel = ⟦x⟧`, assembled from `GenSpec`'s lemmas
      modify fun (m, _) => (m, none)
      let body : PM (Option String) := do
        match ← prf n [] t with
        | some p =>
          let kc := mkConst k
          let ty ← mkArrow (← mkEq (← mkAppM ``CRel.ok #[kc]) (toExpr true))
            (← mkEq (← mkAppM (← need `LeetQ.Rel.Rep.rep) #[← mkAppM ``CRel.rel #[kc]]) (← inferType p).appArg!)
          let pv ← mkAppM (← gs `Sound.eq) #[p]
          addDecl (.thmDecl { name := n ++ Name.mkSimple s!"rep_{x}", levelParams := [], type := ty, value := pv })
          pure none
        | none => pure (((← get).2.map toString).getD "?")
      -- a fresh heartbeat count per theorem, since the expansion has spent the command's
      if let some c ← withCurrHeartbeats body then gaps := gaps ++ [(x, c)]
      es := es ++ [g ``Gen.entry #[toExpr x, oE A, oE B, mkConst k]]
    let ps ← ps.mapM fun (x, ⟨A, B, t⟩, s, u) => do
      pure (g ``printText #[oE A, oE B, os, toExpr x, toExpr s, toExpr u, app (← code n [] t)])
    let cs ← cs.mapM fun (p, x, y, eq, s, u, ⟨A, B, R, S⟩) => do
      pure (g ``checkErr #[oE A, oE B, os, toExpr p, toExpr x, toExpr y, toExpr eq, toExpr s, toExpr u,
        app (← code n [] R), app (← code n [] S)])
    pure (es, ps, cs, gaps) : PM (List Lean.Expr × List Lean.Expr × List Lean.Expr × List (String × String))).run'
      ({}, none) |>.run' ({}, {})
  -- the definitions with no `rep_x` yet, each with the first combinator `GenSpec` has no lemma for
  let sty := pairT (mkConst ``String) (mkConst ``String)
  addConst (n ++ `unproved) (listT sty) (← mkListLit sty (unproved.map fun (x, c) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``String) (toExpr x) (toExpr c)))
  -- the parametric definitions not elaborated once, each with the reason (`walk`)
  addConst (n ++ `notOnce) (listT sty) (← mkListLit sty (xs.map fun (x, c) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``String) (toExpr x) (toExpr c)))
  -- the uses of a constant that expand its body instead (`callDef`); `n.expanded` is taken by the definitions
  addConst (n ++ `notCalled) (listT sty) (← mkListLit sty (ex.map fun (x, c) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``String) (toExpr x) (toExpr c)))
  let ety := pairT (mkConst ``String) (mkConst ``Gen.Gv)
  addConst (n ++ `expanded) (listT ety) (← mkListLit ety entries)
  let pty := pairT (mkConst ``String) (mkConst ``Bool)
  addConst (n ++ `printed) (listT pty) (← mkListLit pty printed)
  -- every term spelled with its implicit arguments: `mkAppM` unifies, and its `isDefEq` is a heartbeat check
  -- against the whole command's count, which the expansion's own work has already spent (`addConst`)
  addConst (n ++ `prints) (listT (mkConst ``String)) (mkApp4 (mkConst ``List.map [0, 0]) pty (mkConst ``String)
    (mkApp2 (mkConst ``Prod.fst [0, 0]) (mkConst ``String) (mkConst ``Bool)) (mkConst (n ++ `printed)))
  let cty := pairT (mkApp (mkConst ``Option [0]) (mkConst ``Err)) (mkConst ``Bool)
  addConst (n ++ `failures) (listT (mkConst ``Err))
    (g ``failures #[mkConst (n ++ `expanded), toExpr ms, mkConst (n ++ `printed), ← mkListLit cty checked])
  addConst (n ++ `ok) (mkConst ``Bool) (mkApp2 (mkConst ``List.isEmpty [0]) (mkConst ``Err) (mkConst (n ++ `failures)))

end Expand

end LeetQ.Rel.Lang
