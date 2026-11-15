import Lean
import LeetQ.Rel.Lang.GenSpec

/-! The expander of `rel_program n`: each closed definition `x ≜ …` becomes the Lean definition `n.rel.x : CRel A B`,
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

/-- A prelude definition as a program sees it: an error raised in its body at a use names the definition and its
    line in the prelude, at the use; one about the arguments (at the use) passes as it is. `perm` is its own
    converse, the one converse rule kept for a definition (`Tm.own`): `perm° = perm` is a theorem the
    language cannot derive from the fold `perm` is. -/
def preludeDef (n : String) (d : Def) : Def :=
  { d with apply := fun p as => do
      let r ← tryCatch (d.apply p as) fun e =>
        throw (if e.pos == p then e else ⟨p, s!"in the prelude's `{n}` (its line {e.pos.line}): {e.msg}"⟩)
      -- the body's positions are the prelude's: at the use, so what `build` raises later is at the use
      match n, r with
      | "perm", .rel q s t => pure (.rel (.own (q.at p)) s t)
      | _, .rel q s t => pure (.rel (q.at p) s t)
      | _, .fam q i a b => pure (.fam (q.at p) i a b) }

/-! ### Printing a relation with the program's names -/

/-- An array of the printed elements `xs`, as a literal's side reads it (§c): two or more juxtaposed, else
    bracketed; `item`: it stands next to others (in an array, after `inl`), so it is always bracketed. -/
def arrText (item : Bool) (xs : List String) : String :=
  let s := " ".intercalate xs; if item || xs.length < 2 then s!"[{s}]" else s

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
    prints or checks (an ok bit false), which no value of the program can be trusted after. -/
def failures (ds : List (String × Gen.Gv)) (ps : List (String × Bool)) (cs : List (Option Err × Bool)) : List Err :=
  cs.filterMap (·.1) ++ if ds.all (·.2.2.2.ok) && ps.all (·.2) && cs.all (·.2) then [] else
    [⟨{}, "an op ran out of capacity (its twin's ok bit is false)"⟩]

namespace Expand

/-- A top-level term, a `print`'s or a `check` side's: closed, with its objects as the program names them. -/
abbrev Top := ((A : Obj) × (B : Obj) × Tm A B false) × OTy × OTy

/-- A `check`: where, both sides' texts, `=` (else `⊑`), the objects as named, both sides at one type. -/
abbrev Chk := Pos × String × String × Bool × OTy × OTy × ((A : Obj) × (B : Obj) × Tm A B false × Tm A B false)

/-- What a program reads: its closed definitions, its prints (text and term), its checks, its objects. -/
abbrev Read := List (String × Res) × List (String × Top) × List Chk × Objs

/-- A top-level term, `r` its elaboration `e` with the objects `st`: closed on its source's universe when it needs
    keys, refused where that object has none. -/
def top (env : Env) (st : St) (p : Pos) (e : Expr) (r : Arg) : Except Err Top := do
  let (q, s, t) := r.plain
  let ⟨A, B, d, tm⟩ ← build env.objs st p (.close p q s noLeft)
  match d, tm with
  | false, tm => pure (⟨A, B, tm⟩, zonk st s, zonk st t)
  | true, _ => throw ⟨p, s!"{e.show}: {zonk st s} has no universe; compose a set of its elements before it (§a)"⟩

/-- The declarations of `prog`, in order, from the environment `env`: each closed definition (no keys) with its
    core term, each `print` and `check` with its terms; nothing evaluated: a definition is in scope as its built
    term. -/
def walk (prog : Program) (env : Env) (wrap : String → Def → Def) :
    Except Err (Env × List (String × Res) × List (String × Top) × List Chk) := do
  let mut env := env
  let mut ds : List (String × Res) := []
  let mut pr : List (String × Top) := []
  let mut cs : List Chk := []
  for d in prog do
    match d with
    | .obj _ n od => env := { env with objs := (n, ← objInfo env n od) :: env.objs }
    | .defn p n ps b ty =>
      let missing := ps.any (·.ty.isNone) || match b with | .rel _ => ty.isNone | .test .. => false
      if missing then throw ⟨p, s!"`{n}` has no type; it is {← (inferSig env n ps b).run' {}}"⟩
      match ps, b, ty with
      | [], .rel e, ty =>
        let rigid := match ty with | some (a, b) => (a.vars ++ b.vars).map fun v => (v, OTy.base v) | none => []
        let (r, st) ← (do
          let r ← elabE env none e
          if let some ty := ty then let (_, s, t) := r.plain; declared env p n rigid ty s t
          settleNil p r.plain.1
          pure r).run {}
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
      | qs, b, ty => env := { env with defs := (n, wrap n (mkDef env n p qs b ty)) :: env.defs }
    | .print p e =>
      let (r, st) ← (do let r ← elabE env none e; settleNil p r.plain.1; pure r).run {}
      pr := pr ++ [(e.show, ← top env st p e r)]
    | .check p e f eq =>
      -- the two sides elaborated together, one type: an object one side leaves open is the other's (§c)
      let ((r, r'), st) ← (do
        let r ← elabE env none e; let r' ← elabE env none f
        let (_, s, t) := r.plain; let (_, s', t') := r'.plain
        let st ← get
        try unify p "" s' s; unify p "" t' t
        catch _ => throw ⟨p, s!"check: the sides have types {zonk st s} ⟶ {zonk st t} and {zonk st s'} ⟶ {zonk st t'}"⟩
        settleNil p r.plain.1; settleNil p r'.plain.1
        pure (r, r') : M (Arg × Arg)).run {}
      let (⟨A, B, R⟩, s, t) ← top env st p e r
      let (⟨A', B', S⟩, s', t') ← top env st p f r'
      if h : A' = A ∧ B' = B then cs := cs ++ [(p, e.show, f.show, eq, s, t, ⟨A, B, R, h.1 ▸ h.2 ▸ S⟩)]
      else throw ⟨p, s!"check: the sides have types {s} ⟶ {t} and {s'} ⟶ {t'}"⟩
  pure (env, ds, pr, cs)

/-- What `prog` declares, read after the prelude `pre` and the programs `mid` (whose own prints and checks are not
    `prog`'s); a program with no prelude is one (`rel_program prelude`), its definitions seen as a prelude's
    (`preludeDef`). -/
def read (pre : Option Program) (mid prog : Program) : Except Err Read := do
  let keep : String → Def → Def := fun _ d => d
  let mut env : Env := {}
  let mut wrap := preludeDef
  if let some p := pre then
    env := (← (walk p {} preludeDef).mapError Err.inPrelude).1
    wrap := keep
  env := (← walk mid env keep).1
  let (e, ds, ps, cs) ← walk prog env wrap
  pure (ds, ps, cs, e.objs)

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
  | _, _, _, .pair R S | _, _, _, .prod R S | _, _, _, .junc R S => fv R ++ fv S
  | _, _, _, .conv R | _, _, _, .dom R | _, _, _, .ran R | _, _, _, .lam R | _, _, _, .E R | _, _, _, .map R => fv R
  | _, _, _, .est R | _, _, _, .thin R | _, _, _, .own R | _, _, _, .thinL R | _, _, _, .merge R => fv R
  | _, _, _, .loop R | _, _, _, .share _ R | _, _, _, .flat R => fv R
  | _, _, _, .ldiv R S U V | _, _, _, .rdiv R S U V => fv R ++ fv S ++ fv U ++ fv V
  | _, _, _, .fold e S | _, _, _, .foldI e S => fv e ++ fv S
  | _, _, _, .var k => [k]
  | _, _, _, .nu k S b => fv S ++ (fv b).filter (· != k)
  | _, _, _, .mu k U V b => fv U ++ fv V ++ (fv b).filter (· != k)
  | _, _, _, _ => []

/-- A term that needs no keys and reads no fixed-point variable: computed once, its own constant (`share`). -/
def closed {A B : Obj} {d : Bool} (t : Tm A B d) : Bool := !d && (fv t).isEmpty

/-- `X C`, `X` the variable `k`, `C` closed: `C`. -/
def varComp (k : Nat) : {A B : Obj} → {d : Bool} → Tm A B d → Option ((D : Obj) × Tm D B false)
  | _, _, _, .comp (B := D) (e := false) (.var k') C => if k' == k && closed C then some ⟨D, C⟩ else none
  | _, _, _, .share _ R => varComp k R
  | _, _, _, _ => none

/-- The arcs of an AC-3 body `S ∩ ⋂ₖ Aₖ\(X Cₖ)` over the variable `k`, its closed conjuncts skipped (they are
    `S`); `none` for any other body. -/
def arcs (k : Nat) : {V D : Obj} → {d : Bool} → Tm V D d →
    Option (List (Tm V V false × Tm D D false × Tm V V false × Tm D D false))
  | _, _, _, .share _ R => arcs k R
  | _, _, _, .meet R S => return (← arcs k R) ++ (← arcs k S)
  | V, D, _, .ldiv (A := V') R S UB UC =>
    if closed R && closed S && closed UB && closed UC then some [] else do
    let ⟨D', C⟩ ← varComp k S
    unless closed R && closed UB && closed UC do none
    if h : V' = V ∧ D' = D then some [(h.1 ▸ R, h.2 ▸ C, UB, UC)] else none
  | _, _, _, t => if closed t then some [] else none

abbrev RM := StateT (Std.HashMap Lean.Expr Name) MetaM

/-- The constant `c : ty := v`, compiled, with the heartbeats a `def` command of its own would have: one
    `rel_program` command adds them all, and a program's count of constants is no measure of any one's cost. -/
def addConst (c : Name) (ty v : Lean.Expr) : MetaM Unit := withCurrHeartbeats <|
  addAndCompile (.defnDecl { name := c, levelParams := [], type := ty, value := v, hints := .opaque, safety := .safe })

def oE (A : Obj) : Lean.Expr := toExpr A
def uE (n : USize) : Lean.Expr := mkApp (mkConst ``USize.ofNat) (toExpr n.toNat)
def bE (b : Bool) : Lean.Expr := toExpr b
def g (n : Name) (as : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) as

/-- The bytes `b` as hex text, two lowercase digits a byte (`Gen.unhex` reads it back). -/
def hex (b : ByteArray) : String :=
  let d (x : UInt8) : Char := if x < 10 then Char.ofNat (48 + x.toNat) else Char.ofNat (87 + x.toNat)
  b.foldl (fun s x => (s.push (d (x / 16))).push (d (x % 16))) ""

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

/-- `t`'s code, `Gen.Fn d A B`: a closed `t` is its constant (`share`), any other its node. -/
partial def code (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM Lean.Expr := do
  if closed t then
    let c ← share pre A B (mkApp (← node pre ρ t) (mkConst ``Unit.unit))
    pure (g ``Gen.const #[oE A, oE B, mkConst c])
  else node pre ρ t

/-- The constant of the closed value `v : CRel A B`: one per structurally equal value. -/
partial def share (pre : Name) (A B : Obj) (v : Lean.Expr) : RM Name := do
  if let some c := (← get)[v]? then return c
  let i := (← get).size
  let c := pre ++ `c ++ Name.mkSimple s!"c{i}"
  addConst c (mkApp2 (mkConst ``CRel) (oE A) (oE B)) v
  modify (·.insert v c); pure c

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

/-- `φ`'s body as `fun X : CRel A B => …`, the variable `k` read as `X`. -/
partial def body (pre : Name) (ρ : List (Nat × Lean.Expr)) (A B : Obj) (k : Nat) (b : Tm A B false) : RM Lean.Expr :=
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
  | A, .arr B, d, .lam R => return g ``Gen.lam #[oE A, oE B, bE d, ← c R]
  | .arr A, .arr B, _, .E (d := d) R => return g ``Gen.E #[oE A, oE B, bE d, ← c R]
  | .arr A, .arr B, _, .map (d := d) R => return g ``Gen.map #[oE A, oE B, bE d, ← c R]
  | _, B, _, .est Q => return g ``Gen.est #[oE B, ← c Q]
  | _, .arr B, _, .thin Q => return g ``Gen.thin #[oE B, ← c Q]
  | _, .arr A, _, .union => return g ``Gen.union #[oE A]
  | A, _, _, .tau => return g ``Gen.tau #[oE A]
  | A, .arr B, _, .nil => return g ``Gen.nil #[oE A, oE B]
  | _, .arr B, _, .cons => return g ``Gen.cons #[oE B]
  | .arr B, _, _, .uncons => return g ``Gen.uncons #[oE B]
  | .arr B, _, _, .length => return g ``Gen.length #[oE B]
  | _, _, _, .total => return mkConst ``Gen.total
  | .arr B, _, _, .inits => return g ``Gen.inits #[oE B]
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
  | A, B, _, .mu k UA UB b => return g ``Gen.mu #[oE A, oE B, ← c UA, ← c UB, ← body pre ρ A B k b]

end

/-! ### The proof that the code computes the term (`GenSpec`) -/

/-- The theorem of each shared constant (`n.c.c<i>.rep`), and the first combinator met with no lemma. -/
abbrev PM := StateT (Std.HashMap Name Name × Option Name) RM

/-- The lemma `n` at the proofs `hs` of its parts, its objects inferred from them; none where a part has none. -/
def lem (n : Name) (hs : List (Option Lean.Expr)) : PM (Option Lean.Expr) := do
  let some as := hs.mapM id | return none
  some <$> mkAppM n as.toArray

/-- A leaf lemma whose objects only the term gives. -/
def lemO (n : Name) (as : Array (Option Lean.Expr)) : PM (Option Lean.Expr) := some <$> mkAppOptM n as

mutual

/-- A proof of `Gen.Sound (code t) T`, `T` the allegory's term; a closed `t` cites its constant's theorem. -/
partial def prf (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  if !closed t then return ← prfNode pre ρ t
  let cd ← code pre ρ t
  let c := cd.appArg!.constName!
  if let some h := (← get).1[c]? then return some (mkConst h)
  let h := c ++ `rep
  -- the cache is rolled back when a definition's proof runs out of heartbeats, the environment is not
  if (← getEnv).contains h then return some (mkConst h)
  let some p ← prfNode pre ρ t | return none
  let ty ← mkAppM ``Gen.Sound #[cd, (← inferType p).appArg!]
  addDecl (.thmDecl { name := h, levelParams := [], type := ty, value := p })
  modify fun (m, g) => (m.insert c h, g)
  pure (some (mkConst h))

/-- A proof of `Gen.PSound (planOr t) T`, following `planOr`. -/
partial def pprf (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  let p {X Y : Obj} {e : Bool} (u : Tm X Y e) := prf pre ρ u
  let q {X Y : Obj} {e : Bool} (u : Tm X Y e) := pprf pre ρ u
  if closed t then return ← lem ``Gen.pleaf_sound [← p t]
  match A, B, d, t with
  | _, _, _, .val _ | _, _, _, .uni _ | _, _, _, .var _ => lem ``Gen.pleaf_sound [← prfNode pre ρ t]
  | _, _, _, .share _ R | _, _, _, .own R => q R
  | _, _, _, .comp R S => lem ``Gen.pcomp_sound [← q R, ← q S]
  | _, _, _, .conv R => lem ``Gen.pconv_sound [← q R]
  | _, _, _, .meet R S => lem ``Gen.pmeet_sound [← q R, ← q S]
  | _, _, _, .join R S => lem ``Gen.pjoin_sound [← q R, ← q S]
  | _, _, _, .diff R S => lem ``Gen.pdiff_sound [← q R, ← q S]
  | _, _, _, .ldiv R S UB UC => lem ``Gen.pldiv_sound [← q R, ← q S, ← p UB, ← p UC]
  | _, _, _, _ => lem ``Gen.pleaf_sound [← p t]

/-- A proof of `Gen.Sound (node t) T`, one `GenSpec` lemma per node, following `node`. -/
partial def prfNode (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  let p {X Y : Obj} {e : Bool} (u : Tm X Y e) := prf pre ρ u
  let q {X Y : Obj} {e : Bool} (u : Tm X Y e) := pprf pre ρ u
  match A, B, d, t with
  | _, _, _, .val R => lem ``Gen.val_sound [some (← liftE (relE R))]
  | A, _, _, .uni (m := m) U => lemO ``Gen.uni_sound #[oE A, uE m, ← liftE (valsE A m U)]
  | A, B, _, .zero => lemO ``Gen.zero_sound #[oE A, oE B]
  | A, _, _, .id => lemO ``Gen.id_sound #[oE A]
  | A, _, _, .top V => match ← p V with
    | some h => lemO ``Gen.top_sound #[oE A, none, none, none, h]
    | none => pure none
  | _, B, _, .mem => lemO ``Gen.mem_sound #[oE B]
  | .prod A B, _, _, .outl => lemO ``Gen.outl_sound #[oE A, oE B]
  | .prod A B, _, _, .outr => lemO ``Gen.outr_sound #[oE A, oE B]
  | A, .sum _ B, _, .inl => lemO ``Gen.inl_sound #[oE A, oE B]
  | B, .sum A _, _, .inr => lemO ``Gen.inr_sound #[oE A, oE B]
  | _, _, true, .comp R S => lem ``Gen.comp_sound [← p R, ← p S]
  | _, _, false, .comp R S => lem ``Gen.compB_sound [← q R, ← q S]
  | _, _, _, .conv R => lem ``Gen.conv_sound [← p R]
  | _, _, _, .meet (d := false) (e := false) R S => lem ``Gen.meetB_sound [← q R, ← q S]
  | _, _, _, .diff (d := false) (e := false) R S => lem ``Gen.diffB_sound [← q R, ← q S]
  | _, _, _, .meet R S => lem ``Gen.meet_sound [← p R, ← p S]
  | _, _, _, .join R S => lem ``Gen.join_sound [← p R, ← p S]
  | _, _, _, .diff R S => lem ``Gen.diff_sound [← p R, ← p S]
  | _, _, _, .dom R => lem ``Gen.dom_sound [← p R]
  | _, _, _, .ran R => lem ``Gen.ran_sound [← p R]
  | _, _, _, .ldiv R S UB UC => lem ``Gen.ldivB_sound [← q R, ← q S, ← p UB, ← p UC]
  | _, _, _, .rdiv R S UA UB => lem ``Gen.rdiv_sound [← p R, ← p S, ← p UA, ← p UB]
  | _, _, _, .pair R S => lem ``Gen.pair_sound [← p R, ← p S]
  | _, _, _, .prod R S => lem ``Gen.prod_sound [← p R, ← p S]
  | _, _, _, .junc R S => lem ``Gen.junc_sound [← p R, ← p S]
  | _, _, _, .own R | _, _, _, .share _ R => p R
  | _, _, _, _ =>
    let f := (← node pre ρ t).getAppFn.constName?
    modify fun (m, g) => (m, g <|> f); pure none

end

def pairT (a b : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``Prod [0, 0]) a b
def listT (a : Lean.Expr) : Lean.Expr := mkApp (mkConst ``List [0]) a

/-- The objects `objs` as a print reads them (`infoOf`). -/
def objsE (objs : Objs) : MetaM Lean.Expr := do
  let ty := pairT (mkConst ``String) (mkConst ``ObjInfo)
  mkListLit ty (objs.map fun (x, i) => mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``ObjInfo)
    (toExpr x) (g ``infoOf #[toExpr i.ty, toExpr i.elems, toExpr i.range]))

/-- The Lean definitions of what the program `n` reads (`read`): `n.rel.x` for each closed definition, its
    sub-terms' constants `n.c.c<i>`, `n.expanded` (the definitions with their objects), `n.objs`, `n.printed`
    (each `print`'s line and ok bit), `n.prints` (the lines), `n.failures` (`failures`: each `check` that does not
    hold, and an op out of capacity) and `n.ok`, that there is none. -/
def emit (n : Name) (r : Read) : MetaM Unit := do
  let (ds, ps, cs, objs) := r
  addConst (n ++ `objs) (mkConst ``Objs) (← objsE objs)
  let os := mkConst (n ++ `objs)
  let app (t : Lean.Expr) := mkApp t (mkConst ``Unit.unit)
  let (entries, printed, checked, unproved) ← (do
    let mut gaps : List (String × String) := []
    let mut es := []
    for (x, ⟨A, B, d, t⟩) in ds do
      let v ← code n [] t
      let k := n ++ `rel ++ Name.mkSimple x
      unless !d do throwError "rel_program expansion: internal: `{x}` needs keys"
      addConst k (mkApp2 (mkConst ``CRel) (oE A) (oE B)) (app v)
      -- `n.rep_x : (n.rel.x).ok = true → rep (n.rel.x).rel = ⟦x⟧`, assembled from `GenSpec`'s lemmas
      modify fun (m, _) => (m, none)
      let body : PM (Option String) := do
        match ← prf n [] t with
        | some p =>
          let kc := mkConst k
          let ty ← mkArrow (← mkEq (← mkAppM ``CRel.ok #[kc]) (toExpr true))
            (← mkEq (← mkAppM ``Rep.rep #[← mkAppM ``CRel.rel #[kc]]) (← inferType p).appArg!)
          let pv ← mkAppM ``Gen.Sound.eq #[p]
          addDecl (.thmDecl { name := n ++ Name.mkSimple s!"rep_{x}", levelParams := [], type := ty, value := pv })
          pure none
        | none => pure (((← get).2.map toString).getD "?")
      -- a fresh heartbeat count per theorem, since the expansion has spent the command's; a proof that still runs
      -- past it is a gap named by its message, while every other error propagates
      let s ← get; let r ← getThe (Std.HashMap Lean.Expr Name)
      match ← (tryCatchRuntimeEx (Except.ok <$> withCurrHeartbeats ((body.run s).run r))
          fun e => if e.isRuntime then pure (.error e) else throw e : MetaM _) with
      | .ok ((gp, s'), r') =>
        set s'; modifyThe (Std.HashMap Lean.Expr Name) fun _ => r'
        if let some c := gp then gaps := gaps ++ [(x, c)]
      | .error e => gaps := gaps ++ [(x, s!"runtime: {(← e.toMessageData.toString).takeWhile (· != '\n')}")]
      es := es ++ [g ``Gen.entry #[toExpr x, oE A, oE B, mkConst k]]
    let ps ← ps.mapM fun (x, ⟨A, B, t⟩, s, u) => do
      pure (g ``printText #[oE A, oE B, os, toExpr x, toExpr s, toExpr u, app (← code n [] t)])
    let cs ← cs.mapM fun (p, x, y, eq, s, u, ⟨A, B, R, S⟩) => do
      pure (g ``checkErr #[oE A, oE B, os, toExpr p, toExpr x, toExpr y, toExpr eq, toExpr s, toExpr u,
        app (← code n [] R), app (← code n [] S)])
    pure (es, ps, cs, gaps) : PM (List Lean.Expr × List Lean.Expr × List Lean.Expr × List (String × String))).run'
      ({}, none) |>.run' {}
  -- the definitions with no `rep_x` yet, each with the first combinator `GenSpec` has no lemma for
  let sty := pairT (mkConst ``String) (mkConst ``String)
  addConst (n ++ `unproved) (listT sty) (← mkListLit sty (unproved.map fun (x, c) =>
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
    (g ``failures #[mkConst (n ++ `expanded), mkConst (n ++ `printed), ← mkListLit cty checked])
  addConst (n ++ `ok) (mkConst ``Bool) (mkApp2 (mkConst ``List.isEmpty [0]) (mkConst ``Err) (mkConst (n ++ `failures)))

end Expand

end LeetQ.Rel.Lang
