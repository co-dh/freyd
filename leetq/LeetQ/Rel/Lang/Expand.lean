import Lean
import LeetQ.Rel.Lang.Gen

/-! The expander of `rel_program n`: each closed definition `x ≜ …` becomes the Lean definition `n.rel.x : CRel A B`,
    a composition of `CRel` ops (`Gen`), so its ok bit is the `&&` of the ops it runs. At elaboration time the
    program is elaborated (`elabE`, `build`) to its core term `Tm`, as a run does; the term is then read into a
    Lean `Expr` constructor by constructor. Every closed sub-term (no keys, no fixed-point variable) becomes one
    constant `n.c.<i>`, structurally equal ones the same constant, so it is computed once, as `Eval.hoist` shares
    it; a fixed point's body is a Lean `fun X => …`; a closed `≫`/`∩`/`−`/`\` runs as a bit-matrix plan. -/

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

namespace Expand

/-- The definitions of `prog`, in order, from the environment `env`: each closed one (no keys) with its core term.
    The elaboration of a run (`Eval.run`), nothing evaluated: a definition is in scope as its built term. -/
def walk (prog : Program) (env : Env) (wrap : String → Def → Def) : Except Err (Env × List (String × Res)) := do
  let mut env := env
  let mut ds : List (String × Res) := []
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
      | ps, b, ty => env := { env with defs := (n, wrap n (mkDef env n p ps b ty)) :: env.defs }
    | _ => pure ()
  pure (env, ds)

/-- The closed definitions of `prog` read after the prelude `pre`, as `Eval.runAfter` reads them; a program with
    no prelude is one (`rel_program prelude`), its definitions seen as a prelude's (`preludeDef`). -/
def defsOf (pre : Option Program) (prog : Program) : Except Err (List (String × Res)) := do
  match pre with
  | some p =>
    let (env, _) ← (walk p {} preludeDef).mapError Err.inPrelude
    pure (← walk prog env fun _ d => d).2
  | none => pure (← walk prog {} preludeDef).2

/-! ### The core term as an `Expr` -/

open Lean Meta

deriving instance ToExpr for QLean.QAtomicType
deriving instance ToExpr for LeetQ.Rel.Obj

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

/-- A term that needs no keys and reads no fixed-point variable: computed once, as `Eval.hoist` does. -/
def closed {A B : Obj} {d : Bool} (t : Tm A B d) : Bool := !d && (fv t).isEmpty

/-- `X C`, `X` the variable `k`, `C` closed: `C`. -/
def varComp (k : Nat) : {A B : Obj} → {d : Bool} → Tm A B d → Option ((D : Obj) × Tm D B false)
  | _, _, _, .comp (B := D) (e := false) (.var k') C => if k' == k && closed C then some ⟨D, C⟩ else none
  | _, _, _, .share _ R => varComp k R
  | _, _, _, _ => none

/-- The arcs of an AC-3 body `S ∩ ⋂ₖ Aₖ\(X Cₖ)` over the variable `k`, its closed conjuncts skipped (they are
    `S`); `none` for any other body (`Eval.acArcs` on the hoisted term). -/
def arcs (k : Nat) : {V D : Obj} → {d : Bool} → Tm V D d →
    Option (List (Tm V V false × Tm D D false × Tm V V false × Tm D D false))
  | _, _, _, .share _ R => arcs k R
  | _, _, _, .meet R S => return (← arcs k R) ++ (← arcs k S)
  | V, D, d, t@(.ldiv (A := V') R S UB UC) =>
    if closed t then some [] else do
    let ⟨D', C⟩ ← varComp k S
    unless closed R && closed UB && closed UC do none
    if h : V' = V ∧ D' = D then some [(h.1 ▸ R, h.2 ▸ C, UB, UC)] else none
  | _, _, _, t => if closed t then some [] else none

abbrev RM := StateT (Std.HashMap Expr Name) MetaM

def oE (A : Obj) : Expr := toExpr A
def uE (n : USize) : Expr := mkApp (mkConst ``USize.ofNat) (toExpr n.toNat)
def bE (b : Bool) : Expr := toExpr b
def g (n : Name) (as : Array Expr) : Expr := mkAppN (mkConst n) as

def longs {n : USize} (x : Arr .long n) : List Int := x.toList.map (·.toInt)

/-- A column rebuilt from its elements: longs, products, arrays; a sum or another atom only empty, as `build`
    makes them (a literal's sum side has no rows). -/
def valsE : (A : Obj) → (n : USize) → Vals A n → Except String Expr
  | .atom .long, n, x => pure (g ``Gen.arrL #[uE n, toExpr (longs x)])
  | .prod a b, n, x => do
    pure (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkApp2 (mkConst ``Vals) (oE a) (uE n))
      (mkApp2 (mkConst ``Vals) (oE b) (uE n)) (← valsE a n x.1) (← valsE b n x.2))
  | .arr b, n, ⟨m, lo, hi, p⟩ => do pure (g ``Gen.arrV #[oE b, uE n, uE m, toExpr (longs lo), toExpr (longs hi), ← valsE b m p])
  | A, n, _ => if n == 0 then pure (g ``Gen.emptyV #[oE A])
    else throw s!"a column of {n} rows at {repr A} cannot be rebuilt: only longs, products and arrays are"

def relE {A B : Obj} (R : Rel A B) : Except String Expr := do
  pure (g ``Rel.mk #[oE A, oE B, uE R.n, ← valsE A R.n R.key, ← valsE B R.n R.val])

def liftE {α : Type} (x : Except String α) : RM α := match x with
  | .ok a => pure a
  | .error e => throwError "rel_program expansion: {e}"

mutual

/-- `t`'s code, `Gen.Fn d A B`: a closed `t` is its constant (`share`), any other its node. -/
partial def code (pre : Name) (ρ : List (Nat × Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM Expr := do
  if closed t then
    let c ← share pre A B (mkApp (← node pre ρ t) (mkConst ``Unit.unit))
    pure (g ``Gen.const #[oE A, oE B, mkConst c])
  else node pre ρ t

/-- The constant of the closed value `v : CRel A B`: one per structurally equal value. -/
partial def share (pre : Name) (A B : Obj) (v : Expr) : RM Name := do
  if let some c := (← get)[v]? then return c
  let c := pre ++ `c ++ Name.mkSimple s!"c{(← get).size}"
  addAndCompile <| .defnDecl { name := c, levelParams := [], type := mkApp2 (mkConst ``CRel) (oE A) (oE B),
    value := v, hints := .opaque, safety := .safe }
  modify (·.insert v c); pure c

/-- The plan of `t` (`Gen.Pl d A B`) where its node has a bit rule, as `Eval.evB` keeps it. -/
partial def plan? (pre : Name) (ρ : List (Nat × Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM (Option Expr) := do
  if closed t then return some (g ``Gen.pleaf #[oE A, oE B, bE d, ← code pre ρ t])
  match A, B, d, t with
  | A, B, d, .val _ | A, B, d, .uni _ | A, B, d, .var _ => return some (g ``Gen.pleaf #[oE A, oE B, bE d, ← node pre ρ t])
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

/-- The plan of `t`, or its table as a leaf (`Bits.orLeaf`). -/
partial def planOr (pre : Name) (ρ : List (Nat × Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM Expr := do
  match ← plan? pre ρ t with
  | some p => pure p
  | none => pure (g ``Gen.pleaf #[oE A, oE B, bE d, ← code pre ρ t])

/-- `φ`'s body as `fun X : CRel A B => …`, the variable `k` read as `X`. -/
partial def body (pre : Name) (ρ : List (Nat × Expr)) (A B : Obj) (k : Nat) (b : Tm A B false) : RM Expr :=
  withLocalDeclD `X (mkApp2 (mkConst ``CRel) (oE A) (oE B)) fun x => do
    mkLambdaFVars #[x] (← code pre ((k, x) :: ρ) b)

/-- `t`'s own node, its parts by `code` (or `planOr` where `Eval.ev` runs them as bit matrices). -/
partial def node (pre : Name) (ρ : List (Nat × Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) : RM Expr := do
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
      let arc (x : Tm A A false × Tm B B false × Tm A A false × Tm B B false) : RM Expr := do
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

/-- The Lean definitions of the closed definitions `ds` of the program `n`: `n.rel.x` for each, its sub-terms'
    constants `n.c.c<i>`, and `n.expanded`, the list of them with their objects. -/
def emit (n : Name) (ds : List (String × Res)) : MetaM Unit := do
  let entries ← (ds.mapM fun (x, ⟨A, B, d, t⟩) => do
    let v ← code n [] t
    let ty := mkApp2 (mkConst ``CRel) (oE A) (oE B)
    let k := n ++ `rel ++ Name.mkSimple x
    unless !d do throwError "rel_program expansion: internal: `{x}` needs keys"
    let val := mkApp v (mkConst ``Unit.unit)
    addAndCompile <| .defnDecl { name := k, levelParams := [], type := ty, value := val, hints := .opaque,
      safety := .safe }
    pure (g ``Gen.entry #[toExpr x, oE A, oE B, mkConst k]) : RM (List Expr)).run' {}
  let ety := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Gen.Gv)
  addAndCompile <| .defnDecl { name := n ++ `expanded, levelParams := [], type := mkApp (mkConst ``List [0]) ety,
    value := ← mkListLit ety entries, hints := .opaque, safety := .safe }

end Expand

end LeetQ.Rel.Lang
