import LeetQ.Run.Algebra
import LeetQ.Run.Lang.Syntax
import LeetQ.Run.Lang.Tm

/-! The elaborator of the Rel language (`doc/rel-lang-design.md` §a, §e): names resolved, every term typed
    `A ⟶ B` over the declared objects, definitions expanded, a body whose declared parameter is given a family
    lifted by the rows of §e. Two passes: `elabE` types the surface term into `Pre` with object variables,
    unified as it goes; `build` reads the solved objects and gives `Tm`, the core term, indexed by its source,
    target and whether it runs on demand, so its expansion (`Expand`) has no error path. -/

namespace LeetQ.Rel.Lang

open LeetQ.Rel LeetQ.Rel.Alg
open QLean.Kernel (need needSize)

/-! ### Objects as the program names them -/

/-- The declared object `n` as Lean's unifier sees it: one constant per name, so `isDefEq` tells `X` from `N` though
    both are stored as `.long` (F6); irreducible, so the unifier never reads a name as its storage. -/
@[irreducible] def _root_.LeetQ.Rel.Obj.named (_ : String) : Obj := .long

/-- An object up to its declared names: `X` and `N` are both `long` and still different objects. `𝒫A` and
    `[A]` are both `arr`. `mv` is an object variable of the inference, a Lean metavariable of type `Obj`. -/
inductive OTy
  | base (n : String)
  | prod (a b : OTy)
  | sum (a b : OTy)
  | arr (a : OTy)
  | mv (m : Lean.MVarId)
  deriving BEq, Inhabited

/-- `o` as an `Obj` term: a declared object its constant `Obj.named`, a variable its metavariable. -/
def OTy.toExpr : OTy → Lean.Expr
  | .base n => .app (.const ``Obj.named []) (Lean.mkStrLit n)
  | .prod a b => Lean.mkApp2 (.const ``Obj.prod []) a.toExpr b.toExpr
  | .sum a b => Lean.mkApp2 (.const ``Obj.sum []) a.toExpr b.toExpr
  | .arr a => .app (.const ``Obj.arr []) a.toExpr
  | .mv m => .mvar m

/-- An `Obj` term read back: the unifier only assigns `toExpr`'s forms to the variables, so no other form occurs;
    one would print as itself. -/
def OTy.ofExpr : Lean.Expr → OTy
  | .app (.const ``Obj.named _) (.lit (.strVal n)) => .base n
  | .app (.app (.const ``Obj.prod _) a) b => .prod (ofExpr a) (ofExpr b)
  | .app (.app (.const ``Obj.sum _) a) b => .sum (ofExpr a) (ofExpr b)
  | .app (.const ``Obj.arr _) a => .arr (ofExpr a)
  | .mvar m => .mv m
  | e => .base s!"{e}"

def OTy.exp : OTy → OExp
  | .base n => .name {} n
  | .prod a b => .prod a.exp b.exp
  | .sum a b => .sum a.exp b.exp
  -- `𝒫A` and `[A]` are one object, an array; printed as the array the interpreter holds
  | .arr a => .list a.exp
  | .mv m => .var {} (match m.name with | .num _ k => s!"?{k}" | n => s!"?{n}")

instance : ToString OTy := ⟨(·.exp.show)⟩

/-- A declared object: what it stands for, and, for a base object, its elements and universe. -/
structure ObjInfo where
  ty : OTy
  elems : List String := []
  range : Option (Int × Int) := none
  uni : Option ((m : USize) × Arr .long m) := none
  /-- An object variable of a definition elaborated once: its universe is the variable `k`, an argument of the
      definition's constant. -/
  uniVar : Option Nat := none
  /-- How it is stored: `.long` for a declared object (F6); `varObj k` for the object variable `k` of a constant
      generic over it. -/
  obj : Obj := .long

/-- The atoms no declared object is stored as (every one is `.long`, F6): each the placeholder of one object
    variable while a constant generic over it is built, its binder `(A : Obj)` once emitted. -/
def varAtoms : List QLean.QAtomicType := [.general, .boolean, .guid, .byte, .short, .int, .real, .float, .char, .symbol,
  .timestamp, .month, .date, .datetime, .timespan, .minute, .second, .time]

/-- The placeholder of the object variable `k`; none past `varAtoms`, where the variable stays `.long`. -/
def varObj (k : Nat) : Option Obj := varAtoms[k]?.map .atom

abbrev Objs := List (String × ObjInfo)

/-- The universe of an object, when every base object in it has one (§a): `cross` of a product's, the two
    sides of a sum's; an `arr` has none. -/
def uniOf (objs : Objs) : OTy → Option ((A : Obj) × (m : USize) × Vals A m)
  | .base n => do let ⟨m, U⟩ ← (← objs.lookup n).uni; pure ⟨.long, m, U⟩
  | .prod a b => do
    let ⟨_, _, Ua⟩ ← uniOf objs a; let ⟨_, _, Ub⟩ ← uniOf objs b
    let k := (Alg.prod (idU Ua) (idU Ub)).key
    pure ⟨_, _, k⟩
  | .sum a b => do
    let ⟨_, n, Ua⟩ ← uniOf objs a; let ⟨_, m, Ub⟩ ← uniOf objs b
    need (n.toNat + m.toNat < USize.size) (fun _ => s!"the universe of {a} + {b}: {n} + {m} do not fit a USize")
      (fun _ => none) fun hN => pure ⟨_, _, sumVals Ua Ub hN⟩
  | _ => none

/-- The rounds a `μ` runs at most when an object of it has no universe: Kleene rounds from `𝟘` stop at the least
    fixed point whatever the object, but an array object may grow every round; a run that reaches the cap fails. -/
def muCap : Nat := 1024

/-- The element count of `uniOf objs o`, read off the declared universes without building the product's. -/
def uniSize (objs : Objs) : OTy → Option Nat
  | .base n => do let ⟨m, _⟩ ← (← objs.lookup n).uni; pure m.toNat
  | .prod a b => do pure ((← uniSize objs a) * (← uniSize objs b))
  | .sum a b => do pure ((← uniSize objs a) + (← uniSize objs b))
  | _ => none

/-! ### The typed surface term -/

/-- A term typed but not yet built: the core operators, object variables on the constants. `close` marks a
    place whose term is read whole — no left context, or an operator that is not local (§a): its term runs on
    its source's universe when it needs keys, `why` naming that operator in the error when there is none.
    `tm` is a built term, a definition's. -/
inductive Pre
  | tm (r : Res)
  | zero (a b : OTy)
  | id (a : OTy)
  | top (p : Pos) (a b : OTy) (tgt : Option Pre)
  | mem (b : OTy)
  | outl (a b : OTy)
  | outr (a b : OTy)
  | inl (a b : OTy)
  | inr (a b : OTy)
  | comp (p q : Pre)
  | conv (p : Pre)
  | meet (p q : Pre)
  | join (p q : Pre)
  | diff (p q : Pre)
  | dom (p : Pre)
  | ran (p : Pre)
  | ldiv (pos : Pos) (p q : Pre) (b c : OTy)
  | rdiv (pos : Pos) (p q : Pre) (a b : OTy)
  | pair (p q : Pre)
  | prod (p q : Pre)
  | junc (p q : Pre)
  | lam (p : Pre)
  | E (p : Pre)
  | map (p : Pre)
  | filter (p : Pre)
  | takewhile (p : Pre)
  | est (p : Pre)
  | thin (p : Pre)
  | nil (a b : OTy)
  /-- The row `r` of `prims` at `s ⟶ t`, an instance of its type. -/
  | prim (r : Prim) (s t : OTy)
  | atPos (k : Nat) (b : OTy)
  | own (p : Pre)
  | thinL (p : Pre)
  | merge (p : Pre)
  | loop (p : Pre)
  | succ (pos : Pos) (n : OTy)
  | arith (pos : Pos) (k : UInt8) (n : OTy)
  | leq (pos : Pos) (n : OTy)
  | lt (pos : Pos) (n : OTy)
  | fold (e s : Pre)
  | foldI (e s : Pre)
  | flat (p : Pre)
  | lit (pos : Pos) (a b : OTy) (ps : List (Tup × Tup))
  | close (pos : Pos) (p : Pre) (a : OTy) (why : String)
  /-- The variable `k` of a fixed point `X : a ⟶ b`, at the place `pos` it is used; or a constant's parameter,
      its argument's form (`Form`): closed (`none`), run on demand (`some false`), tested on pairs and never run
      (`some true`). -/
  | var (pos : Pos) (k : Nat) (a b : OTy) (tst : Option Bool)
  /-- `μX : body` (`least`) or `νX : body`, `X` the variable `k`; `S` the meet of `body`'s conjuncts that do not
      mention `X`, a `ν`'s start. -/
  | fix (pos : Pos) (least : Bool) (k : Nat) (S : Option Pre) (body : Pre) (a b : OTy)
  /-- `refold(c, S)`, `c` at `pos`, where a cycle of `c` is reported: `body` the `μX : c G(X) S` it is, `X` the variable `k`; `ch : a ⟶ a` the children
      `c` gives a node, `c` then `G`'s membership. -/
  | refold (pos : Pos) (k : Nat) (ch body : Pre) (a b : OTy)
  /-- The constant `c` at `pos`, at the objects `us` of its object variables, each with whether `c` is generic
      over it and whether `c` reads its universe, and the arguments `args`, each passed as its pair test where
      `ts` says so (`Form`), its plan on keys in demand when `d`;
      `cv` its converse's constant (`Tm.call`); `tst`: `c` is the pair test of a body that only tests (§a). `alt`
      the definition's body expanded at the use, which every analysis reads and `build` does not. -/
  | call (pos : Pos) (c : Lean.Name) (us : List (OTy × Bool × Bool)) (args : List Pre) (ts : List Bool) (alt : Pre)
      (a b : OTy)
      (d : Bool) (cv : Option (Lean.Name × Bool)) (tst : Bool)

instance : Inhabited Pre := ⟨.id (.base "")⟩

/-- The `why` of a top-level term's `close`. -/
def noLeft : String := "the term here needs keys and has no left context"

/-! ### Object variables -/

/-- The form of an argument at a call (module design §5 M): closed (`none`), run on the keys in demand
    (`some false`), tested on pairs (`some true`, its pair test, §a); or a family whose index is the class `i` among
    the call's indices (§e). Part of the constant's signature. -/
abbrev Form := Option Bool × Option Nat

/-- What a call needs of a constant (the registry), read off its `Once` by `sigOf`. -/
structure Sig where
  /-- The constant. -/
  const : Lean.Name
  /-- Its plan's demand bit. -/
  demand : Bool
  /-- Per object variable, whether it is generic over it and whether it reads its universe. -/
  vars : List (Bool × Bool)
  /-- Its converse's constant and demand bit. -/
  conv : Option (Lean.Name × Bool)
  /-- Whether it is a pair test. -/
  tst : Bool
  /-- Whether a family result `I ⟶ a×b` is its keyed form `I×a ⟶ b` (`keyed`). -/
  kf : Bool
  deriving Inhabited, Repr, BEq

/-- A definition elaborated once at its arguments' forms (`once`). Not an extension of `Sig`: a `Sig` is computed
    from it (`sigOf`), its universes read and converse taken from the body. -/
structure Once where
  /-- Its registry key (`formKey`). -/
  key : Lean.Name
  /-- Its constant. -/
  const : Lean.Name
  /-- Per object variable whether the constant is generic over it (the variables' universes are the term
      variables `0 … n-1`). -/
  gen : List Bool
  /-- Its parameters' objects and demand bits as the constant takes them (the variables from `n` on). -/
  params : List (Obj × Obj × Bool)
  /-- Its body. -/
  res : Res
  /-- Whether that body is its pair test (it builds no relation, §a). -/
  tst : Bool
  /-- Whether it is a family's keyed form. -/
  kf : Bool

structure St where
  /-- The fixed points so far: the next one's variable. -/
  fixes : Nat := 0
  /-- The constants built so far at the forms the program's calls take, in the order `emit` adds them. -/
  specs : List Once := []
  /-- The objects of the program elaborating, where a call tries its arguments' forms (`callDef`): a definition's
      own scope does not hold the caller's objects nor the universes of its object variables. -/
  objs : Objs := []

/-- Elaboration outside a term: the program's error, over Lean's metavariables. -/
abbrev EM := ExceptT Err Lean.Meta.MetaM

/-- The elaborator: its object variables are Lean's metavariables, solved by Lean's unifier (`unify`). -/
abbrev M := StateT St EM

-- `throw`, `try … catch` here are the program's `Err`, not the `Exception` of the `MetaM` under it
instance (priority := high) : MonadExcept Err EM := { throw := throwThe Err, tryCatch := tryCatchThe Err }
instance (priority := high) : MonadExcept Err M := { throw := throwThe Err, tryCatch := tryCatchThe Err }

def fresh : M OTy := do
  let m ← Lean.mkFreshMVarId
  discard <| Lean.Meta.mkFreshExprMVarWithId m (some (.const ``Obj []))
  pure (.mv m)

/-- `o` with every solved variable replaced, as the metavariable context `mc` has them. -/
def zonk (mc : Lean.MetavarContext) (o : OTy) : OTy := .ofExpr (Lean.instantiateMVarsCore mc o.toExpr).1

/-- `x` and `y` made one object by Lean's unifier, which leaves the variables as they were when it fails. -/
def defEq (x y : OTy) : M Bool := Lean.Meta.isDefEq x.toExpr y.toExpr

/-- Unify `x` (found) with `y` (expected); the error names both as the program wrote them. -/
def unify (p : Pos) (what : String) (x y : OTy) : M Unit := do
  unless ← defEq x y do
    let mc ← Lean.getMCtx
    throw ⟨p, s!"{what}: found {zonk mc x}, expected {zonk mc y}"⟩

/-- Where a match that fails part way goes back to: the elaborator's state and Lean's metavariables. -/
def save : M (St × Lean.Meta.SavedState) := return (← get, ← Lean.Meta.saveState)

def restore (s : St × Lean.Meta.SavedState) : M Unit := do set s.1; s.2.restore

/-! ### Fixed points: where the variable occurs -/

/-- How a term reads one of its parts: monotonically, antitonically (`what` names the place), or neither (`op`,
    an operator not monotonic in its argument). -/
inductive Pol
  | mono
  | anti (what : String)
  | not (op : String)

/-- `x` with its positions through `fp` and its parts through `f`, one level down, `f` told how `x` reads each
    part, or `none` for a copy of a part `x` reads elsewhere: a call's arguments (in `alt`), a `ν`'s start (the
    conjuncts of its body). Every walk over `Pre` is an instance (`parts`, `at`, `nilSrcs`). -/
def Pre.traverse {m : Type → Type} [Monad m] (fp : Pos → m Pos) (f : Option Pol → Pre → m Pre) (x : Pre) :
    m Pre :=
  let mo := f (some .mono)
  match x with
  | .top q a b t => return .top (← fp q) a b (← t.mapM mo)
  | .comp x y => return .comp (← mo x) (← mo y)
  | .conv x => return .conv (← mo x)
  | .meet x y => return .meet (← mo x) (← mo y)
  | .join x y => return .join (← mo x) (← mo y)
  | .diff x y => return .diff (← mo x) (← f (some (.anti "the right operand of −")) y)
  | .dom x => return .dom (← mo x)
  | .ran x => return .ran (← mo x)
  | .ldiv q x y b c => return .ldiv (← fp q) (← f (some (.anti "the left operand of \\")) x) (← mo y) b c
  | .rdiv q x y a b => return .rdiv (← fp q) (← mo x) (← f (some (.anti "the right operand of /")) y) a b
  | .pair x y => return .pair (← mo x) (← mo y)
  | .prod x y => return .prod (← mo x) (← mo y)
  | .junc x y => return .junc (← mo x) (← mo y)
  | .lam x => return .lam (← f (some (.not "Λ")) x)
  | .E x => return .E (← f (some (.not "E")) x)
  | .map x => return .map (← mo x)
  | .filter x => return .filter (← mo x)
  | .takewhile x => return .takewhile (← mo x)
  | .est x => return .est (← mo x)
  | .thin x => return .thin (← f (some (.not "thin")) x)
  | .own x => return .own (← mo x)
  | .thinL x => return .thinL (← f (some (.not "thinL")) x)
  | .merge x => return .merge (← f (some (.not "merge")) x)
  | .loop x => return .loop (← mo x)
  | .succ q n => return .succ (← fp q) n
  | .arith q k n => return .arith (← fp q) k n
  | .leq q n => return .leq (← fp q) n
  | .lt q n => return .lt (← fp q) n
  | .fold e s => return .fold (← mo e) (← mo s)
  | .foldI e s => return .foldI (← mo e) (← mo s)
  | .flat x => return .flat (← mo x)
  | .lit q a b ps => return .lit (← fp q) a b ps
  | .close q x a why => return .close (← fp q) (← mo x) a why
  | .var q k a b t => return .var (← fp q) k a b t
  | .fix q l k S x a b => return .fix (← fp q) l k (← S.mapM (f none)) (← mo x) a b
  | .refold q k ch x a b => return .refold (← fp q) k (← mo ch) (← mo x) a b
  | .call q c us xs ts alt a b d cv tst => return .call (← fp q) c us (← xs.mapM (f none)) ts (← mo alt) a b d cv tst
  | x => pure x

/-- The parts of `x`, each with how `x` reads it. A definition's body is expanded at its use, so the prelude's
    and the program's definitions need no rule of their own. -/
def Pre.parts (x : Pre) : List (Pre × Pol) :=
  (Id.run ((x.traverse (m := StateM (List (Pre × Pol))) pure fun pol y => do
    if let some pol := pol then modify (· ++ [(y, pol)])
    pure y).run [])).2

/-- `x` with every position `p`: a prelude body at its use, so an error `build` raises in it is at the use (§c). -/
partial def Pre.at (p : Pos) (x : Pre) : Pre := Id.run (x.traverse (fun _ => pure p) fun _ y => pure (y.at p))

/-- The source of each `nil` in `x`, a definition's body at its use included. -/
partial def Pre.nilSrcs : Pre → List OTy
  | .nil a _ => [a]
  | x => x.parts.flatMap (·.1.nilSrcs)

/-- A `nil` whose source no context fixed, once the whole term is elaborated, starts at `1`: B&dM's
    `nil : 1 ⟶ [A]`, `one` the object `1` in scope (`Env.one`). A fold's seed `ran(nil)` drops that source, so only
    this rule gives it (§e). -/
def settleNil (one : OTy) (p : Pos) (x : Pre) : M Unit := x.nilSrcs.forM fun a => do
  if let .mv _ := zonk (← Lean.getMCtx) a then unify p "nil's source" a one

/-- Where the variable `k` first occurs in `x`. -/
partial def Pre.occ (k : Nat) : Pre → Option Pos
  | .var p j _ _ _ => if j == k then some p else none
  | x => x.parts.findSome? (·.1.occ k)

/-- The first occurrence of `X`, the variable `k` of `fx` (`μX`, `νX`), where the body is not monotonic in it:
    under an operator that is not, or under an odd number of antitone places, `why` the last of them. -/
partial def Pre.polarity (k : Nat) (fx x : String) (pos : Bool) (why : String) : Pre → Option Err
  | .var p j _ _ _ =>
    if j == k && !pos then
      some ⟨p, s!"{fx}: {x} occurs in {why} at {p.line}:{p.col} (antitone); {x} must occur only in monotonic positions"⟩
    else none
  | y => y.parts.findSome? fun (z, pol) => match pol with
    | .mono => z.polarity k fx x pos why
    | .anti w => z.polarity k fx x (!pos) w
    | .not op => (z.occ k).map fun p => ⟨p,
      s!"{fx}: {x} occurs under {op} at {p.line}:{p.col}; {op} is not monotonic in its argument, so the fixed point need not exist"⟩

def Pre.conjuncts : Pre → List Pre
  | .meet x y => x.conjuncts ++ y.conjuncts
  | x => [x]

/-- The meet of the top-level conjuncts of `x` that do not mention the variable `k`: `X ⊑ φ(X) ⊑ S`, so the
    greatest fixed point lies below `S`, and `ν`'s rounds start there. -/
def Pre.bound (k : Nat) (x : Pre) : Option Pre :=
  match x.conjuncts.filter (·.occ k |>.isNone) with
  | [] => none
  | c :: cs => some (cs.foldl .meet c)

/-! ### Elaboration: environments and the lifted rows of §e -/

/-- An elaborated argument or result: one relation `s ⟶ t`, or a family `i ⟶ a×b` read as its fibres `a ⟶ b`. -/
inductive Arg
  | rel (p : Pre) (s t : OTy)
  | fam (p : Pre) (i a b : OTy)

instance : Inhabited Arg := ⟨.rel default default default⟩

/-- A definition: its arity, and its expansion at given arguments (§e: substituted, lifted when a declared
    parameter is given a family). -/
structure Def where
  arity : Nat
  apply : Pos → List Arg → M Arg

structure Env where
  objs : Objs := []
  defs : List (String × Def) := []
  params : List (String × Arg) := []
  /-- The resolver (module design §2.3), and the other programs' definitions and objects by constant: where a name
      the program does not define goes. -/
  res : String → Found := fun _ => .none
  ext : List (Lean.Name × Def) := []
  extObjs : List (Lean.Name × ObjInfo) := []

/-- The definition `n`: the program's, else the one the resolver gives. -/
def Env.def? (env : Env) (n : String) : Option Def :=
  (env.defs.lookup n).orElse fun _ => match env.res n with | .ext e => if e.obj || e.thm then none else env.ext.lookup e.const | _ => none

/-- The infix operator `n`: the program's `_n_`, else the registered infix the resolver gives. -/
def Env.infix? (env : Env) (n : String) : Option Def :=
  (env.defs.lookup s!"_{n}_").orElse fun _ => match env.res n with | .ext e => if e.isInfix then env.ext.lookup e.const else none | _ => none

/-- The object `n`: the program's, else the registered object the resolver gives. -/
def Env.obj? (env : Env) (n : String) : Option ObjInfo :=
  (env.objs.lookup n).orElse fun _ => match env.res n with | .ext e => if e.obj then env.extObjs.lookup e.const else none | _ => none

/-- The object `1` in scope, the source a `nil` no context fixes starts at (`settleNil`). -/
def Env.one (env : Env) : OTy := ((env.obj? "1").map (·.ty)).getD (.base "1")

/-- `o` as the program wrote it, resolved: an alias stands for its definition, a variable for its object in `vs`,
    one use's instantiation (§e). -/
def oty (env : Env) (vs : List (String × OTy) := []) : OExp → M OTy
  | .name p n => match env.obj? n with
    | some i => pure i.ty
    | none => throw ⟨p, s!"unknown object '{n}'"⟩
  | .var p n => match vs.lookup n with
    | some o => pure o
    | none => throw ⟨p, s!"the object variable '{n}' is not instantiated here"⟩
  | .prod a b => return .prod (← oty env vs a) (← oty env vs b)
  | .sum a b => return .sum (← oty env vs a) (← oty env vs b)
  | .pow a | .list a => return .arr (← oty env vs a)

/-! ### The lifted rows of §e, each shape stated once -/

/-- The operators a lifted row is written in: at `Pre` a shape builds the row, at `Pat` it recognises one (`keyed`).
    `Pre`'s own constructors are not enough: a `match` pattern cannot repeat an object, and a row's objects repeat.
    `ω`, `π` are what an object and a place are at `τ`. -/
class Shape (τ : Type) where
  ω : Type
  π : Type
  comp : τ → τ → τ
  pair : τ → τ → τ
  meet : τ → τ → τ
  join : τ → τ → τ
  diff : τ → τ → τ
  dom : τ → τ
  id : ω → τ
  outl : ω → ω → τ
  outr : ω → ω → τ
  prod : ω → ω → ω
  top : π → ω → ω → Option τ → τ
  close : π → τ → ω → String → τ

instance : Shape Pre := ⟨OTy, Pos, .comp, .pair, .meet, .join, .diff, .dom, .id, .outl, .outr, .prod, .top, .close⟩

/-- What recognising a row binds, each at its first occurrence: the place `q`, the parts `R`, `S`, the objects
    `a`–`d`. A row that does not mention a hole leaves it unbound. -/
structure Holes where
  q : Option Pos := none
  R : Option Pre := none
  S : Option Pre := none
  a : Option OTy := none
  b : Option OTy := none
  c : Option OTy := none
  d : Option OTy := none

abbrev Pat := StateT Holes Option Unit

/-- A shape as a recogniser. An object a row writes as `a×b` binds `a`, `b` when the term's is a product and is not
    checked otherwise, as a place the row reads its objects from elsewhere. -/
instance : Shape (Pre → Pat) where
  ω := OTy → Pat
  π := Pos → Pat
  comp f g := fun | .comp x y => do f x; g y | _ => failure
  pair f g := fun | .pair x y => do f x; g y | _ => failure
  meet f g := fun | .meet x y => do f x; g y | _ => failure
  join f g := fun | .join x y => do f x; g y | _ => failure
  diff f g := fun | .diff x y => do f x; g y | _ => failure
  dom f := fun | .dom x => f x | _ => failure
  id o := fun | .id x => o x | _ => failure
  outl o o' := fun | .outl x y => do o x; o' y | _ => failure
  outr o o' := fun | .outr x y => do o x; o' y | _ => failure
  prod o o' := fun | .prod x y => do o x; o' y | _ => pure ()
  top q o o' t := fun
    | .top q' x y t' => do q q'; o x; o' y; match t, t' with | none, none => pure () | some f, some z => f z | _, _ => failure
    | _ => failure
  close q f o _ := fun | .close q' x y _ => do q q'; f x; o y | _ => failure

section Shapes

open Shape

variable {τ : Type} [Shape τ]

/-- `RS` lifted, `R : I ⟶ a×b`, `S` keyed: `⟨𝟙,R⟩⟨π₂π₁,⟨π₁,π₂π₂⟩S⟩`, each row `(a,b)` of `R` at its key `i` joined
    with `S` on `(i,b)`. Not `⟨R,S⟩` cut to the agreeing middles, which pairs every row of `R` with every row of `S`
    at a key. -/
def compSh (I a b : ω τ) (R S : τ) : τ :=
  let ab := prod a b
  comp (pair (Shape.id I) R) (pair (comp (outr I ab) (outl a b)) (comp (pair (outl I ab) (comp (outr I ab) (outr a b))) S))

/-- `⟨R,S⟩` lifted: `⟨R,S⟩dom(π₁π₁ ∩ π₂π₁)⟨π₁π₁,⟨π₁π₂,π₂π₂⟩⟩`, pairs of rows of one source. -/
def pairSh (a b c : ω τ) (R S : τ) : τ :=
  let ab := prod a b; let ac := prod a c
  comp (comp (pair R S) (dom (meet (comp (outl ab ac) (outl a b)) (comp (outr ab ac) (outl a c)))))
    (pair (comp (outl ab ac) (outl a b)) (pair (comp (outl ab ac) (outr a b)) (comp (outr ab ac) (outr a c))))

/-- `R×S` lifted: `⟨R,S⟩⟨⟨π₁π₁,π₂π₁⟩,⟨π₁π₂,π₂π₂⟩⟩`. -/
def prodSh (a b a' b' : ω τ) (R S : τ) : τ :=
  let ab := prod a b; let ab' := prod a' b'
  comp (pair R S) (pair (pair (comp (outl ab ab') (outl a b)) (comp (outr ab ab') (outl a' b')))
    (pair (comp (outl ab ab') (outr a b)) (comp (outr ab ab') (outr a' b'))))

/-- A family then a closed `C`: `F⟨π₁,π₂C⟩`, each row's value carried by `C`. -/
def thenSh (a b : ω τ) (F C : τ) : τ := comp F (pair (outl a b) (comp (outr a b) C))

/-- `dom(F)` lifted: `F⟨π₁,π₁⟩`. -/
def domSh (a b : ω τ) (F : τ) : τ := comp F (pair (outl a b) (outl a b))

/-- `⊤` as a family: `D⊤`, `⊤ : I ⟶ a×b`. -/
def topSh (q : π τ) (I a b : ω τ) : τ := top q I (prod a b) none

/-- A closed `C : a ⟶ b` as a family, `D⊤⟨𝟙,C⟩`, `⊤ : I ⟶ a` onto `V`. -/
def constSh (q : π τ) (I a : ω τ) (V : Option τ) (C : τ) : τ := comp (top q I a V) (pair (Shape.id a) C)

/-- `constSh` onto `dom(C')`, `C` read whole there. -/
def closedSh (q : π τ) (I a : ω τ) (C' C : τ) : τ := constSh q I a (some (close q (dom C') a "a closed term in a lifted body")) C

end Shapes

/-- A row of §e: its shape at the index `I`, the place `q`, the parts `R S` and the objects `a b c d`, and its keyed
    form from the holes recognising it binds, `K` keying a part at its objects, `a b` the family's. -/
structure Row where
  shape : {τ : Type} → [S : Shape τ] → S.ω → S.π → τ → τ → S.ω → S.ω → S.ω → S.ω → τ
  keyed : (Pre → OTy → OTy → Pre) → OTy → OTy → Holes → Option Pre

/-- The holes `x` binds when it has `r`'s shape. -/
def Row.match? (r : Row) (x : Pre) : Option Holes :=
  (r.shape (τ := Pre → Pat) (fun _ => pure ())
    (fun v => modify fun h => { h with q := h.q <|> some v })
    (fun v => modify fun h => { h with R := h.R <|> some v }) (fun v => modify fun h => { h with S := h.S <|> some v })
    (fun v => modify fun h => { h with a := h.a <|> some v }) (fun v => modify fun h => { h with b := h.b <|> some v })
    (fun v => modify fun h => { h with c := h.c <|> some v }) (fun v => modify fun h => { h with d := h.d <|> some v })
    x).run {} |>.map (·.2)

section Rows

open Pre

variable (I : OTy) (p : Pos)

/-- A closed `C : a ⟶ b` as a family: `D⊤⟨𝟙,C⟩`, `⊤ : I ⟶ a` onto `dom(C)`; `⊤` itself is `D⊤`, `𝟙` is
    `D⊤⟨𝟙,𝟙⟩` (§e). -/
def liftConst (C : Pre) (a b : OTy) : Pre × OTy × OTy :=
  match C with
  | .top _ _ _ none => (topSh p I a b, a, b)
  | .id _ => (constSh p I a none (.id a), a, b)
  | C => (closedSh p I a C C, a, b)

/-- A result as a family over `I`. -/
def famOf : Arg → M (Pre × OTy × OTy)
  | .fam q i a b => do unify p "the index of a family" i I; pure (q, a, b)
  | .rel q s t => pure (liftConst I p q s t)

/-- The rows whose fibre at a source reads only that source, in the order `keyed` tries them. -/
def rows : List Row := [
  ⟨fun _ _ R S _ _ _ _ => Shape.join R S, fun K a b h => return join (K (← h.R) a b) (K (← h.S) a b)⟩,
  ⟨fun _ _ R S _ _ _ _ => Shape.meet R S, fun K a b h => return meet (K (← h.R) a b) (K (← h.S) a b)⟩,
  ⟨fun _ _ R S _ _ _ _ => Shape.diff R S, fun K a b h => return diff (K (← h.R) a b) (K (← h.S) a b)⟩,
  -- `D⊤`, `⊤ : I ⟶ a×b`: `D⊤`, `⊤ : I×a ⟶ b`
  ⟨fun I q _ _ a b _ _ => topSh q I a b, fun _ _ _ h => return top (← h.q) (.prod I (← h.a)) (← h.b) none⟩,
  -- a closed `C` onto `V = dom(C')`: `dom(π₂C')π₂C`, so `C'` too runs on the sources in demand, not on its universe
  ⟨fun I q R S a _ _ _ => closedSh q I a R S, fun _ a _ h => return comp (dom (comp (outr I a) (← h.R))) (comp (outr I a) (← h.S))⟩,
  -- a closed `C` onto `V`: `π₂VC`, `C` run on the sources `π₂V` meets
  ⟨fun I q R S a _ _ _ => constSh q I a (some R) S, fun _ a _ h => return comp (comp (outr I a) (← h.R)) (← h.S)⟩,
  ⟨fun I q _ S a _ _ _ => constSh q I a none S, fun _ a _ h => return comp (outr I a) (← h.S)⟩,
  -- `RS` lifted, and `X⦇e,S⦈` lifted, `G : I×b ⟶ c` keyed: `⟨π₁,Rᴵ⟩G`
  ⟨fun I _ R S a b _ _ => compSh I a b R S, fun K _ _ h => do
    let a ← h.a; return comp (pair (outl I a) (K (← h.R) a (← h.b))) (← h.S)⟩,
  -- `⟨R,S⟩` lifted: `⟨Rᴵ,Sᴵ⟩`
  ⟨fun _ _ R S a b c _ => pairSh a b c R S, fun K _ _ h => do
    let a ← h.a; return pair (K (← h.R) a (← h.b)) (K (← h.S) a (← h.c))⟩,
  -- `R×S` lifted: `⟨⟨π₁,π₂π₁⟩Rᴵ,⟨π₁,π₂π₂⟩Sᴵ⟩` on `I×(a×a')`
  ⟨fun _ _ R S a b a' b' => prodSh a b a' b' R S, fun K _ _ h => do
    let a ← h.a; let a' ← h.c; let s := OTy.prod a a'
    return pair (comp (pair (outl I s) (comp (outr I s) (outl a a'))) (K (← h.R) a (← h.b)))
      (comp (pair (outl I s) (comp (outr I s) (outr a a'))) (K (← h.S) a' (← h.d)))⟩,
  -- `F` then `C`: `FᴵC`
  ⟨fun _ _ F C a b _ _ => thenSh a b F C, fun K _ _ h => return comp (K (← h.R) (← h.a) (← h.b)) (← h.S)⟩,
  -- `dom(F)` lifted: `dom(Fᴵ)π₂`
  ⟨fun _ _ F _ a b _ _ => domSh a b F, fun K _ _ h => do let a ← h.a; return comp (dom (K (← h.R) a (← h.b))) (outr I a)⟩]

/-- The family `R : I ⟶ a×b` as one relation of the key and the source, `Rᴵ : I×a ⟶ b`, run on the pairs
    (key, source) in demand (§e, cost of the keyed fold). A row whose fibre at a source reads only that source
    is keyed through its parts, so a closed part runs on the sources in demand, not on its domain at every key.
    Any other family is read whole at each key and cut to the source, `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂`: every part
    runs on the keys in demand, so `I` needs no universe (a converse or `ran` here would close over all of `I`). -/
partial def keyed (R : Pre) (a b : OTy) : Pre :=
  ((rows I).findSome? fun r => r.match? R >>= r.keyed (keyed · · ·) a b).getD (flat R)

def lComp : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, b', c) => do
    unify p "the middle object of a composition" b' b
    pure (compSh I a b R (keyed I S b c), a, c)

def lThen : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (F, a, b), (C, s, t) => do
    unify p "the middle object of a composition" s b
    pure (thenSh a b F C, a, t)

def lConv : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp R (pair (outr a b) (outl a b)), b, a)

def lDom : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (domSh a b R, a, a)

def lRan : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp R (pair (outr a b) (outr a b)), b, b)

/-- `∼R` lifted: `D⊤ − R`, `⊤ : I ⟶ a×b`. -/
def lCompl : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (diff (topSh p I a b) R, a, b)

/-- `∩ ∪ −` lifted: the same operator on the two families. -/
def lSame (op : Pre → Pre → Pre) : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, a', b') => do
    unify p "the source of the right operand" a' a; unify p "the target of the right operand" b' b
    pure (op R S, a, b)

def lLdiv (R S : Pre × OTy × OTy) : M (Pre × OTy × OTy) := do
  unify p "the source of `\\`'s right operand" S.2.1 R.2.1
  pure (lCompl I p (← lComp I p (lConv R) (lCompl I p S)))

def lRdiv (R S : Pre × OTy × OTy) : M (Pre × OTy × OTy) := do
  unify p "the target of `/`'s right operand" S.2.2 R.2.2
  lComp I p (lCompl I p R) (lConv S)

def lPair : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, a', c) => do
    unify p "the source of the pair's second part" a' a
    pure (pairSh a b c R S, a, .prod b c)

def lProd : Pre × OTy × OTy → Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b), (S, a', b') => (prodSh a b a' b' R S, .prod a a', .prod b b')

/-- `[R,S]` lifted: `R⟨π₁inl,π₂⟩ ∪ S⟨π₁inr,π₂⟩`, the row `R(inl×𝟙) ∪ S(inr×𝟙)` with no universe. -/
def lJunc : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, c), (S, b, c') => do
    unify p "the target of the case's second part" c' c
    pure (join (comp R (pair (comp (outl a c) (inl a b)) (outr a c)))
      (comp S (pair (comp (outl b c) (inr a b)) (outr b c))), .sum a b, c)

/-- `Λ(R)` lifted on the sources `S : I ⟶ a` of each key, `Rπ₁` (`dom`) when none: `⟨𝟙,S⟩⟨π₂,Λ(Rᴵ)⟩`. `Λ` takes
    `S = ⊤` onto `a`'s universe, being total; `E` and `thin` take `dom`, as their `a = [x]` has no universe. -/
def lLam (S : Option Pre) : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp (pair (id I) (S.getD (comp R (outl a b)))) (pair (outr I a) (lam (keyed I R a b))), a, .arr b)

/-- `X⦇e,S⦈` lifted, `X : I ⟶ a×[x]`, `e : I ⟶ v×v`, `S : I ⟶ (x×v)×v`: `⟨𝟙,X⟩⟨π₂π₁,⟨π₁,π₂π₂⟩⦇e,S'⦈ᴵ⟩`, where
    `⦇e,S'⦈ᴵ : I×[x] ⟶ v` folds each array at its key, carrier `I×v`, `S' ≜ ⟨π₂π₁,⟨π₁,π₂π₂⟩⟩⟨π₁,Sᴵ⟩`. -/
def lFold : Pre × OTy × OTy → Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (X, a, xs), (e, v, v'), (S, xv, w) => do
    unify p "the fold's start, a coreflexive" v' v
    let x ← fresh
    unify p "the source of the fold's step" xv (.prod x v)
    unify p "the target of the fold's step" w v
    unify p "the arrays a fold runs on" xs (.arr x)
    let iv := OTy.prod I v; let xv := OTy.prod x v
    let S' := comp (pair (comp (outr x iv) (outl I v)) (pair (outl x iv) (comp (outr x iv) (outr I v))))
      (pair (outl I xv) (keyed I S xv v))
    pure (compSh I a (.arr x) X (foldI e S'), a, v)

end Rows

/-- A row that has no lifting (§e). -/
def notLiftable {α : Type} (p : Pos) (what : String) : M α :=
  throw ⟨p, s!"{what} given a family is not liftable: it runs one relation on every array (§e)"⟩

/-- The front-end form of a result: a family outside its body is a relation `i ⟶ a×b`. -/
def Arg.plain : Arg → Pre × OTy × OTy
  | .rel q s t => (q, s, t)
  | .fam q i a b => (q, i, .prod a b)

def Arg.isFam : Arg → Bool
  | .fam .. => true
  | _ => false

/-- The row `r` at fresh objects for its constant's object variables. -/
def Prim.inst (env : Env) (r : Prim) : M (Pre × OTy × OTy) := do
  let vs ← r.vars.mapM fun v => return (v, ← fresh)
  let s ← oty env vs r.sig.2.1; let t ← oty env vs r.sig.2.2
  pure (.prim r s t, s, t)

/-- A constant: fresh objects for its type, the explicit ones `(A,B)` unified with source and target. -/
def constant (env : Env) (p : Pos) (o : Op) (objs : List OExp) : M Arg := do
  let a ← fresh; let b ← fresh
  let row ← match o with
    | .prim s => match Prim.find? s with
      | some r => some <$> r.inst env
      | none => throw ⟨p, s!"internal: no row `{s}` in `prims`"⟩
    | _ => pure none
  let (q, s, t) : Pre × OTy × OTy := row.getD <| match o with
    | .id => (.id a, a, a)
    | .zero => (.zero a b, a, b)
    | .top => (.top p a b none, a, b)
    | .mem => (.mem b, .arr b, b)
    | .outl => (.outl a b, .prod a b, a)
    | .outr => (.outr a b, .prod a b, b)
    | .inl => (.inl a b, a, .sum a b)
    | .inr => (.inr a b, b, .sum a b)
    | .leq => (.leq p a, a, a)
    | .lt => (.lt p a, a, a)
    | .succ => (.succ p a, a, a)
    | .arith k => (.arith p k a, .prod a a, a)
    | .nil => (.nil a b, a, .arr b)
    | .alpha => (.junc (.close p (.nil a b) a "α") (.close p (.prim consRow (.prod b (.arr b)) (.arr b)) (.prod b (.arr b)) "α"),
        .sum a (.prod b (.arr b)), .arr b)
    | .index k => (.atPos k b, .arr b, b)
    | _ => (.id a, a, a)
  match objs with
  | [] => pure ()
  | [x] => unify p s!"the object of {o.sym}" s (← oty env [] x)
  | [x, y] => do unify p s!"the source of {o.sym}" s (← oty env [] x); unify p s!"the target of {o.sym}" t (← oty env [] y)
  | _ => throw ⟨p, s!"{o.sym} takes at most two objects, found {objs.length}"⟩
  pure (.rel q s t)

/-- The declared objects holding all the words `ws` (named elements, or numbers in their range), each once: an
    imported object is in scope under its name and its constant, one object (`Expand.walk`). -/
def holders (objs : Objs) (ws : List String) : List OTy :=
  let holds (i : ObjInfo) (w : String) : Bool := i.elems.contains w ||
    match i.range, w.toInt? with | some (lo, hi), some k => lo ≤ k && k ≤ hi | _, _ => false
  ((objs.filter fun (_, i) => ws.all (holds i)).map (·.2.ty)).eraseDups

/-- Why the rows `ts` of a literal's position do not determine its object: they are none (an empty array's
    elements), or several declared objects hold their words. -/
def litOpen (objs : Objs) (p : Pos) (ts : List Tup) : Err :=
  let ws := ts.filterMap fun | .leaf w => some w | _ => none
  if ts.isEmpty then ⟨p, s!"the object of {(Tup.arr []).show} cannot be read off an empty array: write nil(A,[O])"⟩
  else ⟨p, s!"the elements {ws} are in {holders objs ws}; write the literal after its object"⟩

/-- The object of a literal's position, `ts` the sides there, one per row or array element (§c): a word's is the
    one declared object holding all the words, a pair's the product of its parts', an array's `[O]`, `O` the
    object of the elements of all its arrays together. Where the rows do not determine it (`litOpen`) it is an
    open object, which the context fixes as it fixes `nil`'s; `litCol` reports one still open at `build`. -/
partial def litTy (objs : Objs) (p : Pos) (ts : List Tup) : M OTy := do
  let t := ts.headD default
  if let some r := ts.find? (!·.like t) then
    throw ⟨p, s!"the rows of a literal nest alike: found {r.show}, expected the form of {t.show}"⟩
  match ts, t with
  | [], _ => fresh
  | _, .leaf _ =>
    let ws := ts.filterMap fun | .leaf w => some w | _ => none
    match holders objs ws with
    | [o] => pure o
    | [] => throw ⟨p, s!"no declared object has the elements {ws}"⟩
    | _ => fresh
  | _, .pair .. =>
    pure (.prod (← litTy objs p (ts.map fun | .pair a _ => a | r => r))
      (← litTy objs p (ts.map fun | .pair _ b => b | r => r)))
  | _, .arr _ => pure (.arr (← litTy objs p (ts.flatMap fun | .arr es => es | _ => [])))

/-- A builtin applied to relations, every argument one relation. -/
def applied (p : Pos) (o : Op) : List (Pre × OTy × OTy) → M Arg
  | [(q, s, t)] => do
    match o with
    | .dom => pure (.rel (.dom q) s s)
    | .ran => pure (.rel (.ran (.close p q s "ran( ) reads its argument whole")) t t)
    | .lam => pure (.rel (.lam q) s (.arr t))
    | .E => pure (.rel (.E q) (.arr s) (.arr t))
    | .map => pure (.rel (.map q) (.arr s) (.arr t))
    | .P => throw ⟨p, s!"P(R) : 𝒫{s} ⟶ 𝒫{t} has no universe on its target and no demand there (§a)"⟩
    | .est | .thin | .thinL | .merge => do
      unify p s!"the target of {o.sym}'s argument" t s
      -- the order is tested on the pairs the operator compares (`build`, `param`), not read whole
      let c := Pre.close p q s s!"{o.sym}( )"
      let a := OTy.arr s
      let (r, x, y) : Pre × OTy × OTy := match o with
        | .est => (.est c, a, s) | .thin => (.thin c, a, a) | .thinL => (.thinL c, a, a)
        | _ => (.merge c, .prod a a, a)
      pure (.rel r x y)
    | .loop => do
      let x ← fresh; let y ← fresh
      unify p "the source of loop's argument" s (.prod x y); unify p "the target of loop's argument" t x
      pure (.rel (.loop q) (.prod x (.arr y)) x)
    | _ => throw ⟨p, s!"{o.sym} takes {(Op.table.find? (·.2.1 == o)).map (·.2.2) |>.getD 0} arguments, found 1"⟩
  | as => throw ⟨p, s!"{o.sym}: wrong number of arguments, found {as.length}"⟩

/-- A builtin applied with a family among its arguments, by the rows of §e. -/
def appliedL (I : OTy) (p : Pos) (o : Op) (as : List Arg) : M Arg := do
  let fs ← as.mapM (famOf I p)
  let r ← match o, fs with
    | .dom, [R] => pure (lDom R)
    | .ran, [R] => pure (lRan R)
    | .lam, [R] => pure (lLam I (some (.top p I R.2.1 none)) R)
    | .E, [R] => do let b ← fresh; pure (lLam I none (← lComp I p (liftConst I p (.mem b) (.arr b) b) R))
    | .P, _ => notLiftable p "P(R)"
    | o, _ => notLiftable p s!"{o.sym}( )"
  pure (.fam r.1 I r.2.1 r.2.2)

/-- A binary operator on one relation each side. -/
def binary (p : Pos) (o : Bin) : Pre × OTy × OTy → Pre × OTy × OTy → M Arg
  | (q, s, t), (r, s', t') => do
    match o with
    | .meet | .join | .diff => do
      unify p s!"the source of {o.sym}'s right operand" s' s; unify p s!"the target of {o.sym}'s right operand" t' t
      let x := match o with
        | .meet => Pre.meet q r | .join => .join q r | _ => .diff q r
      pure (.rel x s t)
    | .rdiv => do
      unify p "the target of `/`'s right operand" t' t
      let w := "R/S reads its operands whole outside a meet with a term run on demand"
      pure (.rel (.rdiv p (.close p q s w) (.close p r s' w) s s') s s')
    | .ldiv => do
      unify p "the source of `\\`'s right operand" s' s
      let w := "R\\S reads its operands whole outside a meet with a term run on demand"
      pure (.rel (.ldiv p (.close p q s w) (.close p r s w) t t') t t')
    -- `R×S = ⟨π₁R,π₂S⟩`: `build` runs it as that pair when an operand runs on demand
    | .prod => pure (.rel (.prod (.close p q s "R×S") (.close p r s' "R×S")) (.prod s s') (.prod t t'))

/-- A binary operator with a family on a side, by the rows of §e. -/
def binaryL (I : OTy) (p : Pos) (o : Bin) (x y : Arg) : M Arg := do
  let R ← famOf I p x; let S ← famOf I p y
  let r ← match o with
    | .meet => lSame p Pre.meet R S
    | .join => lSame p Pre.join R S
    | .diff => lSame p Pre.diff R S
    | .rdiv => lRdiv I p R S
    | .ldiv => lLdiv I p R S
    | .prod => pure (lProd R S)
  pure (.fam r.1 I r.2.1 r.2.2)

/-- A defined operator's result where it is used, given the arguments `as`: a family stays one inside a lifted
    body of the same index when an argument is a family of that body; applied to closed terms only, it is a
    closed relation `i ⟶ a×b`, which enters the body by the closed row (§e, mixed terms), as it does outside. -/
def settle (m : Option OTy) (p : Pos) (as : List Arg) : Arg → M Arg
  | .fam q i a b => match m, as.any Arg.isFam with
    | some I, true => do unify p "the index of a family" i I; pure (.fam q i a b)
    | _, _ => pure (.rel q i (.prod a b))
  | r => pure r

/-- `refold(c, S)`'s functor `G`, read off `c : a ⟶ t` (`t = G(a)`) and `S : s ⟶ b` (`s = G(b)`) along `×`, `+`,
    `[ ]`: a place where `t` is `a` and `s` is `b` (or not known yet) is `G`'s argument, one where they are one object
    a constant. Its terms: `G(X) : t ⟶ G(b)`, `X` the variable `k` (`F` on `[ ]`, `⟨π₁·,π₂·⟩` on `×`, `[· inl,· inr]`
    on `+`, `𝟙` where `G` is constant), the object `G(b)`, and `G`'s membership `G(a) ⟶ a`, none where `G` is
    constant; the terms `μX : c G(X) S` would elaborate to as written. -/
partial def refoldG (p : Pos) (k : Nat) (a b : OTy) (t s : OTy) : M (Pre × OTy × Option Pre) := do
  let any := match s with | .mv _ => true | _ => false
  if t == a && (s == b || any) then return (.var p k a b none, b, some (.id a))
  let w := "[R,S] reads its parts whole"
  match t, s with
  | .prod t₁ t₂, .prod s₁ s₂ | .prod t₁ t₂, s₁@(.mv _) =>
    let s₂ := match s with | .prod _ s₂ => s₂ | _ => s₁
    let (g₁, u₁, m₁) ← refoldG p k a b t₁ s₁; let (g₂, u₂, m₂) ← refoldG p k a b t₂ s₂
    if m₁.isNone && m₂.isNone then return (.id t, t, none)
    let side (m : Option Pre) (pr : Pre) : Option Pre := m.map (.comp pr)
    let mem := match side m₁ (.outl t₁ t₂), side m₂ (.outr t₁ t₂) with | some l, some r => some (.join l r) | l, r => l <|> r
    return (.pair (.comp (.outl t₁ t₂) g₁) (.comp (.outr t₁ t₂) g₂), .prod u₁ u₂, mem)
  | .sum t₁ t₂, .sum s₁ s₂ | .sum t₁ t₂, s₁@(.mv _) =>
    let s₂ := match s with | .sum _ s₂ => s₂ | _ => s₁
    let (g₁, u₁, m₁) ← refoldG p k a b t₁ s₁; let (g₂, u₂, m₂) ← refoldG p k a b t₂ s₂
    if m₁.isNone && m₂.isNone then return (.id t, t, none)
    let junc (l r : Pre) : Pre := .junc (.close p l t₁ w) (.close p r t₂ w)
    return (junc (.comp g₁ (.inl u₁ u₂)) (.comp g₂ (.inr u₁ u₂)), .sum u₁ u₂,
      some (junc (m₁.getD (.zero t₁ a)) (m₂.getD (.zero t₂ a))))
  | .arr t₁, .arr s₁ | .arr t₁, s₁@(.mv _) =>
    let (g₁, u₁, m₁) ← refoldG p k a b t₁ s₁
    if m₁.isNone then return (.id t, t, none)
    return (.map g₁, .arr u₁, m₁.map (.comp (.mem t₁)))
  | _, _ =>
    if t == s || any then return (.id t, t, none)
    throw ⟨p, s!"refold(c, S): c's target and S's source differ at {t} against {s}, which is neither {a} against {b} \
      (the recursion) nor one object (a constant); G is read off them"⟩

mutual

/-- Elaborate `e` in the mode `m`: plain, or the body of a definition lifted to the index `I`. -/
def elabE (env : Env) (m : Option OTy) : Expr → M Arg
  | .name p n => do
    match env.params.lookup n with
    -- a fixed point's variable at the place it is used, which its errors name
    | some (.rel (.var _ k a b x) s t) => pure (.rel (.var p k a b x) s t)
    | some a => pure a
    | none => match env.def? n with
      | some d =>
        if d.arity == 0 then (do settle m p [] (← d.apply p []))
        else throw ⟨p, s!"'{n}' takes {d.arity} arguments, found none"⟩
      | none => throw ⟨p, s!"unknown name '{n}'"⟩
  -- `μX : c G(X) S` as written out by hand, `G` read off the types of `c` and `S`, and the children `c ∈_G`
  | .op p .refold _ [c, s] => do
    if m.isSome then notLiftable p "refold( )"
    let (qc, a, t) := (← elabE env none c).plain; let (qs, s', b) := (← elabE env none s).plain
    let k ← modifyGet fun st => (st.fixes, { st with fixes := st.fixes + 1 })
    let mc ← Lean.getMCtx
    let (gx, gb, mem) ← refoldG p k (zonk mc a) (zonk mc b) (zonk mc t) (zonk mc s')
    unify p "the source of refold's algebra S, G(B)" s' gb
    pure (.rel (.refold c.pos k ((mem.map (.comp qc)).getD (.zero a a)) (.comp (.comp qc gx) qs) a b) a b)
  | .op p o objs args => do
    let as ← elabArgs env m args
    if args.isEmpty then constant env p o objs
    else match m with
      | some I => if as.any Arg.isFam then appliedL I p o as else applied p o (as.map Arg.plain)
      | none => applied p o (as.map Arg.plain)
  | .app p n args => do
    let as ← elabArgs env m args
    match env.def? n with
    | some d =>
      if d.arity != as.length then throw ⟨p, s!"'{n}' takes {d.arity} arguments, found {as.length}"⟩
      settle m p as (← d.apply p as)
    | none => throw ⟨p, s!"unknown name '{n}'"⟩
  -- `R n S`: the definition declared `_n_`, given `R` and `S` (§c)
  | .inf p n a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match env.infix? n with
    | some d => settle m p [x, y] (← d.apply p [x, y])
    | none => throw ⟨p, s!"unknown infix operator '{n}'"⟩
  | .comp a b => do
    let x ← elabE env m a
    let p := b.pos
    -- `Xest(Q)`, `Xthin(Q)` with `Q` a family: `est`, `thin` run one `Q` on every array, so the rows of §e
    -- work on `G ≜ X∋`, the values of each key; a closed `Q` takes the closed row below
    let q? ← match m, b with
      | some _, .op _ .est [] [qe] | some _, .op _ .thin [] [qe] => do
        let y ← elabE env m qe; pure (if y.isFam then some y else none)
      | _, _ => pure none
    let est := match b with | .op _ .est _ _ => true | _ => false
    -- `X⦇e,S⦈` with `e` or `S` a family: the fold keyed by the index, on the arrays `X` gives each key (§e)
    let fold? ← match m, b with
      | some _, .fold _ ea sa => do
        let y ← elabE env m ea; let z ← elabE env m sa
        pure (if y.isFam || z.isFam then some (y, z) else none)
      | _, _ => pure none
    if let (some I, some (y, z)) := (m, fold?) then
      let r ← lFold I p (← famOf I p x) (← famOf I p y) (← famOf I p z)
      return .fam r.1 I r.2.1 r.2.2
    match m, q? with
    | some I, some q => do
      let e ← fresh
      let G ← lThen p (← famOf I p x) (.mem e, .arr e, e)
      let Q ← famOf I p q
      let r ← if est then do lSame p Pre.meet G (← lLdiv I p (lConv G) (lConv Q))
        else do pure (lLam I none (← lSame p Pre.diff G (← lComp I p G (← lSame p Pre.diff Q (lConv Q)))))
      pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let y ← elabE env m b
      match m, x.isFam || y.isFam with
      | some I, true =>
        let r ← match x, y with
          | .fam .., .rel q s t => lThen p (← famOf I p x) (q, s, t)
          | _, _ => do lComp I p (← famOf I p x) (← famOf I p y)
        pure (.fam r.1 I r.2.1 r.2.2)
      | _, _ =>
        let (q, s, t) := x.plain; let (r, s', t') := y.plain
        unify p "the source of the right factor of a composition" s' t
        pure (.rel (.comp q r) s t')
  | .bin p o a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => binaryL I p o x y
    | _, _ => binary p o x.plain y.plain
  | .conv p a => do
    -- `build` pushes the converse to the leaves when the term runs on demand (`convTm`)
    match ← elabE env m a with
    | .fam q i s t => let r := lConv (q, s, t); pure (.fam r.1 i r.2.1 r.2.2)
    | .rel q s t => pure (.rel (.conv (.close p q s "R°")) t s)
  | .compl p a => do
    match ← elabE env m a with
    | .fam q i s t => let r := lCompl i p (q, s, t); pure (.fam r.1 i r.2.1 r.2.2)
    | .rel q s t => pure (.rel (.diff (.top p s t none) q) s t)
  | .pair p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => let r ← lPair p (← famOf I p x) (← famOf I p y); pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let (q, s, t) := x.plain; let (r, s', t') := y.plain
      unify p "the source of the pair's second part" s' s
      pure (.rel (.pair q r) s (.prod t t'))
  | .junc p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => let r ← lJunc p (← famOf I p x) (← famOf I p y); pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let (q, s, t) := x.plain; let (r, s', t') := y.plain
      unify p "the target of the case's second part" t' t
      let w := "[R,S] reads its parts whole"
      pure (.rel (.junc (.close p q s w) (.close p r s' w)) (.sum s s') t)
  | .fold p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    if x.isFam || y.isFam then
      throw ⟨p, "⦇e,S⦈ given a family is not liftable on its own: its arrays come from its left, X⦇e,S⦈ (§e)"⟩
    let (q, v, v') := x.plain; let (r, ev, w) := y.plain
    unify p "the fold's start, a coreflexive" v' v
    let e ← fresh
    unify p "the source of the fold's step" ev (.prod e v)
    unify p "the target of the fold's step" w v
    pure (.rel (.fold (.close p q v "the fold's start is read whole") r) (.arr e) v)
  | .lit p ps => do
    let a ← litTy env.objs p (ps.map (·.1)); let b ← litTy env.objs p (ps.map (·.2))
    pure (.rel (.lit p a b ps) a b)
  -- `X : a ⟶ b` in scope in the body, which has that type and is monotonic in `X`; `ν` from the conjuncts
  -- without `X`, `μ` from `𝟘` on any object, its rounds capped at run time (`muCap`)
  | .fix p least x b => do
    let fx := s!"{if least then "μ" else "ν"}{x}"
    if m.isSome then notLiftable p fx
    let a ← fresh; let c ← fresh
    let k ← modifyGet fun s => (s.fixes, { s with fixes := s.fixes + 1 })
    let (q, s, t) := (← elabE { env with params := (x, .rel (.var p k a c none) a c) :: env.params } none b).plain
    unify p s!"the source of {fx}'s body" s a; unify p s!"the target of {fx}'s body" t c
    if let some e := q.polarity k fx x true "" then throw e
    let S := q.bound k
    if !least && S.isNone then
      throw ⟨p, s!"{fx} needs a bound: write S ∩ φ with S not mentioning {x} (⊤(A,B) for the whole object)"⟩
    pure (.rel (.fix p least k S q a c) a c)

def elabArgs (env : Env) (m : Option OTy) : List Expr → M (List Arg)
  | [] => pure []
  | e :: es => do let a ← elabE env m e; pure (a :: (← elabArgs env m es))

end

/-- A declared type matched against an argument's: the variables' objects so far, no match, or a variable met
    at two objects. -/
inductive Match
  | ok (vs : List (String × OTy))
  | no
  | clash (n : String) (o o' : OTy)

/-- `t` as `mk a b`, an unsolved variable solved to that form; none when `t` is another object. -/
def split (p : Pos) (mk : OTy → OTy → OTy) (t : OTy) : M (Option (OTy × OTy)) := do
  let a ← fresh; let b ← fresh
  if ← defEq t (mk a b) then let mc ← Lean.getMCtx; pure (some (zonk mc a, zonk mc b)) else pure none

def Match.bind (r : Match) (k : List (String × OTy) → M Match) : M Match :=
  match r with | .ok vs => k vs | r => pure r

/-- First-order matching of the declared `o` against `t`, extending the instantiation `vs`: a variable takes
    the object it meets, once; a declared object unifies. -/
def pmatch (env : Env) (p : Pos) (vs : List (String × OTy)) : OExp → OTy → M Match
  | .var _ n, t => match vs.lookup n with
    | none => pure (.ok ((n, t) :: vs))
    | some o => do
      if ← defEq t o then pure (.ok vs) else let mc ← Lean.getMCtx; pure (.clash n (zonk mc o) (zonk mc t))
  | .prod x y, t => do match ← split p .prod t with
    | some (a, b) => (← pmatch env p vs x a).bind (pmatch env p · y b)
    | none => pure .no
  | .sum x y, t => do match ← split p .sum t with
    | some (a, b) => (← pmatch env p vs x a).bind (pmatch env p · y b)
    | none => pure .no
  | .pow x, t | .list x, t => do match ← split p (fun a _ => .arr a) t with
    | some (a, _) => pmatch env p vs x a
    | none => pure .no
  | o@(.name ..), t => do
    let O ← oty env [] o
    pure (if ← defEq t O then .ok vs else .no)

/-- `x ⟶ y` matched against `s ⟶ t`. -/
def both (env : Env) (p : Pos) (vs : List (String × OTy)) (x y : OExp) (s t : OTy) : M Match := do
  (← pmatch env p vs x s).bind (pmatch env p · y t)

/-- Bind a parameter to its argument: one relation, or, for a declared `S : A ⟶ B` given `I ⟶ A×B`, a family
    with the index `I` (§e). `vs` is the use's instantiation of the object variables so far. -/
def bind (env : Env) (p : Pos) (P : Param) (a : Arg) (vs : List (String × OTy)) :
    M ((String × Arg) × Option OTy × List (String × OTy)) := do
  match P.ty, a with
  | none, .rel .. => pure ((P.name, a), none, vs)
  | none, .fam .. =>
    throw ⟨p, s!"parameter '{P.name}' is given a family but declares no type; write '{P.name} : A ⟶ B'"⟩
  | some (x, y), a => do
    let sv ← save; let mc := sv.2.meta.mctx
    let decl := s!"'{P.name} : {x.show} ⟶ {y.show}'"
    let clash (r : Match) (s t : OTy) : M Unit := match r with
      | .clash n o o' => throw ⟨p, s!"`{n}` in the type of '{P.name}' is both {o} and {o'}: {decl} given {s} ⟶ {t}"⟩
      | _ => pure ()
    match a with
    | .fam q i s t =>
      match ← both env p vs x y s t with
      | .ok vs => pure ((P.name, .fam q i (← oty env vs x) (← oty env vs y)), some i, vs)
      | r => do restore sv; clash r (zonk mc s) (zonk mc t); throw ⟨p, s!"{decl} given a family of fibre {zonk mc s} ⟶ {zonk mc t}"⟩
    | .rel q s t =>
      -- one relation `A ⟶ B` first; failing that, a family `I ⟶ A×B` (§e)
      let r ← both env p vs x y s t
      if let .ok vs := r then return ((P.name, a), none, vs)
      restore sv
      let r' ← match ← split p .prod t with
        | some (u, v) => both env p vs x y u v
        | none => pure .no
      if let .ok vs := r' then return ((P.name, .fam q s (← oty env vs x) (← oty env vs y)), some s, vs)
      restore sv
      let s := zonk mc s; let t := zonk mc t
      clash r s t; clash r' s t
      throw ⟨p, s!"{decl} given {s} ⟶ {t}: neither {x.show} ⟶ {y.show} nor a family I ⟶ {x.render true}×{y.render true}"⟩

/-- The projection of `(I₀×I₁)×…×Iₙ`, left-nested over the factors `ix`, onto the factor `k`. -/
def proj (ix : Array OTy) (k : Nat) : Pre := go (ix.size - 1)
where
  pre (m : Nat) : OTy := (ix.toList.take (m + 1)).tail.foldl .prod (ix.toList.headD default)
  go : Nat → Pre
    | 0 => .id (pre 0)
    | m + 1 =>
      if m + 1 == k then .outr (pre m) (ix.toList.getD (m + 1) default)
      else if m + 1 > k then .comp (.outl (pre m) (ix.toList.getD (m + 1) default)) (go m)
      else .id (pre (m + 1))

/-! ### Declared types -/

def OTy.mvs : OTy → List Lean.MVarId
  | .mv k => [k]
  | .prod a b | .sum a b => a.mvs ++ b.mvs
  | .arr a => a.mvs
  | .base _ => []

def OTy.bases : OTy → List String
  | .base n => [n]
  | .prod a b | .sum a b => a.bases ++ b.bases
  | .arr a => a.bases
  | .mv _ => []

/-- The letters an inferred type names its open objects by: `α`…`ω` without `ο` and `π`, which read as `o`, `π₁`. -/
def varNames : List String := ("αβγδεζηθικλμνξρστυφχψω".toList).map Char.toString

/-- `o` with each unsolved variable of `os` named an object variable, `α β …` by first occurrence, skipping the
    names `os` already holds: an inferred type as a declaration writes it. -/
def gen (os : List OTy) (o : OTy) (avoid : List String := []) : OTy :=
  let used := avoid ++ os.flatMap OTy.bases
  let σ := (os.flatMap OTy.mvs).eraseDups.zip (varNames.filter (!used.contains ·))
  let rec go : OTy → OTy
    | .mv k => match σ.lookup k with | some n => .base n | none => .mv k
    | .prod a b => .prod (go a) (go b)
    | .sum a b => .sum (go a) (go b)
    | .arr a => .arr (go a)
    | o => o
  go o

/-- The body's type `s ⟶ t` against the declared `ty` of `n`, its variables the parameters' at this use (`vs`)
    and fresh otherwise: the declared type determines the objects the body leaves open (§e). -/
def declared (env : Env) (p : Pos) (n : String) (vs : List (String × OTy)) (ty : OExp × OExp) (s t : OTy) :
    M Unit := do
  let vs ← (ty.1.vars ++ ty.2.vars).foldlM (fun vs v => do
    if (vs.lookup v).isSome then pure vs else pure ((v, ← fresh) :: vs)) vs
  let a ← oty env vs ty.1; let b ← oty env vs ty.2
  let mc ← Lean.getMCtx
  try
    unify p "" s a
    unify p "" t b
  catch _ => do
    let s := zonk mc s; let t := zonk mc t
    throw ⟨p, s!"`{n}` is declared {OExp.arrow ty}, but its body is {gen [s, t] s} ⟶ {gen [s, t] t}"⟩

/-- The parameters `ps` with their objects, each declared one's object variables rigid and an undeclared type
    fresh, and `env` with them in scope: a signature read with no use (`inferSig`, a theorem's statement). -/
def bindSig (env : Env) (ps : List Param) : M (List (String × OTy × OTy) × Env) := do
  let bs ← ps.mapM fun P => do
    match P.ty with
    | some (x, y) =>
      let vs := (x.vars ++ y.vars).map fun v => (v, OTy.base v)
      pure (P.name, ← oty env vs x, ← oty env vs y)
    | none => pure (P.name, ← fresh, ← fresh)
  pure (bs, { env with params := bs.map fun (q, s, t) => (q, .rel (.zero s t) s t) })

/-- The type of `n`, as `typesOf` prints it: each parameter's (declared, its variables kept as written, or
    inferred) and the body's, open objects named as variables; what a definition missing one should write. -/
def inferSig (env : Env) (n : String) (ps : List Param) (b : Body) : M String := do
  let (bs, env') ← bindSig env ps
  let r ← match b with
    | .rel e => do let (_, s, t) := (← elabE env' none e).plain; pure (some (s, t))
    | .test e f => do let _ ← elabE env' none e; let _ ← elabE env' none f; pure none
  let mc ← Lean.getMCtx
  let os := (bs.flatMap fun (_, s, t) => [s, t]) ++ (match r with | some (s, t) => [s, t] | none => [])
  let os := os.map (zonk mc)
  -- a variable is not a name in scope (§e), nor the one being defined
  let avoid := n :: env.defs.map (·.1)
  let arr (s t : OTy) := s!"{gen os (zonk mc s) avoid} ⟶ {gen os (zonk mc t) avoid}"
  pure (sigText n ((ps.zip bs).map fun (P, q, s, t) => (q, some ((P.ty.map OExp.arrow).getD (arr s t))))
    (r.map fun (s, t) => arr s t))

/-- The class of a family argument's index `j?` among the distinct indices `ix` so far, by first occurrence, and
    `ix` with it (§e); `none` for a relation. A definition (`mkDef`) and a call of it (`Expand.callDef`) both number
    by it, so the call lines up with the definition. -/
def idxClass (ix : Array OTy) : Option OTy → M (Array OTy × Option Nat)
  | none => pure (ix, none)
  | some j => do match ← ix.toList.zipIdx.findM? (fun (i, _) => defEq j i) with
    | some (_, k) => pure (ix, some k)
    | none => pure (ix.push j, some ix.size)

/-- A definition with parameters: its body elaborated at each use, lifted when a declared parameter is given
    a family, its result checked against the declared type `ty`; a test `e ⊑ f` is the coreflexive
    `D − dom(R − S)` of the keys whose fibres pass. -/
def mkDef (env : Env) (n : String) (dp : Pos) (ps : List Param) (body : Body) (ty : Option (OExp × OExp)) :
    Def where
  arity := ps.length
  apply p args := do
    -- one instantiation of the object variables per use, shared by the parameters left to right (§e)
    let (bs, vs) ← (ps.zip args).foldlM (fun (bs, vs) (P, a) => do
      let (b, j, vs) ← bind env p P a vs; pure (bs ++ [(b, j)], vs)) ([], [])
    let check (s t : OTy) : M Unit := match ty with
      | some ty => declared env p n vs ty s t
      | none => pure ()
    -- the distinct indices `I₀ … Iₙ` of the family arguments, and each family's place among them (§e, mixed terms)
    let (ix, pl) ← bs.foldlM (fun (ix, pl) (_, j?) => do
      let (ix, k?) ← idxClass ix j?; pure (ix, pl ++ [k?])) (#[], ([] : List (Option Nat)))
    -- several indices: the body runs at `(I₀×I₁)×…`, each family re-keyed by its projection
    let idx := ix.toList.head?.map fun i => ix.toList.tail.foldl .prod i
    let bound := (bs.zip pl).map fun (((n, a), _), k?) => match a, k?, idx with
      | .fam q _ s t, some k, some P => if ix.size > 1 then (n, .fam (.comp (proj ix k) q) P s t) else (n, a)
      | _, _, _ => (n, a)
    let env' := { env with params := bound }
    match body, idx with
    | .rel e, none => do
      let r ← elabE env' none e
      let (_, s, t) := r.plain; check s t; pure r
    | .rel e, some I => do
      let r ← famOf I p (← elabE env' (some I) e)
      check r.2.1 r.2.2
      pure (.fam r.1 I r.2.1 r.2.2)
    | .test _ _, none => throw ⟨p, s!"the test defined at {dp} needs a family; write `check` for one relation"⟩
    | .test e f, some I => do
      let R ← famOf I p (← elabE env' (some I) e)
      let S ← famOf I p (← elabE env' (some I) f)
      let (d, _) ← lSame p Pre.diff R S
      pure (.rel (.diff (.id I) (.dom d)) I I)

/-! ### Build: the solved objects, the core term -/

/-- The swap `A×B ⟶ B×A`, `⟨π₂,π₁⟩`. -/
def swapTm {A B : Obj} : Tm (.prod A B) (.prod B A) true := .pair .outr .outl

/-- `τ(R) = dom(π₂ ∩ π₁R)` for `R` that runs: the pairs `(a,b)` in demand with `a R b`. -/
def pairTest {A B : Obj} {d : Bool} (t : Tm A B d) : Tm (.prod A B) (.prod A B) true :=
  .dom (.meet .outr (.comp .outl t))

/-- `t°` read through one projection of its source `A₁×A₂`: `Zπ₁°` (`.inl Z`) or `Zπ₂°` (`.inr Z`), `Z` run
    on demand. It does not run alone, but a meet with the other projection does (`Proj.meet`). -/
abbrev Proj (B A₁ A₂ : Obj) := (e : Bool) × (Tm B A₁ e ⊕ Tm B A₂ e)

/-- `P` before `Zπᵢ°`: `(PZ)πᵢ°`. -/
def Proj.pre {C B A₁ A₂ : Obj} {d : Bool} (p : Tm C B d) : Proj B A₁ A₂ → Proj C A₁ A₂
  | ⟨_, .inl z⟩ => ⟨_, .inl (.comp p z)⟩
  | ⟨_, .inr z⟩ => ⟨_, .inr (.comp p z)⟩

/-- `Xπᵢ° ∩ Yπⱼ°`: across the two projections the pair `⟨X,Y⟩`, which runs (`Gen.rpair_eq_meet_proj`); on
    one, `(X∩Y)πᵢ°` (`Gen.meet_comp_conv_graph`). -/
def Proj.meet {B A₁ A₂ : Obj} : Proj B A₁ A₂ → Proj B A₁ A₂ → ((e : Bool) × Tm B (.prod A₁ A₂) e) ⊕ Proj B A₁ A₂
  | ⟨_, .inl x⟩, ⟨_, .inr y⟩ => .inl ⟨_, .pair x y⟩
  | ⟨_, .inr x⟩, ⟨_, .inl y⟩ => .inl ⟨_, .pair y x⟩
  | ⟨_, .inl x⟩, ⟨_, .inl y⟩ => .inr ⟨_, .inl (.meet x y)⟩
  | ⟨_, .inr x⟩, ⟨_, .inr y⟩ => .inr ⟨_, .inr (.meet x y)⟩

mutual

/-- `R°` for `R` run on demand (§a), itself run on demand: pushed to the leaves by `(RS)° = S°R°`,
    `(R∩S)° = R°∩S°` (and `∪`, `−`), `⟨R,S⟩° = π₁R° ∩ π₂S°`, a coreflexive is its own converse, and a builtin
    by its named converse (`cons° = uncons`), and the prelude's `perm` as its own (`Tm.own`). A side that reads
    its source through one projection is met with one through the other (`convProj`), so `(R×S)° = R°×S°`. A
    closed part is conversed whole. The error is the leaf whose converse does not run on demand. -/
def convTm {A B : Obj} {d : Bool} (t : Tm A B d) : Except String ((e : Bool) × Tm B A e) :=
  if h : d = false then pure ⟨false, .conv (h ▸ t)⟩ else
  match t with
  | .val R => pure ⟨false, .conv (.val R)⟩
  -- a parameter tested on pairs is a coreflexive, its own converse
  | .var k => pure ⟨true, .var k⟩
  | .nu k S b => pure ⟨false, .conv (.nu k S b)⟩
  | .mu k w n b => pure ⟨false, .conv (.mu k w n b)⟩
  | .uni U => pure ⟨false, .uni U⟩
  | .zero => pure ⟨false, .zero⟩
  | .conv R => pure ⟨false, R⟩
  | .ran R => pure ⟨false, .ran R⟩
  | .ldiv R S U V => pure ⟨false, .conv (.ldiv R S U V)⟩
  | .rdiv R S U V => pure ⟨false, .conv (.rdiv R S U V)⟩
  | .prod R S => pure ⟨false, .conv (.prod R S)⟩
  | .junc R S => pure ⟨false, .conv (.junc R S)⟩
  | .leq U => pure ⟨false, .conv (.leq U)⟩
  | .lt U => pure ⟨false, .conv (.lt U)⟩
  | .id => pure ⟨_, .id⟩
  | .dom R => pure ⟨_, .dom R⟩
  | .own R => pure ⟨_, .own R⟩
  | .comp R S => do let ⟨_, s⟩ ← convTm S; let ⟨_, r⟩ ← convTm R; pure ⟨_, .comp s r⟩
  | .meet R S => match convTm R, convTm S with
    | .ok ⟨_, r⟩, .ok ⟨_, s⟩ => pure ⟨_, .meet r s⟩
    | r, s => do
      let l := match r, s with | .error l, _ => l | _, .error l => l | _, _ => ""
      match A, R, S with
      | .prod _ _, R, S => match convProj R, convProj S with
        | .ok x, .ok y => match Proj.meet x y with | .inl p => pure p | .inr _ => throw l
        | _, _ => throw l
      | _, _, _ => throw l
  | .join R S => do let ⟨_, r⟩ ← convTm R; let ⟨_, s⟩ ← convTm S; pure ⟨_, .join r s⟩
  | .diff R S => do let ⟨_, r⟩ ← convTm R; let ⟨_, s⟩ ← convTm S; pure ⟨_, .diff r s⟩
  -- `⟨R,S⟩° = π₁R° ∩ π₂S°`; with one side's converse only, the other is tested on the pairs it gives:
  -- `⟨π₁R°,π₂⟩τ(S)π₁`, `⟨π₁,π₂S°⟩τ(R°)π₂`
  | .pair R S => match convTm R, convTm S with
    | .ok ⟨_, r⟩, .ok ⟨_, s⟩ => pure ⟨_, .meet (.comp .outl r) (.comp .outr s)⟩
    | .ok ⟨_, r⟩, .error _ => pure ⟨_, .comp (.pair (.comp .outl r) .outr) (.comp (pairTest S) .outl)⟩
    | .error _, .ok ⟨_, s⟩ =>
      pure ⟨_, .comp (.pair .outl (.comp .outr s)) (.comp swapTm (.comp (pairTest R) (.comp swapTm .outr)))⟩
    -- neither runs: each side read through one projection, `⟨π₁P, π₂Q⟩° = ⟨π₁P°, π₂Q°⟩`, i.e. `(P×Q)° = P°×Q°`
    | .error l, .error _ => match A, R, S with
      | .prod _ _, R, S => match convProj R, convProj S with
        | .ok x, .ok y => match Proj.meet (Proj.pre .outl x) (Proj.pre .outr y) with
          | .inl p => pure p
          | .inr _ => throw l
        | _, _ => throw l
      | _, _, _ => throw l
  | .share _ R => convTm R
  -- a row by its converse's row (`cons° = uncons`)
  | .prim r => match r.conv.bind Prim.find? with
    | some r' => pure ⟨_, .prim r'⟩
    | none => throw r.sym
  -- the number verbs are closed on their universe: their converse is read whole there
  | .succ U => pure ⟨false, .conv (.comp U (.succ U))⟩
  | .arith k U => pure ⟨false, .conv (.comp (.prod U U) (.arith k U))⟩
  -- a constant's plan on demand: its converse constant at the same arguments; with none, read whole on its
  -- source's universe
  | .call d c os cv => match cv with
    | some (c', e) => pure ⟨e, .call e c' os (some (c, d))⟩
    | none => throw s!"`{c}`"
  | .arg f x => do let ⟨_, f⟩ ← convTm f; pure ⟨_, .arg f x⟩
  | .top _ => throw "⊤"
  | .mem => throw "∋"
  | .outl => throw "π₁"
  | .outr => throw "π₂"
  | .inl => throw "inl"
  | .inr => throw "inr"
  | .lam _ => throw "Λ( )"
  | .E _ => throw "E( )"
  | .map _ => throw "F( )"
  | .filter _ => throw "filter( )"
  | .takewhile _ => throw "takewhile( )"
  | .est _ => throw "est( )"
  | .thin _ => throw "thin( )"
  | .nil => throw "nil"
  | .refold .. => throw "refold( )"
  | .juncD .. => throw "[R,S]"
  | .atPos k => throw s!"at({k})"
  | .thinL _ => throw "thinL( )"
  | .merge _ => throw "merge( )"
  | .loop _ => throw "loop( )"
  | .fold .. => throw "⦇e,S⦈"
  | .foldI .. => throw "a lifted fold"
  | .flat _ => throw "a lifted family"

/-- `t° = Zπᵢ°` (`Proj`): `π₁° = 𝟙π₁°`, `(RS)° = S°(Zπᵢ°)`, and a meet or pair of two on one projection
    (`Proj.meet`). The error is only that `t` is not of that form: the caller reports its own leaf. -/
def convProj {A₁ A₂ B : Obj} {d : Bool} (t : Tm (.prod A₁ A₂) B d) : Except String (Proj B A₁ A₂) :=
  match t with
  | .outl => pure ⟨_, .inl .id⟩
  | .outr => pure ⟨_, .inr .id⟩
  | .comp R S => do let ⟨_, s⟩ ← convTm S; pure (Proj.pre s (← convProj R))
  | .share _ R => convProj R
  | .meet R S => do match Proj.meet (← convProj R) (← convProj S) with
    | .inr z => pure z
    | .inl _ => throw "a meet across both projections"
  | .pair R S => do match Proj.meet (Proj.pre .outl (← convProj R)) (Proj.pre .outr (← convProj S)) with
    | .inr z => pure z
    | .inl _ => throw "a pair across both projections"
  | _ => throw "not read through one projection"

end

/-- A pair test: `τ(R) : A×B ⟶ A×B`, the coreflexive on the pairs `(a,b)` in demand with `a R b`. -/
abbrev Cor := (A : Obj) × (B : Obj) × Tm (.prod A B) (.prod A B) true

/-- `R ∩ S` with `S` run on demand and `R` tested: `⟨𝟙,S⟩τ(R)π₂`; `R − S` is this with `𝟙 − τ(S)`. -/
def onPairs {A B : Obj} {e : Bool} (s : Tm A B e) (c : Tm (.prod A B) (.prod A B) true) : Tm A B true :=
  .comp (.pair .id s) (.comp c .outr)

/-- `τ(R/S) = 𝟙 − dom(⟨π₁,π₂S⟩(𝟙 − τ(R)))`, `R : A ⟶ C`, `S : B ⟶ C`: no `c` with `b S c` and not `a R c`. -/
def divTest {A B C : Obj} {e : Bool} (c : Tm (.prod A C) (.prod A C) true) (s : Tm B C e) :
    Tm (.prod A B) (.prod A B) true :=
  .diff .id (.dom (.comp (.pair .outl (.comp .outr s)) (.diff .id c)))

section Build

variable (objs : Objs) (mc : Lean.MetavarContext) (dp : Pos)

/-- A solved object's `Obj`: every declared base object is `long`, an object variable as `ObjInfo.obj` stores it. -/
def objOf : OTy → Except Err Obj
  | .base n => pure ((objs.lookup n).elim .long (·.obj))
  | .prod a b => return .prod (← objOf a) (← objOf b)
  | .sum a b => return .sum (← objOf a) (← objOf b)
  | .arr a => return .arr (← objOf a)
  | .mv _ => throw ⟨dp, "an object is not determined; write the constant's objects, as in ⊤(A,B) or 𝟙(A)"⟩

def toObj (o : OTy) : Except Err Obj := objOf objs dp (zonk mc o)

def internal {α : Type} (what : String) : Except Err α := throw ⟨dp, s!"internal: {what}"⟩

/-- `t` at the objects `A ⟶ B`: the cast is the equality `build` decided. -/
def at? {A B : Obj} (r : Res) : Except Err ((d : Bool) × Tm A B d) :=
  match r with
  | ⟨A', B', d, t⟩ => if h : A' = A ∧ B' = B then pure ⟨d, h.1 ▸ h.2 ▸ t⟩ else internal dp "objects disagree"

def closed? {A B : Obj} (r : Res) : Except Err (Tm A B false) := do
  match ← at? dp (A := A) (B := B) r with
  | ⟨false, t⟩ => pure t
  | ⟨true, _⟩ => internal dp "a term that needs keys where none are supplied"

/-- `𝟙` on the universe of `o`, or the error that `o` has none: a declared one's literal (`uniOf`); else built
    from its parts, an object variable's being the universe its constant is given (`uniVar`). -/
def uniPart (o : OTy) (A : Obj) : Except Err (Option (Tm A A false)) := do
  if let some ⟨A', _, U⟩ := uniOf objs o then
    return ← if h : A' = A then pure (some (.uni (h ▸ U))) else internal dp "universe objects disagree"
  match o, A with
  | .base n, _ => pure (((objs.lookup n).bind (·.uniVar)).map .var)
  | .prod a b, .prod A B => do
    let (some u, some v) := (← uniPart a A, ← uniPart b B) | pure none
    pure (some (.prod u v))
  | .sum a b, .sum A B => do
    let (some u, some v) := (← uniPart a A, ← uniPart b B) | pure none
    pure (some (.junc (.comp u .inl) (.comp v .inr)))
  | _, _ => pure none

/-- `uniPart`, or the error naming the whole object `o` that has no universe. -/
def uniTm (p : Pos) (o : OTy) (A : Obj) (what : String) : Except Err (Tm A A false) := do
  match ← uniPart objs dp (zonk mc o) A with
  | some t => pure t
  | none => throw ⟨p, s!"{what}: {zonk mc o} has no universe; compose a set of its elements before it (§a)"⟩

/-- The universe of a number object, for `succ`, the value verbs (`plus`, …), `≤`, `<`: a declared object's,
    or the one a constant is given for an object variable. -/
def numU (p : Pos) (o : OTy) (op : String) : Except Err (Tm .long .long false) :=
  match zonk mc o with
  | .base n => match objs.lookup n with
    | some { uni := some ⟨_, U⟩, .. } => pure (.uni (A := .long) U)
    | some { uniVar := some k, obj := .atom .long, .. } => pure (.var k)
    | some { uniVar := some _, .. } => throw ⟨p, s!"{op} on {n}: a number object, which its constant is not generic over"⟩
    | _ => throw ⟨p, s!"{op} on {n}: no universe"⟩
  | o => throw ⟨p, s!"{op} runs on a declared object, found {o}"⟩

/-- The element `w` of the declared base object `o`: its position among the named elements, or the number. -/
def code (p : Pos) (o : OTy) (w : String) : Except Err Int64 :=
  match zonk mc o with
  | .base n => match objs.lookup n with
    | some i => match i.range, i.elems.idxOf? w, w.toInt? with
      | some (lo, hi), _, some k => if lo ≤ k ∧ k ≤ hi then pure (Int64.ofInt k)
          else throw ⟨p, s!"{w} is not in {n} = {lo}…{hi}"⟩
      | none, some k, _ => pure (Int64.ofNat k)
      | _, _, _ => throw ⟨p, s!"'{w}' is not an element of {n}"⟩
    | none => throw ⟨p, s!"unknown object '{n}'"⟩
  | o => throw ⟨p, s!"a literal relates elements of declared objects, found {o}"⟩

/-- The column of a literal's side of object `o`, its `n` rows' sides `rows`: a long column of codes at a leaf,
    the pair of the two parts' columns at a product, at an array the column of all its elements row after row
    as the payload, row `i` the slice `[lo i, hi i)`. `o` is zonked. -/
def litCol (p : Pos) (n : USize) (o : OTy) (rows : List Tup) : Except Err ((A : Obj) × Vals A n) :=
  match o with
  | .prod x y => do
    let ⟨A, u⟩ ← litCol p n x (rows.map fun | .pair r _ => r | r => r)
    let ⟨B, v⟩ ← litCol p n y (rows.map fun | .pair _ r => r | r => r)
    pure ⟨.prod A B, (u, v)⟩
  | .arr x => do
    let ts ← rows.mapM fun
      | .arr es => pure es
      | r => throw ⟨p, s!"a literal's element of {o} is an array, found {r.show}"⟩
    let es := ts.flatten
    needSize es.length "literal array cells" (fun _ => internal dp "literal array cells") fun m => do
    let ⟨B, v⟩ ← litCol p m x es
    let ends := (ts.foldl (fun (k, acc) t => (k + t.length, (k + t.length) :: acc)) (0, ([] : List Nat))).2.reverse
    let hi := ends.map Int64.ofNat; let lo := (ends.zip ts).map fun (e, t) => Int64.ofNat (e - t.length)
    if h : lo.length.toUSize = n ∧ hi.length.toUSize = n then
      (let l : Arr .long n := h.1 ▸ col lo; let r : Arr .long n := h.2 ▸ col hi; pure ⟨.arr B, ⟨_, l, r, v⟩⟩)
    else internal dp "literal array rows"
  | .mv _ => throw (litOpen objs p rows)
  -- a sum only the context gives, to an empty array's elements: no rows to read
  | .sum x y =>
    if h : n = 0 ∧ rows.isEmpty then h.1 ▸ (do
      let ⟨A, u⟩ ← litCol p 0 x []; let ⟨B, v⟩ ← litCol p 0 y []
      pure ⟨.sum A B, ⟨0, 0, emptyArr .boolean, emptyArr .long, u, v⟩⟩ : Except Err ((A : Obj) × Vals A 0))
    else throw ⟨p, s!"a literal relates elements of declared objects, found {o}"⟩
  | o => do
    let cs ← rows.mapM fun
      | .leaf w => code objs mc p o w
      | r => throw ⟨p, s!"a literal's element of {o} is a word, found {r.show}"⟩
    if h : cs.length.toUSize = n then (let c : Arr .long n := h ▸ col cs; pure ⟨.long, c⟩) else internal dp "literal rows"

/-- A pair test at the objects `A×B`. -/
def corAt (A B : Obj) : Cor → Except Err (Tm (.prod A B) (.prod A B) true)
  | ⟨A', B', c⟩ => if h : A' = A ∧ B' = B then pure (h.1 ▸ h.2 ▸ c) else internal dp "pair-test objects disagree"

/-- A built term read whole: closed as it is, or on demand run on the universe of its source `a`. -/
def closeRes (p : Pos) (a : OTy) (why : String) : Res → Except Err Res
  | ⟨A, B, false, t⟩ => pure ⟨A, B, false, t⟩
  | ⟨A, B, true, t⟩ => return ⟨A, B, false, .comp (← uniTm objs mc dp p a A why) t⟩

/-- The pair test of an order parameter at its object `B`,or the error naming the leaf that is not testable. -/
def paramOf (why : String) : Except Err Cor → Except Err ((B : Obj) × Tm (.prod B B) (.prod B B) true)
  | .ok ⟨A, B, c⟩ => if h : B = A then pure ⟨A, h ▸ c⟩ else internal dp s!"{why}'s order is not on one object"
  | .error e => throw ⟨e.pos,
    s!"{why} runs its order on the pairs it compares, and the order is not testable on pairs (§a): {e.msg}"⟩

mutual

/-- `Pre` to `Tm` at the solved objects. Every check here holds by `elabE`'s unification except the
    universes, whose absence is the error of §a. -/
def build : Pre → Except Err Res
  | .tm r => pure r
  | .zero a b => return ⟨← toObj objs mc dp a, ← toObj objs mc dp b, false, .zero⟩
  | .id a => return ⟨_, _, true, .id (A := ← toObj objs mc dp a)⟩
  | .top p a b tgt => do
    let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
    let V ← match tgt with
      | none => uniTm objs mc dp p b B "⊤'s target"
      | some q => do closed? dp (← build q)
    pure ⟨A, B, true, .top V⟩
  | .mem b => return ⟨_, _, true, .mem (B := ← toObj objs mc dp b)⟩
  | .outl a b => return ⟨_, _, true, .outl (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .outr a b => return ⟨_, _, true, .outr (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .inl a b => return ⟨_, _, true, .inl (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .inr a b => return ⟨_, _, true, .inr (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .comp p q => do
    let ⟨A, B, d, t⟩ ← build p; let ⟨B', C, _, u⟩ ← build q
    if h : B' = B then pure ⟨A, C, d, .comp t (h ▸ u)⟩ else internal dp "composition objects disagree"
  -- `R°`: closed, conversed whole; on demand, pushed to the leaves (`convTm`); a leaf whose converse does not
  -- run on demand reads `R` whole on its source's universe
  | .conv (.close _ (.conv (.close _ q _ _)) _ _) => build q
  | .conv (.close pos q a _) => do
    let ⟨A, B, _, t⟩ ← build q
    match convTm t with
    | .ok ⟨e, u⟩ => pure ⟨B, A, e, u⟩
    | .error leaf => do
      let U ← uniTm objs mc dp pos a A s!"the converse of {leaf} does not run on demand, so R° reads R whole"
      pure ⟨B, A, false, .conv (.comp U t)⟩
  | .conv p => do let r ← build p; let ⟨A, B, _, _⟩ := r; pure ⟨B, A, false, .conv (← closed? dp (A := A) (B := B) r)⟩
  -- a side that cannot run is tested on the pairs the other side gives (`test`)
  | .meet p q => match build p, build q with
    | .ok ⟨A, B, _, t⟩, .ok s => do let ⟨_, u⟩ ← at? dp (A := A) (B := B) s; pure ⟨A, B, _, .meet t u⟩
    | .error err, .ok ⟨A, B, _, s⟩ => match test p with
      | .ok c => do pure ⟨A, B, true, onPairs s (← corAt dp A B c)⟩
      | .error _ => throw err
    | .ok ⟨A, B, _, s⟩, .error err => match test q with
      | .ok c => do pure ⟨A, B, true, onPairs s (← corAt dp A B c)⟩
      | .error _ => throw err
    | .error err, .error _ => throw err
  | .join p q => do let ⟨A, B, _, t⟩ ← build p; let ⟨_, u⟩ ← at? dp (A := A) (B := B) (← build q); pure ⟨A, B, _, .join t u⟩
  | .diff p q => match build p, build q with
    | .ok ⟨A, B, _, t⟩, .ok s => do let ⟨_, u⟩ ← at? dp (A := A) (B := B) s; pure ⟨A, B, _, .diff t u⟩
    | .ok ⟨A, B, _, s⟩, .error err => match test q with
      | .ok c => do pure ⟨A, B, true, onPairs s (.diff .id (← corAt dp A B c))⟩
      | .error _ => throw err
    | .error err, _ => throw err
  | .dom p => do let ⟨A, _, d, t⟩ ← build p; pure ⟨A, A, d, .dom t⟩
  | .ran p => do let r ← build p; let ⟨A, B, _, _⟩ := r; pure ⟨B, B, false, .ran (← closed? dp (A := A) (B := B) r)⟩
  | .ldiv pos p q b c => do
    let r ← build p; let s ← build q; let ⟨A, B, _, _⟩ := r; let ⟨_, C, _, _⟩ := s
    let R ← closed? dp (A := A) (B := B) r; let S ← closed? dp (A := A) (B := C) s
    pure ⟨B, C, false, .ldiv R S (← uniTm objs mc dp pos b B "R\\S") (← uniTm objs mc dp pos c C "R\\S")⟩
  | .rdiv pos p q a b => do
    let r ← build p; let s ← build q; let ⟨A, C, _, _⟩ := r; let ⟨B, _, _, _⟩ := s
    let R ← closed? dp (A := A) (B := C) r; let S ← closed? dp (A := B) (B := C) s
    pure ⟨A, B, false, .rdiv R S (← uniTm objs mc dp pos a A "R/S") (← uniTm objs mc dp pos b B "R/S")⟩
  | .pair p q => do
    let ⟨A, _, _, t⟩ ← build p; let s ← build q; let ⟨_, C, _, _⟩ := s
    let ⟨_, u⟩ ← at? dp (A := A) (B := C) s; pure ⟨A, _, _, .pair t u⟩
  -- `R×S`: both operands closed on their sources, `Alg.prod`; an operand whose source has no universe, the pair
  -- `⟨π₁R,π₂S⟩` on demand
  | .prod (.close pp p a w) (.close pq q b w') =>
    match build (.close pp p a w), build (.close pq q b w') with
    | .ok ⟨A, B, false, t⟩, .ok ⟨C, D, false, u⟩ => pure ⟨.prod A C, .prod B D, false, .prod t u⟩
    | _, _ => do
      let ⟨A, B, _, t⟩ ← build p; let ⟨C, D, _, u⟩ ← build q
      pure ⟨.prod A C, .prod B D, true, .pair (.comp .outl t) (.comp .outr u)⟩
  | .prod p q => do
    let ⟨A, B, _, t⟩ ← build p; let ⟨C, D, _, u⟩ ← build q
    pure ⟨.prod A C, .prod B D, true, .pair (.comp .outl t) (.comp .outr u)⟩
  -- read whole where both parts can be; otherwise on demand, each part on its side's values in demand
  | .junc p@(.close _ p' _ _) q@(.close _ q' _ _) => do
    let whole : Except Err Res := do
      let r ← build p; let s ← build q; let ⟨A, C, _, _⟩ := r; let ⟨B, _, _, _⟩ := s
      pure ⟨_, _, false, .junc (← closed? dp (A := A) (B := C) r) (← closed? dp (A := B) (B := C) s)⟩
    match whole with
    | .ok r => pure r
    | .error _ => do
      let r ← build p'; let s ← build q'; let ⟨A, C, _, _⟩ := r; let ⟨B, _, _, _⟩ := s
      let ⟨_, t⟩ ← at? dp (A := A) (B := C) r; let ⟨_, u⟩ ← at? dp (A := B) (B := C) s
      pure ⟨_, _, true, .juncD t u⟩
  | .junc p q => do
    let r ← build p; let s ← build q; let ⟨A, C, _, _⟩ := r; let ⟨B, _, _, _⟩ := s
    pure ⟨_, _, false, .junc (← closed? dp (A := A) (B := C) r) (← closed? dp (A := B) (B := C) s)⟩
  | .lam p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .lam t⟩
  | .E p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .E t⟩
  | .map p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .map t⟩
  | .filter p => do
    let ⟨A, B, d, t⟩ ← build p
    if h : B = A then pure ⟨_, _, _, .filter (h ▸ t)⟩ else internal dp "filter's predicate is not on one object"
  | .takewhile p => do
    let ⟨A, B, d, t⟩ ← build p
    if h : B = A then pure ⟨_, _, _, .takewhile (h ▸ t)⟩ else internal dp "takewhile's predicate is not on one object"
  | .est p => do let ⟨_, c⟩ ← param p; pure ⟨_, _, _, .est c⟩
  | .thin p => do let ⟨_, c⟩ ← param p; pure ⟨_, _, _, .thin c⟩
  | .nil a b => return ⟨_, _, true, .nil (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .prim r s t => do
    let A ← toObj objs mc dp s; let B ← toObj objs mc dp t
    if r.fits A B then pure ⟨A, B, true, .prim r⟩ else internal dp s!"{r.sym}'s objects"
  | .own p => do
    let ⟨A, B, d, t⟩ ← build p
    if h : B = A then pure ⟨A, A, d, .own (h ▸ t)⟩ else internal dp "perm's objects"
  | .atPos k b => return ⟨_, _, true, .atPos k (B := ← toObj objs mc dp b)⟩
  | .thinL p => do let ⟨_, c⟩ ← param p; pure ⟨_, _, _, .thinL c⟩
  | .merge p => do let ⟨_, c⟩ ← param p; pure ⟨_, _, _, .merge c⟩
  | .loop p => do
    match ← build p with
    | r@⟨.prod X Y, _, _, _⟩ => do let ⟨_, F⟩ ← at? dp (A := .prod X Y) (B := X) r; pure ⟨_, _, true, .loop F⟩
    | _ => internal dp "loop's argument"
  | .succ p n => return ⟨_, _, true, .succ (← numU objs mc p n "succ")⟩
  | .arith p k n => return ⟨_, _, true, .arith k (← numU objs mc p n (Op.arith k).sym)⟩
  | .leq p n => return ⟨_, _, false, .leq (← numU objs mc p n "≤")⟩
  | .lt p n => return ⟨_, _, false, .lt (← numU objs mc p n "<")⟩
  | .fold e s => do
    let r ← build e; let ⟨V, _, _, _⟩ := r
    match ← build s with
    | ⟨.prod E V', V'', _, S⟩ =>
      if h : V' = V ∧ V'' = V then
        pure ⟨.arr E, V, true, .fold (← closed? dp (A := V) (B := V) r) (h.1 ▸ h.2 ▸ S)⟩
      else internal dp "the fold's objects"
    | _ => internal dp "the fold's step"
  | .foldI e s => do
    let r ← build e; let ⟨I, VV, _, _⟩ := r
    let sr ← build s
    match VV, sr with
    | .prod V _, ⟨.prod E _, _, _, _⟩ => do
      let ⟨_, et⟩ ← at? dp (A := I) (B := .prod V V) r
      let ⟨_, S⟩ ← at? dp (A := .prod E (.prod I V)) (B := .prod I V) sr
      pure ⟨_, _, _, .foldI et S⟩
    | _, _ => internal dp "the lifted fold's objects"
  | .flat p => do
    match ← build p with
    | ⟨I, .prod A B, _, t⟩ => pure ⟨.prod I A, B, true, .flat t⟩
    | _ => internal dp "a family's objects"
  | .lit p a b ps =>
    needSize ps.length "literal rows" (fun _ => internal dp "literal rows") fun n => do
    let ⟨A, k⟩ ← litCol objs mc dp p n (zonk mc a) (ps.map (·.1))
    let ⟨B, v⟩ ← litCol objs mc dp p n (zonk mc b) (ps.map (·.2))
    pure ⟨A, B, false, .val ⟨n, k, v⟩⟩
  | .close p q a why => do closeRes objs mc dp p a why (← build q)
  -- the children and the body run on the nodes in demand, no universe read
  | .refold p k ch q a b => do
    let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
    let ⟨_, c⟩ ← at? dp (A := A) (B := A) (← build ch)
    let ⟨_, t⟩ ← at? dp (A := A) (B := B) (← build q)
    pure ⟨A, B, true, .refold k s!"the coalgebra c at {p}" c t⟩
  | .var _ k a b none => return ⟨← toObj objs mc dp a, ← toObj objs mc dp b, false, .var k⟩
  | .var _ k a b (some false) => return ⟨← toObj objs mc dp a, ← toObj objs mc dp b, true, .var k⟩
  -- a parameter given a pair test runs nowhere; `test` reads it
  | .var pos _ _ _ (some true) =>
    throw ⟨pos, "this parameter is tested on the pairs it compares, not run: its argument is a pair test (§a)"⟩
  -- a constant that is a pair test runs nowhere; `test` calls it
  | .call pos c _ _ _ _ _ _ _ _ true =>
    throw ⟨pos, s!"`{c}` is tested on the pairs it compares, not run: its constant is its pair test (§a)"⟩
  | .call pos c us xs ts _ a b d cv false => do
    let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
    let os ← (us.filter (·.2.1)).mapM fun (u, _) => toObj objs mc dp u
    pure ⟨A, B, d, ← callArgs pos c us xs ts (Tm.call (A := A) (B := B) d c os cv)⟩
  -- the body read whole each round, on its source's universe when it needs keys
  | .fix p least k S q a b => do
    let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
    let why := s!"{if least then "μ" else "ν"}'s body is read whole each round"
    let body ← closed? dp (A := A) (B := B) (← closeRes objs mc dp p a why (← build q))
    if least then
      -- a chain from `𝟘` on universes of `n` and `m` elements stops within `n·m+1` rounds, so their `cap` never
      -- fails a monotonic body; an array object has no such bound, and `muCap` only guards termination
      let cap := match uniSize objs (zonk mc a), uniSize objs (zonk mc b) with
        | some n, some m => max muCap (n * m + 2)
        | _, _ => muCap
      pure ⟨A, B, false, .mu k s!"the μ at {p}" cap body⟩
    else match S with
      | some s => do
        let s ← closed? dp (A := A) (B := B) (← closeRes objs mc dp p a why (← build s))
        pure ⟨A, B, false, .nu k s body⟩
      | none => internal dp "ν without its bound"
termination_by x => (sizeOf x, 0)

/-- The call `f` given, per object variable `u` of its constant, the universe of `u` where the constant reads it,
    then the arguments `xs`, each built (closed or run on demand) or, where `ts` says so, its pair test (`Form`). A
    variable the constant is not generic over is a number object (`.long`). -/
def callArgs (pos : Pos) (c : Lean.Name) (us : List (OTy × Bool × Bool)) (xs : List Pre) (ts : List Bool) {A B : Obj}
    {d : Bool} (f : Tm A B d) : Except Err (Tm A B d) := do
  let f ← us.foldlM (init := f) fun f (u, gen, reads) => do
    let U ← toObj objs mc dp u
    unless gen || U == .long do
      throw ⟨pos, s!"`{c}`: an object variable is {zonk mc u} here; its constant is not generic over it, a number object"⟩
    if reads then return .arg f (← uniTm objs mc dp pos u U s!"`{c}`") else pure f
  xs.attach.zipIdx.foldlM (init := f) fun f (⟨x, h⟩, i) => do
    have : sizeOf x < sizeOf xs := List.sizeOf_lt_of_mem h
    if ts.getD i false then let ⟨_, _, t⟩ ← test x; return .arg f t
    let ⟨_, _, _, t⟩ ← build x; pure (.arg f t)
termination_by (sizeOf xs, 3)

/-- `τ(R)`, the pair test of `R : A ⟶ B` (`Cor`), for `R` that cannot enumerate its targets: a term that
    builds is tested as `dom(π₂ ∩ π₁R)`; otherwise by its form — `R/S`, `R\S`, `frac`, `∼`, `−`, `∩`, `∪`, `°`,
    and a composite with a side that runs. The error is `p`'s own build error. -/
def test (p : Pre) : Except Err Cor :=
  match build p with
  | .ok ⟨A, B, _, t⟩ => pure ⟨A, B, pairTest t⟩
  | .error err => match p with
    | .close _ q _ _ => test q
    -- a constant that is a pair test, `τ(c(…)) : A×B ⟶ A×B` (`once`)
    -- a parameter given a pair test (`Form`)
    | .var _ k a b (some true) => do pure ⟨← toObj objs mc dp a, ← toObj objs mc dp b, .var k⟩
    | .call pos c us xs ts _ a b _ _ true => do
      let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
      let os ← (us.filter (·.2.1)).mapM fun (u, _) => toObj objs mc dp u
      pure ⟨A, B, ← callArgs pos c us xs ts (Tm.call (A := .prod A B) (B := .prod A B) true c os none)⟩
    | .conv q => do let ⟨A, B, c⟩ ← test q; pure ⟨B, A, .comp swapTm (.comp c swapTm)⟩
    | .top _ a b none => do pure ⟨← toObj objs mc dp a, ← toObj objs mc dp b, .id⟩
    | .meet q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .meet c₁ (← corAt dp A B (← test r))⟩
    | .join q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .join c₁ (← corAt dp A B (← test r))⟩
    | .diff q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .diff c₁ (← corAt dp A B (← test r))⟩
    -- `τ(PT) = dom(⟨π₁P,π₂⟩τ(T))` with `P` run; `τ(TQ) = dom(⟨π₁,π₂Q°⟩τ(T))` with `Q°` run on demand
    | .comp q r => match build q with
      | .ok ⟨A, M, _, t⟩ => do
        let c ← test r; let ⟨_, B, _⟩ := c
        pure ⟨A, B, .dom (.comp (.pair (.comp .outl t) .outr) (← corAt dp M B c))⟩
      | .error _ => match build r with
        | .ok ⟨M, B, _, u⟩ => match convTm u with
          | .ok ⟨_, v⟩ => do
            let c ← test q; let ⟨A, _, _⟩ := c
            pure ⟨A, B, .dom (.comp (.pair .outl (.comp .outr v)) (← corAt dp A M c))⟩
          | .error _ => throw err
        | .error _ => throw err
    -- `R/S`, `R : A ⟶ C` tested, `S : B ⟶ C` run on the `b`s
    | .rdiv _ (.close _ q _ _) (.close _ r _ _) _ _ => do
      let c ← test q; let ⟨A, C, _⟩ := c
      let ⟨B, _, _, s⟩ ← build r
      let ⟨_, s⟩ ← at? dp (A := B) (B := C) ⟨B, _, _, s⟩
      pure ⟨A, B, divTest (← corAt dp A C c) s⟩
    -- `R\S`, `R : A ⟶ B` with `R°` run on the `b`s, `S : A ⟶ C` tested: `τ = 𝟙 − dom(⟨π₁R°,π₂⟩(𝟙 − τ(S)))`
    | .ldiv _ (.close _ q _ _) (.close _ r _ _) _ _ => do
      let ⟨A, B, _, t⟩ ← build q
      match convTm t with
      | .ok ⟨_, v⟩ => do
        let c ← test r; let ⟨_, C, _⟩ := c
        pure ⟨B, C, .diff .id (.dom (.comp (.pair (.comp .outl v) .outr) (.diff .id (← corAt dp A C c))))⟩
      | .error _ => throw err
    | _ => throw err
termination_by (sizeOf p, 1)

/-- The order (or coreflexive) parameter `Q : B ⟶ B` of `est thin filter takewhile thinL merge`
    as its pair test `τ(Q)` (§a), which the operator runs on the pairs it compares: a closed `Q` and a `Q` that
    runs on demand alike, and any `Q` testable on pairs. `why` names the operator; the error names the leaf. -/
def param : Pre → Except Err ((B : Obj) × Tm (.prod B B) (.prod B B) true)
  | .close _ q _ why => paramOf dp why (test q)
  | q => paramOf dp "an operator" (test q)
termination_by p => (sizeOf p, 2)

end

end Build

end LeetQ.Rel.Lang
