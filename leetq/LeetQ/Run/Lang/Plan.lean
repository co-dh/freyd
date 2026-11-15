import LeetQ.Run.Lang.Expand
import QLean.Db.Own

/-! # A program as kernel calls (`doc/rel-native-design.md` §6), stage 1a: `lit`, `call`, `fail`

A plan is first-order data: instructions over numbered registers, each register defined once, in order. A `call`
names an `@[extern]` kernel by its C symbol; `Plan.run` is what a plan means, calling the same kernels through the
table `kernel%` builds from their declarations, and `relc` (`Rel/Lang/EmitC`) prints the same plan as C. -/

namespace LeetQ.Rel.Lang.Plan

open Lean Elab Term Meta QLean

/-- A register's type: the argument and result types of the kernels' `@[extern]` declarations. -/
inductive Ty
  | bytes | size | bit | u8 | str | parts
  deriving BEq, Repr, Inhabited, ToExpr

/-- What a register holds: a buffer, a size, a bit, a byte, a string, or an array of buffers (a column's parts). -/
inductive Val
  | bytes (b : ByteArray)
  | size (n : USize)
  | bit (b : Bool)
  | u8 (b : UInt8)
  | str (s : String)
  | parts (bs : Array ByteArray)
  deriving Inhabited

def Val.ty : Val → Ty
  | .bytes _ => .bytes | .size _ => .size | .bit _ => .bit | .u8 _ => .u8 | .str _ => .str | .parts _ => .parts

/-- `v` as `fail` prints it: a scalar or a string as itself, a buffer by its size. -/
def Val.show : Val → String
  | .bytes b => s!"<{b.size} bytes>"
  | .size n => toString n
  | .bit b => toString b
  | .u8 b => toString b
  | .str s => s
  | .parts bs => s!"<{bs.size} parts>"

/-- The Lean types a register holds, each with its `Ty`; `kernel%` reads an `@[extern]` signature through it. -/
class Reg (α : Type) where
  ty : Ty
  get? : Val → Option α
  put : α → Val

instance : Reg ByteArray := ⟨.bytes, fun | .bytes b => some b | _ => none, .bytes⟩
instance : Reg USize := ⟨.size, fun | .size n => some n | _ => none, .size⟩
instance : Reg Bool := ⟨.bit, fun | .bit b => some b | _ => none, .bit⟩
instance : Reg UInt8 := ⟨.u8, fun | .u8 b => some b | _ => none, .u8⟩
instance : Reg String := ⟨.str, fun | .str s => some s | _ => none, .str⟩
instance : Reg (Array ByteArray) := ⟨.parts, fun | .parts bs => some bs | _ => none, .parts⟩
/-- A layout is an enum, which the C ABI passes as its constructor index in a byte. -/
instance : Reg Scan.Kind := ⟨.u8, fun
  | .u8 0 => some .bit | .u8 1 => some .u8 | .u8 2 => some .i16 | .u8 3 => some .i32 | .u8 4 => some .i64
  | .u8 5 => some .f32 | .u8 6 => some .f64 | .u8 7 => some .c8 | _ => none,
  fun k => .u8 (match k with | .bit => 0 | .u8 => 1 | .i16 => 2 | .i32 => 3 | .i64 => 4 | .f32 => 5 | .f64 => 6 | .c8 => 7)⟩

/-- A kernel as its `@[extern]` declaration states it (`kernel%`): the C symbol, each argument's type and whether
    it is borrowed (`@&`), the result's types (a product flattened), whether it runs in `IO`, whether the toolchain
    declares it (so `lean.h` defines its symbol, `static inline`), and the Lean call on registers. -/
structure Kernel where
  sym : String
  args : Array (Ty × Bool)
  res : Array Ty
  io : Bool
  std : Bool
  run : Array Val → IO (Array Val)

/-- Argument `i` of the kernel `sym`, read from its register as the type the declaration asks for. -/
def arg {α : Type} [Reg α] (sym : String) (vs : Array Val) (i : Nat) : IO α :=
  match vs[i]?.bind Reg.get? with
  | some a => pure a
  | none => throw (IO.userError s!"{sym}: argument {i} is not a {repr (Reg.ty α)} register")

/-- A result as registers: none for `Unit`, else one. -/
class Out (α : Type) where
  out : α → Array Val

instance : Out Unit := ⟨fun _ => #[]⟩
instance {α : Type} [Reg α] : Out α := ⟨fun a => #[Reg.put a]⟩
/-- A product's registers: its components', left first. -/
instance {α β : Type} [Out α] [Out β] : Out (α × β) := ⟨fun (a, b) => Out.out a ++ Out.out b⟩
/-- A decision is its bit (`lean_usize_dec_eq` answers a `uint8_t`). -/
instance {p : Prop} : Out (Decidable p) := ⟨fun d => #[.bit (@decide p d)]⟩

/-- The `Ty` that `Reg t` answers, read off the instance. -/
def tyOf (t : Lean.Expr) : MetaM Ty := do
  let some inst ← synthInstance? (mkApp (mkConst ``Reg) t)
    | throwError "kernel%: `{t}` is not a register type (`Plan.Reg`)"
  match (← whnfD (mkApp2 (mkConst ``Reg.ty) t inst)).constName? with
  | some ``Ty.bytes => pure .bytes | some ``Ty.size => pure .size | some ``Ty.bit => pure .bit
  | some ``Ty.u8 => pure .u8 | some ``Ty.str => pure .str | some ``Ty.parts => pure .parts
  | _ => throwError "kernel%: `Reg.ty` of `{t}` does not reduce to a `Ty`"

/-- A result's registers' types, as `Out` lays them: none for `Unit`, a product's components', a decision's bit. -/
partial def resTys (r : Lean.Expr) : MetaM (Array Ty) := do
  if r.isConstOf ``Unit then return #[]
  if r.isAppOfArity ``Decidable 1 then return #[.bit]
  if r.isAppOfArity ``Prod 2 then return (← resTys r.appFn!.appArg!) ++ (← resTys r.appArg!)
  return #[← tyOf r]

/-- `kernel% f`: the `Kernel` of the `@[extern]` constant `f`, its symbol, `@&` marks and types read off the
    declaration, so the ABI is never written a second time. -/
elab "kernel% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let some sym := getExternNameFor (← getEnv) `c n | throwError "kernel%: `{n}` has no `@[extern]` C symbol"
  let rec doms : Lean.Expr → List Lean.Expr × Lean.Expr
    | .forallE _ d b _ => let (ds, r) := doms b; (d :: ds, r)
    | e => ([], e)
  let (ds, r) := doms (← getConstInfo n).type
  let args ← ds.toArray.mapM fun d => return (← tyOf d.consumeMData, isMarkedBorrowed d)
  let (io, r) := if r.isAppOfArity ``IO 1 then (true, r.appArg!) else (false, r)
  let res ← resTys r
  -- the toolchain's own externs are the ones `lean.h` defines; its modules are those of `Init`, `Std`, `Lean`
  let env ← getEnv
  let std := (env.getModuleIdxFor? n >>= (env.header.moduleNames[·.toNat]?)).any ([`Init, `Std, `Lean].contains ·.getRoot)
  let vs := mkIdent `vs
  let as : Array Term ← (List.range ds.length).toArray.mapM fun i => `((← arg $(quote sym) $vs $(quote i)))
  let call ← `($(mkIdent n) $as*)
  let run ← if io then `(fun $vs => do let r ← ($call); pure (Out.out r)) else `(fun $vs => do pure (Out.out $call))
  let runE ← elabTermAndSynthesize (← `(($run : Array Val → IO (Array Val)))) none
  return mkAppN (mkConst ``Kernel.mk) #[toExpr sym, toExpr args, toExpr res, toExpr io, toExpr std, ← instantiateMVars runE]

/-- One step. A `lit` defines one register, a `call` as many as its kernel's results, an `apply` as many as the
    function's, a `global` as many as the global's, an `ite` as many as each branch names, a `fail` none. -/
inductive Instr
  /-- `r = lit v`. -/
  | lit (v : Val)
  /-- `r… = call sym(args)`: the `@[extern]` kernel of C symbol `sym` on the registers `args`. -/
  | call (sym : String) (args : Array Nat)
  /-- `need`'s failing branch: print `msg` and the registers `args`, exit 1. -/
  | fail (msg : String) (args : Array Nat)
  /-- `r… = apply f(args)`: the plan's function number `f`, which must come before the one applying it. -/
  | apply (f : Nat) (args : Array Nat)
  /-- `r… = global g`: the registers the plan's global number `g` computed, once, before `main`. -/
  | global (g : Nat)
  /-- `r… = if c then t else e`: a branch runs after the registers so far, and its registers `rt` (`re`) are the
      results; the two name as many. -/
  | ite (c : Nat) (t : List Instr) (rt : Array Nat) (e : List Instr) (re : Array Nat)
  deriving Inhabited

/-- A function: its parameters' types (registers `0 … k-1`, borrowed), its body, its result registers (owned). A
    global is a function of no parameter. -/
structure Fun where
  params : Array Ty
  body : List Instr
  res : Array Nat
  deriving Inhabited

/-- A plan (§6): functions, each applying only earlier ones, so the call graph has no cycle; globals, computed in
    order before `main`; and `main`. -/
structure Plan where
  funs : Array Fun := #[]
  globals : Array Fun := #[]
  main : List Instr
  deriving Inhabited

/-- What `fail msg args` prints: `msg`, then the registers after `: `, separated by `, `. -/
def failText (msg : String) (vs : List Val) : String :=
  if vs.isEmpty then msg else msg ++ ": " ++ ", ".intercalate (vs.map Val.show)

/-- Register `a`, read by `who`. -/
def reg (rs : Array Val) (who : String) (a : Nat) : IO Val := match rs[a]? with
  | some v => pure v
  | none => throw (IO.userError s!"plan: {who} reads register {a}, which no earlier instruction defines")

/-- What a function means, given the globals: its parameters' values to its results'. -/
abbrev Sem := Array (Array Val) → Array Val → IO (Array Val)

mutual
/-- What a block means after the registers `rs`: each instruction in order, each kernel looked up in `abi`, each
    function in `fs`, each global in `gs`. -/
def runB (abi : String → Option Kernel) (fs : Array Sem) (gs : Array (Array Val)) :
    List Instr → Array Val → IO (Array Val)
  | [], rs => pure rs
  | i :: is, rs => do runB abi fs gs is (← runI abi fs gs i rs)

def runI (abi : String → Option Kernel) (fs : Array Sem) (gs : Array (Array Val)) :
    Instr → Array Val → IO (Array Val)
  | .lit v, rs => pure (rs.push v)
  | .call sym as, rs => do
    let some k := abi sym | throw (IO.userError s!"plan: no kernel `{sym}` in the ABI table")
    let out ← k.run (← as.mapM (reg rs sym))
    unless out.size == k.res.size do
      throw (IO.userError s!"plan: `{sym}` answered {out.size} registers, its declaration {k.res.size}")
    pure (rs ++ out)
  | .fail msg as, rs => do throw (IO.userError (failText msg (← as.mapM (reg rs "fail")).toList))
  | .apply f as, rs => do
    let some g := fs[f]? | throw (IO.userError s!"plan: apply f{f}, which is not an earlier function")
    pure (rs ++ (← g gs (← as.mapM (reg rs s!"apply f{f}"))))
  | .global g, rs => do
    let some v := gs[g]? | throw (IO.userError s!"plan: global g{g} read before it is computed")
    pure (rs ++ v)
  | .ite c t rt e re, rs => do
    match ← reg rs "if" c with
    | .bit true => let xs ← runB abi fs gs t rs; pure (rs ++ (← rt.mapM (reg xs "then")))
    | .bit false => let xs ← runB abi fs gs e rs; pure (rs ++ (← re.mapM (reg xs "else")))
    | _ => throw (IO.userError s!"plan: if reads register {c}, which is not a bit")
end

/-- What function `f` means where the functions before it mean `fs`. -/
def Fun.sem (abi : String → Option Kernel) (fs : Array Sem) (f : Fun) : Sem := fun gs args => do
  let xs ← runB abi fs gs f.body args; f.res.mapM (reg xs "result")

/-- The functions' meanings, each seeing only the ones before it. -/
def sems (abi : String → Option Kernel) (funs : Array Fun) : Array Sem :=
  funs.foldl (fun fs f => fs.push (f.sem abi fs)) #[]

/-- What `p` means: the globals in order, then `main`'s registers. -/
def Plan.run (abi : String → Option Kernel) (p : Plan) : IO (Array Val) := do
  let fs := sems abi p.funs
  let gs ← p.globals.foldlM (fun gs g => return gs.push (← g.sem abi fs gs #[])) #[]
  runB abi fs gs p.main #[]

/-! ### Building a plan -/

/-- A plan being built: the current block's instructions, the number of registers defined so far, and the plan's
    functions and globals. -/
abbrev Bld := StateT (Array Instr × Nat × Array Fun × Array Fun) (Except String)

/-- `r = lit v`: the new register. -/
def lit (v : Val) : Bld Nat := modifyGet fun (is, n, fg) => (n, (is.push (.lit v), n + 1, fg))

/-- An instruction defining `nres` registers: the new registers. -/
def emit (i : Instr) (nres : Nat) : Bld (Array Nat) :=
  modifyGet fun (is, n, fg) => ((List.range' n nres).toArray, (is.push i, n + nres, fg))

/-- `call sym(args)` of a kernel answering `nres` registers: the new registers. -/
def call (sym : String) (args : Array Nat) (nres : Nat) : Bld (Array Nat) := emit (.call sym args) nres

/-- `b` as a block of its own after the registers so far: its instructions and result registers; the functions and
    globals it adds stay. -/
def block (b : Bld (Array Nat)) : Bld (List Instr × Array Nat) := do
  let (is, n, fg) ← get
  let (r, is', _, fg') ← b.run (#[], n, fg)
  set (is, n, fg'); pure (is'.toList, r)

/-- `if c then t else e`, both answering as many registers: the new registers. -/
def ite (c : Nat) (t e : Bld (Array Nat)) : Bld (Array Nat) := do
  let (ti, rt) ← block t; let (ei, re) ← block e
  unless rt.size == re.size do throw s!"if r{c}: the branches answer {rt.size} and {re.size} registers"
  emit (.ite c ti rt ei re) rt.size

/-- The function of parameters `ps` and body `b` (run on the parameter registers), added to the plan: its number. -/
def defFun (ps : Array Ty) (b : Array Nat → Bld (Array Nat)) : Bld Nat := do
  let (is, n, fs, gs) ← get
  let (r, body, _, fs', gs') ← (b (List.range ps.size).toArray).run (#[], ps.size, fs, gs)
  set (is, n, fs'.push ⟨ps, body.toList, r⟩, gs'); pure fs'.size

/-- `apply f(args)`, `f` answering `nres` registers. -/
def apply (f : Nat) (args : Array Nat) (nres : Nat) : Bld (Array Nat) := emit (.apply f args) nres

/-- The global computed by `b`, added to the plan, and its registers read here. -/
def global (b : Bld (Array Nat)) : Bld (Array Nat) := do
  let (is, n, fs, gs) ← get
  let (r, body, _, fs', gs') ← b.run (#[], 0, fs, gs)
  set (is, n, fs', gs'.push ⟨#[], body.toList, r⟩)
  emit (.global gs'.size) r.size

/-- The plan of `main`. -/
def Bld.plan (b : Bld Unit) : Except String Plan := do
  let ((), is, _, fs, gs) ← b.run (#[], 0, #[], #[])
  pure ⟨fs, gs, is.toList⟩

/-- A side's atom columns, each with its path in the side: `""` an atom; `.1`/`.2` a product's; `.lo`/`.hi`/`.e`
    an array's bounds and payload; `.tag`/`.idx`/`.l`/`.r` a sum's tags, positions and two payloads. -/
def cols : (A : Obj) → {n : USize} → Vals A n → String → List (String × QValue)
  | .atom _, _, x, p => [(p, x.1)]
  | .prod a b, _, x, p => cols a x.1 (p ++ ".1") ++ cols b x.2 (p ++ ".2")
  | .arr b, _, ⟨_, lo, hi, f⟩, p => [(p ++ ".lo", lo.1), (p ++ ".hi", hi.1)] ++ cols b f (p ++ ".e")
  | .sum a b, _, ⟨_, _, tag, idx, x, y⟩, p =>
    [(p ++ ".tag", tag.1), (p ++ ".idx", idx.1)] ++ cols a x (p ++ ".l") ++ cols b y (p ++ ".r")

/-- A column as qlean's column writer takes it (`Db.ownFile`): `code`, `attr`, `kind`, `count`, `domain`, `parts`. -/
def ownFile (p : String) (v : QValue) : Except String Db.OwnFile :=
  match Db.ownFile v with
  | some f => pure f
  | none => throw s!"column `{p}`: a general list, which qlean's own column format does not hold"

/-- A side's registers: each column's path and its six `ownFile` registers. -/
abbrev Side := List (String × Array Nat)

/-- The side's columns as `lit`s. -/
def litSide {A : Obj} {n : USize} (x : Vals A n) : Bld Side :=
  (cols A x "").mapM fun (p, v) => do
    let f ← ownFile p v
    return (p, ← #[.u8 f.code, .u8 f.attr, .u8 f.kind, .size f.count, .str f.domain, .parts f.parts].mapM lit)

/-- The registers of a closed term's value, key side then value side. Stage 1a builds a literal and a converse,
    which swaps the sides and emits nothing; any other node is refused. -/
def ofTm : {A B : Obj} → {d : Bool} → Tm A B d → Bld (Side × Side)
  | _, _, _, .val R => return (← litSide R.key, ← litSide R.val)
  | _, _, _, .conv R => return (← ofTm R).swap
  | _, _, _, .share _ R => ofTm R
  | _, _, _, _ => throw "a node other than a literal, a converse or a shared term: stage 1a builds only those"

/-! ### Builders of `Alg`'s defs (stage 1b) -/

/-- A one-register instruction's register. -/
def emit1 (i : Instr) : Bld Nat := modifyGet fun (is, n, fg) => (n, (is.push i, n + 1, fg))

/-- `Code.groupIds` on a code's registers `w`, `n`, `card` (as `card.toUSize`, all `idGroups` reads), `b`: one `if`
    per lane `laneKind` names, tested at run time on `w`, `groupIds` at that layout; `idGroups` past the last. -/
def groupIdsB (w n card b : Nat) : Bld (Array Nat) :=
  go ([1, 8, 16, 32, 64].filterMap fun v => (Alg.laneKind v).map (v, ·))
where
  go : List (Nat × Scan.Kind) → Bld (Array Nat)
    | [] => call "qlean_sort_id_groups" #[card, n, w, b] 2
    | (v, k) :: ks => do
      let x ← lit (.size v.toUSize)
      let e ← emit1 (.call "lean_usize_dec_eq" #[w, x])
      ite e (do call "qlean_sort_group_ids" #[← lit (Reg.put k), n, b] 2) (go ks)

/-- `Code.groupIds` as a plan function of the code's four registers. -/
def groupIdsF : Bld Nat := defFun #[.size, .size, .size, .bytes] fun ps => groupIdsB 0 1 2 3

end LeetQ.Rel.Lang.Plan
