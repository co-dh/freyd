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

/-- A kernel as its `@[extern]` declaration states it (`kernel%`): the C symbol, each argument's type and whether
    it is borrowed (`@&`), the result's types, whether it runs in `IO`, and the Lean call on registers. -/
structure Kernel where
  sym : String
  args : Array (Ty × Bool)
  res : Array Ty
  io : Bool
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

/-- The `Ty` that `Reg t` answers, read off the instance. -/
def tyOf (t : Lean.Expr) : MetaM Ty := do
  let some inst ← synthInstance? (mkApp (mkConst ``Reg) t)
    | throwError "kernel%: `{t}` is not a register type (`Plan.Reg`)"
  match (← whnfD (mkApp2 (mkConst ``Reg.ty) t inst)).constName? with
  | some ``Ty.bytes => pure .bytes | some ``Ty.size => pure .size | some ``Ty.bit => pure .bit
  | some ``Ty.u8 => pure .u8 | some ``Ty.str => pure .str | some ``Ty.parts => pure .parts
  | _ => throwError "kernel%: `Reg.ty` of `{t}` does not reduce to a `Ty`"

/-- `kernel% f`: the `Kernel` of the `@[extern]` constant `f`, its symbol, `@&` marks and types read off the
    declaration, so the ABI is never written a second time. A result of more than one register is refused. -/
elab "kernel% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let some sym := getExternNameFor (← getEnv) `c n | throwError "kernel%: `{n}` has no `@[extern]` C symbol"
  let rec doms : Lean.Expr → List Lean.Expr × Lean.Expr
    | .forallE _ d b _ => let (ds, r) := doms b; (d :: ds, r)
    | e => ([], e)
  let (ds, r) := doms (← getConstInfo n).type
  let args ← ds.toArray.mapM fun d => return (← tyOf d.consumeMData, isMarkedBorrowed d)
  let (io, r) := if r.isAppOfArity ``IO 1 then (true, r.appArg!) else (false, r)
  let res ← if r.isConstOf ``Unit then pure #[] else pure #[← tyOf r]
  let vs := mkIdent `vs
  let as : Array Term ← (List.range ds.length).toArray.mapM fun i => `((← arg $(quote sym) $vs $(quote i)))
  let call ← `($(mkIdent n) $as*)
  let run ← if io then `(fun $vs => do let r ← ($call); pure (Out.out r)) else `(fun $vs => do pure (Out.out $call))
  let runE ← elabTermAndSynthesize (← `(($run : Array Val → IO (Array Val)))) none
  return mkAppN (mkConst ``Kernel.mk) #[toExpr sym, toExpr args, toExpr res, toExpr io, ← instantiateMVars runE]

/-- One step. A `lit` defines one register, a `call` as many as its kernel's results, a `fail` none. -/
inductive Instr
  /-- `r = lit v`. -/
  | lit (v : Val)
  /-- `r… = call sym(args)`: the `@[extern]` kernel of C symbol `sym` on the registers `args`. -/
  | call (sym : String) (args : Array Nat)
  /-- `need`'s failing branch: print `msg` and the registers `args`, exit 1. -/
  | fail (msg : String) (args : Array Nat)
  deriving Inhabited

/-- A plan: its instructions. Stage 1a has no functions, globals, branches or loops (§6). -/
structure Plan where
  main : Array Instr
  deriving Inhabited

/-- What `fail msg args` prints: `msg`, then the registers after `: `, separated by `, `. -/
def failText (msg : String) (vs : List Val) : String :=
  if vs.isEmpty then msg else msg ++ ": " ++ ", ".intercalate (vs.map Val.show)

/-- What `p` means: each instruction in order, each register defined once, each kernel looked up in `abi`. -/
def Plan.run (abi : String → Option Kernel) (p : Plan) : IO (Array Val) := do
  let get (rs : Array Val) (who : String) (a : Nat) : IO Val := match rs[a]? with
    | some v => pure v
    | none => throw (IO.userError s!"plan: {who} reads register {a}, which no earlier instruction defines")
  p.main.foldlM (init := #[]) fun rs i => match i with
    | .lit v => pure (rs.push v)
    | .call sym as => do
      let some k := abi sym | throw (IO.userError s!"plan: no kernel `{sym}` in the ABI table")
      let out ← k.run (← as.mapM (get rs sym))
      unless out.size == k.res.size do
        throw (IO.userError s!"plan: `{sym}` answered {out.size} registers, its declaration {k.res.size}")
      pure (rs ++ out)
    | .fail msg as => do throw (IO.userError (failText msg (← as.mapM (get rs "fail")).toList))

/-! ### Building a plan -/

/-- A plan being built: its instructions and the number of registers they define. -/
abbrev Bld := StateT (Array Instr × Nat) (Except String)

/-- `r = lit v`: the new register. -/
def lit (v : Val) : Bld Nat := modifyGet fun (is, n) => (n, (is.push (.lit v), n + 1))

/-- `call sym(args)` of a kernel answering `nres` registers: the new registers. -/
def call (sym : String) (args : Array Nat) (nres : Nat) : Bld (Array Nat) :=
  modifyGet fun (is, n) => ((List.range' n nres).toArray, (is.push (.call sym args), n + nres))

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

end LeetQ.Rel.Lang.Plan
