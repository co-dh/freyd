import LeetQ.Run.Lang.Plan
import LeetQ.Run.Lang.Expand

/-! # `relc`: a plan printed as C (`doc/rel-native-design.md` §6, stage 1a)

The C has no plan interpreter: one line per instruction. A literal is a static Lean object with `m_rc = 0` (a
persistent object, never counted or freed), a kernel a direct call to its C symbol, `fail` a message and exit 1.
It is linked against qlean's `libqleankernel.a` and `qrt.o` (`rust/build.sh rt`), not against the Lean runtime. -/

namespace LeetQ.Rel.Lang.Plan

open QLean

/-- The kernels a plan may call, each read off its `@[extern]` declaration. -/
def abi : List Kernel :=
  [kernel% QLean.Db.ownWrite, kernel% QLean.Kernel.Order.groupIds, kernel% QLean.Kernel.Order.idGroups,
   kernel% USize.decEq, kernel% USize.add, kernel% USize.div, kernel% ByteArray.usize, kernel% Kernel.Ew.val,
   kernel% Kernel.Ew.cmp, kernel% Kernel.Ew.bit, kernel% Kernel.whereBits, kernel% Kernel.gatherBytes]

def abiOf (sym : String) : Option Kernel := abi.find? (·.sym == sym)

/-! ### Writing a relation as a column directory -/

/-- `output R to dir`: each column of `R`'s registers written by `qlean_own_write` to `dir/key<path>` and
    `dir/val<path>`. The directory must exist; the kernel's error names the path when it does not. -/
def output (dir : String) (rs : Side × Side) : Bld Unit := do
  for (side, cs) in [("key", rs.1), ("val", rs.2)] do
    for (p, r) in cs do
      let path ← lit (.str (System.FilePath.mk dir / (side ++ p)).toString)
      discard <| call "qlean_own_write" (#[path] ++ r) 0

/-- The plan of `output x to dir` in the program `prog`, read after the programs `chain` (`Expand.read`). -/
def planOf (chain : List (Lean.Name × Program)) (prog : Program) (x : String) (dir : String) :
    Lean.Meta.MetaM (Except String Plan) := do
  let r ← (Expand.read (fun _ => none) chain prog).run
  return do
    let (ds, _) ← r.mapError (s!"{repr ·}")
    let some ⟨_, _, _, t⟩ := ds.lookup x | throw s!"`{x}` is no closed definition of the program"
    Bld.plan (do output dir (← ofTm t))

/-- The Lean side of the same output: `R`'s columns written by `Db.ownWrite` under the names `output` gives them,
    from the value Lean computed, not from a plan. -/
def writeRel {A B : Obj} (dir : String) (R : Rel A B) : IO Unit := do
  for (side, cs) in [("key", cols A R.key ""), ("val", cols B R.val "")] do
    for (p, v) in cs do
      let f ← IO.ofExcept (ownFile (side ++ p) v)
      Db.ownWrite (System.FilePath.mk dir / (side ++ p)).toString f.code f.attr f.kind f.count f.domain f.parts

/-! ### The C -/

def isObj : Ty → Bool
  | .bytes | .str | .parts => true
  | _ => false

def cTy (t : Ty) : String := match t with
  | .size => "size_t"
  | .bit | .u8 => "uint8_t"
  | .u64 => "uint64_t"
  | .i64 => "int64_t"
  | _ => "lean_object *"

/-- A C string literal of `s`'s bytes, each an octal escape: three digits, so no following byte is absorbed. -/
def cStr (s : String) : String :=
  "\"" ++ String.join (s.toUTF8.toList.map fun b =>
    let o := Nat.toDigits 8 b.toNat; "\\" ++ String.mk (List.replicate (3 - o.length) '0' ++ o)) ++ "\""

/-- A static scalar array `L` holding `b`, `m_rc = 0`. -/
def cBytes (L : String) (b : ByteArray) : String :=
  let n := b.size
  s!"static struct \{ lean_object h; size_t n, c; uint8_t d[{max n 1}]; } __attribute__((aligned(8))) {L} = " ++
    s!"\{\{0, 0, 1, LeanScalarArray}, {n}, {max n 1}, \{" ++
    ", ".intercalate (b.toList.map toString) ++ "}};\n"

/-- The C prototype of `k`, from its declaration: an owned or borrowed object, a scalar; an `IO` world. -/
def proto (k : Kernel) : Except String String := do
  let as := k.args.toList.map fun (t, b) => if isObj t then (if b then "b_lean_obj_arg" else "lean_obj_arg") else cTy t
  let as := if k.io then as ++ ["lean_obj_arg"] else as
  let r ← if k.io then pure "lean_obj_res" else match k.res.toList with
    | [] => pure "void"
    | [t] => pure (cTy t)
    | [a, b] => if isObj a && isObj b then pure "lean_obj_res" else
      throw s!"`{k.sym}`: a pair holding a scalar, whose constructor layout `relc` does not read"
    | _ => throw s!"`{k.sym}`: a result of {k.res.size} registers, which `relc` does not print"
  pure s!"{r} {k.sym}({", ".intercalate as});\n"

/-- `fail`'s print of register `r` of type `t`, as `Val.show` prints it. -/
def cShow (r : String) : Ty → String
  | .bytes => s!"fprintf(stderr, \"<%zu bytes>\", lean_sarray_size({r}));"
  | .size => s!"fprintf(stderr, \"%zu\", {r});"
  | .bit => s!"fputs({r} ? \"true\" : \"false\", stderr);"
  | .u8 => s!"fprintf(stderr, \"%u\", (unsigned){r});"
  | .str => s!"fputs(lean_string_cstr({r}), stderr);"
  | .parts => s!"fprintf(stderr, \"<%zu parts>\", lean_array_size({r}));"
  | .u64 => s!"fprintf(stderr, \"%llu\", (unsigned long long){r});"
  | .i64 => s!"fprintf(stderr, \"%lld\", (long long){r});"

/-- A result register `r` of type `t` read out of the `IO` value `v`. -/
def cUnbox (t : Ty) (v : String) : String := match t with
  | .size => s!"lean_unbox_usize({v})"
  | .bit | .u8 => s!"(uint8_t)lean_unbox({v})"
  | .u64 => s!"lean_unbox_uint64({v})"
  | .i64 => s!"(int64_t)lean_unbox_uint64({v})"
  | _ => v

/-- The registers an instruction reads that were defined before register `base` (an `if`'s first result): a nested
    block's own registers are numbered from `base` on, so its reads below `base` are the outer ones. -/
partial def reads (base : Nat) : Instr → List Nat
  | .call _ as | .fail _ as | .apply _ as => as.toList
  | .ite c t rt e re => c :: ((t.flatMap (reads base) ++ rt.toList ++ e.flatMap (reads base) ++ re.toList).filter (· < base))
  | .lit _ | .global _ => []

/-- How many registers an instruction defines. -/
def defs (abi : String → Option Kernel) (fres : Array (Array Ty)) (gtys : Array (Array Ty)) : Instr → Except String Nat
  | .lit _ => pure 1
  | .call sym _ => match abi sym with | some k => pure k.res.size | none => throw s!"no kernel `{sym}` in the ABI table"
  | .fail .. => pure 0
  | .apply f _ => match fres[f]? with | some t => pure t.size | none => throw s!"apply f{f}: no earlier function"
  | .global g => match gtys[g]? with | some t => pure t.size | none => throw s!"global g{g}: no earlier global"
  | .ite _ _ rt _ _ => pure rt.size

/-- The emitter's state: the next fresh C name, the prototypes, the statics. -/
abbrev EM := StateT (Nat × List String × String) (Except String)

def fresh : EM String := modifyGet fun (k, ps, st) => (s!"v{k}", (k + 1, ps, st))
def static (s : String) : EM Unit := modify fun (k, ps, st) => (k, ps, st ++ s)

/-- A scope's register: its C name, its type, and whether the scope holds a reference it must release. -/
abbrev CReg := String × Ty × Bool

def creg (rs : Array CReg) (a : Nat) : EM CReg := match rs[a]? with
  | some r => pure r
  | none => throw s!"an instruction reads register {a}, which no earlier instruction defines"

/-- The C of the literal `v`, as register `x`. -/
def litC (x : String) (v : Val) : EM String := do
  let L := "L" ++ x
  match v with
  | .bytes b => static (cBytes L b); pure s!"lean_object *{x} = (lean_object *)&{L};\n"
  | .str s =>
    let n := s.utf8ByteSize + 1
    static (s!"static struct \{ lean_object h; size_t n, c, l; char d[{n}]; } __attribute__((aligned(8))) " ++
      s!"{L} = \{\{0, 0, 0, LeanString}, {n}, {n}, {s.length}, {cStr s}};\n")
    pure s!"lean_object *{x} = (lean_object *)&{L};\n"
  | .parts bs =>
    for (b, j) in bs.toList.zipIdx do static (cBytes s!"{L}_{j}" b)
    static (s!"static struct \{ lean_object h; size_t n, c; lean_object *d[{max bs.size 1}]; } " ++
      s!"__attribute__((aligned(8))) {L} = \{\{0, 0, 0, LeanArray}, {bs.size}, {max bs.size 1}, \{" ++
      ", ".intercalate ((List.range bs.size).map (s!"(lean_object *)&{L}_{·}")) ++ "}};\n")
    pure s!"lean_object *{x} = (lean_object *)&{L};\n"
  | .size n => pure s!"size_t {x} = {n}u;\n"
  | .u8 b => pure s!"uint8_t {x} = {b};\n"
  | .bit b => pure s!"uint8_t {x} = {if b then 1 else 0};\n"
  -- through the unsigned bits, so `INT64_MIN` (q's null) is no out-of-range literal
  | .u64 w => pure s!"uint64_t {x} = UINT64_C({w.toNat});\n"
  | .i64 w => pure s!"int64_t {x} = (int64_t)UINT64_C({w.toUInt64.toNat});\n"

/-- A block as C at indent `ind`, after the scope's registers `rs`, releasing the references it holds: those `owe`
    hands it from the enclosing scope and those its instructions make, each right after its last read (§8); an owned
    argument at its last read is moved, not counted. Its results `res` leave owned: moved where the block holds the
    reference, counted otherwise. The C, and the scope's registers at its end. -/
partial def blockC (abi : String → Option Kernel) (fres gtys : Array (Array Ty)) (ind : String) (rs₀ : Array CReg)
    (owe : List Nat) (is : List Instr) (res : Array Nat) : EM (String × Array CReg × Array String) := do
  let held (rs : Array CReg) (a : Nat) : Bool := match rs[a]? with | some (_, t, o) => o && isObj t | none => false
  -- the references held, minus those released; `later j` the reads at and after instruction `j`, results included
  let ia := is.toArray
  let mut bases : Array Nat := #[]
  let mut n := rs₀.size
  for i in ia do bases := bases.push n; n := n + (← defs abi fres gtys i)
  let later (j : Nat) : List Nat := res.toList ++ ((ia.extract j ia.size).zip (bases.extract j ia.size)).toList.flatMap
    fun (i, b) => reads b i
  let mut rs := rs₀
  let mut live : List Nat := owe
  let mut c := ""
  let release (rs : Array CReg) (live : List Nat) (keep : List Nat) : List Nat × String :=
    live.foldl (fun (l, s) a => if keep.contains a then (l ++ [a], s) else
      (l, s ++ match rs[a]? with | some (x, t, _) => if isObj t then s!"{ind}lean_dec({x});\n" else "" | none => "")) ([], "")
  let (l0, s0) := release rs live (later 0); live := l0; c := c ++ s0
  for (i, j) in ia.toList.zipIdx do
    let after := later (j + 1)
    match i with
    | .lit v => let x ← fresh; c := c ++ ind ++ (← litC x v); rs := rs.push (x, v.ty, false)
    | .call sym as =>
      let some k := abi sym | throw s!"no kernel `{sym}` in the ABI table"
      unless k.args.size == as.size do throw s!"`{sym}` takes {k.args.size} registers, given {as.size}"
      let mut args : List String := []
      for ((t, b), a) in k.args.toList.zip as.toList do
        let (x, t', _) ← creg rs a
        unless t' == t do throw s!"`{sym}`: register {a} is a {repr t'}, the kernel's argument a {repr t}"
        if isObj t && !b then
          -- moved where this is its last read and the only one in the call; counted otherwise
          if live.contains a && !after.contains a && (as.toList.filter (· == a)).length == 1 then live := live.erase a
          else c := c ++ s!"{ind}lean_inc({x});\n"
        args := args ++ [x]
      let pr ← proto k
      unless k.std do modify fun (q, ps, st) => (q, if ps.contains pr then ps else ps ++ [pr], st)
      let call := s!"{sym}({", ".intercalate (args ++ if k.io then ["lean_box(0)"] else [])})"
      let call := if k.io then s!"qlean_rt_io({call}, {cStr sym})" else call
      match k.res.toList with
      | [] => c := c ++ s!"{ind}{if k.io then s!"lean_dec({call})" else call};\n"
      | [t] =>
        let x ← fresh
        c := c ++ s!"{ind}{cTy t} {x} = {if k.io then cUnbox t call else call};\n"
        rs := rs.push (x, t, true)
      | [t, u] =>
        let p ← fresh; let x ← fresh; let y ← fresh
        c := c ++ s!"{ind}lean_object *{p} = {call};\n{ind}lean_object *{x} = lean_ctor_get({p}, 0), *{y} = " ++
          s!"lean_ctor_get({p}, 1);\n{ind}lean_inc({x}); lean_inc({y}); lean_dec({p});\n"
        rs := (rs.push (x, t, true)).push (y, u, true)
      | _ => throw s!"`{sym}`: a result of {k.res.size} registers, which `relc` does not print"
      live := live ++ ((List.range k.res.size).map (rs.size - k.res.size + ·))
    | .fail msg as =>
      let shows ← as.toList.zipIdx.mapM fun (a, j) => do
        let (x, t, _) ← creg rs a
        pure ((if j == 0 then "fputs(\": \", stderr); " else "fputs(\", \", stderr); ") ++ cShow x t)
      c := c ++ s!"{ind}fputs({cStr msg}, stderr); " ++ " ".intercalate shows ++ " fputc('\\n', stderr); exit(1);\n"
    | .apply f as =>
      let some ts := fres[f]? | throw s!"apply f{f}: no earlier function"
      let xs ← as.toList.mapM fun a => return (← creg rs a).1
      let os ← ts.toList.mapM fun t => return (← fresh, t)
      for (o, t) in os do c := c ++ s!"{ind}{cTy t} {o};\n"
      c := c ++ s!"{ind}f{f}({", ".intercalate (xs ++ os.map (s!"&{·.1}"))});\n"
      for (o, t) in os do rs := rs.push (o, t, true); live := live ++ [rs.size - 1]
    | .global g =>
      let some ts := gtys[g]? | throw s!"global g{g}: no earlier global"
      for (t, k) in ts.toList.zipIdx do rs := rs.push (s!"g{g}_{k}", t, false)
    | .ite cnd t rt e re =>
      let (x, ty, _) ← creg rs cnd
      unless ty == .bit do throw s!"if reads register {cnd}, a {repr ty}, not a bit"
      -- the references read last here are handed to the branches, each releasing them itself
      let down := live.filter (!after.contains ·)
      live := live.filter (after.contains ·)
      let (tc, trs, txs) ← blockC abi fres gtys (ind ++ "  ") rs down t rt
      let (ec, _, exs) ← blockC abi fres gtys (ind ++ "  ") rs down e re
      let tys ← rt.toList.mapM fun a => return (← creg trs a).2.1
      let os ← tys.mapM fun t => return (← fresh, t)
      for (o, t) in os do c := c ++ s!"{ind}{cTy t} {o};\n"
      let set (xs : Array String) := String.join ((os.zip xs.toList).map fun ((o, _), v) => s!"{ind}  {o} = {v};\n")
      c := c ++ s!"{ind}if ({x}) \{\n" ++ tc ++ set txs ++ s!"{ind}} else \{\n" ++ ec ++ set exs ++ s!"{ind}}\n"
      for (o, t) in os do rs := rs.push (o, t, true); live := live ++ [rs.size - 1]
    let (l, s) := release rs live after; live := l; c := c ++ s
  -- the results: moved where held, counted otherwise
  let mut outs : Array String := #[]
  let mut moved : List Nat := []
  for a in res do
    let (x, t, _) ← creg rs a
    if held rs a && live.contains a && !moved.contains a then moved := a :: moved
    else if isObj t then c := c ++ s!"{ind}lean_inc({x});\n"
    outs := outs.push x
  pure (c, rs, outs)

/-- `p` as one C file: the statics, the kernels' prototypes, one `static` function per plan function, and `main`,
    which computes the globals, runs `main`'s block in the directory its one argument names, and frees the globals. -/
def relc (abi : String → Option Kernel) (p : Plan) : Except String String := do
  let go : EM String := do
    let mut fres : Array (Array Ty) := #[]
    let mut fns := ""
    for (f, i) in p.funs.toList.zipIdx do
      let ps ← f.params.toList.mapM fun t => return (← fresh, t)
      let (c, rs, outs) ← blockC abi fres #[] "  " (ps.toArray.map fun (x, t) => (x, t, false)) [] f.body f.res
      let tys ← f.res.toList.mapM fun a => return (← creg rs a).2.1
      let sig := ps.map (fun (x, t) => s!"{cTy t} {x}") ++ (tys.zipIdx.map fun (t, k) => s!"{cTy t} *o{k}")
      fns := fns ++ s!"static void f{i}({", ".intercalate sig}) \{\n" ++ c ++
        String.join ((outs.toList.zipIdx).map fun (x, k) => s!"  *o{k} = {x};\n") ++ "}\n"
      fres := fres.push tys.toArray
    let mut gtys : Array (Array Ty) := #[]
    let mut gs := ""
    let mut gdec := ""
    for (g, i) in p.globals.toList.zipIdx do
      let (c, rs, outs) ← blockC abi fres gtys "    " #[] [] g.body g.res
      let tys ← g.res.toList.mapM fun a => return (← creg rs a).2.1
      for (t, k) in tys.zipIdx do
        static s!"static {cTy t} g{i}_{k};\n"
        if isObj t then gdec := gdec ++ s!"  lean_dec(g{i}_{k});\n"
      gs := gs ++ "  {\n" ++ c ++ String.join ((outs.toList.zipIdx).map fun (x, k) => s!"    g{i}_{k} = {x};\n") ++ "  }\n"
      gtys := gtys.push tys.toArray
    let (c, _, _) ← blockC abi fres gtys "  " #[] [] p.main #[]
    let (_, protos, stat) ← get
    pure <| "/* generated by relc (LeetQ.Rel.Lang.EmitC): do not edit */\n" ++
      "#include <lean/lean.h>\n#include <errno.h>\n#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n" ++
      "#include <unistd.h>\n\nlean_object *qlean_rt_io(lean_object *r, const char *sym);\n" ++ String.join protos ++
      "\n" ++ stat ++ "\n" ++ fns ++ "\nint main(int argc, char **argv) {\n" ++
      "  if (argc > 2) { fprintf(stderr, \"usage: %s [DIR]\\n\", argv[0]); return 2; }\n" ++
      "  if (argc == 2 && chdir(argv[1]) != 0) { fprintf(stderr, \"chdir %s: %s\\n\", argv[1], strerror(errno)); return 1; }\n" ++
      gs ++ c ++ gdec ++ "  return 0;\n}\n"
  go.run' (0, [], "")

end LeetQ.Rel.Lang.Plan
