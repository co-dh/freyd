import LeetQ.Run.Lang.Plan

/-! # `relc`: a plan printed as C (`doc/rel-native-design.md` §6, stage 1a)

The C has no plan interpreter: one line per instruction. A literal is a static Lean object with `m_rc = 0` (a
persistent object, never counted or freed), a kernel a direct call to its C symbol, `fail` a message and exit 1.
It is linked against qlean's `libqleankernel.a` and `c/rt.c`, not against the Lean runtime. -/

namespace LeetQ.Rel.Lang.Plan

open QLean

/-- The kernels a plan may call, each read off its `@[extern]` declaration. -/
def abi : List Kernel := [kernel% QLean.Db.ownWrite]

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
def planOf (chain : List (Lean.Name × Program)) (prog : Program) (x : String) (dir : String) : Except String Plan := do
  let (ds, _) ← (Expand.read (fun _ => false) chain prog).mapError (s!"{repr ·}")
  let some ⟨_, _, _, t⟩ := ds.lookup x | throw s!"`{x}` is no closed definition of the program"
  let ((), is, _) ← (do output dir (← ofTm t) : Bld Unit).run (#[], 0)
  pure ⟨is⟩

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
    | _ => throw s!"`{k.sym}`: a result of {k.res.size} registers, which stage 1a does not print"
  pure s!"{r} {k.sym}({", ".intercalate as});\n"

/-- `fail`'s print of register `r` of type `t`, as `Val.show` prints it. -/
def cShow (r : Nat) : Ty → String
  | .bytes => s!"fprintf(stderr, \"<%zu bytes>\", lean_sarray_size(r{r}));"
  | .size => s!"fprintf(stderr, \"%zu\", r{r});"
  | .bit => s!"fputs(r{r} ? \"true\" : \"false\", stderr);"
  | .u8 => s!"fprintf(stderr, \"%u\", (unsigned)r{r});"
  | .str => s!"fputs(lean_string_cstr(r{r}), stderr);"
  | .parts => s!"fprintf(stderr, \"<%zu parts>\", lean_array_size(r{r}));"

/-- A result register `r` of type `t` read out of the `IO` value `v`. -/
def cUnbox (t : Ty) (v : String) : String := match t with
  | .size => s!"lean_unbox_usize({v})"
  | .bit | .u8 => s!"(uint8_t)lean_unbox({v})"
  | _ => v

/-- `p` as one C file: the statics, the kernels' prototypes, and `main`, which runs in the directory its one
    argument names. -/
def relc (abi : String → Option Kernel) (p : Plan) : Except String String := do
  let mut stat := ""
  let mut body := ""
  let mut tys : Array Ty := #[]
  let mut protos : List String := []
  for i in p.main do
    match i with
    | .lit v =>
      let r := tys.size
      let L := s!"L{r}"
      match v with
      | .bytes b =>
        stat := stat ++ cBytes L b
        body := body ++ s!"  lean_object *r{r} = (lean_object *)&{L};\n"
      | .str s =>
        let n := s.utf8ByteSize + 1
        stat := stat ++ s!"static struct \{ lean_object h; size_t n, c, l; char d[{n}]; } __attribute__((aligned(8))) " ++
          s!"{L} = \{\{0, 0, 0, LeanString}, {n}, {n}, {s.length}, {cStr s}};\n"
        body := body ++ s!"  lean_object *r{r} = (lean_object *)&{L};\n"
      | .parts bs =>
        for (b, j) in bs.toList.zipIdx do stat := stat ++ cBytes s!"{L}_{j}" b
        stat := stat ++ s!"static struct \{ lean_object h; size_t n, c; lean_object *d[{max bs.size 1}]; } " ++
          s!"__attribute__((aligned(8))) {L} = \{\{0, 0, 0, LeanArray}, {bs.size}, {max bs.size 1}, \{" ++
          ", ".intercalate ((List.range bs.size).map (s!"(lean_object *)&{L}_{·}")) ++ "}};\n"
        body := body ++ s!"  lean_object *r{r} = (lean_object *)&{L};\n"
      | .size n => body := body ++ s!"  size_t r{r} = {n}u;\n"
      | .u8 b => body := body ++ s!"  uint8_t r{r} = {b};\n"
      | .bit b => body := body ++ s!"  uint8_t r{r} = {if b then 1 else 0};\n"
      tys := tys.push v.ty
    | .call sym as =>
      let some k := abi sym | throw s!"no kernel `{sym}` in the ABI table"
      unless k.args.size == as.size do throw s!"`{sym}` takes {k.args.size} registers, given {as.size}"
      for ((t, _), a) in k.args.toList.zip as.toList do
        unless tys[a]? == some t do throw s!"`{sym}`: register {a} is not a {repr t}"
      let pr ← proto k
      unless protos.contains pr do protos := protos ++ [pr]
      -- an owned object argument is consumed by the callee; the register keeps its own reference
      for ((t, b), a) in k.args.toList.zip as.toList do
        if isObj t && !b then body := body ++ s!"  lean_inc(r{a});\n"
      let args := as.toList.map (s!"r{·}") ++ (if k.io then ["lean_box(0)"] else [])
      let c := s!"{sym}({", ".intercalate args})"
      match k.io, k.res.toList with
      | true, [] => body := body ++ s!"  lean_dec(qlean_rt_io({c}, {cStr sym}));\n"
      | true, [t] =>
        body := body ++ s!"  {cTy t} r{tys.size} = {cUnbox t s!"qlean_rt_io({c}, {cStr sym})"};\n"
      | false, [] => body := body ++ s!"  {c};\n"
      | false, [t] => body := body ++ s!"  {cTy t} r{tys.size} = {c};\n"
      | _, _ => throw s!"`{sym}`: a result of {k.res.size} registers, which stage 1a does not print"
      tys := tys ++ k.res
    | .fail msg as =>
      let shows ← as.toList.zipIdx.mapM fun (a, j) => match tys[a]? with
        | some t => pure ((if j == 0 then "fputs(\": \", stderr); " else "fputs(\", \", stderr); ") ++ cShow a t)
        | none => throw s!"fail reads register {a}, which no earlier instruction defines"
      body := body ++ s!"  fputs({cStr msg}, stderr); " ++ " ".intercalate shows ++ " fputc('\\n', stderr); exit(1);\n"
  pure <| "/* generated by relc (LeetQ.Rel.Lang.EmitC): do not edit */\n" ++
    "#include <lean/lean.h>\n#include <errno.h>\n#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n" ++
    "#include <unistd.h>\n\nlean_object *qlean_rt_io(lean_object *r, const char *sym);\n" ++ String.join protos ++
    "\n" ++ stat ++ "\nint main(int argc, char **argv) {\n" ++
    "  if (argc > 2) { fprintf(stderr, \"usage: %s [DIR]\\n\", argv[0]); return 2; }\n" ++
    "  if (argc == 2 && chdir(argv[1]) != 0) { fprintf(stderr, \"chdir %s: %s\\n\", argv[1], strerror(errno)); return 1; }\n" ++
    body ++ "  return 0;\n}\n"

end LeetQ.Rel.Lang.Plan
