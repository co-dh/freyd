// Rel language architecture at master HEAD (dbee43e), read from leetq/LeetQ/Run/Lang/*, Rel/Lang/{RelRep,TestRep,Test}.
#set page(paper: "a5", margin: 12mm)
#set text(size: 9pt, font: ("Noto Serif CJK SC", "Noto Sans CJK SC"), lang: "zh")
#set par(justify: false, leading: 0.5em)
#set list(spacing: 0.45em, indent: 0pt)
#set enum(spacing: 0.45em, indent: 0pt)
#show heading.where(level: 1): set text(size: 10.5pt)
#show heading.where(level: 2): set text(size: 9.5pt)
#show heading: set block(above: 0.75em, below: 0.4em)
#show raw: set text(size: 8pt)
#set table(inset: (x: 2.5pt, y: 1.8pt), stroke: 0.4pt + gray)
#show table: set text(size: 8pt)

#let bx(m, body) = block(width: 100%, inset: 2.5pt, radius: 2pt, stroke: 0.6pt, fill: luma(245), spacing: 0pt)[
  #text(weight: "bold")[#m] #h(2pt) #text(size: 7.5pt)[#body]]
#let ar(lbl) = block(spacing: 2pt, align(center, text(size: 7.5pt)[↓ #h(2pt) #lbl]))

= Rel 语言架构(`leetq/LeetQ`,master `dbee43e`)

== 1. 流水线

#grid(columns: (1fr, 1fr), column-gutter: 6pt,
  [
    #bx[`Grammar`][Lean 语法类别 `relObj relType rel relStmt …`;命令 `rel_program n where`、`rel_program n from b upto x where`]
    #ar[`Syntax` 树]
    #bx[`Parse`][只处理一个 token 内部:按 scope 切名字、`m.x`、`𝒫` 前缀、数字]
    #ar[`Decl`,`Program := List Decl`]
    #bx[`Embed`][`params defn stmt program`;`define`:常量 `n : Program`,再调 `read`、`emit`,写 registry]
    #ar[`Program` + resolver `String → Found`]
    #bx[`Expand.read`/`walk`][逐个 `Decl`;带参数的定义走 `callDef`/`once`;读 `.call`]
    #v(5pt)
    #bx[qlean][`QValue`/`Enc` 列、`@[extern]` C kernel、`Verify`;`Gen` 生成的 `CRel` op 运行时调用它]
  ],
  [
    #bx[`Elab`][`elabE`(`OTy` 元变量,`isDefEq`);`build`/`test`;`convTm`;`keyed`]
    #ar[`Pre` → `Res`;`Read`(定义、print、check、`Objs`、`List Once`)]
    #bx[`Expand.emit`][`number`(`share`);`code`/`node`/`planOr`;`primE`]
    #ar[基于 `Gen`/`CRel` 的 `Lean.Expr`:`n.x`、`n.c.c<i>`、`n.ok`]
    #bx[`Registry`][`emit` 写 `.call`、`.rep`;`define` 写 `.ext .prog .chain`]
    #ar[`RegEntry.rep`:编号后的 `Res`、共享常量]
    #bx[`RelRep`][`rel_rep n` → `n.rep_x`、`n.unproved`;`TestRep` 对所有 `progs` 跑 `rep`]
  ])

== 2. 模块(`wc -l`;只列 Rel 模块之间的 import)

#table(columns: (auto, auto, 1fr, auto),
  table.header[*模块*][*行数*][*负责*][*import*],
  [`Run/Lang/Syntax`], [421], [`Pos Err Ext Found OExp Prim prims prim% Op Bin Tup Expr Decl`], [`CRel*Def`],
  [`Run/Lang/Parse`], [245], [scope 状态 `S`、`name`、`object`、`fresh`、`after`、`constOf`、`extOf`], [`Syntax`],
  [`Run/Lang/Grammar`], [421], [语法类别、`relOp binOp cmpOp`、`relTokens`、`kwBack`、AST 读取器 `C`], [`Parse`],
  [`Run/Lang/Embed`], [262], [两个命令、`define`、`resolverAt`、`homesOf`、`decl_line%`], [`Grammar Expand`],
  [`Run/Lang/Tm`], [142], [`Tm`、`Res`、`Tm.mapM`、`Tm.parts`], [`Syntax`],
  [`Run/Lang/Elab`], [1729], [`OTy Pre Sig Once Arg Def Env M`、`Shape Row keyed`、`elabE build test convTm`], [`Syntax Tm`],
  [`Run/Lang/Bits`], [252], [`Tm` 上的 bit-matrix route:`tableC cols fits bits runC`], [`Tm`],
  [`Run/Lang/Gen`], [289], [`Dem Fn Pl Gv`;每个节点一个 `def`;row 的 wrapper;plan `p*`], [`Bits CRel*Def`],
  [`Run/Lang/Expand`], [885], [`useDef callDef once primE fitConst read walk fv mus number code node emit RegEntry Registry`], [`Gen Elab Parse`],
  [`Run/Lang/Plan`], [417], [给 `EmitC` 用的 kernel 调用 plan(`Ty`、`Val`)], [`Tm`],
  [`Rel/Lang/RelRep`], [162], [`prf pprf prfNode rep rel_rep`;检查每个 `Prim.sound`], [`Embed GenSpec`],
  [`Rel/Lang/TestRep`], [27], [对每个已注册的程序跑 `rep`], [`RelRep Test` +17],
)

== 3. Registry(`Expand.RegEntry`,一个 persistent env extension)

#table(columns: (auto, 1fr, 1fr),
  table.header[*条目*][*存什么*][*谁写 / 谁读*],
  [`.prog n ns opens`], [程序、它的 namespace 与 `open`,按定义顺序], [`define` / variant 的 scope、`resOf`、`homesOf`、`TestRep`],
  [`.chain n homes`], [`n` 的名字能到达的程序,按读入顺序], [`define` / `homesOf`、variant],
  [`.call key sig`], [在某个 `formKey` 上只建一次的常量的 `Sig`], [`emit` / `read` → `walk`、`callDef`],
  [`.ext e home`], [按常量索引的 `Ext`(const、arity、infix、obj、thm)], [`define` / `resolverAt`、`homesOf`],
  [`.rep n ds sh cs`], [编号后的 closed 定义;`code` 的常量,按值和按编号], [`emit` / `RelRep.rep`],
)

== 4. 核心数据类型

- `Pre`(已定型,对象是带元变量的 `OTy`):`tm res`;代数部分 `zero id top outl outr inl inr comp conv meet join
  diff dom ran ldiv rdiv pair prod junc lam E map est thin nil`;`prim r args s t`;`atPos own succ arith leq lt fold
  foldI flat lit`;`close p x a why`;`var p k a b tst`;`fix`;`refold`;`call p c us args ts alt a b d cv tst`
  (`alt` 是展开式,分析读它,`build` 不读)。
- `Tm : Obj → Obj → Bool → Type`(`d`:按 demand 运行):`Pre` 的代数部分加 `val uni juncD share var call arg nu
  mu`;`prim r : Tm A B true` 的关系参数由 `arg` 给。`Res := (A B : Obj) × (d : Bool) × Tm A B d`。
- `Sig`:`const demand vars conv tst kf`。`Once`:`key const gen params res tst kf`;`Sig` 由 `sigOf` 算出。
- `Prim`:`sym`、`sig`(由 `prim% c` 读出:常量、带 form 的关系参数、source、target)、`conv`、`written`、
  `prelude`、`aop`、`mono`、`sound`。`prims` 共 25 行。
- `Op`:`id zero top outl outr inl inr leq lt succ arith nil alpha prim dom ran lam E P est thin map refold
  index`;`Op.table` = 固定行 ++ 所有 `written && !prelude` 的 row。`Bin`:`meet join diff rdiv ldiv prod`。

== 5. 各阶段

*Expand*:
- `callDef`:每个参数取第一个能 build 的 form:closed、on demand、pair test;都不行就用展开式。
- `once`:先 whole,再 keyed(`kf`),再 pair test(`tst`);每个对象变量试 generic(`varObj` 占位 atom);
  `primsFit` 拒绝有 row 匹配不上的 build。
- `code` 给每个 closed 值一个常量;closed 的 `≫ ∩ − \` 走 bit plan。
- `primE`:在 `ofVals after elems testVals testAfter stepAfter` 中取第一个 `fitConst` 能套上的 wrapper
  (关系 binder 来自参数,其余用 `isDefEq` 解);`prfNode` 用同一方法套 `Sound` lemma。

*RelRep*:`prf`/`pprf`/`prfNode` 给出 `Gen.Sound (code t) T`,每个节点一个 `GenSpec` lemma,row 用 `Prim.sound`;
产出 `n.rep_x : (n.x).ok = true → rep (n.x).rel = T`;`n.unproved` 记下第一个没有 lemma 的节点。

== 6. 加一个 builtin

+ kernel `CRel.x : Vals A n → CRel A B` 或 `CRel K A → CRel K B`;其余 binder 是对象、size 或关系
  (`CRel X Y` 按 demand 运行,`CRel S S → CRel S T` 是 step,`S = T = B×B` 是 pair test)。
+ `prims` 里加一行 `{ sym := "x", sig := prim% CRel.x, … }`;`prelude := true` 让同名的 prelude 定义换成 kernel
  (`useDef`);`aop` 由 `Calc.builtins` 读。
+ 它的 `GenSpec` lemma 写进 `sound`;该名字未声明时 `RelRep` 的 `run_cmd` 让 build 失败。

`Op.table`、`Prim.inst`、`convTm`(经 `conv`)、`node`(经 `primE`)、`prfNode`(经 `sound`)都从这一行读。

仍是 constructor 的,以及代码里能看到的原因:
- `id outl outr top comp pair meet join diff`:`Shape` 用它们构造并识别 lifted row(`keyed`)。
- `dom ran lam E`:参数是 family 时由 `appliedL` lift;其它 builtin 拿到 family 时是 `notLiftable`。
- `succ arith leq lt`:带一个 universe `U : Tm .long .long false`,`prim%` 不读这种 binder。
- `nil`(`settleNil` 把它的 source 定为 `1`)、`alpha`(= `[nil, cons]`)、`refold`/`fix`(绑定变量)、
  `own`(`prelude.perm`,自身的 converse)。
- `est thin map`:代码里没有写原因。

== 7. 代码里的未决项

- `partial`:`Expand.fv mus number`(基于 `Tm.mapM`)、`Pre.at`、`Pre.nilSrcs`(基于 `Pre.traverse`)。
- 双胞胎:`Tm.cols`(`Array Col`,在 `Bits`)与 `Tm.colsL`(`List Col`,在 `BitsSpecRun`),由 `cols_toList` 连接。
- `.ext` 保留:它重述了 environment;删掉它净增 6 行,`Test.lean` 慢约 11%,未合并。
- 只有 `memRow` 设了 `sound`;其它 row 的节点都是缺口,由 `n.unproved` 报告。
- `useDef` 仍按常量名选择:`prelude` row 用 `prelude ++ x.sym`,另有 `prelude.perm`。

== 8. 与 qlean 的连接(`/home/dh/repo/qlean`,HEAD `88249ea`)

- `-K qlean=<dir>`:`leetq/lakefile.lean` 里 `require qlean from (get_config? qlean |>.getD "../../qlean")`,
  只决定 qlean 包的路径(默认是 freyd 旁边的 checkout;worktree 更深一层,所以要指定),不开任何功能。
- `LeetQRun`(`LeetQ.Run.*`)`precompileModules := true`,其共享库作为 plugin 在 qlean 的之后加载并用它的符号;
  target `rel-native-1a` 把 `relc-1a` 打印的 C 与 qlean 的 `libqleankernel.a`、`c/rt.c` 链接。

#table(columns: (auto, 1fr, 1fr),
  table.header[*leetq 模块*][*import 的 qlean 模块*][*用途*],
  [`Run/Core`], [`Value Dep.Val Dep.Monadic`、`Kernel.{Sort Search Structural Elementwise Scan}`、`Verify.{Encoding SymFind Alp}`], [`Arr t n := {v : QValue // v.WFAt t n}`、`El := Carrier`:关系的 key/val 列],
  [`Run/Code`], [`Kernel.{Sort Structural Reduce Elementwise Coc}`、`Verify.{Grade Chain}`], [`CRel` op 调用的 kernel],
  [`Lang/Syntax`], [`Kernel.Elementwise`], [`Ew.add mul …`:`plus times …` 的 verb 码],
  [`Lang/Plan`], [`Db.Own`], [native plan 的列文件],
  [`Rel/*` 证明], [`Verify.*`(`Raw Group Ids Gather …`)、`Eval.Val`、`Dep.Table`], [kernel 的 Lean 规格引理],
)
- `Parse Grammar Embed Tm Elab Expand Gen Bits` 不直接 import qlean;`Gen` 经 `CRel*Def` 用到它。
- qlean 独有:压缩列编码(`Enc`:bytes、bits、syms、FoR、ALP)、C kernel(`c/*.c`,Lean body 即规格)、
  `Verify` 证明、`Db.Own` 文件格式(内存布局即文件,mmap 读回)、`libqleankernel.a`。
