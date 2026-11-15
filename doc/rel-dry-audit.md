# Rel language 的 DRY 审计与 Freyd/AOP 依赖

范围:`leetq/LeetQ/Rel/Lang/*.lean`、`leetq/LeetQ/Rel/Programs/*.lean`,master @ 77ddb5c,只读分析。

- 路径一律相对 `/home/dh/repo/freyd/leetq/LeetQ/Rel/`;`Lang/` 下的文件省略前缀。
- 索引 `.lake/build/refactor-index.db` 对 Lang 是旧的:还有 `Lang.Eval`,没有 `Expand`/`Gen`/`BitsSpec*`,
  `S2_30 → AOP.A4_1` 这条边也是 rel-140d 之前的。Lang 部分的结论来自读源文件和 import 行,不来自索引。
- 判据(`doc/dry.md`):新东西做成已有概念的 instance;平行机制是错;看着像但因不同原因变化的不算重复。

## 1 重复

### 1.1 表

| #  | 副本(file:line)                                              | 它重复的 source                         | 做法                                  | 行数  | 风险 |
|----|----------------------------------------------------------------|-----------------------------------------|---------------------------------------|-------|------|
| 1  | `Parse.lean:150-446` 文本 grammar(`expr`…`program`)          | `Embed.lean:81-154` 的 Lean grammar     | 删;lexer helper 留下                 | ≈260  | 中   |
| 2  | `Embed.lean:335-365 defn`、`309-316 at(i)`                     | `Parse.lean:339-407 decl`、`240-246`    | 随 #1 只剩一份                        | ≈40   | 低   |
| 3  | `Parse.lean:411 after`、`433 scope`、`S.known/objs/taken`      | Lean 的 `import`/`open`/`namespace`     | 做成 Lean module 的 instance          | ≈40   | 中   |
| 4  | `Embed.lean:402-425 programOf`、`Chain`、`chainOf`、`scopeOf`  | Lean environment 里的常量               | 同 #3,按 `rel-module-design.md`      | ≈25   | 中   |
| 5  | `Embed.lean:455-477 elabRelVariant`(`from … upto`)            | 带参数的 module(设计 §2.1)            | module 落地后删                       | ≈25   | 中   |
| 6  | `Embed.lean:17-25 deriving ToExpr`(整个 AST)                  | 只为 #4 把 `Program` 存进常量           | 随 #4 删                              | ≈10   | 低   |
| 7  | `Elab.lean:267-316` `fresh/zonk/occurs/unify`                  | Lean elaborator 的 unifier              | 长期:类型交给 Lean(`Calc` 已这样)  | ≈50   | 高   |
| 8  | `Elab.lean:1006 inferSig`、`1029 mkDef`、`339-391 polarity`    | 同上(泛化、签名推断)                  | 随 #7                                 | ≈110  | 高   |
| 9  | 每个 builtin 的类型写四遍,见 1.2                              | CRel op 的 Lean 签名                    | 一张表生成其余三份                    | ≈350  | 中   |
| 10 | `Elab.lean:156-217 Pre` 与 `21-100 Tm` 同一 constructor 列表   | 彼此                                    | 一个 inductive,对象参数化            | ≈60   | 中   |
| 11 | `Bits.lean:28-35 TP` + `Gen.lean:109-118,232-245`              | `Tm` 的 `comp/meet/diff/ldiv` 四个结点  | `TP` 做成 `Tm` 的一个谓词             | ≈40   | 中   |
| 12 | `Elab.lean:434-478 keyed`                                      | `482-563 lComp/lThen/lPair/lProd/lDom`  | 构造和识别从一张 row 表出             | ≈45   | 中   |
| 13 | `Elab.lean:117-123 OTy.render`                                 | `Syntax.lean:186-191 OExp.render`       | 一个 render,另一个经转换调用         | 7     | 低   |
| 14 | `Expand.lean:45 arrText`                                       | `Syntax.lean:99-106 Tup.render`         | 调 `Tup.render`                       | 5     | 低   |
| 15 | `Syntax.lean:224-241 Expr.render`                              | 源文本(`FileMap` 里已有)              | 报错引用源区间,删 render             | ≈18   | 低   |
| 16 | `Calc.lean:95 prelude` 写死 `∈ ↦ ∋°`                           | `Programs/Prelude.lean` 的 `∈`          | 从 Prelude 的定义读                   | 3     | 低   |
| 17 | `Calc.lean:231-250 rEst/rThin/rPow` + `lift`                   | `Embed.lean:31-63 relTokenTable`        | 同一个 token 冲突只修一处             | ≈20   | 中   |
| 18 | `Expand.lean:31-39 preludeDef` 按名字 `"perm"` 分支            | `Tm`/声明本身                           | 按 constructor 判,不按字符串         | ≈9    | 低   |
| 19 | `SudokuPC.lean`、`SudokuPC9.lean` 共有 9 个 def                | 彼此                                    | 一个 `csp` module(设计 §2.1)        | ≈35   | 低   |
| 20 | `SudokuAC.lean` 的 `peer/AC3/s₀/s` + 9×9 `unit` 字面量         | `SudokuPC9.lean`                        | 同 #19                                | ≈20   | 低   |
| 21 | 每个 Programs 文件 `import Lang.Embed`                         | `Programs/Prelude.lean` 已 import       | 删这一行                              | 9     | 无   |
| 22 | `Bits.lean:258-262 orLeaf`                                     | 无使用者(原使用者 `Eval` 已删)        | 删                                    | 5     | 无   |
| 23 | `Syntax.lean:5`、`Bits.lean:41,227` 提到 evaluator / `ev`      | 已删的 `Lang/Eval.lean`                 | 改注释                                | 3     | 无   |
| 24 | `Bits.lean:239-246 run`(只被 `runC` 的 check 模式用)         | `Gen` 的同一 op                         | 并进 `runC`                           | 8     | 低   |

### 1.2 #9 的展开:一个 builtin 的知识落在哪些地方

以 `cons` 为例,新增一个 builtin 现在要改下面每一处:

| 位置                                      | 写的是什么                         |
|-------------------------------------------|------------------------------------|
| `Syntax.lean:43-69 Op`、`Op.table`        | 名字和 arity                       |
| `Elab.lean:581-617 constant`              | 类型,用 `OTy` 写                  |
| `Elab.lean:156-217 Pre`                   | constructor                        |
| `Elab.lean:21-100 Tm`                     | constructor,类型写在 index 里     |
| `Elab.lean:1276-1427 build`               | `Pre → Tm` 的一支                  |
| `Elab.lean:1088-1157 convTm`              | converse 规则(`cons° = uncons`)  |
| `Gen.lean:85-228`                         | `Gen.cons`,类型写在 `Fn` 里       |
| `Expand.lean:283-408 node`、`201-235 fv`  | `Tm → Gen.*` 的一支                |
| `CRel*.lean`                              | `CRel.cons` 的 Lean 签名           |
| `Calc.lean:161-212 toTerm`、`89-91`       | 到 AOP 记号的一支                  |

- 类型出现四次:`constant` 的 `OTy`、`Tm` 的 index、`Gen.Fn`、`CRel.cons` 的签名。只有最后一个被 Lean 检查到底。
- `Gen.lean` 里大多数 def 是 `fun D => CRel.x D.val`,是 `CRel.x` 的转发,不带新知识。
- 做法:`Tm` 的 constructor 直接带它的 `Gen`/`CRel` 常量名;`constant` 的类型从该常量的 Lean 类型读出;
  `node` 变成一行通用规则。新增 builtin 时只加一行。

### 1.3 类别 (c):kernel 与 primitive 之间有没有 law

- 有 law 的(不算重复,是带证明的实现):`rep_dom`、`rep_ran`(`RepOps`,等式形如
  `rep (dom R) = 𝟙 ∩ rep R ≫ (rep R)°`)、`rep_E`(`RepE`)、`rep_est`/`rep_thin`(`RepEst`、`CRelEst`)、
  `rep_setify`(`RepPower`)、`rep_perm`/`rep_map`(`CRelFold`)、`rep_uncons`/`rep_unsnoc`/`rep_uncat`(`CRelList`)。
- `convTm` 的 `cons° = uncons`、`snoc° = unsnoc`、`cat° = uncat`:law 只有逐点形式(`xs = b :: bs`),
  没有一条 `rep (uncons X) = (rep (cons …))°`。`convTm` 的重写规则没有被任何定理引用。
- `Gen.lean` 里没有 primitive 的复合规则,Lang 里看不到对应的 law:
  `comp` 的空 `R` 短路(`103-106`)、`E/map`(`139-142`)、`thin`(`147-150`)、`onKeys`(`175`)、
  `foldI`(`191-201`)、`flat`(`204-207`)、`nu/nuAC/mu`(`210-228`)。`BitsSpec*` 只覆盖 `Bits`。
- `Elab.lean:686` 把 `E` lift 成 `Λ(∋R)`,同时 `Alg.E` 有自己的 kernel:两条路,由 `rep_E` 连接,不用动。
- `Programs/Prelude.lean` 用语言自己定义了 `tails tail suffix subseq perm ordered sort`,而 `CRel` 里还有同名
  kernel(`tails tail subseq perm ordered sortSet`)。读 `Gen.lean` 时没看到它引用这些 kernel 的全部;索引过旧,
  这一条需要在索引重建后用 `dep` 核实再删。

### 1.4 看着像、但不是重复

| 一对                                             | 为什么不是                                                        |
|--------------------------------------------------|-------------------------------------------------------------------|
| `Calc.toTerm` 与 `Expand.node`                   | 一个到 AOP 的 spec 项,一个到可执行的 `Gen`;目标不同             |
| `BitsSpec.lean` 的 `TP.den` 与 `Rep.rep`         | `den` 是证明用的指称,`bits_table` 把两者连起来                   |
| `CRel.*` 与 `Alg.*C`                             | `CRel` 多带 `ok` 位并串接它                                       |
| `Expand.lean:250 hex` 与 `Gen.lean:58 unhex`     | 编码和解码,一对                                                  |
| `Expand.lean:50-82 showEl/cmpEl/showRel`         | 按程序里的元素名打印,Lean 的 `Repr` 不知道这些名字               |
| `Embed` 的 token 表与 `Parse` 的 lexer helper    | 分词规则只有一份,`Embed` 调它                                    |
| `AC3Def.lean` 与 `AC3.lean`                      | def 与证明的拆分,正是 2.4 要推广的做法                           |
| `Knapsack`/`Mss`/`Blocks`/`JobShop` 的局部 def   | 没看到跨文件的副本                                                |

## 2 对 Freyd/ 和 AOP/ 的依赖

### 2.1 结论

- run path(`Syntax`、`Parse`、`Elab`、`Bits`、`Gen`、`Expand`、`Embed`、`Programs/*` 和生成的代码)不使用任何
  `Freyd.*`/`AOP.*` 常量:索引里 Lang、Programs、`Alg`、`Code`、`Core`、`AC3Def` 到 Freyd/AOP 的 `dep` 行数为 0;
  `CRel.*` 的 def 只依赖 `Alg`(67 个常量)、`Core`(9 个)和其它 `CRel` def。
- run path 仍然 import 了 59 个 Freyd/AOP module,原因只有一个:`Gen.lean` import `CRelEst`,而每个 `CRel*.lean`
  把运行用的 def 和 `rep_*` 定理放在同一个文件里,定理要 `Rep` → `AOP.A6_1_RelSet`。
- 直接 import Freyd/AOP 的 leetq 文件只有三个:`Rep.lean`(`AOP.A6_1_RelSet`)、`Lang/Calc.lean`、
  `Lang/CalcTest.lean`。
- 122 个 `LeetQ` module 里 88 个不使用任何 Freyd/AOP 常量。

### 2.2 import cone

| 起点                         | Freyd | AOP | `Rep*` | `KernelWF` | QLean |
|------------------------------|-------|-----|--------|------------|-------|
| `CRelEst`(`Gen` 现在的入口) | 44    | 15  | 23     | 49         | 31    |
| `Algebra`(run path 的最小)  | 0     | 0   | 0      | 3          | 22    |
| `Lang/Calc.lean`             | 44    | 20  | —      | —          | —     |

- run path 的最小集合:Lang 七个文件 + `Alg`/`Code`/`Core` + `CRel` 的 def + `AC3Def` + QLean。
- 索引总数:Freyd 232 个 module,AOP 107 个。

### 2.3 每个依赖

| module                 | 用到的常量                                                  | 用途        | 使用者     | cone | 做法                       |
|------------------------|-------------------------------------------------------------|-------------|------------|------|----------------------------|
| `Freyd.S1_10`(31 行)  | `Cat.Hom`、`comp`、`id`                                     | 类型        | 32 module  | 1    | 留                         |
| `Freyd.S1_41`(135 行) | 无直接使用,`S2_10` import 它                               | —           | —          | 1    | 留                         |
| `Freyd.S2_10`(1214)   | `Allegory.inter/recip/toCat/le/le_antisymm/le_trans`        | 类型 + 证明 | 19         | 3    | 留                         |
| `Freyd.S2_20`(1532)   | `DistributiveAllegory.union/zero`、`Coproduct`、`u₁`、`u₂`  | 类型 + 证明 | 17         | 4    | 留                         |
| `Freyd.S2_22`(2182)   | `UnionAllegory.toAllegory`、`…_isUnionAllegory`             | 证明        | 2          | ≈6   | 留                         |
| `AOP.A6_1_RelSet`      | 94 个声明里的 18 个,见下                                   | 类型 + 证明 | 34         | 59   | 拆出只 import `S2_20` 的底 |
| `AOP.A5_3`(511)       | `Freyd.Alg.junc`                                            | 证明        | 5          | 49   | 把 `junc` 挪到 Freyd       |
| `AOP.A4_*`…`A8_1`      | `Calc.toTerm` 引用的记号,见下                              | spec 项     | `Calc` 2   | 64   | 留,保持隔离               |

- `AOP.A6_1_RelSet` 用到的 18 个:`RelSet`、`carrier`、`mk`、`instCat`、`instAllegory`、
  `instDistributiveAllegory`、`comp_apply`、`inter_apply`、`recip_apply`、`union_apply`、`hom_ext`、`le_iff`、
  `corefl`、`graph`、`rpair`、`rprodMap`、`relTop`、`sumCop`。它们只依赖 `S1_10`、`S2_10`、`S2_20`。
  cone 是 59 而不是 5,是因为该文件 import `AOP.A6_2`(→ `A5_5`、`S2_41b`、`CalcSteps`)给另外 76 个声明用。
- `junc` 只依赖 `S1_10`、`S2_10`、`S2_20`、`S2_22`;使用者是 `CRelArith`、`CRelList`、`KernelWF.RazeFoR`、
  `RepOps`、`RepPerm`。
- `Calc` 引用:`RelProd`、`Coproduct`、`InitialAlgebra`、`relCata`、`PowerAllegory.eps`、`Λ`、`existsImage`、
  `powerRel`、`est`、`thinRel`、`singletonMap`、`DivisionAllegory.div`、`leftDiv`、`prodMap`、`junc`、`dom`、
  `ran`、`Relator`、`BooleanAllegory`、`topHom`、`topMor`。只有 `CalcTest` import `Calc`。
  这是语言到 AOP 的对应,本来就要 AOP。
- rel-140b 已把 `modular_le_right` 挪进 `Freyd/S2_10`;rel-140d 让 `S2_30` 只 import `Freyd.S2_20`。
  下面 2.4 的两步是同一方向的继续。
- 不建议把 `RelSet` 或 `junc` 抄进 leetq:那是第二个 `RelSet`,正是 DRY 规则禁止的。

### 2.4 两步拆分

1. `CRel*.lean` 拆成 def module 和证明 module(先例:`AC3Def.lean`/`AC3.lean`)。
   - 9 个文件共 ≈82 个 def、≈179 个定理;def 只依赖 `Alg`/`Core`,移动时不改内容。
   - `Gen.lean` 改 import def module。之后 run path 的 cone:Freyd 0、AOP 0、`Rep*` 0。
   - precompiled 的 run path 不再需要链接 `libfreyd_Freyd`(rel-140d 为此加的)。
2. `AOP/A6_1_RelSet.lean` 拆出一个只 import `Freyd.S2_20` 的底(那 18 个声明),`junc` 挪到 `Freyd/S2_22`。
   - `Rep.lean` 改 import 这个底。证明 path 的 Freyd/AOP cone:59 → ≈7。

## 3 排序后的计划

| 序 | 做什么                                         | 收益                                            | 代价                          | 待定 |
|----|------------------------------------------------|-------------------------------------------------|-------------------------------|------|
| 1  | `CRel*` 拆 def / 证明(2.4 第 1 步)           | run path 少 import 59 Freyd/AOP + 23 `Rep*`     | 移动 ≈82 个 def,改 import    | A    |
| 2  | `A6_1_RelSet` 拆底、`junc` 挪走(第 2 步)     | 证明 path 的 cone 59 → ≈7                       | 两次 `lean-refactor` 移动     | B    |
| 3  | 小清理 #13 #14 #16 #18 #21–#24                 | ≈50 行                                          | 一个 agent,无设计            | —    |
| 4  | 删文本 grammar(#1 #2)                        | ≈300 行,错误信息只剩一份                       | `Test.lean` 改用 `rel_program` | C    |
| 5  | module 系统落地(#3–#6 #19 #20)               | ≈155 行,Sudoku 三份合一                        | 实现 `rel-module-design.md`   | D    |
| 6  | 一张 operator 表(#9–#12)                     | ≈450 行;新增 builtin 改一处                    | 重写 `Elab`/`Gen`/`Expand` 的骨架 | E |
| 7  | 类型检查交给 Lean(#7 #8)                     | ≈160 行,少一个 unifier                         | 重写 `elabE`,报错文本会变    | F    |

- 第 4–7 项都碰 ffreyd 正在改的 `Lang/Expand.lean` 一带;第 1–3 项不碰,可以现在做。
- 第 6 项和第 7 项互相影响:若类型交给 Lean,`constant` 那份 `OTy` 类型表直接消失,第 6 项变小。

### 待定

- A — def module 怎么分
  - A:每个文件一个 `*Def`(`CRelEstDef.lean` …),和 `AC3Def` 同形,证明文件名不变。
  - B:九个文件的 def 合进一个 `CRelDef.lean`(≈82 个 def)。
- B — `RelSet` 的底放哪
  - C:留在 AOP,新 module(如 `AOP/A6_1_RelSetBase.lean`),只 import `Freyd.S2_20`。
  - D:挪进 `Freyd/`。它不是书里的节,和 `Sa_bc.lean` 的规则不合。
- C — 文本 parser
  - E:删 grammar 那一半,`Prelude.lean:45-58` 的 `typesOf` 和 `Test.lean` 改走 `Embed`。
  - F:留着,给 Lean 之外读 `.rel` 文本文件用。此时 #1 是有意的第二个入口,应让 `Embed` 调它而不是重写。
- D — module 系统
  - G:现在按 `rel-module-design.md` 做,第一个使用者是 Sudoku 的 `csp`。
  - H:等 stage 3(rel-143)合进 master 之后再做。
- E — operator 表的形式
  - I:`Tm` 的 constructor 带 `Gen`/`CRel` 常量名,类型从 Lean 读。
  - J:Lean 里一张 `Op` 属性表,由 macro 生成 `Pre`/`Tm`/`Gen`/`node`。
- F — unifier
  - K:暂缓,等 E 做完再看还剩多少。
  - L:现在就把对象变量换成 Lean 的 metavariable。
