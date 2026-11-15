# Rel native：把 rel_program 编译成不依赖 Lean runtime 的 exe —— 设计与计划

状态：只有设计，没有任何代码。数字来自 `.lake/build/refactor-index.db`（`dep` 表、`decl_range`）、`nm -u`、`wc -l`
和源码。索引里 run path 的 module 名还是搬家前的 `LeetQ.Rel.*`，声明名和行号与 `Run/` 下的文件一致。

路径约定（master `ab83fdd` 起 run path 单独成库）：

| 前缀     | 相对于                                    | 内容                                                        |
|----------|-------------------------------------------|-------------------------------------------------------------|
| `Run/…`  | `/home/dh/repo/freyd/leetq/LeetQ/Run/`    | 运行时：`Core` `Code` `Alg` `CRel*Def` `AC3Def` `ValEq` `KernelWF/` `Lang/{Syntax,Parse,Elab,Embed,Expand,Gen,Bits}`；唯一 precompile 的库 |
| `Rel/…`  | `/home/dh/repo/freyd/leetq/LeetQ/Rel/`    | 证明和程序：`Rep*` `CRel*` `Lang/{GenSpec,BitsSpec*,Calc}` `Programs/`；解释执行 |
| `c/…`、`QLean/…` | `/home/dh/repo/qlean/`            | qlean 的 C kernel 和 Lean 分派层                            |

## 1. 已定的和结论

已定（2026-11-15）：

| 项     | 决定                                                                                              |
|--------|---------------------------------------------------------------------------------------------------|
| 路线 B | plan 的一步是一个 `@[extern]` kernel；Lean runtime 用 `rt.c` 去掉（第 3、4 节）                   |
| 输入 G | 语言加输入声明，外加通用 IO：qlean column 目录（mmap）、csv、txt；reader 是 C，不是关系算子；输出对称（第 11 节） |
| 旧定义 S→H | `Alg`/`Code` 的正文不动；一个 Lean 元程序遍历每个 def 的 `Expr` 生成 plan（"记录指令"实例）；"记录再执行 = 立即执行"是每个 def 的翻译检查，不是每个 kernel 一条定理（第 14 节） |
| 输入 P | 带 `input` 的 program 在 elaboration 时不读文件；`check`/`print` 只在 exe 和 `n.run` 里跑（第 14 节） |

- 输入声明改掉了先前的规则 "Rel program 是封闭的文本"：program 的定义仍然只有关系，但它的值从此依赖启动时读进来的文件。
- 修正（他的原话："if you make each relation concrete, it's memory explod fast. we have many trick to avoid
  that."）：上一版把 plan 写成一串直线的 kernel 调用，等于把每个子项都做成表。plan 的真实形状是第 6 节：带
  demand 参数的函数、循环、运行时选的分支。ffreyd 审计出的每一条不物化的手法都保留（第 5 节）。
- 8 种运行时 closure 全部能在 emit 时消掉，没有一种需要运行时 closure 或 interpreter（第 7 节）。
- qlean 的 C 这一侧便宜：已编译的 kernel object 只缺 16 个 Lean runtime 符号，一个 `rt.c` 补齐，kernel 源码不改。
- 工作量在 `Alg`/`Code` 的 builder（约 4170 行运行时 Lean），不在 `Gen`（257 行）。
- "it can use Lean to prove" 今天只对 22 种节点成立（第 10 节）；这和 native 无关，计划里单列一个阶段。

## 2. 现状：一个定义怎样变成代码

一条路径：`segment : [α] ⟶ [α] ≜ tails ∋ inits ∋` → `Tm` → `Gen.comp … (Gen.mem …)` 的 `Lean.Expr` → 常量
`mss.rel.segment : CRel _ _` → `addAndCompile` → Lean 编出的 native code → `CRel.*` → `Alg.*C` → qlean `@[extern]`。

| 层                   | 文件                                                   | 内容                                        | 规模       |
|----------------------|---------------------------------------------------     |---------------------------------------      |------------|
| core term `Tm A B d` | `Run/Lang/Elab.lean`                                   | 带类型的 first-order 项，`d` 是 demand 标志 | 1514 行    |
| `Expand.code`/`node` | `Run/Lang/Expand.lean`                                 | `Tm` → `Gen.*` 的应用                       | 783 行     |
| `Gen.*`              | `Run/Lang/Gen.lean`                                    | 每个 `Tm` constructor 一个函数              | 257 行     |
| `CRel.*` / `Alg.*C`  | `Run/{Alg,Code,Core,AC3Def}.lean`、`Run/CRel*Def.lean` | 关系运算，对 `Obj` 递归，带 ok bit          | 3919 行    |
| bit-matrix           | `Run/Lang/Bits.lean`                                   | 闭的 `≫`/`∩`/`∪`/`−`/`\`/`°` 的 route `Route`    | 250 行     |
| qlean Lean 分派      | `QLean/Kernel/*.lean`、`QLean/Dep`                     | `Enc` 各 payload 上的 match                 | —          |
| qlean C              | `c/*.c`、`c/*.h`                                       | 266 个 `LEAN_EXPORT`                        | 21024 行   |

- `Gen.Fn d A B := Dem d A → CRel A B`（`Run/Lang/Gen.lean:45`）：一个项的代码是 Lean 函数。`Dem true A = Rel A A`
  （它读的 key，一个 coreflexive），`Dem false A = Unit`（闭项）。
- 闭子项各成一个常量 `n.c.c<i>`，结构相同的共用一个（`Expand.share`，`:429`）；常量由 `Expand.addConst`（`:373`）经
  `addAndCompile`（`:376`）加入并编译。
- 循环都是 Lean 循环，全部落到 `Alg.hylo`（`Run/Alg.lean:506`，well-founded recursion）：`iter`（`:514`）、`fixOn`
  （`:521`）、`foldRound`/`foldRowsC`/`foldByC`（`:677`–`:720`）、`iterC`/`fixOnC`（`:946`/`:952`）、`loopOnC`
  （`:1397`）、`acFixC`（`Run/AC3Def.lean:57`）。除 `hylo` 和对 `Obj`/`Route` 的结构递归外，run path 没有别的递归。
- 证明：`Expand.prf`/`prfNode`（`:612`）按节点拼 `Gen.Sound`；拼不出的定义进 `n.unproved`。
- 文字量只重建 `bytes`/`bits` 两种 payload（`Expand.atomE`，`:390`）。
- 最小程序的依赖锥（`dep.in_value` 的传递闭包，只数 `LeetQ.*` 的 `def`；qlean 的声明不在这个索引里）：

| 起点                                          | LeetQ 的 def |
|-----------------------------------------------|--------------|
| `Alg.unionC`                                  | 85           |
| `Alg.compC`                                   | 88           |
| `Gen.join` + `Gen.val`（`{…} ∪ {…}`）         | 98           |
| `Gen.comp` + `Gen.arith` + `Gen.val`（只走 table） | 108     |
| `Bits.runC`                                   | 155          |
| `Gen.compB` + `Gen.arith` + `Gen.val`（`{…} plus` 实际 elaborate 出来的） | 173 |

- 闭的 `R S` 由 `Expand.node`（`:475`）选 `Gen.compB`，不是 `Gen.comp`：最小的带复合的程序已经走 `Route`，
  比只数 `Alg.plus` 的旧数字（93）大出 bit 路径的 65 个 def。
- 任何带一个算子的程序都带上 `Code`（grade、groupIds、find、`codesC`、`razeC`）：约 85 个 def 的底座。

## 3. qlean 的 C kernel 依赖 Lean runtime 吗

依赖，但面很窄，而且不用剥。

- 每个 entry 的参数和结果是 Lean 对象：`ByteArray`（`lean_sarray_cptr`/`_size` 出现 751 次，`lean_alloc_sarray`
  192 次）、对象数组（symbol 的 `offs`，76 次 `lean_array_cptr`）、`Prod`/`Option` constructor（29 次）。
- 这些 `lean_*` 几乎全是 `lean.h` 里的 `static inline`。`nm -u /home/dh/repo/qlean/.lake/build/c/*.o`
  里未定义的 Lean 符号只有 16 个：

| 符号                                                              | 用处                     | `rt.c` 里的实现       |
|-------------------------------------------------------------------|--------------------------|-----------------------|
| `lean_alloc_object`、`mi_malloc_small`                            | 所有分配                 | `malloc`              |
| `lean_dec_ref_cold`                                               | 引用计数归零             | `free`                |
| `lean_internal_panic_out_of_memory`、`lean_notify_assert`         | 失败路径                 | 打印后 `abort`        |
| `lean_inc_heartbeat`                                              | 计数                     | 空函数                |
| `lean_copy_byte_array`                                            | 非独占时复制             | `malloc` + `memcpy`   |
| `lean_big_usize_to_nat`                                           | 超过 2⁶³ 的 `USize`      | `abort`               |
| `lean_mk_string`、`lean_mk_io_user_error`、`lean_decode_io_error` | `own.c` 的 IO 错误       | errno 后 `exit(1)`   |
| `lean_apply_1`、`lean_apply_2`、`lean_apply_5`                    | 回调 Lean（见下）        | `abort`               |
| `lean_register_external_class`、`lean_mark_persistent`、`lean_mark_mt` | `search.c` 的 index cell | `abort`           |

- 做法：C 这边继续 `#include <lean/lean.h>`（只当头文件用，exe 里没有一行 Lean 库代码），加一个约 150 行的
  `rt.c` 定义上表符号，链接现成的 `libqleankernel.a` 里的 `coc`/`elementwise*`/`reduce`/`scan`/`search`/`sort`/
  `structural`/`own`，去掉 `handle`（IPC）、`interp`、`env`、`time`、`zip`。21024 行 kernel 一行不改。
- 回调 Lean 的只有两处：`qlean_stop`（`c/env.c:23`，`need` 失败时求消息 thunk）和带属性向量的 index cell
  （`search.c:2137–2193`）。前者在 plan 里是 `fail` 指令，不链接 `env.c`；后者 C 路径走不到（列一律不带属性），
  走到就是 `abort` 加一句话，不是静默错。
- 之后若要连 `lean.h` 也不要：写一个同名、同布局的小头文件替换它（`own.c` 的 mmap 依赖 `lean_sarray_object`
  头部 24 字节的布局）。没有第二个用户之前不做。

## 4. 路线：B（已定）

| 路线 | plan 的一步             | 结果                                                                              |
|------|-------------------------|-----------------------------------------------------------------------------------|
| B    | 一个 `@[extern]` kernel | 采用。Lean 之外写 `Alg`/`Code` 的 builder、`rt.c`、emitter；信任 emitter、`rt.c`、kernel ABI 表 |
| A    | 没有 plan，`lean_exe` 静态链接 | 否决：exe 里有 leanrt，不满足 "do not depend on Lean runtime"               |
| C    | 一个 `Tm` 算子一份手写 C | 否决：是 `Alg` 的第二份拷贝，证明边界退到 `Tm`                                    |

- 上一版的 "阶段 0：A 当对照基准" 随 A 一起删掉。对照基准是 Lean 这一侧今天的求值（`n.prints`、`n.ok`）和
  `Plan.run`，不需要另编一个 `lean_exe`。

## 5. 不物化的手法，和它们在 plan 里的去向

来源：ffreyd 的审计 `/data/tmp/rel-nonmaterialise.md`（锚点在那里，这里不重抄）。一条手法落在三处之一：

| 去向             | 含义                                                                                         |
|------------------|----------------------------------------------------------------------------------------------|
| elab 改写        | 在 `Tm` 造出来之前就做完了。plan 从改写后的 `Tm` 造，所以自动保留，builder 不用知道          |
| emit 时静态      | 取决于 `Tm` 的形状，emitter 读得到；在 C 里表现为"生成了哪些函数、哪条分支"                 |
| 运行时           | 取决于数据；builder 必须照 `Gen`/`Alg` 的写法逐条重现，是 plan 里的 `if`、`loop`、demand 参数 |

elab 改写（自动保留）：

| 手法                                                   | 位置（`Run/Lang/`）                    |
|--------------------------------------------------------|----------------------------------------|
| `∼R` 改写成 `⊤ − R`，没有自己的 `Tm` constructor       | `Elab:829`–`:832`、`:520`              |
| `⊤` 造不出（没有 universe）时，它的 pair test 是 `𝟙`   | `Elab:1469`                            |
| `−`/`∩` 有一侧造不出：融成 `⟨𝟙,S⟩τ(R)π₂`，那一侧只在另一侧的 pair 上测 | `Elab:1322`–`:1336`、`:1178`、`:1463` |
| 除法当 test：`τ(R/S)`、`τ(R\S)` 是 demand pair 上的 coreflexive | `Elab:1182`、`:1486`–`:1498`  |
| converse 推到叶子：`(RS)°=S°R°`、`⟨R,S⟩°`、`cons°=uncons`、`R°°=R` | `Elab:1103`、`:1312`–`:1320` |
| `R×S` 不闭时成 `⟨π₁R,π₂S⟩`；闭化是 `U ≫ t`；family 按 key 提升 | `Elab:1353`–`:1361`、`:1278`、`:465` |
| 序 `Q` 造成 pair test `τ(Q)`（`est`/`thin`/`thinL`/`merge` 的参数） | `Elab:1505`              |
| `ν` 的起点                                             | `Elab:403`、`:865`–`:880`              |
| demand 标志 `d` 本身；`⊤` 只存目标 coreflexive `V`     | `Elab:21`、`:27`                       |

emit 时静态（`Expand` 选的节点，emitter 照着生成）：

| 手法                                         | 位置                          | 在 C 里                                             |
|----------------------------------------------|-------------------------------|-----------------------------------------------------|
| 闭子项共享成常量                             | `Expand:310`、`:418`、`:429`  | 一个 global，启动后算一次                           |
| 闭的 `≫ ∩ − \` 选 bit 节点，route 的形状      | `Expand:437`、`:475`          | 一个 plan root 两条分支的代码（第 6 节）            |
| AC-3 形状的识别（`nuAC`）                    | `Expand:349`、`:356`          | delta 循环，arc 的列表在 emit 时展开                |
| converse 是视图（`convArr`，字段互换）       | `Run/Alg.lean:93`             | 寄存器改名，不产生一行 C                            |
| `𝟙` 返回 demand 本身，universe 上 key、val 同列 | `Run/Alg.lean:85`          | 寄存器别名                                          |
| 右除是 `(S°\R°)°`                            | `Run/Alg.lean:247`            | 两次改名加一次左除                                  |

运行时（builder 逐条重现）：

| 手法                                                       | 位置                                  | plan 里                                    |
|------------------------------------------------------------|---------------------------------------|--------------------------------------------|
| `R S`：`S` 只在 `ran R` 上跑，`R` 空就不跑                 | `Gen:111`                             | `if n == 0`；`S` 的函数吃 `ran R` 当 demand |
| `⊤`：demand 的 key 和 `V` 做 cross                         | `Gen:97`、`Alg:80`                    | demand 参数                                |
| `−`：joint pair code 上的 anti-join，不展开操作数          | `Alg:167`、`Code:989`                 | kernel 调用                                |
| bit matrix 还是 table                                      | `Bits:215`、`:241`                    | `if`（第 6 节）                            |
| route 里 `≫`/`\` 的左叶读成排好序的 code pair，不建矩阵     | `Bits:200`                            | bit 分支里的 kernel 调用                   |
| 左除：bit 路径是行的 ∧；table 路径是 join 加计数比较；空真部分只在 `anti(Ub, ran R) × Uc` 上 | `Bits:168`、`Alg:230`、`:216` | 两条分支各自的 kernel 调用 |
| `Λ`：每个 cell 是同一个扁平 payload 里的 lo/hi 切片        | `Alg:313`、`Core:440`                 | `arr` 的寄存器是 `lo`、`hi`、payload       |
| `∋`：只展开 demand 里的 array                              | `Gen:98`、`Alg:333`、`Code:85`        | demand 参数                                |
| `est`/`thin`/`thinL`/`merge`：`τ(Q)` 只在一个 key 的 `⟨G,G⟩` 上跑 | `Gen:153`–`:178`、`Alg:538`–`:578`、`:1280` | 调用生成的 test 函数            |
| `E`/`map`：`R` 在 `ran(∋ D)` 上跑                          | `Gen:147`、`:149`                     | demand 参数                                |
| fold/`foldI`/`loop`：step 只在本轮遇到的 pair 上跑，没有就跳过 | `Gen:183`–`:207`、`Alg:677`–`:737` | `loop` 里 `if n == 0`，调用 step 函数      |
| AC-3：除法只在 `ran(Δ A)` 的行上；`Δ′ = dom(X − X′)`       | `Run/AC3Def.lean:37`–`:57`            | `loop`，状态是 `(X, Δ)`                    |
| `Code` 按 lane 宽度（1…64 bit）打包                        | `Code:106`、`:156`–`:201`             | 宽度是一个 size 寄存器，传给 kernel        |
| `need`/`guard`：容量守卫                                   | `Code:120`、`Alg:60`、`Run/CRelDef.lean:26` | `fail`、`if`                         |

现有的限制（不是 backend 的问题，plan 照样继承）：

- 通用的 `ν`/`μ` 不是 semi-naive：每轮 `X ↦ nub(φ X)` 整个重算，直到行数不变（`Gen:218`、`:234`、
  `Alg:952`）。唯一的 Δ 是 AC-3 的 `acDeltaC`。
- range 定义的 universe 不保留成 range：`objInfo`（`Expand:21`）把它物化成一列 long。
- 对称除法 `symDivC`（`Alg:279`）没有 `Tm` constructor，语言里用不到。
- `Enc` 没有 range 或 constant constructor；今天 Rel 的列只从 `bytes`/`bits` 的文字量来。kernel 会不会从稠密输入
  产出 foR/enum，没有查。

## 6. Plan 的形状

不是一串直线的 kernel 调用。是一组 first-order 函数：

```
Plan   := globals : (名字, Block)*          -- 闭节点，按依赖序各算一次
          funs    : Fun*                    -- 非闭节点、test、step、fixed point 的 body
          main    : Block                   -- 读输入、算 global、写输出、按 ok 退出
Fun    := 名字, 参数寄存器, 结果寄存器 + ok bit, Block
Block  := Instr*
Instr  := r… = call sym(args)               -- 一个 extern kernel
        | r… = apply f(args)                -- 直接调用一个生成的 Fun
        | r… = lit bytes | r… = global g
        | r… = if c then Block else Block   -- 两支给出同一组结果寄存器
        | r… = loop init bound done Block   -- 状态寄存器组、轮数上限、结束条件、一轮的 body
        | fail fmt args                     -- need 的失败支：打印后 exit 1
        | r… = host f(args)                 -- 只在迁移期：还没写成 builder 的 Lean 函数
```

一个例子，`R S`（`Gen.comp`，`d = true`）在 `D` 上：

```
Lean   fun D => let r := R D; if r.rel.n == 0 then ⟨zero, r.ok⟩ else
         let k := CRel.ran r; also k.ok (CRel.comp r (S (Dem.of e k.rel)))
plan   fun f7(D) =
         r, ok1 = apply f3(D)                    -- R 在 D 上
         if r.n == 0 then (empty, ok1) else
           k, ok2 = <ranC 的 kernel 序列>(r)
           s, ok3 = apply f5(k)                  -- S 只在 ran(R) 上
           c, ok4 = <compC 的 kernel 序列>(r, s)
           (c, ok1 && ok2 && ok3 && ok4)
```

- 寄存器三种：buffer（`ByteArray`）、size（`USize`）、bit（`Bool`）。
- demand 参数：`Dem true A = Rel A A` 是 coreflexive，所以是 `A` 摊平后的一组列寄存器加行数；`d = false` 的函数
  没有这个参数。`d` 在 elab 时定死，所以每个 `Fun` 的签名是静态的。
- 被捕获的值是数据，不是函数：外层 `μ`/`ν` 的 `X`、program 的输入、常量的参数。它们成为 `Fun` 的额外参数
  （lambda lifting）。
- `Obj` 是静态的：`Vals A n` 在建 plan 时摊平成寄存器元组（`prod` 两列；`arr` 是 `lo`、`hi`、payload；`sum` 是
  `tag`、`idx` 和两支），`Vals.pick`、`Obj.razeC`、`codesC` 这类对 `Obj` 的递归在建 plan 时跑完，C 里看不到 `Obj`。
- 运行时选的分支，全部是 `if`：demand 为空就不跑（`comp`、`onKeys`）；`guard` 看输入的 ok bit；`need` 的容量条件；
  bit matrix 还是 table；`loop` 的结束条件。
- bit-matrix route（`Route`，原名 `TP`；"plan" 只指 native 的 `Plan`）：树的形状由 `Gen.pleaf`/`pcomp`/… 的静态表达式决定，emitter 读得到，所以运行时没有
  `Route` 这个值。每个 route root 生成：
  - 叶子各算一次（`apply`），两条分支共用；
  - 条件 `codeAll` 成功 `&&` `Route.fits`（每个节点的矩阵 ≤ 2²⁷ bit）`&&` `capsOK`，是 size 寄存器上的静态公式；
  - then 支：每个节点一个 bit kernel，根上转成 table（`Bits.table`）；左叶走 `Route.pairs`，不建矩阵；
  - else 支：`Route.tableC`，也就是普通的 `compC`/`interC`/… 序列。
  - 代价：每个 route root 两份代码。`LEETQ_CHECK` 的两路对比模式不进 C（那道门在 exe 外面做，第 13 节）。
- `loop`：`hylo`/`iter`/`iterC`/`fixOn`/`fixOnC` 这一串的 done 和 step 在每个调用点都是源码里写死的 lambda，
  builder 把它们合成一条 `loop`。上限是 `Nat`，C 里用饱和乘法（`μ` 的 `|UA|·|UB|+1`）。
- 调用图没有环：`apply` 的方向跟着 `Tm` 树走，Rel 没有递归定义（迭代只有 `μ`/`ν` 和 fold，都是 `loop`）。
  所以 C 里只有直接调用，没有函数指针；`Plan.run` 对 plan 的结构递归，`loop` 的上限当 fuel。
- 参数化的常量（module 设计 2.4：`csp.AC3 : (α β : Obj) → … → Pl … → Pl …`）：它的值改成 plan builder，一个
  `Obj` 和实参 builder 的 Lean 函数。调用叶子在建 plan 时调它，每个调用点得到按具体 `Obj` 展开的函数，
  结构相同的共用。Lean 只 elaborate 一次；C 里是每个 instantiation 一份代码。
- Lean backend：`Plan.run : Plan → Regs → Regs × Bool`，逐条调同一批 `@[extern]`。它是 plan 的语义，
  不是 compiler 旁边的第二个 interpreter —— 没有别的东西定义 plan 的意思。
- C backend：`relc`（Lean 写的 emitter）把 plan 打印成一个 `.c`：每个 `Fun` 一个 `static` 函数，`call` 一行，
  `loop` 是 `for`，`if` 是 `if`。C 里没有 plan interpreter。
- kernel ABI 表（C 符号、每个参数 owned 还是 borrowed、结果形状）从 `@[extern]` 声明读出（extern 名和类型里的
  `@&`），不手写第二份。
- 迁移期的 `host f`：`Plan.run` 能跑，emitter 遇到就报错并点名。"程序 X 能不能出 C" 就是 "它的 plan 里还有没有
  `host`"。

## 7. 8 种运行时 closure 逐条

前提（已对源码核对）：`Tm` 树在 elaboration 时定死；`Gen.*` 的函数实参都是另一个 `Gen.*` 表达式或源码里写死的
lambda；没有任何一处从运行时数据造出函数。唯一在运行时造的树是 `Route`，它的形状也是静态的（第 6 节）。

| # | closure（`Run/` 下的位置）                                             | 成立吗 | emit 时变成什么                                                   |
|---|------------------------------------------------------------------------|--------|-------------------------------------------------------------------|
| 1 | `Gen.Fn d A B`（`Lang/Gen.lean:45`），每个节点一个                     | 成立   | 每个非闭节点一个 `Fun`，demand 是参数；闭节点是 global            |
| 2 | `Gen.Pl d A B`（`:48`），运行时造 `Route`                                 | 成立   | 不造 `Route`：形状在 emit 时读出，生成两条分支                       |
| 3 | fixed point 的 body `φ : CRel A B → Fn false A B`（`:218`、`:234`）    | 成立   | `Fun φᵢ(X, 捕获的寄存器)`，`loop` 里直接调用                      |
| 4 | 序的 test `fun P => Q P.rel`（`:153`–`:179`）→ `testC` → `estOnC` 等的 `qC` | 成立 | `Fun qᵢ(D)`；`estOnC` 等的 builder 收一个 `Fun` 名，每个使用点展开一份，直接调用 |
| 5 | `onKeys d F` 里的 step（`:183`）：`loop`、fold、`foldI`                | 成立   | `Fun stepᵢ(P)`，外加 `if P.n == 0` 跳过                           |
| 6 | AC-3：`acFixC` 的 `iterC` lambda、`foldlC (deltaStepC …)`（`AC3Def.lean:19`–`:60`） | 成立 | 一条 `loop`；arc 的 `List` 长度在 elab 时已知，逐个展开 |
| 7 | continuation：`need … model k`、`longCount k`、`expand … k`、`CRel.guard b k` | 成立 | 不是 closure conversion：builder 把 `k` 就地接在后面，`need` 是 `if … fail`，`guard` 是 `if` |
| 8 | `Route.bits`/`Route.pairs` 的 `StateM Nat`（`Lang/Bits.lean:187`、`:200`）   | 成立   | 计数器是叶子在 `Route.cols` 里的序号，emit 时是常数，状态消失        |

没有不成立的。四点要记住，都不是 closure：

- 第 7 条的证明参数（`fun h => …`、`len b = n.toNat`）在 plan 里没有载体：擦掉。plan 的证明要在读回处重新判定
  `Enc.WF`（第 12 节）。
- `need` 的消息是 Lean 的字符串插值，plan 里是 `fail` 的格式串加参数；stderr 的文字不进逐字节比较的门。
- 第 4 条 "每个使用点展开一份" 使 C 的大小随 `est`/`thin` 的使用次数线性增长；不用函数指针是为了让捕获的寄存器
  仍然是普通参数。
- `Enc` 的 payload 分派（`gatherColumn` 等返回 `Option Enc`）是数据上的 `match`，要写成 plan 的 `if`；
  稠密列阶段不需要（第 13 节阶段 7）。

## 8. 生成的 C 里的内存

- 占用和今天的 Lean 路径同阶：builder 逐条重现 `Gen`/`Alg`，plan 里物化的表就是今天物化的那些，不多一张。
- 不用 arena：fold 跑 `长度+1` 轮，`fixOn` 跑到不动点，arena 的占用是 轮数 × 表大小。
- 用 kernel 已有的约定：结果是带引用计数的 sarray，`rt.c` 用 `malloc`/`free` 实现。
- 释放由 emitter 决定：每个 `Block` 里寄存器的最后一次使用是静态的，其后插一条 `lean_dec`；`if` 的两支各自放掉
  自己不用的；参数是 owned 的 kernel（entry 里有 `lean_is_exclusive` 的就地更新，11 处）在最后一次使用时移交，
  否则先 `lean_inc`。
- `Fun` 的参数一律 borrowed，结果 owned。
- `loop` 的回边上只有状态寄存器活着，一轮的中间结果在轮内放完，占用不随轮数涨。
- global 活到最后一次使用它的 `Block` 结束（Lean 今天的常量是 persistent，永不释放）。
- mmap 进来的输入和编进 exe 的文字量 `m_rc = 0`（`lean_inc`/`lean_dec` 在 0 上不动），永不释放。
- `pass.h` 的线程池（pthread + futex）照旧，只依赖 libc。

## 9. 让 `Gen` 成为 Lean backend 的最小路径

不动的：`Tm`、`Elab`、`Expand.node` 的分派表（每个 constructor 对一个 `Gen.*` 名字）、`number`/`share` 的编号。

| 改动                                                                        | 位置                                        |
|-----------------------------------------------------------------------------|---------------------------------------------|
| 新增 `Plan`、`Plan.run`、寄存器与 `Rel A B` 的摊平/读回                     | 新文件 `Run/Lang/Plan.lean`                 |
| `Gen.Fn d A B` 改成 "建 plan 的 monad 里：demand 寄存器 → 结果寄存器"；`Gen.Pl` 改成 "emit 时的 `Route` 形状，叶子是寄存器" | `Run/Lang/Gen.lean` |
| 每个 `Gen.*` 的体从调 `CRel.*` 改成发指令；没迁的发 `host`                  | `Run/Lang/Gen.lean`，约 70 个 def           |
| `Gen.fold`/`foldI`/`loop`/`nu`/`mu`/`nuAC` 发 `loop`，step 和 `φ` 是 `Fun`  | `Run/Lang/Gen.lean`、`Expand.body`          |
| `n.rel.x := 读回 (Plan.run n.plan.x)`；`n.c.c<i>` 是 plan 的 global         | `Expand.addConst`/`share`/`emit`            |
| `Gen.Sound` 改述在 `Plan.run` 上                                            | `Rel/Lang/GenSpec.lean`、`Expand.prf`       |
| 算子的 builder（`compC`、`nubC`、`foldRound`、`Bits.*` … 各自的 kernel 序列） | `Run/{Alg,Code,AC3Def}.lean`、`Run/CRel*Def.lean`、`Run/Lang/Bits.lean` |
| emitter 和 ABI 表                                                           | 新 `Rel/Lang/EmitC.lean`，exe `relc`        |

- 每条 `*_sound` 由两步合成：`Plan.run (builder args) = 原 CRel 算子 args`，加今天的 `rep_*`。
- 顺序由程序拉动（第 13 节）。迁完一个算子的标志：它的 `host` 从 `Gen` 里消失，且上面那条等式有定理。
- 全部迁完后 `Gen` 里没有 `host`，`Dem`/`Fn`/`Pl` 的旧含义、`Gen.unhex` 的运行时读回都删掉（文字量是 `lit`）。

## 10. fused kernel 和它的模式之间的定理

- `sum` 不是 fused kernel。`Alg.Arr.sumC X = foldOnC (col [0]) (fun D => (plus D.val, true)) X`
  （`Run/Alg.lean:1442`），`Gen.total = CRel.Arr.sum`（`Run/Lang/Gen.lean:165`）：内建 `sum` 的定义体就是
  `⦇zero,plus⦈` 的 fold，两者按定义相等，没有第二份代码需要绑。
- 存在的：`CRel.Arr.rep_sum`（`Rel/CRelFold.lean`）—— ok bit 为真时 `rep (Arr.sum X).rel xs w` 当且仅当 `xs` 是
  `X` 的一行、各后缀和不溢出、无 null、`w = xs.foldr (· + ·) 0`；它还带着假设 `hat`
  （`/home/dh/repo/freyd/doc/rel-architecture-review.md` 第 1 条）。
- 缺的：allegory 层的 `sum = ⦇[zero,plus]⦈` 没有陈述；`Gen.total_sound` 和 `Gen.fold_sound` 都不存在，
  所以用到 `sum` 或 fold 的定义没有 `rep_x`。

一般情形，按 `Expand.prfNode` 有没有 lemma 分（上一版查的；`GenSpec` 之后有改动，动手前逐个再查索引）：

- 有 `Gen.*_sound`（22 个）：`val` `uni` `zero` `id` `top` `mem` `outl` `outr` `inl` `inr` `comp` `conv` `meet`
  `join` `diff` `dom` `ran` `ldiv` `rdiv` `pair` `prod` `junc`。
- fused，绑定定理齐：bit-matrix 的 `compB` `meetB` `diffB` `ldivB`（`p*_sound`，`Rel/Lang/BitsSpec*.lean`）。
- fused，Alg 层有绑定、Gen 层没有：`nuAC` —— `AC3.acFix_eq_fixOn`，没有 `nuAC_sound`。
- 只有 CRel 层逐点定理，没有 `Gen.*_sound`：`fold`/`foldI`（`CRel.rep_fold`）、`total`、`lam`
  （`CRel.rep_transpose`）、`E`、`est`、`thinL`、`merge`、`loop`、`nu`/`mu`（`CRel.rep_fixOn`）、`cons`、`inits`。
- 两层都没查到：`map` `thin` `union` `tau` `nil` `uncons` `length` `cat` `uncat` `zip` `snoc` `unsnoc` `atPos`
  `setify` `bagify` `tic` `succ` `arith` `leq` `lt` `flat`。

## 11. 输入和输出（G 加通用 IO，已定）

声明（语法是这里定的，没有实现）：

```
input  x : K ⟶ [N] from "data.csv"              -- 格式按扩展名：.csv
input  g : V ⟶ D   from "grid"  as col          -- qlean column 目录
input  t : I ⟶ [N] from "rows.txt"
output y to "out.csv"                            -- y 是本 program 的一个闭定义
```

- `input x : A ⟶ B from "p"` 引入名字 `x`，一个 `d = false` 的关系；`A`、`B` 必须是声明过的 object，没有 type variable。
- 格式在 elab 时定：`as col|csv|txt` 写了就用它；没写按 `System.FilePath.extension`（`csv`、`txt`；没有扩展名是
  `col`）；别的扩展名报错，要求写 `as`。
- exe 启动时可以换路径：参数 `x=other.csv`。文件不存在或读不了：exit 1，点名输入的名字、路径和 errno。
- 输入是整个 program 的参数，和 module 设计里常量的关系参数是同一个机制（`Tm` 的参数叶子，`d = false`）：
  用到 `x` 的闭节点仍然是 global，在读完输入之后算一次。
- `Tm`、关系算子都不增加：reader 和 writer 是 `main` 里的 C 调用，不是 plan 的关系指令。

三种格式（一行 `(a, b)` 摊平成字段：`prod` 是并排的字段，atom 是一个字段）：

| 格式  | 文件                                              | `arr`                                     | 能装的类型                       | 读法                                   |
|-------|---------------------------------------------------|-------------------------------------------|----------------------------------|----------------------------------------|
| `col` | 一个目录，摊平后每个原子列一个 qlean column file（`c/own.c`，头 `"qleancol"`） | `lo`、`hi`、payload 三个文件 | 任何 `Obj`（含 `sum`、嵌套 `arr`） | `qlean_own_map`：一次 `MAP_PRIVATE` 的 mmap，不解析、不复制 |
| `csv` | 一行一条记录，`,` 分隔，RFC 4180 的引号；`header` 选项跳过第一行 | 一个字段，元素用空格分隔 | atom、`prod`、atom 的 `arr`      | 新 C reader，一遍扫描，出稠密列        |
| `txt` | 一行一条记录，空白分隔，没有引号                  | 只能是最后一个字段，占这一行剩下的全部    | 同 csv                           | 和 csv 同一个 reader，换分隔规则       |

- csv/txt 装不下的类型（`sum`、嵌套 `arr`、`prod` 的 `arr`）在 elab 时报错并点名类型，提示改用 `col`。
- 字段的读法跟 object 走：range object 读整数；枚举 object（`obj K = {a,b,…}`）读名字，查它的 `elems` 得到序号。
- 每个值都对着 object 的 universe 检查：csv/txt 在解析时逐字段查，`col` 在 mmap 之后跑一遍 min/max kernel。
  不在 universe 里就 exit 1，点名文件、行、字段（`col` 是列和行号）。不丢行，不截断。
- `col` 读进来的 kind 有 foR/alp/enum；阶段 7 之前 C 路径只收 kind 0（bytes）和 1（bits），别的报错点名文件。
- 输出对称：`output y to "p"` 用同样的三种格式和同样的选格式规则；`col` 走 `qlean_own_write`（写临时文件再
  rename），csv/txt 是新的 C writer。`print` 照旧写 stdout。`check` 不成立或 ok bit 为 false 时 exit 1 并打印
  `n.failures` 的那一行。
- reader/writer 只有一份：`c/relio.c`（qlean 仓库，约 400 行）。Lean backend 通过 `@[extern]` 调同一份，
  所以两个 backend 读出来的列逐字节相同。
- 带 `input` 的 program 在 elaboration 时算不算，是第 14 节的 P 对 Q。

## 12. 风险

- 粒度：最大的一项。`{…} plus` 的锥是 173 个 LeetQ def；先用 spike 量出每个 def 的 builder 加定理的代价再承诺。
- 代码大小：每个 route root 两条分支，每个 `est`/`thin` 使用点一份，每个参数化常量的 instantiation 一份。
  SudokuPC9 这种程序的 `.c` 有多大，spike 之后量。
- `Rep*` 证明都陈述在今天的 `Alg` 定义上。builder 是第二份文本，即使有定理绑着也是两处改动（J 对 K）。
- 依赖类型：`Arr t n` 的 `n` 是运行时值，`need`、`longCount … fun r hr =>` 把证明传给后续代码；
  builder 里这些证明没有载体，只能在读回处重新判定 `Enc.WF`，证明里要多一层"判定通过"。
- `Enc` 的动态分派在 qlean 的 Lean 侧。C 路径只做稠密列时，从 `col` 目录读进来的编码列用不上
  compute-on-compression；补上它等于把那层分派写成 plan 的 `if`（阶段 7）。
- `general` 列（`Enc.gen`，每个元素一个 boxed `QValue`）没有 C 表示：C 路径不支持，报错点名。
- "emitter 和 Lean compiler 同级信任" 只对一半：Lean 的 compiler 有全世界的用户，`relc` 只有 differential 门。
  所以逐字节比较的那道门不是可选项，每个出 C 的程序都要进它。
- `rep_*` 留在 `Alg` 层不动，新增的只是 `Plan.run (builder) = 旧定义` 这一族定理，`Gen.*_sound` 由两者合成。

## 13. 计划

owner：`Run/*`、`Rel/Lang/*`、`Rel/Rep*` = ffreyd；`Rel/Programs/*` = aima；`/home/dh/repo/qlean` 的改动由 ffreyd
在 qlean 的分支上做。

四条门（每个出 C 的程序都过）：

| 门 | 内容                                                                     |
|----|--------------------------------------------------------------------------|
| 1  | `nm -u exe` 里没有 `lean_`                                               |
| 2  | `ldd exe` 只有 libc/libm/libpthread                                      |
| 3  | exe 的 stdout 和输出文件逐字节等于 Lean backend（`Plan.run`）在同一输入上的 |
| 4  | plan 里没有 `host`                                                       |

| 阶段 | 交付                                                                                     | 规模         |
|------|------------------------------------------------------------------------------------------|--------------|
| 1a   | 最小的端到端 exe：`x ≜ {…}°`，结果经 `qlean_own_write` 写成 `col` 目录                   | 约 900 行    |
| 1b   | `{…} plus`：demand 函数、`if`、`fail`、bit/table 两条分支                                | 约 1900 行   |
| 2    | 输入声明和三种格式的 reader/writer                                                       | 约 900 行    |
| 3    | `loop`：`x⦇ran(zero),plus⦈`                                                              | 约 1500 行   |
| 4    | `Gen` 变成 Lean backend                                                                  | 约 900 行改动 |
| 5    | 按程序迁其余算子                                                                         | 每个程序 500–1500 行 |
| 6    | 补 `Gen.*_sound`                                                                         | 每个节点 50–300 行 |
| 7    | C 路径上的 FoR/ALP                                                                       | 大，单独立项 |

### 阶段 1a — 最小的端到端 exe，不带 Lean runtime（约 900 行）
- 程序：`x ≜ {…}°`，`output x to "out"`。文字量编进 exe 成 `m_rc = 0` 的静态数组；`°` 是寄存器改名；
  唯一的 kernel 调用是 `qlean_own_write`。锥是 0 个 `Alg` def，所以这一步只量管线本身。
- 交付和估计：`rt.c`（150）；`Plan` 的 `lit`/`call`/`fail` 和 `Plan.run`（200）；`relc` 和 ABI 表（350）；
  `col` 的 writer 胶水和 `main`（100）；lakefile 和测试（100）。
- 文件：`c/rt.c`（qlean）、新 `Run/Lang/Plan.lean`、新 `Rel/Lang/EmitC.lean`、新 `Rel/Lang/TestNative.lean`、
  `/home/dh/repo/freyd/leetq/lakefile.lean`。owner：ffreyd。
- 门：1、2；输出目录逐字节等于 Lean 这一侧用 `qlean_own_write` 写出的。
- 它回答路线 B 最大的未知数：现成的 `libqleankernel.a` 能不能只靠 `rt.c` 链接并跑起来。

### 阶段 1b — 第一个带 demand 的程序（约 1900 行）
- 程序：`{…} plus`。elaborate 出来是 `Gen.compB`：文字量叶子、`ranC` 给出 demand、`arith` 的 demand 函数、
  route root 的 bit/table 两条分支。第 6 节的每一种构造除了 `loop` 都出现一次。
- 交付和估计：`Fun`/`apply`/`if`/global 和 last-use 释放（350）；173 个 def 的锥的 builder —— `Code` 的底座、
  `compC`、`ranC`、`arith`、`Bits` 的 `comp` 一条 bit 规则（约 1200）；`Plan.run (builder) = compC` 一条定理，
  用来量代价（约 300）；测试（50）。
- 文件：`Run/Lang/Plan.lean`、`Rel/Lang/EmitC.lean`、`Run/{Alg,Code}.lean`、`Run/Lang/Bits.lean` 里那个锥。
  owner：ffreyd。
- 门：四条；另外两个测试输入各逼出一条分支（一个 universe 小到走 bit，一个超过 2²⁷ bit 走 table）。
- 判断点：这里量出每个 def 的 builder 加定理的代价。若明显贵于它的旧定义，停下来把范围缩到他点名的程序。

### 阶段 2 — 输入和输出（约 900 行）
- 交付：`input`/`output` 声明；`c/relio.c`（csv/txt 的 reader 和 writer，`col` 的目录读写，universe 检查）；
  Lean backend 的 `@[extern]`；exe 的参数。
- 估计：`relio.c`（400）；`Syntax`/`Parse`/`Elab` 的声明和参数叶子（250）；`Plan` 的 `main` 和 Lean 侧 extern（150）；
  测试和 `/home/dh/repo/freyd/doc/rel-lang-design.md`（100）。
- 文件：`Run/Lang/{Syntax,Parse,Elab,Plan}.lean`、`c/relio.c`。owner：ffreyd。
- 门：四条；同一个程序、三种格式各一份同内容的输入，三次输出逐字节相同；坏输入（越界的值、缺字段、不存在的文件）
  各有一个测试，exit 1 且消息点名位置。
- 排在循环之前：阶段 3 的内存门要一个 100 万行的输入，文字量做不到。

### 阶段 3 — 循环（约 1500 行）
- 交付：`loop` 指令；`foldByC` 的锥（`foldRound`、`nubC`、`antiJoinC`、`unionC`、`pairC`、`demandStepC`）；
  程序 `x⦇ran(zero),plus⦈`，step 是一个 `Fun`。
- 文件：`Run/Lang/Plan.lean`、`Rel/Lang/EmitC.lean`、`Run/Alg.lean`。owner：ffreyd。
- 门：四条；100 万行输入下峰值 RSS 不随轮数涨，且不超过 Lean backend 的峰值。

### 阶段 4 — `Gen` 变成 Lean backend（约 900 行改动）
- 交付：约 70 个 `Gen.*` 全部产 plan，未迁的发 `host`；`Expand` 出 `n.plan`；参数化常量的值改成 plan builder；
  `Fn`/`Pl` 的旧含义删除。
- 文件：`Run/Lang/Gen.lean`、`Run/Lang/Expand.lean`、`Rel/Lang/GenSpec.lean`。owner：ffreyd。
- 门：仓库里只剩一条执行路径；`lake build LeetQ` 全绿；所有 `Rel/Programs/*` 的 `#guard` 和已有的 `rep_*` 不变；
  `SudokuPC9` 的运行时间不退。

### 阶段 5 — 按程序迁其余算子（每个程序约 500–1500 行）
- 交付：先 `Rel/Programs/Mss.lean`（`Λ`、`est`、`inits`、`cons`：第一个 test 函数），再 `μ`/`ν`、其余 bit 规则、
  AC-3。
- 文件：`Run/{Alg,Code,AC3Def}.lean`、`Run/Lang/Bits.lean`；每个程序一个 native 测试。
  owner：ffreyd；程序侧的改写归 aima。
- 门：四条。

### 阶段 6 — 补 `Gen.*_sound`（每个节点 50–300 行，可与 1–5 并行）
- 交付：第 10 节后三类节点的 lemma，从 `fold`、`total`、`lam`、`est` 开始。
- 文件：`Rel/Lang/GenSpec.lean`、`Expand.prfNode`。owner：ffreyd。
- 门：`Rel/Programs/*` 每个程序的 `n.unproved = []`。

### 阶段 7 — C 路径上的 FoR/ALP（大，单独立项）
- 交付：`Enc` 分派写成 plan 的 `if`；`col` 目录的编码列直接进 kernel。
- 文件：`Run/Lang/Plan.lean`、qlean 的 Lean 分派层。owner：ffreyd。
- 门：编码列输入下 exe 与 Lean backend 逐字节相同；`rel-bench` 的数不退。

## 14. 需要他定的事

已定 H（由 S 的评估得出）：`Alg`/`Code` 的正文不动，Lean 元程序遍历每个 def 的 `Expr` 生成 plan；"记录再执行 =
立即执行"是每个 def 的翻译检查。拼法仍只有一份。落选：G，即照 S 原样写成泛型（`Mode` 参数 + `@[reducible] exec`），
因为要改 `Alg.lean` + `Code.lean`（2906 行）几乎每个签名、约 140 个 law 字段，运行时分支（`need`/`longCount`/`decide`
共 105 处）要改写成 `Bit` 编码（约 +250 行证明）；J（同一算子两份文本）；K（`Rep*` 全部重写）。

`Alg` 的旧定义（原选项，留作记录）：

- J — 旧定义留作 spec，builder 另写，用 `Plan.run (builder) = 旧定义` 绑定；`Rep*` 证明不动（和 qlean 的
  `@[extern]` 带 Lean body 是同一个模式，但同一个算子有两份文本）。
- K — 旧定义删掉，改成 `Plan.run (builder)`，`Rep*` 证明跟着重写（一份文本，证明的改动量大得多）。

带 `input` 的 program 在 elaboration 时做什么（阶段 2 要用）。已定 P；Q 落选，因为 lake 不追踪数据文件，改了文件
build 读到的是旧缓存：

- P — 不读文件。依赖输入的定义在 elaboration 时没有值；它们的 `check`/`print` 只在 exe 和 Lean backend 的
  `n.run` 里跑；`rep_x` 对输入的值全称量化。build 不依赖数据文件（建议）。
- Q — elaboration 时读 `from` 的文件（必须存在），照今天的样子全部算完；exe 启动时再读一遍，路径可以由参数换掉。
  `#guard n.ok` 照旧能用，但 build 依赖数据文件，证明仍然要按 P 的方式量化。
