# Rel 的 module 系统 — 设计

只是设计,没有实现任何东西。路径都在 `/home/dh/repo/freyd/leetq/LeetQ/Rel/` 下面。没有跑过 build,
标了"未验证"的条目是读源码或凭记忆得出的。`Lang/Embed.lean` 正被 stage 2 改动,行号是写本文时的。

## 1. `after` 现在做什么

| 问题                           | 回答                                                                              | 位置                                   |
|--------------------------------|-----------------------------------------------------------------------------------|----------------------------------------|
| grammar                        | `rel_program n (after ident)? where …`:最多一个 module                            | `Lang/Embed.lean:150`                  |
| `n` 存了什么                   | `n : Program`,只有它自己的 declaration;没有记录它的 `after`                       | `Lang/Embed.lean:447`                  |
| 文本在什么 scope 里读          | `Parse.scope pre`:`pre` 的名字、arity、object,每个名字标成 "in the prelude"       | `Lang/Parse.lean:411`, `:433`          |
| elaboration                    | `Expand.defsOf (some pre) prog`:先 `walk pre {}`,再 `walk prog env`               | `Lang/Expand.lean:80`                  |
| 能不能 chain                   | 不能。`walk pre {}` 从空 `Env` 开始,`pre` 自己需要 prelude 时报 "in the prelude"  | `Lang/Expand.lean:80`                  |
| parametric def `f(R : α ⟶ β)`  | 共享,但方式是每次使用都把 body 重新 elaborate 一遍,α β 每次使用各自 instantiate   | `Lang/Elab.lean:1029` `mkDef`, `:917`  |
| polymorphic closed def `head`  | 同上                                                                              | `Lang/Expand.lean:66`                  |
| monomorphic closed def         | 每个 import 它的 program 各 build 一次,作为 `.tm res` inline                      | `Lang/Expand.lean:72`                  |
| object                         | `pre` 的 `obj` 进入 `Parse.S.objs` 和 `Env.objs`:全局名字,元素固定;object 不能当参数 | `Lang/Parse.lean:413`, `Lang/Expand.lean:22` |
| 生成的 Lean constant           | 只给 `n` 自己的 closed def:`n.rel.x` 和 `n.c.c<i>`;share map 每个 program 一份     | `Lang/Expand.lean:308`, `:184`         |
| 名字查找                       | 全在 Rel 自己的表里:`Parse.S.known`/`objs`/`taken`、`Env.defs`/`objs`;不看 Lean environment | `Lang/Parse.lean:13`, `Lang/Elab.lean:408` |

所以现在 Rel 有一套和 Lean 平行的 scope。下面的设计把它去掉。

## 2. 设计:直接用 Lean 的 module 系统

- 一个 Rel module 就是一个 Lean module:`rel_program csp where …` 写在 `Programs/CSP.lean` 里。
- 每个 Rel def 是一个 Lean constant,`csp.AC3`(Gen/CRel 那一层),elaborate 一次,存在 `.olean` 里(2.4)。
- import 用 Lean 自己的 `import LeetQ.Rel.Programs.CSP`,写在文件头。
- qualified 用法是 `csp.AC3(…)`;selective 用法是 Lean 的 `open csp (AC3)` 或 `open csp`,写在
  `rel_program` 之前。
- visibility 规则全部是 Lean 的 `namespace`/`open`/`export`;Rel 不发明任何 import 语句。
- Rel body 的名字解析读 Lean environment 和当前的 open declaration,不再读自己的 `Env`/`after`。
  `after prelude` 变成普通的 `import` 加 `open prelude`。

| 要做的事               | 写法(都是 Lean 的,在 `rel_program` 之外)          | Haskell               | Python                 |
|------------------------|----------------------------------------------------|-----------------------|------------------------|
| 定义 module            | `rel_program csp where …`,相当于 `namespace csp`   | `module M where`      | 文件 `m.py`            |
| import                 | `import LeetQ.Rel.Programs.CSP`                    | `import qualified M`  | `import m`             |
| qualified 使用         | body 里写 `csp.AC3(A,C,s)`                         | `M.a`                 | `m.a`                  |
| selective 打开         | `open csp (AC3)`                                   | `import M (a)`        | `from m import a`      |
| 整个打开               | `open csp`                                         | `import M`            | `from m import *`      |
| 去掉 / 改名            | `open csp hiding K`、`open csp renaming s₀ → start` | `hiding`、`as`       | `import a as b`        |
| re-export              | `export csp (AC3)`                                 | export list           | —                      |

### 2.1 例子(问题 1)

module 保留书上的名字;原来依赖 board 的 def 把 board 作为参数。`revise` 删掉,因为它比自己的定义长。

```
import LeetQ.Rel.Programs.Prelude                                    -- Programs/CSP.lean
namespace LeetQ.Rel.Programs
open prelude

rel_program csp where
    peer(unit : α ⟶ γ) : α ⟶ α ≜ (unit unit°) ∩ ≠
    AC3(A : α ⟶ α, C : β ⟶ β, s : α ⟶ β) : α ⟶ β ≜ νX : s ∩ (A\(X C))
    s₀(g : α ⟶ β) : α ⟶ β ≜ g°\𝟙
    K₀(A : α ⟶ α, s : α ⟶ β) : α×β ⟶ α×β ≜ cor(s) ∼((A×𝟙) ∪ (𝟙×≠)) cor(s)
    sup(X : α×β ⟶ α×β) : (α×β)×α ⟶ α×β ≜ π₁X ∩ (π₂π₁°)
    pc(X : α×β ⟶ α×β) : α×β ⟶ α×β ≜ π₁\(sup(X) X)
    K(R : α×β ⟶ α×β) : α×β ⟶ α×β ≜ νX : R ∩ pc(X)
    s'(K : α×β ⟶ α×β) : α ⟶ β ≜ π₁°(K ∩ 𝟙)π₂
```

qualified:board 自己的 `peer`、`s₀`、`s`、`K₀`、`K`、`s'` 是 `sudokupc9.peer` 等,和 `csp.peer` 不冲突。

```
import LeetQ.Rel.Programs.CSP                                        -- Programs/SudokuPC9.lean
namespace LeetQ.Rel.Programs
open prelude

rel_program sudokupc9 where
    obj Cell = 0…80
    obj Unit = 0…26
    obj D = 1…9
    unit : Cell ⟶ Unit ≜ {…}
    g : Cell ⟶ D ≜ {…}

    peer : Cell ⟶ Cell ≜ csp.peer(unit)
    s₀ : Cell ⟶ D ≜ csp.s₀(g)
    s  : Cell ⟶ D ≜ csp.AC3(peer, ≠, s₀)
    K₀ : Cell×D ⟶ Cell×D ≜ csp.K₀(peer, s₀)
    K  : Cell×D ⟶ Cell×D ≜ csp.K(K₀)
    s' : Cell ⟶ D ≜ csp.s'(K)
    check s' ⊑ s
```

selective:只打开 board 自己不定义的名字。

```
import LeetQ.Rel.Programs.CSP                                        -- Programs/SudokuAC.lean
namespace LeetQ.Rel.Programs
open prelude
open csp (AC3)

rel_program sudokuac where
    obj …; unit …; g …; sol …
    peer : Cell ⟶ Cell ≜ csp.peer(unit)
    s₀ : Cell ⟶ D ≜ csp.s₀(g)
    s  : Cell ⟶ D ≜ AC3(peer, ≠, s₀)
    check s = s₀ ∩ (peer\(s ≠))
```

- 同一步还能做第二个 module:`obj Cell/Unit/D` 和 243 对的 `unit` 在 `SudokuAC` 和 `SudokuPC9` 里逐字相同。
  `rel_program board9 where obj … ; unit ≜ {…}` 加 `open board9` 去掉这份拷贝(object 也是 Lean constant)。

### 2.2 对 object 的 parametricity(问题 2)

| 方案                                              | Lean 对应物                                                  | 结论   |
|---------------------------------------------------|--------------------------------------------------------------|--------|
| polymorphic def:α β,关系作参数                    | 带隐式 `{A B : 𝒜}` 和显式参数的普通 def(`doc/rel-lean-mapping.md` 的 "type variable"、"parameter" 两行) | 采用 |
| module 以 obj 和关系为参数(`csp(Cell, D, unit, g)`) | 没有:带 `variable` 的 `section` 关闭后就是上一行,Lean 没有"在参数处实例化一个 section"的构造 | 否决 |

- 第一种的代价:import 的一方自己写参数(`csp.peer(unit)`),自己给结果起名字。
- module 从不提 `Cell` 或 `D`;object 通过传进来的关系的 type 到达 def。

### 2.3 名字解析(问题 3)

规则是 Lean 的,不是 Rel 的:

| 情形                                        | 结果                                                                              |
|---------------------------------------------|-----------------------------------------------------------------------------------|
| `csp.x`                                     | import 了文件就能用,不需要 `open`                                                 |
| 本地 def 和 `open` 进来的名字同名           | 本地的赢:Lean 先查当前 namespace(`sudokupc9.peer`),再查 open。凭记忆,实现时核对 `Lean.ResolveName.resolveGlobalName` |
| 两个 `open` 给出同一个名字                  | 在使用处报 ambiguous,列出两个 constant                                            |
| re-export                                   | 没有,除非写 `export`                                                              |
| `private`                                   | Rel body 里没有写它的地方;不提供。要隐藏就不 `open`                               |
| cycle                                       | Lean 的 import DAG 不允许                                                         |
| 一个名字能解析到哪些 constant               | 只有 registry 里的和 kernel 表里的(见 "边界");别的 Lean constant 报 "`x` is not a Rel definition" |

#### 名字查找改走 Lean environment,要改什么

| 位置                                             | 现在                                                    | 改成                                                                 |
|--------------------------------------------------|---------------------------------------------------------|----------------------------------------------------------------------|
| 新增:一个 persistent environment extension       | —                                                       | `rel_program` 每 emit 一个 def 或 object 就登记:constant 名、arity、是否 infix、signature(参数和结果的 `OExp`)、是 def 还是 object。存进 `.olean`,import 之后就在 |
| `Lang/Embed.lean:150` grammar                    | `(&" after " ident)?`                                   | 删掉                                                                 |
| `Lang/Embed.lean:447` `elabRelProgram`           | `programOf` 读出 prelude 的 AST,`Parse.scope` 造初始 scope | 从 `getEnv`、`getCurrNamespace`、`getOpenDecls` 造一个 resolver:字符串 → 登记过的 constant(及其 arity)。用 Lean 自己的 `ResolveName.resolveGlobalName`,不重写它的规则 |
| `Lang/Parse.lean:13` `S`                         | `known`、`objs`、`taken` 三张表,含 prelude 的名字       | 三张表只留本 program 自己的名字;加一个字段放上面的 resolver          |
| `Lang/Parse.lean:104` `name`(`:110` `inScope`)   | 最长前缀在 `known` 或 builtin 里                        | 最长前缀在 `known`、builtin,或者 resolver 认得。字母串的切分就是这样从 `open` 得知 scope 里有哪些名字的 |
| `Lang/Parse.lean:101` `isInfix`                  | `known` 里有 `_n_`                                      | 再问 resolver:`n` 解析到的 constant 登记为 infix                     |
| `Lang/Parse.lean:237`、`Lang/Embed.lean:304`     | `known.lookup n` 取 arity                               | 先 `known`,再 resolver 的 arity                                      |
| `Lang/Parse.lean:143` `oprim`                    | `s.objs.contains w`                                     | 再问 resolver:`w` 解析到一个登记为 object 的 constant                |
| `Lang/Parse.lean:175` `fresh`                    | 和 `taken`(含 prelude)比,重名报错                       | 只和本 program 自己的名字比;和 open 进来的名字同名不报错(Lean 的规则) |
| `Lang/Parse.lean:433` `scope`                    | 把 prelude 的 AST 折成 scope                            | 删掉                                                                 |
| `Lang/Elab.lean:408` `Env`                       | `defs : List (String × Def)` 含 prelude 的 closure      | `defs` 只留本 program 的;外面的名字经 resolver 得到 constant         |
| `Lang/Elab.lean:741`, `:754`, `:762` `elabE`     | `env.defs.lookup n`                                     | 查不到时问 resolver;得到的是 "constant + signature",type 检查只看 signature(2.4) |
| `Lang/Elab.lean:416` `oty`                       | `env.objs.lookup n`                                     | 查不到时问 resolver,从 object 的 constant 读出它的 `Obj` 和 universe  |
| `Lang/Expand.lean:80` `defsOf`、`:32` `preludeDef` | 每个 program 重新 `walk` 一遍 prelude                  | 删掉;`perm° = perm` 这条规则改成登记在 `prelude.perm` 这个 constant 上的标记 |
| `Lang/Expand.lean:46` `walk`、`:308` `emit`      | 最后一起 emit `n.rel.x`                                 | 每个 def emit 成 `n.x` 并登记;辅助 constant(`n.expanded`、`n.c.*`)挪到 Rel 名字拼不出来的名字下面 |
| `Lang/Gen.lean`                                  |                                                         | 名字查找不需要改它;2.4 需要                                          |

`m.x` 怎么读:

- `.` 加入 `Parse.reserved`(`Lang/Parse.lean:52`),不再是单字符名字。
- 在 `Parse.name` 里,光标处到 `.` 之前的那串字母如果是一个 namespace(`ResolveName.resolveNamespace`),就读
  qualified name:member 是 `.` 后面那串字母里 resolver 认得的最长前缀。`csp.AC3peer` 是 `csp.AC3` 再 `peer`,
  `Rcsp.AC3` 是 `R` 再 `csp.AC3`。
- 它是一个 primary,唯一的那一级优先级不变。
- Lean 把 `csp.AC3`、`csp.s₀`、`csp.s'` 读成一个 identifier,`Embed.namesOf`(`Lang/Embed.lean:185`)本来就把
  identifier 的文本交给 `Parse.name`,所以这部分不需要新的 production。

符号名(`≼`、`≠`、`_⇒_`):

- constant 的名字就是那个字符:`prelude.«≠»`、`csp.«≼»`。Lean 的 `Name` 允许任何字符串;resolver 用
  `Name.mkSimple "≠"` 去查,不经过 Lean 的 tokenizer。
- infix def `_⇒_(R,S)` 的 constant 叫 `prelude.«⇒»`,"是 infix" 记在 extension 里,不放在名字里。
- 整个打开:`open prelude` 之后 body 里直接写 `≠`、`R ⇒ S`,和现在一样。
- selective 打开:写 `open csp («≼»)`。书名号是 Lean 对非 identifier 名字的写法,不是新语法。
- qualified:`csp.≼` 不是一个 Lean identifier(Lean 读成 `csp`、`.`、`≼` 三个 token),所以 `rel` category 要加一个
  production `ident noWs "." noWs relSym`。这是唯一新增的 production。

#### 边界:Rel body 能看到的只有 registry 和 kernel 表

已定:借用 Lean 的 scope,再用 registry 过滤。Rel 不加自己的 open 语句。

| 东西          | 是什么                                                                              | 谁能写                         |
|---------------|-------------------------------------------------------------------------------------|--------------------------------|
| registry      | 上表的 environment extension:每个 Rel def/object 的 constant 名、所在 module、arity、infix、signature | 只有 `rel_program` 的 elaborator。没有 attribute,没有别的登记入口 |
| kernel 表     | `Op.table`(`Lang/Syntax.lean:55`),`Parse.builtin`(`Lang/Parse.lean:96`)读它        | 只有改这张表                   |
| Lean 的 scope | 当前 namespace 和 open declaration                                                  | 文件头的 `namespace`/`open`    |

- Lean 的 `import` 和 `.olean` 只是运输:registry 的条目和 constant 随 `.olean` 到达 import 它的文件。
- kernel 表是唯一一处 `rel_program` 之外、Rel body 够得着的东西。`Bin.table`(`Lang/Syntax.lean:82`)的
  `∩ ∪ − / \ ×` 是 grammar 的 reserved 字符,不是名字,不经过名字查找。
- 一个名字 `x`(或 `m.x`)的解析,顺序固定:
  1. 参数、fixed point 变量、本 program 已定义的名字(`Parse.S.known`);
  2. kernel 表;
  3. Lean 的 `resolveGlobalName` 在当前 namespace 和 open declaration 下给出的候选,只留 registry 里的:
     - 留下一个:就是它;
     - 留下多个:报 ambiguous,列出它们;
     - 一个不留,但 Lean 给出过候选:报 "`x` is not a Rel definition",并写出 Lean 解析到的 constant;
     - Lean 也没有候选:报 unknown name(现在的报错)。
- 字母串的切分只用第 1–3 步里留下来的名字:一个不在 registry 里的 Lean constant 不会改变切分,即使它被
  `open` 进了 scope。`open Nat` 之后 `succ` 仍然是 kernel 表里的 `succ`。
- 为什么选 "Lean 的 `open` 加过滤",不选 "Rel 自己的 open 行":
  - 边界由过滤那一步保证,不由谁来写 `open` 保证;两种做法在边界上一样强;
  - Rel 自己的 open 行要把 namespace、selective、hiding、renaming、export 的规则再实现一遍,是第二份
    scope 规则;用 Lean 的,规则只有一份。
- 怎么检查边界:
  - 过滤是 resolver 里的一处代码,所有查找(`Parse.name`、`isInfix`、`oprim`、`elabE`、`oty`)都经过它,
    没有第二条路;
  - `Expand` 生成的 `Expr` 里,除了 `Gen.*`/`Bits.*` 的运行时函数,出现的 constant 必须在 registry 里。
    `emit` 在 `addConst` 之前对生成的值检查这一条,失败就是 internal error。这是对 "实际生成了什么" 的
    检查,不依赖 resolver 没写错;
  - 测试见第 4 节 "封闭性" 三行。

#### 和 "Rel 是封闭的文本语言" 冲突吗

不冲突,条件有两个:

- 只有文件头是 Lean(`import`、`namespace`、`open`、`export`)。`rel_program … where` 本来就是 Lean 文件里的一条
  Lean command,前面已经有 `import LeetQ.Run.Lang.Embed` 和 `namespace LeetQ.Rel.Programs`。body 仍然只有
  `obj`、关系定义、parametric def、μ/ν、`check`,没有新增任何 production 能嵌 Lean 的 `term`。
- 上一小节的边界。一个手写的 Lean def 即使 type 是 `CRel A B`、即使被 `open` 进来,Rel body 写它的名字也
  得到 "`x` is not a Rel definition"。去掉这一条,body 就能调用任意 Lean 代码,那才是 escape。

代价:一个 Rel program 不再是自包含的文本,它的 import 和 open 在 Lean 文件头里。独立的 `.rel` 文本文件
(`doc/rel-lang-design.md` 里的 `program_file` 那条路)没有地方写 import(见 I)。

### 2.4 只 elaborate 一次(问题 4)

要求:`AC3(A,C,s) ≜ νX : s ∩ (A\(X C))` 在 `csp` 里 elaborate 一次,成为一个 polymorphic Lean constant;
调用处是它的 application,不是 body 的拷贝,也不随 import 它的 program 重做。现在的 "每次使用展开" 是要
改掉的行为。2.3 的 resolver 给出的正是 "constant + signature",所以两件事是同一个改动的两半。

#### 现在是什么逼着每次使用都展开

| # | 原因                                                                                             | 位置                                         |
|---|--------------------------------------------------------------------------------------------------|----------------------------------------------|
| 1 | parametric def 在 `Env` 里是一个 closure:`mkDef.apply` 每次使用都对 body 跑 `elabE`,`bind` 每次 instantiate α β | `Lang/Elab.lean:1029`, `:917`       |
| 2 | `walk` 对带参数的 def 和 polymorphic closed def 什么都不 emit,只存 `mkDef`;只有 monomorphic closed def 进 `ds` | `Lang/Expand.lean:66`, `:74`         |
| 3 | core term `Tm : Obj → Obj → Bool → Type` 按具体的 `Obj` 和具体的 demand bit `d` 索引;`build` 只在解出的 object 上造 `Tm`,`objOf` 遇到没解出的 variable 报错 | `Lang/Elab.lean:21`, `:1276`, `:1176` |
| 4 | `Tm` 没有"参数"这种叶子,只有 fixed point 的 `.var k`                                              | `Lang/Elab.lean:95`                          |
| 5 | universe(object 的元素,也就是它的大小)在 build 时按 object 的名字从 `Env.objs` 取,作为字面数据烧进 constant | `Lang/Elab.lean:138` `uniOf`, `:1198`, `:1204` `numU`; `Lang/Expand.lean:157` `valsE`; `Lang/Gen.lean:87`, `:185` |
| 6 | bit planner 只穿过它看得见的节点,其余都是 `pleaf`(一张 table)。inline 之后 `pc(X) = π₁\(sup(X) X)` 的 plan 穿过 `sup` 的 body;如果 `sup` 是一个返回 `CRel` 的 constant,`sup(X)` 就要先做成 table(9×9 上约 10⁸ 行,见 `SudokuPC9` 的文件头) | `Lang/Expand.lean:192` `plan?`, `:212` `planOr` |
| 7 | AC-3 的形状是静态识别的:`arcs` 要求 `A`、`C` 是 `closed`(`fv` 为空)。参数如果读成 variable 就不 closed,退到通用的 `Gen.nu`,不走 `Gen.nuAC` | `Lang/Expand.lean:120`, `:110`; `Lang/Gen.lean:210`, `:217` |
| 8 | 节点的选择看具体的 `d`:`comp` 对 `compB`,`meet` 对 `meetB`,`diff` 对 `diffB`                      | `Lang/Expand.lean:223` `node`; `Lang/Gen.lean:103`, `:109` |
| 9 | 参数给的是 family 时,body 在 index `I` 上 lift 之后重新 elaborate,得到的是另一个 term            | `Lang/Elab.lean:1029`(`.rel e, some I` 分支) |

不是原因的两条:

- plan 本身已经是 run time 造的(`Gen.pcomp` … `Gen.pldiv`,`Lang/Gen.lean:232`–`:242`),矩阵大小在
  `Bits.run?`(`Lang/Bits.lean:215`)从叶子读出。逼着展开的是 plan 的形状要穿过 def 的边界(第 6 条),
  不是大小。
- ν 的 body 已经是一个 Lean `fun X`(`Lang/Expand.lean:218` `body`)。

#### 一个 constant,每个调用仍然各自 plan

`csp` 里 emit 的 constant(Gen/CRel 这一层;AOP 那一层对应
`csp.AC3 {α β} (A : α ⟶ α) (C : β ⟶ β) (s : α ⟶ β) : α ⟶ β`):

```
csp.AC3 : (α β : Obj) → (Uα : CRel α α) → (Uβ : CRel β β)
        → Pl false α α → Pl false β β → Pl false α β → Pl false α β
```

| 做法                                                                                         | 解决哪条 | 代价                                                          |
|----------------------------------------------------------------------------------------------|----------|---------------------------------------------------------------|
| type 检查只看登记的 signature:调用处用 `bind` + `declared` 对 signature,不碰 body            | 1        | 无;每个参数和结果本来就必须声明 type(`Lang/Expand.lean:53`)   |
| `walk` 对 parametric def 也 build 一次并 emit,type variable 当作 rigid(`walk` 给 closed def 做声明检查时已经这样) | 2 | `Expand.emit` 多一条 "带 λ 的 constant" 路径 |
| type variable 变成 constant 的 `Obj` 参数;`Gen` 的函数本来就都收 `Obj` 参数                 | 3        | `Tm` 的 index 里要能出现 object variable —— 数据结构改动,见 L |
| 关系参数是 λ 绑定的变量,和 fixed point 的 `X` 用同一个机制(`ρ`,`Lang/Expand.lean:177`)       | 4        | `fv`/`closed` 要分清 "参数" 和 "fixed point 变量"             |
| body 用到 universe 的每个 type variable 多一个参数 `Uα`;调用处传它 instantiate 到的 object 的 universe | 5 | signature 变长;`≤`、`succ`、算术在 type variable 上要的是 `Arr .long m`,这种 variable 固定为 `.long`,只对 universe 泛化 |
| 参数和结果都是 PLAN(`Gen.Pl`),不是 table:一次调用是一个 plan 节点,plan 在 run time 按这次调用的实参造出来,和现在一样穿过 `sup` | 6 | 没有 bit rule 的 body 包成 `pleaf`;要 table 的地方跑 `Bits.runC` |
| `arcs` 把参数当 closed;只依赖参数的子项用 Lean `let` 提到 `fun X` 外面(生成的代码里的 `let`,不是 Rel 里的) | 7 | `share`(`Lang/Expand.lean:184`)要多一种 "提到 λ 之内、`fun X` 之外" 的情况 |
| constant 的参数固定为 `d = false`(closed 关系)                                               | 8        | 需要 key 的实参不能直接传,见 M                                |
| 调用处在 `Tm` 里是一个新叶子:constant 的名字加实参                                           | 1, 6     | `Tm` 多一个 constructor —— 数据结构改动,见 L                  |

- 这样每个调用仍然各自 plan:plan 是 constant 在 run time 的返回值,是实参的函数,矩阵大小照旧从叶子读。
- 没有做原型。主要风险是第 3 条:`Tm` 被 `BitsSpec*.lean` 的证明和 `Obj.El` 用着,index 里加 variable
  会动到它们。动手之前先做一个只针对 `AC3` 的 spike。
- 第 9 条(family 实参)不被上面的 constant 覆盖,见 M。

#### 对 SudokuPC9 那 ~3 s 的影响

- 现在:`sudokupc9` 的 elaboration 包括重新 `walk` 一遍 prelude,以及把 `AC3`、`sup`、`pc` 的 body 在每个
  使用处 elaborate、build、转成 Lean `Expr`、`addAndCompile`,全部在 IR interpreter 里跑。
- 之后:prelude 和 `csp` 的 body 各在自己的文件里做一次。`sudokupc9` 只剩 3 个 `obj`、两个字面量
  (`unit` 243 对、`g` 17 对)和 6 行 application,每行一个小 constant。
- 3 s 里有多少花在 prelude 和展开的 body 上、多少花在字面量上,没有量过。动手前用 `perf record` 分开;
  如果大头是字面量,`board9`(J)才是去掉它的那一步。
- `Lang` 仍然在 IR interpreter 里跑;native(`precompileModules`)和 module 无关,见 K。
- run time 不应变化:plan 的形状和 `nuAC` 的识别都保留。这一条要由 `SudokuPC9` 的运行时间来验证。

## 3. 发现

- F1. `.` 现在是合法的关系名(`Parse.isSym '.'` 成立)。把它 reserve 之后,定义了 `.` 的 program 会坏;
  `Op.table` 里没有,`Programs/` 下的 program 没有搜过。
- F2. "本地名字赢过 open 进来的名字" 是凭记忆写的 Lean 规则,未验证。如果 Lean 实际报 ambiguous,2.1 的
  例子不受影响(它们用 qualified 和 selective),只有 `open csp` 整个打开再本地重定义的写法会报错。
- F3. object variable 在 body 里读不到。`s₀ ≜ g°\𝟙(D)` 提到了 `D`;泛化后的 `s₀(g) ≜ g°\𝟙` 靠声明的 type
  推出 `𝟙 : β ⟶ β`。未验证。推不出来的话,修法是让 signature 的 variable 在 body 里可见(`𝟙(β)`),
  这正是 Lean 对 `{β}` 的规则。
- F4. `Expand.walk` 跳过 `check` 和 `print`;它们只在 `Eval.runProgram` 里跑。下面的测试需要 stage 2 的
  runner 来算 `check`。
- F5. `doc/rel-lang-design.md` 的 "The prelude" 一节还在说 `prelude.rel.md` 由 `include_str` 读入;prelude
  现在是 `Programs/Prelude.lean`。
- F6. 每个声明的 base object 的 `Obj` 都是 `.long`(`Lang/Elab.lean:1176` `objOf`);`Cell`、`Unit`、`D` 的区别
  只在 universe。所以 object 的 constant 和 type variable 都带两样东西:`Obj`(存储类型)和 universe(元素)。
- F7. `open csp` 整个打开会把 `csp` 的全部名字加进字母串的切分:打开一个定义了 `pc` 的 module 之后,
  `pc` 不再是 `p` 再 `c`。这是现在 prelude 就有的情况;selective `open csp (AC3)` 只加一个名字。
- F8. 这个设计不需要 host loop、Rel 文本里的 Lean `let`、或 lambda。

## 4. 实现计划(问题 5)

| 步 | 文件                                               | 改动                                                                              |
|----|----------------------------------------------------|-----------------------------------------------------------------------------------|
| 1  | `Lang/Expand.lean`(或新文件)                       | environment extension:登记 def 和 object;`emit` 把 `n.rel.x` 改成 `n.x`,辅助 constant 改名 |
| 2  | `Lang/Parse.lean`、`Lang/Embed.lean`               | resolver 字段;`.` reserved;`name`/`isInfix`/`oprim`/`fresh` 按 2.3 的表改;删 `scope`、`after ident`;加 `ident "." relSym` |
| 3  | `Lang/Elab.lean`、`Lang/Expand.lean`               | `elabE`、`oty` 查不到时问 resolver;删 `defsOf` 对 prelude 的 `walk` 和 `preludeDef`;`perm` 的标记 |
| 4  | spike:`Lang/Elab.lean`、`Lang/Expand.lean`、`Lang/Gen.lean` | 只对 `AC3`:2.4 的 constant,手工核对它在 `SudokuAC` 上给出同一个 `s`、走 `nuAC`;定下 L、M、N |
| 5  | `Lang/Elab.lean`、`Lang/Expand.lean`、`Lang/Gen.lean` | 2.4 全部:`Tm` 的调用叶子和 object variable、signature-only 的 type 检查、带 λ 的 emit、plan 进 plan 出、`arcs` 和 `let` 提升 |
| 6  | `Programs/*.lean`、`Lang/ExpandTest.lean`、各 `Test*.lean` | 每个文件 `after prelude` 换成 `open prelude`;新的 `Programs/CSP.lean`;`SudokuAC/PC/PC9` import 它 |
| 7  | `Programs/Board9.lean`(新)                         | 可选,量过之后再定:`board9`                                                        |

- 第 3 步之后、第 5 步之前有一个中间状态:外面的 parametric def 已经只能通过 constant 到达,但 constant 还
  没有。所以 3 和 5 要一起落地,第 4 步的 spike 在它们之前。
- `Lang/Eval.lean` 不碰(stage 2 删它)。

测试:

| 要证明的                                         | 测试                                                                            |
|--------------------------------------------------|---------------------------------------------------------------------------------|
| 共享的 `AC3`/`K` 算出的和拷贝算出的一样          | `SudokuPC`:`check s = {…}`、`check s' = {…}`(精确的表);`SudokuAC`:`check s = sol`、`check s = s₀ ∩ (peer\(s ≠))`;`SudokuPC9`:`check s' ⊑ s`;各自的 `#guard` |
| 其他 program 不变                                | `Lang/ExpandTest.lean` 跑过所有 program                                         |
| 只 elaborate 一次                                | `csp.AC3` 存在;`sudokuac`、`sudokupc`、`sudokupc9` 的 `s` 的值是 `csp.AC3` 的 application;三个 program 自己的 constant 里没有 `Gen.nuAC` |
| plan 仍然穿过调用                                | `LEETQ_CHECK=paths` 下 `sudokupc9` 的 `pc` 走 "LEETQ bits",不走 "LEETQ table"   |
| elaboration 时间                                 | `sudokupc9` 的 `rel_program` 前后各量一次,和 3 s 比                             |
| qualified 不冲突                                 | `sudokupc9` 在 `csp.s₀`、`csp.K`、`csp.s'` 旁边定义自己的 `s₀`、`K`、`s'`       |
| selective                                        | `sudokuac`:`open csp (AC3)`,body 里 `AC3(…)` 和 `csp.peer(unit)` 都能用;没有 `open` 时 `AC3` 报 unknown |
| 两个 `open` 同名                                 | 一个报 ambiguous 的 program,比对报错文本                                        |
| 没有 `open prelude`                              | `≠` 报 unknown;`prelude.«≠»` 存在                                               |
| 封闭性:qualified                                 | body 里写 `Nat.add`,报 "`Nat.add` is not a Rel definition"                      |
| 封闭性:`open` 进来的                             | 文件头 `open Nat`,body 里写 `add`,同样报错;写 `succ` 得到 kernel 表的 `succ`    |
| 封闭性:type 对也不行                             | 文件里手写 `def fake : CRel .long .long := …`,body 里写 `fake`,同样报错         |
| 切分不受非 Rel constant 影响                     | `open Nat` 前后,同一个 program 的 AST 相同                                      |
| 生成的代码不出边界                               | 对每个 program:`n.*` 的值里的 constant 都在 registry 或 `Gen`/`Bits` 里(`emit` 的检查,加一个故意违反的 internal 测试) |
| 符号名                                           | `open csp («≼»)` 之后 `R ≼ S` 能读;`csp.≼` 能读                                 |
| 字母串的切分                                     | `csp.AC3peer` 读成 `csp.AC3` 再 `peer`;`Rcsp.AC3` 读成 `R` 再 `csp.AC3`         |
| 没有剩下的拷贝                                   | `AC3`、`sup`、`pc` 各自只在一个 `rel_program` 里定义                            |

## 5. 已决定(2026-11-15)

| # | 决定                                                                                                          |
|---|---------------------------------------------------------------------------------------------------------------|
| E | prelude 跟 Lean 一样:每个文件显式写 `open prelude`;`rel_program` 不自动打开任何东西                           |
| F | Rel 名字只解析到 registry 和 kernel 表;scope 借用 Lean 的 `open`,再过滤                                      |
| G | Rel def 的 constant 叫 `csp.AC3`;辅助 constant 改名,不再有 `.rel.` 这一层                                      |
| H | 允许 selective 打开符号名:`open csp («≼»)`                                                                    |
| I | 不支持独立的 `.rel` 文本文件:program 只写在 Lean 文件里,只有这一种方式                                       |
| J | 做 `board9` module(第 7 步)                                                                                  |
| K | native(`precompileModules`)单独做(rel-140b),不并进这项工作                                                 |
| L | `Tm` 的 index 允许 object variable,并加一个调用叶子(数据结构改动,已批准)                                   |
| M | 需要 key 的实参(`d = true`)和 family 实参报错;constant 只收 closed 关系                                      |
|   | 第 5 步之前的例外:family 实参、或 object variable 不是声明过的 object 时,这次使用展开 body,记进 `n.notCalled`(被调的 constant、位置、原因) |
|   | 第 5 步之前的例外:body 做不成 constant 的定义(type variable 上的算术、复合 object 的 universe)在每次使用处展开,记进 `n.notOnce`;第 5 步让两张表都空,之后两者都报错 |
| N | object 是 "`Obj` 加 universe" 的一个 structure,每个 type variable 收一个这样的值(数据结构改动,已批准)       |

## 6. 证明 `rel_program` 的定义:等式风格(elaborate-once 之后的一步)

只是设计。没有 elaborate 过下面任何一段 Lean;标了"未验证"的是读源码推出来的。第 5 节的 E–N 照旧有效,本节不改它们。

本节已决定(2026-11-15;字母是本节自己的,和第 5 节的 E–N 无关,本节提到第 5 节的决定时写 "5-G" 这样):

| # | 决定                                                                                          | 在哪    |
|---|-----------------------------------------------------------------------------------------------|---------|
| D | literal def 和 `obj` 是 `.aop` constant 的参数;书的 model 靠代入得到                          | 6.5     |
| L | registry 的每个条目存 def 的 body(`Lang.Expr`)(数据结构改动,已批准)                         | 6.4     |
| N | 单独的 Lean command `rel_aop` 生成 `.aop` constant;run path 不 import AOP                     | 6.4     |

被否决的选项各一行在 6.9。

### 6.1 现状

| 东西                     | 现在                                                                            | 位置                              |
|--------------------------|---------------------------------------------------------------------------------|-----------------------------------|
| `rel(t)`                 | 把 Rel term 读成 AOP allegory 的 term;`calc` 的每一步写 Rel,理由写 AOP 的定律   | `Lang/Calc.lean:254`              |
| `rel(t)` 里的名字        | 只能是 statement 的 local variable;别的报 "is not a local variable"             | `Lang/Calc.lean:164`–`:168`       |
| `rel(t)` 里的 Rel def    | `.app`/`.inf` 报 "is a Rel definition, and rel(…) has none"                     | `Lang/Calc.lean:212`              |
| prelude                  | 一张手写的表,只有 `∈`                                                           | `Lang/Calc.lean:96`               |
| program fold `⦇e,S⦈`     | 报错,要求改写成书上的 `⦇[e,S]⦈`                                                 | `Lang/Calc.lean:210`              |
| literal、`at(i)`、`setify`、μ/ν | 报错:没有 AOP 对应物                                                     | `Lang/Calc.lean:203`–`:213`       |
| Rel def 的 executable    | `n.rel.x : CRel A B`                                                            | `Lang/Expand.lean:577`            |
| executable 的含义        | `n.rep_x : (n.rel.x).ok = true → rep (n.rel.x).rel = T`,`T : Den A B`           | `Lang/Expand.lean:580`–`:590`     |
| `T` 是什么               | `Rel(Set)` 里 `⟨A.El⟩ ⟶ ⟨B.El⟩` 的一个 term,由 `GenSpec` 的引理逐节点拼出,inline 在 `rep_x` 的 type 里,没有名字 | `Lang/GenSpec.lean:21`, `:36` |
| 拼不出 `T` 的 def        | 进 `n.unproved`,带上第一个没有引理的 combinator                                 | `Lang/Expand.lean:607`            |
| program 里的 `check`     | 只在有限数据上求值,例如 `mss` 对它的 derived program                            | `Programs/Mss.lean:34`–`:35`      |

所以现在能用 `calc` 证的只有"对任意 `R S` 成立"的定律(`Lang/CalcTest.lean`);关于 `mss`、`sort(Q)` 这些
def 的命题写不出来,因为 `rel(…)` 不认识它们的名字。

### 6.2 两种读法(先定义,下面都用这两个词)

一个 Rel def `m.x` 有两种含义,它们不是同一个东西:

| 读法        | 是什么                                                                  | 在哪个 allegory                         | 现在有没有          |
|-------------|-------------------------------------------------------------------------|-----------------------------------------|---------------------|
| AOP 读法    | `rel(body)` 给出的 term:`Calc.toTerm` 对 body 的翻译                    | statement 的 allegory `𝒜`,object 是 Lean 的 | 没有(名字不认识)  |
| `Den` 读法  | `rep_x` 右边的 `T`                                                      | `Rel(Set)`,object 是 `⟨A.El⟩`           | 有,但没有名字      |

两种读法在这些地方不同(`doc/rel-lean-mapping.md` 的 note [7] [8] [9] 和 `GenSpec`):

| 构造               | AOP 读法                         | `Den` 读法                                                     |
|--------------------|----------------------------------|----------------------------------------------------------------|
| `[α]`、`𝒫α`        | `dList A` 和 `P A` 是两个 object | 同一个 array type                                              |
| `∋`、`Λ`、`est`、`thin` | 在 power object `P A` 上    | 在 array 上;`mem_sound` 的 `T` 是 `fun xs x => x ∈ xs`         |
| `obj N = lo…hi`    | 没有;书的 model 是全的 `Int`     | 有限 universe,算术出范围就没有值                               |
| `R/S`、`R\S`       | `DivisionAllegory.div`、`leftDiv` | 限制在 universe 里的公式(`ldivDen`,`Lang/GenSpec.lean:288`)   |
| `R − S`、`⊤`       | `sub`(Boolean)、`topHom`/`topMor` | `fun x y => TR x y ∧ ¬TS x y`、`relTop ≫ TV`                  |
| fold、`Λ`、`est`、list builtin、算术 | `relCata` 等          | `GenSpec` 没有引理,def 落进 `n.unproved`                       |

- AOP 的定理(`greedy`、`thinning_est`、`mss_eq_scan`)都是关于 AOP 读法的。等式风格的证明因此证的是 AOP 读法。
- `Den` 读法是 executable 和证明之间唯一已有的定理。把两种读法连起来是 6.4 的 gap G3–G5,排在最后一个 stage。

### 6.3 `rel(t)` 怎么解析 Rel def 的名字(问题 1)

同一个 resolver,不是第二套查找:

- 2.3 的 resolver 是一个函数:字符串 → registry 里的 constant(及其 arity、infix、signature)。它读
  `getEnv`、`getCurrNamespace`、`getOpenDecls`。`rel_program` 把它放进 `Parse.S` 的 resolver 字段;
  `Calc.elabRel`(`Lang/Calc.lean:256`)在读 `rel(t)` 时放进同一个字段。
- theorem 写在 Lean 文件里,它所在位置的 `namespace` 和 `open` 就是 scope。`open mss (mss oplus w)` 写在
  theorem 之前,和写在 `rel_program` 之前是同一条 Lean 语句、同一个过滤。
- 解析顺序是 2.3 "边界" 一节的三步,只有第 1 步的内容不同:

| 步 | `rel_program` 的 body                       | `rel(t)`                                   |
|----|---------------------------------------------|--------------------------------------------|
| 1  | 参数、fixed point 变量、本 program 的名字   | statement 的 local variable(现在的 `vars`) |
| 2  | kernel 表                                   | kernel 表                                  |
| 3  | `resolveGlobalName` 的候选,只留 registry 里的 | 同左                                     |

- local variable 赢过 registry 里的名字,和 Lean 的 local 赢过 global 一致。
- 字母串的切分(`Parse.name` 的最长前缀)用同一批名字,所以 F7 在这里同样成立:`open mss` 整个打开会把 `w`、
  `A`、`D`、`x`、`K` 加进切分。证明文件用 selective `open`。
- `Calc.toTerm` 要改的三处:`.name`(`:164`)查不到 local variable 时问 resolver;`.app`、`.inf`(`:212`)不再
  报错,变成 "AOP constant 作用到各实参的 `toTerm`"。
- `Calc.prelude` 这张表(`:96`)删掉:`∈` 经 `open prelude` 解析到 `prelude.«∈»`,和别的 def 一样。
- 报错沿用 2.3:"`x` is not a Rel definition";另加一条 "`x` has no AOP reading: <第一个没有 AOP 对应物的构造>"。

### 6.4 一个 Rel def 的 AOP 含义(问题 2)

是一个 Lean def,`calc` 的一步能把它展开。

- 对 registry 里的每个 def `m.x`,生成一个 Lean constant,记作 `m.x.aop`(名字待定;registry 里没有它,所以
  Rel body 和 `rel(…)` 都拼不出来,符合 5-G):
  - value 是 `Calc.toTerm` 对 `m.x` 的 body 的翻译,和 `calc` 步里的 `rel(body)` 走同一段代码;
  - body 里提到的别的 def 是它们的 `.aop` constant 的 application,不是 body 的拷贝(elaborate-once 的 AOP 一侧);
  - `rel(x)` elaborate 成 `m.x.aop` 的 application。
- `≜` 步:`rel(mss) = rel(Λ(segment ⦇[zero,plus]⦈) est(≥)) := rfl`。两边 elaborate 之后一边是 constant,一边是
  它的 value,`rfl` 靠 delta 成立。不需要新的 tactic;要显式的话 `by unfold`。
- 生成的 def 的 binder(细节见 6.5):

| body 里的东西                                      | binder                                                        |
|----------------------------------------------------|---------------------------------------------------------------|
| type variable `α`                                  | `{α : 𝒜}`                                                     |
| 关系参数 `Q : α ⟶ α`                               | 显式 `(Q : α ⟶ α)`                                            |
| allegory                                           | `{𝒜} [TabularUnitaryUnguardedPowerLCDA 𝒜]`;用到 `∼`、`−` 再加 `[BooleanAllegory 𝒜]` |
| `rel(…)` 不写的 witness(`RelProd`、`Coproduct`、`InitialAlgebra`、`Relator`) | 每个 hole 一个 binder;使用处仍由 `Calc.fill` 从 statement 的 context 取 |

- allegory 的 class 先固定为 `CalcTest` 的 `Fold`、`Power` 两节用的那一个;按 body 推最弱的 class 等有第二个
  需要它的例子再做。
- 在哪里生成:不在 `rel_program` 里。`Lang/Embed.lean` 不 import AOP,`Lang/Calc.lean` import 了十个 AOP/Freyd
  module(`Lang/Calc.lean:1`–`:11`);在 `rel_program` 里生成会让每个 program 都依赖它们。所以是证明文件里的一条
  Lean command,`rel_aop mss`(决定 N):从 registry 读出 program `mss` 的每个 def 的 AST,各 emit 一个 `.aop` constant。
  - registry 的条目多存一个字段:def 的 body(`Lang.Expr`)(决定 L)。
  - `rel_aop` 是 Lean 一侧的 command,在 `rel_program` 之外,不是 Rel 语法。
  - run path(`LeetQ/Run/`,唯一 precompile 的库)因此不 import AOP:`rel_aop` 和 `Lang/Calc.lean` 留在 `LeetQ/Rel/`。

和 executable 的关系,以及 gap:

| #  | gap                                                                                             | 谁来补                       |
|----|-------------------------------------------------------------------------------------------------|------------------------------|
| G1 | AOP 读法没有 constant:`rel(…)` 不认识 def 的名字                                               | 本节 6.3、6.4                |
| G2 | `Den` 读法没有名字:`T` inline 在 `rep_x` 里,每个引用它的 def 再 inline 一遍                    | elaborate-once 第 5 步顺带:`rep_x` 的右边引用被调用 def 的 `T` |
| G3 | 没有定理连接两种读法。需要一个新定理,不是现有的 `rep_*`/`const_sound`:`m.x.sound : (m.x).ok = true → rep (m.x).rel = m.x.aop` 在 executable 的 model 上的实例 | stage 6 |
| G4 | G3 的右边要有意义,executable 的 model 必须是 6.2 第二张表每一行的 model:array 当 power object、有限 universe 上的除法。这些等式现在没有陈述 | stage 6 |
| G5 | `GenSpec` 对 fold、`Λ`、`est`、`thin`、list builtin、算术没有 `*_sound` 引理,所以 `mss` 这类 def 连 `rep_x` 都没有(推断:`Lang/GenSpec.lean` 全文只有 leaf、allegory 运算、bit plan 三组;没有查 `mss.unproved` 的值) | stage 6 |

- `rep_*` 和 `const_sound` 不动。它们说的是 "executable 算出 `T`";G3 说的是 "`T` 就是 AOP 读法"。两个定理
  合起来才是 "executable 算出证明里的那个关系"。
- G3–G5 补上之前,等式证明和 executable 之间的证据仍然是 `check`(有限数据)。这一点要写在每个这样的
  theorem 的 docstring 里,不能让 theorem 读起来像是关于 executable 的。

### 6.5 statement 量化的是什么(问题 3)

| def 的种类                              | 例子                            | `.aop` 的形状                                   | statement 量化的东西                         |
|-----------------------------------------|---------------------------------|-------------------------------------------------|----------------------------------------------|
| body 全在 `rel(…)` 的 fragment 里       | `frac(R,S)`、`cor(S)`、`csp.peer(unit)` | 对 `𝒜`、object、参数泛型的 def            | 所有 allegory、所有 object、所有实参         |
| 带关系参数                              | `sort(Q)`、`filter(p)`          | `(Q : α ⟶ α)` 是显式参数                        | 所有 `Q`:`theorem (Q : A ⟶ A) : rel(sort(Q)) = …` |
| body 用到 list builtin 或算术           | `sort(Q)`、`segment`、`oplus`   | AOP 只在 `Rel(Set)` 里定义了它们(`ListRel.*`) | `𝒜` 固定为 `RelSet`;量化 Lean 的 `A : Type` |
| body 是 literal,或 type 里有 `obj`      | `zero ≜ {(∗,0)}`、`N = -10…20`  | 自己没有 `.aop`;是用到它的 def 的 `.aop` 的参数(D) | 所有 model;书的 model 是一次代入          |
| body 用到 μ/ν、`at(i)`、`setify`、lifting | `csp.AC3`、`csp.K`            | 没有;registry 记下第一个这样的构造             | 写不出 statement;`rel(AC3(…))` 报错         |

- 参数在 statement 里是 local variable,没有 demand bit,也没有 family:5-M 的限制("constant 只收 closed 关系")
  只管 executable,不管 `.aop`。
- list 和算术这一行需要 `Calc.powers`(`Lang/Calc.lean:90`)旁边的第二张表:builtin → 它在 `Rel(Set)` 里的 AOP
  declaration(`cons`、`nil`、`cat`、`inits`、`plus`、`≤`、`sum`、`length` …,即 `doc/rel-lean-mapping.md` Table A
  里 status 是 same 或 differs [8] 的那些行)。`Calc.power`(`:111`)已经会按 declaration 的 binder 作用它,并在
  statement 的 allegory 不对时报错;不需要新机制。
- `sort(Q)` 另有一个已知的缺口:Rel 的 `ordered(Q)` 是公式,AOP 的 `ordered` 是递归谓词,两者相等没有陈述
  (mapping 的 note [14])。要 reuse AOP 关于 `sortSpec` 的定理,先证这一条。
- program fold `⦇e,S⦈` 要一条翻译规则(现在是报错):`⦇e,S⦈` 读成 `⦇[⊤e, S]⦈`,`⊤ : 1 ⟶ V`,`e` 是 seed 的
  coreflexive。`ran(zero)` 这种 seed 给出 `⊤ ran(zero)`,它等于 `zero` 需要 `zero` 是 map(一步 `calc`)。未验证。

literal 和 `obj`(决定 D):

| literal def 和 `obj` 的 AOP 读法                                           | statement 说的是                   | 代价                                                        |
|----------------------------------------------------------------------------|------------------------------------|-------------------------------------------------------------|
| 没有读法;它们是用到它们的 def 的 `.aop` 的参数:`obj N` 是 `{N : 𝒜}`,`zero` 是 `(zero : 1 ⟶ N)`。`rel(mss)` 从 statement 的同名 local variable 取 | 对每个 model 成立;书的 model 是一次代入 | statement 要写出 `zero` 和它的假设;范围 `-10…20` 不出现在命题里 |

- D 不发明 model:书的 model 和(以后的)executable model 都是同一个 def 的实例。
- 书的 model 的写法:statement 把 literal 列成 binder 加一条等式假设(`(zero : …) (hz : zero = MSS.zero)`),
  证明第一步 `subst`;6.6 的骨架就是这样。

### 6.6 目标例子:`mss = ⦇k⦈ π₂ est(≥)`(问题 4)

AOP 一侧已有的(索引 db,行号对过源文件):

| 声明                              | 位置                     | statement                                                             |
|-----------------------------------|--------------------------|-----------------------------------------------------------------------|
| `Freyd.Alg.RelSet.MSS.mss`        | `AOP/A7_7_MSS.lean:106`  | `dCL Unit Int ⟶ ⟨Int⟩ := (segment ≫ sum)%∋ ≫ est(geq)`               |
| `MSS.k`                           | `AOP/A7_7_MSS.lean:756`  | `Alg (F Unit Int) ⟨Int × (Int → Prop)⟩`,由 `wstep`、`tailSet` 写成    |
| `MSS.mss_eq_scan`                 | `AOP/A7_7_MSS.lean:993`  | `mss = ⦇k⦈ ≫ graph (fun p => p.2) ≫ est(geq)`                         |
| `ListRel.segment`、`ListRel.sum`  | `AOP/A5_6_ListCombinators.lean:311`, `:323` | `dList A ⟶ dList A`、`dList A ⟶ ⟨A⟩`               |

能不能 reuse:能,但只在书的 model 上,而且两端各要一组桥。

- `mss_eq_scan` 不是泛型定理:它在 `RelSet.{0}`、`Int`、`ConsList Unit Int`、`Int → Prop` 上逐点证出来
  (`oplusFn`、`scanFn`、`mssPreFn`)。所以结论是关于书的 model 的,不是关于 `N = -10…20` 上的 array 程序的。
- 左端的桥:`rel(mss)` 展开之后等于 `MSS.mss`。需要 `segment`(Rel 写成 `tails ∋ inits ∋`)等于
  `ListRel.segment`,program fold `⦇ran(zero),plus⦈` 等于 `ListRel.sum`。
  - `tails ∋` 里的 `∋` 作用在 list 上;`rel(…)` 把 `∋` 读成 `PowerAllegory.eps`,type 对不上。在 D 之下 `segment`
    因此没有 AOP 读法,成为 `mss.aop` 的参数,在书的 model 上代入 `ListRel.segment`。
- 右端的桥:Rel 写的 `[zero⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]` 等于 `MSS.k`。`MSS.k` 用逐点定义的 `wstep`、
  `tailSet` 写成,所以要三条引理:`wstep = (𝟙×π₁)oplus`、`tailSet = π₂π₂∋`、`⊤zero = graph fun _ => zeroVal`。
  源文件里有 `wstep_apply`(`:771`)、`tailSet_apply`(`:784`)、`discZero_zero`(`:251`)可以用。
- 书的 model 的 witness(`sumCop`、`rpair`、`CL.listInitial`,`AOP/A6_ConsList.lean:364`)是 def,不是 instance;
  `Calc.fill` 只从 context 或 instance search 找。证明文件要把它们声明成 local instance 或 hypothesis。未验证。

statement 和 `calc` 骨架(`Programs/MssProof.lean`,新文件):

```
import LeetQ.Rel.Programs.Mss
import LeetQ.Rel.Lang.Calc
import AOP.A7_7_MSS

namespace LeetQ.Rel.Programs
open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.MSS
open prelude
open mss (mss oplus w)                          -- Lean 的 open;registry 过滤后 rel(…) 认识这三个名字

rel_aop mss                                     -- 生成 mss.mss.aop、mss.oplus.aop、mss.w.aop

-- 书的 model 的 witness:rel(…) 不写它们,`fill` 从 context 取(未验证:是否要写成 hypothesis)
attribute [local instance] CL.listInitial

/-- B&dM Ex 7.40 在书的 model 上(`Int`、cons list、power object):Rel 的 `mss` 等于 Rel 写的 scan。
    不是关于 executable 的命题:`mss.rel.mss` 和它之间的证据是 `Programs/Mss.lean` 的 `check`。 -/
theorem mss_scan
    (zero : dL Unit ⟶ (⟨Int⟩ : RelSet.{0})) (hz : zero = MSS.zero)         -- literal `{(∗,0)}` 的读法
    (segment : dCL Unit Int ⟶ dCL Unit Int) (hs : segment = ListRel.segment) :
    rel(mss) = rel(⦇[zero ⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]⦈ π₂ est(≥)) := by
  subst hz hs
  calc rel(mss)
      = rel(Λ(segment ⦇[zero,plus]⦈) est(≥)) := rfl                        -- ≜ mss(program fold 已翻译)
    _ = rel(Λ(segment sum) est(≥)) := by rw [sum_eq_fold]                   -- 桥:⦇[zero,plus]⦈ = sum
    _ = MSS.mss := rfl                                                      -- ≜ MSS.mss
    _ = ⦇k⦈ ≫ graph (fun p : Int × (Int → Prop) => p.2) ≫ est(geq) := mss_eq_scan
    _ = rel(⦇[zero ⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]⦈ π₂ est(≥)) := by
        rw [k_eq, snd_eq_outr]                                              -- 桥:MSS.k 的拼法
```

- AOP 的证明一行都不重证:中间那一步就是 `mss_eq_scan`。新写的只有两端的桥(`sum_eq_fold`、`k_eq`、
  `snd_eq_outr`,名字是占位)和 `≜` 步。
- 第二、三步用到 `plus`、`≥`、`sum` 的 `Rel(Set)` 读法(6.5 的第二张 builtin 表),并假定 `MSS.plus`、`MSS.geq`
  和 `ListRel` 的那两个可以互相化简。未验证。
- 要得到关于 `N = -10…20` 的 array 程序的定理,需要 `mss_eq_scan` 的一个不依赖 `Int` 的版本(假设写成
  hypothesis)加上 G3–G5。那是另一项工作,不在这个目标里。

### 6.7 `rel_program` 里要不要证明语法(问题 5)

不要。

- Lean 的 `calc` 是唯一的证明语言。理由(右边的 term)是 Lean term,定律是 Lean 的 theorem;`rel_program` 里
  的证明语法要么把 Lean term 嵌进 Rel body(破坏 2.3 的边界),要么自己实现一套定律名字的查找和 congruence,
  是第二个证明检查器。
- note 的 `calc_steps`、`lean-calc(…)` 已经从 Lean 的 `calc` 画证明表;证明留在 Lean 里,图免费得到。
- 什么情况才值得加:
  - 有一个读者只能读 Rel 文本、读不了 Lean 文件。5-I 已经否决了独立的 `.rel` 文件,所以现在没有这个读者;
  - 或者证明步骤需要一条 Lean 的 `calc` 表达不了的 Rel 专有规则。现在没有这样的规则。
- 可以加、但不是语法的一样东西:一个 gate,列出每个 program 的每条 `check R = S`,报告哪些没有同名 statement
  的 theorem。它枚举的是 `check`(义务),不是 theorem(记录)。等有第二个带证明的 program 再做。

### 6.8 分阶段计划(问题 6)

owner:`Lang/*`、`CRel*`、`Rep*` 是 ffreyd;`Programs/*` 是 aima。"第 n 步" 指第 4 节的表。

| stage | 交付物                                                                                                                               | 文件                                                               | owner               | gate                                                                                                           | 规模         | 等 elaborate-once 吗      |
|-------|---------------------------------------------------------------------                                                                 |--------------------------------------------------------            |--------             |-----------------------------------------------------------                                                     |--------------|---------------------------|
| P0    | spike:6.6 的 theorem,Rel def 先手写成 Lean def(各一行 `rel(…)`),不碰 registry。按 D 写 statement;定下 witness 的写法、三组桥是否成立 | `Lang/CalcMssTest.lean`(新)                                        | ffreyd              | 该 module build;`#print axioms` 不比 `mss_eq_scan` 多                                                          | ~150 行      | 不等,现在就能做           |
| P1    | program fold 的翻译规则;list/算术 builtin 的 `Rel(Set)` 表                                                                           | `Lang/Calc.lean`、`Lang/CalcTest.lean`                             | ffreyd              | `CalcTest`:每个新构造一条 `guard_expr`,每个仍不支持的一条报错                                                  | ~80 行       | 不等                      |
| P2    | registry 多存 body;`rel_aop m` 生成 `.aop` constant                                                                                  | registry 所在文件、`Lang/Calc.lean`                                | ffreyd              | `rel_aop prelude` 之后每个 def 要么有 `.aop`,要么在 "no AOP reading" 表里带原因;两者之和等于 registry 的条目数 | ~150 行      | 等第 1 步(registry)       |
| P3    | `rel(t)` 用 2.3 的 resolver;`.name`/`.app`/`.inf` 解析到 `.aop`;删 `Calc.prelude`                                                    | `Lang/Calc.lean`、`Lang/CalcTest.lean`                             | ffreyd              | 测试:`rel(mss)` 能读;没有 `open` 报 unknown;手写的 Lean def 报 "is not a Rel definition";`≜` 步是 `rfl`        | ~100 行      | 等第 1–3 步(resolver)     |
| P4    | `mss_scan`,用真的 `rel(mss)`;P0 的 spike 文件删掉                                                                                    | `Programs/MssProof.lean`(新);桥引理放 `AOP/A7_7_MSS.lean` 或新文件 | aima(桥引理:ffreyd) | 该 module build;axioms 同 P0                                                                                   | ~120 行      | 等 P2、P3                 |
| P5    | 第二个例子,取一个带参数的 def(`sort(Q)` 或 `filter(p)`),含 note [14] 那条等式                                                        | `Programs/*Proof.lean`                                             | aima                | 同 P4                                                                                                          | 取决于 [14]  | 等 P3                     |
| P6    | 连接 executable:G2–G5                                                                                                                | `Lang/GenSpec.lean`、`Lang/Expand.lean`、`Rep*.lean`               | ffreyd              | 每个 program:`n.unproved` 为空的 def 都有 `m.x.sound`                                                          | 大,未估      | 等第 5 步                 |

- P0 和 P1 不依赖 module 的工作,可以和第 1–5 步并行;P0 先做,因为它验证 D 的 statement 写得出来,也决定 P2 的 binder 规则。
- P2–P4 只需要 registry 和 resolver(第 1–3 步),不需要 2.4 的 Gen 一侧(第 4–5 步)。
- P6 是唯一等 2.4 的:带参数的 def 要先有 executable 的 constant,才有东西可以陈述 `sound`。P6 不做,P0–P5 的
  theorem 照样成立,只是它们和 executable 之间仍然只有 `check`。

### 6.9 被否决的选项

决定是本节开头那张表的 D、L、N。没有剩下要他决定的。

| # | 选项                                                         | 否决的理由                                                                   |
|---|--------------------------------------------------------------|------------------------------------------------------------------------------|
| E | literal def 和 `obj` 固定读成书的 `Rel(Set)` model           | 枚举的 `obj` 要生成 Lean type(新结构);命题把有限的 `N` 说成了 `Int`(note [8]) |
| F | literal def 和 `obj` 读成 executable 的 model(`Den` 读法)   | AOP 第 7 章以后的定理陈述在 `Int`、`ConsList`、`P` 上,用不上;G5 的 def 没有 `T` |
| M | registry 不存 body                                           | `rel_aop` 在 `rel_program` 之外拿不到 def 的 AST,只能重新 parse 源文本,是 def 的第二份拷贝 |
| O | `.aop` constant 在 `rel_program` 里生成,不加 command         | 每个 program、连同 run path,都要 import `Lang/Calc.lean` 的十个 AOP/Freyd module |
