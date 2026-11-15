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
