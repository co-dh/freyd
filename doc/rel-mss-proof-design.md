# `mss` 的等式证明写在 `rel_program` 里 — 设计

只是设计,没有 elaborate 过下面任何一段。标 "未验证" 的是读源码推出来的。

- 目标(原话):Mss.lean 写出 mss 的几个版本,并证明最后的线性版本实现了 spec `mss = Λ(segment sum) est(≥)`;
  等式证明写在 `rel_program` 里,每一步的定律可以在 Lean 里证。
- 这一条改掉 `doc/rel-module-design.md` 6.7 的 "`rel_program` 里不要证明语法"。6.7 的理由(不要第二个证明检查器、
  Rel body 里不嵌 Lean term)仍然成立,本设计两条都守住:链生成 Lean 的 `calc`,Rel 文本里没有 Lean term。
- 下文 "6-D、6-L、6-N" 指 `doc/rel-module-design.md` 第 6 节的决定;本文自己的选项用字母 D、E、F(第 4 节)。

## 1. 现状(读到的)

| 东西                       | 现在                                                                                       | 位置                                  |
|----------------------------|--------------------------------------------------------------------------------------------|---------------------------------------|
| Rel 程序                   | spec `mss`、`oplus`、`w`,scan 只 inline 在两条 `check` 里,没有名字                         | `leetq/LeetQ/Rel/Programs/Mss.lean`   |
| Lean 的证明                | `mss_eq_scan` 已经是一个 `calc`,3 步:`mss_shape`、`mssPre_eq_oplus_cata`、`Kalg_snd_eq`    | `AOP/A7_7_MSS.lean:993`               |
| P0 spike(master e03261c)  | `mss_scan`,4 步 `calc`:`≜ mss`、`ListRel.sum_cata`、`MSS.mss_eq_scan`、`≜ k`;axioms `{propext, Quot.sound}` | `leetq/LeetQ/Aop/CalcMssTest.lean` |
| `rel(t)`                   | Rel term 读成 AOP term;名字只能是 local variable                                           | `leetq/LeetQ/Aop/Calc.lean:254`       |
| Rel 的语句                 | `obj`、def、`print`、`check e (⊑\|=) f`;def 的 body 可以是 test `e ⊑ f`(`Body.test`)       | `leetq/LeetQ/Run/Lang/Embed.lean:168` |
| `sum`                      | builtin(`Op.total`),所以 spec 可以直接写 `Λ(segment sum)est(≥)`                           | `leetq/LeetQ/Run/Lang/Syntax.lean:60` |
| lib 的划分                 | `LeetQRun`(precompile,run path)、`LeetQ`(`LeetQ.Rel.*`)、`LeetQAop`(唯一 import AOP 的) | `leetq/lakefile.lean`                 |

spike 的结论,下面直接用:

- 6-D 用 statement 里的 `let` 实现:每个参数和 witness 绑到书的 model 的一个 term,不需要等式假设。
- object 是 `{N : RelSet}`;product object 是一个 `RelProd` binder 的 apex `NN.p`。
- `RelProd`、`Coproduct` 是 structure,每个不同的 type 一个显式 binder,`Calc.fill` 按 type 取;`InitialAlgebra`
  (`CL.initial`)、`PowerAllegory`、`⊤` 不要 binder。
- `plus`、`sum` 是 builtin,local 不能叫这个名字;它们要有 `RelSet` 读法(P1 的 builtin 表)。`≥` 可以是 local `«≥»`。
- program fold `⦇ran(zero),plus⦈` 要读成书的 `⦇[zero,plus]⦈`(P1 的翻译规则)。
- spike 的第 4 步是 `simp only […]; rfl`,应当成为一条引理 `k_eq`。

## 2. mss 的版本(问题 3)

note 的推导(`diag/aop/07-optimisation.typ` §mss,B&dM Ex 7.40 的五个 display)经过下面五个版本。名字是占位,
取 note 的 label(`mss-shape`、`mss-prefix-sum`、`mss-step`、`mss-scan`)。

辅助定义(都在 program `mss` 里):

```
segment : [α] ⟶ [α] ≜ suffix prefix                       -- note: segment = suffix prefix;prelude 的 suffix、prefix
S : 1+N×N ⟶ N ≜ [zero, ⊤zero ∪ plus]                      -- note 的 S(Lean `MSS.Salg`)
oplus : N×N ⟶ N ≜ Λ(⊤zero ∪ plus)est(≥)                   -- 已有
g : [N] ⟶ N ≜ ⦇[zero,oplus]⦈                              -- note 的 g
w : N×(N×α) ⟶ N ≜ (𝟙×π₁)oplus                             -- 已有
k ≜ [zero⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]                    -- note :844,Lean `MSS.k`(:756)
```

| 版本     | 定义                                        | 说的是                               | 复杂度(长度 n) | executable          | 在数据上 check               |
|----------|---------------------------------------------|--------------------------------------|-----------------|---------------------|------------------------------|
| `mss`    | `Λ(segment sum)est(≥)`                      | spec:最大的 segment sum             | n³              | 是(现在就在跑)     | 是:`x mss`、`A mss`          |
| `shape`  | `Λ(suffix)E(Λ(prefix sum)est(≥))est(≥)`     | 每个 suffix 的最大 prefix sum 的最大 | n³              | 是(未验证)         | 新增 `check A shape = A mss` |
| `fused`  | `Λ(suffix)E(Λ(⦇S⦈)est(≥))est(≥)`            | `prefix sum` 融合成一个 fold         | n² 个候选       | 是(未验证)         | 新增                         |
| `greedy` | `Λ(suffix)E(g)est(≥)`                       | 贪心:每个 suffix 只留 `g` 的一个值  | n²              | 是(未验证)         | 新增                         |
| `scan`   | `⦇k⦈π₂est(≥)`                               | 一个 fold 带着 (当前值, 各 suffix 的值的集合) | 线性(note 的说法) | 是(现在 inline 在 `check` 里) | 是:两条已有的 `check` |

- spec 用 builtin `sum`,就是他写的形式。链的一步 `sum = ⦇[zero,plus]⦈` 是定律 `ListRel.sum_cata`(spike 已用)。
- `segment ≜ suffix prefix` 换掉现在的 `tails ∋ inits ∋`:后者的 `∋` 作用在 list 上,没有 AOP 读法(6.6);前者
  每一项都有(`suffix ≜ cat° π₂`、`prefix ≜ ⦇ran(nil), nil ∪ cons⦈`,要 P1 的 `cat`、`nil`、`cons` 读法)。
  在 `A` 上是否够快未验证;不够快就留 `tails ∋ inits ∋` 当 executable,加一条 `check A segment = A(tails ∋ inits ∋)`。
- 现在的 program fold 语法是 `⦇e,S⦈`;上面写的书的 `⦇[e,S]⦈` 在 `rel_program` 里还不能写(`Lang` 只有 program
  fold)。Mss.lean 里仍写 `⦇ran(zero),oplus⦈`,P1 的规则把它读成 `⦇[zero,oplus]⦈`。
- `scan` 的 "线性" 是 note 的说法(n+1 个 running maxima,`est(≥)` 再扫一遍)。executable 里 `Λ(w ∪ π₂π₂∋)` 每步
  重建一个 array,实际开销没有测。真正常数空间的版本(carrier 是 (当前值, 目前最大),`est(≥)` 融进 fold)note 和
  AOP 都没有,需要一条新定律;列为第 7 节最后一个可选 stage,不在本目标里。

## 3. `rel_program` 里的推导语法(问题 1)

一个新语句 `law`。先看一个例子,再给规则。

```
    law toShape : mss = shape                                     -- 没有链:证明欠 Lean 的
    law linear : mss = scan on A where                            -- 有链:证明由链生成
        mss = shape                                               by toShape
            = fused                                               by toFused
            = greedy                                              by toGreedy
            = scan                                                by toScan
```

一步是一行:`(= | ⊑) term by 理由`。例:`= Λ(suffix)E(prefix sum)est(≥)   by absorption`。

| 部分                    | 语法                                                        | 规则                                                                                  |
|-------------------------|-------------------------------------------------------------|---------------------------------------------------------------------------------------|
| statement               | `law n(params) : e (= \| ⊑) f`                              | `params` 就是 def 的 `relParam`;type variable 和 def 一样隐式                          |
| 链                      | `where` 后第一行 `e`,之后每行 `(= \| ⊑) term by 理由`       | 第一行必须是 statement 的左边,最后一行的 term 是右边;全是 `=` 才能证 `=`              |
| 理由:定律              | `by n` 或 `by n(args)`                                      | `n` 是一条 `law`;实参通常由 unification 得到,写出来是为了消歧                         |
| 理由:定义              | `by ≜ n`                                                    | 展开或折回 def `n`;关系符号仍是 `=`(CLAUDE.md:折回名字的一步是 `=`,不是 `≜`)       |
| 数据                    | `on A`(可选)                                               | 没有参数的 law:每一步另作 `check A e = A f` 求值,和已有的 `check` 同一条路          |
| 假设                    | 暂无                                                        | 带假设的定律(`f` 是 map、`R` reflexive)先写成一条具体的 law、欠 Lean;见第 7 节 S7 |

定律的名字怎么解析:同一个 registry、同一个 `open` 边界,不设第二张定律表。

- `law` 是 registry 里的一个条目,多一个 kind 字段(def 或 law)。`by` 后面的名字走 2.3 的 resolver,只收 law;
  term 里的名字只收 def。错位各报一条:"`absorption` is a law, not a relation"、"`segment` is a definition; write
  `by ≜ segment`"。
- 通用定律写在 prelude 里,`open prelude` 之后可用,例:
  `law absorption(S : α ⟶ β, R : β ⟶ γ) : Λ(S)E(R) = Λ(S R)`。
- Rel 文本里没有 Lean 的名字。定律的 statement 只有 Rel 这一份;Lean 只给证明(第 4 节)。所以 "理由印定律的公式"
  (CLAUDE.md:A REFERENCE NAMES THE ROW)直接从 registry 读得到。
- 和已有概念的关系:`law` 的 statement 是 `check e (⊑|=) f` 加名字和参数,形状同 `Body.test`。新的只有两样:
  `=`、链。AST 上是 `Decl` 的一个新 constructor(数据结构改动,要他批准):
  `law (p) (n) (ps : List Param) (e f : Expr) (eq : Bool) (on : Option Expr) (steps : List (Bool × Expr × Why))`,
  `Why` 是 `law n args` 或 `unfold n`。

`rel_program` 自己(不 import AOP)对一条 law 做的检查:

| 检查                                              | 失败时                                          |
|---------------------------------------------------|-------------------------------------------------|
| 每一步两边的 type 相同(Rel 的 elaborator)       | 报该行的 type                                   |
| 链的首尾是 statement 的两边                       | 报不一致的那一端                                |
| `by` 的名字是 scope 里的 law;`≜ n` 的 `n` 是 def | 报名字                                          |
| 有 `on A`:每一步在数据上成立                     | 和 `check` 一样把 `n.ok` 置 false,报该行        |

## 4. 链怎样变成 Lean 的 `calc`(问题 2),以及和 6-N 的关系

6-N:`.aop` constant 由 `rel_program` 之外的 command `rel_aop` 生成,run path 不 import AOP。本设计不改 6-N:
链存在 program 里(AST 的一部分),由 `rel_aop` 检查。

`rel_aop` 的形状(在 `LeetQAop` 的一个文件里):

```
import LeetQ.Rel.Programs.Mss
import LeetQ.Aop.Calc
import AOP.A7_7_MSS

rel_aop mss
  model   N := (⟨Int⟩ : RelSet.{0}), zero := MSS.zero       -- 6-D:obj 和 literal 的一次代入(书的 model)
  proof   toShape := …, toFused := …, toGreedy := …, toScan := …   -- 没有链的 law,各一个 Lean term
```

它按 program 的声明顺序做三件事:

| 声明          | 生成                                                                                               | 谁检查                 |
|---------------|----------------------------------------------------------------------------------------------------|------------------------|
| def `x`       | `mss.x.aop`,value 是 `Calc.toTerm(body)`(6.4);binder 按 spike 的规则                            | Lean elaborator        |
| law,没有链   | `theorem mss.n.aop : rel(e) = rel(f)`,在 `model` 的 `let` 之下;证明是 `proof` 块里的 term        | kernel                 |
| law,有链     | 同样的 statement;证明是生成的 `calc`,每步 `_ = rel(term) := by rel_step <理由的 .aop theorem>`    | kernel                 |

- 链就是一个 Lean `calc`:生成的是普通 theorem,`calc_steps mss.linear.aop` 和 note 的 `lean-calc(…)` 照常能画
  (未验证:`calc_steps` 读 `by rel_step h` 的定律名)。没有第二个检查器。
- `rel_step h` 是一个小 tactic,只做 "一条定律在 congruence 之下":
  1. `exact h`;2. `rw [h]` 或 `rw [← h]` 后 `rfl`;3. 两边用 `Cat.assoc` 右结合后,用 `h` 和它的带尾形式
  (`l ≫ Z = r ≫ Z`)再试;`⊑` 的步:`exact h`,或两边剥掉相同的前缀、后缀(`comp_mono_left/right`)后 `exact h`。
  - 需要第 3 条的原因:Rel 的并置是平的,Lean 的 `≫` 是二元的;`mss_eq_scan` 自己的第三步就是
    `rw [← Cat.assoc, ← Cat.assoc, Kalg_snd_eq]`。
  - 失败的报错:哪一行、定律的公式、改写后剩下的 goal。
- `by ≜ n` 生成 `rfl`(delta),不行则 `by unfold mss.n.aop; rfl`。
- 没有链、`proof` 块里也没有 term 的 law:`rel_aop` 报错,列出每一条和它的 statement(枚举的是 law 这个义务)。
- 错的一步在哪里失败:

| 错法                                 | 在哪里失败                                     |
|--------------------------------------|------------------------------------------------|
| type 不对、定律名不存在              | `rel_program`(`lake build LeetQ`)            |
| type 对但在数据上不成立(有 `on`)   | `rel_program`                                  |
| 不是所引定律的实例                   | `rel_aop` 生成的 `calc`(`lake build LeetQAop`)|

要他定的一件事:`rel_aop mss` 这一行放在哪里。

| 选项 | 做法                                                                       | 得到                                              | 代价                                                                   |
|------|----------------------------------------------------------------------------|---------------------------------------------------|------------------------------------------------------------------------|
| D    | 链在 `Programs/Mss.lean`;`rel_aop mss` 在 `LeetQ/Aop/Mss.lean`(推荐)     | 6-N 原样;`LeetQ` lib 和测试不加载 AOP            | `Programs/Mss.lean` 绿不等于链已证;要一个覆盖 gate(下)               |
| E    | `Mss.lean` 整个搬进 `LeetQAop`,`rel_aop mss` 写在文件末尾                 | 一个文件:程序、链、证明;build 绿就是已证         | import 它的测试(`TestMss`)连带加载 AOP;带证明的程序和别的程序分两处 |
| F    | `rel_program` 通过一个 hook 自己检查链,`Calc` 注册这个 hook               | 不需要 `rel_aop` 这一行                           | 漏 import `Calc` 时要么不检查要么报错;run path 多一个扩展点           |

- D 的覆盖 gate:`LeetQ/Aop/` 里一个文件 import 每个 program,枚举 registry 里的每条 law,报告没有 `.aop` theorem 的。
  它枚举的是 law,不是 theorem;漏洞是没被它 import 的 program,所以 import 列表要对着 `Programs/*.lean` 核对。
- 三个选项里 run path(`LeetQRun`)都不 import AOP。

## 5. 每一步要的定律(问题 4)

主链 `linear` 的四步,先各是一条欠 Lean 的 law(S6),之后各展开成 Rel 的链(S7)。

| law        | statement                              | note 的 display     | Lean 里已有的                                                                 | 缺的                                             |
|------------|----------------------------------------|---------------------|-------------------------------------------------------------------------------|--------------------------------------------------|
| `toShape`  | `mss = shape`                          | `mss-shape`         | `MSS.mss_shape`(:567),加 `ListRel.sum_cata`                                 | Rel 的 `suffix`、`prefix` 等于 `ListRel` 的(桥)|
| `toFused`  | `shape = fused`                        | `mss-prefix-sum`    | `MSS.mss_prefix_sum`(:118):`prefix sum = ⦇S⦈`                               | `S` 的桥:`⊤zero = ⊸ zero`(spike 的 `top_zero`)|
| `toGreedy` | `fused = greedy`                       | `mss-mono`、`mss-step`、greedy | `mssPre_eq_oplus_cata`(:891)、`mss_step`(:432)、`mss_greedy`(:392)| `oplus` 的桥(spike 的 `oplus_eq`)              |
| `toScan`   | `greedy = scan`                        | `mss-scan`、`mss-deriv` | `Kalg_snd_eq`(:984)                                                      | `k_eq`:Rel 写的 `k` 等于 `MSS.k`;spike 的 `w_eq` |

`toShape` 展开之后的五步(note `mss-shape` 的五行;`mss_shape_step1`–`5` 是这五行在书的 model 上的 theorem):

| 步 | 得到                                             | 定律(Rel 的 statement)                             | Lean                                           | 通用吗             |
|----|--------------------------------------------------|------------------------------------------------------|------------------------------------------------|--------------------|
| 1  | `Λ(suffix prefix sum)est(≥)`                     | `≜ segment`                                          | `rfl`(`ListRel.segment_eq`:1175 是桥)        | —                  |
| 2  | `Λ(suffix)E(prefix sum)est(≥)`                   | `absorption(S,R) : Λ(S)E(R) = Λ(S R)`                | `Λ_absorption`(`AOP/A4_6.lean:103`)          | 是,进 prelude     |
| 3  | `Λ(suffix)E(Λ(prefix sum))union est(≥)`          | `E_union(R) : E(R) = E(Λ(R))union`                   | `existsImage_eq_Λ_bigUnion`(`A4_6:320`)      | 是,进 prelude     |
| 4  | `Λ(suffix)E(Λ(prefix sum))E(est(≥))est(≥)`       | 具体的 law(集合非空是假设)                         | `mss_shape_step4`(:594);通用形式 `powerRel_est_eq_bigUnion`(`A7_1:748`) | 否,欠 Lean |
| 5  | `Λ(suffix)E(Λ(prefix sum)est(≥))est(≥)`,即 `shape` | `E_comp(R,S) : E(R S) = E(R)E(S)`                  | `existsImage_comp`(`A4_6:117`)               | 是,进 prelude     |

`toGreedy` 展开之后:

| 步 | 得到                                   | 定律                                               | Lean                                                    | 缺的                                   |
|----|----------------------------------------|----------------------------------------------------|---------------------------------------------------------|----------------------------------------|
| 1  | `Λ(suffix)E(⦇Λ(S)est(≥)⦈)est(≥)`       | `Λ(⦇S⦈)est(≥) = ⦇Λ(S)est(≥)⦈`(具体的 law)        | `⊑` 是 `mss_greedy`;`=` 靠 entire 加 simple(`mssPre_eq_cata`:515 的证明里) | 这条等式没有自己的 theorem,要加一条(约 5 行) |
| 2  | `Λ(suffix)E(⦇[zero,oplus]⦈)est(≥)`     | `Λ(S)est(≥) = [zero,oplus]`(具体的 law)          | `mss_step`(:432)                                      | —                                      |
| 3  | `greedy`                               | `≜ g`、`≜ greedy`                                  | `rfl`                                                   | —                                      |

缺的东西汇总:

| 缺的                                                                 | 放哪                                   | 谁      |
|----------------------------------------------------------------------|----------------------------------------|---------|
| `k_eq`,以及 spike 的 `top_zero`、`oplus_eq`、`w_eq` 搬出测试文件     | `LeetQ/Aop/`(桥属于 Rel→AOP 这一侧)  | ffreyd  |
| `Λ(⦇S⦈)est(≥) = ⦇Λ(S)est(≥)⦈` 在书的 model 上                        | `AOP/A7_7_MSS.lean`                    | ffreyd  |
| Rel 的 `suffix`、`prefix` 的 AOP 读法等于 `ListRel.suffix`、`«prefix»`(用 `suffix_cat`:1164、`prefix_cata`:1120) | `LeetQ/Aop/` | ffreyd |
| P1:program fold 的翻译;builtin 的 `RelSet` 读法(`plus`、`sum`、`≤`、`nil`、`cons`、`cat`) | `LeetQ/Aop/Calc.lean` | ffreyd |
| `E`、`union` 在链里的读法已有(`Calc.powers`)                       | —                                      | —       |

## 6. 证明了什么,没证明什么(问题 5)

链检查通过之后有的 theorem:`mss.linear.aop : mss.mss.aop M = mss.scan.aop M`,`M` 是 `model` 块给的书的 model
(`RelSet`、`Int`、`ConsList Unit Int`、power object `Int → Prop`)。

| 命题                                                                 | 状态                                                                              |
|----------------------------------------------------------------------|-----------------------------------------------------------------------------------|
| Rel 文本的 AOP 读法里,spec 等于 scan,在书的 model 上               | 证明了(kernel),axioms `{propext, Quot.sound}`                                   |
| 链的每一步是所引定律的实例                                           | 证明了(生成的 `calc`)                                                           |
| 对别的 model(例如 `N = -10…20`)同样成立                            | 没有:`mss_eq_scan` 在 `Int` 上逐点证出来,不是泛型定理                            |
| executable `mss.rel.mss : CRel [N] N` 的含义等于 `mss.mss.aop`       | 没有:G3–G5。`Gen` 对 fold、`sum`、`Λ`、`est`、μ/ν 没有 `*_sound`;array 不是 power object;`N` 是有限 universe |
| executable 的 `scan` 是线性的                                        | 没有:没有任何关于开销的 theorem                                                  |
| executable 的各版本在数据上相等                                      | `check`、`on A`:40 个 array 加 5 个输入                                           |

- 所以 "线性版本实现了 spec" 现在的证据是两段:model 上的 theorem,加上 executable 在有限数据上的 `check`。
  连接两段的是 P6(G2–G5),规模大、未估。这句话要写进 `mss.linear` 的注释,不能让它读起来像是关于 executable 的。

## 7. 分阶段计划(问题 6)

owner:`Run/Lang/*`、`Aop/*` 是 ffreyd;`Programs/*` 是 aima。"第 n 步" 指 `doc/rel-module-design.md` 第 4 节。

| stage | 交付物                                                                                     | 文件                                              | owner  | gate                                                              | 规模     | 等什么                                |
|-------|--------------------------------------------------------------------------------------------|---------------------------------------------------|--------|-------------------------------------------------------------------|----------|---------------------------------------|
| S1    | 五个版本写进 program(def,各一条 `check A v = A mss`);spec 用 `sum`;`segment ≜ suffix prefix` | `Programs/Mss.lean`、`Rel/Lang/TestMss.lean`    | aima   | `#guard mss.ok`;`TestMss` 的 40 个 array                          | ~25 行   | 不等                                  |
| S2    | spike 扩成四条版本间的 theorem(`toShape`…`toScan`),Rel def 仍手写成 Lean def;`k_eq`;缺的那条 greedy 等式 | `Aop/CalcMssTest.lean`、`AOP/A7_7_MSS.lean` | ffreyd | 该 module build;`#print axioms` 不比 `mss_eq_scan` 多             | ~150 行  | 不等                                  |
| S3    | P1:program fold 的翻译;builtin 的 `RelSet` 表                                             | `Aop/Calc.lean`、`Aop/CalcTest.lean`              | ffreyd | 每个新构造一条 `guard_expr`                                       | ~80 行   | 不等                                  |
| S4    | `law` 语句:parse、AST(`Decl.law`)、第 3 节的四项检查、`on`                               | `Run/Lang/Embed.lean`、`Syntax.lean`、`Elab.lean` | ffreyd | `EmbedTest`:好的链通过;type 错、名字错、数据错各一条报错         | ~150 行  | 他批准 `Decl.law`;跨 program 的定律名等第 1–3 步(registry、resolver) |
| S5    | `rel_aop`:`model`、`proof`、`.aop` def、law 的 theorem、生成 `calc`;`rel_step`            | `Aop/Calc.lean`(或新文件 `Aop/RelAop.lean`)     | ffreyd | 测试:错的一步 build 失败并报行号;缺 `proof` 的 law 被列出        | ~250 行  | 6-N(P2)、P3 的 resolver;6-L 见下   |
| S6    | `linear` 写进 Mss.lean(四步,各引一条欠 Lean 的 law);`rel_aop mss`;删 spike 文件        | `Programs/Mss.lean`、`Aop/Mss.lean`(选项 D)     | aima(桥:ffreyd) | `lake build LeetQAop`;axioms;覆盖 gate                   | ~60 行   | S2–S5                                 |
| S7    | 四条 law 各展开成 Rel 的链;通用定律进 prelude;需要时加 law 的假设(`if`)                 | `Programs/Prelude.lean`、`Programs/Mss.lean`、`Aop/Prelude.lean` | aima | 同 S6;每条 prelude law 有 `.aop`                       | ~120 行  | S6                                    |
| S8    | executable 的 soundness(P6,G2–G5)                                                        | `Rel/Lang/GenSpec.lean`、`Rep*.lean`              | ffreyd | 每个 `unproved` 为空的 def 有 `sound`                             | 大,未估 | elaborate-once 第 5 步                |
| S9    | 可选:常数空间的版本和它的定律(`est(≥)` 融进 fold)                                       | `AOP/A7_7_MSS.lean`、`Programs/Mss.lean`          | 待定   | 同 S6                                                             | 未估     | S6;他要才做                          |

- S1、S2、S3 互不依赖,现在就能并行;S1 之后 Mss.lean 已经 "写出几个版本并在数据上核对"。
- 6-L(registry 存 body)对 S5 可能不是前提:`rel_program mss` 已经定义了 Lean constant `Programs.mss : Program`,
  它就是 AST;`rel_aop` 可以求值这个 constant 读出 def 和 law(未验证)。跨 program 的名字解析仍要 registry。
- S7 的 "假设" 只在第二条需要它的定律出现时才加语法;在那之前带假设的一步是一条具体的、欠 Lean 的 law。

## 8. 要他定的

已定(2026-11-15):

| # | 事情                                   | 决定                                                                                           |
|---|----------------------------------------|------------------------------------------------------------------------------------------------|
| 1 | `rel_aop mss` 放哪                     | D:单独的 `Aop/Mss.lean`。E 落选:import Mss 的都带上 AOP;F 落选:漏 import 时要么不检查要么退化成 E |
| 2 | 新 constructor                         | 批准,名字跟 Lean 叫 `Decl.theorem`                                                            |
| 3 | 语法                                   | 跟 Lean:`theorem linear : mss = scan := calc`,每步 `_ = e := 定律名`;不用 `law … where … by`。上文第 3 节的 `law`/`by` 一律按此读 |
