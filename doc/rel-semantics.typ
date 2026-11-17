#set page(paper: "a5", margin: 12mm, numbering: "1")
#set text(size: 9pt, font: ("Noto Serif CJK SC", "Noto Sans CJK SC", "JuliaMono"), lang: "zh")
#set par(justify: false, leading: 0.5em)
#set list(spacing: 0.45em, indent: 0pt)
#set enum(spacing: 0.45em, indent: 0pt)
#set heading(numbering: "1.")
#show heading.where(level: 1): set text(size: 10.5pt)
#show heading.where(level: 2): set text(size: 9.5pt)
#show heading: set block(above: 0.75em, below: 0.4em)
#show raw: set text(size: 8pt, font: "JuliaMono")
#set table(inset: (x: 2.5pt, y: 1.8pt), stroke: 0.4pt + gray)
#show table: set text(size: 8pt)

// A Lean declaration behind a claim, without the common prefix `LeetQ.Rel.Lang.`.
#let lean(..ns) = text(size: 6.5pt, fill: luma(110), ns.pos().map(n => raw(n)).join(", "))
#let nolp = text(size: 7.5pt, fill: rgb("#b00020"))[(no Lean proof)]
#let blkc = counter("blk")
#let blk(kind, name, tag, body) = block(width: 100%, inset: (left: 5pt, y: 2pt), stroke: (left: 0.6pt + gray),
  breakable: true)[#blkc.step()*#kind #context blkc.display()*#if name != none [（#name）] #h(1fr) #tag \ #body]
#let defn = blk.with("Definition")
#let rul = blk.with("Rule")
#let thm = blk.with("Theorem")
#let rmk = blk.with("Remark")

#align(center)[#text(size: 12pt)[*Rel 语言的形式定义：语法，与作为 functor 的语义*]]

本文给出 `leetq/LeetQ/` 中 Rel 语言的定义：抽象语法、typing、到 allegory `RelSet` 的 denotational semantics，
以及 `CRel` 上的 operational semantics 与两者之间的 soundness。每条规则或定理后的灰色标签是它在 Lean 中的声明，
省去公共前缀 `LeetQ.Rel.Lang.`；Lean 中没有对应声明的陈述标为 #nolp，不作断言。

约定：composition 按 diagram order 写成并置，$R S$ 表示先 $R$ 后 $S$（Lean 中为 `≫`）；$𝟙 A$ 为恒等；
$R°$ 为 converse；$∈$ 是 $∋$ 的 converse；运算符作用于参数时带括号，如 $E(R)$、$Λ(R)$。

= 抽象语法

== 具体文法

#defn("objects", lean("Grammar.relObj", "OExp", "Obj"))[
$ A ::= w | [A] | A × A | A + A | (A) $
object 是一个名字 $w$、array、product 或 sum；$×$ 为左结合。名字解析为 qlean 原子类型，声明的 object
存为 `.long`，由不可展开的 `Obj.named n` 区分；集合一律用 array $[A]$ 表示（`Obj.arr`）。]

#defn("relation terms", lean("Grammar.rel", "Expr"))[
$ R ::= & x | f(T_1, …, T_n) | ⟨R, S⟩ | [R, S] | ⦇R⦈ | {ℓ_1, …, ℓ_k} \
  & | ∼R | R° | R^* | R S | R #raw("|") S | R ⊙ S | μ X : R | ν X : R, quad ⊙ ∈ {∩, ∪, −, \/, \\, ×} $
$R$、$S$ 是 relation term（本定义），$A$ 是 object（Definition 1）。term 是名字、application（每个参数 $T_i$
是 relation term 或 object：`Λ(R)`、`⊤(A,B)`）、pair、junc、fold
（$R : 1 + E × V ⟶ V$ 时 $⦇R⦈ : [E] ⟶ V$）、literal、补、converse、star、composition（并置或 `|`）、
binary operator，或以 $μ$/$ν$ 开头的 fixed point。]

#rmk("parsing", lean("Grammar.rComp", "Parse.isFix"))[
名字后面紧贴 `(` 是 application，`f` 不带参数时报错；有空格（`f (a)`）或写 `f|(a)` 是 composition；
`f⟨R,S⟩` 是 composition。所有 infix operator（并置在内）同一优先级、从左到右结合；并置不跨行（`sameLine`）。
fixed point 的绑定名以 `μ` 或 `ν` 开头时才是 fixed point。]

#defn("desugaring", lean("Elab.elabE"))[
$ R^* ≜ μ X : 𝟙 ∪ R X, quad quad ∼R ≜ ⊤ − R $
star 是从 $𝟙$ 开始、每轮在左边再接一个 $R$ 的最小 fixed point；补是相对 $⊤$ 的差。]

#defn("declarations and programs", lean("Grammar.relStmt", "Decl", "Program"))[
$ D ::= & "obj" w = {w_1, …, w_k} | "obj" w = w_"lo" … w_"hi" | "obj" w = A \
  & | x(p_1 : A_1 ⟶ B_1, …) : A ⟶ B ≜ R #h(0.3em) [⊑ S] #h(0.3em) ["where" …] \
  & | "print" R | "check" R ⋈ S | "theorem" … , quad quad P ::= D_1 … D_n $
声明是一个有限集合、一个整数区间或一个别名 object，一个可带参数和类型的 definition（`Body.rel`，或带 `⊑ S`
的 `Body.test`），一条 print、check 或 theorem；程序是声明的列表。`rel_program n from b where …` 用
`where` 中的定义替换 `b` 的同名定义，丢掉 check 与 theorem，并截到 `upto`。]

== 核心 term

#defn("core terms", lean("Tm", "Res"))[
$ "Tm" : "Obj" → "Obj" → "Bool" → "Type" $
核心 term `Tm A B d` 按 source $A$、target $B$ 和 demand 位 $d$ 编号；$d = "true"$ 表示它只在左侧上下文
提供的 key 上求值，$d = "false"$ 表示 closed。构造子：
`val uni zero id top outl outr inl inr comp conv meet join diff dom ran ldiv rdiv pair prod junc juncD lam E map est thin nil prim atPos own succ arith leq lt fold share foldI flat var call arg nu mu refold`。
例如 `comp : Tm A B d → Tm B C e → Tm A C d`，`conv : Tm A B false → Tm B A false`，
`meet : Tm A B d → Tm A B e → Tm A B (d || e)`。]

#rmk(none, lean("Tm"))[
`Tm` 是 intrinsically typed：不合类型的核心 term 在 Lean 中写不出来。converse、`ran`、`prod`、`junc`、
两种 division 只接受 closed 参数（$d = "false"$）。]

= Typing

#rul("typing", lean("Elab.elabE", "Elab.binary", "Elab.Pre.polarity", "Prim.inst", "Elab.litTy"))[
- 每个运算的类型就是 allegory（带 product、sum 与 power）中对应运算的类型，两个类型由 `isDefEq` 合一；
- closedness：$×$、$\\$、$\/$、`ran` 与 converse 的参数必须 closed，即能在其整个 source 上算出全部 pair，
  不依赖左边传来的 key；不 closed 的 term（如 `≤`、`succ`、带参数的 prim）只对左边给出的 key 求值；
- fixed point：$X$ 只出现在单调位置（$−$ 的右侧、$\\$ 的左侧、$\/$ 的右侧取反；$Λ$、$E$、`thin` 与非单调 prim
  之下禁止）；$ν X : R$ 还要求 $R$ 有不含 $X$ 的合取项作为起点；
- prim 行：每个 object 变量在每次使用时换成新的 $?β$；
- literal：类型由其中各词所属的已声明 object 决定。]

= Denotational semantics

== 目标 allegory

#defn("RelSet", lean("Freyd.Alg.RelSet"))[
$ "Hom"(A, B) = A → B → "Prop", quad 𝟙 A = (x, y) ↦ x = y, quad R S = (x, z) ↦ ∃ y. R(x, y) ∧ S(y, z) $
object 是一个类型，arrow 是二元谓词；恒等是相等，composition 是经过某个中间点的关系积。
converse 交换两个参数，$∩$ 是 $∧$，modular law 已证，因此 `RelSet` 是一个 allegory。]

#defn("objects", lean("Obj.El"))[
$ ⟦a⟧ = "Carrier"(a), quad ⟦A × B⟧ = ⟦A⟧ × ⟦B⟧, quad ⟦[A]⟧ = "List"(⟦A⟧), quad ⟦A + B⟧ = ⟦A⟧ ⊕ ⟦B⟧ $
原子类型解释为其 carrier，product 为 Lean product，array 为 Lean `List`，sum 为 `Sum`；
$∋$ 解释为 list membership（`Gen.mem_sound`）。relation 是不重复的 pair 集合，所以模型仍是 `RelSet`。]

#defn("hom of meanings", lean("Gen.Den"))[
$ "Den"(A, B) ≜ ⟦A⟧ ⟶_"RelSet" ⟦B⟧ $
一个 Rel term 的意义是 `RelSet` 中从 $⟦A⟧$ 到 $⟦B⟧$ 的 arrow。]

== 逐个构造子的意义

#defn("the interpretation", lean("Gen.Sound", "Expand.prfNode"))[
$⟦t⟧$ 是 `Gen.Sound (code t) T` 中的 $T$。Lean 中*没有*一个函数 $"Tm" A B d → "Den"(A, B)$：每个程序的
$T$ 由 `rel_rep` 逐个节点用下表的 lemma 拼出。作为 Lean 函数的 $⟦−⟧$ #nolp。]

#table(columns: (auto, 1fr, auto), align: left + horizon,
  table.header([term], [$⟦t⟧$], [lemma]),
  [$R$ (table)], [$"rep"(R)$], lean("Gen.val_sound"),
  [$"uni"(U)$], [$"rep"("idU"(U))$, $U$ 中值上的 coreflexive], lean("Gen.uni_sound"),
  [$𝟘$, $𝟙$], [$𝟘$, $𝟙 A$], lean("Gen.zero_sound", "Gen.id_sound"),
  [$⊤_V$], [$⊤ ⟦V⟧$], lean("Gen.top_sound"),
  [$π_1$, $π_2$], [graph of `Prod.fst`, `Prod.snd`], lean("Gen.outl_sound", "Gen.outr_sound"),
  [inl, inr], [sum 的 coprojection $u_1$, $u_2$], lean("Gen.inl_sound", "Gen.inr_sound"),
  [$R S$], [$⟦R⟧ ⟦S⟧$], lean("Gen.comp_sound", "Gen.compB_sound"),
  [$R°$], [$⟦R⟧°$], lean("Gen.conv_sound"),
  [$R ∩ S$, $R ∪ S$], [$⟦R⟧ ∩ ⟦S⟧$, $⟦R⟧ ∪ ⟦S⟧$], lean("Gen.meet_sound", "Gen.meetB_sound", "Gen.join_sound"),
  [$R − S$], [$(x, y) ↦ ⟦R⟧(x, y) ∧ ¬⟦S⟧(x, y)$], lean("Gen.diff_sound", "Gen.diffB_sound"),
  [dom, ran], [$𝟙 ∩ ⟦R⟧ ⟦R⟧°$, $𝟙 ∩ ⟦R⟧° ⟦R⟧$], lean("Gen.dom_sound", "Gen.ran_sound"),
  [$⟨R, S⟩$, $R × S$], [`rpair`, `rprodMap`], lean("Gen.pair_sound", "Gen.prod_sound"),
  [$[R, S]$], [`Freyd.Alg.junc` over `sumCop`], lean("Gen.junc_sound"),
  [$R \\ S$, $R \/ S$], [division relative to the universes], lean("Gen.ldivB_sound", "Gen.rdiv_sound"),
  [$∋$], [$(x s, x) ↦ x ∈ x s$], lean("Gen.mem_sound"),
  [18 prim rows], [每行一个 $T$（如 cons, length, zip）], lean("Gen.ofVals_sound", "Gen.after_sound"),
)
每一行说：该节点的代码在 ok 位为真时计算右栏的关系（精确形式见下文 Theorem "Sound"）。

#rmk("division", lean("Gen.ldivDen"))[
$ (R \\ S)(b, c) ⟺ U_B (b) ∧ U_C (c) ∧ ∀ a. R(a, b) → S(a, c) $
division 只在 universe $U_B × U_C$ 内取值；在 $R$ 的某一列为空时它给出 universe 的全部对，而不是书上在
整个类型上的 division。与书上定义的一致性 #nolp。]

#thm("compositionality clauses", lean("Gen.comp_sound", "Gen.id_sound", "Gen.conv_sound", "Gen.meet_sound"))[
$ ⟦R S⟧ = ⟦R⟧ ⟦S⟧, quad ⟦𝟙⟧ = 𝟙, quad ⟦R°⟧ = ⟦R⟧°, quad ⟦R ∩ S⟧ = ⟦R⟧ ∩ ⟦S⟧ $
composition、恒等、converse、meet 的意义由其部分的意义经 `RelSet` 的同名运算得到；这些是对每个节点各自
的 lemma，不是一个关于 $⟦−⟧$ 的定理。]

#defn("syntactic category", none)[
自然的 syntactic category 以 `Obj` 为 object、以模掉 allegory 公理的 `Tm A B d` 为 arrow（free allegory
on the program's definitions）。Lean 中没有定义它 #nolp；因此 $⟦−⟧$ 是 functor（以及 allegory 的
morphism）这件事 #nolp。]

#rmk("operators without a node lemma", lean("Expand.prfNode", "Expand.rep"))[
下列 `Tm` 节点在 `prfNode` 中没有 lemma，所以其意义在 Lean 中没有给出 #nolp：
`lam`（$Λ$）、`E`、`thin`、`foldI`、`flat`、`var`、`call`、`arg`、`nu`、`mu`、`refold`、`juncD`，
以及 prim 行 setify、asc。用到它们的 definition 不产生 `rep_x`，而在 `n.unproved` 中记下第一个缺 lemma 的 combinator。]

== 与 arXiv:1711.08699 的关系

#defn("cartesian bicategory and model", none)[
该文 Def 4.1：cartesian bicategory of relations 是 poset-enriched symmetric monoidal category，每个 object
上有 comonoid $(Δ, !)$ 与 monoid $(∇, ?)$ 并满足若干条件。Def 4.15：Frobenius theory $𝕋 = (Σ, I)$；
$F 𝕋$ 是由 $(Σ ⊎ Σ_"CW", I ⊎ I_"CW" ⊎ I_"LCH")$ 自由生成的 ordered PROP。Def 4.17：$𝕋$ 的 model 是
cartesian bifunctor $F 𝕋 → C$，morphism 是满足 $α_n G(f) ⩽ F(f) α_m$ 的 lax-natural monoidal
transformation。p.28：空 Frobenius theory 的 model 范畴是 Set。]

#rmk("reading Rel in that frame", none)[
- 目标 `RelSet` 是集合与关系的 allegory，即该文中 Set 上关系的 cartesian bicategory；Lean 中证明了
  它是 allegory，未证明它满足 Def 4.1 的 cartesian bicategory 条件 #nolp。
- 一个 Rel 程序可读作 Frobenius theory：$Σ$ 为其 definitions 与 prim 行，$I$ 为其 `⊑`-test 与
  `check`/`theorem` 的不等式；$⟦−⟧$ 则应是 cartesian bifunctor $F 𝕋 → "RelSet"$。这一读法 #nolp。
- Rel 的 term 超出 Frobenius theory 的语言：$∪$、$−$、$\\$、$\/$、$Λ$、$μ$、$ν$ 需要 union allegory、
  Boolean 结构、division 与 power object，而 Def 4.1 只提供 $∩$、$⊤$ 与 Frobenius 结构。
- Rel 的 product $A × B$ 是一个 object 的类型构造子，不是 PROP 中线的 monoidal 并列；二者的对应 #nolp。]

= Operational semantics

== 数据

#defn("relations as arrays", lean("Rel", "Vals", "CRel"))[
$ "Rel"(k, v) = {n : "USize", "key" : "Vals"(k, n), "val" : "Vals"(v, n)}, quad "CRel"(k, v) = "Rel"(k, v) × "Bool" $
一个关系是等长的两列 array，第 $i$ 行是一对 $("key"_i, "val"_i)$；`CRel` 再带一个 ok 位。]

#defn("representation", lean("Rep.rep"))[
$ "rep"(R)(x, y) ⟺ ∃ i. "key"_i = x ∧ "val"_i = y $
一个 array 关系表示的 `RelSet` arrow 恰好关联其某一行的 key 与 val。]

#defn("demand and code", lean("Gen.Dem", "Gen.Fn", "Gen.Pl"))[
$ "Dem"("true", A) = "Rel"(A, A), quad "Dem"("false", A) = "Unit", quad "Fn"(d, A, B) = "Dem"(d, A) → "CRel"(A, B) $
on demand 的代码收到一个 $A$ 上的 coreflexive $D$（要求值的 key），closed 代码不收任何东西；代码是从 demand
到带 ok 位的 array 关系的 Lean 函数。plan `Pl d A B` 返回保留 bit-rule 节点的 term 与一个 ok 位。]

== 代码生成与 kernels

#defn("code", lean("Expand.code", "Expand.node", "Expand.planOr", "Expand.primE"))[
`Expand.emit` 把每个 `Tm` 节点译成 `Gen` 的一个 combinator（`Gen.comp`、`Gen.E`、`Gen.fold`、`Gen.mu` …），
closed 子 term 编号后各生成一个 Lean 常量，只建一次。]

#defn("CRel kernels", lean("CRel.comp", "CRel.inter", "CRel.union", "CRel.E", "CRel.foldOn", "CRel.fixOn"))[
每个 combinator 落到 `CRel` 上的 kernel；kernel 是带 Lean body 的 `@[extern]` qlean C 函数，Lean body 是其规格。
C 实现与其 Lean body 一致 #nolp（`@[extern]` 被信任）。]

#defn("fixed points", lean("Gen.mu", "Gen.nu", "Expand.muCap"))[
$ μ X : φ ⇝ "fixOn"("cap", φ, 𝟘), quad "ok" ⟺ "rounds" < "cap", quad "cap" = 1024 $
$μ$ 从 $𝟘$ 开始重复 $φ$，最多 cap 轮；跑满 cap 轮时 ok 位为假，而不是把截断的链当作答案。$ν$ 从其起点 $S$
向下迭代，最多 $|S| + 1$ 轮。]

== Soundness

#thm("Sound", lean("Gen.Sound"))[
$ "Sound"(f, T) ⟺ ∀ D. "Cor"(D) → (f D)."ok" → ∀ x, y. "keys"(D)(x, x) → ("rep"((f D)."rel")(x, y) ⟺ T(x, y)) $
代码 $f$ 计算 $T$：对每个 coreflexive demand $D$，只要 ok 位为真，对 $D$ 中每个 key $x$，结果关联 $x$ 与
$y$ 当且仅当 $T$ 关联它们。closed 时 `keys` 是 $𝟙$。<sound>]

#rmk("as an equation", lean("Gen.Sound"))[
$ "ok"(f D) ⟹ "keys"(D) thin "rep"(f D) = "keys"(D) thin T $
在 ok 位下，结果与 $T$ 在 demand 的 key 上一致；在 key 之外 `Sound` 不说任何话。这是限制在 $"keys"(D)$
上的等式，不是 inclusion。]

#thm("closed", lean("Gen.Sound.eq"))[
$ "Sound"(f, T) ∧ (f ())."ok" ⟹ "rep"((f ())."rel") = T $
closed 代码在 ok 位为真时恰好表示 $T$。]

#thm("program theorem", lean("Expand.rep", "Expand.elabRelRep"))[
$ n."rep"_x : (n.x)."ok" = "true" → "rep"((n.x)."rel") = ⟦x⟧ $
`rel_rep n` 为程序 $n$ 的每个 definition $x$ 生成此定理（当 `prfNode` 对其每个节点都有 lemma 时）：若运行
结果的 ok 位为真，它表示的关系就是 $x$ 的意义。没有 lemma 的 definition 进入 `n.unproved`。
`TestRep` 对注册表中的每个程序运行它。]

#rmk("natural transformation reading", lean("Gen.comp_sound", "Gen.Sound.eq"))[
$ "rep"("code"(R S)) = "rep"("code"(R)) thin "rep"("code"(S)) quad ("在 ok 位下") $
`rep` 把代码的运算送到 `RelSet` 的运算，所以它是从代码代数到 `RelSet` 的一个 *partial* homomorphism，
只在 ok 位为真时有定义。代码一侧不构成 category，因此把它陈述为 natural transformation #nolp。]

== CRel 层的 lemma

#thm("rep lemmas", lean("CRel.rep_E", "CRel.rep_lamOn", "CRel.rep_map", "CRel.rep_fold", "CRel.rep_thin", "CRel.rep_fixOn"))[
$ "rep"(E(R) X)(x s, Y) ⟹ (y ∈ Y ⟺ ∃ x ∈ x s. "rep"(R)(x, y)) $
$E(R)$ 的结果把每个输入 list 关联到其元素在 $R$ 下的像。同层还有：$Λ$（`rep_lamOn`：对每个 $a$，$y ∈ Y ⟺ R(a, y)$，
且在 universe $U$ 上 total）、`map`（逐位）、fold（`rep_fold`：存在长 $|x s| + 1$ 的中间值 list $y s$，
末项来自 $e$，每步由 $S$ 联系，结果为 $y s_0$）、`thin`、`est`、`fixOn`。]

#thm("fixOn", lean("CRel.rep_fixOn"))[
$ "rep"("fixOn"(n, φ, X_0)) = Φ^j ("rep"(X_0)), quad j < n ⟹ Φ("rep"(…)) = "rep"(…), quad ∀ Y. X_0 ⊑ Y ∧ Φ(Y) ⊑ Y ⟹ "rep"(…) ⊑ Y $
在 $φ$ 表示单调的 $Φ$、ok 位为真时，迭代 $j ≤ n$ 轮后得到 $Φ^j(X_0)$；若 $j < n$ 它是 fixed point，且在每个
包含 $X_0$ 的 pre-fixed point 之下（从 $𝟘$ 起即最小 fixed point）。]

#rmk("gap", lean("Expand.prfNode"))[
这些 CRel lemma 没有接到 `prfNode`：`Gen.E`、`Gen.lam`、`Gen.mu` 等 combinator 没有 `Sound`
lemma #nolp，所以使用它们的程序没有 `rep_x`。]

== 证明了什么，没证明什么

- 证明的：在 ok 位为真时，结果在 demand 的 key 上等于意义（`Sound`）；closed 时整体相等（`rep_x`）。
- 没证明 totality：没有任何定理给出某个输入上 ok 位为真 #nolp。$μ$ 跑满 1024 轮、`refold` 遇到环时 ok 为假。
- 没证明 termination 的语义版本：`Gen` 的每个 combinator 是 Lean 中的 total 函数（`fixOn` 有轮数上限，
  `refoldRounds` 对 `Nat` 结构递归），所以求值总会返回；但"上限足够"#nolp，C kernel 的终止 #nolp。
- 没证明 `rep_x` 的意义 $⟦x⟧$ 与 AOP 中同名构造一致：`Calc.builtins` 只按名字连到 `Freyd.Alg`
  的常量 #nolp。

= Metatheory

#table(columns: (auto, auto, 1fr), align: left + horizon,
  table.header([property], [status], [Lean / note]),
  [type preservation], [partial], [`Tm` intrinsically typed，`build : Pre → Res`；判断与 `Res` 一致 #nolp],
  [Sound: leaves, $∘$, $°$, $∩$, $∪$, $−$, dom, ran, pair, $×$, junc, division, $∋$], [proved],
    lean("Gen.*_sound", "Gen.Sound.eq"),
  [Sound: 18 prim rows（τ cons uncons length sum inits tails prefix suffix concat cat uncat zip snoc unsnoc distinct tic merge）],
    [proved], lean("Gen.ofVals_sound", "Gen.after_sound", "Gen.cons_sound", "…"),
  [Sound: prim rows filter, takewhile, thinL, loop, setify, asc], [missing], [`sound := none` #nolp],
  [Sound: $Λ$, $E$, map, est, thin, fold, foldI, flat, $μ$, $ν$, refold, juncD, nil, atPos, succ, arith, $≤$, $<$, call/arg/var],
    [partial], [CRel-level `rep_*` lemma for most（`rep_lamOn`, `rep_E`, `rep_fold`, `rep_fixOn` …）；no `Gen` lemma #nolp],
  [program soundness], [proved per program], [`n.rep_x`, ok-conditional; gaps in `n.unproved`],
  [compositionality], [partial], [per-node clauses; $⟦−⟧$ as function, functoriality #nolp],
  [syntactic category / free allegory], [missing], [#nolp],
  [model in a cartesian bicategory], [missing], [#nolp],
  [determinism of evaluation], [by construction], [`Gen.Fn` is a Lean function; no theorem needed],
  [determinism of meaning ($⟦x⟧$ a map)], [missing], [not claimed #nolp],
  [totality (ok = true)], [missing], [#nolp],
  [termination], [partial], [Lean totality of `Gen` with fuel; C kernels #nolp],
)
