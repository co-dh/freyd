#import "../note-prelude.typ": *
#show: note-chapter.with(10)
// note-split: chapter 10 — this header is written by scripts/note-split and stripped by scripts/note-join
= Greedy Algorithms <sec-greedy>

== Theory

// B&dM §10.1, p. 245.  Theorem 9.2 with `est(Q)` for `thin(Q)`: the same hypotheses, a much stronger
// conclusion, and one far harder to refine into a program.
#disp[#definition[
`h`, `T`, `≤`, `H`, `M` as in @Freyd.Alg.M; #h(4pt) additionally `Q` a *connected* preorder on the sets
$frac(#[`T°`], ∋)$ returns, so that $frac(#[`T°`], ∋)$ `est(Q)` is entire.
]]<greedy-defn>

#disp(num: "Theorem 10.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.greedy_dp") \
    #src[the same optimum reached by keeping ONE decomposition at each step, so that no set is ever
 carried and the recursion runs on values alone #h(4pt) ]],
  lean-chain(
    (none, "Freyd.Alg.greedy_dp_step1.rhs",
      src[`H≜⦇T⦈°⦇h⦈` — @greedy-defn]),
    // dp-shrink row: Theorem 10.1
    // `est(Q) : PFA⟶FA` kills the SET but not the `F` under it, so its wire spans the `E` lane
    // down to the object wire, crossing `F` — the whole difference from @dp-laws' second row.
    (RQ, "Freyd.Alg.greedy_dp_step1.lhs", src[]),
  ),
  // Proposition 10.1 holds for EVERY `X`, and only at a base functor `−+(−×W)`: a chain of its own,
  // since a step relates two sides of one generality.
  lean-chain(
    (none, "Freyd.Alg.RelSet.SL.est_arm₂_le.rhs", src[the body at `T` a coproduct of two arms]),
    // lean:AOP.A9_1.est_summand_le@599fa245
    // The branch, not the conditional; nothing survives outside the set here, so `est(Qᵢ)` lands on
    // the object wire.
    (RQ, "Freyd.Alg.RelSet.SL.est_arm₂_le.lhs",
      src[Proposition 10.1, `V₂V₁°=𝟘`]),
  ),
)]<greedy-laws>

#import "../generated/Freyd.Alg.greedy_dp_lower.calc.typ" as calc-gl
#import "../generated/Freyd.Alg.greedy_dp_upper.calc.typ" as calc-gu
#import "../generated/Freyd.Alg.RelSet.Tardy.tardy_tail.calc.typ" as calc-tt
#import "../generated/Freyd.Alg.RelSet.Tardy.bagify_recip_le.calc.typ" as calc-brl
#import "../generated/Freyd.Alg.RelSet.Tardy.tardy_greedy.calc.typ" as calc-tg
#import "../generated/Freyd.Alg.RelSet.Tex.tex_fusion_condition.calc.typ" as calc-tf
#import "../generated/Freyd.Alg.RelSet.Tex.tex_laws.calc.typ" as calc-tl
#import "../generated/Freyd.Alg.RelSet.Tex.tex_greedy.calc.typ" as calc-tgr
#import "../generated/Freyd.Alg.RelSet.greedy_disjoint_ranges.calc.typ" as calc-gd
#import "../generated/Freyd.Alg.RelSet.Detab.expand_V.calc.typ" as calc-ev
#import "../generated/Freyd.Alg.RelSet.Detab.detab_V_R.calc.typ" as calc-dv
// B&dM Theorem 10.1, p. 245, "left as an exercise": the proof of Theorem 9.2 with `est(Q)` for
// `thin(Q)`.  Knaster–Tarski needs the body at `M` below `M`; `M=H∩(H°\R°)` splits that in two.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.greedy_dp_lower") \
    #src[taking the input apart in one `Q`-extreme way, solving the parts by `M` and assembling by
     `h` returns only what `H` returns]],
     // lean:AOP.A10_1.greedy_dp_lower@7018e48b
  lean-calc(calc-gl),
)]<greedy-lower>

// The second half of the same proof.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.greedy_dp_upper") \
    #src[`H°` followed by the greedy body at `M` is `⊑≥`: an answer of the body is never worse
     than an answer of `H` to the same input]],
     // lean:AOP.A10_1.greedy_dp_upper@450eaa94
  lean-calc(calc-gu, breaks: (4,)),
)]<greedy-upper>

// B&dM Proposition 10.1, p. 245, "a variation on Proposition 9.1", in Rel(Set).  The book's
// `(ran V₁ → W₁, W₂)` is the union below: off `ran V₁ ∪ ran V₂` both are empty.
#disp(num: "Proposition 10.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.greedy_disjoint_ranges") \
    #src[when `V₁` and `V₂` have disjoint ranges, the greedy step over `[V₁,V₂]` runs the `V₁` step
     on inputs `V₁` reaches and the `V₂` step on inputs `V₂` reaches]],
     // lean:AOP.A10_1.greedy_disjoint_ranges@e60d7430
  lean-calc(calc-gd, breaks: (3, 5)),
)]<greedy-disjoint>

== The detab-entab problem

=== Detab
// B&dM §10.2, p. 246.  `V ≜ prefix° ∩ (fill fill°)` is the whole trick: a bare `prefix°` fails because
// a prefix of the expansion can be longer than the input once it crosses a tab stop.
#disp[#deftab(

  [#rowkey("Freyd.Alg.RelSet.Detab.detabFn")], [#leant("Freyd.Alg.RelSet.Detab.detabFn")],
  "Freyd.Alg.RelSet.Detab.detab_cata",
  [replace every tab by blanks up to the next tab stop; `H=detab°`],
  [#rowkey("Freyd.Alg.RelSet.Detab.expandFn")], [#leant("Freyd.Alg.RelSet.Detab.expandFn")],
  "Freyd.Alg.RelSet.Detab.expandFn",
  [a tab fills the line to the next stop; any other character is appended],
  [#rowkey("Freyd.Alg.RelSet.Detab.fillFn")], [#leant("Freyd.Alg.RelSet.Detab.fillFn")],
  "Freyd.Alg.RelSet.Detab.fillFn",
  [append blanks up to the next multiple of `n` columns],
  [#rowkey("Freyd.Alg.RelSet.Detab.colFn")], [#leant("Freyd.Alg.RelSet.Detab.colFn")],
  "Freyd.Alg.RelSet.Detab.colFn",
  [the column the string ends at: characters since the last newline],
  [#rowkey("Freyd.Alg.RelSet.Detab.R")], [#leant("Freyd.Alg.RelSet.Detab.R")],
  "Freyd.Alg.RelSet.Detab.R",
  [`x` is no longer than `y`],
  [#rowkey("Freyd.Alg.RelSet.Detab.U")], [#leant("Freyd.Alg.RelSet.Detab.U")],
  "Freyd.Alg.RelSet.Detab.U",
  [`a` is the tab or `a=b`],
  [#rowkey("Freyd.Alg.RelSet.Detab.V")], [#leant("Freyd.Alg.RelSet.Detab.V")],
  "Freyd.Alg.RelSet.Detab.V",
  [a prefix that fills to the same string],
  [#rowkey("Freyd.Alg.RelSet.Detab.Q")], [#leant("Freyd.Alg.RelSet.Detab.Q")],
  "Freyd.Alg.RelSet.Detab.Q_eq",
  [compare two decompositions by `V` on the strings and `U` on the characters],
  [#rowkey("Freyd.Alg.RelSet.Detab.unfillFn")], [#leant("Freyd.Alg.RelSet.Detab.unfillFn")],
  "Freyd.Alg.RelSet.Detab.unfillFn",
  [the shortest prefix that fills to the same string],
  [#rowkey("Freyd.Alg.RelSet.Detab.tbcFn")], [#leant("Freyd.Alg.RelSet.Detab.tbcFn")],
  "Freyd.Alg.RelSet.Detab.tbcFn",
  [the number of trailing blanks],
  [#rowkey("Freyd.Alg.RelSet.Detab.triple")], [#leant("Freyd.Alg.RelSet.Detab.triple")],
  "Freyd.Alg.RelSet.Detab.triple",
  [what `entab` keeps: the unfilled output, its trailing blank count and its column],
// lean:AOP.A10_2_Detab.detab_cata@54307fd6
// lean:AOP.A10_2_Detab.R@2b264e9a
// lean:AOP.A10_2_Detab.V@548e5cfc
// lean:AOP.A10_2_Detab.Q@582cab8a lean:AOP.A10_2_Detab.Q_eq@971ff06f
)]<entab-defn>

=== Derivation
// B&dM pp.249–250, "we argue": the claim the next chain leaves aside, one row per hint.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.expand_V") \
    #src[shortening the output of one `expand` step to a `V`-smaller string either keeps the whole
     step (`expand`) or drops its character and shortens its input string (`π₁V°`)]],
     // lean:AOP.A10_2_Detab.expand_V@bbbb18ac
  lean-calc(calc-ev, breaks: (3,)),
)]<entab-expand-V>

// B&dM p.249, "To prove V·detab ⊆ detab·R we reason", in diagram order: the note's `V` relates the
// shorter string to the longer, so the book's `V·detab` is `detab V°` here.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.detab_V_R") \
    #src[any `V`-shortening of `detab`'s output is `detab`'s output on an input no longer than the
     given one]],
     // lean:AOP.A10_2_Detab.detab_V_R@4e8c7126
  lean-calc(calc-dv, breaks: (4,)),
)]<entab-detab-V>

// ONE WIRE, `String` to `String`; `F(X)h` is drawn as the ONE bead the formula writes,
// `(𝟙+(X×𝟙))[nil,snoc]`, so the `list` lane pinches twice rather than three times.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.entab_laws") \
    #src[the shortest input `detab` expands to the given output is one pass along that output,
     holding each blank back and cashing the held blanks in for a tab wherever the column reaches a
     tab stop]],
  lean-chain(
    (none, "Freyd.Alg.RelSet.Detab.entab_laws_prefixed.rhs",
      src[the specification — @Freyd.Alg.RelSet.Detab.detabFn; `detab entab=𝟙` and nothing
       shorter does]),
    // `[nil,expand]°` opens `−×Char` inside the set the singleton opened; `est(Q)` kills that set but
    // not the `F` under it, so its wire spans down to the object wire, crossing `F`.
    (RQ, "Freyd.Alg.RelSet.Detab.entab_laws_prefixed.lhs", [
     // entab-thin row: Theorem 10.1
     #src[at `Q≜𝟙+(V×U)`
 #src[]: one character of input is
      // lean:AOP.A10_2_Detab.entab_thin_condition@69c1ae8b
      decided at each step. `F(⊤,R)α⊑αR`#src[].
      // lean:AOP.A10_2_Detab.entab_mono@d08087a2
      `detab prefix⊑R° detab` is
 FALSE #src[,
      // lean:AOP.A10_2_Detab.detab_prefix_false@b3bb96e1
 ] — at `n=8`,
      // lean:AOP.A10_2_Detab.detab_len_of_short@3fdda196
      `detab [a,b,c,d,e,TB]=[a,b,c,d,e,BL,BL,BL]`, whose prefix
      `[a,b,c,d,e,BL,BL]` is longer than any input giving it, and `detab V°⊑R° detab`
 #src[]
      // lean:Freyd.Alg.RelSet.Detab.detab_V@d64fef36 lean:AOP.A10_2_Detab.entab_V@0f631a23
      holds. `expand V°⊑expand ∪ (π₁V°)`
 #src[] — shortening the output either leaves the
      // lean:AOP.A10_2_Detab.expand_V@bbbb18ac
      last step alone or discards it]]),
    (RQ, "Freyd.Alg.RelSet.Detab.entab_branch.lhs",
      src[Proposition 10.1: `nil` and `expand` have disjoint ranges. The greedy step is to emit
       a tab whenever a tab is legal, consuming all the blanks back to the previous tab stop]),
  ),
)
]<entab-laws>

// B&dM p.247: the program for `detab`, `detab` tupled with `col` and run as a loop.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.detab_tupled") \
    #src[one pass over the input carries the output so far together with its column]],
    // lean:AOP.A10_2_Detab.detab_tupled@da1e2396
  lean-chain(
    (none, "Freyd.Alg.RelSet.Detab.detab_tupled.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Detab.detab_tupled.rhs",
      src[both components are folds over the same input; `step` on `(detab x,col(detab x))` is
       `(detab,col detab)` one character further — not a tabulated row]),
  ),
)]<entab-detab-tupled>

#disp(num: "Exercise 10.1")[
  - #leanf("Freyd.Alg.RelSet.Detab.detab_loop") \
    #src[the fold of `[base,step]` over the input converted to a snoc-list is the left loop of
     `step` from `base`]
    // lean:AOP.A10_2_Detab.detab_loop@8ea9a446
  - #leanf("Freyd.Alg.RelSet.Detab.outl_loop") \
    #src[Exercise 10.1: when `step` only appends `f(c,a)` to the output and moves the state by
     `g`, the output of the loop is `loop'(f,g)`, which never carries the output]
    // lean:AOP.A10_2_Detab.outl_loop@069af82d
]<entab-detab-loop>

// B&dM p.250: the greedy step `min(V×U)Λexpand°`, read on points.
#disp[
  - #leanf("Freyd.Alg.RelSet.Detab.expand_recip_snoc") \
    #src[`expand` produces `x⧺[a]` from a tab after a string that fills to it, or from `x` and `a`]
    // lean:AOP.A10_2_Detab.expand_recip_snoc@d8fd6118
  - #leanf("Freyd.Alg.RelSet.Detab.fill_exists_iff") \
    #src[a string is a `fill` exactly when it ends in a blank on a tab stop]
    // lean:AOP.A10_2_Detab.fill_exists_iff@4f895b07
]<entab-step>

// B&dM p.251: (10.1) and the equations for `tbc` it gives.
#disp(num: "(10.1)")[
  - #leanf("Freyd.Alg.RelSet.Detab.entab_unfill") \
    #src[(10.1): the output of `entab` is that of `unfill x` followed by the trailing blanks held
     back]
    // lean:AOP.A10_2_Detab.entab_unfill@673f3918
  - #leanf("Freyd.Alg.RelSet.Detab.tbc_nil") \
    #src[the empty string has no trailing blanks]
    // lean:AOP.A10_2_Detab.tbc_nil@cc857e37
  - #leanf("Freyd.Alg.RelSet.Detab.tbc_snoc") \
    #src[a blank off a tab stop adds one held blank; anything else releases them all]
    // lean:AOP.A10_2_Detab.tbc_snoc@0a859f14
]<entab-tbc>

// B&dM pp.251–252: `⟨tbc,col⟩`, `triple` and `entab` as one fold.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.tbc_col_fold") \
    #src[one pass counts the held blanks and the column together]],
    // lean:AOP.A10_2_Detab.tbc_col_fold@6e1b6f47
  lean-chain(
    (none, "Freyd.Alg.RelSet.Detab.tbc_col_fold.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Detab.tbc_col_fold.rhs",
      src[`op` on `(tbc x,col x)` is `(tbc,col)` one character further, from the equations for
       `tbc` — @entab-tbc]),
  ),
)]<entab-tbc-col>

#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.triple_fold") \
    #src[one pass carries the output up to the held blanks, their count and the column]],
    // lean:AOP.A10_2_Detab.triple_fold@ca010e10
  lean-chain(
    (none, "Freyd.Alg.RelSet.Detab.triple_fold.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Detab.triple_fold.rhs",
      src[`op` on `triple x` is `triple` one character further: (10.1) where the blanks are
       released — @entab-tbc]),
  ),
)]<entab-triple>

#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.entab_triple") \
    #src[`entab` is `triple` with the held blanks appended to its output]],
    // lean:AOP.A10_2_Detab.entab_triple@413fca13
  lean-chain(
    (none, "Freyd.Alg.RelSet.Detab.entab_triple.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Detab.entab_triple.rhs", src[(10.1) — @entab-tbc]),
  ),
)]<entab-entab>


== The minimum tardiness problem

// B&dM §10.3, p. 253.  Both conditions need context, and `cost` has to be restated over `perm xs`
// before Proposition 9.3 fits — `penalty` reads the bag of scheduled jobs, not their order.
#disp[#deftab(

  [#rowkey("Freyd.Alg.RelSet.Tardy.Bag")], [#leant("Freyd.Alg.RelSet.Tardy.Bag")],
  "Freyd.Alg.RelSet.Tardy.Bag",
  [a bag of jobs: a list up to reordering],
  [#rowkey("Freyd.Alg.RelSet.Tardy.snag")], [#leant("Freyd.Alg.RelSet.Tardy.snag")],
  "Freyd.Alg.RelSet.Tardy.snag",
  [put one job into a bag],
  [#rowkey("Freyd.Alg.RelSet.Tardy.bagify")], [#leant("Freyd.Alg.RelSet.Tardy.bagify")],
  "Freyd.Alg.RelSet.Tardy.bagify_cata",
  [forget the order of a schedule; `H=bagify°` lists every schedule of a bag],
  [#rowkey("Freyd.Alg.RelSet.Tardy.Fn.penalty")], [#leant("Freyd.Alg.RelSet.Tardy.Fn.penalty")],
  "Freyd.Alg.RelSet.Tardy.Fn.penalty",
  [how late job `j` finishes after the schedule `xs`, times its weight],
  [#rowkey("Freyd.Alg.RelSet.Tardy.Fn.cost")], [#leant("Freyd.Alg.RelSet.Tardy.Fn.cost")],
  "Freyd.Alg.RelSet.Tardy.Fn.cost",
  [the largest penalty of any job in the schedule],
  [#rowkey("Freyd.Alg.RelSet.Tardy.bmax")], [#leant("Freyd.Alg.RelSet.Tardy.bmax")],
  "Freyd.Alg.RelSet.Tardy.bmax",
  [the larger of two numbers],
  [#rowkey("Freyd.Alg.RelSet.Tardy.R")], [#leant("Freyd.Alg.RelSet.Tardy.R")],
  "Freyd.Alg.RelSet.Tardy.R_eq",
  [`xs` costs no more than `ys`],
  [#rowkey("Freyd.Alg.RelSet.Tardy.add")], [#leant("Freyd.Alg.RelSet.Tardy.add")],
  "Freyd.Alg.RelSet.Tardy.add",
  [insert `j` anywhere in `xs`; `perm≜bagify bagify°=⦇[nil,add]⦈`],
  [#rowkey("Freyd.Alg.RelSet.Tardy.k")], [#leant("Freyd.Alg.RelSet.Tardy.k")],
  "Freyd.Alg.RelSet.Tardy.k",
  [the cost of a schedule from the cost of its front and the penalty of its last job],
  [#rowkey("Freyd.Alg.RelSet.Tardy.f")], [#leant("Freyd.Alg.RelSet.Tardy.f")],
  "Freyd.Alg.RelSet.Tardy.f",
  [the penalty of the last job, read off the bag before it],
  [#rowkey("Freyd.Alg.RelSet.Tardy.Q")], [#leant("Freyd.Alg.RelSet.Tardy.Q")],
  "Freyd.Alg.RelSet.Tardy.Q",
  [the last job of `u` gets no larger penalty than that of `v`],
  [#rowkey("Freyd.Alg.RelSet.Tardy.Q'")], [#leant("Freyd.Alg.RelSet.Tardy.Q'")],
  "Freyd.Alg.RelSet.Tardy.Q'",
  [`Q` on the `snag` summand: compare the penalties of the two last jobs],
// lean:AOP.A10_3_Tardy.bagifyFn_wrap@9bd5e745 lean:AOP.A10_3_Tardy.bagifyFn_snoc@301a3227 lean:AOP.A10_3_Tardy.kFn_inl@dbcc712f lean:AOP.A10_3_Tardy.kFn_inr@220dafce
// lean:AOP.A10_3_Tardy.gFn_inl@eb07155f lean:AOP.A10_3_Tardy.gFn_inr@655c3c27
// lean:Freyd.Alg.RelSet.Tardy.bagify@400950a5 lean:AOP.A10_3_Tardy.bagAlg@e7aab730 lean:AOP.A10_3_Tardy.snag@1f3be566 lean:AOP.A10_3_Tardy.Bag.nil@99bfc384 lean:AOP.A10_3_Tardy.Bag@eb33ed5e lean:AOP.A10_3_Tardy.bagify_cata@bcacee1a lean:Freyd.Alg.RelSet.Tardy.Fn.penalty@ff3abba7 lean:Freyd.Alg.RelSet.Tardy.Fn.cost@9e78397e lean:AOP.A10_3_Tardy.bmax@fc84cd0a lean:AOP.A10_3_Tardy.R@db17959c lean:AOP.A10_3_Tardy.Q@4533da60 lean:AOP.A10_3_Tardy.Q'@0eaae1da lean:AOP.A10_3_Tardy.f@582d995f lean:AOP.A10_3_Tardy.tardy_H@23f37b4f lean:AOP.A10_3_Tardy.nil_ne_snag@28c8cf7e
  [#rowkey("Freyd.Alg.RelSet.Tardy.g")], [#leant("Freyd.Alg.RelSet.Tardy.g")],
  "Freyd.Alg.RelSet.Tardy.g",
  [(10.5): the penalty of the last job, zero for the empty schedule],
  [#rowkey("Freyd.Alg.RelSet.Tardy.m")], [#leant("Freyd.Alg.RelSet.Tardy.m")],
  "Freyd.Alg.RelSet.Tardy.m",
  [(10.6), B&dM's `h` renamed as in @tardy-laws: the cost of the schedule before the last job],
// lean:Freyd.Alg.RelSet.Tardy.g@4ab2f12a lean:AOP.A10_3_Tardy.m@895650fd lean:Freyd.Alg.RelSet.Tardy.k@7716dabf lean:AOP.A10_3_Tardy.add@a93c9066 lean:Freyd.Alg.RelSet.Tardy.cost@c55b3476 lean:Freyd.Alg.RelSet.Tardy.penalty@c9716100 lean:AOP.A7_5_Van.bmax@6afe4642 lean:AOP.A10_3_Tardy.R_eq@5ae7b2aa
)]<tardy-defn>

// B&dM p.255: `cost` restated over the bag of the schedule, the form Proposition 9.3 asks for.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.cost_alg_k") \
    #src[the cost of a schedule is got from the cost and the bag of the schedule before its last
     job, and that job]],
  // lean:AOP.A10_3_Tardy.cost_alg_k@e7a35e83
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.cost_alg_k.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Tardy.cost_alg_k.rhs",
      src[`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))`, and `penalty(xs,j)` reads only the
       bag of `xs` — @Freyd.Alg.RelSet.Tardy.Fn.penalty]),
    // lean:AOP.A10_3_Tardy.penalty_eq_bagPenalty@e9bc8eb5
  ),
)]<tardy-cost-k>

// B&dM Exercise 10.5, p.258: "it is easy to check".
#disp(num: "Exercise 10.5")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.k_mono") \
    #src[a larger cost before the last job gives a larger cost after it]],
  // lean:AOP.A10_3_Tardy.k_mono@9a19f3c6
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.k_mono.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Tardy.k_mono.rhs",
      src[`bmax` is monotone in its first argument]),
  ),
)]<tardy-k-mono>

// B&dM (10.2), p.256: "(10.2) follows on appeal to Proposition 9.3".
#disp(num: "(10.2)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.tardy_mono") \
    #src[improving the schedule before the last job, among schedules of the same bag, improves
     the whole schedule]],
  // lean:AOP.A10_3_Tardy.tardy_mono@cc03f5c8
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.tardy_mono.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_mono.rhs",
      src[Proposition 9.3 at `S≜bagify`, `≼≜≥` — @dp-context-mono, with @tardy-cost-k and
       @tardy-k-mono]),
    // lean:AOP.A9_1.pres_in_context@12588624
  ),
)]<tardy-mono>

// B&dM (10.4)–(10.6), p.256, Exercise 10.6.
#disp(num: "(10.4)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.cost_alg_bmax") \
    #src[the cost of a schedule is the larger of the penalty of its last job and the cost of the
     schedule before it]],
  // lean:AOP.A10_3_Tardy.cost_alg_bmax@9df71c82
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.cost_alg_bmax.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Tardy.cost_alg_bmax.rhs",
      src[`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))` and `bmax` commutes — @Freyd.Alg.RelSet.Tardy.Fn.cost]),
  ),
)]<tardy-cost-bmax>

// B&dM (10.7), p.256, Exercise 10.7; needs `ct` and `wt` positive.
#disp(num: "(10.7)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.add_le") \
    #src[putting one more job anywhere into a schedule never lowers its cost]],
  // lean:AOP.A10_3_Tardy.add_le@069fcc4b
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.add_le.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Tardy.add_le.rhs",
      src[induction on where `j` goes: every job after it starts later, so no penalty falls]),
    // lean:AOP.A10_3_Tardy.cost_add_le@ed21959f lean:AOP.A10_3_Tardy.ctsum_add_le@427ceec2
  ),
)]<tardy-add>

// B&dM (10.8), p.256, Exercise 10.8.
#disp(num: "(10.8)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.bagify_recip_cata") \
    #src[the orderings of a bag with one more job are the orderings of the bag with that job put
     in anywhere]],
  // lean:AOP.A10_3_Tardy.bagify_recip_cata@47557b4a
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.bagify_recip_cata.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Tardy.bagify_recip_cata.rhs",
      src[take out the last copy of `j` and put it back — @Freyd.Alg.RelSet.Tardy.add]),
    // lean:AOP.A10_3_Tardy.add_del@18003f68 lean:AOP.A10_3_Tardy.blist_add@74e74883
  ),
)]<tardy-bag-cata>

// B&dM p.256, "putting (10.7) and (10.8) together".
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.bagify_recip_le") \
    #src[an ordering of a bag with one more job costs at least the cost of the ordering of the
     bag before its last job]],
  // lean:AOP.A10_3_Tardy.bagify_recip_le@ab39fee3
  lean-calc(calc-brl),
)]<tardy-bag-le>

// B&dM (10.3), p.257: the book's calculation, one row per hint.
#disp(num: "(10.3)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.tardy_greedy") \
    #src[a schedule of a bag ending in a job of least penalty is no worse than any schedule of
     the same bag]],
  // lean:AOP.A10_3_Tardy.tardy_greedy@98404d8f
  lean-calc(calc-tg, breaks: (4,)),
)]<tardy-greedy>

// B&dM p.257, "to complete the proof it is sufficient to show", `cost°` shunted.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.tardy_tail") \
    #src[a job whose penalty is at most the last penalty, put after a schedule costing at most
     the cost before the last job, gives a schedule costing at most the whole]],
  // lean:AOP.A10_3_Tardy.tardy_tail@b72f576a
  lean-calc(calc-tt, breaks: (3,)),
)]<tardy-tail>

// ONE WIRE, `Bag Job` to `[Job]`, one datatype lane carrying `bag` above the bead that eats it and
// `list` below.  The last row has NO `E` wire: `pick` is where the greedy program stops carrying a
// set at all.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[`schedule=(null→nil,pick (schedule×𝟙) snoc)`, #h(6pt) #leanf("Freyd.Alg.RelSet.Tardy.tardy_laws") \
    #src[an ordering of the given bag with least maximum penalty is got by taking a job of least
     penalty out of the bag, putting it last, and scheduling what is left the same way]],
  // lean:AOP.A10_3_Tardy.schedule_le@44177dc3 lean:AOP.A10_3_Tardy.schedule_unfold@d509c632
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.tardy_laws_prefixed.rhs", src[the specification — @Freyd.Alg.RelSet.Tardy.bagify]),
    // job-schedule row: Theorem 10.1
    // `(10.6)`'s arrow is B&dM's `h`, which is @dp-defn's algebra letter; renamed `m` here, since the
    // theorem it feeds and it would otherwise both be `h` in one table.
    (RQ, "Freyd.Alg.RelSet.Tardy.tardy_laws_prefixed.lhs",
      src[No greedy *reduce* exists — one would also
       solve every prefix of the input, and the best schedule of a prefix need not extend to a best
       schedule of the whole]),
    (RQ, "Freyd.Alg.RelSet.Tardy.tardy_branch.lhs",
      src[Proposition 10.1: `nil` and `snag` have disjoint ranges]),
    // lean:AOP.A10_3_Tardy.pick_branch_le@7525e408 lean:AOP.A10_3_Tardy.pick_branch_simple@43683444
    // No `E` lane: `pick` does the transpose and the `est` in one function, so nothing is ever a set.
    (RQ, "Freyd.Alg.RelSet.Tardy.pick_branch_le.lhs",
      src[`pick⊑`#frc([`snag°`])` est(Q')`, a partial function, quadratic in the number of jobs]),
  ),
  // lean:AOP.A10_3_Tardy.tardy_laws@3389e8bd lean:AOP.A10_3_Tardy.greedy_dp_context@da8a63ce lean:AOP.A10_3_Tardy.tardy_mono@cc03f5c8 lean:AOP.A10_3_Tardy.tardy_greedy@98404d8f
)]<tardy-laws>

== The TeX problem

// B&dM §10.4, p. 259.  The book's local `h` for `⦇[arb,step]⦈` is @dp-defn's algebra letter, so it
// is written `H°` here instead.  The base case of `f` is `a<0` on p. 262 and `p≤0` in the program.
#disp[#deftab(

  [#rowkey("Freyd.Alg.RelSet.Tex.intern")], [#leant("Freyd.Alg.RelSet.Tex.intern")],
  "Freyd.Alg.RelSet.Tex.intern",
  [the value of a decimal fraction, rounded to `16` binary places],
  [#rowkey("Freyd.Alg.RelSet.Tex.val")], [#leant("Freyd.Alg.RelSet.Tex.val")],
  "Freyd.Alg.RelSet.Tex.val",
  [the real number a digit list denotes after the decimal point],
  [#rowkey("Freyd.Alg.RelSet.Tex.shift")], [#leant("Freyd.Alg.RelSet.Tex.shift")],
  "Freyd.Alg.RelSet.Tex.shiftFn",
  [put digit `d` in front of `r`: `(d+r)/10`],
  [#rowkey("Freyd.Alg.RelSet.Tex.round")], [#leant("Freyd.Alg.RelSet.Tex.round")],
  "Freyd.Alg.RelSet.Tex.round_recip",
  [the nearest integer to `2¹⁶r`: `round r=n` iff `2n−1<2¹⁷r<2n+1`],
  [#rowkey("Freyd.Alg.RelSet.Tex.interval")], [#leant("Freyd.Alg.RelSet.Tex.interval")],
  "Freyd.Alg.RelSet.Tex.Fn.interval",
  [the open interval `((2n−1)/2¹⁷,(2n+1)/2¹⁷)` of the reals that round to `n`],
  [#rowkey("Freyd.Alg.RelSet.Tex.inrange")], [#leant("Freyd.Alg.RelSet.Tex.inrange")],
  "Freyd.Alg.RelSet.Tex.inrange",
  [`r` lies strictly inside `(a,b)`],
  [#rowkey("Freyd.Alg.RelSet.Tex.Legal")], [#leant("Freyd.Alg.RelSet.Tex.Legal")],
  "Freyd.Alg.RelSet.Tex.Legal",
  [(10.9): `0<b<1` and `a<b`; `Interval` is the legal pairs],
  [#rowkey("Freyd.Alg.RelSet.Tex.arb")], [#leant("Freyd.Alg.RelSet.Tex.arb")],
  "Freyd.Alg.RelSet.Tex.arb",
  [any legal interval],
  [#rowkey("Freyd.Alg.RelSet.Tex.step")], [#leant("Freyd.Alg.RelSet.Tex.step")],
  "Freyd.Alg.RelSet.Tex.Fn.step",
  [put digit `d` in front of both ends: `((d+a)/10,(d+b)/10)`],
  [#rowkey("Freyd.Alg.RelSet.Tex.H")], [#leant("Freyd.Alg.RelSet.Tex.H")],
  "Freyd.Alg.RelSet.Tex.H",
  [every digit list whose interval the given one is],
  [#rowkey("Freyd.Alg.RelSet.Tex.R")], [#leant("Freyd.Alg.RelSet.Tex.R")],
  "Freyd.Alg.RelSet.Tex.R",
  [`x` is no longer than `y`],
  [#rowkey("Freyd.Alg.RelSet.Tex.l")], [#leant("Freyd.Alg.RelSet.Tex.l")],
  "Freyd.Alg.RelSet.Tex.l",
  [the injection of the empty case into `FX=1+(Digit×X)`],
  [#rowkey("Freyd.Alg.RelSet.Tex.r")], [#leant("Freyd.Alg.RelSet.Tex.r")],
  "Freyd.Alg.RelSet.Tex.r",
  [the injection of the digit case into `FX=1+(Digit×X)`],
  [#rowkey("Freyd.Alg.RelSet.Tex.bang")], [#leant("Freyd.Alg.RelSet.Tex.bang")],
  "Freyd.Alg.RelSet.Tex.bang",
  [the one map to `1`],
  [#rowkey("Freyd.Alg.RelSet.Tex.Q")], [#leant("Freyd.Alg.RelSet.Tex.Q")],
  "Freyd.Alg.RelSet.Tex.Q",
  [`u` is the empty case and `z` a digit case, or `u=z`],
  [#rowkey("Freyd.Alg.RelSet.Tex.w")], [#leant("Freyd.Alg.RelSet.Tex.w")],
  "Freyd.Alg.RelSet.Tex.w",
  [`2¹⁷`],
// lean:AOP.A10_4_Tex.intern@56deb4eb
// lean:AOP.A10_4_Tex.val@b556684c lean:AOP.A10_4_Tex.zero@c2d020a3
// lean:AOP.A10_4_Tex.shift@522be7b7
// lean:AOP.A10_4_Tex.round@81382467
// lean:AOP.A10_4_Tex.Freyd.Alg.RelSet.Tex.interval@0be323e5
// lean:AOP.A10_4_Tex.inrange@324d56b2
// lean:AOP.A10_4_Tex.round_recip@8787573e
// lean:AOP.A10_4_Tex.R@6bf311b6
// lean:AOP.A10_4_Tex.Legal@ad318946
// lean:Freyd.Alg.RelSet.Tex.step@2407894f
// lean:AOP.A10_4_Tex.H@f5c2c294
)]<tex-defn>

// B&dM pp. 260-261: the fusion condition, the two cases of `[zero,shift]` one row each.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tex.tex_fusion") \
    #src[every interval got by folding a decimal's digits with `[arb,step]` has the decimal's value
     strictly inside it]],
    // lean:AOP.A10_4_Tex.tex_fusion@6c48b5bc
  lean-calc(calc-tf),
)]<tex-fusion>

// B&dM p. 262: the greedy condition, the book's hints one row each; `Q` here is the book's `Q°`
// because the chain runs in diagram order.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tex.tex_greedy") \
    #src[choosing by `Q` among the one-step decompositions before building with `F(X)` and `α`
     yields only decimals that are `R`-related to one built without choosing]],
    // lean:AOP.A10_4_Tex.tex_greedy@a8ba8ee9
  lean-calc(calc-tgr, breaks: (3, 6)),
)]<tex-greedy>

// ONE WIRE, `[0,2¹⁶)` to `Decimal`, in every row: `interval`, `H` and `[arb,step]°` are relations
// between objects with no functor of their own, so the picture never needs to open `Decimal`'s own
// `list`.  `interval` sits ABOVE the singleton in every row from the second on: it is the map
// pulled out of the transpose, and holding it at one height is what says the rest of the chain
// moved past it.

#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[`extern(n)=f(2n−1,2n+1)`, #h(6pt) #leanf("Freyd.Alg.RelSet.Tex.tex_laws") \
    #src[a shortest decimal whose internal representation is the given multiple of `2⁻¹⁶` is got by
     emitting the one digit the interval of admissible reals allows, until that interval contains
     zero and the empty decimal will do]],
  lean-calc(calc-tl),
  // lean:AOP.A10_4_Tex.tex_laws@9152d6ce lean:AOP.A10_4_Tex.tex_body_prefixed@765738e0
)
]<tex-laws>

// B&dM p.263, on points: no picture, the two sides are values, not the objects the panels carry.
// The base case is `a<0`/`p<0`, not the Gofer `p<=0`: at `p=0` the empty decimal's value `0` is
// not strictly inside `(a,b)`, so only `<` makes `f`'s output lie in the interval.
#disp[
  - #leanf("Freyd.Alg.RelSet.Tex.f_eq") \
    #src[`f` gives `(a,b)` the empty decimal when `a<0`, and otherwise the digit `d=⌊10b⌋`
     followed by what it gives `(10a−d,10b−d)`]
    // lean:AOP.A10_4_Tex.f_eq@6a541def
  - #leanf("Freyd.Alg.RelSet.Tex.tex_f") \
    #src[the least solution of the greedy recursion of @tex-laws is `f`]
    // lean:AOP.A10_4_Tex.tex_f@de95755e
  - #leanf("Freyd.Alg.RelSet.Tex.digit_unique") \
    #src[Exercise 10.12: two digits `d` and `e` with `0<10b−d<1` and `0<10b−e<1` are equal]
    // lean:AOP.A10_4_Tex.digit_unique@4fd18062
  - #leanf("Freyd.Alg.RelSet.Tex.Prog.f_nil") \
    #src[the program's first clause: `f(p,q)=[]` when `p<0`]
    // lean:AOP.A10_4_Tex.Prog.f_nil@e28d0992
  - #leanf("Freyd.Alg.RelSet.Tex.Prog.f_cons") \
    #src[the program's second clause: with `d=(10q) div w`, `f(p,q)` is `d` followed by
     `f(10p−w·d,10q−w·d)`]
    // lean:AOP.A10_4_Tex.Prog.f_cons@745b991e
  - #leanf("Freyd.Alg.RelSet.Tex.f_agree") \
    #src[on the pairs the program reaches from `interval n`, the integer `f` at `(p,q)` is a value
     of the rational `f` at `(p/w,q/w)`]
    // lean:AOP.A10_4_Tex.f_agree@326f321b
  - #leanf("Freyd.Alg.RelSet.Tex.tex_extern") \
    #src[`f` after `interval` is the program `extern`, whose value at `n` is `f(2n−1,2n+1)`]
    // lean:AOP.A10_4_Tex.tex_extern@5e874693
]<tex-extern>

// One run of the program on `n=8192`: its input, then one row per stage; each value is a theorem
// of the `TexRun` section of A10_4_Tex, cited beside its row.  A digit candidate prints as
// `r((d,(p,q)))`: the digit and the pair it leaves; the stop prints as `l(())`.
#ex-table(col: [*stage*],
  (sym: [input], type: leant("Freyd.Alg.RelSet.Tex.run_input.rhs"),
   value: leanf("Freyd.Alg.RelSet.Tex.run_input.rhs"),
   meaning: [`interval 8192`, the pair `(2n−1,2n+1)` around `8192/2¹⁶=0.125`]),
  // lean:AOP.A10_4_Tex.run_input@0fb9161f
  (sym: leann("Freyd.Alg.RelSet.Tex.pickL"), type: leant("Freyd.Alg.RelSet.Tex.run_pick0.rhs"),
   value: leanf("Freyd.Alg.RelSet.Tex.run_pick0.rhs"),
   meaning: [at `(16383,16385)` the one legal digit is `1`]),
  // lean:AOP.A10_4_Tex.run_pick0@0bd034d7
  (sym: leann("Freyd.Alg.RelSet.Tex.pickL"), type: leant("Freyd.Alg.RelSet.Tex.run_pick1.rhs"),
   value: leanf("Freyd.Alg.RelSet.Tex.run_pick1.rhs"),
   meaning: [at `(32758,32778)` the one legal digit is `2`]),
  // lean:AOP.A10_4_Tex.run_pick1@da1b6d3b
  (sym: leann("Freyd.Alg.RelSet.Tex.pickL"), type: leant("Freyd.Alg.RelSet.Tex.run_pick2.rhs"),
   value: leanf("Freyd.Alg.RelSet.Tex.run_pick2.rhs"),
   meaning: [at `(65436,65636)` the one legal digit is `5`]),
  // lean:AOP.A10_4_Tex.run_pick2@b93b8cd2
  (sym: leann("Freyd.Alg.RelSet.Tex.cands"), type: leant("Freyd.Alg.RelSet.Tex.run_cands3.rhs"),
   value: leanf("Freyd.Alg.RelSet.Tex.run_cands3.rhs"),
   meaning: [at `(−1000,1000)`, `p<0`: the stop and the digit `0` are both offered]),
  // lean:AOP.A10_4_Tex.run_cands3@dce42184
  (sym: leann("Freyd.Alg.RelSet.Tex.pickL"), type: leant("Freyd.Alg.RelSet.Tex.run_pick3.rhs"),
   value: leanf("Freyd.Alg.RelSet.Tex.run_pick3.rhs"),
   meaning: [`Q` keeps the stop]),
  // lean:AOP.A10_4_Tex.run_pick3@f5afab6b
  (sym: leann("Freyd.Alg.RelSet.Tex.run"), type: leant("Freyd.Alg.RelSet.Tex.run_out.rhs"),
   value: leanf("Freyd.Alg.RelSet.Tex.run_out.rhs"),
   meaning: [`0.125`: the digits `1`, `2`, `5`]),
  // lean:AOP.A10_4_Tex.run_out@93c35862
)<tex-run>

#pagebreak(weak: true)
#include "../allegory-appendix.typ"
