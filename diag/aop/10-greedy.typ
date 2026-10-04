#import "../note-prelude.typ": *
#show: note-chapter.with(10)
// note-split: chapter 10 — this header is written by scripts/note-split and stripped by scripts/note-join
= Greedy Algorithms <sec-greedy>

== Theory

// B&dM §10.1, p. 245.  Theorem 9.2 with `est(Q)` for `thin(Q)`: the same hypotheses, a much stronger
// conclusion, and one far harder to refine into a program.
#disp[#definition[
`h`, `T`, `R`, `H`, `M` as in @Freyd.Alg.M; #h(4pt) additionally `Q` a *connected* preorder on the sets
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
    // lean:AOP.A9_1.est_summand_le@096fa074
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
     // lean:AOP.A10_1.greedy_dp_lower@3dbc8cfa
  lean-calc(calc-gl),
)]<greedy-lower>

// The second half of the same proof.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.greedy_dp_upper") \
    #src[`H°` followed by the greedy body at `M` is `⊑R°`: an answer of the body is never worse
     than an answer of `H` to the same input]],
     // lean:AOP.A10_1.greedy_dp_upper@7abcb139
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

// B&dM §10.2, p. 246.  `V ≜ prefix° ∩ (fill fill°)` is the whole trick: a bare `prefix°` fails because
// a prefix of the expansion can be longer than the input once it crosses a tab stop.
#disp[#table(
  columns: (auto, auto, 1.3fr, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*type*], [*definition*], [*meaning*]),

  [#leann("Freyd.Alg.RelSet.Detab.detabFn")], [#leant("Freyd.Alg.RelSet.Detab.detabFn")],
  [#leanf("Freyd.Alg.RelSet.Detab.detab_cata")],
  [replace every tab by blanks up to the next tab stop; `H=detab°`],
  [#leann("Freyd.Alg.RelSet.Detab.expandFn")], [#leant("Freyd.Alg.RelSet.Detab.expandFn")],
  [#leanf("Freyd.Alg.RelSet.Detab.expandFn")],
  [a tab fills the line to the next stop; any other character is appended],
  [#leann("Freyd.Alg.RelSet.Detab.fillFn")], [#leant("Freyd.Alg.RelSet.Detab.fillFn")],
  [#leanf("Freyd.Alg.RelSet.Detab.fillFn")],
  [append blanks up to the next multiple of `n` columns],
  [#leann("Freyd.Alg.RelSet.Detab.colFn")], [#leant("Freyd.Alg.RelSet.Detab.colFn")],
  [#leanf("Freyd.Alg.RelSet.Detab.colFn")],
  [the column the string ends at: characters since the last newline],
  [#leann("Freyd.Alg.RelSet.Detab.R")], [#leant("Freyd.Alg.RelSet.Detab.R")],
  [#leanf("Freyd.Alg.RelSet.Detab.R")],
  [`x` is no longer than `y`],
  [#leann("Freyd.Alg.RelSet.Detab.U")], [#leant("Freyd.Alg.RelSet.Detab.U")],
  [#leanf("Freyd.Alg.RelSet.Detab.U")],
  [`a` is the tab or `a=b`],
  [#leann("Freyd.Alg.RelSet.Detab.V")], [#leant("Freyd.Alg.RelSet.Detab.V")],
  [#leanf("Freyd.Alg.RelSet.Detab.V")],
  [a prefix that fills to the same string],
  [#leann("Freyd.Alg.RelSet.Detab.Q")], [#leant("Freyd.Alg.RelSet.Detab.Q")],
  [#leanf("Freyd.Alg.RelSet.Detab.Q")],
  [compare two decompositions by `V` on the strings and `U` on the characters],
  [#leann("Freyd.Alg.RelSet.Detab.unfillFn")], [#leant("Freyd.Alg.RelSet.Detab.unfillFn")],
  [#leanf("Freyd.Alg.RelSet.Detab.unfillFn")],
  [the shortest prefix that fills to the same string],
  [#leann("Freyd.Alg.RelSet.Detab.tbcFn")], [#leant("Freyd.Alg.RelSet.Detab.tbcFn")],
  [#leanf("Freyd.Alg.RelSet.Detab.tbcFn")],
  [the number of trailing blanks],
  [#leann("Freyd.Alg.RelSet.Detab.tripleR")], [#leant("Freyd.Alg.RelSet.Detab.tripleR")],
  [#leanf("Freyd.Alg.RelSet.Detab.tripleR")],
  [what `entab` keeps: the unfilled output, its trailing blank count and its column],
// lean:AOP.A10_2_Detab.detab_cata@37355797
// lean:AOP.A10_2_Detab.R@5b23da25
// lean:AOP.A10_2_Detab.V@b0fc79bc
// lean:AOP.A10_2_Detab.Q@7a0a1541
)]<entab-defn>

// B&dM pp.249–250, "we argue": the claim the next chain leaves aside, one row per hint.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.expand_V") \
    #src[shortening the output of one `expand` step to a `V`-smaller string either keeps the whole
     step (`expand`) or drops its character and shortens its input string (`π₁V°`)]],
     // lean:AOP.A10_2_Detab.expand_V@56eb1503
  lean-calc(calc-ev, breaks: (3,)),
)]<entab-expand-V>

// B&dM p.249, "To prove V·detab ⊆ detab·R we reason", in diagram order: the note's `V` relates the
// shorter string to the longer, so the book's `V·detab` is `detab V°` here.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.detab_V_R") \
    #src[any `V`-shortening of `detab`'s output is `detab`'s output on an input no longer than the
     given one]],
     // lean:AOP.A10_2_Detab.detab_V_R@a6015fdd
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
      // lean:AOP.A10_2_Detab.entab_thin_condition@4bf50608
      decided at each step. `F(⊤,R)α⊑αR`#src[].
      // lean:AOP.A10_2_Detab.entab_mono@1561c867
      `detab prefix⊑R° detab` is
 FALSE #src[,
      // lean:AOP.A10_2_Detab.detab_prefix_false@5fe54dc9
 ] — at `n=8`,
      // lean:AOP.A10_2_Detab.detab_len_of_short@66be497e
      `detab [a,b,c,d,e,TB]=[a,b,c,d,e,BL,BL,BL]`, whose prefix
      `[a,b,c,d,e,BL,BL]` is longer than any input giving it, and `detab V°⊑R° detab`
 #src[]
      // lean:Freyd.Alg.RelSet.Detab.detab_V@332fe8ac lean:AOP.A10_2_Detab.entab_V@ff19c265
      holds. `expand V°⊑expand ∪ (π₁V°)`
 #src[] — shortening the output either leaves the
      // lean:AOP.A10_2_Detab.expand_V@56eb1503
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
    // lean:AOP.A10_2_Detab.detab_tupled@6e91c58a
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
    // lean:AOP.A10_2_Detab.detab_loop@9eb74257
  - #leanf("Freyd.Alg.RelSet.Detab.outl_loop") \
    #src[Exercise 10.1: when `step` only appends `f(c,a)` to the output and moves the state by
     `g`, the output of the loop is `loop'(f,g)`, which never carries the output]
    // lean:AOP.A10_2_Detab.outl_loop@069af82d
]<entab-detab-loop>

// B&dM p.250: the greedy step `min(V×U)Λexpand°`, read on points.
#disp[
  - #leanf("Freyd.Alg.RelSet.Detab.expand_recip_snoc") \
    #src[`expand` produces `x⧺[a]` from a tab after a string that fills to it, or from `x` and `a`]
    // lean:AOP.A10_2_Detab.expand_recip_snoc@7a7b0b8f
  - #leanf("Freyd.Alg.RelSet.Detab.fill_exists_iff") \
    #src[a string is a `fill` exactly when it ends in a blank on a tab stop]
    // lean:AOP.A10_2_Detab.fill_exists_iff@0db73b67
]<entab-step>

// B&dM p.251: (10.1) and the equations for `tbc` it gives.
#disp(num: "(10.1)")[
  - #leanf("Freyd.Alg.RelSet.Detab.entab_unfill") \
    #src[(10.1): the output of `entab` is that of `unfill x` followed by the trailing blanks held
     back]
    // lean:AOP.A10_2_Detab.entab_unfill@8725e757
  - #leanf("Freyd.Alg.RelSet.Detab.tbc_nil") \
    #src[the empty string has no trailing blanks]
    // lean:AOP.A10_2_Detab.tbc_nil@71e49d67
  - #leanf("Freyd.Alg.RelSet.Detab.tbc_snoc") \
    #src[a blank off a tab stop adds one held blank; anything else releases them all]
    // lean:AOP.A10_2_Detab.tbc_snoc@accc64d3
]<entab-tbc>

// B&dM pp.251–252: `⟨tbc,col⟩`, `triple` and `entab` as one fold.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.tbc_col_fold") \
    #src[one pass counts the held blanks and the column together]],
    // lean:AOP.A10_2_Detab.tbc_col_fold@a4bc74e4
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
    // lean:AOP.A10_2_Detab.triple_fold@69838b3d
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
    // lean:AOP.A10_2_Detab.entab_triple@31bc2b82
  lean-chain(
    (none, "Freyd.Alg.RelSet.Detab.entab_triple.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Detab.entab_triple.rhs", src[(10.1) — @entab-tbc]),
  ),
)]<entab-entab>


== The minimum tardiness problem

// B&dM §10.3, p. 253.  Both conditions need context, and `cost` has to be restated over `perm xs`
// before Proposition 9.3 fits — `penalty` reads the bag of scheduled jobs, not their order.
#disp[#table(
  columns: (auto, auto, 1.3fr, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*type*], [*definition*], [*meaning*]),

  [#leann("Freyd.Alg.RelSet.Tardy.Bag")], [#leant("Freyd.Alg.RelSet.Tardy.Bag")],
  [#leanf("Freyd.Alg.RelSet.Tardy.Bag")],
  [a bag of jobs: a list up to reordering],
  [#leann("Freyd.Alg.RelSet.Tardy.snag")], [#leant("Freyd.Alg.RelSet.Tardy.snag")],
  [#leanf("Freyd.Alg.RelSet.Tardy.snag")],
  [put one job into a bag],
  [#leann("Freyd.Alg.RelSet.Tardy.bagify")], [#leant("Freyd.Alg.RelSet.Tardy.bagify")],
  [#leanf("Freyd.Alg.RelSet.Tardy.bagify_cata")],
  [forget the order of a schedule; `H=bagify°` lists every schedule of a bag],
  [#leann("Freyd.Alg.RelSet.Tardy.penalty")], [#leant("Freyd.Alg.RelSet.Tardy.penalty")],
  [#leanf("Freyd.Alg.RelSet.Tardy.penalty")],
  [how late job `j` finishes after the schedule `xs`, times its weight],
  [#leann("Freyd.Alg.RelSet.Tardy.cost")], [#leant("Freyd.Alg.RelSet.Tardy.cost")],
  [#leanf("Freyd.Alg.RelSet.Tardy.cost")],
  [the largest penalty of any job in the schedule],
  [#leann("Freyd.Alg.RelSet.Tardy.bmax")], [#leant("Freyd.Alg.RelSet.Tardy.bmax")],
  [#leanf("Freyd.Alg.RelSet.Tardy.bmax")],
  [the larger of two numbers],
  [#leann("Freyd.Alg.RelSet.Tardy.R")], [#leant("Freyd.Alg.RelSet.Tardy.R")],
  [#leanf("Freyd.Alg.RelSet.Tardy.R_eq")],
  [`xs` costs no more than `ys`],
  [#leann("Freyd.Alg.RelSet.Tardy.add")], [#leant("Freyd.Alg.RelSet.Tardy.add")],
  [#leanf("Freyd.Alg.RelSet.Tardy.add")],
  [insert `j` anywhere in `xs`; `perm≜bagify bagify°=⦇[nil,add]⦈`],
  [#leann("Freyd.Alg.RelSet.Tardy.k")], [#leant("Freyd.Alg.RelSet.Tardy.k")],
  [#leanf("Freyd.Alg.RelSet.Tardy.k")],
  [the cost of a schedule from the cost of its front and the penalty of its last job],
  [#leann("Freyd.Alg.RelSet.Tardy.fFn")], [#leant("Freyd.Alg.RelSet.Tardy.fFn")],
  [#leanf("Freyd.Alg.RelSet.Tardy.fFn")],
  [the penalty of the last job, read off the bag before it],
  [#leann("Freyd.Alg.RelSet.Tardy.Q")], [#leant("Freyd.Alg.RelSet.Tardy.Q")],
  [#leanf("Freyd.Alg.RelSet.Tardy.Q")],
  [the last job of `u` gets no larger penalty than that of `v`],
  [#leann("Freyd.Alg.RelSet.Tardy.Q'")], [#leant("Freyd.Alg.RelSet.Tardy.Q'")],
  [#leanf("Freyd.Alg.RelSet.Tardy.Q'")],
  [`Q` on the `snag` summand: compare the penalties of the two last jobs],
// lean:AOP.A10_3_Tardy.bagify@31766900 lean:AOP.A10_3_Tardy.bagAlg@d0f7446e lean:AOP.A10_3_Tardy.snag@c772c474 lean:AOP.A10_3_Tardy.nilBag@f9126385 lean:AOP.A10_3_Tardy.Bag@257c054f lean:AOP.A10_3_Tardy.bagify_cata@bcacee1a lean:AOP.A10_3_Tardy.penalty@cb396f8a lean:AOP.A10_3_Tardy.cost@a1054f80 lean:AOP.A10_3_Tardy.bmax@fc84cd0a lean:AOP.A10_3_Tardy.R@be4c6db5 lean:AOP.A10_3_Tardy.Q@f060536c lean:AOP.A10_3_Tardy.Q'@ea357147 lean:AOP.A10_3_Tardy.fFn@94a6f009 lean:AOP.A10_3_Tardy.tardy_H@23f37b4f lean:AOP.A10_3_Tardy.nil_ne_snag@77e87166
  [#leann("Freyd.Alg.RelSet.Tardy.g")], [#leant("Freyd.Alg.RelSet.Tardy.g")],
  [#leanf("Freyd.Alg.RelSet.Tardy.g"), #leanf("Freyd.Alg.RelSet.Tardy.g_apply")],
  [(10.5): the penalty of the last job, zero for the empty schedule],
  [#leann("Freyd.Alg.RelSet.Tardy.m")], [#leant("Freyd.Alg.RelSet.Tardy.m")],
  [#leanf("Freyd.Alg.RelSet.Tardy.m")],
  [(10.6), B&dM's `h` renamed as in @tardy-laws: the cost of the schedule before the last job],
// lean:AOP.A10_3_Tardy.g@41729767 lean:AOP.A10_3_Tardy.m@7bff7a03 lean:AOP.A10_3_Tardy.k@daadb101 lean:AOP.A10_3_Tardy.add@a93c9066 lean:AOP.A10_3_Tardy.costR@42c139cf lean:AOP.A10_3_Tardy.penaltyR@89469572 lean:AOP.A10_3_Tardy.bmaxR@c4eeff86 lean:AOP.A10_3_Tardy.R_eq@8f5cc907
)]<tardy-defn>

// B&dM p.255: `cost` restated over the bag of the schedule, the form Proposition 9.3 asks for.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.cost_alg_k") \
    #src[the cost of a schedule is got from the cost and the bag of the schedule before its last
     job, and that job]],
  // lean:AOP.A10_3_Tardy.cost_alg_k@7f483422
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.cost_alg_k.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Tardy.cost_alg_k.rhs",
      src[`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))`, and `penalty(xs,j)` reads only the
       bag of `xs` — @Freyd.Alg.RelSet.Tardy.penalty]),
    // lean:AOP.A10_3_Tardy.penalty_eq_bagPenalty@437884a3
  ),
)]<tardy-cost-k>

// B&dM Exercise 10.5, p.258: "it is easy to check".
#disp(num: "Exercise 10.5")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.k_mono") \
    #src[a larger cost before the last job gives a larger cost after it]],
  // lean:AOP.A10_3_Tardy.k_mono@4ce1b877
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
  // lean:AOP.A10_3_Tardy.tardy_mono@f508140f
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.tardy_mono.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_mono.rhs",
      src[Proposition 9.3 at `S≜bagify`, `≤≜≥` — @dp-context-mono, with @tardy-cost-k and
       @tardy-k-mono]),
    // lean:AOP.A9_1.monoAlg_in_context@f0a1b13c
  ),
)]<tardy-mono>

// B&dM (10.4)–(10.6), p.256, Exercise 10.6.
#disp(num: "(10.4)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.cost_alg_bmax") \
    #src[the cost of a schedule is the larger of the penalty of its last job and the cost of the
     schedule before it]],
  // lean:AOP.A10_3_Tardy.cost_alg_bmax@6bdd5030
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.cost_alg_bmax.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Tardy.cost_alg_bmax.rhs",
      src[`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))` and `bmax` commutes — @Freyd.Alg.RelSet.Tardy.cost]),
  ),
)]<tardy-cost-bmax>

// B&dM (10.7), p.256, Exercise 10.7; needs `ct` and `wt` positive.
#disp(num: "(10.7)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.add_le") \
    #src[putting one more job anywhere into a schedule never lowers its cost]],
  // lean:AOP.A10_3_Tardy.add_le@d29b4a89
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.add_le.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Tardy.add_le.rhs",
      src[induction on where `j` goes: every job after it starts later, so no penalty falls]),
    // lean:AOP.A10_3_Tardy.cost_add_le@4e677fdd lean:AOP.A10_3_Tardy.ctsum_add_le@aababe5b
  ),
)]<tardy-add>

// B&dM (10.8), p.256, Exercise 10.8.
#disp(num: "(10.8)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.bagify_recip_cata") \
    #src[the orderings of a bag with one more job are the orderings of the bag with that job put
     in anywhere]],
  // lean:AOP.A10_3_Tardy.bagify_recip_cata@9781e524
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
  // lean:AOP.A10_3_Tardy.bagify_recip_le@583c3c44
  lean-calc(calc-brl),
)]<tardy-bag-le>

// B&dM (10.3), p.257: the book's calculation, one row per hint.
#disp(num: "(10.3)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.tardy_greedy") \
    #src[a schedule of a bag ending in a job of least penalty is no worse than any schedule of
     the same bag]],
  // lean:AOP.A10_3_Tardy.tardy_greedy@5953b96f
  lean-calc(calc-tg, breaks: (4,)),
)]<tardy-greedy>

// B&dM p.257, "to complete the proof it is sufficient to show", `cost°` shunted.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.tardy_tail") \
    #src[a job whose penalty is at most the last penalty, put after a schedule costing at most
     the cost before the last job, gives a schedule costing at most the whole]],
  // lean:AOP.A10_3_Tardy.tardy_tail@d6af1dd1
  lean-calc(calc-tt, breaks: (3,)),
)]<tardy-tail>

// ONE WIRE, `Bag Job` to `[Job]`, one datatype lane carrying `bag` above the bead that eats it and
// `list` below.  The last row has NO `E` wire: `pick` is where the greedy program stops carrying a
// set at all.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[`schedule=(null→nil,pick (schedule×𝟙) snoc)`, #h(6pt) #leanf("Freyd.Alg.RelSet.Tardy.tardy_laws") \
    #src[an ordering of the given bag with least maximum penalty is got by taking a job of least
     penalty out of the bag, putting it last, and scheduling what is left the same way]],
  // lean:AOP.A10_3_Tardy.schedule_le@af8c3e61 lean:AOP.A10_3_Tardy.schedule_unfold@d98fd6f6
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
    // lean:AOP.A10_3_Tardy.pick_branch_le@ee1b2a00 lean:AOP.A10_3_Tardy.pick_branch_simple@43683444
    // No `E` lane: `pick` does the transpose and the `est` in one function, so nothing is ever a set.
    (RQ, "Freyd.Alg.RelSet.Tardy.pick_branch_le.lhs",
      src[`pick⊑`#frc([`snag°`])` est(Q')`, a partial function, quadratic in the number of jobs]),
  ),
  // lean:AOP.A10_3_Tardy.tardy_laws@9a4c81ea lean:AOP.A10_3_Tardy.greedy_dp_context@78d89cdf lean:AOP.A10_3_Tardy.tardy_mono@f508140f lean:AOP.A10_3_Tardy.tardy_greedy@5953b96f
)]<tardy-laws>

== The TeX problem

// B&dM §10.4, p. 259.  The book's local `h` for `⦇[arb,step]⦈` is @dp-defn's algebra letter, so it
// is written `H°` here instead.  The base case of `f` is `a<0` on p. 262 and `p≤0` in the program.
#disp[#table(
  columns: (auto, auto, 1.3fr, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*type*], [*definition*], [*meaning*]),

  [#leann("Freyd.Alg.RelSet.Tex.intern")], [#leant("Freyd.Alg.RelSet.Tex.intern")],
  [#leanf("Freyd.Alg.RelSet.Tex.intern")],
  [the value of a decimal fraction, rounded to `16` binary places],
  [#leann("Freyd.Alg.RelSet.Tex.val")], [#leant("Freyd.Alg.RelSet.Tex.val")],
  [#leanf("Freyd.Alg.RelSet.Tex.val")],
  [the real number a digit list denotes after the decimal point],
  [#leann("Freyd.Alg.RelSet.Tex.shift")], [#leant("Freyd.Alg.RelSet.Tex.shift")],
  [#leanf("Freyd.Alg.RelSet.Tex.shift"), #leanf("Freyd.Alg.RelSet.Tex.shiftFn")],
  [put digit `d` in front of `r`: `(d+r)/10`],
  [#leann("Freyd.Alg.RelSet.Tex.round")], [#leant("Freyd.Alg.RelSet.Tex.round")],
  [#leanf("Freyd.Alg.RelSet.Tex.round"), #leanf("Freyd.Alg.RelSet.Tex.round_recip")],
  [the nearest integer to `2¹⁶r`: `round r=n` iff `2n−1<2¹⁷r<2n+1`],
  [#leann("Freyd.Alg.RelSet.Tex.interval")], [#leant("Freyd.Alg.RelSet.Tex.interval")],
  [#leanf("Freyd.Alg.RelSet.Tex.intervalFn")],
  [the open interval `((2n−1)/2¹⁷,(2n+1)/2¹⁷)` of the reals that round to `n`],
  [#leann("Freyd.Alg.RelSet.Tex.inrange")], [#leant("Freyd.Alg.RelSet.Tex.inrange")],
  [#leanf("Freyd.Alg.RelSet.Tex.inrange")],
  [`r` lies strictly inside `(a,b)`],
  [#leann("Freyd.Alg.RelSet.Tex.Legal")], [#leant("Freyd.Alg.RelSet.Tex.Legal")],
  [#leanf("Freyd.Alg.RelSet.Tex.Legal")],
  [(10.9): `0<b<1` and `a<b`; `Interval` is the legal pairs],
  [#leann("Freyd.Alg.RelSet.Tex.arb")], [#leant("Freyd.Alg.RelSet.Tex.arb")],
  [#leanf("Freyd.Alg.RelSet.Tex.arb")],
  [any legal interval],
  [#leann("Freyd.Alg.RelSet.Tex.step")], [#leant("Freyd.Alg.RelSet.Tex.step")],
  [#leanf("Freyd.Alg.RelSet.Tex.stepFn")],
  [put digit `d` in front of both ends: `((d+a)/10,(d+b)/10)`],
  [#leann("Freyd.Alg.RelSet.Tex.H")], [#leant("Freyd.Alg.RelSet.Tex.H")],
  [#leanf("Freyd.Alg.RelSet.Tex.H")],
  [every digit list whose interval the given one is],
  [#leann("Freyd.Alg.RelSet.Tex.R")], [#leant("Freyd.Alg.RelSet.Tex.R")],
  [#leanf("Freyd.Alg.RelSet.Tex.R")],
  [`x` is no longer than `y`],
  [#leann("Freyd.Alg.RelSet.Tex.l")], [#leant("Freyd.Alg.RelSet.Tex.l")],
  [#leanf("Freyd.Alg.RelSet.Tex.l")],
  [the injection of the empty case into `FX=1+(Digit×X)`],
  [#leann("Freyd.Alg.RelSet.Tex.r")], [#leant("Freyd.Alg.RelSet.Tex.r")],
  [#leanf("Freyd.Alg.RelSet.Tex.r")],
  [the injection of the digit case into `FX=1+(Digit×X)`],
  [#leann("Freyd.Alg.RelSet.Tex.bang")], [#leant("Freyd.Alg.RelSet.Tex.bang")],
  [#leanf("Freyd.Alg.RelSet.Tex.bang")],
  [the one map to `1`],
  [#leann("Freyd.Alg.RelSet.Tex.Q")], [#leant("Freyd.Alg.RelSet.Tex.Q")],
  [#leanf("Freyd.Alg.RelSet.Tex.Q"), #leanf("Freyd.Alg.RelSet.Tex.Q_apply")],
  [`u` is the empty case and `z` a digit case, or `u=z`],
  [#leann("Freyd.Alg.RelSet.Tex.w")], [#leant("Freyd.Alg.RelSet.Tex.w")],
  [#leanf("Freyd.Alg.RelSet.Tex.w")],
  [`2¹⁷`],
// lean:AOP.A10_4_Tex.intern@56deb4eb
// lean:AOP.A10_4_Tex.val@b556684c lean:AOP.A10_4_Tex.zero@c2d020a3
// lean:AOP.A10_4_Tex.shift@522be7b7
// lean:AOP.A10_4_Tex.round@81382467
// lean:AOP.A10_4_Tex.Freyd.Alg.RelSet.Tex.interval@9dc05d20
// lean:AOP.A10_4_Tex.inrange@324d56b2
// lean:AOP.A10_4_Tex.round_recip@8787573e
// lean:AOP.A10_4_Tex.R@393e9bb8
// lean:AOP.A10_4_Tex.Legal@ad318946
// lean:AOP.A10_4_Tex.step@1b245185
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
    // lean:AOP.A10_4_Tex.f_eq@c0c2128a
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
    // lean:AOP.A10_4_Tex.Prog.f_cons@7cf555c4
  - #leanf("Freyd.Alg.RelSet.Tex.f_agree") \
    #src[on the pairs the program reaches from `interval n`, the integer `f` at `(p,q)` is a value
     of the rational `f` at `(p/w,q/w)`]
    // lean:AOP.A10_4_Tex.f_agree@e4dce558
  - #leanf("Freyd.Alg.RelSet.Tex.tex_extern") \
    #src[`f` after `interval` is the program `extern`, whose value at `n` is `f(2n−1,2n+1)`]
    // lean:AOP.A10_4_Tex.tex_extern@5e874693
]<tex-extern>

#pagebreak(weak: true)
#include "../allegory-appendix.typ"
