#import "../note-prelude.typ": *
#show: note-chapter.with(16)
// note-split: chapter 16 — this header is written by scripts/note-split and stripped by scripts/note-join
= Greedy Algorithms <sec-greedy>

== Theory

// B&dM §10.1, p. 245.  Theorem 9.2 with `est(Q)` for `thin(Q)`: the same hypotheses, a much stronger
// conclusion, and one far harder to refine into a program.
#disp[#definition[
`h`, `T`, `R`, `H`, `M` as in @dp-defn; #h(4pt) additionally `Q` a *connected* preorder on the sets
$frac(#[`T°`], ∋)$ returns, so that $frac(#[`T°`], ∋)$ `est(Q)` is entire.
]]<greedy-defn>

#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.greedy_dp") \
    #src[the same optimum reached by keeping ONE decomposition at each step, so that no set is ever
 carried and the recursion runs on values alone #h(4pt) ]],
  lean-chain(
    (none, "Freyd.Alg.greedy_dp_step1.rhs",
      src[`H≜⦇T⦈°⦇h⦈` — @greedy-defn]),
    // dp-shrink row: Theorem 10.1
    // `est(Q) : E(FA)⟶FA` kills the SET but not the `F` under it, so its wire spans the `E` lane
    // down to the object wire, crossing `F` — the whole difference from @dp-laws' second row.
    (RQ, "Freyd.Alg.greedy_dp.lhs.body", src[]),
    // lean:AOP.A9_1.est_summand_le@1efecafb
    // The branch, not the conditional; nothing survives outside the set here, so `est(Qᵢ)` lands on
    // the object wire.
    (EQ, "Freyd.Alg.RelSet.SL.est_arm₂_le.lhs",
      src[Proposition 10.1, `V₂V₁°=𝟘`]),
  ),
)]<greedy-laws>

// B&dM Theorem 10.1, p. 245, "left as an exercise": the proof of Theorem 9.2 with `est(Q)` for
// `thin(Q)`.  Knaster–Tarski needs the body at `M` below `M`; `M=H∩(H°\R°)` splits that in two.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.greedy_dp_lower") \
    #src[taking the input apart in one `Q`-extreme way, solving the parts by `M` and assembling by
     `h` returns only what `H` returns]],
     // lean:AOP.A10_1.greedy_dp_lower@44565adb
  lean-chain(
    (none, "Freyd.Alg.greedy_dp_lower.lhs", []),
    (SQ, "Freyd.Alg.greedy_dp_lower_step1.rhs", src[`est(Q)⊑∋` — @est-defn]),
     // lean:AOP.A10_1.greedy_dp_lower_step1@66f7230b
    (EQ, "Freyd.Alg.dynamic_programming_lower_step2.rhs", src[#frc([`T°`])`∋=T°` — @pow-laws]),
    (SQ, "Freyd.Alg.dynamic_programming_lower_step3.rhs", src[`M⊑`#frc([`H`])`∋=H` — @est-up]),
    (EQ, "Freyd.Alg.greedy_dp_lower.rhs", src[`T°F(H)h=H` — @hylo-mu]),
  ),
)]<greedy-lower>

// The second half of the same proof.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.greedy_dp_upper") \
    #src[`H°` followed by the greedy body at `M` is `⊑R°`: an answer of the body is never worse
     than an answer of `H` to the same input]],
     // lean:AOP.A10_1.greedy_dp_upper@2d89b7d1
  lean-chain((
    (none, "Freyd.Alg.greedy_dp_upper_step1.lhs", []),
    (EQ, "Freyd.Alg.greedy_dp_upper_step1.rhs",
      src[`H°=h°F(H°)T` — @hylo-mu]),
     // lean:AOP.A10_1.greedy_dp_upper_step1@8ec8c9b2
    (SQ, "Freyd.Alg.greedy_dp_upper_step2.rhs",
      src[`T`#frc([`T°`])`⊑∈`]),
     // lean:AOP.A10_1.greedy_dp_upper_step2@4a189407
    (SQ, "Freyd.Alg.greedy_dp_upper_step3.rhs", src[`∈est(Q)⊑Q°` — @est-up]),
     // lean:AOP.A10_1.greedy_dp_upper_step3@c17d0163
  ), (
    (SQ, "Freyd.Alg.greedy_dp_upper_step4.rhs",
      src[`QF(H)h⊑F(H)hR` conversed]),
     // lean:AOP.A10_1.greedy_dp_upper_step4@bbace0f9
    (SQ, "Freyd.Alg.greedy_dp_upper_step5.rhs", src[`H°M⊑R°` under `F` — @est-up]),
     // lean:AOP.A10_1.greedy_dp_upper_step5@49e70aa8
    (SQ, "Freyd.Alg.greedy_dp_upper_step6.rhs",
      src[`h°F(R°)h⊑R°`]),
     // lean:AOP.A10_1.greedy_dp_upper_step6@8d3afe63
    (SQ, "Freyd.Alg.greedy_dp_upper.rhs", src[`R` transitive]),
  )),
)]<greedy-upper>

// B&dM Proposition 10.1, p. 245, "a variation on Proposition 9.1", in Rel(Set).  The book's
// `(ran V₁ → W₁, W₂)` is the union below: off `ran V₁ ∪ ran V₂` both are empty.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.greedy_disjoint_ranges") \
    #src[when `V₁` and `V₂` have disjoint ranges, the greedy step over `[V₁,V₂]` runs the `V₁` step
     on inputs `V₁` reaches and the `V₂` step on inputs `V₂` reaches]],
     // lean:AOP.A10_1.greedy_disjoint_ranges@611c02b4
  lean-chain(
    (none, "Freyd.Alg.RelSet.greedy_disjoint_ranges_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.greedy_disjoint_ranges_step1.rhs.inl",
      src[empty off `ran V₁ ∪ ran V₂`]),
     // lean:AOP.A10_1.greedy_disjoint_ranges_step1@631ac87a
    (EQ, "Freyd.Alg.RelSet.greedy_disjoint_ranges_step2.rhs.inl",
      src[#frc([`[V₁,V₂]°`])` = `#frc([`V₁°`])`P(inl)` on `ran V₁` — @dp-disjoint]),
     // lean:AOP.A10_1.greedy_disjoint_ranges_step2@f2908d30
    (EQ, "Freyd.Alg.RelSet.greedy_disjoint_ranges_step3.rhs.inl",
      src[`P(inl)est(Q₁+Q₂)=est(Q₁)inl`]),
     // lean:AOP.A10_1.powerRel_inl_est@2ceb36e3 lean:AOP.A10_1.greedy_disjoint_ranges_step3@3a192617
    (EQ, "Freyd.Alg.RelSet.greedy_disjoint_ranges_step4.rhs.inl", src[`inl[U₁,U₂]=U₁`]),
  ),
)]<greedy-disjoint>

== The detab-entab problem

// B&dM §10.2, p. 246.  `V ≜ prefix° ∩ (fill fill°)` is the whole trick: a bare `prefix°` fails because
// a prefix of the expansion can be longer than the input once it crosses a tab stop.
#disp[#definition[
`detab≜⦇[nil,expand]⦈ : String⟶String` #src[]
// lean:AOP.A10_2_Detab.detab_cata@37355797
over snoc-lists, #h(4pt) `α≜[nil,snoc]`, #h(4pt)
`H=detab°`; #h(4pt) `expand (xs,a)=(a=TB→fill xs,xs⧺[a])`, #h(4pt)
`fill xs=xs⧺blanks (n−(col xs) mod n)`.

`col≜⦇[zero,count]⦈`, #h(4pt) `count (c,a)=(a=NL→0,c+1)`; #h(4pt) `TB` the tab, `BL` the
blank, `NL` the newline, tab stops every `n` columns.

`R≜length≤length°` #src[], #h(4pt)
// lean:AOP.A10_2_Detab.R@5b23da25
`U` the preorder with `a U b⟺a=TB∨a=b`, #h(4pt)
`V≜prefix°∩(fill fill°)` #src[], #h(4pt)
// lean:AOP.A10_2_Detab.V@b0fc79bc
`Q≜𝟙+(V×U)` #src[].
// lean:AOP.A10_2_Detab.Q@7a0a1541

`unfill xs` the shortest prefix of `xs` with `fill (unfill xs)=fill xs`; #h(4pt) `tbc` the trailing
blank count, #h(4pt) `triple≜⟨unfill entab,⟨tbc,col⟩⟩`.
]]<entab-defn>

// B&dM pp.249–250, "we argue": the claim the next chain leaves aside, one row per hint.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.expand_V") \
    #src[shortening the output of one `expand` step to a `V`-smaller string either keeps the whole
     step (`expand`) or drops its character and shortens its input string (`π₁V°`)]],
     // lean:AOP.A10_2_Detab.expand_V@56eb1503
  lean-chain((
    (none, "Freyd.Alg.RelSet.Detab.expand_V_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Detab.expand_V_step1.rhs",
      src[definition of `expand`]),
     // lean:AOP.A10_2_Detab.expand_V_step1@d11ccbc6
    (EQ, "Freyd.Alg.RelSet.Detab.expand_V_step2.rhs",
      src[conditionals distribute]),
     // lean:AOP.A10_2_Detab.expand_V_step2@390338c4
  ), (
    (EQ, "Freyd.Alg.RelSet.Detab.expand_V_step3.rhs", src[`fill V°=fill` (Ex. 10.4)]),
     // lean:AOP.A10_2_Detab.expand_V_step3@1a325a1e lean:AOP.A10_2_Detab.fill_V@6f4dc6ad
    (SQ, "Freyd.Alg.RelSet.Detab.expand_V_step4.rhs", src[`snoc V°⊑snoc∪(π₁V°)` (Ex. 10.4)]),
     // lean:AOP.A10_2_Detab.expand_V_step4@1743f6f5 lean:AOP.A10_2_Detab.snoc_V@2f6227ca
    (SQ, "Freyd.Alg.RelSet.Detab.expand_V_step5.rhs",
      src[definition of `expand`, guard dropped]),
     // lean:AOP.A10_2_Detab.expand_V_step5@664b51b5
  )),
)]<entab-expand-V>

// B&dM p.249, "To prove V·detab ⊆ detab·R we reason", in diagram order: the note's `V` relates the
// shorter string to the longer, so the book's `V·detab` is `detab V°` here.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.detab_V_R") \
    #src[any `V`-shortening of `detab`'s output is `detab`'s output on an input no longer than the
     given one]],
     // lean:AOP.A10_2_Detab.detab_V_R@a6015fdd
  lean-chain((
    (none, "Freyd.Alg.RelSet.Detab.detab_V_R_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Detab.detab_V_R_step1.rhs",
      src[`detab` is a fold: `detab=α°F(detab)[nil,expand]` — @entab-defn]),
     // lean:AOP.A10_2_Detab.detab_V_R_step1@7202f1a5
    (EQ, "Freyd.Alg.RelSet.Detab.detab_V_R_step2.rhs",
      src[coproducts, and `nil V°=nil` (Exercise 10.4)]),
     // lean:AOP.A10_2_Detab.detab_V_R_step2@17093b20 lean:AOP.A10_2_Detab.nil_V@ab8b8818
    (SQ, "Freyd.Alg.RelSet.Detab.detab_V_R_step3.rhs", src[the claim — @entab-expand-V]),
     // lean:AOP.A10_2_Detab.detab_V_R_step3@63a29781
  ), (
    (EQ, "Freyd.Alg.RelSet.Detab.detab_V_R_step4.rhs",
      src[distributing `∪`; the fold again, and the definition of `F`]),
     // lean:AOP.A10_2_Detab.detab_V_R_step4@12589ca1
    (EQ, "Freyd.Alg.RelSet.Detab.detab_V_R_step5.rhs",
      src[naturality of `π₁`: `(detab×𝟙)π₁=π₁ detab`; `snoc°π₁` is `init`]),
     // lean:AOP.A10_2_Detab.detab_V_R_step5@84af6677
    (SQ, "Freyd.Alg.RelSet.Detab.detab_V_R_step6.rhs",
      src[`init` is inductive, so `X≜detab V°`, a solution of `X⊑detab∪(init X)`, lies below the
       greatest one, `prefix detab` (induction on the input); `prefix⊑R°`]),
     // lean:AOP.A10_2_Detab.detab_V_R_step6@6f212d06
  )),
)]<entab-detab-V>

// ONE WIRE, `String` to `String`; `F(X)h` is drawn as the ONE bead the formula writes,
// `(𝟙+(X×𝟙))[nil,snoc]`, so the `list` lane pinches twice rather than three times.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Detab.entab_laws") \
    #src[the shortest input `detab` expands to the given output is one pass along that output,
     holding each blank back and cashing the held blanks in for a tab wherever the column reaches a
     tab stop]],
  lean-chain(
    (none, "Freyd.Alg.RelSet.Detab.entab_laws.rhs",
      src[the specification — @entab-defn; `detab entab=𝟙` and nothing
       shorter does]),
    // `[nil,expand]°` opens `−×Char` inside the set the singleton opened; `est(Q)` kills that set but
    // not the `F` under it, so its wire spans down to the object wire, crossing `F`.
    (RQ, "Freyd.Alg.RelSet.Detab.entab_laws.lhs.body", [
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
    (EQ, "Freyd.Alg.RelSet.Detab.entab_branch.lhs",
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

#disp[
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
#disp[
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
#disp[#definition[
`FX=1+(X×Job)`, #h(4pt) `α≜[nil,snoc]` on schedules, #h(4pt) `β≜[nil,snag]` on bags,
`snag` putting a job into a bag; #h(4pt) `bagify≜⦇β⦈ : [Job]⟶Bag Job`, #h(4pt) `H=bagify°`.

`ct`, `dt`, `wt : Job⟶Real` the completion, due and weighting quantities of a job; #h(4pt)
`penalty(xs,j)=(sum(list(ct)(xs))+ct(j)−dt(j))×wt(j)`.

`cost≜` $frac(#[`prefix`], ∋)$ `P(α° [zero,penalty]) est(≥)`, #h(4pt) `cost []=0`, #h(4pt)
`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))`, #h(4pt) `R≜cost≤cost°`.

`perm≜bagify bagify°=⦇[nil,add]⦈`, #h(4pt) `add (xs,j)=ys⧺[j]⧺zs` for some `xs=ys⧺zs`.

`k≜[zero,assocr (𝟙×((bagify°×𝟙) penalty)) bmax]`, #h(4pt)
`f≜[zero,(bagify°×𝟙) penalty]`, #h(4pt) `Q≜f≤f°`, #h(4pt) `Q'≜(bagify°×𝟙) penalty≤penalty°(bagify×𝟙)`.
// lean:AOP.A10_3_Tardy.bagify@31766900 lean:AOP.A10_3_Tardy.bagAlg@d0f7446e lean:AOP.A10_3_Tardy.snag@c772c474 lean:AOP.A10_3_Tardy.nilBag@f9126385 lean:AOP.A10_3_Tardy.Bag@257c054f lean:AOP.A10_3_Tardy.bagify_cata@bcacee1a lean:AOP.A10_3_Tardy.penalty@cb396f8a lean:AOP.A10_3_Tardy.cost@a1054f80 lean:AOP.A10_3_Tardy.bmax@fc84cd0a lean:AOP.A10_3_Tardy.R@be4c6db5 lean:AOP.A10_3_Tardy.Q@f060536c lean:AOP.A10_3_Tardy.Q'@ea357147 lean:AOP.A10_3_Tardy.fFn@94a6f009 lean:AOP.A10_3_Tardy.tardy_H@23f37b4f lean:AOP.A10_3_Tardy.nil_ne_snag@77e87166

`g≜[zero,penalty]`, #h(4pt) `m≜[zero,π₁ cost]` (B&dM's `h`, renamed as in @tardy-laws).
// lean:AOP.A10_3_Tardy.g@41729767 lean:AOP.A10_3_Tardy.m@7bff7a03 lean:AOP.A10_3_Tardy.k@daadb101 lean:AOP.A10_3_Tardy.add@a93c9066 lean:AOP.A10_3_Tardy.costR@42c139cf lean:AOP.A10_3_Tardy.penaltyR@89469572 lean:AOP.A10_3_Tardy.bmaxR@c4eeff86 lean:AOP.A10_3_Tardy.R_eq@8f5cc907
]]<tardy-defn>

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
       bag of `xs` — @tardy-defn]),
    // lean:AOP.A10_3_Tardy.penalty_eq_bagPenalty@437884a3
  ),
)]<tardy-cost-k>

// B&dM Exercise 10.5, p.258: "it is easy to check".
#disp[#calc-table(cols: (1fr,), al: (left + top,),
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
#disp[#calc-table(cols: (1fr,), al: (left + top,),
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
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.cost_alg_bmax") \
    #src[the cost of a schedule is the larger of the penalty of its last job and the cost of the
     schedule before it]],
  // lean:AOP.A10_3_Tardy.cost_alg_bmax@6bdd5030
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.cost_alg_bmax.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Tardy.cost_alg_bmax.rhs",
      src[`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))` and `bmax` commutes — @tardy-defn]),
  ),
)]<tardy-cost-bmax>

// B&dM (10.7), p.256, Exercise 10.7; needs `ct` and `wt` positive.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
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
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.bagify_recip_cata") \
    #src[the orderings of a bag with one more job are the orderings of the bag with that job put
     in anywhere]],
  // lean:AOP.A10_3_Tardy.bagify_recip_cata@9781e524
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.bagify_recip_cata.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Tardy.bagify_recip_cata.rhs",
      src[take out the last copy of `j` and put it back — @tardy-defn]),
    // lean:AOP.A10_3_Tardy.add_del@18003f68 lean:AOP.A10_3_Tardy.blist_add@74e74883
  ),
)]<tardy-bag-cata>

// B&dM p.256, "putting (10.7) and (10.8) together".
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.bagify_recip_le") \
    #src[an ordering of a bag with one more job costs at least the cost of the ordering of the
     bag before its last job]],
  // lean:AOP.A10_3_Tardy.bagify_recip_le@583c3c44
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.bagify_recip_cata.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Tardy.bagify_recip_cata.rhs", src[(10.8) — @tardy-bag-cata]),
    (SQ, "Freyd.Alg.RelSet.Tardy.bagify_recip_le_step2.rhs", src[(10.7) — @tardy-add]),
    // lean:AOP.A10_3_Tardy.bagify_recip_le_step2@88a920c7
    (SQ, "Freyd.Alg.RelSet.Tardy.bagify_recip_le_step3.rhs",
      src[definition of `R`, and `nil⊑zero≤cost°`]),
    // lean:AOP.A10_3_Tardy.bagify_recip_le_step3@6d50a490
    (EQ, "Freyd.Alg.RelSet.Tardy.bagify_recip_le_step4.rhs", src[definition of `m`]),
    // lean:AOP.A10_3_Tardy.bagify_recip_le_step4@720cf659
  ),
)]<tardy-bag-le>

// B&dM (10.3), p.257: the book's calculation, one row per hint.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.tardy_greedy") \
    #src[a schedule of a bag ending in a job of least penalty is no worse than any schedule of
     the same bag]],
  // lean:AOP.A10_3_Tardy.tardy_greedy@5953b96f
  lean-chain((
    (none, "Freyd.Alg.RelSet.Tardy.tardy_greedy_step1.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_greedy_step1.rhs", src[monotonicity of composition]),
    // lean:AOP.A10_3_Tardy.tardy_greedy_step1@588b14c9
    (EQ, "Freyd.Alg.RelSet.Tardy.tardy_greedy_step2.rhs",
      src[`β°F(bagify°)α=bagify°`, since `bagify=⦇β⦈`]),
    // lean:AOP.A10_3_Tardy.tardy_greedy_step2@0c67ad67 lean:AOP.A10_3_Tardy.bagify_recip_alg@909c28b3
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_greedy_step3.rhs", src[@tardy-bag-le]),
    // lean:AOP.A10_3_Tardy.tardy_greedy_step3@4c8ea4a0
  ), (
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_greedy_step4.rhs", src[modular law]),
    // lean:AOP.A10_3_Tardy.tardy_greedy_step4@03c0558d
    (EQ, "Freyd.Alg.RelSet.Tardy.tardy_greedy_step5.rhs",
      src[choice of `Q`: `F(bagify) Q F(bagify°)=g≤g°`]),
    // lean:AOP.A10_3_Tardy.tardy_greedy_step5@1f772cd4 lean:AOP.A10_3_Tardy.Q_choice@1881a8ab
    (EQ, "Freyd.Alg.RelSet.Tardy.tardy_greedy_step6.rhs", src[products: `⟨R,S⟩⟨T,U⟩°=RT°∩SU°`]),
    // lean:AOP.A10_3_Tardy.tardy_greedy_step6@19339638
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_greedy.rhs", src[@tardy-tail]),
  )),
)]<tardy-greedy>

// B&dM p.257, "to complete the proof it is sufficient to show", `cost°` shunted.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.tardy_tail") \
    #src[a job whose penalty is at most the last penalty, put after a schedule costing at most
     the cost before the last job, gives a schedule costing at most the whole]],
  // lean:AOP.A10_3_Tardy.tardy_tail@d6af1dd1
  lean-chain((
    (none, "Freyd.Alg.RelSet.Tardy.tardy_tail_step1.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_tail_step1.rhs", src[`cost` a map, so `𝟙⊑cost cost°`]),
    // lean:AOP.A10_3_Tardy.tardy_tail_step1@7ed1c8a6
    (EQ, "Freyd.Alg.RelSet.Tardy.tardy_tail_step2.rhs", src[`α cost=⟨g,α cost⟩ bmax`]),
    // lean:AOP.A10_3_Tardy.tardy_tail_step2@8865bddf lean:AOP.A10_3_Tardy.alg_cost_self@29bcea57
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_tail_step3.rhs", src[`⟨g,α cost⟩` simple]),
    // lean:AOP.A10_3_Tardy.tardy_tail_step3@3427a120
  ), (
    (SQ, "Freyd.Alg.RelSet.Tardy.tardy_tail_step4.rhs", src[monotonicity of `bmax`]),
    // lean:AOP.A10_3_Tardy.tardy_tail_step4@337d771d
    (EQ, "Freyd.Alg.RelSet.Tardy.tardy_tail_step5.rhs", src[(10.4) — @tardy-cost-bmax]),
    // lean:AOP.A10_3_Tardy.tardy_tail_step5@739d1394
    (EQ, "Freyd.Alg.RelSet.Tardy.tardy_tail.rhs", src[definition of `R`]),
  )),
)]<tardy-tail>

// ONE WIRE, `Bag Job` to `[Job]`, one datatype lane carrying `bag` above the bead that eats it and
// `list` below.  The last row has NO `E` wire: `pick` is where the greedy program stops carrying a
// set at all.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tardy.tardy_laws"), #h(6pt) `schedule=(null→nil,pick (schedule×𝟙) snoc)` \
    #src[an ordering of the given bag with least maximum penalty is got by taking a job of least
     penalty out of the bag, putting it last, and scheduling what is left the same way]],
  // lean:AOP.A10_3_Tardy.schedule_le@e2c381dc lean:AOP.A10_3_Tardy.schedule_unfold@d98fd6f6
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tardy.tardy_laws.rhs", src[the specification — @tardy-defn]),
    // job-schedule row: Theorem 10.1
    // `(10.6)`'s arrow is B&dM's `h`, which is @dp-defn's algebra letter; renamed `m` here, since the
    // theorem it feeds and it would otherwise both be `h` in one table.
    (RQ, "Freyd.Alg.RelSet.Tardy.tardy_laws.lhs.body",
      src[No greedy *reduce* exists — one would also
       solve every prefix of the input, and the best schedule of a prefix need not extend to a best
       schedule of the whole]),
    (EQ, "Freyd.Alg.RelSet.Tardy.tardy_branch.lhs",
      src[Proposition 10.1: `nil` and `snag` have disjoint ranges]),
    // lean:AOP.A10_3_Tardy.pick_branch_le@e50eb5ea lean:AOP.A10_3_Tardy.pick_branch_simple@43683444
    // No `E` lane: `pick` does the transpose and the `est` in one function, so nothing is ever a set.
    (RQ, "Freyd.Alg.RelSet.Tardy.pick_branch_le.lhs",
      src[`pick⊑`#frc([`snag°`])` est(Q')`, a partial function, quadratic in the number of jobs]),
  ),
  // lean:AOP.A10_3_Tardy.tardy_laws@706eb827 lean:AOP.A10_3_Tardy.greedy_dp_context@4a318c49 lean:AOP.A10_3_Tardy.tardy_mono@f508140f lean:AOP.A10_3_Tardy.tardy_greedy@5953b96f
)]<tardy-laws>

== The TeX problem

// B&dM §10.4, p. 259.  The book's local `h` for `⦇[arb,step]⦈` is @dp-defn's algebra letter, so it
// is written `H°` here instead.  The base case of `f` is `a<0` on p. 262 and `p≤0` in the program.
#disp[#definition[
`intern≜val round : Decimal⟶[0,2¹⁶)`, #h(4pt) `val≜⦇[zero,shift]⦈`, #h(4pt)
`shift (d,r)=(d+r)/10`, #h(4pt) `round r` rounds `2¹⁶r` to the nearest integer:
`round r=n⟺2n−1<2¹⁷r<2n+1`.

`interval n=((2n−1)/2¹⁷,(2n+1)/2¹⁷)`, #h(4pt) `r inrange (a,b)⟺a<r<b`, #h(4pt)
`round°=interval inrange`, #h(4pt) `R≜length≤length°`.

`Interval` the pairs `(a,b)` with `Legal(a,b)⟺0<b<1` and `a<b` #h(4pt) #src[(10.9); `step_legal` is what types `step`]; #h(4pt)
`[arb,step] : 1+(Digit×Interval)⟶Interval`, #h(4pt)
`step (d,(a,b))=((d+a)/10,(d+b)/10)`.

`FX=1+(Digit×X)`, #h(4pt) `α≜[nil,cons]`, #h(4pt) `H≜⦇[arb,step]⦈°`, #h(4pt)
`! : Digit×Interval⟶1`, #h(4pt) `Q≜(l°!°r) ∪ 𝟙` #h(4pt)
#src[`l`, `r` are @coprod-laws's injections into `FX=1+(Digit×X)`, so `l : 1⟶FX` and
 `r : Digit×X⟶FX`], #h(4pt) `w≜2¹⁷`.
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
]]<tex-defn>

// B&dM pp. 260-261: the fusion condition, the two cases of `[zero,shift]` one row each.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tex.tex_fusion") \
    #src[every interval got by folding a decimal's digits with `[arb,step]` has the decimal's value
     strictly inside it]],
    // lean:AOP.A10_4_Tex.tex_fusion@6c48b5bc
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tex.tex_fusion_step1.lhs",
      src[fusion: it suffices that `[zero,shift] inrange°⊒F(inrange°)[arb,step]`]),
    (EQ, "Freyd.Alg.RelSet.Tex.tex_fusion_step1.rhs",
      src[`[T,U]Z=[TZ,UZ]`, a coproduct law not tabulated in the note]),
     // lean:AOP.A10_4_Tex.tex_fusion_step1@258065cf
    (EQ, "Freyd.Alg.RelSet.Tex.tex_fusion_step2.rhs",
      src[`zero inrange°=arb`: the first condition, which determines `arb`]),
     // lean:AOP.A10_4_Tex.tex_fusion_step2@bc02821b
    (RQ, "Freyd.Alg.RelSet.Tex.tex_fusion_step3.lhs",
      src[arithmetic: `10a−d<r<10b−d ⟹ a<(d+r)/10<b` for `(a,b)=step(d,(10a−d,10b−d))`; only `⊒`,
       since `(10a−d,10b−d)` satisfies (10.9) only when `d<10b<d+1`]),
     // lean:AOP.A10_4_Tex.tex_fusion_step3@15be0440
    (EQ, "Freyd.Alg.RelSet.Tex.tex_fusion_step4.rhs",
      src[`F(S)[T,U]=[T,(𝟙×S)U]` read right to left: definition of `F`]),
     // lean:AOP.A10_4_Tex.tex_fusion_step4@66ce201d
  ),
)]<tex-fusion>

// B&dM p. 262: the greedy condition, the book's hints one row each; `Q` here is the book's `Q°`
// because the chain runs in diagram order.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tex.tex_greedy") \
    #src[choosing by `Q` among the one-step decompositions before building with `F(X)` and `α`
     yields only decimals that are `R`-related to one built without choosing]],
    // lean:AOP.A10_4_Tex.tex_greedy@a8ba8ee9
  lean-chain(
    (
      (none, "Freyd.Alg.RelSet.Tex.tex_greedy_step1.lhs", []),
      (EQ, "Freyd.Alg.RelSet.Tex.tex_greedy_step1.rhs",
        src[definition of `Q`; composition distributes over `∪`]),
       // lean:AOP.A10_4_Tex.tex_greedy_step1@01b945da
      (SQ, "Freyd.Alg.RelSet.Tex.tex_greedy_step2.rhs", src[`R` is reflexive]),
       // lean:AOP.A10_4_Tex.tex_greedy_step2@a4d7ae25
      (SQ, "Freyd.Alg.RelSet.Tex.tex_greedy_step3.rhs",
        src[`r F(X) α⊑! l α R`: `l α=nil`, and `length(nil)=0` is at most any length]),
       // lean:AOP.A10_4_Tex.tex_greedy_step3@178d1ae7
    ),
    (
      (SQ, "Freyd.Alg.RelSet.Tex.tex_greedy_step4.rhs",
        src[`!°!⊑𝟙` on `𝟏`: universal property of `!`]),
       // lean:AOP.A10_4_Tex.tex_greedy_step4@c1f18bc7
      (EQ, "Freyd.Alg.RelSet.Tex.tex_greedy_step5.rhs",
        src[`l F(X)=l`: definition of `F`]),
       // lean:AOP.A10_4_Tex.tex_greedy_step5@f5a296e0
      (SQ, "Freyd.Alg.RelSet.Tex.tex_greedy_step6.rhs", src[`l` is simple: `l°l⊑𝟙`]),
       // lean:AOP.A10_4_Tex.tex_greedy_step6@d0746bbf
      (EQ, "Freyd.Alg.RelSet.Tex.tex_greedy_step7.rhs", src[`∪` is idempotent]),
       // lean:AOP.A10_4_Tex.tex_greedy_step7@a3c2f19f
    ),
  ),
)]<tex-greedy>

// ONE WIRE, `[0,2¹⁶)` to `Decimal`, in every row: `interval`, `H` and `[arb,step]°` are relations
// between objects with no functor of their own, so the picture never needs to open `Decimal`'s own
// `list`.  `interval` sits ABOVE the singleton in every row from the second on: it is the map
// pulled out of the transpose, and holding it at one height is what says the rest of the chain
// moved past it.

#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Tex.tex_laws"), #h(6pt) `extern(n)=f(2n−1,2n+1)` \
    #src[a shortest decimal whose internal representation is the given multiple of `2⁻¹⁶` is got by
     emitting the one digit the interval of admissible reals allows, until that interval contains
     zero and the empty decimal will do]],
  lean-chain(
    (none, "Freyd.Alg.RelSet.Tex.tex_laws_step1.lhs", src[the specification — @tex-defn]),
    // `interval` is an arrow between two objects that carry no functor, so it is a bare bead above
    // the unit: the set the transpose opens starts on its target.
    (EQ, "Freyd.Alg.RelSet.Tex.tex_laws_step1.rhs",
      src[`round°` is not a map, but `interval` is, so it comes out of the transpose]),
    (RQ, "Freyd.Alg.RelSet.Tex.tex_laws_step2.lhs",
      src[the type restriction (10.9): a shortest decimal `H` gives an interval is a shortest one
       among all decimals inside it, and is inside it by @tex-fusion]),
    // interval row: Theorem 10.1
    // `est(Q) : E(F(Interval))⟶F(Interval)` kills the set but not the `F` under it, so its wire ends
    // on the `E` lane; `F(H)α` closes `F` and is where the digits' `list` is born (`H` recurses,
    // `α≜[nil,cons]` — @tex-defn — builds the list).
    (RQ, "Freyd.Alg.RelSet.Tex.tex_laws_body.lhs",
      src[#frc([`[arb,step]°`]) returns at most two elements — stop, or take one more
       digit — and `! nil⊑cons R°` makes it stop whenever stopping is legal]),
  ),
  // lean:AOP.A10_4_Tex.tex_laws@393983dc lean:AOP.A10_4_Tex.tex_laws_step1@ddde5bc4 lean:AOP.A10_4_Tex.tex_laws_step2@3fd53250 lean:AOP.A10_4_Tex.tex_laws_step3@12f54b12 lean:AOP.A10_4_Tex.tex_laws_body@942aced5
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
    // lean:AOP.A10_4_Tex.tex_f@059727cf
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
