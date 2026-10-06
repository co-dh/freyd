#import "../note-prelude.typ": *
#show: note-chapter.with(8)
// note-split: chapter 8 — this header is written by scripts/note-split and stripped by scripts/note-join
= Thinning Algorithms <sec-thin>


// ---- HINZE–MARSDEN.  A WIRE IS A FUNCTOR: `[A]` is the `list` wire beside the `A` wire, at the
// ENDS as much as in the middle, and `E` is born by the unit `𝟙%∋` — a bead with a free upper end.
// A counit may only land on the object wire when nothing is left outside it; where a datatype
// survives (`est(R) : P(LA)⟶LA`) the wire ends on its own lane, since bending in would CROSS it.
// A bead sits on the wire it CHANGES: a functor wire when it only rearranges that functor, the
// object wire when it changes the value.  Lane labels run west, object-wire labels east.
#let THU = 1.90                                   // the set the transpose opens, outside everything
#let THM = 2.65                                   // the datatype under it
#let THN = 3.40                                   // a second one, inside the first
#let THO = 5.40                                   // the object wire
== Thinning

// B&dM §8.1, p. 193.  Between the two extremes of the last section: `𝟙` keeps every partial solution
// and `est(Q) (𝟙%∋)` keeps one, `thin(Q)` keeps a representative collection.
#disp(num: "(8.1)")[#definition[
#leanf("Freyd.Alg.thinRel") #h(4pt) — `thin(Q)` takes a set `ys` to a subset `xs` that keeps a `Q`-lower bound of every `a∈ys`.

`thin(≤)` #h(4pt) `ys thin(≤) xs⟺xs⊆ys∧(∀a∈ys. ∃b∈xs. b≤a)`.
]]<thin-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [#leanf("Freyd.Alg.le_Λ_comp_thinRel_iff")],
  [`S` is the whole algebra: it produces every candidate that `thin(Q)` thins. Everything kept is an `S`-value, and every `S`-value has a `Q`-lower bound among the kept ones],
  [#leanf("Freyd.Alg.thinRel_comp_eps_le")],
  [everything a thinning keeps was in the set],
   // lean:AOP.A8_1.thinRel_comp_eps_le@17481c78
  [#leanf("Freyd.Alg.recip_thinRel_comp_eps_le")],
  [every element of the set has a `Q`-lower bound among the kept ones],
   // lean:AOP.A8_1.recip_thinRel_comp_eps_le@4c5767f4
  [#leanf("Freyd.Alg.thinRel_mono")],
  [the fewer pairs `Q` relates, the fewer subsets count as thinnings],
  [#leanf("Freyd.Alg.id_le_thinRel") \ #leanf("Freyd.Alg.thinRel_trans")],
   // lean:AOP.A8_1.id_le_thinRel@8ec713e9
   // lean:AOP.A8_1.thinRel_trans@84a7d558
  [keeping everything is always a legal thinning],
  [#leanf("Freyd.Alg.thinRel_comp_est") #h(4pt) #src[@thin-intro]],
  [*thin-introduction*: thinning first cannot lose an `R`-minimum],
   // lean:AOP.A8_1.thinRel_comp_est@eafff35f
  [`thin(Q)⊒est(Q)` $frac(#[`𝟙`], ∋)$ #h(6pt)
 #src[(8.2) — @thin-82]],
   // lean:AOP.A8_1.est_comp_singletonMap_le_thinRel@8aad298c
  [*thin-elimination*: keeping one element is a thinning, but its domain is the sets `est(Q)` is
   defined on],
  [$frac(#[`S`], ∋)$ `thin(Q)⊒` $frac(#[`S`], ∋)$ `est(R)` $frac(#[`𝟙`], ∋)$ \
   #src[(8.3), `R∩(S°S)⊑Q` — @thin-83]],
  [the usable variant: `R` need only refine `Q` between values `S` gives one argument],
  [#leanf("Freyd.Alg.powerRel_thinRel_comp_bigUnion_le") #h(6pt) #src[(8.4) — @thin-84]],
  [thinning each member set is a thinning of the union],
)]<thin-laws>

=== #leanf("Freyd.Alg.le_Λ_comp_thinRel_iff") — the definition of $frac(#[`S`], ∋)$ `thin(Q)`

// @thin-laws' first row drawn: the `E` lane is born at the singleton and dies at the `∋`, so the
// left panel's `X` lands on it and each condition on the right is one panel.
#disp[
#grid(columns: 5, align: horizon, column-gutter: 4pt,
row((
  lean("Freyd.Alg.le_Λ_comp_thinRel_iff.lhs"),
), s: 96%),
[⟺],
row((
  lean("Freyd.Alg.le_Λ_comp_thinRel_iff.rhs.lhs", "Freyd.Alg.le_Λ_comp_thinRel_iff.rhs.rhs", op: [and]),
), s: 96%),
)
]<thin-up>

#disp[
   // lean:AOP.A4_6.Λ_eps_reflection@eb919721
#grid(columns: 3, align: horizon, column-gutter: 4pt,
  lean("Freyd.Alg.thinRel_comp_eps_le"), [and], lean("Freyd.Alg.recip_thinRel_comp_eps_le"),
)
#src[@thin-up at `X≜thin(Q)`, `S≜∋`: the left side is `thin(Q)⊑thin(Q)`, since $frac(#[`∋`], ∋)$`=Λ(∋)=𝟙`]
]<thin-up-eps>

=== #leanf("Freyd.Alg.thinRel_comp_est") — thinning first, then taking the smallest, is the same as taking the smallest

// B&dM p. 194, thin-introduction, mirrored: the row above read as a calculation.
#import "../generated/Freyd.Alg.thinRel_comp_est_cond1.calc.typ" as calc-up1
#grid(columns: (1fr, 1fr), column-gutter: 42pt, align: top,
[#disp[
   // lean:AOP.A8_1.thinRel_comp_est@eafff35f
#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinRel_comp_est_step1") \
    #src[the `⊑` half: keeping everything is a thinning — `𝟙⊑Q`]],
     // lean:AOP.A8_1.thinRel_comp_est_step1@65f6cc95
  lean-chain(
    (none, "Freyd.Alg.thinRel_comp_est_step1.lhs", []),
    (SQ, "Freyd.Alg.thinRel_comp_est_step1.rhs", src[`𝟙⊑thin(Q)` — @Freyd.Alg.id_le_thinRel]),
  ),
)
]<thin-intro>],
[#disp[
#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinRel_comp_est_cond1") \
    #src[the `⊒` half, first condition of the UP of `est` at `X≜thin(Q) est(R)` — @est-up]],
     // lean:AOP.A8_1.thinRel_comp_est_cond1@2c9241e0
  lean-calc(calc-up1),
)
]<thin-intro-up1>])

#import "../generated/Freyd.Alg.thinRel_comp_est_cond2.calc.typ" as calc-up2
#disp[
#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinRel_comp_est_cond2") \
    #src[the `⊒` half, second condition]],
     // lean:AOP.A8_1.thinRel_comp_est_cond2@1bf58dd7
  lean-calc(calc-up2),
)]<thin-intro-up2>

#import "../generated/Freyd.Alg.est_comp_singletonMap_cond1.calc.typ" as calc-82a
#import "../generated/Freyd.Alg.est_comp_singletonMap_cond2.calc.typ" as calc-82b
#import "../generated/Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1.calc.typ" as calc-83a
#import "../generated/Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2.calc.typ" as calc-83b
#import "../generated/Freyd.Alg.thinning_fusion.calc.typ" as calc-81a
#import "../generated/Freyd.Alg.thinning_prefixed.calc.typ" as calc-81
#import "../generated/Freyd.Alg.RelSet.ListRel.Fmap_sort_comp_listcp_list_filter_le.calc.typ" as calc-l81
=== Properties of thinning
// B&dM (8.2), p. 194, mirrored.  `thin` is a meet of two divisions, so the law is its two halves:
// the first cancels the singleton against the `∋`, the second is the chain.
#disp(num: "(8.2)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.est_comp_singletonMap_le_thinRel") \
    #src[the singleton holding a `Q`-least member of a set is a thinning of that set
     // thin-elimination row: (8.2), p. 194
 #h(4pt) ]],
     // lean:AOP.A8_1.est_comp_singletonMap_le_thinRel@8aad298c
  Thm(cols: 1)[#leanf("Freyd.Alg.est_comp_singletonMap_cond1") \
    #src[every member of the singleton is a member of the set — @thin-defn, `∋/∋` half]],
     // lean:AOP.A8_1.est_comp_singletonMap_cond1@14824541
  lean-calc(calc-82a),
  Thm(cols: 1)[#leanf("Freyd.Alg.est_comp_singletonMap_cond2") \
    #src[the singleton's member stands in `Q` to every member of the set — @thin-defn, `∈\(Q°∈)` half]],
     // lean:AOP.A8_1.est_comp_singletonMap_cond2@9dbd159d
  lean-calc(calc-82b),
)]<thin-82>

// B&dM (8.3), p. 194, mirrored.  The first of the two conditions cancels the singleton against `∋`;
// the second is the chain, and the context row is where the side condition enters.
#disp(num: "(8.3)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.Λ_comp_est_comp_singletonMap_le_thinRel")
    // thinning row: (8.3), p. 194
    ],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_le_thinRel@d66c2a44
  Thm(cols: 1)[#leanf("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1") \
    #src[every member of the singleton is a value `S` returns — @thin-laws:1, first condition]],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond1@58772169
  lean-calc(calc-83a),
  Thm(cols: 1)[#leanf("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2") \
    #src[the singleton's member stands in `Q` to every value `S` returns at the same argument —
     @thin-laws:1, second condition]],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond2@aa38c1af
  lean-calc(calc-83b),
)]<thin-83>

// B&dM Theorem 8.1, p. 195, mirrored.  The proof is about the SECOND half of `thin`'s universal
// property: the first half is fusion, and the hylomorphism theorem turns the second into one chain.
// `thin(Q) : PA⟶PA` is fixed by one `Q`, not natural in `A`: an arrow of the object `PA`, so its bead
// touches both wires — the `E` it receives dies at it and the `E` it returns is born there.
#disp(num: "Theorem 8.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning") \
    #src[thinning at every step of the reduce is a thinning of the whole candidate set]
     // thinning-of-reduce row: Theorem 8.1, p. 195
  ],
     // lean:AOP.A8_1.thinning@6d6c6473
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning_cond1") \
    #src[everything the thinning fold keeps is a value of the plain fold — @thin-laws:1, first
     condition, by @cata-fusion from the chain below]],
     // lean:AOP.A8_1.thinning_cond1@daa38052
  lean-calc(calc-81a),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning_cond2") \
    #src[every value of the plain fold is `Q`-above one the thinning fold keeps — @thin-laws:1,
     second condition, by @hylo-mu from the chain below]],
     // lean:AOP.A8_1.thinning_cond2@6a7d582f
  lean-calc(calc-81),
)]<thin-thm81>

// The prefixed-point inequality of the chain above, one factor per row.  Step and type cells are
// read off `thinning_prefixed`'s sides by `.lhs.f<k>`; the example runs at `F(X)=V+V×X`.
#disp[#table(
  columns: (auto, auto, 1fr, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*step*], [*type*], [*example*], [*what it does*]),
  table.cell(colspan: 4)[`S:F(A)⟶A` is 8.1's algebra; example `F(X)=V+V×X`, `S=[wrap,cons]`,
   candidate `a=cons(v,p)`],

  [#leann("Freyd.Alg.thinning_prefixed.lhs.f1")], [#leant("Freyd.Alg.thinning_prefixed.lhs.f1")],
  [`cons(v,p) ↦ r(v,p)`],
  [takes `a` apart into the input of its last step],
  [#leann("Freyd.Alg.thinning_prefixed.lhs.f2")], [#leant("Freyd.Alg.thinning_prefixed.lhs.f2")],
  [`r(v,p) ↦ r(v,ps)`, some `p'∈ps` with `p' Q p`],
  [replaces each recursive component by a set holding a `Q`-no-worse one; `v` stays],
  [#leann("Freyd.Alg.thinning_prefixed.lhs.f3")], [#leant("Freyd.Alg.thinning_prefixed.lhs.f3")],
  [`r(v,ps) ↦ {cons(v,t) ∣ t∈ps}`],
  [picks one element from each set, combines by `S`, collects every result],
  [#leann("Freyd.Alg.thinning_prefixed.lhs.f4")], [#leant("Freyd.Alg.thinning_prefixed.lhs.f4")],
  [`{cons(v,t) ∣ t∈ps} ↦ ys`],
  [keeps a subset; every dropped element is `Q`-beaten by a kept one],
  [#SQ #leann("Freyd.Alg.thinning_prefixed.rhs")], [#leant("Freyd.Alg.thinning_prefixed.rhs")],
  [`ys` holds `y` with `y Q cons(v,p') Q cons(v,p) = a`],
  [the thinned set still holds an element `Q`-no-worse than `a` (`S` monotonic on `Q`, `Q`
   transitive)],
  // lean:AOP.A8_1.thinning_prefixed@3d1dc0a4
)]<thin-thm81-steps>

// B&dM Corollary 8.1, p. 195: the thinning theorem read against the optimisation problem itself.
// `⦇−⦈` and not the algebra: its transpose opens an `E` INSIDE the reduce, which no outer panel has.
#import "../generated/Freyd.Alg.thinning_est.calc.typ" as calc-cor
#disp(num: "Corollary 8.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning_est") \
    #src[the thinning fold refines the optimisation problem itself]
     // thinning-est row: Corollary 8.1
  ],
     // lean:AOP.A8_1.thinning_est@6aa3a7c1
  // The reduce CONSUMES `T` and the transpose inside it BIRTHS `E`, so the two wires meet at one bead.
  lean-calc(calc-cor),
)]<thin-cor>

// B&dM (8.4), p. 195, mirrored.  `union` is `Λ(∋∋)`, so @thin-up at `S≜∋∋` splits the law into its
// two conditions, each a chain.
#import "../generated/Freyd.Alg.powerRel_thinRel_comp_bigUnion_cond1.calc.typ" as calc-84a
#import "../generated/Freyd.Alg.powerRel_thinRel_comp_bigUnion_cond2.calc.typ" as calc-84b
#disp(num: "(8.4)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.powerRel_thinRel_comp_bigUnion_le") \
    #src[thinning each member set, then taking the union, is a thinning of the union]],
     // lean:AOP.A8_1.powerRel_thinRel_comp_bigUnion_le@7b334e71
  Thm(cols: 1)[#leanf("Freyd.Alg.powerRel_thinRel_comp_bigUnion_cond1") \
    #src[every member of the result is a member of a member set — @thin-laws:1, first condition]],
     // lean:AOP.A8_1.powerRel_thinRel_comp_bigUnion_cond1@3774ee8b
  lean-calc(calc-84a),
  Thm(cols: 1)[#leanf("Freyd.Alg.powerRel_thinRel_comp_bigUnion_cond2") \
    #src[every member of a member set has a `Q`-lower bound in the result — @thin-laws:1, second
     condition]],
     // lean:AOP.A8_1.powerRel_thinRel_comp_bigUnion_cond2@144e72b2
  lean-calc(calc-84b),
)]<thin-84>

== Paths in a layered network

// B&dM §8.2, p. 196.  `Q` has to record `head` because `wt (a, head xs)` is unbounded: a dearer path
// with a nearer first vertex can still win.
#disp[#deftab(

  [#rowkey("Freyd.Alg.pathF")], [#leant("Freyd.Alg.pathF")],
  [#leanf("Freyd.Alg.pathF_obj")],
  [a path is either one vertex a, or a vertex a followed by a path xs],
  [#rowkey("Freyd.Alg.alphaR_pathF")], [#leant("Freyd.Alg.alphaR_pathF")],
  [#leanf("Freyd.Alg.alphaR_pathF")],
  [build a path: wrap one vertex as [a], or put a in front of xs],
  [#rowkey("Freyd.Alg.wrapz")], [#leant("Freyd.Alg.wrapz")],
  [#leanf("Freyd.Alg.wrapz")],
  [a path of one vertex, no edge, cost 0],
  [#rowkey("Freyd.Alg.consw")], [#leant("Freyd.Alg.consw")],
  [#leanf("Freyd.Alg.consw_apply.mapsto")],
  [put a in front of the path; the cost adds the weight of the new edge a→head(xs)],
  [#rowkey("Freyd.Alg.pathCost")], [#leant("Freyd.Alg.pathCost")],
  [#leanf("Freyd.Alg.pathCost")],
  [the cost of [a₀,…,aₙ] is wt(a₀,a₁)+…+wt(aₙ₋₁,aₙ)],
  [#rowkey("Freyd.Alg.pathR")], [#leant("Freyd.Alg.pathR")],
  [#leanf("Freyd.Alg.pathR")],
  [xs is cheaper than ys],
  [#rowkey("Freyd.Alg.RelSet.ListRel.nelist")], [#leant("Freyd.Alg.RelSet.ListRel.nelist")],
  [#leanf("Freyd.Alg.relCata_pathF_eps_eq_nelist")],
  [L(∋) relates a list of layers to every path that chooses one vertex from each layer],
  [#rowkey("Freyd.Alg.minpath")], [#leant("Freyd.Alg.minpath")],
  [#leanf("Freyd.Alg.minpath_spec")],
  [the input [x₀,…,xₙ] : L(PA) is a list of layers, each a set of vertices; a path chooses one vertex from each layer, and minpath returns a cheapest one],
  [#rowkey("Freyd.Alg.pathQ")], [#leant("Freyd.Alg.pathQ")],
  [#leanf("Freyd.Alg.pathQ")],
  [like R, and the two paths also start at the same vertex: head(xs) = head(ys)],
  [#rowkey("Freyd.Alg.sumCop_u₁_eq")], [#leant("Freyd.Alg.sumCop_u₁_eq")],
  [#leanf("Freyd.Alg.sumCop_u₁_apply.mapsto")],
  [mark a value as the left alternative],
  [#rowkey("Freyd.Alg.sumCop_u₂_eq")], [#leant("Freyd.Alg.sumCop_u₂_eq")],
  [#leanf("Freyd.Alg.sumCop_u₂_apply.mapsto")],
  [mark a value as the right alternative],
  [#rowkey("Freyd.Alg.cplMap")], [#leant("Freyd.Alg.cplMap")],
  [#leanf("Freyd.Alg.cplMap")],
  [pair every element of the set with the value beside it],
  [#rowkey("Freyd.Alg.cprMap")], [#leant("Freyd.Alg.cprMap")],
  [#leanf("Freyd.Alg.cprMap")],
  [pair the value beside the set with every element of the set],
  [#rowkey("Freyd.Alg.Λ_pathF_map_eps_id")], [#leant("Freyd.Alg.Λ_pathF_map_eps_id")],
  [#leanf("Freyd.Alg.Λ_pathF_map_eps_id")],
  [cpl transpose: from layer x and a set of paths ps, choose a vertex a ∈ x],
  [#rowkey("Freyd.Alg.Λ_pathF_map_id_eps")], [#leant("Freyd.Alg.Λ_pathF_map_id_eps")],
  [#leanf("Freyd.Alg.Λ_pathF_map_id_eps")],
  [cpr transpose: from a vertex a and a set of paths ps, choose a tail xs ∈ ps],
  [#rowkey("Freyd.Alg.pathStep")], [#leant("Freyd.Alg.pathStep")],
  [#leanf("Freyd.Alg.pathStep")],
  [put a in front of every path in ps and keep a cheapest one],
// lean:AOP.A8_2_Exec.pathF_obj@55c448b1
// lean:AOP.A8_2.pathF@2dcf37fa
// lean:AOP.A8_2_Exec.alphaR_pathF@6536d8fa
// lean:AOP.A8_2.wrapz@e528d496
// lean:AOP.A8_2.wrapz_apply@e7256951
// lean:AOP.A8_2.consw@53d456cc
// lean:AOP.A8_2.consw_apply@e512412c
// lean:AOP.A8_2.pathCost@2d18e3c4
// lean:AOP.A8_2.costOf@dfe994f6
// lean:AOP.A8_2.pathR@6d0be9c8
// lean:AOP.A8_2_Exec.relCata_pathF_eps_eq_nelist@c0422a4d
// lean:AOP.A8_2_Exec.minpath_spec@15aa3287
// lean:AOP.A8_2_Exec.minpath@6e6b277d
// lean:AOP.A5_6_ListCombinators.RelSet.ListRel.nelist@8f93f06d
// lean:AOP.A8_2.sumCop_u₁_eq@77ceb1de
// lean:AOP.A8_2.sumCop_u₂_eq@345d6352
// lean:AOP.A8_2.sumCop_u₁_apply@950600cc
// lean:AOP.A8_2.sumCop_u₂_apply@774edfff
// lean:AOP.A5_6.cplMap@a82b3919
// lean:AOP.A5_6.cprMap@379d6c37
// lean:AOP.A8_2.pathQ@9626226f
// lean:AOP.A8_2.head@32b2507f
// lean:AOP.A8_2.pathStep@f546a21f
// lean:AOP.A8_2.Λ_pathF_map_eps_id@59cd9f69
// lean:AOP.A8_2.Λ_pathF_map_id_eps@b7473cec
)]<path-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`F(∋,Q)α⊑F(∋,𝟙)αQ`],
  [`F(∋,𝟙)α` is monotonic on `Q`; on `R` it is not, since the next edge can cost arbitrarily much],
  [`S head⊑[𝟙,π₁]` #h(4pt) #src[`S≜F(𝟙,∋)α`]],
  [`S head` is simple, which gives `R∩(S°S)⊑Q`: between two paths `S` builds from one argument,
   equal cost and equal head already means `Q`],
  // lean:AOP.A8_2.pathAlg_monotonic@98a6ae56 lean:AOP.A8_2.pathSplit_comp_headRel_le@1e7c3c78 lean:AOP.A8_2.pathR_inter_recip_le_pathQ@2e1f5c5d
)]<path-mono>

=== Derivation
// B&dM §8.2, p. 198.  The `E` the transpose opens is born OUTSIDE the reduce in the specification
// and INSIDE it from the thinning theorem on; that is what rows 1 and 2 differ by.
// TWO `E` wires, and that is the content: the one the source carries inside `L` (top port), and the
// one the transpose opens outside it — by the unit `𝟙%∋` above the reduce, or by the reduce itself.
#import "../generated/Freyd.Alg.thinning_paths.calc.typ" as calc-82c
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning_paths") \
    // layered-network row: B&dM §8.2, p. 198
    #src[a least-cost path in a layered network, as a fold over the layers]],
     // lean:AOP.A8_2_Exec.thinning_paths@a206827d
  [- Why it is needed: `est(R)` keeps one cheapest `w` of the set `Λ(S)(x)`; `thin(Q)` needs every
     dropped `z` to be `Q`-beaten by a kept one. For `{w}` alone to be a thinning we need `w Q z` for
     every `z` in `Λ(S)(x)`.
   - We have `w R z` (`w` is cheapest) and `w (S°S) z` (both are built by `S` from the same argument
     `x`); the hypothesis turns the two into `w Q z`: among candidates from one argument, cheaper
     already means `Q`-better.],
  lean-calc(calc-82c),
)]<path-laws>

#import "../generated/Freyd.Alg.thinning_paths_alg.calc.typ" as calc-82d
// B&dM §8.2, p. 198, one row per printed line.  Every step rewrites the ALGEBRA, so the chain is stated
// about the algebra alone: no `⦇ ⦈` around it and no `est(R)` behind it.
// q in row (a): x is the vertex list, y the path list; a path is a list of vertices, head first, so `x,p` is cons.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.algSplit"), #h(4pt) #leanf("Freyd.Alg.thinning_paths_alg") \
    // algebra row: B&dM §8.2, p. 198
    #src[thinning the algebra of a layered network costs no more than taking the program's two cases]],
     // lean:AOP.A8_2.thinning_paths_alg@b81f936d
  lean-calc(calc-82d),
  [#EQ #leanf("Freyd.Alg.cpMap_comp_powerRel_alphaR_comp_est_eq_junc") \ #src[at the layered network (`F(A,X)=A+A×X`, `B` the paths `V⁺`, `α=[wrap,cons]`): #frc([`F(𝟙,∋)`])` P(α) est(R)=[wrap,step]` — @Freyd.Alg.pathStep]],
    // lean:AOP.A8_2.cpMap_comp_powerRel_alphaR_comp_est_eq_junc@7d981497
    // lean:AOP.A8_2.pathStep@f546a21f
  // No panel: `cpMap_sum_eq_junc` holds for EVERY pair of relators, and the exporter has no
  // naturality verdict for an `F` that is only a variable — it draws a red stub instead.
  [#EQ #src[#frc([`F(∋,𝟙)`])` =𝟙+cpl` — @Freyd.Alg.Λ_pathF_map_eps_id]],
      // lean:AOP.A5_6.cpMap_sum_eq_junc@01828e3f
)]<path-alg>
// What `F(R,S)` does at 8.2d's `F(A,X)=A+A×X`: each part moves by its own relation, the summand stays.
#disp[
  ```
  F(A,X)   =  A   +   A  ×  X
              │       │     │
              R       R     S
              ↓       ↓     ↓
  F(A',X') =  A'  +   A' ×  X'
  ```
]
// lean:AOP.A8_2.pathF@2dcf37fa
`u F(R,S) v` holds iff one of:
- `u`, `v` are both `inl` and `d R d'`: the leaf moves by `R`;
- `u`, `v` are both `inr` and `p₁ R q₁ ∧ p₂ S q₂`: the vertex moves by `R`, the rest by `S`.
- An `inl` never relates to an `inr`: `R+S≜[R inl, S inr]` returns to the summand it came from, and `F(𝟙)=𝟙` allows no crossing.
- `F(∋,∋)` relates `inr({a,b},{p,q})` to `inr(a,p)`, `inr(a,q)`, `inr(b,p)`, `inr(b,q)`, and `inl({a,b})` to `inl(a)`, `inl(b)`.

== Implementing thin

// B&dM §8.3, p. 199.  Lemma 8.1 is printed with `R` where its own proof and Theorem 8.2 write `P`;
// it is one connected preorder, spelled `≼` here.  `≼` is a connected preorder throughout.
#disp[#deftab(

  [#rowkey("Freyd.Alg.RelSet.ListRel.setify")], [#leant("Freyd.Alg.RelSet.ListRel.setify")],
  [#leanf("Freyd.Alg.RelSet.ListRel.setify_ni_iff")],
  [the set of a list's elements],
  [#rowkey("Freyd.Alg.cup")], [#leant("Freyd.Alg.cup")],
  [#leanf("Freyd.Alg.cup")],
  [the union of two sets],
  [#rowkey("Freyd.Alg.cpMap")], [#leant("Freyd.Alg.cpMap")],
  [#leanf("Freyd.Alg.cpMap")],
  [every `F`-shaped value whose parts are chosen from the given sets],
  [#rowkey("Freyd.Alg.RelSet.Poly.listcp")], [#leant("Freyd.Alg.RelSet.Poly.listcp")],
  [#leanf("Freyd.Alg.RelSet.Poly.listcpFn")],
  [by the shape of `F`: a constant or `arg₁` is a one-element list, `arg₂` the list itself, a sum
   lists its summand, a product pairs every element of one list with every element of the other],
  [#rowkey("Freyd.Alg.RelSet.Poly.linear")], [#leant("Freyd.Alg.RelSet.Poly.linear")],
  [#leanf("Freyd.Alg.RelSet.Poly.linear")],
  [no product in `F` has the argument on both sides],
  [#rowkey("Freyd.Alg.sortRel")], [#leant("Freyd.Alg.sortRel")],
  [#leanf("Freyd.Alg.sortRel")],
  [read a set back as one of its `≼`-ordered listings],
  [#rowkey("Freyd.Alg.RelSet.CL.bumpRel")], [#leant("Freyd.Alg.RelSet.CL.bumpRel")],
  [#leanf("Freyd.Alg.RelSet.CL.bumpRel_wrap.mapsto"), #leanf("Freyd.Alg.RelSet.CL.bumpRel_cons")],
  [put `a` in front of a thinned list, dropping whichever of `a` and the old head the other beats],
  [#rowkey("Freyd.Alg.RelSet.ListRel.thinlist")], [#leant("Freyd.Alg.RelSet.ListRel.thinlist")],
  [#leanf("Freyd.Alg.RelSet.ListRel.thinlist")],
  [only drop elements, and on the set of the elements be a thinning by `Q`],
  [], [],
  [#leanf("Freyd.Alg.RelSet.ListRel.le_thinlist_iff")],
  [what a list implementation of `thin(Q)` must do: only drop elements, and thin the set],
  [], [],
  [#leanf("Freyd.Alg.RelSet.ListRel.bumpFold_le_thinlist")],
  [an implementation: thin a list in one pass, bumping each element into the thinned rest],
  [#rowkey("Freyd.Alg.RelSet.CL.minlist")], [#leant("Freyd.Alg.RelSet.CL.minlist")],
  [#leanf("Freyd.Alg.RelSet.CL.minlist")],
  [a `Q`-least element of the list],
// lean:AOP.A5_6_ListCombinators.RelSet.ListRel.setify@c31d6e6f
// lean:AOP.A5_6_ListCombinators.RelSet.ListRel.setify_ni_iff@fefd0da3
// lean:AOP.A5_6.cup@38377606
// lean:AOP.A5_6.cpMap@636ea157
// lean:AOP.A8_3.sortRel@0e1a3dba
// lean:AOP.A8_3.RelSet.CL.bumpRel@415b7c12
// lean:AOP.A8_3.RelSet.CL.bumpRel_wrap@993629d2
// lean:AOP.A8_3.RelSet.CL.bumpRel_cons@a12aeb2f
// lean:AOP.A8_3.RelSet.ListRel.thinlist@91e5cf00
// lean:AOP.A8_3.RelSet.ListRel.le_thinlist_iff@a16f1cea
// lean:AOP.A8_3.RelSet.ListRel.bumpFold_le_thinlist@a3505422
// lean:AOP.A8_3.RelSet.CL.minlist@7684e8d6
)]<thinlist-defn>

// B&dM's paragraph title "Sorting sets", p. 200: `sort(≼)`, its laws (8.6)–(8.11) and Lemma 8.1.
=== Sorting sets

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [#leanf("Freyd.Alg.RelSet.CL.bumpFold_eq_singleton_minlist") #h(6pt) #src[(8.5)]],
  [what thinning should come to when it can: one element],
  [#leanf("Freyd.Alg.RelSet.ListRel.sort_comp_thinlist_le") #h(6pt) #src[(8.6) — @thinlist-86]],
  [the thinning may run after the sort],
  [#leanf("Freyd.Alg.RelSet.ListRel.sort_comp_minlist_le") #h(6pt) #src[(8.7)]],
  [a minimum of the sorted list is a minimum of the set],
  [#leanf("Freyd.Alg.RelSet.ListRel.sort_comp_list_le") #h(6pt) #src[(8.8)]],
  [shunt a function through a sort],
  [#leanf("Freyd.Alg.RelSet.ListRel.sort_comp_filter_le") #h(6pt) #src[(8.9)] \
   #leanf("Freyd.Alg.RelSet.ListRel.sort_comp_filter_le#p")],
  [filtering a sorted list sorts the restricted set],
  [#leanf("Freyd.Alg.RelSet.ListRel.prodMap_sort_comp_merge_le") #h(6pt) #src[(8.10)]],
  [merging two sorted lists sorts their union],
  [#leanf("Freyd.Alg.RelSet.ListRel.Fmap_sort_comp_listcp_le") \ #src[(8.11), `FX=L+E×X`]],
  [`listcp` is the list implementation of the cartesian product `cp(F)`],
  [#leanf("Freyd.Alg.RelSet.Poly.Fmap_sort_comp_listcp_le") \ #src[(8.11), `F` polynomial and linear]],
  [the same for every linear polynomial `F`],
  // lean:AOP.A8_3.RelSet.CL.bumpFold_eq_singleton_minlist@05ff3ba8 lean:AOP.A8_3.RelSet.ListRel.sort_comp_thinlist_le@12d9be58 lean:AOP.A8_3.RelSet.ListRel.sort_comp_minlist_le@f29a7afa lean:AOP.A8_3.RelSet.ListRel.sort_comp_list_le@e2552a3c lean:AOP.A8_3.sortRel_comp_filter_le@a19a57e0 lean:AOP.A8_3.RelSet.ListRel.prodMap_sort_comp_merge_le@c2de68cc lean:AOP.A8_3.RelSet.ListRel.prodMap_setify_recip_comp_merge_le@e29a3c9c lean:AOP.A8_3.map_sortRel_comp_listcp_le@7c091df5 lean:AOP.A8_3.ordered_comp_subseq_le@3d670f97 lean:AOP.A8_3.prodMap_ordered_comp_merge_le@9cd186c6 lean:AOP.A8_3.RelSet.ListRel.sort_comp_filter_le@293fdf1e lean:AOP.A8_3.RelSet.ListRel.Fmap_sort_comp_listcp_le@388575e2
)]<thinlist-laws>

// B&dM (8.6), p. 201, mirrored.  Row 3 is the content: `thinlist(Q)` only drops elements, and a
// subsequence of a `≼`-ordered list is `≼`-ordered, so the thinning may run before the sort.
// `setify°` is where the set becomes a list, so it is a NODE on the object wire — the `E` bends in,
// the `list` bends out — and the two coreflexive-shaped arrows are beads on the lane each acts on.
#import "../generated/Freyd.Alg.RelSet.ListRel.sort_comp_thinlist_le.calc.typ" as calc-86
#disp(num: "(8.6)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.ListRel.sort_comp_thinlist_le") \
    // sortRel row: (8.6), p. 201
    #src[every list got by sorting the set and then thinning it by `Q` is also got by thinning the
     set by `Q` and then sorting.]],
     // lean:AOP.A8_3.RelSet.ListRel.sort_comp_thinlist_le@12d9be58
  // `sort(≼) : PA⟶[A]`, `ordered(≼)`,`thinlist(Q) : [A]⟶[A]` — @thinlist-defn's
  // `sort(≼)≜setify° ordered(≼)` at `setify : [A]⟶PA`.
  lean-calc(calc-86),
)]<thinlist-86>

// B&dM Lemma 8.1, p. 202, mirrored.  The chain walks the sort INWARDS, past `filter(p)`, then past
// `list(f)`, then under `F` — each step one of (8.9), (8.8), (8.11).
// `sort(≼) : PA⟶[A]` is where one datatype becomes another, and nothing survives outside it, so it
// is a NODE on the object wire — the `E` bends in, the `list` bends out — not a bead on a lane.
#disp(num: "Lemma 8.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.ListRel.Fmap_sort_comp_listcp_list_filter_le") \
    #src[sorting each argument set (`F(sort(≼))`), forming every combination of their elements
     (`listcp`), applying `f` to each (`list(f)`) and keeping those that pass `p` (`filter(p)`)
     gives one of the sorted lists of the set of all `f(u)` that pass `p`, with `u` drawn from the
     argument sets.
     // map_sort row: Lemma 8.1, p. 202
 ]],
     // lean:AOP.A8_3.RelSet.ListRel.Fmap_sort_comp_listcp_list_filter_le@307a8486
  // `filter(p) : [A]⟶[A]` — @thinlist-defn's `gᵢ≜list(fᵢ) filter(pᵢ)`.
  lean-calc(calc-l81),
)]<thinlist-lem81>

// Lemma 8.1 worked example, asked for by the user: each side step by step on one input.
#disp[
At `F(X)=L+E×X`, `f(r(e,x))=e+x`, `≼` is `≤`, `p` passes the odd numbers, input `r(3,{4,1,2})`.
#table(
  columns: (2.6cm, 1fr, 4.6cm),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*left side*], [*what it does*], [*result*]),
  [input], [an `r(e,xs)`, `xs` a set], [`r(3,{4,1,2})`],
  [`F(sort(≼))`], [sorts the set in the `X` place; `e` is untouched], [`r(3,[1,2,4])`],
  [`listcp`], [pairs `e` with each element, in list order], [`[r(3,1),r(3,2),r(3,4)]`],
  [`list(f)`], [`f` on each], [`[4,5,7]`],
  [`filter(p)`], [keeps the odd ones, order kept], [`[5,7]`],
)
#table(
  columns: (2.6cm, 1fr, 4.6cm),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*right side*], [*what it does*], [*result*]),
  [input], [], [`r(3,{4,1,2})`],
  [`F(∋)`], [relates `r(3,xs)` to each `r(3,x)` with `x∈xs`], [`r(3,4)`, `r(3,1)`, `r(3,2)`],
  [`f`], [], [`7`, `4`, `5`],
  [`p`], [only odd values pass], [`7`, `5`],
  [`Λ(…)`], [collects every result into one set], [`{5,7}`],
  [`sort(≼)`], [], [`[5,7]`],
)
- `⊑`: the left's `[5,7]` is one result of the right; with ties `sort(≼)` has several orders.
- `f` preserving `≼` is used at `list(f)`: `[1,2,4]` is sorted, so `[4,5,7]` is; `filter(p)` only drops
  elements. With `f(r(e,x))=e−x` the left gives `[1,−1]` after `p`, not sorted, so `⊑` fails.
]

// B&dM Theorem 8.2, p. 202–203: the binary thinning theorem.
=== Binary thinning

// The data Theorem 8.2 and its fusion condition are stated at: no single definition, so it stays
// a list of assumptions rather than a row of the table above.
#disp[#definition[
*Binary thinning* data: #h(4pt) `Q` a preorder with `Q⊑R` and both `f₁p₁`, `f₂p₂` monotonic on
`Q`; #h(4pt) `≼` a connected preorder with both `f₁`, `f₂` monotonic on `≼`; #h(4pt) `R` a
preorder.
]]<binthin-data>

// B&dM Theorem 8.2, p. 203, mirrored.  The candidate SET of the thinning theorem becomes a sorted
// LIST: `E` is killed by `est(R)`, `list` by `minlist(R)`.
#import "../generated/Freyd.Alg.RelSet.ListRel.thinningList.calc.typ" as calc-82
#disp(num: "Theorem 8.2")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.ListRel.thinningList") \
    // thinningList row: Theorem 8.2, p. 203
    #src[a fold on sorted lists of partial solutions, thinned at every step, refines the thinning
 specification — at @binthin-data. ]],
     // lean:AOP.A8_3.RelSet.ListRel.thinningList@8b11bce1
  lean-calc(calc-82),
)]<thinlist-thm82>

// Theorem 8.2 worked example, asked for by the user, laid out like the Lemma 8.1 one: one row per
// fold step.  `Q` is `=`, so `Q⊑R` and both `fᵢpᵢ` monotonic on `Q` hold trivially.
#disp[
At `F(X)=L+E×X`, `f₁(inl(l))=f₂(inl(l))=0`, `f₁(r(e,x))=x`, `f₂(r(e,x))=e+x`, `p₁` passes all,
`p₂` passes values `≤6`, `≼` is `≤`, `Q` is `=`, `R` is `≥`, input `[3,3,1]`.
#table(
  columns: (2.8cm, 1fr, 1fr, 1fr, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*input*], [`list(f₁) filter(p₁)`], [`list(f₂) filter(p₂)`], [`merge(≼)`],
    [`thinlist(Q)`]),
  [`inl(l)`], [`[0]`], [`[0]`], [`[0,0]`], [`[0]`],
  [`r(1,[0])`], [`[0]`], [`[1]`], [`[0,1]`], [`[0,1]`],
  [`r(3,[0,1])`], [`[0,1]`], [`[3,4]`], [`[0,1,3,4]`], [`[0,1,3,4]`],
  [`r(3,[0,1,3,4])`], [`[0,1,3,4]`], [`[3,4,6]`], [`[0,1,3,3,4,4,6]`], [`[0,1,3,4,6]`],
  [`minlist(R)`], [], [], [], [`6`],
)
- `merge(≼)` is one pass: both copies arrive `≤`-sorted (`fᵢ` monotonic on `≼`, `filter(pᵢ)` only
  drops), so it only compares their two heads.
- `thinlist(Q)` compares neighbours only; the list is `≤`-sorted, so equal values are neighbours and one
  pass drops every repeat.
]

// The fusion condition of the first step above, B&dM p. 203.
#import "../generated/Freyd.Alg.RelSet.ListRel.sortedAlg_fusion.calc.typ" as calc-82f
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.ListRel.sortedAlg_fusion") \
    // sortedAlg-fusion row: B&dM p. 203
    #src[sorting the candidate set turns the thinning algebra into an algebra on sorted lists. ]],
     // lean:AOP.A8_3.RelSet.ListRel.sortedAlg_fusion@2ef7b16c
  lean-calc(calc-82f),
)]<thinlist-fusion>


== The knapsack problem

// B&dM §8.4, p. 205.  The printed base of the final fold is `nil`, without the outer `wrap` that
// §8.5 and §8.6 do print (`wrap wrap wrap`, `start wrap`).
#disp[#deftab(

  [#rowkey("Freyd.Alg.RelSet.ListRel.total")], [#leant("Freyd.Alg.RelSet.ListRel.total")],
  [#leanf("Freyd.Alg.RelSet.ListRel.total_eq")],
  [add up f over the items of the list],
  [#rowkey("Freyd.Alg.RelSet.ListRel.subseq")], [#leant("Freyd.Alg.RelSet.ListRel.subseq")],
  [#leanf("Freyd.Alg.RelSet.ListRel.subseq_cata")],
  [every subsequence of the list],
  [#rowkey("Freyd.Alg.RelSet.Knapsack.value")], [#leant("Freyd.Alg.RelSet.Knapsack.value")],
  [#leanf("Freyd.Alg.RelSet.Knapsack.value_eq")],
  [the total value of a packing],
  [#rowkey("Freyd.Alg.RelSet.Knapsack.weight")], [#leant("Freyd.Alg.RelSet.Knapsack.weight")],
  [#leanf("Freyd.Alg.RelSet.Knapsack.weight_eq")],
  [the total weight of a packing],
  [#rowkey("Freyd.Alg.RelSet.Knapsack.con_eq_junc")], [#leant("Freyd.Alg.RelSet.Knapsack.con_eq_junc")],
  [#leanf("Freyd.Alg.RelSet.Knapsack.con_eq_junc")],
  [keep the item: the list constructor],
  [#rowkey("Freyd.Alg.RelSet.Knapsack.dropFn")], [#leant("Freyd.Alg.RelSet.Knapsack.dropFn")],
  [#leanf("Freyd.Alg.RelSet.Knapsack.drop_eq_junc")],
  [drop the item: keep the tail],
  [#rowkey("Freyd.Alg.RelSet.Knapsack.within")], [#leant("Freyd.Alg.RelSet.Knapsack.within")],
  [#leanf("Freyd.Alg.RelSet.Knapsack.within_apply")],
  [the packing weighs at most w],
  [#rowkey("Freyd.Alg.RelSet.Knapsack.Salg")], [#leant("Freyd.Alg.RelSet.Knapsack.Salg")],
  [#leanf("Freyd.Alg.RelSet.Knapsack.Salg")],
  [at each item, keep it if the packing still fits, or drop it],
  [#rowkey("Freyd.Alg.RelSet.Knapsack.R")], [#leant("Freyd.Alg.RelSet.Knapsack.R")],
  [#leanf("Freyd.Alg.RelSet.Knapsack.R_eq")],
  [x is worth at least as much as y],
  [#rowkey("Freyd.Alg.RelSet.Knapsack.Q")], [#leant("Freyd.Alg.RelSet.Knapsack.Q")],
  [#leanf("Freyd.Alg.RelSet.Knapsack.Q_eq")],
  [x is worth at least as much as y and weighs no more],
// lean:AOP.A5_6_ListCombinators.total@374f995b
// lean:AOP.A5_6_ListCombinators.total_eq@2b26e4d0
// lean:AOP.A5_6_ListCombinators.subseq@9db1a985
// lean:AOP.A5_6_ListCombinators.subseq_cata@8a4731df
// lean:AOP.A8_4_Knapsack.value@37f1f8ed
// lean:AOP.A8_4_Knapsack.value_eq@f814ce68
// lean:AOP.A8_4_Knapsack.weight@37f1f8ed
// lean:AOP.A8_4_Knapsack.weight_eq@267afa15
// lean:AOP.A8_4_Knapsack.con_eq_junc@f6f12bd6
// lean:AOP.A8_4_Knapsack.dropFn@08a216bd
// lean:AOP.A8_4_Knapsack.drop_eq_junc@1f5b4c77
// lean:AOP.A8_4_Knapsack.within@945da576
// lean:AOP.A8_4_Knapsack.Salg@7d39c25b
// lean:AOP.A8_4_Knapsack.Salg_junc@56a14e5c
// lean:AOP.A8_4_Knapsack.R@9a274328
// lean:AOP.A8_4_Knapsack.R_eq@d1b279af
// lean:AOP.A8_4_Knapsack.Q@7cb37d7d
// lean:AOP.A8_4_Knapsack.Q_eq@79079c45
// lean:AOP.A8_4_Knapsack.within_apply@9a705752
// lean:AOP.A8_4_Knapsack.R_apply@787706e9
// lean:AOP.A8_4_Knapsack.Q_apply@43d4a123
)]<knap-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) (cons (within w))⊑cons (within w)R` \ #src[FALSE]],
  [not monotonic on `R`: a selection of greater value need not still fit once one more item goes in],
  [#leanf("Freyd.Alg.RelSet.Knapsack.knap_mono_cons") \ #leanf("Freyd.Alg.RelSet.Knapsack.knap_mono_drop")
 #src[,
   // lean:AOP.A8_4_Knapsack.knap_mono_cons@53c00514
 ]],
   // lean:AOP.A8_4_Knapsack.knap_mono_drop@e779f3ef
  [both halves are monotonic on `Q` once ties in value are broken by weight],
  [#leanf("Freyd.Alg.RelSet.Knapsack.knap_sort_cons") \ #leanf("Freyd.Alg.RelSet.Knapsack.knap_sort_drop")],
  // lean:AOP.A8_4_Knapsack.knap_sort_cons@837e4575
  // lean:AOP.A8_4_Knapsack.knap_sort_drop@c890ae16
  [both algebras are monotonic on `R` itself, so `R` is the sort order `P`],
)]<knap-mono>

=== Derivation
// B&dM §8.4, p. 206.  The set the transpose opens becomes a LIST at the binary thinning step, and
// that swap — `E` killed by `est(R)`, `list` killed by `minlist(R)` — is what the right column draws.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Knapsack.knap_laws") \
    // knapsack row: B&dM §8.4, p. 206
    #src[the knapsack problem, as a fold that thins the packings kept at each item]],
     // lean:AOP.A8_4_Knapsack.knap_laws@3afe2d7d
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.rhs"),
    [#leanf("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.rhs")])],
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.lhs"),
    [#leanf("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.lhs") \
 #src[@cata-fusion, weights non-negative. ]])],
     // lean:AOP.A8_4_Knapsack.knap_spec@4c91383d
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.lhs", step: true)],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step1.lhs"),
    [#leanf("Freyd.Alg.RelSet.Knapsack.knap_laws_step1.lhs") \
     #src[@thinlist-thm82, at `P≜R`, `F` linear, `Q` from @knap-mono:2]])],
  // The candidate set is now a candidate LIST: the reduce births `list` where it births `E` above.
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step1.lhs")],

  [#vstep(EQ, [],
    [`⦇[nil,cpr ⟨h₁,h₂⟩ merge R thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ=[list(nil),hᵢ]` — @Freyd.Alg.RelSet.Knapsack.con_eq_junc, @Freyd.Alg.RelSet.Knapsack.dropFn; `minlist(R)` is `head`, packings
      coming out in descending value]])],
  [],
)]<knap-laws>

== The paragraph problem

// B&dM §8.5, p. 207.  `P ≜ ⊤` works because `merge ⊤ = cat`, which already brings equal first lines
// together; the book's first choice `head prefix head°` is correct but not needed.
#disp[#deftab(

  [#rowkey("Freyd.Alg.RelSet.Paragraph.Line")], [#leant("Freyd.Alg.RelSet.Paragraph.Line")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.Line")],
  [a line is a non-empty list of words],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.Para")], [#leant("Freyd.Alg.RelSet.Paragraph.Para")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.Para")],
  [a paragraph is a non-empty list of lines],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.new")], [#leant("Freyd.Alg.RelSet.Paragraph.new")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.new")],
  [start a new first line holding only the word a],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.glue")], [#leant("Freyd.Alg.RelSet.Paragraph.glue")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.glue")],
  [put the word a at the front of the first line],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.newAlgFn")], [#leant("Freyd.Alg.RelSet.Paragraph.newAlgFn")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.newAlgFn")],
  [one word is a one-line paragraph; each further word starts a new line],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.glueAlgFn")], [#leant("Freyd.Alg.RelSet.Paragraph.glueAlgFn")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.glueAlgFn")],
  [one word is a one-line paragraph; each further word joins the first line],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.partition")], [#leant("Freyd.Alg.RelSet.Paragraph.partition")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.partition")],
  [every way of breaking the words into lines],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.widthFn")], [#leant("Freyd.Alg.RelSet.Paragraph.widthFn")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.widthFn")],
  [the lengths of the words plus one space between neighbours],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.head")], [#leant("Freyd.Alg.RelSet.Paragraph.head")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.head")],
  [the first line of the paragraph],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.allFitP")], [#leant("Freyd.Alg.RelSet.Paragraph.allFitP")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.allFitP")],
  [every line is at most w wide],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.fits")], [#leant("Freyd.Alg.RelSet.Paragraph.fits")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.allFitP")],
  [the paragraphs whose every line is at most w wide],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.ok")], [#leant("Freyd.Alg.RelSet.Paragraph.ok")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.okP")],
  [the paragraphs whose first line is at most w wide],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.sqr")], [#leant("Freyd.Alg.RelSet.Paragraph.sqr")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.sqr")],
  [n squared],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.wasteFn")], [#leant("Freyd.Alg.RelSet.Paragraph.wasteFn")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.wasteFn")],
  [the squared white space left on every line but the last, added up],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.R")], [#leant("Freyd.Alg.RelSet.Paragraph.R")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.R_eq")],
  [p wastes no more than q],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.Q")], [#leant("Freyd.Alg.RelSet.Paragraph.Q")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.Q_eq")],
  [p wastes no more than q and has the same first line],
  [#rowkey("Freyd.Alg.RelSet.Paragraph.start")], [#leant("Freyd.Alg.RelSet.Paragraph.start")],
  [#leanf("Freyd.Alg.RelSet.Paragraph.start")],
  [the one candidate for a single word: the paragraph of one line holding that word],
// lean:AOP.A8_5_Paragraph.Line@5d1dfba3
// lean:AOP.A8_5_Paragraph.Para@03a1f9c7
// lean:AOP.A8_5_Paragraph.new@bda7247b
// lean:AOP.A8_5_Paragraph.glue@f4a46e72
// lean:AOP.A8_5_Paragraph.newAlgFn@e587172a
// lean:AOP.A8_5_Paragraph.glueAlgFn@65824f9e
// lean:AOP.A8_5_Paragraph.partition@913aa4cf
// lean:AOP.A8_5_Paragraph.widthFn@925793a1
// lean:AOP.A8_5_Paragraph.head@d781968f
// lean:AOP.A8_5_Paragraph.allFitP@1d59ef2e
// lean:AOP.A8_5_Paragraph.fits@e9533e02 lean:AOP.A8_5_Paragraph.allFitP@1d59ef2e
// lean:AOP.A8_5_Paragraph.ok@6a24d4f2 lean:AOP.A8_5_Paragraph.okP@5ebaf3a1
// lean:AOP.A8_5_Paragraph.sqr@0bb9fcb4
// lean:AOP.A8_5_Paragraph.wasteFn@598047f9
// lean:AOP.A8_5_Paragraph.R@1aaea13f
// lean:AOP.A8_5_Paragraph.R_eq@cf0ea074
// lean:AOP.A8_5_Paragraph.Q@546d086e
// lean:AOP.A8_5_Paragraph.Q_eq@72a43c20
// lean:AOP.A8_5_Paragraph.fits_apply@42c87fb1
// lean:AOP.A8_5_Paragraph.ok_apply@b7eeed25
// lean:AOP.A8_5_Paragraph.R_apply@358f7c84
// lean:AOP.A8_5_Paragraph.Q_apply@57c91c80
// lean:AOP.A8_5_Paragraph.start@056fc54e
)]<para-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) glue⊑glue R` #h(6pt) #src[FALSE]],
  [`glue` is not monotonic on `R`: the waste of a paragraph depends on its whole first line, so no
   greedy algorithm solves this],
  [#leanf("Freyd.Alg.RelSet.Paragraph.para_mono_new") \ #leanf("Freyd.Alg.RelSet.Paragraph.para_mono_glue") \ #src[`cons` monotonic on
 `collect≤collect°`. ,
   // lean:AOP.A8_5_Paragraph.para_mono_new@e5ccddce
 ]],
   // lean:AOP.A8_5_Paragraph.para_mono_glue@86db095e
  [both halves are monotonic on `Q` once ties in waste are broken by the first line],
  [#leanf("Freyd.Alg.RelSet.ListRel.merge_top")],
  // lean:AOP.A8_3.merge_top@9e31b76a
  [`⊤` needs no sorting at all],
  [#leanf("Freyd.Alg.RelSet.Paragraph.para_sort_new") \ #leanf("Freyd.Alg.RelSet.Paragraph.para_sort_glue")],
  // lean:AOP.A8_5_Paragraph.para_sort_new@c164c661
  // lean:AOP.A8_5_Paragraph.para_sort_glue@65a740c1
  [both algebras are monotonic on `⊤`, so `⊤` is the sort order `P`],
)]<para-mono>

=== Derivation
// B&dM §8.5, p. 210.  `partition` turns ONE list into two — the paragraph and its lines — so it is a
// bead on the object wire with three list wires at it, and the candidate set is a fourth.
// The source is ONE `L`; `partition` births the paragraph's, and the reduce of the last two rows
// births a third — the list of candidate paragraphs `minlist(R)` reads back down.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Paragraph.para_laws") \
    // paragraph row: B&dM §8.5, p. 210
    #src[a paragraph laid out as a fold that thins the layouts kept at each word]],
     // lean:AOP.A8_5_Paragraph.para_laws@cf96b9c5
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step2.rhs"),
    [#leanf("Freyd.Alg.RelSet.Paragraph.para_laws_step2.rhs")])],
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step2.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step2.lhs"),
    [#leanf("Freyd.Alg.RelSet.Paragraph.para_laws_step2.lhs") \
     #src[@cata-fusion, every word fits on a line by itself.
 ]])],
     // lean:AOP.A8_5_Paragraph.para_alg_fusion@031c245f
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step2.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Paragraph.para_laws_split.rhs"),
    [#leanf("Freyd.Alg.RelSet.Paragraph.para_laws_split.rhs") \
     #src[the algebra as `(f₁p₁) ∪ (f₂p₂)`, `p₁≜𝟙` — @thinlist-thm82.
 ]])],
     // lean:AOP.A8_5_Paragraph.para_spec@0ec1a795
  // Empty: the step renames the algebra and the panel above already draws the reduce.
  [],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step1.lhs"),
    [#leanf("Freyd.Alg.RelSet.Paragraph.para_laws_step1.lhs") \
     #src[@thinlist-thm82, at `P≜⊤` with `merge ⊤=cat` (@para-mono:3), `Q` from @para-mono:2]])],
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step1.lhs")],

  [#vstep(EQ, [],
    [`⦇[start,cpr ⟨h₁,h₂⟩ cat thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ` along the coproduct — @para-defn:5, @para-defn:6]])],
  [],
)]<para-laws>

== Bitonic tours

// B&dM §8.6, p. 212.  `Q` keeps the `head2` conjunct p.215 derives and then drops on the grounds
// that tours of one input share their heads: without it the two `tour-mono` rows are false.
#disp[#deftab(

  [#rowkey("Freyd.Alg.RelSet.Tour.Journey")], [#leant("Freyd.Alg.RelSet.Tour.Journey")],
  [#leanf("Freyd.Alg.RelSet.Tour.Journey")],
  [a list of at least two cities, the last two held as a pair],
  [#rowkey("Freyd.Alg.RelSet.Tour.Tour")], [#leant("Freyd.Alg.RelSet.Tour.Tour")],
  [#leanf("Freyd.Alg.RelSet.Tour.Tour")],
  [the outward journey and the return journey],
  [#rowkey("Freyd.Alg.RelSet.Tour.head")], [#leant("Freyd.Alg.RelSet.Tour.head")],
  [#leanf("Freyd.Alg.RelSet.Tour.head")],
  [the first city of the journey],
  [#rowkey("Freyd.Alg.RelSet.Tour.next")], [#leant("Freyd.Alg.RelSet.Tour.next")],
  [#leanf("Freyd.Alg.RelSet.Tour.next")],
  [the second city of the journey],
  [#rowkey("Freyd.Alg.RelSet.Tour.replaceHead")], [#leant("Freyd.Alg.RelSet.Tour.replaceHead")],
  [#leanf("Freyd.Alg.RelSet.Tour.replaceHead")],
  [replace the first city of the journey by a],
  [#rowkey("Freyd.Alg.RelSet.Tour.outcost")], [#leant("Freyd.Alg.RelSet.Tour.outcost")],
  [#leanf("Freyd.Alg.RelSet.Tour.outcost")],
  [the cost of travelling the journey forwards],
  [#rowkey("Freyd.Alg.RelSet.Tour.incost")], [#leant("Freyd.Alg.RelSet.Tour.incost")],
  [#leanf("Freyd.Alg.RelSet.Tour.incost")],
  [the cost of travelling the journey backwards],
  [#rowkey("Freyd.Alg.RelSet.Tour.cost")], [#leant("Freyd.Alg.RelSet.Tour.cost")],
  [#leanf("Freyd.Alg.RelSet.Tour.cost")],
  [the outward journey forwards plus the return journey backwards],
  [#rowkey("Freyd.Alg.RelSet.Tour.start")], [#leant("Freyd.Alg.RelSet.Tour.start")],
  [#leanf("Freyd.Alg.RelSet.Tour.start")],
  [the tour of the last two cities, both journeys being that one edge],
  [#rowkey("Freyd.Alg.RelSet.Tour.droplFn")], [#leant("Freyd.Alg.RelSet.Tour.droplFn")],
  [#leanf("Freyd.Alg.RelSet.Tour.droplFn")],
  [a replaces the first city of the outward journey and is put in front of the return],
  [#rowkey("Freyd.Alg.RelSet.Tour.droprFn")], [#leant("Freyd.Alg.RelSet.Tour.droprFn")],
  [#leanf("Freyd.Alg.RelSet.Tour.droprFn")],
  [a is put in front of the outward journey and replaces the first city of the return],
  [#rowkey("Freyd.Alg.RelSet.Tour.droplAlgFn")], [#leant("Freyd.Alg.RelSet.Tour.droplAlgFn")],
  [#leanf("Freyd.Alg.RelSet.Tour.droplAlgFn")],
  [start at the last two cities, then add each city by dropl],
  [#rowkey("Freyd.Alg.RelSet.Tour.droprAlgFn")], [#leant("Freyd.Alg.RelSet.Tour.droprAlgFn")],
  [#leanf("Freyd.Alg.RelSet.Tour.droprAlgFn")],
  [start at the last two cities, then add each city by dropr],
  [#rowkey("Freyd.Alg.RelSet.Tour.tour")], [#leant("Freyd.Alg.RelSet.Tour.tour")],
  [#leanf("Freyd.Alg.RelSet.Tour.tour")],
  [every bitonic tour of the cities],
  [#rowkey("Freyd.Alg.RelSet.Tour.R")], [#leant("Freyd.Alg.RelSet.Tour.R")],
  [#leanf("Freyd.Alg.RelSet.Tour.R_eq")],
  [t costs no more than t′],
  [#rowkey("Freyd.Alg.RelSet.Tour.next2")], [#leant("Freyd.Alg.RelSet.Tour.next2")],
  [#leanf("Freyd.Alg.RelSet.Tour.next2")],
  [the second cities of both journeys],
  [#rowkey("Freyd.Alg.RelSet.Tour.head2")], [#leant("Freyd.Alg.RelSet.Tour.head2")],
  [#leanf("Freyd.Alg.RelSet.Tour.head2")],
  [the first cities of both journeys],
  [#rowkey("Freyd.Alg.RelSet.Tour.Qc")], [#leant("Freyd.Alg.RelSet.Tour.Qc")],
  [#leanf("Freyd.Alg.RelSet.Tour.Qc_eq")],
  [t costs no more than t′, and both journeys of t and t′ share their first two cities],
// lean:AOP.A8_6_Tour.Journey@43d30e10
// lean:AOP.A8_6_Tour.Tour@5351625c
// lean:AOP.A8_6_Tour.head@8f3cba94
// lean:AOP.A8_6_Tour.next@6c6f8f88
// lean:AOP.A8_6_Tour.replaceHead@7ff6abf9
// lean:AOP.A8_6_Tour.outcost@d2f4dc52
// lean:AOP.A8_6_Tour.incost@f7717a87
// lean:AOP.A8_6_Tour.cost@06de8db1
// lean:AOP.A8_6_Tour.start@d985a9ce
// lean:AOP.A8_6_Tour.droplFn@fbc7f8e7
// lean:AOP.A8_6_Tour.droprFn@f1f2bddf
// lean:AOP.A8_6_Tour.droplAlgFn@b62e1231
// lean:AOP.A8_6_Tour.droprAlgFn@1ee00147
// lean:AOP.A8_6_Tour.tour@e98fe8cb
// lean:AOP.A8_6_Tour.R@99271c4e
// lean:AOP.A8_6_Tour.R_eq@15ad4adc
// lean:AOP.A8_6_Tour.Qc@dc87d553
// lean:AOP.A8_6_Tour.R_apply@f30bcc6e
// lean:AOP.A8_6_Tour.next2@dc51681a
// lean:AOP.A8_6_Tour.head2@593fe366
// lean:AOP.A8_6_Tour.Qc_eq@1fd75015
// lean:AOP.A8_6_Tour.Qc_apply@cbc2eb9b
)]<tour-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) dropl⊑dropl R` #h(6pt) #src[FALSE] \ `(𝟙×R) dropr⊑dropr R` #h(6pt) #src[FALSE]],
  [neither drop is monotonic on `R`: the two edges it adds and removes depend on `head` and `next`
   of both lists],
  [#leanf("Freyd.Alg.RelSet.Tour.tour_mono_dropl") \ #leanf("Freyd.Alg.RelSet.Tour.tour_mono_dropr")
 #src[,
   // lean:AOP.A8_6_Tour.tour_mono_dropl@3401aca0
 ]],
   // lean:AOP.A8_6_Tour.tour_mono_dropr@2e2401d3
  [both are, once ties in cost are broken by the two second cities — the heads already agree among
   tours of one input],
  [#leanf("Freyd.Alg.RelSet.Tour.tour_sort_dropl") \ #leanf("Freyd.Alg.RelSet.Tour.tour_sort_dropr")],
  // lean:AOP.A8_6_Tour.tour_sort_dropl@2a2e451c
  // lean:AOP.A8_6_Tour.tour_sort_dropr@cc84df43
  [both algebras are monotonic on `⊤`, so `⊤` is the sort order `P`],
)]<tour-mono>

=== Derivation
// B&dM §8.6, p. 215.  A tour is a PAIR of lists, so `[City]×[City]` is the one unary functor
// `X↦[X]×[X]` — a bifunctor is never a wire, and this one is partially applied before it is drawn.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Tour.tour_laws") \
    // tour row: B&dM §8.6, p. 215
    #src[a least-cost bitonic tour, as a fold that thins the tours kept at each city]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Tour.tour_laws.rhs"), [#leanf("Freyd.Alg.RelSet.Tour.tour_laws.rhs")])],
  [#lean("Freyd.Alg.RelSet.Tour.tour_laws.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Tour.tour_laws_defn.rhs"),
    [#leanf("Freyd.Alg.RelSet.Tour.tour_laws_defn.rhs") \ #src[@Freyd.Alg.RelSet.Tour.tour]])],
  // Empty: the step only names the reduce, and the panel above already draws it.
  [],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Tour.tour_laws.lhs"),
    [#leanf("Freyd.Alg.RelSet.Tour.tour_laws.lhs") \
     #src[@thinlist-thm82, at `P≜⊤` with `merge ⊤=cat`, `Q` from @tour-mono:2]])],
  [#lean("Freyd.Alg.RelSet.Tour.tour_laws.lhs", step: true)],

  [#vstep(EQ, [],
    [`⦇[start wrap,cpr ⟨list(dropl),list(dropr)⟩ cat thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ=[list(start),list(dropᵢ)]` — @tour-defn:12, @tour-defn:13; quadratic, two tours
      added per step]])],
  [],
)]<tour-laws>

#pagebreak(weak: true)
