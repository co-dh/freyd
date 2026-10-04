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
For `Q : A⟶A`, #h(4pt) `thin(Q)≜(∋/∋)∩(∈\(Q°∈)) : PA⟶PA` #h(4pt) #src[(8.1)].

`ys thin(Q) xs⟺xs⊆ys∧(∀a∈ys. ∃b∈xs. b Q a)` #src[the same `°` as @est-defn: `∈X` runs `a⟶ys⟶xs`, member of `ys` first, and `Q°∈` runs `a⟶b⟶xs`, so `(a,b)∈Q°` reads `b Q a`; at `Q≜≤` every `a∈ys` keeps some `b≤a` in `xs`, the end `est(≤)` picks]
// lean:AOP.A8_1.thinRel_pt@f6ff770e
]]<thin-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X⊑` $frac(#[`S`], ∋)$ `thin(Q)⟺X∋⊑S` and `S°X⊑Q°∈`],
  [everything kept is an `S`-value, and every `S`-value has a `Q`-lower bound among the kept ones],
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
  [#leanf("Freyd.Alg.thinRel_comp_est") #h(4pt) #src[`Q⊑R`, `𝟙⊑Q`, `RR⊑R` — @thin-intro; weaker than the book’s "both preorders": `Q` transitive is never used and `𝟙⊑R` follows]],
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
  [#leanf("Freyd.Alg.powerRel_thinRel_comp_bigUnion_le") #h(6pt) #src[(8.4)]],
  [thinning each member set is a thinning of the union],
)]<thin-laws>

=== `X⊑(S%∋) thin(Q)⟺X∋⊑S` and `S°X⊑Q°∈`

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
#src[@thin-up at `X≜thin(Q)`, `S≜∋`: the left side is `thin(Q)⊑thin(Q)`, since `∋%∋=Λ(∋)=𝟙`]
]<thin-up-eps>

=== `est(R)=thin(Q) est(R)` given `Q⊑R`, `𝟙⊑Q`, `RR⊑R`

// B&dM p. 194, thin-introduction, mirrored: the row above read as a calculation.
#grid(columns: (1fr, 1fr), column-gutter: 42pt, align: top,
[#disp[
   // lean:AOP.A8_1.thinRel_comp_est@eafff35f
#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[`est(R)⊑thin(Q) est(R)` \
    #src[the `⊑` half: keeping everything is a thinning — `𝟙⊑Q`]],
     // lean:AOP.A8_1.thinRel_comp_est_step1@65f6cc95
  lean-chain(
    (none, "Freyd.Alg.thinRel_comp_est_step1.lhs", []),
    (SQ, "Freyd.Alg.thinRel_comp_est_step1.rhs", src[`𝟙⊑thin(Q)` — @thin-laws]),
  ),
)
]<thin-intro>],
[#disp[
#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[`thin(Q) est(R)⊑∋` \
    #src[the `⊒` half, first condition of the UP of `est` at `X≜thin(Q) est(R)` — @est-up]],
     // lean:AOP.A8_1.thinRel_comp_est_cond1@2c9241e0
  lean-chain(
    (none, "Freyd.Alg.thinRel_comp_est_step2.lhs", []),
    (SQ, "Freyd.Alg.thinRel_comp_est_step2.rhs", src[`est(R)⊑∋` — @est-laws]),
    (SQ, "Freyd.Alg.thinRel_comp_eps_le.rhs",
      src[`thin(Q)∋⊑∋` — @thin-up]),
  ),
)
]<thin-intro-up1>])

#disp[
#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[`∈ thin(Q) est(R)⊑R°` \
    #src[the `⊒` half, second condition — `Q⊑R`, `R` transitive]],
     // lean:AOP.A8_1.thinRel_comp_est_cond2@1bf58dd7
  lean-chain(
    (none, "Freyd.Alg.thinRel_comp_est_step3.lhs", []),
    (SQ, "Freyd.Alg.thinRel_comp_est_step3.rhs",
      src[`∈ thin(Q)⊑Q°∈` — @thin-up]),
    (SQ, "Freyd.Alg.thinRel_comp_est_step4.rhs",
      src[`∈ est(R)⊑R°` — @est-laws]),
    (SQ, "Freyd.Alg.thinRel_comp_est_step5.rhs", src[`Q⊑R`]),
    (SQ, "Freyd.Alg.thinRel_comp_est_step6.rhs", src[`R` transitive]),
  ),
)]<thin-intro-up2>

// B&dM (8.2), p. 194, mirrored.  `thin` is a meet of two divisions, so the law is its two halves:
// the first cancels the singleton against the `∋`, the second is the chain.
#disp(num: "(8.2)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.est_comp_singletonMap_le_thinRel") \
    #src[the singleton holding a `Q`-least member of a set is a thinning of that set
     // thin-elimination row: (8.2), p. 194
 #h(4pt) ]],
     // lean:AOP.A8_1.est_comp_singletonMap_le_thinRel@8aad298c
  lean-chain(Sub("Freyd.Alg.est_comp_singletonMap_cond1",
    gloss: src[every member of the singleton is a member of the set],
    (IMP, "Freyd.Alg.est_comp_singletonMap_cond1.lhs",
      src[@thin-defn, `∋/∋` half]),
     // lean:AOP.A8_1.est_comp_singletonMap_cond1@14824541
    (SQ, "Freyd.Alg.est_comp_singletonMap_cond1.rhs",
      src[#frc([`𝟙`])`∋=𝟙` — @pow-laws; `est(Q)⊑∋` — @est-laws]),
  ), Sub("Freyd.Alg.est_comp_singletonMap_cond2",
    gloss: src[the singleton's member stands in `Q` to every member of the set],
    (IMP, "Freyd.Alg.est_comp_singletonMap_cond2_step1.lhs", src[@thin-defn, `∈\(Q°∈)` half]),
     // lean:AOP.A8_1.est_comp_singletonMap_cond2@9dbd159d
    (SQ, "Freyd.Alg.est_comp_singletonMap_cond2_step1.rhs",
      src[`∈ est(Q)⊑Q°` — @est-up]),
     // lean:AOP.A8_1.est_comp_singletonMap_cond2_step1@b4d0cc01
    (SQ, "Freyd.Alg.recip_comp_singletonMap_le.rhs",
      src[#frc([`𝟙`])`⊑∈` — @pow-laws]),
     // lean:AOP.A8_1.recip_comp_singletonMap_le@e1798cc6
  )),
)]<thin-82>

// B&dM (8.3), p. 194, mirrored.  The first of the two conditions cancels the singleton against `∋`;
// the second is the chain, and the context row is where the side condition enters.
#disp(num: "(8.3)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.Λ_comp_est_comp_singletonMap_le_thinRel") \
    #src[given `R∩(S°S)⊑Q`, `Q` a preorder
     // thinning row: (8.3), p. 194
 #h(4pt) ]],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_le_thinRel@d66c2a44
  lean-chain(Sub("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1",
    gloss: src[every member of the singleton is a value `S` returns],
    (IMP, "Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1.lhs",
      src[@thin-laws, first condition]),
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond1@58772169
    (SQ, "Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1.rhs",
      src[#frc([`𝟙`])`∋=𝟙` — @pow-laws; #frc([`S`])` est(R)⊑S` — @est-laws]),
  ), Sub("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2",
    gloss: src[the singleton's member stands in `Q` to every value `S` returns at the same argument],
    (IMP, "Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_context.lhs", src[@thin-laws, second condition]),
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond2@aa38c1af
    (EQ, "Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_context.rhs",
      src[#frc([`S`])` est(R)=`#frc([`S`])` est(R∩S°S)` — @est-laws]),
    (SQ, "Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_step1.rhs",
      src[`S°`#frc([`S`])`⊑∈` — @pow-laws]),
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond2_step1@f65de19f
  ), (
    (SQ, "Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_step2.rhs",
      src[`∈ est(R∩S°S)⊑(R∩S°S)°` — @est-up; `R∩(S°S)⊑Q`]),
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond2_step2@fde1a573
    (SQ, "Freyd.Alg.recip_comp_singletonMap_le.rhs",
      src[#frc([`𝟙`])`⊑∈` — @pow-laws]),
     // lean:AOP.A8_1.recip_comp_singletonMap_le@e1798cc6
  )),
)]<thin-83>

// B&dM Theorem 8.1, p. 195, mirrored.  The proof is about the SECOND half of `thin`'s universal
// property: the first half is fusion, and the hylomorphism theorem turns the second into one chain.
// `thin(Q) : PA⟶PA` is fixed by one `Q`, not natural in `A`: an arrow of the object `PA`, so its bead
// touches both wires — the `E` it receives dies at it and the `E` it returns is born there.
#disp(num: "Theorem 8.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning") \
    #src[thinning at every step of the reduce is a thinning of the whole candidate set —
     // thinning-of-reduce row: Theorem 8.1, p. 195
     `S` monotonic on `Q`, `Q` a preorder
 #h(4pt) ]],
     // lean:AOP.A8_1.thinning@5c4fa102
  // A conjunction has no shape in either calculus, so it heads the chain as text.
  [`⦇`#frc([`F(∋)S`])` thin(Q)⦈∋⊑⦇S⦈` #h(10pt) and #h(10pt)
   `⦇S⦈°⦇`#frc([`F(∋)S`])` thin(Q)⦈⊑Q°∈` \
   #src[@thin-laws at `X≜⦇`#frc([`F(∋)S`])` thin(Q)⦈`, `⦇S⦈` for its `S`]],
  lean-chain(
    (IMP, "Freyd.Alg.thinning_step1.lhs",
      src[@cata-fusion, @hylo-mu]),
    (SQ, "Freyd.Alg.thinning_step1.rhs",
      src[`S°F(Q°)⊑Q°S°` — @mon-str, @relator-laws]),
    (SQ, "Freyd.Alg.thinning_step2.rhs",
      src[`S°F(∈)`#frc([`F(∋)S`])`⊑∈` — @pow-laws]),
    (SQ, "Freyd.Alg.thinning_step3.rhs", src[`∈ thin(Q)⊑Q°∈` — @thin-defn, @adj-all]),
    (SQ, "Freyd.Alg.thinning_step4.rhs", src[`Q` a preorder]),
  ),
)]<thin-thm81>

// B&dM Corollary 8.1, p. 195: the thinning theorem read against the optimisation problem itself.
// `⦇−⦈` and not the algebra: its transpose opens an `E` INSIDE the reduce, which no outer panel has.
#disp(num: "Corollary 8.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning_est") \
    #src[the thinning fold refines the optimisation problem itself —
     // thinning-est row: Corollary 8.1
     `S` monotonic on `Q`, `Q⊑R`, both preorders
 #h(4pt) ]],
     // lean:AOP.A8_1.thinning_est@bb2ad6af
  lean-chain(
    // The reduce CONSUMES `T` and the transpose inside it BIRTHS `E`, so the two wires meet at one bead.
    (none, "Freyd.Alg.thinning_est_step1.lhs", []),
    (SQ, "Freyd.Alg.thinning_est_step1.rhs", src[@thin-thm81]),
    (EQ, "Freyd.Alg.thinning_est_step2.rhs", src[`est(R)=thin(Q) est(R)` — @thin-laws]),
  ),
)]<thin-cor>

== Paths in a layered network

// B&dM §8.2, p. 196.  `Q` has to record `head` because `wt (a, head xs)` is unbounded: a dearer path
// with a nearer first vertex can still win.
#disp[#definition[
`F(A,X)=A+A×X`, #h(4pt) `L=list⁺` with initial algebra #leanf("Freyd.Alg.RelSet.CL.alphaR") `: F(A,LA)⟶LA`.

#leanf("Freyd.Alg.wrapz"), #h(4pt) #leanf("Freyd.Alg.conswFn_apply").

#leanf("Freyd.Alg.pathCost"), #h(4pt) #leanf("Freyd.Alg.cataR_wrapz_consw"), #h(4pt) #leanf("Freyd.Alg.pathR").

#leanf("Freyd.Alg.pathQ"), #h(4pt) #leanf("Freyd.Alg.algSplit"), #h(4pt) #leanf("Freyd.Alg.Λ_pathF_map_eps_id"), #h(4pt)
#leanf("Freyd.Alg.Λ_pathF_map_id_eps"), #h(4pt) #leanf("Freyd.Alg.pathStep").
// lean:AOP.A6_ConsList.alphaR@d7bb4987
// lean:AOP.A8_2.wrapz@e528d496
// lean:AOP.A8_2.conswFn_apply@c88ec21b
// lean:AOP.A8_2.pathCost@2d18e3c4
// lean:AOP.A8_2.cataR_wrapz_consw@03d3331b
// lean:AOP.A8_2.algSplit@e9b028ae
// lean:AOP.A8_2.costOf@dfe994f6
// lean:AOP.A8_2.pathR@6d0be9c8
// lean:AOP.A8_2.pathQ@adf20bfb
// lean:AOP.A8_2.headRel@32b2507f
// lean:AOP.A8_2.pathStep@f546a21f
// lean:AOP.A8_2.Λ_pathF_map_eps_id@59cd9f69
// lean:AOP.A8_2.Λ_pathF_map_id_eps@b7473cec
]]<path-defn>

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
  // lean:AOP.A8_2.pathAlg_monotonic@7f6f2311 lean:AOP.A8_2.pathSplit_comp_headRel_le@c6b78bec lean:AOP.A8_2.pathR_inter_recip_le_pathQ@2e1f5c5d
)]<path-mono>

// B&dM §8.2, p. 198.  The `E` the transpose opens is born OUTSIDE the reduce in the specification
// and INSIDE it from the thinning theorem on; that is what rows 1 and 2 differ by.
// TWO `E` wires, and that is the content: the one the source carries inside `L` (top port), and the
// one the transpose opens outside it — by the unit `𝟙%∋` above the reduce, or by the reduce itself.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning_paths") \
    // layered-network row: B&dM §8.2, p. 198
    #src[a least-cost path in a layered network, as a fold over the layers]],
     // lean:AOP.A8_2.thinning_paths@f43f12a8
  lean-chain(
    (none, "Freyd.Alg.thinning_paths_step.rhs", src[`=` #frc([`L(∋)`])` est(R)`]),
    // thinning_paths_step row: Corollary 8.1
    (RQ, "Freyd.Alg.thinning_paths_step.lhs", src[@thin-cor, @path-mono]),
  ),
  // No panel: the program's fold is the path instance, and `thinning_paths` states this step over a
  // general `F`, whose algebra is @path-alg's row 6 rather than this row's `[P(wrap),cpl P(step)]`.
  [#RQ #src[@path-alg under #box[`⦇ ⦈`] monotonic: the whole chain runs inside the reduce, and the
    `est(R)` behind it never moves.]],
      // lean:AOP.A8_2.thinning_paths_alg@b4146c58
)]<path-laws>

// B&dM §8.2, p. 198, one row per printed line.  Every step rewrites the ALGEBRA, so the chain is stated
// about the algebra alone: no `⦇ ⦈` around it and no `est(R)` behind it.
// q in row (a): x is the vertex list, y the path list; a path is a list of vertices, head first, so `x,p` is cons.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thinning_paths_alg") \
    // algebra row: B&dM §8.2, p. 198
    #src[thinning the algebra of a layered network costs no more than taking the program's two cases]],
     // lean:AOP.A8_2.thinning_paths_alg@b4146c58
  lean-chain(
    (none, "Freyd.Alg.thinning_paths_alg_map.lhs", src[the algebra of @path-laws row 2]),
    (EQ, "Freyd.Alg.thinning_paths_alg.lhs",
      src[#frc([`F(𝟙,∋)`])` P(α)=`#frc([`S`])]),
      // lean:AOP.A8_2.thinning_paths_alg_map@14c94a65
      // lean:AOP.A4_6.Λ_absorption@00399742
    (EQ, "Freyd.Alg.thinning_paths_alg_elim.lhs", src[`𝟙=P(`#frc([`𝟙`])`) E(∋)`]),
      // lean:AOP.A8_2.thinning_paths_alg_unit@96b5fe96
      // lean:AOP.A4_6.bigUnion_existsImage_singleton@304e0108
      // lean:AOP.A4_6.bigUnion_eq_existsImage_eps@bca8d7c5
    (SQ, "Freyd.Alg.thinning_paths_alg_distrib.lhs",
      src[#frc([`S`])` est(R) `#frc([`𝟙`])`⊑`#frc([`S`])` thin(Q) if R∩(S°S)⊑Q` — @thin-laws, @path-mono]),
      // lean:AOP.A8_2.thinning_paths_alg_elim@92e08ad6
      // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_le_thinRel@d66c2a44
      // lean:AOP.A8_2.pathSplit_eq_Fmap_comp_alphaR@962bc252
    (SQ, "Freyd.Alg.thinning_paths_alg_distrib.rhs",
      src[`P(thin(Q)) E(∋)⊑E(∋) thin(Q)` — @thin-laws]),
      // lean:AOP.A8_2.thinning_paths_alg_distrib@50cc6d67
      // lean:AOP.A8_1.powerRel_thinRel_comp_bigUnion_le@91d6431a
    (EQ, "Freyd.Alg.thinning_paths_alg_bifunctors.lhs",
      src[`P(`#frc([`S`])`) E(∋)=E(S)`, #frc([`R`])` E(S)=`#frc([`RS`])` — `@pow-laws]),
      // lean:AOP.A8_2.thinning_paths_alg_split@c56f2cb9
      // lean:AOP.A8_2.Λ_comp_eq_Λ_comp_powerRel_bigUnion@40ff2482
      // lean:AOP.A4_6.existsImage_eq_Λ_bigUnion@cd08cc82
      // lean:AOP.A4_6.Λ_absorption@00399742
    (EQ, "Freyd.Alg.thinning_paths_alg.rhs",
      src[`F(∋,𝟙)F(𝟙,∋)=F(∋,∋)` \ #frc([`F(∋,∋)α`]) `= {raze x,/:\:y}`]),
      // lean:AOP.A8_2.thinning_paths_alg_bifunctors@19e61c12
      // lean:AOP.A5_5_TypeFunctor.BiRelator.interchange@cc0eb4af
  ),
  [#EQ #leanf("Freyd.Alg.cpMap_comp_powerRel_alphaR_comp_est_eq_junc") \ #src[at the layered network (`F(A,X)=A+A×X`, `B` the paths `V⁺`, `α=[wrap,cons]`): #frc([`F(𝟙,∋)`])` P(α) est(R)=[wrap,step]` — @path-defn]],
    // lean:AOP.A8_2.cpMap_comp_powerRel_alphaR_comp_est_eq_junc@7d981497
    // lean:AOP.A8_2.pathStep@f546a21f
  // No panel: `cpMap_sum_eq_junc` holds for EVERY pair of relators, and the exporter has no
  // naturality verdict for an `F` that is only a variable — it draws a red stub instead.
  [#EQ #src[#frc([`F(∋,𝟙)`])` =𝟙+cpl` — @path-defn]],
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

// Same reason as the hand-placed breaks in §@sec-opt: `sticky` cannot hold a heading to a BREAKABLE
// figure, so this heading stranded itself at the foot of the page.
#pagebreak(weak: true)
== Implementing thin

// B&dM §8.3, p. 199.  Lemma 8.1 is printed with `R` where its own proof and Theorem 8.2 write `P`;
// it is one connected preorder, spelled `≼` here.
#disp[#definition[
`setify : [A]⟶PA`, #h(4pt) `cup : PA×PA⟶PA`, #h(4pt) `cp(F)` #src[@comb-fns], #h(4pt)
`listcp : F(L)⟶LF`, #h(4pt) `sort(≼)≜setify° ordered(≼)` #src[]
// lean:AOP.A8_3.sortRel@0e1a3dba lean:AOP.A5_6_ListCombinators.ordered@76bb18c0 lean:AOP.A8_3.merge@536822df
for `≼` a connected preorder.

`thinlist(Q)` is any `thinlist(Q)⊑subseq` with #h(4pt) `thinlist(Q) setify⊑setify thin(Q)`; #h(4pt)
one is #h(4pt) `⦇[nil,bump Q]⦈`, #h(4pt) `bump Q (a,[])=[a]`, #h(4pt)
`bump Q (a,[b]⧺xs)=(b Q a→[a]⧺xs,a Q b→[b]⧺xs,[a]⧺[b]⧺xs)`.

*Binary thinning* data: #h(4pt) `S=(f₁p₁) ∪ (f₂p₂)` with `p₁`, `p₂` coreflexive; #h(4pt) `Q` a
preorder with `Q⊑R` and both `f₁p₁`, `f₂p₂` monotonic on `Q`; #h(4pt) `≼` a connected preorder
with both `f₁`, `f₂` monotonic on `≼`; #h(4pt) `gᵢ≜list(fᵢ) filter(pᵢ)`.
]]<thinlist-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`thinlist(Q) xs=[minlist(Q) xs]` \ #src[(8.5), `Q` connected, `xs` non-empty]],
  [what thinning should come to when it can: one element],
  [`sort(≼) thinlist(Q)⊑thin(Q) sort(≼)` #h(6pt) #src[(8.6) — @thinlist-86]],
  [thinning a sorted list is a thinning of the set — this is what `thinlist(Q)⊑subseq` buys],
  [`sort(≼) minlist(Q)⊑est(Q)` #h(6pt) #src[(8.7)]],
  [a minimum of the sorted list is a minimum of the set],
  [`sort(f≼f°) list(f)⊑P(f) sort(≼)` #h(6pt) #src[(8.8)]],
  [shunt a function through a sort],
  [`sort(≼) filter(p)⊑E(p) sort(≼)` #h(6pt) #src[(8.9), `p` coreflexive]],
  [filtering a sorted list sorts the restricted set],
  [`(sort(≼)×sort(≼)) merge(≼)⊑cup sort(≼)` #h(6pt) #src[(8.10)]],
  [merging two sorted lists sorts their union],
  [`F(sort(≼)) listcp⊑cp(F) sort(F(≼))` \ #src[(8.11), `F` linear]],
  [`listcp` is the list implementation of the cartesian product `cp(F)`],
  // lean:AOP.A8_3.sortRel_comp_thinlist_le@9b7ffbea lean:AOP.A8_3.sortRel_comp_le@53ffaf83 lean:AOP.A8_3.sortRel_comp_minlist_le@fbc36753 lean:AOP.A8_3.sortRel_comp_listMap_le@04773615 lean:AOP.A8_3.sortRel_comp_filter_le@a19a57e0 lean:AOP.A8_3.prodMap_sortRel_comp_merge_le@4178afbc lean:AOP.A8_3.map_sortRel_comp_listcp_le@7c091df5 lean:AOP.A8_3.sort_comp_thinlist_le@d576e387 lean:AOP.A8_3.sort_comp_filter_le@b35d850d lean:AOP.A8_3.prodMap_sort_comp_merge_le@904cb4a4 lean:AOP.A8_3.ordered_comp_subseq_le@3d670f97 lean:AOP.A8_3.prodMap_ordered_comp_merge_le@9cd186c6
)]<thinlist-laws>

// B&dM (8.6), p. 201, mirrored.  Row 3 is the content: `thinlist(Q)` only drops elements, and a
// subsequence of a `≼`-ordered list is `≼`-ordered, so the thinning may run before the sort.
// `setify°` is where the set becomes a list, so it is a NODE on the object wire — the `E` bends in,
// the `list` bends out — and the two coreflexive-shaped arrows are beads on the lane each acts on.
#disp(num: "(8.6)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.sortRel_comp_thinlist_le") \
    // sortRel row: (8.6), p. 201
    #src[a thinning of the sorted list lists a thinning of the set — `≼` a connected
 preorder, `thinlist(Q)⊑subseq`. ]],
     // lean:AOP.A8_3.sortRel_comp_thinlist_le@9b7ffbea
  lean-chain(
    // `sort(≼) : PA⟶[A]`, `ordered(≼)`,`thinlist(Q) : [A]⟶[A]` — @thinlist-defn's
    // `sort(≼)≜setify° ordered(≼)` at `setify : [A]⟶PA`.
    (none, "Freyd.Alg.sortRel_comp_thinlist_le_step1.lhs", []),
    (EQ, "Freyd.Alg.sortRel_comp_thinlist_le_step1.rhs", src[`sort(≼)≜setify° ordered(≼)` — @thinlist-defn]),
    (SQ, "Freyd.Alg.sortRel_comp_thinlist_le_step2.rhs",
      src[`ordered(≼) thinlist(Q)⊑thinlist(Q) ordered(≼)` — @thinlist-defn]),
    (SQ, "Freyd.Alg.sortRel_comp_thinlist_le_step3.rhs",
      src[`thinlist(Q) setify⊑setify thin(Q)` — @thinlist-defn, @dom-laws, @triple-chains]),
    (EQ, "Freyd.Alg.sortRel_comp_thinlist_le_step4.rhs", src[`sort(≼)≜setify° ordered(≼)` — @thinlist-defn]),
  ),
)]<thinlist-86>

// B&dM Lemma 8.1, p. 202, mirrored.  The chain walks the sort INWARDS, past `filter(p)`, then past
// `list(f)`, then under `F` — each step one of (8.9), (8.8), (8.11).
// `sort(≼) : PA⟶[A]` is where one datatype becomes another, and nothing survives outside it, so it
// is a NODE on the object wire — the `E` bends in, the `list` bends out — not a bead on a lane.
#disp(num: "Lemma 8.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.map_sort_comp_listcp_le") \
    #src[one sorted list built from sorted arguments, instead of a set built and then sorted —
     // map_sort row: Lemma 8.1, p. 202
     `f : FA⟶A` monotonic on `≼`, `p` coreflexive, `F` linear.
 ]],
  lean-chain(Sub("Freyd.Alg.map_sort_comp_listcp_le_steps4to6",
    gloss: src[sorting the `f`-images of the product and filtering by `p` is below sorting the set `F(∋)fp` builds],
     // lean:AOP.A8_3.map_sort_comp_listcp_le_steps4to6@32a5d6f6
    (none, "Freyd.Alg.map_sort_comp_listcp_le.rhs", []),
    (EQ, "Freyd.Alg.map_sort_comp_listcp_le_step6.lhs",
      src[#frc([`F(∋)fp`])` =`#frc([`F(∋)`])` E(fp)` — @pow-laws, @thinlist-defn]),
    (EQ, "Freyd.Alg.map_sort_comp_listcp_le_step5.lhs",
      src[`E(f)=P(f)`, `f` a map — @powrel-laws]),
    // The node has walked up past `p`, which comes out the other side as `filter(p)` on the `list`
    // lane: the same coreflexive, applied to the sorted list instead of to the set.
    // `filter(p) : [A]⟶[A]` — @thinlist-defn's `gᵢ≜list(fᵢ) filter(pᵢ)`.
    (RQ, "Freyd.Alg.map_sort_comp_listcp_le_step4.lhs", src[`sort(≼) filter(p)⊑E(p) sort(≼)` — @thinlist-laws]),
  ), Sub("Freyd.Alg.map_sort_comp_listcp_le_steps1to3",
    gloss: src[combining the arguments' sorted lists by `listcp`, mapping `f` and filtering is below sorting the `f`-images and filtering],
     // lean:AOP.A8_3.map_sort_comp_listcp_le_steps1to3@fb9f18b9
    (RQ, "Freyd.Alg.map_sort_comp_listcp_le_step3.lhs",
      src[`sort(f≼f°) list(f)⊑P(f) sort(≼)` — @thinlist-laws]),
    (RQ, "Freyd.Alg.map_sort_comp_listcp_le_step2.lhs",
      src[`F(≼)⊑f≼f°` — @mon-str, @thinlist-defn]),
    (RQ, "Freyd.Alg.map_sort_comp_listcp_le.lhs",
      src[`F(sort(≼)) listcp⊑cp(F) sort(F(≼))` — @thinlist-laws]),
  )),
)]<thinlist-lem81>

// B&dM Theorem 8.2, p. 203, mirrored.  The candidate SET of the thinning theorem becomes a sorted
// LIST, and that swap — `E` killed by `est(R)`, `list` by `minlist(R)` — is what rows 3 and 4 draw.
#disp(num: "Theorem 8.2")[#calc-table(
  Thm[#leanf("Freyd.Alg.thinningList") \
    #src[a fold on sorted lists of partial solutions, thinned at every step —
     // thinningList row: Theorem 8.2, p. 203
     at @thinlist-defn's binary thinning data.
 ]],
     // lean:AOP.A8_3.thinningList@8637feb9
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.thinningList_step3.rhs"), [])],
  [#lean("Freyd.Alg.thinningList_step3.rhs", step: true)],

  [#vstep(RQ, leanc("Freyd.Alg.thinningList_step3.lhs"),
    [#src[@thin-cor at `f₁p₁` and `f₂p₂` monotonic on `Q` — @thinlist-defn]])],
  [#lean("Freyd.Alg.thinningList_step3.lhs", step: true)],

  [#vstep(RQ, leanc("Freyd.Alg.thinningList_step2.lhs"),
    [#src[`sort(≼) minlist(R)⊑est(R)` — @thinlist-laws at its `Q≜R`]])],
  // `est(R)` has split into the node that sorts and the `minlist(R)` that reads the head back.
  // `minlist(R) : [A]⟶A` — @thinlist-laws' (8.5) `thinlist(Q) xs=[minlist(Q) xs]`.
  [#lean("Freyd.Alg.thinningList_step2.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.thinningList_step1.lhs"),
    [#src[@cata-fusion at @thinlist-fusion]])],
  // The reduce now births `list` where it births `E` above: no set is ever built.
  [#lean("Freyd.Alg.thinningList_step1.lhs")],
)]<thinlist-thm82>

// The fusion condition of the last step above, B&dM p. 203.  Two of its moves are unwritten there:
// the product law that distributes `sort(≼)×sort(≼)` over the fork, and the fork law that closes it.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.sortedAlg_fusion") \
    #src[sorting the candidate set is what turns the thinning algebra into an algebra on lists —
     // sortedAlg-fusion row: B&dM p. 203
     the side condition of @thinlist-thm82's last step.
 ]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.sortedAlg_fusion.rhs"), [])],
  [#lean("Freyd.Alg.sortedAlg_fusion.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.sortedAlg_fusion_step5.lhs"),
    [#src[`sort(≼) thinlist(Q)⊑thin(Q) sort(≼)` — @thinlist-laws]])],
  // The node has walked up past `thin(Q)`, which comes out below it as `thinlist(Q)` on the `list`
  // lane: that exchange is the whole of (8.6), and the rest of the chain rewrites the algebra.
  [#lean("Freyd.Alg.sortedAlg_fusion_step5.lhs")],

  [#vstep(EQ, leanc("Freyd.Alg.sortedAlg_fusion_step4.lhs"),
    [`⟨`#frc([`F(∋)f₁p₁`])`,`#frc([`F(∋)f₂p₂`])`⟩ cup sort(≼) thinlist(Q)` \
     #src[`S=(f₁p₁) ∪ (f₂p₂)` — @thinlist-defn, then @cup-defn]])],
  // Empty from here: a fork is an operation on hom-sets, and `×` is a bifunctor, so neither is a
  // wiring; the circuit column keeps them as one box, §14's convention for a pair.
  [],

  [#vstep(RQ, leanc("Freyd.Alg.sortedAlg_fusion_step3.lhs"),
    [`⟨`#frc([`F(∋)f₁p₁`])`,`#frc([`F(∋)f₂p₂`])`⟩(sort(≼)×sort(≼)) merge(≼) thinlist(Q)` \
     #src[`(sort(≼)×sort(≼)) merge(≼)⊑cup sort(≼)` — @thinlist-laws]])],
  [],

  [#vstep(EQ, leanc("Freyd.Alg.sortedAlg_fusion_step2.lhs"),
    [`⟨`#frc([`F(∋)f₁p₁`])` sort(≼),`#frc([`F(∋)f₂p₂`])` sort(≼)⟩ merge(≼) thinlist(Q)` \
     #src[`⟨X,Y⟩(sort(≼)×sort(≼))=⟨X sort(≼),Y sort(≼)⟩` — @bdm-prod-laws]])],
  [],

  [#vstep(RQ, leanc("Freyd.Alg.sortedAlg_fusion.lhs"),
    [`F(sort(≼)) listcp ⟨g₁,g₂⟩ merge(≼) thinlist(Q)` \
     #src[@thinlist-lem81 at `f₁`, `p₁` and at `f₂`, `p₂`, then
      `X⟨g₁,g₂⟩⊑⟨Xg₁,Xg₂⟩` — @bdm-prod-laws; `gᵢ≜list(fᵢ) filter(pᵢ)` — @thinlist-defn]])],
  [],
)]<thinlist-fusion>

== The knapsack problem

// B&dM §8.4, p. 205.  The printed base of the final fold is `nil`, without the outer `wrap` that
// §8.5 and §8.6 do print (`wrap wrap wrap`, `start wrap`).
#disp[#definition[
`vol,wt : Item⟶Real`, #h(4pt) `value≜list(vol) sum`, #h(4pt) `weight≜list(wt) sum`
#src[].
// lean:AOP.A5_6_ListCombinators.total_eq@2b26e4d0

`subseq=⦇[nil,cons] ∪ [nil,π₂]⦈` #src[,
// lean:AOP.A8_4_Knapsack.con_eq_junc@f6f12bd6
], #h(4pt) `within w` the coreflexive on `xs` with
// lean:AOP.A8_4_Knapsack.drop_eq_junc@1f5b4c77
`weight xs≤w`, #h(4pt) `0≤w`.

`R≜value≥value°` #src[], #h(4pt)
// lean:AOP.A8_4_Knapsack.R_eq@1c13d35d
`Q≜R∩(weight≤weight°)` #src[], #h(4pt)
// lean:AOP.A8_4_Knapsack.Q_eq@22acbe51
`P≜R` #src[,
// lean:AOP.A8_4_Knapsack.knap_sort_cons@dce0f4b3
].
// lean:AOP.A8_4_Knapsack.knap_sort_drop@23381fc8

`FA=1+Item×A`, #h(4pt) `listcp=wrap+cpr`, #h(4pt) `g₁≜list([nil,cons]) filter(within w)`
#h(4pt) `=[list(nil),h₁]`, #h(4pt) `g₂≜list([nil,π₂])=[list(nil),h₂]`.

`h₁≜list(cons) filter(within w)`, #h(4pt) `h₂≜list(π₂)`.
]]<knap-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) (cons (within w))⊑cons (within w)R` \ #src[FALSE]],
  [not monotonic on `R`: a selection of greater value need not still fit once one more item goes in],
  [`(𝟙×Q) (cons (within w))⊑cons (within w)Q` \ `(𝟙×Q)π₂⊑π₂Q`
 #src[,
   // lean:AOP.A8_4_Knapsack.knap_mono_cons@d44e5999
 ]],
   // lean:AOP.A8_4_Knapsack.knap_mono_drop@fce8ac80
  [both halves are monotonic on `Q` once ties in value are broken by weight],
)]<knap-mono>

// B&dM §8.4, p. 206.  The set the transpose opens becomes a LIST at the binary thinning step, and
// that swap — `E` killed by `est(R)`, `list` killed by `minlist(R)` — is what the right column draws.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Knapsack.knap_laws") \
    // knapsack row: B&dM §8.4, p. 206
    #src[the knapsack problem, as a fold that thins the packings kept at each item]],
     // lean:AOP.A8_4_Knapsack.knap_laws@12891aa4
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.rhs"),
    [#frc([`subseq (within w)`])` est(R)`])],
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.lhs"),
    [#frc([`⦇[nil,cons](within w) ∪ [nil,π₂]⦈`])` est(R)` \
 #src[@cata-fusion, weights non-negative. ]])],
     // lean:AOP.A8_4_Knapsack.knap_spec@89359e6f
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.lhs", step: true)],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step1.lhs"),
    [`⦇listcp ⟨g₁,g₂⟩ merge R thinlist(Q)⦈ minlist(R)` \
     #src[@thinlist-thm82, at `P≜R`, `F` linear, `Q` from @knap-mono]])],
  // The candidate set is now a candidate LIST: the reduce births `list` where it births `E` above.
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step1.lhs")],

  [#vstep(EQ, [],
    [`⦇[nil,cpr ⟨h₁,h₂⟩ merge R thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ=[list(nil),hᵢ]` — @knap-defn; `minlist(R)` is `head`, packings
      coming out in descending value]])],
  [],
)]<knap-laws>

// Stranded at the foot of its page for the same reason as the break above.
#pagebreak(weak: true)
== The paragraph problem

// B&dM §8.5, p. 207.  `P ≜ ⊤` works because `merge ⊤ = cat`, which already brings equal first lines
// together; the book's first choice `head prefix head°` is correct but not needed.
#disp[#definition[
`Line=list⁺ Word`, #h(4pt) `Para=list⁺ Line`, #h(4pt) `FA=Word+Word×A`, #h(4pt)
`listcp=wrap+cpr`.

`new(a,xs)=[[a]]⧺xs`, #h(4pt) `glue(a,xs)=[[a]⧺head(xs)]⧺tail(xs)`, #h(4pt)
`partition≜⦇[wrap wrap,new ∪ glue]⦈ : list⁺ Word⟶Para`.

`width≜⦇[length,(length×𝟙) plus succ]⦈`, #h(4pt) `0≤length a`, #h(4pt) `fits w` the coreflexive on a
line `x` with `width x≤w`, #h(4pt) `ok w` the coreflexive on `[x]⧺xs` with `width x≤w`.

`white w x=w−width x`, #h(4pt) `collect≜list(sqr) sum`, #h(4pt) `waste w≜init list(white w) collect`.

`R≜(waste w)≤(waste w)°` #src[], #h(4pt)
// lean:AOP.A8_5_Paragraph.R_eq@cf0ea074
`Q≜R∩(head head°)` #src[], #h(4pt)
// lean:AOP.A8_5_Paragraph.Q_eq@a6330fbf
`P≜⊤` #src[,
// lean:AOP.A8_5_Paragraph.para_sort_new@79ca91ea
].
// lean:AOP.A8_5_Paragraph.para_sort_glue@01887a30

`g₁≜list([wrap wrap,new])`, #h(4pt) `g₂≜list([wrap wrap,glue]) filter(ok w)`, #h(4pt)
`start≜wrap wrap wrap`, #h(4pt) `h₁≜list(new)`, #h(4pt) `h₂≜list(glue) filter(ok w)`.
]]<para-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) glue⊑glue R` #h(6pt) #src[FALSE]],
  [`glue` is not monotonic on `R`: the waste of a paragraph depends on its whole first line, so no
   greedy algorithm solves this],
  [`(𝟙×Q) new⊑new Q` \ `(𝟙×Q) (glue (ok w))⊑glue (ok w)Q` \ #src[`cons` monotonic on
 `collect≤collect°`. ,
   // lean:AOP.A8_5_Paragraph.para_mono_new@7bd0f665
 ]],
   // lean:AOP.A8_5_Paragraph.para_mono_glue@d88580bd
  [both halves are monotonic on `Q` once ties in waste are broken by the first line],
  [`merge ⊤=cat`; #h(4pt) `P≜head prefix head°` also serves],
  [`⊤` needs no sorting at all, and `prefix` is a linear order on first lines of paragraphs of one
   input],
)]<para-mono>

// B&dM §8.5, p. 210.  `partition` turns ONE list into two — the paragraph and its lines — so it is a
// bead on the object wire with three list wires at it, and the candidate set is a fourth.
// The source is ONE `list⁺`; `partition` births the paragraph's, and the reduce of the last two rows
// births a third — the list of candidate paragraphs `minlist(R)` reads back down.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Paragraph.para_laws") \
    // paragraph row: B&dM §8.5, p. 210
    #src[a paragraph laid out as a fold that thins the layouts kept at each word]],
     // lean:AOP.A8_5_Paragraph.para_laws@58149d9d
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step2.rhs"),
    [#frc([`partition list⁺(fits w)`])` est(R)`])],
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step2.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step2.lhs"),
    [#frc([`⦇[wrap wrap,new ∪ (glue (ok w))]⦈`])` est(R)` \
     #src[@cata-fusion, every word fits on a line by itself.
 ]])],
     // lean:AOP.A8_5_Paragraph.para_alg_fusion@031c245f
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step2.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Paragraph.para_laws_split.rhs"),
    [#frc([`⦇[wrap wrap,new] ∪ ([wrap wrap,glue] (ok w))⦈`])` est(R)` \
     #src[the algebra as `(f₁p₁) ∪ (f₂p₂)`, `p₁≜𝟙` — @thinlist-defn.
 ]])],
     // lean:AOP.A8_5_Paragraph.para_spec@0ec1a795
  // Empty: the step renames the algebra and the panel above already draws the reduce.
  [],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step1.lhs"),
    [`⦇listcp ⟨g₁,g₂⟩ cat thinlist(Q)⦈ minlist(R)` \
     #src[@thinlist-thm82, at `P≜⊤` with `merge ⊤=cat`, `Q` from @para-mono]])],
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step1.lhs")],

  [#vstep(EQ, [],
    [`⦇[start,cpr ⟨h₁,h₂⟩ cat thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ` along the coproduct — @para-defn]])],
  [],
)]<para-laws>

== Bitonic tours

// B&dM §8.6, p. 212.  `Q` keeps the `head2` conjunct p.215 derives and then drops on the grounds
// that tours of one input share their heads: without it the two `tour-mono` rows are false.
#disp[#definition[
`FA=(City×City)+(City×A)`, the base functor of cons-lists of length at least two; #h(4pt)
`listcp=wrap+cpr`; #h(4pt) `tc : City×City⟶Real`, neither positive nor symmetric.

`start (a,b)=([a,b],[a,b])`, #h(4pt) `dropl (a,([b]⧺xs,ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt)
`dropr (a,(xs,[b]⧺ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt) `tour≜⦇[start,dropl ∪ dropr]⦈`.

`cost (xs,ys)=outcost xs+incost ys`, #h(4pt) `outcost [a₀,…,aₙ]=tc (a₀,a₁)+⋯+tc (aₙ₋₁,aₙ)`,
#h(4pt) `incost [a₀,…,aₙ]=tc (a₁,a₀)+⋯+tc (aₙ,aₙ₋₁)`.

`next≜tail head`, #h(4pt) `next2≜next×next`, #h(4pt) `head2≜head×head`, #h(4pt) `R≜cost≤cost°`
#src[], #h(4pt)
// lean:AOP.A8_6_Tour.R_eq@15ad4adc
`Q≜R∩(next2 next2°)∩(head2 head2°)`, #h(4pt) `P≜⊤` #src[,
// lean:AOP.A8_6_Tour.tour_sort_dropl@0dc4ff40
], #h(4pt) `g₁≜list([start,dropl])`, #h(4pt)
// lean:AOP.A8_6_Tour.tour_sort_dropr@f9356ac3
`g₂≜list([start,dropr])`.
]]<tour-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) dropl⊑dropl R` #h(6pt) #src[FALSE] \ `(𝟙×R) dropr⊑dropr R` #h(6pt) #src[FALSE]],
  [neither drop is monotonic on `R`: the two edges it adds and removes depend on `head` and `next`
   of both lists],
  [`(𝟙×Q) dropl⊑dropl Q` \ `(𝟙×Q) dropr⊑dropr Q`
 #src[,
   // lean:AOP.A8_6_Tour.tour_mono_dropl@a80a947d
 ]],
   // lean:AOP.A8_6_Tour.tour_mono_dropr@327889aa
  [both are, once ties in cost are broken by the two second cities — the heads already agree among
   tours of one input],
)]<tour-mono>

// B&dM §8.6, p. 215.  A tour is a PAIR of lists, so `[City]×[City]` is the one unary functor
// `X↦[X]×[X]` — a bifunctor is never a wire, and this one is partially applied before it is drawn.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Tour.tour_laws") \
    // tour row: B&dM §8.6, p. 215
    #src[a least-cost bitonic tour, as a fold that thins the tours kept at each city]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Tour.tour_laws.rhs"), [#frc([`tour`])` est(R)`])],
  [#lean("Freyd.Alg.RelSet.Tour.tour_laws.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Tour.tour_laws_defn.rhs"),
    [#frc([`⦇[start,dropl ∪ dropr]⦈`])` est(R)` \ #src[`tour≜⦇[start,dropl ∪ dropr]⦈` — @tour-defn]])],
  // Empty: the step only names the reduce, and the panel above already draws it.
  [],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Tour.tour_laws.lhs"),
    [`⦇listcp ⟨g₁,g₂⟩ cat thinlist(Q)⦈ minlist(R)` \
     #src[@thinlist-thm82, at `P≜⊤` with `merge ⊤=cat`, `Q` from @tour-mono]])],
  [#lean("Freyd.Alg.RelSet.Tour.tour_laws.lhs", step: true)],

  [#vstep(EQ, [],
    [`⦇[start wrap,cpr ⟨list(dropl),list(dropr)⟩ cat thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ=[list(start),list(dropᵢ)]` — @tour-defn; quadratic, two tours
      added per step]])],
  [],
)]<tour-laws>

#pagebreak(weak: true)
