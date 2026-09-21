#import "../note-prelude.typ": *
#show: note-chapter.with(12)
// note-split: chapter 12 — this header is written by scripts/note-split and stripped by scripts/note-join
= Combinatorial functions <sec-comb>

// B&dM §5.6, p. 125, plus the three specifications of Ex 7.39–7.41 (p. 174).  Every composite is
// mirrored to diagram order, so B&dM's `prefix · suffix` is `suffix prefix` here.
#disp[#table(
  columns: (7.1cm, 2.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

  [`[A]::=nil|cons(A,[A])`],
  [`𝒜⟶𝒜`],
  // list type note: B&dM's `listr`, renamed here from p. 125 on
  [The list type, under the short name it keeps.],

 [`list(R)≜⦇[nil,(R⊗𝟙) cons]⦈` #src[]],
  // lean:AOP.A5_6_ListCombinators.list_cata@83b2fcc6
  [#leant("Freyd.Alg.RelSet.ListRel.list_cata")],
  [The relator's action on `R : A⟶B`: one `R` per element, the shape untouched.],

 [`subseq≜⦇[nil,cons ∪ π₂]⦈` #src[]],
  // lean:AOP.A5_6_ListCombinators.subseq_cata@97265f47
  [#leant("Freyd.Alg.RelSet.ListRel.subseq_cata")],
  [`xs subseq ys`: `ys` is `xs` with elements dropped — `cons` keeps the head, `π₂` drops it.],

  [`prefix≜⦇[nil,nil ∪ cons]⦈` \
 `=cat° π₁=init*` #src[]],
   // lean:AOP.A5_6_ListCombinators.prefix_cata@b8d861c4 lean:AOP.A5_6_ListCombinators.prefix_cat@eb19c936
  [#leant("Freyd.Alg.RelSet.ListRel.prefix_cata")],
  [`ys` is an initial segment of `xs`; the first `nil` is where it stops early. `init≜snoc° π₁`.],

 [`suffix≜cat° π₂=tail*` #src[]],
  // lean:AOP.A5_6_ListCombinators.suffix_cat@c70cd49e
  [#leant("Freyd.Alg.RelSet.ListRel.suffix_cat")],
  [The dual, `tail≜cons° π₂`; as a reduce it needs snoc-lists.],

 [`segment≜suffix prefix` #src[]],
  // lean:AOP.A5_6_ListCombinators.segment_eq@db9aa91a
  [#leant("Freyd.Alg.RelSet.ListRel.segment_eq")],
  [A contiguous stretch of `xs`: a suffix, then a prefix of that.],

 [`partition≜concat°` #src[]],
  // lean:AOP.A5_6_ListCombinators.partition_concat@f9c15a2e
  [`[A]⟶[[A]⁺]`],
  [This `cat` is restricted to `[A]⁺×[A]⟶[A]`, so `ys` is a list of non-empty segments of `xs`.],

 [`concat≜⦇[nil,cat]⦈` #src[]],
  // lean:AOP.A5_6_ListCombinators.concat_cata@7345ecd3
  [#leant("Freyd.Alg.RelSet.ListRel.concat_cata")],
  [Joins the segments back up, which is why its converse splits a list.],

  [`inits`],
  [`[A]⟶[[A]]`],
  [Implements $frac(#[`prefix`], ∋)$, listing the prefixes by increasing length.],

  [`tails`],
  [`[A]⟶[[A]]`],
  [Implements $frac(#[`suffix`], ∋)$ by decreasing length — the opposite order.],

  [`filter(p)≜` $frac(#[`subseq list(p)`], ∋)$ `est(R°)`],
  [#leant("Freyd.Alg.RelSet.Filter.filter")],
  [The longest subsequence of `xs` whose every element passes `p`.
   // filter row: Ex 7.41
   #h(4pt) #src[`est(R°)` is @est-defn]],

  [`R≜length≤length°`],
  [#leant("Freyd.Alg.RelSet.GCTakeWhile.lenLE")],
  [The preorder `filter` and `takewhile` maximise over: the longer list wins.
   #h(4pt) #src[`≥≜≤°`]],

  [`takewhile(p)≜` $frac(#[`prefix list(p)`], ∋)$ `est(R°)`],
  [#leant("Freyd.Alg.RelSet.GCTakeWhile.takewhile")],
  [The same with `prefix` for `subseq`: the longest prefix whose every element passes `p`.
   // takewhile row: Ex 7.39
   #h(4pt) #src[]],

  [`mss≜` $frac(#[`segment sum`], ∋)$ `est(≥)`],
  [#leant("Freyd.Alg.RelSet.MSS.mss")],
  [Maximum segment sum. `segment=suffix prefix` splits it into $frac(#[`prefix sum`], ∋)$ `est(≥)`
   // mss row: Ex 7.40
   on each suffix. #h(4pt) #src[]],
)]<comb-fns>

== $frac(#[`subseq`], ∋)$ `=⦇[nil` $frac(#[`𝟙`], ∋)$`,⟨`$frac(#[`𝟙×∋`], ∋)$` E(cons),π₂⟩ cup]⦈`

// B&dM §5.6, p. 124: @cata-map-calc run at `subseq`'s algebra `[nil, cons ∪ π₂]`, which is what
// turns the relation into a program.  `cup` is needed first — nothing above this note has a binary union.
#disp[#definition[
`cup≜` $frac(#[`π₁∋ ∪ π₂∋`], ∋)$ ` : EA×EA⟶EA`, #h(4pt) so
$frac(#[`R ∪ S`], ∋)$ `=⟨`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`⟩ cup`.
#h(4pt) #src[]
// lean:AOP.A5_6.Λ_union@632cc56a
]]<cup-defn>

// The `∪`'s `cons` operand, drawn Hinze–Marsden: `𝟙×∋` acts on the TAIL, so `∋` is a bead on the
// object wire and `cons` is where the `A×−` wire ends on it.  Emitted verbatim by `./scripts/diagram`;
// `sb-hm-born` adds the `E` the transpose opens.
#let sb-hm = lean("Freyd.Alg.RelSet.ListRel.prod_ni_union_dist.rhs", branch: "inl")
#let sb-hm-born = lean("Freyd.Alg.RelSet.ListRel.Λ_prod_ni_cons.lhs")
// @subseq-EW-case draws the `π₂` operand of `cons ∪ π₂` in every row, never `cons`: the derivation
// rewrites only `π₂` (@subseq-outr-square, then `∋%∋=𝟙`); `(𝟙×∋)cons` stays as `sb-hm` draws it.
// Recipe for a union's lower operand: the `cert:` is the formula with the `∪` cut to that operand
// by hand (`rank` in `scripts/diagram` would pick the other), and the cell's `#src` names it.
#let sb-hm-p2 = lean("Freyd.Alg.RelSet.ListRel.Λ_prod_ni_proj.lhs")
// @subseq-EW-join's `π₂` operand at three steps, each the `∪` cut to `π₂` by hand (`rank` would pick
// `cons`): after the distribution, after @relprod-pic slides the `∋` past `π₂`, and bare at the end.
#let sb-hm-p2-slid = lean("Freyd.Alg.RelSet.ListRel.prod_ni_union_slide.rhs", branch: "inr")
#let sb-hm-p2-bare = lean("Freyd.Alg.RelSet.ListRel.Λ_proj_ni.rhs")

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.ListRel.subseq_alg_Λ") \
    #src[the set of lists the algebra builds is, from nothing, just `nil`, and from a head and a set
     of tails, every tail in the set with the head put on or left off — @cata-map-calc at
     `subseq=⦇[nil,cons ∪ π₂]⦈`, @comb-fns.
 ]],
    // lean:AOP.A5_6_ListCombinators.subseq_alg_Λ@d73bdb8e lean:AOP.A5_6_ListCombinators.subseq_cata@97265f47
  table.header([*circuit* — the fork is `F([A])=𝟏+A×[A]`: `nil` above, the pair below],
    [*Hinze–Marsden*]),

  // THE TWO COLUMNS ARE NOT ONE THEOREM PER ROW HERE, and that is deliberate: the circuit column
  // rewrites the WHOLE term step by step, where the Hinze–Marsden column stays on the one operand
  // `(𝟙×∋)π₂` the steps do not touch — which is why one selector repeats down three rows.  The
  // general rule is the other way round (AGENTS.md); §12.1 is its exception and stays as it is.
  // Rows 1–3 draw the NUMERATOR, `F(E[A]) ⟶ [A]`: the transpose is still outside the bracket there,
  // and the generator fuses `F(∋)[f,g]` into the one tape `[f,(𝟙×∋)g]` on trust (CIRCUIT-GEN §1.4).
  [#vstep([], leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.lhs"), [#frc([`F(∋)[nil,cons ∪ π₂]`])])],
  [#lean("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.rhs", branch: "inr.inr") \ #src[the `π₂` operand of `cons ∪ π₂` under the `𝟙×∋` summand of `F(∋)`, i.e. `(𝟙×∋)π₂`]],

  // The sum `𝟙+𝟙×∋` and the bracket after it fuse into the one tape, `(R+S)[f,g]=[Rf,Sg]`.
  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_map.lhs"),
    [#frc([`(𝟙+𝟙×∋)[nil,cons ∪ π₂]`]) \ #src[`F(X)=𝟏+A×X` — @comb-fns]])],
    // lean:AOP.A5_6_ListCombinators.subseq_alg_sum_map@73aaa858 lean:AOP.A6_ConsList.F_eq_sum_prod@cab297e7
  [#lean("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.rhs", branch: "inr.inr") \ #src[the same operand under `𝟙+𝟙×∋`, whose `𝟙×∋` summand it sits in]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.rhs"), [#frc([`[nil,(𝟙×∋)(cons ∪ π₂)]`]) \
    #src[`R+S≜[Rl,Sr]`, `l[R,S]=R`, `r[R,S]=S` — @coprod-laws]])],
  [#lean("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.rhs", branch: "inr.inr") \ #src[the `π₂` operand of the second arm `(𝟙×∋)(cons ∪ π₂)`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_Λ_junc.rhs"), [`[`#frc([`nil`])`,`#frc([`(𝟙×∋)(cons ∪ π₂)`])`]` \
    #src[@coprod-calc at `T:=[nil,(𝟙×∋)(cons ∪ π₂)]`]])],
    // lean:AOP.A5_3.Λ_junc@d392c2aa
  [#sb-hm-p2 \ #src[the `π₂` operand under its `𝟙%∋`, the arm @subseq-outr-square's square rewrites,
    `(𝟙×∋)π₂=π₂∋`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_Λ_nil.rhs"), [`[nil `#frc([`𝟙`])`,`#frc([`(𝟙×∋)(cons ∪ π₂)`])`]` \
    #src[@pow-laws, #frc([`f`])` =f `#frc([`𝟙`]) for `f` a map, at `f:=nil`]])],
    // lean:AOP.A5_6_ListCombinators.Λ_nil_singleton@99c153ab
  [#sb-hm-p2 \ #src[the same operand; the two rows differ only in the `nil` arm]],
)]<subseq-EW-case>

// @relprod-pic's square at `R × S := 𝟙 × ∋`, on @cata-defining's 5.2 × 2.7 geometry.  The two `π₂`
// sit on OPPOSITE sides — one name, one colour, two rows, which is what the string picture cannot show.
#disp[#leancd("Freyd.Alg.RelSet.ListRel.prod_ni_proj_slide")]<subseq-outr-square>

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.ListRel.subseq_alg_join") \
    #src[power transpose of join: the power transpose of the join of two relations is
     `⟨`#frc([`R`])`,`#frc([`S`])`⟩ cup`, where `cup` is the function that returns the union of two sets]],
    // lean:AOP.A5_6_ListCombinators.subseq_alg_join@3a6f03a8
  table.header([*circuit*],
    [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.ListRel.prod_ni_union_dist.lhs"),
    [#frc([`(𝟙×∋)(cons ∪ π₂)`]) \ #src[@subseq-EW-case's second branch]])],
  [#sb-hm \ #src[the `cons` operand of `cons ∪ π₂`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.prod_ni_union_dist.rhs"),
    [#frc([`(𝟙×∋)cons ∪ (𝟙×∋)π₂`]) \ #src[`T(X₁ ∪ X₂)=TX₁ ∪ TX₂` — @adj-cross]])],
  [#lean("Freyd.Alg.RelSet.ListRel.prod_ni_union_dist.rhs", branch: "inr") \ #src[the `π₂` operand of `(𝟙×∋)cons ∪ (𝟙×∋)π₂`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.prod_ni_union_slide.rhs"),
    [#frc([`(𝟙×∋)cons ∪ π₂∋`]) \
    #src[`(𝟙×∋)π₂=π₂∋` — @relprod-pic at `π₂`, an equality because `𝟙` is entire]])],
    // lean:AOP.A5_6_ListCombinators.prod_ni_proj_slide@d3755d54
  [#sb-hm-p2-slid \ #src[the `π₂` operand of `(𝟙×∋)cons ∪ π₂∋`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.Λ_prod_ni_union.rhs"), [`⟨`#frc([`(𝟙×∋)cons`])`,`#frc([`π₂∋`])`⟩ cup` \
    #src[#frc([`R ∪ S`])` =⟨`#frc([`R`])`,`#frc([`S`])`⟩ cup` — @cup-defn]])],
  [#sb-hm-born \ #src[the `cons` operand under its `𝟙%∋`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_join.rhs"), [`⟨`#frc([`𝟙×∋`])` E(cons),π₂⟩ cup` \
    #src[@pow-laws, absorption #frc([`S`])` E(R)=`#frc([`SR`]) at `S:=𝟙×∋`, `R:=cons`; fusion and
     #frc([`∋`])` =𝟙` on the `π₂` operand]])],
  [#sb-hm-p2-bare \ #src[the `π₂` operand, bare `π₂`]],
)]<subseq-EW-join>

// @coprod-laws' picture at this algebra, so the banana's contents are read off the tape: the fork is
// the coproduct, and every box inside it but the two injections is a MAP — `chamfer: false`.
#disp[#leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_transpose.rhs")
#align(center, block(inset: (y: 4pt))[
  `[`#frc([`nil`])`,⟨`#frc([`𝟙×∋`])` E(cons),π₂⟩ cup]` \
  #src[which writes `Pcons`; `cons` is a map, and there `P(cons)=E(cons)` — @powrel-laws.]
])]<subseq-alg>

#pagebreak(weak: true)
