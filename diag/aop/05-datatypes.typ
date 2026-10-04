#import "../note-prelude.typ": *
#show: note-chapter.with(5)
// note-split: chapter 5 — this header is written by scripts/note-split and stripped by scripts/note-join
= Datatypes in Allegories

== Relators

#disp[#definition[
Every hom-set of an allegory is a poset, so an allegory is a *locally posetal 2-category*: the 2-cell
from `R` to `S` IS `R⊑S`. A *relator* `F : 𝒞⟶𝓓` is a 2-functor between allegories:

  #align(center, block(inset: (y: 6pt))[
 #text(12.5pt)[`F(𝟙)=𝟙` #src[] #h(1cm)
    // lean:Freyd.S1_18.map_id@1cd85d8e
 `F(RS)=F(R)F(S)` #src[] #h(1cm)
    // lean:Freyd.S1_18.map_comp@ab212d4e
 #leanf("Freyd.Alg.Relator.map_mono") #src[]]
  ])

Preserving `°` is *not* asked for — `°` is an identity-on-objects involution `𝒞ᵒᵖ⟶𝒞`, no part of
the 2-category.
]]<relator-defn>

#disp[#table(
  columns: (1fr,),
  align: (left + horizon,),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the statement*]),

 // F(f) map preserving row: Lemma 5.1
 [#leanf("Freyd.Alg.Relator.map_is_map") and #leanf("Freyd.Alg.Relator.map_recip_map"). #src[Lemma 5.1]],
  // lean:AOP.A5_1.map_is_map@8f150beb lean:AOP.A5_1.map_recip_map@c9f5d6f2
  // functor-is-relator row: Theorem 5.1
  [Over a *tabular* allegory a functor is a relator `⟺` it preserves `°`. #src[Theorem 5.1]
    #src[the book's reverse direction (preserving `°` ⟹ relator) needs the source to be `Rel`: the
    counterexample over a tabular allegory that is not `Rel` shows it can fail]],
  // lean:AOP.A5_1_Converse.map_mono_of_preservesRecip_relSet@9b4c46b5
  // lean:AOP.A5_1.preservesRecip_of_tabular@02b327b3
  // lean:AOP.A5_1_Converse.thm5_1_fails_for_tabular@e3406781
  // F(R°)=F(R)° row: after Theorem 5.1, p. 113
  [`F(R°)=F(R)°` for every `R`, so `F(R)°` needs no bracket.],
  // relators-agree-on-maps row: Corollary 5.1
  [Two relators agreeing on maps are equal. #src[Corollary 5.1]],
 // F(X∩Y) row: Ex 5.2
 [#leanf("Freyd.Alg.Relator.map_inter_coreflexive") #src[Ex 5.2]],
  // lean:AOP.A5_1.map_inter_coreflexive@a2233804
 // F(R∩S) row: Ex 5.2, the restriction
 [#leanf("Freyd.Alg.Relator.map_inter_le"), and strictly. #src[Ex 5.2]],
  // lean:AOP.A5_1.map_inter_le@af565f80
 [#leanf("Freyd.Alg.Relator.map_dom") #src[Ex 5.5]],
  // lean:AOP.A5_1.map_dom@5e9ecd68
)]<relator-laws>

The *power relator* `P` — `xs P(R) ys⟺(∀a∈xs. ∃b∈ys. a R b)∧(∀b∈ys. ∃a∈xs. a R b)` — is where
the fourth is strict: for `R={(a₁,b₁),(a₂,b₂)}` and `S={(a₁,b₂),(a₂,b₁)}` the pair
`({a₁,a₂},{b₁,b₂})` is in `P(R)∩P(S)`, while `R∩S=∅`.

== Relational products

#disp(num: "(5.1)")[#definition[
The *fork* of `R : C⟶A` and `S : C⟶B` is `⟨R,S⟩≜Rπ₁°∩Sπ₂°` #src[],
// lean:AOP.A5_2.Freyd.Alg.RelProd.pair@df1791ca
where `(π₁,π₂)` is the tabulation of `⊤`
#src[].
// lean:AOP.A5_2.eq_topMor@31e6622f lean:AOP.A5_2.joint_id@f9cba0f7
]]<fork-defn>

#disp[#block(inset: (y: 6pt))[
 #leanf("Freyd.Alg.RelProd.pair_outl") #src[(5.6)] #h(1.4cm)
  // lean:AOP.A5_2.pair_outl@18c8ddee
 #leanf("Freyd.Alg.RelProd.pair_outr") #src[(5.7)]
  // lean:AOP.A5_2.pair_outr@ce99887d
]]<fork-proj>

#disp[#row((box(inset: (right: 18pt),
  leancd("Freyd.Alg.RelProd.pair_outl_le+Freyd.Alg.RelProd.pair_outr_le")), leanc("Freyd.Alg.RelProd.pair")))]<fork-pic>

A domain is coreflexive, so `⟨R,S⟩π₁⊑R`, with equality exactly when `S` is entire; for maps both
triangles commute and `⟨f,g⟩` is unique. In `Rel`, `c ⟨R,S⟩ (a,b)` iff `c R a` and `c S b` — copy `c`, then
`R` on one strand and `S` on the other, which is `◁(R⊗S)` on the right.

No `°` survives the translation. `π₁=𝟙⊗⊸` discards the second component, so `π₁°=𝟙⊗⟜`
*creates* one out of nothing, and `∩` is copy, run both, merge. Draw that and the created strands —
the two dots with no left end, and the crossing they force — are merged against real ones, which is
the monoid's unit law:

#disp[#leanc("Freyd.Alg.RelProd.pair") #src[`⟜▷=𝟙` on each half]]<fork-collapse>
// lean:AOP.A5_2.Freyd.Alg.RelProd.pair@df1791ca


=== Relational product `R×S`

#disp(num: "(5.2)")[#definition[
`R×S≜⟨π₁R,π₂S⟩` #src[], a relator in each argument
// lean:AOP.A5_2.prodMap@28e34ad0
#src[] but no longer a categorical product.
// lean:AOP.A5_2.prod@64fdb8dc
]]<relprod-defn>

// The same pair of pictures with `C` replaced by `C × D`, once per projection: the two triangles
// become two squares, and the copy dot goes away — `R × S` is the two strands side by side.
#disp[#row((box(inset: (right: 18pt),
  leancd("Freyd.Alg.prodMap_outl_le+Freyd.Alg.prodMap_outr_le")), leanc("Freyd.Alg.prodMap")))]<relprod-pic>

Right-then-up is `(R×S)π₁`, up-then-right is `π₁R`, and `(R×S)π₁⊑π₁R`, equality when `S` is
entire. In `Rel`, `(c,d) (R×S) (a,b)` iff `c R a` and `d S b` — two strands side by side, no copy
dot: `R×S=R⊗S`.

=== Absorption

For `X : E⟶C` and `Y : E⟶D`, `⟨X,Y⟩(R×S)=⟨XR,YS⟩`. Both sides are this picture:

// ONE picture, not two with an `=`: pushing `R ⊗ S` past `X ⊗ Y` is interchange, already spent by the
// notation — both sides are the same strokes.  All of B&dM (5.3), whose direct proof needs two lemmas.
#disp(num: "(5.3)")[#leanc("Freyd.Alg.RelProd.pair_prodMap.rhs")]<absorption-pic>
// lean:AOP.A5_2.pair_prodMap@8861fda2

// A `#disp` block does NOT break across a page — it overflows and the last row is lost — so the rows
// below are kept short enough that the whole table fits one.
// B&dM §5.2, pp. 114–117, MIRRORED: the book writes `h·f` for first `f`, this note `f h`.  Five rows are
// ONE picture — `×` is `⊗` and `⟨R,S⟩` is `◁(R⊗S)`, so interchange spends the law before it is stated.
#disp[
  #show table.cell.where(x: 0): rownum
  #table(
  columns: (5.95cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*picture*]),

  // prodMap (duplicate of @relprod-defn), pair_prodMap (duplicate of @absorption-pic),
  // pair_outl/pair_outr (duplicate of @fork-proj) deleted — rule M.
 [#leanf("Freyd.Alg.RelProd.pair_recip_pair") #src[]],
  // lean:AOP.A5_2.pair_recip_pair@7b967917
  P(leanc("Freyd.Alg.RelProd.pair_recip_pair"), s: 74%),

  [#leanf("Freyd.Alg.RelProd.recip_pair_pair_le") #src[]],
  // lean:AOP.A5_2.recip_pair_pair_le@3e24af96
  P(leanc("Freyd.Alg.RelProd.recip_pair_pair_le"), s: 74%),

  [#leanf("Freyd.Alg.RelProd.map_comp_pair") \ #src[`f` a map; it fails for an arbitrary arrow;
 ]],
   // lean:AOP.A5_2.map_comp_pair@4056dfe1
  P(leanc("Freyd.Alg.RelProd.map_comp_pair"), s: 74%),

  [#leanf("Freyd.Alg.unzip_lax") \ #src[`unzip(F)≜⟨F(π₁),F(π₂)⟩`; only `⊑` for an arbitrary `R`, `S`]],
  P(leanc("Freyd.Alg.unzip_lax"), s: 74%),

  [`g=curry(f)⟺(g×𝟙)eval=f` \ #src[reading `×` as the relational product, does `Rel`
   have exponentials?]],
  // lean:Freyd.S1_85.curry_eq_iff@3d3eb304
  [],
)]<bdm-prod-laws>

== Relational coproducts <sec-coprod>

// THE DEFINITION, DRAWN, and it needs no new generator: `+` is a UNION, already drawn as the tape of
// the laws above.  A TAPE ONLY WHERE THERE IS A `∪`, which is why two of the three shape rows have none.
#disp[#table(
  columns: (1fr, 10.5cm),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*the statement* \ `R : a₁⟶c`, `S : a₂⟶c`], [*picture*]),

  [#leanf("Freyd.Alg.junc") \ #src[(5.9) The tape is the union — a particle entering at `A+B` takes exactly
   one branch — and the two mirrored boxes are what makes the branches disjoint.]],
  // lean:AOP.A5_3.junc@da022f10
  P(leanc("Freyd.Alg.junc"), s: 85%),

  [#leanf("Freyd.Alg.junc_eq_Λ_junc_eps") #src[]], P(leanc("Freyd.Alg.junc_eq_Λ_junc_eps"), s: 85%),
  // lean:AOP.A5_3.junc_eq_Λ_junc_eps@ea4663e1
  [#leanf("Freyd.Alg.u₁_junc"), #leanf("Freyd.Alg.u₂_junc") \ #leanf("Freyd.Alg.junc_unique")
 #src[,
   // lean:AOP.A5_3.u₁_junc@a01a115a lean:AOP.A5_3.u₂_junc@e692ee94
 ]], [],
   // lean:AOP.A5_3.junc_unique@192cec99

  [`U : a₁⟶D`, `V : a₂⟶D` \ #leanf("Freyd.Alg.junc_recip_junc") #src[(5.11)]], P(leanc("Freyd.Alg.junc_recip_junc"), s: 85%),
  // lean:AOP.A5_3.junc_recip_junc@838f4abc
)]<coprod-laws>

#disp[#table(
  columns: (1fr, 10.5cm),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*the statement* \ `R : a₁⟶b₁`, `S : a₂⟶b₂`], [*picture*]),

  [#leanf("Freyd.Alg.sumMap") #src[(5.10)]], P(leanc("Freyd.Alg.sumMap"), s: 85%),
  // lean:AOP.A5_3.sumMap@eb035ed1

  [#leanf("Freyd.Alg.Coproduct.u₁_self_comp_recip"), #leanf("Freyd.Alg.Coproduct.u₂_self_comp_recip") #src[Ex 5.12]],
  P(row((leanc("Freyd.Alg.Coproduct.u₁_self_comp_recip"),
    leanc("Freyd.Alg.Coproduct.u₂_self_comp_recip"))), s: 85%),
  // lean:Freyd.S2_20.Coproduct.u₁_self_comp_recip@6cd82772
  // lean:Freyd.S2_20.Coproduct.u₂_self_comp_recip@53e6991d

  // `rl°=𝟘` stays a formula: the exporter finds no naturality for the `𝟘` family on `B⟶A`.
  [#leanf("Freyd.Alg.Coproduct.u₁_u₂_recip"), #leanf("Freyd.Alg.Coproduct.u₂_u₁_recip") #src[Ex 5.12]],
  P(leanc("Freyd.Alg.Coproduct.u₁_u₂_recip"), s: 85%),
  // lean:Freyd.S2_20.Coproduct.u₁_u₂_recip@ade7327c lean:Freyd.S2_20.Coproduct.u₂_u₁_recip@61def7d7

  [#leanf("Freyd.Alg.Coproduct.recip_union_eq_id") #src[Ex 5.12]], P(leanc("Freyd.Alg.Coproduct.recip_union_eq_id"), s: 85%),
  // lean:Freyd.S2_20.Coproduct.recip_union_eq_id@6443cb0e
)]<coprod-map-laws>

=== `[R,S]≜[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]∋`

// B&dM §5.3, pp. 117-118, mirrored into this note's diagram order: why the universal property holds
// with equality where the fork's triangles above only hold up to `Dom`.
The universal-property row is not free: `l,r` were only ever asked to be a coproduct of *maps*. They stay one
once every arrow is allowed because $frac(#box(width: 8pt), ∋)$ sends an arrow `A⟶C` to a map `A⟶PC` reversibly, so the
map coproduct can be applied underneath it. For any `T : A+B⟶C`,

// The box chain of the `R%∋ = (R/∋) ∩ (∋/R)°` subsection, wrapped the same way: the row that
// carries over opens with its `⟺`.  Both `·∋ ⊣ %∋` steps are the same bijection, used each way.
#disp[
#zline(
  zpair(zsqc(`lT`, `R`, eq: true), zsqc(`rT`, `S`, eq: true)),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zpair(zsqc($frac(#[`lT`], ∋)$, $frac(#[`R`], ∋)$, eq: true), zsqc($frac(#[`rT`], ∋)$, $frac(#[`S`], ∋)$, eq: true)),
  zstep(op: sym.arrow.l.r.double, under: true)[fusion],
  zpair(zsqc([`l` $frac(#[`T`], ∋)$], $frac(#[`R`], ∋)$, eq: true), zsqc([`r` $frac(#[`T`], ∋)$], $frac(#[`S`], ∋)$, eq: true)),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[coproduct of maps],
  zsqc($frac(#[`T`], ∋)$, [`[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]`], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`T`, [`[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]∋`], eq: true),
)
 // lean:AOP.A5_3.Λ_junc@a2c38b7d lean:AOP.A5_3.junc_map@b2d62c40
]<coprod-calc>

#disp[#leancd("Freyd.Alg.u_junc_Λ_eps")]<coprod-square>

Nothing here holds only up to `⊑`: every triangle commutes on the nose, which is the difference from
the fork above. The border spells `[R,S]=[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]∋`, and pushing `∋` into the union that
`[·,·]` on maps already is turns that back into the definition,
`(l°` $frac(#[`R`], ∋)$ `∪r°` $frac(#[`S`], ∋)$`)∋=l°R ∪ r°S`.

// B&dM §5.3, pp. 117–119, mirrored like the product table.  A TAPE WHEREVER THERE IS A `∪`, so (5.9)
// and (5.10) are definitions drawn rather than equations: the tape IS the union on the right.
#disp[#table(
  columns: (5.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*picture*]),

  // junc (5.9), sumMap (5.10), junc_recip_junc (5.11) — duplicates of @coprod-laws's first,
  // third and last rows — and junc_id_zero/junc_zero_id/junc_injections (Ex 5.12) — duplicate
  // of @coprod-laws's Exercise 5.12 rows — deleted, rule M.

  // prove (5.11), and say why duality does not carry it over from the product law: B&dM Ex 5.13
  [#src[prove (5.11), and say why duality does not carry it over from the product law]],
  [],

  // row: Ex 5.14
  [#leanf("Freyd.Alg.sumMap_inter_junc_recip") \ #src[`[P,Q][U,V]°` is a full 2×2 of
   composites; `R+S` is diagonal, so the meet cuts the two off-diagonal branches]],
  P(leanc("Freyd.Alg.sumMap_inter_junc_recip"), s: 62%),
)]<bdm-coprod-laws>

// B&dM §5.4, p. 119.  The heading gets its own page: the definition, the paragraph that explains its
// shape, and the table are one argument, and the coproduct figure above ends a page mid-way.
#pagebreak(weak: true)
== The power relator `P(R)` <sec-powrel>

// B&dM p. 119's three steps, in its order: the point-free line, the `Rel` set formula, one plain
// sentence.
#disp[#definition[
For `R : A⟶B`,
#grid(columns: 2, column-gutter: 5pt, align: (right + horizon, left + horizon), row-gutter: 7pt,
 [], [#leanf("Freyd.Alg.powerRel") #src[]],
  // lean:AOP.A5_4.powerRel@ec676a67
 [`E(R)≜` $frac(#[`∋R`], ∋)$ `=`], [`((∋R)/∋)∩(∋/(∋R))°` #src[]],
  // lean:AOP.A4_6.existsImage@eb2a9f39
)

`xs P(R) ys⟺(∀a∈xs. ∃b∈ys. a R b)∧(∀b∈ys. ∃a∈xs. a R b)`

Every element of `xs` is related by `R` to some element of `ys`, and conversely.
]]<powrel-defn>

#disp[#align(center, table(
  columns: 5,
  align: left + horizon,
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([], [*in Rel*], [*in words*], [*im(xs)*], [*partner*]),

  [`(∋R)/∋`],
    [`∀y∈ys. ∃x∈xs. x R y`],
    [`∀y. some xs R y`],
    [`ys⊆im(xs)`],
    [every `y` has a partner],
  [`(∋/(∋R))°`],
    [`∀y. (∃x∈xs. x R y)→y∈ys`],
    [every `y` with `some xs R y` is in `ys`],
    [`ys⊇im(xs)`],
    [`ys` leaves out no partner],
  [`E(R)`],
    [`ys={y∣∃x∈xs. x R y}`],
    [`ys` = every `y` with `some xs R y`],
    [`ys=im(xs)`],
    [every `y` has a partner, \ and none is left out],
  [`((∋R°)/∋)°`],
    [`∀x∈xs. ∃y∈ys. x R y`],
    [`∀x. x R some ys`],
    [—],
    [every `x` has a partner],
  [`P(R)`],
    [`∀y∈ys. ∃x∈xs. x R y` and \ `∀x∈xs. ∃y∈ys. x R y`],
    [`∀y. some xs R y` and \ `∀x. x R some ys`],
    [—],
    [every `x` and every `y` \ has a partner],
  // lean:AOP.A7_2_RelSet.powrel_readings@c8d9a0e3
  // lean:AOP.A7_2_RelSet.existsImage_apply@df0c21b6
  // lean:AOP.A5_7_PowerBeads.powerRel_apply@bbd76348
))]<powrel-readings>

// `1,2,3` on the left, `a,b,c` on the right — and the `skel` pictures below are a DIFFERENT example,
// where `a₁,a₂,a₃` is the source, not the target. Only this one has the empty image `R(2) = ∅`.
#disp[#block(breakable: false)[
#align(center, leang("Freyd.Alg.ImageExample.R",
  cols: ((type: "A", x: 0, ys: ("1": 1.0, "2": 0, "3": -1.0), node: "dot", lab: (-0.42, 0)),
    (type: "B", x: 3.2, ys: (a: 1.0, b: 0, c: -1.0), node: "dot", lab: (0.42, 0))),
  rels: (R: (col: GIVEN1, s0: 0.22, s1: 0.3)),
  notes: (((1.6, 1.5), text(10pt, GIVEN1)[`R`]), ((0, -1.7), text(10pt)[`A`]), ((3.2, -1.7), text(10pt)[`B`]))))

#align(center, table(
  columns: 6,
  align: left + horizon,
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*`xs`*], [*`(∋R)/∋`*], [*`(∋/(∋R))°`*], [*`E(R)`*], [*`((∋R°)/∋)°`*], [*`P(R)`*]),

  [`∅`],        [`∅`],                    [all 8 subsets of `abc`], [`∅`], [all 8 subsets of `abc`], [`∅`],
  [`{1}`],      [`∅`, `a`, `b`, `ab`],    [`ab`, `abc`], [`ab`], [`a`, `b`, `ab`, `ac`, `bc`, `abc`], [`a`, `b`, `ab`],
  [`{2}`],      [`∅`],                    [all 8 subsets of `abc`], [`∅`], [none], [none],
  [`{3}`],      [`∅`, `c`],               [`c`, `ac`, `bc`, `abc`], [`c`], [`c`, `ac`, `bc`, `abc`], [`c`],
  [`{1,2}`],    [`∅`, `a`, `b`, `ab`],    [`ab`, `abc`], [`ab`], [none], [none],
  [`{1,3}`],    [all 8 subsets of `abc`], [`abc`], [`abc`], [`ac`, `bc`, `abc`], [`ac`, `bc`, `abc`],
  [`{2,3}`],    [`∅`, `c`],               [`c`, `ac`, `bc`, `abc`], [`c`], [none], [none],
  [`{1,2,3}`],  [all 8 subsets of `abc`], [`abc`], [`abc`], [none], [none],
  // lean:AOP.A5_4_ImageExample.E_column@fcf876cf
  // lean:AOP.A5_4_ImageExample.P_column@7adea435
))

]]<powrel-vs-erel>

#disp[#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [`X⊑P(R)⟺X∋⊑∋R` and `X°∋⊑∋R°`],
  [One containment, and the same one at `R°` — which is the definition read off the two divisions.
 Hence `P(R°)=P(R)°`, and `R⊑S⟹P(R)⊑P(S)` #src[].],
   // lean:AOP.A5_4.powerRel_mono@c7c7e038

  [#leanf("Freyd.Alg.powerRel_id")],
  [The straightness axiom verbatim: extensionality *is* `P`'s unit law.
 #src[]],
   // lean:AOP.A5_4.powerRel_id@9a05ab0f

  [#leanf("Freyd.Alg.powerRel_map")],
  [In `Rel`, `xs P(f) ys⟺ys={f(a)|a∈xs}`. The half at `f°` says every `a∈xs` has its `f(a)` on
   `ys`; `f` has just the one image per `a`, so that already says `ys` contains everything `xs`
   reaches, which is the fraction's second half. For a map the two definitions coincide.
 #src[]],
   // lean:AOP.A5_4.powerRel_map@e6f91701

  [#leanf("Freyd.Alg.powerRel_comp")],
  [`⊒` is the division cancellation laws. `⊑` is the one law in this section that is not a
 calculation: it needs a tabulation of `P(RS)`. #src[]],
   // lean:AOP.A5_4.powerRel_comp@cc53e370
)]<powrel-laws>

// Its own page: the definition below only says what `T(R)` is, and the square after it is the reason
// that arrow exists, so the two have to be read together — under the picture above they would not be.
#pagebreak(weak: true)
=== Type relator

// `F`-algebra, `F`-homomorphism, the initial algebra, its reflection and fusion laws — @initial-defn,
// @cata-reflection, @cata-fusion — moved to §2 (Functions and Categories, `02-categories.typ`).

#disp[#definition[
Let `F` be a binary relator with initial type `(α,T)`, so `T` is a type functor. `F(R,S)` is its
action on a pair, and `F(X)` abbreviates `F(𝟙,X)`, the `F` of the reduce section. For every object
`A` the initial algebra is `α : F(A,TA)⟶TA`, among the maps. `T` acts on an arrow `R : A⟶B` by

  #align(center, block(inset: (y: 6pt))[#leanf("Freyd.Alg.typeMap_defn") #h(4pt)
 #src[]])
    // lean:AOP.A5_5_TypeFunctor.typeMap@dc092317 lean:AOP.A5_5_TypeFunctor.typeMap_defn@0b53edb2
]]<tf-defn>

// Same widths and stroke as the reduce table: the two tables are read one after the other, and
// a law column that changes width between them reads as a different kind of column.
// Equality fusion needs NO local completeness — (2.12) is on record for that.
#disp[#table(
  columns: (4.2cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*law*], [*what it says*]),

  [the defining equation],
  [#leanf("Freyd.Alg.typeMap_defn")],
  [Rebuild the structure with `α`, applying `R` to the parameter on the way.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_defn@0b53edb2

  [type relator],
  [#leanf("Freyd.Alg.typeMap_recip")],
  [A datatype acts on relations, not only on maps — the map of the converse is the converse of the
   map.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_recip@be2f7fb9
)]<tf-laws>

// The type functor `T` itself (its definition, the naturality square of `α`, and its fusion law —
// @tfun-defn, @tfun-sq, @tfun-fusion) moved to §2's "Type functor" section (`02-categories.typ`).

// Its own page: otherwise the heading lands as the last line under the power relator's table, an orphan
// a page away from the definition it names, and the defining square below straddles the break.
#pagebreak(weak: true)
// B&dM and Freyd call this a catamorphism; the note says reduce, after q's `/`.
== Relational catamorphisms <sec-cata>

#disp[#definition[
let `F` be a relator and has  *initial algebra* `α : F(T)⟶T` in the subcategory of functions.
`α` is also initial in the allegory:
]]<cata-defn>


=== The defining equation

// A WIRE'S COLOUR IS ITS TYPE, A BEAD'S COLOUR IS WHICH ARROW IT IS, so arrows carry over from the
// square.  The string half is generated, on @initial-defn's two panels at `⦇f⦈ := X`: two ALGEBRAS,
// `α` at `T` and `f` at `A`, each an arrow at its own carrier and so a bead on the object wire.
#let cata-def-l = "Freyd.Alg.relCata_UP.lhs.lhs"
#let cata-def-r = "Freyd.Alg.relCata_UP.lhs.rhs"
#disp[#pair(
  leancd("Freyd.Alg.relCata_UP.lhs"),
  lean(cata-def-l, cata-def-r, op: [=]),
  [#leanf("Freyd.Alg.relCata_UP") #h(6pt)
 #src[]],
)]<cata-defining>

// Machine-checked: an algebra on `A` IS definitionally a natural transformation `F∘A ⇒ A` between
// functors `𝟏 ⟶ 𝒜`, NOT one `F ⇒ 𝟙` on `𝒜` — `Nat.add` is an algebra that is no such component.
An F-algebra is a *weakened* natural transformation. A transformation `F⇒𝟙` on `𝒜` would need a
component `FX⟶X` at every object and a commuting square at every arrow, but F-Algebra only need it works on T and A.

// B&dM §2.6 (p. 46) at the two initial types this note folds over: the last row is what the defining
// equation above says pointwise.
#disp[#table(
  columns: (4.4cm, 1fr, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  // `y: 6.5pt`, tighter than the note's 9pt: its rows are two lines tall already, and the slack pays
  // for the marker line under @cata-map-calc, which the page had no room for.
  inset: (x: 9pt, y: 6.5pt), stroke: 0.4pt + luma(190),
  table.header(
    // B&dM p.46: "Arrows of the form ⦇f⦈ are called catamorphisms" … "two examples that reveal the notion of
    // a catamorphism to be a familiar idea in abstract clothing."
    table.cell(colspan: 3, align: center)[#text(12.5pt)[`⦇[c,f]⦈=reduce(c,f)`] \
      #src[catamorphism: arrows of the form `⦇f⦈` are called catamorphisms, and these two examples reveal the
       notion to be a familiar idea in abstract clothing]],
    [*part*], [*`Nat`*], [*`[A]`*],
  ),

  [datatype],
  [`Nat::=zero|succ Nat`],
  [`[A]::=nil|cons(A,[A])`],

  [base functor `F`],
  [`F(X)=1+X`],
 [`F(X)=1+A×X` #src[]],
  // lean:AOP.A6_ConsList.F_eq_sum_prod@cab297e7

  [initial algebra `α`],
  [`α=[zero,succ]` \ `: 1+Nat⟶Nat`],
 [`α=[nil,cons]` \ `: 1+A×[A]⟶[A]` #src[]],
  // lean:AOP.A6_ConsList.initial@ac4e2c78

  [the fold, pointwise],
  [`⦇[c,f]⦈(zero)=c` \ `⦇[c,f]⦈(succ(n))=f(⦇[c,f]⦈(n))`],
  [`⦇[c,f]⦈(nil)=c` \ `⦇[c,f]⦈(cons(a,x))=f(a,⦇[c,f]⦈(x))`],
)]<cata-initial>


=== `⦇R⦈=⦇`$frac(#[`F(∋)R`], ∋)$`⦈∋`

// B&dM p.121's figure, mirrored: @cata-defining's square at `f := `#frc([`F(∋)R`])`, `A := P A`,
// over the ∋/F(∋) rows and the relation `R` — the renamed arrows are the two induced ones and the bottom row.
// Generated, on the defining equation above at `X := ⦇`#frc([`F(∋)R`])`⦈`: the `E` wire is BORN at the
// banana, `T⟶PA` being where the power object enters.  TWO ALGEBRAS, `α : F(T)⟶T` and `f : F(PA)⟶PA`.
#let cata-map-l = "Freyd.Alg.Λ_relCata.lhs"
#let cata-map-r = "Freyd.Alg.Λ_relCata.rhs"
#disp[#pair(
  grid(columns: 1, align: center, row-gutter: 6pt,
  leancd("Freyd.Alg.relCata_mapAlg_cancel"),
  src[$frac(#[`𝟙`], ∋)$ is the inverse of `∋`]),
  lean(cata-map-l, cata-map-r, op: [=]),
  [#leanf("Freyd.Alg.Λ_relCata")
 #src[]],
   // lean:AOP.A5_5.Λ_relCata@4967772e lean:AOP.A5_5.relCata_unfold@8434a6c2
)]<cata-map-square>

// B&dM (5.12), p. 121, mirrored into this note's diagram order.  A row too wide for the column wraps,
// and the next row opens with the `⟺` that carries it over.
#disp(num: "(5.12)")[
#zline(
  zsqc([`αX`], [`F(X)R`], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc([$frac(#[`αX`], ∋)$], [$frac(#[`F(X)R`], ∋)$], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc([$frac(#[`αX`], ∋)$], [$frac(#[`F(`$frac(#[`X`], ∋)$ `∋)R`], ∋)$], eq: true),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[relator, fusion twice],
  zsqc([`α` $frac(#[`X`], ∋)$], [`F(`$frac(#[`X`], ∋)$`)` $frac(#[`F(∋)R`], ∋)$], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[reduce of maps],
  zsqc([$frac(#[`X`], ∋)$], [`⦇`$frac(#[`F(∋)R`], ∋)$`⦈`], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc([`X`], [`⦇`$frac(#[`F(∋)R`], ∋)$`⦈∋`], eq: true),
)
#align(center, block(inset: (y: 3pt))[#src[the last two rows at `X:=⦇R⦈`:
 ]])
 // lean:AOP.A5_5.Λ_relCata@4967772e lean:AOP.A5_5.relCata_unfold@8434a6c2
]<cata-map-calc>

// B&dM (5.12), p.121: the `⟹` half as ONE term chain from $frac(#[`X`], ∋)$ to the fold that names it,
// each panel drawn from the theorem proving that step, its last the fold uniqueness.
#disp[#calc-table(cols: (1fr,), al: auto,
  Thm(cols: 1)[#leanf("Freyd.Alg.relCata_UP_fold") \
    #src[in a tabular allegory, with `F` a relator and `α : F(T)⟶T` its initial algebra: a relation `X` out of `T` satisfies the fold equation `αX=F(X)R` of `R` exactly when $frac(#[`X`], ∋)$ is the fold of the map $frac(#[`F(∋)R`], ∋)$]],
    // lean:AOP.A5_5.relCata_UP_fold@daf65f6e
  [#lean-chain(formula: true,
      (none, "Freyd.Alg.relCata_UP_step1.lhs", []),
      (EQ, "Freyd.Alg.relCata_UP_step1.rhs", src[`α` iso; `αX=F(X)R`]),
      // lean:AOP.A5_5.InitialAlgebra.recip_alpha_alpha@5dcef861
      (EQ, "Freyd.Alg.relCata_UP_step2.rhs", src[`α°` is a map because `α` is an iso, so it leaves Λ: $frac(#[`α°F(X)R`], ∋)$`=α°`$frac(#[`F(X)R`], ∋)$ — @pow-laws]),
      (EQ, "Freyd.Alg.relCata_UP_step3.rhs", src[`X=`$frac(#[`X`], ∋)$`∋` — @pow-laws]),
      (EQ, "Freyd.Alg.relCata_UP_step4.rhs", src[`F(`$frac(#[`X`], ∋)$`∋)=F(`$frac(#[`X`], ∋)$`)F(∋)` as `F` is a functor, and `F(`$frac(#[`X`], ∋)$`)` is a map (a relator sends maps to maps), so it leaves Λ — @relator-defn, @pow-laws]),
      (EQ, "Freyd.Alg.relCata_UP_step5.rhs", src[fold uniqueness, $frac(#[`F(∋)R`], ∋)$ being a map — @initial-defn]),
      // lean:AOP.A5_5.relCata_UP_step5@cdbc6943
  )],
)]<cata-map-proof>

// The step-table helpers, hoisted above §@sec-mu, the first section that uses them: a Typst `#let`
// binds only below its line.  The step's relation sits at the LEFT EDGE of formula AND picture, so
// both read as chains: `⊑`/`⊒` takes `SLACK` where the proof loses information, `=` stays grey.
#let SQ = text(SLACK)[$subset.eq.sq$]
#let RQ = text(SLACK)[$supset.eq.sq$]


== Combinatorial functions <sec-comb>

// B&dM §5.6, p. 125, plus the three specifications of Ex 7.39–7.41 (p. 174).  Every composite is
// mirrored to diagram order, so B&dM's `prefix · suffix` is `suffix prefix` here.
#disp[#table(
  columns: (7.1cm, 2.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

  [`[A]::=nil|cons(A,[A])`],
  [#leant("Freyd.Alg.RelSet.ListRel.listRelator")],
  // list type note: B&dM's `listr`, renamed here from p. 125 on
  [The list type, under the short name it keeps.],

 [#leanf("Freyd.Alg.RelSet.ListRel.list_cata") #src[]],
  // lean:AOP.A5_6_ListCombinators.list_cata@08d57306
  [#leant("Freyd.Alg.RelSet.ListRel.list_cata")],
  [The relator's action on `R : A⟶B`: one `R` per element, the shape untouched.],

 [#leanf("Freyd.Alg.RelSet.ListRel.subseq_cata") #src[]],
  // lean:AOP.A5_6_ListCombinators.subseq_cata@8a4731df
  [#leant("Freyd.Alg.RelSet.ListRel.subseq_cata")],
  [`xs subseq ys`: `ys` is `xs` with elements dropped — `cons` keeps the head, `π₂` drops it.],

  [#leanf("Freyd.Alg.RelSet.ListRel.prefix_cata") \
 #leanf("Freyd.Alg.RelSet.ListRel.prefix_cat")`=init*` #src[]],
   // lean:AOP.A5_6_ListCombinators.prefix_cata@9836cfe0 lean:AOP.A5_6_ListCombinators.prefix_cat@eb19c936
  [#leant("Freyd.Alg.RelSet.ListRel.prefix_cata")],
  [`ys` is an initial segment of `xs`; the first `nil` is where it stops early. `init≜snoc° π₁`.],

 [#leanf("Freyd.Alg.RelSet.ListRel.suffix_cat")`=tail*` #src[]],
  // lean:AOP.A5_6_ListCombinators.suffix_cat@c70cd49e
  [#leant("Freyd.Alg.RelSet.ListRel.suffix_cat")],
  [The dual, `tail≜cons° π₂`; as a reduce it needs snoc-lists.],

 [#leanf("Freyd.Alg.RelSet.ListRel.partition_concat") #src[]],
  // lean:AOP.A5_6_ListCombinators.partition_concat@f9c15a2e
  [#leant("Freyd.Alg.RelSet.ListRel.partition_concat")],
  [This `cat` is restricted to `[A]⁺×[A]⟶[A]`, so `ys` is a list of non-empty segments of `xs`.],

 [#leanf("Freyd.Alg.RelSet.ListRel.concat_cata") #src[]],
  // lean:AOP.A5_6_ListCombinators.concat_cata@37766c0d
  [#leant("Freyd.Alg.RelSet.ListRel.concat_cata")],
  [Joins the segments back up, which is why its converse splits a list.],

  [`inits`],
  [#leant("Freyd.Alg.RelSet.ListRel.initsR")],
  [Implements $frac(#[`prefix`], ∋)$, listing the prefixes by increasing length.],

  [`tails`],
  [#leant("Freyd.Alg.RelSet.ListRel.tailsR")],
  [Implements $frac(#[`suffix`], ∋)$ by decreasing length — the opposite order.],

  // B&dM §5.6, pp. 125–126, "Cartesian product".
  [`cpp`, `cpl`, `cpr`],
  [#leant("Freyd.Alg.RelSet.ListRel.cpp") \ #leant("Freyd.Alg.RelSet.ListRel.cpl") \
   #leant("Freyd.Alg.RelSet.ListRel.cpr")],
  [Every pair `(a,b)` with `a` from the first list and `b` from the second; `cpl`, `cpr` keep one side a single element.],

  [#leanf("Freyd.Alg.RelSet.ListRel.setify_cpp") \ #leanf("Freyd.Alg.RelSet.ListRel.setify_cpl") \
   #leanf("Freyd.Alg.RelSet.ListRel.setify_cpr") #src[]],
  // lean:AOP.A5_6_ListCombinators.setify_cpp@1a28e284 lean:AOP.A5_6_ListCombinators.setify_cpl@a501aaa4 lean:AOP.A5_6_ListCombinators.setify_cpr@87353fd8
  [#leant("Freyd.Alg.RelSet.ListRel.setify_cpp")],
  [Forgetting the order with `setify`, `cpp` is the transpose of `∋×∋`.],

  [#leanf("Freyd.Alg.cpMap") #src[]],
  // lean:AOP.A5_6.cpMap@636ea157
  [#leant("Freyd.Alg.cpMap")],
  [`cp(F)`, the transpose of a relator's action on `∋`; `cpp` implements it at `F(A)=A×A`.],

  [#leanf("Freyd.Alg.RelSet.ListRel.cp_list") \ #leanf("Freyd.Alg.RelSet.ListRel.cp_list_alg") #src[]],
  // lean:AOP.A5_6_ListCombinators.cp_list@b2418f21 lean:AOP.A5_6_ListCombinators.cp_list_alg@34227b70
  [#leant("Freyd.Alg.RelSet.ListRel.cp_list")],
  [`cp(list)`: @cata-map-calc at `list(∋)=⦇[nil,(∋×𝟙)cons]⦈`, then the algebra expanded.],

  [#leanf("Freyd.Alg.RelSet.ListRel.cplist_cata") #src[]],
  // lean:AOP.A5_6_ListCombinators.cplist_cata@69ef2d49
  [#leant("Freyd.Alg.RelSet.ListRel.cplist")],
  [`cp(list)` with every set a list: `cpp` in place of $frac(#[`∋×∋`], ∋)$.],

)]<comb-fns>

#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.ListRel.concat_glue") \
    #src[putting `a` on the front of the first segment and flattening (`glue concat`) gives at most
     flattening the segments and putting `a` on the front of the result (`(𝟙×concat) cons`)]],
  // lean:AOP.A5_6_ListCombinators.concat_glue@4d016cca
  // two rows: seven panels in one row shrink the labels past reading
  lean-chain((
    (none, "Freyd.Alg.RelSet.ListRel.concat_glue_step1.lhs", src[the starting composite]),
    (DF, "Freyd.Alg.RelSet.ListRel.concat_glue_step1.rhs", src[definition of glue]),
    // lean:AOP.A5_6_ListCombinators.concat_glue_step1@116e04aa
    (EQ, "Freyd.Alg.RelSet.ListRel.concat_glue_step2.rhs", src[since `concat=⦇[nil,cat]⦈`]),
    // lean:AOP.A5_6_ListCombinators.concat_glue_step2@6a274ac8
    (EQ, "Freyd.Alg.RelSet.ListRel.concat_glue_step3.rhs", src[naturality of `assocl`]),
    // lean:AOP.A5_6_ListCombinators.concat_glue_step3@f23e8b63
  ), (
    (SQ, "Freyd.Alg.RelSet.ListRel.concat_glue_step4.rhs", src[since `concat=⦇[nil,cat]⦈`]),
    // lean:AOP.A5_6_ListCombinators.concat_glue_step4@6a0affce
    (EQ, "Freyd.Alg.RelSet.ListRel.concat_glue_step5.rhs", src[since `(cons×𝟙) cat=assocr (𝟙×cat) cons`]),
    // lean:AOP.A5_6_ListCombinators.concat_glue_step5@72b82363
    (SQ, "Freyd.Alg.RelSet.ListRel.concat_glue_step6.rhs", src[since `assocl assocr=𝟙` and `cat° cat⊑𝟙`]),
    // lean:AOP.A5_6_ListCombinators.concat_glue_step6@ff4485e8
  )),
)]<concat-glue>

=== $frac(#[`subseq`], ∋)$ `=⦇[nil` $frac(#[`𝟙`], ∋)$`,⟨`$frac(#[`𝟙×∋`], ∋)$` E(cons),π₂⟩ cup]⦈`

// B&dM §5.6, p. 124: @cata-map-calc run at `subseq`'s algebra `[nil, cons ∪ π₂]`, which is what
// turns the relation into a program.  `cup` is needed first — nothing above this note has a binary union.
#disp[#definition[
`cup≜` $frac(#[`π₁∋ ∪ π₂∋`], ∋)$ ` : PA×PA⟶PA`, #h(4pt) so
$frac(#[`R ∪ S`], ∋)$ `=⟨`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`⟩ cup`.
#h(4pt) #src[]
// lean:AOP.A5_6.Λ_union@a769989a
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
    // lean:AOP.A5_6_ListCombinators.subseq_alg_Λ@e9ebf14d lean:AOP.A5_6_ListCombinators.subseq_cata@8a4731df
  table.header([*circuit* — the fork is `F([A])=𝟏+A×[A]`: `nil` above, the pair below],
    [*Hinze–Marsden*]),

  // THE TWO COLUMNS ARE NOT ONE THEOREM PER ROW HERE, and that is deliberate: the circuit column
  // rewrites the WHOLE term step by step, where the Hinze–Marsden column stays on the one operand
  // `(𝟙×∋)π₂` the steps do not touch — which is why one selector repeats down three rows.  The
  // general rule is the other way round (AGENTS.md); §12.1 is its exception and stays as it is.
  // Rows 1–3 draw the NUMERATOR, `F(P[A]) ⟶ [A]`: the transpose is still outside the bracket there,
  // and the generator fuses `F(∋)[f,g]` into the one tape `[f,(𝟙×∋)g]` on trust (CIRCUIT-GEN §1.4).
  [#vstep([], leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.lhs"), [#frc([`F(∋)[nil,cons ∪ π₂]`])])],
  [#lean("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.rhs", branch: "inr.inr") \ #src[the `π₂` operand of `cons ∪ π₂` under the `𝟙×∋` summand of `F(∋)`, i.e. `(𝟙×∋)π₂`]],

  // The sum `𝟙+𝟙×∋` and the bracket after it fuse into the one tape, `(R+S)[f,g]=[Rf,Sg]`.
  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_map.lhs"),
    [#frc([`(𝟙+𝟙×∋)[nil,cons ∪ π₂]`]) \ #src[`F(X)=𝟏+A×X` — @comb-fns]])],
    // lean:AOP.A5_6_ListCombinators.subseq_alg_sum_map@5548e84e lean:AOP.A6_ConsList.F_eq_sum_prod@cab297e7
  [#lean("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.rhs", branch: "inr.inr") \ #src[the same operand under `𝟙+𝟙×∋`, whose `𝟙×∋` summand it sits in]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.rhs"), [#frc([`[nil,(𝟙×∋)(cons ∪ π₂)]`]) \
    #src[`R+S≜[Rl,Sr]`, `l[R,S]=R`, `r[R,S]=S` — @coprod-laws]])],
  [#lean("Freyd.Alg.RelSet.ListRel.subseq_alg_sum_junc.rhs", branch: "inr.inr") \ #src[the `π₂` operand of the second arm `(𝟙×∋)(cons ∪ π₂)`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_Λ_junc.rhs"), [`[`#frc([`nil`])`,`#frc([`(𝟙×∋)(cons ∪ π₂)`])`]` \
    #src[@coprod-calc at `T:=[nil,(𝟙×∋)(cons ∪ π₂)]`]])],
    // lean:AOP.A5_3.Λ_junc@a2c38b7d
  [#sb-hm-p2 \ #src[the `π₂` operand under its `𝟙%∋`, the arm @subseq-outr-square's square rewrites,
    `(𝟙×∋)π₂=π₂∋`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.ListRel.subseq_alg_Λ_nil.rhs"), [`[nil `#frc([`𝟙`])`,`#frc([`(𝟙×∋)(cons ∪ π₂)`])`]` \
    #src[@pow-laws, #frc([`f`])` =f `#frc([`𝟙`]) for `f` a map, at `f:=nil`]])],
    // lean:AOP.A5_6_ListCombinators.Λ_nil_singleton@d276006e
  [#sb-hm-p2 \ #src[the same operand; the two rows differ only in the `nil` arm]],
)]<subseq-EW-case>

// @relprod-pic's square at `R × S := 𝟙 × ∋`, on @cata-defining's 5.2 × 2.7 geometry.  The two `π₂`
// sit on OPPOSITE sides — one name, one colour, two rows, which is what the string picture cannot show.
#disp[#leancd("Freyd.Alg.RelSet.ListRel.prod_ni_proj_slide")]<subseq-outr-square>

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.ListRel.subseq_alg_join") \
    #src[power transpose of join: the power transpose of the join of two relations is
     `⟨`#frc([`R`])`,`#frc([`S`])`⟩ cup`, where `cup` is the function that returns the union of two sets]],
    // lean:AOP.A5_6_ListCombinators.subseq_alg_join@b7ae8680
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
    // lean:AOP.A5_6_ListCombinators.prod_ni_proj_slide@931da6a5
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
#pagebreak(weak: true)
== Lax natural transformations (LaT)

// B&dM §5.7, p. 133.  Same `⇒` the note gives an ordinary natural transformation: B&dM's own hooked
// arrow marks laxness, but the word already does, and the inequation is right there.
#disp[#definition[
For relators `G,F : 𝒞⟶𝓓` and components `φ`#sub[`A`]` : GA⟶FA`, `φ` is *lax at*
`R : A⟶B` when #h(4pt) `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) — both sides `GA⟶FB`, the
left through the component at `B`, the right through the one at `A`.

`φ : G⇒F` is a *lax natural transformation* (LaT) when it is lax at *every* `R`. #h(4pt) #src[(5.13)]

Lax at every *map* already gives LaT, and at a map the inequation is an equality #h(4pt)
`G(f)φ=φF(f)`: #h(4pt) laxness is about relations only.
// lax-defn row: Theorem 5.2
#h(4pt) #src[]
// lean:AOP.A5_7.laxNatural_iff_strict_on_maps@e374cc23
]]<lax-defn>

// The two panels of the inequation, emitted by `./scripts/diagram --sigs … --src … --tgt …` plus
// `s: 100%`, the square's own size.  `φ` is `!lax`: the HOLLOW dot is the whole difference from a
// natural transformation's filled one, and it is why `φ` may leave the object wire at all — a LaT is
// a family, not an arrow at one object.  The bead is BARE, as §11.4's `α` is: the component's index
// is the object wire it stands on, and the two panels differ in exactly where that wire is renamed.
#let lax-hm-l = "Freyd.Alg.LaxNatural.lhs"
#let lax-hm-r = "Freyd.Alg.LaxNatural.rhs"

#disp[#pair(
  leancd("Freyd.Alg.LaxNatural"),
  lean(lax-hm-l, lax-hm-r, op: [#SQ]),
 [`G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #src[]],
)
// lean:AOP.A5_1.LaxNatural@ba661fee
]<lax-str>

// Not in B&dM §5.7, which stops at Theorem 5.2.

#disp[#table(
  columns: (4.8cm, 10.6cm, 6.6cm),
  align: (left + horizon, center + horizon, center + horizon),
  // `y: 2pt`: the LaT letters wrap two of the statement lines, and at 5pt the table outgrew the page —
  // a `#disp` table cannot break, so the last row was laid over the one above it.
  inset: (x: 9pt, y: 2pt), stroke: 0.4pt + luma(190),
  table.header([*closed under*], [*commutative diagram*], [*string diagram*]),

  [composition \ `ψφ`],
  [#P(leancd("Freyd.Alg.laxNatural_comp_slide"), s: 74%)
   `H(R)ψ`#sub[`B`]`⊑ψ`#sub[`A`]`G(R)` #h(4pt) and #h(4pt) `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)`
   #h(4pt) give #h(4pt) `H(R)(ψ`#sub[`B`]`φ`#sub[`B`]`)⊑(ψ`#sub[`A`]`φ`#sub[`A`]`)F(R)`],
  P(lean("Freyd.Alg.laxNatural_comp_slide"), s: 74%),

  [horizontal composition \ `χ∘φ`],
  [#P(leancd("Freyd.Alg.laxNatural_hcomp_outer_first"), s: 74%)
   `φ : G⇒F` with `G,F : 𝒞⟶𝓓` and `χ : L⇒K` with `L,K : 𝓓⟶𝓔` give
   `χ∘φ : L∘G⇒K∘F`, the family `A ↦ χ`#sub[`GA`]`K(φ`#sub[`A`]`)` \
   #src[`L(G(R))χ`#sub[`GB`]`⊑χ`#sub[`GA`]`K(G(R))` is `χ` lax at `G(R)`; then
   `K(G(R)φ`#sub[`B`]`)⊑K(φ`#sub[`A`]`F(R))` is `K` applied to `φ`'s own inequation;
 ] \
   // lean:AOP.A5_7.laxNatural_hcomp_outer_first@ce6a24d8
   #src[`χ:=𝟙`#sub[`K`] gives `K(φ) : K∘G⇒K∘F`, `K` composed on the outside;
   `φ:=𝟙`#sub[`G`] gives `χG : L∘G⇒K∘G`, `G` composed on the inside] \
   #src[two candidates, `χ`#sub[`GA`]`K(φ`#sub[`A`]`)` and `L(φ`#sub[`A`]`)χ`#sub[`FA`], ordered by
   `⊑`; this row is the first]],
  // Two wires side by side, a bead on each; an identity 2-cell is a bare wire, so dropping the left
  // bead leaves `K(φ)` and dropping the right one leaves `χG` — the two cases that had rows of their own.
  P(lean("Freyd.Alg.laxNatural_hcomp_outer_first_slide"), s: 74%),

  [union \ `φ ∪ ψ`],
  [#P(leancd("Freyd.Alg.laxNatural_union"), s: 74%)
   `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) and #h(4pt) `G(R)ψ`#sub[`B`]`⊑ψ`#sub[`A`]`F(R)`
   #h(4pt) give #h(4pt) `G(R)(φ`#sub[`B`]` ∪ ψ`#sub[`B`]`)⊑(φ`#sub[`A`]` ∪ ψ`#sub[`A`]`)F(R)`
 #h(4pt) #src[]],
   // lean:AOP.A5_7.union_slides@f7484fb4
  P(lean("Freyd.Alg.laxNatural_union_slide"), s: 74%),

  [a relator `K` \ `K(φ)`],
  [#P(leancd("Freyd.Alg.Relator.map_laxNatural"), s: 74%)
   `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) gives #h(4pt)
   `K(G(R))K(φ`#sub[`B`]`)⊑K(φ`#sub[`A`]`)K(F(R))`],
  [],

  [product \ `φ×ψ`],
  [#P(leancd("Freyd.Alg.laxNatural_prod"), s: 74%)
   `φ : G⇒F` and `ψ : G'⇒F'` give `φ×ψ : G×G'⇒F×F'` \
   #src[`(R×S)(U×V)=(RU)×(SV)` and monotonicity in both slots — the row above's `K` applied to the
   inequation, run on a bifunctor; the fork is the derived case `⟨φ,ψ⟩=◁(φ×ψ)`, and its ONE cost is
   the lax copy law `R◁⊑◁(R×R)` — @rel-monoid]],
  // `G×G'=×∘⟨G,G'⟩`: two UNARY functors, so the split is typed — `⟨G,G'⟩ : 𝒞⟶𝓓×𝓓` then `× : 𝓓×𝓓⟶𝓓`.
  // The bead is the PAIR in `𝓓×𝓓`, written `(φ,ψ)`: the fork `⟨φ,ψ⟩=◁(φ×ψ)` is a different arrow, in `𝓓`.
  P(lean("Freyd.Alg.laxNatural_prod_slide"), s: 74%),

  [coproduct \ `φ+ψ`],
  [#P(leancd("Freyd.Alg.laxNatural_sum"), s: 74%)
   `φ : G⇒F` and `ψ : G'⇒F'` give `φ+ψ : G+G'⇒F+F'` \
   #src[`(R+S)(U+V)=(RU)+(SV)` and monotonicity in both slots; the co-fork is the derived case
   `[φ,ψ]=(φ+ψ)▿`, and `▿` costs nothing]],
  // `+`, like `×`, is a functor `𝓓×𝓓⟶𝓓`, so the picture is the one above with `+` on the left wire.
  P(lean("Freyd.Alg.laxNatural_sum_slide"), s: 74%),

  [meet — *fails* \ `φ∩ψ`],
  [#src[the step it would need is
   `(φ`#sub[`A`]`F(R))∩(ψ`#sub[`A`]`F(R))⊑(φ∩ψ)`#sub[`A`]`F(R)`, the wrong direction of
   @meet-semidistrib] \
   #src[a counterexample: @meet-counterex]],
  [],

  table.cell(colspan: 3, align: left + horizon)[Each row is the general slide #h(4pt)
   `R`#sub[`A`]`X⊑X'R`#sub[`B`] and `R`#sub[`B`]`Y⊑Y'R`#sub[`C`] give
   `R`#sub[`A`]`(XY)⊑(X'Y')R`#sub[`C`] #h(4pt) at `R`#sub[`A`]`,R`#sub[`B`]`:=G(R),F(R)` and
   `X,X':=φ`#sub[`B`]`,φ`#sub[`A`], quantified over `R`; at `X'=X` with `R`#sub[`A`]`,R`#sub[`B`]
   endorelations it is the monotonicity reading instead — the `∀R` sits outside the law, and is the
 only difference #h(4pt) #src[]],
   // lean:AOP.A5_7.comp_slides@480a3dc9
)]<lax-closure>

// `sticky` binds a heading to the next BLOCK, and `conf` wraps every display in a breakable one, so
// the heading stays behind while the picture moves on: the break has to be placed by hand.
#pagebreak(weak: true)
=== meet is not closed in LaT

// diag/natsq.typ's idiom for a square that FAILS: ONE COLOUR PER ROUTE — here `GIVEN1`/`GIVEN2` mark
// across-then-down and down-then-across, not horizontal/vertical — and the traced element's values
// wear their route's colour, so the two results are read off without following the arrows.
// `breakable: false`: `conf` makes every display breakable, and the claim line broke away from its
// own picture at the foot of a page.
#disp[#block(breakable: false)[
#align(center, strong[counterexample — `φ,ψ : G⇒F` lax natural does NOT give `φ∩ψ` lax natural])
#v(4pt)
#capbox(
  leancd("Freyd.Alg.inter_not_laxNatural_square"),
  [`A=B≜{0,1}`, #h(4pt) `R≜{(0,0),(1,0)}`, #h(4pt) `φ≜π₁∩π₂ : Δ⇒Id` #h(4pt) #src[]],
   // lean:AOP.A6_1_OrdRelSet.laxNatural_inter_false@bcff53dc
)]]<meet-counterex>

=== Two stacked towers

// TWO towers, not one four-level ladder: `R⊑S` is the LOWER tower's 2-cell, and the whole lower
// tower is one 0-cell of the upper.  Drawn together because that containment is the only thing that
// answers "where did the ordinary `⊑` go".
#disp[
#table(
  columns: (2.2cm, 5.5cm, 1fr),
  align: (center + horizon, left + horizon, left + horizon),
  inset: (x: 9pt, y: 5pt), stroke: 0.4pt + luma(190),
  table.header([], [*lower — inside ONE allegory*], [*upper — between allegories*]),

  [`0`-cell], [an object `A`],
  [an allegory `𝒞` #h(4pt) — *a whole lower tower*],

  [`1`-cell], [a relation `R : A⟶B`], [a relator `F : 𝒞⟶𝓓`],

  [`2`-cell], [`R⊑S`], [a LaT `φ : G⇒F` #h(4pt) #src[@lax-defn]],

  [order], [`R⊑S`], [`φ⊑ψ` componentwise],

  [union], [`R ∪ S`], [`φ ∪ ψ`, *survives* #h(4pt) #src[@lax-closure]],

  [product], [`R×S` #h(4pt) #src[@relprod-defn]],
  [`φ×ψ`, *survives*; a TENSOR, not a categorical product; SYMMETRIC
   #h(4pt) #src[@fork-proj] #h(4pt) #src[@lax-closure]],

  [coproduct], [`R+S`],
  [`φ+ψ`, *survives*; a BIPRODUCT #h(4pt) #src[@lax-closure]],

  [meet], [`R∩S`],
  [`φ∩ψ` componentwise, *fails* #h(4pt) #src[@meet-counterex]],

  [converse], [`R°`],
  [`φ°`, *fails*, oplax: `φ`#sub[`A`]`°G(R)⊑F(R)φ`#sub[`B`]`°`
 #h(4pt) #src[]],
   // lean:AOP.A5_7.recip_oplax@7735eec0 lean:AOP.A6_1_OrdRelSet.recip_not_laxNatural@1983c3f6

  [zero object], [`z` with `𝟙 z=𝟘`],
  [the constant relator at such a `z`, initial and terminal],
)
]<lat-tower>


=== `R⊑S` is a special case of LaT

// @lax-str's square three times over, at the base arrow `R : X⟶Y`: general, then at the two constant
// relators, then with the identity verticals gone.  Identity verticals are what turn a square into a
// comparison of its two horizontals, so the collapse is drawn, not asserted.
#disp[#capbox(
  row((leancd("Freyd.Alg.LaxNatural"), [#h(9pt) #sym.arrow.r.double.long #h(9pt)],
       leancd("Freyd.Alg.laxNatural_const_iff.lhs"),
       [#h(9pt) #sym.arrow.r.double.long #h(9pt)],
       leancd("Freyd.Alg.laxNatural_const_iff.rhs"))),
  [`G≜const A`, #h(4pt) `F≜const B` #h(4pt) — the relators `X↦A` and `X↦B`, each sending every arrow
   to `𝟙` #h(4pt) #src[@lax-defn] \
   with `𝒞` two objects and one non-identity arrow `X⟶Y`, a LaT `const A⇒const B` is the pair
   `φ`#sub[`X`]`,φ`#sub[`Y`]` : A⟶B` with `φ`#sub[`Y`]`⊑φ`#sub[`X`] #h(4pt) — the datum `R⊑S` \
   not every LaT is constant: #h(4pt) `∋ : P⇒Id` #h(4pt) #src[@powrel-laws] #h(4pt)
   `π₂ : (A×−)⇒Id` #h(4pt) #src[@subseq-outr-square] #h(4pt) `◁ : Id⇒Δ` #h(4pt) #src[@rel-monoid]],
  // lean:AOP.A5_7.laxNatural_const_iff@4af68018
)]<lat-const>

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
