#import "../note-prelude.typ": *
#show: note-chapter.with(11)
// note-split: chapter 11 — this header is written by scripts/note-split and stripped by scripts/note-join
= Relator

#disp[#definition[
Every hom-set of an allegory is a poset, so an allegory is a *locally posetal 2-category*: the 2-cell
from `R` to `S` IS `R⊑S`. A *relator* `F : 𝒞⟶𝓓` is a 2-functor between allegories:

  #align(center, block(inset: (y: 6pt))[
 #text(12.5pt)[`F(𝟙)=𝟙` #src[] #h(1cm)
    // lean:Freyd.S1_18.map_id@1cd85d8e
 `F(RS)=F(R)F(S)` #src[] #h(1cm)
    // lean:Freyd.S1_18.map_comp@ab212d4e
 `R⊑S⟹F(R)⊑F(S)` #src[]]
    // lean:AOP.A5_1.map_mono@308d5798
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
 [For `f` a map, `F(f)` is a map and `F(f°)=F(f)°`. #src[]],
  // lean:AOP.A5_1.map_is_map@8f150beb lean:AOP.A5_1.map_recip_map@c9f5d6f2
  // functor-is-relator row: Theorem 5.1
  [Over a *tabular* allegory a functor is a relator `⟺` it preserves `°`.],
  // F(R°)=F(R)° row: after Theorem 5.1, p. 113
  [`F(R°)=F(R)°` for every `R`, so `F(R)°` needs no bracket.],
  // relators-agree-on-maps row: Corollary 5.1
  [Two relators agreeing on maps are equal.],
 // F(X∩Y) row: Ex 5.2
 [`F(X∩Y)=F(X)∩F(Y)` for `X,Y` coreflexive. #src[]],
  // lean:AOP.A5_1.map_inter_coreflexive@a2233804
 // F(R∩S) row: Ex 5.2, the restriction
 [`F(R∩S)⊑F(R)∩F(S)`, and strictly. #src[]],
  // lean:AOP.A5_1.map_inter_le@af565f80
 [`F(dom(R))=dom(F(R))` for `F` preserving `°`. #src[]],
  // lean:AOP.A5_1.map_dom@5e9ecd68
)]<relator-laws>

The *power relator* `P` — `xs P(R) ys⟺(∀a∈xs. ∃b∈ys. a R b)∧(∀b∈ys. ∃a∈xs. a R b)` — is where
the fourth is strict: for `R={(a₁,b₁),(a₂,b₂)}` and `S={(a₁,b₂),(a₂,b₁)}` the pair
`({a₁,a₂},{b₁,b₂})` is in `P(R)∩P(S)`, while `R∩S=∅`.

== Fork `⟨R,S⟩`

#disp[#definition[
The *fork* of `R : C⟶A` and `S : C⟶B` is `⟨R,S⟩≜Rπ₁°∩Sπ₂°` #src[],
// lean:AOP.A5_2.Freyd.Alg.RelProd.pair@df1791ca
where `(π₁,π₂)` is the tabulation of `⊤`
#src[].
// lean:AOP.A5_2.eq_topMor@31e6622f lean:AOP.A5_2.joint_id@f9cba0f7
]]<fork-defn>

#disp[#block(inset: (y: 6pt))[
 `⟨R,S⟩π₁=dom(S)R` #src[] #h(1.4cm)
  // lean:AOP.A5_2.pair_outl@18c8ddee
 `⟨R,S⟩π₂=dom(R)S` #src[]
  // lean:AOP.A5_2.pair_outr@ce99887d
]]<fork-proj>

#disp[#row((box(inset: (right: 18pt),
  leancd("Freyd.Alg.RelProd.pair_outl_le+Freyd.Alg.RelProd.pair_outr_le")), lean("Freyd.Alg.RelProd.pair")))]<fork-pic>

A domain is coreflexive, so `⟨R,S⟩π₁⊑R`, with equality exactly when `S` is entire; for maps both
triangles commute and `⟨f,g⟩` is unique. In `Rel`, `c ⟨R,S⟩ (a,b)` iff `c R a` and `c S b` — copy `c`, then
`R` on one strand and `S` on the other, which is `◁(R⊗S)` on the right.

No `°` survives the translation. `π₁=𝟙⊗⊸` discards the second component, so `π₁°=𝟙⊗⟜`
*creates* one out of nothing, and `∩` is copy, run both, merge. Draw that and the created strands —
the two dots with no left end, and the crossing they force — are merged against real ones, which is
the monoid's unit law:

// The chain at FULL size: `chain`'s 62% is calibrated for the exported pictures, which are drawn on a
// bigger canvas than these two.
#disp[#leanc("Freyd.Alg.RelProd.pair") #src[`⟜▷=𝟙` on each half]]<fork-collapse>
// lean:AOP.A5_2.Freyd.Alg.RelProd.pair@df1791ca


=== Relational product `R×S`

#disp[#definition[
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
#disp[#leanc("Freyd.Alg.RelProd.pair_prodMap.rhs")]<absorption-pic>
// lean:AOP.A5_2.pair_prodMap@8861fda2

// One run of boxes on one strand, for the book tables below: `"r"` a relation (chamfered), `"m"` a
// map (square), `"c"` a converse (mirrored and tinted).  Twenty inline copies is twenty chances to drift.
#let BOXW = 0.92
#let BOXG = 0.34
#let brun(x, y, items, w: BOXW) = {
  let cx = x + BOXG
  wire((x, y), (cx, y))
  for (i, it) in items.enumerate() {
    gbox((cx, y), it.at(0), w: w, chamfer: it.at(1) != "m", flip: it.at(1) == "c",
      fill: if it.at(1) == "c" { TINT } else { none })
    cx = cx + w
    if i + 1 < items.len() { wire((cx, y), (cx + BOXG, y)); cx = cx + BOXG }
  }
  wire((cx, y), (cx + BOXG, y))
}

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

  [], P(lean("Freyd.Alg.prodMap"), s: 74%),
  // lean:AOP.A5_2.prodMap@28e34ad0

  [#src[both sides are the same strokes — @absorption-pic. Its `⊑`
// R×S row: ⊑ half is Ex 5.8, B&dM's (5.4),(5.5); (R×S)(U×V) corollary is Ex 5.6
   half is that half at `S:=𝟙` and at `R:=𝟙` — stages of their proof of
   this row; the corollary is the `(R×S)(U×V)=(RU)×(SV)` it yields, at `R:=𝟙` and `V:=𝟙`.
 ]],
   // lean:AOP.A5_2.pair_prodMap@8861fda2
  P(lean("Freyd.Alg.RelProd.pair_prodMap"), s: 74%),

 [#src[@fork-proj]],
  // lean:AOP.A5_2.pair_outl@18c8ddee
  P(lean("Freyd.Alg.RelProd.pair_outl"), s: 74%),

 [#src[@fork-proj]],
  // lean:AOP.A5_2.pair_outr@ce99887d
  P(lean("Freyd.Alg.RelProd.pair_outr"), s: 74%),

 [#src[]],
  // lean:AOP.A5_2.pair_recip_pair@7b967917
  P(lean("Freyd.Alg.RelProd.pair_recip_pair"), s: 74%),

  [#src[]],
  // lean:AOP.A5_2.recip_pair_pair_le@3e24af96
  P(lean("Freyd.Alg.RelProd.recip_pair_pair_le"), s: 74%),

  [#leanf("Freyd.Alg.RelProd.map_comp_pair") \ #src[`f` a map; it fails for an arbitrary arrow;
 ]],
   // lean:AOP.A5_2.map_comp_pair@4056dfe1
  P(lean("Freyd.Alg.RelProd.map_comp_pair"), s: 74%),

  [`F(R×S)unzip(F)=unzip(F)(F(R)×F(S))` \ #src[`unzip(F)≜⟨F(π₁),F(π₂)⟩`, a map]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.75
    lab(-1.4, 0, black)[`F(C×D)`]
    wire((-0.45, 0), (0, 0)); gbox((0, 0), [`F(R×S)`], w: 1.9); wire((1.9, 0), (2.25, 0))
    // ONE box with two wires out: `unzip(F)` is where a relator's `F(C×D)` becomes the pair `F C×F D`.
    gbox((2.25, 0), [`unzip(F)`], w: 2.2, h: 2 * y + 0.5, chamfer: false)
    wire((4.45, y), (4.85, y)); wire((4.45, -y), (4.85, -y))
    lab(5.3, y, black)[`FA`]; lab(5.3, -y, black)[`FB`]
    lab(5.95, 0, black)[$=$]
    lab(7.0, 0, black)[`F(C×D)`]
    wire((7.85, 0), (8.2, 0))
    gbox((8.2, 0), [`unzip(F)`], w: 2.2, h: 2 * y + 0.5, chamfer: false)
    wire((10.4, y), (10.8, y)); gbox((10.8, y), [`FR`], w: 1.2); wire((12.0, y), (12.35, y))
    wire((10.4, -y), (10.8, -y)); gbox((10.8, -y), [`FS`], w: 1.2); wire((12.0, -y), (12.35, -y))
    lab(12.8, y, black)[`FA`]; lab(12.8, -y, black)[`FB`]
  }), s: 70%),

  [`g=curry(f)⟺(g×𝟙)eval=f` \ #src[reading `×` as the relational product, does `Rel`
   have exponentials?]],
  [],
)]<bdm-prod-laws>

== Coproduct `[R,S] : A+B⟶C` <sec-coprod>

// THE DEFINITION, DRAWN, and it needs no new generator: `+` is a UNION, already drawn as the tape of
// the laws above.  A TAPE ONLY WHERE THERE IS A `∪`, which is why two of the three shape rows have none.
#disp[#table(
  columns: (1fr, 10.5cm),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*the statement*], [*picture*]),

  [#src[The tape is the union — a particle entering at `A+B` takes exactly
   one branch — and the two mirrored boxes are what makes the branches disjoint.]],
  // lean:AOP.A5_3.junc@da022f10
  P(lean("Freyd.Alg.junc"), s: 85%),

  [#src[]], P(lean("Freyd.Alg.junc_eq_Λ_junc_eps"), s: 85%),
  // lean:AOP.A5_3.junc_eq_Λ_junc_eps@2e29215d
  [], P(lean("Freyd.Alg.sumMap"), s: 85%),
  // lean:AOP.A5_3.sumMap@eb035ed1
  [#leanf("Freyd.Alg.u₁_junc"), #leanf("Freyd.Alg.u₂_junc") \ #leanf("Freyd.Alg.junc_unique")
 #src[,
   // lean:AOP.A5_3.u₁_junc@a01a115a lean:AOP.A5_3.u₂_junc@e692ee94
 ]], [],
   // lean:AOP.A5_3.junc_unique@192cec99

  [], P(row((lean("Freyd.Alg.Coproduct.u₁_self_comp_recip"),
    lean("Freyd.Alg.Coproduct.u₂_self_comp_recip"))), s: 85%),
  // lean:Freyd.S2_20.Coproduct.u₁_self_comp_recip@6cd82772
  // lean:Freyd.S2_20.Coproduct.u₂_self_comp_recip@53e6991d

  // `rl°=𝟘` stays a formula: the exporter finds no naturality for the `𝟘` family on `B⟶A`.
  [#leanf("Freyd.Alg.Coproduct.u₂_u₁_recip")], P(lean("Freyd.Alg.Coproduct.u₁_u₂_recip"), s: 85%),
  // lean:Freyd.S2_20.Coproduct.u₁_u₂_recip@ade7327c lean:Freyd.S2_20.Coproduct.u₂_u₁_recip@61def7d7

  [], P(lean("Freyd.Alg.Coproduct.recip_union_eq_id"), s: 85%),
  // lean:Freyd.S2_20.Coproduct.recip_union_eq_id@6443cb0e

  [], P(lean("Freyd.Alg.junc_recip_junc"), s: 85%),
  // lean:AOP.A5_3.junc_recip_junc@838f4abc
)]<coprod-laws>

=== `[R,S]≜[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]∋`

// B&dM §5.3, pp. 117-118, mirrored into this note's diagram order: why the universal property holds
// with equality where the fork's triangles above only hold up to `Dom`.
The universal-property row is not free: `l,r` were only ever asked to be a coproduct of *maps*. They stay one
once every arrow is allowed because $frac(#box(width: 8pt), ∋)$ sends an arrow `A⟶C` to a map `A⟶EC` reversibly, so the
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
 // lean:AOP.A5_3.Λ_junc@d392c2aa lean:AOP.A5_3.junc_map@b2d62c40
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

  // [R,S]=(l°R) ∪ (r°S): B&dM (5.9)
  [#src[@coprod-laws's first row]],
  // lean:AOP.A5_3.junc@da022f10
  P(lean("Freyd.Alg.junc"), s: 82%),

  // R+S=[Rl,Sr]: B&dM (5.10)
  [],
  // lean:AOP.A5_3.sumMap@eb035ed1
  P(lean("Freyd.Alg.sumMap"), s: 82%),

  // [U,V]°[R,S]=(U°R) ∪ (V°S): B&dM (5.11)
  [#src[@coprod-laws's last row;
 ]],
   // lean:AOP.A5_3.junc_recip_junc@838f4abc
  P(lean("Freyd.Alg.junc_recip_junc"), s: 68%),

  // X≜[𝟙,𝟘]=l° and Y≜[𝟘,𝟙]=r°, so (Xl) ∪ (Yr)=[l,r]=𝟙: B&dM Ex 5.12
  [#leanf("Freyd.Alg.junc_id_zero"), #leanf("Freyd.Alg.junc_zero_id") \
   #leanf("Freyd.Alg.junc_injections") \ #src[which is (5.9)]],
  // lean:AOP.A5_3.junc_id_zero@28919704 lean:AOP.A5_3.junc_zero_id@328e3c31
  // lean:AOP.A5_3.junc_injections@11d515bf lean:Freyd.S2_20.Coproduct.recip_union_eq_id@6443cb0e
  P(lean("Freyd.Alg.Coproduct.recip_union_eq_id"), s: 78%),

  // prove (5.11), and say why duality does not carry it over from the product law: B&dM Ex 5.13
  [#src[prove (5.11), and say why duality does not carry it over from the product law]],
  [],

  // row: Ex 5.14
  [`(R+S)∩([P,Q][U,V]°)` \ `=(R∩(PU°))+(S∩(QV°))` \ #src[`[P,Q][U,V]°` is a full 2×2 of
   composites; `R+S` is diagonal, so the meet cuts the two off-diagonal branches]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62
    let t = 1.5
    wcopy((0.6, 0), li: 0.5, lo: 0.8, sp: t)
    tape((1.4, t - 1.05), (6.22, t + 1.05))
    tape-fork((1.62, t), sp: y, len: 0.42)
    gbox((2.04, t + y), [`l`], flip: true, fill: TINT); wire((2.96, t + y), (3.30, t + y))
    gbox((3.30, t + y), [R]); wire((4.22, t + y), (4.56, t + y))
    gbox((4.56, t + y), [`l`], chamfer: false); wire((5.48, t + y), (5.58, t + y))
    gbox((2.04, t - y), [`r`], flip: true, fill: TINT); wire((2.96, t - y), (3.30, t - y))
    gbox((3.30, t - y), [S]); wire((4.22, t - y), (4.56, t - y))
    gbox((4.56, t - y), [`r`], chamfer: false); wire((5.48, t - y), (5.58, t - y))
    tape-join((6.00, t), sp: y, len: 0.42)
    wire((6.22, t), (9.16, t))
    tape((1.4, -t - 1.05), (4.96, -t + 1.05))
    tape-fork((1.62, -t), sp: y, len: 0.42)
    gbox((2.04, -t + y), [`l`], flip: true, fill: TINT); wire((2.96, -t + y), (3.30, -t + y))
    gbox((3.30, -t + y), [P]); wire((4.22, -t + y), (4.32, -t + y))
    gbox((2.04, -t - y), [`r`], flip: true, fill: TINT); wire((2.96, -t - y), (3.30, -t - y))
    gbox((3.30, -t - y), [Q]); wire((4.22, -t - y), (4.32, -t - y))
    tape-join((4.74, -t), sp: y, len: 0.42)
    wire((4.96, -t), (5.60, -t))
    tape((5.60, -t - 1.05), (9.16, -t + 1.05))
    tape-fork((5.82, -t), sp: y, len: 0.42)
    gbox((6.24, -t + y), [U], flip: true, fill: TINT); wire((7.16, -t + y), (7.50, -t + y))
    gbox((7.50, -t + y), [`l`], chamfer: false); wire((8.42, -t + y), (8.52, -t + y))
    gbox((6.24, -t - y), [V], flip: true, fill: TINT); wire((7.16, -t - y), (7.50, -t - y))
    gbox((7.50, -t - y), [`r`], chamfer: false); wire((8.42, -t - y), (8.52, -t - y))
    tape-join((8.94, -t), sp: y, len: 0.42)
    wmerge((9.96, 0), li: 0.8, lo: 0.5, sp: t)
    lab(11.2, 0, black)[$=$]
    wire((11.66, 0), (12.0, 0))
    tape((12.0, -2.25), (20.3, 2.25))
    tape-fork((12.22, 0), sp: 1.1, len: 0.42)
    for (b, u, fwd, cnv, i) in ((1.1, [R], [P], [U], [`l`]), (-1.1, [S], [Q], [V], [`r`])) {
      gbox((12.64, b), i, flip: true, fill: TINT)
      wcopy((14.0, b), li: 0.44, lo: 0.5, sp: y)
      brun(14.5, b + y, ((u, "r"),)); wire((16.1, b + y), (17.36, b + y))
      brun(14.5, b - y, ((fwd, "r"), (cnv, "c")))
      wmerge((17.86, b), li: 0.5, lo: 0.44, sp: y)
      gbox((18.30, b), i, chamfer: false); wire((19.22, b), (19.32, b))
    }
    tape-join((19.74, 0), sp: 1.1, len: 0.42)
    wire((20.3, 0), (20.64, 0))
  }), s: 62%),
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
 [`P(R)≜`], [`((∋R)/∋)∩((∋R°)/∋)° : EA⟶EB` #src[]],
  // lean:AOP.A5_4.powerRel@80c5b402
 [`E(R)≜` $frac(#[`∋R`], ∋)$ `=`], [`((∋R)/∋)∩(∋/(∋R))°` #src[]],
  // lean:AOP.A4_6.existsImage@db266886
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
))]<powrel-readings>

// `1,2,3` on the left, `a,b,c` on the right — and the `skel` pictures below are a DIFFERENT example,
// where `a₁,a₂,a₃` is the source, not the target. Only this one has the empty image `R(2) = ∅`.
#disp[#block(breakable: false)[
#align(center, box(cetz.canvas(length: 0.8cm, {
  let (L, RC) = (0, 3.2)
  let ys = (1.0, 0, -1.0)
  ar((L, ys.at(0)), (RC, ys.at(0)), GIVEN1, s0: 0.22, s1: 0.3)
  ar((L, ys.at(0)), (RC, ys.at(1)), GIVEN1, s0: 0.22, s1: 0.3)
  ar((L, ys.at(2)), (RC, ys.at(2)), GIVEN1, s0: 0.22, s1: 0.3)
  for (k, y) in ys.enumerate() {
    wiredot((L, y)); lab(L - 0.42, y, black)[#raw(str(k + 1))]
    wiredot((RC, y)); lab(RC + 0.42, y, black)[#raw(("a", "b", "c").at(k))]
  }
  lab((L + RC) / 2, 1.5, GIVEN1)[`R`]
  lab(L, -1.7, black)[`A`]; lab(RC, -1.7, black)[`B`]
})))

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
   // lean:AOP.A5_4.powerRel_mono@00de2d62

  [`P(𝟙)=` $frac(∋, ∋)$ `=𝟙`],
  [The straightness axiom verbatim: extensionality *is* `P`'s unit law.
 #src[]],
   // lean:AOP.A5_4.powerRel_id@4ada24f9

  [`P(f)=` $frac(∋ f, ∋)$, for `f` a map],
  [In `Rel`, `xs P(f) ys⟺ys={f(a)|a∈xs}`. The half at `f°` says every `a∈xs` has its `f(a)` on
   `ys`; `f` has just the one image per `a`, so that already says `ys` contains everything `xs`
   reaches, which is the fraction's second half. For a map the two definitions coincide.
 #src[]],
   // lean:AOP.A5_4.powerRel_map@2bf77d9f

  [`P(RS)=P(R)P(S)`],
  [`⊒` is the division cancellation laws. `⊑` is the one law in this section that is not a
 calculation: it needs a tabulation of `P(RS)`. #src[]],
   // lean:AOP.A5_4.powerRel_comp@06364064
)]<powrel-laws>

// Ahead of §11.4 and §11.5, which both write `⦇…⦈` before anything says what it is.  The three
// squares are the one geometry: algebras across the rows, homomorphisms down the columns.
#pagebreak(weak: true)
== Initial algebra

// §11.4's panels, emitted by `./scripts/diagram --sigs … --src … --tgt … "<formula>"` plus `s: 100%`,
// the squares' own size.  An algebra is an ARROW AT ITS CARRIER — `f : F(A)⟶A`, `α : F(T)⟶T`, B&dM
// (2.10) — so its bead spans the object wire and carries no dot; only the type functor's `αᴀ`
// (@tfun-defn), a family over the parameter `A`, is a transformation and draws on the functor lane.
#let ia-hom-l = lean("Freyd.Alg.IsFHom.lhs")
#let ia-hom-r = lean("Freyd.Alg.IsFHom.rhs")
#let ia-cata-l = lean("Freyd.Alg.InitialAlgebra.cata_comm.lhs")
#let ia-cata-r = lean("Freyd.Alg.InitialAlgebra.cata_comm.rhs")

#disp[#definition[
An *F-algebra* is a map `f : F(A)⟶A`; `A` is its *carrier*.
An *F-homomorphism* from `f : F(A)⟶A` to `g : F(B)⟶B` is a map `h : A⟶B` with `f h=F(h)g`.
The *initial algebra* `α : F(T)⟶T` is the F-algebra with exactly one F-homomorphism `⦇f⦈ : T⟶A` to
every F-algebra `f`
#src[].
// lean:AOP.A5_5.InitialAlgebra@a45a8436

  // ONE OBJECT, ONE HUE down the display: `A` is amber in both rows.  The positional defaults would
  // paint the same carrier red in the row below and cyan in the row above.
  #pair(
    leancd("Freyd.Alg.IsFHom"),
    row((ia-hom-l, [#h(7pt) = #h(7pt)], ia-hom-r)),
    [`f h=F(h)g , h:f->g in Alg(F)`],
  )
  #pair(
    leancd("Freyd.Alg.InitialAlgebra.cata_comm"),
    row((ia-cata-l, [#h(7pt) = #h(7pt)], ia-cata-r)),
    [`α⦇f⦈=F(⦇f⦈)f,  ⦇f⦈:α->f in Alg(F)`],
  )
  // lean:AOP.A5_5.relCata_cancel@957f4846
]]<initial-defn>

=== Reflection

// THE LAW ITSELF, not the square that proves it.  The identity natural transformation "is represented by
// the edge for the corresponding functor" (IntroString p. 37), so the right of the `=` is the `T` wire
// alone in its grey `𝟏` box — a panel with no bead, not an empty cell.  The `T` on the wire under the
// bead is the fold's carrier: this is the fold of the initial algebra itself, `α : F(T)⟶T`.
#let ia-refl-l = lean("Freyd.Alg.relCata_alpha.lhs")
#let ia-refl-r = lean("Freyd.Alg.relCata_alpha.rhs")

#disp[#pair(
  leancd("Freyd.Alg.relCata_alpha"),
  row((ia-refl-l, [#h(7pt) = #h(7pt)], ia-refl-r)),
 [`⦇α⦈=𝟙` #h(6pt) #src[(2.11)]],
)]<cata-reflection>

// `relCata_alpha`, AOP/A6_3.lean:40.
Taking a value apart with `α` and putting it straight back is doing nothing.

=== Fusion: ⦇R:FB⦈ absorb S:R->Q (in Alg(F) ) and becomes ⦇Q⦈ 

// `T` is already the initial algebra's carrier, so the two algebras of the law take their own letters,
// `R` on `B` and `Q` on `C`; `S` is the homomorphism between them, not an algebra.
When `S : B⟶C` is an F-homomorphism from `R : F(B)⟶B` to `Q : F(C)⟶C`, folding with `R` and
then applying `S` is folding with `Q`.

// `s: 92%`: the one row that does not fit at full size.  The side condition is the homomorphism
// square of @initial-defn at `f := R`, `g := Q`, `h := S`.
#let ia-fuse-l = lean("Freyd.Alg.relCata_fusion#h.lhs")
#let ia-fuse-r = lean("Freyd.Alg.relCata_fusion#h.rhs")
// The conclusion, generated like the side condition above it: the two folds differ by their algebra,
// and the wire under each says where it lands — `B` on the left, `C` on the right.
#let ia-fuse-cl = lean("Freyd.Alg.relCata_fusion.lhs")
#let ia-fuse-cr = lean("Freyd.Alg.relCata_fusion.rhs")

#disp[#pair(
  leancd("Freyd.Alg.relCata_fusion"),
  grid(
    columns: 2, align: horizon, column-gutter: 16pt, row-gutter: 10pt,
    src[the side condition],
    row((ia-fuse-l, [#h(7pt) = #h(7pt)], ia-fuse-r)),
    src[the conclusion],
    row((ia-fuse-cl, [#h(7pt) = #h(7pt)], ia-fuse-cr)),
  ),
  [`⦇R⦈S=⦇Q⦈⟸R S=F(S)Q` #h(6pt)
 #src[(2.12)]],
  s: 92%,
)]<cata-fusion>

// Its own page: the definition below only says what `T(R)` is, and the square after it is the reason
// that arrow exists, so the two have to be read together — under the picture above they would not be.
#pagebreak(weak: true)
== Type relator

#disp[#definition[
Let `F` be a binary relator with initial type `(α,T)`, so `T` is a type functor. `F(R,S)` is its
action on a pair, and `F(X)` abbreviates `F(𝟙,X)`, the `F` of the reduce section. For every object
`A` the initial algebra is `α : F(A,TA)⟶TA`, among the maps. `T` acts on an arrow `R : A⟶B` by

  #align(center, block(inset: (y: 6pt))[`T(R)=⦇F(R,𝟙)α⦈ : TA⟶TB` #h(4pt)
 #src[]])
    // lean:AOP.A5_5_TypeFunctor.typeMap@ce1f93d0 lean:AOP.A5_5_TypeFunctor.typeMap_defn@edbd9794
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
  [`T(R)=⦇F(R,𝟙)α⦈`],
  [Rebuild the structure with `α`, applying `R` to the parameter on the way.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_defn@edbd9794

  [functor],
  [`T(𝟙)=𝟙` and `T(R)T(S)=T(RS)`],
  [Acting by the identity changes nothing, and two actions in a row are one action.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_id@e509bbf1 lean:AOP.A5_5_TypeFunctor.typeMap_comp@c9ae6abd

  [type functor fusion],
  [`T(R)⦇Q⦈=⦇F(R,𝟙)Q⦈`],
  [A relator action followed by a fold is a single fold — the intermediate structure is never built.
   The side condition holds because `F` is a bifunctor —
   `F(R,𝟙)F(𝟙,⦇Q⦈)=F(R,⦇Q⦈)=F(𝟙,⦇Q⦈)F(R,𝟙)`.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_fusion@7d2c6178 lean:AOP.A5_5_TypeFunctor.interchange@cc0eb4af

  [naturality of `α`],
  [`αT(R)=F(R,T(R))α`],
  [Building and then mapping is the same as mapping the parts and then building, so `α` is natural
   from `G(R)=F(R,T(R))` to `T`.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.alpha_natural@02d77e92

  [type relator],
  [`T(R)°=T(R°)`, for `F` preserving `°`],
  [A datatype acts on relations, not only on maps — the map of the converse is the converse of the
   map.
 #h(4pt) #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_recip@4bb90fe1
)]<tf-laws>

// Its own page: the definition and its two squares are read together, and without the break the
// fusion square is the only one of the three on the next page.
#pagebreak(weak: true)
=== Type functor

#disp[#definition[
Let `F` be a bifunctor taking both the parameter `A` and the recursive position `TA`, with an initial
algebra `α`#sub[`A`]` : F(A,TA)⟶TA` for every object `A`. Then `T` is a functor, acting on a map
`f : A⟶B` by

  #align(center, block(inset: (y: 6pt))[`T(f)≜⦇F(f,𝟙)α`#sub[`B`]`⦈ : TA⟶TB` #h(4pt)
 #src[]])
    // lean:AOP.A5_5_TypeFunctor.typeMap@ce1f93d0
]]<tfun-defn>

// The square is the five arrows `alpha_natural_split` states; the algebra `F(f,𝟙)α_B` is the path
// through `F(B,TB)`, not a sixth arrow, because the statement names no such composite.
// TWO WIRES, not one indexed `F`: `⟨𝟙,T⟩ : 𝒜⟶𝒜×𝒜` packs the two arguments and `F : 𝒜×𝒜⟶𝒜` is then
// unary, so every wire is a functor again and the region between them is `𝒜×𝒜`.  That is what makes
// `F(f,T(f))` free — it is `f` on the object wire with `⟨𝟙,T⟩` and `F` running past — and the law the
// naturality of `α`, the `f` bead sliding past it.  Not `P`, which is the powerset relator already.
// This REPLACES the 2026-08-26 unindexed-`F` exception, which needed a second bead `F(f,𝟙)`.
#let tfun-l = lean("Freyd.Alg.alphaT_natural.lhs")
#let tfun-r = lean("Freyd.Alg.alphaT_natural.rhs")
#disp[#pair(
  leancd("Freyd.Alg.alpha_natural_split"),
  row((tfun-l, [#h(7pt) = #h(7pt)], tfun-r), s: 92%),
  [`α`#sub[`A`]` T(f)=F(f,T(f))α`#sub[`B`] #h(6pt)
 #src[]],
)]<tfun-sq>

- `F : 𝒜×𝒜⟶𝒜` is a bifunctor and a wire is a unary functor, so the two arguments are packed first:
  `⟨𝟙,T⟩ : 𝒜⟶𝒜×𝒜` sends `A` to `(A,TA)`, and `F(⟨𝟙,T⟩(A))` is `F(A,TA)`.
- The picture is three wires — `F`, `⟨𝟙,T⟩`, and the object — and the region between the first two
  is `𝒜×𝒜`.
- `α` is then an ordinary natural transformation `F∘⟨𝟙,T⟩⇒T`: its bead eats the `F` and `⟨𝟙,T⟩` wires,
  and the `T` wire is born under it.
- `F(f,T(f))` costs no notation. It is the bead `f` on the object wire with `⟨𝟙,T⟩` and `F` running
  past: `⟨𝟙,T⟩` is what turns `f` into the pair `(f,T(f))`, and `F` is what applies it.
- The law is the naturality of `α`, which is exactly the freedom to slide that `f` bead past it.

// The defining square of `⦇F(f,𝟙)h⦈`, its right column drawn twice: straight down as the one fold, and
// bowed out through `TB` as `T(f)` then `⦇h⦈`.  That the two paths agree IS the law.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
  let (FA, TA) = ((-3, 2.0), (3, 2.0))
  let TB = (5.6, 0)
  let (FC, C) = ((-3, -2.0), (3, -2.0))
  ar(FA, TA, GIVEN2, s0: 1.45, s1: 0.65); ar(FC, C, GIVEN1, s0: 1.45, s1: 0.5)
  ar(FA, FC, INDUCED, s0: 0.55, s1: 0.55)
  ar(TA, C, INDUCED, dash: "dashed", s0: 0.55, s1: 0.5)
  ar(TA, TB, INDUCED, dash: "dashed", s0: 0.55, s1: 0.6)
  ar(TB, C, INDUCED, dash: "dashed", s0: 0.6, s1: 0.55)
  lab(0.4, 2.55, GIVEN2)[`α`#sub[`A`]]; lab(0.4, -2.55, GIVEN1)[`F(f,𝟙)h`]
  lab(-5.15, 0, INDUCED)[`F(𝟙,⦇F(f,𝟙)h⦈)`]; lab(1.25, 0, INDUCED)[`⦇F(f,𝟙)h⦈`]
  lab(4.67, 1.47, INDUCED)[`T(f)`]; lab(4.67, -1.47, INDUCED)[`⦇h⦈`]
  node(FA.at(0), FA.at(1), black, `F(A,TA)`); node(TA.at(0), TA.at(1), black, `TA`)
  node(TB.at(0), TB.at(1), black, `TB`)
  node(FC.at(0), FC.at(1), GIVEN1, `F(A,C)`); node(C.at(0), C.at(1), GIVEN1, `C`)
  }),
  row((
    lean("Freyd.Alg.typeMap_fusion"),
  )),
  [`T(f)⦇h⦈=⦇F(f,𝟙)h⦈` #h(6pt)
 #src[]],
)]<tfun-fusion>

// Its own page: otherwise the heading lands as the last line under the power relator's table, an orphan
// a page away from the definition it names, and the defining square below straddles the break.
#pagebreak(weak: true)
// B&dM and Freyd call this a catamorphism; the note says reduce, after q's `/`.
== Reduce <sec-cata>

#disp[#definition[
let `F` be a relator and has  *initial algebra* `α : F(T)⟶T` in the subcategory of functions.
`α` is also initial in the allegory:
]]<cata-defn>


=== The defining equation

// A WIRE'S COLOUR IS ITS TYPE, A BEAD'S COLOUR IS WHICH ARROW IT IS, so arrows carry over from the
// square.  The string half is generated, on @initial-defn's two panels at `⦇f⦈ := X`: two ALGEBRAS,
// `α` at `T` and `f` at `A`, each an arrow at its own carrier and so a bead on the object wire.
#let cata-def-l = lean("Freyd.Alg.relCata_UP.lhs.lhs")
#let cata-def-r = lean("Freyd.Alg.relCata_UP.lhs.rhs")
#disp[#pair(
  leancd("Freyd.Alg.relCata_UP.lhs"),
  row((cata-def-l, [#h(7pt) = #h(7pt)], cata-def-r)),
  [`X=⦇f⦈⟺αX=F(X)f` #h(6pt)
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
  // lean:AOP.A6_ConsList.initial@0ebba980

  [the fold, pointwise],
  [`⦇[c,f]⦈(zero)=c` \ `⦇[c,f]⦈(succ(n))=f(⦇[c,f]⦈(n))`],
  [`⦇[c,f]⦈(nil)=c` \ `⦇[c,f]⦈(cons(a,x))=f(a,⦇[c,f]⦈(x))`],
)]<cata-initial>


=== `⦇R⦈=⦇`$frac(#[`F(∋)R`], ∋)$`⦈∋`

// B&dM p.121's figure, mirrored: @cata-defining's square at `f := `#frc([`F(∋)R`])`, `A := E A`,
// over the ∋/F(∋) rows and the relation `R` — the renamed arrows are the two induced ones and the bottom row.
// Generated, on the defining equation above at `X := ⦇`#frc([`F(∋)R`])`⦈`: the `E` wire is BORN at the
// banana, `T⟶EA` being where the power object enters.  TWO ALGEBRAS, `α : F(T)⟶T` and `f : F(EA)⟶EA`.
#let cata-map-l = lean("Freyd.Alg.Λ_relCata.lhs")
#let cata-map-r = lean("Freyd.Alg.Λ_relCata.rhs")
#disp[#pair(
  grid(columns: 1, align: center, row-gutter: 6pt,
  cetz.canvas(length: 0.8cm, {
    let (FT, T) = ((-2.6, 1.5), (2.6, 1.5))
    let (FE, E) = ((-2.6, -1.2), (2.6, -1.2))
    let (FA, A) = ((-2.6, -3.9), (2.6, -3.9))
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FE, E, GIVEN1, s0: 0.55, s1: 0.55)
    ar(FA, A, black, s0: 0.55, s1: 0.55)
    ar(FT, FE, INDUCED, s0: 0.55, s1: 0.55)
    ar(T, E, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
    ar(FE, FA, black, s0: 0.55, s1: 0.55)
    ar(E, A, black, s0: 0.55, s1: 0.55)
    lab(0, 2.05, GIVEN2)[`α`]
    lab(-4.6, 0.15, INDUCED)[`F(⦇`$frac(#[`F(∋)R`], ∋)$`⦈)`]
    lab(4.2, 0.15, INDUCED)[`⦇`$frac(#[`F(∋)R`], ∋)$`⦈`]
    lab(0, -0.65, GIVEN1)[`f`]
    lab(0, -1.95, GIVEN1)[$frac(#[`F(∋)R`], ∋)$]
    lab(-4.0, -2.55, black)[`F(∋)`]; lab(3.6, -2.55, black)[`∋`]
    lab(0, -4.45, black)[`R`]
    node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
    node(FE.at(0), FE.at(1), GIVEN1, `F(EA)`); node(E.at(0), E.at(1), GIVEN1, `EA`)
    node(FA.at(0), FA.at(1), GIVEN1, `FA`); node(A.at(0), A.at(1), GIVEN1, `A`)
  }),
  src[$frac(#[`𝟙`], ∋)$ is the inverse of `∋`]),
  row((cata-map-l, [#h(7pt) = #h(7pt)], cata-map-r)),
  [`α⦇`$frac(#[`F(∋)R`], ∋)$`⦈=F(⦇`$frac(#[`F(∋)R`], ∋)$`⦈)` $frac(#[`F(∋)R`], ∋)$
 #src[]],
   // lean:AOP.A5_5.Λ_relCata@5b63ea5d lean:AOP.A5_5.relCata_unfold@22ba1c5c
)]<cata-map-square>

// B&dM (5.12), p. 121, mirrored into this note's diagram order.  A row too wide for the column wraps,
// and the next row opens with the `⟺` that carries it over.
#disp[
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
 // lean:AOP.A5_5.Λ_relCata@5b63ea5d lean:AOP.A5_5.relCata_unfold@22ba1c5c
]<cata-map-calc>

// The step-table helpers, hoisted above §@sec-mu, the first section that uses them: a Typst `#let`
// binds only below its line.  The step's relation sits at the LEFT EDGE of formula AND picture, so
// both read as chains: `⊑`/`⊒` takes `SLACK` where the proof loses information, `=` stays grey.
#let SQ = text(SLACK)[$subset.eq.sq$]
#let RQ = text(SLACK)[$supset.eq.sq$]







// Otherwise the heading lands alone at the foot of the reduce-of-maps page.
#pagebreak(weak: true)
=== `φ(Y)⊑Y⟹(μX : φ(X))⊑Y` <sec-mu>

// B&dM Theorem 6.1, p. 140.  `μ` is read off a whole chapter of specifications from §@sec-dp on,
// and nothing before this said what it was.
#disp[#definition[
`φ` a *monotonic* mapping of the hom-set `A⟶B` into itself: #h(4pt) `X⊑Y⟹φ(X)⊑φ(Y)`
#src[].
// lean:AOP.A6_2.Monotonic@66dddf1e

`(μX : φ(X))` the least `X : A⟶B` with #h(4pt) `φ(X)⊑X` #src[].
// lean:AOP.A6_2.mu@4928a490
]]<mu-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

 // μX upper bound row: Theorem 6.1
 [`φ(Y)⊑Y⟹(μX : φ(X))⊑Y` \ #src[]],
  // lean:AOP.A6_2.mu_le@9918bd39
  [to bound `(μX : φ(X))` above, exhibit one `Y` the body does not grow past — the half §@sec-hylo
   and every chapter after it uses],
 // μX fixed point row: Theorem 6.1
 [`φ((μX : φ(X)))=(μX : φ(X))` \ #src[]],
  // lean:AOP.A6_2.mu_fixed@2d3d1a8a
  [*Knaster–Tarski*: the least solution of `φ(X)⊑X` already solves `φ(X)=X`, so the least prefix
   point and the least fixed point are one relation],
)]<mu-laws>

=== `⦇S⦈°⦇R⦈=(μX : S°F(X)R)` <sec-hylo>

// §@sec-hylo's panels, emitted by `./scripts/diagram --sigs … --src … --tgt … "<formula>"` plus
// `s: 100%`.  `sigs:` types the section's abstract letters; `frame: 5` is the ONE box every panel
// of the section draws in, so a step's two panels line up under `trow`'s `align: horizon`, and
// `top: 3` drops a lone bead to the height of the bead it stands against.
#let hy-body = lean("Freyd.Alg.hylo_fixed_step1.lhs")
#let hy-split = lean("Freyd.Alg.hylo_fixed_step1.rhs")
#let hy-alg = lean("Freyd.Alg.hylo_fixed_step2.rhs")
#let hy-alpha-iso = lean("Freyd.Alg.hylo_fixed_step3.rhs")
#let hy-cataR = lean("Freyd.Alg.hylo_le_of_prefixed_step1.lhs")
#let hy-rec = lean("Freyd.Alg.hylo_le_of_prefixed_step2.lhs")
#let hy-adj = lean("Freyd.Alg.hylo_le_of_prefixed_step3.lhs")
#let hy-fuse = lean("Freyd.Alg.hylo_le_of_prefixed_step4.lhs")
#let hy-prefix = lean("Freyd.Alg.hylo_le_of_prefixed#h.lhs")
// The right-hand side of a step: the one relation the chain is bounded by, at the height its
// partner's own bead keeps — `X` against @hylo-least's `S°F(X)R`, `⦇S⦈°\X` against `α°F(⦇S⦈°\X)R`.

// B&dM p. 142, mirrored into diagram order.  The `F` wire is born at the leading converse and dies
// at the trailing algebra; every step shortens it, and by the last panel it is gone.
#disp[#calc-table(cols: (1fr,), al: auto, 
  // hylo-fixed row: Theorem 6.2
  Thm(cols: 1)[`S°F(⦇S⦈°⦇R⦈)R=⦇S⦈°⦇R⦈` \
 #src[hylomorphism theorem: a prototypical 'divide and conquer' scheme — the term `S°` represents the
     decomposition stage, `F(⦇S⦈°⦇R⦈)` the stage of solving the subproblems recursively, and `R` the
     recombination stage; `R : FA⟶A`, `S : FB⟶B`, `α : FT⟶T` initial]],
    // lean:AOP.A6_3.hylo_fixed@42010f9f
  [#hchain(
    (none, hy-body, src[the body at `⦇S⦈°⦇R⦈`]),
    (EQ, hy-split, src[`F(RS)=F(R)F(S)` — @relator-defn]),
    (EQ, hy-alg, src[@cata-defining at `R`: `F(⦇R⦈)R=α⦇R⦈`]),
    (EQ, hy-alpha-iso, src[@cata-defining at `S` conversed: `⦇S⦈°α°=S°F(⦇S⦈)°`, and
     `F(⦇S⦈)°=F(⦇S⦈°)` — @relator-laws]),
    (EQ, lean("Freyd.Alg.hylo_fixed_step4.rhs"), src[`α°α=𝟙`: `α` is an iso]),
    // lean:AOP.A6_2.InitialAlgebra.recip_alpha_alpha@5a99c7f6
  )],
)]<hylo-fix>

// B&dM p. 143, mirrored.  Two adjunction steps carry `⦇S⦈°` out of the way and back, the reduce's
// own leastness fires between them, and the `F` wire's top end walks from `α°` up to `S°`.
#disp[#calc-table(cols: (1fr,), al: auto, 
 // hylo-least row: Theorem 6.2
 Thm(cols: 1)[`S°F(X)R⊑X⟹⦇S⦈°⦇R⦈⊑X` \
    #src[hylomorphism theorem: by Knaster–Tarski, the hylomorphism `⦇S⦈°⦇R⦈` is included in `X` if `X`
     satisfies the associated recursion inequation]],
  [#hchain(
    (none, lean("Freyd.Alg.hylo_le_of_prefixed.lhs", "Freyd.Alg.hylo_le_of_prefixed.rhs"),
     src[the conclusion]),
    (IFF, trow(hy-cataR, lean("Freyd.Alg.hylo_le_of_prefixed_step1.rhs")),
     src[@adj-all's `S·⊣S\` at `⦇S⦈°`]),
    (IMP, trow(hy-rec, lean("Freyd.Alg.hylo_le_of_prefixed_step2.rhs")),
     src[(6.2) `⦇R⦈=(μX : α°F(X)R)` — @cata-defining and @mu-laws;
 ]),
     // lean:AOP.A6_2.relCata_le_of_prefixed@9f98060a
    (IFF, trow(hy-adj, lean("Freyd.Alg.hylo_le_of_prefixed_step3.rhs")),
     src[@adj-all's `S·⊣S\` at `⦇S⦈°`]),
    (IFF, trow(hy-fuse, lean("Freyd.Alg.hylo_le_of_prefixed_step4.rhs")),
     src[`⦇S⦈°α°=S°F(⦇S⦈°)` — @hylo-fix]),
    (IMP, trow(hy-prefix, lean("Freyd.Alg.hylo_le_of_prefixed#h.rhs")),
     src[`F(RS)=F(R)F(S)` — @relator-defn — and `⦇S⦈°(⦇S⦈°\X)⊑X` — @adj-all]),
  )],
)]<hylo-least>

// The chain LEAVES `(μX : S°F(X)R)` and comes back to it, so everything on the way is equal: one
// `⊑` is @hylo-fix through @mu-laws, the other @hylo-least at the prefix point `μ` is.
#disp[#calc-table(cols: (1fr,), al: auto, 
 // hylo-fusion-eq row: Theorem 6.2
 Thm(cols: 1)[`⦇S⦈°⦇R⦈=(μX : S°F(X)R)` \
    #src[hylomorphism theorem: a hylomorphism is the least fixed point of a certain recursion equation]],
  // lean:AOP.A6_3.hylo_eq_mu@c60df971
  [#hchain(
    (none, lean("Freyd.Alg.hylo_eq_mu_step1.lhs"),
     src[@mu-defn at `φ(X):=S°F(X)R`]),
    (SQ, lean("Freyd.Alg.hylo_eq_mu_step1.rhs"),
     src[@mu-laws's `φ(Y)⊑Y⟹(μX : φ(X))⊑Y` at `Y:=⦇S⦈°⦇R⦈`, whose
 `S°F(⦇S⦈°⦇R⦈)R=⦇S⦈°⦇R⦈` is @hylo-fix]),
     // lean:AOP.A6_2.mu_le_of_fixed@8ea2332b
    (SQ, lean("Freyd.Alg.hylo_eq_mu_step2.rhs"),
     src[@hylo-least at `X:=(μX : S°F(X)R)`, whose
     `S°F((μX : S°F(X)R))R⊑(μX : S°F(X)R)` is @mu-laws's `φ((μX : φ(X)))=(μX : φ(X))`;
 ]),
     // lean:AOP.A6_2.mu_prefixed@fc0a1dca
  )],
)]<hylo-mu>

#pagebreak(weak: true)
