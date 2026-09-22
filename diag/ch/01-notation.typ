#import "../note-prelude.typ": *
#show: note-chapter.with(1)
// note-split: chapter 1 — this header is written by scripts/note-split and stripped by scripts/note-join
= Notation

Traditionaly Adjunction F -| G is defined as $F(x) <= y$ iff $x <= G(y)$, and you derive laws like this:

$ F(x) <= F(x) quad &==> quad x <= G(F(x)) quad &&==> quad F(x) <= F(G(F(x))) \
  G(y) <= G(y) quad &==> quad F(G(y)) <= y quad &&==> quad G(F(G(y))) <= G(y) $


By define $X: * |-> x$, $Y: *|->y$ and use diagram order, application can be replaced by composition:
     $X F<=Y$ iff $X<=Y G$
// A table, not a list: the second column is what hangs `rewrite`'s name out at the right.  The marker
// rides INSIDE the text cell — a column of its own would centre it, dropping it below the first line.
#disp[#table(
  columns: (1fr, auto),
  stroke: (x: none, y: 0.4pt + luma(215)),
  inset: (x: 6pt, y: 7pt),
  align: (left + horizon, right + horizon),
  [- write $F$ as #zw("/") , $G$ as #zw("\\")], [],
  [- render $a <= b$ as #h(0.8em) #zsq("a", "b")], [],
  [- *rewrite* $X<=X F$ as $1<=F$], [],
)]<notation-marks>

#znamed("adj", zsq("X/", "Y"), $=$, zsq("X", "Y\\"))

#zderiv(
  (zsq("X/", "X/"), zstep[adj], zsq("X", "X/\\"), zstep("rewrite", op: sym.eq),
   zsq("*", "/\\", name: "unit")),
  (
    ([put #zw("\\") on left],  zsq("\\", "\\/\\")),
    ([put #zw("/") on right],  zsq("/", "/\\/")),
  ),
)

#zderiv(
  (zsq("Y\\", "Y\\"), zstep[adj], zsq("Y\\/", "Y"), zstep("rewrite", op: sym.eq),
   zsq("\\/", "*", name: "counit")),
  (
    ([put #zw("/") on left],   zsq("/\\/", "/")),
    ([put #zw("\\") on right], zsq("\\/\\", "\\")),
  ),
)

now we have #zw("/\\/") $=$ #zw("/") and #zw("\\/\\") $=$ #zw("\\"), and you just discovered string
diagrams.


#pagebreak(weak: true)
== Adjunctions <sec-adj>

// The type column says which poset a row's `⊑` is read in — the first two rows are 1-cells of Rel, the
// rest monotone maps between hom-posets.  Sections, not an invented `•`: `•` reads as a composition dot.
// #src[Both halves of a row are written as sections — the operator stays and its missing argument is
// the gap: `·S` is `R ↦ R S`, `/S` is `T ↦ T/S`, `S\` is `Y ↦ S\Y`. Composition is juxtaposition, so
// the dot is written only in the rows where nothing else marks the gap.]

#disp[#table(
  columns: 9, align: left + horizon, inset: 3pt, stroke: 0.4pt + luma(190),
  table.header([*`F⊣G`*], [*`F`'s type*], [*monad `FG`*], [*`𝟙⊑FG`*], [*`GF⊑𝟙`*], [*`F` preserves `∪`*], [*`G` preserves `∩`*], [*`FGF=F`*], [*`GFG=G`*]),

  [`◁⊣▷`], [`A⟶` \ `A⊗A`], [`◁▷=𝟙`], [`𝟙⊑◁▷`], [`▷◁⊑𝟙`], [`(R ∪ S)◁=` \ `R◁ ∪ S◁`], [`(R∩S)▷=` \ `R▷∩S▷`], [`◁▷◁=◁`], [`▷◁▷=▷`],

  [`⊸⊣⟜`], [`A⟶𝕀`], [`⊸⟜=⊤`], [`𝟙⊑⊸⟜`], [`⟜⊸⊑𝟙`], [`(R ∪ S)⊸=` \ `R⊸ ∪ S⊸`], [`(R∩S)⟜=` \ `R⟜∩S⟜`], [`⊸⟜⊸=⊸`], [`⟜⊸⟜=⟜`],

 [`°⊣°`], [`(A⟶B)⟶` \ `(B⟶A)`], [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]],
  // lean:Freyd.S2_10.recip_recip@cb99fa11
 [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]], [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11 lean:Freyd.S2_10.recip_recip@cb99fa11
 [#leanf("Freyd.Alg.recip_union") #src[]],
    // lean:Freyd.S2_20.recip_union@d1eae8a9
 [#leanf("Freyd.Alg.Allegory.recip_inter") #src[]],
    // lean:Freyd.S2_10.recip_inter@e08c9f2d
 [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]], [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11 lean:Freyd.S2_10.recip_recip@cb99fa11

  [`⟜◁⊣▷⊸`], [`(X⊗A⟶Y)⟶` \ `(X⟶Y⊗A)`], [`𝟙`], [`(⟜◁⊗𝟙)` \ `(𝟙⊗▷⊸)=𝟙`], [`(𝟙⊗⟜◁)` \
    `(▷⊸⊗𝟙)=𝟙`], [`=`], [`=`], [`=`], [`=`],

  // An iso is an adjunction BOTH WAYS, so the bend gets a row in each direction; the pair differs
  // only by swapping columns 4/5, which is what makes the last four columns bare equalities.
  [`▷⊸⊣⟜◁`], [`(X⟶Y⊗A)⟶` \ `(X⊗A⟶Y)`], [`𝟙`], [`(𝟙⊗⟜◁)` \ `(▷⊸⊗𝟙)=𝟙`], [`(⟜◁⊗𝟙)` \
    `(𝟙⊗▷⊸)=𝟙`], [`=`], [`=`], [`=`], [`=`],

 [`Δ⊣∩`], [`(A⟶B)⟶` \ `(A⟶B)²`], [#leanf("Freyd.Alg.Allegory.inter_idem") #src[]],
  // lean:Freyd.S2_10.inter_idem@599acf28
 [#leanf("Freyd.Alg.Allegory.inter_idem") #src[]], [#leanf("Freyd.Alg.inter_lb_left") #src[]],
    // lean:Freyd.S2_10.inter_idem@599acf28 lean:Freyd.S2_10.inter_lb_left@4eca3d20
    [`Δ(R ∪ S)=` \ `ΔR ∪ ΔS`], [`(R∩T)∩(S∩U)=` \ `(R∩S)∩(T∩U)`],
 [#leanf("Freyd.Alg.Allegory.inter_idem") #src[]], [#leanf("Freyd.Alg.Allegory.inter_idem") #src[]],
    // lean:Freyd.S2_10.inter_idem@599acf28 lean:Freyd.S2_10.inter_idem@599acf28

  [`∪⊣Δ`], [`(A⟶B)²⟶` \ `(A⟶B)`], [`(R,S)↦` \ `(R ∪ S,R ∪ S)`],
 [#leanf("Freyd.Alg.le_union_left") #src[]], [#leanf("Freyd.Alg.DistributiveAllegory.union_idem") #src[]],
    // lean:Freyd.S2_20.le_union_left@0a8565e2 lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711
    [`(R ∪ T) ∪ (S ∪ U)=` \ `(R ∪ S) ∪ (T ∪ U)`], [`Δ(R∩S)=` \ `ΔR∩ΔS`],
 [#leanf("Freyd.Alg.DistributiveAllegory.union_idem") #src[]], [#leanf("Freyd.Alg.DistributiveAllegory.union_idem") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711 lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711

 [`𝟘⊣!`], [`{*}⟶` \ `(A⟶B)`], [], [], [#leanf("Freyd.Alg.zero_le") #src[]], [], [], [], [],
  // lean:Freyd.S2_20.zero_le@4399de93

  [`·S⊣/S`], [`(A⟶B)⟶` \ `(A⟶C)`], [`S/S`], [`R⊑(RS)/S`], [`(T/S)S⊑T`],
 [#leanf("Freyd.Alg.union_comp_distrib") #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [#leanf("Freyd.Alg.div_inter_eq") #src[]],
    // lean:Freyd.S2_30.div_inter_eq@d75d5861
    [`((RS)/S)S` \ `=RS`], [`((T/S)S)/S` \ `=T/S`],

  [`S·⊣S\`], [`(B⟶C)⟶` \ `(A⟶C)`], [`S\S`], [`R⊑S\(SR)`], [`S(S\T)⊑T`],
 [#leanf("Freyd.Alg.DistributiveAllegory.comp_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [#leanf("Freyd.Alg.leftDiv_inter") #src[]],
    // lean:Freyd.S2_30.leftDiv_inter@ba9dda1e
    [`S(S\(SR))` \ `=SR`], [`S\(S(S\T))` \ `=S\T`],

  [`R∩⊣R⇒`], [`(A⟶B)⟶` \ `(A⟶B)`], [`X↦R⇒(X∩R)`], [`X⊑R⇒(X∩R)`], [`R∩(R⇒Y)⊑Y`],
    [`R∩(X ∪ Y)=` \ `(R∩X) ∪ (R∩Y)`],
 [#leanf("Freyd.Alg.impl_inter") #src[]],
    // lean:AOP.A4_4.impl_inter@d2d55732
    [`R∩(R⇒(X∩R))` \ `=X∩R`], [`R⇒(R∩(R⇒Y))` \ `=R⇒Y`],

  [`𝓓⊣·⊤`], [`(A⟶B)⟶` \ `Cor A`], [`R↦(𝓓R)⊤`], [`R⊑(𝓓R)⊤`], [`𝓓(A⊤)⊑A`], [`𝓓(R ∪ S)=` \ `𝓓R ∪ 𝓓S`], [`(A∩B)⊤=` \ `A⊤∩B⊤`], [`𝓓((𝓓R)⊤)` \ `=𝓓R`], [`(𝓓(A⊤))⊤` \ `=A⊤`],

  [`𝓡⊣⊤·`], [`(A⟶B)⟶` \ `Cor B`], [`R↦⊤(𝓡R)`], [`R⊑⊤(𝓡R)`], [`𝓡(⊤A)⊑A`], [`𝓡(R ∪ S)=` \ `𝓡R ∪ 𝓡S`], [`⊤(A∩B)=` \ `⊤A∩⊤B`], [`𝓡(⊤(𝓡R))` \ `=𝓡R`], [`⊤(𝓡(⊤A))` \ `=⊤A`],

 [`·f⊣·f°`], [`(A⟶B)⟶` \ `(A⟶C)`], [`ff°`], [`𝟙⊑ff°` #src[]], [`f°f⊑𝟙`],
  // `map_entire_le` is private in `Freyd.S2_30` and cannot be opened: `Freyd.S2_147_MapCat` declares
  // its own, so the name would clash.  Hand-typed until one of the two copies survives the other.
  // lean:Freyd.S2_30.map_entire_le@833e9621
 [#leanf("Freyd.Alg.union_comp_distrib") #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [#leanf("Freyd.Alg.simple_dist_inter_recip") #src[]], [`ff°f=f`], [`f°ff°=f°`],
    // lean:AOP.A4_2.simple_dist_inter_recip@9d565a77

 [`f°·⊣f·`], [`(A⟶C)⟶` \ `(B⟶C)`], [`ff°`], [`𝟙⊑ff°` #src[]], [`f°f⊑𝟙`],
  // lean:Freyd.S2_30.map_entire_le@833e9621
 [#leanf("Freyd.Alg.DistributiveAllegory.comp_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
    [`f(X∩Y)=` \ `fX∩fY`], [`ff°f=f`], [`f°ff°=f°`],

  [`i⊣E`], [`Map↪Rel`], [`E`], [$frac(#[`𝟙`], ∋)$`:A⟶EA`], [`∋:EB⟶B`], [—], [—], [$frac(#[`∋`], ∋)$`=𝟙`], [$frac(#[`R`], ∋)$`∋=R`],

  // The row above at the HOM-SET level, and the table's only bijection that is not an ORDER-iso:
  // `%∋` is not monotone, and monotone would force every hom-poset discrete.
  [`·∋⊣` $frac(#box(width: 8pt), ∋)$], [`Map(A,EB)⟶` \ `(A⟶B)`], [`𝟙`], [$frac(#[`f∋`], ∋)$`=f`], [$frac(#[`R`], ∋)$`∋=R`], [—], [—], [$frac(#[`f∋`], ∋)$`∋` \ `=f∋`], [$frac(#[$frac(#[`R`], ∋)$`∋`], ∋)$ \ `=`$frac(#[`R`], ∋)$],

  [$frac(#box(width: 8pt), ∋)$ `⊣·∋`], [`(A⟶B)⟶` \ `Map(A,EB)`], [`𝟙`], [$frac(#[`R`], ∋)$`∋=R`], [$frac(#[`f∋`], ∋)$`=f`], [—], [—], [$frac(#[$frac(#[`R`], ∋)$`∋`], ∋)$ \ `=`$frac(#[`R`], ∋)$], [$frac(#[`f∋`], ∋)$`∋` \ `=f∋`],
)]<adj-all>

// Row parameters: `S`/`f` are `B ⟶ C` in the `·S`, `·f` rows and `A ⟶ B` in the `S·`, `f°·` ones;
// `Cor A` is the coreflexives on `A`, so the `A`, `B` of the `𝓓`, `𝓡` rows are coreflexives.

== Composing adjunctions <sec-compose>


// Why every cell below is an equation and not a `⊑`: the chain runs down one composite and back up the
// other, so both are right adjoints of the one left adjoint `X ↦ f°(X T)`, and that one is unique.
#disp[
#zline(
  zsqc(`X`, `f(R/T)`, name: "f a map"),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc(`f°X`, `R/T`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·T⊣/T`],
  zsqc(`(f°X)T`, `R`),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[associativity],
  zsqc(`f°(XT)`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc(`XT`, `fR`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·T⊣/T`],
  zsqc(`X`, `(fR)/T`),
)
#zline(
  zstep(under: true)[indirect equality],
  zsqc(`f(R/T)`, `(fR)/T`, eq: true),
)
#align(center, block(inset: (y: 3pt))[#leanf("Freyd.Alg.map_comp_div") #src[]])
// lean:AOP.A4_4.map_comp_div@3b1816a2
]<adj-cross-why>

// A cross table, not a list: what matters is WHICH PAIRS give a law, and a list of the ones that do
// hides how few they are.  `Δ` is a column and `∪`, `⊥` rows, on ONE side each — the other is all-empty.
#disp[#table(
  columns: 9, align: left + horizon, inset: 3pt, stroke: 0.4pt + luma(190),
  table.header([], [*`·T`*], [*`T·`*], [*`·g`*], [*`g°·`*], [*`T∩`*], [*`°`*], [*`⟜◁`*], [*`Δ`*]),

 [*`·S`*], [#leanf("Freyd.Alg.div_comp_assoc") #src[]],
  // lean:Freyd.S2_30.div_comp_assoc@30a074f3
 [#leanf("Freyd.Alg.leftDiv_div") #src[]],
    // lean:Freyd.S2_30.leftDiv_div@e6e6897c
 [`R/(Sg)=` \ `(Rg°)/S`], [#leanf("Freyd.Alg.map_comp_div") #src[]],
    // lean:AOP.A4_4.map_comp_div@3b1816a2
    [—], [`(Y/S)°=` \ `S°\(Y°)`], [`(RS)^=` \ `R^(S⊗𝟙)`],
 [#leanf("Freyd.Alg.div_inter_eq") #src[]],
    // lean:Freyd.S2_30.div_inter_eq@d75d5861

 [*`S·`*], [#leanf("Freyd.Alg.leftDiv_div") #src[]],
  // lean:Freyd.S2_30.leftDiv_div@e6e6897c
 [#leanf("Freyd.Alg.leftDiv_comp") #src[]],
    // lean:Freyd.S2_30.leftDiv_comp@f40e561a
    [`S\(Rg°)=` \ `(S\R)g°`], [`(g°S)\R=` \ `S\(gR)`], [—],
    [`(S\Y)°=` \ `Y°/S°`], [`((S⊗𝟙)R)^=` \ `SR^`],
 [#leanf("Freyd.Alg.leftDiv_inter") #src[]],
    // lean:Freyd.S2_30.leftDiv_inter@ba9dda1e

 [*`·f`*], [#leanf("Freyd.Alg.div_comp_recip_map") #src[]],
  // lean:AOP.A4_4.div_comp_recip_map@bc41ec1a
    [`T\(Rf°)=` \ `(T\R)f°`],
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.simple_dist_inter_recip") #src[]],
    // lean:AOP.A4_2.simple_dist_inter_recip@9d565a77

 [*`f°·`*], [#leanf("Freyd.Alg.map_comp_div") #src[]],
  // lean:AOP.A4_4.map_comp_div@3b1816a2
    [`(Tf°)\R=` \ `f(T\R)`], [—],
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
    [`f(T₁∩T₂)=` \ `fT₁∩fT₂`],

  [*`R∩`*], [—], [—], [—], [—],
 [#leanf("Freyd.Alg.impl_curry") #src[]],
    // lean:AOP.A4_4.impl_curry@96ec2371
    [`(R⇒Y)°=` \ `R°⇒(Y°)`], [—],
 [#leanf("Freyd.Alg.impl_inter") #src[]],
    // lean:AOP.A4_4.impl_inter@d2d55732

  [*`°`*], [`(Y/T)°=` \ `T°\(Y°)`], [`(T\Y)°=` \ `Y°/T°`],
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [`(T⇒Y)°=` \ `T°⇒(Y°)`],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11
    [`(R^)°=` \ `(R°⊗𝟙)(𝟙⊗▷⊸)` \ #src[both bends: the `°` section's display]],
    [`(T₁∩T₂)°=` \ `T₁°∩T₂°`],

  [*`⟜◁`*], [`(RT)^=` \ `R^(T⊗𝟙)`], [`((T⊗𝟙)R)^=` \ `TR^`], [—], [—], [—],
    [`(R^)°=` \ `(R°⊗𝟙)(𝟙⊗▷⊸)` \ #src[both bends: the `°` section's display]], [—], [—],

 [*`∪`*], [#leanf("Freyd.Alg.union_comp_distrib") #src[]],
  // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [#leanf("Freyd.Alg.DistributiveAllegory.comp_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [#leanf("Freyd.Alg.union_comp_distrib") #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [#leanf("Freyd.Alg.DistributiveAllegory.comp_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [#leanf("Freyd.Alg.DistributiveAllegory.inter_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.inter_union_distrib@83bb6087
 [#leanf("Freyd.Alg.recip_union") #src[]], [], [],
    // lean:Freyd.S2_20.recip_union@d1eae8a9

 [*`𝟘`*], [#leanf("Freyd.Alg.DistributiveAllegory.zero_comp") #src[]], [#leanf("Freyd.Alg.DistributiveAllegory.comp_zero") #src[]],
  // lean:Freyd.Alg.DistributiveAllegory.zero_comp@77e0792c lean:Freyd.Alg.DistributiveAllegory.comp_zero@ee8988af
 [#leanf("Freyd.Alg.DistributiveAllegory.zero_comp") #src[]], [#leanf("Freyd.Alg.DistributiveAllegory.comp_zero") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.zero_comp@77e0792c lean:Freyd.Alg.DistributiveAllegory.comp_zero@ee8988af
 [`T∩𝟘=𝟘` #src[]],
  // `inter_zero` lives in `Freyd.S2_50`, which `diag-export`'s environment does not import, so the
  // formula cannot be generated from it yet.
    // lean:Freyd.S2_50.inter_zero@d458c7d7
 [#leanf("Freyd.Alg.recip_zero") #src[]], [], [],
    // lean:Freyd.S2_20.recip_zero@49eaea12
)]<adj-cross>

// Proved in the repository: div_comp_assoc, leftDiv_div, leftDiv_comp, leftDiv_inter, leftDiv_div_recip,
// map_comp_div, div_comp_recip_map, div_inter_eq, recip_*, {union_comp,comp_union}_distrib, zero_*.

== Adjoint triples

Beyond `∪⊣Δ⊣∩`, which §@sec-adj already carries as two rows, the table holds one adjoint triple with
content: `∃_f⊣f*⊣∀_f` along a map `f`, once on each side of the composite.
#src[`f : A⟶B` throughout this subsection.]

#disp[#block(inset: (y: 6pt))[
  `·f⊣·f°⊣/f°` \
  `f°·⊣f·⊣f\`
  // The four cited statements are `↔`s between inclusions; `diag-export --formula` prints those with
  // Lean's own `≫`/`⊑`, not the note's juxtaposition, so the chain stays hand-typed for now.
  // lean:AOP.A4_2.map_shunt_right@789b4e7c lean:AOP.A4_2.map_shunt_left@9ab4e095 lean:Freyd.S2_30.le_div_iff@bb6a7930 lean:Freyd.S2_30.le_leftDiv_iff@6b879927
]]<triple-chains>

// `map_shunt_right`, AOP/A4_2.lean:223; `map_shunt_left`, AOP/A4_2.lean:241.
The first two links of each chain are the map shunting rules, and the third is §@sec-adj's division row read at a chosen divisor: `·S⊣/S` at `S:=f°`, and
`S·⊣S\` at `S:=f`.

The third link is not the first over again. For a map `f`, `/f` collapses to `·f°`; being a map is
exactly what that collapse spends
// `div_comp_recip_map`, AOP/A4_4.lean:378.
#src[#leanf("Freyd.Alg.div_comp_recip_map")] — `f°` is not a map, so
// lean:AOP.A4_4.div_comp_recip_map@bc41ec1a
`/f°` does not collapse in turn, and the three operators stay distinct. On `Rel(𝕀,A)=EA` they
are the image triple:

#disp[#table(
  columns: 3, align: left + horizon, inset: 4pt, stroke: 0.4pt + luma(190),
  table.header([*operator*], [*acts by*], [*name*]),
  [`·f`], [`S↦f[S]`], [direct image, `∃_f`],
  [`·f°`], [`T↦f⁻¹[T]`], [inverse image, `f*`],
  [`/f°`], [`S↦{b : f⁻¹(b)⊆S}`], [`∀_f`],
)]<triple-image>

§@sec-adj's `𝓓⊣·⊤` is this same chain along the projection `A⊗B⟶A`, read through
`Rel(A,B)=E(A⊗B)`: `𝓓R={(a,a) : ∃b. aRb}`, `A⊤` is the relation that ignores `b`
altogether, and the third link is `R↦𝟙∩R/⊤={(a,a) : ∀b. aRb}`.

#disp[#block(inset: (y: 6pt))[`𝓓⊣·⊤⊣𝟙∩·/⊤`
  // Both cited statements are `↔`s between inclusions, which `diag-export --formula` prints in Lean's
  // own spelling, so this chain stays hand-typed too.
  // lean:AOP.A5_2.dom_adj_comp_topMor@874d1a3e lean:AOP.A5_2.comp_topMor_adj_id_inter_div_topMor@794c6795
]]<triple-dom>

Three is where it stops, and one map breaks both ends. Take `A={a₁,a₂}` and `B={b}`:
`f[{a₁}]∩f[{a₂}]={b}` while `f[{a₁}∩{a₂}]=∅`, so `·f` does not preserve meets and has no
left adjoint, and the same two subsets give `∀_f({a₁} ∪ {a₂})={b}` against
`∀_f{a₁} ∪ ∀_f{a₂}=∅`, so `/f°` does not preserve joins and has no right adjoint. A monic `f`
restores the binary case and no more — `⊤f` still reaches only `im f`, and `∀_f𝟘=B∖im f` is
still not `𝟘`. The chain extends only when `f°` is a map as well, and then `/f°=·f°°=·f` and it
repeats forever. For an `S` with neither `S` nor `S°` a map there is no triple at all: `·S⊣/S` is
two links and stops.

#src[The rows that chain forever say nothing by it: `°` is an order-isomorphism of hom-posets, so it
is adjoint to itself on both sides and `°⊣°⊣°` has no end, and §@sec-adj's other row of that kind,
`⟜◁⊣▷⊸`, goes the same way.]

#pagebreak(weak: true)
