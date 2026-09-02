// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name (see circuit.typ's header); `dot` is renamed on the way in for that reason.
#import "circuit.typ": conv, conv-frame, conv-body, conv-w, SPLIT, LEAD, meet, wire, bend, gbox, boxrun, boxrun-w, dot as wiredot, tape, tape-fork, tape-join, TINT, delta as wcopy, nabla as wmerge, lw
// draw.typ owns the Hinze–Marsden geometry (Reduce) and every helper this note draws with:
// it is also the standalone PNG of those laws, and one geometry drawn in two files is one that drifts.
#import "draw.typ": snake, homeq, tfuneq, twobeadeq, TCOL, BCOL, CCOL, GIVEN1, GIVEN2, INDUCED, SLACK, ADMIRES, HATES, WORKS, ADMIRERS, HATERS, PEOPLE, LX, BD, LY, lab, ar, node, nodes, ings, edges, arc, head, e, syqnode, syqedge, domstr, pairstr, zw, zsq, zsqc, zstep, znamed, zderiv, zline, zpair, skel, yset, capbox, pair, blocked, CHPAD, CHFAN, fb-ALLC, fb-MAPC, fb-ZC, KNEE, FCOL, hm-bead, hm-join, hm-name, hm-port, hm-region, hm-wire
#import "cpanel.typ": cpanel
// EVERY PICTURE OF A THEOREM BELOW IS EXPORTED, NOT DRAWN: hand-drawing is how the first draft got
// `inter_assoc` wrong.  `./scripts/diag-regen` redraws every binding, reading the list off these imports.
#import "generated/Freyd.Diag.meet_top.typ": pic as p-meet-top
#import "generated/Freyd.Diag.meet_comm.typ": pic as p-meet-comm
#import "generated/Freyd.Diag.meet_assoc.typ": pic as p-meet-assoc
#import "generated/Freyd.Diag.meet_idem.typ": pic as p-meet-idem
#import "generated/Freyd.Diag.semidistrib_of_lax.typ": pic as p-semidistrib
#import "generated/Freyd.Diag.CartBicat.«∇_assoc».typ": pic as p-n-assoc
#import "generated/Freyd.Diag.CartBicat.«∇_comm».typ": pic as p-n-comm
#import "generated/Freyd.Diag.CartBicat.«∇_unit».typ": pic as p-n-unit
#import "generated/Freyd.Diag.CartBicat.«∇Δ≤𝟙».typ": pic as p-37
#import "generated/Freyd.Diag.CartBicat.«𝟙≤Δ∇».typ": pic as p-38
#import "generated/Freyd.Diag.CartBicat.«?!≤𝟙».typ": pic as p-39
#import "generated/Freyd.Diag.CartBicat.«𝟙≤!?».typ": pic as p-40
#import "generated/Freyd.Diag.CartBicat.frob.proof.typ": branches as frobb
#import "generated/Freyd.Diag.CartBicat.lax_Δ.typ": pic as p-lax-delta
#import "generated/Freyd.Diag.CartBicat.lax_!.typ": pic as p-lax-bang
#import "generated/Freyd.Diag.CartBicat.«°_slide».typ": pic as p-conv-slide
#import "generated/Freyd.Diag.comp_meet_of_singleValued.typ": lhs as p-236a, rhs as p-236b
// The allegory layer's division (last section).  `Freyd.Alg`, not `Freyd.Diag`: `/` is a theorem of
// `Freyd/S2_30.lean` and `AOP/A4_4`, and of nothing in `diag/`.
#import "generated/Freyd.Alg.le_div_iff.typ": pic as p-le-div
#import "generated/Freyd.Alg.le_leftDiv_iff.typ": pic as p-le-ldiv
#import "generated/Freyd.Alg.DivisionAllegory.div_comp_le.typ": pic as p-div-cancel
#import "generated/Freyd.Alg.leftDiv_comp_le.typ": pic as p-ldiv-cancel
#import "generated/Freyd.Alg.div_comp_assoc.typ": pic as p-div-assoc
#import "generated/Freyd.Alg.leftDiv_comp.typ": pic as p-ldiv-assoc
#import "generated/Freyd.Alg.map_comp_div.typ": pic as p-map-div
#import "generated/Freyd.Alg.div_comp_recip_map.typ": pic as p-div-map
// §2.314's list, in the book's order.
#import "generated/Freyd.Alg.div_comp.typ": pic as p-div-comp
#import "generated/Freyd.Alg.one_le_div_self.typ": pic as p-one-div
#import "generated/Freyd.Alg.div_self_comp_self.typ": pic as p-div-self-idem
#import "generated/Freyd.Alg.div_self_comp.typ": pic as p-div-self
#import "generated/Freyd.Alg.div_one.typ": pic as p-div-one
#import "generated/Freyd.Alg.div_union.typ": pic as p-div-union
#import "generated/Freyd.Alg.leftDiv_div.typ": pic as p-ldiv-div

#show: conf.with(title: "Relation Algebra")

// `supplement: none` so a `@sec-…` reference prints the BARE number: the prose writes its own
// `§`, and the default supplement would set "Section §1.1." in the middle of a sentence.
#set heading(supplement: none)

// `▿` at the four generator glyphs' size and for the same reason: at running-text size it reads as a
// subscript, not an operator.  Not in note-style.typ — the proofs note shares that file and has no copair.
#show regex("▿"): it => text(size: 1.45em, it)

// Row numbers so a law can be cited: `it.y` is the table's OWN index, so deleting a row renumbers
// the rest.  Rebuilt as a cell, not returned bare — bare content loses the row's height.
#let rownum = it => if it.y == 0 or it.body.func() == grid { it } else {
  let f = it.fields()
  let _ = f.remove("body")
  table.cell(..f, grid(columns: (0.55cm, 1fr), text(9pt, luma(140))[#it.y], it.body))
}

// WHAT THE TABLE SETTLES, in its top row: the reader needs the destination before the steps, and a
// footer would only confirm it.  Grey ground, heavier rule under it, no new font size.
#let Thm(body, cols: 2) = table.cell(colspan: cols, fill: luma(233), align: center + horizon,
  stroke: (rest: 0.4pt + luma(190), bottom: 1.1pt + luma(120)), strong(body))

// The Hinze–Marsden picture column the derivation tables share; the formula column takes the rest
// of the 22cm block, and 9cm is what the widest circuit in that column still fits in.
#let HMW = 9cm

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

  [`◁⊣▷`], [`A⟶` \ `A⊗A`], [`◁▷=𝟙`], [`𝟙⊑◁▷`], [`▷◁⊑𝟙`], [`(R∪S)◁=` \ `R◁∪S◁`], [`(R∩S)▷=` \ `R▷∩S▷`], [`◁▷◁=◁`], [`▷◁▷=▷`],

  [`⊸⊣⟜`], [`A⟶𝕀`], [`⊸⟜=⊤`], [`𝟙⊑⊸⟜`], [`⟜⊸⊑𝟙`], [`(R∪S)⊸=` \ `R⊸∪S⊸`], [`(R∩S)⟜=` \ `R⟜∩S⟜`], [`⊸⟜⊸=⊸`], [`⟜⊸⟜=⟜`],

 [`°⊣°`], [`(A⟶B)⟶` \ `(B⟶A)`], [`°°=𝟙` #src[]],
  // lean:Freyd.S2_10.recip_recip@cb99fa11
 [`R=R°°` #src[]], [`R=R°°` #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11 lean:Freyd.S2_10.recip_recip@cb99fa11
 [`(R∪S)°=` \ `R°∪S°` #src[]],
    // lean:Freyd.S2_20.recip_union@d1eae8a9
 [`(R∩S)°=` \ `R°∩S°` #src[]],
    // lean:Freyd.S2_10.recip_inter@e08c9f2d
 [`R°°°=R°` #src[]], [`R°°°=R°` #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11 lean:Freyd.S2_10.recip_recip@cb99fa11

  [`⟜◁⊣▷⊸`], [`(X⊗A⟶Y)⟶` \ `(X⟶Y⊗A)`], [`𝟙`], [`(⟜◁⊗𝟙)` \ `(𝟙⊗▷⊸)=𝟙`], [`(𝟙⊗⟜◁)` \
    `(▷⊸⊗𝟙)=𝟙`], [`=`], [`=`], [`=`], [`=`],

  // An iso is an adjunction BOTH WAYS, so the bend gets a row in each direction; the pair differs
  // only by swapping columns 4/5, which is what makes the last four columns bare equalities.
  [`▷⊸⊣⟜◁`], [`(X⟶Y⊗A)⟶` \ `(X⊗A⟶Y)`], [`𝟙`], [`(𝟙⊗⟜◁)` \ `(▷⊸⊗𝟙)=𝟙`], [`(⟜◁⊗𝟙)` \
    `(𝟙⊗▷⊸)=𝟙`], [`=`], [`=`], [`=`], [`=`],

 [`Δ⊣∩`], [`(A⟶B)⟶` \ `(A⟶B)²`], [`R↦R∩R=R` #src[]],
  // lean:Freyd.S2_10.inter_idem@599acf28
 [`R⊑R∩R` #src[]], [`R∩S⊑R` #src[]],
    // lean:Freyd.S2_10.inter_idem@599acf28 lean:Freyd.S2_10.inter_lb_left@4eca3d20
    [`Δ(R∪S)=` \ `ΔR∪ΔS`], [`(R∩T)∩(S∩U)=` \ `(R∩S)∩(T∩U)`],
 [`R∩R=R` #src[]], [`R∩R=R` #src[]],
    // lean:Freyd.S2_10.inter_idem@599acf28 lean:Freyd.S2_10.inter_idem@599acf28

  [`∪⊣Δ`], [`(A⟶B)²⟶` \ `(A⟶B)`], [`(R,S)↦` \ `(R∪S,R∪S)`],
 [`R⊑R∪S` #src[]], [`R∪R⊑R` #src[]],
    // lean:Freyd.S2_20.le_union_left@0a8565e2 lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711
    [`(R∪T)∪(S∪U)=` \ `(R∪S)∪(T∪U)`], [`Δ(R∩S)=` \ `ΔR∩ΔS`],
 [`R∪R=R` #src[]], [`R∪R=R` #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711 lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711

 [`⊥⊣!`], [`{*}⟶` \ `(A⟶B)`], [], [], [`⊥⊑R` #src[]], [], [], [], [],
  // lean:Freyd.S2_20.zero_le@4399de93

  [`·S⊣/S`], [`(A⟶B)⟶` \ `(A⟶C)`], [`S/S`], [`R⊑(RS)/S`], [`(T/S)S⊑T`],
 [`(R∪T)S=` \ `RS∪TS` #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [`(R∩T)/S=` \ `R/S∩T/S` #src[]],
    // lean:Freyd.S2_30.div_inter_eq@d75d5861
    [`((RS)/S)S` \ `=RS`], [`((T/S)S)/S` \ `=T/S`],

  [`S·⊣S\`], [`(B⟶C)⟶` \ `(A⟶C)`], [`S\S`], [`R⊑S\(SR)`], [`S(S\T)⊑T`],
 [`S(R∪T)=` \ `SR∪ST` #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [`S\(R∩T)=` \ `S\R∩S\T` #src[]],
    // lean:Freyd.S2_30.leftDiv_inter@ba9dda1e
    [`S(S\(SR))` \ `=SR`], [`S\(S(S\T))` \ `=S\T`],

  [`R∩⊣R⇒`], [`(A⟶B)⟶` \ `(A⟶B)`], [`X↦R⇒(X∩R)`], [`X⊑R⇒(X∩R)`], [`R∩(R⇒Y)⊑Y`],
    [`R∩(X∪Y)=` \ `(R∩X)∪(R∩Y)`],
 [`R⇒(X∩Y)=` \ `(R⇒X)∩(R⇒Y)` #src[]],
    // lean:AOP.A4_4.impl_inter@d2d55732
    [`R∩(R⇒(X∩R))` \ `=X∩R`], [`R⇒(R∩(R⇒Y))` \ `=R⇒Y`],

  [`𝓓⊣·⊤`], [`(A⟶B)⟶` \ `Cor A`], [`R↦(𝓓R)⊤`], [`R⊑(𝓓R)⊤`], [`𝓓(A⊤)⊑A`], [`𝓓(R∪S)=` \ `𝓓R∪𝓓S`], [`(A∩B)⊤=` \ `A⊤∩B⊤`], [`𝓓((𝓓R)⊤)` \ `=𝓓R`], [`(𝓓(A⊤))⊤` \ `=A⊤`],

  [`𝓡⊣⊤·`], [`(A⟶B)⟶` \ `Cor B`], [`R↦⊤(𝓡R)`], [`R⊑⊤(𝓡R)`], [`𝓡(⊤A)⊑A`], [`𝓡(R∪S)=` \ `𝓡R∪𝓡S`], [`⊤(A∩B)=` \ `⊤A∩⊤B`], [`𝓡(⊤(𝓡R))` \ `=𝓡R`], [`⊤(𝓡(⊤A))` \ `=⊤A`],

 [`·f⊣·f°`], [`(A⟶B)⟶` \ `(A⟶C)`], [`ff°`], [`𝟙⊑ff°` #src[]], [`f°f⊑𝟙`],
  // lean:Freyd.S2_30.map_entire_le@833e9621
 [`(R∪S)f=` \ `Rf∪Sf` #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [`(R∩S)f°=` \ `Rf°∩Sf°` #src[]], [`ff°f=f`], [`f°ff°=f°`],
    // lean:AOP.A4_2.simple_dist_inter_recip@9d565a77

 [`f°·⊣f·`], [`(A⟶C)⟶` \ `(B⟶C)`], [`ff°`], [`𝟙⊑ff°` #src[]], [`f°f⊑𝟙`],
  // lean:Freyd.S2_30.map_entire_le@833e9621
 [`f°(X∪Y)=` \ `f°X∪f°Y` #src[]],
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
#align(center, block(inset: (y: 3pt))[#src[]])
// lean:AOP.A4_4.map_comp_div@3b1816a2
]<adj-cross-why>

// A cross table, not a list: what matters is WHICH PAIRS give a law, and a list of the ones that do
// hides how few they are.  `Δ` is a column and `∪`, `⊥` rows, on ONE side each — the other is all-empty.
#disp[#table(
  columns: 9, align: left + horizon, inset: 3pt, stroke: 0.4pt + luma(190),
  table.header([], [*`·T`*], [*`T·`*], [*`·g`*], [*`g°·`*], [*`T∩`*], [*`°`*], [*`⟜◁`*], [*`Δ`*]),

 [*`·S`*], [`R/(ST)=` \ `(R/T)/S` #src[]],
  // lean:Freyd.S2_30.div_comp_assoc@30a074f3
 [`T\(R/S)=` \ `(T\R)/S` #src[]],
    // lean:Freyd.S2_30.leftDiv_div@e6e6897c
 [`R/(Sg)=` \ `(Rg°)/S`], [`g(R/S)=` \ `(gR)/S` #src[]],
    // lean:AOP.A4_4.map_comp_div@3b1816a2
    [—], [`(Y/S)°=` \ `S°\(Y°)`], [`(RS)^=` \ `R^(S⊗𝟙)`],
 [`(T₁∩T₂)/S=` \ `T₁/S∩T₂/S` #src[]],
    // lean:Freyd.S2_30.div_inter_eq@d75d5861

 [*`S·`*], [`S\(R/T)=` \ `(S\R)/T` #src[]],
  // lean:Freyd.S2_30.leftDiv_div@e6e6897c
 [`(TS)\R=` \ `S\(T\R)` #src[]],
    // lean:Freyd.S2_30.leftDiv_comp@f40e561a
    [`S\(Rg°)=` \ `(S\R)g°`], [`(g°S)\R=` \ `S\(gR)`], [—],
    [`(S\Y)°=` \ `Y°/S°`], [`((S⊗𝟙)R)^=` \ `SR^`],
 [`S\(T₁∩T₂)=` \ `S\T₁∩S\T₂` #src[]],
    // lean:Freyd.S2_30.leftDiv_inter@ba9dda1e

 [*`·f`*], [`R/(fT)=` \ `(R/T)f°` #src[]],
  // lean:AOP.A4_4.div_comp_recip_map@bc41ec1a
    [`T\(Rf°)=` \ `(T\R)f°`],
 [`(fg)°=g°f°` #src[]], [], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [`(fY)°=Y°f°` #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [`(T₁∩T₂)f°=` \ `T₁f°∩T₂f°` #src[]],
    // lean:AOP.A4_2.simple_dist_inter_recip@9d565a77

 [*`f°·`*], [`f(R/T)=` \ `(fR)/T` #src[]],
  // lean:AOP.A4_4.map_comp_div@3b1816a2
    [`(Tf°)\R=` \ `f(T\R)`], [—],
 [`(fg)°=g°f°` #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [`(fY)°=Y°f°` #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
    [`f(T₁∩T₂)=` \ `fT₁∩fT₂`],

  [*`R∩`*], [—], [—], [—], [—],
 [`(R∩T)⇒Y=` \ `R⇒(T⇒Y)` #src[]],
    // lean:AOP.A4_4.impl_curry@96ec2371
    [`(R⇒Y)°=` \ `R°⇒(Y°)`], [—],
 [`R⇒(T₁∩T₂)=` \ `(R⇒T₁)∩(R⇒T₂)` #src[]],
    // lean:AOP.A4_4.impl_inter@d2d55732

  [*`°`*], [`(Y/T)°=` \ `T°\(Y°)`], [`(T\Y)°=` \ `Y°/T°`],
 [`(gY)°=Y°g°` #src[]],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [`(gY)°=Y°g°` #src[]], [`(T⇒Y)°=` \ `T°⇒(Y°)`],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [`Y°°=Y` #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11
    [`(R^)°=` \ `(R°⊗𝟙)(𝟙⊗▷⊸)` \ #src[both bends: the `°` section's display]],
    [`(T₁∩T₂)°=` \ `T₁°∩T₂°`],

  [*`⟜◁`*], [`(RT)^=` \ `R^(T⊗𝟙)`], [`((T⊗𝟙)R)^=` \ `TR^`], [—], [—], [—],
    [`(R^)°=` \ `(R°⊗𝟙)(𝟙⊗▷⊸)` \ #src[both bends: the `°` section's display]], [—], [—],

 [*`∪`*], [`(X₁∪X₂)T=` \ `X₁T∪X₂T` #src[]],
  // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [`T(X₁∪X₂)=` \ `TX₁∪TX₂` #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [`(X₁∪X₂)g=` \ `X₁g∪X₂g` #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [`g°(X₁∪X₂)=` \ `g°X₁∪g°X₂` #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [`T∩(X₁∪X₂)=` \ `(T∩X₁)∪(T∩X₂)` #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.inter_union_distrib@83bb6087
 [`(X₁∪X₂)°=` \ `X₁°∪X₂°` #src[]], [], [],
    // lean:Freyd.S2_20.recip_union@d1eae8a9

 [*`⊥`*], [`⊥T=⊥` #src[]], [`T⊥=⊥` #src[]],
  // lean:Freyd.Alg.DistributiveAllegory.zero_comp@77e0792c lean:Freyd.Alg.DistributiveAllegory.comp_zero@ee8988af
 [`⊥g=⊥` #src[]], [`g°⊥=⊥` #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.zero_comp@77e0792c lean:Freyd.Alg.DistributiveAllegory.comp_zero@ee8988af
 [`T∩⊥=⊥` #src[]],
    // lean:Freyd.S2_50.inter_zero@d458c7d7
 [`⊥°=⊥` #src[]], [], [],
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
]]<triple-chains>

// `map_shunt_right`, AOP/A4_2.lean:223; `map_shunt_left`, AOP/A4_2.lean:241.
The first two links of each chain are the map shunting rules, and the third is §@sec-adj's division row read at a chosen divisor: `·S⊣/S` at `S:=f°`, and
`S·⊣S\` at `S:=f`.

The third link is not the first over again. For a map `f`, `/f` collapses to `·f°`; being a map is
exactly what that collapse spends
// `div_comp_recip_map`, AOP/A4_4.lean:378.
#src[`R/(fS)=(R/S)f°`.] — `f°` is not a map, so
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

#disp[#block(inset: (y: 6pt))[`𝓓⊣·⊤⊣𝟙∩·/⊤`]]<triple-dom>

Three is where it stops, and one map breaks both ends. Take `A={a₁,a₂}` and `B={b}`:
`f[{a₁}]∩f[{a₂}]={b}` while `f[{a₁}∩{a₂}]=∅`, so `·f` does not preserve meets and has no
left adjoint, and the same two subsets give `∀_f({a₁}∪{a₂})={b}` against
`∀_f{a₁}∪∀_f{a₂}=∅`, so `/f°` does not preserve joins and has no right adjoint. A monic `f`
restores the binary case and no more — `⊤f` still reaches only `im f`, and `∀_f⊥=B∖im f` is
still not `⊥`. The chain extends only when `f°` is a map as well, and then `/f°=·f°°=·f` and it
repeats forever. For an `S` with neither `S` nor `S°` a map there is no triple at all: `·S⊣/S` is
two links and stops.

#src[The rows that chain forever say nothing by it: `°` is an order-isomorphism of hom-posets, so it
is adjoint to itself on both sides and `°⊣°⊣°` has no end, and §@sec-adj's other row of that kind,
`⟜◁⊣▷⊸`, goes the same way.]

#pagebreak(weak: true)
= Relations

#disp[#definition[
Rel is a poset-enriched category with ($times.o$, °) where $times.o$ is commutative cartisian product, and converse `°⊣°`, and

  #align(center, block(inset: (y: 6pt))[
    #src[C:] `(▷ : A⊗A⟶A,⟜ : 𝕀⟶A)` a commutative monoid with `C°⊣C`.
    We write `C°` as `(◁ : A⟶A⊗A,⊸ : A⟶𝕀)`
  ])
]]<rel-defn>

#disp[#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-n-assoc, s: 60%) #v(-7pt) \ #src[`▷` associative]],
  [#P(p-n-comm, s: 60%) #v(-7pt) \ #src[`▷` commutative]],
  [#P(p-n-unit, s: 60%) #v(-7pt) \ #src[`⟜` is its unit]],
  // `slice(0, 2)`, not `slice(1)`: the exporter draws the relation symbol at the LEFT edge of every
  // step after the first, so dropping the first step would leave a dangling `=` in front.
  [#row(frobb.at(0).steps.slice(0, 2), s: 42%) #v(-7pt) \ #src[Frobenius, one half — the other is
   its `°`]],
  [#P(p-lax-delta, s: 60%) #v(-7pt) \ #src[`R◁≤◁(R⊗R)`]],
  [#P(p-lax-bang, s: 60%) #v(-7pt) \ #src[`R⊸≤⊸`]],
)]<rel-monoid>

== $forall$ object A, `(A,◁,⊸)⊣(A,▷,⟜)`

#disp[#grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-37, s: 52%) #v(-7pt) \ #src[`▷◁≤𝟙`]],
  [#P(p-38, s: 52%) #v(-7pt) \ #src[`𝟙≤◁▷`]],
  [#P(p-39, s: 52%) #v(-7pt) \ #src[`⟜⊸≤𝟙`]],
  [#P(p-40, s: 52%) #v(-7pt) \ #src[`𝟙≤⊸⟜`]],
)]<rel-adj>

The last of these is the only one that makes a picture *bigger*, and it is worth a name: *a wire is
below the cut wire*. In `Rel` it reads `{(a,a)}⊆A×A` — cut a wire and its two ends stop having
to agree, so cutting can only add pairs. It is the one weakening this calculus gives away for free.


#pagebreak(weak: true)
= ° : 𝒞ᵒᵖ ⟶ 𝒞 is a 2 functor 

#disp[#definition[
`°` is primitive, part of the data the first section lists. It turns both of `R`'s wires round, and
the Frobenius structure DRAWS that — the picture and the formula below are `R°`, not its definition:

#fig({ conv((0, -0.80), $R$) })

#align(center, block(inset: (y: 4pt))[#text(12.5pt)[`R°=(⟜◁⊗𝟙)(𝟙⊗R⊗𝟙)(𝟙⊗▷⊸)`]])

where `⟜◁ : 𝕀⟶a⊗a` opens a pair of wires out of nothing and `▷⊸ : b⊗b⟶𝕀` closes one, so
the input of `R°` is where the output of `R` was.  Taking that formula as the definition would now
be circular: `◁` and `⊸` are `▷°` and `⟜°`.  The laws of `°` are that it is a contravariant
2-functor `° : 𝒞ᵒᵖ⟶𝒞`:

#align(center, block(inset: (y: 5pt))[
 (i) `𝟙°=𝟙` #src[] #h(1cm) (ii) `(RS)°=S°R°`
  // lean:Freyd.S2_10.recip_id@319d8965
 #src[] #h(1cm) (iii) `(R⊗S)°=R°⊗S°`
  // lean:Freyd.S2_10.recip_comp@516c2d8a
 #h(1cm) (iv) `R≤S` implies `R°≤S°` #src[]
  // lean:Freyd.S2_10.recip_mono@d584321d
])
]]<conv-defn>

== The slide

The one rule (ii) and (iii) use, and each of them uses it twice. A converse facing a merge on the
lower strand is the box itself, upright, on the upper one:

#disp[#P(p-conv-slide, s: 62%)]<conv-slide>

`R°` is DEFINED as the bending of `(R⊗𝟙)▷⊸`, so the slide claims only that unbending it gives
that back — and unbending undoes bending for every arrow. That is the snake above with a passenger:
the `⟜◁` bends the `a` strand down and the `▷⊸` brings it back up, while the `b` strand rides
through untouched. Nothing else is spent below.


#pagebreak(weak: true)
= `∩` is a commutative idempotent monoid on every hom-set

#disp[#definition[
The *meet* of `R,S : a⟶b`, the paper's *convolution*, is `R∩S:=◁(R⊗S)▷` — copy the
input, run `R` and `S` on the two copies, merge the results — so what comes out is what both of them
do.

#fig({ meet((0, 0), $R$, $S$) })
#align(center, src[transcribed: a definition has no statement to export])

On every hom-set it is associative, commutative and idempotent
#src[,
// lean:Freyd.S2_10.inter_assoc@958bcd8a lean:Freyd.S2_10.inter_comm@4e93697e
], with unit the maximal arrow
// lean:Freyd.S2_10.inter_idem@599acf28
`⊤=⊸⟜` #src[(the paper's Lemma 4.11)].
]]<meet-defn>

#disp[#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-meet-top, s: 60%) #v(-7pt) \ #src[*unit:* one half of `⊤` per end — the merge's unit law
   absorbs the `⟜`, the copy's counit law the `⊸`]],
  [#P(p-meet-comm, s: 60%) #v(-7pt) \ #src[*commutative:* `σ` crosses `R⊗S` by naturality and is
   absorbed by cocommutativity and commutativity]],
  [#P(p-meet-assoc, s: 44%) #v(-7pt) \ #src[*associative:* coassociativity and associativity; `⊗`
   re-brackets for nothing, being strict here]],
  [#P(p-meet-idem, s: 60%) #v(-7pt) \ #src[*idempotent:* the one that is not bookkeeping — the lax
   copy law is the whole of it, worked in allegory2]],
)]<meet-laws>

So `≤` is the order this monoid induces. `R∩S≤R` comes from the unit, and idempotency turns
anything under both `S` and `T` into something under `S∩T`, since `R=R∩R≤S∩T`.

And one law relating `∩` to composition, which is *not* an equation:

#disp[#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*semi-distributivity, and what supplies it*], [*picture*]),

  [`R (S∩T)⊑RS∩RT` — the lax copy law. #src[Equality exactly when `R` is single valued: the Maps section's
 `F(R∩S)=FR∩FS`. ]], P(p-semidistrib),
   // lean:AOP.A4_1.comp_inter_le@c62bf05a
)]<meet-semidistrib>

#pagebreak(weak: true)
= Domain and range

#disp[#definition[
The *domain* `Dom(R)≜𝟙∩RR°` #src[] and the *range* `Ran R≜Dom(R°)`.
// lean:Freyd.S2_10.dom@9e0aed7a
]]<dom-defn>

// THE MEET FIRST, then the stub: the stub alone does not look like `𝟙 ∩ R R°` — one strand carries no
// box and the return leg is gone — so the definition is drawn beside it and the chain shows the collapse.
#disp[#chain((cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (4.4, y))
  wire((1.55, -y), (1.7, -y)); gbox((1.7, -y), [R])
  wire((2.62, -y), (2.85, -y)); gbox((2.85, -y), [R], flip: true)
  wire((3.77, -y), (4.4, -y))
  bend((4.4, y), (5.05, 0), k: 0.4); bend((4.4, -y), (5.05, 0), k: 0.4); wiredot((5.05, 0))
  wire((5.05, 0), (5.6, 0))
  lab(-0.35, 0, black)[$A$]; lab(5.95, 0, black)[$A$]
}), domstr(rel: [$=$])),
  // Broken by hand: `chain` sizes its column to the hint, so an unbroken line of this length pushes
  // the two pictures a third of the page apart.
  ("", [`▷` lands the return leg back on the value `◁` handed out, \
   so `R°▷` cuts to `⊸` — Frobenius]), s: 100%)]<dom-collapse>

Running `R` and throwing the result away leaves only the fact that `R` could fire, and `Ran R` is the
same picture with the box mirrored. In `Rel` both steps are `{(a,a) : ∃b. a R b}`.

#disp[#table(
  columns: 1, inset: 9pt, stroke: 0.4pt + luma(190),

  [`Dom(R)≜𝟙∩RR°`],
 [`Dom(R)⊑A⟺R⊑AR`, for `A` coreflexive #src[]],
  // lean:AOP.A4_2.dom_UP@9eaee77f
 [`Dom(RS)⊑Dom(R)` #src[]],
  // lean:Freyd.S2_10.dom_comp_le@a99434dd
 [`Dom(R∩S)=𝟙∩SR°` #src[]],
  // lean:Freyd.S2_10.dom_inter@e702a791
  [`R` entire `⟺Dom(R)=𝟙⟺𝟙⊑RR°`],
  [`R` simple `⟺R°R⊑𝟙`],
  [`R` a map `⟺R` entire and simple],
  [`R,S` entire `⟹RS` entire — likewise simple, likewise maps
 #src[,
   // lean:Freyd.S2_10.entire_comp@2dfbf431 lean:Freyd.S2_10.simple_comp@c3c56ec3
 ]],
   // lean:Freyd.S2_10.map_comp@841b047c
 [`RS` entire `⟹R` entire #src[]],
  // lean:Freyd.S2_10.entire_of_comp_entire@ad998fc1
)]<dom-laws>

== Sliding the discard

`Dom(RS)⊑Dom(R)`, and a single glyph for `Dom` would have nothing to slide: with the box and the
discard drawn apart, the law is one dot walking back along the lower strand.

#disp[#chain((cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (4.6, y))
  wire((1.55, -y), (1.7, -y)); gbox((1.7, -y), [R])
  wire((2.62, -y), (2.85, -y)); gbox((2.85, -y), [S])
  wire((3.77, -y), (4.15, -y)); wiredot((4.15, -y))
  lab(-0.35, 0, black)[$A$]; lab(4.95, y, black)[$A$]
}), domstr(rel: [`⊑`])),
  ("", [`S⊸⊑⊸`, the lax axiom for `⊸` in the first section \
 — the discard slides back past `S` #src[]]), s: 100%)]<dom-slide>
   // lean:Freyd.S2_10.dom_comp_le@a99434dd

Equality is `S` entire, which is the same picture read as `Dom(R)=𝟙⟺R` entire.

#pagebreak(weak: true)
= Maps

// A 2×2, not a list of four: the ROW says which composite (`R° R`, `R R°`), the COLUMN which way the
// containment runs, so each property's opposite is the cell diagonally across.
#disp[#table(
  columns: (1fr, 1fr),
  align: center + horizon,
  inset: 10pt, stroke: 0.4pt + luma(190),

  [*surjective* \ #src[`𝟙⊑R°R`, that is, `R°` entire.]],
  [*single valued* \ #src[`R°R⊑𝟙`]],

  [*entire* \ #src[`𝟙⊑RR°`. With *single valued*, a *map*.]],
  [*injective* \ #src[`RR°⊑𝟙`]],
)]<map-square>

#disp[#table(
  columns: (1fr, 2.2fr),
  align: (center + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*picture*]),

 [`F(R∩S)=FR∩FS` \ #v(2pt) #src[`F` single valued]],
  // lean:Freyd.S2_10.simple_dist_inter@46ef7904
  grid(columns: 3, align: horizon, column-gutter: 10pt,
    [#P(p-236a, s: 74%) #v(-9pt) #align(center, src[one person who admires both])],
    text(17pt)[=],
    [#P(p-236b, s: 74%) #v(-9pt) #align(center, src[`a` at A, `b` at B])],
  ),
)]<map-meet>

= Reduce in 𝒮et

// B&dM §3.1 "Banana-split", pp. 55–57.  The book writes `h · f` applicatively; every composite in the
// table is mirrored to `f h`, this note's diagram order.
#disp[#table(
  columns: (8.7cm, 4.5cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

  [`listr A::=nil|cons (A,listr A)`],
  [`𝒮et⟶𝒮et`],
  [The cons-lists over `A`, the datatype every row below folds (B&dM p. 55).],

  [`sum≜⦇[zero,plus]⦈`],
  [`listr Nat⟶Nat`],
  [`plus(a,b)=a+b`.],

  [`length≜⦇[zero,π₂ succ]⦈`],
  [`listr A⟶Nat`],
  [`π₂` drops the head and keeps the count of the tail, `succ` adds one for the head.],

  [`average≜⟨sum,length⟩ div`],
  [`listr Nat⟶Real`],
  [`div(m,n)=m/n`, with `div(0,0)=0` so `average` is total. Traverses the list twice.],

  [banana-split law \
   `⟨⦇h⦈,⦇k⦈⟩=⦇⟨F(π₁)h,F(π₂)k⟩⦈`],
  [`T⟶A×B`],
  [Any fork of folds is a single fold, hence one traversal — `F` the base functor.],

  [what it reduces to \
   `α⟨⦇h⦈,⦇k⦈⟩=F(⟨⦇h⦈,⦇k⦈⟩)⟨F(π₁)h,F(π₂)k⟩`],
  [`FT⟶A×B`],
  [All that @cata-defining leaves to check: the fork satisfies the defining equation.],

  [the instance \
   `⟨sum,length⟩=⦇[zeros,pluss]⦈`],
  [`listr Nat⟶Nat×Nat`],
  [`pluss(a,(b,n))=(a+b,n+1)`, so `average` runs in one pass.],

  [`preds n=[n,n−1,…,1]`],
  [`Nat⟶[Nat]`],
  [B&dM Ex 3.6 (p. 57): apply Ex 3.4 to write `preds` as `⦇k⦈π₁`.],
)]<cata-examples>

// The square is the product's universal property at `T`, the string diagram the row above it: one
// fold bead, the algebra falling past it, exactly as in @cata-defining.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    // The fan is ±4.6 wide only so that `⟨⦇h⦈,⦇k⦈⟩` fits between the induced arrow and `⦇h⦈`'s leg.
    let (T, A, AB, B) = ((0, 2.2), (-4.6, -1.9), (0, -1.9), (4.6, -1.9))
    ar(T, A, GIVEN1, s0: 0.5, s1: 0.5); ar(T, B, GIVEN2, s0: 0.5, s1: 0.5)
    ar(T, AB, INDUCED, dash: "dashed", s0: 0.45, s1: 0.55)
    ar(AB, A, GIVEN1, s0: 0.95, s1: 0.5); ar(AB, B, GIVEN2, s0: 0.95, s1: 0.5)
    lab(-2.6, 0.45, GIVEN1)[`⦇h⦈`]; lab(2.6, 0.45, GIVEN2)[`⦇k⦈`]
    lab(-1.45, -0.85, INDUCED)[`⟨⦇h⦈,⦇k⦈⟩`]
    lab(-2.4, -2.45, GIVEN1)[`π₁`]; lab(2.4, -2.45, GIVEN2)[`π₂`]
    node(T.at(0), T.at(1), black, `T`); node(A.at(0), A.at(1), GIVEN1, `A`)
    node(AB.at(0), AB.at(1), INDUCED, `A×B`); node(B.at(0), B.at(1), GIVEN2, `B`)
  }),
  homeq(`F`, `T`, [`α`], [`⟨⦇h⦈,⦇k⦈⟩`], [`⟨F(π₁)h,F(π₂)k⟩`], `A×B`,
    ctop: GIVEN2, cmid: INDUCED, cbot: GIVEN1, typed: true, gap: 3.2, regions: auto),
  [`⟨⦇h⦈,⦇k⦈⟩=⦇⟨F(π₁)h,F(π₂)k⟩⦈` #h(6pt) #src[banana split]],
)]<banana-split>

// Its own page: the heading was left orphaned at the foot of the page before it.
#pagebreak(weak: true)
== Fokkinga's mutual recursion theorem

// Algebras lettered `h`, `k` as in @cata-examples; the display below reuses the letters for the
// general case, which is what the last bullet contrasts the product with.
- `F-Alg(𝒜)` — the algebras and their homomorphisms — has binary products whenever `𝒜` does, and the
  forgetful `U : F-Alg(𝒜)⟶𝒜` *creates* them: the product of `h : FA⟶A` and `k : FB⟶B` is
  carried by `A×B`, with structure `⟨F(π₁)h,F(π₂)k⟩ : F(A×B)⟶A×B`.
- `π₁` and `π₂` are homomorphisms out of it, and `⟨p,q⟩ : X⟶A×B` is a homomorphism *iff* `p`
  and `q` both are — substitute the structure and compare the two forks component by component.
- The banana-split law of @cata-examples IS that product's universal property read at the initial
  algebra: `⦇h⦈` and `⦇k⦈` are the unique homomorphisms to `(A,h)` and `(B,k)`, so their fork is the
  unique homomorphism into the product, which is `⦇⟨F(π₁)h,F(π₂)k⟩⦈`.
- Fokkinga's theorem is *strictly more general* and is not that product: in @fokkinga the two arrows
  leave `F(A×B)`, not `FA` and `FB`, so each sees BOTH components. The product is the case where
  they factor as `F(π₁)h` and `F(π₂)k`; B&dM's Ex 3.4 is the other special case (p. 58). What
  it says: *any algebra on a product carrier is folded by a fork*.

// B&dM Ex 3.8 (p. 58), ONE SQUARE PER CONJUNCT: `h` and `k` leave `F(A × B)` for different corners,
// so a single square cannot carry both.  Dashed blue as in @cata-defining — the arrows uniqueness gives.
#disp[#capbox(
  grid(columns: 2, align: horizon, column-gutter: 34pt,
    cetz.canvas(length: 0.8cm, {
      let (FT, T, FAB, A) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
      ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FAB, A, GIVEN1, s0: 1.35, s1: 0.55)
      ar(FT, FAB, INDUCED, s0: 0.5, s1: 0.5)
      ar(T, A, INDUCED, dash: "dashed", s0: 0.5, s1: 0.5)
      lab(0, 1.9, GIVEN2)[`α`]; lab(0.4, -1.9, GIVEN1)[`h`]
      lab(-4.15, 0, INDUCED)[`F(⟨f,g⟩)`]; lab(3.0, 0, INDUCED)[`f`]
      node(FT.at(0), FT.at(1), black, `FT`); node(FAB.at(0), FAB.at(1), GIVEN1, `F(A×B)`)
      node(T.at(0), T.at(1), black, `T`); node(A.at(0), A.at(1), GIVEN1, `A`)
    }),
    cetz.canvas(length: 0.8cm, {
      let (FT, T, FAB, B) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
      ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FAB, B, GIVEN1, s0: 1.35, s1: 0.55)
      ar(FT, FAB, INDUCED, s0: 0.5, s1: 0.5)
      ar(T, B, INDUCED, dash: "dashed", s0: 0.5, s1: 0.5)
      lab(0, 1.9, GIVEN2)[`α`]; lab(0.4, -1.9, GIVEN1)[`k`]
      lab(-4.15, 0, INDUCED)[`F(⟨f,g⟩)`]; lab(3.0, 0, INDUCED)[`g`]
      node(FT.at(0), FT.at(1), black, `FT`); node(FAB.at(0), FAB.at(1), GIVEN1, `F(A×B)`)
      node(T.at(0), T.at(1), black, `T`); node(B.at(0), B.at(1), GIVEN1, `B`)
    }),
  ),
  [`αf=F(⟨f,g⟩)h∧αg=F(⟨f,g⟩)k≡⟨f,g⟩=⦇⟨h,k⟩⦈`],
)]<fokkinga>

== Ruby triangles

// B&dM §3.2, pp. 58–59.  The book writes `cons · (id × listr f)` applicatively; every composite in the
// table is mirrored by `h·f ↦ f h` into this note's diagram order.
#disp[#table(
  columns: (5.8cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*stage*], [*definition*]),

  [informally (p. 58)],
  [`tri(f) [a₀,a₁,…,aᵢ,…,aₙ]=[a₀,f a₁,…,fⁱ aᵢ,…,fⁿ aₙ]`],

  [for cons-lists (p. 59)],
  [`tri(f)=⦇[nil,(𝟙×listr(f)) cons]⦈`],

  [with the base functor named],
  [`F(A,B)=1+A×B`, `α=[nil,cons]`, so `tri(f)=⦇F(𝟙,listr(f))α⦈`],

  [abstractly (p. 59)],
  [`F` a bifunctor with initial type `(α,T)`: `tri(f)=⦇F(𝟙,T(f))α⦈`],
)]<tri-evolution>

For the definition to make sense `f : A⟶A` is required, and then `tri(f) : TA⟶TA`.

// The book's top arrow points LEFT because it composes applicatively, so mirroring it into diagram
// order swaps the legs: `⦇g⦈` post-composes `tri(f)`, hence leaves the RIGHT `T A` (B&dM p. 59).
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (TL, TR, A) = ((-2.2, 1.25), (2.2, 1.25), (0, -1.25))
    ar(TL, TR, GIVEN2, s0: 0.6, s1: 0.6)
    ar(TL, A, INDUCED, dash: "dashed", s0: 0.6, s1: 0.6)
    ar(TR, A, INDUCED, dash: "dashed", s0: 0.6, s1: 0.6)
    lab(0, 1.8, GIVEN2)[`tri(f)`]
    lab(-3.1, -0.35, INDUCED)[`⦇F(𝟙,f)g⦈`]; lab(2.0, -0.35, INDUCED)[`⦇g⦈`]
    node(TL.at(0), TL.at(1), black, `TA`); node(TR.at(0), TR.at(1), black, `TA`)
    node(A.at(0), A.at(1), GIVEN1, `A`)
  }),
  twobeadeq(`TA`, [`tri(f)`], [`⦇g⦈`], [`⦇F(𝟙,f)g⦈`], `A`, c1: GIVEN2, c2: INDUCED, c3: INDUCED,
    typed: true, vcol: TCOL, bcol: BCOL, regions: auto),
  [`tri(f) ⦇g⦈=⦇F(𝟙,f)g⦈` #h(1.6cm) `⟸` #h(1.6cm) `gf=F(f,f)g`],
)]<horner>

@horner is Horner's rule, generalised from cons-lists to any initial type; B&dM call it that because
for cons-lists it is the schoolbook method for evaluating a polynomial (p. 58). Fusion reduces it to
`F(𝟙,T(f))α⦇g⦈=F(𝟙,⦇g⦈)F(𝟙,f)g` (p. 59).

// Its own page: the section is one table long and the heading was left orphaned at the foot of the
// page before it once the F-Alg bullets above pushed the table over the break.
#pagebreak(weak: true)
== Depth of a tree

// B&dM p. 60, mirrored to diagram order: the book writes `depths = tri succ · tree zero` and
// `depth = max · depths`.
#disp[#table(
  columns: (3.0cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [the datatype],
  [`tree A::=tip A|bin (tree A,tree A)`, base functor `F(A,B)=A+B×B`, \
   initial type `([tip,bin],tree)`],

  [the fold],
  [`⦇[g,h]⦈` is the unique `f` with `f (tip a)=g a` and `f (bin (x,y))=h (f x,f y)`],

  [`tree(f)`],
  [`tree(f)=⦇F(f,𝟙) [tip,bin]⦈`; pointwise `tree(f) (tip a)=tip (f a)` and \
   `tree(f) (bin (x,y))=bin (tree(f) x,tree(f) y)`],

  [`max`],
  [`max=⦇[𝟙,bmax]⦈`, where `bmax (a,b)` is the larger of `a` and `b`],

  [`depths`],
  [`depths=tree(zero) tri(succ)` — replaces every tip by its depth in the tree, `zero` the
   constant function returning 0 and `succ` the successor],

  [`depth`],
  [`depth=depths max`],
)]<tree-depth>

#pagebreak(weak: true)
= `/` is all of

#disp[#definition[
#align(center, `x (R/S) y⟺∀p. y S p→x R p`)
#align(center, `x (S\R) y⟺∀p. p S x→p R y`)
#align(center, `/compares images: S(y)⊆R(x).   \ compares preimages: S°(x)⊆R°(y).`)
#align(center, `example: A admires,H hates,W works for`)
#align(center, `x (A/H) y — x admires everyone y hates.`)
#align(center, `x (H\A) y — everyone who hates x admires y.`)
]]<div-defn>


== `(R/S)(S/W)⊑R/W`


#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  edges(-9.6, -4.8, ADMIRES); edges(0, -4.8, HATES); edges(0, 4.8, HATES); edges(9.6, 4.8, WORKS)
  arc((-9.6, 1.6), (-0.8, 1.6), 1, [`A/H` admires all])
  arc((0.8, 1.6), (9.6, 0), 1, [`H/W` hates all])
  arc((-9.6, 1.6), (9.6, 0), -1, [`A/W` admires all], col: GIVEN1, h: 5.4, cx: 8)
  arc((-9.6, -1.6), (9.6, 0), -1, [`A/W` admires all], col: GIVEN1, h: 7.0, cx: 8)
  nodes(-9.6, ADMIRES); ings(-4.8); nodes(0, HATES); ings(4.8); nodes(9.6, WORKS)
  head(-9.6, [`A` — `x` admires]); head(0, [`H` — `y` hates])
  head(9.6, [`W` — `z` works for])
}))]<div-comp-pic>

// The whole of each quotient in one line of English, laid out as the law reads: the two legs of the
// path first, the arrow they are contained in last.
#disp[#block(inset: (top: 2pt), text(10.5pt)[
  `x (A/H) y` — `x` admires everyone `y` hates \
  `y (H/W) z` — `y` hates everyone `z` works for \
  `x (A/W) z` — `x` admires everyone `z` works for
])]<div-comp-gloss>

`(A/H)(H/W)` is a path: `x` → `y` → `z`, and that is all of it. `A/W` also holds of
`x'`, who admires everyone `z` works for — but `x'` does not admire everyone anybody
hates, so nothing composes to it. The missing path is exactly the strictness of
// Boxed so the line breaker cannot split the law after a `/` — it lands at the end of the paragraph.
#box[`(R/S)(S/W)⊑R/W`].

// One law per row, and the picture column takes the rest of the 22cm: `le_div_iff` is a `⟺` between
// two containments, four sub-pictures wide (10.9cm before scaling), the widest picture in the note.
#disp[#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`X⊑R/S⟺XS⊑R` \ #src[`X` is any `x`-to-`y` pairing; one that only pairs `x` with a `y`
   such that `x` admires everyone `y` hates lies inside `R/S`, and `R/S` is the largest such.]],
  P(p-le-div),

  [`X⊑S\R⟺SX⊑R` \ #src[The mirror — divide on the left when `x` comes first.]],
  P(p-le-ldiv),

  [`(R/S)S⊑R` \ #src[There is a `y` such that `x` admires everyone `y` hates, and `p` is one of
   the people `y` hates — then `x` admires `p` too. Strict at `S=∅`: `R/S` is everyone, `(R/S)S=∅`.]],
  P(p-div-cancel),

  [`S (S\R)⊑R` \ #src[The mirror.]],
  P(p-ldiv-cancel),

  [*associate:* `R/(S₁S₂)=(R/S₂)/S₁` \ #src[*A friend's enemy* is two hops: divide by the far end
   first.]],
  P(p-div-assoc),

  [`(S₁S₂)\R=S₂\(S₁\R)` \ #src[The mirror.]],
  P(p-ldiv-assoc),

  [*maps:* `f (R/S)=(fR)/S` \ #src[Rename `x` before or after dividing — the licence to write
   `fR/S`.]],
  P(p-map-div),

  [`R/(fS)=(R/S)f°` \ #src[Rename `y`: a map leaves a denominator as `f°` outside the box.
 ]],
   // lean:AOP.A4_4.div_comp_recip_map@bc41ec1a
  P(p-div-map),

  [`(R/S)(S/W)⊑R/W` \ #src[Someone who admires all of a hate-set that already covers everyone
   `z` works for admires those people too.]],
  P(p-div-comp),

  [`𝟙⊑R/R` \ #src[`R/R` runs admirer to admirer: each admires everyone they admire. Strict: two
   people who each admire only `a` and `b` admire each other's idols too, and still stay two people.]],
  P(p-one-div),

  [`(R/R)(R/R)=R/R` \ #src[`R/R` is the preorder *admires at least as much as*, and a preorder is
   idempotent. Freyd writes `⊑`; with `𝟙⊑R/R` above it is an equality.]],
  P(p-div-self-idem),

  [`(R/R)R=R` \ #src[Reaching `p` through someone whose idols `x` fully admires is reaching `p`
   directly, since `x` admires their own idols.]],
  P(p-div-self),

  [`R/𝟙=R` \ #src[Dividing by `𝟙`: `p`'s set is just `{p}`, so admiring all of it is admiring `p`.]],
  P(p-div-one),

  [`R/(S₁∪S₂)=R/S₁∩R/S₂` \ #src[Admiring a combined hate-set is admiring each set in full.]],
  P(p-div-union),

  [`S\(R/W)=(S\R)/W` \ #src[Which is why `S\R/W` needs no bracket.]],
  P(p-ldiv-div),
)]<div-laws>

Fifteen laws, fifteen pictures, and not one shows a generator: `∩`, `∪`, `°` and composition are what
the Frobenius generators build, and `/` is none of those — it is posited, with nothing to unfold.

#pagebreak(weak: true)
= $frac(R, S)$

#disp[#definition[
$frac(R, S)$ `≜(R/S)∩(S/R)°` #src[]. In `Rel` `x` and `y` has the same image:
// lean:Freyd.S2_30.symmDiv@7e3fc41a
`∀p. (x R p⟺y S p)`
]]<syq-defn>

// The meet read one factor at a time, in the vocabulary of the section above: `/` supplies ALL, the
// converse of the mirror division supplies ONLY, and the meet is what names this section.
#disp[#block(inset: (top: 2pt), text(10.5pt)[
  `x (A/H) y` — `x` admires everyone `y` hates \
  `x ((H/A)°) y` — `x` admires only people `y` hates \
  `x ((A/H)∩(H/A)°) y` — `x` admires only and all whom `y` hates
])]<syq-gloss>

`x` admires exactly whom `y` hates: `/` is *all of*, $frac(R, S)$ is *only all of*.


#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  // `A`: who each `x` admires.  `H`: who each `y` hates.  `x` and `y` name the same three.
  for p in ("a", "b", "c") { syqedge(ADMIRERS.x1, PEOPLE.at(p), INDUCED, 1.1) }
  for p in ("a", "b") { syqedge(ADMIRERS.x2, PEOPLE.at(p), INDUCED.lighten(60%), 0.7) }
  for p in ("a", "b", "c") { syqedge(HATERS.y1, PEOPLE.at(p), SLACK, 1.1) }
  for p in ("a", "b", "d") { syqedge(HATERS.y2, PEOPLE.at(p), SLACK.lighten(60%), 0.7) }

  // The shared column, filled: exactly the people both sides of the matched pair reach.
  // `d` stays hollow — `y'` reaches it and no admirer does.
  for p in ("a", "b", "c") { d.circle(PEOPLE.at(p), radius: 0.17, fill: GIVEN2, stroke: GIVEN2) }
  d.circle(PEOPLE.d, radius: 0.17, fill: white, stroke: 0.9pt + black)
  // Named as in the division picture, and above the dot: beside it the name would land on a fan.
  for (p, q) in PEOPLE { d.content((q.at(0), q.at(1) + 0.62), raw(p)) }

  // The result: the one pair whose two sets agree.  It runs over the top from `x` to `y` — an
  // arc slung underneath would start below `x'` and read as the wrong pair.
  d.bezier((ADMIRERS.x1.at(0), 2.35), (HATERS.y1.at(0), 2.35), (-2.6, 4.4), (2.6, 4.4),
    mark: (end: ">", scale: 0.6), stroke: 1pt + GIVEN2)
  // Clear of the curve's apex (y ≈ 3.9), because the fraction is two lines tall and its bar sitting
  // on the arc would read as part of it.
  d.content((0, 4.4), box(inset: 3pt, fill: white)[#text(10pt, GIVEN2)[$frac(A, H)$]])

  syqnode(ADMIRERS.x1, GIVEN2, rgb("#f2e9f8"), `x`, ring: 0.7pt + GIVEN2)
  syqnode(ADMIRERS.x2, black, white, `x'`)
  syqnode(HATERS.y1, GIVEN2, rgb("#f2e9f8"), `y`, ring: 0.7pt + GIVEN2)
  syqnode(HATERS.y2, black, white, `y'`)
  // The family names sit outside the columns at mid-height: the top belongs to the arc, and beside
  // an arrow they would land on another arrow.
  d.content((-6.5, 0), text(10pt, INDUCED)[`A`]); d.content((6.5, 0), text(10pt, SLACK)[`H`])
}))]<syq-pic>

#disp[#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

 [$X ⊑ frac(R, S) ⟺ X S ⊑ R$ and `X°R⊑S` #src[]],
  // lean:Freyd.S2_30.le_symmDiv_iff@b1cfe4dc
  [`X` may pair `x` with `y` only when `x` admires exactly whom `y` hates. Both halves must typecheck,
   so the operation is *partial*.],

 [$(frac(R, S))^circle.small = frac(S, R)$ #src[]],
  // lean:Freyd.S2_30.symmDiv_recip@b93b9076
  [Matching is symmetric.],

 [$frac(R, S) frac(S, W) ⊑ frac(R, W)$ #src[]],
  // lean:Freyd.S2_30.symmDiv_comp@5930c455
  [And transitive.],

  [$frac(R, S) S ⊑ R$],
  [$(∃ y. thin x (frac(R, S)) y ∧ y S p) → x R p$ \
   `x only admires whom y hates` \
   $frac(R, S) S = "Dom"(frac(R, S)) R$],

 [$frac(R, R) R = R$ #src[]],
  // lean:Freyd.S2_30.symmDiv_self_comp@2b447963
  [$(∃ y. thin x (frac(R, R)) y ∧ y R p) ⟺ x R p$ \
   `x and y admire the same people` \
   `y=x always qualifies (𝟙⊑R%R below)`],

 [$𝟙 ⊑ frac(R, R)$ #src[]],
  // lean:Freyd.S2_30.symmDiv_self_reflexive@9e2af20e
  [$x (frac(R, R)) y$ if `x` and `y` admires the same peoples.],

  [$(frac(R, R))^2 = frac(R, R)$],
  [So the relation *admires the same people* is an equivalence relation.],

  [$X ⊑ frac(R, R) ⟺ X R ⊑ R$, for symmetric `X`
 #src[]],
   // lean:Freyd.S2_11.symmetric_le_symmDiv_self_iff@a5fc04b4
  [The largest symmetric arrow that leaves `R` alone.],

 [$frac(R, 𝟙)$ is the *simple part* of `R` #src[]],
  // lean:Freyd.S2_30.simplePart@3779ee66
  [The people who admire exactly one person and nobody else. It equals `R` only when `R` is simple, unlike
   `R/𝟙=R`.],

 [`Dom` $frac(R, S)$ `=𝟙∩(R/S)(S/R)` #src[]],
  // lean:Freyd.S2_30.dom_symmDiv@0ef1aa31
  [Its domain is the *domain of simplicity* of `R`.],
)]<syq-readings>

#pagebreak(weak: true)
= Freyd's Power allegories <sec-power>

#disp[#definition[
A *power allegory* is a division allegory with one unary operation on arrows, `∋` *epsiloff*,
subject to

// Freyd's three display lines, in his order, with the names he gives the last two.  A stroke-less
// table, not three centred lines: the names have to hang off the containments they name.
#align(center, table(
  columns: 2, stroke: none, inset: (x: 14pt, y: 3pt), align: (left + horizon, left + horizon),
  [$#e[R] □ = R □, quad #e[R] = #e[R □]$], [],
  [$𝟙 ⊑ (R slash #e[R])(#e[R] slash R)$], [$#e[R]$ is *thick*],
  [$frac(#e[R], #e[R]) = 𝟙$], [$#e[R]$ is *straight*],
))

`R□` is `R`'s target, an identity arrow. For `R : A⟶B` write `∋ : EB⟶B`, dropping the
subscript.

// The converse of epsiloff IS membership, and the note's pointwise glosses already write it `∈`.
`∈≜∋° : A⟶EA`
]]<pow-defn>

#disp[
  #show table.cell.where(x: 0): rownum
  #table(
  columns: (7.95cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [$#e[R] □ = R □$, #h(4pt) $#e[R] = #e[R □]$],
  [One `∋` per object, not per arrow.],

  [`∋` is *thick*],
  [*Comprehension*: every `x` has a set of exactly the people `x` admires.],

  [$frac(R, ∋)$ ` : A⟶EB`, for `R : A⟶B` ],
  [convert a relation to a function. `a` $frac(R, ∋)$ ` ={b|a R b}` ],
  [$frac(#[`R`], ∋)$ is a *map*],  [],

 [$frac(#[`R`], ∋)$ `∋=R` ], [#src[]],
  // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a

  [`F⊑` $frac(#[`F∋`], ∋)$, `F` simple],
 [A partial choice of sets is inside the total one. #src[]],
  // lean:Freyd.S2_40.simple_le_Λ_eps@a28487fe

  [$frac(#[`𝟙`], ∋)$, the *singleton map*, monic],
  [The one-person set.],

  [$frac(#[`∋`], ∋)$ `=𝟙`],
 [Make the set of a set, then read it back one level down. #src[]],
  // lean:AOP.A4_6.Λ_eps_reflection@2e9ddea3

  [*fusion:* $frac(#[`fR`], ∋)$ `=f` $frac(#[`R`], ∋)$, `f` a map],
  [Naturality of the unit, `f` $frac(#[`𝟙`], ∋)$ `=` $frac(#[`𝟙`], ∋)$ `(E(f))`.
 #src[]],
   // lean:AOP.A4_6.Λ_fusion@9d7bda13

  [$frac(#[`f`], ∋)$ `=f` $frac(#[`𝟙`], ∋)$, `f` a map],
  [Rename first or take singletons first — the fusion row above at `R=𝟙`.],

  [$frac(R, S) = frac(R, ∋) (frac(S, ∋))^circle.small$],
  [`x` and `y` match when `R` sends `x` and `S` sends `y` to the same set.],

  [`E(R)≜` $frac(#[`∋R`], ∋)$, `E≜` $frac(#[`∋·`], ∋)$], [`E(R): EA⟶EB`, image of a set of A],
  [$frac(#[`R`], ∋)$ `=` $frac(#[`𝟙`], ∋)$ `E(R)`],
 [$frac(#[`𝟙`], ∋)$`: x↦{x}` #src[]],
  // lean:AOP.A4_6.Λ_eq_singleton_existsImage@02b29ea8
  [$frac(#[`S`], ∋)$ `E(R)=` $frac(#[`S`], ∋)$ $frac(#[`∋R`], ∋)$ `=` $frac(#[`SR`], ∋)$],
  [absorption — the monad's composition law, $frac(#[`S`], ∋)$ `⋄` $frac(#[`R`], ∋)$ `=`
 $frac(#[`SR`], ∋)$, §@sec-kleisli #src[]],
   // lean:AOP.A4_6.Λ_absorption@e87bd8f2

  [`subset≜∋/∋ : EA⟶EA`],
  [`xs subset ys⟺∀a. ys∋a→xs∋a`, that is `ys⊆xs`, not `xs⊆ys`.],
)]<pow-laws>

== `i⊣E` Power Allegory defined as adjunction <sec-adj-E>

// The factorisation the whole adjunction is about, drawn once.  Middle arrow is `E(R)`, NOT `P(R)`:
// the two agree on maps only (B&dM p. 119), and `𝟙/∋ P(R)` is every nonempty subset of `R(a)`.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
  let (T, B) = (1.5, -1.5)
  let (xA, xB) = (-3.1, 3.1)
  ar((xA, T), (xB, T), GIVEN1, s0: 0.45, s1: 0.45)
  ar((xA, T), (xA, B), GIVEN2, s0: 0.5, s1: 0.5)
  ar((xA, B), (xB, B), GIVEN2, s0: 0.85, s1: 0.85)
  ar((xB, B), (xB, T), GIVEN2, s0: 0.5, s1: 0.45)
  // The diagonal cuts the square into the two laws: upper left `𝟙/∋ E(R) = R/∋`, lower right `(R/∋) ∋ = R`.
  ar((xA, T), (xB, B), INDUCED, dash: "dashed", s0: 0.5, s1: 0.75)
  lab(0, T + 0.5, GIVEN1)[`R`]
  // Each label also says what the arrow IS in the one operator, so the four read as instances of it.
  lab(xA - 0.62, 0, GIVEN2)[$frac(#[`𝟙`], ∋)$]
  lab(0, B - 0.95, GIVEN2)[#align(center)[`E(R)` \
    #text(8.5pt)[`E=` $frac(#[`∋·`], ∋)$]]]
  lab(xB + 0.35, 0, GIVEN2)[`∋`]
  lab(1.25, 0.2, INDUCED)[$frac(#[`R`], ∋)$]
  node(xA, T, black, `A`); node(xB, T, black, `B`)
  node(xA, B, black, `EA`); node(xB, B, black, `EB`)
  }),
  // `𝟙/∋` opens the `i E` pair and `∋` closes it again, so the strand running in and out of a panel is
  // the one functor; the panel beside it draws that same functor as the plain wire the law equates it to.
  context {
    let g = grid(columns: 2, column-gutter: 14pt, align: horizon,
      snake(`i`, `E`, false), snake(`E`, `i`, true))
    let w = measure(g).width
    grid(columns: 1, row-gutter: 8pt, align: center, g,
      box(width: w, grid(columns: (1fr, 1fr), align: (center + horizon, center + horizon),
 [$frac(#[`𝟙`], ∋)$ `∋=𝟙` #src[]],
        // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a
 [$frac(#[`∋`], ∋)$ `=𝟙` #src[]])))
        // lean:AOP.A4_6.Λ_eps_reflection@2e9ddea3
  },
  [$frac(#[`R`], ∋)$ `∋=R` #h(1.4cm)
   #src[`EA` is the powerset of `A`. B&dM write `PA` — standard mathematics, but here `P` is
 already the relator `P(R)`. ]],
   // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a
  // The two snakes are four panels wide, so the pair only clears the 22cm text block scaled down.
  s: 95%,
)]<adj-E-bend>

#block[#src[`i` is the inclusion `Map(𝒜)⟶𝒜`, doing nothing, so `E` is both the functor and the
monad `iE`.]]

// The heading gets its own page: §10.1's pair fills the foot of the previous one, and the definition
// below is unbreakable, so the heading was left standing alone there.
#pagebreak(weak: true)
== `𝒜≅Kleisli(E)` <sec-kleisli>

// Every ingredient is a row of @pow-laws; nothing here is new.  `union` is `E(∋)`: the counit with
// `E` applied to it, which is the multiplication the adjunction hands back.
#disp[#block(breakable: false)[#definition[
`E(R)≜` $frac(#[`∋R`], ∋)$, #h(4pt) $frac(#[`𝟙`], ∋)$ ` : A⟶EA`, #h(4pt)
`union=E(∋)=` $frac(#[`∋∋`], ∋)$ ` : E(EA)⟶EA`

`f⋄g≜f E(g) union : A⟶EC`, #h(4pt) for `f : A⟶EB` and `g : B⟶EC`

#src[the monad is on `Map(𝒜)`, not on the allegory: `E` is a relator on all relations, but
$frac(#[`𝟙`], ∋)$,
`union` and `f E(g) union` are maps, and the Kleisli construction happens where they live.]
]]]<kleisli-defn>

#disp[
#zline(
  zsqc([$frac(#[`S`], ∋)$ `⋄` $frac(#[`R`], ∋)$], none),
  zstep(op: sym.eq, under: true)[definition of `⋄`, `union=E(∋)`],
  zsqc([$frac(#[`S`], ∋)$ `E(`$frac(#[`R`], ∋)$`)E(∋)`], none),
  zstep(op: sym.eq, under: true)[`E` a functor, `E(X)E(Y)=E(XY)`],
  zsqc([$frac(#[`S`], ∋)$ `E(`$frac(#[`R`], ∋)$`∋)`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[@pow-laws, $frac(#[`R`], ∋)$ `∋=R`],
  zsqc([$frac(#[`S`], ∋)$ `E(R)`], none),
  zstep(op: sym.eq, under: true)[@pow-laws, absorption],
  zsqc([$frac(#[`SR`], ∋)$], none),
)
#align(center, block(width: 16.5cm, inset: (y: 4pt))[#align(center)[#src[the first three steps only
  unfold `⋄` — `E` is a functor, so `E(`$frac(#[`R`], ∋)$`)union=E(`$frac(#[`R`], ∋)$`∋)=E(R)` and the
  `union` is gone. Absorption, the row of @pow-laws, is the whole law, and it is the functoriality
 of $frac(#[`·`], ∋)$. ]]])
  // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a lean:AOP.A4_6.Λ_absorption@e87bd8f2
]<kleisli-comp>

#block[#src[`𝟙` goes to $frac(#[`𝟙`], ∋)$, the Kleisli identity, by definition — so
$frac(#[`·`], ∋)$ is an isomorphism of categories `𝒜≅Kleisli(E)`, and §@sec-adj-E's `i⊣E` is the
Kleisli adjunction. `i` is the identity on objects, so every object of the allegory is free.]]

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
  columns: (1fr, 5.2cm),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the statement*], [*B&dM*]),

 [For `f` a map, `F(f)` is a map and `F(f°)=F(f)°`. #src[]], [Lemma 5.1],
  // lean:AOP.A5_1.map_is_map@8f150beb lean:AOP.A5_1.map_recip_map@c9f5d6f2
  [Over a *tabular* allegory a functor is a relator `⟺` it preserves `°`.], [Theorem 5.1],
  [`F(R°)=F(R)°` for every `R`, so `F(R)°` needs no bracket.], [after Theorem 5.1, p. 113],
  [Two relators agreeing on maps are equal.], [Corollary 5.1],
 [`F(X∩Y)=F(X)∩F(Y)` for `X,Y` coreflexive. #src[]], [Ex 5.2],
  // lean:AOP.A5_1.map_inter_coreflexive@a2233804
 [`F(R∩S)⊑F(R)∩F(S)`, and strictly. #src[]], [Ex 5.2, the restriction],
  // lean:AOP.A5_1.map_inter_le@af565f80
 [`F(Dom(R))=Dom(F(R))` for `F` preserving `°`. #src[]], [],
  // lean:AOP.A5_1.map_dom@5e9ecd68
)]<relator-laws>

The *power relator* `P` — `xs P(R) ys⟺(∀a∈xs. ∃b∈ys. a R b)∧(∀b∈ys. ∃a∈xs. a R b)` — is where
the fourth is strict: for `R={(a₁,b₁),(a₂,b₂)}` and `S={(a₁,b₂),(a₂,b₁)}` the pair
`({a₁,a₂},{b₁,b₂})` is in `P(R)∩P(S)`, while `R∩S=∅`.

== Fork `⟨R,S⟩`

#disp[#definition[
The *fork* of `R : C⟶A` and `S : C⟶B` is `⟨R,S⟩≜Rπ₁°∩Sπ₂°` #src[],
// lean:AOP.A5_2.pair@df1791ca
where `(π₁,π₂)` is the tabulation of `⊤`
#src[].
// lean:AOP.A5_2.eq_topMor@31e6622f lean:AOP.A5_2.joint_id@f9cba0f7
]]<fork-defn>

#disp[#block(inset: (y: 6pt))[
 `⟨R,S⟩π₁=Dom(S)R` #src[] #h(1.4cm)
  // lean:AOP.A5_2.pair_outl@5cb53112
 `⟨R,S⟩π₂=Dom(R)S` #src[]
  // lean:AOP.A5_2.pair_outr@a6bc4ebd
]]<fork-proj>

#disp[#row((box(inset: (right: 18pt), cetz.canvas(length: 0.8cm, {
  let (C, A, B, P) = ((-3, 0), (0, 1.7), (0, -1.7), (3, 0))
  ar(C, A, GIVEN1); ar(C, B, GIVEN2); ar(P, A, GIVEN1, s0: 0.75); ar(P, B, GIVEN2, s0: 0.75)
  ar(C, P, INDUCED, dash: "dashed", s1: 0.95)
  lab(-1.75, 1.12, GIVEN1)[`R`]; lab(-1.75, -1.12, GIVEN2)[`S`]
  lab(1.8, 1.12, GIVEN1)[`π₁`]; lab(1.8, -1.12, GIVEN2)[`π₂`]
  lab(-1.0, 0.32, INDUCED)[$chevron.l R, S chevron.r$]
  node(C.at(0), C.at(1), black, $C$)
  node(A.at(0), A.at(1), GIVEN1, $A$); node(B.at(0), B.at(1), GIVEN2, $B$)
  node(P.at(0), P.at(1), INDUCED, $A times B$)
})), pairstr()))]<fork-pic>

A domain is coreflexive, so `⟨R,S⟩π₁⊑R`, with equality exactly when `S` is entire; for maps both
triangles commute and `⟨f,g⟩` is unique. In `Rel`, `c ⟨R,S⟩ (a,b)` iff `c R a` and `c S b` — copy `c`, then
`R` on one strand and `S` on the other, which is `◁(R⊗S)` on the right.

No `°` survives the translation. `π₁=𝟙⊗⊸` discards the second component, so `π₁°=𝟙⊗⟜`
*creates* one out of nothing, and `∩` is copy, run both, merge. Draw that and the created strands —
the two dots with no left end, and the crossing they force — are merged against real ones, which is
the monoid's unit law:

// The chain at FULL size: `chain`'s 62% is calibrated for the exported pictures, which are drawn on a
// bigger canvas than these two.
#disp[#chain((cetz.canvas(length: 0.8cm, {
  wire((0, 0), (0.8, 0)); wiredot((0.8, 0))
  bend((0.8, 0), (1.4, 1.5)); bend((0.8, 0), (1.4, -1.5))
  wire((1.4, 1.5), (1.6, 1.5)); gbox((1.6, 1.5), [R]); wire((2.52, 1.5), (3.7, 1.5))
  wire((1.4, -1.5), (1.6, -1.5)); gbox((1.6, -1.5), [S]); wire((2.52, -1.5), (3.7, -1.5))
  // `π₁°=𝟙⊗⟜` is a PAIR: `R`'s wire and the created one beside it.  Merging the pairs componentwise
  // is what crosses.
  wiredot((2.7, 0.9)); wire((2.7, 0.9), (3.7, 0.9))
  wiredot((2.7, -0.9)); wire((2.7, -0.9), (3.7, -0.9))
  bend((3.7, 1.5), (5.4, 0.3), k: 0.4); bend((3.7, -0.9), (5.4, 0.3), k: 0.4); wiredot((5.4, 0.3))
  bend((3.7, 0.9), (5.4, -0.3), k: 0.4); bend((3.7, -1.5), (5.4, -0.3), k: 0.4)
  wiredot((5.4, -0.3))
  wire((5.4, 0.3), (6.0, 0.3)); wire((5.4, -0.3), (6.0, -0.3))
  lab(-0.35, 0, black)[$C$]; lab(6.35, 0.3, GIVEN1)[$A$]; lab(6.35, -0.3, GIVEN2)[$B$]
}), pairstr(eq: true)), ("", [`⟜▷=𝟙` on each half #src[]]), s: 100%)]<fork-collapse>
// lean:AOP.A5_2.pair@df1791ca


=== Relational product `R×S`

#disp[#definition[
`R×S≜⟨π₁R,π₂S⟩` #src[], a relator in each argument
// lean:AOP.A5_2.prodMap@28e34ad0
#src[] but no longer a categorical product.
// lean:AOP.A5_2.prod@64fdb8dc
]]<relprod-defn>

// The same pair of pictures with `C` replaced by `C × D`, once per projection: the two triangles
// become two squares, and the copy dot goes away — `R × S` is the two strands side by side.
#disp[#row((box(inset: (right: 18pt), cetz.canvas(length: 0.8cm, {
  let (C, CD, D) = ((-2.7, 1.7), (-2.7, 0), (-2.7, -1.7))
  let (A, AB, B) = ((2.7, 1.7), (2.7, 0), (2.7, -1.7))
  ar(CD, C, GIVEN1, s0: 0.55); ar(CD, D, GIVEN2, s0: 0.55)
  ar(AB, A, GIVEN1, s0: 0.55); ar(AB, B, GIVEN2, s0: 0.55)
  ar(C, A, GIVEN1); ar(D, B, GIVEN2)
  ar(CD, AB, INDUCED, dash: "dashed", s0: 0.95, s1: 0.95)
  lab(-3.1, 0.85, GIVEN1)[`π₁`]; lab(-3.1, -0.85, GIVEN2)[`π₂`]
  lab(3.1, 0.85, GIVEN1)[`π₁`]; lab(3.1, -0.85, GIVEN2)[`π₂`]
  lab(0, 2.0, GIVEN1)[`R`]; lab(0, -1.4, GIVEN2)[`S`]
  lab(-1.2, 0.32, INDUCED)[$R times S$]
  lab(1.2, 0.85, SLACK, rot: -135deg)[`⊑`]; lab(1.2, -0.85, SLACK, rot: 135deg)[`⊑`]
  node(C.at(0), C.at(1), GIVEN1, $C$); node(D.at(0), D.at(1), GIVEN2, $D$)
  node(CD.at(0), CD.at(1), INDUCED, $C times D$)
  node(A.at(0), A.at(1), GIVEN1, $A$); node(B.at(0), B.at(1), GIVEN2, $B$)
  node(AB.at(0), AB.at(1), INDUCED, $A times B$)
})), cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, y), (0.5, y)); gbox((0.5, y), [R]); wire((1.42, y), (2.0, y))
  wire((0, -y), (0.5, -y)); gbox((0.5, -y), [S]); wire((1.42, -y), (2.0, -y))
  lab(-0.35, y, GIVEN1)[$C$]; lab(-0.35, -y, GIVEN2)[$D$]
  lab(2.35, y, GIVEN1)[$A$]; lab(2.35, -y, GIVEN2)[$B$]
})))]<relprod-pic>

Right-then-up is `(R×S)π₁`, up-then-right is `π₁R`, and `(R×S)π₁⊑π₁R`, equality when `S` is
entire. In `Rel`, `(c,d) (R×S) (a,b)` iff `c R a` and `d S b` — two strands side by side, no copy
dot: `R×S=R⊗S`.

=== Absorption

For `X : E⟶C` and `Y : E⟶D`, `⟨X,Y⟩(R×S)=⟨XR,YS⟩`. Both sides are this picture:

// ONE picture, not two with an `=`: pushing `R ⊗ S` past `X ⊗ Y` is interchange, already spent by the
// notation — both sides are the same strokes.  All of B&dM (5.3), whose direct proof needs two lemmas.
#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (1.9, y)); wire((1.55, -y), (1.9, -y))
  gbox((1.9, y), [X]); gbox((1.9, -y), [Y])
  wire((2.82, y), (3.2, y)); wire((2.82, -y), (3.2, -y))
  gbox((3.2, y), [R]); gbox((3.2, -y), [S])
  wire((4.12, y), (4.7, y)); wire((4.12, -y), (4.7, -y))
  lab(-0.35, 0, black)[$E$]; lab(5.05, y, GIVEN1)[$A$]; lab(5.05, -y, GIVEN2)[$B$]
}))]<absorption-pic>

// One run of boxes on one strand, for the two book tables below: `"r"` a relation (chamfered), `"m"` a
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

  [`R×S=⟨π₁R,π₂S⟩`],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    let (a, b) = (1.35, 0.62)
    lab(-0.35, y, black)[$C$]; lab(-0.35, -y, black)[$D$]
    brun(0, y, (([R], "r"),)); brun(0, -y, (([S], "r"),))
    lab(1.95, y, black)[$A$]; lab(1.95, -y, black)[$B$]
    lab(2.6, 0, black)[$=$]
    lab(3.0, 1.0, black)[$C$]; lab(3.0, -1.0, black)[$D$]
    // The fork copies the WHOLE pair, and each branch discards the component it does not use.
    wire((3.35, 1.0), (3.9, 1.0)); wiredot((3.9, 1.0))
    bend((3.9, 1.0), (4.7, a)); bend((3.9, 1.0), (4.7, -b))
    wire((3.35, -1.0), (3.9, -1.0)); wiredot((3.9, -1.0))
    bend((3.9, -1.0), (4.7, b)); bend((3.9, -1.0), (4.7, -a))
    brun(4.7, a, (([R], "r"),)); brun(4.7, -a, (([S], "r"),))
    wire((4.7, b), (5.3, b)); wiredot((5.3, b))
    wire((4.7, -b), (5.3, -b)); wiredot((5.3, -b))
    lab(6.65, a, black)[$A$]; lab(6.65, -a, black)[$B$]
  }), s: 74%),

  [`⟨X,Y⟩(R×S)=⟨XR,YS⟩` \ #src[both sides are the same strokes — @absorption-pic. Its `⊑`
   half is Ex 5.8, that half at `S:=𝟙` and at `R:=𝟙` B&dM's (5.4), (5.5) — stages of their proof of
   this row; Ex 5.6 is the `(R×S)(U×V)=(RU)×(SV)` it yields, at `R:=𝟙` and `V:=𝟙`.
 ]],
   // lean:AOP.A5_2.pair_prodMap@9d21307f
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, 0, black)[$E$]
    wcopy((0.5, 0), li: 0.5, lo: 0.55, sp: y)
    brun(1.05, y, (([X], "r"), ([R], "r"))); brun(1.05, -y, (([Y], "r"), ([S], "r")))
    lab(4.25, y, black)[$A$]; lab(4.25, -y, black)[$B$]
  }), s: 74%),

 [`⟨R,S⟩π₁=Dom(S)R` \ #src[@fork-proj]],
  // lean:AOP.A5_2.pair_outl@5cb53112
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, 0, black)[$C$]
    wcopy((0.5, 0), li: 0.5, lo: 0.55, sp: y)
    brun(1.05, y, (([R], "r"),))
    brun(1.05, -y, (([S], "r"),)); wiredot((2.65, -y))
    lab(3.0, y, black)[$A$]
  }), s: 74%),

 [`⟨R,S⟩π₂=Dom(R)S` \ #src[@fork-proj]],
  // lean:AOP.A5_2.pair_outr@a6bc4ebd
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, 0, black)[$C$]
    wcopy((0.5, 0), li: 0.5, lo: 0.55, sp: y)
    brun(1.05, y, (([R], "r"),)); wiredot((2.65, y))
    brun(1.05, -y, (([S], "r"),))
    lab(3.0, -y, black)[$B$]
  }), s: 74%),

 [`⟨X,Y⟩⟨R,S⟩°=(XR°)∩(YS°)` #src[]],
  // lean:AOP.A5_2.pair_recip_pair@c082becf
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, 0, black)[$E$]
    wcopy((0.5, 0), li: 0.5, lo: 0.55, sp: y)
    brun(1.05, y, (([X], "r"), ([R], "c"))); brun(1.05, -y, (([Y], "r"), ([S], "c")))
    wmerge((4.46, 0), li: 0.55, lo: 0.5, sp: y)
    lab(5.3, 0, black)[$C$]
  }), s: 74%),

  [`⟨R,S⟩°⟨P,Q⟩⊑(R°P)×(S°Q)`],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, y, black)[$A$]; lab(-0.35, -y, black)[$B$]
    brun(0, y, (([R], "c"),)); brun(0, -y, (([S], "c"),))
    wmerge((2.15, 0), li: 0.55, lo: 0.5, sp: y)
    lab(2.65, 0.4, black)[$C$]
    wcopy((3.15, 0), li: 0.5, lo: 0.55, sp: y)
    brun(3.7, y, (([P], "r"),)); brun(3.7, -y, (([Q], "r"),))
    lab(5.65, y, black)[$A'$]; lab(5.65, -y, black)[$B'$]
    lab(6.4, 0, black)[`⊑`]
    lab(7.15, y, black)[$A$]; lab(7.15, -y, black)[$B$]
    brun(7.5, y, (([R], "c"), ([P], "r"))); brun(7.5, -y, (([S], "c"), ([Q], "r")))
    lab(10.7, y, black)[$A'$]; lab(10.7, -y, black)[$B'$]
  }), s: 74%),

  [`f⟨R,S⟩=⟨fR,fS⟩` \ #src[`f` a map; it fails for an arbitrary arrow;
 ]],
   // lean:AOP.A5_2.map_comp_pair@bbc85d03
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, 0, black)[$D$]
    brun(0, 0, (([`f`], "m"),))
    wcopy((2.15, 0), li: 0.55, lo: 0.55, sp: y)
    brun(2.7, y, (([R], "r"),)); brun(2.7, -y, (([S], "r"),))
    lab(4.65, y, black)[$A$]; lab(4.65, -y, black)[$B$]
    lab(5.3, 0, black)[$=$]
    lab(5.95, 0, black)[$D$]
    wcopy((6.5, 0), li: 0.5, lo: 0.55, sp: y)
    brun(7.05, y, (([`f`], "m"), ([R], "r"))); brun(7.05, -y, (([`f`], "m"), ([S], "r")))
    lab(10.25, y, black)[$A$]; lab(10.25, -y, black)[$B$]
  }), s: 74%),

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

  [`[R,S]≜l°R∪r°S` \ #src[The tape is the union — a particle entering at `A+B` takes exactly
   one branch — and the two mirrored boxes are what makes the branches disjoint.]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62                  // the tape's two branches, at the exported pictures' half-spacing
    wire((0, 0), (0.34, 0))
    // 1.57 = y + 0.95, the clearance §@sec-comb's tapes leave above a branch they label.
    tape((0.34, -1.57), (4.24, 1.57))
    tape-fork((0.56, 0), sp: y, len: 0.42)
    // Mirrored and tinted: this file draws a converse by flipping the box, so these are `l°` and `r°`.
    gbox((0.98, y), [`l`], flip: true, fill: TINT); wire((1.90, y), (2.24, y)); gbox((2.24, y), [R])
    wire((3.16, y), (3.60, y))
    gbox((0.98, -y), [`r`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y)); gbox((2.24, -y), [S])
    wire((3.16, -y), (3.60, -y))
    lab(2.07, 1.24, black)[$A$]; lab(2.07, 0, black)[$B$]
    tape-join((4.02, 0), sp: y, len: 0.42)
    wire((4.24, 0), (4.58, 0))
    lab(-0.9, 0, black)[$A + B$]; lab(4.93, 0, black)[$C$]
  }), s: 85%),

  [`[R,S]=[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]∋`], [],
  [`R+S≜[Rl,Sr]`], [],
  [`l[R,S]=R`, `r[R,S]=S`, and `[R,S]` is the only such arrow
 #src[,
   // lean:AOP.A5_3.u₁_junc@a01a115a lean:AOP.A5_3.u₂_junc@e692ee94
 ]], [],
   // lean:AOP.A5_3.junc_unique@192cec99

  // A map is the UNCHAMFERED box (`chamfer: false`), so the injection and its converse are told apart
  // by shape as well as by the tint, and a round trip reads as one box undoing the other.
  [`ll°=𝟙=rr°`],
  P(cetz.canvas(length: 0.8cm, {
    wire((0, 0), (0.34, 0)); gbox((0.34, 0), [`l`], chamfer: false)
    wire((1.26, 0), (1.60, 0)); gbox((1.60, 0), [`l`], flip: true, fill: TINT)
    wire((2.52, 0), (2.86, 0))
    lab(-0.35, 0, black)[$A$]; lab(1.43, 0.66, black)[$A + B$]; lab(3.21, 0, black)[$A$]
    lab(4.00, 0, black)[$=$]
    lab(4.55, 0, black)[$A$]; wire((4.90, 0), (6.30, 0)); lab(6.65, 0, black)[$A$]
  }), s: 85%),

  [`lr°=⊥=rl°`],
  P(cetz.canvas(length: 0.8cm, {
    wire((0, 0), (0.34, 0)); gbox((0.34, 0), [`l`], chamfer: false)
    wire((1.26, 0), (1.60, 0)); gbox((1.60, 0), [`r`], flip: true, fill: TINT)
    wire((2.52, 0), (2.86, 0))
    lab(-0.35, 0, black)[$A$]; lab(1.43, 0.66, black)[$A + B$]; lab(3.21, 0, black)[$B$]
    lab(4.00, 0, black)[$=$]
    lab(4.55, 0, black)[$A$]; blocked((4.90, 0), (6.30, 0)); lab(6.65, 0, black)[$B$]
  }), s: 85%),

  [`l°l∪r°r=𝟙`],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62
    wire((0, 0), (0.34, 0))
    tape((0.34, -1.57), (4.24, 1.57))
    tape-fork((0.56, 0), sp: y, len: 0.42)
    gbox((0.98, y), [`l`], flip: true, fill: TINT); wire((1.90, y), (2.24, y))
    gbox((2.24, y), [`l`], chamfer: false); wire((3.16, y), (3.60, y))
    gbox((0.98, -y), [`r`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y))
    gbox((2.24, -y), [`r`], chamfer: false); wire((3.16, -y), (3.60, -y))
    lab(2.07, 1.24, black)[$A$]; lab(2.07, 0, black)[$B$]
    tape-join((4.02, 0), sp: y, len: 0.42)
    wire((4.24, 0), (4.58, 0))
    lab(-1.05, 0, black)[$A + B$]; lab(5.60, 0, black)[$A + B$]
    lab(6.90, 0, black)[$=$]
    lab(7.85, 0, black)[$A + B$]; wire((8.55, 0), (9.95, 0)); lab(10.75, 0, black)[$A + B$]
  }), s: 85%),

  [`[U,V]°[R,S]=U°R∪V°S`], [],
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
]<coprod-calc>

// The book's figure turned a quarter turn, source at the left like every other picture here.  `R` and
// `S` arc outside because their straight lines would run over `E C`; blue dashed is the induced arrow.
#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (AB, PC, C) = ((-6.4, 0), (0.4, 0), (4.6, 0))
  let (A, B) = ((-3.4, 2.4), (-3.4, -2.4))
  ar(A, AB, black, s0: 0.5, s1: 0.9)
  ar(B, AB, black, s0: 0.5, s1: 0.9)
  ar(AB, PC, INDUCED, dash: "dashed", s0: 0.9, s1: 0.6)
  ar(PC, C, black, s0: 0.6, s1: 0.5)
  ar(A, PC, GIVEN1, s0: 0.5, s1: 0.6)
  ar(B, PC, GIVEN2, s0: 0.5, s1: 0.6)
  arc(A, C, 1, [`R`], col: GIVEN1, h: 4.0, cx: 3)
  arc(B, C, -1, [`S`], col: GIVEN2, h: 4.0, cx: 3)
  lab(-5.18, 1.55, black)[`l`]; lab(-5.18, -1.55, black)[`r`]
  lab(-1.23, 1.62, GIVEN1)[$frac(#[`R`], ∋)$]; lab(-1.23, -1.62, GIVEN2)[$frac(#[`S`], ∋)$]
  lab(-3.0, 0.5, INDUCED)[`[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]`]
  lab(2.5, 0.45, black)[`∋`]
  node(A.at(0), A.at(1), GIVEN1, $A$); node(B.at(0), B.at(1), GIVEN2, $B$)
  node(AB.at(0), AB.at(1), black, $A + B$)
  node(PC.at(0), PC.at(1), INDUCED, $E C$)
  node(C.at(0), C.at(1), black, $C$)
}))]<coprod-square>

Nothing here holds only up to `⊑`: every triangle commutes on the nose, which is the difference from
the fork above. The border spells `[R,S]=[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]∋`, and pushing `∋` into the union that
`[·,·]` on maps already is turns that back into the definition,
`(l°` $frac(#[`R`], ∋)$ `∪r°` $frac(#[`S`], ∋)$`)∋=l°R∪r°S`.

// B&dM §5.3, pp. 117–119, mirrored like the product table.  A TAPE WHEREVER THERE IS A `∪`, so (5.9)
// and (5.10) are definitions drawn rather than equations: the tape IS the union on the right.
#disp[#table(
  columns: (1.9cm, 5.4cm, 1fr),
  align: (left + horizon, left + horizon, center + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*B&dM*], [*the law*], [*picture*]),

  [(5.9)], [`[R,S]=(l°R)∪(r°S)` \ #src[@coprod-laws's first row]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62
    lab(-0.9, 0, black)[$A + B$]
    wire((-0.3, 0), (0.34, 0))
    tape((0.34, -1.05), (4.24, 1.05))
    tape-fork((0.56, 0), sp: y, len: 0.42)
    gbox((0.98, y), [`l`], flip: true, fill: TINT); wire((1.90, y), (2.24, y))
    gbox((2.24, y), [R]); wire((3.16, y), (3.60, y))
    gbox((0.98, -y), [`r`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y))
    gbox((2.24, -y), [S]); wire((3.16, -y), (3.60, -y))
    tape-join((4.02, 0), sp: y, len: 0.42)
    wire((4.24, 0), (4.58, 0))
    lab(4.93, 0, black)[$C$]
  }), s: 82%),

  [(5.10)], [`R+S=[Rl,Sr]`],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62
    lab(-0.9, 0, black)[$A + B$]
    wire((-0.3, 0), (0.34, 0))
    tape((0.34, -1.05), (5.16, 1.05))
    tape-fork((0.56, 0), sp: y, len: 0.42)
    gbox((0.98, y), [`l`], flip: true, fill: TINT); wire((1.90, y), (2.24, y))
    gbox((2.24, y), [R]); wire((3.16, y), (3.50, y))
    gbox((3.50, y), [`l`], chamfer: false); wire((4.42, y), (4.52, y))
    gbox((0.98, -y), [`r`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y))
    gbox((2.24, -y), [S]); wire((3.16, -y), (3.50, -y))
    gbox((3.50, -y), [`r`], chamfer: false); wire((4.42, -y), (4.52, -y))
    tape-join((4.94, 0), sp: y, len: 0.42)
    wire((5.16, 0), (5.50, 0))
    lab(6.25, 0, black)[$C + D$]
  }), s: 82%),

  [(5.11)], [`[U,V]°[R,S]=(U°R)∪(V°S)` \ #src[@coprod-laws's last row;
 ]],
   // lean:AOP.A5_3.junc_recip_junc@838f4abc
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62
    lab(-0.3, 0, black)[$C$]
    wire((0, 0), (0.34, 0))
    tape((0.34, -1.05), (3.90, 1.05))
    tape-fork((0.56, 0), sp: y, len: 0.42)
    gbox((0.98, y), [U], flip: true, fill: TINT); wire((1.90, y), (2.24, y))
    gbox((2.24, y), [`l`], chamfer: false); wire((3.16, y), (3.26, y))
    gbox((0.98, -y), [V], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y))
    gbox((2.24, -y), [`r`], chamfer: false); wire((3.16, -y), (3.26, -y))
    tape-join((3.68, 0), sp: y, len: 0.42)
    wire((3.90, 0), (5.20, 0)); lab(4.55, 0.42, black)[$A + B$]
    tape((5.20, -1.05), (8.76, 1.05))
    tape-fork((5.42, 0), sp: y, len: 0.42)
    gbox((5.84, y), [`l`], flip: true, fill: TINT); wire((6.76, y), (7.10, y))
    gbox((7.10, y), [R]); wire((8.02, y), (8.12, y))
    gbox((5.84, -y), [`r`], flip: true, fill: TINT); wire((6.76, -y), (7.10, -y))
    gbox((7.10, -y), [S]); wire((8.02, -y), (8.12, -y))
    tape-join((8.54, 0), sp: y, len: 0.42)
    wire((8.76, 0), (9.10, 0)); lab(9.45, 0, black)[$D$]
    // `ll°=𝟙` and `lr°=⊥` (@coprod-laws): the two cross branches are cut, the two straight ones fuse.
    lab(10.1, 0, black)[$=$]
    lab(10.75, 0, black)[$C$]
    wire((11.05, 0), (11.39, 0))
    tape((11.39, -1.05), (14.95, 1.05))
    tape-fork((11.61, 0), sp: y, len: 0.42)
    gbox((12.03, y), [U], flip: true, fill: TINT); wire((12.95, y), (13.29, y))
    gbox((13.29, y), [R]); wire((14.21, y), (14.31, y))
    gbox((12.03, -y), [V], flip: true, fill: TINT); wire((12.95, -y), (13.29, -y))
    gbox((13.29, -y), [S]); wire((14.21, -y), (14.31, -y))
    tape-join((14.73, 0), sp: y, len: 0.42)
    wire((14.95, 0), (15.29, 0)); lab(15.64, 0, black)[$D$]
  }), s: 68%),

  [Ex 5.12], [`X≜[𝟙,⊥]=l°` and `Y≜[⊥,𝟙]=r°`, \ so `(Xl)∪(Yr)=[l,r]=𝟙` \ #src[which is (5.9)]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62
    lab(-1.0, 0, black)[$A + B$]
    wire((-0.3, 0), (0.34, 0))
    tape((0.34, -1.05), (4.24, 1.05))
    tape-fork((0.56, 0), sp: y, len: 0.42)
    gbox((0.98, y), [`l`], flip: true, fill: TINT); wire((1.90, y), (2.24, y))
    gbox((2.24, y), [`l`], chamfer: false); wire((3.16, y), (3.60, y))
    gbox((0.98, -y), [`r`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y))
    gbox((2.24, -y), [`r`], chamfer: false); wire((3.16, -y), (3.60, -y))
    tape-join((4.02, 0), sp: y, len: 0.42)
    wire((4.24, 0), (4.58, 0))
    lab(5.30, 0, black)[$A + B$]
    lab(6.40, 0, black)[$=$]
    lab(7.40, 0, black)[$A + B$]; wire((8.10, 0), (9.30, 0)); lab(10.0, 0, black)[$A + B$]
  }), s: 78%),

  [Ex 5.13], [#src[prove (5.11), and say why duality does not carry it over from the product law]],
  [],

  [Ex 5.14], [`(R+S)∩([P,Q][U,V]°)` \ `=(R∩(PU°))+(S∩(QV°))` \ #src[`[P,Q][U,V]°` is a full 2×2 of
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
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
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
  [In `Rel`, `xs P(f) ys⟺ys={f a|a∈xs}`. The half at `f°` says every `a∈xs` has its `f a` on
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

#disp[#definition[
An *F-algebra* on `A` is a map `α`#sub[`A`]` : FA⟶A`.
An *F-homomorphism* from `α`#sub[`A`] to `α`#sub[`B`] is a map `h : A⟶B` with
`α`#sub[`A`]` h=F(h)α`#sub[`B`].
The *initial algebra* `α`#sub[`T`]` : FT⟶T` is the F-algebra with exactly one F-homomorphism
`⦇α`#sub[`A`]`⦈ : T⟶A` to every F-algebra `α`#sub[`A`]
#src[].
// lean:AOP.A5_5.InitialAlgebra@a45a8436

  #row((box(inset: (right: 18pt), cetz.canvas(length: 0.8cm, {
    let (FA, A, FB, B) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
    ar(FA, A, GIVEN2, s0: 0.55, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.55, s1: 0.55)
    ar(FA, FB, black, s0: 0.55, s1: 0.55); ar(A, B, black, s0: 0.55, s1: 0.55)
    lab(0, 1.9, GIVEN2)[`α`#sub[`A`]]; lab(0, -1.9, GIVEN1)[`α`#sub[`B`]]
    lab(-3.55, 0, black)[`F(h)`]; lab(3.2, 0, black)[`h`]
    node(FA.at(0), FA.at(1), black, `FA`); node(A.at(0), A.at(1), black, `A`)
    node(FB.at(0), FB.at(1), GIVEN1, `FB`); node(B.at(0), B.at(1), GIVEN1, `B`)
  })), cetz.canvas(length: 0.8cm, {
    let (FT, T, FA, A) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FA, A, GIVEN1, s0: 0.55, s1: 0.55)
    ar(FT, FA, INDUCED, s0: 0.55, s1: 0.55)
    ar(T, A, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
    lab(0, 1.9, GIVEN2)[`α`#sub[`T`]]; lab(0, -1.9, GIVEN1)[`α`#sub[`A`]]
    lab(-4.25, 0, INDUCED)[`F(⦇α`#sub[`A`]`⦈)`]; lab(3.7, 0, INDUCED)[`⦇α`#sub[`A`]`⦈`]
    node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
    node(FA.at(0), FA.at(1), GIVEN1, `FA`); node(A.at(0), A.at(1), GIVEN1, `A`)
  })), s: 100%)
]]<initial-defn>

=== Reflection

// The defining square at `X := 𝟙`, `α_B := α_T`, on @cata-defining's own geometry: both rows are the ONE
// arrow `α_T`, so both are GIVEN2.  The right panel is bare — `𝟙` is an empty wire, and that is the law.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FT, T, FT2, T2) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FT2, T2, GIVEN2, s0: 0.55, s1: 0.55)
    ar(FT, FT2, INDUCED, s0: 0.55, s1: 0.55)
    ar(T, T2, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
    lab(0, 1.9, GIVEN2)[`α`#sub[`T`]]; lab(0, -1.9, GIVEN2)[`α`#sub[`T`]]
    lab(-4.0, 0, INDUCED)[`F(𝟙)`]; lab(3.4, 0, INDUCED)[`𝟙`]
    node(FT.at(0), FT.at(1), black, `FT`); node(FT2.at(0), FT2.at(1), black, `FT`)
    node(T.at(0), T.at(1), black, `T`); node(T2.at(0), T2.at(1), black, `T`)
  }),
  homeq(`F`, `T`, [`α`#sub[`T`]], none, [`α`#sub[`T`]], `T`,
    typed: true, bcol: TCOL, regions: auto, ctop: GIVEN2, cmid: INDUCED, cbot: GIVEN2),
 [`⦇α`#sub[`T`]`⦈=𝟙` #h(6pt) #src[(2.11)]],
  // lean:AOP.A6_3.relCata_alpha@656cd4b8
)]<cata-reflection>

// `relCata_alpha`, AOP/A6_3.lean:40.
Taking a value apart with `α`#sub[`T`] and putting it straight back is doing nothing.

=== Fusion

// `T` is already the initial algebra's carrier, so the second algebra's is `C`.  `R` is `α_B` and `Q`
// is `α_C`; `S` keeps its letter, being the homomorphism, not an algebra — a subscript would miscast it.
Fusion rewrites `⦇α`#sub[`B`]`⦈S` through a second algebra `α`#sub[`C`]` : FC⟶C` along an arrow
`S : B⟶C`.

// `tcol`/`bcol` spelled out because the side condition's object wire runs `B` then `C` where the
// defaults run `T`, `B` — one object, one hue.  `s: 92%`: the one row that does not fit at full size.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FT, T) = ((-2.6, 2.5), (2.6, 2.5))
    let (FB, B) = ((-2.6, 0), (2.6, 0))
    let (FC, C) = ((-2.6, -2.5), (2.6, -2.5))
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.55, s1: 0.55)
    ar(FC, C, GIVEN1, s0: 0.55, s1: 0.55)
    ar(FT, FB, INDUCED, s0: 0.55, s1: 0.55)
    ar(FB, FC, black, s0: 0.55, s1: 0.55)
    ar(T, B, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
    ar(B, C, black, s0: 0.55, s1: 0.55)
    lab(-4.25, 1.25, INDUCED)[`F(⦇α`#sub[`B`]`⦈)`]; lab(3.7, 1.25, INDUCED)[`⦇α`#sub[`B`]`⦈`]
    lab(-3.55, -1.25, black)[`F(S)`]; lab(3.1, -1.25, black)[`S`]
    lab(0, 3.05, GIVEN2)[`α`#sub[`T`]]; lab(0, 0.55, GIVEN1)[`α`#sub[`B`]]; lab(0, -1.95, GIVEN1)[`α`#sub[`C`]]
    node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
    node(FB.at(0), FB.at(1), GIVEN1, `FB`); node(B.at(0), B.at(1), GIVEN1, `B`)
    node(FC.at(0), FC.at(1), GIVEN1, `FC`); node(C.at(0), C.at(1), GIVEN1, `C`)
  }),
  grid(
    columns: 2, align: horizon, column-gutter: 16pt, row-gutter: 10pt,
    src[the side condition],
    homeq(`F`, `B`, [`α`#sub[`B`]], `S`, [`α`#sub[`C`]], `C`, ctop: GIVEN1, cmid: black, cbot: GIVEN1,
      typed: true, tcol: BCOL, bcol: CCOL, regions: auto),
    src[the conclusion],
    twobeadeq(`T`, [`⦇α`#sub[`B`]`⦈`], `S`, [`⦇α`#sub[`C`]`⦈`], `C`, c1: INDUCED, c2: black, c3: INDUCED,
      typed: true, regions: auto),
  ),
  [`⦇α`#sub[`B`]`⦈S=⦇α`#sub[`C`]`⦈⟸α`#sub[`B`]` S=F(S)α`#sub[`C`] #h(6pt)
 #src[(2.12)]],
   // lean:AOP.A5_5.relCata_fusion@15d8a5b5
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
   // lean:AOP.A5_5_TypeFunctor.alpha_natural@bf347627

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

// The house orientation: the fold runs down the columns, over the FLAT algebra `F(f,𝟙)α_B`, which the
// triangle hanging below splits into its two steps.
// The `F` wire is UNINDEXED, against Hinze-Marsden's own practice of partially applying a bifunctor:
// its bead `F(f,𝟙)` and the object bead `f` are one arrow, `F(f,T(f))` — the square carries both steps.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
  let (FA, TA) = ((-3, 2.5), (3, 2.5))
  let (FM, TB) = ((-3, 0), (3, 0))
  let FB = (-3, -2.5)
  ar(FA, TA, GIVEN2, s0: 1.45, s1: 0.65); ar(FM, TB, GIVEN1, s0: 1.45, s1: 0.55)
  ar(FA, FM, INDUCED, s0: 0.55, s1: 0.55)
  ar(FM, FB, black, s0: 0.55, s1: 0.55)
  ar(TA, TB, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  ar(FB, TB, GIVEN1, s0: 1.45, s1: 0.85)
  lab(0.4, 3.05, GIVEN2)[`α`#sub[`A`]]; lab(0.4, 0.6, GIVEN1)[`F(f,𝟙)α`#sub[`B`]]
  lab(-4.75, 1.25, INDUCED)[`F(𝟙,T(f))`]; lab(-4.25, -1.25, black)[`F(f,𝟙)`]
  lab(4.0, 1.25, INDUCED)[`T(f)`]; lab(0.7, -1.8, GIVEN1)[`α`#sub[`B`]]
  node(FA.at(0), FA.at(1), black, `F(A,TA)`); node(TA.at(0), TA.at(1), black, `TA`)
  node(FM.at(0), FM.at(1), black, `F(A,TB)`)
  node(FB.at(0), FB.at(1), GIVEN1, `F(B,TB)`); node(TB.at(0), TB.at(1), GIVEN1, `TB`)
  }),
  tfuneq([`F`], [`T`], [`A`], [`B`], [`α`#sub[`A`]], [`α`#sub[`B`]], [`f`],
    cact1: GIVEN2, cact2: GIVEN1, regions: auto),
  [`α`#sub[`A`]` T(f)=F(f,T(f))α`#sub[`B`] #h(6pt)
 #src[]],
   // lean:AOP.A5_5_TypeFunctor.alpha_natural@bf347627
)]<tfun-sq>

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
  lab(-5.15, 0, INDUCED)[`F(𝟙,T(f)⦇h⦈)`]; lab(1.25, 0, INDUCED)[`⦇F(f,𝟙)h⦈`]
  lab(4.67, 1.47, INDUCED)[`T(f)`]; lab(4.67, -1.47, INDUCED)[`⦇h⦈`]
  node(FA.at(0), FA.at(1), black, `F(A,TA)`); node(TA.at(0), TA.at(1), black, `TA`)
  node(TB.at(0), TB.at(1), black, `TB`)
  node(FC.at(0), FC.at(1), GIVEN1, `F(A,C)`); node(C.at(0), C.at(1), GIVEN1, `C`)
  }),
  twobeadeq(`TA`, [`T(f)`], [`⦇h⦈`], [`⦇F(f,𝟙)h⦈`], `C`, c1: INDUCED, c2: INDUCED, c3: INDUCED,
    typed: true, regions: auto),
  [`T(f)⦇h⦈=⦇F(f,𝟙)h⦈` #h(6pt)
 #src[]],
   // lean:AOP.A5_5_TypeFunctor.typeMap_fusion@7d2c6178
)]<tfun-fusion>

// Its own page: otherwise the heading lands as the last line under the power relator's table, an orphan
// a page away from the definition it names, and the defining square below straddles the break.
#pagebreak(weak: true)
// B&dM and Freyd call this a catamorphism; the note says reduce, after q's `/`.
== Reduce <sec-cata>

#disp[#definition[
let `F` be a relator and has  *initial algebra* `α`#sub[T]` : FT⟶T` in the subcategory of functions. 
α#sub[T] is also initial in the allegory:
]]<cata-defn>


=== The defining equation

// `α` subscripted by its CARRIER through this section, `#sub` OUTSIDE the raw span (inside backticks `_` is
// literal).  A WIRE'S COLOUR IS ITS TYPE, A BEAD'S COLOUR IS WHICH ARROW IT IS, so arrows carry over.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    // The same 5.2 × 2.7 square as @cata-map-square's top row, so the two pictures overlay.
    let (FT, T, FA, A) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FA, A, GIVEN1, s0: 0.55, s1: 0.55)
    ar(FT, FA, INDUCED, s0: 0.55, s1: 0.55)
    ar(T, A, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
    lab(0, 1.9, GIVEN2)[`α`#sub[`T`]]; lab(0, -1.9, GIVEN1)[`α`#sub[`A`]]
    lab(-4.0, 0, INDUCED)[`F(X)`]; lab(3.6, 0, INDUCED)[`X`]
    node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
    node(FA.at(0), FA.at(1), GIVEN1, `FA`); node(A.at(0), A.at(1), GIVEN1, `A`)
  }),
  homeq(`F`, `T`, [`α`#sub[`T`]], [`⦇α`#sub[`A`]`⦈`], [`α`#sub[`A`]], `A`,
    typed: true, regions: (`𝒜`, `𝟏`), ctop: GIVEN2, cmid: INDUCED, cbot: GIVEN1),
  [`X=⦇α`#sub[`A`]`⦈⟺α`#sub[`T`]` X=F(X)α`#sub[`A`] #h(6pt)
 #src[]],
   // lean:AOP.A5_5.relCata_UP@e4a4905f
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
    table.cell(colspan: 3, align: center, text(12.5pt)[`⦇[c,f]⦈=reduce(c,f)`]),
    [*part*], [*`Nat`*], [*`[A]`*],
  ),

  [datatype],
  [`Nat::=zero|succ Nat`],
  [`[A]::=nil|cons (A,[A])`],

  [base functor `F`],
  [`F(X)=1+X`],
 [`F(X)=1+A×X` #src[]],
  // lean:AOP.A6_ConsList.F_eq_sum_prod@cab297e7

  [initial algebra `α`],
  [`α=[zero,succ]` \ `: 1+Nat⟶Nat`],
 [`α=[nil,cons]` \ `: 1+A×[A]⟶[A]` #src[]],
  // lean:AOP.A6_ConsList.initial@79b3402c

  [the fold, pointwise],
  [`⦇[c,f]⦈ zero=c` \ `⦇[c,f]⦈ (succ n)=f (⦇[c,f]⦈n)`],
  [`⦇[c,f]⦈ nil=c` \ `⦇[c,f]⦈ (cons (a,x))=f (a,⦇[c,f]⦈ x)`],
)]<cata-initial>


=== `⦇R⦈=⦇`$frac(#[`F(∋)R`], ∋)$`⦈∋`

// B&dM p.121's figure, mirrored: @cata-defining's square at `α`#sub[`A`]` := (F(∋) R)%∋`, `A := E A`,
// over the ∋/F(∋) rows and the relation `R` — the renamed arrows are the two induced ones and the bottom row.
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
    lab(0, 2.05, GIVEN2)[`α`#sub[`T`]]
    lab(-4.6, 0.15, INDUCED)[`F(⦇`$frac(#[`F(∋)R`], ∋)$`⦈)`]
    lab(4.2, 0.15, INDUCED)[`⦇`$frac(#[`F(∋)R`], ∋)$`⦈`]
    lab(0, -0.65, GIVEN1)[`α`#sub[`EA`]]
    lab(0, -1.95, GIVEN1)[$frac(#[`F(∋)R`], ∋)$]
    lab(-4.0, -2.55, black)[`F(∋)`]; lab(3.6, -2.55, black)[`∋`]
    lab(0, -3.35, black)[`α`#sub[`A`]]
    lab(0, -4.45, black)[`R`]
    node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
    node(FE.at(0), FE.at(1), GIVEN1, `F(EA)`); node(E.at(0), E.at(1), GIVEN1, `EA`)
    node(FA.at(0), FA.at(1), GIVEN1, `FA`); node(A.at(0), A.at(1), GIVEN1, `A`)
  }),
  src[$frac(#[`𝟙`], ∋)$ is the inverse of `∋`]),
  homeq(`F`, `T`, [`α`#sub[`T`]], [`⦇`$frac(#[`F(∋)R`], ∋)$`⦈`], [`α`#sub[`EA`]], `EA`,
    typed: true, regions: auto, ctop: GIVEN2, cmid: INDUCED, cbot: GIVEN1, gap: 5.2,
    outsplit: (`E`, `A`)),
  [`α`#sub[`T`]` ⦇`$frac(#[`F(∋)R`], ∋)$`⦈=F(⦇`$frac(#[`F(∋)R`], ∋)$`⦈)` $frac(#[`F(∋)R`], ∋)$
 #src[]],
   // lean:AOP.A5_5.Λ_relCata@5b63ea5d lean:AOP.A5_5.relCata_unfold@22ba1c5c
)]<cata-map-square>

// B&dM (5.12), p. 121, mirrored into this note's diagram order.  A row too wide for the column wraps,
// and the next row opens with the `⟺` that carries it over.
#disp[
#zline(
  zsqc([`α`#sub[`T`]` X`], [`F(X)R`], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc([$frac(#[`α`#sub[`T`]` X`], ∋)$], [$frac(#[`F(X)R`], ∋)$], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc([$frac(#[`α`#sub[`T`]` X`], ∋)$], [$frac(#[`F(`$frac(#[`X`], ∋)$ `∋)R`], ∋)$], eq: true),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[relator, fusion twice],
  zsqc([`α`#sub[`T`] $frac(#[`X`], ∋)$], [`F(`$frac(#[`X`], ∋)$`)` $frac(#[`F(∋)R`], ∋)$], eq: true),
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
#let EQ = text(luma(140))[$=$]
#let IFF = text(SLACK)[$arrow.l.r.double$]
#let IMP = text(SLACK)[$arrow.l.double$]

// The op lane is one glyph wide: `⊑`, `⊒` and `=` all measure 8.95pt here.  `layout` gives the
// CELL's width, so a row that cannot fit picture and formula side by side stacks them itself.
// PICTURE FIRST on a shared left edge (a table rebinds `pw` to its widest drawing); the formula is
// flush RIGHT in both branches, so it lands on one edge whether the row fits side by side or stacks.
#let OPW = 10pt
#let step(op, pic, f, pw: none) = layout(sz => {
  let gut = 6pt
  // `box`: `P` centres its drawing in whatever width it gets, which would undo the shared left edge.
  let p = box(pic)
  let lane = if pw == none { measure(p).width } else { pw }
  let row = if measure(f).width + lane + gut <= sz.width - OPW - gut {
    grid(columns: (OPW, lane, 1fr), align: (left + horizon, left + horizon, right + horizon),
      column-gutter: gut, op, p, f)
  } else {
    grid(columns: (OPW, 1fr), align: (left + horizon, left + horizon), column-gutter: gut,
      op, stack(spacing: 5pt, p, align(right, f)))
  }
  pic-meta(plain(f), row, width: sz.width)
  row
})
#let mbp(body) = P(cetz.canvas(length: 0.8cm, body), s: 72%)

#let frc(n) = $frac(#n, ∋)$
#let TH = 1.2   // a fraction box is two lines tall

// A row is TALLER than it is wide once the second column is a picture too, so the circuit and its
// formula stack on one left edge — which `step`'s side-by-side branch cannot give.
#let vstep(op, pic, f) = layout(sz => {
  let row = grid(columns: (OPW, 1fr), align: (left + horizon, left + horizon),
    column-gutter: 6pt, op, stack(spacing: 5pt, box(pic), f))
  pic-meta(plain(f), row, width: sz.width)
  row
})

// A panel's address is the display it stands in and its place in that display, both read off the
// counters at the point it is PLACED, so a reordered row cannot keep a stale name.
#let hm-meta(rec) = {
  counter("hm-panel").step()
  context metadata((kind: "scanline",
    id: plain(dispnum(counter(heading).get(),
      counter(figure.where(kind: "disp")).get().first()))
      + "." + str(counter("hm-panel").get().first()),
    ..rec))
}

// The panel every Hinze–Marsden column in this note draws — §@sec-hylo's, §13.3.1's, `tw-hm`,
// `party-hm`, §13.4.4's two.  A wire is a FUNCTOR, a bead an arrow, a region a category: `Rel` left
// of the object wire, `𝟏` right of it.
#let DKN = 0.45                                   // the handle's knee
// IntroString.pdf (2.5), p. 46: an arrow of a composite is a bead on the OBJECT line, which runs
// STRAIGHT through it; the functor wires that composite is made of bend in to the bead and out again.
// `k` is how far above and below the node the lane leaves its column: a panel stacking four lanes in
// one column detours more shallowly than a two-wire one — still a slope, never a horizontal tangent.
#let NKN = 0.45
#let nodepts(x, xo, ys, k: NKN) = {
  let pts = ()
  for y in ys { pts += ((x, y + k), (xo, y), (x, y - k)) }
  pts
}
#let lwire(x, xo, ys, ytop, ybot, k: NKN) = hm-wire(
  ((x, ytop),) + nodepts(x, xo, ys, k: k) + ((x, ybot),))
// `s` scales the LABELS with the geometry, so a panel that must lose height lowers `length:`, never
// `s`; `tpan`/`mpan` pass 100% and print their labels at the size `tw-hm` does.
// `opath` slopes the object wire: a polyline top to bottom, kinked at bead heights, hugging the
// lanes already born.  Fills and wire are built from the SAME pts, so the region edge IS the wire.
#let dpan(h, w, xa, body, s: 74%, opath: none, key: none) = P(cetz.canvas(length: 0.8cm, {
  let op = if opath == none { ((xa, h), (xa, 0)) } else { opath }
  hm-region(((0, 0), (0, h)) + op, fb-ALLC)
  hm-region(op + ((w, 0), (w, h)), luma(226))
  hm-wire(op, col: BCOL)
  body
}), s: s, key: key)

// A lane runs from where its functor is BORN to where it DIES: `"top"`/`"bot"` for a panel edge, a
// bead's height otherwise, and `un` is a birth carrying a bead of its own (the singleton).  The knee
// GROWS WITH THE RUN, so a wire crossing four lanes and one crossing none meet the object at one angle.
// CLAMPED to the drop the lane has: a knee taller than the run puts the turn above the panel's top
// edge, where the wire strikes through the port labels.
#let dknee(x, xo, drop) = calc.min(0.45 + 0.25 * calc.abs(xo - x), 0.55 * drop)
// `xat` is the object wire's x at a height (constant `xo` unless `opath` slopes it); `kb`/`kd` are
// knees shared by every arm into one bead — equal knees keep the arms' x order, so they nest.
#let dlane(xat, h, x, y0, y1, nm, un, kb: none, kd: none, col: none) = {
  let wc = if col == none { (:) } else { (col: col) }
  let top = if y0 == "top" { h } else { y0 }
  let bot = if y1 == "bot" { 0 } else { y1 }
  let pts = if y0 == "top" { ((x, h),) } else if un != none { ((x, y0),) } else {
    let k = if kb == none { dknee(x, xat(y0), top - bot) } else { kb }
    ((xat(y0), y0), (x, y0 - k))
  }
  pts += if y1 == "bot" { ((x, 0),) } else {
    let k = if kd == none { dknee(x, xat(y1), top - bot) } else { kd }
    ((x, y1 + k), (xat(y1), y1))
  }
  hm-wire(pts, ..wc)
  if un != none { hm-bead((x, y0), un) }
}
// The bead is a POINT and every arm into one is a bend (IntroString.pdf p. 40, whose spider takes six
// of them), so a wire the bead does not consume dips to the dot at each `ybs` and comes back out.
#let ddip(xat, h, x, y0, y1, ybs, nm, kb: none, kd: none, col: none) = {
  let wc = if col == none { (:) } else { (col: col) }
  let (t, b) = (if y0 == "top" { h } else { y0 }, if y1 == "bot" { 0 } else { y1 })
  // The lane change keeps `dlane`'s own knee, so the wire reaches its lane exactly where it did
  // before and crosses nothing new; the dip is a separate, smaller excursion below that corner.
  let keb = calc.min(if kb == none { dknee(x, xat(t), t - b) } else { kb },
    0.60 * (t - ybs.first()))
  let ked = calc.min(if kd == none { dknee(x, xat(b), t - b) } else { kd },
    0.60 * (t - ybs.first()))
  let pts = if y0 == "top" { ((x, h),) } else { ((xat(t), t), (x, t - keb)) }
  for (i, yb) in ybs.enumerate() {
    // A dip may share its run with the next dip down, and then each gets under half of it.
    let (hi, up) = if i == 0 { (t - keb, 0.85) } else { (ybs.at(i - 1), 0.42) }
    let (lo, dn) = if i == ybs.len() - 1 { (if y1 == "bot" { b } else { b + ked }, 0.85) }
      else { (ybs.at(i + 1), 0.42) }
    let kdip = calc.min(0.30 * (xat(yb) - x), up * (hi - yb), dn * (yb - lo))
    pts += ((x, yb + kdip), (xat(yb), yb), (x, yb - kdip))
  }
  hm-wire(pts + (if y1 == "bot" { ((x, 0),) } else { ((x, b + ked), (xat(b), b)) }), ..wc)
}

// A bead's 4th element is how far left it reaches, and the reach is ink the crossed WIRES make by
// bending onto the dot (`ddip`) — never a line drawn past them, which would cross without meeting.
#let dpanel(h, w, xo, lanes, beads, top, bot, names: false, s: 74%, opath: none, cert: (:)) = {
  let xat = if opath == none { y => xo } else { y => {
    let r = xo
    for i in range(opath.len() - 1) {
      let (a, b) = (opath.at(i), opath.at(i + 1))
      if y <= a.at(1) + 0.001 and y >= b.at(1) - 0.001 {
        r = if a.at(1) - b.at(1) < 0.001 { b.at(0) } else {
          b.at(0) + (a.at(0) - b.at(0)) * (y - b.at(1)) / (a.at(1) - b.at(1)) }
      }
    }
    r
  } }
  // One knee per bead-and-side (sized by the group's longest run, clamped by its shortest drop):
  // arms converging on one dot with EQUAL knees keep their x order, so they nest, never braid.
  let gk = (:)
  if opath != none {
    let acc = (:)
    for l in lanes {
      let drop = ((if l.at(1) == "top" { h } else { l.at(1) })
        - (if l.at(2) == "bot" { 0 } else { l.at(2) }))
      if l.at(1) != "top" and l.at(4) == none {
        let key = "b" + str(l.at(1))
        acc.insert(key, acc.at(key, default: ()) + ((l.at(0), drop),))
      }
      if l.at(2) != "bot" {
        let key = "d" + str(l.at(2))
        acc.insert(key, acc.at(key, default: ()) + ((l.at(0), drop),))
      }
    }
    for (key, v) in acc {
      let y = float(key.slice(1))
      gk.insert(key, calc.min(
        0.45 + 0.25 * v.map(p => xat(y) - p.at(0)).fold(0, calc.max),
        0.55 * v.map(p => p.at(1)).fold(99, calc.min)))
    }
    // An arm's knee stays UNDER where every leg dipping to its bead lands on its lane (`ddip`'s
    // `t - keb`), else the arm cuts through that leg on its way in, off any column.
    for key in gk.keys().filter(k => k.first() == "d") {
      let y = float(key.slice(1))
      let land = lanes.filter(l => l.at(1) != "top" and l.at(4) == none and l.at(1) > y
          and (if l.at(2) == "bot" { 0 } else { l.at(2) }) < y
          and beads.any(bd => bd.at(3, default: none) != none and calc.abs(bd.at(0) - y) < 0.001
            and bd.at(3) <= l.at(0) and l.at(0) < xat(y)))
        .map(l => l.at(1) - calc.min(gk.at("b" + str(l.at(1)), default: 99), 0.60 * (l.at(1) - y)) - y)
      if land != () { gk.insert(key, calc.min(gk.at(key), 0.85 * land.fold(99, calc.min))) }
    }
  }
  dpan(h, w, xo, {
  for l in lanes {
    // EVERY live wire the bead spans dips onto it, not just the one its `x` names: the span reaches
    // across the lanes between, so a wire inside the span meets the bead rather than passing it.
    let ys = beads.filter(bd => bd.at(3, default: none) != none
      and bd.at(3) <= l.at(0) and l.at(0) < xat(bd.at(0))
      and (if l.at(1) == "top" { h } else { l.at(1) }) > bd.at(0)
      and (if l.at(2) == "bot" { 0 } else { l.at(2) }) < bd.at(0)).map(bd => bd.at(0))
    let kb = if l.at(1) == "top" or l.at(4) != none { none }
      else { gk.at("b" + str(l.at(1)), default: none) }
    let kd = if l.at(2) == "bot" { none } else { gk.at("d" + str(l.at(2)), default: none) }
    // The lane's functor name keys `FCOL`; it is never drawn, the colour names the wire (2026-09-01).
    let nm = if l.at(3) != none { l.at(3) } else {
      let q = (if l.at(1) == "top" { top } else { bot }).find(t => t.at(0) == l.at(0))
      if q == none { none } else { q.at(1) } }
    let col = if nm == none { none } else { FCOL.at(plain(nm), default: none) }
    if ys == () { dlane(xat, h, l.at(0), l.at(1), l.at(2), l.at(3), l.at(4), kb: kb, kd: kd, col: col) }
    else { ddip(xat, h, l.at(0), l.at(1), l.at(2), ys.sorted().rev(), l.at(3), kb: kb, kd: kd, col: col) }
  }
  for b in beads { hm-bead((xat(b.at(0)), b.at(0)), b.at(1), col: b.at(2, default: black)) }
  for (x, l) in top {
    hm-port((if x == xo { xat(h) } else { x }, h), l, col: if x == xo { BCOL } else { FCOL.at(plain(l), default: black) }) }
  for (x, l) in bot {
    hm-port((if x == xo { xat(0) } else { x }, 0), l, dir: -1, col: if x == xo { BCOL } else { FCOL.at(plain(l), default: black) }) }
  if names { hm-name((1.12, 0.35), [`Rel`]); hm-name((xo + 1.4, 0.35), [`𝟏`]) }
  }, s: s, opath: opath, key: cert.at("expect", default: "dpanel"))
  hm-meta((helper: "dpanel", h: h, w: w, xo: xo, cert: cert,
    lanes: lanes.map(l => l.map(plain)), beads: beads.map(b => b.map(plain)),
    top: top.map(p => p.map(plain)), bot: bot.map(p => p.map(plain)))
    + (if opath == none { (:) } else { (opath: opath) }))
}

// A relator wire OPENED by the arrow that applies it and CLOSED by the one that consumes it; `born`
// is an opener that CREATES the relator (`X⟶EX`), so the wire starts at that bead instead.
#let dhandle(xa, xe, y0, y1, l, born: none) = {
  if born == none { hm-wire(((xa, y0), (xe, y0 - DKN), (xe, y1 + DKN), (xa, y1))) } else {
    hm-wire(((xe, y0), (xe, y1 + DKN), (xa, y1)))
    hm-bead((xe, y0), born)
  }
  hm-name((xe - 0.32, (y0 + y1) / 2), l)
}

// The columns the wires stand in.  `F` is a relator, hence a WIRE; a reduce, an algebra and a
// transpose are arrows, hence BEADS on the object wire.  `F(X)` costs no notation: it is the `X`
// bead with the `F` wire running straight past it — that pass IS the relator's action.
#let TXF = 0.60                                   // the `F` wire
#let TXH = 1.20                                   // the `E` wire, inside `F`
#let TXO = 1.95                                   // the object wire
// §13.3.1's first right panel runs TWO `E` wires — 10.1a's unit and counit.  `𝟙%∋ : F(EA)⟶E(F(EA))`
// births its one around the WHOLE object, so that one is outermost and the other three slide right.
#let RXU = 0.55                                   // the `E` the unit opens, outside `F`
#let RXF = 1.65                                   // the `F` wire
#let RXC = 2.25                                   // the `E` the counit `∋` closes, inside `F`
#let RXO = 2.85                                   // the object wire
#let tpan(h, beads, hands: (), joins: (), top: (), bot: [`A`], names: false, w: 4.5, xo: TXO, cert: (:)) = {
  dpan(h, w, xo, {
  for hd in hands { dhandle(xo, hd.at(0), hd.at(1), hd.at(2), hd.at(3), born: hd.at(4, default: none)) }
  for (x, y, k) in joins { hm-join(x, h, xo, y, knee: k) }
  for (y, l) in beads { hm-bead((xo, y), l) }
  for (x, l) in top { hm-port((x, h), l, col: if x == xo { BCOL } else { black }) }
  hm-port((xo, 0), bot, dir: -1, col: BCOL)
  if names { hm-name((1.05, 0.30), [`Rel`]); hm-name((3.4, 0.30), [`𝟏`]) }
  }, s: 100%)
  // `bot` is the one label the drawing pairs with `xo` by hand; emitted as a port list, so every
  // panel's ports have one shape.
  hm-meta((helper: "tpan", h: h, w: w, xo: xo, cert: cert,
    beads: beads.map(b => b.map(plain)), hands: hands.map(hd => hd.map(plain)),
    joins: joins.map(j => j.map(plain)),
    top: top.map(p => p.map(plain)), bot: ((xo, plain(bot)),)))
}
// The right-hand side of a row: the single relation the chain is bounded by.  `w` is the label's
// room, so a long one — `⦇S⦈°\X` — cannot run out of the panel.
#let tpanR(h, y, l, w: 1.9, top: [`A`], bot: [`A`]) = dpan(h, w, 0.55, {
  hm-bead((0.55, y), l)
  hm-port((0.55, h), top, col: BCOL); hm-port((0.55, 0), bot, dir: -1, col: BCOL)
}, s: 100%)
#let trow(l, r) = align(center, grid(columns: 3, align: horizon, column-gutter: 6pt, l, SQ, r))

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

 [`φ(Y)⊑Y⟹(μX : φ(X))⊑Y` \ #src[Theorem 6.1]],
  // lean:AOP.A6_2.mu_le@9918bd39
  [to bound `(μX : φ(X))` above, exhibit one `Y` the body does not grow past — the half §@sec-hylo
   and every chapter after it uses],
 [`φ((μX : φ(X)))=(μX : φ(X))` \ #src[Theorem 6.1]],
  // lean:AOP.A6_2.mu_fixed@2d3d1a8a
  [*Knaster–Tarski*: the least solution of `φ(X)⊑X` already solves `φ(X)=X`, so the least prefix
   point and the least fixed point are one relation],
)]<mu-laws>

=== `⦇S⦈°⦇R⦈=(μX : S°F(X)R)` <sec-hylo>

// §@sec-hylo's boxes.  `R` and `S` are algebras of RELATIONS, so they and their reduces are
// chamfered; `α` and `α°` are maps — the initial algebra is invertible — so they are plain.
#let hb-So = ([`S°`], 0.85, true)
#let hb-R = ([`R`], 0.70, true)
#let hb-X = ([`X`], 0.70, true)
#let hb-al = ([`α`], 0.70, false)
#let hb-alo = ([`α°`], 0.85, false)
#let hb-cSo = ([`⦇S⦈°`], 1.55, true)
#let hb-cR = ([`⦇R⦈`], 1.30, true)
#let hb-W = ([`⦇S⦈°\X`], 2.30, true)
#let hb-FcSR = ([`F(⦇S⦈°⦇R⦈)`], 3.10, true)
#let hb-FcSo = ([`F(⦇S⦈°)`], 2.15, true)
#let hb-FcR = ([`F(⦇R⦈)`], 1.90, true)
#let hb-FX = ([`F(X)`], 1.30, true)
#let hb-FW = ([`F(⦇S⦈°\X)`], 2.90, true)
#let hb-mu = ([`(μX : S°F(X)R)`], 4.50, true)
// A run of boxes between its source and target objects, and with `rhs` the run it is below: `gterm`
// without the converse frame, which is the shape every row of both tables draws.
#let hterm(items, a0, a1, rhs: none) = {
  lab(-0.42, 0, black)[#a0]
  boxrun(0, 0, items)
  let xe = boxrun-w(items)
  if rhs == none { lab(xe + 0.42, 0, black)[#a1] } else {
    lab(xe + 0.95, 0, SLACK)[`⊑`]
    boxrun(xe + 1.5, 0, rhs)
    lab(xe + 1.5 + boxrun-w(rhs) + 0.42, 0, black)[#a1]
  }
}

// §@sec-hylo's panels, emitted by `./scripts/diagram --sigs … --src … --tgt … "<formula>"` plus
// `s: 100%`, the size their `tpanR` partners keep.  `sigs:` types the section's abstract letters.
#let hy-body = dpanel(5, 4.55, 1.7,
  ((0.55, 4, 1, [`F`], none),),
  ((4, [`S°`]), (3, [`⦇S⦈°`]), (2, [`⦇R⦈`]), (1, [`R`], black, 0.55)),
  ((1.7, [`B`]),),
  ((1.7, [`A`]),),
  cert: (expect: "S° F(⦇S⦈°⦇R⦈)R", src: "B", tgt: "A", sigs: ("R": "F(A)⟶A", "S": "F(B)⟶B", "⦇R⦈": "T⟶A", "⦇S⦈": "T⟶B")),
  names: true, s: 100%)
#let hy-split = dpanel(5, 4.55, 1.7,
  ((0.55, 4, 1, [`F`], none),),
  ((4, [`S°`]), (3, [`⦇S⦈°`]), (2, [`⦇R⦈`]), (1, [`R`], black, 0.55)),
  ((1.7, [`B`]),),
  ((1.7, [`A`]),),
  cert: (expect: "S° F(⦇S⦈°)F(⦇R⦈)R", src: "B", tgt: "A", sigs: ("R": "F(A)⟶A", "S": "F(B)⟶B", "⦇R⦈": "T⟶A", "⦇S⦈": "T⟶B")), s: 100%)
#let hy-alg = dpanel(5, 4.55, 1.7,
  ((0.55, 4, 2, [`F`], none),),
  ((4, [`S°`]), (3, [`⦇S⦈°`]), (2, [`α`], black, 0.55), (1, [`⦇R⦈`])),
  ((1.7, [`B`]),),
  ((1.7, [`A`]),),
  cert: (expect: "S° F(⦇S⦈°)α⦇R⦈", src: "B", tgt: "A", sigs: ("S": "F(B)⟶B", "⦇R⦈": "T⟶A", "⦇S⦈": "T⟶B")), s: 100%)
#let hy-lambek = dpanel(5, 4.55, 1.7,
  ((0.55, 3, 2, [`F`], none),),
  ((4, [`⦇S⦈°`]), (3, [`α°`]), (2, [`α`], black, 0.55), (1, [`⦇R⦈`])),
  ((1.7, [`B`]),),
  ((1.7, [`A`]),),
  cert: (expect: "⦇S⦈° α° α⦇R⦈", src: "B", tgt: "A", sigs: ("⦇R⦈": "T⟶A", "⦇S⦈": "T⟶B")), s: 100%)
#let hy-cata = dpanel(3, 3.4, 0.55,
  (),
  ((2, [`⦇S⦈°`]), (1, [`⦇R⦈`])),
  ((0.55, [`B`]),),
  ((0.55, [`A`]),),
  cert: (expect: "⦇S⦈°⦇R⦈", src: "B", tgt: "A", sigs: ("⦇R⦈": "T⟶A", "⦇S⦈": "T⟶B")), s: 100%)
#let hy-cataR = dpanel(2, 3.4, 0.55,
  (),
  ((1, [`⦇R⦈`]),),
  ((0.55, [`T`]),),
  ((0.55, [`A`]),),
  cert: (expect: "⦇R⦈", src: "T", tgt: "A", sigs: ("⦇R⦈": "T⟶A")), s: 100%)
#let hy-prefix = dpanel(4, 4.55, 1.7,
  ((0.55, 3, 1, [`F`], none),),
  ((3, [`S°`]), (2, [`X`]), (1, [`R`], black, 0.55)),
  ((1.7, [`B`]),),
  ((1.7, [`A`]),),
  cert: (expect: "S° F(X)R", src: "B", tgt: "A", sigs: ("R": "F(A)⟶A", "S": "F(B)⟶B", "X": "B⟶A")), s: 100%)

// B&dM p. 142, mirrored into diagram order.  The `F` wire is born at the leading converse and dies
// at the trailing algebra; every step shortens it, and by the last row it is gone.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`S°F(⦇S⦈°⦇R⦈)R=⦇S⦈°⦇R⦈` \
 #src[Theorem 6.2; `R : FA⟶A`, `S : FB⟶B`, `α : FT⟶T` initial]],
    // lean:AOP.A6_3.hylo_fixed@42010f9f
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], mbp(hterm((hb-So, hb-FcSR, hb-R), [`B`], [`A`])),
    [`S°F(⦇S⦈°⦇R⦈)R` \ #src[the body at `⦇S⦈°⦇R⦈`]])],
  [#hy-body],

  [#vstep(EQ, mbp(hterm((hb-So, hb-FcSo, hb-FcR, hb-R), [`B`], [`A`])),
    [`S°F(⦇S⦈°)F(⦇R⦈)R` \ #src[`F(RS)=F(R)F(S)` — @relator-defn]])],
  [#hy-split],

  [#vstep(EQ, mbp(hterm((hb-So, hb-FcSo, hb-al, hb-cR), [`B`], [`A`])),
    [`S°F(⦇S⦈°)α⦇R⦈` \ #src[@cata-defining at `R`: `F(⦇R⦈)R=α⦇R⦈`]])],
  [#hy-alg],

  [#vstep(EQ, mbp(hterm((hb-cSo, hb-alo, hb-al, hb-cR), [`B`], [`A`])),
    [`⦇S⦈°α°α⦇R⦈` \ #src[@cata-defining at `S` conversed: `⦇S⦈°α°=S°F(⦇S⦈)°`, and
     `F(⦇S⦈)°=F(⦇S⦈°)` — @relator-laws]])],
  [#hy-lambek],

  [#vstep(EQ, mbp(hterm((hb-cSo, hb-cR), [`B`], [`A`])),
 [`⦇S⦈°⦇R⦈` \ #src[`α°α=𝟙`, Lambek]])],
    // lean:AOP.A6_2.InitialAlgebra.recip_alpha_alpha@5a99c7f6
  [#hy-cata],
))]<hylo-fix>

// B&dM p. 143, mirrored.  Two adjunction steps carry `⦇S⦈°` out of the way and back, the reduce's
// own leastness fires between them, and the `F` wire's top end walks from `α°` up to `S°`.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
 Thm[`S°F(X)R⊑X⟹⦇S⦈°⦇R⦈⊑X` \ #src[Theorem 6.2]],
  // lean:AOP.A6_3.hylo_le_of_prefixed@b892517c
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], mbp(hterm((hb-cSo, hb-cR), [`B`], [`A`], rhs: (hb-X,))),
    [`⦇S⦈°⦇R⦈⊑X` \ #src[the conclusion]])],
  [#trow(
    hy-cata,
    tpanR(4.2, 2.1, [`X`], w: 3.0, top: [`B`]),
  )],

  [#vstep(IFF, mbp(hterm((hb-cR,), [`T`], [`A`], rhs: (hb-W,))),
    [`⦇R⦈⊑⦇S⦈°\X` \ #src[@adj-all's `S·⊣S\` at `⦇S⦈°`]])],
  [#trow(
    hy-cataR,
    tpanR(4.2, 2.1, [`⦇S⦈°\X`], w: 3.0, top: [`T`]),
  )],

  [#vstep(IMP, mbp(hterm((hb-alo, hb-FW, hb-R), [`T`], [`A`], rhs: (hb-W,))),
    [`α°F(⦇S⦈°\X)R⊑⦇S⦈°\X` \ #src[(6.2) `⦇R⦈=(μX : α°F(X)R)` — @cata-defining and @mu-laws;
 ]])],
     // lean:AOP.A6_2.relCata_le_of_prefixed@9f98060a
  [#trow(
    tpan(4.2, ((3.0, [`α°`]), (2.1, [`⦇S⦈°\X`]), (1.2, [`R`])),
      hands: ((TXF, 3.0, 1.2, [`F`]),), top: ((TXO, [`T`]),), w: 4.8),
    tpanR(4.2, 2.1, [`⦇S⦈°\X`], w: 3.0, top: [`T`]),
  )],

  [#vstep(IFF, mbp(hterm((hb-cSo, hb-alo, hb-FW, hb-R), [`B`], [`A`], rhs: (hb-X,))),
    [`⦇S⦈°α°F(⦇S⦈°\X)R⊑X` \ #src[@adj-all's `S·⊣S\` at `⦇S⦈°`]])],
  [#trow(
    tpan(4.2, ((3.6, [`⦇S⦈°`]), (3.0, [`α°`]), (2.1, [`⦇S⦈°\X`]), (1.2, [`R`])),
      hands: ((TXF, 3.0, 1.2, [`F`]),), top: ((TXO, [`B`]),), w: 4.8),
    tpanR(4.2, 2.1, [`X`], w: 3.0, top: [`B`]),
  )],

  [#vstep(IFF, mbp(hterm((hb-So, hb-FcSo, hb-FW, hb-R), [`B`], [`A`], rhs: (hb-X,))),
    [`S°F(⦇S⦈°)F(⦇S⦈°\X)R⊑X` \ #src[`⦇S⦈°α°=S°F(⦇S⦈°)` — @hylo-fix]])],
  [#trow(
    tpan(4.2, ((3.6, [`S°`]), (3.0, [`⦇S⦈°`]), (2.1, [`⦇S⦈°\X`]), (1.2, [`R`])),
      hands: ((TXF, 3.6, 1.2, [`F`]),), top: ((TXO, [`B`]),), w: 4.8),
    tpanR(4.2, 2.1, [`X`], w: 3.0, top: [`B`]),
  )],

  [#vstep(IMP, mbp(hterm((hb-So, hb-FX, hb-R), [`B`], [`A`], rhs: (hb-X,))),
    [`S°F(X)R⊑X` \ #src[`F(RS)=F(R)F(S)` — @relator-defn — and `⦇S⦈°(⦇S⦈°\X)⊑X` — @adj-all]])],
  [#trow(
    hy-prefix,
    tpanR(4.2, 2.1, [`X`], w: 3.0, top: [`B`]),
  )],
))]<hylo-least>

// The chain LEAVES `(μX : S°F(X)R)` and comes back to it, so everything on the way is equal: one
// `⊑` is @hylo-fix through @mu-laws, the other @hylo-least at the prefix point `μ` is.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
 Thm[`⦇S⦈°⦇R⦈=(μX : S°F(X)R)` \ #src[Theorem 6.2]],
  // lean:AOP.A6_3.hylo_eq_mu@c60df971
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], mbp(hterm((hb-mu,), [`B`], [`A`])),
    [`(μX : S°F(X)R)` \ #src[@mu-defn at `φ(X):=S°F(X)R`]])],
  [#tpanR(4.2, 2.1, [`(μX : S°F(X)R)`], w: 5.8, top: [`B`])],

  [#vstep(SQ, mbp(hterm((hb-cSo, hb-cR), [`B`], [`A`])),
    [`⦇S⦈°⦇R⦈` \ #src[@mu-laws's `φ(Y)⊑Y⟹(μX : φ(X))⊑Y` at `Y:=⦇S⦈°⦇R⦈`, whose
 `S°F(⦇S⦈°⦇R⦈)R=⦇S⦈°⦇R⦈` is @hylo-fix]])],
     // lean:AOP.A6_2.mu_le_of_fixed@8ea2332b
  [#hy-cata],

  [#vstep(SQ, mbp(hterm((hb-mu,), [`B`], [`A`])),
    [`(μX : S°F(X)R)` \ #src[@hylo-least at `X:=(μX : S°F(X)R)`, whose
     `S°F((μX : S°F(X)R))R⊑(μX : S°F(X)R)` is @mu-laws's `φ((μX : φ(X)))=(μX : φ(X))`;
 ]])],
     // lean:AOP.A6_2.mu_prefixed@fc0a1dca
  [#tpanR(4.2, 2.1, [`(μX : S°F(X)R)`], w: 5.8, top: [`B`])],
))]<hylo-mu>

#pagebreak(weak: true)
= Combinatorial functions <sec-comb>

// B&dM §5.6, p. 125, plus the three specifications of Ex 7.39–7.41 (p. 174).  Every composite is
// mirrored to diagram order, so B&dM's `prefix · suffix` is `suffix prefix` here.
#disp[#table(
  columns: (7.1cm, 2.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

  [`[A]::=nil|cons (A,[A])`],
  [`𝒜⟶𝒜`],
  [B&dM's `listr` under the short name it keeps from p. 125 on.],

 [`list(R)≜⦇[nil,(R⊗𝟙) cons]⦈` #src[]],
  // lean:AOP.A5_6_ListCombinators.list_cata@83b2fcc6
  [`[A]⟶[B]`],
  [The relator's action on `R : A⟶B`: one `R` per element, the shape untouched.],

 [`subseq≜⦇[nil,cons∪π₂]⦈` #src[]],
  // lean:AOP.A5_6_ListCombinators.subseq_cata@97265f47
  [`[A]⟶[A]`],
  [`xs subseq ys`: `ys` is `xs` with elements dropped — `cons` keeps the head, `π₂` drops it.],

  [`prefix≜⦇[nil,nil∪cons]⦈` \
 `=cat° π₁=init*` #src[]],
   // lean:AOP.A5_6_ListCombinators.prefix_cata@82edcdaa lean:AOP.A5_6_ListCombinators.prefix_cat@eb19c936
  [`[A]⟶[A]`],
  [`ys` is an initial segment of `xs`; the first `nil` is where it stops early. `init≜snoc° π₁`.],

 [`suffix≜cat° π₂=tail*` #src[]],
  // lean:AOP.A5_6_ListCombinators.suffix_cat@c70cd49e
  [`[A]⟶[A]`],
  [The dual, `tail≜cons° π₂`; as a reduce it needs snoc-lists.],

 [`segment≜suffix prefix` #src[]],
  // lean:AOP.A5_6_ListCombinators.segment_eq@db9aa91a
  [`[A]⟶[A]`],
  [A contiguous stretch of `xs`: a suffix, then a prefix of that.],

 [`partition≜concat°` #src[]],
  // lean:AOP.A5_6_ListCombinators.partition_concat@f9c15a2e
  [`[A]⟶[[A]⁺]`],
  [This `cat` is restricted to `[A]⁺×[A]⟶[A]`, so `ys` is a list of non-empty segments of `xs`.],

 [`concat≜⦇[nil,cat]⦈` #src[]],
  // lean:AOP.A5_6_ListCombinators.concat_cata@7345ecd3
  [`[[A]]⟶[A]`],
  [Joins the segments back up, which is why its converse splits a list.],

  [`inits`],
  [`[A]⟶[[A]]`],
  [Implements $frac(#[`prefix`], ∋)$, listing the prefixes by increasing length.],

  [`tails`],
  [`[A]⟶[[A]]`],
  [Implements $frac(#[`suffix`], ∋)$ by decreasing length — the opposite order.],

  [`filter(p)≜` $frac(#[`subseq list(p)`], ∋)$ `est(R°)`],
  [`[A]⟶[A]`],
  [The longest subsequence of `xs` whose every element passes `p`.
   #h(4pt) #src[Ex 7.41; `est(R°)` is @est-defn]],

  [`R≜length≤length°`],
  [`[A]⟶[A]`],
  [The preorder `filter` and `takewhile` maximise over: the longer list wins.
   #h(4pt) #src[`≥≜≤°`]],

  [`takewhile(p)≜` $frac(#[`prefix list(p)`], ∋)$ `est(R°)`],
  [`[A]⟶[A]`],
  [The same with `prefix` for `subseq`: the longest prefix whose every element passes `p`.
   #h(4pt) #src[Ex 7.39]],

  [`mss≜` $frac(#[`segment sum`], ∋)$ `est(≥)`],
  [`[Int]⟶Int`],
  [Maximum segment sum. `segment=suffix prefix` splits it into $frac(#[`prefix sum`], ∋)$ `est(≥)`
   on each suffix. #h(4pt) #src[Ex 7.40]],
)]<comb-fns>

== $frac(#[`subseq`], ∋)$ `=⦇[nil` $frac(#[`𝟙`], ∋)$`,⟨`$frac(#[`𝟙×∋`], ∋)$` E(cons),π₂⟩ cup]⦈`

// B&dM §5.6, p. 124: @cata-map-calc run at `subseq`'s algebra `[nil, cons ∪ π₂]`, which is what
// turns the relation into a program.  `cup` is needed first — nothing above this note has a binary union.
#disp[#definition[
`cup≜` $frac(#[`π₁∋∪π₂∋`], ∋)$ ` : EA×EA⟶EA`, #h(4pt) so
$frac(#[`R∪S`], ∋)$ `=⟨`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`⟩ cup`.
#h(4pt) #src[]
// lean:AOP.A5_6.Λ_union@632cc56a
]]<cup-defn>

// §12.1's bracket: the tape's fork IS `F([A])=𝟏+A×[A]`'s case split, `𝟏` above and the pair below,
// ONE WIRE each, each branch opening with an injection's converse — `[R,S]=l°R∪r°S` (@coprod-laws).
#let SBY = 1.15                                   // the branch height
#let SBW = 0.92                                   // circuit.typ's box width, which it does not export
#let sbw(items, inj) = (if inj { SBW + LEAD } else { 0.0 }) + items.map(it => it.at(1)).sum(default: 0.0) + calc.max(items.len() - 1, 0) * LEAD
#let sbtw(up, lo, inj: true) = calc.max(sbw(up, inj), sbw(lo, inj)) + 1.92
#let sbbranch(x, y, inj, items, cw) = {
  let cx = x
  if inj != none {
    gbox((cx, y), inj, flip: true, fill: TINT); cx = cx + SBW
    wire((cx, y), (cx + LEAD, y)); cx = cx + LEAD
  }
  for (i, it) in items.enumerate() {
    if i > 0 { wire((cx, y), (cx + LEAD, y)); cx = cx + LEAD }
    gbox((cx, y), it.at(0), w: it.at(1), h: it.at(3, default: 0.6), chamfer: it.at(2))
    cx = cx + it.at(1)
  }
  if x + cw - cx > 0.02 { wire((cx, y), (x + cw, y)) }
}
// `inj: false` draws a `∪` instead: both its branches carry the same object and inject nothing.
#let sbtape(x, up, lo, inj: true) = {
  let cw = calc.max(sbw(up, inj), sbw(lo, inj))
  let hh = SBY + 0.45 + (up + lo).map(it => it.at(3, default: 0.6)).fold(0.6, calc.max) / 2
  tape((x, -hh), (x + cw + 1.92, hh))
  tape-fork((x + 0.22, 0), sp: SBY, len: 0.7)
  sbbranch(x + 0.92, SBY, if inj { [`l`] } else { none }, up, cw)
  sbbranch(x + 0.92, -SBY, if inj { [`r`] } else { none }, lo, cw)
  tape-join((x + cw + 1.62, 0), sp: SBY, len: 0.7)
}
// A box is `(label, width, chamfer)`, or `(…, height)` where a fraction needs two lines.
#let sb-me = ([`𝟙×∋`], 1.55, true)
#let sb-cons = ([`cons`], 1.3, false)
#let sb-p2 = ([`π₂`], 1.3, false)
#let sb-ni = ([`∋`], 0.7, true)
#let sb-consE = (frc([`(𝟙×∋)cons`]), 2.9, false, TH)
#let sb-p2E = (frc([`π₂∋`]), 1.5, false, TH)
#let sb-meE = (frc([`𝟙×∋`]), 1.7, false, TH)
#let sb-Econs = ([`E(cons)`], 2.0, false)

// The `∪`'s `cons` operand, drawn Hinze–Marsden: `𝟙×∋` acts on the TAIL, so `∋` is a bead on the
// object wire and `cons` is where the `A×−` wire ends on it.  Emitted verbatim by `./scripts/diagram`;
// `sb-hm-born` adds the `E` the transpose opens.
#let sb-hm = dpanel(3, 8, 5.15,
  ((0.55, 1, "bot", none, none), (1.7, "top", 1, none, none), (2.85, "top", 2, none, none), (4, "top", 1, none, none)),
  ((2, [`∋`], black, 2.85), (1, [`cons`], black, 1.7)),
  ((1.7, [`A×−`]), (2.85, [`E`]), (4, [`list`]), (5.15, [`A`])),
  ((0.55, [`list`]), (5.15, [`A`])),
  opath: ((5.15, 3), (5.15, 2), (4, 1), (1.7, 0)),
  cert: (expect: "(𝟙×∋)cons", src: "A×E(list(A))", tgt: "list(A)"))
#let sb-hm-born = dpanel(4, 9.15, 6.3,
  ((0.55, 2.5, "bot", none, frc([`𝟙`])), (1.7, 1, "bot", none, none), (2.85, "top", 1, none, none), (4, "top", 2, none, none), (5.15, "top", 1, none, none)),
  ((2, [`∋`], black, 4), (1, [`cons`], black, 2.85)),
  ((2.85, [`A×−`]), (4, [`E`]), (5.15, [`list`]), (6.3, [`A`])),
  ((0.55, [`E`]), (1.7, [`list`]), (6.3, [`A`])),
  opath: ((6.3, 4), (6.3, 2), (5.15, 1), (2.85, 0)),
  cert: (expect: "𝟙%∋ E(𝟙×∋)E(cons)", src: "A×E(list(A))", tgt: "E(list(A))"))
// @subseq-EW-case draws the `π₂` operand of `cons∪π₂` in every row, never `cons`: the derivation
// rewrites only `π₂` (@subseq-outr-square, then `∋%∋=𝟙`); `(𝟙×∋)cons` stays as `sb-hm` draws it.
// Recipe for a union's lower operand: the `cert:` is the formula with the `∪` cut to that operand
// by hand (`rank` in `scripts/diagram` would pick the other), and the cell's `#src` names it.
#let sb-hm-p2a = dpanel(3, 6.85, 4,
  ((0.55, "top", 1, none, none), (1.7, "top", 2, none, none), (2.85, "top", "bot", none, none)),
  ((2, [`∋`], black, 1.7), (1, [`π₂`], black, 0.55)),
  ((0.55, [`A×−`]), (1.7, [`E`]), (2.85, [`list`]), (4, [`A`])),
  ((2.85, [`list`]), (4, [`A`])),
  cert: (expect: "(𝟙×∋)π₂", src: "A×E(list(A))", tgt: "list(A)"))
#let sb-hm-p2 = dpanel(4, 8, 5.15,
  ((0.55, 2.5, "bot", none, frc([`𝟙`])), (1.7, "top", 1, none, none), (2.85, "top", 2, none, none), (4, "top", "bot", none, none)),
  ((2, [`∋`], black, 2.85), (1, [`π₂`], black, 1.7)),
  ((1.7, [`A×−`]), (2.85, [`E`]), (4, [`list`]), (5.15, [`A`])),
  ((0.55, [`E`]), (4, [`list`]), (5.15, [`A`])),
  cert: (expect: "𝟙%∋ E(𝟙×∋)E(π₂)", src: "A×E(list(A))", tgt: "E(list(A))"))

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`F(∋)[nil,cons∪π₂]`])` =[nil `#frc([`𝟙`])`,`#frc([`(𝟙×∋)(cons∪π₂)`])`]` \
    #src[@cata-map-calc at `subseq=⦇[nil,cons∪π₂]⦈` — @comb-fns.
 ]],
    // lean:AOP.A5_6_ListCombinators.subseq_cata@97265f47
  table.header([*circuit* — the fork is `F([A])=𝟏+A×[A]`: `nil` above, the pair below],
    [*Hinze–Marsden*]),

  // Rows 1–3 draw the NUMERATOR, `F(E([A])) ⟶ [A]`: the transpose is still outside the bracket there,
  // and the generator fuses `F(∋)[f,g]` into the one tape `[f,(𝟙×∋)g]` on trust (CIRCUIT-GEN §1.4).
  [#vstep([], [#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "∋", chamfer: true, frac: false, flip: false),
              ), seams: ()),
          )),
        (k: "union", nin: 2, nout: 1, bodies: (
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "proj", nin: 2, nout: 1, at: 1, label: "π₂", keep: (1, 1, )),
              ), seams: ()),
          )),
      ), seams: (
        (
          0,
          ("A", "E[A]", ),
        ),
      )),
  ), src: ("FE[A]", ), tgt: ("[A]", )),
  cert: (expect: "F(∋)[nil,cons∪π₂]", src: "F(E([A]))", tgt: "[A]"))], [#frc([`F(∋)[nil,cons∪π₂]`])])],
  [#sb-hm-p2a \ #src[the `π₂` operand of `cons∪π₂` under the `𝟙×∋` summand of `F(∋)`, i.e. `(𝟙×∋)π₂`]],

  // `+` is not in the generator's grammar: `𝟙+𝟙×∋` is drawn as the `F(∋)` it unfolds (`F(X)=𝟏+A×X`).
  [#vstep(EQ, [#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "∋", chamfer: true, frac: false, flip: false),
              ), seams: ()),
          )),
        (k: "union", nin: 2, nout: 1, bodies: (
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "proj", nin: 2, nout: 1, at: 1, label: "π₂", keep: (1, 1, )),
              ), seams: ()),
          )),
      ), seams: (
        (
          0,
          ("A", "E[A]", ),
        ),
      )),
  ), src: ("FE[A]", ), tgt: ("[A]", )),
  cert: (expect: "F(∋)[nil,cons∪π₂]", src: "F(E([A]))", tgt: "[A]"))], [#frc([`(𝟙+𝟙×∋)[nil,cons∪π₂]`]) \ #src[`F(X)=𝟏+A×X` — @comb-fns]])],
  [#sb-hm-p2a \ #src[the same operand under `𝟙+𝟙×∋`, whose `𝟙×∋` summand it sits in]],

  [#vstep(EQ, [#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "∋", chamfer: true, frac: false, flip: false),
              ), seams: ()),
          )),
        (k: "union", nin: 2, nout: 1, bodies: (
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "proj", nin: 2, nout: 1, at: 1, label: "π₂", keep: (1, 1, )),
              ), seams: ()),
          )),
      ), seams: (
        (
          0,
          ("A", "E[A]", ),
        ),
      )),
  ), src: ("FE[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(𝟙×∋)(cons∪π₂)]", src: "F(E([A]))", tgt: "[A]"))], [#frc([`[nil,(𝟙×∋)(cons∪π₂)]`]) \
    #src[`R+S≜[Rl,Sr]`, `l[R,S]=R`, `r[R,S]=S` — @coprod-laws]])],
  [#sb-hm-p2a \ #src[the `π₂` operand of the second arm `(𝟙×∋)(cons∪π₂)`]],

  [#vstep(EQ, [#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(nil)", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          1,
          ("E𝟏", ),
        ),
      )),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E((𝟙×∋)(cons∪π₂))", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "E[A]", ),
        ),
        (
          1,
          ("E(A×E[A])", ),
        ),
      )),
  ), src: ("FE[A]", ), tgt: ("E[A]", )),
  cert: (expect: "[nil%∋,((𝟙×∋)(cons∪π₂))%∋]", src: "F(E([A]))", tgt: "E([A])"))], [`[`#frc([`nil`])`,`#frc([`(𝟙×∋)(cons∪π₂)`])`]` \
    #src[@coprod-calc at `T:=[nil,(𝟙×∋)(cons∪π₂)]`]])],
  [#sb-hm-p2 \ #src[the `π₂` operand under its `𝟙%∋`, the arm @subseq-outr-square's square rewrites,
    `(𝟙×∋)π₂=π₂∋`]],

  [#vstep(EQ, [#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
      ), seams: (
        (
          1,
          ("[A]", ),
        ),
      )),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E((𝟙×∋)(cons∪π₂))", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "E[A]", ),
        ),
        (
          1,
          ("E(A×E[A])", ),
        ),
      )),
  ), src: ("FE[A]", ), tgt: ("E[A]", )),
  cert: (expect: "[nil 𝟙%∋,((𝟙×∋)(cons∪π₂))%∋]", src: "F(E([A]))", tgt: "E([A])"))], [`[nil `#frc([`𝟙`])`,`#frc([`(𝟙×∋)(cons∪π₂)`])`]` \
    #src[@pow-laws, #frc([`f`])` =f `#frc([`𝟙`]) for `f` a map, at `f:=nil`]])],
  [#sb-hm-p2 \ #src[the same operand; the two rows differ only in the `nil` arm]],
))]<subseq-EW-case>

// @relprod-pic's square at `R × S := 𝟙 × ∋`, on @cata-defining's 5.2 × 2.7 geometry.  The two `π₂`
// sit on OPPOSITE sides — one name, one colour, two rows, which is what the string picture cannot show.
#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (AE, E, AL, L) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
  ar(AE, E, GIVEN2, s0: 1.55, s1: 1.05); ar(AL, L, GIVEN2, s0: 1.2, s1: 0.7)
  ar(AE, AL, GIVEN1, s0: 0.55, s1: 0.55); ar(E, L, GIVEN1, s0: 0.55, s1: 0.55)
  lab(0, 1.9, GIVEN2)[`π₂`]; lab(0, -1.9, GIVEN2)[`π₂`]
  lab(-3.95, 0, GIVEN1)[`𝟙×∋`]; lab(3.2, 0, GIVEN1)[`∋`]
  node(AE.at(0), AE.at(1), black, `A×E([A])`); node(E.at(0), E.at(1), black, `E([A])`)
  node(AL.at(0), AL.at(1), black, `A×[A]`); node(L.at(0), L.at(1), black, `[A]`)
}))]<subseq-outr-square>

// The union under the transpose: `⟨·,·⟩` copies the input, one transpose per branch, and `cup` joins
// the two sets.  Both strands carry the same object, so the fork costs no crossing.
#let sbfork(a, b) = {
  let s = 0.95
  let rw(items) = items.map(it => it.at(1)).sum(default: 0.0) + calc.max(items.len() - 1, 0) * LEAD
  let w = calc.max(rw(a), rw(b))
  lab(-1.52, 0, black)[`A×E([A])`]
  wire((0, 0), (LEAD, 0)); wiredot((LEAD, 0))
  bend((LEAD, 0), (1.10, s)); bend((LEAD, 0), (1.10, -s))
  for (y, items) in ((s, a), (-s, b)) {
    wire((1.10, y), (1.10 + LEAD, y))
    let cx = 1.10 + LEAD
    for (i, it) in items.enumerate() {
      if i > 0 { wire((cx, y), (cx + LEAD, y)); cx = cx + LEAD }
      gbox((cx, y), it.at(0), w: it.at(1), h: it.at(3, default: 0.6), chamfer: it.at(2))
      cx = cx + it.at(1)
    }
    wire((cx, y), (1.10 + w + 2 * LEAD, y))
  }
  let xc = 1.10 + w + 2 * LEAD
  gbox((xc, 0), [`cup`], w: 1.15, h: 2.6, chamfer: false)
  wire((xc + 1.15, 0), (xc + 1.15 + LEAD, 0)); lab(xc + 2.40, 0, black)[`E([A])`]
}
#let sbB1 = P(cetz.canvas(length: 0.8cm, {
  lab(-1.52, 0, black)[`A×E([A])`]
  wire((0, 0), (LEAD, 0)); gbox((LEAD, 0), [`𝟙×∋`], w: 1.55)
  wire((LEAD + 1.55, 0), (2 * LEAD + 1.55, 0))
  sbtape(2 * LEAD + 1.55, (sb-cons,), (sb-p2,), inj: false)
  let xe = 2 * LEAD + 1.55 + sbtw((sb-cons,), (sb-p2,), inj: false)
  wire((xe, 0), (xe + LEAD, 0)); lab(xe + 0.95, 0, black)[`[A]`]
}), s: 82%)
#let sbB2 = P(cetz.canvas(length: 0.8cm, {
  lab(-1.52, 0, black)[`A×E([A])`]
  wire((0, 0), (LEAD, 0))
  sbtape(LEAD, (sb-me, sb-cons), (sb-me, sb-p2), inj: false)
  let xe = LEAD + sbtw((sb-me, sb-cons), (sb-me, sb-p2), inj: false)
  wire((xe, 0), (xe + LEAD, 0)); lab(xe + 0.95, 0, black)[`[A]`]
}), s: 82%)
#let sbB3 = P(cetz.canvas(length: 0.8cm, {
  lab(-1.52, 0, black)[`A×E([A])`]
  wire((0, 0), (LEAD, 0))
  sbtape(LEAD, (sb-me, sb-cons), (sb-p2, sb-ni), inj: false)
  let xe = LEAD + sbtw((sb-me, sb-cons), (sb-p2, sb-ni), inj: false)
  wire((xe, 0), (xe + LEAD, 0)); lab(xe + 0.95, 0, black)[`[A]`]
}), s: 82%)
#let sbB4 = P(cetz.canvas(length: 0.8cm, sbfork((sb-consE,), (sb-p2E,))), s: 82%)
#let sbB5 = P(cetz.canvas(length: 0.8cm, sbfork((sb-meE, sb-Econs), (sb-p2,))), s: 82%)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`(𝟙×∋)(cons∪π₂)`])` =⟨`#frc([`𝟙×∋`])` E(cons),π₂⟩ cup` \
    #src[B&dM §5.6, p. 124]],
  table.header([*circuit* — the tape IS the `∪`, and neither branch injects],
    [*Hinze–Marsden* — the `cons` operand]),

  [#vstep([], sbB1, [#frc([`(𝟙×∋)(cons∪π₂)`]) \ #src[@subseq-EW-case's second branch]])],
  [#sb-hm],

  [#vstep(EQ, sbB2, [#frc([`(𝟙×∋)cons∪(𝟙×∋)π₂`]) \ #src[`T(X₁∪X₂)=TX₁∪TX₂` — @adj-cross]])],
  // Empty: the step is in the `π₂` operand, which the panel above does not draw.
  [],

  [#vstep(EQ, sbB3, [#frc([`(𝟙×∋)cons∪π₂∋`]) \
    #src[`(𝟙×∋)π₂=π₂∋` — @relprod-pic at `π₂`, an equality because `𝟙` is entire]])],
  [],

  [#vstep(EQ, sbB4, [`⟨`#frc([`(𝟙×∋)cons`])`,`#frc([`π₂∋`])`⟩ cup` \
    #src[#frc([`R∪S`])` =⟨`#frc([`R`])`,`#frc([`S`])`⟩ cup` — @cup-defn]])],
  [#sb-hm-born],

  [#vstep(EQ, sbB5, [`⟨`#frc([`𝟙×∋`])` E(cons),π₂⟩ cup` \
    #src[@pow-laws, absorption #frc([`S`])` E(R)=`#frc([`SR`]) at `S:=𝟙×∋`, `R:=cons`; fusion and
     #frc([`∋`])` =𝟙` on the `π₂` operand]])],
  // Empty: `E((𝟙×∋)cons)=E(𝟙×∋)E(cons)` costs no notation, so the panel above is unchanged.
  [],
))]<subseq-EW-join>

// @coprod-laws' picture at this algebra, so the banana's contents are read off the tape: the fork is
// the coproduct, and every box inside it but the two injections is a MAP — `chamfer: false`.
#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let y = 1.7                     // branch height: a fraction box is 1.2 tall and has to clear the tape
  let (up, dn) = (-0.75, -2.65)     // the two strands of the fork `⟨·,·⟩` inside the right branch
  wire((0, 0), (0.34, 0))
  tape((0.34, -3.2), (11.7, 2.5))
  tape-fork((0.56, 0), sp: y, len: 1.0)
  gbox((1.56, y), [`l`], flip: true, fill: TINT); wire((2.48, y), (3.80, y))
  gbox((3.80, y), [`nil`], chamfer: false, w: 1.05); wire((4.85, y), (6.10, y))
  gbox((6.10, y), [$frac(#[`𝟙`], ∋)$], chamfer: false, w: 0.85, h: 1.2); wire((6.95, y), (10.40, y))
  gbox((1.56, -y), [`r`], flip: true, fill: TINT); wire((2.48, -y), (2.95, -y))
  wiredot((2.95, -y)); bend((2.95, -y), (3.70, up)); bend((2.95, -y), (3.70, dn))
  wire((3.70, up), (3.90, up))
  gbox((3.90, up), [$frac(#[`𝟙×∋`], ∋)$], chamfer: false, w: 1.7, h: 1.2); wire((5.60, up), (5.95, up))
  gbox((5.95, up), [`E(cons)`], chamfer: false, w: 2.0); wire((7.95, up), (8.50, up))
  wire((3.70, dn), (3.90, dn))
  gbox((3.90, dn), [`π₂`], chamfer: false, w: 1.3); wire((5.20, dn), (8.50, dn))
  gbox((8.50, -y), [`cup`], chamfer: false, w: 1.15, h: 2.6); wire((9.65, -y), (10.40, -y))
  tape-join((11.40, 0), sp: y, len: 1.0)
  wire((11.70, 0), (12.04, 0))
  lab(-2.22, 0, black)[`𝟏+A×E([A])`]; lab(13.25, 0, black)[`E([A])`]
}))
#align(center, block(inset: (y: 4pt))[
  #src[B&dM §5.6, p. 124, which writes `Pcons`; `cons` is a map, and there `P(cons)=E(cons)` — @powrel-laws.]
])]<subseq-alg>

#pagebreak(weak: true)
= Optimisation Problems <sec-opt>

== `est(R)≜∋∩(∈\R°)` <sec-est>

// B&dM §7.1, p. 166.  The `°` is what diagram order costs: it reverses the arrow but not the `≤`
// glyph, so without it `est(≤)` would come out the greatest element.
#disp[#definition[
For `R : A⟶A`, #h(4pt) `est(R)≜∋∩(∈\R°) : EA⟶A` #h(4pt) #src[].
// lean:AOP.A7_1.est@e39806f8

`xs (est(R)) x⟺x∈xs∧(∀y∈xs. x R y)` #h(4pt) #src[B&dM's `min R`, the same predicate under the same
letter; his `R : A⟵A` reads `x R y` as the arrow `y⟶x`, so `est(R)=min(R°)` once `R` is an arrow;
]
// lean:AOP.A7_4_Horner.est_apply@91dc1299

`xs (est(R)) x⟺(x in xs) and all x R\: xs` #h(4pt) #src[in q]

`est(R)=∋∩all R°` #h(4pt) #src[`all R≜∈\R`, q's `all`; the chains below keep it written `∈\`]

`E(R)≜` $frac(#[`∋R`], ∋)$ ` : EA⟶EB`, #h(4pt) `xs E(R) ys⟺ys={y∣∃x∈xs. x R y}` #h(4pt)
#src[the image of `xs`, @pow-laws]

`P(R) : EA⟶EB`, #h(4pt) `xs P(R) ys⟺(∀x∈xs. ∃y∈ys. x R y)∧(∀y∈ys. ∃x∈xs. x R y)` #h(4pt)
#src[every `x` and every `y` has a partner, @powrel-readings]
]]<est-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X⊑est(R)⟺X⊑∋` and `X°∋⊑R`], [in the set, and below every element of it],
  [$frac(#[`𝟙`], ∋)$ `(∈\R)=R`], [bounding a singleton is bounding its element],
  [$frac(#[`S`], ∋)$ `(∈\R)=S°\R`], [bound `S`'s image without building the set],
  [`union≜` $frac(#[`∋∋`], ∋)$ `: E(EA)⟶EA`], [flattens a set of sets],
  [`union (∈\R)=∈\(∈\R)`], [bound a union by bounding each member set],
  [$frac(#[`𝟙`], ∋)$ `est(R)=𝟙∩R°`],
 [a singleton's minimum is its element, where `R` is reflexive \ #src[$frac(#[`S`], ∋)$ `est(R)` at `S:=𝟙`]],
  // lean:AOP.A7_1.singletonMap_comp_est@06b2ed05
  [$frac(#[`S`], ∋)$ `est(R)=S∩(S°\R°)`], [an `S`-value that points to every `S`-value],
  [$frac(#[`S`], ∋)$ `est(R)=` $frac(#[`S`], ∋)$ `est(R∩S°S)`], [only `R` between values `S` gives one argument counts — context],
  [`E(S) est(R)=(∋S)∩((∋S)°\R°)`],
  [the same for the image of a set \ #src[$frac(#[`S`], ∋)$ `est(R)` at `S:=∋S`]],
  [`P(f) est(R)=est(fRf°) f`], [shunt a function through a minimum],
  [`P(S) est(R)=(∋S)∩(∈\(SR°))` \ #src[`R` reflexive]],
  [fusion with the power relator \ #src[`⊒` is the only proof here that tabulates]],
  [`P(S) est(R)⊑(∋S)∩(∈\(SR°))`], [the half of the row above that costs nothing],
  [`P(est(R)) est(R)⊑union est(R)` \ #src[`R` transitive]],
  [a minimum in each set, then a minimum of those],
  [`P(est(R)) est(R)=P(Dom(est(R))) union est(R)` \ #src[`R` a preorder]],
  [the same as an equality, once empty sets are dropped],
)]<est-laws>

=== `X⊑est(R)⟺X⊑∋` and `X°∋⊑R`

// The definition read through the two adjunctions it is built from.  B&dM p. 166 cites this as the
// hint "universal property of min", which the chains below cite as "UP of `est`".
#disp[
#zline(
  zsqc(`X`, `est(R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zpair(zsqc(`X`, `∋`), zsqc(`X`, `∈\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zpair(zsqc(`X`, `∋`), zsqc(`∈X`, `R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zpair(zsqc(`X`, `∋`), zsqc(`X°∋`, `R`)),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.le_est_iff@81855810
]<est-up>

=== $frac(#[`𝟙`], ∋)$ `(∈\R)=R`

// B&dM (7.1): the same four steps as the subsection below, with `(𝟙%∋) ∋ = 𝟙` — the `i ⊣ E` triangle —
// where that one has `(S%∋) ∋ = S`.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`𝟙`], ∋)$ `(∈\R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`𝟙`], ∋)$`°X`], `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc([`∈` $frac(#[`𝟙`], ∋)$`°X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc([`(`$frac(#[`𝟙`], ∋)$` ∋)°X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`i⊣E`],
  zsqc(`X`, `R`),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.singletonMap_comp_lb@9d4759cf
]<est-71>

=== $frac(#[`S`], ∋)$ `(∈\R)=S°\R`

$frac(#[`S`], ∋)$ gathers the `S`-image of a point into one set and `∈\R` asks that every member of
that set be `R`-related to the target, so the set cancels and `S°\R` asks it of the `S`-image
directly.

// B&dM (7.2): two adjunctions composed, `(S%∋) ∋ = S` collapsing the middle — the shape of (1.2a).
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `(∈\R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`S`], ∋)$`°X`], `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc([`∈` $frac(#[`S`], ∋)$`°X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc([`(`$frac(#[`S`], ∋)$ `∋)°X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`S°X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc(`X`, `S°\R`),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.Λ_comp_lb@f14ab8b5
]<est-72>

=== `union (∈\R)=∈\(∈\R)`

// B&dM (7.3): the shape of the two chains above with `union ∋ = ∋ ∋` in the middle.
#disp[
#zline(
  zsqc(`X`, `union (∈\R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc(`union° X`, `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc(`∈union° X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc(`(union∋)°X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`(∋∋)°X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`, `T·⊣T\`],
  zsqc(`X`, `∈\(∈\R)`),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.bigUnion_comp_lb@ed13dc7a
]<est-73>

=== $frac(#[`S`], ∋)$ `est(R)=S∩(S°\R°)`

// B&dM (7.5).  (7.4) is this at `S := 𝟙` and (7.7) at `S := ∋ S`, so neither needs a chain of its own.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `est(R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`S`], ∋)$`°X`], `est(R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zpair(zsqc([$frac(#[`S`], ∋)$`°X`], `∋`), zsqc([$frac(#[`S`], ∋)$`°X`], `∈\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zpair(zsqc(`X`, [$frac(#[`S`], ∋)$ `∋`]), zsqc(`X`, [$frac(#[`S`], ∋)$ `(∈\R°)`])),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, @est-72],
  zpair(zsqc(`X`, `S`), zsqc(`X`, `S°\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zsqc(`X`, `S∩(S°\R°)`),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.Λ_comp_est@4c6d38d0
]<est-75>

=== $frac(#[`S`], ∋)$ `est(R)=` $frac(#[`S`], ∋)$ `est(R∩S°S)`

// B&dM (7.6): `X ⊑ S` already forces `S° X ⊑ S° S`, so the extra conjunct costs nothing — that is
// the whole content, and it is the middle step.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `est(R∩S°S)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[@est-75, `°`],
  zsqc(`X`, `S∩(S°\(R°∩S°S))`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`X`, `S`), zsqc(`S°X`, `R°∩S°S`)),
)
// Six boxes on one row squeezed the wide ones into three lines each; the break is at the pair.
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`, `S°·` monotone],
  zpair(zsqc(`X`, `S`), zsqc(`S°X`, `R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`, `Δ⊣∩`],
  zsqc(`X`, `S∩(S°\R°)`),
  zstep(op: sym.arrow.l.r.double, under: true)[@est-75],
  zsqc(`X`, [$frac(#[`S`], ∋)$ `est(R)`]),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.Λ_comp_est_context@e8052cf4
]<est-76>

=== `P(f) est(R)=est(fRf°) f`

// B&dM (7.8), shunting a map through a minimum.  The one step that is not an adjunction is the
// modular law, and it needs `f` simple — the only such step in §@sec-est.
// No marker: (7.8) is one of the statements AOP/A7_1.lean drops (its closing block note).
#disp[
#zline(
  zsqc(`P(f) est(R)`, none, name: "f a map"),
  zstep(op: sym.eq, under: true)[`P=E` on maps, @est-75],
  zsqc(`(∋f)∩((∋f)°\R°)`, none),
  zstep(op: sym.eq, under: true)[`°`, `T·⊣T\`, `f°·⊣f·`],
  zsqc(`(∋f)∩(∈\(fR°))`, none),
)
// An operator is stretched to the reason's UNWRAPPED width, so a reason squeezed onto two lines
// overhangs the boxes beside it; the breaks below keep each reason on one line.
#zline(
  zstep(op: sym.eq, under: true)[modular law, `f` simple],
  zsqc(`(∋∩((∈\(fR°))f°))f`, none),
  zstep(op: sym.eq, under: true)[`·f⊣·f°`, `°`, `est`],
  zsqc(`est(fRf°) f`, none),
)
]<est-78>

=== `P(S) est(R)⊑(∋S)∩(∈\(SR°))`

// B&dM (7.10): `∋` is lax natural for the power relator, `P(S) ∋ ⊑ ∋ S`, and with the universal
// property of `est` that is the whole proof.  The equality (7.9) is not this — it needs tabulations.
#disp[
#zline(
  zsqc(`P(S) est(R)`, `(∋S)∩(∈\(SR°))`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(S) est(R)`, `∋S`), zsqc(`∈P(S) est(R)`, `SR°`)),
  zstep(op: sym.arrow.l.double, under: true)[UP of `est`],
  zpair(zsqc(`P(S)∋`, `∋S`), zsqc(`∈P(S)`, `S∈`)),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.powerRel_comp_est_le@d8b5692c
]<est-710>

=== `P(est(R)) est(R)⊑union est(R)`

// B&dM (7.11): (7.5) at `S := ∋ ∋` opens the right-hand side, then the same two facts as (7.10)
// close both strands — the left one twice, the right one against transitivity.
#disp[
#zline(
  zsqc(`P(est(R)) est(R)`, `union est(R)`, name: "R transitive"),
  zstep(op: sym.arrow.l.r.double, under: true)[@est-75],
  zsqc(`P(est(R)) est(R)`, `(∋∋)∩((∋∋)°\R°)`),
  zstep(op: sym.arrow.l.double, under: true)[`°`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(est(R)) est(R)`, `∋∋`), zsqc(`∈∈P(est(R)) est(R)`, `R°`)),
  zstep(op: sym.arrow.l.double, under: true)[UP of `est`, `R` transitive],
  zpair(zsqc(`P(est(R))∋`, `∋est(R)`), zsqc(`∈P(est(R))`, `est(R)∈`)),
)
#align(center, block(inset: (y: 4pt))[#src[, `R` transitive]])
// lean:AOP.A7_1.powerRel_est_le_bigUnion@d0c726a1
]<est-711>

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
#h(4pt) #src[Theorem 5.2]
// lean:AOP.A5_7.laxNatural_iff_strict_on_maps@e374cc23
]]<lax-defn>

#disp[#capbox(
  cetz.canvas(length: 0.8cm, {
    let (GT, FT, GB, FB) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
    ar(GT, FT, GIVEN1, s0: 0.75, s1: 0.75); ar(GB, FB, GIVEN1, s0: 0.75, s1: 0.75)
    ar(GT, GB, GIVEN2, s0: 0.55, s1: 0.55); ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55)
    lab(0, 1.8, GIVEN1)[`φ`#sub[`A`]]; lab(0, -1.8, GIVEN1)[`φ`#sub[`B`]]
    lab(-3.8, 0, GIVEN2)[`G(R)`]; lab(3.8, 0, GIVEN2)[`F(R)`]
    lab(0, 0, SLACK, rot: -45deg)[`⊑`]
    node(GT.at(0), GT.at(1), black, `GA`); node(FT.at(0), FT.at(1), black, `FA`)
    node(GB.at(0), GB.at(1), black, `GB`); node(FB.at(0), FB.at(1), black, `FB`)
  }),
 [`G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #src[]],
  // lean:AOP.A5_1.LaxNatural@ba661fee
)]<lax-str>

// Not in B&dM §5.7, which stops at Theorem 5.2.
// @lax-str's square at table size: `ns` are its four corners (top-left, top-right, bottom-left,
// bottom-right), `es` its four edges (top, bottom, left, right).  A vertical edge's name sits ON the
// edge, so two squares sharing one carry it once and a long name cannot reach into the next square.
#let SQW = 2.2
#let SQH = 0.95
#let laxsq(ns, es, x: 0) = {
  let (l, r) = (x - SQW, x + SQW)
  ar((l, SQH), (r, SQH), GIVEN1, s0: 0.5, s1: 0.5); ar((l, -SQH), (r, -SQH), GIVEN1, s0: 0.5, s1: 0.5)
  ar((l, SQH), (l, -SQH), GIVEN2, s0: 0.5, s1: 0.5); ar((r, SQH), (r, -SQH), GIVEN2, s0: 0.5, s1: 0.5)
  if es.at(0) != none { lab(x, SQH + 0.62, GIVEN1)[#es.at(0)] }
  if es.at(1) != none { lab(x, -SQH - 0.62, GIVEN1)[#es.at(1)] }
  if es.at(2) != none { node(l, 0, GIVEN2, es.at(2)) }
  if es.at(3) != none { node(r, 0, GIVEN2, es.at(3)) }
  lab(x, 0, SLACK, rot: -45deg)[`⊑`]
  node(l, SQH, black, ns.at(0)); node(r, SQH, black, ns.at(1))
  node(l, -SQH, black, ns.at(2)); node(r, -SQH, black, ns.at(3))
}

// Hinze–Marsden at the 2-category level: a REGION is an allegory, a WIRE a relator, a BEAD a
// LaT.  Regions are `LATP` wide, so the wire carrying the bead stands at the same pitch in every cell.
#let LATP = 1.15
#let LATH = 2.5
#let LATB = 1.35
#let latcol(i, j) = ((i * LATP, LATH), (j * LATP, LATH), (j * LATP, 0), (i * LATP, 0))
#let latpic(regions, wires, beads: (), ports: (), marks: (), names: (), s: 74%) = P(
  cetz.canvas(length: 0.8cm, {
    for (f, pts) in regions { hm-region(pts, f) }
    for pts in wires { hm-wire(pts) }
    // `side` is which way the name hangs off the dot, `dy` lifts it clear of a strand leaving there.
    for (p, l, side, dy) in beads {
      hm-bead(p, l, dx: side * 0.32, dy: dy, anchor: if side > 0 { "west" } else { "east" })
    }
    for (p, l, dir) in ports { hm-port(p, l, dir: dir) }
    // A relator between two beads has no box edge to be named at, so its name goes beside the wire.
    for (p, l) in marks { d.content((p.at(0) + 0.3, p.at(1)), text(black)[#l], anchor: "west") }
    for (p, l) in names { hm-name(p, l) }
  }),
  s: s,
)

#disp[#table(
  columns: (4.8cm, 10.6cm, 6.6cm),
  align: (left + horizon, center + horizon, center + horizon),
  // `y: 2pt`: the LaT letters wrap two of the statement lines, and at 5pt the table outgrew the page —
  // a `#disp` table cannot break, so the last row was laid over the one above it.
  inset: (x: 9pt, y: 2pt), stroke: 0.4pt + luma(190),
  table.header([*closed under*], [*commutative diagram*], [*string diagram*]),

  [composition \ `ψφ`],
  [#P(cetz.canvas(length: 0.8cm, {
    laxsq((`HA`, `GA`, `HB`, `GB`), ([`ψ`#sub[`A`]], [`ψ`#sub[`B`]], [`H(R)`], none), x: -SQW)
    laxsq((`GA`, `FA`, `GB`, `FB`), ([`φ`#sub[`A`]], [`φ`#sub[`B`]], [`G(R)`], [`F(R)`]), x: SQW)
  }), s: 74%)
   `H(R)ψ`#sub[`B`]`⊑ψ`#sub[`A`]`G(R)` #h(4pt) and #h(4pt) `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)`
   #h(4pt) give #h(4pt) `H(R)(ψ`#sub[`B`]`φ`#sub[`B`]`)⊑(ψ`#sub[`A`]`φ`#sub[`A`]`)F(R)`],
  latpic(
    ((fb-ALLC, latcol(0, 1)), (fb-ZC, latcol(1, 2))),
    (((LATP, LATH), (LATP, 0)),),
    beads: (((LATP, 1.75), [`ψ`], 1, 0), ((LATP, 0.75), [`φ`], 1, 0)),
    ports: (((LATP, LATH), [`H`], 1), ((LATP, 0), [`F`], -1)),
    marks: (((LATP, 1.25), [`G`]),),
    names: (((0.5 * LATP, 0.3), [`𝓓`]), ((1.5 * LATP, 0.3), [`𝒞`])),
  ),

  [horizontal composition \ `χ∘φ`],
  [#P(cetz.canvas(length: 0.8cm, laxsq(
    (`L(GA)`, `K(FA)`, `L(GB)`, `K(FB)`),
    ([`χ`#sub[`GA`]`K(φ`#sub[`A`]`)`], [`χ`#sub[`GB`]`K(φ`#sub[`B`]`)`], `L(G(R))`, `K(F(R))`),
  )), s: 74%)
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
  latpic(
    ((fb-MAPC, latcol(0, 1)), (fb-ALLC, latcol(1, 2)), (fb-ZC, latcol(2, 3))),
    (((LATP, LATH), (LATP, 0)), ((2 * LATP, LATH), (2 * LATP, 0))),
    beads: (((LATP, LATB), [`χ`], 1, 0), ((2 * LATP, LATB), [`φ`], 1, 0)),
    ports: (((LATP, LATH), [`L`], 1), ((LATP, 0), [`K`], -1),
      ((2 * LATP, LATH), [`G`], 1), ((2 * LATP, 0), [`F`], -1)),
    names: (((0.5 * LATP, 0.3), [`𝓔`]), ((1.5 * LATP, 0.3), [`𝓓`]), ((2.5 * LATP, 0.3), [`𝒞`])),
  ),

  [union \ `φ∪ψ`],
  [#P(cetz.canvas(length: 0.8cm, {
    laxsq((`GA`, `FA`, `GB`, `FB`), ([`φ`#sub[`A`]], [`φ`#sub[`B`]], [`G(R)`], [`F(R)`]), x: -(SQW + 1.4))
    laxsq((`GA`, `FA`, `GB`, `FB`), ([`ψ`#sub[`A`]], [`ψ`#sub[`B`]], [`G(R)`], [`F(R)`]), x: SQW + 1.4)
    lab(0, 0, black)[`∪`]
  }), s: 74%)
   `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) and #h(4pt) `G(R)ψ`#sub[`B`]`⊑ψ`#sub[`A`]`F(R)`
   #h(4pt) give #h(4pt) `G(R)(φ`#sub[`B`]`∪ψ`#sub[`B`]`)⊑(φ`#sub[`A`]`∪ψ`#sub[`A`]`)F(R)`
 #h(4pt) #src[]],
   // lean:AOP.A5_7.union_slides@f7484fb4
  align(center, grid(columns: 3, align: horizon, column-gutter: 2pt,
    latpic(
      ((fb-ALLC, latcol(0, 1)), (fb-ZC, latcol(1, 2))),
      (((LATP, LATH), (LATP, 0)),),
      beads: (((LATP, LATB), [`φ`], 1, 0),),
      ports: (((LATP, LATH), [`G`], 1), ((LATP, 0), [`F`], -1)),
    ),
    [`∪`],
    latpic(
      ((fb-ALLC, latcol(0, 1)), (fb-ZC, latcol(1, 2))),
      (((LATP, LATH), (LATP, 0)),),
      beads: (((LATP, LATB), [`ψ`], 1, 0),),
      ports: (((LATP, LATH), [`G`], 1), ((LATP, 0), [`F`], -1)),
    ),
  )),

  [a relator `K` \ `K(φ)`],
  [#P(cetz.canvas(length: 0.8cm, laxsq(
    (`K(GA)`, `K(FA)`, `K(GB)`, `K(FB)`),
    ([`K(φ`#sub[`A`]`)`], [`K(φ`#sub[`B`]`)`], [`K(G(R))`], [`K(F(R))`]),
  )), s: 74%)
   `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) gives #h(4pt)
   `K(G(R))K(φ`#sub[`B`]`)⊑K(φ`#sub[`A`]`)K(F(R))`],
  [],

  [product \ `φ×ψ`],
  [#P(cetz.canvas(length: 0.8cm, laxsq(
    (`GA×G'A`, `FA×F'A`, `GB×G'B`, `FB×F'B`),
    ([`φ`#sub[`A`]`×ψ`#sub[`A`]], [`φ`#sub[`B`]`×ψ`#sub[`B`]], `G(R)×G'(R)`, `F(R)×F'(R)`),
  )), s: 74%)
   `φ : G⇒F` and `ψ : G'⇒F'` give `φ×ψ : G×G'⇒F×F'` \
   #src[`(R×S)(U×V)=(RU)×(SV)` and monotonicity in both slots — the row above's `K` applied to the
   inequation, run on a bifunctor; the fork is the derived case `⟨φ,ψ⟩=◁(φ×ψ)`, and its ONE cost is
   the lax copy law `R◁⊑◁(R×R)` — @rel-monoid]],
  // `G×G'=×∘⟨G,G'⟩`: two UNARY functors, so the split is typed — `⟨G,G'⟩ : 𝒞⟶𝓓×𝓓` then `× : 𝓓×𝓓⟶𝓓`.
  // The bead is the PAIR in `𝓓×𝓓`, written `(φ,ψ)`: the fork `⟨φ,ψ⟩=◁(φ×ψ)` is a different arrow, in `𝓓`.
  latpic(
    ((fb-ALLC, latcol(0, 1)), (fb-MAPC, latcol(1, 2)), (fb-ZC, latcol(2, 3))),
    (((LATP, LATH), (LATP, 0)), ((2 * LATP, LATH), (2 * LATP, 0))),
    beads: (((2 * LATP, LATB), [`(φ,ψ)`], 1, 0),),
    ports: (((LATP, LATH), [`×`], 1), ((LATP, 0), [`×`], -1),
      ((2 * LATP, LATH), [`⟨G,G'⟩`], 1), ((2 * LATP, 0), [`⟨F,F'⟩`], -1)),
    names: (((1.5 * LATP, 0.3), [`𝓓×𝓓`]),),
  ),

  [coproduct \ `φ+ψ`],
  [#P(cetz.canvas(length: 0.8cm, laxsq(
    (`GA+G'A`, `FA+F'A`, `GB+G'B`, `FB+F'B`),
    ([`φ`#sub[`A`]`+ψ`#sub[`A`]], [`φ`#sub[`B`]`+ψ`#sub[`B`]], `G(R)+G'(R)`, `F(R)+F'(R)`),
  )), s: 74%)
   `φ : G⇒F` and `ψ : G'⇒F'` give `φ+ψ : G+G'⇒F+F'` \
   #src[`(R+S)(U+V)=(RU)+(SV)` and monotonicity in both slots; the co-fork is the derived case
   `[φ,ψ]=(φ+ψ)▿`, and `▿` costs nothing]],
  // `+`, like `×`, is a functor `𝓓×𝓓⟶𝓓`, so the picture is the one above with `+` on the left wire.
  latpic(
    ((fb-ALLC, latcol(0, 1)), (fb-MAPC, latcol(1, 2)), (fb-ZC, latcol(2, 3))),
    (((LATP, LATH), (LATP, 0)), ((2 * LATP, LATH), (2 * LATP, 0))),
    beads: (((2 * LATP, LATB), [`(φ,ψ)`], 1, 0),),
    ports: (((LATP, LATH), [`+`], 1), ((LATP, 0), [`+`], -1),
      ((2 * LATP, LATH), [`⟨G,G'⟩`], 1), ((2 * LATP, 0), [`⟨F,F'⟩`], -1)),
    names: (((1.5 * LATP, 0.3), [`𝓓×𝓓`]),),
  ),

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
  P(cetz.canvas(length: 0.9cm, {
    let (TL, TR, BL, BR) = ((-3.4, 1.3), (3.4, 1.3), (-3.4, -1.3), (3.4, -1.3))
    ar(TL, TR, GIVEN1, s0: 0.75, s1: 0.55); ar(TR, BR, GIVEN1, s0: 0.5, s1: 0.5)
    ar(TL, BL, GIVEN2, s0: 0.5, s1: 0.5); ar(BL, BR, GIVEN2, s0: 0.75, s1: 0.55)
    lab(0, 1.75, GIVEN1)[`π₁∩π₂`]; lab(3.95, 0, GIVEN1)[`R`]
    lab(-4.15, 0, GIVEN2)[`R×R`]; lab(0, -1.75, GIVEN2)[`π₁∩π₂`]
    lab(0, 0, TCOL, rot: -45deg)[$subset.eq.sq.not$]
    node(TL.at(0), TL.at(1), black, `A×A`); node(TR.at(0), TR.at(1), black, `A`)
    node(BL.at(0), BL.at(1), black, `B×B`); node(BR.at(0), BR.at(1), black, `B`)
    // The trace: `(0,1)` in at the top left, out as `{0}` down-then-across and as `∅` the other way.
    lab(-3.4, 2.1, luma(110))[`(0,1)`]; lab(3.4, 2.1, GIVEN1)[`∅`]
    lab(-3.4, -2.1, GIVEN2)[`(0,0)`]
    lab(2.85, -2.1, GIVEN2)[`{0}`]; lab(3.6, -2.1, TCOL)[$subset.eq.sq.not$]
    lab(4.25, -2.1, GIVEN1)[`∅`]
  }), s: 88%),
  [`A=B≜{0,1}`, #h(4pt) `R≜{(0,0),(1,0)}`, #h(4pt) `φ≜π₁∩π₂ : Δ⇒Id` \
   `π₁,π₂ : Δ⇒Id` are both LaTs #h(4pt) #src[@party-mono-branch's `g` row] #h(4pt) and
 `π₁∩π₂={((x,x),x)}` #h(4pt) #src[]],
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

  [union], [`R∪S`], [`φ∪ψ`, *survives* #h(4pt) #src[@lax-closure]],

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
  P(cetz.canvas(length: 0.8cm, {
    laxsq((`GX`, `FX`, `GY`, `FY`), ([`φ`#sub[`X`]], [`φ`#sub[`Y`]], `G(R)`, `F(R)`), x: -7.4)
    lab(-3.7, 0, black)[#sym.arrow.r.double.long]
    laxsq((`A`, `B`, `A`, `B`),
      ([`φ`#sub[`X`]], [`φ`#sub[`Y`]], [`𝟙`#sub[`A`]], [`𝟙`#sub[`B`]]), x: 0)
    lab(3.7, 0, black)[#sym.arrow.r.double.long]
    arc((5.2, 0), (9.6, 0), 1, [`φ`#sub[`X`]], col: GIVEN1, h: 1.6, cx: 3)
    arc((5.2, 0), (9.6, 0), -1, [`φ`#sub[`Y`]], col: GIVEN1, h: 1.6, cx: 3)
    // -45deg, the note's own tilt: a `⊑` turned the full -90deg is read as a `⊔`.
    lab(7.4, 0, SLACK, rot: -45deg)[`⊑`]
    node(5.2, 0, black, `A`); node(9.6, 0, black, `B`)
  }), s: 82%),
  [`G≜const A`, #h(4pt) `F≜const B` #h(4pt) — the relators `X↦A` and `X↦B`, each sending every arrow
   to `𝟙` #h(4pt) #src[@lax-defn] \
   with `𝒞` two objects and one non-identity arrow `X⟶Y`, a LaT `const A⇒const B` is the pair
   `φ`#sub[`X`]`,φ`#sub[`Y`]` : A⟶B` with `φ`#sub[`Y`]`⊑φ`#sub[`X`] #h(4pt) — the datum `R⊑S` \
   not every LaT is constant: #h(4pt) `∋ : P⇒Id` #h(4pt) #src[@powrel-laws] #h(4pt)
   `π₂ : (A×−)⇒Id` #h(4pt) #src[@subseq-outr-square] #h(4pt) `◁ : Id⇒Δ` #h(4pt) #src[@rel-monoid]],
)]<lat-const>

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
// would sit alone at the foot of §13.2's last page.
#pagebreak(weak: true)
== Monotonic algebras

// B&dM §7.2, p. 172.  The section numbers no equation, so the table names its theorem instead;
// Theorem 7.1 is the subsection below, which states and proves it.
#disp[#definition[
An F-algebra `φ : FA⟶A` is *monotonic on* `R : A⟶A` when it is lax at `R` at #h(4pt)
`G:=F`, `F:=Id`: #h(4pt) `F(R)φ⊑φR`. #h(4pt) `R` is an *endorelation*, so `B=A` and
the two components `φ`#sub[`A`], `φ`#sub[`B`] are the one arrow `φ` — an algebra, not a family.

For a map `f : FA⟶A` that is #h(4pt) `f°F(R)f⊑R` #h(4pt) #src[@adj-all's `f°·⊣f·` at `X:=F(R)f`,
`Y:=R`], #h(4pt) equivalently #h(4pt)
// lean:AOP.A7_2.monotonicAlg_iff_conj@46638b64
`F(R)⊑fRf°` #h(4pt) #src[`·f⊣·f°` then `f°·⊣f·`,
].
// lean:AOP.A7_2.monotonicAlg_iff_sandwich@f82f1b18

`(≤×≤)+⊑+≤` — addition on `Nat` is monotonic on `≤`, which at the point level
reads #h(4pt) `c=a+b∧a≤a'∧b≤b'⟹c≤a'+b'`.
]]<mon-defn>

// @lax-str at `G := F`, `F := Id`: the right edge's `Id(R)` is written `R`, and the one algebra `φ`
// stands at both components.  `⊑` points NE — down-then-across is the smaller `F(R)φ`.
#disp[#capbox(
  cetz.canvas(length: 0.8cm, {
    let (FT, T, FB, B) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
    ar(FT, T, GIVEN1, s0: 0.75, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.75, s1: 0.55)
    ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55); ar(T, B, GIVEN2, s0: 0.55, s1: 0.55)
    lab(0, 1.8, GIVEN1)[`φ`]; lab(0, -1.8, GIVEN1)[`φ`]
    lab(-3.75, 0, GIVEN2)[`F(R)`]; lab(3.35, 0, GIVEN2)[`R`]
    lab(0, 0, SLACK, rot: -45deg)[`⊑`]
    node(FT.at(0), FT.at(1), black, `FA`); node(T.at(0), T.at(1), black, `A`)
    node(FB.at(0), FB.at(1), black, `FA`); node(B.at(0), B.at(1), black, `A`)
  }),
 [`F(R)φ⊑φR` #src[]],
  // lean:AOP.A7_2.MonotonicAlg@26944450
)]<mon-str>

=== Function `f` is monotonic on `R` iff it distributes over `R` <sec-mon-thm71>

#disp[#definition[
`f : FA⟶A` *distributes over* `R` if #h(4pt) `F(est(R))f⊑` $frac(#[`F(∋)f`], ∋)$ `est(R)`
#src[].
// lean:AOP.A7_2.Distributes@e061e29e

`+` distributes over `≤`, at the point level #h(4pt)
`min xs+min ys=min{x+y∣x∈xs∧y∈ys}` #h(4pt) for `xs`, `ys` non-empty and
`min≜est(≤)`.
]]<dist-defn>

// The `f` edges run across, as @mon-str's algebra does, so down-then-across is the smaller
// `F(est(R)) f` and `⊑` points NE.  Right: the same square at `F := (−×−)`, `f := +`, `R := ≤`.
#disp[#align(center, grid(columns: 2, align: horizon, column-gutter: 14pt,
  capbox(
    P(cetz.canvas(length: 0.8cm, {
      let (FEA, EA, FA, A) = ((-3.6, 1.25), (3.6, 1.25), (-3.6, -1.25), (3.6, -1.25))
      ar(FEA, EA, GIVEN1, s0: 1.05, s1: 0.65); ar(FA, A, GIVEN1, s0: 0.65, s1: 0.45)
      ar(FEA, FA, GIVEN2, s0: 0.55, s1: 0.55); ar(EA, A, GIVEN2, s0: 0.55, s1: 0.55)
      lab(0, 2.1, GIVEN1)[$frac(#[`F(∋)f`], ∋)$]; lab(0, -1.8, GIVEN1)[`f`]
      lab(-4.75, 0, GIVEN2)[`F(est(R))`]; lab(4.4, 0, GIVEN2)[`est(R)`]
      lab(0, 0, SLACK, rot: -45deg)[`⊑`]
      node(FEA.at(0), FEA.at(1), black, `F(EA)`); node(EA.at(0), EA.at(1), black, `EA`)
      node(FA.at(0), FA.at(1), black, `FA`); node(A.at(0), A.at(1), black, `A`)
    }), s: 74%),
 [`F(est(R))f⊑` $frac(#[`F(∋)f`], ∋)$ ` est(R)` #src[]],
    // lean:AOP.A7_2.Distributes@e061e29e
  ),
  capbox(
    P(cetz.canvas(length: 0.8cm, {
      // Each corner carries its VALUE under its type, inside the node's own white box: an annotation
      // set loose beside the node would land on the vertical edge it hangs off.
      let val(s) = { show raw: set text(size: 8.5pt); text(luma(110), s) }
      let vnode(p, ty, el) = node(p.at(0), p.at(1), black,
        grid(align: center, row-gutter: 2.5pt, ty, val(el)))
      let (FEA, EA, FA, A) = ((-4.8, 1.9), (4.8, 1.9), (-4.8, -1.9), (4.8, -1.9))
      ar(FEA, EA, GIVEN1, s0: 2.0, s1: 3.2); ar(FA, A, GIVEN1, s0: 2.15, s1: 2.05)
      ar(FEA, FA, GIVEN2, s0: 1.0, s1: 1.0); ar(EA, A, GIVEN2, s0: 1.0, s1: 1.0)
      lab(0, 2.75, GIVEN1)[$frac(#[`(∋×∋)+`], ∋)$]; lab(0, -2.5, GIVEN1)[`+`]
      lab(-6.75, 0, GIVEN2)[`est(≤)×est(≤)`]; lab(5.75, 0, GIVEN2)[`est(≤)`]
      lab(0, 0, SLACK, rot: -45deg)[`⊑`]
      vnode(FEA, `E Nat×E Nat`, `(xs,ys)`); vnode(EA, `E Nat`, `{x+y∣x∈xs∧y∈ys}`)
      vnode(FA, `Nat×Nat`, `(min xs,min ys)`); vnode(A, `Nat`, `min xs+min ys`)
    }), s: 74%),
    [`(est(≤)×est(≤))+⊑` $frac(#[`(∋×∋)+`], ∋)$ ` est(≤)`],
  ),
))]<dist-str>

// ---- Theorem 7.1's own drawing vocabulary.  A converse is the cup–cap FRAME of @conv-defn, so
// `f°Xf` is `f` bumped up over `X`; what the chain does is shrink that frame from `(F(∋)f)°` to `f°`.
#let convrun(x, y, items, rise: 1.9) = {
  conv-frame((x, y), w: boxrun-w(items), rise: rise)
  let b = conv-body((x, y), rise: rise)
  boxrun(b.at(0), b.at(1), items)
}
#let convrun-end(items) = conv-w(w: boxrun-w(items)) - SPLIT
// `mid` types the wire OUT of the frame; it also opens the `⊑` up so both runs can name their ends,
// which is how row 1 is typed.  Left `none`, the picture is the untyped one the later rows want.
#let mconj(inner, after, rhs, mid: none) = {
  let rise = 1.9
  convrun(0, 0, inner)
  let x = convrun-end(inner)
  boxrun(x, rise, after)
  let xe = x + boxrun-w(after)
  let d = if mid == none { 0.0 } else { 1.2 }
  lab(-0.42, 0, black)[`A`]
  if mid != none {
    node((1.4 + x) / 2, rise, black, mid)
    lab(xe + 0.42, rise, black)[`A`]
    lab(xe + 1.5 + d - 0.42, rise, black)[`A`]
  }
  lab(xe + 0.95 + d / 2, rise, SLACK)[`⊑`]
  boxrun(xe + 1.5 + d, rise, rhs)
  lab(xe + 1.5 + d + boxrun-w(rhs) + 0.42, rise, black)[`A`]
}

// B&dM Theorem 7.1, p. 172.  The mirrored chain lands on `R°`, and the last step, `f` a map, is
// what carries it back.
#let mb-f = ([`f`], 0.55, false)
#let mb-Fest = ([`F(est(R))`], 2.5, true)
#let mb-Fni = ([`F(∋)`], 1.3, true)
#let mb-Lam = (frc([`F(∋)f`]), 1.75, false)
#let mb-est = ([`est(R)`], 1.7, true)
#let mb-Fniest = ([`F(∈ est(R))`], 3.05, true)
#let mb-FRo = ([`F(R°)`], 1.4, true)
#let mb-FR = ([`F(R)`], 1.3, true)
#let mb-Ro = ([`R°`], 0.8, true)
#let mb-R = ([`R`], 0.7, true)
// The display number is 1.2cm wide but placed only 1.0cm into the margin, so it reaches ~6pt back
// into the column and the `Thm` cell's fill — drawn after it — paints over it; `pad` returns that strip.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`f°F(R)f⊑R⟺F(est(R))f⊑` #frc([`F(∋)f`]) ` est(R)` \
    #src[Theorem 7.1, `f` a map, `R` reflexive;
 ,
      // lean:AOP.A7_2.distributes_of_monotonicAlg@188d993a
 ]],
      // lean:AOP.A7_2.monotonicAlg_of_distributes@2fa0f83b
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], mbp({
    lab(-1.05, 0, black)[`F(EA)`]
    boxrun(0, 0, (mb-Fest, mb-f))
    let xl = boxrun-w((mb-Fest, mb-f))
    lab(xl + 0.42, 0, black)[`A`]
    lab(xl + 1.35, 0, SLACK)[`⊑`]
    boxrun(xl + 1.9, 0, (mb-Lam, mb-est), h: TH)
  }), [`F(est(R))f⊑` #frc([`F(∋)f`]) ` est(R)` \
    #frc([`S`]) `=` #frc([`𝟙`]) `E(S)`, #h(4pt) `S≜F(∋)f` \
    #src[def. `f` distributes over `R` — @dist-defn, @adj-E-bend]])],
  [#trow(
    tpan(4.2, ((2.75, [`est(R)`]), (1.35, [`f`])), joins: ((TXH, 2.75, 0.40), (TXF, 1.35, 0.70)),
      top: ((TXF, [`F`]), (TXH, [`E`]), (TXO, [`A`])), w: 3.8),
    tpan(4.2, ((2.45, [`∋`]), (1.55, [`f`]), (0.65, [`est(R)`])),
      hands: ((RXU, 3.40, 0.65, [`E`], frc([`𝟙`])),),
      joins: ((RXC, 2.45, 0.35), (RXF, 1.55, 0.65)),
      top: ((RXF, [`F`]), (RXC, [`E`]), (RXO, [`A`])), xo: RXO, w: 4.5),
  )],

  [#vstep(IFF, [],
    [#grid(columns: 3, align: (right + horizon, center + horizon, left + horizon),
       column-gutter: 6pt, row-gutter: 3pt,
       [`F(est(R))f`], [`⊑`], [`F(∋)f`],
       grid.cell(colspan: 3, align: center + horizon)[and],
       [`(F(∋)f)°F(est(R))f`], [`⊑`], [`R°`],
       grid.cell(colspan: 3, align: left + horizon, inset: (top: 3pt))[#src[@est-75 at `F(∋)f`;
         `F(est(R))f⊑(F(∋)f)°\R°⟺(F(∋)f)°F(est(R))f⊑R°` — @div-laws]],
       grid.cell(colspan: 3, align: left + horizon)[#src[`est(R)≜∋∩(∈\R°)` — @est-defn]])])],
  // One picture per conjunct: the first is row 1's left panel twice over, `est(R)` against `∋`, so
  // the inequation is bead against bead; the second is the row-3 panel the next step keeps.
  [#grid(rows: 3, align: center + horizon, row-gutter: 4pt,
    trow(
      tpan(4.2, ((2.75, [`est(R)`]), (1.35, [`f`])), joins: ((TXH, 2.75, 0.40), (TXF, 1.35, 0.70)),
        top: ((TXF, [`F`]), (TXH, [`E`]), (TXO, [`A`])), w: 3.8),
      tpan(4.2, ((2.75, [`∋`]), (1.35, [`f`])), joins: ((TXH, 2.75, 0.40), (TXF, 1.35, 0.70)),
        top: ((TXF, [`F`]), (TXH, [`E`]), (TXO, [`A`])), w: 3.8),
    ),
    [and],
    trow(
      tpan(4.0, ((3.25, [`f°`]), (2.35, [`∈`]), (1.35, [`est(R)`]), (0.55, [`f`])),
        hands: ((TXF, 3.25, 0.55, [`F`]), (TXH, 2.35, 1.35, [`E`])), top: ((TXO, [`A`]),)),
      tpanR(4.0, 1.90, [`R°`]),
    ),
  )],

  [#vstep(IFF, mbp(mconj((mb-Fni, mb-f), (mb-Fest, mb-f), (mb-Ro,), mid: [`F(EA)`])),
    [`(F(∋)f)°F(est(R))f⊑R°` \ #src[`est(R)⊑∋` — @est-defn; the first conjunct is free]])],
  // `(F(∋)f)°=f°F(∈)` splits the leading bead: `f°` opens the `F` wire, `∈` the `E` wire inside it.
  [#trow(
    tpan(4.0, ((3.25, [`f°`]), (2.35, [`∈`]), (1.35, [`est(R)`]), (0.55, [`f`])),
      hands: ((TXF, 3.25, 0.55, [`F`]), (TXH, 2.35, 1.35, [`E`])), top: ((TXO, [`A`]),)),
    tpanR(4.0, 1.90, [`R°`]),
  )],

  [#vstep(IFF, mbp(mconj((mb-f,), (mb-Fniest, mb-f), (mb-Ro,))),
    [`f°F(∈ est(R))f⊑R°` \ #src[converse, relators: `(F(∋)f)°=f°F(∈)` and
     `F(∈)F(est(R))=F(∈ est(R))`]])],
  // Empty: the step is a formula-level rewrite, and the picture above already draws it.
  [],

  [#vstep(IFF, mbp(mconj((mb-f,), (mb-FRo, mb-f), (mb-Ro,))),
    [`f°F(R°)f⊑R°` \ #src[`∈ est(R)=R°`, `R` reflexive — @est-defn]])],
  [#trow(
    tpan(3.8, ((3.00, [`f°`]), (1.85, [`R°`]), (0.70, [`f`])),
      hands: ((TXF, 3.00, 0.70, [`F`]),), top: ((TXO, [`A`]),)),
    tpanR(3.8, 1.85, [`R°`]),
  )],

  [#vstep(IFF, mbp(mconj((mb-f,), (mb-FR, mb-f), (mb-R,))),
    [`f°F(R)f⊑R` \ #src[`f` a map, so monotonic on `R` and `R°` together;
 ,
     // lean:AOP.A7_2.monotonicAlg_iff_conj@46638b64
 ]])],
     // lean:AOP.A7_2.monotonicAlg_recip_iff@27f6bb47
  [#trow(
    tpan(3.8, ((3.00, [`f°`]), (1.85, [`R`]), (0.70, [`f`])),
      hands: ((TXF, 3.00, 0.70, [`F`]),), top: ((TXO, [`A`]),)),
    tpanR(3.8, 1.85, [`R`]),
  )],
))]<mon-thm71>

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
// would sit alone at the foot of §13.3.1's last page.
#pagebreak(weak: true)
=== `Greedy Theorem: ⦇`$frac(#[`S`], ∋)$` est(R)⦈⊑`$frac(#[`⦇S⦈`], ∋)$` est(R), given S monotoic on R, F preserving °, and R transitive` <sec-greedy-thm72>

#let mb-S = ([`S`], 0.7, true)
#let mb-LamS = (frc([`S`]), 0.9, false)
// The `F` lane of the split panels, wider from `RXU` than §13.3.1's `RXF`: here the handle carries
// its own `F` name, which at that lane would sit against the unit's label.
#let GXF = 2.05
// `mconj` with the `⊑` optional, so rows 5–7 draw a TERM of one chain rather than an inequation,
// and with the run after the frame raised to `TH` — a fraction box is two lines tall.  A leading run
// of converses is ONE frame: `(SR)°=R°S°`, so the step that pulls `R°` out of `F` moves `R` inside.
#let gterm(inner, after, rhs: none) = {
  let rise = 1.9
  convrun(0, 0, inner)
  let x = convrun-end(inner)
  boxrun(x, rise, after, h: TH)
  let xe = x + boxrun-w(after)
  lab(-0.42, 0, black)[`A`]
  if rhs == none { lab(xe + 0.42, rise, black)[`A`] } else {
    lab(xe + 0.95, rise, SLACK)[`⊑`]
    boxrun(xe + 1.5, rise, rhs)
    lab(xe + 1.5 + boxrun-w(rhs) + 0.42, rise, black)[`A`]
  }
}
// B&dM Theorem 7.2, p. 173.  The hypothesis is monotonicity on the SAME `R` the conclusion's
// `est(R)` uses: the book reads right to left and states it on `R°`, and mirroring flips it back.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], [], [`⦇`#frc([`S`])` est(R)⦈⊑`#frc([`⦇S⦈`])` est(R)` \
    #src[the conclusion: one minimum kept at each step is below every result collected and one
 minimum taken at the end]])],
     // lean:AOP.A7_2.greedy@21400acf
  [],

  [#vstep(IFF, [],
    [#grid(columns: 3, align: (right + horizon, center + horizon, left + horizon),
       column-gutter: 6pt, row-gutter: 3pt,
       [`⦇`#frc([`S`])` est(R)⦈`], [`⊑`], [`⦇S⦈`],
       grid.cell(colspan: 3, align: center + horizon)[and],
       [`⦇S⦈°⦇`#frc([`S`])` est(R)⦈`], [`⊑`], [`R°`],
       grid.cell(colspan: 3, align: left + horizon, inset: (top: 3pt))[#src[@est-75 at `⦇S⦈`;
         `⦇`#frc([`S`])` est(R)⦈⊑⦇S⦈°\R°⟺⦇S⦈°⦇`#frc([`S`])` est(R)⦈⊑R°` — @div-laws]])])],
  [],

  [#vstep(IMP, [], [#frc([`S`])` est(R)⊑S` \
    #src[the left conjunct; @est-75, and `⦇−⦈` is monotone]])],
  [],

  [#vstep(IMP, mbp(gterm((mb-S,), (mb-FRo, mb-LamS, mb-est), rhs: (mb-Ro,))),
    [`S°F(R°)(`#frc([`S`])` est(R))⊑R°` \
     #src[the right conjunct; `⦇S⦈°⦇`#frc([`S`])` est(R)⦈` is the least `X` with
      `X=S°F(X)(`#frc([`S`])` est(R))` #h(4pt) #src[@hylo-mu] #h(4pt) — so Knaster–Tarski
      leaves this one inequation] \
     #src[#frc([`S`]) `=` #frc([`𝟙`]) `E(S)` — @adj-E-bend]])],
  // `S°` births the `F` wire and `S` kills it, so `F(R°)` is the `R°` bead INSIDE that span — the
  // relator's action costs no notation.  The unit births the `E` wire, and `est(R)` kills it.
  [#trow(
    tpan(4.0, ((3.45, [`S°`]), (2.45, [`R°`]), (1.45, [`S`]), (0.45, [`est(R)`])),
      hands: ((RXU, 1.95, 0.45, [`E`], frc([`𝟙`])), (GXF, 3.45, 1.45, [`F`])),
      top: ((RXO, [`A`]),), xo: RXO),
    tpanR(4.0, 2.45, [`R°`]),
  )],

  [#vstep(SQ, mbp(gterm((mb-S, mb-R), (mb-LamS, mb-est))),
    [`R°S°(`#frc([`S`])` est(R))` \
     #src[`S°F(R°)⊑R°S°` — @mon-defn at `S`, conversed; `F(R)°=F(R°)` — @relator-laws]])],
  // `R°` leaves the `F` span and lands above `S°`; the three beads that did not move keep their height.
  [#tpan(4.0, ((3.45, [`R°`]), (2.45, [`S°`]), (1.45, [`S`]), (0.45, [`est(R)`])),
    hands: ((RXU, 1.95, 0.45, [`E`], frc([`𝟙`])), (GXF, 2.45, 1.45, [`F`])),
    top: ((RXO, [`A`]),), xo: RXO)],

  [#vstep(SQ, [#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
    (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
  ), seams: (), src: ("A", ), tgt: ("A", )),
  cert: (expect: "R°R°", src: "A", tgt: "A"))],
    [`R°R°` \ #src[`S°(`#frc([`S`])` est(R))⊑S°(S°\R°)⊑R°` — @est-75, @div-laws]])],
  // The collapsed group's bead sits at the middle of the span it replaces.
  [#tpan(4.0, ((3.45, [`R°`]), (1.45, [`R°`])), top: ((RXO, [`A`]),), xo: RXO)],

  [#vstep(SQ, [#cpanel((k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true, src: ("A", ), tgt: ("A", )),
  cert: (expect: "R°", src: "A", tgt: "A"))], [`R°` \ #src[`R` transitive]])],
  [#tpan(4.0, ((2.45, [`R°`]),), top: ((RXO, [`A`]),), xo: RXO)],
))]<greedy-thm72>

// The fork is the bracket's case split `F([A])=𝟏+A×[A]`; `⊸` discards.
#let TAPEEDGE = rgb("#c25b5b")  // circuit.typ's tape edge, which it does not export
#let BRT = 1.6  // the bracket's branch height
#let UIP = 0.4  // the pair's half-height, at the fork and inside the `∪` copies
#let UOP = 0.3  // a `∪` copy's output port
#let UHH = 0.7  // a `∪` copy's half-height
#let UDY = UHH + 0.55  // copy separation, wider than the strands inside one copy
#let UH = UHH + UDY    // the `∪` region's half-height
#let CW = 3.0  // a `∪` copy's width
#let UM = 0.2  // region edge to the deepest box inside a copy — a strand box is taller than a wire
// A `∪` region with arbitrary branch bodies: the pair arrives once, the dashed fan hands it to
// both copies, and their outputs merge (choosebox's geometry, generalised).
#let unionbox(a, b, upper, lower, ip: UIP, op: UOP, hh: UHH) = {
  let cy = (a.at(1) + b.at(1)) / 2
  let dy = hh + 0.55
  let cx = a.at(0) + CHPAD
  let ox = b.at(0) - CHPAD
  let xi = a.at(0) - CHFAN
  let xo = b.at(0) + CHFAN
  let fan = (thickness: lw, paint: black, dash: "dashed")
  tape(a, b)
  lab((a.at(0) + b.at(0)) / 2, b.at(1) + 0.3, TAPEEDGE)[`∪`]
  d.group({ d.translate((cx, cy + dy)); upper })
  d.group({ d.translate((cx, cy - dy)); lower })
  for s in (1, -1) {
    bend((xi, cy + s * ip), (cx, cy + dy + s * ip), stroke: fan)
    bend((xi, cy + s * ip), (cx, cy - dy + s * ip), stroke: fan)
  }
  bend((ox, cy + dy + op), (xo, cy), stroke: fan)
  bend((ox, cy - dy - op), (xo, cy), stroke: fan)
}
// `⊸ X`: both wires discarded, then `X` created.  `w` is the copy's run — the two copies of one `∪`
// have to reach the same edge, and takewhile's `cons` branch is wider than mss's.
#let disc-copy(label, w: CW) = {
  wire((0, UIP), (0.35, UIP)); wiredot((0.35, UIP))
  wire((0, -UIP), (0.35, -UIP)); wiredot((0.35, -UIP))
  gbox((0.6, 0), label, w: 0.75, chamfer: false)
  wire((1.35, 0), (w, UOP))
}
#let cons-copy = {
  gbox((0, 0), [`cons`], w: 1.3, h: 2 * UIP + 0.35, chamfer: false)
  bend((1.3, 0), (CW, -UOP))
}

// ---- takewhile's own circuits.  A box is `(label, width, chamfer)`; the pair is TWO strands, the
// head above and the tail below, so a coreflexive `p` is a box on the head strand alone.
#let TBH = 0.6  // circuit.typ's default box height, which it does not export
#let PBH = 0.5  // a box sitting on ONE strand of the pair, low enough to clear the other
#let twbox(x, y, b, h: PBH) = gbox((x, y), b.at(0), w: b.at(1), h: h, chamfer: b.at(2))
// The `cons` branch of a `∪`: `a` restricts the head and `l` acts on the tail — drawn to one shared
// width so `cons` stays upright — then `cons`, then `post`.  `w` is the copy's run.
#let tw-cons(w, a: none, l: none, post: none, types: false) = {
  let pw = calc.max(if a == none { 0.0 } else { a.at(1) }, if l == none { 0.0 } else { l.at(1) })
  // The fan hands the pair over unlabelled, so `types` says which of the two strands is which; it
  // buys the room for those labels by starting the boxes 0.87 further in — add that to `w` too.
  let lead = if types { 1.15 } else { 0.28 }
  let x = if pw > 0 { lead + 0.28 + pw } else { 0.0 }
  if types { lab(lead / 2, UIP + 0.34, black)[`A`]; lab(lead / 2, -UIP + 0.34, black)[`[A]`] }
  if pw > 0 {
    for (s, b) in ((1, a), (-1, l)) {
      wire((0, s * UIP), (lead, s * UIP))
      if b != none { twbox(lead, s * UIP, b) }
      wire((lead + (if b == none { 0.0 } else { b.at(1) }), s * UIP), (x, s * UIP))
    }
  }
  gbox((x, 0), [`cons`], w: 1.3, h: 2 * UIP + 0.35, chamfer: false)
  let xe = x + 1.3
  if post != none {
    wire((xe, 0), (xe + 0.28, 0))
    twbox(xe + 0.28, 0, post, h: TBH); xe = xe + 0.28 + post.at(1)
  }
  bend((xe, 0), (w, -UOP))
}

// ONE wire while `S` is still inside a division: a run of boxes on it.
// `from`/`mid` are the two type labels the run is not free to guess: @takewhile-laws starts at `[A]`
// rather than `F([A])`, and its cata rows never open `E([A])` at all.
#let twrun(items, from: [`F([A])`], mid: [`E([A])`], mid-at: 0) = {
  lab(-1.1, 0, black, from)
  let x = 0.0
  for (i, b) in items.enumerate() {
    wire((x, 0), (x + 0.34, 0)); twbox(x + 0.34, 0, b, h: TH); x = x + 0.34 + b.at(1)
    if i == mid-at and mid != none {
      // 2.26, not 0.34: `E([A])`'s white fill is 1.94 wide and was painting out both boxes' edges.
      wire((x, 0), (x + 2.26, 0)); node(x + 1.3, 0, black, mid); x = x + 2.26
    }
  }
  wire((x, 0), (x + 0.34, 0)); lab(x + 0.9, 0, black)[`[A]`]
}
#let twp(body, s: 100%) = P(cetz.canvas(length: 0.8cm, body), s: s)

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
// would sit alone at the foot of §13.3's last page.
#pagebreak(weak: true)
=== `takewhile(p)=⦇[nil,(π₁p→cons,⊸ nil)]⦈` <sec-takewhile>

// B&dM Ex 7.39, p. 174.  The derivation runs on `est(R°)` (@est-defn) and the greedy theorem
// (Theorem 7.2), both above it.
// One running example: `A≜Nat` and `p≜even`, fixed by the `p` row and used by every row below it.
#disp[#align(center, block(width: 21cm)[
#table(
  columns: (1.7cm, 5.3cm, 2.9cm, 4.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*type*], [*example*], [*in words*]),

  [`F`], [`FX=𝟏+A×X`], [`𝒜⟶𝒜`], [],
  [nothing, or a head and a tail],

  [`nil`, `cons`], [`[A]::=nil|cons (A,[A])` #h(4pt) #src[@comb-fns]],
  [`𝟏⟶[A]`, #h(4pt) `A×[A]⟶[A]`],
  [`cons(3,[1,2])=[3,1,2]`],
  [the empty list; a head onto a tail],

  [`α`], [`[nil,cons]`], [`F([A])⟶[A]`], [],
  [both constructors as one map],

 [`p`], [a coreflexive #src[]], [`A⟶A`], [`p≜even` #h(4pt) — `2 p 2`, and `3∉Dom(p)`],
  // lean:AOP.A7_7_TakeWhile.pcor@62cb073c
  [`{(a,a)∣a` passes the test`}`],

 [`R`], [`length≤length°`, a preorder #src[]], [`[A]⟶[A]`], [`[1] R [1,2]`],
  // lean:AOP.A7_7_TakeWhile.lenLE@833ff8fc
  [`xs R ys⟺length xs≤length ys`],

  [`⊸ nil`], [the constant `nil` — the second `nil` of `prefix`], [`A×[A]⟶[A]`],
  [`(⊸ nil)(3,[1,2])=nil`],
  [drop the pair, return `nil`],

  [`prefix`], [`⦇[nil,⊸ nil ∪ cons]⦈` #h(4pt) #src[@comb-fns]], [`[A]⟶[A]`],
  [`[3,1,2] prefix [3,1]`],
  [`xs prefix ys⟺∃zs. xs=ys⧺zs` #h(4pt) — at each `cons`, stop or keep the head],

 [`S`], [`[nil,⊸ nil ∪ (p×𝟙) cons]` #src[]], [`F([A])⟶[A]`],
  // lean:AOP.A7_7_TakeWhile.Salg@25dee952
  [`(4,[2]) S [4,2]`, #h(4pt) and `(3,[2]) S nil` only],
  [`prefix`'s algebra with one extra `p` — stop, or keep a head that passes `p`],

  [`(g→X,Y)`], [`X` where `g` is defined and `Y` where it is not], [`A⟶B` #h(4pt) at
   `X`,`Y : A⟶B`], [],
  [the test picks the branch],
)
#v(6pt)
#align(center)[`nil R=⊤`, #h(4pt) `nil R°=nil` #h(4pt) #src[`nil` is the shortest list — below
  every list, and above only itself, so it loses every `est(R°)`]]
])]<takewhile-defn>

#let bx-p = ([`p`], 0.65, true)
// HINZE–MARSDEN (IntroString.pdf §1.4.2), @party-mono-branch's second column at this section's data:
// a wire is a FUNCTOR, a bead an arrow, a region a category, gray `𝟏`.  ONLY the `(p×𝟙) cons` operand
// is drawn — `∪` has no geometry here, and the other operand `⊸ nil` creates a constant and draws
// nothing.  `[A]` is TWO wires, `list` beside `A`: `p : A⟶A` is a bead on the object wire with the
// `list` running past it, and `prefix : [A]⟶[A]` eats that `list` and makes another.
// `prefix`/`subseq` are only LAX natural in `Rel` — `list(p) prefix⊑prefix list(p)` and no more, since
// `list(p)` needs every element to have a `p`-image — so `p` stays strictly below.

// Emitted verbatim by `./scripts/diagram --src "F([A])" --tgt "[A]" "<the row's formula>"`: the
// source IS the generator's output, so a redraw is a re-run of that line and never a hand edit.
// Bead colour is WHICH ARROW: `cons` is the structure map and stays black.
#let tw-pfx1 = dpanel(4, 6.85, 4,
  ((0.55, "top", 3, none, none), (1.7, 2, "bot", none, none), (2.85, "top", 2, none, none)),
  ((3, [`α`], black, 0.55), (2, [`prefix`], black, 2.85), (1, [`p`])),
  ((0.55, [`F`]), (2.85, [`list`]), (4, [`A`])),
  ((1.7, [`list`]), (4, [`A`])),
  cert: (expect: "α prefix list(p)", src: "F([A])", tgt: "[A]"))
#let tw-pfx2 = dpanel(4, 8, 5.15,
  ((0.55, 2, "bot", none, none), (1.7, "top", 2, none, none), (2.85, 3, 2, [`list`], none), (4, "top", 3, none, none)),
  ((3, [`prefix`], black, 4), (2, [`cons`], black, 1.7), (1, [`p`])),
  ((1.7, [`A×−`]), (4, [`list`]), (5.15, [`A`])),
  ((0.55, [`list`]), (5.15, [`A`])),
  opath: ((5.15, 4), (5.15, 3), (2.85, 2), (2.85, 1), (2.85, 0)),
  cert: (expect: "F(prefix)[nil,⊸ nil ∪ cons]list(p)", src: "F([A])", tgt: "[A]", branch: "cons"))
#let tw-pfx3 = dpanel(3, 6.85, 4,
  ((0.55, "top", 1, none, none), (1.7, 2, "bot", none, none), (2.85, "top", 2, none, none)),
  ((2, [`prefix`], black, 2.85), (1, [`(p×list(p))cons`], black, 0.55)),
  ((0.55, [`A×−`]), (2.85, [`list`]), (4, [`A`])),
  ((1.7, [`list`]), (4, [`A`])),
  cert: (expect: "F(prefix)[nil,⊸ nil ∪ (p×list(p)) cons]", src: "F([A])", tgt: "[A]", branch: "cons"))

#disp[#table(
  columns: (1fr, 4.9cm),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`α prefix list(p)=F(prefix list(p))S` \
    #src[building the list and then keeping a `p`-passing prefix of it is keeping one of the tail
     first, and then building with `S`] \
    #src[this same diagram is `subseq`'s: algebra `[nil,π₂ ∪ cons]`, type `[A]⟶[A]`]
    // lean:AOP.A7_7_Filter.filter_alg_comm@d130a86c
    // lean:AOP.A7_7_Filter.filter_alg@5f9648f5
    ],
  table.header([*circuit* — the fork is `F([A])=𝟏+A×[A]`: `nil` above, the pair below],
    [*Hinze–Marsden*]),

  [#vstep([], [#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "box", nin: 2, nout: 1, label: "α", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "list(p)", chamfer: true, frac: false, flip: false),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "α prefix list(p)", src: "F([A])", tgt: "[A]"))],
    [`α prefix list(p)`])],
  [#tw-pfx1 \
    #src[the `cons` branch alone, without `𝟏+` or `⊸ nil`]],

  [#vstep(EQ, [#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "case", nin: 1, nout: 1, bodies: (
        (k: "seq", nin: 1, nout: 1, items: (
            (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
            (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
          ), seams: ()),
        (k: "seq", nin: 1, nout: 1, items: (
            (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
            (k: "stack", nin: 2, nout: 2, lanes: (
                (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
                (k: "seq", nin: 1, nout: 1, items: (
                    (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: false),
                  ), seams: ()),
              )),
            (k: "union", nin: 2, nout: 1, bodies: (
                (k: "seq", nin: 2, nout: 1, items: (
                    (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
                          (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
                        ), seams: ())),
                  ), seams: ()),
                (k: "seq", nin: 2, nout: 1, items: (
                    (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
                  ), seams: ()),
              )),
          ), seams: (
            (
              0,
              ("A", "[A]", ),
            ),
          )),
      )),
    (k: "box", nin: 1, nout: 1, label: "list(p)", chamfer: true, frac: false, flip: false),
  ), seams: (), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "F(prefix) [nil,⊸ nil ∪ cons] list(p)", src: "F([A])", tgt: "[A]"))],
    [`F(prefix) [nil,⊸ nil ∪ cons] list(p)` \ #src[defining equation]])],
  [#tw-pfx2],

  [#vstep(EQ, [#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: false),
              ), seams: ()),
          )),
        (k: "union", nin: 2, nout: 1, bodies: (
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
                      (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
                    ), seams: ())),
              ), seams: ()),
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "stack", nin: 2, nout: 2, lanes: (
                    (k: "seq", nin: 1, nout: 1, items: (
                        (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
                      ), seams: ()),
                    (k: "seq", nin: 1, nout: 1, items: (
                        (k: "box", nin: 1, nout: 1, label: "list(p)", chamfer: true, frac: false, flip: false),
                      ), seams: ()),
                  )),
                (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
              ), seams: ()),
          )),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "F(prefix) [nil,⊸ nil ∪ (p×list(p)) cons]", src: "F([A])", tgt: "[A]"))],
    [`F(prefix) [nil,⊸ nil ∪ (p×list(p)) cons]` \ #src[`list(p)` through `cons`]])],
  [#tw-pfx3],

  [#vstep(EQ, [#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "union", nin: 2, nout: 1, bodies: (
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
                      (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
                    ), seams: ())),
              ), seams: ()),
            (k: "seq", nin: 2, nout: 1, items: (
                (k: "stack", nin: 2, nout: 2, lanes: (
                    (k: "seq", nin: 1, nout: 1, items: (
                        (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
                      ), seams: ()),
                    (k: "seq", nin: 1, nout: 1, items: (
                        (k: "box", nin: 1, nout: 1, label: "prefix", chamfer: true, frac: false, flip: false),
                        (k: "box", nin: 1, nout: 1, label: "list(p)", chamfer: true, frac: false, flip: false),
                      ), seams: ()),
                  )),
                (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
              ), seams: ()),
          )),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,⊸ nil ∪ (p×(prefix list(p))) cons]", src: "F([A])", tgt: "[A]"))],
    [`[nil,⊸ nil ∪ (p×(prefix list(p))) cons]` \ #src[relator, `prefix` entire]])], [],

  [#vstep(EQ, [#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "box", nin: 2, nout: 2, label: "F(prefix list(p))", chamfer: true, frac: false, flip: false),
    (k: "box", nin: 2, nout: 1, label: "S", chamfer: true, frac: false, flip: false),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "F(prefix list(p))S", src: "F([A])", tgt: "[A]"))],
    [`F(prefix list(p))S` \ #src[`prefix list(p)` entire]])], [],
)
#align(center, block(inset: (y: 4pt))[#src[@cata-defining reads that off as `prefix list(p)=⦇S⦈`.
  @cata-fusion cannot: `list(p)` is not entire, `(𝟙×list(p))⊸ nil⊏⊸ nil`, and no algebra meets
 the side condition. ,
  // lean:AOP.A7_7_TakeWhile.takewhile_alg@950e7adb
 ]])
  // lean:AOP.A7_7_TakeWhile.takewhile_alg_comm@4bc81b63
]<takewhile-alg>

// One law to a step: `R°` starts on the tail strand, is copied into both operands of the `∪`,
// dies against `⊸` on one and slides through `cons` on the other, and leaves past the join.
#let step = step.with(pw: 300pt)
#let bx-Ro = ([`R°`], 0.85, true)
#disp[#table(
  columns: (1fr, 6.0cm),
  align: (center + horizon, left + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`(𝟙×R°)(⊸ nil ∪ (p×𝟙) cons)⊑(⊸ nil ∪ (p×𝟙) cons)R°` \
    #src[shortening the tail and then taking the step lands inside taking the step and then
     shortening the result]],
  table.header([*circuit* — the `cons` branch of `F(R°)S⊑SR°`], [*reason*]),

  [#step([])[#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "stack", nin: 2, nout: 2, lanes: (
        (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
        (k: "seq", nin: 1, nout: 1, items: (
            (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
          ), seams: ()),
      )),
    (k: "union", nin: 2, nout: 1, bodies: (
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
                  (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
                ), seams: ())),
          ), seams: ()),
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "stack", nin: 2, nout: 2, lanes: (
                (k: "seq", nin: 1, nout: 1, items: (
                    (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
                  ), seams: ()),
                (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
              )),
            (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
          ), seams: ()),
      )),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(𝟙×R°)(⊸ nil ∪ (p×𝟙) cons)", src: "A×[A]", tgt: "[A]"))][`(𝟙×R°)(⊸ nil ∪ (p×𝟙) cons)`]],
  [],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_cons@ea69a5bc

  [#step(EQ)[#cpanel((k: "union", nin: 2, nout: 1, bodies: (
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
              ), seams: ()),
          )),
        (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ())),
      ), seams: ()),
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
              ), seams: ()),
          )),
        (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(𝟙×R°)⊸ nil ∪ (p×R°) cons", src: "A×[A]", tgt: "[A]"))][`(𝟙×R°)⊸ nil ∪ (p×R°) cons`]],
  [each operand is reached on its own #h(4pt) #src[@adj-all] #h(4pt) — and `(𝟙×R°)(p×𝟙)` is `p`
   and `R°` on the pair's two strands at once],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_fork@cbdcc4d1

  [#step(SQ)[#cpanel((k: "union", nin: 2, nout: 1, bodies: (
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ())),
      ), seams: ()),
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
              ), seams: ()),
          )),
        (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "⊸ nil ∪ (p×R°) cons", src: "A×[A]", tgt: "[A]"))][`⊸ nil ∪ (p×R°) cons`]],
  [`⊸` is the greatest arrow into `𝟏`, so `(𝟙×R°)⊸⊑⊸`],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_disc@6d2514be

  [#step(SQ)[#cpanel((k: "union", nin: 2, nout: 1, bodies: (
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ())),
      ), seams: ()),
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
          )),
        (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "⊸ nil ∪ (p×𝟙) cons R°", src: "A×[A]", tgt: "[A]"))][`⊸ nil ∪ (p×𝟙) cons R°`]],
  [`cons length=(𝟙×length)π₂ succ` with `succ` monotone — a shorter tail makes a shorter list],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_slide@577d240b

  [#step(EQ)[#cpanel((k: "union", nin: 2, nout: 1, bodies: (
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ())),
        (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
      ), seams: ()),
    (k: "seq", nin: 2, nout: 1, items: (
        (k: "stack", nin: 2, nout: 2, lanes: (
            (k: "seq", nin: 1, nout: 1, items: (
                (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
              ), seams: ()),
            (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
          )),
        (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
      ), seams: ()),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "⊸ nil R° ∪ (p×𝟙) cons R°", src: "A×[A]", tgt: "[A]"))][`⊸ nil R° ∪ (p×𝟙) cons R°`]],
  [`nil R°=nil` #h(4pt) #src[@takewhile-defn] #h(4pt) — so the constant branch may carry the `R°`
   the other one already has],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_nil@5635abfd

  [#step(EQ)[#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "union", nin: 2, nout: 1, bodies: (
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "konst", nin: 2, nout: 1, body: (k: "seq", nin: 0, nout: 1, items: (
                  (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
                ), seams: ())),
          ), seams: ()),
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "stack", nin: 2, nout: 2, lanes: (
                (k: "seq", nin: 1, nout: 1, items: (
                    (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
                  ), seams: ()),
                (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
              )),
            (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
          ), seams: ()),
      )),
    (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(⊸ nil ∪ (p×𝟙) cons)R°", src: "A×[A]", tgt: "[A]"))][`(⊸ nil ∪ (p×𝟙) cons)R°`]],
  [one `R°` past the join is the two inside it #h(4pt) #src[@adj-all]],
  // lean:Freyd.S2_20.union_comp_distrib@0025430d
)
#align(center, block(inset: (y: 4pt))[#src[the `nil` branch, which no row above draws, is
  `nil⊑nil R°`.]])
  // lean:AOP.A7_7_TakeWhile.takewhile_mono@69b53bd4
]<takewhile-mono>

// ONE wire while `S` sits inside a division — nothing can be seen into it — then the bracket, once
// the coproduct of maps has opened it.
#let step = step.with(pw: 340pt)
#let bx-est = ([`est(R°)`], 2.2, true)
#let bx-Sd = (frc([`S`]), 1.0, false)
#disp[#table(
  columns: (1fr, 4.4cm),
  align: (center + horizon, left + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[$frac(#[`S`], ∋)$ ` est(R°)=[nil,(π₁p→cons,⊸ nil)]` \
    #src[the longest of the lists the algebra allows is the `cons` where the head passes `p`, and
     `nil` where it does not]],
  table.header([*formula*], [*reason*]),

  // lean:AOP.A4_6.Λ_eq_singleton_existsImage@02b29ea8
  [#step([])[#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(S)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      0,
      ("EF[A]", ),
    ),
    (
      1,
      ("E[A]", ),
    ),
  ), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "S%∋ est(R°)", src: "F([A])", tgt: "[A]"))][$frac(#[`S`], ∋)$ ` est(R°)`]], [],

  [#step(EQ)[#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(nil)", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
      ), seams: (
        (
          1,
          ("E𝟏", ),
        ),
        (
          2,
          ("E[A]", ),
        ),
      )),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(⊸ nil ∪ (p×𝟙) cons)", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
        (
          1,
          ("E(A×[A])", ),
        ),
        (
          2,
          ("E[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil%∋ est(R°),(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]", src: "F([A])", tgt: "[A]"))][`[`$frac(#[`nil`], ∋)$` est(R°),` $frac(#[`⊸ nil ∪ (p×𝟙) cons`], ∋)$` est(R°)]`]],
  [coproduct of maps],

  [#step(EQ)[#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(⊸ nil ∪ (p×𝟙) cons)", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
        (
          1,
          ("E(A×[A])", ),
        ),
        (
          2,
          ("E[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(⊸ nil ∪ (p×𝟙) cons)%∋ est(R°)]", src: "F([A])", tgt: "[A]"))][`[nil,` $frac(#[`⊸ nil ∪ (p×𝟙) cons`], ∋)$` est(R°)]`]],
  [singleton, `R°` reflexive],

  [#step(EQ)[#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "(π₁p→cons,⊸ nil)", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(π₁p→cons,⊸ nil)]", src: "F([A])", tgt: "[A]"))][`[nil,(π₁p→cons,⊸ nil)]`]],
  [`nil R=⊤`],
)
#align(center, block(inset: (y: 4pt))[#src[the set is `{nil}` where `p` fails on the head and
  `{nil,cons(a,xs)}` where it holds, and `nil` loses the second — @est-defn at a two-element set.
 ]])
  // lean:AOP.A7_7_TakeWhile.takewhile_step@60d42a5b
]<takewhile-step>

// B&dM Ex 7.39, p. 174: the specification down to the program, then the three facts that turn the
// greedy `⊒` into the heading's `=`.  Only the last three rows are cited rather than derived.
#let bx-LS = (frc([`⦇S⦈`]), 1.5, false)
// `[A]` is TWO wires, `list` beside `A`, so the object wire is `A` and the `E` the transpose opens
// closes on `list`, the leftmost survivor; `dpan`'s single object wire cannot say either.
#let LPX = (1.05, 2.35, 4.85)                     // `E`, `list`, `A`
#let LPY = (3.55, 2.55, 1.00)                     // the singleton, the arrow, `est(R°)`
// The specification row splits `LPY.at(1)`'s one arrow into two, straddling it, so the row below —
// which collapses them into `⦇S⦈` — puts that bead midway between the pair it replaces.
#let LPYS = (3.05, 2.00)                          // `prefix`/`subseq` above, `p` below
#let LPH = 4.20
// ONE `w` for every row of a display, so `list` and `A` stand in one column down it: a per-row width
// centres each panel on its own label and moves the two wires the chain never touches.
// `sp` lists the `[A]⟶[A]` nodes on the `A` line, top down, as `(y, label)`: the `list` wire bends in
// to each and back out, `A` runs straight through, so the gray's edge stays the rectangle it was.
#let lpan(body: (), w: 11.7, names: false, sp: ()) = P(cetz.canvas(length: 0.8cm, {
  let (XE, XL, XO) = LPX
  d.rect((0, 0), (XO, LPH), fill: fb-ALLC, stroke: none)
  d.rect((XO, 0), (w, LPH), fill: luma(226), stroke: none)
  hm-wire(((XO, LPH), (XO, 0)), col: BCOL)
  lwire(XL, XO, sp.map(n => n.at(0)), LPH, 0)
  for (y, l) in sp { hm-bead((XO, y), l) }
  body
  hm-port((XL, LPH), [`list`]); hm-port((XO, LPH), [`A`], col: BCOL)
  hm-port((XL, 0), [`list`], dir: -1); hm-port((XO, 0), [`A`], dir: -1, col: BCOL)
  if names { hm-name((0.45, 0.30), [`Rel`]); hm-name((XO + 2.8, 0.30), [`𝟏`]) }
}), s: 76%)
// The `E` wire is BORN by the singleton and killed by `est(R°)`, itself a node like any other: `E`
// dies on the `A` line under the `list` wire's own bend, so the two fan in without crossing.
#let epan(body: (), w: 11.7, names: false, sp: ()) = lpan(
  body: {
    dhandle(LPX.at(2), LPX.at(0), LPY.at(0), LPY.at(2), [`E`], born: frc([`𝟙`]))
    body
  },
  w: w, names: names, sp: sp + ((LPY.at(2), [`est(R°)`]),))
// `S` is defined in @takewhile-defn, three pages back, and every row below reads it: the definition
// is repeated here rather than looked up, in that table's own five columns.
#disp[#align(center, block(width: 21cm)[
#table(
  columns: (1.7cm, 5.3cm, 2.9cm, 4.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*type*], [*example*], [*in words*]),

  [`S`], [`[nil,⊸ nil ∪ (p×𝟙) cons]` #h(4pt) #src[@takewhile-defn]], [`F([A])⟶[A]`],
  [`(4,[2]) S [4,2]`, #h(4pt) and `(3,[2]) S nil` only],
  [`prefix`'s algebra with one extra `p` — stop, or keep a head that passes `p`],
)])]

#disp[#pad(right: 10pt, table(
  columns: (1fr, 7.9cm),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`takewhile(p)≜` #frc([`prefix list(p)`]) ` est(R°)=⦇[nil,(π₁p→cons,⊸ nil)]⦈` \
    #src[Ex 7.39: the longest prefix all of whose elements pass `p`.
 ]],
     // lean:AOP.A7_7_TakeWhile.takewhile_eq_cata@3fbff510
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], [#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(prefix list(p))", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      1,
      ("E[A]", ),
    ),
  ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "(prefix list(p))%∋ est(R°)", src: "[A]", tgt: "[A]"))],
    [#frc([`prefix list(p)`]) ` est(R°)` \ #src[the specification — @est-defn's `est(R°)`.
 ]])],
     // lean:AOP.A7_7_TakeWhile.takewhile@6fb798ac
  [#epan(body: hm-bead((LPX.at(2), LPYS.at(1)), [`p`]), sp: ((LPYS.at(0), [`prefix`]),), names: true)],

  [#vstep(EQ, twp(twrun((bx-LS, bx-est), from: [`[A]`]), s: 70%),
 [#frc([`⦇S⦈`]) ` est(R°)` \ #src[@takewhile-alg]])],
    // lean:AOP.A7_7_TakeWhile.takewhile_alg@950e7adb
  [#epan(sp: ((LPY.at(1), [`⦇S⦈`]),))],

  [#vstep(RQ, [#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 2, nout: 1, items: (
      (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
      (k: "box", nin: 1, nout: 1, label: "E(S)", chamfer: false, frac: false, flip: false),
      (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
    ), seams: (
      (
        0,
        ("EF[A]", ),
      ),
      (
        1,
        ("E[A]", ),
      ),
    )), label: none, port: ("A", "[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇S%∋ est(R°)⦈", src: "[A]", tgt: "[A]"))],
    [`⦇`#frc([`S`])` est(R°)⦈` \ #src[@greedy-thm72 at `R°`, with `F(R°)S⊑SR°` — @takewhile-mono —
     for its hypothesis: one longest `p`-prefix kept at each `cons`, instead of every `p`-prefix
 collected and one chosen at the end. ]])],
     // lean:AOP.A7_7_TakeWhile.takewhile_greedy@22f769a1
  [#lpan(sp: ((LPY.at(1), [`⦇`#frc([`S`])` est(R°)⦈`]),))],

  [#vstep(EQ, [#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 1, nout: 1, items: (
      (k: "case", nin: 1, nout: 1, bodies: (
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ()),
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 2, nout: 1, label: "(π₁p→cons,⊸ nil)", chamfer: false, frac: false, flip: false),
            ), seams: (
              (
                0,
                ("A", "[A]", ),
              ),
            )),
        )),
    ), seams: ()), label: none, port: ("F[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇[nil,(π₁p→cons,⊸ nil)]⦈", src: "[A]", tgt: "[A]"))],
 [`⦇[nil,(π₁p→cons,⊸ nil)]⦈` \ #src[@takewhile-step]])],
    // lean:AOP.A7_7_TakeWhile.takewhile_step@60d42a5b
  [#lpan(sp: ((LPY.at(1), [`⦇[nil,(π₁p→cons,⊸ nil)]⦈`]),))],

  [#vstep([], [], [`takewhile(p)° takewhile(p)⊑prefix° prefix∩R∩R°⊑𝟙` \
    #src[`takewhile(p)⊑prefix list(p)` and `(prefix list(p))° takewhile(p)⊑R` — @est-75 at `est(R°)` —
     and two prefixes of one list of equal length are equal, so `takewhile(p)` is simple: *the*
 longest, not *a* longest. ]])],
     // lean:AOP.A7_7_TakeWhile.takewhile_simple@568a360d
  [],

  [#vstep([], [], [#frc([`prefix list(p)`]) ` est(R°)` entire \ #src[`nil` is always a `p`-prefix and
    `R` is connected on the prefixes of one list, so the longest exists.
 ]])],
    // lean:AOP.A7_7_TakeWhile.takewhile_entire@d7c8c6e5
  [],

  [#vstep([], [], [`X⊑Y`, `X` entire, `Y` simple `⟹X=Y` \ #src[`⦇[nil,(π₁p→cons,⊸ nil)]⦈` is a
    reduce of maps, hence entire — what turns the `⊒` above into the heading's `=`.
 ]])],
    // lean:Freyd.S2_10.eq_of_le_entire_simple@e9665c67
  [],
))]<takewhile-laws>

=== `mss=⦇[zero⟨𝟙,`#frc([`𝟙`])`⟩,⟨(𝟙×π₁)⊕,⟨(𝟙×π₁)⊕ `#frc([`𝟙`])`,π₂π₂⟩ cup⟩]⦈ π₂ est(≥)` <sec-mss>

// B&dM Ex 7.40, p. 174–175, whose five staged instructions are the five displays below, mirrored.
// `≤` is on `Int`: over `Nat` every `⊕` would take its right branch and `mss` would be `sum`.
#disp[#definition[
`FX=𝟏+A×X`, #h(4pt) `A:=Int`, #h(4pt) `α≜[nil,cons]`, #h(4pt)
`sum=⦇[zero,plus]⦈` and `segment=suffix prefix` from @cata-examples and @comb-fns.
#h(4pt) #src[]
// lean:AOP.A5_6_ListCombinators.sum_cata@ce1fa8a0

`head≜cons° π₁`, #h(4pt) `wrap≜⟨𝟙,⊸ nil⟩ cons` #h(4pt) #src[the head of a list and the
one-element list, beside @comb-fns's `tail≜cons° π₂`]

`⊕≜` $frac(#[`⊸ zero ∪ plus`], ∋)$ ` est(≥)` #h(4pt) #src[B&dM's `oplus=max(Λ(zero∪plus))`; the
set at `(a,b)` is `{0,a+b}`, so `⊕` is the larger of the two,
]
// lean:AOP.A7_7_MSS.oplus@f61727f6 lean:AOP.A7_7_MSS.oplus_eq@b0466a25
]]<mss-defn>

// ONE WIRE, `[A]` to `A`: this chain never forks, so a row is a run of boxes and the picture's whole
// content is the TYPE the wire carries — where `E(EA)` is born, and which box collapses it again.
// A type sits ON its strand (`node`'s white ground masks the wire): a gap is that white ground (text
// plus its insets) plus a wire stub either side, so the strand visibly runs into each label.  `X/∋`
// and `E(X)` are fractions, hence maps (@pow-laws), so their boxes are square; `est(≥)` is the chain's
// one relation and its only chamfered box.  Widths are measured at the note's text sizes.
#let TH = 1.2   // a fraction box is two lines tall
#let ty-l = ([`[A]`], 1.25)
#let ty-el = ([`E([A])`], 2.0)
#let ty-ea = ([`EA`], 1.0)
#let ty-eea = ([`E(EA)`], 1.75)
#let ty-a = ([`A`], 0.75)
#let bx-mss = (frc([`segment sum`]), 2.2, false)
#let bx-spp = (frc([`suffix (prefix sum)`]), 3.6, false)
#let bx-sf = (frc([`suffix`]), 1.3, false)
#let bx-eps = ([`E(prefix sum)`], 3.5, false)
#let bx-ep = ([`E(`#frc([`prefix sum`])`)`], 2.8, false)
#let bx-un = ([`union`], 1.45, false)
#let bx-est = ([`est(≥)`], 2.0, true)
#let bx-eest = ([`E(est(≥))`], 2.65, false)
#let bx-epest = ([`E(`#frc([`prefix sum`])` est(≥))`], 4.8, false)
#let mss-run(tys, items) = {
  let x = 0.0
  for (i, it) in items.enumerate() {
    let (tl, tw) = tys.at(i)
    wire((x, 0), (x + tw, 0)); node(x + tw / 2, 0, black, tl)
    gbox((x + tw, 0), it.at(0), w: it.at(1), h: TH, chamfer: it.at(2))
    x = x + tw + it.at(1)
  }
  let (tl, tw) = tys.at(items.len())
  wire((x, 0), (x + tw, 0)); node(x + tw / 2, 0, black, tl)
}
#let mss-pic(tys, items, s: 100%) = P(cetz.canvas(length: 0.8cm, mss-run(tys, items)), s: s)

#let step = step.with(pw: 303pt)
#disp[#table(
  columns: (1fr, 4.6cm),
  align: (center + horizon, left + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`segment sum`])` est(≥)=`#frc([`suffix`])` E(`#frc([`prefix sum`])` est(≥)) est(≥)` \
 #src[]],
    // lean:AOP.A7_7_MSS.mss_shape@f600dda0
  table.header([*formula* — one wire from `[A]` to `A`, its type written along it], [*reason*]),

  [#step([])[#mss-pic((ty-l, ty-ea, ty-a), (bx-mss, bx-est))][#frc([`segment sum`])` est(≥)`]], [],

  [#step(EQ)[#mss-pic((ty-l, ty-ea, ty-a), (bx-spp, bx-est))][#frc([`suffix (prefix sum)`])` est(≥)`]],
  [`segment=suffix prefix` \ #src[@comb-fns, @mss-defn]],

  [#step(EQ)[#mss-pic((ty-l, ty-el, ty-ea, ty-a), (bx-sf, bx-eps, bx-est), s: 94%)][#frc([`suffix`])` E(prefix sum) est(≥)`]],
  [absorption \ #src[@pow-laws — `frac(S,∋) E(R)=frac(SR,∋)` at `S:=suffix`, `R:=prefix sum`]],

  [#step(EQ)[#mss-pic((ty-l, ty-el, ty-eea, ty-ea, ty-a), (bx-sf, bx-ep, bx-un, bx-est), s: 95%)][#frc([`suffix`])` E(`#frc([`prefix sum`])`)` \ #h(1em)`union est(≥)`]],
  [#frc([`R`])` ∋=R`, `union=E(∋)` \ #src[@pow-laws's `frac(R,∋)∋=R` at `R:=prefix sum` and
   `E(R)≜frac(∋R,∋)`; @est-laws's `union≜frac(∋∋,∋)`; the middle equality is @relator-defn's
   `F(RS)=F(R)F(S)` at `F:=E`]],

  [#step(EQ)[#mss-pic((ty-l, ty-el, ty-eea, ty-ea, ty-a), (bx-sf, bx-ep, bx-eest, bx-est), s: 85%)][#frc([`suffix`])` E(`#frc([`prefix sum`])`)` \ #h(1em)`E(est(≥)) est(≥)`]],
  [@est-laws, the sets non-empty],

  [#step(EQ)[#mss-pic((ty-l, ty-el, ty-ea, ty-a), (bx-sf, bx-epest, bx-est), s: 92%)][#frc([`suffix`])` E(`#frc([`prefix sum`])` est(≥))` \ #h(1em)`est(≥)`]],
  [relator \ #src[@relator-defn — `F(RS)=F(R)F(S)` at `F:=E`]],
)
#align(center, block(inset: (y: 4pt))[#src[B&dM's `max(P(max(Λ(sum prefix))))Λsuffix`, mirrored. The
  `union` step is @est-laws's `P(est(R)) est(R)=P(Dom(est(R))) union est(R)` — every suffix has the
  empty prefix, so `Dom` is `𝟙` here — and `P(f)=E(f)` at the map it is applied to (@powrel-laws).]])
]<mss-shape>

#let sumplus-copy = {
  wire((0, UIP), (1.55, UIP))
  wire((0, -UIP), (0.5, -UIP)); gbox((0.5, -UIP), [`sum`], w: 0.85, chamfer: false)
  wire((1.35, -UIP), (1.55, -UIP))
  gbox((1.55, 0), [`plus`], w: 0.9, h: 2 * UIP + 0.35, chamfer: false)
  bend((2.45, 0), (CW, -UOP))
}
#let plus-copy = {
  wire((0, UIP), (0.9, UIP)); wire((0, -UIP), (0.9, -UIP))
  gbox((0.9, 0), [`plus`], w: 0.9, h: 2 * UIP + 0.35, chamfer: false)
  bend((1.8, 0), (CW, -UOP))
}
// One row's picture: the bracket forks into the create `c` above and the pair below, whose `∪` the
// `lower` copy closes; `pre` puts `𝟙×sum` before the region, `end` a `sum` box after the join.
#let msspic(c, lower, pre: false, end: none) = {
  let cy = -BRT
  let ux0 = if pre { 3.5 } else { 2.6 }
  let ux1 = ux0 + CW + 2 * CHPAD
  let xo = ux1 + CHFAN
  let xj = xo + 1.05
  tape((0.34, cy - UH - 0.15), (xj, BRT + 0.15))
  wire((0, 0), (0.34, 0))
  let st = (thickness: 1.4pt, paint: TAPEEDGE)
  d.bezier((0.56, 0), (1.26, BRT), (0.98, 0), (0.98, BRT), stroke: st)
  d.bezier((0.56, 0), (1.26, cy + UIP), (0.98, 0), (0.98, cy + UIP), stroke: st)
  d.bezier((0.56, 0), (1.26, cy - UIP), (0.98, 0), (0.98, cy - UIP), stroke: st)
  gbox((1.26, BRT), c, w: 0.75, chamfer: false)
  wire((2.01, BRT), (xj - 0.7, BRT))
  if pre {
    wire((1.26, cy + UIP), (ux0 - CHFAN, cy + UIP))
    wire((1.26, cy - UIP), (1.55, cy - UIP))
    gbox((1.55, cy - UIP), [`sum`], w: 0.85, chamfer: false)
    wire((2.4, cy - UIP), (ux0 - CHFAN, cy - UIP))
  } else {
    wire((1.26, cy + UIP), (ux0 - CHFAN, cy + UIP))
    wire((1.26, cy - UIP), (ux0 - CHFAN, cy - UIP))
  }
  unionbox((ux0, cy - UH), (ux1, cy + UH), disc-copy(c), lower)
  wire((xo, cy), (xj - 0.7, cy))
  tape-join((xj, 0), sp: BRT, len: 0.7)
  wire((xj, 0), (xj + 0.34, 0))
  if end != none {
    gbox((xj + 0.44, 0), end, w: 0.95, chamfer: false)
    wire((xj + 1.39, 0), (xj + 1.73, 0))
    lab(xj + 2.15, 0, black)[`A`]
  } else {
    lab(xj + 0.8, 0, black)[`A`]
  }
  lab(-1.3, cy + UIP, black)[`A`]; lab(-1.3, cy - UIP, black)[`[A]`]
}
// §13.3.4's Hinze–Marsden lanes (IntroString.pdf §1.4.2), read left to right as the panel is drawn:
// `MA` is always the leftmost wire and the object wire is whichever the panel ends on.  `MLW` is one
// lane — the room two port labels need side by side.  `[A]` is the `list` wire BESIDE the `A` wire.
#let MLW = 1.25
#let MA = 0.55
#let MB = MA + MLW
#let MC = MB + MLW
#let MD = MC + MLW
// A BEAD OFF THE OBJECT WIRE writes its label at the object wire's x all the same: the labels then
// read as one column, and none of them crosses the wires standing between it and its own dot.
// `hands` is a relator wire born at `(x0,y0)` — free in its own lane, or on the wire carrying `b` —
// running down lane `xe` and dying at `(x1,y1)`; `wires` are the lanes that run the whole height.
// A node on the object wire at `y` that a lane outside `xin` opened; lanes INSIDE it detour through
// it.  A hand born ON the object wire is one; a unit, whose source is `Id`, floats in its own lane.
// Bound outside the drawing so the scan line is handed the nodes that DREW, not the argument alone.
// `hdx` is the hand's name offset FROM its lane: a one-letter functor fits left of it, a wide one
// like `list` would cross its own wire there and goes right, into the gap before the object wire.
// A WIDENING is not a functor lane: the object wire opens into `outer` beside `inner` and closes
// again with no bead, so the scan reads it as `tw-hm`'s split — one record per bead it brackets.
#let mpan(xo, w, top, bot, beads: (), joins: (), hands: (), widen: (), wires: (), nodes: (), h: 4.3,
    hdx: -0.32, cert: (:)) = {
  let ns = nodes + hands.filter(hd => hd.at(6) != none and hd.at(0) == xo).map(hd => (hd.at(1), hd.at(2)))
  let splits = ()
  for (y0, y1, x, outer, ofs) in widen {
    let ys = (y0,) + beads.filter(b => b.at(0) == xo and y1 < b.at(1) and b.at(1) < y0)
      .map(b => b.at(1)).sorted().rev() + (y1,)
    for i in range(ofs.len()) {
      splits.push((ys.at(i), ys.at(i + 1), x, ofs.at(i).at(0), outer, ofs.at(i).at(1)))
    }
  }
  dpan(h, w, xo, {
  let at(x, ylo) = ns.filter(n => n.at(1) < x and n.at(0) > ylo).map(n => n.at(0))
  for x in wires { lwire(x, xo, at(x, 0), h, 0, k: 0.35) }
  for (xf, xt, y, k) in joins {
    hm-wire(((xf, h),) + nodepts(xf, xo, at(xf, y), k: 0.35) + ((xf, y + k), (xt, y)))
  }
  for (x0, y0, xe, x1, y1, l, b) in hands {
    hm-wire(((x0, y0), (xe, y0 - DKN), (xe, y1 + DKN), (x1, y1)))
    hm-name((xe + hdx, (y0 + y1) / 2), l)
    if b != none { hm-bead((x0, y0), b, dx: xo - x0 + 0.32) }
  }
  for (y0, y1, x, outer, ofs) in widen {
    hm-wire(((xo, y0), (x, y0 - DKN), (x, y1 + DKN), (xo, y1)))
    hm-name((x + hdx, (y0 + y1) / 2), outer)
  }
  for (x, y, l) in beads { hm-bead((x, y), l, dx: xo - x + 0.32) }
  for (x, l) in top { hm-port((x, h), l, col: if x == xo { BCOL } else { black }) }
  for (x, l) in bot { hm-port((x, 0), l, dir: -1, col: if x == xo { BCOL } else { black }) }
  }, s: 100%)
  hm-meta((helper: "mpan", h: h, w: w, xo: xo, cert: cert,
    beads: beads.map(b => b.map(plain)), joins: joins.map(j => j.map(plain)),
    hands: hands.map(hd => hd.map(plain)), wires: wires.map(plain),
    splits: splits.map(s => s.map(plain)), nodes: ns.map(n => n.map(plain)),
    top: top.map(p => p.map(plain)), bot: bot.map(p => p.map(plain))))
}
#let mtop3 = ((MA, [`A×−`]), (MB, [`list`]), (MC, [`A`]))

// §13.3.4's generated panels, emitted verbatim by `./scripts/diagram --src … --tgt … "<formula>"`: a
// bracket is cut to ONE branch, which the `cert:` names, and the bead wears that branch's name.
#let mh-cons-sum = dpanel(3, 6.85, 4,
  ((0.55, 2, 1, [`list`], none), (1.7, "top", 2, none, none), (2.85, "top", 2, none, none)),
  ((2, [`cons`], black, 1.7), (1, [`sum`], black, 0.55)),
  ((1.7, [`A×−`]), (2.85, [`list`]), (4, [`A`])),
  ((4, [`A`]),),
  opath: ((4, 3), (2.85, 2), (0.55, 1), (0.55, 0)),
  cert: (expect: "cons sum", src: "A×list(A)", tgt: "A"))
#let mh-alg-est = dpanel(4, 5.7, 2.85,
  ((0.55, 2.5, 1, [`E`], frc([`𝟙`])), (1.7, "top", 2, none, none)),
  ((2, [`zero`], black, 1.7), (1, [`est(≥)`], black, 0.55)),
  ((1.7, [`𝟏`]), (2.85, [`Int`])),
  ((2.85, [`Int`]),),
  opath: ((2.85, 4), (2.85, 2), (0.55, 1), (0.55, 0)),
  cert: (expect: "𝟙%∋ E([zero,⊸ zero ∪ plus])est(≥)", src: "F(Int)", tgt: "Int", branch: "zero"))
#let mh-alg = dpanel(2, 4.55, 1.7,
  ((0.55, "top", 1, none, none),),
  ((1, [`zero`], black, 0.55),),
  ((0.55, [`𝟏`]), (1.7, [`Int`])),
  ((1.7, [`Int`]),),
  cert: (expect: "[zero,⊕]", src: "F(Int)", tgt: "Int", branch: "zero"))
#let mh-segsum = dpanel(5, 6.85, 4,
  ((0.55, 3.5, 1, [`E`], frc([`𝟙`])), (1.7, 3, 2, [`list`], none), (2.85, "top", 3, none, none)),
  ((3, [`segment`], black, 2.85), (2, [`sum`], black, 1.7), (1, [`est(≥)`], black, 0.55)),
  ((2.85, [`list`]), (4, [`A`])),
  ((4, [`A`]),),
  opath: ((4, 5), (4, 3), (1.7, 2), (1.7, 1), (1.7, 0)),
  cert: (expect: "𝟙%∋ E(segment sum)est(≥)", src: "list(A)", tgt: "A"))
#let mh-greedy = dpanel(5, 6.85, 4,
  ((0.55, 3.5, 1, [`E`], frc([`𝟙`])), (1.7, 3, 2, [`list`], none), (2.85, "top", 3, none, none)),
  ((3, [`suffix`], black, 2.85), (2, [`⦇[zero,⊕]⦈`], black, 1.7), (1, [`est(≥)`], black, 0.55)),
  ((2.85, [`list`]), (4, [`A`])),
  ((4, [`A`]),),
  opath: ((4, 5), (4, 3), (1.7, 2), (1.7, 1), (1.7, 0)),
  cert: (expect: "𝟙%∋ E(suffix)E(⦇[zero,⊕]⦈)est(≥)", src: "list(A)", tgt: "A"))
#let mh-shape = dpanel(8, 9.15, 6.3,
  ((0.55, 6.5, 1, [`E`], frc([`𝟙`])), (1.7, 4.5, 2, [`E`], frc([`𝟙`])), (2.85, 4, 3, [`list`], none), (4, 6, 4, [`list`], none), (5.15, "top", 6, none, none)),
  ((6, [`suffix`], black, 5.15), (4, [`prefix`], black, 4), (3, [`sum`], black, 2.85), (2, [`est(≥)`], black, 1.7), (1, [`est(≥)`], black, 0.55)),
  ((5.15, [`list`]), (6.3, [`A`])),
  ((6.3, [`A`]),),
  opath: ((6.3, 8), (6.3, 6), (4, 4), (4, 3), (1.7, 2), (1.7, 1), (1.7, 0)),
  cert: (expect: "𝟙%∋ E(suffix)E(𝟙%∋)E(E(prefix sum))E(est(≥))est(≥)", src: "list(A)", tgt: "A"))

// HINZE–MARSDEN: `[A]` is `list` beside `A`, so `cons` kills the base functor's `A×−` onto the `list`
// wire and `sum` kills `list` onto `A`.  `∪` has no shape here — only `cons`'s branch is drawn.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt),
  stroke: 0.4pt + luma(190),
  Thm[`[nil,⊸ nil ∪ cons] sum=F(sum)[zero,⊸ zero ∪ plus]`],
  table.header([*circuit* — the fork is the bracket's case split `F([A])=𝟙+A×[A]`: `nil` above, the pair and its `∪` below], [*Hinze–Marsden*]),

  // `sum` keeps ONE height down the column: what the fusion moves is the algebra bead, from below
  // `sum` to above it, and the join it rides is drawn with the same knee angle both times.
  [#vstep([], P(cetz.canvas(length: 0.8cm, msspic([`nil`], cons-copy, end: [`sum`]))),
    [`[nil,⊸ nil ∪ cons] sum`])],
  [#mh-cons-sum],

  [#vstep(EQ, P(cetz.canvas(length: 0.8cm, msspic([`nil`], cons-copy, end: [`sum`]))),
    [`[nil sum,⊸ nil sum∪cons sum]` \ #src[coproduct of maps, composition over `∪`]])],
  // Empty: composing `sum` into each branch is re-bracketing, which draws the row above again.
  [],

  [#vstep(EQ, P(cetz.canvas(length: 0.8cm, msspic([`zero`], sumplus-copy))),
    [`[zero,⊸ zero ∪ (𝟙×sum) plus]` \ #src[`sum`'s defining equation]])],
  [#mpan(MC, 5.2, mtop3, ((MC, [`A`]),),
    joins: ((MB, MC, 1.90, 0.60), (MA, MC, 0.80, 1.40)),
    beads: ((MC, 1.90, [`sum`]), (MC, 0.80, [`plus`])))],

  [#vstep(EQ, P(cetz.canvas(length: 0.8cm, msspic([`zero`], plus-copy, pre: true))),
    [`[zero,(𝟙×sum)(⊸ zero ∪ plus)]` \ #src[`(𝟙×sum)⊸=⊸`, `sum` entire]])],
  // Empty: the last two steps rewrite the bracket and the `⊸ zero` branch, and leave the drawn
  // `(𝟙×sum)plus` exactly as the row above has it.
  [],

  [#vstep(EQ, P(cetz.canvas(length: 0.8cm, msspic([`zero`], plus-copy, pre: true))),
    [`F(sum) [zero,⊸ zero ∪ plus]` \ #src[relator]])],
  [],
))
#align(center, block(inset: (y: 4pt))[#src[@cata-fusion at `α`#sub[`B`]` :=[nil,⊸ nil ∪ cons]`,
  `S:=sum`: the side condition, so `prefix sum=⦇[zero,⊸ zero ∪ plus]⦈`. `prefix` is the
  reduce, `sum` the map fused into it — the intermediate list is gone.
 ]])
  // lean:AOP.A7_7_MSS.mss_prefix_sum@001a3374
]<mss-prefix-sum>

// The `∪` is `choosebox`'s tape, which itself cannot be reused: it writes `π₁`/`π₂`
// beside its two branches, and here each branch carries a circuit of its own and wants no label.
#import "circuit.typ": TAPEEDGE
#let MIY = 0.5           // `A×Int` is TWO strands: the head above, the running sum below
#let GEQ = 0.9           // the `≥` box — an order, not a map, so it keeps its chamfer
#let MPRE = GEQ + 0.4    // `𝟙×≥` in front of a branch: the head runs straight past it

#let mtape(a, b, upper, lower) = {
  let cy = (a.at(1) + b.at(1)) / 2
  let dy = MIY + 0.9
  let (cx, ox) = (a.at(0) + CHPAD, b.at(0) - CHPAD)
  let (xi, xo) = (a.at(0) - CHFAN, b.at(0) + CHFAN)
  let fan(c) = (thickness: lw, paint: c, dash: "dashed")
  tape(a, b)
  lab((a.at(0) + b.at(0)) / 2, b.at(1) + 0.32, TAPEEDGE)[`∪`]
  upper(cx, cy + dy); lower(cx, cy - dy)
  for s in (1, -1) {
    bend((xi, cy + s * MIY), (cx, cy + dy + s * MIY), stroke: fan(GIVEN1))
    bend((xi, cy + s * MIY), (cx, cy - dy + s * MIY), stroke: fan(GIVEN2))
  }
  bend((ox, cy + dy), (xo, cy), stroke: fan(GIVEN1))
  bend((ox, cy - dy), (xo, cy), stroke: fan(GIVEN2))
}

// `⊸ zero`: BOTH strands are discarded and `zero : 𝕀⟶Int` starts a new one — a box with nothing on
// its left IS a state, which is what the unit `𝕀` looks like when it costs no wire.
#let bzero(x, y, w) = {
  for s in (1, -1) { wire((x, y + s * MIY), (x + 0.5, y + s * MIY)); wiredot((x + 0.5, y + s * MIY)) }
  gbox((x + 0.9, y), [`zero`], w: 1.3, chamfer: false)
  wire((x + 2.2, y), (x + w, y))
}
// `plus` reads both strands and leaves on one; it is a map, so no chamfer.
#let bplus(x, y, w) = {
  for s in (1, -1) { wire((x, y + s * MIY), (x + 0.34, y + s * MIY)) }
  gbox((x + 0.34, y), [`plus`], w: 1.3, h: 2 * MIY + 0.5, chamfer: false)
  wire((x + 1.64, y), (x + w, y))
}
// A branch of the tape, drawn in the coordinates `mtape` hands it; `w` is the body's run, set per
// row so BOTH branches end at the region's edge whatever they carry.
#let mbranch(body, w, pre: false, post: false) = (x, y) => {
  if pre {
    wire((x, y + MIY), (x + MPRE, y + MIY))
    wire((x, y - MIY), (x + 0.2, y - MIY)); gbox((x + 0.2, y - MIY), [`≥`], w: GEQ)
    wire((x + 0.2 + GEQ, y - MIY), (x + MPRE, y - MIY))
  }
  let x0 = x + (if pre { MPRE } else { 0 })
  body(x0, y, w)
  if post { gbox((x0 + w, y), [`≥`], w: GEQ); wire((x0 + w + GEQ, y), (x0 + w + GEQ + 0.3, y)) }
}
// One row: the pair arrives on two strands, takes one branch of the `∪`, and leaves on one.
#let mrow(upper, lower, W, pre: false, post: false) = {
  let x0 = if pre { 2.6 } else { 1.6 }
  let x1 = x0 + W + 2 * CHPAD
  mtape((x0, -2.55), (x1, 2.55), upper, lower)
  lab(-0.45, MIY, black)[`A`]; lab(-0.62, -MIY, black)[`Int`]
  wire((0, MIY), (x0 - CHFAN, MIY))
  if pre {
    wire((0, -MIY), (0.4, -MIY)); gbox((0.4, -MIY), [`≥`], w: GEQ)
    wire((0.4 + GEQ, -MIY), (x0 - CHFAN, -MIY))
  } else { wire((0, -MIY), (x0 - CHFAN, -MIY)) }
  let xe = x1 + CHFAN
  if post {
    wire((xe, 0), (xe + 0.3, 0)); gbox((xe + 0.3, 0), [`≥`], w: GEQ)
    wire((xe + 0.3 + GEQ, 0), (xe + 0.6 + GEQ, 0)); lab(xe + 1.15 + GEQ, 0, black)[`Int`]
  } else { wire((xe, 0), (xe + 0.4, 0)); lab(xe + 0.95, 0, black)[`Int`] }
}
#let mss-pic(body) = P(cetz.canvas(length: 0.8cm, body), s: 88%)

// HINZE–MARSDEN: the drawn branch is `plus`'s, so `A×−` is the functor wire and `Int` the object
// one; `𝟙×≥` is `F(≥)`, the `≥` bead with `A×−` running past it, and the join stays put while it moves.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`(𝟙×≥)(⊸ zero ∪ plus)⊑(⊸ zero ∪ plus)≥` \ #src[the `plus` branch of `F(≥)S⊑S≥`; the `zero`
 branch is `zero⊑zero≥`]],
    // lean:AOP.A7_7_MSS.mss_mono@d2c09a73
  table.header([*circuit* — the head above, the running sum below; the tape is the `∪`],
    [*Hinze–Marsden*]),

  [#vstep([], mss-pic(mrow(mbranch(bzero, 2.6), mbranch(bplus, 2.6), 2.6, pre: true)),
    [`(𝟙×≥)(⊸ zero ∪ plus)`])],
  [#mpan(MB, 4.2, ((MA, [`A×−`]), (MB, [`Int`])), ((MB, [`Int`]),),
    joins: ((MA, MB, 1.90, 1.20),),
    beads: ((MB, 3.00, [`≥`]), (MB, 1.90, [`plus`])))],

  [#vstep(EQ, mss-pic(mrow(mbranch(bzero, 2.6, pre: true), mbranch(bplus, 2.6, pre: true), 3.9)),
    [`(𝟙×≥)⊸ zero ∪ (𝟙×≥) plus` \ #src[relator, composition over `∪`]])],
  // Empty: `∪` is an operation on hom-sets, not a wiring, so distributing over it draws the row above.
  [],

  [#vstep(SQ, mss-pic(mrow(mbranch(bzero, 3.8), mbranch(bplus, 2.6, post: true), 3.8)),
    [`⊸ zero ∪ plus≥` \ #src[@dom-slide, `(≥×≥) plus⊑plus≥`; `(≤×≤) plus⊑plus≤` is @mon-defn,
     written `+` there, and `plus` is a map, so it is monotonic on an order and on its opposite
     together, which carries it to `≥`.]])],
  [#mpan(MB, 4.2, ((MA, [`A×−`]), (MB, [`Int`])), ((MB, [`Int`]),),
    joins: ((MA, MB, 1.90, 1.20),),
    beads: ((MB, 1.90, [`plus`]), (MB, 0.80, [`≥`])))],

  [#vstep(SQ, mss-pic(mrow(mbranch(bzero, 2.6), mbranch(bplus, 2.6), 2.6, post: true)),
    [`(⊸ zero ∪ plus)≥` \ #src[`≥` reflexive]])],
  // Empty: `≥` is put back on the `⊸ zero` branch, which this column does not draw.
  [],
))]<mss-mono>

// Every row is ONE WIRE, `𝟏+A×Int` to `Int` — `F(Int)` with `A:=Int` — so its two ends are drawn once.
#let mss-src = { lab(-1.62, 0, black)[`𝟏+A×Int`]; wire((-0.45, 0), (0, 0)) }
#let mss-tgt(x) = lab(x + 0.62, 0, black)[`Int`]
// Every `R/∋` is a MAP (@pow-laws), so a fraction box is square; `est(≥)` is partial — no greatest of
// the empty set — and is the one chamfered box here.  `h` is shared down a run: a fraction is two lines.
#let mss-est = ([`est(≥)`], 2.1, true)
#let mss-alg = $frac(#[`[zero,⊸ zero ∪ plus]`], ∋)$
#let mss-zero = $frac(#[`zero`], ∋)$
#let mss-plus = $frac(#[`⊸ zero ∪ plus`], ∋)$
#let mss-run(items, h: 0.6) = { mss-src; boxrun(0, 0, items, h: h); mss-tgt(boxrun-w(items)) }
// @coprod-laws' tape at this algebra: `[X,Y]` is ONE BRANCH PER SUMMAND, each opening with the
// injection's converse — `𝟏` above, `A×Int` below.  The shorter branch is padded to the same join.
#let mss-tape(up, dn, h: 0.6, y: 1.35) = {
  let hh = y + h / 2 + 0.45
  let xr = 2.18 + calc.max(boxrun-w(up), boxrun-w(dn)) + 1.2
  mss-src; wire((0, 0), (0.34, 0))
  tape((0.34, -hh), (xr, hh))
  tape-fork((0.56, 0), sp: y, len: 0.7)
  for (s, inj, run) in ((1, [`l`], up), (-1, [`r`], dn)) {
    gbox((1.26, s * y), inj, flip: true, fill: TINT)
    boxrun(2.18, s * y, run, h: h)
    wire((2.18 + boxrun-w(run), s * y), (xr - 1.0, s * y))
  }
  tape-join((xr - 0.3, 0), sp: y, len: 0.7)
  wire((xr, 0), (xr + 0.34, 0)); mss-tgt(xr + 0.34)
}
#let mss-pic(body) = P(cetz.canvas(length: 0.8cm, body), s: 78%)

// HINZE–MARSDEN: the WHOLE algebra is one bead here, so `F` is its wire and joins the object wire
// there; #frc([`S`]) `=` #frc([`𝟙`]) `E(S)` (@adj-E-bend) births the `E` the last row has no more.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
 Thm[#mss-alg ` est(≥)=[zero,⊕]` \ #src[]],
  // lean:AOP.A7_7_MSS.mss_step@ba23320b
  table.header([*circuit* — the tape is the coproduct: `zero`'s branch above, `plus`'s below],
    [*Hinze–Marsden*]),

  [#vstep([], mss-pic(mss-run(((mss-alg, 5.4, false), mss-est), h: 1.25)), [#mss-alg ` est(≥)`])],
  [#mh-alg-est],

  [#vstep(EQ, mss-pic(mss-tape(((mss-zero, 1.35, false), mss-est), ((mss-plus, 3.4, false), mss-est), h: 1.25)),
    [`[`#mss-zero` est(≥),` #mss-plus ` est(≥)]` \ #src[coproduct of maps — @coprod-calc at
     `T:=[zero,⊸ zero ∪ plus]`, then `[U,V]Z=[UZ,VZ]` — @coprod-laws, composition over `∪`]])],
  // Empty: `[U,V]` is a coproduct of hom-sets, so splitting the bead into branches is not a wiring.
  [],

  [#vstep(EQ, mss-pic(mss-tape((([`zero`], 1.3, false),), (([`⊕`], 0.9, false),))), [`[zero,⊕]`
    \ #src[singleton, `≥` reflexive — @est-laws's $frac(#[`𝟙`], ∋)$ `est(R)=𝟙∩R` at `R:=≥`, `zero` a
    map; the lower branch is `⊕`'s definition, @mss-defn, and no law]])],
  [#mh-alg],
))
#align(center, block(inset: (y: 4pt))[#src[with @mss-mono the greedy theorem gives
  `⦇[zero,⊕]⦈⊑` $frac(#[`prefix sum`], ∋)$ ` est(≥)` — B&dM's own containment — and @mss-deriv
 makes it an equality. ]])
  // lean:AOP.A7_7_MSS.mss_greedy@7547c0f9
]<mss-step>

// B&dM Ex 7.40's last stage, in the power object: @cata-defining's equation for the pair whose
// components are `k`'s two output wires.  No circuit — the carrier is a PRODUCT, and a fork needs
// the product bifunctor, which is not a wire (as in @subseq-EW-join's Hinze-Marsden column).
#disp[#pad(right: 10pt, table(
  columns: (1.5fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`[nil,cons]⟨g,`#frc([`suffix`])` E(g)⟩=F(⟨g,`#frc([`suffix`])` E(g)⟩)k` \
    #src[`k≜[zero⟨𝟙,`#frc([`𝟙`])`⟩,⟨w,⟨w `#frc([`𝟙`])`,π₂π₂⟩ cup⟩]`, `w≜(𝟙×π₁)⊕`: the value at the
     whole list, paired with the set of the values at its suffixes, runs `k`'s recursion.
 ]],
     // lean:AOP.A7_7_MSS.Kalg@206c4ecd lean:AOP.A7_7_MSS.scanStep_union@ca4b2850
  table.header([*the equation at that branch*], [*why*]),

  [`nil⟨g,`#frc([`suffix`])` E(g)⟩=zero⟨𝟙,`#frc([`𝟙`])`⟩`],
  [#src[`nil` has one suffix, itself, and `g nil=zero`, so the set is the singleton `{zero}`]],

  [`cons⟨g,`#frc([`suffix`])` E(g)⟩=(𝟙×⟨g,`#frc([`suffix`])` E(g)⟩)⟨w,⟨w `#frc([`𝟙`])`,π₂π₂⟩ cup⟩`],
  [#src[`g(cons(a,x))=a⊕(g x)`, which is `w` reading `g x` off `π₁`; and the suffixes of
   `cons(a,x)` are `cons(a,x)` itself, whose value is that same `w`, together with those of `x`,
   which `π₂π₂` carries — so the two sets meet at `cup`]],
))]<mss-scan>

// B&dM Ex 7.40, p. 174–175: the four stages above, run as one chain from the specification down to
// the fold.  `g≜⦇[zero,⊕]⦈` throughout, as @mss-scan's `g`.
#let bx-Eg = ([`E(⦇[zero,⊕]⦈)`], 3.6, false)
#let bx-fold = ([`⦇k⦈`], 1.5, false)
#let bx-p2 = ([`π₂`], 1.0, false)
// Every row runs `[A]` to `A`, so the ends are drawn once.  @mss-shape's helper writes the TYPE
// along the wire, which is that display's content; here what changes is the boxes.
// The Hinze–Marsden column counts `[A]` out as the `list` wire beside the `A` wire, and every row's
// two ends are the same, so the ports are bound once too.
#let mtopL = ((MC, [`list`]), (MD, [`A`]))
#let mbotL = ((MD, [`A`]),)
#let mss-line(items) = {
  lab(-0.62, 0, black)[`[A]`]; boxrun(0, 0, items, h: TH)
  lab(boxrun-w(items) + 0.55, 0, black)[`A`]
}
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`mss=⦇k⦈ π₂ est(≥)` \
    #src[Ex 7.40, `⊕≜` #frc([`⊸ zero ∪ plus`]) ` est(≥)` — @mss-defn; `k` and `w` — @mss-scan.
 ]],
    // lean:AOP.A7_7_MSS.mss_eq_scan@d283eef8
  table.header([*circuit*], [*Hinze–Marsden*]),

  // #frc([`R`]) `=` #frc([`𝟙`]) `E(R)` (@adj-E-bend): the singleton BIRTHS the `E` and `est(≥)` KILLS
  // it, so no bead here carries a `%∋`.  One height per bead down the column, and a row that
  // collapses a pair puts its one bead midway between the two it replaces.
  [#vstep([], [#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(segment sum)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(≥)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      0,
      ("E[A]", ),
    ),
    (
      1,
      ("EA", ),
    ),
  ), src: ("[A]", ), tgt: ("A", )),
  cert: (expect: "(segment sum)%∋ est(≥)", src: "[A]", tgt: "A"))],
    [#frc([`segment sum`]) ` est(≥)` \
     #src[`mss` is the greatest of the segment sums — @mss-defn]])],
  [#mh-segsum],

  [#vstep(EQ, [#cpanel((k: "seq", nin: 1, nout: 1, items: (
    (k: "box", nin: 1, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(suffix)", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "E(𝟙%∋ E(prefix sum)est(≥))", chamfer: false, frac: false, flip: false),
    (k: "box", nin: 1, nout: 1, label: "est(≥)", chamfer: true, frac: false, flip: false),
  ), seams: (
    (
      1,
      ("E[A]", ),
    ),
    (
      2,
      ("EA", ),
    ),
  ), src: ("[A]", ), tgt: ("A", )),
  cert: (expect: "suffix%∋ E((prefix sum)%∋ est(≥))est(≥)", src: "[A]", tgt: "A"))],
    [#src[@mss-shape]])],
  // `suffix` is only LAX natural in `Rel`, so it is a NODE on the object wire like the rest; the outer
  // `E` runs past it, and `prefix sum` is where the `list` wire dies.
  [#mh-shape],

  [#vstep(EQ, mbp(mss-line((bx-sf, bx-Eg, bx-est))),
    [#frc([`suffix`]) ` E(⦇[zero,⊕]⦈) est(≥)` \
     #src[the greedy theorem @greedy-thm72 at `R:=≥`, `S:=[zero,⊸ zero ∪ plus]` — @mss-mono is its
      condition and @mss-step its #frc([`S`]) ` est(≥)`; its `⊑` is an `=` because `⦇[zero,⊕]⦈` is
      entire and #frc([`prefix sum`]) ` est(≥)` simple #src[@takewhile-laws's last row]]])],
  [#mh-greedy],

  [#vstep(EQ, mbp(mss-line((bx-fold, bx-p2, bx-est))),
    [`⦇k⦈ π₂ est(≥)` \
     #src[@cata-defining at @mss-scan's equation, so `⦇k⦈=⟨⦇[zero,⊕]⦈,`#frc([`suffix`])
      ` E(⦇[zero,⊕]⦈)⟩`, of which `π₂` is the row above]])],
  // ONE bead: the fold kills `list` and `π₂` opens the `E`, and the pair they hand across is a
  // product, which is not a wire.
  [#mpan(MD, 7.6, mtopL, mbotL, h: 4.8,
    hands: ((MD, 3.00, MA, MD, 0.45, [`E`], none),),
    joins: ((MC, MD, 3.00, 0.90),),
    beads: ((MD, 3.00, [`⦇k⦈π₂`]), (MD, 0.45, [`est(≥)`])))],
))
#align(center, block(inset: (y: 4pt))[#src[one fold builds the `n+1` running maxima and the final
  `est(≥)` reads them in one more pass, so `mss` is linear.]])
]<mss-deriv>

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
// would sit alone at the foot of @mss-deriv's page.
#pagebreak(weak: true)
=== `filter(p)=⦇[nil,(π₁p→cons,π₂)]⦈` <sec-filter>

// B&dM Ex 7.41, p. 174.  @sec-takewhile with `subseq` for `prefix`: same `F`, `α`, `p`, `R`, same
// greedy theorem, and only the second branch of the algebra differs.
// One running example, as @takewhile-defn's: `A≜Nat` and `p≜even`.
#disp[#align(center, block(width: 21cm)[
#table(
  columns: (1.7cm, 5.3cm, 2.9cm, 4.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*type*], [*example*], [*in words*]),

  [`F`, `α`, `p`, `R`], [as in @takewhile-defn], [], [], [],

  [`π₂`], [`π₂` where @takewhile-defn has `⊸ nil`], [`A×[A]⟶[A]`], [`π₂(3,[1,2])=[1,2]`],
  [drop the head, keep the tail],

  [`subseq`], [`⦇[nil,π₂ ∪ cons]⦈` #h(4pt) #src[@comb-fns]], [`[A]⟶[A]`],
  [`[3,1,2] subseq [3,2]`],
  [`xs subseq ys⟺ys` is `xs` with elements dropped #h(4pt) — at each `cons`, drop the head or
   keep it],

 [`S`], [`[nil,π₂∪(p×𝟙) cons]` #h(4pt) #src[]], [`F([A])⟶[A]`],
  // lean:AOP.A7_7_Filter.Salg@dfbf37e0
  [`(4,[2]) S [2]` #h(4pt) and #h(4pt) `(4,[2]) S [4,2]`, #h(4pt) but `(3,[2]) S [2]` only],
  [`subseq`'s algebra with one extra `p` — drop the head, or keep a head that passes `p`],

 [`𝟙⊑π₂R cons°` #h(4pt) #src[]], [], [], [],
  // lean:AOP.A7_7_Filter.id_le_pi2_lenLE_cons@f9fd4c82
  [the tail is one shorter than the cons, so `π₂` loses the `est(R°)` at every step — where
   @takewhile-defn's loser is `nil`],
)
])]<filter-defn>

#let step = step.with(pw: 232pt)
#disp[#table(
  columns: (1fr, 6.6cm),
  align: (center + horizon, left + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`(𝟙×R°)(π₂∪(p×𝟙) cons)⊑(π₂∪(p×𝟙) cons)R°` \
    #src[shortening the tail and then taking the step lands inside taking the step and then
 shortening the result]],
     // lean:AOP.A7_7_Filter.filter_mono@a4557bcf
  table.header([*formula* — the `cons` branch of `F(R°)S⊑SR°`], [*reason*]),

  [`(𝟙×R°)π₂=π₂R°`],
  [`π₂` natural #h(4pt) #src[@subseq-outr-square] #h(4pt) — the right side is an EQUALITY here],

  [`(𝟙×R°)(p×𝟙) cons⊑(p×𝟙) cons R°`],
  [@takewhile-mono's `cons` branch, unchanged],

  [#step([])[#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "stack", nin: 2, nout: 2, lanes: (
        (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
        (k: "seq", nin: 1, nout: 1, items: (
            (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
          ), seams: ()),
      )),
    (k: "union", nin: 2, nout: 1, bodies: (
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "proj", nin: 2, nout: 1, at: 1, label: "π₂", keep: (1, 1, )),
          ), seams: ()),
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "stack", nin: 2, nout: 2, lanes: (
                (k: "seq", nin: 1, nout: 1, items: (
                    (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
                  ), seams: ()),
                (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
              )),
            (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
          ), seams: ()),
      )),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(𝟙×R°)(π₂∪(p×𝟙) cons)", src: "A×[A]", tgt: "[A]"))][`(𝟙×R°)(π₂∪(p×𝟙) cons)`]], [],

  [#step(SQ)[#cpanel((k: "seq", nin: 2, nout: 1, items: (
    (k: "union", nin: 2, nout: 1, bodies: (
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "proj", nin: 2, nout: 1, at: 1, label: "π₂", keep: (1, 1, )),
          ), seams: ()),
        (k: "seq", nin: 2, nout: 1, items: (
            (k: "stack", nin: 2, nout: 2, lanes: (
                (k: "seq", nin: 1, nout: 1, items: (
                    (k: "box", nin: 1, nout: 1, label: "p", chamfer: true, frac: false, flip: false),
                  ), seams: ()),
                (k: "seq", nin: 1, nout: 1, items: (), seams: ()),
              )),
            (k: "box", nin: 2, nout: 1, label: "cons", chamfer: false, frac: false, flip: false),
          ), seams: ()),
      )),
    (k: "box", nin: 1, nout: 1, label: "R", chamfer: true, frac: false, flip: true),
  ), seams: (), src: ("A", "[A]", ), tgt: ("[A]", )),
  cert: (expect: "(π₂∪(p×𝟙) cons)R°", src: "A×[A]", tgt: "[A]"))][`(π₂∪(p×𝟙) cons)R°`]],
  [union #h(4pt) #src[@lax-closure] #h(4pt) at `X:=π₂`, `Y:=(p×𝟙) cons`],
)
#align(center, block(inset: (y: 4pt))[#src[`F(R°)S⊑SR°`, the `nil` branch again `nil⊑nil R°`. The
  first step is an equality: @takewhile-mono buys its `⊸ nil` branch with `nil R°=nil`, and `π₂`
  needs only its naturality square.]])
]<filter-mono>

#let step = step.with(pw: 246pt)
// §13.3.4 rebound `bx-est` to `est(≥)`, which is what the pictures below were drawing.
#let bx-est = ([`est(R°)`], 2.2, true)
#disp[#table(
  columns: (1fr, 4.4cm),
  align: (center + horizon, left + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[$frac(#[`S`], ∋)$ ` est(R°)=[nil,(π₁p→cons,π₂)]` \
    #src[the longest of the lists the algebra allows is the `cons` where the head passes `p`, and
 the tail where it does not]],
     // lean:AOP.A7_7_Filter.filter_step@7322621d
  table.header([*formula*], [*reason*]),

  [#step([])[#twp(twrun((bx-Sd, bx-est)), s: 74%)][$frac(#[`S`], ∋)$ ` est(R°)`]], [],

  [#step(EQ)[#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
        (k: "box", nin: 1, nout: 1, label: "E(π₂∪(p×𝟙) cons)", chamfer: false, frac: false, flip: false),
        (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
        (
          1,
          ("E(A×[A])", ),
        ),
        (
          2,
          ("E[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(π₂∪(p×𝟙) cons)%∋ est(R°)]", src: "F([A])", tgt: "[A]"))][`[nil,` $frac(#[`π₂∪(p×𝟙) cons`], ∋)$` est(R°)]`]],
  [@takewhile-step's first two steps],

  [#step(EQ)[#cpanel((k: "case", nin: 1, nout: 1, bodies: (
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
      ), seams: ()),
    (k: "seq", nin: 1, nout: 1, items: (
        (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
        (k: "box", nin: 2, nout: 1, label: "(π₁p→cons,π₂)", chamfer: false, frac: false, flip: false),
      ), seams: (
        (
          0,
          ("A", "[A]", ),
        ),
      )),
  ), src: ("F[A]", ), tgt: ("[A]", )),
  cert: (expect: "[nil,(π₁p→cons,π₂)]", src: "F([A])", tgt: "[A]"))][`[nil,(π₁p→cons,π₂)]`]],
  [`𝟙⊑π₂R cons°`],
)
#align(center, block(inset: (y: 4pt))[#src[at `(a,xs)` the set is `{xs}` where `p` fails on `a` and
  `{xs,cons(a,xs)}` where it holds, and `xs` loses the second — @est-defn at a two-element set. The
  head is dropped, not the whole tail: that is the one place `π₂` shows against @takewhile-step's `⊸ nil`.]])
]<filter-step>

// B&dM Ex 7.41, p. 174, assembled: the four displays above are the four steps, and the `E([A])` the
// transpose births is what the greedy step moves inside the reduce.
#let bx-slp = (frc([`subseq list(p)`]), 2.9, false)
#let bx-cS = (frc([`⦇S⦈`]), 1.6, false)
// ONE WIRE, `[A]` to `[A]`, its type written along it; `mid: none` once `E([A])` has gone inside the
// reduce.  Its own run and not @takewhile-step's, which starts at `F([A])` and belongs to §13.3.3.
#let fpic(items, mid: [`E([A])`]) = P(cetz.canvas(length: 0.8cm, {
  lab(-1.1, 0, black)[`[A]`]
  let x = 0.0
  for (i, b) in items.enumerate() {
    wire((x, 0), (x + 0.34, 0))
    gbox((x + 0.34, 0), b.at(0), w: b.at(1), h: TH, chamfer: b.at(2)); x = x + 0.34 + b.at(1)
    if i == 0 and mid != none {
      wire((x, 0), (x + 0.34, 0)); node(x + 0.9, 0, black, mid); x = x + 1.46
    }
  }
  wire((x, 0), (x + 0.34, 0)); lab(x + 0.9, 0, black)[`[A]`]
}), s: 80%)
// This display's longest bead is shorter than @takewhile-laws's, so its gray is narrower — one width
// for its own four rows, which is what puts `list` and `A` in a column.
#let lpan = lpan.with(w: 8.6)
#let epan = epan.with(w: 8.6)
// `S` is defined in @filter-defn, three pages back, and every row below reads it: the definition is
// repeated here rather than looked up, in that table's own five columns.
#disp[#align(center, block(width: 21cm)[
#table(
  columns: (1.7cm, 5.3cm, 2.9cm, 4.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*type*], [*example*], [*in words*]),

  [`S`], [`[nil,π₂∪(p×𝟙) cons]` #h(4pt) #src[@filter-defn]], [`F([A])⟶[A]`],
  [`(4,[2]) S [2]` #h(4pt) and #h(4pt) `(4,[2]) S [4,2]`, #h(4pt) but `(3,[2]) S [2]` only],
  [`subseq`'s algebra with one extra `p` — drop the head, or keep a head that passes `p`],
)])]

#disp[#pad(right: 10pt, table(
  columns: (1fr, 6.3cm),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`filter(p)=⦇[nil,(π₁p→cons,π₂)]⦈` \
    #src[Ex 7.41, `R` a preorder: the longest subsequence all of whose elements pass `p`,
 ]],
     // lean:AOP.A7_7_Filter.filter_eq_cata@c34da8f5
  table.header([*circuit* — one wire, its type written along it], [*Hinze–Marsden*]),

  [#vstep([], fpic((bx-slp, bx-est)),
 [`filter(p)≜`#frc([`subseq list(p)`])` est(R°)` \ #src[@comb-fns]])],
    // lean:AOP.A7_7_Filter.filter@86c3d821
  [#epan(body: hm-bead((LPX.at(2), LPYS.at(1)), [`p`]), sp: ((LPYS.at(0), [`subseq`]),), names: true)],

  [#vstep(EQ, fpic((bx-cS, bx-est)),
    [#frc([`⦇S⦈`])` est(R°)` \ #src[`subseq list(p)=⦇S⦈` — @takewhile-alg's header, `subseq` for `prefix`]])],
  [#epan(sp: ((LPY.at(1), [`⦇S⦈`]),))],

  [#vstep(RQ, [#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 2, nout: 1, items: (
      (k: "box", nin: 2, nout: 1, label: "𝟙", chamfer: false, frac: true, flip: false),
      (k: "box", nin: 1, nout: 1, label: "E(S)", chamfer: false, frac: false, flip: false),
      (k: "box", nin: 1, nout: 1, label: "est(R°)", chamfer: true, frac: false, flip: false),
    ), seams: (
      (
        0,
        ("EF[A]", ),
      ),
      (
        1,
        ("E[A]", ),
      ),
    )), label: none, port: ("A", "[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇S%∋ est(R°)⦈", src: "[A]", tgt: "[A]"))],
    [`⦇`#frc([`S`])` est(R°)⦈` \ #src[@greedy-thm72 at `R°`, whose hypothesis `F(R°)S⊑SR°` is
 @filter-mono]])],
     // lean:AOP.A7_7_Filter.filter_greedy@a4d1b1a5
  // The `E` wire is gone: the transpose and `est(R°)` now meet inside the reduce.  `list` and `A` are
  // unchanged, so they are drawn where the two panels above draw them.
  [#lpan(sp: ((LPY.at(1), [`⦇`#frc([`S`])` est(R°)⦈`]),))],

  [#vstep(EQ, [#cpanel((k: "cata", nin: 1, nout: 1, body: (k: "seq", nin: 1, nout: 1, items: (
      (k: "case", nin: 1, nout: 1, bodies: (
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 0, label: "l", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 0, nout: 1, label: "nil", chamfer: false, frac: false, flip: false),
            ), seams: ()),
          (k: "seq", nin: 1, nout: 1, items: (
              (k: "box", nin: 1, nout: 2, label: "r", chamfer: true, frac: false, flip: true),
              (k: "box", nin: 2, nout: 1, label: "(π₁p→cons,π₂)", chamfer: false, frac: false, flip: false),
            ), seams: (
              (
                0,
                ("A", "[A]", ),
              ),
            )),
        )),
    ), seams: ()), label: none, port: ("F[A]", ), src: ("[A]", ), tgt: ("[A]", )),
  cert: (expect: "⦇[nil,(π₁p→cons,π₂)]⦈", src: "[A]", tgt: "[A]"))],
    [`⦇[nil,(π₁p→cons,π₂)]⦈` \ #src[@filter-step]])],
  // Empty: the step only renames the algebra, and the picture above already draws the reduce.
  [],

  [#vstep(EQ, [],
    [#grid(columns: 3, align: (right + horizon, center + horizon, left + horizon),
       column-gutter: 6pt, row-gutter: 3pt,
 [`⦇[nil,(π₁p→cons,π₂)]⦈` entire #h(4pt) #src[]],
       // lean:AOP.A7_7_Filter.filter_entire@0c8b8ee9
 [and], [`filter(p)` simple #h(4pt) #src[]],
       // lean:AOP.A7_7_Filter.filter_simple@613696ae
       grid.cell(colspan: 3, align: left + horizon, inset: (top: 3pt))[#src[an entire relation below
         a simple one equals it; the simplicity is @comb-fns's Ex 7.41, not a law of this note,
 ]])])],
         // lean:Freyd.S2_10.eq_of_le_entire_simple@e9665c67
  [],
))
#align(center, block(inset: (y: 4pt))[#src[`(subseq list(p))°(subseq list(p))∩R∩R°⊑𝟙` fails — two
  `p`-subsequences of one list can be of equal length and different — so §@sec-takewhile's uniqueness
  argument does not transfer. What survives `est(R°)` is the one keeping *exactly* the passing
  elements: a subsequence that drops a passing element is beaten by the one that keeps it.]])
]<filter-deriv>

// Its own page: the section opens with a long definition display and was starting mid-page.
#pagebreak(weak: true)
== Planning a company party

// B&dM §7.3, p. 175.  No numbered equations; the two monotonicity claims are the section's own
// proof obligations, and the exercise blocks (7.43–7.44) are left out as everywhere else.
#disp[#table(
  columns: (7.8cm, 4.9cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

 [`tree A::=node (A,[tree A])` #src[]],
  // lean:AOP.A6_RoseTree.Rose@1e5d7a7f
  [`𝒜⟶𝒜`],
  [The company hierarchy: an employee, and the list of subtrees under them.],

 [`F(A,B)=A×[B]` #src[]],
  // lean:AOP.A6_RoseTree.F@bd6da71e
  [`𝒜×𝒜⟶𝒜`],
  [The base functor `tree` folds: an employee beside the recursive position, one layer deep.],

  [`rating`],
  [`A⟶Real`],
  [What one employee is worth as a guest.],

 [`cost≜list(rating) sum` #src[]],
  // lean:AOP.A7_3_Party.cost_eq@4da87db0
  [`[A]⟶Real`],
  [What a guest list is worth.],

 [`R≜cost≤cost°` #src[]],
  // lean:AOP.A7_3_Party.R_eq@9fa61324
  [`[A]⟶[A]`],
  [The preorder the guest list is maximised over.],

  [`choose≜π₁∪π₂`],
  [`[A]×[A]⟶[A]`],
  [Takes one of the two parties a subtree returns.],

  [`include≜(𝟙×(list(π₂) concat)) cons`],
  [`F(A,[A]×[A])⟶[A]`],
  [The party that invites the root, which puts every immediate subtree's root out. A map.],

  [`exclude≜(𝟙×(list(choose) concat))π₂`],
  [`F(A,[A]×[A])⟶[A]`],
  [The party that leaves the root out, so each subtree is free to choose. Not a map.],

  [`S≜⟨include,exclude⟩`],
  [`F(A,[A]×[A])⟶[A]×[A]`],
  [The algebra: one step returns both parties of a subtree at once.],

 [`party≜⦇S⦈ choose` #src[]],
  // lean:AOP.A7_3_Party.party_eq@db515982
  [`tree A⟶[A]`],
  [Every guest list the president's ruling allows.],

  [the specification \ $frac(#[`party`], ∋)$ `est(R°)`],
  [`tree A⟶[A]`],
  [A guest list of greatest total conviviality.],
)]<party-defn>

=== `include` and `exclude` <sec-party-algebras>

// Coordinates are literal: `d` is cetz.draw here and `e` is draw.typ's `∋`, so the six nodes cannot
// be named after the letters they carry.
#disp[#block(breakable: false)[#P(cetz.canvas(length: 0.8cm, {
  for (p, q) in (((0, 2.2), (-2, 0)), ((0, 2.2), (2, 0)), ((-2, 0), (-3, -2.2)),
                 ((-2, 0), (-1, -2.2)), ((2, 0), (3, -2.2))) { d.line(p, q, stroke: 0.75pt + black) }
  // Ratings deliberately not 1–6 in node order: as a run they read as indices, not as values.
  for (x, y, n, r) in ((0, 2.2, "a", "3"), (-2, 0, "b", "7"), (2, 0, "c", "2"),
                       (-3, -2.2, "d", "5"), (-1, -2.2, "e", "1"), (3, -2.2, "f", "8")) {
    node(x, y, black, [#raw(n) #text(9pt, luma(105))[#r]])
  }
}), s: 100%)
#align(center, src[the small grey number is the employee's rating])]]<party-example-tree>

// The fold on that tree, bottom-up; the last row reads its two cells off the rows for `b` and `c`.
// The `#src` block is 16.5cm, not the text width: at 22cm the wrap falls inside `[a,d,e,f]=17`.
#disp[
#table(
  columns: (2.0cm, 6.3cm, 7.3cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*node*], [*the algebra's input* \ `A×[[A]×[A]]`], [*`include`*], [*`exclude`*]),

  [`d`, `e`, `f`],
  [`(d,[])`],
  [`[d]`],
  [`[]`],

  [`b`],
  [`(b,[([d],[]),([e],[])])`],
  [`[b]`],
  [`[d,e]`, #h(4pt) `[d]`, #h(4pt) `[e]`, #h(4pt) `[]`],

  [`c`],
  [`(c,[([f],[])])`],
  [`[c]`],
  [`[f]`, #h(4pt) `[]`],

  [`a`],
  [`(a,[([b],…),([c],…)])`],
  [`[a]⧺exclude(b)⧺exclude(c)`],
  [`choose(b)⧺choose(c)`],
)
#align(center, block(width: 16.5cm, inset: (y: 4pt))[#align(center)[#src[with those ratings,
  `est(R°)` keeps `([b]=7,[d,e]=6)` at `b`, where `include` wins, and `([c]=2,[f]=8)` at `c`, where
  `exclude` wins, so at the root `include=[a,d,e,f]=17` beats `exclude=[b,f]=15`, and `choose`
  takes 17.]]])
]<party-example>

// `list(π₂)` is ONE box, not the `⊸ ⊗ 𝟙` inside the relator: the picture is here for the shape of
// `include`, and opening `π₂` up costs a discard stub per list element that says nothing about it.
// Both pictures share every stage's x: the boxes are right-aligned at 9.2, so the two read one under
// the other and a wire's type is found at the same place in each.
// The BOUNDARY of a circuit: nothing in `circuit.typ` or `draw.typ` draws one — `capbox` frames a
// picture and its caption, `gbox` frames a single relation — so one helper serves both algebras.
// The frame is 1.9pt, well over the 1.1pt of a wire and of a box edge: at wire weight it reads as
// one more wire.  Dark grey, not black, so the boxes ON the wires stay the darkest ink in the picture.
#let portbox(a, b, ports) = {
  d.rect(a, b, stroke: 1.9pt + luma(55), radius: 0.14)
  for (x, y, l) in ports { lab(x, y, black, l) }
}

#disp[#P(cetz.canvas(length: 0.8cm, {
  let y = 0.8
  portbox((-0.9, -1.8), (22.4, 1.8),
    ((-3.2, y, [`a:A`]), (-3.2, -y, [`[[A]×[A]]`]), (24.2, 0, [`adef:[A]`])))
  lab(-3.2, 2.5, black)[`include`$=$]
  wire((-1.5, y), (19.9, y))                 // the root, straight through: the `𝟙` of `𝟙 × (…)`
  wire((-1.5, -y), (6.6, -y))
  gbox((6.6, -y), [`list(π₂)`], w: 2.6, h: 0.75, chamfer: false)
  wire((9.2, -y), (13.8, -y))
  gbox((13.8, -y), [`concat`], w: 1.9, h: 0.75, chamfer: false)
  wire((15.7, -y), (18.9, -y))
  gbox((18.9, 0), [`cons`], w: 1.4, h: 2 * y + 0.35, chamfer: false)
  wire((20.3, 0), (22.9, 0))
  lab(3.7, -y + 0.5, black)[`b`]; lab(4.9, -y + 0.5, black)[`c`]
  lab(3.7, -y - 0.5, black)[`de`]; lab(4.9, -y - 0.5, black)[`f`]
  lab(10.2, -y + 0.5, black)[`[[A]]`]
  lab(11.7, -y - 0.5, black)[`de`]; lab(12.9, -y - 0.5, black)[`f`]
  lab(16.5, -y + 0.5, black)[`[A]`]
  lab(17.8, -y - 0.5, black)[`def`]
}), s: 80%)
#align(center, src[])]<include-pic>
// lean:AOP.A7_3_Party.include_eq@d4df2bf2

// The trailing `π₂` is `⊸ ⊗ 𝟙`, and here the discard IS the step, so it is drawn and not boxed.
// `list(choose)` keeps the chamfer: `choose` is a relation, where `include`'s `π₂` is a map.
#disp[#P(cetz.canvas(length: 0.8cm, {
  let y = 0.8
  portbox((-0.9, -1.8), (22.4, 1.8),
    ((-3.2, y, [`a:A`]), (-3.2, -y, [`[[A]×[A]]`]), (24.2, -y, [`bf:[A]`])))
  lab(-3.2, 2.5, black)[`exclude`$=$]
  wire((-1.5, y), (18.9, y))                 // the root, thrown away by the `⊸` of `π₂`
  wiredot((18.9, y))
  wire((-1.5, -y), (5.9, -y))
  gbox((5.9, -y), [`list(choose)`], w: 3.3, h: 0.75)
  wire((9.2, -y), (13.8, -y))
  gbox((13.8, -y), [`concat`], w: 1.9, h: 0.75, chamfer: false)
  wire((15.7, -y), (22.9, -y))
  lab(3.7, -y + 0.5, black)[`b`]; lab(4.9, -y + 0.5, black)[`c`]
  lab(3.7, -y - 0.5, black)[`de`]; lab(4.9, -y - 0.5, black)[`f`]
  lab(10.2, -y + 0.5, black)[`[[A]]`]
  lab(11.7, -y + 0.5, black)[`b`]; lab(12.9, -y - 0.5, black)[`f`]
  lab(16.5, -y + 0.5, black)[`[A]`]
  lab(17.8, -y - 0.5, black)[`bf`]
}), s: 80%)
#align(center, src[])]<exclude-pic>
// lean:AOP.A7_3_Party.exclude_eq@05c2777f

// `choose = π₁ ∪ π₂` is a choice PER ELEMENT, so `list(choose)` multiplies: two items, four lists.
#disp[#align(center, grid(
  columns: 5, column-gutter: 16pt, row-gutter: 6pt,
  align: (left + horizon, center + horizon, center + horizon, center + horizon, center + horizon),
  grid.cell(colspan: 5, align: left)[`list(choose) [([d],[]),([e],[])]`],
  [#h(1em)`1st item`], grid.cell(colspan: 4, align: left)[`([d],[])  choose↦[d]  or  []`],
  [#h(1em)`2nd item`], grid.cell(colspan: 4, align: left)[`([e],[])  choose↦[e]  or  []`],
  [#h(1em)`2×2=4 combinations:`], [`[[d],[e]]`], [`[[d],[]]`], [`[[],[e]]`], [`[[],[]]`],
  [#h(1em)`concat flattens:`], [`[d,e]`], [`[d]`], [`[e]`], [`[]`],
))]<party-list-choose>

=== `list((R×R)°)` <sec-party-listrr>

// The two lists are stacked so the correspondence is read DOWN a column: `list` relates lists of the
// same length position by position, so everything `list((R×R)°)` says is what `(R×R)°` says of one item.
#disp[#align(center, grid(
  columns: 6, column-gutter: 10pt, row-gutter: 5pt,
  align: (center + horizon, center + horizon, center + horizon, center + horizon, center + horizon,
          left + horizon),
  [`[`], [`([b],[d,e])`], [`,`], [`([c],[f])`], [`]`], [],
  [], [`│`], [], [`│`], [], [],
  [], [`▼`], [], [`▼`], [], src[`list((R×R)°)`, elementwise],
  [`[`], [`([b],[d])`], [`,`], [`([c],[])`], [`]`], [],
))
// One raw block, not a grid: the ticks land under `b` and `d` because every glyph is one monospace
// advance wide, which no measured column can promise.
#v(8pt)
#align(center)[```
([b],[d,e])
  │   └── exclude: the best party in b's subtree when b does not come
  └────── include: the best party in b's subtree when b comes
```]
#align(center, src[])]<party-listrr>
// lean:AOP.A7_3_Party.party_listrr_example@286e6447

// `(R×R)°` is TWO demands, one per component, and at `a` both elements move, each in its second —
// the table is here because "the relator relates them elementwise" hides which component that is.
#disp[
#table(
  columns: (3.6cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*element*], [*1st component* \ `include`], [*2nd component* \ `exclude`]),

  [1st, `([b],[d,e])`],
  [`[b] R° [b]` \ #src[`7≥7`, reflexivity]],
  [`[d,e] R° [d]` \ #src[`6≥5`, and `([b],[d,e])` is the pair `est(R°)` keeps at `b`]],

  [2nd, `([c],[f])`],
  [`[c] R° [c]` \ #src[`2≥2`, reflexivity]],
  [`[f] R° []` \ #src[`8≥0`, and `([c],[f])` is the pair `est(R°)` keeps at `c`]],
)
#align(center, src[the first component of `𝟙×list((R×R)°)` is the root employee.
 ])
  // lean:AOP.A7_3_Party.party_listrr_example@286e6447
]<party-rr>

// Each note in its own block: the template indents the second of two consecutive paragraphs, and an
// indented note reads as a continuation of the one above it.
#block[#src[`R≜cost≤cost°` is a preorder, so the components that do not move are related by
  reflexivity — `(R×R)°` demands a relation in *both* components, it cannot skip one.]]

#block[#src[`R` compares cost only, not contents: `[f] R° []` is legal though `[f]` has an element
  `[]` does not. That is why the three leaves of §@sec-party-mono's proof all reduce to
  "`cost` is a sum".]]

=== `(𝟙×list((R×R)°))S⊑S(R×R)°` — `S : F([A]×[A])⟶[A]×[A]` monotonic on `(R×R)°` <sec-party-mono>

// @mon-str at `F := (− × [−])`, `A := [A]×[A]`, `R := (R×R)°`, so `F((R×R)°) = 𝟙×list((R×R)°)`; @lax-defn at
// `G := F`, `F := Id`, `φ := S` for the panels, `rev` putting the smaller side left, where `⊑` points.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FT, T, FB, B) = ((-4.2, 1.25), (4.2, 1.25), (-4.2, -1.25), (4.2, -1.25))
    ar(FT, T, GIVEN1, s0: 1.9, s1: 1.5); ar(FB, B, GIVEN1, s0: 1.9, s1: 1.5)
    ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55); ar(T, B, GIVEN2, s0: 0.55, s1: 0.55)
    lab(0, 1.8, GIVEN1)[`S`]; lab(0, -1.8, GIVEN1)[`S`]
    lab(-6.4, 0, GIVEN2)[`𝟙×list((R×R)°)`]; lab(5.2, 0, GIVEN2)[`(R×R)°`]
    lab(0, 0, SLACK, rot: -45deg)[`⊑`]
    node(FT.at(0), FT.at(1), black, `F([A]×[A])`); node(T.at(0), T.at(1), black, `[A]×[A]`)
    node(FB.at(0), FB.at(1), black, `F([A]×[A])`); node(B.at(0), B.at(1), black, `[A]×[A]`)
  }),
  // `length` up from the file's 0.95cm: the port labels do not scale with it, and at 0.95cm the two
  // top ports touch — `F` `[A]×[A]`, which the reader reads across, comes out as `F[A]`.
  homeq(`F`, `[A]×[A]`, `S`, `(R×R)°`, `S`, `[A]×[A]`, ctop: GIVEN1, cmid: GIVEN2, cbot: GIVEN1,
    regions: auto, sep: text(SLACK)[`⊑`], rev: true, gap: 1.4, length: 1.35cm),
 [`(𝟙×list((R×R)°))S⊑S(R×R)°` #src[]],
  // lean:AOP.A7_3_Party.party_mono@8a43178e
)]<party-mono>

// @adj-E-bend's shapes at this instance: a transpose is the dashed INDUCED arrow the adjunction
// produces, and the factorisation it runs through is that picture's GIVEN2 path.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (T, EB) = ((-2.9, 0), (2.9, 0))
    ar(T, EB, INDUCED, dash: "dashed", s0: 1.05, s1: 0.8)
    lab(0, 0.85, INDUCED)[$frac(#[`⦇S⦈ choose`], ∋)$]
    node(T.at(0), T.at(1), black, `tree A`); node(EB.at(0), EB.at(1), black, `E[A]`)
  }),
  cetz.canvas(length: 0.8cm, {
    lab(-6.8, 0, black)[$=$]
    let (T, EM, EB) = ((-5.0, 0), (0, 0), (5.0, 0))
    ar(T, EM, GIVEN2, s0: 1.05, s1: 1.6); ar(EM, EB, GIVEN2, s0: 1.6, s1: 0.8)
    lab(-2.5, 0.85, GIVEN2)[$frac(#[`⦇S⦈`], ∋)$]
    lab(2.5, 0.62, GIVEN2)[`E(choose)`]
    node(T.at(0), T.at(1), black, `tree A`); node(EM.at(0), EM.at(1), black, `E([A]×[A])`)
    node(EB.at(0), EB.at(1), black, `E[A]`)
  }),
  [$frac(#[`⦇S⦈ choose`], ∋)$ `=` $frac(#[`⦇S⦈`], ∋)$ `E(choose)` #h(1cm) #src[@pow-laws, absorption,
 ]],
   // lean:AOP.A4_6.Λ_absorption@e87bd8f2
)]<party-absorb>

// `(label, width, chamfer)`, set once: the same box is drawn in up to four rows, and a width typed
// per row is a width that drifts.  No chamfer is a map — `concat` is one, `list(g)` is not (`choose`).
#let box-ro = ([`R°`], 1.1, true)
#let box-lrro = ([`list((R×R)°)`], 3.2, true)
#let box-cc = ([`concat`], 1.9, false)
#let box-lg = ([`list(g)`], 2.2, true)
#let box-lgro = ([`list(gR°)`], 2.6, true)

// A PRODUCT IS TWO WIRES.  `F([A]×[A])=A×[[A]×[A]]` enters as two, `[A]×[A]` leaves as two, and
// `𝟙×list((R×R)°)` is the root's wire running straight past a box that sits on the other one — `×` costs no
// notation, it IS the second wire.  `[[A]×[A]]` stays ONE wire: its outermost former is the list.
// The shape below opens with `pairin`, at two strand heights, so the height is its parameter.
#let pairin(y, items) = {
  lab(-0.55, y, black)[`A`]; lab(-1.6, -y, black)[`[[A]×[A]]`]
  wire((0, y), (boxrun-w(items), y))
  boxrun(0, -y, items)
}
// A branch's shape: the root straight through the upper wire, the subtrees' pairs down the lower
// one, both entering the box that spans them — `h` once `include`/`exclude` is unfolded.
#let tallpic(items, head, hw, hc: false, post: ()) = {
  let (y, w) = (0.8, boxrun-w(items))
  pairin(y, items)
  gbox((w, 0), head, w: hw, h: 2 * y + 0.4, chamfer: hc)
  boxrun(w + hw, 0, post)
  lab(w + hw + boxrun-w(post) + 0.45, 0, black)[`[A]`]
}
// Every row's picture is drawn at ONE length and ONE scale, and a scale typed per cell is a scale
// that drifts — both times this one changed, it had to change in every cell.
#let party-pic(body) = P(cetz.canvas(length: 0.8cm, body), s: 90%)
#let TREE = [`tree`]
#let LIST = [`list`]
#let DELTA = [`Δ`]
#let OBJ = [`A`]
#let EW = [`E`]
#let UNIT = frc([`𝟙`])

// Only the three `⊑` steps are rows: the five `=` steps are `F(RS)=F(R)F(S)`, `(R×S)(U×V)=(RU)×(SV)`
// and the branch unfolded and refolded, and BOTH pictures draw either side of them with the same ink.
// HINZE–MARSDEN (IntroString.pdf §1.4.2): a wire is a FUNCTOR, a bead an arrow, a region a category, gray `𝟏`.
// `Δ` = the relator `X↦X×X` (the diagonal `X↦(X,X)`, then `×`): a FUNCTOR, not the copy relation `◁ : A⟶A⊗A`.
// `[A]` STAYS ONE WIRE here, the one panel family that declares `split: ""`: `R:[A]⟶[A]` is an
// ordering on parties, so split it would have to eat the `list` and make another at each of the four
// heights the `R°` bead takes — two more columns, and 10.3 of width in a 5.0cm column.
#let PXM = 0.55                  // `A×−`, the root employee
#let PXLo = 1.70                 // `list`, the subtrees
#let PXD = 2.85                  // `Δ`, the pair one subtree returns
#let PXO = 4.00                  // the object wire, `[A]`
// Tighter slots, not a smaller `s`: the panel prints its labels at the circuit column's 90%, and the
// height the four rows must give back comes out of the wire spacing instead.
#let HMY = (0.45, 1.05, 1.65, 2.25, 2.85, 3.45, 4.05)   // slot 3, `h`, 2, `concat`, 1, `g`, 0
#let HMH = 4.5
#let PARTY = [`[A]`]
// The key table below the display: `include` is the panel's own composite at `g:=π₂`, `h:=cons`.
#let INCL = "include = (𝟙×(list(g)concat))h"
#let party-hm(rs) = {
  let (Y3, YN, Y2, YC, Y1, YP, Y0) = HMY
  dpanel(HMH, PXO + 2.85, PXO,
    ((PXM, "top", YN, none, none), (PXLo, "top", YC, none, none), (PXD, "top", YP, none, none)),
    ((YP, [`g`]), (YC, [`concat`]), (YN, [`h`]),
     ((Y0, Y1, Y2, Y3).at(rs), [`R°`], GIVEN1)),
    ((PXM, [`A×−`]), (PXLo, LIST), (PXD, DELTA), (PXO, PARTY)),
    ((PXO, PARTY),), names: rs == 0, s: 90%,
    // The first and last panels are the row the display states; the two in between are the steps
    // the `R°` bead takes to get from one to the other, and the display states no formula for them.
    cert: ((expect: "(𝟙×list((R×R)°))include", alias: (INCL,), split: ""), (:), (:),
           (expect: "include R°", alias: (INCL,), split: "")).at(rs))
}

#let step = step.with(pw: 319pt)
#disp[#table(
  // Not `HMW`: that column holds a circuit, this one a panel, and 5.0cm is the four wires at `s: 90%`.
  columns: (1fr, 5.0cm),
  align: (center + horizon, center + horizon),
  // `y: 1pt`, tighter than the note's usual 3pt: the four rows plus the key list are a page exactly.
  inset: (x: 9pt, y: 1pt), stroke: 0.4pt + luma(190),
  // One shape instantiated three times, so the three `⊑` stand in a column.
  Thm[#align(center, grid(columns: 3, column-gutter: 6pt, row-gutter: 3pt,
    align: (right + horizon, center + horizon, left + horizon),
    grid.cell(colspan: 3, align: center)[`S≜⟨include,exclude⟩`],
    [`(𝟙×list((R×R)°))S`], SQ, [`S(R×R)°`],
    [`(𝟙×list((R×R)°))include`], SQ, [`include R°`],
    [`(𝟙×list((R×R)°))exclude`], SQ, [`exclude R°`],
  ))
  #src[bettering both parties of every subtree before the node's algebra runs gets no further than
   running it first and bettering the two parties it returns,
 ]],
   // lean:AOP.A7_3_Party.branch_monotonic@668fb773 lean:AOP.A7_3_Party.exclude_monotonic@92dade83
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#step([])[#party-pic(tallpic((box-lrro, box-lg, box-cc), [`h`], 0.95))][]], [#party-hm(0)],

  [#step(SQ)[#party-pic(tallpic((box-lgro, box-cc), [`h`], 0.95))][]], [#party-hm(1)],

  [#step(SQ)[#party-pic(tallpic((box-lg, box-cc, box-ro), [`h`], 0.95))][]], [#party-hm(2)],

  [#step(SQ)[#party-pic(tallpic((box-lg, box-cc), [`h`], 0.95, post: (box-ro,)))][]], [#party-hm(3)],
)

#v(3pt)

// The key list, read DOWNWARD like the pictures: one line per bead `R°` walks past.
#align(center, block(width: 20.5cm)[#src[#grid(
  columns: (1.7cm, auto),
  row-gutter: 3.5pt, align: (left, left),
  [`g`],
  [`(R×R)°g⊑gR°` \ `g:=π₂` is `(R×R)°π₂=(Dom(π₁R°))π₂R°⊑π₂R°`
 #src[], `g:=π₁` its mirror
   // lean:AOP.A7_3_Party.include_monotonic@c4d977bd
   `(Dom(π₂R°))π₁R°⊑π₁R°` — 1 and 4 of @bdm-prod-laws, then `Dom⊑𝟙`; `g:=choose≜π₁∪π₂` is the union
 of the two #h(4pt) #src[@lax-closure].
   // lean:AOP.A7_3_Party.chooseR_monotonic@8817d447
   `list` monotonic, @relator-defn],
  [`concat`],
  [`list(R°)concat⊑concat R°` \ a LEAF: no law above it. `cost` is a sum, so
   `cost(concat xss)=sum(list(cost)xss)` and a cheaper part makes a cheaper whole. B&dM's exercise.
 #src[]],
   // lean:AOP.A7_3_Party.concat_monotonic@084e46a9
  [`h`],
  [`(𝟙×R°)h⊑hR°` \ a LEAF: `cost(cons(a,xs))` `=rating(a)+cost(xs)`, so a cheaper tail
 makes a cheaper list. B&dM's exercise. #src[]
   // lean:AOP.A7_3_Party.cons_monotonic@e5288fc0
   For `h:=π₂` it is an EQUALITY `(𝟙×R°)π₂=(Dom(π₁))π₂R°`
 `=π₂R°` #src[]: `π₁` is a map, hence entire, so
   // lean:AOP.A6_1_RelSet.rprodMap_id_snd@dc93a451
   `Dom(π₁)=𝟙` — @dom-laws],
)]])

#v(3pt)

#align(center, table(
  columns: 3, align: center + horizon,
  inset: (x: 9pt, y: 2pt), stroke: 0.4pt + luma(190),
  table.header([`(𝟙×(list(g) concat))h`], [`g`], [`h`]),
  [`include`], [`π₂`], [`cons`],
 [`exclude` #src[]], [`choose`], [`π₂`],
  // lean:AOP.A7_3_Party.exclude_monotonic@92dade83
))
]<party-mono-branch>

// The `⊑` is STRICT, and the witness says where: the `g` row's one inequality is `Dom⊑𝟙`.
#disp[#table(
  columns: (auto, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`R≜{(0,0)} : {0,1}⟶{0,1}`], [not entire — undefined at `1`],

  [`(R×R)choose` at `(0,1)`], [nothing — `R×R` needs BOTH components related, and `R` is undefined
   at `1`],

  [`choose R` at `(0,1)`], [`0` — `choose` picks the first component `0`, and `R 0 0` holds],

  [`((0,1),0)`], [in `choose R`, not in `(R×R)choose`
 #h(4pt) #src[]],
   // lean:AOP.A7_3_ChooseStrict.choose_monotonic_strict@2b446ff0

  [`(R×R)choose=choose R`], [iff `R` is entire — `Dom⊑𝟙` is the `g` row's only inequality step,
   and it is an equality iff `Dom(R)=𝟙`],
)]<choose-strict>

=== The derivation <sec-party-deriv>

// The pictures are ONE WIRE from `tree A` to `[A]`, a box per factor; `[A]×[A]` is where it runs as
// TWO — `est((R×R)°)` opens the strand into a pair and `choose/∋` closes it again.  Every `R/∋` is a
// MAP (@pow-laws), so every fraction box is square and every other box chamfered.
#let LD = 0.34               // circuit.typ's lead, which it does not export
#let LH = 1.25               // a box on the wire: two lines tall, because a `/∋` label is a fraction
#let LSP = 0.62              // half the gap between the two strands of `[A]×[A]`
#let LPH = 2 * LSP + 0.62    // a box that spans the pair
#let LBA = 1.5               // inside the fold, a branch's root strand ...
#let LBB = 0.55              // ... and its subtree-list strand
#let LBY = (LBA + LBB) / 2   // ... and the single strand the branch leaves on
#let TG = 1.7                // a lead wide enough to carry a TYPE label, not just join two boxes
#let TGW = 3.0                // ... and wide enough for the longest of them, `E([A]×[A])`
#let TY = 0.34                // how far above (or, mirrored, below) its wire a type label floats

#let lb-est = ([`est(R°)`], 2.2, true)
#let lb-cc = ([`concat`], 1.9, false)
#let lb-lcm = ([`list(`#frc([`choose`])` est(R°))`], 5.5, true)

// The tail every row ends with, `choose/∋ est(R°)`: `choose` takes TWO wires, so the pair closes
// there, and `est(R°)` reads the set back down to one list.  `sp` is the height the pair arrives at.
// `midlabel`: `13.4.4a`'s row is the only caller that names the type between `choose/∋` and `est(R°)`
// — every other row shares this same tail, so the label stays off unless asked for.
#let ltail(x, sp, midlabel: none) = {
  gbox((x, 0), frc([`choose`]), w: 2.0, h: 2 * sp + 0.62, chamfer: false)
  let g = if midlabel == none { LD } else { TG }
  wire((x + 2.0, 0), (x + 2.0 + g, 0))
  if midlabel != none { lab(x + 2.0 + g / 2, TY, black)[#midlabel] }
  gbox((x + 2.0 + g, 0), lb-est.at(0), w: lb-est.at(1), h: LH, chamfer: lb-est.at(2))
  let xe = x + 2.0 + g + lb-est.at(1)
  wire((xe, 0), (xe + LD, 0))
  lab(xe + LD + 0.5, 0, black)[`[A]`]
}
#let lsrc = { lab(-1.32, 0, black)[`tree A`]; wire((-0.45, 0), (0, 0)) }

#let lrun(items) = {
  lsrc; boxrun(0, 0, items, h: LH)
  lab(boxrun-w(items) + 0.5, 0, black)[`[A]`]
}
// `13.4.4a`'s row: the only one where the type actually changes mid-run, so it is the only one
// that gets the wire types spelled out — `E([A]×[A])` in, `est((R×R)°)` opens the pair, `[A]` on
// each of the two strands it opens into (a PRODUCT is two wires, never one wire marked `×`).
#let lopen(items) = {
  lsrc; boxrun(0, 0, items, h: LH)
  let w = boxrun-w(items)
  wire((w, 0), (w + TGW, 0)); lab(w + TGW / 2, TY, black)[`E([A]×[A])`]
  gbox((w + TGW, 0), [`est((R×R)°)`], w: 3.3, h: LPH)
  let w2 = w + TGW + 3.3
  wire((w2, LSP), (w2 + TG, LSP)); lab(w2 + TG / 2, LSP + TY, black)[`[A]`]
  wire((w2, -LSP), (w2 + TG, -LSP)); lab(w2 + TG / 2, -LSP - TY, black)[`[A]`]
  ltail(w2 + TG, LSP, midlabel: [`E([A])`])
}

// `⦇−⦈` drawn as MELLIÈS' functorial box: the body's own circuit, inside brackets.  A bar is where
// the type changes, so nothing crosses the LEFT one — the tree arrives at it and the algebra's two
// strands start there, which is the recursion — while the body's output IS the fold's and runs on.
#let banana(x, yh, right: false) = {
  let s = if right { -1 } else { 1 }
  let st = (thickness: lw, paint: black)
  d.line((x, -yh), (x, yh), stroke: st); d.line((x + s * 0.13, -yh), (x + s * 0.13, yh), stroke: st)
  d.line((x, yh), (x + s * 0.3, yh), stroke: st); d.line((x, -yh), (x + s * 0.3, -yh), stroke: st)
}
#let lfold(yh, bw, sp, body) = {
  lsrc; banana(0, yh)
  wire((0.13, LSP), (0.4, LSP)); wire((0.13, -LSP), (0.4, -LSP))
  body
  let x1 = 0.8 + bw
  banana(x1, yh, right: true)
  wire((0.4 + bw, sp), (x1 + LD, sp)); wire((0.4 + bw, -sp), (x1 + LD, -sp))
  ltail(x1 + LD, sp)
}

#let lbody5 = {
  wire((0.4, LSP), (0.4 + LD, LSP)); wire((0.4, -LSP), (0.4 + LD, -LSP))
  gbox((0.4 + LD, 0), frc([`S`]), w: 1.0, h: LPH, chamfer: false)
  wire((1.74, 0), (1.74 + LD, 0))
  gbox((1.74 + LD, 0), [`est((R×R)°)`], w: 3.3, h: LPH)
}
#let LBW5 = 2 * LD + 1.0 + 3.3
// The pair is COPIED into the two branches and the middle strands cross, as in §@sec-party-mono:
// each branch keeps one copy of the root and one of the subtree list.
#let lshuffle = {
  wiredot((0.4, LSP)); bend((0.4, LSP), (1.3, LBA)); bend((0.4, LSP), (1.3, -LBB))
  wiredot((0.4, -LSP)); bend((0.4, -LSP), (1.3, LBB)); bend((0.4, -LSP), (1.3, -LBA))
}
#let lbody6 = {
  lshuffle
  for (yh, yl, head) in ((LBA, LBB, frc([`include`])), (-LBB, -LBA, frc([`exclude`]))) {
    gbox((1.3, (yh + yl) / 2), head, w: 2.3, h: yh - yl + 0.55, chamfer: false)
    boxrun(3.6, (yh + yl) / 2, (lb-est,), h: LH)
  }
}
#let LBW6 = 0.9 + 2.3 + boxrun-w((lb-est,))
#let lbody7 = {
  lshuffle
  gbox((1.3, LBY), [`include`], w: 2.2, h: LBA - LBB + 0.55, chamfer: false)
  // `π₂` throws the root away, so the lower branch runs on the subtree list alone.
  wiredot((1.3, -LBB))
  boxrun(1.3, -LBA, (lb-lcm, lb-cc), h: LH)
  let xe = 1.3 + boxrun-w((lb-lcm, lb-cc))
  wire((3.5, LBY), (xe + 0.6, LBY)); bend((xe, -LBA), (xe + 0.6, -LBY))
}
#let LBW7 = 0.9 + boxrun-w((lb-lcm, lb-cc)) + 0.6

// ---- The two Hinze-Marsden panels: what surrounds the `⦇ ⦈`, and what sits inside it.  A wire is
// a FUNCTOR and a bead an arrow, so SUGAR IS UNDONE BEFORE DRAWING and at the ends too: `[A]` is the
// `list` wire beside the `A` wire, `tree A` the `tree` wire beside it, `[A]×[A]` the relator `Δ`
// (`X↦X×X`) over both.  One lane then carries `tree` above the bead that eats it and `list` below.
// The transpose is split, #frc([`R`])`=`#frc([`𝟙`])`E(R)` (@adj-E-bend): the singleton OPENS the `E`
// wire — a bead of its own, off the object wire — and an `est` CLOSES it.  So `E(choose)` is the
// `choose` bead with `E` running past, and `party`'s absorption step is one picture drawn twice.
// The lanes, outermost functor LEFTMOST: the composite reads across applicatively, `𝟏` at the right.
// Two of these panels stack in ONE cell from the greedy step on, and the seven rows are a page
// exactly: this is the scale that buys the last row its reason line.
#let DS = 70%
#let DXE = 0.55                  // `E`, outside everything
#let DXL = 2.85                  // `tree` down to the bead that eats it, `list` from there on
#let DXO = 4.00                  // the object wire, `A`
#let DW = DXO + 2.85
#let DIE = 0.55                  // `E`, when the transpose is applied OUTSIDE the list
#let DIM = 1.70                  // `A×−`, the base functor's own factor
#let DIL = 2.85                  // `list`, the algebra's argument
#let DID = 5.15                  // `Δ`
#let DIl = 6.30                  // `list`, inside the pair
#let DIO = 7.45                  // the object wire, `A`
#let DIW = DIO + 2.85

// The panel pair a row shows.  `none` is a panel the row above already drew — the outside is fixed
// from the greedy step on, and the inside does not exist before it.
#let dcell(o, i) = align(center, stack(spacing: 5pt, ..(o, i).filter(x => x != none)))

// Every row writes one fraction where its panel draws two beads: the unit `H%∋=(𝟙%∋)E(H)` opens
// `E` outside `H`.  One law, instantiated at the numerator each row names.
#let DUN(h) = h + "%∋ = 𝟙%∋ E(" + h + ")"

// `est(R°)` holds one height down the family and `choose` another, so what moves is the fold: the
// bead that eats the `tree` wire, and where the `E` it opens is closed.
#let d-out1 = dpanel(4, 6.85, 4,
  ((0.55, 2.5, 1, [`E`], frc([`𝟙`])), (1.7, 2, "bot", none, none), (2.85, "top", 2, none, none)),
  ((2, [`party`], black, 2.85), (1, [`est(R°)`], black, 0.55)),
  ((2.85, [`tree`]), (4, [`A`])),
  ((1.7, [`list`]), (4, [`A`])),
  cert: (expect: "𝟙%∋ E(party)est(R°)", src: "tree(A)", tgt: "[A]"))
// Rows 2 and 3 draw the SAME panel: `E(⦇S⦈ choose)=E(⦇S⦈)E(choose)`, which is the absorption step.
// The ink spells the LOWER of the two rows: `⦇S⦈%∋` and `choose` are two beads, and row 2's
// `frc(⦇S⦈ choose)` is that one absorption step away.
#let d-out2 = dpanel(5, 8, 5.15,
  ((0.55, 3.5, 1, [`E`], frc([`𝟙`])), (1.7, 3, 2, [`Δ`], none), (2.85, 3, "bot", none, none), (4, "top", 3, none, none)),
  ((3, [`⦇S⦈`], black, 4), (2, [`choose`], black, 1.7), (1, [`est(R°)`], black, 0.55)),
  ((4, [`tree`]), (5.15, [`A`])),
  ((2.85, [`list`]), (5.15, [`A`])),
  cert: (expect: "𝟙%∋ E(⦇S⦈)E(choose)est(R°)", src: "tree(A)", tgt: "[A]"))
#let d-out4 = dpanel(7, 9.15, 6.3,
  ((0.55, 5.5, 4, [`E`], frc([`𝟙`])), (1.7, 2.5, 1, [`E`], frc([`𝟙`])), (2.85, 5, 2, [`Δ`], none), (4, 5, "bot", none, none), (5.15, "top", 5, none, none)),
  ((5, [`⦇S⦈`], black, 5.15), (4, [`est((R×R)°)`], black, 0.55), (2, [`choose`], black, 2.85), (1, [`est(R°)`], black, 1.7)),
  ((5.15, [`tree`]), (6.3, [`A`])),
  ((4, [`list`]), (6.3, [`A`])),
  cert: (expect: "𝟙%∋ E(⦇S⦈)est((R×R)°)𝟙%∋ E(choose)est(R°)", src: "tree(A)", tgt: "[A]"))

// Inside the brackets the source is `F([A]×[A])=A×[[A]×[A]]`: five wires down to the object.  The
// algebra is natural in NOTHING — it eats every functor the source carries and MAKES the pair it
// returns — so all four strands land on its bead and the two it returns are born there.
#let d-in5 = dpanel(4, 11.45, 8.6,
  ((0.55, 2.5, 1, [`E`], frc([`𝟙`])), (1.7, 2, "bot", none, none), (2.85, 2, "bot", none, none), (4, "top", 2, none, none), (5.15, "top", 2, none, none), (6.3, "top", 2, none, none), (7.45, "top", 2, none, none)),
  ((2, [`S`], black, 4), (1, [`est((R×R)°)`], black, 0.55)),
  ((4, [`A×−`]), (5.15, [`list`]), (6.3, [`Δ`]), (7.45, [`list`]), (8.6, [`A`])),
  ((1.7, [`Δ`]), (2.85, [`list`]), (8.6, [`A`])),
  opath: ((8.6, 4), (7.45, 2), (4, 1), (4, 0)),
  cert: (expect: "𝟙%∋ E(S)est((R×R)°)", src: "A×[[A]×[A]]", tgt: "[A]×[A]"))
#let d-in6 = dpanel(4, 10.3, 7.45,
  ((0.55, 2.5, 1, [`E`], frc([`𝟙`])), (1.7, 2, "bot", none, none), (2.85, "top", 2, none, none), (4, "top", 2, none, none), (5.15, "top", 2, none, none), (6.3, "top", 2, none, none)),
  ((2, [`include`], black, 2.85), (1, [`est(R°)`], black, 0.55)),
  ((2.85, [`A×−`]), (4, [`list`]), (5.15, [`Δ`]), (6.3, [`list`]), (7.45, [`A`])),
  ((1.7, [`list`]), (7.45, [`A`])),
  opath: ((7.45, 4), (6.3, 2), (2.85, 1), (2.85, 0)),
  cert: (expect: "𝟙%∋ E(include)est(R°)", src: "A×[[A]×[A]]", tgt: "[A]"))
// `list(`#frc([`choose`])` est(R°))` opens its `E` INSIDE the list: the transpose is taken once per
// element, and `concat` is what finally eats the list the elements sat in.  The row writes the two
// beads under one `list` wire as one application, which is `F(R)F(S)=F(RS)` at `F:=list`.
#let d-in7 = dpanel(6, 10.3, 7.45,
  ((0.55, "top", 5, none, none), (1.7, 1, "bot", none, none), (2.85, "top", 1, none, none), (4, 3.5, 2, [`E`], frc([`𝟙`])), (5.15, "top", 3, none, none), (6.3, "top", 1, none, none)),
  ((5, [`π₂`], black, 0.55), (3, [`choose`], black, 5.15), (2, [`est(R°)`], black, 4), (1, [`concat`], black, 2.85)),
  ((0.55, [`A×−`]), (2.85, [`list`]), (5.15, [`Δ`]), (6.3, [`list`]), (7.45, [`A`])),
  ((1.7, [`list`]), (7.45, [`A`])),
  opath: ((7.45, 6), (7.45, 5), (7.45, 3), (7.45, 2), (6.3, 1), (2.85, 0)),
  cert: (expect: "π₂ list(𝟙%∋)list(E(choose))list(est(R°))concat", src: "A×[[A]×[A]]", tgt: "[A]"))

// Not `P`: its 5pt of vertical inset is what `vstep`'s own 5pt of spacing already gives, and the
// seven rows are a page exactly — the scale below is what those two insets bought.
#let laws-pic(body) = align(center, box(inset: (y: 1pt),
  scale(x: 84%, y: 84%, reflow: true, cetz.canvas(length: 0.8cm, body))))

// The reason rides UNDER the formula, in the picture's own column: a column of its own cost the
// circuits 3.8cm, and the two laws that would not fit it are now written out in full.  `vstep`, not
// `step`: a cell whose height `layout` decides is measured on the branch it does not draw, and the
// third line then lands under the row's rule.
#disp[#table(
  columns: (1fr, 6.6cm),
  align: (left + horizon, center + horizon),
  // `y: 1pt`, tighter than the note's usual 3pt: the seven rows are a page exactly, and a `#disp`
  // that outgrows its page does not break — the last row keeps its rule and spills its text past it.
  inset: (x: 8pt, y: 2pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`party`])` est(R°)⊒⦇⟨include,π₂ list(`#frc([`choose`])` est(R°)) concat⟩⦈ `#frc([`choose`])` est(R°)` \
    #src[the best of every guest list the president allows is one pass up the tree, each subtree
     handing up its best party with its boss in and its best with the boss out, and `choose` taking
 the better of the two at the root]],
     // lean:AOP.A7_3_Party.party_laws@a2d9caf9
  table.header([*circuit*],
    [*Hinze–Marsden* — outside the `⦇ ⦈` above, inside it below; a fork drawn at one branch]),

  [#vstep([], laws-pic(lrun(((frc([`party`]), 1.7, false), lb-est))),
    [#src[the specification — @party-defn]])],
  [#dcell(d-out1, none)],

  [#vstep(EQ, laws-pic(lrun(((frc([`⦇S⦈ choose`]), 3.0, false), lb-est))),
    [#src[`party≜⦇S⦈ choose` — @party-defn]])],
  [#dcell(d-out2, none)],

  [#vstep(EQ, laws-pic(lrun(((frc([`⦇S⦈`]), 1.3, false), ([`E(choose)`], 2.7, true), lb-est))),
    [#src[#frc([`⦇S⦈ choose`])`=`#frc([`⦇S⦈`])` E(choose)` — @party-absorb]])],
  [#dcell(d-out2, none)],

  [#vstep(RQ, laws-pic(lopen(((frc([`⦇S⦈`]), 1.3, false),))),
    [#src[`(R×R)°choose⊑choose R°` — Ex 7.38, @party-mono-branch's `g` row,
 ]])],
      // lean:AOP.A7_2.est_Λ_est_le@1083248a
  [#dcell(d-out4, none)],

  [#vstep(RQ, laws-pic(lfold(1.18, LBW5, LSP, lbody5)),
    [#src[from here `⦇ ⦈` is drawn open — the two bars, with the algebra's own circuit between them;
      `(𝟙×list((R×R)°))S⊑S(R×R)°` — Theorem 7.2 at `(R×R)°`, @party-mono,
 ]])],
      // lean:AOP.A7_2.greedy@21400acf
  [#dcell(none, d-in5)],

  [#vstep(RQ, laws-pic(lfold(2.05, LBW6, LBY, lbody6)),
    [#src[`⟨`#frc([`include`])` est(R°),`#frc([`exclude`])` est(R°)⟩⊑`#frc([`S`])` est((R×R)°)` — Ex 7.15,
 ]])],
      // lean:AOP.A7_3_Party.pair_est_le@75a48598
  [#dcell(none, d-in6)],

  [#vstep(RQ, laws-pic(lfold(2.05, LBW7, LBY, lbody7)),
    [#src[`include` a map, `est(R°)` into each branch,
 ]])],
      // lean:AOP.A7_3_Party.graph_le_Λ_est@32e3aa7d lean:AOP.A7_3_Party.exclude_step@7360252f
  [#dcell(none, d-in7)],
)]<party-laws>

// Its own page: the section opens with a long definition display and was starting mid-page.
#pagebreak(weak: true)
== Shortest paths on a cylinder

// B&dM §7.4, p. 179.  Its crux is @mon-thm71, not the greedy theorem: `α` is a map, so monotonic
// gives distributes, which is (7.13) — the section's only numbered equation.
#disp[#table(
  columns: (7.2cm, 5.0cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

  [`F(A,X)=A+A×X`],
  [`𝒜×𝒜⟶𝒜`],
  [The base functor: one square of the new column, alone or in front of the path so far.],

  [`L=list⁺`],
  [`𝒜⟶𝒜`],
  [A path is a non-empty list of squares, one per column crossed.],

  [`α` the initial algebra],
  [`F(A,LA)⟶LA`],
  [`α=[wrap,cons]`: a path is started by one square, or extended by one.],

  [`N` \ the `n`-tuple relator],
  [`𝒜⟶𝒜`],
  [One component per row of a column, so the fold carries `n` answers at once.],

  [`R≜sum≤sum°`],
  [`L Nat⟶L Nat`],
  [The cost of a path, which the cheapest minimises.],

  [`setify`],
  [`NA⟶EA`],
  [Forgets which row a component came from, so the `n` answers become one set.],

  [`moves`],
  [`NA⟶E(NA)`],
  [The three columns a path may step to: rotated up, unrotated, rotated down.],

  [`trans`],
  [`E(NA)⟶N(EA)`],
  [Transposes a set of tuples, so every row collects its own paths.],

  [`zip`],
  [`F(NA,NB)⟶NF(A,B)`],
  [Commutes `N` with the base functor, pairing each new square with its own row's paths.],

  [`cp≜` $frac(#[`F(𝟙,∋)`], ∋)$],
  [`F(A,EB)⟶E(F(A,B))`],
  [Turns a square paired with a set of paths into the set of extensions of those paths.],

  [`generate≜F(𝟙,moves trans N(union)) zip N(cp P(α))`
 #src[]],
   // lean:AOP.A7_4_Cylinder.generate@4bd0bafd
  [`F(NA,N(E(LA)))⟶N(E(LA))`],
  [One fold step: extends every path of every row by the new column.],

 [`paths≜⦇generate⦈ setify union` #src[]],
  // lean:AOP.A7_4_Cylinder.paths@c16ad5b9
  [`L N Nat⟶E(L Nat)`],
  [Every path across the cylinder.],

  [the specification \ `paths est(R)`],
  [`L N Nat⟶L Nat`],
  [A cheapest path from the entry side to the exit side.],
)]<cyl-defn>

=== `N(E(L A))` <sec-cyl-nela>

#disp[#align(center, grid(
  columns: 2, column-gutter: 34pt, align: horizon,
  grid(columns: 2, column-gutter: 14pt, row-gutter: 5pt, align: center,
    [`1`], [`5`], [`2`], [`6`], [`3`], [`7`], [`4`], [`8`]),
  [`[(1,2,3,4),(5,6,7,8)] : L N Nat`],
))]<cyl-array>

// One raw block, not a grid: the four components line up because every glyph is one monospace
// advance wide, which no measured column can promise.
#disp[#align(center)[```
⦇generate⦈[(5,6,7,8)] = ({[5]},{[6]},{[7]},{[8]})

generate((1,2,3,4),({[5]},{[6]},{[7]},{[8]})) =
    ( {[1,5],[1,6],[1,8]},
      {[2,5],[2,6],[2,7]},
      {[3,6],[3,7],[3,8]},
      {[4,5],[4,7],[4,8]} )
```]]<cyl-generate>

#disp[#block(breakable: false)[
#table(
  columns: (2.0cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`N`],
  [the 4-tuple, one component per row of the entry column],

  [`E`],
  [the set of paths that can start in that row],

  [`L`],
  [a path is the non-empty list of the squares it crosses],
)
#align(center, block(width: 16.5cm, inset: (y: 4pt))[#src[row 1's set has no `[1,7]` — from row 1
  only rows 4, 1 and 2 are reachable — and it does have `[1,8]`, because the cylinder glues the
  bottom row to the top. That is `moves trans N(union)` of @cyl-defn: component `k` collects the
  paths of rows `k-1`, `k`, `k+1`.]])
]]<cyl-nela>

=== The derivation <sec-cyl-deriv>

// ---- §13.5.2's own vocabulary.  CIRCUIT: one wire, a box per factor of the composite, a cut
// corner for a relation and a square box for a map.
#let cb-paths = ([`paths`], 1.9, false)
#let cb-est = ([`est(R)`], 1.9, true)
#let cb-fold = ([`⦇generate⦈`], 3.6, false)
#let cb-setify = ([`setify`], 1.9, false)
#let cb-union = ([`union`], 1.75, false)
#let cb-Pest = ([`P(est(R))`], 3.0, true)
#let cb-Nest = ([`N(est(R))`], 3.0, true)
#let cb-foldQ = ([`⦇Q⦈`], 1.5, true)
#let cb-gen = ([`generate`], 2.7, false)
#let cb-FNest = ([`F(𝟙,N(est(R)))`], 4.4, true)
#let cb-Q = ([`Q`], 0.8, true)
#let cb-Fmtn = ([`F(𝟙,moves trans N(est(R)))`], 7.8, true)
#let cb-zip = ([`zip`], 1.3, false)
#let cb-Nal = ([`N(α)`], 1.7, false)
#let cb-Nwrap = ([`N(wrap)`], 2.4, false)
#let cb-moves = ([`moves`], 1.75, false)
#let cb-trans = ([`trans`], 1.75, false)
#let cb-zipp = ([`zip'`], 1.5, false)
#let cb-Ncons = ([`N(cons)`], 2.4, false)

#let cyp(body, s: 92%) = P(cetz.canvas(length: 0.8cm, body), s: s)
// The end names are ANCHORED, not centred at a hand-measured x: one of them is `F(NA,N(E(LA)))`
// and every row would otherwise need its own offset.
#let cyrun(lft, rgt, items) = {
  d.content((-0.2, 0), text(10pt)[#lft], anchor: "east")
  boxrun(0, 0, items)
  d.content((boxrun-w(items) + 0.2, 0), text(10pt)[#rgt], anchor: "west")
}
// The bracket at `F(NA,N(LA))=NA+NA×N(LA)`: the fork sends `NA` to the box above and the pair
// below, where `zip'` closes the two strands into one before the run that follows it.
#let CYBR = 1.40   // the bracket's branch height
#let CYSP = 0.45   // half the gap between the pair's strands
#let cyfork(up, lo, span, post) = {
  let cy = -CYBR
  let x0 = 1.26
  let runw(bs) = bs.map(b => b.at(1) + LEAD).sum(default: 0.0)
  let xs = x0 + runw(lo)
  let xj = calc.max(x0 + runw(up), xs + span.at(1) + runw(post)) + 0.7
  tape((0.34, cy - CYSP - 0.95), (xj, CYBR + 0.95))
  wire((0, 0), (0.34, 0))
  let st = (thickness: 1.4pt, paint: TAPEEDGE)
  d.bezier((0.56, 0), (x0, CYBR), (0.98, 0), (0.98, CYBR), stroke: st)
  d.bezier((0.56, 0), (x0, cy + CYSP), (0.98, 0), (0.98, cy + CYSP), stroke: st)
  d.bezier((0.56, 0), (x0, cy - CYSP), (0.98, 0), (0.98, cy - CYSP), stroke: st)
  let x = x0
  for b in up { gbox((x, CYBR), b.at(0), w: b.at(1), chamfer: b.at(2)); x = x + b.at(1) }
  wire((x, CYBR), (xj - 0.7, CYBR))
  // The head strand runs straight to `zip'`; the tail carries the run that `𝟙×−` acts on.
  wire((x0, cy + CYSP), (xs, cy + CYSP))
  x = x0
  for b in lo {
    gbox((x, cy - CYSP), b.at(0), w: b.at(1), chamfer: b.at(2)); x = x + b.at(1)
    wire((x, cy - CYSP), (x + LEAD, cy - CYSP)); x = x + LEAD
  }
  gbox((xs, cy), span.at(0), w: span.at(1), h: 2 * CYSP + 0.55, chamfer: span.at(2))
  x = xs + span.at(1)
  for b in post {
    wire((x, cy), (x + LEAD, cy)); x = x + LEAD
    gbox((x, cy), b.at(0), w: b.at(1), chamfer: b.at(2)); x = x + b.at(1)
  }
  wire((x, cy), (xj - 0.7, cy))
  tape-join((xj, 0), sp: CYBR, len: 0.7)
  wire((xj, 0), (xj + LEAD, 0))
  d.content((xj + LEAD + 0.2, 0), text(10pt)[`N(LA)`], anchor: "west")
  d.content((-0.35, CYBR), text(10pt)[`NA`], anchor: "east")
  d.content((-0.35, cy + CYSP), text(10pt)[`NA`], anchor: "east")
  d.content((-0.35, cy - CYSP), text(10pt)[`N(LA)`], anchor: "east")
}

// ---- HINZE–MARSDEN.  A wire is a FUNCTOR, so the object wire carries `L N Nat` down to `L Nat`
// and the two set functors ride beside it: `N` the fold's tuple, `E` the path set inside it.
#let CAN = 1.80    // the `N` the fold builds, which `setify` renames `E`
#let CAE = 2.70    // the `E` inside it, where a set of paths lives
#let CAO = 4.90    // the object wire
#let CAW = 8.50
#let CAH = 5.05
#let CY5 = 4.30    // the fold
#let CY4 = 3.30    // `est(R)` under `N`
#let CY3 = 2.45    // `setify`
#let CY2 = 1.60    // `union`, or `est(R)` under `E`
#let CY1 = 0.75    // the last `est(R)`
#let CKN = 0.45    // the knee, shortened on an arc too flat to carry it twice
// An arc is `(x, y0, y1, xe)`: a wire born at `y0` on the object wire, run out to lane `x`, landed
// at `y1` on `xe` (`none` = back on the object wire).  A bead's `sd` is which side its name takes.
#let cypan(arcs, beads, names, reg: false) = dpan(CAH, CAW, CAO, {
  for (x, y0, y1, xe) in arcs {
    let k = calc.min(CKN, (y0 - y1) / 3)
    hm-wire(((CAO, y0), (x, y0 - k), (x, y1 + k), (if xe == none { CAO } else { xe }, y1)))
  }
  for (x, y, l) in names { hm-name((x, y), l) }
  for (x, y, l, sd) in beads {
    hm-bead((x, y), l, dx: sd, anchor: if sd > 0 { "west" } else { "east" })
  }
  hm-port((CAO, CAH), [`L N Nat`], col: BCOL)
  hm-port((CAO, 0), [`L Nat`], dir: -1, col: BCOL)
  if reg { hm-name((4.05, 0.25), [`Rel`]); hm-name((5.55, 0.25), [`𝟏`]) }
}, s: 78%)
#let ca1 = cypan(((CAE, CY5, CY1, none),),
  ((CAO, CY5, [`paths`], 0.32), (CAO, CY1, [`est(R)`], 0.32)),
  ((CAE - 0.30, 2.60, [`E`]),), reg: true)
#let ca2 = cypan(((CAE, CY5, CY1, none), (CAN, CY5, CY2, CAE)),
  ((CAO, CY5, [`⦇generate⦈`], 0.32), (CAN, CY3, [`setify`], -0.32), (CAE, CY2, [`union`], 0.32),
   (CAO, CY1, [`est(R)`], 0.32)),
  ((CAE - 0.30, 3.30, [`E`]), (CAN - 0.30, 3.30, [`N`]), (CAN + 0.30, 1.95, [`E`])))
#let ca3 = cypan(((CAE, CY5, CY2, none), (CAN, CY5, CY1, none)),
  ((CAO, CY5, [`⦇generate⦈`], 0.32), (CAN, CY3, [`setify`], -0.32), (CAO, CY2, [`est(R)`], 0.32),
   (CAO, CY1, [`est(R)`], 0.32)),
  ((CAE - 0.30, 3.30, [`E`]), (CAN - 0.30, 3.30, [`N`]), (CAN + 0.30, 1.95, [`E`])))
#let ca4 = cypan(((CAE, CY5, CY4, none), (CAN, CY5, CY1, none)),
  ((CAO, CY5, [`⦇generate⦈`], 0.32), (CAO, CY4, [`est(R)`], 0.32), (CAN, CY3, [`setify`], -0.32),
   (CAO, CY1, [`est(R)`], 0.32)),
  ((CAE - 0.40, 3.80, [`E`]), (CAN - 0.30, 2.90, [`N`]), (CAN + 0.30, 1.95, [`E`])))
#let ca5 = cypan(((CAN, CY5, CY1, none),),
  ((CAO, CY5, [`⦇Q⦈`], 0.32), (CAN, CY3, [`setify`], -0.32), (CAO, CY1, [`est(R)`], 0.32)),
  ((CAN - 0.30, 3.30, [`N`]), (CAN + 0.30, 1.95, [`E`])))

// B&dM §7.4, p. 182.  The `E` the fold builds is killed earlier at every step, until @cyl-step's
// algebra never builds it: that migration is what the right column draws.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`paths est(R)⊒⦇Q⦈ setify est(R)` \ #src[B&dM §7.4, p. 182; `Q` is @cyl-step's algebra,
 ]],
    // lean:AOP.A7_4_Cylinder.cyl_laws@6fc8d336
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], cyp(cyrun([`L N Nat`], [`L Nat`], (cb-paths, cb-est))), [`paths est(R)`])],
  [#ca1],

  [#vstep(EQ, cyp(cyrun([`L N Nat`], [`L Nat`], (cb-fold, cb-setify, cb-union, cb-est))),
    [`⦇generate⦈ setify union est(R)` \ #src[@cyl-defn at `paths`]])],
  [#ca2],

  [#vstep(RQ, cyp(cyrun([`L N Nat`], [`L Nat`], (cb-fold, cb-setify, cb-Pest, cb-est))),
    [`⦇generate⦈ setify P(est(R)) est(R)` \ #src[@est-laws at `union`, `R` a preorder]])],
  [#ca3],

  [#vstep(RQ, cyp(cyrun([`L N Nat`], [`L Nat`], (cb-fold, cb-Nest, cb-setify, cb-est))),
    [`⦇generate⦈N(est(R)) setify est(R)` \ #src[`setify` lax natural]])],
  [#ca4],

  [#vstep(RQ, cyp(cyrun([`L N Nat`], [`L Nat`], (cb-foldQ, cb-setify, cb-est))),
    [`⦇Q⦈ setify est(R)` \ #src[@cata-fusion at @cyl-fusion]])],
  [#ca5],
))]<cyl-laws>

// ---- Chains B and C.  `F` is CURRIED to the unary `F(NA,−)`, so its wire is a functor and the
// algebra may die ON `N` instead of reaching past it; `trans` and `zip` are the only crossings left.
#let CL1 = 0.65
#let CL2 = 1.55
#let CL3 = 2.45
#let CBO = 4.60
#let CBW = 7.60
#let cbpan(h, wires, beads, top, bot) = dpan(h, CBW, CBO, {
  for pts in wires { hm-wire(pts) }
  for (x, y, l, sd) in beads {
    hm-bead((x, y), l, dx: sd, anchor: if sd > 0 { "west" } else { "east" })
  }
  for (x, l) in top { hm-port((x, h), l, col: if x == CBO { BCOL } else { black }) }
  for (x, l) in bot { hm-port((x, 0), l, dir: -1, col: if x == CBO { BCOL } else { black }) }
}, s: 78%)
// Tall enough that `F(NA,−)` gets a straight run under its port label before it turns onto `N`.
#let CBH = 4.40
// `est(R)` is the one bead BOTH sides carry, so it keeps the middle row and the base functor's own
// bead travels down past it: `generate` above it on the left, `Q` below it on the right.
#let CBHI = 3.00
#let CBMD = 1.95
#let CBLO = 0.90
// Chain B's own lanes: the wide `F(NA,−)` port label and `generate`'s, left of its bead on `N`,
// both need room chain C's evenly spaced lanes have no use for.
#let CB1 = 0.65
#let CB2 = 2.25
#let CB3 = 3.15
#let cb-top = ((CB1, [`F(NA,−)`]), (CB2, [`N`]), (CB3, [`E`]), (CBO, [`LA`]))
#let cb-bot = ((CB2, [`N`]), (CBO, [`LA`]))
#let cb1 = cbpan(CBH,
  (((CB1, CBH), (CB1, CBHI + 0.95), (CB2, CBHI)), ((CB2, CBH), (CB2, 0)),
   ((CB3, CBH), (CB3, CBMD + 0.6), (CBO, CBMD))),
  ((CB2, CBHI, [`generate`], -0.32), (CBO, CBMD, [`est(R)`], 0.32)), cb-top, cb-bot)
#let cb2 = cbpan(CBH,
  (((CB1, CBH), (CB1, CBLO + 0.95), (CB2, CBLO)), ((CB2, CBH), (CB2, 0)),
   ((CB3, CBH), (CB3, CBMD + 0.6), (CBO, CBMD))),
  ((CBO, CBMD, [`est(R)`], 0.32), (CB2, CBLO, [`Q`], -0.32)), cb-top, cb-bot)

// B&dM §7.4, p. 183.  `generate` kills the base functor before the minimum is taken inside the
// tuple; the right-hand side kills it after, and that swap is the whole step.
#disp[
#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`generate N(est(R))⊒F(𝟙,N(est(R)))Q` \ #src[the fusion condition of @cyl-laws's last step,
 ]],
    // lean:AOP.A7_4_Cylinder.cyl_fusion@d69b5189
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], cyp(cyrun([`F(NA,N(E(LA)))`], [`N(LA)`], (cb-gen, cb-Nest)), s: 88%),
    [`generate N(est(R))`])],
  [#cb1],

  [#vstep(RQ, cyp(cyrun([`F(NA,N(E(LA)))`], [`N(LA)`], (cb-FNest, cb-Q)), s: 88%),
    [`F(𝟙,N(est(R)))Q` \ #src[(7.13), then `zip`, `trans`, `moves` lax natural]])],
  [#cb2],
))
#align(center, block(inset: (y: 4pt))[#src[(7.13) is `F(𝟙,est(R))α⊑cp P(α) est(R)`, @mon-thm71 at the
  map `α` with $frac(#[`F(𝟙,∋)α`], ∋)$ `=cp P(α)`: extending every path in a set and then taking a
  minimum is beaten by extending one minimum. It is the crux here, not the greedy theorem.
 ]])
  // lean:AOP.A7_4_Cylinder.cyl_7_13@5224efdc
]<cyl-fusion>

#let CC5 = 4.30    // `moves`, where the `E` is born
#let CC4 = 3.45    // `trans`, where it crosses `N`
#let CC3 = 2.60    // `est(R)` under `N`, where it dies
#let CC2 = 1.70    // `zip`, where `F` crosses `N`
#let CC1 = 0.85    // `α`, where `F` dies
#let cc-bot = ((CL1, [`N`]), (CBO, [`LA`]))
#let cc1 = cbpan(2.60,
  (((CL1, 2.60), (CL1, 1.85), (CL3, 0.95)), ((CL3, 2.60), (CL3, 0))),
  ((CL3, 0.95, [`Q`], -0.32),),
  ((CL1, [`F(NA,−)`]), (CL3, [`N`]), (CBO, [`LA`])), ((CL3, [`N`]), (CBO, [`LA`])))
// `zip` is the one crossing that RE-INDEXES the curried wire — `F(NA,−)N⇒N F(A,−)` — so below it
// the `F` wire is `F(A,−)`, which is the wire `N(α)` kills on the object wire.
#let cc2 = cbpan(5.05,
  (((CL3, 5.05), (CL3, CC4 + 0.42), (CL2, CC4 - 0.42), (CL2, CC2 + 0.45), (CL1, CC2 - 0.45),
    (CL1, 0)),
   ((CL3, CC5), (CL2, CC5 - 0.45), (CL2, CC4 + 0.42), (CL3, CC4 - 0.42), (CL3, CC3 + 0.5),
    (CBO, CC3)),
   ((CL1, 5.05), (CL1, CC2 + 0.45), (CL2, CC2 - 0.45), (CL2, CC1 + 0.5), (CBO, CC1))),
  ((CL3, CC5, [`moves`], 0.32), ((CL2 + CL3) / 2, CC4, [`trans`], 0.75), (CBO, CC3, [`est(R)`], 0.32),
   ((CL1 + CL2) / 2, CC2, [`zip`], 0.75), (CBO, CC1, [`α`], 0.32)),
  ((CL1, [`F(NA,−)`]), (CL3, [`N`]), (CBO, [`LA`])), cc-bot)

// B&dM §7.4, p. 183.  Read as a definition, the fusion condition names `Q`; opening the coproduct
// of maps turns it into the program.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`Q=[N(wrap),(𝟙×moves trans N(est(R))) zip' N(cons)]` \
 #src[the algebra @cyl-laws's last step folds]],
    // lean:AOP.A7_4_Cylinder.cyl_step@4930da05
  table.header([*circuit* — the fork is `F(NA,N(LA))=NA+NA×N(LA)`], [*Hinze–Marsden*]),

  [#vstep([], cyp(cyrun([`F(NA,N(LA))`], [`N(LA)`], (cb-Q,)), s: 88%), [`Q`])],
  [#cc1],

  [#vstep(EQ, cyp(cyrun([`F(NA,N(LA))`], [`N(LA)`], (cb-Fmtn, cb-zip, cb-Nal)), s: 74%),
    [`F(𝟙,moves trans N(est(R))) zip N(α)` \ #src[the fusion condition read as a definition,
 ]])],
     // lean:AOP.A7_4_Cylinder.Q@2b4dd374
  [#cc2],

  [#vstep(EQ, cyp(cyfork((cb-Nwrap,), (cb-moves, cb-trans, cb-Nest), cb-zipp, (cb-Ncons,)), s: 78%),
    [`[N(wrap),(𝟙×moves trans N(est(R))) zip' N(cons)]` \ #src[`zip=𝟙+zip'`, `α=[wrap,cons]`]])],
  // A coproduct is a case split, not a composite of functors: Hinze–Marsden has no wiring for it.
  [],
))]<cyl-step>

// Its own page: the section opens with a long definition display and was starting mid-page.
#pagebreak(weak: true)
== The security van problem

// B&dM §7.5, p. 184.  `Π`, the universal relation, is this note's `⊤`; the p. 187 printing of the
// greedy result puts `wrap wrap` where p. 185 and the final program both put `nil`.
#disp[#table(
  columns: (8.0cm, 4.7cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

 [`R≜length≤length°` #src[]],
  // lean:AOP.A7_5_Van.R_eq@fa26242d
  [`[[Int]]⟶[[Int]]`],
  [The order the schedule is minimised over: fewer van visits is better.],

  [`ceiling≜` $frac(#[`prefix sum`], ∋)$ `est(≥)`],
  [`[Int]⟶Int`],
  [The highest the bank's balance reaches over a stretch of transactions.],

  [`floor≜` $frac(#[`prefix sum`], ∋)$ `est(≤)`],
  [`[Int]⟶Int`],
  [The lowest it reaches, so `ceiling−floor` is the cash the stretch has to carry.],

  [`secure` \ the coreflexive on `x` with \ `bmax(ceiling x,ceiling x−floor x)≤N`],
  [`[Int]⟶[Int]`],
  [The stretches one van visit can serve: some starting reserve keeps the cash between `0` and `N`.],

  [`ok` \ the coreflexive on `(a,xs)` with `xs` non-empty and `[a]⧺head xs` secure],
  [`Int×[[Int]]` \ `⟶Int×[[Int]]`],
  [The test the final program runs, in place of `old`'s `secure`.],

  [`new≜(wrap×𝟙) cons`],
  [`Int×[[Int]]⟶[[Int]]`],
  [Calls the van: the transaction opens a segment of its own.],

  [`glue≜(𝟙×cons°) assocl (cons×𝟙) cons`],
  [`Int×[[Int]]⟶[[Int]]`],
  [Puts the transaction on the front of the first segment.],

  [`old≜(𝟙×cons°) assocl` \
   `((cons secure)×𝟙) cons`],
  [`Int×[[Int]]⟶[[Int]]`],
  [`glue` restricted to a first segment that stays secure.],

  [`partition=⦇[nil,new∪glue]⦈`],
  [`[Int]⟶[[Int]]`],
  [Every splitting of the transactions into consecutive segments.],

  [`S≜[nil,new∪old]`],
  [`1+Int×[[Int]]⟶[[Int]]`],
  [The algebra whose fold is every splitting of the transactions into secure segments.],

 [`partition list(secure)=⦇S⦈` #src[]],
  // lean:AOP.A7_5_Van.van_spec@79d2f560
  [`[Int]⟶[[Int]]`],
  [Fusion: keeping only secure segments is what turns `glue` into `old`.],

 [`H≜(head prefix° head°)∪(nil° nil)` #src[]],
  // lean:AOP.A7_5_Van.H_eq@b1cf5141
  [`[[Int]]⟶[[Int]]`],
  [One schedule's first segment is a prefix of the other's, or both are empty.],

 [`R;H≜R∩(R°⇒H)` #src[]],
  // lean:AOP.A7_5_Van.RH_eq@ddc8b9dc
  [`[[Int]]⟶[[Int]]`],
  [The refinement of `R` that makes both halves of `S` monotonic.],

  [`|R|≜R∩¬R°`],
  [`[[Int]]⟶[[Int]]`],
  [The strict part `R` splits into: `R;H=|R|∪(R∩H)`.],

  [the specification \ $frac(#[`partition list(secure)`], ∋)$ `est(R)`],
  [`[Int]⟶[[Int]]`],
  [A schedule with the fewest secure segments.],
)]<van-defn>

// B&dM §7.5, pp. 186–188: the specification down to the program.  ONE WIRE, `[Int]` to `[[Int]]`:
// nothing forks, so a row is a run of boxes and what changes is the box the wire runs through.  A
// fraction is a map (@pow-laws), hence a square box; `est` and the folds that carry one are the
// chain's relations, hence chamfered.
#let vb-spec = (frc([`partition list(secure)`]), 7.6, false)
#let vb-LS = (frc([`⦇S⦈`]), 1.5, false)
#let vb-estR = ([`est(R)`], 2.0, true)
#let vb-estRH = ([`est(R;H)`], 2.6, true)
#let vb-greedy = ([`⦇`#frc([`S`])` est(R;H)⦈`], 4.0, true)
#let vb-prog = ([`⦇[nil,(ok→glue,new)]⦈`], 6.2, false)
#let van-line(items) = {
  lab(-0.82, 0, black)[`[Int]`]; boxrun(0, 0, items, h: TH)
  lab(boxrun-w(items) + 1.05, 0, black)[`[[Int]]`]
}
#let van-pic(body) = P(cetz.canvas(length: 0.8cm, body), s: 78%)

// The same lanes as §13.4.4's panels, at this section's types: `[[Int]]` is TWO `list` wires beside
// the `Int` one, and the outer `list` is born where the partition is.  A bead whose source and target
// differ by one outermost functor kills just that wire (`est` the `E`); an ALGEBRA rebuilds the type,
// so every strand lands on it and the ones it returns are born there.
#let VXE = 0.55                  // `E`, opened by the singleton and closed by an `est`
#let VXLo = 1.70                 // `list`, the segments
#let VXLi = 2.85                 // `list`, the transactions in one segment
#let VXO = 4.00                  // the object wire, `Int`
#let VXW = VXO + 2.85
#let INT = [`Int`]
#let van-top = ((VXLi, LIST), (VXO, INT))
#let van-bot = ((VXLo, LIST), (VXLi, LIST), (VXO, INT))
#let v-hm1 = dpanel(4.0, VXW, VXO,
  ((VXE, 3.30, 0.95, EW, UNIT), (VXLi, "top", 2.60, none, none),
   (VXLo, 2.60, "bot", none, none), (VXLi, 2.60, "bot", none, none)),
  ((2.60, [`partition`]), (1.85, [`secure`], black, VXLi), (0.95, [`est(R)`], black, VXLo)),
  van-top, van-bot, names: true)
#let van-fold(h, y, l, e) = dpanel(h, VXW, VXO,
  (((VXE, 3.30, 0.95, EW, UNIT),) * (if e == none { 0 } else { 1 })
   + ((VXLi, "top", y, none, none), (VXLo, y, "bot", none, none), (VXLi, y, "bot", none, none))),
  ((y, l),) + (if e == none { () } else { ((0.95, e, black, VXLo),) }), van-top, van-bot)

// `(𝟙×X)old` and `old X`: the transaction runs straight past the box on the list wire — that pass is
// the `𝟙×` — and `old` spans the pair.  A PRODUCT IS TWO WIRES.
#let vb-RH = ([`R;H`], 1.65, true)
#let vb-sR = ([`|R|`], 1.4, true)
#let vb-RH2 = ([`R∩H`], 1.85, true)
#let van-old(pre, post) = {
  let y = 0.62
  let w = boxrun-w(pre)
  lab(-0.62, y, black)[`Int`]; lab(-1.15, -y, black)[`[[Int]]`]
  wire((0, y), (w, y))
  boxrun(0, -y, pre)
  gbox((w, 0), [`old`], w: 1.35, h: 2 * y + 0.42)
  boxrun(w + 1.35, 0, post)
  lab(w + 1.35 + boxrun-w(post) + 1.05, 0, black)[`[[Int]]`]
}
// `Int×−` is a wider name than `list`, so its lane keeps a wider gap: the port labels are written at
// the panel's top edge and two of them touching read as one name.
#let VMM = 0.55                  // `Int×−`, the base functor's own factor
#let VMLo = 2.10
#let VMLi = 3.25
#let VMO = 4.40
// `old` holds ONE height in all four panels and the wires land on it the same way: what moves is the
// relation, from above the algebra to below it, which is the whole of (7.17).
#let van-mono-hm(l, above) = dpanel(3.8, VMO + 2.85, VMO,
  ((VMM, "top", 1.95, none, none), (VMLo, "top", 1.95, none, none), (VMLi, "top", 1.95, none, none),
   (VMLo, 1.95, "bot", none, none), (VMLi, 1.95, "bot", none, none)),
  ((1.95, [`old`]), (if above { 2.85 } else { 1.05 }, l, black, VMLo)),
  ((VMM, [`Int×−`]), (VMLo, LIST), (VMLi, LIST), (VMO, INT)),
  ((VMLo, LIST), (VMLi, LIST), (VMO, INT)))

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`partition list(secure)`])` est(R)⊒⦇[nil,(ok→glue,new)]⦈` \
    #src[the fewest secure segments the transactions can be cut into are one pass along them, the
     next transaction glued onto the open segment wherever that segment stays secure and the van
 called where it does not]],
     // lean:AOP.A7_5_Van.van_laws@400440f3
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], van-pic(van-line((vb-spec, vb-estR))),
    [#frc([`partition list(secure)`])` est(R)` \ #src[the specification — @van-defn]])],
  [#v-hm1],

  [#vstep(EQ, van-pic(van-line((vb-LS, vb-estR))),
    [#frc([`⦇S⦈`])` est(R)` \ #src[`partition list(secure)=⦇S⦈`
 #h(4pt) — @van-defn, @cata-fusion at
     // lean:AOP.A7_5_Van.van_spec@79d2f560
     `secure prefix⊑prefix secure`]])],
  [#van-fold(4.0, 2.20, [`⦇S⦈`], [`est(R)`])],

  [#vstep(RQ, van-pic(van-line((vb-LS, vb-estRH))),
    [#frc([`⦇S⦈`])` est(R;H)` \ #src[`R;H⊑R` — @van-defn; (7.15) `(𝟙×R)old⊑(new∪old)R` is FALSE, the
     shorter partition need not stay secure, where (7.14) `(𝟙×R)new⊑(new∪old)R` holds,
 ]])],
     // lean:AOP.A7_5_Van.van_7_15_false@1b163187 lean:AOP.A7_5_Van.van_7_14@31454849
  [#van-fold(4.0, 2.20, [`⦇S⦈`], [`est(R;H)`])],

  [#vstep(RQ, van-pic(van-line((vb-greedy,))),
    [`⦇`#frc([`S`])` est(R;H)⦈` \ #src[@greedy-thm72 at `R;H`, its hypothesis `F(R;H)S⊑S(R;H)`
     the `old` half (7.17) — @van-mono — and the `new` half (7.16), which rests on (7.18)
 `(𝟙×⊤)new⊑new H`]])],
     // lean:AOP.A7_5_Van.van_mono_new@ca4101c9
  [#van-fold(3.4, 2.20, [`⦇`#frc([`S`])` est(R;H)⦈`], none)],

  [#vstep(RQ, van-pic(van-line((vb-prog,))),
    [`⦇[nil,(ok→glue,new)]⦈` \ #src[`old⊑new (R;H)°`: `old` returns the shorter result wherever it
 returns one, and `ok` is where it does]])],
     // lean:AOP.A7_5_Van.prog_le_greedy@9203a952
  [#van-fold(3.4, 2.20, [`⦇[nil,(ok→glue,new)]⦈`], none)],
))]<van-laws>

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`(𝟙×(R;H))old⊑(new∪old)(R;H)` \
    #src[gluing the transaction onto a better schedule for the rest gets no further than gluing it
     on, or calling the van, and bettering the whole schedule after,
 ]],
     // lean:AOP.A7_5_Van.van_mono@5f456bbf
  table.header([*circuit* — the `old` branch of each union], [*Hinze–Marsden*]),

  [#vstep([], van-pic(van-old((vb-RH,), ())), [`(𝟙×(R;H))old`])],
  [#van-mono-hm([`R;H`], true)],

  [#vstep(EQ, van-pic(van-old((vb-sR,), ())),
    [`(𝟙×|R|)old∪(𝟙×(R∩H))old` \ #src[`R;H=|R|∪(R∩H)` — @van-defn, `∪` distributes,
 ]])],
     // lean:AOP.A7_5_Van.RH_eq_strict@63c91c5e
  [#van-mono-hm([`|R|`], true)],

  [#vstep(SQ, van-pic(van-old((), (vb-RH2,))),
    [`new (R∩H)∪old (R∩H)` \ #src[(7.19) and (7.20) on `|R|`, (7.21) on `R∩H`]])],
  [#van-mono-hm([`R∩H`], false)],

  [#vstep(SQ, van-pic(van-old((), (vb-RH,))),
    [`(new∪old)(R;H)` \ #src[`X∩Y⊑X;Y`, converses]])],
  [#van-mono-hm([`R;H`], false)],
))]<van-mono>

#pagebreak(weak: true)
= Thinning Algorithms <sec-thin>

// ---- §14's own vocabulary.  CIRCUIT: one wire, a box per factor; a reduce whose ALGEBRA a step
// rewrites is MELLIÈS' functorial box, with the algebra's own run inside it.
#let THY = 0.95                                   // the functorial box's half-height, clear of `TH`
#let thpic(lft, rgt, alg, tail, s: 76%) = P(cetz.canvas(length: 0.8cm, {
  d.content((-0.30, 0), text(10pt)[#lft], anchor: "east")
  let x = 0.0
  if alg != none {
    banana(0, THY); boxrun(0.13, 0, alg, h: TH)
    x = 0.26 + boxrun-w(alg); banana(x, THY, right: true)
  }
  boxrun(x, 0, tail, h: TH)
  d.content((x + boxrun-w(tail) + 0.30, 0), text(10pt)[#rgt], anchor: "west")
}), s: s)

// ---- HINZE–MARSDEN.  A WIRE IS A FUNCTOR: `[A]` is the `list` wire beside the `A` wire, at the
// ENDS as much as in the middle, and `E` is born by the unit `𝟙%∋` — a bead with a free upper end.
// A counit may only land on the object wire when nothing is left outside it; where a datatype
// survives (`est(R) : E(LA)⟶LA`) the wire ends on its own lane, since bending in would CROSS it.
// A bead sits on the wire it CHANGES: a functor wire when it only rearranges that functor, the
// object wire when it changes the value.  Lane labels run west, object-wire labels east.
#let THU = 1.90                                   // the set the transpose opens, outside everything
#let THM = 2.65                                   // the datatype under it
#let THN = 3.40                                   // a second one, inside the first
#let THO = 5.40                                   // the object wire
#let THW = 11.4
// A wire ENDING on the object wire at `y1`, arriving down lane `x` from `y0`; `out` is the mirror,
// born on the object wire at `y0` and leaving down its own lane; `arc` is both at once.
#let thw-in(x, y0, y1) = ((x, y0), (x, y1 + KNEE), (THO, y1))
#let thw-out(x, y0, y1) = ((THO, y0), (x, y0 - KNEE), (x, y1))
#let thw-arc(x, y0, y1) = ((THO, y0), (x, y0 - KNEE), (x, y1 + KNEE), (THO, y1))
#let thpan(h, wires, beads, top, bot, lanes: (), names: false, w: THW) = dpan(h, w, THO, {
  for pts in wires { hm-wire(pts) }
  for (x, y, l) in lanes { hm-name((x, y), l) }
  for (x, y, l, sd) in beads {
    hm-bead((x, y), l, dx: sd, anchor: if sd > 0 { "west" } else { "east" })
  }
  // A port's third slot is its gap from the edge: two lanes 0.75 apart cannot both carry `list⁺`
  // on one line, so one of them is dropped clear of the other.
  for p in top {
    hm-port((p.at(0), h), p.at(1), col: if p.at(0) == THO { BCOL } else { black },
      gap: p.at(2, default: 0.28))
  }
  for p in bot {
    hm-port((p.at(0), 0), p.at(1), dir: -1, col: if p.at(0) == THO { BCOL } else { black },
      gap: p.at(2, default: 0.28))
  }
  if names { hm-name((THO - 0.70, 0.26), [`Rel`]); hm-name((THO + 0.80, 0.26), [`𝟏`]) }
}, s: 63%)

== Thinning

// B&dM §8.1, p. 193.  Between the two extremes of the last section: `𝟙` keeps every partial solution
// and `est(Q) (𝟙%∋)` keeps one, `thin Q` keeps a representative collection.
#disp[#definition[
For `Q : A⟶A`, #h(4pt) `thin Q≜(∋/∋)∩(∈\(Q°∈)) : EA⟶EA` #h(4pt) #src[(8.1)].

`ys (thin Q) xs⟺xs⊆ys∧(∀a∈ys. ∃b∈xs. b Q a)` #src[]
// lean:rel.AutoDeriveThin.thinRel_pt@dec7230e
]]<thin-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X⊑` $frac(#[`S`], ∋)$ `thin Q⟺X∋⊑S` and `S°X⊑Q°∈`],
  [everything kept is an `S`-value, and every `S`-value has a `Q`-lower bound among the kept ones],
  [`Q⊑R⟹thin Q⊑thin R`],
  [the fewer pairs `Q` relates, the fewer subsets count as thinnings],
  [`𝟙⊑thin Q`, and `thin Q` is a preorder if `Q` is],
  [keeping everything is always a legal thinning],
  [`est(R)=thin Q est(R)` #h(4pt) #src[`Q⊑R`, both preorders]],
  [*thin-introduction*: thinning first cannot lose an `R`-minimum],
  [`thin Q⊒est(Q)` $frac(#[`𝟙`], ∋)$ #h(6pt)
 #src[(8.2)]],
   // lean:AOP.A8_1.est_comp_singletonMap_le_thinRel@663394c4
  [*thin-elimination*: keeping one element is a thinning, but its domain is the sets `est(Q)` is
   defined on],
  [$frac(#[`S`], ∋)$ `thin Q⊒` $frac(#[`S`], ∋)$ `est(R)` $frac(#[`𝟙`], ∋)$ \
   #src[(8.3), `R∩(S°S)⊑Q` — @thin-83]],
  [the usable variant: `R` need only refine `Q` between values `S` gives one argument],
  [`union thin Q⊒P(thin Q) union` #h(6pt) #src[(8.4)]],
  [thinning each member set is a thinning of the union],
)]<thin-laws>

// B&dM (8.3), p. 194, mirrored.  The first of the two conditions cancels the singleton against `∋`;
// the second is the chain, and the context row is where the side condition enters.
#let eb-So = ([`S°`], 0.85, true)
#let eb-LamS = (frc([`S`]), 1.0, false)
#let eb-est = ([`est(R)`], 1.9, true)
#let eb-estc = ([`est(R∩S°S)`], 3.1, true)
#let eb-tau = (frc([`𝟙`]), 1.0, false)
#let eb-Qo = ([`Q°`], 0.85, true)
#let eb-in = ([`∈`], 0.75, true)
#let eb-pic(tail) = thpic([`A`], [`EA`], none, tail)
// TWO `E` wires on one lane, never live at once: the transpose opens one that `est(R)` closes, and
// the singleton opens the one that leaves the panel.
#let eb-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THO, [`A`]),), ((THU, [`E`]), (THO, [`A`])), lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`S`])` thin Q⊒`#frc([`S`])` est(R) `#frc([`𝟙`]) \
    #src[keeping one `R`-least of the `S`-values is a thinning, once `R` refines `Q` between the
     values `S` gives one argument — (8.3), p. 194, `R∩(S°S)⊑Q`, `Q` a preorder
 #h(4pt) ]],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_le_thinRel@d22de9c7
  table.header([*circuit* — one wire, `A` to `EA`], [*Hinze–Marsden*]),

  [#vstep([], [],
    [#frc([`S`])` est(R) `#frc([`𝟙`])`∋⊑S` #h(10pt) and #h(10pt)
     `S°`#frc([`S`])` est(R) `#frc([`𝟙`])`⊑Q°∈` \
     #src[@thin-laws at `X≜`#frc([`S`])` est(R) `#frc([`𝟙`])]])],
  // A conjunction has no shape in either calculus.
  [],

  [#vstep(IMP, eb-pic((eb-So, eb-LamS, eb-est, eb-tau)),
    [`S°`#frc([`S`])` est(R) `#frc([`𝟙`]) \
     #src[the first is #frc([`𝟙`])`∋=𝟙` — @pow-laws — then #frc([`S`])` est(R)=S∩(S°\R°)⊑S` —
      @est-laws; the second is this chain, `−⊑Q°∈`]])],
  [#eb-pan(4.6, (thw-in(THU, 3.30, 1.60), ((THU, 0.80), (THU, 0))),
    ((THO, 4.00, [`S°`], 0.32), (THU, 3.30, frc([`𝟙`]), -0.32), (THO, 2.60, [`S`], 0.32),
     (THO, 1.60, [`est(R)`], 0.32), (THU, 0.80, frc([`𝟙`]), -0.32)),
    lanes: ((THU - 1.05, 2.45, [`E`]),), names: true)],

  [#vstep(EQ, eb-pic((eb-So, eb-LamS, eb-estc, eb-tau)),
    [`S°`#frc([`S`])` est(R∩S°S) `#frc([`𝟙`]) \
     #src[#frc([`S`])` est(R)=`#frc([`S`])` est(R∩S°S)` — @est-laws]])],
  // Empty: the wiring is the row above's, with one bead renamed.
  [],

  [#vstep(SQ, eb-pic((eb-in, eb-estc, eb-tau)),
    [`∈ est(R∩S°S) `#frc([`𝟙`]) \
     #src[`S°`#frc([`S`])`⊑∈`, since #frc([`S`])`∋=S` with #frc([`S`]) a map — @pow-laws]])],
  [#eb-pan(4.0, (thw-arc(THU, 3.10, 1.60), ((THU, 0.80), (THU, 0))),
    ((THO, 3.10, [`∈`], 0.32), (THO, 1.60, [`est(R∩S°S)`], 0.32),
     (THU, 0.80, frc([`𝟙`]), -0.32)),
    lanes: ((THU - 1.05, 2.35, [`E`]),))],

  [#vstep(SQ, eb-pic((eb-Qo, eb-tau)),
    [`Q° `#frc([`𝟙`]) \
     #src[`∈ est(R∩S°S)⊑(R∩S°S)°` — @est-up at `X≜est(R∩S°S)`, conversed — then `R∩(S°S)⊑Q`]])],
  [#eb-pan(3.0, (((THU, 1.10), (THU, 0)),),
    ((THO, 2.10, [`Q°`], 0.32), (THU, 1.10, frc([`𝟙`]), -0.32)))],

  [#vstep(SQ, eb-pic((eb-Qo, eb-in)),
    [`Q°∈` \ #src[#frc([`𝟙`])`⊑∈`, since #frc([`𝟙`])`∋=𝟙` with #frc([`𝟙`]) a map — @pow-laws]])],
  [#eb-pan(3.0, (thw-out(THU, 1.10, 0),),
    ((THO, 2.10, [`Q°`], 0.32), (THO, 1.10, [`∈`], 0.32)))],
))]<thin-83>

// B&dM Theorem 8.1, p. 195, mirrored.  The proof is about the SECOND half of `thin`'s universal
// property: the first half is fusion, and the hylomorphism theorem turns the second into one chain.
#let nb-So = ([`S°`], 0.85, true)
#let nb-FQin = ([`F(Q°∈)`], 2.15, true)
#let nb-Fin = ([`F(∈)`], 1.45, true)
#let nb-LamS = (frc([`F(∋)S`]), 2.05, false)
#let nb-thin = ([`thin Q`], 1.9, true)
#let nb-Qo = ([`Q°`], 0.85, true)
#let nb-in = ([`∈`], 0.75, true)
#let nb-pic(tail) = thpic([`A`], [`EA`], none, tail)
// TWO `E` wires, and that is the content: the one `∈` opens INSIDE `F`, and the transpose's own,
// opened outside everything by the unit and carried out of the panel by `thin Q`.
#let nb-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THO, [`A`]),), ((THU, [`E`]), (THO, [`A`])), lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`⦇`#frc([`F(∋)S`])` thin Q⦈⊑`#frc([`⦇S⦈`])` thin Q` \
    #src[thinning at every step of the reduce is a thinning of the whole candidate set —
     Theorem 8.1, p. 195, `S` monotonic on `Q`, `Q` a preorder
 #h(4pt) ]],
     // lean:AOP.A8_1.thinning@db624922
  table.header([*circuit* — one wire, `A` to `EA`], [*Hinze–Marsden*]),

  [#vstep([], [],
    [`⦇`#frc([`F(∋)S`])` thin Q⦈∋⊑⦇S⦈` #h(10pt) and #h(10pt)
     `⦇S⦈°⦇`#frc([`F(∋)S`])` thin Q⦈⊑Q°∈` \
     #src[@thin-laws at `X≜⦇`#frc([`F(∋)S`])` thin Q⦈`, `⦇S⦈` for its `S`]])],
  // A conjunction has no shape in either calculus.
  [],

  [#vstep(IMP, nb-pic((nb-So, nb-FQin, nb-LamS, nb-thin)),
    [`S°F(Q°∈)`#frc([`F(∋)S`])` thin Q` \
     #src[the first by @cata-fusion; @hylo-least at the bound `Q°∈` reduces the second to
      `−⊑Q°∈`]])],
  [#nb-pan(5.4, (thw-arc(THM, 4.85, 1.10), thw-arc(THN, 3.35, 1.85), ((THU, 2.60), (THU, 0))),
    ((THO, 4.85, [`S°`], 0.32), (THO, 4.10, [`Q°`], 0.32), (THO, 3.35, [`∈`], 0.32),
     (THU, 2.60, frc([`𝟙`]), -0.32), (THO, 1.85, [`∋`], 0.32), (THO, 1.10, [`S`], 0.32),
     (THU, 0.45, [`thin Q`], -0.32)),
    lanes: ((THM - 0.34, 3.70, [`F`]), (THN - 0.34, 2.60, [`E`])), names: true)],

  [#vstep(SQ, nb-pic((nb-Qo, nb-So, nb-Fin, nb-LamS, nb-thin)),
    [`Q°S°F(∈)`#frc([`F(∋)S`])` thin Q` \
     #src[`S°F(Q°)⊑Q°S°` — @mon-str at `S`, conversed; `F(R)°=F(R°)` — @relator-laws]])],
  // `Q°` has walked out of the `F` handle: that move IS the monotonicity assumption.
  [#nb-pan(5.4, (thw-arc(THM, 4.10, 1.10), thw-arc(THN, 3.35, 1.85), ((THU, 2.60), (THU, 0))),
    ((THO, 4.85, [`Q°`], 0.32), (THO, 4.10, [`S°`], 0.32), (THO, 3.35, [`∈`], 0.32),
     (THU, 2.60, frc([`𝟙`]), -0.32), (THO, 1.85, [`∋`], 0.32), (THO, 1.10, [`S`], 0.32),
     (THU, 0.45, [`thin Q`], -0.32)))],

  [#vstep(SQ, nb-pic((nb-Qo, nb-in, nb-thin)),
    [`Q°∈ thin Q` \
     #src[`S°F(∈)`#frc([`F(∋)S`])`⊑∈`, since #frc([`F(∋)S`])`∋=F(∋)S` with #frc([`F(∋)S`]) a map —
      @pow-laws]])],
  [#nb-pan(3.4, (thw-out(THU, 1.85, 0),),
    ((THO, 2.60, [`Q°`], 0.32), (THO, 1.85, [`∈`], 0.32), (THU, 0.85, [`thin Q`], -0.32)))],

  [#vstep(SQ, nb-pic((nb-Qo, nb-Qo, nb-in)),
    [`Q°Q°∈` \ #src[`∈ thin Q⊑Q°∈`, the `∈\(Q°∈)` half of @thin-defn — @adj-all]])],
  [#nb-pan(3.4, (thw-out(THU, 1.30, 0),),
    ((THO, 2.60, [`Q°`], 0.32), (THO, 1.95, [`Q°`], 0.32), (THO, 1.30, [`∈`], 0.32)))],

  [#vstep(EQ, nb-pic((nb-Qo, nb-in)),
    [`Q°∈` \ #src[`Q°Q°=Q°`, `Q` a preorder]])],
  [#nb-pan(3.4, (thw-out(THU, 1.60, 0),),
    ((THO, 2.35, [`Q°`], 0.32), (THO, 1.60, [`∈`], 0.32)))],
))]<thin-thm81>

// B&dM Corollary 8.1, p. 195: the thinning theorem read against the optimisation problem itself.
// `⦇−⦈` and not the algebra: its transpose opens an `E` INSIDE the reduce, which no outer panel has.
#let tb-est = ([`est(R)`], 1.9, true)
#let tb-thin = ([`thin Q`], 1.9, true)
#let tb-cS = (frc([`⦇S⦈`]), 1.5, false)
#let tb-fold = ([`⦇`#frc([`F(∋)S`])` thin Q⦈`], 4.2, false)
#let tb-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THM, [`T`]), (THO, [`A`])), ((THO, [`A`]),), lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`⦇`#frc([`F(∋)S`])` thin Q⦈ est(R)⊑`#frc([`⦇S⦈`])` est(R)` \
    #src[the thinning fold refines the optimisation problem itself —
     Corollary 8.1, `S` monotonic on `Q`, `Q⊑R`, both preorders
 #h(4pt) ]],
     // lean:AOP.A8_1.thinning_est@c31bcdd8
  table.header([*circuit* — one wire, `T` to `A`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`T`], [`A`], none, (tb-fold, tb-est)),
    [`⦇`#frc([`F(∋)S`])` thin Q⦈ est(R)`])],
  // The reduce CONSUMES `T` and the transpose inside it BIRTHS `E`, so the two wires meet at one bead.
  [#tb-pan(3.2, (thw-in(THM, 3.2, 2.15), thw-arc(THU, 2.15, 0.85)),
    ((THO, 2.15, [`⦇−⦈`], 0.32), (THO, 0.85, [`est(R)`], 0.32)),
    lanes: ((THU - 1.05, 1.50, [`E`]),), names: true)],

  [#vstep(SQ, thpic([`T`], [`A`], none, (tb-cS, tb-thin, tb-est)),
    [#frc([`⦇S⦈`])` thin Q est(R)` \ #src[@thin-thm81]])],
  // `⦇S⦈%∋=(𝟙%∋)E(⦇S⦈)`: the unit births `E` OUTSIDE `T`, so the reduce runs under it and `thin Q`
  // — an arrow of the set alone — is a bead on the `E` wire, not on the object wire.
  [#tb-pan(3.7, (thw-in(THM, 3.7, 2.15), ((THU, 3.05), (THU, 0.85 + KNEE), (THO, 0.85))),
    ((THU, 3.05, frc([`𝟙`]), -0.32), (THO, 2.15, [`⦇S⦈`], 0.32), (THU, 1.55, [`thin Q`], -0.32),
     (THO, 0.85, [`est(R)`], 0.32)))],

  [#vstep(EQ, thpic([`T`], [`A`], none, (tb-cS, tb-est)),
    [#frc([`⦇S⦈`])` est(R)` \ #src[`est(R)=thin Q est(R)` — @thin-laws, `Q⊑R`]])],
  [#tb-pan(3.7, (thw-in(THM, 3.7, 2.15), ((THU, 3.05), (THU, 0.85 + KNEE), (THO, 0.85))),
    ((THU, 3.05, frc([`𝟙`]), -0.32), (THO, 2.15, [`⦇S⦈`], 0.32), (THO, 0.85, [`est(R)`], 0.32)))],
))]<thin-cor>

== Paths in a layered network

// B&dM §8.2, p. 196.  `Q` has to record `head` because `wt (a, head xs)` is unbounded: a dearer path
// with a nearer first vertex can still win.
#disp[#definition[
`F(A,X)=A+A×X`, #h(4pt) `L=list⁺` with initial algebra `α≜[wrap,cons] : F(A,LA)⟶LA`.

`wrapz≜⟨wrap,zero⟩`, #h(4pt) `consw (a,(xs,n))=(cons (a,xs),wt (a,head xs)+n)`.

`cost≜⦇[wrapz,consw]⦈π₂`, #h(4pt) `⦇[wrapz,consw]⦈=⟨𝟙,cost⟩`, #h(4pt) `R≜cost≤cost°`.

`Q≜R∩(head head°)`, #h(4pt) `S≜F(𝟙,∋)α`, #h(4pt) $frac(#[`F(∋,𝟙)`], ∋)$ `=𝟙+cpl`, #h(4pt)
$frac(#[`F(𝟙,∋)`], ∋)$ `=𝟙+cpr`, #h(4pt) `step≜cpr P(cons) est(R)`.
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
)]<path-mono>

// B&dM §8.2, p. 198.  The `E` the transpose opens is born OUTSIDE the reduce in the specification
// and INSIDE it from the thinning theorem on; that is what rows 1 and 2 differ by.
#let pb-est = ([`est(R)`], 1.9, true)
#let pb-thin = ([`thin Q`], 1.9, true)
#let pb-spec = (frc([`⦇F(∋,𝟙)α⦈`]), 3.1, false)
#let pb-alg = (frc([`F(∋,∋)α`]), 2.6, false)
#let pb-out = (frc([`F(∋,𝟙)`]), 2.4, false)
#let pb-un = ([`union`], 1.75, false)
#let pb-Pa = ([`P(`#frc([`F(𝟙,∋)α`])`)`], 3.6, false)
#let pb-Pat = ([`P(`#frc([`F(𝟙,∋)α`])` thin Q)`], 5.5, true)
#let pb-Pae = ([`P(`#frc([`F(𝟙,∋)α`])` est(R) `#frc([`𝟙`])`)`], 7.0, true)
#let pb-Pea = ([`P(`#frc([`F(𝟙,∋)`])` P(α) est(R))`], 6.3, true)
#let pb-Pws = ([`P([wrap,step])`], 3.9, true)
#let pb-prog = ([`[P(wrap),cpl P(step)]`], 6.3, true)
#let pb-pic(alg, tail) = thpic([`L(EA)`], [`LA`], alg, tail)
// TWO `E` wires, and that is the content: the one the source carries inside `L` (top port), and the
// one the transpose opens outside it — by the unit `𝟙%∋` above the reduce, or by the reduce itself.
#let pb-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THM, [`L`]), (THN, [`E`]), (THO, [`A`])), ((THM, [`L`]), (THO, [`A`])),
  lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`⦇F(∋,𝟙)α⦈`])` est(R)⊒⦇[P(wrap),cpl P(step)]⦈ est(R)` \
    #src[a least-cost path in a layered network, as a fold over the layers —
 B&dM §8.2, p. 198. ]],
     // lean:AOP.A8_2.thinning_paths@b30f4f31
  table.header([*circuit* — one wire, `L(EA)` to `LA`; the algebra inside the functorial box],
    [*Hinze–Marsden*]),

  [#vstep([], pb-pic(none, (pb-spec, pb-est)),
    [#frc([`⦇F(∋,𝟙)α⦈`])` est(R)` #h(4pt) #src[`=` #frc([`L(∋)`])` est(R)`]])],
  [#pb-pan(4.0,
    (((THU, 3.35), (THU, 0.85)), thw-in(THM, 4.0, 2.20),
     thw-in(THN, 4.0, 2.20), thw-out(THM, 2.20, 0.0)),
    ((THU, 3.35, frc([`𝟙`]), -0.32), (THO, 2.20, [`⦇F(∋,𝟙)α⦈`], 0.32), (THU, 0.85, [`est(R)`], -0.32)),
    lanes: ((THU - 1.05, 2.10, [`E`]),), names: true)],

  [#vstep(RQ, pb-pic((pb-alg, pb-thin), (pb-est,)),
    [`⦇`#frc([`F(∋,∋)α`])` thin Q⦈ est(R)` \
     #src[Corollary 8.1 — @thin-cor, at `F(∋,𝟙)α` monotonic on `Q` — @path-mono.
 ]])],
      // lean:AOP.A8_2.thinAlg_elim@f26d947f
  [#pb-pan(4.0,
    (thw-in(THM, 4.0, 2.20), thw-in(THN, 4.0, 2.20), thw-out(THM, 2.20, 0.0),
     thw-out(THU, 2.20, 0.85)),
    ((THO, 2.20, [`⦇−⦈`], 0.32), (THU, 0.85, [`est(R)`], -0.32)))],

  [#vstep(EQ, pb-pic((pb-out, pb-Pa, pb-un, pb-thin), (pb-est,)),
    [`⦇`#frc([`F(∋,𝟙)`])` P(`#frc([`F(𝟙,∋)α`])`) union thin Q⦈ est(R)` \
     #src[`F(∋,∋)=F(∋,𝟙)F(𝟙,∋)`; #h(3pt) #frc([`F(∋,𝟙)F(𝟙,∋)α`])`=`#frc([`F(∋,𝟙)`])`
 P(`#frc([`F(𝟙,∋)α`])`) union`. ]])],
      // lean:AOP.A8_2.thinAlg_elim@f26d947f
  // Empty from here down: every step rewrites the ALGEBRA, and the outer panel is row 2's.  The
  // algebra's source is the bifunctor at two DIFFERENT arguments, which is a square, not a wire.
  [],

  [#vstep(RQ, pb-pic((pb-out, pb-Pat, pb-un), (pb-est,)),
    [`⦇`#frc([`F(∋,𝟙)`])` P(`#frc([`F(𝟙,∋)α`])` thin Q) union⦈ est(R)` \
     #src[`union thin Q⊒P(thin Q) union` — @thin-laws.
 ]])],
      // lean:AOP.A8_2.thinAlg_elim@f26d947f
  [],

  [#vstep(RQ, pb-pic((pb-out, pb-Pae, pb-un), (pb-est,)),
    [`⦇`#frc([`F(∋,𝟙)`])` P(`#frc([`F(𝟙,∋)α`])` est(R) `#frc([`𝟙`])`) union⦈ est(R)` \
     #src[#frc([`S`])` thin Q⊒`#frc([`S`])` est(R) `#frc([`𝟙`]) #h(4pt) — @thin-laws at
 `S≜F(𝟙,∋)α`, `R∩(S°S)⊑Q` — @path-mono. ]])],
      // lean:AOP.A8_2.thinAlg_elim@f26d947f
  [],

  [#vstep(EQ, pb-pic((pb-out, pb-Pea), (pb-est,)),
    [`⦇`#frc([`F(∋,𝟙)`])` P(`#frc([`F(𝟙,∋)`])` P(α) est(R))⦈ est(R)` \
     #src[`P(`#frc([`𝟙`])`) union=𝟙`; #h(3pt) `α` a map, so #frc([`F(𝟙,∋)α`])`=`#frc([`F(𝟙,∋)`])` P(α)`.
 ]])],
      // lean:AOP.A8_2.thinAlg_elim@f26d947f
  [],

  [#vstep(EQ, pb-pic((pb-out, pb-Pws), (pb-est,)),
    [`⦇`#frc([`F(∋,𝟙)`])` P([wrap,step])⦈ est(R)` \
     #src[#frc([`F(𝟙,∋)`])` P(α) est(R)=[wrap,step]` — @path-defn]])],
  [],

  [#vstep(EQ, pb-pic((pb-prog,), (pb-est,)),
    [`⦇[P(wrap),cpl P(step)]⦈ est(R)` \ #src[#frc([`F(∋,𝟙)`])` =𝟙+cpl` — @path-defn]])],
  [],
))]<path-laws>

// Same reason as the hand-placed breaks in §@sec-opt: `sticky` cannot hold a heading to a BREAKABLE
// figure, so this heading stranded itself at the foot of the page.
#pagebreak(weak: true)
== Implementing thin

// B&dM §8.3, p. 199.  Lemma 8.1 is printed with `R` where its own proof and Theorem 8.2 write `P`;
// it is one connected preorder, spelled `P` here.
#disp[#definition[
`setify : [A]⟶EA`, #h(4pt) `cup : EA×EA⟶EA`, #h(4pt) `cp(F)≜` $frac(#[`F(∋)`], ∋)$, #h(4pt)
`listcp(F) : F([A])⟶[FA]`, #h(4pt) `sort P≜setify° ordered P` #src[]
// lean:AOP.A8_3.sortRel@f1ae9750
for `P` a connected preorder.

`thinlist Q` is any `thinlist Q⊑subseq` with #h(4pt) `thinlist Q setify⊑setify thin Q`; #h(4pt)
one is #h(4pt) `⦇[nil,bump Q]⦈`, #h(4pt) `bump Q (a,[])=[a]`, #h(4pt)
`bump Q (a,[b]⧺xs)=(b Q a→[a]⧺xs,a Q b→[b]⧺xs,[a]⧺[b]⧺xs)`.

*Binary thinning* data: #h(4pt) `S=(f₁p₁)∪(f₂p₂)` with `p₁`, `p₂` coreflexive; #h(4pt) `Q` a
preorder with `Q⊑R` and both `f₁p₁`, `f₂p₂` monotonic on `Q`; #h(4pt) `P` a connected preorder
with both `f₁`, `f₂` monotonic on `P`; #h(4pt) `gᵢ≜list(fᵢ) filter(pᵢ)`.
]]<thinlist-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`thinlist Q xs=[minlist Q xs]` \ #src[(8.5), `Q` connected, `xs` non-empty]],
  [what thinning should come to when it can: one element],
  [`sort P thinlist Q⊑thin Q sort P` #h(6pt) #src[(8.6) — @thinlist-86]],
  [thinning a sorted list is a thinning of the set — this is what `thinlist Q⊑subseq` buys],
  [`sort P minlist Q⊑est(Q)` #h(6pt) #src[(8.7)]],
  [a minimum of the sorted list is a minimum of the set],
  [`sort(fPf°) list(f)⊑P(f) sort P` #h(6pt) #src[(8.8)]],
  [shunt a function through a sort],
  [`sort P filter(p)⊑E(p) sort P` #h(6pt) #src[(8.9), `p` coreflexive]],
  [filtering a sorted list sorts the restricted set],
  [`(sort P×sort P) merge P⊑cup sort P` #h(6pt) #src[(8.10)]],
  [merging two sorted lists sorts their union],
  [`F(sort P) listcp(F)⊑cp(F) sort(FP)` \ #src[(8.11), `F` linear]],
  [`listcp(F)` is the list implementation of the cartesian product `cp(F)`],
)]<thinlist-laws>

// B&dM (8.6), p. 201, mirrored.  Row 3 is the content: `thinlist Q` only drops elements, and a
// subsequence of a `P`-ordered list is `P`-ordered, so the thinning may run before the sort.
#let tl-sort = ([`sort P`], 2.0, true)
#let tl-tl = ([`thinlist Q`], 3.0, true)
#let tl-set = ([`setify°`], 2.3, true)
#let tl-ord = ([`ordered P`], 2.8, true)
#let tl-pic(tail) = thpic([`EA`], [`[A]`], none, tail)
// `setify°` is where the set becomes a list, so it is a NODE on the object wire — the `E` bends in,
// the `list` bends out — and the two coreflexive-shaped arrows are beads on the lane each acts on.
#let tl-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THN, [`E`]), (THO, [`A`])), ((THU, [`list`]), (THO, [`A`])), lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[`sort P thinlist Q⊑thin Q sort P` \
    #src[a thinning of the sorted list lists a thinning of the set — (8.6), p. 201, `P` a connected
 preorder, `thinlist Q⊑subseq`. ]],
     // lean:AOP.A8_3.sortRel_comp_thinlist_le@11564234
  table.header([*circuit* — one wire, `EA` to `[A]`], [*Hinze–Marsden*]),

  [#vstep([], tl-pic((tl-sort, tl-tl)), [`sort P thinlist Q`])],
  [#tl-pan(3.6, (thw-in(THN, 3.6, 2.40), thw-out(THU, 2.40, 0)),
    ((THO, 2.40, [`sort P`], 0.32), (THU, 1.30, [`thinlist Q`], -0.32)), names: true)],

  [#vstep(EQ, tl-pic((tl-set, tl-ord, tl-tl)),
    [`setify° ordered P thinlist Q` \ #src[`sort P≜setify° ordered P` — @thinlist-defn]])],
  [#tl-pan(3.6, (thw-in(THN, 3.6, 2.40), thw-out(THU, 2.40, 0)),
    ((THO, 2.40, [`setify°`], 0.32), (THU, 1.45, [`ordered P`], -0.32),
     (THU, 0.70, [`thinlist Q`], -0.32)))],

  [#vstep(SQ, tl-pic((tl-set, tl-tl, tl-ord)),
    [`setify° thinlist Q ordered P` \
     #src[`ordered P thinlist Q⊑thinlist Q ordered P`, since `thinlist Q⊑subseq` — @thinlist-defn —
      and a subsequence of a `P`-ordered list is `P`-ordered]])],
  [#tl-pan(3.6, (thw-in(THN, 3.6, 2.40), thw-out(THU, 2.40, 0)),
    ((THO, 2.40, [`setify°`], 0.32), (THU, 1.45, [`thinlist Q`], -0.32),
     (THU, 0.70, [`ordered P`], -0.32)))],

  [#vstep(SQ, tl-pic((nb-thin, tl-set, tl-ord)),
    [`thin Q setify° ordered P` \
     #src[@thinlist-defn's `thinlist Q setify⊑setify thin Q` after `setify°`, at `setify°setify⊑𝟙`
      for `setify` simple — @dom-laws — then `·setify⊣·setify°` — @triple-chains]])],
  [#tl-pan(4.2, (thw-in(THN, 4.2, 2.10), thw-out(THU, 2.10, 0)),
    ((THN, 3.10, [`thin Q`], -0.32), (THO, 2.10, [`setify°`], 0.32),
     (THU, 1.10, [`ordered P`], -0.32)))],

  [#vstep(EQ, tl-pic((nb-thin, tl-sort)),
    [`thin Q sort P` \ #src[`sort P≜setify° ordered P` — @thinlist-defn]])],
  [#tl-pan(4.2, (thw-in(THN, 4.2, 2.10), thw-out(THU, 2.10, 0)),
    ((THN, 3.10, [`thin Q`], -0.32), (THO, 2.10, [`sort P`], 0.32)))],
))]<thinlist-86>

// B&dM Lemma 8.1, p. 202, mirrored.  The chain walks the sort INWARDS, past `filter(p)`, then past
// `list(f)`, then under `F` — each step one of (8.9), (8.8), (8.11).
#let lb-Lam = (frc([`F(∋)fp`]), 2.3, false)
#let lb-sort = ([`sort P`], 2.0, true)
#let lb-cp = ([`cp(F)`], 1.7, false)
#let lb-Efp = ([`E(fp)`], 1.7, false)
#let lb-Pf = ([`P(f)`], 1.4, false)
#let lb-Ep = ([`E(p)`], 1.4, false)
#let lb-fil = ([`filter(p)`], 2.4, false)
#let lb-lf = ([`list(f)`], 2.0, false)
#let lb-sfPf = ([`sort(fPf°)`], 3.1, true)
#let lb-sFP = ([`sort(FP)`], 2.4, true)
#let lb-Fsort = ([`F(sort P)`], 2.7, true)
#let lb-lcp = ([`listcp(F)`], 2.7, false)
#let lb-pic(tail) = thpic([`F(EA)`], [`[A]`], none, tail)
// `sort P : EA⟶[A]` is where one datatype becomes another, and nothing survives outside it, so it
// is a NODE on the object wire — the `E` bends in, the `list` bends out — not a bead on a lane.
#let lb-pan(h, wires, beads, lanes: (), names: false) = thpan(h,
  (thw-in(THN, h, 3.15), thw-in(THM, h, 2.40)) + wires, beads,
  ((THM, [`F`]), (THN, [`E`]), (THO, [`A`])), ((THU, [`list`]), (THO, [`A`])),
  lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`F(∋)fp`])` sort P⊒F(sort P) listcp(F) list(f) filter(p)` \
    #src[one sorted list built from sorted arguments, instead of a set built and then sorted —
     Lemma 8.1, p. 202, `f : FA⟶A` monotonic on `P`, `p` coreflexive, `F` linear.
 ]],
     // lean:AOP.A8_3.map_sort_comp_listcp_le@88dfad7c
  table.header([*circuit* — one wire, `F(EA)` to `[A]`], [*Hinze–Marsden*]),

  [#vstep([], lb-pic((lb-Lam, lb-sort)), [#frc([`F(∋)fp`])` sort P`])],
  [#lb-pan(4.6, (((THU, 3.90), (THU, 0.90 + KNEE), (THO, 0.90)), thw-out(THU, 0.90, 0)),
    ((THU, 3.90, frc([`𝟙`]), -0.32), (THO, 3.15, [`∋`], 0.32), (THO, 2.40, [`f`], 0.32),
     (THO, 1.65, [`p`], 0.32), (THO, 0.90, [`sort P`], 0.32)),
    lanes: ((THU - 1.05, 2.60, [`E`]),), names: true)],

  [#vstep(EQ, lb-pic((lb-cp, lb-Efp, lb-sort)),
    [`cp(F)E(fp) sort P` \
     #src[#frc([`F(∋)fp`])` =`#frc([`F(∋)`])` E(fp)` — @pow-laws; `cp(F)≜`#frc([`F(∋)`]) —
      @thinlist-defn]])],
  // Empty: rows 2 and 3 redraw row 1 — the two steps only rebracket what the transpose is made of.
  [],

  [#vstep(EQ, lb-pic((lb-cp, lb-Pf, lb-Ep, lb-sort)),
    [`cp(F)P(f)E(p) sort P` \ #src[`E(fp)=E(f)E(p)`; #h(3pt) `E(f)=P(f)` for `f` a map —
     @powrel-laws]])],
  [],

  [#vstep(RQ, lb-pic((lb-cp, lb-Pf, lb-sort, lb-fil)),
    [`cp(F)P(f) sort P filter(p)` \ #src[`sort P filter(p)⊑E(p) sort P` — @thinlist-laws]])],
  // The node has walked up past `p`, which comes out the other side as `filter(p)` on the `list`
  // lane: the same coreflexive, applied to the sorted list instead of to the set.
  [#lb-pan(4.6, (((THU, 3.90), (THU, 1.65 + KNEE), (THO, 1.65)), thw-out(THU, 1.65, 0)),
    ((THU, 3.90, frc([`𝟙`]), -0.32), (THO, 3.15, [`∋`], 0.32), (THO, 2.40, [`f`], 0.32),
     (THO, 1.65, [`sort P`], 0.32), (THU, 0.75, [`filter(p)`], -0.32)))],

  [#vstep(RQ, lb-pic((lb-cp, lb-sfPf, lb-lf, lb-fil)),
    [`cp(F) sort(fPf°) list(f) filter(p)` \
     #src[`sort(fPf°) list(f)⊑P(f) sort P` — @thinlist-laws]])],
  // Empty from here: the node now acts while `F` is still alive, so it cannot reach the object wire
  // without crossing it, and `listcp(F)` below is the `F`/`list` swap — two functor wires, not one.
  [],

  [#vstep(RQ, lb-pic((lb-cp, lb-sFP, lb-lf, lb-fil)),
    [`cp(F) sort(FP) list(f) filter(p)` \
     #src[`FP⊑fPf°` — @mon-str at `f` a map; `sort P≜setify° ordered P` grows with `P` —
      @thinlist-defn]])],
  [],

  [#vstep(RQ, lb-pic((lb-Fsort, lb-lcp, lb-lf, lb-fil)),
    [`F(sort P) listcp(F) list(f) filter(p)` \
     #src[`F(sort P) listcp(F)⊑cp(F) sort(FP)` — @thinlist-laws, `F` linear]])],
  [],
))]<thinlist-lem81>

// B&dM Theorem 8.2, p. 203, mirrored.  The candidate SET of the thinning theorem becomes a sorted
// LIST, and that swap — `E` killed by `est(R)`, `list` by `minlist R` — is what rows 3 and 4 draw.
#let sb-sort = ([`sort P`], 2.0, true)
#let sb-min = ([`minlist R`], 2.7, true)
#let sb-prog = ([`⦇listcp(F) ⟨g₁,g₂⟩ merge P thinlist Q⦈`], 11.0, false)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`⦇S⦈`])` est(R)⊒⦇listcp(F) ⟨g₁,g₂⟩ merge P thinlist Q⦈ minlist R` \
    #src[a fold on sorted lists of partial solutions, thinned at every step —
     Theorem 8.2, p. 203, at @thinlist-defn's binary thinning data.
 ]],
     // lean:AOP.A8_3.thinningList@7b3eb252
  table.header([*circuit* — one wire, `T` to `A`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`T`], [`A`], none, (tb-cS, tb-est)), [#frc([`⦇S⦈`])` est(R)`])],
  [#tb-pan(3.7, (thw-in(THM, 3.7, 2.15), ((THU, 3.05), (THU, 0.85 + KNEE), (THO, 0.85))),
    ((THU, 3.05, frc([`𝟙`]), -0.32), (THO, 2.15, [`⦇S⦈`], 0.32), (THO, 0.85, [`est(R)`], 0.32)),
    names: true)],

  [#vstep(RQ, thpic([`T`], [`A`], none, (tb-fold, tb-est)),
    [`⦇`#frc([`F(∋)S`])` thin Q⦈ est(R)` \
     #src[@thin-cor at `f₁p₁` and `f₂p₂` monotonic on `Q` — @thinlist-defn]])],
  [#tb-pan(3.2, (thw-in(THM, 3.2, 2.15), thw-arc(THU, 2.15, 0.85)),
    ((THO, 2.15, [`⦇−⦈`], 0.32), (THO, 0.85, [`est(R)`], 0.32)),
    lanes: ((THU - 1.05, 1.50, [`E`]),))],

  [#vstep(RQ, thpic([`T`], [`A`], none, (tb-fold, sb-sort, sb-min)),
    [`⦇`#frc([`F(∋)S`])` thin Q⦈ sort P minlist R` \
     #src[`sort P minlist R⊑est(R)` — @thinlist-laws at its `Q≜R`]])],
  // `est(R)` has split into the node that sorts and the `minlist R` that reads the head back.
  [#tb-pan(4.6, (thw-in(THM, 4.6, 3.50), thw-arc(THU, 3.50, 2.10), thw-arc(THU, 2.10, 0.80)),
    ((THO, 3.50, [`⦇−⦈`], 0.32), (THO, 2.10, [`sort P`], 0.32), (THO, 0.80, [`minlist R`], 0.32)),
    lanes: ((THU - 1.05, 2.80, [`E`]), (THU - 1.05, 1.45, [`list`])))],

  [#vstep(RQ, thpic([`T`], [`A`], none, (sb-prog, sb-min)),
    [`⦇listcp(F) ⟨g₁,g₂⟩ merge P thinlist Q⦈ minlist R` \ #src[@cata-fusion at @thinlist-fusion]])],
  // The reduce now births `list` where it births `E` above: no set is ever built.
  [#tb-pan(3.7, (thw-in(THM, 3.7, 2.50), thw-arc(THU, 2.50, 1.00)),
    ((THO, 2.50, [`⦇−⦈`], 0.32), (THO, 1.00, [`minlist R`], 0.32)),
    lanes: ((THU - 1.05, 1.75, [`list`]),))],
))]<thinlist-thm82>

// The fusion condition of the last step above, B&dM p. 203.  Two of its moves are unwritten there:
// the product law that distributes `sort P×sort P` over the fork, and the fork law that closes it.
#let qb-tl = ([`thinlist Q`], 3.0, true)
#let qb-fork = ([`⟨`#frc([`F(∋)f₁p₁`])`,`#frc([`F(∋)f₂p₂`])`⟩`], 5.6, false)
#let qb-cup = ([`cup`], 1.3, false)
#let qb-sxs = ([`sort P×sort P`], 3.6, true)
#let qb-merge = ([`merge P`], 2.3, true)
#let qb-fork2 = ([`⟨`#frc([`F(∋)f₁p₁`])` sort P,`#frc([`F(∋)f₂p₂`])` sort P⟩`], 8.8, true)
#let qb-g = ([`⟨g₁,g₂⟩`], 2.2, false)
#let qb-pic(tail) = thpic([`F(EA)`], [`[A]`], none, tail)
// The panel `lb-pan` draws, with `S` for `f` and no `p`: same source, same two ports killed.
#let qb-pan(h, wires, beads, lanes: (), names: false) = thpan(h,
  (thw-in(THN, h, 3.15), thw-in(THM, h, 2.40)) + wires, beads,
  ((THM, [`F`]), (THN, [`E`]), (THO, [`A`])), ((THU, [`list`]), (THO, [`A`])),
  lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`F(∋)S`])` thin Q sort P⊒F(sort P) listcp(F) ⟨g₁,g₂⟩ merge P thinlist Q` \
    #src[sorting the candidate set is what turns the thinning algebra into an algebra on lists —
     B&dM p. 203, the side condition of @thinlist-thm82's last step.
 ]],
     // lean:AOP.A8_3.sortedAlg_fusion@4732cb05
  table.header([*circuit* — one wire, `F(EA)` to `[A]`], [*Hinze–Marsden*]),

  [#vstep([], qb-pic((nb-LamS, nb-thin, sb-sort)), [#frc([`F(∋)S`])` thin Q sort P`])],
  [#qb-pan(4.6, (((THU, 3.90), (THU, 0.90 + KNEE), (THO, 0.90)), thw-out(THU, 0.90, 0)),
    ((THU, 3.90, frc([`𝟙`]), -0.32), (THO, 3.15, [`∋`], 0.32), (THO, 2.40, [`S`], 0.32),
     (THU, 1.65, [`thin Q`], -0.32), (THO, 0.90, [`sort P`], 0.32)),
    lanes: ((THU - 1.05, 2.85, [`E`]),), names: true)],

  [#vstep(RQ, qb-pic((nb-LamS, sb-sort, qb-tl)),
    [#frc([`F(∋)S`])` sort P thinlist Q` \
     #src[`sort P thinlist Q⊑thin Q sort P` — @thinlist-laws]])],
  // The node has walked up past `thin Q`, which comes out below it as `thinlist Q` on the `list`
  // lane: that exchange is the whole of (8.6), and the rest of the chain rewrites the algebra.
  [#qb-pan(4.6, (((THU, 3.90), (THU, 1.65 + KNEE), (THO, 1.65)), thw-out(THU, 1.65, 0)),
    ((THU, 3.90, frc([`𝟙`]), -0.32), (THO, 3.15, [`∋`], 0.32), (THO, 2.40, [`S`], 0.32),
     (THO, 1.65, [`sort P`], 0.32), (THU, 0.75, [`thinlist Q`], -0.32)))],

  [#vstep(EQ, qb-pic((qb-fork, qb-cup, sb-sort, qb-tl)),
    [`⟨`#frc([`F(∋)f₁p₁`])`,`#frc([`F(∋)f₂p₂`])`⟩ cup sort P thinlist Q` \
     #src[`S=(f₁p₁)∪(f₂p₂)` — @thinlist-defn, then @cup-defn]])],
  // Empty from here: a fork is an operation on hom-sets, and `×` is a bifunctor, so neither is a
  // wiring; the circuit column keeps them as one box, §14's convention for a pair.
  [],

  [#vstep(RQ, qb-pic((qb-fork, qb-sxs, qb-merge, qb-tl)),
    [`⟨`#frc([`F(∋)f₁p₁`])`,`#frc([`F(∋)f₂p₂`])`⟩(sort P×sort P) merge P thinlist Q` \
     #src[`(sort P×sort P) merge P⊑cup sort P` — @thinlist-laws]])],
  [],

  [#vstep(EQ, qb-pic((qb-fork2, qb-merge, qb-tl)),
    [`⟨`#frc([`F(∋)f₁p₁`])` sort P,`#frc([`F(∋)f₂p₂`])` sort P⟩ merge P thinlist Q` \
     #src[`⟨X,Y⟩(sort P×sort P)=⟨X sort P,Y sort P⟩` — @bdm-prod-laws]])],
  [],

  [#vstep(RQ, qb-pic((lb-Fsort, lb-lcp, qb-g, qb-merge, qb-tl)),
    [`F(sort P) listcp(F) ⟨g₁,g₂⟩ merge P thinlist Q` \
     #src[@thinlist-lem81 at `f₁`, `p₁` and at `f₂`, `p₂`, then
      `X⟨g₁,g₂⟩⊑⟨Xg₁,Xg₂⟩` — @bdm-prod-laws; `gᵢ≜list(fᵢ) filter(pᵢ)` — @thinlist-defn]])],
  [],
))]<thinlist-fusion>

== The knapsack problem

// B&dM §8.4, p. 205.  The printed base of the final fold is `nil`, without the outer `wrap` that
// §8.5 and §8.6 do print (`wrap wrap wrap`, `start wrap`).
#disp[#definition[
`vol,wt : Item⟶Real`, #h(4pt) `value≜list(vol) sum`, #h(4pt) `weight≜list(wt) sum`
#src[].
// lean:AOP.A5_6_ListCombinators.total_eq@bb0818ee

`subseq=⦇[nil,cons]∪[nil,π₂]⦈` #src[,
// lean:AOP.A8_4_Knapsack.con_eq_junc@f6f12bd6
], #h(4pt) `within w` the coreflexive on `xs` with
// lean:AOP.A8_4_Knapsack.drop_eq_junc@1f5b4c77
`weight xs≤w`, #h(4pt) `0≤w`.

`R≜value≥value°` #src[], #h(4pt)
// lean:AOP.A8_4_Knapsack.R_eq@1c13d35d
`Q≜R∩(weight≤weight°)` #src[], #h(4pt)
// lean:AOP.A8_4_Knapsack.Q_eq@22acbe51
`P≜R` #src[,
// lean:AOP.A8_4_Knapsack.knap_sort_cons@2219de33
].
// lean:AOP.A8_4_Knapsack.knap_sort_drop@ab5c746c

`FA=1+Item×A`, #h(4pt) `listcp(F)=wrap+cpr`, #h(4pt) `g₁≜list([nil,cons]) filter(within w)`
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
   // lean:AOP.A8_4_Knapsack.knap_mono_cons@978d716e
 ]],
   // lean:AOP.A8_4_Knapsack.knap_mono_drop@b49841b3
  [both halves are monotonic on `Q` once ties in value are broken by weight],
)]<knap-mono>

// B&dM §8.4, p. 206.  The set the transpose opens becomes a LIST at the binary thinning step, and
// that swap — `E` killed by `est(R)`, `list` killed by `minlist R` — is what the right column draws.
#let kb-est = ([`est(R)`], 1.9, true)
#let kb-min = ([`minlist R`], 2.7, true)
#let kb-spec = (frc([`subseq (within w)`]), 4.3, false)
#let kb-fus = (frc([`⦇[nil,cons](within w)∪[nil,π₂]⦈`]), 7.2, false)
#let kb-lcp = ([`listcp(F)`], 2.7, false)
#let kb-g = ([`⟨g₁,g₂⟩`], 2.2, false)
#let kb-mg = ([`merge R`], 2.3, true)
#let kb-tl = ([`thinlist Q`], 3.0, true)
#let kb-prog = ([`[nil,cpr ⟨h₁,h₂⟩ merge R thinlist Q]`], 10.5, true)
#let kb-pic(alg, tail) = thpic([`[Item]`], [`[Item]`], alg, tail)
// The `list` wire runs the panel's whole height — the selections stay lists throughout — so it is
// drawn here rather than repeated in every row.
#let kb-pan(h, wires, beads, lanes: (), names: false) = thpan(h, (((THM, h), (THM, 0)),) + wires,
  beads, ((THM, [`list`]), (THO, [`Item`])), ((THM, [`list`]), (THO, [`Item`])),
  lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`subseq (within w)`])` est(R)⊒⦇[nil,cpr ⟨h₁,h₂⟩ merge R thinlist Q]⦈ minlist R` \
    #src[the knapsack problem, as a fold that thins the packings kept at each item —
 B&dM §8.4, p. 206. ]],
     // lean:AOP.A8_4_Knapsack.knap_laws@6299a9fe
  table.header([*circuit* — one wire, `[Item]` to `[Item]`; the algebra inside the functorial box],
    [*Hinze–Marsden*]),

  [#vstep([], kb-pic(none, (kb-spec, kb-est)),
    [#frc([`subseq (within w)`])` est(R)`])],
  [#kb-pan(3.6, (((THU, 3.05), (THU, 0.85)),),
    ((THU, 3.05, frc([`𝟙`]), -0.32), (THM, 2.30, [`subseq`], 0.32), (THM, 1.65, [`within w`], 0.32),
     (THU, 0.85, [`est(R)`], -0.32)),
    names: true)],

  [#vstep(EQ, kb-pic(none, (kb-fus, kb-est)),
    [#frc([`⦇[nil,cons](within w)∪[nil,π₂]⦈`])` est(R)` \
 #src[@cata-fusion, weights non-negative. ]])],
     // lean:AOP.A8_4_Knapsack.knap_spec@dc0de67d
  [#kb-pan(3.6, (((THU, 3.05), (THU, 0.85)),),
    ((THU, 3.05, frc([`𝟙`]), -0.32), (THM, 1.95, [`⦇−⦈`], 0.32), (THU, 0.85, [`est(R)`], -0.32)))],

  [#vstep(RQ, kb-pic((kb-lcp, kb-g, kb-mg, kb-tl), (kb-min,)),
    [`⦇listcp(F) ⟨g₁,g₂⟩ merge R thinlist Q⦈ minlist R` \
     #src[@thinlist-thm82, at `P≜R`, `F` linear, `Q` from @knap-mono]])],
  // The candidate set is now a candidate LIST: the reduce births `list` where it births `E` above.
  [#kb-pan(3.6, (((THM, 2.30), (THU, 2.30 - KNEE), (THU, 0.85)),),
    ((THM, 2.30, [`⦇−⦈`], 0.32), (THU, 0.85, [`minlist R`], -0.32)),
    lanes: ((THU - 1.05, 1.75, [`list`]),))],

  [#vstep(EQ, kb-pic((kb-prog,), (kb-min,)),
    [`⦇[nil,cpr ⟨h₁,h₂⟩ merge R thinlist Q]⦈ minlist R` \
     #src[`listcp(F)=wrap+cpr`, `gᵢ=[list(nil),hᵢ]` — @knap-defn; `minlist R` is `head`, packings
      coming out in descending value]])],
  [],
))]<knap-laws>

// Stranded at the foot of its page for the same reason as the break above.
#pagebreak(weak: true)
== The paragraph problem

// B&dM §8.5, p. 207.  `P ≜ ⊤` works because `merge ⊤ = cat`, which already brings equal first lines
// together; the book's first choice `head prefix head°` is correct but not needed.
#disp[#definition[
`Line=list⁺ Word`, #h(4pt) `Para=list⁺ Line`, #h(4pt) `FA=Word+Word×A`, #h(4pt)
`listcp(F)=wrap+cpr`.

`new (a,xs)=[[a]]⧺xs`, #h(4pt) `glue (a,xs)=[[a]⧺head xs]⧺tail xs`, #h(4pt)
`partition≜⦇[wrap wrap,new∪glue]⦈ : list⁺ Word⟶Para`.

`width≜⦇[length,(length×𝟙) plus succ]⦈`, #h(4pt) `0≤length a`, #h(4pt) `fits w` the coreflexive on a
line `x` with `width x≤w`, #h(4pt) `ok w` the coreflexive on `[x]⧺xs` with `width x≤w`.

`white w x=w−width x`, #h(4pt) `collect≜list(sqr) sum`, #h(4pt) `waste w≜init list(white w) collect`.

`R≜(waste w)≤(waste w)°` #src[], #h(4pt)
// lean:AOP.A8_5_Paragraph.R_eq@cf0ea074
`Q≜R∩(head head°)` #src[], #h(4pt)
// lean:AOP.A8_5_Paragraph.Q_eq@a6330fbf
`P≜⊤` #src[,
// lean:AOP.A8_5_Paragraph.para_sort_new@30222bce
].
// lean:AOP.A8_5_Paragraph.para_sort_glue@bd4641b6

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
   // lean:AOP.A8_5_Paragraph.para_mono_new@d0ba9ffb
 ]],
   // lean:AOP.A8_5_Paragraph.para_mono_glue@0149af32
  [both halves are monotonic on `Q` once ties in waste are broken by the first line],
  [`merge ⊤=cat`; #h(4pt) `P≜head prefix head°` also serves],
  [`⊤` needs no sorting at all, and `prefix` is a linear order on first lines of paragraphs of one
   input],
)]<para-mono>

// B&dM §8.5, p. 210.  `partition` turns ONE list into two — the paragraph and its lines — so it is a
// bead on the object wire with three list wires at it, and the candidate set is a fourth.
#let ab-est = ([`est(R)`], 1.9, true)
#let ab-min = ([`minlist R`], 2.7, true)
#let ab-spec = (frc([`partition list⁺(fits w)`]), 5.6, false)
#let ab-fus = (frc([`⦇[wrap wrap,new∪(glue (ok w))]⦈`]), 7.4, false)
#let ab-split = (frc([`⦇[wrap wrap,new]∪([wrap wrap,glue] (ok w))⦈`]), 10.6, false)
#let ab-lcp = ([`listcp(F)`], 2.7, false)
#let ab-g = ([`⟨g₁,g₂⟩`], 2.2, false)
#let ab-cat = ([`cat`], 1.4, false)
#let ab-tl = ([`thinlist Q`], 3.0, true)
#let ab-prog = ([`[start,cpr ⟨h₁,h₂⟩ cat thinlist Q]`], 9.9, true)
#let ab-pic(alg, tail) = thpic([`list⁺ Word`], [`Para`], alg, tail)
// The source is ONE `list⁺`; `partition` births the paragraph's, and the reduce of the last two rows
// births a third — the list of candidate paragraphs `minlist R` reads back down.
#let ab-pan(h, wires, beads, bot, lanes: (), names: false) = thpan(h,
  (((THO, h), (THO, 0)), ((THN, h), (THN, 2.60))) + wires, beads,
  ((THN, [`list⁺`]), (THO, [`Word`])), bot, lanes: lanes, names: names)
#let ab-out = (((THO, 2.60), (THM, 2.60 - KNEE), (THM, 0)), ((THO, 2.60), (THN, 2.60 - KNEE), (THN, 0)))
#let ab-bot = ((THM, [`list⁺`], 0.90), (THN, [`list⁺`]), (THO, [`Word`]))
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`partition list⁺(fits w)`])` est(R)⊒⦇[start,cpr ⟨h₁,h₂⟩ cat thinlist Q]⦈ minlist R` \
    #src[a paragraph laid out as a fold that thins the layouts kept at each word —
 B&dM §8.5, p. 210. ]],
     // lean:AOP.A8_5_Paragraph.para_laws@2ed8ee5e
  table.header([*circuit* — one wire, `list⁺ Word` to `Para`; the algebra inside the functorial box],
    [*Hinze–Marsden*]),

  [#vstep([], ab-pic(none, (ab-spec, ab-est)),
    [#frc([`partition list⁺(fits w)`])` est(R)`])],
  [#ab-pan(4.2, (((THU, 3.55), (THU, 0.75)),) + ab-out,
    ((THU, 3.55, frc([`𝟙`]), -0.32), (THO, 2.60, [`partition`], 0.32), (THN, 1.60, [`fits w`], 0.32),
     (THU, 0.75, [`est(R)`], -0.32)),
    ab-bot, names: true)],

  [#vstep(EQ, ab-pic(none, (ab-fus, ab-est)),
    [#frc([`⦇[wrap wrap,new∪(glue (ok w))]⦈`])` est(R)` \
     #src[@cata-fusion, every word fits on a line by itself.
 ]])],
     // lean:AOP.A8_5_Paragraph.para_alg_fusion@658f3c24
  [#ab-pan(4.2, (((THU, 3.55), (THU, 0.75)),) + ab-out,
    ((THU, 3.55, frc([`𝟙`]), -0.32), (THO, 2.60, [`⦇−⦈`], 0.32), (THU, 0.75, [`est(R)`], -0.32)),
    ab-bot)],

  [#vstep(EQ, ab-pic(none, (ab-split, ab-est)),
    [#frc([`⦇[wrap wrap,new]∪([wrap wrap,glue] (ok w))⦈`])` est(R)` \
     #src[the algebra as `(f₁p₁)∪(f₂p₂)`, `p₁≜𝟙` — @thinlist-defn.
 ]])],
     // lean:AOP.A8_5_Paragraph.para_spec@f39d2ce8
  // Empty: the step renames the algebra and the panel above already draws the reduce.
  [],

  [#vstep(RQ, ab-pic((ab-lcp, ab-g, ab-cat, ab-tl), (ab-min,)),
    [`⦇listcp(F) ⟨g₁,g₂⟩ cat thinlist Q⦈ minlist R` \
     #src[@thinlist-thm82, at `P≜⊤` with `merge ⊤=cat`, `Q` from @para-mono]])],
  [#ab-pan(4.2, (((THO, 2.60), (THU, 2.60 - KNEE), (THU, 0.75)),) + ab-out,
    ((THO, 2.60, [`⦇−⦈`], 0.32), (THU, 0.75, [`minlist R`], -0.32)),
    ab-bot, lanes: ((THU - 1.05, 1.75, [`list`]),))],

  [#vstep(EQ, ab-pic((ab-prog,), (ab-min,)),
    [`⦇[start,cpr ⟨h₁,h₂⟩ cat thinlist Q]⦈ minlist R` \
     #src[`listcp(F)=wrap+cpr`, `gᵢ` along the coproduct — @para-defn]])],
  [],
))]<para-laws>

== Bitonic tours

// B&dM §8.6, p. 212.  `Q` keeps the `head2` conjunct p.215 derives and then drops on the grounds
// that tours of one input share their heads: without it the two `tour-mono` rows are false.
#disp[#definition[
`FA=(City×City)+(City×A)`, the base functor of cons-lists of length at least two; #h(4pt)
`listcp(F)=wrap+cpr`; #h(4pt) `tc : City×City⟶Real`, neither positive nor symmetric.

`start (a,b)=([a,b],[a,b])`, #h(4pt) `dropl (a,([b]⧺xs,ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt)
`dropr (a,(xs,[b]⧺ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt) `tour≜⦇[start,dropl∪dropr]⦈`.

`cost (xs,ys)=outcost xs+incost ys`, #h(4pt) `outcost [a₀,…,aₙ]=tc (a₀,a₁)+⋯+tc (aₙ₋₁,aₙ)`,
#h(4pt) `incost [a₀,…,aₙ]=tc (a₁,a₀)+⋯+tc (aₙ,aₙ₋₁)`.

`next≜tail head`, #h(4pt) `next2≜next×next`, #h(4pt) `head2≜head×head`, #h(4pt) `R≜cost≤cost°`
#src[], #h(4pt)
// lean:AOP.A8_6_Tour.R_eq@15ad4adc
`Q≜R∩(next2 next2°)∩(head2 head2°)`, #h(4pt) `P≜⊤` #src[,
// lean:AOP.A8_6_Tour.tour_sort_dropl@3dddee2e
], #h(4pt) `g₁≜list([start,dropl])`, #h(4pt)
// lean:AOP.A8_6_Tour.tour_sort_dropr@12e55048
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
   // lean:AOP.A8_6_Tour.tour_mono_dropl@72fb7ce1
 ]],
   // lean:AOP.A8_6_Tour.tour_mono_dropr@950fdec0
  [both are, once ties in cost are broken by the two second cities — the heads already agree among
   tours of one input],
)]<tour-mono>

// B&dM §8.6, p. 215.  A tour is a PAIR of lists, so `[City]×[City]` is the one unary functor
// `X↦[X]×[X]` — a bifunctor is never a wire, and this one is partially applied before it is drawn.
#let ub-est = ([`est(R)`], 1.9, true)
#let ub-min = ([`minlist R`], 2.7, true)
#let ub-tour = (frc([`tour`], ), 1.7, false)
#let ub-fold = (frc([`⦇[start,dropl∪dropr]⦈`]), 5.6, false)
#let ub-lcp = ([`listcp(F)`], 2.7, false)
#let ub-g = ([`⟨g₁,g₂⟩`], 2.2, false)
#let ub-cat = ([`cat`], 1.4, false)
#let ub-tl = ([`thinlist Q`], 3.0, true)
#let ub-prog = ([`[start wrap,cpr ⟨list(dropl),list(dropr)⟩ cat thinlist Q]`], 16.1, true)
#let ub-pic(alg, tail) = thpic([`[City]`], [`[City]×[City]`], alg, tail)
#let ub-pan(h, wires, beads, lanes: (), names: false) = thpan(h,
  (((THO, h), (THO, 0)), ((THN, h), (THN, 2.60)), ((THO, 2.60), (THM, 2.60 - KNEE), (THM, 0)))
    + wires, beads,
  ((THN, [`list`]), (THO, [`City`])), ((THM, [`list×list`]), (THO, [`City`])),
  lanes: lanes, names: names)
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`tour`])` est(R)⊒⦇[start wrap,cpr ⟨list(dropl),list(dropr)⟩ cat thinlist Q]⦈ minlist R` \
    #src[a least-cost bitonic tour, as a fold that thins the tours kept at each city —
 B&dM §8.6, p. 215. ]],
     // lean:AOP.A8_6_Tour.tour_laws@033921a1
  table.header([*circuit* — one wire, `[City]` to `[City]×[City]`; the algebra inside the functorial
    box], [*Hinze–Marsden*]),

  [#vstep([], ub-pic(none, (ub-tour, ub-est)), [#frc([`tour`])` est(R)`])],
  [#ub-pan(4.2, (((THU, 3.55), (THU, 0.75)),),
    ((THU, 3.55, frc([`𝟙`]), -0.32), (THO, 2.60, [`tour`], 0.32), (THU, 0.75, [`est(R)`], -0.32)),
    names: true)],

  [#vstep(EQ, ub-pic(none, (ub-fold, ub-est)),
    [#frc([`⦇[start,dropl∪dropr]⦈`])` est(R)` \ #src[`tour≜⦇[start,dropl∪dropr]⦈` — @tour-defn]])],
  // Empty: the step only names the reduce, and the panel above already draws it.
  [],

  [#vstep(RQ, ub-pic((ub-lcp, ub-g, ub-cat, ub-tl), (ub-min,)),
    [`⦇listcp(F) ⟨g₁,g₂⟩ cat thinlist Q⦈ minlist R` \
     #src[@thinlist-thm82, at `P≜⊤` with `merge ⊤=cat`, `Q` from @tour-mono]])],
  [#ub-pan(4.2, (((THO, 2.60), (THU, 2.60 - KNEE), (THU, 0.75)),),
    ((THO, 2.60, [`⦇−⦈`], 0.32), (THU, 0.75, [`minlist R`], -0.32)),
    lanes: ((THU - 1.05, 1.75, [`list`]),))],

  [#vstep(EQ, ub-pic((ub-prog,), (ub-min,)),
    [`⦇[start wrap,cpr ⟨list(dropl),list(dropr)⟩ cat thinlist Q]⦈ minlist R` \
     #src[`listcp(F)=wrap+cpr`, `gᵢ=[list(start),list(dropᵢ)]` — @tour-defn; quadratic, two tours
      added per step]])],
  [],
))]<tour-laws>

#pagebreak(weak: true)
= Dynamic Programming <sec-dp>

// ---- §15's and §16's own vocabulary, built on §14's.  CIRCUIT: one wire, a box per factor
// (`thpic`); a PRODUCT source is TWO wires, both entering the first box (`gpair`).
// A `(μX : …)` row draws the BODY of the recursion: a fixed point has no circuit of its own, and
// what moves from row to row is a box inside that body.
#let gpair(l1, l2, rgt, head, hw, tail, hc: false, s: 74%) = P(cetz.canvas(length: 0.8cm, {
  let sp = 0.62
  d.content((-0.36, sp), text(10pt)[#l1], anchor: "east")
  d.content((-0.36, -sp), text(10pt)[#l2], anchor: "east")
  wire((-0.30, sp), (0, sp)); wire((-0.30, -sp), (0, -sp))
  gbox((0, 0), head, w: hw, h: 2 * sp + 0.62, chamfer: hc)
  boxrun(hw, 0, tail, h: TH)
  d.content((hw + boxrun-w(tail) + 0.30, 0), text(10pt)[#rgt], anchor: "west")
}), s: s)

// ---- HINZE–MARSDEN: §14's own lanes, so the two chapters' panels stack, with one lane added.
// Outermost functor LEFTMOST and `𝟏` at the right; `E` takes `THU` because the transpose is taken of
// the WHOLE problem, the base functor `THM` because `T°` opens it inside that set, and a datatype
// the input carries `THN`, `THP`.  An `est` kills the SET alone, so its wire ends on its own lane
// wherever a datatype survives under it — bending in would cross that datatype's wire.
#let THP = 4.15                                   // a datatype inside `THN`

== Theory

// B&dM §9.1, p. 220.  @sec-opt's problem with the algebra cut down to a MAP `h`; the decompositions
// come from `⦇T⦈°`, and the recursion is over them rather than over an initial algebra.
#disp[#definition[
`h : FB⟶B` a map, #h(4pt) `T : FA⟶A` an F-algebra, #h(4pt) `R : B⟶B`.

`H≜⦇T⦈°⦇h⦈ : A⟶B`, #h(4pt) `M≜` $frac(#[`H`], ∋)$ `est(R)` the problem to be solved, #h(4pt) `(μX : G(X))` as
in @mu-defn.
]]<dp-defn>

// The chapter's chain, at the level every application below instantiates it.  ONE WIRE, `A` to `B`:
// nothing forks, so a row is a run of boxes and what changes is the box the wire runs through.  A
// transpose is a MAP (@pow-laws), hence a square box; `est`, `thin` and `P(−)` are relations, hence
// chamfered.
#let db-LH = (frc([`H`]), 0.95, false)
#let db-est = ([`est(R)`], 1.90, true)
#let db-LT = (frc([`T°`]), 1.20, false)
#let db-thin = ([`thin Q`], 1.90, true)
#let db-PFX = ([`P(F(X)h)`], 2.55, true)
#let db-LV = (frc([`Vᵢ°`]), 1.50, false)
#let db-thini = ([`thin(Qᵢ)`], 2.45, true)
#let db-PU = ([`P(Uᵢ)`], 1.65, true)
#let dp-pan(h, wires, beads, names: false, lanes: ()) = thpan(h, wires, beads,
  ((THO, [`A`]),), ((THO, [`B`]),), lanes: lanes, names: names)
// `H%∋=(𝟙%∋)E(H)`: the unit BIRTHS `E` outside everything and `est(R)` kills it, and `H` is a bead
// with that `E` running past — the pass IS `E`'s action on `H`.  §16.1 opens on the same problem, so
// it draws the same panel; the regions are named only in the first.
#let g-spec-pan(names) = dp-pan(3.0, (((THU, 2.35), (THU, 0.70 + KNEE), (THO, 0.70)),),
  ((THU, 2.35, frc([`𝟙`]), -0.32), (THO, 1.55, [`H`], 0.32), (THO, 0.70, [`est(R)`], 0.32)),
  lanes: ((THU - 0.34, 1.60, [`E`]),), names: names)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`H`])` est(R)⊒(μX : `#frc([`T°`])` thin Q P(F(X)h) est(R))` \
    #src[an optimum over everything `H` returns is reached by taking the input apart every way `T`
     allows, dropping the parts that can never win, solving each of the rest and keeping one
 optimum #h(4pt) ]],
     // lean:AOP.A9_1.dynamic_programming_thin@6b5aa580
  table.header([*circuit* — one wire, `A` to `B`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`A`], [`B`], none, (db-LH, db-est)),
    [`M≜`#frc([`H`])` est(R)` \ #src[the problem to be solved, `H≜⦇T⦈°⦇h⦈` — @dp-defn]])],
  [#g-spec-pan(true)],

  // (9.3) concludes `⊑R°` where B&dM prints `⊑R` (p. 220): his `R` is this `R` conversed as an arrow.
  [#vstep(RQ, thpic([`A`], [`B`], none, (db-LT, db-thin, db-PFX, db-est)),
    [`(μX : `#frc([`T°`])` thin Q P(F(X)h) est(R))` \
     #src[Theorem 9.2, `h` monotonic on `R` and `Q` a preorder with `QF(H)h⊑F(H)hR`; `thin Q` as in
      @thin-laws. Theorem 9.1 is this with the thinning step dropped — `𝟙⊑thin Q`, so the body and
      with it the fixed point only shrink. Knaster–Tarski leaves (9.1) #frc([`T°`])` P(F(M)h)
      est(R)⊑M`; `M=H∩(H°\R°)` splits that into (9.2) #frc([`T°`])` P(F(M)h) est(R)⊑H` and
      (9.3) `H°`#frc([`T°`])` P(F(M)h) est(R)⊑R°`, and both use only (9.4) = (7.10)
      `P(X)est(R)⊑(∋X)∩(∈\(XR°))` — @est-710]])],
  // `T°` births the base functor and `h` kills it; `X` is a bead with `F` running past, which is
  // `F(X)`.  `thin Q : E(FA)⟶E(FA)` rearranges the SET alone, so it is a bead on the `E` wire.
  [#dp-pan(4.6, (((THU, 3.95), (THU, 0.55 + KNEE), (THO, 0.55)), thw-arc(THM, 3.30, 1.45)),
    ((THU, 3.95, frc([`𝟙`]), -0.32), (THO, 3.30, [`T°`], 0.32), (THU, 2.70, [`thin Q`], -0.32),
     (THO, 2.10, [`X`], 0.32), (THO, 1.45, [`h`], 0.32), (THO, 0.55, [`est(R)`], 0.32)),
    lanes: ((THM - 0.34, 2.35, [`F`]), (THU - 0.34, 1.55, [`E`])))],

  [#vstep(EQ, thpic([`A`], [`B`], none, (db-LV, db-thini, db-PU, db-est)),
    [`(Ran V₁→W₁,W₂)`, #h(4pt) `Wᵢ≜`#frc([`Vᵢ°`])` thin(Qᵢ) P(Uᵢ) est(R)` \
     #src[Proposition 9.1 at `T=[V₁,V₂]`, `h=[U₁,U₂]`, `Q=Q₁+Q₂`, `V₂V₁°=⊥`: `FA` is usually a
      coproduct, and disjoint ranges split the fixed point into one branch per summand. The fixed
      point is unique and entire by Theorem 6.3 — `T°` followed by `F`'s membership relation
      inductive, #frc([`T°`]) finite and non-empty, `R` connected]])],
  // One branch of the `→`, not both: it is a union of two restricted branches with the one shape, so
  // the second adds no shape the first does not already show.
  [#dp-pan(3.8, (((THU, 3.15), (THU, 0.60 + KNEE), (THO, 0.60)),),
    ((THU, 3.15, frc([`𝟙`]), -0.32), (THO, 2.55, [`Vᵢ°`], 0.32), (THU, 1.95, [`thin(Qᵢ)`], -0.32),
     (THO, 1.35, [`Uᵢ`], 0.32), (THO, 0.60, [`est(R)`], 0.32)))],
))]<dp-laws>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the condition*], [*how it is discharged*]),

  [`F(R)h⊑hR` \ #src[Proposition 9.2, `R≜cost≤cost°`, `h cost=F(cost)k`,
 `F(≤)k⊑k≤`]],
   // lean:AOP.A9_1.monotonicAlg_of_cost@c2542f9d
  [monotonicity when the cost is itself a fold with a step `k` monotonic on `≤`],
  [`F(R∩(H°H))h⊑hR` \ #src[Proposition 9.3, `R≜cost≤cost°`,
   `h cost=F(⟨cost,H°⟩)k`, `F(≤×𝟙)k⊑k≤`, `H°` simple;
 ]],
   // lean:AOP.A9_1.monotonicAlg_in_context@f0a1b13c
  [monotonicity *in context*: `k` may also read the input the part was built from],
  [`QF(H)h⊑F(H)hR` at `Q≜F(U,V)` \ #src[Proposition 9.4, `U`, `V` preorders, `F(U,R)h⊑hR`,
   `VH⊑HR`]],
  [both conditions of Theorem 9.2 at once, split along the two arguments of a bifunctor],
)]<dp-conditions>

== The string edit problem

// B&dM §9.2, p. 225.  The section numbers no equation.  `base` and `step` are reused for the
// tabulating fold at the foot of the table; they are not `edit`'s.
#disp[#definition[
`Op::=cpy Char∣del Char∣ins Char`, #h(4pt) `F(A,B)=1+(A×B)`, #h(4pt) `α≜[nil,cons]`.

`edit≜⦇[base,step]⦈ : [Op]⟶[Char]×[Char]` #src[],
// lean:AOP.A9_2_Edit.edit_cata@0dafb85c
#h(4pt) `base` returning `([],[])`,
#h(4pt) `step (cpy a,(xs,ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt) `step (del a,(xs,ys))=([a]⧺xs,ys)`,
#h(4pt) `step (ins a,(xs,ys))=(xs,[a]⧺ys)`.

`length≜⦇[zero,π₂ succ]⦈` #src[], #h(4pt)
// lean:AOP.A9_2_Edit.length_cata@9e3040b0
`R≜length≤length°` #src[], #h(4pt) `U≜⊤`, #h(4pt)
// lean:AOP.A9_2_Edit.R_eq@0f7a4661
`V≜suffix°×suffix°` #src[], #h(4pt)
// lean:AOP.A9_2_Edit.V@09fe0b1a
`Q≜𝟙+(U×V)` #src[], #h(4pt) `empty` the coreflexive on `(xs,ys)` with
// lean:AOP.A9_2_Edit.Q@e6ebf648
both lists empty.

`unstep` implements $frac(#[`step°`], ∋)$ `thin(U×V)`
#src[]:
// lean:AOP.A9_2_Edit.unstep@c08a1892 lean:AOP.A9_2_Edit.unstep_sound@623dda5a
#h(4pt) `unstep ([a]⧺xs,[])=[(del a,(xs,[]))]`,
#h(4pt) `unstep ([],[b]⧺ys)=[(ins b,([],ys))]`, #h(4pt)
`unstep ([a]⧺xs,[b]⧺ys)=(a=b→[(cpy a,(xs,ys))],[(del a,(xs,[b]⧺ys)),(ins b,([a]⧺xs,ys))])`.
]]<edit-defn>

// The two strings are a PRODUCT, hence TWO WIRES, and every box here spans them: nothing in the
// chain acts on one string alone.  `Δ` is the relator `X↦X×X`, so `[Char]×[Char]` is `Δ`, `list`,
// `Char` — sugar undone at the ends too.
#let eb-est = ([`est(R)`], 1.90, true)
#let eb-thin = ([`thin Q`], 1.90, true)
#let eb-thinUV = ([`thin(U×V)`], 3.15, true)
#let eb-PX = ([`P([nil,(𝟙×X)cons])`], 5.95, true)
#let eb-PXb = ([`P((𝟙×X)cons)`], 4.10, true)
#let eb-lst = ([`list((𝟙×mle)cons)`], 5.65, true)
#let eb-min = ([`minlist R`], 2.85, false)
#let ed-top = ((THN, [`Δ`], 0.62), (THP, [`list`], 0.24), (THO, [`Char`], 0.62))
#let ed-bot = ((THP, [`list`]), (THO, [`Op`]))
#let ed-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads, ed-top, ed-bot,
  lanes: lanes, names: names)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`edit°`])` est(R)⊒mle`, #h(6pt) `mle=(empty→nil,unstep list((𝟙×mle)cons) minlist R)` \
    #src[a shortest edit sequence from which both strings can be reconstituted is one pass over the
     two of them, each step copying, deleting or inserting one character and the best sequence for
     what is left taken from the entries already computed]],
  table.header([*circuit* — two wires, one per string], [*Hinze–Marsden*]),

  [#vstep([], gpair([`[Char]`], [`[Char]`], [`[Op]`], frc([`edit°`]), 2.15, (eb-est,)),
    [#frc([`edit°`])` est(R)` \ #src[the specification — @edit-defn]])],
  // `edit°` eats `Δ` and the source `list` and MAKES the target one, so every strand lands on it;
  // `est(R) : E([Op])⟶[Op]` kills the set alone, so its wire ends on the `E` lane.
  [#ed-pan(3.6, (((THU, 2.95), (THU, 0.60)), thw-in(THN, 3.6, 1.85), thw-in(THP, 3.6, 1.85),
      thw-out(THP, 1.85, 0)),
    ((THU, 2.95, frc([`𝟙`]), -0.32), (THO, 1.85, [`edit°`], 0.32), (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THU - 0.34, 1.75, [`E`]),), names: true)],

  [#vstep(RQ, gpair([`[Char]`], [`[Char]`], [`[Op]`], frc([`[base,step]°`]), 4.30,
      (eb-thin, eb-PX, eb-est)),
    [`(μX : `#frc([`[base,step]°`])` thin Q P([nil,(𝟙×X)cons]) est(R))`
 #src[] \
     // lean:AOP.A9_2_Edit.edit_laws@c69d7d69
     #src[Theorem 9.2 at `Q≜𝟙+(U×V)`. Monotonicity `F(R)α⊑αR`
 #src[] is Proposition 9.2 at
      // lean:AOP.A9_2_Edit.edit_mono@089b97ab
      `length≜⦇[zero,π₂ succ]⦈` with `succ` monotonic on `≤`, so `cons` is monotonic on `R`. The
      thinning condition `QF(𝟙,edit°)α⊑F(𝟙,edit°)αR`
 #src[] over `F(Op,[Char]×[Char])` is
      // lean:AOP.A9_2_Edit.edit_thin_condition@e22f4fe4
      Proposition 9.4 at `U≜⊤` — `F(⊤,R)α⊑αR`, left as an exercise, so any two operations may be
      compared — and `V≜suffix°×suffix°`
 #src[,
      // lean:Freyd.Alg.RelSet.Edit.edit_V@274d4558
 ] —
      // lean:AOP.A9_2_Edit.edit_Vrecip@1d49fb2e
 `edit (𝟙×suffix)⊑R° edit` #src[],
      // lean:AOP.A9_2_Edit.edit_suffix_right@6e4ee2a2
 `edit (suffix×𝟙)⊑R° edit` #src[]. `suffix=tail*`
      // lean:AOP.A9_2_Edit.edit_suffix_left@dda69ad1
      and `BA⊑CB⟹BA*⊑C*B` cut those to one step each: drop the operation that produced the head, or
      weaken its `cpy` to a `del`, never lengthening the sequence]])],
  // `[base,step]°` opens the base functor INSIDE the set the singleton opened, and the algebra
  // closes it again; `Δ` and the source `list` die and are remade at both beads, so each runs as a
  // loop between them.  `thin Q : E(F−)⟶E(F−)` rearranges the set alone: a bead on the `E` wire.
  [#ed-pan(6.4, (((THU, 5.70), (THU, 0.60)), thw-in(THN, 6.4, 4.70), thw-in(THP, 6.4, 4.70),
      thw-arc(THM, 4.70, 1.70), thw-arc(THN, 4.70, 1.70), thw-arc(THP, 4.70, 1.70),
      thw-out(THP, 1.70, 0)),
    ((THU, 5.70, frc([`𝟙`]), -0.32), (THO, 4.70, [`[base,step]°`], 0.32),
     (THU, 3.90, [`thin Q`], -0.32), (THO, 1.70, [`[nil,(𝟙×X)cons]`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THM, 5.55, [`F`]),))],

  [#vstep(EQ, gpair([`[Char]`], [`[Char]`], [`[Op]`], frc([`step°`]), 2.15,
      (eb-thinUV, eb-PXb, eb-est)),
    [`(μX : (empty→nil,`#frc([`step°`])` thin(U×V) P((𝟙×X)cons) est(R)))` \
     #src[Proposition 9.1: `base` and `step` have disjoint ranges, so the fixed point splits into
      one branch per summand — `empty`, the coreflexive on `(xs,ys)` with both lists empty, is where
      `base` returns]])],
  // The `step` branch of the `→`, not both: the `base` branch is `nil` on an empty pair, nothing to
  // draw.  `Op×−` is the summand `step°` opens.
  [#ed-pan(6.4, (((THU, 5.70), (THU, 0.60)), thw-in(THN, 6.4, 4.70), thw-in(THP, 6.4, 4.70),
      thw-arc(THM, 4.70, 1.70), thw-arc(THN, 4.70, 1.70), thw-arc(THP, 4.70, 1.70),
      thw-out(THP, 1.70, 0)),
    ((THU, 5.70, frc([`𝟙`]), -0.32), (THO, 4.70, [`step°`], 0.32),
     (THU, 3.90, [`thin(U×V)`], -0.32), (THO, 1.70, [`(𝟙×X)cons`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THM, 5.55, [`Op×−`]),))],

  [#vstep(RQ, gpair([`[Char]`], [`[Char]`], [`[Op]`], [`unstep`], 2.00, (eb-lst, eb-min)),
    [`mle=(empty→nil,unstep list((𝟙×mle)cons) minlist R)` \
     #src[`unstep` implements #frc([`step°`])` thin(U×V)` — at most two decompositions survive, a
      copy beating a delete or an insert wherever it is available — and `minlist R` implements
      `est(R)`. The same subproblem is solved many times over, so the running time is exponential in
      the two lengths]])],
  // The program is the branch above with each box replaced by a function computing it, so the wires
  // and the beads are the same picture: only the labels change.
  [#ed-pan(6.4, (((THU, 5.70), (THU, 0.60)), thw-in(THN, 6.4, 4.70), thw-in(THP, 6.4, 4.70),
      thw-arc(THM, 4.70, 1.70), thw-arc(THN, 4.70, 1.70), thw-arc(THP, 4.70, 1.70),
      thw-out(THP, 1.70, 0)),
    ((THU, 5.70, frc([`𝟙`]), -0.32), (THO, 4.70, [`unstep`], 0.32),
     (THO, 1.70, [`(𝟙×mle)cons`], 0.32), (THU, 0.60, [`minlist R`], -0.32)),
    lanes: ((THM, 5.55, [`Op×−`]),))],

  [#vstep(EQ, [],
    [`mle (xs,ys)=head (column xs ys)`, #h(4pt) `column xs ys=[mle (u,ys)∣u←tails xs]` \
     `column xs=⦇[fstcol xs,nextcol xs]⦈`, #h(4pt) `fstcol=list(del) tails` \
     #src[the tabulation: `mle (xs,ys)` needs `mle (u,v)` for every tail `u` of `xs` and `v` of
      `ys`, so the columns are built right to left]])],
  // No picture: a curried function on lists is not a relation between the objects the panels carry.
  [],

  [#vstep(EQ, [],
    [`column xs ([b]⧺ys)=nextcol xs (b,column xs ys)` \
     `nextcol xs (b,us)=⦇[base (b,last us),step b]⦈ xus`, #h(4pt)
     `xus=zip (xs,zip (init us,tail us))` \
     #src[each column is a fold built bottom to top, over `xs` zipped with the adjacent pairs of the
      column to its right]])],
  [],

  [#vstep(EQ, [],
    [`base (b,u)=[[ins b]⧺u]` \ `step b ((a,(u,v)),ws)=(a=b→[[cpy a]⧺v]⧺ws,`
     `[bmin(R) ([del a]⧺w,[ins b]⧺u)]⧺ws)` \
     #src[`w=head ws`; these `base`, `step` are not `edit`'s. An entry depends on the one below it
      (a delete), the one to its right (an insert), and the one below that (a copy) — quadratic in
      the two lengths]])],
  [],
))]<edit-laws>

== Optimal bracketing

// B&dM §9.3, p. 230.  `⦇T⦈ = flatten` is a map, so `H° = flatten` is simple and Proposition 9.3
// applies; no decomposition is preferable to another here, so there is no thinning step.
#disp[#definition[
`tree A::=tip A∣bin (tree A,tree A)`, #h(4pt) `FX=A+X²`, so `F(R)=𝟙+R²`; #h(4pt)
`h≜[tip,bin]`, #h(4pt) `flatten≜⦇[wrap,cat]⦈ : tree A⟶list⁺ A`
#src[], #h(4pt) `H=flatten°`.
// lean:AOP.A9_3_Bracket.flatten_cata@416f62ee

`⟨cost,size⟩≜⦇[opt,opb]⦈`, #h(4pt) `opt≜⟨zero,st⟩`, #h(4pt)
`opb ((cx,sx),(cy,sy))=(cb (sx,sy)+cx+cy,sb (sx,sy))`.

`sb` associative, so `size=flatten sz` for a map `sz`
#src[]; #h(4pt)
// lean:AOP.A9_3_Bracket.size_eq_sz_flatten@e6003d74
`R≜cost≤cost°` #src[], #h(4pt)
// lean:AOP.A9_3_Bracket.R_eq@48f5ee2a
`g≜[zero,(𝟙×sz)² opb π₁]`, #h(4pt) `single` the coreflexive on singleton lists.

`splits≜⟨inits⁺,tails⁺⟩ zip`, an implementation of $frac(#[`cat°`], ∋)$; #h(4pt) `array≜inits list(row)`,
#h(4pt) `row≜tails list(mct)`, #h(4pt) `col≜inits list(mct)`.

`mix≜zip list(bin) minlist R`, #h(4pt) `next≜⟨π₁,mix⟩ snoc`, #h(4pt)
`process≜((tip wrap)×𝟙) loop(next)`.
]]<mct-defn>

// ONE WIRE, `list⁺ A` to `tree A`, and one datatype lane carrying `list⁺` above the bead that eats
// it and `tree` below.  No thinning step: no decomposition of a list is preferable to another here.
#let mb-estR = ([`est(R)`], 1.90, true)
#let mb-Lfl = (frc([`flatten°`]), 3.05, false)
#let mb-Lwc = (frc([`[wrap,cat]°`]), 4.00, false)
#let mb-Ptip = ([`P([tip,(X×X)bin])`], 5.35, true)
#let mb-Lcat = (frc([`cat°`]), 1.80, false)
#let mb-Pbin = ([`P((X×X)bin)`], 3.50, true)
#let mb-splits = ([`splits`], 1.90, false)
#let mb-lbin = ([`list((mct×mct)bin)`], 5.65, true)
#let mb-min = ([`minlist R`], 2.85, false)
#let mc-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THN, [`list⁺`]), (THO, [`A`])), ((THN, [`tree`]), (THO, [`A`])), lanes: lanes, names: names)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`flatten°`])` est(R)⊒mct`, #h(6pt) `mct=(single→head tip,⟨init col,tail row⟩ mix)` \
    #src[a least-cost bracketing of `a₁⊕⋯⊕aₙ` is read off an array holding one best tree per
     non-empty segment, each entry built from the column to its left and the row below it]],
  table.header([*circuit* — one wire, `list⁺ A` to `tree A`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`list⁺ A`], [`tree A`], none, (mb-Lfl, mb-estR)),
    [#frc([`flatten°`])` est(R)` \ #src[the specification — @mct-defn]])],
  // `flatten°` eats `list⁺` and MAKES `tree`, so one lane carries both; `est(R) : E(tree A)⟶tree A`
  // kills the set alone and its wire ends on the `E` lane, `tree` surviving under it.
  [#mc-pan(3.6, (((THU, 2.95), (THU, 0.60)), thw-in(THN, 3.6, 1.85), thw-out(THN, 1.85, 0)),
    ((THU, 2.95, frc([`𝟙`]), -0.32), (THO, 1.85, [`flatten°`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THU - 0.34, 1.75, [`E`]),), names: true)],

  [#vstep(RQ, thpic([`list⁺ A`], [`tree A`], none, (mb-Lwc, mb-Ptip, mb-estR)),
    [`(μX : `#frc([`[wrap,cat]°`])` P([tip,(X×X)bin]) est(R))`
 #src[] \
     // lean:AOP.A9_3_Bracket.mct_laws@6ebebce1
     #src[Theorem 9.1: split the list in every way, bracket both halves, join. The condition is
      monotonicity *in context*, `F(R∩(flatten flatten°))h⊑hR`
 #src[] — only trees with the same flattening
      // lean:AOP.A9_3_Bracket.mct_mono@a3daf2b8
      are compared — which is Proposition 9.3 at `H°=flatten`, a map, with (9.5)
 `[tip,bin] cost=(𝟙+⟨cost,flatten⟩²)g` #src[]
      // lean:AOP.A9_3_Bracket.mct_cost_alg@f266a5f3
      (the cost of a node reads only the cost and the
      flattening of its two subtrees) and (9.6) `(𝟙+(≤×𝟙)²)g⊑g≤`
 #src[] (`g` monotonic on `≤` in its two
      // lean:AOP.A9_3_Bracket.mct_g_mono@4aa3e122
      cost arguments)]])],
  // `[wrap,cat]°` opens the base functor `A+(−)²` inside the set and `[tip,(X×X)bin]` closes it;
  // `list⁺` dies and is remade at both, so it runs as a loop between them.
  [#mc-pan(5.6, (((THU, 4.90), (THU, 0.60)), thw-in(THN, 5.6, 4.10),
      thw-arc(THM, 4.10, 1.60), thw-arc(THN, 4.10, 1.60), thw-out(THN, 1.60, 0)),
    ((THU, 4.90, frc([`𝟙`]), -0.32), (THO, 4.10, [`[wrap,cat]°`], 0.32),
     (THO, 1.60, [`[tip,(X×X)bin]`], 0.32), (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THM, 4.85, [`A+(−)²`]),))],

  [#vstep(EQ, thpic([`list⁺ A`], [`tree A`], none, (mb-Lcat, mb-Pbin, mb-estR)),
    [`(μX : (single→wrap° tip,`#frc([`cat°`])` P((X×X)bin) est(R)))` \
     #src[Proposition 9.1: `wrap` and `cat` have disjoint ranges, and `single` is the coreflexive on
      singleton lists, where `wrap` returns]])],
  // The `cat` branch of the `→`, not both: the `wrap` branch is one bead on a singleton, nothing the
  // `cat` branch does not already show.  `(−)²` is the summand `cat°` opens.
  [#mc-pan(5.6, (((THU, 4.90), (THU, 0.60)), thw-in(THN, 5.6, 4.10),
      thw-arc(THM, 4.10, 1.60), thw-arc(THN, 4.10, 1.60), thw-out(THN, 1.60, 0)),
    ((THU, 4.90, frc([`𝟙`]), -0.32), (THO, 4.10, [`cat°`], 0.32),
     (THO, 1.60, [`(X×X)bin`], 0.32), (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THM, 4.85, [`(−)²`]),))],

  [#vstep(RQ, thpic([`list⁺ A`], [`tree A`], none, (mb-splits, mb-lbin, mb-min)),
    [`mct=(single→head tip,splits list((mct×mct)bin) minlist R)` \
     #src[`splits≜⟨inits⁺,tails⁺⟩ zip` implements #frc([`cat°`]) and `minlist R` implements
      `est(R)`. Exponential, since the segments of one list overlap]])],
  [#mc-pan(5.6, (((THU, 4.90), (THU, 0.60)), thw-in(THN, 5.6, 4.10),
      thw-arc(THM, 4.10, 1.60), thw-arc(THN, 4.10, 1.60), thw-out(THN, 1.60, 0)),
    ((THU, 4.90, frc([`𝟙`]), -0.32), (THO, 4.10, [`splits`], 0.32),
     (THO, 1.60, [`(mct×mct)bin`], 0.32), (THU, 0.60, [`minlist R`], -0.32)),
    lanes: ((THM, 4.85, [`(−)²`]),))],

  [#vstep(EQ, [],
    [`mct=(single→head tip,⟨init col,tail row⟩ mix)` #h(4pt) #src[(9.7)] \
     #src[the tabulation: `mct xs` is needed for every non-empty segment `xs`, so the values are
      held as an array of rows, `array≜inits list(row)`, `row≜tails list(mct)`,
      `col≜inits list(mct)`, `mix≜zip list(bin) minlist R`]])],
  // No picture: the tabulated program relates arrays of trees, not the objects the panels carry.
  [],

  [#vstep(EQ, [],
    [`col=(single→head tip wrap,⟨init col,tail row⟩ next)` #h(4pt) #src[(9.8)] \
     `cons col=(𝟙×array) process` #h(4pt) #src[(9.9)] \
     `row=(single→head tip wrap,⟨mct,tail row⟩ cons)` #h(4pt) #src[(9.10)] \
     #src[a column extends the column to its left, a row the row below it; (9.9) is (9.8) rewritten
      as a loop, `next≜⟨π₁,mix⟩ snoc`, `process≜((tip wrap)×𝟙) loop(next)`]])],
  [],

  [#vstep(EQ, [],
    [`array=⦇[fstcol,addcol]⦈`, #h(4pt) `fstcol≜tip wrap wrap` \
     `addcol≜⟨π₁ tip wrap,step⟩ cons`, #h(4pt) `step≜⟨process tail,π₂⟩ zip list(cons)` \
     #src[the program: one fold building the array column by column, cubic in the length of the
      input]])],
  [],
))]<mct-laws>

== Data compression

// B&dM §9.4, p. 238.  Snoc-lists throughout.  No numbered equations, and no tabulation phase — the
// book stops at the recursive program and says the details are messy.
#disp[#definition[
`[A]::=nil∣snoc ([A],A)`, #h(4pt) `list⁺ A::=wrap A∣snoc (list⁺ A,A)`, #h(4pt)
`String=[Char]`, #h(4pt) `Code::=sym Char∣ptr (String,String⁺)`, #h(4pt)
`F(Code,String)=1+(String×Code)`, #h(4pt) `α≜[nil,snoc]`.

`decode≜⦇[nil,extend]⦈ : [Code]⟶String`, #h(4pt) `extend (xs,sym a)=xs⧺[a]`, #h(4pt)
`extend (xs,ptr (ys,zs))=xs⧺zs` when `ys⧺zs` is a proper prefix of `xs⧺zs`; #h(4pt)
`H=decode°`.

`size≜⦇[zero,distr [𝟙×c,𝟙×p] plus]⦈` with `c`, `p` the constant costs of a symbol and a
pointer; #h(4pt) `R≜size≤size°`, #h(4pt) `Q≜F(⊤+⊤,prefix°)=𝟙+(prefix°×(⊤+⊤))`, the
two `⊤` on symbols and on pointers.

`lrt ws=est(prefix°×(⊤+⊤)) {(xs,(ys,zs))∣xs⧺zs=ws`, `ys⧺zs` a proper prefix of `ws}`,
the longest repeated tail; #h(4pt)
`reduce (ws⧺[a])=(zs≠[]→[(ws,sym a),(xs,ptr (ys,zs))],[(ws,sym a)])` with
`(xs,(ys,zs))=lrt (ws⧺[a])`.
]]<code-defn>

// ONE WIRE, `String` to `[Code]`, and one `list` lane: the string above the bead that eats it, the
// code sequence below.  Snoc-lists throughout, so the base functor is `(−)×Code`.
#let cb-estR = ([`est(R)`], 1.90, true)
#let cb-thin = ([`thin Q`], 1.90, true)
#let cb-Ldec = (frc([`decode°`]), 2.75, false)
#let cb-Lne = (frc([`[nil,extend]°`]), 4.60, false)
#let cb-Psnoc = ([`P([nil,(X×𝟙)snoc])`], 5.65, true)
#let cb-Lext = (frc([`extend°`]), 2.75, false)
#let cb-thinp = ([`thin(prefix°×(⊤+⊤))`], 5.95, true)
#let cb-Pb = ([`P((X×𝟙)snoc)`], 3.80, true)
#let cb-red = ([`reduce`], 1.90, false)
#let cb-lst = ([`list((encode×𝟙)snoc)`], 6.25, true)
#let cb-min = ([`minlist R`], 2.85, false)
#let co-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THN, [`list`]), (THO, [`Char`])), ((THN, [`list`]), (THO, [`Code`])),
  lanes: lanes, names: names)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`decode°`])` est(R)⊒encode`, #h(6pt)
    `encode=(null→nil,reduce list((encode×𝟙)snoc) minlist R)` \
    #src[a smallest code sequence decoding to the given string is built from the right, each step
     emitting the last character as a symbol or ending with a pointer back into what has already
     been decoded]],
  table.header([*circuit* — one wire, `String` to `[Code]`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`String`], [`[Code]`], none, (cb-Ldec, cb-estR)),
    [#frc([`decode°`])` est(R)` \ #src[the specification — @code-defn]])],
  [#co-pan(3.6, (((THU, 2.95), (THU, 0.60)), thw-in(THN, 3.6, 1.85), thw-out(THN, 1.85, 0)),
    ((THU, 2.95, frc([`𝟙`]), -0.32), (THO, 1.85, [`decode°`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THU - 0.34, 1.75, [`E`]),), names: true)],

  [#vstep(RQ, thpic([`String`], [`[Code]`], none, (cb-Lne, cb-thin, cb-Psnoc, cb-estR)),
    [`(μX : `#frc([`[nil,extend]°`])` thin Q P([nil,(X×𝟙)snoc]) est(R))` \
     #src[Theorem 9.2 at `Q≜F(⊤+⊤,prefix°)=𝟙+(prefix°×(⊤+⊤))`, the two `⊤` on symbols and on
      pointers. Monotonicity `F(R)α⊑αR` is routine, the two costs being constants:
      `(⊤+⊤)[c,p]=[c,p]`. Proposition 9.4 splits the thinning condition in two — `F(⊤+⊤,R)α⊑αR`,
      and `decode prefix⊑R° decode`, for which `decode init⊑R° decode` is enough: dropping the last
      character of the output shortens or removes the last code element and never raises the cost.
      So between a symbol and a pointer nothing can be decided in advance, and between two pointers
      the longer match wins]])],
  // `[nil,extend]°` opens `(−)×Code` inside the set the singleton opened and `[nil,(X×𝟙)snoc]`
  // closes it; `list` dies and is remade at both beads, so it runs as a loop between them.
  [#co-pan(6.4, (((THU, 5.70), (THU, 0.60)), thw-in(THN, 6.4, 4.70),
      thw-arc(THM, 4.70, 1.70), thw-arc(THN, 4.70, 1.70), thw-out(THN, 1.70, 0)),
    ((THU, 5.70, frc([`𝟙`]), -0.32), (THO, 4.70, [`[nil,extend]°`], 0.32),
     (THU, 3.90, [`thin Q`], -0.32), (THO, 1.70, [`[nil,(X×𝟙)snoc]`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THM, 5.55, [`−×Code`]),))],

  [#vstep(EQ, thpic([`String`], [`[Code]`], none, (cb-Lext, cb-thinp, cb-Pb, cb-estR)),
    [`(μX : (null→nil,`#frc([`extend°`])` thin(prefix°×(⊤+⊤)) P((X×𝟙)snoc) est(R)))` \
     #src[Proposition 9.1: `nil` and `extend` have disjoint ranges. The decompositions of one string
      are #frc([`extend°`])` (ws⧺[a])={(ws,sym a)}∪{(xs,ptr (ys,zs))∣xs⧺zs=ws⧺[a]`, `ys⧺zs` a
      proper prefix of `ws}` — take the last character as a symbol, or end with a pointer]])],
  [#co-pan(6.4, (((THU, 5.70), (THU, 0.60)), thw-in(THN, 6.4, 4.70),
      thw-arc(THM, 4.70, 1.70), thw-arc(THN, 4.70, 1.70), thw-out(THN, 1.70, 0)),
    ((THU, 5.70, frc([`𝟙`]), -0.32), (THO, 4.70, [`extend°`], 0.32),
     (THU, 3.90, [`thin(prefix°×(⊤+⊤))`], -0.32), (THO, 1.70, [`(X×𝟙)snoc`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THM, 5.55, [`−×Code`]),))],

  [#vstep(RQ, thpic([`String`], [`[Code]`], none, (cb-red, cb-lst, cb-min)),
    [`encode=(null→nil,reduce list((encode×𝟙)snoc) minlist R)` \
     #src[`reduce` implements #frc([`extend°`])` thin(prefix°×(⊤+⊤))`: thinning leaves at most two,
      the symbol and the pointer of the longest repeated tail `lrt`. Again exponential; the book
      gives no tabulation for it]])],
  [#co-pan(6.4, (((THU, 5.70), (THU, 0.60)), thw-in(THN, 6.4, 4.70),
      thw-arc(THM, 4.70, 1.70), thw-arc(THN, 4.70, 1.70), thw-out(THN, 1.70, 0)),
    ((THU, 5.70, frc([`𝟙`]), -0.32), (THO, 4.70, [`reduce`], 0.32),
     (THO, 1.70, [`(encode×𝟙)snoc`], 0.32), (THU, 0.60, [`minlist R`], -0.32)),
    lanes: ((THM, 5.55, [`−×Code`]),))],
))]<code-laws>

#pagebreak(weak: true)
= Greedy Algorithms <sec-greedy>

== Theory

// B&dM §10.1, p. 245.  Theorem 9.2 with `est(Q)` for `thin Q`: the same hypotheses, a much stronger
// conclusion, and one far harder to refine into a program.
#disp[#definition[
`h`, `T`, `R`, `H`, `M` as in @dp-defn; #h(4pt) additionally `Q` a *connected* preorder on the sets
$frac(#[`T°`], ∋)$ returns, so that $frac(#[`T°`], ∋)$ `est(Q)` is entire.
]]<greedy-defn>

#let gb-estQ = ([`est(Q)`], 1.90, true)
#let gb-FXh = ([`F(X)h`], 1.85, true)
#let gb-estQi = ([`est(Qᵢ)`], 2.15, true)
#let gb-Ui = ([`Uᵢ`], 0.90, true)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`H`])` est(R)⊒(μX : `#frc([`T°`])` est(Q) F(X)h)` \
    #src[the same optimum reached by keeping ONE decomposition at each step, so that no set is ever
 carried and the recursion runs on values alone #h(4pt) ]],
     // lean:AOP.A10_1.greedy_dp@93506ebf
  table.header([*circuit* — one wire, `A` to `B`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`A`], [`B`], none, (db-LH, db-est)),
    [`M≜`#frc([`H`])` est(R)` \ #src[the problem to be solved, `H≜⦇T⦈°⦇h⦈` — @greedy-defn]])],
  [#g-spec-pan(false)],

  [#vstep(RQ, thpic([`A`], [`B`], none, (db-LT, gb-estQ, gb-FXh)),
    [`(μX : `#frc([`T°`])` est(Q) F(X)h)` \
     #src[Theorem 10.1]])],
  // `est(Q) : E(FA)⟶FA` kills the SET but not the `F` under it, so its wire ends on the `E` lane:
  // bending in would cross `F`.  That free end is the whole difference from @dp-laws' second row.
  [#dp-pan(4.4, (((THU, 3.95), (THU, 2.55)), thw-arc(THM, 3.30, 0.90)),
    ((THU, 3.95, frc([`𝟙`]), -0.32), (THO, 3.30, [`T°`], 0.32), (THU, 2.55, [`est(Q)`], -0.32),
     (THO, 1.70, [`X`], 0.32), (THO, 0.90, [`h`], 0.32)),
    lanes: ((THM - 0.34, 2.10, [`F`]),))],

  [#vstep(EQ, thpic([`A`], [`B`], none, (db-LV, gb-estQi, gb-Ui)),
    [`(Ran V₁→W₁,W₂)`, #h(4pt) `Wᵢ≜`#frc([`Vᵢ°`])` est(Qᵢ) Uᵢ` \
     #src[Proposition 10.1 at `T=[V₁,V₂]`, `h=[U₁,U₂]`, `Q=Q₁+Q₂`, `V₂V₁°=⊥`]])],
  // The branch, not the conditional; nothing survives outside the set here, so `est(Qᵢ)` lands on
  // the object wire.
  [#dp-pan(3.4, (((THU, 2.85), (THU, 1.40 + KNEE), (THO, 1.40)),),
    ((THU, 2.85, frc([`𝟙`]), -0.32), (THO, 2.25, [`Vᵢ°`], 0.32), (THO, 1.40, [`est(Qᵢ)`], 0.32),
     (THO, 0.65, [`Uᵢ`], 0.32)))],
))]<greedy-laws>

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

// ONE WIRE, `String` to `String`; `F(X)h` is drawn as the ONE bead the formula writes,
// `(𝟙+(X×𝟙))[nil,snoc]`, so the `list` lane pinches twice rather than three times.
#let nb-est = ([`est(R)`], 1.90, true)
#let nb-Ldet = (frc([`detab°`]), 2.45, false)
#let nb-Lnx = (frc([`[nil,expand]°`]), 4.60, false)
#let nb-estQ = ([`est(Q)`], 1.90, true)
#let nb-alg = ([`(𝟙+(X×𝟙))[nil,snoc]`], 6.25, true)
#let nb-Lexp = (frc([`expand°`]), 2.75, false)
#let nb-estVU = ([`est(V×U)`], 2.55, true)
#let nb-snoc = ([`(X×𝟙)snoc`], 2.85, true)
#let en-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THN, [`list`]), (THO, [`Char`])), ((THN, [`list`]), (THO, [`Char`])),
  lanes: lanes, names: names)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`detab°`])` est(R)⊒entab`, #h(6pt) `entab=triple assocl π₁ (𝟙×blanks) cat` \
    #src[the shortest input `detab` expands to the given output is one pass along that output,
     holding each blank back and cashing the held blanks in for a tab wherever the column reaches a
     tab stop]],
  table.header([*circuit* — one wire, `String` to `String`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`String`], [`String`], none, (nb-Ldet, nb-est)),
    [#frc([`detab°`])` est(R)` \ #src[the specification — @entab-defn; `detab entab=𝟙` and nothing
     shorter does]])],
  [#en-pan(3.6, (((THU, 2.95), (THU, 0.60)), thw-in(THN, 3.6, 1.85), thw-out(THN, 1.85, 0)),
    ((THU, 2.95, frc([`𝟙`]), -0.32), (THO, 1.85, [`detab°`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THU - 0.34, 1.75, [`E`]),), names: true)],

  [#vstep(RQ, thpic([`String`], [`String`], none, (nb-Lnx, nb-estQ, nb-alg)),
    [`(μX : `#frc([`[nil,expand]°`])` est(Q)(𝟙+(X×𝟙))[nil,snoc])`
 #src[] \
     // lean:AOP.A10_2_Detab.entab_laws@3b89184f
     #src[Theorem 10.1 at `Q≜𝟙+(V×U)`
 #src[]: one character of input is
      // lean:AOP.A10_2_Detab.entab_thin_condition@4bf50608
      decided at each step. `F(⊤,R)α⊑αR`#src[].
      // lean:AOP.A10_2_Detab.entab_mono@b7c30f2e
      `detab prefix⊑R° detab` is
 FALSE #src[,
      // lean:AOP.A10_2_Detab.detab_prefix_false@5fe54dc9
 ] — at `n=8`,
      // lean:AOP.A10_2_Detab.detab_len_of_short@66be497e
      `detab [a,b,c,d,e,TB]=[a,b,c,d,e,BL,BL,BL]`, whose prefix
      `[a,b,c,d,e,BL,BL]` is longer than any input giving it, and `detab V°⊑R° detab`
 #src[]
      // lean:Freyd.Alg.RelSet.Detab.detab_V@332fe8ac lean:AOP.A10_2_Detab.entab_V@ff19c265
      holds. `expand V°⊑expand∪(π₁V°)`
 #src[] — shortening the output either leaves the
      // lean:AOP.A10_2_Detab.expand_V_step@1e653239
      last step alone or discards it]])],
  // `[nil,expand]°` opens `−×Char` inside the set the singleton opened; `est(Q)` kills that set but
  // not the `F` under it, so its wire ends on the `E` lane.
  [#en-pan(5.6, (((THU, 4.90), (THU, 3.30)), thw-in(THN, 5.6, 4.10),
      thw-arc(THM, 4.10, 1.60), thw-arc(THN, 4.10, 1.60), thw-out(THN, 1.60, 0)),
    ((THU, 4.90, frc([`𝟙`]), -0.32), (THO, 4.10, [`[nil,expand]°`], 0.32),
     (THU, 3.30, [`est(Q)`], -0.32), (THO, 1.60, [`(𝟙+(X×𝟙))[nil,snoc]`], 0.32)),
    lanes: ((THM, 4.85, [`−×Char`]),))],

  [#vstep(EQ, thpic([`String`], [`String`], none, (nb-Lexp, nb-estVU, nb-snoc)),
    [`(μX : (null→nil,`#frc([`expand°`])` est(V×U)(X×𝟙)snoc))` \
     #src[Proposition 10.1: `nil` and `expand` have disjoint ranges. The greedy step is to emit
      a tab whenever a tab is legal, consuming all the blanks back to the previous tab stop]])],
  [#en-pan(5.6, (((THU, 4.90), (THU, 3.30)), thw-in(THN, 5.6, 4.10),
      thw-arc(THM, 4.10, 1.60), thw-arc(THN, 4.10, 1.60), thw-out(THN, 1.60, 0)),
    ((THU, 4.90, frc([`𝟙`]), -0.32), (THO, 4.10, [`expand°`], 0.32),
     (THU, 3.30, [`est(V×U)`], -0.32), (THO, 1.60, [`(X×𝟙)snoc`], 0.32)),
    lanes: ((THM, 4.85, [`−×Char`]),))],

  [#vstep(EQ, [],
    [`entab xs=entab (unfill xs)⧺blanks (tbc xs)` #h(4pt) #src[(10.1)] \
     #src[what makes `triple≜⟨unfill entab,⟨tbc,col⟩⟩` a snoc-list reduce: the output splits at the
      last tab stop]])],
  // No picture: `entab` is here read on points, and the equation relates two strings, not two
  // objects the panels carry.
  [],

  [#vstep(EQ, [],
    [`triple=⦇[base,op]⦈`, #h(4pt) `entab=triple assocl π₁ (𝟙×blanks) cat` \
     `base` returns `([],(0,0))`, #h(4pt) `op ((xs,(t,c)),a)=` \ #h(10pt)
     `(a=BL∧(c+1) mod n≠0→(xs,(t+1,c+1)),` #h(4pt) `a=BL→(xs⧺[TB],(0,c+1)),` \ #h(10pt)
     `a=NL→(xs⧺blanks t⧺[NL],(0,0)),` #h(4pt) `(xs⧺blanks t⧺[a],(0,c+1)))` \
     #src[the program: one pass carrying the column and the count of pending blanks]])],
  [],
))]<entab-laws>

== The minimum tardiness problem

// B&dM §10.3, p. 253.  Both conditions need context, and `cost` has to be restated over `perm xs`
// before Proposition 9.3 fits — `penalty` reads the bag of scheduled jobs, not their order.
#disp[#definition[
`FX=1+(X×Job)`, #h(4pt) `α≜[nil,snoc]` on schedules, #h(4pt) `β≜[nil,snag]` on bags,
`snag` putting a job into a bag; #h(4pt) `bagify≜⦇β⦈ : [Job]⟶Bag Job`, #h(4pt) `H=bagify°`.

`ct`, `dt`, `wt : Job⟶Real` the completion, due and weighting quantities of a job; #h(4pt)
`penalty (xs,j)=(sum (list(ct) xs)+ct j−dt j)×wt j`.

`cost≜` $frac(#[`prefix`], ∋)$ `P(α° [zero,penalty]) est(≥)`, #h(4pt) `cost []=0`, #h(4pt)
`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))`, #h(4pt) `R≜cost≤cost°`.

`perm≜bagify bagify°=⦇[nil,add]⦈`, #h(4pt) `add (xs,j)=ys⧺[j]⧺zs` for some `xs=ys⧺zs`.

`k≜[zero,assocr (𝟙×((bagify°×𝟙) penalty)) bmax]`, #h(4pt)
`f≜[zero,(bagify°×𝟙) penalty]`, #h(4pt) `Q≜f≤f°`.
]]<tardy-defn>

// ONE WIRE, `Bag Job` to `[Job]`, one datatype lane carrying `bag` above the bead that eats it and
// `list` below.  The last row has NO `E` wire: `pick` is where the greedy program stops carrying a
// set at all.
#let tb-estR = ([`est(R)`], 1.90, true)
#let tb-Lbag = (frc([`bagify°`]), 2.75, false)
#let tb-Lb = (frc([`β°`]), 1.25, false)
#let tb-estQ = ([`est(Q)`], 1.90, true)
#let tb-alg = ([`(𝟙+(X×𝟙))[nil,snoc]`], 6.25, true)
#let tb-Lsnag = (frc([`snag°`]), 2.15, false)
#let tb-snoc = ([`(X×𝟙)snoc`], 2.85, true)
#let tb-pick = ([`pick`], 1.50, false)
#let tb-sch = ([`(schedule×𝟙)snoc`], 4.90, true)
#let ty-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THN, [`bag`]), (THO, [`Job`])), ((THN, [`list`]), (THO, [`Job`])),
  lanes: lanes, names: names)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`bagify°`])` est(R)⊒schedule`, #h(6pt) `schedule=(null→nil,pick (schedule×𝟙) snoc)` \
    #src[an ordering of the given bag with least maximum penalty is got by taking a job of least
     penalty out of the bag, putting it last, and scheduling what is left the same way]],
  table.header([*circuit* — one wire, `Bag Job` to `[Job]`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`Bag Job`], [`[Job]`], none, (tb-Lbag, tb-estR)),
    [#frc([`bagify°`])` est(R)` \ #src[the specification — @tardy-defn]])],
  [#ty-pan(3.6, (((THU, 2.95), (THU, 0.60)), thw-in(THN, 3.6, 1.85), thw-out(THN, 1.85, 0)),
    ((THU, 2.95, frc([`𝟙`]), -0.32), (THO, 1.85, [`bagify°`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THU - 0.34, 1.75, [`E`]),), names: true)],

  [#vstep(RQ, thpic([`Bag Job`], [`[Job]`], none, (tb-Lb, tb-estQ, tb-alg)),
    [`(μX : `#frc([`β°`])` est(Q)(𝟙+(X×𝟙))[nil,snoc])` \
     #src[Theorem 10.1. No greedy *reduce* exists — one would also
      solve every prefix of the input, and the best schedule of a prefix need not extend to a best
      schedule of the whole]])],
  // `(10.6)`'s arrow is B&dM's `h`, which is @dp-defn's algebra letter; renamed `m` here, since the
  // theorem it feeds and it would otherwise both be `h` in one table.
  [#ty-pan(5.6, (((THU, 4.90), (THU, 3.30)), thw-in(THN, 5.6, 4.10),
      thw-arc(THM, 4.10, 1.60), thw-arc(THN, 4.10, 1.60), thw-out(THN, 1.60, 0)),
    ((THU, 4.90, frc([`𝟙`]), -0.32), (THO, 4.10, [`β°`], 0.32),
     (THU, 3.30, [`est(Q)`], -0.32), (THO, 1.60, [`(𝟙+(X×𝟙))[nil,snoc]`], 0.32)),
    lanes: ((THM, 4.85, [`−×Job`]),))],

  [#vstep(EQ, thpic([`Bag Job`], [`[Job]`], none, (tb-Lsnag, tb-estQ, tb-snoc)),
    [`(μX : (null→nil,`#frc([`snag°`])` est(Q)(X×𝟙)snoc))` \
     #src[Proposition 10.1: `nil` and `snag` have disjoint ranges]])],
  [#ty-pan(5.6, (((THU, 4.90), (THU, 3.30)), thw-in(THN, 5.6, 4.10),
      thw-arc(THM, 4.10, 1.60), thw-arc(THN, 4.10, 1.60), thw-out(THN, 1.60, 0)),
    ((THU, 4.90, frc([`𝟙`]), -0.32), (THO, 4.10, [`snag°`], 0.32),
     (THU, 3.30, [`est(Q)`], -0.32), (THO, 1.60, [`(X×𝟙)snoc`], 0.32)),
    lanes: ((THM, 4.85, [`−×Job`]),))],

  [#vstep(RQ, thpic([`Bag Job`], [`[Job]`], none, (tb-pick, tb-sch)),
    [`schedule=(null→nil,pick (schedule×𝟙) snoc)` \
     #src[`pick⊑`#frc([`snag°`])` est(Q)`, a partial function, quadratic in the number of jobs]])],
  // No `E` lane: `pick` does the transpose and the `est` in one function, so nothing is ever a set.
  [#ty-pan(4.0, (thw-in(THN, 4.0, 2.80), thw-arc(THM, 2.80, 1.20), thw-arc(THN, 2.80, 1.20),
      thw-out(THN, 1.20, 0)),
    ((THO, 2.80, [`pick`], 0.32), (THO, 1.20, [`(schedule×𝟙)snoc`], 0.32)),
    lanes: ((THM, 3.45, [`−×Job`]),))],
))]<tardy-laws>

== The TeX problem

// B&dM §10.4, p. 259.  The book's local `h` for `⦇[arb,step]⦈` is @dp-defn's algebra letter, so it
// is written `H°` here instead.  The base case of `f` is `a<0` on p. 262 and `p≤0` in the program.
#disp[#definition[
`intern≜val round : Decimal⟶[0,2¹⁶)`, #h(4pt) `val≜⦇[zero,shift]⦈`, #h(4pt)
`shift (d,r)=(d+r)/10`, #h(4pt) `round r` rounds `2¹⁶r` to the nearest integer:
`round r=n⟺2n−1<2¹⁷r<2n+1`.

`interval n=((2n−1)/2¹⁷,(2n+1)/2¹⁷)`, #h(4pt) `r inrange (a,b)⟺a<r<b`, #h(4pt)
`round°=interval inrange`, #h(4pt) `R≜length≤length°`.

`Interval` the pairs `(a,b)` with `0<b<1` and `a<b` #h(4pt) #src[(10.9)]; #h(4pt)
`[arb,step] : 1+(Digit×Interval)⟶Interval`, #h(4pt)
`step (d,(a,b))=((d+a)/10,(d+b)/10)`.

`FX=1+(Digit×X)`, #h(4pt) `α≜[nil,cons]`, #h(4pt) `H≜⦇[arb,step]⦈°`, #h(4pt)
`! : Digit×Interval⟶1`, #h(4pt) `Q≜(l°!°r)∪𝟙` #h(4pt)
#src[`l`, `r` are @coprod-laws's injections into `FX=1+(Digit×X)`, so `l : 1⟶F(Interval)` and
 `r : Digit×Interval⟶F(Interval)`], #h(4pt) `w≜2¹⁷`.
]]<tex-defn>

// ONE WIRE, `[0,2¹⁶)` to `Decimal`; the `list` is born only where the algebra builds the digits.
// `interval` sits ABOVE the singleton in every row from the second on: it is the map pulled out of
// the transpose, and holding it at one height is what says the rest of the chain moved past it.
#let xb-est = ([`est(R)`], 1.90, true)
#let xb-Lint = (frc([`intern°`]), 2.75, false)
#let xb-ival = ([`interval`], 2.55, false)
#let xb-Linv = (frc([`inrange val°`]), 4.30, false)
#let xb-LH = (frc([`H`]), 0.95, false)
#let xb-Larb = (frc([`[arb,step]°`]), 3.95, false)
#let xb-estQ = ([`est(Q)`], 1.90, true)
#let xb-FXa = ([`F(X)α`], 1.85, true)
#let tx-pan(h, wires, beads, lanes: (), names: false) = thpan(h, wires, beads,
  ((THO, [`[0,2¹⁶)`]),), ((THN, [`list`]), (THO, [`Digit`])), lanes: lanes, names: names)

#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),
  Thm[#frc([`intern°`])` est(R)⊒extern`, #h(6pt) `extern n=f (2n−1,2n+1)` \
    #src[a shortest decimal whose internal representation is the given multiple of `2⁻¹⁶` is got by
     emitting the one digit the interval of admissible reals allows, until that interval contains
     zero and the empty decimal will do]],
  table.header([*circuit* — one wire, `[0,2¹⁶)` to `Decimal`], [*Hinze–Marsden*]),

  [#vstep([], thpic([`[0,2¹⁶)`], [`Decimal`], none, (xb-Lint, xb-est)),
    [#frc([`intern°`])` est(R)` \ #src[the specification — @tex-defn]])],
  [#tx-pan(3.6, (((THU, 2.95), (THU, 0.60)), thw-out(THN, 1.85, 0)),
    ((THU, 2.95, frc([`𝟙`]), -0.32), (THO, 1.85, [`intern°`], 0.32),
     (THU, 0.60, [`est(R)`], -0.32)),
    lanes: ((THU - 0.34, 1.75, [`E`]),), names: true)],

  [#vstep(EQ, thpic([`[0,2¹⁶)`], [`Decimal`], none, (xb-ival, xb-Linv, xb-est)),
    [`interval `#frc([`inrange val°`])` est(R)` \
     #src[`round°` is not a map, but `interval` is, so it comes out of the transpose]])],
  // `interval` is an arrow between two objects that carry no functor, so it is a bare bead above
  // the unit: the set the transpose opens starts on its target.
  [#tx-pan(4.2, (((THU, 2.85), (THU, 0.60)), thw-out(THN, 1.85, 0)),
    ((THO, 3.55, [`interval`], 0.32), (THU, 2.85, frc([`𝟙`]), -0.32),
     (THO, 1.85, [`inrange val°`], 0.32), (THU, 0.60, [`est(R)`], -0.32)))],

  [#vstep(EQ, thpic([`[0,2¹⁶)`], [`Decimal`], none, (xb-ival, xb-LH, xb-est)),
    [`interval `#frc([`H`])` est(R)`, #h(4pt) `H≜⦇[arb,step]⦈°` \
     #src[fusion: `val inrange°=⦇[arb,step]⦈` — the converse of `val`, cut down to intervals, is a
      reduce on cons-lists]])],
  [#tx-pan(4.2, (((THU, 2.85), (THU, 0.60)), thw-out(THN, 1.85, 0)),
    ((THO, 3.55, [`interval`], 0.32), (THU, 2.85, frc([`𝟙`]), -0.32),
     (THO, 1.85, [`H`], 0.32), (THU, 0.60, [`est(R)`], -0.32)))],

  [#vstep(RQ, thpic([`[0,2¹⁶)`], [`Decimal`], none, (xb-ival, xb-Larb, xb-estQ, xb-FXa)),
    [`interval (μX : `#frc([`[arb,step]°`])` est(Q) F(X)α)` \
     #src[Theorem 10.1: #frc([`[arb,step]°`]) returns at most two elements — stop, or take one more
      digit — and `! nil⊑cons R°` makes it stop whenever stopping is legal]])],
  // `est(Q) : E(F(Interval))⟶F(Interval)` kills the set but not the `F` under it, so its wire ends
  // on the `E` lane; `F(X)α` closes `F` and is where the digits' `list` is born.
  [#tx-pan(6.2, (((THU, 4.60), (THU, 3.10)), thw-arc(THM, 3.90, 1.60), thw-out(THN, 1.60, 0)),
    ((THO, 5.30, [`interval`], 0.32), (THU, 4.60, frc([`𝟙`]), -0.32),
     (THO, 3.90, [`[arb,step]°`], 0.32), (THU, 3.10, [`est(Q)`], -0.32),
     (THO, 1.60, [`F(X)α`], 0.32)),
    lanes: ((THM - 0.34, 2.75, [`F`]),))],

  [#vstep(EQ, [],
    [`extern=interval f`, #h(4pt) `f (a,b)=(a<0→[],[d]⧺f (10a−d,10b−d))` \
     #src[the program, with `d` the digit above]])],
  // No picture: `f` is read on points, and the two sides are values, not the objects the panels
  // carry.
  [],

  [#vstep(EQ, [],
    [`extern n=f (2n−1,2n+1)`, #h(4pt) `f (p,q)=(p≤0→[],[d]⧺f (10p−w d,10q−w d))` \
     #src[`d=(10q) div w`: the same in integer arithmetic only, as chapter 3 required of
      `intern` — every interval reached is `(p/w,q/w)`]])],
  [],
))]<tex-laws>

#pagebreak(weak: true)
#include "allegory-appendix.typ"
