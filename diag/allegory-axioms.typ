// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name (see circuit.typ's header); `dot` is renamed on the way in for that reason.
#import "circuit.typ": conv, meet, wire, bend, gbox, boxrun, boxrun-w, dot as wiredot, tape, tape-fork, tape-join, TINT, delta as wcopy, nabla as wmerge, lw
// draw.typ owns the Hinze–Marsden geometry (Reduce) and every helper this note draws with:
// it is also the standalone PNG of those laws, and one geometry drawn in two files is one that drifts.
#import "draw.typ": snake, homeq, tfuneq, twobeadeq, TCOL, BCOL, CCOL, GIVEN1, GIVEN2, INDUCED, SLACK, ADMIRES, HATES, WORKS, ADMIRERS, HATERS, PEOPLE, LX, BD, LY, lab, ar, node, nodes, ings, edges, arc, head, e, syqnode, syqedge, domstr, pairstr, zw, zsq, zsqc, zstep, znamed, zderiv, zline, zpair, skel, yset, capbox, pair, blocked, choosebox, CHPAD, CHFAN, hm-bead, hm-region, hm-wire
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

  [`°⊣°`], [`(A⟶B)⟶` \ `(B⟶A)`], [`°°=𝟙`], [`R=R°°`], [`R=R°°`], [`(R∪S)°=` \ `R°∪S°`], [`(R∩S)°=` \ `R°∩S°`], [`R°°°=R°`], [`R°°°=R°`],

  [`⟜◁⊣▷⊸`], [`(X⊗A⟶Y)⟶` \ `(X⟶Y⊗A)`], [`𝟙`], [`(⟜◁⊗𝟙)` \ `(𝟙⊗▷⊸)=𝟙`], [`(𝟙⊗⟜◁)` \
    `(▷⊸⊗𝟙)=𝟙`], [`=`], [`=`], [`=`], [`=`],

  // An iso is an adjunction BOTH WAYS, so the bend gets a row in each direction; the pair differs
  // only by swapping columns 4/5, which is what makes the last four columns bare equalities.
  [`▷⊸⊣⟜◁`], [`(X⟶Y⊗A)⟶` \ `(X⊗A⟶Y)`], [`𝟙`], [`(𝟙⊗⟜◁)` \ `(▷⊸⊗𝟙)=𝟙`], [`(⟜◁⊗𝟙)` \
    `(𝟙⊗▷⊸)=𝟙`], [`=`], [`=`], [`=`], [`=`],

  [`Δ⊣∩`], [`(A⟶B)⟶` \ `(A⟶B)²`], [`R↦R∩R=R`], [`R⊑R∩R`], [`R∩S⊑R`], [`Δ(R∪S)=` \ `ΔR∪ΔS`], [`(R∩T)∩(S∩U)=` \ `(R∩S)∩(T∩U)`], [`R∩R=R`], [`R∩R=R`],

  [`∪⊣Δ`], [`(A⟶B)²⟶` \ `(A⟶B)`], [`(R,S)↦` \ `(R∪S,R∪S)`], [`R⊑R∪S`], [`R∪R⊑R`], [`(R∪T)∪(S∪U)=` \ `(R∪S)∪(T∪U)`], [`Δ(R∩S)=` \ `ΔR∩ΔS`], [`R∪R=R`], [`R∪R=R`],

  [`⊥⊣!`], [`{*}⟶` \ `(A⟶B)`], [—], [—], [`⊥⊑R`], [—], [—], [—], [—],

  [`·S⊣/S`], [`(A⟶B)⟶` \ `(A⟶C)`], [`S/S`], [`R⊑(RS)/S`], [`(T/S)S⊑T`], [`(R∪T)S=` \ `RS∪TS`], [`(R∩T)/S=` \ `R/S∩T/S`], [`((RS)/S)S` \ `=RS`], [`((T/S)S)/S` \ `=T/S`],

  [`S·⊣S\`], [`(B⟶C)⟶` \ `(A⟶C)`], [`S\S`], [`R⊑S\(SR)`], [`S(S\T)⊑T`], [`S(R∪T)=` \ `SR∪ST`], [`S\(R∩T)=` \ `S\R∩S\T`], [`S(S\(SR))` \ `=SR`], [`S\(S(S\T))` \ `=S\T`],

  [`R∩⊣R⇒`], [`(A⟶B)⟶` \ `(A⟶B)`], [`X↦R⇒(X∩R)`], [`X⊑R⇒(X∩R)`], [`R∩(R⇒Y)⊑Y`], [`R∩(X∪Y)=` \ `(R∩X)∪(R∩Y)`], [`R⇒(X∩Y)=` \ `(R⇒X)∩(R⇒Y)`], [`R∩(R⇒(X∩R))` \ `=X∩R`], [`R⇒(R∩(R⇒Y))` \ `=R⇒Y`],

  [`𝓓⊣·⊤`], [`(A⟶B)⟶` \ `Cor A`], [`R↦(𝓓R)⊤`], [`R⊑(𝓓R)⊤`], [`𝓓(A⊤)⊑A`], [`𝓓(R∪S)=` \ `𝓓R∪𝓓S`], [`(A∩B)⊤=` \ `A⊤∩B⊤`], [`𝓓((𝓓R)⊤)` \ `=𝓓R`], [`(𝓓(A⊤))⊤` \ `=A⊤`],

  [`𝓡⊣⊤·`], [`(A⟶B)⟶` \ `Cor B`], [`R↦⊤(𝓡R)`], [`R⊑⊤(𝓡R)`], [`𝓡(⊤A)⊑A`], [`𝓡(R∪S)=` \ `𝓡R∪𝓡S`], [`⊤(A∩B)=` \ `⊤A∩⊤B`], [`𝓡(⊤(𝓡R))` \ `=𝓡R`], [`⊤(𝓡(⊤A))` \ `=⊤A`],

  [`·f⊣·f°`], [`(A⟶B)⟶` \ `(A⟶C)`], [`ff°`], [`𝟙⊑ff°`], [`f°f⊑𝟙`], [`(R∪S)f=` \ `Rf∪Sf`], [`(R∩S)f°=` \ `Rf°∩Sf°`], [`ff°f=f`], [`f°ff°=f°`],

  [`f°·⊣f·`], [`(A⟶C)⟶` \ `(B⟶C)`], [`ff°`], [`𝟙⊑ff°`], [`f°f⊑𝟙`], [`f°(X∪Y)=` \ `f°X∪f°Y`], [`f(X∩Y)=` \ `fX∩fY`], [`ff°f=f`], [`f°ff°=f°`],

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
]<adj-cross-why>

// A cross table, not a list: what matters is WHICH PAIRS give a law, and a list of the ones that do
// hides how few they are.  `Δ` is a column and `∪`, `⊥` rows, on ONE side each — the other is all-empty.
#disp[#table(
  columns: 9, align: left + horizon, inset: 3pt, stroke: 0.4pt + luma(190),
  table.header([], [*`·T`*], [*`T·`*], [*`·g`*], [*`g°·`*], [*`T∩`*], [*`°`*], [*`⟜◁`*], [*`Δ`*]),

  [*`·S`*], [`R/(ST)=` \ `(R/T)/S`], [`T\(R/S)=` \ `(T\R)/S`],
    [`R/(Sg)=` \ `(Rg°)/S`], [`g(R/S)=` \ `(gR)/S`],
    [—], [`(Y/S)°=` \ `S°\(Y°)`], [`(RS)^=` \ `R^(S⊗𝟙)`],
    [`(T₁∩T₂)/S=` \ `T₁/S∩T₂/S`],

  [*`S·`*], [`S\(R/T)=` \ `(S\R)/T`], [`(TS)\R=` \ `S\(T\R)`],
    [`S\(Rg°)=` \ `(S\R)g°`], [`(g°S)\R=` \ `S\(gR)`], [—],
    [`(S\Y)°=` \ `Y°/S°`], [`((S⊗𝟙)R)^=` \ `SR^`],
    [`S\(T₁∩T₂)=` \ `S\T₁∩S\T₂`],

  [*`·f`*], [`R/(fT)=` \ `(R/T)f°`], [`T\(Rf°)=` \ `(T\R)f°`],
    [`(fg)°=g°f°`], [—], [—], [`(fY)°=Y°f°`], [—],
    [`(T₁∩T₂)f°=` \ `T₁f°∩T₂f°`],

  [*`f°·`*], [`f(R/T)=` \ `(fR)/T`], [`(Tf°)\R=` \ `f(T\R)`], [—],
    [`(fg)°=g°f°`], [—], [`(fY)°=Y°f°`], [—],
    [`f(T₁∩T₂)=` \ `fT₁∩fT₂`],

  [*`R∩`*], [—], [—], [—], [—], [`(R∩T)⇒Y=` \ `R⇒(T⇒Y)`], [`(R⇒Y)°=` \ `R°⇒(Y°)`], [—],
    [`R⇒(T₁∩T₂)=` \ `(R⇒T₁)∩(R⇒T₂)`],

  [*`°`*], [`(Y/T)°=` \ `T°\(Y°)`], [`(T\Y)°=` \ `Y°/T°`],
    [`(gY)°=Y°g°`],
    [`(gY)°=Y°g°`], [`(T⇒Y)°=` \ `T°⇒(Y°)`], [`Y°°=Y`],
    [`(R^)°=` \ `(R°⊗𝟙)(𝟙⊗▷⊸)` \ #src[both bends: the `°` section's display]],
    [`(T₁∩T₂)°=` \ `T₁°∩T₂°`],

  [*`⟜◁`*], [`(RT)^=` \ `R^(T⊗𝟙)`], [`((T⊗𝟙)R)^=` \ `TR^`], [—], [—], [—],
    [`(R^)°=` \ `(R°⊗𝟙)(𝟙⊗▷⊸)` \ #src[both bends: the `°` section's display]], [—], [—],

  [*`∪`*], [`(X₁∪X₂)T=` \ `X₁T∪X₂T`], [`T(X₁∪X₂)=` \ `TX₁∪TX₂`],
    [`(X₁∪X₂)g=` \ `X₁g∪X₂g`],
    [`g°(X₁∪X₂)=` \ `g°X₁∪g°X₂`],
    [`T∩(X₁∪X₂)=` \ `(T∩X₁)∪(T∩X₂)`], [`(X₁∪X₂)°=` \ `X₁°∪X₂°`], [—], [—],

  [*`⊥`*], [`⊥T=⊥`], [`T⊥=⊥`], [`⊥g=⊥`], [`g°⊥=⊥`],
    [`T∩⊥=⊥`], [`⊥°=⊥`], [—], [—],
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
  (i) `𝟙°=𝟙`  #h(1cm) (ii) `(RS)°=S°R°`  #h(1cm) (iii) `(R⊗S)°=R°⊗S°`
  #h(1cm) (iv) `R≤S` implies `R°≤S°`
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

On every hom-set it is associative, commutative and idempotent, with unit the maximal arrow
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
   `F(R∩S)=FR∩FS`.]], P(p-semidistrib),
)]<meet-semidistrib>

#pagebreak(weak: true)
= Domain and range

#disp[#definition[
The *domain* `Dom(R)≜𝟙∩RR°` and the *range* `Ran R≜Dom(R°)`.
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
  [`Dom(R)⊑A⟺R⊑AR`, for `A` coreflexive],
  [`Dom(RS)⊑Dom(R)`],
  [`Dom(R∩S)=𝟙∩SR°`],
  [`R` entire `⟺Dom(R)=𝟙⟺𝟙⊑RR°`],
  [`R` simple `⟺R°R⊑𝟙`],
  [`R` a map `⟺R` entire and simple],
  [`R,S` entire `⟹RS` entire — likewise simple, likewise maps],
  [`RS` entire `⟹R` entire],
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
   — the discard slides back past `S`]), s: 100%)]<dom-slide>

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

  [`R/(fS)=(R/S)f°` \ #src[Rename `y`: a map leaves a denominator as `f°` outside the box.]],
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
$frac(R, S)$ `≜(R/S)∩(S/R)°`. In `Rel` `x` and `y` has the same image:
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

  [$X ⊑ frac(R, S) ⟺ X S ⊑ R$ and `X°R⊑S`],
  [`X` may pair `x` with `y` only when `x` admires exactly whom `y` hates. Both halves must typecheck,
   so the operation is *partial*.],

  [$(frac(R, S))^circle.small = frac(S, R)$], [Matching is symmetric.],

  [$frac(R, S) frac(S, W) ⊑ frac(R, W)$], [And transitive.],

  [$frac(R, S) S ⊑ R$],
  [$(∃ y. thin x (frac(R, S)) y ∧ y S p) → x R p$ \
   `x only admires whom y hates` \
   $frac(R, S) S = "Dom"(frac(R, S)) R$],

  [$frac(R, R) R = R$],
  [$(∃ y. thin x (frac(R, R)) y ∧ y R p) ⟺ x R p$ \
   `x and y admire the same people` \
   `y=x always qualifies (𝟙⊑R%R below)`],

  [$𝟙 ⊑ frac(R, R)$],
  [$x (frac(R, R)) y$ if `x` and `y` admires the same peoples.],

  [$(frac(R, R))^2 = frac(R, R)$],
  [So the relation *admires the same people* is an equivalence relation.],

  [$X ⊑ frac(R, R) ⟺ X R ⊑ R$, for symmetric `X`],
  [The largest symmetric arrow that leaves `R` alone.],

  [$frac(R, 𝟙)$ is the *simple part* of `R`],
  [The people who admire exactly one person and nobody else. It equals `R` only when `R` is simple, unlike
   `R/𝟙=R`.],

  [`Dom` $frac(R, S)$ `=𝟙∩(R/S)(S/R)`],
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

  [$frac(#[`R`], ∋)$ `∋=R` ], [],

  [`F⊑` $frac(#[`F∋`], ∋)$, `F` simple],
  [A partial choice of sets is inside the total one.],

  [$frac(#[`𝟙`], ∋)$, the *singleton map*, monic],
  [The one-person set.],

  [$frac(#[`∋`], ∋)$ `=𝟙`],
  [Make the set of a set, then read it back one level down.],

  [*fusion:* $frac(#[`fR`], ∋)$ `=f` $frac(#[`R`], ∋)$, `f` a map],
  [Naturality of the unit, `f` $frac(#[`𝟙`], ∋)$ `=` $frac(#[`𝟙`], ∋)$ `(E(f))`.],

  [$frac(#[`f`], ∋)$ `=f` $frac(#[`𝟙`], ∋)$, `f` a map],
  [Rename first or take singletons first — the fusion row above at `R=𝟙`.],

  [$frac(R, S) = frac(R, ∋) (frac(S, ∋))^circle.small$],
  [`x` and `y` match when `R` sends `x` and `S` sends `y` to the same set.],

  [`E(R)≜` $frac(#[`∋R`], ∋)$, `E≜` $frac(#[`∋·`], ∋)$], [`E(R): EA⟶EB`, image of a set of A],
  [$frac(#[`R`], ∋)$ `=` $frac(#[`𝟙`], ∋)$ `E(R)`], [$frac(#[`𝟙`], ∋)$`: x↦{x}` ],
  [$frac(#[`S`], ∋)$ `E(R)=` $frac(#[`S`], ∋)$ $frac(#[`∋R`], ∋)$ `=` $frac(#[`SR`], ∋)$],
  [absorption — the monad's composition law, $frac(#[`S`], ∋)$ `⋄` $frac(#[`R`], ∋)$ `=`
   $frac(#[`SR`], ∋)$, §@sec-kleisli],

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
        [$frac(#[`𝟙`], ∋)$ `∋=𝟙`], [$frac(#[`∋`], ∋)$ `=𝟙`])))
  },
  [$frac(#[`R`], ∋)$ `∋=R` #h(1.4cm)
   #src[`EA` is the powerset of `A`. B&dM write `PA` — standard mathematics, but here `P` is
   already the relator `P(R)`.]],
  // The two snakes are four panels wide, so the pair only clears the 22cm text block scaled down.
  s: 95%,
)]<adj-E-bend>

// The heading gets its own page: §10.1's pair fills the foot of the previous one, and the definition
// below is unbreakable, so the heading was left standing alone there.
#pagebreak(weak: true)
== `𝒜≅Kleisli(E)` <sec-kleisli>

// Every ingredient is a row of @pow-laws; nothing here is new.  `union` is `E(∋)`: the counit with
// `E` applied to it, which is the multiplication the adjunction hands back.
#disp[#block(breakable: false)[#definition[
`E(R)≜` $frac(#[`∋R`], ∋)$, #h(4pt) `{·}=` $frac(#[`𝟙`], ∋)$ ` : A⟶EA`, #h(4pt)
`union=E(∋)=` $frac(#[`∋∋`], ∋)$ ` : E(EA)⟶EA`

`f⋄g≜f E(g) union : A⟶EC`, #h(4pt) for `f : A⟶EB` and `g : B⟶EC`

#src[the monad is on `Map(𝒜)`, not on the allegory: `E` is a relator on all relations, but `{·}`,
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
  of $frac(#[`·`], ∋)$.]]])
]<kleisli-comp>

#block[#src[`𝟙` goes to $frac(#[`𝟙`], ∋)$ `={·}`, the Kleisli identity, by definition — so
$frac(#[`·`], ∋)$ is an isomorphism of categories `𝒜≅Kleisli(E)`, and §@sec-adj-E's `i⊣E` is the
Kleisli adjunction. `i` is the identity on objects, so every object of the allegory is free.]]

= Relator

#disp[#definition[
Every hom-set of an allegory is a poset, so an allegory is a *locally posetal 2-category*: the 2-cell
from `R` to `S` IS `R⊑S`. A *relator* `F : 𝒞⟶𝓓` is a 2-functor between allegories:

  #align(center, block(inset: (y: 6pt))[
    #text(12.5pt)[`F(𝟙)=𝟙` #h(1cm) `F(RS)=F(R)F(S)` #h(1cm) `R⊑S⟹F(R)⊑F(S)`]
  ])

Preserving `°` is *not* asked for — `°` is an identity-on-objects involution `𝒞ᵒᵖ⟶𝒞`, no part of
the 2-category.
]]<relator-defn>

#disp[#table(
  columns: (1fr, 5.2cm),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the statement*], [*B&dM*]),

  [For `f` a map, `F(f)` is a map and `F(f°)=F(f)°`.], [Lemma 5.1],
  [Over a *tabular* allegory a functor is a relator `⟺` it preserves `°`.], [Theorem 5.1],
  [`F(R°)=F(R)°` for every `R`, so `F(R)°` needs no bracket.], [after Theorem 5.1, p. 113],
  [Two relators agreeing on maps are equal.], [Corollary 5.1],
  [`F(X∩Y)=F(X)∩F(Y)` for `X,Y` coreflexive.], [Ex 5.2],
  [`F(R∩S)⊑F(R)∩F(S)`, and strictly.], [Ex 5.2, the restriction],
  [`F(Dom(R))=Dom(F(R))` for `F` preserving `°`.], [—],
)]<relator-laws>

The *power relator* `P` — `xs P(R) ys⟺(∀a∈xs. ∃b∈ys. a R b)∧(∀b∈ys. ∃a∈xs. a R b)` — is where
the fourth is strict: for `R={(a₁,b₁),(a₂,b₂)}` and `S={(a₁,b₂),(a₂,b₁)}` the pair
`({a₁,a₂},{b₁,b₂})` is in `P(R)∩P(S)`, while `R∩S=∅`.

== Fork `⟨R,S⟩`

#disp[#definition[
The *fork* of `R : C⟶A` and `S : C⟶B` is `⟨R,S⟩≜Rπ₁°∩Sπ₂°`, where `(π₁,π₂)` is the
tabulation of `⊤`.
]]<fork-defn>

#disp[#block(inset: (y: 6pt))[
  `⟨R,S⟩π₁=Dom(S)R` #h(1.4cm) `⟨R,S⟩π₂=Dom(R)S`
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
}), pairstr(eq: true)), ("", [`⟜▷=𝟙` on each half]), s: 100%)]<fork-collapse>


=== Relational product `R×S`

#disp[#definition[
`R×S≜⟨π₁R,π₂S⟩`, a relator in each argument but no longer a categorical product.
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
   this row; Ex 5.6 is the `(R×S)(U×V)=(RU)×(SV)` it yields, at `R:=𝟙` and `V:=𝟙`.]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, 0, black)[$E$]
    wcopy((0.5, 0), li: 0.5, lo: 0.55, sp: y)
    brun(1.05, y, (([X], "r"), ([R], "r"))); brun(1.05, -y, (([Y], "r"), ([S], "r")))
    lab(4.25, y, black)[$A$]; lab(4.25, -y, black)[$B$]
  }), s: 74%),

  [`⟨R,S⟩π₁=Dom(S)R` \ #src[@fork-proj]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, 0, black)[$C$]
    wcopy((0.5, 0), li: 0.5, lo: 0.55, sp: y)
    brun(1.05, y, (([R], "r"),))
    brun(1.05, -y, (([S], "r"),)); wiredot((2.65, -y))
    lab(3.0, y, black)[$A$]
  }), s: 74%),

  [`⟨R,S⟩π₂=Dom(R)S` \ #src[@fork-proj]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.72
    lab(-0.35, 0, black)[$C$]
    wcopy((0.5, 0), li: 0.5, lo: 0.55, sp: y)
    brun(1.05, y, (([R], "r"),)); wiredot((2.65, y))
    brun(1.05, -y, (([S], "r"),))
    lab(3.0, -y, black)[$B$]
  }), s: 74%),

  [`⟨X,Y⟩⟨R,S⟩°=(XR°)∩(YS°)`],
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

  [`f⟨R,S⟩=⟨fR,fS⟩` \ #src[`f` a map; it fails for an arbitrary arrow]],
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
    // 1.57 = y + 0.95, the clearance @subseq-union-slide leaves above a branch it labels.
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
  [`l[R,S]=R`, `r[R,S]=S`, and `[R,S]` is the only such arrow], [],

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

  [(5.11)], [`[U,V]°[R,S]=(U°R)∪(V°S)` \ #src[@coprod-laws's last row]],
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
  [`P(R)≜`], [`((∋R)/∋)∩((∋R°)/∋)° : EA⟶EB`],
  [`E(R)≜` $frac(#[`∋R`], ∋)$ `=`], [`((∋R)/∋)∩(∋/(∋R))°`],
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
   Hence `P(R°)=P(R)°`, and `R⊑S⟹P(R)⊑P(S)`.],

  [`P(𝟙)=` $frac(∋, ∋)$ `=𝟙`],
  [The straightness axiom verbatim: extensionality *is* `P`'s unit law.],

  [`P(f)=` $frac(∋ f, ∋)$, for `f` a map],
  [In `Rel`, `xs P(f) ys⟺ys={f a|a∈xs}`. The half at `f°` says every `a∈xs` has its `f a` on
   `ys`; `f` has just the one image per `a`, so that already says `ys` contains everything `xs`
   reaches, which is the fraction's second half. For a map the two definitions coincide.],

  [`P(RS)=P(R)P(S)`],
  [`⊒` is the division cancellation laws. `⊑` is the one law in this section that is not a
   calculation: it needs a tabulation of `P(RS)`.],
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
`⦇α`#sub[`A`]`⦈ : T⟶A` to every F-algebra `α`#sub[`A`].

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
  [`⦇α`#sub[`B`]`⦈S=⦇α`#sub[`C`]`⦈⟸α`#sub[`B`]` S=F(S)α`#sub[`C`] #h(6pt) #src[(2.12)]],
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

  #align(center, block(inset: (y: 6pt))[`T(R)=⦇F(R,𝟙)α⦈ : TA⟶TB`])
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
  [Rebuild the structure with `α`, applying `R` to the parameter on the way.],

  [functor],
  [`T(𝟙)=𝟙` and `T(R)T(S)=T(RS)`],
  [Acting by the identity changes nothing, and two actions in a row are one action.],

  [type functor fusion],
  [`T(R)⦇Q⦈=⦇F(R,𝟙)Q⦈`],
  [A relator action followed by a fold is a single fold — the intermediate structure is never built.
   The side condition holds because `F` is a bifunctor —
   `F(R,𝟙)F(𝟙,⦇Q⦈)=F(R,⦇Q⦈)=F(𝟙,⦇Q⦈)F(R,𝟙)`.],

  [naturality of `α`],
  [`αT(R)=F(R,T(R))α`],
  [Building and then mapping is the same as mapping the parts and then building, so `α` is natural
   from `G(R)=F(R,T(R))` to `T`.],

  [type relator],
  [`T(R)°=T(R°)`],
  [A datatype acts on relations, not only on maps — the map of the converse is the converse of the
   map.],
)]<tf-laws>

// Its own page: the definition and its two squares are read together, and without the break the
// fusion square is the only one of the three on the next page.
#pagebreak(weak: true)
=== Type functor

#disp[#definition[
Let `F` be a bifunctor taking both the parameter `A` and the recursive position `TA`, with an initial
algebra `α`#sub[`A`]` : F(A,TA)⟶TA` for every object `A`. Then `T` is a functor, acting on a map
`f : A⟶B` by

  #align(center, block(inset: (y: 6pt))[`T(f)≜⦇F(f,𝟙)α`#sub[`B`]`⦈ : TA⟶TB`])
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
  [`α`#sub[`A`]` T(f)=F(f,T(f))α`#sub[`B`]],
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
  [`T(f)⦇h⦈=⦇F(f,𝟙)h⦈`],
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
  [`X=⦇α`#sub[`A`]`⦈⟺α`#sub[`T`]` X=F(X)α`#sub[`A`]],
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
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header(
    table.cell(colspan: 3, align: center, text(12.5pt)[`⦇[c,f]⦈=reduce(c,f)`]),
    [*part*], [*`Nat`*], [*`[A]`*],
  ),

  [datatype],
  [`Nat::=zero|succ Nat`],
  [`[A]::=nil|cons (A,[A])`],

  [base functor `F`],
  [`F(X)=1+X`],
  [`F(X)=1+A×X`],

  [initial algebra `α`],
  [`α=[zero,succ]` \ `: 1+Nat⟶Nat`],
  [`α=[nil,cons]` \ `: 1+A×[A]⟶[A]`],

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
  [`α`#sub[`T`]` ⦇`$frac(#[`F(∋)R`], ∋)$`⦈=F(⦇`$frac(#[`F(∋)R`], ∋)$`⦈)` $frac(#[`F(∋)R`], ∋)$],
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
]<cata-map-calc>

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

  [`list(R)≜⦇[nil,(R⊗𝟙) cons]⦈`],
  [`[A]⟶[B]`],
  [The relator's action on `R : A⟶B`: one `R` per element, the shape untouched.],

  [`subseq≜⦇[nil,cons∪π₂]⦈`],
  [`[A]⟶[A]`],
  [`xs subseq ys`: `ys` is `xs` with elements dropped — `cons` keeps the head, `π₂` drops it.],

  [`prefix≜⦇[nil,nil∪cons]⦈` \
   `=cat° π₁=init*`],
  [`[A]⟶[A]`],
  [`ys` is an initial segment of `xs`; the first `nil` is where it stops early. `init≜snoc° π₁`.],

  [`suffix≜cat° π₂=tail*`],
  [`[A]⟶[A]`],
  [The dual, `tail≜cons° π₂`; as a reduce it needs snoc-lists.],

  [`segment≜suffix prefix`],
  [`[A]⟶[A]`],
  [A contiguous stretch of `xs`: a suffix, then a prefix of that.],

  [`partition≜concat°`],
  [`[A]⟶[[A]]`],
  [`cat` restricted to a non-empty first argument, so `ys` is a list of non-empty segments of `xs`.],

  [`concat≜⦇[nil,cat]⦈`],
  [`[[A]]⟶[A]`],
  [Joins the segments back up, which is why its converse splits a list.],

  [`inits`],
  [`[A]⟶[[A]]`],
  [Implements $frac(#[`prefix`], ∋)$, listing the prefixes by increasing length.],

  [`tails`],
  [`[A]⟶[[A]]`],
  [Implements $frac(#[`suffix`], ∋)$ by decreasing length — the opposite order.],

  [`filter(p)≜` $frac(#[`subseq list(p)`], ∋)$ `max(R)`],
  [`[A]⟶[A]`],
  [The longest subsequence of `xs` whose every element passes `p`.
   #h(4pt) #src[Ex 7.41; `max(R)` is @min-defn]],

  [`R≜length≤length°`],
  [`[A]⟶[A]`],
  [The preorder `filter` and `takewhile` maximise over: the longer list wins.],

  [`takewhile(p)≜` $frac(#[`prefix list(p)`], ∋)$ `max(R)`],
  [`[A]⟶[A]`],
  [The same with `prefix` for `subseq`: the longest prefix whose every element passes `p`.
   #h(4pt) #src[Ex 7.39]],

  [`mss≜` $frac(#[`segment sum`], ∋)$ `max(≤)`],
  [`[Int]⟶Int`],
  [Maximum segment sum. `segment=suffix prefix` splits it into $frac(#[`prefix sum`], ∋)$ `max(≤)`
   on each suffix. #h(4pt) #src[Ex 7.40]],
)]<comb-fns>

== $frac(#[`subseq`], ∋)$ `=⦇[nil` $frac(#[`𝟙`], ∋)$`,⟨`$frac(#[`𝟙×∋`], ∋)$` E(cons),π₂⟩ cup]⦈`

// B&dM §5.6, p. 124: @cata-map-calc run at `subseq`'s algebra `[nil, cons ∪ π₂]`, which is what
// turns the relation into a program.  `cup` is needed first — nothing above this note has a binary union.
#disp[#definition[
`cup≜` $frac(#[`π₁∋∪π₂∋`], ∋)$ ` : EA×EA⟶EA`, #h(4pt) so
$frac(#[`R∪S`], ∋)$ `=⟨`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`⟩ cup`.
]]<cup-defn>

#disp[
#zline(
  zsqc([$frac(#[`F(∋) [nil,cons∪π₂]`], ∋)$], none),
  zstep(op: sym.eq, under: true)[`FX=𝟏+A×X`],
  zsqc([$frac(#[`(𝟙+𝟙×∋) [nil,cons∪π₂]`], ∋)$], none),
  zstep(op: sym.eq, under: true)[coproduct],
  zsqc([$frac(#[`[nil,(𝟙×∋)(cons∪π₂)]`], ∋)$], none),
)
#zline(
  zstep(op: sym.eq, under: true)[coproduct of maps],
  zsqc([`[`$frac(#[`nil`], ∋)$`,` $frac(#[`(𝟙×∋)(cons∪π₂)`], ∋)$`]`], none),
  zstep(op: sym.eq, under: true)[singleton],
  zsqc([`[nil` $frac(#[`𝟙`], ∋)$`,` $frac(#[`(𝟙×∋)(cons∪π₂)`], ∋)$`]`], none),
)
]<subseq-EW-case>

// The `coproduct` step above on @coprod-laws' tape, because the `[·,·]` brackets hide what moves: the
// sum is one box per branch, so the second fork meets the first and each branch keeps its own composite.
#disp[#row((
  box(cetz.canvas(length: 0.8cm, {
    let y = 1.15
    wire((0, 0), (0.34, 0))
    // `R + S ≜ [R l, S r]`, so a branch of the sum ENDS by injecting back — that upright `l` is what
    // the second tape's `l°` cancels against.
    tape((0.34, -1.9), (6.33, 1.9))
    tape-fork((0.56, 0), sp: y, len: 0.7)
    gbox((1.26, y), [`l`], flip: true, fill: TINT); wire((2.18, y), (2.52, y))
    gbox((2.52, y), [`𝟙`], chamfer: false, w: 0.7); wire((3.22, y), (3.56, y))
    gbox((3.56, y), [`l`], chamfer: false); wire((4.48, y), (5.33, y))
    gbox((1.26, -y), [`r`], flip: true, fill: TINT); wire((2.18, -y), (2.52, -y))
    gbox((2.52, -y), [`𝟙×∋`], w: 1.55); wire((4.07, -y), (4.41, -y))
    gbox((4.41, -y), [`r`], chamfer: false)
    tape-join((6.03, 0), sp: y, len: 0.7)
    wire((6.33, 0), (7.18, 0))
    tape((7.18, -1.9), (13.41, 1.9))
    tape-fork((7.40, 0), sp: y, len: 0.7)
    gbox((8.10, y), [`l`], flip: true, fill: TINT); wire((9.02, y), (9.36, y))
    gbox((9.36, y), [`nil`], chamfer: false, w: 1.05); wire((10.41, y), (12.41, y))
    gbox((8.10, -y), [`r`], flip: true, fill: TINT); wire((9.02, -y), (9.36, -y))
    gbox((9.36, -y), [`cons∪π₂`], w: 3.05)
    tape-join((13.11, 0), sp: y, len: 0.7)
    wire((13.41, 0), (13.75, 0))
  })),
  [#h(12pt) $=$ #h(12pt)],
  box(cetz.canvas(length: 0.8cm, {
    let y = 1.15
    wire((0, 0), (0.34, 0))
    tape((0.34, -1.9), (8.46, 1.9))
    tape-fork((0.56, 0), sp: y, len: 0.7)
    gbox((1.26, y), [`l`], flip: true, fill: TINT); wire((2.18, y), (2.52, y))
    gbox((2.52, y), [`nil`], chamfer: false, w: 1.05); wire((3.57, y), (7.46, y))
    gbox((1.26, -y), [`r`], flip: true, fill: TINT); wire((2.18, -y), (2.52, -y))
    // Chamfered where the rest of this section is not: `𝟙 × ∋` and `cons ∪ π₂` are relations, not maps.
    gbox((2.52, -y), [`𝟙×∋`], w: 1.55); wire((4.07, -y), (4.41, -y))
    gbox((4.41, -y), [`cons∪π₂`], w: 3.05)
    tape-join((8.16, 0), sp: y, len: 0.7)
    wire((8.46, 0), (8.80, 0))
  })),
), s: 92%)
#align(center, block(inset: (y: 4pt))[#src[B&dM p. 124, "coproduct": `R+S≜[Rl,Sr]` and
  `l[R,S]=R`, `r[R,S]=S` — @coprod-laws.]])]<subseq-sum-branchwise>

#disp[
#zline(
  zsqc([$frac(#[`(𝟙×∋)(cons∪π₂)`], ∋)$], none),
  zstep(op: sym.eq, under: true)[`∪` composes, `π₂` natural],
  zsqc([$frac(#[`(𝟙×∋) cons∪π₂∋`], ∋)$], none),
  zstep(op: sym.eq, under: true)[`cup`],
  zsqc([`⟨`$frac(#[`(𝟙×∋) cons`], ∋)$`,` $frac(#[`π₂∋`], ∋)$`⟩ cup`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[absorption, fusion],
  zsqc([`⟨`$frac(#[`𝟙×∋`], ∋)$` E(cons),π₂⟩ cup`], none),
)
]<subseq-EW-join>

// The first step of the chain above, cut in two so both halves are visible: the tape IS the `∪`
// (@coprod-laws), so distributing is the box entering it, and `∋` crossing `π₂` is the second panel's
// bottom branch redrawn.  No injections on these branches — the union is not over a coproduct here.
// An object is named ONLY where it changes, and every label sits 0.62 ABOVE the wire it names —
// except panel 2's, centred between two branches that carry the same object there.
#disp[#chain((
  cetz.canvas(length: 0.8cm, {
    let y = 1.15
    lab(-1.52, 0, black)[`A×E([A])`]
    wire((0, 0), (0.34, 0))
    gbox((0.34, 0), [`𝟙×∋`], w: 1.55); wire((1.89, 0), (4.00, 0))
    lab(2.95, 0.62, black)[`A×[A]`]
    tape((4.00, -2.10), (7.22, 2.10))
    tape-fork((4.22, 0), sp: y, len: 0.7)
    gbox((4.92, y), [`cons`], chamfer: false, w: 1.3)
    gbox((4.92, -y), [`π₂`], chamfer: false, w: 1.3)
    tape-join((6.92, 0), sp: y, len: 0.7)
    wire((7.22, 0), (7.56, 0))
  }),
  cetz.canvas(length: 0.8cm, {
    let y = 1.15
    lab(-1.2, 0, black)[$=$]
    wire((0, 0), (0.34, 0))
    tape((0.34, -2.10), (5.45, 2.10))
    tape-fork((0.56, 0), sp: y, len: 0.7)
    gbox((1.26, y), [`𝟙×∋`], w: 1.55); wire((2.81, y), (3.15, y))
    gbox((3.15, y), [`cons`], chamfer: false, w: 1.3)
    gbox((1.26, -y), [`𝟙×∋`], w: 1.55); wire((2.81, -y), (3.15, -y))
    gbox((3.15, -y), [`π₂`], chamfer: false, w: 1.3)
    lab(2.98, 0, black)[`A×[A]`]
    tape-join((5.15, 0), sp: y, len: 0.7)
    wire((5.45, 0), (5.79, 0))
  }),
  cetz.canvas(length: 0.8cm, {
    let y = 1.15
    lab(-1.2, 0, black)[$=$]
    wire((0, 0), (0.34, 0))
    tape((0.34, -2.10), (5.45, 2.10))
    tape-fork((0.56, 0), sp: y, len: 0.7)
    gbox((1.26, y), [`𝟙×∋`], w: 1.55); wire((2.81, y), (3.15, y))
    gbox((3.15, y), [`cons`], chamfer: false, w: 1.3)
    gbox((1.26, -y), [`π₂`], chamfer: false, w: 1.3); wire((2.56, -y), (2.90, -y))
    gbox((2.90, -y), [`∋`], w: 0.7); wire((3.60, -y), (4.45, -y))
    lab(2.98, 1.77, black)[`A×[A]`]; lab(2.73, -0.53, black)[`E([A])`]
    tape-join((5.15, 0), sp: y, len: 0.7)
    wire((5.45, 0), (5.79, 0))
    lab(6.42, 0, black)[`[A]`]
  }),
), ("", [composition over `∪`], [`π₂` natural]), s: 88%)
#align(center, block(inset: (y: 4pt))[#src[B&dM p. 124, "composition over join, naturality of `π₂`":
  `T(X₁∪X₂)=TX₁∪TX₂` — @adj-cross; `(𝟙×∋)π₂=π₂∋` — @relprod-pic at `π₂`, an equality
  because `𝟙` is entire.]])]<subseq-union-slide>

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

== Minimum and maximum <sec-min>

// B&dM §7.1, p. 166.  The `°` is what diagram order costs: it reverses the arrow but not the `≤`
// glyph, so without it `min(≤)` would come out the greatest element.
#disp[#definition[
For `R : A⟶A`, #h(4pt) `min(R)≜∋∩(∈\R°) : EA⟶A`, #h(4pt) `max(R)≜min(R°)`.

`xs (min(R)) x⟺x∈xs∧(∀y∈xs. x R y)`

`xs (min(R)) x⟺(x in xs) and all x R\: xs` #h(4pt) #src[in q]

`min(R)=∋∩all R°` #h(4pt) #src[`all R≜∈\R`, q's `all`; the chains below keep it written `∈\`]
]]<min-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X⊑min(R)⟺X⊑∋` and `X°∋⊑R`], [in the set, and below every element of it],
  [$frac(#[`𝟙`], ∋)$ `(∈\R)=R`], [bounding a singleton is bounding its element],
  [$frac(#[`S`], ∋)$ `(∈\R)=S°\R`], [bound `S`'s image without building the set],
  [`union≜` $frac(#[`∋∋`], ∋)$ `: E(EA)⟶EA`], [flattens a set of sets],
  [`union (∈\R)=∈\(∈\R)`], [bound a union by bounding each member set],
  [$frac(#[`𝟙`], ∋)$ `min(R)=𝟙∩R`],
  [a singleton's minimum is its element, where `R` is reflexive \ #src[$frac(#[`S`], ∋)$ `min(R)` at `S:=𝟙`]],
  [$frac(#[`S`], ∋)$ `min(R)=S∩(S°\R°)`], [an `S`-value that points to every `S`-value],
  [$frac(#[`S`], ∋)$ `min(R)=` $frac(#[`S`], ∋)$ `min(R∩S°S)`], [only `R` between values `S` gives one argument counts — context],
  [`E(S) min(R)=(∋S)∩((∋S)°\R°)`],
  [the same for the image of a set \ #src[$frac(#[`S`], ∋)$ `min(R)` at `S:=∋S`]],
  [`P(f) min(R)=min(fRf°) f`], [shunt a function through a minimum],
  [`P(S) min(R)=(∋S)∩(∈\(SR°))` \ #src[`R` reflexive]],
  [fusion with the power relator \ #src[`⊒` is the only proof here that tabulates]],
  [`P(S) min(R)⊑(∋S)∩(∈\(SR°))`], [the half of the row above that costs nothing],
  [`P(min(R)) min(R)⊑union min(R)` \ #src[`R` a preorder]],
  [a minimum in each set, then a minimum of those],
  [`P(min(R)) min(R)=P(Dom(min(R))) union min(R)` \ #src[`R` a preorder]],
  [the same as an equality, once empty sets are dropped],
)]<min-laws>

=== `X⊑min(R)⟺X⊑∋` and `X°∋⊑R`

// The definition read through the two adjunctions it is built from.  B&dM p. 166 cites this as the
// hint "universal property of min"; the chains below cite it the same way.
#disp[
#zline(
  zsqc(`X`, `min(R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zpair(zsqc(`X`, `∋`), zsqc(`X`, `∈\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zpair(zsqc(`X`, `∋`), zsqc(`∈X`, `R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zpair(zsqc(`X`, `∋`), zsqc(`X°∋`, `R`)),
)
]<min-up>

=== $frac(#[`𝟙`], ∋)$ `(∈\R)=R`

// B&dM (7.1): the same four steps as the subsection below, with `{·} ∋ = 𝟙` — the `i ⊣ E` triangle —
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
]<min-71>

=== $frac(#[`S`], ∋)$ `(∈\R)=S°\R`

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
]<min-72>

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
]<min-73>

// Same reason as the hand-placed break further down: `sticky` cannot hold a heading to a BREAKABLE
// figure, and the extra heading level pushed this one to the foot of its page.
#pagebreak(weak: true)
=== $frac(#[`S`], ∋)$ `min(R)=S∩(S°\R°)`

// B&dM (7.5).  (7.4) is this at `S := 𝟙` and (7.7) at `S := ∋ S`, so neither needs a chain of its own.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `min(R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`S`], ∋)$`°X`], `min(R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zpair(zsqc([$frac(#[`S`], ∋)$`°X`], `∋`), zsqc([$frac(#[`S`], ∋)$`°X`], `∈\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zpair(zsqc(`X`, [$frac(#[`S`], ∋)$ `∋`]), zsqc(`X`, [$frac(#[`S`], ∋)$ `(∈\R°)`])),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, @min-72],
  zpair(zsqc(`X`, `S`), zsqc(`X`, `S°\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zsqc(`X`, `S∩(S°\R°)`),
)
]<min-75>

=== $frac(#[`S`], ∋)$ `min(R)=` $frac(#[`S`], ∋)$ `min(R∩S°S)`

// B&dM (7.6): `X ⊑ S` already forces `S° X ⊑ S° S`, so the extra conjunct costs nothing — that is
// the whole content, and it is the middle step.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `min(R∩S°S)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[@min-75, `°`],
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
  zstep(op: sym.arrow.l.r.double, under: true)[@min-75],
  zsqc(`X`, [$frac(#[`S`], ∋)$ `min(R)`]),
)
]<min-76>

=== `P(f) min(R)=min(fRf°) f`

// B&dM (7.8), shunting a map through a minimum.  The one step that is not an adjunction is the
// modular law, and it needs `f` simple — the only such step in §18.
#disp[
#zline(
  zsqc(`P(f) min(R)`, none, name: "f a map"),
  zstep(op: sym.eq, under: true)[`P=E` on maps, @min-75],
  zsqc(`(∋f)∩((∋f)°\R°)`, none),
  zstep(op: sym.eq, under: true)[`°`, `T·⊣T\`, `f°·⊣f·`],
  zsqc(`(∋f)∩(∈\(fR°))`, none),
)
// An operator is stretched to the reason's UNWRAPPED width, so a reason squeezed onto two lines
// overhangs the boxes beside it; the breaks below keep each reason on one line.
#zline(
  zstep(op: sym.eq, under: true)[modular law, `f` simple],
  zsqc(`(∋∩((∈\(fR°))f°))f`, none),
  zstep(op: sym.eq, under: true)[`·f⊣·f°`, `°`, `min`],
  zsqc(`min(fRf°) f`, none),
)
]<min-78>

=== `P(S) min(R)⊑(∋S)∩(∈\(SR°))`

// B&dM (7.10): `∋` is lax natural for the power relator, `P(S) ∋ ⊑ ∋ S`, and with the universal
// property of `min` that is the whole proof.  The equality (7.9) is not this — it needs tabulations.
#disp[
#zline(
  zsqc(`P(S) min(R)`, `(∋S)∩(∈\(SR°))`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(S) min(R)`, `∋S`), zsqc(`∈P(S) min(R)`, `SR°`)),
  zstep(op: sym.arrow.l.double, under: true)[UP of `min`],
  zpair(zsqc(`P(S)∋`, `∋S`), zsqc(`∈P(S)`, `S∈`)),
)
]<min-710>

=== `P(min(R)) min(R)⊑union min(R)`

// B&dM (7.11): (7.5) at `S := ∋ ∋` opens the right-hand side, then the same two facts as (7.10)
// close both strands — the left one twice, the right one against transitivity.
#disp[
#zline(
  zsqc(`P(min(R)) min(R)`, `union min(R)`, name: "R a preorder"),
  zstep(op: sym.arrow.l.r.double, under: true)[@min-75],
  zsqc(`P(min(R)) min(R)`, `(∋∋)∩((∋∋)°\R°)`),
  zstep(op: sym.arrow.l.double, under: true)[`°`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(min(R)) min(R)`, `∋∋`), zsqc(`∈∈P(min(R)) min(R)`, `R°`)),
  zstep(op: sym.arrow.l.double, under: true)[UP of `min`, `R` transitive],
  zpair(zsqc(`P(min(R))∋`, `∋min(R)`), zsqc(`∈P(min(R))`, `min(R)∈`)),
)
]<min-711>

#pagebreak(weak: true)
== Lax natural transformations (LaT)

// B&dM §5.7, p. 133.  Same `⇒` the note gives an ordinary natural transformation: B&dM's own hooked
// arrow marks laxness, but the word already does, and the inequation is right there.
#disp[#definition[
For relators `G,F : 𝒞⟶𝓓` and components `φ`#sub[`A`]` : GA⟶FA`, `φ` is *lax at*
`R : A⟶B` when #h(4pt) `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) — both sides `GA⟶FB`, the
left through the component at `B`, the right through the one at `A`.

`φ : G⇒F` is a *lax natural transformation* (LaT) when it is lax at *every* `R`. #h(4pt) #src[(5.13)]

`∋ : P⇒Id` — that is `P(R)∋⊑∋R`, @powrel-laws's first row at `X:=P(R)`.

Lax at every *map* already gives LaT, and at a map the inequation is an equality #h(4pt)
`G(f)φ=φF(f)`: #h(4pt) laxness is about relations only. #h(4pt) #src[Theorem 5.2]
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
  [`G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)`],
)]<lax-str>

== Monotonic algebras

// B&dM §7.2, p. 172.  The section numbers no equation, so the table names its two theorems instead.
#disp[#definition[
An F-algebra `S : FA⟶A` is *monotonic on* `R : A⟶A` when it is lax at `R` at #h(4pt)
`G:=F`, `F:=Id`, `φ:=S`: #h(4pt) `F(R)S⊑SR`. #h(4pt) `R` is an *endorelation*, so `B=A` and
the two components `φ`#sub[`A`], `φ`#sub[`B`] are the one arrow `S` — an algebra, not a family.

For a map `f : FA⟶A` that is #h(4pt) `f°F(R)f⊑R`, #h(4pt) equivalently #h(4pt) `F(R)⊑fRf°`.

`(≤×≤)+⊑+≤` — addition on `Nat` is monotonic on `≤`, which at the point level
reads #h(4pt) `c=a+b∧a≤a'∧b≤b'⟹c≤a'+b'`.
]]<mon-defn>

// @lax-str at `G := F`, `F := Id`, `φ := S`: the right edge's `Id(R)` is written `R`, and the one `S`
// stands at both `φ` components.  `⊑` points NE — down-then-across is the smaller `F(R)S`.
#disp[#capbox(
  cetz.canvas(length: 0.8cm, {
    let (FT, T, FB, B) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
    ar(FT, T, GIVEN1, s0: 0.75, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.75, s1: 0.55)
    ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55); ar(T, B, GIVEN2, s0: 0.55, s1: 0.55)
    lab(0, 1.8, GIVEN1)[`S`]; lab(0, -1.8, GIVEN1)[`S`]
    lab(-3.75, 0, GIVEN2)[`F(R)`]; lab(3.35, 0, GIVEN2)[`R`]
    lab(0, 0, SLACK, rot: -45deg)[`⊑`]
    node(FT.at(0), FT.at(1), black, `FA`); node(T.at(0), T.at(1), black, `A`)
    node(FB.at(0), FB.at(1), black, `FA`); node(B.at(0), B.at(1), black, `A`)
  }),
  [`F(R)S⊑SR`],
)]<mon-str>

#disp[#definition[
`f : FA⟶A` *distributes over* `R` if #h(4pt) `F(min(R))f⊑` $frac(#[`F(∋)f`], ∋)$ `min(R)`.

`+` distributes over `≤`, at the point level #h(4pt)
`min xs+min ys=min{x+y∣x∈xs∧y∈ys}` #h(4pt) for `xs`, `ys` non-empty and
`min≜min(≤)`.
]]<dist-defn>

// The `f` edges run across, as @mon-str's algebra does, so down-then-across is the smaller
// `F(min(R)) f` and `⊑` points NE.  Right: the same square at `F := (−×−)`, `f := +`, `R := ≤`.
#disp[#align(center, grid(columns: 2, align: horizon, column-gutter: 14pt,
  capbox(
    P(cetz.canvas(length: 0.8cm, {
      let (FEA, EA, FA, A) = ((-3.6, 1.25), (3.6, 1.25), (-3.6, -1.25), (3.6, -1.25))
      ar(FEA, EA, GIVEN1, s0: 1.05, s1: 0.65); ar(FA, A, GIVEN1, s0: 0.65, s1: 0.45)
      ar(FEA, FA, GIVEN2, s0: 0.55, s1: 0.55); ar(EA, A, GIVEN2, s0: 0.55, s1: 0.55)
      lab(0, 2.1, GIVEN1)[$frac(#[`F(∋)f`], ∋)$]; lab(0, -1.8, GIVEN1)[`f`]
      lab(-4.75, 0, GIVEN2)[`F(min(R))`]; lab(4.4, 0, GIVEN2)[`min(R)`]
      lab(0, 0, SLACK, rot: -45deg)[`⊑`]
      node(FEA.at(0), FEA.at(1), black, `F(EA)`); node(EA.at(0), EA.at(1), black, `EA`)
      node(FA.at(0), FA.at(1), black, `FA`); node(A.at(0), A.at(1), black, `A`)
    }), s: 74%),
    [`F(min(R))f⊑` $frac(#[`F(∋)f`], ∋)$ ` min(R)`],
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
      lab(-6.75, 0, GIVEN2)[`min(≤)×min(≤)`]; lab(5.75, 0, GIVEN2)[`min(≤)`]
      lab(0, 0, SLACK, rot: -45deg)[`⊑`]
      vnode(FEA, `E Nat×E Nat`, `(xs,ys)`); vnode(EA, `E Nat`, `{x+y∣x∈xs∧y∈ys}`)
      vnode(FA, `Nat×Nat`, `(min xs,min ys)`); vnode(A, `Nat`, `min xs+min ys`)
    }), s: 74%),
    [`(min(≤)×min(≤))+⊑` $frac(#[`(∋×∋)+`], ∋)$ ` min(≤)`],
  ),
))]<dist-str>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`f°F(R)f⊑R⟺f°F(R°)f⊑R°`],
  [a *map* is monotonic on an order and on its opposite together — a relation is not],
  [`f°F(R)f⊑R⟺F(min(R))f⊑` $frac(#[`F(∋)f`], ∋)$ `min(R)` \ #src[Theorem 7.1, `f` a map]],
  [for a map the two definitions above are one condition],
  [`⦇`$frac(#[`S`], ∋)$ `min(R)⦈⊑` $frac(#[`⦇S⦈`], ∋)$ `min(R)` \ #src[Theorem 7.2, `R` a preorder and `F(R°)S⊑SR°`]],
  [the *greedy theorem*: keeping one minimum at every step beats no more than taking the minimum at
   the end],
)]<mon-laws>

=== `takewhile(p)=⦇[nil,(π₁p→cons,⊸ nil)]⦈` <sec-takewhile>

// B&dM Ex 7.39, p. 174.  The derivation runs on `max(R)` (@min-defn) and the greedy theorem
// (@mon-laws), both above it.
#disp[#definition[
`FX=𝟏+A×X`, #h(4pt) `α≜[nil,cons]`, #h(4pt) `p` a coreflexive on `A`, #h(4pt)
`R≜length≤length°`, a preorder, #h(4pt) `S≜[nil,⊸ nil∪(p×𝟙) cons] : F([A])⟶[A]`.

`⊸ nil` is the constant `nil`, the second `nil` of `prefix=⦇[nil,⊸ nil∪cons]⦈`; #h(4pt)
`(g→X,Y)` is `X` where `g` is defined and `Y` where it is not.

`nil R=⊤` #h(4pt) #src[`nil` is the shortest list, so it loses every `max(R)`]
]]<takewhile-defn>

#disp[
#zline(
  zsqc([`α prefix list(p)`], none),
  zstep(op: sym.eq, under: true)[defining equation],
  zsqc([`F(prefix) [nil,⊸ nil∪cons] list(p)`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[`list(p)` through `cons`],
  zsqc([`F(prefix) [nil,⊸ nil∪(p×list(p)) cons]`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[relator, `prefix` entire],
  zsqc([`[nil,⊸ nil∪(p×(prefix list(p))) cons]`], none),
  zstep(op: sym.eq, under: true)[`prefix list(p)` entire],
  zsqc([`F(prefix list(p))S`], none),
)
#align(center, block(inset: (y: 4pt))[#src[@cata-defining reads that off as `prefix list(p)=⦇S⦈`.
  @cata-fusion cannot: `list(p)` is not entire, `(𝟙×list(p))⊸ nil⊏⊸ nil`, and no algebra meets
  the side condition.]])
]<takewhile-alg>

#disp[
#zline(
  zsqc([`(𝟙×R)(⊸ nil∪(p×𝟙) cons)`], none),
  zstep(op: sym.eq, under: true)[relator, composition over `∪`],
  zsqc([`(𝟙×R)⊸ nil∪(p×R) cons`], none),
  zstep(op: sym.subset.eq.sq, under: true)[@dom-slide, `(𝟙×R) cons⊑cons R`],
  zsqc([`⊸ nil∪(p×𝟙) cons R`], none),
  zstep(op: sym.subset.eq.sq, under: true)[`R` reflexive],
  zsqc([`(⊸ nil∪(p×𝟙) cons)R`], none),
)
#align(center, block(inset: (y: 4pt))[#src[the `cons` branch of `F(R)S⊑SR`; the `nil` branch is
  `nil⊑nil R`. `(𝟙×R) cons⊑cons R` is `cons length=(𝟙×length)π₂ succ` with `succ`
  monotone — a longer tail makes a longer list.]])
]<takewhile-mono>

#disp[
#zline(
  zsqc([$frac(#[`S`], ∋)$ ` max(R)`], none),
  zstep(op: sym.eq, under: true)[coproduct of maps],
  zsqc([`[`$frac(#[`nil`], ∋)$` max(R),` $frac(#[`⊸ nil∪(p×𝟙) cons`], ∋)$` max(R)]`], none),
  zstep(op: sym.eq, under: true)[singleton, `R°` reflexive],
  zsqc([`[nil,` $frac(#[`⊸ nil∪(p×𝟙) cons`], ∋)$` max(R)]`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[`nil R=⊤`],
  zsqc([`[nil,(π₁p→cons,⊸ nil)]`], none),
)
#align(center, block(inset: (y: 4pt))[#src[the set is `{nil}` where `p` fails on the head and
  `{nil,cons(a,xs)}` where it holds, and `nil` loses the second — @min-defn at a two-element set.]])
]<takewhile-step>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`⦇`$frac(#[`S`], ∋)$ `max(R)⦈⊑` $frac(#[`⦇S⦈`], ∋)$ `max(R)` \ #src[Theorem 7.2, @mon-laws at `R°`;
   `max(R)=min(R°)`, so the hypothesis is monotonicity on `(R°)°=R`, which is @takewhile-mono]],
  [greedy: one longest `p`-prefix kept at each `cons`, instead of every `p`-prefix collected and one
   chosen at the end],

  [`prefix° prefix∩R∩R°⊑𝟙` \ #src[context, @min-laws: only `R` between prefixes of one list counts]],
  [two prefixes of one list of equal length are equal, so $frac(#[`prefix list(p)`], ∋)$ `max(R)` is
   simple — *the* longest, not *a* longest],

  [$frac(#[`prefix list(p)`], ∋)$ `max(R)` entire],
  [`nil` is always a `p`-prefix and `R` is connected on the prefixes of one list, so the longest exists],

  [`X⊑Y`, `X` entire, `Y` simple `⟹X=Y` \ #src[`⦇[nil,(π₁p→cons,⊸ nil)]⦈` is a
   reduce of maps, hence entire]],
  [what turns the greedy `⊑` into the heading's `=`],
)]<takewhile-laws>

=== `mss=⦇[zero wrap,⟨(𝟙×head)⊕,π₂⟩ cons]⦈ max(≤)` <sec-mss>

// B&dM Ex 7.40, p. 174–175, whose five staged instructions are the five displays below, mirrored.
// `≤` is on `Int`: over `Nat` every `⊕` would take its right branch and `mss` would be `sum`.
#disp[#definition[
`FX=𝟏+A×X`, #h(4pt) `A:=Int`, #h(4pt) `α≜[nil,cons]`, #h(4pt)
`sum=⦇[zero,plus]⦈` and `segment=suffix prefix` from @cata-examples and @comb-fns.

`head≜cons° π₁`, #h(4pt) `wrap≜⟨𝟙,⊸ nil⟩ cons` #h(4pt) #src[the head of a list and the
one-element list, beside @comb-fns's `tail≜cons° π₂`]

`⊕≜` $frac(#[`⊸ zero∪plus`], ∋)$ ` max(≤)` #h(4pt) #src[B&dM's `oplus=max(Λ(zero∪plus))`; the
set at `(a,b)` is `{0,a+b}`, so `⊕` is the larger of the two]
]]<mss-defn>

#disp[
#zline(
  zsqc([$frac(#[`segment sum`], ∋)$ ` max(≤)`], none),
  zstep(op: sym.eq, under: true)[`segment=suffix prefix`],
  zsqc([$frac(#[`suffix (prefix sum)`], ∋)$ ` max(≤)`], none),
  zstep(op: sym.eq, under: true)[absorption],
  zsqc([$frac(#[`suffix`], ∋)$ ` E(prefix sum) max(≤)`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[$frac(#[`R`], ∋)$` ∋=R`, `union=E(∋)`],
  zsqc([$frac(#[`suffix`], ∋)$ ` E(`$frac(#[`prefix sum`], ∋)$`) union max(≤)`], none),
  zstep(op: sym.eq, under: true)[@min-laws, the sets non-empty],
  zsqc([$frac(#[`suffix`], ∋)$ ` E(`$frac(#[`prefix sum`], ∋)$`)E(max(≤)) max(≤)`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[relator],
  zsqc([$frac(#[`suffix`], ∋)$ ` E(`$frac(#[`prefix sum`], ∋)$` max(≤)) max(≤)`], none),
)
#align(center, block(inset: (y: 4pt))[#src[B&dM's `max(P(max(Λ(sum prefix))))Λsuffix`, mirrored. The
  `union` step is @min-laws's `P(min(R)) min(R)=P(Dom(min(R))) union min(R)` — every suffix has the
  empty prefix, so `Dom` is `𝟙` here — and `P(f)=E(f)` at the map it is applied to (@powrel-laws).]])
]<mss-shape>

#disp[
#zline(
  zsqc([`[nil,⊸ nil∪cons] sum`], none),
  zstep(op: sym.eq, under: true)[coproduct of maps, composition over `∪`],
  zsqc([`[nil sum,⊸ nil sum∪cons sum]`], none),
  zstep(op: sym.eq, under: true)[`sum`'s defining equation],
  zsqc([`[zero,⊸ zero∪(𝟙×sum) plus]`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[`(𝟙×sum)⊸=⊸`, `sum` entire],
  zsqc([`[zero,(𝟙×sum)(⊸ zero∪plus)]`], none),
  zstep(op: sym.eq, under: true)[relator],
  zsqc([`F(sum) [zero,⊸ zero∪plus]`], none),
)
#align(center, block(inset: (y: 4pt))[#src[@cata-fusion at `α`#sub[`B`]` :=[nil,⊸ nil∪cons]`,
  `S:=sum`: the side condition, so `prefix sum=⦇[zero,⊸ zero∪plus]⦈`. `prefix` is the
  reduce, `sum` the map fused into it — the intermediate list is gone.]])
]<mss-prefix-sum>

#disp[
#zline(
  zsqc([`(𝟙×≤°)(⊸ zero∪plus)`], none),
  zstep(op: sym.eq, under: true)[relator, composition over `∪`],
  zsqc([`(𝟙×≤°)⊸ zero∪(𝟙×≤°) plus`], none),
  zstep(op: sym.subset.eq.sq, under: true)[@dom-slide, `(≤°×≤°) plus⊑plus≤°`],
  zsqc([`⊸ zero∪plus≤°`], none),
  zstep(op: sym.subset.eq.sq, under: true)[`≤°` reflexive],
  zsqc([`(⊸ zero∪plus)≤°`], none),
)
#align(center, block(inset: (y: 4pt))[#src[the `plus` branch of `F(≤°)S⊑S≤°`; the `zero` branch is
  `zero⊑zero≤°`. `(≤×≤) plus⊑plus≤` is @mon-defn, written `+` there, and @mon-laws's first row
  carries it to `≤°` — `plus` is a map, so it is monotonic on an order and on its opposite together.]])
]<mss-mono>

#disp[
#zline(
  zsqc([$frac(#[`[zero,⊸ zero∪plus]`], ∋)$ ` max(≤)`], none),
  zstep(op: sym.eq, under: true)[coproduct of maps],
  zsqc([`[`$frac(#[`zero`], ∋)$` max(≤),` $frac(#[`⊸ zero∪plus`], ∋)$` max(≤)]`], none),
  zstep(op: sym.eq, under: true)[singleton, `≤°` reflexive],
  zsqc([`[zero,⊕]`], none),
)
#align(center, block(inset: (y: 4pt))[#src[with @mss-mono the greedy theorem gives
  `⦇[zero,⊕]⦈⊑` $frac(#[`prefix sum`], ∋)$ ` max(≤)` — B&dM's own containment — and @mss-laws's
  second row makes it an equality.]])
]<mss-step>

#disp[
#zline(
  zsqc([`[nil wrap,⟨(𝟙×head) cons,π₂⟩ cons] list(g)`], none),
  zstep(op: sym.eq, under: true)[coproduct of maps, `wrap` and `cons` natural],
  zsqc([`[nil g wrap,⟨(𝟙×head) cons g,π₂ list(g)⟩ cons]`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[`g`'s defining equation, `list(g) head=head g`],
  zsqc([`[c wrap,⟨(𝟙×(list(g) head))f,(𝟙×list(g))π₂⟩ cons]`], none),
  zstep(op: sym.eq, under: true)[fork, relator],
  zsqc([`F(list(g))[c wrap,⟨(𝟙×head)f,π₂⟩ cons]`], none),
)
#align(center, block(inset: (y: 4pt))[#src[`g≜⦇[c,f]⦈` and
  `tails=⦇[nil wrap,⟨(𝟙×head) cons,π₂⟩ cons]⦈`, since `tails(cons(a,xs))` is
  `cons(cons(a,head(tails xs)),tails xs)`. @cata-fusion then reads off
  `tails list(g)=⦇[c wrap,⟨(𝟙×head)f,π₂⟩ cons]⦈`, at `c,f:=zero,⊕` the heading's fold.]])
]<mss-scan>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`⦇`$frac(#[`S`], ∋)$ `max(≤)⦈⊑` $frac(#[`⦇S⦈`], ∋)$ `max(≤)` \ #src[@mon-laws at `≤°`,
   `S:=[zero,⊸ zero∪plus]`, condition @mss-mono]],
  [greedy: one running maximum kept at each `cons`, instead of every prefix sum collected and one
   chosen at the end],

  [`X⊑Y`, `X` entire, `Y` simple `⟹X=Y` \ #src[@takewhile-laws's last row at this `S`]],
  [`⦇[zero,⊕]⦈` is a reduce of maps, and the prefix sums of one list are finitely many
   integers with one greatest, so @mss-step's `⊑` is an equality],

  [`list(g) head=head g` \ #src[the one step of @mss-scan the note has no law for]],
  [`head` is a partial map, undefined at `nil`; the equality holds because `tails` never returns an
   empty list, which is a fact about `tails`, not a naturality square],

  [`tails` implements $frac(#[`suffix`], ∋)$, `list(f)` implements `E(f)` \ #src[@comb-fns]],
  [what makes @mss-shape a program: one fold builds the `n+1` running maxima, and the final `max(≤)`
   reads them in one more pass, so `mss` is linear],
)]<mss-laws>

=== `filter(p)=⦇[nil,(π₁p→cons,π₂)]⦈` <sec-filter>

// B&dM Ex 7.41, p. 174.  @sec-takewhile with `subseq` for `prefix`: same `F`, `α`, `p`, `R`, same
// greedy theorem, and only the second branch of the algebra differs.
#disp[#definition[
`F`, #h(4pt) `α`, #h(4pt) `p`, #h(4pt) `R` as in @takewhile-defn; #h(4pt)
`S≜[nil,π₂∪(p×𝟙) cons] : F([A])⟶[A]`, #h(4pt) `π₂` where @takewhile-defn has `⊸ nil`.

`𝟙⊑π₂R cons°` #h(4pt) #src[the tail is one shorter than the cons, so `π₂` loses the `max(R)` at
every step — where @takewhile-defn's loser is `nil`]
]]<filter-defn>

#disp[
#zline(
  zsqc([`α subseq list(p)`], none),
  zstep(op: sym.eq, under: true)[defining equation],
  zsqc([`F(subseq) [nil,cons∪π₂] list(p)`], none),
  zstep(op: sym.eq, under: true)[`list(p)` through `cons`, `π₂` natural],
  zsqc([`F(subseq) [nil,(p×list(p)) cons∪(𝟙×list(p))π₂]`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[relator, `subseq list(p)` entire],
  zsqc([`F(subseq list(p))S`], none),
)
#align(center, block(inset: (y: 4pt))[#src[@cata-defining reads that off as `subseq list(p)=⦇S⦈` —
  @takewhile-alg's chain with `π₂` for `⊸ nil`. Here @cata-fusion is blocked for the same reason,
  and `π₂` is the branch that carries `list(p)` out by naturality (@subseq-outr-square at `∋:=list(p)`).]])
]<filter-alg>

#disp[
#zline(
  zsqc([`(𝟙×R)(π₂∪(p×𝟙) cons)`], none),
  zstep(op: sym.eq, under: true)[composition over `∪`, `π₂` natural],
  zsqc([`π₂R∪(p×R) cons`], none),
  zstep(op: sym.subset.eq.sq, under: true)[@takewhile-mono's `cons` branch],
  zsqc([`π₂R∪(p×𝟙) cons R`], none),
  zstep(op: sym.eq, under: true)[composition over `∪`],
  zsqc([`(π₂∪(p×𝟙) cons)R`], none),
)
#align(center, block(inset: (y: 4pt))[#src[`F(R)S⊑SR`, the `nil` branch again `nil⊑nil R`. The
  first step is an equality: @takewhile-mono spends `R` reflexive on getting `⊸ nil` past `𝟙×R`,
  and `π₂` needs only its naturality square.]])
]<filter-mono>

#disp[
#zline(
  zsqc([$frac(#[`S`], ∋)$ ` max(R)`], none),
  zstep(op: sym.eq, under: true)[@takewhile-step's first two steps],
  zsqc([`[nil,` $frac(#[`π₂∪(p×𝟙) cons`], ∋)$` max(R)]`], none),
  zstep(op: sym.eq, under: true)[`𝟙⊑π₂R cons°`],
  zsqc([`[nil,(π₁p→cons,π₂)]`], none),
)
#align(center, block(inset: (y: 4pt))[#src[at `(a,xs)` the set is `{xs}` where `p` fails on `a` and
  `{xs,cons(a,xs)}` where it holds, and `xs` loses the second — @min-defn at a two-element set. The
  head is dropped, not the whole tail: that is the one place `π₂` shows against @takewhile-step's `⊸ nil`.]])
]<filter-step>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`⦇`$frac(#[`S`], ∋)$ `max(R)⦈⊑` $frac(#[`⦇S⦈`], ∋)$ `max(R)` \ #src[@takewhile-laws's first row at
   this `S`, its condition @filter-mono]],
  [greedy: one longest `p`-subsequence kept at each `cons`],

  [`S°S∩R∩R°⊑𝟙` fails at `S:=subseq list(p)` \ #src[@takewhile-laws's uniqueness row does not
   transfer]],
  [two `p`-subsequences of one list can have equal length and differ: the prefixes of one list are
   linearly ordered by length, its subsequences are not],

  [$frac(#[`subseq list(p)`], ∋)$ `max(R)` simple \ #src[@comb-fns]],
  [a `p`-subsequence that drops a passing element is beaten by the one that keeps it, so only the
   subsequence keeping *exactly* the passing elements survives `max(R)` — *the* longest, not *a* longest],

  [`X⊑Y`, `X` entire, `Y` simple `⟹X=Y` \ #src[@takewhile-laws's last row at this `S`]],
  [what turns the greedy `⊑` into the heading's `=`; `⦇[nil,(π₁p→cons,π₂)]⦈` is again a
   reduce of maps, hence entire],
)]<filter-laws>

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

  [`tree A::=node (A,[tree A])`],
  [`𝒜⟶𝒜`],
  [The company hierarchy: an employee, and the list of subtrees under them.],

  [`F(A,B)=A×[B]`],
  [`𝒜×𝒜⟶𝒜`],
  [The base functor `tree` folds: an employee beside the recursive position, one layer deep.],

  [`rating`],
  [`A⟶Real`],
  [What one employee is worth as a guest.],

  [`cost≜list(rating) sum`],
  [`[A]⟶Real`],
  [What a guest list is worth.],

  [`R≜cost≤cost°`],
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

  [`party≜⦇S⦈ choose`],
  [`tree A⟶[A]`],
  [Every guest list the president's ruling allows.],

  [the specification \ $frac(#[`party`], ∋)$ `max(R)`],
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
  `max(R)` keeps `([b]=7,[d,e]=6)` at `b`, where `include` wins, and `([c]=2,[f]=8)` at `c`, where
  `exclude` wins, so at the root `include=[a,d,e,f]=17` beats `exclude=[b,f]=15`, and `choose`
  takes 17.]]])
]<party-example>

// `list(π₂)` is ONE box, not the `⊸ ⊗ 𝟙` inside the relator: the picture is here for the shape of
// `include`, and opening `π₂` up costs a discard stub per list element that says nothing about it.
// Both pictures share every stage's x: the boxes are right-aligned at 9.2, so the two read one under
// the other and a wire's type is found at the same place in each.
#disp[#P(cetz.canvas(length: 0.8cm, {
  let y = 0.8
  lab(-2.0, 0, black)[`include`$=$]
  wire((0, y), (19.9, y))                    // the root, straight through: the `𝟙` of `𝟙 × (…)`
  wire((0, -y), (6.6, -y))
  gbox((6.6, -y), [`list(π₂)`], w: 2.6, h: 0.75, chamfer: false)
  wire((9.2, -y), (13.8, -y))
  gbox((13.8, -y), [`concat`], w: 1.9, h: 0.75, chamfer: false)
  wire((15.7, -y), (18.9, -y))
  gbox((18.9, 0), [`cons`], w: 1.4, h: 2 * y + 0.35, chamfer: false)
  wire((20.3, 0), (23.5, 0))
  lab(1.25, y + 0.42, black)[`a:A`]
  lab(1.25, -y + 0.5, black)[`[[A]×[A]]`]
  lab(3.7, -y + 0.5, black)[`b`]; lab(4.9, -y + 0.5, black)[`c`]
  lab(3.7, -y - 0.5, black)[`de`]; lab(4.9, -y - 0.5, black)[`f`]
  lab(10.2, -y + 0.5, black)[`[[A]]`]
  lab(11.7, -y - 0.5, black)[`de`]; lab(12.9, -y - 0.5, black)[`f`]
  lab(16.5, -y + 0.5, black)[`[A]`]
  lab(17.8, -y - 0.5, black)[`def`]
  lab(21.9, 0.45, black)[`adef:[A]`]
}), s: 80%)]<include-pic>

// The trailing `π₂` is `⊸ ⊗ 𝟙`, and here the discard IS the step, so it is drawn and not boxed.
// `list(choose)` keeps the chamfer: `choose` is a relation, where `include`'s `π₂` is a map.
#disp[#P(cetz.canvas(length: 0.8cm, {
  let y = 0.8
  lab(-2.0, 0, black)[`exclude`$=$]
  wire((0, y), (18.9, y))                    // the root, thrown away by the `⊸` of `π₂`
  wiredot((18.9, y))
  wire((0, -y), (5.9, -y))
  gbox((5.9, -y), [`list(choose)`], w: 3.3, h: 0.75)
  wire((9.2, -y), (13.8, -y))
  gbox((13.8, -y), [`concat`], w: 1.9, h: 0.75, chamfer: false)
  wire((15.7, -y), (23.5, -y))
  lab(1.25, y + 0.42, black)[`a:A`]
  lab(1.25, -y + 0.5, black)[`[[A]×[A]]`]
  lab(3.7, -y + 0.5, black)[`b`]; lab(4.9, -y + 0.5, black)[`c`]
  lab(3.7, -y - 0.5, black)[`de`]; lab(4.9, -y - 0.5, black)[`f`]
  lab(10.2, -y + 0.5, black)[`[[A]]`]
  lab(11.7, -y + 0.5, black)[`b`]; lab(12.9, -y - 0.5, black)[`f`]
  lab(16.5, -y + 0.5, black)[`[A]`]
  lab(17.8, -y - 0.5, black)[`bf`]
}), s: 80%)]<exclude-pic>

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

=== `list(R×R)` <sec-party-listrr>

// The two lists are stacked so the correspondence is read DOWN a column: `list` relates lists of the
// same length position by position, so everything `list(R×R)` says is what `R×R` says of one item.
#disp[#align(center, grid(
  columns: 6, column-gutter: 10pt, row-gutter: 5pt,
  align: (center + horizon, center + horizon, center + horizon, center + horizon, center + horizon,
          left + horizon),
  [`[`], [`([b],[d])`], [`,`], [`([c],[])`], [`]`], [],
  [], [`│`], [], [`│`], [], [],
  [], [`▼`], [], [`▼`], [], src[`list(R×R)`, elementwise],
  [`[`], [`([b],[d,e])`], [`,`], [`([c],[f])`], [`]`], [],
))
// One raw block, not a grid: the ticks land under `b` and `d` because every glyph is one monospace
// advance wide, which no measured column can promise.
#v(8pt)
#align(center)[```
([b],[d])
  │   └── exclude: the best party in b's subtree when b does not come
  └────── include: the best party in b's subtree when b comes
```]]<party-listrr>

// `R×R` is TWO demands, one per component, and at `a` both elements move, each in its second — the
// table is here because "the relator relates them elementwise" hides which component that is.
#disp[
#table(
  columns: (3.6cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*element*], [*1st component* \ `include`], [*2nd component* \ `exclude`]),

  [1st, `([b],[d])`],
  [`[b] R [b]` \ #src[`7≤7`, reflexivity]],
  [`[d] R [d,e]` \ #src[`5≤6`, and `([b],[d,e])` is the pair `max(R)` keeps at `b`]],

  [2nd, `([c],[])`],
  [`[c] R [c]` \ #src[`2≤2`, reflexivity]],
  [`[] R [f]` \ #src[`0≤8`, and `([c],[f])` is the pair `max(R)` keeps at `c`]],
)
#align(center, src[the first component of `𝟙×list(R×R)` is the root employee.])
]<party-rr>

// Each note in its own block: the template indents the second of two consecutive paragraphs, and an
// indented note reads as a continuation of the one above it.
#block[#src[`R≜cost≤cost°` is a preorder, so the components that do not move are related by
  reflexivity — `R×R` demands a relation in *both* components, it cannot skip one.]]

#block[#src[`R` compares cost only, not contents: `[] R [f]` is legal though `[f]` has an element
  `[]` does not. That is why the three leaves of §@sec-party-mono's proof all reduce to
  "`cost` is a sum".]]

=== `(𝟙×list(R×R))S⊑S(R×R)` — `S : F([A]×[A])⟶[A]×[A]` monotonic on `R×R` <sec-party-mono>

// @mon-str at `F := (− × [−])`, `A := [A]×[A]`, `R := R×R`, so `F(R×R) = 𝟙×list(R×R)`; @lax-defn at
// `G := F`, `F := Id`, `φ := S` for the panels, `rev` putting the smaller side left, where `⊑` points.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FT, T, FB, B) = ((-4.2, 1.25), (4.2, 1.25), (-4.2, -1.25), (4.2, -1.25))
    ar(FT, T, GIVEN1, s0: 1.9, s1: 1.5); ar(FB, B, GIVEN1, s0: 1.9, s1: 1.5)
    ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55); ar(T, B, GIVEN2, s0: 0.55, s1: 0.55)
    lab(0, 1.8, GIVEN1)[`S`]; lab(0, -1.8, GIVEN1)[`S`]
    lab(-6.0, 0, GIVEN2)[`𝟙×list(R×R)`]; lab(4.9, 0, GIVEN2)[`R×R`]
    lab(0, 0, SLACK, rot: -45deg)[`⊑`]
    node(FT.at(0), FT.at(1), black, `F([A]×[A])`); node(T.at(0), T.at(1), black, `[A]×[A]`)
    node(FB.at(0), FB.at(1), black, `F([A]×[A])`); node(B.at(0), B.at(1), black, `[A]×[A]`)
  }),
  // `length` up from the file's 0.95cm: the port labels do not scale with it, and at 0.95cm the two
  // top ports touch — `F` `[A]×[A]`, which the reader reads across, comes out as `F[A]`.
  homeq(`F`, `[A]×[A]`, `S`, `R×R`, `S`, `[A]×[A]`, ctop: GIVEN1, cmid: GIVEN2, cbot: GIVEN1,
    regions: auto, sep: text(SLACK)[`⊑`], rev: true, gap: 1.4, length: 1.35cm),
  [`(𝟙×list(R×R))S⊑S(R×R)`],
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
  [$frac(#[`⦇S⦈ choose`], ∋)$ `=` $frac(#[`⦇S⦈`], ∋)$ `E(choose)` #h(1cm) #src[@pow-laws, absorption]],
)]<party-absorb>

// B&dM p. 177 in diagram order; the `exclude` half is their Ex 7.43.  `boxrun` and its width are
// `circuit.typ`'s, beside `chain`: a run of boxes is not this proof's idea.
// `(label, width, chamfer)`, set once: the same box is drawn in up to five rows, and a width typed
// per row is a width that drifts.  No chamfer is a map — `list(π₂)` is one, `list(choose)` is not.
#let box-r = ([`R`], 0.92, true)
#let box-lrr = ([`list(R×R)`], 2.7, true)
#let box-lr = ([`list(R)`], 2.2, true)
#let box-cc = ([`concat`], 1.9, false)
#let box-lp = ([`list(π₂)`], 2.4, false)
#let box-lrrp = ([`list((R×R)π₂)`], 3.7, true)
#let box-lpr = ([`list(π₂R)`], 2.7, true)
#let box-lch = ([`list(choose)`], 3.3, true)
#let box-lrrc = ([`list((R×R)choose)`], 4.7, true)
#let box-lchr = ([`list(choose R)`], 3.8, true)

// A PRODUCT IS TWO WIRES.  `F([A]×[A])=A×[[A]×[A]]` enters as two, `[A]×[A]` leaves as two, and
// `𝟙×list(R×R)` is the root's wire running straight past a box that sits on the other one — `×` costs no
// notation, it IS the second wire.  `[[A]×[A]]` stays ONE wire: its outermost former is the list.
// All four shapes below open with `pairin`, at two strand heights, so the height is its parameter.
#let SIY = 0.5          // the two input strands, where the pair is forked ...
#let STA = 1.5          // ... a branch's root strand ...
#let STB = 0.55         // ... and its subtree-list strand
#let pairin(y, items) = {
  lab(-0.55, y, black)[`A`]; lab(-1.6, -y, black)[`[[A]×[A]]`]
  wire((0, y), (boxrun-w(items), y))
  boxrun(0, -y, items)
}
#let sbox(pre, post) = {
  pairin(SIY, pre)
  let (w, ow) = (boxrun-w(pre), boxrun-w(post))
  gbox((w, 0), [`S`], w: 1.2, h: 2 * SIY + 0.6)
  boxrun(w + 1.2, SIY, post); boxrun(w + 1.2, -SIY, post)
  lab(w + 1.65 + ow, SIY, black)[`[A]`]; lab(w + 1.65 + ow, -SIY, black)[`[A]`]
}
// Forking a PAIR costs a shuffle: each of the two strands is copied, and the root's two copies
// straddle the list's, so the two middle strands cross on their way to the branch they belong to.
// ONE loop for the two branches: they differ by their strand heights and by which box spans them.
#let sfork(pre, inner, post) = {
  pairin(SIY, pre)
  let w = boxrun-w(pre)
  wiredot((w, SIY)); bend((w, SIY), (w + 0.9, STA)); bend((w, SIY), (w + 0.9, -STB))
  wiredot((w, -SIY)); bend((w, -SIY), (w + 0.9, STB)); bend((w, -SIY), (w + 0.9, -STA))
  let (x, iw) = (w + 0.9, boxrun-w(inner))
  for (yh, yl, head, hc) in ((STA, STB, [`include`], false), (-STB, -STA, [`exclude`], true)) {
    wire((x, yh), (x + iw, yh)); boxrun(x, yl, inner)
    gbox((x + iw, (yh + yl) / 2), head, w: 2.2, h: yh - yl + 0.5, chamfer: hc)
    boxrun(x + iw + 2.2, (yh + yl) / 2, post)
  }
  let ex = x + iw + 2.65 + boxrun-w(post)
  lab(ex, (STA + STB) / 2, black)[`[A]`]; lab(ex, -(STA + STB) / 2, black)[`[A]`]
}
// `include`'s shape: the root straight through the upper wire, the subtrees' pairs down the lower
// one, both entering the box that spans them — `cons` once `include` is unfolded.
#let tallpic(items, head, hw, hc: false, post: ()) = {
  let (y, w) = (0.8, boxrun-w(items))
  pairin(y, items)
  gbox((w, 0), head, w: hw, h: 2 * y + 0.4, chamfer: hc)
  boxrun(w + hw, 0, post)
  lab(w + hw + boxrun-w(post) + 0.45, 0, black)[`[A]`]
}
// `exclude`'s shape: the trailing `π₂` throws the root away, so the upper wire ends in a discard.
#let droppic(items, post: ()) = {
  let (y, w) = (0.8, boxrun-w(items))
  pairin(y, items)
  wiredot((w, y))
  boxrun(w, -y, post)
  lab(w + boxrun-w(post) + 0.45, -y, black)[`[A]`]
}

// Every row's picture is drawn at ONE length and ONE scale: 24 cells, and a scale typed per cell is
// a scale that drifts — both times this one changed, it had to change in all 24.
#let party-pic(body) = P(cetz.canvas(length: 0.8cm, body), s: 62%)

// The step's relation at the LEFT EDGE of the formula, so the column of symbols reads straight down
// the table: `⊑` is where the proof loses information and takes `SLACK`, `=` stays grey and quiet.
#let SQ = text(SLACK)[$subset.eq.sq$]
#let EQ = text(luma(140))[$=$]
#let step(op, body) = grid(columns: (0.72cm, 1fr), align: (left + horizon, left + horizon), op, body)

#disp[#table(
  columns: (8.8cm, 5.4cm, 1fr),
  align: (left + horizon, left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*formula*], [*reason*],
    [*picture* — a product is two wires: the root above, the subtrees' pairs below]),

  [#step([])[`(𝟙×list(R×R))S`]], [],
  party-pic(sbox((box-lrr,), ())),

  [#step(EQ)[`(𝟙×list(R×R))⟨include,exclude⟩`]], [`S≜⟨include,exclude⟩`],
  party-pic(sfork((box-lrr,), (), ())),

  [#step(SQ)[`⟨(𝟙×list(R×R))include,` \ #h(1em)`(𝟙×list(R×R))exclude⟩`]],
  [@fork-proj, @meet-semidistrib \ #src[`⊑`, not `=`: 7 of @bdm-prod-laws asks for a map and
   `𝟙×list(R×R)` is not one. B&dM write the step `=`.]],
  party-pic(sfork((), (box-lrr,), ())),

  [#step(SQ)[`⟨include R,exclude R⟩`]],
  [@party-mono-include, @party-mono-exclude \ #src[@fork-proj: a fork is monotonic in both
   components]],
  party-pic(sfork((), (), (box-r,))),

  [#step(EQ)[`⟨include,exclude⟩(R×R)`]], [2 of @bdm-prod-laws, `⟨X,Y⟩(R×S)=⟨XR,YS⟩`],
  party-pic(sfork((), (), (box-r,))),

  [#step(EQ)[`S(R×R)`]], [`S≜⟨include,exclude⟩`],
  party-pic(sbox((), (box-r,))),
)]<party-mono-proof>

// The rows either side of a `(R×S)(U×V)=(RU)×(SV)` step are the SAME STROKES — `×` is `⊗`, and the
// step is spent by the notation — so the picture repeats; the repeat IS the reason cell's content.
#disp[#table(
  columns: (9.0cm, 5.4cm, 1fr),
  align: (left + horizon, left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*formula*], [*reason*], [*picture* — the root above, the subtrees' pairs below]),

  [#step([])[`(𝟙×list(R×R))include`]], [],
  party-pic(tallpic((box-lrr,), [`include`], 2.2)),

  [#step(EQ)[`(𝟙×(list(R×R) list(π₂) concat)) cons`]],
  [`include≜(𝟙×(list(π₂) concat)) cons`, then 2 of @bdm-prod-laws \ #src[`(R×S)(U×V)=(RU)×(SV)`,
   Ex 5.6]],
  party-pic(tallpic((box-lrr, box-lp, box-cc), [`cons`], 1.4)),

  [#step(EQ)[`(𝟙×(list((R×R)π₂) concat)) cons`]], [@relator-defn, `F(RS)=F(R)F(S)`],
  party-pic(tallpic((box-lrrp, box-cc), [`cons`], 1.4)),

  [#step(SQ)[`(𝟙×(list(π₂R) concat)) cons`]],
  [`(R×R)π₂=(Dom(π₁R))π₂R` `⊑π₂R` \ #src[1 and 4 of @bdm-prod-laws, then `Dom⊑𝟙`; `list` monotonic,
   @relator-defn]],
  party-pic(tallpic((box-lpr, box-cc), [`cons`], 1.4)),

  [#step(EQ)[`(𝟙×(list(π₂) list(R) concat)) cons`]], [@relator-defn, `F(RS)=F(R)F(S)`],
  party-pic(tallpic((box-lp, box-lr, box-cc), [`cons`], 1.4)),

  [#step(SQ)[`(𝟙×(list(π₂) concat R)) cons`]],
  [`list(R)concat⊑concat R` \ #src[a LEAF: no law above it. `cost` is a sum, so
   `cost(concat xss)=sum(list(cost)xss)` and a costlier part makes a costlier whole. B&dM's exercise.]],
  party-pic(tallpic((box-lp, box-cc, box-r), [`cons`], 1.4)),

  [#step(EQ)[`(𝟙×(list(π₂) concat))(𝟙×R) cons`]], [2 of @bdm-prod-laws, `(R×S)(U×V)=(RU)×(SV)`],
  party-pic(tallpic((box-lp, box-cc, box-r), [`cons`], 1.4)),

  [#step(SQ)[`(𝟙×(list(π₂) concat)) cons R`]],
  [`(𝟙×R)cons⊑cons R` \ #src[a LEAF: `cost(cons(a,xs))` `=rating(a)+cost(xs)`, so a costlier tail
   makes a costlier list. B&dM's exercise.]],
  party-pic(tallpic((box-lp, box-cc), [`cons`], 1.4, post: (box-r,))),

  [#step(EQ)[`include R`]], [`include≜(𝟙×(list(π₂) concat)) cons`],
  party-pic(tallpic((), [`include`], 2.2, post: (box-r,))),
)]<party-mono-include>

// The same eight steps with `choose` where `include` has `π₂`, and one difference: the step that was
// `Dom⊑𝟙` there is §@sec-party-choose here, and the closing `π₂` is an EQUALITY — `π₁` is entire.
#disp[#table(
  columns: (9.0cm, 5.4cm, 1fr),
  align: (left + horizon, left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*formula*], [*reason*], [*picture* — the root above, the subtrees' pairs below]),

  [#step([])[`(𝟙×list(R×R))exclude`]], [],
  party-pic(tallpic((box-lrr,), [`exclude`], 2.2, hc: true)),

  [#step(EQ)[`(𝟙×(list(R×R) list(choose) concat))π₂`]],
  [`exclude≜(𝟙×(list(choose) concat))π₂`, then 2 of @bdm-prod-laws \ #src[`(R×S)(U×V)=(RU)×(SV)`,
   Ex 5.6]],
  party-pic(droppic((box-lrr, box-lch, box-cc))),

  [#step(EQ)[`(𝟙×(list((R×R)choose) concat))π₂`]], [@relator-defn, `F(RS)=F(R)F(S)`],
  party-pic(droppic((box-lrrc, box-cc))),

  [#step(SQ)[`(𝟙×(list(choose R) concat))π₂`]],
  [§@sec-party-choose, `(R×R)choose⊑choose R` \ #src[`list` monotonic, @relator-defn]],
  party-pic(droppic((box-lchr, box-cc))),

  [#step(EQ)[`(𝟙×(list(choose) list(R) concat))π₂`]], [@relator-defn, `F(RS)=F(R)F(S)`],
  party-pic(droppic((box-lch, box-lr, box-cc))),

  [#step(SQ)[`(𝟙×(list(choose) concat R))π₂`]],
  [`list(R)concat⊑concat R` \ #src[the same LEAF as @party-mono-include's sixth row]],
  party-pic(droppic((box-lch, box-cc, box-r))),

  [#step(EQ)[`(𝟙×(list(choose) concat))(𝟙×R)π₂`]], [2 of @bdm-prod-laws, `(R×S)(U×V)=(RU)×(SV)`],
  party-pic(droppic((box-lch, box-cc, box-r))),

  [#step(EQ)[`(𝟙×(list(choose) concat))π₂R`]],
  [`(𝟙×R)π₂=(Dom(π₁))π₂R` `=π₂R` \ #src[1 and 4 of @bdm-prod-laws; `π₁` is a map, hence entire, so
   `Dom(π₁)=𝟙` — @dom-laws]],
  party-pic(droppic((box-lch, box-cc), post: (box-r,))),

  [#step(EQ)[`exclude R`]], [`exclude≜(𝟙×(list(choose) concat))π₂`],
  party-pic(tallpic((), [`exclude`], 2.2, hc: true, post: (box-r,))),
)]<party-mono-exclude>

=== `(R×R)choose⊑choose R` — `choose` monotonic on `R` <sec-party-choose>

// B&dM p. 176, §7.3's first claim, left there as a simple exercise; Ex 7.38 is the LAW the derivation
// applies and this is its side condition.  A TAPE because `choose≜π₁∪π₂` is a `∪` — @coprod-laws.
// ONE BODY PER BRANCH, and a row's two branches are that body mirrored: `k` is the side the
// projection keeps, `1` for `π₁` and `-1` for `π₂`.  Each is drawn in its copy's own coordinates —
// input ports at `(0, ±ip)`, output at `(w, ±op)` — because `choosebox` is what places it.
#let pi-bare(k) = {
  let y = 0.5
  wire((0, k * y), (1.8, k * y))
  wire((0, -k * y), (1.1, -k * y)); wiredot((1.1, -k * y))
}
#let pi-rr(k) = {
  // `R×R` inside the branch: both wires run `R`, and only then is one of them dropped.
  let y = 0.5
  wire((0, k * y), (0.34, k * y)); gbox((0.34, k * y), [R]); wire((1.26, k * y), (2.6, k * y))
  wire((0, -k * y), (0.34, -k * y)); gbox((0.34, -k * y), [R])
  wire((1.26, -k * y), (1.9, -k * y)); wiredot((1.9, -k * y))
}
#let pi-r(k) = {
  // `Dom⊑𝟙` has taken the `R` off the strand this branch drops — it ends bare — leaving the `R` on
  // the kept wire alone, which is where `π₁R` puts it.
  let y = 0.5
  wire((0, k * y), (0.9, k * y)); gbox((0.9, k * y), [R]); wire((1.82, k * y), (2.6, k * y))
  wire((0, -k * y), (0.7, -k * y)); wiredot((0.7, -k * y))
}
#let pi-fork(k) = {
  // `⟨π₁R,π₂R⟩` written out: the pair is COPIED, each copy keeps one component and discards the
  // other before its `R`, and the projection then drops one of the two components.
  let y = 0.7
  wire((0, y), (0.4, y)); wcopy((0.4, y), li: 0, lo: 0.5, sp: 0.45)
  wire((0, -y), (0.4, -y)); wcopy((0.4, -y), li: 0, lo: 0.5, sp: 0.45)
  wire((0.9, 1.15), (1.2, 1.15)); gbox((1.2, 1.15), [R])
  wire((0.9, 0.25), (1.4, 0.25)); wiredot((1.4, 0.25))
  wire((0.9, -0.25), (1.4, -0.25)); wiredot((1.4, -0.25))
  wire((0.9, -1.15), (1.2, -1.15)); gbox((1.2, -1.15), [R])
  wire((2.12, k * 1.15), (3.4, k * 1.15))
  wire((2.12, -k * 1.15), (2.75, -k * 1.15)); wiredot((2.75, -k * 1.15))
}
// While the `∪` stands split into two summands — the rows between `T(R∪S)=TR∪TS` and `Dom⊑𝟙` — a row
// draws ONE BRANCH of it and no region: the two are symmetric, so the second only doubles the
// height.  The header says that once.  The rows either side of them carry the union whole.
#let pi-row(body, w, ip: 0.5, op: 0.5) = {
  lab(-0.75, ip, black)[`[A]`]; lab(-0.75, -ip, black)[`[A]`]
  body(1)
  wire((w, op), (w + 0.4, op)); lab(w + 0.8, op, black)[`[A]`]
}
// A row's whole picture: the `∪` region with `body` drawn once per branch, and whatever that row's
// formula leaves OUTSIDE the region — `R×R` on the way in, or the one `R` on the way out.
#let choose-row(body, w, ip: 0.5, op: 0.5, hh: 0.5, pre: false, post: false) = {
  let ys = 0.5
  let x0 = if pre { 2.6 } else { 1.7 }
  let x1 = x0 + w + 2 * CHPAD
  choosebox((x0, -(2 * hh + 1.55)), (x1, 2 * hh + 1.55), body(1), body(-1), ip: ip, op: op, hh: hh)
  lab(-0.75, ys, black)[`[A]`]; lab(-0.75, -ys, black)[`[A]`]
  if pre {
    wire((0, ys), (0.4, ys)); gbox((0.4, ys), [R]); wire((1.32, ys), (x0 - CHFAN, ys))
    wire((0, -ys), (0.4, -ys)); gbox((0.4, -ys), [R]); wire((1.32, -ys), (x0 - CHFAN, -ys))
  } else {
    wire((0, ys), (x0 - CHFAN, ys)); wire((0, -ys), (x0 - CHFAN, -ys))
  }
  wire((x1 + CHFAN, 0), (x1 + CHFAN + 0.4, 0))
  if post {
    gbox((x1 + CHFAN + 0.4, 0), [R]); wire((x1 + CHFAN + 1.32, 0), (x1 + CHFAN + 1.7, 0))
    lab(x1 + CHFAN + 2.1, 0, black)[`[A]`]
  } else {
    lab(x1 + CHFAN + 0.8, 0, black)[`[A]`]
  }
}

#disp[#pair(
  cetz.canvas(length: 0.8cm, choose-row(pi-bare, 1.8, pre: true)),
  cetz.canvas(length: 0.8cm, { lab(-1.9, 0, SLACK)[`⊑`]; choose-row(pi-bare, 1.8, post: true) }),
  [`(R×R)choose⊑choose R`],
)]<party-choose>

// The `⊑` is STRICT, and the witness says where: the one inequality above is `Dom⊑𝟙`.
#disp[#table(
  columns: (auto, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`R≜{(0,0)} : {0,1}⟶{0,1}`], [not entire — undefined at `1`],

  [`(R×R)choose` at `(0,1)`], [nothing — `R×R` needs BOTH components related, and `R` is undefined
   at `1`],

  [`choose R` at `(0,1)`], [`0` — `choose` picks the first component `0`, and `R 0 0` holds],

  [`((0,1),0)`], [in `choose R`, not in `(R×R)choose`],

  [`(R×R)choose=choose R`], [iff `R` is entire — `Dom⊑𝟙` is the calculation's only inequality step,
   and it is an equality iff `Dom(R)=𝟙`],
)]<choose-strict>

// The table's FIRST row has no reason: it is the starting formula.  It has no picture either — the
// next row unfolds `choose` into `π₁∪π₂` without touching the circuit, so the two would be the same
// drawing.  Rows 2 and 7–8 are the display's two panels, drawn from the same bodies.
#disp[#table(
  columns: (7.2cm, 6.2cm, 1fr),
  align: (left + horizon, left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*formula*], [*reason*], [*picture* — one branch of the `∪`; the other is symmetric]),

  [#step([])[`(R×R)choose`]], [], [],

  [#step(EQ)[`(R×R)(π₁∪π₂)`]], [`choose≜π₁∪π₂`],
  P(cetz.canvas(length: 0.8cm, choose-row(pi-bare, 1.8, pre: true)), s: 68%),

  [#step(EQ)[`(R×R)π₁∪(R×R)π₂`]], [`T(R∪S)=TR∪TS`],
  P(cetz.canvas(length: 0.8cm, pi-row(pi-rr, 2.6)), s: 68%),

  [#step(EQ)[`⟨π₁R,π₂R⟩π₁∪⟨π₁R,π₂R⟩π₂`]], [1 of @bdm-prod-laws, `R×S=⟨π₁R,π₂S⟩`],
  P(cetz.canvas(length: 0.8cm, pi-row(pi-fork, 3.4, ip: 0.7, op: 1.15)), s: 68%),

  [#step(EQ)[`(Dom(π₂R))π₁R∪(Dom(π₁R))π₂R`]], [3 and 4 of @bdm-prod-laws],
  P(cetz.canvas(length: 0.8cm, pi-row(pi-rr, 2.6)), s: 68%),

  [#step(SQ)[`π₁R∪π₂R`]], [`Dom⊑𝟙`],
  P(cetz.canvas(length: 0.8cm, pi-row(pi-r, 2.6)), s: 68%),

  [#step(EQ)[`(π₁∪π₂)R`]], [`(R∪S)T=RT∪ST`],
  P(cetz.canvas(length: 0.8cm, choose-row(pi-bare, 1.8, post: true)), s: 68%),

  [#step(EQ)[`choose R`]], [`choose≜π₁∪π₂`],
  P(cetz.canvas(length: 0.8cm, choose-row(pi-bare, 1.8, post: true)), s: 68%),
)]<party-choose-proof>

=== The derivation <sec-party-deriv>

#disp[
#zline(
  zsqc([$frac(#[`party`], ∋)$ `max(R)`], none),
  zstep(op: sym.eq, under: true)[def. `party`],
  zsqc([$frac(#[`⦇S⦈ choose`], ∋)$ `max(R)`], none),
  zstep(op: sym.eq, under: true)[@pow-laws, absorption],
  zsqc([$frac(#[`⦇S⦈`], ∋)$ `E(choose) max(R)`], none),
)
#zline(
  zstep(op: sym.supset.eq.sq, under: true)[§@sec-party-choose],
  zsqc([$frac(#[`⦇S⦈`], ∋)$ `max(R×R)` $frac(#[`choose`], ∋)$ `max(R)`], none),
)
#zline(
  zstep(op: sym.supset.eq.sq, under: true)[@mon-laws, `(𝟙×list(R×R))S⊑S(R×R)`],
  zsqc([`⦇`$frac(#[`S`], ∋)$ `max(R×R)⦈` $frac(#[`choose`], ∋)$ `max(R)`], none),
)
#zline(
  zstep(op: sym.supset.eq.sq, under: true)[Ex 7.15, the fork splits],
  zsqc([`⦇⟨`$frac(#[`include`], ∋)$ `max(R),` $frac(#[`exclude`], ∋)$ `max(R)⟩⦈` $frac(#[`choose`], ∋)$ `max(R)`], none),
)
#zline(
  zstep(op: sym.supset.eq.sq, under: true)[`include` a map, `max(R)` into each branch],
  zsqc([`⦇⟨include,π₂ list(`$frac(#[`choose`], ∋)$ `max(R)) concat⟩⦈` $frac(#[`choose`], ∋)$ `max(R)`], none),
)
]<party-laws>

// MARSDEN'S calculus (arXiv:1401.7220), not this note's: `Rel` as a BICATEGORY, so a region is a type,
// a wire a relation with its relator in the label, a bead a `⊑`.  Fills and bead style off his pp. 7, 12.
#disp[#block(breakable: false)[
#align(center, cetz.canvas(length: 1cm, {
  // His own fills: `ccffcc`/`ccccff`/`ffe6cc` for a plain 0-cell, the 50% tints `81ff81`/`8181ff` for
  // its power set, so `E X` is `X` saturated.
  let TREE = rgb("#ffe6cc"); let PAIR = rgb("#ccccff"); let EPAIR = rgb("#8181ff")
  let ELA = rgb("#81ff81"); let LA = rgb("#ccffcc")
  // One x per wire, held for the wire's whole life; `XB2` is `max(R×R)`, born at `@mon-laws` and
  // consumed at `Ex 7.38`, and `XR` is `max(R)`, touched by no step.
  let (XL, XB, XB2, XC, XR, XE) = (0.0, 1.5, 3.4, 5.7, 8.5, 9.9)
  // The beads' heights, bottom (the program) to top (the specification).
  let (Y0, Y1, Y2, Y3, Y4, Y5, TOP) = (1.6, 3.5, 5.4, 8.0, 10.4, 12.3, 13.8)
  let RA = 1.9    // how far below `@pow-laws` the fold wire leaves its column to meet it
  let RB = 1.05   // the same for `max(R×R)`, at both its ends
  // The four wires, bound once: a region's boundary is drawn from THESE lists, so a fill can never
  // disagree with the wire bounding it.
  let PXR = ((XR, 0), (XR, TOP))
  let PXC = ((XC, 0), (XC, TOP))
  let PXB = ((XB, 0), (XB, Y4 - RA), (XC, Y4))
  let PXB2 = ((XB, Y2), (XB2, Y2 + RB), (XB2, Y3 - RB), (XC, Y3))
  let lb(x, y, body) = d.content((x + 0.17, y), body, anchor: "west")
  let rg(x, y, body) = d.content((x, y), body)
  let out(x, y, body, up) = d.content((x, y), body, anchor: if up { "south" } else { "north" })

  // Fills first, every one of them a single contiguous area for one type, labelled once.
  hm-region(((XL, 0), (XL, TOP), (XC, TOP), (XC, Y4), (XB, Y4 - RA), (XB, 0)), TREE)
  hm-region(((XB, 0), (XB, Y2), (XB2, Y2 + RB), (XB2, Y3 - RB), (XC, Y3), (XC, 0)), PAIR)
  hm-region(((XB, Y2), (XB, Y4 - RA), (XC, Y4), (XC, Y3), (XB2, Y3 - RB), (XB2, Y2 + RB),
            (XB, Y2)), EPAIR)
  d.rect((XC, 0), (XR, TOP), fill: ELA, stroke: none)
  d.rect((XR, 0), (XE, TOP), fill: LA, stroke: none)

  hm-wire(PXR)
  hm-wire(PXC)
  hm-wire(PXB)
  hm-wire(PXB2)

  // One name per 0-cell, inside its own area.
  rg(4.0, 0.75, [`[A]×[A]`])
  rg(3.5, 8.4, [`E([A]×[A])`])
  rg(7.1, 4.0, [`E[A]`])
  rg(9.2, 6.5, [`[A]`])
  rg(2.6, 11.3, [`tree A`])

  // A 1-cell reaching the edge is named outside it — the program along the bottom, the
  // specification along the top; `max(R)` is one wire the whole way, so it is named at both.
  out(XB, -0.34, align(center)[`⦇⟨include,π₂ list(` \ $frac(#[`choose`], ∋)$ `max(R)) concat⟩⦈`], false)
  out(XC, -0.34, $frac(#[`choose`], ∋)$, false)
  out(XR, -0.34, [`max(R)`], false)
  out(XC, TOP + 0.34, $frac(#[`party`], ∋)$, true)
  out(XR, TOP + 0.34, [`max(R)`], true)

  // A 1-cell born and consumed inside is named beside its own stretch, once.
  lb(XB, 2.55, [`⦇⟨`$frac(#[`include`], ∋)$ `max(R),` \ $frac(#[`exclude`], ∋)$ `max(R)⟩⦈`])
  lb(XB, 4.45, [`⦇`$frac(#[`S`], ∋)$ `max(R×R)⦈`])
  lb(XB, 6.7, $frac(#[`⦇S⦈`], ∋)$)
  lb(XB2, 6.7, [`max(R×R)`])
  lb(XC, 9.2, [`E(choose)`])
  lb(XC, 11.35, $frac(#[`⦇S⦈ choose`], ∋)$)

  // The beads. ONE SHORT KEY apiece, his way; the justification is in the list below the figure.
  hm-bead((XB, Y0), [`include map`])
  hm-bead((XB, Y1), [`Ex 7.15`])
  hm-bead((XB, Y2), [`@mon-laws`])
  hm-bead((XC, Y3), [`Ex 7.38`])
  hm-bead((XC, Y4), [`@pow-laws`])
  hm-bead((XC, Y5), [`party≜`])
}))

#v(4pt)

// The key list, read UPWARD like the picture: the top line is the bottom bead.
#align(center, block(width: 12.6cm)[#src[#grid(
  columns: (2.5cm, 0.7cm, auto),
  row-gutter: 3.5pt, align: (left, center, left),
  [`include map`], text(SLACK)[$subset.eq.sq$], [`include` a map, `max(R)` into each branch],
  [`Ex 7.15`], text(SLACK)[$subset.eq.sq$], [the fork splits],
  [`@mon-laws`], text(SLACK)[$subset.eq.sq$], [`(𝟙×list(R×R))S⊑S(R×R)`],
  [`Ex 7.38`], text(SLACK)[$subset.eq.sq$], [`(R×R)choose⊑choose R`],
  [`@pow-laws`], [$=$], [absorption],
  [`party≜`], [$=$], [definition of `party`],
)]])
]]<party-marsden>

// Its own page: the section opens with a long definition display and was starting mid-page.
#pagebreak(weak: true)
== Shortest paths on a cylinder

// B&dM §7.4, p. 179.  Its crux is Theorem 7.1, not the greedy theorem: `α` is a map, so monotonic
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

  [`generate≜F(𝟙,moves trans N(union)) zip N(cp P(α))`],
  [`F(NA,N(E(LA)))⟶N(E(LA))`],
  [One fold step: extends every path of every row by the new column.],

  [`paths≜⦇generate⦈ setify union`],
  [`L N Nat⟶E(L Nat)`],
  [Every path across the cylinder.],

  [the specification \ `paths min(R)`],
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

#disp[
#zline(
  zsqc([`paths min(R)`], none),
  zstep(op: sym.eq, under: true)[definition of `paths`],
  zsqc([`⦇generate⦈ setify union min(R)`], none),
  zstep(op: sym.supset.eq.sq, under: true)[@min-laws at `union`, `R` a preorder],
  zsqc([`⦇generate⦈ setify P(min(R)) min(R)`], none),
)
#zline(
  zstep(op: sym.supset.eq.sq, under: true)[`setify` lax natural],
  zsqc([`⦇generate⦈N(min(R)) setify min(R)`], none),
  zstep(op: sym.supset.eq.sq, under: true)[@cata-fusion at `Q`],
  zsqc([`⦇Q⦈ setify min(R)`], none),
)
#zline(
  zsqc([`generate N(min(R))`], none),
  zstep(op: sym.supset.eq.sq, under: true)[(7.13), then `zip`, `trans`, `moves` lax natural],
  zsqc([`F(𝟙,N(min(R)))Q`], none),
)
#zline(
  zsqc([`Q`], none),
  zstep(op: sym.eq, under: true)[the fusion condition read as a definition],
  zsqc([`F(𝟙,moves trans N(min(R))) zip N(α)`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[`zip=𝟙+zip'`, `α=[wrap,cons]`],
  zsqc([`[N(wrap),(𝟙×moves trans N(min(R))) zip' N(cons)]`], none),
)
#align(center, block(inset: (y: 4pt))[#src[(7.13) is `F(𝟙,min(R))α⊑cp P(α) min(R)`, Theorem 7.1 at the map
  `α` with $frac(#[`F(𝟙,∋)α`], ∋)$ `=cp P(α)`: extending every path in a set and then taking a minimum
  is beaten by extending one minimum. It is the crux here, not the greedy theorem.]])
]<cyl-laws>

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

  [`R≜length≤length°`],
  [`[[Int]]⟶[[Int]]`],
  [The order the schedule is minimised over: fewer van visits is better.],

  [`ceiling≜` $frac(#[`prefix sum`], ∋)$ `max(≤)`],
  [`[Int]⟶Int`],
  [The highest the bank's balance reaches over a stretch of transactions.],

  [`floor≜` $frac(#[`prefix sum`], ∋)$ `min(≤)`],
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

  [`partition list(secure)=⦇S⦈`],
  [`[Int]⟶[[Int]]`],
  [Fusion: keeping only secure segments is what turns `glue` into `old`.],

  [`H≜(head prefix° head°)∪(nil° nil)`],
  [`[[Int]]⟶[[Int]]`],
  [One schedule's first segment is a prefix of the other's, or both are empty.],

  [`R;H≜R∩(R°⇒H)`],
  [`[[Int]]⟶[[Int]]`],
  [The refinement of `R` that makes both halves of `S` monotonic.],

  [`|R|≜R∩¬R°`],
  [`[[Int]]⟶[[Int]]`],
  [The strict part `R` splits into: `R;H=|R|∪(R∩H)`.],

  [the specification \ $frac(#[`partition list(secure)`], ∋)$ `min(R)`],
  [`[Int]⟶[[Int]]`],
  [A schedule with the fewest secure segments.],
)]<van-defn>

#disp[
#zline(
  zsqc([$frac(#[`partition list(secure)`], ∋)$ `min(R)`], none),
  zstep(op: sym.eq, under: true)[@cata-fusion, `secure prefix⊑prefix secure`],
  zsqc([$frac(#[`⦇S⦈`], ∋)$ `min(R)`], none),
  zstep(op: sym.supset.eq.sq, under: true)[(7.14) holds, (7.15) FALSE; `R;H⊑R`],
  zsqc([$frac(#[`⦇S⦈`], ∋)$ `min(R;H)`], none),
)
#zline(
  zstep(op: sym.supset.eq.sq, under: true)[@mon-laws, `S` monotonic on `R;H` by (7.16) and (7.17)],
  zsqc([`⦇`$frac(#[`S`], ∋)$ `min(R;H)⦈`], none),
  zstep(op: sym.supset.eq.sq, under: true)[`old⊑new (R;H)°`],
  zsqc([`⦇[nil,(ok→glue,new)]⦈`], none),
)
#zline(
  zsqc([`(𝟙×(R;H)) old`], none),
  zstep(op: sym.eq, under: true)[`R;H=|R|∪(R∩H)`, `∪` distributes],
  zsqc([`(𝟙×|R|) old∪(𝟙×(R∩H)) old`], none),
  zstep(op: sym.subset.eq.sq, under: true)[(7.19) and (7.20) on `|R|`, (7.21) on `R∩H`],
  zsqc([`new (R∩H)∪old (R∩H)`], none),
)
#zline(
  zstep(op: sym.subset.eq.sq, under: true)[`X∩Y⊑X;Y`, converses],
  zsqc([`(new∪old)(R;H)`], none),
)
#align(center, block(inset: (y: 4pt))[#src[(7.15) `(𝟙×R) old⊑(new∪old)R` is FALSE — the shorter
  partition need not stay secure — and that is what refining `R` to `R;H` buys; the second chain is
  (7.17), and (7.16) rests the same way on (7.18) `(𝟙×⊤) new⊑new H`.]])
]<van-laws>

#pagebreak(weak: true)
= Thinning Algorithms <sec-thin>

== Thinning

// B&dM §8.1, p. 193.  Between the two extremes of the last section: `𝟙` keeps every partial solution
// and `min(Q) {·}` keeps one, `thin Q` keeps a representative collection.
#disp[#definition[
For `Q : A⟶A`, #h(4pt) `thin Q≜(∋/∋)∩(∈\(Q°∈)) : EA⟶EA` #h(4pt) #src[(8.1)].

`ys (thin Q) xs⟺xs⊆ys∧(∀a∈ys. ∃b∈xs. b Q a)`
]]<thin-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X⊑` $frac(#[`S`], ∋)$ `thin Q⟺X∋⊑S` and `S°X⊑Q°∈`],
  [the universal property: everything kept is an `S`-value, and every `S`-value has a `Q`-lower bound
   among the kept ones],
  [`Q⊑R⟹thin Q⊑thin R`],
  [the fewer pairs `Q` relates, the fewer subsets count as thinnings],
  [`𝟙⊑thin Q`, and `thin Q` is a preorder if `Q` is],
  [keeping everything is always a legal thinning],
  [`min(R)=thin Q min(R)` #h(4pt) #src[`Q⊑R`, both preorders]],
  [*thin-introduction*: thinning first cannot lose an `R`-minimum],
  [`thin Q⊒min(Q)` $frac(#[`𝟙`], ∋)$ #h(6pt) #src[(8.2)]],
  [*thin-elimination*: keeping one element is a thinning, but its domain is the sets `min(Q)` is
   defined on],
  [$frac(#[`S`], ∋)$ `thin Q⊒` $frac(#[`S`], ∋)$ `min(R)` $frac(#[`𝟙`], ∋)$ \
   #src[(8.3), `R∩(S°S)⊑Q`]],
  [the usable variant: `R` need only refine `Q` between values `S` gives one argument],
  [`union thin Q⊒P(thin Q) union` #h(6pt) #src[(8.4)]],
  [thinning each member set is a thinning of the union],
  [`⦇`$frac(#[`F(∋)S`], ∋)$ `thin Q⦈⊑` $frac(#[`⦇S⦈`], ∋)$ `thin Q` \ #src[Theorem 8.1, `S` monotonic on `Q`]],
  [the *thinning theorem*: thinning at every step beats thinning only at the end],
  [`⦇`$frac(#[`F(∋)S`], ∋)$ `thin Q⦈ min(R)⊑` $frac(#[`⦇S⦈`], ∋)$ `min(R)` \ #src[Corollary 8.1, `Q⊑R` as well]],
  [the same against the optimisation problem itself, by thin-introduction],
)]<thin-laws>

== Paths in a layered network

// B&dM §8.2, p. 196.  `Q` has to record `head` because `wt (a, head xs)` is unbounded: a dearer path
// with a nearer first vertex can still win.
#disp[#definition[
`F(A,X)=A+A×X`, #h(4pt) `L=list⁺` with initial algebra `α≜[wrap,cons] : F(A,LA)⟶LA`.

`wrapz≜⟨wrap,zero⟩`, #h(4pt) `consw (a,(xs,n))=(cons (a,xs),wt (a,head xs)+n)`.

`cost≜⦇[wrapz,consw]⦈π₂`, #h(4pt) `⦇[wrapz,consw]⦈=⟨𝟙,cost⟩`, #h(4pt) `R≜cost≤cost°`.

`Q≜R∩(head head°)`, #h(4pt) `S≜F(𝟙,∋)α`, #h(4pt) $frac(#[`F(∋,𝟙)`], ∋)$ `=𝟙+cpl`, #h(4pt)
$frac(#[`F(𝟙,∋)`], ∋)$ `=𝟙+cpr`, #h(4pt) `step≜cpr P(cons) min(R)`.
]]<path-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`⦇F(∋,𝟙)α⦈`], ∋)$ `min(R)` #h(4pt) #src[`=` $frac(#[`L(∋)`], ∋)$ `min(R)`]],
  [the specification: a least-cost path across the network],
  [`F(∋,Q)α⊑F(∋,𝟙)αQ`],
  [`S` is monotonic on `Q`; on `R` it is not, since the next edge can cost arbitrarily much],
  [`⦇`$frac(#[`F(∋,∋)α`], ∋)$ `thin Q⦈ min(R)⊑` $frac(#[`⦇F(∋,𝟙)α⦈`], ∋)$ `min(R)` \ #src[Corollary 8.1]],
  [thinning applies: one partial path per starting vertex is enough],
  [`S head⊑[𝟙,π₂]` \ #src[`S head` simple, so `R∩(S°S)⊑Q`]],
  [the side condition of (8.3): between two paths `S` builds from one argument, equal cost and equal
   head already means `Q`],
  [$frac(#[`F(∋,∋)α`], ∋)$ `thin Q` \ #h(6pt) `⊒` $frac(#[`F(∋,𝟙)`], ∋)$ `P(`$frac(#[`F(𝟙,∋)`], ∋)$ `P(α) min(R))` \
   #src[(8.4), (8.3), `P(`$frac(#[`𝟙`], ∋)$`) union=𝟙`]],
  [thin eliminated: split the algebra at `F(∋,𝟙)F(𝟙,∋)`, thin each part, one minimum per part],
  [$frac(#[`F(𝟙,∋)`], ∋)$ `P(α) min(R)=[wrap,step]`],
  [that inner part read off the two branches of `α`],
  [$frac(#[`⦇F(∋,𝟙)α⦈`], ∋)$ `min(R)⊒⦇[P(wrap),cpl P(step)]⦈ min(R)`],
  [the program: one fold, a best path per vertex of the current layer],
)]<path-laws>

// Same reason as the two hand-placed breaks in §18: `sticky` cannot hold a heading to a BREAKABLE
// figure, so this heading stranded itself at the foot of the page.
#pagebreak(weak: true)
== Implementing thin

// B&dM §8.3, p. 199.  Lemma 8.1 is printed with `R` where its own proof and Theorem 8.2 write `P`;
// it is one connected preorder, spelled `P` here.
#disp[#definition[
`setify : [A]⟶EA`, #h(4pt) `cup : EA×EA⟶EA`, #h(4pt) `cp(F)≜` $frac(#[`F(∋)`], ∋)$, #h(4pt)
`listcp(F) : F([A])⟶[FA]`, #h(4pt) `sort P≜setify° ordered P` for `P` a connected preorder.

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
  [`sort P thinlist Q⊑thin Q sort P` #h(6pt) #src[(8.6)]],
  [thinning a sorted list is a thinning of the set — this is what `thinlist Q⊑subseq` buys],
  [`sort P minlist Q⊑min(Q)` #h(6pt) #src[(8.7)]],
  [a minimum of the sorted list is a minimum of the set],
  [`sort(fPf°) list(f)⊑P(f) sort P` #h(6pt) #src[(8.8)]],
  [shunt a function through a sort],
  [`sort P filter(p)⊑E(p) sort P` #h(6pt) #src[(8.9), `p` coreflexive]],
  [filtering a sorted list sorts the restricted set],
  [`(sort P×sort P) merge P⊑cup sort P` #h(6pt) #src[(8.10)]],
  [merging two sorted lists sorts their union],
  [`F(sort P) listcp(F)⊑cp(F) sort(FP)` \ #src[(8.11), `F` linear]],
  [`listcp(F)` is the list implementation of the cartesian product `cp(F)`],
  [`F(sort P) listcp(F) list(f) filter(p)⊑` $frac(#[`F(∋)fp`], ∋)$ `sort P` \ #src[Lemma 8.1, `f` monotonic on
   `P`, `p` coreflexive]],
  [one sorted list built from sorted arguments, instead of a set built and then sorted],
  [`⦇listcp(F) ⟨g₁,g₂⟩ merge P thinlist Q⦈ minlist R` \ #h(6pt) `⊑` $frac(#[`⦇S⦈`], ∋)$ `min(R)` \
   #src[Theorem 8.2]],
  [the *binary thinning theorem*: a fold on sorted lists of partial solutions, thinned at every step],
)]<thinlist-laws>

== The knapsack problem

// B&dM §8.4, p. 205.  The printed base of the final fold is `nil`, without the outer `wrap` that
// §8.5 and §8.6 do print (`wrap wrap wrap`, `start wrap`).
#disp[#definition[
`vol,wt : Item⟶Real`, #h(4pt) `value≜list(vol) sum`, #h(4pt) `weight≜list(wt) sum`.

`subseq=⦇[nil,cons]∪[nil,π₂]⦈`, #h(4pt) `within w` the coreflexive on `xs` with `weight xs≤w`.

`≥≜≤°`, #h(4pt) `R≜value≥value°`, #h(4pt) `Q≜R∩(weight≤weight°)`, #h(4pt) `P≜R`.

`FA=1+Item×A`, #h(4pt) `listcp(F)=wrap+cpr`, #h(4pt) `g₁≜list([nil,cons]) filter(within w)`
#h(4pt) `=[list(nil),h₁]`, #h(4pt) `g₂≜list([nil,π₂])=[list(nil),h₂]`.

`h₁≜list(cons) filter(within w)`, #h(4pt) `h₂≜list(π₂)`.
]]<knap-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`subseq (within w)`], ∋)$ `min(R)`],
  [the specification: a selection of greatest total value that stays within the capacity `w`],
  [`subseq (within w)=⦇([nil,cons] (within w))∪[nil,π₂]⦈` \ #src[fusion, weights non-negative]],
  [the selections that fit are themselves a fold, and the fold's algebra already has binary thinning's
   shape],
  [`(𝟙×R) (cons (within w))⊑cons (within w)R` \ #src[FALSE]],
  [not monotonic on `R`: a selection of greater value need not still fit once one more item goes in],
  [`(𝟙×Q) (cons (within w))⊑cons (within w)Q` \ `(𝟙×Q)π₂⊑π₂Q`],
  [both halves are monotonic on `Q` once ties in value are broken by weight],
  [`⦇listcp(F) ⟨g₁,g₂⟩ merge R thinlist Q⦈ minlist R` \ #src[Theorem 8.2 at `P≜R`, `F` linear]],
  [binary thinning, sorting in descending order of value],
  [`knapsack w=⦇[nil,cpr ⟨h₁,h₂⟩ merge R thinlist Q]⦈ minlist R`],
  [the program; `minlist R` becomes `head`, since packings come out in descending value],
)]<knap-laws>

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

`width≜⦇[length,(length×𝟙) plus succ]⦈`, #h(4pt) `fits w` the coreflexive on a line `x` with
`width x≤w`, #h(4pt) `ok w` the coreflexive on `[x]⧺xs` with `width x≤w`.

`white w x=w−width x`, #h(4pt) `collect≜list(sqr) sum`, #h(4pt) `waste w≜init list(white w) collect`.

`R≜(waste w)≤(waste w)°`, #h(4pt) `Q≜R∩(head head°)`, #h(4pt) `P≜⊤`.

`g₁≜list([wrap wrap,new])`, #h(4pt) `g₂≜list([wrap wrap,glue]) filter(ok w)`, #h(4pt)
`start≜wrap wrap wrap`, #h(4pt) `h₁≜list(new)`, #h(4pt) `h₂≜list(glue) filter(ok w)`.
]]<para-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`partition list⁺(fits w)`], ∋)$ `min(R)`],
  [the specification: least waste among the paragraphs whose every line fits],
  [`partition list⁺(fits w)=⦇[wrap wrap,new∪(glue (ok w))]⦈` \ #src[fusion, every word fits on a
   line by itself]],
  [the fitting paragraphs are themselves a fold],
  [`[wrap wrap,new∪(glue (ok w))]` \ #h(6pt) `=[wrap wrap,new]∪([wrap wrap,glue] (ok w))`],
  [rewritten into binary thinning's shape `(f₁p₁)∪(f₂p₂)`],
  [`(𝟙×R) glue⊑glue R` #h(6pt) #src[FALSE]],
  [`glue` is not monotonic on `R`: the waste of a paragraph depends on its whole first line, so no
   greedy algorithm solves this],
  [`(𝟙×Q) new⊑new Q` \ `(𝟙×Q) (glue (ok w))⊑glue (ok w)Q` \ #src[`cons` monotonic on
   `collect≤collect°`]],
  [both halves are monotonic on `Q` once ties in waste are broken by the first line],
  [`merge ⊤=cat`; #h(4pt) `P≜head prefix head°` also serves],
  [`⊤` needs no sorting at all, and `prefix` is a linear order on first lines of paragraphs of one
   input],
  [`⦇listcp(F) ⟨g₁,g₂⟩ cat thinlist Q⦈ minlist R` \ #src[Theorem 8.2 at `P≜⊤`]],
  [binary thinning, one candidate kept per first line],
  [`paragraph w=⦇[start,cpr ⟨h₁,h₂⟩ cat thinlist Q]⦈ minlist R`],
  [the program, `g₁` and `g₂` split along the coproduct],
)]<para-laws>

== Bitonic tours

// B&dM §8.6, p. 212.  `Q` records `next2`, not `head`: tours of one input already share their heads,
// and the cost of the next drop turns on the second city of each list.
#disp[#definition[
`FA=(City×City)+(City×A)`, the base functor of cons-lists of length at least two; #h(4pt)
`listcp(F)=wrap+cpr`; #h(4pt) `tc : City×City⟶Real`, neither positive nor symmetric.

`start (a,b)=([a,b],[a,b])`, #h(4pt) `dropl (a,([b]⧺xs,ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt)
`dropr (a,(xs,[b]⧺ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt) `tour≜⦇[start,dropl∪dropr]⦈`.

`cost (xs,ys)=outcost xs+incost ys`, #h(4pt) `outcost [a₀,…,aₙ]=tc (a₀,a₁)+⋯+tc (aₙ₋₁,aₙ)`,
#h(4pt) `incost [a₀,…,aₙ]=tc (a₁,a₀)+⋯+tc (aₙ,aₙ₋₁)`.

`next≜tail head`, #h(4pt) `next2≜next×next`, #h(4pt) `R≜cost≤cost°`, #h(4pt)
`Q≜R∩(next2 next2°)`, #h(4pt) `P≜⊤`, #h(4pt) `g₁≜list([start,dropl])`, #h(4pt)
`g₂≜list([start,dropr])`.
]]<tour-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`tour`], ∋)$ `min(R)`],
  [the specification: a least-cost bitonic tour, outward journey and return kept as a pair of lists],
  [`(𝟙×R) dropl⊑dropl R` #h(6pt) #src[FALSE] \ `(𝟙×R) dropr⊑dropr R` #h(6pt) #src[FALSE]],
  [neither drop is monotonic on `R`: the two edges it adds and removes depend on `head` and `next`
   of both lists],
  [`(𝟙×Q) dropl⊑dropl Q` \ `(𝟙×Q) dropr⊑dropr Q`],
  [both are, once ties in cost are broken by the two second cities — the heads already agree among
   tours of one input],
  [`⦇listcp(F) ⟨g₁,g₂⟩ cat thinlist Q⦈ minlist R` \ #src[Theorem 8.2 at `P≜⊤`, `merge ⊤=cat`]],
  [binary thinning, one candidate per pair of second cities],
  [`mintour=⦇[start wrap,cpr ⟨list(dropl),list(dropr)⟩ cat thinlist Q]⦈ minlist R`],
  [the program: quadratic, because each step adds just two tours to the list kept],
)]<tour-laws>

#pagebreak(weak: true)
= Dynamic Programming <sec-dp>

== Theory

// B&dM §9.1, p. 220.  @sec-opt's problem with the algebra cut down to a MAP `h`; the decompositions
// come from `⦇T⦈°`, and the recursion is over them rather than over an initial algebra.
#disp[#definition[
`h : FB⟶B` a map, #h(4pt) `T : FA⟶A` an F-algebra, #h(4pt) `R : B⟶B`.

`H≜⦇T⦈°⦇h⦈ : A⟶B`, #h(4pt) `M≜` $frac(#[`H`], ∋)$ `min(R)` the problem to be solved, #h(4pt) `(μX : G(X))` the
least fixed point of `G`.
]]<dp-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(μX :` $frac(#[`T°`], ∋)$ `P(F(X)h) min(R))⊑M` \ #src[Theorem 9.1, `h` monotonic on `R`]],
  [*dynamic programming*: decompose in every way, solve each part, keep one optimum per part],
  [$frac(#[`T°`], ∋)$ `P(F(M)h) min(R)⊑M` #h(6pt) #src[(9.1)]],
  [all Knaster–Tarski leaves to prove],
  [$frac(#[`T°`], ∋)$ `P(F(M)h) min(R)⊑H` #h(6pt) #src[(9.2)] \
   `H°` $frac(#[`T°`], ∋)$ `P(F(M)h) min(R)⊑R` #h(6pt) #src[(9.3)]],
  [(9.1) split by the universal property of `min`],
  [`P(X) min(R)⊑(∋X)∩(∈\(XR°))` \ #src[(9.4) = (7.10), @min-laws]],
  [the only fact about `min` either proof uses],
  [`(μX :` $frac(#[`T°`], ∋)$ `thin Q P(F(X)h) min(R))⊑M` \ #src[Theorem 9.2, `Q` a preorder with
   `QF(H)h⊑F(H)hR`; `thin Q` as in @thin-laws]],
  [the same with a thinning step: decompositions that can never win are dropped],
  [the fixed point is unique, and entire \ #src[Theorem 6.3, `T°` followed by `F`'s membership
   relation inductive; $frac(#[`T°`], ∋)$ finite and non-empty, `R` connected]],
  [when the recursion can be refined to a recursive function],
  [$frac(#[`[V₁,V₂]°`], ∋)$ `thin(Q₁+Q₂) P([U₁,U₂]) min(R)` \ #h(10pt) `=(Ran V₁→W₁,W₂)` \ #h(10pt)
   `Wᵢ≜` $frac(#[`Vᵢ°`], ∋)$ `thin(Qᵢ) P(Uᵢ) min(R)` \ #src[Proposition 9.1, `V₂V₁°=⊥`]],
  [`FA` is usually a coproduct, and disjoint ranges split the fixed point into one branch per
   summand],
  [`F(R)h⊑hR` \ `QF(H)h⊑F(H)hR`],
  [the two conditions to be checked, in the order the three propositions below discharge them],
  [`F(R)h⊑hR` \ #src[Proposition 9.2, `R≜cost≤cost°`, `h cost=F(cost)k`,
   `F(≤)k⊑k≤`]],
  [monotonicity when the cost is itself a fold with a step `k` monotonic on `≤`],
  [`F(R∩(H°H))h⊑hR` \ #src[Proposition 9.3, `R≜cost≤cost°`,
   `h cost=F(⟨cost,H°⟩)k`, `F(≤×𝟙)k⊑k≤`, `H°` simple]],
  [monotonicity *in context*: `k` may also read the input the part was built from],
  [`Q≜F(U,V)` \ #src[Proposition 9.4, `U`, `V` preorders, `F(U,R)h⊑hR`, `VH⊑HR`]],
  [both conditions of Theorem 9.2 at once, split along the two arguments of a bifunctor],
)]<dp-laws>

== The string edit problem

// B&dM §9.2, p. 225.  The section numbers no equation.  `base` and `step` are reused for the
// tabulating fold at the foot of the table; they are not `edit`'s.
#disp[#definition[
`Op::=cpy Char∣del Char∣ins Char`, #h(4pt) `F(A,B)=1+(A×B)`, #h(4pt) `α≜[nil,cons]`.

`edit≜⦇[base,step]⦈ : [Op]⟶[Char]×[Char]`, #h(4pt) `base` returning `([],[])`,
#h(4pt) `step (cpy a,(xs,ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt) `step (del a,(xs,ys))=([a]⧺xs,ys)`,
#h(4pt) `step (ins a,(xs,ys))=(xs,[a]⧺ys)`.

`length≜⦇[zero,π₂ succ]⦈`, #h(4pt) `R≜length≤length°`, #h(4pt) `U≜⊤`, #h(4pt)
`V≜suffix°×suffix°`, #h(4pt) `Q≜𝟙+(U×V)`, #h(4pt) `empty` the coreflexive on `(xs,ys)` with
both lists empty.

`unstep` implements $frac(#[`step°`], ∋)$ `thin(U×V)`: #h(4pt) `unstep ([a]⧺xs,[])=[(del a,(xs,[]))]`,
#h(4pt) `unstep ([],[b]⧺ys)=[(ins b,([],ys))]`, #h(4pt)
`unstep ([a]⧺xs,[b]⧺ys)=(a=b→[(cpy a,(xs,ys))],[(del a,(xs,[b]⧺ys)),(ins b,([a]⧺xs,ys))])`.
]]<edit-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`edit°`], ∋)$ `min(R)`],
  [the specification: a shortest edit sequence from which both strings can be reconstituted],
  [`F(R)α⊑αR` \ #src[Proposition 9.2 at `length`, `succ` monotonic on `≤`]],
  [`cons` is monotonic on `R`, so Theorem 9.1 already applies],
  [`QF(𝟙,edit°)α⊑F(𝟙,edit°)αR`],
  [the thinning condition sought, over `F(Op,[Char]×[Char])`],
  [`F(⊤,R)α⊑αR` #h(6pt) #src[left as an exercise]],
  [`U≜⊤` costs nothing: any two operations may be compared],
  [`edit (𝟙×suffix)⊑R° edit` \ `edit (suffix×𝟙)⊑R° edit`],
  [the other half of Proposition 9.4 for `V≜suffix°×suffix°`],
  [`edit (𝟙×tail)⊑R° edit` \ `edit (tail×𝟙)⊑R° edit` \
   #src[`suffix=tail*`, and `BA⊑CB⟹BA*⊑C*B`]],
  [one step is enough: drop the operation that produced the head, or weaken its `cpy` to a `del` —
   never lengthening the sequence],
  [`(μX :` $frac(#[`[base,step]°`], ∋)$ `thin Q P([nil,(𝟙×X) cons]) min(R))⊑` $frac(#[`edit°`], ∋)$ `min(R)` \
   #src[Theorem 9.2]],
  [a copy, when available, beats a delete or an insert],
  [`X=(empty→nil,` $frac(#[`step°`], ∋)$ `thin(U×V) P((𝟙×X) cons) min(R))` #h(4pt) #src[Proposition 9.1]],
  [`base` and `step` have disjoint ranges],
  [`mle=(empty→nil,unstep list((𝟙×mle) cons) minlist R)`],
  [the program: at most two decompositions survive, but the same subproblem is solved many times,
   so the running time is exponential],
  [`column xs ys=[mle (u,ys)∣u←tails xs]` \ `column xs=⦇[fstcol xs,nextcol xs]⦈`, #h(4pt)
   `fstcol=list(del) tails`],
  [the tabulation: `mle (xs,ys)` needs `mle (u,v)` for every tail `u` of `xs` and `v` of `ys`, so the
   columns are built right to left],
  [`column xs ([b]⧺ys)=nextcol xs (b,column xs ys)` \
   `nextcol xs (b,us)` \ #h(10pt) `=⦇[base (b,last us),step b]⦈ xus` \ #h(10pt)
   `xus=zip (xs,zip (init us,tail us))`],
  [each column is a fold built bottom to top, over `xs` zipped with the adjacent pairs of the column
   to its right],
  [`base (b,u)=[[ins b]⧺u]` \ `step b ((a,(u,v)),ws)=` \ #h(10pt)
   `(a=b→[[cpy a]⧺v]⧺ws,` \ #h(10pt) `[bmin(R) ([del a]⧺w,[ins b]⧺u)]⧺ws)` \
   #src[`w=head ws`; these `base`, `step` are not `edit`'s]],
  [an entry depends on the one below it (a delete), the one to its right (an insert), and the one
   below that (a copy) — quadratic in the two lengths],
)]<edit-laws>

== Optimal bracketing

// B&dM §9.3, p. 230.  `⦇T⦈ = flatten` is a map, so `H° = flatten` is simple and Proposition 9.3
// applies; no decomposition is preferable to another here, so there is no thinning step.
#disp[#definition[
`tree A::=tip A∣bin (tree A,tree A)`, #h(4pt) `FX=A+X²`, so `F(R)=𝟙+R²`; #h(4pt)
`h≜[tip,bin]`, #h(4pt) `flatten≜⦇[wrap,cat]⦈ : tree A⟶list⁺ A`, #h(4pt) `H=flatten°`.

`⟨cost,size⟩≜⦇[opt,opb]⦈`, #h(4pt) `opt≜⟨zero,st⟩`, #h(4pt)
`opb ((cx,sx),(cy,sy))=(cb (sx,sy)+cx+cy,sb (sx,sy))`.

`sb` associative, so `size=flatten sz` for a map `sz`; #h(4pt) `R≜cost≤cost°`, #h(4pt)
`g≜[zero,(𝟙×sz)² opb π₁]`, #h(4pt) `single` the coreflexive on singleton lists.

`splits≜⟨inits⁺,tails⁺⟩ zip`, an implementation of $frac(#[`cat°`], ∋)$; #h(4pt) `array≜inits list(row)`,
#h(4pt) `row≜tails list(mct)`, #h(4pt) `col≜inits list(mct)`.

`mix≜zip list(bin) minlist R`, #h(4pt) `next≜⟨π₁,mix⟩ snoc`, #h(4pt)
`process≜((tip wrap)×𝟙) loop(next)`.
]]<mct-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`flatten°`], ∋)$ `min(R)`],
  [the specification: a least-cost bracketing of `a₁⊕⋯⊕aₙ`, the tree whose flattening is the
   given list],
  [`[tip,bin] cost=(𝟙+⟨cost,flatten⟩²) g` #h(4pt) #src[(9.5)]],
  [the cost of a node reads only the cost and the flattening of its two subtrees],
  [`(𝟙+(≤×𝟙)²) g⊑g≤` #h(6pt) #src[(9.6)]],
  [`g` is monotonic on `≤` in its two cost arguments],
  [`F(R∩(flatten flatten°))h⊑hR` \ #src[Proposition 9.3, `H°=flatten` a map]],
  [monotonicity in context: only trees with the same flattening are compared],
  [`(μX :` $frac(#[`[wrap,cat]°`], ∋)$ `P([tip,(X×X) bin]) min(R))⊑` $frac(#[`flatten°`], ∋)$ `min(R)` #h(4pt)
   #src[Theorem 9.1]],
  [split the list in every way, bracket both halves, join],
  [`X=(single→wrap° tip,` $frac(#[`cat°`], ∋)$ `P((X×X) bin) min(R))` #h(4pt) #src[Proposition 9.1]],
  [`wrap` and `cat` have disjoint ranges],
  [`mct=(single→head tip,splits list((mct×mct) bin) minlist R)`],
  [the program; exponential, since the segments of one list overlap],
  [`mct=(single→head tip,⟨init col,tail row⟩ mix)` #h(4pt) #src[(9.7)]],
  [the tabulation: `mct xs` is needed for every non-empty segment `xs`, so the values are held as an
   array of rows],
  [`col=(single→head tip wrap,⟨init col,tail row⟩ next)` #h(4pt) #src[(9.8)] \
   `cons col=(𝟙×array) process` #h(4pt) #src[(9.9)] \
   `row=(single→head tip wrap,⟨mct,tail row⟩ cons)` #h(4pt) #src[(9.10)]],
  [a column extends the column to its left, a row the row below it; (9.9) is (9.8) rewritten as a
   loop],
  [`array=⦇[fstcol,addcol]⦈`, #h(4pt) `fstcol≜tip wrap wrap` \
   `addcol≜⟨π₁ tip wrap,step⟩ cons` \ `step≜⟨process tail,π₂⟩ zip list(cons)`],
  [the program: one fold building the array column by column, cubic in the length of the input],
)]<mct-laws>

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

`lrt ws=min(prefix°×(⊤+⊤)) {(xs,(ys,zs))∣xs⧺zs=ws`, `ys⧺zs` a proper prefix of `ws}`,
the longest repeated tail; #h(4pt)
`reduce (ws⧺[a])=(zs≠[]→[(ws,sym a),(xs,ptr (ys,zs))],[(ws,sym a)])` with
`(xs,(ys,zs))=lrt (ws⧺[a])`.
]]<code-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`decode°`], ∋)$ `min(R)`],
  [the specification: a smallest code sequence decoding to the given string],
  [`F(R)α⊑αR` #h(6pt) #src[`(⊤+⊤)[c,p]=[c,p]`]],
  [monotonicity is routine, the two costs being constants],
  [`F(⊤+⊤,R)α⊑αR` \ `decode prefix⊑R° decode` \ #src[Proposition 9.4 at `Q≜F(⊤+⊤,prefix°)`]],
  [the thinning condition split in two: pointers are ordered only by how much input they consume,
   symbols and pointers not at all],
  [`decode init⊑R° decode`],
  [enough for the second: drop the last character of the output by shortening or removing the last
   code element, never raising the cost],
  [`(μX :` $frac(#[`[nil,extend]°`], ∋)$ `thin Q P([nil,(X×𝟙) snoc]) min(R))⊑` $frac(#[`decode°`], ∋)$ `min(R)` \
   #src[Theorem 9.2]],
  [between a symbol and a pointer nothing can be decided in advance; between two pointers the longer
   match wins],
  [`X=(null→nil,` $frac(#[`extend°`], ∋)$ `thin(prefix°×(⊤+⊤)) P((X×𝟙) snoc) min(R))` \
   #src[Proposition 9.1]],
  [`nil` and `extend` have disjoint ranges],
  [$frac(#[`extend°`], ∋)$ `(ws⧺[a])={(ws,sym a)}∪` \ #h(10pt)
   `{(xs,ptr (ys,zs))∣xs⧺zs=ws⧺[a]`, `ys⧺zs` a proper prefix of `ws}`],
  [the decompositions of one string: take the last character as a symbol, or end with a pointer],
  [`reduce` implements $frac(#[`extend°`], ∋)$ `thin(prefix°×(⊤+⊤))`],
  [thinning leaves at most two: the symbol, and the pointer of `lrt`],
  [`encode=(null→nil,reduce list((encode×𝟙) snoc) minlist R)`],
  [the program, again exponential; the book gives no tabulation for it],
)]<code-laws>

#pagebreak(weak: true)
= Greedy Algorithms <sec-greedy>

== Theory

// B&dM §10.1, p. 245.  Theorem 9.2 with `min(Q)` for `thin Q`: the same hypotheses, a much stronger
// conclusion, and one far harder to refine into a program.
#disp[#definition[
`h`, `T`, `R`, `H`, `M` as in @dp-defn; #h(4pt) additionally `Q` a *connected* preorder on the sets
$frac(#[`T°`], ∋)$ returns, so that $frac(#[`T°`], ∋)$ `min(Q)` is entire.
]]<greedy-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(μX :` $frac(#[`T°`], ∋)$ `min(Q) F(X)h)⊑M` \ #src[Theorem 10.1, the hypotheses of Theorem 9.2]],
  [*greedy*: one decomposition is kept at every step, so `P` and $frac(#box(width: 8pt), ∋)$ disappear from the recursion],
  [$frac(#[`[V₁,V₂]°`], ∋)$ `min(Q₁+Q₂) [U₁,U₂]` \ #h(10pt) `=(Ran V₁→W₁,W₂)` \ #h(10pt)
   `Wᵢ≜` $frac(#[`Vᵢ°`], ∋)$ `min(Qᵢ) Uᵢ` \ #src[Proposition 10.1, `V₂V₁°=⊥`]],
  [Proposition 9.1 with `min` for `thin`],
  [`Q≜F(U,V)` #h(6pt) #src[Proposition 9.4]],
  [still the way to get both conditions, but $frac(#[`T°`], ∋)$ `min(Q)` must now be entire as well],
  [#src[Theorem 7.2, @mon-laws]],
  [that greedy theorem chooses among the *results* of one relational step of a reduce;
   Theorem 10.1 chooses among the *decompositions* of the input, for an arbitrary `T` rather than an
   initial algebra, at the cost of `h` being a map],
)]<greedy-laws>

== The detab-entab problem

// B&dM §10.2, p. 246.  `V ≜ prefix° ∩ (fill fill°)` is the whole trick: a bare `prefix°` fails because
// a prefix of the expansion can be longer than the input once it crosses a tab stop.
#disp[#definition[
`detab≜⦇[nil,expand]⦈ : String⟶String` over snoc-lists, #h(4pt) `α≜[nil,snoc]`, #h(4pt)
`H=detab°`; #h(4pt) `expand (xs,a)=(a=TB→fill xs,xs⧺[a])`, #h(4pt)
`fill xs=xs⧺blanks (n−(col xs) mod n)`.

`col≜⦇[zero,count]⦈`, #h(4pt) `count (c,a)=(a=NL→0,c+1)`; #h(4pt) `TB` the tab, `BL` the
blank, `NL` the newline, tab stops every `n` columns.

`R≜length≤length°`, #h(4pt) `U` the preorder with `a U b⟺a=TB∨a=b`, #h(4pt)
`V≜prefix°∩(fill fill°)`, #h(4pt) `Q≜𝟙+(V×U)`.

`unfill xs` the shortest prefix of `xs` with `fill (unfill xs)=fill xs`; #h(4pt) `tbc` the trailing
blank count, #h(4pt) `triple≜⟨unfill entab,⟨tbc,col⟩⟩`.
]]<entab-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`detab°`], ∋)$ `min(R)`],
  [the specification: a shortest input `detab` expands to the given output — `detab entab=𝟙` and
   nothing shorter does],
  [`F(⊤,R)α⊑αR` #h(6pt) #src[left as an exercise]],
  [`U` may be any preorder on characters; `a U b⟺a=TB∨a=b` puts `TB` below every character, so `min` prefers
   a tab to a blank],
  [`detab prefix⊑R° detab` #h(6pt) #src[FALSE]],
  [at `n=8`, `detab [a,b,c,d,e,TB]=[a,b,c,d,e,BL,BL,BL]`, whose prefix `[a,b,c,d,e,BL,BL]` is
   longer than any input giving it],
  [`detab V°⊑R° detab` #h(6pt) #src[`V≜prefix°∩(fill fill°)`]],
  [true once only the prefixes that do not cross a tab stop are allowed],
  [`nil V°=nil` #h(10pt) `fill V°=fill` \ `snoc V°⊑snoc∪(π₁V°)` #h(6pt) #src[left as exercises]],
  [the three properties of `V` the derivation rests on; the second is what `fill fill°` was added for],
  [`expand V°⊑expand∪(π₁V°)`],
  [the claim they add up to: shortening the output either leaves the last step alone or discards it],
  [`detab V°⊑detab∪(init detab V°)` \ #src[`init` inductive, so the greatest solution is the unique
   one]],
  [hence `detab V°⊑prefix detab`, and `prefix⊑R°` finishes Proposition 9.4],
  [`(μX :` $frac(#[`[nil,expand]°`], ∋)$ `min(Q) (𝟙+(X×𝟙)) [nil,snoc])⊑` $frac(#[`detab°`], ∋)$ `min(R)` \
   #src[Theorem 10.1]],
  [greedy: one character of input is decided at each step],
  [`X=(null→nil,` $frac(#[`expand°`], ∋)$ `min(V×U) (X×𝟙) snoc)` #h(4pt) #src[Proposition 10.1]],
  [`nil` and `expand` have disjoint ranges],
  [$frac(#[`expand°`], ∋)$ `(xs⧺[a])={(ys,TB)∣fill ys=xs⧺[a]}∪{(xs,a)}` \ #h(6pt)
   the first set is non-empty iff `a=BL` and `col (xs⧺[a]) mod n=0`],
  [the last output character came from a tab only if it is a blank landing exactly on a tab stop],
  [$frac(#[`expand°`], ∋)$ `min(V×U) (xs⧺[a])=` \ #h(10pt)
   `(a=BL∧col (xs⧺[a]) mod n=0→(unfill xs,TB),(xs,a))`],
  [the greedy step: emit a tab whenever a tab is legal, consuming all the blanks back to the previous
   tab stop],
  [`entab xs=entab (unfill xs)⧺blanks (tbc xs)` #h(4pt) #src[(10.1)]],
  [what makes `triple` a snoc-list reduce: the output splits at the last tab stop],
  [`triple=⦇[base,op]⦈` and `entab=triple assocl π₁ (𝟙×blanks) cat`],
  [the program: one pass carrying the column and the count of pending blanks],
  [`base` returns `([],(0,0))` \ `op ((xs,(t,c)),a)=` \ #h(10pt)
   `(a=BL∧(c+1) mod n≠0→(xs,(t+1,c+1)),` \ #h(10pt)
   `a=BL→(xs⧺[TB],(0,c+1)),` \ #h(10pt)
   `a=NL→(xs⧺blanks t⧺[NL],(0,0)),` \ #h(10pt)
   `(xs⧺blanks t⧺[a],(0,c+1)))`],
  [hold a blank back, cash the held blanks in for a tab at a tab stop, flush them at a newline,
   flush them before anything else],
)]<entab-laws>

== The minimum tardiness problem

// B&dM §10.3, p. 253.  Both conditions need context, and `cost` has to be restated over `perm xs`
// before Proposition 9.3 fits — `penalty` reads the bag of scheduled jobs, not their order.
#disp[#definition[
`FX=1+(X×Job)`, #h(4pt) `α≜[nil,snoc]` on schedules, #h(4pt) `β≜[nil,snag]` on bags,
`snag` putting a job into a bag; #h(4pt) `bagify≜⦇β⦈ : [Job]⟶Bag Job`, #h(4pt) `H=bagify°`.

`ct`, `dt`, `wt : Job⟶Real` the completion, due and weighting quantities of a job; #h(4pt)
`penalty (xs,j)=(sum (list(ct) xs)+ct j−dt j)×wt j`.

`cost≜` $frac(#[`prefix`], ∋)$ `P(α° [zero,penalty]) max(≤)`, #h(4pt) `cost []=0`, #h(4pt)
`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))`, #h(4pt) `R≜cost≤cost°`.

`perm≜bagify bagify°=⦇[nil,add]⦈`, #h(4pt) `add (xs,j)=ys⧺[j]⧺zs` for some `xs=ys⧺zs`.

`k≜[zero,assocr (𝟙×((bagify°×𝟙) penalty)) bmax]`, #h(4pt)
`f≜[zero,(bagify°×𝟙) penalty]`, #h(4pt) `Q≜f≤f°`.
]]<tardy-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`bagify°`], ∋)$ `min(R)`],
  [the specification: an ordering of the given bag of jobs with least maximum penalty],
  [`F(R∩(bagify bagify°))α⊑αR` #h(4pt) #src[(10.2)]],
  [monotonicity in context — only schedules of one bag are compared],
  [`(Q∩(ββ°))F(bagify°)α⊑F(bagify°)αR` #h(4pt) #src[(10.3)]],
  [the greedy condition, also in context],
  [`cost (xs⧺[j])=bmax (cost xs,penalty (perm xs,j))` \ `α cost=F(⟨cost,bagify⟩)k`, #h(4pt)
   `F(≤×𝟙)k⊑k≤` \ #src[Proposition 9.3]],
  [(10.2): `penalty` sums the completion times of `xs`, and a sum does not see the order],
  [`α cost=⟨g,h⟩ bmax` #h(4pt) #src[(10.4)] \ `g≜[zero,penalty]` #h(4pt) #src[(10.5)] \
   `h≜[zero,π₁ cost]` #h(4pt) #src[(10.6)]],
  [the cost of a schedule split into the penalty of its last job and the cost of the rest],
  [`add⊑π₁R` #h(6pt) #src[(10.7)] \ `β bagify°=F(bagify°) [nil,add]` #h(6pt) #src[(10.8)]],
  [adding a job never lowers the cost; and `bagify°` is itself a reduce on bags. Together:
   `β bagify°⊑F(bagify°)h≤cost°`],
  [`F(bagify)Q°F(bagify°)=g≥g°`, met by \ `Q≜f≤f°`, `f≜[zero,(bagify°×𝟙) penalty]`],
  [the specification `Q` has to satisfy, and the choice that meets it: a `Q`-minimum is a job of
   least penalty],
  [no greedy *reduce* exists],
  [a greedy snoc-list reduce would also solve every prefix of the input, and the best schedule
   of a prefix need not extend to a best schedule of the whole],
  [`X=(null→nil,` $frac(#[`snag°`], ∋)$ `min(Q) (X×𝟙) snoc)` #h(4pt) #src[Theorem 10.1, Proposition 10.1]],
  [`nil` and `snag` have disjoint ranges],
  [`schedule=(null→nil,pick (schedule×𝟙) snoc)` \ #src[`pick⊑` $frac(#[`snag°`], ∋)$ `min(Q)`, a partial
   function]],
  [the program: repeatedly remove a job of least penalty and put it last; quadratic in the number of
   jobs],
)]<tardy-laws>

== The TeX problem

// B&dM §10.4, p. 259.  The section's `h` is `⦇[arb, step]⦈`, which is `H°`, not §21.1's algebra `h`.
// The book prints the base case of `f` as `a < 0` on p. 262 and as `p ≤ 0` in the program.
#disp[#definition[
`intern≜val round : Decimal⟶[0,2¹⁶)`, #h(4pt) `val≜⦇[zero,shift]⦈`, #h(4pt)
`shift (d,r)=(d+r)/10`, #h(4pt) `round r` rounds `2¹⁶r` to the nearest integer:
`round r=n⟺2n−1<2¹⁷r<2n+1`.

`interval n=((2n−1)/2¹⁷,(2n+1)/2¹⁷)`, #h(4pt) `r inrange (a,b)⟺a<r<b`, #h(4pt)
`round°=interval inrange`, #h(4pt) `R≜length≤length°`.

`Interval` the pairs `(a,b)` with `0<b<1` and `a<b` #h(4pt) #src[(10.9)]; #h(4pt)
`[arb,step] : 1+(Digit×Interval)⟶Interval`, #h(4pt)
`step (d,(a,b))=((d+a)/10,(d+b)/10)`.

`FX=1+(Digit×X)`, #h(4pt) `α≜[nil,cons]`, #h(4pt) `h≜⦇[arb,step]⦈=H°`, #h(4pt)
`! : Digit×Interval⟶1`, #h(4pt) `Q≜(l°!°r)∪𝟙`, #h(4pt) `w≜2¹⁷`.
]]<tex-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`intern°`], ∋)$ `min(R)=interval` $frac(#[`inrange val°`], ∋)$ `min(R)`],
  [the specification: a shortest decimal whose internal representation is the given multiple of
   `2⁻¹⁶`. `round°` is not a map, but `interval` is, so it comes out of the $frac(#box(width: 8pt), ∋)$],
  [`val inrange°=⦇[arb,step]⦈` \ #src[fusion; `zero inrange°=arb`,
   `shift inrange°=(𝟙×inrange°) step`]],
  [the converse of `val`, cut down to intervals, is a reduce on cons-lists],
  [`F(R)α⊑αR`],
  [`cons` is monotonic on `R` — routine],
  [`α°F(h)Q°⊑R°α°F(h)`],
  [the greedy condition of Theorem 10.1, converted],
  [$frac(#[`arb°`], ∋)$ `(a,b)=(a<0→{*},{})` \
   $frac(#[`step°`], ∋)$ `(a,b)={(d,(10a−d,10b−d))∣0<10b−d<1}`],
  [the decompositions of an interval: stop, or take one more digit],
  [`0<10b−d₁<1` and `0<10b−d₂<1` imply `d₁=d₂`],
  [`step°` is in fact a map, `d` the digit with `0<10b−d<1`, so $frac(#[`[arb,step]°`], ∋)$ returns at
   most two elements and `Q` need only choose between them],
  [`Q≜(l°!°r)∪𝟙`, and `! nil⊑cons R°` \ #src[from `! nil length⊑cons length≥`]],
  [stop whenever stopping is legal: the empty decimal is shorter than any other],
  [`(μX :` $frac(#[`[arb,step]°`], ∋)$ `min(Q) F(X)α)⊑` $frac(#[`intern°`], ∋)$ `min(R)` #h(4pt) #src[Theorem 10.1]],
  [greedy: emit the one digit the interval allows, until the interval contains zero],
  [`extern=interval f` \ `f(a,b)=(a<0→[],[d]⧺f(10a−d,10b−d))`],
  [the program, with `d` the digit above],
  [`extern n=f(2n−1,2n+1)` \
   `f (p,q)=(p≤0→[],[d]⧺f (10p−w d,10q−w d))` \ #src[`d=(10q) div w`, `w=2¹⁷`]],
  [the same in integer arithmetic only, as chapter 3 required of `intern`: every interval reached is
   `(p/w,q/w)`],
)]<tex-laws>

#pagebreak(weak: true)
#include "allegory-appendix.typ"
