// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name (see circuit.typ's header); `dot` is renamed on the way in for that reason.
#import "circuit.typ": conv, meet, wire, bend, gbox, dot as wiredot, tape, tape-fork, tape-join, TINT
// draw.typ owns the Hinze–Marsden geometry (Catamorphism, Monad) and every helper this note draws with:
// it is also the standalone PNG of those laws, and one geometry drawn in two files is one that drifts.
#import "draw.typ": homeq, beadeq, twobeadeq, TCOL, BCOL, CCOL, monadops, monadunit, monadassoc, stateops, unitlaw, GIVEN1, GIVEN2, INDUCED, SLACK, ADMIRES, HATES, WORKS, ADMIRERS, HATERS, PEOPLE, LX, BD, LY, lab, ar, node, nodes, ings, edges, arc, head, e, syqnode, syqedge, domstr, pairstr, zw, zsq, zsqc, zstep, znamed, zderiv, zline, zpair, skel, yset, capbox, pair, blocked
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
#import "generated/Freyd.Diag.SingleValued.typ": pic as p-sv46
#import "generated/Freyd.Diag.Total.typ": pic as p-tot47
#import "generated/Freyd.Diag.Injective.typ": pic as p-inj48
#import "generated/Freyd.Diag.Surjective.typ": pic as p-sur49
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
  table.header([*`F ⊣ G`*], [*`F`'s type*], [*monad `FG`*], [*`𝟙⊑FG`*], [*`GF⊑𝟙`*], [*`F` preserves `∪`*], [*`G` preserves `∩`*], [*`FGF=F`*], [*`GFG=G`*]),

  [`◁ ⊣ ▷`], [`A ⟶` \ `A⊗A`], [`◁▷=𝟙`], [`𝟙⊑◁▷`], [`▷◁⊑𝟙`], [`(R∪S)◁=` \ `R◁∪S◁`], [`(R∩S)▷=` \ `R▷∩S▷`], [`◁▷◁=◁`], [`▷◁▷=▷`],

  [`⊸ ⊣ ⟜`], [`A ⟶ 𝕀`], [`⊸⟜=⊤`], [`𝟙⊑⊸⟜`], [`⟜⊸⊑𝟙`], [`(R∪S)⊸=` \ `R⊸∪S⊸`], [`(R∩S)⟜=` \ `R⟜∩S⟜`], [`⊸⟜⊸=⊸`], [`⟜⊸⟜=⟜`],

  [`° ⊣ °`], [`(A⟶B) ⟶` \ `(B⟶A)`], [`°°=𝟙`], [`R=R°°`], [`R=R°°`], [`(R∪S)°=` \ `R°∪S°`], [`(R∩S)°=` \ `R°∩S°`], [`R°°°=R°`], [`R°°°=R°`],

  [`⟜◁ ⊣ ▷⊸`], [`(X⊗A ⟶ Y) ⟶` \ `(X ⟶ Y⊗A)`], [`𝟙`], [`(⟜◁⊗𝟙)` \ `(𝟙⊗▷⊸)=𝟙`], [`(𝟙⊗⟜◁)` \
    `(▷⊸⊗𝟙)=𝟙`], [`=`], [`=`], [`=`], [`=`],

  // An iso is an adjunction BOTH WAYS, so the bend gets a row in each direction; the pair differs
  // only by swapping columns 4/5, which is what makes the last four columns bare equalities.
  [`▷⊸ ⊣ ⟜◁`], [`(X ⟶ Y⊗A) ⟶` \ `(X⊗A ⟶ Y)`], [`𝟙`], [`(𝟙⊗⟜◁)` \ `(▷⊸⊗𝟙)=𝟙`], [`(⟜◁⊗𝟙)` \
    `(𝟙⊗▷⊸)=𝟙`], [`=`], [`=`], [`=`], [`=`],

  [`Δ ⊣ ∩`], [`(A⟶B) ⟶` \ `(A⟶B)²`], [`R↦R∩R=R`], [`R⊑R∩R`], [`R∩S⊑R`], [`Δ(R∪S)=` \ `ΔR∪ΔS`], [`(R∩T)∩(S∩U)=` \ `(R∩S)∩(T∩U)`], [`R∩R=R`], [`R∩R=R`],

  [`∪ ⊣ Δ`], [`(A⟶B)² ⟶` \ `(A⟶B)`], [`(R,S)↦` \ `(R∪S,R∪S)`], [`R⊑R∪S`], [`R∪R⊑R`], [`(R∪T)∪(S∪U)=` \ `(R∪S)∪(T∪U)`], [`Δ(R∩S)=` \ `ΔR∩ΔS`], [`R∪R=R`], [`R∪R=R`],

  [`⊥ ⊣ !`], [`{*} ⟶` \ `(A⟶B)`], [—], [—], [`⊥⊑R`], [—], [—], [—], [—],

  [`·S ⊣ /S`], [`(A⟶B) ⟶` \ `(A⟶C)`], [`S/S`], [`R⊑(RS)/S`], [`(T/S)S⊑T`], [`(R∪T)S=` \ `RS∪TS`], [`(R∩T)/S=` \ `R/S∩T/S`], [`((RS)/S)S` \ `=RS`], [`((T/S)S)/S` \ `=T/S`],

  [`S· ⊣ S\`], [`(B⟶C) ⟶` \ `(A⟶C)`], [`S\S`], [`R⊑S\(SR)`], [`S(S\T)⊑T`], [`S(R∪T)=` \ `SR∪ST`], [`S\(R∩T)=` \ `S\R∩S\T`], [`S(S\(SR))` \ `=SR`], [`S\(S(S\T))` \ `=S\T`],

  [`R∩ ⊣ R⇒`], [`(A⟶B) ⟶` \ `(A⟶B)`], [`X↦R⇒(X∩R)`], [`X⊑R⇒(X∩R)`], [`R∩(R⇒Y)⊑Y`], [`R∩(X∪Y)=` \ `(R∩X)∪(R∩Y)`], [`R⇒(X∩Y)=` \ `(R⇒X)∩(R⇒Y)`], [`R∩(R⇒(X∩R))` \ `=X∩R`], [`R⇒(R∩(R⇒Y))` \ `=R⇒Y`],

  [`𝓓 ⊣ ·⊤`], [`(A⟶B) ⟶` \ `Cor A`], [`R↦(𝓓R)⊤`], [`R⊑(𝓓R)⊤`], [`𝓓(A⊤)⊑A`], [`𝓓(R∪S)=` \ `𝓓R∪𝓓S`], [`(A∩B)⊤=` \ `A⊤∩B⊤`], [`𝓓((𝓓R)⊤)` \ `=𝓓R`], [`(𝓓(A⊤))⊤` \ `=A⊤`],

  [`𝓡 ⊣ ⊤·`], [`(A⟶B) ⟶` \ `Cor B`], [`R↦⊤(𝓡R)`], [`R⊑⊤(𝓡R)`], [`𝓡(⊤A)⊑A`], [`𝓡(R∪S)=` \ `𝓡R∪𝓡S`], [`⊤(A∩B)=` \ `⊤A∩⊤B`], [`𝓡(⊤(𝓡R))` \ `=𝓡R`], [`⊤(𝓡(⊤A))` \ `=⊤A`],

  [`·f ⊣ ·f°`], [`(A⟶B) ⟶` \ `(A⟶C)`], [`ff°`], [`𝟙⊑ff°`], [`f°f⊑𝟙`], [`(R∪S)f=` \ `Rf∪Sf`], [`(R∩S)f°=` \ `Rf°∩Sf°`], [`ff°f=f`], [`f°ff°=f°`],

  [`f°· ⊣ f·`], [`(A⟶C) ⟶` \ `(B⟶C)`], [`ff°`], [`𝟙⊑ff°`], [`f°f⊑𝟙`], [`f°(X∪Y)=` \ `f°X∪f°Y`], [`f(X∩Y)=` \ `fX∩fY`], [`ff°f=f`], [`f°ff°=f°`],

  [`i ⊣ E`], [`Map ↪ Rel`], [`E`], [$frac(#[`𝟙`], ∋)$`:A⟶E A`], [`∋:E B⟶B`], [—], [—], [$frac(#[`∋`], ∋)$`=𝟙`], [$frac(#[`R`], ∋)$`∋=R`],

  // The row above at the HOM-SET level, and the table's only bijection that is not an ORDER-iso:
  // `%∋` is not monotone, and monotone would force every hom-poset discrete.
  [`·∋ ⊣` $frac(#box(width: 8pt), ∋)$], [`Map(A,E B) ⟶` \ `(A⟶B)`], [`𝟙`], [$frac(#[`f∋`], ∋)$`=f`], [$frac(#[`R`], ∋)$`∋=R`], [—], [—], [$frac(#[`f∋`], ∋)$`∋` \ `=f∋`], [$frac(#[$frac(#[`R`], ∋)$`∋`], ∋)$ \ `=`$frac(#[`R`], ∋)$],

  [$frac(#box(width: 8pt), ∋)$ `⊣ ·∋`], [`(A⟶B) ⟶` \ `Map(A,E B)`], [`𝟙`], [$frac(#[`R`], ∋)$`∋=R`], [$frac(#[`f∋`], ∋)$`=f`], [—], [—], [$frac(#[$frac(#[`R`], ∋)$`∋`], ∋)$ \ `=`$frac(#[`R`], ∋)$], [$frac(#[`f∋`], ∋)$`∋` \ `=f∋`],
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
  zsqc(`f° X`, `R/T`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·T⊣/T`],
  zsqc(`(f° X) T`, `R`),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[associativity],
  zsqc(`f°(X T)`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc(`X T`, `f R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·T⊣/T`],
  zsqc(`X`, `(f R)/T`),
)
#zline(
  zstep(under: true)[indirect equality],
  zsqc(`f(R/T)`, `(f R)/T`, eq: true),
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
    [`(S\Y)°=` \ `Y°/S°`], [`((S⊗𝟙)R)^=` \ `S R^`],
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

  [*`⟜◁`*], [`(RT)^=` \ `R^(T⊗𝟙)`], [`((T⊗𝟙)R)^=` \ `T R^`], [—], [—], [—],
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

Beyond `∪ ⊣ Δ ⊣ ∩`, which §@sec-adj already carries as two rows, the table holds one adjoint triple with
content: `∃_f ⊣ f* ⊣ ∀_f` along a map `f`, once on each side of the composite.
#src[`f : A ⟶ B` throughout this subsection.]

#disp[#block(inset: (y: 6pt))[
  `·f ⊣ ·f° ⊣ /f°` \
  `f°· ⊣ f· ⊣ f\`
]]<triple-chains>

// `map_shunt_right`, AOP/A4_2.lean:223; `map_shunt_left`, AOP/A4_2.lean:241.
The first two links of each chain are the map shunting rules, and the third is §@sec-adj's division row read at a chosen divisor: `·S ⊣ /S` at `S := f°`, and
`S· ⊣ S\` at `S := f`.

The third link is not the first over again. For a map `f`, `/f` collapses to `·f°`; being a map is
exactly what that collapse spends
// `div_comp_recip_map`, AOP/A4_4.lean:378.
#src[`R/(f S) = (R/S) f°`.] — `f°` is not a map, so
`/f°` does not collapse in turn, and the three operators stay distinct. On `Rel(𝕀, A) = E A` they
are the image triple:

#disp[#table(
  columns: 3, align: left + horizon, inset: 4pt, stroke: 0.4pt + luma(190),
  table.header([*operator*], [*acts by*], [*name*]),
  [`·f`], [`S ↦ f[S]`], [direct image, `∃_f`],
  [`·f°`], [`T ↦ f⁻¹[T]`], [inverse image, `f*`],
  [`/f°`], [`S ↦ {b : f⁻¹(b) ⊆ S}`], [`∀_f`],
)]<triple-image>

§@sec-adj's `𝓓 ⊣ ·⊤` is this same chain along the projection `A⊗B ⟶ A`, read through
`Rel(A, B) = E(A⊗B)`: `𝓓R = {(a,a) : ∃b. aRb}`, `A⊤` is the relation that ignores `b`
altogether, and the third link is `R ↦ 𝟙 ∩ R/⊤ = {(a,a) : ∀b. aRb}`.

#disp[#block(inset: (y: 6pt))[`𝓓 ⊣ ·⊤ ⊣ 𝟙∩·/⊤`]]<triple-dom>

Three is where it stops, and one map breaks both ends. Take `A = {a₁,a₂}` and `B = {b}`:
`f[{a₁}] ∩ f[{a₂}] = {b}` while `f[{a₁} ∩ {a₂}] = ∅`, so `·f` does not preserve meets and has no
left adjoint, and the same two subsets give `∀_f({a₁} ∪ {a₂}) = {b}` against
`∀_f{a₁} ∪ ∀_f{a₂} = ∅`, so `/f°` does not preserve joins and has no right adjoint. A monic `f`
restores the binary case and no more — `⊤f` still reaches only `im f`, and `∀_f⊥ = B ∖ im f` is
still not `⊥`. The chain extends only when `f°` is a map as well, and then `/f° = ·f°° = ·f` and it
repeats forever. For an `S` with neither `S` nor `S°` a map there is no triple at all: `·S ⊣ /S` is
two links and stops.

#src[The rows that chain forever say nothing by it: `°` is an order-isomorphism of hom-posets, so it
is adjoint to itself on both sides and `° ⊣ ° ⊣ °` has no end, and §@sec-adj's other row of that kind,
`⟜◁ ⊣ ▷⊸`, goes the same way.]

#pagebreak(weak: true)
= Relations

#disp[#definition[
Rel is a poset-enriched category with ($times.o$, °) where $times.o$ is commutative cartisian product, and converse `° ⊣ °`, and

  #align(center, block(inset: (y: 6pt))[
    #src[C:] `(▷ : A ⊗ A ⟶ A, ⟜ : 𝕀 ⟶ A)` a commutative monoid with `C° ⊣ C`.
    We write `C°` as `(◁ : A ⟶ A ⊗ A, ⊸ : A ⟶ 𝕀)`
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
  [#P(p-lax-delta, s: 60%) #v(-7pt) \ #src[`R◁ ≤ ◁(R⊗R)`]],
  [#P(p-lax-bang, s: 60%) #v(-7pt) \ #src[`R⊸ ≤ ⊸`]],
)]<rel-monoid>

== $forall$ object A, `(A, ◁, ⊸) ⊣ (A, ▷, ⟜)`

#disp[#grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-37, s: 52%) #v(-7pt) \ #src[`▷ ◁ ≤ 𝟙`]],
  [#P(p-38, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ◁ ▷`]],
  [#P(p-39, s: 52%) #v(-7pt) \ #src[`⟜ ⊸ ≤ 𝟙`]],
  [#P(p-40, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ⊸ ⟜`]],
)]<rel-adj>

The last of these is the only one that makes a picture *bigger*, and it is worth a name: *a wire is
below the cut wire*. In `Rel` it reads `{(a, a)} ⊆ A × A` — cut a wire and its two ends stop having
to agree, so cutting can only add pairs. It is the one weakening this calculus gives away for free.


#pagebreak(weak: true)
= ° : 𝒞ᵒᵖ ⟶ 𝒞 is a 2 functor 

#disp[#definition[
`°` is primitive, part of the data the first section lists. It turns both of `R`'s wires round, and
the Frobenius structure DRAWS that — the picture and the formula below are `R°`, not its definition:

#fig({ conv((0, -0.80), $R$) })

#align(center, block(inset: (y: 4pt))[#text(12.5pt)[`R° = (⟜◁ ⊗ 𝟙) (𝟙 ⊗ R ⊗ 𝟙) (𝟙 ⊗ ▷⊸)`]])

where `⟜◁ : 𝕀 ⟶ a ⊗ a` opens a pair of wires out of nothing and `▷⊸ : b ⊗ b ⟶ 𝕀` closes one, so
the input of `R°` is where the output of `R` was.  Taking that formula as the definition would now
be circular: `◁` and `⊸` are `▷°` and `⟜°`.  The laws of `°` are that it is a contravariant
2-functor `° : 𝒞ᵒᵖ ⟶ 𝒞`:

#align(center, block(inset: (y: 5pt))[
  (i) `𝟙° = 𝟙`  #h(1cm) (ii) `(R S)° = S° R°`  #h(1cm) (iii) `(R ⊗ S)° = R° ⊗ S°`
  #h(1cm) (iv) `R ≤ S` implies `R° ≤ S°`
])
]]<conv-defn>

== The slide

The one rule (ii) and (iii) use, and each of them uses it twice. A converse facing a merge on the
lower strand is the box itself, upright, on the upper one:

#disp[#P(p-conv-slide, s: 62%)]<conv-slide>

`R°` is DEFINED as the bending of `(R ⊗ 𝟙) ▷⊸`, so the slide claims only that unbending it gives
that back — and unbending undoes bending for every arrow. That is the snake above with a passenger:
the `⟜◁` bends the `a` strand down and the `▷⊸` brings it back up, while the `b` strand rides
through untouched. Nothing else is spent below.


#pagebreak(weak: true)
= `∩` is a commutative idempotent monoid on every hom-set

#disp[#definition[
The *meet* of `R, S : a ⟶ b`, the paper's *convolution*, is `R ∩ S := ◁ (R ⊗ S) ▷` — copy the
input, run `R` and `S` on the two copies, merge the results — so what comes out is what both of them
do.

#fig({ meet((0, 0), $R$, $S$) })
#align(center, src[transcribed: a definition has no statement to export])

On every hom-set it is associative, commutative and idempotent, with unit the maximal arrow
`⊤ = ⊸ ⟜` #src[(the paper's Lemma 4.11)].
]]<meet-defn>

#disp[#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-meet-top, s: 60%) #v(-7pt) \ #src[*unit:* one half of `⊤` per end — the merge's unit law
   absorbs the `⟜`, the copy's counit law the `⊸`]],
  [#P(p-meet-comm, s: 60%) #v(-7pt) \ #src[*commutative:* `σ` crosses `R ⊗ S` by naturality and is
   absorbed by cocommutativity and commutativity]],
  [#P(p-meet-assoc, s: 44%) #v(-7pt) \ #src[*associative:* coassociativity and associativity; `⊗`
   re-brackets for nothing, being strict here]],
  [#P(p-meet-idem, s: 60%) #v(-7pt) \ #src[*idempotent:* the one that is not bookkeeping — the lax
   copy law is the whole of it, worked in allegory2]],
)]<meet-laws>

So `≤` is the order this monoid induces. `R ∩ S ≤ R` comes from the unit, and idempotency turns
anything under both `S` and `T` into something under `S ∩ T`, since `R = R ∩ R ≤ S ∩ T`.

And one law relating `∩` to composition, which is *not* an equation:

#disp[#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*semi-distributivity, and what supplies it*], [*picture*]),

  [`R (S ∩ T) ⊑ R S ∩ R T` — the lax copy law. #src[Equality exactly when `R` is single valued: the Maps section's
   `F (R ∩ S) = F R ∩ F S`.]], P(p-semidistrib),
)]<meet-semidistrib>

#pagebreak(weak: true)
= Domain and range

#disp[#definition[
The *domain* `Dom R ≜ 𝟙 ∩ R R°` and the *range* `Ran R ≜ Dom R°`.
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
   so `R° ▷` cuts to `⊸` — Frobenius]), s: 100%)]<dom-collapse>

Running `R` and throwing the result away leaves only the fact that `R` could fire, and `Ran R` is the
same picture with the box mirrored. In `Rel` both steps are `{(a,a) : ∃b. a R b}`.

#disp[#table(
  columns: 1, inset: 9pt, stroke: 0.4pt + luma(190),

  [`Dom R ≜ 𝟙 ∩ R R°`],
  [`Dom R ⊑ A ⟺ R ⊑ A R`, for `A` coreflexive],
  [`Dom (R S) ⊑ Dom R`],
  [`Dom (R ∩ S) = 𝟙 ∩ S R°`],
  [`R` entire `⟺ Dom R = 𝟙 ⟺ 𝟙 ⊑ R R°`],
  [`R` simple `⟺ R° R ⊑ 𝟙`],
  [`R` a map `⟺ R` entire and simple],
  [`R, S` entire `⟹ R S` entire — likewise simple, likewise maps],
  [`R S` entire `⟹ R` entire],
)]<dom-laws>

== Sliding the discard

`Dom (R S) ⊑ Dom R`, and a single glyph for `Dom` would have nothing to slide: with the box and the
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
  ("", [`S ⊸ ⊑ ⊸`, the lax axiom for `⊸` in the first section \
   — the discard slides back past `S`]), s: 100%)]<dom-slide>

Equality is `S` entire, which is the same picture read as `Dom R = 𝟙 ⟺ R` entire.

#pagebreak(weak: true)
= Maps

Every arrow is lax for `◁` and for `⊸` by axiom, and for `▷` and `⟜` by taking `°` of those two. All four
hold for *every* arrow, their REVERSES do not, and each reverse holding is a property of the arrow.
The right-hand column is the *adjoint* form, which is the definition
used here because it is literally the allegory's `Simple` and `Entire`; that the two forms agree is
a separate theorem, not proved here.

// A 2×2, not a list of four: the ROW says which composite (`R° R`, `R R°`), the COLUMN which way the
// containment runs, so each property's opposite is the cell diagonally across.  Name under picture.
#disp[#table(
  columns: (1fr, 1fr),
  align: center + horizon,
  inset: 10pt, stroke: 0.4pt + luma(190),

  [#P(p-sur49, s: 74%) #v(-4pt) *surjective* \ #src[`𝟙 ⊑ R° R`, that is, `R°` entire.]],
  [#P(p-sv46, s: 74%) #v(-4pt) *single valued* \ #src[`R° R ⊑ 𝟙`]],

  [#P(p-tot47, s: 74%) #v(-4pt) *entire* \ #src[`𝟙 ⊑ R R°`. With *single valued*, a *map*.]],
  [#P(p-inj48, s: 74%) #v(-4pt) *injective* \ #src[`R R° ⊑ 𝟙`]],
)]<map-square>

#disp[#table(
  columns: (1fr, 2.2fr),
  align: (center + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*picture*]),

  [`F (R ∩ S) = F R ∩ F S` \ #v(2pt) #src[`F` single valued] \ #v(6pt)
   #src[`F` = people `x` may ask, `R` = admires `a`, `S` = admires `b`. Single valued means one person,
   so the sides agree.]],
  grid(columns: 3, align: horizon, column-gutter: 10pt,
    [#P(p-236a, s: 74%) #v(-9pt) #align(center, src[one person who admires both])],
    text(17pt)[=],
    [#P(p-236b, s: 74%) #v(-9pt) #align(center, src[`a` at A, `b` at B])],
  ),
)]<map-meet>

#pagebreak(weak: true)
= `/` is all of

#disp[#definition[
#align(center, `x (R/S) y  ⟺  ∀p. y S p → x R p`)
#align(center, `x (S\R) y  ⟺  ∀p. p S x → p R y`)
#align(center, `/ compares images: S(y) ⊆ R(x).   \ compares preimages: S°(x) ⊆ R°(y).`)
#align(center, `example: A admires, H hates, W works for`)
#align(center, `x (A/H) y — x admires everyone y hates.`)
#align(center, `x (H\A) y — everyone who hates x admires y.`)
]]<div-defn>


== `(R/S)(S/W) ⊑ R/W`


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
#box[`(R/S)(S/W) ⊑ R/W`].

// One law per row, and the picture column takes the rest of the 22cm: `le_div_iff` is a `⟺` between
// two containments, four sub-pictures wide (10.9cm before scaling), the widest picture in the note.
#disp[#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`X ⊑ R/S ⟺ X S ⊑ R` \ #src[`X` is any `x`-to-`y` pairing; one that only pairs `x` with a `y`
   such that `x` admires everyone `y` hates lies inside `R/S`, and `R/S` is the largest such.]],
  P(p-le-div),

  [`X ⊑ S\R ⟺ S X ⊑ R` \ #src[The mirror — divide on the left when `x` comes first.]],
  P(p-le-ldiv),

  [`(R/S) S ⊑ R` \ #src[There is a `y` such that `x` admires everyone `y` hates, and `p` is one of
   the people `y` hates — then `x` admires `p` too. Strict at `S = ∅`: `R/S` is everyone, `(R/S) S = ∅`.]],
  P(p-div-cancel),

  [`S (S\R) ⊑ R` \ #src[The mirror.]],
  P(p-ldiv-cancel),

  [*associate:* `R/(S₁ S₂) = (R/S₂)/S₁` \ #src[*A friend's enemy* is two hops: divide by the far end
   first.]],
  P(p-div-assoc),

  [`(S₁ S₂)\R = S₂\(S₁\R)` \ #src[The mirror.]],
  P(p-ldiv-assoc),

  [*maps:* `f (R/S) = (f R)/S` \ #src[Rename `x` before or after dividing — the licence to write
   `f R / S`.]],
  P(p-map-div),

  [`R/(f S) = (R/S) f°` \ #src[Rename `y`: a map leaves a denominator as `f°` outside the box.]],
  P(p-div-map),

  [`(R/S)(S/W) ⊑ R/W` \ #src[Someone who admires all of a hate-set that already covers everyone
   `z` works for admires those people too.]],
  P(p-div-comp),

  [`𝟙 ⊑ R/R` \ #src[`R/R` runs admirer to admirer: each admires everyone they admire. Strict: two
   people who each admire only `a` and `b` admire each other's idols too, and still stay two people.]],
  P(p-one-div),

  [`(R/R)(R/R) = R/R` \ #src[`R/R` is the preorder *admires at least as much as*, and a preorder is
   idempotent. Freyd writes `⊑`; with `𝟙 ⊑ R/R` above it is an equality.]],
  P(p-div-self-idem),

  [`(R/R) R = R` \ #src[Reaching `p` through someone whose idols `x` fully admires is reaching `p`
   directly, since `x` admires their own idols.]],
  P(p-div-self),

  [`R/𝟙 = R` \ #src[Dividing by `𝟙`: `p`'s set is just `{p}`, so admiring all of it is admiring `p`.]],
  P(p-div-one),

  [`R/(S₁ ∪ S₂) = R/S₁ ∩ R/S₂` \ #src[Admiring a combined hate-set is admiring each set in full.]],
  P(p-div-union),

  [`S\(R/W) = (S\R)/W` \ #src[Which is why `S\R/W` needs no bracket.]],
  P(p-ldiv-div),
)]<div-laws>

Fifteen laws, fifteen pictures, and not one shows a generator: `∩`, `∪`, `°` and composition are what
the Frobenius generators build, and `/` is none of those — it is posited, with nothing to unfold.

#pagebreak(weak: true)
= $frac(R, S)$

#disp[#definition[
$frac(R, S)$ `≜ (R/S) ∩ (S/R)°`. In `Rel` `x` and `y` has the same image:
`∀p. (x R p ⟺ y S p)`
]]<syq-defn>

// The meet read one factor at a time, in the vocabulary of the section above: `/` supplies ALL, the
// converse of the mirror division supplies ONLY, and the meet is what names this section.
#disp[#block(inset: (top: 2pt), text(10.5pt)[
  `x (A/H) y` — `x` admires everyone `y` hates \
  `x ((H/A)°) y` — `x` admires only people `y` hates \
  `x ((A/H) ∩ (H/A)°) y` — `x` admires only and all whom `y` hates
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

  [$X ⊑ frac(R, S) ⟺ X S ⊑ R$ and `X° R ⊑ S`],
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
   `y = x always qualifies (𝟙 ⊑ R%R below)`],

  [$𝟙 ⊑ frac(R, R)$],
  [$x (frac(R, R)) y$ if `x` and `y` admires the same peoples.],

  [$(frac(R, R))^2 = frac(R, R)$],
  [So the relation *admires the same people* is an equivalence relation.],

  [$X ⊑ frac(R, R) ⟺ X R ⊑ R$, for symmetric `X`],
  [The largest symmetric arrow that leaves `R` alone.],

  [$frac(R, 𝟙)$ is the *simple part* of `R`],
  [The people who admire exactly one person and nobody else. It equals `R` only when `R` is simple, unlike
   `R/𝟙 = R`.],

  [`Dom` $frac(R, S)$ `= 𝟙 ∩ (R/S)(S/R)`],
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

`R □` is `R`'s target, an identity arrow. For `R : A ⟶ B` write `∋ : E B ⟶ B`, dropping the
subscript.

// The converse of epsiloff IS membership, and the note's pointwise glosses already write it `∈`.
`∈ ≜ ∋° : A ⟶ E A`
]]<pow-defn>

#disp[
  // Row numbers so a law can be cited: `it.y` is the table's OWN index, so deleting a row renumbers
  // the rest.  Rebuilt as a cell, not returned bare — bare content loses the row's height.
  #show table.cell.where(x: 0): it => if it.y == 0 or it.body.func() == grid { it } else {
    let f = it.fields()
    let _ = f.remove("body")
    table.cell(..f, grid(columns: (0.55cm, 1fr), text(9pt, luma(140))[#it.y], it.body))
  }
  #table(
  columns: (7.95cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [$#e[R] □ = R □$, #h(4pt) $#e[R] = #e[R □]$],
  [One `∋` per object, not per arrow.],

  [`∋` is *thick*],
  [*Comprehension*: every `x` has a set of exactly the people `x` admires.],

  [$frac(R, ∋)$ ` : A ⟶ E B`, for `R : A ⟶ B` ],
  [convert a relation to a function. `a` $frac(R, ∋)$ ` = {b|a R b}` ],
  [$frac(#[`R`], ∋)$ is a *map*],  [],

  [$frac(#[`R`], ∋)$ `∋ = R` ], [],

  [`F ⊑` $frac(#[`F ∋`], ∋)$, `F` simple],
  [A partial choice of sets is inside the total one.],

  [$frac(#[`𝟙`], ∋)$, the *singleton map*, monic],
  [The one-person set.],

  [$frac(#[`∋`], ∋)$ `= 𝟙`],
  [Make the set of a set, then read it back one level down.],

  [*fusion:* $frac(#[`f R`], ∋)$ `= f` $frac(#[`R`], ∋)$, `f` a map],
  [Naturality of the unit, `f` $frac(#[`𝟙`], ∋)$ `=` $frac(#[`𝟙`], ∋)$ `(E(f))`.],

  [$frac(#[`f`], ∋)$ `= f` $frac(#[`𝟙`], ∋)$, `f` a map],
  [Rename first or take singletons first — the fusion row above at `R = 𝟙`.],

  [$frac(R, S) = frac(R, ∋) (frac(S, ∋))^circle.small$],
  [`x` and `y` match when `R` sends `x` and `S` sends `y` to the same set.],

  [`E(R) ≜` $frac(#[`∋ R`], ∋)$, `E ≜` $frac(#[`∋·`], ∋)$], [`E(R): E A ⟶ E B`, image of a set of A],
  [$frac(#[`R`], ∋)$ `=` $frac(#[`𝟙`], ∋)$ `E(R)`], [$frac(#[`𝟙`], ∋)$`: x ↦ {x}` ],
  [$frac(#[`S`], ∋)$ `E(R) =` $frac(#[`S`], ∋)$ $frac(#[`∋ R`], ∋)$ `=` $frac(#[`S R`], ∋)$],
  [absorption ],

  [`subset ≜ ∋/∋ : E A ⟶ E A`],
  [`xs subset ys ⟺ ∀a. ys ∋ a → xs ∋ a`, that is `ys ⊆ xs`, not `xs ⊆ ys`.],
)]<pow-laws>

== `i ⊣ E` Power Allegory defined as adjunction <sec-adj-E>

// The factorisation the whole adjunction is about, drawn once.  Middle arrow is `E(R)`, NOT `P(R)`:
// the two agree on maps only (B&dM p. 119), and `{·} P(R)` is every nonempty subset of `R(a)`.
#disp[#box(inset: (y: 10pt), cetz.canvas(length: 0.8cm, {
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
    #text(8.5pt)[`E =` $frac(#[`∋·`], ∋)$]]]
  lab(xB + 0.35, 0, GIVEN2)[`∋`]
  lab(1.25, 0.2, INDUCED)[$frac(#[`R`], ∋)$]
  node(xA, T, black, `A`); node(xB, T, black, `B`)
  node(xA, B, black, `E A`); node(xB, B, black, `E B`)
}))
#align(center, block(inset: (y: 4pt))[
  $frac(#[`R`], ∋)$ `∋ = R` #h(1.4cm)
  #src[`E A` is the powerset of `A`. B&dM write `P A` — standard mathematics, but here `P` is
  already the relator `P(R)`.]
])]<adj-E-bend>

= Relator

#disp[#definition[
Every hom-set of an allegory is a poset, so an allegory is a *locally posetal 2-category*: the 2-cell
from `R` to `S` IS `R ⊑ S`. A *relator* `F : 𝒞 ⟶ 𝓓` is a 2-functor between allegories:

  #align(center, block(inset: (y: 6pt))[
    #text(12.5pt)[`F(𝟙) = 𝟙` #h(1cm) `F(R S) = F(R) F(S)` #h(1cm) `R ⊑ S ⟹ F(R) ⊑ F(S)`]
  ])

Preserving `°` is *not* asked for — `°` is an identity-on-objects involution `𝒞ᵒᵖ ⟶ 𝒞`, no part of
the 2-category.
]]<relator-defn>

#disp[#table(
  columns: (1fr, 5.2cm),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the statement*], [*B&dM*]),

  [For `f` a map, `F(f)` is a map and `F(f°) = F(f)°`.], [Lemma 5.1],
  [Over a *tabular* allegory a functor is a relator `⟺` it preserves `°`.], [Theorem 5.1],
  [`F(R°) = F(R)°` for every `R`, so `F(R)°` needs no bracket.], [after Theorem 5.1, p. 113],
  [Two relators agreeing on maps are equal.], [Corollary 5.1],
  [`F(X ∩ Y) = F(X) ∩ F(Y)` for `X, Y` coreflexive.], [Ex 5.2],
  [`F(R ∩ S) ⊑ F(R) ∩ F(S)`, and strictly.], [Ex 5.2, the restriction],
  [`F(Dom R) = Dom(F(R))` for `F` preserving `°`.], [—],
)]<relator-laws>

The *power relator* `P` — `xs P(R) ys ⟺ (∀a ∈ xs. ∃b ∈ ys. a R b) ∧ (∀b ∈ ys. ∃a ∈ xs. a R b)` — is where
the fourth is strict: for `R = {(a₁,b₁), (a₂,b₂)}` and `S = {(a₁,b₂), (a₂,b₁)}` the pair
`({a₁,a₂}, {b₁,b₂})` is in `P(R) ∩ P(S)`, while `R ∩ S = ∅`.

= Fork `⟨R,S⟩`

#disp[#definition[
The *fork* of `R : C ⟶ A` and `S : C ⟶ B` is `⟨R,S⟩ ≜ R π₁° ∩ S π₂°`, where `(π₁, π₂)` is the
tabulation of `⊤`.
]]<fork-defn>

#disp[#block(inset: (y: 6pt))[
  `⟨R,S⟩ π₁ = (Dom S) R` #h(1.4cm) `⟨R,S⟩ π₂ = (Dom R) S`
]]<fork-proj>

#disp[#row((box(inset: (right: 18pt), cetz.canvas(length: 0.8cm, {
  let (C, A, B, P) = ((-3, 0), (0, 1.7), (0, -1.7), (3, 0))
  ar(C, A, GIVEN1); ar(C, B, GIVEN2); ar(P, A, GIVEN1, s0: 0.75); ar(P, B, GIVEN2, s0: 0.75)
  ar(C, P, INDUCED, dash: "dashed", s1: 0.95)
  lab(-1.75, 1.12, GIVEN1)[`R`]; lab(-1.75, -1.12, GIVEN2)[`S`]
  lab(1.8, 1.12, GIVEN1)[`π₁`]; lab(1.8, -1.12, GIVEN2)[`π₂`]
  lab(-1.0, 0.32, INDUCED)[$chevron.l R, S chevron.r$]
  lab(1.1, 0.5, SLACK, rot: -135deg)[`⊑`]; lab(1.1, -0.5, SLACK, rot: 135deg)[`⊑`]
  node(C.at(0), C.at(1), black, $C$)
  node(A.at(0), A.at(1), GIVEN1, $A$); node(B.at(0), B.at(1), GIVEN2, $B$)
  node(P.at(0), P.at(1), INDUCED, $A times B$)
})), pairstr()))]<fork-pic>

A domain is coreflexive, so `⟨R,S⟩ π₁ ⊑ R`, with equality exactly when `S` is entire; for maps both
triangles commute and `⟨f,g⟩` is unique. In `Rel`, `c ⟨R,S⟩ (a,b)` iff `c R a` and `c S b` — copy `c`, then
`R` on one strand and `S` on the other, which is `◁ (R ⊗ S)` on the right.

No `°` survives the translation. `π₁ = 𝟙 ⊗ ⊸` discards the second component, so `π₁° = 𝟙 ⊗ ⟜`
*creates* one out of nothing, and `∩` is copy, run both, merge. Draw that and the created strands —
the two dots with no left end, and the crossing they force — are merged against real ones, which is
the monoid's unit law:

// The chain at FULL size: `chain`'s 62% is calibrated for the exported pictures, which are drawn on a
// bigger canvas than these two.
#disp[#chain((cetz.canvas(length: 0.8cm, {
  wire((0, 0), (0.8, 0)); wiredot((0.8, 0))
  bend((0.8, 0), (1.4, 1.5)); bend((0.8, 0), (1.4, -1.5))
  wire((1.4, 1.5), (1.6, 1.5)); gbox((1.6, 1.5), [R]); wire((2.52, 1.5), (3.3, 1.5))
  wire((1.4, -1.5), (1.6, -1.5)); gbox((1.6, -1.5), [S]); wire((2.52, -1.5), (3.3, -1.5))
  // `⟜` has no input, so these two strands simply begin — that is what a converse of a projection is.
  wiredot((2.1, 0.5)); wire((2.1, 0.5), (3.3, 0.5))
  wiredot((2.1, -0.5)); wire((2.1, -0.5), (3.3, -0.5))
  bend((3.3, 1.5), (4.4, 0.85), k: 0.4); bend((3.3, -0.5), (4.4, 0.85), k: 0.4); wiredot((4.4, 0.85))
  bend((3.3, 0.5), (4.4, -0.85), k: 0.4); bend((3.3, -1.5), (4.4, -0.85), k: 0.4)
  wiredot((4.4, -0.85))
  wire((4.4, 0.85), (5.0, 0.85)); wire((4.4, -0.85), (5.0, -0.85))
  lab(-0.35, 0, black)[$C$]; lab(5.35, 0.85, GIVEN1)[$A$]; lab(5.35, -0.85, GIVEN2)[$B$]
}), pairstr(eq: true)), ("", [`⟜ ▷ = 𝟙` on each half]), s: 100%)]<fork-collapse>


== Relational product `R × S`

#disp[#definition[
`R × S ≜ ⟨π₁ R, π₂ S⟩`, a relator in each argument but no longer a categorical product.
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

Right-then-up is `(R × S) π₁`, up-then-right is `π₁ R`, and `(R × S) π₁ ⊑ π₁ R`, equality when `S` is
entire. In `Rel`, `(c,d) (R × S) (a,b)` iff `c R a` and `d S b` — two strands side by side, no copy
dot: `R × S = R ⊗ S`.

== Absorption

For `X : E ⟶ C` and `Y : E ⟶ D`, `⟨X,Y⟩ (R × S) = ⟨X R, Y S⟩`. Both sides are this picture:

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

= Coproduct `[R,S]` <sec-coprod>

// THE DEFINITION, DRAWN, and it needs no new generator: `+` is a UNION, already drawn as the tape of
// the laws above.  A TAPE ONLY WHERE THERE IS A `∪`, which is why two of the three shape rows have none.
#disp[#table(
  columns: (1fr, 10.5cm),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*the statement*], [*picture*]),

  [`[R,S] ≜ ιₗ° R ∪ ιᵣ° S` \ #src[The tape is the union — a particle entering at `A + B` takes exactly
   one branch — and the two mirrored boxes are what makes the branches disjoint.]],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62                  // the tape's two branches, at the exported pictures' half-spacing
    wire((0, 0), (0.34, 0))
    tape((0.34, -1.14), (3.80, 1.14))
    tape-fork((0.56, 0), sp: y, len: 0.42)
    // Mirrored and tinted: this file draws a converse by flipping the box, so these are `ιₗ°` and `ιᵣ°`.
    gbox((0.98, y), [`ιₗ`], flip: true, fill: TINT); wire((1.90, y), (2.24, y)); gbox((2.24, y), [R])
    gbox((0.98, -y), [`ιᵣ`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y)); gbox((2.24, -y), [S])
    tape-join((3.58, 0), sp: y, len: 0.42)
    wire((3.80, 0), (4.14, 0))
    lab(-0.9, 0, black)[$A + B$]; lab(4.49, 0, black)[$C$]
  }), s: 85%),

  [`[R,S] = [`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`] ∋`], [],
  [`R + S ≜ [R ιₗ, S ιᵣ]`], [],
  [`ιₗ [R,S] = R`, `ιᵣ [R,S] = S`, and `[R,S]` is the only such arrow], [],

  // A map is the UNCHAMFERED box (`chamfer: false`), so the injection and its converse are told apart
  // by shape as well as by the tint, and a round trip reads as one box undoing the other.
  [`ιₗ ιₗ° = 𝟙 = ιᵣ ιᵣ°`],
  P(cetz.canvas(length: 0.8cm, {
    wire((0, 0), (0.34, 0)); gbox((0.34, 0), [`ιₗ`], chamfer: false)
    wire((1.26, 0), (1.60, 0)); gbox((1.60, 0), [`ιₗ`], flip: true, fill: TINT)
    wire((2.52, 0), (2.86, 0))
    lab(-0.35, 0, black)[$A$]; lab(1.43, 0.66, black)[$A + B$]; lab(3.21, 0, black)[$A$]
    lab(4.00, 0, black)[$=$]
    lab(4.55, 0, black)[$A$]; wire((4.90, 0), (6.30, 0)); lab(6.65, 0, black)[$A$]
  }), s: 85%),

  [`ιₗ ιᵣ° = ⊥ = ιᵣ ιₗ°`],
  P(cetz.canvas(length: 0.8cm, {
    wire((0, 0), (0.34, 0)); gbox((0.34, 0), [`ιₗ`], chamfer: false)
    wire((1.26, 0), (1.60, 0)); gbox((1.60, 0), [`ιᵣ`], flip: true, fill: TINT)
    wire((2.52, 0), (2.86, 0))
    lab(-0.35, 0, black)[$A$]; lab(1.43, 0.66, black)[$A + B$]; lab(3.21, 0, black)[$B$]
    lab(4.00, 0, black)[$=$]
    lab(4.55, 0, black)[$A$]; blocked((4.90, 0), (6.30, 0)); lab(6.65, 0, black)[$B$]
  }), s: 85%),

  [`ιₗ° ιₗ ∪ ιᵣ° ιᵣ = 𝟙`],
  P(cetz.canvas(length: 0.8cm, {
    let y = 0.62
    wire((0, 0), (0.34, 0))
    tape((0.34, -1.14), (4.24, 1.14))
    tape-fork((0.56, 0), sp: y, len: 0.42)
    gbox((0.98, y), [`ιₗ`], flip: true, fill: TINT); wire((1.90, y), (2.24, y))
    gbox((2.24, y), [`ιₗ`], chamfer: false); wire((3.16, y), (3.60, y))
    gbox((0.98, -y), [`ιᵣ`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y))
    gbox((2.24, -y), [`ιᵣ`], chamfer: false); wire((3.16, -y), (3.60, -y))
    tape-join((4.02, 0), sp: y, len: 0.42)
    wire((4.24, 0), (4.58, 0))
    lab(-1.05, 0, black)[$A + B$]; lab(5.60, 0, black)[$A + B$]
    lab(6.90, 0, black)[$=$]
    lab(7.85, 0, black)[$A + B$]; wire((8.55, 0), (9.95, 0)); lab(10.75, 0, black)[$A + B$]
  }), s: 85%),

  [`[U,V]° [R,S] = U° R ∪ V° S`], [],
)]<coprod-laws>

== `[R,S] ≜ [`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`] ∋`

// B&dM §5.3, pp. 117-118, mirrored into this note's diagram order: why the universal property holds
// with equality where the fork's triangles above only hold up to `Dom`.
The universal-property row is not free: `ιₗ, ιᵣ` were only ever asked to be a coproduct of *maps*. They stay one
once every arrow is allowed because $frac(#box(width: 8pt), ∋)$ sends an arrow `A ⟶ C` to a map `A ⟶ E C` reversibly, so the
map coproduct can be applied underneath it. For any `T : A + B ⟶ C`,

// The box chain of the `R%∋ = (R/∋) ∩ (∋/R)°` subsection, wrapped the same way: the row that
// carries over opens with its `⟺`.  Both `·∋ ⊣ %∋` steps are the same bijection, used each way.
#disp[
#zline(
  zpair(zsqc(`ιₗ T`, `R`, eq: true), zsqc(`ιᵣ T`, `S`, eq: true)),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zpair(zsqc($frac(#[`ιₗ T`], ∋)$, $frac(#[`R`], ∋)$, eq: true), zsqc($frac(#[`ιᵣ T`], ∋)$, $frac(#[`S`], ∋)$, eq: true)),
  zstep(op: sym.arrow.l.r.double, under: true)[fusion],
  zpair(zsqc([`ιₗ` $frac(#[`T`], ∋)$], $frac(#[`R`], ∋)$, eq: true), zsqc([`ιᵣ` $frac(#[`T`], ∋)$], $frac(#[`S`], ∋)$, eq: true)),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[coproduct of maps],
  zsqc($frac(#[`T`], ∋)$, [`[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]`], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`T`, [`[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`] ∋`], eq: true),
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
  lab(-5.18, 1.55, black)[`ιₗ`]; lab(-5.18, -1.55, black)[`ιᵣ`]
  lab(-1.23, 1.62, GIVEN1)[$frac(#[`R`], ∋)$]; lab(-1.23, -1.62, GIVEN2)[$frac(#[`S`], ∋)$]
  lab(-3.0, 0.5, INDUCED)[`[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]`]
  lab(2.5, 0.45, black)[`∋`]
  node(A.at(0), A.at(1), GIVEN1, $A$); node(B.at(0), B.at(1), GIVEN2, $B$)
  node(AB.at(0), AB.at(1), black, $A + B$)
  node(PC.at(0), PC.at(1), INDUCED, $E C$)
  node(C.at(0), C.at(1), black, $C$)
}))]<coprod-square>

Nothing here holds only up to `⊑`: every triangle commutes on the nose, which is the difference from
the fork above. The border spells `[R,S] = [`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`] ∋`, and pushing `∋` into the union that
`[·,·]` on maps already is turns that back into the definition,
`(ιₗ°` $frac(#[`R`], ∋)$ `∪ ιᵣ°` $frac(#[`S`], ∋)$`) ∋ = ιₗ° R ∪ ιᵣ° S`.

// B&dM §5.4, p. 119.  The heading gets its own page: the definition, the paragraph that explains its
// shape, and the table are one argument, and the coproduct figure above ends a page mid-way.
#pagebreak(weak: true)
= The power relator `P(R)` <sec-powrel>

// B&dM p. 119's three steps, in its order: the point-free line, the `Rel` set formula, one plain
// sentence.
#disp[#definition[
For `R : A ⟶ B`, #h(4pt) `P(R) ≜ ((∋ R)/∋) ∩ ((∋ R°)/∋)° : E A ⟶ E B`.

`xs P(R) ys ⟺ (∀a ∈ xs. ∃b ∈ ys. a R b) ∧ (∀b ∈ ys. ∃a ∈ xs. a R b)`

Every element of `xs` is related by `R` to some element of `ys`, and conversely.
]]<powrel-defn>

// On `1,2,3` both sides, NOT the `a₁,a₂,a₃`/`b₁,b₂,b₃` of the `skel` pictures below: two different
// examples, and this one has the empty image `R(2) = ∅` that those three cannot show.
#disp[#block(breakable: false)[
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (L, RC) = (0, 3.2)
  let ys = (1.0, 0, -1.0)
  ar((L, ys.at(0)), (RC, ys.at(0)), GIVEN1, s0: 0.22, s1: 0.3)
  ar((L, ys.at(0)), (RC, ys.at(1)), GIVEN1, s0: 0.22, s1: 0.3)
  ar((L, ys.at(2)), (RC, ys.at(2)), GIVEN1, s0: 0.22, s1: 0.3)
  for (k, y) in ys.enumerate() {
    wiredot((L, y)); lab(L - 0.42, y, black)[#raw(str(k + 1))]
    wiredot((RC, y)); lab(RC + 0.42, y, black)[#raw(str(k + 1))]
  }
  lab((L + RC) / 2, 1.5, GIVEN1)[`R`]
  lab(L, -1.7, black)[`A`]; lab(RC, -1.7, black)[`A`]
})))

#align(center, table(
  columns: 3,
  align: (left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*`xs`*], [*`ys` under `P(R)`*], [*`ys` under `E(R)`*]),

  [`∅`],       [`∅`],                       [`∅`],
  [`{1}`],     [`{1}`, `{2}`, `{1,2}`],     [`{1,2}`],
  [`{2}`],     [none],                      [`∅`],
  [`{3}`],     [`{3}`],                     [`{3}`],
  [`{1,2}`],   [none],                      [`{1,2}`],
  [`{1,3}`],   [`{1,3}`, `{2,3}`, `{1,2,3}`], [`{1,2,3}`],
  [`{2,3}`],   [none],                      [`{3}`],
  [`{1,2,3}`], [none],                      [`{1,2,3}`],
))

#align(center, block(width: 15cm, inset: (y: 8pt))[
  #src[`R(2) = ∅`, so `P(R)` sends no `ys` at all to any `xs` containing `2` — not entire.] \
  #src[`R(1)` has two elements, so `{1}` gets three: `1` need only meet `ys`, not be swallowed by it —
   not simple. Every `E(R)` row has exactly one `ys`, which is what makes it a map.]
])
]]<powrel-vs-erel>

#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, BD.b1, 1, [`∋ R`], h: 4.2, cx: 5)
  arc(LX, BD.b3, -1, [`∋ R`], h: 4.2, cx: 5)
})))
// The arrow and its `Rel` reading go UNDER the picture that draws them, one pair per picture: read
// against the drawing they were just given, where a table of all three read against nothing.
#align(center, block(inset: (y: 6pt))[
  `∋ R : E A ⟶ B` #h(1.4cm) `xs (∋ R) b ⟺ ∃a ∈ xs. a R b`
])
#align(center, src[one arc per element of `B` that `xs` reaches, and `b₂` gets none])]<powrel-elem>

Dividing by `∋` turns that into a relation between *sets*.

#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, LY.y1, 1, [`(∋ R)/∋`], h: 5.6, cx: 6)
  lab(3.2, 3.4, SLACK)[`∋`]
  yset(LY.y1, (BD.b1, BD.b3), `ys₁ = {b₁,b₃}`)
  yset(LY.y3, (BD.b2, BD.b3), `ys₃ = {b₂,b₃}`, on: false)
})))
#align(center, block(inset: (y: 6pt))[
  `(∋ R)/∋ : E A ⟶ E B` #h(1.4cm) `xs ((∋ R)/∋) ys ⟺ ∀b ∈ ys. ∃a ∈ xs. a R b`
])
#align(center, src[`ys₃` is rejected: it names `b₂`, which `xs` does not reach])]<powrel-div>

// Lead-in, picture and readings in ONE unbreakable block: left to itself the sentence ends one page
// and the picture opens the next, so the reader turns the page between the clause and its drawing.
#block(breakable: false)[
The other half of the meet is that clause with the sets swapped and `R` turned round: every element
of `xs` must reach `ys`:

#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, LY.y1, 1, [`P(R)`], h: 5.6, cx: 6)
  arc(LX, LY.y4, -1, [`P(R)`], h: 5.6, cx: 6)
  lab(3.2, 3.4, SLACK)[`∋`]
  yset(LY.y1, (BD.b1, BD.b3), `ys₁ = {b₁,b₃}`)
  yset(LY.y2, (BD.b1,), `ys₂ = {b₁}`, on: false)
  yset(LY.y3, (BD.b2, BD.b3), `ys₃ = {b₂,b₃}`, on: false)
  yset(LY.y4, (BD.b3,), `ys₄ = {b₃}`)
})))
#align(center, block(inset: (y: 6pt))[
  `((∋ R°)/∋)° : E A ⟶ E B` #h(1.4cm) `xs ((∋ R°)/∋)° ys ⟺ ∀a ∈ xs. ∃b ∈ ys. a R b`
])
#align(center, src[`ys₂` is rejected too: `a₂`'s only image is `b₃`, which `ys₂` does not name])]<powrel-both>
]

#disp[#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [`X ⊑ P(R) ⟺ X ∋ ⊑ ∋ R` and `X° ∋ ⊑ ∋ R°`],
  [One containment, and the same one at `R°` — which is the definition read off the two divisions.
   Hence `P(R°) = P(R)°`, and `R ⊑ S ⟹ P(R) ⊑ P(S)`.],

  [`P(𝟙) =` $frac(∋, ∋)$ `= 𝟙`],
  [The straightness axiom verbatim: extensionality *is* `P`'s unit law.],

  [`P(f) =` $frac(∋ f, ∋)$, for `f` a map],
  [In `Rel`, `xs P(f) ys ⟺ ys = {f a | a ∈ xs}`. The half at `f°` says every `a ∈ xs` has its `f a` on
   `ys`; `f` has just the one image per `a`, so that already says `ys` contains everything `xs`
   reaches, which is the fraction's second half. For a map the two definitions coincide.],

  [`P(R S) = P(R) P(S)`],
  [`⊒` is the division cancellation laws. `⊑` is the one law in this section that is not a
   calculation: it needs a tabulation of `P(R S)`.],
)]<powrel-laws>

// Its own page: otherwise the heading lands as the last line under the power relator's table, an orphan
// a page away from the definition it names, and the defining square below straddles the break.
#pagebreak(weak: true)
= Catamorphism <sec-cata>

#disp[#definition[
`F` a relator with an *initial algebra* `α`#sub[`T`]` : F T ⟶ T` among the maps. For a relational
algebra `α`#sub[`B`]` : F B ⟶ B`, the *catamorphism* `⦇α`#sub[`B`]`⦈ : T ⟶ B` is the unique arrow
with `α`#sub[`T`]` ⦇α`#sub[`B`]`⦈ = F(⦇α`#sub[`B`]`⦈) α`#sub[`B`]. Explicitly, for a relation
`R : F B ⟶ B`, `⦇R⦈ ≜ ⦇`$frac(#[`F(∋) R`], ∋)$`⦈ ∋`, the inner `⦇·⦈` being the catamorphism of a *map* algebra.
]]<cata-defn>

// Machine-checked: an algebra on `A` IS definitionally a natural transformation `F∘A ⇒ A` between
// functors `𝟏 ⟶ 𝒜`, NOT one `F ⇒ 𝟙` on `𝒜` — `Nat.add` is an algebra that is no such component.
An F-algebra is a *weakened* natural transformation. A transformation `F ⇒ 𝟙` on `𝒜` would need a
component `F X ⟶ X` at every object and a commuting square at every arrow, but F-Algebra only need it works on T and B.


== The defining equation

// `α` subscripted by its CARRIER through this section, `#sub` OUTSIDE the raw span (inside backticks `_` is
// literal).  A WIRE'S COLOUR IS ITS TYPE, A BEAD'S COLOUR IS WHICH ARROW IT IS, so arrows carry over.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FT, FB, T, B) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
    ar(FT, FB, INDUCED, dash: "dashed", s0: 0.75, s1: 0.75)
    ar(T, B, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.55, s1: 0.55)
    lab(0, 1.8, INDUCED)[`F(X)`]; lab(0, -1.8, INDUCED)[`X`]
    lab(-3.75, 0, GIVEN2)[`α`#sub[`T`]]; lab(3.7, 0, GIVEN1)[`α`#sub[`B`]]
    node(FT.at(0), FT.at(1), black, `F T`); node(FB.at(0), FB.at(1), GIVEN1, `F B`)
    node(T.at(0), T.at(1), black, `T`); node(B.at(0), B.at(1), GIVEN1, `B`)
  }),
  homeq(`F`, `T`, [`α`#sub[`T`]], [`⦇α`#sub[`B`]`⦈`], [`α`#sub[`B`]], `B`,
    typed: true, regions: (`𝒜`, `𝟏`), ctop: GIVEN2, cmid: INDUCED, cbot: GIVEN1),
  [`X = ⦇α`#sub[`B`]`⦈ ⟺ α`#sub[`T`]` X = F(X) α`#sub[`B`]],
)]<cata-defining>

== `⦇R⦈ = ⦇`$frac(#[`F(∋) R`], ∋)$`⦈ ∋`

// @cata-defining's square at `α`#sub[`B`]`:= (F(∋) R)%∋`, `B := E B`: the same geometry, the same
// colours, only the two induced arrows and the right vertical renamed.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FT, FB, T, B) = ((-3.4, 1.25), (3.4, 1.25), (-3.4, -1.25), (3.4, -1.25))
    ar(FT, FB, INDUCED, dash: "dashed", s0: 0.75, s1: 1.15)
    ar(T, B, INDUCED, dash: "dashed", s0: 0.55, s1: 0.9)
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.55, s1: 0.55)
    lab(0, 1.8, INDUCED)[`F(⦇`$frac(#[`F(∋) R`], ∋)$`⦈)`]; lab(0, -1.8, INDUCED)[`⦇`$frac(#[`F(∋) R`], ∋)$`⦈`]
    lab(-4.15, 0, GIVEN2)[`α`#sub[`T`]]; lab(4.85, 0, GIVEN1)[$frac(#[`F(∋) R`], ∋)$]
    node(FT.at(0), FT.at(1), black, `F T`); node(FB.at(0), FB.at(1), GIVEN1, `F(E B)`)
    node(T.at(0), T.at(1), black, `T`); node(B.at(0), B.at(1), GIVEN1, `E B`)
  }),
  homeq(`F`, `T`, [`α`#sub[`T`]], [`⦇`$frac(#[`F(∋) R`], ∋)$`⦈`], [$frac(#[`F(∋) R`], ∋)$], `E B`,
    typed: true, regions: auto, ctop: GIVEN2, cmid: INDUCED, cbot: GIVEN1, gap: 5.2),
  [`α`#sub[`T`]` ⦇`$frac(#[`F(∋) R`], ∋)$`⦈ = F(⦇`$frac(#[`F(∋) R`], ∋)$`⦈)` $frac(#[`F(∋) R`], ∋)$],
)]<cata-map-square>

// B&dM (5.12), p. 121, mirrored into this note's diagram order.  A row too wide for the column wraps,
// and the next row opens with the `⟺` that carries it over.
#disp[
#zline(
  zsqc([`α`#sub[`T`]` X`], [`F(X) R`], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc([$frac(#[`α`#sub[`T`]` X`], ∋)$], [$frac(#[`F(X) R`], ∋)$], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc([$frac(#[`α`#sub[`T`]` X`], ∋)$], [$frac(#[`F(`$frac(#[`X`], ∋)$ `∋) R`], ∋)$], eq: true),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[relator, fusion twice],
  zsqc([`α`#sub[`T`] $frac(#[`X`], ∋)$], [`F(`$frac(#[`X`], ∋)$`)` $frac(#[`F(∋) R`], ∋)$], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[catamorphism of maps],
  zsqc([$frac(#[`X`], ∋)$], [`⦇`$frac(#[`F(∋) R`], ∋)$`⦈`], eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc([`X`], [`⦇`$frac(#[`F(∋) R`], ∋)$`⦈ ∋`], eq: true),
)
]<cata-map-calc>

== Reflection

// The defining square at `X := 𝟙`, `α_B := α_T`, on the defining equation's ±3 geometry: both verticals are the ONE
// arrow `α_T`, so both are GIVEN2.  The right panel is bare — `𝟙` is an empty wire, and that is the law.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FT, FT2, T, T2) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
    ar(FT, FT2, INDUCED, dash: "dashed", s0: 0.75, s1: 0.75)
    ar(T, T2, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FT2, T2, GIVEN2, s0: 0.55, s1: 0.55)
    lab(0, 1.8, INDUCED)[`F(𝟙)`]; lab(0, -1.8, INDUCED)[`𝟙`]
    lab(-3.75, 0, GIVEN2)[`α`#sub[`T`]]; lab(3.7, 0, GIVEN2)[`α`#sub[`T`]]
    node(FT.at(0), FT.at(1), black, `F T`); node(FT2.at(0), FT2.at(1), black, `F T`)
    node(T.at(0), T.at(1), black, `T`); node(T2.at(0), T2.at(1), black, `T`)
  }),
  beadeq(`T`, [`⦇α`#sub[`T`]`⦈`], `T`, cb: INDUCED, typed: true, regions: auto),
  [`⦇α`#sub[`T`]`⦈ = 𝟙`],
)]<cata-reflection>

// `relCata_alpha`, AOP/A6_3.lean:40.
Taking a value apart with `α`#sub[`T`] and putting it straight back is doing nothing.

== Fusion

// `T` is already the initial algebra's carrier, so the second algebra's is `C`.  `R` is `α_B` and `Q`
// is `α_C`; `S` keeps its letter, being the homomorphism, not an algebra — a subscript would miscast it.
Fusion rewrites `⦇α`#sub[`B`]`⦈ S` through a second algebra `α`#sub[`C`]` : F C ⟶ C` along an arrow
`S : B ⟶ C`.

// `tcol`/`bcol` spelled out because the side condition's object wire runs `B` then `C` where the
// defaults run `T`, `B` — one object, one hue.  `s: 92%`: the one row that does not fit at full size.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FT, FB, FC) = ((-6, 1.25), (0, 1.25), (6, 1.25))
    let (T, B, C) = ((-6, -1.25), (0, -1.25), (6, -1.25))
    ar(FT, FB, INDUCED, dash: "dashed", s0: 0.75, s1: 0.75)
    ar(FB, FC, black, s0: 0.75, s1: 0.75)
    ar(T, B, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
    ar(B, C, black, s0: 0.55, s1: 0.55)
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.55, s1: 0.55)
    ar(FC, C, GIVEN1, s0: 0.55, s1: 0.55)
    lab(-3, 1.8, INDUCED)[`F(⦇α`#sub[`B`]`⦈)`]; lab(3, 1.8, black)[`F(S)`]
    lab(-3, -1.8, INDUCED)[`⦇α`#sub[`B`]`⦈`]; lab(3, -1.8, black)[`S`]
    lab(-6.75, 0, GIVEN2)[`α`#sub[`T`]]; lab(0.75, 0, GIVEN1)[`α`#sub[`B`]]; lab(6.8, 0, GIVEN1)[`α`#sub[`C`]]
    node(FT.at(0), FT.at(1), black, `F T`); node(T.at(0), T.at(1), black, `T`)
    node(FB.at(0), FB.at(1), GIVEN1, `F B`); node(B.at(0), B.at(1), GIVEN1, `B`)
    node(FC.at(0), FC.at(1), GIVEN1, `F C`); node(C.at(0), C.at(1), GIVEN1, `C`)
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
  [`⦇α`#sub[`B`]`⦈ S = ⦇α`#sub[`C`]`⦈ ⟸ α`#sub[`B`]` S = F(S) α`#sub[`C`]],
  s: 92%,
)]<cata-fusion>

The left square is `⦇α`#sub[`B`]`⦈`'s own defining square and the right one is the side condition,
so the outer rectangle says `⦇α`#sub[`B`]`⦈ S` satisfies the defining equation of `⦇α`#sub[`C`]`⦈` —
and uniqueness finishes it. A fold followed by `S` has collapsed into a single fold, which is how an
intermediate structure is got rid of.

// The substitution stays on ONE source line: a newline inside a backtick span is a hard line break
// in the output, which cut this sentence in two on the first render.
The side condition is @cata-defining's picture again under
`α`#sub[`T`]`↦α`#sub[`B`]`, ⦇α`#sub[`B`]`⦈↦S, α`#sub[`B`]`↦α`#sub[`C`]: both say that the bead
between the two merges is a homomorphism of `F`-algebras.

== Catamorphism in 𝒮et

// B&dM §3.1 "Banana-split", pp. 55–57.  The book writes `h · f` applicatively; every composite in the
// table is mirrored to `f h`, this note's diagram order.
#disp[#table(
  columns: (3.0cm, 11.2cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*note*]),

  [`listr`],
  [`listr A ::= nil | cons (A, listr A)`],
  [The cons-lists over `A`, the datatype every row below folds (B&dM p. 55).],

  [`sum`],
  [`⦇[zero, plus]⦈`],
  [`plus(a, b) = a + b`.],

  [`length`],
  [`⦇[zero, outr succ]⦈`],
  [`outr` drops the head and keeps the count of the tail, `succ` adds one for the head.],

  [`average`],
  [`⟨sum, length⟩ div`],
  [`div(m, n) = m/n`, with `div(0, 0) = 0` so `average` is total. Traverses the list twice.],

  [banana-split law],
  [`⟨⦇h⦈, ⦇k⦈⟩ = ⦇⟨F(outl) h, F(outr) k⟩⦈`],
  [Any fork of folds is a single fold, hence one traversal — `F` the base functor.],

  [what it reduces to],
  [`α ⟨⦇h⦈, ⦇k⦈⟩ = F(⟨⦇h⦈, ⦇k⦈⟩) ⟨F(outl) h, F(outr) k⟩`],
  [All that @cata-defining leaves to check: the fork satisfies the defining equation, and
   uniqueness finishes it.],

  [the instance],
  [`⟨sum, length⟩ = ⦇[zeros, pluss]⦈`],
  [`zeros = ⟨zero, zero⟩` and `pluss(a, (b, n)) = (a + b, n + 1)`, so `average` runs in one pass.],

  [`preds`],
  [`preds : Nat -> [Nat]`, `preds n = [n, n−1, …, 1]`],
  [B&dM Ex 3.6 (p. 57), posed and not answered there: apply Ex 3.4 to write `preds` as `⦇k⦈ outl`.],
)]<cata-examples>

// The square is the product's universal property at `T`, the string diagram the row above it: one
// fold bead, the algebra falling past it, exactly as in @cata-defining.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (T, A, AB, B) = ((-4.2, 0), (2.8, 1.9), (2.8, 0), (2.8, -1.9))
    ar(T, A, GIVEN1, s0: 0.45, s1: 0.55); ar(T, B, GIVEN2, s0: 0.45, s1: 0.55)
    ar(T, AB, INDUCED, dash: "dashed", s0: 0.45, s1: 0.95)
    ar(AB, A, GIVEN1, s0: 0.55, s1: 0.55); ar(AB, B, GIVEN2, s0: 0.55, s1: 0.55)
    lab(-0.7, 1.35, GIVEN1)[`⦇h⦈`]; lab(-0.7, -1.35, GIVEN2)[`⦇k⦈`]
    lab(-0.5, 0.4, INDUCED)[`⟨⦇h⦈, ⦇k⦈⟩`]
    lab(3.5, 0.95, GIVEN1)[`outl`]; lab(3.5, -0.95, GIVEN2)[`outr`]
    node(T.at(0), T.at(1), black, `T`); node(A.at(0), A.at(1), GIVEN1, `A`)
    node(AB.at(0), AB.at(1), INDUCED, `A × B`); node(B.at(0), B.at(1), GIVEN2, `B`)
  }),
  homeq(`F`, `T`, [`α`], [`⟨⦇h⦈, ⦇k⦈⟩`], [`⟨F(outl) h, F(outr) k⟩`], `A × B`,
    ctop: GIVEN2, cmid: INDUCED, cbot: GIVEN1, typed: true, gap: 3.2, regions: auto),
  [`⟨⦇h⦈, ⦇k⦈⟩ = ⦇⟨F(outl) h, F(outr) k⟩⦈`],
)]<banana-split>

*The other laws.*

// (2.12) is NOT one of them: it follows from `relCata_UP` (AOP/A5_5.lean:31) and associativity alone,
// under a class with no local completeness.  The two `⊑` rows are AOP/A6_2.lean:224,239, (6.4)/(6.5).
The two `⊑` *fusion* rows rewrite `⦇α`#sub[`B`]`⦈ S` through the same `α`#sub[`C`] and `S`. They are the only rows here
that need the allegory *locally complete* — every hom-set a complete lattice — because they come from
a least-fixed-point argument; the rest, the equality fusion @cata-fusion included, needs only the
initial algebra and the defining equation.

// The law column is the law tables' 7.4cm, so `⦇α_C⦈ ⊑ ⦇α_B⦈ S ⟸ F(S) α_C ⊑ α_B S` stays on one line;
// the name column fits `Eilenberg–Wright` unbroken, a split hyphenated name reading as two names.
#disp[#table(
  columns: (4.2cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*law*], [*what it says*]),

  [Lambek],
  [`α`#sub[`T`]`° = α`#sub[`T`]`⁻¹`, the initial algebra is an isomorphism],
  [A constructor can be undone — `α`#sub[`T`]`°` takes a value apart into the parts it was built
   from.],

  [Eilenberg–Wright],
  [$frac(#[`⦇α`#sub[`B`]`⦈`], ∋)$ `= ⦇`$frac(#[`F(∋) α`#sub[`B`]], ∋)$`⦈`],
  [A relational fold is a deterministic fold of SETS: $frac(#box(width: 8pt), ∋)$ pushes the nondeterminism into the
   power-object, where the fold is a map again.],

  [Eilenberg–Wright],
  [`⦇α`#sub[`B`]`⦈ = ⦇`$frac(#[`F(∋) α`#sub[`B`]], ∋)$`⦈ ∋`],
  [The same fact read back — fold deterministically into a set, then take a member of it.],

  [fusion],
  [`⦇α`#sub[`C`]`⦈ ⊑ ⦇α`#sub[`B`]`⦈ S ⟸ F(S) α`#sub[`C`]` ⊑ α`#sub[`B`]` S`],
  [Half of fusion: an inclusion between the two algebras is inherited by the folds.],

  [fusion],
  [`⦇α`#sub[`B`]`⦈ S ⊑ ⦇α`#sub[`C`]`⦈ ⟸ α`#sub[`B`]` S ⊑ F(S) α`#sub[`C`]],
  [The other half, with both inclusions turned around.],
)]<cata-other-laws>

// UNBREAKABLE, sentence and figure together: otherwise the sentence ends the page and "drawn:" points
// at nothing overleaf.  `width: 100%` or the block shrinks and `align(center)` has nothing to centre.
#block(breakable: false, width: 100%)[
The two $frac(#box(width: 8pt), ∋)$ rows, drawn:

// `⦇(F(∋) α_B)%∋⦈` is three node-boxes wide, so inside the picture it is the single letter `K` and the
// sentence below says what `K` is; the middle algebra stays spelled out, being what the square is OF.
#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (FT, FP, FB) = ((-6, 1.25), (0, 1.25), (6, 1.25))
  let (T, P, B) = ((-6, -1.25), (0, -1.25), (6, -1.25))
  ar(FT, FP, INDUCED, dash: "dashed", s0: 0.75, s1: 0.95)
  ar(FP, FB, black, s0: 0.95, s1: 0.75)
  ar(T, P, INDUCED, dash: "dashed", s0: 0.55, s1: 0.7)
  ar(P, B, black, s0: 0.7, s1: 0.55)
  ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FP, P, black, s0: 0.55, s1: 0.55)
  ar(FB, B, GIVEN1, s0: 0.55, s1: 0.55)
  lab(-3, 1.8, INDUCED)[`F(K)`]; lab(3, 1.8, black)[`F(∋)`]
  lab(-3, -1.8, INDUCED)[`K`]; lab(3, -1.8, black)[`∋`]
  lab(-6.75, 0, GIVEN2)[`α`#sub[`T`]]; lab(6.8, 0, GIVEN1)[`α`#sub[`B`]]; lab(2.2, 0, black)[$frac(#[`F(∋) α`#sub[`B`]], ∋)$]
  node(FT.at(0), FT.at(1), black, `F T`); node(T.at(0), T.at(1), black, `T`)
  node(FP.at(0), FP.at(1), INDUCED, `F(E B)`); node(P.at(0), P.at(1), INDUCED, `E B`)
  node(FB.at(0), FB.at(1), GIVEN1, `F B`); node(B.at(0), B.at(1), GIVEN1, `B`)
}))]<cata-lambda-square>
]

The left square is that catamorphism's own defining square, `K = ⦇`$frac(#[`F(∋) α`#sub[`B`]], ∋)$`⦈`, and the
right one is $frac(#box(width: 8pt), ∋)$'s cancellation, so the outer rectangle says `K ∋` satisfies the defining equation
of `⦇α`#sub[`B`]`⦈` — and uniqueness finishes it.

// Its own page: the heading was left orphaned at the foot of the page before it.
#pagebreak(weak: true)
=== Fokkinga's mutual recursion theorem

// Algebras lettered `h`, `k` as in @cata-examples; the display below reuses the letters for the
// general case, which is what the last bullet contrasts the product with.
- `F-Alg(𝒜)` — the algebras and their homomorphisms — has binary products whenever `𝒜` does, and the
  forgetful `U : F-Alg(𝒜) ⟶ 𝒜` *creates* them: the product of `h : F A ⟶ A` and `k : F B ⟶ B` is
  carried by `A × B`, with structure `⟨F(outl) h, F(outr) k⟩ : F(A × B) ⟶ A × B`.
- `outl` and `outr` are homomorphisms out of it, and `⟨p, q⟩ : X ⟶ A × B` is a homomorphism *iff* `p`
  and `q` both are — substitute the structure and compare the two forks component by component.
- The banana-split law of @cata-examples IS that product's universal property read at the initial
  algebra: `⦇h⦈` and `⦇k⦈` are the unique homomorphisms to `(A, h)` and `(B, k)`, so their fork is the
  unique homomorphism into the product, which is `⦇⟨F(outl) h, F(outr) k⟩⦈`.
- Fokkinga's theorem is *strictly more general* and is not that product: in @fokkinga the two arrows
  leave `F(A × B)`, not `F A` and `F B`, so each sees BOTH components. The product is the case where
  they factor as `F(outl) h` and `F(outr) k`; B&dM's Ex 3.4 is the other special case (p. 58). What
  it says: *any algebra on a product carrier is folded by a fork*.

// B&dM Ex 3.8 (p. 58), ONE SQUARE PER CONJUNCT: `h` and `k` leave `F(A × B)` for different corners,
// so a single square cannot carry both.  Dashed blue as in @cata-defining — the arrows uniqueness gives.
#disp[#capbox(
  grid(columns: 2, align: horizon, column-gutter: 34pt,
    cetz.canvas(length: 0.8cm, {
      let (FT, FAB, T, A) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
      ar(FT, FAB, INDUCED, dash: "dashed", s0: 0.75, s1: 1.45)
      ar(T, A, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
      ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FAB, A, GIVEN1, s0: 0.55, s1: 0.55)
      lab(0, 1.8, INDUCED)[`F(⟨f, g⟩)`]; lab(0, -1.8, INDUCED)[`f`]
      lab(-3.4, 0, GIVEN2)[`α`]; lab(3.4, 0, GIVEN1)[`h`]
      node(FT.at(0), FT.at(1), black, `F T`); node(FAB.at(0), FAB.at(1), GIVEN1, `F(A × B)`)
      node(T.at(0), T.at(1), black, `T`); node(A.at(0), A.at(1), GIVEN1, `A`)
    }),
    cetz.canvas(length: 0.8cm, {
      let (FT, FAB, T, B) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
      ar(FT, FAB, INDUCED, dash: "dashed", s0: 0.75, s1: 1.45)
      ar(T, B, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
      ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FAB, B, GIVEN1, s0: 0.55, s1: 0.55)
      lab(0, 1.8, INDUCED)[`F(⟨f, g⟩)`]; lab(0, -1.8, INDUCED)[`g`]
      lab(-3.4, 0, GIVEN2)[`α`]; lab(3.4, 0, GIVEN1)[`k`]
      node(FT.at(0), FT.at(1), black, `F T`); node(FAB.at(0), FAB.at(1), GIVEN1, `F(A × B)`)
      node(T.at(0), T.at(1), black, `T`); node(B.at(0), B.at(1), GIVEN1, `B`)
    }),
  ),
  [`α f = F(⟨f, g⟩) h  ∧  α g = F(⟨f, g⟩) k  ≡  ⟨f, g⟩ = ⦇⟨h, k⟩⦈`],
)]<fokkinga>

=== Ruby triangles

// B&dM §3.2, pp. 58–59.  The book writes `cons · (id × listr f)` applicatively; every composite in the
// table is mirrored by `h·f ↦ f h` into this note's diagram order.
#disp[#table(
  columns: (5.8cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*stage*], [*definition*]),

  [informally (p. 58)],
  [`tri(f) [a₀, a₁, …, aᵢ, …, aₙ] = [a₀, f a₁, …, fⁱ aᵢ, …, fⁿ aₙ]`],

  [for cons-lists (p. 59)],
  [`tri(f) = ⦇[nil, (𝟙 × listr(f)) cons]⦈`],

  [with the base functor named],
  [`F(A, B) = 1 + A × B`, `α = [nil, cons]`, so `tri(f) = ⦇F(𝟙, listr(f)) α⦈`],

  [abstractly (p. 59)],
  [`F` a bifunctor with initial type `(α, T)`: `tri(f) = ⦇F(𝟙, T(f)) α⦈`],
)]<tri-evolution>

For the definition to make sense `f : A ⟶ A` is required, and then `tri(f) : T A ⟶ T A`.

// The book's top arrow points LEFT because it composes applicatively, so mirroring it into diagram
// order swaps the legs: `⦇g⦈` post-composes `tri(f)`, hence leaves the RIGHT `T A` (B&dM p. 59).
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (TL, TR, A) = ((-2.2, 1.25), (2.2, 1.25), (0, -1.25))
    ar(TL, TR, GIVEN2, s0: 0.6, s1: 0.6)
    ar(TL, A, INDUCED, dash: "dashed", s0: 0.6, s1: 0.6)
    ar(TR, A, INDUCED, dash: "dashed", s0: 0.6, s1: 0.6)
    lab(0, 1.8, GIVEN2)[`tri(f)`]
    lab(-3.1, -0.35, INDUCED)[`⦇F(𝟙, f) g⦈`]; lab(2.0, -0.35, INDUCED)[`⦇g⦈`]
    node(TL.at(0), TL.at(1), black, `T A`); node(TR.at(0), TR.at(1), black, `T A`)
    node(A.at(0), A.at(1), GIVEN1, `A`)
  }),
  twobeadeq(`T A`, [`tri(f)`], [`⦇g⦈`], [`⦇F(𝟙, f) g⦈`], `A`, c1: GIVEN2, c2: INDUCED, c3: INDUCED,
    typed: true, vcol: TCOL, bcol: BCOL, regions: auto),
  [`tri(f) ⦇g⦈ = ⦇F(𝟙, f) g⦈` #h(1.6cm) `⟸` #h(1.6cm) `g f = F(f, f) g`],
)]<horner>

@horner is Horner's rule, generalised from cons-lists to any initial type; B&dM call it that because
for cons-lists it is the schoolbook method for evaluating a polynomial (p. 58). Fusion reduces it to
`F(𝟙, T(f)) α ⦇g⦈ = F(𝟙, ⦇g⦈) F(𝟙, f) g` (p. 59).

// Its own page: the section is one table long and the heading was left orphaned at the foot of the
// page before it once the F-Alg bullets above pushed the table over the break.
#pagebreak(weak: true)
=== Depth of a tree

// B&dM p. 60, mirrored to diagram order: the book writes `depths = tri succ · tree zero` and
// `depth = max · depths`.
#disp[#table(
  columns: (3.0cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [the datatype],
  [`tree A ::= tip A | bin (tree A, tree A)`, base functor `F(A, B) = A + B × B`, \
   initial type `([tip, bin], tree)`],

  [the fold],
  [`⦇[g, h]⦈` is the unique `f` with `f (tip a) = g a` and `f (bin (x, y)) = h (f x, f y)`],

  [`tree(f)`],
  [`tree(f) = ⦇F(f, 𝟙) [tip, bin]⦈`; pointwise `tree(f) (tip a) = tip (f a)` and \
   `tree(f) (bin (x, y)) = bin (tree(f) x, tree(f) y)`],

  [`max`],
  [`max = ⦇[𝟙, bmax]⦈`, where `bmax (a, b)` is the larger of `a` and `b`],

  [`depths`],
  [`depths = tree(zero) tri(succ)` — replaces every tip by its depth in the tree, `zero` the
   constant function returning 0 and `succ` the successor],

  [`depth`],
  [`depth = depths max`],
)]<tree-depth>

// Its own page: the definition below only says what `T(R)` is, and the square after it is the reason
// that arrow exists, so the two have to be read together — under the picture above they would not be.
#pagebreak(weak: true)
= Type functor

#disp[#definition[
`F` a *binary* relator: `F(R, S)` is its action on a pair, and `F(X)` abbreviates `F(𝟙, X)`, the `F` of
the catamorphism section. For every object `A` the initial algebra is `α : F(A, T A) ⟶ T A`, among the
maps. The *type functor* `T` acts on an arrow `R : A ⟶ B` by

  #align(center, block(inset: (y: 6pt))[`T(R) = ⦇F(R, 𝟙) α⦈ : T A ⟶ T B`])
]]<tf-defn>

`F` is the *base functor* — one layer of the structure, acting on the recursive position — while `T` is
the datatype itself, acting on the parameter. For cons-lists, `list(R) = ⦇[nil, (R ⊗ 𝟙) cons]⦈`, which
is `map(R)`.

// THE DRAWING CONVENTION FOR A BIFUNCTOR, stated before the first picture that uses it.
A bifunctor puts its two arguments in two different places. The wire is the partial application
`F`#sub[`A`]` = F(A, −)`, and an arrow in the SECOND argument is a bead on the object wire with the
`F` wire running past it — the catamorphism section's rule, unchanged — while an arrow `R : A ⟶ B`
in the FIRST induces a natural transformation `F`#sub[`R`]` : F`#sub[`A`]` ⇒ F`#sub[`B`], which is a
bead ON the `F` wire. Marsden draws bifunctors exactly so (`CatString.pdf`, *Bifunctors*):
side-by-side is already spent on functor composition, so one argument has to go into the wire's name.

// (2.10) at `F := F(A, −)`, `α_B := F(R, 𝟙) α`: the algebra is the WHOLE right vertical, and the old
// drawing spent `F(R, 𝟙)` along the top row, which hid the fold.  x = ±3.5 for `F(A, T A)`'s width.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (FA, FM, TA, TB) = ((-3.5, 1.25), (3.5, 1.25), (-3.5, -1.25), (3.5, -1.25))
    ar(FA, FM, INDUCED, dash: "dashed", s0: 1.45, s1: 1.45)
    ar(TA, TB, INDUCED, dash: "dashed", s0: 0.65, s1: 0.65)
    ar(FA, TA, GIVEN2, s0: 0.55, s1: 0.55); ar(FM, TB, GIVEN1, s0: 0.55, s1: 0.55)
    lab(0, 1.85, INDUCED)[`F(𝟙, T(R))`]; lab(0, -1.85, INDUCED)[`T(R)`]
    lab(-4.15, 0, GIVEN2)[`α`]; lab(5.6, 0, GIVEN1)[`F(R, 𝟙) α`]
    node(FA.at(0), FA.at(1), black, `F(A, T A)`); node(TA.at(0), TA.at(1), black, `T A`)
    node(FM.at(0), FM.at(1), GIVEN1, `F(A, T B)`); node(TB.at(0), TB.at(1), GIVEN1, `T B`)
  }),
  homeq([`F`#sub[`A`]], [`T A`], `α`, [`T(R)`], `α`, [`T B`],
    fmid: [`F`#sub[`R`]], cfmid: GIVEN1, typed: true, regions: auto,
    ctop: GIVEN2, cmid: INDUCED, cbot: GIVEN1),
  [`T(R) = ⦇F(R, 𝟙) α⦈`],
)]<tf-sq>

`T(R)` is the unique arrow making it commute; there is no `⊑` in it.

Two beads at one height on two different wires are one action, here `F(R, T(R))`, so the right panel
reads `F(R, T(R)) α` and the left one `α T(R)`. Their relative height says nothing: slide
`F`#sub[`R`] below the `T(R)` bead and the panel reads `F(𝟙, T(R)) F(R, 𝟙)` and then `α`, which is the
square's top row followed by its right vertical; slide it above and the panel reads
`F(R, 𝟙) F(𝟙, T(R))`, the route through `F(B, T A)` the square leaves out. Identifying those two is
the exchange condition every bifunctor satisfies (Hinze & Marsden, Ex 1.23), and in this calculus
there is nothing to identify.

// Same widths and stroke as the catamorphism table: the two tables are read one after the other, and
// a law column that changes width between them reads as a different kind of column.
#disp[#table(
  columns: (4.2cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*law*], [*what it says*]),

  [the defining equation],
  [`T(R) = ⦇F(R, 𝟙) α⦈`],
  [Rebuild the structure with `α`, applying `R` to the parameter on the way; that is `map(R)`.],

  [functor],
  [`T(𝟙) = 𝟙` and `T(R) T(S) = T(R S)`],
  [Mapping the identity changes nothing, and two maps in a row are one map.],

  [type functor fusion],
  [`T(R) ⦇Q⦈ = ⦇F(R, 𝟙) Q⦈`],
  [A map followed by a fold is a single fold — the mapped structure is never built.],

  [naturality of `α`],
  [`α T(R) = F(R, T(R)) α`],
  [Building and then mapping is the same as mapping the parts and then building, so `α` is natural
   from `G(R) = F(R, T(R))` to `T`.],

  [type relator],
  [`T(R)° = T(R°)`],
  [A datatype acts on relations, not only on maps — the map of the converse is the converse of the
   map.],
)]<tf-laws>

// Equality fusion needs NO local completeness — (2.12) above is on record for that.
Type functor fusion is the equality fusion @cata-fusion applied to `T(R)`'s own defining algebra,
whose side condition holds because `F` is a bifunctor —
`F(R, 𝟙) F(𝟙, ⦇Q⦈) = F(R, ⦇Q⦈) = F(𝟙, ⦇Q⦈) F(R, 𝟙)` — so it too needs only the initial algebra and
the defining equation.

// THE NATURALITY ROW, drawn: the square above with its two top arrows composed into the one relator
// action `F(R, T(R))`, which is why this one is back to the ±3 of the catamorphism square.
#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (FA, FB, TA, TB) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
  ar(FA, FB, INDUCED, s0: 1.45, s1: 1.45)
  ar(TA, TB, INDUCED, s0: 0.65, s1: 0.65)
  ar(FA, TA, GIVEN2, s0: 0.55, s1: 0.55); ar(FB, TB, GIVEN1, s0: 0.55, s1: 0.55)
  lab(0, 1.85, INDUCED)[`F(R, T(R))`]; lab(0, -1.85, INDUCED)[`T(R)`]
  lab(-3.6, 0, GIVEN2)[`α`]; lab(3.55, 0, GIVEN1)[`α`]
  node(FA.at(0), FA.at(1), black, `F(A, T A)`); node(TA.at(0), TA.at(1), black, `T A`)
  node(FB.at(0), FB.at(1), GIVEN1, `F(B, T B)`); node(TB.at(0), TB.at(1), GIVEN1, `T B`)
}))]<tf-nat>

It commutes strictly, and it is @tf-sq with the right vertical's two halves separated: push
`F(R, 𝟙)` up into the top row, where it meets `F(𝟙, T(R))` as the one action `F(R, T(R))`, and `α` is
left as the vertical. In the string diagram that is the `F`#sub[`R`] bead sliding up past `T(R)`, and
what stays put is `α`, one bead falling past `T(R)` from the row above to the row below — which is
what "`α` is natural" means.

= Monad

// IntroString §3.1 (p. 64), in this note's diagram order; the book prints `μ ⋅ (η∘M) = id`.
// Juxtaposition is vertical composition, `∘` is functor composition and applicative.
#disp[#definition[
An endofunctor `M : 𝒜 ⟶ 𝒜` with two natural transformations, the *unit* `η : Id ⇒ M` and the
*multiplication* `μ : M∘M ⇒ M`, subject to a unit law and an associativity law:

  #align(center, block(inset: (y: 6pt))[
    `(η∘M) μ = 𝟙 = (M∘η) μ` #h(1.6cm) `(μ∘M) μ = (M∘μ) μ`
  ])
]]<monad-defn>

// ONE HUE PER TRANSFORMATION FOR THE WHOLE SECTION, fixed here: `η` GIVEN2, `μ` GIVEN1.  Both are
// given data and neither induced by the other, so INDUCED stays for @state-unit's conclusion.
#disp[#align(center, monadops(ceta: GIVEN2, cmu: GIVEN1))]<monad-ops>

In @monad-ops the identity functor is a REGION and not a wire, so `η : Id ⇒ M` has nothing above it and the `M`
wire simply begins at its bead — the book's lollipop. `μ : M∘M ⇒ M` is the two `M` wires of `M∘M`
merging into one, its tuning fork.

// `capbox` and not `pair`: there is no commutative square to set beside an axiom already stated as an
// equation between pictures.  Same hues as @monad-ops so the beads carry over; `monadassoc` has no `η`.
#disp[#capbox(monadunit(ceta: GIVEN2, cmu: GIVEN1), [`(η∘M) μ = 𝟙 = (M∘η) μ`])]<monad-unit>

The lollipop is absorbed into the fork from either side and a bare wire is left, which is what `𝟙` is
in this calculus: nothing is drawn for it.

#disp[#capbox(monadassoc(cmu: GIVEN1), [`(μ∘M) μ = (M∘μ) μ`])]<monad-assoc>

The two nestings of the fork agree, so three `M`s collapse to one whichever pair is multiplied first.

== Monad in 𝒮et

// The powerset row is `Pow`, the book's own name for the functor (p. 66): `P` is spoken for twice —
// the power relator section and this table's set of states — and `[−]` names the OBJECT, not the functor.
#disp[#table(
  columns: 5, inset: 9pt, stroke: 0.4pt + luma(190), align: horizon,
  table.header([*monad*], [*`η`*], [*`μ`*], [*`η` on elements*], [*`μ` on elements*]),

  [`Id A = A`], [`𝟙`], [`𝟙`], [`η A a = a`], [`μ A a = a`],

  [`Exc A = A + E`], [`ιₗ`], [`𝟙 ▿ ιᵣ`], [`η A a = ιₗ a`],
  [`μ A (ιₗ y) = y` \ `μ A (ιᵣ e) = ιᵣ e`],

  [`State A = (A × P)`#super[`P`]], [`curry 𝟙`], [`(apply`#sub[`A × P`]`)`#super[`P`]],
  [`η A a = λ x . (a, x)`], [`μ A f = λ x . g y` where `(g, y) = f x`],

  [`Pow A = E A`], [$frac(#[`𝟙`], ∋)$], [`⋃`], [`η A a = {a}`], [`μ A Xs = ⋃ Xs`],
)]<monad-table>

== The state monad

// ORDER: the two formulas first, since they are what the reader has and they look arbitrary; then the
// adjunction that makes them what they are (IntroString p. 96 points at the same connection).
For a fixed set `P` of states, IntroString p. 67 defines

  #align(center, block(inset: (y: 6pt))[
    `State A = (A × P)`#super[`P`] #h(1.1cm) `η A = curry (𝟙 : A × P ⟶ A × P)` #h(1.1cm)
    `μ A = (apply`#sub[`A × P`]`)`#super[`P`]
  ])

Both arrows come from the curry adjunction `L ⊣ R`, `L A = A × P` and `R B = B`#super[`P`]
(IntroString p. 96):

// `⊣` LOOKS LIKE A COMPOSITION AND IS NOT: `L ⊣ R` beside `State = R∘L` reads as two opposite orders
// in one paragraph, so the last row says once that it is no order at all.
- `State = R∘L`.
- `η` *is* the unit `Id ⇒ R∘L`, which is why it is the curried identity.
- the counit `ε : L∘R ⇒ Id` is `apply`.
- `μ = R∘ε∘L`, that counit with a functor on each side: in `μ A = (apply`#sub[`A × P`]`)`#super[`P`]
  the subscript `A × P` is `L A`, the functor INSIDE, and the outer `(−)`#super[`P`] is `R`, the
  functor OUTSIDE.
- `⊣` composes nothing; it only names the left adjoint first.

// OPEN and CLOSE, not "cup" and "cap": those are the drawing code's names for the bends of the
// Frobenius calculus every other picture here is made of, and reusing them would name two things once.
Applicative order stands `R` left and `L` right in `State = R∘L`. The identity functor is a region, so
a unit `Id ⇒ R∘L` has nothing above it and two wires below — one strand that OPENS the pair; a counit
`L∘R ⇒ Id` is that strand upside down, CLOSING a pair that arrives from above.

#disp[#align(center, stateops(ceta: GIVEN2, ceps: GIVEN1))]<state-ops>

In @state-ops, `State∘State` is the four wires `R L R L`, and `μ = R∘ε∘L` closes the middle pair — the
`L∘R` — leaving the outer `R` and `L`, which is `State` again. The two wires that run past the turn
untouched are the two functors composed on, `R` outside and `L` inside.

// THE DIAGONAL IS SOLID BLUE, NOT DASHED: dashed means "the unique arrow a universal property
// produces" everywhere else here, and `𝟙` is produced by nothing.  The `ε` bead is green because `μ = R ε L`.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (SA, SSA, SA2) = ((-3.2, 1.25), (3.2, 1.25), (3.2, -1.25))
    ar(SA, SSA, GIVEN2, s0: 1.0, s1: 2.3)
    ar(SSA, SA2, GIVEN1, s0: 0.55, s1: 0.55)
    // The only edge at an angle, so its trim is computed rather than copied: 1.15 along a slope of
    // −2.5/6.4 leaves the same tenth-of-a-unit gap the horizontal and vertical edges do.
    ar(SA, SA2, INDUCED, s0: 1.15, s1: 1.15)
    lab(0, 1.85, GIVEN2)[`η (State A)`]; lab(3.85, 0, GIVEN1)[`μ A`]
    lab(0, -0.55, INDUCED)[`𝟙`]
    node(SA.at(0), SA.at(1), black, `State A`); node(SSA.at(0), SSA.at(1), black, `State (State A)`)
    node(SA2.at(0), SA2.at(1), black, `State A`)
  }),
  unitlaw(ceta: GIVEN2, ceps: GIVEN1),
  [`(η∘State) μ = 𝟙`],
)]<state-unit>

@state-unit is the zig-zag. `η∘State` opens a new `R L` left of the pair already there and `μ` closes
the middle two — the new `L` against the old `R` — leaving the new `R` and the old `L`, which is
`State` unchanged. Strip the old `L`, which never moves, and what zig-zags is the curry adjunction's
snake equation `(η∘R)(R∘ε) = 𝟙` (IntroString p. 93): @monad-unit read at `State` is that triangle
identity with `L` composed on the inside.

In Set it is beta-reduction. `η (State A) f = λ x . (f, x)` pairs the computation with the state, and
`μ A` applies it back, `λ x . f x`, which is `f`.

#pagebreak(weak: true)
= Combinatorial functions <sec-comb>

// B&dM §5.6, p. 125, plus the three specifications of Ex 7.39–7.41 (p. 174).  Every composite is
// mirrored to diagram order, so B&dM's `prefix · suffix` is `suffix prefix` here.
#disp[#table(
  columns: (3.1cm, 7.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*note*]),

  [`list`],
  [`list A ::= nil | cons (A, list A)`],
  [B&dM's `listr` under the short name it keeps from p. 125 on.],

  [`subseq`],
  [`⦇[nil, cons ∪ outr]⦈`],
  [`xs subseq ys`: `ys` is `xs` with elements dropped — `cons` keeps the head, `outr` drops it.],

  [`prefix`],
  [`⦇[nil, nil ∪ cons]⦈ = cat° outl = init*`],
  [`ys` is an initial segment of `xs`; the first `nil` is where it stops early. `init ≜ snoc° outl`.],

  [`suffix`],
  [`cat° outr = tail*`],
  [The dual, `tail ≜ cons° outr`; as a catamorphism it needs snoc-lists.],

  [`segment`],
  [`suffix prefix`],
  [A contiguous stretch of `xs`: a suffix, then a prefix of that.],

  [`partition`],
  [`concat°`, #h(4pt) `concat ≜ ⦇[nil, cat]⦈`],
  [`cat` restricted to a non-empty first argument, so `ys` is a list of non-empty segments of `xs`.],

  [`inits`, `tails`],
  [implementations of $frac(#[`prefix`], ∋)$ and $frac(#[`suffix`], ∋)$],
  [`inits` by increasing length, `tails` by decreasing — opposite orders, which is what
   `splits ≜ ⟨inits, tails⟩ zip` needs to implement $frac(#[`cat°`], ∋)$.],

  [`filter(p)`],
  [$frac(#[`subseq list(p)`], ∋)$ `max R`, #h(4pt) `R ≜ length ≤ length°`],
  [The longest subsequence of `xs` whose every element passes `p`. `p` is a *coreflexive* and `list(p)`
   the relator applied to it, so `list(p)` is the test "every element passes" — no boolean anywhere.
   The longest is unique: only one subsequence keeps exactly the passing elements. The program is
   `⦇[nil, (outl p → cons, outr)]⦈`. #h(4pt) #src[Ex 7.41; `max R` is @min-defn]],

  [`takewhile(p)`],
  [$frac(#[`prefix list(p)`], ∋)$ `max R`],
  [The same with `prefix` for `subseq`: the longest prefix whose every element passes `p`. Unique,
   since the prefixes of one list are linearly ordered by length. #h(4pt) #src[Ex 7.39]],

  [`mss`],
  [$frac(#[`segment sum`], ∋)$ `max ≤`],
  [Maximum segment sum. `segment = suffix prefix` splits it into $frac(#[`prefix sum`], ∋)$ `max ≤`
   on each suffix, which the greedy theorem turns into a catamorphism. #h(4pt) #src[Ex 7.40]],
)]<comb-fns>

#pagebreak(weak: true)
= Optimisation Problems <sec-opt>

== Minimum and maximum <sec-min>

// B&dM §7.1, p. 166.  The `°` is what diagram order costs: it reverses the arrow but not the `≤`
// glyph, so without it `min ≤` would come out the greatest element.
#disp[#definition[
For `R : A ⟶ A`, #h(4pt) `min R ≜ ∋ ∩ (∈\R°) : E A ⟶ A`, #h(4pt) `max R ≜ min R°`.

`xs (min R) x ⟺ x ∈ xs ∧ (∀y ∈ xs. x R y)`

`xs (min R) x ⟺ (x in xs) and all x R\: xs` #h(4pt) #src[in q]

`min R = ∋ ∩ all R°` #h(4pt) #src[`all R ≜ ∈\R`, q's `all`; the chains below keep it written `∈\`]
]]<min-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X ⊑ min R ⟺ X ⊑ ∋` and `X° ∋ ⊑ R`], [in the set, and below every element of it],
  [$frac(#[`𝟙`], ∋)$ `(∈\R) = R`], [bounding a singleton is bounding its element],
  [$frac(#[`S`], ∋)$ `(∈\R) = S°\R`], [bound `S`'s image without building the set],
  [`union (∈\R) = ∈\(∈\R)` \ #src[`union ≜` $frac(#[`∋ ∋`], ∋)$ `: E(E A) ⟶ E A`]],
  [bound a union by bounding each member set],
  [$frac(#[`𝟙`], ∋)$ `min R = 𝟙 ∩ R`],
  [a singleton's minimum is its element, where `R` is reflexive \ #src[$frac(#[`S`], ∋)$ `min R` at `S := 𝟙`]],
  [$frac(#[`S`], ∋)$ `min R = S ∩ (S°\R°)`], [an `S`-value that points to every `S`-value],
  [$frac(#[`S`], ∋)$ `min R =` $frac(#[`S`], ∋)$ `min(R ∩ S° S)`], [only `R` between values `S` gives one argument counts — context],
  [`E(S) min R = (∋ S) ∩ ((∋ S)°\R°)`],
  [the same for the image of a set \ #src[$frac(#[`S`], ∋)$ `min R` at `S := ∋ S`]],
  [`P(f) min R = min(f R f°) f`], [shunt a function through a minimum],
  [`P(S) min R = (∋ S) ∩ (∈\(S R°))` \ #src[`R` reflexive]],
  [fusion with the power relator \ #src[`⊒` is the only proof here that tabulates]],
  [`P(S) min R ⊑ (∋ S) ∩ (∈\(S R°))`], [the half of the row above that costs nothing],
  [`P(min R) min R ⊑ union min R` \ #src[`R` a preorder]],
  [a minimum in each set, then a minimum of those],
  [`P(min R) min R = P(Dom (min R)) union min R` \ #src[`R` a preorder]],
  [the same as an equality, once empty sets are dropped],
)]<min-laws>

=== `X ⊑ min R ⟺ X ⊑ ∋` and `X° ∋ ⊑ R`

// The definition read through the two adjunctions it is built from.  B&dM p. 166 cites this as the
// hint "universal property of min"; the chains below cite it the same way.
#disp[
#zline(
  zsqc(`X`, `min R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zpair(zsqc(`X`, `∋`), zsqc(`X`, `∈\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zpair(zsqc(`X`, `∋`), zsqc(`∈ X`, `R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zpair(zsqc(`X`, `∋`), zsqc(`X° ∋`, `R`)),
)
]<min-up>

=== $frac(#[`𝟙`], ∋)$ `(∈\R) = R`

// B&dM (7.1): the same four steps as the subsection below, with `{·} ∋ = 𝟙` — the `i ⊣ E` triangle —
// where that one has `(S%∋) ∋ = S`.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`𝟙`], ∋)$ `(∈\R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`𝟙`], ∋)$`° X`], `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc([`∈` $frac(#[`𝟙`], ∋)$`° X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc([`(`$frac(#[`𝟙`], ∋)$` ∋)° X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`i⊣E`],
  zsqc(`X`, `R`),
)
]<min-71>

=== $frac(#[`S`], ∋)$ `(∈\R) = S°\R`

// B&dM (7.2): two adjunctions composed, `(S%∋) ∋ = S` collapsing the middle — the shape of (1.2a).
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `(∈\R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`S`], ∋)$`° X`], `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc([`∈` $frac(#[`S`], ∋)$`° X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc([`(`$frac(#[`S`], ∋)$ `∋)° X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`S° X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc(`X`, `S°\R`),
)
]<min-72>

=== `union (∈\R) = ∈\(∈\R)`

// B&dM (7.3): the shape of the two chains above with `union ∋ = ∋ ∋` in the middle.
#disp[
#zline(
  zsqc(`X`, `union (∈\R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc(`union° X`, `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc(`∈ union° X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc(`(union ∋)° X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`(∋ ∋)° X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`, `T·⊣T\`],
  zsqc(`X`, `∈\(∈\R)`),
)
]<min-73>

// Same reason as the hand-placed break further down: `sticky` cannot hold a heading to a BREAKABLE
// figure, and the extra heading level pushed this one to the foot of its page.
#pagebreak(weak: true)
=== $frac(#[`S`], ∋)$ `min R = S ∩ (S°\R°)`

// B&dM (7.5).  (7.4) is this at `S := 𝟙` and (7.7) at `S := ∋ S`, so neither needs a chain of its own.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `min R`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`S`], ∋)$`° X`], `min R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zpair(zsqc([$frac(#[`S`], ∋)$`° X`], `∋`), zsqc([$frac(#[`S`], ∋)$`° X`], `∈\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zpair(zsqc(`X`, [$frac(#[`S`], ∋)$ `∋`]), zsqc(`X`, [$frac(#[`S`], ∋)$ `(∈\R°)`])),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, @min-72],
  zpair(zsqc(`X`, `S`), zsqc(`X`, `S°\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zsqc(`X`, `S ∩ (S°\R°)`),
)
]<min-75>

=== $frac(#[`S`], ∋)$ `min R =` $frac(#[`S`], ∋)$ `min(R ∩ S° S)`

// B&dM (7.6): `X ⊑ S` already forces `S° X ⊑ S° S`, so the extra conjunct costs nothing — that is
// the whole content, and it is the middle step.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `min(R ∩ S° S)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[@min-75, `°`],
  zsqc(`X`, `S ∩ (S°\(R° ∩ S° S))`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`X`, `S`), zsqc(`S° X`, `R° ∩ S° S`)),
)
// Six boxes on one row squeezed the wide ones into three lines each; the break is at the pair.
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`, `S°·` monotone],
  zpair(zsqc(`X`, `S`), zsqc(`S° X`, `R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`, `Δ⊣∩`],
  zsqc(`X`, `S ∩ (S°\R°)`),
  zstep(op: sym.arrow.l.r.double, under: true)[@min-75],
  zsqc(`X`, [$frac(#[`S`], ∋)$ `min R`]),
)
]<min-76>

=== `P(f) min R = min(f R f°) f`

// B&dM (7.8), shunting a map through a minimum.  The one step that is not an adjunction is the
// modular law, and it needs `f` simple — the only such step in §18.
#disp[
#zline(
  zsqc(`P(f) min R`, none, name: "f a map"),
  zstep(op: sym.eq, under: true)[`P = E` on maps, @min-75],
  zsqc(`(∋ f) ∩ ((∋ f)°\R°)`, none),
  zstep(op: sym.eq, under: true)[`°`, `T·⊣T\`, `f°·⊣f·`],
  zsqc(`(∋ f) ∩ (∈\(f R°))`, none),
)
// An operator is stretched to the reason's UNWRAPPED width, so a reason squeezed onto two lines
// overhangs the boxes beside it; the breaks below keep each reason on one line.
#zline(
  zstep(op: sym.eq, under: true)[modular law, `f` simple],
  zsqc(`(∋ ∩ ((∈\(f R°)) f°)) f`, none),
  zstep(op: sym.eq, under: true)[`·f⊣·f°`, `°`, `min`],
  zsqc(`min(f R f°) f`, none),
)
]<min-78>

=== `P(S) min R = (∋ S) ∩ (∈\(S R°))`

// B&dM (7.9), `R` reflexive.  `⊑` is @min-710; `⊒` is the one place in §18 where a tabulation is
// unavoidable — `y` below is the set the right-hand side only describes.
#disp[#definition[
`(p, q)` tabulates `W ≜ (∋ S) ∩ (∈\(S R°))`, and #h(4pt) `y ≜` $frac(#[`(p ∋ S) ∩ (q R)`], ∋)$, a map.
]]<min-79-defn>

#disp[
#zline(
  zsqc(`W`, `P(S) min R`),
  zstep(op: sym.arrow.l.double, under: true)[`p° q = W`, `𝟙 ⊑ y y°`],
  zpair(zsqc(`p° y`, `P(S)`), zsqc(`y° q`, `min R`)),
)
]<min-79>

#disp[
#zline(
  zsqc(`y° q`, `∋`),
  zstep(op: sym.arrow.l.double, under: true)[`f°·⊣f·`, `·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`q`, `(p ∋ S) ∩ (q R)`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `f°·⊣f·`],
  // Only the LOWER box of a pair can carry a `name`: on the upper one it lands on the box below it.
  zpair(zsqc(`p° q`, `∋ S`), zsqc(`𝟙`, `R`, name: "R reflexive")),
)
#zline(
  zsqc(`∈ y° q`, `R°`),
  zstep(op: sym.arrow.l.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, `°`, meet],
  zsqc(`R° q° q`, `R°`, name: "q simple"),
)
]<min-79-min>

#disp[
#zline(
  zsqc(`p° y`, `P(S)`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `·T⊣/T`, `°`, `f°·⊣f·`],
  zpair(zsqc(`p° y ∋`, `∋ S`), zsqc(`p ∋`, `y ∋ S°`)),
)
#zline(
  zsqc(`p° y ∋`, `∋ S`),
  zstep(op: sym.arrow.l.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, meet],
  zsqc(`p° p ∋ S`, `∋ S`, name: "p simple"),
)
#zline(
  zsqc(`p ∋`, `y ∋ S°`),
  zstep(op: sym.arrow.l.double, under: true)[modular law],
  zsqc(`p ∋`, `(p ∋) ∩ (q R S°)`),
  zstep(op: sym.arrow.l.double, under: true)[`𝟙 ⊑ q q°`],
  zsqc(`q° p ∋`, `R S°`),
  zstep(op: sym.arrow.l.double, under: true)[`°`, `T·⊣T\`],
  zsqc(`W`, `∈\(S R°)`, name: "W's right half"),
)
]<min-79-pow>

// `sticky` keeps a heading with the display under it, but the display here is a breakable figure, so
// the heading still stranded itself at the foot of the page; the break is set by hand.
#pagebreak(weak: true)
=== `P(S) min R ⊑ (∋ S) ∩ (∈\(S R°))`

// B&dM (7.10): `∋` is lax natural for the power relator, `P(S) ∋ ⊑ ∋ S`, and with the universal
// property of `min` that is the whole proof.  The equality (7.9) is not this — it needs tabulations.
#disp[
#zline(
  zsqc(`P(S) min R`, `(∋ S) ∩ (∈\(S R°))`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(S) min R`, `∋ S`), zsqc(`∈ P(S) min R`, `S R°`)),
  zstep(op: sym.arrow.l.double, under: true)[UP of `min`],
  zpair(zsqc(`P(S) ∋`, `∋ S`), zsqc(`∈ P(S)`, `S ∈`)),
)
]<min-710>

=== `P(min R) min R ⊑ union min R`

// B&dM (7.11): (7.5) at `S := ∋ ∋` opens the right-hand side, then the same two facts as (7.10)
// close both strands — the left one twice, the right one against transitivity.
#disp[
#zline(
  zsqc(`P(min R) min R`, `union min R`, name: "R a preorder"),
  zstep(op: sym.arrow.l.r.double, under: true)[@min-75],
  zsqc(`P(min R) min R`, `(∋ ∋) ∩ ((∋ ∋)°\R°)`),
  zstep(op: sym.arrow.l.double, under: true)[`°`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(min R) min R`, `∋ ∋`), zsqc(`∈ ∈ P(min R) min R`, `R°`)),
  zstep(op: sym.arrow.l.double, under: true)[UP of `min`, `R` transitive],
  zpair(zsqc(`P(min R) ∋`, `∋ min R`), zsqc(`∈ P(min R)`, `min R ∈`)),
)
]<min-711>

=== `P(min R) min R = P(Dom (min R)) union min R`

// B&dM (7.12), `R` a preorder.  `⊑` puts the domain in for free; `⊒` is @min-79 at `S := min R`
// and then the two halves the book leaves as exercises.
#disp[
#zline(
  zsqc(`P(min R) min R`, none),
  zstep(op: sym.eq, under: true)[`Dom (min R) min R = min R`],
  zsqc(`P(Dom (min R) min R) min R`, none),
)
#zline(
  zstep(op: sym.eq, under: true)[`P` a relator],
  zsqc(`P(Dom (min R)) P(min R) min R`, none),
  zstep(op: sym.subset.eq.sq, under: true)[@min-711],
  zsqc(`P(Dom (min R)) union min R`, none),
)
]<min-712>

#disp[
#zline(
  zsqc(`P(Dom (min R)) union min R`, `P(min R) min R`),
  zstep(op: sym.arrow.l.double, under: true)[@min-79 at `S := min R`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(Dom (min R)) union min R`, `∋ min R`),
        zsqc(`∈ P(Dom (min R)) union min R`, `min R R°`)),
)
#zline(
  zsqc(`P(Dom (min R)) union min R`, `∋ min R`),
  zstep(op: sym.arrow.l.double, under: true)[`P(Dom (min R)) ⊑ 𝟙`],
  zsqc(`union min R`, `∋ min R`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`T(U ∩ V) ⊑ T U ∩ T V`, `·∋⊣`$frac(#box(width: 8pt), ∋)$, @min-73],
  zsqc(`(∋ ∋) ∩ (∈\(∈\R°))`, `∋ min R`),
  zstep(op: sym.arrow.l.double, under: true)[modular law],
  zsqc(`∋ (∋ ∩ (∈ (∈\(∈\R°))))`, `∋ (∋ ∩ (∈\R°))`, name: "counit of T·⊣T\\"),
)
#zline(
  zsqc(`∈ P(Dom (min R)) union min R`, `min R R°`),
  zstep(op: sym.arrow.l.double, under: true)[`∈` lax natural],
  zsqc(`Dom (min R) ∈ union min R`, `min R R°`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`Dom (min R) ⊑ min R (min R)°`],
  zsqc(`min R (min R)° ∈ union min R`, `min R R°`),
  zstep(op: sym.arrow.l.double, under: true)[`(min R)° ⊑ ∈`, `∈ ∈ union ⊑ ∈`],
  zsqc(`min R ∈ min R`, `min R R°`, name: "UP of min"),
)
]<min-712-geq>

#pagebreak(weak: true)
== Lax natural transformations

// B&dM §5.7, p. 133.  Same `⇒` the note gives an ordinary natural transformation: B&dM's own hooked
// arrow marks laxness, but the word already does, and the inequation is right there.
#disp[#definition[
`φ`#sub[`A`]` : G A ⟶ F A` is a *lax natural transformation* `φ : G ⇒ F` when, for every
`R : A ⟶ B`, #h(4pt) `G(R) φ ⊑ φ F(R)`. #h(4pt) #src[(5.13)]

`∋ : P ⇒ Id` — that is `P(R) ∋ ⊑ ∋ R`, @powrel-laws's first row at `X := P(R)`.

It is enough to check *maps*, and there it is an equality #h(4pt) `G(f) φ = φ F(f)`: #h(4pt) laxness
is about relations only. #h(4pt) #src[Theorem 5.2]
]]<lax-defn>

#disp[#capbox(
  cetz.canvas(length: 0.8cm, {
    let (GT, FT, GB, FB) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
    ar(GT, FT, GIVEN1, s0: 0.75, s1: 0.75); ar(GB, FB, GIVEN1, s0: 0.75, s1: 0.75)
    ar(GT, GB, GIVEN2, s0: 0.55, s1: 0.55); ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55)
    lab(0, 1.8, GIVEN1)[`φ`]; lab(0, -1.8, GIVEN1)[`φ`]
    lab(-3.8, 0, GIVEN2)[`G(R)`]; lab(3.8, 0, GIVEN2)[`F(R)`]
    lab(0, 0, SLACK, rot: -45deg)[`⊑`]
    node(GT.at(0), GT.at(1), black, `G A`); node(FT.at(0), FT.at(1), black, `F A`)
    node(GB.at(0), GB.at(1), black, `G B`); node(FB.at(0), FB.at(1), black, `F B`)
  }),
  [`G(R) φ ⊑ φ F(R)`],
)]<lax-str>

== Monotonic algebras

// B&dM §7.2, p. 172.  The section numbers no equation, so the table names its two theorems instead.
#disp[#definition[
An F-algebra `S : F A ⟶ A` is *monotonic on* `R : A ⟶ A` if #h(4pt) `F(R) S ⊑ S R`.

For a map `f : F A ⟶ A` that is #h(4pt) `f° F(R) f ⊑ R`, #h(4pt) equivalently #h(4pt) `F(R) ⊑ f R f°`.

`(≤ × ≤) + ⊑ + ≤` — addition on `Nat` is monotonic on `≤`, which at the point level
reads #h(4pt) `c = a + b ∧ a ≤ a' ∧ b ≤ b' ⟹ c ≤ a' + b'`.

`F(R) S ⊑ S R` is @lax-defn's inequation at `G := F`, `F := Id`, `φ := S`, so @mon-str is @lax-str
with `Id(R)` written `R`.
]]<mon-defn>

// @lax-str at `G := F`, `F := Id`, `φ := S`: the right edge's `Id(R)` is written `R`, and `S` stands where
// the lax transformation does.  `⊑` points NE — down-then-across is the smaller `F(R) S`.
#disp[#capbox(
  cetz.canvas(length: 0.8cm, {
    let (FT, T, FB, B) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
    ar(FT, T, GIVEN1, s0: 0.75, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.75, s1: 0.55)
    ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55); ar(T, B, GIVEN2, s0: 0.55, s1: 0.55)
    lab(0, 1.8, GIVEN1)[`S`]; lab(0, -1.8, GIVEN1)[`S`]
    lab(-3.75, 0, GIVEN2)[`F(R)`]; lab(3.35, 0, GIVEN2)[`R`]
    lab(0, 0, SLACK, rot: -45deg)[`⊑`]
    node(FT.at(0), FT.at(1), black, `F A`); node(T.at(0), T.at(1), black, `A`)
    node(FB.at(0), FB.at(1), black, `F A`); node(B.at(0), B.at(1), black, `A`)
  }),
  [`F(R) S ⊑ S R`],
)]<mon-str>

#disp[#definition[
`f : F A ⟶ A` *distributes over* `R` if #h(4pt) `F(min R) f ⊑` $frac(#[`F(∋) f`], ∋)$ `min R`.

`+` distributes over `≤`, at the point level #h(4pt)
`min xs + min ys = min{x + y ∣ x ∈ xs ∧ y ∈ ys}` #h(4pt) for `xs`, `ys` non-empty and
`min ≜ min ≤`.
]]<dist-defn>

// The `f` edges run across, as @mon-str's algebra does, so down-then-across is the smaller
// `F(min R) f` and `⊑` points NE.  Right: the same square at `F := (−×−)`, `f := +`, `R := ≤`.
#disp[#align(center, grid(columns: 2, align: horizon, column-gutter: 14pt,
  capbox(
    P(cetz.canvas(length: 0.8cm, {
      let (FEA, EA, FA, A) = ((-3.6, 1.25), (3.6, 1.25), (-3.6, -1.25), (3.6, -1.25))
      ar(FEA, EA, GIVEN1, s0: 1.05, s1: 0.65); ar(FA, A, GIVEN1, s0: 0.65, s1: 0.45)
      ar(FEA, FA, GIVEN2, s0: 0.55, s1: 0.55); ar(EA, A, GIVEN2, s0: 0.55, s1: 0.55)
      lab(0, 2.1, GIVEN1)[$frac(#[`F(∋) f`], ∋)$]; lab(0, -1.8, GIVEN1)[`f`]
      lab(-4.75, 0, GIVEN2)[`F(min R)`]; lab(4.4, 0, GIVEN2)[`min R`]
      lab(0, 0, SLACK, rot: -45deg)[`⊑`]
      node(FEA.at(0), FEA.at(1), black, `F(E A)`); node(EA.at(0), EA.at(1), black, `E A`)
      node(FA.at(0), FA.at(1), black, `F A`); node(A.at(0), A.at(1), black, `A`)
    }), s: 74%),
    [`F(min R) f ⊑` $frac(#[`F(∋) f`], ∋)$ ` min R`],
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
      lab(0, 2.75, GIVEN1)[$frac(#[`(∋ × ∋) +`], ∋)$]; lab(0, -2.5, GIVEN1)[`+`]
      lab(-6.75, 0, GIVEN2)[`min ≤ × min ≤`]; lab(5.75, 0, GIVEN2)[`min ≤`]
      lab(0, 0, SLACK, rot: -45deg)[`⊑`]
      vnode(FEA, `E Nat × E Nat`, `(xs, ys)`); vnode(EA, `E Nat`, `{x + y ∣ x ∈ xs ∧ y ∈ ys}`)
      vnode(FA, `Nat × Nat`, `(min xs, min ys)`); vnode(A, `Nat`, `min xs + min ys`)
    }), s: 74%),
    [`(min ≤ × min ≤) + ⊑` $frac(#[`(∋ × ∋) +`], ∋)$ ` min ≤`],
  ),
))]<dist-str>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`f° F(R) f ⊑ R ⟺ f° F(R°) f ⊑ R°`],
  [a *map* is monotonic on an order and on its opposite together — a relation is not],
  [`f° F(R) f ⊑ R ⟺ F(min R) f ⊑` $frac(#[`F(∋) f`], ∋)$ `min R` \ #src[Theorem 7.1, `f` a map]],
  [for a map the two definitions above are one condition],
  [`⦇`$frac(#[`S`], ∋)$ `min R⦈ ⊑` $frac(#[`⦇S⦈`], ∋)$ `min R` \ #src[Theorem 7.2, `R` a preorder and `F(R) S ⊑ S R`]],
  [the *greedy theorem*: keeping one minimum at every step beats no more than taking the minimum at
   the end],
)]<mon-laws>

== Planning a company party

// B&dM §7.3, p. 175.  No numbered equations; the two monotonicity claims are the section's own
// proof obligations, and the exercise blocks (7.43–7.44) are left out as everywhere else.
#disp[#definition[
`tree A ::= node (A, list(tree A))`, base functor `F(A, B) = A × list B`, `rating : Employee ⟶ Real`.

`cost ≜ list(rating) sum`, #h(4pt) `R ≜ cost ≤ cost°`, #h(4pt) `choose ≜ outl ∪ outr`.

`include ≜ (𝟙 × (list(outr) concat)) cons` #h(10pt) `exclude ≜ (𝟙 × (list(choose) concat)) outr`

`S ≜ ⟨include, exclude⟩`, #h(4pt) `party ≜ ⦇S⦈ choose : tree Employee ⟶ list Employee`
]]<party-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`party`], ∋)$ `max R`], [the specification: a guest list of greatest total conviviality],
  [`(R° × R°) choose ⊑ choose R°`], [`choose` is monotonic on `R°` — the first claim],
  [`(𝟙 × list(R° × R°)) S ⊑ S (R° × R°)`],
  [`S` is monotonic on `R° × R°` — the second claim],
  [$frac(#[`party`], ∋)$ `max R ⊒ ⦇`$frac(#[`S`], ∋)$ `max(R × R)⦈` $frac(#[`choose`], ∋)$ `max R`],
  [the greedy theorem: one best pair per subtree instead of all parties of the whole tree],
  [`party = ⦇S⦈` $frac(#[`choose`], ∋)$ `max R` \ `include = (𝟙 × (list(outr) concat)) cons` \
   `exclude = outr list(`$frac(#[`choose`], ∋)$ `max R) concat`],
  [the program, `exclude` renamed: `include` was already a map, and `exclude` becomes one],
)]<party-laws>

== Shortest paths on a cylinder

// B&dM §7.4, p. 179.  Its crux is Theorem 7.1, not the greedy theorem: `α` is a map, so monotonic
// gives distributes, which is (7.13) — the section's only numbered equation.
#disp[#definition[
`F(A, X) = A + A × X`, `L = list⁺` with initial algebra `α : F(A, L A) ⟶ L A`, `N` the `n`-tuple relator.

`R ≜ sum ≤ sum°`, #h(4pt) `setify : N A ⟶ E A`, #h(4pt) `moves : N A ⟶ E(N A)`, #h(4pt)
`trans : E(N A) ⟶ N(E A)`, #h(4pt) `zip : F(N A, N B) ⟶ N F(A, B)`, #h(4pt) `cp ≜` $frac(#[`F(𝟙, ∋)`], ∋)$.

`generate ≜ F(𝟙, moves trans N(union)) zip N(cp P(α)) : F(N A, N(E(L A))) ⟶ N(E(L A))`

`paths ≜ ⦇generate⦈ setify union : L N Nat ⟶ E(L Nat)`
]]<cyl-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`paths min R`], [the specification: a cheapest path across the cylinder],
  [`F(𝟙, min R) α ⊑ cp P(α) min R` \ #src[(7.13), Theorem 7.1 at the map `α`, using
   $frac(#[`F(𝟙, ∋) α`], ∋)$ `= cp P(α)`]],
  [extending every path in a set and then taking a minimum is beaten by extending one minimum],
  [`generate N(min R) ⊒ F(𝟙, N(min R)) Q`],
  [the fusion condition that defines `Q` — this is what (7.13) is spent on],
  [`Q = F(𝟙, moves trans N(min R)) zip N(α)` \ #h(4pt) `= [N(wrap),` \ #h(20pt)
   `(𝟙 × moves trans N(min R)) zip' N(cons)]`],
  [`generate` with the minimum taken inside each tuple component],
  [`paths min R ⊒ ⦇Q⦈ setify min R`], [the program: one fold, `n` best paths carried per column],
)]<cyl-laws>

== The security van problem

// B&dM §7.5, p. 184.  `Π`, the universal relation, is this note's `⊤`; the p. 187 printing of the
// greedy result puts `wrap wrap` where p. 185 and the final program both put `nil`.
#disp[#definition[
`R ≜ length ≤ length°`, #h(4pt) `ceiling ≜` $frac(#[`prefix sum`], ∋)$ `max ≤`, #h(4pt) `floor ≜` $frac(#[`prefix sum`], ∋)$ `min ≤`.

`secure` the coreflexive on `x` with `bmax(ceiling x, ceiling x − floor x) ≤ N`; #h(4pt) `ok` the
coreflexive on `(a, xs)` with `xs` non-empty and `[a] ⧺ head xs` secure.

`new ≜ (wrap × 𝟙) cons` #h(10pt) `glue ≜ (𝟙 × cons°) assocl (cons × 𝟙) cons`

`old ≜ (𝟙 × cons°) assocl ((cons secure) × 𝟙) cons`

`partition = ⦇[nil, new ∪ glue]⦈`, #h(4pt) `S ≜ [nil, new ∪ old]`, #h(4pt) `partition list(secure) = ⦇S⦈`.

`H ≜ (head prefix° head°) ∪ (nil° nil)`, #h(4pt) `R ; H ≜ R ∩ (R° ⇒ H)`, #h(4pt) `|R| ≜ R ∩ ¬R°`.
]]<van-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`partition list(secure)`], ∋)$ `min R`], [the specification: fewest secure segments],
  [`secure prefix ⊑ prefix secure`], [`secure` is prefix-closed — the only property of it used until
   the program],
  [`(𝟙 × R) new ⊑ (new ∪ old) R` \ #src[(7.14)]], [starting a new segment is monotonic on `R`],
  [`(𝟙 × R) old ⊑ (new ∪ old) R` \ #src[(7.15), FALSE]],
  [extending the first segment is not — the shorter partition need not stay secure],
  [`(𝟙 × (R ; H)) new ⊑ (new ∪ old) (R ; H)` #h(4pt) #src[(7.16)] \
   `(𝟙 × (R ; H)) old ⊑ (new ∪ old) (R ; H)` #h(4pt) #src[(7.17)]],
  [both halves do become monotonic once `R` is refined by `H`, which breaks a tie in length by the
   first segment's prefix order],
  [`(𝟙 × ⊤) new ⊑ new H` #h(6pt) #src[(7.18)]],
  [whatever the tail, `new`'s first segment is `[a]`, a prefix of every first segment — this is what
   (7.16) rests on],
  [`(𝟙 × ⊤) old ⊑ new H` #h(6pt) #src[(7.19)] \ `(𝟙 × |R|) old ⊑ new R` #h(6pt) #src[(7.20)] \
   `(𝟙 × (R ∩ H)) old ⊑ old (R ∩ H)` #h(6pt) #src[(7.21)]],
  [the three claims (7.17) rests on, split along \ `(R ; H) = |R| ∪ (R ∩ H)`],
  [`old ⊑ new (R ; H)°`], [`old` returns a shorter result than `new` if it returns any result at all,
   so the fold's choice refines to a map],
  [`⦇[nil, (ok → glue, new)]⦈ ⊑ ⦇`$frac(#[`S`], ∋)$ `min(R ; H)⦈`],
  [the program: glue onto the first segment while it stays secure, else start a new one],
)]<van-laws>

#pagebreak(weak: true)
= Thinning Algorithms <sec-thin>

== Thinning

// B&dM §8.1, p. 193.  Between the two extremes of the last section: `𝟙` keeps every partial solution
// and `min Q {·}` keeps one, `thin Q` keeps a representative collection.
#disp[#definition[
For `Q : A ⟶ A`, #h(4pt) `thin Q ≜ (∋/∋) ∩ (∈\(Q° ∈)) : E A ⟶ E A` #h(4pt) #src[(8.1)].

`ys (thin Q) xs ⟺ xs ⊆ ys ∧ (∀a ∈ ys. ∃b ∈ xs. b Q a)`
]]<thin-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X ⊑` $frac(#[`S`], ∋)$ `thin Q ⟺ X ∋ ⊑ S` and `S° X ⊑ Q° ∈`],
  [the universal property: everything kept is an `S`-value, and every `S`-value has a `Q`-lower bound
   among the kept ones],
  [`Q ⊑ R ⟹ thin Q ⊑ thin R`],
  [the fewer pairs `Q` relates, the fewer subsets count as thinnings],
  [`𝟙 ⊑ thin Q`, and `thin Q` is a preorder if `Q` is],
  [keeping everything is always a legal thinning],
  [`min R = thin Q min R` #h(4pt) #src[`Q ⊑ R`, both preorders]],
  [*thin-introduction*: thinning first cannot lose an `R`-minimum],
  [`thin Q ⊒ min Q` $frac(#[`𝟙`], ∋)$ #h(6pt) #src[(8.2)]],
  [*thin-elimination*: keeping one element is a thinning, but its domain is the sets `min Q` is
   defined on],
  [$frac(#[`S`], ∋)$ `thin Q ⊒` $frac(#[`S`], ∋)$ `min R` $frac(#[`𝟙`], ∋)$ \
   #src[(8.3), `R ∩ (S° S) ⊑ Q`]],
  [the usable variant: `R` need only refine `Q` between values `S` gives one argument],
  [`union thin Q ⊒ P(thin Q) union` #h(6pt) #src[(8.4)]],
  [thinning each member set is a thinning of the union],
  [`⦇`$frac(#[`F(∋) S`], ∋)$ `thin Q⦈ ⊑` $frac(#[`⦇S⦈`], ∋)$ `thin Q` \ #src[Theorem 8.1, `S` monotonic on `Q`]],
  [the *thinning theorem*: thinning at every step beats thinning only at the end],
  [`⦇`$frac(#[`F(∋) S`], ∋)$ `thin Q⦈ min R ⊑` $frac(#[`⦇S⦈`], ∋)$ `min R` \ #src[Corollary 8.1, `Q ⊑ R` as well]],
  [the same against the optimisation problem itself, by thin-introduction],
)]<thin-laws>

== Paths in a layered network

// B&dM §8.2, p. 196.  `Q` has to record `head` because `wt (a, head xs)` is unbounded: a dearer path
// with a nearer first vertex can still win.
#disp[#definition[
`F(A, X) = A + A × X`, #h(4pt) `L = list⁺` with initial algebra `α ≜ [wrap, cons] : F(A, L A) ⟶ L A`.

`wrapz ≜ ⟨wrap, zero⟩`, #h(4pt) `consw (a, (xs, n)) = (cons (a, xs), wt (a, head xs) + n)`.

`cost ≜ ⦇[wrapz, consw]⦈ outr`, #h(4pt) `⦇[wrapz, consw]⦈ = ⟨𝟙, cost⟩`, #h(4pt) `R ≜ cost ≤ cost°`.

`Q ≜ R ∩ (head head°)`, #h(4pt) `S ≜ F(𝟙, ∋) α`, #h(4pt) $frac(#[`F(∋, 𝟙)`], ∋)$ `= 𝟙 + cpl`, #h(4pt)
$frac(#[`F(𝟙, ∋)`], ∋)$ `= 𝟙 + cpr`, #h(4pt) `step ≜ cpr P(cons) min R`.
]]<path-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`⦇F(∋, 𝟙) α⦈`], ∋)$ `min R` #h(4pt) #src[`=` $frac(#[`L(∋)`], ∋)$ `min R`]],
  [the specification: a least-cost path across the network],
  [`F(∋, Q) α ⊑ F(∋, 𝟙) α Q`],
  [`S` is monotonic on `Q`; on `R` it is not, since the next edge can cost arbitrarily much],
  [`⦇`$frac(#[`F(∋, ∋) α`], ∋)$ `thin Q⦈ min R ⊑` $frac(#[`⦇F(∋, 𝟙) α⦈`], ∋)$ `min R` \ #src[Corollary 8.1]],
  [thinning applies: one partial path per starting vertex is enough],
  [`S head ⊑ [𝟙, outr]` \ #src[`S head` simple, so `R ∩ (S° S) ⊑ Q`]],
  [the side condition of (8.3): between two paths `S` builds from one argument, equal cost and equal
   head already means `Q`],
  [$frac(#[`F(∋, ∋) α`], ∋)$ `thin Q` \ #h(6pt) `⊒` $frac(#[`F(∋, 𝟙)`], ∋)$ `P(`$frac(#[`F(𝟙, ∋)`], ∋)$ `P(α) min R)` \
   #src[(8.4), (8.3), `P(`$frac(#[`𝟙`], ∋)$`) union = 𝟙`]],
  [thin eliminated: split the algebra at `F(∋, 𝟙) F(𝟙, ∋)`, thin each part, one minimum per part],
  [$frac(#[`F(𝟙, ∋)`], ∋)$ `P(α) min R = [wrap, step]`],
  [that inner part read off the two branches of `α`],
  [$frac(#[`⦇F(∋, 𝟙) α⦈`], ∋)$ `min R ⊒ ⦇[P(wrap), cpl P(step)]⦈ min R`],
  [the program: one fold, a best path per vertex of the current layer],
)]<path-laws>

// Same reason as the two hand-placed breaks in §18: `sticky` cannot hold a heading to a BREAKABLE
// figure, so this heading stranded itself at the foot of the page.
#pagebreak(weak: true)
== Implementing thin

// B&dM §8.3, p. 199.  Lemma 8.1 is printed with `R` where its own proof and Theorem 8.2 write `P`;
// it is one connected preorder, spelled `P` here.
#disp[#definition[
`setify : list A ⟶ E A`, #h(4pt) `cup : E A × E A ⟶ E A`, #h(4pt) `cp(F) ≜` $frac(#[`F(∋)`], ∋)$, #h(4pt)
`listcp(F) : F(list A) ⟶ list(F A)`, #h(4pt) `sort P ≜ setify° ordered P` for `P` a connected preorder.

`thinlist Q` is any `thinlist Q ⊑ subseq` with #h(4pt) `thinlist Q setify ⊑ setify thin Q`; #h(4pt)
one is #h(4pt) `⦇[nil, bump Q]⦈`, #h(4pt) `bump Q (a, []) = [a]`, #h(4pt)
`bump Q (a, [b] ⧺ xs) = (b Q a → [a] ⧺ xs, a Q b → [b] ⧺ xs, [a] ⧺ [b] ⧺ xs)`.

*Binary thinning* data: #h(4pt) `S = (f₁ p₁) ∪ (f₂ p₂)` with `p₁`, `p₂` coreflexive; #h(4pt) `Q` a
preorder with `Q ⊑ R` and both `f₁ p₁`, `f₂ p₂` monotonic on `Q`; #h(4pt) `P` a connected preorder
with both `f₁`, `f₂` monotonic on `P`; #h(4pt) `gᵢ ≜ list(fᵢ) filter(pᵢ)`.
]]<thinlist-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`thinlist Q xs = [minlist Q xs]` \ #src[(8.5), `Q` connected, `xs` non-empty]],
  [what thinning should come to when it can: one element],
  [`sort P thinlist Q ⊑ thin Q sort P` #h(6pt) #src[(8.6)]],
  [thinning a sorted list is a thinning of the set — this is what `thinlist Q ⊑ subseq` buys],
  [`sort P minlist Q ⊑ min Q` #h(6pt) #src[(8.7)]],
  [a minimum of the sorted list is a minimum of the set],
  [`sort(f P f°) list(f) ⊑ P(f) sort P` #h(6pt) #src[(8.8)]],
  [shunt a function through a sort],
  [`sort P filter(p) ⊑ E(p) sort P` #h(6pt) #src[(8.9), `p` coreflexive]],
  [filtering a sorted list sorts the restricted set],
  [`(sort P × sort P) merge P ⊑ cup sort P` #h(6pt) #src[(8.10)]],
  [merging two sorted lists sorts their union],
  [`F(sort P) listcp(F) ⊑ cp(F) sort(F P)` \ #src[(8.11), `F` linear]],
  [`listcp(F)` is the list implementation of the cartesian product `cp(F)`],
  [`F(sort P) listcp(F) list(f) filter(p) ⊑` $frac(#[`F(∋) f p`], ∋)$ `sort P` \ #src[Lemma 8.1, `f` monotonic on
   `P`, `p` coreflexive]],
  [one sorted list built from sorted arguments, instead of a set built and then sorted],
  [`⦇listcp(F) ⟨g₁, g₂⟩ merge P thinlist Q⦈ minlist R` \ #h(6pt) `⊑` $frac(#[`⦇S⦈`], ∋)$ `min R` \
   #src[Theorem 8.2]],
  [the *binary thinning theorem*: a fold on sorted lists of partial solutions, thinned at every step],
)]<thinlist-laws>

== The knapsack problem

// B&dM §8.4, p. 205.  The printed base of the final fold is `nil`, without the outer `wrap` that
// §8.5 and §8.6 do print (`wrap wrap wrap`, `start wrap`).
#disp[#definition[
`vol, wt : Item ⟶ Real`, #h(4pt) `value ≜ list(vol) sum`, #h(4pt) `weight ≜ list(wt) sum`.

`subseq = ⦇[nil, cons] ∪ [nil, outr]⦈`, #h(4pt) `within w` the coreflexive on `xs` with `weight xs ≤ w`.

`≥ ≜ ≤°`, #h(4pt) `R ≜ value ≥ value°`, #h(4pt) `Q ≜ R ∩ (weight ≤ weight°)`, #h(4pt) `P ≜ R`.

`F A = 1 + Item × A`, #h(4pt) `listcp(F) = wrap + cpr`, #h(4pt) `g₁ ≜ list([nil, cons]) filter(within w)`
#h(4pt) `= [list(nil), h₁]`, #h(4pt) `g₂ ≜ list([nil, outr]) = [list(nil), h₂]`.

`h₁ ≜ list(cons) filter(within w)`, #h(4pt) `h₂ ≜ list(outr)`.
]]<knap-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`subseq (within w)`], ∋)$ `min R`],
  [the specification: a selection of greatest total value that stays within the capacity `w`],
  [`subseq (within w) = ⦇([nil, cons] (within w)) ∪ [nil, outr]⦈` \ #src[fusion, weights non-negative]],
  [the selections that fit are themselves a fold, and the fold's algebra already has binary thinning's
   shape],
  [`(𝟙 × R) (cons (within w)) ⊑ cons (within w) R` \ #src[FALSE]],
  [not monotonic on `R`: a selection of greater value need not still fit once one more item goes in],
  [`(𝟙 × Q) (cons (within w)) ⊑ cons (within w) Q` \ `(𝟙 × Q) outr ⊑ outr Q`],
  [both halves are monotonic on `Q` once ties in value are broken by weight],
  [`⦇listcp(F) ⟨g₁, g₂⟩ merge R thinlist Q⦈ minlist R` \ #src[Theorem 8.2 at `P ≜ R`, `F` linear]],
  [binary thinning, sorting in descending order of value],
  [`knapsack w = ⦇[nil, cpr ⟨h₁, h₂⟩ merge R thinlist Q]⦈ minlist R`],
  [the program; `minlist R` becomes `head`, since packings come out in descending value],
)]<knap-laws>

// Stranded at the foot of its page for the same reason as the break above.
#pagebreak(weak: true)
== The paragraph problem

// B&dM §8.5, p. 207.  `P ≜ ⊤` works because `merge ⊤ = cat`, which already brings equal first lines
// together; the book's first choice `head prefix head°` is correct but not needed.
#disp[#definition[
`Line = list⁺ Word`, #h(4pt) `Para = list⁺ Line`, #h(4pt) `F A = Word + Word × A`, #h(4pt)
`listcp(F) = wrap + cpr`.

`new (a, xs) = [[a]] ⧺ xs`, #h(4pt) `glue (a, xs) = [[a] ⧺ head xs] ⧺ tail xs`, #h(4pt)
`partition ≜ ⦇[wrap wrap, new ∪ glue]⦈ : list⁺ Word ⟶ Para`.

`width ≜ ⦇[length, (length × 𝟙) plus succ]⦈`, #h(4pt) `fits w` the coreflexive on a line `x` with
`width x ≤ w`, #h(4pt) `ok w` the coreflexive on `[x] ⧺ xs` with `width x ≤ w`.

`white w x = w − width x`, #h(4pt) `collect ≜ list(sqr) sum`, #h(4pt) `waste w ≜ init list(white w) collect`.

`R ≜ (waste w) ≤ (waste w)°`, #h(4pt) `Q ≜ R ∩ (head head°)`, #h(4pt) `P ≜ ⊤`.

`g₁ ≜ list([wrap wrap, new])`, #h(4pt) `g₂ ≜ list([wrap wrap, glue]) filter(ok w)`, #h(4pt)
`start ≜ wrap wrap wrap`, #h(4pt) `h₁ ≜ list(new)`, #h(4pt) `h₂ ≜ list(glue) filter(ok w)`.
]]<para-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`partition list⁺(fits w)`], ∋)$ `min R`],
  [the specification: least waste among the paragraphs whose every line fits],
  [`partition list⁺(fits w) = ⦇[wrap wrap, new ∪ (glue (ok w))]⦈` \ #src[fusion, every word fits on a
   line by itself]],
  [the fitting paragraphs are themselves a fold],
  [`[wrap wrap, new ∪ (glue (ok w))]` \ #h(6pt) `= [wrap wrap, new] ∪ ([wrap wrap, glue] (ok w))`],
  [rewritten into binary thinning's shape `(f₁ p₁) ∪ (f₂ p₂)`],
  [`(𝟙 × R) glue ⊑ glue R` #h(6pt) #src[FALSE]],
  [`glue` is not monotonic on `R`: the waste of a paragraph depends on its whole first line, so no
   greedy algorithm solves this],
  [`(𝟙 × Q) new ⊑ new Q` \ `(𝟙 × Q) (glue (ok w)) ⊑ glue (ok w) Q` \ #src[`cons` monotonic on
   `collect ≤ collect°`]],
  [both halves are monotonic on `Q` once ties in waste are broken by the first line],
  [`merge ⊤ = cat`; #h(4pt) `P ≜ head prefix head°` also serves],
  [`⊤` needs no sorting at all, and `prefix` is a linear order on first lines of paragraphs of one
   input],
  [`⦇listcp(F) ⟨g₁, g₂⟩ cat thinlist Q⦈ minlist R` \ #src[Theorem 8.2 at `P ≜ ⊤`]],
  [binary thinning, one candidate kept per first line],
  [`paragraph w = ⦇[start, cpr ⟨h₁, h₂⟩ cat thinlist Q]⦈ minlist R`],
  [the program, `g₁` and `g₂` split along the coproduct],
)]<para-laws>

== Bitonic tours

// B&dM §8.6, p. 212.  `Q` records `next2`, not `head`: tours of one input already share their heads,
// and the cost of the next drop turns on the second city of each list.
#disp[#definition[
`F A = (City × City) + (City × A)`, the base functor of cons-lists of length at least two; #h(4pt)
`listcp(F) = wrap + cpr`; #h(4pt) `tc : City × City ⟶ Real`, neither positive nor symmetric.

`start (a, b) = ([a, b], [a, b])`, #h(4pt) `dropl (a, ([b] ⧺ xs, ys)) = ([a] ⧺ xs, [a] ⧺ ys)`, #h(4pt)
`dropr (a, (xs, [b] ⧺ ys)) = ([a] ⧺ xs, [a] ⧺ ys)`, #h(4pt) `tour ≜ ⦇[start, dropl ∪ dropr]⦈`.

`cost (xs, ys) = outcost xs + incost ys`, #h(4pt) `outcost [a₀, …, aₙ] = tc (a₀, a₁) + ⋯ + tc (aₙ₋₁, aₙ)`,
#h(4pt) `incost [a₀, …, aₙ] = tc (a₁, a₀) + ⋯ + tc (aₙ, aₙ₋₁)`.

`next ≜ tail head`, #h(4pt) `next2 ≜ next × next`, #h(4pt) `R ≜ cost ≤ cost°`, #h(4pt)
`Q ≜ R ∩ (next2 next2°)`, #h(4pt) `P ≜ ⊤`, #h(4pt) `g₁ ≜ list([start, dropl])`, #h(4pt)
`g₂ ≜ list([start, dropr])`.
]]<tour-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`tour`], ∋)$ `min R`],
  [the specification: a least-cost bitonic tour, outward journey and return kept as a pair of lists],
  [`(𝟙 × R) dropl ⊑ dropl R` #h(6pt) #src[FALSE] \ `(𝟙 × R) dropr ⊑ dropr R` #h(6pt) #src[FALSE]],
  [neither drop is monotonic on `R`: the two edges it adds and removes depend on `head` and `next`
   of both lists],
  [`(𝟙 × Q) dropl ⊑ dropl Q` \ `(𝟙 × Q) dropr ⊑ dropr Q`],
  [both are, once ties in cost are broken by the two second cities — the heads already agree among
   tours of one input],
  [`⦇listcp(F) ⟨g₁, g₂⟩ cat thinlist Q⦈ minlist R` \ #src[Theorem 8.2 at `P ≜ ⊤`, `merge ⊤ = cat`]],
  [binary thinning, one candidate per pair of second cities],
  [`mintour = ⦇[start wrap, cpr ⟨list(dropl), list(dropr)⟩ cat thinlist Q]⦈ minlist R`],
  [the program: quadratic, because each step adds just two tours to the list kept],
)]<tour-laws>

#pagebreak(weak: true)
= Dynamic Programming <sec-dp>

== Theory

// B&dM §9.1, p. 220.  @sec-opt's problem with the algebra cut down to a MAP `h`; the decompositions
// come from `⦇T⦈°`, and the recursion is over them rather than over an initial algebra.
#disp[#definition[
`h : F B ⟶ B` a map, #h(4pt) `T : F A ⟶ A` an F-algebra, #h(4pt) `R : B ⟶ B`.

`H ≜ ⦇T⦈° ⦇h⦈ : A ⟶ B`, #h(4pt) `M ≜` $frac(#[`H`], ∋)$ `min R` the problem to be solved, #h(4pt) `(μX : G(X))` the
least fixed point of `G`.
]]<dp-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(μX :` $frac(#[`T°`], ∋)$ `P(F(X) h) min R) ⊑ M` \ #src[Theorem 9.1, `h` monotonic on `R`]],
  [*dynamic programming*: decompose in every way, solve each part, keep one optimum per part],
  [$frac(#[`T°`], ∋)$ `P(F(M) h) min R ⊑ M` #h(6pt) #src[(9.1)]],
  [all Knaster–Tarski leaves to prove],
  [$frac(#[`T°`], ∋)$ `P(F(M) h) min R ⊑ H` #h(6pt) #src[(9.2)] \
   `H°` $frac(#[`T°`], ∋)$ `P(F(M) h) min R ⊑ R` #h(6pt) #src[(9.3)]],
  [(9.1) split by the universal property of `min`],
  [`P(X) min R ⊑ (∋ X) ∩ (∈\(X R°))` \ #src[(9.4) = (7.10), @min-laws]],
  [the only fact about `min` either proof uses],
  [`(μX :` $frac(#[`T°`], ∋)$ `thin Q P(F(X) h) min R) ⊑ M` \ #src[Theorem 9.2, `Q` a preorder with
   `Q F(H) h ⊑ F(H) h R`; `thin Q` as in @thin-laws]],
  [the same with a thinning step: decompositions that can never win are dropped],
  [the fixed point is unique, and entire \ #src[Theorem 6.3, `T°` followed by `F`'s membership
   relation inductive; $frac(#[`T°`], ∋)$ finite and non-empty, `R` connected]],
  [when the recursion can be refined to a recursive function],
  [$frac(#[`[V₁, V₂]°`], ∋)$ `thin(Q₁ + Q₂) P([U₁, U₂]) min R` \ #h(10pt) `= (Ran V₁ → W₁, W₂)` \ #h(10pt)
   `Wᵢ ≜` $frac(#[`Vᵢ°`], ∋)$ `thin(Qᵢ) P(Uᵢ) min R` \ #src[Proposition 9.1, `V₂ V₁° = ⊥`]],
  [`F A` is usually a coproduct, and disjoint ranges split the fixed point into one branch per
   summand],
  [`F(R) h ⊑ h R` \ `Q F(H) h ⊑ F(H) h R`],
  [the two conditions to be checked, in the order the three propositions below discharge them],
  [`F(R) h ⊑ h R` \ #src[Proposition 9.2, `R ≜ cost ≤ cost°`, `h cost = F(cost) k`,
   `F(≤) k ⊑ k ≤`]],
  [monotonicity when the cost is itself a fold with a step `k` monotonic on `≤`],
  [`F(R ∩ (H° H)) h ⊑ h R` \ #src[Proposition 9.3, `R ≜ cost ≤ cost°`,
   `h cost = F(⟨cost, H°⟩) k`, `F(≤ × 𝟙) k ⊑ k ≤`, `H°` simple]],
  [monotonicity *in context*: `k` may also read the input the part was built from],
  [`Q ≜ F(U, V)` \ #src[Proposition 9.4, `U`, `V` preorders, `F(U, R) h ⊑ h R`, `V H ⊑ H R`]],
  [both conditions of Theorem 9.2 at once, split along the two arguments of a bifunctor],
)]<dp-laws>

== The string edit problem

// B&dM §9.2, p. 225.  The section numbers no equation.  `base` and `step` are reused for the
// tabulating fold at the foot of the table; they are not `edit`'s.
#disp[#definition[
`Op ::= cpy Char ∣ del Char ∣ ins Char`, #h(4pt) `F(A, B) = 1 + (A × B)`, #h(4pt) `α ≜ [nil, cons]`.

`edit ≜ ⦇[base, step]⦈ : list Op ⟶ list Char × list Char`, #h(4pt) `base` returning `([], [])`,
#h(4pt) `step (cpy a, (xs, ys)) = ([a] ⧺ xs, [a] ⧺ ys)`, #h(4pt) `step (del a, (xs, ys)) = ([a] ⧺ xs, ys)`,
#h(4pt) `step (ins a, (xs, ys)) = (xs, [a] ⧺ ys)`.

`length ≜ ⦇[zero, outr succ]⦈`, #h(4pt) `R ≜ length ≤ length°`, #h(4pt) `U ≜ ⊤`, #h(4pt)
`V ≜ suffix° × suffix°`, #h(4pt) `Q ≜ 𝟙 + (U × V)`, #h(4pt) `empty` the coreflexive on `(xs, ys)` with
both lists empty.

`unstep` implements $frac(#[`step°`], ∋)$ `thin(U × V)`: #h(4pt) `unstep ([a] ⧺ xs, []) = [(del a, (xs, []))]`,
#h(4pt) `unstep ([], [b] ⧺ ys) = [(ins b, ([], ys))]`, #h(4pt)
`unstep ([a] ⧺ xs, [b] ⧺ ys) = (a = b → [(cpy a, (xs, ys))], [(del a, (xs, [b] ⧺ ys)), (ins b, ([a] ⧺ xs, ys))])`.
]]<edit-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`edit°`], ∋)$ `min R`],
  [the specification: a shortest edit sequence from which both strings can be reconstituted],
  [`F(R) α ⊑ α R` \ #src[Proposition 9.2 at `length`, `succ` monotonic on `≤`]],
  [`cons` is monotonic on `R`, so Theorem 9.1 already applies],
  [`Q F(𝟙, edit°) α ⊑ F(𝟙, edit°) α R`],
  [the thinning condition sought, over `F(Op, list Char × list Char)`],
  [`F(⊤, R) α ⊑ α R` #h(6pt) #src[left as an exercise]],
  [`U ≜ ⊤` costs nothing: any two operations may be compared],
  [`edit (𝟙 × suffix) ⊑ R° edit` \ `edit (suffix × 𝟙) ⊑ R° edit`],
  [the other half of Proposition 9.4 for `V ≜ suffix° × suffix°`],
  [`edit (𝟙 × tail) ⊑ R° edit` \ `edit (tail × 𝟙) ⊑ R° edit` \
   #src[`suffix = tail*`, and `B A ⊑ C B ⟹ B A* ⊑ C* B`]],
  [one step is enough: drop the operation that produced the head, or weaken its `cpy` to a `del` —
   never lengthening the sequence],
  [`(μX :` $frac(#[`[base, step]°`], ∋)$ `thin Q P([nil, (𝟙 × X) cons]) min R) ⊑` $frac(#[`edit°`], ∋)$ `min R` \
   #src[Theorem 9.2]],
  [a copy, when available, beats a delete or an insert],
  [`X = (empty → nil,` $frac(#[`step°`], ∋)$ `thin(U × V) P((𝟙 × X) cons) min R)` #h(4pt) #src[Proposition 9.1]],
  [`base` and `step` have disjoint ranges],
  [`mle = (empty → nil, unstep list((𝟙 × mle) cons) minlist R)`],
  [the program: at most two decompositions survive, but the same subproblem is solved many times,
   so the running time is exponential],
  [`column xs ys = [mle (u, ys) ∣ u ← tails xs]` \ `column xs = ⦇[fstcol xs, nextcol xs]⦈`, #h(4pt)
   `fstcol = list(del) tails`],
  [the tabulation: `mle (xs, ys)` needs `mle (u, v)` for every tail `u` of `xs` and `v` of `ys`, so the
   columns are built right to left],
  [`column xs ([b] ⧺ ys) = nextcol xs (b, column xs ys)` \
   `nextcol xs (b, us)` \ #h(10pt) `= ⦇[base (b, last us), step b]⦈ xus` \ #h(10pt)
   `xus = zip (xs, zip (init us, tail us))`],
  [each column is a fold built bottom to top, over `xs` zipped with the adjacent pairs of the column
   to its right],
  [`base (b, u) = [[ins b] ⧺ u]` \ `step b ((a, (u, v)), ws) =` \ #h(10pt)
   `(a = b → [[cpy a] ⧺ v] ⧺ ws,` \ #h(10pt) `[bmin R ([del a] ⧺ w, [ins b] ⧺ u)] ⧺ ws)` \
   #src[`w = head ws`; these `base`, `step` are not `edit`'s]],
  [an entry depends on the one below it (a delete), the one to its right (an insert), and the one
   below that (a copy) — quadratic in the two lengths],
)]<edit-laws>

== Optimal bracketing

// B&dM §9.3, p. 230.  `⦇T⦈ = flatten` is a map, so `H° = flatten` is simple and Proposition 9.3
// applies; no decomposition is preferable to another here, so there is no thinning step.
#disp[#definition[
`tree A ::= tip A ∣ bin (tree A, tree A)`, #h(4pt) `F X = A + X²`, so `F(R) = 𝟙 + R²`; #h(4pt)
`h ≜ [tip, bin]`, #h(4pt) `flatten ≜ ⦇[wrap, cat]⦈ : tree A ⟶ list⁺ A`, #h(4pt) `H = flatten°`.

`⟨cost, size⟩ ≜ ⦇[opt, opb]⦈`, #h(4pt) `opt ≜ ⟨zero, st⟩`, #h(4pt)
`opb ((cx, sx), (cy, sy)) = (cb (sx, sy) + cx + cy, sb (sx, sy))`.

`sb` associative, so `size = flatten sz` for a map `sz`; #h(4pt) `R ≜ cost ≤ cost°`, #h(4pt)
`g ≜ [zero, (𝟙 × sz)² opb outl]`, #h(4pt) `single` the coreflexive on singleton lists.

`splits ≜ ⟨inits⁺, tails⁺⟩ zip`, an implementation of $frac(#[`cat°`], ∋)$; #h(4pt) `array ≜ inits list(row)`,
#h(4pt) `row ≜ tails list(mct)`, #h(4pt) `col ≜ inits list(mct)`.

`mix ≜ zip list(bin) minlist R`, #h(4pt) `next ≜ ⟨outl, mix⟩ snoc`, #h(4pt)
`process ≜ ((tip wrap) × 𝟙) loop(next)`.
]]<mct-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`flatten°`], ∋)$ `min R`],
  [the specification: a least-cost bracketing of `a₁ ⊕ ⋯ ⊕ aₙ`, the tree whose flattening is the
   given list],
  [`[tip, bin] cost = (𝟙 + ⟨cost, flatten⟩²) g` #h(4pt) #src[(9.5)]],
  [the cost of a node reads only the cost and the flattening of its two subtrees],
  [`(𝟙 + (≤ × 𝟙)²) g ⊑ g ≤` #h(6pt) #src[(9.6)]],
  [`g` is monotonic on `≤` in its two cost arguments],
  [`F(R ∩ (flatten flatten°)) h ⊑ h R` \ #src[Proposition 9.3, `H° = flatten` a map]],
  [monotonicity in context: only trees with the same flattening are compared],
  [`(μX :` $frac(#[`[wrap, cat]°`], ∋)$ `P([tip, (X × X) bin]) min R) ⊑` $frac(#[`flatten°`], ∋)$ `min R` #h(4pt)
   #src[Theorem 9.1]],
  [split the list in every way, bracket both halves, join],
  [`X = (single → wrap° tip,` $frac(#[`cat°`], ∋)$ `P((X × X) bin) min R)` #h(4pt) #src[Proposition 9.1]],
  [`wrap` and `cat` have disjoint ranges],
  [`mct = (single → head tip, splits list((mct × mct) bin) minlist R)`],
  [the program; exponential, since the segments of one list overlap],
  [`mct = (single → head tip, ⟨init col, tail row⟩ mix)` #h(4pt) #src[(9.7)]],
  [the tabulation: `mct xs` is needed for every non-empty segment `xs`, so the values are held as an
   array of rows],
  [`col = (single → head tip wrap, ⟨init col, tail row⟩ next)` #h(4pt) #src[(9.8)] \
   `cons col = (𝟙 × array) process` #h(4pt) #src[(9.9)] \
   `row = (single → head tip wrap, ⟨mct, tail row⟩ cons)` #h(4pt) #src[(9.10)]],
  [a column extends the column to its left, a row the row below it; (9.9) is (9.8) rewritten as a
   loop],
  [`array = ⦇[fstcol, addcol]⦈`, #h(4pt) `fstcol ≜ tip wrap wrap` \
   `addcol ≜ ⟨outl tip wrap, step⟩ cons` \ `step ≜ ⟨process tail, outr⟩ zip list(cons)`],
  [the program: one fold building the array column by column, cubic in the length of the input],
)]<mct-laws>

== Data compression

// B&dM §9.4, p. 238.  Snoc-lists throughout.  No numbered equations, and no tabulation phase — the
// book stops at the recursive program and says the details are messy.
#disp[#definition[
`list A ::= nil ∣ snoc (list A, A)`, #h(4pt) `list⁺ A ::= wrap A ∣ snoc (list⁺ A, A)`, #h(4pt)
`String = list Char`, #h(4pt) `Code ::= sym Char ∣ ptr (String, String⁺)`, #h(4pt)
`F(Code, String) = 1 + (String × Code)`, #h(4pt) `α ≜ [nil, snoc]`.

`decode ≜ ⦇[nil, extend]⦈ : list Code ⟶ String`, #h(4pt) `extend (xs, sym a) = xs ⧺ [a]`, #h(4pt)
`extend (xs, ptr (ys, zs)) = xs ⧺ zs` when `ys ⧺ zs` is a proper prefix of `xs ⧺ zs`; #h(4pt)
`H = decode°`.

`size ≜ ⦇[zero, distr [𝟙 × c, 𝟙 × p] plus]⦈` with `c`, `p` the constant costs of a symbol and a
pointer; #h(4pt) `R ≜ size ≤ size°`, #h(4pt) `Q ≜ F(⊤ + ⊤, prefix°) = 𝟙 + (prefix° × (⊤ + ⊤))`, the
two `⊤` on symbols and on pointers.

`lrt ws = min(prefix° × (⊤ + ⊤)) {(xs, (ys, zs)) ∣ xs ⧺ zs = ws`, `ys ⧺ zs` a proper prefix of `ws}`,
the longest repeated tail; #h(4pt)
`reduce (ws ⧺ [a]) = (zs ≠ [] → [(ws, sym a), (xs, ptr (ys, zs))], [(ws, sym a)])` with
`(xs, (ys, zs)) = lrt (ws ⧺ [a])`.
]]<code-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`decode°`], ∋)$ `min R`],
  [the specification: a smallest code sequence decoding to the given string],
  [`F(R) α ⊑ α R` #h(6pt) #src[`(⊤ + ⊤) [c, p] = [c, p]`]],
  [monotonicity is routine, the two costs being constants],
  [`F(⊤ + ⊤, R) α ⊑ α R` \ `decode prefix ⊑ R° decode` \ #src[Proposition 9.4 at `Q ≜ F(⊤ + ⊤, prefix°)`]],
  [the thinning condition split in two: pointers are ordered only by how much input they consume,
   symbols and pointers not at all],
  [`decode init ⊑ R° decode`],
  [enough for the second: drop the last character of the output by shortening or removing the last
   code element, never raising the cost],
  [`(μX :` $frac(#[`[nil, extend]°`], ∋)$ `thin Q P([nil, (X × 𝟙) snoc]) min R) ⊑` $frac(#[`decode°`], ∋)$ `min R` \
   #src[Theorem 9.2]],
  [between a symbol and a pointer nothing can be decided in advance; between two pointers the longer
   match wins],
  [`X = (null → nil,` $frac(#[`extend°`], ∋)$ `thin(prefix° × (⊤ + ⊤)) P((X × 𝟙) snoc) min R)` \
   #src[Proposition 9.1]],
  [`nil` and `extend` have disjoint ranges],
  [$frac(#[`extend°`], ∋)$ `(ws ⧺ [a]) = {(ws, sym a)} ∪` \ #h(10pt)
   `{(xs, ptr (ys, zs)) ∣ xs ⧺ zs = ws ⧺ [a]`, `ys ⧺ zs` a proper prefix of `ws}`],
  [the decompositions of one string: take the last character as a symbol, or end with a pointer],
  [`reduce` implements $frac(#[`extend°`], ∋)$ `thin(prefix° × (⊤ + ⊤))`],
  [thinning leaves at most two: the symbol, and the pointer of `lrt`],
  [`encode = (null → nil, reduce list((encode × 𝟙) snoc) minlist R)`],
  [the program, again exponential; the book gives no tabulation for it],
)]<code-laws>

#pagebreak(weak: true)
= Greedy Algorithms <sec-greedy>

== Theory

// B&dM §10.1, p. 245.  Theorem 9.2 with `min Q` for `thin Q`: the same hypotheses, a much stronger
// conclusion, and one far harder to refine into a program.
#disp[#definition[
`h`, `T`, `R`, `H`, `M` as in @dp-defn; #h(4pt) additionally `Q` a *connected* preorder on the sets
$frac(#[`T°`], ∋)$ returns, so that $frac(#[`T°`], ∋)$ `min Q` is entire.
]]<greedy-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(μX :` $frac(#[`T°`], ∋)$ `min Q F(X) h) ⊑ M` \ #src[Theorem 10.1, the hypotheses of Theorem 9.2]],
  [*greedy*: one decomposition is kept at every step, so `P` and $frac(#box(width: 8pt), ∋)$ disappear from the recursion],
  [$frac(#[`[V₁, V₂]°`], ∋)$ `min(Q₁ + Q₂) [U₁, U₂]` \ #h(10pt) `= (Ran V₁ → W₁, W₂)` \ #h(10pt)
   `Wᵢ ≜` $frac(#[`Vᵢ°`], ∋)$ `min(Qᵢ) Uᵢ` \ #src[Proposition 10.1, `V₂ V₁° = ⊥`]],
  [Proposition 9.1 with `min` for `thin`],
  [`Q ≜ F(U, V)` #h(6pt) #src[Proposition 9.4]],
  [still the way to get both conditions, but $frac(#[`T°`], ∋)$ `min Q` must now be entire as well],
  [#src[Theorem 7.2, @mon-laws]],
  [that greedy theorem chooses among the *results* of one relational step of a catamorphism;
   Theorem 10.1 chooses among the *decompositions* of the input, for an arbitrary `T` rather than an
   initial algebra, at the cost of `h` being a map],
)]<greedy-laws>

== The detab-entab problem

// B&dM §10.2, p. 246.  `V ≜ prefix° ∩ (fill fill°)` is the whole trick: a bare `prefix°` fails because
// a prefix of the expansion can be longer than the input once it crosses a tab stop.
#disp[#definition[
`detab ≜ ⦇[nil, expand]⦈ : String ⟶ String` over snoc-lists, #h(4pt) `α ≜ [nil, snoc]`, #h(4pt)
`H = detab°`; #h(4pt) `expand (xs, a) = (a = TB → fill xs, xs ⧺ [a])`, #h(4pt)
`fill xs = xs ⧺ blanks (n − (col xs) mod n)`.

`col ≜ ⦇[zero, count]⦈`, #h(4pt) `count (c, a) = (a = NL → 0, c + 1)`; #h(4pt) `TB` the tab, `BL` the
blank, `NL` the newline, tab stops every `n` columns.

`R ≜ length ≤ length°`, #h(4pt) `U` the preorder with `a U b ⟺ a = TB ∨ a = b`, #h(4pt)
`V ≜ prefix° ∩ (fill fill°)`, #h(4pt) `Q ≜ 𝟙 + (V × U)`.

`unfill xs` the shortest prefix of `xs` with `fill (unfill xs) = fill xs`; #h(4pt) `tbc` the trailing
blank count, #h(4pt) `triple ≜ ⟨unfill entab, ⟨tbc, col⟩⟩`.
]]<entab-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`detab°`], ∋)$ `min R`],
  [the specification: a shortest input `detab` expands to the given output — `detab entab = 𝟙` and
   nothing shorter does],
  [`F(⊤, R) α ⊑ α R` #h(6pt) #src[left as an exercise]],
  [`U` may be any preorder on characters; `a U b ⟺ a = TB ∨ a = b` puts `TB` below every character, so `min` prefers
   a tab to a blank],
  [`detab prefix ⊑ R° detab` #h(6pt) #src[FALSE]],
  [at `n = 8`, `detab [a,b,c,d,e,TB] = [a,b,c,d,e,BL,BL,BL]`, whose prefix `[a,b,c,d,e,BL,BL]` is
   longer than any input giving it],
  [`detab V° ⊑ R° detab` #h(6pt) #src[`V ≜ prefix° ∩ (fill fill°)`]],
  [true once only the prefixes that do not cross a tab stop are allowed],
  [`nil V° = nil` #h(10pt) `fill V° = fill` \ `snoc V° ⊑ snoc ∪ (outl V°)` #h(6pt) #src[left as exercises]],
  [the three properties of `V` the derivation rests on; the second is what `fill fill°` was added for],
  [`expand V° ⊑ expand ∪ (outl V°)`],
  [the claim they add up to: shortening the output either leaves the last step alone or discards it],
  [`detab V° ⊑ detab ∪ (init detab V°)` \ #src[`init` inductive, so the greatest solution is the unique
   one]],
  [hence `detab V° ⊑ prefix detab`, and `prefix ⊑ R°` finishes Proposition 9.4],
  [`(μX :` $frac(#[`[nil, expand]°`], ∋)$ `min Q (𝟙 + (X × 𝟙)) [nil, snoc]) ⊑` $frac(#[`detab°`], ∋)$ `min R` \
   #src[Theorem 10.1]],
  [greedy: one character of input is decided at each step],
  [`X = (null → nil,` $frac(#[`expand°`], ∋)$ `min(V × U) (X × 𝟙) snoc)` #h(4pt) #src[Proposition 10.1]],
  [`nil` and `expand` have disjoint ranges],
  [$frac(#[`expand°`], ∋)$ `(xs ⧺ [a]) = {(ys, TB) ∣ fill ys = xs ⧺ [a]} ∪ {(xs, a)}` \ #h(6pt)
   the first set is non-empty iff `a = BL` and `col (xs ⧺ [a]) mod n = 0`],
  [the last output character came from a tab only if it is a blank landing exactly on a tab stop],
  [$frac(#[`expand°`], ∋)$ `min(V × U) (xs ⧺ [a]) =` \ #h(10pt)
   `(a = BL ∧ col (xs ⧺ [a]) mod n = 0 → (unfill xs, TB), (xs, a))`],
  [the greedy step: emit a tab whenever a tab is legal, consuming all the blanks back to the previous
   tab stop],
  [`entab xs = entab (unfill xs) ⧺ blanks (tbc xs)` #h(4pt) #src[(10.1)]],
  [what makes `triple` a snoc-list catamorphism: the output splits at the last tab stop],
  [`triple = ⦇[base, op]⦈` and `entab = triple assocl outl (𝟙 × blanks) cat`],
  [the program: one pass carrying the column and the count of pending blanks],
  [`base` returns `([], (0, 0))` \ `op ((xs, (t, c)), a) =` \ #h(10pt)
   `(a = BL ∧ (c + 1) mod n ≠ 0 → (xs, (t + 1, c + 1)),` \ #h(10pt)
   `a = BL → (xs ⧺ [TB], (0, c + 1)),` \ #h(10pt)
   `a = NL → (xs ⧺ blanks t ⧺ [NL], (0, 0)),` \ #h(10pt)
   `(xs ⧺ blanks t ⧺ [a], (0, c + 1)))`],
  [hold a blank back, cash the held blanks in for a tab at a tab stop, flush them at a newline,
   flush them before anything else],
)]<entab-laws>

== The minimum tardiness problem

// B&dM §10.3, p. 253.  Both conditions need context, and `cost` has to be restated over `perm xs`
// before Proposition 9.3 fits — `penalty` reads the bag of scheduled jobs, not their order.
#disp[#definition[
`F X = 1 + (X × Job)`, #h(4pt) `α ≜ [nil, snoc]` on schedules, #h(4pt) `β ≜ [nil, snag]` on bags,
`snag` putting a job into a bag; #h(4pt) `bagify ≜ ⦇β⦈ : list Job ⟶ Bag Job`, #h(4pt) `H = bagify°`.

`ct`, `dt`, `wt : Job ⟶ Real` the completion, due and weighting quantities of a job; #h(4pt)
`penalty (xs, j) = (sum (list(ct) xs) + ct j − dt j) × wt j`.

`cost ≜` $frac(#[`prefix`], ∋)$ `P(α° [zero, penalty]) max ≤`, #h(4pt) `cost [] = 0`, #h(4pt)
`cost (xs ⧺ [j]) = bmax (cost xs, penalty (xs, j))`, #h(4pt) `R ≜ cost ≤ cost°`.

`perm ≜ bagify bagify° = ⦇[nil, add]⦈`, #h(4pt) `add (xs, j) = ys ⧺ [j] ⧺ zs` for some `xs = ys ⧺ zs`.

`k ≜ [zero, assocr (𝟙 × ((bagify° × 𝟙) penalty)) bmax]`, #h(4pt)
`f ≜ [zero, (bagify° × 𝟙) penalty]`, #h(4pt) `Q ≜ f ≤ f°`.
]]<tardy-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`bagify°`], ∋)$ `min R`],
  [the specification: an ordering of the given bag of jobs with least maximum penalty],
  [`F(R ∩ (bagify bagify°)) α ⊑ α R` #h(4pt) #src[(10.2)]],
  [monotonicity in context — only schedules of one bag are compared],
  [`(Q ∩ (β β°)) F(bagify°) α ⊑ F(bagify°) α R` #h(4pt) #src[(10.3)]],
  [the greedy condition, also in context],
  [`cost (xs ⧺ [j]) = bmax (cost xs, penalty (perm xs, j))` \ `α cost = F(⟨cost, bagify⟩) k`, #h(4pt)
   `F(≤ × 𝟙) k ⊑ k ≤` \ #src[Proposition 9.3]],
  [(10.2): `penalty` sums the completion times of `xs`, and a sum does not see the order],
  [`α cost = ⟨g, h⟩ bmax` #h(4pt) #src[(10.4)] \ `g ≜ [zero, penalty]` #h(4pt) #src[(10.5)] \
   `h ≜ [zero, outl cost]` #h(4pt) #src[(10.6)]],
  [the cost of a schedule split into the penalty of its last job and the cost of the rest],
  [`add ⊑ outl R` #h(6pt) #src[(10.7)] \ `β bagify° = F(bagify°) [nil, add]` #h(6pt) #src[(10.8)]],
  [adding a job never lowers the cost; and `bagify°` is itself a catamorphism on bags. Together:
   `β bagify° ⊑ F(bagify°) h ≤ cost°`],
  [`F(bagify) Q° F(bagify°) = g ≥ g°`, met by \ `Q ≜ f ≤ f°`, `f ≜ [zero, (bagify° × 𝟙) penalty]`],
  [the specification `Q` has to satisfy, and the choice that meets it: a `Q`-minimum is a job of
   least penalty],
  [no greedy *catamorphism* exists],
  [a greedy snoc-list catamorphism would also solve every prefix of the input, and the best schedule
   of a prefix need not extend to a best schedule of the whole],
  [`X = (null → nil,` $frac(#[`snag°`], ∋)$ `min Q (X × 𝟙) snoc)` #h(4pt) #src[Theorem 10.1, Proposition 10.1]],
  [`nil` and `snag` have disjoint ranges],
  [`schedule = (null → nil, pick (schedule × 𝟙) snoc)` \ #src[`pick ⊑` $frac(#[`snag°`], ∋)$ `min Q`, a partial
   function]],
  [the program: repeatedly remove a job of least penalty and put it last; quadratic in the number of
   jobs],
)]<tardy-laws>

== The TeX problem

// B&dM §10.4, p. 259.  The section's `h` is `⦇[arb, step]⦈`, which is `H°`, not §21.1's algebra `h`.
// The book prints the base case of `f` as `a < 0` on p. 262 and as `p ≤ 0` in the program.
#disp[#definition[
`intern ≜ val round : Decimal ⟶ [0, 2¹⁶)`, #h(4pt) `val ≜ ⦇[zero, shift]⦈`, #h(4pt)
`shift (d, r) = (d + r)/10`, #h(4pt) `round r` rounds `2¹⁶ r` to the nearest integer:
`round r = n ⟺ 2n − 1 < 2¹⁷ r < 2n + 1`.

`interval n = ((2n − 1)/2¹⁷, (2n + 1)/2¹⁷)`, #h(4pt) `r inrange (a, b) ⟺ a < r < b`, #h(4pt)
`round° = interval inrange`, #h(4pt) `R ≜ length ≤ length°`.

`Interval` the pairs `(a, b)` with `0 < b < 1` and `a < b` #h(4pt) #src[(10.9)]; #h(4pt)
`[arb, step] : 1 + (Digit × Interval) ⟶ Interval`, #h(4pt)
`step (d, (a, b)) = ((d + a)/10, (d + b)/10)`.

`F X = 1 + (Digit × X)`, #h(4pt) `α ≜ [nil, cons]`, #h(4pt) `h ≜ ⦇[arb, step]⦈ = H°`, #h(4pt)
`! : Digit × Interval ⟶ 1`, #h(4pt) `Q ≜ (ιₗ° !° ιᵣ) ∪ 𝟙`, #h(4pt) `w ≜ 2¹⁷`.
]]<tex-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [$frac(#[`intern°`], ∋)$ `min R = interval` $frac(#[`inrange val°`], ∋)$ `min R`],
  [the specification: a shortest decimal whose internal representation is the given multiple of
   `2⁻¹⁶`. `round°` is not a map, but `interval` is, so it comes out of the $frac(#box(width: 8pt), ∋)$],
  [`val inrange° = ⦇[arb, step]⦈` \ #src[fusion; `zero inrange° = arb`,
   `shift inrange° = (𝟙 × inrange°) step`]],
  [the converse of `val`, cut down to intervals, is a catamorphism on cons-lists],
  [`F(R) α ⊑ α R`],
  [`cons` is monotonic on `R` — routine],
  [`α° F(h) Q° ⊑ R° α° F(h)`],
  [the greedy condition of Theorem 10.1, converted],
  [$frac(#[`arb°`], ∋)$ `(a, b) = (a < 0 → {*}, {})` \
   $frac(#[`step°`], ∋)$ `(a, b) = {(d, (10a − d, 10b − d)) ∣ 0 < 10b − d < 1}`],
  [the decompositions of an interval: stop, or take one more digit],
  [`0 < 10b − d₁ < 1` and `0 < 10b − d₂ < 1` imply `d₁ = d₂`],
  [`step°` is in fact a map, `d` the digit with `0 < 10b − d < 1`, so $frac(#[`[arb, step]°`], ∋)$ returns at
   most two elements and `Q` need only choose between them],
  [`Q ≜ (ιₗ° !° ιᵣ) ∪ 𝟙`, and `! nil ⊑ cons R°` \ #src[from `! nil length ⊑ cons length ≥`]],
  [stop whenever stopping is legal: the empty decimal is shorter than any other],
  [`(μX :` $frac(#[`[arb, step]°`], ∋)$ `min Q F(X) α) ⊑` $frac(#[`intern°`], ∋)$ `min R` #h(4pt) #src[Theorem 10.1]],
  [greedy: emit the one digit the interval allows, until the interval contains zero],
  [`extern = interval f` \ `f (a, b) = (a < 0 → [], [d] ⧺ f (10a − d, 10b − d))`],
  [the program, with `d` the digit above],
  [`extern n = f (2n − 1, 2n + 1)` \
   `f (p, q) = (p ≤ 0 → [], [d] ⧺ f (10p − w d, 10q − w d))` \ #src[`d = (10q) div w`, `w = 2¹⁷`]],
  [the same in integer arithmetic only, as chapter 3 required of `intern`: every interval reached is
   `(p/w, q/w)`],
)]<tex-laws>
