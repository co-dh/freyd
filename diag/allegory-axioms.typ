// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name (see circuit.typ's header); `dot` is renamed on the way in for that reason.
#import "circuit.typ": conv, meet, wire, bend, gbox, dot as wiredot, tape, tape-fork, tape-join, TINT
// draw.typ owns the Hinze–Marsden geometry (Catamorphism, Monad) and every helper this note draws with:
// it is also the standalone PNG of those laws, and one geometry drawn in two files is one that drifts.
#import "draw.typ": homeq, beadeq, twobeadeq, TCOL, BCOL, CCOL, monadops, monadunit, monadassoc, stateops, unitlaw, lamsnake, lamfuse, lamabsorb, snake, snaketri, zpal, GIVEN1, GIVEN2, INDUCED, SLACK, fb-MAPC, fb-ALLC, fb-ZC, fb-WALL, fb-FILL, IY, ADMIRES, HATES, WORKS, ADMIRERS, HATERS, PEOPLE, LX, AD, BD, LY, lab, ar, node, nodes, ings, edges, arc, head, e, fb-dot, fb-rule, fb-wire, fb-region, fb-wall, fb-sing, syqnode, syqedge, domstr, pairstr, zwire, zw, zsq, zsqc, zstep, znamed, zderiv, zline, zpair, skel, yset, capbox, pair
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
#import "generated/Freyd.Alg.symmDiv.typ": pic as p-symmdiv
#import "generated/Freyd.Alg.symmDiv_recip.typ": pic as p-sdiv-recip
#import "generated/Freyd.Alg.symmDiv_comp.typ": pic as p-sdiv-comp
// §2.314's list, in the book's order.
#import "generated/Freyd.Alg.div_comp.typ": pic as p-div-comp
#import "generated/Freyd.Alg.one_le_div_self.typ": pic as p-one-div
#import "generated/Freyd.Alg.div_self_comp_self.typ": pic as p-div-self-idem
#import "generated/Freyd.Alg.div_self_comp.typ": pic as p-div-self
#import "generated/Freyd.Alg.div_one.typ": pic as p-div-one
#import "generated/Freyd.Alg.div_union.typ": pic as p-div-union
#import "generated/Freyd.Alg.leftDiv_div.typ": pic as p-ldiv-div

#show: conf.with(title: "The allegory axioms, and what defines them in the Frobenius calculus")

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

  [`i ⊣ E`], [`Map ↪ Rel`], [`P`], [`{·}:A⟶P A`], [`∋:P B⟶B`], [—], [—], [`Λ(∋)=𝟙`], [`Λ(R)∋=R`],

  // The row above at the HOM-SET level, and the table's only bijection that is not an ORDER-iso:
  // `Λ` is not monotone, and monotone would force every hom-poset discrete.
  [`·∋ ⊣ Λ`], [`Map(A,P B) ⟶` \ `(A⟶B)`], [`𝟙`], [`Λ(f∋)=f`], [`Λ(R)∋=R`], [—], [—], [`Λ(f∋)∋` \ `=f∋`], [`Λ(Λ(R)∋)` \ `=Λ(R)`],

  [`Λ ⊣ ·∋`], [`(A⟶B) ⟶` \ `Map(A,P B)`], [`𝟙`], [`Λ(R)∋=R`], [`Λ(f∋)=f`], [—], [—], [`Λ(Λ(R)∋)` \ `=Λ(R)`], [`Λ(f∋)∋` \ `=f∋`],
)]<adj-all>

// Row parameters: `S`/`f` are `B ⟶ C` in the `·S`, `·f` rows and `A ⟶ B` in the `S·`, `f°·` ones;
// `Cor A` is the coreflexives on `A`, so the `A`, `B` of the `𝓓`, `𝓡` rows are coreflexives.

== Composing adjunctions <sec-compose>

One more adjunction first, which §@sec-adj cannot hold because it is ANTITONE — its left adjoint turns
joins into meets, so that table's `F` preserves `∪` column would read the wrong way; its type is
contravariant, `F : (B⟶C)^op ⟶ (A⟶B)`, so the `F`'s type column cannot be written in §@sec-adj's form
either; and BOTH composites are inflationary, `𝟙⊑FG` and `𝟙⊑GF`, so the `GF⊑𝟙` column has no entry
for it at all. That last is the signature of an antitone Galois connection — two closure operators
rather than a closure and an interior — and the table's own *both units* cell is it:

// Proved as `le_div_iff` then `le_leftDiv_iff`.
#disp[#table(
  columns: 3, align: left + horizon, inset: 4pt, stroke: 0.4pt + luma(190),
  table.header([*`F ⊣ G`*], [*the law*], [*both units*]),
  [`R/ ⊣ \R`], [`T⊑R/S` iff `S⊑T\R`], [`S⊑(R/S)\R`, `T⊑R/(T\R)`],
)]<div-antitone>

Two rows of §@sec-adj composed are a third adjunction, and its right adjoint read in the two orders is a
law. Row first, column second; right adjoints compose the other way round, which is where every
reversal in the table comes from.

The table's `⟜◁` row and column need a name for that row's left adjoint, and §@sec-adj gave it none:
write `R^` for the operator listed there, `R ↦ (𝟙⊗⟜◁)(R⊗𝟙)`.

#disp[#block(inset: (y: 6pt))[
  `R : X⊗A ⟶ Y` #h(1.4cm) `R^ = (𝟙⊗⟜◁)(R⊗𝟙) : X ⟶ Y⊗A`
]]<bend-type>

// HAND-DRAWN, and allowed to be: `R^` is a definition, with no Lean declaration to export from.  ONE
// canvas — two side by side would centre on their own boxes and put the two `R` boxes at different heights.
#disp[#box(inset: (y: 6pt), cetz.canvas(length: 0.8cm, {
  let GLOW = (thickness: 4.5pt, paint: TINT, cap: "round")
  let bent(glow) = {
    let seg(a, b) = if glow { d.line(a, b, stroke: GLOW) } else { wire(a, b) }
    let arc(a, b) = {
      let mx = a.at(0) + (b.at(0) - a.at(0)) * 0.6
      if glow { d.bezier(a, b, (mx, a.at(1)), (mx, b.at(1)), stroke: GLOW) } else { bend(a, b) }
    }
    // `⟜` then `◁`, drawn split: the pair of `A`s is opened out of nothing and one of them is fed
    // back into the box it came out beside.
    seg((4.76, -0.76), (5.1, -0.76))
    arc((5.1, -0.76), (5.7, -0.42)); seg((5.7, -0.42), (6.1, -0.42))
    arc((5.1, -0.76), (5.7, -1.1)); seg((5.7, -1.1), (7.7, -1.1))
    if not glow { wiredot((4.76, -0.76)); wiredot((5.1, -0.76)) }
  }
  // `R` itself: `X` and `A` in, `Y` out.
  wire((0, 0.42), (0.9, 0.42)); wire((0, -0.42), (0.9, -0.42))
  gbox((0.9, 0), [R], h: 1.5); wire((1.82, 0), (2.4, 0))
  lab(-0.35, 0.42, black)[$X$]; lab(-0.35, -0.42, black)[$A$]; lab(2.75, 0, black)[$Y$]
  // `R^`: the same box, the `A` wire bent round to the other side.  Glow first, then the black
  // strand, then the box — each pass covers the round cap the pass before it left in the way.
  bent(true); bent(false)
  wire((4.6, 0.42), (6.1, 0.42))
  gbox((6.1, 0), [R], h: 1.5); wire((7.02, 0), (7.7, 0))
  lab(4.25, 0.42, black)[$X$]; lab(8.05, 0, black)[$Y$]; lab(8.05, -1.1, black)[$A$]
}))
#align(center, src[left `R`, right `R^`: the pale strand is everything the bend adds, and the box
and the `X`, `Y` wires are where they were.])]<bend-pic>

In `Rel` the two are one set of triples split two ways — the bend moves the `A` coordinate from the
input side to the output side:

#disp[#block(inset: (y: 6pt))[`x R^ (y,a) ⟺ (x,a) R y`]]<bend-rel>

Read `Rel(I,J)` as an `I×J` boolean matrix — Freyd's §2.111, which defines reciprocation entrywise
as `j R° i = i R j` — and `R^` is the smallest of three degrees of bending, all of the same
`R : X⊗A ⟶ Y`:

#disp[#table(
  columns: 4, align: left + horizon, inset: 4pt, stroke: 0.4pt + luma(190),
  table.header([], [*what moves*], [*type*], [*as a matrix*]),
  [`R^`], [one index, to the output side], [`X ⟶ Y⊗A`],
    [rows re-indexed from `(x,a)` to `x`, columns from `y` to `(y,a)`],
  [`R°`], [the input index goes out and the output index comes in
    #src[drawn in the `°` section below]], [`Y ⟶ X⊗A`], [the transpose],
  [`⌜R⌝`], [everything, to the output side — the *name* of `R`], [`𝕀 ⟶ Y⊗A⊗X`],
    [the whole matrix flattened into one row],
)]<bend-degrees>

All three carry the same entries; only the split of the indices into row and column changes. That is
what a matrix transpose always was — moving an index from the domain side to the codomain side — and
compact closure is the structure that permits the move: `Rel` is self-dual, `A* = A`, so there is no
up/down index distinction to keep track of.

#src[Of the three, only `^` is this note's own, the half bend having no settled symbol. `⌜R⌝` and
its mirror the *coname* `⌞R⌟ : Y⊗A⊗X ⟶ 𝕀` are the literature's. Neither is the transpose `Λ` of
B&dM, which is Freyd's §2.421 `R/S = Λ(R)Λ°(S)` as well: that one sends `R : X⊗A ⟶ Y` to a MAP
`Λ(R) : X⊗A ⟶ P Y`, and needs a power allegory rather than compact closure.]

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
`/f°` does not collapse in turn, and the three operators stay distinct. On `Rel(𝕀, A) = P A` they
are the image triple:

#disp[#table(
  columns: 3, align: left + horizon, inset: 4pt, stroke: 0.4pt + luma(190),
  table.header([*operator*], [*acts by*], [*name*]),
  [`·f`], [`S ↦ f[S]`], [direct image, `∃_f`],
  [`·f°`], [`T ↦ f⁻¹[T]`], [inverse image, `f*`],
  [`/f°`], [`S ↦ {b : f⁻¹(b) ⊆ S}`], [`∀_f`],
)]<triple-image>

§@sec-adj's `𝓓 ⊣ ·⊤` is this same chain along the projection `A⊗B ⟶ A`, read through
`Rel(A, B) = P(A⊗B)`: `𝓓R = {(a,a) : ∃b. aRb}`, `A⊤` is the relation that ignores `b`
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


== `R/R` is a preorder, which is what a monad is here

A *monad* in a locally posetal 2-category is a 1-cell `M` with `𝟙 ⊑ M` and `M M ⊑ M` — a unit and a
multiplication, and with the hom-posets thin there is nothing else to give. In `Rel` that is a
reflexive transitive relation: a preorder. The table above proves both halves at `M := R/R`, and
names the preorder they define.

`(R/R) R = R` is then the action that makes `R` a module over that monad — Hinze and Marsden's
α : M ∘ A →̇ A (IntroString p. 83) at M := `R/R`, A := `R`. Their two
coherence conditions are free here: parallel 2-cells are unique, so any two of them are equal.

// Hand-drawn one dimension up — region an object, wire a relation, dot a 2-cell — read bottom to top.
// `R/R` is an endo-wire on `X`, so the SAME fill lies on both sides: that is a monad, not a missing colour.
#disp[#box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
  d.rect((-1.7, -1.2), (1.7, 1.2), fill: fb-ALLC, stroke: none)
  d.rect((-1.7, -1.2), (0.5, 1.2), fill: fb-MAPC, stroke: none)
  // `R` runs the full height: it is the wire the action lands ON, and landing on it changes nothing.
  d.line((0.5, -1.2), (0.5, 1.2), stroke: 1.1pt)
  d.bezier((-0.6, -1.2), (0.5, 0.15), (-0.6, -0.3), (0.0, 0.15), stroke: 1.1pt)
  fb-dot((0.5, 0.15), `α`, dx: 0.32)
  lab(-0.6, -1.48, black)[`R/R`]; lab(0.5, -1.48, black)[`R`]; lab(0.5, 1.48, black)[`R`]
  lab(-1.3, 0.7, luma(80))[$X$]; lab(1.1, 0.7, luma(80))[$P$]
}))

#align(center, src[Green is `X`, where `x` lives; purple is `P`, where the `p` of the definition
lives. `R/R : X ⟶ X` runs inside `X` and ends on `R : X ⟶ P` at the action `α`, which is
`(R/R) R ⊑ R`.])]<div-monad-cell>

== The whole family is one preorder

#disp[#box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
  d.rect((-1.9, -1.2), (1.9, 1.2), fill: fb-MAPC, stroke: none)
  d.merge-path(close: true, fill: fb-ZC, stroke: none, {
    d.line((1.9, -1.2), (0.9, -1.2))
    d.bezier((0.9, -1.2), (0.0, 0.15), (0.9, -0.35), (0.4, 0.15))
    d.line((0.0, 0.15), (0.0, 1.2)); d.line((0.0, 1.2), (1.9, 1.2))
  })
  d.merge-path(close: true, fill: fb-ALLC, stroke: none, {
    d.line((-0.9, -1.2), (0.9, -1.2))
    d.bezier((0.9, -1.2), (0.0, 0.15), (0.9, -0.35), (0.4, 0.15))
    d.bezier((0.0, 0.15), (-0.9, -1.2), (-0.4, 0.15), (-0.9, -0.35))
  })
  d.bezier((-0.9, -1.2), (0.0, 0.15), (-0.9, -0.35), (-0.4, 0.15), stroke: 1.1pt)
  d.bezier((0.9, -1.2), (0.0, 0.15), (0.9, -0.35), (0.4, 0.15), stroke: 1.1pt)
  d.line((0.0, 0.15), (0.0, 1.2), stroke: 1.1pt)
  wiredot((0.0, 0.15))
  lab(-0.9, -1.48, black)[`R/S`]; lab(0.9, -1.48, black)[`S/W`]; lab(0.0, 1.48, black)[`R/W`]
  lab(-1.45, -0.5, luma(80))[$X$]; lab(0.0, -0.75, luma(80))[$Y$]; lab(1.45, -0.5, luma(80))[$Z$]
}))

#align(center, src[The same dot with one region more: `R/S : X ⟶ Y` and `S/W : Y ⟶ Z` come in,
`R/W : X ⟶ Z` goes out. Green `X`, purple `Y`, amber `Z`.])]<div-polyad-cell>

Closing `Y` off is the mid-point `y` being quantified away; the `⊑` rather than `=` is the loss the
figure for that law above already draws.

Concretely in `Rel`, `𝟙 ⊑ R/R` and `(R/S)(S/W) ⊑ R/W` are one preorder on the disjoint union of
`X`, `Y`, `Z`, …: reflexivity is `𝟙 ⊑ R/R` inside a block, transitivity is `(R/S)(S/W) ⊑ R/W` across
blocks.

Abstractly the same two are a *lax functor* out of the codiscrete category on `{R, S, W, …}` — one
object per relation, exactly one arrow each way — sending `R` to `X`, the object its rows are indexed
by, and the arrow `R → S` to `R/S : X ⟶ Y`. That is Bénabou's *polyad* (Bénabou 1967, Def. 5.5), of
which a monad is the one-object case: the subsection above is this one at `R = S = W`.

`R/S` is at the same time a bimodule between the two monads `R/R` and `S/S`: `(R/R)(R/S) ⊑ R/S` and
`(R/S)(S/S) ⊑ R/S`, each the counit `(R/S) S ⊑ R` with one action composed on — `(R/R) R = R` on the
left, `(S/S) S = S` on the right.

#pagebreak(weak: true)
= `x (Admires%Hates) y` is `x admires only all whom y hates`

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

A meet of two long divisions, the second turned round by the converse frame:

#disp[#P(p-symmdiv, s: 66%)
#align(center, src[exported from the definition, not transcribed])]<syq-frobenius>

#disp[#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [$(frac(R, S))^circle.small = frac(S, R)$ \ #src[Matching is symmetric.]],
  P(p-sdiv-recip),

  [$frac(R, S) frac(S, W) ⊑ frac(R, W)$ \ #src[And transitive.]],
  P(p-sdiv-comp),
)]<syq-laws>

No pictures for the rest of §2.35: symmetric division is not built from the generators.

#disp[#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [$X ⊑ frac(R, S) ⟺ X S ⊑ R$ and `X° R ⊑ S`],
  [`X` may pair `x` with `y` only when `x` admires exactly whom `y` hates. Both halves must typecheck,
   so the operation is *partial*.],

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

== Straight

#disp[#definition[
`S` is *straight* when $frac(S, S) = 𝟙$ — no two `y`s hate the same people.
]]<straight-defn>

#disp[#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [every symmetric `X` with `X S ⊑ S` is coreflexive],
  [Equivalently, `S` is straight.],

  [`f S = g S ⟹ f = g`],
  [A straight `S` tells its `y`s apart, so it cancels on the right.],

  [`S R` straight `⟹ S` straight],
  [If the longer chain tells them apart, the first step already does.],

  [`S` straight `⟺ R/S` simple for all `R`],
  [If no two `y`s agree, at most one `x` can match a given `y`.],

  [`R = h S`, `h` a cover, `S` straight],
  [In an effective division allegory every arrow factors that way.],
)]<straight-laws>

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
  [$(#e[R] slash #e[R]) ∩ (#e[R] slash #e[R])^circle.small ⊑ 𝟙$], [$#e[R]$ is *straight*],
))

`R □` is `R`'s target, an identity arrow. For `R : A ⟶ B` write `∋ : P B ⟶ B`, dropping the
subscript.
]]<pow-defn>

#disp[#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [$#e[R] □ = R □$, #h(4pt) $#e[R] = #e[R □]$],
  [`∋` has the same target as `R`, and replacing `R` by the identity at that target leaves it
   unchanged: one `∋` per object, not per arrow.],

  [`∋` is *thick*],
  [*Comprehension*: every `x` has a set of exactly the people `x` admires. Equivalently every `R`
   factors as a map followed by `∋`.],

  [`∋` is *straight*, that is $frac(∋, ∋) ⊑ 𝟙$],
  [*Extensionality*: two sets with the same people are the same set.],
  [],[],
 [`Λ(R) ≜` $frac(R, ∋)$ ` : A ⟶ P B`, for `R : A ⟶ B` ],
 [convert a relation to a function. `a Λ(R) = {b|a R b}`, image of a ], 
  [`Λ(R)` is simple],
  [`∋` is straight, and dividing by a straight arrow is simple. At most one set per `x`.],

  [`Λ(R)` is entire `⟺ ∋` thick],
  [`Dom` $frac(R, ∋)$ `= 𝟙 ∩ (R/∋)(∋/R)`, the domain row above. At least one set per `x`, so
   `Λ(R)` is a *map*.],

  // The wall stands OUTSIDE the box here, unlike `Λ(∋) = 𝟙`'s: `∋` follows `Λ(R)` rather than sitting
  // inside it, so its name goes above, clear of the box's own `P`.
  [`Λ(R) ∋ = R` ], [Drawn in §@sec-adj-E, where it is the counit's cancellation.],

  [`Λ(R)` is the only map with `Λ(R) ∋ = R`],
  [Two maps naming the same people name the same set — extensionality again.],

  [`F ⊑ Λ(F ∋)`, `F` simple],
  [A partial choice of sets is inside the total one.],

  [`P A` ≜ source of `∋`, the *power-object*],
  [Notation, not a law: `∋` goes `P A ⟶ A`, and `P A` is simply a name for where it starts. Every
   subset of `A`.],

  [`{·} ≜ Λ(𝟙)`, the *singleton map*, monic],
  [The one-person set. `Λ(𝟙)Λ°(𝟙) ⊑` $frac(𝟙, ∋) frac(∋, 𝟙) ⊑ frac(𝟙, 𝟙) ⊑ 𝟙$.],

  [`Λ(∋) = 𝟙`],
  [Make the set of a set, then read it back one level down. Straightness itself, and one of the two
   snake laws of §@sec-adj-E; the other is `{·} ∋ = 𝟙`.],

  [*fusion:* `Λ(f R) = f Λ(R)`, `f` a map],
  [Naturality of the unit, `f {·} = {·} (E(f))`, and that is the whole content of fusion. Drawn in
   §@sec-adj-E.],

  [`Λ(f) = f {·}`, `f` a map],
  [Rename first or take singletons first — the fusion row above at `R = 𝟙`.],

  [$frac(R, S) = Λ(R) Λ^circle.small (S)$],
  [`x` and `y` match exactly when `Λ(R)x` and `Λ(S)y` are one and the same set.],

  [`E(R) ≜ Λ(∋ R)` ], [`E(R): P A ⟶ P B`, image of a set of A],
  [`Λ(R) = {·} E(R)`], [{·}: x ↦ {x} ],
  [`Λ(S) E(R) = Λ(S R)`], [absorption ],

  [`subset ≜ ∋/∋ : P A ⟶ P A`],
  [`x subset y ⟺ ∀a. y ∋ a → x ∋ a`, that is `y ⊆ x`: diagram order reverses B&dM's argument order
   along with the arrow. It *models* inclusion between sets, where `⊑` is the allegory's own
   primitive comparing arrows (B&dM p. 106).],
)]<pow-laws>

#pagebreak(weak: true)
= `i ⊣ E` <sec-adj-E>

// `existsImage` and `existsImage_eps`, AOP/A4_6.lean:90 and :94; `E(𝟙) = 𝟙`, `E(R S) = E(R) E(S)` at
// :106 and :111.  B&dM's `P` is the power relator section below, and `E` is what makes the slide an equality.
`E(R) ≜ Λ(∋ R)` is Bird & de Moor's *existential image* (p. 105), and it is the right adjoint of the
inclusion `i : Map(𝒜) ↪ 𝒜`: `Λ` is the transpose, so `𝒜(A, B) ≅ Map(A, P B)`.

#disp[#table(
  columns: (4.6cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*part of `i ⊣ E`*], [*the statement*]),

  [`∋` the counit, natural], [`E(R) ∋ = ∋ R`],
  [`{·}` the unit, natural], [`f {·} = {·} E(f)`, for `f` a map],
  [`Λ` the transpose], [`Λ(R) ∋ = R`, and `Λ(R)` the only map with it],
  [`·∋` the transpose back], [`{·} ∋ = 𝟙` and `Λ(∋) = 𝟙`, the two triangles],
)]<adj-lean>

// Trim the diagonal at 0.5, not the 1.15 Catamorphism's squares use: those clear a wide node box, and `B` is
// one glyph.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (A, PB, B) = ((-3, 1.25), (3, 1.25), (3, -1.25))
    ar(A, PB, INDUCED, dash: "dashed", s0: 0.55, s1: 0.7)
    ar(PB, B, GIVEN1, s0: 0.55, s1: 0.55)
    ar(A, B, GIVEN2, s0: 0.5, s1: 0.5)
    lab(0, 1.85, INDUCED)[`Λ(R)`]; lab(3.55, 0, GIVEN1)[`∋`]; lab(-0.2, -0.75, GIVEN2)[`R`]
    node(A.at(0), A.at(1), black, `A`); node(PB.at(0), PB.at(1), INDUCED, `P B`)
    node(B.at(0), B.at(1), black, `B`)
  }),
  lamsnake(),
  [`Λ(R) ∋ = R` \ and `Λ(R)` is the only *map* with that property],
)]<adj-E>

// The two triangle identities, `i` first: horizontal order is applicative, so `E∘i` stands `E` left,
// and the pair `{·}` opens lands on the incoming wire's right in one picture and its left in the other.
#disp[#pair(
  grid(columns: 2, column-gutter: 14pt, align: horizon,
    snaketri(`i`, `i E i`, `i∘{·}`, `∋∘i`), snaketri(`E`, `E i E`, `{·}∘E`, `E∘∋`)),
  grid(columns: 2, column-gutter: 14pt, align: horizon,
    snake(`i`, `E`, false), snake(`E`, `i`, true)),
  [`{·} ∋ = 𝟙` #h(1.6cm) `Λ(∋) = 𝟙`],
)]<adj-E-snakes>

#pagebreak(weak: true)
== Fusion law <sec-fusion>

// `f` is the ONE arrow both halves carry, so it is GIVEN1 in both; the square has no `{·}` and no `R`,
// which is the whole reason the string diagram stands beside it.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (C, A, PB) = ((-2.6, 1.25), (2.6, 1.25), (2.6, -1.25))
    ar(C, A, GIVEN1, s0: 0.4, s1: 0.4)
    ar(A, PB, INDUCED, dash: "dashed", s0: 0.4, s1: 0.7)
    ar(C, PB, INDUCED, dash: "dashed", s0: 0.4, s1: 0.7)
    lab(0, 1.85, GIVEN1)[`f`]; lab(3.5, 0, INDUCED)[`Λ(R)`]; lab(-0.1, -0.8, INDUCED)[`Λ(f R)`]
    node(C.at(0), C.at(1), black, `C`); node(A.at(0), A.at(1), black, `A`)
    node(PB.at(0), PB.at(1), INDUCED, `P B`)
  }),
  lamfuse(),
  [`Λ(f R) = f Λ(R)`, `f` a map],
)]<adj-E-fusion>

// The two panels are the SAME STROKES, which is the law: the square's two routes are one picture.
#disp[#pair(
  cetz.canvas(length: 0.8cm, {
    let (C, PA, PB) = ((-2.6, 1.25), (2.6, 1.25), (2.6, -1.25))
    ar(C, PA, INDUCED, dash: "dashed", s0: 0.4, s1: 0.7)
    ar(PA, PB, GIVEN1, s0: 0.7, s1: 0.7)
    ar(C, PB, INDUCED, dash: "dashed", s0: 0.4, s1: 0.7)
    lab(0, 1.85, INDUCED)[`Λ(S)`]; lab(3.6, 0, GIVEN1)[`E(R)`]; lab(-0.1, -0.8, INDUCED)[`Λ(S R)`]
    node(C.at(0), C.at(1), black, `C`); node(PA.at(0), PA.at(1), INDUCED, `P A`)
    node(PB.at(0), PB.at(1), INDUCED, `P B`)
  }),
  lamabsorb(),
  [`Λ(S R) = Λ(S) E(R)`, for `S : C ⟶ A` and `R : A ⟶ B`],
)]<adj-E-absorb>

#disp[#table(
  columns: (5.6cm, 4.2cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*scan line*], [*the object on it*], [*the bead just passed*]),

  [the top edge], [`C`], [—],
  [between `{·}` and `S`], [`i E C` `=` `P C`], [`{·} : C ⟶ P C`],
  [between `S` and `R`], [`i E A` `=` `P A`], [`S`, inside the pair, so `E(S) : P C ⟶ P A`],
  [the bottom edge], [`i E B` `=` `P B`], [`R`, likewise `E(R) : P A ⟶ P B`],
)]<absorb-scan>

One string of beads, two groupings:

- The first two, then the third: `{·} E(S) = Λ(S) : C ⟶ P A` followed by `E(R) : P A ⟶ P B`.
- All three at once: `{·} E(S) E(R) = {·} E(S R) = Λ(S R) : C ⟶ P B`.

Absorption holds for every `S`, so fusion is its case `S := f`, plus one step: absorption there reads
`Λ(f R) = Λ(f) E(R)`, and turning `Λ(f) E(R)` into `f Λ(R)` needs `Λ(f) = f {·}`, which is
@adj-E-fusion at `R = 𝟙`. That step is the unit's naturality, and it is all fusion adds.

== `Λ(R) = (R/∋) ∩ (∋/R)°`

// B&dM p. 107, in diagram order.  A row too wide for the column wraps, and the next row opens with
// the `⟺` that carries it over; the two strands of rows 2 stay one above the other throughout.
#disp[
#zline(
  zsqc(`g° f`, `Λ(R)`, name: "f, g maps"),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°· ⊣ f·`],
  zsqc(`f`, `g Λ(R)`, eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[fusion],
  zsqc(`f`, `Λ(g R)`, eq: true),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋ ⊣ Λ`],
  zsqc(`f ∋`, `g R`, eq: true),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[antisymmetry],
  zpair(zsqc(`f ∋`, `g R`), zsqc(`g R`, `f ∋`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°· ⊣ f·`],
  zpair(zsqc(`g° f ∋`, `R`), zsqc(`f° g R`, `∋`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`·S ⊣ /S`],
  zpair(zsqc(`g° f`, `R/∋`), zsqc(`f° g`, `∋/R`)),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[`°`, meet],
  zsqc(`g° f`, `(R/∋) ∩ (∋/R)°`),
)
]<lam-symmdiv>

#pagebreak(weak: true)
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

- For `f` a map, `F(f)` is a map and `F(f°) = F(f)°`.
- Over a *tabular* allegory a functor is a relator `⟺` it preserves `°`.
- A relator is fixed by what it does to maps.
- `F(R ∩ S) ⊑ F(R) ∩ F(S)`, and strictly.
- `F(X ∩ Y) = F(X) ∩ F(Y)` for `X, Y` coreflexive.
- `F(Dom R) = Dom(F(R))` for `F` preserving `°`.

The *power relator* `P` — `x P(R) y ⟺ (∀a ∈ x. ∃b ∈ y. a R b) ∧ (∀b ∈ y. ∃a ∈ x. a R b)` — is where
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

The injections `ιₗ : A ⟶ A + B` and `ιᵣ : B ⟶ A + B` are maps, and the coproduct they make of the maps
stays a coproduct once every arrow is allowed: both equations hold with equality and `[R,S]` is the only
arrow satisfying them, with none of the `Dom` slack `⟨R,S⟩` carries.

#disp[#definition[
`[R,S] ≜ ιₗ° R ∪ ιᵣ° S`, and `R + S ≜ [R ιₗ, S ιᵣ]`.
]]<coprod-defn>

// THE DEFINITION, DRAWN, and it needs no new generator: `+` is a UNION, already drawn as the tape of
// the laws above.  The other rows are calculated from this one line and stay formulas.
#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let y = 0.62                    // the tape's two branches, at the exported pictures' half-spacing
  wire((0, 0), (0.34, 0))
  tape((0.34, -1.14), (3.80, 1.14))
  tape-fork((0.56, 0), sp: y, len: 0.42)
  // Mirrored and tinted: this file draws a converse by flipping the box, so these are `ιₗ°` and `ιᵣ°`.
  gbox((0.98, y), [`ιₗ`], flip: true, fill: TINT); wire((1.90, y), (2.24, y)); gbox((2.24, y), [R])
  gbox((0.98, -y), [`ιᵣ`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y)); gbox((2.24, -y), [S])
  tape-join((3.58, 0), sp: y, len: 0.42)
  wire((3.80, 0), (4.14, 0))
  lab(-0.9, 0, black)[$A + B$]; lab(4.49, 0, black)[$C$]
}))]<coprod-pic>

The tape is the union — a particle entering at `A + B` takes exactly one branch — and the two mirrored
boxes are what makes the branches disjoint.

#disp[#table(
  columns: 1, inset: 9pt, stroke: 0.4pt + luma(190),

  [`ιₗ [R,S] = R`, `ιᵣ [R,S] = S`, and `[R,S]` is the only such arrow],
  [`ιₗ ιₗ° = 𝟙 = ιᵣ ιᵣ°`],
  [`ιₗ ιᵣ° = ⊥ = ιᵣ ιₗ°`],
  [`ιₗ° ιₗ ∪ ιᵣ° ιᵣ = 𝟙`],
  [`[U,V]° [R,S] = U° R ∪ V° S`],
)]<coprod-laws>

// B&dM §5.3, pp. 117-118, mirrored into this note's diagram order: why the first row holds with
// equality where the fork's triangles above only hold up to `Dom`.
The first row is not free: `ιₗ, ιᵣ` were only ever asked to be a coproduct of *maps*. They stay one
once every arrow is allowed because `Λ` sends an arrow `A ⟶ C` to a map `A ⟶ P C` reversibly, so the
map coproduct can be applied underneath it. For any `T : A + B ⟶ C`,

// B&dM's own layout for a calculation: the line, then the step's justification indented under a `⟺`,
// then the next line.  Stroke-less, so it reads as one argument and not as another law table.
#disp[#table(
  columns: 2, stroke: none, inset: (x: 10pt, y: 3pt), align: (right + horizon, left + horizon),
  [], [`ιₗ T = R` and `ιᵣ T = S`],
  [`⟺`], [#src[`Λ` is injective — `Λ(X) ∋ = X` gives `X` back]],
  [], [`Λ(ιₗ T) = Λ(R)` and `Λ(ιᵣ T) = Λ(S)`],
  [`⟺`], [#src[`Λ` fusion, `Λ(f X) = f Λ(X)` for `f` a map]],
  [], [`ιₗ Λ(T) = Λ(R)` and `ιᵣ Λ(T) = Λ(S)`],
  [`⟺`], [#src[the coproduct of maps, at the map `Λ(T)`]],
  [], [`Λ(T) = [Λ(R), Λ(S)]`],
  [`⟺`], [#src[`Λ(X)` is the only map with `Λ(X) ∋ = X`]],
  [], [`T = [Λ(R), Λ(S)] ∋`],
)]<coprod-calc>

// The lead-in and the figure in ONE unbreakable block: left to itself the sentence ends a page and
// the picture opens the next, so the reader turns the page between "drawn" and the drawing.
#block(breakable: false)[
Every step is an `⟺`, so `[Λ(R), Λ(S)] ∋` is the *only* arrow satisfying the two equations — which is
what `[R,S]` was claimed to be. Drawn:

// The book's figure turned a quarter turn, source at the left like every other picture here.  `R` and
// `S` arc outside because their straight lines would run over `P C`; blue dashed is the induced arrow.
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
  lab(-1.23, 1.62, GIVEN1)[`Λ(R)`]; lab(-1.23, -1.62, GIVEN2)[`Λ(S)`]
  lab(-3.0, 0.5, INDUCED)[`[Λ(R), Λ(S)]`]
  lab(2.5, 0.45, black)[`∋`]
  node(A.at(0), A.at(1), GIVEN1, $A$); node(B.at(0), B.at(1), GIVEN2, $B$)
  node(AB.at(0), AB.at(1), black, $A + B$)
  node(PC.at(0), PC.at(1), INDUCED, $P C$)
  node(C.at(0), C.at(1), black, $C$)
}))]<coprod-square>
]

Nothing here holds only up to `⊑`: every triangle commutes on the nose, which is the difference from
the fork above. The border spells `[R,S] = [Λ(R), Λ(S)] ∋`, and pushing `∋` into the union that
`[·,·]` on maps already is turns that back into the definition,
`(ιₗ° Λ(R) ∪ ιᵣ° Λ(S)) ∋ = ιₗ° R ∪ ιᵣ° S`.

// B&dM §5.4, p. 119.  The heading gets its own page: the definition, the paragraph that explains its
// shape, and the table are one argument, and the coproduct figure above ends a page mid-way.
#pagebreak(weak: true)
= The power relator `P(R)` <sec-powrel>

#disp[#definition[
For `R : A ⟶ B`, #h(4pt) `P(R) ≜ ((∋ R)/∋) ∩ ((∋ R°)/∋)° : P A ⟶ P B`.
]]<powrel-defn>

`∋ R` is a *composition* — `∋ : P A ⟶ A` followed by `R` — and not Freyd's subscripted $#e[R]$,
which is the `∋` at `R`'s *target*: §@sec-power writes one `∋` per object and drops the subscript. Piece by
piece, on one instance, with `x, y` sets and `a, b` their elements.

`x = {a₁,a₂}`, and `R` sends `a₁` to `b₁` and `b₃`, `a₂` to `b₃` alone. Nothing on `x` reaches `b₂`,
so `b₂` is drawn hollow.

#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, BD.b1, 1, [`∋ R`], h: 4.2, cx: 5)
  arc(LX, BD.b3, -1, [`∋ R`], h: 4.2, cx: 5)
})))
// The arrow and its `Rel` reading go UNDER the picture that draws them, one pair per picture: read
// against the drawing they were just given, where a table of all three read against nothing.
#align(center, block(inset: (y: 6pt))[
  `∋ R : P A ⟶ B` #h(1.4cm) `x (∋ R) b ⟺ ∃a ∈ x. a R b`
])
#align(center, src[one arc per element of `B` that `x` reaches, and `b₂` gets none])]<powrel-elem>

Dividing by `∋` turns that into a relation between *sets*: every element of `y` must be one of the
filled dots.

#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, LY.y1, 1, [`(∋ R)/∋`], h: 5.6, cx: 6)
  lab(3.2, 3.4, SLACK)[`∋`]
  yset(LY.y1, (BD.b1, BD.b3), `y₁ = {b₁,b₃}`)
  yset(LY.y3, (BD.b2, BD.b3), `y₃ = {b₂,b₃}`, on: false)
})))
#align(center, block(inset: (y: 6pt))[
  `(∋ R)/∋ : P A ⟶ P B` #h(1.4cm) `x ((∋ R)/∋) y ⟺ ∀b ∈ y. ∃a ∈ x. a R b`
])
#align(center, src[`y₃` is rejected: it names `b₂`, which `x` does not reach])]<powrel-div>

// Lead-in, picture and readings in ONE unbreakable block: left to itself the sentence ends page 17
// and the picture opens page 18, so the reader turns the page between "them" and them.
#block(breakable: false)[
The other half of the meet is that clause with the sets swapped and `R` turned round: every element
of `x` must reach `y`. Both together, and two more sets to separate them:

#disp[#box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, LY.y1, 1, [`P(R)`], h: 5.6, cx: 6)
  arc(LX, LY.y4, -1, [`P(R)`], h: 5.6, cx: 6)
  lab(3.2, 3.4, SLACK)[`∋`]
  yset(LY.y1, (BD.b1, BD.b3), `y₁ = {b₁,b₃}`)
  yset(LY.y2, (BD.b1,), `y₂ = {b₁}`, on: false)
  yset(LY.y3, (BD.b2, BD.b3), `y₃ = {b₂,b₃}`, on: false)
  yset(LY.y4, (BD.b3,), `y₄ = {b₃}`)
})))
#align(center, block(inset: (y: 6pt))[
  `((∋ R°)/∋)° : P A ⟶ P B` #h(1.4cm) `x ((∋ R°)/∋)° y ⟺ ∀a ∈ x. ∃b ∈ y. a R b`
])
#align(center, src[`y₂` is rejected too: `a₂`'s only image is `b₃`, which `y₂` does not name])]<powrel-both>
]

In words, if `x P(R) y` then every element of `x` is related by `R` to some element of `y`, and
conversely — the two clauses of `∩`, one per direction.

Neither `∋` nor `P(R)` is a map. `∋` sends a set to *each* of its elements; `P(R)` sends `x` to
*every* `y` meeting the two clauses, `y₁` and `y₄` both. Nor is it entire: an `a ∈ x` with no image
at all leaves `x` with no partner whatever. Turning a relation into a map is `Λ`'s job (§@sec-power), and on
sets that map is `Λ(∋ R)` — of the four it accepts `y₁` only.

// The question this subsection exists to answer: the definition IS two divisions and a converse, the
// shape of a symmetric division, and the reader who has just read the symmetric-division section will try to fold it into one.
*Not* a symmetric division. $frac(∋ R, ∋)$ is `Λ(∋ R)`, and in `Rel` it reads
`x Λ(∋ R) y ⟺ y = {b | ∃a ∈ x. a R b}`: in words, `y` is *exactly* what `x` reaches, where `P(R)`
asks only that each side cover the other. Nor can it be repaired: in that fraction's second half
$(∋ slash (∋ R))^circle.small$ the `R` sits in a denominator, so the operation is antitone there, and
a relator has to be monotone. `P(R)` keeps the first half and takes the second half at `R°`, which
puts `R` back in a numerator. The fraction returns exactly where the two halves agree — at `𝟙`, and
at a map.

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

  [`P(f) = Λ(∋ f)` `=` $frac(∋ f, ∋)$, for `f` a map],
  [In `Rel`, `x P(f) y ⟺ y = {f a | a ∈ x}`. The half at `f°` says every `a ∈ x` has its `f a` on
   `y`; `f` has just the one image per `a`, so that already says `y` contains everything `x`
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
with `α`#sub[`T`]` ⦇α`#sub[`B`]`⦈ = F(⦇α`#sub[`B`]`⦈) α`#sub[`B`].
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

= Catamorphism in 𝒮et

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
  [`Λ(⦇α`#sub[`B`]`⦈) = ⦇Λ(F(∋) α`#sub[`B`]`)⦈`],
  [A relational fold is a deterministic fold of SETS: `Λ` pushes the nondeterminism into the
   power-object, where the fold is a map again.],

  [Eilenberg–Wright],
  [`⦇α`#sub[`B`]`⦈ = ⦇Λ(F(∋) α`#sub[`B`]`)⦈ ∋`],
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
The two `Λ` rows, drawn:

// `⦇Λ(F(∋) α_B)⦈` is three node-boxes wide, so inside the picture it is the single letter `K` and the
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
  lab(-6.75, 0, GIVEN2)[`α`#sub[`T`]]; lab(6.8, 0, GIVEN1)[`α`#sub[`B`]]; lab(2.2, 0, black)[`Λ(F(∋) α`#sub[`B`]`)`]
  node(FT.at(0), FT.at(1), black, `F T`); node(T.at(0), T.at(1), black, `T`)
  node(FP.at(0), FP.at(1), INDUCED, `F(P B)`); node(P.at(0), P.at(1), INDUCED, `P B`)
  node(FB.at(0), FB.at(1), GIVEN1, `F B`); node(B.at(0), B.at(1), GIVEN1, `B`)
}))]<cata-lambda-square>
]

The left square is that catamorphism's own defining square, `K = ⦇Λ(F(∋) α`#sub[`B`]`)⦈`, and the
right one is `Λ`'s cancellation, so the outer rectangle says `K ∋` satisfies the defining equation
of `⦇α`#sub[`B`]`⦈` — and uniqueness finishes it.

// Its own page: the heading was left orphaned at the foot of the page before it.
#pagebreak(weak: true)
== Fokkinga's mutual recursion theorem

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

== Ruby triangles

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
== Depth of a tree

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

  [`Pow A = P A`], [`{·}`], [`⋃`], [`η A a = {a}`], [`μ A Xs = ⋃ Xs`],
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
