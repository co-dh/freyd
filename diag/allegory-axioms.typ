// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name.  See the header of strdiag.typ.
// `dot` is renamed on the way in for the same reason: it is Typst's math `dot`.
#import "strdiag.typ": conv, meet, wire, bend, gbox, dot as wiredot, tape, tape-fork, tape-join, TINT
// The zigzag box and its wires, for the `f ⊣ f°` section.  Renamed on the way in: `wire` above is
// this file's, and `w`/`sq` are too short to leave unmarked in a file that has neither.  The
// definitions stay in the note at the repository root, which is what `--root .` in the Makefile is
// for; a copy here would be a second one to keep in step.
#import "../notation_as_a_tool_of_thought_adjunction.typ": sq as zsq, w as zw

// EVERY PICTURE OF A THEOREM BELOW IS EXPORTED, NOT DRAWN.  `./scripts/diag-export <decl>` walks the
// Lean declaration's TYPE and writes diag/generated/<decl>.typ, which binds the cetz drawing to
// `pic`; this note only places those bindings in table cells.  Hand-drawing them is how the first
// draft of this page got `inter_assoc` wrong — it showed coassociativity of `◁` instead of the axiom
// — and dropped the `=` from `recip_inter`.  A picture derived from the statement cannot drift from
// it.  `./scripts/diag-regen` redraws every binding below, reading the list off these very imports.
#import "generated/Freyd.Diag.CartBicat.conv_conv.typ": pic as p-conv-conv
#import "generated/Freyd.Diag.CartBicat.conv_comp.typ": pic as p-conv-comp
#import "generated/Freyd.Diag.conv_inter.typ": pic as p-conv-inter
#import "generated/Freyd.Diag.meet_top.typ": pic as p-meet-top
#import "generated/Freyd.Diag.meet_comm.typ": pic as p-meet-comm
#import "generated/Freyd.Diag.meet_assoc.typ": pic as p-meet-assoc
#import "generated/Freyd.Diag.meet_idem.typ": pic as p-meet-idem
#import "generated/Freyd.Diag.semidistrib_of_lax.typ": pic as p-semidistrib
#import "generated/Freyd.Diag.«≤_top».typ": pic as p-le-top
#import "generated/Freyd.Diag.CartBicat.Δ_assoc.typ": pic as p-d-assoc
#import "generated/Freyd.Diag.CartBicat.Δ_comm.typ": pic as p-d-comm
#import "generated/Freyd.Diag.CartBicat.Δ_counit.typ": pic as p-d-counit
#import "generated/Freyd.Diag.CartBicat.«∇_assoc».typ": pic as p-n-assoc
#import "generated/Freyd.Diag.CartBicat.«∇_comm».typ": pic as p-n-comm
#import "generated/Freyd.Diag.CartBicat.«∇_unit».typ": pic as p-n-unit
#import "generated/Freyd.Diag.CartBicat.«∇Δ≤𝟙».typ": pic as p-37
#import "generated/Freyd.Diag.CartBicat.«𝟙≤Δ∇».typ": pic as p-38
#import "generated/Freyd.Diag.CartBicat.«?!≤𝟙».typ": pic as p-39
#import "generated/Freyd.Diag.CartBicat.«𝟙≤!?».typ": pic as p-40
#import "generated/Freyd.Diag.CartBicat.frob.proof.typ": branches as frobb
#import "generated/Freyd.Diag.CartBicat.snakes.proof.typ": branches as snakeb
#import "generated/Freyd.Diag.CartBicat.snake'.proof.typ": branches as snkb
#import "generated/Freyd.Diag.CartBicat.lax_Δ.typ": pic as p-lax-delta
#import "generated/Freyd.Diag.CartBicat.lax_!.typ": pic as p-lax-bang
#import "generated/Freyd.Diag.«lax_∇».typ": pic as p-lax-nabla
#import "generated/Freyd.Diag.lax_?.typ": pic as p-lax-unit
#import "generated/Freyd.Diag.Biprod.«≤_union_left».typ": pic as p-union-left
#import "generated/Freyd.Diag.Biprod.union_comm.typ": pic as p-union-comm
#import "generated/Freyd.Diag.Biprod.bot_union.typ": pic as p-bot-union
#import "generated/Freyd.Diag.Biprod.comp_union.typ": pic as p-comp-union
#import "generated/Freyd.Diag.Biprod.conv_union.typ": pic as p-conv-union
#import "generated/Freyd.Diag.FbCbRig.meet_union_distrib.typ": pic as p-distrib
#import "generated/Freyd.Diag.CartBicat.conv_comp.proof.typ": branches as l42ii
#import "generated/Freyd.Diag.CartBicat.conv_tensHom.proof.typ": branches as l42iii
#import "generated/Freyd.Diag.CartBicat.conv_mono.proof.typ": branches as l42iv
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

= Cartesian bicategory of relations

#definition[
A *cartesian bicategory of relations* is a poset-enriched category(bicategory)
that is has a symmetric monoidal product $times.o$ (cartisin product of set in Rel, vertical junctposition in the diagram) and

  #align(center, block(inset: (y: 6pt))[
    #text(12.5pt)[ $forall$ object A, `(A, ◁, ⊸) ⊣ (A, ▷, ⟜)`,  *Frobenius*, arrows *lax*.]
    #v(3pt)
    #src[`(◁ : A ⟶ A ⊗ A, ⊸ : A ⟶ 𝕀)` formed a cocommutative comonoid] \
    #src[`(▷ : A ⊗ A ⟶ A, ⟜ : 𝕀 ⟶ A)` formed a commutative monoid]
  ])
]

#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + horizon,
  P(p-d-assoc, s: 60%), P(p-d-comm, s: 60%), P(p-d-counit, s: 60%),
)

#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + horizon,
  P(p-n-assoc, s: 60%), P(p-n-comm, s: 60%), P(p-n-unit, s: 60%),
)

In `Rel(Set)`, the four generators are these relations on a set `A`:

#align(center, table(
  columns: 2, stroke: none, inset: (x: 8pt, y: 2.5pt), align: left,
  [`◁`], src[`= {(a, (a, a))}` — copy: one in, two identical out],
  [`▷`], src[`= {((a, a), a)}` — merge: a pair passes only when its two components agree, and the
   common value comes out],
  [`⊸`], src[`= A × {∗}` — discard: forget the value, keep only that there was one],
  [`⟜`], src[`= {∗} × A` — create: any element at all],
))

== $forall$ object A, `(A, ◁, ⊸) ⊣ (A, ▷, ⟜)`

#grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-37, s: 52%) #v(-7pt) \ #src[`▷ ◁ ≤ 𝟙`]],
  [#P(p-38, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ◁ ▷`]],
  [#P(p-39, s: 52%) #v(-7pt) \ #src[`⟜ ⊸ ≤ 𝟙`]],
  [#P(p-40, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ⊸ ⟜`]],
)

The last of these is the only one that makes a picture *bigger*, and it is worth a name: *a wire is
below the cut wire*. In `Rel` it reads `{(a, a)} ⊆ A × A` — cut a wire and its two ends stop having
to agree, so cutting can only add pairs. It is the one weakening this calculus gives away for free.

== The Frobenius law

#row(frobb.at(0).steps, s: 54%)

The only clause coupling the comonoid to the monoid beyond adjointness. Both sides reduce to the
same picture, `▷ ◁` — merge, then copy — which is the two-in two-out *spider*. Every connected
diagram built from these four generators collapses to the spider on its own inputs and outputs, and
this equation is what starts that collapse. A *bubble* is the other order, `◁ ▷`: copy then merge,
a closed loop, which the idempotency of `∩` uses below.

// No heading of its own: the word is defined where it is first used, which is the heading below, and
// a two-paragraph definition that every later section leans on is not a section.
// `R`, `S` for the two arrows rather than the usual `a`, `b` of a lax-functor statement: `a`, `b`, `c`
// are this chapter's ELEMENTS, and the reading of the composite two lines down needs all three.
A *functor* asks for `F(R) F(S) = F(R S)` and `𝟙 = F(𝟙)`. A *lax* one keeps only a 2-cell, always the
same way round,

#align(center, block(inset: (y: 4pt))[`F(R) F(S) ⇒ F(R S)` #h(1.4cm) `𝟙 ⇒ F(𝟙)`])

with coherence conditions on top. The other direction is *oplax*, an invertible 2-cell *pseudo*, an
identity one *strict*. In `Rel` a 2-cell is `⊑` and parallel 2-cells are unique, so the coherence
conditions are automatic and a lax functor into `Rel` is exactly two inequalities,
`F(R) F(S) ⊑ F(R S)` and `𝟙 ⊑ F(𝟙)`, with nothing else to check.

Which way round is forced, not a convention to memorise: `a (F(R) F(S)) c ⟺ ∃b. a F(R) b ∧ b F(S) c`
quantifies the mid-point `b` away, so a pair that gets through in two steps has to stop somewhere in
between, and one that `F` lets through in one need not — *step by step `⊑` all at once*. Equality
comes back exactly on maps: of the two laws just below, the first is an equality exactly when `R` is
single valued, the second when `R` is entire, and both when `R` is a *map*, whose two halves those are — so
*lax* or *strict* is the relation/map boundary under another name. The unit and counit above, the two
homomorphism sections below and the polyad of the division chapter are all this one move.

== Every arrow is a lax comonoid homomorphism

#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-lax-delta, s: 60%) #v(-7pt) \ #src[`R◁ ≤ ◁(R⊗R)`]],
  [#P(p-lax-bang, s: 60%) #v(-7pt) \ #src[`R⊸ ≤ ⊸`]],
)

== The four generators one dimension up

// `lab` lives here, ahead of every picture this note draws by hand, because the fork below is the
// first of them and a Typst binding exists only from its definition on.
// `rot` turns a cell's `⊑` to point from the SMALLER path to the larger one.  Unrotated it reads
// left to right, which in a triangle or a square is the wrong axis: in the pairing section's left
// triangle the small side is the path over the top and the large one is `R` at the lower left, so
// the symbol has to point southwest.  Typst rotates clockwise, so southwest is 135°, southeast 45°,
// northwest −135°, northeast −45°.
#let lab(x, y, col, w, rot: 0deg) = d.content((x, y), rotate(rot, text(10pt, col)[#w]))
// The 2-cell helpers, shared with the Marsden section far below, which draws the same cup, cap and
// snake with `i`, `P` for `◁`, `▷` — one definition apiece, placed at the earlier of the two users.
// The two fills mean nothing on their own: they are one hue apiece to tell two regions apart, here
// `A` and `A ⊗ A`, there `Map(𝒜)` and `𝒜`.
#let fb-MAPC = rgb("#e6f3e4")
#let fb-ALLC = rgb("#e9e7f7")
// A 2-cell: a dot on the wire, named beside it.  `wiredot` is the note's own solid dot, at the same
// radius every generator uses, so a 2-cell here and a generator in a string diagram look alike on
// purpose — both are a node on a wire.
#let fb-dot(p, t, dx: 0.34, dy: 0) = {
  wiredot(p)
  lab(p.at(0) + dx, p.at(1) + dy, black)[#t]
}
// A hairline parting two independent pictures that share one canvas.
#let fb-rule(x, y0, y1) = d.line((x, y0), (x, y1), stroke: 0.4pt + luma(170))

Nothing about `◁` changes; what changes is which dimension carries what. Read the same fork in the
two calculi — (a) left to right, as every other string diagram here, (b) bottom to top:

// ONE canvas parted by a hairline, not two figures: it is the same `◁` twice, and only side by side
// does it show that the fork has flattened to a straight wire.
#align(center, box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
  // (a) `◁` is a NODE: its source and target are the wires, and one in two out is why it forks.
  wire((-4.6, 0), (-3.7, 0)); lab(-4.9, 0, black)[$A$]
  wiredot((-3.7, 0))
  bend((-3.7, 0), (-2.7, 0.42)); bend((-3.7, 0), (-2.7, -0.42))
  wire((-2.7, 0.42), (-2.2, 0.42)); wire((-2.7, -0.42), (-2.2, -0.42))
  lab(-1.95, 0.42, black)[$A$]; lab(-1.95, -0.42, black)[$A$]
  lab(-3.7, -0.95, black)[(a) `◁` is a node]

  fb-rule(-1.0, -1.2, 1.1)

  // (b) `◁` is a 1-cell, so it is the WIRE, and its source and target are the regions either side of
  // it — source `A` on the left, target `A ⊗ A` on the right, so that a composite reads left to
  // right here exactly as it does in (a).
  d.rect((0.2, -1), (2.8, 1), fill: fb-ALLC, stroke: none)
  d.rect((0.2, -1), (1.5, 1), fill: fb-MAPC, stroke: none)
  d.line((1.5, -1), (1.5, 1), stroke: 1.1pt)
  lab(1.5, 1.3, black)[`◁`]
  lab(0.82, -0.75, luma(80))[$A$]; lab(2.2, -0.75, luma(80))[$A ⊗ A$]
  lab(1.5, -1.45, black)[(b) `◁` is a wire]
})))

#align(center, table(
  columns: 3, inset: 8pt, stroke: 0.4pt + luma(190),
  align: (left + horizon, left + horizon, left + horizon),
  table.header([], [*(a) monoidal*], [*(b) 2-cell*]),

  [region], [only one, undrawn], [a set: `A`, `A ⊗ A`],
  [wire], [a set], [a relation: `◁`, `▷`],
  [node], [a relation: `◁`, `▷`, `⊸`, `⟜`], [an inclusion `⊑`],
))

Everything moves up one dimension, so the fork flattens: its three wires were the sets `A`, `A`, `A`,
and in (b) sets are regions — the two prongs are no longer drawn at all, they are the name of the
region on the right. What (b) gains is the room to draw the inclusions, and with them the adjunction
this section opened with:

// The two 2-cells, then the snake they make.  FILL AND STROKE ARE SEPARATE PATHS on the cup and the
// cap: one `merge-path(close: true)` carrying both would stroke the closing segment too, drawing a
// line across the top of the cup that joins the `◁` and `▷` legs — and there is no such line, it is
// one wire that bends, its two legs running free to the frame edge.
#align(center, box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
  // The unit `𝟙 ⊑ ◁▷` runs between two arrows `A ⟶ A`, so `A` is the ground the cup is cut out of,
  // and the `A ⊗ A` between its legs is where the wire goes and comes back from.
  // All four panels of the row are the same 1.2 half-height, and a named 2-cell sits 0.45 clear of
  // its own bend: these two names
  // are whole containments, far wider and taller than the `{·}` and `∋` of the Marsden section
  // below, and at that section's 0.3 they are drawn through by the curve they name.
  d.rect((-1.0, -1.2), (1.0, 1.2), fill: fb-MAPC, stroke: none)
  d.merge-path(close: true, fill: fb-ALLC, stroke: none, {
    d.line((-0.4, 1.2), (-0.4, 0.1))
    d.bezier((-0.4, 0.1), (0.4, 0.1), (-0.4, -0.55), (0.4, -0.55))
    d.line((0.4, 0.1), (0.4, 1.2))
  })
  d.line((-0.4, 1.2), (-0.4, 0.1), stroke: 1.1pt)
  d.bezier((-0.4, 0.1), (0.4, 0.1), (-0.4, -0.55), (0.4, -0.55), stroke: 1.1pt)
  d.line((0.4, 0.1), (0.4, 1.2), stroke: 1.1pt)
  fb-dot((0, -0.31), `𝟙 ⊑ ◁▷`, dx: 0, dy: -0.45)
  lab(-0.4, 1.48, black)[`◁`]; lab(0.4, 1.48, black)[`▷`]

  fb-rule(1.8, -1.5, 1.5)

  // The counit `▷◁ ⊑ 𝟙` runs between two arrows `A ⊗ A ⟶ A ⊗ A`, so the cap is the mirror of the
  // cup in both colours: `A ⊗ A` is its ground and `A` is what sits between its legs.
  d.rect((2.6, -1.2), (4.6, 1.2), fill: fb-ALLC, stroke: none)
  d.merge-path(close: true, fill: fb-MAPC, stroke: none, {
    d.line((3.2, -1.2), (3.2, -0.1))
    d.bezier((3.2, -0.1), (4.0, -0.1), (3.2, 0.55), (4.0, 0.55))
    d.line((4.0, -0.1), (4.0, -1.2))
  })
  d.line((3.2, -1.2), (3.2, -0.1), stroke: 1.1pt)
  d.bezier((3.2, -0.1), (4.0, -0.1), (3.2, 0.55), (4.0, 0.55), stroke: 1.1pt)
  d.line((4.0, -0.1), (4.0, -1.2), stroke: 1.1pt)
  fb-dot((3.6, 0.31), `▷◁ ⊑ 𝟙`, dx: 0, dy: 0.45)
  lab(3.2, -1.48, black)[`▷`]; lab(4.0, -1.48, black)[`◁`]

  fb-rule(5.4, -1.5, 1.5)

  // The snake: the cup and the cap on one wire, so the merge-path is the region LEFT of the zigzag,
  // which for `◁` is its source `A`, and the ground is its target `A ⊗ A` to the right.
  d.rect((6.2, -1.2), (9.8, 1.2), fill: fb-ALLC, stroke: none)
  d.merge-path(close: true, fill: fb-MAPC, stroke: none, {
    d.line((6.2, 1.2), (7.2, 1.2)); d.line((7.2, 1.2), (7.2, -0.2))
    d.bezier((7.2, -0.2), (8.1, -0.2), (7.2, -0.85), (8.1, -0.85))
    d.line((8.1, -0.2), (8.1, 0.2))
    d.bezier((8.1, 0.2), (9.0, 0.2), (8.1, 0.85), (9.0, 0.85))
    d.line((9.0, 0.2), (9.0, -1.2)); d.line((9.0, -1.2), (6.2, -1.2))
  })
  d.line((7.2, 1.2), (7.2, -0.2), stroke: 1.1pt)
  d.bezier((7.2, -0.2), (8.1, -0.2), (7.2, -0.85), (8.1, -0.85), stroke: 1.1pt)
  d.line((8.1, -0.2), (8.1, 0.2), stroke: 1.1pt)
  d.bezier((8.1, 0.2), (9.0, 0.2), (8.1, 0.85), (9.0, 0.85), stroke: 1.1pt)
  d.line((9.0, 0.2), (9.0, -1.2), stroke: 1.1pt)
  // The two dots are the unit and the counit of the panels to the left, unlabelled here: naming them
  // again would say only what the two panels have just said.
  wiredot((7.65, -0.68)); wiredot((8.55, 0.68))
  lab(7.2, 1.48, black)[`◁`]; lab(9.0, -1.48, black)[`◁`]

  lab(10.3, 0, black)[$=$]

  d.rect((11.0, -1.2), (13.0, 1.2), fill: fb-ALLC, stroke: none)
  d.rect((11.0, -1.2), (11.9, 1.2), fill: fb-MAPC, stroke: none)
  d.line((11.9, -1.2), (11.9, 1.2), stroke: 1.1pt)
  lab(11.9, 1.48, black)[`◁`]; lab(11.9, -1.48, black)[`◁`]
})))

#align(center, src[Green is `A`, purple `A ⊗ A`, and a wire carries its source on the left and its
target on the right. The unit runs between two arrows `A ⟶ A`, so `A` is the ground the cup is cut
out of; the counit runs between two arrows `A ⊗ A ⟶ A ⊗ A`, and that is the ground of the cap. The
snake is the adjunction this section opened with, pulled straight.])

// Its definition box was straddling the break, which reads as two half-boxes.
#pagebreak(weak: true)
= ° : 𝒞ᵒᵖ ⟶ 𝒞 is a 2 functor 

#definition[
The *converse* `R°` of `R : a ⟶ b` is `R` with both of its wires turned round,

#fig({ conv((0, -0.80), $R$) })

#align(center, block(inset: (y: 4pt))[#text(12.5pt)[`R° = (⟜◁ ⊗ 𝟙) (𝟙 ⊗ R ⊗ 𝟙) (𝟙 ⊗ ▷⊸)`]])

where `⟜◁ : 𝕀 ⟶ a ⊗ a` opens a pair of wires out of nothing and `▷⊸ : b ⊗ b ⟶ 𝕀` closes one, so
the input of `R°` is where the output of `R` was. And it is a contravariant 2-functor `° : 𝒞ᵒᵖ ⟶ 𝒞`:

#align(center, block(inset: (y: 5pt))[
  (i) `𝟙° = 𝟙`  #h(1cm) (ii) `(R S)° = S° R°`  #h(1cm) (iii) `(R ⊗ S)° = R° ⊗ S°`
  #h(1cm) (iv) `R ≤ S` implies `R° ≤ S°`
])
]

== `𝟙° = 𝟙`  (snake)

#chain(
  (snkb.at(0).steps.at(2), snkb.at(0).steps.at(3), snkb.at(0).steps.at(5)),
  ([], [Frobenius], [unit, counit]))

== The slide

The one rule (ii) and (iii) use, and each of them uses it twice. A converse facing a merge on the
lower strand is the box itself, upright, on the upper one:

#P(p-conv-slide, s: 62%)

`R°` is DEFINED as the bending of `(R ⊗ 𝟙) ▷⊸`, so the slide claims only that unbending it gives
that back — and unbending undoes bending for every arrow. That is the snake above with a passenger:
the `⟜◁` bends the `a` strand down and the `▷⊸` brings it back up, while the `b` strand rides
through untouched. Nothing else is spent below.

== `(R S)° = S° R°`

#chain(
  (l42ii.at(0).steps.at(0), l42ii.at(0).steps.at(3), l42ii.at(0).steps.at(4),
   l42ii.at(0).steps.at(5), l42ii.at(0).steps.at(7)),
  ([], [slide], [interchange], [slide], [snake]), s: 41%)

== `(R ⊗ S)° = R° ⊗ S°`

A merge at a product is two merges behind a crossing, so the pair unbends one strand at a time and
the crossing is all that is left to move.

#chain(
  (l42iii.at(0).steps.at(0), l42iii.at(0).steps.at(1), l42iii.at(0).steps.at(3),
   l42iii.at(0).steps.at(4), l42iii.at(0).steps.at(6)),
  ([], [a strand per letter], [`σ` past both boxes], [slide, twice], [snake]), s: 36%)

// Kept whole: the row is two pictures, and the break was falling between them and their heading.
#block(breakable: false)[
== `R ≤ S` implies `R° ≤ S°`

`R` sits in a frame of wires built from `≫` and `⊗`, and both of those are monotone, so the box may
be replaced where it stands.

#chain(
  (l42iv.at(0).steps.at(1), l42iv.at(0).steps.at(2)),
  ([], [`≫`, `⊗` monotone]), s: 55%)
]



= Every arrow is a lax monoid homomorphism

The merge/create mirror of the two comonoid laws opening this note — the paper's (41) and (42),
p. 22, which it gets by bending them with (ii) and (iv) above. No bending is needed: expand by the
unit `𝟙 ≤ ◁ ▷`, duplicate the box with the comonoid law, contract by the counit `▷ ◁ ≤ 𝟙`. Both
halves of the adjunction, and nothing else.

In `Rel(Set)` with `R ⊆ A × B`, where `▷` is the equality test on a pair and `⟜` produces any
element at all:

#align(center, table(
  columns: 2, stroke: none, inset: (x: 8pt, y: 2.5pt), align: left,
  [`▷ R`], src[`= {((a, a ), b) : a R b}` — two equal inputs, then one run of `R`],
  [`(R ⊗ R) ▷`], src[`= {((a, a'), b) : a R b and a' R b}` — a run on each input, then the results
   merged],
  [`⟜ R`], src[`= {(∗, b) : ∃a. a R b}` — the image of `R`],
  [`⟜`], src[`= {∗} × B` — all of `B`],
))

Take `a' = a` for the first containment; every `b` lies in `B` for the second. Each is strict exactly
when its reverse fails — `R` not injective, `R` not surjective — which is what the later table on
maps reads off them.

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*inequation, and what proves it*], [*picture*]),

  [(41) `▷ R ≤ (R ⊗ R) ▷` \
   #src[`▷R = ▷R𝟙 ≤ ▷R◁▷ ≤ ▷◁(R⊗R)▷ ≤ (R⊗R)▷` — unit, lax `◁`, counit.]],
  P(p-lax-nabla),

  [(42) `⟜ R ≤ ⟜` \
   #src[`⟜R = ⟜R𝟙 ≤ ⟜R⊸⟜ ≤ ⟜⊸⟜ ≤ ⟜` — the same three steps at `𝕀`.]],
  P(p-lax-unit),
)

#pagebreak(weak: true)
= `∩` is a commutative idempotent monoid on every hom-set

#definition[
The *meet* of `R, S : a ⟶ b`, the paper's *convolution*, is `R ∩ S := ◁ (R ⊗ S) ▷` — copy the
input, run `R` and `S` on the two copies, merge the results — so what comes out is what both of them
do.

#fig({ meet((0, 0), $R$, $S$) })
#align(center, src[transcribed: a definition has no statement to export])

On every hom-set it is associative, commutative and idempotent, with unit the maximal arrow
`⊤ = ⊸ ⟜` #src[(the paper's Lemma 4.11)].
]

#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-meet-top, s: 60%) #v(-7pt) \ #src[*unit:* one half of `⊤` per end — the merge's unit law
   absorbs the `⟜`, the copy's counit law the `⊸`]],
  [#P(p-meet-comm, s: 60%) #v(-7pt) \ #src[*commutative:* `σ` crosses `R ⊗ S` by naturality and is
   absorbed by cocommutativity and commutativity]],
  [#P(p-meet-assoc, s: 44%) #v(-7pt) \ #src[*associative:* coassociativity and associativity; `⊗`
   re-brackets for nothing, being strict here]],
  [#P(p-meet-idem, s: 60%) #v(-7pt) \ #src[*idempotent:* the one that is not bookkeeping — the lax
   copy law is the whole of it, worked in allegory2]],
)

So `≤` is the order this monoid induces. `R ∩ S ≤ R` comes from the unit, and idempotency turns
anything under both `S` and `T` into something under `S ∩ T`, since `R = R ∩ R ≤ S ∩ T`.

And one law relating `∩` to composition, which is *not* an equation:

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*semi-distributivity, and what supplies it*], [*picture*]),

  [`R (S ∩ T) ⊑ R S ∩ R T` — the lax copy law. #src[Equality exactly when `R` is single valued: the Maps section's
   `F (R ∩ S) = F R ∩ F S`.]], P(p-semidistrib),
)

= Unitary and pre-tabular — what the other direction needs

#table(
  columns: (3.2cm, 1fr, 1fr),
  align: (left + top, left + top, left + top),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*condition*], [*allegory*], [*Frobenius side*]),

  [*unitary*],
  [`T` is a *unit* when `𝟙 T` is the largest endomorphism on it and every object carries an entire
   arrow to it. A unit is what makes `⊤` exist.],
  [*free.* `𝕀` is the unit object, `𝟙 ≤ ⊸ ⟜` says `⊸` is entire, and `⊤ = ⊸ ⟜` is maximal.],

  [*pre-tabular*],
  [`f, g` *tabulate* `R` when both are maps, `R = f° g`, and

   #row((cetz.canvas(length: 0.72cm, { meet((0, 0), $f f°$, $g g°$) }),
         $=$,
         cetz.canvas(length: 0.72cm, { wire((0, 0), (1.5, 0)) })))

   `R` is *tabular* when some pair tabulates it, the allegory *pre-tabular* when every arrow lies
   under a tabular one.],
  [*this is what `⊗` is.* Given unitarity it reduces to tabulating each `⊤`, and a tabulation of `⊤`
   is an object `n ⊗ m` with its two projections. One side derives the product from tabulations, the
   other posits it.],
)

Together: *cartesian bicategory of relations ≃ unitary pre-tabular allegory*.

#pagebreak(weak: true)
= Union

Past what the definition can build: a union needs a *biproduct* on top of the Frobenius structure.
It draws as a *tape* — the rounded wrapper is the second product, and its fork and join open and
close a branch a particle takes exactly one of. #src[The residual, which needs a second composition
with linear adjoints, is in the division section below.]

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*statement*], [*picture*]),

  [`R ⊑ R ∪ S` #h(4pt) #src[`union R S := ⟨R, S⟩ [𝟙, 𝟙]`: offer both branches, then forget which was
   taken.]],
  P(p-union-left),

  [`R ∪ S = S ∪ R`], P(p-union-comm),
  [`⊥ ∪ R = R` #h(4pt) #src[`⊥` routes through the zero object; there is no shape for it.]],
  P(p-bot-union),
  [`R (S ∪ T) = R S ∪ R T` — composition distributes over union, which `∩` does not.],
  P(p-comp-union),
  [`(R ∪ S)° = R° ∪ S°`], P(p-conv-union),
  [`R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)` — what makes the whole *distributive*, and the one picture with
   both layers in it.], P(p-distrib, s: 78%),
)

The last of Freyd's §2.21 equations that have no picture here — a tape around nothing, or a tape
around what is already inside it, is not worth drawing. `R` = people who admire `a`, `S` = people who
admire `b` throughout.

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*equation*], [*the reading*]),

  [`R ∪ (S ∩ R) = R` #h(10pt) `(R ∪ S) ∩ R = R` #h(4pt) #src[absorption]],
  [People who admire `a`, or who admire both: still the people who admire `a`. People who admire `a`
   or `b`, and who admire `a`: the same. The smaller side of each pair is already inside the larger.],

  [`R ⊥ = ⊥` #h(4pt) #src[`R 0_S = 0_{R S}` — and `⊥ R = ⊥` on the other side]],
  [Admiring someone and then taking a step that leads nowhere gets you nowhere. `⊥` is a two-sided
   zero for composition, as `⊤` is not.],
)

== Where the list comes from

Adjunctions on the hom-set. `Δ` is the diagonal of the hom-set `a ⟶ b`, `Δ R = (R, R)` #src[one
level up from the copy `◁`, which is an arrow of the allegory itself], and the argument in every row
is the same one: a left adjoint preserves joins.

#table(
  columns: (4.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*adjunction*], [*what it forces*]),

  [`∪ ⊣ Δ ⊣ ∩`],
  [`R ∪ S ⊑ T` iff `R ⊑ T` and `S ⊑ T`, and `T ⊑ R ∩ S` iff `T ⊑ R` and `T ⊑ S`. A left adjoint of
   `Δ` *is* a binary join, so idempotency, commutativity, associativity and both absorption laws
   arrive with it — and nothing else does. The chain says exactly that the hom-set is a lattice.],

  [`⊥ ⊣ !`],
  [The same at arity zero, the join of nothing: `⊥ ∪ R = R`.],

)

// The COLLAPSED domain: `R` ends in a `⊸`, so nothing `R` computes can leave, and what the upper
// strand carries out is the input itself — the coreflexive on the values `R` accepts.  Bound rather
// than drawn in place: it is the right-hand step of both chains below.  `rel` draws the chain's
// relation symbol at the picture's LEFT EDGE, since a `$=$` set beside a canvas sits on the canvas's
// baseline, not on its horizon.
#let domstr(rel: none) = cetz.canvas(length: 0.8cm, {
  let y = 0.85
  if rel != none { lab(-1.2, 0, black)[#rel] }
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (3.75, y))
  wire((1.55, -y), (1.9, -y)); gbox((1.9, -y), [R]); wire((2.82, -y), (3.3, -y))
  wiredot((3.3, -y))
  lab(-0.35, 0, black)[$A$]; lab(4.1, y, black)[$A$]
})

#pagebreak(weak: true)
= Domain and range

#definition[
The *domain* `Dom R ≜ 𝟙 ∩ R R°` and the *range* `Ran R ≜ Dom R°`.
]

// THE MEET FIRST, then the stub.  The stub on its own does not look like `𝟙 ∩ R R°` — one strand
// carries no box at all and the return leg is gone — so the definition is drawn literally beside it
// and the collapse is what the chain shows.
#chain((cetz.canvas(length: 0.8cm, {
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
   so `R° ▷` cuts to `⊸` — Frobenius]), s: 100%)

Running `R` and throwing the result away leaves only the fact that `R` could fire, and `Ran R` is the
same picture with the box mirrored. In `Rel` both steps are `{(a,a) : ∃b. a R b}`.

#align(center, table(
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
))

== Sliding the discard

`Dom (R S) ⊑ Dom R`, and a single glyph for `Dom` would have nothing to slide: with the box and the
discard drawn apart, the law is one dot walking back along the lower strand.

#chain((cetz.canvas(length: 0.8cm, {
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
   — the discard slides back past `S`]), s: 100%)

Equality is `S` entire, which is the same picture read as `Dom R = 𝟙 ⟺ R` entire.

#pagebreak(weak: true)
= Maps

Every arrow is lax for `◁` and for `⊸` by axiom, and for `▷` and `⟜` by the lax monoid section. All four
hold for *every* arrow, their REVERSES do not, and each reverse holding is a property of the arrow.
The right-hand column is the *adjoint* form, which is the definition
used here because it is literally the allegory's `Simple` and `Entire`; that the two forms agree is
a separate theorem, not proved here.

// A 2×2, not a list of four: the ROW says which composite the law is about — `R° R` on top,
// `R R°` below — and the COLUMN which way the containment runs, `𝟙 ⊑ …` on the left and `… ⊑ 𝟙` on
// the right.  The four properties then sit at the four corners of one square, and each one's
// opposite is the cell diagonally across.  The name goes under its own picture, so the picture is
// read first and the word only names what was just seen.
#table(
  columns: (1fr, 1fr),
  align: center + horizon,
  inset: 10pt, stroke: 0.4pt + luma(190),

  [#P(p-sur49, s: 74%) #v(-4pt) *surjective* \ #src[`𝟙 ⊑ R° R`, that is, `R°` entire.]],
  [#P(p-sv46, s: 74%) #v(-4pt) *single valued* \ #src[`R° R ⊑ 𝟙`]],

  [#P(p-tot47, s: 74%) #v(-4pt) *entire* \ #src[`𝟙 ⊑ R R°`. With *single valued*, a *map*.]],
  [#P(p-inj48, s: 74%) #v(-4pt) *injective* \ #src[`R R° ⊑ 𝟙`]],
)

#table(
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
)

== Two adjunctions: `•f ⊣ •f°`, `f°• ⊣ f•`

#src[A box is `⊑`, top row over bottom row; #zw("/") is `f` and #zw("\\") is `f°`. The notation is
`notation_as_a_tool_of_thought_adjunction.typ`.]

#table(
  columns: (1fr, 1fr),
  align: center + horizon,
  inset: 10pt, stroke: 0.4pt + luma(190),

  [#zsq("*", "/\\") #v(4pt) *unit* \ #src[`𝟙 ⊑ f f°` — `f` entire]],
  [#zsq("\\/", "*") #v(4pt) *counit* \ #src[`f° f ⊑ 𝟙` — `f` single valued]],

  [#zw("/\\/") #h(3pt) = #h(3pt) #zw("/") #v(4pt) *snake* \ #src[`f f° f = f`]],
  [#zw("\\/\\") #h(3pt) = #h(3pt) #zw("\\") #v(4pt) *snake* \ #src[`f° f f° = f°`]],
)

#align(center, grid(columns: 2, column-gutter: 1.4cm, align: left,
  [`X f ⊑ Y` iff `X ⊑ Y f°` #h(6pt) #src[right]],
  [`f° Y ⊑ X` iff `Y ⊑ f X` #h(6pt) #src[left]],
))

#src[The right one IS `f ⊣ f°`: put `𝟙` in the dot and it hands back the unit and the counit. The
left one comes out flipped because composing on the left reverses order, `(f g)• = f• ∘ g•`.]

// Its own page: the ten rows are one table and the long-division figure heads them, so a break
// inside would separate the metaphor from the laws it explains.
#pagebreak(weak: true)
= `/` is all of

#definition[
#align(center, `x (R/S) y  ⟺  ∀p. y S p → x R p`)
#align(center, `x (S\R) y  ⟺  ∀p. p S x → p R y`)
#align(center, `/ compares images: S(y) ⊆ R(x).   \ compares preimages: S°(x) ⊆ R°(y).`)
#align(center, `example: A admires, H hates, W works for`)
#align(center, `x (A/H) y — x admires everyone y hates.`)
#align(center, `x (H\A) y — everyone who hates x admires y.`)
]


== `(R/S)(S/W) ⊑ R/W`

// ONE picture for the whole law.  A quotient is drawn as its numerator column, a shared people
// column, its denominator column (ADMIRES, people, HATES for `A/H`; HATES, people, WORKS for `H/W`),
// every arrow pointing at the person it names; the reader then answers by eye — is every arrow into
// a person from the H/W side matched by one from the A/H side? — and the answer is the arc.
// The three quotients share their columns: `y` relates via `H` to the pool on its left and again to
// the pool on its right, so the shared-pool column is repeated, once per quotient.  Above the
// columns the two legs `A/H`, `H/W` meet over the `y` that carries the composite; below them `A/W`
// spans the whole width in its own colour, and that it starts at BOTH `x`s while the path starts
// only at `x` is the strictness of the law, drawn.
// Colour marks WHICH node, not which column — the columns are already told apart by position, so
// spending a hue on them would leave nothing to tell `x` from `x'`.  First in a column blue,
// second pink, in every column.
#let PAL = (rgb("#1a5fb4"), rgb("#c2247f"))
#let ARC = rgb("#7d3c98")
#let RW = rgb("#26734d")
#let IY = (a: 2.4, b: 0.8, c: -0.8, d: -2.4)
// Nodes are drawn last, with a white fill, so an edge may start at the node's centre and let the box
// cover the stub — every edge then ends the same distance from its label, whatever its width.
#let node(x, y, c, w) = d.content((x, y), box(inset: 4pt, fill: white)[#text(10pt, c)[#w]])
// A column of nodes at x; a row is (y, label, the people it names).
#let nodes(x, rows) = for (k, row) in rows.enumerate() { node(x, row.at(0), PAL.at(k), row.at(1)) }
#let ings(x) = for (it, y) in IY { node(x, y, black, raw(it)) }
// Every arrow from column x into the shared-pool column xi, stopping on the side it comes from.
#let edges(x, xi, rows) = {
  let dir = if x < xi { -1 } else { 1 }
  for (k, row) in rows.enumerate() { for it in row.at(2) {
    d.line((x, row.at(0)), (xi + 1.05 * dir, IY.at(it)), mark: (end: ">", scale: 0.5),
      stroke: 0.75pt + PAL.at(k)) } }
}
// `h` is where the control points sit; the label goes on the curve's own midpoint, which is where
// the cubic actually is (`0.75h` from the axis, not `h`) — a label placed at `h` floats off a deep
// arc.  `cx` shortens the horizontal reach of those controls: the smaller it is, the sooner the
// curve dives, which is how the bottom arcs clear the shared-pool columns without going twice as deep.
#let arc(a, b, up, lab, col: ARC, h: 3.8, cx: 4) = {
  let (x0, y0) = (a.at(0), a.at(1) + 0.45 * up)
  let (x1, y1) = (b.at(0), b.at(1) + 0.45 * up)
  let c = (x1 - x0) / cx
  d.bezier((x0, y0), (x1, y1), (x0 + c, h * up), (x1 - c, h * up),
    mark: (end: ">", scale: 0.55), stroke: 0.9pt + col)
  d.content(((x0 + x1) / 2, 0.125 * y0 + 0.75 * h * up + 0.125 * y1),
    box(inset: 3pt, fill: white)[#text(9.5pt, col)[#lab]])
}
#let head(x, lab) = d.content((x, 3.9), text(9.5pt, luma(60))[#lab])
#let ADMIRES = ((1.6, `x`, ("a", "b", "c")),
              (-1.6, `x'`, ("a", "b")))
#let HATES = ((1.6, `y`, ("a", "b", "c")),
              (-1.6, `y'`, ("a", "b", "d")))
#let WORKS = ((0, `z`, ("a", "b")),)

#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  edges(-9.6, -4.8, ADMIRES); edges(0, -4.8, HATES); edges(0, 4.8, HATES); edges(9.6, 4.8, WORKS)
  arc((-9.6, 1.6), (-0.8, 1.6), 1, [`A/H` admires all])
  arc((0.8, 1.6), (9.6, 0), 1, [`H/W` hates all])
  arc((-9.6, 1.6), (9.6, 0), -1, [`A/W` admires all], col: RW, h: 5.4, cx: 8)
  arc((-9.6, -1.6), (9.6, 0), -1, [`A/W` admires all], col: RW, h: 7.0, cx: 8)
  nodes(-9.6, ADMIRES); ings(-4.8); nodes(0, HATES); ings(4.8); nodes(9.6, WORKS)
  head(-9.6, [`A` — `x` admires]); head(0, [`H` — `y` hates])
  head(9.6, [`W` — `z` works for])
})))

// The whole of each quotient in one line of English, laid out as the law reads: the two legs of the
// path first, the arrow they are contained in last.
#align(center, block(inset: (top: 2pt), text(10.5pt)[
  `x (A/H) y` — `x` admires everyone `y` hates \
  `y (H/W) z` — `y` hates everyone `z` works for \
  `x (A/W) z` — `x` admires everyone `z` works for
]))

`(A/H)(H/W)` is a path: `x` → `y` → `z`, and that is all of it. `A/W` also holds of
`x'`, who admires everyone `z` works for — but `x'` does not admire everyone anybody
hates, so nothing composes to it. The missing path is exactly the strictness of
// Boxed so the line breaker cannot split the law after a `/` — it lands at the end of the paragraph.
#box[`(R/S)(S/W) ⊑ R/W`].

// Two columns like every other table, one law per row.  The pictures here are the widest in the
// note — `le_div_iff` is a `⟺` between two containments, four sub-pictures in a row, 10.9cm before
// scaling — which is why the picture column gets the rest of the 22cm and the laws that used to
// share a row are split: one picture per row is what keeps them at readable size.
#table(
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

  [`(R/S)(S/W) ⊑ R/W` \ #src[Someone who admires all of a hate-list that already covers everyone
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

  [`R/𝟙 = R` \ #src[Dividing by `𝟙`: `p`'s list is just `{p}`, so admiring all of it is admiring `p`.]],
  P(p-div-one),

  [`R/(S₁ ∪ S₂) = R/S₁ ∩ R/S₂` \ #src[Admiring a combined hate-list is admiring each list in full.]],
  P(p-div-union),

  [`S\(R/W) = (S\R)/W` \ #src[Which is why `S\R/W` needs no bracket.]],
  P(p-ldiv-div),
)

Fifteen laws, fifteen pictures, and not one shows a generator: `∩`, `∪`, `°` and composition are what
the Frobenius generators build, and `/` is none of those — it is posited, with nothing to unfold.

== `/` is a right adjoint

// The unknown is `T` here and `X` in the table above: the two pictures below need the capitals `X`,
// `Y`, `Z` for the objects the elements `x`, `y`, `z` live in, and one letter cannot be both.
As a *picture*, "posited, with nothing to unfold" is exactly right. As a *law* it is not posited at
all — one line generates the whole table above:

#align(center, `T S ⊑ R   ⟺   T ⊑ R/S`)
#align(center, src[dividing by `S` is right adjoint to composing with `S`])

Both ends of the adjunction are that line read at an identity: `R/S ⊑ R/S` gives the *counit*
`(R/S) S ⊑ R`, and `T S ⊑ T S` gives the *unit* `T ⊑ (T S)/S`. Every law in the table is one pass
through the equivalence and back. Two of them in full:

#align(center, block(inset: (y: 4pt))[
  `T ⊑ R/(S₁ S₂)  ⟺  T (S₁ S₂) ⊑ R  ⟺  (T S₁) S₂ ⊑ R  ⟺  T S₁ ⊑ R/S₂  ⟺  T ⊑ (R/S₂)/S₁` \
  #src[out and back twice; in between, only `T (S₁ S₂) = (T S₁) S₂`] \
  #v(5pt)
  `T ⊑ R/(f S)  ⟺  T (f S) ⊑ R  ⟺  (T f) S ⊑ R  ⟺  T f ⊑ R/S  ⟺  T ⊑ (R/S) f°` \
  #src[same shape, and the last step is `f ⊣ f°` — being a map is all `f` is asked for]
])

The four generators with `∩`, `∪`, `°` and composition express exactly the regular fragment — `∃`,
`∧`, `=` — while `x (R/S) y ⟺ ∀p. y S p → x R p` carries a `∀`. The opaque box is therefore forced,
not lazy: drawing `/` needs a second composition beside `;`, which is what the calculus of
neo-Peircean relations adds (Bonchi, Di Giorgio, Haydon and Sobociński, Calculus-neo-peircean.pdf),
where `R/S = ¬(¬R ; S°)`.

Dividing by a map is the case where the `∀` costs nothing: in `R/f` it ranges over the single output
`f y`, so `∀p. y f p → x R p` collapses to `x R (f y)` — that is `R f°`, which is the map row of the
table above at `S := 𝟙`.

== `R/R` is a preorder, which is what a monad is here

A *monad* in a locally posetal 2-category is a 1-cell `M` with `𝟙 ⊑ M` and `M M ⊑ M` — a unit and a
multiplication, and with the hom-posets thin there is nothing else to give. In `Rel` that is a
reflexive transitive relation: a preorder. The table above proves both halves at `M := R/R`, and
names the preorder they define.

`(R/R) R = R` is then the action that makes `R` a module over that monad — Hinze and Marsden's
α : M ∘ A →̇ A (IntroString p. 83, laws (3.10a) and (3.10b)) at M := `R/R`, A := `R`. Their two
coherence conditions are free here: parallel 2-cells are unique, so any two of them are equal.

// Drawn by hand in the one-dimension-up language above — region an object, wire a relation, dot a
// 2-cell — read bottom to top, and left to right in diagram order, so the bottom boundary is the
// composite `(R/R) R` and the top boundary is what it lands in.
// `R/R` is an endo-wire on `X`, so the SAME fill lies on both sides of it: that is what a monad
// looks like here, not a colour left out.
#align(center, box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
  d.rect((-1.7, -1.2), (1.7, 1.2), fill: fb-ALLC, stroke: none)
  d.rect((-1.7, -1.2), (0.5, 1.2), fill: fb-MAPC, stroke: none)
  // `R` runs the full height: it is the wire the action lands ON, and landing on it changes nothing.
  d.line((0.5, -1.2), (0.5, 1.2), stroke: 1.1pt)
  d.bezier((-0.6, -1.2), (0.5, 0.15), (-0.6, -0.3), (0.0, 0.15), stroke: 1.1pt)
  fb-dot((0.5, 0.15), `α`, dx: 0.32)
  lab(-0.6, -1.48, black)[`R/R`]; lab(0.5, -1.48, black)[`R`]; lab(0.5, 1.48, black)[`R`]
  lab(-1.3, 0.7, luma(80))[$X$]; lab(1.1, 0.7, luma(80))[$P$]
})))

#align(center, src[Green is `X`, where `x` lives; purple is `P`, where the `p` of the definition
lives. `R/R : X ⟶ X` runs inside `X` and ends on `R : X ⟶ P` at the action `α`, which is
`(R/R) R ⊑ R`.])

== The whole family is one preorder

// The same fork with three labels and three regions.  FILL AND STROKE ARE SEPARATE PATHS: the
// closing segments of `Y` and `Z` run along the frame, they are not wires, and one
// `merge-path(close: true)` carrying both would draw a floor under each region.
// A third hue, because `X`, `Y`, `Z` are three different objects and two fills cannot tell them
// apart — the two above are one hue per region, and this picture has one region more.
#let fb-ZC = rgb("#faf0dc")
#align(center, box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
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
})))

#align(center, src[The same dot with one region more: `R/S : X ⟶ Y` and `S/W : Y ⟶ Z` come in,
`R/W : X ⟶ Z` goes out. Green `X`, purple `Y`, amber `Z`.])

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
`(R/S)(S/S) ⊑ R/S`, each the counit `(R/S) S ⊑ R` with one action whiskered on — `(R/R) R = R` on the
left, `(S/S) S = S` on the right.

#pagebreak(weak: true)
= `x (Admires%Hates) y` is `x admires only all whom y hates`

#definition[
$frac(R, S)$ `≜ (R/S) ∩ (S/R)°`. In `Rel` `x` and `y` has the same image:
`∀p. (x R p ⟺ y S p)`
]

// The meet read one factor at a time, in the vocabulary of the section above: `/` supplies ALL, the
// converse of the mirror division supplies ONLY, and the meet is what names this section.
#align(center, block(inset: (top: 2pt), text(10.5pt)[
  `x (A/H) y` — `x` admires everyone `y` hates \
  `x ((H/A)°) y` — `x` admires only people `y` hates \
  `x ((A/H) ∩ (H/A)°) y` — `x` admires only and all whom `y` hates
]))

`x` admires exactly whom `y` hates: `/` is *all of*, $frac(R, S)$ is *only all of*.

// The same admires / people / hates picture as the division section, with one column each side and
// the people between: matching is read by eye as "the two fans land on the same dots".
// Weight, not hue, carries the comparison — the heavy fans are the pair being compared, the washed
// out ones the pairs that fail, so the reader sees WHICH two are claimed to match before reading
// anything.  Colour stays with the family, blue for `A` and pink for `H`, as everywhere else here.
#let syqnode(p, c, fill, w, ring: none) = d.content(p,
  box(inset: 4pt, fill: fill, radius: 3pt, stroke: ring)[#text(10pt, c)[#w]])
// Every arrow stops short of the dot it names, on the side it comes from, so the two columns' heads
// meet over the person instead of piling onto it.
#let syqedge(from, to, col, w) = {
  let dir = if from.at(0) < to.at(0) { -1 } else { 1 }
  d.line(from, (to.at(0) + 0.42 * dir, to.at(1)),
    mark: (end: ">", scale: if w > 0.9 { 0.55 } else { 0.4 }), stroke: w * 1pt + col)
}
// The cast and the numbers are the division section's, read for equality instead of containment.
#let ADMIRERS = (x1: (-5.2, 1.8), x2: (-5.2, -1.8))
#let HATERS = (y1: (5.2, 1.8), y2: (5.2, -1.8))
#let PEOPLE = (a: (0, 2.4), b: (0, 0.8), c: (0, -0.8), d: (0, -2.4))

#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  // `A`: who each `x` admires.  `H`: who each `y` hates.  `x` and `y` name the same three.
  for p in ("a", "b", "c") { syqedge(ADMIRERS.x1, PEOPLE.at(p), PAL.at(0), 1.1) }
  for p in ("a", "b") { syqedge(ADMIRERS.x2, PEOPLE.at(p), PAL.at(0).lighten(60%), 0.7) }
  for p in ("a", "b", "c") { syqedge(HATERS.y1, PEOPLE.at(p), PAL.at(1), 1.1) }
  for p in ("a", "b", "d") { syqedge(HATERS.y2, PEOPLE.at(p), PAL.at(1).lighten(60%), 0.7) }

  // The shared column, filled: exactly the people both sides of the matched pair reach.
  // `d` stays hollow — `y'` reaches it and no admirer does.
  for p in ("a", "b", "c") { d.circle(PEOPLE.at(p), radius: 0.17, fill: ARC, stroke: ARC) }
  d.circle(PEOPLE.d, radius: 0.17, fill: white, stroke: 0.9pt + black)
  // Named as in the division picture, and above the dot: beside it the name would land on a fan.
  for (p, q) in PEOPLE { d.content((q.at(0), q.at(1) + 0.62), raw(p)) }

  // The result: the one pair whose two sets agree.  It runs over the top from `x` to `y` — an
  // arc slung underneath would start below `x'` and read as the wrong pair.
  d.bezier((ADMIRERS.x1.at(0), 2.35), (HATERS.y1.at(0), 2.35), (-2.6, 4.4), (2.6, 4.4),
    mark: (end: ">", scale: 0.6), stroke: 1pt + ARC)
  // Clear of the curve's apex (y ≈ 3.9), because the fraction is two lines tall and its bar sitting
  // on the arc would read as part of it.
  d.content((0, 4.4), box(inset: 3pt, fill: white)[#text(10pt, ARC)[$frac(A, H)$]])

  syqnode(ADMIRERS.x1, ARC, rgb("#f2e9f8"), `x`, ring: 0.7pt + ARC)
  syqnode(ADMIRERS.x2, black, white, `x'`)
  syqnode(HATERS.y1, ARC, rgb("#f2e9f8"), `y`, ring: 0.7pt + ARC)
  syqnode(HATERS.y2, black, white, `y'`)
  // The family names sit outside the columns at mid-height: the top belongs to the arc, and beside
  // an arrow they would land on another arrow.
  d.content((-6.5, 0), text(10pt, PAL.at(0))[`A`]); d.content((6.5, 0), text(10pt, PAL.at(1))[`H`])
})))

A meet of two long divisions, the second turned round by the converse frame:

#P(p-symmdiv, s: 66%)
#align(center, src[exported from the definition, not transcribed])

#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [$(frac(R, S))^circle.small = frac(S, R)$ \ #src[Matching is symmetric.]],
  P(p-sdiv-recip),

  [$frac(R, S) frac(S, W) ⊑ frac(R, W)$ \ #src[And transitive.]],
  P(p-sdiv-comp),
)

No pictures for the rest of §2.35: symmetric division is not built from the generators.

#table(
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
)

== Straight

#definition[
`S` is *straight* when $frac(S, S) = 𝟙$ — no two `y`s hate the same people.
]

#table(
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
)

#pagebreak(weak: true)
= Power allegories

// `∋` is a large operator in math, so a plain `∋_R` sets the R UNDERNEATH it; `attach(.., br: ..)`
// puts the subscript where Freyd has it.  `slash` for a related reason: a plain `/` in math sets a
// stacked fraction, and in this note a stacked fraction is symmetric division.  Defined out here,
// not inside the block, because the table below the block subscripts `∋` too.
#let e(x) = math.attach(math.class("normal", [∋]), br: x)

#definition[
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

`R □` is `R`'s target, an identity arrow. For `R : A ⟶ B` write `∋ : [B] ⟶ B`, dropping the
subscript.
]

In `Rel` its source is the powerset of its target and `l ∋ i` iff `i ∈ l`, and `∋` reads a
list `l` back into the people on it.

#definition[
`Λ(R) ≜` $frac(R, ∋)$ ` : A ⟶ [B]`, for `R : A ⟶ B`. The list-of map: send `x` to the list of the
people `x` admires.
]

// THE WALL IS THE PICTURE, and this is the key to the four drawn rows of the table below — hence its
// place ahead of them.  `Λ` and `∋` are two graphical moves: seal a wire inside a box, open the box
// and let what is inside come out.  Drawn left to right like every other string diagram in this
// note, so `Λ(R) ∋` reads in the order it is written.
#let fb-WALL = rgb("#2f6ea8")
#let fb-FILL = rgb("#eaf2fb")
// A `[B]`-wire: two thin strands, so a boxed wire is visibly not a plain one.  Each strand is
// thinner than `strdiag`'s `lw` — at full weight the pair reads as two wires side by side rather
// than as one wire one level down.
#let fb-wire(a, b) = {
  for o in (0.055, -0.055) {
    d.line((a.at(0), a.at(1) + o), (b.at(0), b.at(1) + o), stroke: (thickness: 0.8pt))
  }
}
// The box IS the power relator: what is drawn inside is one level down, `B` inside ⇒ `[B]` outside.
// The parameter is `name`, not `lab`, because `lab` is this note's 10pt in-figure label and the body
// below calls it — a parameter of that name would shadow it here.
#let fb-region(a, b, name: [`P`]) = {
  d.rect(a, b, radius: 0.2, fill: fb-FILL, stroke: (thickness: 1pt, paint: fb-WALL))
  lab((a.at(0) + b.at(0)) / 2, b.at(1) + 0.3, fb-WALL)[#name]
}
// A bare wall the wire crosses — the box opened, which is what `∋` does.  `side` and `up` push the
// name clear of whichever end of the wall the wire runs into.
#let fb-wall(x, y0, y1, name, side: 1, up: true) = {
  d.line((x, y0), (x, y1), stroke: (thickness: 1pt, paint: fb-WALL))
  lab(x + 0.42 * side, if up { y1 + 0.22 } else { y0 - 0.22 }, fb-WALL)[#name]
}
// `{·}`, the unit.  `chamfer: false` is this note's mark for a map, and being a map is the whole
// reason `{·}` may be moved past another box while `∋` may not.
#let fb-sing(p) = gbox(p, `{·}`, chamfer: false, w: 1.0)

One convention: a `[B]`-wire is drawn double, because it is a `B`-wire one level down — inside the
box. The box is the power relator `P`, which the relator section below defines: a box holding
`R : B ⟶ C` is `P R : [B] ⟶ [C]`. Inside the box lives the allegory, outside only maps, and
`i : Map(𝒜) ↪ 𝒜` is the inclusion that forgets the difference. The adjunction `i ⊣ P`, that is
`𝒜(A, B) ≅ Map(A, [B])`, has the two ends:

// The two ends share one canvas, parted by a hairline, because neither is a picture on its own: the
// point is that they face opposite ways, `[B]` in and `B` out against `A` in and `[A]` out.
#align(center, box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
  fb-wire((-3.9, 0), (-2.6, 0)); lab(-4.2, 0, black)[$[B]$]
  fb-wall(-2.6, -0.5, 0.5, [`∋`])
  wire((-2.6, 0), (-1.6, 0)); lab(-1.35, 0, black)[$B$]
  lab(-2.6, -0.95, black)[counit: open the box]

  fb-rule(0.2, -1.1, 1.0)

  wire((1.6, 0), (2.6, 0)); lab(1.35, 0, black)[$A$]
  fb-sing((2.6, 0))
  fb-wire((3.6, 0), (4.9, 0)); lab(5.2, 0, black)[$[A]$]
  lab(3.1, -0.95, black)[unit: the one-person list]
})))

#align(center, src[`Λ` is neither of them — it is the transpose the adjunction gives,
`Λ(R) = {·} (P R)`: make the singleton, then push `R` through the box.])

#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [$#e[R] □ = R □$, #h(4pt) $#e[R] = #e[R □]$],
  [`∋` has the same target as `R`, and replacing `R` by the identity at that target leaves it
   unchanged: one `∋` per object, not per arrow.],

  [`∋` is *thick*],
  [*Comprehension*: every `x` has a list of exactly the people `x` admires. Equivalently every `R`
   factors as a map followed by `∋`.],

  [`∋` is *straight*, that is $frac(∋, ∋) ⊑ 𝟙$],
  [*Extensionality*: two lists with the same people are the same list.],

  [`Λ(R)` is simple],
  [`∋` is straight, and dividing by a straight arrow is simple. At most one list per `x`.],

  [`Λ(R)` is entire `⟺ ∋` thick],
  [`Dom` $frac(R, ∋)$ `= 𝟙 ∩ (R/∋)(∋/R)`, the domain row above. At least one list per `x`, so
   `Λ(R)` is a *map*.],

  // FOUR ROWS ARE DRAWN, not read out: they are the four laws that are moves of the box calculus,
  // and the move is what the picture shows.  Column one keeps the law and one line of gloss, column
  // two the picture, exactly as the division section's table is laid out.  `P` centres and shrinks
  // to the cell — 92%, its default, is what the fusion picture (the widest of the four) needs.
  [`Λ(R) ∋ = R` \ #src[Everything left of the `∋` wall is `Λ(R)`; open the wall and what was inside
   comes out unchanged. That is the β of this calculus.]],
  P(cetz.canvas(length: 1cm, {
    wire((-4.6, 0), (-3.8, 0)); lab(-4.85, 0, black)[$A$]
    fb-sing((-3.8, 0))
    fb-wire((-2.8, 0), (-2.4, 0))
    fb-region((-2.4, -0.55), (-0.8, 0.55))
    gbox((-2.15, 0), `R`)
    fb-wire((-0.8, 0), (-0.2, 0))
    fb-wall(-0.2, -0.55, 0.55, [`∋`])
    wire((-0.2, 0), (0.6, 0)); lab(0.85, 0, black)[$B$]

    lab(1.6, 0, black)[$=$]

    wire((2.6, 0), (3.4, 0)); lab(2.35, 0, black)[$A$]
    gbox((3.4, 0), `R`)
    wire((4.32, 0), (5.1, 0)); lab(5.35, 0, black)[$B$]
  })),

  [`Λ(R)` is the only map with `Λ(R) ∋ = R`],
  [Two maps naming the same people name the same list — extensionality again.],

  [`F ⊑ Λ(F ∋)`, `F` simple],
  [A partial choice of lists is inside the total one.],

  [`[α]` = source of `∋`, the *power-object*],
  [Every list over `α`.],

  [`{·} ≜ Λ(𝟙)`, the *singleton map*, monic],
  [The one-person list. `Λ(𝟙)Λ°(𝟙) ⊑` $frac(𝟙, ∋) frac(∋, 𝟙) ⊑ frac(𝟙, 𝟙) ⊑ 𝟙$.],

  // The `∋` wall stands INSIDE the box here, hence `up: false`: its name goes below, where the box's
  // own `P` is not.
  [`Λ(∋) = 𝟙` \ #src[Make the list of a list, then read it back one level down. Straightness itself,
   and one of the two triangle identities of `i ⊣ P`; the other is `{·} ∋ = 𝟙`.]],
  P(cetz.canvas(length: 1cm, {
    fb-wire((-4.6, 0), (-3.8, 0)); lab(-4.9, 0, black)[$[B]$]
    fb-sing((-3.8, 0))
    fb-wire((-2.8, 0), (-2.4, 0))
    fb-region((-2.4, -0.55), (-0.8, 0.55))
    fb-wall(-1.6, -0.55, 0.55, [`∋`], up: false)
    fb-wire((-0.8, 0), (0.0, 0)); lab(0.3, 0, black)[$[B]$]

    lab(1.3, 0, black)[$=$]

    fb-wire((2.3, 0), (4.6, 0)); lab(2.0, 0, black)[$[B]$]; lab(3.45, 0.32, black)[$𝟙$]
  })),

  [*fusion:* `Λ(f R) = f Λ(R)`, `f` a map \ #src[`f` is a plain rectangle — a map, so it may cross
   the `{·}` node. That is naturality of the unit, `f {·} = {·} (P f)`, and it is the whole content
   of fusion; a chamfered box is stuck on the side it is on.]],
  P(cetz.canvas(length: 1cm, {
    wire((-5.0, 0), (-4.2, 0)); lab(-5.25, 0, black)[$A'$]
    fb-sing((-4.2, 0))
    fb-wire((-3.2, 0), (-2.8, 0))
    fb-region((-2.8, -0.55), (-0.5, 0.55))
    gbox((-2.55, 0), `f`, chamfer: false)
    wire((-1.63, 0), (-1.45, 0))
    gbox((-1.45, 0), `R`)
    fb-wire((-0.5, 0), (0.3, 0)); lab(0.6, 0, black)[$[B]$]

    lab(1.4, 0, black)[$=$]

    wire((2.4, 0), (3.1, 0)); lab(2.15, 0, black)[$A'$]
    gbox((3.1, 0), `f`, chamfer: false)
    wire((4.02, 0), (4.3, 0))
    fb-sing((4.3, 0))
    fb-wire((5.3, 0), (5.7, 0))
    fb-region((5.7, -0.55), (7.1, 0.55))
    gbox((5.95, 0), `R`)
    fb-wire((7.1, 0), (7.9, 0)); lab(8.2, 0, black)[$[B]$]
  })),

  [`Λ(f) = f {·}`, `f` a map],
  [Rename first or take singletons first — the fusion row above at `R = 𝟙`.],

  [$frac(R, S) = Λ(R) Λ^circle.small (S)$ \ #src[`x` and `y` match exactly when the two boxes hold
   one and the same list — the `[B]`-wire joining them is the whole statement.]],
  P(cetz.canvas(length: 1cm, {
    wire((-5.0, 0), (-4.2, 0)); lab(-5.25, 0, black)[$x$]
    fb-sing((-4.2, 0))
    fb-wire((-3.2, 0), (-2.8, 0))
    fb-region((-2.8, -0.55), (-1.4, 0.55))
    gbox((-2.55, 0), `R`)
    fb-wire((-1.4, 0), (1.4, 0)); lab(0, 0.45, fb-WALL)[one list]
    fb-region((1.4, -0.55), (2.8, 0.55), name: [`P°`])
    gbox((1.65, 0), `S`, flip: true)
    fb-wire((2.8, 0), (3.2, 0))
    gbox((3.2, 0), `{·}°`, chamfer: false, w: 1.0, flip: true)
    wire((4.2, 0), (5.0, 0)); lab(5.25, 0, black)[$y$]
  })),

  [`C` a topos `⟹ Rel(C)` a power allegory],
  [And back: a unitary tabular power allegory has `Map(A)` a topos. Extensionality and comprehension
   are all a topos adds.],
)

= The same adjunction in Marsden's 2-cell calculus

Other language, other level. Here a *wire* is a functor, a *dot* is a natural transformation, a
*region* is a category, and the picture is read bottom to top. Colour marks the category, and for
`F : C ⟶ D` the wire carries the source `C` on its left and the target `D` on its right (Marsden
Def 3.1). `R` itself cannot appear — it is an arrow, not a 2-cell — which is exactly the trade: this
language draws the adjunction, the section above draws the arrows inside it.

// The two functors and the two 2-cells, side by side.  Each functor panel is split UNEVENLY: the
// half that has to hold `Map(𝒜)` gets the room, the half holding `𝒜` does not.  The names are kept
// so the colour rule can be checked by reading rather than by counting.
// FILL AND STROKE ARE SEPARATE PATHS on the cup and the cap.  One `merge-path(close: true)` carrying
// both would stroke the closing segment too, drawing a line across the top of the cup that joins the
// `i` and `P` legs — and there is no such line: it is one wire that bends, its two legs running free
// to the frame edge.  The snakes below are built the same way.
#align(center, box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
  // ---- i : Map(𝒜) ⟶ 𝒜        source `Map(𝒜)` on the left, target `𝒜` on the right
  d.rect((-1.0, -1), (1.8, 1), fill: fb-ALLC, stroke: none)
  d.rect((-1.0, -1), (0.8, 1), fill: fb-MAPC, stroke: none)
  d.line((0.8, -1), (0.8, 1), stroke: 1.1pt)
  lab(0.8, 1.28, black)[`i`]
  lab(-0.1, -0.75, luma(80))[`Map(𝒜)`]; lab(1.3, -0.75, luma(80))[`𝒜`]

  // ---- P : 𝒜 ⟶ Map(𝒜)        the mirror: source `𝒜` left, target `Map(𝒜)` right
  d.rect((2.4, -1), (5.2, 1), fill: fb-MAPC, stroke: none)
  d.rect((2.4, -1), (3.4, 1), fill: fb-ALLC, stroke: none)
  d.line((3.4, -1), (3.4, 1), stroke: 1.1pt)
  lab(3.4, 1.28, black)[`P`]
  lab(2.9, -0.75, luma(80))[`𝒜`]; lab(4.3, -0.75, luma(80))[`Map(𝒜)`]

  // ---- unit {·} : Id ⇒ i P    a cup, legs `i` (left) and `P` (right), so the inside of the U —
  //      right of `i`, left of `P` — is `𝒜`, and the ground outside it is `Map(𝒜)`, the category
  //      the unit's two arrows `Id` and `i P` both run in.
  d.rect((5.8, -1), (7.8, 1), fill: fb-MAPC, stroke: none)
  d.merge-path(close: true, fill: fb-ALLC, stroke: none, {
    d.line((6.4, 1), (6.4, 0.1))
    d.bezier((6.4, 0.1), (7.2, 0.1), (6.4, -0.55), (7.2, -0.55))
    d.line((7.2, 0.1), (7.2, 1))
  })
  d.line((6.4, 1), (6.4, 0.1), stroke: 1.1pt)
  d.bezier((6.4, 0.1), (7.2, 0.1), (6.4, -0.55), (7.2, -0.55), stroke: 1.1pt)
  d.line((7.2, 0.1), (7.2, 1), stroke: 1.1pt)
  fb-dot((6.8, -0.31), `{·}`, dx: 0, dy: -0.32)
  lab(6.4, 1.28, black)[`i`]; lab(7.2, 1.28, black)[`P`]

  // ---- counit ∋ : P i ⇒ Id    a cap, legs `P` (left) and `i` (right), so the inside of the ∩ is
  //      `Map(𝒜)` and the ground is `𝒜`, where `P i` and `Id` both run
  d.rect((8.4, -1), (10.4, 1), fill: fb-ALLC, stroke: none)
  d.merge-path(close: true, fill: fb-MAPC, stroke: none, {
    d.line((9.0, -1), (9.0, -0.1))
    d.bezier((9.0, -0.1), (9.8, -0.1), (9.0, 0.55), (9.8, 0.55))
    d.line((9.8, -0.1), (9.8, -1))
  })
  d.line((9.0, -1), (9.0, -0.1), stroke: 1.1pt)
  d.bezier((9.0, -0.1), (9.8, -0.1), (9.0, 0.55), (9.8, 0.55), stroke: 1.1pt)
  d.line((9.8, -0.1), (9.8, -1), stroke: 1.1pt)
  fb-dot((9.4, 0.38), `∋`, dx: 0, dy: 0.32)
  lab(9.0, -1.28, black)[`P`]; lab(9.8, -1.28, black)[`i`]
})))

#align(center, src[the two functors, then the unit `{·}` as a cup and the counit `∋` as a cap])

// Two checks the colours have to pass, and they are why every fill above is stated twice — once as
// a ground and once as the region the wire cuts out of it.  (1) Crossing a wire changes the colour,
// so along any horizontal cut the two alternate at every crossing.  (2) The two sides of an `=` must
// agree on their outermost regions: the plain wire on the right has one colour to its left and the
// other to its right, and those are the far-left and far-right colours of the snake on the left.
#align(center, box(inset: (y: 6pt), cetz.canvas(length: 1cm, {
  // ---- snake (5a):  {·} ∋ = 𝟙 on i
  // The merge-path is the region LEFT of the zigzag, which for `i` is its source `Map(𝒜)`; the
  // ground is the region to its right, the target `𝒜`.
  d.rect((-1.0, -1.2), (2.6, 1.2), fill: fb-ALLC, stroke: none)
  d.merge-path(close: true, fill: fb-MAPC, stroke: none, {
    d.line((-1.0, 1.2), (0, 1.2)); d.line((0, 1.2), (0, -0.2))
    d.bezier((0, -0.2), (0.9, -0.2), (0, -0.85), (0.9, -0.85))
    d.line((0.9, -0.2), (0.9, 0.2))
    d.bezier((0.9, 0.2), (1.8, 0.2), (0.9, 0.85), (1.8, 0.85))
    d.line((1.8, 0.2), (1.8, -1.2)); d.line((1.8, -1.2), (-1.0, -1.2))
  })
  d.line((0, 1.2), (0, -0.2), stroke: 1.1pt)
  d.bezier((0, -0.2), (0.9, -0.2), (0, -0.85), (0.9, -0.85), stroke: 1.1pt)
  d.line((0.9, -0.2), (0.9, 0.2), stroke: 1.1pt)
  d.bezier((0.9, 0.2), (1.8, 0.2), (0.9, 0.85), (1.8, 0.85), stroke: 1.1pt)
  d.line((1.8, 0.2), (1.8, -1.2), stroke: 1.1pt)
  fb-dot((0.45, -0.68), `{·}`, dx: 0, dy: -0.3); fb-dot((1.35, 0.68), `∋`, dx: 0, dy: 0.3)
  lab(0, 1.48, black)[`i`]; lab(1.8, -1.48, black)[`i`]

  lab(3.3, 0, black)[$=$]

  d.rect((4.0, -1.2), (6.0, 1.2), fill: fb-ALLC, stroke: none)
  d.rect((4.0, -1.2), (4.9, 1.2), fill: fb-MAPC, stroke: none)
  d.line((4.9, -1.2), (4.9, 1.2), stroke: 1.1pt)
  lab(4.9, 1.48, black)[`i`]; lab(4.9, -1.48, black)[`i`]

  fb-rule(7.0, -1.5, 1.5)

  // ---- snake (5b):  Λ(∋) = 𝟙 on P — the mirror, so the merge-path is the region RIGHT of the
  // zigzag, which for `P` is its target `Map(𝒜)`.
  d.rect((7.8, -1.2), (11.4, 1.2), fill: fb-ALLC, stroke: none)
  d.merge-path(close: true, fill: fb-MAPC, stroke: none, {
    d.line((11.4, 1.2), (10.4, 1.2)); d.line((10.4, 1.2), (10.4, -0.2))
    d.bezier((10.4, -0.2), (9.5, -0.2), (10.4, -0.85), (9.5, -0.85))
    d.line((9.5, -0.2), (9.5, 0.2))
    d.bezier((9.5, 0.2), (8.6, 0.2), (9.5, 0.85), (8.6, 0.85))
    d.line((8.6, 0.2), (8.6, -1.2)); d.line((8.6, -1.2), (11.4, -1.2))
  })
  d.line((10.4, 1.2), (10.4, -0.2), stroke: 1.1pt)
  d.bezier((10.4, -0.2), (9.5, -0.2), (10.4, -0.85), (9.5, -0.85), stroke: 1.1pt)
  d.line((9.5, -0.2), (9.5, 0.2), stroke: 1.1pt)
  d.bezier((9.5, 0.2), (8.6, 0.2), (9.5, 0.85), (8.6, 0.85), stroke: 1.1pt)
  d.line((8.6, 0.2), (8.6, -1.2), stroke: 1.1pt)
  fb-dot((9.95, -0.68), `{·}`, dx: 0, dy: -0.3); fb-dot((9.05, 0.68), `∋`, dx: 0, dy: 0.3)
  lab(10.4, 1.48, black)[`P`]; lab(8.6, -1.48, black)[`P`]

  lab(12.1, 0, black)[$=$]

  d.rect((12.8, -1.2), (14.8, 1.2), fill: fb-MAPC, stroke: none)
  d.rect((12.8, -1.2), (13.7, 1.2), fill: fb-ALLC, stroke: none)
  d.line((13.7, -1.2), (13.7, 1.2), stroke: 1.1pt)
  lab(13.7, 1.48, black)[`P`]; lab(13.7, -1.48, black)[`P`]
})))

#align(center, src[left: `{·} ∋ = 𝟙` on `i` — the triangle identity the section above only names. \
right: `Λ(∋) = 𝟙` on `P` — the straightness of the section above. Both are one wire pulled straight, \
the same shape as the snake in the cartesian-bicategory section with `i`, `P` for `◁`, `▷`.])

These two snakes are this note's own snake one bicategory down. `𝟙° = 𝟙` and *The slide*, in the
converse section near the top, pull the same wire straight — there the two bends are `⟜◁` and `▷⊸`
and the wire is an object of `𝒜`, here they are `{·}` and `∋` and the wire is a functor. The one real
difference is how often the situation arises: in `Rel` every object is self-dual, so every arrow has
its `°` and the snake costs nothing, while in `Cat` an adjoint is rare — `i ⊣ P` is something a power
allegory asserts, not something every category has.

What this buys and what it does not. The wall is genuine graphical structure — sealing, opening, and
"only maps cross" are the three rules, and `Λ(R) ∋ = R`, `Λ(∋) = 𝟙`, `Λ(f R) = f Λ(R)` are those
three rules and nothing more. What it does not buy: the wall is *not* built from `◁`, `⊸`, `▷`, `⟜`.
Those four generate `∩`, `∪`, `°` and composition, and the power object is extra structure, posited
the same way `/` is — which is why the fifteen `/`-pictures in the division section above show black
boxes too.

#pagebreak(weak: true)
= Relator

#definition[
Every hom-set of an allegory is a poset, so an allegory is a *locally posetal 2-category*: the 2-cell
from `R` to `S` IS `R ⊑ S`. A *relator* `F : 𝒞 ⟶ 𝒟` is a 2-functor between allegories:

  #align(center, block(inset: (y: 6pt))[
    #text(12.5pt)[`F 𝟙 = 𝟙` #h(1cm) `F(R S) = (F R)(F S)` #h(1cm) `R ⊑ S ⟹ F R ⊑ F S`]
  ])

Preserving `°` is *not* asked for — `°` is an identity-on-objects involution `𝒞ᵒᵖ ⟶ 𝒞`, no part of
the 2-category.
]

- For `f` a map, `F f` is a map and `F(f°) = (F f)°`.
- Over a *tabular* allegory a functor is a relator `⟺` it preserves `°`.
- A relator is fixed by what it does to maps.
- `F(R ∩ S) ⊑ (F R) ∩ (F S)`, and strictly.
- `F(X ∩ Y) = (F X) ∩ (F Y)` for `X, Y` coreflexive.
- `F(Dom R) = Dom(F R)` for `F` preserving `°`.

The *power relator* `P` — `x (P R) y ⟺ (∀a ∈ x. ∃b ∈ y. a R b) ∧ (∀b ∈ y. ∃a ∈ x. a R b)` — is where
the fourth is strict: for `R = {(a₁,b₁), (a₂,b₂)}` and `S = {(a₁,b₂), (a₂,b₁)}` the pair
`({a₁,a₂}, {b₁,b₂})` is in `P R ∩ P S`, while `R ∩ S = ∅`.

== The pairing `⟨R,S⟩`

#definition[
The *pairing* of `R : C ⟶ A` and `S : C ⟶ B` is `⟨R,S⟩ ≜ R π₁° ∩ S π₂°`, where `(π₁, π₂)` is the
tabulation of `⊤`.
]

#align(center, block(inset: (y: 6pt))[
  `⟨R,S⟩ π₁ = (Dom S) R` #h(1.4cm) `⟨R,S⟩ π₂ = (Dom R) S`
])

// TWO PICTURES OF ONE ARROW, side by side: Freyd's commutative diagram and this note's Frobenius
// string diagram.  Both are HAND-DRAWN — `./scripts/diag-export` walks a Lean TYPE, and `pair` lives
// in the allegory layer (`AOP/A5_2.lean`), not in the `diag/` bicategory the exporter draws.
// LAID OUT LEFT TO RIGHT, source at the left: every string diagram in this note runs that way, and
// two pictures of the same arrow that disagree about which way it flows cannot be read together.
// That is a quarter turn off the usual commutative-diagram habit of putting the product on top.
//
// `ar` pulls both ends back off the node centres: these edges carry ARROWHEADS, and a head drawn at a
// centre is buried under that node's own white box.  `s0`, `s1` are how far to stay clear at each end
// — 0.95 leaving a two-letter box like `A × B` sideways, 0.55 entering one from above or below.  Top
// level, not a `let` inside the canvas: the `R × S` figure below draws the same kind of edge.
#let ar(a, b, col, dash: none, s0: 0.45, s1: 0.45) = {
  let (dx, dy) = (b.at(0) - a.at(0), b.at(1) - a.at(1))
  let n = calc.sqrt(dx * dx + dy * dy)
  d.line((a.at(0) + s0 / n * dx, a.at(1) + s0 / n * dy),
    (b.at(0) - s1 / n * dx, b.at(1) - s1 / n * dy),
    mark: (end: ">", scale: 0.5), stroke: (thickness: 0.75pt, paint: col, dash: dash))
}
// `◁` then `R ⊗ S`: the copy dot is the whole difference between this picture and `R × S` below.
// Bound rather than drawn in place — it is also the last step of the collapse chain further down.
// `eq` draws the chain's `=` at the LEFT EDGE of the picture, the way `./scripts/diag-export` places
// it: a `$=$` set beside the canvas instead sits on the canvas's baseline, not on its horizon.
#let pairstr(eq: false) = cetz.canvas(length: 0.8cm, {
  let y = 0.85
  if eq { lab(-1.2, 0, black)[$=$] }
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (1.9, y)); wire((1.55, -y), (1.9, -y))
  gbox((1.9, y), [R]); gbox((1.9, -y), [S])
  wire((2.82, y), (3.4, y)); wire((2.82, -y), (3.4, -y))
  lab(-0.35, 0, black)[$C$]; lab(3.75, y, RW)[$A$]; lab(3.75, -y, ARC)[$B$]
})
#row((box(inset: (right: 18pt), cetz.canvas(length: 0.8cm, {
  let (C, A, B, P) = ((-3, 0), (0, 1.7), (0, -1.7), (3, 0))
  ar(C, A, RW); ar(C, B, ARC); ar(P, A, RW, s0: 0.75); ar(P, B, ARC, s0: 0.75)
  ar(C, P, PAL.at(0), dash: "dashed", s1: 0.95)
  lab(-1.75, 1.12, RW)[`R`]; lab(-1.75, -1.12, ARC)[`S`]
  lab(1.8, 1.12, RW)[`π₁`]; lab(1.8, -1.12, ARC)[`π₂`]
  lab(-1.0, 0.32, PAL.at(0))[$chevron.l R, S chevron.r$]
  lab(1.1, 0.5, PAL.at(1), rot: -135deg)[`⊑`]; lab(1.1, -0.5, PAL.at(1), rot: 135deg)[`⊑`]
  node(C.at(0), C.at(1), black, $C$)
  node(A.at(0), A.at(1), RW, $A$); node(B.at(0), B.at(1), ARC, $B$)
  node(P.at(0), P.at(1), PAL.at(0), $A times B$)
})), pairstr()))

A domain is coreflexive, so `⟨R,S⟩ π₁ ⊑ R`, with equality exactly when `S` is entire; for maps both
triangles commute and `⟨f,g⟩` is unique. In `Rel`, `c ⟨R,S⟩ (a,b)` iff `c R a` and `c S b` — copy `c`, then
`R` on one strand and `S` on the other, which is `◁ (R ⊗ S)` on the right.

No `°` survives the translation. `π₁ = 𝟙 ⊗ ⊸` discards the second component, so `π₁° = 𝟙 ⊗ ⟜`
*creates* one out of nothing, and `∩` is copy, run both, merge. Draw that and the created strands —
the two dots with no left end, and the crossing they force — are merged against real ones, which is
the monoid's unit law:

// The chain at FULL size: `chain`'s 62% is calibrated for the exported pictures, which are drawn on a
// bigger canvas than these two.
#chain((cetz.canvas(length: 0.8cm, {
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
  lab(-0.35, 0, black)[$C$]; lab(5.35, 0.85, RW)[$A$]; lab(5.35, -0.85, ARC)[$B$]
}), pairstr(eq: true)), ("", [`⟜ ▷ = 𝟙` on each half]), s: 100%)


== The relational product `R × S`

#definition[
`R × S ≜ ⟨π₁ R, π₂ S⟩`, a relator in each argument but no longer a categorical product.
]

// The same pair of pictures with `C` replaced by `C × D`, once per projection: the two triangles
// become two squares, and the copy dot goes away — `R × S` is the two strands side by side.
#row((box(inset: (right: 18pt), cetz.canvas(length: 0.8cm, {
  let (C, CD, D) = ((-2.7, 1.7), (-2.7, 0), (-2.7, -1.7))
  let (A, AB, B) = ((2.7, 1.7), (2.7, 0), (2.7, -1.7))
  ar(CD, C, RW, s0: 0.55); ar(CD, D, ARC, s0: 0.55)
  ar(AB, A, RW, s0: 0.55); ar(AB, B, ARC, s0: 0.55)
  ar(C, A, RW); ar(D, B, ARC)
  ar(CD, AB, PAL.at(0), dash: "dashed", s0: 0.95, s1: 0.95)
  lab(-3.1, 0.85, RW)[`π₁`]; lab(-3.1, -0.85, ARC)[`π₂`]
  lab(3.1, 0.85, RW)[`π₁`]; lab(3.1, -0.85, ARC)[`π₂`]
  lab(0, 2.0, RW)[`R`]; lab(0, -1.4, ARC)[`S`]
  lab(-1.2, 0.32, PAL.at(0))[$R times S$]
  lab(1.2, 0.85, PAL.at(1), rot: -135deg)[`⊑`]; lab(1.2, -0.85, PAL.at(1), rot: 135deg)[`⊑`]
  node(C.at(0), C.at(1), RW, $C$); node(D.at(0), D.at(1), ARC, $D$)
  node(CD.at(0), CD.at(1), PAL.at(0), $C times D$)
  node(A.at(0), A.at(1), RW, $A$); node(B.at(0), B.at(1), ARC, $B$)
  node(AB.at(0), AB.at(1), PAL.at(0), $A times B$)
})), cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, y), (0.5, y)); gbox((0.5, y), [R]); wire((1.42, y), (2.0, y))
  wire((0, -y), (0.5, -y)); gbox((0.5, -y), [S]); wire((1.42, -y), (2.0, -y))
  lab(-0.35, y, RW)[$C$]; lab(-0.35, -y, ARC)[$D$]
  lab(2.35, y, RW)[$A$]; lab(2.35, -y, ARC)[$B$]
})))

Right-then-up is `(R × S) π₁`, up-then-right is `π₁ R`, and `(R × S) π₁ ⊑ π₁ R`, equality when `S` is
entire. In `Rel`, `(c,d) (R × S) (a,b)` iff `c R a` and `d S b` — two strands side by side, no copy
dot: `R × S = R ⊗ S`.

== Absorption

For `X : E ⟶ C` and `Y : E ⟶ D`, `⟨X,Y⟩ (R × S) = ⟨X R, Y S⟩`. Both sides are this picture:

// ONE picture, not two with an `=`: pushing `R ⊗ S` past `X ⊗ Y` is the interchange law, which the
// notation has already spent — the two sides are drawn by the same strokes, so a second copy of the
// picture would say nothing.  This is the whole of B&dM's (5.3), whose direct proof needs two
// auxiliary special cases.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (1.9, y)); wire((1.55, -y), (1.9, -y))
  gbox((1.9, y), [X]); gbox((1.9, -y), [Y])
  wire((2.82, y), (3.2, y)); wire((2.82, -y), (3.2, -y))
  gbox((3.2, y), [R]); gbox((3.2, -y), [S])
  wire((4.12, y), (4.7, y)); wire((4.12, -y), (4.7, -y))
  lab(-0.35, 0, black)[$E$]; lab(5.05, y, RW)[$A$]; lab(5.05, -y, ARC)[$B$]
})))

== The coproduct `[R,S]`

The injections `ιₗ : A ⟶ A + B` and `ιᵣ : B ⟶ A + B` are maps, and the coproduct they make of the maps
stays a coproduct once every arrow is allowed: both equations hold with equality and `[R,S]` is the only
arrow satisfying them, with none of the `Dom` slack `⟨R,S⟩` carries.

#definition[
`[R,S] ≜ ιₗ° R ∪ ιᵣ° S`, and `R + S ≜ [R ιₗ, S ιᵣ]`.
]

// THE DEFINITION, DRAWN — and it needs no new generator.  `+` shares none of `◁ ▷ ⊸ ⟜`, but it does
// not have to: the definition is a UNION, and the union is already drawn, as the tape of the laws
// above.  So the one picture this subsection gets is the one line the other rows are calculated from;
// the rest stay formulas, which read as written.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
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
})))

The tape is the union — a particle entering at `A + B` takes exactly one branch — and the two mirrored
boxes are what makes the branches disjoint.

#align(center, table(
  columns: 1, inset: 9pt, stroke: 0.4pt + luma(190),

  [`ιₗ [R,S] = R`, `ιᵣ [R,S] = S`, and `[R,S]` is the only such arrow],
  [`ιₗ ιₗ° = 𝟙 = ιᵣ ιᵣ°`],
  [`ιₗ ιᵣ° = ⊥ = ιᵣ ιₗ°`],
  [`ιₗ° ιₗ ∪ ιᵣ° ιᵣ = 𝟙`],
  [`[U,V]° [R,S] = U° R ∪ V° S`],
))

// B&dM §5.3, pp. 117-118, mirrored into this note's diagram order: the derivation that a coproduct of
// MAPS is already a coproduct of every arrow, and the diagram the book prints beside it.  The
// paragraph opening this subsection asserts that; here is the argument, and it is why the first row
// holds with equality where the pairing's triangles above only hold up to `Dom`.
The first row is not free: `ιₗ, ιᵣ` were only ever asked to be a coproduct of *maps*. They stay one
once every arrow is allowed because `Λ` sends an arrow `A ⟶ C` to a map `A ⟶ [C]` reversibly, so the
map coproduct can be applied underneath it. For any `T : A + B ⟶ C`,

// B&dM's own layout for a calculation: the line, then the step's justification indented under a `⟺`,
// then the next line.  Stroke-less, so it reads as one argument and not as another law table.
#align(center, table(
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
))

// The lead-in and the figure in ONE unbreakable block: left to itself the sentence ends a page and
// the picture opens the next, so the reader turns the page between "drawn" and the drawing.
#block(breakable: false)[
Every step is an `⟺`, so `[Λ(R), Λ(S)] ∋` is the *only* arrow satisfying the two equations — which is
what `[R,S]` was claimed to be. Drawn:

// The book's figure, turned a quarter turn: source at the left, like every other picture here.  `A`
// fans out to the three points of the spine, so nothing crosses a node — except `R` and `S`, whose
// straight lines would run over `[C]`, so they arc outside instead.  Blue and dashed is the induced
// arrow, as in the squares below.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (AB, PC, C) = ((-6.4, 0), (0.4, 0), (4.6, 0))
  let (A, B) = ((-3.4, 2.4), (-3.4, -2.4))
  ar(A, AB, black, s0: 0.5, s1: 0.9)
  ar(B, AB, black, s0: 0.5, s1: 0.9)
  ar(AB, PC, PAL.at(0), dash: "dashed", s0: 0.9, s1: 0.6)
  ar(PC, C, black, s0: 0.6, s1: 0.5)
  ar(A, PC, RW, s0: 0.5, s1: 0.6)
  ar(B, PC, ARC, s0: 0.5, s1: 0.6)
  arc(A, C, 1, [`R`], col: RW, h: 4.0, cx: 3)
  arc(B, C, -1, [`S`], col: ARC, h: 4.0, cx: 3)
  lab(-5.18, 1.55, black)[`ιₗ`]; lab(-5.18, -1.55, black)[`ιᵣ`]
  lab(-1.23, 1.62, RW)[`Λ(R)`]; lab(-1.23, -1.62, ARC)[`Λ(S)`]
  lab(-3.0, 0.5, PAL.at(0))[`[Λ(R), Λ(S)]`]
  lab(2.5, 0.45, black)[`∋`]
  node(A.at(0), A.at(1), RW, $A$); node(B.at(0), B.at(1), ARC, $B$)
  node(AB.at(0), AB.at(1), black, $A + B$)
  node(PC.at(0), PC.at(1), PAL.at(0), $[C]$)
  node(C.at(0), C.at(1), black, $C$)
})))
]

Nothing here holds only up to `⊑`: every triangle commutes on the nose, which is the difference from
the pairing above. The border spells `[R,S] = [Λ(R), Λ(S)] ∋`, and pushing `∋` into the union that
`[·,·]` on maps already is turns that back into the definition,
`(ιₗ° Λ(R) ∪ ιᵣ° Λ(S)) ∋ = ιₗ° R ∪ ιᵣ° S`.

// B&dM §5.4, p. 119.  The heading gets its own page: the definition, the paragraph that explains its
// shape, and the table are one argument, and the coproduct figure above ends a page mid-way.
#pagebreak(weak: true)
== The power relator `P R`

#definition[
For `R : A ⟶ B`, #h(4pt) `P R ≜ ((∋ R)/∋) ∩ ((∋ R°)/∋)° : [A] ⟶ [B]`.
]

`∋ R` is a *composition* — `∋ : [A] ⟶ A` followed by `R` — and not Freyd's subscripted $#e[R]$,
which is the `∋` at `R`'s *target*: §11 writes one `∋` per object and drops the subscript. Piece by
piece, on one instance, with `x, y` lists and `a, b` their elements.

// §10's picture — a column per type, every arrow pointing at the dot it names — drawn THREE times on
// ONE instance, a row of the table above per picture.  The `∋` fans point INWARD at the element
// columns and `R` runs between them, so no fan ever shares a horizontal band with `R`.  The lists
// keep their coordinates across the three, so the reader compares them by looking at the same place
// twice; and the two lists `P R` accepts are the top and the bottom one, which is what lets both of
// its arcs sweep clear of every other node.
#let LX = (-8.6, 0)
#let AD = (a1: (-4.6, 1.6), a2: (-4.6, -1.6))
#let BD = (b1: (0.6, 2.2), b2: (0.6, 0), b3: (0.6, -2.2))
#let LY = (y1: (5.6, 3.3), y2: (5.6, 1.1), y3: (5.6, -1.1), y4: (5.6, -3.3))

// `x`, its `∋` fan, `R`, and the elements — everything all three pictures share.  `body` is drawn
// between the shared part and `x`'s own box, so an arc drawn there has its tail tucked under that
// box and its head under the list box it lands on, the way §10 hides an arc's ends.
#let skel(body) = {
  for a in (AD.a1, AD.a2) { syqedge(LX, a, PAL.at(0), 1.1) }
  ar(AD.a1, BD.b1, RW, s0: 0.3, s1: 0.3); ar(AD.a1, BD.b3, RW, s0: 0.3, s1: 0.3)
  ar(AD.a2, BD.b3, RW, s0: 0.3, s1: 0.3)
  for p in (AD.a1, AD.a2) { d.circle(p, radius: 0.17, fill: black, stroke: black) }
  // Filled = reached from `x`, hollow = not.  That colouring IS `∋ R`, and the next two pictures do
  // nothing but read lists off these three dots.
  for p in (BD.b1, BD.b3) { d.circle(p, radius: 0.17, fill: ARC, stroke: ARC) }
  d.circle(BD.b2, radius: 0.17, fill: white, stroke: 0.9pt + black)
  lab(-4.6, 2.35, black)[`a₁`]; lab(-4.6, -2.35, black)[`a₂`]
  // `b₁`'s label goes to its RIGHT: above the dot it lands on the head of the first picture's arc.
  lab(1.5, 2.7, black)[`b₁`]; lab(0.6, 0.75, black)[`b₂`]; lab(0.6, -1.45, black)[`b₃`]
  lab(-6.6, 0, PAL.at(0))[`∋`]; lab(-2.0, 2.6, RW)[`R`]
  body
  syqnode(LX, ARC, rgb("#f2e9f8"), `x = {a₁,a₂}`, ring: 0.7pt + ARC)
}
// A list over `B`: its `∋` fan and its box, washed out when the picture rejects it.
#let ylist(p, es, w, on: true) = {
  let (col, wt) = if on { (PAL.at(1), 1.1) } else { (PAL.at(1).lighten(60%), 0.7) }
  for b in es { syqedge(p, b, col, wt) }
  if on { syqnode(p, ARC, rgb("#f2e9f8"), w, ring: 0.7pt + ARC) } else { syqnode(p, black, white, w) }
}

`x = {a₁,a₂}`, and `R` sends `a₁` to `b₁` and `b₃`, `a₂` to `b₃` alone. Nothing on `x` reaches `b₂`,
so `b₂` is drawn hollow.

#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, BD.b1, 1, [`∋ R`], h: 4.2, cx: 5)
  arc(LX, BD.b3, -1, [`∋ R`], h: 4.2, cx: 5)
}))))
// The arrow and its `Rel` reading go UNDER the picture that draws them, one pair per picture: read
// against the drawing they were just given, where a table of all three read against nothing.
#align(center, block(inset: (y: 6pt))[
  `∋ R : [A] ⟶ B` #h(1.4cm) `x (∋ R) b ⟺ ∃a ∈ x. a R b`
])
#align(center, src[one arc per element of `B` that `x` reaches, and `b₂` gets none])

Dividing by `∋` turns that into a relation between *lists*: every element of `y` must be one of the
filled dots.

#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, LY.y1, 1, [`(∋ R)/∋`], h: 5.6, cx: 6)
  lab(3.2, 3.4, PAL.at(1))[`∋`]
  ylist(LY.y1, (BD.b1, BD.b3), `y₁ = {b₁,b₃}`)
  ylist(LY.y3, (BD.b2, BD.b3), `y₃ = {b₂,b₃}`, on: false)
}))))
#align(center, block(inset: (y: 6pt))[
  `(∋ R)/∋ : [A] ⟶ [B]` #h(1.4cm) `x ((∋ R)/∋) y ⟺ ∀b ∈ y. ∃a ∈ x. a R b`
])
#align(center, src[`y₃` is rejected: it names `b₂`, which `x` does not reach])

// Lead-in, picture and readings in ONE unbreakable block: left to itself the sentence ends page 17
// and the picture opens page 18, so the reader turns the page between "them" and them.
#block(breakable: false)[
The other half of the meet is that clause with the lists swapped and `R` turned round: every element
of `x` must reach `y`. Both together, and two more lists to separate them:

#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, skel({
  arc(LX, LY.y1, 1, [`P R`], h: 5.6, cx: 6)
  arc(LX, LY.y4, -1, [`P R`], h: 5.6, cx: 6)
  lab(3.2, 3.4, PAL.at(1))[`∋`]
  ylist(LY.y1, (BD.b1, BD.b3), `y₁ = {b₁,b₃}`)
  ylist(LY.y2, (BD.b1,), `y₂ = {b₁}`, on: false)
  ylist(LY.y3, (BD.b2, BD.b3), `y₃ = {b₂,b₃}`, on: false)
  ylist(LY.y4, (BD.b3,), `y₄ = {b₃}`)
}))))
#align(center, block(inset: (y: 6pt))[
  `((∋ R°)/∋)° : [A] ⟶ [B]` #h(1.4cm) `x ((∋ R°)/∋)° y ⟺ ∀a ∈ x. ∃b ∈ y. a R b`
])
#align(center, src[`y₂` is rejected too: `a₂`'s only image is `b₃`, which `y₂` does not name])
]

In words, if `x (P R) y` then every element of `x` is related by `R` to some element of `y`, and
conversely — the two clauses of `∩`, one per direction.

Neither `∋` nor `P R` is a map. `∋` sends a list to *each* of its elements; `P R` sends `x` to
*every* `y` meeting the two clauses, `y₁` and `y₄` both. Nor is it entire: an `a ∈ x` with no image
at all leaves `x` with no partner whatever. Turning a relation into a map is `Λ`'s job (§11), and on
lists that map is `Λ(∋ R)` — of the four it accepts `y₁` only.

// The question this subsection exists to answer: the definition IS two divisions and a converse, the
// shape of a symmetric division, and the reader who has just read §10 will try to fold it into one.
*Not* a symmetric division. $frac(∋ R, ∋)$ is `Λ(∋ R)`, and in `Rel` it reads
`x Λ(∋ R) y ⟺ y = {b | ∃a ∈ x. a R b}`: in words, `y` is *exactly* what `x` reaches, where `P R`
asks only that each side cover the other. Nor can it be repaired: in that fraction's second half
$(∋ slash (∋ R))^circle.small$ the `R` sits in a denominator, so the operation is antitone there, and
a relator has to be monotone. `P R` keeps the first half and takes the second half at `R°`, which
puts `R` back in a numerator. The fraction returns exactly where the two halves agree — at `𝟙`, and
at a map.

#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [`X ⊑ P R ⟺ X ∋ ⊑ ∋ R` and `X° ∋ ⊑ ∋ R°`],
  [One containment, and the same one at `R°` — which is the definition read off the two divisions.
   Hence `P(R°) = (P R)°`, and `R ⊑ S ⟹ P R ⊑ P S`.],

  [`P 𝟙 =` $frac(∋, ∋)$ `= 𝟙`],
  [The straightness axiom verbatim: extensionality *is* `P`'s unit law.],

  [`P f = Λ(∋ f)` `=` $frac(∋ f, ∋)$, for `f` a map],
  [In `Rel`, `x (P f) y ⟺ y = {f a | a ∈ x}`. The half at `f°` says every `a ∈ x` has its `f a` on
   `y`; `f` has just the one image per `a`, so that already says `y` contains everything `x`
   reaches, which is the fraction's second half. For a map the two definitions coincide.],

  [`P(R S) = (P R)(P S)`],
  [`⊒` is the division cancellation laws. `⊑` is the one law in this section that is not a
   calculation: it needs a tabulation of `P(R S)`.],
)

// Its own page: the heading otherwise lands as the last line under §12's table, an orphan a page away
// from the definition it names, and the two squares below then straddle the break.
#pagebreak(weak: true)
= Catamorphism

#definition[
`F` a relator with an *initial algebra* `α : F T ⟶ T` among the maps. For a relational algebra
`R : F B ⟶ B`, the *catamorphism* `⦇R⦈ : T ⟶ B` is the unique arrow with `α ⦇R⦈ = (F ⦇R⦈) R`.
]

// A COMMUTATIVE SQUARE, hand-drawn like §12's: same `ar`/`lab`/`node`, same palette, the induced arrow
// dashed and blue.  Left to right with the source on the left, so this picture flows the way every
// string diagram above does.  The given data are the two solid arrows `α` and `R`; everything blue is
// what the initial algebra produces.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (FT, FB, T, B) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
  ar(FT, FB, PAL.at(0), dash: "dashed", s0: 0.75, s1: 0.75)
  ar(T, B, PAL.at(0), dash: "dashed", s0: 0.55, s1: 0.55)
  ar(FT, T, ARC, s0: 0.55, s1: 0.55); ar(FB, B, RW, s0: 0.55, s1: 0.55)
  lab(0, 1.8, PAL.at(0))[`F X`]; lab(0, -1.8, PAL.at(0))[`X`]
  lab(-3.6, 0, ARC)[`α`]; lab(3.55, 0, RW)[`R`]
  node(FT.at(0), FT.at(1), black, `F T`); node(FB.at(0), FB.at(1), RW, `F B`)
  node(T.at(0), T.at(1), black, `T`); node(B.at(0), B.at(1), RW, `B`)
})))

With `X = ⦇R⦈` the square commutes strictly: unlike the product's triangles, there is no slack
here, so no `⊑` appears anywhere in it.

// `T` is already the initial algebra's carrier, so the second algebra's carrier is `C`, never `T`.
The three *fusion* rows rewrite `⦇R⦈ S` through a second algebra `Q : F C ⟶ C` along an arrow
`S : B ⟶ C`. They are the only rows here that need the allegory *locally complete* — every hom-set a
complete lattice — because they come from a least-fixed-point argument; the rest of the table needs
only the initial algebra.

// The law column is 7.4cm, the width the law tables use, so the widest row —
// `⦇Q⦈ ⊑ ⦇R⦈ S ⟸ (F S) Q ⊑ R S` — stays on one line; the name column is wide enough for
// `Eilenberg–Wright` unbroken, since a hyphenated name split across lines reads as two names.
#align(center, table(
  columns: (4.2cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*law*], [*what it says*]),

  [the defining equation],
  [`X = ⦇R⦈ ⟺ α X = (F X) R`],
  [Folding a value that `α` has just built is the same as folding its parts and combining them with
   `R`. Nothing else has that property.],

  [Lambek],
  [`α° = α⁻¹`, the initial algebra is an isomorphism],
  [A constructor can be undone — `α°` takes a value apart into the parts it was built from.],

  [Eilenberg–Wright],
  [`Λ⦇R⦈ = ⦇Λ((F ∋) R)⦈`],
  [A relational fold is a deterministic fold of SETS: `Λ` pushes the nondeterminism into the
   power-object, where the fold is a map again.],

  [Eilenberg–Wright],
  [`⦇R⦈ = ⦇Λ((F ∋) R)⦈ ∋`],
  [The same fact read back — fold deterministically into a set, then take a member of it.],

  [fusion],
  [`⦇Q⦈ ⊑ ⦇R⦈ S ⟸ (F S) Q ⊑ R S`],
  [Half of fusion: an inclusion between the two algebras is inherited by the folds.],

  [fusion],
  [`⦇R⦈ S ⊑ ⦇Q⦈ ⟸ R S ⊑ (F S) Q`],
  [The other half, with both inclusions turned around.],

  [fusion],
  [`⦇R⦈ S = ⦇Q⦈ ⟸ R S = (F S) Q`],
  [Both halves at once: a fold followed by `S` collapses into a single fold, which is how an
   intermediate structure is got rid of.],
))

// The name column already says which two rows these are, so the sentence only points at them.
The two `Λ` rows, drawn:

// TWO SQUARES, sharing the middle column.  `⦇Λ((F ∋) R)⦈` is three times the width of a node box, so
// inside the picture it is the single letter `K` and the sentence below says what `K` is; the table
// keeps the term in full.  The middle arrow stays spelled out — it is the algebra whose catamorphism
// `K` is, and abbreviating it too would leave the left square with nothing to be the square OF.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (FT, FP, FB) = ((-6, 1.25), (0, 1.25), (6, 1.25))
  let (T, P, B) = ((-6, -1.25), (0, -1.25), (6, -1.25))
  ar(FT, FP, PAL.at(0), dash: "dashed", s0: 0.75, s1: 0.95)
  ar(FP, FB, black, s0: 0.95, s1: 0.75)
  ar(T, P, PAL.at(0), dash: "dashed", s0: 0.55, s1: 0.7)
  ar(P, B, black, s0: 0.7, s1: 0.55)
  ar(FT, T, ARC, s0: 0.55, s1: 0.55); ar(FP, P, black, s0: 0.55, s1: 0.55)
  ar(FB, B, RW, s0: 0.55, s1: 0.55)
  lab(-3, 1.8, PAL.at(0))[`F K`]; lab(3, 1.8, black)[`F ∋`]
  lab(-3, -1.8, PAL.at(0))[`K`]; lab(3, -1.8, black)[`∋`]
  lab(-6.6, 0, ARC)[`α`]; lab(6.55, 0, RW)[`R`]; lab(2.05, 0, black)[`Λ((F ∋) R)`]
  node(FT.at(0), FT.at(1), black, `F T`); node(T.at(0), T.at(1), black, `T`)
  node(FP.at(0), FP.at(1), PAL.at(0), `F [B]`); node(P.at(0), P.at(1), PAL.at(0), `[B]`)
  node(FB.at(0), FB.at(1), RW, `F B`); node(B.at(0), B.at(1), RW, `B`)
})))

The left square is that catamorphism's own defining square, `K = ⦇Λ((F ∋) R)⦈`, and the right one is
`Λ`'s cancellation, so the outer rectangle says `K ∋` satisfies the defining equation of `⦇R⦈` — and
uniqueness finishes it.

// Its own page: the definition below only says what `T R` is, and the square after it is the reason
// that arrow exists, so the two have to be read together — under the picture above they would not be.
#pagebreak(weak: true)
= Type functor

#definition[
`F` a *binary* relator: `F(R, S)` is its action on a pair, and `F X` abbreviates `F(𝟙, X)`, the `F` of
the catamorphism section. For every object `A` the initial algebra is `α : F(A, T A) ⟶ T A`, among the
maps. The *type functor* `T` acts on an arrow `R : A ⟶ B` by

  #align(center, block(inset: (y: 6pt))[`T R = ⦇F(R, 𝟙) α⦈ : T A ⟶ T B`])
]

`F` is the *base functor* — one layer of the structure, acting on the recursive position — while `T` is
the datatype itself, acting on the parameter. For cons-lists, `list R = ⦇[nil, (R ⊗ 𝟙) cons]⦈`, which
is `map R`.

// THE DEFINING SQUARE: the catamorphism square with `T R`'s algebra spelled out as the composite it
// is, `F(R, 𝟙) α`, which is why the top row has three nodes and the bottom two.  The middle node is
// where the recursive positions have already been mapped and the parameters have not.
// x = ±5, not the ±3 of the square above: `F(A, T A)` is three times the width of `F T`, and at ±3
// the boxes would meet.  `s0`/`s1` are how far to stay clear of a node — 1.45 leaves a box that wide
// sideways, 0.65 leaves `T A`, 0.55 enters one from above or below.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (FA, FM, FB) = ((-5, 1.25), (0, 1.25), (5, 1.25))
  let (TA, TB) = ((-5, -1.25), (5, -1.25))
  ar(FA, FM, PAL.at(0), dash: "dashed", s0: 1.45, s1: 1.45)
  ar(FM, FB, black, s0: 1.45, s1: 1.45)
  ar(TA, TB, PAL.at(0), dash: "dashed", s0: 0.65, s1: 0.65)
  ar(FA, TA, ARC, s0: 0.55, s1: 0.55); ar(FB, TB, RW, s0: 0.55, s1: 0.55)
  lab(-2.5, 1.85, PAL.at(0))[`F(𝟙, T R)`]; lab(2.5, 1.85, black)[`F(R, 𝟙)`]
  lab(0, -1.85, PAL.at(0))[`T R`]
  lab(-5.6, 0, ARC)[`α`]; lab(5.55, 0, RW)[`α`]
  node(FA.at(0), FA.at(1), black, `F(A, T A)`); node(TA.at(0), TA.at(1), black, `T A`)
  node(FM.at(0), FM.at(1), PAL.at(0), `F(A, T B)`)
  node(FB.at(0), FB.at(1), RW, `F(B, T B)`); node(TB.at(0), TB.at(1), RW, `T B`)
})))

`T R` is the unique arrow making it commute; there is no `⊑` in it.

// Same widths and stroke as the catamorphism table: the two tables are read one after the other, and
// a law column that changes width between them reads as a different kind of column.
#align(center, table(
  columns: (4.2cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*law*], [*what it says*]),

  [the defining equation],
  [`T R = ⦇F(R, 𝟙) α⦈`],
  [Rebuild the structure with `α`, applying `R` to the parameter on the way; that is `map R`.],

  [functor],
  [`T 𝟙 = 𝟙` and `(T R)(T S) = T (R S)`],
  [Mapping the identity changes nothing, and two maps in a row are one map.],

  [type functor fusion],
  [`(T R) ⦇Q⦈ = ⦇F(R, 𝟙) Q⦈`],
  [A map followed by a fold is a single fold — the mapped structure is never built.],

  [naturality of `α`],
  [`α (T R) = F(R, T R) α`],
  [Building and then mapping is the same as mapping the parts and then building, so `α` is natural
   from `G R = F(R, T R)` to `T`.],

  [type relator],
  [`(T R)° = T (R°)`],
  [A datatype acts on relations, not only on maps — the map of the converse is the converse of the
   map.],
))

Type functor fusion is the equality fusion row above applied to `T R`'s own defining algebra, whose
side condition holds because `F` is a bifunctor — `F(R, 𝟙) F(𝟙, ⦇Q⦈) = F(R, ⦇Q⦈) = F(𝟙, ⦇Q⦈) F(R, 𝟙)`
— so it inherits that row's local-completeness requirement.

// THE NATURALITY ROW, drawn: the square above with its two top arrows composed into the one relator
// action `F(R, T R)`, which is why this one is back to the ±3 of the catamorphism square.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let (FA, FB, TA, TB) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
  ar(FA, FB, PAL.at(0), s0: 1.45, s1: 1.45)
  ar(TA, TB, PAL.at(0), s0: 0.65, s1: 0.65)
  ar(FA, TA, ARC, s0: 0.55, s1: 0.55); ar(FB, TB, RW, s0: 0.55, s1: 0.55)
  lab(0, 1.85, PAL.at(0))[`F(R, T R)`]; lab(0, -1.85, PAL.at(0))[`T R`]
  lab(-3.6, 0, ARC)[`α`]; lab(3.55, 0, RW)[`α`]
  node(FA.at(0), FA.at(1), black, `F(A, T A)`); node(TA.at(0), TA.at(1), black, `T A`)
  node(FB.at(0), FB.at(1), RW, `F(B, T B)`); node(TB.at(0), TB.at(1), RW, `T B`)
})))

It commutes strictly: it is the naturality square of `α`.
