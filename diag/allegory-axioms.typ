// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name.  See the header of strdiag.typ.
#import "strdiag.typ": cetz, d, conv, meet, wire

// EVERY PICTURE OF A THEOREM BELOW IS EXPORTED, NOT DRAWN.  `./scripts/diag-export <decl>` walks the
// Lean declaration's TYPE and writes diag/generated/<decl>.typ, which binds the cetz drawing to
// `pic`; this note only places those bindings in table cells.  Hand-drawing them is how the first
// draft of this page got `inter_assoc` wrong — it showed coassociativity of `Δ` instead of the axiom
// — and dropped the `=` from `recip_inter`.  A picture derived from the statement cannot drift from
// it.  Regenerate every binding used here with:
//
//   ./scripts/diag-export Freyd.Diag.CartBicat.Δ_assoc Freyd.Diag.CartBicat.Δ_comm \
//     Freyd.Diag.CartBicat.Δ_counit Freyd.Diag.CartBicat.«∇_assoc» Freyd.Diag.CartBicat.«∇_comm» \
//     Freyd.Diag.CartBicat.«∇_unit» \
//     Freyd.Diag.CartBicat.conv_conv Freyd.Diag.CartBicat.conv_comp \
//     Freyd.Diag.conv_inter Freyd.Diag.meet_idem Freyd.Diag.meet_comm Freyd.Diag.meet_assoc \
//     Freyd.Diag.semidistrib_of_lax Freyd.Diag.modular_of_frobenius Freyd.Diag.«≤_top» \
//     Freyd.Diag.CartBicat.special Freyd.Diag.CartBicat.«∇Δ≤𝟙» Freyd.Diag.CartBicat.«𝟙≤Δ∇» \
//     Freyd.Diag.CartBicat.«?!≤𝟙» Freyd.Diag.CartBicat.«𝟙≤!?» Freyd.Diag.CartBicat.frob_left \
//     Freyd.Diag.CartBicat.lax_Δ Freyd.Diag.CartBicat.lax_! Freyd.Diag.Biprod.«≤_union_left» \
//     Freyd.Diag.Biprod.union_comm Freyd.Diag.Biprod.bot_union Freyd.Diag.Biprod.comp_union \
//     Freyd.Diag.Biprod.conv_union Freyd.Diag.FbCbRig.meet_union_distrib \
//     Freyd.Diag.ClosedLinearBicat.«residual_comp_≤» Freyd.Diag.SingleValued Freyd.Diag.Total \
//     Freyd.Diag.Injective Freyd.Diag.Surjective Freyd.Diag.ineq_SV Freyd.Diag.ineq_TOT \
//     Freyd.Diag.ineq_INJ Freyd.Diag.ineq_SUR Freyd.Diag.shunt_right Freyd.Diag.shunt_left \
//     Freyd.Diag.entire_inter_iff Freyd.Diag.CartBicat.«∇_slide_conv»
// and, for the last section, the ALLEGORY layer's division:
//   ./scripts/diag-export Freyd.Alg.le_div_iff Freyd.Alg.le_leftDiv_iff \
//     Freyd.Alg.DivisionAllegory.div_comp_le Freyd.Alg.leftDiv_comp_le Freyd.Alg.div_comp_assoc \
//     Freyd.Alg.leftDiv_comp Freyd.Alg.map_comp_div Freyd.Alg.div_comp_recip_map \
//     Freyd.Alg.symmDiv_recip Freyd.Alg.symmDiv_comp
// and the PROOF chains:
//   ./scripts/diag-export Freyd.Diag.CartBicat.«°_slide»
//   ./scripts/diag-export --proof Freyd.Diag.CartBicat.conv_comp Freyd.Diag.shunt_right \
//     Freyd.Diag.shunt_left Freyd.Diag.CartBicat.«∇_slide_conv» \
//     Freyd.Diag.modular_of_frobenius Freyd.Diag.entire_inter_iff
#import "generated/Freyd.Diag.CartBicat.conv_conv.typ": pic as p-conv-conv
#import "generated/Freyd.Diag.CartBicat.conv_comp.typ": pic as p-conv-comp
#import "generated/Freyd.Diag.conv_inter.typ": pic as p-conv-inter
#import "generated/Freyd.Diag.meet_idem.typ": pic as p-meet-idem
#import "generated/Freyd.Diag.meet_comm.typ": pic as p-meet-comm
#import "generated/Freyd.Diag.meet_assoc.typ": pic as p-meet-assoc
#import "generated/Freyd.Diag.semidistrib_of_lax.typ": pic as p-semidistrib
#import "generated/Freyd.Diag.modular_of_frobenius.typ": pic as p-modular
#import "generated/Freyd.Diag.«≤_top».typ": pic as p-le-top
#import "generated/Freyd.Diag.CartBicat.special.typ": pic as p-special
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
#import "generated/Freyd.Diag.CartBicat.frob_left.typ": pic as p-frob
#import "generated/Freyd.Diag.CartBicat.frob_right.typ": pic as p-frob-r
#import "generated/Freyd.Diag.CartBicat.frob.proof.typ": branches as frobb
#import "generated/Freyd.Diag.CartBicat.snakes.proof.typ": branches as snakeb
#import "generated/Freyd.Diag.CartBicat.snake.typ": pic as p-snake
#import "generated/Freyd.Diag.CartBicat.snake'.typ": pic as p-snake-r
#import "generated/Freyd.Diag.CartBicat.lax_Δ.typ": pic as p-lax-delta
#import "generated/Freyd.Diag.CartBicat.lax_!.typ": pic as p-lax-bang
#import "generated/Freyd.Diag.Biprod.«≤_union_left».typ": pic as p-union-left
#import "generated/Freyd.Diag.Biprod.union_comm.typ": pic as p-union-comm
#import "generated/Freyd.Diag.Biprod.bot_union.typ": pic as p-bot-union
#import "generated/Freyd.Diag.Biprod.comp_union.typ": pic as p-comp-union
#import "generated/Freyd.Diag.Biprod.conv_union.typ": pic as p-conv-union
#import "generated/Freyd.Diag.FbCbRig.meet_union_distrib.typ": pic as p-distrib
#import "generated/Freyd.Diag.ClosedLinearBicat.«residual_comp_≤».typ": pic as p-residual
#import "generated/Freyd.Diag.CartBicat.conv_comp.proof.typ": branches as l42b
#import "generated/Freyd.Diag.shunt_right.proof.typ": branches as srb
#import "generated/Freyd.Diag.shunt_left.proof.typ": branches as slb
#import "generated/Freyd.Diag.CartBicat.«∇_slide_conv».proof.typ": branches as nsb
#import "generated/Freyd.Diag.modular_of_frobenius.proof.typ": branches as mfb
#import "generated/Freyd.Diag.CartBicat.«°_slide».typ": pic as p-conv-slide
#import "generated/Freyd.Diag.CartBicat.«∇_slide_conv».typ": pic as p-nabla-slide
#import "generated/Freyd.Diag.SingleValued.typ": pic as p-sv46
#import "generated/Freyd.Diag.Total.typ": pic as p-tot47
#import "generated/Freyd.Diag.Injective.typ": pic as p-inj48
#import "generated/Freyd.Diag.Surjective.typ": pic as p-sur49
#import "generated/Freyd.Diag.ineq_SV.typ": pic as p-sv
#import "generated/Freyd.Diag.ineq_TOT.typ": pic as p-tot
#import "generated/Freyd.Diag.ineq_INJ.typ": pic as p-inj
#import "generated/Freyd.Diag.ineq_SUR.typ": pic as p-sur
#import "generated/Freyd.Diag.shunt_right.typ": lhs as sr-a, rhs as sr-b
#import "generated/Freyd.Diag.shunt_left.typ": lhs as sl-a, rhs as sl-b
#import "generated/Freyd.Diag.entire_inter_iff.typ": pic as p-entire, lhs as ent-a, rhs as ent-b
#import "generated/Freyd.Diag.entire_inter_iff.proof.typ": branches as entb
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
#import "generated/Freyd.Alg.symmDiv_recip.typ": pic as p-sdiv-recip
#import "generated/Freyd.Alg.symmDiv_comp.typ": pic as p-sdiv-comp

#set page(width: 25cm, height: auto, margin: 1.5cm)
#set text(size: 11.5pt)
#set par(justify: true)
#show raw: set text(size: 9.6pt)
#show heading: set block(above: 16pt, below: 9pt)
#set heading(numbering: "1.")
// Justification inside a table cell stretches the spaces around long unbreakable monospace runs
// (`Freyd.Diag.ClosedLinearBicat.«residual_comp_≤»`) into gaps you can drive a car through.
#show table: set par(justify: false)
// The four generators are relation-operator glyphs, cut to sit inline beside `→` and `⊢`, so at
// running-text size their rings and triangles are too fine to tell apart.  They are read here as
// pictures, not as operators, so scale them back up to the surrounding cap height.
#show regex("[◁▷⊸⟜]"): it => text(size: 1.45em, it)

#let src(s) = text(9.2pt, luma(105))[#s]
/// An exported picture, shrunk to fit a table cell.  `reflow` so the cell measures the shrunk size.
#let P(p, s: 92%) = align(center, box(inset: (y: 5pt), scale(x: s, y: s, reflow: true, p)))
/// A picture set INLINE in a table header, naming the statement the chain proves.  Deliberately
/// large: the header is the one row every reader looks at first, and at running-text size the
/// theorem it states cannot be read at all.
#let Pin(p, s: 70%) = box(baseline: 36%, scale(x: s, y: s, reflow: true, p))
/// A chain table's top header row: the theorem, one size up from the body.
#let Th(body) = table.cell(colspan: 3, text(12.5pt)[#body])
/// A figure transcribed from the paper by hand — used only where there is no Lean STATEMENT to
/// export, i.e. for the two primitive operations.
#let fig(body) = align(center, box(inset: (y: 5pt), cetz.canvas(length: 0.78cm, body)))
/// `P`, but not centred.  In the one-column division table the exported picture sits BESIDE the
/// long-division figure, and two centred blocks leave a gutter down the middle of the page.
#let Pl(p, s: 90%) = box(inset: (y: 5pt), scale(x: s, y: s, reflow: true, p))

// ------------------------------------------------------------------ the long-division figure
#let AMBER = rgb("#f6e3bd")
#let GREEN = rgb("#cfe6cd")
/// The long-division bar: `R` as a bar, the composite laid inside it left to right, and a hairline
/// of slack at the far end.
///
/// `tiles` are `(label, kind)` in DIAGRAM order.  `"q"` is the quotient — amber, full height, solid
/// outline, because `T S ⊑ R` is what pins it.  `"d"` is a divisor laid down inside `R`: green,
/// inset top and bottom so it reads as embedded, dashed because its far edge is not pinned either.
/// The slack closes the bar and is deliberately a sliver: `R / S` is the LARGEST quotient, so what
/// is left when nothing more can be taken is exactly a hairline.
///
/// Transcribed, every one of them — this is a metaphor for the universal property, not a picture of
/// a term, and it is the one account of `/` in this note that needs no complement.
#let divbar(..tiles, qw: 3.0, dw: 1.9, slack: 0.12, note: none) = {
  let y0 = -0.55
  let y1 = 0.55
  let ys = 0.36
  let sol = (thickness: 1.1pt, paint: black)
  let dsh = (thickness: 1.1pt, paint: black, dash: "dashed")
  let ts = tiles.pos()
  let ws = ts.map(t => if t.at(1) == "q" { qw } else { dw })
  let total = ws.sum() + slack
  box(inset: (y: 5pt), cetz.canvas(length: 0.78cm, {
    d.rect((0, y0), (total, y1), fill: AMBER, stroke: none)
    // `R`'s own outline: far edge not pinned; top and bottom are drawn tile by tile below.  The
    // LEFT edge comes last, after the tiles, or a divisor laid first — left division — covers it
    // with its own dashed edge and `R`'s one pinned boundary reads as slack.
    d.line((total, y0), (total, y1), stroke: dsh)
    let x = 0.0
    for t in ts {
      let w = if t.at(1) == "q" { qw } else { dw }
      let st = if t.at(1) == "q" { sol } else { dsh }
      d.line((x, y1), (x + w, y1), stroke: st)
      d.line((x, y0), (x + w, y0), stroke: st)
      if t.at(1) == "q" {
        d.line((x, y0), (x, y1), stroke: sol)
        d.line((x + w, y0), (x + w, y1), stroke: sol)
      } else {
        d.rect((x, -ys), (x + w, ys), fill: GREEN, stroke: none)
        d.line((x, ys), (x + w, ys), stroke: dsh)
        d.line((x, -ys), (x + w, -ys), stroke: dsh)
        d.line((x, -ys), (x, ys), stroke: dsh)
        d.line((x + w, -ys), (x + w, ys), stroke: dsh)
      }
      d.content((x + w / 2, 0), text(10.5pt)[#t.at(0)])
      x = x + w
    }
    d.line((total - slack, y1), (total, y1), stroke: dsh)
    d.line((total - slack, y0), (total, y0), stroke: dsh)
    d.line((0, y0), (0, y1), stroke: sol)
    if note != none {
      d.line((total, y0 - 0.42), (total, y0 - 0.1), stroke: (thickness: 0.6pt, paint: luma(110)))
      d.content((total, y0 - 0.62), text(8.5pt, luma(90))[#note])
    }
  }))
}

/// Pictures laid side by side in one row.  Every exported canvas is drawn symmetrically about its
/// own `y = 0`, so aligning the cells on the horizon puts the wires of all of them at one height;
/// a per-box `baseline:` shift cannot, because each box is shifted by a fraction of its OWN height.
#let row(items, s: 100%) = align(center, box(inset: (y: 4pt), grid(
  columns: items.len(), align: horizon, column-gutter: 3pt,
  ..items.map(t => scale(x: s, y: s, reflow: true, t)))))

#align(center)[#text(16pt)[*The allegory axioms, and what defines them in the Frobenius calculus*]]

#v(4pt)

= Cartesian bicategory of relations

#align(center, block(inset: (y: 6pt))[
  #text(12.5pt)[`(◁, ⊸) ⊣ (▷, ⟜)`, commutative, *Frobenius*, arrows *lax*.]
])

#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + horizon,
  P(p-d-assoc, s: 60%), P(p-d-comm, s: 60%), P(p-d-counit, s: 60%),
)

#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + horizon,
  P(p-n-assoc, s: 60%), P(p-n-comm, s: 60%), P(p-n-unit, s: 60%),
)

== `◁ ⊣ ▷` and `⊸ ⊣ ⟜`

#grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-37, s: 52%) #v(-7pt) \ #src[`▷ ◁ ≤ 𝟙`]],
  [#P(p-38, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ◁ ▷`]],
  [#P(p-39, s: 52%) #v(-7pt) \ #src[`⟜ ⊸ ≤ 𝟙`]],
  [#P(p-40, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ⊸ ⟜`]],
)

== The Frobenius law

#row(frobb.at(0).steps, s: 54%)

The only clause coupling the comonoid to the monoid beyond adjointness. Both sides reduce to the
same picture, the bubble `▷ ◁`.

== Every arrow a lax comonoid homomorphism

#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-lax-delta, s: 60%) #v(-7pt) \ #src[`R ◁ ≤ ◁ (R ⊗ R)`]],
  [#P(p-lax-bang, s: 60%) #v(-7pt) \ #src[`R ⊸ ≤ ⊸`]],
)

= Compact closed, and where the converse comes from

The cup `⟜ ◁` and the cap `▷ ⊸` come with the definition — create then copy, merge then discard —
and they satisfy the snakes:

#row(snakeb.at(0).steps, s: 54%)

So every object is its own dual, and `R°` is `R` with its wires bent round the cup and the cap.
That is what makes reciprocation *definable* rather than primitive, and its four laws theorems:

#align(center, block(inset: (y: 5pt))[
  (i) `𝟙° = 𝟙`  #h(1cm) (ii) `(R S)° = S° R°`  #h(1cm) (iii) `(R ⊗ S)° = R° ⊗ S°`
  #h(1cm) (iv) `R ≤ S` implies `R° ≤ S°`
])

(i) is the snake above; (ii) is drawn below. The other two say nothing a picture makes clearer.

= The allegory primitives are definitions here

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*primitive, and what defines it here*], [*picture*]),

  [*reciprocation* `R° := bend ((R ⊗ 𝟙) cap)`, not a generator. \
   #src[It is the cup and the cap that reverse the arrow — a wire merely bumped up over the box and
   back down is an isotopy of `R` itself.]],
  fig({ conv((0, -0.80), $R$) }),

  [*intersection* `R ∩ S := ◁ (R ⊗ S) ▷`. \
   #src[Copy the input, run both, merge; the merge forces the two results to agree.]],
  fig({ meet((0, 0), $R$, $S$) }),

  [*containment* `R ⊑ S`, which an allegory *defines* as `R ∩ S = R`. Here `≤` is primitive and `∩`
   is derived, so the two directions are swapped.],
  align(center, src[no picture — this is the 2-cell itself]),

  [*maximal morphism* `⊤ := ⊸ ⟜`, free here; an allegory needs a unit object before it has one.],
  P(p-le-top),
)

= The eight axioms, and what proves each

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*axiom, and what supplies it*], [*picture*]),

  [`(R°)° = R` — the *snake*. \
   #src[Bending down and back up straightens out, so bending twice is the identity.]],
  P(p-conv-conv),

  [`(R S)° = S° R°` — mirroring the picture. \
   #src[Reflecting a chain left to right reverses it; each box comes back flipped.]],
  P(p-conv-comp),

  [`(R ∩ S)° = R° ∩ S°` — the same mirroring. \
   #src[`◁` and `▷` are each other's mirror image, so reflecting the convolution leaves its shape
   alone and only turns the boxes round.]],
  P(p-conv-inter),

  [`R ∩ R = R` — the lax copy law and the *special* law. \
   #src[Copy, run `R` twice, merge — the lax copy law pushes `R` back through the copy and
   `◁ ▷ = 𝟙` closes the bubble.]],
  P(p-meet-idem),

  [`R ∩ S = S ∩ R` — cocommutativity and commutativity. \
   #src[The two strands of `◁` are interchangeable, and so are those of `▷`.]],
  P(p-meet-comm),

  [`R ∩ (S ∩ T) = (R ∩ S) ∩ T` — coassociativity and associativity. \
   #src[Either bracketing builds the same three-way copy tree, and dually the same merge tree.]],
  P(p-meet-assoc, s: 70%),

  [`R (S ∩ T) ⊑ R S ∩ R T` — the lax copy law. \
   #src[Running `R` and then copying is below copying and then running `R` on each strand.]],
  P(p-semidistrib),

  [`R S ∩ T ⊑ (R ∩ T S°) S`, the modular law — *adjoined* as an axiom by an allegory, which has no
   structure to derive it from. Here Frobenius and the lax copy law give it. \
   #src[Strip the shared prefix `◁ (R ⊗ T)` off both sides and what is left is the merge slide: a
   box slides through a merge at the cost of its converse on the other strand.]],
  P(p-modular),
)

= Unitary and pre-tabular — what the other direction needs

The eight axioms are all a cartesian bicategory has to give back. Going the other way needs two
further conditions.

#table(
  columns: (3.2cm, 1fr, 1fr),
  align: (left + top, left + top, left + top),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*condition*], [*allegory*], [*Frobenius side*]),

  [*unitary*],
  [`T` is a *unit* when `𝟙 T` is the largest endomorphism on it and every object carries an entire
   arrow to it. \ #src[The point of a unit is that it makes `⊤` exist, as `p_α p_β°` through the
   unit — which is also where the lax discard law comes from.]],
  [*already there, for free.* The monoidal unit `𝕀` is the unit object, `⊸ : n ⟶ 𝕀` is the entire
   arrow every object carries to it — `𝟙 ≤ ⊸ ⟜` says so — and `⊤ = ⊸ ⟜` is maximal. Every
   cartesian bicategory of relations is unitary, with nothing assumed.],

  [*pre-tabular*],
  [`f, g` *tabulate* `R` when both are maps, `R = f° g`, and the two agree only on the diagonal:

   #row((cetz.canvas(length: 0.72cm, { meet((0, 0), $f f°$, $g g°$) }),
         $=$,
         cetz.canvas(length: 0.72cm, { wire((0, 0), (1.5, 0)) })))

   `R` is *tabular* when some pair tabulates it, and the allegory *pre-tabular* when every arrow
   lies under a tabular one.],
  [*this is what `⊗` is.* Given unitarity the condition reduces to tabulating each `⊤`, and a
   tabulation of `⊤` is precisely an object `n ⊗ m` with its two projections. One side derives the
   product from tabulations, the other posits it.],
)

Together they are the whole gap: *cartesian bicategory of relations ≃ unitary pre-tabular allegory*.

= Union and residual

`∪` and `/` are past where the eight axioms stop and past what the definition can build: a union
needs a *biproduct* on top of the Frobenius structure, a residual a *second composition* with linear
adjoints. Both are built, so both draw.

A union is a *tape*: the rounded wrapper is the second monoidal product, and its `▷`/`◁` open and
close a branch a particle takes exactly one of — the same fork-runs-join shape as a meet, on a
different product.

A residual is drawn as *long division*, deliberately not as its own definition. As a term it is a
composition against a complement, and drawing it that way needs a complement to mean anything. The
operation does not: it is one Galois connection, and the last section draws it with none.

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*statement*], [*picture*]),

  [`R ⊑ R ∪ S`. \ #src[`union R S := ⟨R, S⟩ [𝟙, 𝟙]`: offer both branches, then forget which was
   taken.]],
  P(p-union-left),

  [`R ∪ S = S ∪ R`. \ #src[The two branches of a tape are interchangeable, exactly as the two
   strands of `◁` are.]],
  P(p-union-comm),

  [`⊥ ∪ R = R`. \ #src[`⊥` is routed through the zero object; there is no shape for it, so it
   prints as a box.]],
  P(p-bot-union),

  [`R (S ∪ T) = R S ∪ R T` — composition distributes over union, which `∩` does not. \
   #src[This is what a *distributive* allegory has over an allegory.]],
  P(p-comp-union),

  [`(R ∪ S)° = R° ∪ S°`. \ #src[The converse is a 2-functor for the tape layer too.]],
  P(p-conv-union),

  [`R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)`, the law that makes the whole distributive. \
   #src[The one picture with both layers in it: meets inside a tape on the left, tapes around meets
   on the right.]],
  P(p-distrib, s: 78%),

  [`(R / S) S ⊑ R` — the residual is a lower bound of the arrows it is the greatest of. \
   #src[The bar is the last section's: amber ground for the numerator, the divisor laid inside it, a
   hairline of slack past it.]],
  P(p-residual),
)

= `(R S)° = S° R°`, drawn

The pictures below are not a retelling: each is drawn from one term of the chain that was actually
checked, so a picture and the term beside it cannot drift apart.

== These are not pictures of a converse

The converse is drawn with *two* bends, a cup on the way in and a cap on the way out. The proof
never draws that. An arrow is *the* converse of `R` as soon as it satisfies one equation between
UNBENT arrows into `𝕀` — two strands in on the left, one cap on the right — and bending is a
bijection, so settling the unbent equation settles the bent one. Hence every row below has a cap and
no cup, and an arrow that "is a converse" shows up not as a bent box but as a box sitting on the
*bottom* strand, mirrored.

#table(
  columns: (1fr,),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*the slide — the one rule the proof uses, and it uses it twice*]),
  P(p-conv-slide, s: 88%),
  [#src[A box on the BOTTOM strand facing a cap is the same as that box on the TOP strand, upright.
   Sliding round the bend is what turns `R°` into `R`, and it is the entire content of the theorem
   — the other seven steps are bookkeeping.]],
)

== The chain

One row per *term*: the right-hand side of every step is the left-hand side of the next. Watch which
*strand* each box is on — bottom means mirrored, top means upright.

#table(
  columns: (4.4cm, 1fr, 6.6cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[`(R S)° = S° R°` #h(8pt) #Pin(p-conv-comp)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(l42b.at(0).terms.at(0)),
  P(l42b.at(0).steps.at(0), s: 66%),
  [*the start.* #src[What has to be shown about `S° R°`: both boxes on the bottom strand, mirrored.]],

  raw(l42b.at(0).terms.at(1)),
  P(l42b.at(0).steps.at(1), s: 66%),
  [*1.* `⊗` is a functor. #src[*Same picture.*]],

  raw(l42b.at(0).terms.at(2)),
  P(l42b.at(0).steps.at(2), s: 66%),
  [*2. the slide.* `R°` is the box nearest the cap: it leaves the bottom strand, arrives on the top,
   and comes back upright as `R`. #src[*The first of the two steps that prove anything.*]],

  raw(l42b.at(0).terms.at(3)),
  P(l42b.at(0).steps.at(3), s: 66%),
  [*3.* re-bracketing. #src[*Same picture.*]],

  raw(l42b.at(0).terms.at(4)),
  P(l42b.at(0).steps.at(4), s: 66%),
  [*4. interchange.* `R` is on the top strand and `S°` on the bottom, so running them in sequence
   and running them side by side are the same thing. #src[Shows as a re-spacing only.]],

  raw(l42b.at(0).terms.at(5)),
  P(l42b.at(0).steps.at(5), s: 66%),
  [*5. interchange back.* Split them apart again, `R` first, so `S°` is the box facing the cap.],

  raw(l42b.at(0).terms.at(6)),
  P(l42b.at(0).steps.at(6), s: 66%),
  [*6.* re-bracketing. #src[*Same picture.*]],

  raw(l42b.at(0).terms.at(7)),
  P(l42b.at(0).steps.at(7), s: 66%),
  [*7. the slide,* on `S` this time. Both boxes are now on top, both upright, in the order `R` then
   `S`. #src[*The second and last real step.*]],

  raw(l42b.at(0).terms.at(8)),
  P(l42b.at(0).steps.at(8), s: 66%),
  [*8.* re-bracketing. #src[*Same picture.*]],

  raw(l42b.at(0).terms.at(9)),
  P(l42b.at(0).steps.at(9), s: 66%),
  [*9. interchange* once more; the two top-strand boxes merge into one. This is `R S` unbent.
   #src[*Done.*]],
)

*What the chain measures.* Steps 1, 3, 6, 8 and 9 change nothing and step 4 changes only spacing,
while the term column changes at every row. Those are associativity, the unit laws and interchange —
precisely the laws a string diagram has built into its geometry rather than as rewrites. Seven of
the nine steps are bureaucracy the picture language does not charge for, and the theorem is two
slides.

= The modular law, from Frobenius

Four terms, of which exactly one step is an inequality.

#table(
  columns: (5.4cm, 1fr, 5.8cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[*the modular law,* `R S ∩ T ≤ (R ∩ T S°) S` #h(8pt) #Pin(p-modular)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(mfb.at(0).terms.at(0)), P(mfb.at(0).steps.at(0), s: 62%),
  [*the start:* `R S ∩ T`. #src[A copy and a merge with `R S` above and `T` below.]],

  raw(mfb.at(0).terms.at(1)), P(mfb.at(0).steps.at(1), s: 62%),
  [*Factor out the shared prefix.* `(R S) ⊗ T` is `(R ⊗ T) (S ⊗ 𝟙)`, so everything before the `S`
   is common to both sides. #src[An equality, and drawn as one.]],

  raw(mfb.at(0).terms.at(2)), P(mfb.at(0).steps.at(2), s: 62%),
  [*The merge slide,* under the shared prefix. #src[`S` slides through the merge and reappears as
   `S°` on the other strand. *The only inequality in the proof.*]],

  raw(mfb.at(0).terms.at(3)), P(mfb.at(0).steps.at(3), s: 62%),
  [*Fold the prefix back in.* `R ⊗ (T S°)` is `(R ⊗ T) (𝟙 ⊗ S°)`, and the copy-merge pair reads as
   a meet again. #src[`(R ∩ T S°) S`, the goal.]],
)

== Inside the middle step

The merge slide mentions only `S` — `R` and `T` sit untouched in the prefix throughout. `S` occurs
once on the left and twice on the right, and the lax copy law is the only law in the definition that
may duplicate a box, so it has to be the inequality step. The chain shows it is the only one.

#table(
  columns: (5.4cm, 1fr, 5.8cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[*the merge slide,* `(S ⊗ 𝟙) ▷ ≤ (𝟙 ⊗ S°) ▷ S` #h(8pt) #Pin(p-nabla-slide)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(nsb.at(0).terms.at(0)), P(nsb.at(0).steps.at(0), s: 62%),
  [*the start:* `(S ⊗ 𝟙) ▷`.],

  raw(nsb.at(0).terms.at(1)), P(nsb.at(0).steps.at(1), s: 62%),
  [*Rebuild the merge* from a copy and a cap. #src[Which puts the term into the shape `(S ◁) ⊗ 𝟙`
   the lax copy law applies to.]],

  raw(nsb.at(0).terms.at(2)), P(nsb.at(0).steps.at(2), s: 62%),
  [*The lax copy law.* `S ◁` becomes `◁ (S ⊗ S)`: the box is copied. \
   #src[*The whole of the modular law, in one step.*]],

  raw(nsb.at(0).terms.at(3)), P(nsb.at(0).steps.at(3), s: 62%),
  [*Reshape back,* and the surviving duplicate slides round the cap to become `S°`.],
)

*What the associators cost.* `α` and `ρ` have no shape in this calculus and print as opaque boxes,
so the two middle terms are less legible than the ends. That is the honest price of drawing what was
checked; a hand-drawn version would have hidden them by working up to coherence.

= Maps

Every arrow is lax for `◁` and for `⊸`. Applying (ii) and (iv) above gives the merge form and the
unit form, the same statements about `▷` and `⟜`. Those four hold for *every* arrow. Their four
REVERSES do not, and each one holding is a property of the arrow.

#table(
  columns: (1fr, 4.6cm, 1fr),
  align: (center + horizon, left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*holds for every arrow*], [*property*], [*holds iff*]),

  [#src[`R ◁ ≤ ◁ (R ⊗ R)`] #v(-2pt) #P(p-lax-delta, s: 74%)],
  [(SV) *single valued* \ #src[`R° R ⊑ 𝟙`]],
  P(p-sv46, s: 74%),

  [#src[`R ⊸ ≤ ⊸`] #v(-2pt) #P(p-lax-bang, s: 74%)],
  [(TOT) *total* \ #src[`𝟙 ⊑ R R°`. With *single valued*, `R` is a *map*.]],
  P(p-tot47, s: 74%),

  [#src[`▷ R ≤ (R ⊗ R) ▷` — the converse of the lax copy law. *Not stated;* see below.]],
  [(INJ) *injective* \ #src[`R R° ⊑ 𝟙`]],
  P(p-inj48, s: 74%),

  [#src[`⟜ R ≤ ⟜` — the converse of the lax discard law. *Not stated;* see below.]],
  [(SUR) *surjective* \ #src[`𝟙 ⊑ R° R`, that is, `R°` is entire.]],
  P(p-sur49, s: 74%),
)

The right-hand column is the ADJOINT form of each property, and it is the definition used here,
because it is literally the allegory's own `Simple` and `Entire` — so a diagrammatic map and a book
map are one predicate with no translation layer. That the comonoid form and the adjoint form agree
is a separate theorem, and it is not proved here.

*Why the merge form and the unit form have no picture.* Both are converse-images, and getting them
needs `◁° = ▷`, `⊸° = ⟜` and `(f ⊗ g)° = f° ⊗ g°`. The first is a Frobenius computation at a
COMPOSITE object, which is the clause the printed definition omits — the same gap that leaves the
agreement above unproved. The four reverse inequations are unaffected.

= Entireness of an intersection

The *domain* of `R` is the part of the identity where `R` is defined, `Dom R = 𝟙 ∩ R R°`; `R` is
*entire* when it is defined everywhere, `Dom R = 𝟙`, equivalently `𝟙 ⊑ R R°` — which is (TOT)
above. When is an *intersection* entire?

#align(center, block(inset: (y: 6pt))[
  #P(p-entire, s: 80%) \
  #src[`Total (R ∩ S) ↔ 𝟙 ≤ R S°`]])

On the left `R ∩ S` is named *twice*; on the right `R` and `S` are named *once each* and the meet is
gone. That is the point of the lemma — the meet is needed to *ask* whether something is entire, not
to *answer* it — and it is why every later use quotes the right-hand form.

Where `⊑` is *defined* as `X ∩ Y = X`, the two sides are the same proposition and there is nothing
to prove. Here `≤` is primitive, so both directions are real steps — and they cost very different
things.

#table(
  columns: (5.0cm, 1fr, 6.0cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*`⟹`* #h(6pt) given `R ∩ S` entire, #Pin(ent-a)
    #h(6pt) show #Pin(ent-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(entb.at(0).terms.at(0)), P(entb.at(0).steps.at(0), s: 68%),
  [*the start:* `𝟙`.],

  raw(entb.at(0).terms.at(1)), P(entb.at(0).steps.at(1), s: 68%),
  [*the hypothesis:* `𝟙 ≤ P P°` at `P = R ∩ S`.],

  raw(entb.at(0).terms.at(2)), P(entb.at(0).steps.at(2), s: 68%),
  [*monotonicity, twice:* `R ∩ S ≤ R`, and `R ∩ S ≤ S` under `°`. #src[No modular law.]],
)

#table(
  columns: (5.0cm, 1fr, 6.0cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*`⟸`* #h(6pt) given #Pin(ent-b) #h(6pt) show
    `R ∩ S` entire, #Pin(ent-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(entb.at(1).terms.at(0)), P(entb.at(1).steps.at(0), s: 68%),
  [*the start:* `𝟙`.],

  raw(entb.at(1).terms.at(1)), P(entb.at(1).steps.at(1), s: 68%),
  [*the hypothesis,* met with `𝟙`. #src[`𝟙 ≤ 𝟙` and `𝟙 ≤ R S°`, so `𝟙` is below the meet.]],

  raw(entb.at(1).terms.at(2)), P(entb.at(1).steps.at(2), s: 68%),
  [`𝟙 ∩ R S° = 𝟙 ∩ (S ∩ R)(S ∩ R)°`. #src[`R S°` relates `a` to `a′` when some `b` has `a R b` and
   `a′ S b`. The `𝟙 ∩` sets `a′ = a`, and it then reads "some `b` has `a R b` and `a S b`" — one
   arrow of `R ∩ S`. Two arrows become one; that is the step, and it is what needs the modular law.]],

  raw(entb.at(1).terms.at(3)), P(entb.at(1).steps.at(3), s: 68%),
  [*`X ∩ Y ≤ Y`,* then `S ∩ R = R ∩ S`. #src[The outer fork drops away, leaving the goal.]],
)

*What the asymmetry says.* One direction is two applications of monotonicity; the other needs the
modular law, which needs Frobenius and the lax copy law. The third row of the second table is the
whole strength of the lemma; everything else is bookkeeping.

= The gaps

*Nothing on the allegory side.* All eight axioms are theorems of the definition, the modular
identity included.

*Two laws do no work here.* `▷◁≤𝟙` and `⟜⊸≤𝟙` occur only in the definition and are never used.
They are there to make `◁ ⊣ ▷` and `⊸ ⊣ ⟜` genuine adjunctions — which is what pins `▷ = ◁°` and
`⟜ = ⊸°` by uniqueness of adjoints — not to prove any allegory law.

*Two things are stated but unproved:* the merge form and the unit form of the lax laws, and the
agreement of the comonoid and adjoint forms of the map conditions. Both trace to the one omission in
the printed definition — no Frobenius structure at a composite object.

*The bridge runs one way only.* A cartesian bicategory carries a symmetric monoidal `⊗`; an
allegory carries nothing of the kind, which is what the two conditions above supply.

*Everything here is a theorem OF the axioms.* That relations satisfy them is not checked on this
branch: making the monoidal structure strict cost the `Rel(Set)` instances, so the layer has no
model here.

*What the definition alone does not have.*

#table(
  columns: (3.4cm, 6.0cm, auto),
  align: (left + top, left + top, left + top),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*construct*], [*counterpart*], [*status*]),

  [*tabulation*], [none], [no splitting of coreflexives; `⊤ = ⊸ ⟜` is all the tabular
  content there is.],

  [`∪`, `⊥`], [a *biproduct* `⊕` on top of the Frobenius structure], [built, and drawn above. Not
  derivable from the definition alone — the calculus has no union at all.],

  [`R / S`, complement], [a *second composition* with linear adjoints], [built, and drawn above,
  but axiomatised only: nothing on this branch instantiates the complement.],

  [`Λ`, power transpose], [none], [open. No calculus in this tower has a power object.],

  [allegory ⟹ cartesian bicategory], [rebuild `⊗` from tabulations], [deliberately not built.],
)

= The shunting rule

A map may be moved from one side of a containment to the other, at the cost of its converse:
`R f ≤ S ⟺ R ≤ S f°`, and its mirror. That is the workhorse of relational program calculation and
what makes point-free derivation possible at all — it is how a function gets out of the way so the
relation underneath can be reasoned about.

Each `↔` is two chains, and each direction spends exactly one half of *map* — never both.

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting right, `⟹`* #h(6pt) given #Pin(sr-a) #h(4pt)
    show #Pin(sr-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(srb.at(0).terms.at(0)),
  P(srb.at(0).steps.at(0), s: 74%),
  [*the start:* `R`.],

  raw(srb.at(0).terms.at(1)),
  P(srb.at(0).steps.at(1), s: 74%),
  [*total.* `𝟙 ≤ f f°`, so `f f°` may be inserted after `R`. #src[The only cost of this direction.]],

  raw(srb.at(0).terms.at(2)),
  P(srb.at(0).steps.at(2), s: 74%),
  [Re-bracket to `(R f) f°` and apply the hypothesis. #src[`R ≤ S f°`, the goal.]],
)

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting right, `⟸`* #h(6pt) given #Pin(sr-b) #h(4pt)
    show #Pin(sr-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(srb.at(1).terms.at(0)),
  P(srb.at(1).steps.at(0), s: 74%),
  [*the start:* `R f`.],

  raw(srb.at(1).terms.at(1)),
  P(srb.at(1).steps.at(1), s: 74%),
  [Apply the hypothesis on the left. #src[The two `f`s are now adjacent.]],

  raw(srb.at(1).terms.at(2)),
  P(srb.at(1).steps.at(2), s: 74%),
  [*single valued.* `f° f ≤ 𝟙`, so the pair cancels and `S` is left.],
)

*Shunting left is the mirror,* same shape, map on the other side throughout.

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting left, `⟹`* #h(6pt) given #Pin(sl-a) #h(4pt)
    show #Pin(sl-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(slb.at(0).terms.at(0)),
  P(slb.at(0).steps.at(0), s: 74%),
  [*the start:* `R`.],

  raw(slb.at(0).terms.at(1)),
  P(slb.at(0).steps.at(1), s: 74%),
  [*total.* `f f°` inserted before `R`.],

  raw(slb.at(0).terms.at(2)),
  P(slb.at(0).steps.at(2), s: 74%),
  [Re-bracket to `f (f° R)` and apply the hypothesis. #src[`R ≤ f S`.]],
)

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting left, `⟸`* #h(6pt) given #Pin(sl-b) #h(4pt)
    show #Pin(sl-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(slb.at(1).terms.at(0)),
  P(slb.at(1).steps.at(0), s: 74%),
  [*the start:* `f° R`.],

  raw(slb.at(1).terms.at(1)),
  P(slb.at(1).steps.at(1), s: 74%),
  [Apply the hypothesis on the right.],

  raw(slb.at(1).terms.at(2)),
  P(slb.at(1).steps.at(2), s: 74%),
  [*single valued.* The pair cancels, leaving `S`.],
)

*What the rule really is.* An adjunction. `R f ≤ S ⟺ R ≤ S f°` says `f ⊣ f°` in the
poset-enriched sense — *total* is its unit and *single valued* its counit — so "`f` is a map" and
"`f` has a right adjoint, namely `f°`" are the same statement, and any right adjoint of a map must
be its converse. The converse half, that an arrow with a right adjoint is a map, needs the
unproved agreement above.

= Division

Only division is drawn here, and not negation. The reason is not layout.

*Negation is not how programs get specified.* Complement occurs only in theory: the complement of a
*coreflexive*, `∼X ∩ 𝟙`, so a conditional can split on a guard; one direction of "well-founded =
inductive", the other direction needing nothing; and subtraction. Where the programs are actually
specified and derived — greedy, thinning, dynamic programming, Horner, knapsack, paragraph
formatting, string edit, bracketing, compression — there are *no* occurrences at all: that work runs
on local completeness, division and power objects, not on a Boolean structure. The one thing there
that looks like negation is not: `mnl R ≜ min(R° ⇨ R)` uses *implication*, a `Sup` that lives in any
locally complete allegory, and `∼R` is only its special case `R ⇨ 𝟘`.

So the specification vocabulary is ` `, `∩`, `∪`, `°`, `/`, `Λ`, `min`/`max`, `thin` and
catamorphisms, and a note about what those pictures look like has no business spending a page on an
operation none of them uses.

*Which also settles which picture of `/` is the right one.* As a term a residual is a composition
against a complement, and drawing it that way makes every homset a Boolean algebra. Division asks
for nothing of the kind: it wants one Galois connection, `T ⊑ R/S ⟺ T S ⊑ R`, and `Rel(Set)`
satisfies it with a bare `∀`, `(R / S) x y ≜ ∀z. S y z → R x z`, no negation in the definition.
`Rel` over a non-Boolean topos is a division allegory with no `∼` to draw with at all. What follows
is the account that needs none.

*What stays a box.* Dashed means "no definition to unfold and no metaphor either", which here leaves
one thing: `/ₛ`, a meet of two converses. A dashed box takes a label, so `(R /ₛ S)°` is a mirrored
box reading `R /ₛ S`, not a picture of the meet in its definition. Maps are the other exception, the
other way round: `f` is a plain *rectangle*, since the chamfer exists to say which way a relation
runs and a map runs one way by construction.

*What `/` is, without a complement anywhere: long division.* `R / S` is how much of `R` you can lay
down before `S` still fits inside what is left. Read the bar left to right, as a composite: `R / S`
first, then `S`, and the two together stay inside `R`. The leftover is the whole reason the cancel
law is `(R/S) S ⊑ R` and not an equality — and it is a hairline on purpose, because `R / S` is the
*largest* such quotient: any wider and `S` stops fitting.

Solid is what the equation pins: `R`'s left edge, `S`'s left edge, and the stretch before `S`, which
is what `R / S` measures. Dashed is the slack: nothing to the right of `S` is determined by
`T S ⊑ R`.

Read it as a *measurement*, not as a containment of relations. `R : a → c` and `S : b → c` are not
in the same hom-set, so `S` is not a sub-relation of `R` and neither is `R / S` — what sits inside
`R` is the composite `(R/S) S`, which does have `R`'s type. Pushed too far, the metaphor breaks in
the usual place: `⊥ / ⊥ = ⊤`.

#align(center, divbar(($R slash S$, "q"), ($S$, "d"), note: [the slack: why `⊑`]))
#align(center, src[transcribed — the universal property has a statement, this metaphor does not])

// ONE COLUMN, and only this table.  The exported pictures here are the widest in the note —
// `le_div_iff` is a `⟺` between two containments, four sub-pictures in a row, 10.9cm before scaling
// — and a second picture column for the long-division figure would have squeezed them to 60%.  One
// column at the full 22cm takes both side by side at 90%, and the six rows the metaphor does not
// reach simply have nothing beside them.  Every other table in the note keeps the two-column shape:
// their pictures are small and none of them is a division.
#table(
  columns: (1fr,),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*the ten laws, their pictures, and — where the metaphor reaches — the same law as
    long division*]),

  [*Division is the right adjoint of composition:* `T ⊑ R/S ⟺ T S ⊑ R`
   #v(4pt)
   #Pl(p-le-div)],

  [`T ⊑ S\R ⟺ S T ⊑ R` \ #src[`S\R ≜ (R°/S°)°`: left division is right division conjugated by
   the converse, not a second primitive.]
   #v(4pt)
   #Pl(p-le-ldiv)],

  [*cancel:* `(R/S) S ⊑ R`, and `S (S\R) ⊑ R` \ #src[The counit of each adjunction: the quotient
   composed back with the divisor lands under the numerator, never on it — the law the figure above
   draws.]
   #v(4pt)
   #stack(dir: ttb, spacing: 6pt, Pl(p-div-cancel), Pl(p-ldiv-cancel))],

  [*associate:* `R/(S₁ S₂) = (R/S₂)/S₁`, and `(S T)\R = T\(S\R)` \ #src[Dividing by a composite
   one factor at a time. The composition is drawn on the left of each equation and swallowed into a
   label on the right — and the bar shows what that swallowing hides: two tiles laid where there was
   one.]
   #v(4pt)
   #grid(columns: (10.5cm, auto), column-gutter: 18pt, align: horizon,
     stack(dir: ttb, spacing: 6pt, Pl(p-div-assoc), Pl(p-ldiv-assoc)),
     divbar(($(R slash S_2) slash S_1$, "q"), ($S_1$, "d"), ($S_2$, "d"), qw: 4.2))],

  [*maps:* `f (R/S) = (f R)/S`, and `R/(f S) = (R/S) f°` \ #src[`f` is a rectangle, so the first
   law reads off the picture: the same three pieces, bracketed two ways — the licence to drop the
   brackets and write `f R / S`. The second is the one that pays: a map moves out of a denominator
   and reappears as `f°` outside the box. Both are the shunting rule, spent twice. No bar: the
   metaphor has no handle on prefixing by a map.]
   #v(4pt)
   #stack(dir: ttb, spacing: 6pt, Pl(p-map-div), Pl(p-div-map))],

  [*symmetric division:* `(R/ₛS)° = S/ₛR`, and `(R/ₛS)(S/ₛT) ⊑ R/ₛT` \
   #src[`R/ₛS ≜ (R/S) ∩ (S/R)°`. The meet is inside the definition, not inside the statement, so it
   stays under the label: what the pictures show is that `/ₛ` is converse-symmetric and transitive,
   i.e. behaves like an equality of columns. No bar: a meet of two converses is not a quotient with
   a remainder.]
   #v(4pt)
   #stack(dir: ttb, spacing: 6pt, Pl(p-sdiv-recip), Pl(p-sdiv-comp))],
)

*The measurement.* Ten laws, ten pictures, and not one of them shows a generator. `∩`, `∪`, `°` and
composition are what the Frobenius generators build; `/` is none of those — it is posited, with
nothing to unfold. Eight of the ten carry the long-division bar instead, which is a metaphor for the
universal property rather than a composite of anything, and the two that do not say why in place.
