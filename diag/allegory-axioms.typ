// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name.  See the header of strdiag.typ.
#import "@preview/dvdtyp:1.0.1": dvdtyp, definition, theorem, example
#import "strdiag.typ": cetz, d, conv, meet, wire

// EVERY PICTURE OF A THEOREM BELOW IS EXPORTED, NOT DRAWN.  `./scripts/diag-export <decl>` walks the
// Lean declaration's TYPE and writes diag/generated/<decl>.typ, which binds the cetz drawing to
// `pic`; this note only places those bindings in table cells.  Hand-drawing them is how the first
// draft of this page got `inter_assoc` wrong — it showed coassociativity of `◁` instead of the axiom
// — and dropped the `=` from `recip_inter`.  A picture derived from the statement cannot drift from
// it.  `./scripts/diag-regen` redraws every binding below, reading the list off these very imports.
#import "generated/Freyd.Diag.CartBicat.conv_conv.typ": pic as p-conv-conv
#import "generated/Freyd.Diag.CartBicat.conv_comp.typ": pic as p-conv-comp
#import "generated/Freyd.Diag.conv_inter.typ": pic as p-conv-inter
#import "generated/Freyd.Diag.meet_idem.typ": pic as p-meet-idem
#import "generated/Freyd.Diag.meet_comm.typ": pic as p-meet-comm
#import "generated/Freyd.Diag.meet_assoc.typ": pic as p-meet-assoc
#import "generated/Freyd.Diag.semidistrib_of_lax.typ": pic as p-semidistrib
#import "generated/Freyd.Diag.modular_of_frobenius.typ": pic as p-modular
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
#import "generated/Freyd.Diag.Biprod.«≤_union_left».typ": pic as p-union-left
#import "generated/Freyd.Diag.Biprod.union_comm.typ": pic as p-union-comm
#import "generated/Freyd.Diag.Biprod.bot_union.typ": pic as p-bot-union
#import "generated/Freyd.Diag.Biprod.comp_union.typ": pic as p-comp-union
#import "generated/Freyd.Diag.Biprod.conv_union.typ": pic as p-conv-union
#import "generated/Freyd.Diag.FbCbRig.meet_union_distrib.typ": pic as p-distrib
#import "generated/Freyd.Diag.ClosedLinearBicat.«residual_comp_≤».typ": pic as p-residual
#import "generated/Freyd.Diag.CartBicat.conv_comp.proof.typ": branches as l42ii
#import "generated/Freyd.Diag.CartBicat.conv_tensHom.proof.typ": branches as l42iii
#import "generated/Freyd.Diag.CartBicat.conv_mono.proof.typ": branches as l42iv
#import "generated/Freyd.Diag.shunt_right.proof.typ": branches as srb
#import "generated/Freyd.Diag.CartBicat.«∇_slide_conv».proof.typ": branches as nsb
#import "generated/Freyd.Diag.modular_of_frobenius.proof.typ": branches as mfb
#import "generated/Freyd.Diag.CartBicat.«°_slide».typ": pic as p-conv-slide
#import "generated/Freyd.Diag.CartBicat.«∇_slide_conv».typ": pic as p-nabla-slide
#import "generated/Freyd.Diag.SingleValued.typ": pic as p-sv46
#import "generated/Freyd.Diag.Total.typ": pic as p-tot47
#import "generated/Freyd.Diag.Injective.typ": pic as p-inj48
#import "generated/Freyd.Diag.Surjective.typ": pic as p-sur49
#import "generated/Freyd.Diag.shunt_right.typ": lhs as sr-a, rhs as sr-b
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

// PAGINATED, not one endless page: a viewer's page number and page keys are worth more than the
// unbroken column, and the tables here are short enough that few of them straddle a break.  25cm
// wide because the widest exported picture is a `⟺` between two containments, four sub-pictures in
// a row.
#set page(width: 25cm, height: 35cm, margin: 1.5cm)
#set text(size: 11.5pt)
// The template supplies the title block, the running header, page numbers, heading numbering and
// the definition environment.  Everything it sets is merged into, not replaced by, the rules above.
#show: dvdtyp.with(
  title: "The allegory axioms, and what defines them in the Frobenius calculus",
)
#show raw: set text(size: 9.6pt)
#show heading: set block(above: 16pt, below: 9pt)
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

/// A proof in ONE ROW: the steps side by side, and under each the rule that reached it.  The
/// exporter draws the `=` (or `≤`) at the LEFT edge of every step after the first, so a hint
/// left-aligned in the same column lands under it — a `place`d one collided with the wires.
/// The first hint is therefore always empty.  Steps that change no picture are simply left out:
/// this is a note for a reader who is ahead of it, not a transcript.
///
/// `horizon` for the same reason as `row`: every canvas is symmetric about its own `y = 0`, so
/// centring them puts all the `=` of the chain on one line even when one step is twice as tall.
#let chain(steps, hints, s: 62%) = align(center, box(inset: (y: 6pt), grid(
  columns: steps.len(), align: horizon, column-gutter: 14pt, row-gutter: 1pt,
  ..steps.map(t => scale(x: s, y: s, reflow: true, t)),
  ..hints.map(h => src[#h]))))

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

== $forall$ object A, `(A, ◁, ⊸) ⊣ (A, ▷, ⟜)`

#grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-37, s: 52%) #v(-7pt) \ #src[`▷ ◁ ≤ 𝟙`]],
  [#P(p-38, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ◁ ▷`]],
  [#P(p-39, s: 52%) #v(-7pt) \ #src[`⟜ ⊸ ≤ 𝟙`]],
  [#P(p-40, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ⊸ ⟜`]],
)

== The Frobenius law

#row(frobb.at(0).steps, s: 54%)

The only clause coupling the comonoid to the monoid beyond adjointness. Both sides reduce to the
same picture, `▷ ◁` — merge, then copy — which is the two-in two-out *spider*. Every connected
diagram built from these four generators collapses to the spider on its own inputs and outputs, and
this equation is what starts that collapse. A *bubble* is the other order, `◁ ▷`: copy then merge,
a closed loop, which §4 uses.

== Every arrow is a lax comonoid homomorphism

#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-lax-delta, s: 60%) #v(-7pt) \ #src[`R◁ ≤ ◁(R⊗R)`]],
  [#P(p-lax-bang, s: 60%) #v(-7pt) \ #src[`R⊸ ≤ ⊸`]],
)

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

(ii) and (iii) are not pictures of a converse. An arrow IS the converse of `R` as soon as it
satisfies one equation between UNBENT arrows into `𝕀`, and bending is a bijection, so the cup is
never drawn: every step below closes with a cap and opens with nothing, and "is a converse" shows
up as a box on the *bottom* strand, mirrored. Both use one rule, the *slide* — a box on the bottom
strand facing a cap is that box on the top strand, upright:

#P(p-conv-slide, s: 62%)

== `(R S)° = S° R°`

#chain(
  (l42ii.at(0).steps.at(0), l42ii.at(0).steps.at(2), l42ii.at(0).steps.at(5),
   l42ii.at(0).steps.at(7)),
  ([], [slide], [interchange], [slide]), s: 46%)

== `(R ⊗ S)° = R° ⊗ S°`

A cap at a product is two caps behind a crossing, so the pair unbends one strand at a time and the
crossing is all that is left to move.

#chain(
  (l42iii.at(0).steps.at(0), l42iii.at(0).steps.at(2), l42iii.at(0).steps.at(5)),
  ([], [two caps, then slide twice], [`σ` past `S`]), s: 52%)

// Kept whole: the row is two pictures, and the break was falling between them and their heading.
#block(breakable: false)[
== `R ≤ S` implies `R° ≤ S°`

Here the cup IS drawn: `R` sits in a frame of wires built from `≫` and `⊗`, and both of those are
monotone, so the box may be replaced where it stands.

#chain(
  (l42iv.at(0).steps.at(1), l42iv.at(0).steps.at(2)),
  ([], [`≫`, `⊗` monotone]), s: 55%)
]



= The allegory primitives are definitions here

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*primitive, and what defines it here*], [*picture*]),

  [*reciprocation* `R° := bend ((R ⊗ 𝟙) cap)`, not a generator.],
  fig({ conv((0, -0.80), $R$) }),

  [*intersection* `R ∩ S := ◁ (R ⊗ S) ▷` — copy, run both, merge.],
  fig({ meet((0, 0), $R$, $S$) }),

  [*containment* `R ⊑ S`, which an allegory *defines* as `R ∩ S = R`. Here `≤` is primitive and `∩`
   is derived, so the two directions are swapped.],
  align(center, src[the 2-cell itself]),

  [*maximal morphism* `⊤ := ⊸ ⟜`, free here; an allegory needs a unit object first.],
  P(p-le-top),
)

= The eight axioms, and what proves each

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*axiom, and what supplies it*], [*picture*]),

  [`(R°)° = R` — the *snake*.], P(p-conv-conv),
  [`(R S)° = S° R°` — mirroring the picture.], P(p-conv-comp),
  [`(R ∩ S)° = R° ∩ S°` — the same mirroring; `◁` and `▷` are each other's mirror image.],
  P(p-conv-inter),
  [`R ∩ R = R` — the lax copy law, then `◁ ▷ = 𝟙` closes the bubble.], P(p-meet-idem),
  [`R ∩ S = S ∩ R` — cocommutativity and commutativity.], P(p-meet-comm),
  [`R ∩ (S ∩ T) = (R ∩ S) ∩ T` — coassociativity and associativity.], P(p-meet-assoc, s: 70%),
  [`R (S ∩ T) ⊑ R S ∩ R T` — the lax copy law.], P(p-semidistrib),
  [`R S ∩ T ⊑ (R ∩ T S°) S`, the modular law — *adjoined* as an axiom by an allegory, which has no
   structure to derive it from. Here Frobenius and the lax copy law give it.], P(p-modular),
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

= Union and residual

Both are past what the definition can build: a union needs a *biproduct* on top of the Frobenius
structure, a residual a *second composition* with linear adjoints. A union draws as a *tape* — the
rounded wrapper is the second product, and its fork and join open and close a branch a particle
takes exactly one of. A residual draws as *long division*, not as its own term, which is a
composition against a complement.

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
  [`(R / S) S ⊑ R` — the residual is a lower bound of the arrows it is the greatest of.],
  P(p-residual),
)

= The modular law, from Frobenius

#table(
  columns: (5.4cm, 1fr, 5.8cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[*the modular law,* `R S ∩ T ≤ (R ∩ T S°) S` #h(8pt) #Pin(p-modular)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(mfb.at(0).terms.at(0)), P(mfb.at(0).steps.at(0), s: 62%),
  [*the start:* `R S ∩ T`.],

  raw(mfb.at(0).terms.at(1)), P(mfb.at(0).steps.at(1), s: 62%),
  [*Factor out the shared prefix:* `(R S) ⊗ T` is `(R ⊗ T) (S ⊗ 𝟙)`.],

  raw(mfb.at(0).terms.at(2)), P(mfb.at(0).steps.at(2), s: 62%),
  [*The merge slide.* `S` slides through the merge and reappears as `S°` on the other strand.
   #src[*The only inequality in the proof.*]],

  raw(mfb.at(0).terms.at(3)), P(mfb.at(0).steps.at(3), s: 62%),
  [*Fold the prefix back in;* the copy-merge pair reads as a meet again.],
)

`S` occurs once on the left of the slide and twice on the right, and the lax copy law is the only law
in the definition that may duplicate a box — so that is where the inequality has to be.

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
  [*Rebuild the merge* from a copy and a right bracket, the shape the lax copy law applies to.],

  raw(nsb.at(0).terms.at(2)), P(nsb.at(0).steps.at(2), s: 62%),
  [*The lax copy law:* `S ◁` becomes `◁ (S ⊗ S)`, the box copied. #src[*The whole of the modular law,
   in one step.*]],

  raw(nsb.at(0).terms.at(3)), P(nsb.at(0).steps.at(3), s: 62%),
  [*Reshape back,* and the surviving duplicate slides round the right bracket to become `S°`.],
)

= Maps

Every arrow is lax for `◁` and for `⊸`; (ii) and (iv) above turn those into the same statements
about `▷` and `⟜`. All four hold for *every* arrow, their REVERSES do not, and each reverse holding
is a property of the arrow. The right-hand column is the *adjoint* form, which is the definition
used here because it is literally the allegory's `Simple` and `Entire`; that the two forms agree is
a separate theorem, not proved here.

#table(
  columns: (1fr, 4.6cm, 1fr),
  align: (center + horizon, left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*holds for every arrow*], [*property*], [*holds iff*]),

  [#src[`R ◁ ≤ ◁ (R ⊗ R)`] #v(-2pt) #P(p-lax-delta, s: 74%)],
  [(SV) *single valued* \ #src[`R° R ⊑ 𝟙`]],
  P(p-sv46, s: 74%),

  [#src[`R ⊸ ≤ ⊸`] #v(-2pt) #P(p-lax-bang, s: 74%)],
  [(TOT) *total* \ #src[`𝟙 ⊑ R R°`. With *single valued*, a *map*.]],
  P(p-tot47, s: 74%),

  [#src[`▷ R ≤ (R ⊗ R) ▷` — *not stated;* see below.]],
  [(INJ) *injective* \ #src[`R R° ⊑ 𝟙`]],
  P(p-inj48, s: 74%),

  [#src[`⟜ R ≤ ⟜` — *not stated;* see below.]],
  [(SUR) *surjective* \ #src[`𝟙 ⊑ R° R`, that is, `R°` entire.]],
  P(p-sur49, s: 74%),
)

The two unstated ones are converse-images, and getting them needs `◁° = ▷` and `⊸° = ⟜` — a
Frobenius computation at a COMPOSITE object, which is the clause the printed definition omits.

= Entireness of an intersection

`R` is *entire* when `𝟙 ⊑ R R°`, which is (TOT) above. When is an *intersection* entire?

#align(center, block(inset: (y: 6pt))[
  #P(p-entire, s: 80%) \
  #src[`Total (R ∩ S) ↔ 𝟙 ≤ R S°`]])

On the left `R ∩ S` is named *twice*; on the right `R` and `S` once each and the meet is gone. The
meet is needed to *ask* whether something is entire, not to *answer* it. Where `⊑` is *defined* as
`X ∩ Y = X` the two sides are one proposition; here `≤` is primitive, so both directions are real
steps — and they cost very different things.

#table(
  columns: (5.0cm, 1fr, 6.0cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*`⟹`* #h(6pt) given `R ∩ S` entire, #Pin(ent-a)
    #h(6pt) show #Pin(ent-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(entb.at(0).terms.at(0)), P(entb.at(0).steps.at(0), s: 68%), [*the start:* `𝟙`.],
  raw(entb.at(0).terms.at(1)), P(entb.at(0).steps.at(1), s: 68%),
  [*the hypothesis:* `𝟙 ≤ P P°` at `P = R ∩ S`.],
  raw(entb.at(0).terms.at(2)), P(entb.at(0).steps.at(2), s: 68%),
  [*monotonicity, twice.* #src[No modular law.]],
)

#table(
  columns: (5.0cm, 1fr, 6.0cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*`⟸`* #h(6pt) given #Pin(ent-b) #h(6pt) show
    `R ∩ S` entire, #Pin(ent-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(entb.at(1).terms.at(0)), P(entb.at(1).steps.at(0), s: 68%), [*the start:* `𝟙`.],

  raw(entb.at(1).terms.at(1)), P(entb.at(1).steps.at(1), s: 68%),
  [*the hypothesis,* met with `𝟙`.],

  raw(entb.at(1).terms.at(2)), P(entb.at(1).steps.at(2), s: 68%),
  [`𝟙 ∩ R S° = 𝟙 ∩ (S ∩ R)(S ∩ R)°`. #src[`R S°` relates `a` to `a′` when some `b` has `a R b` and
   `a′ S b`; the `𝟙 ∩` sets `a′ = a`, and it reads "some `b` has `a R b` and `a S b`" — one arrow of
   `R ∩ S`. Two arrows become one, and that is what needs the modular law.]],

  raw(entb.at(1).terms.at(3)), P(entb.at(1).steps.at(3), s: 68%),
  [*`X ∩ Y ≤ Y`,* then `S ∩ R = R ∩ S`.],
)

= The gaps

- All eight axioms are theorems of the definition, the modular identity included.
- `▷◁≤𝟙` and `⟜⊸≤𝟙` are never used. They are there to make `◁ ⊣ ▷` and `⊸ ⊣ ⟜` genuine
  adjunctions, which is what pins `▷ = ◁°` and `⟜ = ⊸°`.
- Unproved: the merge and unit forms of the lax laws, and the agreement of the comonoid and adjoint
  forms of the map conditions. Both trace to the one omission above.
- The bridge runs one way only: a cartesian bicategory carries `⊗`, an allegory carries nothing of
  the kind, which is what the two conditions supply.
- Everything here is a theorem OF the axioms. That relations satisfy them is not checked here.

#table(
  columns: (3.4cm, 6.0cm, auto),
  align: (left + top, left + top, left + top),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*construct*], [*counterpart*], [*status*]),

  [*tabulation*], [none], [`⊤ = ⊸ ⟜` is all the tabular content there is.],
  [`∪`, `⊥`], [a *biproduct* `⊕` on top of the Frobenius structure],
  [built, and drawn above. The calculus itself has no union.],
  [`R / S`, complement], [a *second composition* with linear adjoints],
  [built, and drawn above, but axiomatised only: nothing instantiates the complement.],
  [`Λ`, power transpose], [none], [open. No power object anywhere in this tower.],
  [allegory ⟹ cartesian bicategory], [rebuild `⊗` from tabulations], [deliberately not built.],
)

= The shunting rule

A map moves from one side of a containment to the other at the cost of its converse,
`R f ≤ S ⟺ R ≤ S f°`. It is how a function gets out of the way so the relation underneath can be
reasoned about. Each direction spends exactly one half of *map* — never both.

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting right, `⟹`* #h(6pt) given #Pin(sr-a) #h(4pt)
    show #Pin(sr-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(srb.at(0).terms.at(0)), P(srb.at(0).steps.at(0), s: 74%), [*the start:* `R`.],
  raw(srb.at(0).terms.at(1)), P(srb.at(0).steps.at(1), s: 74%),
  [*total:* `𝟙 ≤ f f°`, so `f f°` may be inserted after `R`.],
  raw(srb.at(0).terms.at(2)), P(srb.at(0).steps.at(2), s: 74%),
  [Re-bracket to `(R f) f°` and apply the hypothesis.],
)

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting right, `⟸`* #h(6pt) given #Pin(sr-b) #h(4pt)
    show #Pin(sr-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(srb.at(1).terms.at(0)), P(srb.at(1).steps.at(0), s: 74%), [*the start:* `R f`.],
  raw(srb.at(1).terms.at(1)), P(srb.at(1).steps.at(1), s: 74%),
  [Apply the hypothesis on the left; the two `f`s are now adjacent.],
  raw(srb.at(1).terms.at(2)), P(srb.at(1).steps.at(2), s: 74%),
  [*single valued:* `f° f ≤ 𝟙`, so the pair cancels.],
)

Shunting left is the mirror, same shape, map on the other side throughout. What the rule is, is an
adjunction: `f ⊣ f°`, with *total* the unit and *single valued* the counit, so "`f` is a map" and
"`f` has a right adjoint, namely `f°`" are one statement.

= Division

Division is drawn and negation is not, because negation is not how programs get specified: the
chapters where they are — greedy, thinning, dynamic programming, Horner, knapsack, paragraph
formatting, string edit, bracketing, compression — use local completeness, division and power
objects, and no Boolean structure at all. That also settles which picture of `/` is right. As a term
a residual is a composition against a complement, which makes every homset Boolean; division asks
for nothing of the kind, only the Galois connection `T ⊑ R/S ⟺ T S ⊑ R`, which `Rel(Set)` satisfies
with a bare `∀`, `(R / S) x y ≜ ∀z. S y z → R x z`.

*Long division.* `R / S` is how much of `R` you can lay down before `S` still fits in what is left.
Read the bar as a composite: `R / S` first, then `S`, the two together inside `R`. Solid is what the
equation pins — `R`'s left edge, `S`'s left edge, and the stretch before `S`. Dashed is the slack:
nothing to the right of `S` is determined by `T S ⊑ R`, which is why the cancel law is `(R/S) S ⊑ R`
and not an equality, and why the slack is a hairline — `R / S` is the *largest* such quotient.

It is a *measurement*, not a containment: `R : a → c` and `S : b → c` are not in the same hom-set,
so what sits inside `R` is the composite `(R/S) S`. Pushed too far the metaphor breaks in the usual
place, `⊥ / ⊥ = ⊤`.

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

  [`T ⊑ S\R ⟺ S T ⊑ R` \ #src[`S\R ≜ (R°/S°)°`: left division is right division conjugated by the
   converse, not a second primitive.]
   #v(4pt)
   #Pl(p-le-ldiv)],

  [*cancel:* `(R/S) S ⊑ R`, and `S (S\R) ⊑ R` \ #src[The counit of each adjunction — the law the
   figure above draws.]
   #v(4pt)
   #stack(dir: ttb, spacing: 6pt, Pl(p-div-cancel), Pl(p-ldiv-cancel))],

  [*associate:* `R/(S₁ S₂) = (R/S₂)/S₁`, and `(S T)\R = T\(S\R)` \ #src[Dividing by a composite one
   factor at a time; the bar shows what the label on the right hides — two tiles laid where there
   was one.]
   #v(4pt)
   #grid(columns: (10.5cm, auto), column-gutter: 18pt, align: horizon,
     stack(dir: ttb, spacing: 6pt, Pl(p-div-assoc), Pl(p-ldiv-assoc)),
     divbar(($(R slash S_2) slash S_1$, "q"), ($S_1$, "d"), ($S_2$, "d"), qw: 4.2))],

  [*maps:* `f (R/S) = (f R)/S`, and `R/(f S) = (R/S) f°` \ #src[The same three pieces bracketed two
   ways, which is the licence to write `f R / S`; then a map moves out of a denominator and
   reappears as `f°` outside the box. Both are the shunting rule, spent twice.]
   #v(4pt)
   #stack(dir: ttb, spacing: 6pt, Pl(p-map-div), Pl(p-div-map))],

  [*symmetric division:* `(R/ₛS)° = S/ₛR`, and `(R/ₛS)(S/ₛT) ⊑ R/ₛT` \
   #src[`R/ₛS ≜ (R/S) ∩ (S/R)°`. The meet is inside the definition, not the statement, so it stays
   under the label: `/ₛ` is converse-symmetric and transitive, like an equality of columns.]
   #v(4pt)
   #stack(dir: ttb, spacing: 6pt, Pl(p-sdiv-recip), Pl(p-sdiv-comp))],
)

Ten laws, ten pictures, and not one shows a generator: `∩`, `∪`, `°` and composition are what the
Frobenius generators build, and `/` is none of those — it is posited, with nothing to unfold.
