#import "@preview/dvdtyp:1.0.1": *

// ==========================================================================
//  Freyd §2.124 in string diagrams — a proof from the axioms.
//  House template: dvdtyp + the repo palette (subc/imgc/prec).
//  Calculus: cartesian bicategory of relations = graphical syntax of a
//  (unitary, tabular) allegory (Bonchi–Pavlović–Sobociński).
//  Composition is diagram order, left-to-right: `x y` = "first x then y".
// ==========================================================================

// ---- repo palette (as in Freyd/S1_70.typ) ---------------------------------
#let subc = rgb("#1457a6")   // blue  — S
#let imgc = rgb("#c0392b")   // red   — R
#let prec = rgb("#0a7d3f")   // green — P / witnesses
#let callout(c, body) = block(width: 100%, fill: c.lighten(94%), inset: 10pt, radius: 5pt,
  stroke: (left: 3pt + c), body)
#let gloss(body) = text(9pt, fill: luma(110), style: "italic", body)
#show raw.where(block: false): box.with(fill: luma(240), inset: (x: 2pt), outset: (y: 3pt), radius: 1.5pt)

// ---- drawing primitives -----------------------------------------------------
// This file's private copies now live in strdiag.typ, shared with diag/aop-diagrams.typ.
// A copy dot with no incoming stub, used to grow copy trees, is `delta(..., li: 0)`.
// Imported by name, not with `*`: `delta`, `nabla`, `cap` and `dot` shadow the Typst math symbols
// of the same name, so an unqualified `*` would silently turn `$nabla$` into a drawing function.
// Write the symbols themselves (`∇`) in math here.
#import "strdiag.typ": cetz, d, lw, wire, dot, gbox, delta, nabla, bang, unitR, swap, cap

// colour-coded box labels (R red, S blue, P green) — tracked across every figure
#let cR = text(fill: imgc)[$R$]
#let cS = text(fill: subc)[$S$]
#let cP = text(fill: prec)[$P$]

#let normalForm(ox, oy) = {
  wire((ox - 1.7, oy), (ox + 1.7, oy))
  d.content((ox - 2.0, oy), $a$); d.content((ox + 2.0, oy), $a$)
  d.line((ox, oy), (ox + 0.55, oy - 0.45), stroke: (thickness: lw))
  d.line((ox, oy), (ox + 0.55, oy - 1.05), stroke: (thickness: lw))
  dot((ox, oy))
  gbox((ox + 0.55, oy - 0.45), cR, w: 0.7, h: 0.4)
  gbox((ox + 0.55, oy - 1.05), cS, w: 0.7, h: 0.4)
  cap((ox + 1.25, oy - 0.45), (ox + 1.25, oy - 1.05), (ox + 1.85, oy - 0.75))
  d.content((ox + 2.1, oy - 0.75), text(fill: prec)[$b$])
}

#show: dvdtyp.with(
  title: "§2.124 in string diagrams — a proof from the axioms",
  subtitle: [Freyd & Scedrov, _Categories, Allegories_ §2.124: #h(3pt) $mono("Dom")(R inter S) = 1 inter S R^degree$ #h(3pt) — "a lemma we will use repeatedly"],
  author: none,
  accent: subc,
  abstract: [
    An earlier note only *drew* the two sides and declared them equal. Here is the actual proof: the
    generators, the axioms they obey, two lemmas, and a step-by-step calculation in point-free (AOP)
    style, then drawn. Every algebraic step is tagged with the axiom it uses. The three underlying
    identities are proved in Lean for #emph[arbitrary] relations — not a random sample — in
    `Freyd/S2_124.lean` (sorry-free, axioms `[propext, Classical.choice, Quot.sound]`).
  ],
)
#set text(hyphenate: false)

= What a string diagram is

An arrow of a symmetric monoidal category drawn as a circuit: white boxes are the *relations*
#h(1pt) #cR, #cS #h(1pt) $: a -> b$; wires carry objects. Left-to-right juxtaposition is composition
`;` (the book's `x y`), vertical stacking is the monoidal product `⊗` (the book's `⊕`). The identity
`1` is a bare wire. An *allegory*'s operations are recovered from *one* extra structure on every
object: a black-dotted *special Frobenius (co)monoid* — four generators.

#align(center, cetz.canvas({
  delta((0.6, 0));    d.content((0.65, -1.05), text(8.5pt)[copy #h(2pt) $Delta : a -> a ⊗ a$])
  bang((3.9, 0)); d.content((3.6, -1.05), text(8.5pt)[discard #h(2pt) $! : a -> I$])
  nabla((6.7, 0));   d.content((6.55, -1.05), text(8.5pt)[merge #h(2pt) $∇ : a ⊗ a -> a$])
  unitR((9.6, 0));    d.content((9.7, -1.05), text(8.5pt)[unit #h(2pt) $? : I -> a$])
}))

In #smallcaps[Rel] these are the diagonal relations: `copy` is `x ↦ (x,x)`, `discard` is `x ↦ ✓`,
`merge = copy°`, `unit = discard°`. Two derived pieces are used constantly — *converse* and *meet*:

*Converse* `R°` is *free*: bend both of #cR's wires around, so what was an input is read as an output.
In #smallcaps[Rel], #h(2pt) $x thin R^degree thin y$ #h(2pt) holds exactly when #h(2pt) $y thin R thin x$.

#align(center, cetz.canvas({
  d.content((-1.5, 0), $R^degree #h(2pt) = $)
  wire((-0.7, -0.6), (0.0, -0.6))
  d.bezier((0.0, -0.6), (0.8, 0.55), (0.7, -0.6), (0.2, 0.55), stroke: (thickness: lw))
  gbox((0.8, 0.55), cR, w: 0.75, h: 0.45)
  d.bezier((1.55, 0.55), (2.35, -0.6), (2.15, 0.55), (1.65, -0.6), stroke: (thickness: lw))
  wire((2.35, -0.6), (3.05, -0.6))
}))

*Meet* `R ∩ S` is *not* a new generator; it is the convolution #h(2pt)
$R inter S = Delta ; (R ⊗ S) ; ∇$: #h(2pt) copy the input, run #cR and #cS in parallel, then
*merge*. The merge forces the two outputs to *coincide* — it demands both `xRy` and `xSy`.

#align(center, cetz.canvas({
  delta((0.2, 0), li: 0.45, lo: 0.55, sp: 0.55)
  gbox((0.75, 0.55), cR, w: 0.8, h: 0.45); gbox((0.75, -0.55), cS, w: 0.8, h: 0.45)
  wire((1.55, 0.55), (1.95, 0.55)); wire((1.55, -0.55), (1.95, -0.55))
  nabla((2.55, 0), li: 0.6, lo: 0.45, sp: 0.55)
  d.content((3.3, 0), $= R inter S$)
}))

The *domain* used below is `Dom R = 1 ∩ R R°` (Freyd §2.122): the coreflexive `⊑ 1` picking out the
`a` that #cR relates to *something*.

= The axioms of the calculus

#definition("Special commutative Frobenius algebra (per object)")[
  The four dots obey these equations — the only moves a diagram may be rewritten by. `σ` is the wire
  swap; #h(1pt) *`?` is the unit* #h(1pt): a wire *created from nothing* (`? : I → a`), the converse of
  discard `!`. The pair `(Δ, !)` copies and deletes; its converse pair `(∇, ?)` merges and creates. Each
  law is drawn beside it (the monoid `(∇, ?)` laws — assoc, unit, commutative — are the vertical mirrors
  of the first three):
  #v(3pt)
  #table(
    columns: (1fr, auto),
    align: (left + horizon, center + horizon),
    inset: (x: 5pt, y: 8pt),
    stroke: (_, y) => if y > 0 { (top: 0.4pt + luma(215)) },
    [*counit* #h(5pt) `Δ;(1⊗!) = 1`], cetz.canvas({
      delta((0.3, 0), li: 0.3, lo: 0.42, sp: 0.33)
      bang((1.12, 0.33), li: 0.4)
      wire((0.72, -0.33), (1.35, -0.33))
      d.content((1.7, 0), $=$); wire((1.95, 0), (2.6, 0))
    }),
    [*cocommutative* #h(5pt) `Δ;σ = Δ`], cetz.canvas({
      delta((0.0, 0), li: 0.3, lo: 0.32, sp: 0.33)
      swap((0.32, 0), w: 0.5, sp: 0.33)
      wire((0.82, 0.33), (1.05, 0.33)); wire((0.82, -0.33), (1.05, -0.33))
      d.content((1.4, 0), $=$)
      delta((1.7, 0), li: 0.3, lo: 0.42, sp: 0.33)
    }),
    [*coassociative* #h(5pt) `Δ;(Δ⊗1) = Δ;(1⊗Δ)` \
     #gloss[the picture re-brackets three wires for free; `coassoc` in the Lean spells the
     associator `assocLR` out]], cetz.canvas({
      delta((0.3, 0), li: 0.3, lo: 0.4, sp: 0.42)
      delta((0.7, 0.42), li: 0, lo: 0.4, sp: 0.26)
      wire((0.7, -0.42), (1.1, -0.42))
      wire((1.1, 0.68), (1.35, 0.68)); wire((1.1, 0.16), (1.35, 0.16)); wire((1.1, -0.42), (1.35, -0.42))
      d.content((1.7, 0), $=$)
      delta((2.05, 0), li: 0.3, lo: 0.4, sp: 0.42)
      wire((2.45, 0.42), (2.85, 0.42))
      delta((2.45, -0.42), li: 0, lo: 0.4, sp: 0.26)
      wire((2.85, 0.42), (3.1, 0.42)); wire((2.85, -0.16), (3.1, -0.16)); wire((2.85, -0.68), (3.1, -0.68))
    }),
    [*special* #h(5pt) `Δ;∇ = 1` #h(4pt) #gloss[copy-then-merge = wire]], cetz.canvas({
      delta((0.0, 0), li: 0.3, lo: 0.4, sp: 0.3)
      nabla((0.8, 0), li: 0.4, lo: 0.35, sp: 0.3)
      d.content((1.5, 0), $=$); wire((1.75, 0), (2.4, 0))
    }),
    [*Frobenius* #h(5pt) `(Δ⊗1);(1⊗∇) = ∇;Δ = (1⊗Δ);(∇⊗1)` \
     #gloss[same suppression: `frobenius` in the Lean carries `assocLR` too, because `Prod` is not
     strictly associative]], cetz.canvas({
      wire((0.0, 0.42), (0.35, 0.42)); delta((0.35, 0.42), li: 0, lo: 0.4, sp: 0.26)
      wire((0.0, -0.42), (0.75, -0.42))
      d.bezier((0.75, 0.16), (1.25, -0.1), (1.05, 0.16), stroke: (thickness: lw))
      d.bezier((0.75, -0.42), (1.25, -0.1), (1.05, -0.42), stroke: (thickness: lw))
      dot((1.25, -0.1), hollow: true); wire((1.25, -0.1), (1.5, -0.1))
      wire((0.75, 0.68), (1.5, 0.68))
      d.content((1.95, 0.1), text(11pt)[$=$])
      nabla((2.75, 0.1), li: 0.45, lo: 0.0, sp: 0.4)
      delta((2.75, 0.1), li: 0.0, lo: 0.45, sp: 0.4)
    }),
  )
]

*Converse* `(-)°` is the involution reversing composition and fixing the structure:
$ (P;Q)^degree = Q^degree; P^degree, quad P^(degree degree) = P, quad Delta^degree = ∇, quad !^degree = ?, quad (P ⊗ Q)^degree = P^degree ⊗ Q^degree, $
whence `(R ∩ S)° = R° ∩ S°`. With #box[`cup = ?;Δ`] and #box[`cap = ∇;!`], the special and Frobenius
laws give the *yanking* (snake) equations, so a wire may be straightened.

#callout(prec)[
  *Derived — spider fusion.* From the four groups above, any *connected* diagram built only from
  `Δ, ∇, !, ?` with `m` inputs and `n` outputs equals the *single spider* `s_(m,n)`. This is the one
  power tool: a tangle of dots collapses to one node with the right number of legs.
]

= Two lemmas

#lemma("domain = copy · run · discard")[
  #grid(columns: (1.3fr, 1fr), align: horizon, gutter: 8pt,
    [$ mono("Dom") P #h(3pt) = #h(3pt) 1 inter P P^degree #h(3pt) = #h(3pt) Delta ; (1 ⊗ P) ; (1 ⊗ !). $
     #v(2pt) Copy the input; run #cP on one copy; *discard* its output. The discard is the existential
     "#cP relates to something", so this is the domain coreflexive. (Both sides denote
     `{(a,a) : ∃b. aPb}`.)],
    [#align(center, cetz.canvas({
       delta((0.0, 0), li: 0.5, lo: 0.55, sp: 0.5)
       wire((0.55, 0.5), (2.4, 0.5)); d.content((-0.85, 0), $a$); d.content((2.65, 0.5), $a$)
       wire((0.55, -0.5), (0.85, -0.5)); gbox((0.85, -0.5), cP, w: 0.7, h: 0.45)
       bang((2.0, -0.5), li: 0.45)
       d.content((1.2, -1.15), text(8pt)[$mono("Dom") P$])
     }))],
  )
]

#lemma("converse folds into a cap")[
  For #h(2pt) $R : a -> b$,
  $ (1 ⊗ R^degree) ; ∇ #h(3pt) = #h(3pt) (Delta ⊗ 1) ; (1 ⊗ R ⊗ 1) ; (1 ⊗ mono("cap")). $
  A converse `R°` feeding a merge equals: *copy* the surviving wire, run #cR forward, and *cap* its
  output against the incoming one — just "bend #cR, then yank" (converse + Frobenius). This is the move
  that turns `S R°` into a witness.
  #align(center, cetz.canvas({
    wire((-1.4, 0.5), (1.85, 0.5)); d.content((-1.65, 0.5), $a$)
    wire((-1.4, -0.55), (0.2, -0.55)); d.content((-1.65, -0.55), text(fill: prec)[$b$])
    d.bezier((0.2, -0.55), (0.95, 0.15), (0.85, -0.55), (0.35, 0.15), stroke: (thickness: lw))
    gbox((0.95, 0.15), cR, w: 0.65, h: 0.4)
    d.bezier((1.6, 0.15), (1.85, -0.55), (1.8, 0.15), (1.7, -0.55), stroke: (thickness: lw))
    nabla((2.35, 0), li: 0.5, lo: 0.4, sp: 0.55); d.content((2.95, 0), $a$)
    d.content((0.5, -1.25), text(8pt)[$(1 ⊗ R^degree);∇$])
    d.content((3.5, 0), text(13pt)[$=$])
    delta((4.6, 0), li: 0.5, lo: 0.5, sp: 0.4)
    d.content((3.95, 0), $a$)
    wire((5.1, 0.4), (6.9, 0.4)); d.content((7.15, 0.4), $a$)
    wire((5.1, -0.4), (5.35, -0.4)); gbox((5.35, -0.4), cR, w: 0.65, h: 0.4)
    wire((4.0, -1.2), (5.7, -1.2)); d.content((3.75, -1.2), text(fill: prec)[$b$])
    cap((6.0, -0.4), (5.7, -1.2), (6.55, -0.8))
    d.content((5.5, -1.75), text(8pt)[$(Delta ⊗ 1);(1 ⊗ R ⊗ 1);(1 ⊗ mono("cap"))$])
  }))
]

= The proof

#theorem[
  $ 1 inter S R^degree #h(4pt) = #h(4pt) mono("Dom")(R inter S). $
]

Read the pictures top to bottom: `Dom(R∩S)` and `1 ∩ S R°` both reduce to the *same* middle diagram
`W`, so `Dom(R∩S) = W = 1 ∩ S R°`. Each `=` is one graphical move.

#align(center)[
  #text(9pt)[*`Dom(R∩S)`* #h(3pt) #gloss[Lemma 1: copy `a`, run `R∩S` on one copy, discard]]
  #v(4pt)
  #cetz.canvas({
    delta((0, 0), li: 0.5, lo: 0.5, sp: 0.5); d.content((-0.8, 0), $a$)
    wire((0.5, 0.5), (3.0, 0.5)); d.content((3.25, 0.5), $a$)
    wire((0.5, -0.5), (0.9, -0.5))
    gbox((0.9, -0.5), [#cR #h(1pt) ∩ #h(1pt) #cS], w: 1.15, h: 0.5)
    bang((2.65, -0.5), li: 0.6)
  })
  #v(6pt)
  #text(10pt)[$=$] #h(4pt) #gloss[unfold `R∩S = Δ;(R⊗S);∇`; #h(2pt) `∇;! = cap`; #h(2pt) fuse the copies (coassoc)]
  #v(7pt)
  #cetz.canvas(normalForm(0, 0))
  #v(1pt) #text(8.5pt)[the normal form #h(2pt) `W = Δ³;(1⊗R⊗S);(1⊗cap)` #h(4pt) #gloss[tap `a`; run #cR, #cS; cap to one #text(fill: prec)[$b$]]]
  #v(7pt)
  #text(10pt)[$=$] #h(4pt) #gloss[Lemma 2: bend the `R°` straight]
  #v(7pt)
  #cetz.canvas({
    delta((0, 0), li: 0.6, lo: 0.55, sp: 0.8); d.content((-0.85, 0), $a$)
    wire((0.55, 0.8), (4.0, 0.8))
    wire((0.55, -0.8), (0.95, -0.8)); gbox((0.95, -0.8), cS, w: 0.7, h: 0.5)
    d.bezier((1.65, -0.8), (2.4, 0.15), (2.3, -0.8), (1.85, 0.15), stroke: (thickness: lw))
    gbox((2.4, 0.15), cR, w: 0.85, h: 0.5)
    d.bezier((3.25, 0.15), (4.0, -0.8), (3.85, 0.15), (3.35, -0.8), stroke: (thickness: lw))
    nabla((4.5, 0), li: 0.5, lo: 0.45, sp: 0.8); d.content((5.15, 0), $a$)
  })
  #v(3pt)
  #text(9pt)[*`1 ∩ S R°`* #h(3pt) #gloss[copy; the top wire is the `1`; `S` then the bent `R°`; merge]]
]

#v(4pt)
The one step with content is *Lemma 2* (bottom `=`): bending the `R°` in `S R°` straightens the
`S`–`R°` loop into #cR *beside* #cS, both fed by the same tap, their `b`-outputs meeting at the cap —
the shared witness #text(fill: prec)[$b$]. Everything else is unfolding `∩` and spider fusion. No
modular law appears; §2.124 is here *derived* from Frobenius + converse.

= Is this checked in Lean?

*Yes — every boxed result above is a Lean theorem in `Freyd/S2_124.lean`, sorry-free, for arbitrary
relations `R, S`:*

#align(center, table(
  columns: (auto, auto), align: (left, left), inset: 6pt, stroke: 0.4pt + luma(180),
  table.header([*in this note*], [*in `Freyd/S2_124.lean`*]),
  [Lemma 3.1 (domain = copy·run·discard)], [`dom_cd`],
  [Lemma 3.2 (converse folds into a cap)], [`cv_merge`],
  [Theorem 4.1 #h(2pt) `1 ∩ SR° = Dom(R∩S)`], [`dom_inter_rel` #h(2pt) — via `left_eq_W`, `right_eq_W`],
  [the axioms of §2 (special, Frobenius, coassoc, …)], [`special`, `frobenius`, `coassoc`, `counit`, …],
))

One honest caveat about *how* Lean checks them. Lean works in the concrete model #smallcaps[Rel]
(`Rel A B := A → B → Prop`) and confirms each equality holds there for all relations; the §2 axioms are
also proved there, so #smallcaps[Rel] is shown to be a model of the calculus. The step-by-step diagram
*rewriting* above is the human "why"; a fully point-free Lean replay of it would additionally need the
associator/unitor coherence lemmas (`Prod` is not strictly associative). The `1∩PP° → Δ;(1⊗P);!` collapse
of Lemma 1 needs one extra relational law beyond bare Frobenius — `adequacy` (`Δ;(R⊗R);∇ = R`) — stated
explicitly in the file. No modular law is used anywhere.

The abstract, allegory-level §2.124 that *does* use the modular law is `dom_inter` in `Freyd/S2_1.lean`;
its two halves are the two moves this diagram fuses into one:

#align(center, table(
  columns: (auto, auto),
  align: (left, left), inset: 6pt, stroke: 0.4pt + luma(180),
  table.header([*`dom_inter` step (allegory / AOP)*], [*string-diagram move*]),
  [`1 ∩ SR° ⊑ 1 ∩ (R∩S)R°` #h(2pt)— `modular_le S R° 1`], [Lemma 2: bend `R°`, so `R` hangs beside `S`],
  [`= 1 ∩ R(R°∩S°)` #h(2pt)— a coreflexive equals its reciprocal], [read the tapped loop either way (converse of a coreflexive = itself)],
  [`⊑ (R∩S)(R°∩S°) = Dom(R∩S)` #h(2pt)— `modular_le R (R°∩S°) 1`], [coassoc: the two prongs share one tap `Δ³` and one `cap`],
  [the outer `1` kept at each step (`le_inter` with `⊑ 1`)], [the straight *diagonal wire* — the spider only *taps* it, never deletes it],
))
