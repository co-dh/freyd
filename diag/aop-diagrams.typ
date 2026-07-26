// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name.  See the header of strdiag.typ.
#import "strdiag.typ": cetz, d, wire, gbox, note, delta, nabla, bang, unitR, cap, cup, conv, meet, chain, chain-w

#set page(width: 21cm, height: auto, margin: 1.6cm)
#set text(size: 10pt)
#set par(justify: true)
#show raw: set text(size: 8.5pt)

#let canvas(body) = align(center, cetz.canvas(body))
#let cap-below(body) = align(center, text(8.5pt, luma(80), body))

#align(center)[
  #text(15pt)[*Seven AOP theorems, drawn*] \
  #text(9pt, luma(90))[
    primitives in `diag/strdiag.typ`; the calculus is
    `functorialSemanticsForRelationalTheories.pdf` §4
  ]
]

#v(4pt)

A string diagram is an arrow of the monoidal category drawn as a circuit. Left-to-right juxtaposition
is composition `≫` — the book's diagram order, so `R S` means first `R` then `S` — and vertical
stacking is the monoidal product. A wire is an identity, a white box is a relation, and the black
dots are one algebraic structure: the special Frobenius (co)monoid every object carries in a
cartesian bicategory of relations. `diag/S2_124.typ` is the companion note that proves a
theorem in this calculus rather than only displaying one.

Each picture below is a Lean statement from this repo, drawn field for field. Converse is written
`R°`, as the Lean does; `functorialSemanticsForRelationalTheories.pdf` writes the same operation
`R†`.

= 0. The vocabulary

The four dots are `Δ` (copy), `!` (discard), `∇` (merge), `?` (unit) — Definition 4.1, clauses 1
and 2, carried by `diag/CB.lean` as the `CartBicat` fields `delta`/`bang`/`nabla`/`unitR`.

#canvas({
  delta((0.6, 0)); d.content((0.65, -1.05), text(8.5pt)[copy #h(2pt) $Delta : a -> a ⊗ a$])
  bang((3.9, 0)); d.content((3.6, -1.05), text(8.5pt)[discard #h(2pt) $! : a -> I$])
  nabla((6.7, 0)); d.content((6.55, -1.05), text(8.5pt)[merge #h(2pt) $∇ : a ⊗ a -> a$])
  unitR((9.6, 0)); d.content((9.7, -1.05), text(8.5pt)[unit #h(2pt) $? : I -> a$])
})

Bending a wire is done with a *cup* and a *cap* — `? ; Δ` and `∇ ; !`, whose dots the Frobenius
equations collapse. Bending down and back up again straightens out, which is what lets a wire be
turned around at all (p. 19).

#canvas({
  cup((0.0, 0), (0.75, 0.45), (0.75, -0.45))
  wire((0.75, 0.45), (1.15, 0.45)); wire((0.75, -0.45), (1.15, -0.45))
  d.content((0.5, -1.0), text(8.5pt)[cup #h(2pt) $I -> a ⊗ a$])
  wire((3.0, 0.45), (3.4, 0.45)); wire((3.0, -0.45), (3.4, -0.45))
  cap((3.4, 0.45), (3.4, -0.45), (4.15, 0))
  d.content((3.6, -1.0), text(8.5pt)[cap #h(2pt) $a ⊗ a -> I$])
})

Two derived pieces are used in every diagram that follows, so they come first. The *meet* `R ∩ S` is
not a new generator: it is the convolution `Δ ≫ (R ⊗ S) ≫ ∇` (p. 22, `meet` in
`diag/CB_Derived.lean`). Copy the input, run `R` and `S` on the two copies, then merge — and the
merge forces the two results to coincide, which is exactly "both `R` and `S`". The *converse* `R°`
is not a new generator either: bend both of `R`'s wires around, and what was an input is read as an
output (p. 19, `conv` in `diag/CB.lean`).

#canvas({
  d.content((-1.0, 0), $R inter S :=$)
  meet((0.0, 0), $R$, $S$)
  d.content((3.1, 0), $R^degree :=$)
  conv((3.95, -0.45), $R$)
})

Everywhere below, `R°` is drawn as a plain box rather than as that bent picture — the bending is
what `R°` *is*, not something to redraw at every occurrence.

== What the pictures mean in `Rel(Set)`

The captions below are allowed to name these shapes `∩` and `°` only because `diag/RelSetCB.lean`
proves they *are* those operations in this repo's own `Rel(Set)`, not merely something that behaves
like them. That file gives the whole dictionary:

#table(
  columns: (auto, 1fr),
  inset: 5pt, stroke: 0.4pt + luma(200), align: (left + horizon, left + horizon),
  table.header([*drawn*], [*what it is in `Rel(Set)`, and the theorem that says so*]),
  [a copy dot `Δ`],    [`deltaRel n = graph (fun x => (x, x))`, the diagonal — and `delta_eq`],
  [a discard dot `!`], [`bangRel n = graph (fun _ => PUnit.unit)`, the map to a point — `bang_eq`],
  [a merge dot `∇`],   [`nabla_eq`: `∇ = Δ°`; `deltaRel_recip_apply` says `(x, y) ∇ z ↔ x = z ∧ y = z`,
                        which is why merging two strands demands that both agree],
  [a unit dot `?`],    [`unitR_eq`: `? = !°`; `bangRel_recip_apply` says it relates the point to
                        everything],
  [the `meet` combinator], [`meet_eq_inter`: `Δ ≫ (R ⊗ S) ≫ ∇ = R ∩ S`, the intersection of
                        `Allegory RelSet`],
  [a bent-wire converse],  [`conv_eq_recip`: `conv R = R°`, the ordinary relational converse],
  [`! ≫ ?`],               [`top_apply`: `⊤` relates everything to everything],
)

#v(3pt)

One thing every picture here silently does that its Lean statement does not: it *suppresses the
coherence maps*. Stacking three wires and re-bracketing them is free on paper, but `(a × b) × c` is
not `a × (b × c)` as a Lean type, so `diag/Monoidal.lean` carries a real associator arrow
`tensAssoc`, spelled out in `delta_assoc` and in both halves of the Frobenius equation
`frob_left`/`frob_right`. Wherever a diagram below stacks more than two strands — the modular law and the tabulation
meet — read it as the picture of a statement that has associators written out.

= 1. Map shunting — `map_shunt_right`, `map_shunt_left`

The workhorse of relational program calculation (`AOP/A4_2.lean`, B&dM 4.19 and 4.20): for a *map*
`f`, composing with `f` on one side of a containment is the same as composing with `f°` on the
other. Diagrammatically this is the unit/counit triangle of the adjunction `f ⊣ f°` — Lemma 4.8 of
`functorialSemanticsForRelationalTheories.pdf`, which says `f` is a map exactly when it has a right
adjoint, and that adjoint is `f°`.

#canvas({
  let w1 = chain-w(1)
  let w2 = chain-w(2)
  d.content((-0.75, 0), $arrow.l.r.double$)
  chain((0, 0.8), ($R$, $f$))
  d.content((w2 + 0.4, 0.8), $subset.sq.eq$); chain((w2 + 0.8, 0.8), ($S$,))
  chain((w2 - w1, -0.8), ($R$,))
  d.content((w2 + 0.4, -0.8), $subset.sq.eq$); chain((w2 + 0.8, -0.8), ($S$, $f^degree$))
})
#cap-below[`map_shunt_right`: for a map `f`, `R ≫ f ⊑ S ↔ R ⊑ S ≫ f°`]

#v(6pt)

#canvas({
  let w1 = chain-w(1)
  let w2 = chain-w(2)
  d.content((-0.75, 0), $arrow.l.r.double$)
  chain((0, 0.8), ($f^degree$, $R$))
  d.content((w2 + 0.4, 0.8), $subset.sq.eq$); chain((w2 + 0.8, 0.8), ($S$,))
  chain((w2 - w1, -0.8), ($R$,))
  d.content((w2 + 0.4, -0.8), $subset.sq.eq$); chain((w2 + 0.8, -0.8), ($f$, $S$))
})
#cap-below[`map_shunt_left`: for a map `f`, `f° ≫ R ⊑ S ↔ R ⊑ f ≫ S`]

= 2. The map dictionary — `Entire`, `Simple`, `Map`

`Freyd/S2_10.lean` §2.13 defines `Simple R := R° ≫ R ⊑ 𝟙` and `Entire R := dom R = 𝟙`, the latter
equivalent to `𝟙 ⊑ R ≫ R°`; a `Map` is both. These are inequations (46) and (47) of Lemma 4.4,
p. 20, where the paper calls them single-valued and total.

#canvas({
  let w1 = chain-w(1)
  let w2 = chain-w(2)
  chain((0, 0.8), ($R^degree$, $R$))
  d.content((w2 + 0.4, 0.8), $subset.sq.eq$); wire((w2 + 0.8, 0.8), (w2 + 0.8 + w1, 0.8))
  wire((w2 - w1, -0.8), (w2, -0.8))
  d.content((w2 + 0.4, -0.8), $subset.sq.eq$); chain((w2 + 0.8, -0.8), ($R$, $R^degree$))
  note((2 * w2 + 1.0, 0.8), [(46) `Simple` — single valued])
  note((2 * w2 + 1.0, -0.8), [(47) `Entire` — total])
})

The same two conditions read off the Frobenius structure instead. Every arrow is only a *lax*
comonoid homomorphism — that is eq. (3), p. 4, the `lax_delta` and `lax_bang` fields — and a map is
precisely an arrow for which those two inequations are equalities.

#canvas({
  // R ; Δ  =  Δ ; (R ⊗ R)
  wire((0, 0.9), (0.34, 0.9)); gbox((0.34, 0.9), $R$)
  delta((1.56, 0.9), li: 0.3, lo: 0.5, sp: 0.55)
  wire((2.06, 1.45), (2.4, 1.45)); wire((2.06, 0.35), (2.4, 0.35))
  d.content((2.85, 0.9), $=$)
  delta((3.4, 0.9), li: 0.4, lo: 0.3, sp: 0.55)
  gbox((3.7, 1.45), $R$); gbox((3.7, 0.35), $R$)
  wire((4.62, 1.45), (4.96, 1.45)); wire((4.62, 0.35), (4.96, 0.35))
  note((5.5, 0.9), [`Simple` again: `R ≫ Δ = Δ ≫ (R ⊗ R)`])
  // R ; !  =  !
  wire((0, -0.9), (0.34, -0.9)); gbox((0.34, -0.9), $R$)
  bang((1.76, -0.9), li: 0.5)
  d.content((2.85, -0.9), $=$)
  bang((3.9, -0.9), li: 1.0)
  note((5.5, -0.9), [`Entire` again: `R ≫ ! = !`])
})

= 3. Simple relations distribute over the meet — `simple_dist_inter`

`Freyd/S2_10.lean` §2.136: if `F` is simple then `F ≫ (R ∩ S) = (F ≫ R) ∩ (F ≫ S)`. The `⊑`
direction of this is eq. (3) on p. 4 — it holds for every arrow, because `F` can always be copied
early rather than late. Simplicity is exactly what tightens it to an equality, which is why this is
the engine of §2.141 below.

#canvas({
  wire((0, 0), (0.34, 0)); gbox((0.34, 0), $F$)
  meet((1.66, 0), $R$, $S$)
  d.content((3.95, 0), $=$)
  delta((4.65, 0), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((4.95, 0.62), $F$); wire((5.87, 0.62), (6.17, 0.62)); gbox((6.17, 0.62), $R$)
  gbox((4.95, -0.62), $F$); wire((5.87, -0.62), (6.17, -0.62)); gbox((6.17, -0.62), $S$)
  nabla((7.39, 0), li: 0.3, lo: 0.4, sp: 0.62)
})

= 4. The modular law — `modular_le`, `modular_le_right`, `modular_sym`

The one axiom of an allegory that is not a lattice law (`Freyd/S2_10.lean` §2.11, order form
`modular_le`). Its two one-sided halves are `modular_le_right` (`AOP/A4_1.lean`), and B&dM 4.8's
symmetric form `modular_sym` is visibly the two halves applied at once.

#canvas({
  // the left-hand side, (R S) ∩ T, is the same in all three rows
  let lhs(y) = {
    delta((0, y), li: 0.4, lo: 0.3, sp: 0.62)
    gbox((0.3, y + 0.62), $R$); wire((1.22, y + 0.62), (1.52, y + 0.62))
    gbox((1.52, y + 0.62), $S$)
    gbox((0.3, y - 0.62), $T$); wire((1.22, y - 0.62), (2.44, y - 0.62))
    nabla((2.74, y), li: 0.3, lo: 0.4, sp: 0.62)
    d.content((3.45, y), $subset.sq.eq$)
  }
  let x0 = 4.15   // where every right-hand side starts, clear of the ⊑
  // the meet (R ∩ T S°), used by rows 1 and 3
  let meetRTS(x, y) = {
    delta((x, y), li: 0.4, lo: 0.3, sp: 0.62)
    gbox((x + 0.3, y + 0.62), $R$); wire((x + 1.22, y + 0.62), (x + 2.44, y + 0.62))
    gbox((x + 0.3, y - 0.62), $T$); wire((x + 1.22, y - 0.62), (x + 1.52, y - 0.62))
    gbox((x + 1.52, y - 0.62), $S^degree$)
    nabla((x + 2.74, y), li: 0.3, lo: 0.3, sp: 0.62)
  }
  // the meet (S ∩ R° T), used by rows 2 and 3
  let meetSRT(x, y) = {
    gbox((x + 0.3, y + 0.62), $S$); wire((x + 1.22, y + 0.62), (x + 2.44, y + 0.62))
    gbox((x + 0.3, y - 0.62), $R^degree$); wire((x + 1.22, y - 0.62), (x + 1.52, y - 0.62))
    gbox((x + 1.52, y - 0.62), $T$)
    nabla((x + 2.74, y), li: 0.3, lo: 0.4, sp: 0.62)
  }
  // (R S) ∩ T ⊑ (R ∩ T S°) S
  lhs(2.6)
  meetRTS(x0, 2.6)
  gbox((x0 + 3.04, 2.6), $S$); wire((x0 + 3.96, 2.6), (x0 + 4.3, 2.6))
  // (R S) ∩ T ⊑ R (S ∩ R° T)
  lhs(0)
  wire((x0, 0), (x0 + 0.34, 0)); gbox((x0 + 0.34, 0), $R$)
  delta((x0 + 1.56, 0), li: 0.3, lo: 0.3, sp: 0.62)
  meetSRT(x0 + 1.56, 0)
  // (R S) ∩ T ⊑ (R ∩ T S°) (S ∩ R° T) — visibly the two rows above, applied at once
  lhs(-2.6)
  meetRTS(x0, -2.6)
  delta((x0 + 3.04, -2.6), li: 0.0, lo: 0.3, sp: 0.62)
  meetSRT(x0 + 3.04, -2.6)
  note((x0 + 6.5, 2.6), [`modular_le`])
  note((x0 + 6.5, 0), [`modular_le_right`])
  note((x0 + 6.5, -2.6), [`modular_sym`])
})

= 5. Domain — `dom`, `dom_UP`

A relation `X : a ⟶ a` is *coreflexive* when `X ⊑ 𝟙`: a wire that filters and does nothing else.

#canvas({
  let w1 = chain-w(1)
  chain((0, 0), ($X$,))
  d.content((w1 + 0.4, 0), $subset.sq.eq$); wire((w1 + 0.8, 0), (2 * w1 + 0.8, 0))
  note((2 * w1 + 1.2, 0), [`Coreflexive X`])
})

`dom R` (`Freyd/S2_10.lean` §2.122) is the coreflexive `𝟙 ∩ R ≫ R°` — go out along `R` and come
back, and keep only the inputs for which that round trip returns. The identity strand of the meet is
drawn as what it is, a bare wire.

#canvas({
  d.content((-1.15, 0), $"dom" R :=$)
  delta((0, 0), li: 0.4, lo: 0.3, sp: 0.62)
  wire((0.3, 0.62), (2.44, 0.62))
  gbox((0.3, -0.62), $R$); wire((1.22, -0.62), (1.52, -0.62)); gbox((1.52, -0.62), $R^degree$)
  nabla((2.74, 0), li: 0.3, lo: 0.4, sp: 0.62)
})

Its universal property, `dom_UP` (`AOP/A4_2.lean`, B&dM 4.11): among coreflexives, `dom R` is the
least one that `R` factors through.

#canvas({
  let wd = chain-w(1, w: 1.35)
  let w1 = chain-w(1)
  d.content((-0.75, 0), $arrow.l.r.double$)
  chain((0, 0.8), ($"dom" R$,), w: 1.35)
  d.content((wd + 0.4, 0.8), $subset.sq.eq$); chain((wd + 0.8, 0.8), ($X$,))
  chain((wd - w1, -0.8), ($R$,))
  d.content((wd + 0.4, -0.8), $subset.sq.eq$); chain((wd + 0.8, -0.8), ($X$, $R$))
})
#cap-below[`dom_UP`: for coreflexive `X`, `dom R ⊑ X ↔ R ⊑ X ≫ R`]

= 6. Tabulations — `Tabulates`, `tabulates_monic_pair`

`Freyd/S2_10.lean` §2.14: maps `f : c ⟶ a` and `g : c ⟶ b` *tabulate* `R : a ⟶ b` when
`R = f° ≫ g` and `f ≫ f° ∩ g ≫ g° = 𝟙`. The first equation says the span computes `R`; the second
says the span is *jointly monic* — nothing collapses.

#canvas({
  let w1 = chain-w(1)
  chain((0, 0), ($R$,))
  d.content((w1 + 0.4, 0), $=$); chain((w1 + 0.8, 0), ($f^degree$, $g$))
  delta((6.4, 0), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((6.7, 0.62), $f$); wire((7.62, 0.62), (7.92, 0.62)); gbox((7.92, 0.62), $f^degree$)
  gbox((6.7, -0.62), $g$); wire((7.62, -0.62), (7.92, -0.62)); gbox((7.92, -0.62), $g^degree$)
  nabla((9.14, 0), li: 0.3, lo: 0.4, sp: 0.62)
  d.content((10.0, 0), $=$)
  wire((10.4, 0), (12.0, 0))
})

§2.141, `tabulates_monic_pair`: that second equation makes `(f, g)` a monic pair in `Map(𝒜)`. The
proof is one rewrite — push a map `h` through the meet, which is legal by `simple_dist_inter` above,
since every map is simple.

#canvas({
  wire((0, 0), (0.34, 0)); gbox((0.34, 0), $h$)
  delta((1.66, 0), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((1.96, 0.62), $f$); wire((2.88, 0.62), (3.18, 0.62)); gbox((3.18, 0.62), $f^degree$)
  gbox((1.96, -0.62), $g$); wire((2.88, -0.62), (3.18, -0.62)); gbox((3.18, -0.62), $g^degree$)
  nabla((4.4, 0), li: 0.3, lo: 0.4, sp: 0.62)
  d.content((5.15, 0), $=$)
  delta((5.9, 0), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((6.2, 0.62), $h$); wire((7.12, 0.62), (7.42, 0.62)); gbox((7.42, 0.62), $f$)
  wire((8.34, 0.62), (8.64, 0.62)); gbox((8.64, 0.62), $f^degree$)
  gbox((6.2, -0.62), $h$); wire((7.12, -0.62), (7.42, -0.62)); gbox((7.42, -0.62), $g$)
  wire((8.34, -0.62), (8.64, -0.62)); gbox((8.64, -0.62), $g^degree$)
  nabla((9.86, 0), li: 0.3, lo: 0.4, sp: 0.62)
})

Read left to right, the left-hand side is `h ≫ 𝟙 = h`; read right to left, the right-hand side is
built only from `h ≫ f` and `h ≫ g`. So two maps agreeing on `f` and on `g` are equal.

= 7. Division as a two-sided rule — `le_div_iff`

`Freyd/S2_30.lean` §2.31: `T ⊑ R / S ↔ T ≫ S ⊑ R`. Both sides of the equivalence are drawable
today, but `R / S` itself is *not* a composite of the generators — every operation of this calculus
is monotone in each hole, and division is antitone in `S`. It is drawn dashed for that reason; a
first-class residual box needs the second composition of `diag/FO.lean`
(`DiagrammaticAlgebraOfFirstOrderLogic.pdf` §5), which is phase 9.

#canvas({
  let w1 = chain-w(1)
  let w2 = chain-w(2)
  d.content((-0.75, 0), $arrow.l.r.double$)
  chain((w2 - w1, 0.8), ($T$,))
  d.content((w2 + 0.4, 0.8), $subset.sq.eq$)
  chain((w2 + 0.8, 0.8), ($R slash S$,), w: 1.3, dashed: (0,))
  chain((0, -0.8), ($T$, $S$))
  d.content((w2 + 0.4, -0.8), $subset.sq.eq$); chain((w2 + 0.8, -0.8), ($R$,))
})
#cap-below[`le_div_iff`: `T ⊑ R / S ↔ T ≫ S ⊑ R`]

Taking `T := R / S` in the right-to-left direction gives the semi-commutative triangle that defines
division, `div_comp_le`:

#canvas({
  let wr = chain-w(2, w: 1.3)
  chain((0, 0), ($R slash S$, $S$), w: 1.3, dashed: (0,))
  d.content((wr + 0.4, 0), $subset.sq.eq$)
  chain((wr + 0.8, 0), ($R$,))
})
