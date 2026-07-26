#import "strdiag.typ": *

#set page(width: 21cm, height: auto, margin: 1.6cm)
#set text(size: 10pt)
#set par(justify: true)
#show raw: set text(size: 8.5pt)

#let canvas(body) = align(center, cetz.canvas(body))
#let cap-below(body) = align(center, text(8.5pt, luma(80), body))

#align(center)[
  #text(15pt)[*Seven AOP theorems, drawn*] \
  #text(9pt, luma(90))[
    primitives in `Freyd/note/strdiag.typ`; the calculus is
    `functorialSemanticsForRelationalTheories.pdf` §4
  ]
]

#v(4pt)

A string diagram is an arrow of the monoidal category drawn as a circuit. Left-to-right juxtaposition
is composition `≫` — the book's diagram order, so `R S` means first `R` then `S` — and vertical
stacking is the monoidal product. A wire is an identity, a white box is a relation, and the black
dots are one algebraic structure: the special Frobenius (co)monoid every object carries in a
cartesian bicategory of relations.

Each picture below is a Lean statement from this repo, drawn field for field. Converse is written
`R°`, as the Lean does; `functorialSemanticsForRelationalTheories.pdf` writes the same operation
`R†`.

= 0. The vocabulary

The four dots are `Δ` (copy), `!` (discard), `∇` (merge), `?` (unit) — Definition 4.1, clauses 1
and 2, and the `cop`/`dis`/`mer`/`un` fields of `diag/CB.lean`. In `Rel` they are the diagonal
relations: `Δ` is $x |-> (x, x)$, `!` is the map to a point, and `∇ = Δ°`, `? = !°`.

#canvas({
  copy((0.7, 0)); d.content((0.85, -1.15), text(8.5pt)[copy $Delta : n -> n times n$])
  discard((3.9, 0)); d.content((3.75, -1.15), text(8.5pt)[discard $! : n -> I$])
  merge((6.9, 0)); d.content((6.85, -1.15), text(8.5pt)[merge $nabla : n times n -> n$])
  unit((10.0, 0)); d.content((10.2, -1.15), text(8.5pt)[unit $? : I -> n$])
})

Two derived pieces are used in every diagram that follows, so they come first. The *meet* `R ∩ S` is
not a new generator: it is the convolution `Δ ≫ (R ⊗ S) ≫ ∇` (p. 22, `convolution` in
`diag/CB_Derived.lean`). Copy the input, run `R` and `S` on the two copies, then merge — and the
merge forces the two results to coincide, which is exactly "both `R` and `S`". The *converse* `R°`
is not a new generator either: bend both of `R`'s wires around with a cup and a cap, and what was
an input is read as an output (p. 19, `conv` in `diag/CB.lean`).

#canvas({
  d.content((-0.95, 0), $R inter S :=$)
  meet((0.0, 0), $R$, $S$)
  d.content((4.6, 0), $R^degree :=$)
  conv((5.6, -0.45), $R$)
})

Everywhere below, `R°` is drawn as a plain box rather than as that bent picture — the bending is
what `R°` *is*, not something to redraw at every occurrence.

= 1. Map shunting — `map_shunt_right`, `map_shunt_left`

The workhorse of relational program calculation (`AOP/A4_2.lean`, B&dM 4.19 and 4.20): for a *map*
`f`, composing with `f` on one side of a containment is the same as composing with `f°` on the
other. Diagrammatically this is the unit/counit triangle of the adjunction `f ⊣ f°` — Lemma 4.8 of
`functorialSemanticsForRelationalTheories.pdf`, which says `f` is a map exactly when it has a right
adjoint, and that adjoint is `f°`.

#canvas({
  d.content((-0.75, 0), $arrow.l.r.double$)
  chain((0, 0.8), ($R$, $f$)); d.content((3.25, 0.8), $subset.sq.eq$); chain((3.65, 0.8), ($S$,))
  chain((1.26, -0.8), ($R$,)); d.content((3.25, -0.8), $subset.sq.eq$)
  chain((3.65, -0.8), ($S$, $f^degree$))
})
#cap-below[`map_shunt_right`: for a map `f`, `R ≫ f ⊑ S ↔ R ⊑ S ≫ f°`]

#v(6pt)

#canvas({
  d.content((-0.75, 0), $arrow.l.r.double$)
  chain((0, 0.8), ($f^degree$, $R$)); d.content((3.25, 0.8), $subset.sq.eq$)
  chain((3.65, 0.8), ($S$,))
  chain((1.26, -0.8), ($R$,)); d.content((3.25, -0.8), $subset.sq.eq$)
  chain((3.65, -0.8), ($f$, $S$))
})
#cap-below[`map_shunt_left`: for a map `f`, `f° ≫ R ⊑ S ↔ R ⊑ f ≫ S`]

= 2. The map dictionary — `Entire`, `Simple`, `Map`

`Freyd/S2_10.lean` §2.13 defines `Simple R := R° ≫ R ⊑ 𝟙` and `Entire R := dom R = 𝟙`, the latter
equivalent to `𝟙 ⊑ R ≫ R°`; a `Map` is both. These are inequations (46) and (47) of Lemma 4.4,
p. 20, where the paper calls them single-valued and total.

#canvas({
  chain((0, 0.8), ($R^degree$, $R$)); d.content((3.25, 0.8), $subset.sq.eq$)
  wire((3.65, 0.8), (5.25, 0.8))
  wire((1.26, -0.8), (2.86, -0.8)); d.content((3.25, -0.8), $subset.sq.eq$)
  chain((3.65, -0.8), ($R$, $R^degree$))
  note((7.1, 0.8), [(46) `Simple` — single valued])
  note((7.1, -0.8), [(47) `Entire` — total])
})

The same two conditions read off the Frobenius structure instead. Every arrow is only a *lax*
comonoid homomorphism — that is eq. (3), p. 4, the `lax_cop` and `lax_dis` fields — and a map is
precisely an arrow for which those two inequations are equalities.

#canvas({
  // R ; Δ  =  Δ ; (R ⊗ R)
  wire((0, 0.9), (0.34, 0.9)); gbox((0.34, 0.9), $R$)
  copy((1.56, 0.9), li: 0.3, lo: 0.5, sp: 0.55)
  wire((2.06, 1.45), (2.4, 1.45)); wire((2.06, 0.35), (2.4, 0.35))
  d.content((2.85, 0.9), $=$)
  copy((3.4, 0.9), li: 0.4, lo: 0.3, sp: 0.55)
  gbox((3.7, 1.45), $R$); gbox((3.7, 0.35), $R$)
  wire((4.62, 1.45), (4.96, 1.45)); wire((4.62, 0.35), (4.96, 0.35))
  note((5.5, 0.9), [`Simple` again: `R ≫ Δ = Δ ≫ (R ⊗ R)`])
  // R ; !  =  !
  wire((0, -0.9), (0.34, -0.9)); gbox((0.34, -0.9), $R$)
  discard((1.76, -0.9), li: 0.5)
  d.content((2.85, -0.9), $=$)
  discard((3.9, -0.9), li: 1.0)
  note((5.5, -0.9), [`Entire` again: `R ≫ ! = !`])
})

= 3. Simple relations distribute over the meet — `simple_dist_inter`

`Freyd/S2_10.lean` §2.136: if `F` is simple then `F ≫ (R ∩ S) = (F ≫ R) ∩ (F ≫ S)`. The `⊑`
direction of this is eq. (3) on p. 4 — it holds for every arrow, because `F` can always be copied
early rather than late. Simplicity is exactly what tightens it to an equality, which is why this is
the engine of §2.141 below.

#canvas({
  wire((0, 0), (0.34, 0)); gbox((0.34, 0), $F$)
  meet((1.66, 0), $R$, $S$, sp: 0.62)
  d.content((4.0, 0), $=$)
  copy((4.4, 0), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((4.7, 0.62), $F$); gbox((5.92, 0.62), $R$); wire((5.62, 0.62), (5.92, 0.62))
  gbox((4.7, -0.62), $F$); gbox((5.92, -0.62), $S$); wire((5.62, -0.62), (5.92, -0.62))
  merge((7.14, 0), li: 0.3, lo: 0.4, sp: 0.62)
})

= 4. The modular law — `modular_le`, `modular_le_right`, `modular_sym`

The one axiom of an allegory that is not a lattice law (`Freyd/S2_10.lean` §2.11, order form
`modular_le`). Its two one-sided halves are `modular_le_right` (`AOP/A4_1.lean`), and B&dM 4.8's
symmetric form `modular_sym` is visibly the two halves applied at once.

#canvas({
  let lhs(y) = {
    copy((0, y), li: 0.4, lo: 0.3, sp: 0.62)
    gbox((0.3, y + 0.62), $R$); wire((1.22, y + 0.62), (1.52, y + 0.62))
    gbox((1.52, y + 0.62), $S$)
    gbox((0.3, y - 0.62), $T$); wire((1.22, y - 0.62), (2.44, y - 0.62))
    merge((2.74, y), li: 0.3, lo: 0.4, sp: 0.62)
    d.content((3.5, y), $subset.sq.eq$)
  }
  // (R S) ∩ T ⊑ (R ∩ T S°) S
  lhs(1.9)
  copy((3.9, 1.9), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((4.2, 2.52), $R$); wire((5.12, 2.52), (6.34, 2.52))
  gbox((4.2, 1.28), $T$); wire((5.12, 1.28), (5.42, 1.28)); gbox((5.42, 1.28), $S^degree$)
  merge((6.64, 1.9), li: 0.3, lo: 0.3, sp: 0.62)
  gbox((6.94, 1.9), $S$); wire((7.86, 1.9), (8.2, 1.9))
  // (R S) ∩ T ⊑ R (S ∩ R° T)
  lhs(0)
  wire((3.9, 0), (4.24, 0)); gbox((4.24, 0), $R$)
  copy((5.46, 0), li: 0.3, lo: 0.3, sp: 0.62)
  gbox((5.76, 0.62), $S$); wire((6.68, 0.62), (7.9, 0.62))
  gbox((5.76, -0.62), $R^degree$); wire((6.68, -0.62), (6.98, -0.62)); gbox((6.98, -0.62), $T$)
  merge((8.2, 0), li: 0.3, lo: 0.4, sp: 0.62)
  // (R S) ∩ T ⊑ (R ∩ T S°) (S ∩ R° T)
  lhs(-1.9)
  copy((3.9, -1.9), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((4.2, -1.28), $R$); wire((5.12, -1.28), (6.34, -1.28))
  gbox((4.2, -2.52), $T$); wire((5.12, -2.52), (5.42, -2.52)); gbox((5.42, -2.52), $S^degree$)
  merge((6.64, -1.9), li: 0.3, lo: 0.3, sp: 0.62)
  copy((6.94, -1.9), li: 0.0, lo: 0.3, sp: 0.62)
  gbox((7.24, -1.28), $S$); wire((8.16, -1.28), (9.38, -1.28))
  gbox((7.24, -2.52), $R^degree$); wire((8.16, -2.52), (8.46, -2.52)); gbox((8.46, -2.52), $T$)
  merge((9.68, -1.9), li: 0.3, lo: 0.4, sp: 0.62)
  d.content((10.9, 1.9), text(8.5pt)[`modular_le`])
  d.content((10.9, 0), text(8.5pt)[`modular_le_right`])
  d.content((10.9, -1.9), text(8.5pt)[`modular_sym`])
})

= 5. Domain — `dom`, `dom_UP`

A relation `X : a ⟶ a` is *coreflexive* when `X ⊑ 𝟙`: a wire that filters and does nothing else.

#canvas({
  chain((0, 0), ($X$,)); d.content((1.95, 0), $subset.sq.eq$); wire((2.35, 0), (3.95, 0))
  d.content((5.0, 0), text(8.5pt)[`Coreflexive X`])
})

`dom R` (`Freyd/S2_10.lean` §2.122) is the coreflexive `𝟙 ∩ R ≫ R°` — go out along `R` and come
back, and keep only the inputs for which that round trip returns. The identity strand of the meet
is drawn as what it is, a bare wire.

#canvas({
  d.content((-1.1, 0), $"dom" R :=$)
  copy((0, 0), li: 0.4, lo: 0.3, sp: 0.62)
  wire((0.3, 0.62), (2.44, 0.62))
  gbox((0.3, -0.62), $R$); wire((1.22, -0.62), (1.52, -0.62)); gbox((1.52, -0.62), $R^degree$)
  merge((2.74, 0), li: 0.3, lo: 0.4, sp: 0.62)
})

Its universal property, `dom_UP` (`AOP/A4_2.lean`, B&dM 4.11): among coreflexives, `dom R` is the
least one that `R` factors through.

#canvas({
  d.content((-0.75, 0), $arrow.l.r.double$)
  chain((0, 0.8), ($"dom" R$,), w: 1.35); d.content((2.5, 0.8), $subset.sq.eq$)
  chain((2.9, 0.8), ($X$,))
  chain((0.43, -0.8), ($R$,)); d.content((2.5, -0.8), $subset.sq.eq$)
  chain((2.9, -0.8), ($X$, $R$))
})
#cap-below[`dom_UP`: for coreflexive `X`, `dom R ⊑ X ↔ R ⊑ X ≫ R`]

= 6. Tabulations — `Tabulates`, `tabulates_monic_pair`

`Freyd/S2_10.lean` §2.14: maps `f : c ⟶ a` and `g : c ⟶ b` *tabulate* `R : a ⟶ b` when
`R = f° ≫ g` and `f ≫ f° ∩ g ≫ g° = 𝟙`. The first equation says the span computes `R`; the second
says the span is *jointly monic* — nothing collapses.

#canvas({
  chain((0, 0), ($R$,)); d.content((1.95, 0), $=$); chain((2.35, 0), ($f^degree$, $g$))
  copy((6.4, 0), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((6.7, 0.62), $f$); wire((7.62, 0.62), (7.92, 0.62)); gbox((7.92, 0.62), $f^degree$)
  gbox((6.7, -0.62), $g$); wire((7.62, -0.62), (7.92, -0.62)); gbox((7.92, -0.62), $g^degree$)
  merge((9.14, 0), li: 0.3, lo: 0.4, sp: 0.62)
  d.content((10.0, 0), $=$)
  wire((10.4, 0), (12.0, 0))
})

§2.141, `tabulates_monic_pair`: that second equation makes `(f, g)` a monic pair in `Map(𝒜)`. The
proof is one rewrite — push a map `h` through the meet, which is legal by `simple_dist_inter`
above, since every map is simple.

#canvas({
  wire((0, 0), (0.34, 0)); gbox((0.34, 0), $h$)
  copy((1.66, 0), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((1.96, 0.62), $f$); wire((2.88, 0.62), (3.18, 0.62)); gbox((3.18, 0.62), $f^degree$)
  gbox((1.96, -0.62), $g$); wire((2.88, -0.62), (3.18, -0.62)); gbox((3.18, -0.62), $g^degree$)
  merge((4.4, 0), li: 0.3, lo: 0.4, sp: 0.62)
  d.content((5.2, 0), $=$)
  copy((5.6, 0), li: 0.4, lo: 0.3, sp: 0.62)
  gbox((5.9, 0.62), $h$); wire((6.82, 0.62), (7.12, 0.62)); gbox((7.12, 0.62), $f$)
  wire((8.04, 0.62), (8.34, 0.62)); gbox((8.34, 0.62), $f^degree$)
  gbox((5.9, -0.62), $h$); wire((6.82, -0.62), (7.12, -0.62)); gbox((7.12, -0.62), $g$)
  wire((8.04, -0.62), (8.34, -0.62)); gbox((8.34, -0.62), $g^degree$)
  merge((9.56, 0), li: 0.3, lo: 0.4, sp: 0.62)
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
  d.content((-0.75, 0), $arrow.l.r.double$)
  chain((0.43, 0.8), ($T$,)); d.content((2.5, 0.8), $subset.sq.eq$)
  chain((2.9, 0.8), ($R slash S$,), w: 1.3, dashed: (0,))
  chain((0, -0.8), ($T$, $S$)); d.content((2.5, -0.8), $subset.sq.eq$)
  chain((2.9, -0.8), ($R$,))
})
#cap-below[`le_div_iff`: `T ⊑ R / S ↔ T ≫ S ⊑ R`]

Taking `T := R / S` in the right-to-left direction gives the semi-commutative triangle that defines
division, `div_comp_le`:

#canvas({
  chain((0, 0), ($R slash S$, $S$), w: 1.3, dashed: (0,))
  d.content((3.6, 0), $subset.sq.eq$)
  chain((4.0, 0), ($R$,))
})
