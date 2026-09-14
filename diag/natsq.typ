// natsq.typ — WHY A SINGLE F-ALGEBRA IS NOT A NATURAL TRANSFORMATION `F ⇒ 1`.
//
// `F X = X × X` on sets, and addition `+ : ℕ × ℕ ⟶ ℕ` is an F-algebra on `ℕ`.  For it to be the
// `ℕ` component of some `θ : F ⇒ 1` the square below would have to commute at EVERY arrow; it
// already fails at the constant `g : 𝟏 ⟶ ℕ`, `• ↦ 1`.  `𝟏` has one element, so whatever `θ_𝟏` is,
// the lower path can only come back as `g • = 1`, while the upper path adds and gets `2`.
//
// The picture is the naturality square, not the algebra square: the two verticals are components
// of the SAME would-be `θ`, which is exactly the demand a single algebra does not meet.
// Machine-checked as `addAlg_not_natural`, over the repository's own `Functor` and `setCat`.
//
// typst compile --root . --format png --ppi 220 diag/natsq.typ diag/natsq.png
#import "circuit.typ": cetz, d

#set page(width: auto, height: auto, margin: 0.8cm, fill: white)

// ONE COLOUR PER PATH, because the whole content is that the two paths disagree: the upper route
// through `F g` and `+`, the lower through `θ_𝟏` and `g`.  Values carried along a route wear its
// colour, so the `2` and the `1` at the bottom right are read off without tracing the arrows.
#let UP = rgb("#26734d")
#let LO = rgb("#7d3c98")
#let VAL = luma(110)

#let ar(a, b, col, s0: 0.55, s1: 0.55) = {
  let (dx, dy) = (b.at(0) - a.at(0), b.at(1) - a.at(1))
  let n = calc.sqrt(dx * dx + dy * dy)
  d.line((a.at(0) + s0 / n * dx, a.at(1) + s0 / n * dy),
    (b.at(0) - s1 / n * dx, b.at(1) - s1 / n * dy),
    mark: (end: ">", scale: 0.5), stroke: (thickness: 0.75pt, paint: col))
}
#let lab(x, y, col, w) = d.content((x, y), text(10pt, col)[#w])
#let node(x, y, w) = d.content((x, y), box(inset: 4pt, fill: white)[#text(10pt)[#w]])

#align(center, cetz.canvas(length: 0.9cm, {
  let (TL, TR, BL, BR) = ((-3.2, 1.3), (3.2, 1.3), (-3.2, -1.3), (3.2, -1.3))
  ar(TL, TR, UP); ar(TR, BR, UP)
  ar(TL, BL, LO); ar(BL, BR, LO)
  node(TL.at(0), TL.at(1), `𝟏 × 𝟏`); node(TR.at(0), TR.at(1), `ℕ × ℕ`)
  node(BL.at(0), BL.at(1), `𝟏`); node(BR.at(0), BR.at(1), `ℕ`)
  lab(0, 1.75, UP)[`F g = g × g`]; lab(4.0, 0, UP)[`+`]
  lab(-3.9, 0, LO)[θ#sub[`𝟏`]]; lab(0, -1.75, LO)[`g`]
  // The element trace: one element goes in at the top left and comes out as two numbers.
  lab(-3.2, 2.05, VAL)[`(•, •)`]; lab(3.2, 2.05, VAL)[`(1, 1)`]
  lab(-3.2, -2.05, VAL)[`•`]
  lab(3.6, -2.05, UP)[`2`]; lab(4.35, -2.05, VAL)[`≠`]; lab(5.0, -2.05, LO)[`1`]
}))

#align(center, box(width: 14cm, text(10.5pt)[
  `g` is the constant `1`, and `𝟏` has one element, so whichever component is chosen at `𝟏` the
  lower path can only come back as `1` — while the upper path adds and gets `2`.
]))
