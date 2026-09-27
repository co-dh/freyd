// cdref-hfix.typ — the square the author asked for under `<dp-laws>`, standing alone, so
// `scripts/cd-check` can hold the generated panel of `Freyd.Alg.H_fixed` to it.  His words:
// "`T° : A → F(A)`, then `F(H)`, then `h`, equal to `H`" — `T°F(H)h=H` — "drawn as a square with
// `H` on left": the three-arrow path round the top, right and bottom, `H` the left side.  `H` is
// solid: it is named by its definition `⦇T⦈°⦇h⦈`, not produced by a uniqueness, and `T°` is a relation.
//
//   typst compile --root . diag/cdref-hfix.typ diag/cdref-hfix.svg
//   ./scripts/diag-export --commutative Freyd.Alg.H_fixed
#import "draw.typ": GIVEN1, GIVEN2, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (A, FA) = ((-3, 2.5), (3, 2.5))
  let (B, FB) = ((-3, -2.5), (3, -2.5))
  ar(A, FA, GIVEN1, s0: 0.55, s1: 0.65)
  ar(FA, FB, GIVEN2, s0: 0.55, s1: 0.55)
  ar(FB, B, GIVEN1, s0: 0.65, s1: 0.55)
  ar(A, B, GIVEN2, s0: 0.55, s1: 0.55)
  lab(0, 3.05, GIVEN1)[`T°`]
  lab(3.8, 0, GIVEN2)[`F(H)`]
  lab(0, -3.05, GIVEN1)[`h`]
  lab(-3.5, 0, GIVEN2)[`H`]
  node(A.at(0), A.at(1), black, `A`); node(FA.at(0), FA.at(1), black, `FA`)
  node(FB.at(0), FB.at(1), black, `FB`); node(B.at(0), B.at(1), black, `B`)
})
