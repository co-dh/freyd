// cdref-catadef.typ — the note's OWN square, standing alone, so `scripts/svg-diff` can hold the
// generated panel to it.  This is the picture of `diag/allegory-axioms.typ`'s `<cata-defining>`
// copied mark for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `Freyd.Alg.relCata_UP` is the defining property `αX=F(X)f ⟺ X=⦇f⦈`, and the square is its `.lhs`
// side — `X` dashed because the OTHER side says the property produces it.
//
//   typst compile --root . --format svg diag/cdref-catadef.typ diag/cdref-catadef.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  // The same 5.2 × 2.7 square as @cata-map-square's top row, so the two pictures overlay.
  let (FT, T, FA, A) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
  ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FA, A, GIVEN1, s0: 0.55, s1: 0.55)
  ar(FT, FA, INDUCED, s0: 0.55, s1: 0.55)
  ar(T, A, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  lab(0, 1.9, GIVEN2)[`α`]; lab(0, -1.9, GIVEN1)[`f`]
  lab(-4.0, 0, INDUCED)[`F(X)`]; lab(3.6, 0, INDUCED)[`X`]
  node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
  node(FA.at(0), FA.at(1), GIVEN1, `FA`); node(A.at(0), A.at(1), GIVEN1, `A`)
})
