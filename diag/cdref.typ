// cdref.typ — the note's OWN square, standing alone, so `scripts/svg-diff` can hold a generated
// commutative diagram to it.  This is the second `#pair` of `diag/allegory-axioms.typ`'s
// `<initial-defn>` — `α⦇f⦈=F(⦇f⦈)f` — copied mark for mark: same `ar`/`node`/`lab`, same corners,
// same `length: 0.8cm`.  `Freyd.Alg.relCata_cancel` IS that law, so its generated panel must be
// this picture up to the letters (the note writes `f` where Lean binds `R`, `A` where it binds `c`)
// and up to colour, which svg-diff reports as glyphs and ink rather than as geometry.
//
//   typst compile --root . --format svg diag/cdref.typ diag/cdref.svg
//   ./scripts/diag-export --commutative Freyd.Alg.relCata_cancel
//   typst compile --root . --format svg diag/generated/commutative/Freyd.Alg.relCata_cancel.typ x.svg
//   ./scripts/svg-diff diag/cdref.svg x.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FT, T, FA, A) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
  ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FA, A, GIVEN1, s0: 0.55, s1: 0.55)
  ar(FT, FA, INDUCED, s0: 0.55, s1: 0.55)
  ar(T, A, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  lab(0, 1.9, GIVEN2)[`α`]; lab(0, -1.9, GIVEN1)[`f`]
  lab(-3.95, 0, INDUCED)[`F(⦇f⦈)`]; lab(3.45, 0, INDUCED)[`⦇f⦈`]
  node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
  node(FA.at(0), FA.at(1), GIVEN1, `FA`); node(A.at(0), A.at(1), GIVEN1, `A`)
})
