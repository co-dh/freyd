// cdref-tfun.typ — the note's OWN picture of type-functor fusion, standing alone, so
// `scripts/svg-check` can hold the generated panel to it.  This is the picture of
// `diag/allegory-axioms.typ`'s `<tfun-fusion>` copied mark for mark: same `ar`/`node`/`lab`, same
// corners, same `length: 0.8cm`.  `Freyd.Alg.typeMap_fusion_cancel` states the fold's defining
// square at the fused algebra AND the fusion triangle, and the two are pasted along the fold they
// share; `F(f,𝟙)h` is the ALGEBRA that fold is taken over, so it is ONE edge and the picture has no
// corner between `F(f,𝟙)` and `h`.
//
//   typst compile --root . --format svg diag/cdref-tfun.typ diag/cdref-tfun.svg
//   ./scripts/diag-export --commutative Freyd.Alg.typeMap_fusion_cancel
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (TA, FA, FC) = ((-4.2, 1.4), (0, 1.4), (4.2, 1.4))
  let (TB, C) = ((-4.2, -1.4), (4.2, -1.4))
  ar(FA, TA, GIVEN2, s0: 1.45, s1: 0.65); ar(FA, FC, INDUCED, s0: 1.45, s1: 1.45)
  ar(FC, C, GIVEN1, s0: 0.6, s1: 0.55)
  ar(TA, TB, GIVEN2, s0: 0.6, s1: 0.6)
  ar(TB, C, INDUCED, dash: "dashed", s0: 0.6, s1: 0.55)
  ar(TA, C, INDUCED, dash: "dashed", s0: 0.75, s1: 0.75)
  lab(-2.1, 1.95, GIVEN2)[`α`]; lab(2.1, 1.95, INDUCED)[`F(𝟙,⦇F(f,𝟙)h⦈)`]
  lab(5.35, 0, GIVEN1)[`F(f,𝟙)h`]; lab(-5.0, 0, GIVEN2)[`T(f)`]
  lab(0, -1.95, INDUCED)[`⦇h⦈`]; lab(0.9, 0.55, INDUCED)[`⦇F(f,𝟙)h⦈`]
  node(TA.at(0), TA.at(1), black, `TA`); node(FA.at(0), FA.at(1), black, `F(A,TA)`)
  node(FC.at(0), FC.at(1), black, `F(A,C)`)
  node(TB.at(0), TB.at(1), black, `TB`); node(C.at(0), C.at(1), GIVEN1, `C`)
})
