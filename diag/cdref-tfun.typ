// cdref-tfun.typ — the note's OWN picture of type-functor fusion, standing alone, so
// `scripts/cd-check` can hold the generated panel to it.  This is the picture of
// `diag/allegory-axioms.typ`'s `<tfun-fusion>` copied mark for mark: same `ar`/`node`/`lab`, same
// corners, same `length: 0.8cm`.  `Freyd.Alg.typeMap_fusion_cancel` states the fold's defining
// square at the fused algebra AND the fusion triangle; the square is drawn straight and the
// triangle bows OUT through `TB` beyond the edge the two share, which is drawn once.  `F(f,𝟙)h` is
// the ALGEBRA that fold is taken over and nothing names `F(B,C)`, so it is ONE edge.
//
//   typst compile --root . diag/cdref-tfun.typ diag/cdref-tfun.svg
//   ./scripts/diag-export --commutative Freyd.Alg.typeMap_fusion_cancel
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FA, TA) = ((-3, 2.0), (3, 2.0))
  let TB = (5.6, 0)
  let (FC, C) = ((-3, -2.0), (3, -2.0))
  ar(FA, TA, GIVEN2, s0: 1.45, s1: 0.65); ar(FC, C, GIVEN1, s0: 1.45, s1: 0.5)
  ar(FA, FC, INDUCED, s0: 0.55, s1: 0.55)
  ar(TA, C, INDUCED, dash: "dashed", s0: 0.55, s1: 0.5)
  ar(TA, TB, INDUCED, dash: "dashed", s0: 0.55, s1: 0.6)
  ar(TB, C, INDUCED, dash: "dashed", s0: 0.6, s1: 0.55)
  lab(0.4, 2.55, GIVEN2)[`α`#sub[`A`]]; lab(0.4, -2.55, GIVEN1)[`F(f,𝟙)h`]
  lab(-5.15, 0, INDUCED)[`F(𝟙,⦇F(f,𝟙)h⦈)`]; lab(1.25, 0, INDUCED)[`⦇F(f,𝟙)h⦈`]
  lab(4.67, 1.47, INDUCED)[`T(f)`]; lab(4.67, -1.47, INDUCED)[`⦇h⦈`]
  node(FA.at(0), FA.at(1), black, `F(A,TA)`); node(TA.at(0), TA.at(1), black, `TA`)
  node(TB.at(0), TB.at(1), black, `TB`)
  node(FC.at(0), FC.at(1), GIVEN1, `F(A,C)`); node(C.at(0), C.at(1), GIVEN1, `C`)
})
