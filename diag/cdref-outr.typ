// cdref-outr.typ — the note's OWN `subseq-outr-square`, standing alone, so `scripts/svg-check
// --against` can hold the generated panel to it.  This is the canvas of
// `diag/allegory-axioms.typ`'s `<subseq-outr-square>` — `(𝟙×∋)π₂=π₂∋` — copied mark for mark: same
// `ar`/`node`/`lab`, same corners, same `length: 0.8cm`, and no `⊑`, the square commuting on the
// nose.  `Freyd.Alg.RelSet.ListRel.prod_ni_proj_slide` IS that equation.
//
//   typst compile --root . --format svg diag/cdref-outr.typ diag/cdref-outr.svg
//   ./scripts/diag-export --commutative Freyd.Alg.RelSet.ListRel.prod_ni_proj_slide
#import "draw.typ": GIVEN1, GIVEN2, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (AE, E, AL, L) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
  ar(AE, E, GIVEN2, s0: 1.55, s1: 1.05); ar(AL, L, GIVEN2, s0: 1.2, s1: 0.7)
  ar(AE, AL, GIVEN1, s0: 0.55, s1: 0.55); ar(E, L, GIVEN1, s0: 0.55, s1: 0.55)
  lab(0, 1.9, GIVEN2)[`π₂`]; lab(0, -1.9, GIVEN2)[`π₂`]
  lab(-3.95, 0, GIVEN1)[`𝟙×∋`]; lab(3.2, 0, GIVEN1)[`∋`]
  node(AE.at(0), AE.at(1), black, `A×E[A]`); node(E.at(0), E.at(1), black, `E[A]`)
  node(AL.at(0), AL.at(1), black, `A×[A]`); node(L.at(0), L.at(1), black, `[A]`)
})
