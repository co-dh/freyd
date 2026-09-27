// cdref-thincond.typ — the square the author asked for under `<dp-laws>`, standing alone, so
// `scripts/cd-check` can hold the generated panel of `Freyd.Alg.ThinCondition` to it.  His words:
// "top `Q`, right `F(H)h`, left `F(H)h`, bottom `R`, the 2-cell `⊑`" — `QF(H)h⊑F(H)hR`, the
// composite `F(H)h` opened through `FB` on both sides because the statement composes it there.
//
//   typst compile --root . diag/cdref-thincond.typ diag/cdref-thincond.svg
//   ./scripts/diag-export --commutative Freyd.Alg.ThinCondition
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (LA, RA) = ((-3, 2.5), (3, 2.5))
  let (LF, RF) = ((-3, 0), (3, 0))
  let (LB, RB) = ((-3, -2.5), (3, -2.5))
  ar(LA, RA, GIVEN1, s0: 0.65, s1: 0.65)
  ar(RA, RF, GIVEN2, s0: 0.55, s1: 0.55); ar(RF, RB, GIVEN1, s0: 0.55, s1: 0.55)
  ar(LA, LF, GIVEN2, s0: 0.55, s1: 0.55); ar(LF, LB, GIVEN1, s0: 0.55, s1: 0.55)
  ar(LB, RB, GIVEN1, s0: 0.65, s1: 0.65)
  lab(0, 3.05, GIVEN1)[`Q`]; lab(0, -1.95, GIVEN1)[`R`]
  lab(3.8, 1.25, GIVEN2)[`F(H)`]; lab(3.5, -1.25, GIVEN1)[`h`]
  lab(-3.8, 1.25, GIVEN2)[`F(H)`]; lab(-3.5, -1.25, GIVEN1)[`h`]
  lab(0, 0, SLACK)[`⊑`]
  node(LA.at(0), LA.at(1), black, `FA`); node(RA.at(0), RA.at(1), black, `FA`)
  node(LF.at(0), LF.at(1), black, `FB`); node(RF.at(0), RF.at(1), black, `FB`)
  node(LB.at(0), LB.at(1), GIVEN1, `B`); node(RB.at(0), RB.at(1), GIVEN1, `B`)
})
