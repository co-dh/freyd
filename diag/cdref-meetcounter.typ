// cdref-meetcounter.typ — the note's OWN square, standing alone, so `scripts/cd-check` can hold the
// generated panel to it.  This is the canvas of `diag/ch/13-optimisation.typ`'s `<meet-counterex>`
// as the author drew it, copied mark for mark: same `ar`/`node`/`lab`, same corners, same
// `length: 0.9cm`.  `∩` is ONE bead on the square and the face carries `⋢`.
//
//   typst compile --root . diag/cdref-meetcounter.typ diag/cdref-meetcounter.svg
#import "draw.typ": GIVEN1, GIVEN2, TCOL, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.9cm, {
  let (TL, TR, BL, BR) = ((-3.4, 1.3), (3.4, 1.3), (-3.4, -1.3), (3.4, -1.3))
  ar(TL, TR, GIVEN1, s0: 0.75, s1: 0.55); ar(TR, BR, GIVEN1, s0: 0.5, s1: 0.5)
  ar(TL, BL, GIVEN2, s0: 0.5, s1: 0.5); ar(BL, BR, GIVEN2, s0: 0.75, s1: 0.55)
  lab(0, 1.75, GIVEN1)[`π₁∩π₂`]; lab(3.95, 0, GIVEN1)[`R`]
  lab(-4.15, 0, GIVEN2)[`R×R`]; lab(0, -1.75, GIVEN2)[`π₁∩π₂`]
  lab(0, 0, TCOL, rot: -45deg)[$subset.eq.sq.not$]
  node(TL.at(0), TL.at(1), black, `A×A`); node(TR.at(0), TR.at(1), black, `A`)
  node(BL.at(0), BL.at(1), black, `B×B`); node(BR.at(0), BR.at(1), black, `B`)
  // THE TRACE, back at the corners it belongs to: the statement pins each value and names the edge
  // that carried it (`inter_not_laxNatural_square`), so the panel stands them under the corners and
  // this drawing does too.  Each wears its route's colour, and `(0,1)`, which both routes leave, is
  // black; the corner `B` carries the two routes' two answers.
  lab(TL.at(0), TL.at(1) - 0.62, black)[`(0,1)`]
  lab(BL.at(0), BL.at(1) - 0.62, GIVEN2)[`(0,0)`]
  lab(TR.at(0), TR.at(1) - 0.62, GIVEN1)[`∅`]
  lab(BR.at(0), BR.at(1) - 0.62, GIVEN2)[`{0}`]
  lab(BR.at(0), BR.at(1) - 1.12, GIVEN1)[`∅`]
})
