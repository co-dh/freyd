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
  // The trace: `(0,1)` in at the top left, out as `{0}` down-then-across and as `∅` the other way.
  lab(-3.4, 2.1, luma(110))[`(0,1)`]; lab(3.4, 2.1, GIVEN1)[`∅`]
  lab(-3.4, -2.1, GIVEN2)[`(0,0)`]
  lab(2.85, -2.1, GIVEN2)[`{0}`]; lab(3.6, -2.1, TCOL)[$subset.eq.sq.not$]
  lab(4.25, -2.1, GIVEN1)[`∅`]
})
