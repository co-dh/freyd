// cdref-fusion.typ — the note's OWN two stacked squares, standing alone, so `scripts/svg-check` can
// hold the generated panel to them.  This is the picture of `diag/allegory-axioms.typ`'s
// `<cata-fusion>` copied mark for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `Freyd.Alg.relCata_fusion` IS (2.12) — `⦇R⦈S=⦇Q⦈⟸RS=F(S)Q` — and its generated panel is the
// fold's defining square (`relCata_cancel`) pasted onto the side condition along the chord `R`.
//
//   typst compile --root . --format svg diag/cdref-fusion.typ diag/cdref-fusion.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FT, T) = ((-2.6, 2.5), (2.6, 2.5))
  let (FB, B) = ((-2.6, 0), (2.6, 0))
  let (FC, C) = ((-2.6, -2.5), (2.6, -2.5))
  ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.55, s1: 0.55)
  ar(FC, C, GIVEN1, s0: 0.55, s1: 0.55)
  ar(FT, FB, INDUCED, s0: 0.55, s1: 0.55)
  ar(FB, FC, GIVEN2, s0: 0.55, s1: 0.55)
  ar(T, B, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  ar(B, C, GIVEN2, s0: 0.55, s1: 0.55)
  lab(-3.95, 1.25, INDUCED)[`F(⦇R⦈)`]; lab(3.45, 1.25, INDUCED)[`⦇R⦈`]
  lab(-3.55, -1.25, GIVEN2)[`F(S)`]; lab(3.1, -1.25, GIVEN2)[`S`]
  lab(0, 3.05, GIVEN2)[`α`]; lab(0, 0.55, GIVEN1)[`R`]; lab(0, -1.95, GIVEN1)[`Q`]
  node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
  node(FB.at(0), FB.at(1), black, `FB`); node(B.at(0), B.at(1), black, `B`)
  node(FC.at(0), FC.at(1), black, `FC`); node(C.at(0), C.at(1), black, `C`)
})
