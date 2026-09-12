// cdref-horner.typ — the note's OWN triangle, standing alone, so `scripts/svg-diff` can hold the
// generated panel to it.  This is the picture of `diag/allegory-axioms.typ`'s `<horner>` copied mark
// for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `Freyd.Alg.tri_cata_fusion` IS Horner's rule — `tri(f)⦇g⦈=⦇F(𝟙,f)g⦈` under `gf=F(f,f)g` — so its
// generated panel must be this picture up to the letters and up to colour.
//
//   typst compile --root . --format svg diag/cdref-horner.typ diag/cdref-horner.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (TL, TR, A) = ((-2.2, 1.25), (2.2, 1.25), (0, -1.25))
  ar(TL, TR, GIVEN2, s0: 0.6, s1: 0.6)
  ar(TL, A, INDUCED, dash: "dashed", s0: 0.6, s1: 0.6)
  ar(TR, A, INDUCED, dash: "dashed", s0: 0.6, s1: 0.6)
  lab(0, 1.8, GIVEN2)[`tri(f)`]
  lab(-3.1, -0.35, INDUCED)[`⦇F(𝟙,f)g⦈`]; lab(2.0, -0.35, INDUCED)[`⦇g⦈`]
  node(TL.at(0), TL.at(1), black, `TA`); node(TR.at(0), TR.at(1), black, `TA`)
  node(A.at(0), A.at(1), GIVEN1, `A`)
})
