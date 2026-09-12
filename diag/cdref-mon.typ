// cdref-mon.typ — the note's OWN lax square, standing alone, so `scripts/svg-check --against` can
// hold the generated panel to it.  This is the first `#pair` of `diag/allegory-axioms.typ`'s
// `<mon-str>` — `F(R)φ⊑φR` — copied mark for mark: same `ar`/`node`/`lab`, same corners, same
// `length: 0.8cm`.  `Freyd.Alg.MonotonicAlg` IS that property, so its generated panel must be this
// picture: the transported `F(R)`/`R` hanging on the verticals and the algebra `φ` across.
//
//   typst compile --root . --format svg diag/cdref-mon.typ diag/cdref-mon.svg
//   ./scripts/diag-export --commutative Freyd.Alg.MonotonicAlg
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FT, T, FB, B) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
  ar(FT, T, GIVEN1, s0: 0.75, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.75, s1: 0.55)
  ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55); ar(T, B, GIVEN2, s0: 0.55, s1: 0.55)
  lab(0, 1.8, GIVEN1)[`φ`]; lab(0, -1.8, GIVEN1)[`φ`]
  lab(-3.75, 0, GIVEN2)[`F(R)`]; lab(3.35, 0, GIVEN2)[`R`]
  lab(0, 0, SLACK, rot: -45deg)[`⊑`]
  node(FT.at(0), FT.at(1), black, `FA`); node(T.at(0), T.at(1), black, `A`)
  node(FB.at(0), FB.at(1), black, `FA`); node(B.at(0), B.at(1), black, `A`)
})
