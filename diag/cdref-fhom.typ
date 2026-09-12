// cdref-fhom.typ — the note's OWN F-homomorphism square, standing alone, so `scripts/svg-check
// --against` can hold the generated panel to it.  This is the first `#pair` of
// `diag/allegory-axioms.typ`'s `<initial-defn>` — `f h=F(h)g` — copied mark for mark: same
// `ar`/`node`/`lab`, same corners, same `length: 0.8cm`, and the same ONE HUE per object the note
// gives the display (`A` amber in both of its rows).  `Freyd.Alg.IsFHom` IS that property.
//
//   typst compile --root . --format svg diag/cdref-fhom.typ diag/cdref-fhom.svg
//   ./scripts/diag-export --commutative Freyd.Alg.IsFHom
#import "draw.typ": GIVEN1, GIVEN2, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FA, A, FB, B) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
  ar(FA, A, GIVEN2, s0: 0.55, s1: 0.55); ar(FB, B, GIVEN1, s0: 0.55, s1: 0.55)
  ar(FA, FB, black, s0: 0.55, s1: 0.55); ar(A, B, black, s0: 0.55, s1: 0.55)
  lab(0, 1.9, GIVEN2)[`f`]; lab(0, -1.9, GIVEN1)[`g`]
  lab(-3.55, 0, black)[`F(h)`]; lab(3.2, 0, black)[`h`]
  node(FA.at(0), FA.at(1), black, `FA`); node(A.at(0), A.at(1), black, `A`)
  node(FB.at(0), FB.at(1), GIVEN1, `FB`); node(B.at(0), B.at(1), GIVEN1, `B`)
})
