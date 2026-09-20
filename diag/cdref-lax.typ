// cdref-lax.typ — the note's OWN lax-naturality square, standing alone, so `scripts/svg-check
// --against` can hold the generated panel to it.  This is the first `#pair` of
// `diag/allegory-axioms.typ`'s `<lax-str>` — `G(R)φʙ⊑φᴀF(R)` — copied mark for mark: same
// `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.  `Freyd.Alg.LaxNatural` IS that property.
//
//   typst compile --root . --format svg diag/cdref-lax.typ diag/cdref-lax.svg
//   ./scripts/diag-export --commutative Freyd.Alg.LaxNatural
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (GT, FT, GB, FB) = ((-3, 1.25), (3, 1.25), (-3, -1.25), (3, -1.25))
  ar(GT, FT, GIVEN1, s0: 0.75, s1: 0.75); ar(GB, FB, GIVEN1, s0: 0.75, s1: 0.75)
  ar(GT, GB, GIVEN2, s0: 0.55, s1: 0.55); ar(FT, FB, GIVEN2, s0: 0.55, s1: 0.55)
  lab(0, 1.8, GIVEN1)[`φ`#sub[`A`]]; lab(0, -1.8, GIVEN1)[`φ`#sub[`B`]]
  lab(-3.8, 0, GIVEN2)[`G(R)`]; lab(3.8, 0, GIVEN2)[`F(R)`]
  lab(0, 0, SLACK, rot: -45deg)[`⊑`]
  node(GT.at(0), GT.at(1), black, `GA`); node(FT.at(0), FT.at(1), black, `FA`)
  node(GB.at(0), GB.at(1), black, `GB`); node(FB.at(0), FB.at(1), black, `FB`)
})
