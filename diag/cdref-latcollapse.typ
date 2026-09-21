// cdref-latcollapse.typ — the note's OWN collapse of the lax square to two arrows `A⟶B` with `⊑`
// between them, standing alone, so `scripts/svg-check --against` can hold the generated panel to
// it.  This is the THIRD drawing of `diag/ch/13-optimisation.typ`'s `<lat-const>` canvas, at its
// own coordinates; its two arrows are the bowed `ar`s the generator draws, where the canvas wrote
// `arc`s — an `arc` drops no `cdscan` mark and a canvas of nothing but arcs is no commutative
// canvas at all.  `Freyd.Alg.laxNatural_const_iff.rhs` IS that pair of arrows.
//
//   typst compile --root . --format svg diag/cdref-latcollapse.typ diag/cdref-latcollapse.svg
//   ./scripts/diag-export --commutative Freyd.Alg.laxNatural_const_iff.rhs
#import "draw.typ": GIVEN1, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (a, b) = ((5.2, 0), (9.6, 0))
  ar(a, b, GIVEN1, s0: 0.5, s1: 0.5, bow: 1.2); ar(a, b, GIVEN1, s0: 0.5, s1: 0.5, bow: -1.2)
  lab(7.4, 1.2, GIVEN1)[`φ`#sub[`X`]]; lab(7.4, -1.2, GIVEN1)[`φ`#sub[`Y`]]
  // -45deg, the note's own tilt: a `⊑` turned the full -90deg is read as a `⊔`.
  lab(7.4, 0, SLACK, rot: -45deg)[`⊑`]
  node(5.2, 0, black, `A`); node(9.6, 0, black, `B`)
})
