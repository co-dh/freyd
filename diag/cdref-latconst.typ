// cdref-latconst.typ — the note's OWN lax square AT THE TWO CONSTANT RELATORS, standing alone, so
// `scripts/svg-check --against` can hold the generated panel to it.  This is the SECOND drawing of
// `diag/ch/13-optimisation.typ`'s `<lat-const>` canvas — the `laxsq` at `x: 0` — cut out mark for
// mark, the helper's body written out at those arguments and no coordinate touched.
// `Freyd.Alg.laxNatural_const_iff.lhs` IS that square.
//
//   typst compile --root . --format svg diag/cdref-latconst.typ diag/cdref-latconst.svg
//   ./scripts/diag-export --commutative Freyd.Alg.laxNatural_const_iff.lhs
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (SQW, SQH, x) = (2.2, 0.95, 0)
  let (l, r) = (x - SQW, x + SQW)
  ar((l, SQH), (r, SQH), GIVEN1, s0: 0.5, s1: 0.5); ar((l, -SQH), (r, -SQH), GIVEN1, s0: 0.5, s1: 0.5)
  ar((l, SQH), (l, -SQH), GIVEN2, s0: 0.5, s1: 0.5); ar((r, SQH), (r, -SQH), GIVEN2, s0: 0.5, s1: 0.5)
  lab(x, SQH + 0.62, GIVEN1)[`φ`#sub[`X`]]
  lab(x, -SQH - 0.62, GIVEN1)[`φ`#sub[`Y`]]
  lab(l - 0.8, 0, GIVEN2)[`𝟙`#sub[`A`]]
  lab(r + 0.8, 0, GIVEN2)[`𝟙`#sub[`B`]]
  lab(x, 0, SLACK, rot: -45deg)[`⊑`]
  node(l, SQH, black, `A`); node(r, SQH, black, `B`)
  node(l, -SQH, black, `A`); node(r, -SQH, black, `B`)
})
