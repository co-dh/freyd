// cdref-comp.typ — the note's OWN composition row of `<lax-closure>`, standing alone, so
// `scripts/cd-check` can hold the generated panel to it.  This is `diag/allegory-axioms.typ`'s
//   laxsq((`HA`, `GA`, `HB`, `GB`), ([`ψ`#sub[`A`]], [`ψ`#sub[`B`]], [`H(R)`], none), x: -SQW)
//   laxsq((`GA`, `FA`, `GB`, `FB`), ([`φ`#sub[`A`]], [`φ`#sub[`B`]], [`G(R)`], [`F(R)`]), x: SQW)
// expanded mark for mark: same `ar`/`node`/`lab`, same `SQW`/`SQH`, same `length: 0.8cm`.
// `Freyd.Alg.laxNatural_comp_slide` IS the pair — `comp_slides` at the note's own chord, the
// relator-moved `G(R)`, which is what stands it upright between the two squares.
//
// The shared edge is drawn ONCE here.  `laxsq` draws it twice — once as the first square's right
// side and once as the second's left — and two `ar`s on one segment read back as one edge anyway;
// the note's own line is reported as a defect rather than edited.
//
//   typst compile --root . --format svg diag/cdref-comp.typ diag/cdref-comp.svg
//   ./scripts/diag-export --commutative Freyd.Alg.laxNatural_comp_slide
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (SQW, SQH) = (2.2, 0.95)
  let (l, m, r) = (-2 * SQW, 0, 2 * SQW)
  ar((l, SQH), (m, SQH), GIVEN1, s0: 0.5, s1: 0.5); ar((l, -SQH), (m, -SQH), GIVEN1, s0: 0.5, s1: 0.5)
  ar((m, SQH), (r, SQH), GIVEN1, s0: 0.5, s1: 0.5); ar((m, -SQH), (r, -SQH), GIVEN1, s0: 0.5, s1: 0.5)
  ar((l, SQH), (l, -SQH), GIVEN2, s0: 0.5, s1: 0.5); ar((m, SQH), (m, -SQH), GIVEN2, s0: 0.5, s1: 0.5)
  ar((r, SQH), (r, -SQH), GIVEN2, s0: 0.5, s1: 0.5)
  lab(-SQW, SQH + 0.62, GIVEN1)[`ψ`#sub[`A`]]; lab(-SQW, -SQH - 0.62, GIVEN1)[`ψ`#sub[`B`]]
  lab(SQW, SQH + 0.62, GIVEN1)[`φ`#sub[`A`]]; lab(SQW, -SQH - 0.62, GIVEN1)[`φ`#sub[`B`]]
  lab(l - 0.8, 0, GIVEN2)[`H(R)`]; lab(m - 0.8, 0, GIVEN2)[`G(R)`]
  lab(r + 0.8, 0, GIVEN2)[`F(R)`]
  lab(-SQW, 0, SLACK, rot: -45deg)[`⊑`]; lab(SQW, 0, SLACK, rot: -45deg)[`⊑`]
  node(l, SQH, black, `HA`); node(m, SQH, black, `GA`); node(r, SQH, black, `FA`)
  node(l, -SQH, black, `HB`); node(m, -SQH, black, `GB`); node(r, -SQH, black, `FB`)
})
