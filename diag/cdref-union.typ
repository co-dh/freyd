// cdref-union.typ — the note's OWN union row of `<lax-closure>`, standing alone, so
// `scripts/cd-check` can hold the generated panel to it.  This is `diag/allegory-axioms.typ`'s
//   laxsq((`GA`, `FA`, `GB`, `FB`), ([`φ`#sub[`A`]], [`φ`#sub[`B`]], `G(R)`, `F(R)`), x: -(SQW + 1.4))
//   laxsq((`GA`, `FA`, `GB`, `FB`), ([`ψ`#sub[`A`]], [`ψ`#sub[`B`]], `G(R)`, `F(R)`), x: SQW + 1.4)
//   lab(0, 0, black)[`∪`]
// expanded mark for mark: same `ar`/`node`/`lab`, same `SQW`/`SQH`, same `length: 0.8cm`.
// `Freyd.Alg.laxNatural_union` IS the pair: an assertion about a JOIN is one panel per operand
// (`@[diag_join "∪"]`), and the operator itself stands between the panels and never in a label.
//
//   typst compile --root . --format svg diag/cdref-union.typ diag/cdref-union.svg
//   ./scripts/diag-export --commutative Freyd.Alg.laxNatural_union
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (SQW, SQH) = (2.2, 0.95)
  for (x, a, b) in ((-(SQW + 1.4), [`φ`#sub[`A`]], [`φ`#sub[`B`]]),
                    (SQW + 1.4, [`ψ`#sub[`A`]], [`ψ`#sub[`B`]])) {
    let (l, r) = (x - SQW, x + SQW)
    ar((l, SQH), (r, SQH), GIVEN1, s0: 0.5, s1: 0.5)
    ar((l, -SQH), (r, -SQH), GIVEN1, s0: 0.5, s1: 0.5)
    ar((l, SQH), (l, -SQH), GIVEN2, s0: 0.5, s1: 0.5)
    ar((r, SQH), (r, -SQH), GIVEN2, s0: 0.5, s1: 0.5)
    lab(x, SQH + 0.62, GIVEN1)[#a]; lab(x, -SQH - 0.62, GIVEN1)[#b]
    lab(l - 0.8, 0, GIVEN2)[`G(R)`]; lab(r + 0.8, 0, GIVEN2)[`F(R)`]
    lab(x, 0, SLACK, rot: -45deg)[`⊑`]
    node(l, SQH, black, `GA`); node(r, SQH, black, `FA`)
    node(l, -SQH, black, `GB`); node(r, -SQH, black, `FB`)
  }
  lab(0, 0, black)[`∪`]
})
