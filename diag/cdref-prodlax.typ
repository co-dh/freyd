// cdref-prodlax.typ — the note's OWN product row of `<lax-closure>`, standing alone, so
// `scripts/cd-check` can hold the generated panel to it.  This is `diag/allegory-axioms.typ`'s
// `laxsq((`GA×G'A`, `FA×F'A`, `GB×G'B`, `FB×F'B`), ([`φ`#sub[`A`]`×ψ`#sub[`A`]],
// [`φ`#sub[`B`]`×ψ`#sub[`B`]], `G(R)×G'(R)`, `F(R)×F'(R)`))`
// expanded mark for mark: same `ar`/`node`/`lab`, same `SQW`/`SQH`, same `length: 0.8cm`.
// `Freyd.Alg.laxNatural_prod` IS that square — `φ : G⇒F` and `ψ : G'⇒F'` give `φ×ψ : G×G'⇒F×F'`.
//
// THE ONE CHANGE FROM THE NOTE: `laxsq` sets the two SIDE labels with `node` — the mark for a
// VERTEX — standing them ON the edge with a white ground, where every other commutative panel of
// the note labels an edge with `lab` beside it (`<lax-str>`'s own square included).  Read back,
// four vertices on the edges cut the square into four diagrams.  They are `lab` here, beside the
// edge as `cdref-lax.typ` sets them; the note's own line is reported as a defect rather than edited.
//
//   typst compile --root . --format svg diag/cdref-prodlax.typ diag/cdref-prodlax.svg
//   ./scripts/diag-export --commutative Freyd.Alg.laxNatural_prod
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (SQW, SQH) = (2.2, 0.95)
  let (l, r) = (-SQW, SQW)
  ar((l, SQH), (r, SQH), GIVEN1, s0: 0.5, s1: 0.5); ar((l, -SQH), (r, -SQH), GIVEN1, s0: 0.5, s1: 0.5)
  ar((l, SQH), (l, -SQH), GIVEN2, s0: 0.5, s1: 0.5); ar((r, SQH), (r, -SQH), GIVEN2, s0: 0.5, s1: 0.5)
  lab(0, SQH + 0.62, GIVEN1)[`φ`#sub[`A`]`×ψ`#sub[`A`]]
  lab(0, -SQH - 0.62, GIVEN1)[`φ`#sub[`B`]`×ψ`#sub[`B`]]
  lab(l - 0.8, 0, GIVEN2)[`G(R)×G'(R)`]; lab(r + 0.8, 0, GIVEN2)[`F(R)×F'(R)`]
  lab(0, 0, SLACK, rot: -45deg)[`⊑`]
  node(l, SQH, black, `GA×G'A`); node(r, SQH, black, `FA×F'A`)
  node(l, -SQH, black, `GB×G'B`); node(r, -SQH, black, `FB×F'B`)
})
