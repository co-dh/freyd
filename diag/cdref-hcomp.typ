// cdref-hcomp.typ — the note's OWN horizontal-composition row of `<lax-closure>`, standing alone,
// so `scripts/cd-check` can hold the generated panel to it.  This is
// `diag/allegory-axioms.typ`'s
//   laxsq((`LGA`, `KFA`, `LGB`, `KFB`),
//         (`χ`#sub[`GA`] `K(φ`#sub[`A`]`)`, `χ`#sub[`GB`] `K(φ`#sub[`B`]`)`, `L(G(R))`, `K(F(R))`))
// expanded mark for mark: same `ar`/`node`/`lab`, same `SQW`/`SQH`, same `length: 0.8cm`.
// `Freyd.Alg.laxNatural_hcomp_outer_first` IS that square — the note's own first candidate of the
// two the row orders by `⊑`.
// A generated label is one `raw` and `raw` carries no subscript, so the note's
// `` `χ` ``#sub[`` `GA` ``] `` `K(φ` ``#sub[`` `A` ``]`` `)` `` is the one name `χGA K(φA)` — a chain of
// one-letter functors on an object closes up (`LGA`), two composed factors keep their space.
//
//   typst compile --root . --format svg diag/cdref-hcomp.typ diag/cdref-hcomp.svg
//   ./scripts/diag-export --commutative Freyd.Alg.laxNatural_hcomp_outer_first
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (SQW, SQH) = (2.2, 0.95)
  let (l, r) = (-SQW, SQW)
  ar((l, SQH), (r, SQH), GIVEN1, s0: 0.5, s1: 0.5); ar((l, -SQH), (r, -SQH), GIVEN1, s0: 0.5, s1: 0.5)
  ar((l, SQH), (l, -SQH), GIVEN2, s0: 0.5, s1: 0.5); ar((r, SQH), (r, -SQH), GIVEN2, s0: 0.5, s1: 0.5)
  lab(0, SQH + 0.62, GIVEN1)[`χGA K(φA)`]; lab(0, -SQH - 0.62, GIVEN1)[`χGB K(φB)`]
  lab(l - 0.8, 0, GIVEN2)[`L(G(R))`]; lab(r + 0.8, 0, GIVEN2)[`K(F(R))`]
  lab(0, 0, SLACK, rot: -45deg)[`⊑`]
  node(l, SQH, black, `LGA`); node(r, SQH, black, `KFA`)
  node(l, -SQH, black, `LGB`); node(r, -SQH, black, `KFB`)
})
