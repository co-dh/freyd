// cdref-dist.typ — the note's OWN square, standing alone, so `scripts/svg-diff` can hold the
// generated commutative diagram to it.  This is the first `cetz.canvas` of
// `diag/allegory-axioms.typ`'s `<dist-str>` copied mark for mark: same `ar`/`node`/`lab`, same
// corners, same `length: 0.8cm`.  `Freyd.Alg.Distributes` IS that predicate — a LAX square, so the
// face carries the `⊑` — and its generated panel must be this picture up to the letters and up to
// colour.  The top edge is a SYMMETRIC DIVISION and is set as the note's fraction bar, which
// delimits its numerator: `frac(F(∋)f, ∋)`, never the inline `(F(∋)f)%∋`.
//
//   typst compile --root . --format svg diag/cdref-dist.typ diag/cdref-dist.svg
#import "draw.typ": GIVEN1, GIVEN2, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FEA, EA, FA, A) = ((-3.6, 1.25), (3.6, 1.25), (-3.6, -1.25), (3.6, -1.25))
  ar(FEA, EA, GIVEN1, s0: 1.05, s1: 0.65); ar(FA, A, GIVEN1, s0: 0.65, s1: 0.45)
  ar(FEA, FA, GIVEN2, s0: 0.55, s1: 0.55); ar(EA, A, GIVEN2, s0: 0.55, s1: 0.55)
  lab(0, 2.1, GIVEN1)[$frac(#[`F(∋)f`], ∋)$]; lab(0, -1.8, GIVEN1)[`f`]
  lab(-4.75, 0, GIVEN2)[`F(est(R))`]; lab(4.4, 0, GIVEN2)[`est(R)`]
  lab(0, 0, SLACK, rot: -45deg)[`⊑`]
  node(FEA.at(0), FEA.at(1), black, `F(EA)`); node(EA.at(0), EA.at(1), black, `EA`)
  node(FA.at(0), FA.at(1), black, `FA`); node(A.at(0), A.at(1), black, `A`)
})
