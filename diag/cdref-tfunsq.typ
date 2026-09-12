// cdref-tfunsq.typ — the note's OWN square, standing alone, so `scripts/cd-check` can hold the
// generated panel to it.  This is the picture of `diag/allegory-axioms.typ`'s `<tfun-sq>` copied
// mark for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `Freyd.Alg.alpha_natural_split` is the naturality with its left edge FACTORED — `F(𝟙,T(f))` then
// `F(f,𝟙)` through `F(A,TB)` — which is the fifth corner the note stands at.  The statement names
// no composite `F(f,𝟙)α`, so the chord the note once drew across the square is gone and its three-
// edge side lies along the grid `layout` gives it.
//
//   typst compile --root . diag/cdref-tfunsq.typ diag/cdref-tfunsq.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FA, TA) = ((-4.5, 1.4), (4.5, 1.4))
  let (FM, FB, TB) = ((-4.5, -1.4), (0, -1.4), (4.5, -1.4))
  ar(FA, TA, GIVEN2, s0: 1.45, s1: 0.65); ar(TA, TB, GIVEN2, s0: 0.6, s1: 0.6)
  ar(FA, FM, GIVEN2, s0: 0.55, s1: 0.55)
  ar(FM, FB, GIVEN2, s0: 1.45, s1: 1.45); ar(FB, TB, GIVEN2, s0: 1.45, s1: 0.65)
  lab(0, 1.95, GIVEN2)[`α`]; lab(5.25, 0, GIVEN2)[`T(f)`]
  lab(-6.25, 0, GIVEN2)[`F(𝟙,T(f))`]
  lab(-2.25, -1.95, GIVEN2)[`F(f,𝟙)`]; lab(2.25, -1.95, GIVEN2)[`α`]
  node(FA.at(0), FA.at(1), black, `F(A,TA)`); node(TA.at(0), TA.at(1), black, `TA`)
  node(FM.at(0), FM.at(1), black, `F(A,TB)`); node(FB.at(0), FB.at(1), black, `F(B,TB)`)
  node(TB.at(0), TB.at(1), black, `TB`)
})
