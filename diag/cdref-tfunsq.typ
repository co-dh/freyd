// cdref-tfunsq.typ — the note's OWN square, standing alone, so `scripts/cd-check` can hold the
// generated panel to it.  This is the picture of `diag/allegory-axioms.typ`'s `<tfun-sq>` copied
// mark for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `T(f)` IS the fold `⦇F(f,𝟙)α`#sub[`B`]`⦈`, so the picture is that fold's defining square — `α`
// at the top, `F(𝟙,T(f))` at the left, `T(f)` dashed at the right — with the algebra opened
// through `F(B,TB)`, the corner the statement names.  By the author's decision this square follows
// the declaration: five arrows round a rectangle, `α`#sub[`B`] along the bottom, and no chord
// `F(f,𝟙)α`#sub[`B`], because that composite is no arrow of the statement.
//
//   typst compile --root . diag/cdref-tfunsq.typ diag/cdref-tfunsq.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FA, TA) = ((-3, 2.5), (3, 2.5))
  let FM = (-3, 0)
  let (FB, TB) = ((-3, -2.5), (3, -2.5))
  ar(FA, TA, GIVEN2, s0: 1.45, s1: 0.65)
  ar(FA, FM, INDUCED, s0: 0.55, s1: 0.55)
  ar(FM, FB, GIVEN2, s0: 0.55, s1: 0.55)
  ar(TA, TB, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  ar(FB, TB, GIVEN2, s0: 1.45, s1: 0.65)
  lab(0.4, 3.05, GIVEN2)[`α`#sub[`A`]]
  lab(-4.75, 1.25, INDUCED)[`F(𝟙,T(f))`]; lab(-4.25, -1.25, GIVEN2)[`F(f,𝟙)`]
  lab(4.0, 0, INDUCED)[`T(f)`]; lab(0.4, -1.95, GIVEN2)[`α`#sub[`B`]]
  node(FA.at(0), FA.at(1), black, `F(A,TA)`); node(TA.at(0), TA.at(1), black, `TA`)
  node(FM.at(0), FM.at(1), black, `F(A,TB)`)
  node(FB.at(0), FB.at(1), black, `F(B,TB)`); node(TB.at(0), TB.at(1), black, `TB`)
})
