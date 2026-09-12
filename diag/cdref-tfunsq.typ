// cdref-tfunsq.typ — the note's OWN square, standing alone, so `scripts/cd-check` can hold the
// generated panel to it.  This is the picture of `diag/allegory-axioms.typ`'s `<tfun-sq>` copied
// mark for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `T(f)` IS the fold `⦇F(f,𝟙)α`#sub[`B`]`⦈`, so the picture is that fold's defining square — `α`
// at the top, `F(𝟙,T(f))` at the left, the algebra `F(f,𝟙)α`#sub[`B`] as the chord, `T(f)` dashed
// at the right — with the algebra ALSO opened through `F(B,TB)`, the corner the statement names.
//
//   typst compile --root . diag/cdref-tfunsq.typ diag/cdref-tfunsq.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FA, TA) = ((-3, 2.5), (3, 2.5))
  let (FM, TB) = ((-3, 0), (3, 0))
  let FB = (-3, -2.5)
  ar(FA, TA, GIVEN2, s0: 1.45, s1: 0.65); ar(FM, TB, GIVEN1, s0: 1.45, s1: 0.55)
  ar(FA, FM, INDUCED, s0: 0.55, s1: 0.55)
  ar(FM, FB, black, s0: 0.55, s1: 0.55)
  ar(TA, TB, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  ar(FB, TB, GIVEN1, s0: 1.45, s1: 0.85)
  lab(0.4, 3.05, GIVEN2)[`α`#sub[`A`]]; lab(0.4, 0.6, GIVEN1)[`F(f,𝟙)α`#sub[`B`]]
  lab(-4.75, 1.25, INDUCED)[`F(𝟙,T(f))`]; lab(-4.25, -1.25, black)[`F(f,𝟙)`]
  lab(4.0, 1.25, INDUCED)[`T(f)`]; lab(0.7, -1.8, GIVEN1)[`α`#sub[`B`]]
  node(FA.at(0), FA.at(1), black, `F(A,TA)`); node(TA.at(0), TA.at(1), black, `TA`)
  node(FM.at(0), FM.at(1), black, `F(A,TB)`)
  node(FB.at(0), FB.at(1), GIVEN1, `F(B,TB)`); node(TB.at(0), TB.at(1), GIVEN1, `TB`)
})
