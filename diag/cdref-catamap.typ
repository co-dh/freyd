// cdref-catamap.typ — the note's OWN two stacked squares, standing alone, so `scripts/cd-check` can
// hold the generated panel to them.  This is the picture of `diag/allegory-axioms.typ`'s
// `<cata-map-square>` copied mark for mark: same `ar`/`node`/`lab`, same corners, same
// `length: 0.8cm`.  The map algebra is a NAMED arrow `f`, so it is drawn solid under its name with
// its value written beneath it, and the fold's defining square is pasted onto the triangle that
// pins that name, `f∋=F(∋)R`.
//
//   typst compile --root . diag/cdref-catamap.typ diag/cdref-catamap.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FT, T) = ((-2.6, 1.5), (2.6, 1.5))
  let (FE, E) = ((-2.6, -1.2), (2.6, -1.2))
  let (FA, A) = ((-2.6, -3.9), (2.6, -3.9))
  ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FE, E, GIVEN1, s0: 0.55, s1: 0.55)
  ar(FA, A, black, s0: 0.55, s1: 0.55)
  ar(FT, FE, INDUCED, s0: 0.55, s1: 0.55)
  ar(T, E, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  ar(FE, FA, black, s0: 0.55, s1: 0.55)
  ar(E, A, black, s0: 0.55, s1: 0.55)
  lab(0, 2.05, GIVEN2)[`α`]
  lab(-4.6, 0.15, INDUCED)[`F(⦇`$frac(#[`F(∋)R`], ∋)$`⦈)`]
  lab(4.2, 0.15, INDUCED)[`⦇`$frac(#[`F(∋)R`], ∋)$`⦈`]
  lab(0, -0.65, GIVEN1)[`f`]
  lab(0, -1.95, GIVEN1)[$frac(#[`F(∋)R`], ∋)$]
  lab(-4.0, -2.55, black)[`F(∋)`]; lab(3.6, -2.55, black)[`∋`]
  lab(0, -4.45, black)[`R`]
  node(FT.at(0), FT.at(1), black, `FT`); node(T.at(0), T.at(1), black, `T`)
  node(FE.at(0), FE.at(1), GIVEN1, `F(EA)`); node(E.at(0), E.at(1), GIVEN1, `EA`)
  node(FA.at(0), FA.at(1), GIVEN1, `FA`); node(A.at(0), A.at(1), GIVEN1, `A`)
})
