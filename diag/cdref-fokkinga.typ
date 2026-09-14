// cdref-fokkinga.typ — the note's OWN pair of squares, standing alone, so `scripts/svg-diff` can hold
// the generated panel to it.  This is the picture of `diag/allegory-axioms.typ`'s `<fokkinga>` copied
// mark for mark, `capbox`'s caption dropped because the generated file draws only the picture.
// `Freyd.Alg.pair_eq_relCata_pair_iff.lhs` IS that conjunction, one square per conjunct, so its
// generated row must be these two squares up to the letters and up to colour.
//
//   typst compile --root / --format svg diag/cdref-fokkinga.typ diag/cdref-fokkinga.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#grid(columns: 2, align: horizon, column-gutter: 34pt,
  cetz.canvas(length: 0.8cm, {
    let (FT, T, FAB, A) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FAB, A, GIVEN1, s0: 1.35, s1: 0.55)
    ar(FT, FAB, INDUCED, s0: 0.5, s1: 0.5)
    ar(T, A, INDUCED, dash: "dashed", s0: 0.5, s1: 0.5)
    lab(0, 1.9, GIVEN2)[`α`]; lab(0.4, -1.9, GIVEN1)[`h`]
    lab(-4.15, 0, INDUCED)[`F(⟨f,g⟩)`]; lab(3.0, 0, INDUCED)[`f`]
    node(FT.at(0), FT.at(1), black, `FT`); node(FAB.at(0), FAB.at(1), GIVEN1, `F(A×B)`)
    node(T.at(0), T.at(1), black, `T`); node(A.at(0), A.at(1), GIVEN1, `A`)
  }),
  cetz.canvas(length: 0.8cm, {
    let (FT, T, FAB, B) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
    ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FAB, B, GIVEN1, s0: 1.35, s1: 0.55)
    ar(FT, FAB, INDUCED, s0: 0.5, s1: 0.5)
    ar(T, B, INDUCED, dash: "dashed", s0: 0.5, s1: 0.5)
    lab(0, 1.9, GIVEN2)[`α`]; lab(0.4, -1.9, GIVEN1)[`k`]
    lab(-4.15, 0, INDUCED)[`F(⟨f,g⟩)`]; lab(3.0, 0, INDUCED)[`g`]
    node(FT.at(0), FT.at(1), black, `FT`); node(FAB.at(0), FAB.at(1), GIVEN1, `F(A×B)`)
    node(T.at(0), T.at(1), black, `T`); node(B.at(0), B.at(1), GIVEN1, `B`)
  }),
)
