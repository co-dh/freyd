// cdref-refl.typ — the note's OWN square, standing alone, so `scripts/cd-check` can hold the
// generated panel to it.  This is the picture of `diag/allegory-axioms.typ`'s `<cata-reflection>`
// copied mark for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `Freyd.Alg.relCata_alpha_UP` is `αX=F(X)α ⟺ X=𝟙`, and its left side is this square: the arrow
// the equivalence pins down is dashed, exactly as `cata-defining` dashes the fold's `X`.
//
//   typst compile --root . diag/cdref-refl.typ diag/cdref-refl.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (FT, T, FT2, T2) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
  ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FT2, T2, GIVEN2, s0: 0.55, s1: 0.55)
  ar(FT, FT2, INDUCED, s0: 0.55, s1: 0.55)
  ar(T, T2, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  lab(0, 1.9, GIVEN2)[`α`]; lab(0, -1.9, GIVEN2)[`α`]
  lab(-4.0, 0, INDUCED)[`F(X)`]; lab(3.4, 0, INDUCED)[`X`]
  node(FT.at(0), FT.at(1), black, `FT`); node(FT2.at(0), FT2.at(1), black, `FT`)
  node(T.at(0), T.at(1), black, `T`); node(T2.at(0), T2.at(1), black, `T`)
})
