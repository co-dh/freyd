// cdref-banana.typ — the note's OWN fan, standing alone, so `scripts/svg-diff` can hold the generated
// panel to it.  This is the first picture of `diag/allegory-axioms.typ`'s `<banana-split>` copied mark
// for mark.  `Freyd.HasBinaryProducts.fst_pair+Freyd.HasBinaryProducts.snd_pair` IS that law — the
// product's two β-laws pasted along the arrow they share — so its generated panel must be this picture
// up to the letters (the note writes `⦇h⦈` where Lean binds `f`) and up to colour.
//
//   typst compile --root / --format svg diag/cdref-banana.typ diag/cdref-banana.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  // The fan is ±4.6 wide only so that `⟨⦇h⦈,⦇k⦈⟩` fits between the induced arrow and `⦇h⦈`'s leg.
  let (T, A, AB, B) = ((0, 2.2), (-4.6, -1.9), (0, -1.9), (4.6, -1.9))
  ar(T, A, GIVEN1, s0: 0.5, s1: 0.5); ar(T, B, GIVEN2, s0: 0.5, s1: 0.5)
  ar(T, AB, INDUCED, dash: "dashed", s0: 0.45, s1: 0.55)
  ar(AB, A, GIVEN1, s0: 0.95, s1: 0.5); ar(AB, B, GIVEN2, s0: 0.95, s1: 0.5)
  lab(-2.6, 0.45, GIVEN1)[`⦇h⦈`]; lab(2.6, 0.45, GIVEN2)[`⦇k⦈`]
  lab(-1.45, -0.85, INDUCED)[`⟨⦇h⦈,⦇k⦈⟩`]
  lab(-2.4, -2.45, GIVEN1)[`π₁`]; lab(2.4, -2.45, GIVEN2)[`π₂`]
  node(T.at(0), T.at(1), black, `T`); node(A.at(0), A.at(1), GIVEN1, `A`)
  node(AB.at(0), AB.at(1), INDUCED, `A×B`); node(B.at(0), B.at(1), GIVEN2, `B`)
})
