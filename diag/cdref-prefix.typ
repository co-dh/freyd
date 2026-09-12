// cdref-prefix.typ — the note's OWN square, standing alone, so `scripts/svg-diff` can hold the
// generated panel to it.  This is the picture of `diag/allegory-axioms.typ`'s `<prefix-defn>` copied
// mark for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `Freyd.Alg.RelSet.ListRel.prefix_cancel` IS that square — `α prefix=F(prefix)[nil,⊸ nil ∪ cons]` —
// at the one initial algebra the note names, so its corners are the list itself where the abstract
// square (`cdref-catadef.typ`) has `T`.
//
//   typst compile --root . --format svg diag/cdref-prefix.typ diag/cdref-prefix.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  // The same 5.2 × 2.7 square as @cata-defining, `prefix` in the induced arrow's place.
  let (FT, T, FA, A) = ((-2.6, 1.35), (2.6, 1.35), (-2.6, -1.35), (2.6, -1.35))
  ar(FT, T, GIVEN2, s0: 0.55, s1: 0.55); ar(FA, A, GIVEN1, s0: 0.55, s1: 0.55)
  ar(FT, FA, INDUCED, s0: 0.55, s1: 0.55)
  ar(T, A, INDUCED, dash: "dashed", s0: 0.55, s1: 0.55)
  lab(0, 1.9, GIVEN2)[`α`]; lab(0, -1.9, GIVEN1)[`[nil,⊸ nil ∪ cons]`]
  lab(-4.2, 0, INDUCED)[`F(prefix)`]; lab(3.7, 0, INDUCED)[`prefix`]
  node(FT.at(0), FT.at(1), black, `F[A]`); node(T.at(0), T.at(1), black, `[A]`)
  node(FA.at(0), FA.at(1), GIVEN1, `F[A]`); node(A.at(0), A.at(1), GIVEN1, `[A]`)
})
