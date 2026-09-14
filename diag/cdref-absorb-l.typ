// cdref-absorb-l.typ — the FIRST canvas of `diag/allegory-axioms.typ`'s `<party-absorb>` standing
// alone, so `scripts/svg-check --against` can hold the generated panel to it: the one transpose
// `Λ(⦇S⦈choose)` the absorption law's left side is.  `Freyd.Alg.RelSet.Party.party_absorb` IS that
// law at this instance, and `.lhs` names this side of it; the `=` the note sets between the two
// canvases is the row's text, so it is in neither reference.
//
//   typst compile --root . --format svg diag/cdref-absorb-l.typ diag/cdref-absorb-l.svg
//   ./scripts/diag-export --commutative Freyd.Alg.RelSet.Party.party_absorb.lhs
#import "draw.typ": INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (T, EB) = ((-2.9, 0), (2.9, 0))
  ar(T, EB, INDUCED, dash: "dashed", s0: 1.05, s1: 0.8)
  lab(0, 0.85, INDUCED)[$frac(#[`⦇S⦈choose`], ∋)$]
  node(T.at(0), T.at(1), black, `tree(A)`); node(EB.at(0), EB.at(1), black, `E[A]`)
})
