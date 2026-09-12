// cdref-absorb-r.typ — the SECOND canvas of `diag/allegory-axioms.typ`'s `<party-absorb>` standing
// alone, so `scripts/svg-check --against` can hold the generated panel to it: the path the
// absorption law's right side runs, the transpose of the fold followed by the relator's image of
// `choose`.  `.rhs` of `Freyd.Alg.RelSet.Party.party_absorb` names this side; the transpose is the
// arrow the adjunction produces, hence dashed and INDUCED on both sides of the `=`, and `E(choose)`
// is the relator's image of an arrow the statement is handed, hence GIVEN2.
//
//   typst compile --root . --format svg diag/cdref-absorb-r.typ diag/cdref-absorb-r.svg
//   ./scripts/diag-export --commutative Freyd.Alg.RelSet.Party.party_absorb.rhs
#import "draw.typ": GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (T, EM, EB) = ((-5.0, 0), (0, 0), (5.0, 0))
  ar(T, EM, INDUCED, dash: "dashed", s0: 1.05, s1: 1.6); ar(EM, EB, GIVEN2, s0: 1.6, s1: 0.8)
  lab(-2.5, 0.85, INDUCED)[$frac(#[`⦇S⦈`], ∋)$]
  lab(2.5, 0.62, GIVEN2)[`E(choose)`]
  node(T.at(0), T.at(1), black, `tree(A)`); node(EM.at(0), EM.at(1), black, `E([A]×[A])`)
  node(EB.at(0), EB.at(1), black, `E[A]`)
})
