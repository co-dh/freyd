// cdref-adjE.typ — the note's OWN bent square, standing alone, so `scripts/svg-diff` can hold the
// generated panel to it.  This is the first picture of `diag/allegory-axioms.typ`'s `<adj-E-bend>`
// copied mark for mark.  `Freyd.Alg.Λ_eps_eq'+Freyd.Alg.Λ_eq_singleton_existsImage` IS that square —
// the two laws the dashed diagonal cuts it into, pasted along the diagonal they share — so its
// generated panel must be this picture up to the letters and up to colour.
//
//   typst compile --root / --format svg diag/cdref-adjE.typ diag/cdref-adjE.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (T, B) = (1.5, -1.5)
  let (xA, xB) = (-3.1, 3.1)
  ar((xA, T), (xB, T), GIVEN1, s0: 0.45, s1: 0.45)
  ar((xA, T), (xA, B), GIVEN2, s0: 0.5, s1: 0.5)
  ar((xA, B), (xB, B), GIVEN2, s0: 0.85, s1: 0.85)
  ar((xB, B), (xB, T), GIVEN2, s0: 0.5, s1: 0.45)
  // The diagonal cuts the square into the two laws: upper left `𝟙/∋ E(R) = R/∋`, lower right `(R/∋) ∋ = R`.
  ar((xA, T), (xB, B), INDUCED, dash: "dashed", s0: 0.5, s1: 0.75)
  lab(0, T + 0.5, GIVEN1)[`R`]
  // Each label also says what the arrow IS in the one operator, so the four read as instances of it.
  lab(xA - 0.62, 0, GIVEN2)[$frac(#[`𝟙`], ∋)$]
  lab(0, B - 0.95, GIVEN2)[#align(center)[`E(R)` \
    #text(8.5pt)[`E=` $frac(#[`∋·`], ∋)$]]]
  lab(xB + 0.35, 0, GIVEN2)[`∋`]
  lab(1.25, 0.2, INDUCED)[$frac(#[`R`], ∋)$]
  node(xA, T, black, `A`); node(xB, T, black, `B`)
  node(xA, B, black, `EA`); node(xB, B, black, `EB`)
})
