// cdref-coprod.typ — the note's OWN coproduct square in the power allegory, standing alone, so
// `scripts/svg-check --against` can hold the generated panel to it.  This is the canvas
// `diag/ch/11-relator.typ`'s `<coprod-square>` drew — copied mark for mark: same `ar`/`arc`/`node`/
// `lab`, same coordinates, same `length: 0.8cm`.  `Freyd.Alg.u_junc_Λ_eps` IS that statement.
//
//   typst compile --root . --format svg diag/cdref-coprod.typ diag/cdref-coprod.svg
//   ./scripts/diag-export --commutative Freyd.Alg.u_junc_Λ_eps
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, ar, arc, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

// The book's figure turned a quarter turn, source at the left like every other picture here.  `R` and
// `S` arc outside because their straight lines would run over `E C`; blue dashed is the induced arrow.
#cetz.canvas(length: 0.8cm, {
  let (AB, PC, C) = ((-6.4, 0), (0.4, 0), (4.6, 0))
  let (A, B) = ((-3.4, 2.4), (-3.4, -2.4))
  ar(A, AB, black, s0: 0.5, s1: 0.9)
  ar(B, AB, black, s0: 0.5, s1: 0.9)
  ar(AB, PC, INDUCED, dash: "dashed", s0: 0.9, s1: 0.6)
  ar(PC, C, black, s0: 0.6, s1: 0.5)
  ar(A, PC, GIVEN1, s0: 0.5, s1: 0.6)
  ar(B, PC, GIVEN2, s0: 0.5, s1: 0.6)
  arc(A, C, 1, [`R`], col: GIVEN1, h: 4.0, cx: 3)
  arc(B, C, -1, [`S`], col: GIVEN2, h: 4.0, cx: 3)
  lab(-5.18, 1.55, black)[`l`]; lab(-5.18, -1.55, black)[`r`]
  lab(-1.23, 1.62, GIVEN1)[$frac(#[`R`], ∋)$]; lab(-1.23, -1.62, GIVEN2)[$frac(#[`S`], ∋)$]
  lab(-3.0, 0.5, INDUCED)[`[`$frac(#[`R`], ∋)$`,` $frac(#[`S`], ∋)$`]`]
  lab(2.5, 0.45, black)[`∋`]
  node(A.at(0), A.at(1), GIVEN1, $A$); node(B.at(0), B.at(1), GIVEN2, $B$)
  node(AB.at(0), AB.at(1), black, $A + B$)
  node(PC.at(0), PC.at(1), INDUCED, $E C$)
  node(C.at(0), C.at(1), black, $C$)
})
