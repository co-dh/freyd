// cdref-coprod.typ — the note's OWN coproduct square in the power allegory, standing alone, so
// `scripts/svg-check --against` can hold the generated panel to it.  This is the canvas
// `diag/ch/11-relator.typ`'s `<coprod-square>` drew — copied mark for mark: same `ar`/`arc`/`node`/
// `lab`, same coordinates, same `length: 0.8cm`.  `Freyd.Alg.u_junc_Λ_eps` IS that statement.
//
// THE CHANGES FROM THE NOTE, all of them the note's MATH set raw as every other commutative panel
// sets its labels, because `scripts/cd-labels` tokenises the two spellings apart — `A + B` as three
// words against the panel's one, and a fraction whose bar is math as two words against the panel's
// one.  The five node labels (`$A$`, `$A + B$`, `$E C$`) and every `∋` under a fraction bar are raw
// here; the note's own lines are reported as a defect rather than edited.
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
  // BOWED, not `arc`: `arc` sets its label in a white BOX, which `scripts/svg-check` reads back as
  // a node — the two arcs then stood as two one-node diagrams of their own beside the polygon.
  ar(A, C, GIVEN1, s0: 0.5, s1: 0.5, bow: 3.4)
  ar(B, C, GIVEN2, s0: 0.5, s1: 0.5, bow: -3.4)
  lab(0.6, 3.41, GIVEN1)[`R`]; lab(0.6, -3.41, GIVEN2)[`S`]
  lab(-5.18, 1.55, black)[`l`]; lab(-5.18, -1.55, black)[`r`]
  lab(-1.23, 1.62, GIVEN1)[$frac(#[`R`], #[`∋`])$]; lab(-1.23, -1.62, GIVEN2)[$frac(#[`S`], #[`∋`])$]
  lab(-3.0, 0.5, INDUCED)[`[`$frac(#[`R`], #[`∋`])$`,`$frac(#[`S`], #[`∋`])$`]`]
  lab(2.5, 0.45, black)[`∋`]
  node(A.at(0), A.at(1), GIVEN1, `A`); node(B.at(0), B.at(1), GIVEN2, `B`)
  node(AB.at(0), AB.at(1), black, `A+B`)
  node(PC.at(0), PC.at(1), INDUCED, `EC`)
  node(C.at(0), C.at(1), black, `C`)
})
