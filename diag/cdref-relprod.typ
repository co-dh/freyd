// cdref-relprod.typ — the note's OWN product square, standing alone, so `scripts/cd-check` can hold
// the generated panel to it.  This is the first picture of `diag/allegory-axioms.typ`'s
// `<relprod-pic>` copied mark for mark: same `ar`/`node`/`lab`, same corners, same `length: 0.8cm`.
// `Freyd.Alg.prodMap_outl_le+Freyd.Alg.prodMap_outr_le` IS that square — the two claims of book
// p.115, `(R×S)π₁⊑π₁R` and `(R×S)π₂⊑π₂S`, pasted along the arrow they share.
//
// THE ONE CHANGE FROM THE NOTE: its six node labels and `R×S` are set in MATH (`$C$`, `$C times D$`,
// `$R times S$`) where every other commutative panel of the note sets its labels raw, so
// `scripts/cd-labels` tokenises `C × D` as three words against the panel's one.  They are raw here;
// the note's own lines are reported as a defect rather than edited.
//
//   typst compile --root . --format svg diag/cdref-relprod.typ diag/cdref-relprod.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (C, CD, D) = ((-2.7, 1.7), (-2.7, 0), (-2.7, -1.7))
  let (A, AB, B) = ((2.7, 1.7), (2.7, 0), (2.7, -1.7))
  ar(CD, C, GIVEN1, s0: 0.55); ar(CD, D, GIVEN2, s0: 0.55)
  ar(AB, A, GIVEN1, s0: 0.55); ar(AB, B, GIVEN2, s0: 0.55)
  ar(C, A, GIVEN1); ar(D, B, GIVEN2)
  ar(CD, AB, INDUCED, dash: "dashed", s0: 0.95, s1: 0.95)
  lab(-3.1, 0.85, GIVEN1)[`π₁`]; lab(-3.1, -0.85, GIVEN2)[`π₂`]
  lab(3.1, 0.85, GIVEN1)[`π₁`]; lab(3.1, -0.85, GIVEN2)[`π₂`]
  lab(0, 2.0, GIVEN1)[`R`]; lab(0, -1.4, GIVEN2)[`S`]
  lab(-1.2, 0.32, INDUCED)[`R×S`]
  lab(1.2, 0.85, SLACK, rot: -135deg)[`⊑`]; lab(1.2, -0.85, SLACK, rot: 135deg)[`⊑`]
  node(C.at(0), C.at(1), GIVEN1, `C`); node(D.at(0), D.at(1), GIVEN2, `D`)
  node(CD.at(0), CD.at(1), INDUCED, `C×D`)
  node(A.at(0), A.at(1), GIVEN1, `A`); node(B.at(0), B.at(1), GIVEN2, `B`)
  node(AB.at(0), AB.at(1), INDUCED, `A×B`)
})
