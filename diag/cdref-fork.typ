// cdref-fork.typ — the drawing `diag/allegory-axioms.typ`'s `<fork-pic>` must be, so `scripts/cd-check`
// can hold the generated panel to it.  It is the note's OWN fan — `<banana-split>`'s first canvas, mark
// for mark, at this statement's letters and narrowed to the width `⟨R,S⟩` needs — because the fork and
// that fan ARE one diagram: four nodes, two given legs, two projections and the induced arrow between
// them.  `<fork-pic>` draws that same wiring turned on its side, which is one picture in two shapes.
//
// The two `⊑` are the statement: a domain is coreflexive, so `⟨R,S⟩π₁⊑R` and `⟨R,S⟩π₂⊑S`, with equality
// exactly when the OTHER leg is entire.  A fan drawn with no symbol claims the equality outright, which
// is the note's own `<relprod-pic>` convention read the other way.
//
//   typst compile --root / --format svg diag/cdref-fork.typ diag/cdref-fork.svg
#import "draw.typ": GIVEN1, GIVEN2, INDUCED, SLACK, ar, cetz, lab, node

#set page(width: auto, height: auto, margin: 12pt, fill: white)

#cetz.canvas(length: 0.8cm, {
  let (C, A, AB, B) = ((0, 2.2), (-3.4, -1.9), (0, -1.9), (3.4, -1.9))
  ar(C, A, GIVEN1, s0: 0.5, s1: 0.5); ar(C, B, GIVEN2, s0: 0.5, s1: 0.5)
  ar(C, AB, INDUCED, dash: "dashed", s0: 0.45, s1: 0.55)
  ar(AB, A, GIVEN1, s0: 0.95, s1: 0.5); ar(AB, B, GIVEN2, s0: 0.95, s1: 0.5)
  lab(-2.0, 0.45, GIVEN1)[`R`]; lab(2.0, 0.45, GIVEN2)[`S`]
  lab(-0.95, -0.85, INDUCED)[`⟨R,S⟩`]
  lab(-1.8, -2.45, GIVEN1)[`π₁`]; lab(1.8, -2.45, GIVEN2)[`π₂`]
  lab(-1.6, -1.35, SLACK)[`⊑`]; lab(1.3, -0.85, SLACK)[`⊑`]
  node(C.at(0), C.at(1), black, `C`); node(A.at(0), A.at(1), GIVEN1, `A`)
  node(AB.at(0), AB.at(1), INDUCED, `A×B`); node(B.at(0), B.at(1), GIVEN2, `B`)
})
