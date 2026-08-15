// whisker.typ — what whiskering does, drawn.  Standalone PNG:
//   typst compile --root . --format png --ppi 220 diag/whisker.typ diag/whisker.png
//
// The top row is the unit of the INTERNAL adjunction `◁ ⊣ ▷`: an inequality between two 1-cells,
// with nothing applied to anything.  The rows below stick a box on one end of BOTH sides — that is
// the whole operation — and the inequality becomes one between arrows `A ⟶ B`, read at an
// argument.  Which side the box goes on decides which of the two induced adjunctions you get, and
// the pre-composition side flips the order, as right adjoints always do.
#import "strdiag.typ": cetz, d, wire, gbox, delta, nabla, TINT

#set page(width: auto, height: auto, margin: 0.8cm, fill: white)
#set text(font: "New Computer Modern", size: 11pt)

#let pic(body) = cetz.canvas(length: 0.95cm, body)

// A bare wire, and the copy-merge pair it is below.  `li`/`lo` are set so the two panels of a row
// start and end at the same x, or the `⊑` between them would not line up with either.
#let idwire = pic({ wire((0, 0), (2.4, 0)) })

#let copymerge = pic({
  wire((0, 0), (0.5, 0))
  delta((0.5, 0), li: 0, lo: 0.7, sp: 0.5)
  nabla((1.9, 0), li: 0.7, lo: 0.5)
})

// The whiskered box is tinted: the tint is what was added, everything black was already there.
#let boxonly(lab) = pic({
  wire((0, 0), (0.4, 0)); gbox((0.4, 0), lab, fill: TINT); wire((1.32, 0), (1.72, 0))
})

#let boxleft(lab) = pic({
  wire((0, 0), (0.4, 0)); gbox((0.4, 0), lab, fill: TINT); wire((1.32, 0), (1.7, 0))
  delta((1.7, 0), li: 0, lo: 0.7, sp: 0.5)
  nabla((3.1, 0), li: 0.7, lo: 0.5)
})

#let boxright(lab) = pic({
  wire((0, 0), (0.5, 0))
  delta((0.5, 0), li: 0, lo: 0.7, sp: 0.5)
  nabla((1.9, 0), li: 0.7, lo: 0.38)
  gbox((2.28, 0), lab, fill: TINT); wire((3.2, 0), (3.6, 0))
})

#let le = text(13pt)[⊑]
#let hint(body) = text(9.5pt, luma(105), body)

#align(center, grid(
  columns: 4, column-gutter: 12pt, row-gutter: 16pt, align: horizon + left,

  idwire, le, copymerge, hint[`𝟙 ⊑ ◁▷` — the unit of `◁ ⊣ ▷`, no argument in it],

  boxonly(`R`), le, boxleft(`R`),
    hint[whisker on the left: `R ⊑ R◁▷`, the unit of `·◁ ⊣ ·▷`],

  boxonly(`Z`), le, boxright(`Z`),
    hint[whisker on the right: `Z ⊑ ◁▷Z`, the unit of `▷· ⊣ ◁·`],
))

#v(8pt)
#set text(size: 10.5pt)
#align(center, box(width: 15cm)[
  Whiskering is the tinted box: the same box on both sides of the same `⊑`. Nothing else changes,
  and the inequality stays true because composition is monotone — `comp_mono_left`,
  `comp_mono_right`.
  \ #v(3pt)
  The top row compares two arrows `A ⟶ A`; the rows below compare two arrows out of wherever `R`
  and `Z` start. That is the whole difference between an adjunction of 1-cells and an adjunction of
  hom-posets: a box on the end.
])
