#import "../note-prelude.typ": *
#show: note-chapter.with(8)
// note-split: chapter 8 — this header is written by scripts/note-split and stripped by scripts/note-join
#import "../shared-laws.typ": *
= `/` is all of

#disp[#definition[
#align(center, `x (R/S) y⟺∀p. y S p→x R p`)
#align(center, `x (S\R) y⟺∀p. p S x→p R y`)
#align(center, `/compares images: S(y)⊆R(x).   \ compares preimages: S°(x)⊆R°(y).`)
#align(center, `example: A admires,H hates,W works for`)
#align(center, `x (A/H) y — x admires everyone y hates.`)
#align(center, `x (H\A) y — everyone who hates x admires y.`)
// lean:Freyd.S2_30_Example.over@fb2a984b
]]<div-defn>


== `(R/S)(S/W)⊑R/W`


#disp[#leang("Freyd.S2_30.Example.A+Freyd.S2_30.Example.H+Freyd.S2_30.Example.W+Freyd.S2_30.Example.AH+Freyd.S2_30.Example.HW+Freyd.S2_30.Example.AW",
  cols: (
    (type: "Admirer", x: -9.6, ys: (x: 1.6, "x'": -1.6), col: (INDUCED, SLACK)),
    (type: "Person", x: -4.8, ys: (a: 2.4, b: 0.8, c: -0.8, d: -2.4)),
    (type: "Hater", x: 0, ys: (y: 1.6, "y'": -1.6), col: (INDUCED, SLACK), pad: 0.8),
    (type: "Person", x: 4.8, ys: (a: 2.4, b: 0.8, c: -0.8, d: -2.4)),
    (type: "Worker", x: 9.6, ys: (z: 0), col: INDUCED)),
  rels: (
    A: (on: ((0, 1),), col: (INDUCED, SLACK), s1: 1.05),
    H: (on: ((2, 1), (2, 3)), col: (INDUCED, SLACK), s1: 1.05),
    W: (on: ((4, 3),), col: INDUCED, s1: 1.05),
    AH: (arc: 1, label: [`A/H` admires all]),
    HW: (arc: 1, label: [`H/W` hates all]),
    AW: (arc: -1, label: [`A/W` admires all], col: GIVEN1, h: 5.4, cx: 8)),
  notes: (((-9.6, 3.9), text(9.5pt, luma(60))[`A` — `x` admires]),
    ((0, 3.9), text(9.5pt, luma(60))[`H` — `y` hates]),
    ((9.6, 3.9), text(9.5pt, luma(60))[`W` — `z` works for])))]<div-comp-pic>

// The whole of each quotient in one line of English, laid out as the law reads: the two legs of the
// path first, the arrow they are contained in last.
#disp[#block(inset: (top: 2pt), text(10.5pt)[
  `x (A/H) y` — `x` admires everyone `y` hates \
  `y (H/W) z` — `y` hates everyone `z` works for \
  `x (A/W) z` — `x` admires everyone `z` works for
])]<div-comp-gloss>

`(A/H)(H/W)` is a path: `x` → `y` → `z`, and that is all of it. `A/W` also holds of
`x'`, who admires everyone `z` works for — but `x'` does not admire everyone anybody
hates, so nothing composes to it. The missing path is exactly the strictness of
// Boxed so the line breaker cannot split the law after a `/` — it lands at the end of the paragraph.
#box[`(R/S)(S/W)⊑R/W`].

#law-div-laws

Fifteen laws, fifteen pictures, and not one shows a generator: `∩`, `∪`, `°` and composition are what
the Frobenius generators build, and `/` is none of those — it is posited, with nothing to unfold.

#pagebreak(weak: true)
