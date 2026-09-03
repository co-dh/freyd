// SCRATCH.  `scripts/diagram`'s output, pasted unedited, so the calls it prints can be looked at as
// pictures and swept by `scripts/scanline diag/gen-preview.typ` through the real helper.
// Not part of `make p`: nothing in the note reads it.
#import "allegory-axioms.typ": dpanel
#set page(width: auto, height: auto, margin: 0.8cm, fill: white)
#set text(11pt)

// 13.5.3's five panels, regenerated.  The object edge now SLOPES: an arrow of the base category
// rides it (`est(R)`), which is IntroString's condition for the sloped edge, and it is one straight
// line across the whole picture — the run is the lanes' span, the book's 2:1 being too wide here.
#stack(dir: ltr, spacing: 26pt,

// ca1  paths est(R)
dpanel(3, 8, 5.15,
  ((0.55, 2, 1, [`E`], none), (1.7, 2, "bot", none, none), (0.55, "top", 2, none, none), (1.7, "top", 2, none, none)),
  ((2, [`paths`], black, 0.55, 1.125), (1, [`est(R)`], black, 0.55)),
  ((0.55, [`L`]), (1.7, [`N`]), (5.15, [`Nat`])),
  ((1.7, [`L`]), (5.15, [`Nat`])),
  opath: ((5.15, 3), (2.85, 1), (2.85, 0))),

// ca2  ⦇generate⦈setify union est(R)
dpanel(5, 10.3, 7.45,
  ((1.125, 2, 1, [`E`], none), (0.55, 3, 2, [`E`], none), (0.55, 4, 3, [`N`], none), (1.7, 4, 2, [`E`], none), (2.85, 4, "bot", none, none), (1.125, "top", 4, none, none), (2.275, "top", 4, none, none)),
  ((4, [`⦇generate⦈`], black, 1.125, 1.7), (3, [`setify`], black, 0.55, 0.55), (2, [`union`], black, 0.55, 1.125), (1, [`est(R)`], black, 1.125)),
  ((1.125, [`L`]), (2.275, [`N`]), (7.45, [`Nat`])),
  ((2.85, [`L`]), (7.45, [`Nat`])),
  opath: ((7.45, 5), (4, 1), (4, 0))),

// ca3  ⦇generate⦈setify P(est(R))est(R)
dpanel(5, 10.3, 7.45,
  ((0.55, 3, 1, [`E`], none), (0.55, 4, 3, [`N`], none), (1.7, 4, 2, [`E`], none), (2.85, 4, "bot", none, none), (1.125, "top", 4, none, none), (2.275, "top", 4, none, none)),
  ((4, [`⦇generate⦈`], black, 1.125, 1.7), (3, [`setify`], black, 0.55, 0.55), (2, [`est(R)`], black, 1.7), (1, [`est(R)`], black, 0.55)),
  ((1.125, [`L`]), (2.275, [`N`]), (7.45, [`Nat`])),
  ((2.85, [`L`]), (7.45, [`Nat`])),
  opath: ((7.45, 5), (4, 2), (4, 0))),

// ca4  ⦇generate⦈N(est(R))setify est(R)
dpanel(5, 10.3, 7.45,
  ((0.55, 2, 1, [`E`], none), (0.55, 4, 2, [`N`], none), (1.7, 4, 3, [`E`], none), (2.85, 4, "bot", none, none), (1.125, "top", 4, none, none), (2.275, "top", 4, none, none)),
  ((4, [`⦇generate⦈`], black, 1.125, 1.7), (3, [`est(R)`], black, 1.7), (2, [`setify`], black, 0.55, 0.55), (1, [`est(R)`], black, 0.55)),
  ((1.125, [`L`]), (2.275, [`N`]), (7.45, [`Nat`])),
  ((2.85, [`L`]), (7.45, [`Nat`])),
  opath: ((7.45, 5), (4, 3), (4, 0))),

// ca5  ⦇Q⦈setify est(R)
dpanel(4, 8, 5.15,
  ((0.55, 2, 1, [`E`], none), (0.55, 3, 2, [`N`], none), (1.7, 3, "bot", none, none), (0.55, "top", 3, none, none), (1.7, "top", 3, none, none)),
  ((3, [`⦇Q⦈`], black, 0.55, 1.125), (2, [`setify`], black, 0.55, 0.55), (1, [`est(R)`], black, 0.55)),
  ((0.55, [`L`]), (1.7, [`N`]), (5.15, [`Nat`])),
  ((1.7, [`L`]), (5.15, [`Nat`])),
  opath: ((5.15, 4), (2.85, 1), (2.85, 0))),
)
