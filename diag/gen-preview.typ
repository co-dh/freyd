// SCRATCH.  `scripts/diagram`'s output, pasted unedited, so the calls it prints can be looked at as
// pictures and swept by `scripts/scanline diag/gen-preview.typ` through the real helper.
// Not part of `make p`: nothing in the note reads it.
#import "allegory-axioms.typ": dpanel
#set page(width: auto, height: auto, margin: 0.8cm, fill: white)
#set text(11pt)

#stack(dir: ltr, spacing: 18pt,

// 13.3.3b.1  α prefix list(p) — the `list` wire OPENED out of the object wire at `prefix`
dpanel(4, 5.7, 2.85,
  ((0.55, "top", 3, none, none), (1.7, 2, "bot", none, none)),
  ((3, [`α`]), (2, [`prefix`]), (1, [`p`])),
  ((0.55, [`F`]), (2.85, [`[A]`])),
  ((1.7, [`list`]), (2.85, [`A`])),
  names: true, s: 100%,
  cert: (expect: "α prefix list(p)", src: "F([A])", tgt: "[A]")),

// 13.4.4a.2  ⦇S⦈%∋ E(choose) est(R°) — the `E` wire born and eaten by beads on the object wire
dpanel(4, 5.7, 2.85,
  ((0.55, "top", 3, none, none), (1.7, 3, 1, [`E`], none)),
  ((3, [`⦇S⦈%∋`]), (2, [`choose`]), (1, [`est(R°)`])),
  ((0.55, [`tree`]), (2.85, [`A`])),
  ((2.85, [`[A]`]),),
  s: 100%,
  cert: (expect: "⦇S⦈%∋ E(choose) est(R°)", src: "tree(A)", tgt: "[A]")),

// 13.4.4a.6  S%∋ est((R×R)°) — the bar that says how far the bead's source reaches
dpanel(3, 6.85, 4,
  ((0.55, "top", 2, none, none), (1.7, "top", 2, none, none), (2.85, "top", "bot", none, none)),
  ((2, [`S%∋`]), (1, [`est((R×R)°)`], black, 2.85)),
  ((0.55, [`A×−`]), (1.7, [`list`]), (2.85, [`Δ`]), (4, [`[A]`])),
  ((2.85, [`Δ`]), (4, [`[A]`])),
  s: 100%,
  cert: (expect: "S%∋ est((R×R)°)", src: "A×[[A]×[A]]", tgt: "[A]×[A]")),

// 13.4.4a.8  π₂ list(choose%∋ est(R°)) concat — two beads at two heights under one `list` wire
dpanel(5, 6.85, 4,
  ((0.55, "top", 4, none, none), (1.7, "top", 1, none, none), (2.85, "top", 4, none, none)),
  ((4, [`π₂`]), (3, [`choose%∋`]), (2, [`est(R°)`]), (1, [`concat`])),
  ((0.55, [`A×−`]), (1.7, [`list`]), (2.85, [`Δ`]), (4, [`[A]`])),
  ((4, [`[A]`]),),
  s: 100%,
  cert: (expect: "π₂ list(choose%∋ est(R°)) concat", src: "A×[[A]×[A]]", tgt: "[A]")),
)
