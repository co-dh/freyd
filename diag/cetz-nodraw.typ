// cetz, with one switch: `--input nodraw=1` makes every canvas an empty box.
//
// WHY.  Every panel helper (`dpanel`, `cpanel`) computes the lists it emits as `#metadata`
// OUTSIDE the canvas and then draws from them, so `typst query` — which is all `scanline`,
// `diagram --roundtrip` and `hm-check` ever want — needs none of the ink.  Measured on the note:
// 12.9 s with the 646 canvases, 0.5 s without, and the queried metadata is byte-identical.
// A module, not a dictionary: `cetz.canvas(..)` is a method call, and a dict field cannot be one.
//
// NEVER pass `nodraw` to a `typst compile` that produces a PDF — the pages would come out blank,
// and `pic-meta`'s crop boxes (`./scripts/book pic`) would be measured off empty boxes.
#import "@preview/cetz:0.3.4" as cetzlib

#let draw = cetzlib.draw
#let d = draw
// The two conventions draw with the same pen: a wire is a wire whether it carries an object
// (`circuit.typ`) or a functor (`hm.typ`).  Here, so neither of those files imports the other.
#let lw = 1.1pt         // wire thickness            (S2_124.typ)
#let NODRAW = "nodraw" in sys.inputs
// The placeholder has a NONZERO size on purpose: `hchain(fill: true)` divides by the summed width of
// the pictures it packs, and a zero-width box makes that a division by zero rather than a blank page.
// `--input cdscan=1`: one queryable mark per canvas, ahead of the marks `draw.typ`'s `ar`/`node`
// drop inside it, so a gate can cut the note's mark stream into CANVASES — the unit a commutative
// diagram is one of — without reading the note's source as text.
#let CDSCAN = "cdscan" in sys.inputs
// The mark goes INSIDE the canvas, as its first drawn element: wrapping the canvas in a sequence
// changes what the caller gets back, and `pair`'s `hm-sepx` reads its panel's content tree.
#let canvas(..a) = if NODRAW { box(width: 2cm, height: 1cm) } else if CDSCAN {
  // cetz flattens no nesting: a body is an ARRAY of element functions, so the mark is concatenated
  // onto it rather than tupled with it.
  let body = a.pos().at(0)
  cetzlib.canvas(draw.content((0, 0), [#metadata((kind: "cd", el: "canvas"))])
    + (if type(body) == array { body } else { (body,) }), ..a.named())
} else { cetzlib.canvas(..a) }
