// cetz, with one switch: `--input nodraw=1` makes every canvas an empty box.
//
// WHY.  Every panel helper (`dpanel`, `tpan`, `cpanel`) computes the lists it emits as `#metadata`
// OUTSIDE the canvas and then draws from them, so `typst query` — which is all `scanline`,
// `diagram --roundtrip` and `hm-check` ever want — needs none of the ink.  Measured on the note:
// 12.9 s with the 646 canvases, 0.5 s without, and the queried metadata is byte-identical.
// A module, not a dictionary: `cetz.canvas(..)` is a method call, and a dict field cannot be one.
//
// NEVER pass `nodraw` to a `typst compile` that produces a PDF — the pages would come out blank,
// and `pic-meta`'s crop boxes (`./scripts/book pic`) would be measured off empty boxes.
#import "@preview/cetz:0.3.4" as cetzlib

#let draw = cetzlib.draw
#let NODRAW = "nodraw" in sys.inputs
// The placeholder has a NONZERO size on purpose: `hchain(fill: true)` divides by the summed width of
// the pictures it packs, and a zero-width box makes that a division by zero rather than a blank page.
#let canvas(..a) = if NODRAW { box(width: 2cm, height: 1cm) } else { cetzlib.canvas(..a) }
