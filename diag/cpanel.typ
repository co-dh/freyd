// cpanel.typ — the walker `scripts/circuit` emits into: a layout tree in, the CIRCUIT picture out.
// The exact analogue of the note's `dpanel` for the OTHER picture language (diag/CIRCUIT-GEN.md §2):
// a wire is an object, a box a morphism, composition runs left to right, and a product is two wires.
// The primitives are circuit.typ's — this file only places them.
//
// WIDTHS ARE MEASURED, NOT PASSED.  The note's `bx-*` tuples carry a hand-tuned width per label; a
// generated call cannot guess font metrics, so each label is measured here at render time (§4f) and
// the generator ships labels alone.

#import "@preview/cetz:0.3.4"
#import "circuit.typ": gbox, wire, BH, TINT
#import "draw.typ": lab, node
#import "note-style.typ": P

// The note's own `frc` (allegory-axioms.typ), so a generated call renders OUTSIDE the note too —
// the label of `x%∋` is the only thing an emitted `#cpanel` needs that circuit.typ does not export.
#let frc(n) = $frac(#n, ∋)$

#let CGAP = 0.34        // wire stub before the first box, between two boxes, and after the last
#let CPAD = 0.34        // label to box edge, each side
#let CNODE = 0.34       // the white inset `node` paints round a seam label, in canvas units
#let CPORT = 0.34       // wire end to the nearest edge of a port label
// A run carrying a two-line fraction label is raised WHOLE — one shared height, or the wire steps
// up and down between boxes (`boxrun`'s own rule, and why the note's `twrun` passes `TH`).
#let CTH = 1.2

#let cu(len, length) = len / length     // an absolute length in canvas units

// `seq` — composition, ports glued (§3 row 5).  `items` are box nodes left to right; `seams` names
// the interior objects that get printed, `(i, label)` = after item `i`.  `src`/`tgt` are the ports.
#let cseq(tree, length) = {
  let items = tree.items
  let ws = items.map(it => cu(measure(it.label).width, length) + 2 * CPAD)
  let h = if items.any(it => it.at("frac", default: false)) { CTH } else { BH }
  let seam = (:)
  for s in tree.at("seams", default: ()) { seam.insert(str(s.at(0)), s.at(1)) }
  let x = 0.0
  for (i, it) in items.enumerate() {
    wire((x, 0), (x + CGAP, 0)); x = x + CGAP
    let flip = it.at("flip", default: false)
    gbox((x, 0), it.label, w: ws.at(i), h: h, chamfer: it.at("chamfer", default: true),
      flip: flip, fill: if flip { TINT } else { none })
    x = x + ws.at(i)
    if str(i) in seam {
      let l = text(10pt, seam.at(str(i)))
      let g = cu(measure(l).width, length) + 2 * CNODE
      wire((x, 0), (x + g, 0)); node(x + g / 2, 0, black, seam.at(str(i))); x = x + g
    }
  }
  wire((x, 0), (x + CGAP, 0))
  lab(-CPORT - cu(measure(text(10pt, tree.src)).width, length) / 2, 0, black, tree.src)
  lab(x + CGAP + CPORT + cu(measure(text(10pt, tree.tgt)).width, length) / 2, 0, black, tree.tgt)
}

#let cpanel(tree, s: 74%, length: 0.8cm, cert: (:)) = {
  context P(cetz.canvas(length: length, cseq(tree, length)), s: s)
  // The drawn lists want the note's `plain` to serialise; the cert is the part that is text already.
  metadata((kind: "circuit", helper: "cpanel", cert: cert))
}
