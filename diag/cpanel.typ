// cpanel.typ — the walker `scripts/circuit` emits into: a layout tree in, the CIRCUIT picture out.
// The exact analogue of the note's `dpanel` for the OTHER picture language (diag/CIRCUIT-GEN.md §2):
// a wire is an object, a box a morphism, composition runs left to right, and a product is two wires.
// The primitives are circuit.typ's — this file only places them.
//
// WIDTHS ARE MEASURED, NOT PASSED.  The note's `bx-*` tuples carry a hand-tuned width per label; a
// generated call cannot guess font metrics, so each label is measured here at render time (§4f) and
// the generator ships labels alone.  Every `pic` answers `(w, hh, body)`: its width, its half-height
// (what a tape has to be drawn round), and the cetz content, entering at `ys(nin)` and leaving at
// `ys(nout)`.  Branch equalisation — §4e's `w` — lives here and nowhere else.

#import "@preview/cetz:0.3.4"
#import "circuit.typ": gbox, wire, bend, dot as wiredot, tape, tape-join, BH, TINT, TAPEEDGE, lw
#import "draw.typ": lab, node
#import "note-style.typ": P

#let d = cetz.draw

// The note's own `frc` and `unionbox` geometry (allegory-axioms.typ), duplicated because the note is
// a DOCUMENT: importing it would evaluate 8000 lines of prose and close an import cycle the moment
// the note draws a generated panel.  Fold them the day those helpers move into circuit.typ.
#let frc(n) = $frac(#n, ∋)$
#let UIP = 0.4          // the pair's half-height — one strand of a product to the next
#let UOP = 0.3          // a `∪` copy's output port
#let UHH = 0.7          // a `∪` copy's half-height
#let UDY = UHH + 0.55   // copy separation, wider than the strands inside one copy
#let UM = 0.2           // region edge to the deepest box inside a copy
#let BRT = 1.6          // the bracket's branch height
#let CHPAD = 0.30       // `∪` region edge to the body inside it
#let CHFAN = 0.50       // how far outside the region the dashed fan reaches

#let CGAP = 0.34        // wire stub before the first box, between two boxes, and after the last
#let CPAD = 0.34        // label to box edge, each side
#let CNODE = 0.34       // the white inset `node` paints round a seam label, in canvas units
#let CPORT = 0.34       // wire end to the nearest edge of a port label
// A run carrying a two-line fraction label is raised WHOLE — one shared height, or the wire steps
// up and down between boxes (`boxrun`'s own rule, and why the note's `twrun` passes `TH`).
#let CTH = 1.2
#let FAN = (thickness: lw, paint: black, dash: "dashed")

#let cu(len, length) = len / length     // an absolute length in canvas units
#let ys(n) = if n == 0 { () } else { range(n).map(i => (n - 1) * UIP - 2 * UIP * i) }
#let lb(it) = if it.at("frac", default: false) { frc(raw(it.label)) } else { raw(it.label) }
#let tx(s) = text(10pt, raw(s))

#let pic(t, length) = {
  // ---- §3 rows 1-2, 7, 10, 15: one box.  A box spanning several strands is as tall as they are.
  if t.k == "box" {
    let n = calc.max(t.nin, t.nout)
    let h = if n > 1 { (n - 1) * 2 * UIP + 0.35 } else if t.at("frac", default: false) { CTH }
            else { BH }
    let w = cu(measure(lb(t)).width, length) + 2 * CPAD
    return (w: w, hh: h / 2, body: gbox((0, 0), lb(t), w: w, h: h, chamfer: t.chamfer,
      flip: t.flip, fill: if t.flip { TINT } else { none }))
  }
  // ---- §3 row 5: composition, ports glued, with the printed seams between the factors.
  if t.k == "seq" {
    let seam = (:)
    for s in t.seams { seam.insert(str(s.at(0)), s.at(1)) }
    let stub(x, n) = if n == 0 { (x, none) } else {
      (x + CGAP, ys(n).map(y => wire((x, y), (x + CGAP, y))).join())
    }
    let x = 0.0; let n = t.nin; let hh = 0.2; let body = ()
    for (i, it) in t.items.enumerate() {
      let (x2, s) = stub(x, n); x = x2; body.push(s)
      let p = pic(it, length)
      body.push(d.group({ d.translate((x, 0)); p.body }))
      x = x + p.w; n = it.nout; hh = calc.max(hh, p.hh)
      if str(i) in seam {
        let g = cu(measure(tx(seam.at(str(i)))).width, length) + 2 * CNODE
        body.push(wire((x, 0), (x + g, 0)))
        body.push(node(x + g / 2, 0, black, tx(seam.at(str(i))))); x = x + g
      }
    }
    let (x2, s) = stub(x, n); body.push(s)
    return (w: x2, hh: hh, body: body.join())
  }
  // ---- §3 row 6: a product is a vertical stack, one lane per ×-factor, padded to one right edge.
  if t.k == "stack" {
    let ps = t.lanes.map(l => pic(l, length))
    let mw = calc.max(..ps.map(p => p.w))
    return (w: mw, hh: (t.nin - 1) * UIP + calc.max(..ps.map(p => p.hh)),
      body: ps.zip(ys(t.nin)).map(((p, y)) =>
        d.group({ d.translate((0, y)); p.body; wire((p.w, 0), (mw, 0)) })).join())
  }
  // ---- §3 row 14: `⊸ x`, the constant.  Every input strand ends at a dot, then `x` is created.
  if t.k == "konst" {
    let p = pic(t.body, length)
    let body = ys(t.nin).map(y => { wire((0, y), (0.35, y)); wiredot((0.35, y)) }).join()
    return (w: 0.6 + p.w, hh: calc.max(p.hh, (t.nin - 1) * UIP + 0.1),
      body: { body; d.group({ d.translate((0.6, 0)); p.body }) })
  }
  // ---- §3 row 11: the `∪` region.  The input arrives once and a dashed fan hands it to BOTH
  // bodies, which are padded to a common right edge (§4e) and merge into one output.
  if t.k == "union" {
    let ps = t.bodies.map(b => pic(b, length))
    let mw = calc.max(..ps.map(p => p.w))
    let x0 = CHFAN; let x1 = CHFAN + mw + 2 * CHPAD; let hh = UDY + UHH + UM
    let body = {
      tape((x0, -hh), (x1, hh))
      lab((x0 + x1) / 2, hh + 0.3, TAPEEDGE)[`∪`]
      for (i, p) in ps.enumerate() {
        let s = if i == 0 { 1 } else { -1 }
        d.group({ d.translate((x0 + CHPAD, s * UDY)); p.body; wire((p.w, 0), (mw, 0)) })
        bend((x1 - CHPAD, s * UDY), (x1 + CHFAN, 0), stroke: FAN)
        for y in ys(t.nin) { bend((0, y), (x0 + CHPAD, s * UDY + y), stroke: FAN) }
      }
    }
    return (w: x1 + CHFAN, hh: hh + 0.3, body: body)
  }
  // ---- §3 row 13: the bracket at a polynomial object — tape fork, branches, tape join.  A branch
  // with no strand (the `𝟏` summand) still gets one fork stroke: that is what says it is reachable.
  let ps = t.bodies.map(b => pic(b, length))
  let oys = (BRT, -BRT)
  // A branch whose source object HAS strands names them, and buys the room for the labels with a
  // lead — the fan hands the pair over unlabelled, so the fork is the only place to say which is which.
  let leads = t.ports.map(q => if q.len() > 0 { 0.7 } else { 0.0 })
  let mw = calc.max(..ps.zip(leads).map(((p, l)) => p.w + l))
  let xf = 1.26; let xj = xf + mw + 0.7
  // The tape is drawn round what the branches actually reach, top and bottom apart: the `𝟏` summand
  // is one small box where the pair below it carries a whole `∪` region.
  let top = calc.max(..ps.zip(oys).map(((p, o)) => o + p.hh)) + 0.15
  let bot = calc.min(..ps.zip(oys).map(((p, o)) => o - p.hh)) - 0.15
  let st = (thickness: 1.4pt, paint: TAPEEDGE)
  let body = {
    tape((0.34, bot), (xj, top))
    wire((0, 0), (0.34, 0))
    for (i, p) in ps.enumerate() {
      let oy = oys.at(i); let ports = t.ports.at(i); let lead = leads.at(i)
      for y in (if ports.len() > 0 { ys(ports.len()) } else { (0.0,) }) {
        d.bezier((0.56, 0), (xf, oy + y), (0.98, 0), (0.98, oy + y), stroke: st)
      }
      for (j, y) in ys(ports.len()).enumerate() {
        wire((xf, oy + y), (xf + lead, oy + y))
        lab(xf + lead / 2, oy + y + 0.32, black, tx(ports.at(j)))
      }
      d.group({ d.translate((xf + lead, oy)); p.body; wire((p.w, 0), (mw - lead, 0)) })
    }
    tape-join((xj, 0), sp: BRT, len: 0.7)
  }
  (w: xj, hh: calc.max(top, -bot), body: body)
}

// The panel: the tree's own picture, with the ports named at both ends.  `src`/`tgt` are one label
// per STRAND — a product is two wires, so it is two labels, never one reading `A×[A]`.
#let cbody(t, length) = {
  let p = pic(t, length)
  p.body
  for (i, y) in ys(t.nin).enumerate() {
    lab(-CPORT - cu(measure(tx(t.src.at(i))).width, length) / 2, y, black, tx(t.src.at(i)))
  }
  for (i, y) in ys(t.nout).enumerate() {
    lab(p.w + CPORT + cu(measure(tx(t.tgt.at(i))).width, length) / 2, y, black, tx(t.tgt.at(i)))
  }
}

#let cpanel(tree, s: 74%, length: 0.8cm, cert: (:)) = {
  context P(cetz.canvas(length: length, cbody(tree, length)), s: s)
  // The drawn lists want the note's `plain` to serialise; the cert is the part that is text already.
  metadata((kind: "circuit", helper: "cpanel", cert: cert))
}
