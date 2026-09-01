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
#import "circuit.typ": gbox, wire, bend, delta, nabla, bang, cut, tape, tape-join, BH, TINT, TAPEEDGE, lw
#import "draw.typ": lab, node
#import "note-style.typ": P, TYCOL

#let d = cetz.draw

// The note's own `frc` and `unionbox` geometry (allegory-axioms.typ), duplicated because the note is
// a DOCUMENT: importing it would evaluate 8000 lines of prose and close an import cycle the moment
// the note draws a generated panel.  Fold them the day those helpers move into circuit.typ.
#let frc(n) = $frac(#n, ∋)$
#let CBAR = 0.13        // the functorial box's two bars, as the note's own `banana` spaces them
// MELLIÈS' functorial box, the note's `banana`, here for the reason `frc` is.  A bar is where the
// type changes, so the tick closes the pair on the side the fold's own object is not.
#let banana(x, yh, right: false, invert: false) = {
  let s = if right { -1 } else { 1 }
  let st = (thickness: lw, paint: if invert { white } else { black })
  d.line((x, -yh), (x, yh), stroke: st)
  d.line((x + s * CBAR, -yh), (x + s * CBAR, yh), stroke: st)
  d.line((x, yh), (x + s * 0.3, yh), stroke: st)
  d.line((x, -yh), (x + s * 0.3, -yh), stroke: st)
}
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
#let CPORT = 0.05       // wire end to its type label: a hairline, so the glyph does not overprint the stroke
#let CLEAD = 0.34       // wire run past each side of a label sitting above it, so it clears the bar and the box
#let CABOVE = 0.25      // a label sitting above its wire: text centre to the stroke
// A run carrying a two-line fraction label is raised WHOLE — one shared height, or the wire steps
// up and down between boxes (`boxrun`'s own rule, and why the note's `twrun` passes `TH`).
#let CTH = 1.2
#let FAN = (thickness: lw, paint: black, dash: "dashed")
#let CSP = 0.34         // a copy dot to the lane it opens, and a merge dot to the lane it closes
#let CDL = 0.35         // the last box of a guard to the dot that discards it
#let CBACK = 0.5        // a guarded body's output back up to the branch's own port height

#let cu(len, length) = len / length     // an absolute length in canvas units
#let ys(n) = if n == 0 { () } else { range(n).map(i => (n - 1) * UIP - 2 * UIP * i) }
#let lb(it) = if it.at("frac", default: false) { frc(raw(it.label)) } else { raw(it.label) }
#let tx(s) = text(10pt, raw(s))

// `invert` is the Peirce cut's axis, not a decoration: inside a `cut` the page is black, so every
// wire, dot and box drawn there has to be light-on-dark.  Only a lane the walker calls `flat` — a
// run of boxes, stacks and projections — is ever asked for it; a tape keeps its own colours.
#let pic(t, length, invert: false) = {
  // ---- §3 rows 1-2, 7, 10, 15: one box.  A box spanning several strands is as tall as they are.
  if t.k == "box" {
    let n = calc.max(t.nin, t.nout)
    let h = if n > 1 { (n - 1) * 2 * UIP + 0.35 } else if t.at("frac", default: false) { CTH }
            else { BH }
    let w = cu(measure(lb(t)).width, length) + 2 * CPAD
    return (w: w, hh: h / 2, body: gbox((0, 0), lb(t), w: w, h: h, chamfer: t.chamfer,
      flip: t.flip, invert: invert, fill: if t.flip { TINT } else { none }))
  }
  // ---- §3 row 5: composition, ports glued, with the printed seams between the factors.
  if t.k == "seq" {
    let seam = (:)
    for s in t.seams { seam.insert(str(s.at(0)), s.at(1)) }
    let stub(x, n) = if n == 0 { (x, none) } else {
      (x + CGAP, ys(n).map(y => wire((x, y), (x + CGAP, y), invert: invert)).join())
    }
    let x = 0.0; let n = t.nin; let hh = 0.2; let body = ()
    for (i, it) in t.items.enumerate() {
      let (x2, s) = stub(x, n); x = x2; body.push(s)
      let p = pic(it, length, invert: invert)
      body.push(d.group({ d.translate((x, 0)); p.body }))
      x = x + p.w; n = it.nout; hh = calc.max(hh, p.hh)
      if str(i) in seam {
        let g = cu(measure(tx(seam.at(str(i)))).width, length) + 2 * CNODE
        body.push(wire((x, 0), (x + g, 0), invert: invert))
        body.push(node(x + g / 2, 0, TYCOL, tx(seam.at(str(i))))); x = x + g
      }
    }
    let (x2, s) = stub(x, n); body.push(s)
    return (w: x2, hh: hh, body: body.join())
  }
  // ---- §3 row 6: a product is a vertical stack, one lane per ×-factor, padded to one right edge.
  if t.k == "stack" {
    let ps = t.lanes.map(l => pic(l, length, invert: invert))
    let mw = calc.max(..ps.map(p => p.w))
    return (w: mw, hh: (t.nin - 1) * UIP + calc.max(..ps.map(p => p.hh)),
      body: ps.zip(ys(t.nin)).map(((p, y)) =>
        d.group({ d.translate((0, y)); p.body; wire((p.w, 0), (mw, 0), invert: invert) })).join())
  }
  // ---- §3 row 3: a projection.  The factors it drops END AT A DOT and the one it keeps crosses to
  // the port it leaves on — a product is already two wires, so this costs no box at all.
  if t.k == "proj" {
    let lo = t.keep.slice(0, t.at).sum(default: 0)
    let ins = ys(t.nin); let outs = ys(t.nout)
    let body = range(t.nin).map(i => if i >= lo and i < lo + t.keep.at(t.at) {
        bend((0, ins.at(i)), (0.75, outs.at(i - lo)), k: 0.5, invert: invert)
      } else { bang((CDL, ins.at(i)), li: CDL, invert: invert) }).join()
    return (w: 0.75, hh: calc.max(t.nin, t.nout, 1) * UIP - UIP, body: body)
  }
  // ---- §3 row 14: `⊸ x`, the constant.  Every input strand ends at a dot, then `x` is created.
  if t.k == "konst" {
    let p = pic(t.body, length, invert: invert)
    let body = ys(t.nin).map(y => bang((0.35, y), li: 0.35, invert: invert)).join()
    return (w: 0.6 + p.w, hh: calc.max(p.hh, (t.nin - 1) * UIP + 0.1),
      body: { body; d.group({ d.translate((0.6, 0)); p.body }) })
  }
  // ---- §3 row 12: `x∩y`.  Copy every strand, run BOTH lanes, merge.  `∇=Δ°` forces the two to
  // carry the same value, and that is the whole of the intersection: no box says `∩`.
  if t.k == "cap" {
    let ps = t.lanes.map(l => pic(l, length, invert: invert))
    let mw = calc.max(..ps.map(p => p.w))
    let mh = calc.max(..ps.map(p => p.hh))
    let sp = mh + 0.22
    let x1 = CSP + mw + CSP
    let body = {
      for (i, p) in ps.enumerate() {
        let s = if i == 0 { 1 } else { -1 }
        d.group({
          d.translate((CSP, s * sp)); p.body
          for y in ys(t.nout) { wire((p.w, y), (mw, y), invert: invert) }
        })
      }
      for y in ys(t.nin) { delta((0, y), li: 0, lo: CSP, sp: sp, invert: invert) }
      for y in ys(t.nout) { nabla((x1, y), li: CSP, lo: 0, sp: sp, invert: invert) }
    }
    return (w: x1, hh: sp + mh, body: body)
  }
  // ---- §3 row 17: `⦇α⦈` as MELLIÈS' FUNCTORIAL BOX.  Nothing crosses the LEFT pair of bars: the
  // input arrives at them and the algebra's own strands start inside, and that break IS the
  // recursion.  The algebra's output is the fold's, so it runs out through the right pair.
  if t.k == "cata" {
    let p = pic(t.body, length, invert: invert)
    let yh = calc.max(p.hh, (t.nin - 1) * UIP) + 0.28
    let ld = calc.max(..t.port.map(s => cu(measure(tx(s)).width, length))) + 2 * CLEAD
    let x0 = CBAR + ld
    let xr = x0 + p.w + CBAR
    // The CARRIER types the fold's OUTPUT WIRE, so it sits on that wire's own stub, exactly like
    // an input port label sits on its wire (below) — never floating over the box.  `scripts/circuit`
    // sends `label: none` when the panel or the next box already names that same type at this
    // wire's end — drawing it twice would put `[A]` on the wire and its end (§13.3.3b).
    let og = if t.label == none { CGAP } else { cu(measure(tx(t.label)).width, length) + 2 * CLEAD }
    let body = {
      banana(0, yh, invert: invert)
      banana(xr + CBAR, yh, right: true, invert: invert)
      for (i, y) in ys(t.body.nin).enumerate() {
        wire((CBAR, y), (x0, y), invert: invert)
        lab(CBAR + ld / 2, y + CABOVE, if invert { white } else { TYCOL }, tx(t.port.at(i)))
      }
      d.group({ d.translate((x0, 0)); p.body })
      for y in ys(t.nout) {
        wire((x0 + p.w, y), (xr + CBAR + og, y), invert: invert)
        if t.label != none {
          lab(xr + CBAR + og / 2, y + CABOVE, if invert { white } else { TYCOL }, tx(t.label))
        }
      }
    }
    return (w: xr + CBAR + og, hh: yh, body: body)
  }
  // ---- §3 row 16: `(g→x,y)`.  A `∪` of two RESTRICTED branches: each copies the input, runs the
  // guard on one copy and ends it at a dot — that composite is `dom(g)` — and its body on the
  // other.  `¬dom(g)` is that same guard inside a Peirce CUT, negation having no wiring of its own.
  if t.k == "cond" {
    let arm(i, neg) = {
      let pg = pic(t.guard, length, invert: neg)
      let pb = pic(t.bodies.at(i), length, invert: invert)
      let gh = calc.max(pg.hh, (t.guard.nin - 1) * UIP, (t.guard.nout - 1) * UIP) + 0.2
      let gw = CBAR + pg.w + CDL + CBAR
      let sp = calc.max(gh, pb.hh + 0.22, 0.5)
      let mw = calc.max(gw, pb.w)
      let body = {
        for y in ys(t.nin) { delta((0, y), li: 0, lo: CSP, sp: sp, invert: invert) }
        if neg { cut((CSP, sp - gh), (CSP + gw, sp + gh)) }
        for y in ys(t.guard.nin) { wire((CSP, sp + y), (CSP + CBAR, sp + y), invert: neg) }
        d.group({
          d.translate((CSP + CBAR, sp)); pg.body
          for y in ys(t.guard.nout) { bang((pg.w + CDL, y), li: CDL, invert: neg) }
        })
        d.group({
          d.translate((CSP, -sp)); pb.body
          for y in ys(t.nout) { wire((pb.w, y), (mw, y), invert: invert) }
        })
        for y in ys(t.nout) { bend((CSP + mw, -sp + y), (CSP + mw + CBACK, y), invert: invert) }
      }
      (w: CSP + mw + CBACK, hh: sp + calc.max(gh, pb.hh), body: body)
    }
    let ps = (arm(0, false), arm(1, true))
    let mw = calc.max(..ps.map(p => p.w))
    let mh = calc.max(..ps.map(p => p.hh))
    let x0 = CHFAN; let x1 = CHFAN + mw + 2 * CHPAD; let hh = mh + 0.35 + mh + UM
    let body = {
      tape((x0, -hh), (x1, hh))
      lab((x0 + x1) / 2, hh + 0.3, TAPEEDGE)[`→`]
      for (i, p) in ps.enumerate() {
        let s = if i == 0 { 1 } else { -1 } * (mh + 0.35)
        d.group({
          d.translate((x0 + CHPAD, s)); p.body
          for y in ys(t.nout) { wire((p.w, y), (mw, y), invert: invert) }
        })
        for y in ys(t.nout) { bend((x1 - CHPAD, s + y), (x1 + CHFAN, y), stroke: FAN) }
        for y in ys(t.nin) { bend((0, y), (x0 + CHPAD, s + y), stroke: FAN) }
      }
    }
    return (w: x1 + CHFAN, hh: hh + 0.3, body: body)
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
        lab(xf + lead / 2, oy + y + CABOVE, TYCOL, tx(ports.at(j)))
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
    lab(-CPORT - cu(measure(tx(t.src.at(i))).width, length) / 2, y, TYCOL, tx(t.src.at(i)))
  }
  for (i, y) in ys(t.nout).enumerate() {
    lab(p.w + CPORT + cu(measure(tx(t.tgt.at(i))).width, length) / 2, y, TYCOL, tx(t.tgt.at(i)))
  }
}

#let cpanel(tree, s: 74%, length: 0.8cm, cert: (:)) = {
  context P(cetz.canvas(length: length, cbody(tree, length)), s: s)
  // The drawn lists want the note's `plain` to serialise; the cert is the part that is text already.
  metadata((kind: "circuit", helper: "cpanel", cert: cert))
}
