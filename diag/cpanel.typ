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
#import "circuit.typ": gbox, wire, bend, delta, nabla, bang, tape, tape-join, BH, TINT, TAPEEDGE, lw
#import "draw.typ": lab
#import "note-style.typ": P, TYCOL

#let d = cetz.draw

// The note's own `frc` and `unionbox` geometry (allegory-axioms.typ), duplicated because the note is
// a DOCUMENT: importing it would evaluate 8000 lines of prose and close an import cycle the moment
// the note draws a generated panel.  Fold them the day those helpers move into circuit.typ.
#let frc(n) = $frac(#n, ∋)$
#let CBAR = 0.13        // the functorial box's two bars, as the note's own `banana` spaces them
// MELLIÈS' functorial box, the note's `banana`, here for the reason `frc` is.  A bar is where the
// type changes, so the tick closes the pair on the side the fold's own object is not.
#let banana(x, yh, right: false) = {
  let s = if right { -1 } else { 1 }
  let st = (thickness: lw, paint: black)
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
#let CPORT = 0.4        // how far a wire runs INTO its type label, as a fraction of one mono advance: where
                        // the ink of `[`/`]` starts (measured); `A`/`E`/`F` are wider there and hide the rest
#let CLEAD = 0.34       // wire run past each side of a label sitting above it, so it clears the bar and the box
#let CABOVE = 0.25      // a label sitting above its wire: text centre to the stroke
// A run carrying a two-line fraction label is raised WHOLE — one shared height, or the wire steps
// up and down between boxes (`boxrun`'s own rule, and why the note's `twrun` passes `TH`).
#let CTH = 1.2
#let FAN = (thickness: lw, paint: black, dash: "dashed")
#let CSP = 0.34         // a copy dot to the lane it opens, and a merge dot to the lane it closes
#let CDL = 0.35         // the last box of a guard to the dot that discards it

#let cu(len, length) = len / length     // an absolute length in canvas units
#let ys(n) = if n == 0 { () } else { range(n).map(i => (n - 1) * UIP - 2 * UIP * i) }
// A `x%∋` INSIDE a label (`E((prefix sum)%∋ est(≥))`) is the fraction the note writes by hand: the
// numerator is the parenthesised group, or the one word, before the `%∋`.
#let lbl(s) = {
  let cs = s.clusters()
  let i = cs.position(c => c == "%")
  if i == none or cs.at(i + 1, default: none) != "∋" { return raw(s) }
  let j = i - 1
  let pre(k) = raw(cs.slice(0, k).sum(default: ""))
  let rest = lbl(cs.slice(i + 2).sum(default: ""))
  if cs.at(j) == ")" {
    let depth = 0
    while true {
      depth = depth + (if cs.at(j) == ")" { 1 } else if cs.at(j) == "(" { -1 } else { 0 })
      if depth == 0 { break }
      j = j - 1
    }
    return pre(j) + frc(raw(cs.slice(j + 1, i - 1).sum(default: ""))) + rest
  }
  while j > 0 and cs.at(j - 1) not in (" ", "(") { j = j - 1 }
  pre(j) + frc(raw(cs.slice(j, i).sum(default: ""))) + rest
}
#let lb(it) = if it.at("frac", default: false) { frc(lbl(it.label)) } else { lbl(it.label) }
#let tall(it) = it.at("frac", default: false) or it.label.contains("%∋")
#let tx(s) = text(10pt, raw(s))
#let into(length) = CPORT * cu(measure(tx("[")).width, length)  // `measure` is the advance box, not the ink

// The dashed fan into and out of a region holding alternatives, one arm per height in `ss`, after
// a straight `lead` at each port (see `pic`).
#let fan(nin, nout, x0, x1, ss, lead: 0) = {
  for s in ss {
    for y in ys(nin) { bend((lead, y), (x0 + CHPAD, s + y), stroke: FAN) }
    for y in ys(nout) { bend((x1 - CHPAD, s + y), (x1 + CHFAN - lead, y), stroke: FAN) }
  }
  if lead > 0 {
    for y in ys(nin) { wire((0, y), (lead, y)) }
    for y in ys(nout) { wire((x1 + CHFAN - lead, y), (x1 + CHFAN, y)) }
  }
}

// `lead` is a straight run at every port for whoever places the node: the panel's labels run `into`
// a port, and a fan leaving the port itself would cross their ink.
#let pic(t, length, lead: 0) = {
  // ---- §3 rows 1-2, 7, 10, 15-16: one box.  A box spanning several strands is as tall as they are.
  if t.k == "box" {
    let n = calc.max(t.nin, t.nout)
    let h = if n > 1 { (n - 1) * 2 * UIP + 0.35 } else if tall(t) { CTH } else { BH }
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
      // two boxes with no strand between them (`l°` into `nil`) still stand a stub apart
      let (x2, s) = if n == 0 and i > 0 { (x + CGAP, none) } else { stub(x, n) }; x = x2; body.push(s)
      let p = pic(it, length)
      body.push(d.group({ d.translate((x, 0)); p.body }))
      x = x + p.w; n = it.nout; hh = calc.max(hh, p.hh)
      if str(i) in seam {
        // one label per strand, each wire broken round its own ink; the column is as wide as the widest
        let ws = seam.at(str(i)).map(s => cu(measure(tx(s)).width, length))
        let (w, o) = (calc.max(..ws), into(length))
        for ((s, wi), y) in seam.at(str(i)).zip(ws).zip(ys(n)) {
          body.push(wire((x, y), (x + CGAP + (w - wi) / 2 + o, y)))
          body.push(wire((x + CGAP + (w + wi) / 2 - o, y), (x + 2 * CGAP + w, y)))
          body.push(lab(x + CGAP + w / 2, y, TYCOL, tx(s)))
        }
        x = x + 2 * CGAP + w
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
  // ---- §3 row 3: a projection.  The factors it drops END AT A DOT and the one it keeps crosses to
  // the port it leaves on — a product is already two wires, so this costs no box at all.
  if t.k == "proj" {
    let lo = t.keep.slice(0, t.at).sum(default: 0)
    let ins = ys(t.nin); let outs = ys(t.nout)
    let body = range(t.nin).map(i => if i >= lo and i < lo + t.keep.at(t.at) {
        bend((0, ins.at(i)), (0.75, outs.at(i - lo)), k: 0.5)
      } else { bang((CDL, ins.at(i)), li: CDL) }).join()
    return (w: 0.75, hh: calc.max(t.nin, t.nout, 1) * UIP - UIP, body: body)
  }
  // ---- §3 row 14: `⊸ x`, the constant.  Every input strand ends at a dot, then `x` is created.
  if t.k == "konst" {
    let p = pic(t.body, length)
    let body = ys(t.nin).map(y => bang((0.35, y), li: 0.35)).join()
    return (w: 0.6 + p.w, hh: calc.max(p.hh, (t.nin - 1) * UIP + 0.1),
      body: { body; d.group({ d.translate((0.6, 0)); p.body }) })
  }
  // ---- §3 row 12: `x∩y`.  Copy every strand, run BOTH lanes, merge.  `∇=Δ°` forces the two to
  // carry the same value, and that is the whole of the intersection: no box says `∩`.
  if t.k == "cap" {
    let ps = t.lanes.map(l => pic(l, length))
    let mw = calc.max(..ps.map(p => p.w))
    let mh = calc.max(..ps.map(p => p.hh))
    let sp = mh + 0.22
    let x1 = CSP + mw + CSP
    let body = {
      for (i, p) in ps.enumerate() {
        let s = if i == 0 { 1 } else { -1 }
        d.group({
          d.translate((CSP, s * sp)); p.body
          for y in ys(t.nout) { wire((p.w, y), (mw, y)) }
        })
      }
      for y in ys(t.nin) { delta((0, y), li: 0, lo: CSP, sp: sp) }
      for y in ys(t.nout) { nabla((x1, y), li: CSP, lo: 0, sp: sp) }
    }
    return (w: x1, hh: sp + mh, body: body)
  }
  // ---- §3 row 17: `⦇α⦈` as MELLIÈS' FUNCTORIAL BOX.  Nothing crosses the LEFT pair of bars: the
  // input arrives at them and the algebra's own strands start inside, and that break IS the
  // recursion.  The algebra's output is the fold's, so it runs out through the right pair.
  if t.k == "cata" {
    let p = pic(t.body, length)
    let yh = calc.max(p.hh, (t.nin - 1) * UIP) + 0.28
    let ld = calc.max(..t.port.map(s => cu(measure(tx(s)).width, length))) + 2 * CLEAD
    // A stub before the left bars, the mirror of the one after the right bars: the source label
    // then sits on a wire, not between the bars.
    let x0 = CGAP + CBAR + ld
    let xr = x0 + p.w + CBAR
    // The carrier labels the fold's single OUTPUT wire on its stub; `scripts/circuit` sends `none`
    // when the carrier is a product (already drawn as its wires) or is that wire's own label.
    let og = if t.label == none { CGAP } else { cu(measure(tx(t.label)).width, length) + 2 * CLEAD }
    let body = {
      for y in ys(t.nin) { wire((0, y), (CGAP, y)) }
      banana(CGAP, yh)
      banana(xr + CBAR, yh, right: true)
      for (i, y) in ys(t.body.nin).enumerate() {
        wire((x0 - ld, y), (x0, y))
        lab(x0 - ld / 2, y + CABOVE, TYCOL, tx(t.port.at(i)))
      }
      d.group({ d.translate((x0, 0)); p.body })
      for y in ys(t.nout) {
        wire((x0 + p.w, y), (xr + CBAR + og, y))
        if t.label != none {
          lab(xr + CBAR + og / 2, y + CABOVE, TYCOL, tx(t.label))
        }
      }
    }
    return (w: xr + CBAR + og, hh: yh, body: body)
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
      }
      fan(t.nin, t.nout, x0, x1, (UDY, -UDY), lead: lead)
    }
    return (w: x1 + CHFAN, hh: hh + 0.3, body: body)
  }
  // ---- §3 row 13: the bracket at a polynomial object — tape fork, branches, tape join.  Every arm
  // opens with the converse injection `scripts/circuit` put there (11.2a), so the fork hands ONE
  // coproduct wire to each arm and the seam after that box names the summand's strands.
  let ps = t.bodies.map(b => pic(b, length))
  let oys = (BRT, -BRT)
  let mw = calc.max(..ps.map(p => p.w))
  let xf = 1.26; let xj = xf + mw + 0.7
  // The tape is drawn round what the branches actually reach, top and bottom apart: the `𝟏` summand
  // is one small box where the pair below it carries a whole `∪` region.
  let top = calc.max(..ps.zip(oys).map(((p, o)) => o + p.hh)) + 0.15
  let bot = calc.min(..ps.zip(oys).map(((p, o)) => o - p.hh)) - 0.15
  let st = (thickness: 1.4pt, paint: TAPEEDGE)
  let body = {
    tape((CGAP, bot), (xj, top))
    wire((0, 0), (CGAP, 0))
    for (i, p) in ps.enumerate() {
      let oy = oys.at(i)
      d.bezier((0.56, 0), (xf, oy), (0.98, 0), (0.98, oy), stroke: st)
      d.group({ d.translate((xf, oy)); p.body; wire((p.w, 0), (mw, 0)) })
    }
    tape-join((xj, 0), sp: BRT, len: 0.7)
    // The join sits on the tape edge, so the label needs a stub after it, the mirror of the input stub.
    wire((xj, 0), (xj + CGAP, 0))
  }
  (w: xj + CGAP, hh: calc.max(top, -bot), body: body)
}

// The panel: the tree's own picture, with the ports named at both ends.  `src`/`tgt` are one label
// per STRAND — a product is two wires, so it is two labels, never one reading `A×[A]`.
#let cbody(t, length) = {
  let o = into(length)
  let p = pic(t, length, lead: o)
  p.body
  for (i, y) in ys(t.nin).enumerate() {
    lab(o - cu(measure(tx(t.src.at(i))).width, length) / 2, y, TYCOL, tx(t.src.at(i)))
  }
  for (i, y) in ys(t.nout).enumerate() {
    lab(p.w - o + cu(measure(tx(t.tgt.at(i))).width, length) / 2, y, TYCOL, tx(t.tgt.at(i)))
  }
}

#let cpanel(tree, s: 74%, length: 0.8cm, cert: (:)) = {
  context P(cetz.canvas(length: length, cbody(tree, length)), s: s,
    key: cert.at("expect", default: "cpanel"))
  // The drawn lists want the note's `plain` to serialise; the cert is the part that is text already.
  metadata((kind: "circuit", helper: "cpanel", cert: cert))
}
