// cdpanel — the note's COMMUTATIVE-DIAGRAM panel: a NODE is an object, an EDGE an arrow, a FACE the
// equation between the two paths round it.  It is the third of the note's panel helpers, beside
// `dpanel.typ` (a wire is a functor) and `cpanel.typ` (a wire is an object); the three share no
// geometry, and a picture drawn in the wrong one is a different claim, not a slightly different one.
//
// Everything here is emitted by `diag-export --commutative`, which reads the declaration's own
// elaborated statement.  Nothing in this file is per-declaration: it is given a graph in GRID
// coordinates and turns it into centimetres, which is the one part of the layout Lean cannot do —
// only Typst can measure a label.
//
//   ./scripts/diag-export --commutative AOP.A5_5_TypeFunctor.alpha_natural
//   typst compile --root . diag/generated/commutative/<name>.typ
#import "note-style.typ": P
#import "circuit.typ": cetz, d

// `diag/natsq.typ`'s own square, which every panel here is measured against: its horizontal edge is
// 6.4 canvas units at `length: 0.9cm` and its vertical 2.6; its arrows are 0.75pt with a `">"` mark
// at scale 0.5; its node labels are 10pt inside a 4pt-inset white box.
#let STEPX = 6.4
#let STEPY = 2.6
#let NPAD = 4pt
#let NSIZE = 10pt
#let STROKE = (thickness: 0.75pt, paint: black)
#let MARK = (end: ">", scale: 0.5)
// The clear space two node boxes in adjacent columns (or rows) keep between them.  A step is never
// SMALLER than natsq's, and never so small that two labels touch: a long label pushes the grid open
// rather than being drawn over its neighbour, which is the failure a fixed step guarantees.
#let LGAP = 0.9
// Where an arrow stops, measured out from the node box it points at — so the arrowhead is visible
// clear of the label instead of being hidden under the white box that covers it.
#let ARRGAP = 0.14
// An edge label's clearance from its edge, measured from the label's near side.
#let LABGAP = 0.20
// The relation between the two paths, set larger than the labels: it is what the picture asserts.
#let SYMSIZE = 13pt

#let cu(l, length) = l / length

// A label's half-width and half-height in canvas units.  `pad` is the box inset a node label wears
// and an edge label does not.
#let hext(lbl, length, pad) = {
  let m = measure(box(inset: pad, text(NSIZE, lbl)))
  (cu(m.width, length) / 2, cu(m.height, length) / 2)
}

// One axis: the distinct grid values in ascending order become positions, each step the larger of
// natsq's step scaled by the grid distance and what the two labels either side of it need.
#let axis(vs, step, hs) = {
  let ps = (0.0,)
  for i in range(1, vs.len()) {
    ps.push(ps.at(i - 1) + calc.max(step * calc.abs(vs.at(i) - vs.at(i - 1)),
      hs.at(i - 1) + hs.at(i) + LGAP))
  }
  ps
}

// Where a grid value sits, for a value BETWEEN two node columns — the face symbol's, which is the
// average of the corners and lands on no node.
#let interp(vs, ps, v) = {
  if vs.len() == 1 { ps.at(0) } else {
    let i = 0
    while i < vs.len() - 2 and v > vs.at(i + 1) { i += 1 }
    ps.at(i) + (v - vs.at(i)) / (vs.at(i + 1) - vs.at(i)) * (ps.at(i + 1) - ps.at(i))
  }
}

// Where a ray leaving a node's centre crosses that node's label box, grown by `pad`.  This, and not
// a fixed shortening, is why a long label does not have an arrow drawn through it.
#let exitpt(c, hw, hh, dir, pad) = {
  let tx = if calc.abs(dir.at(0)) < 1e-9 { 1e9 } else { (hw + pad) / calc.abs(dir.at(0)) }
  let ty = if calc.abs(dir.at(1)) < 1e-9 { 1e9 } else { (hh + pad) / calc.abs(dir.at(1)) }
  let t = calc.min(tx, ty)
  (c.at(0) + t * dir.at(0), c.at(1) + t * dir.at(1))
}

// The outward normal of the side of the face an edge is on: its label is set that way, clear of the
// face, so the symbol in the middle is the only thing inside the polygon.
#let normalOf(side) = {
  if side == "top" { (0.0, 1.0) } else if side == "bottom" { (0.0, -1.0) }
  else if side == "left" { (-1.0, 0.0) } else { (1.0, 0.0) }
}

#let cdbody(nodes, edges, faces, length) = {
  let ext = (:)
  for n in nodes { ext.insert(n.id, hext(n.label, length, NPAD)) }
  let cols = nodes.map(n => n.at.at(0)).dedup().sorted()
  let rows = nodes.map(n => n.at.at(1)).dedup().sorted()
  let colh = cols.map(c => calc.max(
    ..nodes.filter(n => n.at.at(0) == c).map(n => ext.at(n.id).at(0))))
  let rowh = rows.map(r => calc.max(
    ..nodes.filter(n => n.at.at(1) == r).map(n => ext.at(n.id).at(1))))
  // Every box in a row is drawn at the row's height (see below), so that is also the height an
  // arrow has to clear: the clipping and the ink must be measured from the same box.
  for n in nodes {
    ext.insert(n.id, (ext.at(n.id).at(0), rowh.at(rows.position(r => r == n.at.at(1)))))
  }
  let xps = axis(cols, STEPX, colh)
  let yps = axis(rows, STEPY, rowh)
  let pos(a) = (interp(cols, xps, a.at(0)), interp(rows, yps, a.at(1)))

  let at = (:)
  for n in nodes { at.insert(n.id, pos(n.at)) }
  // The arrows first, the white node boxes over them: an arrow that a label box has to cover was
  // drawn too long, but the cover costs nothing and the note's other panels draw in this order.
  for e in edges {
    let (a, b) = (at.at(e.at("from")), at.at(e.at("to")))
    let (dx, dy) = (b.at(0) - a.at(0), b.at(1) - a.at(1))
    let len = calc.sqrt(dx * dx + dy * dy)
    let u = (dx / len, dy / len)
    let ea = ext.at(e.at("from"))
    let eb = ext.at(e.at("to"))
    let p = exitpt(a, ea.at(0), ea.at(1), u, ARRGAP)
    let q = exitpt(b, eb.at(0), eb.at(1), (-u.at(0), -u.at(1)), ARRGAP)
    // The label is set along the EDGE's own perpendicular, `side` choosing only which of the two it
    // is.  An axis normal clears a horizontal or vertical edge and not a diagonal one: a wide label
    // offset straight up from the midpoint of a 45° chord has that chord run through it.
    let ax = normalOf(e.side)
    let per = (-u.at(1), u.at(0))
    let nm = if per.at(0) * ax.at(0) + per.at(1) * ax.at(1) < 0 {
      (-per.at(0), -per.at(1))
    } else { per }
    let mid = ((p.at(0) + q.at(0)) / 2 + nm.at(0) * e.bow,
      (p.at(1) + q.at(1)) / 2 + nm.at(1) * e.bow)
    if e.bow == 0 { d.line(p, q, mark: MARK, stroke: STROKE) }
    else { d.bezier(p, q, mid, mark: MARK, stroke: STROKE) }
    let lh = hext(e.label, length, 0pt)
    // How far the label box reaches in that direction — its support function, so the WHOLE box
    // clears the edge and not just its centre.
    let off = LABGAP + calc.abs(nm.at(0)) * lh.at(0) + calc.abs(nm.at(1)) * lh.at(1)
    d.content((mid.at(0) + nm.at(0) * off, mid.at(1) + nm.at(1) * off), text(NSIZE, e.label))
  }
  // ONE HEIGHT PER ROW.  cetz centres a content's own frame, and a label with a descender has a
  // taller frame than one without, so labels drawn at the same row coordinate come out at different
  // heights and the arrow between them slopes.  Giving every box in a row the row's height — the
  // height the row was spaced for — is what makes a row level.
  for n in nodes {
    let h = rowh.at(rows.position(r => r == n.at.at(1))) * 2 * length
    d.content(at.at(n.id),
      box(inset: NPAD, fill: white, height: h, align(horizon, text(NSIZE, n.label))))
  }
  for f in faces { d.content(pos(f.at), text(SYMSIZE)[#f.sym]) }
}

// `length: 0.9cm` and `s: 74%` are natsq's scale and the note's: a panel that must lose height lowers
// `length`, never `s`, so the labels keep their size relative to the geometry.
#let cdpanel(nodes, edges, faces, s: 74%, length: 0.9cm, cert: (:)) = {
  context P(cetz.canvas(length: length, cdbody(nodes, edges, faces, length)), s: s,
    key: cert.at("expect", default: "cdpanel"))
  metadata((kind: "commutative", helper: "cdpanel", cert: cert))
}
