// cdpanel — the note's COMMUTATIVE-DIAGRAM panel: a NODE is an object, an EDGE an arrow, a FACE the
// equation between the two paths round it.  It is the third of the note's panel helpers, beside
// `dpanel.typ` (a wire is a functor) and `cpanel.typ` (a wire is an object); the three share no
// geometry, and a picture drawn in the wrong one is a different claim, not a slightly different one.
//
// IT DRAWS WITH THE NOTE'S OWN MARKS.  `ar`, `node` and `lab` are `draw.typ`'s — the same three the
// note's hand-laid squares are built from (`<initial-defn>`, `α⦇f⦈=F(⦇f⦈)f`) — so a generated square
// and the note's are the same picture, and `scripts/svg-diff` holds them to that.  Nothing here is
// re-derived from `natsq.typ`: an arrow's clearance, its 0.75pt pen and its `">"` mark at scale 0.5
// live in `ar` alone.
//
// Everything here is emitted by `diag-export --commutative`, which reads the declaration's own
// elaborated statement.  Nothing in this file is per-declaration: it is given a graph in GRID
// coordinates and turns it into canvas units, which is the one part of the layout Lean cannot do —
// only Typst can measure a label.
//
//   ./scripts/diag-export --commutative Freyd.Alg.relCata_cancel
//   typst compile --root . diag/generated/commutative/<name>.typ
#import "note-style.typ": P
#import "draw.typ": ar, cetz, d, lab, node

// THE NOTE'S SQUARE, `diag/allegory-axioms.typ` `<initial-defn>`: `cetz.canvas(length: 0.8cm)` with
// its corners at `(±2.6, ±1.35)`.  One grid step is therefore 5.2 across and 2.7 down, whatever the
// path lengths are — a four-edge side against a one-edge side lays out on this same pitch.
#let LENGTH = 0.8cm
#let STEPX = 5.2
#let STEPY = 2.7
#let NPAD = 4pt
#let NSIZE = 10pt
// The clear space two node boxes in adjacent columns (or rows) keep between them.  A step is never
// SMALLER than the note's, and never so small that two labels touch: a long label pushes the grid
// open rather than being drawn over its neighbour, which is the failure a fixed step guarantees.
#let LGAP = 0.9
// An edge label's clearance from its edge, measured from the label's near side.  0.416 plus a
// one-line label's own half-height is the 0.55 the note holds its top label at, `lab(0, ±1.9)`
// against corners on `y = ±1.35`.
#let LABGAP = 0.416
// The relation between the two paths, set larger than the labels: it is what the picture asserts.
#let SYMSIZE = 13pt
// What an arrow keeps clear of the label box it leaves.  The note's own square stands its arrows
// 0.55 off a node CENTRE, which clears a two-letter box; a label wide enough to swallow that stub
// pushes the arrow out to its own box instead, or the arrowhead is drawn under the label.
#let ACLEAR = 0.12

#let cu(l, length) = l / length

// A label's half-width and half-height in canvas units.  `pad` is the box inset a node label wears
// and an edge label does not.
#let hext(lbl, pad, length) = {
  let m = measure(box(inset: pad, text(NSIZE, lbl)))
  (cu(m.width, length) / 2, cu(m.height, length) / 2)
}

// One axis: the distinct grid values in ascending order become positions, each step the larger of
// the note's step scaled by the grid distance and what the two labels either side of it need.  The
// whole axis is then centred on 0, which is where the note's own square sits.
#let axis(vs, step, hs) = {
  let ps = (0.0,)
  for i in range(1, vs.len()) {
    ps.push(ps.at(i - 1) + calc.max(step * calc.abs(vs.at(i) - vs.at(i - 1)),
      hs.at(i - 1) + hs.at(i) + LGAP))
  }
  let c = ps.at(ps.len() - 1) / 2
  ps.map(p => p - c)
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

// The outward normal of the side of the face an edge is on: its label is set that way, clear of the
// face, so the symbol in the middle is the only thing inside the polygon.
#let normalOf(side) = {
  if side == "top" { (0.0, 1.0) } else if side == "bottom" { (0.0, -1.0) }
  else if side == "left" { (-1.0, 0.0) } else { (1.0, 0.0) }
}

// How far the label box of a node reaches along a ray leaving its centre: the nearer of the two
// faces the ray can cross.
#let reach(h, u) = {
  let tx = if calc.abs(u.at(0)) < 1e-9 { 1e9 } else { h.at(0) / calc.abs(u.at(0)) }
  let ty = if calc.abs(u.at(1)) < 1e-9 { 1e9 } else { h.at(1) / calc.abs(u.at(1)) }
  calc.min(tx, ty)
}

#let cdbody(nodes, edges, faces, length) = {
  let ext = (:)
  for n in nodes { ext.insert(n.id, hext(n.label, NPAD, length)) }
  let cols = nodes.map(n => n.at.at(0)).dedup().sorted()
  let rows = nodes.map(n => n.at.at(1)).dedup().sorted()
  let colh = cols.map(c => calc.max(
    ..nodes.filter(n => n.at.at(0) == c).map(n => ext.at(n.id).at(0))))
  let rowh = rows.map(r => calc.max(
    ..nodes.filter(n => n.at.at(1) == r).map(n => ext.at(n.id).at(1))))
  let xps = axis(cols, STEPX, colh)
  let yps = axis(rows, STEPY, rowh)
  let pos(a) = (interp(cols, xps, a.at(0)), interp(rows, yps, a.at(1)))

  let at = (:)
  for n in nodes { at.insert(n.id, pos(n.at)) }
  // The arrows first, the white node boxes over them, so a stub that does reach under a label is
  // covered rather than drawn over it.
  for e in edges {
    let (a, b) = (at.at(e.at("from")), at.at(e.at("to")))
    // The label is set along the EDGE's own perpendicular, `side` choosing only which of the two it
    // is.  An axis normal clears a horizontal or vertical edge and not a diagonal one: a wide label
    // offset straight up from the midpoint of a 45° chord has that chord run through it.
    let (dx, dy) = (b.at(0) - a.at(0), b.at(1) - a.at(1))
    let len = calc.sqrt(dx * dx + dy * dy)
    let u = (dx / len, dy / len)
    let ax = normalOf(e.side)
    let per = (-u.at(1), u.at(0))
    let nm = if per.at(0) * ax.at(0) + per.at(1) * ax.at(1) < 0 {
      (-per.at(0), -per.at(1))
    } else { per }
    // `ar`'s `bow` is signed towards the LEFT normal, and `nm` is the side the label is on.
    let sgn = if nm.at(0) * per.at(0) + nm.at(1) * per.at(1) < 0 { -1 } else { 1 }
    ar(a, b, black, bow: sgn * e.bow,
      s0: calc.max(0.55, reach(ext.at(e.at("from")), u) + ACLEAR),
      s1: calc.max(0.55, reach(ext.at(e.at("to")), (-u.at(0), -u.at(1))) + ACLEAR))
    let lh = hext(e.label, 0pt, length)
    // How far the label box reaches in that direction — its support function, so the WHOLE box
    // clears the edge and not just its centre.
    let off = LABGAP + calc.abs(nm.at(0)) * lh.at(0) + calc.abs(nm.at(1)) * lh.at(1) + e.bow
    let mid = ((a.at(0) + b.at(0)) / 2, (a.at(1) + b.at(1)) / 2)
    lab(mid.at(0) + nm.at(0) * off, mid.at(1) + nm.at(1) * off, black, e.label)
  }
  for n in nodes { node(at.at(n.id).at(0), at.at(n.id).at(1), black, n.label) }
  for f in faces {
    let p = pos(f.at)
    d.content(p, text(SYMSIZE)[#f.sym])
  }
}

// `length: 0.8cm` and `s: 74%` are the note's own: a panel that must lose height lowers `length`,
// never `s`, so the labels keep their size relative to the geometry.
#let cdpanel(nodes, edges, faces, s: 74%, length: LENGTH, cert: (:)) = {
  context P(cetz.canvas(length: length, cdbody(nodes, edges, faces, length)), s: s,
    key: cert.at("expect", default: "cdpanel"))
  metadata((kind: "commutative", helper: "cdpanel", cert: cert))
}
