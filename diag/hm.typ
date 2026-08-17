// hm.typ — Hinze–Marsden drawing primitives (IntroString.pdf §1.4.2 p. 17, Remark 2.1 p. 36, layout
// from diagram (3.6) p. 77).  A wire is a FUNCTOR, a bead an arrow or natural transformation, the
// areas between wires CATEGORIES; pictures read top to bottom, so going down composes in diagram
// order.  Sibling of circuit.typ, where a wire is an object and pictures read left to right.
// THE ONE INVARIANT: a region boundary and the wire bounding it come from THE SAME `pts` through THE
// SAME `hm-path` — bind the list once, never hand-fit a fill to a wire.
#import "circuit.typ": cetz, d, lw, Rr

// Where a bend's control points sit along its drop.  The golden ratio, from the CTAN package
// `string-diagrams`, whose model (not code) this file follows.
#let HMK = 0.618

// How far above a junction the consumed strand leaves its straight run.  `hm-join`'s default, and a
// client that bends in by hand (draw.typ's `splitcut`) must use the same or shapes differ.
#let KNEE = 0.6

// A step changing both x and y is a bezier with vertical tangents, so wires meet edges and beads at
// a right angle.  Mirror-symmetric on purpose: reversing `pts` gives back the same curve.
#let hm-seg(a, b, k: HMK) = {
  if a.at(0) == b.at(0) or a.at(1) == b.at(1) {
    d.line(a, b)
  } else {
    let dy = b.at(1) - a.at(1)
    d.bezier(a, b, (a.at(0), a.at(1) + k * dy), (b.at(0), b.at(1) - k * dy))
  }
}

/// The path through `pts`, unstyled — `hm-wire` and `hm-region` put the stroke or fill on it.
#let hm-path(pts, k: HMK) = {
  for i in range(pts.len() - 1) { hm-seg(pts.at(i), pts.at(i + 1), k: k) }
}

/// One `merge-path` and not one element per segment, so a bend and its straight run cannot seam.
#let hm-wire(pts, col: black, thickness: lw, k: HMK) = d.merge-path(
  fill: none, stroke: (thickness: thickness, paint: col), hm-path(pts, k: k),
)

/// AN UNCHANGED WIRE IS DRAWN UNCHANGED: at a junction the SURVIVOR runs straight and the CONSUMED
/// strand — this one — bends in and terminates on it, so the survivor's shape says it did not move.
#let hm-join(xfrom, ytop, xonto, y, knee: KNEE, col: black) = hm-wire(
  ((xfrom, ytop), (xfrom, y + knee), (xonto, y)), col: col,
)

/// The shape of a unit or counit.  `dir` is which side of the feet the arch lies on: `+1` above, so
/// the wires hang down and the turn OPENS a pair (a unit); `-1` below, CLOSING one (a counit).
#let hm-turn(xl, xr, y, dir: 1, col: black, rise: 0.62, thickness: lw) = {
  let h = dir * rise * (xr - xl)
  d.merge-path(fill: none, stroke: (thickness: thickness, paint: col),
    d.bezier((xl, y), (xr, y), (xl, y + h), (xr, y + h)))
}

/// Where a bead or name goes on `hm-turn`'s strand.  Beside the bezier it reads, because the `3/4`
/// is that cubic's midpoint and would be a magic number nothing keeps in step anywhere else.
#let hm-apex(xl, xr, y, dir: 1, rise: 0.62) = ((xl + xr) / 2, y + 0.75 * dir * rise * (xr - xl))

/// `hm-turn` cut at its apex, where a strand joining two functors changes from one to the other.
/// De Casteljau at `t = 1/2`: the halves ARE that cubic, so the shape is `hm-turn`'s untouched.
#let hm-turn-split(xl, xr, y, cl, cr, dir: 1, rise: 0.62, thickness: lw) = {
  let h = dir * rise * (xr - xl)
  let ap = hm-apex(xl, xr, y, dir: dir, rise: rise)
  let half(x, cx, col) = d.bezier((x, y), ap, (x, y + h / 2), (cx, y + 3 * h / 4),
    stroke: (thickness: thickness, paint: col))
  half(xl, (3 * xl + xr) / 4, cl)
  half(xr, (xl + 3 * xr) / 4, cr)
}

/// FILL AND STROKE ARE NEVER THE SAME PATH, or the region draws a floor along the box's edges.
/// Draw every region before any wire, or a fill hides the wire bounding it.
#let hm-region(pts, fill, k: HMK) = d.merge-path(
  close: true, fill: fill, stroke: none, hm-path(pts, k: k),
)

/// Dot and name share `col`, so an arrow and its label cannot be told apart by colour.  `dx`/`dy`
/// move the name off the dot: centred on one it falls inside the fork of a merge.
#let hm-bead(p, label, col: black, dx: 0.32, dy: 0, anchor: "west") = {
  d.circle(p, radius: Rr, fill: col, stroke: none)
  if label != none {
    d.content((p.at(0) + dx, p.at(1) + dy), text(col)[#label], anchor: anchor)
  }
}

/// A wire end on a box edge, name OUTSIDE; `dir` is `+1` above the top edge, `-1` below the bottom.
/// `p` and not `(x, "top")`: a panel body is drawn in its own coordinates and is not told the height.
#let hm-port(p, label, dir: 1, col: black, gap: 0.28) = d.content(
  (p.at(0), p.at(1) + dir * gap), text(col)[#label],
  anchor: if dir > 0 { "south" } else { "north" },
)

/// A region name, muted, inside the region.  Named ONCE in a family's first picture — the book's own
/// practice; unlabelled regions still carry their colour.
#let hm-name(p, label, col: luma(150), size: 9pt) = d.content(p, text(size, col)[#label])

/// `body` is drawn in the panel's own coordinates, `(0, 0)` bottom left.  Returns DATA, not a
/// drawing: `hm-row` needs `w` to lay panels out.  `frame` defaults to none — the fills are the box.
#let hm-panel(w, h, body, fill: none, frame: none) = (
  w: w,
  h: h,
  body: {
    if fill != none { d.rect((0, 0), (w, h), fill: fill, stroke: none) }
    body
    if frame != none { d.rect((0, 0), (w, h), fill: none, stroke: frame) }
  },
)

/// ONE CANVAS AND NOT A GRID: separate canvases each centre on their own bounding box, so panels
/// with beads at different heights would start and end at different heights, matching no `=`.
#let hm-row(panels, sep: [=], gap: 1.0, length: 0.95cm, sepsize: 13pt) = cetz.canvas(
  length: length,
  {
    let ymid = calc.max(..panels.map(p => p.h)) / 2
    let x = 0.0
    for (i, p) in panels.enumerate() {
      if i > 0 {
        if sep != none { d.content((x + gap / 2, ymid), text(sepsize)[#sep]) }
        x = x + gap
      }
      d.group({ d.translate(x: x); p.body })
      x = x + p.w
    }
  },
)
