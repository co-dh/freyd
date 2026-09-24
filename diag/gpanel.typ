// gpanel.typ — the helper `diag-export --graph` emits into: a CONCRETE relation between finite sets,
// drawn element by element.  The generated file carries only what Lean decided — each relation's
// elements and the pairs it holds of — and the note's `leang` call carries only the LAYOUT: which
// column each element type stands in, where each element sits, and how each relation is inked.
// An arrow therefore cannot be typed in: a pair is drawn exactly when Lean's `decide` accepted it.
//
// cols   one dictionary per column, left to right:
//          type   the element type it holds (the short name the exporter writes)
//          x, ys  its x, and the y of each element by name — every element Lean lists must have one
//          node   "box" (a label in a white box) or "dot" (a dot, labelled `lab` = (dx, dy) off it)
//          col    the label colour, or an array of colours by element index
//          pad    how far an arc keeps off this column's node centres
// rels   by relation key: a FAN (straight arrows, the default) or an ARC (`arc: 1` above, `-1` below)
//          on     the (source column, target column) pairs a fan is drawn between, when a type
//                 stands in two columns
//          col    the arrow colour, or an array of colours by SOURCE element index
//          s0, s1 how far a fan starts off its source and stops short of its target, along x
//          label, h, dh, cx, ly   an arc's label, its height, the height each further pair of it
//                 adds, the reach of its controls, and its label's y (`draw.typ`'s `arc`)
// emph   a relation key: both ends of its pairs are ringed, fans out of them drawn heavy and the rest
//        washed out, and a dot any heavy fan reaches is filled
// notes  ((x, y), content) pairs set on the canvas as they are — headings and family names
#import "circuit.typ": cetz, d, dot
#import "draw.typ": arc, GIVEN2

#let gpanel(graph, cols: (), rels: (:), emph: none, notes: (), length: 0.8cm) = {
  for k in rels.keys() {
    if graph.all(g => g.key != k) { panic("gpanel: a layout for `" + k + "`, which no drawn relation is") }
  }
  let colOf(t) = {
    let ix = range(cols.len()).filter(i => cols.at(i).type == t)
    if ix.len() != 1 {
      panic("gpanel: " + str(ix.len()) + " columns hold `" + t + "`; name the columns with `on:`")
    }
    ix.at(0)
  }
  let pos(i, e) = {
    let c = cols.at(i)
    if e not in c.ys { panic("gpanel: column " + str(i) + " (`" + c.type + "`) places no `" + e + "`") }
    (c.x, c.ys.at(e))
  }
  let pick(col, k) = if type(col) == array { col.at(k) } else { col }
  // Both ends of every pair of `emph`, as (type, element): a name alone is not unique across types.
  let hot = if emph == none { () } else {
    let g = graph.filter(g => g.key == emph)
    if g.len() != 1 { panic("gpanel: emph names `" + emph + "`, which is not a drawn relation") }
    g.at(0).pairs.map(p => ((g.at(0).src, p.at(0)), (g.at(0).tgt, p.at(1)))).flatten().chunks(2)
  }
  let fans = graph.filter(g => "arc" not in rels.at(g.key, default: (:)))
  let reached = fans.map(g => g.pairs.filter(p => (g.src, p.at(0)) in hot).map(p => (g.tgt, p.at(1)))).flatten().chunks(2)
  let elems(t) = {
    let g = graph.filter(g => g.src == t).map(g => g.srcs) + graph.filter(g => g.tgt == t).map(g => g.tgts)
    if g.len() == 0 { panic("gpanel: no drawn relation has elements of `" + t + "`") }
    g.at(0)
  }
  box(cetz.canvas(length: length, {
    for g in fans {
      let h = rels.at(g.key, default: (:))
      // Not `h.at("on", default: …)`: a default is evaluated even when unused, and would panic.
      for (i, j) in if "on" in h { h.on } else { ((colOf(g.src), colOf(g.tgt)),) } {
        for (s, t) in g.pairs {
          let (a, b) = (pos(i, s), pos(j, t))
          let dir = if a.at(0) < b.at(0) { 1 } else { -1 }
          let col = pick(h.at("col", default: black), g.srcs.position(e => e == s))
          let (w, sc) = if emph == none { (0.75, 0.5) } else if (g.src, s) in hot { (1.1, 0.55) } else {
            col = col.lighten(60%); (0.7, 0.4)
          }
          d.line((a.at(0) + h.at("s0", default: 0) * dir, a.at(1)),
            (b.at(0) - h.at("s1", default: 0) * dir, b.at(1)),
            mark: (end: ">", scale: sc), stroke: w * 1pt + col)
        }
      }
    }
    for g in graph.filter(g => g not in fans) {
      let h = rels.at(g.key)
      let (i, j) = (colOf(g.src), colOf(g.tgt))
      for (k, (s, t)) in g.pairs.enumerate() {
        let (a, b) = (pos(i, s), pos(j, t))
        let dir = if a.at(0) < b.at(0) { 1 } else { -1 }
        arc((a.at(0) + cols.at(i).at("pad", default: 0) * dir, a.at(1)),
          (b.at(0) - cols.at(j).at("pad", default: 0) * dir, b.at(1)), h.arc, h.label,
          col: h.at("col", default: GIVEN2), h: h.at("h", default: 3.8) + k * h.at("dh", default: 1.6),
          cx: h.at("cx", default: 4), ly: h.at("ly", default: none))
      }
    }
    for (p, c) in notes { d.content(p, c) }
    // Nodes last, with an opaque fill, so an arrow may start at a centre and the node covers the stub.
    for (i, c) in cols.enumerate() {
      for (k, e) in elems(c.type).enumerate() {
        let p = pos(i, e)
        let on = (c.type, e) in hot
        if c.at("node", default: "box") == "box" {
          d.content(p, box(inset: 4pt, radius: 3pt, fill: if on { rgb("#f2e9f8") } else { white },
            stroke: if on { 0.7pt + GIVEN2 } else { none },
            text(10pt, if on { GIVEN2 } else { pick(c.at("col", default: black), k) }, raw(e))))
        } else {
          if emph == none { dot(p) } else if (c.type, e) in reached {
            d.circle(p, radius: 0.17, fill: GIVEN2, stroke: GIVEN2)
          } else { d.circle(p, radius: 0.17, fill: white, stroke: 0.9pt + black) }
          let off = c.at("lab", default: (0, 0.62))
          d.content((p.at(0) + off.at(0), p.at(1) + off.at(1)), text(10pt, raw(e)))
        }
      }
    }
  }))
}
