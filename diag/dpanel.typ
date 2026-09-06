// dpanel — the note's Hinze–Marsden panel helper: a wire is a FUNCTOR, a bead an arrow, a region a
// category.  It is the sibling of `cpanel.typ`, which draws the OTHER convention (a wire is an
// object, a box a morphism); the two share no geometry, and a panel drawn in the wrong one is
// transposed, not slightly wrong.  Kept out of the prose file so a helper edit and a wording edit
// never touch the same file.
//
//   typst compile --root . diag/allegory-axioms.typ diag/allegory-axioms.pdf
//   ./scripts/diagram --pairs diag/allegory-axioms.typ   // rebuild every panel from its own `cert:`
//   ./scripts/scanline diag/allegory-axioms.typ --strict // sweep what these calls emit
#import "note-style.typ": P, dispnum, plain
#import "hm.typ": cetz, hm-bead, hm-name, hm-panel, hm-port, hm-region, hm-wire
#import "draw.typ": BCOL, fb-ALLC, fcol, lanecheck, objcol

// ---- the Hinze-Marsden panel machinery, ABOVE every section that draws one: Typst binds a
// `#let` where it stands, and §11.4's generated panels are the first `dpanel` calls in the note.
// A panel's address is the display it stands in and its place in that display, both read off the
// counters at the point it is PLACED, so a reordered row cannot keep a stale name.
#let hm-meta(rec) = {
  counter("hm-panel").step()
  context metadata((kind: "scanline",
    id: plain(dispnum(counter(heading).get(),
      counter(figure.where(kind: "disp")).get().first()))
      + "." + str(counter("hm-panel").get().first()),
    ..rec))
}

// The panel every Hinze–Marsden column in this note draws — §@sec-hylo's, §13.3.1's, `tw-hm`,
// `party-hm`, §13.4.4's two.  A wire is a FUNCTOR, a bead an arrow, a region a category: `Rel` left
// of the object wire, `𝟏` right of it.
// One ROW — `scripts/diagram`'s own `DY`, respelled so a panel can report its size as the COMPLEXITY
// it was drawn from: `rows` beads deep and `wires` wide.  A pair's `cert.frame` is a row count for
// that reason, so re-measuring the row (`./scripts/labelfit`) moves no number in this file.
#let DY = 1.1
// IntroString.pdf (2.5), p. 46: an arrow of a composite is a bead on the OBJECT line, which runs
// STRAIGHT through it; the functor wires that composite is made of bend in to the bead and out again.
// `k` is how far above and below the node the lane leaves its column: a panel stacking four lanes in
// one column detours more shallowly than a two-wire one — still a slope, never a horizontal tangent.
#let NKN = 0.45
// EVERY sloped run of the object edge is bowed, p. 74's lone corner-to-corner `L` included: the bow
// is what lets a bead riding the edge sit ON a surface instead of being passed end-on, and what
// makes the join with a vertical run smooth instead of a kink.  A path with no sloped run — a
// plain vertical edge — has no knee to give.
// The knee is 0.88, the top of IntroString p. 79's own measured range (0.55 to 0.88) and as flat
// as the edge may get: at 1, the flat limit, `hm-seg`'s vertical handles put the curve's one
// stationary point on its midpoint, and an arm reaching a bead THERE arrives along the same
// horizontal the edge already has — the two run tangent and the ink grazes.  Seven panels put a
// bead on that midpoint.  Past 1 the handle overshoots the far end and the wire doubles back.
#let oknee(op) = {
  let k = 0
  for i in range(op.len() - 1) {
    let (a, b) = (op.at(i), op.at(i + 1))
    if a.at(0) != b.at(0) and a.at(1) != b.at(1) { k = 0.88 }
  }
  k
}
// Where that bezier stands at a height.  Its handles are VERTICAL, so the x-controls ARE the
// endpoints and x(t) is the smoothstep `3t²-2t³`; y(t) is inverted by bisection.
#let obez(a, b, k, y) = {
  let u = (y - a.at(1)) / (b.at(1) - a.at(1))
  let (lo, hi) = (0.0, 1.0)
  for i in range(40) {
    let m = (lo + hi) / 2
    let f = 3 * k * m * calc.pow(1 - m, 2) + 3 * (1 - k) * m * m * (1 - m) + calc.pow(m, 3)
    if f < u { lo = m } else { hi = m }
  }
  let t = (lo + hi) / 2
  a.at(0) + (b.at(0) - a.at(0)) * (3 * t * t - 2 * t * t * t)
}
#let nodepts(x, xo, ys, k: NKN) = {
  let pts = ()
  for y in ys { pts += ((x, y + k), (xo, y), (x, y - k)) }
  pts
}
#let lwire(x, xo, ys, ytop, ybot, k: NKN) = hm-wire(
  ((x, ytop),) + nodepts(x, xo, ys, k: k) + ((x, ybot),))
// `s` scales the LABELS with the geometry, so a panel that must lose height lowers `length:`, never
// `s`; §@sec-hylo passes 100% and prints its labels at the size `tw-hm` does.
// A strand STOPS SHORT of the dot it lands on, by 0.06cm measured along its own direction — the gap
// IntroString p.74 (pdf 89) leaves at every arm, leg and dip, of which the dot's own 0.05cm radius
// covers all but 0.01cm.  0.06cm / (cetz `length: 0.8cm`) = 0.075 canvas units.
#let HSTUB = 0.075
// The object edge BROKEN at the beads riding it: IntroString p.74's single-bead figure leaves a gap
// centred on the dot, each stub ending `HSTUB` from the centre measured ALONG the edge, where the
// two-bead figure beside it draws the same edge through its dots unbroken.  The REGION boundary
// stays the whole `op` — the break is a gap in the INK, not in the boundary the fills follow.
#let obroken(op, bks) = {
  let (out, cur) = ((), (op.at(0),))
  for i in range(op.len() - 1) {
    let (a, b) = (op.at(i), op.at(i + 1))
    let (ux, uy) = (b.at(0) - a.at(0), b.at(1) - a.at(1))
    let m = calc.max(calc.sqrt(ux * ux + uy * uy), 1e-9)
    for p in bks.filter(p => p.at(1) <= a.at(1) + 1e-9 and p.at(1) >= b.at(1) - 1e-9)
                .sorted(key: p => -p.at(1)) {
      cur.push((p.at(0) - HSTUB * ux / m, p.at(1) - HSTUB * uy / m))
      out.push(cur)
      cur = ((p.at(0) + HSTUB * ux / m, p.at(1) + HSTUB * uy / m),)
    }
    cur.push(b)
  }
  out + (cur,)
}
// ---- THE OBJECT WIRE'S COLOUR IS ITS OBJECT.  A wire that changes object at a bead changes hue
// there, so `A` visibly ends and `B` begins instead of one line wearing two names.  The hue is the
// OBJECT'S, off `draw.typ`'s `objcol`, so one object is one colour across the whole note.
// The bands top to bottom as `(ytop, colour)`: the top port's object, then every seam that RENAMES
// it — an endo bead leaves the object alone and starts no band.
#let obands(h, obj, top, bot, ride) = {
  let bs = ((h, plain(top)),)
  for s in obj.sorted(key: s => -s.at(0)) {
    if plain(s.at(1)) != bs.last().at(1) { bs.push((s.at(0), plain(s.at(1)))) }
  }
  // A panel the generator did not TYPE still ends at a named port, and a bottom port the bands do
  // not reach is a rename nobody recorded: seam it at the lowest bead riding the wire, which is the
  // same guess `scanline` makes when a panel says nothing, so the ink and the sweep agree.
  if plain(bot) != bs.last().at(1) and ride != () { bs.push((calc.min(..ride), plain(bot))) }
  bs.map(b => (b.at(0), objcol(b.at(1))))
}
// The band a height falls in: the LAST one that opens above it, the bands running down the panel.
#let ocolat(bs, y) = {
  let c = if bs == () { BCOL } else { bs.first().at(1) }
  for b in bs { if y < b.at(0) - 1e-9 { c = b.at(1) } }
  c
}
// Cut a vertical run at the band seams with NO gap — `obroken`'s cut opens one, being a cut at a dot.
#let ocut(seg, ys) = {
  let (out, cur) = ((), (seg.at(0),))
  for i in range(seg.len() - 1) {
    let (a, b) = (seg.at(i), seg.at(i + 1))
    for y in ys.filter(y => y < a.at(1) - 1e-9 and y > b.at(1) + 1e-9).sorted().rev() {
      cur.push((a.at(0), y)); out.push(cur); cur = ((a.at(0), y),)
    }
    cur.push(b)
  }
  out + (cur,)
}

// `opath` slopes the object wire: a polyline top to bottom, kinked at bead heights, hugging the
// lanes already born.  Fills and wire are built from the SAME pts, so the region edge IS the wire.
// `straight` draws it as the book's own polyline instead of `oknee`'s bow, and `obreak` lists the
// dots it is broken at.  An edge may STOP ON THE PANEL'S RIGHT SIDE rather than its bottom (all
// three of IntroString p.74's figures do), and then both regions close along that side.
#let dpan(h, w, xa, body, s: 74%, opath: none, obreak: (), straight: false, obnd: (), key: none) = P(
    cetz.canvas(length: 0.8cm, {
  let op = if opath == none { ((xa, h), (xa, 0)) } else { opath }
  let ok = if straight { 0 } else { oknee(op) }
  let (ex, ey) = op.last()
  let side = if ey > 1e-9 and calc.abs(ex - w) > 1e-9 { ((w, ey),) } else { () }
  let lead = if calc.abs(op.first().at(0)) > 1e-9 { ((0, 0), (0, h)) } else { ((0, 0),) }
  hm-region(lead + op + (if ey > 1e-9 { side + ((w, 0),) } else { () }), fb-ALLC,
            k: ok, straight: straight)
  hm-region(op + (if ey > 1e-9 { side } else { ((w, 0),) }) + ((w, h),), luma(226),
            k: ok, straight: straight)
  // A SLOPED edge is drawn as ONE bow whose ink `scanline` re-models from `opath`; cutting it into
  // two bows would move the ink without moving the model, so a sloped edge keeps a single hue.
  for seg in obroken(op, obreak) {
    let cuts = if opath == none and obnd.len() > 1 { obnd.slice(1).map(b => b.at(0)) } else { () }
    for part in ocut(seg, cuts) {
      hm-wire(part, col: ocolat(obnd, (part.first().at(1) + part.last().at(1)) / 2),
              k: ok, straight: straight)
    }
  }
  body
}), s: s, key: key)

// Which bead heights a lane bends down to: every bead whose reach spans this column and which the
// lane is live across — the reach crosses the lanes between, so a wire inside it MEETS that bead.
#let ddips(xat, h, beads, x, y0, y1) = beads.filter(bd => bd.at(3, default: none) != none
  and bd.at(3) <= x and x < xat(bd.at(0))
  and (if y0 == "top" { h } else { y0 }) > bd.at(0)
  and (if y1 == "bot" { 0 } else { y1 }) < bd.at(0)).map(bd => bd.at(0)).sorted().rev()
#let dkey(s, y) = s + str(float(y))
// Where a strand standing in column `x` stops on its way to the dot at `(bx, y)`: back along the row
// it arrives on, or — where the dot stands in the strand's OWN column and there is no room along the
// row — back up its column, `vy` being +1 for a strand above the dot and -1 for one below.
#let dstub(bx, y, x, vy) = {
  let d = if calc.abs(x - bx) < 1e-6 { (0, HSTUB * vy) } else if x < bx { (-HSTUB, 0) } else { (HSTUB, 0) }
  (bx + d.at(0), y + d.at(1))
}
// ONE knee per bead-and-side, for arms, legs and dips alike: equal knees on one bezier family give
// the strands the same y(t) and they nest, where unequal ones braid — so a per-strand knee, whose
// aspect grew with the horizontal run, is given up; the arrival stays VERTICAL either way, since
// `hm-seg` puts its controls straight above and below the ends.  Half the gap, so two bands never
// OVERLAP — they may share a midpoint, and there each strand is vertical, in its own column.
// `0.5 * gap` is PROVED for the 113 `dpanel`s, under three preconditions all true today: every lane
// left of `xo`, no `opath`, and no unit lane born at an object-bead height with a lane born left of
// it.
#let dknees(xat, h, lanes, beads) = {
  let bys = beads.map(bd => bd.at(0))
  let (run, cap) = ((:), (:))
  for l in lanes {
    let (x, y0, y1) = (l.at(0), l.at(1), l.at(2))
    let room = (if y0 == "top" { h } else { y0 }) - (if y1 == "bot" { 0 } else { y1 })
    let es = ((if y0 != "top" and l.at(4) == none { ((y0, ("b",)),) } else { () })
      + ddips(xat, h, beads, x, y0, y1).map(y => (y, ("b", "d")))
      + (if y1 != "bot" { ((y1, ("d",)),) } else { () }))
    for (i, e) in es.enumerate() {
      let y = e.at(0)
      for s in e.at(1) {
        let nb = if s == "d" and i > 0 { es.at(i - 1).at(0) }
          else if s == "b" and i + 1 < es.len() { es.at(i + 1).at(0) }
        let c = if nb == none { 0.55 * room } else { 0.5 * calc.abs(nb - y) }
        // 1e-6 is `scanline`'s `EPS`: ONE tolerance, so the two `dknees` are one function.
        let o = bys.filter(z => if s == "d" { z > y + 1e-6 } else { z < y - 1e-6 })
        if o != () {
          c = calc.min(c, 0.5 * calc.abs(
            (if s == "d" { o.fold(99, calc.min) } else { o.fold(-99, calc.max) }) - y))
        }
        run.insert(dkey(s, y), calc.max(run.at(dkey(s, y), default: 0), calc.abs(xat(y) - x)))
        cap.insert(dkey(s, y), calc.min(cap.at(dkey(s, y), default: 99), c))
      }
    }
  }
  let gk = (:)
  for (k, v) in run { gk.insert(k, calc.min(0.3 * DY + 0.25 * v, cap.at(k))) }
  gk
}
// A lane runs from where its functor is BORN to where it DIES: `"top"`/`"bot"` for a panel edge, a
// bead's height otherwise, and `un` is a birth carrying a bead of its own (the singleton).  `xat` is
// the object wire's x at a height (constant `xo` unless `opath` slopes it); `kb`/`kd` are the knees
// `dknees` gave the bead this lane is born on and the one it dies on.
#let dlane(xat, h, x, y0, y1, nm, un, kb: none, kd: none, col: none, alone: false, ulax: false) = {
  let wc = if col == none { (:) } else { (col: col) }
  // Two beads a row apart give knees that eat the whole gap, so the lane stands in its own column
  // for ZERO height and the wire kinks there — vertical for an instant between two swings.  One
  // bezier dot to dot is the same corridor without the wiggle.  Two guards keep the corridor the
  // same one: the lane is ALONE between those two beads, since siblings leave one dot and land on
  // one dot and only their columns hold them apart; and its column lies BETWEEN the two dots, so
  // the columned route was already monotone and the straight line sweeps nothing new.
  let flat = (alone and y0 != "top" and y1 != "bot" and un == none
    and y0 - kb <= y1 + kd + 1e-6
    and x >= calc.min(xat(y0), xat(y1)) - 1e-6 and x <= calc.max(xat(y0), xat(y1)) + 1e-6)
  let pts = if flat {
    // Dot to dot the stub runs along the LINE, which is the strand's own direction here.
    let (a, b) = ((xat(y0), y0), (xat(y1), y1))
    let (ux, uy) = (b.at(0) - a.at(0), b.at(1) - a.at(1))
    let m = calc.sqrt(ux * ux + uy * uy)
    ((a.at(0) + HSTUB * ux / m, a.at(1) + HSTUB * uy / m),
     (b.at(0) - HSTUB * ux / m, b.at(1) - HSTUB * uy / m))
  } else {
    (if y0 == "top" { ((x, h),) } else if un != none { ((x, y0 - HSTUB),) } else {
      (dstub(xat(y0), y0, x, -1), (x, y0 - kb))
    }) + (if y1 == "bot" { ((x, 0),) } else { ((x, y1 + kd), dstub(xat(y1), y1, x, 1)) })
  }
  // Straight, as the object edge is: dot to dot the two ends need no vertical tangent to meet, and
  // `hm-seg`'s would bow the run into an S — IntroString p. 48 draws that run as a single `L`.
  // Otherwise the end that lands ON a dot arrives along the bead's row, as the book's arcs do.
  hm-wire(pts, ..(if flat { (k: 0) } else { (:) }), ..wc,
          hs: (if not flat and y0 != "top" and un == none { (0,) } else { () })
            + (if not flat and y1 != "bot" { (pts.len() - 1,) } else { () }))
  // The unit's own dot draws its naturality, exactly as a bead's does: hollow where the row says
  // `lax`, because the singleton's naturality square commutes one way only.
  if un != none { hm-bead((x, y0), un, bg: if ulax { fb-ALLC } else { none }) }
}
// The bead is a POINT and every arm into one is a bend (IntroString.pdf p. 40, whose spider takes six
// of them), so a wire the bead does not consume dips to the dot at each `ybs` and comes back out, at
// that bead's own two knees — and EVERY contact is met along the bead's row, which is what `hs` says.
#let ddip(xat, h, x, y0, y1, ybs, nm, gk, col: none) = {
  let wc = if col == none { (:) } else { (col: col) }
  let (t, b) = (if y0 == "top" { h } else { y0 }, if y1 == "bot" { 0 } else { y1 })
  // `hs` is recorded where the contact is appended, so the index and the point cannot drift apart.
  let (pts, hs) = ((), ())
  if y0 == "top" { pts.push((x, h)) } else {
    hs.push(pts.len())
    pts += (dstub(xat(t), t, x, -1), (x, t - gk.at(dkey("b", t))))
  }
  for yb in ybs {
    pts.push((x, yb + gk.at(dkey("d", yb))))
    hs.push(pts.len())
    pts += (dstub(xat(yb), yb, x, 0), (x, yb - gk.at(dkey("b", yb))))
  }
  if y1 == "bot" { pts.push((x, 0)) } else {
    pts.push((x, b + gk.at(dkey("d", b))))
    hs.push(pts.len())
    pts.push(dstub(xat(b), b, x, 1))
  }
  hm-wire(pts, ..wc, hs: hs)
}

// A lane's name is its own when it has one, and otherwise the one the port list writes at the edge
// it reaches — the two places on the page the same wire can be read.
#let dnm(l, top, bot) = if l.at(3) != none { l.at(3) } else {
  let q = (if l.at(1) == "top" { top } else { bot }).find(t => t.at(0) == l.at(0))
  if q == none { none } else { q.at(1) } }

// A WIRE is not one lane: a bead hands it from one column to the next and the reader sees one
// continuous wire, so the lanes with the same name, each dying where the next is born, are ONE
// group.  Its name is written once — on the lane born highest, where the wire first appears — and
// not at all when some lane of the group reaches an edge, where a port list already writes it.
#let dnamed(lanes, top, bot) = {
  let n = lanes.len()
  let ns = lanes.map(l => plain(dnm(l, top, bot)))
  // A death and a birth are the same literal from the same table, so this `==` needs no `EPS`; one
  // pass per lane closes a chain of at most that many lanes.
  let g = range(n)
  for _ in range(n) {
    for i in range(n) {
      for j in range(n) {
        if ns.at(i) != none and ns.at(i) == ns.at(j) and lanes.at(i).at(2) == lanes.at(j).at(1) {
          let m = calc.min(g.at(i), g.at(j))
          g.at(i) = m
          g.at(j) = m
        }
      }
    }
  }
  let edge = range(n).filter(i => lanes.at(i).at(1) == "top" or lanes.at(i).at(2) == "bot")
    .map(i => g.at(i))
  range(n).filter(i => not edge.contains(g.at(i)) and range(n).all(j =>
    g.at(j) != g.at(i) or lanes.at(j).at(1) < lanes.at(i).at(1)
      or (lanes.at(j).at(1) == lanes.at(i).at(1) and j >= i)))
}

// A bead's 4th element is how far left it reaches, and the reach is ink the crossed WIRES make by
// bending onto the dot (`ddip`) — never a line drawn past them, which would cross without meeting.
// `right` is a port list for the panel's RIGHT side, `(y, label)` each: the object edge may leave
// through that side instead of the bottom (IntroString p.74).  `obreak` names the bead heights the
// edge is broken at, and `ostraight` draws it as the book's straight polyline.
// A DEFN BOUNDARY: `(x0, x1, y, label)`.  The note abbreviates an object — `A[m+1] ≜ F(A[m])` — and
// the picture draws what the right side IS, two wires; the edge then writes the LEFT side's own name
// once, under a thin bracket spanning both columns, instead of the two per-wire labels.  Reading the
// two labels the reader would have to re-derive the abbreviation the note already stated.
#let dbrace(x0, x1, y, l, h) = {
  let dir = if y > h / 2 { 1 } else { -1 }
  let c = fcol(l)
  let yb = y + dir * 0.16
  hm-wire(((x0, yb), (x1, yb)), col: c)
  hm-wire(((x0, yb), (x0, yb - dir * 0.10)), col: c)
  hm-wire(((x1, yb), (x1, yb - dir * 0.10)), col: c)
  hm-port(((x0 + x1) / 2, yb), l, dir: dir, col: c)
}
#let dcovers(defn, y, x) = defn.any(d => calc.abs(d.at(2) - y) < 1e-6
  and x >= d.at(0) - 1e-6 and x <= d.at(1) + 1e-6)
#let dpanel(h, w, xo, lanes, beads, top, bot, names: false, s: 74%, opath: none, right: (),
            obreak: (), ostraight: false, obj: (), defn: (), cert: (:)) = {
  // `obj` is the generator's OWN typing of the object wire — which bead renames it, and to what.
  // `dpan` colours the wire by it; the sweep, which otherwise guesses the seam at the lowest bead
  // on the wire, reads the same list back off `hm-meta`.
  let obnd = obands(h, obj, top.find(p => p.at(0) == xo).at(1),
                    bot.find(p => p.at(0) == xo).at(1),
                    beads.filter(b => b.at(4, default: none) == none).map(b => b.at(0)))
  // Bound ONCE and used by both the ink and `hm-meta`: a check reading a value the drawing does not
  // use is a check on a second copy of the rule, which is the bug the `knees` field exists to stop.
  let (otc, obc) = (ocolat(obnd, h), ocolat(obnd, 0))
  // 1e-6 is `scanline`'s `EPS` and the FIRST match wins, as it does there: at a segment boundary both
  // sides match, so taking the last one would make `xat` two functions in two languages, not one.
  let ok = if opath == none or ostraight { 0 } else { oknee(opath) }
  let xat = if opath == none { y => xo } else { y => {
    let r = none
    for i in range(opath.len() - 1) {
      let (a, b) = (opath.at(i), opath.at(i + 1))
      if r == none and y <= a.at(1) + 1e-6 and y >= b.at(1) - 1e-6 {
        r = if a.at(1) - b.at(1) < 1e-6 { b.at(0) }
          else if ok == 0 or a.at(0) == b.at(0) {
            b.at(0) + (a.at(0) - b.at(0)) * (y - b.at(1)) / (a.at(1) - b.at(1)) }
          else { obez(a, b, ok, y) }
      }
    }
    if r == none { xo } else { r }
  } }
  // A bead's 5th element is where its DOT sits.  IntroString p. 36: an object IS the constant functor
  // `𝟏 → 𝒞` and an arrow IS a natural transformation between two of them, so a dot ON the object
  // wire says "an arrow of the base category".  One natural in the object is `α∘X` (p. 38), whose
  // object argument is drawn as a wire running PAST the dot, so its dot names only functor wires.
  let dotx = (:)
  for b in beads { if b.at(4, default: none) != none { dotx.insert(dkey("x", b.at(0)), b.at(4)) } }
  let dx = y => dotx.at(dkey("x", y), default: xat(y))
  let gk = dknees(dx, h, lanes, beads)
  let nmd = dnamed(lanes, top, bot)
  // The palette's separations, measured on THIS panel — its lanes against each other, and each lane
  // against the beads and the object bands it is read beside.  The rule is only true panel by panel:
  // two lanes that never share a picture may reuse a band, and only the panel knows which those are.
  lanecheck(cert.at("expect", default: "dpanel"),
    lanes.map(l => dnm(l, top, bot)).filter(n => n != none).map(n => (plain(n), fcol(n))),
    beads.map(b => (plain(b.at(1)), b.at(2, default: black)))
      + obnd.map(o => ("the object wire", o.at(1))))
  dpan(h, w, xo, {
  for (i, l) in lanes.enumerate() {
    let ys = ddips(dx, h, beads, l.at(0), l.at(1), l.at(2))
    let kb = if l.at(1) == "top" or l.at(4) != none { none } else { gk.at(dkey("b", l.at(1))) }
    let kd = if l.at(2) == "bot" { none } else { gk.at(dkey("d", l.at(2))) }
    // The lane's functor name keys `fcol`, and the colour names a wire that has a PORT to be read
    // beside; `dnamed` says on which lanes that name is nowhere else on the page.
    let nm = dnm(l, top, bot)
    let col = if nm == none { none } else { fcol(nm) }
    // ALONE IN THE CORRIDOR, not merely on the two rows: a lane whose column lies between the two
    // dots and is live across the gap has ink there, and the straight line sweeps from one side of
    // that column to the other — two wires that meet have exchanged.
    let corr = if l.at(1) == "top" or l.at(2) == "bot" { () } else {
      let (a, b) = (dx(l.at(1)), dx(l.at(2)))
      lanes.enumerate().filter(o => o.at(0) != i
        and o.at(1).at(0) > calc.min(a, b) + 1e-6 and o.at(1).at(0) < calc.max(a, b) - 1e-6
        and (o.at(1).at(1) == "top" or o.at(1).at(1) >= l.at(1) - 1e-6)
        and (o.at(1).at(2) == "bot" or o.at(1).at(2) <= l.at(2) + 1e-6))
    }
    let alone = (corr.len() == 0
      and lanes.filter(o => o.at(1) == l.at(1) and o.at(2) == l.at(2)).len() == 1)
    if ys == () { dlane(dx, h, l.at(0), l.at(1), l.at(2), l.at(3), l.at(4), kb: kb, kd: kd, col: col,
                        alone: alone, ulax: l.at(5, default: none) == "lax") }
    else { ddip(dx, h, l.at(0), l.at(1), l.at(2), ys, l.at(3), gk, col: col) }
    // On the birth row, where every arm leaves its dot vertically — EXCEPT where another strand
    // sweeps that row west of this lane: a leg of the same bead born there, or a lane DYING there,
    // which arrives at the dot across the very gap the name is written in.  Then the name drops to
    // the end of the knee, where both are back in their columns.
    if nmd.contains(i) {
      let swept = lanes.any(o =>
        (o.at(1) == l.at(1) or o.at(2) == l.at(1)) and o.at(0) < l.at(0))
      // Half a name's height BELOW the knee's end, so the box's top edge is where the sibling's
      // strand has just come vertical; on the knee's own end the box still straddles the bend.
      hm-name((l.at(0) - 0.12, l.at(1) - (if swept and kb != none { calc.min(kb, 0.3) + 0.161 } else { 0 })),
              nm, col: col, anchor: "east")
    }
  }
  // A MERGE IS A HOLD, NOT A POINT: where more than one strand dies on a bead, IntroString p.74
  // (pdf 89) lands them on the ends of a 0.12cm horizontal segment centred on the dot, and drops the
  // outgoing leg from its midpoint — exactly the two `HSTUB`s back to back.
  for b in beads {
    let dy = lanes.filter(l => l.at(2) != "bot" and l.at(2) == b.at(0))
    if dy.len() > 1 {
      let nm = dnm(dy.sorted(key: l => l.at(0)).first(), top, bot)
      hm-wire(((dx(b.at(0)) - HSTUB, b.at(0)), (dx(b.at(0)) + HSTUB, b.at(0))),
              ..(if nm == none { (:) } else { (col: fcol(nm)) }))
    }
  }
  // A bead's 6th element is `"lax"`: the naturality square commutes one way only, so the dot is
  // hollow — punched out in the region behind it, which is the `Rel` side every dot sits in.
  for b in beads { hm-bead((dx(b.at(0)), b.at(0)), b.at(1), col: b.at(2, default: black),
                           bg: if b.at(5, default: none) == "lax" { fb-ALLC } else { none }) }
  for (x, l) in top {
    if not dcovers(defn, h, x) {
      hm-port((if x == xo { xat(h) } else { x }, h), l, col: if x == xo { otc } else { fcol(l) }) } }
  for (x, l) in bot {
    if not dcovers(defn, 0, x) {
      hm-port((if x == xo { xat(0) } else { x }, 0), l, dir: -1,
              col: if x == xo { obc } else { fcol(l) }) } }
  for (x0, x1, y, l) in defn { dbrace(x0, x1, y, l, h) }
  // The right side carries only the object edge, so its ports take `BCOL` with no lookup.
  for (y, l) in right { hm-port((w, y), l, axis: "x", col: BCOL) }
  if names { hm-name((1.12, 0.35), [`Rel`]); hm-name((xo + 1.4, 0.35), [`𝟏`]) }
  }, s: s, opath: opath, obreak: obreak.map(y => (xat(y), y)), straight: ostraight, obnd: obnd,
     key: cert.at("expect", default: "dpanel"))
  // `knees` is what the ink was DRAWN with: `scanline` re-models the same rule, and a panel whose
  // two knees disagree is a crossing the sweep would call clean while the page still braids.
  // The panel's COMPLEXITY, so a display is laid out from what is in the picture and not by eye:
  // `rows` is how many bead heights deep the frame is, `wires` how many lines cross it — the lanes
  // plus the object edge.  A pair's `cert.frame` is one panel's `rows` written into the other.
  hm-meta((helper: "dpanel", h: h, w: w, xo: xo, rows: calc.round(h / DY), wires: lanes.len() + 1,
    cert: cert, knees: gk, ok: ok, named: nmd,
    lanes: lanes.map(l => l.map(plain)), beads: beads.map(b => b.map(plain)),
    top: top.map(p => p.map(plain)), bot: bot.map(p => p.map(plain)))
    + (if opath == none { (:) } else { (opath: opath) })
    + (if right == () { (:) } else { (right: right.map(p => p.map(plain))) })
    + (if obreak == () { (:) } else { (obreak: obreak) })
    + (if ostraight { (ostraight: true) } else { (:) })
    + (if obj == () { (:) } else { (obj: obj.map(p => p.map(plain))) })
    // The object PORTS' hues, so the sweep can hold the rule that a wire changing object changes
    // colour — the ink is a `dpan` argument and nothing else on the rec would show it.
    + (ocol: (otc.to-hex(), obc.to-hex())))
}
