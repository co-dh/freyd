// note-style.typ — the page setup and cell helpers shared by diag/allegory-axioms.typ (the laws) and
// diag/allegory2.typ (the proofs), which must look like one document; a copy in either is how they drift.
//
// `conf` rather than plain `#set` lines: set and show rules at the top level of an imported file do
// not reach the importer, so the document rules have to be applied by a function the note shows
// itself through.  The helpers below are ordinary `#let`s and travel by import.

// `theorem`, `example` are rebuilt here rather than re-exported: they must carry the same band as
// `definition` below, and importing the template twice is the copy this file exists to avoid.
#import "@preview/dvdtyp:1.0.1": dvdtyp, builder-thmbox, builder-thmline, colors
/// THE ONE BAND A THEOREM-LIKE BOX OWNS: from its tint to the prose and displays it holds.  dvdtyp's
/// 1.2em puts a blank line on every side of every picture inside the box, and a box holding three
/// displays pays it twice; 0.5em still detaches the tint from the running text.
#let THMPAD = 0.5em
#let thmline(c, ..a) = builder-thmline(color: c, frame: (body-color: c.lighten(92%),
  border-color: c.darken(10%), thickness: (left: 2pt), inset: THMPAD, radius: 0em), ..a)
#let thmbox(c, ..a) = builder-thmbox(color: c, frame: (body-color: c.lighten(92%),
  border-color: c.darken(10%), thickness: 1.5pt, inset: THMPAD, radius: 0.3em), ..a)
// `definition` also drops the "Definition 9.1." head: every block already names its term in bold and
// nothing ever cited a definition by number.  The separator goes with it.
#let definition = thmline(colors.at(8))("definition", "", separator: []).with(numbering: none)
#let theorem = thmbox(colors.at(6), shadow: (offset: (x: 3pt, y: 3pt), color: luma(70%)))(
  "theorem", "Theorem")
#let example = thmline(colors.at(16))("example", "Example").with(numbering: none)
#import "cetz-nodraw.typ" as cetz
#import "cetz-nodraw.typ": d
#let NODRAW = cetz.NODRAW

/// The document rules; a note begins with `#show: conf.with(title: "…")`.  PAGINATED, not one endless
/// A display's path — `13.4.3c`, the heading numbers then the display's letter.  Bare, so a panel's
/// `scanline` metadata can use it as an address; `conf` parenthesises it for the margin.
/// ONE pattern built from the heading depth rather than a branch per depth: a three-slot pattern fed
/// four numbers repeats its last symbol, which is how a `===` display came out `(15.5a)a)`.
#let dispnum(h, n) = numbering("1." * (h.len() - 1) + "1a", ..h, n)

// ---- `scripts/scanline`'s input.  A panel helper emits THE SAME lists it draws from as
// `#metadata`, which is not laid out: a copy written beside the picture is a copy that drifts.
// A label is content and JSON wants its text; coordinates, `none` and strings ride through, so a
// lane tuple maps elementwise.  `frac(x, ∋)` is the note's division, spelled `x%∋` as one token.
// ABOVE the template: a `#let` is in scope only after it is bound, and the display's own show rule
// spells its number with this.
#let plain(c) = {
  if type(c) == color { c.to-hex() } else if type(c) != content { c }
  else if c == [ ] or c.func() == linebreak { " " }
  // `raw`, `text` and a math `symbol` all carry their glyphs in `text`; `∋` is the third.
  else if c.has("text") { c.text }
  else if c.func() == math.frac { plain(c.num) + "%" + plain(c.denom) }
  else if c.has("children") { c.children.map(plain).join("") }
  else if c.has("body") { plain(c.body) }
  // `styled` is what a `src` side note in a step's caption is; a `ref` reads as its label.
  else if c.has("child") { plain(c.child) }
  else if c.func() == ref { repr(c.target) }
  else { repr(c) }
}

/// page: page numbers beat the unbroken column.  25cm is the widest exported picture, a four-part `⟺`.
#let PAGEW = 25cm
#let MARGIN = 1.5cm
#let NUMGAP = 0.15cm  // column edge to the display number's LEFT edge; the rest of MARGIN is its room to grow
#let conf(title: "", body) = {
  set page(width: PAGEW, height: 35cm, margin: MARGIN)
  set text(size: 11.5pt)
  show raw: set text(size: 9.6pt)
  // `sticky`: a heading whose display lands on the next page goes with it, instead of sitting alone
  // at the foot of this one.
  show heading: set block(above: 16pt, below: 9pt, sticky: true)
  // Justification inside a table cell stretches the spaces around long unbreakable monospace runs
  // (`Freyd.Diag.ClosedLinearBicat.«residual_comp_≤»`) into gaps you can drive a car through.
  show table: set par(justify: false)
  // The four generators are read as PICTURES, not operators: at running-text size their rings and
  // triangles are too fine to tell apart, so scale them back up to the surrounding cap height.
  show regex("[◁▷⊸⟜]"): it => text(size: 1.45em, it)
  // Everything the template sets is merged into, not replaced by, the rules above.
  // `author: none` or the template prints a bare "by" under the title.
  show: dvdtyp.with(title: title, author: none)
  // The heading path is read from the HEADING COUNTER rather than stored anywhere, so it cannot
  // disagree with the heading it sits under.  A display is `(13a)` at top level and `(13.1a)` in
  // subsection §13.1: section references and display references can never be mistaken for one
  // another.  See `disp`.
  set figure(numbering: n => context { [(] + dispnum(counter(heading).get(), n) + [)] })
  show heading: it => { counter(figure.where(kind: "disp")).update(0); it }
  // A REFERENCE RESOLVES AT THE DISPLAY, NOT AT THE SENTENCE THAT CITES IT: a `context` inside a
  // reference resolves where the REFERENCE stands, so a display in §12 cited from §13 came out `(13.n)`.
  show ref: it => {
    let el = it.element
    if el != none and el.func() == figure and el.at("kind", default: none) == "disp" {
      context {
        let h = counter(heading).at(el.location())
        let n = counter(figure.where(kind: "disp")).at(el.location()).first()
        link(el.location(), [(] + dispnum(h, n) + [)])
      }
    } else { it }
  }
  // THE NUMBER SITS IN THE RIGHT MARGIN and takes no width: a column of its own cost every display
  // about 35pt.  `breakable` because a figure is not, and the chain tables here run over a page break.
  // `dx` is MEASURED, never a constant: `place(top + right)` fixes the number's RIGHT edge at `dx`
  // past the column, so a constant leaves its LEFT edge to the number's own width, and anything
  // wider than that constant reaches back INTO the column — where the display's own tint is painted
  // after the `place` and covers the overrun.  `(13.4.4a)` printed `3.4.4a`.  Measuring makes the
  // LEFT edge the fixed thing, at `NUMGAP` past the column, whatever the number's depth.
  // `./scripts/inkfit` gates both ends: the tint no longer covers it, the trim does not cut it.
  // The figure's OWN block, which the show rule below sits inside: breakable there too, or a table
  // taller than a page loses its last rows past the foot, silently (`<edit-mono>`'s last row).
  show figure.where(kind: "disp"): set block(breakable: true)
  show figure.where(kind: "disp"): it => block(width: 100%, breakable: true, {
    // `--input cdscan=1`: the display's own LABEL, which nothing inside `disp` can see — a label
    // belongs to the figure, and only a show rule holds the element it is attached to.
    if cetz.CDSCAN {
      metadata((kind: "cd", el: "disp",
        label: if it.at("label", default: none) == none { "" } else { str(it.label) }))
    }
    // THE DISPLAY'S NAME AND ITS NUMBER, TOGETHER, for every display and not only a scan: a panel's
    // `hm-meta` can address itself only by the NUMBER it stands under, and a number moves with every
    // heading, so `diag/string-panels.txt` names a display by its LABEL and the gate reads the pair
    // off here.  Same reason as the line above — a label belongs to the figure, and only a show rule
    // holds the element it is attached to.
    context metadata((kind: "disp",
      id: plain(dispnum(counter(heading).get(), it.counter.at(here()).first())),
      label: if it.at("label", default: none) == none { "" } else { str(it.label) }))
    context {
      let n = text(9pt, luma(130), it.counter.display(it.numbering))
      place(top + right, dx: measure(n).width + NUMGAP, n)
    }
    // A string-diagram panel is addressed by its display and its place in it (see `hm-meta`), so the
    // count restarts here; the update draws nothing.
    counter("hm-panel").update(0)
    it.body
  })
  body
}

/// THE WHOLE-BOOK COMPILE, SEEN FROM INSIDE A CHAPTER: the root sets this before its first
/// `#include`, so a chapter can tell whether it is the document or one file of it.
#let NOTEROOT = state("note-root", false)

/// A CHAPTER COMPILED ALONE — its file starts `#show: note-chapter.with(N)` — must look like its
/// pages in the book, and a whole-note compile costs about 13 GiB, which every gate paid.  Same
/// rules as `conf`; the heading counter set to N-1 so §13 numbers as §13; and a reference to a
/// label in another chapter rendered as its `names` entry, or as the label's own text, instead of
/// stopping the compile.  Inside the whole book the root has already applied `conf` and the counter
/// already stands at N-1, so there the chapter's own rules are skipped and nothing changes.
#let note-chapter(N, title: "Relation Algebra", names: (:), doc) = context if NOTEROOT.get() { doc } else {
  conf(title: title, {
    counter(heading).update(N - 1)
    // Bound after `conf`'s own `ref` rule, so it runs FIRST and a label that is not in this chapter
    // never reaches `it.element`: reading that is what turns a cross-chapter reference into an error.
    show ref: it => context {
      let t = str(it.target)
      let present = query(it.target).len() > 0
      if t in names { if present { link(it.target, names.at(t)) } else { names.at(t) } }
      else if present { it } else { [#t] }
    }
    doc
  })
}

/// A NUMBERED DISPLAY carrying a letter-suffixed section path — `(13a)` or `(13.1a)` — at its right
/// edge; a literal number typed into prose is what this makes impossible.  `kind: "disp"`: ONE
/// sequence per heading whatever the display is.
// Where a display sits on the page, for `./scripts/book pic`: `here()` is its top-left corner and
// `measure` its extent, so a crop box is read off the layout instead of guessed from the text.
// Under `--input nodraw=1` there is no ink to crop and this is the query's remaining cost: one
// `query(heading.before(here()))` per picture is quadratic in the note (650 pictures × 600 headings).
// `disp: true` only from `disp` below: a picture INSIDE a display reports a crop box of its own, so
// without the flag a gate grouping marks by the preceding `pic` would file a display's arrows under
// whichever inner picture came last.
// `size`: the extent when the caller already has it — every `measure` lays `body` out once more,
// and `P` inside `disp` nests that cost four deep.
#let pic-meta(key, body, width: auto, disp: false, size: auto) = if NODRAW { none } else { context {
  let hs = query(selector(heading).before(here()))
  let sec = if hs.len() == 0 { "" } else {
    numbering("1.1", ..counter(heading).get()) + " " + plain(hs.last().body) }
  let (sz, pos) = (if size == auto { measure(body, width: width) } else { size }, here().position())
  // `plain([])` is `none` — an empty caption's `join` — and the key column wants text.
  [#metadata((kind: "pic", key: if key == none { "" } else { key }, section: sec, page: pos.page,
    x: pos.x.pt(), y: pos.y.pt(), disp: disp,
    w: sz.width.pt(), h: sz.height.pt()))<pic>]
} }
#let disp(body) = figure(kind: "disp", supplement: none, {
  // No `layout` here: the block is `breakable` (see `conf`), so the width is the text width.  The
  // height is read off an end marker, not a `measure` that lays the body out again (off in the last
  // bit, ~1e-14pt); only a display split across pages, whose positions do not subtract, measures.
  context {
    let (a, b) = (here().position(), query(selector(<disp-end>).after(here())).first().location().position())
    let W = PAGEW - 2 * MARGIN
    pic-meta(dispnum(counter(heading).get(), counter(figure.where(kind: "disp")).get().first()),
      body, width: W, disp: true, size: if a.page == b.page { (width: W, height: b.y - a.y) } else { auto })
  }
  body
  [#metadata(none)<disp-end>]
})

#let TYCOL = rgb("#5f7fa0")  // the circuit panels' type labels only: a muted blue, quieter than the black box names
#let src(s) = text(9.2pt, luma(105))[#s]
/// ONE BAND, ONE OWNER — the rule for every helper below and for `capbox`/`zline`/`zderiv` in
/// `draw.typ`.  A vertical gap belongs to whatever draws the boundary on its far side: a theorem
/// box's tint (`THMPAD`), `capbox`'s hairline, a table cell's rule, the block spacing between two
/// displays.  A helper that only ARRANGES pictures — `P`, `fig`, `row`, `chain` — draws no boundary
/// and so pads nothing; they nest four deep (`capbox` > `P` > `row` > `P` inside `dpan`) and each
/// paid its own band, which is 22pt of blank above every string-diagram panel and 22pt below.
///
/// An exported picture, shrunk to fit a table cell.  `reflow` so the cell measures the shrunk size.
/// `key`: the picture also reports its crop box (`pic-meta`) — INSIDE the box, so the corner is its own.
///
/// FIT, and not merely centre: a picture wider than the column it is given is drawn ON TOP of the
/// column beside it, and since both neighbours are centred they grow towards each other until a
/// label of one lands on a label of the other (`./scripts/labelfit`).  No geometry inside a panel
/// can prevent that — the panel is not told the width — so the one place that knows it, this one,
/// spends the second scale factor.  `s` stays what the picture asked for whenever it fits.
#let P(p, s: 92%, key: none) = layout(sz => align(center, box({
  let q = scale(x: s, y: s, reflow: true, p)
  let m = measure(q)
  let f = if m.width > sz.width and sz.width > 0pt { sz.width / m.width * 100% } else { 100% }
  let q = if f == 100% { q } else { scale(x: f, y: f, reflow: true, q) }
  // `m * f`, not a second `measure` of the scaled `q`: the two differ only in the last bit (~1e-14pt).
  if key != none { pic-meta(key, q, size: (width: m.width * (f / 100%), height: m.height * (f / 100%))) }
  q
})))
/// A picture set INLINE in a table header.  Deliberately large: at running-text size the theorem it
/// states cannot be read at all.
#let Pin(p, s: 70%) = box(baseline: 36%, scale(x: s, y: s, reflow: true, p))
/// A chain table's top header row: the theorem, one size up from the body.
#let Th(body) = table.cell(colspan: 3, text(12.5pt)[#body])
/// A figure transcribed from the paper by hand — used only where there is no Lean STATEMENT to
/// export, i.e. for the two primitive operations.
#let fig(body) = align(center, box(cetz.canvas(length: 0.78cm, body)))
/// Pictures side by side.  Every exported canvas is symmetric about its own `y = 0`, so aligning on the
/// horizon puts all their wires at one height; a per-box `baseline:` shift cannot, being a fraction of each.
#let row(items, s: 100%) = align(center, box(grid(
  columns: items.len(), align: horizon, column-gutter: 3pt,
  ..items.map(t => scale(x: s, y: s, reflow: true, t)))))

/// A proof in ONE ROW, the rule under each step.  The exporter draws the `=` (or `≤`) at the LEFT edge
/// of every step after the first, so a left-aligned hint lands under it and the first hint is empty.
#let chain(steps, hints, s: 62%) = align(center, box(grid(
  columns: steps.len(), align: horizon, column-gutter: 14pt, row-gutter: 1pt,
  ..steps.map(t => scale(x: s, y: s, reflow: true, t)),
  ..hints.map(h => src[#h]))))

// WHAT THE TABLE SETTLES, in its top row: the reader needs the destination before the steps, and a
// footer would only confirm it.  Grey ground, heavier rule under it, no new font size.
#let Thm(body, cols: 2) = table.cell(colspan: cols, fill: luma(233), align: center + horizon,
  stroke: (rest: 0.4pt + luma(190), bottom: 1.1pt + luma(120)), strong(body))

// `auto` and not a fixed width: a panel column is as wide as the panels IN IT, so the column beside
// it keeps every point they do not use.  A constant is a guess made against one table's widest panel
// and spent in every other, and the picture it starves overflows its own column — both pictures are
// centred, so they grow towards each other and a label of one lands on a label of the other
// (`./scripts/labelfit`), which no per-panel geometry can prevent.
// A ROW IS NEVER SPLIT at a page break: its cells are pictures, which cannot be cut, so a row split
// there overran the page foot and drew its panels over the row above (`<edit-mono>`'s last rows).
#let calc-table(..rows, cols: (1fr, auto), al: (left + horizon, center + horizon), pr: 10pt) = {
  set table.cell(breakable: false)
  pad(right: pr, table(columns: cols, align: al, inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190), ..rows)) }

#let EQ = text(luma(140))[$=$]

// The op lane is one glyph wide: `⊑`, `⊒` and `=` all measure 8.95pt here.  `layout` gives the
// CELL's width, so a row that cannot fit picture and formula side by side stacks them itself.
#let OPW = 10pt

// A row is TALLER than it is wide once the second column is a picture too, so the circuit and its
// formula stack on one left edge — which `step`'s side-by-side branch cannot give.
#let vstep(op, pic, f) = layout(sz => {
  let row = grid(columns: (OPW, 1fr), align: (left + horizon, left + horizon),
    column-gutter: 6pt, op, stack(spacing: 5pt, box(pic), f))
  pic-meta(plain(f), row, width: sz.width)
  row
})
