// Shared macros for the Freyd–Scedrov cheatsheet (§1.4 onwards).
// Every part file starts with  #import "style.typ": *  and uses ONLY these macros.
#import "@preview/dvdtyp:1.0.1": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let accent = colors.at(6)
#let dimc = luma(100)

// The sheet has two contents from one source: the default Rel-focused build, and the full
// chapter-1 build selected by `--input full=1` (see Makefile). Entries only the full build
// wants are spread through `fullonly`, which yields nothing in the default build.
#let full = sys.inputs.at("full", default: "0") != "0"
#let fullonly(..items) = if full { items.pos() } else { () }

// One body, two shapes. `cols: 1` is the phone sheet — a screen-shaped page, one column,
// type big enough to read at that width; `cols: 2` is the desktop sheet — A4 in two
// columns, whose measure comes out slightly wider than the phone's, so the diagrams that
// were drawn to fit a phone fit here unchanged. Everything else is shared, so the two
// PDFs (and the per-section review copies) always say the same thing the same way.
#let sheet(title: "", subtitle: [], cols: 1, body) = {
  let phone = cols == 1
  set page(..if phone { (width: 9cm, height: 16cm, margin: (x: 0.5cm, y: 0.5cm)) }
           else { (paper: "a4", margin: (x: 1.2cm, y: 1.2cm)) })
  // A4 is read at arm's length, a phone at reading distance, so the desktop shape needs the
  // larger type even though its column is the wider of the two.
  set text(size: if phone { 8.5pt } else { 9.8pt })
  show figure.where(kind: "thmenv"): set block(breakable: false)
  show table: set text(size: if phone { 8.2pt } else { 9.5pt })
  // dvdtyp hard-codes 25pt/18pt for the title row. The 25pt title wraps at the phone's
  // measure, and the 18pt subtitle wraps at both, so each gets a size that fits one line.
  show text.where(size: 25pt): it => if phone { text(size: 15pt, it) } else { it }
  show text.where(size: 18pt): it => text(size: if phone { 10pt } else { 14pt }, it)
  // dvdtyp re-sets heading numbering and par itself, so anything they touch has to go
  // inside its body or it loses: no "§3." before a book section number, and no
  // justification — at 8cm of measure it opens rivers.
  dvdtyp(title: title, subtitle: subtitle, author: none, accent: accent, {
    set par(leading: 0.5em, spacing: 0.7em, justify: false, first-line-indent: 0pt)
    set heading(numbering: none)
    // Sections are the only landmarks in a 50-page scroll, and the rows below them are
    // dense, so a size bump is not enough: break, rule it off, give it air. Typst forbids a
    // pagebreak inside `columns`, so the two-column shape breaks the column instead — and a
    // bare column break read as no separation at all, the new section landing level with the
    // tail of the old one, so it also takes a fixed (non-collapsing) gap above the rule.
    // Only the TOP level breaks. Breaking at a subsection too left every column a third
    // empty, so a subsection flows where it falls: a weak gap, which collapses to nothing at
    // the top of a column, a thinner rule, and `sticky` so the title cannot be the last thing
    // in a column with its rows in the next one.
    show heading: it => {
      let top = it.level <= 1
      if top {
        if phone { pagebreak(weak: true) } else { colbreak(weak: true); v(1.8em) }
      } else { v(1.1em, weak: true) }
      block(width: 100%, above: 0em, sticky: not top,
            below: if top { if phone { 1.1em } else { 1.4em } } else { 0.7em }, {
        line(length: 100%, stroke: (if top { 1.2pt } else { 0.6pt }) + accent)
        v(0.5em, weak: true)
        text(font: "New Computer Modern Sans", size: if top { 13pt } else { 11pt },
             weight: 700, fill: accent, it.body)
      })
    }
    // The title stays full width; only the entries below it are set in columns.
    if phone { body } else { columns(2, gutter: 11pt, body) }
  })
}

// ── entry macros ───────────────────────────────────────────────────────────
// dt(("1.41", [...]), ("1.412", [...]), …) — THE entry format: one book item per
// ruled table row, number cell then body cell. Never set items as running prose.
#let dt(..rows) = table(
  columns: (auto, 1fr),
  stroke: (x, y) => (top: 0.25pt + luma(205)),
  inset: (x: 2.5pt, y: 3.2pt),
  align: (right + top, left + top),
  ..rows.pos().map(((k, v)) => (
    text(fill: dimc, size: 6.6pt, weight: "bold")[#k], v)).flatten()
)
// D("term") — a definiendum (the book's small caps).
#let D(t) = text(fill: accent, weight: "bold", smallcaps(t))
// Th(body) — a theorem/lemma statement (the book sets these in italics).
#let Th(body) = emph(body)
// rel(body) — an example in the category of sets and relations.
#let rel(body) = text(fill: luma(70))[#text(weight: "bold", size: 6.8pt)[Rel]#h(0.35em)#body]

// name | statement table, one law per row
#let laws(..rows) = table(
  columns: (auto, 1fr), stroke: 0.3pt + luma(205),
  inset: (x: 3.5pt, y: 2.1pt), align: (left + horizon, left + horizon),
  ..rows,
)

// ── diagram helpers ────────────────────────────────────────────────────────
// Freyd's arrows: tailed = monic, hollow triangle head = cover, dashed = the
// unique morphism whose existence the universal property asserts.
#let cover = (none, (inherit: "cone", fill: white, stroke: auto))
#let dia(..args) = align(center, block(inset: (y: 1.5pt),
  diagram(spacing: (9mm, 6mm), node-inset: 1.5pt, label-size: 6.6pt, ..args)))

// ── Freyd's diagrammatic sentences (§1.2) ──────────────────────────────────
// A definition is a row of diagrams separated by bars carrying ∀, ∃, ∃! or !
// ("there is at most one extension to the next diagram"). Vertices are bare
// dots: the language names nothing.
//   sent(pan(vx((0,0)), …), qbar[∀], pan(…), qbar[∃!], pan(…))
#let vx(p) = node(p, circle(radius: 1.15pt, fill: black, stroke: none), inset: 0pt)
#let pan(..args) = diagram(spacing: (7mm, 5.5mm), node-inset: 0pt, label-size: 6.6pt,
  node-outset: 2pt, ..args)
#let qbar(q) = box(baseline: 45%, stack(dir: ttb, spacing: 1.5pt,
  align(center, text(size: 7pt)[#q]), line(angle: 90deg, length: 9mm, stroke: 0.5pt)))
#let sent(..items) = align(center, block(inset: (y: 2pt), grid(
  columns: items.pos().len(), align: horizon + center, column-gutter: 4.5pt,
  ..items.pos())))
// The two marks Freyd writes onto a diagram: a cross drawn across the two arrows of a
// wedge says "this is a product diagram"; a plus laid over a region is the puncture
// mark, which removes exactly one equation — that part of the diagram need not commute.
#let prodm-sample = box(width: 7pt, height: 7pt,
  place(line(start: (0pt, 0pt), end: (7pt, 7pt), stroke: 0.45pt))
    + place(line(start: (7pt, 0pt), end: (0pt, 7pt), stroke: 0.45pt)))
#let punc-sample = box(width: 5pt, height: 5pt,
  place(line(start: (0pt, 2.5pt), end: (5pt, 2.5pt), stroke: 0.45pt))
    + place(line(start: (2.5pt, 0pt), end: (2.5pt, 5pt), stroke: 0.45pt)))
#let prodm(p) = node(p, prodm-sample, inset: 0pt)
#let punc(p) = node(p, punc-sample, inset: 0pt)
// Freyd's corner mark — the little ⌐ that says "this vertex is a pullback / a monic
// pair". Put it at a fractional coordinate just inside the apex; `rot` turns it:
// 0deg for a square whose apex is top-left; 135deg for the wedge diagrams, where the
// apex is on top and the mark sits just under it (put it at (x, y + 0.38)).
// Freyd draws the mark big: a bracket running from one arrow out of the vertex across
// to the other, both arms touching their arrow. So it is built from the apex and its
// two neighbours, not placed as a fixed-size glyph — it then scales with the diagram
// and lands correctly on squares and on wedges alike.
//   dia(…, ..pb((0, 0), (1, 0), (0, 1)))     apex top-left of a square
//   dia(…, ..pb((1, 0), (0, 1), (2, 1)))     apex on top of a wedge
#let pb(p, n1, n2, t: 0.4) = {
  let lerp(u, v) = (u.at(0) + t * (v.at(0) - u.at(0)), u.at(1) + t * (v.at(1) - u.at(1)))
  let (a, b) = (lerp(p, n1), lerp(p, n2))
  let c = (a.at(0) + b.at(0) - p.at(0), a.at(1) + b.at(1) - p.at(1))
  (edge(a, c, "-", stroke: 0.4pt), edge(c, b, "-", stroke: 0.4pt))
}
#let corner-sample = box(width: 5pt, height: 5pt,
  place(line(start: (0pt, 5pt), end: (5pt, 5pt), stroke: 0.4pt))
    + place(line(start: (5pt, 0pt), end: (5pt, 5pt), stroke: 0.4pt)))
// TODO: the fixed-size version, still used by the parts not yet converted to `pb`.
#let corner(p, rot: 0deg, size: 5pt) = node(p, rotate(rot, box(width: size, height: size,
  place(line(start: (0pt, size), end: (size, size), stroke: 0.4pt))
    + place(line(start: (size, 0pt), end: (size, size), stroke: 0.4pt)))), inset: 0pt)

// ── notation fixes ─────────────────────────────────────────────────────────
// ∋ is classed as a relation, so it glues to a following = / ⊂; force operand class.
#let eps = math.class("normal", sym.in.rev)
#let Rel = math.cal("Rel")
#let Sub = math.cal("Sub")
#let Val = math.cal("Val")
