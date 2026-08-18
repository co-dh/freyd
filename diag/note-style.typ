// note-style.typ — the page setup and cell helpers shared by diag/allegory-axioms.typ (the laws) and
// diag/allegory2.typ (the proofs), which must look like one document; a copy in either is how they drift.
//
// `conf` rather than plain `#set` lines: set and show rules at the top level of an imported file do
// not reach the importer, so the document rules have to be applied by a function the note shows
// itself through.  The helpers below are ordinary `#let`s and travel by import.

// `theorem`, `example` are re-exported: a note that shows itself through `conf` uses the template's
// environments too, and importing the template twice is the copy this file exists to avoid.
#import "@preview/dvdtyp:1.0.1": dvdtyp, builder-thmline, colors, theorem, example
// `definition` is rebuilt, not re-exported, to drop the "Definition 9.1." head: every block already
// names its term in bold and nothing ever cited a definition by number.  The separator goes with it.
#let definition = builder-thmline(color: colors.at(8))(
  "definition", "", separator: []).with(numbering: none)
#import "circuit.typ": cetz, d

/// The document rules; a note begins with `#show: conf.with(title: "…")`.  PAGINATED, not one endless
/// page: page numbers beat the unbroken column.  25cm is the widest exported picture, a four-part `⟺`.
#let conf(title: "", body) = {
  set page(width: 25cm, height: 35cm, margin: 1.5cm)
  set text(size: 11.5pt)
  show raw: set text(size: 9.6pt)
  show heading: set block(above: 16pt, below: 9pt)
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
  // ONE pattern built from the heading depth rather than a branch per depth: a three-slot pattern fed
  // four numbers repeats its last symbol, which is how a `===` display came out `(15.5a)a)`.
  let dispnum(h, n) = numbering("(" + "1." * (h.len() - 1) + "1a)", ..h, n)
  set figure(numbering: n => context { dispnum(counter(heading).get(), n) })
  show heading: it => { counter(figure.where(kind: "disp")).update(0); it }
  // A REFERENCE RESOLVES AT THE DISPLAY, NOT AT THE SENTENCE THAT CITES IT: a `context` inside a
  // reference resolves where the REFERENCE stands, so a display in §12 cited from §13 came out `(13.n)`.
  show ref: it => {
    let el = it.element
    if el != none and el.func() == figure and el.at("kind", default: none) == "disp" {
      context {
        let h = counter(heading).at(el.location())
        let n = counter(figure.where(kind: "disp")).at(el.location()).first()
        link(el.location(), dispnum(h, n))
      }
    } else { it }
  }
  // THE NUMBER SITS IN THE RIGHT MARGIN and takes no width: a column of its own cost every display
  // about 35pt.  `breakable` because a figure is not, and the chain tables here run over a page break.
  show figure.where(kind: "disp"): it => block(width: 100%, breakable: true, {
    place(top + right, dx: 1.0cm, text(9pt, luma(130), it.counter.display(it.numbering)))
    it.body
  })
  body
}

/// A NUMBERED DISPLAY carrying a letter-suffixed section path — `(13a)` or `(13.1a)` — at its right
/// edge; a literal number typed into prose is what this makes impossible.  `kind: "disp"`: ONE
/// sequence per heading whatever the display is.
#let disp(body) = figure(body, kind: "disp", supplement: none)

#let src(s) = text(9.2pt, luma(105))[#s]
/// An exported picture, shrunk to fit a table cell.  `reflow` so the cell measures the shrunk size.
#let P(p, s: 92%) = align(center, box(inset: (y: 5pt), scale(x: s, y: s, reflow: true, p)))
/// A picture set INLINE in a table header.  Deliberately large: at running-text size the theorem it
/// states cannot be read at all.
#let Pin(p, s: 70%) = box(baseline: 36%, scale(x: s, y: s, reflow: true, p))
/// A chain table's top header row: the theorem, one size up from the body.
#let Th(body) = table.cell(colspan: 3, text(12.5pt)[#body])
/// A figure transcribed from the paper by hand — used only where there is no Lean STATEMENT to
/// export, i.e. for the two primitive operations.
#let fig(body) = align(center, box(inset: (y: 5pt), cetz.canvas(length: 0.78cm, body)))
/// Pictures side by side.  Every exported canvas is symmetric about its own `y = 0`, so aligning on the
/// horizon puts all their wires at one height; a per-box `baseline:` shift cannot, being a fraction of each.
#let row(items, s: 100%) = align(center, box(inset: (y: 4pt), grid(
  columns: items.len(), align: horizon, column-gutter: 3pt,
  ..items.map(t => scale(x: s, y: s, reflow: true, t)))))

/// A proof in ONE ROW, the rule under each step.  The exporter draws the `=` (or `≤`) at the LEFT edge
/// of every step after the first, so a left-aligned hint lands under it and the first hint is empty.
#let chain(steps, hints, s: 62%) = align(center, box(inset: (y: 6pt), grid(
  columns: steps.len(), align: horizon, column-gutter: 14pt, row-gutter: 1pt,
  ..steps.map(t => scale(x: s, y: s, reflow: true, t)),
  ..hints.map(h => src[#h]))))
