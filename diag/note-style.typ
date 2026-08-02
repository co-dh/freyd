// note-style.typ — the page setup and the cell helpers shared by the two allegory notes.
//
// TWO NOTES, ONE STYLE.  diag/allegory-axioms.typ states the laws and diag/allegory2.typ works the
// proofs, and they must look like one document: same page, same picture scales, same grey for an
// aside.  A copy of this block in each of them is how the two would drift — the same failure the
// header of `scripts/diag-regen` records, where a list of declarations was kept twice and one copy
// went stale.
//
// `conf` rather than plain `#set` lines: set and show rules at the top level of an imported file do
// not reach the importer, so the document rules have to be applied by a function the note shows
// itself through.  The helpers below are ordinary `#let`s and travel by import.

// `definition`, `theorem`, `example` are re-exported: a note that shows itself through `conf` uses
// the template's environments too, and importing the template twice is the copy this file exists to
// avoid.
#import "@preview/dvdtyp:1.0.1": dvdtyp, definition, theorem, example
#import "strdiag.typ": cetz, d

/// The document rules.  A note begins with `#show: conf.with(title: "…")`.
///
/// PAGINATED, not one endless page: a viewer's page number and page keys are worth more than the
/// unbroken column, and the tables here are short enough that few of them straddle a break.  25cm
/// wide because the widest exported picture is a `⟺` between two containments, four sub-pictures in
/// a row.
#let conf(title: "", body) = {
  set page(width: 25cm, height: 35cm, margin: 1.5cm)
  set text(size: 11.5pt)
  show raw: set text(size: 9.6pt)
  show heading: set block(above: 16pt, below: 9pt)
  // Justification inside a table cell stretches the spaces around long unbreakable monospace runs
  // (`Freyd.Diag.ClosedLinearBicat.«residual_comp_≤»`) into gaps you can drive a car through.
  show table: set par(justify: false)
  // The four generators are relation-operator glyphs, cut to sit inline beside `→` and `⊢`, so at
  // running-text size their rings and triangles are too fine to tell apart.  They are read here as
  // pictures, not as operators, so scale them back up to the surrounding cap height.
  show regex("[◁▷⊸⟜]"): it => text(size: 1.45em, it)
  // The template supplies the title block, the running header, page numbers, heading numbering and
  // the definition environment.  Everything it sets is merged into, not replaced by, the rules
  // above.
  // `author: none` or the template prints a bare "by" under the title.
  show: dvdtyp.with(title: title, author: none)
  body
}

#let src(s) = text(9.2pt, luma(105))[#s]
/// An exported picture, shrunk to fit a table cell.  `reflow` so the cell measures the shrunk size.
#let P(p, s: 92%) = align(center, box(inset: (y: 5pt), scale(x: s, y: s, reflow: true, p)))
/// A picture set INLINE in a table header, naming the statement the chain proves.  Deliberately
/// large: the header is the one row every reader looks at first, and at running-text size the
/// theorem it states cannot be read at all.
#let Pin(p, s: 70%) = box(baseline: 36%, scale(x: s, y: s, reflow: true, p))
/// A chain table's top header row: the theorem, one size up from the body.
#let Th(body) = table.cell(colspan: 3, text(12.5pt)[#body])
/// A figure transcribed from the paper by hand — used only where there is no Lean STATEMENT to
/// export, i.e. for the two primitive operations.
#let fig(body) = align(center, box(inset: (y: 5pt), cetz.canvas(length: 0.78cm, body)))
/// Pictures laid side by side in one row.  Every exported canvas is drawn symmetrically about its
/// own `y = 0`, so aligning the cells on the horizon puts the wires of all of them at one height;
/// a per-box `baseline:` shift cannot, because each box is shifted by a fraction of its OWN height.
#let row(items, s: 100%) = align(center, box(inset: (y: 4pt), grid(
  columns: items.len(), align: horizon, column-gutter: 3pt,
  ..items.map(t => scale(x: s, y: s, reflow: true, t)))))

/// A proof in ONE ROW: the steps side by side, and under each the rule that reached it.  The
/// exporter draws the `=` (or `≤`) at the LEFT edge of every step after the first, so a hint
/// left-aligned in the same column lands under it — a `place`d one collided with the wires.
/// The first hint is therefore always empty.  Steps that change no picture are simply left out:
/// this is a note for a reader who is ahead of it, not a transcript.
///
/// `horizon` for the same reason as `row`: every canvas is symmetric about its own `y = 0`, so
/// centring them puts all the `=` of the chain on one line even when one step is twice as tall.
#let chain(steps, hints, s: 62%) = align(center, box(inset: (y: 6pt), grid(
  columns: steps.len(), align: horizon, column-gutter: 14pt, row-gutter: 1pt,
  ..steps.map(t => scale(x: s, y: s, reflow: true, t)),
  ..hints.map(h => src[#h]))))
