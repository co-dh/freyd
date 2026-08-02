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
/// `P`, but not centred.  In the one-column division table the exported picture sits BESIDE the
/// long-division figure, and two centred blocks leave a gutter down the middle of the page.
#let Pl(p, s: 90%) = box(inset: (y: 5pt), scale(x: s, y: s, reflow: true, p))

// ------------------------------------------------------------------ the long-division figure
#let AMBER = rgb("#f6e3bd")
#let GREEN = rgb("#cfe6cd")
/// The long-division bar: `R` as a bar, the composite laid inside it left to right, and a hairline
/// of slack at the far end.
///
/// `tiles` are `(label, kind)` in DIAGRAM order.  `"q"` is the quotient — amber, full height, solid
/// outline, because `T S ⊑ R` is what pins it.  `"d"` is a divisor laid down inside `R`: green,
/// inset top and bottom so it reads as embedded, dashed because its far edge is not pinned either.
/// The slack closes the bar and is deliberately a sliver: `R / S` is the LARGEST quotient, so what
/// is left when nothing more can be taken is exactly a hairline.
///
/// Transcribed, every one of them — this is a metaphor for the universal property, not a picture of
/// a term, and it is the one account of `/` in this note that needs no complement.
#let divbar(..tiles, qw: 3.0, dw: 1.9, slack: 0.12, note: none) = {
  let y0 = -0.55
  let y1 = 0.55
  let ys = 0.36
  let sol = (thickness: 1.1pt, paint: black)
  let dsh = (thickness: 1.1pt, paint: black, dash: "dashed")
  let ts = tiles.pos()
  let ws = ts.map(t => if t.at(1) == "q" { qw } else { dw })
  let total = ws.sum() + slack
  box(inset: (y: 5pt), cetz.canvas(length: 0.78cm, {
    d.rect((0, y0), (total, y1), fill: AMBER, stroke: none)
    // `R`'s own outline: far edge not pinned; top and bottom are drawn tile by tile below.  The
    // LEFT edge comes last, after the tiles, or a divisor laid first — left division — covers it
    // with its own dashed edge and `R`'s one pinned boundary reads as slack.
    d.line((total, y0), (total, y1), stroke: dsh)
    let x = 0.0
    for t in ts {
      let w = if t.at(1) == "q" { qw } else { dw }
      let st = if t.at(1) == "q" { sol } else { dsh }
      d.line((x, y1), (x + w, y1), stroke: st)
      d.line((x, y0), (x + w, y0), stroke: st)
      if t.at(1) == "q" {
        d.line((x, y0), (x, y1), stroke: sol)
        d.line((x + w, y0), (x + w, y1), stroke: sol)
      } else {
        d.rect((x, -ys), (x + w, ys), fill: GREEN, stroke: none)
        d.line((x, ys), (x + w, ys), stroke: dsh)
        d.line((x, -ys), (x + w, -ys), stroke: dsh)
        d.line((x, -ys), (x, ys), stroke: dsh)
        d.line((x + w, -ys), (x + w, ys), stroke: dsh)
      }
      d.content((x + w / 2, 0), text(10.5pt)[#t.at(0)])
      x = x + w
    }
    d.line((total - slack, y1), (total, y1), stroke: dsh)
    d.line((total - slack, y0), (total, y0), stroke: dsh)
    d.line((0, y0), (0, y1), stroke: sol)
    if note != none {
      d.line((total, y0 - 0.42), (total, y0 - 0.1), stroke: (thickness: 0.6pt, paint: luma(110)))
      d.content((total, y0 - 0.62), text(8.5pt, luma(90))[#note])
    }
  }))
}

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
