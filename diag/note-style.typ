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
// nothing ever cited a definition by number.  The separator goes with it; a weak space in its place
// eats the space the source newline after `#definition[` leaves, which indented only the first line.
#let definition = thmline(colors.at(8))("definition", "", separator: h(0pt, weak: true)).with(numbering: none)
#let theorem = thmbox(colors.at(6), shadow: (offset: (x: 3pt, y: 3pt), color: luma(70%)))(
  "theorem", "Theorem")
#let example = thmline(colors.at(16))("example", "Example").with(numbering: none)
#import "cetz-nodraw.typ" as cetz
#import "cetz-nodraw.typ": d
#let NODRAW = cetz.NODRAW
#let PAGEW = 25cm
#let PAGEH = 35cm
#let MARGIN = 1.5cm

/// THE WHOLE-BOOK COMPILE, SEEN FROM INSIDE A CHAPTER: the root sets this before its first
/// `#include`, so a chapter can tell whether it is the document or one file of it.
#let NOTEROOT = state("note-root", false)

/// The document rules; a note begins with `#show: conf.with(title: "…")`.  PAGINATED, not one endless
/// A display's path — `13.4.3c`, the heading numbers then the display's letter.  Bare, so a panel's
/// `scanline` metadata can use it as an address; `conf` parenthesises it for the display.
/// ONE pattern built from the heading depth rather than a branch per depth: a three-slot pattern fed
/// four numbers repeats its last symbol, which is how a `===` display came out `(15.5a)a)`.
#let dispnum(h, n) = numbering("1." * (h.len() - 1) + "1a", ..h, n)
/// THE DISPLAY'S NUMBER, at the given location — the figure's own print and every `@ref` to it call
/// this ONE function, so neither can show a number the other disagrees with.  An explicit book
/// number (`disp`'s own `<disp-num>` metadata, the first thing in its body) is spelled exactly as
/// given, an equation's own parens included; with none, the letter is the count of AUTOMATIC
/// displays since the last heading up to and including this one, so an explicitly numbered display
/// consumes no letter and the next automatic one continues the same sequence.  `raw`: the bare form
/// external tools match on, with no parens added to the automatic letter.
#let dispid(loc, raw: false) = {
  // `.at(0, default: none)`, not `.first()`: introspection converges over several passes, and a
  // pass where this figure's own `<disp-num>` has not been placed yet must degrade to `none`
  // (every caller already accepts it, `pic-meta`'s `key` included) rather than abort the compile.
  let m = query(selector(<disp-num>).after(loc)).at(0, default: none)
  if m == none { none } else if m.value != none { m.value } else {
    let hs = query(selector(heading).before(loc))
    let sec = selector(<disp-num>).before(m.location())
    let sec = if hs.len() == 0 { sec } else { sec.after(hs.last().location()) }
    // `.before` is INCLUSIVE of `m.location()` itself, so this count already counts `m` — no `+ 1`.
    let n = query(sec).filter(x => x.value == none).len()
    let l = dispnum(counter(heading).at(loc), n)
    if raw { l } else { [(] + l + [)] }
  }
}
/// A display's number as printed, `(13.4.3c)` or `Theorem 10.1`: grey, a size under the text — the
/// parens, when there are any, are already in `id` (`dispid`'s job, not this styling).
#let numtext(id) = text(9pt, luma(130))[#id]
/// THE `Thm` HEADERS OF A DISPLAY are the `<thm-num>` markers between its `<disp-start>` and its
/// `<disp-end>`.  Every marker is emitted unconditionally, so each query settles in one pass: a
/// marker that depends on a state or query of its own costs a layout pass per link and never converged.
#let disp-thms(s, at) = query(selector(<thm-num>).after(s.location()).before(at))

// ---- A REFERENCE NAMES THE ROW, NEVER THE TABLE: a law cited as its whole table sends the reader
// hunting through every row for the one that justifies the step.  Every first cell of a table inside a
// display (`law-row`, bound by `conf`) emits a `<law-row>` marker holding its row index, the same index
// under the label `<table-label:index>`, and under each Lean selector its `#leanf`s name — so the row
// that states a law owns its number, and `@Freyd.Alg.Λ_absorption` lands on it.
/// The `<disp-start>` of the display around `loc`, or `none` outside every display.
#let disp-of(loc) = {
  let s = query(selector(<disp-start>).before(loc)).at(-1, default: none)
  if s != none and query(selector(<disp-end>).after(s.location()).before(loc)).len() == 0 { s }
}
/// A LAW TABLE: a display of two or more numbered rows, no `Thm` header and no book number.  A `Thm`
/// heads a theorem and a book number (`disp(num: …)`) names one book statement: either is cited whole.
#let law-table(s) = {
  let e = query(selector(<disp-end>).after(s.location())).at(0, default: none)
  let m = query(selector(<disp-num>).after(s.location())).at(0, default: none)
  (e != none and m != none and m.value == none and disp-thms(s, e.location()).len() == 0
    and query(selector(<law-row>).after(s.location()).before(e.location())).len() > 1)
}
/// The Lean selectors a cell's `#leanf`s name: the CONTENT TREE walked, not the cell's text matched.
/// `labels`: which calls count; `STATED` collects the statements the cell draws whole instead.
#let lean-keys(c, labels: (<lean-formula>, <lean-row-key>)) = { if type(c) != content { () }
  else if c.func() == metadata { let l = c.at("label", default: none)
    if l in labels { (c.value,) } else if l == <lean-keys-in> { lean-keys(c.value, labels: labels) } else { () } }
  else if c.has("children") { c.children.map(x => lean-keys(x, labels: labels)).flatten() }
  else if c.has("body") { lean-keys(c.body, labels: labels) } else if c.has("child") { lean-keys(c.child, labels: labels) } else { () } }
/// A commutative diagram draws one WHOLE statement (`leancd` takes one selector); a `lean`/`leanc`
/// panel draws a side, which may be the heading's own statement's (`<thin-up>`).
#let STATED = (<lean-cd>,)
// A CONDITIONAL LAW IN A REASON CELL breaks before `⟹`, never inside a hypothesis: the formula file
// cuts there with a `zws` (FormulaRender `render`), which becomes the line break.  Always, not by a
// measured width: the cell is measured inside the chain's own scaling, where every width fits.
#let first-raw(x) = if x.func() == raw { x.text } else if x.has("children") and x.children.len() > 0 { first-raw(x.children.first()) } else if x.has("body") { first-raw(x.body) } else { none }
#let impl-split(c) = if not c.has("children") { c } else {
  let ch = c.children
  for (i, x) in ch.enumerate() {
    let nxt = if i + 1 < ch.len() { first-raw(ch.at(i + 1)) } else { none }
    if x == [#sym.zws] and nxt != none and nxt.starts-with("⟹") { linebreak() } else { x }
  }
}
/// A CITED LAW PRINTS ITS FORMULA, read off Lean as the row stating it prints it, because a generated
/// row number sends the reader off to look the row up.  A cited DISPLAY keeps its number beside the
/// formula only when the book gave it (`Theorem 8.1`, `(7.5)`), since only then is the number a name;
/// `row`: the number is generated, so the formula stands alone.  `keys`: the Lean selectors the cited
/// row or display states; with none the number is all there is.  Under `list`, where no formula file
/// need exist yet, each key is requested instead, so a chapter compiled alone draws what it only cites.
#let law-formula(keys) = if "list" in sys.inputs { for k in keys [#metadata(k)<lean-cited>] } else {
  keys.map(k => impl-split(include "generated/formula/" + k + ".typ")).join([, ]) }
#let cite(id, keys, row: false) = if keys.len() == 0 { id } else if row { law-formula(keys) } else [#id #law-formula(keys)]
/// The Lean selectors the law row around `loc` states: its first cell's `#leanf`s, else its other
/// cells' `#leanf`s, else the declarations its `#leant` cells type — a definition row's formula is that definition,
/// `<name>≜<body>` — else the one declaration its picture draws (`<lean-decls>` of a single
/// selector), else `()`.
#let row-keys(loc) = {
  let ks = query(selector(<law-row-cite>).before(loc)).last().value
  if ks.len() > 0 { ks } else {
    let a = query(selector(<law-row>).before(loc)).last().location()
    let nxt = (query(selector(<law-row>).after(loc)) + query(selector(<disp-end>).after(loc))).map(m => m.location())
    let b = nxt.sorted(key: l => (l.page(), l.position().y)).at(0, default: none)
    let within(l) = query(if b == none { selector(l).after(a) } else { selector(l).after(a).before(b) })
    let fs = within(<lean-formula>).map(m => m.value).dedup()
    let ts = if fs.len() > 0 { fs } else { within(<lean-type>).map(m => m.value).dedup() }
    if ts.len() > 0 { ts } else {
      let vs = within(<lean-decls>).map(m => m.value).filter(v => v.len() == 1).map(v => v.first())
      vs.slice(0, calc.min(1, vs.len()))
    }
  }
}
/// The Lean selectors a display states: its first `Thm` header's formulas; else the `#leanf`s in its
/// own body (`lean-keys`: a chain's cited laws are emitted from a `context`, which it does not walk);
/// else what its heading states, the theorem a derivation with no statement of its own proves.  A
/// display that draws a statement whole (`STATED`) states that one, not its heading's: it cites by number.
/// `(keys, at)`: `at` is the heading when the formula is its, so the link lands where the formula
/// stands; `none` for the display itself.
#let disp-keys(s) = {
  let e = query(selector(<disp-end>).after(s.location())).at(0, default: none)
  let ts = if e == none { () } else { disp-thms(s, e.location()) }
  if ts.len() > 0 {
    let te = query(selector(<thm-end>).after(ts.first().location())).first()
    (query(selector(<lean-formula>).after(ts.first().location()).before(te.location())).map(m => m.value).dedup(), none)
  } else {
    // `<lean-keys-in>` by QUERY too: a wrapper such as `definition` hides its body from the walk.
    let ins = if e == none { () } else { query(selector(<lean-keys-in>).after(s.location()).before(e.location())) }
    let body = query(selector(figure.where(kind: "disp")).before(s.location())).last().body
    let keys(labels) = (lean-keys(body, labels: labels) + ins.map(m => lean-keys(m.value, labels: labels)).flatten()).dedup()
    let own = keys((<lean-formula>, <lean-row-key>))
    let h = query(selector(heading).before(s.location())).at(-1, default: none)
    let hk = if own.len() > 0 or h == none or keys(STATED).len() > 0 { () } else { lean-keys(h.body).dedup() }
    if hk.len() == 0 { (own, none) } else { (hk, h.location()) }
  }
}
/// The book's own number for the display `s` opens (`disp(num: …)`), `none` for a generated one.
#let booknum(s) = query(selector(<disp-num>).after(s.location())).at(0).value
/// A row's number as a reference prints it: the display's number and the row index, `(0.10a.5)`;
/// a row of a theorem display is cited as the theorem, its display's number.
#let rowid(loc, y) = {
  let s = disp-of(loc)
  let m = query(selector(<disp-num>).after(s.location())).at(0)
  if not law-table(s) { dispid(s.location()) }
  else if m.value == none { "(" + dispid(s.location(), raw: true) + "." + str(y) + ")" }
  else { [#m.value.#str(y)] }
}
/// THE GATE: a reference to a law table records itself, where it stands and what it cites, and `conf`
/// stops the compile at the end with every such reference listed — one run names them all.
#let law-gate(it) = {
  let el = it.element
  if el != none and el.func() == figure and el.at("kind", default: none) == "disp" {
    let s = query(selector(<disp-start>).after(el.location())).at(0)
    if law-table(s) {
      let at = disp-of(here())
      [#metadata("p." + str(here().page()) + (if at == none { "" } else { " in (" + dispid(at.location(), raw: true) + ")" }) +
        ": @" + str(it.target) + " cites the whole law table (" + dispid(s.location(), raw: true) + ")")<table-ref>]
    }
  }
}
/// The first cell of every row of a display's table, numbered from 1: a header (`h`) is row 0 and the table's,
/// not a row; a table with none starts its rows at `y = 0`, and that row is a law too (`<dom-laws>`).
/// A cell's LEFT inset, from any form typst accepts for `inset`: a length, a side dictionary, a
/// per-column array or a function of the cell's position.
#let left-inset(i, x, y) = if type(i) == dictionary { i.at("left", default: i.at("x", default: i.at("rest", default: 0pt))) } else if type(i) == array { left-inset(i.at(calc.rem(x, i.len())), x, y) } else if type(i) == function { left-inset(i(x, y), x, y) } else { i }
/// A ROW'S NUMBER, just outside the table's left border: a number column inside the table spends
/// width every row needs, and the page margin is too far from a table that does not start the line.
/// `inset`: the cell's left inset, which separates its content from the border.  Placed, so the cell
/// keeps its width; call it first in a `block` with the body, so it sits on the body's first line.
#let rownum(n, inset) = place(left + top, dx: -inset - 1.5em, box(width: 1.2em, align(right, text(9pt, luma(140))[#n])))
/// The rebuilt cell matches this rule again; its leading `<law-row>` marker is what stops it.  A
/// `<chain-row>` cell is a chain's own line (`chain-table`), numbered by the chain, not by this rule.
#let law-row(h, inset, it) = if (h and it.y == 0) or (it.body.has("children") and it.body.children.at(0, default: none) != none and it.body.children.at(0).at("label", default: none) in (<law-row>, <chain-row>)) { it } else {
  let n = if h { it.y } else { it.y + 1 }
  let f = it.fields()
  let _ = f.remove("body")
  table.cell(..f, {
    [#metadata(n)<law-row>]
    context {
      let s = disp-of(here())
      // The markers a link lands on, INLINE beside the body: as flow items ahead of it, a `horizon`
      // cell placed them against its full-height region, about half a page above the row.
      // `<law-row-keys>`: what a reference to this row prints (`cite`).
      // A key labels only the FIRST row stating it: a table restating a definition stated earlier
      // (a running example's rows) leaves the link on its home.  Read off `<law-row-keys>`, which
      // every row emits unconditionally, so the choice settles in one pass.
      let ks = lean-keys(it.body).dedup()
      let seen = query(selector(<law-row-keys>).before(here())).map(m => m.value).flatten()
      // A cite prints the row's FORMULAS; its row key only labels it, and prints only when the row has
      // no formula — a key `x` of `x≜graph(x)` would print `x ≜ x`.
      let fs = lean-keys(it.body, labels: (<lean-formula>,)).dedup()
      let marks = [#metadata(ks)<law-row-keys>#metadata(if fs.len() > 0 { fs } else { ks })<law-row-cite>] + for k in ks.filter(k => k not in seen) [#metadata(n)#label(k)] + if s != none and s.value != none [#metadata(n)#label(s.value + ":" + str(n))]
      if s != none and law-table(s) {
        let i = f.at("inset", default: auto)
        block({ rownum(n, left-inset(if i == auto { inset } else { i }, it.x, it.y)); marks; it.body })
      } else { marks; it.body }
    }
  })
}

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
// Where a display sits on the page, for `./scripts/book pic`: `here()` is its top-left corner and
// `measure` its extent, so a crop box is read off the layout instead of guessed from the text.
// Under `--input nodraw=1` there is no ink to crop and this is the query's remaining cost: one
// `query(heading.before(here()))` per picture is quadratic in the note (650 pictures × 600 headings).
// `disp: true` only from `disp` below: a picture INSIDE a display reports a crop box of its own, so
// without the flag a gate grouping marks by the preceding `pic` would file a display's arrows under
// whichever inner picture came last.
// `size`: the extent when the caller already has it — every `measure` lays `body` out once more,
// and `P` inside `disp` nests that cost four deep.
// `parts`: one `(page, y, h)` per page the body occupies, one row each, so a crop never runs off its page.
#let pic-meta(key, body, width: auto, disp: false, size: auto, parts: auto) = if NODRAW { none } else { context {
  let hs = query(selector(heading).before(here()))
  let sec = if hs.len() == 0 { "" } else {
    numbering("1.1", ..counter(heading).get()) + " " + plain(hs.last().body) }
  let (sz, pos) = (if size == auto { measure(body, width: width) } else { size }, here().position())
  let parts = if parts == auto { ((page: pos.page, y: pos.y, h: sz.height),) } else { parts }
  // `plain([])` is `none` — an empty caption's `join` — and the key column wants text.
  for t in parts [#metadata((kind: "pic", key: if key == none { "" } else { key }, section: sec,
    page: t.page, x: pos.x.pt(), y: t.y.pt(), disp: disp,
    w: sz.width.pt(), h: t.h.pt()))<pic>]
} }
// A block `body` set in flow at `width`, reporting its crop box off an end marker, not a `measure` that
// lays the body out again: a body split across pages reports one part per page, from its start to the
// content bottom, whole content columns between, and from the content top to its end.  The marker
// carries its start's location, so a nested one cannot be taken for it; before introspection has it,
// the height is a placeholder.  `k`: the key the marker is found by, when a caller outside the body
// must find it too (`kept`); by default the start's own location.
#let pic-span(k, from) = {
  let e = query(selector(<pic-end>).after(from)).find(m => m.value.k == k)
  if e != none { (e.value.at.position(), e.location().position()) }
}
#let pic-flow(key, body, width: auto, disp: false, k: none) = if NODRAW { body } else { context {
  let a = here()
  let k = if k == none { a } else { k }
  let s = pic-span(k, a)
  let (p, q) = if s == none { (a.position(), a.position()) } else { s }
  let top(n) = if n == p.page { p.y } else { MARGIN }
  let bot(n) = if n == q.page { q.y } else { PAGEH - MARGIN }
  pic-meta(key, body, width: width, disp: disp, size: (width: width),
    parts: range(p.page, q.page + 1).map(n => (page: n, y: top(n), h: bot(n) - top(n))))
  body
  [#metadata((k: k, at: a))<pic-end>]
} }
// ONE PAGE OR BROKEN: `f(k)` — a block holding a `pic-flow` keyed `k` — is unbreakable when its
// body fits the content height, so it moves to the next page whole instead of splitting there, and a
// taller one stays breakable.  The height is the markers', not a `measure`: the first pass has none
// and lays every body out unbroken, so the next reads each one's true height off one page; a span
// over two pages can only be one that height made breakable.  `>=` a FULL page, not `>`: laid out
// unbreakable, a taller body is cut at the page foot and reports exactly the content height; 1e-4pt
// is typst's own `fits` tolerance.  Under `NODRAW` there are no markers.
#let kept(f) = context {
  let k = here()
  let s = if NODRAW { none } else { pic-span(k, k) }
  set block(breakable: NODRAW or (s != none and (s.first().page != s.last().page
    or s.last().y - s.first().y >= PAGEH - 2 * MARGIN - 0.0001pt)))
  f(k)
}
#let conf(title: "", body) = {
  set page(width: PAGEW, height: PAGEH, margin: MARGIN)
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
  // The reader needs to know where they are; the same title on every page says nothing.
  set page(header: context {
    let hs = query(heading.where(level: 1).or(heading.where(level: 2)))
    let here-p = here().page()
    let on = hs.filter(hd => hd.location().page() == here-p)
    let before = hs.filter(hd => hd.location().page() < here-p)
    let hd = if on.len() > 0 { on.first() } else if before.len() > 0 { before.last() } else { none }
    if hd != none {
      let n = if hd.numbering == none { none } else { numbering(hd.numbering, ..counter(heading).at(hd.location())) }
      box(stroke: (bottom: 0.7pt), inset: 0.2em, width: 100%)[#text(font: "New Computer Modern Sans", size: 0.8em)[#h(1fr)#if n != none [#n #h(0.4em)]#hd.body]]
    }
  })
  // The heading path is read from the HEADING COUNTER rather than stored anywhere, so it cannot
  // disagree with the heading it sits under.  A display is `(13a)` at top level and `(13.1a)` in
  // subsection §13.1: section references and display references can never be mistaken for one
  // another.  See `disp`.
  set figure(numbering: n => context { [(] + dispnum(counter(heading).get(), n) + [)] })
  show heading: it => { counter(figure.where(kind: "disp")).update(0); it }
  // Every chapter opens a page; `weak` so the first chapter, and a per-chapter pdf, get no blank page.
  show heading.where(level: 1): it => { pagebreak(weak: true); it }
  // A REFERENCE RESOLVES AT THE DISPLAY, NOT AT THE SENTENCE THAT CITES IT: a `context` inside a
  // reference resolves where the REFERENCE stands, so a display in §12 cited from §13 came out `(13.n)`.
  show ref: it => context {
    let el = it.element
    // A row of a law table cites as its formula alone; a display, or a row of a theorem display,
    // as the formula it states, after the display's number only when the book gave it (`cite`).
    // `to`: where the cited formula stands, when not at the element (`disp-keys`); a book number
    // printed beside it names the display, so then the link stays on the display.
    let (id, keys, row, to) = if el == none { (none, (), false, none) }
      else if el.func() == figure and el.at("kind", default: none) == "disp" {
        let s = query(selector(<disp-start>).after(el.location())).at(0)
        let (ks, at) = disp-keys(s)
        (dispid(el.location()), ks, booknum(s) == none, at) }
      else if el.func() == metadata and type(el.value) == int {
        let s = disp-of(el.location())
        if law-table(s) { (rowid(el.location(), el.value), row-keys(el.location()), true, none) }
        else { let (ks, at) = disp-keys(s); (rowid(el.location(), el.value), ks, booknum(s) == none, at) } }
      else { (none, (), false, none) }
    if el != none and el.func() == figure { law-gate(it) }
    if id == none { it } else { link(if to == none or not row { el.location() } else { to }, cite(id, keys, row: row)) }
    // The whole note records what each reference printed, so a chapter compiled alone prints a label
    // of another chapter the same way (`make ref-ids`), not as the label's own name.
    // A heading reference prints its counter dot-joined: typst drops the numbering pattern's trailing `.`.
    // What `cite` needs beside the number, under `<label>#cite`: the plain entry stays a string, which
    // an older tree's compile (`diff-crop`'s before) still prints.
    if NOTEROOT.get() and id != none [#metadata((str(it.target) + "#cite", (keys: keys, row: row)))<ref-id>]
    let rec = if id != none { plain(id) } else if el != none and el.func() == heading and el.numbering != none {
      counter(heading).at(el.location()).map(str).join(".") }
    if NOTEROOT.get() and rec != none [#metadata((str(it.target), rec))<ref-id>]
  }
  // Breakable when taller than a page (`kept`), though a figure is not: a chain table that tall
  // must run on.
  // The blocks INSIDE a display: breakable too, or a table taller than a page loses its last rows
  // past the foot, silently (`<edit-mono>`'s last row).  The display's own block is `kept`'s choice.
  // `pic-flow` here and not in `disp`: `kept` must find the body's markers from outside its block.
  show figure.where(kind: "disp"): set block(breakable: true)
  // A display is not running prose: its second paragraph starts flush, not at the text's 1em
  // indent, and a list or a table reads from the display's left edge, not centred like the pictures
  // `figure` centres, with a gap between items so a gloss stays with the formula above it.
  show figure.where(kind: "disp"): set par(first-line-indent: 0em)
  show figure.where(kind: "disp"): it => kept(k => block(width: 100%, {
    show list: set align(left)
    show table: set align(left)
    show table: t => { show table.cell.where(x: 0): law-row.with(t.children.any(c => c.func() == table.header), t.at("inset", default: 5pt)); t }
    set list(indent: 0pt, spacing: 0.9em)
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
      id: plain(dispid(here(), raw: true)),
      label: if it.at("label", default: none) == none { "" } else { str(it.label) }))
    // THE NUMBER GOES IN THE DISPLAY'S FIRST `Thm` HEADER, at its right end (see `Thm`); a display
    // with no `Thm` sets it on its own line above, right-aligned to the column.  In the margin it
    // stood a page gutter away from the table it names.
    context {
      // its label, so a row inside can name itself `<label:row>`
      [#metadata(if it.at("label", default: none) == none { none } else { str(it.label) })<disp-start>]
      context {
        let s = query(selector(<disp-start>).before(here())).last()
        let e = query(selector(<disp-end>).after(here())).at(0, default: none)
        if e == none or disp-thms(s, e.location()).len() == 0 {
          block(width: 100%, below: 2pt, align(right, numtext(dispid(here()))))
        }
      }
    }
    // A string-diagram panel is addressed by its display and its place in it (see `hm-meta`), so the
    // count restarts here; the update draws nothing.
    counter("hm-panel").update(0)
    pic-flow(dispid(k, raw: true), it.body,
      width: PAGEW - 2 * MARGIN, disp: true, k: k)
    [#metadata(none)<disp-end>]
  }))
  body
  context {
    let bad = query(<table-ref>).map(m => m.value)
    if bad.len() > 0 {
      panic(str(bad.len()) + " reference(s) cite a whole law table; cite the row that justifies the step — " +
        "@<the selector its #leanf names> or @<table label>:<row number>\n" + bad.join("\n"))
    }
  }
}


/// A CHAPTER COMPILED ALONE — its file starts `#show: note-chapter.with(N)` — must look like its
/// pages in the book, and a whole-note compile costs about 13 GiB, which every gate paid.  Same
/// rules as `conf`; the heading counter set to N-1 so §13 numbers as §13; and a reference to a
/// label in another chapter rendered as its `names` entry, or as the label's own text, instead of
/// stopping the compile.  Inside the whole book the root has already applied `conf` and the counter
/// already stands at N-1, so there the chapter's own rules are skipped and nothing changes.
///
/// `title`: NEVER a hardcoded default — a chapter belongs to whichever note split it, and a shared
/// fallback here is how every note's chapter printed the SAME title.  A chapter file passes none, so
/// this falls to `--input title=...` (`./scripts/note-files --title`, spliced in by the Makefile);
/// missing both, it stops rather than guess.
// Typst's own heading counter steps at EVERY level-1 heading regardless of that instance's own
// `numbering` (`set heading(numbering: none)` inside the show below only changes what dvdtyp's
// OWN show rule would have printed for `it`, not whether the built-in counter steps) — and it can
// only ever step forward from a non-negative state, so it cannot land ON N by priming N-1 when N
// is 0.  So the chapter's own first-level heading is drawn unnumbered, with its number as the
// literal N in dvdtyp's own style (`dvd.typ`'s `show heading`), and the counter is corrected to N
// AFTER that heading's own (otherwise wrong) step, for every heading and display that follows —
// works for any N including 0.
// Mirrors dvdtyp's own per-heading `show heading` (`dvd.typ`'s `set text(...)`/`set
// par(first-line-indent: 0em)`/`numbering("1.", ..)`) exactly, since our show rule for the
// level-1 heading replaces the heading element outright and so no longer matches dvdtyp's.
#let chapter-number(N) = {
  text(colors.at(6), weight: 500)[#sym.section]
  text(colors.at(6))[#numbering("1.", N) ]
}
#let chapter-heading(N, it) = {
  set text(font: "New Computer Modern Sans")
  set par(first-line-indent: 0em)
  chapter-number(N)
  it.body
}
// Included or alone is read off the page `conf` sets, a STYLE, not off `NOTEROOT`: a state reads its
// initial `false` on the first pass, which laid the whole note out as standalone chapters and spent
// a layout pass, so the note's position-dependent blocks ran out of passes ("did not converge").
/// EVERY SECTION OPENS A PAGE, except one that follows its chapter heading with nothing between, which
/// shares the chapter's opening page.  Read off the chapter body's own children, never by a query: a
/// break that depends on the heading before it, queried, ran the companion out of layout passes.
#let has-section(c) = type(c) == content and ((c.func() == heading and c.depth == 2)
  or (c.has("children") and c.children.any(has-section)) or (c.has("child") and has-section(c.child)))
#let section-breaks(doc) = if type(doc) != content or not doc.has("children") { doc } else {
  let (prev, gap) = (none, ([ ].func(), parbreak))
  for c in doc.children {
    // A `set`/`show` wraps what follows it in one styled element, which cannot be rebuilt around a break.
    assert(not (c.has("child") and c.has("styles") and has-section(c.child)), message: "section-breaks: a "
      + "set/show rule wraps a section heading, so it gets no page break; scope the rule to a block")
    if c.func() == heading and c.depth == 2 and not (prev != none and prev.func() == heading and prev.depth == 1) {
      pagebreak(weak: true)
    }
    if c.func() == doc.func() { section-breaks(c) } else { c }
    if c.func() not in gap { prev = c }
  }
}
#let note-chapter(N, title: none, names: (:), doc) = context if page.height == PAGEH {
  show heading.where(level: 1): it => { set heading(numbering: none); chapter-heading(N, it); counter(heading).update(N) }
  section-breaks(doc)
} else {
  let title = if title != none { title } else { sys.inputs.at("title", default: none) }
  if title == none {
    panic("note-chapter: no title — pass title: to note-chapter.with(...), or compile with " +
      "--input title=\"$(./scripts/note-files --title)\"")
  }
  conf(title: title, {
    show heading.where(level: 1): it => { set heading(numbering: none); chapter-heading(N, it); counter(heading).update(N) }
    // Bound after `conf`'s own `ref` rule, so it runs FIRST and a label that is not in this chapter
    // never reaches `it.element`: reading that is what turns a cross-chapter reference into an error.
    show ref: it => context {
      let t = str(it.target)
      let present = query(it.target).len() > 0
      if t in names { if present { law-gate(it); link(it.target, names.at(t)) } else { names.at(t) } }
      else if present { it } else {
        // Another chapter's label: printed as the root printed it (`make ref-ids`), never as its name.
        let p = sys.inputs.at("refs", default: none)
        // A QUERY with no `refs` (the `ref-ids` listing itself; `cdscan=1`: cd-check) renders no
        // reference; the chapter's panel listing is given `refs`, so `cite` requests what it prints.
        if p == none and ("list" in sys.inputs or "cdscan" in sys.inputs) { t } else {
        if p == none { panic("@" + t + " is in another chapter: compile with --input refs=/.lake/build/ref-ids-<note>.json, which `make ref-ids` writes") }
        let r = json(p).to-dict().at(t, default: none)
        if r == none { panic("@" + t + ": no label of that name in the whole note (" + p + "), so no chapter can print it") }
        let c = json(p).to-dict().at(t + "#cite", default: none)
        if c == none { r } else { cite(r, c.keys, row: c.row) }
        }
      }
    }
    section-breaks(doc)
  })
}

/// A NUMBERED DISPLAY carrying a letter-suffixed section path — `(13a)` or `(13.1a)` — at its right
/// edge; a literal number typed into prose is what this makes impossible.  `kind: "disp"`: ONE
/// sequence per heading whatever the display is.
// Its crop box and its page break are `conf`'s show rule; the width is the text width.
// `num`: the book's own number for a display that states one, spelled exactly as the book prints
// it — `"(10.3)"` for an equation, `"Theorem 10.1"` for a theorem, proposition or exercise; `none`
// (the default) keeps the automatic section+letter, which SKIPS every display that carries one
// rather than give it a letter of its own.  Recorded as `<disp-num>` metadata, the first thing in
// the figure's own body, so `dispid` reads one value for both the figure's print and every `@ref`.
#let disp(body, num: none) = figure(kind: "disp", supplement: none, [#metadata(num)<disp-num>#body])

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
/// `fit(w, sz)`: that second factor for a picture `w` wide, already at `s`, in the region `sz`.
#let fit(w, sz) = if w > sz.width and sz.width > 0pt { sz.width / w * 100% } else { 100% }
/// The product of every factor the helpers here have scaled a picture by: `scale` tells its body
/// nothing, and a picture that must hold a length ON THE PAGE (`cpanel`'s frame pad) needs it.
/// `measure` does not see an update inside what it measures, only one placed before it.  A STACK of
/// factors, popped exactly: a running `x / k` drifts in the last bit, and typst then never converges.
#let pscale = state("pscale", ())
#let pscaled(k, body) = {
  pscale.update(a => a + (k,)); scale(k * 100%, reflow: true, body); pscale.update(a => a.slice(0, -1))
}
#let pscale-get() = pscale.get().product(default: 1.0)
#let P(p, s: 92%, key: none) = layout(sz => align(center, box({
  let q = scale(x: s, y: s, reflow: true, p)
  let m = measure(q)
  let f = fit(m.width, sz)
  let q = if f == 100% { q } else { scale(x: f, y: f, reflow: true, q) }
  // `m * f`, not a second `measure` of the scaled `q`: the two differ only in the last bit (~1e-14pt).
  if key != none { pic-meta(key, q, size: (width: m.width * (f / 100%), height: m.height * (f / 100%))) }
  q
})))
/// A picture set INLINE in a table header.  Deliberately large: at running-text size the theorem it
/// states cannot be read at all.
#let Pin(p, s: 70%) = box(baseline: 36%, pscaled(s / 100%, p))
/// A chain table's top header row: the theorem, one size up from the body.
#let Th(body) = table.cell(colspan: 3, text(12.5pt)[#body])
/// A figure transcribed from the paper by hand — used only where there is no Lean STATEMENT to
/// export, i.e. for the two primitive operations.
#let fig(body) = align(center, box(cetz.canvas(length: 0.78cm, body)))
/// Pictures side by side.  Every exported canvas is symmetric about its own `y = 0`, so aligning on the
/// horizon puts all their wires at one height; a per-box `baseline:` shift cannot, being a fraction of each.
#let row(items, s: 100%) = align(center, box(grid(
  columns: items.len(), align: horizon, column-gutter: 3pt,
  ..items.map(t => pscaled(s / 100%, t)))))

/// A proof in ONE ROW, the rule under each step.  The exporter draws the `=` (or `≤`) at the LEFT edge
/// of every step after the first, so a left-aligned hint lands under it and the first hint is empty.
#let chain(steps, hints, s: 62%) = align(center, box(grid(
  columns: steps.len(), align: horizon, column-gutter: 14pt, row-gutter: 1pt,
  ..steps.map(t => pscaled(s / 100%, t)),
  ..hints.map(h => src[#h]))))

// WHAT THE TABLE SETTLES, in its top row: the reader needs the destination before the steps, and a
// footer would only confirm it.  Grey ground, heavier rule under it, no new font size.
// The display's number at its right end, in the display's first `Thm` only; an empty column as wide
// on the left keeps the theorem centred on the cell.  Outside a display it is the plain header.
#let Thm(body, cols: 2) = table.cell(colspan: cols, fill: luma(233), align: center + horizon,
  stroke: (rest: 0.4pt + luma(190), bottom: 1.1pt + luma(120)), {
    [#metadata(none)<thm-num>]
    context {
      let s = query(selector(<disp-start>).before(here())).at(-1, default: none)
      let inside = s != none and query(selector(<disp-end>).after(s.location()).before(here())).len() == 0
      if not inside or disp-thms(s, here()).len() != 1 { strong(body) } else {
        let n = numtext(dispid(s.location()))
        let w = measure(n).width
        grid(columns: (w, 1fr, w), column-gutter: 4pt, [], strong(body), align(right + top, n))
      }
    }
    // Where the header ends: a `<lean-formula>` between a `<thm-num>` and this states the display
    // (`law-ref`).
    [#metadata(none)<thm-end>]
  })

// `auto` and not a fixed width: a panel column is as wide as the panels IN IT, so the column beside
// it keeps every point they do not use.  A constant is a guess made against one table's widest panel
// and spent in every other, and the picture it starves overflows its own column — both pictures are
// centred, so they grow towards each other and a label of one lands on a label of the other
// (`./scripts/labelfit`), which no per-panel geometry can prevent.
// A ROW IS NEVER SPLIT at a page break: its cells are pictures, which cannot be cut, so a row split
// there overran the page foot and drew its panels over the row above (`<edit-mono>`'s last rows).
#let CALC-INSET = (x: 9pt, y: 3pt)
#let calc-table(..rows, cols: (1fr, auto), al: (left + horizon, center + horizon), pr: 10pt) = {
  set table.cell(breakable: false)
  pad(right: pr, table(columns: cols, align: al, inset: CALC-INSET, stroke: 0.4pt + luma(190), ..rows)) }

#let EQ = text(luma(140))[$=$]
// A chain step that only opens a definition (`FormulaRender.stepRel`'s `≜`).
#let DF = text(luma(140))[$≜$]

// The op lane is one glyph wide: `⊑`, `⊒` and `=` all measure 8.95pt here.  `layout` gives the
// CELL's width, so a row that cannot fit picture and formula side by side stacks them itself.
#let OPW = 10pt

// A row is TALLER than it is wide once the second column is a picture too, so the circuit and its
// formula stack on one left edge — which `step`'s side-by-side branch cannot give.
#let vstep(op, pic, f) = kept(k => layout(sz => {
  let row = grid(columns: (OPW, 1fr), align: (left + horizon, left + horizon),
    column-gutter: 6pt, op, stack(spacing: 5pt, box(pic), f))
  pic-flow(plain(f), row, width: sz.width, k: k)
}))
