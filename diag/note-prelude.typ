// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name (see circuit.typ's header); `dot` is renamed on the way in for that reason.
#import "circuit.typ": conv, LEAD, meet, wire, bend, gbox, boxrun, boxrun-w, dot as wiredot, tape, tape-fork, tape-join, TINT, delta as wcopy, nabla as wmerge, frc, banana, TAPEEDGE, est-R-box, union-box
// draw.typ owns the Hinze–Marsden geometry (Reduce) and every helper this note draws with:
// it is also the standalone PNG of those laws, and one geometry drawn in two files is one that drifts.
#import "draw.typ": homeq, TCOL, BCOL, objcol, GIVEN1, GIVEN2, INDUCED, SLACK, lab, ar, node, arc, e, zw, zsq, zsqc, zstep, znamed, zderiv, zline, zpair, skel, capbox, pair, blocked, fb-ALLC, fb-MAPC, fb-ZC, KNEE, lanecheck, hm-bead, hm-name, hm-port, hm-region, hm-wire, SQ, RQ
// The two panel helpers, one per convention: `cpanel` draws a circuit (wire = object, box = a
// morphism), `dpanel` a Hinze–Marsden panel (wire = functor, bead = an arrow).  Neither file
// imports the other.
#import "cpanel.typ": cpanel
#import "dpanel.typ": dpanel, hm-meta
#import "gpanel.typ": gpanel
// A picture is a Lean declaration's name and nothing else: the exporter draws it into diag/generated/
// and decides every mark, type and row.  `--input list=1` lists the names instead of drawing them.
// ONE CALL IS ONE BOX: `lean(a, b)` names a PAIR — the two panels that stand beside each other, with
// the relation symbol between them — and the exporter draws the selectors of one call to one depth,
// so both sides of the equation come out the same height and line up on the bead they share.  Two
// separate calls share nothing, which is what keeps a calc-table's cells as short as their own
// pictures.
#let trow(l, r) = align(center, grid(columns: 3, align: horizon, column-gutter: 6pt, l, SQ, r))
// One body, two routes: `dir` is the exporter's output directory and `label` the metadata the
// listing queries, because a second copy of this would drift from the first at the next change.
#let lean-call(dir, label, ns) = {
  [#metadata(ns.join("+"))#label]
  if "list" not in sys.inputs {
    let pics = ns.map(n => { import dir + n + ".typ": pic; pic })
    if pics.len() == 1 { pics.at(0) } else if pics.len() == 2 { trow(..pics) } else {
      panic("a lean(…) call draws one panel or a pair, not " + str(pics.len()))
    }
  }
}
// A COPRODUCT STAYS ONE WIRE THAT THE HINZE–MARSDEN ROUTE CANNOT OPEN, so a panel of a side that
// branches is drawn at ONE branch, and `branch:` names which — `.inl`/`.inr`, innermost last.  It is
// an argument of THIS route and not part of the selector because the circuit draws the fork itself
// and takes the WHOLE side: the row's two cells then name one declaration and one side, and the
// restriction sits where it belongs, on the picture that has it.
#let lean(..sels, branch: none) = lean-call("generated/", <lean-panel>,
  sels.pos().map(n => if branch == none { n } else { n + "." + branch }))
// The CIRCUIT column's counterpart: the same declaration read by `diag-export --circuit`, which
// walks the same Expr under the monoidal reading.
#let leanc(..sels) = lean-call("generated/circuit/", <lean-circuit>, sels.pos())
// The COMMUTATIVE DIAGRAM route: `diag-export --commutative` draws the statement as a graph rather
// than a term walk.  Unlike `lean`/`leanc`, a `+` inside ONE selector is not a pair of boxes but two
// DIFFERENT statements drawn on one page (`diag/cd-panels.txt`'s `A+B`), so it stays one string and
// `leancd` takes exactly one selector, never `..sels`.
#let leancd(sel) = lean-call("generated/commutative/", <lean-cd>, (sel,))
// The ELEMENT-GRAPH route: `diag-export --graph` decides a concrete relation between finite types
// pair by pair, and `gpanel` draws it; the call adds only the layout (`gpanel.typ`'s header), never a pair.
#let leang(sel, ..layout) = {
  [#metadata(sel)<lean-graph>]
  if "list" not in sys.inputs { import "generated/graph/" + sel + ".typ": graph; gpanel(graph, ..layout) }
}
// A FORMULA GENERATED FROM THE SAME DECLARATION a row's picture is drawn from, so the words beside
// a `#lean`/`#leanc` panel are checked against the declaration and not typed by hand: the file
// `diag-export --formula` writes is inline `raw` and nothing else — no `pic` binding — so it is
// `#include`d directly rather than imported.  A raw is one unbreakable word, so the statement's
// relation closes its raw and a `#sym.zws` stands between the two, giving the cell the place to
// wrap that a hand-typed formula's `\` gives it.
#let lean-text(dir, label, sel) = {
  [#metadata(sel)#label]
  if "list" not in sys.inputs { include dir + sel + ".typ" }
}
#let leanf(sel) = lean-text("generated/formula/", <lean-formula>, sel)
// A TYPE CELL, from `diag-export --type`: the hom a declaration's arrows share, in the note's
// spelling, so a table's type column is read off the declaration its row already cites.
#let leant(sel) = lean-text("generated/type/", <lean-type>, sel)
// EVERY PICTURE OF A THEOREM BELOW IS EXPORTED, NOT DRAWN: hand-drawing is how the first draft got
// `inter_assoc` wrong.  `./scripts/diag-regen` redraws every binding, reading the list off these imports.
#import "generated/Freyd.Diag.meet_top.typ": pic as p-meet-top
#import "generated/Freyd.Diag.meet_comm.typ": pic as p-meet-comm
#import "generated/Freyd.Diag.meet_assoc.typ": pic as p-meet-assoc
#import "generated/Freyd.Diag.meet_idem.typ": pic as p-meet-idem
#import "generated/Freyd.Diag.semidistrib_of_lax.typ": pic as p-semidistrib
#import "generated/Freyd.Diag.CartBicat.«∇_assoc».typ": pic as p-n-assoc
#import "generated/Freyd.Diag.CartBicat.«∇_comm».typ": pic as p-n-comm
#import "generated/Freyd.Diag.CartBicat.«∇_unit».typ": pic as p-n-unit
#import "generated/Freyd.Diag.CartBicat.«∇Δ≤𝟙».typ": pic as p-37
#import "generated/Freyd.Diag.CartBicat.«𝟙≤Δ∇».typ": pic as p-38
#import "generated/Freyd.Diag.CartBicat.«?!≤𝟙».typ": pic as p-39
#import "generated/Freyd.Diag.CartBicat.«𝟙≤!?».typ": pic as p-40
#import "generated/Freyd.Diag.CartBicat.frob.proof.typ": branches as frobb
#import "generated/Freyd.Diag.CartBicat.lax_Δ.typ": pic as p-lax-delta
#import "generated/Freyd.Diag.CartBicat.lax_!.typ": pic as p-lax-bang
#import "generated/Freyd.Diag.CartBicat.«°_slide».typ": pic as p-conv-slide
#import "generated/Freyd.Diag.dom_cd.typ": pic as p-dom-cd
#import "generated/Freyd.Diag.dom_comp_le.typ": pic as p-dom-comp-le
#import "generated/Freyd.Diag.comp_meet_of_singleValued.typ": lhs as p-236a, rhs as p-236b
// The allegory layer's division (last section).  `Freyd.Alg`, not `Freyd.Diag`: `/` is a theorem of
// `Freyd/S2_30.lean` and `AOP/A4_4`, and of nothing in `diag/`.
#import "generated/Freyd.Alg.le_div_iff.typ": pic as p-le-div
#import "generated/Freyd.Alg.le_leftDiv_iff.typ": pic as p-le-ldiv
#import "generated/Freyd.Alg.DivisionAllegory.div_comp_le.typ": pic as p-div-cancel
#import "generated/Freyd.Alg.leftDiv_comp_le.typ": pic as p-ldiv-cancel
#import "generated/Freyd.Alg.div_comp_assoc.typ": pic as p-div-assoc
#import "generated/Freyd.Alg.leftDiv_comp.typ": pic as p-ldiv-assoc
#import "generated/Freyd.Alg.map_comp_div.typ": pic as p-map-div
#import "generated/Freyd.Alg.div_comp_recip_map.typ": pic as p-div-map
// §2.314's list, in the book's order.
#import "generated/Freyd.Alg.div_comp.typ": pic as p-div-comp
#import "generated/Freyd.Alg.one_le_div_self.typ": pic as p-one-div
#import "generated/Freyd.Alg.div_self_comp_self.typ": pic as p-div-self-idem
#import "generated/Freyd.Alg.div_self_comp.typ": pic as p-div-self
#import "generated/Freyd.Alg.div_one.typ": pic as p-div-one
#import "generated/Freyd.Alg.div_union.typ": pic as p-div-union
#import "generated/Freyd.Alg.leftDiv_div.typ": pic as p-ldiv-div

// Row numbers so a law can be cited: `it.y` is the table's OWN index, so deleting a row renumbers
// the rest.  Rebuilt as a cell, not returned bare — bare content loses the row's height.
#let rownum = it => if it.y == 0 or it.body.func() == grid { it } else {
  let f = it.fields()
  let _ = f.remove("body")
  table.cell(..f, grid(columns: (0.55cm, 1fr), text(9pt, luma(140))[#it.y], it.body))
}

// The Hinze–Marsden picture column the derivation tables share; the formula column takes the rest
// of the 22cm block, and 9cm is what the widest circuit in that column still fits in.
#let HMW = 9cm

// A CITED DISPLAY RENDERS AS ITS NAME, the way B&dM cite a law in a hint; a number sends the reader
// off to look the display up.  `≜ x` is the display that DEFINES `x`; a display named here nowhere
// keeps its number (`conf`'s rule).  Laws carry B&dM's names, lowercase as the book prints them.
#let refname = (
  "conv-defn": [≜ `°`],
  "relator-defn": [≜ relator],
  "relprod-defn": [≜ `×`],
  "mu-defn": [≜ `μ`],
  "cata-defining": [≜ `reduce`],
  "comb-fns": [≜ `subseq`],
  "cup-defn": [≜ `cup`],
  "est-defn": [≜ `est`],
  "lax-defn": [≜ lax],
  "mon-defn": [≜ monotonic],
  "dist-defn": [≜ distributes],
  "takewhile-defn": [≜ `takewhile`],
  "mss-defn": [≜ `mss`],
  "filter-defn": [≜ `filter`],
  "party-defn": [≜ `party`],
  "cyl-defn": [≜ `paths`],
  "van-defn": [≜ `secure`],
  "thin-defn": [≜ `thin`],
  "path-defn": [≜ `cost`],
  "thinlist-defn": [≜ `thinlist`],
  "knap-defn": [≜ `within`],
  "para-defn": [≜ `partition`],
  "tour-defn": [≜ `tour`],
  "dp-defn": [≜ `H`],
  "edit-defn": [≜ `edit`],
  "mct-defn": [≜ `flatten`],
  "code-defn": [≜ `decode`],
  "greedy-defn": [≜ `H`, `Q`],
  "entab-defn": [≜ `detab`],
  "tardy-defn": [≜ `bagify`],
  "tex-defn": [≜ `intern`],
  "fokkinga": [mutual recursion],
  "horner": [Horner's rule],
  "absorption-pic": [absorption],
  "cata-fusion": [fusion],
  "hylo-mu": [hylomorphism theorem],
  "greedy-thm72": [greedy theorem],
  "thin-83": [thin-elimination variant],
  "thin-thm81": [thinning theorem],
  "thinlist-thm82": [binary thinning theorem],
  "dp-laws": [dynamic programming theorem],
)
#let IMP = text(SLACK)[$arrow.l.double$]
#let TH = 1.2   // a fraction box is two lines tall
#let IFF = text(SLACK)[$arrow.l.r.double$]
#let So-box = ([`S°`], 0.85, true)
// A derivation read LEFT TO RIGHT: one panel per `(op, panel, reason[, formula])` step, the op
// between it and the step before, the formula above, the reason underneath both.  Steps pack
// greedily into lines of the cell's width, a continued line opening with its op; a line's slack
// widens its columns — or, `fill`, ONE line, the pictures scaled by the factor that spends it all.
#let hchain(..steps, fill: false) = layout(sz => {
  let gut = 4pt
  let ss = steps.pos().map(s => (op: s.at(0), pic: box(s.at(1)), why: s.at(2), f: s.at(3, default: none),
    w: measure(box(s.at(1))).width))
  if fill {
    let lanes = ss.len() - if ss.first().op == none { 1 } else { 0 }
    // `--list` renders the panels as bare metadata, so every width is zero and there is no slack to spend
    let tot = ss.map(s => s.w).sum(default: 0pt)
    let k = if tot == 0pt { 1.0 } else { (sz.width - lanes * (OPW + 2 * gut)) / tot }
    ss = ss.map(s => s + (pic: scale(k * 100%, reflow: true, s.pic), w: s.w * k))
  }
  let (lines, cur, used) = ((), (), 0pt)
  for s in ss {
    let add = s.w + if lines.len() == 0 and cur.len() == 0 and s.op == none { 0pt } else { OPW + 2 * gut }
    if not fill and cur.len() > 0 and used + add > sz.width { lines.push(cur); cur = (); used = s.w } else { used += add }
    cur.push(s)
  }
  lines.push(cur)
  stack(dir: ttb, spacing: 10pt, ..lines.enumerate().map(((li, line)) => {
    let extra = calc.max(0pt, (sz.width - line.map(s => s.w).sum()
      - (line.len() - if li == 0 and line.first().op == none { 1 } else { 0 }) * (OPW + 2 * gut)) / line.len())
    let py = if line.any(s => s.f != none) { 1 } else { 0 }     // the picture row sits under the formulas
    let (cols, fr, pr, rr) = ((), (), (), ())
    for (i, s) in line.enumerate() {
      let op = not (li == 0 and i == 0 and s.op == none)
      if op { cols.push(OPW); pr.push(s.op) }
      cols.push(s.w + extra)
      pr.push({ pic-meta(plain(if s.f == none { s.why } else { s.f }), s.pic); s.pic })
      let span = grid.cell.with(colspan: if op { 2 } else { 1 })
      let wide = box.with(width: s.w + extra + if op { OPW + gut } else { 0pt })
      fr.push(span(wide(if s.f == none { [] } else { s.f })))
      rr.push(span(wide(s.why)))
    }
    grid(columns: cols, column-gutter: gut, row-gutter: 4pt,
      align: (x, y) => if y == py { center + horizon } else { left + top },
      ..if py == 1 { fr } else { () }, ..pr, ..rr)
  }))
})
// The op lane is one glyph wide: `⊑`, `⊒` and `=` all measure 8.95pt here.  `layout` gives the
// CELL's width, so a row that cannot fit picture and formula side by side stacks them itself.
// PICTURE FIRST on a shared left edge (a table rebinds `pw` to its widest drawing); the formula is
// flush RIGHT in both branches, so it lands on one edge whether the row fits side by side or stacks.
#let step(op, pic, f, pw: none) = layout(sz => {
  let gut = 6pt
  // `box`: `P` centres its drawing in whatever width it gets, which would undo the shared left edge.
  let p = box(pic)
  let lane = if pw == none { measure(p).width } else { pw }
  let row = if measure(f).width + lane + gut <= sz.width - OPW - gut {
    grid(columns: (OPW, lane, 1fr), align: (left + horizon, left + horizon, right + horizon),
      column-gutter: gut, op, p, f)
  } else {
    grid(columns: (OPW, 1fr), align: (left + horizon, left + horizon), column-gutter: gut,
      op, stack(spacing: 5pt, p, align(right, f)))
  }
  pic-meta(plain(f), row, width: sz.width)
  row
})
#let sort-P-box = ([`sort(P)`], 2.23, true)
#let thinlist-Q-box = ([`thinlist(Q)`], 3.0, true)
#let est-Rc-box = ([`est(R°)`], 2.2, true)
#let listcp-F-box = ([`listcp`], 1.87, false)
#let pair-g-box = ([`⟨g₁,g₂⟩`], 2.2, false)
#let minlist-R-box = ([`minlist(R)`], 2.93, true)
// note-split: prelude footer — written by scripts/note-split and stripped by scripts/note-join
#let note-chapter = note-chapter.with(names: refname)
