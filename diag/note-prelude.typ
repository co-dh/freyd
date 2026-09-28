// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name (see circuit.typ's header); `dot` is renamed on the way in for that reason.
#import "circuit.typ": conv, LEAD, meet, wire, bend, gbox, boxrun, boxrun-w, dot as wiredot, tape, tape-fork, tape-join, TINT, delta as wcopy, nabla as wmerge, frc, banana, TAPEEDGE, est-R-box, union-box
// draw.typ owns the Hinze–Marsden geometry (Reduce) and every helper this note draws with:
// it is also the standalone PNG of those laws, and one geometry drawn in two files is one that drifts.
#import "draw.typ": homeq, TCOL, BCOL, objcol, GIVEN1, GIVEN2, INDUCED, SLACK, lab, ar, node, arc, e, zw, zsq, zsqc, zstep, znamed, zderiv, zline, zpair, skel, capbox, pair, pair-fill, blocked, fb-ALLC, fb-MAPC, fb-ZC, KNEE, lanecheck, hm-bead, hm-name, hm-port, hm-region, hm-wire, SQ, RQ
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
// `op` is what stands between them: the relation by default, `∩`/`∪` when the pair is the two
// operands `.inl`/`.inr` of one side — a meet or union is a label between pictures, never wiring.
#let trow(l, r, op: SQ) = align(center, grid(columns: 3, align: horizon, column-gutter: 6pt, l, op, r))
// One body, two routes: `dir` is the exporter's output directory and `label` the metadata the
// listing queries, because a second copy of this would drift from the first at the next change.
// `lean-pics` is the call's metadata and its panels one by one, for a layout that puts something
// between them — a chain's steps in `hchain` — while the call stays ONE box.
#let lean-pics(dir, label, ns) = ([#metadata(ns.join("+"))#label],
  // a call of several selectors is its own directory, the exporter's `outPath`: a selector drawn in
  // a shared box and drawn alone are two pictures
  // each file's MODULE: a chain reads the string route's `dup` beside `pic` (`lean-chain`)
  if "list" in sys.inputs { ns.map(n => (pic: [], dup: false)) } else {
    let sub = if ns.len() > 1 { ns.join("/") + "/" } else { "" }
    ns.map(n => { import dir + sub + n + ".typ" as f; f }) })
#let lean-call(dir, label, ns, op: SQ) = {
  let (m, fs) = lean-pics(dir, label, ns)
  let pics = fs.map(f => f.pic)
  m
  if pics.len() == 1 { pics.at(0) } else if pics.len() == 2 { trow(..pics, op: op) } else {
    panic("a lean(…) call draws one panel or a pair, not " + str(pics.len()) + "; a chain is lean-chain(…)")
  }
}
// A COPRODUCT STAYS ONE WIRE THAT THE HINZE–MARSDEN ROUTE CANNOT OPEN, so a panel of a side that
// branches is drawn at ONE branch, and `branch:` names which — `.inl`/`.inr`, innermost last.  It is
// an argument of THIS route and not part of the selector because the circuit draws the fork itself
// and takes the WHOLE side: the row's two cells then name one declaration and one side, and the
// restriction sits where it belongs, on the picture that has it.
// `step: true` marks a CALC-TABLE STEP: each side of a step is its own row, stacked, so there is no
// `=` for two panels to stand beside; `diag-export --list` refuses a statement's two sides in two
// calls unless both are steps (`splitSides`).
#let lean-step(ns) = for n in ns [#metadata(n)<lean-step>]
#let lean(..sels, branch: none, op: SQ, step: false) = {
  let ns = sels.pos().map(n => if branch == none { n } else { n + "." + branch })
  if step { lean-step(ns) }
  lean-call("generated/", <lean-panel>, op: op, ns)
}
// The CIRCUIT column's counterpart: the same declaration read by `diag-export --circuit`, which
// walks the same Expr under the monoidal reading.
#let leanc(..sels) = lean-call("generated/circuit/", <lean-circuit>, sels.pos())
// The COMMUTATIVE DIAGRAM route: `diag-export --commutative` draws the statement as a graph rather
// than a term walk.  Unlike `lean`/`leanc`, a `+` inside ONE selector is not a pair of boxes but two
// DIFFERENT statements drawn on one page (`diag/cd-panels.txt`'s `A+B`), so it stays one string and
// `leancd` takes exactly one selector, never `..sels`.
#let leancd(sel) = lean-call("generated/commutative/", <lean-cd>, (sel,))
// A DATA VALUE drawn as a tree, from `diag-export --value`: a tree-valued `def` read off its value,
// so an example tree in the note is the one its theorems run on.
#let leanv(sel) = lean-call("generated/value/", <lean-value>, (sel,))
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
// widens its columns — or, `fill`, ONE line, the pictures scaled by the factor that spends it all
// (`fill: true`), or by a factor the caller fixed (`fill: k`, `lean-chain`'s shared one).
#let hgut = 4pt
// The factor that spends a line's slack: `w` the pictures' widths, `lead` whether the first has no op.
// `--list` renders the panels as bare metadata, so every width is zero and there is no slack to spend.
// Capped at 1.0: a chain must never draw a panel BIGGER than `#lean` draws it standalone, so a chain
// with little content (one short row) leaves its slack outside the row instead of blowing the row up.
#let chain-k(width, lead, w) = {
  let tot = w.sum(default: 0pt)
  if tot == 0pt { 1.0 } else {
    calc.min(1.0, (width - (w.len() - if lead { 1 } else { 0 }) * (OPW + 2 * hgut)) / tot)
  }
}
#let hchain(..steps, fill: none) = layout(sz => {
  let gut = hgut
  // `u`, a second picture UNDER the first — the step's circuit under its Hinze–Marsden panel.
  // `pm`, `um`: the sizes `pic-meta` reports, kept from this one `measure` rather than taken again.
  let ss = steps.pos().map(s => {
    let (pic, u) = (box(s.at(1)), s.at(4, default: none))
    let (pm, um) = (measure(pic), if u == none { none } else { measure(box(u)) })
    (op: s.at(0), pic: pic, why: s.at(2), f: s.at(3, default: none), u: u, pm: pm, um: um,
      w: calc.max(pm.width, if um == none { 0pt } else { um.width }))
  })
  if fill != none {
    let k = if fill == true { chain-k(sz.width, ss.first().op == none, ss.map(s => s.w)) } else { fill }
    let sk(m) = if m == none { none } else { (width: m.width * k, height: m.height * k) }
    ss = ss.map(s => s + (pic: scale(k * 100%, reflow: true, s.pic), w: s.w * k, pm: sk(s.pm), um: sk(s.um),
      u: if s.u == none { none } else { scale(k * 100%, reflow: true, box(s.u)) }))
  }
  let (lines, cur, used) = ((), (), 0pt)
  for s in ss {
    let add = s.w + if lines.len() == 0 and cur.len() == 0 and s.op == none { 0pt } else { OPW + 2 * gut }
    if fill == none and cur.len() > 0 and used + add > sz.width { lines.push(cur); cur = (); used = s.w } else { used += add }
    cur.push(s)
  }
  lines.push(cur)
  stack(dir: ttb, spacing: 10pt, ..lines.enumerate().map(((li, line)) => {
    // A wrapped line's slack widens its columns: its formulas and reasons sit in them and need it.
    // A `fill` line's pictures already took the slack their factor allows; the rest stays outside.
    let extra = if fill != none { 0pt } else { calc.max(0pt, (sz.width - line.map(s => s.w).sum()
      - (line.len() - if li == 0 and line.first().op == none { 1 } else { 0 }) * (OPW + 2 * gut)) / line.len()) }
    let py =if line.any(s => s.f != none) { 1 } else { 0 }     // the picture row sits under the formulas
    let under = ss.any(s => s.u != none)
    let (cols, fr, pr, ur, rr) = ((), (), (), (), ())
    for (i, s) in line.enumerate() {
      let op = not (li == 0 and i == 0 and s.op == none)
      if op { cols.push(OPW); pr.push(s.op); ur.push([]) }
      cols.push(s.w + extra)
      pr.push({ pic-meta(plain(if s.f == none { s.why } else { s.f }), s.pic, size: s.pm); s.pic })
      ur.push(if s.u == none { [] } else { pic-meta(plain(if s.f == none { s.why } else { s.f }), s.u, size: s.um); s.u })
      let span = grid.cell.with(colspan: if op { 2 } else { 1 })
      let wide = box.with(width: s.w + extra + if op { OPW + gut } else { 0pt })
      fr.push(span(wide(if s.f == none { [] } else { s.f })))
      rr.push(span(wide(s.why)))
    }
    grid(columns: cols, column-gutter: gut, row-gutter: 4pt,
      // the reason right under its op, and the picture `u` under that, so no picture parts them
      align: (x, y) => if y == py { center + horizon } else if under and y == py + 2 { center + top } else { left + top },
      ..if py == 1 { fr } else { () }, ..pr, ..rr, ..if under { ur } else { () })
  }))
})
// The op lane is one glyph wide: `⊑`, `⊒` and `=` all measure 8.95pt here.  `layout` gives the
// CELL's width, so a row that cannot fit picture and formula side by side stacks them itself.
// PICTURE FIRST on a shared left edge (a table rebinds `pw` to its widest drawing); the formula is
// flush RIGHT in both branches, so it lands on one edge whether the row fits side by side or stacks.
#let step(op, pic, f, pw: none) = kept(k => layout(sz => {
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
  pic-flow(plain(f), row, width: sz.width, k: k)
}))
// A CHAIN `(op, selector, reason)` per step, read left to right: the Hinze–Marsden panels are ONE
// `#lean` call, so every step stands in one box at one height, on ONE line scaled to the width
// (`fill`), because a wrapped chain hides which step follows which.  `circuit: true` draws the
// circuits after as their own block, one `step` row each — op, circuit, reason — since aligning them
// under the panels forced the panels to wrap to the circuits' widths; the default `false` draws no
// circuit and sets each reason under its panel.
// A chain too long for one line is SEVERAL ROWS, each an array of steps and its own `#lean` box;
// every row takes the SMALLEST row's factor, since a short row filled on its own grows its beads
// and labels past its neighbours' and stands the tallest.
// A step is `(op, sel, reason)`, one declaration driving BOTH pictures.
// A row may instead be `Sub(decl, gloss: [..], step, ..)`: `Sub` names the declaration the row
// proves and packages it as the dict `lean-chain` reads, printed in a header row across the cell so
// a new obligation reads apart from a row that only wraps; a plain row after it continues the same
// obligation.  `gloss` is optional.  `lean-chain` accepts only a dict `Sub` built — never a
// hand-written one — so a row can't drift from what `Sub` prints.
// A step whose `sel` is `(decl,)` draws that WHOLE STATEMENT as its own `lean(decl)` call — both
// sides one height, and between them the relation the exporter reads off the statement's head, so
// no hand-written symbol can call an equation an inclusion — beside the row's single-side steps,
// which share one call.
#let stmt-sel(p) = {
  assert(p.len() == 1, message: "a lean-chain statement step is `(decl,)`, not " + repr(p)
    + ": the exporter draws both sides and the relation between them from the one declaration")
  p
}
// A step whose Lean side at `sel` is branches joined by `sym` — a union `P ∪ Q`, or a sum
// `∇°(P+Q)∇` whose codiagonals the sign stands for — reads as `sel.inr` then `sel.inl` (`rev:`
// swaps them).  A lean-chain row `(op, union(sel), reason)` expands (in `lean-chain`, below) to the
// panel at the first selector under `op` then the second under `sym`, with no reason; `.sels`
// spread is what a raw `lean(..union(sel).sels, op: [∪])` call draws side by side.  A dictionary,
// so it never collides with `stmt-sel`'s `(decl,)` array.
// `split:` names ONE of the two top branches ("inl"/"inr", the book's writing order) that is ITSELF
// a further `∪`/`+`, and flattens it in place: `union(sel, split: "inr")` on the default (non-rev)
// order reads `sel.inr.inr, sel.inr.inl, sel.inl` — three selectors, one `sym` between each pair —
// the same mechanism `<entab-expand-V>` uses for the `nottab` arm's nested `∪`.  `rev:` still
// reverses the WHOLE flattened list, so the split branch's two children stay adjacent to each other
// under any order.  `sel` (the un-suffixed parent) survives in the dict so `lean-chain` can generate
// the group's own formula from it — the whole side the branches split, not one formula per branch.
#let branches(sym, sel, rev: false, split: none) = {
  let s = (sel + ".inr", sel + ".inl")
  let s = if split == none { s } else {
    let nest = sel + "." + split
    s.map(x => if x == nest { (nest + ".inr", nest + ".inl") } else { x }).flatten()
  }
  (sym: sym, sel: sel, sels: if rev { s.rev() } else { s })
}
#let union = branches.with([∪])
#let sum = branches.with([+])
// A reason stands under its panel only when it fits the panel's width; a longer one would run into
// the next step's, so the panel gets a letter instead, numbered per row, and the lettered reasons
// are listed under the row, where the circuits stood.  A row with a BRANCHES step (∪/+) letters
// EVERY step and lists a 3-column table instead — letter, formula, hint — because the group's
// formula only reads against its own hint, not against a panel too narrow to hold it.
#let chain-tags = "abcdefghijklmnopqrstuvwxyz".clusters()
// Shrinks CONTENT to whatever width its container gives it, never growing past 1.0 — the ratio
// `chain-k` uses for a whole row, read here from `layout` since a table cell's width is only known
// once the surrounding grid resolves its `1fr` columns.
#let fit-w(f) = layout(sz => {
  let need = measure(f).width
  let ratio = if need > sz.width and need > 0pt { sz.width / need } else { 1.0 }
  align(center, scale(ratio * 100%, reflow: true, f))
})
#let Sub(decl, gloss: none, ..steps) = (sub: decl, gloss: gloss, steps: steps.pos(), kind: "Sub")
// `formula: true` sets each panel's own statement side above it, generated from the panel's
// selector like a header, so the chain reads as a term chain as well as a picture chain.
#let lean-chain(..args, circuit: false, formula: false) = {
  let a = args.pos()
  let rows = (if type(a.first()) == dictionary or type(a.first().at(0)) == array { a } else { (a,) })
    .map(r => if type(r) == dictionary {
      assert(r.at("kind", default: none) == "Sub", message: "a lean-chain row dict must come from Sub(...)")
      r
    } else { (steps: r) })
    // expand a `branches` step into its two rows before anything else sees it, so the rest of
    // this function only ever meets plain string selectors or a `stmt-sel` singleton; `groups`
    // remembers which flat rows came from ONE row entry — a `branches` pair, or a row of its own —
    // so the merge below decides once per STEP, never once per branch.
    // A branches step's OWN FORMULA — the whole side the branches split, e.g. `S₁°G(X)R₁∪S₂°H(X)R₂`
    // — is generated ONCE from the un-suffixed parent selector and carried on EVERY flat step of the
    // group as `(gform: ..)`, head and members alike: the below-row table (further down) tables one
    // line per step, and every line of the group names the SAME group formula in its formula column,
    // so it must read off whichever member that line is, not only the first.
    .map(r => {
      let steps = ()
      let groups = ()
      for s in r.steps {
        if type(s.at(1)) == dictionary {
          let b = s.at(1)
          let i0 = steps.len()
          let n = b.sels.len()
          let g = (gform: leanf(b.sel),)
          steps.push((s.at(0), b.sels.at(0), s.at(2), g))
          for k in range(1, n) { steps.push((b.sym, b.sels.at(k), src[], g)) }
          groups.push(range(i0, i0 + n))
        } else {
          groups.push((steps.len(),))
          steps.push(s)
        }
      }
      r + (steps: steps, groups: groups)
    })
  // ONE PICTURE ONCE: a STEP whose panel the exporter found drawn the same as the NEXT step's,
  // branch for branch (`dup`, the exporter's `stepGroups`/`Diagram.drawnAs`), only re-spells the
  // term, so the whole step is merged into the next one — its op and the next step's own
  // picture(s), both reasons — and neither its panel nor its circuit is drawn.  A pair merges only
  // with a pair whose two branches BOTH match; it never merges with a single panel, and never with
  // its own sibling branch, because the exporter's `dup` answers for the STEP, not the branch, and
  // is the same for every row of one step — so this loop reads it once, at the step's first row.
  let calls = rows.map(r => {
    let singles = r.steps.map(s => s.at(1)).filter(x => type(x) != array)
    let (m, sp) = if singles.len() > 0 { lean-pics("generated/", <lean-panel>, singles) } else { ([], ()) }
    let m = m + lean-step(singles)
    let i = 0
    let got = ()
    for s in r.steps {
      if type(s.at(1)) == array { got.push((pic: lean-call("generated/", <lean-panel>, stmt-sel(s.at(1))), dup: false)) }
      else { got.push(sp.at(i)); i += 1 }
    }
    let (steps, pics, held) = ((), (), none)
    for grp in r.groups {
      let i0 = grp.first()
      let s = r.steps.at(i0)
      let s = if held == none { s } else if s.len() > 3 {
        (held.at(0), s.at(1), [#held.at(2) \ #s.at(2)], s.at(3))
      } else { (held.at(0), s.at(1), [#held.at(2) \ #s.at(2)]) }
      held = if got.at(i0).dup { s } else { none }
      if not got.at(i0).dup {
        steps.push(s); pics.push(got.at(i0).pic)
        for idx in grp.slice(1) { steps.push(r.steps.at(idx)); pics.push(got.at(idx).pic) }
      }
    }
    assert(held == none, message: "the last step of a lean-chain row is marked `dup`: it has no next step to merge into")
    (m, pics, steps)
  })
  // A BREAKABLE CELL, against `calc-table`'s unbreakable default: a chain is many pictures, each
  // step `kept` whole, so it breaks between steps; unbreakable, a chain taller than the rest of the
  // page overran its foot (16.3i).
  table.cell(breakable: true, { for c in calls { c.at(0) }; layout(sz => {
    let ws = calls.map(c => c.at(1).map(p => measure(box(p)).width))
    let k = calc.min(..calls.zip(ws).map(((c, w)) => chain-k(sz.width, c.at(2).first().at(0) == none, w)))
    for ((row, c), w) in rows.zip(calls).zip(ws) {
      let r = c.at(2)
      // the `Thm` header's look one step down: lighter fill, no bold, a thinner rule; `pad` spends
      // the table's 9pt inset so it spans the cell like a row of the table
      if "sub" in row {
        pad(x: -9pt, block(width: 100%, fill: luma(246), inset: (x: 9pt, y: 4pt), below: 6pt,
          stroke: (top: 0.4pt + luma(190), bottom: 0.7pt + luma(150)),
          align(center, { leanf(row.sub); if row.gloss != none { [ \ ]; row.gloss } })))
      }
      // `circuit: false`: each reason under its panel if it fits the panel's width, else a letter
      // there and the reason in the list under the row; `circuit: true`: the panels bare, and under
      // them one circuit row per step carrying its reason.  A row with a BRANCHES step (∪/+) letters
      // every step regardless of width and replaces the list with a 3-column table (letter, formula,
      // hint) — see the comment above `chain-tags`.
      let pw = w.map(x => x * k)
      let hasg = not circuit and r.any(s => type(s.at(3, default: none)) == dictionary)
      let (tags, n) = ((), 0)
      for (s, x) in r.zip(pw) {
        if hasg or (not circuit and measure(s.at(2)).width > x) { tags.push(chain-tags.at(n)); n += 1 }
        else { tags.push(none) }
      }
      hchain(fill: k, ..r.zip(c.at(1), w, pw, tags).map(((s, p, cw, x, t)) => {
        let g = s.at(3, default: none)
        let isg = type(g) == dictionary
        (s.at(0), box(width: cw, align(center, p)), if circuit { [] } else {
          align(right, box(width: x, align(center, if t == none { s.at(2) } else { [(#t)] }))) },
        if isg { none }
          else if formula { leanf(if type(s.at(1)) == array { s.at(1).first() } else { s.at(1) }) }
          else { none },
        none)
      }))
      if hasg {
        block(above: 6pt, below: 0pt, calc-table(cols: (auto, 1fr, 1fr),
          al: (center + horizon, center + horizon, left + horizon),
          ..r.zip(tags).map(((s, t)) => {
            let g = s.at(3, default: none)
            let f = if type(g) == dictionary { g.gform }
              else { leanf(if type(s.at(1)) == array { s.at(1).first() } else { s.at(1) }) }
            ([(#t)], fit-w(f), s.at(2))
          }).flatten()))
      } else if n > 0 {
        block(above: 6pt, below: 0pt, grid(columns: (auto, 1fr), column-gutter: 6pt, row-gutter: 5pt,
          ..r.zip(tags).filter(((s, t)) => t != none).map(((s, t)) => ([(#t)], s.at(2))).flatten()))
      }
      // One block per circuit IN FLOW, never a `stack`: a stack is one unbreakable piece, so a chain
      // whose circuits outgrow the page ran its last one over the page foot and number (16.3i).
      if circuit { for s in r {
        assert(type(s.at(1)) != array, message: "lean-chain(circuit: true): the step " + repr(s.at(1))
          + " draws a whole statement, and the circuit route reads one side only")
        block(above: 6pt, below: 0pt, step(if s.at(0) == none { [] } else { s.at(0) }, leanc(s.at(1)), s.at(2)))
      } }
      // the last circuit is the cell's last ink, and the table's 3pt inset alone set it on the border
      v(6pt)
    }
  }) })
}
#let sort-P-box = ([`sort(P)`], 2.23, true)
#let thinlist-Q-box = ([`thinlist(Q)`], 3.0, true)
#let est-Rc-box = ([`est(R°)`], 2.2, true)
#let listcp-F-box = ([`listcp`], 1.87, false)
#let pair-g-box = ([`⟨g₁,g₂⟩`], 2.2, false)
#let minlist-R-box = ([`minlist(R)`], 2.93, true)
// note-split: prelude footer — written by scripts/note-split and stripped by scripts/note-join
#let note-chapter = note-chapter.with(names: refname)
