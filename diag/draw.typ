// draw.typ — B&dM §2.6 (p. 46) catamorphism laws, §2.7 (p. 50) type functor, IntroString §3.1
// (p. 64) monads, drawn; and every helper diag/allegory-axioms.typ draws with.  Standalone PNG:
//   typst compile --root . --format png --ppi 220 diag/draw.typ diag/draw.png
// (2.10) `relCata_UP`, (2.11) `relCata_alpha`, Ex 2.35 `relCata_of_comp` (AOP/A5_5, A6_3.lean); laws in
// DIAGRAM order, `xy` first `x` then `y`, mirroring B&dM's applicative `h·f` by `h·f ↦ f h`.
// `𝟏` IS ALWAYS GREY (Remark 2.1, p. 36): no other region in this repository may be grey.

// A newline ENDS an import list in Typst — keep this on one line however long it gets, or the names
// after the break are parsed as an expression and `hm-row` becomes the subtraction `hm - row`.
#import "hm.typ": KNEE, cetz, d, hm-apex, hm-bead, hm-join, hm-name, hm-panel, hm-path, hm-port, hm-region, hm-row, hm-sepx, hm-turn, hm-turn-split, hm-wire, lw
// Same one-line rule.  NOT `cap`/`cup` from circuit and NOT `*` from note-style: this file already
// binds `cap`, and note-style re-exports a `cetz`/`d` that would shadow hm.typ's.
#import "circuit.typ": wire, bend, gbox, dot as wiredot, tape, TAPEEDGE
#import "note-style.typ": P, src, plain

#set page(width: auto, height: auto, margin: 0.8cm, fill: white)
#set text(font: "New Computer Modern", size: 11pt)

// -------------------------------------------- one geometry for all four laws: THREE ROWS, ONE PITCH
// A panel leaves a row EMPTY rather than compressing: a shared bead at two heights reads as a reshuffle.
#let H = 3.6            // panel height — every wire runs it end to end, top edge to bottom edge
#let SEP = 1.0          // the two wires of `F T`
#let PADX = 0.5         // the box's left edge to the `F` wire
// Wider on the right, because that strip is `𝟏` and a bead sits on its left boundary with its name
// 0.32 to the right of the dot, inside the grey — which is where the book puts an arrow's name.
#let PADR = 1.2
#let W = PADX + SEP + PADR
#let XF = PADX              // the `F` wire
#let XO = PADX + SEP        // the object wire
#let XM = PADX + SEP / 2    // `splitcut`'s merged wire, and where a region's name sits — see both
// PITCH 0.9, the one every family here now uses, and MARGIN 0.9 — the `F` strand bends `KNEE` above
// its row, and at margin 0.8 the 0.2 left over reads as a wire entering the panel already turning.
#let PITCH = 0.9            // one row to the next, and the margin above row 1 and below the last row
#let H1 = H - PITCH         // row 1
#let H2 = H - 2 * PITCH     // row 2 — also the row a LONE bead sits on, being the average of the other two
#let H3 = H - 3 * PITCH     // row 3
#let GAP = 1.0              // between two panels, with the `=` centred in it

// The object wire, bound once: the vertex at `H2` is where a `homeq` wire changes type, and a 2-point
// list would have nowhere to split the colour.  It is also the boundary `regionfills` walks.
#let OWIRE = ((XO, H), (XO, H2), (XO, 0))

// Where a SPLIT output's second strand runs — see `algpanel`'s `outsplit`.  Well inside `PADR`, so the
// new port's name still sits over the panel and the `𝟏` strip keeps a name's width to its right.
#let OUTDX = 0.55

// ONE PANEL WIDTH FOR THE WHOLE FILE, one-wire pictures included: they put their object wire at the same
// `XO`, so the `𝒜` and `𝟏` strips are the same width everywhere and a colour read off one is found in the next.

// ------------------------------------- a wire's colour is its type (`typed: true`): ONE HUE PER OBJECT
// Off the note's ARROW palette, since a bead's colour says which arrow; `C` gold not olive, too near `α_C`'s green.
// FOUR HUES, named by hue and no longer by a letter: which object wears which is `OCOL` below.  They
// are spread by HUE ANGLE — 35°, 70°, 142°, 234° — because two objects on one wire read as the same
// object when their angles are close, whatever ΔE says: red against amber is 35° apart and was the
// pair the note kept getting wrong, so no display now puts those two on one wire.
#let TCOL = rgb("#b91c1c")      // red
#let BCOL = rgb("#0e7490")      // teal
#let CCOL = rgb("#a16207")      // amber
#let GCOL = rgb("#00932d")      // green, the fourth: §16.4b runs four types down one wire

// ONE OBJECT, ONE HUE, NOTE-WIDE.  Bands assigned by POSITION made `C` amber in one panel of §11.4.2a
// and teal in the next, which is the one thing the colour is there to prevent.  Two objects share a
// hue only where no display puts them on one wire: this map is a colouring of that co-occurrence
// graph, and the ORDER within §16.4b's four is chosen so red and amber are never neighbours.  A new
// object name belongs here — `obands` reads it with no default, so an unlisted one is a compile
// error, not a wrong hue.
#let OCOL = (
  "A": GCOL, "B": BCOL, "C": GCOL, "T": TCOL, "[A]": TCOL, "TA": TCOL, "TB": TCOL,
  "Int": TCOL, "Nat": TCOL, "LA": TCOL, "Job": TCOL, "Item": TCOL, "Word": TCOL, "City": TCOL,
  "Char": TCOL, "Code": BCOL, "Op": GCOL,
  "[0,2¹⁶)": CCOL, "Interval": BCOL, "Real": TCOL, "Decimal": GCOL)

// A NAME'S OWN NUMBER — FNV over its bytes, with the round's `+` where FNV-1a has an exclusive or,
// which `calc` does not carry.  Every derived hue below is indexed by it, so a name always draws in
// the same colour and the choice is reproducible without a table.
#let namehash(s) = {
  let h = 2166136261
  for b in array(bytes(s)) { h = calc.rem((h + b) * 16777619, 4294967296) }
  h
}
// An object the map does not list still needs ONE hue, note-wide, and these four bands are all there
// are: take the band from the name, so a new object is drawn before anyone declares it and always in
// the same band.  DELIBERATE sharing stays in `OCOL` above — a derived band is only a starting point,
// and two objects that must be told apart in one panel are what an entry there is for.
#let OBANDS = (TCOL, BCOL, CCOL, GCOL)
#let objcol(l) = OCOL.at(plain(l), default: OBANDS.at(calc.rem(namehash(plain(l)), OBANDS.len())))

// `auto` on a hand-drawn panel's object colour means THE OBJECT'S OWN HUE, so a hand-laid figure and
// a generated one give one object one colour.  A composite port names no single object — `A×B`, `EA`,
// `TA` are the three the note writes — and keeps the panel's positional default.
#let ocol(c, l, d) = if c != auto { c } else if l == none { d } else { OCOL.at(plain(l), default: d) }

// The FUNCTORS of `i ⊣ E`, keyed by name and OFF the palette above: the `Λ` panels set these wires
// beside typed object wires.  `i` is black, this file's colour for a functor wire; `E` marks the pair.
#let ADJC = (i: black, E: rgb("#ea580c"))
// Functor wires are coloured BY NAME; a bead sits ON the wire it changes, so the FIXED obstacles are the
// bead hues `GIVEN1`/`GIVEN2`/`INDUCED`/`SLACK` and the object hues `BCOL`/`TCOL`/`CCOL`.  ΔE76 ≥ 25 from
// every one, ≥ 29 between two lanes sharing a panel, ≥ 12 between any two; muted, so the beads stay loudest.
// THE ENTRIES BELOW ARE DATA, NOT THE RULE: `fcol` derives a hue for a name they do not list, and
// `lanecheck` measures every panel's lanes against its beads, so nothing here rests on a hand count.
#let FCOL = (
  "E": rgb("#00a5a2"), "list": rgb("#8193c9"), "tree": rgb("#725730"), "F": rgb("#695c53"), "F(A,−)": rgb("#93ae75"), "A": rgb("#214875"),
  "L": rgb("#7e668d"), "N": rgb("#576000"), "Δ": rgb("#ba6d9f"), "list⁺": rgb("#969b49"),
  "bag": rgb("#a29366"), "Fᵢ": rgb("#8d7e75"), "A×−": rgb("#b1605a"), "Int×−": rgb("#c78675"),
  "Op×−": rgb("#844a3b"), "−×Code": rgb("#c4858b"), "−×Job": rgb("#85474f"),
  "−×Char": rgb("#966e59"), "𝟏": rgb("#a3a3a3"),
  // IntroString p.48's three monads, for the panels that redraw Cheng's commuting diagram.
  "B": rgb("#7a5c3e"), "C": rgb("#3f7d6e"),
  // `M`, the monad of IntroString p.74, so those figures render against the book without a rename;
  // amber is ΔE76 66 from the nearest bead colour and 31 from the nearest lane.
  "M": rgb("#b58900"),
  // `P A = E A` is the same object, so `P` takes `E`'s hue a shade darker: the two relators must
  // read as siblings, because the whole content of `P(est(R))est(R)⊑union est(R)` is that they differ.
  "P": rgb("#00767e"),
  // §11.5.1's type functor and the fork that feeds the bifunctor its two arguments, `⟨𝟙,T⟩ : 𝒜⟶𝒜×𝒜`.
  // They share a panel with `F`, hence ΔE76 37 and 41 from it and from each other.
  "T": rgb("#883462"), "⟨𝟙,T⟩": rgb("#a884ca"),
  // §13.2's SOURCE relator: a LaT `φ : G⇒F` puts the two in one panel, hence ΔE76 59 from `F`.
  "G": rgb("#babd56"))

// ------------------------------------------------ the regions, Remark 2.1 (p. 36); grey is `𝟏` alone
// The book's own yellow (diagram (3.6), p. 77) kept far paler: a ground under running text, not a plate.
#let AC = rgb("#fbf3d5")        // the ambient category
#let UC = rgb("#e4e4e4")        // `𝟏`
#let NAMEC = luma(150)          // a region's name

// `algpanel` — ONE PANEL of `homeq`.  The object wire SURVIVES the junction, so it runs straight and the
// consumed `F` strand bends; `owire` is passed by name so panel and region walk the one list, reversed.
// `w`/`h`/`xo` default to the two-strand panel's; a caller with a strand or a row more passes its own.
#let regionfills(owire, regions, ucol, w: W, h: H, xo: XO) = if regions != none {
  // Right edge, bottom edge, then UP the object wire; `close` walks the top edge back.
  hm-region(((w, h), (w, 0)) + owire.rev(), ucol)
  if regions != auto {
    // The ambient name at `XM`, one position for both panel kinds: between the wires where an `F`
    // wire runs, and still mid-strip where none does.
    hm-name((XM, h - 0.3), regions.at(0), col: NAMEC)
    hm-name((xo + PADR / 2, h - 0.3), regions.at(1), col: NAMEC)
  }
}

// `fmid` — a bead on the `F` wire, for §2.7's BIFUNCTOR `F_A = F(A, −)` (CatString.pdf, §Bifunctors).
// ALWAYS ON ROW 2: two beads at one height are one composite, and only the `ymerge = H3` panel has room.
// `outsplit` — the pair of names for an output that LEAVES `mid` AS TWO STRANDS instead of one, `out`'s
// wire keeping `XO` and the second branching right to `OUTDX`; it replaces `out`'s single port.
#let algpanel(
  owire, ymerge, w1, w2, out, act, cact, mid, cmid, cT, cB, regions, acol, ucol, frame,
  fmid: none, cfmid: black, outsplit: none,
) = {
  // `hm-join`'s knee, mirrored: the branch leaves the bead vertically and straightens into its column.
  let branch = ((XO, H2), (XO + OUTDX, H2 - KNEE), (XO + OUTDX, 0))
  hm-panel(W, H, fill: if regions != none { acol } else { none }, frame: frame, {
    // `𝟏` is bounded on the left by the RIGHTMOST wire, which after a split is the branch.
    regionfills(if outsplit == none { owire } else { owire.slice(0, 2) + branch.slice(1) },
      regions, ucol)
    hm-join(XF, H, XO, ymerge)
    if fmid != none { hm-bead((XF, H2), fmid, col: cfmid) }
    hm-wire(owire.slice(0, 2), col: cT)
    hm-wire(owire.slice(1), col: cB)
    if outsplit != none { hm-wire(branch, col: cB) }
    hm-bead((XO, ymerge), act, col: cact)
    // `mid: none` is the IDENTITY: a bare wire, not a labelled bead.
    if mid != none { hm-bead((XO, H2), mid, col: cmid) }
    hm-port((XF, H), w1)
    hm-port((XO, H), w2, col: cT)
    if outsplit == none {
      hm-port((XO, 0), out, dir: -1, col: cB)
    } else {
      hm-port((XO, 0), outsplit.at(0), dir: -1, col: cB)
      hm-port((XO + OUTDX, 0), outsplit.at(1), dir: -1, col: cB)
    }
  })
}

// `onepanel` — ONE PANEL of `beadeq`/`twobeadeq`, no `F` wire.  Width, `XO`, rows and fills are
// `algpanel`'s through the same `regionfills`, so the two panel kinds cannot disagree about the strip.
#let onepanel(segs, beads, w, out, cw, cout, regions, acol, ucol, frame) = hm-panel(
  W, H, fill: if regions != none { acol } else { none }, frame: frame, {
    regionfills(OWIRE, regions, ucol)
    for (y0, y1, c) in segs { hm-wire(((XO, y0), (XO, y1)), col: c) }
    for (y, l, c) in beads { hm-bead((XO, y), l, col: c) }
    hm-port((XO, H), w, col: cw)
    hm-port((XO, 0), out, dir: -1, col: cout)
  },
)

// `homeq` — "`mid` is a homomorphism of F-algebras": `top mid = F(mid) bot`.  `mid` sits at ONE height
// and the object wire is one `OWIRE` on both sides; only the ALGEBRA bead moves, which is the law.
// `gap` widens the space the `=` sits in: `mid`'s name runs right from the left panel's row 2, which is
// the row the `=` is on, so a long `mid` needs the sign pushed clear of it.
// `sep`/`rev` state a LAX law instead — the sign, and which side of it `F(mid) bot` falls on; `length`
// scales the geometry alone, so a caller whose port names crowd sets it rather than shrinking them.
#let homeq(w1, w2, top, mid, bot, out, ctop: black, cmid: black, cbot: black,
           fmid: none, cfmid: black, outsplit: none,
           typed: false, tcol: auto, bcol: auto, gap: GAP, sep: [=], rev: false, length: 0.95cm,
           regions: none, acol: AC, ucol: UC, frame: none) = {
  let (cT, cB) = if typed { (ocol(tcol, w2, TCOL), ocol(bcol, out, BCOL)) } else { (black, black) }
  let panels = (
      // The `F` strand lands on row 1, above `mid`: `w2`-typed through the junction down to `mid`,
      // `out`-typed from `mid` down.
      algpanel(OWIRE, H1, w1, w2, out, top, ctop, mid, cmid, cT, cB, regions, acol, ucol, frame,
        outsplit: outsplit),
      // The `F` strand runs straight past `mid` and lands on row 3: that two-row fall is the only
      // difference between the panels, which is the law.
      algpanel(OWIRE, H3, w1, w2, out, bot, cbot, mid, cmid, cT, cB, regions, acol, ucol, frame,
        fmid: fmid, cfmid: cfmid, outsplit: outsplit),
  )
  hm-row(if rev { panels.rev() } else { panels }, sep: sep, gap: gap, length: length)
}

// `beadeq` — `b = 𝟙` on the wire `w`: a bead on the left, a BARE WIRE on the right, which is what the
// identity is here.  One colour throughout, `b` being an endo-arrow — that is the law, not a gap.
#let beadeq(w, b, out, cb: black, typed: false, wcol: auto,
            regions: none, acol: AC, ucol: UC, frame: none) = {
  let c = if typed { ocol(wcol, w, TCOL) } else { black }
  hm-row(
    (
      onepanel(((H, 0, c),), ((H2, b, cb),), w, out, c, c, regions, acol, ucol, frame),
      onepanel(((H, 0, c),), (), w, out, c, c, regions, acol, ucol, frame),
    ),
    gap: GAP,
  )
}

// `twobeadeq` — `b1 b2 = b3`: `b1` and `b2` take rows 1 and 3 and `b3` their average, row 2, so the
// collapse reads as two heights meeting.  `vcol` is the intermediate type, which the convention leaves unnamed.
#let twobeadeq(w, b1, b2, b3, out, c1: black, c2: black, c3: black,
               typed: false, tcol: auto, vcol: BCOL, bcol: auto,
               regions: none, acol: AC, ucol: UC, frame: none) = {
  let (cT, cV, cB) = if typed { (ocol(tcol, w, TCOL), vcol, ocol(bcol, out, CCOL)) }
    else { (black, black, black) }
  hm-row(
    (
      onepanel(
        ((H, H1, cT), (H1, H3, cV), (H3, 0, cB)), ((H1, b1, c1), (H3, b2, c2)),
        w, out, cT, cB, regions, acol, ucol, frame,
      ),
      onepanel(
        ((H, H2, cT), (H2, 0, cB)), ((H2, b3, c3),),
        w, out, cT, cB, regions, acol, ucol, frame,
      ),
    ),
    gap: GAP,
  )
}

// A BRACKET, marking a run of beads from OUTSIDE the picture: `dir` is +1 left of it, -1 right, label
// on the far side where it cannot land on a wire.  Not a real brace, which costs a bezier per bracket.
#let TK = 0.18          // the tick at each end
#let BM = 0.32          // how far the rule reaches beyond the beads it spans
#let brack(x, y0, y1, w, col, dir) = {
  let st = (thickness: 0.7pt, paint: col)
  let (a, b) = (y0 + BM, y1 - BM)
  d.line((x, a), (x, b), stroke: st)
  d.line((x, a), (x + dir * TK, a), stroke: st)
  d.line((x, b), (x + dir * TK, b), stroke: st)
  d.content((x - dir * 0.14, (y0 + y1) / 2), text(9pt, col)[#w],
    anchor: if dir > 0 { "east" } else { "west" })
}

// The two bracket columns, outside the wires.  `XBR` clears a one-glyph bead name, which `hm-bead`
// sets 0.32 to the right of its dot; a longer name would want a wider gap, and none here is longer.
#let XBL = XF - 0.75
#let XBR = XO + 1.15

// `splitcut` — ONE picture cut two ways (Ex 2.35): a string diagram has no notation for a bracket, so
// the two sides are the two BRACKET columns.  No regions — `XBR` is inside the panel — and no type hues.
#let splitcut(
  w1, w2, b1, mid, b2, out,
  ltop: [], lbot: [], rtop: [], rbot: [],
  c1: black, cmid: black, c2: black, cl: luma(110), cr: luma(110),
) = hm-row(
  (
    hm-panel(W, H, {
      hm-wire(((XF, H), (XF, H2 + KNEE), (XM, H2)))
      hm-wire(((XO, H), (XO, H2 + KNEE), (XM, H2), (XM, 0)))
      hm-bead((XO, H1), b1, col: c1)
      hm-bead((XM, H2), mid, col: cmid)
      hm-bead((XM, H3), b2, col: c2)
      hm-port((XF, H), w1); hm-port((XO, H), w2); hm-port((XM, 0), out, dir: -1)

      brack(XBL, H1, H2, ltop, cl, 1); brack(XBL, H3, H3, lbot, cl, 1)
      brack(XBR, H1, H1, rtop, cr, -1); brack(XBR, H2, H3, rbot, cr, -1)
    }),
  ),
  sep: none,
)

// ============================ THE MONAD PICTURES — IntroString §3.1 (p. 64) and Example 3.6 (p. 67)
// THE IDENTITY FUNCTOR IS A REGION, NOT A WIRE (p. 64); horizontal order is APPLICATIVE, leftmost = outermost.
// The MARGINS here are not slack: a turn's apex plus its name reaches almost to either edge, so only
// the pitch shrank, to the 0.9 the other two families use.
#let HMON = 3.35           // panel height — a wire that is not consumed runs it end to end
#let YU = 2.15          // the row a UNIT acts on
#let YM = 1.25          // the row a MULTIPLICATION acts on
#let GAPN = 0.32        // a bead's name, off its dot; hm-bead's default, respelled so the vertical placements match
// The four columns of `State∘State`, `R L R L`.  Every picture in the file draws its wires on a
// prefix of them, so a wire in one picture stands where the same wire stands in the next.
#let X = (0, 1, 2, 3).map(i => PADX + i * SEP)
// Where a fork's two arms meet: the MIDPOINT, since neither arm survives a multiplication.  A function
// and not one constant, because `monadassoc` nests forks and an inner junction is off the column grid.
#let midx(a, b) = (a + b) / 2
#let W1 = 2 * PADX                // a one-wire panel
#let W2 = 2 * PADX + SEP          // a two-wire panel
#let W3 = 2 * PADX + 2 * SEP      // a three-wire panel — `M∘M∘M`, the associativity law's source
#let W4 = 2 * PADX + 3 * SEP      // a four-wire panel

// ------------------------------------------------------- `mufork` — the tuning fork, drawn once
// THREE paths, stem included: hm.typ draws only a junction's SURVIVOR straight, and neither arm survives.
#let mufork(xl, yl, xr, yr, y, ybot, col: black) = {
  let xj = midx(xl, xr)
  // An arm that BEGINS at the knee height — a nested fork's stem — has no straight run left, and
  // asking for one would be a segment from a point to itself.
  let arm(x, ytop) = hm-wire(
    if ytop > y + KNEE { ((x, ytop), (x, y + KNEE), (xj, y)) } else { ((x, ytop), (xj, y)) },
  )
  arm(xl, yl); arm(xr, yr)
  hm-wire(((xj, y), (xj, ybot)))
  hm-bead((xj, y), `μ`, col: col, dx: -GAPN, anchor: "east")
}

// `monadops` — what a monad IS, in two pictures joined by the book's own "and" (p. 64).  The lollipop
// `η : Id ⇒ M` has nothing above it, so the `M` wire simply begins at its bead.
#let monadops(ceta: black, cmu: black) = hm-row(
  (
    hm-panel(W1, HMON, fill: AC, {
      hm-wire(((PADX, YU), (PADX, 0)))
      hm-bead((PADX, YU), `η`, col: ceta, dx: 0, dy: GAPN, anchor: "south")
      hm-port((PADX, 0), `M`, dir: -1)
    }),
    hm-panel(W2, HMON, fill: AC, {
      mufork(X.at(0), HMON, X.at(1), HMON, YM, 0, col: cmu)
      hm-port((X.at(0), HMON), `M`); hm-port((X.at(1), HMON), `M`); hm-port((XM, 0), `M`, dir: -1)
    }),
  ),
  sep: [and], gap: 1.6, sepsize: 11pt,
)

// `monadunit` — the unit law (p. 64).  Horizontal order is applicative, so `η∘M`'s lollipop caps the
// LEFT arm and `M∘η`'s the right; the middle panel is a bare wire, which is what `𝟙` is here.
#let monadunit(ceta: black, cmu: black) = hm-row(
  (
    hm-panel(W2, HMON, fill: AC, {
      mufork(X.at(0), YU, X.at(1), HMON, YM, 0, col: cmu)
      hm-bead((X.at(0), YU), `η`, col: ceta, dx: 0, dy: GAPN, anchor: "south")
      hm-port((X.at(1), HMON), `M`); hm-port((XM, 0), `M`, dir: -1)
    }),
    hm-panel(W1, HMON, fill: AC, {
      hm-wire(((PADX, HMON), (PADX, 0)))
      hm-port((PADX, HMON), `M`); hm-port((PADX, 0), `M`, dir: -1)
    }),
    hm-panel(W2, HMON, fill: AC, {
      mufork(X.at(0), HMON, X.at(1), YU, YM, 0, col: cmu)
      hm-bead((X.at(1), YU), `η`, col: ceta, dx: 0, dy: GAPN, anchor: "south")
      hm-port((X.at(0), HMON), `M`); hm-port((XM, 0), `M`, dir: -1)
    }),
  ),
  gap: 1.2,
)

// `monadassoc` — the two nestings of the fork.  The upper fork's STEM is the lower's ARM, hence
// `mufork`'s per-arm start height.  The panels' outputs do not line up: a junction is a midpoint.
#let monadassoc(cmu: black) = hm-row(
  (
    hm-panel(W3, HMON, fill: AC, {
      mufork(X.at(0), HMON, X.at(1), HMON, YU, YM + KNEE, col: cmu)
      mufork(XM, YM + KNEE, X.at(2), HMON, YM, 0, col: cmu)
      for i in (0, 1, 2) { hm-port((X.at(i), HMON), `M`) }
      hm-port((midx(XM, X.at(2)), 0), `M`, dir: -1)
    }),
    hm-panel(W3, HMON, fill: AC, {
      mufork(X.at(1), HMON, X.at(2), HMON, YU, YM + KNEE, col: cmu)
      mufork(X.at(0), HMON, midx(X.at(1), X.at(2)), YM + KNEE, YM, 0, col: cmu)
      for i in (0, 1, 2) { hm-port((X.at(i), HMON), `M`) }
      hm-port((midx(X.at(0), midx(X.at(1), X.at(2))), 0), `M`, dir: -1)
    }),
  ),
  gap: 1.2,
)

// `stateops` — the same two for `State = R∘L`, and the point is that neither is a new arrow: both are
// the curry adjunction's, drawn as turns — `η` opening the pair, `ε` closing the middle `L∘R`.
#let stateops(ceta: black, ceps: black) = hm-row(
  (
    hm-panel(W2, HMON, fill: AC, {
      hm-turn(X.at(0), X.at(1), YU)
      hm-wire(((X.at(0), YU), (X.at(0), 0)))
      hm-wire(((X.at(1), YU), (X.at(1), 0)))
      hm-bead(hm-apex(X.at(0), X.at(1), YU), `η`, col: ceta, dx: 0, dy: GAPN, anchor: "south")
      hm-port((X.at(0), 0), `R`, dir: -1); hm-port((X.at(1), 0), `L`, dir: -1)
    }),
    hm-panel(W4, HMON, fill: AC, {
      hm-wire(((X.at(0), HMON), (X.at(0), 0)))
      hm-wire(((X.at(1), HMON), (X.at(1), YM)))
      hm-wire(((X.at(2), HMON), (X.at(2), YM)))
      hm-wire(((X.at(3), HMON), (X.at(3), 0)))
      hm-turn(X.at(1), X.at(2), YM, dir: -1)
      hm-bead(hm-apex(X.at(1), X.at(2), YM, dir: -1), `ε`, col: ceps,
        dx: 0, dy: -GAPN, anchor: "north")
      for (i, w) in (`R`, `L`, `R`, `L`).enumerate() { hm-port((X.at(i), HMON), w) }
      hm-port((X.at(0), 0), `R`, dir: -1); hm-port((X.at(3), 0), `L`, dir: -1)
    }),
  ),
  sep: [and], gap: 1.6, sepsize: 11pt,
)

// `unitlaw` — `(η∘State) μ = 𝟙` in diagram order: the new `R`, both turns and the old `R` are ONE strand,
// the zig-zag.  The panels' ports cannot line up, nor do the book's snakes (4.3a)–(4.3b), p. 93.
#let unitlaw(ceta: black, ceps: black) = hm-row(
  (
    hm-panel(W4, HMON, fill: AC, {
      hm-turn(X.at(0), X.at(1), YU)
      hm-turn(X.at(1), X.at(2), YM, dir: -1)
      hm-wire(((X.at(0), YU), (X.at(0), 0)))      // the new `R`, down to the bottom edge
      hm-wire(((X.at(1), YU), (X.at(1), YM)))     // the new `L`, into the closing turn
      hm-wire(((X.at(2), HMON), (X.at(2), YM)))      // the old `R`, into the closing turn
      hm-wire(((X.at(3), HMON), (X.at(3), 0)))       // the old `L`, untouched
      hm-bead(hm-apex(X.at(0), X.at(1), YU), `η`, col: ceta, dx: 0, dy: GAPN, anchor: "south")
      hm-bead(hm-apex(X.at(1), X.at(2), YM, dir: -1), `ε`, col: ceps,
        dx: 0, dy: -GAPN, anchor: "north")
      hm-port((X.at(2), HMON), `R`); hm-port((X.at(3), HMON), `L`)
      hm-port((X.at(0), 0), `R`, dir: -1); hm-port((X.at(3), 0), `L`, dir: -1)
    }),
    hm-panel(W2, HMON, fill: AC, {
      hm-wire(((X.at(0), HMON), (X.at(0), 0)))
      hm-wire(((X.at(1), HMON), (X.at(1), 0)))
      hm-port((X.at(0), HMON), `R`); hm-port((X.at(1), HMON), `L`)
      hm-port((X.at(0), 0), `R`, dir: -1); hm-port((X.at(1), 0), `L`, dir: -1)
    }),
  ),
  gap: 1.2,
)


// =================================================================================================
// THE NOTE'S OWN DRAWING CODE — diag/allegory-axioms.typ keeps only prose and its `cetz.canvas` calls.

// ==== palettes and colour constants — one hue per role, named for the role it plays ==============

/// The colour of a numbered generator: `/1` is drawn in the first colour, `/2` in the second.  A
/// bare `/` is 0 and stays black — most of the note has one `S` and nothing to tell apart.
#let zpal = (black, rgb("1565c0"), rgb("c62828"), rgb("2e7d32"))

// ONE HUE PER ROLE: `GIVEN1`/`GIVEN2` are the two arrows a picture is HANDED (which takes which carries
// nothing), `INDUCED` is what a universal property produces and is always dashed, `SLACK` marks a `⊑`.
#let GIVEN1 = rgb("#26734d")    // green

#let GIVEN2 = rgb("#7d3c98")    // purple

#let INDUCED = rgb("#1a5fb4")   // blue

#let SLACK = rgb("#c2247f")     // pink

// ==== ΔE76, and the hue a lane gets when `FCOL` does not name it ==================================
// CIELAB (D65) and the ΔE76 distance in it — the separation the palette is designed around, COMPUTED
// here rather than written into a comment per letter, because a comment cannot fail when a hue moves.
#let _lin(u) = if u <= 0.04045 { u / 12.92 } else { calc.pow((u + 0.055) / 1.055, 2.4) }
#let _fw(t) = if t > 0.008856 { calc.root(t, 3) } else { 7.787 * t + 16 / 116 }
#let lab76(c) = {
  let (r, g, b) = rgb(c).components(alpha: false).map(u => _lin(u / 100%))
  let y = 0.2126 * r + 0.7152 * g + 0.0722 * b
  let (fx, fy, fz) = (_fw((0.4124 * r + 0.3576 * g + 0.1805 * b) / 0.95047), _fw(y),
                      _fw((0.0193 * r + 0.1192 * g + 0.9505 * b) / 1.08883))
  (116 * fy - 16, 500 * (fx - fy), 200 * (fy - fz))
}
#let dE76(a, b) = {
  let (p, q) = (lab76(a), lab76(b))
  calc.sqrt(calc.pow(p.at(0) - q.at(0), 2) + calc.pow(p.at(1) - q.at(1), 2)
            + calc.pow(p.at(2) - q.at(2), 2))
}
// Lab back to sRGB.  A point outside the gamut is NOT clipped: clipping lands it somewhere else in
// Lab, where the separation it was chosen for no longer holds, so the caller drops it instead.
#let _unf(t) = if t > 0.206893 { t * t * t } else { (t - 16 / 116) / 7.787 }
#let _gam(u) = if u <= 0.0031308 { 12.92 * u } else { 1.055 * calc.pow(u, 1 / 2.4) - 0.055 }
#let labcol(L, A, B) = {
  let y = (L + 16) / 116
  let (X, Y, Z) = (0.95047 * _unf(y + A / 500), _unf(y), 1.08883 * _unf(y - B / 200))
  let ch = (3.2406 * X - 1.5372 * Y - 0.4986 * Z, -0.9689 * X + 1.8758 * Y + 0.0415 * Z,
            0.0557 * X - 0.2040 * Y + 1.0570 * Z)
  // The 0.001 slack is the round trip's own error, and the clamp is only for that slack: a point
  // further out than it is dropped above, never squeezed back in.
  if ch.any(u => u < -0.001 or u > 1.001) { none }
  else { rgb(..ch.map(u => calc.max(0%, calc.min(100%, _gam(u) * 100%)))) }
}

#let SEPFIX = 25      // a lane against a bead hue or an object hue — the two things it is read beside
#let SEPPAIR = 12     // a lane against another lane anywhere in the note
#let SEPPANEL = 29    // ... and against one drawn in the SAME panel; the note's own tightest is `F`/`L`
// The rings the muted band is: lightness and chroma in Lab, hue swept round each.  Six of them, not
// one, because one ring at one lightness has too few points left once the declared lanes and the
// fixed obstacles have taken their neighbourhoods.
#let RINGS = ((38, 30), (50, 30), (62, 30), (44, 42), (56, 42), (66, 36))

// The hues STILL FREE: every ring point clear of the beads, the object hues and every declared lane,
// thinned so two of them are themselves apart.  Pure, so Typst memoises it — one sweep per document.
#let freehues() = {
  let obst = (GIVEN1, GIVEN2, INDUCED, SLACK, black, TCOL, BCOL, CCOL, GCOL)
  let out = ()
  for (L, C) in RINGS {
    for i in range(90) {
      let c = labcol(L, C * calc.cos(i * 4deg), C * calc.sin(i * 4deg))
      if (c != none and obst.all(o => dE76(c, o) >= SEPFIX)
          and FCOL.values().all(o => dE76(c, o) >= SEPPAIR)
          and out.all(o => dE76(c, o) >= SEPPAIR + 1)) { out.push(c) }
    }
  }
  out
}
// A LANE'S COLOUR.  `FCOL`'s entry where it has one — so no panel in the note moves — and otherwise
// the free hue the name's own number picks, which is why a new functor draws without an edit here.
// Empty palette is the one failure, and it names the name and the two ways out.
#let fcol(nm) = {
  let n = plain(nm)
  if n in FCOL { FCOL.at(n) } else {
    let free = freehues()
    assert(free.len() > 0, message: "no hue for the functor `" + n + "`: every muted ring point is"
      + " within ΔE76 " + str(SEPFIX) + " of a bead or object hue, or " + str(SEPPAIR) + " of a lane"
      + " `FCOL` already names — give `" + n + "` an entry in `FCOL` (diag/draw.typ) or widen `RINGS`")
    free.at(calc.rem(namehash(n), free.len()))
  }
}
// THE PALETTE'S RULE IS ONLY TRUE PANEL BY PANEL — two lanes that never share a picture may reuse a
// band — so this is where it is checked: every pair of lanes drawn together, and every lane against
// the beads and object hues drawn beside it.  `lanes` and `obst` are `(name, colour)` pairs.
#let lanecheck(id, lanes, obst) = {
  for (i, a) in lanes.enumerate() {
    for b in lanes.slice(i + 1) {
      let d = dE76(a.at(1), b.at(1))
      assert(a.at(0) == b.at(0) or d >= SEPPANEL, message: "panel `" + id + "`: the lanes `"
        + a.at(0) + "` and `" + b.at(0) + "` are ΔE76 " + str(calc.round(d, digits: 1)) + " apart,"
        + " under " + str(SEPPANEL) + " — give one of them its own entry in `FCOL` (diag/draw.typ)")
    }
    for o in obst {
      let d = dE76(a.at(1), o.at(1))
      assert(d >= SEPFIX, message: "panel `" + id + "`: the lane `" + a.at(0) + "` is ΔE76 "
        + str(calc.round(d, digits: 1)) + " from " + o.at(0) + " drawn on it, under " + str(SEPFIX)
        + " — give the lane its own entry in `FCOL` (diag/draw.typ)")
    }
  }
}

// The 2-cell helpers, used by the Maps and Power-allegory sections below.  The two fills mean
// nothing on their own: one hue apiece to tell the two regions `Map(𝒜)` and `𝒜` apart.
#let fb-MAPC = rgb("#e6f3e4")

#let fb-ALLC = rgb("#e9e7f7")

// A third hue: `X`, `Y`, `Z` are three objects and two fills cannot tell them apart.  Fill and stroke
// stay SEPARATE paths — one `merge-path(close: true)` would draw a floor under each region.
#let fb-ZC = rgb("#faf0dc")

// The wall's stroke: `Λ` seals a wire inside the box and `∋` opens it, drawn left to right like every
// other string diagram here, so `Λ(R) ∋` reads in the order it is written.
#let fb-WALL = rgb("#2f6ea8")

#let fb-FILL = rgb("#eaf2fb")

// ==== coordinate and data tables — the cast of the set-theoretic pictures, and where it stands ==

#let IY = (a: 2.4, b: 0.8, c: -0.8, d: -2.4)

#let ADMIRES = ((1.6, `x`, ("a", "b", "c")),
              (-1.6, `x'`, ("a", "b")))

#let HATES = ((1.6, `y`, ("a", "b", "c")),
              (-1.6, `y'`, ("a", "b", "d")))

#let WORKS = ((0, `z`, ("a", "b")),)

// The cast and the numbers are the division section's, read for equality instead of containment.
#let ADMIRERS = (x1: (-5.2, 1.8), x2: (-5.2, -1.8))

#let HATERS = (y1: (5.2, 1.8), y2: (5.2, -1.8))

#let PEOPLE = (a: (0, 2.4), b: (0, 0.8), c: (0, -0.8), d: (0, -2.4))

// The lists keep their coordinates across §10's three pictures, so the reader compares them by looking
// at the same place twice; `P(R)`'s two lists are the top and bottom one, whose arcs then sweep clear.
#let LX = (-8.6, 0)

#let AD = (a1: (-4.6, 1.6), a2: (-4.6, -1.6))

#let BD = (b1: (0.6, 2.2), b2: (0.6, 0), b3: (0.6, -2.2))

#let LY = (y1: (5.6, 3.3), y2: (5.6, 1.1), y3: (5.6, -1.1), y4: (5.6, -3.3))

// ==== primitive drawing helpers — one mark apiece, on a cetz canvas the caller opens =============

// `lab` lives here, ahead of every hand-drawn picture: a Typst binding exists only from its definition on.
// A square's SMALLER side is always drawn down the left then across the bottom, so its `⊑` is `-45deg`.
#let lab(x, y, col, w, rot: 0deg) = d.content((x, y), rotate(rot, text(10pt, col)[#w]))

// `ar` pulls both ends back off the node centres: a head drawn at a centre is buried under that node's
// own white box.  `s0`/`s1` are the clearances — 0.95 leaving `A × B` sideways, 0.55 entering vertically.
#let ar(a, b, col, dash: none, s0: 0.45, s1: 0.45) = {
  let (dx, dy) = (b.at(0) - a.at(0), b.at(1) - a.at(1))
  let n = calc.sqrt(dx * dx + dy * dy)
  d.line((a.at(0) + s0 / n * dx, a.at(1) + s0 / n * dy),
    (b.at(0) - s1 / n * dx, b.at(1) - s1 / n * dy),
    mark: (end: ">", scale: 0.5), stroke: (thickness: 0.75pt, paint: col, dash: dash))
}

// Nodes are drawn last, with a white fill, so an edge may start at the node's centre and let the box
// cover the stub — every edge then ends the same distance from its label, whatever its width.
#let node(x, y, c, w) = d.content((x, y), box(inset: 4pt, fill: white)[#text(10pt, c)[#w]])

// A column of nodes at x; a row is (y, label, the people it names).
#let nodes(x, rows) = for (k, row) in rows.enumerate() { node(x, row.at(0), (INDUCED, SLACK).at(k), row.at(1)) }

#let ings(x) = for (it, y) in IY { node(x, y, black, raw(it)) }

// Every arrow from column x into the shared-pool column xi, stopping on the side it comes from.
#let edges(x, xi, rows) = {
  let dir = if x < xi { -1 } else { 1 }
  for (k, row) in rows.enumerate() { for it in row.at(2) {
    d.line((x, row.at(0)), (xi + 1.05 * dir, IY.at(it)), mark: (end: ">", scale: 0.5),
      stroke: 0.75pt + (INDUCED, SLACK).at(k)) } }
}

// The label goes on the curve's own midpoint (`0.75h` from the axis, not `h`), or it floats off a deep
// arc.  `cx` shortens the controls' reach: how a bottom arc clears a column without diving twice as far.
#let arc(a, b, up, lab, col: GIVEN2, h: 3.8, cx: 4) = {
  let (x0, y0) = (a.at(0), a.at(1) + 0.45 * up)
  let (x1, y1) = (b.at(0), b.at(1) + 0.45 * up)
  let c = (x1 - x0) / cx
  d.bezier((x0, y0), (x1, y1), (x0 + c, h * up), (x1 - c, h * up),
    mark: (end: ">", scale: 0.55), stroke: 0.9pt + col)
  d.content(((x0 + x1) / 2, 0.125 * y0 + 0.75 * h * up + 0.125 * y1),
    box(inset: 3pt, fill: white)[#text(9.5pt, col)[#lab]])
}

#let head(x, lab) = d.content((x, 3.9), text(9.5pt, luma(60))[#lab])

// `∋` is a large operator, so a plain `∋_R` sets the `R` UNDERNEATH it; `attach(.., br: ..)` puts it
// where Freyd has it.  Out here, not inside the block, because the table below subscripts `∋` too.
#let e(x) = math.attach(math.class("normal", [∋]), br: x)

// A 2-cell: `wiredot` at the radius every generator uses, so a 2-cell and a generator look alike on
// purpose — both are a node on a wire.
#let fb-dot(p, t, dx: 0.34, dy: 0) = {
  wiredot(p)
  lab(p.at(0) + dx, p.at(1) + dy, black)[#t]
}

// `⊥` on a wire: the wire is DRAWN and then severed, a stop bar facing each side of the gap.  A blank
// space would say "no wire of this type"; `⊥` says the type is there and nothing gets across it.
#let blocked(a, b, gap: 0.34, h: 0.26) = {
  let (ax, ay) = a
  let (bx, by) = b
  let (l, r) = ((ax + bx) / 2 - gap / 2, (ax + bx) / 2 + gap / 2)
  wire(a, (l, ay)); wire((r, by), b)
  for x in (l, r) { d.line((x, ay - h), (x, ay + h), stroke: (thickness: lw, paint: black)) }
}

// A hairline parting two independent pictures that share one canvas.
#let fb-rule(x, y0, y1) = d.line((x, y0), (x, y1), stroke: 0.4pt + luma(170))

// An `E B`-wire: two strands, each thinner than circuit's `lw` — at full weight the pair reads as two
// wires side by side rather than as one wire one level down.
#let fb-wire(a, b) = {
  for o in (0.055, -0.055) {
    d.line((a.at(0), a.at(1) + o), (b.at(0), b.at(1) + o), stroke: (thickness: 0.8pt))
  }
}

// The box IS the power relator: what is drawn inside is one level down.  The parameter is `name`, not
// `lab`, because the body calls `lab`, the note's 10pt in-figure label, which it would shadow.
#let fb-region(a, b, name: [`P`]) = {
  d.rect(a, b, radius: 0.2, fill: fb-FILL, stroke: (thickness: 1pt, paint: fb-WALL))
  lab((a.at(0) + b.at(0)) / 2, b.at(1) + 0.3, fb-WALL)[#name]
}

// A bare wall the wire crosses — the box opened, which is what `∋` does.  `side` and `up` push the
// name clear of whichever end of the wall the wire runs into.
#let fb-wall(x, y0, y1, name, side: 1, up: true) = {
  d.line((x, y0), (x, y1), stroke: (thickness: 1pt, paint: fb-WALL))
  lab(x + 0.42 * side, if up { y1 + 0.22 } else { y0 - 0.22 }, fb-WALL)[#name]
}

// `𝟙%∋`, the unit.  `chamfer: false` is this note's mark for a map, and being a map is the whole
// reason `𝟙%∋` may be moved past another box while `∋` may not.
#let fb-sing(p) = gbox(p, $frac(#[`𝟙`], ∋)$, chamfer: false, w: 1.0, h: 1.2)

// WEIGHT, NOT HUE, carries the comparison: the heavy fans are the pair claimed to match, the washed-out
// ones the pairs that fail, so hue is left to the family — blue for `A`, pink for `H`, as everywhere.
#let syqnode(p, c, fill, w, ring: none) = d.content(p,
  box(inset: 4pt, fill: fill, radius: 3pt, stroke: ring)[#text(10pt, c)[#w]])

// Every arrow stops short of the dot it names, on the side it comes from, so the two columns' heads
// meet over the person instead of piling onto it.
#let syqedge(from, to, col, w) = {
  let dir = if from.at(0) < to.at(0) { -1 } else { 1 }
  d.line(from, (to.at(0) + 0.42 * dir, to.at(1)),
    mark: (end: ">", scale: if w > 0.9 { 0.55 } else { 0.4 }), stroke: w * 1pt + col)
}

// `choose ≜ π₁ ∪ π₂` as ONE region: the tape this note draws every `∪` with, holding TWO STACKED
// CIRCUITS — `upper` is the whole `π₁` branch, `lower` the whole `π₂` branch, each an ordinary black
// circuit with its own wires, its own boxes and its own discard.  The two alternatives are told
// apart by BEING TWO PICTURES, not by two colours laid over one.
// Colour and dash mark one thing only: the region's ports are doubled, so the pair that arrives once
// has to reach both copies and each copy's output has to reach the one output wire.  Those are the
// connections that cross the region's boundary — `GIVEN1` to and from the upper copy, `GIVEN2` the
// lower — and nothing inside a copy is ever coloured.
// `a`/`b` are the region's corners, like `tape`.  A copy is drawn `CHPAD` inside them, in its OWN
// coordinates: input ports at `(0, ±ip)`, output at `(w, ±op)` with the sign the side that branch
// keeps, and width exactly `b.x - a.x - 2*CHPAD`.  `hh` is the copy's half-height — what the branch
// name is placed clear of.
// DRAW IT BEFORE the wires that reach it: the tape's fill would otherwise cover them.
#let CHPAD = 0.5        // the region's edge to the copies inside it
#let CHFAN = 0.9        // the region's edge to where the external wires stop — the fan's run
#let choosebox(a, b, upper, lower, ip: 0.5, op: 0.5, hh: 0.5) = {
  let cy = (a.at(1) + b.at(1)) / 2
  // the copies must stand FURTHER apart than the wires inside one of them, or the reader sees
  // four evenly spaced strands instead of two circuits.
  let dy = hh + 0.9
  let cx = a.at(0) + CHPAD
  let ox = b.at(0) - CHPAD
  let xi = a.at(0) - CHFAN
  let xo = b.at(0) + CHFAN
  let fan(col) = (thickness: lw, paint: col, dash: "dashed")
  tape(a, b)
  lab((a.at(0) + b.at(0)) / 2, b.at(1) + 0.3, TAPEEDGE)[`∪`]
  d.group({ d.translate((cx, cy + dy)); upper })
  d.group({ d.translate((cx, cy - dy)); lower })
  // in: the pair arrives once and is handed to both copies, wire for wire
  for s in (1, -1) {
    bend((xi, cy + s * ip), (cx, cy + dy + s * ip), stroke: fan(GIVEN1))
    bend((xi, cy + s * ip), (cx, cy - dy + s * ip), stroke: fan(GIVEN2))
  }
  // out: whichever branch ran, its output is the region's
  bend((ox, cy + dy + op), (xo, cy), stroke: fan(GIVEN1))
  bend((ox, cy - dy - op), (xo, cy), stroke: fan(GIVEN2))
  lab(cx + 0.3, cy + dy + hh + 0.34, GIVEN1)[`π₁`]
  lab(cx + 0.3, cy - dy - hh - 0.34, GIVEN2)[`π₂`]
}

// ==== named whole pictures — bound because each is drawn more than once ==========================

// The collapsed domain, bound rather than drawn in place: it is the right-hand step of both chains
// below.  `rel` draws the symbol at the picture's LEFT EDGE — beside a canvas it sits on the baseline.
#let domstr(rel: none) = cetz.canvas(length: 0.8cm, {
  let y = 0.85
  if rel != none { lab(-1.2, 0, black)[#rel] }
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (3.75, y))
  wire((1.55, -y), (1.9, -y)); gbox((1.9, -y), [R]); wire((2.82, -y), (3.3, -y))
  wiredot((3.3, -y))
  lab(-0.35, 0, black)[$A$]; lab(4.1, y, black)[$A$]
})

// `◁` then `R ⊗ S`, bound because it is also the last step of the collapse chain below.  `eq` draws the
// `=` at the LEFT EDGE, as `./scripts/diag-export` does: beside the canvas it would sit on the baseline.
#let pairstr(eq: false) = cetz.canvas(length: 0.8cm, {
  let y = 0.85
  if eq { lab(-1.2, 0, black)[$=$] }
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (1.9, y)); wire((1.55, -y), (1.9, -y))
  gbox((1.9, y), [R]); gbox((1.9, -y), [S])
  wire((2.82, y), (3.4, y)); wire((2.82, -y), (3.4, -y))
  lab(-0.35, 0, black)[$C$]; lab(3.75, y, GIVEN1)[$A$]; lab(3.75, -y, GIVEN2)[$B$]
})

// The `Λ` family's geometry, one copy for all three pictures: wider and taller than §14's monads,
// three beads down one wire and a loop that has to hold two names inside it.  `LAMY` are its rows.
#let LAMPAD = 0.6
#let LAMSEP = 1.1
// §12's pitch and margin, and for its own reason: `𝟙%∋` and `∋` are the only beads whose name is set
// ABOVE or BELOW the dot, and each reaches about 0.7 further towards its edge than one set beside it.
#let LAMPITCH = 0.9
#let LAMMARG = 0.9
// The rows top down, and the height that holds them: a law needing one more row LENGTHENS its panel
// instead of re-spacing what is already there, so a bead keeps its height as pictures grow.
#let lamy(n) = range(n).map(i => LAMMARG + (n - 1 - i) * LAMPITCH)
#let lamh(n) = 2 * LAMMARG + (n - 1) * LAMPITCH
#let LAMX = (0, 1, 2).map(i => LAMPAD + i * LAMSEP)
#let LAMW = 2 * LAMPAD + 2 * LAMSEP
#let LAMH = lamh(3)
#let LAMY = lamy(3)
// The quarter-arc that turns the `i` and `E` wires over: `r` its radius, `c` its bezier handle
// (cetz's own `corner-arc` constant, shapes.typ), so region and wire cannot disagree.
#let LAMR = LAMSEP / 2
#let LAMC = 0.551784 * LAMR
#let LAMM = (LAMX.at(0) + LAMX.at(1)) / 2

// The `i` and `E` names, on the wires they belong to; `y` because a picture that closes the pair puts
// them beside its beads and one that leaves it open puts them low, clear of everything above.
#let lamnames(y) = {
  d.content((LAMX.at(0) - 0.28, y), text(9pt, ADJC.i)[`i`], anchor: "east")
  d.content((LAMX.at(1) + 0.28, y), text(9pt, ADJC.E)[`E`], anchor: "west")
}

// ONE panel of `lamfuse`/`lamabsorb`: `𝟙%∋` opens the pair `i E` at `yu` and it stays open to the
// bottom edge, so a bead below that line reads as `E` of its arrow and one above it as the arrow.
// `cols` is one longer than `beads` — the segments the beads cut the object wire into — so a picture
// with fewer beads passes a shorter list instead of getting the three-colour one out of bounds.
#let lampanel(h, yu, beads, top: `C`, bot: `B`, cols: (CCOL, TCOL, BCOL)) = hm-panel(LAMW, h, fill: fb-ALLC, {
  d.rect((LAMX.at(2), 0), (LAMW, h), fill: UC, stroke: none)
  d.merge-path(close: true, fill: fb-MAPC, stroke: none, {
    d.line((LAMX.at(0), 0), (LAMX.at(0), yu - LAMR))
    d.bezier((LAMX.at(0), yu - LAMR), (LAMM, yu), (LAMX.at(0), yu - LAMR + LAMC), (LAMM - LAMC, yu))
    d.bezier((LAMM, yu), (LAMX.at(1), yu - LAMR), (LAMM + LAMC, yu), (LAMX.at(1), yu - LAMR + LAMC))
    d.line((LAMX.at(1), yu - LAMR), (LAMX.at(1), 0))
  })
  let side(xe, s, col) = d.merge-path(fill: none, stroke: (thickness: lw, paint: col), {
    d.bezier((LAMM, yu), (xe, yu - LAMR), (LAMM - s * LAMC, yu), (xe, yu - LAMR + LAMC))
    d.line((xe, yu - LAMR), (xe, 0))
  })
  side(LAMX.at(0), 1, ADJC.i); side(LAMX.at(1), -1, ADJC.E)
  // The object wire changes type at every bead on it, so the bead heights ARE the segment bounds:
  // `C` down to the first, `A` to the second, `B` to the bottom edge.
  let ys = (h,) + beads.map(b => b.at(0)) + (0,)
  for (k, c) in cols.enumerate() {
    hm-wire(((LAMX.at(2), ys.at(k)), (LAMX.at(2), ys.at(k + 1))), col: c)
  }
  hm-bead((LAMM, yu), $frac(#[`𝟙`], ∋)$, col: GIVEN2, dx: 0, dy: 0.3, anchor: "south")
  for (y, b, col) in beads { hm-bead((LAMX.at(2), y), b, col: col) }
  lamnames(LAMMARG / 2)
  hm-port((LAMX.at(2), h), top, col: cols.first()); hm-port((LAMX.at(2), 0), bot, dir: -1, col: cols.last())
})

// The bare arrow `R : A ⟶ B` in `𝒜`, nothing opened: `lamsnake`'s right-hand side and
// `lamtranspose`'s left-hand side are the same panel, at the height its row needs.
#let lamplain(h, y) = hm-panel(2 * LAMPAD, h, fill: fb-ALLC, {
  d.rect((LAMPAD, 0), (2 * LAMPAD, h), fill: UC, stroke: none)
  hm-wire(((LAMPAD, h), (LAMPAD, y)), col: TCOL)
  hm-wire(((LAMPAD, y), (LAMPAD, 0)), col: BCOL)
  hm-bead((LAMPAD, y), `R`)
  hm-port((LAMPAD, h), `A`, col: TCOL); hm-port((LAMPAD, 0), `B`, dir: -1, col: BCOL)
})

// `lamtranspose` — `Λ` and `·∋` are no part of a picture: they take one picture to another, so they
// are drawn as the ARROWS BETWEEN two panels.  `Λ` glues the `𝟙%∋` cap on and `·∋` glues `∋` on.
#let lamtranspose() = {
  let (h, y) = (lamh(2), lamy(2))
  // The cap each arrow glues on is the colour of that cap's bead, so the arrow and the bead it
  // produces are read as one thing.
  let name(a, n, col, up) = {
    let (t, b) = (text(10pt, col)[#n], text(17pt, col)[#a])
    grid(rows: 2, row-gutter: 1pt, align: center, ..if up { (t, b) } else { (b, t) })
  }
  hm-row(
    (lamplain(h, y.at(1)),
     lampanel(h, y.at(0), ((y.at(1), `R`, black),), top: `A`, cols: (TCOL, BCOL))),
    sep: grid(rows: 2, row-gutter: 5pt, align: center,
      name($arrow.r.long$, $frac(#box(width: 8pt), ∋)$, GIVEN2, true), name($arrow.l.long$, `·∋`, GIVEN1, false)),
    gap: 2.6,
  )
}

// `lambend` — IntroString (4.7) p.98 at `i ⊣ E`.  ONLY PICTURE HERE THAT DRAWS `i` AS A STRAND THE
// ARROW ABSORBS: `R : i A ⟶ B` is a 2-cell `i∘A ⇒ B`, so bending `i` over a cap is what transposes it.
#let BH = 2.9                   // panel height, all four
#let BRISE = 0.62               // hm-turn's default rise, respelled so a fill can be handed the same
// The turn re-traced for a FILL: `hm-turn` strokes this same cubic, so region and wire cannot disagree.
#let bturn(xl, xr, y, dir) = {
  let h = dir * BRISE * (xr - xl)
  d.bezier((xl, y), (xr, y), (xl, y + h), (xr, y + h))
}

// `R : A ⟶ B` — the `A` strand bends into `i` and the pair leaves as `B`.
#let bp1() = {
  let (xi, xa, w, y) = (0.7, 1.8, 2.4, 1.25)
  hm-panel(w, BH, fill: fb-ALLC, {
    hm-region(((xa, BH), (xa, y + KNEE), (xi, y), (xi, 0), (w, 0), (w, BH)), UC)
    hm-region(((xi, BH), (xi, y), (xa, y + KNEE), (xa, BH)), fb-MAPC)
    hm-wire(((xi, BH), (xi, y)), col: ADJC.i); hm-wire(((xi, y), (xi, 0)), col: BCOL)
    hm-join(xa, BH, xi, y, col: TCOL)
    hm-bead((xi, y), `R`, dx: -0.3, anchor: "east")
    hm-port((xi, BH), `i`, col: ADJC.i); hm-port((xa, BH), `A`, col: TCOL)
    hm-port((xi, 0), `B`, dir: -1, col: BCOL)
  })
}

// `Λ(R) ∋` — the map first, then `∋` closes the `i E` pair it opened.
#let bp2() = {
  // The `∋` name hangs below the arch, so a `y2` under 1.05 puts that name outside the panel.
  let (xi, xm, xa, w) = (0.5, 1.35, 2.2, 3.4)
  let (y1, y2) = (1.95, 1.05)
  hm-panel(w, BH, fill: fb-ALLC, {
    hm-region(((xa, BH), (xa, 0), (w, 0), (w, BH)), UC)
    d.merge-path(close: true, fill: fb-MAPC, stroke: none, {
      d.line((xi, BH), (xi, y2))
      bturn(xi, xm, y2, -1)
      hm-path(((xm, y2), (xm, y1 - KNEE), (xa, y1), (xa, BH)))
    })
    hm-wire(((xi, BH), (xi, y2)), col: ADJC.i)
    hm-turn-split(xi, xm, y2, ADJC.i, ADJC.E, dir: -1)
    hm-wire(((xm, y2), (xm, y1 - KNEE), (xa, y1)), col: ADJC.E)
    hm-wire(((xa, BH), (xa, y1)), col: TCOL); hm-wire(((xa, y1), (xa, 0)), col: BCOL)
    hm-bead((xa, y1), $frac(#[`R`], ∋)$, col: INDUCED)
    hm-bead(hm-apex(xi, xm, y2, dir: -1), `∋`, col: GIVEN1, dx: 0, dy: -0.3, anchor: "north")
    hm-port((xi, BH), `i`, col: ADJC.i); hm-port((xa, BH), `A`, col: TCOL)
    hm-port((xa, 0), `B`, dir: -1, col: BCOL)
  })
}

// `𝟙%∋ E(R)` — the cap opens `E i`, and `R` below it absorbs that `i`, so what leaves is `E B`.
#let bp3() = {
  // The `𝟙%∋` name rises above the arch, so a `y1` over 1.8 puts that name outside the panel.
  let (xe, xi, xa, w) = (0.5, 1.35, 2.2, 3.0)
  let (y1, y2) = (1.8, 0.9)
  hm-panel(w, BH, fill: fb-MAPC, {
    d.merge-path(close: true, fill: fb-ALLC, stroke: none, {
      bturn(xe, xi, y1, 1)
      d.line((xi, y1), (xi, 0), (xe, 0))
    })
    hm-region(((xa, BH), (xa, y2 + KNEE), (xi, y2), (xi, 0), (w, 0), (w, BH)), UC)
    hm-turn-split(xe, xi, y1, ADJC.E, ADJC.i, dir: 1)
    hm-wire(((xe, y1), (xe, 0)), col: ADJC.E)
    hm-wire(((xi, y1), (xi, y2)), col: ADJC.i); hm-wire(((xi, y2), (xi, 0)), col: BCOL)
    hm-join(xa, BH, xi, y2, col: TCOL)
    hm-bead(hm-apex(xe, xi, y1, dir: 1), $frac(#[`𝟙`], ∋)$, col: GIVEN2, dx: 0, dy: 0.3, anchor: "south")
    hm-bead((xi, y2), `R`)
    hm-port((xa, BH), `A`, col: TCOL)
    hm-port((xe, 0), `E`, dir: -1, col: ADJC.E); hm-port((xi, 0), `B`, dir: -1, col: BCOL)
  })
}

// `Λ(R) : A ⟶ E B` — one bead, and the `E` it produces is the strand that bent away in `bp2`.
#let bp4() = {
  let (xe, xa, w, y) = (0.7, 1.8, 3.0, 1.4)
  hm-panel(w, BH, fill: fb-MAPC, {
    hm-region(((xa, y), (xe, y - KNEE), (xe, 0), (xa, 0)), fb-ALLC)
    hm-region(((xa, BH), (xa, 0), (w, 0), (w, BH)), UC)
    hm-wire(((xa, BH), (xa, y)), col: TCOL); hm-wire(((xa, y), (xa, 0)), col: BCOL)
    hm-wire(((xa, y), (xe, y - KNEE), (xe, 0)), col: ADJC.E)
    hm-bead((xa, y), $frac(#[`R`], ∋)$, col: INDUCED)
    hm-port((xa, BH), `A`, col: TCOL)
    hm-port((xe, 0), `E`, dir: -1, col: ADJC.E); hm-port((xa, 0), `B`, dir: -1, col: BCOL)
  })
}

#let lambend() = grid(columns: 3, column-gutter: 20pt, align: horizon,
  hm-row((bp1(), bp2()), gap: 1.2), text(15pt)[$arrow.l.r.double$],
  hm-row((bp3(), bp4()), gap: 1.2))

// `lamsnake` — `Λ(R) ∋ = R`: the object wire runs straight through, never consumed.  Beside it `𝟙%∋`
// opens the pair `i E` and `∋` closes it, and the loop's two sides are those two functors.
#let lamsnake() = hm-row(
  (
    hm-panel(LAMW, LAMH, fill: fb-ALLC, {
      d.rect((LAMX.at(2), 0), (LAMW, LAMH), fill: UC, stroke: none)
      // The rect keeps the FILL and its outline is re-traced in halves off the same arc constants,
      // so region and wire cannot disagree.
      d.rect((LAMX.at(0), LAMY.at(2)), (LAMX.at(1), LAMY.at(0)), radius: LAMR, fill: fb-MAPC, stroke: none)
      let side(xe, s, col) = d.merge-path(fill: none, stroke: (thickness: lw, paint: col), {
        d.bezier((LAMM, LAMY.at(0)), (xe, LAMY.at(0) - LAMR), (LAMM - s * LAMC, LAMY.at(0)),
          (xe, LAMY.at(0) - LAMR + LAMC))
        d.line((xe, LAMY.at(0) - LAMR), (xe, LAMY.at(2) + LAMR))
        d.bezier((xe, LAMY.at(2) + LAMR), (LAMM, LAMY.at(2)), (xe, LAMY.at(2) + LAMR - LAMC),
          (LAMM - s * LAMC, LAMY.at(2)))
      })
      side(LAMX.at(0), 1, ADJC.i); side(LAMX.at(1), -1, ADJC.E)
      hm-wire(((LAMX.at(2), LAMH), (LAMX.at(2), LAMY.at(1))), col: TCOL)
      hm-wire(((LAMX.at(2), LAMY.at(1)), (LAMX.at(2), 0)), col: BCOL)
      hm-bead((LAMM, LAMY.at(0)), $frac(#[`𝟙`], ∋)$, col: GIVEN2, dx: 0, dy: 0.3, anchor: "south")
      hm-bead((LAMM, LAMY.at(2)), `∋`, col: GIVEN1, dx: 0, dy: -0.3, anchor: "north")
      hm-bead((LAMX.at(2), LAMY.at(1)), `R`)
      lamnames(LAMY.at(1))
      hm-port((LAMX.at(2), LAMH), `A`, col: TCOL); hm-port((LAMX.at(2), 0), `B`, dir: -1, col: BCOL)
    }),
    lamplain(LAMH, LAMY.at(1)),
  ),
  gap: 1.2,
)

// `lamfuse` — `Λ(f R) = f Λ(R)`: the map bead `f` slides across `𝟙%∋`, which is unit naturality.
// `𝟙%∋` HOLDS STILL on row 2 and only `f` moves — that is the law — so `f` needs a row of its own on
// each side, the panel is FOUR rows, and each side leaves one of them empty.
#let lamfuse() = {
  let y = lamy(4)
  hm-row(
    (lampanel(lamh(4), y.at(1), ((y.at(2), `f`, GIVEN1), (y.at(3), `R`, black))),
     lampanel(lamh(4), y.at(1), ((y.at(0), `f`, GIVEN1), (y.at(3), `R`, black)))),
    gap: 1.2,
  )
}

// `lamabsorb` — the two panels are DELIBERATELY the same strokes: the law is an identity of pictures,
// and drawing both with the `=` between them is what says so.
#let lamabsorb() = hm-row(
  (lampanel(LAMH, LAMY.at(0), ((LAMY.at(1), `S`, GIVEN1), (LAMY.at(2), `R`, GIVEN2))),
   lampanel(LAMH, LAMY.at(0), ((LAMY.at(1), `S`, GIVEN1), (LAMY.at(2), `R`, GIVEN2)))),
  gap: 1.2,
)

// `snake` — ONE triangle identity of `i ⊣ E`, on `unitlaw`'s geometry: the incoming wire, both turns
// and the outgoing one are one strand.  `flip` puts the opened pair left of it instead of right.
#let snake(name, other, flip) = {
  let (xin, xmid, xout) = if flip { (X.at(2), X.at(1), X.at(0)) } else { (X.at(0), X.at(1), X.at(2)) }
  let (cl, cr) = (calc.min(xin, xmid), calc.max(xin, xmid))
  let (ul, ur) = (calc.min(xmid, xout), calc.max(xmid, xout))
  // A wire's hue is the functor it carries, so a turn is half of each and changes over at the apex,
  // where its bead already sits: `xmid` is `other`'s column, and the two ends are `name`'s.
  let (cn, co) = (ADJC.at(name.text), ADJC.at(other.text))
  let hue(x) = if x == xmid { co } else { cn }
  // ONE rise for the wire and for the region under it — hm-turn's default, respelled so the fill
  // below can be handed the same number instead of hand-fitting a curve to it.
  let rise = 0.62
  let arch(xa, xb, y, dir) = {
    let hh = dir * rise * calc.abs(xb - xa)
    d.bezier((xa, y), (xb, y), (xa, y + hh), (xb, y + hh))
  }
  // The strand cuts the panel in two: `𝒜` is the side the counit lands in, `Map(𝒜)` the side the unit
  // opens out of, and `xc` is whichever bottom corner `𝒜` reaches.
  let xc = if flip { W3 } else { 0 }
  hm-row(
    (
      hm-panel(W3, HMON, fill: fb-MAPC, {
        d.merge-path(close: true, fill: fb-ALLC, stroke: none, {
          d.line((xc, HMON), (xin, HMON), (xin, YM))
          arch(xin, xmid, YM, -1)
          d.line((xmid, YM), (xmid, YU))
          arch(xmid, xout, YU, 1)
          d.line((xout, YU), (xout, 0), (xc, 0))
        })
        hm-wire(((xin, HMON), (xin, YM)), col: cn)
        hm-turn-split(cl, cr, YM, hue(cl), hue(cr), dir: -1, rise: rise)
        hm-wire(((xmid, YM), (xmid, YU)), col: co)
        hm-turn-split(ul, ur, YU, hue(ul), hue(ur), rise: rise)
        hm-wire(((xout, YU), (xout, 0)), col: cn)
        hm-bead(hm-apex(ul, ur, YU, rise: rise), $frac(#[`𝟙`], ∋)$, col: GIVEN2, dx: 0, dy: GAPN, anchor: "south")
        hm-bead(hm-apex(cl, cr, YM, dir: -1, rise: rise), `∋`, col: GIVEN1,
          dx: 0, dy: -GAPN, anchor: "north")
        // The middle strand carries no port, so it is named where it runs, on the incoming wire's side.
        d.content((xmid + if flip { 0.28 } else { -0.28 }, (YM + YU) / 2), text(9pt, co)[#other],
          anchor: if flip { "west" } else { "east" })
        hm-port((xin, HMON), name, col: cn); hm-port((xout, 0), name, dir: -1, col: cn)
      }),
      hm-panel(W1, HMON, fill: if flip { fb-MAPC } else { fb-ALLC }, {
        d.rect((PADX, 0), (W1, HMON), fill: if flip { fb-ALLC } else { fb-MAPC }, stroke: none)
        hm-wire(((PADX, HMON), (PADX, 0)), col: cn)
        hm-port((PADX, HMON), name, col: cn); hm-port((PADX, 0), name, dir: -1, col: cn)
      }),
    ),
    gap: 1.2,
  )
}

// `snaketri` — the same identity as a commutative triangle, `f` the functor that survives and `comp`
// the composite the unit opens.  `𝟙` is SOLID: dashed is what a universal property produces.
// `unit`/`counit` are PASSED, not the bare `𝟙%∋`/`∋`: the nodes here are FUNCTORS, so the arrows are
// the transformation with a functor composed on, and dropping it loses the one thing the picture says.
#let snaketri(f, comp, unit, counit) = cetz.canvas(length: 0.8cm, {
  let (L, T, B) = ((-2, 1.1), (2, 1.1), (2, -1.1))
  ar(L, T, GIVEN2, s0: 0.4, s1: 0.95)
  ar(T, B, GIVEN1, s0: 0.5, s1: 0.4)
  ar(L, B, INDUCED, s0: 0.4, s1: 0.5)
  lab(0, 1.65, GIVEN2)[#unit]; lab(2.9, 0, GIVEN1)[#counit]; lab(-0.25, -0.6, INDUCED)[`𝟙`]
  node(L.at(0), L.at(1), black, f); node(T.at(0), T.at(1), black, comp)
  node(B.at(0), B.at(1), black, f)
})

// ==== picture-frame helpers — what a picture is placed IN: boxes, rows, derivations, rules =======

/// A run of generators as one polyline; the height is which hom-set you are in (`T//` climbs two).
/// One `line` per generator so each carries its own colour; `box` because the lines are `place`d.
#let zwire(cs) = {
  let u = 0.44                                     // one generator's width, in em
  let gap = 0.26                                   // the break at a joint that does not bend
  let (x, l, xs, ls) = (0, 0, (0,), (0,))
  for (d, col, j) in cs { x += u; l += d; xs.push(x); ls.push(l) }
  let hi = calc.max(..ls)                          // `top` would shadow the alignment of that name
  let pt(i) = (xs.at(i), hi - ls.at(i))
  box(width: x * 1em, height: (hi - calc.min(..ls)) * 1em,
    cs.enumerate().map(((i, c)) => {
      let (p, q) = (pt(i), pt(i + 1))
      // A bend is its own mark; two strokes in a line need the joint OPENED, or `R\\` — divide by
      // `S₂` then by `S₁` — is the same stick as `R\2\1+`, divide by the one arrow `S₁S₂`.
      let (dx, dy) = (q.at(0) - p.at(0), q.at(1) - p.at(1))
      let n = calc.sqrt(dx * dx + dy * dy)
      let (ux, uy) = (dx / n * gap / 2, dy / n * gap / 2)
      if i > 0 and cs.at(i - 1).at(0) == c.at(0) and not c.at(2) { p = (p.at(0) + ux, p.at(1) + uy) }
      if i + 1 < cs.len() and cs.at(i + 1).at(0) == c.at(0) and not cs.at(i + 1).at(2) {
        q = (q.at(0) - ux, q.at(1) - uy)
      }
      place(top + left, line(
        start: (p.at(0) * 1em, p.at(1) * 1em), end: (q.at(0) * 1em, q.at(1) * 1em),
        stroke: (paint: zpal.at(c.at(1)), thickness: 0.07em, cap: "round")))
    }).join())
}

/// A word of the calculus: consecutive generators go into ONE `zwire` call, which is what connects them.
/// A digit numbers a generator (`T/1/2` is `T S₁ S₂`); `+` welds it to the one before (`R\2\1+` is `R/S₁S₂`).
#let zw(s) = {
  let out = ()
  let run = ()
  for c in s.clusters() {
    if c == "/" or c == "\\" { run.push((if c == "/" { 1 } else { -1 }, 0, false)) }
    else if run.len() > 0 and c.match(regex("^[0-9]$")) != none {
      let s = run.pop(); run.push((s.at(0), int(c), s.at(2)))
    } else if run.len() > 0 and c == "+" {
      let s = run.pop(); run.push((s.at(0), s.at(1), true))
    } else {
      if run.len() > 0 { out.push(zwire(run)); run = () }
      // `∗` is drawn up at the math axis; alone in a row it needs pushing down to look centred.
      out.push(if c == "*" { move(dy: 0.16em, $*$) } else { $italic(#c)$ })
    }
  }
  if run.len() > 0 { out.push(zwire(run)) }
  box(out.join(h(0.1em)))
}

/// `baseline: 50%` centres the box on its line; the default (bottom) would hang it off the baseline.
/// `name` is `place`d so it does not measure — a chain is centred on the horizon and would be lifted.
// The plain rule IS the `⊑` of §1's notation table; `eq` doubles it and colours it, so a line whose
// relation is `=` is told from a line whose relation is `⊑` without reading either row.
#let zsqc(a, b, name: none, eq: false) = box(
  stroke: 0.6pt + luma(120), fill: luma(253), radius: 2pt, inset: (y: 4pt), baseline: 50%,
  {
    // `bounds`: a line box is cap-height tall by default, so a row carrying a fraction overflows it
    // and the rule between the rows is drawn straight through the formula.
    set text(top-edge: "bounds", bottom-edge: "bounds")
    // The wide box only stops the name wrapping inside a narrow box — `place` is out of flow, so the
    // name still measures nothing and the centre it hangs from is unmoved.
    if name != none { place(bottom + center, dy: 1.15em, box(width: 6cm, align(center, src(name)))) }
    // `measure`, not `length: 100%`: inside an auto-sized column the percentage resolves against the
    // page, not against the box, and the rule would shoot out of it.
    let dbl = context {
      let w = calc.max(measure(a).width, measure(b).width) + 12pt
      stack(spacing: 1.4pt, ..(line(length: w, stroke: 0.55pt + TCOL),) * 2)
    }
    // The 6pt breathing room is on the cells, not the box: the grid then spans the box's full inner
    // width, so both rules land on the side strokes instead of stopping short of them.
    grid(columns: 1, align: center, inset: (x: 6pt), row-gutter: if eq { 1.5pt } else { 4pt },
         ..if b == none { (a,) } else if eq { (a, grid.cell(inset: 0pt, dbl), b) }
           else { (a, grid.hline(y: 1, stroke: 0.6pt + luma(120)), b) })
  },
)

/// The same box filled from the stroke calculus, where `/` and `\` are generators, not division.
#let zsq(a, b, name: none) = zsqc(zw(a), zw(b), name: name)

/// A step of a derivation, with the reason on the operator.  The operator is stretched to the width
/// of the reason, so the two read as one gesture instead of a hint parked beside a short `⟹`.
/// `under` drops the reason below the operator, for a step standing BETWEEN two boxes on one line:
/// above it, the reason would sit on the line the boxes are read along.
/// RULE: a reason NAMES THE ADJUNCTION AND STOPS — `f°·⊣f·`, unspaced, not the display it lives in,
/// not `, twice`, not the side conditions.  The reader knows where the table is; the strands are visible.
// No braces around the reason: they cost width in a chain that has to fit one row, and nothing reads
// a grey line under an arrow as anything but the reason.
#let zstep(reason, op: sym.arrow.r.double, under: false) = context {
  let r = src[#reason]
  let a = $stretch(#op, size: #measure(r).width)$
  grid(columns: 1, align: center, row-gutter: 2pt, ..if under { (a, r) } else { (r, a) })
}

/// A named law, its name out at the right where an equation number would go.  The empty `1fr` on the
/// left keeps the law centred on the page rather than on what is left once the name is placed.
#let znamed(name, ..items) = block(width: 100%, grid(
  columns: (1fr, auto, 1fr), align: horizon,
  [],
  grid(columns: items.pos().len(), align: horizon, column-gutter: 10pt, ..items.pos()),
  align(right, src(name)),
))

/// One line of a derivation that runs sideways: boxes and `zstep(under: true)`s alternating.  A
/// derivation too long for the column wraps into several of these, the next opening with its step.
#let zline(..items) = align(center, block(breakable: false, grid(
  columns: items.pos().len(), align: horizon, column-gutter: 7pt, ..items.pos(),
)))

/// Two boxes carrying two strands of ONE derivation.  A strand is a ROW here — stacking the pair puts
/// each strand on its own line across the whole `zline`, which is what says who continues whom.
#let zpair(a, b) = grid(columns: 1, align: center, row-gutter: 6pt, a, b)

/// `align: horizon` keeps the shared run on one line whatever the branches do — its cells span both
/// rows.  The parameter is `shared`, not `chain`: note-style exports a `chain` this would shadow.
#let zderiv(shared, branches) = align(center, block(grid(
  columns: shared.len() + 2, align: horizon, column-gutter: 10pt, row-gutter: 10pt,
  ..shared.map(c => grid.cell(rowspan: 2, c)),
  ..branches.map(b => (zstep(b.at(0)), b.at(1))).flatten(),
)))

// Everything all three pictures share.  `body` is drawn between the shared part and `x`'s own box, so
// an arc drawn there has its ends tucked under the boxes, the way §10 hides them.
#let skel(body) = {
  for a in (AD.a1, AD.a2) { syqedge(LX, a, INDUCED, 1.1) }
  ar(AD.a1, BD.b1, GIVEN1, s0: 0.3, s1: 0.3); ar(AD.a1, BD.b3, GIVEN1, s0: 0.3, s1: 0.3)
  ar(AD.a2, BD.b3, GIVEN1, s0: 0.3, s1: 0.3)
  for p in (AD.a1, AD.a2) { d.circle(p, radius: 0.17, fill: black, stroke: black) }
  // Filled = reached from `xs`, hollow = not.  That colouring IS `∋ R`, and the next two pictures do
  // nothing but read lists off these three dots.
  for p in (BD.b1, BD.b3) { d.circle(p, radius: 0.17, fill: GIVEN2, stroke: GIVEN2) }
  d.circle(BD.b2, radius: 0.17, fill: white, stroke: 0.9pt + black)
  lab(-4.6, 2.35, black)[`a₁`]; lab(-4.6, -2.35, black)[`a₂`]
  // `b₁`'s label goes to its RIGHT: above the dot it lands on the head of the first picture's arc.
  lab(1.5, 2.7, black)[`b₁`]; lab(0.6, 0.75, black)[`b₂`]; lab(0.6, -1.45, black)[`b₃`]
  lab(-6.6, 0, INDUCED)[`∋`]; lab(-2.0, 2.6, GIVEN1)[`R`]
  body
  syqnode(LX, GIVEN2, rgb("#f2e9f8"), `xs = {a₁,a₂}`, ring: 0.7pt + GIVEN2)
}

// A subset of `B`: its `∋` fan and its box, washed out when the picture rejects it.
#let yset(p, es, w, on: true) = {
  let (col, wt) = if on { (SLACK, 1.1) } else { (SLACK.lighten(60%), 0.7) }
  for b in es { syqedge(p, b, col, wt) }
  if on { syqnode(p, GIVEN2, rgb("#f2e9f8"), w, ring: 0.7pt + GIVEN2) } else { syqnode(p, black, white, w) }
}

// `capbox` — the frame binds picture and caption into one unit; the formula is a REQUIRED positional,
// so a law has one place to land.  Its stroke and radius are the note's own, not new values.
// It DRAWS a boundary, so it owns two bands and they are the only ones inside it (see `P`): `inset`
// keeps the panel's ink off the hairline, `row-gutter` separates the picture from its formula.
#let capbox(body, f) = align(center, box(
  stroke: 0.4pt + luma(190), radius: 2pt, inset: (x: 12pt, y: 6pt),
  grid(align: center, row-gutter: 6pt, body, f),
))

// Where a formula's own relation sign sits: the children up to the one holding it, then the text
// before it.  `none` unless exactly ONE stands before any `#h()` or `\` — only the first line carries
// the law.  `=` is tried first and `⊑` only when there is none, so an equation is never lined up on a
// `⊑` buried in one of its sides.
#let capeqx(f) = {
  let kids = if f.has("children") { f.children } else { (f,) }
  let find(sign) = {
    let (x, at, n) = (0pt, none, 0)
    for c in kids {
      if c.func() == h or c.func() == linebreak { break }
      let t = if c.has("text") { c.text } else { "" }
      let i = t.position(sign)
      if i != none {
        n += t.matches(sign).len()
        // Re-set as `raw` or as plain text, whichever the child was, or the prefix measures in the
        // wrong font and the shift is out by the difference.
        let same(s) = if c.func() == raw { raw(s, block: false) } else { s }
        if at == none { at = x + measure(same(t.slice(0, i))).width + measure(same(sign)).width / 2 }
      }
      x += measure(c).width
    }
    if n == 1 { at }
  }
  let at = find("=")
  if at == none { at = find("⊑") }
  at
}

// `pair` — square LEFT, string diagram RIGHT in one box: the reader checks one against the other, and
// stacked they were a scroll apart.  `s` scales BOTH halves, or the two can no longer be compared.
// THE FORMULA'S SIGN GOES UNDER THE PICTURE'S: the display states one law twice, once in strokes and
// once in symbols, and the reader drops from one sign to the other to match the sides.
#let pair(sq, sd, f, s: 100%) = layout(avail => {
  let body = grid(columns: 2, align: horizon, column-gutter: 34pt, P(sq, s: s), P(sd, s: s))
  let (px, fe) = (hm-sepx(sd), capeqx(f))
  if px == none or fe == none { return capbox(body, f) }
  // Where the formula starts with its sign under the picture's: in from the row's right end to the
  // string diagram's own left edge, on to the sign, then back by the formula's own.
  let bw = measure(body).width
  let fx = bw - measure(P(sd, s: s)).width + s * px - fe
  // `dx` moves the ROW right instead, for a sign so far into the formula that it would start off the
  // box's left edge.
  let dx = calc.max(0pt, -fx)
  let w = calc.max(bw + dx, fx + dx + measure(f).width)
  // A caption that far off centre can outgrow the page; centred beats aligned-and-overflowing.
  if w > avail.width - 26pt { return capbox(body, f) }
  // The offset is a grid COLUMN, not a `move`: `capbox` centres its rows, and that centring happens
  // after a move and would carry the sign straight back off the mark.
  let row(off, it) = box(width: w, grid(columns: (off, auto, 1fr), [], it, []))
  // The caption is left-aligned because `capbox`'s centring reaches inside it and would centre a
  // multi-line caption's first line — the one with the sign — over the longer prose line below.
  capbox(row(dx, body), row(fx + dx, align(left, f)))
})

// ---------------------------------------------------- the standalone page: the note's calls, BLACK BEADS
// A bead's colour in the note is its arrow's hue in the square beside it, and this page has no square.
#let cap(body) = align(center, box(width: 15cm, text(10.5pt, body)))
#let law(n, body) = align(center, text(10.5pt)[*#n* #h(6pt) #body])

// THE LAWS ARE NAMED, NOT NUMBERED, HERE: B&dM's `(2.10)`–`(2.13)` stay in the header as a citation,
// and printing them would put a second numbering beside the note's own `(12.n)`.
#law[the defining equation][`X = ⦇α`#sub[`B`]`⦈ ⟺ α`#sub[`T`]` X = F(X) α`#sub[`B`]]
// THE ONLY PICTURE HERE THAT NAMES ITS REGIONS; the rest carry the same fills unnamed, which is how
// Hinze & Marsden draw a second picture (Remark 2.1, p. 36) — `regions: auto`.
#align(center, homeq(`F`, `T`, [`α`#sub[`T`]], [`⦇α`#sub[`B`]`⦈`], [`α`#sub[`B`]], `B`,
  typed: true, regions: (`𝒜`, `𝟏`)))
#cap[
  This is the universal property: `α`#sub[`T`]` X = F(X) α`#sub[`B`]
  holds exactly when `X` is `⦇α`#sub[`B`]`⦈`, so the equation characterises `⦇α`#sub[`B`]`⦈` among
  ALL relations `T ⟶ B`, not only the maps.
  \ #v(3pt)
  `⦇α`#sub[`B`]`⦈` stands still: it is the middle bead of both panels, at the same height on both
  sides of the `=`. What moves is the algebra bead, which falls past it from the row above to the row
  below, entering the left panel as `α`#sub[`T`] and arriving in the right one as `α`#sub[`B`].
  \ #v(3pt)
  The `F` wire running straight past the `⦇α`#sub[`B`]`⦈` bead is exactly `F(⦇α`#sub[`B`]`⦈)`:
  applying a functor to an arrow costs no notation at all in this calculus (Hinze & Marsden,
  *Introducing String Diagrams* — `IntroString.pdf` — §1.4.2 and §1.5.2).
]

#v(14pt)
#law[reflection][`⦇α`#sub[`T`]`⦈ = 𝟙`]
// ONE COLOUR, END TO END, ON BOTH SIDES: `⦇α_T⦈ : T ⟶ T` changes nothing about the wire's type,
// which is why the bead can be deleted.
#align(center, beadeq(`T`, [`⦇α`#sub[`T`]`⦈`], `T`, typed: true, regions: auto))
#cap[Taking a value apart with `α`#sub[`T`] and putting it straight back is doing nothing.]

#v(14pt)
#law[fusion][`⦇α`#sub[`B`]`⦈ S = ⦇α`#sub[`C`]`⦈ ⟸ α`#sub[`B`]` S = F(S) α`#sub[`C`]]
#cap[the side condition — the picture above under
  `α`#sub[`T`]`↦α`#sub[`B`]`, ⦇α`#sub[`B`]`⦈↦S, α`#sub[`B`]`↦α`#sub[`C`]`, T↦B, B↦C`:]
// `tcol`/`bcol` SPELLED OUT: this wire runs `B` then `C`, and the defaults are `T` then `B`.
#align(center, homeq(`F`, `B`, [`α`#sub[`B`]], `S`, [`α`#sub[`C`]], `C`, typed: true, tcol: BCOL,
  bcol: CCOL, regions: auto))
#cap[the conclusion:]
// `T`, `B`, `C` down the left panel and `T`, `C` down the right: the defaults, this being the one
// picture the three type colours were chosen to keep apart.
#align(center, twobeadeq(`T`, [`⦇α`#sub[`B`]`⦈`], `S`, [`⦇α`#sub[`C`]`⦈`], `C`, typed: true,
  regions: auto))

#v(14pt)
#law[splitting the algebra][`⦇g f⦈ = ⦇F(f) g⦈ f`, for `f : X ⟶ A` and `g : F A ⟶ X`]
#align(center, splitcut(`F`, `X`, `f`, `g`, `f`, `A`,
  ltop: [`α`#sub[`B`]` = F(f) g`], lbot: `S = f`, rtop: `F(S) = F(f)`,
  rbot: [`α`#sub[`C`]` = g f`]))
#cap[
  Fusion at `α`#sub[`B`]` := F(f) g`, `S := f`, `α`#sub[`C`]` := g f`, whose side condition
  `α`#sub[`B`]` S = F(S) α`#sub[`C`] reads `(F(f) g) f = F(f) (g f)` — associativity, and
  nothing else.
  \ #v(3pt)
  The two readings are the two bracket columns, and the picture they bracket is the same one.
  Re-bracketing is what a string diagram has no notation for, so there is nothing here to prove.
]

#v(14pt)
#law[the type functor][`T(R) = ⦇F(R, 𝟙) α⦈`, drawn as the naturality of `α`]
// THE ONE PICTURE HERE WHOSE `F` IS A BIFUNCTOR: the bead is the transformation `R : A ⟶ B` induces —
// see `algpanel`'s `fmid`.  Everything else is (2.10)'s picture unchanged.
#align(center, homeq([`F`#sub[`A`]], [`T A`], `α`, [`T(R)`], `α`, [`T B`],
  fmid: [`F`#sub[`R`]], typed: true, regions: auto))
#cap[
  The two beads on row 2 stand on DIFFERENT wires, so their relative height says nothing: level, they
  read as the one action `F(R, T(R))`; slide `F`#sub[`R`] below the `T(R)` bead and they read
  `F(𝟙, T(R)) F(R, 𝟙)`, above it `F(R, 𝟙) F(𝟙, T(R))`. Those are the two routes the exchange condition
  identifies (Hinze & Marsden, Ex 1.23), and in this calculus there is nothing to identify.
  \ #v(3pt)
  `α` is one bead falling past `T(R)` from the row above to the row below, exactly as in (2.10) — which
  is what "`α` is natural" means. `T(R)` is the only bead that lets it fall.
]
