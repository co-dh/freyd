// circuit.typ — string-diagram primitives for the Rel(Set) calculus.  cetz 0.3.4.
//
// Reading conventions, as in diag/S2_124.typ and
// functorialSemanticsForRelationalTheories.pdf §2 (p. 7):
//
//   left to right   composition `;` — the book's diagram order, `x y` = first x then y
//   vertical stack  the monoidal product
//   solid dots      ALL FOUR generators `Δ`, `!`, `∇`, `?` — the shape says which
//   white boxes     relations; a bare wire is the identity
//
// WHY ALL FOUR ARE SOLID, since the paper also uses a hollow dot.  In
// functorialSemanticsForRelationalTheories.pdf the fill separates a monoid from a comonoid that is a
// DIFFERENT structure: Example 2.3 (a) draws a bare commutative monoid hollow, (b) a bare
// commutative comonoid solid, and (d)/(e) — bialgebras and Hopf algebras — put a hollow monoid and a
// solid comonoid in one picture, where the fill is the only thing telling the two apart.
//
// This calculus is neither of those.  It is Example 2.3(c), special Frobenius algebras, and there
// the monoid and the comonoid are two halves of ONE structure — in `Rel(Set)` each is literally the
// converse of the other.  Nothing needs telling apart, and the paper accordingly draws eqs. (11) and
// (12) with every dot solid, as it does the four generators of Def. 4.1 itself (p. 17, clauses 1 and
// 2).  The shape already carries the distinction: `Δ` opens to the right, `∇` closes from the left.
//
// `dot`'s `hollow` argument is kept for the case the paper reserves it for — a second, genuinely
// different monoid alongside this one.  That arrives in phase 8, where the tape layer adds `∪`/`⊥`.
//
// PROVENANCE.  The drawing code here was extracted from diag/S2_124.typ, the repo's own
// hand-authored string-diagram proof of §2.124, which now imports this file instead of keeping
// private copies.  Line weight, dot radius, bezier control fractions and the default stub lengths
// are its values unchanged, so its rendered PDF is unaffected.
//
// ONE VOCABULARY.  A picture and its Lean statement use the same word — these are the `CartBicat`
// field names of diag/CB.lean, unchanged:
//
//   delta  Δ : a → a ⊗ a     nabla  ∇ : a ⊗ a → a     cap  : a ⊗ a → I     swap  σ
//   bang   ! : a → I         unitR  ? : I → a         cup  : I → a ⊗ a
//
// functorialSemanticsForRelationalTheories.pdf calls the same four `Δ`, `!`, `∇`, `?` (Def. 4.1).
//
// Every function takes its anchor `p` as the LEFT edge of what it draws, on the wire it sits on,
// so a picture is laid out by walking an x grid rightwards.
//
// IMPORT BY NAME, NOT WITH `*`.  `delta`, `nabla`, `cap`, `cup` and `dot` are also Typst math
// symbols (δ, ∇, ∩, ∪, ⋅).  A wildcard import shadows them, and `$nabla$` then silently typesets a
// drawing function instead of ∇ — with no error.  Import the handful of names a note actually uses,
// and write the symbol itself in math.

#import "@preview/cetz:0.3.4"
#let d = cetz.draw

// ---------------------------------------------------------------- style constants
#let lw = 1.1pt         // wire thickness            (S2_124.typ)
#let Rr = 0.07          // solid dot radius          (S2_124.typ)
#let Rh = 0.088         // hollow dot radius — larger, or the ring closes up at `lw`
#let BW = 0.92          // default box width
#let BH = 0.60          // default box height
#let LEAD = 0.34        // wire stub before the first box of a chain and after the last
#let TAPEFILL = rgb("#f6cfcf")
#let TAPEEDGE = rgb("#c25b5b")

#let wstroke(invert: false) = (thickness: lw, paint: if invert { white } else { black })

// ---------------------------------------------------------------- wires and boxes

/// A straight wire from `a` to `b`.
#let wire(a, b, invert: false) = d.line(a, b, stroke: wstroke(invert: invert))

/// A wire from `a` to `b` leaving and arriving horizontally, so strands always meet boxes and dots
/// at right angles.  `k` is where the control points sit along the run: 0.6 opening out of a dot,
/// 0.4 closing into one — the two are mirror images, which is why forks and joins match.
/// `stroke` overrides the wire paint for a strand that is not an ordinary wire — the dashed coloured
/// fan into a region holding two alternatives, say.  Same geometry, so a parameter and not a helper.
#let bend(a, b, k: 0.6, invert: false, stroke: auto) = {
  let (ax, ay) = a
  let (bx, by) = b
  let mx = ax + (bx - ax) * k
  d.bezier(a, b, (mx, ay), (mx, by),
    stroke: if stroke == auto { wstroke(invert: invert) } else { stroke })
}

/// One node of the Frobenius structure.  Solid by default, which is every generator of THIS
/// calculus; `hollow` is for a second monoid drawn beside it, as the header explains.  `invert` is a
/// SEPARATE axis — it flips the page to light-on-dark for the complement region of diag/FO.lean — so
/// the two never collapse into one flag, and all four combinations are spelled out: a hollow dot on
/// a black page is black-filled with a white ring.  The fill is always opaque, so a wire cannot show
/// through a hollow dot and make it read as a crossing.
#let dot(p, hollow: false, invert: false) = {
  let ink = if invert { white } else { black }
  let paper = if invert { black } else { white }
  if hollow {
    d.circle(p, radius: Rh, fill: paper, stroke: (thickness: lw, paint: ink))
  } else {
    d.circle(p, radius: Rr, fill: ink, stroke: none)
  }
}

/// A labelled relation box; `p` is the midpoint of its LEFT edge.
///
/// NOT a rectangle: a rectangle is symmetric, and the box has to say which way the relation runs.
/// functorialSemanticsForRelationalTheories.pdf §4 chamfers the TOP-RIGHT corner and defines the
/// converse to be that same box MIRRORED, so `flip: true` is not a decoration: it is how the paper
/// writes `†`.
///
/// THE FRAME IS MIRRORED, THE LABEL IS NOT.  The paper can mirror its label because the label is a
/// single letter, and `Я` still reads as an R.  A label here is often a whole term — `R ∪ S` — and
/// mirrored it is unreadable, right to left with every glyph reversed.  The chamfer already says
/// which way the box runs, and `TINT` says it again, so the text has no work left to do.
///
/// `dashed` marks a box that is not a composite of the generators (the residual `R/S`, which needs
/// diag/FO.lean).
///
/// `fill` overrides the paper colour.  `TINT` is what a converse gets: mirroring alone tells `R`
/// from `R°` only if the reader looks at which corner is cut, and in a chain where a box crosses a
/// bend and comes back upright — the whole content of Lemma 4.2 — that has to be legible at a
/// glance.  Pale BLUE, not grey: grey reads as "disabled", and it would also collide with the
/// greyed-out prose this repo's notes use for provenance.  It is a hint, not a second kind of box.
// The chamfer is a MARK, not a shape: one size on every box.  Proportional to the height alone, a
// box tall enough to carry two ports has its top-right corner cut away past the upper port, and the
// wire then leaves from open air — so the cut is capped at what a default-height box gets.
#let CHAMFER = 0.35     // fraction of the height taken off the corner, up to CHAMFER * BH
#let TINT = rgb("#dbe8f7")
#let gbox(p, label, w: BW, h: BH, dashed: false, invert: false, flip: false, fill: none,
          chamfer: true) = {
  let (x, y) = p
  let paint = if invert { white } else { black }
  let paper = if fill != none { fill } else if invert { black } else { white }
  let st = if dashed { (thickness: lw, paint: paint, dash: "dashed") } else { (thickness: lw, paint: paint) }
  // `chamfer: false` is a MAP: a plain rectangle.  The cut corner exists to say which way a relation
  // runs, and a map runs one way by construction — there is nothing for the corner to disambiguate.
  // It also makes maps findable at a glance, which is what most of the calculational steps turn on.
  let c = if chamfer { calc.min(CHAMFER * h, CHAMFER * BH) } else { 0.0 }
  let pts = if flip {
    ((x, y - h / 2), (x + w, y - h / 2), (x + w, y + h / 2), (x + c, y + h / 2), (x, y + h / 2 - c))
  } else {
    ((x, y - h / 2), (x + w, y - h / 2), (x + w, y + h / 2 - c), (x + w - c, y + h / 2), (x, y + h / 2))
  }
  d.line(..pts, close: true, fill: paper, stroke: st)
  d.content((x + w / 2, y), text(fill: paint, label))
}

/// An annotation set to the right of a picture, left-aligned so it can never run back into it.
#let note(p, body) = d.content(p, text(8.5pt, body), anchor: "west")

// ------------------------------------------------------- division, drawn as long division
#let DIVNUM = rgb("#f6e3bd")    // the numerator's ground — amber, NOT a red: the tape is pale red
#let DIVDEN = rgb("#cfe6cd")    // the divisor laid inside it

/// `R / S`, drawn instead of spelled.  A chamfered box like any other relation — same outline, same
/// corner cut, so it wires up and says which way it runs — but its INTERIOR is the long-division
/// picture rather than the string `R / S`: the amber ground is the numerator `R`, the green tile
/// inset at the far end is the divisor `S` laid inside it, and the hairline of amber past the tile
/// is the slack that makes the cancel law `(R/S) S ⊑ R` an inclusion and not an equality.
///
/// The tile is DASHED and the frame is SOLID.  The frame is solid because this is an arrow of the
/// allegory like any other; the tile is dashed because `T S ⊑ R` pins nothing beyond it — which is
/// also why the slack is drawn as a sliver: `R / S` is the LARGEST quotient, so what is left when
/// nothing more can be taken is exactly a hairline.
///
/// `flip` mirrors both the chamfer and the tile, which is what left division needs: `S \ R` lays
/// the divisor down FIRST.  Transcribed, in the sense that matters — the interior is a metaphor for
/// the universal property, not a composite of the generators, and it is the one account of `/` in
/// this file that needs no complement.
#let divbox(p, num, den, w: 2.4, h: BH, denw: 0.72, slack: 0.09, flip: false, invert: false) = {
  let (x, y) = p
  let ink = if invert { white } else { black }
  let c = CHAMFER * h
  let pts = if flip {
    ((x, y - h / 2), (x + w, y - h / 2), (x + w, y + h / 2), (x + c, y + h / 2), (x, y + h / 2 - c))
  } else {
    ((x, y - h / 2), (x + w, y - h / 2), (x + w, y + h / 2 - c), (x + w - c, y + h / 2), (x, y + h / 2))
  }
  d.line(..pts, close: true, fill: DIVNUM, stroke: (thickness: lw, paint: ink))
  let ty = h / 2 - 0.11
  let t0 = if flip { x + slack } else { x + w - slack - denw }
  let t1 = t0 + denw
  d.rect((t0, y - ty), (t1, y + ty), fill: DIVDEN,
    stroke: (thickness: 0.9pt, paint: ink, dash: "dashed"))
  // The numerator sits in whatever the tile leaves, which is the other end of the box.
  let nx = if flip { (t1 + x + w) / 2 } else { (x + t0) / 2 }
  d.content((nx, y), text(9pt, fill: ink, num))
  d.content(((t0 + t1) / 2, y), text(8pt, fill: ink, den))
}

// ---------------------------------------------------- the four Frobenius generators

/// Copy `Δ : a → a ⊗ a` (`delta`).  In Rel, `x ↦ (x, x)`.  Pass `li: 0` to grow a copy tree with no
/// incoming stub of its own.
#let delta(p, li: 0.7, lo: 0.7, sp: 0.5, invert: false) = {
  let (x, y) = p
  if li > 0 { wire((x - li, y), p, invert: invert) }
  bend(p, (x + lo, y + sp), k: 0.6, invert: invert)
  bend(p, (x + lo, y - sp), k: 0.6, invert: invert)
  dot(p, invert: invert)
}

/// Merge `∇ : a ⊗ a → a` (`nabla`), the mirror of `delta`.  In Rel it is `Δ°`, so it forces the two
/// incoming strands to carry the same value — which is why `meet` below is an intersection.
#let nabla(p, li: 0.7, lo: 0.7, sp: 0.5, invert: false) = {
  let (x, y) = p
  bend((x - li, y + sp), p, k: 0.4, invert: invert)
  bend((x - li, y - sp), p, k: 0.4, invert: invert)
  if lo > 0 { wire(p, (x + lo, y), invert: invert) }
  dot(p, invert: invert)
}

/// Discard `! : a → I` (`bang`).  In Rel, the map to a point.
#let bang(p, li: 0.7, invert: false) = {
  wire((p.at(0) - li, p.at(1)), p, invert: invert)
  dot(p, invert: invert)
}

/// Unit `? : I → a` (`unitR`) — `!°`.  Told from `bang` by which side the wire leaves on.
#let unitR(p, lo: 0.7, invert: false) = {
  wire(p, (p.at(0) + lo, p.at(1)), invert: invert)
  dot(p, invert: invert)
}

/// The wire swap `σ`, a crossing of two strands.
#let swap(p, w: 0.55, sp: 0.33, invert: false) = {
  let (x, y) = p
  bend((x, y + sp), (x + w, y - sp), k: 0.5, invert: invert)
  bend((x, y - sp), (x + w, y + sp), k: 0.5, invert: invert)
}

// ------------------------------------------------------- compact-closed cup and cap

/// The stub between the two dots of a `split` cup or cap.
#let SPLIT = 0.34

/// The cap `a ⊗ a → I` (`∇ ; !`): the strands arriving at `p1` and `p2` converge on `tip`, to the
/// right, and are discarded there — so the picture says the two strands must agree.
///
/// `tip` is where `∇` and `!` coincide, and only one dot fits there; it is solid like every other
/// node, and a cap is told from a cup by which side its two strands are on.
///
/// `split: true` draws the two dots separately, `∇` at `tip` and `!` a stub to its right — which is
/// how functorialSemanticsForRelationalTheories.pdf draws the cap in the `†` definition figure, and
/// the collapse to one dot is a theorem rather than a notation.  Use it where the figure is quoting
/// that definition; the collapsed form everywhere else.
#let cap(p1, p2, tip, invert: false, split: false) = {
  d.bezier(p1, tip, (tip.at(0) - 0.15, p1.at(1)), stroke: wstroke(invert: invert))
  d.bezier(p2, tip, (tip.at(0) - 0.15, p2.at(1)), stroke: wstroke(invert: invert))
  dot(tip, invert: invert)
  if split {
    let (tx, ty) = tip
    wire(tip, (tx + SPLIT, ty), invert: invert)
    dot((tx + SPLIT, ty), invert: invert)
  }
}

/// The cup `I → a ⊗ a` (`? ; Δ`), the mirror of `cap`: one value is created at `tip` and leaves on
/// both strands.  Bending a wire with a cup and straightening it with a cap is what makes the
/// category compact closed (functorialSemanticsForRelationalTheories.pdf p. 19).
///
/// Its `tip` carries `Δ`; as with `cap`, one solid dot, and the strands say which of the two it is.
/// `split: true` puts `?` a stub to the LEFT of that `Δ`, the form the `†` definition figure uses.
#let cup(tip, p1, p2, invert: false, split: false) = {
  d.bezier(tip, p1, (tip.at(0) + 0.15, p1.at(1)), stroke: wstroke(invert: invert))
  d.bezier(tip, p2, (tip.at(0) + 0.15, p2.at(1)), stroke: wstroke(invert: invert))
  dot(tip, invert: invert)
  if split {
    let (tx, ty) = tip
    wire((tx - SPLIT, ty), tip, invert: invert)
    dot((tx - SPLIT, ty), invert: invert)
  }
}

/// `cap` and `cup` in the ONE-ANCHOR convention every other generator uses: `p` is the left edge on
/// the centre line and `sp` the strand offset, so `diag-export` can place them by walking an x grid
/// like any other cell.  `cap` consumes a pair on its left and offers nothing on its right; `cup`
/// is the mirror.
///
/// SPLIT BY DEFAULT, unlike bare `cup`/`cap`.  These are the forms that appear in pictures OF THE
/// CONVERSE, and functorialSemanticsForRelationalTheories.pdf draws the converse with two dots at
/// each bend — `? ; Δ` and `∇ ; !` — never one.  Collapsing them is a legitimate abbreviation
/// elsewhere; here it would make a quoted picture disagree with the paper it quotes.
#let capAt(p, sp: 0.62, w: 0.60, invert: false, split: true) = {
  let (x, y) = p
  cap((x, y + sp), (x, y - sp), (x + w, y), invert: invert, split: split)
}

#let cupAt(p, sp: 0.62, w: 0.60, invert: false, split: true) = {
  let (x, y) = p
  cup((x, y), (x + w, y + sp), (x + w, y - sp), invert: invert, split: split)
}

// ---------------------------------------------------------------------- the converse

/// THE FRAME a converse sits in, with the middle left empty — the third picture of the `†` notation
/// in functorialSemanticsForRelationalTheories.pdf ("we adopt the graphical notation",
/// `R† =def Я =def` …); `conv` in diag/CB.lean, proved equal to the ordinary relational converse by
/// `conv_eq_recip` in diag/RelSetCB.lean.  `p` is the left end of the INCOMING wire, on the bottom
/// strand.
///
/// Three levels, and it is the CUP and the CAP that make it a converse — a wire merely bumped up
/// over what it reverses and back down is an isotopy of that thing and reverses nothing.  Input
/// arrives bottom left and runs underneath; the cup at the top left creates a pair, one strand
/// feeding the middle and the other leaving as the output at the top right; the cap at the bottom
/// right annihilates the middle's output against the input.
///
/// EMPTY IN THE MIDDLE because what rides there is not always one box: `(R S)°` is two, `(R ∩ S)°`
/// is a whole meet, and `(R /ₛ S)°` is a dashed box.  `w` is the width of whatever does ride it,
/// `mid` the level it is entered at and `out` the level it leaves at — the two differ only when the
/// middle itself climbs, which is what a converse inside a converse does.  `conv-body` is where its
/// left edge goes; `diag-export` draws its own cells there, and `conv` below draws a single box.
#let CONVIN = 0.28 + SPLIT            // in from the left edge to the cup's `◁`
#let conv-body(p, rise: 1.6, mid: none, arc: 0.78) = (
  p.at(0) + CONVIN + arc, p.at(1) + (if mid == none { rise / 2 } else { mid }))

#let conv-frame(p, w: BW, rise: 1.6, mid: none, out: none, lead: 0.40, arc: 0.78, invert: false) = {
  let (x, y) = p
  let ym = y + (if mid == none { rise / 2 } else { mid })   // the level the middle is entered at
  let yo = y + (if out == none { rise / 2 } else { out })   // the level it leaves at
  let yt = y + rise                   // the outgoing strand
  let bx = x + CONVIN + arc           // the middle's left edge
  let cx = bx + w + arc               // the cap's tip, where `∇` sits
  cup((x + CONVIN, ym + 0.6 * (yt - ym)), (bx, yt), (bx, ym), split: true, invert: invert)
  wire((bx, yt), (cx + lead, yt), invert: invert)
  wire((x, y), (bx + w, y), invert: invert)
  cap((bx + w, yo), (bx + w, y), (cx, y + 0.4 * (yo - y)), split: true, invert: invert)
}

/// The converse of ONE BOX, which is the frame with that box on its middle strand.  What a note
/// draws by hand where there is no Lean statement to export from — the definition figures.
#let conv(p, label, w: BW, h: BH, rise: 1.6, lead: 0.40, arc: 0.78, invert: false) = {
  conv-frame(p, w: w, rise: rise, lead: lead, arc: arc, invert: invert)
  gbox(conv-body(p, rise: rise, arc: arc), label, w: w, h: h, invert: invert)
}

#let conv-w(w: BW, lead: 0.40, arc: 0.78) = CONVIN + 2 * arc + w + SPLIT + lead

// -------------------------------------------------------- convolution: the meet `∩`

/// The CONVOLUTION `Δ ; (R ⊗ S) ; ∇` — the meet `R ∩ S`
/// (functorialSemanticsForRelationalTheories.pdf p. 22, `convolution` in diag/CB_Derived.lean,
/// proved equal to the allegory intersection by `convolution_eq_inter` in diag/RelSetCB.lean).
/// Copy the input, run `R` on one strand and `S` on the other, merge; the merge forces the two
/// results to coincide, so the picture demands both.  `p` is the copy dot.
///
/// `flip` mirrors both boxes, which is how the whole picture reads when it is itself mirrored: `Δ`
/// and `∇` are each other's mirror image, so reflecting `R ∩ S` leaves the shape alone and only
/// turns the boxes round — the one-picture proof of `(R ∩ S)° = R° ∩ S°`.
#let meet(p, upper, lower, w: BW, h: BH, sp: 0.62, li: 0.4, lo: 0.4, gap: 0.3, flip: false) = {
  let (x, y) = p
  delta(p, li: li, lo: gap, sp: sp)
  gbox((x + gap, y + sp), upper, w: w, h: h, flip: flip)
  gbox((x + gap, y - sp), lower, w: w, h: h, flip: flip)
  nabla((x + 2 * gap + w, y), li: gap, lo: lo, sp: sp)
}

#let meet-w(w: BW, li: 0.4, lo: 0.4, gap: 0.3) = li + 2 * gap + w + lo

// ----------------------------------------------------------------- chains of boxes

/// The total width of `n` boxes wired in series, so callers can place what comes next.
#let chain-w(n, w: BW, lead: LEAD, gap: LEAD) = 2 * lead + n * w + calc.max(n - 1, 0) * gap

/// `— [a] — [b] — …` in series, i.e. the composite `a ; b ; …`; `p` is the left end of the leading
/// wire stub.  `dashed` lists the indices of boxes to draw dashed.
#let chain(p, labels, w: BW, h: BH, lead: LEAD, gap: LEAD, dashed: ()) = {
  let (x, y) = p
  wire((x, y), (x + lead, y))
  let cx = x + lead
  for (i, lab) in labels.enumerate() {
    gbox((cx, y), lab, w: w, h: h, dashed: dashed.contains(i))
    cx = cx + w
    if i + 1 < labels.len() {
      wire((cx, y), (cx + gap, y))
      cx = cx + gap
    }
  }
  wire((cx, y), (cx + lead, y))
}

/// `chain` with a WIDTH AND A SHAPE PER BOX: `items` is `((label, width, chamfer), …)`.  One shared
/// width cannot carry `list((R×R)choose)` and `R` on one strand, and one shared flag cannot say that
/// `concat` is a map while `list(choose)` is a relation — which is what the chamfer is there to say.
/// `h` is shared: a run whose labels are two lines tall — `R / ∋` written as a fraction — needs every
/// box in the run raised together, or the wire steps up and down between them.
#let boxrun-w(items) = if items.len() == 0 { 2 * LEAD } else {
  2 * LEAD + items.map(it => it.at(1)).sum() + (items.len() - 1) * LEAD
}
#let boxrun(x, y, items, h: BH) = {
  let cx = x + LEAD
  wire((x, y), (cx, y))
  for (i, it) in items.enumerate() {
    gbox((cx, y), it.at(0), w: it.at(1), h: h, chamfer: it.at(2))
    cx = cx + it.at(1)
    if i + 1 < items.len() { wire((cx, y), (cx + LEAD, y)); cx = cx + LEAD }
  }
  wire((cx, y), (cx + LEAD, y))
}

// --------------------------------------------- tapes: the second product (phase 8)

/// The rounded wrapper of a tape (TapeDiagrams.pdf Fig. 1).  A whole circuit is drawn inside it;
/// the tape is the second monoidal product, which is what carries `∪`.
#let tape(a, b, radius: 0.14) = d.rect(a, b, radius: radius, fill: TAPEFILL,
  stroke: (thickness: 0.8pt, paint: TAPEEDGE))

/// The fork `▷` that opens a tape into two branches; a particle takes exactly one of them.
#let tape-fork(p, sp: 0.7, len: 0.5) = {
  let (x, y) = p
  let st = (thickness: 1.4pt, paint: TAPEEDGE)
  d.bezier(p, (x + len, y + sp), (x + len * 0.6, y), (x + len * 0.6, y + sp), stroke: st)
  d.bezier(p, (x + len, y - sp), (x + len * 0.6, y), (x + len * 0.6, y - sp), stroke: st)
}

/// The join `◁` that closes the two branches of a tape.
#let tape-join(p, sp: 0.7, len: 0.5) = {
  let (x, y) = p
  let st = (thickness: 1.4pt, paint: TAPEEDGE)
  d.bezier((x - len, y + sp), p, (x - len * 0.6, y + sp), (x - len * 0.6, y), stroke: st)
  d.bezier((x - len, y - sp), p, (x - len * 0.6, y - sp), (x - len * 0.6, y), stroke: st)
}

// ----------------------------------------- cuts: complement as colour switch (phase 9)

/// Peirce's cut — the colour-switch region that carries complement
/// (DiagrammaticAlgebraOfFirstOrderLogic.pdf §5).  Draw the region, then draw its contents with
/// `invert: true` so wires, dots and boxes come out white on black.
///
/// The paper's own words, p. 2: "given `c`, take its mirror image `c` and then its photographic
/// negative `c`" — that is `c⊥`; and p. 10, on translating Peirce's existential graphs, "each cut
/// [is] a color switch".  So a cut is not a frame drawn AROUND a picture, it is the picture drawn on
/// the other colour, and `R / S` is a black region rather than a box labelled `R / S`.
///
/// `invert` is what makes cuts NEST: a cut inside a cut switches back to white, which is Peirce's
/// double cut, and `∼∼R = R` is that pair of regions cancelling.  Same axis as everywhere else in
/// this file — `invert` always means "the ground under this is black".
#let cut(a, b, radius: 0.1, invert: false) = d.rect(
  a, b, radius: radius, fill: if invert { white } else { black }, stroke: none)
