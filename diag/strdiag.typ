// strdiag.typ — string-diagram primitives for the Rel(Set) calculus.  cetz 0.3.4.
//
// Reading conventions, as in diag/S2_124.typ and
// functorialSemanticsForRelationalTheories.pdf §2 (p. 7):
//
//   left to right   composition `;` — the book's diagram order, `x y` = first x then y
//   vertical stack  the monoidal product
//   solid dots      the COMONOID `(Δ, !)` — copy and discard
//   hollow dots     the MONOID `(∇, ?)` — merge and create
//   white boxes     relations; a bare wire is the identity
//
// The fill convention is the paper's, not ours: functorialSemanticsForRelationalTheories.pdf p. 8,
// Example 2.3 draws the monoid's multiplication and unit hollow (a) and the comonoid's
// comultiplication and counit solid (b), and eqs. (13)–(16) put both in one picture, where the fill
// is the only thing telling them apart.  It earns its keep here too: in the Frobenius equation and
// in both snakes, `Δ` and `∇` sit adjacent, and without the fill you must trace wire direction to
// see which is which.
//
// PROVENANCE.  The drawing code here was extracted from diag/S2_124.typ, the repo's own
// hand-authored string-diagram proof of §2.124, which now imports this file instead of keeping
// private copies.  Line weight, dot radius, bezier control fractions and the default stub lengths
// are its values unchanged, so its rendered PDF is unaffected.
//
// ONE VOCABULARY.  The generators are named after Freyd/S2_124.lean, which proves `Rel` is a model
// of exactly this calculus, so a picture and its Lean statement use the same word:
//
//   delta  Δ : a → a ⊗ a     nabla  ∇ : a ⊗ a → a     cap  : a ⊗ a → I     swap  σ
//   bang   ! : a → I         unitR  ? : I → a         cup  : I → a ⊗ a
//
// functorialSemanticsForRelationalTheories.pdf calls the same four `Δ`, `!`, `∇`, `?` (Def. 4.1)
// and diag/CB.lean fields them as `cop`, `dis`, `mer`, `un`.
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
#let Rr = 0.07          // solid (comonoid) dot radius   (S2_124.typ)
#let Rh = 0.088         // hollow (monoid) dot radius — larger, or the ring closes up at `lw`
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
#let bend(a, b, k: 0.6, invert: false) = {
  let (ax, ay) = a
  let (bx, by) = b
  let mx = ax + (bx - ax) * k
  d.bezier(a, b, (mx, ay), (mx, by), stroke: wstroke(invert: invert))
}

/// One node of the Frobenius structure.  `hollow` selects monoid (`∇`, `?`) over comonoid (`Δ`,
/// `!`), per the fill convention in the header.  `invert` is a SEPARATE axis — it flips the page to
/// light-on-dark for the complement region of diag/FO.lean — so the two never collapse into one
/// flag, and all four combinations are spelled out: a hollow dot on a black page is black-filled
/// with a white ring.  The fill is always opaque, so a wire cannot show through a hollow dot and
/// make it read as a crossing.
#let dot(p, hollow: false, invert: false) = {
  let ink = if invert { white } else { black }
  let paper = if invert { black } else { white }
  if hollow {
    d.circle(p, radius: Rh, fill: paper, stroke: (thickness: lw, paint: ink))
  } else {
    d.circle(p, radius: Rr, fill: ink, stroke: none)
  }
}

/// A labelled relation box; `p` is the midpoint of its LEFT edge.  `dashed` marks a box that is not
/// a composite of the generators (the residual `R/S`, which needs diag/FO.lean).
#let gbox(p, label, w: BW, h: BH, dashed: false, invert: false) = {
  let (x, y) = p
  let paint = if invert { white } else { black }
  let st = if dashed { (thickness: lw, paint: paint, dash: "dashed") } else { (thickness: lw, paint: paint) }
  d.rect((x, y - h / 2), (x + w, y + h / 2), fill: if invert { black } else { white }, stroke: st)
  d.content((x + w / 2, y), text(fill: paint, label))
}

/// An annotation set to the right of a picture, left-aligned so it can never run back into it.
#let note(p, body) = d.content(p, text(8.5pt, body), anchor: "west")

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
  dot(p, hollow: true, invert: invert)
}

/// Discard `! : a → I` (`bang`).  In Rel, the map to a point.
#let bang(p, li: 0.7, invert: false) = {
  wire((p.at(0) - li, p.at(1)), p, invert: invert)
  dot(p, invert: invert)
}

/// Unit `? : I → a` (`unitR`) — `!°`.
#let unitR(p, lo: 0.7, invert: false) = {
  wire(p, (p.at(0) + lo, p.at(1)), invert: invert)
  dot(p, hollow: true, invert: invert)
}

/// The wire swap `σ`, a crossing of two strands.
#let swap(p, w: 0.55, sp: 0.33, invert: false) = {
  let (x, y) = p
  bend((x, y + sp), (x + w, y - sp), k: 0.5, invert: invert)
  bend((x, y - sp), (x + w, y + sp), k: 0.5, invert: invert)
}

// ------------------------------------------------------- compact-closed cup and cap

/// The cap `a ⊗ a → I` (`∇ ; !`): the strands arriving at `p1` and `p2` converge on `tip`, to the
/// right, and are discarded there — so the picture says the two strands must agree.
///
/// `tip` is where `∇` and `!` coincide, and only one dot fits there.  It is drawn as the BINARY
/// generator — hollow, for the merge — because the merge is what the picture is asserting; the
/// unary `!` that follows it has no strand of its own to show.  `cup` makes the mirror choice, so
/// the two are told apart by fill rather than by which way the strands bend.
#let cap(p1, p2, tip, invert: false) = {
  d.bezier(p1, tip, (tip.at(0) - 0.15, p1.at(1)), stroke: wstroke(invert: invert))
  d.bezier(p2, tip, (tip.at(0) - 0.15, p2.at(1)), stroke: wstroke(invert: invert))
  dot(tip, hollow: true, invert: invert)
}

/// The cup `I → a ⊗ a` (`? ; Δ`), the mirror of `cap`: one value is created at `tip` and leaves on
/// both strands.  Bending a wire with a cup and straightening it with a cap is what makes the
/// category compact closed (functorialSemanticsForRelationalTheories.pdf p. 19).
///
/// By the rule stated on `cap`, `tip` shows the binary generator — here `Δ`, so solid.  A cup and a
/// cap are therefore never confusable even where the bend direction is hard to read.
#let cup(tip, p1, p2, invert: false) = {
  d.bezier(tip, p1, (tip.at(0) + 0.15, p1.at(1)), stroke: wstroke(invert: invert))
  d.bezier(tip, p2, (tip.at(0) + 0.15, p2.at(1)), stroke: wstroke(invert: invert))
  dot(tip, invert: invert)
}

// ---------------------------------------------------------------------- the converse

/// The converse `R°` drawn as its definition: bend both of `R`'s wires around, so what was an input
/// is read as an output (functorialSemanticsForRelationalTheories.pdf p. 19; `conv` in
/// diag/CB.lean, proved equal to the ordinary relational converse by `conv_eq_recip` in
/// diag/RelSetCB.lean).  `p` is the left end of the incoming wire, on the lower strand.
#let conv(p, label, w: BW, h: BH, rise: 0.85, lead: 0.45, arc: 0.75) = {
  let (x, y) = p
  let by = y + rise
  wire(p, (x + lead, y))
  bend((x + lead, y), (x + lead + arc, by), k: 0.5)
  gbox((x + lead + arc, by), label, w: w, h: h)
  bend((x + lead + arc + w, by), (x + lead + 2 * arc + w, y), k: 0.5)
  wire((x + lead + 2 * arc + w, y), (x + 2 * lead + 2 * arc + w, y))
}

#let conv-w(w: BW, lead: 0.45, arc: 0.75) = 2 * lead + 2 * arc + w

// -------------------------------------------------------- convolution: the meet `∩`

/// The CONVOLUTION `Δ ; (R ⊗ S) ; ∇` — the meet `R ∩ S`
/// (functorialSemanticsForRelationalTheories.pdf p. 22, `convolution` in diag/CB_Derived.lean,
/// proved equal to the allegory intersection by `convolution_eq_inter` in diag/RelSetCB.lean).
/// Copy the input, run `R` on one strand and `S` on the other, merge; the merge forces the two
/// results to coincide, so the picture demands both.  `p` is the copy dot.
#let meet(p, upper, lower, w: BW, h: BH, sp: 0.62, li: 0.4, lo: 0.4, gap: 0.3) = {
  let (x, y) = p
  delta(p, li: li, lo: gap, sp: sp)
  gbox((x + gap, y + sp), upper, w: w, h: h)
  gbox((x + gap, y - sp), lower, w: w, h: h)
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
#let cut(a, b, radius: 0.1) = d.rect(a, b, radius: radius, fill: black, stroke: none)
