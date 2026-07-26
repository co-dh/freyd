// strdiag.typ — string-diagram primitives for the Rel(Set) calculus.  cetz 0.3.4.
//
// Reading conventions, from functorialSemanticsForRelationalTheories.pdf §2 (p. 7):
//
//   left to right   composition `;`  — the book's diagram order, `x y` = first x then y
//   vertical stack  the monoidal product
//   black dots      the Frobenius structure: copy Δ, discard !, merge ∇, unit ?
//   white boxes     relation generators; a wire is the identity
//
// Every function takes its anchor `p` as the LEFT edge of what it draws, on the wire it sits on,
// so a picture is laid out by walking an x grid rightwards.  Dots are one size everywhere (DOTR)
// because they are one algebraic structure; box width and height are one size (BW, BH) so that
// stacked strands line up without per-call tuning.
//
// The wire/gbox/copy/merge/discard/unit drawing code was salvaged from the repo-root file
// AllegoryStringDiagrams.typ.  That file is an AI-written cheatsheet and is NOT a source: cite
// functorialSemanticsForRelationalTheories.pdf for every mathematical claim.

#import "@preview/cetz:0.3.4"
#let d = cetz.draw

// ---------------------------------------------------------------- style constants
#let W = 1.0pt          // wire thickness
#let DOTR = 0.075       // Frobenius dot radius
#let BW = 0.92          // default box width
#let BH = 0.60          // default box height
#let LEAD = 0.34        // wire stub before the first box and after the last
#let TAPEFILL = rgb("#f6cfcf")
#let TAPEEDGE = rgb("#c25b5b")

#let wstroke(invert: false) = (thickness: W, paint: if invert { white } else { black })

// ---------------------------------------------------------------- wires and boxes

/// A straight wire from `a` to `b`.
#let wire(a, b, invert: false) = d.line(a, b, stroke: wstroke(invert: invert))

/// A wire from `a` to `b` that leaves and arrives horizontally — the shape every fork, cup and
/// cap is built from, so that strands meet boxes and dots at right angles.
#let bend(a, b, invert: false) = {
  let (ax, ay) = a
  let (bx, by) = b
  let mx = ax + (bx - ax) * 0.55
  d.bezier(a, b, (mx, ay), (mx, by), stroke: wstroke(invert: invert))
}

/// One node of the Frobenius structure.
#let dot(p, invert: false) = d.circle(p, radius: DOTR, fill: if invert { white } else { black },
  stroke: none)

/// A labelled generator box; `p` is the midpoint of its LEFT edge.  `dashed` marks a box that is
/// not a composite of the generators (the residual `R/S`, which needs diag/FO.lean).
#let gbox(p, label, w: BW, h: BH, dashed: false, invert: false) = {
  let (x, y) = p
  let paint = if invert { white } else { black }
  let st = if dashed { (thickness: W, paint: paint, dash: "dashed") } else { (thickness: W, paint: paint) }
  d.rect((x, y - h / 2), (x + w, y + h / 2), fill: if invert { black } else { white }, stroke: st)
  d.content((x + w / 2, y), text(fill: paint, label))
}

// ---------------------------------------------------- the four Frobenius generators

/// Copy `Δ : n → n ⊗ n` (Def. 4.1.1).  In Rel, `x ↦ (x, x)`.
#let copy(p, li: 0.5, lo: 0.5, sp: 0.5, invert: false) = {
  let (x, y) = p
  if li > 0 { wire((x - li, y), p, invert: invert) }
  bend(p, (x + lo, y + sp), invert: invert)
  bend(p, (x + lo, y - sp), invert: invert)
  dot(p, invert: invert)
}

/// Merge `∇ : n ⊗ n → n` (Def. 4.1.2), the mirror of `copy`.  In Rel it is `Δ†`, so it forces the
/// two incoming strands to carry the same value — which is why `meet` below is an intersection.
#let merge(p, li: 0.5, lo: 0.5, sp: 0.5, invert: false) = {
  let (x, y) = p
  bend((x - li, y + sp), p, invert: invert)
  bend((x - li, y - sp), p, invert: invert)
  if lo > 0 { wire(p, (x + lo, y), invert: invert) }
  dot(p, invert: invert)
}

/// Discard `! : n → I` (Def. 4.1.1).  In Rel, the map to a point.
#let discard(p, li: 0.6, invert: false) = {
  wire((p.at(0) - li, p.at(1)), p, invert: invert)
  dot(p, invert: invert)
}

/// Unit `? : I → n` (Def. 4.1.2) — `!†`.
#let unit(p, lo: 0.6, invert: false) = {
  wire(p, (p.at(0) + lo, p.at(1)), invert: invert)
  dot(p, invert: invert)
}

// ------------------------------------------------------- compact-closed cup and cap

/// The cup `I → n ⊗ n`; `p` is its apex, at the left.  As a term it is `? ; Δ`, but the Frobenius
/// equations collapse those two dots (functorialSemanticsForRelationalTheories.pdf p. 19), so it
/// is drawn as the bare bent wire it is equal to.
#let cup(p, len: 0.55, sp: 0.5, invert: false) = {
  let (x, y) = p
  bend(p, (x + len, y + sp), invert: invert)
  bend(p, (x + len, y - sp), invert: invert)
}

/// The cap `n ⊗ n → I` (`∇ ; !`); `p` is its apex, at the right.
#let cap(p, len: 0.55, sp: 0.5, invert: false) = {
  let (x, y) = p
  bend((x - len, y + sp), p, invert: invert)
  bend((x - len, y - sp), p, invert: invert)
}

// ---------------------------------------------------------------------- the converse

/// The converse `R†` — Freyd's `R°` — drawn as its definition: bend both of `R`'s wires around,
/// so what was an input is read as an output (functorialSemanticsForRelationalTheories.pdf p. 19,
/// `conv` in diag/CB.lean).  `p` is the left end of the incoming wire, on the lower strand; the
/// box sits `rise` above it.
#let conv(p, label, w: BW, h: BH, rise: 0.85, lead: 0.45, arc: 0.75) = {
  let (x, y) = p
  let by = y + rise
  wire(p, (x + lead, y))
  bend((x + lead, y), (x + lead + arc, by))
  gbox((x + lead + arc, by), label, w: w, h: h)
  bend((x + lead + arc + w, by), (x + lead + 2 * arc + w, y))
  wire((x + lead + 2 * arc + w, y), (x + 2 * lead + 2 * arc + w, y))
}

#let conv-w(w: BW, lead: 0.45, arc: 0.75) = 2 * lead + 2 * arc + w

/// An annotation set to the right of a picture, left-aligned so it can never run back into it.
#let note(p, body) = d.content(p, text(8.5pt, body), anchor: "west")

// -------------------------------------------------------- convolution: the meet `∩`

/// The CONVOLUTION `Δ ; (R ⊗ S) ; ∇` — the meet `R ∩ S`
/// (functorialSemanticsForRelationalTheories.pdf p. 22, `convolution` in diag/CB_Derived.lean).
/// Copy the input, run `R` on one strand and `S` on the other, merge; the merge forces the two
/// results to coincide, so the picture demands both.  `p` is the copy dot.
#let meet(p, upper, lower, w: BW, h: BH, sp: 0.62, li: 0.4, lo: 0.4, gap: 0.3) = {
  let (x, y) = p
  copy(p, li: li, lo: gap, sp: sp)
  gbox((x + gap, y + sp), upper, w: w, h: h)
  gbox((x + gap, y - sp), lower, w: w, h: h)
  merge((x + 2 * gap + w, y), li: gap, lo: lo, sp: sp)
}

#let meet-w(w: BW, li: 0.4, lo: 0.4, gap: 0.3) = li + 2 * gap + w + lo

// ----------------------------------------------------------------- chains of boxes

/// The total width of `n` boxes wired in series, so callers can place what comes next.
#let chain-w(n, w: BW, lead: LEAD, gap: LEAD) = 2 * lead + n * w + calc.max(n - 1, 0) * gap

/// `— [a] — [b] — …` in series, i.e. the composite `a ; b ; …`; `p` is the left end of the
/// leading wire stub.  `dashed` lists the indices of boxes to draw dashed.
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
  d.bezier(p, (x + len, y + sp), (x + len * 0.55, y), (x + len * 0.55, y + sp), stroke: st)
  d.bezier(p, (x + len, y - sp), (x + len * 0.55, y), (x + len * 0.55, y - sp), stroke: st)
}

/// The join `◁` that closes the two branches of a tape.
#let tape-join(p, sp: 0.7, len: 0.5) = {
  let (x, y) = p
  let st = (thickness: 1.4pt, paint: TAPEEDGE)
  d.bezier((x - len, y + sp), p, (x - len * 0.55, y + sp), (x - len * 0.55, y), stroke: st)
  d.bezier((x - len, y - sp), p, (x - len * 0.55, y - sp), (x - len * 0.55, y), stroke: st)
}

// ----------------------------------------- cuts: complement as colour switch (phase 9)

/// Peirce's cut — the colour-switch region that carries complement
/// (DiagrammaticAlgebraOfFirstOrderLogic.pdf §5).  Draw the region, then draw its contents with
/// `invert: true` so wires, dots and boxes come out white on black.
#let cut(a, b, radius: 0.1) = d.rect(a, b, radius: radius, fill: black, stroke: none)
