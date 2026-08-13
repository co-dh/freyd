// notation_as_a_tool_of_thought_adjunction.typ — the author's plain-text note, typeset.
//
// The subject of the note IS the notation, so the page draws what the text asks for:
//   * `a <= b` is a little box of two rows, `a` over `b` — but only from the item that introduces
//     it onward.  The lines above that item keep the ordinary `<=`, because the change of notation
//     is the whole point of the note and it has to be visible where it happens.
//   * a run of `/` and `\` is DRAWN as one connected wire, not set in a font: `/` climbs, `\`
//     falls, and neighbours share an endpoint, so `/\` closes into a peak and `\/` into a valley.
//     No font joins two slashes, and the joins are what the last line of the note is about.
//   * a law carries its name where an equation number would go — `adj` at the right of a displayed
//     law, `unit`/`counit` under a box inside a chain — and the same name in braces, `{adj}`, is
//     the reason written on every arrow that uses it.  The braces are the author's own `={…}=>`,
//     so every arrow's reason wears them.
// The wording is the author's; only the misspellings the author asked to have corrected are.

#import "@preview/dvdtyp:1.0.1": dvdtyp
#show: dvdtyp.with(title: "Notation as a Tool of Thought - Adjunction", author: none)
// Justification stretches the spaces of a cell that holds one long sentence into visible rivers.
#show table: set par(justify: false)

/// The colour of a numbered generator: `/1` is drawn in the first colour, `/2` in the second.  A
/// bare `/` is 0 and stays black — most of the note has one `S` and nothing to tell apart.
#let pal = (black, rgb("1565c0"), rgb("e65100"), rgb("2e7d32"))

/// A run of generators as one polyline: `/` climbs a level, `\` falls one, and the run is drawn
/// from the top of its own range downwards.  A word that alternates, `/\/`, zigzags between two
/// levels; `T//` climbs two, because `T`, `T S₁` and `T S₁ S₂` are three different hom-sets and the
/// height is which one you are in.  One `line` per generator rather than one path for the run, so
/// that each can carry its own colour; they share their endpoints, so the run still reads as one
/// wire.  `box` because the lines are `place`d and something has to give them a size.
#let wire(cs) = {
  let u = 0.44                                     // one generator's width, in em
  let ht = 0.72                                    // the distance between two levels
  let gap = 0.10                                   // the break at a joint that does not bend
  let (x, l, xs, ls) = (0, 0, (0,), (0,))
  for (d, col, sp) in cs { x += u * sp; l += d * sp; xs.push(x); ls.push(l) }
  let hi = calc.max(..ls)                          // `top` would shadow the alignment of that name
  let pt(i) = (xs.at(i), hi - ls.at(i))
  box(width: x * 1em, height: (hi - calc.min(..ls)) * 1em,
    cs.enumerate().map(((i, c)) => {
      let (p, q) = (pt(i), pt(i + 1))
      // A bend is its own mark, but two strokes in a line are one straight stick unless the joint
      // is opened: `R\\` has to be two arrows and not the single arrow `R/(S₁S₂)` divides by.
      let (dx, dy) = (q.at(0) - p.at(0), q.at(1) - p.at(1))
      let n = calc.sqrt(dx * dx + dy * dy)
      let (ux, uy) = (dx / n * gap / 2, dy / n * gap / 2)
      if i > 0 and cs.at(i - 1).at(0) == c.at(0) { p = (p.at(0) + ux, p.at(1) + uy) }
      if i + 1 < cs.len() and cs.at(i + 1).at(0) == c.at(0) { q = (q.at(0) - ux, q.at(1) - uy) }
      place(top + left, line(
        start: (p.at(0) * 1em, p.at(1) * 1em), end: (q.at(0) * 1em, q.at(1) * 1em),
        stroke: (paint: pal.at(c.at(1)), thickness: 0.07em, cap: "round")))
    }).join())
}

/// A word of the calculus, e.g. `X/\`: the generators drawn as wires, everything else typeset.
/// Consecutive generators go into ONE `wire` call — that is what connects them.  A digit right
/// after a generator is not a letter of the word, it numbers that generator: `T/1/2` is `T S₁ S₂`.
/// A `+` lengthens the generator by a level instead: `R\+` is `R` divided by ONE arrow that spans
/// two, which is the same line as `R\\` and the reason the theorem below is worth stating.
#let w(s) = {
  let out = ()
  let run = ()
  for c in s.clusters() {
    if c == "/" or c == "\\" { run.push((if c == "/" { 1 } else { -1 }, 0, 1)) }
    else if run.len() > 0 and c.match(regex("^[0-9]$")) != none {
      let s = run.pop(); run.push((s.at(0), int(c), s.at(2)))
    } else if run.len() > 0 and c == "+" {
      let s = run.pop(); run.push((s.at(0), s.at(1), s.at(2) + 1))
    } else {
      if run.len() > 0 { out.push(wire(run)); run = () }
      // `∗` is drawn up at the math axis; alone in a row it needs pushing down to look centred.
      out.push(if c == "*" { move(dy: 0.16em, $*$) } else { $italic(#c)$ })
    }
  }
  if run.len() > 0 { out.push(wire(run)) }
  box(out.join(h(0.1em)))
}

/// The name of a law, and the reason written on an arrow: the same thing said twice, so it is set
/// the same way both times.
#let hint(body) = text(0.8em, luma(95), body)

/// `a <= b`, as the note asks for it: a little box of two rows, a over b.
/// `baseline: 50%` centres it on the line it sits in; the default (bottom) would hang the whole box
/// off the baseline.  `name` is `place`d so it does not count towards the box's height: a chain is
/// centred on the horizon, and a name that measured would lift its own box above its neighbours.
#let sq(a, b, name: none) = box(
  stroke: 0.6pt + luma(120), fill: luma(253), radius: 2pt, inset: (x: 6pt, y: 4pt), baseline: 50%,
  {
    if name != none { place(bottom + center, dy: 1.15em, hint(name)) }
    grid(columns: 1, align: center, row-gutter: 4pt,
         w(a), grid.hline(y: 1, stroke: 0.4pt + luma(185)), w(b))
  },
)

/// A step of a derivation, with the reason on the operator.  The operator is stretched to the width
/// of the reason, so the two read as one gesture instead of a hint parked beside a short `⟹`.
#let step(reason, op: sym.arrow.r.double) = context {
  let r = hint[{#reason}]
  grid(columns: 1, align: center, row-gutter: 2pt,
       r, $stretch(#op, size: #measure(r).width)$)
}

/// A named law: the boxes and operators on one line, centred, with the name out at the right where
/// an equation number would go.  The empty `1fr` on the left keeps the law itself centred on the
/// page rather than on what is left of it once the name is placed.
#let named(name, ..items) = block(width: 100%, inset: (y: 5pt), grid(
  columns: (1fr, auto, 1fr), align: horizon,
  [],
  grid(columns: items.pos().len(), align: horizon, column-gutter: 10pt, ..items.pos()),
  align(right, hint(name)),
))

/// A derivation: one shared chain, then two one-step branches off its last box.  `align: horizon`
/// keeps the chain on a single line whatever the branches do — the chain's cells span both rows,
/// so the branch below cannot drag it up or down.
#let deriv(chain, branches) = align(center, block(inset: (y: 5pt), grid(
  columns: chain.len() + 2, align: horizon, column-gutter: 10pt, row-gutter: 10pt,
  ..chain.map(c => grid.cell(rowspan: 2, c)),
  ..branches.map(b => (step(b.at(0)), b.at(1))).flatten(),
)))

Adjunction: $F(x) <= y$ iff $x <= G(y)$, given $F$, $G$ monotonic.

$ F(x) <= F(x) quad &==> quad x <= G(F(x)) quad &&==> quad F(x) <= F(G(F(x))) \
  G(y) <= G(y) quad &==> quad F(G(y)) <= y quad &&==> quad G(F(G(y))) <= G(y) $

// Numbered so a derivation can cite one; only the item a derivation does cite carries a name.
#table(
  columns: (auto, 1fr, auto),
  stroke: (x: none, y: 0.4pt + luma(215)),
  inset: (x: 6pt, y: 7pt),
  align: (right + horizon, left + horizon, right + horizon),
  [1], [there are both function application and composition above, we can get rid of application
        by replacing $x$ with constant function $X: * -> x$ . $F(x) = F dot.op X$], [],
  [2], [use diagram order $F dot.op X ==> X F$], [],
  [3], [replace $F$ with #w("/") , $G$ with #w("\\")], [],
  [4], [put $a <= b$ as a over b. #h(0.8em) #sq("a", "b")], [],
  [5], [change from $X <= X F$ to $1 <= F$], hint("rewrite"),
)

#named("adj", sq("X/", "Y"), $=$, sq("X", "Y\\"))
#named("ladj", sq("\\X", "Y"), $=$, sq("X", "/Y"))

#deriv(
  (sq("X/", "X/"), step[adj], sq("X", "X/\\"), step("rewrite", op: sym.eq),
   sq("*", "/\\", name: "unit")),
  (
    ([put #w("\\") on left],  sq("\\", "\\/\\")),
    ([put #w("/") on right],  sq("/", "/\\/")),
  ),
)

#deriv(
  (sq("Y\\", "Y\\"), step[adj], sq("Y\\/", "Y"), step("rewrite", op: sym.eq),
   sq("\\/", "*", name: "counit")),
  (
    ([put #w("/") on left],   sq("/\\/", "/")),
    ([put #w("\\") on right], sq("\\/\\", "\\")),
  ),
)

now we have #w("/\\/") $=$ #w("/") and #w("\\/\\") $=$ #w("\\"), and you just discovered string
diagrams.

// Bound rather than written inline: diag/divproof.typ imports it to make the standalone PNG, and a
// second copy of the chain there would be a second chance to get it wrong.
#let divchain = align(center, grid(
  columns: 7, align: center + horizon, column-gutter: 12pt, row-gutter: 7pt,
  sq("T", "R\\+"), step("adj", op: sym.eq),
  sq("T/1/2", "R"), step("adj", op: sym.eq), sq("T/1", "R\\2"), step("adj", op: sym.eq),
  sq("T", "R\\2\\1"),
  hint[$T <= R\/(S_1 S_2)$], [], hint[$T S_1 S_2 <= R$], [], hint[$T S_1 <= R\/S_2$], [],
  hint[$T <= (R\/S_2)\/S_1$],
))

#pagebreak(weak: true)
= Division

$R S <= T$ iff $R <= T\/S$ is the same law, with #w("/") $= • S$ and #w("\\") $= • \/S$.

== $R\/(S_1 S_2) = (R\/S_2)\/S_1$

Take two, #w("/1") $= S_1$ and #w("/2") $= S_2$. Each one climbs a level — $T$, $T S_1$ and
$T S_1 S_2$ are three different hom-sets — so the composite is one stick twice as long, and `adj`
walks the two down one at a time:

#divchain

The left box is also $T <= R\/(S_1 S_2)$: one arrow or two, the wire is the same. So both right-hand
sides hold of exactly the same $T$, and $R\/(S_1 S_2) = (R\/S_2)\/S_1$.

== $f (R\/S) = (f R)\/S$

`ladj` with #w("/3") $= f$ and #w("\\3") $= f°$ — a map is a left adjoint, so it moves at the left
end. Crossing the bar turns #w("/") into #w("\\") either way; at the right end the stroke travels
down, at the left end up, and it never changes ends. #hint[The other reading, $f X <= Y$ iff
$X <= f° Y$, would need $1 <= f° f$ — $f$ surjective.]

#align(center, grid(
  columns: 9, align: center + horizon, column-gutter: 10pt, row-gutter: 7pt,
  sq("T", "/3R\\1"), step("ladj", op: sym.eq), sq("\\3T", "R\\1"), step("adj", op: sym.eq),
  sq("\\3T/1", "R"), step("ladj", op: sym.eq), sq("T/1", "/3R"), step("adj", op: sym.eq),
  sq("T", "/3R\\1"),
  hint[$T <= f(R\/S)$], [], hint[$f°T <= R\/S$], [], hint[$f°T S <= R$], [], hint[$T S <= f R$], [],
  hint[$T <= (f R)\/S$],
))

The two ends are one picture read with the brackets in the two places they can go, and they hold of
the same $T$. Hence $f(R\/S) = (f R)\/S$.
