// Shared by every Bird & de Moor chapter sheet (AOP/ch5, AOP/ch6, …): the page shapes come from
// the Freyd note's style.typ, and everything below is what the B&dM mirror adds on top of it —
// the notation helpers and the Conventions section, which must read identically on every sheet.
// Imported, not #included: `#include` evaluates a file's CONTENT, so the `#let`s would not travel.
#import "/Freyd/note/cheatsheet/style.typ": *

// The book's ⧺ (list concatenation), which appears in the pointwise glosses, where application
// order is the book's and nothing flips.
#let cc = math.class("binary", "⧺")
// ∼ is classed as a relation, so `∼C` sets with a gap; force operand class, as style.typ does for ∋.
#let tld = math.class("normal", sym.tilde.op)
// style.typ's heading rule breaks the page (or column) at EVERY heading, which is right for a book
// section and wrong for a group inside one.  So the groups are not headings.
#let sub(t) = block(above: 1.0em, below: 0.5em, text(weight: "bold", fill: accent, t))
// B&dM's own layout for a calculation: an expression, then the step's relation and its hint, then
// the next expression.  `deriv($X$, ("=", [why]), $Y$, …)` — a bare item is a line, a pair is a
// step.  Named `deriv`, not `calc`: `calc` is a Typst module.
#let deriv(..items) = block(inset: (y: 3pt), table(
  columns: (auto, 1fr), stroke: none, inset: (x: 5pt, y: 1.6pt),
  align: (right + horizon, left + horizon),
  ..items.pos().map(it => if type(it) == array { ([#it.at(0)], text(fill: dimc, size: 0.92em)[#it.at(1)]) }
    else { ([], it) }).flatten()
))

#let conventions = [
= Conventions

Composition is JUXTAPOSITION in diagram order: $R S$ = "first $R$, then $S$".  Objects
$alpha, beta, gamma$; relations $Q,R,S,T,U,V,X,Y$; *maps* (entire and simple) $f,g,h,k,m$;
coreflexives $C subset 1$.  $R^degree$ converse, $subset$ containment, $inter, union$
meet/join, $minus$ subtraction, $nothing$ empty, $Pi$ largest, $1$ identity, $"dom", "ran"$.
$[alpha]$ power object, $eps : [alpha] -> alpha$ membership, $Lambda$ the power transpose
($f = Lambda R <==> f eps = R$), $tau = Lambda 1$ singleton, $union.big = E eps$ union,
$E R = Lambda(eps R)$ existential image.  $F, G$ relators; $sans("in") : F(mu F) -> mu F$
the initial algebra, $⦇R⦈$ its catamorphism; $(mu X : phi X)$ the least solution of
$X = phi X$.  Points: $x thin R thin y$.

*B&dM dictionary.*  Everything else on the sheet is the book's, mirrored through this
table and nothing more.

#laws(
  [*B&dM*], [*here*],
  [$S dot.c R$], [$R S$ #h(1fr) composition reverses],
  [$i d$], [$1$],
  [$"outl", "outr"$], [$pi, pi'$],
  [$"inl", "inr"$], [$iota, iota'$],
  [$alpha$], [$sans("in")$ #h(1fr) the initial algebra, not an object],
  [$(|R|)$], [$⦇R⦈$],
  [$mu$], [$union.big$ #h(1fr) ($mu$ is kept for the least fixed point)],
  [$∈$, #h(0.3em) $eps$], [$eps$, #h(0.3em) $eps^degree$],
  [$T backslash U$, #h(0.3em) $U slash T$], [$U slash T$, #h(0.3em) $T backslash U$
    #h(1fr) slashes flip, roles kept],
  [$(a,b) thin chevron.l R,S chevron.r thin c$], [$c thin chevron.l R,S chevron.r thin (a,b)$
    #h(1fr) points reverse too],
)

A row tagged *✓* has its mirrored statement machine-checked in `AOP/A*.lean`; the rest are
hand-mirrored from the page.
]
