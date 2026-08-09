// Shared by every Bird & de Moor chapter body (AOP/ch5, AOP/ch6, …): the page shapes come from
// the Freyd note's style.typ, and everything below is what the B&dM mirror adds on top of it.
// Imported, not #included: `#include` evaluates a file's CONTENT, so the `#let`s would not travel.
#import "/Freyd/note/cheatsheet/style.typ": *

// The book's ⧺ (list concatenation), which appears in the pointwise glosses, where application
// order is the book's and nothing flips.
#let cc = math.class("binary", "⧺")
// ∼ is classed as a relation, so `∼C` sets with a gap; force operand class, as style.typ does for ∋.
#let tld = math.class("normal", sym.tilde.op)
// The third tier, under the chapter (breaks, thick rule) and the section (thin rule): a group of
// rows inside a section, which gets neither a rule nor a break, only a bold accent line.
#let sub(t) = block(above: 1.0em, below: 0.5em, sticky: true,
  text(weight: "bold", fill: accent, t))
// B&dM's own layout for a calculation: an expression, then the step's relation and its hint, then
// the next expression.  `deriv($X$, ("=", [why]), $Y$, …)` — a bare item is a line, a pair is a
// step.  Named `deriv`, not `calc`: `calc` is a Typst module.
#let deriv(..items) = block(inset: (y: 3pt), table(
  columns: (auto, 1fr), stroke: none, inset: (x: 5pt, y: 1.6pt),
  align: (right + horizon, left + horizon),
  ..items.pos().map(it => if type(it) == array { ([#it.at(0)], text(fill: dimc, size: 0.92em)[#it.at(1)]) }
    else { ([], it) }).flatten()
))
