// Freyd & Scedrov, "Categories, Allegories" — cheatsheet of chapter 1 from §1.4 on.
// Every capitalized definition, every theorem, and Freyd's own diagrams, drawn in his
// diagrammatic language (panels separated by ∀ / ∃ / ∃! / ! bars) rather than collapsed.
// Deliberately omitted: chapter 2 (allegories); the τ-category apparatus (§1.49–1.4(12))
// and the other machinery that exists only to prove metatheorems; every example built on
// ℒℋ (local homeomorphisms) and its slices 𝒮h(Y) (Lazard sheaves).
#import "style.typ": *

#show: sheet.with(
  title: "Categories, Allegories",
  subtitle: [Freyd & Scedrov, chapter 1 from §1.4 — definitions, diagrams, theorems],
)

= Conventions
Composition is written by juxtaposition in diagram order: $x y$ is "first $x$, then $y$", so
$square x$ is the source of $x$ and $x square$ its target. Bold $bold(A)$ is a category, plain
$A, B, ...$ its objects; $|bold(A)|$ the objects, $(A, B)$ the morphisms from $A$ to $B$,
$bold(A)^circle.small$ the opposite, $bold(A) slash B$ the slice over $B$ with forgetful
$Sigma: bold(A) slash B -> bold(A)$, $cal(S)$ the category of sets, $cal(S)^bold(A)$ the
functor category. $1$ is a terminator, $0$ an initial object (coterminator), $p_A: A -> 1$.
Products come with $ell: A times B -> A$, $kappa.alt: A times B -> B$, pairing
$chevron.l f, g chevron.r$ and $x times y$.

#v(0.2em)
*Diagrams.* Freyd's own figures, in his diagrammatic language. Every diagram states equations
unless punctured. A diagrammatic sentence is a row of diagrams separated by bars carrying
$forall$, $exists$, $exists!$ or $!$ ("there is at most one extension to the next diagram");
its vertices are bare dots, since the language names nothing.
#laws(
  [#box(baseline: 20%, punc-sample)], [puncture mark — removes exactly one equation: that
    part of the diagram need not commute],
  [#box(baseline: 20%, prodm-sample)], [this wedge is a product diagram],
  [#box(baseline: 20%, corner-sample)], [this vertex is a pullback, or a monic pair],
  [$arrow.r.tail$], [monic],
  [#box(baseline: 20%, diagram(spacing: 9mm, node((0,0), $A$), node((1,0), $B$),
     edge((0,0), (1,0), marks: cover)))],
  [cover (§1.512) — the hollow triangle head],
  [$arrow.dashed$], [the morphism whose existence and uniqueness is being asserted],
  [$arrow.r.hook$], [a member of a distinguished class (dense monics, inclusions)],
)

#include "part-1.4.typ"
#include "part-1.5.typ"
#include "part-1.6.typ"
#include "part-1.7.typ"
#include "part-1.8.typ"
#include "part-1.9.typ"
#include "part-1.10.typ"
