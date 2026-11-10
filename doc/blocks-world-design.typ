#set page(paper: "a4", margin: 2cm)
#set text(size: 10.5pt)
#set par(justify: false)
#show raw.where(block: true): set block(fill: luma(245), inset: 8pt, radius: 3pt, width: 100%)

// One block, a tower (listed bottom-up), and a world of towers standing on the table.
#let blk(n) = rect(width: 1.4em, height: 1.4em, inset: 0pt, stroke: 0.6pt, align(center + horizon, n))
#let tower(..bs) = stack(dir: btt, ..bs.pos().map(blk))
#let world(..ts) = stack(dir: ttb,
  grid(columns: 3, column-gutter: 3pt, align: bottom, ..ts.pos().map(t => tower(..t))),
  line(length: 4.8em, stroke: 1.2pt))

= Blocks world as relations

AIMA §11.1.3 (the Sussman anomaly) in STRIPS, written point-free over one object. Composition is juxtaposition in
diagram order: $E F$ is first $E$, then $F$. $E°$ is the converse, $∼E$ the complement in its hom-set, $bb(1)$ the
identity, $top : X -> X$ the top of the hom-set $(X, X)$. Every relation has a one-letter name.

== Encoding

The table is not an object: the diagonal stands for it. $b S b$ means "$b$ is on the table".

#table(
  columns: (auto, auto, 1fr),
  stroke: 0.4pt,
  [*variable*], [*type*], [*meaning*],
  [$X$], [object], [the blocks ${A, B, C}$, the only object],
  [$S$], [$X -> X$], [the state, a map: $b S y$ ⟺ $b$ is on block $y$; $b S b$ ⟺ $b$ is on the table],
  [$R eq.def S ∩ ∼bb(1)$], [$X -> X$], [$b$ rests on another block],
  [$M eq.def ∼(R° top ∪ top R)$], [$X -> X$], [the moves allowed now: nothing is on $b$ and nothing is on $y$.
    $(b, y)$ moves $b$ onto $y$; $(b, b)$ moves $b$ to the table],
  [$p subset.eq M$], [$X -> X$], [the one move chosen, a single pair],
  [$S' eq.def (S ∩ ∼(p top)) ∪ p$], [$X -> X$], [the next state: drop $b$'s old pair, add $p$],
  [$G eq.def {(A, B), (B, C)}$], [$X -> X$], [the goal; it is reached when $G subset.eq S$],
)

== Where each STRIPS precondition went

#table(
  columns: (auto, 1fr),
  stroke: 0.4pt,
  [*precondition*], [*handled by*],
  [$"Clear"(b)$], [$R° top$ removes every pair whose source has a block on it. Without it, $A$ (under $C$) could
    move onto $C$: a cycle.],
  [$"Clear"(y)$], [$top R$ removes every pair whose target has a block on it. Without it, $B$ could move onto $A$:
    two blocks on $A$.],
  [$"Clear"("Table")$], [never tested: the table is not in $R$, so it is always clear.],
  [$"Block"(b), "Block"(y)$], [the type $X$.],
  [$b != y$], [no term: the pair $(b, b)$ is the move to the table.],
  [$b != x$], [an invariant: $S$ has no cycle through other blocks, and $S'$ changes only the pair of a $b$ with
    nothing on it.],
  [$x != y$], [if $x$ is a block, $b$ is on it, so $top R$ removes $(b, x)$. If $x$ is the table, $(b, b)$
    leaves $S$ unchanged: a no-op.],
  [$"On"(b, x)$], [$x$ is not a parameter: it is read off $S$, and $∩ ∼(p top)$ deletes it.],
)

Effects: the add list is $∪ p$, the delete list is $∩ ∼(p top)$. $"Clear"$ is not stored, so its add and delete
come for free.

== The plan

#table(
  columns: (auto, auto, auto, auto, 1fr),
  stroke: 0.4pt,
  align: (center, center, left, left, left),
  [*step*], [*world*], [*$S$*], [*$p$*], [*$M$*],
  [0], world(("A", "C"), ("B",), ()), [${(A,A), (B,B), (C,A)}$], [$(C, C)$],
    [${B, C} times {B, C}$: $A$ is under $C$],
  [1], world(("A",), ("B",), ("C",)), [${(A,A), (B,B), (C,C)}$], [$(B, C)$], [$top$: every block is clear],
  [2], world(("A",), ("C", "B"), ()), [${(A,A), (B,C), (C,C)}$], [$(A, B)$],
    [${A, B} times {A, B}$: $C$ is under $B$],
  [3], world((), ("C", "B", "A"), ()), [${(A,B), (B,C), (C,C)}$], [], [$G subset.eq S$: done],
)

The plan is MoveToTable$(C)$, Move$(B, C)$, Move$(A, B)$. A breadth-first search over $S$ finds it: each state
gives its $M$, and each pair $p$ in $M$ gives one successor $S'$.

== Out of scope

- *Searching the whole state space at once.* Berghammer's style: states are the columns of
  $∈ : X times X -> 2^(X times X)$, and the moves are one relation on $2^(X times X)$. This needs BDDs.
- *Richer PDDL.* Negative preconditions and conditional effects are more $∼$ and $∪$. Numeric fluents are not
  relations.
