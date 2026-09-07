// `#include`d by allegory-axioms.typ, which does not share its scope: the helpers must be re-imported.
#import "note-style.typ": definition, disp, P, d, src, Thm, calc-table, EQ, vstep
#import "draw.typ": zline, zpair, zsqc, zstep, SQ, RQ
#import "circuit.typ": wire, gbox, boxrun, boxrun-w, tape, tape-join, LEAD, frc, TAPEEDGE, est-R-box, union-box
#import "dpanel.typ": dpanel, hm-meta
#import "cetz-nodraw.typ" as cetz

= Appendix <sec-appendix>

== `P(S) est(R)=(∋S)∩(∈\(SR°))`

// B&dM (7.9), `R` reflexive.  `⊑` is @est-710; `⊒` is the one place in this appendix where a tabulation is
// unavoidable — `y` below is the set the right-hand side only describes.
#disp[#definition[
`(p,q)` tabulates `W≜(∋S)∩(∈\(SR°))`, and #h(4pt) `y≜` $frac(#[`(p∋S)∩(qR)`], ∋)$, a map.
]]<est-79-defn>

#disp[
#zline(
  zsqc(`W`, `P(S) est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[`p°q=W`, `𝟙⊑yy°`],
  zpair(zsqc(`p°y`, `P(S)`), zsqc(`y°q`, `est(R)`)),
)
]<est-79>

#disp[
#zline(
  zsqc(`y°q`, `∋`),
  zstep(op: sym.arrow.l.double, under: true)[`f°·⊣f·`, `·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`q`, `(p∋S)∩(qR)`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `f°·⊣f·`],
  // Only the LOWER box of a pair can carry a `name`: on the upper one it lands on the box below it.
  zpair(zsqc(`p°q`, `∋S`), zsqc(`𝟙`, `R`, name: "R reflexive")),
)
#zline(
  zsqc(`∈y°q`, `R°`),
  zstep(op: sym.arrow.l.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, `°`, meet],
  zsqc(`R°q°q`, `R°`, name: "q simple"),
)
]<est-79-est>

#disp[
#zline(
  zsqc(`p°y`, `P(S)`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `·T⊣/T`, `°`, `f°·⊣f·`],
  zpair(zsqc(`p°y∋`, `∋S`), zsqc(`p∋`, `y∋S°`)),
)
#zline(
  zsqc(`p°y∋`, `∋S`),
  zstep(op: sym.arrow.l.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, meet],
  zsqc(`p°p∋S`, `∋S`, name: "p simple"),
)
#zline(
  zsqc(`p∋`, `y∋S°`),
  zstep(op: sym.arrow.l.double, under: true)[modular law],
  zsqc(`p∋`, `(p∋)∩(qRS°)`),
  zstep(op: sym.arrow.l.double, under: true)[`𝟙⊑qq°`],
  zsqc(`q°p∋`, `RS°`),
  zstep(op: sym.arrow.l.double, under: true)[`°`, `T·⊣T\`],
  zsqc(`W`, `∈\(SR°)`, name: "W's right half"),
)
]<est-79-pow>

== `P(est(R)) est(R)=P(Dom(est(R))) union est(R)`

// B&dM (7.12), `R` a preorder.  `⊑` puts the domain in for free; `⊒` is @est-79 at `S := est(R)`
// and then the two halves the book leaves as exercises.
#disp[
#zline(
  zsqc(`P(est(R)) est(R)`, none),
  zstep(op: sym.eq, under: true)[`Dom(est(R)) est(R)=est(R)`],
  zsqc(`P(Dom(est(R)) est(R)) est(R)`, none),
)
#zline(
  zstep(op: sym.eq, under: true)[`P` a relator],
  zsqc(`P(Dom(est(R)))P(est(R)) est(R)`, none),
  zstep(op: sym.subset.eq.sq, under: true)[@est-711],
  zsqc(`P(Dom(est(R))) union est(R)`, none),
)
]<est-712>

#disp[
#zline(
  zsqc(`P(Dom(est(R))) union est(R)`, `P(est(R)) est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[@est-79 at `S:=est(R)`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(Dom(est(R))) union est(R)`, `∋est(R)`),
        zsqc(`∈P(Dom(est(R))) union est(R)`, `est(R)R°`)),
)
#zline(
  zsqc(`P(Dom(est(R))) union est(R)`, `∋est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[`P(Dom(est(R)))⊑𝟙`],
  zsqc(`union est(R)`, `∋est(R)`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`T(U∩V)⊑TU∩TV`, `·∋⊣`$frac(#box(width: 8pt), ∋)$, @est-73],
  zsqc(`(∋∋)∩(∈\(∈\R°))`, `∋est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[modular law],
  zsqc(`∋(∋∩(∈(∈\(∈\R°))))`, `∋(∋∩(∈\R°))`, name: "counit of T·⊣T\\"),
)
#zline(
  zsqc(`∈P(Dom(est(R))) union est(R)`, `est(R)R°`),
  zstep(op: sym.arrow.l.double, under: true)[`∈` lax natural],
  zsqc(`Dom(est(R))∈union est(R)`, `est(R)R°`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`Dom(est(R))⊑est(R) est(R)°`],
  zsqc(`est(R) est(R)°∈union est(R)`, `est(R)R°`),
  zstep(op: sym.arrow.l.double, under: true)[`est(R)°⊑∈`, `∈∈union⊑∈`],
  zsqc(`est(R)∈est(R)`, `est(R)R°`, name: "UP of est"),
)
]<est-712-geq>

== Shortest paths on a cylinder, on lists <sec-cyl-lists>

// B&dM §7.4, p. 179.  Its crux is @mon-thm71, not the greedy theorem: `α` is a map, so monotonic
// gives distributes, which is (7.13) — the section's only numbered equation.
#disp[#table(
  columns: (7.2cm, 5.0cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

  [`F(A,X)=A+A×X`],
  [`𝒜×𝒜⟶𝒜`],
  [The base functor: one square of the new column, alone or in front of the path so far.],

  [`L=list⁺`],
  [`𝒜⟶𝒜`],
  [A path is a non-empty list of squares, one per column crossed.],

  [`α` the initial algebra],
  [`F(A,LA)⟶LA`],
  [`α(5)=[5]` and `α(1,[5])=[1,5]`: a path is started by one square, or extended by one.],

  [`N` \ the `n`-tuple relator],
  [`𝒜⟶𝒜`],
  [One component per row of a column, so the fold carries `n` answers at once.],

  [`R≜sum≤sum°`],
  [`L Nat⟶L Nat`],
  [The cost of a path, which the cheapest minimises.],

  [`setify`],
  [`NA⟶EA`],
  [`setify(1,2,3,4)={1,2,3,4}` — which row a component came from is forgotten.],

  [`moves`],
  [`NA⟶E(NA)`],
  [`moves(x)={up(x),x,down(x)}` — rotated up, unrotated, rotated down.],

  [`trans`],
  [`E(NA)⟶N(EA)`],
  [`trans{(a,b,c),(x,y,z)}=({a,x},{b,y},{c,z})` — component `k` of the result is the set of the `k`-th components.],

  [`zip`],
  [`F(NA,NB)⟶NF(A,B)`],
  [`zip((1,2,3,4),({[5]},{[6]},{[7]},{[8]}))=((1,{[5]}),(2,{[6]}),(3,{[7]}),(4,{[8]}))`.],

  [`cp≜` $frac(#[`F(𝟙,∋)`], ∋)$],
  [`F(A,EB)⟶E(F(A,B))`],
  [`cp(1,{[5],[6],[8]})={(1,[5]),(1,[6]),(1,[8])}`.],

  [`gen≜F(𝟙,moves trans N(union)) zip N(cp P(α))`
 #src[]],
   // lean:AOP.A7_4_Cylinder.gen@4bd0bafd
  [`F(NA,N(E(LA)))⟶N(E(LA))`],
  [`gen((1,2,3,4),({[5]},{[6]},{[7]},{[8]}))` is worked out in @cyl-gen.],

 [`paths≜⦇gen⦈ setify union` #src[]],
  // lean:AOP.A7_4_Cylinder.paths@dbba0e86
  [`L N Nat⟶E(L Nat)`],
  [`paths[(1,2,3,4),(5,6,7,8)]` is the union of @cyl-gen's four sets: 12 paths, 3 from each entry row.],

  [the specification \ `paths est(R)`],
  [`L N Nat⟶L Nat`],
  [A cheapest path from the entry side to the exit side.],
)]<cyl-defn>

=== `N(E(L A))` <sec-cyl-nela>

#disp[#align(center, grid(
  columns: 2, column-gutter: 34pt, align: horizon,
  grid(columns: 2, column-gutter: 14pt, row-gutter: 5pt, align: center,
    [`1`], [`5`], [`2`], [`6`], [`3`], [`7`], [`4`], [`8`]),
  [`[(1,2,3,4),(5,6,7,8)] : L N Nat`],
))]<cyl-array>

// One raw block, not a grid: the four components line up because every glyph is one monospace
// advance wide, which no measured column can promise.
#disp[#align(center)[```
⦇gen⦈[(5,6,7,8)] = ({[5]},{[6]},{[7]},{[8]})

gen((1,2,3,4),({[5]},{[6]},{[7]},{[8]})) =
    ( {[1,5],[1,6],[1,8]},
      {[2,5],[2,6],[2,7]},
      {[3,6],[3,7],[3,8]},
      {[4,5],[4,7],[4,8]} )
```]]<cyl-gen>

#disp[#block(breakable: false)[
#table(
  columns: (2.0cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`N`],
  [the 4-tuple, one component per row of the entry column],

  [`E`],
  [the set of paths that can start in that row],

  [`L`],
  [a path is the non-empty list of the squares it crosses],
)
#align(center, block(width: 16.5cm, inset: (y: 4pt))[#src[row 1's set has no `[1,7]` — from row 1
  only rows 4, 1 and 2 are reachable — and it does have `[1,8]`, because the cylinder glues the
  bottom row to the top. That is `moves trans N(union)` of @cyl-defn: component `k` collects the
  paths of rows `k-1`, `k`, `k+1`.]])
]]<cyl-nela>

=== The cross product `cp≜`$frac(#[`F(𝟙,∋)`], ∋)$ <sec-cyl-cp>

#disp[#align(center, grid(columns: (1fr, 1fr, 1fr), align: center + bottom, column-gutter: 10pt, row-gutter: 4pt,
  dpanel(3.3, 7.88, 6.03,
  ((2.5, 1.65, "bot", none, frc([`𝟙`])), (4.151, "top", "bot", none, none), (4.776, "top", 1.1, none, none), (5.401, "top", "bot", none, none)),
  ((1.1, [`∋`], black, 4.776, 4.776, "lax"),),
  ((4.151, [`F(A,−)`]), (4.776, [`E`]), (5.401, [`L`]), (6.03, [`A`])),
  ((2.5, [`E`]), (4.151, [`F(A,−)`]), (5.401, [`L`]), (6.03, [`A`])),
  obj: ((1.65, [`A`]), (1.1, [`A`])),
  cert: (expect: "𝟙%∋ E(F(𝟙,∋))", src: "F(A,E(L(A)))", tgt: "E(F(A,L(A)))")),
  dpanel(3.3, 7.11, 5.26,
  ((2.5, 1.65, "bot", none, frc([`𝟙`])), (3.387, "top", "bot", none, none), (4.012, "top", 1.1, none, none), (4.637, "top", "bot", none, none)),
  ((1.1, [`∋`], black, 4.012, 4.012, "lax"),),
  ((3.387, [`A×−`]), (4.012, [`E`]), (4.637, [`L`]), (5.26, [`A`])),
  ((2.5, [`E`]), (3.387, [`A×−`]), (4.637, [`L`]), (5.26, [`A`])),
  obj: ((1.65, [`A`]), (1.1, [`A`])),
  cert: (expect: "𝟙%∋ E(𝟙×∋)", src: "A×E(L(A))", tgt: "E(A×L(A))")),
  dpanel(4.4, 4.97, 3.12,
  ((2.5, 2.75, "bot", none, frc([`𝟙`])),),
  (),
  ((3.12, [`A`]),),
  ((2.5, [`E`]), (3.12, [`A`])),
  obj: ((2.75, [`A`]),),
  cert: (expect: "𝟙%∋", src: "A", tgt: "E(A)", frame: 4, top: 3)),

  src[`cp` on all of `F(A,E(L A))`],
  src[the `A×−` summand: `∋` picks one path, `𝟙%∋` collects the results],
  src[the `A` summand, no `E` to distribute: `𝟙%∋` alone, `a↦{a}`],
))]<cp-diag>

#disp[#table(
  columns: (5.6cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*type*], [*note*]),

  [`F(A,−)=A+A×−`],
  [one wire carries the whole functor, both summands with it; the `∋` under it is `F(𝟙,∋)`],

  [`∋:E(L A)⟶L A`],
  [the `∋` inside `F(𝟙,∋)`: a set of paths, one of them — `L A` is one path, `A` one square],

  [`F(𝟙,∋)=𝟙+𝟙×∋`],
  [`:A+A×E(L A)⟶A+A×L A`, the relator acting on each summand],

  [`∋:E(A+A×L A)⟶A+A×L A`],
  [the `∋` under the bar: a set of cells, one of them — a different `∋`],

  [`cp:A+A×E(L A)⟶E(A+A×L A)`],
  [$frac(#[`R`], ∋)$ turns `R:X⟶Y` into `X⟶E Y`],

  [`cp=`$frac(#[`𝟙`], ∋)$` E(F(𝟙,∋))`],
  [what the picture draws: the unit makes the outer `E`, leaving one `∋` — @pow-laws],
)]<cp-types>

#disp[#align(center)[```
w      = (1,{[5],[6],[8]})            : A×E(L A)     the right summand
𝟙×∋   : A×E(L A) ⟶ A×L A                             𝟙 keeps the square 1, ∋ picks one path
         w ↦ (1,[5]), (1,[6]), (1,[8]) : A×L A        one output per path in w
cp(w)  = {(1,[5]),(1,[6]),(1,[8])}   : E(A+A×L A)   the three of them, collected
```]]<cp-step>

#v(8pt)

=== `gen=F(𝟙,moves trans N(union)) zip N(cp P(α))` <sec-cyl-gen>

#disp[#align(center, dpanel(7.7, 6.35, 4.5,
  ((2.5, 3.3, "bot", none, none), (2.877, 2.2, "bot", none, none), (3.658, 2.2, 1.1, [`F`], none), (2.877, 3.3, 2.2, [`F`], none), (2.5, "top", 3.3, none, none), (2.877, 5.5, 3.3, [`N`], none), (3.658, 4.4, 2.2, [`E`], none), (3.502, 5.5, 4.4, [`E`], none), (2.877, 6.6, 5.5, [`E`], none), (3.502, 6.6, 5.5, [`N`], none), (3.189, "top", 6.6, none, none), (3.879, "top", 4.4, none, none)),
  ((6.6, [`moves`], black, 3.189, 3.189, "lax"), (5.5, [`trans`], black, 2.877, 3.1895, "lax"), (4.4, [`union`], black, 3.502, 3.6905), (3.3, [`zip`], black, 2.5, 2.6885, "lax"), (2.2, [`cp`], black, 2.877, 3.2675), (1.1, [`α`], black, 3.658)),
  ((2.5, [`F`]), (3.189, [`N`]), (3.879, [`E`]), (4.5, [`LA`])),
  ((2.5, [`N`]), (2.877, [`E`]), (4.5, [`LA`])),
  obj: ((6.6, [`LA`]), (5.5, [`LA`]), (4.4, [`LA`]), (3.3, [`LA`]), (2.2, [`LA`]), (1.1, [`LA`])),
  cert: (expect: "F(𝟙,moves trans N(union))zip N(cp P(α))", src: "F(N(E(LA)))", tgt: "N(E(LA))", sigs: ("α": "F(LA)⟶LA!lean=lean:AOP.A5_5.Freyd.Alg.InitialAlgebra.α@c4c898e2"))))]<gen-diag>

#disp[#align(center)[```
u = ((1,2,3,4),({[5]},{[6]},{[7]},{[8]}))      : F(N A,N(E(L A)))
F(𝟙,moves trans N(union))                         𝟙 keeps the column, the path SETS move
  moves({[5]},{[6]},{[7]},{[8]})
   = {({[6]},{[7]},{[8]},{[5]}),
      ({[5]},{[6]},{[7]},{[8]}),
      ({[8]},{[5]},{[6]},{[7]})}               : E(N(E(L A)))  down, unmoved, up
  trans(that)
   = ({{[6]},{[5]},{[8]}},{{[7]},{[6]},{[5]}},
      {{[8]},{[7]},{[6]}},{{[5]},{[8]},{[7]}}) : N(E(E(L A)))  row k gets rows k-1, k, k+1
  N(union)(that)
   = ({[5],[6],[8]},{[5],[6],[7]},
      {[6],[7],[8]},{[5],[7],[8]})             : N(E(L A))     every path into row k, none dropped
zip(that)
   = ((1,{[5],[6],[8]}),(2,{[5],[6],[7]}),
      (3,{[6],[7],[8]}),(4,{[5],[7],[8]}))     : N(F(A,E(L A)))  each row: its square, and the
                                                                paths it may be put in front of
N(cp P(α))(that)
   = ({[1,5],[1,6],[1,8]},{[2,5],[2,6],[2,7]},
      {[3,6],[3,7],[3,8]},{[4,5],[4,7],[4,8]}) : N(E(L A))     cp pairs the square with each path,
                                                               α prefixes it: α(1,[5])=[1,5]
```]]<gen-step>

=== `gen` is an `F`-algebra; `⦇gen⦈`: `α⦇gen⦈=F(𝟙,⦇gen⦈)gen` <sec-cyl-fold>

// The defining equation of @cata-defining at `gen`, both sides drawn: the fold bead is
// OUTSIDE `F` on the left and INSIDE it on the right — that is all the recursion there is.
#disp[#align(center, grid(columns: 3, align: horizon + center, column-gutter: 14pt, row-gutter: 5pt,
  dpanel(3.3, 6.23, 4.38,
  ((2.5, 1.1, "bot", none, none), (3.125, 1.1, "bot", none, none), (3.75, 1.1, "bot", none, none), (2.812, 2.2, 1.1, [`L`], none), (3.438, 2.2, 1.1, [`N`], none), (2.5, "top", 2.2, none, none), (3.125, "top", 2.2, none, none), (3.75, "top", 2.2, none, none)),
  ((2.2, [`α`], black, 2.5), (1.1, [`⦇gen⦈`], black, 2.812, 3.125, "lax")),
  ((2.5, [`F`]), (3.125, [`L`]), (3.75, [`N`]), (4.38, [`A`])),
  ((2.5, [`N`]), (3.125, [`E`]), (3.75, [`L`]), (4.38, [`A`])),
  obj: ((2.2, [`A`]), (1.1, [`A`])),
  cert: (expect: "α⦇gen⦈", src: "F(L(N(A)))", tgt: "N(E(L(A)))", sigs: ("⦇⦈": "L(N(x))⟶N(E(L(x)))", "α": "F(L(N(A)))⟶L(N(A))!lean=lean:AOP.A5_5.Freyd.Alg.InitialAlgebra.α@c4c898e2"))),
  EQ,
  dpanel(3.3, 6.6, 4.75,
  ((2.656, 1.1, "bot", none, none), (2.5, "top", 1.1, none, none), (2.877, 2.2, 1.1, [`N`], none), (3.502, 2.2, "bot", none, none), (4.127, 2.2, "bot", none, none), (3.189, "top", 2.2, none, none), (3.814, "top", 2.2, none, none)),
  ((2.2, [`⦇gen⦈`], black, 3.189, 3.5015, "lax"), (1.1, [`gen`], black, 2.5)),
  ((2.5, [`F`]), (3.189, [`L`]), (3.814, [`N`]), (4.75, [`A`])),
  ((2.656, [`N`]), (3.502, [`E`]), (4.127, [`L`]), (4.75, [`A`])),
  obj: ((2.2, [`A`]), (1.1, [`A`])),
  cert: (expect: "F(𝟙,⦇gen⦈)gen", src: "F(L(N(A)))", tgt: "N(E(L(A)))", sigs: ("⦇⦈": "L(N(x))⟶N(E(L(x)))"))),

  src[`α` puts the column back on the list, then the fold reads all of it],
  [],
  src[the fold reads the rest under `F`, then one `gen` puts the column in front],
))]<fold-diag>
   // lean:AOP.A7_4_CylinderPaths.RelSet.Tuple.cataGen@4c4ca025
   // lean:AOP.A7_4_CylinderPaths.RelSet.Tuple.cataGen_lax_natural@1dc8cdb8

#disp[#align(center)[```
xs = [(1,2,3,4),(5,6,7,8)] = α((1,2,3,4),[(5,6,7,8)])   : L(N A)

⦇gen⦈(xs) = gen((1,2,3,4), ⦇gen⦈[(5,6,7,8)])
```]]<fold-step>

#align(center, block(width: 16.5cm, inset: (y: 4pt))[#src[both halves are in @cyl-gen: the
  tail folds to `({[5]},{[6]},{[7]},{[8]})`, one path per row and each of them one square long,
  and `gen` on it is @gen-step's walk.]])

=== `Q : F(N A,N(L A))⟶N(L A)`, an `F(N A,−)`-algebra: `Q=F(𝟙,moves trans N(est(R))) zip N(α)` <sec-cyl-deriv>

#disp[#align(center)[```
Q : F(N A,N(L A)) ⟶ N(L A)                     the fold's algebra: a new column, one path per row

u = ((1,2,3,4),([5],[6],[7],[8]))              : F(N A,N(L A))
F(𝟙,moves trans N(est(R)))                        𝟙 keeps the column, the paths move
  moves([5],[6],[7],[8])
   = {([6],[7],[8],[5]),
      ([5],[6],[7],[8]),
      ([8],[5],[6],[7])}                       : E(N(L A))     down, unmoved, up
  trans(that)
   = ({[6],[5],[8]},{[7],[6],[5]},
      {[8],[7],[6]},{[5],[8],[7]})             : N(E(L A))     row k gets rows k-1, k, k+1
  N(est(R))(that)
   = ([5],[5],[6],[5])                         : N(L A)        the cheapest into each row —
                                                               chosen BEFORE the new square
zip(that)
   = ((1,[5]),(2,[5]),(3,[6]),(4,[5]))         : N(F(A,L A))   each row: its square, and the one
                                                               predecessor that survived
N(α)(that)
   = ([1,5],[2,5],[3,6],[4,5])                 : N(L A)        α(1,[5])=[1,5]
```]]<q-step>

// ---- §13.5.2's own vocabulary.  CIRCUIT: one wire, a box per factor of the composite, a cut
// corner for a relation and a square box for a map.
#let cb-paths = ([`paths`], 1.9, false)
#let cb-fold = ([`⦇gen⦈`], 3.6, false)
#let cb-setify = ([`setify`], 1.9, false)
#let cb-Pest = ([`P(est(R))`], 3.0, true)
#let cb-Nest = ([`N(est(R))`], 3.0, true)
#let cb-foldQ = ([`⦇Q⦈`], 1.5, true)
#let cb-gen = ([`gen`], 2.7, false)
#let cb-FNest = ([`F(𝟙,N(est(R)))`], 4.4, true)
#let cb-Q = ([`Q`], 0.8, true)
#let cb-Fmtn = ([`F(𝟙,moves trans N(est(R)))`], 7.8, true)
#let cb-zip = ([`zip`], 1.3, false)
#let cb-Nal = ([`N(α)`], 1.7, false)
#let cb-Nwrap = ([`N(wrap)`], 2.4, false)
#let cb-moves = ([`moves`], 1.75, false)
#let cb-trans = ([`trans`], 1.75, false)
#let cb-zipp = ([`zip'`], 1.5, false)
#let cb-Ncons = ([`N(cons)`], 2.4, false)

#let cyp(body, s: 92%) = P(cetz.canvas(length: 0.8cm, body), s: s)
// The end names are ANCHORED, not centred at a hand-measured x: one of them is `F(NA,N(E(LA)))`
// and every row would otherwise need its own offset.
#let cyrun(lft, rgt, items) = {
  d.content((-0.2, 0), text(10pt)[#lft], anchor: "east")
  boxrun(0, 0, items)
  d.content((boxrun-w(items) + 0.2, 0), text(10pt)[#rgt], anchor: "west")
}
// The bracket at `F(NA,N(LA))=NA+NA×N(LA)`: the fork sends `NA` to the box above and the pair
// below, where `zip'` closes the two strands into one before the run that follows it.
#let CYBR = 1.40   // the bracket's branch height
#let CYSP = 0.45   // half the gap between the pair's strands
#let cyfork(up, lo, span, post) = {
  let cy = -CYBR
  let x0 = 1.26
  let runw(bs) = bs.map(b => b.at(1) + LEAD).sum(default: 0.0)
  let xs = x0 + runw(lo)
  let xj = calc.max(x0 + runw(up), xs + span.at(1) + runw(post)) + 0.7
  tape((0.34, cy - CYSP - 0.95), (xj, CYBR + 0.95))
  wire((0, 0), (0.34, 0))
  let st = (thickness: 1.4pt, paint: TAPEEDGE)
  d.bezier((0.56, 0), (x0, CYBR), (0.98, 0), (0.98, CYBR), stroke: st)
  d.bezier((0.56, 0), (x0, cy + CYSP), (0.98, 0), (0.98, cy + CYSP), stroke: st)
  d.bezier((0.56, 0), (x0, cy - CYSP), (0.98, 0), (0.98, cy - CYSP), stroke: st)
  let x = x0
  for b in up { gbox((x, CYBR), b.at(0), w: b.at(1), chamfer: b.at(2)); x = x + b.at(1) }
  wire((x, CYBR), (xj - 0.7, CYBR))
  // The head strand runs straight to `zip'`; the tail carries the run that `𝟙×−` acts on.
  wire((x0, cy + CYSP), (xs, cy + CYSP))
  x = x0
  for b in lo {
    gbox((x, cy - CYSP), b.at(0), w: b.at(1), chamfer: b.at(2)); x = x + b.at(1)
    wire((x, cy - CYSP), (x + LEAD, cy - CYSP)); x = x + LEAD
  }
  gbox((xs, cy), span.at(0), w: span.at(1), h: 2 * CYSP + 0.55, chamfer: span.at(2))
  x = xs + span.at(1)
  for b in post {
    wire((x, cy), (x + LEAD, cy)); x = x + LEAD
    gbox((x, cy), b.at(0), w: b.at(1), chamfer: b.at(2)); x = x + b.at(1)
  }
  wire((x, cy), (xj - 0.7, cy))
  tape-join((xj, 0), sp: CYBR, len: 0.7)
  wire((xj, 0), (xj + LEAD, 0))
  d.content((xj + LEAD + 0.2, 0), text(10pt)[`N(LA)`], anchor: "west")
  d.content((-0.35, CYBR), text(10pt)[`NA`], anchor: "east")
  d.content((-0.35, cy + CYSP), text(10pt)[`NA`], anchor: "east")
  d.content((-0.35, cy - CYSP), text(10pt)[`N(LA)`], anchor: "east")
}

// ---- HINZE-MARSDEN, generated by `scripts/diagram --fold-list`.  A wire is a FUNCTOR: the object
// wire carries `L(N(Nat))` down to `L(Nat)` and beside it ride `N` the tuple and `E` the path set.
#let ca1 = dpanel(3.3, 5.6, 3.75,
  ((2.5, 2.2, 1.1, [`E`], none), (3.125, 2.2, "bot", none, none), (2.5, "top", 2.2, none, none), (3.125, "top", 2.2, none, none)),
  ((2.2, [`paths`], black, 2.5, 2.8125, "lax"), (1.1, [`est(R)`], black, 2.5)),
  ((2.5, [`L`]), (3.125, [`N`]), (3.75, [`Nat`])),
  ((3.125, [`L`]), (3.75, [`Nat`])),
  obj: ((2.2, [`Nat`]), (1.1, [`Nat`])),
  cert: (expect: "paths est(R)", src: "L(N(Nat))", tgt: "L(Nat)", split: "", sigs: ("paths": "L(N(x))⟶E(L(x))")))
#let ca2 = dpanel(5.5, 6.23, 4.38,
  ((2.812, 2.2, 1.1, [`E`], none), (2.5, 3.3, 2.2, [`E`], none), (2.5, 4.4, 3.3, [`N`], none), (3.125, 4.4, 2.2, [`E`], none), (3.75, 4.4, "bot", none, none), (2.812, "top", 4.4, none, none), (3.438, "top", 4.4, none, none)),
  ((4.4, [`⦇gen⦈`], black, 2.812, 3.125, "lax"), (3.3, [`setify`], black, 2.5, 2.5, "lax"), (2.2, [`union`], black, 2.5, 2.8125), (1.1, [`est(R)`], black, 2.812)),
  ((2.812, [`L`]), (3.438, [`N`]), (4.38, [`Nat`])),
  ((3.75, [`L`]), (4.38, [`Nat`])),
  obj: ((4.4, [`Nat`]), (3.3, [`Nat`]), (2.2, [`Nat`]), (1.1, [`Nat`])),
  cert: (expect: "⦇gen⦈setify union est(R)", src: "L(N(Nat))", tgt: "L(Nat)", split: "", sigs: ("setify": "N(x)⟶E(x)", "⦇⦈": "L(N(x))⟶N(E(L(x)))")))
#let ca3 = dpanel(5.5, 6.23, 4.38,
  ((2.5, 3.3, 1.1, [`E`], none), (2.5, 4.4, 3.3, [`N`], none), (3.125, 4.4, 2.2, [`E`], none), (3.75, 4.4, "bot", none, none), (2.812, "top", 4.4, none, none), (3.438, "top", 4.4, none, none)),
  ((4.4, [`⦇gen⦈`], black, 2.812, 3.125, "lax"), (3.3, [`setify`], black, 2.5, 2.5, "lax"), (2.2, [`est(R)`], black, 3.125), (1.1, [`est(R)`], black, 2.5)),
  ((2.812, [`L`]), (3.438, [`N`]), (4.38, [`Nat`])),
  ((3.75, [`L`]), (4.38, [`Nat`])),
  obj: ((4.4, [`Nat`]), (3.3, [`Nat`]), (2.2, [`Nat`]), (1.1, [`Nat`])),
  cert: (expect: "⦇gen⦈setify P(est(R))est(R)", src: "L(N(Nat))", tgt: "L(Nat)", split: "", sigs: ("setify": "N(x)⟶E(x)", "⦇⦈": "L(N(x))⟶N(E(L(x)))")))
#let ca4 = dpanel(5.5, 6.23, 4.38,
  ((2.5, 2.2, 1.1, [`E`], none), (2.5, 4.4, 2.2, [`N`], none), (3.125, 4.4, 3.3, [`E`], none), (3.75, 4.4, "bot", none, none), (2.812, "top", 4.4, none, none), (3.438, "top", 4.4, none, none)),
  ((4.4, [`⦇gen⦈`], black, 2.812, 3.125, "lax"), (3.3, [`est(R)`], black, 3.125), (2.2, [`setify`], black, 2.5, 2.5, "lax"), (1.1, [`est(R)`], black, 2.5)),
  ((2.812, [`L`]), (3.438, [`N`]), (4.38, [`Nat`])),
  ((3.75, [`L`]), (4.38, [`Nat`])),
  obj: ((4.4, [`Nat`]), (3.3, [`Nat`]), (2.2, [`Nat`]), (1.1, [`Nat`])),
  cert: (expect: "⦇gen⦈N(est(R))setify est(R)", src: "L(N(Nat))", tgt: "L(Nat)", split: "", sigs: ("setify": "N(x)⟶E(x)", "⦇⦈": "L(N(x))⟶N(E(L(x)))")))
#let ca5 = dpanel(4.4, 5.6, 3.75,
  ((2.5, 2.2, 1.1, [`E`], none), (2.5, 3.3, 2.2, [`N`], none), (3.125, 3.3, "bot", none, none), (2.5, "top", 3.3, none, none), (3.125, "top", 3.3, none, none)),
  ((3.3, [`⦇Q⦈`], black, 2.5), (2.2, [`setify`], black, 2.5, 2.5, "lax"), (1.1, [`est(R)`], black, 2.5)),
  ((2.5, [`L`]), (3.125, [`N`]), (3.75, [`Nat`])),
  ((3.125, [`L`]), (3.75, [`Nat`])),
  obj: ((3.3, [`Nat`]), (2.2, [`Nat`]), (1.1, [`Nat`])),
  cert: (expect: "⦇Q⦈setify est(R)", src: "L(N(Nat))", tgt: "L(Nat)", split: "", sigs: ("setify": "N(x)⟶E(x)", "⦇⦈": "L(N(x))⟶N(L(x))")))

// ---- Chain C, generated.  `F` is CURRIED to the unary `F(NA,−)`, so its wire is a functor and the algebra
// may die ON `N` instead of reaching past it; `trans` and `zip` are the only crossings left.
#let cc1 = dpanel(2.2, 5.6, 3.75,
  ((2.812, 1.1, "bot", none, none), (2.5, "top", 1.1, none, none), (3.125, "top", 1.1, none, none)),
  ((1.1, [`Q`], black, 2.5),),
  ((2.5, [`F`]), (3.125, [`N`]), (3.75, [`LA`])),
  ((2.812, [`N`]), (3.75, [`LA`])),
  obj: ((1.1, [`LA`]),),
  cert: (expect: "Q", src: "F(N(LA))", tgt: "N(LA)", split: "", sigs: ("Q": "F(N(x))⟶N(x)")))
#let cc2 = dpanel(6.6, 5.98, 4.13,
  ((2.5, 2.2, "bot", none, none), (2.877, 2.2, 1.1, [`F`], none), (2.5, "top", 2.2, none, none), (2.877, 4.4, 2.2, [`N`], none), (3.502, 4.4, 3.3, [`E`], none), (2.877, 5.5, 4.4, [`E`], none), (3.502, 5.5, 4.4, [`N`], none), (3.189, "top", 5.5, none, none)),
  ((5.5, [`moves`], black, 3.189, 3.189, "lax"), (4.4, [`trans`], black, 2.877, 3.1895, "lax"), (3.3, [`est(R)`], black, 3.502), (2.2, [`zip`], black, 2.5, 2.6885, "lax"), (1.1, [`α`], black, 2.877)),
  ((2.5, [`F`]), (3.189, [`N`]), (4.13, [`LA`])),
  ((2.5, [`N`]), (4.13, [`LA`])),
  obj: ((5.5, [`LA`]), (4.4, [`LA`]), (3.3, [`LA`]), (2.2, [`LA`]), (1.1, [`LA`])),
  cert: (expect: "F(𝟙,moves trans N(est(R)))zip N(α)", src: "F(N(LA))", tgt: "N(LA)", split: "", sigs: ("moves": "N(x)⟶E(N(x))", "trans": "E(N(x))⟶N(E(x))", "zip": "F(N(x))⟶N(F(x))", "α": "F(LA)⟶LA!lean=lean:AOP.A5_5.Freyd.Alg.InitialAlgebra.α@c4c898e2")))

// B&dM §7.4, p. 183.  Read as a definition, the fusion condition names `Q`; opening the coproduct
// of maps turns it into the program.
#disp[#calc-table(
  Thm[`Q=[N(wrap),(𝟙×moves trans N(est(R))) zip' N(cons)]` \
    #src[at the last column `Q` starts one path per row, and at each earlier one it puts each square in
     front of the cheapest of the three kept paths it can step to — the algebra @cyl-laws's last
     step folds]],
    // lean:AOP.A7_4_Cylinder.cyl_step@4930da05
  table.header([*circuit* — the fork is `F(NA,N(LA))=NA+NA×N(LA)`], [*Hinze–Marsden*]),

  [#vstep([], cyp(cyrun([`F(NA,N(LA))`], [`N(LA)`], (cb-Q,)), s: 88%), [])],
  [#cc1],

  [#vstep(EQ, cyp(cyrun([`F(NA,N(LA))`], [`N(LA)`], (cb-Fmtn, cb-zip, cb-Nal)), s: 74%),
    [#src[the fusion condition @cyl-fusion read as a definition,
 ]])],
     // lean:AOP.A7_4_Cylinder.Q@2b4dd374
  [#cc2],

  [#vstep(EQ, cyp(cyfork((cb-Nwrap,), (cb-moves, cb-trans, cb-Nest), cb-zipp, (cb-Ncons,)), s: 78%),
    [#src[`zip=𝟙+zip'`, `α=[wrap,cons]`]])],
  // A coproduct is a case split, not a composite of functors: Hinze–Marsden has no wiring for it.
  [],
)]<cyl-step>

// B&dM §7.4, p. 182.  The `E` the fold builds is killed earlier at every step, until @cyl-step's
// algebra never builds it: that migration is what the right column draws.
#disp[#calc-table(
  // B&dM p.179: "Show how the dynamic programming approach to exhaustive search allows a path of least
  // cost to be found in O(n × m) time."
  Thm[`paths est(R)⊒⦇Q⦈ setify est(R)` \
    #src[shortest paths on a cylinder: the dynamic programming approach to exhaustive search allows a path
     // cylinder row: B&dM §7.4, p. 182
     of least cost to be found in `O(n×m)` time; `Q` is @cyl-step's algebra.
 ]],
    // lean:AOP.A7_4_Cylinder.cyl_laws@4bbb7420
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], cyp(cyrun([`L N Nat`], [`L Nat`], (cb-paths, est-R-box))), [])],
  [#ca1],

  [#vstep(EQ, cyp(cyrun([`L N Nat`], [`L Nat`], (cb-fold, cb-setify, union-box, est-R-box))),
    [#src[@cyl-defn at `paths`]])],
  [#ca2],

  [#vstep(RQ, cyp(cyrun([`L N Nat`], [`L Nat`], (cb-fold, cb-setify, cb-Pest, est-R-box))),
    [#src[`P(est(R)) est(R)⊑union est(R)` — a minimum in each set, then a minimum of those;
     `R` transitive]])],
  [#ca3],

  [#vstep(RQ, cyp(cyrun([`L N Nat`], [`L Nat`], (cb-fold, cb-Nest, cb-setify, est-R-box))),
    [#src[`setify` lax natural]])],
  [#ca4],

  [#vstep(RQ, cyp(cyrun([`L N Nat`], [`L Nat`], (cb-foldQ, cb-setify, est-R-box))),
    [#src[@cata-fusion at @cyl-fusion]])],
  [#ca5],
)]<cyl-laws>

// ---- Chain B, generated.  `est(R)` is the one bead BOTH sides carry, and the base functor's own
// bead travels past it: `gen` above it on the left, `Q` below it on the right.
#let cb1 = dpanel(3.3, 6.23, 4.38,
  ((2.812, 2.2, "bot", none, none), (2.5, "top", 2.2, none, none), (3.125, "top", 2.2, none, none), (3.75, "top", 1.1, none, none)),
  ((2.2, [`gen`], black, 2.5), (1.1, [`est(R)`], black, 3.75)),
  ((2.5, [`F`]), (3.125, [`N`]), (3.75, [`E`]), (4.38, [`LA`])),
  ((2.812, [`N`]), (4.38, [`LA`])),
  obj: ((2.2, [`LA`]), (1.1, [`LA`])),
  cert: (expect: "gen N(est(R))", src: "F(N(E(LA)))", tgt: "N(LA)", split: "", sigs: ("gen": "F(N(x))⟶N(x)")))
#let cb2 = dpanel(3.3, 6.23, 4.38,
  ((2.812, 1.1, "bot", none, none), (2.5, "top", 1.1, none, none), (3.125, "top", 1.1, none, none), (3.75, "top", 2.2, none, none)),
  ((2.2, [`est(R)`], black, 3.75), (1.1, [`Q`], black, 2.5)),
  ((2.5, [`F`]), (3.125, [`N`]), (3.75, [`E`]), (4.38, [`LA`])),
  ((2.812, [`N`]), (4.38, [`LA`])),
  obj: ((2.2, [`LA`]), (1.1, [`LA`])),
  cert: (expect: "F(𝟙,N(est(R)))Q", src: "F(N(E(LA)))", tgt: "N(LA)", split: "", sigs: ("Q": "F(N(x))⟶N(x)")))

// B&dM §7.4, p. 183.  `gen` kills the base functor before the minimum is taken inside the
// tuple; the right-hand side kills it after, and that swap is the whole step.
#disp[
#calc-table(
  // B&dM p.182: "The condition for fusion is N(min R)·generate ⊇ Q·F(id, N(min R)), and we can use this to
  // derive a definition of Q"
  Thm[`gen N(est(R))⊒F(𝟙,N(est(R)))Q` \
    #src[fusion: the condition for fusion in @cyl-laws's last step, used to derive a definition of `Q`.
 ]],
    // lean:AOP.A7_4_Cylinder.cyl_fusion@10671cc3
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], cyp(cyrun([`F(NA,N(E(LA)))`], [`N(LA)`], (cb-gen, cb-Nest)), s: 88%),
    [])],
  [#cb1],

  [#vstep(RQ, cyp(cyrun([`F(NA,N(E(LA)))`], [`N(LA)`], (cb-FNest, cb-Q)), s: 88%),
    [#src[(7.13), then `zip`, `trans`, `moves` lax natural]])],
  [#cb2],
)
#align(center, block(inset: (y: 4pt))[#src[(7.13) is `F(𝟙,est(R))α⊑cp P(α) est(R)`, @mon-thm71 at the
  map `α` with $frac(#[`F(𝟙,∋)α`], ∋)$ `=cp P(α)`: extending every path in a set and then taking a
  minimum is beaten by extending one minimum. It is the crux here, not the greedy theorem.
 ]])
  // lean:AOP.A7_4_Cylinder.cyl_7_13@5224efdc
]<cyl-fusion>

// Its own page: the section opens with a long definition display and was starting mid-page.
#pagebreak(weak: true)
