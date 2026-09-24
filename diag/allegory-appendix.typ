// `#include`d by allegory-axioms.typ, which does not share its scope: the helpers must be re-imported.
#import "note-style.typ": definition, disp, P, d, src, Thm, calc-table, EQ, vstep
#import "draw.typ": zline, zpair, zsqc, zstep, SQ, RQ
#import "dpanel.typ": dpanel, hm-meta
#import "note-prelude.typ": lean, leanc, leant, leanf

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

== `P(est(R)) est(R)=P(dom(est(R))) union est(R)`

// B&dM (7.12), `R` a preorder.  `⊑` puts the domain in for free; `⊒` is @est-79 at `S := est(R)`
// and then the two halves the book leaves as exercises.
#disp[
#zline(
  zsqc(`P(est(R)) est(R)`, none),
  zstep(op: sym.eq, under: true)[`dom(est(R)) est(R)=est(R)`],
  zsqc(`P(dom(est(R)) est(R)) est(R)`, none),
)
#zline(
  zstep(op: sym.eq, under: true)[`P` a relator],
  zsqc(`P(dom(est(R)))P(est(R)) est(R)`, none),
  zstep(op: sym.subset.eq.sq, under: true)[@est-711],
  zsqc(`P(dom(est(R))) union est(R)`, none),
)
]<est-712>

#disp[
#zline(
  zsqc(`P(dom(est(R))) union est(R)`, `P(est(R)) est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[@est-79 at `S:=est(R)`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(dom(est(R))) union est(R)`, `∋est(R)`),
        zsqc(`∈P(dom(est(R))) union est(R)`, `est(R)R°`)),
)
#zline(
  zsqc(`P(dom(est(R))) union est(R)`, `∋est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[`P(dom(est(R)))⊑𝟙`],
  zsqc(`union est(R)`, `∋est(R)`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`T(U∩V)⊑TU∩TV`, `·∋⊣`$frac(#box(width: 8pt), ∋)$, @est-73],
  zsqc(`(∋∋)∩(∈\(∈\R°))`, `∋est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[modular law],
  zsqc(`∋(∋∩(∈(∈\(∈\R°))))`, `∋(∋∩(∈\R°))`, name: "counit of T·⊣T\\"),
)
#zline(
  zsqc(`∈P(dom(est(R))) union est(R)`, `est(R)R°`),
  zstep(op: sym.arrow.l.double, under: true)[`∈` lax natural],
  zsqc(`dom(est(R))∈union est(R)`, `est(R)R°`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`dom(est(R))⊑est(R) est(R)°`],
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
  [#leant("Freyd.Alg.RelSet.CL.F")],
  [The base functor: one square of the new column, alone or in front of the path so far.],

  [`L=list⁺`],
  [#leant("Freyd.Alg.RelSet.ListRel.nelistRelator")],
  [A path is a non-empty list of squares, one per column crossed.],

  [`α` the initial algebra],
  [#leant("Freyd.Alg.RelSet.CL.alphaR")],
  [`α(5)=[5]` and `α(1,[5])=[1,5]`: a path is started by one square, or extended by one.],

  [`N` \ the `n`-tuple relator],
  [#leant("Freyd.Alg.RelSet.Tuple.tupleRelator")],
  [One component per row of a column, so the fold carries `n` answers at once.],

  [`R≜sum≤sum°`],
  [#leant("Freyd.Alg.RelSet.Tuple.costLE")],
  [The cost of a path, which the cheapest minimises.],

  [`setify`],
  [#leant("Freyd.Alg.RelSet.Tuple.setify")],
  [`setify(1,2,3,4)={1,2,3,4}` — which row a component came from is forgotten.],

  [`moves`],
  [#leant("Freyd.Alg.RelSet.Tuple.moves")],
  [`moves(x)={up(x),x,down(x)}` — rotated up, unrotated, rotated down.],

  [`trans`],
  [#leant("Freyd.Alg.RelSet.Tuple.transT")],
  [`trans{(a,b,c),(x,y,z)}=({a,x},{b,y},{c,z})` — component `k` of the result is the set of the `k`-th components.],

  [`zip`],
  [#leant("Freyd.Alg.RelSet.Tuple.zipF")],
  [`zip((1,2,3,4),({[5]},{[6]},{[7]},{[8]}))=((1,{[5]}),(2,{[6]}),(3,{[7]}),(4,{[8]}))`.],

  [`cp≜` $frac(#[`F(𝟙,∋)`], ∋)$],
  [#leant("Freyd.Alg.cpMap")],
  [`cp(1,{[5],[6],[8]})={(1,[5]),(1,[6]),(1,[8])}`.],

  [#leanf("Freyd.Alg.Cylinder.gen")
 #src[]],
   // lean:AOP.A7_4_Cylinder.gen@07f901a6
  [#leant("Freyd.Alg.Cylinder.gen")],
  [`gen((1,2,3,4),({[5]},{[6]},{[7]},{[8]}))` is worked out in @cyl-gen.],

 [#leanf("Freyd.Alg.Cylinder.paths") #src[]],
  // lean:AOP.A7_4_Cylinder.paths@e6d14f30
  [#leant("Freyd.Alg.Cylinder.paths")],
  [`paths[(1,2,3,4),(5,6,7,8)]` is the union of @cyl-gen's four sets: 12 paths, 3 from each entry row.],

  [the specification \ `paths est(R)`],
  [#leant("Freyd.Alg.RelSet.Tuple.cheapest")],
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
  lean("Freyd.Alg.Cylinder.cyl_cp.rhs"),
  lean("Freyd.Alg.Cylinder.cyl_cp_prod.rhs"),
  lean("Freyd.Alg.Cylinder.cyl_cp_const.rhs"),

  src[`cp` on all of `F(A,E(L A))`],
  src[the `A×−` summand: `∋` picks one path, `𝟙%∋` collects the results],
  src[the `A` summand, no `E` to distribute: `𝟙%∋` alone, `a↦{a}`],
))]<cp-diag>
   // lean:AOP.A7_4_Cylinder.cyl_cp@d2f022d7
   // lean:AOP.A7_4_Cylinder.cyl_cp_prod@7f182a1e
   // lean:AOP.A7_4_Cylinder.cyl_cp_const@94a6c342

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

#disp[#align(center, lean("Freyd.Alg.Cylinder.gen"))]<gen-diag>

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
  lean("Freyd.Alg.Cylinder.gen_cata_comm.lhs"),
  EQ,
  lean("Freyd.Alg.Cylinder.gen_cata_comm.rhs"),

  src[`α` puts the column back on the list, then the fold reads all of it],
  [],
  src[the fold reads the rest under `F`, then one `gen` puts the column in front],
))]<fold-diag>
   // lean:AOP.A7_4_Cylinder.gen_cata_comm@1297cc13
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

// ---- HINZE-MARSDEN, generated by `scripts/diagram --fold-list`.  A wire is a FUNCTOR: the object
// wire carries `L(N(Nat))` down to `L(Nat)` and beside it ride `N` the tuple and `E` the path set.
#let ca1 = lean("Freyd.Alg.Cylinder.cyl_laws_step4.rhs")
#let ca2 = lean("Freyd.Alg.Cylinder.cyl_laws_step4.lhs")
#let ca3 = lean("Freyd.Alg.Cylinder.cyl_laws_step3.lhs")
#let ca4 = lean("Freyd.Alg.Cylinder.cyl_laws_step2.lhs")
#let ca5 = lean("Freyd.Alg.Cylinder.cyl_laws_step1.lhs")

// ---- Chain C, generated.  `F` is CURRIED to the unary `F(NA,−)`, so its wire is a functor and the algebra
// may die ON `N` instead of reaching past it; `trans` and `zip` are the only crossings left.
#let cc1 = lean("Freyd.Alg.Cylinder.cyl_step.lhs")
#let cc2 = lean("Freyd.Alg.Cylinder.Q")

// B&dM §7.4, p. 183.  Read as a definition, the fusion condition names `Q`; opening the coproduct
// of maps turns it into the program.
#disp[#calc-table(
  Thm[`Q=[N(wrap),(𝟙×moves trans N(est(R))) zip' N(cons)]` \
    #src[at the last column `Q` starts one path per row, and at each earlier one it puts each square in
     front of the cheapest of the three kept paths it can step to — the algebra @cyl-laws's last
     step folds]],
  table.header([*circuit* — the fork is `F(NA,N(LA))=NA+NA×N(LA)`], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.Cylinder.cyl_step.lhs"), [])],
  [#cc1],

  [#vstep(EQ, leanc("Freyd.Alg.Cylinder.Q"),
    [#src[the fusion condition @cyl-fusion read as a definition,
 ]])],
  [#cc2],

  [#vstep(EQ, leanc("Freyd.Alg.Cylinder.cyl_step.rhs"),
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
    // lean:AOP.A7_4_Cylinder.cyl_laws@d824dc1f
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.Cylinder.cyl_laws_step4.rhs"), [])],
  [#ca1],

  [#vstep(EQ, leanc("Freyd.Alg.Cylinder.cyl_laws_step4.lhs"),
    [#src[@cyl-defn at `paths`]])],
  [#ca2],

  [#vstep(RQ, leanc("Freyd.Alg.Cylinder.cyl_laws_step3.lhs"),
    [#src[`P(est(R)) est(R)⊑union est(R)` — a minimum in each set, then a minimum of those;
     `R` transitive]])],
  [#ca3],

  [#vstep(RQ, leanc("Freyd.Alg.Cylinder.cyl_laws_step2.lhs"),
    [#src[`setify` lax natural]])],
  [#ca4],

  [#vstep(RQ, leanc("Freyd.Alg.Cylinder.cyl_laws_step1.lhs"),
    [#src[@cata-fusion at @cyl-fusion]])],
  [#ca5],
)]<cyl-laws>

// ---- Chain B, generated.  `est(R)` is the one bead BOTH sides carry, and the base functor's own
// bead travels past it: `gen` above it on the left, `Q` below it on the right.
#let cb1 = lean("Freyd.Alg.Cylinder.cyl_fusion.rhs")
#let cb2 = lean("Freyd.Alg.Cylinder.cyl_fusion.lhs")

// B&dM §7.4, p. 183.  `gen` kills the base functor before the minimum is taken inside the
// tuple; the right-hand side kills it after, and that swap is the whole step.
#disp[
#calc-table(
  // B&dM p.182: "The condition for fusion is N(min R)·generate ⊇ Q·F(id, N(min R)), and we can use this to
  // derive a definition of Q"
  Thm[`gen N(est(R))⊒F(𝟙,N(est(R)))Q` \
    #src[fusion: the condition for fusion in @cyl-laws's last step, used to derive a definition of `Q`.
 ]],
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.Cylinder.cyl_fusion.rhs"),
    [])],
  [#cb1],

  [#vstep(RQ, leanc("Freyd.Alg.Cylinder.cyl_fusion.lhs"),
    [#src[(7.13), then `zip`, `trans`, `moves` lax natural]])],
  [#cb2],
)
#align(center, block(inset: (y: 4pt))[#src[(7.13) is `F(𝟙,est(R))α⊑cp P(α) est(R)`, @mon-thm71 at the
  map `α` with $frac(#[`F(𝟙,∋)α`], ∋)$ `=cp P(α)`: extending every path in a set and then taking a
  minimum is beaten by extending one minimum. It is the crux here, not the greedy theorem.
 ]])
  // lean:AOP.A7_4_Cylinder.cyl_7_13@41e3cf5d
]<cyl-fusion>

// Its own page: the section opens with a long definition display and was starting mid-page.
#pagebreak(weak: true)
