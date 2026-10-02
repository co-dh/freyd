#import "../note-prelude.typ": *
#show: note-chapter.with(1)
// note-split: chapter 1 — this header is written by scripts/note-split and stripped by scripts/note-join
#import "../shared-laws.typ": *
= Notation

Traditionaly Adjunction F -| G is defined as $F(x) <= y$ iff $x <= G(y)$, and you derive laws like this:

$ F(x) <= F(x) quad &==> quad x <= G(F(x)) quad &&==> quad F(x) <= F(G(F(x))) \
  G(y) <= G(y) quad &==> quad F(G(y)) <= y quad &&==> quad G(F(G(y))) <= G(y) $


By define $X: * |-> x$, $Y: *|->y$ and use diagram order, application can be replaced by composition:
     $X F<=Y$ iff $X<=Y G$
// A table, not a list: the second column is what hangs `rewrite`'s name out at the right.  The marker
// rides INSIDE the text cell — a column of its own would centre it, dropping it below the first line.
#disp[#table(
  columns: (1fr, auto),
  stroke: (x: none, y: 0.4pt + luma(215)),
  inset: (x: 6pt, y: 7pt),
  align: (left + horizon, right + horizon),
  [- write $F$ as #zw("/") , $G$ as #zw("\\")], [],
  [- render $a <= b$ as #h(0.8em) #zsq("a", "b")], [],
  [- *rewrite* $X<=X F$ as $1<=F$], [],
)]<notation-marks>

#znamed("adj", zsq("X/", "Y"), $=$, zsq("X", "Y\\"))

#zderiv(
  (zsq("X/", "X/"), zstep[adj], zsq("X", "X/\\"), zstep("rewrite", op: sym.eq),
   zsq("*", "/\\", name: "unit")),
  (
    ([put #zw("\\") on left],  zsq("\\", "\\/\\")),
    ([put #zw("/") on right],  zsq("/", "/\\/")),
  ),
)

#zderiv(
  (zsq("Y\\", "Y\\"), zstep[adj], zsq("Y\\/", "Y"), zstep("rewrite", op: sym.eq),
   zsq("\\/", "*", name: "counit")),
  (
    ([put #zw("/") on left],   zsq("/\\/", "/")),
    ([put #zw("\\") on right], zsq("\\/\\", "\\")),
  ),
)

now we have #zw("/\\/") $=$ #zw("/") and #zw("\\/\\") $=$ #zw("\\"), and you just discovered string
diagrams.


#pagebreak(weak: true)
== Adjunctions <sec-adj>

// The type column says which poset a row's `⊑` is read in — the first two rows are 1-cells of Rel, the
// rest monotone maps between hom-posets.  Sections, not an invented `•`: `•` reads as a composition dot.
// #src[Both halves of a row are written as sections — the operator stays and its missing argument is
// the gap: `·S` is `R ↦ R S`, `/S` is `T ↦ T/S`, `S\` is `Y ↦ S\Y`. Composition is juxtaposition, so
// the dot is written only in the rows where nothing else marks the gap.]

#law-adj-all

// Row parameters: `S`/`f` are `B ⟶ C` in the `·S`, `·f` rows and `A ⟶ B` in the `S·`, `f°·` ones;
// `Cor A` is the coreflexives on `A`, so the `A`, `B` of the `𝓓`, `𝓡` rows are coreflexives.

== Composing adjunctions <sec-compose>


// Why every cell below is an equation and not a `⊑`: the chain runs down one composite and back up the
// other, so both are right adjoints of the one left adjoint `X ↦ f°(X T)`, and that one is unique.
#disp[
#zline(
  zsqc(`X`, `f(R/T)`, name: "f a map"),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc(`f°X`, `R/T`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·T⊣/T`],
  zsqc(`(f°X)T`, `R`),
)
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[associativity],
  zsqc(`f°(XT)`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc(`XT`, `fR`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·T⊣/T`],
  zsqc(`X`, `(fR)/T`),
)
#zline(
  zstep(under: true)[indirect equality],
  zsqc(`f(R/T)`, `(fR)/T`, eq: true),
)
#align(center, block(inset: (y: 3pt))[#leanf("Freyd.Alg.map_comp_div") #src[]])
// lean:AOP.A4_4.map_comp_div@3b1816a2
]<adj-cross-why>

#law-adj-cross

// Proved in the repository: div_comp_assoc, leftDiv_div, leftDiv_comp, leftDiv_inter, leftDiv_div_recip,
// map_comp_div, div_comp_recip_map, div_inter_eq, recip_*, {union_comp,comp_union}_distrib, zero_*.

== Adjoint triples

Beyond `∪⊣Δ⊣∩`, which §@sec-adj already carries as two rows, the table holds one adjoint triple with
content: `∃_f⊣f*⊣∀_f` along a map `f`, once on each side of the composite.
#src[`f : A⟶B` throughout this subsection.]

#law-triple-chains

// `map_shunt_right`, AOP/A4_2.lean:223; `map_shunt_left`, AOP/A4_2.lean:241.
The first two links of each chain are the map shunting rules, and the third is §@sec-adj's division row read at a chosen divisor: `·S⊣/S` at `S:=f°`, and
`S·⊣S\` at `S:=f`.

The third link is not the first over again. For a map `f`, `/f` collapses to `·f°`; being a map is
exactly what that collapse spends
// `div_comp_recip_map`, AOP/A4_4.lean:378.
#src[#leanf("Freyd.Alg.div_comp_recip_map")] — `f°` is not a map, so
// lean:AOP.A4_4.div_comp_recip_map@bc41ec1a
`/f°` does not collapse in turn, and the three operators stay distinct. On `Rel(𝕀,A)=PA` they
are the image triple:

#disp[#table(
  columns: 3, align: left + horizon, inset: 4pt, stroke: 0.4pt + luma(190),
  table.header([*operator*], [*acts by*], [*name*]),
  [`·f`], [`S↦f[S]`], [direct image, `∃_f`],
  [`·f°`], [`T↦f⁻¹[T]`], [inverse image, `f*`],
  [`/f°`], [`S↦{b : f⁻¹(b)⊆S}`], [`∀_f`],
)]<triple-image>

§@sec-adj's `𝓓⊣·⊤` is this same chain along the projection `A⊗B⟶A`, read through
`Rel(A,B)=P(A⊗B)`: `𝓓R={(a,a) : ∃b. aRb}`, `A⊤` is the relation that ignores `b`
altogether, and the third link is `R↦𝟙∩R/⊤={(a,a) : ∀b. aRb}`.

#disp[#block(inset: (y: 6pt))[`𝓓⊣·⊤⊣𝟙∩·/⊤`
  // The same: two links, two `↔` statements, one hand-typed chain citing both.
  // lean:AOP.A5_2.dom_adj_comp_topMor@874d1a3e lean:AOP.A5_2.comp_topMor_adj_id_inter_div_topMor@794c6795
]]<triple-dom>

Three is where it stops, and one map breaks both ends. Take `A={a₁,a₂}` and `B={b}`:
`f[{a₁}]∩f[{a₂}]={b}` while `f[{a₁}∩{a₂}]=∅`, so `·f` does not preserve meets and has no
left adjoint, and the same two subsets give `∀_f({a₁} ∪ {a₂})={b}` against
`∀_f{a₁} ∪ ∀_f{a₂}=∅`, so `/f°` does not preserve joins and has no right adjoint. A monic `f`
restores the binary case and no more — `⊤f` still reaches only `im f`, and `∀_f𝟘=B∖im f` is
still not `𝟘`. The chain extends only when `f°` is a map as well, and then `/f°=·f°°=·f` and it
repeats forever. For an `S` with neither `S` nor `S°` a map there is no triple at all: `·S⊣/S` is
two links and stops.

#src[The rows that chain forever say nothing by it: `°` is an order-isomorphism of hom-posets, so it
is adjoint to itself on both sides and `°⊣°⊣°` has no end, and §@sec-adj's other row of that kind,
`⟜◁⊣▷⊸`, goes the same way.]

#pagebreak(weak: true)
