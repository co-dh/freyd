#import "../note-prelude.typ": *
#show: note-chapter.with(7)
// note-split: chapter 7 — this header is written by scripts/note-split and stripped by scripts/note-join
= Reduce in 𝒮et

// B&dM §3.1 "Banana-split", pp. 55–57.  The book writes `h · f` applicatively; every composite in the
// table is mirrored to `f h`, this note's diagram order.
#disp[#table(
  columns: (8.7cm, 4.5cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

  // cons-lists definition: B&dM p. 55
  [`listr A::=nil|cons(A,listr A)`],
  [#leant("Freyd.Alg.RelSet.ListRel.listRelator")],
  [The cons-lists over `A`, the datatype every row below folds.],

  [#leanf("Freyd.Alg.RelSet.ListRel.sum_cata")],
  // lean:AOP.A5_6_ListCombinators.sum_cata@9396e206
  [#leant("Freyd.Alg.RelSet.ListRel.sumR")],
  [`plus(a,b)=a+b`.],

  [#leanf("Freyd.Alg.RelSet.ListRel.length_cata")],
  // lean:AOP.A5_6_ListCombinators.length_cata@0cd685fc
  [#leant("Freyd.Alg.RelSet.ListRel.length_cata")],
  [`π₂` drops the head and keeps the count of the tail, `succ` adds one for the head.],

  [#leanf("Freyd.Alg.RelSet.ListRel.averageR")],
  // lean:AOP.A5_6_ListCombinators.averageR@1af775cf
  [#leant("Freyd.Alg.RelSet.ListRel.averageR")],
  [`div(m,n)=m/n`, with `div(0,0)=0` so `average` is total. Traverses the list twice.],

  [banana-split law \
   #leanf("Freyd.Alg.pair_relCata_eq_relCata_pair")],
  // lean:AOP.A5_5.pair_relCata_eq_relCata_pair@8e98edce
  [#leant("Freyd.Alg.pair_relCata_eq_relCata_pair")],
  [Any fork of folds is a single fold, hence one traversal — `F` the base functor.],

  [what it reduces to \
   #leanf("Freyd.Alg.pair_relCata_hom")],
  // lean:AOP.A5_5.pair_relCata_hom@93cbc99a
  [#leant("Freyd.Alg.pair_relCata_hom")],
  [All that @cata-defining leaves to check: the fork satisfies the defining equation.],

  [the instance \
   #leanf("Freyd.Alg.RelSet.ListRel.pair_sum_length_cata")],
  // lean:AOP.A5_6_ListCombinators.pair_sum_length_cata@820d9011
  [#leant("Freyd.Alg.RelSet.ListRel.pair_sum_length_cata")],
  [`pluss(a,(b,n))=(a+b,n+1)`, so `average` runs in one pass.],

  // preds row: B&dM Ex 3.6 (p. 57); uses Ex 3.4
  [`preds n=[n,n−1,…,1]`],
  [#leant("Freyd.Alg.RelSet.ListRel.predsR")],
  [apply the earlier special case to write `preds` as `⦇k⦈π₁`.],
)]<cata-examples>

// The square is the product's universal property at `T`, the string diagram the row above it: one
// fold bead, the algebra falling past it, exactly as in @cata-defining.
#disp[#pair(
  leancd("Freyd.Alg.relCata_pair_beta"),
  row((
    lean("Freyd.Alg.pair_relCata_hom"),
  )),
  [#leanf("Freyd.Alg.pair_relCata_eq_relCata_pair") #h(6pt) #src[banana split]],
  // lean:AOP.A5_5.pair_relCata_eq_relCata_pair@8e98edce
)]<banana-split>

// Its own page: the heading was left orphaned at the foot of the page before it.
#pagebreak(weak: true)
== Fokkinga's mutual recursion theorem

// Algebras lettered `h`, `k` as in @cata-examples; the display below reuses the letters for the
// general case, which is what the last bullet contrasts the product with.
- `F-Alg(𝒜)` — the algebras and their homomorphisms — has binary products whenever `𝒜` does, and the
  forgetful `U : F-Alg(𝒜)⟶𝒜` *creates* them: the product of `h : FA⟶A` and `k : FB⟶B` is
  carried by `A×B`, with structure `⟨F(π₁)h,F(π₂)k⟩ : F(A×B)⟶A×B`.
- `π₁` and `π₂` are homomorphisms out of it, and `⟨p,q⟩ : X⟶A×B` is a homomorphism *iff* `p`
  and `q` both are — substitute the structure and compare the two forks component by component.
- The banana-split law of @cata-examples IS that product's universal property read at the initial
  algebra: `⦇h⦈` and `⦇k⦈` are the unique homomorphisms to `(A,h)` and `(B,k)`, so their fork is the
  unique homomorphism into the product, which is `⦇⟨F(π₁)h,F(π₂)k⟩⦈`.
// Fokkinga bullet: B&dM's Ex 3.4 (p. 58) is the other special case
- Fokkinga's theorem is *strictly more general* and is not that product: in @fokkinga the two arrows
  leave `F(A×B)`, not `FA` and `FB`, so each sees BOTH components. The product is the case where
  they factor as `F(π₁)h` and `F(π₂)k`. What
  it says: *any algebra on a product carrier is folded by a fork*.

// B&dM Ex 3.8 (p. 58), ONE SQUARE PER CONJUNCT: `h` and `k` leave `F(A × B)` for different corners,
// so a single square cannot carry both.  Dashed blue as in @cata-defining — the arrows uniqueness gives.
#disp[#capbox(
  leancd("Freyd.Alg.pair_eq_relCata_pair_iff.lhs"),
  [#leanf("Freyd.Alg.pair_eq_relCata_pair_iff")],
  // lean:AOP.A5_5.pair_eq_relCata_pair_iff@beb351af
)]<fokkinga>

== Ruby triangles

// B&dM §3.2, pp. 58–59.  The book writes `cons · (id × listr f)` applicatively; every composite in the
// table is mirrored by `h·f ↦ f h` into this note's diagram order.
#disp[#table(
  columns: (5.8cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*stage*], [*definition*]),

  // tri-evolution stages: B&dM pp. 58-59
  [informally],
  [`tri(f)[a₀,a₁,…,aᵢ,…,aₙ]=[a₀,f(a₁),…,fⁱ(aᵢ),…,fⁿ(aₙ)]`],

  [for cons-lists],
  [`tri(f)=⦇[nil,(𝟙×listr(f)) cons]⦈`],

  [with the base functor named],
  [`F(A,B)=1+A×B`, `α=[nil,cons]`, so `tri(f)=⦇F(𝟙,listr(f))α⦈`],

  [abstractly],
  [`F` a bifunctor with initial type `(α,T)`: #leanf("Freyd.Alg.tri_defn")],
  // lean:AOP.A5_5_TypeFunctor.tri_defn@b4b44137
)]<tri-evolution>

For the definition to make sense `f : A⟶A` is required, and then `tri(f) : TA⟶TA`.

// The book's top arrow points LEFT because it composes applicatively, so mirroring it into diagram
// order swaps the legs: `⦇g⦈` post-composes `tri(f)`, hence leaves the RIGHT `T A` (B&dM p. 59).
#disp[#pair(
  leancd("Freyd.Alg.tri_cata_fusion"),
  row((
    lean("Freyd.Alg.tri_cata_fusion"),
  )),
  [#leanf("Freyd.Alg.tri_cata_fusion")],
  // lean:AOP.A5_5_TypeFunctor.tri_cata_fusion@d3864107 lean:AOP.A5_5_TypeFunctor.tri@864792f0
)]<horner>

// horner paragraph: B&dM pp. 58-59; B&dM call it Horner's rule because for cons-lists it is the
// schoolbook method for evaluating a polynomial.
@horner is Horner's rule, generalised from cons-lists to any initial type. Fusion reduces it to
`F(𝟙,T(f))α⦇g⦈=F(𝟙,⦇g⦈)F(𝟙,f)g`.

// Its own page: the section is one table long and the heading was left orphaned at the foot of the
// page before it once the F-Alg bullets above pushed the table over the break.
#pagebreak(weak: true)
== Depth of a tree

// B&dM p. 60, mirrored to diagram order: the book writes `depths = tri succ · tree zero` and
// `depth = max · depths`.
#disp[#table(
  columns: (3.0cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [the datatype],
  [`tree A::=tip(A)|bin(tree A,tree A)`, base functor `F(A,B)=A+B×B`, \
   initial type `([tip,bin],tree)`],

  [the fold],
  [`⦇[g,h]⦈` is the unique `f` with `f(tip(a))=g(a)` and `f(bin(x,y))=h(f(x),f(y))`],

  [`tree(f)`],
  [`tree(f)=⦇F(f,𝟙) [tip,bin]⦈`; pointwise `tree(f)(tip(a))=tip(f(a))` and \
   `tree(f)(bin(x,y))=bin(tree(f)(x),tree(f)(y))`],

  [`max`],
  [`max=⦇[𝟙,bmax]⦈`, where `bmax(a,b)` is the larger of `a` and `b`],

  [`depths`],
  [`depths=tree(zero) tri(succ)` — replaces every tip by its depth in the tree, `zero` the
   constant function returning 0 and `succ` the successor],

  [`depth`],
  [`depth=depths max`],
)]<tree-depth>

#pagebreak(weak: true)
