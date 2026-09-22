#import "../note-prelude.typ": *
#show: note-chapter.with(16)
// note-split: chapter 16 — this header is written by scripts/note-split and stripped by scripts/note-join
= Greedy Algorithms <sec-greedy>

== Theory

// B&dM §10.1, p. 245.  Theorem 9.2 with `est(Q)` for `thin(Q)`: the same hypotheses, a much stronger
// conclusion, and one far harder to refine into a program.
#disp[#definition[
`h`, `T`, `R`, `H`, `M` as in @dp-defn; #h(4pt) additionally `Q` a *connected* preorder on the sets
$frac(#[`T°`], ∋)$ returns, so that $frac(#[`T°`], ∋)$ `est(Q)` is entire.
]]<greedy-defn>

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.greedy_dp") \
    #src[the same optimum reached by keeping ONE decomposition at each step, so that no set is ever
 carried and the recursion runs on values alone #h(4pt) ]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.greedy_dp_step1.rhs"),
    [#src[the problem to be solved, `H≜⦇T⦈°⦇h⦈` — @greedy-defn]])],
  [#lean("Freyd.Alg.greedy_dp_step1.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.greedy_dp.lhs.body"),
    // dp-shrink row: Theorem 10.1
    [#src[]])],
  // `est(Q) : E(FA)⟶FA` kills the SET but not the `F` under it, so its wire spans the `E` lane
  // down to the object wire, crossing `F` — the whole difference from @dp-laws' second row.
  [#lean("Freyd.Alg.greedy_dp.lhs.body")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.SL.est_arm₂_le.lhs"),
    // lean:AOP.A9_1.est_summand_le@1efecafb
    [#src[Proposition 10.1 at `T=[V₁,V₂]`, `h=[U₁,U₂]`, `Q=Q₁+Q₂`, `V₂V₁°=𝟘`]])],
  // The branch, not the conditional; nothing survives outside the set here, so `est(Qᵢ)` lands on
  // the object wire.
  [#lean("Freyd.Alg.RelSet.SL.est_arm₂_le.lhs")],
)]<greedy-laws>

== The detab-entab problem

// B&dM §10.2, p. 246.  `V ≜ prefix° ∩ (fill fill°)` is the whole trick: a bare `prefix°` fails because
// a prefix of the expansion can be longer than the input once it crosses a tab stop.
#disp[#definition[
`detab≜⦇[nil,expand]⦈ : String⟶String` #src[]
// lean:AOP.A10_2_Detab.detab_cata@37355797
over snoc-lists, #h(4pt) `α≜[nil,snoc]`, #h(4pt)
`H=detab°`; #h(4pt) `expand (xs,a)=(a=TB→fill xs,xs⧺[a])`, #h(4pt)
`fill xs=xs⧺blanks (n−(col xs) mod n)`.

`col≜⦇[zero,count]⦈`, #h(4pt) `count (c,a)=(a=NL→0,c+1)`; #h(4pt) `TB` the tab, `BL` the
blank, `NL` the newline, tab stops every `n` columns.

`R≜length≤length°` #src[], #h(4pt)
// lean:AOP.A10_2_Detab.R@5b23da25
`U` the preorder with `a U b⟺a=TB∨a=b`, #h(4pt)
`V≜prefix°∩(fill fill°)` #src[], #h(4pt)
// lean:AOP.A10_2_Detab.V@b0fc79bc
`Q≜𝟙+(V×U)` #src[].
// lean:AOP.A10_2_Detab.Q@7a0a1541

`unfill xs` the shortest prefix of `xs` with `fill (unfill xs)=fill xs`; #h(4pt) `tbc` the trailing
blank count, #h(4pt) `triple≜⟨unfill entab,⟨tbc,col⟩⟩`.
]]<entab-defn>

// ONE WIRE, `String` to `String`; `F(X)h` is drawn as the ONE bead the formula writes,
// `(𝟙+(X×𝟙))[nil,snoc]`, so the `list` lane pinches twice rather than three times.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Detab.entab_laws"), #h(6pt) `entab=triple assocl π₁ (𝟙×blanks) cat` \
    #src[the shortest input `detab` expands to the given output is one pass along that output,
     holding each blank back and cashing the held blanks in for a tab wherever the column reaches a
     tab stop]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Detab.entab_laws.rhs"),
    [#src[the specification — @entab-defn; `detab entab=𝟙` and nothing
     shorter does]])],
  [#lean("Freyd.Alg.RelSet.Detab.entab_laws.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Detab.entab_laws.lhs.body"),
    [
     // entab-thin row: Theorem 10.1
     #src[at `Q≜𝟙+(V×U)`
 #src[]: one character of input is
      // lean:AOP.A10_2_Detab.entab_thin_condition@4bf50608
      decided at each step. `F(⊤,R)α⊑αR`#src[].
      // lean:AOP.A10_2_Detab.entab_mono@b7c30f2e
      `detab prefix⊑R° detab` is
 FALSE #src[,
      // lean:AOP.A10_2_Detab.detab_prefix_false@5fe54dc9
 ] — at `n=8`,
      // lean:AOP.A10_2_Detab.detab_len_of_short@66be497e
      `detab [a,b,c,d,e,TB]=[a,b,c,d,e,BL,BL,BL]`, whose prefix
      `[a,b,c,d,e,BL,BL]` is longer than any input giving it, and `detab V°⊑R° detab`
 #src[]
      // lean:Freyd.Alg.RelSet.Detab.detab_V@332fe8ac lean:AOP.A10_2_Detab.entab_V@ff19c265
      holds. `expand V°⊑expand ∪ (π₁V°)`
 #src[] — shortening the output either leaves the
      // lean:AOP.A10_2_Detab.expand_V_step@1e653239
      last step alone or discards it]])],
  // `[nil,expand]°` opens `−×Char` inside the set the singleton opened; `est(Q)` kills that set but
  // not the `F` under it, so its wire spans down to the object wire, crossing `F`.
  [#lean("Freyd.Alg.RelSet.Detab.entab_laws.lhs.body")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Detab.entab_branch.lhs"),
    [#src[Proposition 10.1: `nil` and `expand` have disjoint ranges. The greedy step is to emit
      a tab whenever a tab is legal, consuming all the blanks back to the previous tab stop]])],
  [#lean("Freyd.Alg.RelSet.Detab.entab_branch.lhs")],

  [#vstep(EQ, [],
    [`entab xs=entab (unfill xs)⧺blanks (tbc xs)` #h(4pt) #src[(10.1)] \
     #src[what makes `triple≜⟨unfill entab,⟨tbc,col⟩⟩` a snoc-list reduce: the output splits at the
      last tab stop]])],
  // No picture: `entab` is here read on points, and the equation relates two strings, not two
  // objects the panels carry.
  [],

  [#vstep(EQ, [],
    [`triple=⦇[base,op]⦈`, #h(4pt) `entab=triple assocl π₁ (𝟙×blanks) cat` \
     `base` returns `([],(0,0))`, #h(4pt) `op ((xs,(t,c)),a)=` \ #h(10pt)
     `(a=BL∧(c+1) mod n≠0→(xs,(t+1,c+1)),` #h(4pt) `a=BL→(xs⧺[TB],(0,c+1)),` \ #h(10pt)
     `a=NL→(xs⧺blanks t⧺[NL],(0,0)),` #h(4pt) `(xs⧺blanks t⧺[a],(0,c+1)))` \
     #src[the program: one pass carrying the column and the count of pending blanks]])],
  [],
)]<entab-laws>

== The minimum tardiness problem

// B&dM §10.3, p. 253.  Both conditions need context, and `cost` has to be restated over `perm xs`
// before Proposition 9.3 fits — `penalty` reads the bag of scheduled jobs, not their order.
#disp[#definition[
`FX=1+(X×Job)`, #h(4pt) `α≜[nil,snoc]` on schedules, #h(4pt) `β≜[nil,snag]` on bags,
`snag` putting a job into a bag; #h(4pt) `bagify≜⦇β⦈ : [Job]⟶Bag Job`, #h(4pt) `H=bagify°`.

`ct`, `dt`, `wt : Job⟶Real` the completion, due and weighting quantities of a job; #h(4pt)
`penalty(xs,j)=(sum(list(ct)(xs))+ct(j)−dt(j))×wt(j)`.

`cost≜` $frac(#[`prefix`], ∋)$ `P(α° [zero,penalty]) est(≥)`, #h(4pt) `cost []=0`, #h(4pt)
`cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))`, #h(4pt) `R≜cost≤cost°`.

`perm≜bagify bagify°=⦇[nil,add]⦈`, #h(4pt) `add (xs,j)=ys⧺[j]⧺zs` for some `xs=ys⧺zs`.

`k≜[zero,assocr (𝟙×((bagify°×𝟙) penalty)) bmax]`, #h(4pt)
`f≜[zero,(bagify°×𝟙) penalty]`, #h(4pt) `Q≜f≤f°`, #h(4pt) `Q'≜(bagify°×𝟙) penalty≤penalty°(bagify×𝟙)`.
// lean:AOP.A10_3_Tardy.bagify@31766900 lean:AOP.A10_3_Tardy.bagAlg@d0f7446e lean:AOP.A10_3_Tardy.snag@c772c474 lean:AOP.A10_3_Tardy.nilBag@f9126385 lean:AOP.A10_3_Tardy.Bag@257c054f lean:AOP.A10_3_Tardy.bagify_cata@bcacee1a lean:AOP.A10_3_Tardy.penalty@cb396f8a lean:AOP.A10_3_Tardy.cost@a1054f80 lean:AOP.A10_3_Tardy.bmax@fc84cd0a lean:AOP.A10_3_Tardy.R@be4c6db5 lean:AOP.A10_3_Tardy.Q@f060536c lean:AOP.A10_3_Tardy.Q'@ea357147 lean:AOP.A10_3_Tardy.fFn@94a6f009 lean:AOP.A10_3_Tardy.tardy_H@5720a058 lean:AOP.A10_3_Tardy.nil_ne_snag@77e87166
]]<tardy-defn>

// ONE WIRE, `Bag Job` to `[Job]`, one datatype lane carrying `bag` above the bead that eats it and
// `list` below.  The last row has NO `E` wire: `pick` is where the greedy program stops carrying a
// set at all.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Tardy.tardy_laws"), #h(6pt) `schedule=(null→nil,pick (schedule×𝟙) snoc)` \
    #src[an ordering of the given bag with least maximum penalty is got by taking a job of least
     penalty out of the bag, putting it last, and scheduling what is left the same way]],
  // lean:AOP.A10_3_Tardy.schedule_le@e2c381dc lean:AOP.A10_3_Tardy.schedule_unfold@d98fd6f6
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Tardy.tardy_laws.rhs"),
    [#src[the specification — @tardy-defn]])],
  [#lean("Freyd.Alg.RelSet.Tardy.tardy_laws.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Tardy.tardy_laws.lhs.body"),
    // job-schedule row: Theorem 10.1
    [#src[No greedy *reduce* exists — one would also
      solve every prefix of the input, and the best schedule of a prefix need not extend to a best
      schedule of the whole]])],
  // `(10.6)`'s arrow is B&dM's `h`, which is @dp-defn's algebra letter; renamed `m` here, since the
  // theorem it feeds and it would otherwise both be `h` in one table.
  [#lean("Freyd.Alg.RelSet.Tardy.tardy_laws.lhs.body")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Tardy.tardy_branch.lhs"),
    [#src[Proposition 10.1: `nil` and `snag` have disjoint ranges]])],
  [#lean("Freyd.Alg.RelSet.Tardy.tardy_branch.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Tardy.pick_branch_le.lhs"),
    // lean:AOP.A10_3_Tardy.pick_branch_le@e50eb5ea lean:AOP.A10_3_Tardy.pick_branch_simple@43683444
    [#src[`pick⊑`#frc([`snag°`])` est(Q')`, a partial function, quadratic in the number of jobs]])],
  // No `E` lane: `pick` does the transpose and the `est` in one function, so nothing is ever a set.
  [#lean("Freyd.Alg.RelSet.Tardy.pick_branch_le.lhs")],
  // lean:AOP.A10_3_Tardy.tardy_laws@706eb827 lean:AOP.A10_3_Tardy.greedy_dp_context@0cb6fac5 lean:AOP.A10_3_Tardy.tardy_mono@f508140f lean:AOP.A10_3_Tardy.tardy_greedy@5953b96f
)]<tardy-laws>

== The TeX problem

// B&dM §10.4, p. 259.  The book's local `h` for `⦇[arb,step]⦈` is @dp-defn's algebra letter, so it
// is written `H°` here instead.  The base case of `f` is `a<0` on p. 262 and `p≤0` in the program.
#disp[#definition[
`intern≜val round : Decimal⟶[0,2¹⁶)`, #h(4pt) `val≜⦇[zero,shift]⦈`, #h(4pt)
`shift (d,r)=(d+r)/10`, #h(4pt) `round r` rounds `2¹⁶r` to the nearest integer:
`round r=n⟺2n−1<2¹⁷r<2n+1`.

`interval n=((2n−1)/2¹⁷,(2n+1)/2¹⁷)`, #h(4pt) `r inrange (a,b)⟺a<r<b`, #h(4pt)
`round°=interval inrange`, #h(4pt) `R≜length≤length°`.

`Interval` all pairs `(a,b)`, `Legal(a,b)⟺0<b<1` and `a<b` #h(4pt) #src[(10.9), preserved by `[arb,step]` — `arb_legal`, `step_legal`]; #h(4pt)
`[arb,step] : 1+(Digit×Interval)⟶Interval`, #h(4pt)
`step (d,(a,b))=((d+a)/10,(d+b)/10)`.

`FX=1+(Digit×X)`, #h(4pt) `α≜[nil,cons]`, #h(4pt) `H≜⦇[arb,step]⦈°`, #h(4pt)
`! : Digit×Interval⟶1`, #h(4pt) `Q≜(l°!°r) ∪ 𝟙` #h(4pt)
#src[`l`, `r` are @coprod-laws's injections into `FX=1+(Digit×X)`, so `l : 1⟶F(Interval)` and
 `r : Digit×Interval⟶F(Interval)`], #h(4pt) `w≜2¹⁷`.
]]<tex-defn>

// ONE WIRE, `[0,2¹⁶)` to `Decimal`, in every row: `interval`, `H` and `[arb,step]°` are relations
// between objects with no functor of their own, so the picture never needs to open `Decimal`'s own
// `list`.  `interval` sits ABOVE the singleton in every row from the second on: it is the map
// pulled out of the transpose, and holding it at one height is what says the rest of the chain
// moved past it.

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Tex.tex_laws"), #h(6pt) `extern(n)=f(2n−1,2n+1)` \
    #src[a shortest decimal whose internal representation is the given multiple of `2⁻¹⁶` is got by
     emitting the one digit the interval of admissible reals allows, until that interval contains
     zero and the empty decimal will do]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Tex.tex_laws_step1.lhs"),
    [#src[the specification — @tex-defn]])],
  [#lean("Freyd.Alg.RelSet.Tex.tex_laws_step1.lhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Tex.tex_laws_step1.rhs"),
    [#src[`round°` is not a map, but `interval` is, so it comes out of the transpose]])],
  // `interval` is an arrow between two objects that carry no functor, so it is a bare bead above
  // the unit: the set the transpose opens starts on its target.
  [#lean("Freyd.Alg.RelSet.Tex.tex_laws_step1.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Tex.tex_laws_step2.rhs"),
    [#src[fusion: `val inrange°=⦇[arb,step]⦈` — the converse of `val`, cut down to intervals, is a
      reduce on cons-lists]])],
  [#lean("Freyd.Alg.RelSet.Tex.tex_laws_step2.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Tex.tex_laws_body.lhs"),
    // interval row: Theorem 10.1
    [#src[#frc([`[arb,step]°`]) returns at most two elements — stop, or take one more
      digit — and `! nil⊑cons R°` makes it stop whenever stopping is legal]])],
  // `est(Q) : E(F(Interval))⟶F(Interval)` kills the set but not the `F` under it, so its wire ends
  // on the `E` lane; `F(H)α` closes `F` and is where the digits' `list` is born (`H` recurses,
  // `α≜[nil,cons]` — @tex-defn — builds the list).
  [#lean("Freyd.Alg.RelSet.Tex.tex_laws_body.lhs")],

  [#vstep(EQ, [],
    [`extern=interval f`, #h(4pt) `f(a,b)=(a<0→[],[d]⧺f(10a−d,10b−d))` \
     #src[the program, with `d` the digit above]])],
  // No picture: `f` is read on points, and the two sides are values, not the objects the panels
  // carry.
  [],

  [#vstep(EQ, [],
    [`extern(n)=f(2n−1,2n+1)`, #h(4pt) `f(p,q)=(p≤0→[],[d]⧺f(10p−w·d,10q−w·d))` \
     #src[`d=(10q) div w`: the same in integer arithmetic only, as chapter 3 required of
      `intern` — every interval reached is `(p/w,q/w)`]])],
  [],
  // lean:AOP.A10_4_Tex.tex_laws@393983dc lean:AOP.A10_4_Tex.tex_laws_step1@ddde5bc4 lean:AOP.A10_4_Tex.tex_laws_step2@436904e9 lean:AOP.A10_4_Tex.tex_laws_step3@12f54b12 lean:AOP.A10_4_Tex.tex_laws_body@942aced5
)]<tex-laws>

#pagebreak(weak: true)
#include "../allegory-appendix.typ"
