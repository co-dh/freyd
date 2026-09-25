#import "../note-prelude.typ": *
#show: note-chapter.with(15)
// note-split: chapter 15 — this header is written by scripts/note-split and stripped by scripts/note-join
= Dynamic Programming <sec-dp>

// A `(μX : …)` row draws the BODY of the recursion: a fixed point has no circuit of its own, and
// what moves from row to row is a box inside that body.

// ---- HINZE–MARSDEN: §14's own lanes, so the two chapters' panels stack, with one lane added.
// Outermost functor LEFTMOST and `𝟏` at the right; `E` takes `THU` because the transpose is taken of
// the WHOLE problem, the base functor `THM` because `T°` opens it inside that set, and a datatype
// the input carries `THN`, `THP`.  An `est` bead spans from the `E` lane down to the object wire,
// the way `scripts/diagram` draws it; the crossings that makes are the accepted ones.
#let THP = 4.15                                   // a datatype inside `THN`

== Theory

// B&dM §9.1, p. 220.  @sec-opt's problem with the algebra cut down to a MAP `h`; the decompositions
// come from `⦇T⦈°`, and the recursion is over them rather than over an initial algebra.
#disp[#definition[
`h : FB⟶B` a map, #h(4pt) `T : FA⟶A` an F-algebra, #h(4pt) `R : B⟶B`.

`H≜⦇T⦈°⦇h⦈ : A⟶B`, #h(4pt) `M≜` $frac(#[`H`], ∋)$ `est(R)` the problem to be solved, #h(4pt) `(μX : G(X))` as
in @mu-defn.
// lean:AOP.A9_1.H@2beea1fa
]]<dp-defn>

// B&dM (9.2), p. 220: the book's four hints, one row each.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.dynamic_programming_lower") \
    #src[taking the input apart every way `T` allows (#frc([`T°`])), solving each part by `M` and
     keeping an optimum (`P(F(M)h) est(R)`) returns only what `H` returns]],
     // lean:AOP.A9_1.dynamic_programming_lower@38a2b134
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.dynamic_programming_lower_step1.lhs"), [])],
  [#lean("Freyd.Alg.dynamic_programming_lower_step1.lhs")],

  [#vstep(SQ, leanc("Freyd.Alg.dynamic_programming_lower_step1.rhs"),
    [#src[(9.4) `P(X)est(R)⊑∋X` at `X≜F(M)h` — @est-710]])],
     // lean:AOP.A9_1.dynamic_programming_lower_step1@9d770398
  [#lean("Freyd.Alg.dynamic_programming_lower_step1.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.dynamic_programming_lower_step2.rhs"),
    [#src[#frc([`T°`])`∋=T°` — @pow-laws]])],
     // lean:AOP.A9_1.dynamic_programming_lower_step2@3449c959
  [#lean("Freyd.Alg.dynamic_programming_lower_step2.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.dynamic_programming_lower_step3.rhs"),
    [#src[`M≜`#frc([`H`])` est(R)⊑`#frc([`H`])`∋=H` — @est-up]])],
     // lean:AOP.A9_1.dynamic_programming_lower_step3@c6f95aaf
  [#lean("Freyd.Alg.dynamic_programming_lower_step3.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.dynamic_programming_lower.rhs"),
    [#src[`T°F(H)h=H`: `H≜⦇T⦈°⦇h⦈` and @hylo-fix]])],
  [#lean("Freyd.Alg.dynamic_programming_lower.rhs")],
)]<dp-lower>

// The chapter's chain, at the level every application below instantiates it.  ONE WIRE, `A` to `B`:
// nothing forks, so a row is a run of boxes and what changes is the box the wire runs through.  A
// transpose is a MAP (@pow-laws), hence a square box; `est`, `thin` and `P(−)` are relations, hence
// chamfered.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.dynamic_programming_thin") \
    #src[an optimum over everything `H` returns is reached by taking the input apart every way `T`
     allows, dropping the parts that can never win, solving each of the rest and keeping one
 optimum #h(4pt) ]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.dynamic_programming_thin_step1.rhs"),
    [#src[the problem to be solved, `H≜⦇T⦈°⦇h⦈` — @dp-defn]])],
  // `H%∋=(𝟙%∋)E(H)`: the unit BIRTHS `E` outside everything and `est(R)` kills it, and `H` is a bead
  // with that `E` running past — the pass IS `E`'s action on `H`.  §16.1 opens on the same problem, so
  // it draws the same panel; the regions are named only in the first.
  [#lean("Freyd.Alg.dynamic_programming_thin_step1.rhs")],

  // (9.3) concludes `⊑R°` where B&dM prints `⊑R` (p. 220): his `R` is this `R` conversed as an arrow.
  [#vstep(RQ, leanc("Freyd.Alg.dynamic_programming_thin.lhs.body"),
    // dp-laws row: Theorem 9.2 and Theorem 9.1 (thinning step dropped)
    [#src[`h` monotonic on `R` and `Q` a preorder with `QF(H)h⊑F(H)hR`; `thin(Q)` as in
      @thin-laws. This is the same with the thinning step dropped — `𝟙⊑thin(Q)`, so the body and
      with it the fixed point only shrink. Knaster–Tarski leaves (9.1) #frc([`T°`])` P(F(M)h)
      est(R)⊑M`; `M=H∩(H°\R°)` splits that into (9.2) #frc([`T°`])` P(F(M)h) est(R)⊑H` and
      (9.3) `H°`#frc([`T°`])` P(F(M)h) est(R)⊑R°`, and both use only (9.4) = (7.10)
      `P(X)est(R)⊑(∋X)∩(∈\(XR°))` — @est-710]])],
  // `T°` births the base functor and `h` kills it; `X` is a bead with `F` running past, which is
  // `F(X)`.  `thin(Q) : E(FA)⟶E(FA)` rearranges the SET alone, so it is a bead on the `E` wire.
  [#lean("Freyd.Alg.dynamic_programming_thin.lhs.body")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.SL.thin_arm₂_le.lhs"),
    // lean:AOP.A9_1.thin_summand_le@ac202517
    [#src[Proposition 9.1 at `T=[V₁,V₂]`, `h=[U₁,U₂]`, `Q=Q₁+Q₂`, `V₂V₁°=𝟘`: `FA` is usually a
      coproduct, and disjoint ranges split the fixed point into one branch per summand. The fixed
      // uniqueness fact: Theorem 6.3
      point is unique and entire — `T°` followed by `F`'s membership relation
      inductive, #frc([`T°`]) finite and non-empty, `R` connected]])],
  // One branch of the `→`, not both: it is a union of two restricted branches with the one shape, so
  // the second adds no shape the first does not already show.
  [#lean("Freyd.Alg.RelSet.SL.thin_arm₂_le.lhs")],
)]<dp-laws>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the condition*], [*how it is discharged*]),

  [`F(R)h⊑hR` \ #src[Proposition 9.2, `R≜cost≤cost°`, `h cost=F(cost)k`,
 `F(≤)k⊑k≤`]],
   // lean:AOP.A9_1.monotonicAlg_of_cost@f97d27af
  [monotonicity when the cost is itself a fold with a step `k` monotonic on `≤`],
  [`F(R∩(H°H))h⊑hR` \ #src[Proposition 9.3, `R≜cost≤cost°`,
   `h cost=F(⟨cost,H°⟩)k`, `F(≤×𝟙)k⊑k≤`, `H°` simple;
 ]],
   // lean:AOP.A9_1.monotonicAlg_in_context@f0a1b13c
  [monotonicity *in context*: `k` may also read the input the part was built from],
  [`QF(H)h⊑F(H)hR` at `Q≜F(U,V)` \ #src[Proposition 9.4, `U`, `V` preorders, `F(U,R)h⊑hR`,
   `VH⊑HR`]],
  // combined row: Theorem 9.2
  [both conditions at once, split along the two arguments of a bifunctor],
)]<dp-conditions>

// B&dM Proposition 9.3, p. 223: the book's hints, one row each; B&dM's `H°` is `S` here.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.monotonicAlg_in_context") \
    #src[improving each part by `R` among the parts with the same `S`-context (`F(R∩SS°)`) and then
     assembling by `h` gives only what assembling by `h` and then improving by `R` gives (`hR`)]],
     // lean:AOP.A9_1.monotonicAlg_in_context@f0a1b13c
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.monotonicAlg_in_context_step1.lhs"), [])],
  [#lean("Freyd.Alg.monotonicAlg_in_context_step1.lhs")],

  [#vstep(SQ, leanc("Freyd.Alg.monotonicAlg_in_context_step1.rhs"),
    [#src[shunting: `cost` a map, so `𝟙⊑cost cost°` — @triple-chains]])],
     // lean:AOP.A9_1.monotonicAlg_in_context_step1@44f1c030
  [#lean("Freyd.Alg.monotonicAlg_in_context_step1.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.monotonicAlg_in_context_step2.rhs"),
    [#src[products: `R∩SS°=⟨cost leq,S⟩⟨cost,S⟩°` at `R=cost leq cost°` — @relprod-defn]])],
     // lean:AOP.A9_1.monotonicAlg_in_context_step2@e27a633e
  [#lean("Freyd.Alg.monotonicAlg_in_context_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.monotonicAlg_in_context_step3.rhs"),
    [#src[assumption on `cost`: `h cost=F(⟨cost,S⟩)k`]])],
     // lean:AOP.A9_1.monotonicAlg_in_context_step3@23c4eb72
  [#lean("Freyd.Alg.monotonicAlg_in_context_step3.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.monotonicAlg_in_context_step4.rhs"),
    [#src[`S` simple, so `⟨cost,S⟩` simple: `⟨cost,S⟩°⟨cost,S⟩⊑𝟙`]])],
     // lean:AOP.A9_1.monotonicAlg_in_context_step4@e0fdcf2e
  [#lean("Freyd.Alg.monotonicAlg_in_context_step4.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.monotonicAlg_in_context_step5.rhs"),
    [#src[products; functors: `⟨cost leq,S⟩=⟨cost,S⟩(leq×𝟙)` — @bdm-prod-laws, @relator-laws]])],
     // lean:AOP.A9_1.monotonicAlg_in_context_step5@b63ea26a
  [#lean("Freyd.Alg.monotonicAlg_in_context_step5.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.monotonicAlg_in_context_step6.rhs"),
    [#src[assumption on `k`: `F(leq×𝟙)k⊑k leq`]])],
     // lean:AOP.A9_1.monotonicAlg_in_context_step6@941ec9da
  [#lean("Freyd.Alg.monotonicAlg_in_context_step6.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.monotonicAlg_in_context.rhs"),
    [#src[assumption on `cost` read backwards, then `R=cost leq cost°`]])],
     // lean:AOP.A9_1.monotonicAlg_in_context_step7@b5c7d052
  [#lean("Freyd.Alg.monotonicAlg_in_context.rhs")],
)]<dp-context-mono>

// B&dM Proposition 9.4, pp. 223–224, "argue as follows": the thinning condition at `Q≜G(U,V)`,
// the book's hints one row each, without the converse B&dM takes (the note's `R` is his `R°`).
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.birelator_thin_condition") \
    #src[thinning the parts by `U` in the first argument and by `V` in the second (`G(U,V)`), then
     solving by `H` and assembling by `h`, gives only what solving and assembling and then improving
     by `R` gives (`G(𝟙,H)hR`)]],
     // lean:AOP.A9_1.birelator_thin_condition@13d1e400
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.birelator_thin_condition_step1.lhs"), [])],
  [#lean("Freyd.Alg.birelator_thin_condition_step1.lhs")],

  [#vstep(EQ, leanc("Freyd.Alg.birelator_thin_condition_step1.rhs"),
    [#src[taking `Q≜G(U,V)`; bifunctors: `G(U,V)G(𝟙,H)=G(U,VH)` — @relator-laws]])],
     // lean:AOP.A9_1.birelator_thin_condition_step1@3b29bbce
  [#lean("Freyd.Alg.birelator_thin_condition_step1.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.birelator_thin_condition_step2.rhs"),
    [#src[assumption on `V`: `VH⊑HR`]])],
     // lean:AOP.A9_1.birelator_thin_condition_step2@d93a9edb
  [#lean("Freyd.Alg.birelator_thin_condition_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.birelator_thin_condition_step3.rhs"),
    [#src[bifunctors: `G(U,HR)=G(𝟙,H)G(U,R)` — @relator-laws]])],
     // lean:AOP.A9_1.birelator_thin_condition_step3@e063da44
  [#lean("Freyd.Alg.birelator_thin_condition_step3.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.birelator_thin_condition_step4.rhs"),
    [#src[assumption on `h`: `G(U,R)h⊑hR`]])],
     // lean:AOP.A9_1.birelator_thin_condition_step4@84cc2fb5
  [#lean("Freyd.Alg.birelator_thin_condition_step4.rhs")],
)]<dp-bifunctor-thin>

== The string edit problem

// B&dM §9.2, p. 225.  The section numbers no equation.  `base` and `step` are reused for the
// tabulating fold at the foot of the table; they are not `edit`'s.
#disp[#definition[
`Op::=cpy Char∣del Char∣ins Char`, #h(4pt) `F(A,B)=1+(A×B)`, #h(4pt) `α≜[nil,cons]`.

`edit≜⦇[base,step]⦈ : [Op]⟶[Char]×[Char]` #src[],
// lean:AOP.A9_2_Edit.edit_cata@0dafb85c
#h(4pt) `base` returning `([],[])`,
#h(4pt) `step (cpy a,(xs,ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt) `step (del a,(xs,ys))=([a]⧺xs,ys)`,
#h(4pt) `step (ins a,(xs,ys))=(xs,[a]⧺ys)`.

`length≜⦇[zero,π₂ succ]⦈` #src[], #h(4pt)
// lean:AOP.A9_2_Edit.length_cata@9e3040b0
`R≜length≤length°` #src[], #h(4pt) `U≜⊤`, #h(4pt)
// lean:AOP.A9_2_Edit.R_eq@0f7a4661
`V≜suffix°×suffix°` #src[], #h(4pt)
// lean:AOP.A9_2_Edit.V@09fe0b1a
`Q≜𝟙+(U×V)` #src[], #h(4pt) `empty` the coreflexive on `(xs,ys)` with
// lean:AOP.A9_2_Edit.Q@e6ebf648
both lists empty.

`unstep` implements $frac(#[`step°`], ∋)$ `thin(U×V)`
#src[]:
// lean:AOP.A9_2_Edit.unstep@186b86c5 lean:AOP.A9_2_Edit.unstep_sound@d5b21374
#h(4pt) `unstep ([a]⧺xs,[])=[(del a,(xs,[]))]`,
#h(4pt) `unstep ([],[b]⧺ys)=[(ins b,([],ys))]`, #h(4pt)
`unstep ([a]⧺xs,[b]⧺ys)=(a=b→[(cpy a,(xs,ys))],[(del a,(xs,[b]⧺ys)),(ins b,([a]⧺xs,ys))])`.
]]<edit-defn>

// The two strings are a PRODUCT, hence TWO WIRES, and every box here spans them: nothing in the
// chain acts on one string alone.  `Δ` is the relator `X↦X×X`, so `[Char]×[Char]` is `Δ`, `list`,
// `Char` — sugar undone at the ends too.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Edit.edit_laws"), #h(6pt) `mle=(empty→nil,unstep list((𝟙×mle)cons) minlist(R))` \
    #src[a shortest edit sequence from which both strings can be reconstituted is one pass over the
     two of them, each step copying, deleting or inserting one character and the best sequence for
     what is left taken from the entries already computed]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Edit.edit_laws.rhs"),
    [#src[the specification — @edit-defn]])],
  // `edit°` eats `Δ` and the source `list` and MAKES the target one, so every strand lands on it;
  // `est(R) : E([Op])⟶[Op]` kills the set, so its wire spans the `E` lane down to the object.
  [#lean("Freyd.Alg.RelSet.Edit.edit_laws.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Edit.edit_laws.lhs.body"),
    [
     // edit_mono row: Theorem 9.2
     #src[at `Q≜𝟙+(U×V)`. Monotonicity `F(R)α⊑αR`
 #src[] is Proposition 9.2 at
      // lean:AOP.A9_2_Edit.edit_mono@089b97ab
      `length≜⦇[zero,π₂ succ]⦈` with `succ` monotonic on `≤`, so `cons` is monotonic on `R`. The
      thinning condition `QF(𝟙,edit°)α⊑F(𝟙,edit°)αR`
 #src[] over `F(Op,[Char]×[Char])` is
      // lean:AOP.A9_2_Edit.edit_thin_condition@e22f4fe4
      Proposition 9.4 at `U≜⊤` — `F(⊤,R)α⊑αR`, left as an exercise, so any two operations may be
      compared — and `V≜suffix°×suffix°`
 #src[,
      // lean:Freyd.Alg.RelSet.Edit.edit_V@274d4558
 ] —
      // lean:AOP.A9_2_Edit.edit_Vrecip@1d49fb2e
 `edit (𝟙×suffix)⊑R° edit` #src[],
      // lean:AOP.A9_2_Edit.edit_suffix_right@6e4ee2a2
 `edit (suffix×𝟙)⊑R° edit` #src[]. `suffix=tail*`
      // lean:AOP.A9_2_Edit.edit_suffix_left@dda69ad1
      and `BA⊑CB⟹BA*⊑C*B` cut those to one step each: drop the operation that produced the head, or
      weaken its `cpy` to a `del`, never lengthening the sequence]])],
  // `[base,step]°` opens the base functor INSIDE the set the singleton opened, and the algebra
  // closes it again; `Δ` and the source `list` die and are remade at both beads, so each runs as a
  // loop between them.  `thin(Q) : E(F−)⟶E(F−)` rearranges the set alone: a bead on the `E` wire.
  [#lean("Freyd.Alg.RelSet.Edit.edit_laws.lhs.body")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_branch.lhs"),
    [#src[Proposition 9.1: `base` and `step` have disjoint ranges, so the fixed point splits into
      one branch per summand — `empty`, the coreflexive on `(xs,ys)` with both lists empty, is where
      `base` returns]])],
  // The `step` branch of the `→`, not both: the `base` branch is `nil` on an empty pair, nothing to
  // draw.  `Op×−` is the summand `step°` opens.
  [#lean("Freyd.Alg.RelSet.Edit.edit_branch.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Edit.edit_prog.lhs"),
    [#src[`unstep` implements #frc([`step°`])` thin(U×V)` — at most two decompositions survive, a
      copy beating a delete or an insert wherever it is available — and `minlist(R)` implements
      `est(R)`. The same subproblem is solved many times over, so the running time is exponential in
      the two lengths]])],
  // The program is the branch above with each box replaced by a function computing it, so the wires
  // and the beads are the same picture: only the labels change.
  [#lean("Freyd.Alg.RelSet.Edit.edit_prog.lhs")],
)]<edit-laws>

// No picture: a curried function on lists is not a relation between the objects the panels carry.
// Its own display, because `#disp` cannot break across pages and the panel rows above already fill one.
#disp[#table(
  columns: (1fr,),
  align: (left + horizon,),
  inset: (x: 9pt, y: 3pt), stroke: 0.4pt + luma(190),

  [#vstep(EQ, [],
    [#leanf("Freyd.Alg.RelSet.Edit.mle_head_column"), #h(4pt) `column(xs,ys)=[mle(u,ys)∣u←tails(xs)]` \
     // lean:AOP.A9_2_Edit.mle@9c01e9fc lean:AOP.A9_2_Edit.mle_head_column@c8a15220 lean:AOP.A9_2_Edit.column@87907e0c
     `column(xs)=⦇[fstcol(xs),nextcol(xs)]⦈`, #h(4pt) `fstcol=list(del) tails` \
     // lean:AOP.A9_2_Edit.column_cata@06a76bd9 lean:AOP.A9_2_Edit.fstcol@e72647f8 lean:AOP.A9_2_Edit.column_nil@63c24991
     #src[the tabulation: `mle(xs,ys)` needs `mle(u,v)` for every tail `u` of `xs` and `v` of
      `ys`, so the columns are built right to left]])],

  [#vstep(EQ, [],
    [#leanf("Freyd.Alg.RelSet.Edit.column_cons") \
     // lean:AOP.A9_2_Edit.column_cons@bc563c5b lean:AOP.A9_2_Edit.nextcol@170c07d3
     `nextcol(xs)(b,us)=⦇[base(b,last(us)),step(b)]⦈(xus)`, #h(4pt)
     `xus=zip(xs,zip(init(us),tail(us)))` \
     #src[each column is a fold built bottom to top, over `xs` zipped with the adjacent pairs of the
      column to its right]])],

  [#vstep(EQ, [],
    [`base(b,u)=[[ins(b)]⧺u]` \ `step(b)((a,(u,v)),ws)=(a=b→[[cpy(a)]⧺v]⧺ws,`
     // lean:AOP.A9_2_Edit.Tab.base@5520a210 lean:AOP.A9_2_Edit.Tab.step@ace9b1b6
     `[bmin(R)([del(a)]⧺w,[ins(b)]⧺u)]⧺ws)` \
     #src[`w=head(ws)`; these `base`, `step` are not `edit`'s. An entry depends on the one below it
      (a delete), the one to its right (an insert), and the one below that (a copy) — quadratic in
      the two lengths]])],
)]<edit-tabulation>

== Optimal bracketing

// B&dM §9.3, p. 230.  `⦇T⦈ = flatten` is a map, so `H° = flatten` is simple and Proposition 9.3
// applies; no decomposition is preferable to another here, so there is no thinning step.
#disp[#definition[
`tree A::=tip A∣bin (tree A,tree A)`, #h(4pt) `FX=A+X²`, so `F(R)=𝟙+R²`; #h(4pt)
`h≜[tip,bin]`, #h(4pt) `flatten≜⦇[wrap,cat]⦈ : tree A⟶list⁺ A`
#src[], #h(4pt) `H=flatten°`.
// lean:AOP.A9_3_Bracket.flatten_cata@ce76fada

`⟨cost,size⟩≜⦇[opt,opb]⦈`, #h(4pt) `opt≜⟨zero,st⟩`, #h(4pt)
`opb ((cx,sx),(cy,sy))=(cb (sx,sy)+cx+cy,sb (sx,sy))`.

`sb` associative, so `size=flatten sz` for a map `sz`
#src[]; #h(4pt)
// lean:AOP.A9_3_Bracket.size_eq_sz_flatten@e6003d74
`R≜cost≤cost°` #src[], #h(4pt)
// lean:AOP.A9_3_Bracket.R_eq@48f5ee2a
`g≜[zero,(𝟙×sz)² opb π₁]`, #h(4pt) `single` the coreflexive on singleton lists.

`splits≜⟨inits⁺,tails⁺⟩ zip`, an implementation of $frac(#[`cat°`], ∋)$; #h(4pt) `array≜inits list(row)`,
#h(4pt) `row≜tails list(mct)`, #h(4pt) `col≜inits list(mct)`.

`mix≜zip list(bin) minlist(R)`, #h(4pt) `next≜⟨π₁,mix⟩ snoc`, #h(4pt)
`process≜((tip wrap)×𝟙) loop(next)`.
]]<mct-defn>

// ONE WIRE, `list⁺ A` to `tree A`, and one datatype lane carrying `list⁺` above the bead that eats
// it and `tree` below.  No thinning step: no decomposition of a list is preferable to another here.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Bracket.mct_laws"), #h(6pt) `mct=(single→head tip,⟨init col,tail row⟩ mix)` \
    #src[a least-cost bracketing of `a₁⊕⋯⊕aₙ` is read off an array holding one best tree per
     non-empty segment, each entry built from the column to its left and the row below it]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.mct_laws.rhs"),
    [#src[the specification — @mct-defn]])],
  // `flatten°` eats `list⁺` and MAKES `tree`, so one lane carries both; `est(R) : E(tree A)⟶tree A`
  // kills the set, so its wire spans the `E` lane down to the object wire, `tree` surviving.
  [#lean("Freyd.Alg.RelSet.Bracket.mct_laws.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Bracket.mct_laws.lhs.body"),
    [
     // mct_laws row: Theorem 9.1
     #src[split the list in every way, bracket both halves, join. The condition is
      monotonicity *in context*, `F(R∩(flatten flatten°))h⊑hR`
 #src[] — only trees with the same flattening
      // lean:AOP.A9_3_Bracket.mct_mono@a3daf2b8
      are compared — which is Proposition 9.3 at `H°=flatten`, a map, with (9.5)
 `[tip,bin] cost=(𝟙+⟨cost,flatten⟩²)g` #src[]
      // lean:AOP.A9_3_Bracket.mct_cost_alg@984a2c56
      (the cost of a node reads only the cost and the
      flattening of its two subtrees) and (9.6) `(𝟙+(≤×𝟙)²)g⊑g≤`
 #src[] (`g` monotonic on `≤` in its two
      // lean:AOP.A9_3_Bracket.mct_g_mono@6a5a7e62
      cost arguments)]])],
  // `[wrap,cat]°` opens the base functor `A+(−)²` inside the set and `[tip,(X×X)bin]` closes it;
  // `list⁺` dies and is remade at both, so it runs as a loop between them.
  [#lean("Freyd.Alg.RelSet.Bracket.mct_laws.lhs.body")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.mct_branch.lhs"),
    [#src[Proposition 9.1: `wrap` and `cat` have disjoint ranges, and `single` is the coreflexive on
      singleton lists, where `wrap` returns]])],
  // No picture: the disjointness of the two ranges is a case split on a coproduct, which has no
  // shape of its own; the panel above already draws the `cat` branch.
  [],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Bracket.mct_prog.lhs"),
    [#src[`splits≜⟨inits⁺,tails⁺⟩ zip` implements #frc([`cat°`]) and `minlist(R)` implements
      `est(R)`. Exponential, since the segments of one list overlap]])],
  [#lean("Freyd.Alg.RelSet.Bracket.mct_prog.lhs")],

  [#vstep(EQ, [],
    [`mct=(single→head tip,⟨init col,tail row⟩ mix)` #h(4pt) #src[(9.7)] \
     #src[the tabulation: `mct xs` is needed for every non-empty segment `xs`, so the values are
      held as an array of rows, `array≜inits list(row)`, `row≜tails list(mct)`,
      `col≜inits list(mct)`, `mix≜zip list(bin) minlist(R)`]])],
  // No picture: the tabulated program relates arrays of trees, not the objects the panels carry.
  [],

  [#vstep(EQ, [],
    [`col=(single→head tip wrap,⟨init col,tail row⟩ next)` #h(4pt) #src[(9.8)] \
     `cons col=(𝟙×array) process` #h(4pt) #src[(9.9)] \
     `row=(single→head tip wrap,⟨mct,tail row⟩ cons)` #h(4pt) #src[(9.10)] \
     #src[a column extends the column to its left, a row the row below it; (9.9) is (9.8) rewritten
      as a loop, `next≜⟨π₁,mix⟩ snoc`, `process≜((tip wrap)×𝟙) loop(next)`]])],
  [],

  [#vstep(EQ, [],
    [`array=⦇[fstcol,addcol]⦈`, #h(4pt) `fstcol≜tip wrap wrap` \
     `addcol≜⟨π₁ tip wrap,step⟩ cons`, #h(4pt) `step≜⟨process tail,π₂⟩ zip list(cons)` \
     #src[the program: one fold building the array column by column, cubic in the length of the
      input]])],
  [],
)]<mct-laws>

== Data compression

// B&dM §9.4, p. 238.  Snoc-lists throughout.  No numbered equations, and no tabulation phase — the
// book stops at the recursive program and says the details are messy.
#disp[#definition[
`[A]::=nil∣snoc ([A],A)`, #h(4pt) `list⁺ A::=wrap A∣snoc (list⁺ A,A)`, #h(4pt)
`String=[Char]`, #h(4pt) `Code::=sym Char∣ptr (String,String⁺)`, #h(4pt)
`F(Code,String)=1+(String×Code)`, #h(4pt) `α≜[nil,snoc]`.

`decode≜⦇[nil,extend]⦈ : [Code]⟶String`, #h(4pt) `extend (xs,sym a)=xs⧺[a]`, #h(4pt)
`extend (xs,ptr (ys,zs))=xs⧺zs` when `ys⧺zs` is a proper prefix of `xs⧺zs`; #h(4pt)
`H=decode°`.

`size≜⦇[zero,distr [𝟙×c,𝟙×p] plus]⦈` with `c`, `p` the constant costs of a symbol and a
pointer; #h(4pt) `R≜size≤size°`, #h(4pt) `Q≜F(⊤+⊤,prefix°)=𝟙+(prefix°×(⊤+⊤))`, the
two `⊤` on symbols and on pointers.

`lrt ws=est(prefix°×(⊤+⊤)) {(xs,(ys,zs))∣xs⧺zs=ws`, `ys⧺zs` a proper prefix of `ws}`,
the longest repeated tail; #h(4pt)
`reduce (ws⧺[a])=(zs≠[]→[(ws,sym a),(xs,ptr (ys,zs))],[(ws,sym a)])` with
`(xs,(ys,zs))=lrt (ws⧺[a])`.
// lean:AOP.A9_4_Code.Code@1aaa6e50 lean:AOP.A9_4_Code.extendP@f49b7c97 lean:AOP.A9_4_Code.extendAlg@90db2e8c lean:AOP.A9_4_Code.decode@6e333c71 lean:AOP.A9_4_Code.sizeFn@d6390d6f lean:AOP.A9_4_Code.size_cata@acc91a37 lean:AOP.A9_4_Code.R@4bb66fd8 lean:AOP.A9_4_Code.R_eq@5966875d lean:AOP.A9_4_Code.Q@e037d736 lean:AOP.A9_4_Code.U@f6ac9e29 lean:AOP.A9_4_Code.prefixR@0a5c54fb
]]<code-defn>

// ONE WIRE, `String` to `[Code]`, and one `list` lane: the string above the bead that eats it, the
// code sequence below.  Snoc-lists throughout, so the base functor is `(−)×Code`.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Code.code_laws"), #h(6pt)
    `encode=(null→nil,reduce list((encode×𝟙)snoc) minlist(R))` \
    #src[a smallest code sequence decoding to the given string is built from the right, each step
     emitting the last character as a symbol or ending with a pointer back into what has already
     been decoded]],
  // lean:AOP.A9_4_Code.code_laws@a53670d5
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Code.code_laws.rhs"),
    [#src[the specification — @code-defn]])],
  [#lean("Freyd.Alg.RelSet.Code.code_laws.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Code.code_laws.lhs.body"),
    // entab row: Theorem 9.2
    [#src[at `Q≜F(⊤+⊤,prefix°)=𝟙+(prefix°×(⊤+⊤))`, the two `⊤` on symbols and on
      pointers. Monotonicity `F(R)α⊑αR` is routine, the two costs being constants:
      `(⊤+⊤)[c,p]=[c,p]`. Proposition 9.4 splits the thinning condition in two — `F(⊤+⊤,R)α⊑αR`,
      and `decode prefix⊑R° decode`, for which `decode init⊑R° decode` is enough: dropping the last
      character of the output shortens or removes the last code element and never raises the cost.
      So between a symbol and a pointer nothing can be decided in advance, and between two pointers
      the longer match wins]])],
  // `[nil,extend]°` opens `(−)×Code` inside the set the singleton opened and `[nil,(X×𝟙)snoc]`
  // closes it; `list` dies and is remade at both beads, so it runs as a loop between them.
  [#lean("Freyd.Alg.RelSet.Code.code_laws.lhs.body")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Code.code_branch.lhs"),
    [#src[Proposition 9.1: `nil` and `extend` have disjoint ranges. The decompositions of one string
      are #frc([`extend°`])` (ws⧺[a])={(ws,sym a)} ∪ {(xs,ptr (ys,zs))∣xs⧺zs=ws⧺[a]`, `ys⧺zs` a
      proper prefix of `ws}` — take the last character as a symbol, or end with a pointer]])],
  [#lean("Freyd.Alg.RelSet.Code.code_branch.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Code.code_prog.lhs"),
    [#src[`reduce` implements #frc([`extend°`])` thin(prefix°×(⊤+⊤))`: thinning leaves at most two,
      the symbol and the pointer of the longest repeated tail `lrt`. Again exponential; the book
      gives no tabulation for it]])],
  [#lean("Freyd.Alg.RelSet.Code.code_prog.lhs")],
)]<code-laws>

#pagebreak(weak: true)
