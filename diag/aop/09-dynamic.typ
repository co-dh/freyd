#import "../note-prelude.typ": *
#show: note-chapter.with(9)
// note-split: chapter 9 — this header is written by scripts/note-split and stripped by scripts/note-join
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

=== Example: segmenting a list <dp-example>

// @dp-defn's `H≜⦇T⦈°⦇h⦈` at one instance: `A=B=[ℕ]`, `F(X)=𝟏+[ℕ]×X`, and the non-emptiness of a
// segment carried by `T`'s `cat`, not by the element type.
#disp[
  - #leanf("Freyd.Alg.RelSet.Segment.fold_T") \
    #src[`T=[nil,cat]` takes a non-empty first list, so `T°` cuts a non-empty prefix off a list every
     way, and folding with `T` flattens a list of segments]
    // lean:AOP.A9_0_SegmentExample.fold_T@984e4101
  - #leanf("Freyd.Alg.RelSet.Segment.fold_h") \
    #src[`h=[nil,cons(sum×𝟙)]` puts a segment's sum in front, so folding with `h` sums every segment]
    // lean:AOP.A9_0_SegmentExample.fold_h@a85436e3
  - #leanf("Freyd.Alg.RelSet.Segment.H_eq") \
    #src[`H` segments a list every way, then sums each segment; with `R` comparing the largest entry,
     `M` cuts the list so that the largest segment sum is as small as possible]
    // lean:AOP.A9_0_SegmentExample.H_eq@49b18be4
]<dp-example-defs>

// `h` is a map (`h_iff_hFn`), so each row is one equation of its function, input | output.
#disp[#table(columns: 2, align: left + horizon, inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*`x`*], [*`h(x)`*]),
  [#leanf("Freyd.Alg.RelSet.Segment.h_nil.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Segment.h_nil.rhs")],
  // lean:AOP.A9_0_SegmentExample.h_nil@89d46cbf
  [#leanf("Freyd.Alg.RelSet.Segment.h_c.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Segment.h_c.rhs")],
  // lean:AOP.A9_0_SegmentExample.h_c@ebeb0e4d
  [#leanf("Freyd.Alg.RelSet.Segment.h_ab_c.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Segment.h_ab_c.rhs")],
  // lean:AOP.A9_0_SegmentExample.h_ab_c@cc4f586e
  [#leanf("Freyd.Alg.RelSet.Segment.h_a_bc.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Segment.h_a_bc.rhs")],
  // lean:AOP.A9_0_SegmentExample.h_a_bc@fff1c8b6
)]<dp-example-h>

#disp[
  - #leanf("Freyd.Alg.RelSet.Segment.H_abc") \
    #src[`H` sends `[a,b,c]` to the sums of its four segmentations and nothing else]
    // lean:AOP.A9_0_SegmentExample.H_abc@1d74200c
  - #leanf("Freyd.Alg.RelSet.Segment.H_fix") \
    #src[cut once, solve the rest, put the pieces back together]
    // lean:AOP.A9_0_SegmentExample.H_fix@80717498
]<dp-example-H>

// B&dM §9.1, p. 220.  @sec-opt's problem with the algebra cut down to a MAP `h`; the decompositions
// come from `⦇T⦈°`, and the recursion is over them rather than over an initial algebra.
#disp[#definition[
`h : FB⟶B` a map, #h(4pt) `T : FA⟶A` an F-algebra, #h(4pt) `R : B⟶B`.

`H≜⦇T⦈°⦇h⦈ : A⟶B`, #h(4pt) `M≜` $frac(#[`H`], ∋)$ `est(R)` the problem to be solved, #h(4pt) `(μX : G(X))` as
in @mu-defn.
// lean:AOP.A9_1.H@71852cf7

#leanf("Freyd.Alg.DPSetting") \
#src[`h` is a map, `h` is monotonic on `R°`, and `R°` is transitive — assumed by every theorem below]
// lean:AOP.A9_1.DPSetting@761bb771
]]<dp-defn>

// B&dM Theorem 9.1, p. 220: what the recursion computes, read left to right.
#disp(num: "Theorem 9.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.dynamic_programming") \
    #src[every answer the recursion returns is an optimal one]],
    // lean:AOP.A9_1.dynamic_programming@283c7263
  pad(left: -9pt)[#src[
    - #frc([`T°`]) takes the input apart one step every way; `F(X)` solves
      each part by the recursion `X`; `h` assembles each candidate; `est(R)` keeps a best one
    - `⊑M`: that never misses the optimum, though all candidates are never listed as `H` would
    - `h` monotonic on `R`: a better part never makes the whole worse
    - `⊑`, not `=`: some optima may not be returned; that the recursion returns anything at all
      needs `T°` to stop taking apart — @dp-laws
  ]],
)]<dp-thm>

#import "../generated/Freyd.Alg.dynamic_programming_lower.calc.typ" as calc-dpl
#import "../generated/Freyd.Alg.dynamic_programming_upper.calc.typ" as calc-dpu
#import "../generated/Freyd.Alg.dynamic_programming_thin_lower.calc.typ" as calc-dptl
#import "../generated/Freyd.Alg.dynamic_programming_thin_upper.calc.typ" as calc-dptu
#import "../generated/Freyd.Alg.birelator_thin_condition.calc.typ" as calc-bithin
#import "../generated/Freyd.Alg.monoAlg_of_cost_shunted.calc.typ" as calc-cost
#import "../generated/Freyd.Alg.monoAlg_in_context.calc.typ" as calc-ctx
// B&dM (9.2), p. 220: the book's four hints, one step each, read left to right.
#disp(num: "(9.2)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.dynamic_programming_lower") \
    #src[taking the input apart every way `T` allows (#frc([`T°`])), solving each part by `M` and
     keeping an optimum (`P(F(M)h) est(R)`) returns only what `H` returns]],
     // lean:AOP.A9_1.dynamic_programming_lower@5dd00afd
  lean-calc(calc-dpl),
)]<dp-lower>

// B&dM (9.3), p. 221: the book's five hints and transitivity, one row each.
#disp(num: "(9.3)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.dynamic_programming_upper") \
    #src[for every `b` that `H` returns from an input, the step #frc([`T°`])` P(F(M)h) est(R)` returns
     from that input only `b'` with `R` relating `b'` to `b`]],
     // lean:AOP.A9_1.dynamic_programming_upper@dbf5fa82
  // two rows: nine panels in one row shrink the fractions past reading
  lean-calc(calc-dpu, breaks: (5,)),
)]<dp-upper>

// The chapter's chain, at the level every application below instantiates it.  ONE WIRE, `A` to `B`:
// nothing forks, so a row is a run of boxes and what changes is the box the wire runs through.  A
// transpose is a MAP (@pow-laws), hence a square box; `est`, `thin` and `P(−)` are relations, hence
// chamfered.
#disp(num: "Theorem 9.2")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.dynamic_programming_thin") \
    #src[an optimum over everything `H` returns is reached by taking the input apart every way `T`
     allows, dropping the parts that can never win, solving each of the rest and keeping one
 optimum #h(4pt) ]],
  lean-chain(
    (none, "Freyd.Alg.dynamic_programming_thin_prefixed.rhs",
      src[`H≜⦇T⦈°⦇h⦈` — @dp-defn]),
    // `H%∋=(𝟙%∋)E(H)`: the unit BIRTHS `E` outside everything and `est(R)` kills it, and `H` is a bead
    // with that `E` running past — the pass IS `E`'s action on `H`.  §16.1 opens on the same problem, so
    // it draws the same panel; the regions are named only in the first.
    // (9.3) concludes `⊑R°` where B&dM prints `⊑R` (p. 220): his `R` is this `R` conversed as an arrow.
    (RQ, "Freyd.Alg.dynamic_programming_thin_prefixed.lhs",
      // dp-laws row: Theorem 9.2 and Theorem 9.1 (thinning step dropped)
      src[`QF(H)h⊑F(H)hR`, `h` monotonic on `R` — @thin-laws, @est-up]),
    // `T°` births the base functor and `h` kills it; `X` is a bead with `F` running past, which is
    // `F(X)`.  `thin(Q) : PFA⟶PFA` rearranges the SET alone, so it is a bead on the `E` wire.
  ),
  // The two squares the chain rests on: the hypothesis `hQ` and the fixed point `H` satisfies.
  grid(columns: 2, column-gutter: 24pt, align: center + top,
    [#leancd("Freyd.Alg.dynamic_programming_thin#hQ") \
      #src[`QF(H)h⊑F(H)hR`: every result of thinning by `Q`, solving the parts by `F(H)` and
      assembling by `h` is reached by `R` from a result of solving by `F(H)` and assembling by `h`
      without `Q`]],
    [#leancd("Freyd.Alg.H_fixed") \
      #src[`T°F(H)h=H`: taking the input apart once by `T°`, solving the parts by `F(H)` and
      assembling by `h` returns exactly what `H` returns]]),
)]<dp-laws>

// (9.2): the book's four hints of Theorem 9.1 with `thin(Q)∋⊑∋` added.  Its own display: a `#disp`
// cannot break across a page, and the rows above already fill one.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.dynamic_programming_thin_lower") \
    #src[taking the input apart every way `T` allows (#frc([`T°`])), dropping the parts `thin(Q)`
     rejects, solving each rest by `M` and keeping an optimum returns only what `H` returns]],
     // lean:AOP.A9_1.dynamic_programming_thin_lower@32f5e9ad
  lean-calc(calc-dptl),
)]<dp-laws-92>

// (9.3), the second half of the same proof: a `#disp` does not break across a page.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.dynamic_programming_thin_upper") \
    #src[`H°` followed by the body at `M` is `⊑R°`: an answer of the body is never worse than an
     answer of `H` to the same input]],
  lean-calc(calc-dptu, span: (0, 7), breaks: (4,)),
)]<dp-laws-93>

// (9.3) continued from the last row above: the ten rows overflow one page.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  lean-calc(calc-dptu, span: (6, 12)),
)]<dp-laws-93b>

// B&dM Proposition 9.1, p. 222, along Exercise 9.5, in Rel(Set).  The book's `(ran V₁ → W₁, W₂)` is
// the union below: off `ran V₁ ∪ ran V₂` both are empty.
#disp(num: "Proposition 9.1")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.dp_disjoint_ranges") \
    #src[when `V₁` and `V₂` have disjoint ranges, the body over `[V₁,V₂]` runs the `V₁` problem on
     inputs `V₁` reaches and the `V₂` problem on inputs `V₂` reaches]],
  lean-chain(
    (none, "Freyd.Alg.RelSet.dp_disjoint_ranges_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.dp_disjoint_ranges_step1.rhs.inl",
      src[empty off `ran V₁ ∪ ran V₂`]),
    (EQ, "Freyd.Alg.RelSet.dp_disjoint_ranges_step2.rhs.inl",
      src[#frc([`[V₁,V₂]°`])` = `#frc([`V₁°`])`P(inl)` on `ran V₁`]),
    (EQ, "Freyd.Alg.RelSet.dp_disjoint_ranges_step3.rhs.inl",
      src[`P(inl)thin(Q₁+Q₂)=thin(Q₁)P(inl)`]),
    (EQ, "Freyd.Alg.RelSet.dp_disjoint_ranges_step4.rhs.inl",
      src[`P` a relator, `inl[U₁,U₂]=U₁`]),
  ),
)]<dp-disjoint>

// B&dM Proposition 9.2, p. 222: the book's hints, one row each.
#disp(num: "Proposition 9.2")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.monoAlg_of_cost") \
    #src[if `R` compares two values by comparing their `cost`s under `≤`, and `h` then `cost`
     equals `F(cost)` then a `k` monotonic on `≤`, then `h` is monotonic on `R`] \
     // lean:AOP.A9_1.monoAlg_of_cost@6156daa7
    #leanf("Freyd.Alg.monoAlg_of_cost_shunted") \
    #src[by the definition of `R` and shunting at the map `cost`, `F(R)h⊑hR` is `F(R)h cost⊑h cost ≤`,
     which the chain proves]],
  lean-calc(calc-cost),
)]<dp-cost>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the condition*], [*how it is discharged*]),

  [`F(R)h⊑hR` \ #src[Proposition 9.2, `R≜cost≤cost°`, `h cost=F(cost)k`,
 `F(≤)k⊑k≤`]],
   // lean:AOP.A9_1.monoAlg_of_cost@6156daa7
  [monotonicity when the cost is itself a fold with a step `k` monotonic on `≤`],
  [`F(R∩(H°H))h⊑hR` \ #src[Proposition 9.3, `R≜cost≤cost°`,
   `h cost=F(⟨cost,H°⟩)k`, `F(≤×𝟙)k⊑k≤`, `H°` simple;
 ]],
   // lean:AOP.A9_1.monoAlg_in_context@f0a1b13c
  [monotonicity *in context*: `k` may also read the input the part was built from],
  [`QF(H)h⊑F(H)hR` at `Q≜F(U,V)` \ #src[Proposition 9.4, `U`, `V` preorders, `F(U,R)h⊑hR`,
   `VH⊑HR`]],
  // combined row: Theorem 9.2
  [both conditions at once, split along the two arguments of a bifunctor],
)]<dp-conditions>

// B&dM Proposition 9.3, p. 223: the book's hints, one row each; B&dM's `H°` is `S` here.
#disp(num: "Proposition 9.3")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.monoAlg_in_context") \
    #src[improving each part by `R` within its `S`-context, then assembling by `h`, is below `hR`]],
     // lean:AOP.A9_1.monoAlg_in_context@f0a1b13c
  // two rows: seven panels in one row shrink the bundles past reading
  lean-calc(calc-ctx, breaks: (6,)),
)]<dp-context-mono>

// B&dM Proposition 9.4, pp. 223–224, "argue as follows": the thinning condition at `Q≜G(U,V)`,
// the book's hints one row each, without the converse B&dM takes (the note's `R` is his `R°`).
#disp(num: "Proposition 9.4")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.birelator_thin_condition") \
    #src[thinning the parts by `U` in the first argument and by `V` in the second (`G(U,V)`), then
     solving by `H` and assembling by `h`, gives only what solving and assembling and then improving
     by `R` gives (`G(𝟙,H)hR`)]],
     // lean:AOP.A9_1.birelator_thin_condition@178e7cca
  lean-calc(calc-bithin),
)]<dp-bifunctor-thin>

== The string edit problem

// B&dM §9.2, p. 225.  The section numbers no equation.  `base` and `step` are reused for the
// tabulating fold at the foot of the table; they are not `edit`'s.
#disp[
  - #leanf("Freyd.Alg.RelSet.Edit.op_cases") \
    #src[an edit operation copies, deletes or inserts one character]
    // lean:AOP.A9_2_Edit.op_cases@c6eaf29f
  - #leanf("Freyd.Alg.RelSet.Edit.F_obj") \
    #src[`F(Op,X)` is the empty sequence or one operation paired with an `X`]
    // lean:AOP.A9_2_Edit.F_obj@c75acbc8
  - #leanf("Freyd.Alg.RelSet.Edit.edit_cata") \
    #src[`edit` is the fold of `[base,step]` over an edit sequence, returning the two strings it
     reconstitutes]
    // lean:AOP.A9_2_Edit.edit_cata@2dc97e76
  - #leanf("Freyd.Alg.RelSet.Edit.length_cata") \
    #src[the fold of `[zero,π₂ succ]` counts the operations of a sequence]
    // lean:AOP.A9_2_Edit.length_cata@30fa5c4d
  - #leanf("Freyd.Alg.RelSet.Edit.R_eq") \
    #src[`R` relates `es` to `fs` when `es` is no longer than `fs`]
    // lean:AOP.A9_2_Edit.R_eq@0f7a4661
  - #leanf("Freyd.Alg.RelSet.Edit.V_eq") \
    #src[`V` relates two pairs of strings when each string of the first is a suffix of the matching
     string of the second]
    // lean:AOP.A9_2_Edit.V_eq@dca965f7
  - #leanf("Freyd.Alg.RelSet.Edit.Q_inl") \
    #src[`Q` is the identity on the `base` summand]
    // lean:AOP.A9_2_Edit.Q_inl@881e94ca
  - #leanf("Freyd.Alg.RelSet.Edit.Q_inr") \
    #src[on the `step` summand `Q` compares any two operations (`U≜⊤`) and the two pairs of strings
     by `V`]
    // lean:AOP.A9_2_Edit.Q_inr@3c2b60fa
  - #leanf("Freyd.Alg.RelSet.Edit.empty_iff") \
    #src[`empty` is the coreflexive holding only at the pair of two empty strings]
    // lean:AOP.A9_2_Edit.empty_iff@0a966621
  - #leanf("Freyd.Alg.RelSet.Edit.unstep_sound") \
    #src[every decomposition `unstep` returns is sent back to its input by `step`]
    // lean:AOP.A9_2_Edit.unstep_sound@d5b21374
]<edit-defn>

// `α`, `[base,step]` and `unstep` are maps, so each row is one equation, input | output.
#disp[#table(columns: 2, align: left + horizon, inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*`x`*], [*`α(x)`*]),
  [#leanf("Freyd.Alg.RelSet.Edit.con_nil.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.con_nil.rhs")],
  // lean:AOP.A9_2_Edit.con_nil@56d08b95
  [#leanf("Freyd.Alg.RelSet.Edit.con_cons.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.con_cons.rhs")],
  // lean:AOP.A9_2_Edit.con_cons@347d25ed
)]<edit-defn-alpha>

#disp[#table(columns: 2, align: left + horizon, inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*`x`*], [*`[base,step](x)`*]),
  [#leanf("Freyd.Alg.RelSet.Edit.base_nil.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.base_nil.rhs")],
  // lean:AOP.A9_2_Edit.base_nil@eba6cc46
  [#leanf("Freyd.Alg.RelSet.Edit.step_cpy.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.step_cpy.rhs")],
  // lean:AOP.A9_2_Edit.step_cpy@ef7fd738
  [#leanf("Freyd.Alg.RelSet.Edit.step_del.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.step_del.rhs")],
  // lean:AOP.A9_2_Edit.step_del@eee5b78e
  [#leanf("Freyd.Alg.RelSet.Edit.step_ins.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.step_ins.rhs")],
  // lean:AOP.A9_2_Edit.step_ins@1fed2e53
)]<edit-defn-step>

#disp[#table(columns: 2, align: left + horizon, inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*`p`*], [*`unstep(p)`*]),
  [#leanf("Freyd.Alg.RelSet.Edit.unstep_nil.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.unstep_nil.rhs")],
  // lean:AOP.A9_2_Edit.unstep_nil@1e0900c5
  [#leanf("Freyd.Alg.RelSet.Edit.unstep_del.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.unstep_del.rhs")],
  // lean:AOP.A9_2_Edit.unstep_del@07222c75
  [#leanf("Freyd.Alg.RelSet.Edit.unstep_ins.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.unstep_ins.rhs")],
  // lean:AOP.A9_2_Edit.unstep_ins@d0e84c5e
  [#leanf("Freyd.Alg.RelSet.Edit.unstep_cons.lhs.arg")], [#leanf("Freyd.Alg.RelSet.Edit.unstep_cons.rhs")],
  // lean:AOP.A9_2_Edit.unstep_cons@008bce13
)]<edit-defn-unstep>

// The two strings are a PRODUCT, hence TWO WIRES, and every box here spans them: nothing in the
// chain acts on one string alone.  `Δ` is the relator `X↦X×X`, so `[Char]×[Char]` is `Δ`, `list`,
// `Char` — sugar undone at the ends too.
#disp[#calc-table(
  Thm[`mle=(empty→nil,unstep list((𝟙×mle)cons) minlist(R))`, #h(6pt) #leanf("Freyd.Alg.RelSet.Edit.edit_laws") \
    #src[a shortest edit sequence from which both strings can be reconstituted is one pass over the
     two of them, each step copying, deleting or inserting one character and the best sequence for
     what is left taken from the entries already computed]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Edit.edit_laws.rhs"),
    [#src[the specification — @edit-defn]])],
  // `edit°` eats `Δ` and the source `list` and MAKES the target one, so every strand lands on it;
  // `est(R) : P([Op])⟶[Op]` kills the set, so its wire spans the `E` lane down to the object.
  [#lean("Freyd.Alg.RelSet.Edit.edit_laws.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Edit.edit_laws.lhs.body"),
    [
     // edit_mono row: Theorem 9.2
     #src[at `Q≜𝟙+(U×V)`. Monotonicity `F(R)α⊑αR`
 #src[] is Proposition 9.2 at
      // lean:AOP.A9_2_Edit.edit_mono@02093686
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
  // loop between them.  `thin(Q) : P(F−)⟶P(F−)` rearranges the set alone: a bead on the `E` wire.
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

// B&dM p.226, "immediate from Proposition 9.2": the proposition's argument at `length`, one row
// per fact.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Edit.edit_mono") \
    #src[comparing the tails by `R` and then putting an operation in front (`F(R)α`) relates only
     sequences that `R` also relates once the operation is in front (`αR`)]],
     // lean:AOP.A9_2_Edit.edit_mono@02093686
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Edit.edit_mono_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Edit.edit_mono_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_mono_step1.rhs"),
    [#src[`R≜length≤length°` — @edit-defn; `F` preserves composition]])],
     // lean:AOP.A9_2_Edit.edit_mono_step1@bc06a294
  [#lean("Freyd.Alg.RelSet.Edit.edit_mono_step1.rhs", step: true)],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Edit.edit_mono_step2.rhs"),
    [#src[`length` is a map, so entire: `𝟙⊑length length°`]])],
     // lean:AOP.A9_2_Edit.edit_mono_step2@31a5bbaf
  [#lean("Freyd.Alg.RelSet.Edit.edit_mono_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_mono_step3.rhs"),
    [#src[`α length=F(length)[zero,π₂ succ]`: `length≜⦇[zero,π₂ succ]⦈` — @edit-defn]])],
     // lean:AOP.A9_2_Edit.edit_mono_step3@f2d71928
  [#lean("Freyd.Alg.RelSet.Edit.edit_mono_step3.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Edit.edit_mono_step4.rhs"),
    [#src[`length` is a map, so simple, and `F` is monotonic: `F(length°)F(length)⊑F(𝟙)=𝟙`]])],
     // lean:AOP.A9_2_Edit.edit_mono_step4@758407c4
  [#lean("Freyd.Alg.RelSet.Edit.edit_mono_step4.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Edit.edit_mono_step5.rhs"),
    [#src[`succ` is monotonic on `≤`: `F(≤)[zero,π₂ succ]⊑[zero,π₂ succ]≤`]])],
     // lean:AOP.A9_2_Edit.edit_mono_step5@66ce5aee
  [#lean("Freyd.Alg.RelSet.Edit.edit_mono_step5.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_mono_step6.rhs"),
    [#src[`F(length)[zero,π₂ succ]=α length` again]])],
     // lean:AOP.A9_2_Edit.edit_mono_step6@52788976
  [#lean("Freyd.Alg.RelSet.Edit.edit_mono_step6.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_mono.rhs"),
    [#src[`R≜length≤length°` — @edit-defn]])],
  [#lean("Freyd.Alg.RelSet.Edit.edit_mono.rhs")],
)]<edit-mono>

// B&dM p.226, "it is sufficient to show that": Proposition 9.4's argument at `Q≜F(⊤,V)`.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Edit.edit_thin_condition") \
    #src[every edit sequence built from a decomposition `Q` puts above a given one — any operation,
     each string lengthened at the front — is at least as long as one built from the given one]],
     // lean:AOP.A9_2_Edit.edit_thin_condition@e22f4fe4
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Edit.edit_thin_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Edit.edit_thin_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_thin_step1.rhs"),
    [#src[`Q≜𝟙+(U×V)` is `F(U,V)` at `U≜⊤` — @edit-defn; and the bifunctor `F` preserves
      composition: `F(U,V)F(𝟙,edit°)=F(U,V edit°)`]])],
     // lean:AOP.A9_2_Edit.edit_thin_step1@d6e83157 lean:AOP.A9_2_Edit.Fbimap_comp@65b27e12
  [#lean("Freyd.Alg.RelSet.Edit.edit_thin_step1.rhs", step: true)],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Edit.edit_thin_step2.rhs"),
    [#src[Proposition 9.4's second condition `V edit°⊑edit° R` — @edit-V]])],
     // lean:AOP.A9_2_Edit.edit_thin_step2@fa716636
  [#lean("Freyd.Alg.RelSet.Edit.edit_thin_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_thin_step3.rhs"),
    [#src[`F` preserves composition: `F(U,edit° R)=F(𝟙,edit°)F(U,R)`]])],
     // lean:AOP.A9_2_Edit.edit_thin_step3@cf285d6c
  [#lean("Freyd.Alg.RelSet.Edit.edit_thin_step3.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Edit.edit_thin_step4.rhs"),
    [#src[Proposition 9.4's first condition `F(⊤,R)α⊑αR`, left as an exercise in the book: `cons`
      adds one to both lengths whatever the two operations are]])],
     // lean:AOP.A9_2_Edit.edit_thin_step4@d0f1f0c6
  [#lean("Freyd.Alg.RelSet.Edit.edit_thin_step4.rhs")],
)]<edit-thin>

// B&dM p.226: the second condition of Proposition 9.4, split at `V°=(suffix×𝟙)(𝟙×suffix)`.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Edit.edit_Vrecip") \
    #src[cutting a front off either string an edit sequence produces (`edit V°`) leaves a pair that
     a sequence no longer produces (`R° edit`)]],
     // lean:AOP.A9_2_Edit.edit_Vrecip@1d49fb2e
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Edit.edit_Vrecip_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Edit.edit_Vrecip_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_Vrecip_step1.rhs"),
    [#src[`V≜suffix°×suffix°`, and `×` preserves composition]])],
     // lean:AOP.A9_2_Edit.edit_Vrecip_step1@0604c8cb
  [#lean("Freyd.Alg.RelSet.Edit.edit_Vrecip_step1.rhs", step: true)],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Edit.edit_Vrecip_step2.rhs"),
    [#src[`edit (suffix×𝟙)⊑R° edit`: drop the operation that produced the head, or weaken its
      `cpy` to an `ins`. Proved by induction at `suffix` directly, not through `suffix=tail*` and
      `BA⊑CB⟹BA*⊑C*B` as the book does]])],
     // lean:AOP.A9_2_Edit.edit_Vrecip_step2@5adf6ffd lean:AOP.A9_2_Edit.edit_suffix_left@dda69ad1
  [#lean("Freyd.Alg.RelSet.Edit.edit_Vrecip_step2.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Edit.edit_Vrecip_step3.rhs"),
    [#src[`edit (𝟙×suffix)⊑R° edit`, the mirror image: `cpy` weakens to a `del`]])],
     // lean:AOP.A9_2_Edit.edit_Vrecip_step3@9062388e lean:AOP.A9_2_Edit.edit_suffix_right@6e4ee2a2
  [#lean("Freyd.Alg.RelSet.Edit.edit_Vrecip_step3.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Edit.edit_Vrecip_step4.rhs"),
    [#src[`R°` is transitive, `≤` being so]])],
     // lean:AOP.A9_2_Edit.edit_Vrecip_step4@12b537e9
  [#lean("Freyd.Alg.RelSet.Edit.edit_Vrecip_step4.rhs")],
)]<edit-V>

// B&dM p.227, "base and step have disjoint ranges": Proposition 9.1's hypothesis.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Edit.edit_disj") \
    #src[no pair of strings is both a result of `step` and the result `([],[])` of `base`]],
     // lean:AOP.A9_2_Edit.edit_disj@6767bb19 lean:AOP.A9_2_Edit.Freyd.Alg.RelSet.Edit.base@3b1de06b lean:AOP.A9_2_Edit.empty@ff28cd4c
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Edit.edit_disj_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Edit.edit_disj_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_disj_step1.rhs"),
    [#src[`base` returns only `([],[])`, so `base°=empty base°`]])],
     // lean:AOP.A9_2_Edit.edit_disj_step1@3739ccad
  [#lean("Freyd.Alg.RelSet.Edit.edit_disj_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_disj_step2.rhs"),
    [#src[`step empty=𝟘`: `cpy` and `del` put a character on the left string, `ins` one on the
      right]])],
     // lean:AOP.A9_2_Edit.edit_disj_step2@642314c2
  [#lean("Freyd.Alg.RelSet.Edit.edit_disj_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Edit.edit_disj.rhs"),
    [#src[`𝟘` composed with anything is `𝟘`]])],
  [#lean("Freyd.Alg.RelSet.Edit.edit_disj.rhs")],
)]<edit-disj>

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

// B&dM (9.5), p. 232: the book's five hints, one row each.
#disp(num: "(9.5)")[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Bracket.mct_cost_alg") \
    #src[pairing each subtree with its cost and its flattening and then applying `g` gives what
     building the tree by `[tip,bin]` and taking its `cost` gives]],
     // lean:AOP.A9_3_Bracket.mct_cost_alg@a8bdfa31
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step1.rhs"),
    [#src[definition of `g`; coproducts and products — @mct-defn]])],
     // lean:AOP.A9_3_Bracket.mct_cost_alg_step1@45921a50
  [#lean("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step2.rhs"),
    [#src[`flatten sz=size`, since `sb` is associative — @mct-defn]])],
     // lean:AOP.A9_3_Bracket.mct_cost_alg_step2@4e428835
  [#lean("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step3.rhs"),
    [#src[`⟨cost,size⟩≜⦇[opt,opb]⦈`, at a node `bin⟨cost,size⟩=⟨cost,size⟩² opb`]])],
     // lean:AOP.A9_3_Bracket.mct_cost_alg_step3@7809a574
  [#lean("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step3.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step4.rhs"),
    [#src[`tip cost=zero`; products, `⟨cost,size⟩π₁=cost`]])],
     // lean:AOP.A9_3_Bracket.mct_cost_alg_step4@a9886b38
  [#lean("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step4.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step5.rhs"),
    [#src[coproducts, `[tip cost,bin cost]=[tip,bin] cost`]])],
     // lean:AOP.A9_3_Bracket.mct_cost_alg_step5@43028133
  [#lean("Freyd.Alg.RelSet.Bracket.mct_cost_alg_step5.rhs")],
)]<mct-cost>

// B&dM (9.6), p. 232: the book's four hints, one row each.
#disp(num: "(9.6)")[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Bracket.mct_g_mono") \
    #src[raising the cost of either subtree (`≤×𝟙` in both slots) and then applying `g` returns a
     value at least what `g` returns on the costs before raising (`g≤`)]],
     // lean:AOP.A9_3_Bracket.mct_g_mono@10f38142
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.mct_g_mono_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Bracket.mct_g_mono_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.mct_g_mono_step1.rhs"),
    [#src[definition of `g` — @mct-defn]])],
     // lean:AOP.A9_3_Bracket.mct_g_mono_step1@bfddbbdc
  [#lean("Freyd.Alg.RelSet.Bracket.mct_g_mono_step1.rhs", step: true)],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Bracket.mct_g_mono_step2.rhs"),
    [#src[definition of `opb`, and `+` monotonic]])],
     // lean:AOP.A9_3_Bracket.mct_g_mono_step2@43f63ff6
  [#lean("Freyd.Alg.RelSet.Bracket.mct_g_mono_step2.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Bracket.mct_g_mono_step3.rhs"),
    [#src[`≤` reflexive, so `zero⊑zero ≤`; coproducts]])],
     // lean:AOP.A9_3_Bracket.mct_g_mono_step3@5fae54f1
  [#lean("Freyd.Alg.RelSet.Bracket.mct_g_mono_step3.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.mct_g_mono_step4.rhs"),
    [#src[definition of `g` — @mct-defn]])],
     // lean:AOP.A9_3_Bracket.mct_g_mono_step4@cb9454b8
  [#lean("Freyd.Alg.RelSet.Bracket.mct_g_mono_step4.rhs")],
)]<mct-g-mono>

// ONE WIRE, `list⁺ A` to `tree A`, and one datatype lane carrying `list⁺` above the bead that eats
// it and `tree` below.  No thinning step: no decomposition of a list is preferable to another here.
#disp[#calc-table(
  Thm[`mct=(single→head tip,⟨init col,tail row⟩ mix)`, #h(6pt) #leanf("Freyd.Alg.RelSet.Bracket.mct_laws") \
    #src[a least-cost bracketing of `a₁⊕⋯⊕aₙ` is read off an array holding one best tree per
     non-empty segment, each entry built from the column to its left and the row below it]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.mct_laws.rhs"),
    [#src[the specification — @mct-defn]])],
  // `flatten°` eats `list⁺` and MAKES `tree`, so one lane carries both; `est(R) : P(tree A)⟶tree A`
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
      // lean:AOP.A9_3_Bracket.mct_cost_alg@a8bdfa31
      (the cost of a node reads only the cost and the
      flattening of its two subtrees) and (9.6) `(𝟙+(≤×𝟙)²)g⊑g≤`
 #src[] (`g` monotonic on `≤` in its two
      // lean:AOP.A9_3_Bracket.mct_g_mono@10f38142
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

// B&dM (9.7), pp. 233-234: the book's five hints, one step each, read left to right.
#disp(num: "(9.7)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Bracket.mct_rec") \
    #src[on a list of two or more elements, `mct` gives what `mix` gives on the column of its
     `init` and the row of its `tail`]],
     // lean:AOP.A9_3_Bracket.mct_rec@d5db4aed
  lean-chain(
    (none, "Freyd.Alg.RelSet.Bracket.mct_eq.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Bracket.mct_eq.rhs", src[`mct` — @mct-defn]),
     // lean:AOP.A9_3_Bracket.mct_eq@5c6a919c
    (EQ, "Freyd.Alg.RelSet.Bracket.mct_rec_step1.rhs", src[`splits` — @mct-defn]),
     // lean:AOP.A9_3_Bracket.mct_rec_step1@cab18148
    (EQ, "Freyd.Alg.RelSet.Bracket.mct_rec_step2.rhs",
      src[`graft`, `trees`; `zip list(f×g)=(list(f)×list(g)) zip`]),
     // lean:AOP.A9_3_Bracket.mct_rec_step2@bdfe8912
    (EQ, "Freyd.Alg.RelSet.Bracket.mct_rec_step3.rhs",
      src[`mix≜zip list(bin) minlist(R)` — @mct-defn]),
     // lean:AOP.A9_3_Bracket.mct_rec_step3@8ba2a32c
    (EQ, "Freyd.Alg.RelSet.Bracket.mct_rec_step4.rhs",
      src[`inits⁺=init inits`, `tails⁺=tail tails`; `row`, `col` — @mct-defn]),
     // lean:AOP.A9_3_Bracket.mct_rec_step4@c9829da7
  ),
)]<mct-rec>

// B&dM (9.8), p. 234: the book's five hints, one step each, read left to right.
#disp(num: "(9.8)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Bracket.col_rec") \
    #src[on a list of two or more elements, the column is what `next` makes of the column of its
     `init` and the row of its `tail`]],
     // lean:AOP.A9_3_Bracket.col_rec@11ff5e11
  lean-chain(
    (none, "Freyd.Alg.RelSet.Bracket.col_rec_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Bracket.col_rec_step1.rhs", src[`col` — @mct-defn]),
     // lean:AOP.A9_3_Bracket.col_rec_step1@b9b76e62
    (EQ, "Freyd.Alg.RelSet.Bracket.col_rec_step2.rhs", src[`inits=⟨init inits,𝟙⟩ snoc` on non-singletons]),
     // lean:AOP.A9_3_Bracket.col_rec_step2@42a73ac5
    (EQ, "Freyd.Alg.RelSet.Bracket.col_rec_step3.rhs",
      src[`snoc list(f)=(list(f)×f) snoc`; `col`]),
     // lean:AOP.A9_3_Bracket.col_rec_step3@b23c2989
    (EQ, "Freyd.Alg.RelSet.Bracket.col_rec_step4.rhs",
      src[(9.7) — @mct-rec; `next≜⟨π₁,mix⟩ snoc` — @mct-defn]),
     // lean:AOP.A9_3_Bracket.col_rec_step4@84225c07
  ),
)]<col-rec>

// B&dM (9.10), p. 235: the book's three hints, one step each, read left to right.
#disp(num: "(9.10)")[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Bracket.row_rec") \
    #src[on a list of two or more elements, the row is `mct` of the whole list consed onto the row
     of its `tail`]],
     // lean:AOP.A9_3_Bracket.row_rec@2ee70011
  lean-chain(
    (none, "Freyd.Alg.RelSet.Bracket.row_rec_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Bracket.row_rec_step1.rhs", src[`row` — @mct-defn]),
     // lean:AOP.A9_3_Bracket.row_rec_step1@8ee2d203
    (EQ, "Freyd.Alg.RelSet.Bracket.row_rec_step2.rhs", src[`tails=⟨𝟙,tail tails⟩ cons` on non-singletons]),
     // lean:AOP.A9_3_Bracket.row_rec_step2@53dda069
    (EQ, "Freyd.Alg.RelSet.Bracket.row_rec_step3.rhs",
      src[`cons list(f)=(f×list(f)) cons`; `row`]),
     // lean:AOP.A9_3_Bracket.row_rec_step3@27b9f396
  ),
)]<row-rec>

// B&dM (9.9), p. 234, by Exercise 9.13, p. 237: `col` as a loop, then the book's equivalent form.
#disp(num: "(9.9)")[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Bracket.col_cons") \
    #src[the column of `a` consed onto `x` is what `process` makes of `a` and the array of `x`]],
     // lean:AOP.A9_3_Bracket.col_cons@c6b5beca
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.col_cons_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Bracket.col_cons_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.col_cons_step1.rhs"),
    [#src[Exercise 9.13 with `k≜cons col`, `g≜tip wrap`, `h≜row`, `f≜next`: its two equations are
     (9.8) — @col-rec — at `a:[b]` and at `a:(u++[b])`, with `[a] col=[tip(a)]`]])],
     // lean:AOP.A9_3_Bracket.col_cons_step1@e278817f
  [#lean("Freyd.Alg.RelSet.Bracket.col_cons_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.col_cons_step2.rhs"),
    [#src[products]])],
     // lean:AOP.A9_3_Bracket.col_cons_step2@ef9df3eb
  [#lean("Freyd.Alg.RelSet.Bracket.col_cons_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.col_cons_step3.rhs"),
    [#src[definition of `process`]])],
     // lean:AOP.A9_3_Bracket.col_cons_step3@06b6dc0a
  [#lean("Freyd.Alg.RelSet.Bracket.col_cons_step3.rhs")],
)]<col-cons>

// B&dM pp. 235-236, "We reason:", the second component `tic list(row)` split off under our own names
// `tops`, `rests` and `newrows` (not the book's), so no bead carries a long composite.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Bracket.tops_rec") \
    #src[the trees at the top of the new rows are what `process` makes of `a` and the array of `x`,
     less its first]],
     // lean:AOP.A9_3_Bracket.tops_rec@56489cc3
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.tops_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Bracket.tops_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.tops_step1.rhs"),
    [#src[definition of `tops≜tic list(mct)`, our name]])],
     // lean:AOP.A9_3_Bracket.tops_step1@59fe41e2
  [#lean("Freyd.Alg.RelSet.Bracket.tops_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.tops_step2.rhs"),
    [#src[`tail list(f)=list(f) tail`; definition of `col`]])],
     // lean:AOP.A9_3_Bracket.tops_step2@331c9a78
  [#lean("Freyd.Alg.RelSet.Bracket.tops_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.tops_step3.rhs"),
    [#src[(9.9) — @col-cons]])],
     // lean:AOP.A9_3_Bracket.tops_step3@887fab92
  [#lean("Freyd.Alg.RelSet.Bracket.tops_step3.rhs")],
)]<tops-rec>

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Bracket.rests_eq") \
    #src[the rest of each new row is the array of `x`]],
     // lean:AOP.A9_3_Bracket.rests_eq@5c50e0a4
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.rests_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Bracket.rests_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.rests_step1.rhs"),
    [#src[definition of `rests≜tic list(tail row)`, our name]])],
     // lean:AOP.A9_3_Bracket.rests_step1@23371fac
  [#lean("Freyd.Alg.RelSet.Bracket.rests_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.rests_step2.rhs"),
    [#src[`tic list(tail)=π₂ inits`; definition of `array`]])],
     // lean:AOP.A9_3_Bracket.rests_step2@b93db82c
  [#lean("Freyd.Alg.RelSet.Bracket.rests_step2.rhs")],
)]<rests-eq>

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Bracket.newrows_rec") \
    #src[the rows of the array of `a:x` below its first are what `step` makes of `a` and the array
     of `x`]],
     // lean:AOP.A9_3_Bracket.newrows_rec@0453777f
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.newrows_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Bracket.newrows_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.newrows_step1.rhs"),
    [#src[definition of `newrows≜tic list(row)`, our name]])],
     // lean:AOP.A9_3_Bracket.newrows_step1@74ecf218
  [#lean("Freyd.Alg.RelSet.Bracket.newrows_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.newrows_step2.rhs"),
    [#src[(9.10) — @row-rec — on the non-singleton `tic` lists]])],
     // lean:AOP.A9_3_Bracket.newrows_step2@01b6024a
  [#lean("Freyd.Alg.RelSet.Bracket.newrows_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.newrows_step3.rhs"),
    [#src[`list⟨f,g⟩=⟨list(f),list(g)⟩ zip`; products; definitions of `tops` and `rests`]])],
     // lean:AOP.A9_3_Bracket.newrows_step3@346dfb8b
  [#lean("Freyd.Alg.RelSet.Bracket.newrows_step3.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.newrows_step4.rhs"),
    [#src[@tops-rec and @rests-eq; products; definition of `step`]])],
     // lean:AOP.A9_3_Bracket.newrows_step4@1493a82d
  [#lean("Freyd.Alg.RelSet.Bracket.newrows_step4.rhs")],
)]<newrows-rec>

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Bracket.array_cons") \
    #src[the array of `a` consed onto `x` is what `addcol` makes of `a` and the array of `x`]],
     // lean:AOP.A9_3_Bracket.array_cons@f952f1b1
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Bracket.array_cons_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Bracket.array_cons_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.array_cons_step1.rhs"),
    [#src[definition of `array`]])],
     // lean:AOP.A9_3_Bracket.array_cons_step1@8ccbea69
  [#lean("Freyd.Alg.RelSet.Bracket.array_cons_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.array_cons_step2.rhs"),
    [#src[`cons inits=⟨π₁ wrap,tic⟩ cons`, abbreviating `cons inits tail` by `tic`]])],
     // lean:AOP.A9_3_Bracket.array_cons_step2@5cb45254
  [#lean("Freyd.Alg.RelSet.Bracket.array_cons_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.array_cons_step3.rhs"),
    [#src[`cons list(f)=(f×list(f)) cons`; definition of `newrows`]])],
     // lean:AOP.A9_3_Bracket.array_cons_step3@f5fb37d5
  [#lean("Freyd.Alg.RelSet.Bracket.array_cons_step3.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.array_cons_step4.rhs"),
    [#src[`wrap row=tip wrap`]])],
     // lean:AOP.A9_3_Bracket.array_cons_step4@ae800583
  [#lean("Freyd.Alg.RelSet.Bracket.array_cons_step4.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Bracket.array_cons_step5.rhs"),
    [#src[@newrows-rec; products; definition of `addcol`]])],
     // lean:AOP.A9_3_Bracket.array_cons_step5@a1cfe883
  [#lean("Freyd.Alg.RelSet.Bracket.array_cons_step5.rhs")],
)]<array-cons>

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
  // lean:AOP.A9_4_Code.code_laws@5516bed1
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

// B&dM p.240, "By Proposition 9.4 we have to check that": the proposition's argument at
// `Q≜F(⊤+⊤,prefix°)`, its two conditions one row each.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Code.code_thin_condition") \
    #src[every code sequence built from a decomposition `Q` puts above a given one — a code element
     of the same kind, a longer front string — costs at least as much as one built from the given
     one]],
     // lean:AOP.A9_4_Code.code_thin_condition@00aae404
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Code.code_thin_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Code.code_thin_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Code.code_thin_step1.rhs"),
    [#src[`Q≜𝟙+(prefix°×(⊤+⊤))` is `F(⊤+⊤,prefix°)` — @code-defn]])],
     // lean:AOP.A9_4_Code.code_thin_step1@c5eac63a lean:AOP.A9_4_Code.Fbimap@f45fdcce
  [#lean("Freyd.Alg.RelSet.Code.code_thin_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Code.code_thin_step2.rhs"),
    [#src[the bifunctor `F` preserves composition: `F(U,prefix°)F(𝟙,decode°)=F(U,prefix° decode°)`]])],
     // lean:AOP.A9_4_Code.code_thin_step2@d3e2e959 lean:AOP.A9_4_Code.Fbimap_Fmap@1408119d
  [#lean("Freyd.Alg.RelSet.Code.code_thin_step2.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Code.code_thin_step3.rhs"),
    [#src[Proposition 9.4's second condition `prefix° decode°⊑decode° R`: dropping the last
      character drops the last `sym`, or shortens or drops the last pointer. Proved at `prefix`
      directly by induction, not through `init`]])],
     // lean:AOP.A9_4_Code.code_thin_step3@9c774e54 lean:AOP.A9_4_Code.code_V@3407acb5
  [#lean("Freyd.Alg.RelSet.Code.code_thin_step3.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Code.code_thin_step4.rhs"),
    [#src[`F` preserves composition: `F(U,decode° R)=F(𝟙,decode°)F(U,R)`]])],
     // lean:AOP.A9_4_Code.code_thin_step4@ff2b0d68 lean:AOP.A9_4_Code.Fmap_Fbimap@a683eae6
  [#lean("Freyd.Alg.RelSet.Code.code_thin_step4.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.RelSet.Code.code_thin_step5.rhs"),
    [#src[Proposition 9.4's first condition `F(⊤+⊤,R)α⊑αR`, left as an exercise in the book: `snoc`
      adds the cost of the last element to both sides, and `[c,p](⊤+⊤)=[c,p]`]])],
     // lean:AOP.A9_4_Code.code_thin_step5@2bc8116d lean:AOP.A9_4_Code.bytes_U@953e99c3
  [#lean("Freyd.Alg.RelSet.Code.code_thin_step5.rhs")],
)]<code-thin>

// B&dM p.240, "Since nil and extend have disjoint ranges": Proposition 9.1's hypothesis.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Code.code_disj") \
    #src[no string is both a result of `extend` and the result `[]` of `nil`]],
     // lean:AOP.A9_4_Code.code_disj@80dbea26 lean:AOP.A9_4_Code.null@2ab49554
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Code.code_disj_step1.lhs"), [])],
  [#lean("Freyd.Alg.RelSet.Code.code_disj_step1.lhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Code.code_disj_step1.rhs"),
    [#src[`nil` returns only `[]`, so `nil°=null nil°`]])],
     // lean:AOP.A9_4_Code.code_disj_step1@9698e2de
  [#lean("Freyd.Alg.RelSet.Code.code_disj_step1.rhs", step: true)],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Code.code_disj_step2.rhs"),
    [#src[`extend null=𝟘`: a symbol ends the string with a character, a pointer with its non-empty
      `zs`]])],
     // lean:AOP.A9_4_Code.code_disj_step2@49ebf5ab lean:AOP.A9_4_Code.extend_ne_nil@4f36ac2c
  [#lean("Freyd.Alg.RelSet.Code.code_disj_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Code.code_disj.rhs"),
    [#src[`𝟘` composed with anything is `𝟘`]])],
  [#lean("Freyd.Alg.RelSet.Code.code_disj.rhs")],
)]<code-disj>

#pagebreak(weak: true)
