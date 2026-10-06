#import "../note-prelude.typ": *
#show: note-chapter.with(6)
// note-split: chapter 6 — this header is written by scripts/note-split and stripped by scripts/note-join
= Recursive Programs <sec-recursive>

// B&dM chapter 6, p.137–163.  Every calculation in the text becomes a Lean theorem with one step
// declaration per step, drawn as a horizontal `lean-chain` under a `Thm[#leanf(...)]` header with one
// `#src` gloss and a `// lean:` marker, as diag/ch/16-greedy.typ does for B&dM chapter 10.  The ids
// are B&dM's own equation and theorem numbers; an unnumbered display is named by its page.  The
// inventory, Lean status and agent groups are in tmp/ch6-plan.md.  Statements are in DIAGRAM order.

== Digits of a number

// B&dM (6.1), p.138.  The book derives `val°` for `val=⦇[embed,op]⦈`; the calc is stated for any
// algebra `[g,h]`, and `val_converse_eq` is it at `g≜embed`, `h≜op`.
#import "../generated/Freyd.Alg.RelSet.Digits.cata_converse_eq.calc.typ" as calc-val
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Digits.cata_converse_eq") \
    #src[the converse of a fold over decimals undoes the algebra `[g,h]` and then either `wrap`, or
     the fold's converse on the front and `snoc`]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_eq@19be99a2
  lean-calc(calc-val),
  [#leanf("Freyd.Alg.RelSet.Digits.val_converse_eq") \
    #src[a number is read back into digits either as one nonzero digit, or by splitting off its
     last digit and reading back the rest]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.val_converse_eq@639ee2c7
)]<val-converse>
// B&dM p.139: `op(n,d)=10n+d` read backwards, and where `op°` and `embed°` are defined — which is what
// turns the join of (6.1) into a conditional.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  [#leanf("Freyd.Alg.RelSet.Digits.op_recip_iff") \
    #src[`op°` splits a number into its quotient and remainder by 10]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.op_recip_iff@78c25f21
  [#leanf("Freyd.Alg.RelSet.Digits.op_recip_defined") \
    #src[`op°` gives a pair with a nonzero first component exactly at the numbers with two or more digits]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.op_recip_defined@c44897b0
  [#leanf("Freyd.Alg.RelSet.Digits.embed_recip_defined") \
    #src[`embed°` gives a digit exactly at the one-digit numbers]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.embed_recip_defined@65abb14c
)]<op-recip>
// TODO p.139 digits: the join is a conditional; `val°` the unique solution, total; `digits=val°`.

== Least fixed points <sec-mu>

// B&dM Theorem 6.1, p. 140.  `μ` is read off a whole chapter of specifications from §@sec-dp on,
// and nothing before this said what it was.
#disp[#definition[
#leanf("Freyd.Alg.Monotonic") #h(4pt) — `φ` maps the hom-set `A⟶B` into itself with `X⊑Y⟹φ(X)⊑φ(Y)`.

`(μX : φ(X))` is the least `X : A⟶B` with `φ(X)⊑X`.
]]<mu-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

 // μX upper bound row: Theorem 6.1
 [#leanf("Freyd.Alg.mu_le") \ #src[]],
  [to bound `(μX : φ(X))` above, exhibit one `Y` the body does not grow past — the half §@sec-hylo
   and every chapter after it uses],
 // μX fixed point row: Theorem 6.1
 [#leanf("Freyd.Alg.mu_fixed") \ #src[]],
  [*Knaster–Tarski*: the least solution of `φ(X)⊑X` already solves `φ(X)=X`, so the least prefix
   point and the least fixed point are one relation],
 // B&dM (6.2), p.141: Theorem 6.1 at `φ(X)≜α°F(X)R`, since `⦇R⦈=(μX : α°F(X)R)`
 [#leanf("Freyd.Alg.relCata_le_of_prefixed") \ #src[(6.2)]],
  [a relation `X` that contains one unfolding of the fold's recursion at `X` contains the fold],
 // B&dM (6.3), p.141: `⦇R⦈` is also the greatest fixed point `(νX : α°F(X)R)`
 [#leanf("Freyd.Alg.le_relCata_of_postfixed") \ #src[(6.3)]],
  [a relation `X` contained in one unfolding of the fold's recursion at `X` is contained in the fold],
 // lean:AOP.A6_2.mu_le@9918bd39
 // lean:AOP.A6_2.mu_fixed@2d3d1a8a
 // lean:AOP.A6_2.relCata_le_of_prefixed@837a5bf7
 // lean:AOP.A6_2.le_relCata_of_postfixed@6d0c3236
 // lean:AOP.A6_2.relCata_eq_mu@c2d55908
 // lean:AOP.A6_2.relCata_eq_nu@0af949db
)]<mu-laws>

#import "../generated/Freyd.Alg.relCata_comp_prefixed.calc.typ" as calc-64p
#import "../generated/Freyd.Alg.relCata_le_comp.calc.typ" as calc-64
#import "../generated/Freyd.Alg.relCata_comp_postfixed.calc.typ" as calc-65p
#import "../generated/Freyd.Alg.comp_le_relCata.calc.typ" as calc-65
// B&dM (6.4), p.141, "easy exercise" (Ex 6.6): (6.2) at `X≜⦇R⦈S`, whose prefix-point condition is
// this chain.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.relCata_le_comp") \
    #src[if `S` followed by `R` absorbs `T` after `F(S)`, the fold of `T` is below the fold of `R`
     followed by `S`]],
  // lean:AOP.A6_2.relCata_le_comp@b54d0a6b
  // lean:AOP.A6_2.relCata_comp_prefixed@95daa9e8
  lean-calc(calc-64p),
  lean-calc(calc-64),
)]<cata-fusion-le>

// B&dM (6.5), p.141: (6.3) at `X≜⦇R⦈S`; the chain of (6.4) read backwards, its hypothesis reversed.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.comp_le_relCata") \
    #src[if `R` followed by `S` is absorbed by `F(S)` followed by `T`, the fold of `R` followed by `S`
     is below the fold of `T`]],
  // lean:AOP.A6_2.comp_le_relCata@5874cf45
  // lean:AOP.A6_2.relCata_comp_postfixed@aae78c87
  lean-calc(calc-65p),
  lean-calc(calc-65),
)]<fusion-le-cata>

== Hylomorphisms <sec-hylo>

// §@sec-hylo's panels, emitted by `./scripts/diagram --sigs … --src … --tgt … "<formula>"` plus
// `s: 100%`.  `sigs:` types the section's abstract letters; `frame: 5` is the ONE box every panel
// of the section draws in, so a step's two panels line up under `trow`'s `align: horizon`, and
// `top: 3` drops a lone bead to the height of the bead it stands against.
// 11.6.4a/b are sub theorems of Theorem 6.2, so all three chains share ONE table, headed by it.
// Each chain is one Lean `calc`: hylo_le_of_prefixed is a term chain ending in its hypothesis, then
// a chain of statements (adjunction, fold leastness, adjunction).

// B&dM p. 142, mirrored into diagram order.  The `F` wire is born at the leading converse and dies
// at the trailing algebra; every step shortens it, and by the last panel it is gone.  B&dM p. 143,
// mirrored: two adjunction steps carry `⦇S⦈°` out of the way and back, the reduce's own leastness
// fires between them, and the `F` wire's top end walks from `α°` up to `S°`.  Theorem 6.2's two
// inclusions are these two rows: one `⊑` is hylo_fixed
// through @mu-laws, the other hylo_le_of_prefixed at the prefix point `μ`.
#import "../generated/Freyd.Alg.hylo_fixed.calc.typ" as calc-hf
#import "../generated/Freyd.Alg.hylo_le_of_prefixed_chain.calc.typ" as calc-hlc
#import "../generated/Freyd.Alg.hylo_le_of_prefixed.calc.typ" as calc-hl
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.hylo_eq_mu") \
    #src[hylomorphism theorem: a hylomorphism is the least fixed point of a certain recursion equation]],
  // lean:AOP.A6_3.hylo_eq_mu@5da9c8e8
  // lean:AOP.A6_3.hylo_fixed@67ca7394
  // lean:AOP.A5_5.InitialAlgebra.recip_alpha_alpha@5dcef861
  // lean:AOP.A6_2.relCata_le_of_prefixed@837a5bf7
  lean-calc(calc-hf),
  lean-calc(calc-hlc),
  lean-calc(calc-hl),
)]<hylo-mu>

// B&dM Corollary 6.1, p.143: Theorem 6.2 at `R≜[R₁,R₂]`, `S≜[S₁,S₂]` over `F(X)=G(X)+H(X)`; the calc
// is the body under the `μ`.
#import "../generated/Freyd.Alg.hylo_body_coprod.calc.typ" as calc-hcop
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.hylo_eq_mu_coprod") \
    #src[when both algebras are case splits over the same sum, the recursion runs each case on its
     own and unites the results]],
  // lean:AOP.A6_3.hylo_eq_mu_coprod@aaac99b8
  lean-calc(calc-hcop),
)]<hylo-coprod>

== Fast exponentiation and modulus computation

// B&dM p.144–145: the argument for `exp(a)`, stated once for a map `f` and an algebra `[zero f,h]` with the
// fusion condition `shift f=(f×𝟙)h`; `exp` and `mod` are it at `[one,op(a)]`, `[zero,op(b)]`.
#import "../generated/Freyd.Alg.RelSet.FastExp.convert_program.calc.typ" as calc-convert
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.FastExp.convert_program") \
    #src[once `f` turns `shift` into `h`, the recursion that halves the
     argument at each step computes `f`]],
  // lean:AOP.A6_4_FastExp.RelSet.FastExp.convert_program@c1787858
  lean-calc(calc-convert),
)]<convert-program>

// B&dM p.145: the two fusion conditions for `exp(a)`, then the program.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.FastExp.exp_program") \
    #src[the recursion that halves the exponent at each step computes `a` to the power `b`]],
  // lean:AOP.A6_4_FastExp.RelSet.FastExp.exp_program@08ea7ea9
  [#leanf("Freyd.Alg.RelSet.FastExp.exp_zero") \ #src[`a` to the power `0` is `1`]],
  // lean:AOP.A6_4_FastExp.RelSet.FastExp.exp_zero@753de5ee
  [#leanf("Freyd.Alg.RelSet.FastExp.exp_shift") \
    #src[`a` to the power `2n+d` is `op(a)` of `a` to the power `n` and `d`]],
  // lean:AOP.A6_4_FastExp.RelSet.FastExp.exp_shift@943dfec6
)]<fast-exp>

// B&dM p.145: the same argument for `mod(b)`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.FastExp.mod_program") \
    #src[the recursion that halves `a` at each step computes the remainder of `a` by `b`]],
  // lean:AOP.A6_4_FastExp.RelSet.FastExp.mod_program@82bb412b
  [#leanf("Freyd.Alg.RelSet.FastExp.mod_zero") \ #src[`0 mod b` is `0`]],
  // lean:AOP.A6_4_FastExp.RelSet.FastExp.mod_zero@9b6e59c5
  [#leanf("Freyd.Alg.RelSet.FastExp.mod_shift") \
    #src[`(2a+d) mod b` is `op(b)` of `a mod b` and `d`]],
  // lean:AOP.A6_4_FastExp.RelSet.FastExp.mod_shift@8ad8e239
)]<fast-mod>

== Unique fixed points

// TODO p.146 counterexample: `X=⦇[zero,positive]⦈°⦇[zero,id]⦈` is the coreflexive at 0, its equation
//   `[zero,positive]°(𝟙+X)[zero,id] = zero°zero ∪ positive X` (2 steps) is also solved by `X=𝟙`.
// TODO p.147 inductive: `R⊑S` ⟹ `R` inductive; `S` inductive iff `S⁺` is — Lean AOP.A6_5.inductive_of_le,
//   inductive_transClosure_iff; no picture (statements about `Inductive`, not arrows).
// B&dM p.147 (Ex 6.13)
#import "../generated/Freyd.Alg.div_div_comp_le.calc.typ" as calc-ind
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.div_div_comp_le") \
    #src[`((X/R)/S)` followed by `RR` stays below `X` when `RR⊑SR`] \
    #leanf("Freyd.Alg.inductive_of_comp_le") \
    #src[`R` is inductive when `RR⊑SR` for an inductive `S`]],
    // lean:AOP.A6_5.div_div_comp_le@fba45cc1
    // lean:AOP.A6_5.inductive_of_comp_le@17eb3b43
  lean-calc(calc-ind),
)]<inductive-comp-le>
// TODO p.148 member: `member(id)=𝟙`, `member(FG)=member(F)member(G)`, `member(P)=∈`,
//   `member(T)=setify(T)∈` — Lean idMembership, compMembership; `P`, `T` missing.
// B&dM p.148, the constant, sum and product rows
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.member_const") \
    #src[a constant relator records no elements, so its membership is empty]],
    // lean:AOP.A6_5.member_const@91d83a84
  Thm(cols: 1)[#leanf("Freyd.Alg.member_sum") \
    #src[a member of `F+G` is a member of whichever summand the value is in]],
    // lean:AOP.A6_5.member_sum@f2ed47bd
  Thm(cols: 1)[#leanf("Freyd.Alg.member_prod") \
    #src[a member of `F×G` is a member of either component]],
    // lean:AOP.A6_5.member_prod@fefd83ec
)]<member-sum-prod>
// TODO p.148 lax: `F(R)member ⊑ member R`, the largest lax natural `F ⟶ id`, hence unique — Lean
//   LaxMembership.laxNatural, largestLax_unique.
// TODO p.148 member α°: `α°member(F)` inductive; examples `[zero,succ]°[𝟘,𝟙]=succ°`,
//   `[nil,cons]°[𝟘,outr]=cons°outr=tail` — Lean missing.
// B&dM Theorem 6.3, p.149
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thm63_unique") \
    #src[when `S member` is inductive, two solutions `X`, `Y` of `X=SF(X)R` are equal]],
    // lean:AOP.A6_5.thm63_unique@7de915fc
)]<thm63-unique>

// B&dM Theorem 6.3 (entire), p.149
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thm63_entire") \
    #src[when `S member` is inductive and `S`, `R` are entire, a pre-fixed point of `X↦SF(X)R` is entire]],
    // lean:AOP.A6_5.thm63_entire@d76aca23
)]<thm63-entire>

// B&dM Corollary 6.2, p.149
#import "../generated/Freyd.Alg.cor62_simple.calc.typ" as calc-62
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.cor62") \
    #src[when `g member` is inductive and `f`, `g` are maps, the solution of `X=gF(X)f` is a map] \
    #leanf("Freyd.Alg.cor62_simple") \
    #src[`(gF(Y)f)°` followed by `X` stays below `𝟙` when `g`, `f` are simple and `Y°X⊑𝟙`]],
    // lean:AOP.A6_5.cor62@6df24a22
    // lean:AOP.A6_5.cor62_simple@efffca93
  lean-calc(calc-62),
)]<cor62>
// B&dM Corollary 6.3, p.149
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.cor63") \
    #src[when `R°member` is inductive and `R` is surjective, the fold `⦇R⦈` is surjective]],
    // lean:AOP.A6_5.cor63@a768e5a5
  lean-chain(
    (none, "Freyd.Alg.cor63.lhs", []),
    (SQ, "Freyd.Alg.cor63.rhs", src[@thm63-entire at `S=R°`]),
  ),
)]<cor63>

// B&dM Theorem 6.4, p.150
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thm64") \
    #src[a map `f` with `Rf⊑F(f)α`, for a surjective `R`, has the fold `⦇R⦈` as its converse]],
    // lean:AOP.A6_5.thm64@3db80141
  lean-chain(
    (none, "Freyd.Alg.thm64_forward.lhs", []),
    (SQ, "Freyd.Alg.thm64_forward.rhs", src[shunting `f`, fusion, `Rf⊑F(f)α`]),
  ),
    // lean:AOP.A6_5.thm64_forward@f35729d1
  lean-chain(
    (none, "Freyd.Alg.thm64_backward.lhs", []),
    (SQ, "Freyd.Alg.thm64_backward.rhs", src[@cor63 and `⦇R⦈f⊑𝟙`]),
  ),
    // lean:AOP.A6_5.thm64_backward@117de421
)]<thm64>

// B&dM Theorem 6.4 (the claim), p.150
#import "../generated/Freyd.Alg.thm64_claim.calc.typ" as calc-64c
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thm64_claim") \
    #src[`R°member` is below `α°member` conjugated by `f`, so it is inductive when `α°member` is]],
    // lean:AOP.A6_5.thm64_claim@4b02dea3
  lean-calc(calc-64c),
)]<thm64-claim>

== Sorting by selection

// B&dM (6.6), p.151.  The preorder `R` is fixed, so `ordered` and `ok`
// carry no argument.
#disp[#deftab(
  [#leann("Freyd.Alg.RelSet.ListRel.orderedP")], [#leant("Freyd.Alg.RelSet.ListRel.orderedP")],
  [#leanf("Freyd.Alg.RelSet.ListRel.orderedP")],
  [every element is `R`-below each element after it],
  [#leann("Freyd.Alg.RelSet.ListRel.ordered")], [#leant("Freyd.Alg.RelSet.ListRel.ordered")],
  [#leanf("Freyd.Alg.RelSet.ListRel.ordered")],
  [the coreflexive passing exactly the lists `orderedP` holds of],
  [#leann("Freyd.Alg.RelSet.Sort.ok")], [#leant("Freyd.Alg.RelSet.Sort.ok")],
  [#leanf("Freyd.Alg.RelSet.Sort.ok")],
  [the coreflexive passing `(a, x)` when `a` is `R`-below every element of `x`],
)]
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.ordered_cata") \
    #src[a list is sorted exactly when the fold that rebuilds it passes `ok` at every `cons`, i.e.
     each head is `R`-below every element after it]],
     // lean:AOP.A6_6b_SortConcrete.ordered_cata@38414536
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.ordered_cata.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.ordered_cata.rhs", src[fold uniqueness]),
  ),
)]<sort-ordered>

// B&dM 6.6a, p.152, "selection sort": the specification `perm ordered` refined to the converse of a fold.
// `perm` is strictly natural (lean:AOP.A6_6b_SortConcrete.perm_strictNatural@f0271ba3).
#import "../generated/Freyd.Alg.RelSet.Sort.selection_sort.calc.typ" as calc-selection
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.selection_sort") \
    #src[every output of unfolding the input by `select` is a sorted permutation of it]],
     // lean:AOP.A6_6b_SortConcrete.selection_sort@617e20db
  lean-calc(calc-selection),
)]<sort-selection>

// B&dM 6.6b, p.153, the fusion proviso; `select` is specified by `select°⊑ok cons perm`.
#import "../generated/Freyd.Alg.RelSet.Sort.select_proviso.calc.typ" as calc-select
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.select_proviso") \
    #src[permuting the tail and then undoing `select` lands among the `ok` conses of a permutation]],
     // lean:AOP.A6_6b_SortConcrete.select_proviso@924131a0
  lean-calc(calc-select),
)]<sort-select>
// TODO p.153 select-cata: `select = embed ⦇[base,step]⦈` with `base ⊆ wrap perm cons°ok`,
//   `(𝟙×cons°ok)step ⊆ cons perm cons°ok`; `base(a)=(a,[])`, `step`.
// B&dM 6.6c, p.153, the program.  Uniqueness of the solution is Theorem 6.3 (thm63_unique), which
// needs a `member` for the list functor that Lean lacks; drawn here is that `⦇[nil,select°]⦈°` IS a solution.  `nil` is strictly natural
// (lean:AOP.A6_6b_SortConcrete.nil_strictNatural@c7a02590).
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.sort_rec") \
    #src[selection sort returns `[]` on `[]`, and otherwise selects `(a,y)`, sorts `y` and conses
     `a` back on]],
     // lean:AOP.A6_6b_SortConcrete.sort_rec@19c1b660
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.sort_rec.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.sort_rec.rhs", src[unfolding the converse of a fold]),
  ),
)]<sort-rec>
// B&dM 6.6d, p.154, "quicksort": the specification `perm ordered` refined through a tree; `R` is a
// preorder, which the claim `flatten ordered = inordered flatten` needs.
#import "../generated/Freyd.Alg.RelSet.Sort.quicksort.calc.typ" as calc-quick
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.quicksort") \
    #src[every output of unfolding the input by `split` into a tree and flattening that tree is a
     sorted permutation of the input]],
     // lean:AOP.A6_6e_Quicksort.quicksort@2ff8cd0e
  lean-calc(calc-quick),
)]<sort-quick>

// B&dM 6.6d, p.154, "claim: ordered flatten = inordered flatten"; `inordered = ⦇[null, fork check]⦈` is a
// coreflexive (lean:AOP.A6_6e_Quicksort.inordered_coref@99102d71) and `R` must be transitive.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.flatten_ordered") \
    #src[flattening a tree and then testing the list for order is the same as testing the tree with
     `inordered` and then flattening]],
     // lean:AOP.A6_6e_Quicksort.flatten_ordered@0f755413
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.flatten_ordered.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.flatten_ordered.rhs", src[`R` transitive: a flattened tree is ordered iff every node passes `check`]),
  ),
)]<sort-flatten-ordered>

// B&dM 6.6e, p.155, the three claims left as exercises, the first: `F(flatten)` carries `check` to `check'`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.check_flatten") \
    #src[testing a fork with `check` and then flattening both subtrees equals flattening both subtrees and
     then testing with `check'`, since `intree` of a tree is `inlist` of its flattening]],
     // lean:AOP.A6_6e_Quicksort.check_flatten@65a38823
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.check_flatten.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.check_flatten.rhs", src[`b intree x ⟺ b inlist flatten(x)`]),
  ),
)]<sort-check-flatten>

// B&dM 6.6e, p.155, the second claim: `perm join = F(perm) join perm`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.join_perm") \
    #src[permuting the list `x ++ [a] ++ y` is the same as first permuting `x` and `y` and then permuting the
     joined list]],
     // lean:AOP.A6_6e_Quicksort.join_perm@1c05221d
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.join_perm.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.join_perm.rhs", src[`perm` is transitive and closed under `++`]),
  ),
)]<sort-join-perm>

// B&dM 6.6e, p.155, the third claim: `F(perm) check' = check' F(perm)`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.check'_perm") \
    #src[testing a fork of lists with `check'` and then permuting both parts equals permuting both parts and
     then testing, since permuting a list leaves its members unchanged]],
     // lean:AOP.A6_6e_Quicksort.check'_perm@49e70eef
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.check'_perm.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.check'_perm.rhs", src[`b inlist x ⟺ b inlist perm(x)`]),
  ),
)]<sort-checkp-perm>

// B&dM 6.6e, p.155, the fusion proviso; `split` is specified by `split°⊑check' join perm`.
#import "../generated/Freyd.Alg.RelSet.Sort.split_proviso.calc.typ" as calc-split
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.split_proviso") \
    #src[undoing `split` and then flattening and permuting both parts lands among the `check`ed
     forks whose flattening is permuted]],
     // lean:AOP.A6_6e_Quicksort.split_proviso@124d2f0d
  lean-calc(calc-split),
)]<sort-split>
// B&dM 6.6f, p.155, `split = ⦇[base,step]⦈·embed` on non-empty lists; the fold is below the
// specification `split ⊆ check'·join°·perm` when `base` and `step` meet the two fusion conditions.
#import "../generated/Freyd.Alg.RelSet.Sort.split_cata.calc.typ" as calc-split-cata
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.split_cata") \
    #src[turning a list into a non-empty list and folding it with any `[bs, st]` meeting the two conditions below gives only
     `check`ed triples `(x,a,y)` whose join `x ⧺ [a] ⧺ y` is a permutation of the list]],
     // lean:AOP.A6_6e_Quicksort.split_cata@6dc148a1
  lean-calc(calc-split-cata),
)]<split-cata>

// B&dM p.155, the first fusion condition, with `base(a) = ([],a,[])`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.split_base") \
    #src[`base(a)` is a `check`ed triple whose join is a permutation of the one-element list `[a]`]],
     // lean:AOP.A6_6e_Quicksort.split_base@5518d1ff
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.split_base.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Sort.split_base.rhs", src[`[] ⧺ [a] ⧺ [] = [a]`, and `check'` holds on empty lists]),
  ),
)]<split-base>

// B&dM p.155, the second fusion condition, with `step(a,(x,b,y)) = ([a]⧺x,b,y)` if `aRb`, otherwise
// `(x,b,[a]⧺y)`; `R` connected.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.split_step") \
    #src[if `(x,b,y)` is a `check`ed triple for a permutation of `l`, then `step(a,(x,b,y))` is a
     `check`ed triple for a permutation of `[a] ⧺ l`]],
     // lean:AOP.A6_6e_Quicksort.split_step@b7a3c037
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.split_step.lhs", []),
    (SQ, "Freyd.Alg.RelSet.Sort.split_step.rhs", src[`aRb` puts `a` in front of `x`; otherwise `bRa` and `a` goes in front of `y`]),
  ),
)]<split-step>
// B&dM 6.6f, p.155, the program: by the hylomorphism theorem `X=⦇[nil,split°]⦈°flatten` solves the
// equation, and is its least solution (lean:AOP.A6_6e_Quicksort.qsort_least@3e9893c3).
#import "../generated/Freyd.Alg.RelSet.Sort.qsort_rec.calc.typ" as calc-qsort-rec
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.qsort_rec") \
    #src[quicksort returns `[]` on `[]`, and otherwise splits into `(x,a,y)`, sorts `x` and `y` and
     joins them around `a`]],
     // lean:AOP.A6_6e_Quicksort.qsort_rec@acd4b32a
  lean-calc(calc-qsort-rec),
)]<qsort-rec>
// B&dM p.157 (Ex 6.30): insertion sort, from `perm = ⦇[nil,add]⦈` (§5.6) with `add` putting an
// element anywhere in a list (lean:AOP.A6_6c_ISort.add@88935b2b).
#import "../generated/Freyd.Alg.RelSet.ISort.insertion_sort.calc.typ" as calc-isort
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.ISort.insertion_sort") \
    #src[for any `ins` that, on an ordered list, returns only ordered results of `add`, folding
     with `[nil, ins]` gives only sorted permutations]],
     // lean:AOP.A6_6c_ISort.insertion_sort@3dcc9fbb
  lean-calc(calc-isort),
)]<isort-ex630>

// B&dM p.157 (Ex 6.30), the `insert` asked for: slide `a` past every element it is not below.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.ISort.insert_add") \
    #src[inserting `a` into an ordered list puts `a` somewhere in it and keeps it ordered]],
     // lean:AOP.A6_6c_ISort.insert_add@95dfc136
  lean-chain(
    (none, "Freyd.Alg.RelSet.ISort.insert_add.lhs", []),
    (SQ, "Freyd.Alg.RelSet.ISort.insert_add.rhs", src[`insert` splices `a` in, and `R` transitive and connected]),
  ),
)]<isort-insert>

== Closure

// B&dM (6.7) (6.8), p.157.  Mirrored: the book's `(μX : 𝟙 ∪ X·R)` is `(μX : 𝟙 ∪ RX)` here, and the
// Lean `star` is defined by it; (6.8) is the other side.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_eq_mu'") \
    #src[closing `R` by composing it on the left and closing it by composing on the right give the
     same relation `R*`]],
     // lean:AOP.A6_7.star_eq_mu'@42cc4c0c lean:AOP.A6_7.star@a8a6944f
)]<closure-star>

// B&dM §6.7, p.157: the universal property, a statement with no chain of its own — it is the
// next four displays put together.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_UP") \
    #src[`X` contains `R` exactly when it contains `R*`]],
     // lean:AOP.A6_7.star_UP@96ea823a
)]<closure-up>

// B&dM 6.7a, p.158: `S=(μX : 𝟙∪RX)` is reflexive.
#import "../generated/Freyd.Alg.id_le_star.calc.typ" as calc-67a
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.id_le_star") \
    #src[`R*` is reflexive]],
     // lean:AOP.A6_7.id_le_star@90d24167
  lean-calc(calc-67a, pictures: false),
)]<closure-refl>

// B&dM 6.7b, p.158: `S` contains `R`.
#import "../generated/Freyd.Alg.le_star.calc.typ" as calc-67b
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.le_star") \
    #src[`R*` contains `R`]],
     // lean:AOP.A6_7.le_star@3ecb72e1
  lean-calc(calc-67b, pictures: false),
)]<closure-contains>

// B&dM 6.7c, p.158.  The book's `SS⊑S ≡ S⊑S\S ⇐ 𝟙∪R(S\S)⊑S\S ≡ S(𝟙∪R(S\S))⊑S`: the first two
// equivalences are division and least fixed point, and the chain is the inequality they reduce to,
// mirrored (the book's `S\S` is `S/S` here).
#import "../generated/Freyd.Alg.star_div_prefixed.calc.typ" as calc-star-trans
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_div_prefixed") \
    #src[`R*/R*` is a prefixed point of `X ↦ 𝟙∪RX`, stated through division] \
    #leanf("Freyd.Alg.star_trans") \
    #src[`R*` is transitive, because `R*/R*` is a prefixed point of `X ↦ 𝟙∪RX`]],
     // lean:AOP.A6_7.star_div_prefixed@54036308
     // lean:AOP.A6_7.star_trans@2a716981
  lean-calc(calc-star-trans, pictures: false),
)]<closure-trans>

// B&dM 6.7d, p.158: `S` is the least preorder containing `R`.
#import "../generated/Freyd.Alg.preorder_prefixed.calc.typ" as calc-star-least
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.preorder_prefixed") \
    #src[a reflexive transitive `X` containing `R` is a prefixed point of `Y ↦ 𝟙∪RY`] \
    #leanf("Freyd.Alg.star_le_of_preorder") \
    #src[a reflexive transitive `X` containing `R` is a prefixed point of `X ↦ 𝟙∪RX`, so it
     contains `R*`]],
     // lean:AOP.A6_7.preorder_prefixed@f685d4a1
     // lean:AOP.A6_7.star_le_of_preorder@a62fa34b
  lean-calc(calc-star-least, pictures: false),
)]<closure-least>

// B&dM p.158: the `tails` recursion, `R` being `tail`.
#import "../generated/Freyd.Alg.Λ_star.calc.typ" as calc-tails
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.Λ_star") \
    #src[the set of `R*`-successors of `a` is `a` itself joined with the `R*`-successors of its
     `R`-successors]],
     // lean:AOP.A6_7.Λ_star@f11f82f1
  lean-calc(calc-tails),
)]<closure-tails>

// B&dM 6.7e, p.159: the subtraction laws, chapter 4's (`AOP.A4_5`), each a statement row.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.sub_zero") \ #src[taking nothing away leaves `R`]],
     // lean:AOP.A4_5.sub_zero@2c6ece15
  Thm(cols: 1)[#leanf("Freyd.Alg.union_sub_absorb") \
    #src[beside `R`, only the part of `S` outside `R` adds anything]],
     // lean:AOP.A4_5.union_sub_absorb@00bbf8e8
  Thm(cols: 1)[#leanf("Freyd.Alg.sub_union") \
    #src[taking away `S` and then `T` takes away `S∪T`]],
     // lean:AOP.A4_5.sub_union@b387b972
  Thm(cols: 1)[#leanf("Freyd.Alg.union_sub_distrib") \
    #src[taking `T` away from a union takes it away from each part]],
     // lean:AOP.A4_5.union_sub_distrib@54092403
)]<closure-sub>

// B&dM 6.7f, p.159 (Ex 6.35): the rolling rule.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.mu_rolling") \
    #src[the least fixed point of `φ` after `ψ` is `φ` applied to the least fixed point of `ψ` after
     `φ`]],
     // lean:AOP.A6_2.mu_rolling@c705ef5a
)]<closure-rolling>

// B&dM 6.7g, p.160 and Ex 6.32: `SR*` and `R*S` as least fixed points, mirrored.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.comp_star_eq_mu") \
    #src[`S` followed by any number of `R` steps is the least `X` containing `S` and closed under a
     further `R` step]],
     // lean:AOP.A6_7.comp_star_eq_mu@2bbfa45b
  Thm(cols: 1)[#leanf("Freyd.Alg.star_comp_eq_mu") \
    #src[any number of `R` steps followed by `S` is the least `X` containing `S` and closed under an
     `R` step in front]],
     // lean:AOP.A6_7.star_comp_eq_mu@537dc253
)]<closure-comp>

// B&dM (6.9), p.160: `θ(P,Q) ≜ P ∪ (μX : Q ∪ (XR − P))`, mirrored; `θ(𝟘,S)=SR*` is why it is defined.
#import "../generated/Freyd.Alg.theta_zero_left.calc.typ" as calc-theta-l
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.theta_zero_left") \
    #src[started with nothing found and `S` to explore, `θ` computes `SR*`]],
     // lean:AOP.A6_7.theta_zero_left@b8297d35 lean:AOP.A6_7.theta@494eeaa5
  lean-calc(calc-theta-l, pictures: false),
)]<closure-theta-zero-left>

// B&dM 6.7h, p.160: `θ(P,𝟘)=P`, the recursion's exit.
#import "../generated/Freyd.Alg.theta_zero_right.calc.typ" as calc-theta-r
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.theta_zero_right") \
    #src[with nothing left to explore, `θ` returns what it has found]],
     // lean:AOP.A6_7.theta_zero_right@14a43ab2
  lean-calc(calc-theta-r, pictures: false),
)]<closure-theta-zero-right>

// TODO p.161 close: `E(R*)(s)=close(∅,s)`, `close(p,∅)=p`, `close(p,q)=close(p∪q, E(R)(q)−p−q)` by `Λ`
//   (3 steps) — Lean missing.
