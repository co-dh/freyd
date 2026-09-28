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

// B&dM (6.1), p.138.  The book derives `val°` for `val=⦇[embed,op]⦈`; the chain is stated for any
// algebra `[g,h]`, and `val_converse_eq` is it at `g≜embed`, `h≜op`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Digits.val_converse_eq") \
    #src[a number is read back into digits either as one nonzero digit, or by splitting off its
     last digit and reading back the rest]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.val_converse_eq@464083fc
  // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_eq@83b05a50
  lean-chain(
    (none, "Freyd.Alg.RelSet.Digits.cata_converse_step1.lhs", src[`val=⦇[embed,op]⦈` — definition]),
    (EQ, "Freyd.Alg.RelSet.Digits.cata_converse_step1.rhs", src[`⦇φ⦈=α°F(⦇φ⦈)φ` — catamorphisms]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step1@f212a141
    (EQ, "Freyd.Alg.RelSet.Digits.cata_converse_step2.rhs", src[`(RS)°=S°R°` — converse]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step2@54cfab45
    (EQ, "Freyd.Alg.RelSet.Digits.cata_converse_step3.rhs", src[`F(R)=𝟙+(R×𝟙)` — definition of `F`]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step3@55fc19d6
    (EQ, "Freyd.Alg.RelSet.Digits.cata_converse_step4.rhs", src[`α=[wrap,snoc]`]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step4@f1315001
    (EQ, "Freyd.Alg.RelSet.Digits.cata_converse_step5.rhs", src[`(R+S)[P,Q]=[RP,SQ]` — coproduct]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step5@a1d4f22f
    (EQ, "Freyd.Alg.RelSet.Digits.cata_converse_step6.rhs", src[`[g,h]°[P,Q]=g°P∪h°Q` — coproduct]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step6@6b76c614
  ),
)]<val-converse>
// B&dM p.139: `op(n,d)=10n+d` read backwards, and where `op°` and `embed°` are defined — which is what
// turns the join of (6.1) into a conditional.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  [#leanf("Freyd.Alg.RelSet.Digits.op_recip_iff") \
    #src[`op°` splits a number into its quotient and remainder by 10]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.op_recip_iff@2686cd29
  [#leanf("Freyd.Alg.RelSet.Digits.op_recip_defined") \
    #src[`op°` gives a pair with a nonzero first component exactly at the numbers with two or more digits]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.op_recip_defined@e2b3eb5f
  [#leanf("Freyd.Alg.RelSet.Digits.embed_recip_defined") \
    #src[`embed°` gives a digit exactly at the one-digit numbers]],
  // lean:AOP.A6_1_Digits.RelSet.Digits.embed_recip_defined@65abb14c
)]<op-recip>
// TODO p.139 digits: the join is a conditional; `val°` the unique solution, total; `digits=val°`.

== Least fixed points <sec-mu>

// B&dM Theorem 6.1, p. 140.  `μ` is read off a whole chapter of specifications from §@sec-dp on,
// and nothing before this said what it was.
#disp[#definition[
`φ` a *monotonic* mapping of the hom-set `A⟶B` into itself: #h(4pt) `X⊑Y⟹φ(X)⊑φ(Y)`
#src[].
// lean:AOP.A6_2.Monotonic@66dddf1e

`(μX : φ(X))` the least `X : A⟶B` with #h(4pt) `φ(X)⊑X` #src[].
// lean:AOP.A6_2.mu@4928a490
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
 // lean:AOP.A6_2.mu_le@9918bd39
 // lean:AOP.A6_2.mu_fixed@2d3d1a8a
)]<mu-laws>

// B&dM Theorem 6.1, p.140 — drawn at @mu-laws; not redrawn.
#src[Theorem 6.1 (Knaster–Tarski) is @mu-laws.]
// lean:AOP.A6_2.mu_fixed@2d3d1a8a

// B&dM (6.2), p.141: `⦇R⦈` is `(μX : α°F(X)R)`, so Theorem 6.1's leastness bounds it by any prefix point.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.relCata_le_of_prefixed") \
    #src[a relation `X` that contains one unfolding of the fold's recursion at `X` contains the fold]],
  // lean:AOP.A6_2.relCata_le_of_prefixed@837a5bf7
  lean-chain(
    (none, "Freyd.Alg.relCata_eq_mu.lhs", []),
    (EQ, "Freyd.Alg.relCata_eq_mu.rhs", src[`⦇R⦈` the least fixed point — Theorem 6.1, @mu-laws]),
    // lean:AOP.A6_2.relCata_eq_mu@c2d55908
    (SQ, "Freyd.Alg.relCata_le_of_prefixed#h.rhs", src[`α°F(X)R⊑X`, `μ` below every prefix point]),
  ),
)]<cata-prefix>

// B&dM (6.3), p.141: `⦇R⦈` is also the greatest fixed point `(νX : α°F(X)R)`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.le_relCata_of_postfixed") \
    #src[a relation `X` contained in one unfolding of the fold's recursion at `X` is contained in the fold]],
  // lean:AOP.A6_2.le_relCata_of_postfixed@6d0c3236
  lean-chain(
    (none, "Freyd.Alg.le_relCata_of_postfixed#h.lhs", []),
    (SQ, "Freyd.Alg.relCata_eq_nu.rhs", src[`X⊑α°F(X)R`, `ν` above every postfix point]),
    (EQ, "Freyd.Alg.relCata_eq_nu.lhs", src[`⦇R⦈` the greatest fixed point]),
    // lean:AOP.A6_2.relCata_eq_nu@0af949db
  ),
)]<cata-postfix>

// B&dM (6.4), p.141, "easy exercise" (Ex 6.6): (6.2) at `X≜⦇R⦈S`, whose prefix-point condition is
// this chain.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.relCata_le_comp") \
    #src[if `S` followed by `R` absorbs `T` after `F(S)`, the fold of `T` is below the fold of `R`
     followed by `S`]],
  // lean:AOP.A6_2.relCata_le_comp@b54d0a6b
  lean-chain(
    (none, "Freyd.Alg.relCata_le_comp_step1.lhs", src[(6.2) at `X≜⦇R⦈S`]),
    (EQ, "Freyd.Alg.relCata_le_comp_step1.rhs", src[`F(RS)=F(R)F(S)` — @relator-defn]),
    // lean:AOP.A6_2.relCata_le_comp_step1@2fbeae5c
    (SQ, "Freyd.Alg.relCata_le_comp_step2.rhs", src[`F(S)T⊑RS`]),
    // lean:AOP.A6_2.relCata_le_comp_step2@e2b7aeb0
    (EQ, "Freyd.Alg.relCata_le_comp_step3.rhs", src[`F(⦇R⦈)R=α⦇R⦈`, `α°α=𝟙` — @cata-defining]),
    // lean:AOP.A6_2.relCata_le_comp_step3@3ef0b9b8
  ),
)]<cata-fusion-le>

// B&dM (6.5), p.141: (6.3) at `X≜⦇R⦈S`; the chain of (6.4) read backwards, its hypothesis reversed.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.comp_le_relCata") \
    #src[if `R` followed by `S` is absorbed by `F(S)` followed by `T`, the fold of `R` followed by `S`
     is below the fold of `T`]],
  // lean:AOP.A6_2.comp_le_relCata@5874cf45
  lean-chain(
    (none, "Freyd.Alg.relCata_le_comp_step3.rhs", src[(6.3) at `X≜⦇R⦈S`]),
    (EQ, "Freyd.Alg.relCata_le_comp_step3.lhs", src[`α⦇R⦈=F(⦇R⦈)R`, `α°α=𝟙` — @cata-defining]),
    (SQ, "Freyd.Alg.comp_le_relCata_step2.rhs", src[`RS⊑F(S)T`]),
    // lean:AOP.A6_2.comp_le_relCata_step2@adb9a462
    (EQ, "Freyd.Alg.relCata_le_comp_step1.lhs", src[`F(R)F(S)=F(RS)` — @relator-defn]),
  ),
)]<fusion-le-cata>

== Hylomorphisms <sec-hylo>

// §@sec-hylo's panels, emitted by `./scripts/diagram --sigs … --src … --tgt … "<formula>"` plus
// `s: 100%`.  `sigs:` types the section's abstract letters; `frame: 5` is the ONE box every panel
// of the section draws in, so a step's two panels line up under `trow`'s `align: horizon`, and
// `top: 3` drops a lone bead to the height of the bead it stands against.
// 11.6.4a/b are sub theorems of the fixed-point equation below, so all three rows of Theorem 6.2
// share ONE table, headed by the fixed-point statement.  hylo_le_of_prefixed is a term chain ending
// in its hypothesis, then two statement rows (adjunction, fold leastness), each a pair step: one
// `lean(l, r)` call apiece so its two sides are one height.

// B&dM p. 142, mirrored into diagram order.  The `F` wire is born at the leading converse and dies
// at the trailing algebra; every step shortens it, and by the last panel it is gone.  B&dM p. 143,
// mirrored: two adjunction steps carry `⦇S⦈°` out of the way and back, the reduce's own leastness
// fires between them, and the `F` wire's top end walks from `α°` up to `S°`.  Theorem 6.2's two
// inclusions are these two rows: one `⊑` is hylo_fixed
// through @mu-laws, the other hylo_le_of_prefixed at the prefix point `μ`.
#disp[#calc-table(cols: (1fr,), al: auto,
  // hylo-fusion-eq header: Theorem 6.2, whose two inclusions are the Sub rows a and b
  // lean:AOP.A6_3.hylo_eq_mu@5da9c8e8
  Thm(cols: 1)[#leanf("Freyd.Alg.hylo_eq_mu") \
    #src[hylomorphism theorem: a hylomorphism is the least fixed point of a certain recursion equation]],
  [#lean-chain(
    Sub("Freyd.Alg.hylo_fixed",
      gloss: src[hylomorphism theorem: a prototypical 'divide and conquer' scheme — the term `S°` represents the
        decomposition stage, `F(⦇S⦈°⦇R⦈)` the stage of solving the subproblems recursively, and `R` the
        recombination stage; `R : FA⟶A`, `S : FB⟶B`, `α : FT⟶T` initial],
      // lean:AOP.A6_3.hylo_fixed@67ca7394
      (none, "Freyd.Alg.hylo_fixed_step1.lhs", src[the body at `⦇S⦈°⦇R⦈`]),
      (EQ, "Freyd.Alg.hylo_fixed_step1.rhs", src[`F(RS)=F(R)F(S)` — @relator-defn]),
      (EQ, "Freyd.Alg.hylo_fixed_step2.rhs", src[`F(⦇R⦈)R=α⦇R⦈` — @cata-defining]),
      (EQ, "Freyd.Alg.hylo_fixed_step3.rhs", src[`⦇S⦈°α°=S°F(⦇S⦈°)` — @cata-defining, @relator-laws]),
      (EQ, "Freyd.Alg.hylo_fixed_step4.rhs", src[`α` iso]),
      // lean:AOP.A5_5.InitialAlgebra.recip_alpha_alpha@5dcef861
    ),
  )],
  [#lean-chain(
    Sub("Freyd.Alg.hylo_le_of_prefixed",
      gloss: src[hylomorphism theorem: by Knaster–Tarski, the hylomorphism `⦇S⦈°⦇R⦈` is included in `X` if `X`
        satisfies the associated recursion inequation],
      (none, "Freyd.Alg.hylo_le_of_prefixed_step1.lhs", src[`Y:=⦇S⦈°\X`]),
      (EQ, "Freyd.Alg.hylo_le_of_prefixed_step1.rhs", src[`⦇S⦈°α°=S°F(⦇S⦈°)`]),
      (EQ, "Freyd.Alg.hylo_le_of_prefixed_step2.rhs", src[`F(RS)=F(R)F(S)` — @relator-defn]),
      (SQ, "Freyd.Alg.hylo_le_of_prefixed_step3.rhs", src[`⦇S⦈°(⦇S⦈°\X)⊑X` — @adj-all]),
      (SQ, "Freyd.Alg.hylo_le_of_prefixed#h.rhs", src[`S°F(X)R⊑X`]),
    ),
    (
      (IFF, ("Freyd.Alg.hylo_le_of_prefixed_prefix",),
        src[`S·⊣S\` — @adj-all]),
      (IMP, ("Freyd.Alg.hylo_le_of_prefixed_fold",),
        src[`⦇R⦈=(μX : α°F(X)R)` — @cata-defining, @mu-laws, @adj-all]),
      // lean:AOP.A6_2.relCata_le_of_prefixed@837a5bf7
    ),
  )],
)]<hylo-mu>

// B&dM Theorem 6.2, p.142 — drawn at §@sec-hylo; not redrawn.
#src[Theorem 6.2 is §@sec-hylo.]
// lean:AOP.A6_3.hylo_eq_mu@5da9c8e8

// B&dM Corollary 6.1, p.143: Theorem 6.2 at `R≜[R₁,R₂]`, `S≜[S₁,S₂]` over `F(X)=G(X)+H(X)`; the chain
// is the body under the `μ`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.hylo_eq_mu_coprod") \
    #src[when both algebras are case splits over the same sum, the recursion runs each case on its
     own and unites the results]],
  // lean:AOP.A6_3.hylo_eq_mu_coprod@066877fe
  lean-chain(
    (none, "Freyd.Alg.hylo_body_coprod_step1.lhs", src[the body of Theorem 6.2 at `F(X)=G(X)+H(X)`]),
    (EQ, "Freyd.Alg.hylo_body_coprod_step1.rhs", src[`(P+Q)[R₁,R₂]=[PR₁,QR₂]` — coproduct]),
    // lean:AOP.A6_3.hylo_body_coprod_step1@2ca7d056
    (EQ, "Freyd.Alg.hylo_body_coprod_step2.rhs", src[`[S₁,S₂]°[P,Q]=S₁°P∪S₂°Q` — coproduct]),
    // lean:AOP.A6_3.hylo_body_coprod_step2@00f0c2d0
  ),
)]<hylo-coprod>

== Fast exponentiation and modulus computation

// B&dM p.144–145: the argument for `exp(a)`, stated once for a map `f` and an algebra `[g,h]` with the
// fusion conditions `zero f=g`, `shift f=(f×𝟙)h`; `exp` and `mod` are it at `[one,op(a)]`, `[zero,op(b)]`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.FastExp.convert_program") \
    #src[once `f` sends `zero` to `g` and turns `shift` into `h`, the recursion that halves the
     argument at each step computes `f`]],
  // lean:AOP.A6_4_FastExp.RelSet.FastExp.convert_program@9f928e8d
  lean-chain(
    (none, "Freyd.Alg.RelSet.FastExp.convert_step1.rhs", []),
    (RQ, "Freyd.Alg.RelSet.FastExp.convert_step1.lhs", src[`convert` simple]),
    // lean:AOP.A6_4_FastExp.RelSet.FastExp.convert_step1@69eb83de
    // lean:AOP.A6_4_FastExp.RelSet.FastExp.convert_simple@bb3512f8
    (EQ, "Freyd.Alg.RelSet.FastExp.convert_step2.rhs", src[fusion: `zero f=g`, `shift f=(f×𝟙)h`]),
    // lean:AOP.A6_4_FastExp.RelSet.FastExp.convert_step2@74323421
    // lean:AOP.A6_4_FastExp.RelSet.FastExp.convert_fusion@4f54bb8d
    (EQ, "Freyd.Alg.RelSet.FastExp.convert_step3.rhs", src[Corollary 6.1, @hylo-coprod]),
    // lean:AOP.A6_4_FastExp.RelSet.FastExp.convert_step3@e3126154
  ),
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
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.inductive_of_comp_le") \
    #src[`R` is inductive when `RR⊑SR` for an inductive `S`]],
    // lean:AOP.A6_5.inductive_of_comp_le@17eb3b43
  lean-chain(
    (none, "Freyd.Alg.inductive_of_comp_le_step1.lhs", []),
    (SQ, "Freyd.Alg.inductive_of_comp_le_step1.rhs", src[`RR⊑SR`]),
    // lean:AOP.A6_5.inductive_of_comp_le_step1@541f5e6c
    (SQ, "Freyd.Alg.inductive_of_comp_le_step2.rhs", src[division by `S`]),
    // lean:AOP.A6_5.inductive_of_comp_le_step2@de8b5c71
    (SQ, "Freyd.Alg.inductive_of_comp_le_step3.rhs", src[division by `R`]),
    // lean:AOP.A6_5.inductive_of_comp_le_step3@6567f943
  ),
)]<inductive-comp-le>
// TODO p.148 member: `member(id)=𝟙`, `member(FG)=member(F)member(G)`, `member(P)=∈`,
//   `member(T)=setify(T)∈` — Lean idMembership, compMembership; `P`, `T` missing.
// B&dM p.148, the constant, sum and product rows
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.member_const") \
    #src[a constant relator records no elements, so its membership is empty]],
    // lean:AOP.A6_5.member_const@91d83a84
  lean-chain(
    (none, "Freyd.Alg.member_const.lhs", []),
    (EQ, "Freyd.Alg.member_const.rhs", []),
  ),
  Thm(cols: 1)[#leanf("Freyd.Alg.member_sum") \
    #src[a member of `F+G` is a member of whichever summand the value is in]],
    // lean:AOP.A6_5.member_sum@f2ed47bd
  lean-chain(
    (none, "Freyd.Alg.member_sum.lhs", []),
    (EQ, "Freyd.Alg.member_sum.rhs", []),
  ),
  Thm(cols: 1)[#leanf("Freyd.Alg.member_prod") \
    #src[a member of `F×G` is a member of either component]],
    // lean:AOP.A6_5.member_prod@fefd83ec
  lean-chain(
    (none, "Freyd.Alg.member_prod.lhs", []),
    (EQ, "Freyd.Alg.member_prod.rhs", []),
  ),
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
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.cor62") \
    #src[when `g member` is inductive and `f`, `g` are maps, the solution of `X=gF(X)f` is a map]],
    // lean:AOP.A6_5.cor62@6df24a22
  lean-chain(
    (none, "Freyd.Alg.cor62_step1.lhs", []),
    (SQ, "Freyd.Alg.cor62_step1.rhs", src[`X=gF(X)f`, `g` simple]),
    // lean:AOP.A6_5.cor62_step1@71864db7
    (SQ, "Freyd.Alg.cor62_step2.rhs", src[`Y°X⊑𝟙`]),
    // lean:AOP.A6_5.cor62_step2@e7d4ea15
    (SQ, "Freyd.Alg.cor62_step3.rhs", src[`f` simple]),
    // lean:AOP.A6_5.cor62_step3@fca728a4
  ),
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
    // lean:AOP.A6_5.thm64@296aa783
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
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thm64_claim") \
    #src[`R°member` is below `α°member` conjugated by `f`, so it is inductive when `α°member` is]],
    // lean:AOP.A6_5.thm64_claim@4b02dea3
  lean-chain(
    (none, "Freyd.Alg.thm64_claim_step1.lhs", []),
    (SQ, "Freyd.Alg.thm64_claim_step1.rhs", src[`Rf⊑F(f)α`, shunting]),
    // lean:AOP.A6_5.thm64_claim_step1@b4925181
    (SQ, "Freyd.Alg.thm64_claim_step2.rhs", src[`member` lax natural]),
    // lean:AOP.A6_5.thm64_claim_step2@3e9c7464
  ),
)]<thm64-claim>

== Sorting by selection

// B&dM (6.6), p.151.  `ok(a,x) ≡ ∀b∈x. aRb`; the preorder `R` is fixed, so `ordered` and `ok`
// carry no argument.
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
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.selection_sort") \
    #src[every output of unfolding the input by `select` is a sorted permutation of it]],
     // lean:AOP.A6_6b_SortConcrete.selection_sort@617e20db
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.selection_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.selection_step1.rhs", src[`perm°=perm`, `ordered°=ordered`]),
     // lean:AOP.A6_6b_SortConcrete.selection_step1@b0c2bf70
    (EQ, "Freyd.Alg.RelSet.Sort.selection_step2.rhs", src[@sort-ordered]),
     // lean:AOP.A6_6b_SortConcrete.selection_step2@efecdea7
    (RQ, "Freyd.Alg.RelSet.Sort.selection_step3.lhs", src[fusion (6.4) under @sort-select]),
     // lean:AOP.A6_6b_SortConcrete.selection_step3@2c3b5167
  ),
)]<sort-selection>

// B&dM 6.6b, p.153, the fusion proviso; `select` is specified by `select°⊑ok cons perm`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.select_proviso") \
    #src[permuting the tail and then undoing `select` lands among the `ok` conses of a permutation]],
     // lean:AOP.A6_6b_SortConcrete.select_proviso@924131a0
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.select_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.select_step1.rhs", src[`cons perm=(𝟙×perm)cons perm`]),
     // lean:AOP.A6_6b_SortConcrete.select_step1@7ab18cc3
    (EQ, "Freyd.Alg.RelSet.Sort.select_step2.rhs", src[Ex 6.22, `ok(𝟙×perm)=(𝟙×perm)ok`]),
     // lean:AOP.A6_6b_SortConcrete.select_step2@64cbd9c8
    (RQ, "Freyd.Alg.RelSet.Sort.select_step3.lhs", src[`select°⊑ok cons perm`]),
     // lean:AOP.A6_6b_SortConcrete.select_step3@b7940931
  ),
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
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.quicksort") \
    #src[every output of unfolding the input by `split` into a tree and flattening that tree is a
     sorted permutation of the input]],
     // lean:AOP.A6_6e_Quicksort.quicksort@2ff8cd0e
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.qsort_step1.rhs", []),
    (RQ, "Freyd.Alg.RelSet.Sort.qsort_step1.lhs", src[`flatten` is simple]),
     // lean:AOP.A6_6e_Quicksort.qsort_step1@f0b72a2c
    (EQ, "Freyd.Alg.RelSet.Sort.qsort_step2.rhs", src[`flatten ordered=inordered flatten`]),
     // lean:AOP.A6_6e_Quicksort.qsort_step2@ed8f63c8
    (EQ, "Freyd.Alg.RelSet.Sort.qsort_step3.rhs", src[converses]),
     // lean:AOP.A6_6e_Quicksort.qsort_step3@35ed5007
    (RQ, "Freyd.Alg.RelSet.Sort.qsort_step4.lhs", src[fusion (6.4) under @sort-split]),
     // lean:AOP.A6_6e_Quicksort.qsort_step4@a3fb7ac7
  ),
)]<sort-quick>

// B&dM 6.6e, p.155, the fusion proviso; `split` is specified by `split°⊑check' join perm`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.split_proviso") \
    #src[undoing `split` and then flattening and permuting both parts lands among the `check`ed
     forks whose flattening is permuted]],
     // lean:AOP.A6_6e_Quicksort.split_proviso@124d2f0d
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.split_step1.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.split_step1.rhs", src[`fork flatten=F(flatten)join`]),
     // lean:AOP.A6_6e_Quicksort.split_step1@06a641a0
    (EQ, "Freyd.Alg.RelSet.Sort.split_step2.rhs", src[`check F(flatten)=F(flatten)check'`]),
     // lean:AOP.A6_6e_Quicksort.split_step2@023773b1
    (EQ, "Freyd.Alg.RelSet.Sort.split_step3.rhs", src[`join perm=F(perm)join perm`, `check' F(perm)=F(perm)check'`]),
     // lean:AOP.A6_6e_Quicksort.split_step3@d865bdf1
    (EQ, "Freyd.Alg.RelSet.Sort.split_step4.rhs", src[functors]),
     // lean:AOP.A6_6e_Quicksort.split_step4@a36f98a6
    (RQ, "Freyd.Alg.RelSet.Sort.split_step5.lhs", src[`split°⊑check' join perm`]),
     // lean:AOP.A6_6e_Quicksort.split_step5@94aed1e9
  ),
)]<sort-split>
// TODO p.155 split-cata: `split = embed ⦇[base,step]⦈` with `base ⊆ wrap perm join°check'`,
//   `(𝟙×join check')step ⊆ cons perm join°check'`.
// B&dM 6.6f, p.155, the program: by the hylomorphism theorem `X=⦇[nil,split°]⦈°flatten` solves the
// equation, and is its least solution (lean:AOP.A6_6e_Quicksort.qsort_least@3e9893c3).
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.RelSet.Sort.qsort_rec") \
    #src[quicksort returns `[]` on `[]`, and otherwise splits into `(x,a,y)`, sorts `x` and `y` and
     joins them around `a`]],
     // lean:AOP.A6_6e_Quicksort.qsort_rec@6776e923
  lean-chain(
    (none, "Freyd.Alg.RelSet.Sort.qsort_rec.lhs", []),
    (EQ, "Freyd.Alg.RelSet.Sort.qrec_step1.lhs", src[hylomorphism theorem]),
    (EQ, "Freyd.Alg.RelSet.Sort.qrec_step1.rhs", src[`F(X)[nil,join]=[nil,(X×𝟙×X)join]`]),
     // lean:AOP.A6_6e_Quicksort.qrec_step1@8fce50a6
    (EQ, "Freyd.Alg.RelSet.Sort.qrec_step2.rhs", src[coproduct]),
     // lean:AOP.A6_6e_Quicksort.qrec_step2@4ee6ccce
  ),
)]<qsort-rec>
// TODO Ex 6.30 insertion: `perm ordered = ⦇[nil,add]⦈ordered = ⦇[nil,add ordered]⦈ ⊒ ⦇[nil,insert]⦈`
//   (3 steps) — Lean isort_emerges is concrete.

== Closure

// B&dM (6.7) (6.8), p.157.  Mirrored: the book's `(μX : 𝟙 ∪ X·R)` is `(μX : 𝟙 ∪ RX)` here, and the
// Lean `star` is defined by it; (6.8) is the other side.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_eq_mu'") \
    #src[closing `R` by composing it on the left and closing it by composing on the right give the
     same relation `R*`]],
     // lean:AOP.A6_7.star_eq_mu'@42cc4c0c lean:AOP.A6_7.star@a8a6944f
  lean-chain(
    (none, "Freyd.Alg.star_eq_mu'.lhs", []),
    (EQ, "Freyd.Alg.star_eq_mu'.rhs", src[(6.8), Ex 6.31]),
  ),
)]<closure-star>

// B&dM §6.7, p.157: the universal property, a statement with no chain of its own — it is the
// next four displays put together.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_UP") \
    #src[for a preorder `X`, `X` contains `R` exactly when it contains `R*`]],
     // lean:AOP.A6_7.star_UP@96ea823a
)]<closure-up>

// B&dM 6.7a, p.158: `S=(μX : 𝟙∪RX)` is reflexive.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.id_le_star") \
    #src[`R*` is reflexive]],
     // lean:AOP.A6_7.id_le_star@90d24167
  lean-chain(
    (none, "Freyd.Alg.id_le_star_step1.lhs", []),
    (SQ, "Freyd.Alg.id_le_star_step1.rhs", src[union]),
     // lean:AOP.A6_7.id_le_star_step1@c4b88c90
    (EQ, "Freyd.Alg.star_unfold.rhs", src[fixed point, Thm 6.1]),
     // lean:AOP.A6_7.star_unfold@97a800c3
  ),
)]<closure-refl>

// B&dM 6.7b, p.158: `S` contains `R`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.le_star") \
    #src[`R*` contains `R`]],
     // lean:AOP.A6_7.le_star@3ecb72e1
  lean-chain(
    (none, "Freyd.Alg.le_star_step1.lhs", []),
    (EQ, "Freyd.Alg.le_star_step1.rhs", src[identity]),
     // lean:AOP.A6_7.le_star_step1@ded98a89
    (SQ, "Freyd.Alg.le_star_step2.rhs", src[`𝟙⊑R*` — @closure-refl]),
     // lean:AOP.A6_7.le_star_step2@b6b96fe7
    (SQ, "Freyd.Alg.comp_star_le.rhs", src[fixed point]),
     // lean:AOP.A6_7.comp_star_le@b5af2336
  ),
)]<closure-contains>

// B&dM 6.7c, p.158.  The book's `SS⊑S ≡ S⊑S\S ⇐ 𝟙∪R(S\S)⊑S\S ≡ S(𝟙∪R(S\S))⊑S`: the first two
// equivalences are division and least fixed point, and the chain is the inequality they reduce to,
// mirrored (the book's `S\S` is `S/S` here).
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_trans") \
    #src[`R*` is transitive, because `R*/R*` is a prefixed point of `X ↦ 𝟙∪RX`]],
     // lean:AOP.A6_7.star_trans@2a716981
  lean-chain(
    (none, "Freyd.Alg.star_trans_step1.lhs", []),
    (EQ, "Freyd.Alg.star_trans_step1.rhs", src[composition distributes over `∪`]),
     // lean:AOP.A6_7.star_trans_step1@c574fb0e
    (SQ, "Freyd.Alg.star_trans_step2.rhs", src[`(S/S)S⊑S`]),
     // lean:AOP.A6_7.star_trans_step2@ac21f3be
    (SQ, "Freyd.Alg.star_trans_step3.rhs", src[`RR*⊑R*` — @closure-contains]),
     // lean:AOP.A6_7.star_trans_step3@525c9edd
  ),
)]<closure-trans>

// B&dM 6.7d, p.158: `S` is the least preorder containing `R`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_le_of_preorder") \
    #src[a reflexive transitive `X` containing `R` is a prefixed point of `X ↦ 𝟙∪RX`, so it
     contains `R*`]],
     // lean:AOP.A6_7.star_le_of_preorder@a62fa34b
  lean-chain(
    (none, "Freyd.Alg.star_le_of_preorder_step1.lhs", []),
    (SQ, "Freyd.Alg.star_le_of_preorder_step1.rhs", src[`𝟙⊑X`, `R⊑X`]),
     // lean:AOP.A6_7.star_le_of_preorder_step1@00030274
    (SQ, "Freyd.Alg.star_le_of_preorder_step2.rhs", src[`XX⊑X`]),
     // lean:AOP.A6_7.star_le_of_preorder_step2@28ad3644
  ),
)]<closure-least>

// B&dM p.158: `X=𝟙∪RX` has the one solution `R*` for an inductive `R` (the `if` half; `suffix` is
// the case `R=tail`).  The chain is the induction step `Z/R⊑Z` at `Z=R*⇨R*/X`, read through
// `le_impl_iff` and `le_div_iff` as `((Z/R)∩R*)X⊑R*`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_unique") \
    #src[when `R` admits induction, `R*` is the only `X` equal to `𝟙∪RX`]],
     // lean:AOP.A6_7.star_unique@bce1f49a
  lean-chain(
    (none, "Freyd.Alg.star_unique_step1.lhs", []),
    (EQ, "Freyd.Alg.star_unique_step1.rhs", src[`X=𝟙∪RX`]),
     // lean:AOP.A6_7.star_unique_step1@49cd5ad2
    (EQ, "Freyd.Alg.star_unique_step2.rhs", src[composition distributes over `∪`]),
     // lean:AOP.A6_7.star_unique_step2@0987abdb
    (SQ, "Freyd.Alg.star_unique_step3.rhs", src[`(Z/R)R⊑Z`, `R*R⊑R*`]),
     // lean:AOP.A6_7.star_unique_step3@c0934f90
    (SQ, "Freyd.Alg.star_unique_step4.rhs", src[`(R*⇨R*/X)∩R*⊑R*/X`]),
     // lean:AOP.A6_7.star_unique_step4@f979c4cb
  ),
)]<closure-unique>

// B&dM p.158: the `tails` recursion, `R` being `tail`.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.Λ_star") \
    #src[the set of `R*`-successors of `a` is `a` itself joined with the `R*`-successors of its
     `R`-successors]],
     // lean:AOP.A6_7.Λ_star@eb24385a
  lean-chain(
    (none, "Freyd.Alg.Λ_star_step1.lhs", []),
    (EQ, "Freyd.Alg.Λ_star_step1.rhs", src[`R*=𝟙∪RR*`]),
     // lean:AOP.A6_7.Λ_star_step1@3ed4ca2e
    (EQ, "Freyd.Alg.Λ_star.rhs", src[`Λ(R∪S)=⟨Λ(R),Λ(S)⟩cup`]),
     // lean:AOP.A5_6.Λ_union@632cc56a
  ),
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
  lean-chain(
    (none, "Freyd.Alg.mu_rolling.lhs", []),
    (EQ, "Freyd.Alg.mu_rolling.rhs", src[Ex 6.35]),
  ),
)]<closure-rolling>

// B&dM 6.7g, p.160 and Ex 6.32: `SR*` and `R*S` as least fixed points, mirrored.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.comp_star_eq_mu") \
    #src[`S` followed by any number of `R` steps is the least `X` containing `S` and closed under a
     further `R` step]],
     // lean:AOP.A6_7.comp_star_eq_mu@2bbfa45b
  lean-chain(
    (none, "Freyd.Alg.comp_star_eq_mu.lhs", []),
    (EQ, "Freyd.Alg.comp_star_eq_mu.rhs", src[p.160]),
  ),
  Thm(cols: 1)[#leanf("Freyd.Alg.star_comp_eq_mu") \
    #src[any number of `R` steps followed by `S` is the least `X` containing `S` and closed under an
     `R` step in front]],
     // lean:AOP.A6_7.star_comp_eq_mu@537dc253
  lean-chain(
    (none, "Freyd.Alg.star_comp_eq_mu.lhs", []),
    (EQ, "Freyd.Alg.star_comp_eq_mu.rhs", src[Ex 6.32]),
  ),
)]<closure-comp>

// B&dM (6.9), p.160: `θ(P,Q) ≜ P ∪ (μX : Q ∪ (XR − P))`, mirrored; `θ(𝟘,S)=SR*` is why it is defined.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.theta_zero_left") \
    #src[started with nothing found and `S` to explore, `θ` computes `SR*`]],
     // lean:AOP.A6_7.theta_zero_left@b8297d35 lean:AOP.A6_7.theta@494eeaa5
  lean-chain(
    (none, "Freyd.Alg.theta_zero_left_step1.lhs", []),
    (EQ, "Freyd.Alg.theta_zero_left_step1.rhs", src[definition of `θ`]),
     // lean:AOP.A6_7.theta_zero_left_step1@794d78de
    (EQ, "Freyd.Alg.theta_zero_left_step2.rhs", src[`R−𝟘=R` — @closure-sub]),
     // lean:AOP.A6_7.theta_zero_left_step2@3d29ce01
    (EQ, "Freyd.Alg.comp_star_eq_mu.lhs", src[@closure-comp]),
  ),
)]<closure-theta-zero-left>

// B&dM 6.7h, p.160: `θ(P,𝟘)=P`, the recursion's exit.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.theta_zero_right") \
    #src[with nothing left to explore, `θ` returns what it has found]],
     // lean:AOP.A6_7.theta_zero_right@14a43ab2
  lean-chain(
    (none, "Freyd.Alg.theta_zero_right_step1.lhs", []),
    (EQ, "Freyd.Alg.theta_zero_right_step1.rhs", src[definition of `θ`]),
     // lean:AOP.A6_7.theta_zero_right_step1@6c0c4172
    (EQ, "Freyd.Alg.theta_zero_right_step2.rhs", src[`𝟘` is a prefixed point: `𝟘R−P=𝟘`]),
     // lean:AOP.A6_7.theta_zero_right_step2@e32277dc
    (EQ, "Freyd.Alg.theta_zero_right.rhs", src[`P∪𝟘=P`]),
  ),
)]<closure-theta-zero-right>

// B&dM 6.7i, p.160: the recursion step, the book's five steps.
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.theta_step") \
    #src[one round moves `Q` into the found part and explores the new `R`-successors of `Q` that
     are in neither]],
     // lean:AOP.A6_7.theta_step@49b0c3c6
  lean-chain((
    (none, "Freyd.Alg.theta_step_step1.lhs", []),
    (EQ, "Freyd.Alg.theta_step_step1.rhs", src[definition of `θ`]),
     // lean:AOP.A6_7.theta_step_step1@8b77fe50
    (EQ, "Freyd.Alg.theta_step_step2.rhs", src[`Q∪S=Q∪(S−Q)` — @closure-sub]),
     // lean:AOP.A6_7.theta_step_step2@1ecc0428
    (EQ, "Freyd.Alg.theta_step_step3.rhs", src[rolling — @closure-rolling]),
     // lean:AOP.A6_7.theta_step_step3@db1322e0
  ), (
    (EQ, "Freyd.Alg.theta_step_step4.rhs", src[subtraction — @closure-sub]),
     // lean:AOP.A6_7.theta_step_step4@54c7a347
    (EQ, "Freyd.Alg.theta_step_step5.rhs", src[definition of `θ`]),
     // lean:AOP.A6_7.theta_step_step5@afe9da13
  )),
)]<closure-theta-step>

// TODO p.161 close: `E(R*)(s)=close(∅,s)`, `close(p,∅)=p`, `close(p,q)=close(p∪q, E(R)(q)−p−q)` by `Λ`
//   (3 steps) — Lean missing.
