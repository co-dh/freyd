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

== Least fixed points

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

== Hylomorphisms

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
// TODO p.147 inductive: `S` inductive ∧ `RR⊑SR` ⟹ `R` inductive (the division exercise, 3 steps);
//   `R⊑S` ⟹ `R` inductive; `S` inductive iff `S⁺` is — Lean AOP.A6_5.inductive_of_comp_le,
//   inductive_of_le, inductive_transClosure_iff.
// TODO p.148 member: `member(id)=𝟙`, `member(K)=𝟘`, `member(F+G)=[member(F),member(G)]`,
//   `member(F×G)=outl member(F) ∪ outr member(G)`, `member(FG)=member(F)member(G)`, `member(P)=∈`,
//   `member(T)=setify(T)∈` — Lean idMembership, compMembership; `+`, `×`, `P`, `T` missing.
// TODO p.148 lax: `F(R)member ⊑ member R`, the largest lax natural `F ⟶ id`, hence unique — Lean
//   LaxMembership.laxNatural, largestLax_unique.
// TODO p.148 member α°: `α°member(F)` inductive; examples `[zero,succ]°[𝟘,𝟙]=succ°`,
//   `[nil,cons]°[𝟘,outr]=cons°outr=tail` — Lean missing.
// TODO Thm 6.3: `S member(F)` inductive ⟹ `X=SF(X)R` has a unique solution, entire if `R`,`S` are —
//   a hypothesis in Lean (HyloUnique, HyloEntire); statement row only.
// TODO Cor 6.2: `g member(F)` inductive ⟹ the unique solution of `X=gF(X)f` is a function (2 steps).
// TODO Cor 6.3: `R°member(F)` inductive ⟹ `⦇R⦈` surjective if `R` is (2 steps).
// TODO Thm 6.4: `R` surjective ∧ `Rf⊑F(f)α` ⟹ `f°=⦇R⦈`; `⊑` by shunting, fusion, assumption (3);
//   `⊒` by the surjectivity claim and `⦇R⦈f⊑𝟙` (2); claim `R°member ⊑ R°member F(f°)α°f ⊑ f°member α°f`
//   (2) — Lean thm64 (forward/backward) takes the claim as the hypothesis `hcatasur`.

== Sorting by selection

// TODO (6.6): `sort ⊆ perm ordered`, `ordered=⦇[nil,ok cons]⦈`, `ok(a,x) ≡ ∀b∈x. aRb` — abstract def missing.
// TODO p.152 selection: `perm ordered = (ordered perm)° = (⦇[nil,ok cons]⦈perm)° ⊒ ⦇[nil,select°]⦈°`
//   (3 steps) — Lean AOP.A6_6_Sort.selection_sort_correct.
// TODO p.153 select: proviso `ok cons perm = ok (𝟙×perm)cons perm = (𝟙×perm)ok cons perm ⊒ (𝟙×perm)select°`
//   (3 steps; Ex 6.22 claim `ok (𝟙×perm) = (𝟙×perm) ok`) — pointwise only (hfus_concrete).
// TODO p.153 select-cata: `select = embed ⦇[base,step]⦈` with `base ⊆ wrap perm cons°ok`,
//   `(𝟙×cons°ok)step ⊆ cons perm cons°ok`; `base(a)=(a,[])`, `step`.
// TODO p.153 sort-rec: `X=⦇[nil,select°]⦈°` the unique solution of `X = nil°nil ∪ select(𝟙×X)cons`; the
//   program — Lean sort_recursion (unfold only).
// TODO p.154 quicksort: `perm ordered ⊒ perm flatten°flatten ordered = perm flatten°inordered flatten
//   = (inordered flatten perm)°flatten ⊒ ⦇[nil,split°]⦈°flatten` (4 steps + claim
//   `flatten ordered = inordered flatten`) — abstract Lean missing (qsort_emerges is concrete).
// TODO p.155 split-proviso: `check fork flatten perm = check F(flatten) join perm = F(flatten) check' join perm
//   = F(flatten)F(perm) check' join perm = F(flatten perm) check' join perm ⊒ F(flatten perm) split°`
//   (5 steps, 3 claims) — Lean missing.
// TODO p.155 split-cata: `split = embed ⦇[base,step]⦈` with `base ⊆ wrap perm join°check'`,
//   `(𝟙×join check')step ⊆ cons perm join°check'`.
// TODO p.155 qsort-rec: `X=⦇[nil,split°]⦈°flatten` the least solution of `X = nil°nil ∪ split(X×𝟙×X)join`;
//   the program.
// TODO Ex 6.30 insertion: `perm ordered = ⦇[nil,add]⦈ordered = ⦇[nil,add ordered]⦈ ⊒ ⦇[nil,insert]⦈`
//   (3 steps) — Lean isort_emerges is concrete.

== Closure

// TODO (6.7) (6.8): `R* = (μX : 𝟙 ∪ RX) = (μX : 𝟙 ∪ XR)`; UP `R⊑X ≡ R*⊑X` for preorders `X` — Lean
//   AOP.A6_7.star_eq_mu', star_UP.
// TODO p.158 preorder: `S=(μX : 𝟙∪RX)` is the least preorder containing `R`: `𝟙⊑S` (2), `R⊑S` (3),
//   `SS⊑S ≡ S⊑S\S ⇐ 𝟙∪R(S\S)⊑S\S ≡ S(𝟙∪R(S\S))⊑S ≡ S∪SR(S\S)⊑S ⇐ S∪RS⊑S ≡ true` (6), least (2) — Lean
//   id_le_star', le_star', star'_trans, star'_le_of_preorder.
// TODO p.158 suffix: `X=𝟙∪RX` unique iff `R` inductive; `suffix = 𝟙 ∪ tail suffix`;
//   `Λ(suffix) = ⟨τ, Λ(tail suffix)⟩cup`; the `tails` program — Lean missing.
// TODO p.159 subtraction: `R−𝟘=R`, `R∪S=R∪(S−R)`, `R−(S∪T)=R−S−T`, `(R∪S)−T=(R−T)∪(S−T)` — ch 4 laws
//   (A4_5.sub_zero, union_sub_absorb, sub_union, union_sub_distrib): cite.
// TODO p.159 rolling: `(μX : φ(ψ(X))) = φ(μX : ψ(φ(X)))` (2 steps) — Lean AOP.A6_2.mu_rolling.
// TODO p.160 R*S: `SR* = (μX : S ∪ XR)` (2 steps) — Lean AOP.A6_7.star_comp_eq_mu.
// TODO (6.9) θ: `θ(P,Q) ≜ P ∪ (μX : Q ∪ (XR − P))`; `θ(𝟘,S)=SR*`; `θ(P,𝟘)=P` (2);
//   `θ(P,Q)=θ(P∪Q, QR−P−Q)` (definition; subtraction; rolling; subtraction; definition) — Lean
//   theta_zero_left, theta_zero_right, theta_step.
// TODO p.161 close: `E(R*)(s)=close(∅,s)`, `close(p,∅)=p`, `close(p,q)=close(p∪q, E(R)(q)−p−q)` by `Λ`
//   (3 steps) — Lean missing.
