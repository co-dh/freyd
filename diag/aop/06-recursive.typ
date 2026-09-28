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

// TODO (6.1)+p.138 val°: `digits ⊆ val°`, `val=⦇[embed,op]⦈`; `val° = embed°wrap ∪ op°(val°×𝟙)snoc`
//   — 6 steps (definition; catamorphisms; converse; definition of F; coproduct; coproduct);
//   Lean AOP.A6_1_Digits.val_converse_eq, no step decls yet.
// TODO p.139 op°: `op(n,d)=m ≡ n=m div 10 ∧ d=m mod 10`; `op°` defined iff `m≥10`, `embed°` iff `m<10`
//   — a Lean lemma, not a picture.
// TODO p.139 digits: the join is a conditional; `val°` the unique solution, total; `digits=val°`.

== Least fixed points

// TODO Thm 6.1: Knaster–Tarski, `R=⋂{X∣φ(X)⊑X}`; `φ(R)⊑R` (3 steps), `R⊑φ(R)` (2 steps);
//   Lean AOP.A6_2.mu_fixed via mu_prefixed, mu_postfixed, mu_le; statement drawn at @mu-laws (ch 11).
// TODO (6.2) (6.3): `⦇R⦈⊑X ⇐ α°F(X)R⊑X`; `X⊑⦇R⦈ ⇐ X⊑α°F(X)R` — Lean relCata_le_of_prefixed,
//   le_relCata_of_postfixed.
// TODO (6.4) (6.5): `⦇T⦈⊑⦇R⦈S ⇐ F(S)T⊑RS`; `⦇R⦈S⊑⦇T⦈ ⇐ RS⊑F(S)T` — Lean relCata_le_comp, comp_le_relCata.

== Hylomorphisms

// TODO Thm 6.2: `⦇S⦈°⦇R⦈=(μX : S°F(X)R)` — proved+steps and DRAWN at 11.6.4 (§@sec-hylo): cite with a
//   reference, do not redraw.
// TODO Cor 6.1: `⦇[S₁,S₂]⦈°⦇[R₁,R₂]⦈ = (μX : S₁°G(X)R₁ ∪ S₂°H(X)R₂)` — 2 steps (coproduct; coproduct);
//   Lean AOP.A6_3.hylo_eq_mu_coprod.

== Fast exponentiation and modulus computation

// TODO p.145 exp: `exp(a) ⊒ convert°convert exp(a) = convert°⦇[one,op(a)]⦈ = (μX : zero°one ∪ shift°(X×𝟙)op(a))`
//   — 3 steps (convert simple; fusion; Cor 6.1) + side conditions `zero exp(a)=one`,
//   `shift exp(a)=(exp(a)×𝟙)op(a)`; Lean AOP.A6_4_FastExp.exp_eq_mu.
// TODO p.145 mod: the same for `mod(b)`: `= (μX : zero°zero ∪ shift°(X×𝟙)op(b))`; Lean mod_eq_mu.

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
// TODO p.148 member: `member(id)=𝟙`, `member(K)=𝟘`, `member(F+G)=[member(F),member(G)]`,
//   `member(F×G)=outl member(F) ∪ outr member(G)`, `member(FG)=member(F)member(G)`, `member(P)=∈`,
//   `member(T)=setify(T)∈` — Lean idMembership, compMembership; `+`, `×`, `P`, `T` missing.
// TODO p.148 lax: `F(R)member ⊑ member R`, the largest lax natural `F ⟶ id`, hence unique — Lean
//   LaxMembership.laxNatural, largestLax_unique.
// TODO p.148 member α°: `α°member(F)` inductive; examples `[zero,succ]°[𝟘,𝟙]=succ°`,
//   `[nil,cons]°[𝟘,outr]=cons°outr=tail` — Lean missing.
// B&dM Theorem 6.3, p.149
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thm63_unique") \
    #src[when `S member` is inductive, two solutions `X`, `Y` of `X=SF(X)R` are equal]],
    // lean:AOP.A6_5.thm63_unique@d1b466e6
)]<thm63-unique>

// B&dM Theorem 6.3 (entire), p.149
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thm63_entire") \
    #src[when `S member` is inductive and `S`, `R` are entire, a pre-fixed point of `X↦SF(X)R` is entire]],
    // lean:AOP.A6_5.thm63_entire@04a95a25
)]<thm63-entire>

// B&dM Corollary 6.2, p.149
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.cor62") \
    #src[when `g member` is inductive and `f`, `g` are maps, the solution of `X=gF(X)f` is a map]],
    // lean:AOP.A6_5.cor62@b00cdf6c
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
    // lean:AOP.A6_5.cor63@17c6ea36
  lean-chain(
    (none, "Freyd.Alg.cor63.lhs", []),
    (SQ, "Freyd.Alg.cor63.rhs", src[@thm63-entire at `S=R°`]),
  ),
)]<cor63>

// B&dM Theorem 6.4, p.150
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.thm64") \
    #src[a map `f` with `Rf⊑F(f)α`, for a surjective `R`, has the fold `⦇R⦈` as its converse]],
    // lean:AOP.A6_5.thm64@8cc00228
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
    // lean:AOP.A6_5.thm64_claim@a0b6e290
  lean-chain(
    (none, "Freyd.Alg.thm64_claim_step1.lhs", []),
    (SQ, "Freyd.Alg.thm64_claim_step1.rhs", src[`Rf⊑F(f)α`, shunting]),
    // lean:AOP.A6_5.thm64_claim_step1@12aae1e3
    (SQ, "Freyd.Alg.thm64_claim_step2.rhs", src[`member` lax natural]),
    // lean:AOP.A6_5.thm64_claim_step2@fd00cb7e
  ),
)]<thm64-claim>

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
