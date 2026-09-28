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
  // lean:AOP.A6_1_Digits.RelSet.Digits.val_converse_eq@639ee2c7
  // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_eq@19be99a2
  lean-chain(
    (none, "Freyd.Alg.RelSet.Digits.val_converse_step1.lhs", src[`val=⦇[embed,op]⦈` — definition]),
    (EQ, "Freyd.Alg.RelSet.Digits.val_converse_step1.rhs", src[`⦇φ⦈=α°F(⦇φ⦈)φ` — catamorphisms]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step1@b78dddd4
    (EQ, "Freyd.Alg.RelSet.Digits.val_converse_step2.rhs", src[`(RS)°=S°R°` — converse]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step2@65155218
    (EQ, "Freyd.Alg.RelSet.Digits.val_converse_step3.rhs", src[`F(R)°=F(R°)` — `F=(−×Digit)(Digit⁺+−)`, definition of `F`]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step3@e9a6a733
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step4@2be20807
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step5@69f15a17
    (EQ, "Freyd.Alg.RelSet.Digits.val_converse_step6.rhs.inr", src[`α=[wrap,snoc]`, then `(𝟙+S)[P,Q]=[P,SQ]` and `[g,h]°[P,Q]=g°P∪h°Q` — coproduct]),
    (none, "Freyd.Alg.RelSet.Digits.val_converse_step6.rhs.inl", src[]),
    // lean:AOP.A6_1_Digits.RelSet.Digits.cata_converse_step6@7d262eb2
  ),
)]<val-converse>
// TODO p.139 op°: `op(n,d)=m ≡ n=m div 10 ∧ d=m mod 10`; `op°` defined iff `m≥10`, `embed°` iff `m<10`
//   — a Lean lemma, not a picture.  PROVED: lean:AOP.A6_1_Digits.RelSet.Digits.op_recip_iff@78c25f21
//   lean:AOP.A6_1_Digits.RelSet.Digits.op_recip_defined@c44897b0
//   lean:AOP.A6_1_Digits.RelSet.Digits.embed_recip_defined@65abb14c.  Not displayed: `--formula`
//   drops a relation's points (`op° m p` prints `op°`), an exporter gap to close before a #leanf row.
// TODO p.139 digits: the join is a conditional; `val°` the unique solution, total; `digits=val°`.

// Otherwise the heading lands alone at the foot of the reduce-of-maps page.
#pagebreak(weak: true)
== `φ(Y)⊑Y⟹(μX : φ(X))⊑Y` <sec-mu>

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

== `⦇S⦈°⦇R⦈=(μX : S°F(X)R)` <sec-hylo>

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

// TODO p.145 exp: `exp(a) ⊒ convert°convert exp(a) = convert°⦇[one,op(a)]⦈ = (μX : zero°one ∪ shift°(X×𝟙)op(a))`
//   — 3 steps (convert simple; fusion; Cor 6.1) + side conditions `zero exp(a)=one`,
//   `shift exp(a)=(exp(a)×𝟙)op(a)`; Lean AOP.A6_4_FastExp.exp_eq_mu.
// TODO p.145 mod: the same for `mod(b)`: `= (μX : zero°zero ∪ shift°(X×𝟙)op(b))`; Lean mod_eq_mu.

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
