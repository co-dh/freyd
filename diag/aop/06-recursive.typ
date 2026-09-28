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

// TODO Thm 6.1: Knaster–Tarski, `R=⋂{X∣φ(X)⊑X}`; `φ(R)⊑R` (3 steps), `R⊑φ(R)` (2 steps);
//   Lean AOP.A6_2.mu_fixed via mu_prefixed, mu_postfixed, mu_le; statement drawn at @mu-laws (ch 11).
// TODO (6.2) (6.3): `⦇R⦈⊑X ⇐ α°F(X)R⊑X`; `X⊑⦇R⦈ ⇐ X⊑α°F(X)R` — Lean relCata_le_of_prefixed,
//   le_relCata_of_postfixed.
// TODO (6.4) (6.5): `⦇T⦈⊑⦇R⦈S ⇐ F(S)T⊑RS`; `⦇R⦈S⊑⦇T⦈ ⇐ RS⊑F(S)T` — Lean relCata_le_comp, comp_le_relCata.

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
