#import "../note-prelude.typ": *
#show: note-chapter.with(6)
// note-split: chapter 6 — this header is written by scripts/note-split and stripped by scripts/note-join
= Recursive Programs






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

#pagebreak(weak: true)
