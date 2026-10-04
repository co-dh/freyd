#import "../note-prelude.typ": *
#show: note-chapter.with(10)
// note-split: chapter 10 — this header is written by scripts/note-split and stripped by scripts/note-join
#import "../shared-laws.typ": *
= Freyd's Power allegories <sec-power>

#disp[#definition[
A *power allegory* is a division allegory with one unary operation on arrows, `∋` *epsiloff*,
subject to

// Freyd's three display lines, in his order, with the names he gives the last two.  A stroke-less
// table, not three centred lines: the names have to hang off the containments they name.
#align(center, table(
  columns: 2, stroke: none, inset: (x: 14pt, y: 3pt), align: (left + horizon, left + horizon),
  [$#e[R] □ = R □, quad #e[R] = #e[R □]$], [],
  [$𝟙 ⊑ (R slash #e[R])(#e[R] slash R)$], [$#e[R]$ is *thick*],
  [$frac(#e[R], #e[R]) = 𝟙$], [$#e[R]$ is *straight*],
))
// lean:Freyd.S2_40.PowerAllegory@524da929

`R□` is `R`'s target, an identity arrow. For `R : A⟶B` write `∋ : PB⟶B`, dropping the
subscript.

// The converse of epsiloff IS membership, and the note's pointwise glosses already write it `∈`.
`∈≜∋° : A⟶PA`
]]<pow-defn>

#law-pow-laws

// Rows 5, 6, 9, 13, 14 of @pow-laws, each drawn whole from its own declaration, with every `%∋`
// opened to `(𝟙%∋)E(−)`; a row with hypotheses draws its conclusion.  Row 6 is its composite form,
// row 9 its `R`-free case `R=𝟙`.  Row 10 (`Λ_of_map`) is missing: it lives in a bare power
// allegory, where `E` is no lane (`existsImageFunctor` needs an unguarded one).
#disp[#grid(columns: 3, column-gutter: 14pt, row-gutter: 6pt, align: center + bottom,
  lean("Freyd.Alg.Λ_eps_eq'"),
  lean("Freyd.Alg.simple_le_singleton_existsImage"),
  lean("Freyd.Alg.singletonMap_natural"),
  src[#leanf("Freyd.Alg.Λ_eps_eq'")],
  // lean:Freyd.S2_40.Λ_eps_eq'@2de083e0
  src[#leanf("Freyd.Alg.simple_le_singleton_existsImage")],
  // lean:AOP.A4_6.simple_le_singleton_existsImage@cc1b7c9f
  src[#leanf("Freyd.Alg.singletonMap_natural")],
  // lean:AOP.A4_6.singletonMap_natural@332a071d
  lean("Freyd.Alg.Λ_eq_singleton_existsImage"),
  lean("Freyd.Alg.Λ_absorption.lhs"),
  [],
  src[#leanf("Freyd.Alg.Λ_eq_singleton_existsImage")],
  // lean:AOP.A4_6.Λ_eq_singleton_existsImage@49bf48f6
  src[#leanf("Freyd.Alg.Λ_absorption")],
  // lean:AOP.A4_6.Λ_absorption@00399742
  [],
)]<pow-laws-hm>

== `i⊣E` Power Allegory defined as adjunction <sec-adj-E>

#law-adj-E-bend

#block[#src[`i` is the inclusion `Map(𝒜)⟶𝒜`, doing nothing, so `E` is both the functor and the
monad `iE`.]]

== `∈\` as a composite <sec-mem-ldiv>

#law-mem-ldiv

#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.leftDiv_eq_Λ_subset") \
    #src[`b` is related to `c` by `R\S` exactly when `Λ(R°)(b) ⊆ Λ(S°)(c)`, the `R`-preimage of `b` inside the `S`-preimage of `c`]],
     // lean:AOP.A7_1.leftDiv_eq_Λ_subset@92f4fb8f
  lean-chain(
    (none, "Freyd.Alg.leftDiv_eq_Λ_subset_step1.lhs", []),
    (EQ, "Freyd.Alg.leftDiv_eq_Λ_subset_step1.rhs", src[`R=∈Λ(R°)°` — #ref(label("Freyd.Alg.Λ_eps_eq'"))]),
     // lean:AOP.A7_1.leftDiv_eq_Λ_subset_step1@389887f3
    (EQ, "Freyd.Alg.leftDiv_eq_Λ_subset_step2.rhs", src[`(XY)\S=Y\(X\S)`]),
     // lean:AOP.A7_1.leftDiv_eq_Λ_subset_step2@7002b70d
    (EQ, "Freyd.Alg.leftDiv_eq_Λ_subset_step3.rhs", src[`f°\X=fX`; `∈\S=⊆Λ(S°)°` — @mem-ldiv]),
     // lean:AOP.A7_1.leftDiv_eq_Λ_subset_step3@560d9192
  ),
)]<ldiv-comp>

// The heading gets its own page: §10.1's pair fills the foot of the previous one, and the definition
// below is unbreakable, so the heading was left standing alone there.
#pagebreak(weak: true)
== `𝒜≅Kleisli(E)` <sec-kleisli>

// Every ingredient is a row of @pow-laws; nothing here is new.  `union` is `E(∋)`: the counit with
// `E` applied to it, which is the multiplication the adjunction hands back.
#disp[#block(breakable: false)[#definition[
#leanf("Freyd.Alg.existsImage"), #h(4pt) $frac(#[`𝟙`], ∋)$ ` : A⟶PA`, #h(4pt)
#leanf("Freyd.Alg.bigUnion_eq_existsImage_eps") ` : PPA⟶PA`

#leanf("Freyd.Alg.kleisliComp"), #h(4pt) for `f : A⟶PB` and `g : B⟶PC`

#src[the monad is on `Map(𝒜)`, not on the allegory: `E` is a relator on all relations, but
$frac(#[`𝟙`], ∋)$,
`union` and `f E(g) union` are maps, and the Kleisli construction happens where they live.]
// lean:AOP.A4_6.bigUnion_eq_existsImage_eps@bca8d7c5 lean:AOP.A4_6.kleisliComp@70c8eb7e
]]]<kleisli-defn>

#disp[
#zline(
  zsqc([$frac(#[`S`], ∋)$ `⋄` $frac(#[`R`], ∋)$], none),
  zstep(op: sym.eq, under: true)[definition of `⋄`, `union=E(∋)`],
  zsqc([$frac(#[`S`], ∋)$ `E(`$frac(#[`R`], ∋)$`)E(∋)`], none),
  zstep(op: sym.eq, under: true)[`E` a functor, `E(X)E(Y)=E(XY)`],
  zsqc([$frac(#[`S`], ∋)$ `E(`$frac(#[`R`], ∋)$`∋)`], none),
)
#zline(
  zstep(op: sym.eq, under: true)[#ref(label("Freyd.Alg.Λ_eps_eq'")), $frac(#[`R`], ∋)$ `∋=R`],
  zsqc([$frac(#[`S`], ∋)$ `E(R)`], none),
  zstep(op: sym.eq, under: true)[@Freyd.Alg.Λ_absorption, absorption],
  zsqc([$frac(#[`SR`], ∋)$], none),
)
#align(center, block(width: 16.5cm, inset: (y: 4pt))[#align(center)[#src[the first three steps only
  unfold `⋄` — `E` is a functor, so `E(`$frac(#[`R`], ∋)$`)union=E(`$frac(#[`R`], ∋)$`∋)=E(R)` and the
  `union` is gone. Absorption, @Freyd.Alg.Λ_absorption, is the whole law, and it is the functoriality
 of $frac(#[`·`], ∋)$. ]]])
  // lean:Freyd.S2_40.Λ_eps_eq'@2de083e0 lean:AOP.A4_6.Λ_absorption@00399742
]<kleisli-comp>

#block[#src[`𝟙` goes to $frac(#[`𝟙`], ∋)$, the Kleisli identity, by definition — so
$frac(#[`·`], ∋)$ is an isomorphism of categories `𝒜≅Kleisli(E)`, and §@sec-adj-E's `i⊣E` is the
Kleisli adjunction. `i` is the identity on objects, so every object of the allegory is free.]]

