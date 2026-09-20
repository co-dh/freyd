#import "../note-prelude.typ": *
#show: note-chapter.with(10)
// note-split: chapter 10 — this header is written by scripts/note-split and stripped by scripts/note-join
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

`R□` is `R`'s target, an identity arrow. For `R : A⟶B` write `∋ : EB⟶B`, dropping the
subscript.

// The converse of epsiloff IS membership, and the note's pointwise glosses already write it `∈`.
`∈≜∋° : A⟶EA`
]]<pow-defn>

#disp[
  #show table.cell.where(x: 0): rownum
  #table(
  columns: (7.95cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

  [$#e[R] □ = R □$, #h(4pt) $#e[R] = #e[R □]$],
  [One `∋` per object, not per arrow.],

  [`∋` is *thick*],
  [*Comprehension*: every `x` has a set of exactly the people `x` admires.],

  [$frac(R, ∋)$ ` : A⟶EB`, for `R : A⟶B` ],
  [convert a relation to a function. `a` $frac(R, ∋)$ ` ={b|a R b}` ],
  [$frac(#[`R`], ∋)$ is a *map*],  [],

 [$frac(#[`R`], ∋)$ `∋=R` ], [#src[]],
  // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a

  [`F⊑` $frac(#[`F∋`], ∋)$, `F` simple],
 [A partial choice of sets is inside the total one. #src[]],
  // lean:Freyd.S2_40.simple_le_Λ_eps@a28487fe

  [$frac(#[`𝟙`], ∋)$, the *singleton map*, monic],
  [The one-person set.],

  [$frac(#[`∋`], ∋)$ `=𝟙`],
 [Make the set of a set, then read it back one level down. #src[]],
  // lean:AOP.A4_6.Λ_eps_reflection@2e9ddea3

  [*fusion:* $frac(#[`fR`], ∋)$ `=f` $frac(#[`R`], ∋)$, `f` a map],
  [Naturality of the unit, `f` $frac(#[`𝟙`], ∋)$ `=` $frac(#[`𝟙`], ∋)$ `(E(f))`.
 #src[]],
   // lean:AOP.A4_6.Λ_fusion@9d7bda13

  [$frac(#[`f`], ∋)$ `=f` $frac(#[`𝟙`], ∋)$, `f` a map],
  [Rename first or take singletons first — the fusion row above at `R=𝟙`.],

  [$frac(R, S) = frac(R, ∋) (frac(S, ∋))^circle.small$],
  [`x` and `y` match when `R` sends `x` and `S` sends `y` to the same set.],

  [`E(R)≜` $frac(#[`∋R`], ∋)$, `E≜` $frac(#[`∋·`], ∋)$], [`E(R): EA⟶EB`, image of a set of A],
  [$frac(#[`R`], ∋)$ `=` $frac(#[`𝟙`], ∋)$ `E(R)`],
 [$frac(#[`𝟙`], ∋)$`: x↦{x}` #src[]],
  // lean:AOP.A4_6.Λ_eq_singleton_existsImage@02b29ea8
  [$frac(#[`S`], ∋)$ `E(R)=` $frac(#[`S`], ∋)$ $frac(#[`∋R`], ∋)$ `=` $frac(#[`SR`], ∋)$],
  [absorption — the monad's composition law, $frac(#[`S`], ∋)$ `⋄` $frac(#[`R`], ∋)$ `=`
 $frac(#[`SR`], ∋)$, §@sec-kleisli #src[]],
   // lean:AOP.A4_6.Λ_absorption@e87bd8f2

  [`subset≜∋/∋ : EA⟶EA`],
  [`xs subset ys⟺∀a. ys∋a→xs∋a`, that is `ys⊆xs`, not `xs⊆ys`.],
)]<pow-laws>

== `i⊣E` Power Allegory defined as adjunction <sec-adj-E>

// The factorisation the whole adjunction is about, drawn once.  Middle arrow is `E(R)`, NOT `P(R)`:
// the two agree on maps only (B&dM p. 119), and `𝟙/∋ P(R)` is every nonempty subset of `R(a)`.
#disp[#pair(
  leancd("Freyd.Alg.Λ_comp_eps+Freyd.Alg.Λ_eq_singleton_existsImage"),
  // `𝟙/∋` opens the `i E` pair and `∋` closes it again, so the strand running in and out of a panel is
  // the one functor; the panel beside it draws that same functor as the plain wire the law equates it to.
  context {
    let g = grid(columns: 2, column-gutter: 14pt, align: horizon,
      snake(`i`, `E`, false), snake(`E`, `i`, true))
    let w = measure(g).width
    grid(columns: 1, row-gutter: 8pt, align: center, g,
      box(width: w, grid(columns: (1fr, 1fr), align: (center + horizon, center + horizon),
 [$frac(#[`𝟙`], ∋)$ `∋=𝟙` #src[]],
        // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a
 [$frac(#[`∋`], ∋)$ `=𝟙` #src[]])))
        // lean:AOP.A4_6.Λ_eps_reflection@2e9ddea3
  },
  [$frac(#[`R`], ∋)$ `∋=R` #h(1.4cm)
   #src[`EA` is the powerset of `A` — standard mathematics, but here `P` is
 already the relator `P(R)`. ]],
   // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a
   // B&dM write `PA` for the powerset.
  // The two snakes are four panels wide, so the pair only clears the 22cm text block scaled down.
  s: 95%,
)]<adj-E-bend>

#block[#src[`i` is the inclusion `Map(𝒜)⟶𝒜`, doing nothing, so `E` is both the functor and the
monad `iE`.]]

// The heading gets its own page: §10.1's pair fills the foot of the previous one, and the definition
// below is unbreakable, so the heading was left standing alone there.
#pagebreak(weak: true)
== `𝒜≅Kleisli(E)` <sec-kleisli>

// Every ingredient is a row of @pow-laws; nothing here is new.  `union` is `E(∋)`: the counit with
// `E` applied to it, which is the multiplication the adjunction hands back.
#disp[#block(breakable: false)[#definition[
`E(R)≜` $frac(#[`∋R`], ∋)$, #h(4pt) $frac(#[`𝟙`], ∋)$ ` : A⟶EA`, #h(4pt)
`union=E(∋)=` $frac(#[`∋∋`], ∋)$ ` : E(EA)⟶EA`

`f⋄g≜f E(g) union : A⟶EC`, #h(4pt) for `f : A⟶EB` and `g : B⟶EC`

#src[the monad is on `Map(𝒜)`, not on the allegory: `E` is a relator on all relations, but
$frac(#[`𝟙`], ∋)$,
`union` and `f E(g) union` are maps, and the Kleisli construction happens where they live.]
// lean:AOP.A4_6.bigUnion_eq_existsImage_eps@889637e4
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
  zstep(op: sym.eq, under: true)[@pow-laws, $frac(#[`R`], ∋)$ `∋=R`],
  zsqc([$frac(#[`S`], ∋)$ `E(R)`], none),
  zstep(op: sym.eq, under: true)[@pow-laws, absorption],
  zsqc([$frac(#[`SR`], ∋)$], none),
)
#align(center, block(width: 16.5cm, inset: (y: 4pt))[#align(center)[#src[the first three steps only
  unfold `⋄` — `E` is a functor, so `E(`$frac(#[`R`], ∋)$`)union=E(`$frac(#[`R`], ∋)$`∋)=E(R)` and the
  `union` is gone. Absorption, the row of @pow-laws, is the whole law, and it is the functoriality
 of $frac(#[`·`], ∋)$. ]]])
  // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a lean:AOP.A4_6.Λ_absorption@e87bd8f2
]<kleisli-comp>

#block[#src[`𝟙` goes to $frac(#[`𝟙`], ∋)$, the Kleisli identity, by definition — so
$frac(#[`·`], ∋)$ is an isomorphism of categories `𝒜≅Kleisli(E)`, and §@sec-adj-E's `i⊣E` is the
Kleisli adjunction. `i` is the identity on objects, so every object of the allegory is free.]]

