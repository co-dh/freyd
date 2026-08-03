// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name.  See the header of strdiag.typ.
#import "strdiag.typ": conv, meet, wire

// EVERY PICTURE OF A THEOREM BELOW IS EXPORTED, NOT DRAWN.  `./scripts/diag-export <decl>` walks the
// Lean declaration's TYPE and writes diag/generated/<decl>.typ, which binds the cetz drawing to
// `pic`; this note only places those bindings in table cells.  Hand-drawing them is how the first
// draft of this page got `inter_assoc` wrong — it showed coassociativity of `◁` instead of the axiom
// — and dropped the `=` from `recip_inter`.  A picture derived from the statement cannot drift from
// it.  `./scripts/diag-regen` redraws every binding below, reading the list off these very imports.
#import "generated/Freyd.Diag.CartBicat.conv_conv.typ": pic as p-conv-conv
#import "generated/Freyd.Diag.CartBicat.conv_comp.typ": pic as p-conv-comp
#import "generated/Freyd.Diag.conv_inter.typ": pic as p-conv-inter
#import "generated/Freyd.Diag.meet_top.typ": pic as p-meet-top
#import "generated/Freyd.Diag.meet_comm.typ": pic as p-meet-comm
#import "generated/Freyd.Diag.meet_assoc.typ": pic as p-meet-assoc
#import "generated/Freyd.Diag.meet_idem.typ": pic as p-meet-idem
#import "generated/Freyd.Diag.semidistrib_of_lax.typ": pic as p-semidistrib
#import "generated/Freyd.Diag.«≤_top».typ": pic as p-le-top
#import "generated/Freyd.Diag.CartBicat.Δ_assoc.typ": pic as p-d-assoc
#import "generated/Freyd.Diag.CartBicat.Δ_comm.typ": pic as p-d-comm
#import "generated/Freyd.Diag.CartBicat.Δ_counit.typ": pic as p-d-counit
#import "generated/Freyd.Diag.CartBicat.«∇_assoc».typ": pic as p-n-assoc
#import "generated/Freyd.Diag.CartBicat.«∇_comm».typ": pic as p-n-comm
#import "generated/Freyd.Diag.CartBicat.«∇_unit».typ": pic as p-n-unit
#import "generated/Freyd.Diag.CartBicat.«∇Δ≤𝟙».typ": pic as p-37
#import "generated/Freyd.Diag.CartBicat.«𝟙≤Δ∇».typ": pic as p-38
#import "generated/Freyd.Diag.CartBicat.«?!≤𝟙».typ": pic as p-39
#import "generated/Freyd.Diag.CartBicat.«𝟙≤!?».typ": pic as p-40
#import "generated/Freyd.Diag.CartBicat.frob.proof.typ": branches as frobb
#import "generated/Freyd.Diag.CartBicat.snakes.proof.typ": branches as snakeb
#import "generated/Freyd.Diag.CartBicat.snake'.proof.typ": branches as snkb
#import "generated/Freyd.Diag.CartBicat.lax_Δ.typ": pic as p-lax-delta
#import "generated/Freyd.Diag.CartBicat.lax_!.typ": pic as p-lax-bang
#import "generated/Freyd.Diag.«lax_∇».typ": pic as p-lax-nabla
#import "generated/Freyd.Diag.lax_?.typ": pic as p-lax-unit
#import "generated/Freyd.Diag.Biprod.«≤_union_left».typ": pic as p-union-left
#import "generated/Freyd.Diag.Biprod.union_comm.typ": pic as p-union-comm
#import "generated/Freyd.Diag.Biprod.bot_union.typ": pic as p-bot-union
#import "generated/Freyd.Diag.Biprod.comp_union.typ": pic as p-comp-union
#import "generated/Freyd.Diag.Biprod.conv_union.typ": pic as p-conv-union
#import "generated/Freyd.Diag.FbCbRig.meet_union_distrib.typ": pic as p-distrib
#import "generated/Freyd.Diag.CartBicat.conv_comp.proof.typ": branches as l42ii
#import "generated/Freyd.Diag.CartBicat.conv_tensHom.proof.typ": branches as l42iii
#import "generated/Freyd.Diag.CartBicat.conv_mono.proof.typ": branches as l42iv
#import "generated/Freyd.Diag.CartBicat.«°_slide».typ": pic as p-conv-slide
#import "generated/Freyd.Diag.SingleValued.typ": pic as p-sv46
#import "generated/Freyd.Diag.Total.typ": pic as p-tot47
#import "generated/Freyd.Diag.Injective.typ": pic as p-inj48
#import "generated/Freyd.Diag.Surjective.typ": pic as p-sur49
#import "generated/Freyd.Diag.comp_meet_of_singleValued.typ": lhs as p-236a, rhs as p-236b
// The allegory layer's division (last section).  `Freyd.Alg`, not `Freyd.Diag`: `/` is a theorem of
// `Freyd/S2_30.lean` and `AOP/A4_4`, and of nothing in `diag/`.
#import "generated/Freyd.Alg.le_div_iff.typ": pic as p-le-div
#import "generated/Freyd.Alg.le_leftDiv_iff.typ": pic as p-le-ldiv
#import "generated/Freyd.Alg.DivisionAllegory.div_comp_le.typ": pic as p-div-cancel
#import "generated/Freyd.Alg.leftDiv_comp_le.typ": pic as p-ldiv-cancel
#import "generated/Freyd.Alg.div_comp_assoc.typ": pic as p-div-assoc
#import "generated/Freyd.Alg.leftDiv_comp.typ": pic as p-ldiv-assoc
#import "generated/Freyd.Alg.map_comp_div.typ": pic as p-map-div
#import "generated/Freyd.Alg.div_comp_recip_map.typ": pic as p-div-map
#import "generated/Freyd.Alg.symmDiv.typ": pic as p-symmdiv
#import "generated/Freyd.Alg.symmDiv_recip.typ": pic as p-sdiv-recip
#import "generated/Freyd.Alg.symmDiv_comp.typ": pic as p-sdiv-comp
// §2.314's list, in the book's order.
#import "generated/Freyd.Alg.div_comp.typ": pic as p-div-comp
#import "generated/Freyd.Alg.one_le_div_self.typ": pic as p-one-div
#import "generated/Freyd.Alg.div_self_comp_self.typ": pic as p-div-self-idem
#import "generated/Freyd.Alg.div_self_comp.typ": pic as p-div-self
#import "generated/Freyd.Alg.div_one.typ": pic as p-div-one
#import "generated/Freyd.Alg.div_union.typ": pic as p-div-union
#import "generated/Freyd.Alg.leftDiv_div.typ": pic as p-ldiv-div

#show: conf.with(title: "The allegory axioms, and what defines them in the Frobenius calculus")

= Cartesian bicategory of relations

#definition[
A *cartesian bicategory of relations* is a poset-enriched category(bicategory)
that is has a symmetric monoidal product $times.o$ (cartisin product of set in Rel, vertical junctposition in the diagram) and

  #align(center, block(inset: (y: 6pt))[
    #text(12.5pt)[ $forall$ object A, `(A, ◁, ⊸) ⊣ (A, ▷, ⟜)`,  *Frobenius*, arrows *lax*.]
    #v(3pt)
    #src[`(◁ : A ⟶ A ⊗ A, ⊸ : A ⟶ 𝕀)` formed a cocommutative comonoid] \
    #src[`(▷ : A ⊗ A ⟶ A, ⟜ : 𝕀 ⟶ A)` formed a commutative monoid]
  ])
]

#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + horizon,
  P(p-d-assoc, s: 60%), P(p-d-comm, s: 60%), P(p-d-counit, s: 60%),
)

#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + horizon,
  P(p-n-assoc, s: 60%), P(p-n-comm, s: 60%), P(p-n-unit, s: 60%),
)

In `Rel(Set)`, the four generators are these relations on a set `A`:

#align(center, table(
  columns: 2, stroke: none, inset: (x: 8pt, y: 2.5pt), align: left,
  [`◁`], src[`= {(a, (a, a))}` — copy: one in, two identical out],
  [`▷`], src[`= {((a, a), a)}` — merge: a pair passes only when its two components agree, and the
   common value comes out],
  [`⊸`], src[`= A × {∗}` — discard: forget the value, keep only that there was one],
  [`⟜`], src[`= {∗} × A` — create: any element at all],
))

== $forall$ object A, `(A, ◁, ⊸) ⊣ (A, ▷, ⟜)`

#grid(columns: (1fr, 1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-37, s: 52%) #v(-7pt) \ #src[`▷ ◁ ≤ 𝟙`]],
  [#P(p-38, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ◁ ▷`]],
  [#P(p-39, s: 52%) #v(-7pt) \ #src[`⟜ ⊸ ≤ 𝟙`]],
  [#P(p-40, s: 52%) #v(-7pt) \ #src[`𝟙 ≤ ⊸ ⟜`]],
)

The last of these is the only one that makes a picture *bigger*, and it is worth a name: *a wire is
below the cut wire*. In `Rel` it reads `{(a, a)} ⊆ A × A` — cut a wire and its two ends stop having
to agree, so cutting can only add pairs. It is the one weakening this calculus gives away for free.

== The Frobenius law

#row(frobb.at(0).steps, s: 54%)

The only clause coupling the comonoid to the monoid beyond adjointness. Both sides reduce to the
same picture, `▷ ◁` — merge, then copy — which is the two-in two-out *spider*. Every connected
diagram built from these four generators collapses to the spider on its own inputs and outputs, and
this equation is what starts that collapse. A *bubble* is the other order, `◁ ▷`: copy then merge,
a closed loop, which the idempotency of `∩` uses below.

== Every arrow is a lax comonoid homomorphism

#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-lax-delta, s: 60%) #v(-7pt) \ #src[`R◁ ≤ ◁(R⊗R)`]],
  [#P(p-lax-bang, s: 60%) #v(-7pt) \ #src[`R⊸ ≤ ⊸`]],
)

// Its definition box was straddling the break, which reads as two half-boxes.
#pagebreak(weak: true)
= ° : 𝒞ᵒᵖ ⟶ 𝒞 is a 2 functor 

#definition[
The *converse* `R°` of `R : a ⟶ b` is `R` with both of its wires turned round,

#fig({ conv((0, -0.80), $R$) })

#align(center, block(inset: (y: 4pt))[#text(12.5pt)[`R° = (⟜◁ ⊗ 𝟙) (𝟙 ⊗ R ⊗ 𝟙) (𝟙 ⊗ ▷⊸)`]])

where `⟜◁ : 𝕀 ⟶ a ⊗ a` opens a pair of wires out of nothing and `▷⊸ : b ⊗ b ⟶ 𝕀` closes one, so
the input of `R°` is where the output of `R` was. And it is a contravariant 2-functor `° : 𝒞ᵒᵖ ⟶ 𝒞`:

#align(center, block(inset: (y: 5pt))[
  (i) `𝟙° = 𝟙`  #h(1cm) (ii) `(R S)° = S° R°`  #h(1cm) (iii) `(R ⊗ S)° = R° ⊗ S°`
  #h(1cm) (iv) `R ≤ S` implies `R° ≤ S°`
])
]

== `𝟙° = 𝟙`  (snake)

#chain(
  (snkb.at(0).steps.at(2), snkb.at(0).steps.at(3), snkb.at(0).steps.at(5)),
  ([], [Frobenius], [unit, counit]))

== The slide

The one rule (ii) and (iii) use, and each of them uses it twice. A converse facing a merge on the
lower strand is the box itself, upright, on the upper one:

#P(p-conv-slide, s: 62%)

`R°` is DEFINED as the bending of `(R ⊗ 𝟙) ▷⊸`, so the slide claims only that unbending it gives
that back — and unbending undoes bending for every arrow. That is the snake above with a passenger:
the `⟜◁` bends the `a` strand down and the `▷⊸` brings it back up, while the `b` strand rides
through untouched. Nothing else is spent below.

== `(R S)° = S° R°`

#chain(
  (l42ii.at(0).steps.at(0), l42ii.at(0).steps.at(3), l42ii.at(0).steps.at(4),
   l42ii.at(0).steps.at(5), l42ii.at(0).steps.at(7)),
  ([], [slide], [interchange], [slide], [snake]), s: 41%)

== `(R ⊗ S)° = R° ⊗ S°`

A merge at a product is two merges behind a crossing, so the pair unbends one strand at a time and
the crossing is all that is left to move.

#chain(
  (l42iii.at(0).steps.at(0), l42iii.at(0).steps.at(1), l42iii.at(0).steps.at(3),
   l42iii.at(0).steps.at(4), l42iii.at(0).steps.at(6)),
  ([], [a strand per letter], [`σ` past both boxes], [slide, twice], [snake]), s: 36%)

// Kept whole: the row is two pictures, and the break was falling between them and their heading.
#block(breakable: false)[
== `R ≤ S` implies `R° ≤ S°`

`R` sits in a frame of wires built from `≫` and `⊗`, and both of those are monotone, so the box may
be replaced where it stands.

#chain(
  (l42iv.at(0).steps.at(1), l42iv.at(0).steps.at(2)),
  ([], [`≫`, `⊗` monotone]), s: 55%)
]



= Every arrow is a lax monoid homomorphism

The merge/create mirror of the two comonoid laws opening this note — the paper's (41) and (42),
p. 22, which it gets by bending them with (ii) and (iv) above. No bending is needed: expand by the
unit `𝟙 ≤ ◁ ▷`, duplicate the box with the comonoid law, contract by the counit `▷ ◁ ≤ 𝟙`. Both
halves of the adjunction, and nothing else.

In `Rel(Set)` with `R ⊆ A × B`, where `▷` is the equality test on a pair and `⟜` produces any
element at all:

#align(center, table(
  columns: 2, stroke: none, inset: (x: 8pt, y: 2.5pt), align: left,
  [`▷ R`], src[`= {((a, a ), b) : a R b}` — two equal inputs, then one run of `R`],
  [`(R ⊗ R) ▷`], src[`= {((a, a'), b) : a R b and a' R b}` — a run on each input, then the results
   merged],
  [`⟜ R`], src[`= {(∗, b) : ∃a. a R b}` — the image of `R`],
  [`⟜`], src[`= {∗} × B` — all of `B`],
))

Take `a' = a` for the first containment; every `b` lies in `B` for the second. Each is strict exactly
when its reverse fails — `R` not injective, `R` not surjective — which is what the later table on
maps reads off them.

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*inequation, and what proves it*], [*picture*]),

  [(41) `▷ R ≤ (R ⊗ R) ▷` \
   #src[`▷R = ▷R𝟙 ≤ ▷R◁▷ ≤ ▷◁(R⊗R)▷ ≤ (R⊗R)▷` — unit, lax `◁`, counit.]],
  P(p-lax-nabla),

  [(42) `⟜ R ≤ ⟜` \
   #src[`⟜R = ⟜R𝟙 ≤ ⟜R⊸⟜ ≤ ⟜⊸⟜ ≤ ⟜` — the same three steps at `𝕀`.]],
  P(p-lax-unit),
)

#pagebreak(weak: true)
= `∩` is a commutative idempotent monoid on every hom-set

#definition[
The *meet* of `R, S : a ⟶ b`, the paper's *convolution*, is `R ∩ S := ◁ (R ⊗ S) ▷` — copy the
input, run `R` and `S` on the two copies, merge the results — so what comes out is what both of them
do.

#fig({ meet((0, 0), $R$, $S$) })
#align(center, src[transcribed: a definition has no statement to export])

On every hom-set it is associative, commutative and idempotent, with unit the maximal arrow
`⊤ = ⊸ ⟜` #src[(the paper's Lemma 4.11)].
]

#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-meet-top, s: 60%) #v(-7pt) \ #src[*unit:* one half of `⊤` per end — the merge's unit law
   absorbs the `⟜`, the copy's counit law the `⊸`]],
  [#P(p-meet-comm, s: 60%) #v(-7pt) \ #src[*commutative:* `σ` crosses `R ⊗ S` by naturality and is
   absorbed by cocommutativity and commutativity]],
  [#P(p-meet-assoc, s: 44%) #v(-7pt) \ #src[*associative:* coassociativity and associativity; `⊗`
   re-brackets for nothing, being strict here]],
  [#P(p-meet-idem, s: 60%) #v(-7pt) \ #src[*idempotent:* the one that is not bookkeeping — the lax
   copy law is the whole of it, worked in allegory2]],
)

So `≤` is the order this monoid induces. `R ∩ S ≤ R` comes from the unit, and idempotency turns
anything under both `S` and `T` into something under `S ∩ T`, since `R = R ∩ R ≤ S ∩ T`.

And one law relating `∩` to composition, which is *not* an equation:

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*semi-distributivity, and what supplies it*], [*picture*]),

  [`R (S ∩ T) ⊑ R S ∩ R T` — the lax copy law. #src[Equality exactly when `R` is single valued: the Maps section's
   `F (R ∩ S) = F R ∩ F S`.]], P(p-semidistrib),
)

= Unitary and pre-tabular — what the other direction needs

#table(
  columns: (3.2cm, 1fr, 1fr),
  align: (left + top, left + top, left + top),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*condition*], [*allegory*], [*Frobenius side*]),

  [*unitary*],
  [`T` is a *unit* when `𝟙 T` is the largest endomorphism on it and every object carries an entire
   arrow to it. A unit is what makes `⊤` exist.],
  [*free.* `𝕀` is the unit object, `𝟙 ≤ ⊸ ⟜` says `⊸` is entire, and `⊤ = ⊸ ⟜` is maximal.],

  [*pre-tabular*],
  [`f, g` *tabulate* `R` when both are maps, `R = f° g`, and

   #row((cetz.canvas(length: 0.72cm, { meet((0, 0), $f f°$, $g g°$) }),
         $=$,
         cetz.canvas(length: 0.72cm, { wire((0, 0), (1.5, 0)) })))

   `R` is *tabular* when some pair tabulates it, the allegory *pre-tabular* when every arrow lies
   under a tabular one.],
  [*this is what `⊗` is.* Given unitarity it reduces to tabulating each `⊤`, and a tabulation of `⊤`
   is an object `n ⊗ m` with its two projections. One side derives the product from tabulations, the
   other posits it.],
)

Together: *cartesian bicategory of relations ≃ unitary pre-tabular allegory*.

#pagebreak(weak: true)
= Union

Past what the definition can build: a union needs a *biproduct* on top of the Frobenius structure.
It draws as a *tape* — the rounded wrapper is the second product, and its fork and join open and
close a branch a particle takes exactly one of. #src[The residual, which needs a second composition
with linear adjoints, is in the division section below.]

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*statement*], [*picture*]),

  [`R ⊑ R ∪ S` #h(4pt) #src[`union R S := ⟨R, S⟩ [𝟙, 𝟙]`: offer both branches, then forget which was
   taken.]],
  P(p-union-left),

  [`R ∪ S = S ∪ R`], P(p-union-comm),
  [`⊥ ∪ R = R` #h(4pt) #src[`⊥` routes through the zero object; there is no shape for it.]],
  P(p-bot-union),
  [`R (S ∪ T) = R S ∪ R T` — composition distributes over union, which `∩` does not.],
  P(p-comp-union),
  [`(R ∪ S)° = R° ∪ S°`], P(p-conv-union),
  [`R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)` — what makes the whole *distributive*, and the one picture with
   both layers in it.], P(p-distrib, s: 78%),
)

The last of Freyd's §2.21 equations that have no picture here — a tape around nothing, or a tape
around what is already inside it, is not worth drawing. `R` = shops with rice, `S` = shops with
sugar throughout.

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*equation*], [*the rice reading*]),

  [`R ∪ (S ∩ R) = R` #h(10pt) `(R ∪ S) ∩ R = R` #h(4pt) #src[absorption]],
  [Shops with rice, or with both: still the shops with rice. Shops with rice or sugar, and with
   rice: the same. The smaller side of each pair is already inside the larger.],

  [`R ⊥ = ⊥` #h(4pt) #src[`R 0_S = 0_{R S}` — and `⊥ R = ⊥` on the other side]],
  [Going to a shop and then taking a road that leads nowhere gets you nowhere. `⊥` is a two-sided
   zero for composition, as `⊤` is not.],
)

#pagebreak(weak: true)
= Maps

Every arrow is lax for `◁` and for `⊸` by axiom, and for `▷` and `⟜` by the lax monoid section. All four
hold for *every* arrow, their REVERSES do not, and each reverse holding is a property of the arrow.
The right-hand column is the *adjoint* form, which is the definition
used here because it is literally the allegory's `Simple` and `Entire`; that the two forms agree is
a separate theorem, not proved here.

#table(
  columns: (1fr, 4.6cm, 1fr),
  align: (center + horizon, left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*holds for every arrow*], [*property*], [*holds iff*]),

  [#src[`R ◁ ≤ ◁ (R ⊗ R)`] #v(-2pt) #P(p-lax-delta, s: 74%)],
  [(SV) *single valued* \ #src[`R° R ⊑ 𝟙`]],
  P(p-sv46, s: 74%),

  [#src[`R ⊸ ≤ ⊸`] #v(-2pt) #P(p-lax-bang, s: 74%)],
  [(TOT) *total* \ #src[`𝟙 ⊑ R R°`. With *single valued*, a *map*.]],
  P(p-tot47, s: 74%),

  [#src[`▷ R ≤ (R ⊗ R) ▷`] #v(-2pt) #P(p-lax-nabla, s: 74%)],
  [(INJ) *injective* \ #src[`R R° ⊑ 𝟙`]],
  P(p-inj48, s: 74%),

  [#src[`⟜ R ≤ ⟜`] #v(-2pt) #P(p-lax-unit, s: 74%)],
  [(SUR) *surjective* \ #src[`𝟙 ⊑ R° R`, that is, `R°` entire.]],
  P(p-sur49, s: 74%),
)

What (SV) buys, in one law. Only single valuedness is spent: `F` may be partial, and entireness is
never used.

#table(
  columns: (1fr, 2.2fr),
  align: (center + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*picture*]),

  [`F (R ∩ S) = F R ∩ F S` \ #v(2pt) #src[`F` single valued] \ #v(6pt)
   #src[`F` = shops Ann may go to, `R` = has rice, `S` = has sugar. Single valued means one shop, so
   the sides agree.]],
  grid(columns: 3, align: horizon, column-gutter: 10pt,
    [#P(p-236a, s: 74%) #v(-9pt) #align(center, src[one shop with both])],
    text(17pt)[=],
    [#P(p-236b, s: 74%) #v(-9pt) #align(center, src[rice at A, sugar at B])],
  ),
)

// Its own page: the ten rows are one table and the long-division figure heads them, so a break
// inside would separate the metaphor from the laws it explains.
#pagebreak(weak: true)
= Division is WHAT!

#align(center, `m (R/S) d  ⟺  ∀i. d S i → m R i`)

Read the bar as *what*: `R/S` relates a producer to a consumer when the producer supplies #emph[what]
the consumer asks for. Each picture below is one such reading — supply on the left, demand on the
right, the ingredients they meet over in the middle.

// The three quotients, a drawing each: SUPPLY on the left, the ingredients in a column down the
// middle, DEMAND on the right, every arrow pointing at the ingredient it names.  A quotient is then
// a question the reader answers by eye — is every arrow into an ingredient from the right matched by
// one from the left? — and its answer is the arc over (or under) the column.  ONE function, not
// three canvases: the pictures differ only in their two lists, their two colours and their arcs.
// Colour marks WHICH node, not which side — the sides are already told apart by position, so
// spending a hue on them would leave nothing to tell `m` from `m'`.  First in a column blue, second
// pink, on both sides.
#let PAL = (rgb("#1a5fb4"), rgb("#c2247f"))
#let ARC = rgb("#7d3c98")
#let quot(sup, dem, arcs, supLab, demLab, arcLab, reading) = {
  align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.86cm, {
    let iy = (spice: 2.4, chicken: 0.8, peanut: -0.8, oil: -2.4)
    // Nodes are drawn last, with a white fill, so an edge may start at the node's centre and let the
    // box cover the stub — every edge then ends the same distance from its label, whatever its width.
    for (k, row) in sup.enumerate() { for it in row.at(2) {
      d.line((-5.6, row.at(0)), (-1.05, iy.at(it)), mark: (end: ">", scale: 0.5),
        stroke: 0.75pt + PAL.at(k)) } }
    for (k, row) in dem.enumerate() { for it in row.at(2) {
      d.line((5.6, row.at(0)), (1.05, iy.at(it)), mark: (end: ">", scale: 0.5),
        stroke: 0.75pt + PAL.at(k)) } }
    for (ys, ye, up) in arcs {
      d.bezier((-5.6, ys + 0.45 * up), (5.6, ye + 0.45 * up), (-3.2, 3.8 * up), (3.2, 3.8 * up),
        mark: (end: ">", scale: 0.55), stroke: 0.9pt + ARC) }
    let node(x, y, c, w) = d.content((x, y), box(inset: 4pt, fill: white)[#text(10pt, c)[#w]])
    for (k, row) in sup.enumerate() { node(-5.6, row.at(0), PAL.at(k), row.at(1)) }
    for (k, row) in dem.enumerate() { node(5.6, row.at(0), PAL.at(k), row.at(1)) }
    for (it, y) in iy { node(0, y, black, [#it]) }
    for (ys, ye, up) in arcs {
      d.content((0, 3.3 * up), box(inset: 3pt, fill: white)[#text(9.5pt, ARC)[#arcLab]]) }
    d.content((-5.6, 3.75), text(9.5pt, luma(60))[#supLab])
    d.content((5.6, 3.75), text(9.5pt, luma(60))[#demLab])
  })))
  // The whole of the quotient in one line of English, under the picture that built it.
  align(center, text(11pt)[#reading])
}

#quot(
  ((1.6, [market `m`], ("spice", "chicken", "peanut")), (-1.6, [market `m'`], ("spice", "chicken"))),
  ((1.6, [kung pao], ("spice", "chicken", "peanut")), (-1.6, [chilli chicken], ("spice", "chicken", "oil"))),
  ((1.6, 1.6, 1),), [`R` retails — supply], [`S` specifies — demand], [`R/S` fills],
  [`R/S` — market retails #emph[what] dish specifies])

Every arrow the dish sends into the ingredient column has to be matched by one from the market, so
here a single pair survives: `m'` fills no dish, lacking both peanut and oil, and chilli chicken is
filled by no market, since neither stocks oil.

#quot(
  ((1.6, [kung pao], ("spice", "chicken", "peanut")), (-1.6, [chilli chicken], ("spice", "chicken", "oil"))),
  ((0, [guest `g`], ("spice", "chicken")),),
  ((1.6, 0, 1), (-1.6, 0, -1)), [`S` specifies — supply], [`W` takes — demand], [`S/W` satisfies],
  [`S/W` — dish specifies #emph[what] guest takes])

The same test with the guest as the consumer. `g` takes spice and chicken, and both dishes need
both, so both satisfy him — a dish may need more, never less.

#quot(
  ((1.6, [market `m`], ("spice", "chicken", "peanut")), (-1.6, [market `m'`], ("spice", "chicken"))),
  ((0, [guest `g`], ("spice", "chicken")),),
  ((1.6, 0, 1), (-1.6, 0, -1)), [`R` retails — supply], [`W` takes — demand], [`R/W` feeds],
  [`R/W` — market retails #emph[what] guest takes])

And with the market as the producer: both markets sell spice and chicken, so both feed `g` —
`m'` included, though it fills no dish. Dropping the ingredients now, the three arcs sit like this:

// The composite, with the ingredient column gone: at this level `(R/S)(S/W) ⊑ R/W` is the statement
// that a PATH is a special case of an arrow, and its strictness is a missing path you can see.
#align(center, box(inset: (y: 12pt), cetz.canvas(length: 1cm, {
  let QUO = ARC
  let WANT = rgb("#26734d")
  let arrow(a, b, c) = d.line(a, b, mark: (end: ">", scale: 0.55), stroke: 0.9pt + c)
  arrow((-3.5, 1.3), (-1.4, 1.3), QUO)
  arrow((1.4, 1.3), (3.3, 0.35), WANT)
  arrow((1.5, -1.3), (3.3, -0.35), WANT)
  d.bezier((-4.6, 1.85), (4.1, 0.6), (-2.6, 3.2), (2.4, 2.9),
    mark: (end: ">", scale: 0.55), stroke: (paint: luma(70), thickness: 0.8pt, dash: "dashed"))
  d.bezier((-4.6, -1.85), (4.1, -0.6), (-2.6, -3.2), (2.4, -2.9),
    mark: (end: ">", scale: 0.55), stroke: (paint: luma(70), thickness: 0.8pt, dash: "dashed"))
  let node(x, y, w) = d.content((x, y), box(inset: 4pt, fill: white)[#text(10pt)[#w]])
  node(-4.6, 1.3, text(PAL.at(0))[market `m`]); node(-4.6, -1.3, text(PAL.at(1))[market `m'`])
  node(0, 1.3, text(PAL.at(0))[kung pao]); node(0, -1.3, text(PAL.at(1))[chilli chicken])
  node(4.1, 0, text(PAL.at(0))[guest `g`])
  d.content((-2.45, 1.75), text(9.5pt, QUO)[`R/S`])
  d.content((2.6, 1.15), text(9.5pt, WANT)[`S/W`])
  d.content((-0.4, 2.62), box(inset: 3pt, fill: white)[#text(9.5pt, luma(70))[`R/W`]])
  d.content((-0.4, -2.62), box(inset: 3pt, fill: white)[#text(9.5pt, luma(70))[`R/W`]])
  d.content((-0.4, -3.35), text(9pt, luma(70))[`m'` reaches `g` through no dish])
})))

`(R/S)(S/W)` is a path: `m` → kung pao → `g`, and that is all of it. `R/W` also holds of `m'`,
which retails everything `g` wants — but `m'` fills no dish, so nothing composes to it. The missing
path is exactly the strictness of `(R/S)(S/W) ⊑ R/W`.

// Two columns like every other table, one law per row.  The pictures here are the widest in the
// note — `le_div_iff` is a `⟺` between two containments, four sub-pictures in a row, 10.9cm before
// scaling — which is why the picture column gets the rest of the 22cm and the laws that used to
// share a row are split: one picture per row is what keeps them at readable size.
#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`X ⊑ R/S ⟺ X S ⊑ R` \ #src[`X` is any market-to-dish pairing; one that only pairs a market with
   dishes it fills lies inside `R/S`, and `R/S` is the largest such.]],
  P(p-le-div),

  [`X ⊑ S\R ⟺ S X ⊑ R` \ #src[The mirror — divide on the left when the market comes first.]],
  P(p-le-ldiv),

  [`(R/S) S ⊑ R` \ #src[There is a dish `m` fills that specifies `i` — then `m` retails `i` too. Strict at
   `S = ∅`: `R/S` is everything, `(R/S) S = ∅`.]],
  P(p-div-cancel),

  [`S (S\R) ⊑ R` \ #src[The mirror.]],
  P(p-ldiv-cancel),

  [*associate:* `R/(S₁ S₂) = (R/S₂)/S₁` \ #src[A dish of dishes: divide by the far end first.]],
  P(p-div-assoc),

  [`(S₁ S₂)\R = S₂\(S₁\R)` \ #src[The mirror.]],
  P(p-ldiv-assoc),

  [*maps:* `f (R/S) = (f R)/S` \ #src[Rename the market before or after dividing — the licence to write
   `f R / S`.]],
  P(p-map-div),

  [`R/(f S) = (R/S) f°` \ #src[Rename the dish: a map leaves a denominator as `f°` outside the box.]],
  P(p-div-map),

  [`(R/S)(S/W) ⊑ R/W` \ #src[A market that fills a dish that satisfies a guest feeds that guest.]],
  P(p-div-comp),

  [`𝟙 ⊑ R/R` \ #src[`R/R` runs market to market: each fills its own list. Strict: two markets
   retailing only spice fill each other's and stay two markets.]],
  P(p-one-div),

  [`(R/R)(R/R) = R/R` \ #src[`R/R` is the preorder *retails at least as much as*, and a preorder is
   idempotent. Freyd writes `⊑`; with `𝟙 ⊑ R/R` above it is an equality.]],
  P(p-div-self-idem),

  [`(R/R) R = R` \ #src[Reaching `i` through a market whose list `m` fills is reaching it
   directly, since `m` fills its own.]],
  P(p-div-self),

  [`R/𝟙 = R` \ #src[Filling the dish that specifies exactly `i` is retailing `i`.]],
  P(p-div-one),

  [`R/(S₁ ∪ S₂) = R/S₁ ∩ R/S₂` \ #src[Filling a dish made of two is filling each of them.]],
  P(p-div-union),

  [`S\(R/W) = (S\R)/W` \ #src[Which is why `S\R/W` needs no bracket.]],
  P(p-ldiv-div),
)

Fifteen laws, fifteen pictures, and not one shows a generator: `∩`, `∪`, `°` and composition are what
the Frobenius generators build, and `/` is none of those — it is posited, with nothing to unfold.

= Symmetric division

$frac(R, S)$ `≜ (R/S) ∩ (S/R)°`. In `Rel` it relates `m` and `d` when they reach the same things,
`∀i. (m R i ⟺ d S i)` — market `m` retails exactly what dish `d` specifies, no more and no less.

A meet of two long divisions, the second turned round by the converse frame:

#P(p-symmdiv, s: 66%)
#align(center, src[exported from the definition, not transcribed])

#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [$(frac(R, S))^circle.small = frac(S, R)$ \ #src[Matching is symmetric.]],
  P(p-sdiv-recip),

  [$frac(R, S) frac(S, W) ⊑ frac(R, W)$ \ #src[And transitive.]],
  P(p-sdiv-comp),
)

No pictures for the rest of §2.35: symmetric division is not built from the generators.

#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the market reading*]),

  [$X ⊑ frac(R, S) ⟺ X S ⊑ R$ and `X° R ⊑ S`],
  [`X` may pair `m` with `d` only when each fills the other. Both halves must typecheck, so the
   operation is *partial*.],

  [$frac(R, S) S ⊑ R$],
  [`m` matches `d` and `d` specifies `i`, so `m` retails `i`.],

  [$frac(R, R) R ⊑ R$],
  [The same with `R` against itself, market to market.],

  [$𝟙 ⊑ frac(R, R)$],
  [Every market matches itself.],

  [$(frac(R, R))^2 = frac(R, R)$],
  [So *matches* is an equivalence relation. Freyd writes `⊑`; with the row above it is an
   equality.],

  [$X ⊑ frac(R, R) ⟺ X R ⊑ R$, for symmetric `X`],
  [The largest symmetric arrow that leaves `R` alone.],

  [$frac(S, S) = 𝟙$, `S` is *straight*],
  [No two dishes specify the same ingredients. Equivalently every symmetric `X` with `X S ⊑ S` is
   coreflexive.],

  [`f S = g S ⟹ f = g`, `S` straight],
  [A straight `S` tells its dishes apart, so it cancels on the right.],

  [`S R` straight `⟹ S` straight],
  [If the longer chain tells them apart, the first step already does.],

  [`S` straight `⟺ R/S` simple for all `R`],
  [If no two dishes agree, at most one market can match a given dish.],

  [`R = h S`, `h` a cover, `S` straight],
  [In an effective division allegory every arrow factors that way.],

  [$frac(R, 𝟙)$ is the *simple part* of `R`],
  [The markets retailing one ingredient and nothing else. It equals `R` only when `R` is simple, unlike
   `R/𝟙 = R`.],

  [`Dom` $frac(R, S)$ `= 𝟙 ∩ (R/S)(S/R)`],
  [Its domain is the *domain of simplicity* of `R`.],
)

= Power allegories

One more operation on a division allegory: `∋`, Freyd's *epsiloff*. In `Rel` its source is the
powerset of its target and `l ∋ i` iff `i ∈ l` — the shopping lists over the ingredients, and `∋` reads a
list `l` back into the ingredients on it. Everything else is forced.

#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the market reading*]),

  [`∋ ⊤ = R ⊤`],
  [Same target as `R`, and depending on nothing else: one `∋` per object, not per arrow. What is
   being listed fixes it, not who lists it.],

  [$frac(∋, ∋) ⊑ 𝟙$, `∋` is *straight*],
  [*Extensionality*: two lists with the same ingredients are the same list.],

  [`𝟙 ⊑ (R/∋)(∋/R)`, `∋` is *thick*],
  [*Comprehension*: every market has a list of exactly what it retails. Equivalently every `R`
   factors as a map followed by `∋`.],

  [`Λ(R) ≜` $frac(R, ∋)$],
  [The list-of map: send a market to its list.],

  [`Λ(R)` is simple],
  [`∋` is straight, and dividing by a straight arrow is simple. At most one list per market.],

  [`Λ(R)` is entire `⟺ ∋` thick],
  [`Dom` $frac(R, ∋)$ `= 𝟙 ∩ (R/∋)(∋/R)`, the domain row above. At least one list per market, so
   `Λ(R)` is a *map*.],

  [`Λ(R) ∋ = R`],
  [Look up a market's list, then read off its ingredients: what it retails.],

  [`Λ(R)` is the only map with `Λ(R) ∋ = R`],
  [Two maps naming the same ingredients name the same list — extensionality again.],

  [`F ⊑ Λ(F ∋)`, `F` simple],
  [A partial choice of lists is inside the total one.],

  [`[α]` = source of `∋`, the *power-object*],
  [Every list over `α`.],

  [`{·} ≜ Λ(𝟙)`, the *singleton map*, monic],
  [The one-ingredient list. `Λ(𝟙)Λ°(𝟙) ⊑` $frac(𝟙, ∋) frac(∋, 𝟙) ⊑ frac(𝟙, 𝟙) ⊑ 𝟙$.],

  [`Λ(f) = f {·}`, `f` a map],
  [Rename first or take singletons first.],

  [`C` a topos `⟹ Rel(C)` a power allegory],
  [And back: a unitary tabular power allegory has `Map(A)` a topos. Extensionality and comprehension
   are all a topos adds.],
)
