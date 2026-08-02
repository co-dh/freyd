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
#import "generated/Freyd.Diag.meet_idem.proof.typ": branches as mib
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
#import "generated/Freyd.Diag.ClosedLinearBicat.«residual_comp_≤».typ": pic as p-residual
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

#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-meet-top, s: 60%) #v(-7pt) \ #src[*unit:* one half of `⊤` per end — the merge's unit law
   absorbs the `⟜`, the copy's counit law the `⊸`]],
  [#P(p-meet-comm, s: 60%) #v(-7pt) \ #src[*commutative:* `σ` crosses `R ⊗ S` by naturality and is
   absorbed by cocommutativity and commutativity]],
  [#P(p-meet-assoc, s: 44%) #v(-7pt) \ #src[*associative:* coassociativity and associativity; `⊗`
   re-brackets for nothing, being strict here]],
)

// Heading, chain and its paragraph kept together — `width: 100%` because a block sizes to its
// contents, and inside one that has shrunk the `align(center)` of `chain` has nothing to centre in.
#block(breakable: false, width: 100%)[
== `R ∩ R = R`, the one that is not bookkeeping

#chain(
  (mib.at(0).steps.at(0), mib.at(0).steps.at(1), mib.at(0).steps.at(2)),
  ([], [`◁ ▷ = 𝟙`], [lax copy]))

The last picture is `R ∩ R` itself, so this is `R ≤ R ∩ R` and the lax copy law is the whole of it.
The other direction is not proved here: `R ∩ S ≤ R` holds for every `S`, by weakening `S` to `⊤` and
then collapsing `R ∩ ⊤` — which is the paper's own remaining three steps, packaged once.
]

So `≤` is the order this monoid induces. `R ∩ S ≤ R` comes from the unit, and idempotency turns
anything under both `S` and `T` into something under `S ∩ T`, since `R = R ∩ R ≤ S ∩ T`.

= The eight axioms, and what proves each

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*axiom, and what supplies it*], [*picture*]),

  [`R (S ∩ T) ⊑ R S ∩ R T` — the lax copy law.], P(p-semidistrib),
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
= Union and residual

Both are past what the definition can build: a union needs a *biproduct* on top of the Frobenius
structure, a residual a *second composition* with linear adjoints. A union draws as a *tape* — the
rounded wrapper is the second product, and its fork and join open and close a branch a particle
takes exactly one of. A residual draws as *long division*, not as its own term, which is a
composition against a complement.

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
  [`(R / S) S ⊑ R` — the residual is a lower bound of the arrows it is the greatest of.],
  P(p-residual),
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
   #src[`F` = shops Ann may go to, `R` = has milk, `S` = has bread. Single valued means one shop, so
   the sides agree.]],
  grid(columns: 3, align: horizon, column-gutter: 10pt,
    [#P(p-236a, s: 74%) #v(-9pt) #align(center, src[one shop with both])],
    text(17pt)[=],
    [#P(p-236b, s: 74%) #v(-9pt) #align(center, src[milk at A, bread at B])],
  ),
)

// Its own page: the ten rows are one table and the long-division figure heads them, so a break
// inside would separate the metaphor from the laws it explains.
#pagebreak(weak: true)
= Division

#align(center, divbar(($R slash S$, "q"), ($S$, "d"), note: [the slack: `⊑`]))

// Two columns like every other table, one law per row.  The pictures here are the widest in the
// note — `le_div_iff` is a `⟺` between two containments, four sub-pictures in a row, 10.9cm before
// scaling — which is why the picture column gets the rest of the 22cm and the laws that used to
// share a row are split: one picture per row is what keeps them at readable size.
#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`T ⊑ R/S ⟺ T S ⊑ R`],
  P(p-le-div),

  [`T ⊑ S\R ⟺ S T ⊑ R`],
  P(p-le-ldiv),

  [`(R/S) S ⊑ R` \ #src[Strict at `S = ∅`: `R/S` is everything, `(R/S) S = ∅`.]],
  P(p-div-cancel),

  [`S (S\R) ⊑ R`],
  P(p-ldiv-cancel),

  [*associate:* `R/(S₁ S₂) = (R/S₂)/S₁`],
  divbar(($(R slash S_2) slash S_1$, "q"), ($S_1$, "d"), ($S_2$, "d"), qw: 4.2),

  [`(S T)\R = T\(S\R)`],
  divbar(($S$, "d"), ($T$, "d"), ($T backslash (S backslash R)$, "q"), qw: 4.2),

  [*maps:* `f (R/S) = (f R)/S` \ #src[The same three pieces bracketed two ways, which is the licence
   to write `f R / S`. The shunting rule.]],
  P(p-map-div),

  [`R/(f S) = (R/S) f°` \ #src[A map moves out of a denominator and reappears as `f°` outside the
   box. The shunting rule again.]],
  P(p-div-map),

  [*§2.314:* `(R/S)(S/T) ⊑ R/T`],
  P(p-div-comp),

  [`𝟙 ⊑ R/R` \ #src[`R` = shop `a` stocks `c`, so `R/R` = "`a` stocks all `a'` does", true of every
   shop. Strict: two shops stocking only milk contain each other and stay two shops.]],
  P(p-one-div),

  [`(R/R)(R/R) = R/R` \ #src[Freyd writes `⊑`, but with `𝟙 ⊑ R/R` above it is an equality:
   `R/R = 𝟙(R/R) ⊑ (R/R)(R/R)` is the other direction. A preorder is idempotent.]],
  P(p-div-self-idem),

  [`(R/R) R = R`],
  P(p-div-self),

  [`R/𝟙 = R`],
  P(p-div-one),

  [`R/(S₁ ∪ S₂) = R/S₁ ∩ R/S₂` \ #src[A denominator's union becomes a numerator's meet: dividing by
   more leaves less.]],
  P(p-div-union),

  [`S\(R/T) = (S\R)/T` \ #src[Which is why `S\R/T` needs no bracket.]],
  P(p-ldiv-div),
)

Fifteen laws, fifteen pictures, and not one shows a generator: `∩`, `∪`, `°` and composition are what
the Frobenius generators build, and `/` is none of those — it is posited, with nothing to unfold.

= Symmetric division

`R/ₛS ≜ (R/S) ∩ (S/R)°`, the two-sided quotient: everything `R` says about a column and everything
`S` says about it, in both directions.

#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`(R/ₛS)° = S/ₛR` \ #src[The meet is inside the definition, not the statement, so it stays under
   the label.]],
  P(p-sdiv-recip),

  [`(R/ₛS)(S/ₛT) ⊑ R/ₛT` \ #src[`/ₛ` is converse-symmetric and transitive, like an equality of
   columns.]],
  P(p-sdiv-comp),
)
