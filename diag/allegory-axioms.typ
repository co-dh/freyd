// The page setup and the cell helpers live in note-style.typ, shared with diag/allegory2.typ, which
// carries the PROOFS this note leaves out.
#import "note-style.typ": *
// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name.  See the header of strdiag.typ.
// `dot` is renamed on the way in for the same reason: it is Typst's math `dot`.
#import "strdiag.typ": conv, meet, wire, bend, gbox, dot as wiredot, tape, tape-fork, tape-join, TINT

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

// `lab` lives here, ahead of every note that draws by hand, because the domain picture just below is
// the first of them.
// `rot` turns a cell's `⊑` to point from the SMALLER path to the larger one.  Unrotated it reads
// left to right, which in a triangle or a square is the wrong axis: in the left triangle below the
// small side is the path over the top and the large one is `R` at the lower left, so the symbol has
// to point southwest.  Typst rotates clockwise, so southwest is 135°, southeast 45°, northwest
// −135°, northeast −45°.
#let lab(x, y, col, w, rot: 0deg) = d.content((x, y), rotate(rot, text(10pt, col)[#w]))
// The COLLAPSED domain: `R` ends in a `⊸`, so nothing `R` computes can leave, and what the upper
// strand carries out is the input itself — the coreflexive on the values `R` accepts.  Bound rather
// than drawn in place: it is the right-hand step of both chains below.  `rel` draws the chain's
// relation symbol at the picture's LEFT EDGE, since a `$=$` set beside a canvas sits on the canvas's
// baseline, not on its horizon.
#let domstr(rel: none) = cetz.canvas(length: 0.8cm, {
  let y = 0.85
  if rel != none { lab(-1.2, 0, black)[#rel] }
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (3.75, y))
  wire((1.55, -y), (1.9, -y)); gbox((1.9, -y), [R]); wire((2.82, -y), (3.3, -y))
  wiredot((3.3, -y))
  lab(-0.35, 0, black)[$A$]; lab(4.1, y, black)[$A$]
})

= Domain and range

#definition[
The *domain* `Dom R ≜ 𝟙 ∩ R R°` and the *range* `Ran R ≜ Dom R°`.
]

// THE MEET FIRST, then the stub.  The stub on its own does not look like `𝟙 ∩ R R°` — one strand
// carries no box at all and the return leg is gone — so the definition is drawn literally beside it
// and the collapse is what the chain shows.
#chain((cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (4.4, y))
  wire((1.55, -y), (1.7, -y)); gbox((1.7, -y), [R])
  wire((2.62, -y), (2.85, -y)); gbox((2.85, -y), [R], flip: true)
  wire((3.77, -y), (4.4, -y))
  bend((4.4, y), (5.05, 0), k: 0.4); bend((4.4, -y), (5.05, 0), k: 0.4); wiredot((5.05, 0))
  wire((5.05, 0), (5.6, 0))
  lab(-0.35, 0, black)[$A$]; lab(5.95, 0, black)[$A$]
}), domstr(rel: [$=$])),
  // Broken by hand: `chain` sizes its column to the hint, so an unbroken line of this length pushes
  // the two pictures a third of the page apart.
  ("", [`▷` lands the return leg back on the value `◁` handed out, \
   so `R° ▷` cuts to `⊸` — Frobenius]), s: 100%)

Running `R` and throwing the result away leaves only the fact that `R` could fire, and `Ran R` is the
same picture with the box mirrored. In `Rel` both steps are `{(a,a) : ∃b. a R b}`.

#align(center, table(
  columns: 1, inset: 9pt, stroke: 0.4pt + luma(190),

  [`Dom R ≜ 𝟙 ∩ R R°`],
  [`Dom R ⊑ A ⟺ R ⊑ A R`, for `A` coreflexive],
  [`Dom (R S) ⊑ Dom R`],
  [`Dom (R ∩ S) = 𝟙 ∩ S R°`],
  [`R` entire `⟺ Dom R = 𝟙 ⟺ 𝟙 ⊑ R R°`],
  [`R` simple `⟺ R° R ⊑ 𝟙`],
  [`R` a map `⟺ R` entire and simple],
  [`R, S` entire `⟹ R S` entire — likewise simple, likewise maps],
  [`R S` entire `⟹ R` entire],
))

== Sliding the discard

`Dom (R S) ⊑ Dom R`, and a single glyph for `Dom` would have nothing to slide: with the box and the
discard drawn apart, the law is one dot walking back along the lower strand.

#chain((cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (4.6, y))
  wire((1.55, -y), (1.7, -y)); gbox((1.7, -y), [R])
  wire((2.62, -y), (2.85, -y)); gbox((2.85, -y), [S])
  wire((3.77, -y), (4.15, -y)); wiredot((4.15, -y))
  lab(-0.35, 0, black)[$A$]; lab(4.95, y, black)[$A$]
}), domstr(rel: [`⊑`])),
  ("", [`S ⊸ ⊑ ⊸`, the lax axiom for `⊸` in the first section \
   — the discard slides back past `S`]), s: 100%)

Equality is `S` entire, which is the same picture read as `Dom R = 𝟙 ⟺ R` entire.

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
#align(center, `m's image contains d's pre image.`)

`R/S` relates a producer to a consumer when the producer supplies #emph[WHAT]
the consumer asks for. m' fills no dish, even it has everything the guest wants.

== `(R/S)(S/W) ⊑ R/W`

// ONE picture for the whole law.  A quotient is drawn as SUPPLY, an ingredient column, DEMAND, every
// arrow pointing at the ingredient it names; the reader then answers by eye — is every arrow into an
// ingredient from the demand side matched by one from the supply side? — and the answer is the arc.
// The three quotients share their columns: a dish demands from the market on its left and supplies
// the guest on its right, so the ingredient column is repeated, once per quotient.  Above the
// columns the two legs `R/S`, `S/W` meet over the dish that carries the composite; below them `R/W`
// spans the whole width in its own colour, and that it starts at BOTH markets while the path starts
// only at `m` is the strictness of the law, drawn.
// Colour marks WHICH node, not which column — the columns are already told apart by position, so
// spending a hue on them would leave nothing to tell `m` from `m'`.  First in a column blue, second
// pink, in every column.
#let PAL = (rgb("#1a5fb4"), rgb("#c2247f"))
#let ARC = rgb("#7d3c98")
#let RW = rgb("#26734d")
#let IY = (spice: 2.4, chicken: 0.8, peanut: -0.8, oil: -2.4)
// Nodes are drawn last, with a white fill, so an edge may start at the node's centre and let the box
// cover the stub — every edge then ends the same distance from its label, whatever its width.
#let node(x, y, c, w) = d.content((x, y), box(inset: 4pt, fill: white)[#text(10pt, c)[#w]])
// A column of nodes at x; a row is (y, label, the ingredients it names).
#let nodes(x, rows) = for (k, row) in rows.enumerate() { node(x, row.at(0), PAL.at(k), row.at(1)) }
#let ings(x) = for (it, y) in IY { node(x, y, black, [#it]) }
// Every arrow from column x into the ingredient column xi, stopping on the side it comes from.
#let edges(x, xi, rows) = {
  let dir = if x < xi { -1 } else { 1 }
  for (k, row) in rows.enumerate() { for it in row.at(2) {
    d.line((x, row.at(0)), (xi + 1.05 * dir, IY.at(it)), mark: (end: ">", scale: 0.5),
      stroke: 0.75pt + PAL.at(k)) } }
}
// `h` is where the control points sit; the label goes on the curve's own midpoint, which is where
// the cubic actually is (`0.75h` from the axis, not `h`) — a label placed at `h` floats off a deep
// arc.  `cx` shortens the horizontal reach of those controls: the smaller it is, the sooner the
// curve dives, which is how the bottom arcs clear the ingredient columns without going twice as deep.
#let arc(a, b, up, lab, col: ARC, h: 3.8, cx: 4) = {
  let (x0, y0) = (a.at(0), a.at(1) + 0.45 * up)
  let (x1, y1) = (b.at(0), b.at(1) + 0.45 * up)
  let c = (x1 - x0) / cx
  d.bezier((x0, y0), (x1, y1), (x0 + c, h * up), (x1 - c, h * up),
    mark: (end: ">", scale: 0.55), stroke: 0.9pt + col)
  d.content(((x0 + x1) / 2, 0.125 * y0 + 0.75 * h * up + 0.125 * y1),
    box(inset: 3pt, fill: white)[#text(9.5pt, col)[#lab]])
}
#let head(x, lab) = d.content((x, 3.9), text(9.5pt, luma(60))[#lab])
#let MKT = ((1.6, [market `m`], ("spice", "chicken", "peanut")),
            (-1.6, [market `m'`], ("spice", "chicken")))
#let DISH = ((1.6, [kung pao], ("spice", "chicken", "peanut")),
             (-1.6, [chilli chicken], ("spice", "chicken", "oil")))
#let GUEST = ((0, [guest `g`], ("spice", "chicken")),)

#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  edges(-9.6, -4.8, MKT); edges(0, -4.8, DISH); edges(0, 4.8, DISH); edges(9.6, 4.8, GUEST)
  arc((-9.6, 1.6), (-0.8, 1.6), 1, [`R/S` fills])
  arc((0.8, 1.6), (9.6, 0), 1, [`S/W` satisfies])
  arc((-9.6, 1.6), (9.6, 0), -1, [`R/W` feeds], col: RW, h: 5.4, cx: 8)
  arc((-9.6, -1.6), (9.6, 0), -1, [`R/W` feeds], col: RW, h: 7.0, cx: 8)
  nodes(-9.6, MKT); ings(-4.8); nodes(0, DISH); ings(4.8); nodes(9.6, GUEST)
  head(-9.6, [`R` retails — supply]); head(0, [`S` specifies — demand, then supply])
  head(9.6, [`W` takes — demand])
})))

// The whole of each quotient in one line of English, laid out as the law reads: the two legs of the
// path first, the arrow they are contained in last.
#align(center, block(inset: (top: 2pt), text(10.5pt)[
  `R/S` — market retails #emph[what] dish specifies #h(1.2cm)
  `S/W` — dish specifies #emph[what] guest takes \
  `R/W` — market retails #emph[what] guest takes
]))

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

= Relator

#definition[
Every hom-set of an allegory is a poset, so an allegory is a *locally posetal 2-category*: the 2-cell
from `R` to `S` IS `R ⊑ S`. A *relator* `F : 𝒞 ⟶ 𝒟` is a 2-functor between allegories:

  #align(center, block(inset: (y: 6pt))[
    #text(12.5pt)[`F 𝟙 = 𝟙` #h(1cm) `F(R S) = (F R)(F S)` #h(1cm) `R ⊑ S ⟹ F R ⊑ F S`]
  ])

Preserving `°` is *not* asked for — `°` is an identity-on-objects involution `𝒞ᵒᵖ ⟶ 𝒞`, no part of
the 2-category.
]

- For `f` a map, `F f` is a map and `F(f°) = (F f)°`.
- Over a *tabular* allegory a functor is a relator `⟺` it preserves `°`.
- A relator is fixed by what it does to maps.
- `F(R ∩ S) ⊑ (F R) ∩ (F S)`, and strictly.
- `F(X ∩ Y) = (F X) ∩ (F Y)` for `X, Y` coreflexive.
- `F(Dom R) = Dom(F R)` for `F` preserving `°`.

The *power relator* `P` — `x (P R) y ⟺ (∀a ∈ x. ∃b ∈ y. a R b) ∧ (∀b ∈ y. ∃a ∈ x. a R b)` — is where
the fourth is strict: for `R = {(a₁,b₁), (a₂,b₂)}` and `S = {(a₁,b₂), (a₂,b₁)}` the pair
`({a₁,a₂}, {b₁,b₂})` is in `P R ∩ P S`, while `R ∩ S = ∅`.

== The pairing `⟨R,S⟩`

#definition[
The *pairing* of `R : C ⟶ A` and `S : C ⟶ B` is `⟨R,S⟩ ≜ R π₁° ∩ S π₂°`, where `(π₁, π₂)` is the
tabulation of `⊤`.
]

#align(center, block(inset: (y: 6pt))[
  `⟨R,S⟩ π₁ = (Dom S) R` #h(1.4cm) `⟨R,S⟩ π₂ = (Dom R) S`
])

// TWO PICTURES OF ONE ARROW, side by side: Freyd's commutative diagram and this note's Frobenius
// string diagram.  Both are HAND-DRAWN — `./scripts/diag-export` walks a Lean TYPE, and `pair` lives
// in the allegory layer (`AOP/A5_2.lean`), not in the `diag/` bicategory the exporter draws.
// LAID OUT LEFT TO RIGHT, source at the left: every string diagram in this note runs that way, and
// two pictures of the same arrow that disagree about which way it flows cannot be read together.
// That is a quarter turn off the usual commutative-diagram habit of putting the product on top.
//
// `ar` pulls both ends back off the node centres: these edges carry ARROWHEADS, and a head drawn at a
// centre is buried under that node's own white box.  `s0`, `s1` are how far to stay clear at each end
// — 0.95 leaving a two-letter box like `A × B` sideways, 0.55 entering one from above or below.  Top
// level, not a `let` inside the canvas: the `R × S` figure below draws the same kind of edge.
#let ar(a, b, col, dash: none, s0: 0.45, s1: 0.45) = {
  let (dx, dy) = (b.at(0) - a.at(0), b.at(1) - a.at(1))
  let n = calc.sqrt(dx * dx + dy * dy)
  d.line((a.at(0) + s0 / n * dx, a.at(1) + s0 / n * dy),
    (b.at(0) - s1 / n * dx, b.at(1) - s1 / n * dy),
    mark: (end: ">", scale: 0.5), stroke: (thickness: 0.75pt, paint: col, dash: dash))
}
// `◁` then `R ⊗ S`: the copy dot is the whole difference between this picture and `R × S` below.
// Bound rather than drawn in place — it is also the last step of the collapse chain further down.
// `eq` draws the chain's `=` at the LEFT EDGE of the picture, the way `./scripts/diag-export` places
// it: a `$=$` set beside the canvas instead sits on the canvas's baseline, not on its horizon.
#let pairstr(eq: false) = cetz.canvas(length: 0.8cm, {
  let y = 0.85
  if eq { lab(-1.2, 0, black)[$=$] }
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (1.9, y)); wire((1.55, -y), (1.9, -y))
  gbox((1.9, y), [R]); gbox((1.9, -y), [S])
  wire((2.82, y), (3.4, y)); wire((2.82, -y), (3.4, -y))
  lab(-0.35, 0, black)[$C$]; lab(3.75, y, RW)[$A$]; lab(3.75, -y, ARC)[$B$]
})
#row((box(inset: (right: 18pt), cetz.canvas(length: 0.8cm, {
  let (C, A, B, P) = ((-3, 0), (0, 1.7), (0, -1.7), (3, 0))
  ar(C, A, RW); ar(C, B, ARC); ar(P, A, RW, s0: 0.75); ar(P, B, ARC, s0: 0.75)
  ar(C, P, PAL.at(0), dash: "dashed", s1: 0.95)
  lab(-1.75, 1.12, RW)[`R`]; lab(-1.75, -1.12, ARC)[`S`]
  lab(1.8, 1.12, RW)[`π₁`]; lab(1.8, -1.12, ARC)[`π₂`]
  lab(-1.0, 0.32, PAL.at(0))[$chevron.l R, S chevron.r$]
  lab(1.1, 0.5, PAL.at(1), rot: -135deg)[`⊑`]; lab(1.1, -0.5, PAL.at(1), rot: 135deg)[`⊑`]
  node(C.at(0), C.at(1), black, $C$)
  node(A.at(0), A.at(1), RW, $A$); node(B.at(0), B.at(1), ARC, $B$)
  node(P.at(0), P.at(1), PAL.at(0), $A times B$)
})), pairstr()))

A domain is coreflexive, so `⟨R,S⟩ π₁ ⊑ R`, with equality exactly when `S` is entire; for maps both
triangles commute and `⟨f,g⟩` is unique. In `Rel`, `c ⟨R,S⟩ (a,b)` iff `c R a` and `c S b` — copy `c`, then
`R` on one strand and `S` on the other, which is `◁ (R ⊗ S)` on the right.

No `°` survives the translation. `π₁ = 𝟙 ⊗ ⊸` discards the second component, so `π₁° = 𝟙 ⊗ ⟜`
*creates* one out of nothing, and `∩` is copy, run both, merge. Draw that and the created strands —
the two dots with no left end, and the crossing they force — are merged against real ones, which is
the monoid's unit law:

// The chain at FULL size: `chain`'s 62% is calibrated for the exported pictures, which are drawn on a
// bigger canvas than these two.
#chain((cetz.canvas(length: 0.8cm, {
  wire((0, 0), (0.8, 0)); wiredot((0.8, 0))
  bend((0.8, 0), (1.4, 1.5)); bend((0.8, 0), (1.4, -1.5))
  wire((1.4, 1.5), (1.6, 1.5)); gbox((1.6, 1.5), [R]); wire((2.52, 1.5), (3.3, 1.5))
  wire((1.4, -1.5), (1.6, -1.5)); gbox((1.6, -1.5), [S]); wire((2.52, -1.5), (3.3, -1.5))
  // `⟜` has no input, so these two strands simply begin — that is what a converse of a projection is.
  wiredot((2.1, 0.5)); wire((2.1, 0.5), (3.3, 0.5))
  wiredot((2.1, -0.5)); wire((2.1, -0.5), (3.3, -0.5))
  bend((3.3, 1.5), (4.4, 0.85), k: 0.4); bend((3.3, -0.5), (4.4, 0.85), k: 0.4); wiredot((4.4, 0.85))
  bend((3.3, 0.5), (4.4, -0.85), k: 0.4); bend((3.3, -1.5), (4.4, -0.85), k: 0.4)
  wiredot((4.4, -0.85))
  wire((4.4, 0.85), (5.0, 0.85)); wire((4.4, -0.85), (5.0, -0.85))
  lab(-0.35, 0, black)[$C$]; lab(5.35, 0.85, RW)[$A$]; lab(5.35, -0.85, ARC)[$B$]
}), pairstr(eq: true)), ("", [`⟜ ▷ = 𝟙` on each half]), s: 100%)


== The relational product `R × S`

#definition[
`R × S ≜ ⟨π₁ R, π₂ S⟩`, a relator in each argument but no longer a categorical product.
]

// The same pair of pictures with `C` replaced by `C × D`, once per projection: the two triangles
// become two squares, and the copy dot goes away — `R × S` is the two strands side by side.
#row((box(inset: (right: 18pt), cetz.canvas(length: 0.8cm, {
  let (C, CD, D) = ((-2.7, 1.7), (-2.7, 0), (-2.7, -1.7))
  let (A, AB, B) = ((2.7, 1.7), (2.7, 0), (2.7, -1.7))
  ar(CD, C, RW, s0: 0.55); ar(CD, D, ARC, s0: 0.55)
  ar(AB, A, RW, s0: 0.55); ar(AB, B, ARC, s0: 0.55)
  ar(C, A, RW); ar(D, B, ARC)
  ar(CD, AB, PAL.at(0), dash: "dashed", s0: 0.95, s1: 0.95)
  lab(-3.1, 0.85, RW)[`π₁`]; lab(-3.1, -0.85, ARC)[`π₂`]
  lab(3.1, 0.85, RW)[`π₁`]; lab(3.1, -0.85, ARC)[`π₂`]
  lab(0, 2.0, RW)[`R`]; lab(0, -1.4, ARC)[`S`]
  lab(-1.2, 0.32, PAL.at(0))[$R times S$]
  lab(1.2, 0.85, PAL.at(1), rot: -135deg)[`⊑`]; lab(1.2, -0.85, PAL.at(1), rot: 135deg)[`⊑`]
  node(C.at(0), C.at(1), RW, $C$); node(D.at(0), D.at(1), ARC, $D$)
  node(CD.at(0), CD.at(1), PAL.at(0), $C times D$)
  node(A.at(0), A.at(1), RW, $A$); node(B.at(0), B.at(1), ARC, $B$)
  node(AB.at(0), AB.at(1), PAL.at(0), $A times B$)
})), cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, y), (0.5, y)); gbox((0.5, y), [R]); wire((1.42, y), (2.0, y))
  wire((0, -y), (0.5, -y)); gbox((0.5, -y), [S]); wire((1.42, -y), (2.0, -y))
  lab(-0.35, y, RW)[$C$]; lab(-0.35, -y, ARC)[$D$]
  lab(2.35, y, RW)[$A$]; lab(2.35, -y, ARC)[$B$]
})))

Right-then-up is `(R × S) π₁`, up-then-right is `π₁ R`, and `(R × S) π₁ ⊑ π₁ R`, equality when `S` is
entire. In `Rel`, `(c,d) (R × S) (a,b)` iff `c R a` and `d S b` — two strands side by side, no copy
dot: `R × S = R ⊗ S`.

== Absorption

For `X : E ⟶ C` and `Y : E ⟶ D`, `⟨X,Y⟩ (R × S) = ⟨X R, Y S⟩`. Both sides are this picture:

// ONE picture, not two with an `=`: pushing `R ⊗ S` past `X ⊗ Y` is the interchange law, which the
// notation has already spent — the two sides are drawn by the same strokes, so a second copy of the
// picture would say nothing.  This is the whole of B&dM's (5.3), whose direct proof needs two
// auxiliary special cases.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (1.9, y)); wire((1.55, -y), (1.9, -y))
  gbox((1.9, y), [X]); gbox((1.9, -y), [Y])
  wire((2.82, y), (3.2, y)); wire((2.82, -y), (3.2, -y))
  gbox((3.2, y), [R]); gbox((3.2, -y), [S])
  wire((4.12, y), (4.7, y)); wire((4.12, -y), (4.7, -y))
  lab(-0.35, 0, black)[$E$]; lab(5.05, y, RW)[$A$]; lab(5.05, -y, ARC)[$B$]
})))

== The coproduct `[R,S]`

The injections `ιₗ : A ⟶ A + B` and `ιᵣ : B ⟶ A + B` are maps, and the coproduct they make of the maps
stays a coproduct once every arrow is allowed: both equations hold on the nose and `[R,S]` is the only
arrow satisfying them, with none of the `Dom` slack `⟨R,S⟩` carries.

// THE DEFINITION, DRAWN — and it needs no new generator.  `+` shares none of `◁ ▷ ⊸ ⟜`, but it does
// not have to: the definition is a UNION, and the union is already drawn, as the tape of the laws
// above.  So the one picture this subsection gets is the one line the other rows are calculated from;
// the rest stay formulas, which read as written.
#align(center, box(inset: (y: 8pt), cetz.canvas(length: 0.8cm, {
  let y = 0.62                    // the tape's two branches, at the exported pictures' half-spacing
  wire((0, 0), (0.34, 0))
  tape((0.34, -1.14), (3.80, 1.14))
  tape-fork((0.56, 0), sp: y, len: 0.42)
  // Mirrored and tinted: this file draws a converse by flipping the box, so these are `ιₗ°` and `ιᵣ°`.
  gbox((0.98, y), [`ιₗ`], flip: true, fill: TINT); wire((1.90, y), (2.24, y)); gbox((2.24, y), [R])
  gbox((0.98, -y), [`ιᵣ`], flip: true, fill: TINT); wire((1.90, -y), (2.24, -y)); gbox((2.24, -y), [S])
  tape-join((3.58, 0), sp: y, len: 0.42)
  wire((3.80, 0), (4.14, 0))
  lab(-0.9, 0, black)[$A + B$]; lab(4.49, 0, black)[$C$]
})))

The tape is the union — a particle entering at `A + B` takes exactly one branch — and the two mirrored
boxes are what makes the branches disjoint.

#align(center, table(
  columns: 1, inset: 9pt, stroke: 0.4pt + luma(190),

  [`[R,S] ≜ ιₗ° R ∪ ιᵣ° S`],
  [`ιₗ [R,S] = R`, `ιᵣ [R,S] = S`, and `[R,S]` is the only such arrow],
  [`R + S ≜ [R ιₗ, S ιᵣ]`],
  [`ιₗ ιₗ° = 𝟙 = ιᵣ ιᵣ°`],
  [`ιₗ ιᵣ° = ⊥ = ιᵣ ιₗ°`],
  [`ιₗ° ιₗ ∪ ιᵣ° ιᵣ = 𝟙`],
  [`[U,V]° [R,S] = U° R ∪ V° S`],
))
