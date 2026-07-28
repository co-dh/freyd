// Imported by name, not with `*`: `delta`, `nabla`, `cap`, `cup` and `dot` shadow the Typst math
// symbols of the same name.  See the header of strdiag.typ.
#import "strdiag.typ": cetz, d, conv, meet

// EVERY PICTURE OF A THEOREM BELOW IS EXPORTED, NOT DRAWN.  `./scripts/diag-export <decl>` walks the
// Lean declaration's TYPE and writes diag/generated/<decl>.typ, which binds the cetz drawing to
// `pic`; this note only places those bindings in table cells.  Hand-drawing them is how the first
// draft of this page got `inter_assoc` wrong — it showed coassociativity of `Δ` instead of the axiom
// — and dropped the `=` from `recip_inter`.  A picture derived from the statement cannot drift from
// it.  Regenerate every binding used here with:
//
//   ./scripts/diag-export Freyd.Diag.CartBicat.Δ_assoc Freyd.Diag.CartBicat.Δ_comm \
//     Freyd.Diag.CartBicat.Δ_counit Freyd.Diag.CartBicat.«∇_assoc» Freyd.Diag.CartBicat.«∇_comm» \
//     Freyd.Diag.CartBicat.«∇_unit» \
//     Freyd.Diag.CartBicat.conv_conv Freyd.Diag.CartBicat.conv_comp \
//     Freyd.Diag.conv_inter Freyd.Diag.meet_idem Freyd.Diag.meet_comm Freyd.Diag.meet_assoc \
//     Freyd.Diag.semidistrib_of_lax Freyd.Diag.modular_of_frobenius Freyd.Diag.«≤_top» \
//     Freyd.Diag.CartBicat.special Freyd.Diag.CartBicat.«∇Δ≤𝟙» Freyd.Diag.CartBicat.«𝟙≤Δ∇» \
//     Freyd.Diag.CartBicat.«?!≤𝟙» Freyd.Diag.CartBicat.«𝟙≤!?» Freyd.Diag.CartBicat.frob_left \
//     Freyd.Diag.CartBicat.lax_Δ Freyd.Diag.CartBicat.lax_! Freyd.Diag.Biprod.«≤_union_left» \
//     Freyd.Diag.Biprod.union_comm Freyd.Diag.Biprod.bot_union Freyd.Diag.Biprod.comp_union \
//     Freyd.Diag.Biprod.conv_union Freyd.Diag.FbCbRig.meet_union_distrib \
//     Freyd.Diag.ClosedLinearBicat.«residual_comp_≤» Freyd.Diag.SingleValued Freyd.Diag.Total \
//     Freyd.Diag.Injective Freyd.Diag.Surjective Freyd.Diag.ineq_SV Freyd.Diag.ineq_TOT \
//     Freyd.Diag.ineq_INJ Freyd.Diag.ineq_SUR Freyd.Diag.shunt_right Freyd.Diag.shunt_left \
//     Freyd.Diag.entire_inter_iff Freyd.Diag.CartBicat.«∇_slide_conv»
// and, for the last section, the ALLEGORY layer's division and negation:
//   ./scripts/diag-export Freyd.Alg.le_div_iff Freyd.Alg.le_leftDiv_iff \
//     Freyd.Alg.DivisionAllegory.div_comp_le Freyd.Alg.leftDiv_comp_le Freyd.Alg.div_comp_assoc \
//     Freyd.Alg.leftDiv_comp Freyd.Alg.map_comp_div Freyd.Alg.div_comp_recip_map \
//     Freyd.Alg.symmDiv_recip Freyd.Alg.symmDiv_comp Freyd.Alg.inter_neg_zero \
//     Freyd.Alg.neg_union Freyd.Alg.neg_inter Freyd.Alg.union_neg_eq_top \
//     Freyd.Alg.le_iff_inter_neg_zero Freyd.Alg.schroeder_left Freyd.Alg.schroeder_right \
//     Freyd.Alg.neg_div Freyd.Alg.div_eq_neg_comp Freyd.Alg.topHom_thenRel \
//     Freyd.Alg.RelSet.galoisPF
// and the PROOF chains:
//   ./scripts/diag-export Freyd.Diag.CartBicat.conv_slide
//   ./scripts/diag-export --proof Freyd.Diag.CartBicat.conv_comp Freyd.Diag.shunt_right \
//     Freyd.Diag.shunt_left Freyd.Diag.CartBicat.«∇_slide_conv» \
//     Freyd.Diag.modular_of_frobenius Freyd.Diag.entire_inter_iff
#import "generated/Freyd.Diag.CartBicat.conv_conv.typ": pic as p-conv-conv
#import "generated/Freyd.Diag.CartBicat.conv_comp.typ": pic as p-conv-comp
#import "generated/Freyd.Diag.conv_inter.typ": pic as p-conv-inter
#import "generated/Freyd.Diag.meet_idem.typ": pic as p-meet-idem
#import "generated/Freyd.Diag.meet_comm.typ": pic as p-meet-comm
#import "generated/Freyd.Diag.meet_assoc.typ": pic as p-meet-assoc
#import "generated/Freyd.Diag.semidistrib_of_lax.typ": pic as p-semidistrib
#import "generated/Freyd.Diag.modular_of_frobenius.typ": pic as p-modular
#import "generated/Freyd.Diag.«≤_top».typ": pic as p-le-top
#import "generated/Freyd.Diag.CartBicat.special.typ": pic as p-special
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
#import "generated/Freyd.Diag.CartBicat.frob_left.typ": pic as p-frob
#import "generated/Freyd.Diag.CartBicat.lax_Δ.typ": pic as p-lax-delta
#import "generated/Freyd.Diag.CartBicat.lax_!.typ": pic as p-lax-bang
#import "generated/Freyd.Diag.Biprod.«≤_union_left».typ": pic as p-union-left
#import "generated/Freyd.Diag.Biprod.union_comm.typ": pic as p-union-comm
#import "generated/Freyd.Diag.Biprod.bot_union.typ": pic as p-bot-union
#import "generated/Freyd.Diag.Biprod.comp_union.typ": pic as p-comp-union
#import "generated/Freyd.Diag.Biprod.conv_union.typ": pic as p-conv-union
#import "generated/Freyd.Diag.FbCbRig.meet_union_distrib.typ": pic as p-distrib
#import "generated/Freyd.Diag.ClosedLinearBicat.«residual_comp_≤».typ": pic as p-residual
#import "generated/Freyd.Diag.CartBicat.conv_comp.proof.typ": branches as l42b
#import "generated/Freyd.Diag.shunt_right.proof.typ": branches as srb
#import "generated/Freyd.Diag.shunt_left.proof.typ": branches as slb
#import "generated/Freyd.Diag.CartBicat.«∇_slide_conv».proof.typ": branches as nsb
#import "generated/Freyd.Diag.modular_of_frobenius.proof.typ": branches as mfb
#import "generated/Freyd.Diag.CartBicat.conv_slide.typ": pic as p-conv-slide
#import "generated/Freyd.Diag.CartBicat.«∇_slide_conv».typ": pic as p-nabla-slide
#import "generated/Freyd.Diag.SingleValued.typ": pic as p-sv46
#import "generated/Freyd.Diag.Total.typ": pic as p-tot47
#import "generated/Freyd.Diag.Injective.typ": pic as p-inj48
#import "generated/Freyd.Diag.Surjective.typ": pic as p-sur49
#import "generated/Freyd.Diag.ineq_SV.typ": pic as p-sv
#import "generated/Freyd.Diag.ineq_TOT.typ": pic as p-tot
#import "generated/Freyd.Diag.ineq_INJ.typ": pic as p-inj
#import "generated/Freyd.Diag.ineq_SUR.typ": pic as p-sur
#import "generated/Freyd.Diag.shunt_right.typ": lhs as sr-a, rhs as sr-b
#import "generated/Freyd.Diag.shunt_left.typ": lhs as sl-a, rhs as sl-b
#import "generated/Freyd.Diag.entire_inter_iff.typ": pic as p-entire, lhs as ent-a, rhs as ent-b
#import "generated/Freyd.Diag.entire_inter_iff.proof.typ": branches as entb
// The allegory layer's §4.4–4.5 (last section).  `Freyd.Alg`, not `Freyd.Diag`: division and
// negation are theorems of `Freyd/S2_30.lean` and `AOP/A4_4`–`A4_5`, and of nothing in `diag/`.
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
#import "generated/Freyd.Alg.inter_neg_zero.typ": pic as p-neg-contra
#import "generated/Freyd.Alg.neg_union.typ": pic as p-neg-union
#import "generated/Freyd.Alg.neg_inter.typ": pic as p-neg-inter
#import "generated/Freyd.Alg.union_neg_eq_top.typ": pic as p-neg-excl
#import "generated/Freyd.Alg.le_iff_inter_neg_zero.typ": pic as p-le-neg
#import "generated/Freyd.Alg.schroeder_left.typ": pic as p-schroeder-l
#import "generated/Freyd.Alg.schroeder_right.typ": pic as p-schroeder-r
#import "generated/Freyd.Alg.neg_div.typ": pic as p-neg-div
#import "generated/Freyd.Alg.div_eq_neg_comp.typ": pic as p-div-neg
#import "generated/Freyd.Alg.topHom_thenRel.typ": pic as p-lex
#import "generated/Freyd.Alg.RelSet.galoisPF.typ": pic as p-galois

#set page(width: 25cm, height: auto, margin: 1.5cm)
#set text(size: 11.5pt)
#set par(justify: true)
#show raw: set text(size: 9.6pt)
#show heading: set block(above: 16pt, below: 9pt)
#set heading(numbering: "1.")
// Justification inside a table cell stretches the spaces around long unbreakable monospace runs
// (`Freyd.Diag.ClosedLinearBicat.«residual_comp_≤»`) into gaps you can drive a car through.
#show table: set par(justify: false)

#let src(s) = text(9.2pt, luma(105))[#s]
/// An exported picture, shrunk to fit a table cell.  `reflow` so the cell measures the shrunk size.
#let P(p, s: 92%) = align(center, box(inset: (y: 5pt), scale(x: s, y: s, reflow: true, p)))
/// A picture set INLINE in a table header, naming the statement the chain proves.  Deliberately
/// large: the header is the one row every reader looks at first, and at running-text size the
/// theorem it states cannot be read at all.
#let Pin(p, s: 70%) = box(baseline: 36%, scale(x: s, y: s, reflow: true, p))
/// A chain table's top header row: the theorem, one size up from the body.
#let Th(body) = table.cell(colspan: 3, text(12.5pt)[#body])
/// A figure transcribed from the paper by hand — used only where there is no Lean STATEMENT to
/// export, i.e. for the two primitive operations.
#let fig(body) = align(center, box(inset: (y: 5pt), cetz.canvas(length: 0.78cm, body)))

#align(center)[
  #text(16pt)[*The allegory axioms, and what defines them in the Frobenius calculus*] \
  #src[Freyd, _Categories, Allegories_ §2.11–§2.112 against
  `functorialSemanticsForRelationalTheories.pdf` Def. 4.1 \
  Lean: `Freyd/S2_10.lean` (`Allegory`), `diag/CB.lean` (`CartBicat`),
  `diag/CB_Allegory.lean` (`allegoryOfCartBicat`)]
]

#align(center, block(width: 90%, inset: (y: 4pt))[
  #src[*Where the pictures come from.* Every picture of a theorem is emitted by
  `./scripts/diag-export` from that theorem's Lean type. Nothing about a statement is redrawn here.
  The two figures marked _transcribed_ are the exception: they copy the paper's definition pictures,
  and a definition has no statement to export.]
])

#align(center, block(width: 90%, inset: (y: 4pt))[
  #src[*Equation numbering.* The numbers below are the 2017 preprint's. The `CartBicat`
  fields no longer encode them — a field is named for what it says, `«∇Δ≤𝟙»` rather than
  `ineq_37` — and each docstring carries the preprint number. The repo's copy of the paper is now
  the published version — Poly. J. Math. *2* (6), 20 Oct 2025, doi:10.69763/polyjmath.2.6 — which
  renumbers. Translation, published ← preprint: (34)←(37), (35)←(38), (36)←(39), (37)←(40),
  (38)←(41), (39)←(42), (40)←(43), (33)←(35), and Example 2.3(c)'s (13),(14)←(11),(12); the
  preprint's (36) is unnumbered there. Pages: Def. 4.1 at 20–21 (was 17), the `†` notation at 21
  (was 19), Lemma 4.2 at 21–22 (was 19). Renumbering the Lean fields is a separate decision and has
  not been made.]
])

#v(3pt)

Freyd's allegory takes reciprocation `°` and intersection `∩` as *primitive operations* and lists
eight *equational axioms* on them. A cartesian bicategory of relations takes neither: every object
carries one special Frobenius structure `Δ`, `!`, `∇`, `?`, the hom-order `≤` is primitive, and both
`°` and `∩` are *defined* from the four dots. Every one of Freyd's eight axioms is then a theorem.
The table below is that dictionary, one row per axiom.

Reading the pictures: left to right is composition — the book's diagram order, `R S` means first `R`
then `S` — vertical stacking is `⊗`, a bare wire is an identity, a white box is a relation, and a
box that is mirrored and tinted is its converse — the mirroring is the paper's own notation, the
tint is this note's, because at a glance a chamfer is easy to miss. The label inside is *not*
mirrored: the paper can reverse a single letter and still be read, a whole term like `R ∪ S` cannot. All four dots are solid, as Def. 4.1 draws them. The exporter draws a meet or a converse
as a *labelled* block, so a composite under a `°` appears as a single box reading `R ; S`; a `⊗`
draws as two stacked runs; and any subterm with no shape in this calculus — an associator, say —
degrades to an opaque box. The term columns write the converse `R°`, Freyd's symbol, where the paper
writes `R†`: these terms are read against the book throughout, and one symbol per idea beats asking
the reader to match two. The Lean sources write `R°` as well. The paper reserves `(−)°` for the
colour swap of its §7, but §7 is a worked example in other models — see the caution at the end of
this note — and nothing here formalises it, so in a repo that is `Rel(Set)` throughout there is no
clash to protect against.

In a chain table the symbol at the head of each row is the relation *that step was proved at*: `=`
for a reshaping, `≤` for a genuine inequality. Counting them is the point of drawing a proof at all
— a chain of one `≤` between equalities says the theorem is one law and a lot of bookkeeping.

= Definition 4.1, as the paper states it

#src[`functorialSemanticsForRelationalTheories.pdf` Def. 4.1, pp. 20–21 — transcribed here as
`class CartBicat` (`diag/CB.lean`), field for field. Every picture below is exported from the Lean
field, so the class and the definition cannot drift apart.]

A *cartesian bicategory of relations* is a poset-enriched category, symmetric monoidal, satisfying
four conditions. Clauses 1 and 2 are the two structures every object carries; clause 3 makes each
the other's adjoint and imposes Frobenius; clause 4 is the only condition on arrows.

The tower this note describes is STRICT: the two bracketings of a threefold product are the same
object, so no associator or unitor appears in any picture. The coherence arrows the paper suppresses
in its own diagrams are absent here because they do not exist.

== Every object carries a cocommutative comonoid `(Δ, !)`

#table(
  columns: (1fr, 5.6cm),
  align: (center + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  P(p-d-assoc, s: 84%), [(8) *coassociativity* \ #src[`CartBicat.Δ_assoc` — copying twice on the
   left is copying twice on the right.]],
  P(p-d-comm, s: 84%), [(9) *cocommutativity* \ #src[`CartBicat.Δ_comm` — the two copies are
   interchangeable.]],
  P(p-d-counit, s: 84%), [(10) *counit* \ #src[`CartBicat.Δ_counit` — copy, then discard one
   copy, and nothing has happened.]],
)

== Every object carries a commutative monoid `(∇, ?)`

#table(
  columns: (1fr, 5.6cm),
  align: (center + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  P(p-n-assoc, s: 84%), [(5) *associativity* \ #src[`CartBicat.«∇_assoc»`.]],
  P(p-n-comm, s: 84%), [(6) *commutativity* \ #src[`CartBicat.«∇_comm»`.]],
  P(p-n-unit, s: 84%), [(7) *unit* \ #src[`CartBicat.«∇_unit»` — create, then merge, and nothing
   has happened.]],
)

== Five inequations relate the monoid and the comonoid

#table(
  columns: (1fr, 5.6cm),
  align: (center + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  P(p-37, s: 84%), [(37) `∇ ; Δ ≤ 𝟙` #src[— half of `Δ ⊣ ∇`]],
  P(p-38, s: 84%), [(38) `𝟙 ≤ Δ ; ∇` #src[— the other half]],
  P(p-39, s: 84%), [(39) `? ; ! ≤ 𝟙` #src[— half of `! ⊣ ?`]],
  P(p-40, s: 84%), [(40) `𝟙 ≤ ! ; ?` #src[— the other half]],
  P(p-frob, s: 72%), [(41) the *Frobenius* law \ #src[`CartBicat.frob_left`, and its mirror
   `frob_right`. This is the one equation of the group; the other four are inequalities.]],
)

The *special* law `Δ ; ∇ = 𝟙` is NOT part of the definition. The paper derives it — "one direction
is given by (38) and the other is proved as follows" — and so does the Lean, as
`Freyd.Diag.CartBicat.special`; its picture is in the correspondence table below.

== Every arrow is a lax comonoid homomorphism

#table(
  columns: (1fr, 5.6cm),
  align: (center + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  P(p-lax-delta, s: 84%), [(42) `R ; Δ ≤ Δ ; (R ⊗ R)` \ #src[`CartBicat.lax_Δ` — running `R` once
   and copying is below copying and running it on both strands.]],
  P(p-lax-bang, s: 84%), [(43) `R ; ! ≤ !` \ #src[`CartBicat.lax_!`.]],
)

Read as inequalities in one direction only: an arrow that satisfied these as EQUATIONS would be a
map, and the whole point is that a general relation is not.

= Freyd's primitives are the Frobenius calculus's definitions

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*Freyd's primitive, and what defines it here*], [*picture*]),

  [*reciprocation* `R°` — §2.11, primitive. Here `conv R := bend ((R ⊗ 𝟙) ; cap)`
   (`diag/CB.lean:223`), not a generator. \ #src[Input arrives bottom left and runs under `R`; the
   *cup* `? ; Δ` at the top left creates a pair, one strand feeding `R` and the other leaving as the
   output at the top right; the *cap* `∇ ; !` at the bottom right annihilates `R`'s output against
   the input. It is the cup and the cap that reverse the arrow — a wire merely bumped up over the
   box and back down is an isotopy of `R` itself.]],
  fig({ conv((0, -0.80), $R$) }) + align(center, src[transcribed]),

  [*intersection* `R ∩ S` — §2.11, primitive. Here the convolution `meet R S := Δ ; (R ⊗ S) ; ∇`
   (`diag/CB_Derived.lean:24`). \ #src[Copy the input, run both, merge; the merge forces the two
   results to agree.]],
  fig({ meet((0, 0), $R$, $S$) }) + align(center, src[transcribed]),

  [*containment* `R ⊑ S` — §2.11, *defined* as `R ∩ S = R`. Here the poset-enrichment `≤` is
   primitive and `∩` is derived, so the two directions are swapped. \
   #src[`meet_eq_left_of_le` (`diag/CB_Derived.lean:196`) is the bridge.]],
  align(center, src[no picture — this is the 2-cell itself]),

  [*maximal morphism* `⊤` — §2.15, and Freyd needs a *unitary* allegory for it. Here
   `top a b := ! ; ?` (`diag/CB_Derived.lean:28`) is free in Def. 4.1. \
   #src[`Freyd.Diag.«≤_top»`.]],
  P(p-le-top),
)

= The eight axioms, and what proves each

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*Freyd's axiom, and what supplies it*], [*picture, from the Lean statement*]),

  [`(R°)° = R` — §2.11 `recip_recip`; here the *snake*, from (41). \
   #src[`Freyd.Diag.CartBicat.conv_conv`. Bending down and back up straightens out, so bending twice
   is the identity.]],
  P(p-conv-conv),

  [`(R S)° = S° R°` — §2.11 `recip_comp`; here mirroring the picture. \
   #src[`Freyd.Diag.CartBicat.conv_comp`. Reflecting a chain left to right reverses it; each box
   comes back flipped.]],
  P(p-conv-comp),

  [`(R ∩ S)° = R° ∩ S°` — §2.11 `recip_inter`; the same mirroring. \
   #src[`Freyd.Diag.conv_inter`. `Δ` and `∇` are each other's mirror image, so reflecting the
   convolution leaves its shape alone and only turns the boxes round.]],
  P(p-conv-inter),

  [`R ∩ R = R` — §2.11 `inter_idem`; here (42) and the *special* law. \
   #src[`Freyd.Diag.meet_idem`. Copy, run `R` twice, merge — (42) pushes `R` back through the copy
   and `Δ ; ∇ = 𝟙` closes the bubble.]],
  P(p-meet-idem),

  [`R ∩ S = S ∩ R` — §2.11 `inter_comm`; here cocommutativity (9) and commutativity (6). \
   #src[`Freyd.Diag.meet_comm`. The two strands of `Δ` are interchangeable, and so are those of
   `∇`.]],
  P(p-meet-comm),

  [`R ∩ (S ∩ T) = (R ∩ S) ∩ T` — §2.11 `inter_assoc`; here coassociativity (8) and associativity
   (5). \ #src[`Freyd.Diag.meet_assoc`. Either bracketing builds the same three-way copy tree, and
   dually the same merge tree.]],
  P(p-meet-assoc, s: 70%),

  [*semi-distributivity* `R (S ∩ T) ⊑ R S ∩ R T` — §2.11 `semidistrib`, §2.136; here (42), the *lax
   comonoid* inequation. \ #src[`Freyd.Diag.semidistrib_of_lax`. Running `R` and then copying is
   below copying and then running `R` on each strand.]],
  P(p-semidistrib),

  [*modular identity* `R S ∩ T ⊑ (R ∩ T S°) S` — §2.112 `modular`, the axiom Freyd *adjoins*: "we
   adjoin one more containment, the law of modularity". Here (41) and (42), *derived*. \
   #src[`Freyd.Diag.modular_of_frobenius`. Strip the shared prefix `Δ ; (R ⊗ T)` off both sides and
   what is left is `«∇_slide_conv»` (`diag/CB.lean:560`) — a box slides through a merge at the
   cost of its converse on the other strand.]],
  P(p-modular),
)

= The other direction: what each law of Def. 4.1 says in Freyd's language

// One size down: the declaration names here (`Freyd.Diag.CartBicat.special`) are unbreakable
// monospace words that overrun the middle column at 8.5pt and print over the next one.
#[
#show raw: set text(size: 8.4pt)
#table(
  columns: (8.8cm, 5.0cm, 1fr),
  align: (center + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*picture, from the Lean statement*], [*Def. 4.1*], [*Freyd*]),

  P(p-37, s: 88%), [(37) `∇ ; Δ ≤ 𝟙` \ #src[half of `Δ ⊣ ∇`]],
  [`Δ° Δ ⊑ 1` — *`Δ` is simple* \ #src[§2.13. Not used anywhere in the bridge; see below.]],

  P(p-38, s: 88%), [(38) `𝟙 ≤ Δ ; ∇` \ #src[the other half of `Δ ⊣ ∇`]],
  [`1 ⊑ Δ Δ°` — *`Δ` is entire* \ #src[§2.13; with (37), `Δ` is a *map*.]],

  P(p-39, s: 88%), [(39) `? ; ! ≤ 𝟙` \ #src[half of `! ⊣ ?`]],
  [`!° ! ⊑ 1` — *`!` is simple* \ #src[§2.13. Also unused in the bridge.]],

  P(p-40, s: 88%), [(40) `𝟙 ≤ ! ; ?` \ #src[the other half of `! ⊣ ?`]],
  [`1 ⊑ ! !°` — *`!` is entire* \ #src[§2.13; with (39), `!` is a map. This is what makes
   `⊤ = ! ; ?` contain every arrow.]],

  P(p-frob, s: 74%), [(41) the *Frobenius* law \ #src[an axiom. `𝟙 ⊗ Δ` and `∇ ⊗ 𝟙` draw as stacked runs; only the
  associator `α⁻¹` stays an opaque box, having no shape in this calculus.]],
  [the *modular identity* §2.112 — and reciprocation §2.11 itself, since the cup and cap only
   satisfy the snake because of (41).],

  P(p-special, s: 88%), [the *special* law \ #src[*not* an axiom: derived from (38) and (40),
  `Freyd.Diag.CartBicat.special`]],
  [`Δ Δ° = 1` — *`Δ` is injective*, so by §2.141 at `f = g = Δ` it is a monic map. In `Rel(Set)`:
   copying is total and loses nothing.],

  P(p-lax-delta, s: 84%), [(42) every arrow is a *lax comonoid homomorphism*],
  [§2.136's `R (S ∩ T) ⊑ R S ∩ R T`, read at `S := π₁°`, `T := π₂°` — Freyd's semi-distributivity,
   product-free.],

  P(p-lax-bang, s: 88%), [(43) every arrow is *lax for the counit*],
  [§2.152's step "`p_α` is maximal in `(α, λ)`, hence `R p_β ⊆ p_α`" — that is, `R ⊑ ⊤`.],
)
]

= Unitary and pre-tabular — the two conditions the converse needs

Freyd's §2.11 axioms are all a cartesian bicategory has to give back. Going the other way needs two
further conditions, and they are exactly the two the repo has not formalised. Both definitions below
are quoted from `Freyd/S2_10.lean`, which follows the book.

#table(
  columns: (3.6cm, 1fr, 1fr),
  align: (left + top, left + top, left + top),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*condition*], [*Freyd*], [*what the Frobenius side already has*]),

  [*unitary* \ #src[§2.15]],
  [`T` is a *partial unit* when `𝟙 T` is the largest endomorphism on it,
   `PartialUnit T := ∀ R : T ⟶ T, R ⊑ 𝟙 T` (`:539`); it is a *unit* when moreover every object
   carries an entire arrow to it, `IsUnit T := PartialUnit T ∧ ∀ a, ∃ R : a ⟶ T, Entire R` (`:545`).
   A `UnitaryAllegory` is an allegory with one (`:548`). \ #src[The point of a unit is that it
   makes `⊤_{a,b}` exist: `⊤ = p_α p_β°` through the unit, which is where §2.152's
   "`R p_β ⊆ p_α`" — the repo's (43) — comes from.]],
  [*already there, for free.* The monoidal unit `𝕀` is the unit object, `!_a : a ⟶ 𝕀` is the entire
   arrow every object carries to it — (40) says so — and `⊤ = ! ; ?` is maximal by
   `Freyd.Diag.«≤_top»`. So every cartesian bicategory of relations is unitary, with nothing
   assumed. \ #src[Not recorded in Lean: `allegoryOfCartBicat` builds a plain `Allegory`, and no
   `UnitaryAllegory` instance is derived from `CartBicat`.]],

  [*pre-tabular* \ #src[§2.165]],
  [`f, g` *tabulate* `R` when both are maps, `R = f° g`, and `f f° ∩ g g° = 𝟙`
   (`Tabulates`, `:502`); `R` is *tabular* when some pair tabulates it (`:506`). An allegory is
   `PreTabularAllegory` when every morphism is contained in a tabular one (`:556`). \
   #src[§2.165: "If `A` is unitary then pre-tabularity is equivalent to the existence of tabulations
   for maximal morphisms."]],
  [*this is what `⊗` is.* Given unitarity, the condition reduces to tabulating each `⊤_{a,b}`, and a
   tabulation of `⊤_{a,b}` is precisely an object `a ⊗ b` with its two projections — the monoidal
   product Def. 4.1 assumes. That is the whole content of the swap: Freyd derives the product from
   tabulations, Def. 4.1 posits it. \ #src[Not built. Rebuilding `⊗` from tabulations and products
   in `Map(𝒜)` is `cartBicatOfUnitaryPretabular`; `diag/PLAN.md` holds it back for want of a
   consumer.]],
)

Together they are the whole gap: *cartesian bicategory of relations ≃ unitary pre-tabular allegory*
(`DiagrammaticAlgebraOfFirstOrderLogic` §10, after Carboni–Walters). One half of that equivalence is
`allegoryOfCartBicat` and is a theorem in this repo; the other half is the two rows above.

= Union and residual — what phases 8 and 9 add

`∪` and `/` are past where Freyd's §2.11 list stops, and past what Def. 4.1 can build: they need a
*biproduct* on top of the Frobenius structure (`diag/Tape.lean`, after `TapeDiagrams.pdf`) and a
*second composition* with linear adjoints (`diag/FO.lean`, after
`DiagrammaticAlgebraOfFirstOrderLogic.pdf`). Both are built, so both draw.

The two notations say which layer a picture is in. A union is a *tape*: the rounded wrapper is the
second monoidal product, and its `▷`/`◁` open and close a branch a particle takes exactly one of —
the same fork-runs-join shape as a meet, on a different product. A residual is a *cut*: `R / S` is
`R ⨟• S⊥` by definition, the black composition is drawn on black ground and the linear adjoint `S⊥`
is `S` mirrored and negated, so the picture is `R` on black beside `S` mirrored in a white island.
Both conventions are `DiagrammaticAlgebraOfFirstOrderLogic.pdf`'s own; the last section of this note
sets out where the paper states them, and what goes wrong if a residual is drawn as a box labelled
`R / S` instead.

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*statement*], [*picture, from the Lean statement*]),

  [`R ⊑ R ∪ S` — §2.2 in Freyd; here `Freyd.Diag.Biprod.«≤_union_left»`. \
   #src[`union R S := ⟨R, S⟩ ; [𝟙, 𝟙]` (`diag/Tape.lean:84`): offer both branches, then forget which
   was taken.]],
  P(p-union-left),

  [`R ∪ S = S ∪ R` — `Freyd.Diag.Biprod.union_comm`. \
   #src[The two branches of a tape are interchangeable, exactly as the two strands of `Δ` are.]],
  P(p-union-comm),

  [`⊥ ∪ R = R` — `Freyd.Diag.Biprod.bot_union`. \
   #src[`bot a b := toZero a ; (toZero b)°` (`diag/Tape.lean:87`), routed through the zero object;
   the exporter has no shape for it, so it prints as a box.]],
  P(p-bot-union),

  [`R (S ∪ T) = R S ∪ R T` — `Freyd.Diag.Biprod.comp_union`; composition distributes over union,
   which `∩` does not. \ #src[Freyd §2.2's distributivity, the reason a distributive allegory is
   more than an allegory.]],
  P(p-comp-union),

  [`(R ∪ S)° = R° ∪ S°` — `Freyd.Diag.Biprod.conv_union`. \
   #src[The converse is a 2-functor for the tape layer too.]],
  P(p-conv-union),

  [`R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)` — `Freyd.Diag.FbCbRig.meet_union_distrib`, the law that makes
   `distributiveAllegoryOfFbCb` a *distributive* allegory (§2.2). \
   #src[The one picture with both layers in it: meets inside a tape on the left, tapes around meets
   on the right.]],
  P(p-distrib, s: 78%),

  [`(R / S) S ⊑ R` — `Freyd.Diag.ClosedLinearBicat.«residual_comp_≤»`; the residual is a lower bound
   of the arrows it is the greatest of. \ #src[Freyd's §2.31 division: `R / S` is the largest `T`
   with `T S ⊑ R`, and `«≤_residual_iff»` (`diag/FO.lean:171`) is that Galois statement in full. The
   two colour switches are the definition `R ⨟• S⊥` unfolded — one for the black composition, one for
   the linear adjoint — and the `S` in the island is mirrored because a linear adjoint is a converse
   as well as a negative.]],
  P(p-residual),
)

= Lemma 4.2 (ii) — the proof, not just the statement

`diag-export --proof` draws a *proof*. A `calc` chain elaborates to nested `Trans.trans`, so its
intermediate terms are all recoverable from the proof term: flatten the spine, infer the type of each
leaf, draw one canvas per step. Nothing is replayed and nothing is retold — the nine rows below are
the chain the Lean kernel accepted for `Freyd.Diag.CartBicat.conv_comp`, which is Lemma 4.2 (ii),
`(R ; S)° = S° R°`.

== First: why these pictures are not pictures of a converse

They are not, and that is the thing to get straight before reading them. The converse is drawn with
*two* bends — a cup on the way in and a cap on the way out, each a pair of dots, `? ; Δ` and `∇ ; !`
— which is the left-hand figure below. The proof never draws that. `conv_unique` says an arrow is
*the* converse of `R` as soon as it satisfies one equation between UNBENT arrows `a ⊗ b → I`: two
strands in on the left, one cap on the right. Bending is a bijection (`bend_unbend`/`unbend_bend`),
so settling the unbent equation settles the bent one, and the cup never has to be drawn at all.

That is why every row below has a cap and no cup, and why an arrow that "is a converse" shows up not
as a bent box but as a box sitting on the *bottom* strand, mirrored.

#table(
  columns: (1fr, 1fr),
  align: (center + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*the converse, as the paper draws it*], [*the one rule the proof uses, twice*]),
  fig({ conv((0, -0.80), $R$) }),
  P(p-conv-slide, s: 80%),
  [#src[`R°` is `R` with both wires bent round: in at the bottom left, cup at the top left, cap at
   the bottom right. Two dots at each bend, as `functorialSemanticsForRelationalTheories.pdf` draws
   it — a cup is `?` then `Δ`, a cap is `∇` then `!`. *Transcribed by hand;* a definition has no
   statement to export.]],
  [#src[`conv_slide` (`diag/CB.lean:449`): a box on the BOTTOM strand facing a cap is the same as
   that box on the TOP strand, upright. Sliding round the bend is what turns `R°` into `R`. This is
   the entire content of Lemma 4.2 (ii); the other seven steps are bookkeeping.]],
)

== The chain

One row per *term*, not per step: the right-hand side of every step is the left-hand side of the
next, so drawing steps would draw every picture twice. The first column is the term as the Lean has
it, fully bracketed, with `⊗` binding tighter than `;` — it comes off the same walk as the picture,
so the two cannot drift apart. Watch which *strand* each box is on: bottom means mirrored, top
means upright.

#table(
  columns: (4.4cm, 1fr, 6.6cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[*Lemma 4.2 (ii),* `(R ; S)° = S° ; R°` #h(8pt) #Pin(p-conv-comp)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(l42b.at(0).terms.at(0)),
  P(l42b.at(0).steps.at(0), s: 66%),
  [*the start.* #src[What `conv_unique` asks about `S° R°`: both boxes on the bottom strand, mirrored — that is what "these are converses" looks like once the wires are unbent.]],

  raw(l42b.at(0).terms.at(1)),
  P(l42b.at(0).steps.at(1), s: 66%),
  [*1.* `⊗` is a functor, so doing two things to one strand in sequence is the sequence of doing them. #src[*Same picture.*]],

  raw(l42b.at(0).terms.at(2)),
  P(l42b.at(0).steps.at(2), s: 66%),
  [*2. `conv_slide`.* `R°` is the box nearest the cap, so it slides round the bend: it leaves the bottom strand, arrives on the top, and comes back upright as `R`. #src[*The first of the two steps that prove anything.*]],

  raw(l42b.at(0).terms.at(3)),
  P(l42b.at(0).steps.at(3), s: 66%),
  [*3.* `simp only [Cat.assoc]`. #src[Re-bracketing — visible in the term column, invisible in the picture. *Same picture.*]],

  raw(l42b.at(0).terms.at(4)),
  P(l42b.at(0).steps.at(4), s: 66%),
  [*4. `tensHom_split'`* — interchange. `R` is on the top strand and `S°` on the bottom, so running them in sequence and running them side by side are the same thing. #src[Shows as a re-spacing only because the exporter lays a diagram out left to right.]],

  raw(l42b.at(0).terms.at(5)),
  P(l42b.at(0).steps.at(5), s: 66%),
  [*5. `tensHom_split`* — the same law, back the other way. Split them apart again, `R` first, so that `S°` is now the box facing the cap. #src[Which is what the next real step needs.]],

  raw(l42b.at(0).terms.at(6)),
  P(l42b.at(0).steps.at(6), s: 66%),
  [*6.* `simp only [Cat.assoc]`. #src[Re-bracketing. *Same picture.*]],

  raw(l42b.at(0).terms.at(7)),
  P(l42b.at(0).steps.at(7), s: 66%),
  [*7. `conv_slide`,* on `S` this time. `S°` slides round the bend and arrives upright on the top strand. Both boxes are now on top, both upright, in the order `R` then `S`. #src[*The second and last real step.*]],

  raw(l42b.at(0).terms.at(8)),
  P(l42b.at(0).steps.at(8), s: 66%),
  [*8.* `simp only [Cat.assoc]`. #src[Re-bracketing. *Same picture.*]],

  raw(l42b.at(0).terms.at(9)),
  P(l42b.at(0).steps.at(9), s: 66%),
  [*9. `tensHom_comp`* — interchange once more; the two top-strand boxes merge into one. This is `R ; S` unbent, so `conv_unique` reads off `S° R° = (R ; S)°`. #src[*Done.*]],
)

*What the chain measures.* Read down the pictures and most consecutive pairs are the same drawing —
steps 1, 3, 6, 8 and 9 change nothing at all, and step 4 changes only spacing — while the term
column beside them changes at every row. Those are
associativity, the unit laws and interchange — precisely the laws a string diagram has built into
its geometry rather than as rewrites. Seven of these nine Lean steps are bureaucracy the picture
language does not charge for, and the theorem is two applications of `conv_slide`.

*How this differs from the paper's proof.* The paper proves (ii) by inserting a snake in the middle
of `R ; S` and reading the two halves off as `S°` and `R°` — three pictures, all bent. The Lean
never bends. Same theorem, different route, and the export shows the route the kernel accepted.
Drawn by hand it would have shown the paper's three pictures and quietly implied those were what the
repo had checked.

= The modular law — proved, drawn

Freyd *adjoins* the modular identity: an allegory has no structure to derive it from, so it goes in
as an axiom. Here it is a theorem, and this is its proof — `Freyd.Diag.modular_of_frobenius`
(`diag/CB_Allegory.lean:48`), four terms, of which exactly one step is an inequality.

#table(
  columns: (5.4cm, 1fr, 5.8cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[*the modular law,* `R S ∩ T ≤ (R ∩ T S°) S` #h(8pt) #Pin(p-modular)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(mfb.at(0).terms.at(0)), P(mfb.at(0).steps.at(0), s: 62%),
  [*the start:* `R S ∩ T`. #src[A meet, so a copy and a merge with `R S` above and `T` below.]],

  raw(mfb.at(0).terms.at(1)), P(mfb.at(0).steps.at(1), s: 62%),
  [*Factor out the shared prefix.* `(R S) ⊗ T` is `(R ⊗ T) ; (S ⊗ 𝟙)`, so everything before the
   `S` is common to both sides and can be set aside. #src[An equality, and drawn as one.]],

  raw(mfb.at(0).terms.at(2)), P(mfb.at(0).steps.at(2), s: 62%),
  [*`«∇_slide_conv»`,* under the shared prefix. #src[`S` slides through the merge and reappears as
   `S°` on the other strand. *The only inequality in the proof* — everything else is reshaping.]],

  raw(mfb.at(0).terms.at(3)), P(mfb.at(0).steps.at(3), s: 62%),
  [*Fold the prefix back in.* `R ⊗ (T S°)` is `(R ⊗ T) ; (𝟙 ⊗ S°)`, and the copy-merge pair reads as
   a meet again. #src[`(R ∩ T S°) S`, which is the goal.]],
)

== Inside the middle step

`«∇_slide_conv»` (`diag/CB.lean:560`) is where the mathematics is, and it mentions only `S` —
`R` and `T` sit untouched in the prefix throughout. Read on its own it says one arrow slides
through a merge:

#align(center, block(inset: (y: 8pt))[#P(p-nabla-slide, s: 74%)])

`S` occurs once on the left and twice on the right. That is the tell: the lax copy inequation (42)
is the only law in Def. 4.1 that may duplicate a box, so it has to be the inequality step — and its
own chain shows it is the only one.

#table(
  columns: (5.4cm, 1fr, 5.8cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[*`«∇_slide_conv»`,* `(S ⊗ 𝟙) ; ∇ ≤ (𝟙 ⊗ S°) ; ∇ ; S`
      #h(8pt) #Pin(p-nabla-slide)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(nsb.at(0).terms.at(0)), P(nsb.at(0).steps.at(0), s: 62%),
  [*the start:* `(S ⊗ 𝟙) ; ∇`.],

  raw(nsb.at(0).terms.at(1)), P(nsb.at(0).steps.at(1), s: 62%),
  [*`«∇_of_cap»`,* backwards. #src[The merge is rebuilt from a copy and a cap, which puts the term
   into the shape `(S ; Δ) ⊗ 𝟙` that (42) applies to.]],

  raw(nsb.at(0).terms.at(2)), P(nsb.at(0).steps.at(2), s: 62%),
  [*(42), `lax_Δ`.* `S ; Δ` becomes `Δ ; (S ⊗ S)`: the box is copied. \ #src[*The whole of the
   modular law, in one step.*]],

  raw(nsb.at(0).terms.at(3)), P(nsb.at(0).steps.at(3), s: 62%),
  [*`«cap_tens_∇»` and `conv_slide`.* #src[Reshaping back, and the surviving duplicate slides round
   the cap to become `S°` — the same rule Lemma 4.2 (ii) is made of.]],
)

*What the associators cost.* `α` and `ρ` have no shape in this calculus and print as opaque boxes,
so the two middle terms of the inner chain are less legible than its ends. That is the honest price
of drawing what the Lean says: the reshaping steps really are that fiddly, and a hand-drawn version
would have hidden them by working up to coherence.

= Maps: SV, TOT, INJ, SUR, and the two inequations that always hold

Def. 4.1 clause 4 says every arrow is lax for `Δ` and for `!` — inequations (42) and (43). Applying
Lemma 4.2 (ii) and (iv) to them gives (44) and (45), the same statements about `∇` and `?`. Those
four hold for *every* arrow. Their four REVERSES do not, and each one failing or holding is a
property of the arrow: that is (SV), (TOT), (INJ), (SUR).

#table(
  columns: (4.2cm, 1fr, 1fr),
  align: (left + horizon, center + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([], [*holds for every arrow*], [*holds iff the arrow is …*]),

  [*copy* \ #src[`Δ`]],
  [#src[(42) `R ; Δ ≤ Δ ; (R ⊗ R)`] #v(-2pt) #P(p-lax-delta, s: 74%)],
  [#src[(SV) — *single valued*] #v(-2pt) #P(p-sv, s: 74%)],

  [*discard* \ #src[`!`]],
  [#src[(43) `R ; ! ≤ !`] #v(-2pt) #P(p-lax-bang, s: 74%)],
  [#src[(TOT) — *total*] #v(-2pt) #P(p-tot, s: 74%)],

  [*merge* \ #src[`∇`]],
  [#src[(44) `∇ ; R ≤ (R ⊗ R) ; ∇` — the converse of (42). *Not in the Lean;* see below.]],
  [#src[(INJ) — *injective*] #v(-2pt) #P(p-inj, s: 74%)],

  [*unit* \ #src[`?`]],
  [#src[(45) `? ; R ≤ ?` — the converse of (43). *Not in the Lean;* see below.]],
  [#src[(SUR) — *surjective*] #v(-2pt) #P(p-sur, s: 74%)],
)

The paper gives the same four properties a second time, as ADJOINT conditions — (46)–(49) — and
Lemma 4.4 says the two presentations agree. `diag/CB_Derived.lean` takes the adjoint forms as the
definitions, because they are literally Freyd's `Simple` and `Entire` (§2.13), so a `diag` map and a
book map are one predicate with no translation layer.

#table(
  columns: (5.0cm, 1fr, 1fr),
  align: (left + horizon, center + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*property*], [*adjoint form, the definition*], [*Freyd*]),

  [*single valued* \ #src[`Freyd.Diag.SingleValued`]], P(p-sv46, s: 74%),
  [`Simple R := R° R ⊑ 1` \ #src[§2.13]],

  [*total* \ #src[`Freyd.Diag.Total`]], P(p-tot47, s: 74%),
  [`Entire R := 1 ⊑ R R°` \ #src[§2.13. With *single valued*, `R` is a *map*.]],

  [*injective* \ #src[`Freyd.Diag.Injective`]], P(p-inj48, s: 74%),
  [`R R° ⊑ 1` \ #src[§2.141 at `f = g = R`: a monic pair, so a monic map.]],

  [*surjective* \ #src[`Freyd.Diag.Surjective`]], P(p-sur49, s: 74%),
  [`1 ⊑ R° R` \ #src[§2.147: "`g` is a cover iff `1 ⊑ g° g`", that is, iff `g°` is entire.]],
)

*Why (44) and (45) have no picture.* Both are converse-images, so drawing them from a Lean statement needs
that statement to exist, and it does not. Getting it needs `Δ° = ∇`, `!° = ?` and Lemma 4.2 (iii)
`(f ⊗ g)° = f° ⊗ g°` — and the first of those is a Frobenius computation at a COMPOSITE object,
which is the clause of Carboni & Walters' definition that Def. 4.1 as printed omits (`diag/CB.lean`'s
header records this). It is the same gap that leaves Lemma 4.4 unproved in the repo. The four
reverse inequations opposite are unaffected: they are recorded under the paper's own labels in
`diag/CB_Derived.lean`, and nothing downstream depends on Lemma 4.4.

= Entireness of an intersection

Two definitions from Freyd, both used below. The *domain* of `R` is the part of the identity where
`R` is defined, `Dom R = 1 ∩ R R°` (§2.122). `R` is *entire* if it is defined everywhere,
`Dom R = 1`, equivalently `1 ⊑ R R°` (§2.13) — which is `Total` above, the picture opposite (47).
The question this section answers is when an *intersection* is entire: Freyd's §2.124, "a lemma we
will use repeatedly", and B&dM 4.18.

#align(center, block(inset: (y: 6pt))[
  #P(p-entire, s: 80%) \
  #src[`Freyd.Diag.entire_inter_iff` (`diag/S2_124.lean:213`) — `Total (R ∩ S) ↔ 𝟙 ≤ R ; S°`]])

Read the two sides: on the left `R ∩ S` is named *twice*, on the right `R` and `S` are named *once
each* and the meet is gone. That is the whole point of the lemma — the meet is needed to *ask*
whether something is entire, not to *answer* it — and it is why every later use quotes the right-hand
form. Freyd spends it at §2.147, where `H = x f° ∩ y g°` has to be shown entire; B&dM spend it
throughout chapter 4.

`Freyd.Alg.entire_inter_iff` (`AOP/A4_2.lean:187`) is the same statement for a bare allegory, and
there it is `Iff.rfl` on top of `dom_inter`: in `Freyd/S2_10.lean` the order `X ⊑ Y` is *defined* as
`X ∩ Y = X`, so "`Dom(R ∩ S) = 1`" and "`1 ⊑ R S°`" are the same proposition once §2.124 is known.
Here `≤` is primitive, so both directions are real steps — and they cost very different things.

#table(
  columns: (5.0cm, 1fr, 6.0cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*`⟹`* #h(6pt) given `R ∩ S` entire, #Pin(ent-a)
    #h(6pt) show #Pin(ent-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(entb.at(0).terms.at(0)), P(entb.at(0).steps.at(0), s: 68%),
  [*the start:* `𝟙`.],

  raw(entb.at(0).terms.at(1)), P(entb.at(0).steps.at(1), s: 68%),
  [*the hypothesis:* `R ∩ S` entire. #src[By the definition of entire, `𝟙 ≤ P P°` at `P = R ∩ S`.]],

  raw(entb.at(0).terms.at(2)), P(entb.at(0).steps.at(2), s: 68%),
  [*monotonicity, twice:* `R ∩ S ≤ R`, and `R ∩ S ≤ S` under `°`. #src[No modular law.]],
)

#table(
  columns: (5.0cm, 1fr, 6.0cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*`⟸`* #h(6pt) given #Pin(ent-b) #h(6pt) show
    `R ∩ S` entire, #Pin(ent-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(entb.at(1).terms.at(0)), P(entb.at(1).steps.at(0), s: 68%),
  [*the start:* `𝟙`.],

  raw(entb.at(1).terms.at(1)), P(entb.at(1).steps.at(1), s: 68%),
  [*the hypothesis,* met with `𝟙`. #src[`meet_glb`: `𝟙 ≤ 𝟙` and `𝟙 ≤ R S°`, so `𝟙` is below the
   meet of the two.]],

  raw(entb.at(1).terms.at(2)), P(entb.at(1).steps.at(2), s: 68%),
  [*§2.124:* `𝟙 ∩ R S° = 𝟙 ∩ (S ∩ R)(S ∩ R)°`. #src[`R S°` relates `a` to `a′` when some `b` has
   `a R b` and `a′ S b`. The `𝟙 ∩` sets `a′ = a`, and it then reads "some `b` has `a R b` and
   `a S b`" — one arrow of `R ∩ S`. Two arrows become one; that is the step, and it is what needs
   the modular law. #linebreak() Freyd writes the right-hand side `Dom (S ∩ R)`: `Dom X` is his name
   for `𝟙 ∩ X X°`, so it is the same term, not an extra operation.]],

  raw(entb.at(1).terms.at(3)), P(entb.at(1).steps.at(3), s: 68%),
  [*`X ∩ Y ≤ Y`,* then `S ∩ R = R ∩ S`. #src[The outer fork drops away, leaving the goal.]],
)

*What the asymmetry says.* One direction is two applications of monotonicity; the other needs
§2.124, which needs the modular law, which in this calculus needs the Frobenius equation (41) and
the lax copy inequation (42) — §7 above. So the picture chain locates the cost exactly: the third
row of the second table is the whole strength of the lemma, and everything else is bookkeeping.

= Anything missing?

*Nothing on Freyd's side.* All eight §2.11 axioms are theorems of Def. 4.1, and
`allegoryOfCartBicat` (`diag/CB_Allegory.lean:85`) discharges the `Allegory` structure field for
field. The modular identity, which Freyd has to *adjoin* because an allegory has no structure to
derive it from, comes out of (41) and (42).

*Three things are stated but unproved.* `«∇Δ≤𝟙»` and `«?!≤𝟙»` are discharged and never used (see
below); (44) and (45) are not stated at all; and Lemma 4.4, that the comonoid and adjoint forms of
the map conditions agree, is not proved. All three trace to one omission in Def. 4.1 as printed — no
Frobenius structure at a composite object — which `diag/CB.lean`'s header records.

*Two laws on the Frobenius side do no work here.* Grepping the repo, `«∇Δ≤𝟙»` and `«?!≤𝟙»` are
never used: they appear only in the class definition. They are there to make `Δ ⊣ ∇` and `! ⊣ ?`
genuine adjunctions — which is what pins `∇ = Δ°` and `? = !°` by uniqueness of adjoints — not to
prove any allegory law.

*And nothing on this branch discharges them, because the tower has no model.* `diag/RelSetCB.lean`
and `diag/RelSetFO.lean` carried the `Rel(Set)` instances and were dropped when the monoidal
structure was made strict: `RelSet` is not a model of `diag/Monoidal.lean`, so, as `diag/FO.lean`'s
own header puts it, "the layer has no model here". Everything below Def. 4.1 in this note is a
theorem OF the axioms; that the axioms are satisfied by relations is the paper's, not this repo's.

*The bridge runs one way only*, for the reason the section above sets out: a cartesian bicategory
carries a symmetric monoidal `⊗` and an allegory carries nothing of the kind.

*What Def. 4.1 alone does not have.* Everything past Freyd's §2.11 needs structure beyond it, and —
this is the point — from *different sources*, not from
`functorialSemanticsForRelationalTheories.pdf`:

// The raw is one size down here: `DiagrammaticAlgebraOfFirstOrderLogic.pdf` is a single unbreakable
// monospace word, and at 8.5pt it runs out of its column and over the next one.
#[
#show raw: set text(size: 8.4pt)
#table(
  columns: (3.4cm, 3.6cm, 8.2cm, auto),
  align: (left + top, left + top, left + top, left + top),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*construct*], [*Freyd*], [*diagrammatic counterpart*], [*status*]),

  [*tabulation*], [§2.14], [none], [no counterpart. Def. 4.1 gives no splitting of coreflexives;
  `⊤ = ! ; ?` is all the tabular content there is.],

  [`∪`, `⊥`], [§2.2, distributive allegory],
  [a *biproduct* `⊕` on top of Def. 4.1 — `Biprod`, `union`, `bot`, and
   `distributiveAllegoryOfFbCb` in `diag/Tape.lean`; `TapeDiagrams.pdf`],
  [built, and drawn above. Not derivable from Def. 4.1 alone — the paper's calculus has no union at
   all.],

  [`R / S`, complement], [§2.31, division allegory],
  [`LinearBicat`, `ClosedLinearBicat`, `residual` — `diag/FO.lean`;
   `DiagrammaticAlgebraOfFirstOrderLogic.pdf`],
  [built, and drawn above — but axiomatised only. `perp` is a field of `ClosedLinearBicat` that
   nothing on this branch instantiates.],

  [`Λ`, power transpose], [§2.4], [none], [open. No calculus in this tower has a power object.],

  [Allegory ⟹ CB], [§2.15 + §2.165],
  [`cartBicatOfUnitaryPretabular`], [deliberately not built.],
)
]

One caution on §7–§9 of the paper, which look like they extend this table and do not: they are
worked examples in *other* models. The paper says so itself at the end of §7 — only the black
fragment `⊤, ∩, (−)†, ; , id` coincides with the calculus of relations there, while "`⊥` is not the
empty relation and `>` is not the union".


= The shunting rule

A map may be moved from one side of a containment to the other, at the cost of its converse. That
is the workhorse of relational program calculation — B&dM 4.19 and 4.20 — and it is what makes
point-free derivations possible at all: it is how a function gets out of the way so the relation
underneath can be reasoned about.

`AOP/A4_2.lean` has both rules for a bare `Allegory` (`map_shunt_right`, `map_shunt_left`), which is
where every downstream derivation calls them. They are now also in the diagrammatic layer
(`shunt_right`, `shunt_left` in `diag/CB_Derived.lean`) — same statements, so that there is a Lean
declaration in `diag` terms for the exporter to draw. Nothing new is assumed: both are proved from
`Map` alone.

Each rule is an `↔`, so each is two chains. The statement of a branch is its header: the hypothesis
it is given and the goal it reaches, both drawn from the same Lean `↔` the chain proves.

// One size down: the declaration names are unbreakable monospace words wider than the column.
*The proofs, drawn.* Each `↔` is two chains, and `diag-export --proof` now splits an `Iff.intro`
into its two branches rather than drawing the longer one and dropping the other. The point to watch
is that each direction spends exactly one half of `Map` — never both.

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting right, `⟹`* #h(6pt) given #Pin(sr-a) #h(4pt)
    show #Pin(sr-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(srb.at(0).terms.at(0)),
  P(srb.at(0).steps.at(0), s: 74%),
  [*the start:* `R`.],

  raw(srb.at(0).terms.at(1)),
  P(srb.at(0).steps.at(1), s: 74%),
  [*`Total f`.* `𝟙 ≤ f f°`, so `f f°` may be inserted after `R`. #src[This is the only thing the forward direction costs.]],

  raw(srb.at(0).terms.at(2)),
  P(srb.at(0).steps.at(2), s: 74%),
  [Re-bracket to `(R f) f°` and apply the hypothesis `R f ≤ S`. #src[`R ≤ S f°`, which is the goal.]],
)

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting right, `⟸`* #h(6pt) given #Pin(sr-b) #h(4pt)
    show #Pin(sr-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(srb.at(1).terms.at(0)),
  P(srb.at(1).steps.at(0), s: 74%),
  [*the start:* `R f`.],

  raw(srb.at(1).terms.at(1)),
  P(srb.at(1).steps.at(1), s: 74%),
  [Apply the hypothesis `R ≤ S f°` on the left. #src[The two `f`s are now adjacent.]],

  raw(srb.at(1).terms.at(2)),
  P(srb.at(1).steps.at(2), s: 74%),
  [*`SingleValued f`.* `f° f ≤ 𝟙`, so the pair cancels and `S` is left. #src[The only thing the backward direction costs.]],
)

*Shunting left is the mirror,* and its two chains come out the same shape — `Total f` on the way
out, `SingleValued f` on the way back — with the map on the other side throughout.

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting left, `⟹`* #h(6pt) given #Pin(sl-a) #h(4pt)
    show #Pin(sl-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(slb.at(0).terms.at(0)),
  P(slb.at(0).steps.at(0), s: 74%),
  [*the start:* `R`.],

  raw(slb.at(0).terms.at(1)),
  P(slb.at(0).steps.at(1), s: 74%),
  [*`Total f`.* `f f°` inserted before `R`.],

  raw(slb.at(0).terms.at(2)),
  P(slb.at(0).steps.at(2), s: 74%),
  [Re-bracket to `f (f° R)` and apply the hypothesis. #src[`R ≤ f S`.]],
)

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting left, `⟸`* #h(6pt) given #Pin(sl-b) #h(4pt)
    show #Pin(sl-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(slb.at(1).terms.at(0)),
  P(slb.at(1).steps.at(0), s: 74%),
  [*the start:* `f° R`.],

  raw(slb.at(1).terms.at(1)),
  P(slb.at(1).steps.at(1), s: 74%),
  [Apply the hypothesis on the right. #src[The two `f`s become adjacent.]],

  raw(slb.at(1).terms.at(2)),
  P(slb.at(1).steps.at(2), s: 74%),
  [*`SingleValued f`.* The pair cancels, leaving `S`.],
)

*What the rule really is.* An adjunction. `R f ≤ S ⟺ R ≤ S f°` says exactly that `f ⊣ f°` in the
poset-enriched sense of (35) — `Total f` is its unit and `SingleValued f` its counit — so "`f` is a
map" and "`f` has a right adjoint, namely `f°`" are the same statement. That is Lemma 4.8
(`Freyd.Diag.lemma_4_8`), which turns it round: any right adjoint of a map *must* be its converse,
by the usual uniqueness argument. The paper's converse half — an arrow with a right adjoint is a map
— is the diagram chase that needs Lemma 4.4, and is not proved here for the reason given above.

*Where it is spent.* In this repo, `map_shunt_right`/`map_shunt_left` carry the relational-product
universal property (`AOP/A5_2.lean:177`), division (`AOP/A4_4.lean:370`), the lax naturality
conditions (`AOP/A5_7.lean:67`) and the catamorphism work (`AOP/A6_5.lean:372`). It is the single
most-used lemma of the AOP layer.


= Division and negation — the cheatsheet's §8, drawn

`AOP/Cheatsheet.typ`'s eighth section is B&dM §4.4–4.5: the two divisions, the symmetric division,
negation, and Schröder's rule. Every law of it that is about arrows rather than elements is a
theorem here — division in `Freyd/S2_30.lean` (Freyd's §2.31), implication, the lexical order and
the division map-laws in `AOP/A4_4.lean`, negation and Schröder in `AOP/A4_5.lean` — so every one of
them draws. Not one of them is a theorem of the diagrammatic tower, and the pictures say so.

*Negation is a CUT, and that is what makes these pictures pictures.*
`DiagrammaticAlgebraOfFirstOrderLogic.pdf` says how, twice. On p. 2: given `c`, "take its mirror
image and then its photographic negative" — that is `c⊥`, and its figure is a box on a black ground
with the chamfer on the other side. On p. 10, translating Peirce's existential graphs, where a
closed curve round a subgraph is negation: to move from those to these diagrams "it suffices to
treat lines and predicate symbols in the obvious way and each cut as a *color switch*". So a
complement is not a frame drawn round a picture and it is certainly not a box with `∼R` printed
inside it — it is the *same picture on the other colour*. Fig. 4 of that paper draws the black
composition `⨟•` the same way, as a black band round the run, which is what its (δl) and (δr) are
pictures of.

*Cuts nest, and nesting alternates the ground.* That is Peirce's double cut: `∼∼R = R` is two
grounds cancelling. It is also why `R / Y = ∼(∼R ; Y°)` comes out as a black region with a white
island inside it — the shape of Fig. 4's (νr°) — rather than as a box repeating its own label. The
residual of the earlier section is drawn this way too: `residual R S` is `R ⨟• S⊥` by definition
(`diag/FO.lean:162`), so the exporter unfolds it and the picture shows `R` on black beside `S`
mirrored in a white island.

*What stays a box, and why.* Dashed still means "no definition in terms of the generators to
unfold", and after the cut is taken out that is four things: `/` itself, which is a *field* of
`DivisionAllegory`; `\` and `/ₛ`, defined from it; and `⇨`, a `Sup`. A dashed box takes a label, so
whatever sits under one is set as text — `(R /ₛ S)°` is a mirrored box reading `R /ₛ S`, not a
picture of the meet in its definition. The theorem that says what `/` *is* is `div_eq_neg_comp`,
and that one draws.

*The residual drawn earlier is this `/`.* `«≤_residual_iff»` (`diag/FO.lean:171`) and `le_div_iff`
(`Freyd/S2_30.lean:54`) are the same Galois statement, `T S ⊑ R ⟺ T ⊑ R/S`, so in a model carrying
both structures the two operations agree by uniqueness of adjoints, with neither definition being
unfolded.

*What `/` is, without a complement anywhere: long division.* `R / S` is how much of `R` you can lay
down before `S` still fits inside what is left, and the figure says exactly that. Read the bar left
to right, as a composite: `R / S` first, then `S`, and the two together stay inside `R`. The leftover
is the whole reason the cancel law is `(R/S) S ⊑ R` and not an equality — and it is drawn as a
hairline on purpose, because `R / S` is the *largest* such quotient. Any wider and `S` stops fitting;
the sliver is what is left when nothing more can be taken.

Solid is what the equation pins: `R`'s left edge, `S`'s left edge, and the stretch before `S`, which
is what `R / S` measures. Dashed is the slack: nothing to the right of `S` is determined by
`T S ⊑ R`, so `S`'s far edge, `R`'s far edge and the gap between them are all drawn as not-pinned.

Read it as a *measurement*, not as a containment of relations. `R : a → c` and `S : b → c` are not
in the same hom-set, so `S` is not a sub-relation of `R` and neither is `R / S` — what sits inside
`R` is the composite `(R/S) S`, which does have `R`'s type. The bar is that composite, and the
quotient is how far along it reaches. Pushed too far, the metaphor breaks in the usual place:
`⊥ / ⊥ = ⊤`, which no picture of a part of `⊥` is going to show.

#fig({
  let y0 = -0.55
  let y1 = 0.55
  let ys = 0.36                      // S is inset top and bottom: it sits INSIDE R
  let xq = 3.0                       // R/S ends, S begins
  let xs = 4.9                       // S ends
  let xr = 5.02                      // R ends — a hairline past S, and that hairline is the point
  let sol = (thickness: 1.1pt, paint: black)
  let dsh = (thickness: 1.1pt, paint: black, dash: "dashed")
  // AMBER for `R`, not a red: the tape that draws `∪` elsewhere in this note is pale red, and two
  // pale reds in one document read as one notation.  Green keeps `S`.
  d.rect((0, y0), (xr, y1), fill: rgb("#f6e3bd"), stroke: none)
  d.rect((xq, -ys), (xs, ys), fill: rgb("#cfe6cd"), stroke: none)
  d.line((0, y0), (0, y1), stroke: sol)
  d.line((xq, y0), (xq, y1), stroke: sol)
  d.line((0, y1), (xq, y1), stroke: sol)
  d.line((0, y0), (xq, y0), stroke: sol)
  d.line((xq, y1), (xr, y1), stroke: dsh)
  d.line((xq, y0), (xr, y0), stroke: dsh)
  d.line((xq, ys), (xs, ys), stroke: dsh)
  d.line((xq, -ys), (xs, -ys), stroke: dsh)
  d.line((xs, -ys), (xs, ys), stroke: dsh)
  d.line((xr, y0), (xr, y1), stroke: dsh)
  d.content((xq / 2, 0), text(11pt)[$R slash S$])
  d.content(((xq + xs) / 2, 0), text(11pt)[$S$])
  // The slack is too thin to label in place, so the label stands off and points at it.
  d.line((xr, y0 - 0.42), (xr, y0 - 0.1), stroke: (thickness: 0.6pt, paint: luma(110)))
  d.content((xr, y0 - 0.62), text(9pt, luma(90))[the slack: why `⊑`])
})
#align(center, src[transcribed — the universal property has a Lean statement, this metaphor does
not])

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*statement*], [*picture, from the Lean statement*]),

  [*Division is the right adjoint of composition:* `T ⊑ R/S ⟺ T S ⊑ R` — `Freyd.Alg.le_div_iff`
   (`Freyd/S2_30.lean:54`). The cheatsheet's `\` reversed, since Freyd divides on the right. \
   #src[Everything else in the division half of §8 is this one line applied twice and read
   backwards; `div` itself is a field of `DivisionAllegory` with no definition to unfold.]],
  P(p-le-div, s: 80%),

  [`T ⊑ S\R ⟺ S T ⊑ R` — `Freyd.Alg.le_leftDiv_iff` (`:309`), the mirror. \
   #src[`S\R ≜ (R°/S°)°` (`:301`), so left division is right division conjugated by the converse
   and is not a second primitive.]],
  P(p-le-ldiv, s: 80%),

  [*cancel:* `(R/S) S ⊑ R` — the field `DivisionAllegory.div_comp_le` (`:35`); and `S (S\R) ⊑ R` —
   `Freyd.Alg.leftDiv_comp_le` (`:317`). \ #src[The counit of each adjunction: the quotient composed
   back with the divisor lands under the numerator, never on it.]],
  stack(dir: ttb, spacing: 6pt, P(p-div-cancel, s: 80%), P(p-ldiv-cancel, s: 80%)),

  [*associate:* `R/(S₁ S₂) = (R/S₂)/S₁` — `Freyd.Alg.div_comp_assoc` (`:141`); and
   `(S T)\R = T\(S\R)` — `Freyd.Alg.leftDiv_comp` (`:332`). \ #src[Dividing by a composite one
   factor at a time. The composition is drawn on the left of each equation and swallowed into a
   label on the right, which is exactly what "the calculus cannot see inside `/`" looks like.]],
  stack(dir: ttb, spacing: 6pt, P(p-div-assoc, s: 80%), P(p-ldiv-assoc, s: 80%)),

  [*maps:* `f (R/S) = (f R)/S` — `Freyd.Alg.map_comp_div` (`AOP/A4_4.lean:366`); and
   `R/(f S) = (R/S) f°` — `Freyd.Alg.div_comp_recip_map` (`:376`). \ #src[Both are the shunting rule
   of the previous section, spent twice inside an indirect-equality argument. The second is the one
   that pays: a map moves out of a denominator and reappears as `f°` outside the box.]],
  stack(dir: ttb, spacing: 6pt, P(p-map-div, s: 80%), P(p-div-map, s: 80%)),

  [*symmetric division:* `(R/ₛS)° = S/ₛR` — `Freyd.Alg.symmDiv_recip` (`Freyd/S2_30.lean:237`); and
   `(R/ₛS)(S/ₛT) ⊑ R/ₛT` — `Freyd.Alg.symmDiv_comp` (`:254`). \ #src[`R/ₛS ≜ (R/S) ∩ (S/R)°`
   (`:203`) — the cheatsheet's row. The meet is inside the definition, not inside the statement, so
   it stays under the label: what the pictures show is that `/ₛ` is converse-symmetric and
   transitive, i.e. behaves like an equality of columns.]],
  stack(dir: ttb, spacing: 6pt, P(p-sdiv-recip, s: 80%), P(p-sdiv-comp, s: 80%)),
)

*Negation is `⇨` into `𝟘`.* `∼R ≜ R ⇨ 𝟘` (`AOP/A4_5.lean:44`) on top of `R ⇨ S ≜ ⊔ {X : X ∩ R ⊑ S}`
(`AOP/A4_4.lean:100`), so it needs joins of arbitrary families — a *locally complete* distributive
allegory — and involutivity `∼∼R = R` is an extra axiom, `BooleanAllegory` (`AOP/A4_5.lean:123`).
The two rows marked _boolean_ spend it, and so does the second half of the division-through-negation
row.

#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*statement*], [*picture, from the Lean statement*]),

  [`R ⊑ S ⟺ R ∩ ∼S = 𝟘` — `Freyd.Alg.le_iff_inter_neg_zero` (`AOP/A4_5.lean:144`). \
   #src[The bridge every Schröder proof crosses: containment turned into a disjointness, where
   `comp_inter_zero_iff` can rotate a composite through a converse.]],
  P(p-le-neg, s: 80%),

  [`R ∩ ∼R = 𝟘` — `Freyd.Alg.inter_neg_zero` (`:53`). \ #src[Non-contradiction, and the only law of
   the section that holds with no completeness or Boolean assumption beyond the `⇨` that defines
   `∼`.]],
  P(p-neg-contra, s: 80%),

  [*De Morgan:* `∼(R ∪ S) = ∼R ∩ ∼S` — `Freyd.Alg.neg_union` (`:58`). \ #src[A cut round a tape
   equals a meet of two cuts. Nothing in this picture is a label: `∪`, `∩` and `∼` each have a shape,
   and the equation is the three of them rearranging.]],
  P(p-neg-union, s: 80%),

  [*De Morgan, other side* #text(9.2pt, luma(105))[(boolean)]: `∼(R ∩ S) = ∼R ∪ ∼S` —
   `Freyd.Alg.neg_inter` (`:131`). \ #src[Needs `∼∼R = R`: it is `neg_union` applied to `∼R`, `∼S`
   and then un-negated.]],
  P(p-neg-inter, s: 80%),

  [*excluded middle* #text(9.2pt, luma(105))[(boolean)]: `R ∪ ∼R = ⊤` — `Freyd.Alg.union_neg_eq_top`
   (`:139`). \ #src[`boolean_iff` (`:101`) is the converse: `∼∼` is the identity everywhere exactly
   when this holds everywhere. The two are one axiom, stated two ways.]],
  P(p-neg-excl, s: 80%),

  [*Schröder:* `R S ⊑ T ⟺ R° ∼T ⊑ ∼S` — `Freyd.Alg.schroeder_left` (`:181`); and
   `R S ⊑ T ⟺ ∼T S° ⊑ ∼R` — `Freyd.Alg.schroeder_right` (`:188`). \ #src[The workhorse of §4.5, and
   the picture is the clearest in this section: a two-box composite on the left, and on the right
   the *same* two boxes, one mirrored and both on black. Which factor keeps its orientation is which
   form you are in.]],
  stack(dir: ttb, spacing: 6pt, P(p-schroeder-l, s: 80%), P(p-schroeder-r, s: 80%)),

  [*division through negation:* `(∼R)/Y = ∼(R Y°)` — `Freyd.Alg.neg_div` (`:275`), which holds
   without the Boolean axiom; and `R/Y = ∼((∼R) Y°)` — `Freyd.Alg.div_eq_neg_comp` (`:293`), which
   needs it. \ #src[The cheatsheet's "neg. division" row, and the row that earns the notation: on
   the right of the second equation `/` has become a black region with a white island in it — a
   composite of the generators and two colour switches. In a Boolean allegory division is not
   independent structure at all.]],
  stack(dir: ttb, spacing: 6pt, P(p-neg-div, s: 80%), P(p-div-neg, s: 80%)),

  [*lexical order:* `⊤ ⨾ R = R` — `Freyd.Alg.topHom_thenRel` (`AOP/A4_4.lean:304`). \
   #src[`R ⨾ S ≜ R ∩ (R° ⇨ S)` (`:269`) — compare by `R`, break ties by `S`. Preorders are closed
   under it (`thenRel_transitive`, `:282`) and `⊤` is its unit, which is the cheatsheet's "unit
   `Π`".]],
  P(p-lex, s: 80%),

  [*Galois, point-free:* `f(x) ≼ y ⟺ x ⊴ g(y)` is `R f° = g S` — `Freyd.Alg.RelSet.galoisPF`
   (`AOP/A4_7_Galois.lean:36`), with `galois_iff` (`:63`) proving it equivalent to the pointwise
   form. \ #src[Stated in `Rel(Set)` rather than in an allegory, because the pointwise side needs
   elements; `graph f` is `f` as a relation. The picture is the point-free form's whole advantage —
   two composites, no quantifiers.]],
  P(p-galois, s: 80%),
)

*The measurement.* Twenty-one pictures. Nine show a cut, a meet or a tape — every row of the
negation table except the lexical order and the Galois connection — so §4.5 draws essentially in
full. The ten rows of the division table do not.

*And they cannot, at the generality Freyd states them.* This is the one thing to take from the
section. Every picture of `/` above goes through a complement: `R / S` drawn as a cut is `R ⨟• S⊥`,
and `S⊥` is `∼(S°)`. But division needs no complement. A `DivisionAllegory` (`Freyd/S2_30.lean:30`)
asks for one thing, the Galois connection `T ⊑ R/S ⟺ T S ⊑ R`, and `Rel(Set)` satisfies it with a
bare `∀`: `(R / S) x y ≜ ∀z. S y z → R x z` (`AOP/A6_1_RelSet.lean:157`), no negation anywhere in
the definition. `Rel` over a non-Boolean topos is a division allegory too, and there is no `∼` to
draw with at all.

The diagrammatic route buys the picture at a price, and the price is exactly Booleanness: the
paper's Prop. 6.5 is that *every homset of a first order bicategory is a Boolean algebra*. So the
dashed box on `DivisionAllegory.div` is not a gap in the notation waiting to be filled — it is the
correct picture. Restating these ten laws over `residual` would draw them, and would silently
replace each one by a strictly weaker theorem. `div_eq_neg_comp` is where the trade is made in the
open: it assumes `∼∼R = R` and gets `/` as two colour switches, and it is the only row here that
should.

*What is not drawn, and why.* The cheatsheet's pointwise row,
`x (T\U) y ⟺ ∀w. w T x ⟹ w U y`, quantifies over elements and has no arrow to draw; the strict part
`|R| ≜ R ∩ ∼R°` has no definition in the repo to export. Both are one-line additions if a later
section wants them — the first as a `Rel(Set)` lemma beside `galoisPF`, the second beside `neg`.
