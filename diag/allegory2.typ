// The PROOFS. diag/allegory-axioms.typ states the laws — formula, picture, example, one row each —
// and stops there; a chain of pictures with a rule under every step belongs beside it, not inside
// it. Same style file, so the two read as one document.
//
// EVERY PICTURE HERE IS EXPORTED, NOT DRAWN. `./scripts/diag-export --proof <decl>` walks the Lean
// PROOF and writes diag/generated/<decl>.proof.typ, which binds the steps to `branches`; this note
// only places them. `./scripts/diag-regen` redraws every binding below, reading the list off these
// very imports.
#import "note-style.typ": *
#import "generated/Freyd.Diag.modular_of_frobenius.typ": pic as p-modular
#import "generated/Freyd.Diag.modular_of_frobenius.proof.typ": branches as mfb
#import "generated/Freyd.Diag.CartBicat.«∇_slide_conv».typ": pic as p-nabla-slide
#import "generated/Freyd.Diag.CartBicat.«∇_slide_conv».proof.typ": branches as nsb
#import "generated/Freyd.Diag.CartBicat.«Δ≤?𝟙».typ": pic as p-cut-copy
#import "generated/Freyd.Diag.CartBicat.«∇≤𝟙!».typ": pic as p-cut-merge
#import "generated/Freyd.Diag.le_comp_conv_comp.proof.typ": branches as zzb
#import "generated/Freyd.Diag.le_comp_conv_comp_of_lax.proof.typ": branches as zzlax
#import "generated/Freyd.Diag.entire_inter_iff.typ": pic as p-entire, lhs as ent-a, rhs as ent-b
#import "generated/Freyd.Diag.entire_inter_iff.proof.typ": branches as entb
#import "generated/Freyd.Diag.shunt_right.typ": lhs as sr-a, rhs as sr-b
#import "generated/Freyd.Diag.shunt_right.proof.typ": branches as srb

#show: conf.with(title: "The allegory axioms: the proofs")

The companion to `allegory-axioms.typ`, which states these laws and their pictures. Here each one is
worked: the steps of the Lean proof, side by side, with the rule that reaches each under it.

= The modular law, from Frobenius

#table(
  columns: (5.4cm, 1fr, 5.8cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[*the modular law,* `R S ∩ T ≤ (R ∩ T S°) S` #h(8pt) #Pin(p-modular)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(mfb.at(0).terms.at(0)), P(mfb.at(0).steps.at(0), s: 62%),
  [*the start:* `R S ∩ T`.],

  raw(mfb.at(0).terms.at(1)), P(mfb.at(0).steps.at(1), s: 62%),
  [*Factor out the shared prefix:* `(R S) ⊗ T` is `(R ⊗ T) (S ⊗ 𝟙)`.],

  raw(mfb.at(0).terms.at(2)), P(mfb.at(0).steps.at(2), s: 62%),
  [*The merge slide.* `S` slides through the merge and reappears as `S°` on the other strand.
   #src[*The only inequality in the proof.*]],

  raw(mfb.at(0).terms.at(3)), P(mfb.at(0).steps.at(3), s: 62%),
  [*Fold the prefix back in;* the copy-merge pair reads as a meet again.],
)

`S` occurs once on the left of the slide and twice on the right, and the lax copy law is the only law
in the definition that may duplicate a box — so that is where the inequality has to be.

#table(
  columns: (5.4cm, 1fr, 5.8cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(
    Th[*the merge slide,* `(S ⊗ 𝟙) ▷ ≤ (𝟙 ⊗ S°) ▷ S` #h(8pt) #Pin(p-nabla-slide)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(nsb.at(0).terms.at(0)), P(nsb.at(0).steps.at(0), s: 62%),
  [*the start:* `(S ⊗ 𝟙) ▷`.],

  raw(nsb.at(0).terms.at(1)), P(nsb.at(0).steps.at(1), s: 62%),
  [*Rebuild the merge* from a copy and a right bracket, the shape the lax copy law applies to.],

  raw(nsb.at(0).terms.at(2)), P(nsb.at(0).steps.at(2), s: 62%),
  [*The lax copy law:* `S ◁` becomes `◁ (S ⊗ S)`, the box copied. #src[*The whole of the modular law,
   in one step.*]],

  raw(nsb.at(0).terms.at(3)), P(nsb.at(0).steps.at(3), s: 62%),
  [*Reshape back,* and the surviving duplicate slides round the right bracket to become `S°`.],
)

// One section, one page: the chain is only readable beside the two cuts it is made of.
#block(breakable: false, width: 100%)[
= `R ≤ R R° R`, by cutting two wires

Freyd reads this off the modular law #src[(§2.112)]: `R ⊑ 1R ∩ R ⊑ (1 ∩ R R°) R ⊑ R R° R`. In
pictures neither the modular law nor a meet with `1` is wanted. The one law that makes a picture
bigger is spent twice, and it is the cut, `𝟙 ≤ ⊸ ⟜`:

#grid(columns: (1fr, 1fr), gutter: 30pt, align: center + bottom,
  [#P(p-cut-copy, s: 60%) #v(-7pt) \ #src[cut the copy's left output and what comes out there is
   *anything at all*]],
  [#P(p-cut-merge, s: 60%) #v(-7pt) \ #src[cut the merge's right input and it is *simply
   discarded*]],
)

`R` is its own three-fold meet — three copies of the box between a copy tree and a merge tree — and
the two cuts turn the trees into a `⟜◁` and a `▷⊸`. The three boxes never move:

#chain(
  (zzb.at(0).steps.at(1), zzb.at(0).steps.at(2), zzb.at(0).steps.at(3), zzb.at(0).steps.at(4),
   zzb.at(0).steps.at(5)),
  ([`R ∩ R ∩ R = R`], [cut], [cut], [`⟜◁`, `▷⊸`], [that is `R°`]),
  s: 46%)

Read the last picture from the input, which is now the bottom strand: through the bottom box, up the
`▷⊸` and back along the middle box — which is that box turned round, so it is `R°` — down the `⟜◁`
and out along the top box. Where the meet had one input feeding all three boxes and one output
draining all three, the zig-zag has both of those *cut*, and a cut wire is the one thing this
calculus lets you add for free.
]

// The other route to the same containment.  Kept next to it because the interesting thing is what
// each one SPENDS, and that is only visible with both chains on the page.
#block(breakable: false, width: 100%)[
= The same, from the cap end

The section above cuts twice in its chain. This one cuts once and pays for the other cut with the
*lax copy law* — `R ◁ ≤ ◁ (R ⊗ R)`, the only law in the definition that may duplicate a box. Read
`𝟙` as a copy tree whose last two legs are capped back:

#chain(
  (zzlax.at(0).steps.at(2), zzlax.at(0).steps.at(4), zzlax.at(0).steps.at(6),
   zzlax.at(0).steps.at(7)),
  ([`◁ (◁ ⊗ 𝟙) (𝟙 ⊗ ▷⊸) = 𝟙`], [lax copy, twice], [cut], [that is `R°`]),
  s: 46%)

The three boxes are not there to begin with: there is one, and the two copy dots walk back *through*
it, leaving it behind three times. So the `▷⊸` is the frame's own cap before anything is cut, and
the copy tree is the only thing left to cut.

Neither chain is cheaper in what it *spends*. `◁ ▷ = 𝟙` is itself the merge cut, so the second
`𝟙 ≤ ⊸ ⟜` is underneath this one; `R ∩ R = R` is the lax copy law, so that is underneath the section
above. Both routes pay both. What differs is the *layer*: this chain names only the copy, the cap and
the box, so it holds as soon as the converse does — before `∩` exists. The section above climbs into
the meet semilattice and back down to state a containment in which no meet occurs.
]

= Entireness of an intersection

`R` is *entire* when `𝟙 ⊑ R R°`. When is an *intersection* entire?

#align(center, block(inset: (y: 6pt))[
  #P(p-entire, s: 80%) \
  #src[`Total (R ∩ S) ↔ 𝟙 ≤ R S°`]])

On the left `R ∩ S` is named *twice*; on the right `R` and `S` once each and the meet is gone. The
meet is needed to *ask* whether something is entire, not to *answer* it. Where `⊑` is *defined* as
`X ∩ Y = X` the two sides are one proposition; here `≤` is primitive, so both directions are real
steps — and they cost very different things.

#table(
  columns: (5.0cm, 1fr, 6.0cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*`⟹`* #h(6pt) given `R ∩ S` entire, #Pin(ent-a)
    #h(6pt) show #Pin(ent-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(entb.at(0).terms.at(0)), P(entb.at(0).steps.at(0), s: 68%), [*the start:* `𝟙`.],
  raw(entb.at(0).terms.at(1)), P(entb.at(0).steps.at(1), s: 68%),
  [*the hypothesis:* `𝟙 ≤ P P°` at `P = R ∩ S`.],
  raw(entb.at(0).terms.at(2)), P(entb.at(0).steps.at(2), s: 68%),
  [*monotonicity, twice.* #src[No modular law.]],
)

#table(
  columns: (5.0cm, 1fr, 6.0cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*`⟸`* #h(6pt) given #Pin(ent-b) #h(6pt) show
    `R ∩ S` entire, #Pin(ent-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(entb.at(1).terms.at(0)), P(entb.at(1).steps.at(0), s: 68%), [*the start:* `𝟙`.],

  raw(entb.at(1).terms.at(1)), P(entb.at(1).steps.at(1), s: 68%),
  [*the hypothesis,* met with `𝟙`.],

  raw(entb.at(1).terms.at(2)), P(entb.at(1).steps.at(2), s: 68%),
  [`𝟙 ∩ R S° = 𝟙 ∩ (S ∩ R)(S ∩ R)°`. #src[`R S°` relates `a` to `a′` when some `b` has `a R b` and
   `a′ S b`; the `𝟙 ∩` sets `a′ = a`, and it reads "some `b` has `a R b` and `a S b`" — one arrow of
   `R ∩ S`. Two arrows become one, and that is what needs the modular law.]],

  raw(entb.at(1).terms.at(3)), P(entb.at(1).steps.at(3), s: 68%),
  [*`X ∩ Y ≤ Y`,* then `S ∩ R = R ∩ S`.],
)

= The shunting rule

A map moves from one side of a containment to the other at the cost of its converse,
`R f ≤ S ⟺ R ≤ S f°`. It is how a function gets out of the way so the relation underneath can be
reasoned about. Each direction spends exactly one half of *map* — never both.

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting right, `⟹`* #h(6pt) given #Pin(sr-a) #h(4pt)
    show #Pin(sr-b)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(srb.at(0).terms.at(0)), P(srb.at(0).steps.at(0), s: 74%), [*the start:* `R`.],
  raw(srb.at(0).terms.at(1)), P(srb.at(0).steps.at(1), s: 74%),
  [*total:* `𝟙 ≤ f f°`, so `f f°` may be inserted after `R`.],
  raw(srb.at(0).terms.at(2)), P(srb.at(0).steps.at(2), s: 74%),
  [Re-bracket to `(R f) f°` and apply the hypothesis.],
)

#table(
  columns: (4.4cm, 1fr, 6.4cm),
  align: (left + horizon, center + horizon, left + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header(Th[*shunting right, `⟸`* #h(6pt) given #Pin(sr-b) #h(4pt)
    show #Pin(sr-a)],
    [*term*], [*picture*], [*the rule that reaches it*]),

  raw(srb.at(1).terms.at(0)), P(srb.at(1).steps.at(0), s: 74%), [*the start:* `R f`.],
  raw(srb.at(1).terms.at(1)), P(srb.at(1).steps.at(1), s: 74%),
  [Apply the hypothesis on the left; the two `f`s are now adjacent.],
  raw(srb.at(1).terms.at(2)), P(srb.at(1).steps.at(2), s: 74%),
  [*single valued:* `f° f ≤ 𝟙`, so the pair cancels.],
)

Shunting left is the mirror, same shape, map on the other side throughout. What the rule is, is an
adjunction: `f ⊣ f°`, with *total* the unit and *single valued* the counit, so "`f` is a map" and
"`f` has a right adjoint, namely `f°`" are one statement.
