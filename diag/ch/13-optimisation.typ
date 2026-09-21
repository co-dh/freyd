#import "../note-prelude.typ": *
#show: note-chapter.with(13)
// note-split: chapter 13 — this header is written by scripts/note-split and stripped by scripts/note-join
= Optimisation Problems <sec-opt>

== `est(R)≜∋∩(∈\R°)` <sec-est>

// B&dM §7.1, p. 166.
#disp[#definition[
For `R : A⟶A`, #h(4pt) `est(R)≜∋∩(∈\R°) : EA⟶A` #h(4pt) #src[`X⊑∈\R°⟺∈X⊑R°`, and `∈X` runs `y⟶xs⟶x`, member first, so its pair `(y,x)` is in `R°` exactly when `x R y`; at `R≜≤` that is `x≤y` for every `y∈xs`, the least — `∈\≤` would give `y≤x`, the greatest].
// lean:AOP.A7_1.est@e39806f8

`xs (est(R)) x⟺x∈xs∧(∀y∈xs. x R y)` #h(4pt) #src[the same predicate under the same
letter, `min R`, so `est(R)=min(R°)` once `R` is an arrow;
]
// lean:AOP.A7_4_Horner.est_apply@91dc1299
// B&dM's `min R` has `R : A⟵A` reading `x R y` as the arrow `y⟶x`, ours `R : A⟶A` reading `x⟶y`.

`xs (est(R)) x⟺(x in xs) and all x R\: xs` #h(4pt) #src[in q]

`est(R)=∋∩all R°` #h(4pt) #src[`all R≜∈\R`, q's `all`; the chains below keep it written `∈\`]

`E(R)≜` $frac(#[`∋R`], ∋)$ ` : EA⟶EB`, #h(4pt) `xs E(R) ys⟺ys={y∣∃x∈xs. x R y}` #h(4pt)
#src[the image of `xs`, @pow-laws]

`P(R) : EA⟶EB`, #h(4pt) `xs P(R) ys⟺(∀x∈xs. ∃y∈ys. x R y)∧(∀y∈ys. ∃x∈xs. x R y)` #h(4pt)
#src[every `x` and every `y` has a partner, @powrel-readings]
]]<est-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X⊑est(R)⟺X⊑∋` and `X°∋⊑R`], [in the set, and below every element of it],
  [$frac(#[`𝟙`], ∋)$ `(∈\R)=R`], [bounding a singleton is bounding its element],
  [$frac(#[`S`], ∋)$ `(∈\R)=S°\R`], [bound `S`'s image without building the set],
  [`union≜` $frac(#[`∋∋`], ∋)$ `: E(EA)⟶EA`], [flattens a set of sets],
  [`union (∈\R)=∈\(∈\R)`], [bound a union by bounding each member set],
  [$frac(#[`𝟙`], ∋)$ `est(R)=𝟙∩R°`],
 [a singleton's minimum is its element, where `R` is reflexive \ #src[$frac(#[`S`], ∋)$ `est(R)` at `S:=𝟙`]],
  // lean:AOP.A7_1.singletonMap_comp_est@06b2ed05
  [$frac(#[`S`], ∋)$ `est(R)=S∩(S°\R°)`], [an `S`-value that points to every `S`-value],
  [$frac(#[`S`], ∋)$ `est(R)=` $frac(#[`S`], ∋)$ `est(R∩S°S)`], [only `R` between values `S` gives one argument counts — context],
  [`E(S) est(R)=(∋S)∩((∋S)°\R°)`],
  [the same for the image of a set \ #src[$frac(#[`S`], ∋)$ `est(R)` at `S:=∋S`]],
  [`P(f) est(R)=est(fRf°) f`], [shunt a function through a minimum],
  [`P(S) est(R)=(∋S)∩(∈\(SR°))` \ #src[`R` reflexive]],
  [fusion with the power relator \ #src[`⊒` is the only proof here that tabulates]],
  [`P(S) est(R)⊑(∋S)∩(∈\(SR°))`], [the half of the row above that costs nothing],
  [`P(est(R)) est(R)⊑union est(R)` \ #src[`R` transitive]],
  [a minimum in each set, then a minimum of those],
  [`P(est(R)) est(R)=P(Dom(est(R))) union est(R)` \ #src[`R` transitive]],
  [the same as an equality, once empty sets are dropped],
)]<est-laws>

=== `X⊑est(R)⟺X⊑∋` and `X°∋⊑R`

// The definition read through the two adjunctions it is built from.  B&dM p. 166 cites this as the
// hint "universal property of min", which the chains below cite as "UP of `est`".
#disp[
#zline(
  zsqc(`X`, `est(R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zpair(zsqc(`X`, `∋`), zsqc(`X`, `∈\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zpair(zsqc(`X`, `∋`), zsqc(`∈X`, `R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zpair(zsqc(`X`, `∋`), zsqc(`X°∋`, `R`)),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.le_est_iff@81855810
]<est-up>

=== $frac(#[`𝟙`], ∋)$ `(∈\R)=R`

// B&dM (7.1): the same four steps as the subsection below, with `(𝟙%∋) ∋ = 𝟙` — the `i ⊣ E` triangle —
// where that one has `(S%∋) ∋ = S`.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`𝟙`], ∋)$ `(∈\R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`𝟙`], ∋)$`°X`], `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc([`∈` $frac(#[`𝟙`], ∋)$`°X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc([`(`$frac(#[`𝟙`], ∋)$` ∋)°X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`i⊣E`],
  zsqc(`X`, `R`),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.singletonMap_comp_lb@9d4759cf
]<est-71>

=== $frac(#[`S`], ∋)$ `(∈\R)=S°\R`

$frac(#[`S`], ∋)$ gathers the `S`-image of a point into one set and `∈\R` asks that every member of
that set be `R`-related to the target, so the set cancels and `S°\R` asks it of the `S`-image
directly.

// B&dM (7.2): two adjunctions composed, `(S%∋) ∋ = S` collapsing the middle — the shape of (1.2a).
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `(∈\R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`S`], ∋)$`°X`], `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc([`∈` $frac(#[`S`], ∋)$`°X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc([`(`$frac(#[`S`], ∋)$ `∋)°X`], `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`S°X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc(`X`, `S°\R`),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.Λ_comp_lb@f14ab8b5
]<est-72>

=== `union (∈\R)=∈\(∈\R)`

// B&dM (7.3): the shape of the two chains above with `union ∋ = ∋ ∋` in the middle.
#disp[
#zline(
  zsqc(`X`, `union (∈\R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc(`union° X`, `∈\R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`],
  zsqc(`∈union° X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`],
  zsqc(`(union∋)°X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`(∋∋)°X`, `R`),
  zstep(op: sym.arrow.l.r.double, under: true)[`°`, `T·⊣T\`],
  zsqc(`X`, `∈\(∈\R)`),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.bigUnion_comp_lb@ed13dc7a
]<est-73>

=== $frac(#[`S`], ∋)$ `est(R)=S∩(S°\R°)`

// B&dM (7.5).  (7.4) is this at `S := 𝟙` and (7.7) at `S := ∋ S`, so neither needs a chain of its own.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `est(R)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zsqc([$frac(#[`S`], ∋)$`°X`], `est(R)`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zpair(zsqc([$frac(#[`S`], ∋)$`°X`], `∋`), zsqc([$frac(#[`S`], ∋)$`°X`], `∈\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`f°·⊣f·`],
  zpair(zsqc(`X`, [$frac(#[`S`], ∋)$ `∋`]), zsqc(`X`, [$frac(#[`S`], ∋)$ `(∈\R°)`])),
  zstep(op: sym.arrow.l.r.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, @est-72],
  zpair(zsqc(`X`, `S`), zsqc(`X`, `S°\R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`],
  zsqc(`X`, `S∩(S°\R°)`),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.Λ_comp_est@4c6d38d0
]<est-75>

=== $frac(#[`S`], ∋)$ `est(R)=` $frac(#[`S`], ∋)$ `est(R∩S°S)`

// B&dM (7.6): `X ⊑ S` already forces `S° X ⊑ S° S`, so the extra conjunct costs nothing — that is
// the whole content, and it is the middle step.
#disp[
#zline(
  zsqc(`X`, [$frac(#[`S`], ∋)$ `est(R∩S°S)`]),
  zstep(op: sym.arrow.l.r.double, under: true)[@est-75, `°`],
  zsqc(`X`, `S∩(S°\(R°∩S°S))`),
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`X`, `S`), zsqc(`S°X`, `R°∩S°S`)),
)
// Six boxes on one row squeezed the wide ones into three lines each; the break is at the pair.
#zline(
  zstep(op: sym.arrow.l.r.double, under: true)[`Δ⊣∩`, `S°·` monotone],
  zpair(zsqc(`X`, `S`), zsqc(`S°X`, `R°`)),
  zstep(op: sym.arrow.l.r.double, under: true)[`T·⊣T\`, `Δ⊣∩`],
  zsqc(`X`, `S∩(S°\R°)`),
  zstep(op: sym.arrow.l.r.double, under: true)[@est-75],
  zsqc(`X`, [$frac(#[`S`], ∋)$ `est(R)`]),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.Λ_comp_est_context@e8052cf4
]<est-76>

=== `P(f) est(R)=est(fRf°) f`

// B&dM (7.8), shunting a map through a minimum.  The one step that is not an adjunction is the
// modular law, and it needs `f` simple — the only such step in §@sec-est.
// No marker: (7.8) is one of the statements AOP/A7_1.lean drops (its closing block note).
#disp[
#zline(
  zsqc(`P(f) est(R)`, none, name: "f a map"),
  zstep(op: sym.eq, under: true)[`P=E` on maps, @est-75],
  zsqc(`(∋f)∩((∋f)°\R°)`, none),
  zstep(op: sym.eq, under: true)[`°`, `T·⊣T\`, `f°·⊣f·`],
  zsqc(`(∋f)∩(∈\(fR°))`, none),
)
// An operator is stretched to the reason's UNWRAPPED width, so a reason squeezed onto two lines
// overhangs the boxes beside it; the breaks below keep each reason on one line.
#zline(
  zstep(op: sym.eq, under: true)[modular law, `f` simple],
  zsqc(`(∋∩((∈\(fR°))f°))f`, none),
  zstep(op: sym.eq, under: true)[`·f⊣·f°`, `°`, `est`],
  zsqc(`est(fRf°) f`, none),
)
]<est-78>

=== `P(S) est(R)⊑(∋S)∩(∈\(SR°))`

// B&dM (7.10): `∋` is lax natural for the power relator, `P(S) ∋ ⊑ ∋ S`, and with the universal
// property of `est` that is the whole proof.  The equality (7.9) is not this — it needs tabulations.
#disp[
#zline(
  zsqc(`P(S) est(R)`, `(∋S)∩(∈\(SR°))`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(S) est(R)`, `∋S`), zsqc(`∈P(S) est(R)`, `SR°`)),
  zstep(op: sym.arrow.l.double, under: true)[UP of `est`],
  zpair(zsqc(`P(S)∋`, `∋S`), zsqc(`∈P(S)`, `S∈`)),
)
#align(center, block(inset: (y: 4pt))[#src[]])
// lean:AOP.A7_1.powerRel_comp_est_le@d8b5692c
]<est-710>

=== `P(est(R)) est(R)⊑union est(R)`

// B&dM (7.11): (7.5) at `S := ∋ ∋` opens the right-hand side, then the same two facts as (7.10)
// close both strands — the left one twice, the right one against transitivity.
#disp[
#zline(
  zsqc(`P(est(R)) est(R)`, `union est(R)`, name: "R transitive"),
  zstep(op: sym.arrow.l.r.double, under: true)[@est-75],
  zsqc(`P(est(R)) est(R)`, `(∋∋)∩((∋∋)°\R°)`),
  zstep(op: sym.arrow.l.double, under: true)[`°`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(est(R)) est(R)`, `∋∋`), zsqc(`∈∈P(est(R)) est(R)`, `R°`)),
  zstep(op: sym.arrow.l.double, under: true)[UP of `est`, `R` transitive],
  zpair(zsqc(`P(est(R))∋`, `∋est(R)`), zsqc(`∈P(est(R))`, `est(R)∈`)),
)
#align(center, block(inset: (y: 4pt))[#src[, `R` transitive]])
// lean:AOP.A7_1.powerRel_est_le_bigUnion@d0c726a1
]<est-711>

#pagebreak(weak: true)
== Lax natural transformations (LaT)

// B&dM §5.7, p. 133.  Same `⇒` the note gives an ordinary natural transformation: B&dM's own hooked
// arrow marks laxness, but the word already does, and the inequation is right there.
#disp[#definition[
For relators `G,F : 𝒞⟶𝓓` and components `φ`#sub[`A`]` : GA⟶FA`, `φ` is *lax at*
`R : A⟶B` when #h(4pt) `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) — both sides `GA⟶FB`, the
left through the component at `B`, the right through the one at `A`.

`φ : G⇒F` is a *lax natural transformation* (LaT) when it is lax at *every* `R`. #h(4pt) #src[(5.13)]

Lax at every *map* already gives LaT, and at a map the inequation is an equality #h(4pt)
`G(f)φ=φF(f)`: #h(4pt) laxness is about relations only.
// lax-defn row: Theorem 5.2
#h(4pt) #src[]
// lean:AOP.A5_7.laxNatural_iff_strict_on_maps@e374cc23
]]<lax-defn>

// The two panels of the inequation, emitted by `./scripts/diagram --sigs … --src … --tgt …` plus
// `s: 100%`, the square's own size.  `φ` is `!lax`: the HOLLOW dot is the whole difference from a
// natural transformation's filled one, and it is why `φ` may leave the object wire at all — a LaT is
// a family, not an arrow at one object.  The bead is BARE, as §11.4's `α` is: the component's index
// is the object wire it stands on, and the two panels differ in exactly where that wire is renamed.
#let lax-hm-l = lean("Freyd.Alg.LaxNatural.lhs")
#let lax-hm-r = lean("Freyd.Alg.LaxNatural.rhs")

#disp[#pair(
  leancd("Freyd.Alg.LaxNatural"),
  row((lax-hm-l, [#h(7pt) #SQ #h(7pt)], lax-hm-r)),
 [`G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #src[]],
)]<lax-str>

// Not in B&dM §5.7, which stops at Theorem 5.2.

// Hinze–Marsden at the 2-category level: a REGION is an allegory, a WIRE a relator, a BEAD a
// LaT.  Regions are `LATP` wide, so the wire carrying the bead stands at the same pitch in every cell.
#let LATP = 1.15
#let LATH = 2.5
#let LATB = 1.35
#let latcol(i, j) = ((i * LATP, LATH), (j * LATP, LATH), (j * LATP, 0), (i * LATP, 0))
#let latpic(regions, wires, beads: (), ports: (), marks: (), names: (), s: 74%) = P(
  cetz.canvas(length: 0.8cm, {
    for (f, pts) in regions { hm-region(pts, f) }
    for pts in wires { hm-wire(pts) }
    // `side` is which way the name hangs off the dot, `dy` lifts it clear of a strand leaving there.
    for (p, l, side, dy) in beads {
      hm-bead(p, l, dx: side * 0.32, dy: dy, anchor: if side > 0 { "west" } else { "east" })
    }
    for (p, l, dir) in ports { hm-port(p, l, dir: dir) }
    // A relator between two beads has no box edge to be named at, so its name goes beside the wire.
    for (p, l) in marks { d.content((p.at(0) + 0.3, p.at(1)), text(black)[#l], anchor: "west") }
    for (p, l) in names { hm-name(p, l) }
  }),
  s: s,
)

#disp[#table(
  columns: (4.8cm, 10.6cm, 6.6cm),
  align: (left + horizon, center + horizon, center + horizon),
  // `y: 2pt`: the LaT letters wrap two of the statement lines, and at 5pt the table outgrew the page —
  // a `#disp` table cannot break, so the last row was laid over the one above it.
  inset: (x: 9pt, y: 2pt), stroke: 0.4pt + luma(190),
  table.header([*closed under*], [*commutative diagram*], [*string diagram*]),

  [composition \ `ψφ`],
  [#P(leancd("Freyd.Alg.laxNatural_comp_slide"), s: 74%)
   `H(R)ψ`#sub[`B`]`⊑ψ`#sub[`A`]`G(R)` #h(4pt) and #h(4pt) `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)`
   #h(4pt) give #h(4pt) `H(R)(ψ`#sub[`B`]`φ`#sub[`B`]`)⊑(ψ`#sub[`A`]`φ`#sub[`A`]`)F(R)`],
  latpic(
    ((fb-ALLC, latcol(0, 1)), (fb-ZC, latcol(1, 2))),
    (((LATP, LATH), (LATP, 0)),),
    beads: (((LATP, 1.75), [`ψ`], 1, 0), ((LATP, 0.75), [`φ`], 1, 0)),
    ports: (((LATP, LATH), [`H`], 1), ((LATP, 0), [`F`], -1)),
    marks: (((LATP, 1.25), [`G`]),),
    names: (((0.5 * LATP, 0.3), [`𝓓`]), ((1.5 * LATP, 0.3), [`𝒞`])),
  ),

  [horizontal composition \ `χ∘φ`],
  [#P(leancd("Freyd.Alg.laxNatural_hcomp_outer_first"), s: 74%)
   `φ : G⇒F` with `G,F : 𝒞⟶𝓓` and `χ : L⇒K` with `L,K : 𝓓⟶𝓔` give
   `χ∘φ : L∘G⇒K∘F`, the family `A ↦ χ`#sub[`GA`]`K(φ`#sub[`A`]`)` \
   #src[`L(G(R))χ`#sub[`GB`]`⊑χ`#sub[`GA`]`K(G(R))` is `χ` lax at `G(R)`; then
   `K(G(R)φ`#sub[`B`]`)⊑K(φ`#sub[`A`]`F(R))` is `K` applied to `φ`'s own inequation;
 ] \
   // lean:AOP.A5_7.laxNatural_hcomp_outer_first@ce6a24d8
   #src[`χ:=𝟙`#sub[`K`] gives `K(φ) : K∘G⇒K∘F`, `K` composed on the outside;
   `φ:=𝟙`#sub[`G`] gives `χG : L∘G⇒K∘G`, `G` composed on the inside] \
   #src[two candidates, `χ`#sub[`GA`]`K(φ`#sub[`A`]`)` and `L(φ`#sub[`A`]`)χ`#sub[`FA`], ordered by
   `⊑`; this row is the first]],
  // Two wires side by side, a bead on each; an identity 2-cell is a bare wire, so dropping the left
  // bead leaves `K(φ)` and dropping the right one leaves `χG` — the two cases that had rows of their own.
  latpic(
    ((fb-MAPC, latcol(0, 1)), (fb-ALLC, latcol(1, 2)), (fb-ZC, latcol(2, 3))),
    (((LATP, LATH), (LATP, 0)), ((2 * LATP, LATH), (2 * LATP, 0))),
    beads: (((LATP, LATB), [`χ`], 1, 0), ((2 * LATP, LATB), [`φ`], 1, 0)),
    ports: (((LATP, LATH), [`L`], 1), ((LATP, 0), [`K`], -1),
      ((2 * LATP, LATH), [`G`], 1), ((2 * LATP, 0), [`F`], -1)),
    names: (((0.5 * LATP, 0.3), [`𝓔`]), ((1.5 * LATP, 0.3), [`𝓓`]), ((2.5 * LATP, 0.3), [`𝒞`])),
  ),

  [union \ `φ ∪ ψ`],
  [#P(leancd("Freyd.Alg.laxNatural_union"), s: 74%)
   `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) and #h(4pt) `G(R)ψ`#sub[`B`]`⊑ψ`#sub[`A`]`F(R)`
   #h(4pt) give #h(4pt) `G(R)(φ`#sub[`B`]` ∪ ψ`#sub[`B`]`)⊑(φ`#sub[`A`]` ∪ ψ`#sub[`A`]`)F(R)`
 #h(4pt) #src[]],
   // lean:AOP.A5_7.union_slides@f7484fb4
  align(center, grid(columns: 3, align: horizon, column-gutter: 2pt,
    latpic(
      ((fb-ALLC, latcol(0, 1)), (fb-ZC, latcol(1, 2))),
      (((LATP, LATH), (LATP, 0)),),
      beads: (((LATP, LATB), [`φ`], 1, 0),),
      ports: (((LATP, LATH), [`G`], 1), ((LATP, 0), [`F`], -1)),
    ),
    [`∪`],
    latpic(
      ((fb-ALLC, latcol(0, 1)), (fb-ZC, latcol(1, 2))),
      (((LATP, LATH), (LATP, 0)),),
      beads: (((LATP, LATB), [`ψ`], 1, 0),),
      ports: (((LATP, LATH), [`G`], 1), ((LATP, 0), [`F`], -1)),
    ),
  )),

  [a relator `K` \ `K(φ)`],
  [#P(leancd("Freyd.Alg.Relator.map_laxNatural"), s: 74%)
   `G(R)φ`#sub[`B`]`⊑φ`#sub[`A`]`F(R)` #h(4pt) gives #h(4pt)
   `K(G(R))K(φ`#sub[`B`]`)⊑K(φ`#sub[`A`]`)K(F(R))`],
  [],

  [product \ `φ×ψ`],
  [#P(leancd("Freyd.Alg.laxNatural_prod"), s: 74%)
   `φ : G⇒F` and `ψ : G'⇒F'` give `φ×ψ : G×G'⇒F×F'` \
   #src[`(R×S)(U×V)=(RU)×(SV)` and monotonicity in both slots — the row above's `K` applied to the
   inequation, run on a bifunctor; the fork is the derived case `⟨φ,ψ⟩=◁(φ×ψ)`, and its ONE cost is
   the lax copy law `R◁⊑◁(R×R)` — @rel-monoid]],
  // `G×G'=×∘⟨G,G'⟩`: two UNARY functors, so the split is typed — `⟨G,G'⟩ : 𝒞⟶𝓓×𝓓` then `× : 𝓓×𝓓⟶𝓓`.
  // The bead is the PAIR in `𝓓×𝓓`, written `(φ,ψ)`: the fork `⟨φ,ψ⟩=◁(φ×ψ)` is a different arrow, in `𝓓`.
  latpic(
    ((fb-ALLC, latcol(0, 1)), (fb-MAPC, latcol(1, 2)), (fb-ZC, latcol(2, 3))),
    (((LATP, LATH), (LATP, 0)), ((2 * LATP, LATH), (2 * LATP, 0))),
    beads: (((2 * LATP, LATB), [`(φ,ψ)`], 1, 0),),
    ports: (((LATP, LATH), [`×`], 1), ((LATP, 0), [`×`], -1),
      ((2 * LATP, LATH), [`⟨G,G'⟩`], 1), ((2 * LATP, 0), [`⟨F,F'⟩`], -1)),
    names: (((1.5 * LATP, 0.3), [`𝓓×𝓓`]),),
  ),

  [coproduct \ `φ+ψ`],
  [#P(leancd("Freyd.Alg.laxNatural_sum"), s: 74%)
   `φ : G⇒F` and `ψ : G'⇒F'` give `φ+ψ : G+G'⇒F+F'` \
   #src[`(R+S)(U+V)=(RU)+(SV)` and monotonicity in both slots; the co-fork is the derived case
   `[φ,ψ]=(φ+ψ)▿`, and `▿` costs nothing]],
  // `+`, like `×`, is a functor `𝓓×𝓓⟶𝓓`, so the picture is the one above with `+` on the left wire.
  latpic(
    ((fb-ALLC, latcol(0, 1)), (fb-MAPC, latcol(1, 2)), (fb-ZC, latcol(2, 3))),
    (((LATP, LATH), (LATP, 0)), ((2 * LATP, LATH), (2 * LATP, 0))),
    beads: (((2 * LATP, LATB), [`(φ,ψ)`], 1, 0),),
    ports: (((LATP, LATH), [`+`], 1), ((LATP, 0), [`+`], -1),
      ((2 * LATP, LATH), [`⟨G,G'⟩`], 1), ((2 * LATP, 0), [`⟨F,F'⟩`], -1)),
    names: (((1.5 * LATP, 0.3), [`𝓓×𝓓`]),),
  ),

  [meet — *fails* \ `φ∩ψ`],
  [#src[the step it would need is
   `(φ`#sub[`A`]`F(R))∩(ψ`#sub[`A`]`F(R))⊑(φ∩ψ)`#sub[`A`]`F(R)`, the wrong direction of
   @meet-semidistrib] \
   #src[a counterexample: @meet-counterex]],
  [],

  table.cell(colspan: 3, align: left + horizon)[Each row is the general slide #h(4pt)
   `R`#sub[`A`]`X⊑X'R`#sub[`B`] and `R`#sub[`B`]`Y⊑Y'R`#sub[`C`] give
   `R`#sub[`A`]`(XY)⊑(X'Y')R`#sub[`C`] #h(4pt) at `R`#sub[`A`]`,R`#sub[`B`]`:=G(R),F(R)` and
   `X,X':=φ`#sub[`B`]`,φ`#sub[`A`], quantified over `R`; at `X'=X` with `R`#sub[`A`]`,R`#sub[`B`]
   endorelations it is the monotonicity reading instead — the `∀R` sits outside the law, and is the
 only difference #h(4pt) #src[]],
   // lean:AOP.A5_7.comp_slides@480a3dc9
)]<lax-closure>

// `sticky` binds a heading to the next BLOCK, and `conf` wraps every display in a breakable one, so
// the heading stays behind while the picture moves on: the break has to be placed by hand.
#pagebreak(weak: true)
=== meet is not closed in LaT

// diag/natsq.typ's idiom for a square that FAILS: ONE COLOUR PER ROUTE — here `GIVEN1`/`GIVEN2` mark
// across-then-down and down-then-across, not horizontal/vertical — and the traced element's values
// wear their route's colour, so the two results are read off without following the arrows.
// `breakable: false`: `conf` makes every display breakable, and the claim line broke away from its
// own picture at the foot of a page.
#disp[#block(breakable: false)[
#align(center, strong[counterexample — `φ,ψ : G⇒F` lax natural does NOT give `φ∩ψ` lax natural])
#v(4pt)
#capbox(
  leancd("Freyd.Alg.inter_not_laxNatural_square"),
  [`A=B≜{0,1}`, #h(4pt) `R≜{(0,0),(1,0)}`, #h(4pt) `φ≜π₁∩π₂ : Δ⇒Id` \
   `π₁,π₂ : Δ⇒Id` are both LaTs #h(4pt) #src[@party-mono-branch's `g` row] #h(4pt) and
 `π₁∩π₂={((x,x),x)}` #h(4pt) #src[]],
   // lean:AOP.A6_1_OrdRelSet.laxNatural_inter_false@bcff53dc
)]]<meet-counterex>

=== Two stacked towers

// TWO towers, not one four-level ladder: `R⊑S` is the LOWER tower's 2-cell, and the whole lower
// tower is one 0-cell of the upper.  Drawn together because that containment is the only thing that
// answers "where did the ordinary `⊑` go".
#disp[
#table(
  columns: (2.2cm, 5.5cm, 1fr),
  align: (center + horizon, left + horizon, left + horizon),
  inset: (x: 9pt, y: 5pt), stroke: 0.4pt + luma(190),
  table.header([], [*lower — inside ONE allegory*], [*upper — between allegories*]),

  [`0`-cell], [an object `A`],
  [an allegory `𝒞` #h(4pt) — *a whole lower tower*],

  [`1`-cell], [a relation `R : A⟶B`], [a relator `F : 𝒞⟶𝓓`],

  [`2`-cell], [`R⊑S`], [a LaT `φ : G⇒F` #h(4pt) #src[@lax-defn]],

  [order], [`R⊑S`], [`φ⊑ψ` componentwise],

  [union], [`R ∪ S`], [`φ ∪ ψ`, *survives* #h(4pt) #src[@lax-closure]],

  [product], [`R×S` #h(4pt) #src[@relprod-defn]],
  [`φ×ψ`, *survives*; a TENSOR, not a categorical product; SYMMETRIC
   #h(4pt) #src[@fork-proj] #h(4pt) #src[@lax-closure]],

  [coproduct], [`R+S`],
  [`φ+ψ`, *survives*; a BIPRODUCT #h(4pt) #src[@lax-closure]],

  [meet], [`R∩S`],
  [`φ∩ψ` componentwise, *fails* #h(4pt) #src[@meet-counterex]],

  [converse], [`R°`],
  [`φ°`, *fails*, oplax: `φ`#sub[`A`]`°G(R)⊑F(R)φ`#sub[`B`]`°`
 #h(4pt) #src[]],
   // lean:AOP.A5_7.recip_oplax@7735eec0 lean:AOP.A6_1_OrdRelSet.recip_not_laxNatural@1983c3f6

  [zero object], [`z` with `𝟙 z=𝟘`],
  [the constant relator at such a `z`, initial and terminal],
)
]<lat-tower>


=== `R⊑S` is a special case of LaT

// @lax-str's square three times over, at the base arrow `R : X⟶Y`: general, then at the two constant
// relators, then with the identity verticals gone.  Identity verticals are what turn a square into a
// comparison of its two horizontals, so the collapse is drawn, not asserted.
#disp[#capbox(
  row((leancd("Freyd.Alg.LaxNatural"), [#h(9pt) #sym.arrow.r.double.long #h(9pt)],
       leancd("Freyd.Alg.laxNatural_const_iff.lhs"),
       [#h(9pt) #sym.arrow.r.double.long #h(9pt)],
       leancd("Freyd.Alg.laxNatural_const_iff.rhs"))),
  [`G≜const A`, #h(4pt) `F≜const B` #h(4pt) — the relators `X↦A` and `X↦B`, each sending every arrow
   to `𝟙` #h(4pt) #src[@lax-defn] \
   with `𝒞` two objects and one non-identity arrow `X⟶Y`, a LaT `const A⇒const B` is the pair
   `φ`#sub[`X`]`,φ`#sub[`Y`]` : A⟶B` with `φ`#sub[`Y`]`⊑φ`#sub[`X`] #h(4pt) — the datum `R⊑S` \
   not every LaT is constant: #h(4pt) `∋ : P⇒Id` #h(4pt) #src[@powrel-laws] #h(4pt)
   `π₂ : (A×−)⇒Id` #h(4pt) #src[@subseq-outr-square] #h(4pt) `◁ : Id⇒Δ` #h(4pt) #src[@rel-monoid]],
  // lean:AOP.A5_7.laxNatural_const_iff@4af68018
)]<lat-const>

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
// would sit alone at the foot of §13.2's last page.
#pagebreak(weak: true)
== Monotonic algebras

// B&dM §7.2, p. 172.  The section numbers no equation, so the table names its theorem instead;
// Theorem 7.1 is the subsection below, which states and proves it.
#disp[#definition[
An F-algebra `φ : FA⟶A` is *monotonic on* `R : A⟶A` when it is lax at `R` at #h(4pt)
`G:=F`, `F:=Id`: #h(4pt) `F(R)φ⊑φR`. #h(4pt) `R` is an *endorelation*, so `B=A` and
the two components `φ`#sub[`A`], `φ`#sub[`B`] are the one arrow `φ` — an algebra, not a family.

For a map `f : FA⟶A` that is #h(4pt) `f°F(R)f⊑R` #h(4pt) #src[@adj-all's `f°·⊣f·` at `X:=F(R)f`,
`Y:=R`], #h(4pt) equivalently #h(4pt)
// lean:AOP.A7_2.monotonicAlg_iff_conj@46638b64
`F(R)⊑fRf°` #h(4pt) #src[`·f⊣·f°` then `f°·⊣f·`,
].
// lean:AOP.A7_2.monotonicAlg_iff_sandwich@f82f1b18

`(≤×≤)+⊑+≤` — addition on `Nat` is monotonic on `≤`, which at the point level
reads #h(4pt) `c=a+b∧a≤a'∧b≤b'⟹c≤a'+b'`.
]]<mon-defn>

// @lax-hm-l/@lax-hm-r at `G := F`, `F := Id`, emitted by
// `./scripts/diagram --frame 4 --sigs "φ:F(A)⟶A R:A⟶A"` plus `s: 100%`, with `--top 3` on the left
// so `φ` lands on one row either side: the algebra bead stands still while `R` walks out of the
// functor and down past it.  `φ` is an arrow at the one object `A`, not a family, so its dot rides
// the object wire and carries no `"lax"` — that is where it differs from @lax-str's spider.
#let mon-hm-l = lean("Freyd.Alg.MonotonicAlg.lhs")
#let mon-hm-r = lean("Freyd.Alg.MonotonicAlg.rhs")

// @lax-str at `G := F`, `F := Id`: the right edge's `Id(R)` is written `R`, and the one algebra `φ`
// stands at both components.  `⊑` points NE — down-then-across is the smaller `F(R)φ`.
#disp[#pair(
  leancd("Freyd.Alg.MonotonicAlg"),
  row((mon-hm-l, [#h(7pt) #SQ #h(7pt)], mon-hm-r)),
 [`F(R)φ⊑φR` #src[]],
)]<mon-str>

=== Function `f` is monotonic on `R` iff it distributes over `R` <sec-mon-thm71>

#disp[#definition[
`f : FA⟶A` *distributes over* `R` if #h(4pt) `F(est(R))f⊑` $frac(#[`F(∋)f`], ∋)$ `est(R)`
#src[].
// lean:AOP.A7_2.Distributes@e061e29e

`+` distributes over `≤`, at the point level #h(4pt)
`min(xs)+min(ys)=min{x+y∣x∈xs∧y∈ys}` #h(4pt) for `xs`, `ys` non-empty and
`min≜est(≤)`.
]]<dist-defn>

// The two panels of the inequation, emitted by `./scripts/diagram --frame 12 --sigs "f:F(A)⟶A"`
// plus `s: 100%`, the square's own size.  They line up on `f`, so the picture says what moves:
// `est(R)` starts INSIDE the functor on the left and ends up last of all on the right.  The right
// panel factors `(F(∋)f)%∋` the way @lam-defn does — `𝟙%∋` births the `E` wire, `∋` kills the one
// the source brought in — because a bead drawn whole would hide the very `E` the law is about.
#let dist-hm-l = lean("Freyd.Alg.Distributes.lhs")
#let dist-hm-r = lean("Freyd.Alg.Distributes.rhs")

// The `f` edges run across, as @mon-str's algebra does, so down-then-across is the smaller
// `F(est(R)) f` and `⊑` points NE.  Below: the same square at `F := (−×−)`, `f := +`, `R := ≤`.
#disp[#align(center, grid(columns: 1, align: horizon, row-gutter: 10pt,
  pair(
    leancd("Freyd.Alg.Distributes"),
    row((dist-hm-l, [#h(7pt) #SQ #h(7pt)], dist-hm-r)),
 [`F(est(R))f⊑` $frac(#[`F(∋)f`], ∋)$ ` est(R)` #src[]],
    s: 74%,
  ),
  capbox(
    leancd("Freyd.Alg.RelSet.plus_distributes_le"),
    [`(est(≤)×est(≤))+⊑` $frac(#[`(∋×∋)+`], ∋)$ ` est(≤)`],
  ),
))]<dist-str>

// B&dM Theorem 7.1, p. 172.  The mirrored chain lands on `R°`, and the last step, `f` a map, is
// what carries it back.
// The display number is 1.2cm wide but placed only 1.0cm into the margin, so it reaches ~6pt back
// into the column and the `Thm` cell's fill — drawn after it — paints over it; `pad` returns that strip.
// The monotonic-alg panels, emitted by `./scripts/diagram --sigs "f:F(A)⟶A" --src … --tgt … "<formula>"`
// — `f` is one algebra at the object `A` (Lean: `f : F.obj A ⟶ A`), not a family, so its bead
// sits on the object wire and the sweep needs no naturality verdict.
// plus `s: 100%`, so the labels print at the size the note sets them in.
#let ma-Fest-lam = lean("Freyd.Alg.Distributes.lhs")
#let ma-Fest-ni = lean("Freyd.Alg.Fmap_est_comp_le_Fmap_eps_comp.lhs")
#let ma-lam = lean("Freyd.Alg.Distributes.rhs")
#let ma-Fni = lean("Freyd.Alg.Fmap_est_comp_le_Fmap_eps_comp.rhs")
#let ma-Ro = lean("Freyd.Alg.mon_thm71_step3.rhs.lhs")
#let ma-R = lean("Freyd.Alg.mon_thm71_step4.rhs.lhs")
// The bare `R°`/`R` panels these rows pair with, emitted by `./scripts/diagram --src A --tgt A
// --frame … --top 3 "R°"` (resp. `"R"`); one binding per partner frame, named after the partner.
#let ma-Rbare-Ro = lean("Freyd.Alg.mon_thm71_step3.rhs.rhs")
#let ma-Rplain-R = lean("Freyd.Alg.mon_thm71_step4.rhs.rhs")
#disp[#calc-table(cols: (1fr,), al: auto,
  // monotonic-alg row: Theorem 7.1
  Thm(cols: 1)[`f°F(R)f⊑R⟺F(est(R))f⊑` #frc([`F(∋)f`]) ` est(R)` \
    #src[function `f` is monotonic over `R` if and only if it distributes over `R`; `f` a map,
     `R` reflexive
      // lean:AOP.A7_2.distributes_of_monotonicAlg@633ae757
 ]],
      // lean:AOP.A7_2.monotonicAlg_of_distributes@6d74126d

  [#vstep([], trow(ma-Fest-lam, ma-lam), [#src[`f` distributes over `R` — @dist-defn — the fraction bent as @adj-E-bend]])],

  // One picture per conjunct, side by side so the display stays on one page: the first is row 1's
  // left panel twice over, `est(R)` against `∋`; the second is the row-3 panel the next step keeps.
  [#vstep(IFF, grid(columns: 3, align: center + horizon, column-gutter: 10pt,
    trow(ma-Fest-ni, ma-Fni),
    [and],
    lean("Freyd.Alg.mon_thm71_step2.rhs.lhs", "Freyd.Alg.mon_thm71_step2.rhs.rhs"),
  ), [#src[@est-75 splits the bound in two, @div-laws moving `(F(∋)f)°` across]])],

  // The last three panels share one row, so the display stays on one page: the surviving conjunct,
  // its `∈ est(R)` collapsed to `R°`, and the whole conversed.
  [#hchain(
    (IFF, lean("Freyd.Alg.mon_thm71_step3.lhs.lhs", "Freyd.Alg.mon_thm71_step3.lhs.rhs"),
      src[`est(R)⊑∋` — @est-defn — so the first conjunct drops]),
    (IFF, trow(ma-Ro, ma-Rbare-Ro),
      src[`(F(∋)f)°=f°F(∈)` — @conv-defn — and `∈ est(R)=R°` — @est-defn, `R` reflexive]),
    (IFF, trow(ma-R, ma-Rplain-R),
      src[both sides conversed — `F(R°)°=F(R)`, @relator-laws
     // lean:AOP.A7_2.monotonicAlg_iff_conj@46638b64
    ]),
    // lean:AOP.A7_2.monotonicAlg_recip_iff@27f6bb47
  )],
)]<mon-thm71>

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
// would sit alone at the foot of §13.3.1's last page.
#pagebreak(weak: true)
=== `Greedy Theorem: ⦇`$frac(#[`S`], ∋)$` est(R)⦈⊑`$frac(#[`⦇S⦈`], ∋)$` est(R), given S monotoic on R, F preserving °, and R transitive` <sec-greedy-thm72>

// `inner` conversed, `after` above, `⊑ rhs` if given: rows 5–7 draw a TERM of one chain rather than an inequation,
// and with the run after the frame raised to `TH` — a fraction box is two lines tall.  A leading run
// of converses is ONE frame: `(SR)°=R°S°`, so the step that pulls `R°` out of `F` moves `R` inside.
// The greedy panels, emitted by `./scripts/diagram --sigs "S:F(x)⟶x" --src A --tgt A "<formula>"` plus
// `s: 100%`, so the labels print at the size the note sets them in.
#let gr-mon = lean("Freyd.Alg.greedy_step1.lhs")
#let gr-Rbare = lean("Freyd.Alg.greedy_step3.rhs")
#let gr-slid = lean("Freyd.Alg.greedy_step1.rhs")
#let gr-RR = lean("Freyd.Alg.greedy_step2.rhs")
#let gr-R = lean("Freyd.Alg.greedy_step3.rhs")
// B&dM Theorem 7.2, p. 173.  The hypothesis is monotonicity on the SAME `R` the conclusion's
// `est(R)` uses: the book reads right to left and states it on `R°`, and mirroring flips it back.
#disp[#calc-table(
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], [], [`⦇`#frc([`S`])` est(R)⦈⊑`#frc([`⦇S⦈`])` est(R)` \
    #src[the conclusion: one minimum kept at each step is below every result collected and one
 minimum taken at the end]])],
     // lean:AOP.A7_2.greedy@21400acf
  [],

  [#vstep(IFF, [],
    [#grid(columns: 3, align: (right + horizon, center + horizon, left + horizon),
       column-gutter: 6pt, row-gutter: 3pt,
       [`⦇`#frc([`S`])` est(R)⦈`], [`⊑`], [`⦇S⦈`],
       grid.cell(colspan: 3, align: center + horizon)[and],
       [`⦇S⦈°⦇`#frc([`S`])` est(R)⦈`], [`⊑`], [`R°`],
       grid.cell(colspan: 3, align: left + horizon, inset: (top: 3pt))[#src[@est-75 at `⦇S⦈`;
         `⦇`#frc([`S`])` est(R)⦈⊑⦇S⦈°\R°⟺⦇S⦈°⦇`#frc([`S`])` est(R)⦈⊑R°` — @div-laws]])])],
  [],

  [#vstep(IMP, [], [#frc([`S`])` est(R)⊑S` \
    #src[the left conjunct; @est-75, and `⦇−⦈` is monotone]])],
  [],

  // TWO CALLS, not one `leanc(…)` naming both: a two-name call shares ONE box, which is what makes
  // the two sides of an equation stand at the same height, and these are two statements.
  [#vstep(IMP, trow(leanc("Freyd.Alg.greedy_step1.lhs"), leanc("Freyd.Alg.greedy_step3.rhs")),
    [#src[the right conjunct; `⦇S⦈°⦇`#frc([`S`])` est(R)⦈` is the least `X` with
      `X=S°F(X)(`#frc([`S`])` est(R))` #h(4pt) #src[@hylo-mu] #h(4pt) — so Knaster–Tarski
      leaves this one inequation] \
     #src[#frc([`S`]) `=` #frc([`𝟙`]) `E(S)` — @adj-E-bend]])],
  // `S°` births the `F` wire and `S` kills it, so `F(R°)` is the `R°` bead INSIDE that span — the
  // relator's action costs no notation.  The unit births the `E` wire, and `est(R)` kills it.
  [#trow(gr-mon, gr-Rbare)],

  [#vstep(SQ, leanc("Freyd.Alg.greedy_step1.rhs"),
    [#src[`S°F(R°)⊑R°S°` — @mon-defn at `S`, conversed; `F(R)°=F(R°)` — @relator-laws]])],
  // `R°` leaves the `F` span and lands above `S°`; the three beads that did not move keep their height.
  [#gr-slid],

  [#vstep(SQ, leanc("Freyd.Alg.greedy_step2.rhs"),
    [#src[`S°(`#frc([`S`])` est(R))⊑S°(S°\R°)⊑R°` — @est-75, @div-laws]])],
  // The collapsed group's bead sits at the middle of the span it replaces.
  [#gr-RR],

  [#vstep(SQ, leanc("Freyd.Alg.greedy_step3.rhs"), [#src[`R` transitive]])],
  [#gr-R],
)]<greedy-thm72>

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
// would sit alone at the foot of §13.3's last page.
#pagebreak(weak: true)
=== `takewhile(p)=⦇[nil,(π₁p→cons,⊸ nil)]⦈` <sec-takewhile>

// B&dM Ex 7.39, p. 174.  The derivation runs on `est(R°)` (@est-defn) and the greedy theorem
// (Theorem 7.2), both above it.
// One running example: `A≜Nat` and `p≜even`, fixed by the `p` row and used by every row below it.
#disp[#align(center, block(width: 21cm)[
#table(
  columns: (1.7cm, 5.3cm, 2.9cm, 4.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*type*], [*example*], [*in words*]),

  [`F`], [`FX=𝟏+A×X`], [`𝒜⟶𝒜`], [],
  [nothing, or a head and a tail],

  [`nil`, `cons`], [`[A]::=nil|cons(A,[A])` #h(4pt) #src[@comb-fns]],
  [`𝟏⟶[A]`, #h(4pt) `A×[A]⟶[A]`],
  [`cons(3,[1,2])=[3,1,2]`],
  [the empty list; a head onto a tail],

  [`α`], [`[nil,cons]`], [`F([A])⟶[A]`], [],
  [both constructors as one map],

 [`p`], [a coreflexive #src[]], [`A⟶A`], [`p≜even` #h(4pt) — `2 p 2`, and `3∉Dom(p)`],
  // lean:AOP.A7_7_TakeWhile.pcor@62cb073c
  [`{(a,a)∣a` passes the test`}`],

 [`R`], [`length≤length°`, a preorder #src[]], [`[A]⟶[A]`], [`[1] R [1,2]`],
  // lean:AOP.A7_7_TakeWhile.lenLE@e922b2d4
  [`xs R ys⟺length(xs)≤length(ys)`],

  [`⊸ nil`], [the constant `nil` — the second `nil` of `prefix`], [`A×[A]⟶[A]`],
  [`(⊸ nil)(3,[1,2])=nil`],
  [drop the pair, return `nil`],

  [`prefix`], [`⦇[nil,⊸ nil ∪ cons]⦈` #h(4pt) #src[@comb-fns]], [`[A]⟶[A]`],
  [`[3,1,2] prefix [3,1]`],
  [`xs prefix ys⟺∃zs. xs=ys⧺zs` #h(4pt) — at each `cons`, stop or keep the head],

 [`S`], [`[nil,⊸ nil ∪ (p×𝟙) cons]` #src[]], [`F([A])⟶[A]`],
  // lean:AOP.A7_7_TakeWhile.Salg@8ccdcfd1
  [`(4,[2]) S [4,2]`, #h(4pt) and `(3,[2]) S nil` only],
  [`prefix`'s algebra with one extra `p` — stop, or keep a head that passes `p`],

  [`(g→X,Y)`], [`X` where `g` is defined and `Y` where it is not], [`A⟶B` #h(4pt) at
   `X`,`Y : A⟶B`], [],
  [the test picks the branch],
)
#v(6pt)
#align(center)[`nil R=⊤`, #h(4pt) `nil R°=nil` #h(4pt) #src[`nil` is the shortest list — below
  every list, and above only itself, so it loses every `est(R°)`]]
])]<takewhile-defn>

// `prefix` ON ITS OWN, before `takewhile` specialises it: the fold's defining square, the two Hinze–Marsden
// panels either side of the `=`, and the algebra's circuit.  Panels emitted verbatim by
//   ./scripts/diagram --frame 4 --top 3 --src "F([A])" --tgt "[A]" --sigs "α:F([A])⟶[A]" "α prefix"
//   ./scripts/diagram --frame 4 --src "F([A])" --tgt "[A]" "F(prefix)[nil,⊸ nil ∪ cons]"
// `--frame 4 --top 3` lifts `α prefix` so both panels share one frame and meet on the `prefix` bead.
#let pfx-def-l = lean("Freyd.Alg.RelSet.ListRel.prefix_cancel.lhs")
#let pfx-def-r = lean("Freyd.Alg.RelSet.ListRel.prefix_cancel.rhs", branch: "inr.inr")

#disp[#calc-table(cols: (1fr, 7.4cm), pr: 0pt,
  Thm[#leanf("Freyd.Alg.RelSet.ListRel.prefix_cata") \
    #src[the fold whose algebra, at each `cons`, stops with `nil` or keeps the head:
      `xs prefix ys⟺∃zs. xs=ys⧺zs`]
    // lean:AOP.A5_6_ListCombinators.prefix_cata@b8d861c4
    // lean:AOP.A5_6_ListCombinators.prefixP_iff_append@1c6dd07f
    ],
  table.header([*the defining square* `α prefix=F(prefix)[nil,⊸ nil ∪ cons]` — build the list and then
      take a prefix, or take a prefix of the tail and then rebuild with the algebra],
    [*Hinze–Marsden*]),

  [#leancd("Freyd.Alg.RelSet.ListRel.prefix_cancel") \
  #src[`F=𝟏+A×−`, so `F(prefix)=𝟙+𝟙×prefix`: the head passes, the fold recurses on the tail alone]
  // lean:AOP.A6_ConsList.F@61b71616
  ],
  [#row((pfx-def-l, [#h(7pt) = #h(7pt)], pfx-def-r)) \
   #src[the `cons` operand of `⊸ nil ∪ cons`; `⊸ nil` makes a constant and draws nothing]],

  [#leanc("Freyd.Alg.RelSet.ListRel.prefAlg") \
   #src[the algebra `[nil,⊸ nil ∪ cons] : F([A])⟶[A]` as a circuit: `nil` on the `𝟏` branch; on a pair
     `(a,ys′)` two outputs, `nil` and `cons(a,ys′)`]],
  [#src[`nil prefix ys⟺ys=nil`] \
   #src[`cons(a,xs′) prefix ys⟺ys=nil ∨ ∃ys′. xs′ prefix ys′ ∧ ys=cons(a,ys′)`] \
   #src[a right fold: `α°` peels, `F(prefix)` recurses, the algebra runs on the way back; `init*`
     (@comb-fns) is the tail-recursive form] \
   #src[lax natural only, `list(R) prefix⊑prefix list(R)`: `list(R)` first needs an `R`-image of every
     element, `prefix` first may have dropped the ones without]
   // lean:AOP.A5_6_ListCombinators.prefixP@6b59adf4
   // lean:AOP.A5_7_ListBeads.prefix_lax_natural@b07fb2c5
   // lean:AOP.A5_7_ListBeads.prefix_not_strict@e360d358
   ],
)]<prefix-defn>

// HINZE–MARSDEN (IntroString.pdf §1.4.2), @party-mono-branch's second column at this section's data:
// a wire is a FUNCTOR, a bead an arrow, a region a category, gray `𝟏`.  ONLY the `(p×𝟙) cons` operand
// is drawn — `∪` has no geometry here, and the other operand `⊸ nil` creates a constant and draws
// nothing.  `[A]` is TWO wires, `list` beside `A`: `p : A⟶A` is a bead on the object wire with the
// `list` running past it, and `prefix : [A]⟶[A]` eats that `list` and makes another.
// `prefix`/`subseq` are only LAX natural in `Rel` — `list(p) prefix⊑prefix list(p)` and no more, since
// `list(p)` needs every element to have a `p`-image — so `p` stays strictly below.

// Emitted verbatim by `./scripts/diagram --src "F([A])" --tgt "[A]" "<the row's formula>"`: the
// source IS the generator's output, so a redraw is a re-run of that line and never a hand edit.
// Bead colour is WHICH ARROW: `cons` is the structure map and stays black.
#let tw-pfx1 = lean("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step1.lhs")
#let tw-pfx2 = lean("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step1.rhs", branch: "inr.inr")
#let tw-pfx3 = lean("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step2.rhs", branch: "inr.inr")
#let tw-pfx4 = lean("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step3.rhs", branch: "inr.inr")

#disp[#calc-table(cols: (1fr, 5.6cm), pr: 0pt, 
  Thm[#leanf("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_comm") \
    #src[building the list and then keeping a `p`-passing prefix of it is keeping one of the tail
     first, and then building with `S`] \
    #src[this same diagram is `subseq`'s: algebra `[nil,π₂ ∪ cons]`, type `[A]⟶[A]`]
    // lean:AOP.A7_7_Filter.filter_alg_comm@e2fc9591
    // lean:AOP.A7_7_Filter.filter_alg@5c8645c6
    ],
  table.header([*circuit* — the fork is `F([A])=𝟏+A×[A]`: `nil` above, the pair below],
    [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step1.lhs"),
    [`α prefix list(p)`])],
  [#tw-pfx1 \
    #src[the `cons` branch alone, without `𝟏+` or `⊸ nil`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step1.rhs"),
    [`F(prefix) [nil,⊸ nil ∪ cons] list(p)` \ #src[defining equation]])],
  [#tw-pfx2 \ #src[the `cons` operand of `⊸ nil ∪ cons`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step2.rhs"),
    [`F(prefix) [nil,⊸ nil ∪ (p×list(p)) cons]` \ #src[`list(p)` through `cons`]])],
  [#tw-pfx3 \ #src[the `(p×list(p)) cons` operand of `⊸ nil ∪ (p×list(p)) cons`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step3.rhs"),
    [`[nil,⊸ nil ∪ (p×(prefix list(p))) cons]` \ #src[relator, `prefix` entire]])],
  [#tw-pfx4],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_step4.rhs"),
    [`F(prefix list(p))S` \ #src[`prefix list(p)` entire]])], [],
)
#align(center, block(inset: (y: 4pt))[#src[@cata-defining reads that off as `prefix list(p)=⦇S⦈`.
  @cata-fusion cannot: `list(p)` is not entire, `(𝟙×list(p))⊸ nil⊏⊸ nil`, and no algebra meets
 the side condition. ,
  // lean:AOP.A7_7_TakeWhile.takewhile_alg@89d813c7
 ]])
  // lean:AOP.A7_7_TakeWhile.takewhile_alg_comm@98848cae
]<takewhile-alg>

// One law to a step: `R°` starts on the tail strand, is copied into both operands of the `∪`,
// dies against `⊸` on one and slides through `cons` on the other, and leaves past the join.
#let step = step.with(pw: 300pt)
#disp[#calc-table(cols: (1fr, 6.0cm), al: (center + horizon, left + horizon), pr: 0pt, 
  Thm[#leanf("Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_cons") \
    #src[shortening the tail and then taking the step lands inside taking the step and then
     shortening the result]],
  table.header([*circuit* — the `cons` branch of `F(R°)S⊑SR°`], [*reason*]),

  [#step([])[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_cons.lhs")][`(𝟙×R°)(⊸ nil ∪ (p×𝟙) cons)`]],
  [],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_cons@99fa663b

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_fork.rhs")][`(𝟙×R°)⊸ nil ∪ (p×R°) cons`]],
  [each operand is reached on its own #h(4pt) #src[@adj-all] #h(4pt) — and `(𝟙×R°)(p×𝟙)` is `p`
   and `R°` on the pair's two strands at once],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_fork@0142ae2e

  [#step(SQ)[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_step2.rhs")][`⊸ nil ∪ (p×R°) cons`]],
  [`⊸` is the greatest arrow into `𝟏`, so `(𝟙×R°)⊸⊑⊸`],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_disc@6237fa76

  [#step(SQ)[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_step3.rhs")][`⊸ nil ∪ (p×𝟙) cons R°`]],
  [`cons length=(𝟙×length)π₂ succ` with `succ` monotone — a shorter tail makes a shorter list],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_slide@51fc70a5

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_step4.rhs")][`⊸ nil R° ∪ (p×𝟙) cons R°`]],
  [`nil R°=nil` #h(4pt) #src[@takewhile-defn] #h(4pt) — so the constant branch may carry the `R°`
   the other one already has],
  // lean:AOP.A7_7_TakeWhile.takewhile_mono_nil@17a53619

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_cons.rhs")][`(⊸ nil ∪ (p×𝟙) cons)R°`]],
  [one `R°` past the join is the two inside it #h(4pt) #src[@adj-all]],
  // lean:Freyd.S2_20.union_comp_distrib@0025430d
)
#align(center, block(inset: (y: 4pt))[#src[the `nil` branch, which no row above draws, is
  `nil⊑nil R°`.]])
  // lean:AOP.A7_7_TakeWhile.takewhile_mono@469bb647
]<takewhile-mono>

// ONE wire while `S` sits inside a division — nothing can be seen into it — then the bracket, once
// the coproduct of maps has opened it.
#let step = step.with(pw: 340pt)
#disp[#calc-table(cols: (1fr, 4.4cm), al: (center + horizon, left + horizon), pr: 0pt, 
  Thm[#leanf("Freyd.Alg.RelSet.GCTakeWhile.takewhile_step") \
    #src[the longest of the lists the algebra allows is the `cons` where the head passes `p`, and
     `nil` where it does not]],
  table.header([*formula*], [*reason*]),

  // lean:AOP.A4_6.Λ_eq_singleton_existsImage@02b29ea8
  [#step([])[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_step1.lhs")][]], [],

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_step1.rhs")][`[`$frac(#[`nil`], ∋)$` est(R°),` $frac(#[`⊸ nil ∪ (p×𝟙) cons`], ∋)$` est(R°)]`]],
  [coproduct of maps],

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_step2.rhs")][`[nil,` $frac(#[`⊸ nil ∪ (p×𝟙) cons`], ∋)$` est(R°)]`]],
  [singleton, `R°` reflexive],

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_step3.rhs")][]],
  [`nil R=⊤`],
)
#align(center, block(inset: (y: 4pt))[#src[the set is `{nil}` where `p` fails on the head and
  `{nil,cons(a,xs)}` where it holds, and `nil` loses the second — @est-defn at a two-element set.
 ]])
  // lean:AOP.A7_7_TakeWhile.takewhile_step@a0403ffd
]<takewhile-step>

// B&dM Ex 7.39, p. 174: the specification down to the program, then the three facts that turn the
// greedy `⊒` into the heading's `=`.  Only the last three rows are cited rather than derived.
// `S` is defined in @takewhile-defn, three pages back, and every row below reads it: the definition
// is repeated here rather than looked up, in that table's own five columns.
#disp[#align(center, block(width: 21cm)[
#table(
  columns: (1.7cm, 5.3cm, 2.9cm, 4.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*type*], [*example*], [*in words*]),

  [`S`], [`[nil,⊸ nil ∪ (p×𝟙) cons]` #h(4pt) #src[@takewhile-defn]], [`F([A])⟶[A]`],
  [`(4,[2]) S [4,2]`, #h(4pt) and `(3,[2]) S nil` only],
  [`prefix`'s algebra with one extra `p` — stop, or keep a head that passes `p`],
)])]

#disp[#calc-table(cols: (1fr, 7.9cm), 
  // B&dM p.174, Ex 7.39: "In words, takewhile p x returns the longest prefix of x with the property that all
  // its elements satisfy p." … "derive the standard implementation of takewhile."
  Thm[`takewhile(p)≜` #frc([`prefix list(p)`]) ` est(R°)=⦇[nil,(π₁p→cons,⊸ nil)]⦈` \
    // takewhile-cata row: Ex 7.39
    #src[takewhile: `takewhile(p)(x)` returns the longest prefix of `x` with the property that all its
     elements satisfy `p`; the catamorphism is the standard implementation.
 ]],
     // lean:AOP.A7_7_TakeWhile.takewhile_eq_cata@31b3dec9
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_laws_step1.lhs"),
    [#src[the specification — @est-defn's `est(R°)`.
 ]])],
     // lean:AOP.A7_7_TakeWhile.takewhile@77395e5e
  [#align(center, lean("Freyd.Alg.RelSet.GCTakeWhile.takewhile_laws_step1.lhs"))],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_laws_step1.rhs"),
 [#src[@takewhile-alg]])],
    // lean:AOP.A7_7_TakeWhile.takewhile_alg@89d813c7
  [#align(center, lean("Freyd.Alg.RelSet.GCTakeWhile.takewhile_laws_step1.rhs"))],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_greedy.lhs"),
    [#src[@greedy-thm72 at `R°`, with `F(R°)S⊑SR°` — @takewhile-mono —
     for its hypothesis: one longest `p`-prefix kept at each `cons`, instead of every `p`-prefix
 collected and one chosen at the end. ]])],
  [#align(center, lean("Freyd.Alg.RelSet.GCTakeWhile.takewhile_greedy.lhs"))],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.GCTakeWhile.takewhile_laws_step3.rhs"),
 [#src[@takewhile-step]])],
    // lean:AOP.A7_7_TakeWhile.takewhile_step@a0403ffd
  [#align(center, lean("Freyd.Alg.RelSet.GCTakeWhile.takewhile_laws_step3.rhs"))],

  [#vstep([], [], [`takewhile(p)° takewhile(p)⊑prefix° prefix∩R∩R°⊑𝟙` \
    #src[`takewhile(p)⊑prefix list(p)` and `(prefix list(p))° takewhile(p)⊑R` — @est-75 at `est(R°)` —
     and two prefixes of one list of equal length are equal, so `takewhile(p)` is simple: *the*
 longest, not *a* longest. ]])],
     // lean:AOP.A7_7_TakeWhile.takewhile_simple@f4543b09
  [],

  [#vstep([], [], [#frc([`prefix list(p)`]) ` est(R°)` entire \ #src[`nil` is always a `p`-prefix and
    `R` is connected on the prefixes of one list, so the longest exists.
 ]])],
    // lean:AOP.A7_7_TakeWhile.takewhile_entire@125bd033
  [],

  [#vstep([], [], [`X⊑Y`, `X` entire, `Y` simple `⟹X=Y` \ #src[`⦇[nil,(π₁p→cons,⊸ nil)]⦈` is a
    reduce of maps, hence entire — what turns the `⊒` above into the heading's `=`.
 ]])],
    // lean:Freyd.S2_10.eq_of_le_entire_simple@e9665c67
  [],
)]<takewhile-laws>

=== `mss=⦇[zero⟨𝟙,`#frc([`𝟙`])`⟩,⟨(𝟙×π₁)⊕,⟨(𝟙×π₁)⊕ `#frc([`𝟙`])`,π₂π₂⟩ cup⟩]⦈ π₂ est(≥)` <sec-mss>

// B&dM Ex 7.40, p. 174–175, whose five staged instructions are the five displays below, mirrored.
// `≤` is on `A`: over `Nat` every `⊕` would take its right branch and `mss` would be `sum`.
#disp[#definition[
`FX=𝟏+A×X`, #h(4pt) `α≜[nil,cons]`, #h(4pt)
`sum=⦇[zero,plus]⦈` and `segment=suffix prefix` from @cata-examples and @comb-fns.
#h(4pt) #src[]
// lean:AOP.A5_6_ListCombinators.sum_cata@f08e44f1

`head≜cons° π₁`, #h(4pt) `wrap≜⟨𝟙,⊸ nil⟩ cons` #h(4pt) #src[the head of a list and the
one-element list, beside @comb-fns's `tail≜cons° π₂`]

`⊕≜` $frac(#[`⊸ zero ∪ plus`], ∋)$ ` est(≥)` #h(4pt) #src[the
set at `(a,b)` is `{0,a+b}`, so `⊕` is the larger of the two,
]
// B&dM's `oplus=max(Λ(zero ∪ plus))`.
// lean:AOP.A7_7_MSS.oplus@e876f97f lean:AOP.A7_7_MSS.oplus_eq@8819d3f7
]]<mss-defn>

// ONE WIRE, `[A]` to `A`: this chain never forks, so a row is a run of boxes and the picture's whole
// content is the TYPE the wire carries — where `E(EA)` is born, and which box collapses it again.
// A type sits ON its strand (`node`'s white ground masks the wire): a gap is that white ground (text
// plus its insets) plus a wire stub either side, so the strand visibly runs into each label.  `X/∋`
// and `E(X)` are fractions, hence maps (@pow-laws), so their boxes are square; `est(≥)` is the chain's
// one relation and its only chamfered box.  Widths are measured at the note's text sizes.
#let TH = 1.2   // a fraction box is two lines tall
#let ty-l = ([`[A]`], 1.25)
#let ty-el = ([`E[A]`], 2.0)
#let ty-ea = ([`EA`], 1.0)
#let ty-eea = ([`E(EA)`], 1.75)
#let ty-a = ([`A`], 0.75)
#let bx-mss = (frc([`segment sum`]), 2.2, false)
#let bx-spp = (frc([`suffix (prefix sum)`]), 3.6, false)
#let bx-sf = (frc([`suffix`]), 1.3, false)
#let bx-eps = ([`E(prefix sum)`], 3.5, false)
#let bx-ep = ([`E(`#frc([`prefix sum`])`)`], 2.8, false)
#let bx-un = ([`union`], 1.45, false)
#let bx-eest = ([`E(est(≥))`], 2.65, false)
#let bx-epest = ([`E(`#frc([`prefix sum`])` est(≥))`], 4.8, false)
#let mss-run(tys, items) = {
  let x = 0.0
  for (i, it) in items.enumerate() {
    let (tl, tw) = tys.at(i)
    wire((x, 0), (x + tw, 0)); node(x + tw / 2, 0, black, tl)
    gbox((x + tw, 0), it.at(0), w: it.at(1), h: TH, chamfer: it.at(2))
    x = x + tw + it.at(1)
  }
  let (tl, tw) = tys.at(items.len())
  wire((x, 0), (x + tw, 0)); node(x + tw / 2, 0, black, tl)
}
#let mss-pic(tys, items, s: 100%) = P(cetz.canvas(length: 0.8cm, mss-run(tys, items)), s: s)

#let step = step.with(pw: 303pt)
#disp[#calc-table(cols: (1fr, 4.6cm), al: (center + horizon, left + horizon), pr: 0pt, 
  // B&dM p.174, Ex 7.40: "The maximum segment sum problem … is specified by mss = max·Λ(sum·segment) …
  // Using segment = prefix·suffix, express this problem in the form mss = max·P(max·Λ(sum·prefix))·Λsuffix."
  Thm[#leanf("Freyd.Alg.RelSet.MSS.mss_shape") \
    #src[maximum segment sum problem: using `segment=suffix prefix`, the specification is expressed in this
     form]],
    // lean:AOP.A7_7_MSS.mss_shape@9c38ad6f
  table.header([*formula* — one wire from `[A]` to `A`, its type written along it], [*reason*]),

  [#step([])[#mss-pic((ty-l, ty-ea, ty-a), (bx-mss, est-Rc-box))][]], [],

  [#step(EQ)[#mss-pic((ty-l, ty-ea, ty-a), (bx-spp, est-Rc-box))][]],
  [`segment=suffix prefix` \ #src[@comb-fns, @mss-defn]],

  [#step(EQ)[#mss-pic((ty-l, ty-el, ty-ea, ty-a), (bx-sf, bx-eps, est-Rc-box), s: 94%)][]],
  [absorption \ #src[@pow-laws — `frac(S,∋) E(R)=frac(SR,∋)` at `S:=suffix`, `R:=prefix sum`]],

  [#step(EQ)[#mss-pic((ty-l, ty-el, ty-eea, ty-ea, ty-a), (bx-sf, bx-ep, bx-un, est-Rc-box), s: 95%)][]],
  [#frc([`R`])` ∋=R`, `union=E(∋)` \ #src[@pow-laws's `frac(R,∋)∋=R` at `R:=prefix sum` and
   `E(R)≜frac(∋R,∋)`; @est-laws's `union≜frac(∋∋,∋)`; the middle equality is @relator-defn's
   `F(RS)=F(R)F(S)` at `F:=E`]],

  [#step(EQ)[#mss-pic((ty-l, ty-el, ty-eea, ty-ea, ty-a), (bx-sf, bx-ep, bx-eest, est-Rc-box), s: 85%)][]],
  [@est-laws, the sets non-empty],

  [#step(EQ)[#mss-pic((ty-l, ty-el, ty-ea, ty-a), (bx-sf, bx-epest, est-Rc-box), s: 92%)][]],
  [relator \ #src[@relator-defn — `F(RS)=F(R)F(S)` at `F:=E`]],
)
// mirrored from `max(P(max(Λ(sum prefix))))Λsuffix`.
#align(center, block(inset: (y: 4pt))[#src[The
  `union` step is @est-laws's `P(est(R)) est(R)=P(Dom(est(R))) union est(R)` — every suffix has the
  empty prefix, so `Dom` is `𝟙` here — and `P(f)=E(f)` at the map it is applied to (@powrel-laws).]])
]<mss-shape>

// §13.3.4's generated panels, emitted verbatim by `./scripts/diagram --src … --tgt … "<formula>"`: a
// bracket is cut to ONE branch, which the `cert:` names, and the bead wears that branch's name.
#let mh-cons-sum = lean("Freyd.Alg.RelSet.MSS.cons_comp_sum.lhs")
#let mh-alg-est = lean("Freyd.Alg.RelSet.MSS.mss_step1.lhs")
#let mh-alg = lean("Freyd.Alg.RelSet.MSS.mss_step2.rhs", branch: "inr")
// The `plus` operand of the lower arm's `⊸ zero ∪ plus`, cut by hand (`rank` would draw `⊸ zero`):
// `𝟙%∋ E(plus)est(≥)`, emitted verbatim by `./scripts/diagram --sigs "plus:A×A⟶A"`.
#let mh-alg-plus = lean("Freyd.Alg.RelSet.MSS.mss_step_plus.lhs")
#let mh-segsum = lean("Freyd.Alg.RelSet.MSS.mss_shape.lhs")
#let mh-greedy = lean("Freyd.Alg.RelSet.MSS.mss_eq_scan_step2.rhs")
#let mh-shape = lean("Freyd.Alg.RelSet.MSS.mss_shape.rhs")

// HINZE–MARSDEN: `[A]` is `list` beside `A`, so `cons` kills the base functor's `A×−` onto the `list`
// wire and `sum` kills `list` onto `A`.  `∪` has no shape here — only `cons`'s branch is drawn.
#disp[#pad(right: 10pt, table(
  columns: (1fr, HMW),
  align: (left + horizon, center + horizon),
  inset: (x: 9pt, y: 3pt),
  stroke: 0.4pt + luma(190),
  // B&dM p.174, Ex 7.40: "Express prefix as a catamorphism on cons-lists, and use fusion to express
  // sum·prefix as a catamorphism."
  Thm[`[nil,⊸ nil ∪ cons] sum=F(sum)[zero,⊸ zero ∪ plus]` \
    #src[fusion: `prefix` expressed as a catamorphism on cons-lists, `⦇[nil,⊸ nil ∪ cons]⦈`, and this is
     the fusion condition that expresses `prefix sum` as a catamorphism]],
  table.header([*circuit* — the fork is the bracket's case split `F([A])=𝟙+A×[A]`: `nil` above, the pair and its `∪` below], [*Hinze–Marsden*]),

  // `sum` keeps ONE height down the column: what the fusion moves is the algebra bead, from below
  // `sum` to above it, and the join it rides is drawn with the same knee angle both times.
  [#vstep([], leanc("Freyd.Alg.RelSet.MSS.cons_comp_sum.lhs"),
    [`[nil,⊸ nil ∪ cons] sum`])],
  [#mh-cons-sum \ #src[the `cons` operand of `⊸ nil ∪ cons`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.mss_prefix_sum_step1.rhs"),
    [`[nil sum,⊸ nil sum ∪ cons sum]` \ #src[coproduct of maps, composition over `∪`]])],
  // Empty: composing `sum` into each branch is re-bracketing, which draws the row above again.
  [],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.cons_comp_sum.rhs"),
    [`[zero,⊸ zero ∪ (𝟙×sum) plus]` \ #src[`sum`'s defining equation]])],
  [#lean("Freyd.Alg.RelSet.MSS.cons_comp_sum.rhs") \ #src[the `(𝟙×sum) plus` operand of `⊸ zero ∪ (𝟙×sum) plus`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.mss_prefix_sum_step3.rhs"),
    [`[zero,(𝟙×sum)(⊸ zero ∪ plus)]` \ #src[`(𝟙×sum)⊸=⊸`, `sum` entire]])],
  // Empty: the last two steps rewrite the bracket and the `⊸ zero` branch, and leave the drawn
  // `(𝟙×sum)plus` exactly as the row above has it.
  [],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.mss_prefix_sum_step4.rhs"),
    [`F(sum) [zero,⊸ zero ∪ plus]` \ #src[relator]])],
  [],
))
#align(center, block(inset: (y: 4pt))[#src[@cata-fusion at `R:=[nil,⊸ nil ∪ cons]`,
  `S:=sum`: the side condition, so `prefix sum=⦇[zero,⊸ zero ∪ plus]⦈`. `prefix` is the
  reduce, `sum` the map fused into it — the intermediate list is gone.
 ]])
  // lean:AOP.A7_7_MSS.mss_prefix_sum@4a7ef8bd
]<mss-prefix-sum>

#disp[#calc-table(cols: (1fr,), al: left + horizon, 
  // B&dM p.172: "By definition, an F-algebra S : A ← FA is monotonic on a relation R : A ← A if S·FR ⊆ R·S."
  Thm(cols: 1)[`(𝟙×≥)(⊸ zero ∪ plus)⊑(⊸ zero ∪ plus)≥` \
    #src[monotonic algebra: an `F`-algebra `S` is monotonic on a relation `R` if `F(R)S⊑SR` — the `plus`
     branch of `F(≥)S⊑S≥`; the `zero` branch is `zero⊑zero≥`]],
    // lean:AOP.A7_7_MSS.mss_mono@f623d6fe
  table.header([*circuit* — the head above, the running sum below; the tape is the `∪`]),

  [#hchain(fill: true,
    (none, [#leanc("Freyd.Alg.RelSet.MSS.mss_mono_fork.lhs")],
      [], [`(𝟙×≥)(⊸ zero ∪ plus)`]),
    (EQ, [#leanc("Freyd.Alg.RelSet.MSS.mss_mono_fork.rhs")],
      src[relator, composition over `∪`], [`(𝟙×≥)⊸ zero ∪ (𝟙×≥) plus`]),
    (SQ, [#leanc("Freyd.Alg.RelSet.MSS.mss_mono_step3.rhs")],
      src[@dom-slide, `(≥×≥) plus⊑plus≥`; `(≤×≤) plus⊑plus≤` is @mon-defn,
       written `+` there, and `plus` is a map, so it is monotonic on an order and on its opposite
       together, which carries it to `≥`.], [`⊸ zero ∪ plus≥`]),
    (SQ, [#leanc("Freyd.Alg.RelSet.MSS.mss_mono_step4.rhs")],
      src[`≥` reflexive], [`(⊸ zero ∪ plus)≥`]),
  )],
)]<mss-mono>

// Every row is ONE WIRE, `𝟏+A×A` to `A` — `F(A)` — so its two ends are drawn once.
#let mss-src = { lab(-1.62, 0, black)[`𝟏+A×A`]; wire((-0.45, 0), (0, 0)) }
#let mss-tgt(x) = lab(x + 0.62, 0, black)[`A`]
// Every `R/∋` is a MAP (@pow-laws), so a fraction box is square; `est(≥)` is partial — no greatest of
// the empty set — and is the one chamfered box here.  `h` is shared down a run: a fraction is two lines.
#let mss-alg = $frac(#[`[zero,⊸ zero ∪ plus]`], ∋)$
#let mss-zero = $frac(#[`zero`], ∋)$
#let mss-plus = $frac(#[`⊸ zero ∪ plus`], ∋)$
#let mss-run(items, h: 0.6) = { mss-src; boxrun(0, 0, items, h: h); mss-tgt(boxrun-w(items)) }
// @coprod-laws' tape at this algebra: `[X,Y]` is ONE BRANCH PER SUMMAND, each opening with the
// injection's converse — `𝟏` above, `A×Int` below.  The shorter branch is padded to the same join.
#let mss-pic(body) = P(cetz.canvas(length: 0.8cm, body), s: 78%)

// HINZE–MARSDEN: the WHOLE algebra is one bead here, so `F` is its wire and joins the object wire
// there; #frc([`S`]) `=` #frc([`𝟙`]) `E(S)` (@adj-E-bend) births the `E` the last row has no more.
#disp[#calc-table(
 Thm[#leanf("Freyd.Alg.RelSet.MSS.mss_step") \
    #src[the largest sum the algebra offers is zero from nothing and, from a head and a running sum,
     the larger of zero and the head added to it]],
  // lean:AOP.A7_7_MSS.mss_step@28267eec lean:AOP.A7_7_MSS.mss_step_plus@b71cc592
  table.header([*circuit* — the tape is the coproduct: `zero`'s branch above, `plus`'s below],
    [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.MSS.mss_step1.lhs"), [#mss-alg ` est(≥)`])],
  [#mh-alg-est \ #src[the `zero` arm of the bracket]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.mss_step_plus.lhs"),
    [`[`#mss-zero` est(≥),` #mss-plus ` est(≥)]` \ #src[coproduct of maps — @coprod-calc at
     `T:=[zero,⊸ zero ∪ plus]`, then `[U,V]Z=[UZ,VZ]` — @coprod-laws, composition over `∪`]])],
  [#mh-alg-plus \ #src[the `plus` operand of the lower arm's `⊸ zero ∪ plus`, under its `𝟙%∋ E(…)` and `est(≥)`]],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.mss_step2.rhs"), [#src[singleton, `≥` reflexive — @est-laws's $frac(#[`𝟙`], ∋)$ `est(R)=𝟙∩R` at `R:=≥`, `zero` a
    map; the lower branch is `⊕`'s definition, @mss-defn, and no law]])],
  [#mh-alg],
)
// B&dM's own containment.
#align(center, block(inset: (y: 4pt))[#src[with @mss-mono the greedy theorem gives
  `⦇[zero,⊕]⦈⊑` $frac(#[`prefix sum`], ∋)$ ` est(≥)` — and @mss-deriv
 makes it an equality. ]])
  // lean:AOP.A7_7_MSS.mss_greedy@6f748228
]<mss-step>

// B&dM Ex 7.40's last stage, in the power object: @cata-defining's equation for the pair whose
// components are `k`'s two output wires.  No circuit — the carrier is a PRODUCT, and a fork needs
// the product bifunctor, which is not a wire (as in @subseq-EW-join's Hinze-Marsden column).
#disp[#calc-table(cols: (1.5fr, 1fr), al: (left + horizon, left + horizon), 
  Thm[`[nil,cons]⟨g,`#frc([`suffix`])` E(g)⟩=F(⟨g,`#frc([`suffix`])` E(g)⟩)k` \
    #src[`k≜[zero⟨𝟙,`#frc([`𝟙`])`⟩,⟨w,⟨w `#frc([`𝟙`])`,π₂π₂⟩ cup⟩]`, `w≜(𝟙×π₁)⊕`: the value at the
     whole list, paired with the set of the values at its suffixes, runs `k`'s recursion.
 ]],
     // lean:AOP.A7_7_MSS.Kalg@745285de lean:AOP.A7_7_MSS.scanStep_union@82dd2f1a
  table.header([*the equation at that branch*], [*why*]),

  [`nil⟨g,`#frc([`suffix`])` E(g)⟩=zero⟨𝟙,`#frc([`𝟙`])`⟩`],
  [#src[`nil` has one suffix, itself, and `g(nil)=zero`, so the set is the singleton `{zero}`]],

  [`cons⟨g,`#frc([`suffix`])` E(g)⟩=(𝟙×⟨g,`#frc([`suffix`])` E(g)⟩)⟨w,⟨w `#frc([`𝟙`])`,π₂π₂⟩ cup⟩`],
  [#src[`g(cons(a,x))=a⊕(g(x))`, which is `w` reading `g(x)` off `π₁`; and the suffixes of
   `cons(a,x)` are `cons(a,x)` itself, whose value is that same `w`, together with those of `x`,
   which `π₂π₂` carries — so the two sets meet at `cup`]],
)]<mss-scan>

// B&dM Ex 7.40, p. 174–175: the four stages above, run as one chain from the specification down to
// the fold.  `g≜⦇[zero,⊕]⦈` throughout, as @mss-scan's `g`.
// Every row runs `[A]` to `A`, so the ends are drawn once.  @mss-shape's helper writes the TYPE
// along the wire, which is that display's content; here what changes is the boxes.
#disp[#calc-table(
  // B&dM p.175, Ex 7.40: "Finally, express list ⦇[c,f]⦈ · tails as a catamorphism and hence show how to
  // implement mss by a linear-time algorithm."
  Thm[#leanf("Freyd.Alg.RelSet.MSS.mss_eq_scan") \
    #src[maximum segment sum problem: #frc([`suffix`])` E(⦇[zero,⊕]⦈)` expressed as the catamorphism `⦇k⦈`,
     // mss-scan row: Ex 7.40
     hence `mss` implemented by a linear-time algorithm, `⊕≜` #frc([`⊸ zero ∪ plus`]) ` est(≥)` —
     @mss-defn; `k` and `w` — @mss-scan.
 ]],
    // lean:AOP.A7_7_MSS.mss_eq_scan@0844559d
  table.header([*circuit*], [*Hinze–Marsden*]),

  // #frc([`R`]) `=` #frc([`𝟙`]) `E(R)` (@adj-E-bend): the singleton BIRTHS the `E` and `est(≥)` KILLS
  // it, so no bead here carries a `%∋`.  One height per bead down the column, and a row that
  // collapses a pair puts its one bead midway between the two it replaces.
  [#vstep([], leanc("Freyd.Alg.RelSet.MSS.mss_shape.lhs"),
    [#src[`mss` is the greatest of the segment sums — @mss-defn]])],
  [#mh-segsum],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.mss_shape.rhs"),
    [#src[@mss-shape]])],
  // `suffix` is only LAX natural in `Rel`, so it is a NODE on the object wire like the rest; the outer
  // `E` runs past it, and `prefix sum` is where the `list` wire dies.
  [#mh-shape],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.mss_eq_scan_step2.rhs"),
    [#frc([`suffix`]) ` E(⦇[zero,⊕]⦈) est(≥)` \
     #src[the greedy theorem @greedy-thm72 at `R:=≥`, `S:=[zero,⊸ zero ∪ plus]` — @mss-mono is its
      condition and @mss-step its #frc([`S`]) ` est(≥)`; its `⊑` is an `=` because `⦇[zero,⊕]⦈` is
      entire and #frc([`prefix sum`]) ` est(≥)` simple #src[@takewhile-laws's last row]]])],
  [#mh-greedy],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.MSS.mss_eq_scan_step3.rhs"),
    [`⦇k⦈ π₂ est(≥)` \
     #src[@cata-defining at @mss-scan's equation, so `⦇k⦈=⟨⦇[zero,⊕]⦈,`#frc([`suffix`])
      ` E(⦇[zero,⊕]⦈)⟩`, of which `π₂` is the row above]])],
  [#lean("Freyd.Alg.RelSet.MSS.mss_eq_scan_step3.rhs")],
)
#align(center, block(inset: (y: 4pt))[#src[one fold builds the `n+1` running maxima and the final
  `est(≥)` reads them in one more pass, so `mss` is linear.]])
]<mss-deriv>

// `sticky` cannot reach through the breakable block `conf` wraps every display in, so the heading
// would sit alone at the foot of @mss-deriv's page.
#pagebreak(weak: true)
=== `filter(p)=⦇[nil,(π₁p→cons,π₂)]⦈` <sec-filter>

// B&dM Ex 7.41, p. 174.  @sec-takewhile with `subseq` for `prefix`: same `F`, `α`, `p`, `R`, same
// greedy theorem, and only the second branch of the algebra differs.
// One running example, as @takewhile-defn's: `A≜Nat` and `p≜even`.
#disp[#align(center, block(width: 21cm)[
#table(
  columns: (1.7cm, 5.3cm, 2.9cm, 4.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*type*], [*example*], [*in words*]),

  [`F`, `α`, `p`, `R`], [as in @takewhile-defn], [], [], [],

  [`π₂`], [`π₂` where @takewhile-defn has `⊸ nil`], [`A×[A]⟶[A]`], [`π₂(3,[1,2])=[1,2]`],
  [drop the head, keep the tail],

  [`subseq`], [`⦇[nil,π₂ ∪ cons]⦈` #h(4pt) #src[@comb-fns]], [`[A]⟶[A]`],
  [`[3,1,2] subseq [3,2]`],
  [`xs subseq ys⟺ys` is `xs` with elements dropped #h(4pt) — at each `cons`, drop the head or
   keep it],

 [`S`], [`[nil,π₂ ∪ (p×𝟙) cons]` #h(4pt) #src[]], [`F([A])⟶[A]`],
  // lean:AOP.A7_7_Filter.Salg@a0accc65
  [`(4,[2]) S [2]` #h(4pt) and #h(4pt) `(4,[2]) S [4,2]`, #h(4pt) but `(3,[2]) S [2]` only],
  [`subseq`'s algebra with one extra `p` — drop the head, or keep a head that passes `p`],

 [`𝟙⊑π₂R cons°` #h(4pt) #src[]], [], [], [],
  // lean:AOP.A7_7_Filter.id_le_pi2_lenLE_cons@44ddd75e
  [the tail is one shorter than the cons, so `π₂` loses the `est(R°)` at every step — where
   @takewhile-defn's loser is `nil`],
)
])]<filter-defn>

#disp[#calc-table(cols: 1fr, al: center + horizon, pr: 0pt, 
  Thm(cols: 1)[`(𝟙×R°)(π₂ ∪ (p×𝟙) cons)⊑(π₂ ∪ (p×𝟙) cons)R°` \
    #src[shortening the tail and then taking the step lands inside taking the step and then
 shortening the result]],
     // lean:AOP.A7_7_Filter.filter_mono@4095af88
  table.header([*formula* — the `cons` branch of `F(R°)S⊑SR°`; *reason* under each circuit]),

  [#hchain(fill: true,
  (none, [#leanc("Freyd.Alg.RelSet.Filter.filter_mono_step1.lhs")], [],
   [`(𝟙×R°)(π₂ ∪ (p×𝟙) cons)`]),

  (EQ, [#leanc("Freyd.Alg.RelSet.Filter.filter_mono_step1.rhs")],
   [`(𝟙×R°)(p×𝟙)=p×R°` #h(4pt) #src[@adj-all]], [`(𝟙×R°)π₂ ∪ (p×R°) cons`]),

  (EQ, [#leanc("Freyd.Alg.RelSet.Filter.filter_mono_step2.rhs")],
   [`(𝟙×R°)π₂=π₂R°` #h(4pt) #src[@subseq-outr-square]], [`π₂R° ∪ (p×R°) cons`]),

  (SQ, [#leanc("Freyd.Alg.RelSet.Filter.filter_mono_step3.rhs")],
   [`(p×R°) cons⊑(p×𝟙) cons R°` #h(4pt) #src[@takewhile-mono]], [`π₂R° ∪ (p×𝟙) cons R°`]),

  (SQ, [#leanc("Freyd.Alg.RelSet.Filter.filter_mono_cons.rhs")],
   [#src[@adj-all]], [`(π₂ ∪ (p×𝟙) cons)R°`]),
  )],
)
#align(center, block(inset: (y: 4pt))[#src[the `nil` branch: `nil⊑nil R°`.]])
]<filter-mono>

#let step = step.with(pw: 340pt)
// §13.3.4 rebound `est-Rc-box` to `est(≥)`, which is what the pictures below were drawing.
#disp[#calc-table(cols: (1fr, 4.4cm), al: (center + horizon, left + horizon), pr: 0pt, 
  Thm[#leanf("Freyd.Alg.RelSet.Filter.filter_step") \
    #src[the longest of the lists the algebra allows is the `cons` where the head passes `p`, and
 the tail where it does not]],
     // lean:AOP.A7_7_Filter.filter_step@504b7851
  table.header([*formula*], [*reason*]),

  [#step([])[#leanc("Freyd.Alg.RelSet.Filter.filter_step1.lhs")][]], [],

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.Filter.filter_step1.rhs")][`[`$frac(#[`nil`], ∋)$` est(R°),` $frac(#[`π₂ ∪ (p×𝟙) cons`], ∋)$` est(R°)]`]],
  [`S=[nil,π₂ ∪ (p×𝟙) cons]` #h(4pt) #src[@filter-defn] #h(4pt) — and the `%∋` of a coproduct of maps
   is the coproduct of their `%∋` #h(4pt) #src[@coprod-calc]],

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.Filter.filter_step2.rhs")][`[nil,` $frac(#[`π₂ ∪ (p×𝟙) cons`], ∋)$` est(R°)]`]],
  [`nil%∋` is the singleton `{nil}`, and `est(R°)` of a singleton is its element because `R°` is
   reflexive #h(4pt) #src[@est-defn]],

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.Filter.filter_step3.rhs")][]],
  [#frc([`π₂ ∪ (p×𝟙) cons`])` =⟨`#frc([`π₂`])`,`#frc([`(p×𝟙) cons`])`⟩ cup` #h(4pt) #src[@cup-defn]],

  [#step(EQ)[#leanc("Freyd.Alg.RelSet.Filter.filter_step4.rhs")][]],
  [`𝟙⊑π₂R cons°` #h(4pt) #src[@filter-defn] #h(4pt) — `xs R cons(a,xs)`, so `est(R°)` returns the
   `cons` where `p a` puts it in the set and `xs` where the set is `{xs}` #h(4pt) #src[@est-defn]],
)
#align(center, block(inset: (y: 4pt))[#src[the head is dropped, not the whole tail: that is the one
  place `π₂` shows against @takewhile-step's `⊸ nil`.]])
]<filter-step>

// B&dM Ex 7.41, p. 174, assembled: the four displays above are the four steps, and the `E[A]` the
// transpose births is what the greedy step moves inside the reduce.
// ONE WIRE, `[A]` to `[A]`, its type written along it; `mid: none` once `E[A]` has gone inside the
// reduce.  Its own run and not @takewhile-step's, which starts at `F([A])` and belongs to §13.3.3.
// `S` is defined in @filter-defn, three pages back, and every row below reads it: the definition is
// repeated here rather than looked up, in that table's own five columns.
#disp[#align(center, block(width: 21cm)[
#table(
  columns: (1.7cm, 5.3cm, 2.9cm, 4.6cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 7pt, stroke: 0.4pt + luma(190),
  table.header([*name*], [*definition*], [*type*], [*example*], [*in words*]),

  [`S`], [`[nil,π₂ ∪ (p×𝟙) cons]` #h(4pt) #src[@filter-defn]], [`F([A])⟶[A]`],
  [`(4,[2]) S [2]` #h(4pt) and #h(4pt) `(4,[2]) S [4,2]`, #h(4pt) but `(3,[2]) S [2]` only],
  [`subseq`'s algebra with one extra `p` — drop the head, or keep a head that passes `p`],
)])]

#disp[#calc-table(cols: (1fr, 6.3cm), 
  // B&dM p.175, Ex 7.41: "In words, filter p x returns the longest subsequence of x with the property that
  // all its elements satisfy p." … "derive the standard program for filter."
  Thm[#leanf("Freyd.Alg.RelSet.Filter.filter_eq_cata") \
    // filter-simple row: Ex 7.41
    #src[filter: `filter(p) x` returns the longest subsequence of `x` with the property that all its
     elements satisfy `p`; the catamorphism is the standard program; `R` a preorder.
 ]],
     // lean:AOP.A7_7_Filter.filter_eq_cata@0882803d
  table.header([*circuit* — one wire, its type written along it], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Filter.filter_laws_step1.lhs"),
 [#src[@comb-fns]])],
    // lean:AOP.A7_7_Filter.filter@8a5f6aed
  [#align(center, lean("Freyd.Alg.RelSet.Filter.filter_laws_step1.lhs"))],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Filter.filter_laws_step1.rhs"),
    [#src[`subseq list(p)=⦇S⦈` — @takewhile-alg's header, `subseq` for `prefix`]])],
  [#align(center, lean("Freyd.Alg.RelSet.Filter.filter_laws_step1.rhs"))],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Filter.filter_greedy.lhs"),
    [#src[@greedy-thm72 at `R°`, whose hypothesis `F(R°)S⊑SR°` is
 @filter-mono]])],
  // The `E` wire is gone: the transpose and `est(R°)` now meet inside the reduce.  `list` and `A` are
  // unchanged, so they are drawn where the two panels above draw them.
  [#align(center, lean("Freyd.Alg.RelSet.Filter.filter_greedy.lhs"))],

  [#vstep(EQ, [#leanc("Freyd.Alg.RelSet.Filter.filter_eq_cata.rhs")],
    [#src[@filter-step]])],
  // Empty: the step only renames the algebra, and the picture above already draws the reduce.
  [],

  [#vstep(EQ, [],
    // lean:AOP.A7_7_Filter.filter_entire@587e37a8
    // lean:AOP.A7_7_Filter.filter_simple@de8b5dbc
    [#src[the catamorphism is entire and `filter(p)` simple, so `⊒` is `=`]])],
         // lean:Freyd.S2_10.eq_of_le_entire_simple@e9665c67
  [],
)
#align(center, block(inset: (y: 4pt))[#src[`(subseq list(p))°(subseq list(p))∩R∩R°⊑𝟙` fails — two
  `p`-subsequences of one list can be of equal length and different — so §@sec-takewhile's uniqueness
  argument does not transfer. What survives `est(R°)` is the one keeping *exactly* the passing
  elements: a subsequence that drops a passing element is beaten by the one that keeps it.]])
]<filter-deriv>

// Its own page: the section opens with a long definition display and was starting mid-page.
#pagebreak(weak: true)
== Planning a company party

// B&dM §7.3, p. 175.  No numbered equations; the two monotonicity claims are the section's own
// proof obligations, and the exercise blocks (7.43–7.44) are left out as everywhere else.
#disp[#table(
  columns: (7.8cm, 4.9cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*note*]),

 [`tree A::=node (A,[tree A])` #src[]],
  // lean:AOP.A6_RoseTree.Rose@1e5d7a7f
  [`𝒜⟶𝒜`],
  [The company hierarchy: an employee, and the list of subtrees under them.],

 [`F(A,B)=A×[B]` #src[]],
  // lean:AOP.A6_RoseTree.F@bd6da71e
  [`𝒜×𝒜⟶𝒜`],
  [The base functor `tree` folds: an employee beside the recursive position, one layer deep.],

  [`rating`],
  [`A⟶Real`],
  [What one employee is worth as a guest.],

 [`cost≜list(rating) sum` #src[]],
  // lean:AOP.A7_3_Party.cost_eq@6d5c7097
  [`[A]⟶Real`],
  [What a guest list is worth.],

 [`R≜cost≤cost°` #src[]],
  // lean:AOP.A7_3_Party.R_eq@9fa61324
  [`[A]⟶[A]`],
  [The preorder the guest list is maximised over.],

  [`choose≜π₁ ∪ π₂`],
  [`[A]×[A]⟶[A]`],
  [Takes one of the two parties a subtree returns.],

  [`include≜(𝟙×(list(π₂) concat)) cons`],
  [`F(A,[A]×[A])⟶[A]`],
  [The party that invites the root, which puts every immediate subtree's root out. A map.],

  [`exclude≜(𝟙×(list(choose) concat))π₂`],
  [`F(A,[A]×[A])⟶[A]`],
  [The party that leaves the root out, so each subtree is free to choose. Not a map.],

  [`S≜⟨include,exclude⟩`],
  [`F(A,[A]×[A])⟶[A]×[A]`],
  [The algebra: one step returns both parties of a subtree at once.],

 [`party≜⦇S⦈ choose` #src[]],
  // lean:AOP.A7_3_Party.party_eq@cb4fab14
  [`tree A⟶[A]`],
  [Every guest list the president's ruling allows.],

  [the specification \ $frac(#[`party`], ∋)$ `est(R°)`],
  [`tree A⟶[A]`],
  [A guest list of greatest total conviviality.],
)]<party-defn>

=== `include` and `exclude` <sec-party-algebras>

// Coordinates are literal: `d` is cetz.draw here and `e` is draw.typ's `∋`, so the six nodes cannot
// be named after the letters they carry.
#disp[#block(breakable: false)[#P(cetz.canvas(length: 0.8cm, {
  for (p, q) in (((0, 2.2), (-2, 0)), ((0, 2.2), (2, 0)), ((-2, 0), (-3, -2.2)),
                 ((-2, 0), (-1, -2.2)), ((2, 0), (3, -2.2))) { d.line(p, q, stroke: 0.75pt + black) }
  // Ratings deliberately not 1–6 in node order: as a run they read as indices, not as values.
  for (x, y, n, r) in ((0, 2.2, "a", "3"), (-2, 0, "b", "7"), (2, 0, "c", "2"),
                       (-3, -2.2, "d", "5"), (-1, -2.2, "e", "1"), (3, -2.2, "f", "8")) {
    node(x, y, black, [#raw(n) #text(9pt, luma(105))[#r]])
  }
}), s: 100%)
#align(center, src[the small grey number is the employee's rating])]]<party-example-tree>

// The fold on that tree, bottom-up; the last row reads its two cells off the rows for `b` and `c`.
// The `#src` block is 16.5cm, not the text width: at 22cm the wrap falls inside `[a,d,e,f]=17`.
#disp[
#table(
  columns: (2.0cm, 6.3cm, 7.3cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*node*], [*the algebra's input* \ `A×[[A]×[A]]`], [*`include`*], [*`exclude`*]),

  [`d`, `e`, `f`],
  [`(d,[])`],
  [`[d]`],
  [`[]`],

  [`b`],
  [`(b,[([d],[]),([e],[])])`],
  [`[b]`],
  [`[d,e]`, #h(4pt) `[d]`, #h(4pt) `[e]`, #h(4pt) `[]`],

  [`c`],
  [`(c,[([f],[])])`],
  [`[c]`],
  [`[f]`, #h(4pt) `[]`],

  [`a`],
  [`(a,[([b],…),([c],…)])`],
  [`[a]⧺exclude(b)⧺exclude(c)`],
  [`choose(b)⧺choose(c)`],
)
#align(center, block(width: 16.5cm, inset: (y: 4pt))[#align(center)[#src[with those ratings,
  `est(R°)` keeps `([b]=7,[d,e]=6)` at `b`, where `include` wins, and `([c]=2,[f]=8)` at `c`, where
  `exclude` wins, so at the root `include=[a,d,e,f]=17` beats `exclude=[b,f]=15`, and `choose`
  takes 17.]]])
]<party-example>

// `list(π₂)` is ONE box, not the `⊸ ⊗ 𝟙` inside the relator: the picture is here for the shape of
// `include`, and opening `π₂` up costs a discard stub per list element that says nothing about it.
// Both pictures share every stage's x: the boxes are right-aligned at 9.2, so the two read one under
// the other and a wire's type is found at the same place in each.
// The BOUNDARY of a circuit: nothing in `circuit.typ` or `draw.typ` draws one — `capbox` frames a
// picture and its caption, `gbox` frames a single relation — so one helper serves both algebras.
// The frame is 1.9pt, well over the 1.1pt of a wire and of a box edge: at wire weight it reads as
// one more wire.  Dark grey, not black, so the boxes ON the wires stay the darkest ink in the picture.
#let portbox(a, b, ports) = {
  d.rect(a, b, stroke: 1.9pt + luma(55), radius: 0.14)
  for (x, y, l) in ports { lab(x, y, black, l) }
}

#disp[#P(cetz.canvas(length: 0.8cm, {
  let y = 0.8
  portbox((-0.9, -1.8), (22.4, 1.8),
    ((-3.2, y, [`a:A`]), (-3.2, -y, [`[[A]×[A]]`]), (24.2, 0, [`adef:[A]`])))
  lab(-3.2, 2.5, black)[`include`$=$]
  wire((-1.5, y), (19.9, y))                 // the root, straight through: the `𝟙` of `𝟙 × (…)`
  wire((-1.5, -y), (6.6, -y))
  gbox((6.6, -y), [`list(π₂)`], w: 2.6, h: 0.75, chamfer: false)
  wire((9.2, -y), (13.8, -y))
  gbox((13.8, -y), [`concat`], w: 1.9, h: 0.75, chamfer: false)
  wire((15.7, -y), (18.9, -y))
  gbox((18.9, 0), [`cons`], w: 1.4, h: 2 * y + 0.35, chamfer: false)
  wire((20.3, 0), (22.9, 0))
  lab(3.7, -y + 0.5, black)[`b`]; lab(4.9, -y + 0.5, black)[`c`]
  lab(3.7, -y - 0.5, black)[`de`]; lab(4.9, -y - 0.5, black)[`f`]
  lab(10.2, -y + 0.5, black)[`[[A]]`]
  lab(11.7, -y - 0.5, black)[`de`]; lab(12.9, -y - 0.5, black)[`f`]
  lab(16.5, -y + 0.5, black)[`[A]`]
  lab(17.8, -y - 0.5, black)[`def`]
}), s: 80%)
#align(center, src[])
// lean:AOP.A7_3_Party.include_eq@afb11121
]<include-pic>

// The trailing `π₂` is `⊸ ⊗ 𝟙`, and here the discard IS the step, so it is drawn and not boxed.
// `list(choose)` keeps the chamfer: `choose` is a relation, where `include`'s `π₂` is a map.
#disp[#P(cetz.canvas(length: 0.8cm, {
  let y = 0.8
  portbox((-0.9, -1.8), (22.4, 1.8),
    ((-3.2, y, [`a:A`]), (-3.2, -y, [`[[A]×[A]]`]), (24.2, -y, [`bf:[A]`])))
  lab(-3.2, 2.5, black)[`exclude`$=$]
  wire((-1.5, y), (18.9, y))                 // the root, thrown away by the `⊸` of `π₂`
  wiredot((18.9, y))
  wire((-1.5, -y), (5.9, -y))
  gbox((5.9, -y), [`list(choose)`], w: 3.3, h: 0.75)
  wire((9.2, -y), (13.8, -y))
  gbox((13.8, -y), [`concat`], w: 1.9, h: 0.75, chamfer: false)
  wire((15.7, -y), (22.9, -y))
  lab(3.7, -y + 0.5, black)[`b`]; lab(4.9, -y + 0.5, black)[`c`]
  lab(3.7, -y - 0.5, black)[`de`]; lab(4.9, -y - 0.5, black)[`f`]
  lab(10.2, -y + 0.5, black)[`[[A]]`]
  lab(11.7, -y + 0.5, black)[`b`]; lab(12.9, -y - 0.5, black)[`f`]
  lab(16.5, -y + 0.5, black)[`[A]`]
  lab(17.8, -y - 0.5, black)[`bf`]
}), s: 80%)
#align(center, src[])
// lean:AOP.A7_3_Party.exclude_eq@52820610
]<exclude-pic>

// `choose = π₁ ∪ π₂` is a choice PER ELEMENT, so `list(choose)` multiplies: two items, four lists.
#disp[#align(center, grid(
  columns: 5, column-gutter: 16pt, row-gutter: 6pt,
  align: (left + horizon, center + horizon, center + horizon, center + horizon, center + horizon),
  grid.cell(colspan: 5, align: left)[`list(choose) [([d],[]),([e],[])]`],
  [#h(1em)`1st item`], grid.cell(colspan: 4, align: left)[`([d],[])  choose↦[d]  or  []`],
  [#h(1em)`2nd item`], grid.cell(colspan: 4, align: left)[`([e],[])  choose↦[e]  or  []`],
  [#h(1em)`2×2=4 combinations:`], [`[[d],[e]]`], [`[[d],[]]`], [`[[],[e]]`], [`[[],[]]`],
  [#h(1em)`concat flattens:`], [`[d,e]`], [`[d]`], [`[e]`], [`[]`],
))]<party-list-choose>

=== `list((R×R)°)` <sec-party-listrr>

// The two lists are stacked so the correspondence is read DOWN a column: `list` relates lists of the
// same length position by position, so everything `list((R×R)°)` says is what `(R×R)°` says of one item.
#disp[#align(center, grid(
  columns: 6, column-gutter: 10pt, row-gutter: 5pt,
  align: (center + horizon, center + horizon, center + horizon, center + horizon, center + horizon,
          left + horizon),
  [`[`], [`([b],[d,e])`], [`,`], [`([c],[f])`], [`]`], [],
  [], [`│`], [], [`│`], [], [],
  [], [`▼`], [], [`▼`], [], src[`list((R×R)°)`, elementwise],
  [`[`], [`([b],[d])`], [`,`], [`([c],[])`], [`]`], [],
))
// One raw block, not a grid: the ticks land under `b` and `d` because every glyph is one monospace
// advance wide, which no measured column can promise.
#v(8pt)
#align(center)[```
([b],[d,e])
  │   └── exclude: the best party in b's subtree when b does not come
  └────── include: the best party in b's subtree when b comes
```]
#align(center, src[])]<party-listrr>
// lean:AOP.A7_3_Party.party_listrr_example@286e6447

// `(R×R)°` is TWO demands, one per component, and at `a` both elements move, each in its second —
// the table is here because "the relator relates them elementwise" hides which component that is.
#disp[
#table(
  columns: (3.6cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*element*], [*1st component* \ `include`], [*2nd component* \ `exclude`]),

  [1st, `([b],[d,e])`],
  [`[b] R° [b]` \ #src[`7≥7`, reflexivity]],
  [`[d,e] R° [d]` \ #src[`6≥5`, and `([b],[d,e])` is the pair `est(R°)` keeps at `b`]],

  [2nd, `([c],[f])`],
  [`[c] R° [c]` \ #src[`2≥2`, reflexivity]],
  [`[f] R° []` \ #src[`8≥0`, and `([c],[f])` is the pair `est(R°)` keeps at `c`]],
)
#align(center, src[the first component of `𝟙×list((R×R)°)` is the root employee.
 ])
  // lean:AOP.A7_3_Party.party_listrr_example@286e6447
]<party-rr>

// Each note in its own block: the template indents the second of two consecutive paragraphs, and an
// indented note reads as a continuation of the one above it.
#block[#src[`R≜cost≤cost°` is a preorder, so the components that do not move are related by
  reflexivity — `(R×R)°` demands a relation in *both* components, it cannot skip one.]]

#block[#src[`R` compares cost only, not contents: `[f] R° []` is legal though `[f]` has an element
  `[]` does not. That is why the three leaves of §@sec-party-mono's proof all reduce to
  "`cost` is a sum".]]

=== `(𝟙×list((R×R)°))S⊑S(R×R)°` — `S : F([A]×[A])⟶[A]×[A]` monotonic on `(R×R)°` <sec-party-mono>

// @mon-str at `F := (− × [−])`, `A := [A]×[A]`, `R := (R×R)°`, so `F((R×R)°) = 𝟙×list((R×R)°)`; @lax-defn at
// `G := F`, `F := Id`, `φ := S` for the panels, `rev` putting the smaller side left, where `⊑` points.
#disp[#pair(
  leancd("Freyd.Alg.RelSet.Party.party_mono"),
  // `length` up from the file's 0.95cm: the port labels do not scale with it, and at 0.95cm the two
  // top ports touch — `F` `[A]×[A]`, which the reader reads across, comes out as `F[A]`.
  homeq(`F`, `[A]×[A]`, `S`, `(R×R)°`, `S`, `[A]×[A]`, ctop: GIVEN1, cmid: GIVEN2, cbot: GIVEN1,
    regions: auto, sep: text(SLACK)[`⊑`], rev: true, gap: 1.4, length: 1.35cm),
 [`(𝟙×list((R×R)°))S⊑S(R×R)°` #src[]],
  // lean:AOP.A7_3_Party.party_mono@8a43178e
)]<party-mono>

// @adj-E-bend's shapes at this instance: a transpose is the dashed INDUCED arrow the adjunction
// produces, and the factorisation it runs through is that picture's GIVEN2 path.
#disp[#pair(
  leancd("Freyd.Alg.RelSet.Party.party_absorb.lhs"),
  leancd("Freyd.Alg.RelSet.Party.party_absorb.rhs"),
  [$frac(#[`⦇S⦈choose`], ∋)$ `=` $frac(#[`⦇S⦈`], ∋)$ `E(choose)` #h(1cm) #src[@pow-laws, absorption,
 ]],
   // lean:AOP.A4_6.Λ_absorption@e87bd8f2
   // lean:AOP.A7_3_Party.party_absorb@5ae02626
)]<party-absorb>

// `(label, width, chamfer)`, set once: the same box is drawn in up to four rows, and a width typed
// per row is a width that drifts.  No chamfer is a map — `concat` is one, `list(g)` is not (`choose`).

// A PRODUCT IS TWO WIRES.  `F([A]×[A])=A×[[A]×[A]]` enters as two, `[A]×[A]` leaves as two, and
// `𝟙×list((R×R)°)` is the root's wire running straight past a box that sits on the other one — `×` costs no
// notation, it IS the second wire.  `[[A]×[A]]` stays ONE wire: its outermost former is the list.
// The shape below opens with `pairin`, at two strand heights, so the height is its parameter.
#let pairin(y, items) = {
  lab(-0.55, y, black)[`A`]; lab(-1.6, -y, black)[`[[A]×[A]]`]
  wire((0, y), (boxrun-w(items), y))
  boxrun(0, -y, items)
}
// A branch's shape: the root straight through the upper wire, the subtrees' pairs down the lower
// one, both entering the box that spans them — `h` once `include`/`exclude` is unfolded.
// Every row's picture is drawn at ONE length and ONE scale, and a scale typed per cell is a scale
// that drifts — both times this one changed, it had to change in every cell.
#let EW = [`E`]

// Only the three `⊑` steps are rows: the five `=` steps are `F(RS)=F(R)F(S)`, `(R×S)(U×V)=(RU)×(SV)`
// and the branch unfolded and refolded, and BOTH pictures draw either side of them with the same ink.
#let step = step.with(pw: 319pt)
#disp[#table(
  // Not `HMW`: that column holds a circuit, this one a panel, and 8.92cm is the exported panel's own
  // width — five wires, `[A]` split into `list` and `A` the way every other panel splits it.
  columns: (1fr, 8.92cm),
  align: (center + horizon, center + horizon),
  // `y: 1pt`, tighter than the note's usual 3pt: the four rows plus the key list are a page exactly.
  inset: (x: 9pt, y: 1pt), stroke: 0.4pt + luma(190),
  // One shape instantiated three times, so the three `⊑` stand in a column.
  Thm[#align(center, grid(columns: 3, column-gutter: 6pt, row-gutter: 3pt,
    align: (right + horizon, center + horizon, left + horizon),
    grid.cell(colspan: 3, align: center)[`S≜⟨include,exclude⟩`],
    [`(𝟙×list((R×R)°))S`], SQ, [`S(R×R)°`],
    [`(𝟙×list((R×R)°))include`], SQ, [`include R°`],
    [`(𝟙×list((R×R)°))exclude`], SQ, [`exclude R°`],
  ))
  #src[bettering both parties of every subtree before the node's algebra runs gets no further than
   running it first and bettering the two parties it returns,
 ]],
   // lean:AOP.A7_3_Party.branch_monotonic@668fb773 lean:AOP.A7_3_Party.exclude_monotonic@92dade83
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#step([], leanc("Freyd.Alg.RelSet.Party.branch_step1.lhs"))[]],
  [#lean("Freyd.Alg.RelSet.Party.branch_step1.lhs")],

  [#step(SQ, leanc("Freyd.Alg.RelSet.Party.branch_step1.rhs"))[]],
  [#lean("Freyd.Alg.RelSet.Party.branch_step1.rhs")],

  [#step(SQ, leanc("Freyd.Alg.RelSet.Party.branch_step2.rhs"))[]],
  [#lean("Freyd.Alg.RelSet.Party.branch_step2.rhs")],

  [#step(SQ, leanc("Freyd.Alg.RelSet.Party.branch_step3.rhs"))[]],
  [#lean("Freyd.Alg.RelSet.Party.branch_step3.rhs")],
)

#v(3pt)

// The key list, read DOWNWARD like the pictures: one line per bead `R°` walks past.
#align(center, block(width: 20.5cm)[#src[#grid(
  columns: (1.7cm, auto),
  row-gutter: 3.5pt, align: (left, left),
  [`g`],
  [`(R×R)°g⊑gR°` \ `g:=π₂` is `(R×R)°π₂=(Dom(π₁R°))π₂R°⊑π₂R°`
 #src[], `g:=π₁` its mirror
   // lean:AOP.A7_3_Party.include_monotonic@226b6fb6
   `(Dom(π₂R°))π₁R°⊑π₁R°` — 1 and 4 of @bdm-prod-laws, then `Dom⊑𝟙`; `g:=choose≜π₁ ∪ π₂` is the union
 of the two #h(4pt) #src[@lax-closure].
   // lean:AOP.A7_3_Party.chooseR_monotonic@c712a88d
   `list` monotonic, @relator-defn],
  [`concat`],
  [`list(R°)concat⊑concat R°` \ a LEAF: no law above it. `cost` is a sum, so
   `cost(concat(xss))=sum(list(cost)(xss))` and a cheaper part makes a cheaper whole.
 #src[]],
   // lean:AOP.A7_3_Party.concat_monotonic@084e46a9  — B&dM's exercise
  [`h`],
  [`(𝟙×R°)h⊑hR°` \ a LEAF: `cost(cons(a,xs))` `=rating(a)+cost(xs)`, so a cheaper tail
 makes a cheaper list. #src[]
   // lean:AOP.A7_3_Party.cons_monotonic@e5288fc0  — B&dM's exercise
   For `h:=π₂` it is an EQUALITY `(𝟙×R°)π₂=(Dom(π₁))π₂R°`
 `=π₂R°` #src[]: `π₁` is a map, hence entire, so
   // lean:AOP.A6_1_RelSet.rprodMap_id_snd@dc93a451
   `Dom(π₁)=𝟙` — @dom-laws],
)]])

#v(3pt)

#align(center, table(
  columns: 3, align: center + horizon,
  inset: (x: 9pt, y: 2pt), stroke: 0.4pt + luma(190),
  table.header([`(𝟙×(list(g) concat))h`], [`g`], [`h`]),
  [`include`], [`π₂`], [`cons`],
 [`exclude` #src[]], [`choose`], [`π₂`],
  // lean:AOP.A7_3_Party.exclude_monotonic@92dade83
))
]<party-mono-branch>

// The `⊑` is STRICT, and the witness says where: the `g` row's one inequality is `Dom⊑𝟙`.
#disp[#table(
  columns: (auto, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`R≜{(0,0)} : {0,1}⟶{0,1}`], [not entire — undefined at `1`],

  [`(R×R)choose` at `(0,1)`], [nothing — `R×R` needs BOTH components related, and `R` is undefined
   at `1`],

  [`choose R` at `(0,1)`], [`0` — `choose` picks the first component `0`, and `R 0 0` holds],

  [`((0,1),0)`], [in `choose R`, not in `(R×R)choose`
 #h(4pt) #src[]],
   // lean:AOP.A7_3_ChooseStrict.choose_monotonic_strict@2b446ff0

  [`(R×R)choose=choose R`], [iff `R` is entire — `Dom⊑𝟙` is the `g` row's only inequality step,
   and it is an equality iff `Dom(R)=𝟙`],
)]<choose-strict>

=== The derivation <sec-party-deriv>

// The pictures are ONE WIRE from `tree A` to `[A]`, a box per factor; `[A]×[A]` is where it runs as
// TWO — `est((R×R)°)` opens the strand into a pair and `choose/∋` closes it again.  Every `R/∋` is a
// MAP (@pow-laws), so every fraction box is square and every other box chamfered.
// `13.4.4a`'s row: the only one where the type actually changes mid-run, so it is the only one
// that gets the wire types spelled out — `E([A]×[A])` in, `est((R×R)°)` opens the pair, `[A]` on
// each of the two strands it opens into (a PRODUCT is two wires, never one wire marked `×`).

// `⦇−⦈` drawn as MELLIÈS' functorial box: the body's own circuit, inside brackets.  A bar is where
// the type changes, so nothing crosses the LEFT one — the tree arrives at it and the algebra's two
// strands start there, which is the recursion — while the body's output IS the fold's and runs on.


// ---- The two Hinze-Marsden panels: what surrounds the `⦇ ⦈`, and what sits inside it.  A wire is
// a FUNCTOR and a bead an arrow, so SUGAR IS UNDONE BEFORE DRAWING and at the ends too: `[A]` is the
// `list` wire beside the `A` wire, `tree A` the `tree` wire beside it, `[A]×[A]` the relator `Δ`
// (`X↦X×X`) over both.  One lane then carries `tree` above the bead that eats it and `list` below.
// The transpose is split, #frc([`R`])`=`#frc([`𝟙`])`E(R)` (@adj-E-bend): the singleton OPENS the `E`
// wire — a bead of its own, off the object wire — and an `est` CLOSES it.  So `E(choose)` is the
// `choose` bead with `E` running past, and `party`'s absorption step is one picture drawn twice.
// The lanes, outermost functor LEFTMOST: the composite reads across applicatively, `𝟏` at the right.
// Two of these panels stack in ONE cell from the greedy step on, and the seven rows are a page
// exactly: this is the scale that buys the last row its reason line.

// The panel pair a row shows.  `none` is a panel the row above already drew — the outside is fixed
// from the greedy step on, and the inside does not exist before it.
#let dcell(o, i) = align(center, stack(spacing: 5pt, ..(o, i).filter(x => x != none)))

// Every row writes one fraction where its panel draws two beads: the unit `H%∋=(𝟙%∋)E(H)` opens
// `E` outside `H`.  One law, instantiated at the numerator each row names.

// `est(R°)` holds one height down the family and `choose` another, so what moves is the fold: the
// bead that eats the `tree` wire, and where the `E` it opens is closed.
#let d-out1 = lean("Freyd.Alg.RelSet.Party.party_open.lhs")
// Rows 2 and 3 draw the SAME panel: `E(⦇S⦈ choose)=E(⦇S⦈)E(choose)`, which is the absorption step.
// The ink spells the LOWER of the two rows: `⦇S⦈%∋` and `choose` are two beads, and row 2's
// `frc(⦇S⦈ choose)` is that one absorption step away.
#let d-out4 = lean("Freyd.Alg.est_Λ_est_le.rhs")

// Inside the brackets the source is `F([A]×[A])=A×[[A]×[A]]`: five wires down to the object.  The
// algebra is natural in NOTHING — it eats every functor the source carries and MAKES the pair it
// returns — so all four strands land on its bead and the two it returns are born there.
#let d-in5 = lean("Freyd.Alg.RelSet.Party.party_pair_step.rhs")
#let d-in6 = lean("Freyd.Alg.RelSet.Party.include_step.rhs")
// `list(`#frc([`choose`])` est(R°))` opens its `E` INSIDE the list: the transpose is taken once per
// element, and `concat` is what finally eats the list the elements sat in.  The row writes the two
// beads under one `list` wire as one application, which is `F(R)F(S)=F(RS)` at `F:=list`.
// HAND-KEPT lanes, dots added by hand: regenerated, the unit's `E` lane goes leftmost and the sweep
// reads `𝟙%∋` outside the `list` it is stated inside.
#let d-in7 = lean("Freyd.Alg.RelSet.Party.exclude_step.lhs")

// Not `P`: its 5pt of vertical inset is what `vstep`'s own 5pt of spacing already gives, and the
// seven rows are a page exactly — the scale below is what those two insets bought.

// The reason rides UNDER the formula, in the picture's own column: a column of its own cost the
// circuits 3.8cm, and the two laws that would not fit it are now written out in full.  `vstep`, not
// `step`: a cell whose height `layout` decides is measured on the branch it does not draw, and the
// third line then lands under the row's rule.
#disp[#table(
  columns: (1fr, 6.6cm),
  align: (left + horizon, center + horizon),
  // Four rows here and three in the next display: at the book's own panel metric the seven no longer
  // fit one page, and the cut is where the fold is opened — outside the `⦇ ⦈` here, inside it there.
  inset: (x: 8pt, y: 2pt), stroke: 0.4pt + luma(190),
  Thm[#leanf("Freyd.Alg.RelSet.Party.party_laws") \
    #src[the best of every guest list the president allows is one pass up the tree, each subtree
     handing up its best party with its boss in and its best with the boss out, and `choose` taking
 the better of the two at the root]],
     // lean:AOP.A7_3_Party.party_laws@00692234
  table.header([*circuit*],
    [*Hinze–Marsden* — outside the `⦇ ⦈`]),

  [#vstep([], dcell(leanc("Freyd.Alg.RelSet.Party.party_open.lhs"), none),
    [#src[the specification — @party-defn]])],
  [#dcell(d-out1, none)],

  [#vstep(EQ, dcell(leanc("Freyd.Alg.RelSet.Party.party_open.rhs"), none),
    [#src[`party≜⦇S⦈ choose` — @party-defn]])],
  [#dcell(lean("Freyd.Alg.RelSet.Party.party_open.rhs"), none)],

  [#vstep(EQ, dcell(leanc("Freyd.Alg.est_Λ_est_le.lhs"), none),
    [#src[#frc([`⦇S⦈ choose`])`=`#frc([`⦇S⦈`])` E(choose)` — @party-absorb]])],
  [#dcell(lean("Freyd.Alg.est_Λ_est_le.lhs"), none)],

  [#vstep(RQ, dcell(leanc("Freyd.Alg.est_Λ_est_le.rhs"), none),
    // party-branch row: Ex 7.38
    [#src[`(R×R)°choose⊑choose R°` — @party-mono-branch's `g` row,
 ]])],
  [#dcell(d-out4, none)],
)]<party-laws>

#disp[#table(
  columns: (1fr, 6.6cm),
  align: (left + horizon, center + horizon),
  inset: (x: 8pt, y: 2pt), stroke: 0.4pt + luma(190),
  table.header([*circuit*],
    [*Hinze–Marsden* — inside the `⦇ ⦈`; a fork drawn at one branch]),

  [#vstep(RQ, dcell(none, leanc("Freyd.Alg.RelSet.Party.party_pair_step.rhs")),
    [#src[from here `⦇ ⦈` is drawn open — the two bars, with the algebra's own circuit between them;
      // greedy row: Theorem 7.2
      `(𝟙×list((R×R)°))S⊑S(R×R)°` at `(R×R)°`, @party-mono,
 ]])],
      // lean:AOP.A7_2.greedy@21400acf
  [#dcell(none, d-in5)],

  [#vstep(RQ, dcell(none, leanc("Freyd.Alg.RelSet.Party.include_step.rhs")),
    // pair_est_le row: Ex 7.15
    [#src[`⟨`#frc([`include`])` est(R°),`#frc([`exclude`])` est(R°)⟩⊑`#frc([`S`])` est((R×R)°)`,
 ]])],
      // lean:AOP.A7_3_Party.pair_est_le@75a48598
  [#dcell(none, d-in6)],

  [#vstep(RQ, dcell(none, leanc("Freyd.Alg.RelSet.Party.exclude_step.lhs")),
    [#src[`include` a map, `est(R°)` into each branch,
 ]])],
      // lean:AOP.A7_3_Party.graph_le_Λ_est@32e3aa7d lean:AOP.A7_3_Party.exclude_step@963c1784
  [#dcell(none, d-in7)],
)]<party-laws-fold>

// Its own page: the section opens with a long definition display and was starting mid-page.
#pagebreak(weak: true)
== Shortest paths on a cylinder

// B&dM §7.4, p. 179, with every type a matrix: `A[1]≜A`, `A[m+1]≜A×A[m]`, `A[m][n]≜(A[n])[m]`,
// outermost index first, and `Vec(k)` the functor `X↦X[k]`.  The count of columns crossed and of
// candidate paths is then in the type, so `E` never appears and `wrap`/`cons` are identities.  The
// list version is @sec-cyl-lists.
#disp[#table(
  columns: (2.6cm, 4.4cm, 7.4cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([], [*on `L=list⁺`, @sec-cyl-gen*], [*on `Vec`*], [*note*]),

  [`F`],
  [`F(A,X)=A+A×X`],
  [`F(A,A[m])=A[1]+A[m+1]`],
  [A square alone, or in front of the path so far.],

  [the input],
  [`L(N A)`],
  [`A[m][n]≜(A[n])[m]`],
  [`m` columns of `n` squares, outermost index first — the matrix itself.],

  [a path],
  [`L A`, a non-empty list],
  [`A[1]≜A`, `A[m+1]≜A×A[m]`],
  [Through `m` columns, `m` squares: the count is in the type. A one-square path is the square; `Vec(m)` is the functor `X↦X[m]`.],

  [the paths into a row],
  [`E(L A)`],
  [`A[p][m]`, `p=3^(m-1)`],
  [Three moves per column crossed, so this count is in the type too; a set forgets it.],

  [`α`],
  [`[wrap,cons]` \ `F(A,LA)⟶LA`],
  [`wrap=𝟙:A⟶A[1]` \ `cons:A×A[m]⟶A[m+1]`],
  [`wrap` is an identity; `cons` is only an iso, so it stays a bead.],

  [`moves`],
  [`NA⟶E(NA)`],
  [`X[n]⟶X[3][n]`],
  [`moves(x)=(up(x),x,down(x))`, a `3×n` matrix.],

  [`trans`],
  [`E(NX)⟶N(EX)`],
  [`X[3][n]⟶X[n][3]`],
  [The transpose.],

  [`union`],
  [`E(EX)⟶EX`],
  [`concat:X[j][k]⟶X[jk]`],
  [The `j` rows laid end to end; `j` is `3` inside `gen` and `n` inside `paths`.],

  [`zip`],
  [`F(NA,NB)⟶NF(A,B)`],
  [`F(A[n],B[n])⟶F(A,B)[n]`],
  [Unchanged.],

  [`cp`],
  [`F(A,EB)⟶E(F(A,B))`],
  [`A×B[p]⟶(A×B)[p]`],
  [The square paired with each of the `p` candidates.],

  [`est(R)≜∋∩(∈\R°)`],
  [`E X⟶X`],
  [`X[k]⟶X`, `∋:X[k]⟶X`],
  // lean:AOP.A7_4_CylinderVecRel.Vec.Rel.est@d89b35a7
  // lean:AOP.A7_4_CylinderVecRel.Vec.Rel.est_eq@6474d151
  [A component that is `R`-below every component; `∋` is "is some component" and `∈` its converse.],

  [`R≜sum≤sum°`],
  [`L Nat⟶L Nat`],
  [`Nat[m]⟶Nat[m]`],
  [The cost of a path, which the cheapest minimises — one order per length `m`.],

  [`gen`],
  [`F(𝟙,moves trans N(union))` \ `zip N(cp P(α))` \ `F(NA,N(E(LA)))` \ `⟶N(E(LA))`],
  [`F(𝟙,moves trans Vec(n)(concat))` \ `zip Vec(n)(cp Vec(3p)(cons))` \ `F(A[n],A[n][p][m])⟶A[n][3p][m+1]`],
  // lean:AOP.A7_4_CylinderVec.Vec.gen@0466b07f
  [The same composite without `α`; the type shown is the `cons` side, the `wrap` side is `𝟙:A[n]⟶A[n]`.],

  [`⦇gen⦈`],
  [`L(N A)⟶N(E(L A))`],
  [`A[m][n]⟶A[n][p][m]`],
  // lean:AOP.A7_4_CylinderVec.Vec.genFold@f1b10c83
  [Columns in, rows out.],

  [`paths≜⦇gen⦈ concat`],
  [`⦇gen⦈ setify union` \ `L N Nat⟶E(L Nat)`],
  [`A[m][n]⟶A[np][m]`],
  // lean:AOP.A7_4_CylinderVec.Vec.paths@83577d2b
  [The `n` rows of `p` paths laid end to end: every path of the cylinder, in one row.],

  [`Q`, @sec-cyl-vec-q],
  [`F(𝟙,moves trans N(est(R)))` \ `zip N(α)`],
  [`F(𝟙,moves trans Vec(n)(est(R)))` \ `zip`, `F(A[n],A[n][m])⟶A[n][m+1]`],
  // lean:AOP.A7_4_CylinderVecRel.Vec.Rel.Q@cf11297a
  [The cheapest of three; no `p` anywhere. `⦇Q⦈:A[m][n]⟶A[n][m]` has the type of a transpose.],

  [the specification \ `paths est(R)`],
  [`L N Nat⟶L Nat`],
  [`A[m][n]⟶A[m]`, `est(R):X[np]⟶X`],
  [A cheapest path from the entry side to the exit side.],
)]<vec-defn-cyl>

=== `gen≜(𝟙×(moves trans Vec(n)(concat))) zip Vec(n)(cp Vec(3p)(cons))` <sec-cyl-vec>

// Beside @sec-cyl-gen: `union` becomes `concat`, `trans` the transpose, and `α` drops out because
// `wrap` and `cons` are identities.  A one-square path is its square, which is what keeps `[1]` out
// of every type; the `[m+1]` bracket under the ports is the hidden `cons`.
#disp[#align(center, lean("Freyd.Alg.Vec.gen"))]<vec-gen-diag>

#disp[#align(center)[```
a row is the outer index, a cell one path
u = ((1,2,3,4),C)                               : A[n]×A[n]
    C = 5                                         one candidate per row, one square long:
        6                                         a column of squares
        7
        8
(𝟙×(moves trans Vec(n)(concat)))                  𝟙 keeps the column, the candidates move
  moves(C)                                        down, unmoved, up: a 3×n matrix
   = 6 7 8 5
     5 6 7 8
     8 5 6 7                                    : A[3][n]
  trans(that)                                     the transpose: row k gets rows k-1, k, k+1
   = 6 5 8
     7 6 5
     8 7 6
     5 8 7                                      : A[n][3]
  Vec(n)(concat)(that) = that                     concat:X[3][1]⟶X[3] is 𝟙
zip(that)                                         each row: its square, and its candidates
   = (1, 6 5 8)
     (2, 7 6 5)
     (3, 8 7 6)
     (4, 5 8 7)                                 : (A×A[3])[n]
Vec(n)(cp)(that)                                  cp pairs the square with each candidate:
   = 1 6   2 7   3 8   4 5                        row k of that is the k-th 3×2 block, left
     1 5   2 6   3 7   4 8                        to right; each line a two-square path
     1 8   2 5   3 6   4 7                      : A[n][3][2]
```]]<vec-step>
   // lean:AOP.A7_4_CylinderVec.Vec.gen_run@47a0e44e

=== `gen` is an `F`-algebra; `⦇gen⦈`: `cons ⦇gen⦈=(𝟙×⦇gen⦈)gen` <sec-cyl-vec-fold>

// The defining equation of @cata-defining at `gen`, both sides drawn: the fold bead is OUTSIDE `F`
// on the left and INSIDE it on the right — that is all the recursion there is.  `cons=𝟙` here, so
// on the left it is the `[m+1]` bracket alone.  Every bead is a function, so the dots are filled.
#disp[#align(center, grid(columns: 3, align: horizon + center, column-gutter: 14pt, row-gutter: 5pt,
  lean("Freyd.Alg.Vec.cons_genFold.lhs"),
  EQ,
  lean("Freyd.Alg.Vec.cons_genFold.rhs"),

  src[the `[m+1]` bracket puts the column back on the matrix, then the fold reads all of it],
  [],
  src[the fold reads the rest under `F`, then one `gen` puts the column in front],
))]<vec-fold-diag>
   // lean:AOP.A7_4_CylinderVec.Vec.cons_genFold@5d95f82a

#disp[#align(center)[```
xs = 1 2 3 4                                    : A[m][n], m=2
     5 6 7 8

⦇gen⦈(xs) = gen((1,2,3,4), ⦇gen⦈(5,6,7,8))
⦇gen⦈(5,6,7,8)                                    one column: each square its own one-square path
   = 5
     6
     7
     8                                          : A[n][1][1]
```]]<vec-fold-step>

#align(center, block(width: 16.5cm, inset: (y: 4pt))[#src[both halves are in @vec-step: the tail
  folds to the column `5 6 7 8`, one path per row and each of them one square long, and `gen` on it
  is that walk.]])

=== `Q≜(𝟙×(moves trans Vec(n)(est(R)))) zip`, `A[n]×A[n][m]⟶A[n][m+1]` <sec-cyl-vec-q>

// `gen` with the choice made: `concat` and `cp` are gone, and `est(R)` takes one of the three
// candidates a row is offered before the new square is put in front of it.  In `Rel` now, so
// `moves` is lax (hollow) where `trans` and `zip` are strict, and `est(R)` claims no naturality.
#disp[#align(center, lean("Freyd.Alg.Vec.Rel.Q"))]<vec-q-diag>
   // lean:AOP.A7_4_CylinderVecRel.Vec.Rel.Q@cf11297a

#disp[#align(center)[```
u = ((1,2,3,4),C)                               : A[n]×A[n][m]
    C = 5                                         one path per row, one square long
        6
        7
        8
(𝟙×(moves trans Vec(n)(est(R))))                  𝟙 keeps the column, the paths move
  moves(C)                                        down, unmoved, up: a 3×n matrix
   = 6 7 8 5
     5 6 7 8
     8 5 6 7                                    : A[3][n][m]
  trans(that)                                     the transpose: row k gets rows k-1, k, k+1
   = 6 5 8
     7 6 5
     8 7 6
     5 8 7                                      : A[n][3][m]
  Vec(n)(est(R))(that)                            the cheapest into each row — chosen BEFORE
   = 5 5 6 5                                    : A[n][m]   the new square is put in front
zip(that)                                         each row: its square, and the one predecessor
   = 1 5                                          that survived; the `[m+1]` bracket is cons
     2 5
     3 6
     4 5                                        : A[n][m+1]
```]]<vec-q-step>

=== `paths est(R)⊒⦇Q⦈ est(R)` <sec-cyl-vec-deriv>

// This section's own box vocabulary.  CIRCUIT: one wire, a box per factor of the composite, a cut
// corner for a relation and a square box for a map.

// The end names are ANCHORED, not centred at a hand-measured x: one of them is `F(A[n],A[n][p][m])`
// and every row would otherwise need its own offset.

// B&dM §7.4, p. 182.  Beside @cyl-laws with `E` gone: `setify` has nothing to forget, `union`
// becomes `concat`, and the two steps that moved the minimum inside the set become one.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.Vec.Rel.cyl_laws") \
    #src[a cheapest of all `np` paths of the cylinder is beaten by the greedy fold's one path per
     row and then a cheapest of those `n`, which costs `O(n×m)`.
 ]],
    // lean:AOP.A7_4_CylinderVecRel.Vec.Rel.cyl_laws@126f6cbc
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.Vec.Rel.cyl_laws_step3.rhs"), [])],
  [#lean("Freyd.Alg.Vec.Rel.cyl_laws_step3.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.Vec.Rel.cyl_laws_step3.lhs"),
    [#src[@vec-defn-cyl at `paths`]])],
  [#lean("Freyd.Alg.Vec.Rel.cyl_laws_step3.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.Vec.Rel.cyl_laws_step2.lhs"),
    [#src[a cheapest of each of the `n` rows, then a cheapest of those; `R` transitive]])],
  [#lean("Freyd.Alg.Vec.Rel.cyl_laws_step2.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.Vec.Rel.cyl_laws_step1.lhs"),
    [#src[@cata-fusion at @vec-cyl-fusion]])],
  [#lean("Freyd.Alg.Vec.Rel.cyl_laws_step1.lhs")],

  Thm[#leanf("Freyd.Alg.Vec.Rel.est_concat"), `R` transitive \
    #src[a cheapest of each of the `j` rows and then a cheapest of those `j` is a cheapest of all
     `jk` entries laid end to end.
 ]],
    // lean:AOP.A7_4_CylinderVecRel.Vec.Rel.est_concat@8fdae89e

  Thm[#leanf("Freyd.Alg.Vec.Rel.Qfold_le_genFold"), `R` reflexive, transitive and monotonic \
    #src[the one path per row the greedy fold keeps is one of the `p` that `⦇gen⦈` generates for
     that row, and a cheapest of them.
 ]],
    // lean:AOP.A7_4_CylinderVecRel.Vec.Rel.Qfold_le_genFold@6553db32
)]<vec-cyl-laws>

// B&dM §7.4, p. 183.  `gen` kills the `[3p]` candidates before the minimum is taken inside the
// column; the right-hand side kills the `[p]` before, and that swap is the whole step.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.Vec.Rel.cyl_fusion") \
    #src[choosing a cheapest of each square's `p` paths before the column is extended is no better
     than extending first and choosing among the `3p`.
 ]],
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.Vec.Rel.cyl_fusion.rhs"), [])],
  [#lean("Freyd.Alg.Vec.Rel.cyl_fusion.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.Vec.Rel.cyl_fusion.lhs"),
    [#src[(7.13), then `zip`, `trans`, `moves` lax natural]])],
  [#lean("Freyd.Alg.Vec.Rel.cyl_fusion.lhs")],

  Thm[(7.13) on `Vec`: #leanf("Freyd.Alg.Vec.Rel.cyl_7_13"), `R` monotonic \
    #src[putting the new square in front of every one of the `p` candidates and then choosing a
     cheapest is beaten by choosing a cheapest first and putting the square in front of that one.
 ]],
    // lean:AOP.A7_4_CylinderVecRel.Vec.Rel.cyl_7_13@8bf677c6
)]<vec-cyl-fusion>

== The security van problem

// B&dM §7.5, p. 184.  `Π`, the universal relation, is this note's `⊤`; the p. 187 printing of the
// greedy result puts `wrap wrap` where p. 185 and the final program both put `nil`.
#disp[#table(
  columns: (8.0cm, 4.7cm, 1fr),
  align: (left + horizon, left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*definition*], [*type*], [*example*]),

 [`R≜length≤length°` #src[]],
  // lean:AOP.A7_5_Van.R_eq@fa26242d
  [`[[A]]⟶[[A]]`],
  [`[[a,b,c]]` to `[[a],[b,c]]`, and not back: `1≤2`.],

  [`ceiling≜` $frac(#[`prefix sum`], ∋)$ `est(≥)`],
  [`[A]⟶Int`],
  [`ceiling[a,b]` is the largest of `0`, `a`, `a+b`.],

  [`floor≜` $frac(#[`prefix sum`], ∋)$ `est(≤)`],
  [`[A]⟶Int`],
  [`floor[a,b]` is the smallest of `0`, `a`, `a+b`, so `[a,b]` carries `ceiling−floor` cash.],

  [`secure` \ the coreflexive on `x` with \ `bmax(ceiling x,ceiling x−floor x)≤N`],
  [`[A]⟶[A]`],
  [`secure` keeps `[a]` exactly when `−N≤a≤N`.],

  [`ok` \ the coreflexive on `(a,xs)` with `xs` non-empty and `[a]⧺head(xs)` secure],
  [`A×[[A]]` \ `⟶A×[[A]]`],
  [`ok` keeps `(a,[[b],[c]])` exactly when `[a,b]` is secure.],

  [`new≜(wrap×𝟙) cons`],
  [`A×[[A]]⟶[[A]]`],
  [`new(a,[[b],[c]])=[[a],[b],[c]]`.],

  [`glue≜(𝟙×cons°) assocl (cons×𝟙) cons`],
  [`A×[[A]]⟶[[A]]`],
  [`glue(a,[[b],[c]])=[[a,b],[c]]`.],

  [`old≜(𝟙×cons°) assocl` \
   `((cons secure)×𝟙) cons`],
  [`A×[[A]]⟶[[A]]`],
  [`old(a,[[b],[c]])=[[a,b],[c]]` when `[a,b]` is secure, and nothing otherwise.],

  [`partition=⦇[nil,new ∪ glue]⦈`],
  [`[A]⟶[[A]]`],
  [`partition[a,b]` gives `[[a],[b]]` and `[[a,b]]`.],

  [`S≜[nil,new ∪ old]`],
  [`1+A×[[A]]⟶[[A]]`],
  [`S(a,[[b],[c]])` gives `[[a],[b],[c]]`, and `[[a,b],[c]]` when `[a,b]` is secure.],

 [`partition list(secure)=⦇S⦈` #src[]],
  // lean:AOP.A7_5_Van.van_spec@79d2f560
  [`[A]⟶[[A]]`],
  [Both take `[a,b]` to `[[a],[b]]` — each `[a]` is secure — and to `[[a,b]]` when `[a,b]` is.],

 [`H≜(head prefix° head°) ∪ (nil° nil)` #src[]],
  // lean:AOP.A7_5_Van.H_eq@b1cf5141
  [`[[A]]⟶[[A]]`],
  [`[[a],[b,c]]` to `[[a,b],[c]]`: `[a]` is a prefix of `[a,b]`.],

 [`R;H≜R∩(R°⇒H)` #src[]],
  // lean:AOP.A7_5_Van.RH_eq@ddc8b9dc
  [`[[A]]⟶[[A]]`],
  [`[[a,b,c]]` to `[[a],[b,c]]` by `|R|`, and `[[a],[b,c]]` to `[[a,b],[c]]` by `R∩H`.],

  [`|R|≜R∩¬R°`],
  [`[[A]]⟶[[A]]`],
  [`[[a,b,c]]` to `[[a],[b,c]]`: `1<2`. The strict part `R` splits into: `R;H=|R| ∪ (R∩H)`.],

  [the specification \ $frac(#[`partition list(secure)`], ∋)$ `est(R)`],
  [`[A]⟶[[A]]`],
  [`[a,b]` gives `[[a,b]]` when `[a,b]` is secure, and `[[a],[b]]` otherwise.],
)]<van-defn>

=== `secure prefix⊑prefix secure` <sec-van-prefix>

// B&dM p.185.  `secure` is "the coreflexive corresponding to this predicate", and the predicate's
// test `⟨ceiling,ceiling−floor⟩bmax` is a MAP, so the coreflexive is the one that slides across it
// into `≤N` — which is the equation below, and the whole of what @van-defn's `bmax` row says.
// `Δ` is the pair lane the fork opens and `bmax` eats; `ceiling` and `floor` are @van-defn's.
#let van-sec-l = lean("Freyd.Alg.RelSet.Van.secure_bmax.lhs")
#let van-sec-r = lean("Freyd.Alg.RelSet.Van.secure_bmax.rhs")

#disp[#capbox(
  row((van-sec-l, [#h(7pt) = #h(7pt)], van-sec-r)),
 [`secure⟨ceiling,ceiling−floor⟩bmax=⟨ceiling,ceiling−floor⟩bmax(≤N)` \
   #src[a stretch passes `secure` before the test exactly where the test's own value passes `≤N`
    after it, which is @van-defn's `bmax(ceiling x,ceiling x−floor x)≤N`]],
)]<van-secure>

// The two panels differ only in the ORDER of the two beads, so they share `prefix`'s height and
// `secure` is the one that moves: above `prefix` on the left, below it on the right.  `prefix` is
// only LAX natural — `prefix_lax_natural`/`prefix_not_strict` in diag/hm-sigs.json — hence `⊑`, not `=`.
#let van-pre-l = lean("Freyd.Alg.RelSet.Van.secure_prefix.lhs")
#let van-pre-r = lean("Freyd.Alg.RelSet.Van.secure_prefix.rhs")

#disp[#capbox(
  row((van-pre-l, [#h(7pt) #SQ #h(7pt)], van-pre-r)),
 [`secure prefix⊑prefix secure` \
   #src[every pair `secure` then `prefix` gives, `prefix` then `secure` gives too — a prefix of a
    secure stretch is itself secure, which is the prefix-closure B&dM p.185 names]],
)]<van-prefix>

=== `partition list(secure)=⦇[nil,new ∪ old]⦈` <sec-van-fusion>

// B&dM p.185.  The three algebras are arrows out of a PRODUCT, so their panels are a stack of
// context wires: `A×−` carries the transaction the algebra is handed, `[A]×−` the segment being
// built, and the two `list` wires the schedule.  `assocl` draws nothing — `×` is flat in both
// calculi, so a re-bracketing is the identity and there is no bead for it.
#disp[#calc-table(
  table.header([*definition*], [*Hinze–Marsden*]),

  [`new≜(wrap×𝟙) cons` \
   #src[`wrap` makes the transaction a segment on its own, and `cons` puts that segment at the
    front of the schedule: the van is called]],
  [#lean("Freyd.Alg.RelSet.Van.new_eq.rhs")],

  [`glue≜(𝟙×cons°) assocl (cons×𝟙) cons` \
   #src[`cons°` splits the schedule into its first segment and the rest, the first `cons` puts the
    transaction at the front of that segment, and the second puts the segment back]],
  [#lean("Freyd.Alg.RelSet.Van.glue_eq.rhs")],

  [`old≜(𝟙×cons°) assocl ((cons secure)×𝟙) cons` \
   #src[`glue` with `secure` on the segment the transaction has just joined: the van stays away
    only where the longer segment still passes]],
  [#lean("Freyd.Alg.RelSet.Van.old_eq.rhs")],
)]<van-algebras>

// One wire in, two out, both sides: the fold is ONE bead where the left panel has the two the
// specification writes, and `secure` is what the fusion has moved inside it.
#let van-fus-l = lean("Freyd.Alg.RelSet.Van.van_spec.lhs")
#let van-fus-r = lean("Freyd.Alg.RelSet.Van.van_spec.rhs")

#disp[#capbox(
  row((van-fus-l, [#h(7pt) = #h(7pt)], van-fus-r)),
 [`partition list(secure)=⦇[nil,new ∪ old]⦈` \
   #src[cutting the transactions every way and then keeping the cuts whose every segment is secure
    is one pass along them that either calls the van or extends the open segment while it stays
    secure]],
)]<van-fusion>

=== `(𝟙×R)new⊑(new ∪ old)R` <sec-van-714>

// B&dM p.186's (7.14).  Its mirror (7.15) — the same with `old` in place of `new` — is FALSE, and
// @van-deriv is where that costs the refinement of `R` to `R;H`.  `R` sits on the two schedule
// wires and `new` on the product context, so the chain is those two beads swapping height.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Van.van_7_14") \
    #src[calling the van for the transaction on a no-longer schedule gets no further than calling
     it on this one and shortening the schedule afterwards]],
     // lean:AOP.A7_5_Van.van_7_14@31454849
  table.header([*step*], [*Hinze–Marsden*]),

  [`(𝟙×R)new` \ #src[the left side of (7.14) — @van-defn]],
  [#lean("Freyd.Alg.RelSet.Van.new_eq_cons.lhs")],

  [#EQ #h(5pt) `(wrap×R)cons` \ #src[`new≜(wrap×𝟙)cons` — @van-algebras — and `(wrap×𝟙)(𝟙×R)=(wrap×R)`]],
  [#lean("Freyd.Alg.RelSet.Van.new_eq_cons.rhs")],

  [#SQ #h(5pt) `new R` \ #src[`cons` is monotonic on `R` — `(𝟙×R)cons⊑cons R`, consing onto a
   no-longer schedule leaves it no longer — and `new⊑new ∪ old`]],
     // lean:AOP.A7_5_Van.cons_mono_R@60ccf227
  [#lean("Freyd.Alg.RelSet.Van.van_7_14_step2.rhs")],
)]<van-714>

=== `H≜(head prefix° head°) ∪ (nil° nil)` <sec-van-h>

// B&dM p.186, the order that refines `R`.  Two branches, two panels: the left opens each schedule's
// first segment with `head`, compares the two with `prefix` and closes both again; the right is the
// coreflexive on the empty schedule, where `nil` dies on the `𝟏` wire and is born again.
#let van-h-l = lean("Freyd.Alg.RelSet.Van.H_eq.rhs", branch: "inl")
#let van-h-r = lean("Freyd.Alg.RelSet.Van.H_eq.rhs", branch: "inr")

#disp[#capbox(
  row((van-h-l, [#h(7pt) ∪ #h(7pt)], van-h-r)),
 [`H≜(head prefix° head°) ∪ (nil° nil)` \
   #src[one schedule's first segment is a prefix of the other's, or both schedules are empty]],
)]<van-h>

=== `(𝟙×(R;H))new⊑(new ∪ old)(R;H)` <sec-van-716>

// B&dM p.187's (7.16), the `new` half of monotonicity on the refined order.  It rests on (7.18):
// both sides open a segment `[a]` of their own, so the two first segments are EQUAL and `H` holds
// whatever the schedules were — which is why the left panel below carries `⊤` and not `H`.
#let van-718-l = lean("Freyd.Alg.RelSet.Van.van_7_18.lhs")

#disp[#capbox(
  row((van-718-l, [#h(7pt) #SQ #h(7pt)], lean("Freyd.Alg.RelSet.Van.van_7_18.rhs"))),
 [`(𝟙×⊤)new⊑new H` \
   #src[whatever schedule the van is called on, the result's first segment is the one transaction
    `[a]`, so any two results of `new` on that transaction stand in `H`]],
)]<van-718>

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Van.van_mono_new") \
    #src[calling the van for the transaction on a `R;H`-better schedule gets no further than calling
     it on this one and bettering the whole schedule afterwards]],
     // lean:AOP.A7_5_Van.van_mono_new@ca4101c9
  table.header([*step*], [*Hinze–Marsden*]),

  [`(𝟙×(R;H))new` \ #src[the left side of (7.16)]],
  [#lean("Freyd.Alg.RelSet.Van.van_mono_new_step1.lhs")],

  [#SQ #h(5pt) `(𝟙×R)new` \ #src[`R;H⊑R` — @van-defn]],
     // lean:AOP.A7_5_Van.RH_le_R@84a882e3
  [#lean("Freyd.Alg.RelSet.Van.van_mono_new_step1.rhs")],

  [#SQ #h(5pt) `new R ∩ new H` \ #src[(7.14) as far as its `new R` line — @van-714 — and (7.18)]],
  [#row((lean("Freyd.Alg.RelSet.Van.van_mono_new_step2.rhs", branch: "inl"), [#h(7pt) ∩ #h(7pt)], lean("Freyd.Alg.RelSet.Van.van_mono_new_step2.rhs", branch: "inr")))],

  [#EQ #h(5pt) `new (R∩H)` \ #src[`new` is a map, and a map distributes over `∩`]],
  [#lean("Freyd.Alg.RelSet.Van.van_mono_new_step3.rhs")],

  [#SQ #h(5pt) `new (R;H)` \ #src[`X∩Y⊑X;Y`, and `new⊑new ∪ old`]],
     // lean:AOP.A7_5_Van.inter_le_RH@a000aeda
  [#lean("Freyd.Alg.RelSet.Van.van_mono_new_step4.rhs")],
)]<van-716>

=== `(𝟙×(R;H))old⊑(new ∪ old)(R;H)` <sec-van-717>

// B&dM p.187–188's (7.17), the `old` half.  `R;H` splits as `|R| ∪ (R∩H)` and the two pieces are
// answered by different branches of the algebra: on the strict part the van is called, on the tie
// `old` fires again.  (7.19)–(7.21) below are the three claims that split rests on.
#let van-719-l = lean("Freyd.Alg.RelSet.Van.van_7_19.lhs")
#let van-720-l = lean("Freyd.Alg.RelSet.Van.van_7_20.lhs")
#let van-721-l = lean("Freyd.Alg.RelSet.Van.van_7_21.lhs")
#let van-721-r = lean("Freyd.Alg.RelSet.Van.van_7_21.rhs")

#disp[#capbox(
  row((van-719-l, [#h(7pt) #SQ #h(7pt)], lean("Freyd.Alg.RelSet.Van.van_7_19.rhs"))),
 [`(𝟙×⊤)old⊑new H` \
   #src[`old` leaves the transaction `[a]` at the front of the first segment, and `[a]` is what
    `new` makes that segment, so the two first segments are `prefix`-related whatever the schedules
    were]],
)]<van-719>

#disp[#capbox(
  row((van-720-l, [#h(7pt) #SQ #h(7pt)], lean("Freyd.Alg.RelSet.Van.van_7_20.rhs"))),
 [`(𝟙×|R|)old⊑new R` \
   #src[`old` keeps the schedule's length, so a strictly shorter one still comes out no longer than
    the one the van's own segment lengthens]],
)]<van-720>

#disp[#capbox(
  row((van-721-l, [#h(7pt) #SQ #h(7pt)], van-721-r)),
 [`(𝟙×(R∩H))old⊑old (R∩H)` \
   #src[on a tie the one first segment is a prefix of the other, so prefix-closure of `secure` —
    @van-prefix — lets `old` fire on this side too, and it keeps both the length and the prefix]],
)]<van-721>

#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Van.van_mono") \
    #src[gluing the transaction onto a better schedule for the rest gets no further than gluing it
     on, or calling the van, and bettering the whole schedule after,
 ]],
     // lean:AOP.A7_5_Van.van_mono@5f456bbf
  table.header([*circuit* — the `old` branch of each union], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Van.van_mono_step1.lhs"),
    [])],
  [#lean("Freyd.Alg.RelSet.Van.van_mono_step1.lhs") \ #src[the `old` operand of `new ∪ old`, in every row]],

  [#vstep(EQ, [#leanc("Freyd.Alg.RelSet.Van.van_mono_step1.rhs")],
    [`(𝟙×|R|)old ∪ (𝟙×(R∩H))old` \ #src[`R;H=|R| ∪ (R∩H)` — @van-defn, `∪` distributes,
 ]])],
     // lean:AOP.A7_5_Van.RH_eq_strict@370b0cab
  [#lean("Freyd.Alg.RelSet.Van.van_mono_step1.rhs", branch: "inl")],

  [#vstep(SQ, [#leanc("Freyd.Alg.RelSet.Van.van_mono_step2.rhs")],
    [`new (R∩H) ∪ old (R∩H)` \ #src[(7.19) and (7.20) on `|R|` — @van-719, @van-720 — and (7.21)
 on `R∩H` — @van-721]])],
     // lean:AOP.A7_5_Van.van_strict_old@80a35936 lean:AOP.A7_5_Van.van_7_21@302aa148
  [#lean("Freyd.Alg.RelSet.Van.van_mono_step2.rhs", branch: "inr")],

  [#vstep(SQ, [#leanc("Freyd.Alg.RelSet.Van.van_mono_step4.rhs")],
    [`(new ∪ old)(R;H)` \ #src[`X∩Y⊑X;Y`, converses]])],
  [#lean("Freyd.Alg.RelSet.Van.van_mono_step3.rhs", branch: "inr")],
)]<van-mono>

=== The derivation <sec-van-deriv>

// B&dM §7.5, pp. 186–188: the specification down to the program.  ONE WIRE, `[A]` to `[[A]]`:
// nothing forks, so a row is a run of boxes and what changes is the box the wire runs through.  A
// fraction is a map (@pow-laws), hence a square box; `est` and the folds that carry one are the
// chain's relations, hence chamfered.

// The same lanes as §13.4.4's panels, at this section's types: `[[A]]` is TWO `list` wires beside
// the `A` one, and the outer `list` is born where the partition is.  A bead whose source and target
// differ by one outermost functor kills just that wire (`est` the `E`); an ALGEBRA rebuilds the type,
// so every strand lands on it and the ones it returns are born there.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Van.van_laws") \
    #src[the fewest secure segments the transactions can be cut into are one pass along them, the
     next transaction glued onto the open segment wherever that segment stays secure and the van
 called where it does not]],
     // lean:AOP.A7_5_Van.van_laws@400440f3
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Van.van_laws_step4.rhs"),
    [#frc([`partition list(secure)`])` est(R)` \ #src[the specification — @van-defn]])],
  [#lean("Freyd.Alg.RelSet.Van.van_laws_step4.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Van.van_laws_step4.lhs"),
    [#frc([`⦇S⦈`])` est(R)` \ #src[`partition list(secure)=⦇S⦈`
 #h(4pt) — @van-defn, @cata-fusion at
     // lean:AOP.A7_5_Van.van_spec@79d2f560
     `secure prefix⊑prefix secure`]])],
  [#lean("Freyd.Alg.RelSet.Van.van_laws_step4.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Van.van_laws_step3.lhs"),
    [#frc([`⦇S⦈`])` est(R;H)` \ #src[`R;H⊑R` — @van-defn; (7.15) `(𝟙×R)old⊑(new ∪ old)R` is FALSE, the
     shorter partition need not stay secure, where (7.14) `(𝟙×R)new⊑(new ∪ old)R` holds,
 ]])],
     // lean:AOP.A7_5_Van.van_7_15_false@1b163187 lean:AOP.A7_5_Van.van_7_14@31454849
  [#lean("Freyd.Alg.RelSet.Van.van_laws_step3.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Van.van_laws_step2.lhs"),
    [`⦇`#frc([`S`])` est(R;H)⦈` \ #src[@greedy-thm72 at `R;H`, its hypothesis `F(R;H)S⊑S(R;H)`
     the `old` half (7.17) — @van-mono — and the `new` half (7.16) — @van-716 — which rests on
 (7.18) `(𝟙×⊤)new⊑new H` — @van-718]])],
     // lean:AOP.A7_5_Van.van_mono_new@ca4101c9
  [#lean("Freyd.Alg.RelSet.Van.van_laws_step2.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Van.van_laws_step1.lhs"),
    [`⦇[nil,(ok→glue,new)]⦈` \ #src[`old⊑new (R;H)°`: `old` returns the shorter result wherever it
 returns one, and `ok` is where it does]])],
     // lean:AOP.A7_5_Van.prog_le_greedy@9203a952
  [#lean("Freyd.Alg.RelSet.Van.van_laws_step1.lhs")],
)]<van-laws>

#pagebreak(weak: true)
