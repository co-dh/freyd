#import "../note-prelude.typ": *
#show: note-chapter.with(14)
// note-split: chapter 14 — this header is written by scripts/note-split and stripped by scripts/note-join
= Thinning Algorithms <sec-thin>

// ---- §14's own vocabulary.  CIRCUIT: one wire, a box per factor; a reduce whose ALGEBRA a step
// rewrites is MELLIÈS' functorial box, with the algebra's own run inside it.
#let THY = 0.95                                   // the functorial box's half-height, clear of `TH`
#let thpic(lft, rgt, alg, tail, s: 76%) = P(cetz.canvas(length: 0.8cm, {
  d.content((-0.30, 0), text(10pt)[#lft], anchor: "east")
  let x = 0.0
  if alg != none {
    banana(0, THY); boxrun(0.13, 0, alg, h: TH)
    x = 0.26 + boxrun-w(alg); banana(x, THY, right: true)
  }
  boxrun(x, 0, tail, h: TH)
  d.content((x + boxrun-w(tail) + 0.30, 0), text(10pt)[#rgt], anchor: "west")
}), s: s)

// ---- HINZE–MARSDEN.  A WIRE IS A FUNCTOR: `[A]` is the `list` wire beside the `A` wire, at the
// ENDS as much as in the middle, and `E` is born by the unit `𝟙%∋` — a bead with a free upper end.
// A counit may only land on the object wire when nothing is left outside it; where a datatype
// survives (`est(R) : E(LA)⟶LA`) the wire ends on its own lane, since bending in would CROSS it.
// A bead sits on the wire it CHANGES: a functor wire when it only rearranges that functor, the
// object wire when it changes the value.  Lane labels run west, object-wire labels east.
#let THU = 1.90                                   // the set the transpose opens, outside everything
#let THM = 2.65                                   // the datatype under it
#let THN = 3.40                                   // a second one, inside the first
#let THO = 5.40                                   // the object wire
== Thinning

// B&dM §8.1, p. 193.  Between the two extremes of the last section: `𝟙` keeps every partial solution
// and `est(Q) (𝟙%∋)` keeps one, `thin(Q)` keeps a representative collection.
#disp[#definition[
For `Q : A⟶A`, #h(4pt) `thin(Q)≜(∋/∋)∩(∈\(Q°∈)) : EA⟶EA` #h(4pt) #src[(8.1)].

`ys thin(Q) xs⟺xs⊆ys∧(∀a∈ys. ∃b∈xs. b Q a)` #src[the same `°` as @est-defn: `∈X` runs `a⟶ys⟶xs`, member of `ys` first, and `Q°∈` runs `a⟶b⟶xs`, so `(a,b)∈Q°` reads `b Q a`; at `Q≜≤` every `a∈ys` keeps some `b≤a` in `xs`, the end `est(≤)` picks]
// lean:AOP.A8_1.thinRel_pt@f6ff770e
]]<thin-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`X⊑` $frac(#[`S`], ∋)$ `thin(Q)⟺X∋⊑S` and `S°X⊑Q°∈`],
  [everything kept is an `S`-value, and every `S`-value has a `Q`-lower bound among the kept ones],
  [#leanf("Freyd.Alg.thinRel_comp_eps_le")],
  [everything a thinning keeps was in the set],
   // lean:AOP.A8_1.thinRel_comp_eps_le@632f425f
  [#leanf("Freyd.Alg.recip_thinRel_comp_eps_le")],
  [every element of the set has a `Q`-lower bound among the kept ones],
   // lean:AOP.A8_1.recip_thinRel_comp_eps_le@8b2f6525
  [#leanf("Freyd.Alg.thinRel_mono")],
  [the fewer pairs `Q` relates, the fewer subsets count as thinnings],
  [#leanf("Freyd.Alg.id_le_thinRel") \ #leanf("Freyd.Alg.thinRel_trans")],
   // lean:AOP.A8_1.id_le_thinRel@41729458
   // lean:AOP.A8_1.thinRel_trans@6f2b3a18
  [keeping everything is always a legal thinning],
  [#leanf("Freyd.Alg.thinRel_comp_est") #h(4pt) #src[`Q⊑R`, `𝟙⊑Q`, `RR⊑R` — @thin-intro; weaker than the book’s "both preorders": `Q` transitive is never used and `𝟙⊑R` follows]],
  [*thin-introduction*: thinning first cannot lose an `R`-minimum],
   // lean:AOP.A8_1.thinRel_comp_est@e5ad7ecb
  [`thin(Q)⊒est(Q)` $frac(#[`𝟙`], ∋)$ #h(6pt)
 #src[(8.2) — @thin-82]],
   // lean:AOP.A8_1.est_comp_singletonMap_le_thinRel@6a9d3796
  [*thin-elimination*: keeping one element is a thinning, but its domain is the sets `est(Q)` is
   defined on],
  [$frac(#[`S`], ∋)$ `thin(Q)⊒` $frac(#[`S`], ∋)$ `est(R)` $frac(#[`𝟙`], ∋)$ \
   #src[(8.3), `R∩(S°S)⊑Q` — @thin-83]],
  [the usable variant: `R` need only refine `Q` between values `S` gives one argument],
  [#leanf("Freyd.Alg.powerRel_thinRel_comp_bigUnion_le") #h(6pt) #src[(8.4)]],
  [thinning each member set is a thinning of the union],
)]<thin-laws>

=== `X⊑(S%∋) thin(Q)⟺X∋⊑S` and `S°X⊑Q°∈`

// @thin-laws' first row drawn: the `E` lane is born at the singleton and dies at the `∋`, so the
// left panel's `X` lands on it and each condition on the right is one panel.
#disp[
#grid(columns: 5, align: horizon, column-gutter: 4pt,
row((
  lean("Freyd.Alg.le_Λ_comp_thinRel_iff.lhs"),
), s: 96%),
[⟺],
row((
  lean("Freyd.Alg.le_Λ_comp_thinRel_iff.rhs.lhs"),
), s: 96%),
[and],
row((
  lean("Freyd.Alg.le_Λ_comp_thinRel_iff.rhs.rhs"),
), s: 96%),
)
]<thin-up>

#disp[
   // lean:AOP.A4_6.Λ_eps_reflection@2e9ddea3
#grid(columns: 3, align: horizon, column-gutter: 4pt,
  lean("Freyd.Alg.thinRel_comp_eps_le"), [and], lean("Freyd.Alg.recip_thinRel_comp_eps_le"),
)
#src[@thin-up at `X≜thin(Q)`, `S≜∋`: the left side is `thin(Q)⊑thin(Q)`, since `∋%∋=Λ(∋)=𝟙`]
]<thin-up-eps>

=== `est(R)=thin(Q) est(R)` given `Q⊑R`, `𝟙⊑Q`, `RR⊑R`

// B&dM p. 194, thin-introduction, mirrored: the row above read as a calculation.  Circuit and not
// Hinze–Marsden — `est` and `thin` are both meets, which a wire-is-a-functor picture cannot draw.
#grid(columns: (1fr, 1fr), column-gutter: 42pt, align: top,
[#disp[
   // lean:AOP.A8_1.thinRel_comp_est@e5ad7ecb
#calc-table(cols: (1fr,), al: (left + horizon,),
  Thm(cols: 1)[`est(R)⊑thin(Q) est(R)` \
    #src[the `⊑` half: keeping everything is a thinning — `𝟙⊑Q`]],
     // lean:AOP.A8_1.thinRel_comp_est_step1@45085b64

  [#vstep([], leanc("Freyd.Alg.thinRel_comp_est_step1.lhs"),
    [])],

  [#vstep(SQ, leanc("Freyd.Alg.thinRel_comp_est_step1.rhs"),
    [#src[`𝟙⊑thin(Q)` — @thin-laws, `Q` reflexive]])],

)
]<thin-intro>],
[#disp[
#calc-table(cols: (1fr,), al: (left + horizon,),
  Thm(cols: 1)[`thin(Q) est(R)⊑∋` \
    #src[the `⊒` half, first condition of the UP of `est` at `X≜thin(Q) est(R)` — @est-up]],
     // lean:AOP.A8_1.thinRel_comp_est_cond1@edcd4448

  [#vstep([], leanc("Freyd.Alg.thinRel_comp_est_step2.lhs"),
    [])],

  [#vstep(SQ, leanc("Freyd.Alg.thinRel_comp_est_step2.rhs"),
    [#src[`est(R)⊑∋` — @est-laws first row at `X≜est(R)`]])],

  [#vstep(SQ, leanc("Freyd.Alg.thinRel_comp_eps_le.rhs"),
    [#src[`thin(Q)∋⊑∋` — @thin-up at `S≜∋`, `X≜thin(Q)`: `∋%∋=𝟙`, so the left side is `thin(Q)⊑thin(Q)`]])],

)
]<thin-intro-up1>])

#disp[
#calc-table(cols: (1fr,), al: (left + horizon,),
  Thm(cols: 1)[`∈ thin(Q) est(R)⊑R°` \
    #src[the `⊒` half, second condition — `Q⊑R`, `R` transitive]],
     // lean:AOP.A8_1.thinRel_comp_est_cond2@ffc2b689

  [#vstep([], leanc("Freyd.Alg.thinRel_comp_est_step3.lhs"),
    [])],

  [#vstep(SQ, leanc("Freyd.Alg.thinRel_comp_est_step3.rhs"),
    [#src[`∈ thin(Q)⊑Q°∈` — @thin-up at `S≜∋`, `X≜thin(Q)`, second half]])],

  [#vstep(SQ, leanc("Freyd.Alg.thinRel_comp_est_step4.rhs"),
    [#src[`∈ est(R)⊑R°` — @est-laws first row at `X≜est(R)`, second half, conversed]])],

  [#vstep(SQ, leanc("Freyd.Alg.thinRel_comp_est_step5.rhs"),
    [#src[`Q⊑R`, conversed]])],

  [#vstep(SQ, leanc("Freyd.Alg.thinRel_comp_est_step6.rhs"),
    [#src[`R` transitive, conversed]])],
)]<thin-intro-up2>

// B&dM (8.2), p. 194, mirrored.  `thin` is a meet of two divisions, so the law is its two halves:
// the first cancels the singleton against the `∋`, the second is the chain.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.est_comp_singletonMap_le_thinRel") \
    #src[the singleton holding a `Q`-least member of a set is a thinning of that set
     // thin-elimination row: (8.2), p. 194
 #h(4pt) ]],
     // lean:AOP.A8_1.est_comp_singletonMap_le_thinRel@6a9d3796
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep(IMP, leanc("Freyd.Alg.est_comp_singletonMap_cond1.lhs"),
    [#src[the `∋/∋` half of @thin-defn at `X≜est(Q) `#frc([`𝟙`])]])],
     // lean:AOP.A8_1.est_comp_singletonMap_cond1@3c083e37
  [#lean("Freyd.Alg.est_comp_singletonMap_cond1.lhs")],

  [#vstep(SQ, leanc("Freyd.Alg.est_comp_singletonMap_cond1.rhs"),
    [#src[#frc([`𝟙`])`∋=𝟙` — @pow-laws — then `est(Q)⊑∋` — @est-laws]])],
  [#lean("Freyd.Alg.est_comp_singletonMap_cond1.rhs")],

  [#vstep(IMP, leanc("Freyd.Alg.est_comp_singletonMap_cond2_step1.lhs"),
    [#src[the `∈\(Q°∈)` half of @thin-defn, `−⊑Q°∈`]])],
     // lean:AOP.A8_1.est_comp_singletonMap_cond2@0b3ab216
  [#lean("Freyd.Alg.est_comp_singletonMap_cond2_step1.lhs")],

  [#vstep(SQ, leanc("Freyd.Alg.est_comp_singletonMap_cond2_step1.rhs"),
    [#src[`∈ est(Q)⊑Q°` — @est-up at `X≜est(Q)`, conversed]])],
     // lean:AOP.A8_1.est_comp_singletonMap_cond2_step1@dab28250
  [#lean("Freyd.Alg.est_comp_singletonMap_cond2_step1.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.recip_comp_singletonMap_le.rhs"),
    [#src[#frc([`𝟙`])`⊑∈`, since #frc([`𝟙`])`∋=𝟙` with #frc([`𝟙`]) a map — @pow-laws]])],
     // lean:AOP.A8_1.recip_comp_singletonMap_le@a290eae1
  [#lean("Freyd.Alg.recip_comp_singletonMap_le.rhs")],
)]<thin-82>

// B&dM (8.3), p. 194, mirrored.  The first of the two conditions cancels the singleton against `∋`;
// the second is the chain, and the context row is where the side condition enters.
#let eb-LamS = (frc([`S`]), 1.0, false)
#let eb-estc = ([`est(R∩S°S)`], 3.1, true)
#let eb-tau = (frc([`𝟙`]), 1.0, false)
#let eb-pic(tail) = thpic([`A`], [`EA`], none, tail)
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.Λ_comp_est_comp_singletonMap_le_thinRel") \
    #src[given `R∩(S°S)⊑Q`, `Q` a preorder
     // thinning row: (8.3), p. 194
 #h(4pt) ]],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_le_thinRel@bac7360f
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep(IMP, leanc("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1.lhs"),
    [#src[the first of @thin-laws' two conditions at `X≜`#frc([`S`])` est(R) `#frc([`𝟙`])]])],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond1@29aa52d6
  [#lean("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1.lhs")],

  [#vstep(SQ, leanc("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1.rhs"),
    [#src[#frc([`𝟙`])`∋=𝟙` — @pow-laws — then #frc([`S`])` est(R)=S∩(S°\R°)⊑S` — @est-laws]])],
  [#lean("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond1.rhs")],

  [#vstep(IMP, leanc("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_step1.lhs"),
    [#src[the second condition, `−⊑Q°∈`]])],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond2@29665c3e
  [#lean("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_step1.lhs")],

  [#vstep(EQ, eb-pic((So-box, eb-LamS, eb-estc, eb-tau)),
    [#src[#frc([`S`])` est(R)=`#frc([`S`])` est(R∩S°S)` — @est-laws]])],
  // Empty: the wiring is the row above's, with one bead renamed.
  [],

  [#vstep(SQ, leanc("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_step1.rhs"),
    [#src[`S°`#frc([`S`])`⊑∈`, since #frc([`S`])`∋=S` with #frc([`S`]) a map — @pow-laws]])],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond2_step1@4ac3fc82
  [#lean("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_step1.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_step2.rhs"),
    [#src[`∈ est(R∩S°S)⊑(R∩S°S)°` — @est-up at `X≜est(R∩S°S)`, conversed — then `R∩(S°S)⊑Q`]])],
     // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_cond2_step2@48c5c1ff
  [#lean("Freyd.Alg.Λ_comp_est_comp_singletonMap_cond2_step2.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.recip_comp_singletonMap_le.rhs"),
    [#src[#frc([`𝟙`])`⊑∈`, since #frc([`𝟙`])`∋=𝟙` with #frc([`𝟙`]) a map — @pow-laws]])],
     // lean:AOP.A8_1.recip_comp_singletonMap_le@a290eae1
  [#lean("Freyd.Alg.recip_comp_singletonMap_le.rhs")],
)]<thin-83>

// B&dM Theorem 8.1, p. 195, mirrored.  The proof is about the SECOND half of `thin`'s universal
// property: the first half is fusion, and the hylomorphism theorem turns the second into one chain.
// `thin(Q) : EA⟶EA` is fixed by one `Q`, not natural in `A`: an arrow of the object `EA`, so its bead
// touches both wires — the `E` it receives dies at it and the `E` it returns is born there.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.thinning") \
    #src[thinning at every step of the reduce is a thinning of the whole candidate set —
     // thinning-of-reduce row: Theorem 8.1, p. 195
     `S` monotonic on `Q`, `Q` a preorder
 #h(4pt) ]],
     // lean:AOP.A8_1.thinning@0c230c31
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], [],
    [`⦇`#frc([`F(∋)S`])` thin(Q)⦈∋⊑⦇S⦈` #h(10pt) and #h(10pt)
     `⦇S⦈°⦇`#frc([`F(∋)S`])` thin(Q)⦈⊑Q°∈` \
     #src[@thin-laws at `X≜⦇`#frc([`F(∋)S`])` thin(Q)⦈`, `⦇S⦈` for its `S`]])],
  // A conjunction has no shape in either calculus.
  [],

  [#vstep(IMP, leanc("Freyd.Alg.thinning_step1.lhs"),
    [#src[the first by @cata-fusion; @hylo-least at the bound `Q°∈` reduces the second to
      `−⊑Q°∈`]])],
  [#lean("Freyd.Alg.thinning_step1.lhs")],

  [#vstep(SQ, leanc("Freyd.Alg.thinning_step1.rhs"),
    [#src[`S°F(Q°)⊑Q°S°` — @mon-str at `S`, conversed; `F(R)°=F(R°)` — @relator-laws]])],
  [#lean("Freyd.Alg.thinning_step1.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.thinning_step2.rhs"),
    [#src[`S°F(∈)`#frc([`F(∋)S`])`⊑∈`, since #frc([`F(∋)S`])`∋=F(∋)S` with #frc([`F(∋)S`]) a map —
      @pow-laws]])],
  [#lean("Freyd.Alg.thinning_step2.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.thinning_step3.rhs"),
    [#src[`∈ thin(Q)⊑Q°∈`, the `∈\(Q°∈)` half of @thin-defn — @adj-all]])],
  [#lean("Freyd.Alg.thinning_step3.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.thinning_step4.rhs"),
    [#src[`Q°Q°=Q°`, `Q` a preorder]])],
  [#lean("Freyd.Alg.thinning_step4.rhs")],
)]<thin-thm81>

// B&dM Corollary 8.1, p. 195: the thinning theorem read against the optimisation problem itself.
// `⦇−⦈` and not the algebra: its transpose opens an `E` INSIDE the reduce, which no outer panel has.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.thinning_est") \
    #src[the thinning fold refines the optimisation problem itself —
     // thinning-est row: Corollary 8.1
     `S` monotonic on `Q`, `Q⊑R`, both preorders
 #h(4pt) ]],
     // lean:AOP.A8_1.thinning_est@a5f0005d
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.thinning_est_step1.lhs"),
    [])],
  // The reduce CONSUMES `T` and the transpose inside it BIRTHS `E`, so the two wires meet at one bead.
  [#lean("Freyd.Alg.thinning_est_step1.lhs")],

  [#vstep(SQ, leanc("Freyd.Alg.thinning_est_step1.rhs"),
    [#src[@thin-thm81]])],
  [#lean("Freyd.Alg.thinning_est_step1.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.thinning_est_step2.rhs"),
    [#src[`est(R)=thin(Q) est(R)` — @thin-laws, `Q⊑R`]])],
  [#lean("Freyd.Alg.thinning_est_step2.rhs")],
)]<thin-cor>

== Paths in a layered network

// B&dM §8.2, p. 196.  `Q` has to record `head` because `wt (a, head xs)` is unbounded: a dearer path
// with a nearer first vertex can still win.
#disp[#definition[
`F(A,X)=A+A×X`, #h(4pt) `L=list⁺` with initial algebra `α≜[wrap,cons] : F(A,LA)⟶LA`.

`wrapz≜⟨wrap,zero⟩`, #h(4pt) `consw(a,(xs,n))=(cons(a,xs),wt(a,head(xs))+n)`.

`cost≜⦇[wrapz,consw]⦈π₂`, #h(4pt) `⦇[wrapz,consw]⦈=⟨𝟙,cost⟩`, #h(4pt) `R≜cost≤cost°`.

`Q≜R∩(head head°)`, #h(4pt) `S≜F(𝟙,∋)α`, #h(4pt) $frac(#[`F(∋,𝟙)`], ∋)$ `=𝟙+cpl`, #h(4pt)
$frac(#[`F(𝟙,∋)`], ∋)$ `=𝟙+cpr`, #h(4pt) `step≜cpr P(cons) est(R)`.
]]<path-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`F(∋,Q)α⊑F(∋,𝟙)αQ`],
  [`F(∋,𝟙)α` is monotonic on `Q`; on `R` it is not, since the next edge can cost arbitrarily much],
  [`S head⊑[𝟙,π₁]` #h(4pt) #src[`S≜F(𝟙,∋)α`]],
  [`S head` is simple, which gives `R∩(S°S)⊑Q`: between two paths `S` builds from one argument,
   equal cost and equal head already means `Q`],
  // lean:AOP.A8_2.pathAlg_monotonic@fd5852aa lean:AOP.A8_2.pathSplit_comp_headRel_le@c6b78bec lean:AOP.A8_2.pathR_inter_recip_le_pathQ@2e1f5c5d
)]<path-mono>

// B&dM §8.2, p. 198.  The `E` the transpose opens is born OUTSIDE the reduce in the specification
// and INSIDE it from the thinning theorem on; that is what rows 1 and 2 differ by.
#let pb-prog = ([`[P(wrap),cpl P(step)]`], 6.3, true)
#let pb-pic(alg, tail) = thpic([`L(EA)`], [`LA`], alg, tail)
// TWO `E` wires, and that is the content: the one the source carries inside `L` (top port), and the
// one the transpose opens outside it — by the unit `𝟙%∋` above the reduce, or by the reduce itself.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.thinning_paths") \
    // layered-network row: B&dM §8.2, p. 198
    #src[a least-cost path in a layered network, as a fold over the layers]],
     // lean:AOP.A8_2.thinning_paths@bfee1a14
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.thinning_paths_step.rhs"),
    [#src[`=` #frc([`L(∋)`])` est(R)`]])],
  [#lean("Freyd.Alg.thinning_paths_step.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.thinning_paths_step.lhs"),
    // thinAlg-elim row: Corollary 8.1
    [#src[@thin-cor, at `F(∋,𝟙)α` monotonic on `Q` — @path-mono.
 ]])],
      // lean:AOP.A8_2.thinAlg_elim@c87607a7
  [#lean("Freyd.Alg.thinning_paths_step.lhs")],

  [#vstep(RQ, pb-pic((pb-prog,), (est-R-box,)),
    [#src[@path-alg under #box[`⦇ ⦈`] monotonic: the whole chain runs inside the reduce, and the
 `est(R)` behind it never moves. ]])],
      // lean:AOP.A8_2.thinning_paths_alg@b6e2e903
  // No panel: the program's fold is the path instance, and `thinning_paths` states this step over a
  // general `F`, whose algebra is @path-alg's row 5 rather than this row's `[P(wrap),cpl P(step)]`.
  [],
)]<path-laws>

// B&dM §8.2, p. 198, rows 3–8.  Every step rewrites the ALGEBRA, so the chain is stated about the
// algebra alone: no `⦇ ⦈` around it and no `est(R)` behind it.  Its source is the bifunctor at two
// DIFFERENT arguments — one `F` lane over a pair object wire.
#let pa-pic(alg) = thpic([`F(EA,E(LA))`], [`E(LA)`], none, alg)
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.thinning_paths_alg") \
    // algebra row: B&dM §8.2, p. 198
    #src[thinning the algebra of a layered network costs no more than taking the program's two cases]],
     // lean:AOP.A8_2.thinning_paths_alg@b6e2e903
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.thinning_paths_alg.rhs"),
    [#src[the algebra of @path-laws row 2]])],
  [#lean("Freyd.Alg.thinning_paths_alg.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.Λ_comp_eq_Λ_comp_powerRel_bigUnion.rhs"),
    [#src[`F(∋,∋)=F(∋,𝟙)F(𝟙,∋)`; #h(3pt) #frc([`F(∋,𝟙)F(𝟙,∋)α`])`=`#frc([`F(∋,𝟙)`])`
 P(`#frc([`F(𝟙,∋)α`])`) union`. ]])],
      // lean:AOP.A5_5_TypeFunctor.BiRelator.interchange@cc0eb4af
      // lean:AOP.A8_2.Λ_comp_eq_Λ_comp_powerRel_bigUnion@3b58c96c
  [#lean("Freyd.Alg.Λ_comp_eq_Λ_comp_powerRel_bigUnion.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.powerRel_thinRel_comp_bigUnion_le.lhs"),
    [#src[`union thin(Q)⊒P(thin(Q)) union` — @thin-laws.
 ]])],
      // lean:AOP.A8_1.powerRel_thinRel_comp_bigUnion_le@57742f7b
  [#lean("Freyd.Alg.powerRel_thinRel_comp_bigUnion_le.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.Λ_comp_est_comp_singletonMap_le_thinRel.lhs"),
    [#src[#frc([`S`])` thin(Q)⊒`#frc([`S`])` est(R) `#frc([`𝟙`]) #h(4pt) — @thin-laws at
 `S≜F(𝟙,∋)α`, `R∩(S°S)⊑Q` — @path-mono. ]])],
      // lean:AOP.A8_1.Λ_comp_est_comp_singletonMap_le_thinRel@bac7360f
      // lean:AOP.A8_2.pathSplit_eq_Fmap_comp_alphaR@03155579
  [#lean("Freyd.Alg.Λ_comp_est_comp_singletonMap_le_thinRel.lhs")],

  [#vstep(EQ, leanc("Freyd.Alg.thinning_paths_alg.lhs"),
    [#src[`P(`#frc([`𝟙`])`) union=𝟙`. ]])],
      // lean:AOP.A4_6.bigUnion_existsImage_singleton@0d6a3843
  [#lean("Freyd.Alg.thinning_paths_alg.lhs")],

  [#vstep(EQ, leanc("Freyd.Alg.cpMap_comp_powerRel_alphaR_comp_est_eq_junc.rhs"),
    [#src[`α` a map, so #frc([`F(𝟙,∋)α`])`=`#frc([`F(𝟙,∋)`])` P(α)`; #h(3pt)
 #frc([`F(𝟙,∋)`])` P(α) est(R)=[wrap,step]` — @path-defn. ]])],
      // lean:AOP.A4_6.Λ_absorption@e87bd8f2
      // lean:AOP.A8_2.cpMap_comp_powerRel_alphaR_comp_est_eq_junc@8bf8624f
      // lean:AOP.A8_2.pathStep@5253071f
  [#lean("Freyd.Alg.cpMap_comp_powerRel_alphaR_comp_est_eq_junc.rhs")],

  [#vstep(EQ, pa-pic((pb-prog,)),
    [#src[#frc([`F(∋,𝟙)`])` =𝟙+cpl` — @path-defn]])],
      // lean:AOP.A5_6.cpMap_sum_eq_junc@fde8662f
  // No panel: `cpMap_sum_eq_junc` holds for EVERY pair of relators, and the exporter has no
  // naturality verdict for an `F` that is only a variable — it draws a red stub instead.
  [],
)]<path-alg>

// Same reason as the hand-placed breaks in §@sec-opt: `sticky` cannot hold a heading to a BREAKABLE
// figure, so this heading stranded itself at the foot of the page.
#pagebreak(weak: true)
== Implementing thin

// B&dM §8.3, p. 199.  Lemma 8.1 is printed with `R` where its own proof and Theorem 8.2 write `P`;
// it is one connected preorder, spelled `P` here.
#disp[#definition[
`setify : [A]⟶EA`, #h(4pt) `cup : EA×EA⟶EA`, #h(4pt) `cp(F)≜` $frac(#[`F(∋)`], ∋)$, #h(4pt)
`listcp : F(L)⟶LF`, #h(4pt) `sort(P)≜setify° ordered P` #src[]
// lean:AOP.A8_3.sortRel@7cf6d184
for `P` a connected preorder.

`thinlist(Q)` is any `thinlist(Q)⊑subseq` with #h(4pt) `thinlist(Q) setify⊑setify thin(Q)`; #h(4pt)
one is #h(4pt) `⦇[nil,bump Q]⦈`, #h(4pt) `bump Q (a,[])=[a]`, #h(4pt)
`bump Q (a,[b]⧺xs)=(b Q a→[a]⧺xs,a Q b→[b]⧺xs,[a]⧺[b]⧺xs)`.

*Binary thinning* data: #h(4pt) `S=(f₁p₁) ∪ (f₂p₂)` with `p₁`, `p₂` coreflexive; #h(4pt) `Q` a
preorder with `Q⊑R` and both `f₁p₁`, `f₂p₂` monotonic on `Q`; #h(4pt) `P` a connected preorder
with both `f₁`, `f₂` monotonic on `P`; #h(4pt) `gᵢ≜list(fᵢ) filter(pᵢ)`.
]]<thinlist-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`thinlist(Q) xs=[minlist(Q) xs]` \ #src[(8.5), `Q` connected, `xs` non-empty]],
  [what thinning should come to when it can: one element],
  [`sort(P) thinlist(Q)⊑thin(Q) sort(P)` #h(6pt) #src[(8.6) — @thinlist-86]],
  [thinning a sorted list is a thinning of the set — this is what `thinlist(Q)⊑subseq` buys],
  [`sort(P) minlist(Q)⊑est(Q)` #h(6pt) #src[(8.7)]],
  [a minimum of the sorted list is a minimum of the set],
  [`sort(fPf°) list(f)⊑P(f) sort(P)` #h(6pt) #src[(8.8)]],
  [shunt a function through a sort],
  [`sort(P) filter(p)⊑E(p) sort(P)` #h(6pt) #src[(8.9), `p` coreflexive]],
  [filtering a sorted list sorts the restricted set],
  [`(sort(P)×sort(P)) merge(P)⊑cup sort(P)` #h(6pt) #src[(8.10)]],
  [merging two sorted lists sorts their union],
  [`F(sort(P)) listcp⊑cp(F) sort(FP)` \ #src[(8.11), `F` linear]],
  [`listcp` is the list implementation of the cartesian product `cp(F)`],
  // lean:AOP.A8_3.sortRel_comp_thinlist_le@849100a7 lean:AOP.A8_3.sortRel_comp_le@e0ee4e2c lean:AOP.A8_3.sortRel_comp_minlist_le@7295dd0c lean:AOP.A8_3.sortRel_comp_listMap_le@87e1117e lean:AOP.A8_3.sortRel_comp_filter_le@d0b5bf14 lean:AOP.A8_3.prodMap_sortRel_comp_merge_le@4fd30ab5 lean:AOP.A8_3.map_sortRel_comp_listcp_le@1ae9442c
)]<thinlist-laws>

// B&dM (8.6), p. 201, mirrored.  Row 3 is the content: `thinlist(Q)` only drops elements, and a
// subsequence of a `P`-ordered list is `P`-ordered, so the thinning may run before the sort.
// `setify°` is where the set becomes a list, so it is a NODE on the object wire — the `E` bends in,
// the `list` bends out — and the two coreflexive-shaped arrows are beads on the lane each acts on.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.sortRel_comp_thinlist_le") \
    // sortRel row: (8.6), p. 201
    #src[a thinning of the sorted list lists a thinning of the set — `P` a connected
 preorder, `thinlist(Q)⊑subseq`. ]],
     // lean:AOP.A8_3.sortRel_comp_thinlist_le@849100a7
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.sortRel_comp_thinlist_le_step1.lhs"), [])],
  // `sort(P) : EA⟶[A]`, `ordered P`,`thinlist(Q) : [A]⟶[A]` — @thinlist-defn's
  // `sort(P)≜setify° ordered P` at `setify : [A]⟶EA`.
  [#lean("Freyd.Alg.sortRel_comp_thinlist_le_step1.lhs")],

  [#vstep(EQ, leanc("Freyd.Alg.sortRel_comp_thinlist_le_step1.rhs"),
    [#src[`sort(P)≜setify° ordered P` — @thinlist-defn]])],
  [#lean("Freyd.Alg.sortRel_comp_thinlist_le_step1.rhs")],

  [#vstep(SQ, leanc("Freyd.Alg.sortRel_comp_thinlist_le_step2.lhs"),
    [#src[`ordered P thinlist(Q)⊑thinlist(Q) ordered P`, since `thinlist(Q)⊑subseq` — @thinlist-defn —
      and a subsequence of a `P`-ordered list is `P`-ordered]])],
  [#lean("Freyd.Alg.sortRel_comp_thinlist_le_step2.lhs")],

  [#vstep(SQ, leanc("Freyd.Alg.sortRel_comp_thinlist_le_step2.rhs"),
    [#src[@thinlist-defn's `thinlist(Q) setify⊑setify thin(Q)` after `setify°`, at `setify°setify⊑𝟙`
      for `setify` simple — @dom-laws — then `·setify⊣·setify°` — @triple-chains]])],
  [#lean("Freyd.Alg.sortRel_comp_thinlist_le_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.sortRel_comp_thinlist_le_step3.rhs"),
    [#src[`sort(P)≜setify° ordered P` — @thinlist-defn]])],
  [#lean("Freyd.Alg.sortRel_comp_thinlist_le_step3.rhs")],
)]<thinlist-86>

// B&dM Lemma 8.1, p. 202, mirrored.  The chain walks the sort INWARDS, past `filter(p)`, then past
// `list(f)`, then under `F` — each step one of (8.9), (8.8), (8.11).
#let lb-cp = ([`cp(F)`], 1.7, false)
#let lb-Efp = ([`E(fp)`], 1.7, false)
#let lb-Pf = ([`P(f)`], 1.4, false)
#let lb-Ep = ([`E(p)`], 1.4, false)
#let lb-fil = ([`filter(p)`], 2.4, false)
#let lb-lf = ([`list(f)`], 2.0, false)
#let lb-sfPf = ([`sort(fPf°)`], 3.1, true)
#let lb-sFP = ([`sort(FP)`], 2.4, true)
#let lb-Fsort = ([`F(sort(P))`], 2.93, true)
#let lb-pic(tail) = thpic([`F(EA)`], [`[A]`], none, tail)
// `sort(P) : EA⟶[A]` is where one datatype becomes another, and nothing survives outside it, so it
// is a NODE on the object wire — the `E` bends in, the `list` bends out — not a bead on a lane.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.map_sort_comp_listcp_le") \
    #src[one sorted list built from sorted arguments, instead of a set built and then sorted —
     // map_sort row: Lemma 8.1, p. 202
     `f : FA⟶A` monotonic on `P`, `p` coreflexive, `F` linear.
 ]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.map_sort_comp_listcp_le.lhs"), [])],
  [#lean("Freyd.Alg.map_sort_comp_listcp_le.lhs")],

  [#vstep(EQ, lb-pic((lb-cp, lb-Efp, sort-P-box)),
    [#src[#frc([`F(∋)fp`])` =`#frc([`F(∋)`])` E(fp)` — @pow-laws; `cp(F)≜`#frc([`F(∋)`]) —
      @thinlist-defn]])],
  // Empty: rows 2 and 3 redraw row 1 — the two steps only rebracket what the transpose is made of.
  [],

  [#vstep(EQ, lb-pic((lb-cp, lb-Pf, lb-Ep, sort-P-box)),
    [#src[`E(fp)=E(f)E(p)`; #h(3pt) `E(f)=P(f)` for `f` a map —
     @powrel-laws]])],
  [],

  [#vstep(RQ, leanc("Freyd.Alg.map_sort_comp_listcp_le.rhs"),
    [#src[`sort(P) filter(p)⊑E(p) sort(P)` — @thinlist-laws]])],
  // The node has walked up past `p`, which comes out the other side as `filter(p)` on the `list`
  // lane: the same coreflexive, applied to the sorted list instead of to the set.
  // `filter(p) : [A]⟶[A]` — @thinlist-defn's `gᵢ≜list(fᵢ) filter(pᵢ)`.
  [#lean("Freyd.Alg.map_sort_comp_listcp_le.rhs")],

  [#vstep(RQ, lb-pic((lb-cp, lb-sfPf, lb-lf, lb-fil)),
    [#src[`sort(fPf°) list(f)⊑P(f) sort(P)` — @thinlist-laws]])],
  // Empty from here: the node now acts while `F` is still alive, so it cannot reach the object wire
  // without crossing it, and `listcp` below is the `F`/`list` swap — two functor wires, not one.
  [],

  [#vstep(RQ, lb-pic((lb-cp, lb-sFP, lb-lf, lb-fil)),
    [#src[`FP⊑fPf°` — @mon-str at `f` a map; `sort(P)≜setify° ordered P` grows with `P` —
      @thinlist-defn]])],
  [],

  [#vstep(RQ, lb-pic((lb-Fsort, listcp-F-box, lb-lf, lb-fil)),
    [#src[`F(sort(P)) listcp⊑cp(F) sort(FP)` — @thinlist-laws, `F` linear]])],
  [],
)]<thinlist-lem81>

// B&dM Theorem 8.2, p. 203, mirrored.  The candidate SET of the thinning theorem becomes a sorted
// LIST, and that swap — `E` killed by `est(R)`, `list` by `minlist(R)` — is what rows 3 and 4 draw.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.thinningList") \
    #src[a fold on sorted lists of partial solutions, thinned at every step —
     // thinningList row: Theorem 8.2, p. 203
     at @thinlist-defn's binary thinning data.
 ]],
     // lean:AOP.A8_3.thinningList@06fe93ac
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.thinningList_step3.rhs"), [])],
  [#lean("Freyd.Alg.thinningList_step3.rhs")],

  [#vstep(RQ, leanc("Freyd.Alg.thinningList_step3.lhs"),
    [#src[@thin-cor at `f₁p₁` and `f₂p₂` monotonic on `Q` — @thinlist-defn]])],
  [#lean("Freyd.Alg.thinningList_step3.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.thinningList_step2.lhs"),
    [#src[`sort(P) minlist(R)⊑est(R)` — @thinlist-laws at its `Q≜R`]])],
  // `est(R)` has split into the node that sorts and the `minlist(R)` that reads the head back.
  // `minlist(R) : [A]⟶A` — @thinlist-laws' (8.5) `thinlist(Q) xs=[minlist(Q) xs]`.
  [#lean("Freyd.Alg.thinningList_step2.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.thinningList_step1.lhs"),
    [#src[@cata-fusion at @thinlist-fusion]])],
  // The reduce now births `list` where it births `E` above: no set is ever built.
  [#lean("Freyd.Alg.thinningList_step1.lhs")],
)]<thinlist-thm82>

// The fusion condition of the last step above, B&dM p. 203.  Two of its moves are unwritten there:
// the product law that distributes `sort(P)×sort(P)` over the fork, and the fork law that closes it.
#let qb-fork = ([`⟨`#frc([`F(∋)f₁p₁`])`,`#frc([`F(∋)f₂p₂`])`⟩`], 5.6, false)
#let qb-cup = ([`cup`], 1.3, false)
#let qb-sxs = ([`sort(P)×sort(P)`], 4.06, true)
#let qb-merge = ([`merge(P)`], 2.53, true)
#let qb-fork2 = ([`⟨`#frc([`F(∋)f₁p₁`])` sort(P),`#frc([`F(∋)f₂p₂`])` sort(P)⟩`], 9.26, true)
#let qb-pic(tail) = thpic([`F(EA)`], [`[A]`], none, tail)
// The panel `lb-pan` draws, with `S` for `f` and no `p`: same source, same two ports killed.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.sortedAlg_fusion") \
    #src[sorting the candidate set is what turns the thinning algebra into an algebra on lists —
     // sortedAlg-fusion row: B&dM p. 203
     the side condition of @thinlist-thm82's last step.
 ]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.sortedAlg_fusion.lhs"), [])],
  [#lean("Freyd.Alg.sortedAlg_fusion.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.sortedAlg_fusion.rhs"),
    [#src[`sort(P) thinlist(Q)⊑thin(Q) sort(P)` — @thinlist-laws]])],
  // The node has walked up past `thin(Q)`, which comes out below it as `thinlist(Q)` on the `list`
  // lane: that exchange is the whole of (8.6), and the rest of the chain rewrites the algebra.
  [#lean("Freyd.Alg.sortedAlg_fusion.rhs")],

  [#vstep(EQ, qb-pic((qb-fork, qb-cup, sort-P-box, thinlist-Q-box)),
    [`⟨`#frc([`F(∋)f₁p₁`])`,`#frc([`F(∋)f₂p₂`])`⟩ cup sort(P) thinlist(Q)` \
     #src[`S=(f₁p₁) ∪ (f₂p₂)` — @thinlist-defn, then @cup-defn]])],
  // Empty from here: a fork is an operation on hom-sets, and `×` is a bifunctor, so neither is a
  // wiring; the circuit column keeps them as one box, §14's convention for a pair.
  [],

  [#vstep(RQ, qb-pic((qb-fork, qb-sxs, qb-merge, thinlist-Q-box)),
    [`⟨`#frc([`F(∋)f₁p₁`])`,`#frc([`F(∋)f₂p₂`])`⟩(sort(P)×sort(P)) merge(P) thinlist(Q)` \
     #src[`(sort(P)×sort(P)) merge(P)⊑cup sort(P)` — @thinlist-laws]])],
  [],

  [#vstep(EQ, qb-pic((qb-fork2, qb-merge, thinlist-Q-box)),
    [`⟨`#frc([`F(∋)f₁p₁`])` sort(P),`#frc([`F(∋)f₂p₂`])` sort(P)⟩ merge(P) thinlist(Q)` \
     #src[`⟨X,Y⟩(sort(P)×sort(P))=⟨X sort(P),Y sort(P)⟩` — @bdm-prod-laws]])],
  [],

  [#vstep(RQ, qb-pic((lb-Fsort, listcp-F-box, pair-g-box, qb-merge, thinlist-Q-box)),
    [`F(sort(P)) listcp ⟨g₁,g₂⟩ merge(P) thinlist(Q)` \
     #src[@thinlist-lem81 at `f₁`, `p₁` and at `f₂`, `p₂`, then
      `X⟨g₁,g₂⟩⊑⟨Xg₁,Xg₂⟩` — @bdm-prod-laws; `gᵢ≜list(fᵢ) filter(pᵢ)` — @thinlist-defn]])],
  [],
)]<thinlist-fusion>

== The knapsack problem

// B&dM §8.4, p. 205.  The printed base of the final fold is `nil`, without the outer `wrap` that
// §8.5 and §8.6 do print (`wrap wrap wrap`, `start wrap`).
#disp[#definition[
`vol,wt : Item⟶Real`, #h(4pt) `value≜list(vol) sum`, #h(4pt) `weight≜list(wt) sum`
#src[].
// lean:AOP.A5_6_ListCombinators.total_eq@2b26e4d0

`subseq=⦇[nil,cons] ∪ [nil,π₂]⦈` #src[,
// lean:AOP.A8_4_Knapsack.con_eq_junc@f6f12bd6
], #h(4pt) `within w` the coreflexive on `xs` with
// lean:AOP.A8_4_Knapsack.drop_eq_junc@1f5b4c77
`weight xs≤w`, #h(4pt) `0≤w`.

`R≜value≥value°` #src[], #h(4pt)
// lean:AOP.A8_4_Knapsack.R_eq@1c13d35d
`Q≜R∩(weight≤weight°)` #src[], #h(4pt)
// lean:AOP.A8_4_Knapsack.Q_eq@22acbe51
`P≜R` #src[,
// lean:AOP.A8_4_Knapsack.knap_sort_cons@2219de33
].
// lean:AOP.A8_4_Knapsack.knap_sort_drop@ab5c746c

`FA=1+Item×A`, #h(4pt) `listcp=wrap+cpr`, #h(4pt) `g₁≜list([nil,cons]) filter(within w)`
#h(4pt) `=[list(nil),h₁]`, #h(4pt) `g₂≜list([nil,π₂])=[list(nil),h₂]`.

`h₁≜list(cons) filter(within w)`, #h(4pt) `h₂≜list(π₂)`.
]]<knap-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) (cons (within w))⊑cons (within w)R` \ #src[FALSE]],
  [not monotonic on `R`: a selection of greater value need not still fit once one more item goes in],
  [`(𝟙×Q) (cons (within w))⊑cons (within w)Q` \ `(𝟙×Q)π₂⊑π₂Q`
 #src[,
   // lean:AOP.A8_4_Knapsack.knap_mono_cons@978d716e
 ]],
   // lean:AOP.A8_4_Knapsack.knap_mono_drop@b49841b3
  [both halves are monotonic on `Q` once ties in value are broken by weight],
)]<knap-mono>

// B&dM §8.4, p. 206.  The set the transpose opens becomes a LIST at the binary thinning step, and
// that swap — `E` killed by `est(R)`, `list` killed by `minlist(R)` — is what the right column draws.
#let kb-prog = ([`[nil,cpr ⟨h₁,h₂⟩ merge R thinlist(Q)]`], 10.5, true)
#let kb-pic(alg, tail) = thpic([`[Item]`], [`[Item]`], alg, tail)
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Knapsack.knap_laws") \
    // knapsack row: B&dM §8.4, p. 206
    #src[the knapsack problem, as a fold that thins the packings kept at each item]],
     // lean:AOP.A8_4_Knapsack.knap_laws@0f259407
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.rhs"),
    [#frc([`subseq (within w)`])` est(R)`])],
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.lhs"),
    [#frc([`⦇[nil,cons](within w) ∪ [nil,π₂]⦈`])` est(R)` \
 #src[@cata-fusion, weights non-negative. ]])],
     // lean:AOP.A8_4_Knapsack.knap_spec@dc0de67d
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step2.lhs")],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Knapsack.knap_laws_step1.lhs"),
    [`⦇listcp ⟨g₁,g₂⟩ merge R thinlist(Q)⦈ minlist(R)` \
     #src[@thinlist-thm82, at `P≜R`, `F` linear, `Q` from @knap-mono]])],
  // The candidate set is now a candidate LIST: the reduce births `list` where it births `E` above.
  [#lean("Freyd.Alg.RelSet.Knapsack.knap_laws_step1.lhs")],

  [#vstep(EQ, kb-pic((kb-prog,), (minlist-R-box,)),
    [`⦇[nil,cpr ⟨h₁,h₂⟩ merge R thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ=[list(nil),hᵢ]` — @knap-defn; `minlist(R)` is `head`, packings
      coming out in descending value]])],
  [],
)]<knap-laws>

// Stranded at the foot of its page for the same reason as the break above.
#pagebreak(weak: true)
== The paragraph problem

// B&dM §8.5, p. 207.  `P ≜ ⊤` works because `merge ⊤ = cat`, which already brings equal first lines
// together; the book's first choice `head prefix head°` is correct but not needed.
#disp[#definition[
`Line=list⁺ Word`, #h(4pt) `Para=list⁺ Line`, #h(4pt) `FA=Word+Word×A`, #h(4pt)
`listcp=wrap+cpr`.

`new(a,xs)=[[a]]⧺xs`, #h(4pt) `glue(a,xs)=[[a]⧺head(xs)]⧺tail(xs)`, #h(4pt)
`partition≜⦇[wrap wrap,new ∪ glue]⦈ : list⁺ Word⟶Para`.

`width≜⦇[length,(length×𝟙) plus succ]⦈`, #h(4pt) `0≤length a`, #h(4pt) `fits w` the coreflexive on a
line `x` with `width x≤w`, #h(4pt) `ok w` the coreflexive on `[x]⧺xs` with `width x≤w`.

`white w x=w−width x`, #h(4pt) `collect≜list(sqr) sum`, #h(4pt) `waste w≜init list(white w) collect`.

`R≜(waste w)≤(waste w)°` #src[], #h(4pt)
// lean:AOP.A8_5_Paragraph.R_eq@cf0ea074
`Q≜R∩(head head°)` #src[], #h(4pt)
// lean:AOP.A8_5_Paragraph.Q_eq@a6330fbf
`P≜⊤` #src[,
// lean:AOP.A8_5_Paragraph.para_sort_new@30222bce
].
// lean:AOP.A8_5_Paragraph.para_sort_glue@bd4641b6

`g₁≜list([wrap wrap,new])`, #h(4pt) `g₂≜list([wrap wrap,glue]) filter(ok w)`, #h(4pt)
`start≜wrap wrap wrap`, #h(4pt) `h₁≜list(new)`, #h(4pt) `h₂≜list(glue) filter(ok w)`.
]]<para-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) glue⊑glue R` #h(6pt) #src[FALSE]],
  [`glue` is not monotonic on `R`: the waste of a paragraph depends on its whole first line, so no
   greedy algorithm solves this],
  [`(𝟙×Q) new⊑new Q` \ `(𝟙×Q) (glue (ok w))⊑glue (ok w)Q` \ #src[`cons` monotonic on
 `collect≤collect°`. ,
   // lean:AOP.A8_5_Paragraph.para_mono_new@d0ba9ffb
 ]],
   // lean:AOP.A8_5_Paragraph.para_mono_glue@0b67b0eb
  [both halves are monotonic on `Q` once ties in waste are broken by the first line],
  [`merge ⊤=cat`; #h(4pt) `P≜head prefix head°` also serves],
  [`⊤` needs no sorting at all, and `prefix` is a linear order on first lines of paragraphs of one
   input],
)]<para-mono>

// B&dM §8.5, p. 210.  `partition` turns ONE list into two — the paragraph and its lines — so it is a
// bead on the object wire with three list wires at it, and the candidate set is a fourth.
#let ab-split = (frc([`⦇[wrap wrap,new] ∪ ([wrap wrap,glue] (ok w))⦈`]), 10.6, false)
#let ab-prog = ([`[start,cpr ⟨h₁,h₂⟩ cat thinlist(Q)]`], 9.9, true)
#let ab-pic(alg, tail) = thpic([`list⁺ Word`], [`Para`], alg, tail)
// The source is ONE `list⁺`; `partition` births the paragraph's, and the reduce of the last two rows
// births a third — the list of candidate paragraphs `minlist(R)` reads back down.
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Paragraph.para_laws") \
    // paragraph row: B&dM §8.5, p. 210
    #src[a paragraph laid out as a fold that thins the layouts kept at each word]],
     // lean:AOP.A8_5_Paragraph.para_laws@0147808d
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step2.rhs"),
    [#frc([`partition list⁺(fits w)`])` est(R)`])],
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step2.rhs")],

  [#vstep(EQ, leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step2.lhs"),
    [#frc([`⦇[wrap wrap,new ∪ (glue (ok w))]⦈`])` est(R)` \
     #src[@cata-fusion, every word fits on a line by itself.
 ]])],
     // lean:AOP.A8_5_Paragraph.para_alg_fusion@031c245f
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step2.lhs")],

  [#vstep(EQ, ab-pic(none, (ab-split, est-R-box)),
    [#frc([`⦇[wrap wrap,new] ∪ ([wrap wrap,glue] (ok w))⦈`])` est(R)` \
     #src[the algebra as `(f₁p₁) ∪ (f₂p₂)`, `p₁≜𝟙` — @thinlist-defn.
 ]])],
     // lean:AOP.A8_5_Paragraph.para_spec@af6e3f82
  // Empty: the step renames the algebra and the panel above already draws the reduce.
  [],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Paragraph.para_laws_step1.lhs"),
    [`⦇listcp ⟨g₁,g₂⟩ cat thinlist(Q)⦈ minlist(R)` \
     #src[@thinlist-thm82, at `P≜⊤` with `merge ⊤=cat`, `Q` from @para-mono]])],
  [#lean("Freyd.Alg.RelSet.Paragraph.para_laws_step1.lhs")],

  [#vstep(EQ, ab-pic((ab-prog,), (minlist-R-box,)),
    [`⦇[start,cpr ⟨h₁,h₂⟩ cat thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ` along the coproduct — @para-defn]])],
  [],
)]<para-laws>

== Bitonic tours

// B&dM §8.6, p. 212.  `Q` keeps the `head2` conjunct p.215 derives and then drops on the grounds
// that tours of one input share their heads: without it the two `tour-mono` rows are false.
#disp[#definition[
`FA=(City×City)+(City×A)`, the base functor of cons-lists of length at least two; #h(4pt)
`listcp=wrap+cpr`; #h(4pt) `tc : City×City⟶Real`, neither positive nor symmetric.

`start (a,b)=([a,b],[a,b])`, #h(4pt) `dropl (a,([b]⧺xs,ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt)
`dropr (a,(xs,[b]⧺ys))=([a]⧺xs,[a]⧺ys)`, #h(4pt) `tour≜⦇[start,dropl ∪ dropr]⦈`.

`cost (xs,ys)=outcost xs+incost ys`, #h(4pt) `outcost [a₀,…,aₙ]=tc (a₀,a₁)+⋯+tc (aₙ₋₁,aₙ)`,
#h(4pt) `incost [a₀,…,aₙ]=tc (a₁,a₀)+⋯+tc (aₙ,aₙ₋₁)`.

`next≜tail head`, #h(4pt) `next2≜next×next`, #h(4pt) `head2≜head×head`, #h(4pt) `R≜cost≤cost°`
#src[], #h(4pt)
// lean:AOP.A8_6_Tour.R_eq@15ad4adc
`Q≜R∩(next2 next2°)∩(head2 head2°)`, #h(4pt) `P≜⊤` #src[,
// lean:AOP.A8_6_Tour.tour_sort_dropl@3dddee2e
], #h(4pt) `g₁≜list([start,dropl])`, #h(4pt)
// lean:AOP.A8_6_Tour.tour_sort_dropr@12e55048
`g₂≜list([start,dropr])`.
]]<tour-defn>

#disp[#table(
  columns: (1fr, 1fr),
  align: (left + horizon, left + horizon),
  inset: 5pt, stroke: 0.4pt + luma(190),
  table.header([*the law*], [*what it says*]),

  [`(𝟙×R) dropl⊑dropl R` #h(6pt) #src[FALSE] \ `(𝟙×R) dropr⊑dropr R` #h(6pt) #src[FALSE]],
  [neither drop is monotonic on `R`: the two edges it adds and removes depend on `head` and `next`
   of both lists],
  [`(𝟙×Q) dropl⊑dropl Q` \ `(𝟙×Q) dropr⊑dropr Q`
 #src[,
   // lean:AOP.A8_6_Tour.tour_mono_dropl@72fb7ce1
 ]],
   // lean:AOP.A8_6_Tour.tour_mono_dropr@950fdec0
  [both are, once ties in cost are broken by the two second cities — the heads already agree among
   tours of one input],
)]<tour-mono>

// B&dM §8.6, p. 215.  A tour is a PAIR of lists, so `[City]×[City]` is the one unary functor
// `X↦[X]×[X]` — a bifunctor is never a wire, and this one is partially applied before it is drawn.
#let ub-fold = (frc([`⦇[start,dropl ∪ dropr]⦈`]), 5.6, false)
#let ub-prog = ([`[start wrap,cpr ⟨list(dropl),list(dropr)⟩ cat thinlist(Q)]`], 16.1, true)
#let ub-pic(alg, tail) = thpic([`[City]`], [`[City]×[City]`], alg, tail)
#disp[#calc-table(
  Thm[#leanf("Freyd.Alg.RelSet.Tour.tour_laws") \
    // tour row: B&dM §8.6, p. 215
    #src[a least-cost bitonic tour, as a fold that thins the tours kept at each city]],
  // No source/target in the header: each row draws the LAW its Hinze–Marsden column names, in that
  // law's own letters, so the column has no one pair of ports.
  table.header([*circuit*], [*Hinze–Marsden*]),

  [#vstep([], leanc("Freyd.Alg.RelSet.Tour.tour_laws.rhs"), [#frc([`tour`])` est(R)`])],
  [#lean("Freyd.Alg.RelSet.Tour.tour_laws.rhs")],

  [#vstep(EQ, ub-pic(none, (ub-fold, est-R-box)),
    [#frc([`⦇[start,dropl ∪ dropr]⦈`])` est(R)` \ #src[`tour≜⦇[start,dropl ∪ dropr]⦈` — @tour-defn]])],
  // Empty: the step only names the reduce, and the panel above already draws it.
  [],

  [#vstep(RQ, leanc("Freyd.Alg.RelSet.Tour.tour_laws.lhs"),
    [`⦇listcp ⟨g₁,g₂⟩ cat thinlist(Q)⦈ minlist(R)` \
     #src[@thinlist-thm82, at `P≜⊤` with `merge ⊤=cat`, `Q` from @tour-mono]])],
  [#lean("Freyd.Alg.RelSet.Tour.tour_laws.lhs")],

  [#vstep(EQ, ub-pic((ub-prog,), (minlist-R-box,)),
    [`⦇[start wrap,cpr ⟨list(dropl),list(dropr)⟩ cat thinlist(Q)]⦈ minlist(R)` \
     #src[`listcp=wrap+cpr`, `gᵢ=[list(start),list(dropᵢ)]` — @tour-defn; quadratic, two tours
      added per step]])],
  [],
)]<tour-laws>

#pagebreak(weak: true)
