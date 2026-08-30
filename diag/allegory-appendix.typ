// `#include`d by allegory-axioms.typ, which does not share its scope: the helpers must be re-imported.
#import "note-style.typ": definition, disp
#import "draw.typ": zline, zpair, zsqc, zstep

= Appendix <sec-appendix>

== `P(S) est(R)=(∋S)∩(∈\(SR°))`

// B&dM (7.9), `R` reflexive.  `⊑` is @est-710; `⊒` is the one place in this appendix where a tabulation is
// unavoidable — `y` below is the set the right-hand side only describes.
#disp[#definition[
`(p,q)` tabulates `W≜(∋S)∩(∈\(SR°))`, and #h(4pt) `y≜` $frac(#[`(p∋S)∩(qR)`], ∋)$, a map.
]]<est-79-defn>

#disp[
#zline(
  zsqc(`W`, `P(S) est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[`p°q=W`, `𝟙⊑yy°`],
  zpair(zsqc(`p°y`, `P(S)`), zsqc(`y°q`, `est(R)`)),
)
]<est-79>

#disp[
#zline(
  zsqc(`y°q`, `∋`),
  zstep(op: sym.arrow.l.double, under: true)[`f°·⊣f·`, `·∋⊣`$frac(#box(width: 8pt), ∋)$],
  zsqc(`q`, `(p∋S)∩(qR)`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `f°·⊣f·`],
  // Only the LOWER box of a pair can carry a `name`: on the upper one it lands on the box below it.
  zpair(zsqc(`p°q`, `∋S`), zsqc(`𝟙`, `R`, name: "R reflexive")),
)
#zline(
  zsqc(`∈y°q`, `R°`),
  zstep(op: sym.arrow.l.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, `°`, meet],
  zsqc(`R°q°q`, `R°`, name: "q simple"),
)
]<est-79-est>

#disp[
#zline(
  zsqc(`p°y`, `P(S)`),
  zstep(op: sym.arrow.l.double, under: true)[`Δ⊣∩`, `·T⊣/T`, `°`, `f°·⊣f·`],
  zpair(zsqc(`p°y∋`, `∋S`), zsqc(`p∋`, `y∋S°`)),
)
#zline(
  zsqc(`p°y∋`, `∋S`),
  zstep(op: sym.arrow.l.double, under: true)[`·∋⊣`$frac(#box(width: 8pt), ∋)$, meet],
  zsqc(`p°p∋S`, `∋S`, name: "p simple"),
)
#zline(
  zsqc(`p∋`, `y∋S°`),
  zstep(op: sym.arrow.l.double, under: true)[modular law],
  zsqc(`p∋`, `(p∋)∩(qRS°)`),
  zstep(op: sym.arrow.l.double, under: true)[`𝟙⊑qq°`],
  zsqc(`q°p∋`, `RS°`),
  zstep(op: sym.arrow.l.double, under: true)[`°`, `T·⊣T\`],
  zsqc(`W`, `∈\(SR°)`, name: "W's right half"),
)
]<est-79-pow>

== `P(est(R)) est(R)=P(Dom(est(R))) union est(R)`

// B&dM (7.12), `R` a preorder.  `⊑` puts the domain in for free; `⊒` is @est-79 at `S := est(R)`
// and then the two halves the book leaves as exercises.
#disp[
#zline(
  zsqc(`P(est(R)) est(R)`, none),
  zstep(op: sym.eq, under: true)[`Dom(est(R)) est(R)=est(R)`],
  zsqc(`P(Dom(est(R)) est(R)) est(R)`, none),
)
#zline(
  zstep(op: sym.eq, under: true)[`P` a relator],
  zsqc(`P(Dom(est(R)))P(est(R)) est(R)`, none),
  zstep(op: sym.subset.eq.sq, under: true)[@est-711],
  zsqc(`P(Dom(est(R))) union est(R)`, none),
)
]<est-712>

#disp[
#zline(
  zsqc(`P(Dom(est(R))) union est(R)`, `P(est(R)) est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[@est-79 at `S:=est(R)`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(Dom(est(R))) union est(R)`, `∋est(R)`),
        zsqc(`∈P(Dom(est(R))) union est(R)`, `est(R)R°`)),
)
#zline(
  zsqc(`P(Dom(est(R))) union est(R)`, `∋est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[`P(Dom(est(R)))⊑𝟙`],
  zsqc(`union est(R)`, `∋est(R)`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`T(U∩V)⊑TU∩TV`, `·∋⊣`$frac(#box(width: 8pt), ∋)$, @est-73],
  zsqc(`(∋∋)∩(∈\(∈\R°))`, `∋est(R)`),
  zstep(op: sym.arrow.l.double, under: true)[modular law],
  zsqc(`∋(∋∩(∈(∈\(∈\R°))))`, `∋(∋∩(∈\R°))`, name: "counit of T·⊣T\\"),
)
#zline(
  zsqc(`∈P(Dom(est(R))) union est(R)`, `est(R)R°`),
  zstep(op: sym.arrow.l.double, under: true)[`∈` lax natural],
  zsqc(`Dom(est(R))∈union est(R)`, `est(R)R°`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`Dom(est(R))⊑est(R) est(R)°`],
  zsqc(`est(R) est(R)°∈union est(R)`, `est(R)R°`),
  zstep(op: sym.arrow.l.double, under: true)[`est(R)°⊑∈`, `∈∈union⊑∈`],
  zsqc(`est(R)∈est(R)`, `est(R)R°`, name: "UP of est"),
)
]<est-712-geq>
