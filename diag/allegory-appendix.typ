// `#include`d by allegory-axioms.typ, which does not share its scope: the helpers must be re-imported.
#import "note-style.typ": definition, disp
#import "draw.typ": zline, zpair, zsqc, zstep

= Appendix <sec-appendix>

== `P(S) min R=(∋S)∩(∈\(SR°))`

// B&dM (7.9), `R` reflexive.  `⊑` is @min-710; `⊒` is the one place in §18 where a tabulation is
// unavoidable — `y` below is the set the right-hand side only describes.
#disp[#definition[
`(p,q)` tabulates `W≜(∋S)∩(∈\(SR°))`, and #h(4pt) `y≜` $frac(#[`(p∋S)∩(qR)`], ∋)$, a map.
]]<min-79-defn>

#disp[
#zline(
  zsqc(`W`, `P(S) min R`),
  zstep(op: sym.arrow.l.double, under: true)[`p°q=W`, `𝟙⊑yy°`],
  zpair(zsqc(`p°y`, `P(S)`), zsqc(`y°q`, `min R`)),
)
]<min-79>

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
]<min-79-min>

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
]<min-79-pow>

== `P(min R) min R=P(Dom (min R)) union min R`

// B&dM (7.12), `R` a preorder.  `⊑` puts the domain in for free; `⊒` is @min-79 at `S := min R`
// and then the two halves the book leaves as exercises.
#disp[
#zline(
  zsqc(`P(min R) min R`, none),
  zstep(op: sym.eq, under: true)[`Dom (min R) min R=min R`],
  zsqc(`P(Dom (min R) min R) min R`, none),
)
#zline(
  zstep(op: sym.eq, under: true)[`P` a relator],
  zsqc(`P(Dom (min R))P(min R) min R`, none),
  zstep(op: sym.subset.eq.sq, under: true)[@min-711],
  zsqc(`P(Dom (min R)) union min R`, none),
)
]<min-712>

#disp[
#zline(
  zsqc(`P(Dom (min R)) union min R`, `P(min R) min R`),
  zstep(op: sym.arrow.l.double, under: true)[@min-79 at `S:=min R`, `Δ⊣∩`, `T·⊣T\`],
  zpair(zsqc(`P(Dom (min R)) union min R`, `∋min R`),
        zsqc(`∈P(Dom (min R)) union min R`, `min RR°`)),
)
#zline(
  zsqc(`P(Dom (min R)) union min R`, `∋min R`),
  zstep(op: sym.arrow.l.double, under: true)[`P(Dom (min R))⊑𝟙`],
  zsqc(`union min R`, `∋min R`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`T(U∩V)⊑TU∩TV`, `·∋⊣`$frac(#box(width: 8pt), ∋)$, @min-73],
  zsqc(`(∋∋)∩(∈\(∈\R°))`, `∋min R`),
  zstep(op: sym.arrow.l.double, under: true)[modular law],
  zsqc(`∋(∋∩(∈(∈\(∈\R°))))`, `∋(∋∩(∈\R°))`, name: "counit of T·⊣T\\"),
)
#zline(
  zsqc(`∈P(Dom (min R)) union min R`, `min RR°`),
  zstep(op: sym.arrow.l.double, under: true)[`∈` lax natural],
  zsqc(`Dom (min R)∈union min R`, `min RR°`),
)
#zline(
  zstep(op: sym.arrow.l.double, under: true)[`Dom (min R)⊑min R (min R)°`],
  zsqc(`min R (min R)°∈union min R`, `min RR°`),
  zstep(op: sym.arrow.l.double, under: true)[`(min R)°⊑∈`, `∈∈union⊑∈`],
  zsqc(`min R∈min R`, `min RR°`, name: "UP of min"),
)
]<min-712-geq>
