// The laws the companion note cites from this note: each display is bound here ONCE and placed
// by both notes — here in its own chapter, there at the start — so every @label resolves in each.
#import "note-prelude.typ": *

#let law-adj-all = [
#disp[#table(
  columns: 9, align: left + horizon, inset: 3pt, stroke: 0.4pt + luma(190),
  table.header([*`F⊣G`*], [*`F`'s type*], [*monad `FG`*], [*`𝟙⊑FG`*], [*`GF⊑𝟙`*], [*`F` preserves `∪`*], [*`G` preserves `∩`*], [*`FGF=F`*], [*`GFG=G`*]),

  [`◁⊣▷`], [`A⟶` \ `A⊗A`], [`◁▷=𝟙`], [`𝟙⊑◁▷`], [`▷◁⊑𝟙`], [`(R ∪ S)◁=` \ `R◁ ∪ S◁`], [`(R∩S)▷=` \ `R▷∩S▷`], [`◁▷◁=◁`], [`▷◁▷=▷`],

  [`⊸⊣⟜`], [`A⟶𝕀`], [`⊸⟜=⊤`], [`𝟙⊑⊸⟜`], [`⟜⊸⊑𝟙`], [`(R ∪ S)⊸=` \ `R⊸ ∪ S⊸`], [`(R∩S)⟜=` \ `R⟜∩S⟜`], [`⊸⟜⊸=⊸`], [`⟜⊸⟜=⟜`],

 [`°⊣°`], [`(A⟶B)⟶` \ `(B⟶A)`], [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]],
  // lean:Freyd.S2_10.recip_recip@cb99fa11
 [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]], [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11 lean:Freyd.S2_10.recip_recip@cb99fa11
 [#leanf("Freyd.Alg.recip_union") #src[]],
    // lean:Freyd.S2_20.recip_union@d1eae8a9
 [#leanf("Freyd.Alg.Allegory.recip_inter") #src[]],
    // lean:Freyd.S2_10.recip_inter@e08c9f2d
 [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]], [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11 lean:Freyd.S2_10.recip_recip@cb99fa11

  [`⟜◁⊣▷⊸`], [`(X⊗A⟶Y)⟶` \ `(X⟶Y⊗A)`], [`𝟙`], [`(⟜◁⊗𝟙)` \ `(𝟙⊗▷⊸)=𝟙`], [`(𝟙⊗⟜◁)` \
    `(▷⊸⊗𝟙)=𝟙`], [`=`], [`=`], [`=`], [`=`],

  // An iso is an adjunction BOTH WAYS, so the bend gets a row in each direction; the pair differs
  // only by swapping columns 4/5, which is what makes the last four columns bare equalities.
  [`▷⊸⊣⟜◁`], [`(X⟶Y⊗A)⟶` \ `(X⊗A⟶Y)`], [`𝟙`], [`(𝟙⊗⟜◁)` \ `(▷⊸⊗𝟙)=𝟙`], [`(⟜◁⊗𝟙)` \
    `(𝟙⊗▷⊸)=𝟙`], [`=`], [`=`], [`=`], [`=`],

 [`Δ⊣∩`], [`(A⟶B)⟶` \ `(A⟶B)²`], [#leanf("Freyd.Alg.Allegory.inter_idem") #src[]],
  // lean:Freyd.S2_10.inter_idem@599acf28
 [#leanf("Freyd.Alg.Allegory.inter_idem") #src[]], [#leanf("Freyd.Alg.inter_lb_left") #src[]],
    // lean:Freyd.S2_10.inter_idem@599acf28 lean:Freyd.S2_10.inter_lb_left@4eca3d20
    [`Δ(R ∪ S)=` \ `ΔR ∪ ΔS`], [`(R∩T)∩(S∩U)=` \ `(R∩S)∩(T∩U)`],
 [#leanf("Freyd.Alg.Allegory.inter_idem") #src[]], [#leanf("Freyd.Alg.Allegory.inter_idem") #src[]],
    // lean:Freyd.S2_10.inter_idem@599acf28 lean:Freyd.S2_10.inter_idem@599acf28

  [`∪⊣Δ`], [`(A⟶B)²⟶` \ `(A⟶B)`], [`(R,S)↦` \ `(R ∪ S,R ∪ S)`],
 [#leanf("Freyd.Alg.le_union_left") #src[]], [#leanf("Freyd.Alg.DistributiveAllegory.union_idem") #src[]],
    // lean:Freyd.S2_20.le_union_left@0a8565e2 lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711
    [`(R ∪ T) ∪ (S ∪ U)=` \ `(R ∪ S) ∪ (T ∪ U)`], [`Δ(R∩S)=` \ `ΔR∩ΔS`],
 [#leanf("Freyd.Alg.DistributiveAllegory.union_idem") #src[]], [#leanf("Freyd.Alg.DistributiveAllegory.union_idem") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711 lean:Freyd.Alg.DistributiveAllegory.union_idem@6e40d711

 [`𝟘⊣!`], [`{*}⟶` \ `(A⟶B)`], [], [], [#leanf("Freyd.Alg.zero_le") #src[]], [], [], [], [],
  // lean:Freyd.S2_20.zero_le@4399de93

  [`·S⊣/S`], [`(A⟶B)⟶` \ `(A⟶C)`], [`S/S`], [`R⊑(RS)/S`], [`(T/S)S⊑T`],
 [#leanf("Freyd.Alg.union_comp_distrib") #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [#leanf("Freyd.Alg.div_inter_eq") #src[]],
    // lean:Freyd.S2_30.div_inter_eq@d75d5861
    [`((RS)/S)S` \ `=RS`], [`((T/S)S)/S` \ `=T/S`],

  [`S·⊣S\`], [`(B⟶C)⟶` \ `(A⟶C)`], [`S\S`], [`R⊑S\(SR)`], [`S(S\T)⊑T`],
 [#leanf("Freyd.Alg.DistributiveAllegory.comp_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [#leanf("Freyd.Alg.leftDiv_inter") #src[]],
    // lean:Freyd.S2_30.leftDiv_inter@ba9dda1e
    [`S(S\(SR))` \ `=SR`], [`S\(S(S\T))` \ `=S\T`],

  [`R∩⊣R⇒`], [`(A⟶B)⟶` \ `(A⟶B)`], [`X↦R⇒(X∩R)`], [`X⊑R⇒(X∩R)`], [`R∩(R⇒Y)⊑Y`],
    [`R∩(X ∪ Y)=` \ `(R∩X) ∪ (R∩Y)`],
 [#leanf("Freyd.Alg.impl_inter") #src[]],
    // lean:AOP.A4_4.impl_inter@d2d55732
    [`R∩(R⇒(X∩R))` \ `=X∩R`], [`R⇒(R∩(R⇒Y))` \ `=R⇒Y`],

  [`𝓓⊣·⊤`], [`(A⟶B)⟶` \ `Cor A`], [`R↦(𝓓R)⊤`], [`R⊑(𝓓R)⊤`], [`𝓓(A⊤)⊑A`], [`𝓓(R ∪ S)=` \ `𝓓R ∪ 𝓓S`], [`(A∩B)⊤=` \ `A⊤∩B⊤`], [`𝓓((𝓓R)⊤)` \ `=𝓓R`], [`(𝓓(A⊤))⊤` \ `=A⊤`],

  [`𝓡⊣⊤·`], [`(A⟶B)⟶` \ `Cor B`], [`R↦⊤(𝓡R)`], [`R⊑⊤(𝓡R)`], [`𝓡(⊤A)⊑A`], [`𝓡(R ∪ S)=` \ `𝓡R ∪ 𝓡S`], [`⊤(A∩B)=` \ `⊤A∩⊤B`], [`𝓡(⊤(𝓡R))` \ `=𝓡R`], [`⊤(𝓡(⊤A))` \ `=⊤A`],

 [`·f⊣·f°`], [`(A⟶B)⟶` \ `(A⟶C)`], [`ff°`], [#leanf("Freyd.Alg.map_entire_le") #src[]], [`f°f⊑𝟙`],
  // lean:Freyd.S2_10.map_entire_le@e6d0fe89
 [#leanf("Freyd.Alg.union_comp_distrib") #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [#leanf("Freyd.Alg.simple_dist_inter_recip") #src[]], [`ff°f=f`], [`f°ff°=f°`],
    // lean:AOP.A4_2.simple_dist_inter_recip@9d565a77

 [`f°·⊣f·`], [`(A⟶C)⟶` \ `(B⟶C)`], [`ff°`], [#leanf("Freyd.Alg.map_entire_le") #src[]], [`f°f⊑𝟙`],
  // lean:Freyd.S2_10.map_entire_le@e6d0fe89
 [#leanf("Freyd.Alg.DistributiveAllegory.comp_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
    [`f(X∩Y)=` \ `fX∩fY`], [`ff°f=f`], [`f°ff°=f°`],

  [`i⊣E`], [`Map↪Rel`], [`E`], [$frac(#[`𝟙`], ∋)$`:A⟶EA`], [`∋:EB⟶B`], [—], [—], [$frac(#[`∋`], ∋)$`=𝟙`], [$frac(#[`R`], ∋)$`∋=R`],

  // The row above at the HOM-SET level, and the table's only bijection that is not an ORDER-iso:
  // `%∋` is not monotone, and monotone would force every hom-poset discrete.
  [`·∋⊣` $frac(#box(width: 8pt), ∋)$], [`Map(A,EB)⟶` \ `(A⟶B)`], [`𝟙`], [$frac(#[`f∋`], ∋)$`=f`], [$frac(#[`R`], ∋)$`∋=R`], [—], [—], [$frac(#[`f∋`], ∋)$`∋` \ `=f∋`], [$frac(#[$frac(#[`R`], ∋)$`∋`], ∋)$ \ `=`$frac(#[`R`], ∋)$],

  [$frac(#box(width: 8pt), ∋)$ `⊣·∋`], [`(A⟶B)⟶` \ `Map(A,EB)`], [`𝟙`], [$frac(#[`R`], ∋)$`∋=R`], [$frac(#[`f∋`], ∋)$`=f`], [—], [—], [$frac(#[$frac(#[`R`], ∋)$`∋`], ∋)$ \ `=`$frac(#[`R`], ∋)$], [$frac(#[`f∋`], ∋)$`∋` \ `=f∋`],
)]<adj-all>
]

#let law-adj-cross = [
// A cross table, not a list: what matters is WHICH PAIRS give a law, and a list of the ones that do
// hides how few they are.  `Δ` is a column and `∪`, `⊥` rows, on ONE side each — the other is all-empty.
#disp[#table(
  columns: 9, align: left + horizon, inset: 3pt, stroke: 0.4pt + luma(190),
  table.header([], [*`·T`*], [*`T·`*], [*`·g`*], [*`g°·`*], [*`T∩`*], [*`°`*], [*`⟜◁`*], [*`Δ`*]),

 [*`·S`*], [#leanf("Freyd.Alg.div_comp_assoc") #src[]],
  // lean:Freyd.S2_30.div_comp_assoc@30a074f3
 [#leanf("Freyd.Alg.leftDiv_div") #src[]],
    // lean:Freyd.S2_30.leftDiv_div@e6e6897c
 [`R/(Sg)=` \ `(Rg°)/S`], [#leanf("Freyd.Alg.map_comp_div") #src[]],
    // lean:AOP.A4_4.map_comp_div@3b1816a2
    [—], [`(Y/S)°=` \ `S°\(Y°)`], [`(RS)^=` \ `R^(S⊗𝟙)`],
 [#leanf("Freyd.Alg.div_inter_eq") #src[]],
    // lean:Freyd.S2_30.div_inter_eq@d75d5861

 [*`S·`*], [#leanf("Freyd.Alg.leftDiv_div") #src[]],
  // lean:Freyd.S2_30.leftDiv_div@e6e6897c
 [#leanf("Freyd.Alg.leftDiv_comp") #src[]],
    // lean:Freyd.S2_30.leftDiv_comp@f40e561a
    [`S\(Rg°)=` \ `(S\R)g°`], [`(g°S)\R=` \ `S\(gR)`], [—],
    [`(S\Y)°=` \ `Y°/S°`], [`((S⊗𝟙)R)^=` \ `SR^`],
 [#leanf("Freyd.Alg.leftDiv_inter") #src[]],
    // lean:Freyd.S2_30.leftDiv_inter@ba9dda1e

 [*`·f`*], [#leanf("Freyd.Alg.div_comp_recip_map") #src[]],
  // lean:AOP.A4_4.div_comp_recip_map@bc41ec1a
    [`T\(Rf°)=` \ `(T\R)f°`],
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.simple_dist_inter_recip") #src[]],
    // lean:AOP.A4_2.simple_dist_inter_recip@9d565a77

 [*`f°·`*], [#leanf("Freyd.Alg.map_comp_div") #src[]],
  // lean:AOP.A4_4.map_comp_div@3b1816a2
    [`(Tf°)\R=` \ `f(T\R)`], [—],
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
    [`f(T₁∩T₂)=` \ `fT₁∩fT₂`],

  [*`R∩`*], [—], [—], [—], [—],
 [#leanf("Freyd.Alg.impl_curry") #src[]],
    // lean:AOP.A4_4.impl_curry@96ec2371
    [`(R⇒Y)°=` \ `R°⇒(Y°)`], [—],
 [#leanf("Freyd.Alg.impl_inter") #src[]],
    // lean:AOP.A4_4.impl_inter@d2d55732

  [*`°`*], [`(Y/T)°=` \ `T°\(Y°)`], [`(T\Y)°=` \ `Y°/T°`],
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.Allegory.recip_comp") #src[]], [`(T⇒Y)°=` \ `T°⇒(Y°)`],
    // lean:Freyd.S2_10.recip_comp@516c2d8a
 [#leanf("Freyd.Alg.Allegory.recip_recip") #src[]],
    // lean:Freyd.S2_10.recip_recip@cb99fa11
    [`(R^)°=` \ `(R°⊗𝟙)(𝟙⊗▷⊸)` \ #src[both bends: the `°` section's display]],
    [`(T₁∩T₂)°=` \ `T₁°∩T₂°`],

  [*`⟜◁`*], [`(RT)^=` \ `R^(T⊗𝟙)`], [`((T⊗𝟙)R)^=` \ `TR^`], [—], [—], [—],
    [`(R^)°=` \ `(R°⊗𝟙)(𝟙⊗▷⊸)` \ #src[both bends: the `°` section's display]], [—], [—],

 [*`∪`*], [#leanf("Freyd.Alg.union_comp_distrib") #src[]],
  // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [#leanf("Freyd.Alg.DistributiveAllegory.comp_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [#leanf("Freyd.Alg.union_comp_distrib") #src[]],
    // lean:Freyd.S2_20.union_comp_distrib@0025430d
 [#leanf("Freyd.Alg.DistributiveAllegory.comp_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.comp_union_distrib@bd91d212
 [#leanf("Freyd.Alg.DistributiveAllegory.inter_union_distrib") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.inter_union_distrib@83bb6087
 [#leanf("Freyd.Alg.recip_union") #src[]], [], [],
    // lean:Freyd.S2_20.recip_union@d1eae8a9

 [*`𝟘`*], [#leanf("Freyd.Alg.DistributiveAllegory.zero_comp") #src[]], [#leanf("Freyd.Alg.DistributiveAllegory.comp_zero") #src[]],
  // lean:Freyd.Alg.DistributiveAllegory.zero_comp@77e0792c lean:Freyd.Alg.DistributiveAllegory.comp_zero@ee8988af
 [#leanf("Freyd.Alg.DistributiveAllegory.zero_comp") #src[]], [#leanf("Freyd.Alg.DistributiveAllegory.comp_zero") #src[]],
    // lean:Freyd.Alg.DistributiveAllegory.zero_comp@77e0792c lean:Freyd.Alg.DistributiveAllegory.comp_zero@ee8988af
 [#leanf("Freyd.Alg.inter_zero") #src[]],
    // lean:Freyd.S2_50.inter_zero@d458c7d7
 [#leanf("Freyd.Alg.recip_zero") #src[]], [], [],
    // lean:Freyd.S2_20.recip_zero@49eaea12
)]<adj-cross>
]

#let law-triple-chains = [
#disp[#block(inset: (y: 6pt))[
  `·f⊣·f°⊣/f°` \
  `f°·⊣f·⊣f\`
  // An adjoint chain names three adjunctions in one line and each link is its own `↔` statement;
  // `diag-export --formula` prints one declaration, so the chain stays hand-typed and cites all four.
  // lean:AOP.A4_2.map_shunt_right@789b4e7c lean:AOP.A4_2.map_shunt_left@9ab4e095 lean:Freyd.S2_30.le_div_iff@bb6a7930 lean:Freyd.S2_30.le_leftDiv_iff@6b879927
]]<triple-chains>
]

#let law-rel-monoid = [
#disp[#grid(columns: (1fr, 1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-n-assoc, s: 60%) #v(-7pt) \ #src[`▷` associative]],
  [#P(p-n-comm, s: 60%) #v(-7pt) \ #src[`▷` commutative]],
  [#P(p-n-unit, s: 60%) #v(-7pt) \ #src[`⟜` is its unit]],
  // `slice(0, 2)`, not `slice(1)`: the exporter draws the relation symbol at the LEFT edge of every
  // step after the first, so dropping the first step would leave a dangling `=` in front.
  [#row(frobb.at(0).steps.slice(0, 2), s: 42%) #v(-7pt) \ #src[Frobenius, one half — the other is
   its `°`]],
  [#P(p-lax-delta, s: 60%) #v(-7pt) \ #src[#leanf("Freyd.Diag.CartBicat.lax_Δ")]],
  [#P(p-lax-bang, s: 60%) #v(-7pt) \ #src[#leanf("Freyd.Diag.CartBicat.lax_!")]],
)]<rel-monoid>
]

#let law-conv-defn = [
#disp[#definition[
`°` is primitive, part of the data the first section lists. It turns both of `R`'s wires round, and
the Frobenius structure DRAWS that — the picture and the formula below are `R°`, not its definition:

#fig({ conv((0, -0.80), $R$) })

#align(center, block(inset: (y: 4pt))[#text(12.5pt)[`R°=(⟜◁⊗𝟙)(𝟙⊗R⊗𝟙)(𝟙⊗▷⊸)`]])

where `⟜◁ : 𝕀⟶a⊗a` opens a pair of wires out of nothing and `▷⊸ : b⊗b⟶𝕀` closes one, so
the input of `R°` is where the output of `R` was.  Taking that formula as the definition would now
be circular: `◁` and `⊸` are `▷°` and `⟜°`.  The laws of `°` are that it is a contravariant
2-functor `° : 𝒞ᵒᵖ⟶𝒞`:

#align(center, block(inset: (y: 5pt))[
 (i) `𝟙°=𝟙` #src[] #h(1cm) (ii) `(RS)°=S°R°`
  // lean:Freyd.S2_10.recip_id@319d8965
 #src[] #h(1cm) (iii) `(R⊗S)°=R°⊗S°`
  // lean:Freyd.S2_10.recip_comp@516c2d8a
 #h(1cm) (iv) `R≤S` implies `R°≤S°` #src[]
  // lean:Freyd.S2_10.recip_mono@d584321d
])
]]<conv-defn>
]

#let law-meet-semidistrib = [
#disp[#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*semi-distributivity, and what supplies it*], [*picture*]),

  [`R (S∩T)⊑RS∩RT` — the lax copy law. #src[Equality exactly when `R` is single valued: the Maps section's
 `F(R∩S)=FR∩FS`. ]], P(p-semidistrib),
   // lean:AOP.A4_1.comp_inter_le@c62bf05a
)]<meet-semidistrib>
]

#let law-dom-laws = [
#disp[#table(
  columns: 1, inset: 9pt, stroke: 0.4pt + luma(190),

  [#leanf("Freyd.Alg.dom")],
 [#leanf("Freyd.Alg.dom_UP") #src[]],
  // lean:AOP.A4_2.dom_UP@9eaee77f
 [#leanf("Freyd.Alg.dom_comp_le") #src[]],
  // lean:Freyd.S2_10.dom_comp_le@a99434dd
 [#leanf("Freyd.Alg.dom_inter") #src[]],
  // lean:Freyd.S2_10.dom_inter@e702a791
  [`R` entire #leanf("Freyd.Alg.Entire")],
  // lean:Freyd.S2_10.Entire@6d4b735b
  [`R` simple #leanf("Freyd.Alg.Simple")],
  // lean:Freyd.S2_10.Simple@ed507d14
  [`R` a map #leanf("Freyd.Alg.Map")],
  // lean:Freyd.S2_10.Map@33a3127d
  [#leanf("Freyd.Alg.entire_comp") \
   #leanf("Freyd.Alg.simple_comp") \
   #leanf("Freyd.Alg.map_comp") #src[]],
   // lean:Freyd.S2_10.entire_comp@2dfbf431 lean:Freyd.S2_10.simple_comp@c3c56ec3
   // lean:Freyd.S2_10.map_comp@841b047c
 [#leanf("Freyd.Alg.entire_of_comp_entire") #src[]],
  // lean:Freyd.S2_10.entire_of_comp_entire@ad998fc1
)]<dom-laws>
]

#let law-dom-slide = [
#disp[#chain((p-dom-comp-le,),
  ([`S⊸⊑⊸`, the lax axiom for `⊸` in the first section \
 — the discard slides back past `S` #src[]
   // lean:Freyd.S2_10.dom_comp_le@a99434dd
   // lean:Freyd.Diag.dom_comp_le@4f75b0f2
],), s: 62%)]<dom-slide>
]

#let law-div-laws = [
// One law per row, and the picture column takes the rest of the 22cm: `le_div_iff` is a `⟺` between
// two containments, four sub-pictures wide (10.9cm before scaling), the widest picture in the note.
#disp[#table(
  columns: (8.6cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),

  [`X⊑R/S⟺XS⊑R` \ #src[`X` is any `x`-to-`y` pairing; one that only pairs `x` with a `y`
   such that `x` admires everyone `y` hates lies inside `R/S`, and `R/S` is the largest such.]],
  P(p-le-div),

  [`X⊑S\R⟺SX⊑R` \ #src[The mirror — divide on the left when `x` comes first.]],
  P(p-le-ldiv),

  [`(R/S)S⊑R` \ #src[There is a `y` such that `x` admires everyone `y` hates, and `p` is one of
   the people `y` hates — then `x` admires `p` too. Strict at `S=∅`: `R/S` is everyone, `(R/S)S=∅`.]],
  P(p-div-cancel),

  [`S (S\R)⊑R` \ #src[The mirror.]],
  P(p-ldiv-cancel),

  [*associate:* `R/(S₁S₂)=(R/S₂)/S₁` \ #src[*A friend's enemy* is two hops: divide by the far end
   first.]],
  P(p-div-assoc),

  [`(S₁S₂)\R=S₂\(S₁\R)` \ #src[The mirror.]],
  P(p-ldiv-assoc),

  [*maps:* `f (R/S)=(fR)/S` \ #src[Rename `x` before or after dividing — the licence to write
   `fR/S`.]],
  P(p-map-div),

  [`R/(fS)=(R/S)f°` \ #src[Rename `y`: a map leaves a denominator as `f°` outside the box.
 ]],
   // lean:AOP.A4_4.div_comp_recip_map@bc41ec1a
  P(p-div-map),

  [`(R/S)(S/W)⊑R/W` \ #src[Someone who admires all of a hate-set that already covers everyone
   `z` works for admires those people too.]],
  P(p-div-comp),

  [`𝟙⊑R/R` \ #src[`R/R` runs admirer to admirer: each admires everyone they admire. Strict: two
   people who each admire only `a` and `b` admire each other's idols too, and still stay two people.]],
  P(p-one-div),

  [`(R/R)(R/R)=R/R` \ #src[`R/R` is the preorder *admires at least as much as*, and a preorder is
   idempotent. Freyd writes `⊑`; with `𝟙⊑R/R` above it is an equality.]],
  P(p-div-self-idem),

  [`(R/R)R=R` \ #src[Reaching `p` through someone whose idols `x` fully admires is reaching `p`
   directly, since `x` admires their own idols.]],
  P(p-div-self),

  [`R/𝟙=R` \ #src[Dividing by `𝟙`: `p`'s set is just `{p}`, so admiring all of it is admiring `p`.]],
  P(p-div-one),

  [`R/(S₁ ∪ S₂)=R/S₁∩R/S₂` \ #src[Admiring a combined hate-set is admiring each set in full.]],
  P(p-div-union),

  [`S\(R/W)=(S\R)/W` \ #src[Which is why `S\R/W` needs no bracket.]],
  P(p-ldiv-div),
)]<div-laws>
]

#let law-pow-laws = [
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
  [#leanf("Freyd.Alg.Λ_is_map'")],  [],
  // lean:Freyd.S2_40.Λ_is_map'@d8366eca

 [#leanf("Freyd.Alg.Λ_eps_eq'")], [#src[reading the chosen set back through `∋` returns the relation.]],
  // lean:Freyd.S2_40.Λ_eps_eq'@a9bc729a

  [#leanf("Freyd.Alg.simple_le_Λ_eps")],
 [A partial choice of sets is inside the total one. #src[]],
  // lean:Freyd.S2_40.simple_le_Λ_eps@a28487fe

  [the *singleton map* is monic: #leanf("Freyd.Alg.singletonMap_monic")
 #src[two points with the same one-person set are the same point.]],
  // lean:Freyd.S2_40.singletonMap_monic@f1b11e36
  [The one-person set.],

  [#leanf("Freyd.Alg.Λ_eps_reflection")],
 [Make the set of a set, then read it back one level down. #src[]],
  // lean:AOP.A4_6.Λ_eps_reflection@2e9ddea3

  [*fusion:* #leanf("Freyd.Alg.Λ_fusion")],
  [Naturality of the unit, #leanf("Freyd.Alg.singletonMap_natural").
 #src[renaming a point and then taking its one-person set is taking the set and renaming inside it.]],
   // lean:AOP.A4_6.Λ_fusion@9d7bda13
   // lean:AOP.A4_6.singletonMap_natural@9214d7f0

  [#leanf("Freyd.Alg.Λ_of_map")],
  [Rename first or take singletons first — the fusion row above at `R=𝟙`.],
  // lean:Freyd.S2_40.Λ_of_map@9ddca812

  [#leanf("Freyd.Alg.symm_div_eq_Λ_comp")],
  [`x` and `y` match when `R` sends `x` and `S` sends `y` to the same set.],
  // lean:Freyd.S2_40.symm_div_eq_Λ_comp@d031e970

  [#leanf("Freyd.Alg.existsImage")], [`E(R): EA⟶EB`, image of a set of A],
  // lean:AOP.A4_6.existsImage@db266886
  [#leanf("Freyd.Alg.Λ_eq_singleton_existsImage")],
 [$frac(#[`𝟙`], ∋)$`: x↦{x}` #src[]],
  // lean:AOP.A4_6.Λ_eq_singleton_existsImage@02b29ea8
  [#leanf("Freyd.Alg.Λ_absorption")],
  [absorption — the monad's composition law, $frac(#[`S`], ∋)$ `⋄` $frac(#[`R`], ∋)$ `=`
 $frac(#[`SR`], ∋)$, §@sec-kleisli #src[]],
   // lean:AOP.A4_6.Λ_absorption@e87bd8f2

  [#leanf("Freyd.Alg.supset")],
  [`xs⊇ys⟺∀a. ys∋a→xs∋a`],
  // lean:Freyd.S2_40.supset@51b103bf
  [#leanf("Freyd.Alg.subset_eq_recip_supset")],
  [`xs⊆ys⟺ys⊇xs`],
  // lean:Freyd.S2_40.subset_eq_recip_supset@9180510e
)]<pow-laws>
]

#let law-adj-E-bend = [
// The factorisation the whole adjunction is about, drawn once.  Middle arrow is `E(R)`, NOT `P(R)`:
// the two agree on maps only (B&dM p. 119), and `𝟙/∋ P(R)` is every nonempty subset of `R(a)`.
#disp[#pair(
  leancd("Freyd.Alg.Λ_comp_eps+Freyd.Alg.Λ_eq_singleton_existsImage"),
  // `𝟙/∋` opens the `i E` pair and `∋` closes it again, so the strand running in and out of a panel is
  // the one functor; the panel beside it draws that same functor as the plain wire the law equates it to.
  grid(columns: 2, column-gutter: 14pt, align: horizon,
    lean("Freyd.Alg.singletonMap_comp_eps"), lean("Freyd.Alg.Λ_eps_reflection")),
  [#leanf("Freyd.Alg.Λ_comp_eps") #h(1.4cm)
   #src[`EA` is the powerset of `A` — standard mathematics, but here `P` is
 already the relator `P(R)`. ]],
   // lean:AOP.A4_6.Λ_comp_eps@76d609ed
   // B&dM write `PA` for the powerset.
  // The two identities are four panels wide, so the pair only clears the 22cm text block scaled down.
  s: 95%,
)]<adj-E-bend>
]

#let law-mem-ldiv = [
#disp[#calc-table(cols: (1fr,), al: (left + top,),
  Thm(cols: 1)[#leanf("Freyd.Alg.mem_leftDiv_eq") \
    #src[`xs` is related to `c` by `∈\Z` exactly when `xs ⊆ Λ(Z°)(c)`, the set of every `a` with `a Z c`]],
     // lean:AOP.A7_1.mem_leftDiv_eq@7e4fcb2b
  lean-chain(
    (none, "Freyd.Alg.mem_leftDiv_eq_step1.lhs", []),
    (EQ, "Freyd.Alg.mem_leftDiv_eq_step1.rhs", src[`Z=∈Λ(Z°)°` — @pow-laws]),
     // lean:AOP.A7_1.mem_leftDiv_eq_step1@9ab326b8
    (EQ, "Freyd.Alg.mem_leftDiv_eq_step2.rhs",
      src[`X\(Yf°)=(X\Y)f°`, `f` a map]),
     // lean:AOP.A7_1.mem_leftDiv_eq_step2@dc661372
  ),
)]<mem-ldiv>
]

// A label the laws above cite that lives in Relation Algebra and is no display — a section — prints
// as this name in the companion, where it is absent; Relation Algebra keeps its own rule.
#let elsewhere = ("sec-kleisli": [`𝒜≅Kleisli(E)` in Relation Algebra])

// `#import`ing this file for ONE binding still runs every OTHER binding's `#leanf`/`#lean` calls —
// a content literal evaluates them as soon as it is built, not when the importer places it — so a
// chapter that places only `law-rel-monoid` still needs `law-adj-all`'s panels drawn.  A listing
// scoped to that one chapter cannot see the ones it never places (unplaced content is invisible to
// `query`), so this file places ALL of them itself under `list-shared=1`; `rootsToList`
// (`DiagExport.lean`) queries it that way alongside the chapter, for exactly this reason.
#if sys.inputs.at("list-shared", default: none) != none [
  // A `@sec-…` cross-reference into the chapter that actually places this law fails to resolve
  // here, where nothing defines that label — irrelevant to a listing, which reads selectors, not
  // rendered prose, so references are dropped rather than resolved.
  #show ref: it => []
  #law-adj-all #law-adj-cross #law-triple-chains #law-rel-monoid #law-conv-defn
  #law-meet-semidistrib #law-dom-laws #law-dom-slide #law-div-laws #law-pow-laws
  #law-adj-E-bend #law-mem-ldiv
]
