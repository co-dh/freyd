#import "../note-prelude.typ": *
#show: note-chapter.with(5)
// note-split: chapter 5 — this header is written by scripts/note-split and stripped by scripts/note-join
= Domain and range

#disp[#definition[
The *domain* `Dom(R)≜𝟙∩RR°` #src[] and the *range* `Ran R≜Dom(R°)`.
// lean:Freyd.S2_10.dom@9e0aed7a
]]<dom-defn>

// THE MEET FIRST, then the stub: the stub alone does not look like `𝟙 ∩ R R°` — one strand carries no
// box and the return leg is gone — so the definition is drawn beside it and the chain shows the collapse.
#disp[#chain((p-dom-cd,),
  // Broken by hand: the hint is this column's width, so an unbroken line of this length stretches
  // the row far past the picture.
  ([`▷` lands the return leg back on the value `◁` handed out, \
   so `R°▷` cuts to `⊸` — Frobenius #src[]
   // lean:Freyd.Diag.dom_cd@55211659
],), s: 62%)]<dom-collapse>

Running `R` and throwing the result away leaves only the fact that `R` could fire, and `Ran R` is the
same picture with the box mirrored. In `Rel` both steps are `{(a,a) : ∃b. a R b}`.

#disp[#table(
  columns: 1, inset: 9pt, stroke: 0.4pt + luma(190),

  [`Dom(R)≜𝟙∩RR°`],
 [`Dom(R)⊑A⟺R⊑AR`, for `A` coreflexive #src[]],
  // lean:AOP.A4_2.dom_UP@9eaee77f
 [`Dom(RS)⊑Dom(R)` #src[]],
  // lean:Freyd.S2_10.dom_comp_le@a99434dd
 [`Dom(R∩S)=𝟙∩SR°` #src[]],
  // lean:Freyd.S2_10.dom_inter@e702a791
  [`R` entire `⟺Dom(R)=𝟙⟺𝟙⊑RR°`],
  [`R` simple `⟺R°R⊑𝟙`],
  [`R` a map `⟺R` entire and simple],
  [`R,S` entire `⟹RS` entire — likewise simple, likewise maps
 #src[,
   // lean:Freyd.S2_10.entire_comp@2dfbf431 lean:Freyd.S2_10.simple_comp@c3c56ec3
 ]],
   // lean:Freyd.S2_10.map_comp@841b047c
 [`RS` entire `⟹R` entire #src[]],
  // lean:Freyd.S2_10.entire_of_comp_entire@ad998fc1
)]<dom-laws>

== Sliding the discard

`Dom(RS)⊑Dom(R)`, and a single glyph for `Dom` would have nothing to slide: with the box and the
discard drawn apart, the law is one dot walking back along the lower strand.

#disp[#chain((p-dom-comp-le,),
  ([`S⊸⊑⊸`, the lax axiom for `⊸` in the first section \
 — the discard slides back past `S` #src[]
   // lean:Freyd.S2_10.dom_comp_le@a99434dd
   // lean:Freyd.Diag.dom_comp_le@4f75b0f2
],), s: 62%)]<dom-slide>

Equality is `S` entire, which is the same picture read as `Dom(R)=𝟙⟺R` entire.

#pagebreak(weak: true)
