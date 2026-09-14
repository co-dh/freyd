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
#disp[#chain((cetz.canvas(length: 0.8cm, {
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
   so `R°▷` cuts to `⊸` — Frobenius]), s: 100%)]<dom-collapse>

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

#disp[#chain((cetz.canvas(length: 0.8cm, {
  let y = 0.85
  wire((0, 0), (0.9, 0)); wiredot((0.9, 0))
  bend((0.9, 0), (1.55, y)); bend((0.9, 0), (1.55, -y))
  wire((1.55, y), (4.6, y))
  wire((1.55, -y), (1.7, -y)); gbox((1.7, -y), [R])
  wire((2.62, -y), (2.85, -y)); gbox((2.85, -y), [S])
  wire((3.77, -y), (4.15, -y)); wiredot((4.15, -y))
  lab(-0.35, 0, black)[$A$]; lab(4.95, y, black)[$A$]
}), domstr(rel: [`⊑`])),
  ("", [`S⊸⊑⊸`, the lax axiom for `⊸` in the first section \
 — the discard slides back past `S` #src[]
   // lean:Freyd.S2_10.dom_comp_le@a99434dd
]), s: 100%)]<dom-slide>

Equality is `S` entire, which is the same picture read as `Dom(R)=𝟙⟺R` entire.

#pagebreak(weak: true)
