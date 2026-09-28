#import "../note-prelude.typ": *
#show: note-chapter.with(5)
// note-split: chapter 5 — this header is written by scripts/note-split and stripped by scripts/note-join
#import "../shared-laws.typ": *
= Domain and range

#disp[#definition[
The *domain* #leanf("Freyd.Alg.dom") #src[] and the *range* #leanf("Freyd.Alg.ran") #src[].
// lean:Freyd.S2_10.dom@9e0aed7a
// lean:Freyd.S2_10.ran@f86cb6e9
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

Running `R` and throwing the result away leaves only the fact that `R` could fire, and `ran(R)` is the
same picture with the box mirrored. In `Rel` both steps are `{(a,a) : ∃b. a R b}`.

#law-dom-laws

== Sliding the discard

`dom(RS)⊑dom(R)`, and a single glyph for `dom` would have nothing to slide: with the box and the
discard drawn apart, the law is one dot walking back along the lower strand.

#law-dom-slide

Equality is `S` entire, which is the same picture read as `dom(R)=𝟙⟺R` entire.

#pagebreak(weak: true)
