#import "../note-prelude.typ": *
#show: note-chapter.with(3)
// note-split: chapter 3 — this header is written by scripts/note-split and stripped by scripts/note-join
#import "../shared-laws.typ": *
= ° : 𝒞ᵒᵖ ⟶ 𝒞 is a 2 functor 

#law-conv-defn

== The slide

The one rule (ii) and (iii) use, and each of them uses it twice. A converse facing a merge on the
lower strand is the box itself, upright, on the upper one:

#disp[#P(p-conv-slide, s: 62%)]<conv-slide>

`R°` is DEFINED as the bending of `(R⊗𝟙)▷⊸`, so the slide claims only that unbending it gives
that back — and unbending undoes bending for every arrow. That is the snake above with a passenger:
the `⟜◁` bends the `a` strand down and the `▷⊸` brings it back up, while the `b` strand rides
through untouched. Nothing else is spent below.


#pagebreak(weak: true)
