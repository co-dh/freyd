#import "../note-prelude.typ": *
#show: note-chapter.with(0)
// note-split: chapter 0 — this header is written by scripts/note-split and stripped by scripts/note-join
#import "../shared-laws.typ": *
#let frobenius-box = thmbox(colors.at(8))("frobenius", "Frobenius").with(numbering: none)
= Laws from Relation Algebra

== Adjunctions
#law-adj-all
== Composing adjunctions
#law-adj-cross
== Adjoint triples
#law-triple-chains
== Frobenius
#frobenius-box[
#law-rel-monoid
#law-rel-adj
]
== `°` is a contravariant 2-functor
#law-conv-defn
== Meet and composition
#law-meet-semidistrib
== Domain and range
#law-dom-laws
== Sliding the discard
#law-dom-slide
== Division
#law-div-laws
== Power allegories
#law-pow-laws
== `i⊣E`: power transpose through singleton
#law-adj-E-bend
== `∈\` as a composite
#law-mem-ldiv
