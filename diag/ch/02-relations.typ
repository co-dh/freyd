#import "../note-prelude.typ": *
#show: note-chapter.with(2)
// note-split: chapter 2 — this header is written by scripts/note-split and stripped by scripts/note-join
#import "../shared-laws.typ": *
= Relations

#disp[#definition[
Rel is a poset-enriched category with ($times.o$, °) where $times.o$ is commutative cartisian product, and converse `°⊣°`, and

  #align(center, block(inset: (y: 6pt))[
    #src[C:] `(▷ : A⊗A⟶A,⟜ : 𝕀⟶A)` a commutative monoid with `C°⊣C`.
    We write `C°` as `(◁ : A⟶A⊗A,⊸ : A⟶𝕀)`
  ])
// lean:diag.CB.CartBicat@acc5575a
]]<rel-defn>

#law-rel-monoid

== $forall$ object A, `(A,◁,⊸)⊣(A,▷,⟜)`

#law-rel-adj

The last of these is the only one that makes a picture *bigger*, and it is worth a name: *a wire is
below the cut wire*. In `Rel` it reads `{(a,a)}⊆A×A` — cut a wire and its two ends stop having
to agree, so cutting can only add pairs. It is the one weakening this calculus gives away for free.


#pagebreak(weak: true)
