#import "../note-prelude.typ": *
#show: note-chapter.with(4)
// note-split: chapter 4 — this header is written by scripts/note-split and stripped by scripts/note-join
= `∩` is a commutative idempotent monoid on every hom-set

#disp[#definition[
The *meet* of `R,S : a⟶b`, the paper's *convolution*, is `R∩S:=◁(R⊗S)▷` — copy the
input, run `R` and `S` on the two copies, merge the results — so what comes out is what both of them
do.

#fig({ meet((0, 0), $R$, $S$) })
#align(center, src[transcribed: a definition has no statement to export])

On every hom-set it is associative, commutative and idempotent
#src[,
// lean:Freyd.S2_10.inter_assoc@958bcd8a lean:Freyd.S2_10.inter_comm@4e93697e
], with unit the maximal arrow
// lean:Freyd.S2_10.inter_idem@599acf28
`⊤=⊸⟜` #src[(the paper's Lemma 4.11)].
]]<meet-defn>

#disp[#grid(columns: (1fr, 1fr), gutter: 6pt, align: center + bottom,
  [#P(p-meet-top, s: 60%) #v(-7pt) \ #src[*unit:* one half of `⊤` per end — the merge's unit law
   absorbs the `⟜`, the copy's counit law the `⊸`]],
  [#P(p-meet-comm, s: 60%) #v(-7pt) \ #src[*commutative:* `σ` crosses `R⊗S` by naturality and is
   absorbed by cocommutativity and commutativity]],
  [#P(p-meet-assoc, s: 44%) #v(-7pt) \ #src[*associative:* coassociativity and associativity; `⊗`
   re-brackets for nothing, being strict here]],
  [#P(p-meet-idem, s: 60%) #v(-7pt) \ #src[*idempotent:* the one that is not bookkeeping — the lax
   copy law is the whole of it, worked in allegory2]],
)]<meet-laws>

So `≤` is the order this monoid induces. `R∩S≤R` comes from the unit, and idempotency turns
anything under both `S` and `T` into something under `S∩T`, since `R=R∩R≤S∩T`.

And one law relating `∩` to composition, which is *not* an equation:

#disp[#table(
  columns: (9.4cm, 1fr),
  align: (left + horizon, center + horizon),
  inset: 8pt, stroke: 0.4pt + luma(190),
  table.header([*semi-distributivity, and what supplies it*], [*picture*]),

  [`R (S∩T)⊑RS∩RT` — the lax copy law. #src[Equality exactly when `R` is single valued: the Maps section's
 `F(R∩S)=FR∩FS`. ]], P(p-semidistrib),
   // lean:AOP.A4_1.comp_inter_le@c62bf05a
)]<meet-semidistrib>

#pagebreak(weak: true)
