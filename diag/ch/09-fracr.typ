#import "../note-prelude.typ": *
#show: note-chapter.with(9)
// note-split: chapter 9 — this header is written by scripts/note-split and stripped by scripts/note-join
= $frac(R, S)$

#disp[#definition[
#leanf("Freyd.Alg.symmDiv") #src[what `R` sends `x` to and nothing else is what `S` sends `y` to.]
In `Rel` `x` and `y` has the same image:
// lean:Freyd.S2_30.symmDiv@7e3fc41a
`∀p. (x R p⟺y S p)`
]]<syq-defn>

// The meet read one factor at a time, in the vocabulary of the section above: `/` supplies ALL, the
// converse of the mirror division supplies ONLY, and the meet is what names this section.
#disp[#block(inset: (top: 2pt), text(10.5pt)[
  `x (A/H) y` — `x` admires everyone `y` hates \
  `x ((H/A)°) y` — `x` admires only people `y` hates \
  `x ((A/H)∩(H/A)°) y` — `x` admires only and all whom `y` hates
])]<syq-gloss>

`x` admires exactly whom `y` hates: `/` is *all of*, $frac(R, S)$ is *only all of*.


#disp[#box(cetz.canvas(length: 0.8cm, {
  // `A`: who each `x` admires.  `H`: who each `y` hates.  `x` and `y` name the same three.
  for p in ("a", "b", "c") { syqedge(ADMIRERS.x1, PEOPLE.at(p), INDUCED, 1.1) }
  for p in ("a", "b") { syqedge(ADMIRERS.x2, PEOPLE.at(p), INDUCED.lighten(60%), 0.7) }
  for p in ("a", "b", "c") { syqedge(HATERS.y1, PEOPLE.at(p), SLACK, 1.1) }
  for p in ("a", "b", "d") { syqedge(HATERS.y2, PEOPLE.at(p), SLACK.lighten(60%), 0.7) }

  // The shared column, filled: exactly the people both sides of the matched pair reach.
  // `d` stays hollow — `y'` reaches it and no admirer does.
  for p in ("a", "b", "c") { d.circle(PEOPLE.at(p), radius: 0.17, fill: GIVEN2, stroke: GIVEN2) }
  d.circle(PEOPLE.d, radius: 0.17, fill: white, stroke: 0.9pt + black)
  // Named as in the division picture, and above the dot: beside it the name would land on a fan.
  for (p, q) in PEOPLE { d.content((q.at(0), q.at(1) + 0.62), raw(p)) }

  // The result: the one pair whose two sets agree.  It runs over the top from `x` to `y` — an
  // arc slung underneath would start below `x'` and read as the wrong pair.
  d.bezier((ADMIRERS.x1.at(0), 2.35), (HATERS.y1.at(0), 2.35), (-2.6, 4.4), (2.6, 4.4),
    mark: (end: ">", scale: 0.6), stroke: 1pt + GIVEN2)
  // Clear of the curve's apex (y ≈ 3.9), because the fraction is two lines tall and its bar sitting
  // on the arc would read as part of it.
  d.content((0, 4.4), box(inset: 3pt, fill: white)[#text(10pt, GIVEN2)[$frac(A, H)$]])

  syqnode(ADMIRERS.x1, GIVEN2, rgb("#f2e9f8"), `x`, ring: 0.7pt + GIVEN2)
  syqnode(ADMIRERS.x2, black, white, `x'`)
  syqnode(HATERS.y1, GIVEN2, rgb("#f2e9f8"), `y`, ring: 0.7pt + GIVEN2)
  syqnode(HATERS.y2, black, white, `y'`)
  // The family names sit outside the columns at mid-height: the top belongs to the arc, and beside
  // an arrow they would land on another arrow.
  d.content((-6.5, 0), text(10pt, INDUCED)[`A`]); d.content((6.5, 0), text(10pt, SLACK)[`H`])
}))]<syq-pic>

#disp[#table(
  columns: (7.4cm, 1fr),
  align: (left + horizon, left + horizon),
  inset: 9pt, stroke: 0.4pt + luma(190),
  table.header([*law*], [*the reading*]),

 [#leanf("Freyd.Alg.le_symmDiv_iff") #src[`X` sits inside the matching exactly when it carries `S` back
   inside `R` and, reversed, carries `R` back inside `S`.]],
  // lean:Freyd.S2_30.le_symmDiv_iff@b1cfe4dc
  [`X` may pair `x` with `y` only when `x` admires exactly whom `y` hates. Both halves must typecheck,
   so the operation is *partial*.],

 [#leanf("Freyd.Alg.symmDiv_recip") #src[reversing the matching swaps the two relations.]],
  // lean:Freyd.S2_30.symmDiv_recip@b93b9076
  [Matching is symmetric.],

 [#leanf("Freyd.Alg.symmDiv_comp") #src[a match from `R` to `S` followed by one from `S` to `W` is a
   match from `R` to `W`.]],
  // lean:Freyd.S2_30.symmDiv_comp@5930c455
  [And transitive.],

  [#leanf("Freyd.Alg.symmDiv_comp_le") #src[following the matching by `S` lands inside `R`.]],
  // lean:Freyd.S2_30.symmDiv_comp_le@82f653bd
  [$(∃ y. thin x (frac(R, S)) y ∧ y S p) → x R p$ \
   `x only admires whom y hates` \
   $frac(R, S) S = "Dom"(frac(R, S)) R$],

 [#leanf("Freyd.Alg.symmDiv_self_comp") #src[matching `R` against itself and then following `R` gives
   `R` back.]],
  // lean:Freyd.S2_30.symmDiv_self_comp@2b447963
  [$(∃ y. thin x (frac(R, R)) y ∧ y R p) ⟺ x R p$ \
   `x and y admire the same people` \
   `y=x always qualifies (𝟙⊑R%R below)`],

 [#leanf("Freyd.Alg.symmDiv_self_reflexive") #src[every `x` matches itself.]],
  // lean:Freyd.S2_30.symmDiv_self_reflexive@9e2af20e
  [$x (frac(R, R)) y$ if `x` and `y` admires the same peoples.],

  [#leanf("Freyd.Alg.symmDiv_self_idem") #src[matching twice matches no more pairs than matching once.]],
  // lean:Freyd.S2_30.symmDiv_self_idem@8b70dcc5
  [So the relation *admires the same people* is an equivalence relation.],

  [#leanf("Freyd.Alg.symmetric_le_symmDiv_self_iff")
 #src[a symmetric `X` sits inside the matching exactly when following it by `R` adds nothing to `R`.]],
   // lean:Freyd.S2_11.symmetric_le_symmDiv_self_iff@a5fc04b4
  [The largest symmetric arrow that leaves `R` alone.],

 [#leanf("Freyd.Alg.simplePart") #src[matching `R` against the identity keeps the `x` whose image is a
   single point.]],
  // lean:Freyd.S2_30.simplePart@3779ee66
  [The people who admire exactly one person and nobody else. It equals `R` only when `R` is simple, unlike
   `R/𝟙=R`.],

 [#leanf("Freyd.Alg.dom_symmDiv") #src[the `x` that match something are those the two one-sided
   divisions take round the loop back to `x`.]],
  // lean:Freyd.S2_30.dom_symmDiv@0ef1aa31
  [Its domain is the *domain of simplicity* of `R`.],
)]<syq-readings>

#pagebreak(weak: true)
