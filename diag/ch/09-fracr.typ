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


// The result arc runs over the top from `x` to `y`, its fraction clear of the apex: an arc slung
// underneath would start below `x'` and read as the wrong pair.
#disp[#leang("Freyd.S2_30.Example.A+Freyd.S2_30.Example.H+Freyd.S2_30.Example.AsyqH",
  cols: (
    (type: "Admirer", x: -5.2, ys: (x: 1.8, "x'": -1.8)),
    (type: "Person", x: 0, ys: (a: 2.4, b: 0.8, c: -0.8, d: -2.4), node: "dot"),
    (type: "Hater", x: 5.2, ys: (y: 1.8, "y'": -1.8))),
  rels: (A: (col: INDUCED, s1: 0.42), H: (col: SLACK, s1: 0.42),
    AsyqH: (arc: 1, h: 4.4, ly: 4.4, label: text(10pt)[$frac(A, H)$])),
  emph: "AsyqH",
  notes: (((-6.5, 0), text(10pt, INDUCED)[`A`]), ((6.5, 0), text(10pt, SLACK)[`H`])))]<syq-pic>

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
