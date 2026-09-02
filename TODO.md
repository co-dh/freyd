[X] 13.3.5b didn't proved step by step, so is 13.3.5c
[X] remove the formuls in 13.3.5e row 2, 3, 4, 5.
[X] 13.3.4g row 2 , 1 over e.
[X] 12.1d no l, r. no desc in header. remove B&M $5.6. P.124, add type to 12.1e. it shuld be generated.
[X] make 13.2.3a diagram a 20% taller.
[X] 13.3.1c natural langauge. remove formulas. remove circuit
[X] 14.1d, thin Q on E line? is that correct?
[X] add space around ∪ everywhere in formulas and labels, `cons ∪ π₂` not `cons∪π₂` (12.1d and every other display, generator spelling included)
[X] circuit wire types print E[A], not E([A]); applies to every type label in every circuit diagram
[X] 12.1d rows 4–5 circuits are still hand-drawn (sbB4, sbB5); generate them with the fork kind
[X] 12.1d row 4 HM panel shows a horizontal bar; check it is generated and the bar goes with the straight-wire default
[X] scanline check on in make p; if slow, full scan once, then only the changed diagrams
[X] TODO.md: mark finished items with [X]
[X] six HM panels stay hand-drawn and uncertified because `scripts/scanline`'s `BRANCH` table names only
    cons/nil/plus/zero, so a case split on [base,step]°, [wrap,cat]°, [nil,extend]°, [nil,expand]°, β° or
    [arb,step]° cannot be cut; a sum of arrows (𝟙+(X×𝟙)) has no bead either.  Register the algebra's own
    branch names, or a general fallback, so all six generate and certify.
[ ] all $14, $15, $16 HM diagram has function on functor line. regenerate them. no need for me to review for now. generate their circuit diagram too, no review from me.
[X] check claude session usage daily, find token usage and time usage, find opportunity to optimize. summarize as rule for review
[ ] scripts/circuit refuses `°` on a bracket, so five §14–16 circuit cells stay hand-drawn (`[wrap,cat]°`,
    `[nil,extend]°`, `[nil,expand]°`, `[nil,snag]°`, `[arb,step]°`): a bracket is a `case`, `conv` wants a
    box, and `tape` reads the coproduct off `polys` at the SOURCE, which the conv swap hands only the
    target.  Under `%∋` the node is discarded, so TYPING alone blocks; the mct and entab cells also carry a
    bracket INSIDE `P(…)`, which `typed` really does walk, so those two need `polys` rows as well.
    Needs `conv` under `%∋` to return types without a box, plus a per-panel `polys` override — `polys.F`'s
    `A×x` has the wrong product order for snoc-lists (note :9541) — the same override the greedy `F`/`Fᵢ`
    row mismatch wants.
[ ] the note's HM certs at diag/allegory-axioms.typ :8755 :8790 :9247 write E(F(X)h), E(Fᵢ(X)Uᵢ), E((X×𝟙)snoc)
    where B&dM p.220, the circuit column and Lean's `powerRel` all write P; P and E agree only on maps
    (B&dM p.119, p.202) and these arguments are relations, so the three certs name the wrong operator.
