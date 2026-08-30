# Note queue

Working branch: `est-rename`. Style target: §13.3.1's `<mon-thm71>` table — `Thm[...]` statement cell,
`columns: (1fr, 7.1cm)`, `table.header([*circuit*], [*Hinze–Marsden*])`, one row per derivation step.

## Done

- [x] Theorem 6.1 (Knaster–Tarski) + Theorem 6.2 (hylomorphism) in §11 — `thm62`, merged `4c6bf52`
- [x] §13.3.3 takewhile — `style-takewhile`, merged `f46985c`
- [x] §13.3.4 mss — `style-mss`, cherry-picked `d7de3b1`
- [x] §13.3.5 filter — `style-filter`, merged `69d65a4`
- [x] §13.5.2 cylinder — `style-cylinder`, merged `f54142d`
- [x] 13.3.2a: split the `S%∋` bead into `(𝟙%∋)E(S)` in every panel
- [x] Delete §13.3.1's comment "the note's `est(R)` is B&dM's `min(R°)`"
- [x] Fix the greedy citations in §13.3.3 / §13.3.5 / §13.4 — the monotonicity lemmas restated
      at `R°`, `485fb38`
- [x] Named converses instead of `°`: 72 × `≤°` → `≥`, `485fb38`

## In flight — seven agents, one section each, all worktrees off `est-rename`

- [ ] §13.3.1 `<mon-thm71>`'s `⟺` row and §15's line ~5816: drop the law's name, cite the `@div-laws`
      shunt. Also report whether `@est-laws` and `@est-75` are one fact under two labels — main checkout
- [ ] §13.3.3b `<takewhile-alg>` and §13.3.5b `<filter-alg>`: `[A]` becomes two wires — `style-wires`
- [ ] §13.3.4c–f get the Hinze–Marsden column; 13.3.4g's `%∋` beads split — `style-mss-hm`
- [ ] §13.4 party subsections, §13.6b security van — `style-party`
- [ ] §13.5.2b: curry the bifunctor so no wire crosses — `style-curry`
- [ ] §11.6.4: is Theorem 6.2 proved or only stated? — `style-hylo`
- [ ] §14.1–14.6 law tables — `style-ch14`

## Merged into `est-rename`, or waiting to merge

- [x] §12.1 subseq — `style-subseq`, `2d406d9`, not yet merged

## Next

- [ ] `@est-defn`'s `#src` says `est(R)` is B&dM's `min R`; as *arrows* it is `min_bdm(R°)`,
      because B&dM's infix `a R b` puts the input on the right. Decide which reading the line
      states, and say so — the same ambiguity keeps coming back through the greedy citations
- [ ] The remaining "the law | what it says" tables: §15.1–15.4, §16.1–16.4.
      Most of their rows state B&dM theorems the note cites rather than proves (8.1, 9.1, 9.2, 10.1,
      Prop 9.1/9.4) — those stay citations unless the proof is written
- [ ] 13.4.4a and the others still giving the reason its own column: fold it into column 1
- [ ] Colour the wires by type across the string diagrams, 13.5.2a first; one palette, in a comment.
      Touches every panel, so it must run alone — after the seven in-flight branches are merged
- [ ] Curry the bifunctor in 13.5.2b so no wire crosses — show the picture before changing more
- [ ] Rewrite `X⊑Y`, `X` entire, `Y` simple as its values — `X`/`Y` clash with `@takewhile-defn`'s
      `(g→X,Y)`; cited from §13.3.3, §13.3.4 and §13.3.5, so all three move together

## Lean

- [ ] `lean-refactor`: add a `binder d n {explicit|implicit|instance|strict}` operation (its own repo)
- [ ] `InitialAlgebra` becomes a class, `I` becomes instance-implicit, 284 `relCata` call sites lose it
- [ ] Notation layer so the Lean statement differs from the note only by `≫`:
      `⦇R⦈` for `relCata`, `%∋` for `Λ`, `est(R)` parenthesised
- [ ] `lean:<decl>@<stmt_key>` markers in the note's `#src`, checked against `refactor-index.db`
      (`decl_info` carries `stmt` and `stmt_key`) from `make p`
- [ ] `R°°` left in the thinning / greedy-DP hypotheses (A9_1, A10_1 and wrappers) — collapsing it
      needs the involution applied to `thin_condition_of_optimum` and `birelator_thin_condition`
- [ ] `RelSet.CL.est_pt` and `RelSet.est_apply` are now the same statement in two lib roots

## Drawing

- [ ] `hm-stack` in `diag/hm.typ`: x from the wire count, y from the bead order, `joins` from `kills`,
      so the per-section `TX*`/`RX*` constant sets go away
