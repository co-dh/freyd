# Note queue

Working branch: `est-rename`. Style target: §13.3.1's `<mon-thm71>` table — `Thm[...]` statement cell,
`columns: (1fr, 7.1cm)`, `table.header([*circuit*], [*Hinze–Marsden*])`, one row per derivation step.

## In flight

- [ ] Theorem 6.1 (Knaster–Tarski) + Theorem 6.2 (hylomorphism) in §11 — branch `thm62`
- [ ] 13.3.2a: split the `S%∋` bead into `(𝟙%∋)E(S)` in every panel — main checkout

## Done, waiting to merge into `est-rename`

- [x] §13.3.3 takewhile — `style-takewhile`, merge commit `3097335`
- [x] §13.3.4 mss — `style-mss`, `97c1ccf` (drop its baseline commit `98cbb52` when merging)
- [x] §13.3.5 filter — `style-filter`, `9f85e65`

## Next

- [ ] Merge the style branches; drop each one's hand-copied baseline commit
- [ ] Delete §13.3.1's comment "the note's `est(R)` is B&dM's `min(R°)`" — `@est-defn`'s own `#src`
      says `est(R)` is B&dM's `min R`, and that is the one matching the pointwise definition
- [ ] Fix the greedy citations in §13.3.3 / §13.3.5 / §13.4: `@greedy-thm72` at `R°` needs
      monotonicity on `R°`, not on `(R°)°=R`. `@takewhile-mono`'s `nil R=⊤` row is `R`-specific,
      so it needs its own `R°` version rather than a reworded citation
- [ ] §12.1 subseq
- [ ] §13.4 party subsections, §13.6b security van
- [ ] The 14 remaining "the law | what it says" tables: §14.1–14.6, §15.1–15.4, §16.1–16.4.
      Most of their rows state B&dM theorems the note cites rather than proves (8.1, 9.1, 9.2, 10.1,
      Prop 9.1/9.4) — those stay citations unless the proof is written
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
