# Handoff — a mark belongs to the step that LEAVES the panel (branch worktree-agent-a62aca6cd43669fbd, on 1c50e68)

## Done (diag/tool/StringDiagram.lean, not yet built)
- `Row.eq`: the leaving step's sign is `=`; `panelCode` writes the 6th bead field `"eq"` for it.
- `passOf?` takes `rev` (an equation read right to left); `passHyp` records both readings;
  `moveStep?` tries either side of an equation.
- `Step` (name, eq, proof, hyps, used) with `Step.cites`/`Step.key`; `squareThm` tries only cited
  candidates; `passThm φ Y below st`, `moveThm side st` memoised per step.
- `peerStep n side` replaces `peerHyps`; `settlePass d steps side?` replaces the old
  `settlePass` + `settlePeerHyps`.

## Left
- `panelOf` still passes `proof` to `settlePass`; `withParts` still calls `settlePeerHyps`;
  `drawWith`'s `reqParts` must tag each drawn part with "is the statement's left side" and the
  statement's sign (`Eq` head of `body`), build `steps := own (if left) ++ peers.filterMap peerStep`,
  and hand the call's declarations to the `draw := false` peer drawing too.
- `diag/hm.typ` `hm-mark`: add the key `"eq"` (hollow circle, the ink `"lax"` has; the exporter draws
  lax as `"pass"`, so the circle is free).
- `diag/tool/PassMarkTest.lean`: rewrite on `peerStep`/`settlePass` (bead, shape, panel).
- Task 4: 7.2.1b (`<dist-str>`, diag/aop/07-optimisation.typ) is the only display calling
  `pair-fill` (diag/draw.typ), which scales the pair to the column width; every other `pair` is at
  `s: 100%`.  Measure its present factor from the pdf, then set the scale.
- Gates, changed-marks list (before = agent-aeff542b9ab0c1d14/diag/generated), pictures x62–x65.
