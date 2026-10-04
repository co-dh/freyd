# Handoff: def-table cells the exporter could not print

Done (diag/tool/TypeRender.lean, `render`, last match arm):
- plain functions, `Type`, `Prop` declarations: the type cell is the Lean type of the name-cell term,
  the declaration applied to its NAMED binders (an `A → B` arrow has a hygienic binder and stays in
  the type). Theorems that are no (in)equation are still refused.

Left:
- Item 4 `Paragraph.Q_eq`: `Unknown constant null`. Reproduced by labelling `graph headLine`
  (scratch file Bisect.lean in the session scratchpad: walks the rhs subterms with `labelT`).
  `headLine` is a 2-arm `match` on ConsList. Throw site in diag/tool/Label.lean map-label path not yet
  pinned (`mapLabel`/`guardLabel` ~l.887, `declName?` l.495, `ctorName?` l.727).
- Item 3: `fun x y => …` relation defs (Knapsack.Q/R/within, Paragraph.Q/R/ok/fits, Tour.R/Qc) are
  refused by ExprReader.lean `checkSpelled` (lambda on the page). Plan: a formula-route selector
  printing `x R y ⟺ body` from the def value's lambda telescope.
- Name cells needing `diag_noted`/unexpanders in diag/StrDiagNames.lean (vocabulary for the note
  rows): Tour.Tour, Tour.hd, Tour.nxt, Tour.cost, Tour.incost, Tour.outcost, Tour.replaceHead,
  Paragraph.sqr, glue, new, headLine, widthFn, wasteFn, allFitP, partAlg, ListRel.total, *Fn/*AlgFn.
