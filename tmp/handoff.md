# Segmenting-list example (15.1) — handoff at the 40-call checkpoint

Done:
- AOP/A9_0_SegmentExample.lean: T, h, fold_T, fold_T_recip, fold_h, H_eq, H_fix, h_nil/h_c/h_ab_c/h_a_bc,
  H_abc (+ cappend/partition helper lemmas). Builds.
- AOP/A5_6_ListCombinators.lean: concatNE made @[expose].
- diag/StrDiagNames.lean: imports the module; cons-list literal unexpander; inl(…)/inr(…) notation.
- diag/ch/15-dynamic.typ: `== Example: segmenting a list <dp-example>` before `== Theory`.

Left:
- `make c CH=15` to green; check the generated formula text of the new #leanf cells.
- Review png via pdftotext -bbox + pdftoppm, hand to `look`; commit with diag/ch/15-dynamic.pdf.

Failing (dropped): the `#lean(H_fix.lhs, H_fix.rhs)` panel — exporter wrote a red stub:
  "diag-export: drew a red stub for 2 selector(s): Freyd.Alg.RelSet.Segment.H_fix.lhs ... .rhs"
  (no naturality verdict found for the concrete `T`; "tried …: no unification").
