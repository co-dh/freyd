# Handoff (branch worktree-agent-ad2cf3ac9a47ad576, base afc8346)

## Done and committed
- Item 3: 9 of 10 headers now `#leanf(...)` (allegory-appendix cyl_step/cyl_laws/cyl_fusion; 08-thinning thinRel_comp_est_step1/cond1/cond2;
  07-optimisation mss_mono, filter_mono). NOT regenerated or compiled yet: no `make c` has run with these.
  Skipped: 07-optimisation:339 (Theorem 7.1 iff; its two markers cite two different decls distributes_of_monoAlg and
  monoAlg_of_distributes, no single decl; monoAlg_iff_distributes has different hypotheses), 07:1343 (already leanf).
- Item 7: deleted diag/circuit-sigs.json, sig-audit.txt, CIRCUIT-GEN.md; removed the comment citations in cpanel.typ,
  aop/05-datatypes.typ, tool/CircuitDiagram.lean. Cite.lean:36 and 07-optimisation:~1865 held no such reference. Nothing reads the json.
- Item 10: scripts/wrapper_scan.py deleted (nothing referenced it).
- Item 14: deleted So-box, sort-P-box, thinlist-Q-box, est-Rc-box, listcp-F-box, pair-g-box, minlist-R-box (note-prelude.typ),
  est-R-box, union-box (circuit.typ; also unused), and the 07-optimisation comment about est-Rc-box.

## Skipped
- Item 11: nothing in the Makefile regenerates diag/axiom-crosscheck.typ (only scripts/paper-figs, run by hand, needs paper PDFs).
- Item 12: p's loop is per NOTENAMES with inkfit once; `labels` is per NOTE with inkfit each: not one list; merging changes behaviour, needs make p.

## Left: item 5 (StrDiagNames identity unexpanders) and all gates
- Awk filter ready: /tmp/claude-1000/-home-dh-repo-freyd/b7f0f1a5-63aa-407e-ba33-031579730f2e/scratchpad/ident.awk (reads the file,
  prints the file minus 4-line identity unexpanders; `-v names=FILE` receives their full names). It matches exactly
  `open Lean PrettyPrinter in / @[app_unexpander X] def N : Unexpander / | `($_ $args*) => `($(mkIdent `last) $args*) / | _ => `($(mkIdent `last))`
  with last == X's last component. In diag/StrDiagNames.lean that hits at least Party.party, choose, Tex.interval, intern, Tardy.bagify,
  SL.arm₂, ListRel.subseq, MSS.mss, Paragraph.partition, Bracket.splits, Edit.step, TT.F, and more further down (lines ~1243-1800).
  NOT identity (keep): Edit.Op (drops args), Salg/S (prints S).
  Then add `attribute [diag_noted] <names>` after line 84 (`attribute [diag_noted] dom ran Entire ...`), `lake build diag`.
- Panel comparison: diag/generated was seeded in the worktree from /home/dh/repo/freyd/diag/generated (cp -a) and a copy of that baseline was
  taken at scratchpad/before (same dir as ident.awk). Intended: after the edit, `xargs rm` the generated files that mention the names,
  `make c NOTE=aop CH=n` (n=6..10 at least, 7 and 8 required) regenerates them (--missing), then `diff -r` against scratchpad/before.
  Note: a fresh worktree needs diag/generated seeded first, else `make panels` fails with
  "FileNotFoundError: .../diag/generated/Freyd.Diag.meet_top.typ"; and scripts/diag-regen (full) is refused by a hook after one run.
- Gates still to run: `lake build diag`; `make c NOTE=aop CH=7`, `CH=8` (item 3 and 14 touched them), and the axioms chapter holding
  allegory-appendix (find with scripts/note-files; diag/ch has 01..10 files, appendix is included from somewhere not yet found).
