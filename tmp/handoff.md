# Renumbering handoff (commit 2dc8216)

## Done
- diag/aop/08-thinning.typ: 8 `#disp(num: "...")` additions applied exactly per
  tmp/aop-numbers/ch8.tsv (thin-defn, thin-82, thin-83, thin-thm81, thin-cor,
  thinlist-86, thinlist-lem81, thinlist-thm82). Every other ch8 row's "new number"
  is section+letter (8.2a-8.6c) which the automatic dispnum already produces
  (file has `note-chapter.with(8)`), and the law tables (thin-laws, thinlist-laws)
  already carry their book numbers inline via `#src[(8.2) — @thin-82]` etc., same
  pattern as the ch10 pilot.
  Gate: `make c NOTE=aop CH=8` passes (labelfit/inkfit/dispfit/cd-check all clean).

- diag/aop/09-dynamic.typ: 14 `#disp(num: "...")` additions per ch9.tsv (dp-thm,
  dp-lower, dp-upper, dp-laws, dp-disjoint, dp-cost, dp-context-mono,
  dp-bifunctor-thin, mct-cost, mct-g-mono, mct-rec, col-rec, col-cons, row-rec).
  All section+letter rows (9.1a-9.4d) are automatic, no edit needed.
  `make cite NOTE=aop`: 1002 markers verified, exit 0.

- Verified with `pdftotext -layout diag/aop/08-thinning.pdf` that (8.1),(8.2),
  (8.3), Theorem 8.1, Corollary 8.1, Lemma 8.1, Theorem 8.2 print correctly.

## Ambiguous / not applied
- ch9.tsv rows `dp-example-defs`/`dp-example-h`/`dp-example-H` (typst labels
  `dp-example-defs`, `dp-example-h`, `dp-example-H`): new-number column says
  "flag: ch5/ch6", not a concrete chapter+number — the row's own note says moving
  them would shift the rest of §9.1's letters, and gives no decision on ch5 vs
  ch6. Left as automatic 9.1a/9.1b/9.1c (unchanged). Needs a decision before a
  move: which of diag/aop/05-datatypes.typ or diag/aop/06-recursive.typ, and
  under which heading.
- Did not attempt the "row-level" table-row citations in ch9.tsv (e.g.
  `dp-conditions#row1` = Proposition 9.2, `edit-thin#step4` = Exercise 9.6, etc.)
  — these are `#src[...]` glosses inside existing lean-chain/table rows citing
  book items; a spot check of 08-thinning.typ shows this pattern is ALREADY
  present in the note (inline `#src[(8.2) — @thin-82]` etc.) for both files, so
  no further action looked needed, but I did not verify every row-level entry
  in ch9.tsv against the note text (there are ~15 of them). If they don't
  already match, grep `diag/aop/09-dynamic.typ` for each Exercise/Proposition
  number in the tsv's row-level section and compare to `#src[...]` text nearby.

## Known pre-existing failure (NOT caused by this change, do not fix here)
`make c NOTE=aop CH=9` fails:
```
error: assertion failed: this panel draws the named lanes `tree` and `F` ΔE76 19.8
apart, under 29 — `FCOL` fixes both hues, so no allocation can separate them:
change one of the two entries (diag/draw.typ)
  diag/draw.typ:686:6 (panelpal), called from diag/dpanel.typ:377:12
make: *** [Makefile:116: diag/aop/09-dynamic.pdf] Error 1
```
Confirmed pre-existing: reproduced identically after `git stash` reverted this
commit's two `.typ` files back to HEAD~1 (base 5f5b89c), then re-stashed my
changes back on top. Not one of the two documented known failures (CH=6
labelfit/flatten/° and the Cylinder.gen red stub) but same category — a
lane-color allocation issue in the shared `diag/draw.typ`/`diag/dpanel.typ`
machinery, orthogonal to display numbering.

## Gates run
- `make c NOTE=aop CH=8` — pass
- `make c NOTE=aop CH=9` — fails (pre-existing, see above)
- `make cite NOTE=aop` — pass, 1002 markers
