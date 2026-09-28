# Handoff — (6.1) val-converse chain, 3 faults — DONE

Committed as 9c34e2b on worktree-agent-a850b44fb149979a2 (base 45f69d0). All three faults are fixed,
the build/gates pass, and the `look` review of tmp/rv/u6.png came back PASS on all three items (see
"Review picture" below). Nothing outstanding.

## Done

1. **Union mark between the two branch panels** — `diag/aop/06-recursive.typ`, the `val-converse`
   lean-chain (right after `<val-converse>`): the tuple for `val_converse_step6.rhs.inl` had
   `op: none`; changed to `op: [∪]`. Same mechanism as the existing `lean(a, b, op: [∪])` calls
   elsewhere in the note (e.g. `diag/aop/07-optimisation.typ:1951`, the `Van.Hrel` row).

2. **Gloss in the display's own letters** — same file, the `val_converse_step6.rhs.inr` step's
   `src[...]` gloss: `[g,h]°[P,Q]=g°P∪h°Q` → `[embed,op]°[wrap,snoc]=embed°wrap ∪ op°snoc`. Confirmed
   in the rendered PDF text (pdftotext -bbox) that it prints correctly with the `∪` spaced.

3. **Pink-region/dashed-line label overlap** — root-caused via `pdftotext -bbox` + the generated
   panel's own `dpanel(...)` call plus the Lean source, not pixels. The pink region + dashed line is
   the CORRECT, intentional Hinze-Marsden drawing of a whole-composite converse (`Freyd.StrDiag.Conv`,
   `diag/tool/StringDiagram.lean:76-85`, `whole` field, doc comment confirms: "`whole` is the `°` of a
   conversed COMPOSITE `(XY)°`... stands WEST of them all"). The bug was only the label clearance: the
   `°` boundary column opens a FIXED `DX = 0.625` west of the lane it carries (`panelCode`,
   `StringDiagram.lean` ~line 391-407), but the lane name `Digit⁺+−` (8 chars) needs ~`LCW*8 ≈ 2.04`
   units by the same character-width estimate `spreadEdge` uses for port labels (`LCW = 0.2039/0.8`) —
   far more than the fixed 0.625 gap, so the west-anchored name ran straight across the dashed line.
   Fixed in `diag/tool/StringDiagram.lean` (`panelCode`, the `wholes`/`wires` computation): added
   `wholeGap`, sizing the gap as `max DX (LCW * carryingLane.label.length + LDX)` instead of the bare
   `DX`, used both for the lane-shift and the wire-x1 offset. General fix — any future wide functor
   name on a whole-conv lane gets room automatically; no per-panel special case.

## Gates run

- `./scripts/cap lake -d <wt> build AOP diag` — exit 0, `diag.tool.StringDiagram` built clean.
- `make -C <wt> c NOTE=aop CH=6` — exit 0. `labelfit: 06-recursive.pdf, 5 pages, 0 overlapping label
  pairs, tightest 1.46pt` (this is the check that would have caught the old overlap). `inkfit`: 0
  unreadable words. `dispfit`: 0 pages past frame.
- `make -C <wt> c NOTE=aop CH=N` for N in 5, 7, 8, 9, 10: all exit 0 (CH=9's previously-reported
  lane-hue-clash failure did NOT reproduce here — it now passes clean; nothing to report there).
- `make -C <wt> c NOTE=aop CH=2` — exit 2, but NOT a regression: `diag/aop/` has no chapter-2 file
  for the `aop` note (files are `03-applications`, `05-datatypes`, `06-recursive`, `07-optimisation`,
  `08-thinning`, `09-dynamic`, `10-greedy` — no `02-*`/`04-*`). `note-files --ch 2` correctly refuses.
  Pre-existing structural fact, unrelated to this change.

## Review picture

- Before: `/tmp/claude-1000/-home-dh-repo-freyd/0356838a-1800-4f1b-9ba4-1f0d1ec8a354/scratchpad/S4.png`
- After crop: `<wt>/tmp/rv/NEW.png` (page 1 of `diag/aop/06-recursive.pdf`, 200ppi, x:[0,1969px]
  y:[250,889px] ≈ pt [90,320], located via `pdftotext -bbox` on the rebuilt PDF — covers the Thm
  header formula through the lettered (a)-(d) caption block).
- Stacked: `<wt>/tmp/rv/u6.png` via `./scripts/diff-crop --stack S4.png NEW.png --caption "we can
  start with what you've done: draw each branch as a string diagram" --out <wt>/tmp/rv/u6.png`.
- `look` dispatched on u6.png (agentId ad0e17f3f41d78365), result: **PASS on all three items.**
  (1) every bead/label in the after picture is val°/[embed,op]/val/[wrap,snoc]°/Digit⁺+−/-×Digit/
  [embed,op]°/[wrap,snoc]/op°/snoc/embed°/wrap and gloss letters val/embed/op/wrap/snoc/α/F/R/S/P/Q/φ —
  no g/h/C anywhere, old gloss gone. (2) `∪` sits between the last two branch panels in the after
  picture; the before had blank space at the analogous tail position. (3) the pink region + dashed
  line + `°` mark are still drawn (correct, intentional whole-composite-converse notation) and
  `Digit⁺+−` now sits clear of the dashed line with a visible gap, no overlap.
  Caveat the reviewer flagged: `S4.png` (the before half, handed in as-is per the dispatch) turned out
  to show a different display (6.1b's step-4/5/6 arm) rather than 6.1a's own pre-fix state, so item 1's
  "no g/h/C" was confirmed only by inspecting the after picture directly, not by diffing against a true
  before of 6.1a — the after-picture check is still conclusive on its own. If an exact before/after of
  6.1a itself is wanted later, re-cut both halves from the same section.

## Anchors

- Chain: `diag/aop/06-recursive.typ` lines ~16-36 (`<val-converse>` display).
- Fix: `diag/tool/StringDiagram.lean`, function `panelCode`, the `wholes`/`carried`/`wholeGap`/`wires`
  block (search for `wholeGap` — it's new).
- Constants used: `DX = 0.625`, `LCW = 0.2039/0.8`, `LDX = 0.12` (`StringDiagram.lean` lines ~29-38).
- Generated panel for step1.rhs (the one with the pink region) lives nested under
  `diag/generated/Freyd.Alg.RelSet.Digits.val_converse_step1.lhs/.../val_converse_step6.rhs.inl/
  Freyd.Alg.RelSet.Digits.val_converse_step1.rhs.typ` — the whole chain's singles share one export
  directory (joined selector names), so all six `.typ` panels for this display live under that one
  deeply-nested path.

## Nothing else outstanding

No known failing gate, no uncommitted diff (tmp/ scratch files remain untracked, as expected —
not part of the deliverable). Committed at 9c34e2b.
