# Handoff — emergency stop (machine reboot)

Branch: worktree-agent-af2582376f0111bfb.

## Committed
- c2f22fb — Task 1 (Sub is a function), gated clean earlier (make c CH=14/15 both exit 0).
- b9ad4ba — merge of master (diag-export staleness rework; no conflicts, does not touch diag/ch or
  note-prelude.typ).
- 27b0807 — WIP: 11.6.4 merged table (Task 2) + hylo-mu label repoint. NOT RE-GATED after the last
  two edits inside it (see below) — do not trust it builds until you re-run `make c CH=11`.

## What 27b0807 contains
- `diag/ch/11-relator.typ`: hylo_fixed / hylo_le_of_prefixed / hylo_eq_mu merged into ONE
  `#disp[#calc-table(...)]<hylo-mu>`, headed by hylo_eq_mu's Thm+#src. hylo_fixed and hylo_eq_mu go
  through `Sub("Freyd.Alg....", gloss: ..., steps...)` fed to `lean-chain` (Task 1's mechanism,
  unchanged). hylo_le_of_prefixed is NOT going through Sub/lean-chain — it stays on `hchain(...)`
  directly under a new `sub-header(decl, gloss:)` banner (visually identical to a Sub row), with its
  ORIGINAL `hyl-m` 12-selector `lean-pics` binding restored and its 6 steps as `trow(hy-X, hy-X-r)`
  pairs, EXACTLY as before this task touched it (Task 3's height fix is NOT applied to any of these
  6 pairs in the committed state).
- `diag/note-prelude.typ`: added `#let sub-header(decl, gloss: none) = ...` (the banner block
  factored out of `lean-chain` so a non-lean-chain row can still look like a Sub row). `lean-chain`
  itself is back to EXACTLY Task 1's version (one selector per step, one shared `lean-pics` call per
  row) — the paired-step generalization described below was tried and reverted.
- `diag/ch/14-thinning.typ`, `15-dynamic.typ`, `16-greedy.typ`: every `@hylo-fix`/`@hylo-least`
  citation repointed to `@hylo-mu` (the merged table's one surviving label). This part is done and
  gates fine (labels resolve, `<hylo-mu>` still exists).

## CORRECTED Task 2/3 plan (coordinator's correction — supersedes my earlier "flatten into 12 singles"
plan, which is WRONG: each `trow(hy-X, hy-X-r)` pair is ONE statement `lhs ⊑ rhs`; flattening to two
sequential chain terms joined by SQ asserts a DIFFERENT thing than the pair does. Do NOT flatten.)

Correct design: extend `lean-chain`'s step form so a step's selector may be a 2-array `(selL, selR)`
meaning "this step draws BOTH sides of its own relation, via ONE `lean-call("generated/", <lean-panel>,
(selL, selR))` call" (exactly what `#lean(a, b)` does for an ordinary equation display — one exporter
call, two selectors, shared depth, `trow`-wrapped result). I implemented this once already (now
reverted) as:

```
#let lean-chain(..args) = {
  ...
  let calls = rows.map(r => {
    let singles = r.steps.filter(s => type(s.at(1)) != array).map(s => s.at(1))
    let (m, spics) = if singles.len() > 0 { lean-pics("generated/", <lean-panel>, singles) } else { ([], ()) }
    let i = 0
    let pics = ()
    for s in r.steps {
      if type(s.at(1)) == array { pics.push(lean-call("generated/", <lean-panel>, s.at(1))) }
      else { pics.push(spics.at(i)); i += 1 }
    }
    (m, pics)
  })
  ...
}
```
and the circuit-companion line also needs: `if type(s.at(1)) == array { leanc(..s.at(1)) } else { leanc(s.at(1)) }`.
This is CORRECT and matches the coordinator's ask. Re-apply it (it is fully backward compatible with
every existing plain-string-step chain — verified by re-derivation, not by a green build after
re-applying, since I reverted before re-testing the revert-of-the-revert).

## BLOCKER found, still open: the `#h` pair crashes `diag-export --stale`
Isolating `Freyd.Alg.hylo_le_of_prefixed#h.lhs` + `#h.rhs` as their OWN 2-selector call (via the
mechanism above, or equally via a bare top-level `#lean(a, b)`) makes `make c CH=11` fail
reproducibly, twice, identically:
```
uncaught exception: diag-export --stale: Freyd.Alg.hylo_le_of_prefixed#h.lhs+Freyd.Alg.hylo_le_of_prefixed#h.rhs: no such declaration: [anonymous] — a picture drawn from it is a picture of a statement that no longer exists.  Rename the note's selector
make: *** [Makefile:131: panels] Error 1
```
But the IDENTICAL selector pair succeeds standalone outside the full `make c` sweep:
`./scripts/diag-export --prepared --stale --string "Freyd.Alg.hylo_le_of_prefixed#h.lhs+Freyd.Alg.hylo_le_of_prefixed#h.rhs"`
→ exit 0, and a full `--list` + `--stale` re-run over the WHOLE note's 308-selector metadata list
(built via `./scripts/diag-export --prepared --list /tmp/ll lean-panel lean-circuit lean-cd
lean-graph lean-formula lean-type lean-value`, then `grep -v '^[[:space:]]*$' /tmp/ll/lean-panel |
xargs -d '\n' -r ./scripts/diag-export --prepared --stale --string`) ALSO succeeds — yet `make c
CH=11`'s own `./scripts/diag-regen --missing` invocation of the exact same check, on the exact same
selector, fails every time. I could not isolate what's different about `make`'s invocation context
in the time available (did not find it before the stop). `hylo_le_of_prefixed`'s hypothesis `h` is
real (`h : S° ≫ F.map X ≫ R ⊑ X`, confirmed via the refactor-index sqlite db), so this is not a bad
selector — it is an exporter defect from the recently-merged "diag-export staleness rework"
(master b9ad4ba), not a note-content bug. Do not keep poking at it blindly; if reproducing again,
capture `diag/tool/`'s relevant staleness-check source (I could not grep it — cc-guard blocks Lean
source grep; use the refactor-index db or ask for direct file access) before trying more fixes.

**Given this, when re-applying the pair-step mechanism**: apply it to hylo_le_of_prefixed's OTHER 5
steps (base, cataR, rec, adj, fuse — none of them "#"-suffixed) and leave ONLY the 6th (`#h`) step
as `trow(hy-prefix, hy-prefix-r)` sourced from a small preserved multi-selector `lean-pics` binding
(keep `hyl-m`, or shrink it to just cover the `#h` pair PLUS at least one plain sibling selector so
it is never an isolated 2-element `#`-only group — I did not get to test whether a 2-element
`(#h.lhs, #h.rhs)` group specifically, vs. a >2-element group containing it, is what triggers the
bug; test this cheaply first with the direct CLI commands above before writing note prose). Report
this one pair as the "left alone, and why" exception in the final report, alongside 13-optimisation's.

## Task 3 (other chapters), NOT STARTED
Known pairs to convert to `lean(selL, selR)` (or the new pair-step form, if the row is a `lean-chain`
row) once the mechanism above is back: `ma-Fest-lam`/`ma-lam`, `ma-Fest-ni`/`ma-Fni`,
`mon-s3l-l`/`mon-s3l-r`, `ma-Ro`/`ma-Rbare-Ro`, `ma-R`/`ma-Rplain-R`, `gr-mon`/`gr-Rbare` — chapter
files not yet located, grep each name across `diag/ch/*.typ` first. Leave the `leanc(...)` pair in
`13-optimisation.typ` near line 622 alone (its own comment says the two are two separate statements).
Delete `trow`'s definition in `note-prelude.typ` only if grep shows zero remaining call sites after
all conversions (it is still used by hylo_le_of_prefixed's row right now, so do not delete it yet).

## Gates: NOT RUN since commit 27b0807's last two edits
Before anything else, re-run `make c CH=11` (foreground, timeout 600000) to confirm the CURRENTLY
COMMITTED state (hylo_le_of_prefixed fully reverted to its pre-task form under a `sub-header`
banner) still builds — it did build clean (exit 0) at an earlier point with this exact content, but
re-verify after a fresh checkout since disk state before the stop was not re-tested after the very
last edit pass.

## Do NOT
Do not `git add -A`. Do not run `git stash`. Do not `checkout`/`reset`/`clean`. This worktree is
mid-task; resume by reading this file and `git log`/`git diff HEAD~1` on 27b0807 to see exactly what
changed.
