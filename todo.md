# todo

State at `bcea521` (pushed): `make c` exit 0 — 142 panels / 142 swept / 133 certified / 0 unhandled / 0 failures,
369 markers verified, 96 circuit literals verbatim, 399 respelled 0 differ. `make p` exit 0, 88 pages.
`./scripts/diagram --compare` reports **15 drifted**.

## 1. Apply the left sweep to the note

`scripts/diagram` already clears only the lanes ALIVE at each height instead of every lane the panel ever made, so
the object edge can sweep further left — but `./scripts/diagram --write` has never been run against it. That is why
`--compare` is 15 rather than 14.

- Snapshot `diag/allegory-axioms.typ` first, and run `--compare > drift.txt` BEFORE `--write` to get line numbers.
- `--write`, then restore the fourteen panels below from the snapshot.
- **Restore by LINE NUMBER, never by `expect` string.** Several `expect` strings occur more than once in the note;
  an earlier pass matched by string and restored four wrong blocks.
- Verify: `--compare` must then report exactly 14, and they must be exactly these fourteen.
- A `scan-strict` crossing means the clearance test is too loose — tighten the test, do not restore the panel and
  do not touch any knee.

## 2. The fourteen panels `scripts/diagram` draws wrong

The note's versions are correct and must survive every `--write`. Until these are fixed, task 3 is blocked.

```
𝟙%∋ E(⦇S⦈)E(choose)est(R°)
𝟙%∋ E(⦇S⦈)est((R×R)°)𝟙%∋ E(choose)est(R°)
π₂ list(𝟙%∋)list(E(choose))list(est(R°))concat
(T°)%∋ thin(Q)P(F(X)h)est(R)
(Vᵢ°)%∋ thin(Qᵢ)P(Fᵢ(X)Uᵢ)est(R)
([base,step]°)%∋ thin(Q)P([nil,(𝟙×X)cons])est(R)
(step°)%∋ thin(U×V)P((𝟙×X)cons)est(R)
([nil,extend]°)%∋ thin(Q)P([nil,(X×𝟙)snoc])est(R)
(extend°)%∋ thin(prefix°×(⊤+⊤))P((X×𝟙)snoc)est(R)
reduce list((encode×𝟙)snoc)minlist(R)
([nil,expand]°)%∋ est(Q)[nil,(X×𝟙)snoc]
(expand°)%∋ est(V×U)(X×𝟙)snoc
([nil,snag]°)%∋ est(Q)[nil,(X×𝟙)snoc]
(snag°)%∋ est(Q')(X×𝟙)snoc
```

The fifteenth currently drifting, `⦇generate⦈N(est(R))setify est(R)` near `:7107`, is NOT one of these — it was
restored because its generated shape crossed under the old geometry. Let `--write` take it and see whether the
left sweep fixes it on its own.

## 3. `./scripts/diagram --compare` joins `make c`

Blocked on 2: the gate cannot be green while fourteen panels are known-wrong by design.

## 4. `!nat` — handed to freyd-04

- The marker has **zero call sites** in the note, and no `"nat"` key in `diag/hm-sigs.json`; only the five
  `diag/pairs/*.json` fixtures declare it. A gate refusing an undeclared off-wire bead cannot be written until a
  call site exists.
- `cons` and `π₂` are NOT call sites: `natural()` already infers True for both, so a marker changes no ink. The
  first call site is a name `natural()` infers **False** for and that is one — a single Greek letter, or an
  application.
- **Decide before writing the gate:** a boolean `nat` cannot say lax from strict, and the two places that mention
  it disagree — `natural()`'s docstring states naturality as an EQUALITY, `scanline`'s comment points at
  `LaxNatural`. Nothing consumes the `cite` half of `!nat=lean:...` either; `typed()`'s comment claims `cite-check`
  verifies it, which is intent, not fact.

## 5. Restart Claude Code

440 stale git worktree registrations were pruned to 35 (`freyd` held 242 of them, all dead). The Bash sandbox
profile is built at process start, so the running session still carries the old 484 deny paths and still hits
`E2BIG` on ordinary commands. Only a restart rebuilds it — `compact` does not.

`tv-hask` keeps 26 real worktrees at 4.4 GB; those are live, not stale.
