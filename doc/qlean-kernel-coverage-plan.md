# qlean kernel coverage plan for leetq's five partial ops

Read-only analysis, 2026-11-10. Sources: qlean `master` at `a260b4e` (`/home/dh/repo/qlean`), leetq on branch
`leetq-total` at `5e837d3` (`leetq/` under the freyd checkout). Line numbers are those of these two commits; the
declaration name is the anchor, a line is a pointer and may be off by a few lines. Nothing was built and q was not
run: every statement about q below is quoted from a qlean file, and where qlean has no statement the cell says so.

The five ops (`leetq/LeetQ/Rel/Scan.lean`): `Ops.scan` :36 (`scanColumn`), `Ops.over` :42 (`overColumn`),
`Ops.avg` :45 (`avgColumn`), `Ops.overBy` :113 (`groupedOver`), `Ops.mwin` :127 (`mwinColumn`).

## 0. Findings that change the shape of the work

- Of 456 (verb, type) cells, 297 are covered today, 70 are inputs q rejects, 61 need a qlean change and 28 need a
  decision. 12 further rows (layouts, window `0`, other dyads) are listed apart.
- Only 2 of the 61 "extend" cells need new C (`fills` over symbol and guid). The other 59 are Lean dispatcher
  work in qlean that composes kernels which already exist: `overFloats` (`Kernel/Reduce.lean` :732),
  `castColumn` (`Kernel/Elementwise.lean` :1927), `monColumn "null"` (:2156), `overGroupsFloat` (:458).
- `avgColumn` needs no qlean change at all.
- qlean's own evaluator already answers every float `sum`/`prd`/`min`/`max` by calling `overColumn` and then
  `overFloats` (`Eval/Mon.lean` :325 `sum`, :344 `prd`, :397 `extreme`). leetq calls only the first half.
- In 20 cells the kernel answers where q rejects (`prd` and `prds` at a temporal type, `prd` at `char`). The
  precondition of an op must therefore be q's typing rule, never the kernel's claim set.
- Extending the kernels does not remove the count hypothesis `n < USize.size` of `scanColumn_isSome`,
  `mwinColumn_isSome` and `groupedOver_isSome`. Section 6, decision I/J/K.

## 1. Cells

### 1.0 Type groups and verdict codes

| group | types                             | count |
|-------|-----------------------------------|-------|
| B     | boolean                           | 1     |
| Y     | byte                              | 1     |
| C     | char                              | 1     |
| N     | short, int                        | 2     |
| J     | long                              | 1     |
| T4    | month, date, minute, second, time | 5     |
| T8    | timestamp, timespan               | 2     |
| R     | real                              | 1     |
| F     | float                             | 1     |
| Z     | datetime                          | 1     |
| S     | symbol, guid                      | 2     |
| G     | general                           | 1     |

| code | verdict                                                                      |
|------|------------------------------------------------------------------------------|
| ok   | already covered: the kernel answers every `Enc.WF` payload of the type       |
| ext  | qlean must be extended; the item of section 2 is named                       |
| pre  | q rejects the input, so the op takes a precondition (approval Ap5, option M) |
| dec  | needs the user's decision; the letter of section 6 is named                  |

A layout changes the verdict only in the rows that name one. Everywhere else the cell holds at every layout
`Enc.WF` (`QLean/Value.lean` :930) admits for the type, as the `_isSome` theorems of
`leetq/LeetQ/Rel/KernelWF/Reduce.lean` already prove.

### 1.1 `scanColumn` (`Ops.scan`), `QLean/Kernel/Scan.lean` :711 over `scanWith` :676

What q answers is read off these qlean statements:

- typing of `sums`/`prds`: `Prim.running`, `QLean/Prim/Builtin.lean` :175. A vector answers its own type under
  `sums` when the type is temporal, else `promote t .int` (`Prim/Lattice.lean` :42), else `'type`.
- typing of `mins`/`maxs`: `Builtin1.apply`, `Builtin.lean` :268. `'type` on a vector of a `nonNumeric` type
  (`Lattice.lean` :87: guid, symbol), else the argument's own type.
- typing of `fills`: `Builtin1.apply`, `Builtin.lean` :193: the argument's own type at every type.
- values: `QLean/Dep/Scan.lean` `runScan` :151 (a null element leaves the running value), `Carrier.accum` :106,
  `Carrier.pick` :127, `accumulate` :224, `extremes` :243, `fills` :322, seeds `Carrier.bound` :83.
- a general list: `Prim.throughItems` (`Prim/Result.lean` :223) answers "any value"; the value is
  `Dep.scanItems` (`Dep/Scan.lean` :189) over `Eval.scanEach` (`Eval/Mon.lean` :2986), nothing skipped.

| verb           | types       | q answers              | kernel today             | verdict | cells |
|----------------|-------------|------------------------|--------------------------|---------|-------|
| `+` sums       | B Y N       | int                    | int                      | ok      | 4     |
| `+` sums       | J R F       | own type               | own type                 | ok      | 3     |
| `+` sums       | T4 T8 Z     | own type               | own type                 | ok      | 8     |
| `+` sums       | C           | `'type`                | none                     | pre     | 1     |
| `+` sums       | S           | `'type`                | none                     | pre     | 2     |
| `+` sums       | G           | any value              | none                     | dec A/B | 1     |
| `*` prds       | B Y N       | int                    | int                      | ok      | 4     |
| `*` prds       | J R F       | own type               | own type                 | ok      | 3     |
| `*` prds       | T4 T8 Z     | `'type`                | answers at rt = own type | pre     | 8     |
| `*` prds       | C           | `'type`                | none                     | pre     | 1     |
| `*` prds       | S           | `'type`                | none                     | pre     | 2     |
| `*` prds       | G           | any value              | none                     | dec A/B | 1     |
| `&` mins       | all but S G | own type               | own type                 | ok      | 16    |
| `&` mins       | S           | `'type`                | none                     | pre     | 2     |
| `&` mins       | G           | any value              | none                     | dec A/B | 1     |
| `\|` maxs      | all but S G | own type               | own type                 | ok      | 16    |
| `\|` maxs      | S           | `'type`                | none                     | pre     | 2     |
| `\|` maxs      | G           | any value              | none                     | dec A/B | 1     |
| `^` fills      | all but S G | own type               | own type                 | ok      | 16    |
| `^` fills      | S           | own type               | none                     | ext X6  | 2     |
| `^` fills      | G           | own type (general)     | none                     | dec A/B | 1     |
| other 15 dyads | every type  | no Dep-level statement | none                     | dec C/D | row   |

Totals: ok 70, pre 18, ext 2, dec 5, and one row for decision C/D.

Notes.
- `prds` at T4, T8, Z: `scanWith` compares only layouts (`outKind sv ek != rk`, :684), so a caller that passes
  `rt = t` gets an answer where q answers `'type`. The precondition must be `Prim.running`'s answer.
- The 15 other dyads are everything `Kernel.scanVerb` (:608) maps to `none`. qlean states `f\x` for them only in
  the interpreter's `iterate` (`Eval/Interp/Iterate.lean` :111) and, for a seeded scan, in `Dep.scanVerb`
  (`Dep/Scan.lean` :369, pairwise, no null skipped). There is no rank-1 typed reference to cite.

### 1.2 `overColumn` (`Ops.over`), `QLean/Kernel/Reduce.lean` :169

What q answers:

- `sum`, `min`, `max`: `Prim.aggregate`, `QLean/Prim/Monadic.lean` :29. `'type` at a `nonNumeric` type; `sum` at
  a non-temporal type answers `promote (if char then int else t) .int`; every other case its own type.
- `prd`: `Builtin1.apply .prd`, `Builtin.lean` :213. `'type` at `char`, at every temporal type and at a
  `nonNumeric` type; else `promote t .int`.
- `all`, `any`: `Builtin.lean` :202. `'type` at a `nonNumeric` type, else boolean; `q.k` spells them
  `min"b"` cast and `max"b"` cast (`Kernel/Coc.lean` :194, `Over.boolCast` :201).
- values: `Coc.Over.seed` :210 and `Over.step` :222; narrowing `Coc.narrowed` (`Reduce.lean` :129); the float
  folds `floatOver` :721 with seeds `Coc.Over.floatSeed` :356.
- one function already returns q's type for all six: `Coc.Over.resultType` (`Reduce.lean` :522). It is wrong in
  one place: `all`/`any` answer `boolean` at symbol and guid, where `Builtin.lean` :202 says `'type`.

| verb     | types             | q answers | kernel today               | verdict | cells |
|----------|-------------------|-----------|----------------------------|---------|-------|
| add      | B Y C N           | int       | Int64 of the int           | ok      | 5     |
| add      | J T4 T8           | own type  | Int64 of its payload       | ok      | 8     |
| add      | R F Z             | own type  | none (`overFloats` has it) | ext X1  | 3     |
| add      | S                 | `'type`   | none                       | pre     | 2     |
| add      | G                 | any value | none                       | dec A/B | 1     |
| mul      | B Y N             | int       | Int64 of the int           | ok      | 4     |
| mul      | J                 | long      | Int64                      | ok      | 1     |
| mul      | R F               | own type  | none (`overFloats` has it) | ext X1  | 2     |
| mul      | C T4 T8           | `'type`   | answers                    | pre     | 8     |
| mul      | Z                 | `'type`   | none                       | pre     | 1     |
| mul      | S                 | `'type`   | none                       | pre     | 2     |
| mul      | G                 | any value | none                       | dec A/B | 1     |
| lesser   | all but R F Z S G | own type  | Int64 of its payload       | ok      | 13    |
| lesser   | R F Z             | own type  | none (`overFloats` has it) | ext X1  | 3     |
| lesser   | S                 | `'type`   | none                       | pre     | 2     |
| lesser   | G                 | any value | none                       | dec A/B | 1     |
| greater  | all but R F Z S G | own type  | Int64 of its payload       | ok      | 13    |
| greater  | R F Z             | own type  | none (`overFloats` has it) | ext X1  | 3     |
| greater  | S                 | `'type`   | none                       | pre     | 2     |
| greater  | G                 | any value | none                       | dec A/B | 1     |
| all      | all but R F Z S G | boolean   | 0 or 1                     | ok      | 13    |
| all      | R F Z             | boolean   | none                       | ext X1  | 3     |
| all      | S                 | `'type`   | none                       | pre     | 2     |
| all      | G                 | any value | none                       | dec A/B | 1     |
| any      | all but R F Z S G | boolean   | 0 or 1                     | ok      | 13    |
| any      | R F Z             | boolean   | none                       | ext X1  | 3     |
| any      | S                 | `'type`   | none                       | pre     | 2     |
| any      | G                 | any value | none                       | dec A/B | 1     |
| any verb | Y C as `foR`      | as dense  | none                       | ext X2  | row   |
| any verb | R F Z as `foR`    | as dense  | none, in `floatOver` too   | ext X2  | row   |

Totals: ok 70, ext 17, pre 21, dec 6, and 5 layout rows (one per type) under X2.

Notes.
- `Enc.WF` admits `foR` at every fixed-width type but boolean and guid, so byte, char, real, float and datetime
  as `foR` are well-formed although `Enc.answer` (`Kernel/Coc.lean` :666) never writes them. `overColumn` has no
  arm for them (`Coc.nullOf` :63 is `none`), and `floatOver` ends in `| _ => none`.
- `sum` at a symbol column that carries the sorted mark is outside this table: leetq's `Arr` has no attribute.

### 1.3 `avgColumn` (`Ops.avg`), `QLean/Kernel/Scan.lean` :737

What q answers: `Monadic.apply .avg`, `Prim/Monadic.lean` :60: `'type` at a `nonNumeric` type, else a float atom;
a general list goes through `throughItems`. Values: `avgBits` (`Scan.lean` :330), `Eval.avgOf` (`Mon.lean` :427).

| verb | types       | q answers | kernel today | verdict | cells |
|------|-------------|-----------|--------------|---------|-------|
| avg  | all but S G | float     | float atom   | ok      | 16    |
| avg  | S           | `'type`   | none         | pre     | 2     |
| avg  | G           | any value | none         | dec A/B | 1     |

Totals: ok 16, pre 2, dec 1. No qlean change. `avgColumn_isSome` (`KernelWF/Reduce.lean` :586) already proves
the 16 at every layout; its hypothesis `hn : n < USize.size` does not appear in its proof body and is to be
dropped after one compile confirms that.

### 1.4 `groupedOver` (`Ops.overBy`), `QLean/Kernel/Reduce.lean` :539

`Ops.overBy` calls it at `avg := false`, `whole := false`, `Groups.segs`, order `tilLongs g`. What q answers per
group is the same typing as 1.2 (`Coc.Over.resultType` :522; `Eval/Interp/SelectBy.lean` `groupedColumn` :54
applies it to a group). Values: the header comment "The grouped reduction" (`Reduce.lean` :192-208, measured
against q 4.1), `overGroups` :221, `overGroupsFloat` :458, `groupCells` :503.

qlean has no statement of q's grouped `all`/`any`, and none of a grouped fold over a boolean column:
`groupedColumn` offers only `sum avg prd min max` and `segmentsEach` (:86) declines boolean. The cells below
take the ungrouped typing for them; the values need a q probe before the extension is believed.

| verb    | types             | q answers | kernel today                  | verdict | cells |
|---------|-------------------|-----------|-------------------------------|---------|-------|
| add     | Y C N J T4 T8     | as 1.2    | cells at q's type             | ok      | 12    |
| add     | R F               | own type  | cells at q's type             | ok      | 2     |
| add     | B                 | int       | none                          | ext X3  | 1     |
| add     | Z                 | datetime  | none                          | ext X3  | 1     |
| add     | S                 | `'type`   | none                          | pre     | 2     |
| add     | G                 | any value | none                          | dec A/B | 1     |
| mul     | Y N J R F         | as 1.2    | cells at q's type             | ok      | 6     |
| mul     | B                 | int       | none                          | ext X3  | 1     |
| mul     | C T4 T8 Z         | `'type`   | none (`resultType`)           | pre     | 9     |
| mul     | S                 | `'type`   | none                          | pre     | 2     |
| mul     | G                 | any value | none                          | dec A/B | 1     |
| lesser  | Y C N J T4 T8 R F | own type  | cells at q's type             | ok      | 14    |
| lesser  | B                 | boolean   | none                          | ext X3  | 1     |
| lesser  | Z                 | datetime  | none                          | ext X3  | 1     |
| lesser  | S                 | `'type`   | none                          | pre     | 2     |
| lesser  | G                 | any value | none                          | dec A/B | 1     |
| greater | Y C N J T4 T8 R F | own type  | cells at q's type             | ok      | 14    |
| greater | B                 | boolean   | none                          | ext X3  | 1     |
| greater | Z                 | datetime  | none                          | ext X3  | 1     |
| greater | S                 | `'type`   | none                          | pre     | 2     |
| greater | G                 | any value | none                          | dec A/B | 1     |
| all     | Y C N J T4 T8     | boolean   | 1-byte cells, op answers none | ext X3  | 12    |
| all     | B R F Z           | boolean   | none                          | ext X3  | 4     |
| all     | S                 | `'type`   | none                          | pre     | 2     |
| all     | G                 | any value | none                          | dec A/B | 1     |
| any     | Y C N J T4 T8     | boolean   | 1-byte cells, op answers none | ext X3  | 12    |
| any     | B R F Z           | boolean   | none                          | ext X3  | 4     |
| any     | S                 | `'type`   | none                          | pre     | 2     |
| any     | G                 | any value | none                          | dec A/B | 1     |

Totals: ok 48, ext 39, pre 21, dec 6.

Notes.
- `all`/`any` at an integral type: `groupedOver` answers one byte per group and `resultType` says boolean, but a
  boolean column is a bitmap (`Enc.WF`: `.boolean, .bytes _ => False`), so `Arr.of` in `Ops.overBy` refuses it.
  That is why `groupedOver_wf` (:219) carries `hb : rt /= .boolean`.
- B: `overGroupsColumn` (:276) needs `Coc.denseNul` (:74, none at boolean) and `Enc.bytesOf` (none at `.bits`).
- Z: `groupedOver` tests `t == .float || t == .real` (:541), so datetime takes the integral branch and
  `denseNul` declines it.
- `mul` at a type q rejects is already declined, because `groupedOver` asks `resultType` first. That is the
  behaviour `overColumn` lacks.

### 1.5 `mwinColumn` (`Ops.mwin`), `QLean/Kernel/Scan.lean` :841

What q answers:

- typing: `Prim.window`, `Builtin.lean` :350. `mmax`/`mmin` answer the argument's own type, "guid and symbol
  included"; `mcount` answers int at every type; `msum` answers `arith .add t t` (`Prim/Dyadic.lean` :37) or
  `'type`; `mavg` and `mdev` answer float, `'type` at a `nonNumeric` type, and `mavg` alone `'type` at char.
- the same table as a function: `mwinType`, `Scan.lean` :804, "measured against q 4.1 at every type". It
  answers `none` at symbol and guid "even where q answers" and at `mdev` over char, where its own comment says
  q answers (`2 mdev "ab c"` is `0 0.5 33 33.5`).
- values: `mwinBits` :513, `mwinSumAt` :492, `mwinExt` :480, `MOp.better` :455, `MOp.seed` :467; the
  composition the kernel replaces is `movingWindow`, `Eval/Interp/Window.lean` :87.
- window `0`: the comment of `mwinColumn` (:839) says "`0 msum 1 2 3` is `0 0 0` and `0 mavg 1 2` is `0n 0n`".
  For the two extremes `Eval.windowExtreme` (`Mon.lean` :3004) applies the prior extreme zero times when
  `w <= 1`, so its answer at `w = 0` is the argument.

| verb                  | types         | q answers        | kernel today         | verdict | cells |
|-----------------------|---------------|------------------|----------------------|---------|-------|
| msum                  | all but C S G | `arith .add t t` | that type            | ok      | 15    |
| msum                  | C             | `'type`          | none                 | pre     | 1     |
| msum                  | S             | `'type`          | none                 | pre     | 2     |
| msum                  | G             | any value        | none                 | dec A/B | 1     |
| mcount                | all but S G   | int              | int                  | ok      | 16    |
| mcount                | S             | int              | none                 | ext X4  | 2     |
| mcount                | G             | any value        | none                 | dec A/B | 1     |
| mavg                  | all but C S G | float            | float                | ok      | 15    |
| mavg                  | C             | `'type`          | none                 | pre     | 1     |
| mavg                  | S             | `'type`          | none                 | pre     | 2     |
| mavg                  | G             | any value        | none                 | dec A/B | 1     |
| mdev                  | all but C S G | float            | float                | ok      | 15    |
| mdev                  | C             | float            | none                 | ext X4  | 1     |
| mdev                  | S             | `'type`          | none                 | pre     | 2     |
| mdev                  | G             | any value        | none                 | dec A/B | 1     |
| mmin                  | all but S G   | own type         | own type             | ok      | 16    |
| mmin                  | S             | own type         | none                 | dec E/F | 2     |
| mmin                  | G             | any value        | none                 | dec A/B | 1     |
| mmax                  | all but S G   | own type         | own type             | ok      | 16    |
| mmax                  | S             | own type         | none                 | dec E/F | 2     |
| mmax                  | G             | any value        | none                 | dec A/B | 1     |
| msum mcount mavg mdev | `w = 0`       | zeros, `0n`      | none (`w < 1`, :846) | ext X5  | row   |
| mmin mmax             | `w = 0`       | the argument     | none (`w < 1`, :846) | ext X5  | row   |

Totals: ok 93, ext 3, pre 8, dec 10, and 6 window rows (one per verb) under X5. `w : Nat` in `Ops.mwin`, so a
negative window is not an input.

### 1.6 Count per verdict

| kernel        | ok  | ext | pre | dec | cells | extra rows  |
|---------------|-----|-----|-----|-----|-------|-------------|
| `scanColumn`  | 70  | 2   | 18  | 5   | 95    | 1 (dec C/D) |
| `overColumn`  | 70  | 17  | 21  | 6   | 114   | 5 (ext X2)  |
| `avgColumn`   | 16  | 0   | 2   | 1   | 19    | 0           |
| `groupedOver` | 48  | 39  | 21  | 6   | 114   | 0           |
| `mwinColumn`  | 93  | 3   | 8   | 10  | 114   | 6 (ext X5)  |
| total         | 297 | 61  | 70  | 28  | 456   | 12          |

The 28 `dec` cells are 24 general-list cells (decision A/B) and 4 `mmin`/`mmax` cells at symbol and guid
(decision E/F).

## 2. The extensions

Rule for all of them: a dispatcher declines by TYPE only, at the types q rejects, and never by layout. Its last
arm decodes through `Enc.bytesOf` (`Kernel/Coc.lean` :598) and runs the dense pass; it is not `none`. Every item
below is an instance of that rule or of "compose the kernel that already exists".

### 2.1 What qlean requires of any kernel change

qlean has no Makefile. The requirements are those of `AGENTS.md`, `CLAUDE.md` and `lakefile.lean` there.

| requirement         | what it means here                                                                          |
|---------------------|---------------------------------------------------------------------------------------------|
| build               | `lake build` clean, no `sorry`, no `unsafe`; it runs every `#guard` and `by decide`         |
| spec and C          | the Lean body is the spec, the `@[extern]` C is what runs; `decide` checks the first,       |
|                     | `#guard` the second, so each new cell needs a `#guard` (C) next to any `decide` (spec)      |
| family test module  | `QLean/Kernel/ReduceTest.lean` (28 `#guard`), `QLean/Kernel/ScanTest.lean` (210 `#guard`)   |
| claim set           | `QLean/Kernel/ClaimsTest.lean` writes down each dispatcher's claimed set and `#guard`s it;  |
|                     | a grown claim set is edited there in the same change                                        |
| differential corpus | `QLean/Eval/TestCorpus.lean` (`scanWindowCorpus`), `test/corpus/*.q`, `test/prim/*.txt`;    |
|                     | run by `./.lake/build/bin/qlean-test` against a live q 4.1                                  |
| q probe             | "probe q, never guess": a cell whose q answer is not already written in qlean is probed;    |
|                     | `q tools/licence-check.q` says whether q can run (it needs the licence daemon)              |
| benchmarks          | `tools/bench-matrix.txt` gets a row per new claimed cell; `tools/check-bench-coverage.py`   |
|                     | must stay at 99 % or above; `tools/bench-matrix.py` runs it                                 |
| no boxing           | "never box a whole column": an extension reads the payload in place or through `bytesOf`    |
| shared files        | `QLean/Value.lean`, `Wire/Tags.lean`, `QLean.lean`, `Test.lean`, `lakefile.lean` are edited |
|                     | only when assigned; none of the items below needs them                                      |
| correctness theorem | none is required and none exists: no kernel is proved against `Dep`. What exists is shape   |
|                     | theorems (`scanColumn_bytes`, `mwinColumn_bytes`, `avgColumn_type`, `overFloats_type`) and  |
|                     | `QLean/Verify/ScanOver.lean`. A changed dispatcher keeps its shape theorem green            |

### 2.2 Items

| item | cells                             | where it declines today                               | C   |
|------|-----------------------------------|-------------------------------------------------------|-----|
| X1   | 17 `overColumn` cells at R F Z    | `Reduce.lean` :189 `\| _ => none`; `Coc.denseNul` :74 | no  |
| X2   | 5 layout rows, Y C R F Z as `foR` | `Reduce.lean` :189; `floatOver` :721 `\| _ => none`   | no  |
| X3   | 39 `groupedOver` cells            | `Reduce.lean` :541 `flt`; `overGroupsColumn` :276     | no  |
| X4   | `mcount` at S, `mdev` at C        | `mwinType` :804; `MOp.readKind` :439                  | no  |
| X5   | 6 window rows, `w = 0`            | `mwinColumn` :846 `if w < 1 \|\| ...`                 | no* |
| X6   | `fills` at symbol and guid        | `scanKind` :625 answers `none`                        | yes |

`no*`: no C change is expected, but the C has never run at `w = 0`; see X5.

**X1. One fold entry for all six verbs at every type q accepts.** New dispatcher in `Kernel/Reduce.lean`,
proposed `overAtom (op : Coc.Over) (t : QAtomicType) (n : Nat) (e : Enc) : Option QAtom`:

- `rt <- op.resultType false t` (declines exactly q's `'type` cells once `resultType` is corrected, below);
- `add mul lesser greater`: `overColumn op t n e` then `atomOfInt rt`, else `overFloats op t rt n e` (:732). This
  is the body `Eval.sum` (`Eval/Mon.lean` :325), `Eval.prd` (:344) and `Eval.extreme` (:397) each spell out; they
  are rewritten to call `overAtom`, so the composition has one copy;
- `all any` at R F Z: `castColumn .boolean t n e` (`Elementwise.lean` :1927, `x <> 0` into a bitmap) then
  `overColumn op .boolean`. The interpreter today falls to a boxed `extreme (boolCast d)` (`Interp/Arms.lean`
  :565); it is rewritten to call `overAtom` too.
- `Coc.Over.resultType` (:522): the `all`/`any` arm ignores `t`. Change it to answer `none` at
  `Prim.nonNumeric t`, as `Builtin.lean` :202 states. This is a behaviour fix, not an extension.
- Tests: `ReduceTest` `#guard`s for 3 float types x 6 verbs, dense and `alp`; `ClaimsTest` set for `overAtom`;
  bench rows `sum`/`min`/`all` at float already exist for the evaluator path and need no new row if the
  coverage check still passes.

**X2. Layout arms.** `overColumn`: replace `| _ => none` by an arm that, when `clsOf t` and `Coc.denseNul t` are
`some`, folds `Enc.bytesOf t n e`. `floatOver`: the same with `floatOverDense`. Both reuse the dense pass
already called for `.bytes`. Tests: one `#guard` per type with a hand-built `foR` payload, since `Enc.answer`
never writes one.

**X3. `groupedOver` total on q's typing.** All in `Kernel/Reduce.lean`, reusing `overGroupsFloat` (:458),
`overSegmentsFloat` (:479), `overGroupsColumn` (:276) and `castColumn`:

- Z: `flt := Column.alpEncodes t` (`Coc.lean` :577: real, float, datetime) in place of the two-type test.
- B as input: `castColumn .byte .boolean` gives a dense byte column of 0/1; fold at `.byte`. The byte seeds
  (255 for `lesser`, 0 for `greater`) give `min` of an empty group `1b` and `max` `0b`; the int seeds would not.
  `add`/`mul` answer int, as `resultType` already says for boolean.
- R F Z under `all`/`any`: `castColumn .boolean t` first, then the boolean path.
- a boolean result (`all`/`any` at any type, `lesser`/`greater` at B): the byte cells are packed by
  `castColumn .boolean .byte g (.bytes s)`. So the result type changes from `Option ByteArray` to `Option Enc`
  (approval S5). `Interp/SelectBy.lean` `groupedColumn` (:75) wraps the answer with `QValue.ofBytes rt` and must
  take the `Enc` instead.
- Tests: `ReduceTest` `#guard`s for datetime x 3, boolean x 6, `all`/`any` x 4 type classes, each with an empty
  group; a q probe of grouped `all`/`any` and of a grouped fold over booleans (qlean has no statement; if q
  cannot be run, the cells are marked "unprobed" in `ReduceTest` and in this plan, not "verified").
- Verify before relying on it: `castColumn .byte .boolean` and `castColumn .boolean .byte` both answer (the doc
  comment says a boolean source is promoted to int first); one `#guard` each.

**X4. Two `mwinType` cells.**

- `mdev` at char: `mwinType .mdev .char = some .float`; `MOp.readKind .mdev k = k.raw` so the bytes are read as
  `u8`. The kind is passed to C from Lean, so no C change is expected. `#guard` against the value the comment
  records, `2 mdev "ab c"` is `0 0.5 33 33.5`.
- `mcount` at symbol and guid: compose `monColumn "null"` (`Elementwise.lean` :2156, claimed at guid and symbol,
  answers a bitmap), negate, then `mwinColumn .msum .boolean`, which answers int. `#guard` against the comment's
  ``2 mcount `a`b``c`` is `1 2 1 1i`.

**X5. Window `0`.** Lift `w < 1` from the guard of `mwinColumn`.

- `msum mcount mavg mdev`: the Lean spec at `w = 0` already gives q's stated answers (`mwinSumAt` :492 subtracts
  the same prefix total; `mwinBits` :513 divides 0 by 0 into `0n`). The C (`c/scan.c` `qlean_mwin` :1178) has
  never been called with 0; `#guard` it for each layout before the guard is lifted. If the C reads out of range
  at 0, the fix is in `c/scan.c` and the item grows.
- `mmin mmax`: `mwinExt` (:480) at `w = 0` reads `rd (i+1)`, which is wrong, and at `w = 1` is the identity. Call
  it with `max w 1`, which matches `Eval.windowExtreme`. q's own answer to `0 mmax x` is not written anywhere in
  qlean: probe it.

**X6. `fills` over symbol and guid (decision G/H).** `scanKind` answers `none` for both. A guid column is 16-byte
cells with the all-zero cell null; a symbol column is `syms`/`enum` with id 0 (or the empty symbol) null. This
is new C in `c/scan.c` (one forward pass per layout: `bytes` at 16, `syms`, `enum`), a new `Kind` or a separate
entry beside `scanWith`, `ScanTest` `#guard`s, a `ClaimsTest` set and bench rows. It is the only item that is
real kernel work.

### 2.3 leetq theorems that weaken or break

All in `leetq/LeetQ/Rel/KernelWF/Reduce.lean`. Each `unfold`s the dispatcher it is about, so any change to that
dispatcher's body breaks the proof even where the statement survives.

| theorem                       | line | item  | effect                                                  |
|-------------------------------|------|-------|---------------------------------------------------------|
| `overColumn_isSome`           | :166 | X2    | re-prove; the `.bytes`-only disjunct for Y C is dropped |
| new `overAtom_isSome`         |      | X1    | only hypothesis: `op.resultType false t = some rt`      |
| `resultType_width`, `_float`  | :180 | X1    | re-prove by cases after the `all`/`any` fix             |
| `groupedOver_isSome`          | :204 | X3    | `ht` (the type disjunction) is dropped; `hn`, `hw` stay |
| `groupedOver_wf`              | :219 | X3    | `hb : rt /= .boolean` is dropped; states an `Enc`       |
| `groupedOver_tilLongs_wf`     | :254 | X3    | follows `groupedOver_wf`                                |
| `groupCells_size`             | :192 | X3    | survives; a size lemma for the packed bitmap is added   |
| `mwinType_boolean`, `_layout` | :619 | X4    | re-prove by `cases op <;> cases t` (2 new cells)        |
| `readKind_width`, `_bit`      | :613 | X4    | re-prove after the `mdev` arm                           |
| `mwinColumn_isSome`           | :631 | X4 X5 | `hw1 : 1 <= w` is dropped; `mcount` branch for S added  |
| `mwinColumn_wf`               | :660 | X4 X5 | re-prove                                                |
| `scanColumn_isSome`           | :560 | X6    | `hk`, `hr`, `hc` become one typing hypothesis (S1)      |
| `scanColumn_wf`               | :489 | X6    | new branch for `syms`, `enum`, 16-byte payloads         |
| `avgColumn_isSome`            | :586 | none  | drop the unused `hn`                                    |

New lemmas leetq does not have yet: `castColumn_isSome` and `castColumn_wf` at the three casts X1 and X3 use,
`overFloats_isSome`, and `monColumn "null"` at symbol/guid (`KernelWF/Dyad.lean` :588 has `monColumn_isSome`;
check that its hypotheses admit `"null"` at those types).

Downstream of the five ops, every theorem phrased `h : Ops.x ... = some y` is restated without the `some`:
`LeetQ/Rel/Scan.lean` :509-1563 (`over_bytes`, `overBy_bytes`, `scan_toList`, `scan_toList_float`, `over_foR`,
`over_long`, `avg_bytes`, `avg_long`, `sum_float`, `avg_float`, `mwin_long`, `mwin_float`, `mwin_answer_of`,
`mwin_answer`, the `m*_toList` family), `LeetQ/Rel/SpecScan.lean` :606-1173 (14 theorems),
`LeetQ/Rel/Prog.lean` :36, :1277, :1844-1848, `LeetQ/Rel/Struct.lean` :340 (`wj`), `Bench/Main.lean` :197-220.

## 3. leetq signatures that need approval

Under Ap7 option S the ops answer bare, and under Ap5 option M the precondition is a decidable argument. The
precondition proposed for every op is q's typing rule as qlean states it, so that `KernelWF` proves
"rule implies `isSome`" with no residue about layouts or kernel kinds.

```lean
-- S1  Ops.scan      today:    (f : Prim.Dyadic) (rt : QAtomicType) (R : Arr t n) : Option (Arr rt n)
--                   proposed: (v : Scan.Verb) (R : Arr t n) (h : scanType v t = some rt) : Arr rt n
-- S2  Ops.over      today:    (op : Coc.Over) (R : Arr t n) : Option Int64
--                   proposed: (op : Coc.Over) (R : Arr t n) (h : op.resultType false t = some rt) : El rt
-- S3  Ops.avg       today:    (R : Arr t n) : Option UInt64
--                   proposed: (R : Arr t n) (h : avgType t = some .float) : El .float
-- S4  Ops.overBy    today:    (op : Coc.Over) (P : Parted t) : Option ((rt : QAtomicType) × Arr rt P.g)
--                   proposed: (op : Coc.Over) (P : Parted t) (h : op.resultType false t = some rt) : Arr rt P.g
-- S5  groupedOver   today:    ... : Option ByteArray      (qlean)
--                   proposed: ... : Option Enc            (qlean; a boolean answer is a bitmap)
-- S6  Ops.mwin      today:    (op : Scan.MOp) (w : Nat) (rt : QAtomicType) (R : Arr t n) : Option (Arr rt n)
--                   proposed: (op : Scan.MOp) (w : Nat) (R : Arr t n) (h : mwinType op t = some rt) : Arr rt n
```

- `El rt` stands for whatever leetq already uses for one element of an `Arr rt` (the `Carrier` value); no new
  type is proposed. If the user prefers the raw word, S2 is `UInt64` bits plus `rt` from the witness.
- `scanType` and `avgType` are not new semantics: `scanType v t` is the vector answer of `Builtin1.apply` at
  `sums prds mins maxs fills` (`Builtin.lean` :191), `avgType` that of `Monadic.apply .avg`. They are stated in
  qlean next to `mwinType`, which already has this form, and each gets the `decide` that ties it to `Prim`.
- S1 narrows the verb from the 20 `Prim.Dyadic` to the 5 `Scan.Verb` (decision C/D). `Spec.verb` (`Scan.lean`
  :330) and `Spec.kern` (:348) go with it.
- S4 removes the sigma: `rt` is read from the witness, as in S2.
- Callers decide the witness at the call site (Ap2 option D): each is `by decide` at a concrete type.
- `Ops.lastBy` (:102) calls `overColumn .lesser .long`; it is covered today and keeps its own Ap5 precondition
  (non-empty groups). It is not one of the five.

## 4. Packages

At most two kernels each. qlean packages come first; a leetq package starts when the qlean branch it names is
merged or reachable through `-K qlean=`.

| pkg | repo  | kernels or ops                      | items                        | needs               |
|-----|-------|-------------------------------------|------------------------------|---------------------|
| P1  | qlean | `overColumn`, `groupedOver`         | X1 X2 X3, `resultType` fix   | S5, L/M             |
| P2  | qlean | `mwinColumn`, `scanColumn`          | X4 X5, `scanType`, `avgType` | none                |
| P3  | leetq | `overColumn`, `groupedOver` proofs  | 2.3 rows X1 X2 X3            | P1                  |
| P4  | leetq | `scanColumn`, `mwinColumn` proofs   | 2.3 rows X4 X5, `avgColumn`  | P2                  |
| P5  | leetq | `Ops.over`, `Ops.avg`, `Ops.overBy` | S2 S3 S4                     | P3, N/O             |
| P6  | leetq | `Ops.scan`, `Ops.mwin`              | S1 S6                        | P4, C/D, I/J/K, N/O |
| P7  | qlean | `scanColumn` at symbol, guid        | X6                           | G/H                 |

Owner files.

- P1: `QLean/Kernel/Reduce.lean`, `QLean/Kernel/ReduceTest.lean`, `QLean/Kernel/ClaimsTest.lean` (Reduce part),
  `QLean/Eval/Mon.lean` (`sum`, `prd`, `extreme`), `QLean/Eval/Interp/Arms.lean` (:565),
  `QLean/Eval/Interp/SelectBy.lean` (`groupedColumn`).
- P2: `QLean/Kernel/Scan.lean`, `QLean/Kernel/ScanTest.lean`, `QLean/Kernel/ClaimsTest.lean` (Scan part),
  `tools/bench-matrix.txt`.
- P3: `leetq/LeetQ/Rel/KernelWF/Reduce.lean` :158-260, plus the new cast lemmas beside `KernelWF/Dyad.lean`.
- P4: `leetq/LeetQ/Rel/KernelWF/Reduce.lean` :377-700.
- P5: `leetq/LeetQ/Rel/Scan.lean` :42-126 and the laws of those three ops, `SpecScan.lean`, `Struct.lean` :340,
  `Prog.lean`, `Bench/Main.lean` (`sumR`).
- P6: `leetq/LeetQ/Rel/Scan.lean` :36, :127 and their laws, `SpecScan.lean`, `Prog.lean`, `Bench/Main.lean`
  (`scanOp`, `mwinOp`).
- P7: `c/scan.c`, `QLean/Kernel/Scan.lean`, `ScanTest.lean`, `ClaimsTest.lean`, `tools/bench-matrix.txt`.

- P1 and P2 both edit `ClaimsTest.lean`, in different sections; they run in parallel worktrees and merge by hunk.
- P3 and P4 both edit `KernelWF/Reduce.lean`, in the disjoint line ranges given. P5 and P6 both edit
  `Rel/Scan.lean`, `SpecScan.lean`, `Prog.lean`, `Bench/Main.lean`, in different declarations; run P5 before P6
  if one agent at a time is preferred.
- `Ops.avg` has no qlean dependency beyond `avgType` (P2 states it; P5 can state it locally first).
- P7 is optional and independent; without it `fills` at symbol and guid stays outside `scanType`.

Gates.

| pkg      | gate                                                                                            |
|----------|-------------------------------------------------------------------------------------------------|
| P1 P2 P7 | in the qlean worktree: `lake build` (runs `#guard`s); `./.lake/build/bin/qlean-test` (needs q); |
|          | `python3 tools/check-bench-coverage.py`; `tools/bench-matrix.py` for the rows touched           |
| P3 P4    | `lake -K qlean=<qlean worktree> build LeetQ.Rel.KernelWF.Reduce`                                |
| P5 P6    | `lake -K qlean=<qlean worktree> build LeetQ` then `build Check` (red by design; the op's line   |
|          | must leave the list) and `build bench`                                                          |

Working beside other agents on qlean. `/home/dh/repo/qlean` is a shared checkout with about 70 worktrees;
nothing is edited there.

- one worktree per qlean package:
  `git -C /home/dh/repo/qlean worktree add --lock /data/tmp/qlean-kcov-p1 -b kcov-reduce a260b4e`
  (P2: `/data/tmp/qlean-kcov-p2`, `kcov-scan`), then `cp -a /home/dh/repo/qlean/.lake /data/tmp/qlean-kcov-p1/.lake`
  (reflink) before the first `lake` command; unlock as the agent's last step.
- leetq reads its qlean from `leetq/lakefile.lean`: `require qlean from (get_config? qlean |>.getD "../../qlean")`.
  A leetq agent passes `-K qlean=/data/tmp/qlean-kcov-p1` on every `lake` call; the dependency builds in that
  worktree's own `.lake`, so the shared checkout's build is untouched. P3-P6 need P1 and P2 in ONE qlean tree:
  merge both branches into a third worktree (`kcov`), or wait for both to land on qlean `master`.
- do not change the lakefile default; the `-K` option is the whole mechanism.
- a qlean branch merges to qlean `master` only with `qlean-test` green on a machine where q runs.

## 5. Size, and what is worse than "extend the kernel" suggests

Estimates, not measurements; nothing was compiled.

| pkg | qlean Lean | C       | tests              | leetq code | leetq proof | risk                             |
|-----|------------|---------|--------------------|------------|-------------|----------------------------------|
| P1  | 80-120     | 0       | 50-70 `#guard`     |            |             | q values of grouped `all`/`any`  |
| P2  | 40-70      | 0-40    | 30-40 `#guard`     |            |             | the C at `w = 0`                 |
| P3  |            |         |                    |            | 250-400     | proofs `unfold` rewritten bodies |
| P4  |            |         |                    |            | 150-250     | same                             |
| P5  |            |         |                    | 60-100     | 250-350     | 14 `SpecScan` theorems restated  |
| P6  |            |         |                    | 80-200     | 300-450     | decision I/J/K                   |
| P7  | 100-150    | 150-250 | 40 `#guard`, bench |            | 100-150     | unprobed payload conventions     |

Numbers are lines.

What is worse than expected.

1. **The count bound stays.** `scanColumn_isSome`, `groupedOver_isSome` and `mwinColumn_isSome` need
   `n < USize.size` because the kernels take `n.toUSize`, and `Arr t n` does not carry that bound. No type
   extension removes it. `Ops.scan`, `Ops.overBy` and `Ops.mwin` therefore still need an else-branch or a bound
   (decision I/J/K). `Ops.over` needs none, and `Ops.avg` none once `hn` is confirmed unused.
2. **q is needed to verify, and may not run.** The corpus gate needs the licence daemon. An agent without it can
   prove shapes and run `#guard`s against values already written in qlean, and nothing more. The cells with no
   qlean statement are: grouped `all`/`any`, grouped folds over boolean, `mmin`/`mmax` at `w = 0`, `mmin`/`mmax`
   at symbol/guid, `fills` at symbol/guid payload conventions.
3. **"Correct" means tested, not proved.** No kernel has a theorem against the `Dep` reference, so leetq's
   totality proofs say the op answers, and the spec theorems of `SpecScan` remain the only link to values.
4. **Proof churn is the larger half.** About 60 % of the lines are leetq proofs that break because they `unfold`
   a dispatcher body, plus theorems restated without `some`. The qlean diff itself is small.
5. **The kernel is not q's typing.** 20 cells answer where q rejects, and `resultType` is wrong for `all`/`any`
   at symbol and guid. A precondition copied from the claim set would have made those inputs legal.
6. **`Enc.WF` admits layouts qlean never writes** (`foR` at byte, char, real, float, datetime). They cannot be
   tested through q, only by hand-built payloads; narrowing `Enc.WF` instead is a `Value.lean` change, a shared
   file, and was not costed.
7. **Two of the five problems were never kernel gaps.** `Ops.over` at float and `Ops.overBy`'s boolean answers
   are leetq calling half of what the evaluator calls. X1 moves that composition into one qlean entry so it
   cannot be half-called again.

## 6. Decisions for the user

Each option has its own letter; the proposed one is marked.

- **General lists** (24 cells). q answers "any value", which is not an `Arr rt n`.
  - A (proposed): precondition `t /= .general`; it already follows from every typing rule of section 3.
  - B: a separate op over general lists, later.
- **`Ops.scan` at the 15 dyads `scanVerb` declines.** qlean has no typed rank-1 statement of `f\x` for them.
  - C (proposed): narrow the verb argument to `Scan.Verb` (S1).
  - D: keep `Prim.Dyadic` and first write that reference in qlean `Dep`.
- **`mmin`/`mmax` at symbol and guid** (4 cells). q answers; qlean states no value.
  - E (proposed): leave them outside `mwinType`, as its comment already does.
  - F: probe q and write new kernels.
- **`fills` at symbol and guid** (2 cells, X6). q answers; it needs new C.
  - G: do P7 now.
  - H (proposed): leave them outside `scanType`, say so in its comment, do P7 when a program needs it.
- **The count bound `n < USize.size`** in `scan`, `overBy`, `mwin`.
  - I (proposed): an else-branch that calls qlean's non-extern spec bodies at `Nat` counts (`Scan.intScan`,
    `Scan.fltScan`, `Scan.mwinBits`, `overGroups`), which already state q's arithmetic.
  - J: put the bound in `Arr` (a data-structure change).
  - K: kernels take the count as `Nat` (an ABI change across `c/scan.c` and `Coc.decode`).
- **Where the compositions of X1 and X3 live.**
  - L (proposed): in qlean (`overAtom`, `groupedOver`), and the evaluator calls them.
  - M: in leetq's ops, qlean untouched for those cells.
- **Signatures S1-S6** of section 3.
  - N (proposed): as written.
  - O: he names the changes.
- **Cells qlean cannot cite** (grouped `all`/`any`, grouped folds over boolean, `0 mmax x`).
  - P (proposed): the qlean package probes q and records the values; if q cannot run, the package stops there
    and reports, and the cells stay "unprobed".
  - Q: ship them on the ungrouped typing and the `#guard`s alone.

E and H leave 6 cells where q answers and the typing function says no. That is the only place the proposed
precondition is narrower than q.

C1 and D2 leave 6 cells where q answers and leetq's typing function says no; that is stated in the function's
comment and is the only place the precondition is narrower than q.
