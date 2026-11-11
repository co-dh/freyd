# leetq architecture steps 2, 4, 5: audit

Audit only, nothing performed. Steps named as in `doc/leetq-qlean-architecture.md`, "Plan". Counts read on branch
`leetq-gaps` (base `d862cff` plus the two gap fixes: `Vals.held`, `Ops.rank` without its `List` fallback, `colFn`
moved to `Core`). Every line number below is of that tree and moves with any edit to `Algebra.lean`.

## Who reaches what

- The four programs (`Blocks`, `BlocksRel`, `Chess`, `Circuit`, `Wumpus`) and the `.rel` front end
  (`Lang/Elab.lean`, through it `Eval`, `Test*`) import `LeetQ.Rel.Algebra` and nothing else of leetq. None of
  them names `Find.`, `Ew.`, `Ops.`, `Parted.`, `Spec.` or `KernelWF.`: they reach steps 2 and 4 only through the
  `Alg` ops they call.
- `Algebra.lean` imports `Find`, `Ew`, `Scan`, `Parted`, `KernelWF.Reduce`. What it actually uses of them:

| from                   | names `Algebra.lean` uses                                     | the `Alg` ops behind them                                          |
|------------------------|---------------------------------------------------------------|--------------------------------------------------------------------|
| `Find` (1750 lines)    | `expand`, `one` (opened), `Find.one`, `Find.bitsAt_one` (proof) | `expand`: `Vals.pick` (arr), `Obj.codes` (arr), `join` (so `≫`, `pair`, `⟨R,S⟩`), `mem`/`∋`, `cons`; `one`: `int`, `addc`/`mulc` callers, `cross` (`⊤`, `prod`), `setIds` (`Λ`), `Obj.codes` (arr), `shiftArr` (`Obj.raze` arr, so `∪`, `junc`) |
| `Ew` (499 lines)       | `Ew.notBits`                                                   | `Vals.pick` (sum), `anti` (`\`, `antiJoin`, `est`, `thin`)           |
| `Scan` (1701 lines)    | `Ops.rank` (with `rankAt`)                                     | `lt`, `leq` (Blocks `«≼»`, `δ`, `Blocks.plan`; Lang `<`, `≤`)        |
| `Parted` (79 lines)    | nothing                                                        | none                                                               |
| `KernelWF.Gather`      | `long_cases general_cases gatherColumn_isSome/_wf gatherBytes_size toNat_small` | `pick`, `gather`, `codes`: every op          |
| `KernelWF.Raze`        | `groupIdsColumn_isSome concatBits_wf tilLongs_wf Ew.val_size/_wf razeColumn_isSome/_wf concatBytes_size` | `raze` (`∪`, `junc`), `tags` (`inl inr junc sum`), `tilCol`, `codes` |
| `KernelWF.Reduce`      | `gradeColumn_isSome/_wf`, `razeColumn_count`                    | `Ops.rank` (`lt`), `Obj.sortBy` (`Λ`), `raze_len`                    |

(`Ew.cmp`, `Ew.val`, `Ew.add`, … in `Algebra.lean` are qlean's `QLean.Kernel.Ew`, not leetq's `Ew`.)

## Step 2: move what `Alg` uses into `Core`, delete `Find`/`Ew`/`Scan`/`Parted`/`QSort` and unreached `KernelWF/*`

Done on branch `leetq-arch-step2`. Differences from the plan below, found by the compiler:

- `Ops.rank`/`rankAt` cannot move into `Core`: they cite `gradeColumn_isSome/_wf`, whose proofs use `Raze`'s
  `wf_bytes`, `bytesOf_size`, `countFits_of_lt`, `orderKind_eq_none`, and `Raze` imports `Core`. They moved into
  `KernelWF/Reduce`, cut to the grade facts and `razeColumn_count` (727 → about 270 lines).
- `Core`'s `Cuts`, `cuts_of_ascending`, `cuts_get`, `Cuts.pos` and `Raze`'s `Parted.of?_isSome` served only
  `Parted`; deleted with it, with the five `Parted.of?` guards in `Core`.
- No other import was needed: `Algebra` imports `KernelWF.Gather` and `KernelWF.Reduce` in place of the four
  modules; `Core` gains `QLean.Kernel.Elementwise` and `QLean.Kernel.Scan` (for `expand`, `Ew.notBits`).

Moved into `Core` (a few dozen lines):

- `Find.one` (1 line), `Find.expand` (`Find.lean:158`, its doc and body), `Find.bitsAt_one` (`Find.lean:560`, the one
  lemma `Laws` cites), `Ew.notBits` (`Ew.lean:93`, 1 line), `Ops.rank` + `rankAt` (`Scan.lean:142-158`).
- `Ops.rank` needs `KernelWF.gradeColumn_isSome/_wf` (`KernelWF/Reduce.lean:79-125`); the rest of `Reduce` (`over`,
  `lastBy`, `ranks`, `sort`, `xasc` facts) serves only `Scan`, except `razeColumn_count` (`Reduce.lean:307`), which
  `raze_len` cites. Keep `Reduce` cut down to those, or move the three theorems next to `Gather`/`Raze`.

Deleted:

| module                         | lines | why it can go                                                         |
|--------------------------------|------:|-----------------------------------------------------------------------|
| `Find.lean`                    |  1750 | after the four names above move; its guards test kernel wrappers only |
| `Ew.lean`                      |   499 | after `notBits` moves; `Lift`, `dyad`, `Ew.align/dyadic/keyed` are q's ew verbs, answer `Except` |
| `Scan.lean`                    |  1701 | after `rank` moves; q's `mwin`, `over`, `grade`, `permute`, `xasc`, `Spec` |
| `Parted.lean`                  |    79 | no `Alg` user; `razeParts`/`ofBoxes` answer `Except`                   |
| `Core.lean` `Parted` structure |   ~45 | `Core.lean:519-552` and its guards `:675-688`; only `Parted.lean`/`Scan` read it |
| `QSort.lean`                   |   361 | imports only `Lean`; nothing imports it                               |
| `KernelWF/Dyad, Mon`           | 872   | reached only through `Ew`                                             |
| `KernelWF/DyadAtom, DyadCmpWF, DyadValWF, SearchSym` | 690 | reached by nothing (built only by the glob)         |
| `KernelWF/Search, Shape`       |  1212 | reached only through `Find` and `Parted`                              |

Kept: `KernelWF/Gather` (197), `KernelWF/Raze` (812), `KernelWF/Reduce` (cut, see above). Net about −7,900 lines.

- Dependents: no program and no `Lang/` file changes (none names the moved names); `Algebra.lean` changes its
  imports and its `open LeetQ.Rel.Find (expand one)` line, and `Find.one`/`Find.bitsAt_one` lose their prefix.
- Risk: low for the programs. The moved `expand` and `one` keep their names, so `Algebra.lean`'s body is unchanged
  apart from the prefixes; but the header (imports, `open`) is the hunk the parallel agent's `Algebra.lean` edits are
  least likely to touch, so it merges. A proof in `Laws` that relies on an instance or simp lemma imported
  transitively through `Find`/`Scan` (e.g. `QLean.Verify.*` modules they import) breaks; the fix is to import that
  qlean module directly. `rel`, the `.rel` interpreter, still builds since it reaches only `Algebra`.
- New type: none. One type is deleted (`Core`'s `Parted`).

## Step 4: kernel count theorems instead of reference implementations

Each `if h : <count check> then kernel else reference` site in `Algebra.lean` (all reached by the programs):

| site                          | line  | reference          | needs                                                                 | ops behind it |
|-------------------------------|------:|--------------------|-----------------------------------------------------------------------|---------------|
| `sliceIds`                    | 657   | `slicesRef`        | `rankSlices_size` (`KernelWF/Raze.lean:115`) premises: offsets from `sums` non-decreasing, last ≤ payload | `Obj.codes` (arr): `==`, `∩`, `∪`, `Λ` on array sides |
| `setIds`                      | 800   | `setIdsRef`        | the same premises for the gathered offsets                            | `Λ`, `E`, `P`, `symDiv` |
| `Vals.pick` (arr)             | 510   | `pickShared`       | `sums`/`sub` answer `len i` longs where `len i < USize.size`           | every op that picks rows of an array side |
| `Vals.pick` (sum)             | 521   | `y` (`pickShared`) | `sums`/`sub`/`add` sizes                                               | same, sum sides |
| `shiftArr`                    | 460   | `toList` + `col`   | `addc` size; this reference is a `List` in an implementation          | `Obj.raze` (arr): `∪`, `junc`, `nub` |
| `place`                       | 488   | `colFn`            | `Ew.val`/`add` sizes                                                  | `pick`/`raze`/`codes` on sums |
| `tilCol`                      | 469   | `colFn`            | none possible: past `USize.size` no kernel runs                        | `inl inr sumVals idU` |
| `Vals.compact`                | 534   | `x` itself         | `tilLongs` size (have `tilLongs_wf`)                                   | `uncons`, `Vals.held` |
| `Ops.rank` (moved by step 2)  | Scan  | `rankAt` + `colFn` | none possible past `USize.size`                                       | `lt`, `leq` |

- Deleted when the theorems land: `slicesRef` + `setIdsRef` + `setIdsRef_size` (`Algebra.lean:645-650, 775-780`,
  about 20 lines), `Vals.pickShared` (`:414-421`, 8 lines, but `pick` (sum) also uses it as its first step, so only
  the arr fallback goes), the `shiftArr` `List` branch (3 lines), the `place` reference (3 lines), and the guard
  `Algebra.lean:1609-1611` that compares `setIdsRef` with `setIds`.
- The `USize` sites (`tilCol`, `Ops.rank`, every `n.toUSize` in `Alg`) cannot be closed by a theorem: nothing in
  Lean bounds a `ByteArray`'s size. Either they keep a non-kernel `Arr` reference (as now: `colFn`), or `Arr` carries
  `n < USize.size`, which is a change of representation and needs the author's approval. Today most ops pass
  `n.toUSize` unchecked (`lt` passes `(n*n).toUSize`, wrong past `n ≥ 2³²` on a 64-bit machine), so the domain is
  already `n < USize.size` in fact.
- Dependents: all four programs and `Lang/` reach these sites through `≫`, `∪`, `Λ`, `==`; no signature changes, so
  none of them is edited.
- Risk: medium. The proofs are about `sums` and `rankSlices` on gathered offsets (`rankSlices_size` needs the offsets
  sorted and inside the payload, which for clamped slices needs a monotonicity lemma for `sums` of non-negative
  counts). A wrong proof cannot ship (it does not compile); the risk is effort, and that some site turns out to need
  the `USize` bound above.
- New type: none, unless the `USize` bound is put into `Arr` (then: approval).

## Step 5: split `Algebra.lean` (2214 lines) into `Code`, `Alg`, and the guards

DONE (branch `leetq-arch-step5`): `Code.lean` (codes, payload kernels, laws of codes), `Alg.lean` (operators, `conv_holds`), `AlgTest.lean` (guards); `Algebra.lean` is two imports; `le inter union conv comp diff lamOn nest` stay `private`, and the guards were rewritten with the operators `∩ ∪ ° ≫ \ ⊑` (the second option below). The `#print axioms` of `le inter union conv comp` moved to the end of `Alg.lean`, where they are visible.

| part                                            | lines        | count | goes to         |
|-------------------------------------------------|--------------|------:|-----------------|
| header, long payloads, `Code`, payload kernels, `Part`, `pick`/`raze`/`codes`, the composite steps (`join`, `cross`, `anti`, `setIds`) | 1-812 | ~812 | `Code.lean` |
| the operators (`section Gen`), order, power side, list functions, `Arr.sum`, the predicates | 814-1299 | ~486 | `Alg.lean` |
| `section Checks` (guards)                        | 1301-1796    |  ~496 | `AlgTest.lean`  |
| `#print axioms` of the ops                       | 1797-1834    |   ~38 | `AlgTest.lean`  |
| `section Laws` (codes faithful, ops mean their relation) and its `#print axioms` | 1835-2214 | ~380 | `Code.lean` (laws of codes) / `Alg.lean` (laws of ops) |

- Dependents: every program and `Lang/Elab.lean` import `LeetQ.Rel.Algebra`. Keeping `Algebra.lean` as a three-line
  file that imports `Code`, `Alg` and nothing else leaves all of them unedited; the guards file is imported by nobody.
- `private`: `le inter union conv comp diff` (`:821-885`) and `lamOn` (`:1219`) are private in `section Gen`, and the
  guards call `inter`, `union`, `conv`, `comp`, `diff` by name. A guard file of its own cannot see them: taken:
  the guards are rewritten with the operators (`∩ ∪ ° ≫ \ ⊑`), which stay the only spelling; `private` is kept so the
  `#guard_msgs` in `Blocks.lean` still hold. The `#guard_msgs` at `:1728` prints the parameter name `_h` of `lt` and must move unchanged.
- Risk: high only for collisions. Another agent appends ops to `Algebra.lean` now; a split moves every line, so its
  branch would merge as one conflict per hunk. Do step 5 when no other branch edits `Algebra.lean`, as one mechanical
  move (no body edits in the same commit), then build `LeetQ.Rel.Algebra LeetQ.Rel.Lang.Test rel` and the four
  `Lang/Test*` modules. Elaboration time improves: today any edit to a guard re-elaborates the 1300 lines of ops.
- New type: none.

## Order

Step 2 first (it shrinks `Algebra.lean`'s imports and touches only its header), step 5 when no branch edits
`Algebra.lean`, step 4 last (its proofs land in `Code.lean` after the split, a smaller file to rebuild).
