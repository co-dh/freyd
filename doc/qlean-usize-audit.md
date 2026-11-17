# qlean USize-count audit (branch `usize-count`, worktree `/data/tmp/qlean-usize`, base 8ba72f8)

The rule audited: no `Nat` count in executable qlean code. A count is `USize`; `Nat` is reached only by `n.toNat` in
models and statements; a count from a Lean `Array`/`ByteArray`/`List` size enters through `Kernel.needSize` (or
`QValue.ofArray`, or `asCount` in tests); `Nat.toUSize` is never glue on a count.

Kinds used below, per `toUSize` site (one line may hold several; it is counted under the kind of its count argument):

| kind | meaning                                                                         | verdict   |
|------|---------------------------------------------------------------------------------|-----------|
| a    | width, bit width, byte position/offset, shift, literal, `UInt32.toUSize`        | fine      |
| b    | inside the Lean model of an `@[extern]`, or in a theorem statement/proof        | fine      |
| c    | a Lean size (`xs.size`, `l.length`, `b.size / w`) used as a count               | violation |
| d    | a `Nat` binder holding a count, converted at use                                | violation |
| e    | a hand-written `need (c < USize.size) … c.toUSize`: `needSize` spelled out       | DRY       |
| f    | a count read out of an extern C-ABI `Array Nat` (third list below)              | open      |

Total before: 383 `toUSize` lines in `QLean/` and `tools/`.

## Kernel

| file                  | a  | b | c | d | e | f | notes                                                                    |
|-----------------------|----|---|---|---|---|---|--------------------------------------------------------------------------|
| Kernel/Search.lean    | 22 | 8 | 4 | 0 | 2 | 0 | c: `(ko.size - 1).toUSize` at 980, 1190, 1314, 1315 (symbol-key count)   |
| Kernel/Structural.lean| 18 | 2 | 0 | 0 | 0 | 3 | f: `p.1.1.toUSize` (396, 398), `ns[k]!.toUSize` (644)                    |
| Kernel/Sort.lean      | 15 | 2 | 0 | 0 | 0 | 0 | b: `distinctFoR`/`distinctALP` models; a: `k.width`, `idWidth` widths    |
| Kernel/Elementwise.lean| 12| 0 | 0 | 0 | 0 | 0 | all `(width cls).toUSize`, `idWidth`                                     |
| Kernel/Index.lean     | 7  | 0 | 0 | 0 | 0 | 0 | widths; 299 `word … j` are row positions                                 |
| Kernel/Coc.lean       | 4  | 2 | 0 | 0 | 0 | 0 | b: `countLt`, `popcount` models                                          |
| Kernel/Reduce.lean    | 1  | 0 | 0 | 0 | 4 | 0 | e: `Groups.count`, `overSegments`, float twin (490), `alpLive`           |
| Kernel/Scan.lean      | 2  | 0 | 0 | 0 | 0 | 0 |                                                                          |
| Kernel/Need.lean      | 0  | 1 | 0 | 0 | 0 | 0 | `needSize` itself: the one sanctioned `toUSize` on a count               |
| Kernel/TestChecks.lean| 2  | 0 | 0 | 0 | 0 | 0 |                                                                          |
| Value.lean            | 0  | 3 | 0 | 0 | 3 | 0 | e: `QValue.ofArray` (460), `sliceAt` (2343), `ofBytes` (2401)            |

## Eval

| file                     | a | b | c | d | e | f | notes                                                         |
|--------------------------|---|---|---|---|---|---|---------------------------------------------------------------|
| Eval/Dyad.lean           | 6 | 0 | 0 | 0 | 0 | 0 | 2734 `p`, `span` are row positions; rest widths               |
| Eval/Interp/Amend.lean   | 5 | 0 | 0 | 0 | 0 | 0 |                                                               |
| Eval/Interp/AmendAt.lean | 1 | 0 | 0 | 0 | 0 | 0 |                                                               |
| Eval/Interp/Iterate.lean | 1 | 0 | 0 | 0 | 0 | 0 |                                                               |
| Eval/Interp/SelectBy.lean| 2 | 0 | 0 | 0 | 0 | 0 | `idWidthOf` result is a width                                 |
| Eval/Interp/Qsql.lean    | 1 | 0 | 0 | 0 | 0 | 0 | `idWidthOf ng.toNat` result is a width                        |
| Eval/Interp/Core.lean    | 0 | 0 | 0 | 2 | 0 | 0 | d: `QIO.fileParts`' `count : Nat`; `OwnFile.count : Nat`      |

## Wire, Db, Dep

| file              | a | b | c | d | e | f | notes                                                                   |
|-------------------|---|---|---|---|---|---|-------------------------------------------------------------------------|
| Wire/Decode.lean  | 3 | 0 | 0 | 0 | 0 | 0 | 141 a byte start; 241, 289 are `UInt32.toUSize`, not `Nat`             |
| Db/Splayed.lean   | 1 | 0 | 1 | 0 | 0 | 0 | c: `d.syms.size.toUSize` (147); `nullId` is a position                  |
| Db/ObjectFile.lean| 0 | 0 | 1 | 1 | 0 | 0 | c: `bytes.size.toUSize` as `symOffs`' count bound; d: `Files.parts`     |
| Db/Own.lean       | 0 | 0 | 1 | 0 | 0 | 0 | c: `dictOffs`' `dict.size.toUSize` as `symOffs`' count bound            |
| Db/Test.lean      | 0 | 0 | 0 | 1 | 0 | 0 | d: `OwnFile.count`                                                      |
| Dep/Val.lean      | 0 | 1 | 0 | 0 | 0 | 0 | statement                                                               |

## Verify

All 26 files with `toUSize` (EwEnc 18, FindMember 14, BinWin 14, Group 13, AlpConcat 13, Alp 11, SymFind 9, Gather 9,
ScanOver 7, Encoding 7, Assign 7, Search 6, Dyad 6, Identical 5, Codes 5, Ids 3, Distinct 3, Amend 3, Raw 2,
Grade 1): kind b, theorem statements and proofs. One exception, `Verify/Search.lean:388`, is a `#guard` whose
`w.toUSize` is a width (a).

## Tests and tools

| file                         | a | c | d  | notes                                                            |
|------------------------------|---|---|----|------------------------------------------------------------------|
| Kernel/SortTest.lean         | 5 | 2 | 14 | d: `n`, `d` binders of the `#guard` helpers; c: `xs.length`      |
| Kernel/ElementwiseTest.lean  | 0 | 0 | 13 | d: `chainN`, `sliceN`                                            |
| Kernel/StructuralTest.lean   | 0 | 2 | 6  | d: `n` (754, 1222–1252); c: `xs.length`, `vs.length`             |
| Kernel/ScanTest.lean         | 0 | 6 | 0  | c: `xs.length`, `bs.length`                                      |
| Kernel/SearchTest.lean       | 1 | 2 | 1  | d: `rampTo n`; c: `hay.length`, `ndl.length`                     |
| Kernel/ReduceTest.lean       | 4 | 0 | 0  | `gw`, `idWidthOf` widths                                         |
| Kernel/Test.lean             | 0 | 0 | 1  | d: `nb`                                                          |
| Db/Test.lean                 | 0 | 0 | 1  | `OwnFile.count` (listed under Db)                                |
| tools/need-test.lean         | 0 | 0 | 2  | d: the CLI's `n m`                                               |
| tools/bench-kernel.lean      | 2 | 0 | 20 | d: `n`, `d` (not built by the gate)                              |

## Library functions and fields that take or return a `Nat` count

| declaration                                   | verdict                                                                  |
|-----------------------------------------------|--------------------------------------------------------------------------|
| `Enc.dense (n : Nat) : Nat × Enc`             | count, must change (Verify states things about it: done last)           |
| `Enc.atoms`, `Enc.raw`, `Enc.blobOf (n : Nat)`| count, must change (same)                                                |
| `Db.OwnFile.count : Nat`                      | count, must change                                                       |
| `Db.Files.parts`, `QIO.fileParts` `count`     | count, must change (`start`, `width` are a byte position and a width)    |
| `Db.dictOffs`, `ObjectFile` `symOffs` bound   | count bound from a `ByteArray` size, must enter through `needSize`       |
| `Wire.Encode.vectorBody` returned count       | count, must change (the wire count is checked against `uint32` in `Nat`) |
| `Kernel.Index.pairIds (k : Nat)`              | a group count used as a multiplier, must change                          |
| `Eval.Dyad.partGroups (nr nl : Nat)`          | counts, must change (fed `nr.toNat` by `keyMatch`)                       |
| `Eval.Dyad.keyMatch` `let (nr, nl) := (…toNat)`| shadows its `USize` counts with `Nat`; goes with `partGroups`           |
| `Eval.Dyad.ffColumn (nr : Nat)`               | count, must change (fed `nr.toNat`)                                      |
| `Eval.Dyad.keyGroups (n : Nat)`               | count, fed `nr`/`n.toNat`; goes with `partGroups`                        |
| `Eval.Dyad.divModPairs (n : Nat)`             | count, fed `xs.size` of a Lean array: should enter through `needSize`    |
| `Kernel.worthHalving (n m : Nat)`             | counts, fed `.toNat`; a pure heuristic                                    |
| `Kernel.Coc.foRStd (n : Nat)`, `Structural.appendFoR`, `reverseMoveFoR` | counts, fed `.toNat`; `foRStd` is stated in `Verify.foRStd_iff` |
| `Column.idWidthOf (nd : Nat) : Nat`           | stays: a width function of the dictionary size `idWidth` states in `Nat`; executable callers pass `.toNat` and its result is a width |
| `Eval.Dyad.groupIds (ng : Nat)`               | stays: `ng` is the fill id written into the answer, a value              |
| `Kernel.Reduce.segRange (n r : Nat)`, `sumF64Total`, `sumF32Total`, `laneSum32`, `Scan.scanOf`/`intScan`/`fltScan`, `Sort.firstsBy`/`idsBy`/`bucket`/`runHeads`, `Search.gatherAt`/`findSortedAt`, `Structural.packOf`/`cycleBytes`/`shiftAt` | stay: loop bounds and positions inside extern models |
| `Eval.Interp.Random.dealBelow (n bound : Nat)`, `Eval.Val` `items (n : Nat)`, `Dyad.partitionAt`, `Dyad.search`, `Dyad.seq` | unclassified: Nat from a q long or a Lean size, fed `.toNat`; to check |
| `Wire.Decode.takeBytes (n : Nat)`, `many (n fuel : Nat)` | stays: byte length and decoded element count bounded by `uint32` before |
| Dep's type indices (`Table (n : Nat)`, `Sized`, `Columns`, `Know.len`) | stay: type-level lengths                              |

## Left as `Nat` on purpose: extern C-ABI `Array Nat` (open decision for the user)

| extern input / answer                                 | callers that convert                                             |
|-------------------------------------------------------|------------------------------------------------------------------|
| `concatFoR`/`concatALP` `ns : Array Nat`              | `Structural` 1240–1262 (`#[n.toNat, tn.toNat]`), `encodedParts`  |
| `concatEnum`, `hashConcat` counts                     | `Structural` concat arms                                         |
| `spreadBytes widths : Array Nat`                      | `expandColumn`                                                   |
| `stringDigits`/`splitBytes` answers                   | their callers read sizes back as `Nat`                           |
| `hashSyms`/`findSyms` `offs : Array Nat`              | `Search` symbol arms (`ko.size - 1` is the count)                |
| `distinctFoR`/`distinctALP` return `Nat × …`          | `Sort` distinct arms                                             |
| `razeColumn`/`encodedParts` `cs : Array (Nat × Enc)`  | `Structural` 396, 398, 644 `toUSize` (kind f)                    |

Changing these to `Array USize` changes the C side (`c/*.c` unboxes a `Nat` per element today).

## C-ABI count lists (Q55, worktree `/data/tmp/qlean-usize-abi`, branch `usize-abi`, base 56a250f)

Design (user's decision: a count list across the C ABI is a `ByteArray` of 8-byte LE counts):
- Accessors reused, no new type: count `i` of `cs : ByteArray` is `(Column.bitsAt cs (8 * i) 8)` (read as `.toUSize`
  in executable code, `.toNat` in statements); a list is built by `Column.pushBits acc n.toUInt64 8` per count. In C
  the list is `(const uint64_t *)lean_sarray_cptr(cs)` with `lean_sarray_size(cs) / 8` entries; `count_at` goes.
- Scope = the C-side `count_at` readers plus the named answers: `concatFoR`/`concatALP` `ns`, `concatBits`
  `counts`, `concatIds` `counts` and `widths` (read through the same `count_at`), `hashConcat`'s per-part count,
  `spreadBytes` `widths`, and `distinctFoR`/`distinctALP`'s returned count (`Nat` → `USize`, `size_t` unboxed).
- Not count lists, left: symbol `offs : Array Nat` (byte positions, an `Enc.syms`/`Enc.enum` field: retyping it is
  a data-structure change); `stringDigits`/`splitBytes`/`transpose`/`symOffs` answers (they are such offsets);
  `longBytes`/`longRows` (row numbers, values).
- Pair lists: the Lean callers already hold `USize` counts (`n.toNat` is written at every `razeColumn` call), so
  `razeColumn`/`encodedParts`/`concatEnum`/`internConcat`/`hashConcat` take `Array (USize × …)` and the flat
  `ByteArray` is built only where the extern is called (`Column.pushBits` fold over the pairs). One form everywhere.
- Each extern stays zip-shaped: its model and the C read `min (cs.size / 8) parts.size` entries; the Lean
  dispatcher additionally `need (cs.size = 8 * parts.size)` where that is not a proved fact at the call site.
- Models read the same bytes: a statement over `ns : Array Nat` becomes one over the counts stored in
  `ns : ByteArray`, i.e. `ns[k]!` ↦ `(Column.bitsAt ns (8 * k) 8).toNat`; `foRStd (n : USize)` and
  `Verify.foRStd_iff` reads `foRStd n` ↔ `FoRWF n.toNat`.

Count bytes are built by `Structural.countBytes : Array USize → ByteArray` (a `Column.pushBits … 8` fold); the
earlier `longBytes` deviation at `razeColumn`/`appendColumn` is gone. Q56 (ca9bfcc, branch `usize-verify`):
- `ungroup`'s `Nat` counts came from its local `rowCounts` (`((qcount v).getD 1).toNat`, `qcount` was already
  `Option USize`), not from `qcount`. `rowCounts : QValue → Option (Array USize)`; a `slices` row count (byte
  offsets ÷ width) enters through `needSize`; `spread` passes `spreadBytes (countBytes widths)`.
- `expandColumn (widths : Array Nat)` → `(widths : Array USize)`, `countBytes widths`.
- No other `longBytes` call carries counts in executable code (the rest are row numbers, bounds or long operand
  values); the six `concatBits (longBytes #[…])` in `StructuralTest` are now `countBytes`.
- `countBytes_size : (countBytes ns).size = 8 * ns.size` (proved, next to `countBytes`). The run-time
  `size = 8 * parts` checks where counts and parts are one array mapped (`razeColumn` booleans,
  `appendColumn`, `internConcat`) are removed; the FoR/ALP `razeColumn` check is restated as
  `ns.size = ms.size`, which is `encodedParts`' to hold.
- Tests: count `.toUSize` → `asCount` 28 → 0 (`StructuralTest` 1, `tools/bench-kernel.lean` 27). `bench-kernel`
  does not build at HEAD (13 errors, `composeKey`/`Column`/`groupLongs` drift), and none is new.

| extern                      | before                                | after                                   | state                  |
|-----------------------------|---------------------------------------|-----------------------------------------|------------------------|
| `distinctFoR`/`distinctALP` | returns `Nat × …`                     | returns `USize × …` (`lean_box_usize`)  | done 257ed53           |
| `concatBits`                | `counts : Array Nat`                  | `counts : ByteArray`                    | done e37d349           |
| `concatFoR`/`concatALP`     | `ns : Array Nat`                      | `ns : ByteArray`                        | done b3e01ea           |
| `razeColumn`/`encodedParts` | `Array (Nat × Enc)`                   | `Array (USize × Enc)`, `countBytes`     | done 2181ee3           |
| `concatIds`                 | `counts widths : Array Nat`           | `counts : ByteArray`; `widths` stay (bit widths) | done e6aac52  |
| `hashConcat`/`internConcat`/`concatEnum` | `Array (Nat × …)`        | `Array (USize × …)`; C `lean_unbox_usize` | done e6aac52         |
| `spreadBytes`/`spreadColumn`| `widths : Array Nat`                  | `ByteArray` / `Array USize`             | done 60546fc, Dyad ca9bfcc |
| `Coc.foRStd`, `appendFoR`, `moveFoR` | `n : Nat`                    | `n : USize`                             | done 60546fc           |

Statements whose meaning changed: `Verify.distinctFoR_spec` (`List.range (distinctFoR …).1` →
`List.range (distinctFoR …).1.toNat`; proof gains the bound `D.size / k.width < USize.size` from `firstsOf`'s
length), `Verify.elemsW_concatALP` (`ns : Array Nat`, `ns[k]!`, `ns.size` → `ns : ByteArray`,
`(Column.bitsAt ns (8 * k) 8).toNat`, `ns.size / 8`; hypotheses kept, none added).

## Fixed in Q53 (commits 4d71741, f0715c1; build 553 jobs green; qlean-test: all but `qipc`, eval 13 = open list)

`toUSize` lines: 383 before, 337 after. Every c and d site of the Kernel, Eval, Wire and Db tables is gone:

| fix                                                                                    | sites                        |
|----------------------------------------------------------------------------------------|------------------------------|
| `Db.OwnFile.count : USize`; `ownFile` stores `n`, `ownWrite` callers pass `f.count`      | Own, Core 253, Db/Test 418   |
| `Files.parts`, `QIO.fileParts` take `count : USize`; `columnOf` passes the `ku` it holds | ObjectFile 217, Core 240     |
| `symbolsOver`: the domain size enters through `needSize`                                | Splayed 147                  |
| `dictOffs`, `ObjectFile` symbol file: the byte count bound enters through `needSize`    | Own 64, ObjectFile 98        |
| `findSymColumn`, `binSymColumn`, `memberColumn`: `ko.size - 1` through `needSize`       | Search 980, 1190, 1314–1324  |
| `whereColumn`: hand-written need replaced by `needSize`                                 | Search 1376                  |
| `vectorBody` returns `USize × ByteArray`; payload-derived counts through `needSize`;  `checkedCount n.toNat` | Wire/Encode |
| tests: `n`, `d`, `chainN`, `sliceN`, `nb`, `xs.length`… through `asCount`                | SortTest, ElementwiseTest, StructuralTest, ScanTest, SearchTest, Kernel/Test |
| `need-test`: the CLI counts through `needSize`                                          | tools/need-test              |

Proofs adjusted (no statement changed): `Search.memberColumn_type`, `Search.whereColumn_type`,
`Verify.findSymColumn_idxOf`, `Verify.memberColumn_symbol` unfold `needSize` beside `need`.
Run-time message changed: `memberColumn`/`whereColumn` now print `needSize`'s "`<op>: <c> does not fit a USize`".

## Fixed in Q53 second run (worktree `/data/tmp/qlean-usize-v`, branch `usize-verify`)

Kind e, every hand-written `need (c < USize.size) … c.toUSize` now `needSize` (one source for the fits check):

| site                                                         | proof adjusted (unfold set only)                  |
|--------------------------------------------------------------|---------------------------------------------------|
| `QValue.ofArray`, `Column.sliceAt`, `QValue.ofBytes` (Value) | `ofArray_of_fits`, `ofArray_general`, `ofArray_WF`, `Verify.tyOf_ofBytes` |
| `Groups.count`, `overSegments`, `overSegmentsFloat`, `alpLive` (Reduce) | `Verify.overSegments_slot` (its local `one` restated through `needSize`), `Verify` alp `alpLive` lemma |

Run-time messages now read `<op>: <what>: <c> does not fit a USize`.

The defs not reviewed before:

| def                                   | verdict                                                                                       |
|---------------------------------------|-----------------------------------------------------------------------------------------------|
| `Kernel.worthHalving (n m)`           | retyped `USize`; the cost formula reads `.toNat` inside; `keyMatch` decides it before its `Nat` shadow |
| `Structural.reverseMoveFoR (n)`       | retyped `USize`; `reverseFoR` passes its `n` without `.toNat`; the test passes `asCount n`     |
| `Coc.foRStd (n : Nat)`                | stays until the C-ABI decision: `moveFoR` feeds it `p.1.1` from `concatFoR`'s `ns : Array Nat`, and `Verify.foRStd_iff` states it against the `Nat` model `FoRWF` |
| `Structural.appendFoR (n : Nat)`      | stays until the C-ABI decision: its one caller, `concatFoR`, passes an entry of `ns : Array Nat` |
| `Dyad.divModPairs (n : Nat)`          | stays: `xs.size`/`ys.size` of an array already in memory used as a loop bound; the answer's count enters through `vectorOf` |
| `Random.dealBelow (n)`                | retyped `USize`; its count now arrives checked (next table); `n.toNat` bounds the loop positions |
| `Eval.Val` `items (n : Nat)`          | stays: `xs.size` / `offs.size - 1` used as the bound of a `List.range` scan, nothing sized by it |

Lean-side loops that build an answer of a caller-given count (searched: `Array.range`, `List.range`,
`List.replicate`, `Array.replicate`, `Array.mkEmpty`, `for _ in [:…]` in `QLean/Eval`):

| site                                                    | count from                         | done                                          |
|---------------------------------------------------------|------------------------------------|-----------------------------------------------|
| `Random.randomOf` `draws` (long/temporal bound, list, vector, table sources) | the q count `n` of `n?x` | `counted n Kernel.boxedBytes "draws"`: `needBytes` then `needSize`; `dealBelow` gets the `USize` |
| `Random.randomOf` float source                          | the q count                        | the same `counted`                            |
| `Random.randomOf` guid source                           | the q count                        | its two checks folded into `counted n 16 "drawGuids"` |
| `Eval/Mon.lean` `til` fallback (`tilColumn` declined)    | the q long                         | `needBytes n.natAbs Kernel.boxedBytes "til"` before its fits check (kept: `vectorOf_type` needs it, and in the logic `USize.size` may be `2^32 < maxBytes`, so the byte bound does not imply it); `Verify.til_ok`'s proof splits both |
| `Mon.whereIndices`                                      | the summed q counts                | already bounded by `maxWhereSize` (`whereTotal`), left |
| `Iterate.eachCall`/`zipCall`, `DotH` items, `Arms` insert ids, `Parse` table literal, `Qsql` `spread`/`rows`, `Mon` flip/`csv` rows | a count of a value already in memory | left: the answer is no larger than data that exists |

`Kernel.boxedBytes : Nat := 24` (Need.lean): an 8-byte `Array` slot and a 16-byte object, what one boxed
fixed-width `QAtom` costs.

## Item 4: the `Enc` readers (third run, worktree `/data/tmp/qlean-usize-v`)

| declaration     | before                                 | after                                                    | commit  |
|-----------------|----------------------------------------|----------------------------------------------------------|---------|
| `Enc.dense`     | `(t) (n : Nat) (e) : Nat × Enc`        | `(t) (n : USize) (e) : Nat × Enc`                        | 56a250f |
| `Enc.blobOf`    | `(n : Nat) (e)`                        | `(n : USize) (e)`; the loop reads `Array.range n.toNat`  | 56a250f |
| `Column.atoms_dense` | over `n : Nat`                    | over `n : USize`, the right side at `n.toNat` (retyping) | 56a250f |
| `Enc.raw`       | `(t) (n : Nat) (e) : Array UInt64`     | `(t) (n : USize) (e)`; body `Array.range n.toNat`        | ad54927 |

`Enc.raw` callers are Verify only. Restated by retyping (`n` → `n.toNat`): `raw_foR`, `raw_bytes`, `raw_encode8`,
`raw_encode` (`m : USize`, `hm : m.toNat ≤ x.size / w`), `atoms_eq_map_raw`, `atoms_encode`, `size_raw`, the Gather
lemmas. `ascending_i64_iff_raw` read `(raw t (b.size / 8) b).take n`; it now reads `(raw t n b).take (b.size / 8)`:
both are the first `min n (b.size / 8)` elements, so the meaning is unchanged.

`Enc.atoms` (e6137ab; build 553 jobs green, qlean-test all but `qipc`, eval 13 = open list): before
`atoms (t) (n : Nat) (e)`; after `atoms (t) (n : USize) (e) := atomsN t n.toNat e`, the old body renamed `atomsN (n : Nat)`.
Not a plain retype because the `ofAtoms` round trips (`atoms_ofAtoms`, `…_bytes`, `…_bits`, `…_guid`, `…_syms`,
`Carrier.atoms_column`) state the read at a Lean size `as.size`, and `atoms_dense` reads at `dense`'s `Nat` first
component: over `USize` each would need `as.size < USize.size`. So `atomsN` is the model, called only in statements and
proofs (`Value` round trips, `atoms_type`, `count_atoms`, `atoms_le`, `Dep.Val`, `Dep.Wide`); every executable caller
calls `atoms` at the `USize` it holds (≈90 `.toNat` dropped by `uncoerce`; `Enc.dense` calls `atoms t n`). Verify
statements over a `USize` count read `atoms t n` (was `atoms t n.toNat`, same value by definition). No statement's
meaning changed.

## Still open

| item                                                     | why left                                                                |
|----------------------------------------------------------|-------------------------------------------------------------------------|
| `partGroups (nr nl : Nat)`, `keyMatch`'s shadowing, `ffColumn`, `keyGroups` | they bound `Nat` row positions; retyping moves the `.toNat` inside, removes no conversion |
| `Kernel.Index.pairIds (k : Nat)`                         | re-classified as stays: `k` is the pairing stride written into a long column (`keyShift = 2^32` is not a count) |
| `Coc.foRStd`, `Structural.appendFoR`                     | wait on the C-ABI `Array Nat` decision (above)                          |
| `tools/bench-kernel.lean` (20 d sites)                   | not built by the gate                                                   |
| the C-ABI `Array Nat` list above                         | the user's decision                                                     |
