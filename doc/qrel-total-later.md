> Deferred 2026-11-10. This is the earlier full plan (all of `Ew`, `Find`, `Scan`, `Group`, `Struct`, `Prog`, `Spec*`,
> qlean kernel coverage). The `Alg` ops and the programs moved to `doc/qrel-total-plan.md` and are done first;
> the non-`Alg` packages here are picked up after that. Line numbers are 82b5941's.

# leetq `Rel k v` total: inventory of `Except` sources and the work plan

Analysis only; no Lean file was edited and nothing was built. Read at `origin/leetq-total` = 82b5941 (worktree
`.claude/worktrees/agent-a9f7238370b1a9fc1`), qlean at `/data/tmp/hs4/qlean` (a260b4e). Line numbers are 82b5941's.
Design: `doc/qrel-total-design.md`. Paths below are relative to `leetq/LeetQ/Rel/` unless they start with `Bench/`.

Treated as done (running now, listed only as prerequisites):

| id | running work                                                                                  |
|----|-----------------------------------------------------------------------------------------------|
| R1 | `raze`, `codes`, `Obj.raze`, `Obj.codes` total in `Algebra.lean`; a count bound decided in the op |
| R2 | `Struct.KCol` and `Struct.amend`'s fold state retyped to typed parts                          |
| R3 | `lean-refactor` runs on the leetq package                                                     |

## 1. Inventory: every source of a failure

A source is a line that ORIGINATES a failure (`throw`, `.error`, a failing `match`/`let some` arm). Lines that only
propagate (`←`, `liftV`, `| .error e => .error e`, `Bench/Main.lean` :59 :60 :71) are not counted. 104 sources.

| class | cause                                                                    | sources |
|-------|--------------------------------------------------------------------------|---------|
| K     | a kernel's `Option`/`QValue` answer with no `_isSome`/`_wf` theorem used | 39      |
| T     | a type-tag dispatch a typed argument removes                             | 25      |
| S     | a payload shape `Enc.WF` already excludes                                | 10      |
| C     | a count or arity equality between two parts that the types do not carry  | 10      |
| D     | a data-dependent domain condition of a q verb (q signals an error)       | 9       |
| P     | a program boundary: parsing, search with no answer, CLI                  | 7       |
| B     | a boxed general list read as INPUT whose elements are untyped            | 3       |
| U     | a count past `USize`                                                     | 1       |

### K: kernel answer not yet known to exist or to be well-formed

| site                           | kernel / producer                             | theorem today                       |
|--------------------------------|-----------------------------------------------|-------------------------------------|
| `Core` :105 :106               | `Arr.of` decides `WFAt` of ANY answer         | root of every `Arr.ofPart` call     |
| `Core` :556                    | `sliceColumn` in `Parted.box`                 | `sliceColumn_isSome` (not used yet) |
| `Core` :572                    | `razeColumn` in `razeParts`                   | `razeColumn_isSome/_wf`             |
| `Core` :582                    | `Parted.of?` on running counts                | none                                |
| `Algebra` :243                 | `razeColumn`                                  | R1                                  |
| `Algebra` :328                 | `groupIdsColumn`                              | R1 (`groupIdsColumn_isSome`)        |
| `Algebra` :538                 | `Order.rankSlices` answer count               | none                                |
| `Algebra` :705                 | `Parted.of?` on `runStarts`                   | `runStarts_group` (Algebra :1271)   |
| `Ew` :26 :72                   | `dyadColumn`/`monColumn` answer type          | `dyadColumn_type`, `monColumn_type` |
| `Ew` :89                       | `bitwPayload`                                 | none                                |
| `Ew` :108                      | `shiftColumn`                                 | none                                |
| `Ew` :160                      | `findColumn`, `whereColumn` (non-vector)      | `_type` only                        |
| `Ew` :170                      | `gatherFill`: an encoding it has no arm for   | none                                |
| `Ew` :191                      | `memberColumn`                                | `memberColumn_type` only            |
| `Ew` :193 :195                 | `gatherColumn`                                | `gatherColumn_isSome/_wf`           |
| `Ew` :196 :197                 | `razeColumn`                                  | `razeColumn_isSome/_wf`             |
| `Find` :38                     | `list`: the answer is no vector               | per kernel                          |
| `Find` :47                     | `vec`: eleven dispatch kernels (list below)   | `_type` only, but gather and raze   |
| `Struct` :76                   | `assignSyms`                                  | `assignSyms_syms/_interned` (qlean) |
| `Struct` :122                  | `Parted.of?` on kernel-written offsets        | none                                |
| `Struct` :230                  | `matchColumn`                                 | none                                |
| `Struct` :306                  | `dyadColumn .sub` at a time type              | none                                |
| `Struct` :341, `Prog` :36      | `Ops.overBy` (`groupedOver`)                  | none                                |
| `Prog` :65                     | `Ops.countBy`                                 | none                                |
| `Prog` :289                    | `lowZeroPayload`                              | none                                |
| `Prog` :385                    | `Ops.grade` (`gradeColumn`)                   | `gradeColumn_type` only             |
| `Bench/Main` :66 :136          | `fin?`, `ofBytes?`                            | none                                |
| `Bench/Main` :201 :207 :220    | `Ops.over`, `Ops.scan`, `Ops.mwin`            | none                                |
| `Algebra` :959, `Struct` :1206 | fixtures: `Parted.of?` on literals            | `by decide` suffices                |
| `Ew` :422                      | fixture: `tilColumn` on a literal             | `by decide` suffices                |

- `Find.vec` :47 serves `whereColumn`, `distinctColumn`, `findColumn`, `memberColumn`, `binColumn` in `Find`, and
  `razeColumn`, `takeColumn`, `dropColumn`, `reverseColumn`, `rotateColumn`, `gatherColumn` in `Struct` :27–56.
- `Struct` :122 (`partedP`) is reached with kernel-written offsets from `flipP`, `indexPartedP`, `pairsP`, `wjP`;
  from `cutP` the offsets are user data, counted under D.
- `Scan.lean` has no `Except` line, but twelve `Ops.*` answer `Option`, several through `(Arr.of …).toOption`
  (:64 :68 :79 :100). They are the same partiality under another type; a text search for `Except` misses them.

### T: type-tag dispatch

| site                                | condition                                   | witness that removes it          |
|-------------------------------------|---------------------------------------------|----------------------------------|
| `Ew` :24, :69                       | no kernel claims verb `v` at `t`, `u`       | `Eval.ewType v t u = some rt`    |
| `Ew` :141 :142 :147 :151 :165       | `clsOf`, `nullBits`, unit, `width` = `none` | the same, or `t.width = some w`  |
| `Algebra` :335                      | `orderKind a = none` in `arrDense`          | `orderKind a = some k`           |
| `Algebra` :820                      | `nullBits a = none` in `mapVal`             | `nullBits a = some nb`           |
| `Struct` :64                        | `a.width = none` in `packed`                | `a.width = some w`               |
| `Struct` :99                        | `:` of a `u` into an `a` list               | `y : Arr a ny`                   |
| `Struct` :242 :275 :284 :298        | two key/time columns differ in type         | typed `KCol` pairs (R2)          |
| `Struct` :303 :336, `Prog` :58 :280 | a general list where an atom type is due    | `t ≠ .general` (today's idiom)   |
| `Prog` :256                         | `ordJoin`'s verb is no comparison           | `(cmpOp v).isSome`               |
| `Prog` :305 :308 :346               | a kernel refuses a product key or object    | none: `Alg` is over `Obj` already|
| `Prog` :375                         | `fn c` alone has no stored form             | approval Ap4                     |
| `Bench/Main` :314                   | `relCard`: key and value differ in type     | typed argument                   |

`Eval.ewType v t u = some rt` is already carried by `Prog.Fn.dy` and `Fn.sect` (`Prog` :100–120).

### S, C, D, P, B, U

| class | site                                      | condition                                                    |
|-------|-------------------------------------------|--------------------------------------------------------------|
| S     | `Ew` :33                                  | `Enc.ofAtoms t #[a]` of a typed atom                         |
| S     | `Ew` :81                                  | a boolean column that is not `bits`                          |
| S     | `Ew` :97 :166, `Find` :53, `Algebra` :340 | `Enc.bytesOf` = `none` (`bytesOf_isSome` exists)             |
| S     | `Core` :577                               | a general list whose payload is not `.gen`                   |
| S     | `Struct` :184 :198                        | `longBytes` = `none` (`longBytes_isSome`, Algebra :54)       |
| S     | `Struct` :361                             | a symbol column neither `syms` nor `enum`                    |
| C     | `Algebra` :376                            | `Vals.ofParts`: a part's count against `n` (callers below)   |
| C     | `Algebra` :529                            | `setIds`: the offsets hold no terminator                     |
| C     | `Ew` :113, `Struct` :92                   | two operand columns differ in length                         |
| C     | `Struct` :240 :274 :276 :337              | arity or row counts of key columns differ                    |
| C     | `Struct` :245 :273                        | no key column                                                |
| D     | `Find` :108                               | `&x`: a negative or null count                               |
| D     | `Struct` :96                              | amend: an index outside `0..nx`                              |
| D     | `Struct` :138 (and :122 from `cutP`)      | `cut`: offsets negative, past the end, or not ascending      |
| D     | `Struct` :186                             | `flip`: runs differ in length                                |
| D     | `Struct` :362, :368                       | `like`/`ss`: the pattern does not parse / is not fixed-width |
| D     | `Prog` :331 :332                          | `ranMul` at `a = 0`, `a = 0N`                                |
| D     | `Bench/Main` :293                         | `encCol`: a value outside `0..m`                             |
| P     | `Blocks` :52                              | no plan reaches the goal                                     |
| P     | `Chess` :142                              | `head?` of a relation's rows                                 |
| P     | `Bench/Main` :297 :431 :433 :435 :444     | CLI parsing, unknown encoding, checksum assertion            |
| B     | `Core` :563 :566 :567                     | `razeParts`: a box that is not a list / a vector of `v`      |
| U     | `Prog` :247                               | `tilKey n` past `USize`                                      |

- `Vals.ofParts` is reached from `ofCols` (14 ops of `Alg`), `memP`, `familyP`, `uncons`, `Prog.lamFold`,
  `ordJoin`, `Vals.pick`, `Struct.flipP`, `indexPartedP`, `wjBy`.
- U is one explicit line, but the same bound is a hypothesis of `razeColumn_isSome/_wf`, `answer_wf`,
  `cycleIds_wf` and a decided condition inside `Parted.of?` (Core :538); every caller of those meets it.

## 2. One fix per class

- **K.** `(kernel …).get (isSome proof)` under `Arr.mk _ (wf proof)`, as `pick` and `empty` are at 82b5941. Then
  `Arr.of`, `Arr.ofPart`, `Find.vec`/`list`/`onKey`/`dense` have no caller and are deleted. Needs: one
  `KernelWF/<Family>.lean` per qlean kernel family (wave 1). New type: no, only new theorem files.
- **K, the declined case.** Where a kernel answers `none` on a well-formed input, no theorem exists to find.
  Needs approval Ap6.
- **T.** A witness argument decided at the call site, built from functions that exist (`Eval.ewType`,
  `orderKind`, `nullBits`, `width`, `cmpOp`), with the auto-param `by first | decide | assumption` that
  `ht : t ≠ .general` has today. Needs approval Ap2 and `KernelWF/Dyad.lean`. New type: no (Ap2's other options are).
- **S.** A case split on `x.wf`, as `gens` and `longBytes_isSome` do. Needs `KernelWF.long_cases`,
  `general_cases`, `bytesOf_isSome`, which exist. New type: no.
- **C.** The count is in the type: `pick` answers `Vals A (len i)`, `raze` answers the sum, and a kernel's paired
  answers get one size theorem (`join_len`, `cross_len`, `rankSlices_size`); arity by `Vector`; two operands
  share the index `n`. Needs R1 and approval Ap1. New type: no (Ap1's recommended option deletes one structure).
- **D.** Needs approval Ap5; nothing is proposed without it.
- **P.** The answer is the relation or list itself, empty when there is none; CLI errors are `IO` errors, which
  is where they already end. Needs approval Ap8 for `Blocks.plan`. New type: no.
- **B.** Consumers take the flat `Parted v`; a boxed list is output only. Needs approval Ap3. New type: no
  (Ap3's option H is).
- **U.** Decided in the op: `if h : bound then kernel else kernel-free reference answer`, R1's form. New type: no.

### Approvals (all decided 2026-11-09: the recommended option of every row, Ap1–Ap8)

| id  | question                                                        | options | recommended |
|-----|-----------------------------------------------------------------|---------|-------------|
| Ap1 | How do the counts of an op's two answer columns meet?           | A B C   | A           |
| Ap2 | How does a verb know it has a kernel at its types?              | D E F   | D           |
| Ap3 | What reads a boxed general list?                                | G H I   | G           |
| Ap4 | What happens to `Prog.fn c` alone, which has no stored form?    | J K L   | J           |
| Ap5 | A q verb whose input q rejects (the 9 D sites)                  | M N O   | M           |
| Ap6 | A kernel that declines a well-formed encoding                   | P Q R   | P           |
| Ap7 | Does "total" also ban `Option` results (`Scan.Ops.*`, 12 ops)?  | S T     | S           |
| Ap8 | `Blocks.plan` when no plan exists                               | U V     | U           |

- A: delete `Cols`, `ofCols`, `Vals.ofParts`; ops build `Rel` from count-indexed `Vals`, cast by size theorems.
  `cols` is already `pure` and `Cols` holds what `Rel` holds. This removes a structure.
- B: keep `Cols`; prove one count lemma per op and cast inside `ofCols`.
- C: add a count index to `Part`.
- D: witness arguments from existing functions, decided at the call site.
- E: a typeclass per fact (new classes).
- F: an inductive of typed verbs (new type).
- G: nothing reads one. `mem`, `setId`, `existsImage`, `Struct.flip`/`indexParted`/`raze` take the flat
  `Parted v` or the carrier `(g) × Arr t g × Parted v`; `Parted.ofBoxes` stays only as an `Option` parser where
  q data is loaded.
- H: a typed box, a new subtype of `Arr .general`.
- I: keep `ofBoxes` failing.
- J: change the `Prog` inductive: `fn` leaves, `app P c` and `test c P` enter.
- K: `run` takes a decidable `P.Runnable` proof (a new predicate).
- L: keep the refusal.
- M: a decidable precondition argument; a caller on run-time data writes `if h : pre then op h else …` and owns
  the else branch. For `like`/`ss`, the argument is qlean's parsed pattern instead of a `String`.
- N: a total extension per verb with a stated value, as `pick`'s fill.
- O: the verb leaves the algebra and stays an `Option` parser.
- P: decide in the op and answer the kernel-free reference (R1's form), each case reported.
- Q: extend the qlean kernel first.
- R: narrow the op's domain by a witness.
- S: yes for ops; internal fast-path selectors (`rangeOffsets`, `Find.direct`, `laneKind`, `asTest`, `asFn`)
  stay `Option` because the caller holds the other branch.
- T: only `Except`.
- U: answer the list of plans, empty when none; the search a `hylo` with a measure.
- V: answer `Option`.

## 3. Work packages

Every brief starts with this block, verbatim:

> Rules. (1) The change/fix should be general, not a patch for what's mentioned. (2) Never silently throw away an
> error: no default value answering for a failed read; a case you cannot prove is reported with its exact text.
> (3) No new structure, field or type without approval: stop and report. (4) Mechanical edits (renames, moving a
> declaration, changing a signature at every caller) go through `./scripts/lean-refactor`. (5) Do not edit
> `KernelWF/*` unless this brief names you its owner. (6) Edit only the files and line ranges you own; a lemma you
> need from a file you do not own is proved in your own file and reported. (7) Build only the modules named, through
> `./scripts/cap`, in the background, never silent for 5 minutes. (8) Branch `leetq-total`, never `master`.

Build command in a worktree: `./scripts/cap lake -d leetq -K qlean=/data/tmp/hs4/qlean build <modules>` (check the
flag against `leetq/lakefile.lean` before the first build).

Import order, which fixes the order of everything after wave 1:
`Core → KernelWF/Raze → KernelWF/Gather → {Find, Ew, Scan} → Algebra → {Struct, Chess, Blocks, Wumpus, Circuit} →
Spec → {SpecFind, SpecScan} → SpecStruct → {SpecAmend, SpecKey, Prog} → {Group, Norm} → Bench/Main`.

A package touches nothing outside its "owns" cell. Module names are under `LeetQ.Rel.`.

| pkg | owns                                       | after                     | build green                   |
|-----|--------------------------------------------|---------------------------|-------------------------------|
| K1  | new `KernelWF/Search.lean`                 | none                      | `KernelWF.Search`             |
| K2  | new `KernelWF/Shape.lean`                  | none                      | `KernelWF.Shape`              |
| K3  | new `KernelWF/Dyad.lean`                   | none                      | `KernelWF.Dyad`               |
| K4  | new `KernelWF/Reduce.lean`                 | none                      | `KernelWF.Reduce`             |
| D1  | `Core` :547–583; new `Parted.lean`         | R1, K2, Ap3               | `Parted`                      |
| D2  | `Find.lean`                                | K1, Ap5, Ap6              | `Find`                        |
| D3  | `Ew.lean`                                  | K1, K3, Ap2, Ap6          | `Ew`                          |
| D4  | `Scan.lean`                                | K4, Ap2, Ap7              | `Scan`                        |
| T1  | new `TotalCheck.lean` (section 6)          | R3                        | it must FAIL, listing offenders |
| D5  | `Algebra` :334–700                         | R1, D1–D3, Ap1            | `Algebra` (with D6)           |
| D6  | `Algebra` :700–1604                        | R1, D1–D3, Ap1, Ap3       | `Algebra` (with D5)           |
| D7  | `Struct` :20–230 and their in-file proofs  | R2, D5, D6, Ap5           | `Struct` (with D8)            |
| D8  | `Struct` :232–372 and their in-file proofs | R2, D5, D6, K4, Ap5       | `Struct` (with D7)            |
| D9  | `Chess`, `Blocks`, `Wumpus`, `Circuit`     | D5, D6, Ap8               | the four modules              |
| S1  | `SpecFind` :1–1700; `Spec.lean`            | D7, D8                    | `SpecFind` (with S2)          |
| S2  | `SpecFind` :1700–3265                      | D7, D8                    | `SpecFind` (with S1)          |
| S3  | `SpecScan.lean`                            | D4, D7, D8                | `SpecScan`                    |
| S4  | `SpecStruct` :1–2000                       | S1–S3                     | `SpecStruct` (with S5)        |
| S5  | `SpecStruct` :2000–3239                    | S1–S3                     | `SpecStruct` (with S4)        |
| S6  | `SpecAmend.lean`                           | S4, S5                    | `SpecAmend`                   |
| S7  | `SpecKey.lean`                             | S4, S5                    | `SpecKey`                     |
| D10 | `Prog` :1–840                              | S4, S5, Ap4, Ap5          | `Prog` (with S8)              |
| S8  | `Prog` :840–2428                           | S4, S5, Ap4               | `Prog` (with D10)             |
| D11 | `Group`, `Norm`, `Bench/Main`              | S6, D10, S8               | all of `LeetQ`, `bench`       |
| C1  | the deletions in its brief; `TotalCheck`   | D11                       | `LeetQ`, `bench`, `TotalCheck` |

Two packages that share a file each work in their own worktree on their own line range and are merged by hunk.
Neither can build the module green alone while the other's range still holds the old signatures, so the second to
finish rebases on the first and the pair is green together.

### Statements a later package may assume

From K1–K4. The owner states the weakest hypothesis under which the kernel body answers; these are the shapes:

```
-- KernelWF/Search.lean (K1)
theorem whereColumn_isSome  (hw : Enc.WF .boolean n e) : (whereColumn .boolean n e).isSome
theorem whereColumn_wf      (hw : Enc.WF .boolean n e) (h : whereColumn .boolean n e = some v) :
    ∃ m b, v = .vector .long m (.bytes b) none ∧ Enc.WF .long m (.bytes b)
theorem distinctColumn_isSome (hw : Enc.WF t n e) (hg : t ≠ .general) : (distinctColumn t n e).isSome
theorem distinctColumn_wf   (hw : Enc.WF t n e) (h : distinctColumn t n e = some v) :
    ∃ m e', v = .vector t m e' none ∧ Enc.WF t m e'
theorem findColumn_isSome   (hx : Enc.WF t nx ex) (hy : Enc.WF t ny ey) (hg : t ≠ .general) :
    (findColumn t s nx ex (.vector t ny ey a)).isSome
theorem findColumn_wf       … = some v → ∃ e', v = .vector .long ny e' none ∧ Enc.WF .long ny e'
theorem memberColumn_isSome / memberColumn_wf   -- answer: one boolean per element of the left operand, `.bits`
theorem binColumn_isSome    / binColumn_wf      -- answer: ny longs
theorem matchColumn_isSome  (hx : Enc.WF t nx ex) (hy : Enc.WF t ny ey) (hg : t ≠ .general) :
    (matchColumn t nx ex ny ey).isSome
-- KernelWF/Shape.lean (K2)
theorem takeColumn_isSome/_wf    -- `takeColumn a nx e n`: |n| elements of `a`
theorem dropColumn_isSome/_wf    -- `dropColumn a nx e n`: `nx - |n|` elements
theorem reverseColumn_isSome/_wf -- states exactly which encodings it declines (`syms` today)
theorem rotateColumn_isSome/_wf, shiftColumn_isSome/_wf, assignSyms_isSome/_wf
theorem sliceColumn_wf (hw : Enc.WF t n e) (h : sliceColumn t n e off m = some e') : Enc.WF t m e'
theorem countFits_of_lt (hn : n < USize.size) (hw : Enc.WF t n e) : countFits n e
-- KernelWF/Dyad.lean (K3)
theorem dyadColumn_isSome (h : Eval.ewType v t u = some rt) (ha : Enc.WF t na a) (hb : Enc.WF u nb b)
    (hs : shape agrees with na nb) : (dyadColumn v shape t u na a nb b).isSome
theorem dyadColumn_wf     … = some (rt', c) → rt' = rt ∧ ∃ e, c = .vector rt n e none ∧ Enc.WF rt n e
theorem monColumn_isSome/_wf, bitwPayload_isSome/_wf, lowZeroPayload_isSome/_wf
theorem ofAtoms_singleton_wf (ht : t ≠ .general) (a : Carrier t) :
    ∃ e, Enc.ofAtoms t #[Carrier.atom a] ht = some e ∧ Enc.WF t 1 e
-- KernelWF/Reduce.lean (K4)
theorem gradeColumn_isSome/_wf   -- `n` longs
theorem groupedOver_isSome/_wf   -- under `op.resultType false t = some rt`: `g` elements of `rt`
theorem overColumn_isSome, and `_isSome/_wf` of the scan and moving-window kernels as `Scan.Ops` calls them
theorem rankSlices_size (w : USize) (b o : ByteArray) : (Order.rankSlices w b o).size = o.size - 8
theorem whereBits_size_le (n : USize) (b : ByteArray) : (whereBits n b).size ≤ n.toNat * 8
```

- From R1 (read the landed signatures; assume only this): `Alg.raze`, `Alg.codes`, `Obj.raze`, `Obj.codes` have no
  `Except` in their result and keep their argument types.
- From D1: `Parted.box : (P : Parted v) → Arr .general P.g`.
- From D2–D4: every `Find.*`, `Ew.*`, `Ops.*` op keeps its name and arguments, gains only the witnesses Ap2
  allows, and returns bare the type that was inside its `Except`/`Option`.
- From D5 to D6: `Vals.pick : Vals A n → (i : ByteArray) → Vals A (len i)`;
  `Vals.raze : Vals A n → Vals A m → Vals A (n + m)`; `arrDense (x : Arr a n) (h : orderKind a = some k) : ByteArray`;
  `join_len : len (join l r).1 = len (join l r).2`; `cross_len : len (cross n m).1 = len (cross n m).2`.
- From D5/D6 to all later packages: every `Alg.*` op keeps its name and arguments and returns its payload bare.
- From D10 to S8: `Prog.run : Prog A B → RelV A B`;
  `run_sound : ∀ (P : Prog A B), P.Sound → ((P.run).Holds : Ob A ⟶ Ob B) = P.den`.

### Briefs (prepend the Rules block to each)

**K1.** Create `leetq/LeetQ/Rel/KernelWF/Search.lean`, importing `QLean.Kernel.Search`, `QLean.Kernel.Sort`,
`QLean.Verify.{Where,Distinct,FindMember,Search,SymFind}`, `LeetQ.Rel.KernelWF.Gather`. Prove `_isSome` and `_wf`
for `whereColumn`, `distinctColumn`, `findColumn`, `memberColumn`, `binColumn`, `matchColumn` in the shapes of the
plan's "Statements" block, by unfolding each kernel's Lean body, as `gatherColumn_isSome`/`gatherColumn_wf`
(`KernelWF/Gather.lean` :27, :98) do. The call sites that will use them: `Find.lean` :90 (`where`), :113
(`distinct`), :123 (`find`), :131 (`in`), :142 (`bin`); `Ew.lean` :187–191; `Struct.lean` :226 (`same`). For each
kernel, state the weakest hypothesis; if a well-formed input is declined (`none`), do not add a hypothesis to hide
it: report the kernel, the encoding and the line of the declining arm. Edit no existing file.

**K2.** Create `leetq/LeetQ/Rel/KernelWF/Shape.lean`. Kernels: `takeColumn`, `dropColumn`, `reverseColumn`,
`rotateColumn`, `shiftColumn`, `assignSyms`, plus `sliceColumn_wf` and `countFits_of_lt` to complete
`sliceColumn_isSome` (`KernelWF/Gather.lean` :178). Call sites: `Struct.lean` :31 `take`, :35 `drop`, :40
`reverse` (which already routes `syms` to `gatherColumn`), :47 `rotate`, :71 `scatter`; `Ew.lean` :103 `prior`;
`Core.lean` :547 `Parted.slice`. Existing material: `cycleBytes_size`, `cycleBits_size`, `cycleIds_wf`,
`sliceSyms_wf` (`KernelWF/Gather.lean` :127–156), qlean's `Verify/TakeDrop.lean`, `Verify/Assign.lean`
(`assignSyms_syms`, `assignSyms_interned`). Same reporting rule for declined inputs as K1. Edit no existing file.

**K3.** Create `leetq/LeetQ/Rel/KernelWF/Dyad.lean`. Prove that `dyadColumn v shape t u na a nb b` answers, at
type `rt` and with `n` well-formed elements, whenever `Eval.ewType v t u = some rt` and both payloads are
well-formed, for the three shapes `Ew.vv`, `Ew.av`, `Ew.va`; the same for `monColumn name t n e`, `bitwPayload`,
`lowZeroPayload`; and `ofAtoms_singleton_wf`. Start from `dyadColumn_type` (qlean `Kernel/Elementwise.lean` :1862),
`monColumn_type` (:2163), `Ew.val_wf`, `Ew.mon_wf` (`KernelWF/Raze.lean` :98, :104), `Column.ofAtoms_isSome`,
`Column.ofAtoms_WF`. Call sites: `Ew.lean` :21 `dyad`, :29 `atomCol`, :67 `mon`, :86 `bitwise`; `Prog.lean` :286
`lowZeroArr`; `Struct.lean` :306. If `ewType = some rt` does not imply an answer for some encoding pair, report the
pair; that case goes to approval Ap6, it is not yours to settle. Edit no existing file.

**K4.** Create `leetq/LeetQ/Rel/KernelWF/Reduce.lean`. Kernels behind `Scan.lean`'s `Ops.*` (:34 `scan`, :40
`over`, :43 `avg`, :64 `countBy`, :68 `lastBy`, :79 `overBy`, :93 `mwin`, :100 `grade`, :108 `rank`, :112
`permute`, :117 `sort`, :128 `xasc`): `gradeColumn`, `groupedOver`, `overColumn`, the scan and moving-window
kernels; plus `rankSlices_size` (for `Algebra.lean` :527 `setIds`) and `whereBits_size_le`. Start from
`gradeColumn_type` (qlean `Kernel/Sort.lean` :1076), `overGroups_wf` (`KernelWF/Raze.lean` :110), qlean's
`Verify/{Grade,ScanOver,Group,BinWin}.lean`. `lastBy` answers `none` on an empty group by design: state that
condition, do not remove it. Edit no existing file.

**D1.** Move `Parted.slice`, `box`, `razeParts`, `ofBoxes` (`Core.lean` :547–583) into a new
`leetq/LeetQ/Rel/Parted.lean` that imports `LeetQ.Rel.KernelWF.Shape` (Core cannot: `KernelWF/Raze.lean` imports
Core). Make `box` total: every group's slice exists by `sliceColumn_isSome` under `P.co` (the cuts are in range) and
is well-formed by `sliceColumn_wf`; a count past `USize` is decided in the op with the kernel-free reference
(`List`-level slice) in the other branch. `ofBoxes` and `razeParts` become the one `Option` parser of approval Ap3
and lose every caller inside the algebra. Move with `./scripts/lean-refactor`. Report the new signatures verbatim.

**D2.** `Find.lean`: make `where` (:90), `whereCounts` (:105), `distinct` (:113), `find` (:123), `in` (:131),
`bin` (:142) return their payload bare, by `Option.get` of K1's `_isSome` and `Arr.mk` of K1's `_wf`; delete
`list` (:35), `onKey` (:41), `vec` (:45), `dense` (:50) once nothing in this file calls them (a helper a later
file still calls stays in place until that file's package). `whereCounts`' negative count (:108) follows approval
Ap5. Restate this file's own theorems that carry `= .ok` (:176–207, :732, :780, :1046, :1196–1329) with the
hypothesis gone and the answer named by the op itself. Fix the `#guard`s (:1458 `ans`).

**D3.** `Ew.lean`: `dyad` (:21), `atomCol` (:29), `Ew.val` (:42), `atomVal` (:47), `valAtom` (:60), `mon` (:67),
`not` (:78), `bitwise` (:86), `atomBits` (:92), `prior` (:103), `Lift.ofVerb` (:140), `Ew.vec` (:158),
`gatherFill` (:164), `align` (:180), `dyadic` (:201), `keyed` (:207) total. The verb's type fact is the witness
`Eval.ewType v t u = some rt` that `Prog.Fn.dy` already carries (approval Ap2); answers by K3. `Ew.zip` (:112) is
deleted: its callers hold two columns over one index. `align`'s nine kernel reads (:187–197) use K1 and
`KernelWF/{Gather,Raze}`; its two count checks (:198) become casts by size theorems. Fix the fixtures :397–463.

**D4.** `Scan.lean`: every `Ops.*` listed in K4's brief answers its payload bare (approval Ap7), by K4's theorems;
the `(Arr.of …).toOption` reads (:64, :68, :79, :100) become `Arr.mk`. `lastBy` (:68) keeps a domain condition:
it follows approval Ap5. `byKey` (:86) reads a boxed list: it follows approval Ap3.

**T1.** Write `leetq/LeetQ/Rel/TotalCheck.lean` as section 6 of the plan describes. At this stage it must fail and
print every offender; that list is the progress meter of the later waves. Edit no other file.

**D5.** `Algebra.lean` :334–700. Delete `Vals.ofParts` (:375), `Cols` (:379), `cols` (:385), `ofCols` (:392),
`longsP` (:397) per approval Ap1 and give `Vals.pick`, `Vals.raze` the count-indexed signatures of the
"Statements" block; prove `join_len` (`join` :478), `cross_len` (`cross` :496) and that a raze's count is the sum
of its parts' counts. `arrDense` (:334) takes `orderKind a = some k`. `setIds` (:527) takes typed offsets and uses
`rankSlices_size`; `setId` (:541), `thin` (:551) follow. Then every op of `section Gen` (:566 `le` … :682
`symDiv`) is its body with `do`, `←`, `pure` removed. Do not touch :700–1604; D6 owns it and assumes your
signatures as the plan writes them.

**D6.** `Algebra.lean` :700–1604. `groupedP` (:701) builds `Cuts` from `runStarts_group` (:1271) and never calls
`Parted.of?`; `boxP` (:709), `memP` (:713), `runsP` (:720), `runs`, `familyP` (:730), `family`, `transposeP`,
`transpose`, `group` (:744), `mem` (:754), `existsImage` (:760), `pair` (:765), `prod` (:786), `junc` (:807),
`injConv` (:814), `mapVal` (:818, witness `nullBits a = some nb`), `foldOver` (:824),
`uncons` (:837), `est` (:850), `entire` … `surjective` (:854–871) total. `mem`, `existsImage`, `setId` take the
flat form (approval Ap3). Checks :880–1060: `ok`, `okFlat`, `St` (:986) lose their `Except`. Theorems :1200–1250
(`Vals.ofParts_atom`, `longsP`, `cols`, `conv` lemmas) are deleted with what they describe, or restated.

**D7.** `Struct.lean` :20–230: `concat`, `take`, `drop`, `reverse`, `rotate`, `index`, `packed`, `scatter`,
`amend` (:89), `partedP` (:119), `boxed`, `parted`, `cutP` (:135), `cut`, `pairsP` (:150), `eachRightP`,
`eachLeftP`, `eachLeft`, `eachRight`, `flipP` (:181), `flip`, `indexPartedP` (:197), `indexParted`, `dotP`,
`til` (:218), `enlist` (:221), `same` (:226). Kernel reads by K1–K3; offsets a kernel wrote get a `Cuts` proof,
never `Parted.of?`; `til` past `USize` is decided in the op; the D sites (:96, :122 via `cutP`, :138, :186) follow
approval Ap5. Restate the in-file theorems about these ops (:590–1100) and the fixtures `ans`/`ansP`/`pl`
(:1183–1240).

**D8.** `Struct.lean` :232–372: `keyCodes` (:239), `ej`, `ij`, `colValue`, `keyGroups` (:272), `aj` (:283), `wjP`
(:297), `wj`, `wjBy` (:333), `raze` (:347), `like` (:355), `ss` (:366). The arity, type and row-count checks
(:240–245, :273–276, :284, :298, :337) disappear into the typed `KCol` of R2 and a `Vector` of column pairs; if
R2's type does not carry one of them, stop and report which. `like`/`ss` follow approval Ap5.

**D9.** `Chess.lean`, `Blocks.lean`, `Wumpus.lean`, `Circuit.lean`: every definition is its body with `do`, `←`,
`pure`, `foldlM` removed (`Chess.unions` :32 becomes a `foldl`). `Chess.mateIn1` (:137) iterates the rows of `tp`
instead of `head?` (:142). `Blocks.plan` (:42) becomes a `hylo` (`Algebra.lean` :843) over the frontier with the
unseen-state count as measure and answers per approval Ap8. Fix each file's `Checks` section.

**S1 / S2.** `SpecFind.lean`, split at :1700. Every theorem with a hypothesis `op … = .ok R` is restated with `R`
replaced by the op's value; `bind_ok` (:1675), `keyed_ok` (:2001) are deleted. `ofExcept` (:210), `ix_mapM`
(:213), `pair_cst_left/right` (:261, :267) and every `ofExcept (elem …)` statement stay: they are qlean's partial
spec of a q verb, not an op (section 5). S1 also repairs `Spec.lean` if a statement there names a changed op.

**S3.** `SpecScan.lean`: restate each theorem whose hypothesis is `Ops.x … = some r` with the op's value.

**S4 / S5.** `SpecStruct.lean`, split at :2000. Restate the theorems of section 5's list; delete `ofPart_enc`
(:626) and `toList_ofCols` (:2026) with the declarations they describe.

**S6.** `SpecAmend.lean`: `foldM_inv` (:152) becomes the invariant of the total fold R2 left in `amend`; restate
`amend_round` (:67), `amend_round_ranked` (:300), `amend_verb_toList` (:416), `amend_verb_toList_long` (:568),
`amend_rel_long` (:590).

**S7.** `SpecKey.lean`: delete `mapM_pair_ok` (:59); restate `keyCodes_long` (:463), `ej_long` (:497), `ij_long`
(:521), `aj_groups` (:775), `aj_long` (:2535), `wj_tail` (:2739), `wj_groups` (:2887), `wj_long` (:2992),
`wj1_long` (:3017), `wj_rel` (:3437), `wj1_rel` (:3465), `aj_rel` (:3556).

**D10.** `Prog.lean` :1–840: `overP` … `lamCount` (:35–63), `liftV`/`liftV_ok` (:85, :89) deleted, `tilKey`
(:246, decided in the op), `enumIn`, `ordJoin` (:255, witness `(cmpOp v).isSome`), `ajRun`, `wjRun`, `pairV`,
`sectVal` (:278), `lowZeroArr` (:286), `Vals.pick` (:292, now D5's), `RelV.sel`, `Fn.apply` (:301; `mono`/`cst` on
any key, since `Alg.mapVal` leaves the key untouched), `testKey`, `ranMul` (:330, approval Ap5), `asTest`, `compV`
(:344, `Alg.comp` at any `Obj`), `run` (:357), `Fn.Sound` (:474), `Sound` (:490), `run_sound` (:666) in the form
of the "Statements" block. The `Prog` inductive (:121) changes only as approval Ap4 says.

**S8.** `Prog.lean` :840–2428: restate every `*_prog` theorem (:926–1655), `comp_run` (:1334) and `conv_run`
(:1647) without `(h : P.run = .ok R)`; the `*_den` theorems do not change. Fixtures :2326–2428.

**D11.** `Group.lean`: delete `ok_of_map_ite` (:41); restate `codes_range` (:182), `codes_long_bytes` (:188),
`runsP_long` (:210). `Norm.lean`: `exec` (:331) and `exec_sound` (:334) lose `Except` and the `hr` premise.
`Bench/Main.lean`: `timedE` (:49), `io` (:69), `listR` (:194), `sumR` (:198), `foRR` (:249), `encCol` (:284) lose
`Except`; what is left is CLI parsing (:297, :431–435) and the checksum assertion (:444), thrown as `IO.userError`.

**C1** (sonnet, mechanical). Delete what has no caller left: `Arr.of` (`Core` :102) unless D1's parser uses it,
`Arr.ofPart` (`Algebra` :43), `Find.list/onKey/vec/dense`, `Ew.vec`, `Parted.of?` if unused. Make
`TotalCheck.lean` pass. Run the full `lake build` of `LeetQ` and `bench` once.

## 4. Waves

| wave | packages (Lean agents at once) | starts when                                      |
|------|--------------------------------|--------------------------------------------------|
| 0    | R1, R2, R3                     | running                                          |
| 1    | K1, K2, K3, K4 (4)             | now; needs no approval                           |
| 2    | D1, D2, D3, D4 (4)             | R1, R3 and wave 1 landed; Ap2, Ap3, Ap5, Ap6, Ap7 |
| 3    | D5, D6, T1 (3)                 | wave 2 landed; Ap1                               |
| 4    | D7, D8, D9 (3)                 | wave 3 and R2 landed; Ap8                        |
| 5    | S1, S2, S3 (3)                 | wave 4 landed                                    |
| 6    | S4, S5 (2)                     | wave 5 landed                                    |
| 7    | S6, S7, D10, S8 (4)            | wave 6 landed; Ap4                               |
| 8    | D11 (1)                        | wave 7 landed                                    |
| 9    | C1 (1)                         | wave 8 landed                                    |

Nine waves after the running one. Critical path:
`R1 → D2/D3 → D5 → D7/D8 → S1/S2 → S4/S5 → D10 → D11 → C1`.

Where parallelism does not help:
- The modules form one import chain, and an op's callers and theorems live in the NEXT file of the chain. A file
  cannot be built green before its imports are, so waves 3 to 9 are serial however many agents are free; inside a
  wave the only parallelism is two agents on disjoint line ranges of one file, or sibling files.
- Keeping each old name as `pure (total op)` (as `conv`/`convArr` and `cols` are today) would keep later PROGRAMS
  compiling but not later PROOFS, which unfold the op's body (`simp only [find, …, bind, Except.bind]`, `Find`
  :1196); it would add a second pass and a duplicate of every op, so it is not planned.
- Wave 1 is the only work that can start today without an approval. Waves 8 and 9 are one agent each.
- Between waves the branch is red below the wave just landed; only C1 ends with the whole package green.

## 5. The proof files

| file         | `Except` lines | lines naming `.ok` | theorems to restate |
|--------------|----------------|--------------------|---------------------|
| `SpecFind`   | 94             | 126                | every `op … = .ok R` |
| `SpecKey`    | 10             | 21                 | 12                  |
| `SpecStruct` | 17             | 35                 | about 27            |
| `SpecAmend`  | 5              | 15                 | 7                   |

Disappear when the op is total, with no restatement:
- the `bind`, `Except.bind`, `pure`, `Except.pure` names in `simp` sets: 20 lines in `SpecFind`, 7 in `SpecKey`,
  14 in `SpecStruct`;
- the helper lemmas about a successful bind: `SpecFind` `bind_ok` :1675, `keyed_ok` :2001; `SpecKey`
  `mapM_pair_ok` :59; `SpecStruct` `ofPart_enc` :626, `toList_ofCols` :2026.

Need a restated theorem:
- `SpecFind`: every theorem whose hypothesis is `op … = .ok R`; `mapM_spec_words` :2050 if its `F` becomes a
  function.
- `SpecKey`: the 12 theorems in S7's brief.
- `SpecStruct`: `cut_rel` :218, `raze_rel` :239, `concat_rel` :253, `flipP_segs` :659, `flipP_rel` :758,
  `pairsP_segs` :778, `eachRightP_segs` :852, `eachLeftP_segs` :881, `eachRightP_rel` :912, `indexPartedP_segs`
  :1445, `indexPartedP_rel` :1609, `ej_rel_codes` :2057, `ej_rel_lane` :2114, `ij_rel_codes` :2358,
  `amend_indices` :2620, `amend_toList` :2669, `like_toList` :2837, `like_rel` :2887, `ss_rel` :2978, `til_rel`
  :3076, `enlist_rel` :3105, `eachLeftP_rel` :3163, `same_rel` :3187, `dotP_rel` :3207.
- `SpecAmend`: nothing is free. `foldM_inv` :152 becomes a fold invariant over a total step; `mapM_ok_zipWith`
  :558 and the five `amend_*` theorems are restated.

Do NOT disappear: about 60 of `SpecFind`'s 94 lines are `ofExcept (elem v h …)`. That is qlean's own semantics of
a dyadic verb (`QLean.Dep.elem`, `Dep/Dyadic.lean` :49), a partial map read as a relation. Making the leetq ops
total does not touch it. It goes only if `elem v h` is proved to answer under `h : ewType v a b = some c` and the
laws are restated with `graph`; whether that holds for every verb was not determined (section 7).

The restatement is uniform: `theorem op_rel {R} (h : op x = .ok R) … : R.rel = spec` becomes
`theorem op_rel … : (op x).rel = spec`, and the proof's first step changes from `simp only [op, bind, Except.bind]
at h` to unfolding `op` in the goal. It is a rewrite of each proof's opening, not of its argument.

## 6. The end check

A Lean module, `leetq/LeetQ/Rel/TotalCheck.lean`, run by
`./scripts/cap lake -d leetq build LeetQ.Rel.TotalCheck`; it fails elaboration and prints the offenders.
It has two parts, and both enumerate obligations, not records:

1. The required ops, as typed ascriptions. One `example` per op of the algebra listed in `leetq/CLAUDE.md` and per
   program, stating the type it MUST have, e.g. `example : Rel A B → Rel B C → Rel A C := Alg.comp`,
   `example : Prog A B → RelV A B := Prog.run`, `example : Board → V := Chess.M`. A deleted or renamed op fails to
   resolve; an op that still answers `Except` or `Option` fails to typecheck. The list:
   - `Alg`: `le inter union zero top idU conv comp dom ran antiJoin diff corefl isCorefl leftDiv rightDiv symDiv
     transpose mem existsImage pair prod junc injConv mapVal foldOver uncons hylo est thin entire
     simple isMap injective surjective`;
   - `Prog.run`, `Norm.exec`. `run` is one function on the `Prog` inductive, so every constructor is covered by
     its totality; the check also reads `Prog`'s constructor list from the environment and asserts none takes an
     `Except`-typed argument;
   - `Chess.{T,K,W,B,P,M,isMate,mateIn1}`, `Blocks.{T,R,M,move,same,plan}`, `Wumpus.{uniq,views,tell,agent}`,
     `Circuit.{adder,answer}`.
2. The sweep, from the environment. A command walks every constant whose module is under `LeetQ.Rel` or `Bench`
   and reports each whose TYPE or VALUE uses `Except`, `Except.bind`, `Except.error`, `ExceptT`, or (approval
   Ap7) whose result type is `Option` and whose name is not in the short list of fast-path selectors. It reads
   `ConstantInfo.getUsedConstantsAsSet`, so a `do` block is seen through the `Bind` instance it elaborates to; no
   text is matched. `Bench`'s `IO` is exempt by its monad, not by name.

Deleting an op cannot make it pass (part 1 names it); hiding a failure behind `Option` or in a helper cannot
either (part 2 walks every constant). The exemption list of part 2 is the one hand-written record; it is printed
on every run.

## 7. Not determined

- Whether each dispatch kernel answers on EVERY well-formed encoding at a type it claims (`findColumn`,
  `memberColumn`, `binColumn`, `matchColumn`, `takeColumn`, `dropColumn`, `rotateColumn`, `shiftColumn`,
  `dyadColumn`, `monColumn`, `groupedOver`, `gradeColumn`). qlean has only `_type` theorems for them;
  `reverseColumn` is known to decline `syms`. K1–K4 find out; each declined case is an Ap6 decision.
- Whether `QLean.Dep.elem v h` is total under its `ewType` witness (decides 60 `ofExcept` lines of `SpecFind`).
- The signatures R1 and R2 land with, and whether R2's typed `KCol` carries the row count and the arity that D8
  needs; D8's brief stops and reports if not.
- The exact flag for building leetq from a worktree (`-K qlean=…`) was read from `lakefile.lean`, not run.
- `Scan.lean`, `Group.lean`, `Norm.lean`, `Bench/Main.lean`, `SpecScan.lean` bodies were read only at the lines
  listed; their package sizes are estimates. The source counts in section 1 are per line; one line serving several
  kernels (`Find.vec` :47) is one source.
- Whether `Ops.overBy`/`Ops.grade` decline by TYPE (class T) or by encoding (class K): they are counted under K.
- The exact kernel signatures in the "Statements" block were read off call sites, not off qlean's definitions.
