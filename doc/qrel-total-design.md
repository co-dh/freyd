# leetq `Rel k v` as the one executable relation, every op total

Design only; nothing in the repo was edited. Sources read: `leetq/LeetQ/Rel/{Core,Algebra}.lean` (HEAD 2841a6a),
commit 4bb2b24, qlean at `/data/tmp/hs4/qlean` (`Value.lean`, `Kernel/{Structural,Sort,Coc}.lean`), the freyd index.
Classes: (a) unreachable under `Arr`'s `Enc.WF`, a proof removes it; (b) reachable only for inputs the op should
not accept, a type removes it; (c) genuinely reachable.

## 1. Where each `Except` comes from

Every op in `Alg` fails only through nine shared helpers. `cols` (:313) is `pure` and never fails.

| helper (Algebra.lean)   | failing call                                  | condition                                                        | class | fix |
|-------------------------|-----------------------------------------------|------------------------------------------------------------------|-------|-----|
| `Arr.ofPart` :42, `ofCols` :320 | `Arr.of` (Core :102) decides `WFAt`    | kernel answer not `n` WF elements of `t`                         | a     | take `h : Enc.WF t n e` (`Arr.mk`); one WF lemma per producing kernel |
| `pick` :204             | `gatherColumn` = `none`                       | `alp` on a non-float type; no `rowWidth`; `bytesOf` = `none`; index shorter than `m*8` | a | `gatherColumn_isSome` from `x.wf`; index is `.bytes i` with `m = len i` |
| `pick`, `raze`, `codes` | `gens` :194                                   | general list whose payload is not `.gen`                         | a     | `Enc.WF .general n e` forces `.gen xs` (as `Arr.gen_size`, Core :53) |
| `raze` :213             | `razeColumn` = `none`                         | no parts; boolean part not `bits`; symbol part not `syms`/`enum`; `bytesOf` = `none` | a + b | parts as `c × Array` (non-empty by type); rest from WF |
| `empty` :221            | `Enc.ofAtoms t #[]` = `none`                  | never: `#[].all` holds                                           | a     | `ofAtoms_isSome` (qlean `Value.lean` :1139) already proves it |
| `codes` :274            | `groupIdsColumn` = `none`                     | `orderKind t = none` outside symbol/guid/boolean; `bytesOf` = `none` | a | `orderKind` is `none` only at symbol, guid, general, all handled earlier |
| `rangeOffsets` :234     | `enumIds`/`enumIdsFoR` report a row out of range | offset outside `0..card`                                      | a, or fallback | return `none` and let `codes` take its grouping branch: both are faithful codes |
| `single` :293, `two` :485, `tuples` :368 | size test on `Array Code`    | `codes` answered a different number of parts than given          | a/b   | `codes : (cs : Vector _ m) → Vector Code m`; `tuples` takes `c0` and the rest |
| `arrDense` :299         | `orderKind a = none`; `Enc.bytesOf` = `none`  | symbol, guid, general have no sort layout                        | b + a | hypothesis `orderKind a = some k` (a class with one instance per type) |

Other local failures:

| site                        | condition                                   | class | fix |
|-----------------------------|---------------------------------------------|-------|-----|
| `setIds` :447               | `o.size < 8`; `rankSlices` answer has the wrong count | b + a | offsets typed `Arr .long (g+1)`; `rankSlices_size` from its Lean body |
| `thin` :471                 | `cs.size ≠ big.size`                        | b     | one array of `(Kind × ByteArray × Bool)` |
| `leftDiv` :581–583          | `ycs[0..2]?` missing                        | a/b   | the `Vector` `codes` above |
| `groupedP` :615             | `Parted.of?` = `none`                       | a     | build `Cuts` from `runStarts_group` (:1271) instead of re-deciding it |
| `memP` :629, `mem` :670, `setId` :463 | `longBytes` = `none`              | a     | `Enc.WF .long` admits only `bytes` and `foR` |
| `Parted.box` (Core :555)    | `sliceColumn` = `none`                      | a     | `sliceColumn_isSome` under WF and in-range cuts |
| `Parted.ofBoxes` (Core :576), so `mem`, `setId` | a box that is not a vector of `v` | c | narrow the domain: these take the flat `Parted v` (as `memP`, `setIds` do); a boxed list is output only |
| `mapVal` :755               | `nullBits a = none`                         | b     | hypothesis `nullBits a = some nb` |
| `uncons` :773               | `n = 0`                                     | b     | argument `Arr B (n+1)` |
| `hylo` :780                 | out of fuel                                 | c     | a measure `m : α → Nat` with `¬done x → m (step x) < m x`: well-founded recursion, no fuel |

Per op, the helpers that carry its failure:

| op                                  | helpers                                   |
|-------------------------------------|-------------------------------------------|
| `conv`                              | none; it is `pure (convArr …)` already     |
| `le`, `isCorefl`, `entire`, `simple`, `injective`, `surjective` | `codes`, `two`/`single` |
| `inter`, `comp`, `antiJoin`, `pair` | `codes`, `two`, `pick`, `ofCols`          |
| `union`, `junc`                     | `raze`, `codes`, `pick`, `ofCols`         |
| `zero`                              | `empty`, `ofCols`                         |
| `top`, `prod`                       | `pick`, `ofCols`                          |
| `dom`, `ran`                        | `codes`, `single`, `pick`, `ofCols`       |
| `corefl`, `foldOver`, `est`, `mapVal` | `arrDense`, then `pick`/`ofCols` |
| `leftDiv`, `rightDiv`, `symDiv`     | all of the above, plus `setIds` in `symDiv` |
| `transpose`, `group`, `runs`, `family` | `codes`, `pick`, `groupedP`, `Parted.box` |

Two facts the classification rests on, both to be checked when the work starts:
- `Enc.bytesOf` was read through its callers (`Arr.dense_long`, Core :204), not its definition; the claim is that
  it answers `some` for `bytes`, `foR` and `alp` under WF.
- Which WF/size lemmas qlean's `Verify/` already has was not enumerated. Known: `ofAtoms_isSome`,
  `gatherColumn_type`, `razeColumn_type`, `sliceColumn_type` (shape only), `val_size8`, `runStarts_spec`.

One (c) that the code does not check today: counts are passed as `n.toUSize`, and `cross` (:416) computes
`(n * m).toUSize`. A product past `2^64` wraps and the kernel is called with a wrong count. Several existing laws
already carry `hm : m < USize.size` (`Arr.dense_long`, `groupIds_long_faithful`). Proposal: `Arr` carries
`n < USize.size`; `cross` and `raze` are the two places a count is multiplied or added, and a result that does not
fit is memory exhaustion, the same event as a failed allocation in the C kernel. It ends the process (q's
`'wsfull`); it is never a value and never a default. This adds a field to `Arr`, so it needs his approval.

`pick` is total with q's fill; in-range is a premise of the laws, not of the op.

## 2. Ordered plan, by shared helper

1. `Arr.ofPart`/`ofCols` take a WF proof. Add the per-kernel WF lemmas the callers need: `gatherColumn`,
   `razeColumn`, `Enc.ofAtoms #[]`, `concatBits`, `Ew.val`/`Ew.mon`, `overGroups`, `tilLongs`, `sliceColumn`.
   Everything else depends on this step.
2. `gens`, `empty`, `longBytes`: three short WF case splits. `zero` is total after this and step 1.
3. `pick` total (`gatherColumn_isSome`). `top`, `prod`, `Cols.rows` follow.
4. `raze` total, non-empty by type. `junc` follows.
5. `codes` as `Vector → Vector`; `rangeOffsets` answers `Option` and falls back; delete `single`, `two`, the
   `ycs[i]?` tests. `le`, `inter`, `union`, `comp`, `dom`, `ran`, `antiJoin`, `isCorefl`, `entire`, `simple`,
   `pair`, `leftDiv`, `rightDiv` follow. This is the step that clears the list he named.
6. `arrDense` and `mapVal` behind `orderKind`/`nullBits` hypotheses. `corefl`, `foldOver`, `est`.
7. `Parted`: `groupedP` from `runStarts_group`, `box` total, `mem`/`setId` on the flat form, `setIds` typed.
   `transpose`, `group`, `family`, `symDiv`, `existsImage`.
8. `uncons` on `n+1`, `thin` zipped, `hylo` by measure.
9. Callers: `Prog.lean`'s `run` and `run_sound : run P = ok R → …` lose the `ok` premise; `Struct`, `Circuit`,
   `Wumpus`, the `#guard`s lose `ok (…)`. 4bb2b24 is the pattern (6 files, +109 −111 for two functions).

Size: steps 1 and 3–5 are proofs about kernel Lean bodies and are the bulk; steps 2, 6, 8 are small.

## 3. "Only keep 7": what happens to 1–4

| # | type        | role found in the code                                             | proposal |
|---|-------------|--------------------------------------------------------------------|----------|
| 1 | `RelSet`    | semantics; `Prog.lean` already states `den P` in it                | keep, it is not an implementation |
| 2 | `FinRel`    | stated in `AOP.A9_2_Edit` (3 decls) and `leet.L1` (2)              | delete after porting those two |
| 3 | `SortedRel` | stated in no module outside `A6_FinRel`; `leetq/LeetQ/QRel.lean` re-states its interface | delete |
| 4 | `RelRep`    | 13 AOP modules, 84 statements; 32 of them name `enum`/`arr`/`vec`  | see below |

- Importers of `AOP.A6_FinRel` by `module_need`: 18 modules (17 `AOP.*` and `leet.L1`).
- A denotation for 7 exists: `Rel.Holds` (Core :598) and `idU_holds`, `convArr_holds`, `conv_holds`, `outl_holds`,
  `outr_holds`. Missing are the laws for `comp`, `inter`, `union`, `zero`, `top`, `dom`, `ran`, the divisions;
  `Prog.lean`'s header lists them as "no theorem yet". Once the ops are total they read like 4's `rel_comp`:
  `(comp R S).Holds = R.Holds ≫ S.Holds`, with no `= .ok` premise.
- 7 cannot replace 4 inside `AOP/`, for two reasons. `AOP` must not depend on qlean's C kernels (leetq is a
  separate lake package for exactly that). And 7's objects are `QAtomicType`; `RelRep.enum (f : K → List V)` is a
  function over arbitrary Lean types, which is what the chapter derivations evaluate by `rfl`.

Recommendation: delete 2 and 3 and the `pairs` constructor of 4, which are the parts that store rows; keep
`RelRep.enum`/`arr`/`vec` in `AOP` as the list programs the derivations produce. They store no relation, so 7 is
then the only implementation that holds data, and its laws go straight to `RelSet`, not to 4. Not "keep 4 as the
reference spec 7 is proved equal to": that keeps two copies with a comparator between them.
Open: the counts above are over statements; uses inside proof bodies were not audited. Removing a constructor is a
data-structure change and needs his approval before any port.

## 4. Ops the Rel language still needs

All of `⊤`, `𝟙`, `\`, `/`, `/ₛ`, `Λ`, `∋`, `E`, `⟨R,S⟩`, `×`, `[R,S]`, `est`, `thin` exist. What is missing is
mostly the object they are indexed by.

| missing                         | today                                                  | cost |
|---------------------------------|--------------------------------------------------------|------|
| a carrier as an object          | `top`, `leftDiv`, `rightDiv`, `symDiv`, `entire` each take `Ua`, `Ub` as loose `Arr`s | no kernel; an object is a type with its universe column |
| `𝟙`, `∈`                        | `idU` shares one column; `∈` is `conv` of `∋`          | no kernel |
| `⊤`                             | `cross`: `tilLongs`, two `Ew.val`, two gathers         | exists, `n·m` rows |
| complement `¬R`                 | absent                                                 | `anti` on pair codes: `codes`, `member`, `where`, gather |
| `est(R)`, `thin(Q)` for any `R` | only `≤`/`≥` on longs (`overGroups`), Pareto (`thinSweep`) | by definition `∋ ∩ (∈ \ R°)`: one `leftDiv`; a fused kernel is an optimisation with a theorem |
| `⦇S⦈` for any algebra           | only `Coc.Over` reductions                             | one `comp` per element through `hylo`; no new kernel |
| `F(R)` on lists                 | absent as an op                                        | `comp` on the flat `Parted`, offsets kept: one join |
| `graph(f)` for any `f`          | only `Ew` monads (`mapVal`)                            | one `Ew` kernel per `f`; none for an arbitrary Lean function |
| products as objects             | `Tab`, `Rel2`, `SumRel` are separate structures        | no kernel; `Prog.lean` already has `Obj` |

## 5. Names

- 7 is `Rel`: type `Rel k v`, namespace `LeetQ.Rel`, the language he named. Its doc comments stop saying "RelRep"
  (Core :2, Algebra :2, `leetq/CLAUDE.md`, `Prog.lean` :2, `Spec.lean` :2); "QRel" stays chat shorthand only.
- `RelRep` then means AOP's type alone, and the two-`FinRel` clash ends with the deletion in section 3.
- `leetq/LeetQ/QRel.lean` is not 7: it is `SortedRel`'s interface over qlean columns and imports
  `AOP.A6_FinRel`. It goes with `SortedRel`, or is renamed, before anyone reads "QRel" as the survivor.
