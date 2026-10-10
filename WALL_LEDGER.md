# WALL LEDGER — schema-supplied vs hand-invented correctness in the AOP derivation corpus

Measured at worktree `wt-ledger` (detached at master `4f0c51c`).  Corpus: all 71 `Freyd/L*_derived.lean`
files plus the driver instances `L53_auto.lean`, `L322_dp.lean`, `L279.lean`, and the knapsack demo
(`A8_4_Knapsack.lean` abstract + `AutoDeriveThin.lean` `namespace Knapsack` concrete).  All are sorry-free.

## What is being measured

Every derivation splits into (1) the efficient PROGRAM — identified with a catamorphism/hylomorphism by a
fold-uniqueness law, or emitted by a driver — and (2) the CORRECTNESS, which either transports mechanically
or bottoms out in a problem-specific invariant / spec-match induction (the "eureka", the wall for any
auto-deriver).  This ledger classifies (2) per file.

Classification values (derived-layer classification; base-file provenance is traced in the note):

* **schema** — no new problem-specific induction in the file.  Allowed content: `rfl` base/step equations,
  projections, congruence/lockstep agreement inductions that mirror the base program step-for-step,
  generic data-structure modeling lemmas (`find?` models an assoc list), and REUSE of the base file's
  `solve_correct`-class theorem.
* **hand** — a new problem-specific invariant or spec-match induction had to be devised in this file
  (named, with `file:line`).  Spec↔generator characterisations (`gen_sound`/`spec_gen`-class) count here,
  per the corpus's own driver docstrings ("the genuinely problem-specific inductions").
* **borderline** — neither cleanly: new inductions exist but carry no independent spec content.

Method: all 75 file headers read in full; declaration lists extracted for every file; the key correctness
lemma and its dependencies read in code for every file classified hand/borderline and for ~15 schema files
(L1, L110, L124, L253, L271, L300, L322, L35, L367, L53_auto, L763, L279, L322_dp, knapsack, L139).
Headers were NOT trusted for the verdict where it matters: one stale header was found (`L322_derived.lean`
claims correctness is "RE-PROVED"; the code at `L322_derived.lean:177-213` reuses `solve_correct_inf`
through a mechanical congruence bridge) — all hand/borderline verdicts below are code-based.

## Ledger

"Program origin" names the law/driver that produces/certifies the program.  In every fold file the human
still CHOOSES the carrier and reads off base/step; the law contributes construction + uniqueness.  In the
hylo files the program is written as a well-founded recursion and the law certifies it as the unique
hylomorphism of the chosen coalgebra.

### Cons-list catamorphisms (`CL.consFold_unique`, A6_GenFold) — 31 files

| file  | carrier (the human choice)               | inv    | invariant / note                                        |
|-------|------------------------------------------|--------|---------------------------------------------------------|
| L5    | CPS `List Int → Nat × Nat` (two radii)   | schema | lockstep bridge `foldCL_ofList`; reuse L5 correctness   |
| L13   | `Int × Option Int` (lookahead)           | schema | bridge `romanCL_ofList`; reuse `roman` value proof      |
| L14   | `Option (List Int)` (none = no string)   | schema | bridge `bridge`; reuse `lcp` correctness                |
| L19   | `Nat × List Int` (distance-from-end)     | schema | take/drop agreement lemmas; reuse                       |
| L26   | `List Int` (suffix head = lookahead)     | schema | `dedupFn_head_eq` + `foldFn_ofList`; reuse              |
| L35   | `Nat` + verified `lowerBound` bridge     | schema | `lowerBound_eq_insertPosFn` L35:141 — split-point       |
|       |                                          |        | uniqueness from two REUSED specs; no new invariant      |
| L49   | `List (List (List Int))` (groups)        | schema | bridge `bridge`; reuse `group_correct`                  |
| L56   | 2 folds: sort list + CPS `(Int×Int)→…`   | schema | `mergeSortedFold_eq`; reuse `merge` correctness         |
| L66   | para-as-fold `List Int × List Int` copy  | schema | `pr_ofList`; reuse `valueLE`/`plusOne_correct`          |
| L125  | `List Int` rebuild (O(n) cons order)     | schema | `slToCL` reshape bridge; reuse decision iff             |
| L128  | `AHashSet` build; phase 2 hand-written   | HAND   | run-start invariant: `pigeon` L128:88, `runStart_P1/P2` |
|       |                                          |        | :225, `Ach` :344, `hash_ach`/`hash_dom` :377/:384;      |
|       |                                          |        | base `scanAux_inv` explicitly NOT reused                |
| L139  | `List α × List Bool` (course-of-values)  | HAND   | `table_spec` L139:151 — cell k decides `Seg` on the     |
|       |                                          |        | length-k suffix; per-step `stepBreak_true_iff` reused   |
| L190  | CPS `List Bool → List Bool`              | schema | `revAcc_ofList_append`; reuse                           |
| L205  | residual `AHashMap→AHashMap→List→Bool`   | schema | `Models`/`models_insert` refinement + `isoGoH_eq`; reuse|
| L206  | CPS accumulator `List Int → List Int`    | schema | `revAcc_ofList` = core `reverseAux`; reuse `rev_rev`    |
| L213  | `Int × Int` pair-DP (both ring passes)   | schema | `foldLCL_ofList`; reuse circular-robber correctness     |
| L234  | `List Int` rebuild                       | schema | bridge; reuse `palin_correct`                           |
| L238  | 2 folds: CPS `Int→List Int` + pair       | schema | `foldPre_ofList`/`foldSuf_ofList`; reuse                |
| L242  | `List Int` (insertion sort)              | schema | `isortFold_ofList`; reuse anagram decision iff          |
| L252  | threshold CPS `Int → Bool`               | schema | `noAdjFromC_ofList`; reuse                              |
| L253  | `Nat` max-fold, interval list fixed      | schema | 1-line transports of `rooms_achievable`/`_dominates`    |
|       |                                          |        | (L253:117,124)                                          |
| L271  | encoder fold + decoder HYLO              | schema | round-trip REUSED from `L271.round_trip` via fuel       |
|       |                                          |        | bridge `decodeFuel_some_hylo`                           |
| L283  | `List Int × Nat` (kept + zero count)     | schema | `h_ofList` = filter/replicate; reuse                    |
| L303  | CPS `Int → List Int` (prefix sums)       | schema | `foldScan_ofList`; reuse range-sum correctness          |
| L383  | `Bool` all-fold, both lists fixed        | schema | `canBuildFold_ofList`; reuse decision iff               |
| L387  | 2 folds: `AHashMap` count + CPS          | schema | `find?` models `countL`; reuse `firstUniq` correctness  |
| L392  | residual `List Int → Bool` over `t`      | schema | `matchC_ofList`; reuse decision iff                     |
| L435  | 2 folds: sort + threshold CPS            | schema | `foldKeptSorted_eq`; reuse greedy optimality from base  |
| L724  | CPS `Nat → Int → Option Nat`             | schema | `foldCL_go`; reuse pivot correctness                    |
| L1143 | `List Nat` DP row (`ys` fixed)           | schema | `colCL_ofList`; reuse `solve_correct` (LCS)             |

### Snoc-list catamorphisms (`SL.snocFold_unique`) — 11 files

| file  | carrier                                  | inv    | invariant / note                                        |
|-------|------------------------------------------|--------|---------------------------------------------------------|
| L20   | `Int × Bool` (depth, ok)                 | schema | base/step are `foldFn`'s own `rfl` equations; reuse     |
|       |                                          |        | `solve_correct` (`neverNegP`/`depthP` NOT re-derived)   |
| L55   | `Nat × Nat × Bool` (idx widened in)      | schema | reuse jump-game correctness                             |
| L62   | DP row `SnocList Nat Nat`, width fixed   | schema | `rowFold_snocs` bridge; reuse `solve_correct`           |
| L118  | `(table, current row)`                   | schema | `buildRows_snoc` bridge; reuse `pascal_correct`         |
| L169  | `(candidate, count)` Boyer–Moore         | schema | `foldSL_foldl`; reuse `majority_correct` (the `BMInv`   |
|       |                                          |        | eureka lives in base `L169.lean`)                       |
| L171  | `Int` (Horner base 26)                   | schema | reuse `colNumber_correct`                               |
| L217  | `AHashSet × Bool`                        | schema | `inv`: `mem` models `memB` (refinement); reuse          |
| L300  | `Array Int` patience tails               | HAND   | `PatInv` L300:113 / `patInv_step` :123 — min-last-      |
|       |                                          |        | element-per-length; also bridged to base `solveFn`      |
| L322  | `List (Option Nat)` course-of-values     | schema | `stab` L322d:128 + `entry_eq_dpFuel` :188 (congruence:  |
|       |                                          |        | same recurrence ⇒ same table); reuse `solve_correct_inf`|
|       |                                          |        | from `L322_dp` (header stale: claims re-proof)          |
| L338  | `Array Nat` popcount table               | schema | `dpFold_toList`; reuse `solveFn_eq_target`              |
| L763  | 4-tuple + `AHashMap` lastPos             | schema | `lookupLP_buildLPGo` refinement; reuse `solve_valid` —  |
|       |                                          |        | SOUNDNESS-ONLY headline (base proves no maximality)     |

### Tree catamorphisms (`TB.treeFold_unique`) — 9 files

| file  | carrier                                  | inv    | invariant / note                                        |
|-------|------------------------------------------|--------|---------------------------------------------------------|
| L98   | residual `Option Int → Option Int → Bool`| schema | reuse bounds-generalized `solve_correct`                |
| L100  | residual `Tree Int → Bool` (curried)     | schema | reuse `solve_correct`                                   |
| L101  | residual `Tree Int → Bool` (crosswise)   | schema | reuse `mirror_correct`                                  |
| L102  | difference-list rows `List (List→List)`  | schema | `readoutD_levelsD`; reuse `solve_correct`               |
| L111  | `Nat` (0-as-nil detector)                | schema | reuse `minDepth_correct`                                |
| L112  | `Bool × (Int → Bool)` (nil flag + resid) | schema | `foldC_snd`; reuse `solve_eq_spec`                      |
| L230  | difference list `List Int → List Int`    | schema | `inorderDL_append`; reuse `kthSmallest_correct`         |
| L572  | residual + paramorphism `Bool × Tree`    | schema | reuse subtree correctness                               |
| L617  | residual `Tree Int → Tree Int`           | schema | reuse `merge_correct` (position-lookup spec)            |

### Pair/triple tupling (`SL.tupling`, A6_8) — 6 files

| file  | carrier                                  | inv    | invariant / note                                        |
|-------|------------------------------------------|--------|---------------------------------------------------------|
| L70   | pair (Fibonacci)                         | schema | recurrence `rfl`; projection recovers scalar            |
| L91   | triple `(ways, prevWays, lastDigit)`     | schema | reuse; NB header: "choosing WHICH three quantities to   |
|       |                                          |        | tuple is the whole insight" — program-side eureka       |
| L152  | triple `(minEnd, maxEnd, best)`          | schema | reuse `solve_correct`                                   |
| L198  | pair `(best, prevBest)`                  | schema | reuse `solve_correct`                                   |
| L746  | pair `(reachHere, reachPrev)`            | schema | `pairAlg_eq_alg`; reuse optimality                      |
| L1137 | triple (Tribonacci)                      | schema | projection recovers scalar                              |

### Tree tupling (`TB.treeTupling`, A6_9) — 4 files

| file  | carrier                                  | inv    | invariant / note                                        |
|-------|------------------------------------------|--------|---------------------------------------------------------|
| L110  | `(height, balanced)`                     | schema | naive-spec `balOf_correct` L110d:47 is a trivial unfold |
|       |                                          |        | induction — tupling removed the pair-fold invariant     |
| L124  | `(best, gain)` `Option Int × Int`        | schema | `derivedSolve_eq_solve`; reuse `solve_correct`          |
| L404  | triple `(isNil, sumTrue, sumFalse)`      | schema | `p_node` 4-way case split (mechanical); reuse           |
| L543  | `(height, diam)`                         | schema | `heightOf_eq`/`diamOf_eq` agreement inductions; reuse   |

### Hylomorphisms (`Hylo.hyloFold_unique`, A6_GenHylo) — 9 files

| file  | coalgebra / state                        | inv    | invariant / note                                        |
|-------|------------------------------------------|--------|---------------------------------------------------------|
| L2    | `(carry, xs, ys)`, μ = Σ length          | schema | fuel bridge `addFuel_eq_addH`; reuse value correctness  |
| L9    | digit peel, μ = id                       | schema | `digitsWF_eq_toDigits`; reuse                           |
| L11   | window `(lo,hi)` on `Array`, μ = hi−lo   | schema | `sweep_eq_fuel` + `areaA_eq` (Array/List agreement);    |
|       |                                          |        | reuse achievable/dominates (headline `Nonneg`-cond.)    |
| L21   | `(xs, ys)`, μ = Σ length                 | schema | certifies `mergeFn` itself; reuse `solve_le_spec`       |
| L23   | HEAP drain (`popMin?`), μ = heap size    | HAND   | heap-drain correctness devised here: `popN_sorted`      |
|       |                                          |        | L23d:232, `popN_perm` :259, `sorted_count_ext` :136,    |
|       |                                          |        | `ofList_isHeap` :198; base reuse covers only the OLD    |
|       |                                          |        | `mergeKFn` (per-op heap lemmas from A6_Heap)            |
| L67   | `(carry, xs, ys)` base 2                 | schema | `addBitsRev_eq_addH`; reuse                             |
| L231  | halving, μ = id                          | schema | `pow2Fuel_ge` bridge; reuse                             |
| L367  | upward search, μ = (n+1)−k               | schema | `search_eq_isPerfectSquareFn`; reuse decision iff       |
| L977  | two-pointer `(lo,hi)`, DL output         | HAND   | `valley` L977:117 + `count_ind` :162 + `sorted_ind`     |
|       |                                          |        | :199 — new multiset+sortedness proof (not the base      |
|       |                                          |        | sort-based program)                                     |

### Greedy-theorem instance (A7.2 via `A7_4_Horner`) — 1 file

| file  | route                                    | inv    | invariant / note                                        |
|-------|------------------------------------------|--------|---------------------------------------------------------|
| L104  | generator `S`, greedy refinement         | HAND   | `cataTreeFold_S` L104:72 (spec↔generator) + `alg_mono`/ |
|       |                                          |        | `alg_refines` :136; greedy theorem discharges the rest; |
|       |                                          |        | deliberately does NOT reuse `L104.pathLen_depth`        |

### Driver instances — 5 entries

| file            | driver          | inv        | invariant / note                                        |
|-----------------|-----------------|------------|---------------------------------------------------------|
| L53_auto        | `RunningBest`   | HAND       | `gen_sound` L53a:72 / `spec_gen` :105 — search space =  |
|                 |                 |            | subarray sums; ~104 lines of relational side conditions |
|                 |                 |            | discharged by the driver, 8 omega-class bundle facts    |
| L322_dp         | `DPCount`       | HAND       | `steps_iff_achievable` L322dp:140 (driver reachability  |
|                 |                 |            | ↔ `Achievable` spec, two 4-line inductions); `memo_mem`/|
|                 |                 |            | `memo_lb_step` via base `coinFold_achieves`/`dominates` |
| L279            | `DPCount`       | borderline | NO independent spec: headline `dpSq_min` L279:181 is    |
|                 |                 |            | stated against the driver's own `Steps`; hand-supplied  |
|                 |                 |            | `sqFold_lb` :99 / `sqFold_mem` :114 are mechanical      |
| A8_4_Knapsack   | `thinning_min`  | schema     | abstract instance: all problem obligations (`hmono`,    |
|                 | (A8_1)          | (abstract) | orders) are HYPOTHESES, discharged concretely below     |
| AutoDeriveThin  | `ThinBest`      | HAND       | `gen_iff_choice` ADT:552 (generator = feasible          |
| (Knapsack demo) |                 |            | selections `Choice`) + `step_mono` :516 (dominance      |
|                 |                 |            | survives extension — the §8.4 insight)                  |

## Summary — the measured size of the wall

Corpus: **76 entries** (71 `L*_derived` + 5 driver entries).

| class      | count | entries                                                                       |
|------------|-------|-------------------------------------------------------------------------------|
| schema     |  66   | 65 `L*_derived` + `A8_4_Knapsack` (abstract)                                   |
| hand       |   9   | L23, L104, L128, L139, L300, L977, L53_auto, L322_dp, knapsack demo            |
| borderline |   1   | L279                                                                           |

Within the 71 optimization derivations: **65/71 (91.5%) schema, 6/71 (8.5%) hand**.

The sharper empirical law the table shows:

* **Representation-only changes never needed a new invariant (0/65).**  Hash map for assoc list (L1,
  L205, L217, L387, L763), arrays for lists (L11, L338), difference lists (L102, L230), accumulator/CPS
  carriers (L190, L206, L238, L303, …), tupling (all 10), lookahead/paramorphism carriers (L13, L26, L66)
  — in every case correctness transported by a lockstep agreement induction or a generic
  data-structure-models-the-old-structure lemma, plus reuse of the base file's theorem.
* **Algorithm replacements always needed one (6/6).**  Patience sorting (L300 `PatInv`), two-pointer merge
  (L977 `valley`), hash run-detection (L128 run-start), heap drain (L23 drain sortedness + multiset),
  tabulation-axis flip (L139 `table_spec`), greedy-from-spec (L104 `cataTreeFold_S`).  When the new
  program computes the answer by a different method, a new argument why that method still meets the spec
  had to be devised by hand — every time.
* **The boundary case is L35**: linear scan → verified binary search is an algorithm change absorbed at
  schema level, because both endpoints were ALREADY uniquely characterized by existing specs
  (`insertPos_correct` + `A6_BinSearch.lowerBound` lemmas) and agreement follows from split-point
  uniqueness.  Algorithm changes are schema-absorbable exactly when a reusable uniqueness
  characterisation of the answer pre-exists.
* **Drivers do not eliminate the spec eureka.**  `RunningBest`/`DPCount`/`ThinBest` mechanize the
  relational packaging (~100+ lines per instance), but the spec↔generator characterisation stayed hand in
  3 of 4 concrete instances (`gen_sound`/`spec_gen`, `steps_iff_achievable`, `gen_iff_choice`+`step_mono`).
  The 4th (L279) avoids it only by DEFINING the spec as the driver's reachability predicate.

**The honest ceiling.**  "Schema" above means schema *at the derivation layer*.  Tracing the reuse chain:
every schema file's headline bottoms out in the base `Lxxx.lean`'s `solve_correct`-class theorem, which is
itself a hand spec-match induction there (e.g. L169's Boyer–Moore `BMInv`, L1's `twoSum_correct`, L322's
fuel induction / `L322_dp`'s bridge).  No problem in the corpus has spec-level correctness that was
produced without a hand-invented induction *somewhere* in its chain — the sole arguable exception is L279,
where the spec is the driver's generic `Steps` instantiated at the problem decomposition.  The schemas
therefore RELOCATE and AMORTIZE the eureka (prove the spec once, against the clearest program; re-derive
efficient variants mechanically); they eliminate it only for re-verification under representation change.
That elimination is real and measured: 65 optimization steps, including five hash-map upgrades and ten
tuplings, added zero new invariants.

## Caveats on the classification

1. Every file header was read in full, and the key correctness lemma plus its dependencies were read in
   code for all hand/borderline entries and ~15 schema entries; the remaining ~55 schema entries were
   verified against their complete declaration lists (bridge + `*_ofList` + `*_eq_solve` +
   `*_derived_correct` shape) rather than line-by-line proof reading.
2. Headers can be stale: `L322_derived.lean`'s header still claims correctness is "RE-PROVED", but the
   code reuses `solve_correct_inf` through a congruence bridge — verdicts here follow the code.
3. Judgment calls, flagged: L104 and L322_dp are counted HAND although their hand content is small
   (~30–40 lines of spec↔generator bridging); counting them schema would move the headline from 9 hand
   to 7 hand of 76.  L110's `balOf_correct` and L139's reuse of `stepBreak_true_iff` sit near the line in
   the other direction; L110 is counted schema (a trivial unfold induction against the naive spec, no
   invariant), L139 hand (the per-cell table invariant is new).
4. "Program origin: law" means the human supplies carrier + base/step (or coalgebra + measure) and the
   law contributes the catamorphism/hylomorphism identification and uniqueness.  The carrier choice (CPS,
   lookahead pairing, tupling ansatz, paramorphism copy, nil flag) is genuine per-problem creative input
   present in every file — a program-side eureka this ledger does not count, since it measures the
   correctness wall.  L91's header states this explicitly.
5. Complexity claims (O(n log n), O(n) expected, …) are informal throughout the corpus; Lean verifies
   behaviour, not asymptotics.  This ledger takes the files' complexity story at face value.
