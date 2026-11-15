# Rel: avoiding `cons` — analysis and design

Scope: `leetq/` at 89e3434; a bare `:n` is a line of `LeetQ/Run/Alg.lean`; nothing is implemented; timings are from
the scratch file `/data/tmp/conscost/ConsCost.lean`. Classes: P constructor, S slice, R reduction, M per-element
map, N enumeration (exponential output), Q sequential.

## 1. Inventory

Engine (`Run/Alg.lean`; twins in `Run/CRel{List,Fold}Def.lean`; language in `Run/Lang/{Syntax,Elab,Gen}.lean`):

| op (line)                      | computes                        | why cons / fold                         | class |
|--------------------------------|---------------------------------|-----------------------------------------|-------|
| `consC` :647, `alphaC` :871    | `(y, ys) ↦ y:ys` per row        | B&dM's constructor `α ≜ [nil, cons]`    | P     |
| `snocC` :1107, `ticC` :1417    | `(xs, a) ↦ xs⧺[a]`; `cons inits`| `snoc ≜ (𝟙×τ) cat`, ch. 9–10 snoc-lists | P     |
| `unconsC` :626, `unsnoc` :1076 | first/last element and the rest | `cons°`, `snoc°`; `suffixC` :968 `tail*`| S     |
| `foldRound`…`foldC` :677–:753  | `⦇e, S⦈`, a round per position  | the cons-list fold, unit of every law   | Q     |
| `lengthC` :931, `sumC` :1442   | `⦇zero, π₂ succ⦈`, `⦇zero,plus⦈`| written as their B&dM definitions       | R     |
| `mapC` :761                    | `F(R) = ⦇[], (R×𝟙) cons⦈`       | the list functor as a fold              | M     |
| `subseqC` :1234, `permC` :1140 | subsequences, permutations      | `⦇nil, cons ∪ π₂⦈`, `⦇nil, add⦈`        | N     |
| `thinBodyC` :1267 (`thinL`)    | thinning step, 2 `consC`        | B&dM ch. 8 step                         | Q     |
| `mergeRound` :1302             | 2 `unconsC` + 2 `snocC` a round | accumulator built by `snoc`             | Q     |
| `loopRound` :1381              | left fold, `unconsC` a round    | B&dM p.78 loop over cons-lists          | Q     |

Proofs: `Rel/RepList` (1079 lines: `rep_uncons`, `rep_cons`), `RepPerm` (497: `rep_snoc`), `CRelList` (354),
`RepFold` (883), `CRelFold` (555); also in `RepLambda`, `RepThin`, `RepSubseq`, `RepMerge`, `RepLoop`, `Lang/Test`.

Programs (`Rel/Programs/`, owned by aima):

| file : line            | text                                           | computes                   | class |
|------------------------|------------------------------------------------|----------------------------|-------|
| Prelude :22–25         | `head`,`tail`,`init`,`last` = `cons° π₁` …     | ends of an array           | S     |
| Prelude :26, :30, :38  | `prefix`, `tails`, `ordered` (`tails ∋ cons°`) | prefixes, suffixes, `i<j`  | S     |
| Prelude :28, Mss :19   | `⦇ran(nil), cat⦈`, `segment⦇ran(zero), plus⦈`  | flatten; sum               | R     |
| Prelude :31, :32       | `filter(p)`, `takewhile(p)`                    | keep by predicate          | M     |
| Prelude :29, :37       | `subseq`, `perm` (`add`: `cons`, `cat`)        | enumerations               | N     |
| Edit :21–22, Mss :32   | `ran(r⦇ran(nil), π₂ ∪ ⟨…⟩cons⦈)`               | all arrays over a universe | N     |
| Detab :25, Circuit :22 | same with `snoc`; `ins ≜ ⟨⊤,𝟙⟩cons`            | all strings; one in front  | N     |
| Knapsack :49           | `cpr(a,ps) ≜ ps⦇ran(nil), ⟨⟨⊤a,π₁⟩,π₂⟩cons⦈`   | pair `a` with each element | M     |
| Knapsack :37, :50      | `S ≜ cons within(w) ∪ π₂`, `F(cons)`           | DP step                    | Q     |
| Edit :28, :42, :56     | `step`, `base'`, `step'` (9 `cons`)            | edit-distance column       | Q     |
| Detab :38, :58         | `step`, `op` (5 `snoc`, 2 `cat`)               | output string + column no. | Q     |
| JobShop :30            | `⟨π₁,⟨π₂,…⟩⟩snoc`                              | append the placed job      | Q     |
| Selsort :21, :26       | `perm cons° ok`, `(C⦇ran(nil), select°⦈)°`     | converse of a fold         | Q     |

## 2. Cost (measured, native `LeetQRun`, one core)

| input                   | `Arr.sum` | `length` | `map(𝟙)`             | array-native bound           |
|-------------------------|-----------|----------|----------------------|------------------------------|
| 1 row, L = 1000         | 14 ms     | 125 ms   | 21 ms                | sum: one reduce, ~1 µs       |
| 1 row, L = 4000         | 58 ms     | 540 ms   | 133 ms               | length: `hi − lo`, no pass   |
| 1 row, L = 8000 / 16000 | —         | —        | 384 / 1309 ms (×3.4) | map: one gather over payload |
| 100000 rows × 16 cells* | 248 ms    | 373 ms   | 408 ms               | ~1 ns/cell, about 2 ms       |

- `consC` is NOT per-element: it is one bulk call over all rows. It is not vectorised ALONG an array: one call adds
  one element to every row and copies every cell, ending in a `grade` (sort) of all cells (:661; `catC` :1042).
- The fold is the larger cost: `length + 1` rounds, each `step`, `pair`, `ran`, `≫`, `nub`, `antiJoin`, `∪`. Per
  element of one array: `sum` 14.5 µs, `length` 135 µs.
- `cons` inside a fold is quadratic (×3.4 per doubling above): round k copies the k cells built so far. `snocC` is
  six kernel sequences a call. `cons°`/`snoc°` are slices; their only copy is `Vals.compact`.
- Native backend (`doc/rel-native-design.md` §6): a fold is a `loop` of `length + 1` iterations of a `Fun` plus six
  kernel sequences. Class R, M, S ops should each be a straight-line kernel sequence with no `loop`.
- Class N is not a cons problem: output grows geometrically, so the copies sum to about twice the output. (*) An
  upper bound, 155–255 ns per cell: that timing includes building the input from a `List`.

## 3. Replacement design

No new type or data structure: every replacement is a `Rel` built from `slicesOf`, `expand`, `sums`, `gather`,
`pick`, `raze` — the pieces `nestC` (:989, `inits`/`tails` with no rounds), `catC` and `zipC` already use.

| class | array-native formulation                                                    | k          | tie to cons form  |
|-------|-----------------------------------------------------------------------------|------------|-------------------|
| R     | `length` = `hi − lo` of `slicesOf`                                          | `#:'`      | `rep_length`      |
| R     | `⦇e, (f×𝟙)⊕⦈`, `⊕` associative with unit `e`: per-row reduce of the payload | `+/'`      | T1                |
| R     | `concat`: outer slice of inner slices, one `gather` + `raze`                | `,/'`      | T1, `⊕ = cat`     |
| M     | `F(R)`, `R` simple: `lo`/`hi` kept, payload through `R` by one join; a row  | `f''`      | T2; non-simple    |
|       | with an element outside `dom R` has no result                               |            | `R` keeps the fold|
| M     | `filter(p)`: mask the payload, counts = per-row sum of the mask             | `x@&p x`   | T3                |
| M     | `takewhile(p)`: `hi` := first position failing `p`, no copy                 | `(p x)?0b` | T3                |
| S     | `head`,`last`: `atPos` (:1093); `tail`,`init`: `lo+1`, `hi−1`               | `*:`, `1_` | proved today      |
| S     | `prefix`,`tails`,`inits`,`suffix`,`segment`,`cat°`: `nestC` slices          | `,\`       | `rep_inits`       |
| P     | build once: `Λ` of a relation `position ⟶ B` in position order (`enum`),    | `@[;i]`    | T4                |
|       | or `cat` of whole arrays; `τ` for one element. N: unchanged, stay builtins  |            |                   |

| id | statement (over Lean `List`, where the proofs live)                                | status                |
|----|------------------------------------------------------------------------------------|-----------------------|
| T1 | `⊕` associative with unit `e` ⟹ `⦇e, (f×𝟙)⊕⦈ = F(f) reduce(⊕)`                     | new, by induction     |
| T1'| same premise ⟹ `cat reduce(⊕) = (reduce(⊕) × reduce(⊕)) ⊕`                         | new, `foldr_append`   |
| T2 | `R` simple ⟹ `xs F(R) ys` iff equal length and `xs[i] R ys[i]` at each `i`         | `mapSpec` in AlgTest  |
| T3 | `filter(p) = F(p → τ, nil) concat`; `takewhile(p)` = the longest prefix inside `p` | new                   |
| T4 | `xs = Λ(enum)` of `{(i, xs[i])}`: an array is its position relation                | `enum` exists         |

What survives of B&dM:
- `⦇e, S⦈` on cons-lists stays the SPECIFICATION with every law (fusion `relCata_fusion` A5_5, `Λ_fusion`, greedy,
  thinning); `AOP/` and `LeetQ/Aop/` derivations do not move. This is leetq/CLAUDE.md's rule: "a fused kernel for a
  pattern of primitives is an optimisation, tied to the pattern by a theorem".
- Arrays under `cat` are not the initial algebra of a polynomial functor (`cat` is associative), so fold fusion does
  not transfer to a "fold over `cat`". T1 replaces it: a fold with an associative step is a reduce, and a reduce
  distributes over `cat`. B&dM state only `concat`/`wrap` naturality for this view (p.10, p.20).

## 4. What cannot avoid a sequential pass

| case                                             | why                             | expression                     |
|--------------------------------------------------|---------------------------------|--------------------------------|
| DP steps: Edit `step'`, Knapsack `step`, `thinL` | step reads previous result      | `⦇e,S⦈`/`loop`, bulk over rows |
| state machines: Detab `step`/`op`, JobShop       | output depends on running state | `loop`, OUTPUT by position     |
| `merge`, `select` (Selsort); relational folds    | data-dependent, several results | rounds as today                |

- The rounds stay; `cons`/`snoc` INSIDE the step go. The step emits a relation `(row, position) ⟶ B`, accumulated
  by `∪`, and the array is built once after the loop (T4): O(L²) copies become O(N) plus one sort. The accumulator
  is a `Rel`, not a new type.
- A scan with an associative operator (`+\`) covers a running reduce (Detab's column number, Mss's prefix sums). It
  would be a new `Tm` constructor, so it NEEDS APPROVAL; no stage below depends on it. `μ`/`ν` are untouched.

## 5. Migration

| stage | files: change                                                           | code/proof | proofs broken         |
|-------|-------------------------------------------------------------------------|------------|-----------------------|
| 1     | `Alg`, new `RepReduce`: `length` = `hi − lo`; `sum` = row reduce; T1    | +60/+350   | `rep_length`, `_sum`  |
| 2     | `Alg`, `RepList`: `mapC` simple-`R` path by payload join, else fold     | +50/+300   | `rep_map`: one case   |
| 3     | `Alg`, `Elab`, new `RepSlice`: `filter`, `takewhile`, `prefix`,`concat` | +120/+500  | none; new `rep_*`     |
| 4     | `Alg`, `RepList`, `RepPerm`: `consC`/`catC` place cells, no `grade`     | ±40/±250   | `rep_cons`, `rep_cat` |
| 5     | `Alg`, `RepMerge`, `RepThin`, `RepLoop`: output by position, one `Λ`    | ±150/±900  | their invariants      |
| 6     | `Run/Lang/*`, `Lang/Test`: `cons`/`snoc` leave `Op`/`Tm` (F only)       | −150       | `Lang/Test` tables    |

Order 1 → 5; no stage needs a later one. Gate after each, then the scratch timing on the ops the stage touched:
`env CAP_MEM_MB=13000 /home/dh/repo/freyd/scripts/cap lake -d /home/dh/repo/freyd/leetq build LeetQ LeetQAop`.

Edits in aima's `Rel/Programs/*` under E / F (listed, not made; option D needs none):

| file             | edit                                                                                      |
|------------------|-------------------------------------------------------------------------------------------|
| Prelude, Mss     | Prelude :22–32, :38 on `at`, slices, `cat`, `F`; Mss :19 `total` for `⦇ran(zero),plus⦈`   |
| Knapsack         | :49 `cpr` as `F(⟨⊤a,𝟙⟩)`; :37, :50 stay (class Q, N)                                      |
| Edit, Detab, Job | Edit :28, :42, :56, Detab :38, :58, JobShop :30 output by position; the N lines stay      |
| Selsort, Circuit | F only: `cons°` → `⟨at(0), tail⟩`; `ins` → `⟨⊤τ,𝟙⟩cat`                                    |

## 6. Options

| option | what                                               | cost                       | buys                    |
|--------|----------------------------------------------------|----------------------------|-------------------------|
| D      | Engine only, stages 1–4; program text keeps B&dM's | ~270 code, ~1400 proof     | R, M, S ops loop-free,  |
|        | cons folds, `Elab` runs the proved bulk kernel     | lines; no Programs edit    | 10²–10⁴× on long arrays |
| E      | D + stage 5 + Prelude and programs rewritten on    | D + ~150 code, ~900 proof, | no O(L²) copy in steps; |
|        | arrays; cons folds legal for class Q, N only       | ~40 lines in 6 aima files  | text reads as bulk ops  |
| F      | E + stage 6: `cons`, `snoc`, converses leave the   | E + all 9 cons-using       | one constructor family; |
|        | language, kept only in Lean specs                  | programs rewritten         | text leaves the book    |

Recommendation: **D now, then E's stage 5.** D removes the measured cost without touching a derivation or aima's
files, and each stage is a theorem "bulk kernel = the fold", which the native backend needs anyway. E's program
rewrite is worth doing once D shows which folds remain in the profiles. F buys no speed beyond E.
