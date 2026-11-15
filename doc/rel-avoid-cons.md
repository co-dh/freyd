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
| state machines: Detab `step`/`op`, JobShop       | output depends on running state | `scan`, then `F` and `concat`  |
| `merge`, `select` (Selsort); relational folds    | data-dependent, several results | rounds as today                |

- The rounds stay; `cons`/`snoc` on the OUTPUT go. A step that only appends is a scan (§5 stage 4): the states are
  kept as a relation `(row, position) ⟶ X`, accumulated by `∪`, and the array is built once after the rounds (T4):
  O(L²) copies become O(N) plus one sort. The accumulator is a `Rel`, not a new type. `μ`/`ν` are untouched.

## 5. Migration

Decided: "we choose array over list"; "add scan."; "we don't want strictly follow q and rewrite programs/* with q
style". So a program keeps its relational form, and `cons`/`snoc` are replaced only where an array op does the job.
A `cat` with a one-element array (`⟨π₁,π₂τ⟩cat`, `(τ×𝟙)cat`) is `cons` renamed and is not such an op.

| stage | files: change                                                           | code/proof | proofs broken         |
|-------|-------------------------------------------------------------------------|------------|-----------------------|
| 1     | `Alg`, new `RepReduce`: `length` = `hi − lo`; `sum` = row reduce; T1    | +60/+350   | `rep_length`, `_sum`  |
| 2     | `Alg`, `RepList`: `mapC` simple-`R` path by payload join, else fold     | +50/+300   | `rep_map`: one case   |
| 3     | `Alg`, `Elab`, new `RepSlice`: `filter`, `takewhile`, `prefix`,`concat` | +120/+500  | none; new `rep_*`     |
| 4     | `Syntax`, `Elab`, `Gen`, `Alg`, new `RepScan`: `scan(F)`, `scanr(S)`    | +170/+600  | none; new `rep_scan*` |
| 5     | `Elab`: converse rules; `Alg`: `catC` places cells; the four programs   | +40/±250   | `rep_cat`             |
| 6     | `Run/Lang/*`, `Lang/Test`: `cons`, `snoc`, `α`, `tic` leave `Op`/`Tm`   | −150       | `Lang/Test` tables    |

Order 1 → 6; stage 5's program edits need stages 3 and 4. Gate after each, then the scratch timing on the ops the
stage touched:
`env CAP_MEM_MB=13000 /home/dh/repo/freyd/scripts/cap lake -d /home/dh/repo/freyd/leetq build LeetQ LeetQAop`.

### Stage 4: scan

One traced instance, `(0, a b c) scan(F) x₀ x₁ x₂ x₃`: `x₀ = 0`, `(x₀,a) F x₁`, `(x₁,b) F x₂`, `(x₂,c) F x₃`.

| item       | `scan(F)`, the states of `loop(F)`               | `scanr(S)`, the values of `⦇e,S⦈` on the suffixes  |
|------------|--------------------------------------------------|----------------------------------------------------|
| type       | `F : X×Y ⟶ X`; `scan(F) : X×[Y] ⟶ [X]`           | `S : Y×X ⟶ X`; `scanr(S) : [Y]×X ⟶ [X]`            |
| definition | `xs[0]` the seed, `(xs[i], ys[i]) F xs[i+1]`     | `xs[n]` the seed, `(ys[i], xs[i+1]) S xs[i]`       |
| length     | `|ys| + 1`, as `inits`                           | `|ys| + 1`, as `tails`                             |
| `Op.table` | `("scan", .scan, 1)`, beside `loop`              | `("scanr", .scanr, 1)`                             |

```
T5   F simple ⟹ scan(F) = ⟨π₁,π₂ inits⟩ str F(loop(F))      -- str : X×[A] ⟶ [X×A], in the Lean statement only
T5'  S simple ⟹ ⟨𝟙,⊤e⟩scanr(S) = tails F(⦇e,S⦈)
Tm.scan  (F : Tm (.prod X Y) X d) : Tm (.prod X (.arr Y)) (.arr X) true
Tm.scanr (S : Tm (.prod Y X) X d) : Tm (.prod (.arr Y) X) (.arr X) true
```

| decision      | value                                                                                              |
|---------------|----------------------------------------------------------------------------------------------------|
| spelling      | `scan(F)`, arity 1, a family op as `loop(F)` (`Syntax.lean` :55 `Op.table`; `Elab.lean` :21 `Tm`)  |
| seed          | taken as `loop` takes it; q's `⊕\` is `⟨⊤e,𝟙⟩scan(⊕) tail`, the states before each element `init`  |
| why `n + 1`   | Detab needs the state BEFORE each element, Edit a column of `|x| + 1`; `tail`, `init` are slices   |
| why two       | `loop` runs from the left and `⦇e,S⦈` from the right; Detab scans the first, Edit the second       |
| associativity | not a premise: the definition is the path above, for any `F`. With `⊕` associative with unit `e`,  |
|               | T1 gives `⟨⊤e,𝟙⟩loop(⊕) = reduce(⊕)`, so `⟨⊤e,𝟙⟩scan(⊕) tail = inits tail F(reduce(⊕))`            |
| `F` simple    | states by position: `loopRound` :1375 with each round's states kept under `(row, position)`, one   |
|               | `Λ` in position order at the end (T4); `simpleC` :1461 on each round's step decides                |
| `F` not simple| a state array is one PATH, which positions alone do not hold: the run keeps today's `loop` on      |
|               | `X×[X]`. T5 is then only `⊑`                                                                       |
| one pass      | `scan(plus)`: `Alg.sums` (`Code.lean` :60, qlean `Scan.scan .sums`) over the flat payload less each|
|               | row's base, as `expand` :85 does; a row whose sum leaves the number universe has no result, as     |
|               | stage 1's `sum`. `times`, `max`, `min` have qlean scans (`prds`, `maxs`, `mins`) but no inverse to |
|               | restart at a row: they run by rounds until qlean has a scan that restarts per row                  |
| given a family| by `lFold`'s row (`Elab.lean` :576): the key is carried in the state, `scan` at `I×X`, then        |
|               | `F(π₂)`. Edit's `ent(b)` below needs it. No new `Tm` beyond the two                                |
| converse      | `convTm` throws `scan( )`, as `loop( )`                                                            |
| not built     | `inits'`, a `reduce(⊕)` op, a round-halving scan for a proved-associative `⊕`: no program needs one|

Group-by-key reduce needs no op and no program here uses it: for `R : K ⟶ V`, `Λ(R)sum : K ⟶ N` (`transposeC`
:313 groups once, then stage 1's row reduce). `Λ(R)` holds each value once, so a sum with repeats takes `R` from
`K` to `position×V`. qlean's `Reduce.overGroups` is the fused kernel if a profile asks for it.

### Stage 5: the output lines of Edit, Detab, JobShop, Selsort

| line                   | today                            | array op that does the job                 | needs       |
|------------------------|----------------------------------|--------------------------------------------|-------------|
| Edit `step`, 3 `cons`  | fold appending by the operation  | map an operation to `[a]` or `[]`, flatten | stages 2, 3 |
| Edit `step'`, 2 outer  | fold consing one entry a round   | `scanr`: an entry reads the entry after it | stage 4     |
| Edit `step'`, `base'`  | 4 inner: an operation before an  | none: residue                              | question    |
|                        | entry of the column              |                                            |             |
| Detab `step`, 2 `snoc` | loop on (output, column)         | `scan` the column; map (column, char) to   | stages 3, 4 |
|                        |                                  | its characters; flatten                    |             |
| Detab `op`, 2 `snoc`   | loop on (output, (held, column)) | the same with `tc`; the last state's held  | stages 3, 4 |
|                        |                                  | blanks by one `cat` of whole arrays        |             |
| Detab `op`             | `blanks(t) ⧺ [a]` for one char   | none: residue, inside `F`, no accumulator  | question    |
| JobShop `step`, `snoc` | the state IS the output, read    | none: residue                              | question    |
|                        | whole each round (`π₁ ∋ bad`)    |                                            |             |
| Selsort `select°`      | `ok cons perm`: one element put  | none: residue; `cons°` is `cat°(τ°×𝟙)`     | question,   |
|                        | into an array                    |                                            | `convTm`    |

```
-- Edit: T1 with ⊕ = cat ties it to ⦇ran(base), step⦈
ex : Op ⟶ [A] ≜ (cpy° ∪ del°)τ ∪ (ins° nil)
ey : Op ⟶ [A] ≜ (cpy° ∪ ins°)τ ∪ (del° nil)
edit : [Op] ⟶ [A]×[A] ≜ Es⟨F(ex) concat, F(ey) concat⟩
ent(b : 1 ⟶ A) : (A×([Op]×[Op]))×[Op] ⟶ [Op] ≜ dom(π₁π₁ ∩ (⊤b))⟨π₁π₁cpy,π₁π₂π₂⟩cons
    ∪ (dom(⟨π₁π₁,⊤b⟩ne)⟨⟨π₁π₁del,π₂⟩cons,⟨⊤b ins,π₁π₂π₁⟩cons⟩bmin)       -- step' less its outer cons; π₂ was π₂head
nextcol(x, b, us) ≜ ⟨xus, ⟨b ins,us last⟩cons⟩scanr(ent(b))

-- Detab: w ≜ ⟨⊤m,⟨π₁,⊤m⟩mod⟩minus on (column, char)
col : N×Ch ⟶ N ≜ dom(π₂nl)z ∪ (dom(π₂tb)⟨π₁,w⟩plus) ∪ (dom(π₂(𝟙(Ch) − nl − tb))π₁ succ)
out : N×Ch ⟶ [Ch] ≜ dom(π₂tb)w blanks ∪ (dom(π₂(𝟙(Ch) − tb))π₂τ)
detab : [Ch] ⟶ [Ch] ≜ ⟨⟨z,𝟙⟩scan(col) init, 𝟙⟩zip F(out) concat
tcs : [Ch] ⟶ [N×N] ≜ ⟨⟨z,z⟩,𝟙⟩scan(tc)
out' : (N×N)×Ch ⟶ [Ch] ≜ h nil ∪ ((dom(π₂bl) − h)⊤tb τ) ∪ (dom(π₂(𝟙(Ch) − bl))⟨π₁π₁ blanks,π₂τ⟩cat)
entab : [Ch] ⟶ [Ch] ≜ ⟨⟨tcs init,𝟙⟩zip F(out') concat, tcs last π₁ blanks⟩cat
```

Engine limits these lines met (`Elab.lean` :1103 `convTm`):

| limit                         | decision                                                                           |
|-------------------------------|------------------------------------------------------------------------------------|
| `τ°` not on demand            | rule `τ° = dom(length{(1,1)})at(0)`, from `Tm`s that exist; Prelude's stand-in     |
|                               | `at(0)τ ∩ 𝟙` goes                                                                  |
| `(R×S)°`, an operand on demand| rule `⟨π₁R,π₂S⟩° = ⟨π₁R°,π₂S°⟩`; today's pair rule asks for `π₁°`. With `τ°` it    |
|                               | runs `(cat°(τ°×𝟙))° = (τ×𝟙)cat`, which Selsort's `select°` needs under H           |
| `at(0)°` on demand            | stays an error: it is no function of its key and no array is given to read         |
| `F( )` of a family            | no row: with `scan`/`scanr` lifted, none of the four programs applies `F` to one   |
| `catC` :1024 ends in a `grade`| place the cells by `expand` + `gather`, as stage 3's `concat`: `cat` is the one    |
|                               | constructor left                                                                   |

Residue: the lines where one element is put into an array and no array op does it — Edit's 4 inner `cons`, Detab
`op`'s `blanks(t) ⧺ [a]`, JobShop `step`, Selsort `select`, and the class N lines (`Ss`, `Es`, Detab `S`, Circuit
`ins`, Knapsack `S`, `perm`'s `add`, `subseq`). leetq/CLAUDE.md: "where it cannot be written, or only awkwardly,
that is the finding to record". How they are spelled once `cons` leaves is the open question:

| option | the residue is written                                     | cost                                       |
|--------|------------------------------------------------------------|--------------------------------------------|
| G      | with `cons`/`snoc`, which stay in `Op`/`Tm`; stage 6 only  | none; the language keeps two constructor   |
|        | clears the Prelude and the lines of the table above        | families                                   |
| H      | `(τ×𝟙)cat`, `(𝟙×τ)cat`, known to be `cons` renamed and     | the two `convTm` rules; ~25 program lines; |
|        | listed here as the finding; stage 6 lands whole            | no speed change (JobShop L = 15)           |
| I      | array-natively: Edit's column of lengths and back pointers,| each program redesigned, against "we don't |
|        | JobShop's starts by position, a builtin for class N        | want … rewrite programs/*"                 |

Recommendation: **H**, the standing "ban cons" with the residue recorded.

### Stage 6: `cons`, `snoc`, `α`, `tic` leave `Op`/`Tm`

| must land first                             | why                                                                 |
|---------------------------------------------|---------------------------------------------------------------------|
| stages 1–3                                  | the Prelude's `head`…`takewhile`, `concat` no longer fold over cons |
| stages 4, 5 and G / H / I                   | every program line above has its new text; under G stage 6 stops    |
|                                             | at the Prelude                                                      |
| the two `convTm` rules                      | `cons° = uncons` (:1141) goes with `cons`; `cat°(τ°×𝟙)` replaces it |
| `Lang/Test.lean`'s own programs (33 lines)  | :303–:340, :551–:601 build arrays by `cons`: literals, `Λ`, `cat`;  |
|                                             | :714–:760 test `cons°`, `loop(snoc)`: on `cat°`, `scan`, or deleted |
| `Expand`, `Gen`, `Bits`, `Plan`, `BitsSpec*`| their `cons`/`snoc` cases go with the constructors                  |

Kept: `unconsC` :626, `unsnoc` :1076 (slices; `foldRound`, `loopRound` read them), `consC` where `subseqC`,
`permC`, `thinBodyC` call it — kernels of the engine, not operators of the language — and every `⦇e,S⦈` law in
Lean.

Edits in aima's `Rel/Programs/*` (listed, not made; option D needs none):

| file             | edit                                                                                      |
|------------------|-------------------------------------------------------------------------------------------|
| Prelude, Mss     | Prelude :22–32, :38 on `at`, slices, `cat`, `F`; Mss :19 `total` for `⦇ran(zero),plus⦈`   |
| Knapsack         | :49 `cpr` as `F(⟨⊤a,𝟙⟩)`; :37, :50 are class Q, N: residue                                |
| Edit, Detab      | the stage 5 text above; `fstcol`, `column`, `mle`, `spec` and every `check` unchanged     |
| JobShop, Selsort | residue only, by G / H / I                                                                |

## 6. Options

| option | what                                               | cost                       | buys                    |
|--------|----------------------------------------------------|----------------------------|-------------------------|
| D      | Engine only, stages 1–3; program text keeps B&dM's | ~230 code, ~1150 proof     | R, M, S ops loop-free,  |
|        | cons folds, `Elab` runs the proved bulk kernel     | lines; no Programs edit    | 10²–10⁴× on long arrays |
| E      | D + stages 4, 5: `scan`, and the output lines of   | D + ~210 code, ~850 proof, | no O(L²) copy in steps; |
|        | Edit and Detab on it; relational form kept         | ~15 lines in 2 aima files  | states by position      |
| F      | E + stage 6: `cons`, `snoc`, converses leave the   | E + the residue by G/H/I   | one constructor family; |
|        | language, kept only in Lean specs                  |                            | text leaves the book    |

Chosen: F ("F. and ban cons"), stages in order; the one open item is G / H / I.
