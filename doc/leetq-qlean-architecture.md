# leetq `Alg` and what it depends on

## Goal

Implement `Rel`. This is the goal; work that does not serve it is not done.

The design (`leetq/CLAUDE.md`):

- A relation is a pair of typed arrays of one length: `Rel k v = {n, key : Vals k n, val : Vals v n}`. An `Arr` is
  a qlean column of one `QAtomicType`.
- The algebra on it: composition `≫`, converse `°`, `∩`, `∪`, `⊑`, `𝟘`, `⊤`, `𝟙`, left/right/symmetric division,
  `Λ` and `∋`, pair `⟨R,S⟩` and product, sum `[R,S]`, fold `⦇e,f⦈`, an unfold then a fold, functors `F(R)`, natural
  and lax natural transformations (`∋`, `est`, `thin`), maps on positions, and `enum`.
- Every op is total and answers its relation bare: no `Except`, no `do`, no `←`. A program is one relation term.
- Only the primitives are qlean C kernels; every op is a composition of them.

In scope: the `Alg` ops, their helpers, the programs that test them (Blocks, Chess, Circuit, Wumpus), and a qlean
kernel or theorem only when an `Alg` op needs it. Out of scope until an `Alg` op or a program needs it: q's verbs,
q compatibility, qlean kernel coverage of cells no `Alg` op reads.

State on 2026-11-10, `master` at 77d84e2; the whole leetq package builds. Items marked `[~]` are in an agent's
worktree and not on `master`.

## Data

```
Obj  = atom t | prod a b | arr b | sum a b                  (Core)
Arr t n          an Enc with a proof of Enc.WF t n       one qlean column of n elements
Vals A n         atom: Arr t n     prod: Vals a n × Vals b n
                 arr:  (m : Nat) × Arr long n × Arr long n × Vals b m
                       row i is the slice [lo i, hi i) of one flat payload of m elements
                 sum:  (l r : Nat) × Arr boolean n × Arr long n × Vals a l × Vals b r
                       row i is inl (left[idx i]) when tag i is false, inr (right[idx i]) when true
Rel k v          {n, key : Vals k n, val : Vals v n}
Part A           (n : Nat) × Vals A n                    a side     of some count: what `codes` and `raze`
                                                         take when they read two relations of different n
Code             {w, n, card, b}   a column of integer codes: lane width w, count n, payload b
```

- One representation of a relation: `Rel` with count-indexed `Vals`. `Part` is `Vals` with its count packed, not a
  second tree: `Cols`, `cols`, `ofCols`, `Vals.ofParts`, `Obj.count` are deleted, `Obj.raze` answers at the
  summed count of its parts.
- A set is an array: `Λ(R) : A ⟶ list B`, each array sorted by value and without repeats, so equal sets are equal
  arrays; `∋` is `mem` on those arrays. No set id.

## Layers

The target, five layers, each using only the one below:

```
programs   Blocks  Chess  Circuit  Wumpus          one relation term each
Alg        ≫ ° ∩ ∪ \ ⊑ ==  𝟙 ⊤ ∼  dom ran  / \ ÷  Λ ∋  ⟨R,S⟩ ×  [R,S]  est thin  ⦇e,S⦈  F(R)  cons°  iter
Code       codes, and find / member / gather / groupIds / grade on integer codes; join anti cross
Core       Obj (atom | prod | arr | sum)   Vals   Rel
qlean      kernels, Enc
```

What `master` still has beside it, each removed by a step of the plan:

| extra                                                             | removed by |
|-------------------------------------------------------------------|------------|
| `Find`, `Ew`, `Scan`, `Parted`, `KernelWF/*` between `Alg` and qlean | step 2     |
| reference implementations beside a kernel (`setIdsRef`, …)        | step 4     |
| `Code`, `Alg` and the guards in one file `Algebra.lean`           | step 5     |

The names behind the symbols: `/` `leftDiv`, `\` (division) `rightDiv`, `÷` `symDiv`, `Λ` `transpose`, `∋` `mem`,
`⟨R,S⟩` `pair` with `outl`/`outr`, `×` `prod`, `[R,S]` `junc`, `⦇e,S⦈` `fold`, `F(R)` `map`, `cons°` `uncons`;
also `zero`, `top`, `idU`, `antiJoin`, `num`, and the predicates `entire simple isMap injective surjective`.

The qlean kernels `Code` dispatches to (`QLean/Kernel/{Sort, Structural, Reduce, Elementwise, Coc}` + `c/*.c`):

| group   | kernels                                                                                   |
|---------|-------------------------------------------------------------------------------------------|
| search  | `memberBits/Vec/IdsVec`, `findBitVec/Vec/IdsVec`, `whereBits`                             |
| gather  | `gatherBits`, `gatherBytes`, `gatherPacked`, `razeColumn`, `gatherColumn`                 |
| order   | `Order.groupIds`, `idGroups`, `groupSizes`, `grade`, `gradeColumn`, `groupIdsColumn`, `rankSlices`, `runStarts*` |
| ew      | `Kernel.Ew.val`, `Ew.mon`, `Ew.notBits`                                                   |
| fold    | `Scan.scan .sums`                                                                         |
| columns | `Column.intern`, `idWidthOf`, `packIds`                                                   |

Not used by `Alg`: qlean's q interpreter verbs (`join`, `member`, `cross`, `findColumn`, `memberColumn` on
`QValue`, answering `Except` or `Option`).

## What the B&dM note needs from `Alg`

The companion note (`diag/aop/04-relations.typ` … `10-greedy.typ`) sets the SCOPE of `Alg`: every operator it
writes is supported. Its programs are examples of that scope, not programs to port. After the operators: the Rel
language (`doc/rel-lang-design.md`; decided: its back end is `Alg`, and `∼` is in it) and Blocks written in it. `yes` = on `master` and total;
`no` = not in `Alg`.

| ch. | operator in the note                                   | in `Alg`                                    | state |
|-----|--------------------------------------------------------|---------------------------------------------|-------|
| 4   | `RS`, `R°`, `∩`, `∪`, `⊑`, `𝟘`, `⊤`, `𝟙`               | `≫ ° ∩ ∪ ⊑ zero ⊤ 𝟙`                        | yes   |
| 4   | `dom`, `ran`, coreflexive of a predicate               | `dom`, `ran`; a predicate is a coreflexive  | yes   |
| 4   | `R\S`, `R/S`, `frac(R,S)`                              | `leftDiv`, `rightDiv`, `symDiv`             | yes   |
| 4   | `R ⇒ S` (as in `R;H ≜ R ∩ (R° ⇒ H)`), `−`              | `\` is set difference; `⇒` is `∼R ∪ S`      | yes   |
| 5   | `⟨R,S⟩`, `π₁`, `π₂`, `R×S`                             | `pair`, `outl`, `outr`, `prod`              | yes   |
| 5   | `[R,S]`, `inl`, `inr`, `R+S`                           | `junc`, `inl`, `inr`, `sum` on `Obj.sum`     | yes   |
| 5   | `Λ(R)`, `∋`, `∈`                                       | `Λ(R)`, `∋(R)`, `mem`                       | yes   |
| 5   | `E(R) ≜ frac(∋R,∋)`, `P(R)`, `union ≜ frac(∋∋,∋)`, `τ`, `nil`, `α` | `E`, `P`, `Arr.union`, `τ`, `nil`, `alpha` | yes   |
| 5   | `α ≜ [nil,cons]`, `nil`, `cons`, `cons°`, `snoc`       | `uncons` (`cons°`)                          | yes   |
| 5   | `⦇R⦈` on lists                                         | `fold`                                      | yes   |
| 5   | `F(R)` for the list functor                            | `map`                                       | yes   |
| 5   | `⦇R⦈`, `F(R)` on other datatypes (`tip`/`bin` trees)   | — (needs a tree side: `doc/alg-bdm-ops-proposal.md`) | no |
| 6   | `μX : φ(X)`, an unfold then a fold `⦇T⦈°⦇h⦈`           | `iter`, `hylo` (a Lean loop, not a term)    | part  |
| 6   | closure `R*`                                           | written with `iter` in `Chess.star`         | part  |
| 6   | `perm`, `setify`, `ordered(≼)`, `sort(≼)`              | `perm` (`⦇[nil, add]⦈`), `setify` (`Λ(∋)`), `ordered`, `sort` (`perm ordered`) | yes |
| 6   | `bagify`                                               | — (a bag needs a representation: `doc/alg-bdm-ops-proposal.md`) | no |
| 7   | `est(R) ≜ ∋ ∩ (∈\R°)`, `lb`                            | `est` (least)                               | yes   |
| 7   | `filter(p)`, `takewhile(p)`, `length`, `sum`, `head`, `tail`, `prefix`, `suffix`, `succ`, `+` | `filter takewhile length Arr.sum head tail «prefix» suffix succ plus` | yes |
| 7   | `inits`, `tails`, `concat`, `zip`, `snoc`, `init`, `cat`, `cat°`, `snoc°` | `inits tails zip cat unsnoc` on positions; `concat ≜ ⦇[nil,cat]⦈`, `snoc ≜ (𝟙×τ) cat`, `init ≜ snoc° π₁`, `uncat ≜ ⟨inits,tails⟩ zip ∋` | yes |
| 7   | orders from a cost: `R ≜ cost ≤ cost°`, `≤` on numbers | `leq U`, `lt U` from kernels (not `general`) | yes   |
| 8   | `thin(Q)`                                              | `thin` (minimal)                            | yes   |
| 8   | `merge`, sorting sets, binary thinning                 | `merge` (rounds of `iter`), `sortSet ≜ setify° ordered`, `thinL ≜ setify thin(Q) setify° ∩ subseq`, `subseq` | yes |
| 9   | tabulation: `tic`, `loop`                              | `tic ≜ cons inits tail`, `loop` (rounds of `iter`) | yes |
| 9   | tabulation: `array`, `row`, `col`                      | — (definitions of the bracketing program over `tip`/`bin` trees: `doc/alg-bdm-ops-proposal.md`) | no |

The note's programs, for reference only (they show which operators are used; they are not ported):

| ch. | programs                                                                                        |
|-----|-------------------------------------------------------------------------------------------------|
| 6   | digits of a number, fast exponentiation, selection sort, quicksort, closure                     |
| 7   | `takewhile`, `mss`, `filter`, company party, shortest paths on a cylinder, security van         |
| 8   | paths in a layered network, knapsack, paragraph, bitonic tours                                  |
| 9   | string edit, optimal bracketing, data compression                                               |
| 10  | detab-entab, minimum tardiness, TeX                                                             |

What this still asks of the layers below: an order on numbers as a kernel-backed relation instead of a table, and
`nil` as a relation beside `cons`, so the list functions above are terms.

## Why the helpers exist

- A qlean kernel reads one column of one layout. An `Alg` op reads two relations whose sides are products, so it
  first needs one code space for both: `Obj.codes` gives each row of each side an integer code, equal rows equal
  codes. Every op is then a kernel on `Code`s plus a `pick` of rows.
- `Code`'s nine functions dispatch on lane width to the kernel of that width. qlean's `Enc` dispatches on storage
  layout; the two do not overlap, so `Code` is not a copy of `Enc`.
- No computation is re-implemented in leetq.

| leetq helper    | body                                                                                    |
|-----------------|-----------------------------------------------------------------------------------------|
| `Code.member`   | dispatch on lane width to `memberBits` / `memberVec` / `memberIdsVec`                   |
| `Code.find`     | dispatch to `findBitVec` / `findVec` / `findIdsVec`                                     |
| `Code.gather`   | dispatch to `gatherBits` / `gatherBytes` / `gatherPacked`                               |
| `Code.groupIds` | `Order.groupIds` or `Order.idGroups`                                                    |
| `anti`          | `whereBits (Ew.notBits (member ..))`                                                    |
| `cross`         | `tilLongs`, then `Kernel.Ew.val` twice (`idiv`, `imod`)                                 |
| `join`          | `groupIds`, `classSizes`, `find`, `expand`, `gather`, `grade`, `sums`, `add`, `sub`     |
| `cnt`, `atCnt`  | `groupIds`, `classSizes`, `gather`, `find`                                              |
| `Obj.codes`     | one code space for several sides: `razeColumn`, `Column.intern`, `groupIdsColumn`       |

## Rules

- A narrower domain is acceptable. A witness is type-level and the call site discharges it by `rfl`/`decide`.
- A caller without the witness takes it as its own precondition parameter. It never writes
  `if h : .. then pure (op .. h) else throw ..`; that only moves the `Except` up one level.
- A count equality comes from a theorem (`pick_len`, `fit_len`, `raze_len`, `cross_len`), not a run-time check.
- Where a payload has no size theorem yet: `if h : check then ⟨payload, h⟩ else reference`, the reference
  computing the same relation from atoms (`setIdsRef`, `pickRef`, `slicesRef`).
- New types, fields or representations are shown to the author before they are written.

## Where `Except` is left

None in `Algebra.lean`. One guard (the ALP float column) matches on `Arr.of`, because no theorem gives `Enc.WF`
for `Enc.alpOf`; an error there fails the guard.

## Plan

`[x]` on `master`, `[~]` an agent is on it, `[ ]` open.

Done:

- [x] programs `Blocks`, `Chess`, `Wumpus`, `Circuit`: no `Except`
- [x] core ops bare, with size theorems; operators the only spelling; `==` is `BEq (Rel A B)`
- [x] `𝟙`, `⊤`, `∼` over `class Univ`
- [x] division: `leftDiv`, `rightDiv`, `symDiv`
- [x] `Obj.list`; `Λ(R)`, `∋(R)`, `mem` total on arrays
- [x] `pair`, `prod`, `num`, `iter`
- [x] `est Q G := G \ G ≫ (Q \ Q°)`; the five predicates answer `Bool`
- [x] `Blocks.plan` is in Rel: states named by `Λ`'s arrays, new ones numbered by `num`, parent by `est`
- [x] modules that did not build deleted (`Struct Prog Norm Group Spec*`, `Bench`, `Check`); `foldGroups` deleted

Simplification, in order:

1. [x] one representation: `Part A := (n : Nat) × Vals A n`; `Cols`, `cols`, `ofCols`, `Vals.ofParts`,
   `Obj.count` deleted; `rows`, `nub` on `Rel`. Two new `if count fits then kernel else reference` sites:
   `shiftArr` (its reference keeps null as null from the `Ew` documentation, not a theorem) and `uncons`
2. [ ] move the functions `Alg` uses from `Find`/`Ew`/`Scan`/`Parted` into `Core`; delete those modules and the
   unimported `QSort`, `KernelWF/*` nothing reaches
3. [x] `est` is the least value, `thin` the minimal ones; `uncons` (`cons°`), `fold` (`⦇e,S⦈`), `map` (`F(R)`) on
   arrays, through one helper `foldBy` and a `cons`; `mapVal`, `foldOver`, the kernel `thin`, `arrDense`,
   `Arr.ofPart` deleted. `est` reads `Q` up to its reflexive closure (`b Q c` for every OTHER value `c`), so a
   strict `<` works; on a reflexive `Q` it is the note's `∋ ∩ (∈\Q°)`. `Obj.sum` added: `inl`, `inr`, `junc`, `sum`; `SumRel` deleted
4. [ ] prove the kernel count theorems and delete the reference implementations (`setIdsRef`, `pickRef`,
   `slicesRef`)
5. [ ] split `Algebra.lean` (1803 lines) into `Code`, `Alg`, and the guards

Open after that:

- [x] a `sum` row whose own side holds no value reads that side's null (`Obj.dflt`, what a gather past the side
  reads) everywhere: `row` keeps its tag, `codes` and `raze` first give it its value (`Vals.held`, a `compact`)

- [ ] `join_len` is `≤`, not `=`: `add` takes its count as `USize`, so past `2^64` rows `≫` truncates
- [ ] `symDiv` assumes the last offset of `segments` is the code count
- [ ] `Λ` does not give equal sets equal arrays for `general` atoms or nested arrays
- [ ] a list row with `lo`/`hi` out of range is clamped; untested at `Int64.minValue`
- [ ] `est` gives the minimal elements of a partial order, not a least one
- [ ] properties are `#guard`s, not theorems: `Λ(R) ≫ ∋(R) == R`, kernel and reference agree
- [ ] not implemented: general `⦇R⦈`, `F(R)`, an unfold then a fold, `enum`, maps on positions
- [ ] `scripts/lean-refactor` cannot load the leetq package (`unknown module prefix 'LeetQ'`)

Deferred non-`Alg` work: `doc/qrel-total-later.md`.
