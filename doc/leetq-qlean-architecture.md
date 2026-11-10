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

State on 2026-11-10, `master` at 70f8b08; the whole leetq package builds. Items marked `[~]` are in an agent's
worktree and not on `master`.

## Data

```
Obj  = atom t | prod a b | list b                       (Core)
Arr t n          an Enc with a proof of Enc.WF t n       one qlean column of n elements
Vals A n         atom: Arr t n     prod: Vals a n × Vals b n
                 list: (m : Nat) × Arr long n × Arr long n × Vals b m
                       row i is the slice [lo i, hi i) of one flat payload of m elements
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

```
 leetq  (freyd repo, leetq/, a Lake package that requires qlean)
┌──────────────────────────────────────────────────────────────────────────────────────────┐
│ programs      Blocks   Chess   Circuit   Wumpus                                          │
│               each imports only LeetQ.Rel.Algebra and opens Alg; one relation term each  │
├──────────────────────────────────────────────────────────────────────────────────────────┤
│ Alg ops       ≫  °  ∩  ∪  \  ⊑  ==      (the six names behind them are private)          │
│ (Algebra)     𝟙  ⊤  ∼   over class Univ (A : Obj);   zero  top  idU  dom  ran  antiJoin  │
│               leftDiv  rightDiv  symDiv      Λ(R)  ∋(R)  mem                             │
│               pair  outl  outr  prod  num    est     iter (bounded, over hylo)           │
│               entire  simple  isMap  injective  surjective   (answer Bool)               │
│  no program   junc  injConv  SumRel      (total)                                         │
│  calls them   mapVal  foldOver  uncons  thin      (still Except; kept, to be made total) │
├──────────────────────────────────────────────────────────────────────────────────────────┤
│ helpers       on a side:   Obj.codes  Obj.raze  Obj.sortBy  Vals.pick  Vals.empty        │
│ (Algebra)                  rows  nub  pairs  tuples  distinctCorefl                      │
│               on codes:    Code.gather find member eqAt groupIds grade cat cut runStarts │
│                            join  anti  cross  cnt  atCnt  gradeBy  segments  setIds      │
│               on long payloads (ByteArray):  add  sub  mulc  sums  gather  whereEqV      │
├──────────────────────────────────────────────────────────────────────────────────────────┤
│ leetq modules Core    Obj, Arr, Vals, Rel                                                │
│ imported      Find    expand, one, bitsAt                                                │
│               Ew      (what Alg uses from it: to be listed)                              │
│               Parted, Scan, KernelWF/*   reached through Find/Ew                         │
└───────────────────────────────────────────┬──────────────────────────────────────────────┘
                                            │ every helper is a dispatch on, or a composition of
                                            ▼
┌──────────────────────────────────────────────────────────────────────────────────────────┐
│ qlean kernels  (QLean/Kernel/{Sort, Structural, Reduce, Elementwise, Coc} + c/*.c)       │
│ search    memberBits/Vec/IdsVec   findBitVec/Vec/IdsVec   whereBits                      │
│ gather    gatherBits  gatherBytes  gatherPacked   razeColumn  gatherColumn               │
│ order     Order.groupIds  idGroups  groupSizes  grade  gradeColumn  groupIdsColumn       │
│           rankSlices  runStarts  runStartsIds  runStartsBits                             │
│ ew        Kernel.Ew.val  Ew.mon  Ew.notBits   (add sub mul idiv imod; i64; vv va)        │
│ fold      Scan.scan .sums                                                                │
│ columns   Column.intern  idWidthOf  packIds                                              │
├──────────────────────────────────────────────────────────────────────────────────────────┤
│ qlean storage   Enc (bytes, bits, foR, alp, gen ...)   Enc.WF t n e   QAtom  QAtomicType │
└──────────────────────────────────────────────────────────────────────────────────────────┘

 also imported by Algebra: QLean.Eval.Dyad  (what is used from it: not checked)
 not used by Alg: qlean's q interpreter verbs (join, member, cross, findColumn, memberColumn on QValue,
 answering Except or Option)
```

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

No program and no op a program calls answers `Except`. What is left in `Algebra.lean`:

| def                                   | caller                                    |
|---------------------------------------|-------------------------------------------|
| `mapVal`, `foldOver`, `uncons`, `thin` | guards only                               |
| `arrDense`                            | `mapVal`, `foldOver`                      |
| `Arr.ofPart` (raw `Nat × Enc`)        | `mapVal`, `lst`/`lstV`, `laneOf` (guards) |
| `ok`, `lst`, `lstV`                   | guards over encoded columns               |

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
3. [ ] keep `junc`, `injConv`, `SumRel`, `mapVal`, `foldOver`, `uncons`, `thin` (decided: they are B&dM's sum
   `[R,S]`, `inl°`/`inr°`, a functor on values, a fold, `cons°`, `thin(Q)`); make the four that answer `Except`
   total (`mapVal`, `foldOver`, `uncons`, `thin`), after which `arrDense` and `Arr.ofPart` answer bare or go
4. [ ] prove the kernel count theorems and delete the reference implementations (`setIdsRef`, `pickRef`,
   `slicesRef`)
5. [ ] split `Algebra.lean` (1765 lines) into `Code`, `Alg`, and the guards

Open after that:

- [ ] `join_len` is `≤`, not `=`: `add` takes its count as `USize`, so past `2^64` rows `≫` truncates
- [ ] `symDiv` assumes the last offset of `segments` is the code count
- [ ] `Λ` does not give equal sets equal arrays for `general` atoms or nested arrays
- [ ] a list row with `lo`/`hi` out of range is clamped; untested at `Int64.minValue`
- [ ] `est` gives the minimal elements of a partial order, not a least one
- [ ] `Blocks.lt` is a table on ids `0…26`; no op compares two longs
- [ ] properties are `#guard`s, not theorems: `Λ(R) ≫ ∋(R) == R`, kernel and reference agree
- [ ] not implemented: general `⦇R⦈`, `F(R)`, an unfold then a fold, `enum`, maps on positions
- [ ] `scripts/lean-refactor` cannot load the leetq package (`unknown module prefix 'LeetQ'`)

Deferred non-`Alg` work: `doc/qrel-total-later.md`.
