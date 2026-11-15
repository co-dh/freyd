# Rel: evaluating `R\(S T)` without the table of `S T`
Status: design only, nothing built. Every cost below is an estimate from row counts, not a measurement.
## Recommendation

- The unit is smaller than `R\(S T)`: **one kernel, the grouped `∨`/`∧` of bit rows**. `≫` is its `∨` instance,
  `\` its `∧` instance, and `R\(S T)` is the two applied in turn. No pattern is recognised.
- A closed term over small objects is computed as a **bit matrix** (`Λ` of the relation, each set one bit row)
  instead of a table. `S T` is then `|dom S| · |C|` bits, never rows.
- `Member.lean` (per-row tests, hash indexes, the Lean driver loop) is deleted; its `Route` (was `TP`) and `Route.table` stay.
- Needs approval: the bit matrix is a second representation of a relation (below, "The representation").

## One traced instance

```
u {π₁°} (u,m) {sup(K)} w {K} v        row (u,m) of sup(K) K  =  ∨ of K's bit rows at the w with (u,m) {sup(K)} w
                                      row u of π₁\(sup(K) K) =  ∧ of those rows over the m, i.e. over (u,m) {π₁} u
```

- `(S T)[x] = ∨ { T[w] ∣ x S w }`       // the row of `x` is the union of the rows of its `S`-successors
- `(R\M)[y] = ∧ { M[x] ∣ x R y }`       // the row of `y` is the intersection of the rows of its `R`-predecessors;
  no predecessor gives the all-ones row, which is `leftDiv`'s vacuous `⊤`

## Why not the other units

| unit                               | covers                                    | verdict                                    |
|------------------------------------|-------------------------------------------|--------------------------------------------|
| fused `R\(S T)`                    | 2 of the 5 division shapes in `Programs/` | a patch for the named case                 |
| semi-join / anti-join family       | `∩`, `−`, `R ≫ corNeg(C)`; exists already | does not remove the table of `S T`         |
| "test a plan on rows" in C         | everything `Member` covers                | a second evaluator in C, not a primitive   |
| counting over `S T` (today's `\`)  | everything                                | still materializes `S T`; this is master   |
| grouped `∨`/`∧` of bit rows        | `≫`, `\`, `/`, and with `Ew` `∩ ∪ − ∼`    | one primitive, k's `|/'` and `&/'` on rows |

- The division shapes in `leetq/LeetQ/Rel/Programs/`: `A\(X C)` (SudokuAC), `π₁\(sup(X) X)` (SudokuPC, PC9),
  `g°\𝟙(D)` (both Sudokus), `R°\𝟙` (`uniq`, Wumpus), `S⊤ \ adj` (`wmay`, Wumpus). `Lang/Test.lean` has 126 more
  lines with a `\`.
- A fused `R\(S T)` kernel that stays sparse (per `y`, a stamp and a counter per `z`) does the same number of
  steps as the join has rows, 3.6·10⁸ per round on 9×9 PC. It only saves the memory.
- Top-down membership tests need control flow per row. In C that is an interpreter of plans, whose Lean reference
  body is the evaluator again. Bottom-up, every plan node is one kernel call over whole columns.

## The representation

- `Bits`: a boolean column of `na · w` bits, row `i` at bits `[i·w, (i+1)·w)`, bit `i·w + j` set when code `i` is
  related to code `j`. It is a flat boolean vector, an existing qlean `Column`; no new qlean type.
- Codes: per object, all columns of the plan coded jointly by `Obj.codesC`, as `Member.codeAll` does today, with
  the `\` universes `UB`, `UC` among them. The codes stay `Code` columns; no `Array Nat` is built in Lean.
- `w` is the code count of the target object, `na` that of the source.
- Used only when `na · w ≤ 2²⁷` bits (16 MB) at every node of the plan. Above that the node is a table, as today.
- Not covered, on purpose: a large sparse object. No program in the repo has one; a sparse streaming kernel
  waits for the first real instance.

## The kernel

```
@[extern "qlean_bit_rows_over"]
def bitRowsOver (all : Bool) (w : USize) (offs idx m : @& ByteArray) : ByteArray
```

- Output row `g` is the fold of rows `idx[k]` of `m`, `k ∈ [offs[g], offs[g+1])`, by `∨` (`all = false`) or `∧`
  (`all = true`); an empty segment gives all zeros or all ones.
- `offs`: `ng + 1` long offsets, the form `Kernel.segments` returns and `overSegments` reads. `idx`: long row
  numbers into `m`.
- Lean reference body, bit by bit: output bit `g·w + j` is `any`/`all` over `k` of `Column.bitAt m (idx[k]·w + j)`.
- C: word-at-a-time `|=` / `&=` over `⌈w/64⌉` words per `(g, k)`; segments split across workers as
  `qlean_over_segments` does.

Everything else is an existing kernel:

| step                              | kernel                                                             |
|-----------------------------------|--------------------------------------------------------------------|
| table → `Bits`                    | `scatterPacked` at 1 bit, index `i·w + j` (to verify it takes `wb = 1`) |
| `Bits` → table                    | `whereBits`, then `÷ w` and `mod w`, then `Vals.pick` of the universes |
| `∩`, `∪`, `−`, `∼` on two `Bits`  | `Ew` on boolean payloads (`bitStep`: lesser, greater)              |
| table `∩ Bits`, table `− Bits`    | `gatherBits` at `i·w + j`, `whereBits`, `Rel.rows`                 |
| left operand's `offs`, `idx`      | `Kernel.segments` on the group column's code, as `symDivC` uses it |
| `°`                               | `Bits` → pairs → swap → `Bits`                                     |

## The evaluator

- `evB : Tm A B false → Option Bits` replaces `evP`: `comp`, `ldiv`, `rdiv`, `meet`, `join`, `diff`, `conv`, `top`
  have a rule; any other node is evaluated as its table and scattered (what `Member.orLeaf` does).
- `comp R S`: `R` as a table grouped by key, `S` as `Bits`: `bitRowsOver false`.
- `ldiv R S`: `R` as a table grouped by value, `S` as `Bits`: `bitRowsOver true`, rows indexed by the codes of `UB`.
- `ev` calls `evB` at a closed `comp`/`ldiv`/`meet`/`diff` whose plan fits the 2²⁷ bound, and converts the result
  to a table once, at the root of the plan. A `ν` round's `X` enters as a leaf.
- The choice is by size, not by shape, so `acArcs` is the precedent this does not follow. With `Bits`, a naive
  AC round is about 2.5·10³ word operations; whether `acFix` can then be deleted is a measurement to make after.
- LeetQ is not precompiled, so Lean code runs interpreted. This design runs one kernel call per plan node per
  round and no Lean loop over rows, which removes the 27% interpreter and 21% per-row `gather_run` time of
  `Member`.

## Theorems

On codes, in `leetq/LeetQ/Rel/KernelWF/` beside `DivSpec.lean`:

- `bitRowsOver_spec`: `bitAt (bitRowsOver all w offs idx m) (g·w + j)` iff `∃ k` (resp. `∀ k`) in
  `[offs g, offs (g+1))` with `bitAt m (idx k · w + j)`, for `g < ng`, `j < w`.

On relations, in a new `leetq/LeetQ/Rel/RepBits.lean`, each reduced to the existing law so no second semantics of
`≫` or `\` is stated:

| theorem        | statement                                                               | by                     |
|----------------|-------------------------------------------------------------------------|------------------------|
| `rep_ofBits`   | `rep (ofBits (bitsOf R)) = rep R`                                       | `whereBits_ids`, picks |
| `rep_compB`    | `rep (ofBits (compB S (bitsOf T))) = rep (S ≫ T)`                       | spec, `rep_comp`       |
| `rep_ldivB`    | `rep (ofBits (ldivB R (bitsOf S) Ub Uc)) = rep (leftDiv R S Ub Uc)`     | spec, `rep_leftDiv`    |
| `rep_meetB` …  | `∩`, `∪`, `−` on `Bits` against `rep_inter`, `rep_union`, `rep_diff`    | `Ew` bit spec          |
| `bits_table`   | for a route `p`: `rep (ofBits p.bits) = rep p.table`                     | induction on `Route`      |

- The pattern's own statement is a corollary of two rows, not a theorem of its own:
  `rep (ofBits (ldivB R (compB S (bitsOf T)) Ub Uc)) = rep (leftDiv R (S ≫ T) Ub Uc)`.
- `rep_ldivB` must reproduce `rep_leftDiv`'s vacuous clause: `b ∉ ran R` relates to `c` only for `b` in `Ub` and
  `c` in `Uc`. Rows are the codes of `Ub`; the all-ones row of an empty segment is masked by the codes of `Uc`.
- Hypotheses are the existing ones (`Obj.CodesFit` of the joint coding, `Vals.PickFits` of the universes at the
  picked rows) plus `na · w < 2⁶³`. `bits_table` replaces `Member`'s `answers_*`.

## Where the C goes

- qlean, not leetq: leetq's lakefile has no `extern_lib`, and the rule is "only primitives are qlean C kernels".
- C: `qlean_bit_rows_over` in `/home/dh/repo/qlean/c/reduce.c`, next to `qlean_over_segments`; `reduce.o` is
  already a target of `extern_lib qleankernel`, so the lakefile does not change.
- Lean: `bitRowsOver` in `/home/dh/repo/qlean/QLean/Kernel/Reduce.lean` after `overSegments`, the same shape:
  `@[extern]` on a `def` whose body is the reference; `precompileModules := true` already makes `#guard` reach it.

## Cost on 9×9 path consistency, per `ν` round

Sizes: 729 points; rows of `sup(K)` are `(Cell×D)×Cell` = 59,049; `w` = 729 bits = 12 words; `|K| ≈ 3·10⁵`.

| node                 | table mode (master), rows   | `Bits`, word operations             |
|----------------------|-----------------------------|-------------------------------------|
| `π₁X`                | `81·|K|` ≈ 2.4·10⁷          | 59,049 · 12 ≈ 7·10⁵                 |
| `∩ (π₂π₁°)`          | 2.4·10⁷ pair codes          | 7·10⁵                               |
| `sup(X) X`           | 3.6·10⁸, then dedup         | `|sup(X)|·12 = |K|·12` ≈ 3.6·10⁶    |
| `π₁\ …`              | 3.6·10⁸ joined and counted  | 59,049 · 12 ≈ 7·10⁵                 |
| `K₀ ∩`               | `|K₀|` codes                | 729 · 12 ≈ 9·10³                    |
| conversions of `X`   | —                           | `|K|` scatters + 5.7 MB scanned     |
| total                | ≈ 8·10⁸ row operations      | ≈ 6·10⁶ word operations             |

- Memory: three matrices of 59,049 × 729 bits = 5.4 MB each, against 23.7 GB.
- Time: about 10 ms per round at 1 ns per word operation; the number of rounds is not known (bound `|K₀| + 1`,
  the 31.6 s run would tell). Expected total under 1 s, dominated by the closed terms (`K₀`, `peer`) that stay
  tables.
- `Member` on the same round: one test per row of `K₀`, each up to 81 × (image of ~9) hash lookups, ≈ 2·10⁸
  interpreted steps; that is the 270 s.

## Order of work

1. `bitRowsOver` in qlean with its reference body, tested against it on random rows in `ReduceTest.lean`.
2. `Bits`, `bitsOf`, `ofBits`, `compB`, `ldivB` in leetq; `#guard` each against `≫` and `leftDiv` on the 4×4 board.
3. `evB` in `Eval.lean`; delete `Member.lean`; measure `SudokuPC9`. Then `bitRowsOver_spec` and the `RepBits` laws.
