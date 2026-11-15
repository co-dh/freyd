# Rel corpus benchmark (rel-141)

Rows ranked by wall (median of 3, seconds; load average beside each timing is in /data/tmp/rel-141/out/*.t.*).
elab-only is the same file with the #guard lines removed. interp/kernel/other: self time of one perf run
(interpreter = lean::ir::interpreter*; kernel = qlean_* / libqleankernel.so). rounds: mu/nu loops of >= 3 rounds.

Provenance. The table was measured at 1ab50df (stage 1: `#guard`s ran programs through the interpreter `Eval`),
using the oleans of the main checkout, with `lake env lean --setup …` per file and no precompile. It is not
comparable with the TestChess figures in the native work, which come from a different commit and a different
command:

| figure | commit | command | what it times |
|---|---|---|---|
| TestChess 52.5 s (this table) | 1ab50df, stage 1 | `lean --setup` on the file | interpreter runs at `#guard` time; elaboration 0.6 s |
| TestChess 206 s | fa417e7, stage 2 WIP | `lake build` of the module | 14 Chess variants expanded by the `rel_program` macro, run in the IR interpreter |
| TestChess 9.1 s | cae4f23, stage 2 + precompile | `lake build` of the module | the same expansion, run natively |

The rerun after native lands uses one commit and one command for every row.

| file | wall | elab-only | interp% | kernel% | other% | top symbol | mu/nu rounds | median delta% per round after round 1 |
|------|------|-----------|---------|---------|--------|------------|------------|------------------------------|
| TestChess | 52.5 | 0.6 | 64.1 | 9.2 | 25.4 | interp::eval_body 21.02% | none traced |  |
| Chess | 32.8 | 27.9 | 74.8 | 2.0 | 21.7 | interp::call 22.93% | none traced |  |
| TestKnapsack | 20.1 | 0.6 | 70.3 | 2.2 | 26.0 | interp::eval_body 22.06% | none traced |  |
| Test | 11.3 | 0.7 | 57.8 | 6.0 | 32.6 | interp::eval_body 18.62% | MU 5r 0->11; ACFIX 3r 20->8; NU 10r 183->81; ACFIX 3r 20->8; NU 10r 183->81 | 20.0; 0.0; 7.4; 0.0; 7.4 |
| TestEdit | 9.2 | 0.7 | 64.2 | 4.2 | 30.1 | interp::eval_body 20.80% | none traced |  |
| TestDetab | 6.7 | 0.6 | 63.8 | 4.0 | 30.0 | interp::eval_body 20.97% | none traced |  |
| SudokuPC9 | 3.3 | 3.0 | 50.3 | 15.9 | 35.1 | interp::call 15.83% | NU 13r 337565->62700 | 3.7 |
| Edit | 2.9 | 0.7 | 54.1 | 3.8 | 42.8 | interp::eval_body 17.58% | none traced |  |
| Knapsack | 2.8 | 0.7 | 57.4 | 1.9 | 41.0 | interp::eval_body 18.10% | none traced |  |
| TestSelsort | 1.7 | 0.5 | 45.8 | 5.8 | 49.2 | interp::eval_body 15.34% | none traced |  |
| Detab | 1.6 | 0.7 | 39.1 | 2.4 | 59.4 | interp::eval_body 12.31% | none traced |  |
| Blocks | 1.5 | 0.9 | 44.3 | 2.9 | 53.5 | interp::eval_body 14.35% | none traced |  |
| TestWumpus | 1.1 | 0.6 | 32.3 | 0.7 | 67.4 | interp::eval_body 10.66% | none traced |  |
| TestMss | 1.0 | 0.6 | 24.9 | 1.4 | 73.8 | interp::eval_body 8.52% | none traced |  |
| JobShop | 0.9 | 0.7 | 25.5 | 2.8 | 71.9 | interp::call 7.17% | none traced |  |
| Selsort | 0.8 | 0.6 | 22.9 | 3.0 | 73.8 | interp::eval_body 7.05% | none traced |  |
| Circuit | 0.8 | 0.7 | 2.5 | 0.2 | 97.6 | lean_mark_persistent 9.41% | none traced |  |
| SudokuAC | 0.7 | 0.7 | 8.1 | 0.1 | 92.1 | lean_mark_persistent 8.27% | none traced |  |
| Mss | 0.7 | 0.6 | 11.2 | 0.8 | 87.2 | lean_mark_persistent 7.17% | none traced |  |
| SudokuPC | 0.7 | 0.6 | 12.1 | 0.1 | 87.9 | lean_mark_persistent 6.69% | none traced |  |
| Wumpus | 0.7 | 0.6 | 5.6 | 0.0 | 94.3 | lean_mark_persistent 6.90% | none traced |  |
| TestCircuit | 0.6 | 0.5 | 6.2 | 0.2 | 93.9 | lean_mark_persistent 8.10% | none traced |  |
| Prelude | 0.6 | 0.6 | 2.1 | 0.0 | 97.8 | lean_mark_persistent 8.75% | none traced |  |

Corpus wall total 155.0 s.

- (1) precompile: interpreter self time is 97.3 s = 63% of the total (upper bound: alloc/RC inside interpreted code stays).
- (2) semi-naive mu/nu: files running a >= 3-round loop take 14.7 s = 9% of the total (upper bound; the loops themselves are a part of that).
- (3) fused kernels: qlean kernel self time is 8.2 s = 5% of the total; intermediates below.

Largest intermediates seen (only (3)'s question that the traces could answer; see the limits below):

1. `SudokuPC9` nu loop: X enters round 1 with 337565 rows and leaves round 13 with 62700 (median change 3.7% of X per round,
   max 7.9%); every round recomputes the whole X.
2. `Test` nu loop: X of 183 rows -> 81 over 10 rounds (median change 7.4%, max 14.1%).
3. `Test` mu loop: X from 0 to 11 rows in 5 rounds (median change 20%).

Limits, stated so no number is read as more than it is:

- Round tracing is a scratch copy under `/data/tmp/rel-141/scratch/leetq` (`Lang/Eval.lean` wraps the step of `nu`/`mu`
  in `dbgTrace`; `nuAC` runs `acFixTr`, a traced copy of `acFixC`, text in `doc/rel-bench/acfixtr.lean.txt`). Tracing
  `fixOnC`, `acFixC` or `compC` in place breaks `CRel.lean:50` and `AC3.lean:355,399` (their proofs unfold them), so
  the scratch copy traces one level above, in the evaluator.
- Traced files: `Chess`, `SudokuPC9`, `TestChess`, `TestKnapsack`, `TestEdit`, `TestDetab`, `Test`. The first five except
  `SudokuPC9` run no mu/nu loop at all: their time (Chess 33 s elaboration, TestChess 52 s, TestKnapsack 20 s,
  TestEdit 9 s, TestDetab 7 s) is in straight-line interpreted terms, so (2) does not touch it.
- The 3 largest compC/join intermediates were not measured: a `dbgTrace` in `compC` breaks `CRel.lean:50`. Next step is
  a trace outside the proved definitions (e.g. in `Lang/Eval.lean` around `ck (compC ..)` calls) or `perf` on
  `bit_rows_pass`, which is 5% of SudokuPC9.
- Chess: elab-only 27.9 s of 32.8 s wall, so the cost is elaborating the program (`rel_program` expansion), not running
  it; for the other files elab-only is the 0.5-0.7 s import cost, and the whole wall is `#guard` evaluation.
- Setups used the oleans of `/home/dh/repo/freyd/leetq/.lake` (main checkout at run time), not this branch's rebuild.
- Rerun: `doc/rel-bench/bench.sh` (needs `/data/tmp/rel-141`), `doc/rel-bench/trace.sh` (needs the scratch copy), then
  `doc/rel-bench/mktable.sh > doc/rel-bench.md`.
