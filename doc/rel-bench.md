# Rel corpus benchmark (rel-141b)

Rows ranked by wall (median of 3, seconds; the load average beside each timing is in `/data/tmp/rel-141b/out/*.t.*`, a run above
nproc/2 was redone). elab-only is the same file with the `#guard` lines removed. Buckets are the self time of one perf
run: interpreter = `lean::ir::*`; kernel = `qlean_*` / `libqleankernel.so`; LeetQ native = `lp_leetq_LeetQ_*` /
`l_LeetQ_*` (the precompiled LeetQ); other = the rest. rounds: mu/nu loops of >= 3 rounds, traced in a scratch copy.

## Provenance

Every row: commit `300004c`, one command: `doc/rel-bench/bench.sh`, which builds `LeetQ` (precompiled, the
`rel_program` expansion runs natively), then for each of the 9 `Lang/Test*.lean` and every `Programs/*.lean` times
`lake -d leetq -K qlean=/home/dh/repo/qlean env lean --setup <Module>.setup.json <file>` (zsh/bash `time`, wall) and
runs `perf record -F 4000 -g` on it. A program's run cost is now the elaboration of its module (`Lang/Eval.lean` is
deleted; `Lang/Gen.lean` + `Lang/Expand.lean` expand `rel_program` into `CRel` constants). The old table below was
measured at 1ab50df with the interpreter and is not comparable with a table of another commit or command.

| file | wall | elab-only | interp% | kernel% | LeetQ native% | other% | top symbol | top 3 LeetQ native | mu/nu rounds | median delta% per round after round 1 |
|------|------|-----------|---------|---------|---------------|--------|------------|--------------------|--------------|----------------------------------------|
| TestChess | 15.0 | 7.2 | 0.1 | 38.6 | 7.3 | 50.8 | qlean_structural_enum_ids 8.23% | lp_leetq_LeetQ_Rel_Lang_Expand_hex 3.05%; lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.41%; lp_leetq_LeetQ_Rel_Lang_Expand_fv___redArg 0.34% | NU 11r 489->81; MU 4r 5->11; ACFIX 3r 20->8 | 9.7; 9.1; 0.0 |
| Chess | 3.4 | 1.5 | 0.1 | 33.7 | 8.0 | 60.3 | qlean_structural_enum_ids 7.82% | lp_leetq_LeetQ_Rel_Lang_Expand_hex 3.33%; lp_leetq_LeetQ_Rel_Lang_Expand_fv___redArg 0.64%; lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.41% | none traced |  |
| Test | 3.3 | 2.0 | 0.2 | 11.7 | 3.8 | 87.5 | lean_dec_ref_cold 10.98% | lp_leetq_LeetQ_Rel_Lang_Expand_hex 0.37%; lp_leetq_LeetQ_Rel_Lang_Expand_fv___redArg 0.32%; lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.32% | NU 11r 489->81; MU 4r 5->11; ACFIX 3r 20->8; ACFIX 3r 20->8 | 9.7; 9.1; 0.0; 0.0 |
| TestDetab | 1.6 | 0.7 | 30.1 | 7.6 | 3.0 | 60.0 | interp::eval_body(lean::object_ref const&) 10.35% | lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.27%; lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.26%; lp_leetq_LeetQ_Rel_Alg_pick 0.26% | none traced |  |
| TestKnapsack | 1.6 | 1.4 | 0.1 | 19.9 | 7.1 | 74.1 | lean_dec_ref_cold 8.86% | lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.89%; lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.39%; lp_leetq_LeetQ_Rel_Alg_expand___redArg 0.38% | NU 11r 489->81; MU 4r 5->11; ACFIX 3r 20->8 | 9.7; 9.1; 0.0 |
| TestWumpus | 1.3 | 1.2 | 0.1 | 21.1 | 4.7 | 73.7 | lean_dec_ref_cold 7.53% | lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.53%; lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.38%; lp_leetq_LeetQ_Rel_Alg_pairCode 0.29% | none traced |  |
| TestSelsort | 1.2 | 1.2 | 0.0 | 22.9 | 4.6 | 71.6 | lean_dec_ref_cold 8.03% | lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.55%; lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.24%; lp_leetq_LeetQ_Rel_Alg_codes 0.21% | none traced |  |
| TestMss | 1.2 | 1.2 | 0.1 | 22.0 | 4.3 | 72.6 | lean_dec_ref_cold 7.40% | lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.49%; lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.29%; lp_leetq_LeetQ_Rel_Alg_expand___redArg 0.29% | none traced |  |
| TestCircuit | 1.2 | 1.1 | 0.1 | 22.7 | 5.2 | 70.7 | lean_dec_ref_cold 7.64% | lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.54%; lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.38%; lp_leetq_LeetQ_Rel_Alg_codes 0.35% | none traced |  |
| TestEdit | 1.1 | 1.0 | 0.1 | 9.3 | 3.7 | 85.0 | lean_dec_ref_cold 9.87% | lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.36%; lp_leetq_LeetQ_Rel_Alg_pairCode 0.27%; lp_leetq_LeetQ_Rel_Alg_place___redArg 0.24% | none traced |  |
| Edit | 0.9 | 0.7 | 0.1 | 8.1 | 3.4 | 87.8 | lean_dec_ref_cold 8.01% | lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.46%; lp_leetq_LeetQ_Rel_Alg_place___redArg 0.29%; lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.23% | none traced |  |
| SudokuPC9 | 0.9 | 0.6 | 0.0 | 40.9 | 1.5 | 58.3 | bit_rows_pass 15.21% | lp_leetq_LeetQ_Rel_Lang_Expand_hex 1.29%; lp_leetq_LeetQ_Rel_Lang_Parse_builtin___lam__0___boxed 0.04%; lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.03% | NU 13r 337565->62700 | 3.7 |
| Knapsack | 0.8 | 0.6 | 0.1 | 4.6 | 4.2 | 91.6 | lean_dec_ref_cold 7.87% | lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.41%; lp_leetq_LeetQ_Rel_Alg_pick 0.23%; lp_leetq_LeetQ_Rel_Alg_Code_cat 0.22% | none traced |  |
| Detab | 0.8 | 0.7 | 0.1 | 3.9 | 1.6 | 95.0 | lean_dec_ref_cold 8.71% | lp_leetq_LeetQ_Rel_Lang_Expand_hex 0.26%; lp_leetq_LeetQ_Rel_Obj_codesC_atomFit 0.12%; lp_leetq_LeetQ_Rel_Alg_pairCode 0.11% | none traced |  |
| Blocks | 0.7 | 0.6 | 0.0 | 5.5 | 2.1 | 92.4 | lean_dec_ref_cold 7.21% | lp_leetq_LeetQ_Rel_Lang_Expand_fv___redArg 0.39%; lp_leetq_LeetQ_Rel_Lang_Expand_hex 0.25%; lp_leetq_LeetQ_Rel_Alg_rangeOffsets 0.24% | none traced |  |
| Selsort | 0.6 | 0.6 | 0.1 | 3.6 | 0.6 | 95.9 | lean_mark_persistent 7.14% | lp_leetq_LeetQ_Rel_Vals_pick___redArg 0.19%; lp_leetq_LeetQ_Rel_Alg_expand___redArg 0.10%; lp_leetq_LeetQ_Rel_Arr_enc___redArg 0.09% | none traced |  |
| JobShop | 0.6 | 0.6 | 0.2 | 2.2 | 1.3 | 96.4 | lean_mark_persistent 6.97% | lp_leetq_LeetQ_Rel_Lang_Expand_hex 0.46%; lp_leetq_LeetQ_Rel_Alg_rangeOffsets___lam__2 0.09%; lp_leetq_LeetQ_Rel_Alg_Code_column 0.09% | none traced |  |
| Wumpus | 0.6 | 0.6 | 0.1 | 0.0 | 0.0 | 100.0 | lean_mark_persistent 7.57% |  | none traced |  |
| Mss | 0.6 | 0.6 | 0.1 | 0.3 | 0.3 | 99.2 | lean_mark_persistent 7.77% | lp_leetq_LeetQ_Rel_Lang_Expand_hex 0.10%; lp_leetq_LeetQ_Rel_Alg_codes 0.05%; lp_leetq_LeetQ_Rel_Lang_Expand_planOr 0.05% | none traced |  |
| SudokuAC | 0.6 | 0.6 | 0.2 | 0.1 | 0.1 | 99.5 | lean_mark_persistent 8.25% | lp_leetq_LeetQ_Rel_Lang_Parse_builtin___lam__0___boxed 0.05%; lp_leetq_LeetQ_Rel_Lang_Parse_isSym 0.05% | none traced |  |
| SudokuPC | 0.6 | 0.6 | 0.1 | 0.4 | 0.1 | 99.5 | lean_mark_persistent 9.22% | lp_leetq_LeetQ_Rel_Lang_Expand_hex 0.10% | none traced |  |
| Prelude | 0.6 | 0.6 | 0.1 | 0.0 | 0.1 | 99.2 | lean_mark_persistent 7.61% | lp_leetq_LeetQ_Rel_Lang_Embed_prim 0.07%; lp_leetq_LeetQ_Rel_Lang_Embed_posOf 0.07% | none traced |  |
| Circuit | 0.6 | 0.6 | 0.2 | 0.0 | 0.2 | 99.5 | lean_mark_persistent 8.61% | lp_leetq_LeetQ_Rel_Obj_codesC 0.05%; lp_leetq_LeetQ_Rel_Alg_pick 0.05%; lp_leetq_LeetQ_Rel_Lang_Expand_fv___redArg 0.04% | none traced |  |

Corpus wall total 39.8 s (LeetQ native self time 2.0 s = 5%).

- (1) remaining interpreter time: 0.5 s = 1% of the total (upper bound: alloc/RC under interpreted code stays).
- (2) semi-naive mu/nu: files running a >= 3-round loop take 20.7 s = 52% of the total (upper bound; the loops themselves are a part of that).
- (3) fused kernels: qlean kernel self time is 9.5 s = 24% of the total.

## Before (1ab50df, stage 1, interpreter)

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

Rerun: `doc/rel-bench/bench.sh` (builds, times, perfs, traces, writes this file).
