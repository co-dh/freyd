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
