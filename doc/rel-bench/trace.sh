#!/bin/bash
# usage: trace.sh  -- round counts and per-round row changes of every mu/nu/AC-3 loop, from the scratch copy of leetq
# (/data/tmp/rel-141/scratch/leetq) whose Lang/Gen.lean wraps the step of `nu`/`mu` in dbgTrace ("NU in n" / "MU in n":
# the rows of X entering a round) and runs nuAC through a traced copy of acFixC ("ACFIX round k: X -> X' delta U->U'").
# Output: /data/tmp/rel-141/trace/<M>.log, then summary.tsv via summarize.awk.
S=/data/tmp/rel-141/scratch/leetq; T=/data/tmp/rel-141/trace; mkdir -p $T
for spec in Programs/Chess Programs/SudokuPC9 Lang/TestChess Lang/TestKnapsack Lang/TestEdit Lang/TestDetab Lang/Test; do
  D=${spec%/*}; M=${spec#*/}
  lake -d $S -K qlean=/home/dh/repo/qlean env lean --setup $S/.lake/build/ir/LeetQ/Rel/$D/$M.setup.json $S/LeetQ/Rel/$D/$M.lean > $T/$M.log 2>&1
  awk -f "$(dirname "$0")/summarize.awk" -v m=$M $T/$M.log
done > $T/summary.tsv
cat $T/summary.tsv
