#!/bin/bash
# usage: bench.sh   -- whole corpus (9 Lang/Test*.lean + Programs/*.lean), one TSV sorted by wall (3rd... col 2)
# one file at a time: timings under parallel load are useless. Output: /data/tmp/rel-141/table.tsv
W=${W:-/home/dh/repo/freyd/.claude/worktrees/agent-a79121e1a753abb4b}
H=$(dirname "$0")
O=/data/tmp/rel-141; mkdir -p $O/out
for f in $W/leetq/LeetQ/Rel/Lang/Test*.lean; do
  m=$(basename $f .lean); case $m in TestChess|TestCircuit|TestDetab|TestEdit|TestKnapsack|TestMss|TestSelsort|TestWumpus|Test) $H/bench-one.sh Lang $m;; esac
done
for f in $W/leetq/LeetQ/Rel/Programs/*.lean; do $H/bench-one.sh Programs $(basename $f .lean); done
echo -e "file\twall user sys load\telab wall user sys load\tinterp%\tkernel%\tother%\ttop5" > $O/table.tsv
cat $O/out/*.tsv | sort -t$'\t' -k2 -rn >> $O/table.tsv
cat $O/table.tsv
