#!/bin/bash
# usage: bench.sh   -- the whole pipeline at the current checkout: build, time + perf every file of the corpus
# (the 9 Lang/Test*.lean + Programs/*.lean), trace the mu/nu rounds, write doc/rel-bench.md. One commit, one command.
# Needs a seeded worktree (.lake and leetq/.lake copied from the main checkout), perf, and /data/tmp. One file at a
# time: timings under parallel load are useless.
W=${W:-$(cd "$(dirname "$0")/../.." && pwd)}
Q=${Q:-/home/dh/repo/qlean}
H=$W/doc/rel-bench
export W Q O=${O:-/data/tmp/rel-141b}
mkdir -p $O/out
rm -f $O/out/*.tsv
env CAP_MEM_MB=13000 $W/scripts/cap lake -d $W/leetq -K qlean=$Q build LeetQ > $O/build.log 2>&1 || { echo "build failed: tail $O/build.log" >&2; exit 1; }
for f in $W/leetq/LeetQ/Rel/Lang/Test*.lean; do
  m=$(basename $f .lean); case $m in TestChess|TestCircuit|TestDetab|TestEdit|TestKnapsack|TestMss|TestSelsort|TestWumpus|Test) $H/bench-one.sh Lang $m || exit 1;; esac
done
for f in $W/leetq/LeetQ/Rel/Programs/*.lean; do $H/bench-one.sh Programs $(basename $f .lean) || exit 1; done
echo -e "file\twall user sys load\telab wall\tinterp%\tkernel%\tnative%\tother%\ttop\ttop3native" > $O/table.tsv
cat $O/out/*.tsv | sort -t$'\t' -k2 -rn >> $O/table.tsv
$H/trace.sh || exit 1
git -C $W rev-parse --short HEAD > $O/sha
$H/mktable.sh > $W/doc/rel-bench.md
