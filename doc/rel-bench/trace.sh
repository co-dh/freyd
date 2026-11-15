#!/bin/bash
# usage: trace.sh  -- round counts and per-round row changes of every mu/nu/AC-3 loop.
# Traces in a SCRATCH copy of leetq ($O/scratch), never in place (a trace in `fixOnC`/`acFixC`/`compC` breaks the proofs
# that unfold them, `CRel.lean:50`, `AC3.lean:355,399`). gen-trace.patch edits the scratch Lang/Gen.lean: `nu`/`mu`
# wrap the step of `CRel.fixOn` in dbgTrace ("NU in n" / "MU in n": rows of X entering a round) and `nuAC` runs
# `acFixTr`, a traced copy of `acFixC` ("ACFIX start n", "ACFIX round k: X -> X' delta U->U'").
# Output: $O/trace/<M>.log, then summary.tsv via summarize.awk.
W=${W:-$(cd "$(dirname "$0")/../.." && pwd)}
Q=${Q:-/home/dh/repo/qlean}
O=${O:-/data/tmp/rel-141b}
S=$O/scratch; T=$O/trace; H=$W/doc/rel-bench
SPECS="Programs/Chess Programs/SudokuPC9 Lang/TestChess Lang/TestKnapsack Lang/TestEdit Lang/TestDetab Lang/Test"
rm -rf $S $T; mkdir -p $S $T
cp -a $W/. $S/ || exit 1  # whole checkout: leetq requires its parent package
patch -p1 -d $S/leetq < $H/gen-trace.patch || exit 1
echo $SPECS | tr ' ' '\n' | sed 's|/|.|; s|^|LeetQ.Rel.|' | xargs env CAP_MEM_MB=13000 $W/scripts/cap lake -d $S/leetq -K qlean=$Q build > $T/build.log 2>&1 || { echo "scratch build failed: tail $T/build.log" >&2; exit 1; }
for spec in $SPECS; do
  D=${spec%/*}; M=${spec#*/}
  lake -d $S/leetq -K qlean=$Q env lean --setup $S/leetq/.lake/build/ir/LeetQ/Rel/$D/$M.setup.json $S/leetq/LeetQ/Rel/$D/$M.lean > $T/$M.log 2>&1
  awk -f $H/summarize.awk -v m=$M $T/$M.log
done > $T/summary.tsv
cat $T/summary.tsv
