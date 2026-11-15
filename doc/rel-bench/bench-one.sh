#!/bin/bash
# usage: bench-one.sh <Lang|Programs> <Module>   -> $O/out/<Module>.tsv
# one row: module wall(user sys load1) elab_wall interp% kernel% native% other% top1 top3native
# wall/elab = median of 3 by wall of `lake -d $W/leetq -K qlean=$Q env lean --setup <Module>.setup.json <file>`;
# a run whose 1-min load (read after it) is above nproc/2 is redone, and each run waits for the load to drop first.
# The #guard strip is line-based (a #guard plus its indented continuation lines): a bench-only shortcut, the
# stripped copy is never committed. Buckets are perf self time: interpreter = lean::ir::*; kernel = qlean_* /
# libqleankernel.so; LeetQ native = lp_leetq_LeetQ_* / l_LeetQ_* (precompiled LeetQ); other = the rest.
W=${W:-$(cd "$(dirname "$0")/../.." && pwd)}
Q=${Q:-/home/dh/repo/qlean}
O=${O:-/data/tmp/rel-141b}; mkdir -p $O/out
D=$1; M=$2
SRC=$W/leetq/LeetQ/Rel/$D/$M.lean
SET=$W/leetq/.lake/build/ir/LeetQ/Rel/$D/$M.setup.json
[ -f "$SET" ] || { echo "missing $SET: env CAP_MEM_MB=13000 $W/scripts/cap lake -d $W/leetq -K qlean=$Q build LeetQ.Rel.$D.$M" >&2; exit 1; }
HALF=$(( $(nproc) / 2 ))
load() { cut -d' ' -f1 /proc/loadavg; }
over() { awk -v l="$1" -v h=$HALF 'BEGIN { exit !(l > h) }'; }
timeit() { # file tag -> "wall user sys load" (median by wall); every run's line is kept in $O/out/$M.t.<tag>
  local f=$1 i t l
  : > $O/out/$M.t.$2
  for i in 1 2 3; do
    while :; do
      while over "$(load)"; do sleep 20; done
      t=$( { TIMEFORMAT='%R %U %S'; time lake -d $W/leetq -K qlean=$Q env lean --setup $SET "$f" > $O/out/$M.$2.out 2>&1; } 2>&1 | tail -1)
      l=$(load); over "$l" || break
    done
    echo "$t $l" >> $O/out/$M.t.$2
  done
  sort -n $O/out/$M.t.$2 | sed -n 2p
}
FULL=$(timeit $SRC full)
awk '/^#guard/{g=1;next} g&&/^[ \t]/{next} {g=0;print}' $SRC > $O/$M.noguard.lean
EL=$(timeit $O/$M.noguard.lean el | cut -d' ' -f1)
perf record -F 4000 -g -o $O/$M.perf -- lake -d $W/leetq -K qlean=$Q env lean --setup $SET $SRC > /dev/null 2>&1
perf report -i $O/$M.perf --stdio --no-children -g none --sort dso,sym 2>/dev/null | grep -v '^#' | grep -v '^$' > $O/out/$M.rep
awk -v m=$M -v full="$FULL" -v el="$EL" '
{ p=$1; sub("%","",p); d=$2; s=$0; sub(/^ *[0-9.]+% +[^ ]+ +\[[.k]\] /,"",s)
  if (s ~ /lean::ir::|eval_body|interpreter/) i+=p
  else if (d ~ /qleankernel/ || s ~ /^qlean_/) k+=p
  else if (s ~ /^(lp_leetq_LeetQ_|leetq_LeetQ_|l_LeetQ_)/) { nat+=p; if (nn<3) { nt=nt (nn?"; ":"") s " " p "%"; nn++ } }
  else o+=p
  if (n<1 && s!="") { top=s " " p "%"; n++ } }
END { printf "%s\t%s\t%s\t%.1f\t%.1f\t%.1f\t%.1f\t%s\t%s\n", m, full, el, i, k, nat, o, top, nt }' $O/out/$M.rep > $O/out/$M.tsv
rm -f $O/$M.perf
