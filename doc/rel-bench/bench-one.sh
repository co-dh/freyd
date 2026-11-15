#!/bin/bash
# usage: bench-one.sh <Lang|Programs> <Module>   -> /data/tmp/rel-141/out/<Module>.tsv
# one row: module wall user sys load1 elab_wall interp% kernel% other% top5
# The #guard strip is line-based (a #guard plus its indented continuation lines): a bench-only shortcut, the
# stripped copy is never committed.
W=${W:-/home/dh/repo/freyd/.claude/worktrees/agent-a79121e1a753abb4b}
Q=${Q:-/home/dh/repo/qlean}
O=/data/tmp/rel-141/out; mkdir -p $O
D=$1; M=$2
SRC=$W/leetq/LeetQ/Rel/$D/$M.lean
SET=$W/leetq/.lake/build/ir/LeetQ/Rel/$D/$M.setup.json
[ -f "$SET" ] || { echo "missing $SET: env CAP_MEM_MB=13000 $W/scripts/cap lake -d $W/leetq -K qlean=$Q build LeetQ.Rel.$D.$M" >&2; exit 1; }
run() { lake -d $W/leetq -K qlean=$Q env lean --setup $SET "$1"; }
export -f run 2>/dev/null
# median of 3 by wall; rerun while 1-min load > nproc/2
timeit() { # file -> "wall user sys load"
  local f=$1 i t
  : > $O/$M.t.$2
  for i in 1 2 3; do
    while [ "$(cut -d' ' -f1 /proc/loadavg | cut -d. -f1)" -ge $(( $(nproc) / 2 )) ]; do sleep 20; done
    t=$( { TIMEFORMAT='%R %U %S'; time lake -d $W/leetq -K qlean=$Q env lean --setup $SET "$f" > $O/$M.$2.out 2>&1; } 2>&1 | tail -1)
    echo "$t $(cut -d' ' -f1 /proc/loadavg)" >> $O/$M.t.$2
  done
  sort -n $O/$M.t.$2 | sed -n 2p
}
FULL=$(timeit $SRC full)
awk '/^#guard/{g=1;next} g&&/^[ \t]/{next} {g=0;print}' $SRC > /data/tmp/rel-141/$M.noguard.lean
EL=$(timeit /data/tmp/rel-141/$M.noguard.lean el | cut -d' ' -f1)
# perf on one full run; buckets by symbol/dso
perf record -F 4000 -g -o $O/$M.perf -- lake -d $W/leetq -K qlean=$Q env lean --setup $SET $SRC > /dev/null 2>&1
perf report -i $O/$M.perf --stdio --no-children -g none --sort dso,sym 2>/dev/null | grep -v '^#' | grep -v '^$' > $O/$M.rep
awk -v m=$M -v full="$FULL" -v el="$EL" '
{ p=$1; sub("%","",p); d=$2; s=$0; sub(/^ *[0-9.]+% +[^ ]+ +\[[.k]\] /,"",s)
  if (s ~ /lean::ir::|eval_body|interpreter/) i+=p; else if (d ~ /qleankernel/ || s ~ /^qlean_/) k+=p; else o+=p
  if (n<5 && s!="") {top=top (n?"; ":"") s " " p "%"; n++} }
END { printf "%s\t%s\t%s\t%.1f\t%.1f\t%.1f\t%s\n", m, full, el, i, k, o, top }' $O/$M.rep > $O/$M.tsv
rm -f $O/$M.perf
