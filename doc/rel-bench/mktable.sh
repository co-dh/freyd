#!/bin/bash
# usage: mktable.sh > doc/rel-bench.md   (after bench.sh and trace.sh; reads /data/tmp/rel-141/{table,trace/summary}.tsv)
# Candidate shares are computed here from the table: (1) = sum(wall*interp%), (3) = sum(wall*kernel%), both over sum(wall);
# (2) = wall of the files that run a mu/nu loop of >= 3 rounds, over sum(wall), an upper bound.
T=/data/tmp/rel-141
echo "# Rel corpus benchmark (rel-141)"
echo
echo "Rows ranked by wall (median of 3, seconds; load average beside each timing is in /data/tmp/rel-141/out/*.t.*)."
echo "elab-only is the same file with the #guard lines removed. interp/kernel/other: self time of one perf run"
echo "(interpreter = lean::ir::interpreter*; kernel = qlean_* / libqleankernel.so). rounds: mu/nu loops of >= 3 rounds."
echo
echo "| file | wall | elab-only | interp% | kernel% | other% | top symbol | mu/nu rounds | median delta% per round after round 1 |"
echo "|------|------|-----------|---------|---------|--------|------------|------------|------------------------------|"
awk -F'\t' -v sum=$T/trace/summary.tsv 'BEGIN { while ((getline l < sum) > 0) { split(l, a, "\t"); r[a[1]] = r[a[1]] (r[a[1]] ? "; " : "") a[2] " " a[3] "r " a[4]; d[a[1]] = d[a[1]] (d[a[1]] ? "; " : "") a[5] } }
NR > 1 { split($2, w, " "); split($7, t, "; "); top = t[1]; sub(/\(.*\)/, "", top); sub(/lean::ir::interpreter::/, "interp::", top)
  printf "| %s | %.1f | %.1f | %.1f | %.1f | %.1f | %s | %s | %s |\n", $1, w[1], $3, $4, $5, $6, substr(top, 1, 60), (($1 in r) ? r[$1] : "none traced"), (($1 in d) ? d[$1] : "") }' $T/table.tsv
echo
awk -F'\t' -v sum=$T/trace/summary.tsv 'BEGIN { while ((getline l < sum) > 0) { split(l, a, "\t"); loop[a[1]] = 1 } }
NR > 1 { split($2, w, " "); tot += w[1]; i += w[1] * $4 / 100; k += w[1] * $5 / 100; if ($1 in loop) f += w[1] }
END { printf "Corpus wall total %.1f s.\n\n- (1) precompile: interpreter self time is %.1f s = %.0f%% of the total (upper bound: alloc/RC inside interpreted code stays).\n- (2) semi-naive mu/nu: files running a >= 3-round loop take %.1f s = %.0f%% of the total (upper bound; the loops themselves are a part of that).\n- (3) fused kernels: qlean kernel self time is %.1f s = %.0f%% of the total; intermediate sizes: see the list below.\n", tot, i, 100*i/tot, f, 100*f/tot, k, 100*k/tot }' $T/table.tsv
