#!/bin/bash
# usage: mktable.sh > doc/rel-bench.md   (after bench.sh's timings and trace.sh; reads $O/{table.tsv,sha,trace/summary.tsv})
# Candidate shares are computed here from the table: (1) = sum(wall*interp%), (3) = sum(wall*kernel%), both over sum(wall);
# (2) = wall of the files that run a mu/nu loop of >= 3 rounds, over sum(wall), an upper bound.
W=${W:-$(cd "$(dirname "$0")/../.." && pwd)}
O=${O:-/data/tmp/rel-141b}
SHA=$(cat $O/sha)
cat <<EOF
# Rel corpus benchmark (rel-141b)

Rows ranked by wall (median of 3, seconds; the load average beside each timing is in \`$O/out/*.t.*\`, a run above
nproc/2 was redone). elab-only is the same file with the \`#guard\` lines removed. Buckets are the self time of one perf
run: interpreter = \`lean::ir::*\`; kernel = \`qlean_*\` / \`libqleankernel.so\`; LeetQ native = \`lp_leetq_LeetQ_*\` /
\`l_LeetQ_*\` (the precompiled LeetQ); other = the rest. rounds: mu/nu loops of >= 3 rounds, traced in a scratch copy.

## Provenance

Every row: commit \`$SHA\`, one command: \`doc/rel-bench/bench.sh\`, which builds \`LeetQ\` (precompiled, the
\`rel_program\` expansion runs natively), then for each of the 9 \`Lang/Test*.lean\` and every \`Programs/*.lean\` times
\`lake -d leetq -K qlean=/home/dh/repo/qlean env lean --setup <Module>.setup.json <file>\` (zsh/bash \`time\`, wall) and
runs \`perf record -F 4000 -g\` on it. A program's run cost is now the elaboration of its module (\`Lang/Eval.lean\` is
deleted; \`Lang/Gen.lean\` + \`Lang/Expand.lean\` expand \`rel_program\` into \`CRel\` constants). The old table below was
measured at 1ab50df with the interpreter and is not comparable with a table of another commit or command.

| file | wall | elab-only | interp% | kernel% | LeetQ native% | other% | top symbol | top 3 LeetQ native | mu/nu rounds | median delta% per round after round 1 |
|------|------|-----------|---------|---------|---------------|--------|------------|--------------------|--------------|----------------------------------------|
EOF
awk -F'\t' -v sum=$O/trace/summary.tsv 'BEGIN { while ((getline l < sum) > 0) { split(l, a, "\t"); r[a[1]] = r[a[1]] (r[a[1]] ? "; " : "") a[2] " " a[3] "r " a[4]; d[a[1]] = d[a[1]] (d[a[1]] ? "; " : "") a[5] } }
NR > 1 { split($2, w, " "); top = $8; sub(/lean::ir::interpreter::/, "interp::", top)
  printf "| %s | %.1f | %.1f | %.1f | %.1f | %.1f | %.1f | %s | %s | %s | %s |\n", $1, w[1], $3, $4, $5, $6, $7, substr(top, 1, 60), $9, (($1 in r) ? r[$1] : "none traced"), (($1 in d) ? d[$1] : "") }' $O/table.tsv
echo
awk -F'\t' -v sum=$O/trace/summary.tsv 'BEGIN { while ((getline l < sum) > 0) { split(l, a, "\t"); loop[a[1]] = 1 } }
NR > 1 { split($2, w, " "); tot += w[1]; i += w[1] * $4 / 100; k += w[1] * $5 / 100; n += w[1] * $6 / 100; if ($1 in loop) f += w[1] }
END { printf "Corpus wall total %.1f s (LeetQ native self time %.1f s = %.0f%%).\n\n- (1) remaining interpreter time: %.1f s = %.0f%% of the total (upper bound: alloc/RC under interpreted code stays).\n- (2) semi-naive mu/nu: files running a >= 3-round loop take %.1f s = %.0f%% of the total (upper bound; the loops themselves are a part of that).\n- (3) fused kernels: qlean kernel self time is %.1f s = %.0f%% of the total.\n", tot, n, 100*n/tot, i, 100*i/tot, f, 100*f/tot, k, 100*k/tot }' $O/table.tsv
echo
echo "## Before (1ab50df, stage 1, interpreter)"
echo
cat $W/doc/rel-bench/before-stage1.md
echo
echo "Rerun: \`doc/rel-bench/bench.sh\` (builds, times, perfs, traces, writes this file)."
