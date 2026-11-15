# Reads a trace log. A "NU in n" / "MU in n" line is the size of X entering a round; a run of them ends where the next
# loop starts, detected by n restarting (MU: from 0) or a size increase for NU. An "ACFIX round" line carries the round's
# X -> X' and delta. Prints one line per loop with >= 3 rounds: file kind rounds |X| first/last median-delta% max-delta%.
function flush(  i, n, d, p, m, mx, s) {
  if (cnt < 3) { cnt = 0; return }
  n = 0
  for (i = 2; i <= cnt; i++) { d = x[i] - x[i-1]; if (d < 0) d = -d; p = (x[i] > x[i-1] ? x[i] : x[i-1]); if (p > 0) { n++; r[n] = 100 * d / p } }
  # median over rounds after round 1 (rounds 2..): r[1] is the round-1 change, so start at 2
  m = 0; k = 0
  for (i = 2; i <= n; i++) { k++; q[k] = r[i]; if (r[i] > mx) mx = r[i] }
  for (i = 1; i <= k; i++) for (j = i + 1; j <= k; j++) if (q[j] < q[i]) { t = q[i]; q[i] = q[j]; q[j] = t }
  m = k ? q[int((k + 1) / 2)] : 0
  printf "%s\t%s\t%d\t%d->%d\t%.1f\t%.1f\n", M, kind, cnt, x[1], x[cnt], m, mx
  cnt = 0
}
/^(NU|MU) in / { k = $1; n = $3 + 0
  if (cnt > 0 && (k != kind || (k == "MU" && n == 0) || (k == "NU" && n > x[cnt]))) flush()
  kind = k; cnt++; x[cnt] = n; next }
/^ACFIX start / { flush(); kind = "ACFIX"; cnt = 1; x[1] = $3 + 0; next }
/^ACFIX round / { cnt++; x[cnt] = $6 + 0; next }
END { flush() }
BEGIN { M = m }
