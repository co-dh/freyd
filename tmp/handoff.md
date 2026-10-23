# k-scan handoff (WIP)

Branch: worktree-agent-aa0fa9d63b93240fe. File: leetq/LeetQ/Rel/Scan.lean only.

Done
- countBy / lastBy / overBy read `grp d o`'s offsets as segments (`offs`, `ends`, `sizes`; `Ew.val` for
  `1_deltas o` and `-1+1_o`; `groupedOver … (.segs ob) … (tilLongs g)` for overBy at every type, `rt := .long`).
  `groupIds` and the `.ids` path are gone (no unsegmented key reaches these ops).
- Spec.mmin replaced by `Spec.mext` (q's seed + older-wins ties); guards for mmin/mmax seeds, `3 mmax 0N 0N 0N 1`,
  foR (mwinFoR), boolean bitmap (mwinBitmap), mcount; int overBy guards.
- Helper lemmas pass: get!_eq (check), bitsAt_congr, bitsAt_succ, atI64_eq, bitsAt_extract (general `a`),
  bitsAt_zeros, foldl_append, bitsAt_foldl_append, tilLongs_spec, groupCells_til, filter_range_seg, groupedOver_long.

Left
- `overSegments_slot`: whnf heartbeat timeout around the `show (Column.bitsAt (one s) (0 + 0) 8).toInt64 = _` /
  `rw [Nat.zero_add, hv0, …]` lines.
- `overBy_bytes` last step: `rw [List.map_congr_left …]` fails to find `List.map (fun i => x.toList[?] !) ?`;
  goal after `foldl_filter, Spec.over, List.map_map` is foldl over `map (min lo n + ·) (range L)` on both sides,
  RHS mapped through `(fun i => x.toList[i]!) ∘ (min lo n + ·)`. Plan: `List.foldl_map` both sides then a
  `foldl_congr_mem` lemma (elementwise congruence over list members).
- Then: full build command from the brief, bench msum/mmin/mmin1000 at 1e7, commit.

Check one file: `scripts/cap lake -R -d <wt>/leetq -K qlean=/home/dh/repo/qlean lean <wt>/leetq/LeetQ/Rel/Scan.lean`
(sandbox off; plain `lean` cannot load qlean's native initializers).
