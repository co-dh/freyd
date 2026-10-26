# amend verb (op = some v) — handoff at the 40-call checkpoint

Work file: leetq/LeetQ/Rel/AmendProbe.lean (temporary module importing LeetQ.Rel.SpecStruct; build with
`env CAP_MEM_MB=32768 scripts/cap lake -R -d <wt>/leetq -K qlean=/data/tmp/hs3/qlean build LeetQ.Rel.AmendProbe`,
outside the sandbox; plain `lean` cannot load qlean's externs). Move into SpecStruct.lean after `amend_rel` when done,
and refactor `amend_toList`'s local `dn`/`pkd` onto `bytesOf_fixed`/`packed_fixed`.

Done (compiles): `bytesOf_fixed`, `packed_fixed`, `wf_bytes`, `filter_le_one`, `vec_gather`, `rank_pairwise`,
`amend_round` (one gather -> Ew.dyad -> scatter round, positions naming distinct indices, per position a foldl of f),
`foldM_inv` (Nat.foldM in Except, via loop's two rfl equations; `Nat.foldM.loop` is hygienic, cannot be named),
`filter_lt_succ` (ranks below r+1 = below r ++ at r, along a list where rank strictly rises).
`filter_reindex` had two small errors being fixed at the checkpoint.

Left: main theorem `amend_toList` for `some v`:
- element hypothesis `hdy` (Arr level: dense `cur`, any `yv`, Ew.dyad ⟹ R.toList = zipWith f), instantiate at long
  from `val_spec_long` / `val_spec_long_bF` + `Ew.elem_long_val`.
- rounds ≤ 1: all ranks 0 ⟹ injective indices; one `amend_round` with ix = ib, yv = y.
- rounds > 1: `foldM_inv` with invariant per position: acc[j] = x[j].map (foldl f · (y at positions naming j of
  rank < rr)); round rr's ks = slice of `amendRounds_grouped`'s grouped list (`blocks_get`, `countP_lt_sum`,
  `elemsW_extract`), ixr = gatherBytes 8 0 ib ks, yv = vec_gather of y at ks; `filter_reindex` + `filter_lt_succ`.
- final: foldl_set_getElem? as in the `:` proof; `amend_rel` over op from `ix_amendSpec`.
