# Step 1 (keyCodes path) WIP — checkpoint at tool call 40

Scratch module `leetq/LeetQ/Rel/KeyScratch.lean` (imports SpecStruct; builds in ~4 s:
`scripts/cap lake -d <wt>/leetq -K qlean=/data/tmp/hs2/qlean build LeetQ.Rel.KeyScratch`, outside sandbox).
To be moved into SpecStruct.lean (after `ej_rel_lane`) once the step lands, then deleted.

Done, green: foldl_lesser, foldl_greater, mapM_pair_some, mapM_pair_ok, mapM_pair_P, enumIds_bytes,
bitsAt_of_elemsW, val_add_word, rebase_word, codeKind_spec.

Left: `rangeOffsets_long` (for `#[cl, cr]` with `longWords` = some, `total ≤ 2^32`): unfold, `split at h`
over the three mapM matches, bounds via mapM_pair_P + overBytes_eq / over_eq + foldl_lesser/greater, parts via
mapM_pair_P + rebase_word (bytes: E = Ew.val …; foR: foRShift_spec / decodeW) + enumIds_bytes; then
keyCodes wrapper; then ej law = ej_rel_lane + wrapper.

Finding: without `total ≤ 2^32`, an i64 code lane (span > 2^63) can rebase a non-null value onto
Int64.minValue, which enumIds codes as the null → a null and that value share a code.
