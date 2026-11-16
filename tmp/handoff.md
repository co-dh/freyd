# filter / takewhile soundness — handoff

Done (WIP, may not build yet): in `leetq/LeetQ/Rel/CRelList.lean`, section `filter(p)`, `takewhile(p)` (before
`#print axioms rep_concatC`): helpers `gatherT_get`, `countBefore_get`, `keyBitsC_bit`, `filter_window`,
`range_succ_map`, `first_set`, `takeWhile_window`, `filter_range_le`, `row_window`, `rep_rowwise`, and main
`rep_filterC`, `rep_takewhileC`.

Left: make the module build (`scripts/cap lake -d leetq -K qlean=/home/dh/repo/qlean build LeetQ.Rel.CRelList`);
add `CRel.rep_filter`/`CRel.rep_takewhile` (pattern of `CRel.rep_cons`: `guard_eq ok hb`); add `Gen.filter_sound`,
`Gen.takewhile_sound` in `Rel/Lang/GenSpec.lean` over `elems B B (.arr B) d R CRel.filter` with `hR : Sound R TR`;
set the two rows' `sound` in `Run/Lang/Syntax.lean` (line ~165) and fix the comment; run the gate.
