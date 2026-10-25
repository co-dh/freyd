# leetq -> qlean d16ee01 (header stage 2) handoff

## Done
- qlean d16ee01 cloned at /data/tmp/hs2/qlean (.lake seeded); old ca67f3f at /data/tmp/hs2/qlean-old.
- leetq/.lake seeded. leetq/lake-manifest.json pins the qlean dir: DELETE it whenever switching `-K qlean=`.
- `lean-refactor insert-arg` cannot run on leetq: (1) it reads the declaring file of `QLean.Column.mk`
  from the target's own index, and leetq's index has no qlean; (2) `checkLibraries` treats
  `<qlean>/.lake/build/lib/libqlean_QLean.so` as a copy under leetq's `.lake` and refuses.
- Sweep instead by /data/tmp/hs2/FixCols.lean (`lean --run FixCols.lean <sites>`): sites are the compiler's
  `Insufficient number of fields ... QLean.Column.mk` positions; it appends `, none` (or `_` in a match arm)
  at the bracket-matched `⟩`. rcases/obtain patterns are NOT reported by the compiler: fix by hand
  (bind the 4th field, e.g. Core `get_sym_bytes`).
- Core.lean: Arr fields `attr`/`ix` deleted; `Arr.of` marks via `QValue.IndexCell.new` when attr ≠ 0;
  `c_eq` restated to `x.c = ⟨t, n, e, x.c.attr⟩`; `Parted.of?` carries `o.c.attr`.

## Left
- Build: `CAP_MEM_MB=28000 ./scripts/cap lake -d leetq -K qlean=/data/tmp/hs2/qlean build bench LeetQ.QRel
  LeetQ.Compressed LeetQ.Rel.Core LeetQ.Rel.Find LeetQ.Rel.Scan LeetQ.Rel.Ew LeetQ.Rel.Struct LeetQ.Rel.Algebra`
  (outside sandbox), then FixCols over each wave's errors.
- Find.lean: `x.attr == 1/2` sites -> read `x.c.attr` (byte = `x.c.attr.map (·.1)`); `hu`/`hs` hypotheses
  restated accordingly; check literals `attr := 1/2` -> mark on `c`.
- Scan.lean:897 `(asc xsA).map (·.attr)`.
- Bench results-identical check and timings; commit; report.
