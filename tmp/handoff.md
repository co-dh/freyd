# Step 1 handoff (WIP, budget reached)

## Done
- AOP/A6_FinRel.lean: `FibreIndex.scan` is a plain `def` (no instance). Added `[FibreIndex (K × L)] [FibreIndex (V × W)]
  [FibreIndex (K ⊕ L)]` section variables (Tabulate), `[FibreIndex (E × V)]` (Fold), `[FibreIndex C]` on `mem_comp`,
  `symmDiv`, `rel_symmDiv`. Added `Hashable (α ⊕ β)` instance and `deriving instance Hashable for CL.ConsList`
  before `FibreIndex.hash`.
- 13 spec-only AOP chapter files (A7_3, A7_4, A7_5, A8_2, A8_4, A8_5, A8_6, A9_2, A9_3, A9_4, A10_2, A10_3, A10_4):
  `attribute [local instance low] Freyd.Alg.RelSet.FibreIndex.scan` after the imports (abstract key types, never executed).
  `lake build AOP` was green before the last Sum/ConsList instance edit; re-run it (the last run printed no errors).
- leetq: `[Hashable X]` added next to `[DecidableEq X]` in Rel/Basis, Rel/Container, Rel/Verbs; in Q/Agg, Q/List,
  Q/Table, Compressed, Group every `[FibreIndex X]` binder became `[Hashable X]`; `QF` derives Hashable;
  Verbs.lean: two trailing tactics (`simp only …; rfl`) after msum_spec removed (were "No goals").

## Left
- `./scripts/cap lake -K qlean=/home/dh/repo/qlean -d leetq build LeetQ.Rel.Test LeetQ.Long LeetQ.Q.Table bench`
  (leetq needs an untracked `leetq/lake-manifest.json` with qlean dir `/home/dh/repo/qlean` and `cp -a` of
  `/home/dh/repo/freyd/leetq/.lake/build`; do not commit the manifest).
- Remaining errors in leetq/LeetQ/Q/Table.lean: `don't know how to synthesize implicit argument
  @FibreIndex.get κ (?m …) FibreIndex.hash …` at lines ~303 (`FibreIndex.dedupA`), ~579-581 (`FibreIndex.get`, ajFast).
  Cause: the `DecidableEq` argument of `FibreIndex.*` is a plain implicit, previously fixed by unifying with the local
  `[FibreIndex K]` instance. Fixed for domP (:92) and look (:97) by `@FibreIndex.f K inferInstance FibreIndex.hash …`;
  do the same at the other call sites (or make the class's DecidableEq argument inst-implicit in AOP).
- Then Rel.Test `#guard`s, Long, Group, Compressed, bench; check axioms; re-run `lake build AOP`.
- Bench ops `relEach2` / `relZipD`: cherry-pick `git cherry-pick e3647a0` (only touches leetq/Bench/Main.lean), then time
  1e4/1e5/1e6, 3 runs each, separate processes. Not started.
