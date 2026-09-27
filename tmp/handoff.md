# Handoff — tabular AOP hylomorphism/greedy, 11.6.4c removal

Done (commit 4cd2694 on worktree-agent-af2582376f0111bfb):
- AOP/A6_3: `relCata_alpha`/`relCata_alpha_UP` stay in `section Alpha` over `UnguardedPowerLCDA`; the rest
  is over `TabularUnitaryUnguardedPowerLCDA`, no `hFr` anywhere; `hylo_eq_mu_step1/2` inlined into `hylo_eq_mu`.
- AOP/A7_2: Greedy section tabular; `greedy_step1`, `greedy`, `greedy_of_refinement` (moved into it) lose `hFr`.
- AOP/A7_4_Horner `greedy_of_refinement_mono` tabular, no `hFr`. Call sites fixed in A6_4_FastExp,
  A7_3_Party, A7_5_Van, A7_7_{MSS,Filter,TakeWhile}, A8_1, A9_0_SegmentExample, A9_1, A9_2, A10_1,
  A10_3_Tardy, A10_4_Tex (elaborates against the tabular RelSet instance), leet/L104_derived.
- Note: 11.6.4c chain removed from `<hylo-mu>`; 11.6.2c header (`relCata_UP`) states the tabular setup;
  gr-mon/gr-Rbare back to master's two calls. Markers refreshed.
- Gates green: lake build Freyd AOP diag, make cite, make c CH=11/13/14/15/16; L104 typechecks with lean.

Left:
- `hFr` still carried in sections that are ALREADY tabular: A7_2 Thm71 (`mon_thm71_step1/4`,
  `monoAlg_iff_distributes`, ...), A8_1 `thinning*`, A8_2, A8_3, A9_2, A10_1, A10_3. Dropping them is the
  same rule; mon-thm71's marks were frozen pending a peer branch, so not touched.
- `relCata_UP` (AOP/A5_5) is over `UnguardedPowerAllegory`, not tabular: restricting it would break the
  general `relCata_alpha` (used by A6_5). The 11.6.2c header states the stronger setup in prose only.
- tmp/rv/s2.png (11.6.4b rows alone) not cut: the rows are inside s1.png's display.
