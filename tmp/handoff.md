# handoff: section explaining ∈\ before <dp-upper>

Done
- AOP/A7_1.lean: mem_leftDiv_eq_step1/2/3 added before mem_leftDiv_eq, which is now their `.trans`
  composite. Builds; axioms: step1, step2, mem_leftDiv_eq {propext}; step3 none (rfl).
- diag/ch/15-dynamic.typ: `=== ∈\ as a composite` section, label <mem-ldiv>, just before the
  `// B&dM (9.3)` comment. Marker keys are placeholders MLDKEY/S1KEY/S2KEY/S3KEY.

Blocked (make c CH=15 exits 2 at the `panels` target)
- Every panel of the chain, including mem_leftDiv_eq_step1.lhs, is a red stub:
  "the bead `⊆` is a family and the environment proves neither its naturality nor a refutation";
  "the naturality search for fun a => «⊆» found nothing: state
  `LaxNatural (compFunctor idFunctor E) (compFunctor idFunctor E) (fun a => «⊆»)`".
- Cause: A7_1's context is `[UnguardedPowerLCDA 𝒜]`, where `powerRelator` (needs tabular+unitary)
  does not exist, so `subset_oplaxNatural` (AOP.A5_7_PowerBeads, over powerRelator) cannot apply.
  The same ⊆ bead draws in A9_1 (`[TabularUnitaryUnguardedPowerLCDA 𝒜]`).
- Also: `mem_leftDiv_eq` is `[diag_rewrite]` (diag/StrDiagNames.lean, "`∈\Z` is an APPLICATION of
  `∈\−`"), so the exporter draws `∈\Z` already as `⊆ Λ(Z°)°`: the lhs panel is the rhs picture, and
  step1.rhs `∈\(∈Λ(Z°)°)` gets rewritten to `⊆Λ((∈Λ(Z°)°)°)°`.
- In one lean-chain, `Z` sits at row 2 of step1.lhs and row 4 of step1.rhs (shared-bead height
  error), hence the typ splits the chain after the lhs.
