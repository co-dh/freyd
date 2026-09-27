Handoff

Done (commits 6efde64, 9b8c771 on worktree-agent-af2582376f0111bfb):
- lean-chain (circuit: false): a reason under its panel when it fits the panel width, else a letter
  (a, b, ... per row) under the panel and the lettered reasons listed under the row. Any-character
  raw breaking removed.
- Hints shortened in every lean-chain of ch 10, 11, 13, 14, 15, 16; the 11.6.2c chain has one per step.
- dpanel: a unit mark on the leftmost lane writes its label west, unless its lane's own name is
  written there (then it stays east; otherwise the name drops onto the next lane's name, labelfit 'EF').
- StringDiagram.lean: `canon` renames each free variable to its binder name (macro scopes erased,
  numbered among namesakes); `Row.ctx` holds canon Exprs, `Row.ident` the canon factor; `drawnAs`
  compares `ident`, not printed key/obj.
- Gates: lake build Freyd AOP diag, make cite, make c CH=10,11,13,14,15,16 all exit 0.

Known effect: the ch14 chain thinning_paths_alg_est (steps Λ_comp_est_comp_singletonMap_le_thinRel.lhs,
thinning_paths_alg.lhs) no longer aligns its shared beads: the two declarations name their binders differently.
