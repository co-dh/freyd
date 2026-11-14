rel-82a handoff (WIP at call 40)

Done:
- Code.lean `Obj.sortBy` `.arr`/`.sum`: `gather 8 p ((Obj.codes (.arr b) #v[⟨_, c⟩])[0].gather p).grade`; `codesWF` notation deleted.
- SortSpec.lean: new `grade_gather_perm` (builds); `sortBy_perm` restated with `A.CodesFit #v[⟨n, c⟩]` and
  `∀ t ∈ ids p, t < n.toNat`.
- Signatures rerouted: RepLambda (4), RepE (2), RepEst (1), RepPower (6), RepSort bundle, RepPerm `tauOK` gains
  the CodesFit conjunct before h63; `rep_snoc` drops hW.

Left:
- sortBy_perm fails: `SortSpec.lean:124:0: (deterministic) timeout at whnf, maximum number of heartbeats (200000)`
  — suspect the `.prod` case `simpa using hf.2.1` or the structural recursion; testing in leetq/Scratch82.lean.
- RepMerge: drop `(hW : codesWF)` at merge_round_rep (~457), rep_mergeOn (~620), rep_merge (~687) and `hW` args
  at ~503, 509, 675, 693.
- Build LeetQ; check Programs/AlgTest guards.
