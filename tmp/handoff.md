rel-112 handoff (WIP checkpoint at 40 calls)

Done: Alg.lean nubC/nubC_fst, divJoinC, leftDivC, leftDiv := (leftDivC ..).1, rightDivC, rightDiv := .1.
RepDiv.lean divJoinC_fst (compiles). CRelRel.lean rep_leftDivC/rep_rightDivC/CRel.leftDiv/rightDiv (unbuilt).
Failing: RepDiv.lean `have e` in rep_leftDiv: `rw [nubC_fst R]` times out at whnf (kabstract/motive check at default
transparency evaluates need/longCount/Code.gather). Plan: move keep/top/union into a def `divTailC Ub Uc y ycs zc` so
every rewrite of the twins sits in a non-dependent argument and `simp only` does it.
Left: symDiv, transpose, conversion estimate.
