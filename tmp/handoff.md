# Rel language handoff (branch rel-lang-impl)

Done and pushed: Syntax.lean, Parse.lean (1217e9e), Elab.lean (0aee040), Eval.lean (44732a9).
In the tree, not committed yet: Elab fixes (literal sides resolved from declared objects; `build` no longer
builds a sub-term twice), Eval (`OTy.poly`: a parameterless definition with open objects is elaborated at each
use), programs/blocks.rel, Test.lean, Main.lean, lakefile `lean_exe rel`.

blocks.rel = doc §g with two text fixes: `s₀ ≜ ran(Λ(⊤(X,X)⟨𝟙,S₀⟩))` (⊤'s source undetermined) and
`M ≜ ∼(R(S)°⊤ ∪ (⊤R(S)))` (by §c's flat left fold the doc's line reads `((R°⊤) ∪ ⊤)R(S)`, wrong moves).
With them `print plan` = {(0,(C,C)),(1,(B,C)),(2,(A,B))}.

Left: Test guards green; `lake build rel`; BlocksRel cost fix (bind ν, (Qt)° once outside the step lambda);
doc fixes (§a/§g succ row, §d cost paragraph and 0…6 table, the two §g lines, grammar additions); report.
Lake does not track include_str: change Test.lean's text to force a re-run.
