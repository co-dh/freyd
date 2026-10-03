Handoff (checkpoint at 40 calls), branch worktree-agent-ad2b67cfe725189cc, on top of 8035b38.

Done (WIP commit):
- Task 1: diag/tool/Label.lean `labelTreeCore`'s `bin`: new `side` brackets an operand whose label differs
  at Prec.juxt vs juxt+1 (a composite). Not yet verified by an export run.
- Task 4: pathF + pathF_map_id moved from AOP/A8_2_Exec.lean into AOP/A8_2.lean before pathSplit;
  pathSplit := pathF.map (𝟙 (dE V)) (∋ (dCL V V)) ≫ alphaR; pathSplit_apply carries the pointwise match.
  `lake build AOP.A8_2_Exec diag-export` green. unexpander pathSplit -> S in diag/StrDiagNames.lean.
- Note diag/aop/08-thinning.typ path-defn: α line and S line switched to #leanf (alphaR, pathSplit).

Left: task 2 (cost fold), 5 (frac theorems), 6 (cpr in label walk), marker fix (pathAlg -> pathSplit key),
gates (make c NOTE=aop CH=n, make cite CH=5,8), full lake build, diff-crop k3/k4.
