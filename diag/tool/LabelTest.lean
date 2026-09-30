/-
  Label checks that need the note's own printing rules in scope, run on every `lake build diag`.
  Apart from `DiagExportTest` because `StrDiagNames`' notations (`*`, `−`) re-read that file's
  float literals.
-/
import diag.tool.FormulaRender
import diag.StrDiagNames
import AOP.A9_1

namespace Freyd.LabelTest

/-- The statement's formula, as `--formula` writes it. -/
def formula (n : Lean.Name) : Lean.Meta.MetaM String :=
  return String.join ((← Freyd.FormulaRender.render n none [] []).map Freyd.StrDiag.Lbl.flat).toList

-- `R` sits inside `θ`'s second operand; replacing the operands one at a time rewrote it there first,
-- and that operand then printed raw: `θ(P ∪ Q,Q ≫ R − P − Q)`.
#eval show Lean.Meta.MetaM Unit from do
  let s ← formula ``Freyd.Alg.theta_step
  unless s == "θ(P,Q)=θ(P ∪ Q,QR−P−Q)" do throwError "an operand of `θ` printed raw: {s}"

-- A RELATION APPLIED TO ITS POINTS keeps them, whatever operator builds the relation: the `°`
-- clause matched `(op°) m p` at every arity and printed `op°`, dropping `m` and `p`.
#eval show Lean.Meta.MetaM Unit from do
  let ci ← Lean.getConstInfo `Freyd.Alg.RelSet.Digits.op_recip_iff
  Lean.Meta.forallTelescope ci.type fun _ body => do
    let s ← Freyd.StrDiag.label (body.getArg! 0)
    unless s == "op°(m,p)" do throwError "op_recip_iff's left side prints {s}, not op°(m,p)"

-- JUXTAPOSITION CLOSES UP ONLY BETWEEN TWO ONE-LETTER NAMES: `h` then `cost` printed `hcost`, one
-- name, because the left factor alone was asked whether it was one letter.
#guard Freyd.StrDiag.juxt "h" "cost" == "h cost"
#guard Freyd.StrDiag.juxt "S" "est(R)" == "S est(R)"
#guard Freyd.StrDiag.juxt "cost" "k" == "cost k"
#guard Freyd.StrDiag.juxt "S" "R" == "SR"
#guard Freyd.StrDiag.juxt "R" "R°" == "RR°"
#guard Freyd.StrDiag.juxt "h" "F'(cost)" == "hF'(cost)"
#guard Freyd.StrDiag.juxt "k" "≤" == "k≤"
#guard Freyd.StrDiag.juxt "S" "(S\\T)" == "S(S\\T)"
#guard Freyd.StrDiag.juxt "F(R)" "h" == "F(R)h"

-- …and through a whole statement: `h cost` keeps its space on both sides of `=`, while the
-- one-letter `k` still closes up against `F(cost)` and against `≤`.
/-- info: h cost=F(cost)k ⟹ F(cost)k≤=h cost≤ -/
#guard_msgs in
#eval show Lean.Meta.MetaM Unit from do
  Lean.logInfo (← formula ``Freyd.Alg.monoAlg_of_cost_step4)

end Freyd.LabelTest
