/-
  Label checks that need the note's own printing rules in scope, run on every `lake build diag`.
  Apart from `DiagExportTest` because `StrDiagNames`' notations (`*`, `−`) re-read that file's
  float literals.
-/
import diag.tool.FormulaRender
import diag.StrDiagNames

namespace Freyd.LabelTest

/-- The statement's formula, as `--formula` writes it. -/
def formula (n : Lean.Name) : Lean.Meta.MetaM String :=
  return String.join ((← Freyd.FormulaRender.render n none [] []).map Freyd.StrDiag.Lbl.flat).toList

-- `R` sits inside `θ`'s second operand; replacing the operands one at a time rewrote it there first,
-- and that operand then printed raw: `θ(P ∪ Q,Q ≫ R − P − Q)`.
#eval show Lean.Meta.MetaM Unit from do
  let s ← formula ``Freyd.Alg.theta_step
  unless s == "θ(P,Q)=θ(P ∪ Q,QR−P−Q)" do throwError "an operand of `θ` printed raw: {s}"

end Freyd.LabelTest
