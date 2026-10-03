/-
  Label checks that need the note's own printing rules in scope, run on every `lake build diag`.
  Apart from `DiagExportTest` because `StrDiagNames`' notations (`*`, `−`) re-read that file's
  float literals.
-/
import diag.tool.FormulaRender
import diag.StrDiagNames
import AOP.A9_1

namespace Freyd.LabelTest

/-- The statement's formula: SPACED as `--formula` writes it, COMPACT as a panel label sets it. -/
def formula (n : Lean.Name) (sp : Bool := true) : Lean.Meta.MetaM String :=
  return String.join ((← Freyd.FormulaRender.render sp n none [] []).map Freyd.StrDiag.Lbl.flat).toList

-- `R` sits inside `θ`'s second operand; replacing the operands one at a time rewrote it there first,
-- and that operand then printed raw: `θ(P ∪ Q,Q ≫ R − P − Q)`.
#eval show Lean.Meta.MetaM Unit from do
  let s ← formula ``Freyd.Alg.theta_step false
  unless s == "θ(P,Q)=θ(P ∪ Q,(QR)−P−Q)" do throwError "an operand of `θ` printed raw: {s}"

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
#guard Freyd.StrDiag.juxt "≤" "cost°" == "≤cost°"
#guard Freyd.StrDiag.juxt "S" "(S\\T)" == "S(S\\T)"
#guard Freyd.StrDiag.juxt "F(R)" "h" == "F(R)h"

-- …and through a whole statement: `h cost` keeps its space on both sides of `=`, while the
-- one-letter `k` still closes up against `F(cost)` and against `≤`.
/-- info: h cost=F(cost)k ⟹ F(cost)k≤=h cost≤ -/
#guard_msgs in
#eval show Lean.Meta.MetaM Unit from do
  Lean.logInfo (← formula ``Freyd.Alg.monoAlg_of_cost_step4 false)

-- WE ONLY REMOVE SPACE WHEN SPACE ARE LIMITED: the same declaration SPACED, as a formula set as text
-- prints it — every two juxtaposed factors apart, every relation sign set off — and the two modes
-- differ in spaces ALONE.
#guard Freyd.StrDiag.juxt "S" "R" true == "S R"
#guard Freyd.StrDiag.juxt "F(R)" "h" true == "F(R) h"
#guard Freyd.StrDiag.juxt "k" "≤" true == "k ≤"
#guard Freyd.StrDiag.spaced "=" true == " = " && Freyd.StrDiag.spaced "=" == "="
/-- info: h cost = F(cost) k ⟹ F(cost) k ≤ = h cost ≤ -/
#guard_msgs in
#eval show Lean.Meta.MetaM Unit from do
  let s ← formula ``Freyd.Alg.monoAlg_of_cost_step4
  unless s.replace " " "" == (← formula ``Freyd.Alg.monoAlg_of_cost_step4 false).replace " " "" do
    throwError "the two modes differ in more than spaces: {s}"
  Lean.logInfo s

-- AN APPLICATION'S BRACKETS, A ONE-LETTER FUNCTOR ON AN OBJECT AND A POSTFIX ARE NO SEPARATOR: `F(R)`
-- (here `F(cost)`), `FA` and `op°` are one spelling in both modes.
#eval show Lean.Meta.MetaM Unit from do
  let both (e : Lean.Expr) (want : String) : Lean.Meta.MetaM Unit := do
    let c ← Freyd.StrDiag.label e
    let s ← Freyd.StrDiag.withSpaced true (Freyd.StrDiag.label e)
    unless c == want && s == want do throwError "`{want}` prints `{c}` compact and `{s}` spaced"
  let ci ← Lean.getConstInfo ``Freyd.Alg.monoAlg_of_cost_step4
  Lean.Meta.forallTelescope ci.type fun xs body => do
    -- `F.map cost`, the first factor of the statement's left side
    let some (_, l, _) := Freyd.StrDiag.split body | throwError "monoAlg_of_cost_step4 states no relation"
    let some f := (Freyd.StrDiag.factors l)[0]? | throwError "its left side has no factor"
    both f "F(cost)"
    -- `F.obj A`, the source of `h`
    let some h ← xs.findM? fun x => return (← x.fvarId!.getUserName) == `h | throwError "no binder `h`"
    let ends := (← Lean.Meta.inferType h).getAppArgs
    both ends[ends.size - 2]! "FA"
  let ci ← Lean.getConstInfo `Freyd.Alg.RelSet.Digits.op_recip_iff
  Lean.Meta.forallTelescope ci.type fun _ body =>
    -- `(op°) m p` with its two points taken off
    both (body.getArg! 0).appFn!.appFn! "op°"

end Freyd.LabelTest
