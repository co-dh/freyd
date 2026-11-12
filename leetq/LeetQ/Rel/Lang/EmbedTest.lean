import LeetQ.Rel.Lang.Embed
import LeetQ.Rel.Programs.Prelude
/-! The Rel language written inside Lean (`Embed`): the grammar's closedness, a Lean term in a body is a parse
    error. The programs written with it are `LeetQ.Rel.Programs`, run by the `Test*` modules. -/

namespace LeetQ.Rel.Lang.EmbedTest

open Lean

/-! Closedness: a Lean term in a body is a parse error of the grammar, never a term elaborated. -/

elab "#rel_parse " s:str : command => do
  match Parser.runParserCategory (← getEnv) `relStmt s.getString with
  | .ok t => logInfo m!"parsed {t}"
  | .error e => logInfo e

/-- info: parsed f:A⟶A≜R∩∼S° -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R ∩ ∼S°"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ fun x => x"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ let x := R; x"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ do R"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ if R then S else T"
/-- info: <input>:1:14: expected ')' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ (R, S)"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ 1 + 1"
/-- info: <input>:1:15: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R (1 + 1)"
/-- info: <input>:1:14: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R(fun x => x)"
/-- info: <input>:1:22: expected '≜' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R where x := 1"

-- Lean gives every category the antiquotation `$x`, `$(…)` at any quotation depth, so these parse; reading the
-- program refuses them
/-- info: parsed f:A⟶A≜$x -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ $x"
/-- info: parsed f:A⟶A≜$(fun x => x) -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ $(fun x => x)"
/-- error: line 47, col 19: `$` is no term of the Rel language: an antiquotation has no place in a program -/
#guard_msgs in
rel_program antiquot after Programs.prelude where
    f : 1 ⟶ 1 ≜ 𝟙 $(fun x => x)

end LeetQ.Rel.Lang.EmbedTest
