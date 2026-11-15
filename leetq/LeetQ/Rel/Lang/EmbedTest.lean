import LeetQ.Run.Lang.Embed
import LeetQ.Rel.Programs.Prelude
/-! The Rel language written inside Lean (`Embed`): the grammar's closedness, a Lean term in a body is an
    error (a keyword in it is a Rel name). The programs written with it are `LeetQ.Rel.Programs`, run by the
    `Test*` modules. -/

namespace LeetQ.Rel.Lang.EmbedTest

open Lean

/-! Closedness: a Lean term in a body is an error, never a term elaborated; a keyword in it is a Rel name. -/

elab "#rel_parse " s:str : command => do
  match Parser.runParserCategory (← getEnv) `relStmt s.getString with
  | .ok t => logInfo m!"parsed {t}"
  | .error e => logInfo e

/-- info: parsed f:A⟶A≜R∩∼S° -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R ∩ ∼S°"
/-- info: <input>:1:18: expected end of input -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ fun x => x"
/-- info: <input>:1:18: expected end of input -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ let x := R; x"
/-- info: parsed f:A⟶A≜do R -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ do R"
/-- info: parsed f:A⟶A≜if R then S else T -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ if R then S else T"
/-- info: <input>:1:14: expected ')' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ (R, S)"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ 1 + 1"
/-- info: <input>:1:15: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R (1 + 1)"
/-- info: <input>:1:20: expected ')' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R(fun x => x)"
/-- info: <input>:1:22: expected '≜' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R where x := 1"

-- Lean gives every category the antiquotation `$x`, `$(…)` at any quotation depth, so these parse; reading the
-- program refuses them. Behind `∪`, not juxtaposed: after a juxtaposed antiquotation `sameLine` lets the next line
-- in, so the following command would be read into the program
/-- info: parsed f:A⟶A≜$x -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ $x"
/-- info: parsed f:A⟶A≜$(fun x => x) -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ $(fun x => x)"
/-- error: line 50, col 21: `$` is no term of the Rel language: an antiquotation has no place in a program -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude in
rel_program antiquot where
    f : 1 ⟶ 1 ≜ 𝟙 ∪ $(fun x => x)

/-! `theorem n : e = f := calc` (`doc/rel-mss-proof-design.md` §3, §8): each step `_ = x := n` cites a theorem, `≜ n`
    a definition; `on A` evaluates each step as a `check`. -/

open LeetQ.Rel.Programs.prelude in
rel_program thm where
    obj N = 0…3
    obj K = {a,b}
    two : N ⟶ N ≜ {(1,2),(2,2)}
    up : N ⟶ N ≜ {(1,2)}
    x : K ⟶ N ≜ {(a,1),(b,2)}
    theorem unit : two 𝟙 = two
    theorem good on x : two 𝟙 = two := calc
      _ = {(1,2),(2,2)} := ≜ two
      _ = two := ≜ two
    theorem le on x : up ⊑ two := calc
      _ ⊑ two 𝟙 := unit
      _ = two := unit

#guard thm.ok
-- the chains stay in the program's constant, for `rel_aop` to read back
#guard (thm.filterMap fun | .«theorem» _ n _ _ _ _ _ ss => some (n, ss.length) | _ => none) ==
  [("unit", 0), ("good", 2), ("le", 2)]

/-- error: line 80, col 7: theorem `t`: this step x is LeetQ.Rel.Lang.EmbedTest.thm.K ⟶ LeetQ.Rel.Lang.EmbedTest.thm.N, the statement's two is LeetQ.Rel.Lang.EmbedTest.thm.N ⟶ LeetQ.Rel.Lang.EmbedTest.thm.N -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude thm in
rel_program thmType where
    theorem t : two = two := calc
      _ = x := unit
      _ = two := unit

/-- error: line 88, col 11: `unit` is a theorem, not a relation -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude thm in
rel_program thmAsRel where
    theorem t : two = two := calc
      _ = unit := unit

/-- error: line 95, col 18: `two` is a definition; write `≜ two` -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude thm in
rel_program relAsThm where
    theorem t : two = two := calc
      _ = two := two

/-- error: line 102, col 20: `unit` is a theorem, not a definition -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude thm in
rel_program thmAsDef where
    theorem t : two = two := calc
      _ = two := ≜ unit

/-- error: line 109, col 18: unknown theorem 'nope' -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude thm in
rel_program thmUnknown where
    theorem t : two = two := calc
      _ = two := nope

/-- error: line 116, col 7: the chain of `t` ends at two 𝟙, not at its right side two -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude thm in
rel_program thmEnds where
    theorem t : two 𝟙 = two := calc
      _ = two 𝟙 := unit

/-- error: line 123, col 7: `t` states `=`: a step `⊑` proves only `⊑` -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude thm in
rel_program thmLe where
    theorem t : up = two := calc
      _ ⊑ two := unit

open LeetQ.Rel.Programs.prelude thm in
rel_program thmData where
    theorem t on x : up = two := calc
      _ = two := unit

#guard !thmData.ok
/-- info: ["line 128, col 7: check failed: x up = {(a, 2)}, x two = {(a, 2), (b, 2)}"] -/
#guard_msgs in
#eval thmData.failures.map toString

end LeetQ.Rel.Lang.EmbedTest
