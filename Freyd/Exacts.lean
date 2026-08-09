/-
  The `exacts` tactic — reimplemented here because this repo is STRICTLY MATHLIB-FREE (and
  Batteries-free), so we cannot pull it in as a dependency.  It is a tiny convenience tactic:
  `exacts [e₁, …, eₙ]` closes the first `n` goals with `e₁, …, eₙ` respectively (like running
  `exact e₁`, then `exact e₂`, … each on the next remaining goal).

  Implemented against Lean 4 core's own metaprogramming API (`import Lean`), which ships with the
  toolchain — this adds NO external package (no `require`, no lake-manifest change), so the
  self-contained, mathlib-free build is preserved.
-/
module

public import Lean

open Lean Elab Tactic in
/-- `exacts [e₁, …, eₙ]` closes the first `n` goals with `e₁, …, eₙ` respectively. -/
elab "exacts" "[" hs:term,* "]" : tactic => do
  for h in hs.getElems do
    evalTactic (← `(tactic| exact $h))
