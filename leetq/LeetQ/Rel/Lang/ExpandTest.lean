import LeetQ.Rel.Lang.Eval
import LeetQ.Rel.Programs.Blocks
import LeetQ.Rel.Programs.Chess
import LeetQ.Rel.Programs.Circuit
import LeetQ.Rel.Programs.Detab
import LeetQ.Rel.Programs.Edit
import LeetQ.Rel.Programs.JobShop
import LeetQ.Rel.Programs.Knapsack
import LeetQ.Rel.Programs.Mss
import LeetQ.Rel.Programs.Selsort
import LeetQ.Rel.Programs.SudokuAC
import LeetQ.Rel.Programs.SudokuPC
import LeetQ.Rel.Programs.SudokuPC9
import LeetQ.Rel.Programs.Wumpus

/-! The expander against the interpreter, over every `rel_program`: each closed definition the interpreter
    prints (`Out.vals`) must have its expansion `n.rel.x`, printing the same text (`showRel`), and the
    program's ok bit must be the `&&` of the expansions' ok bits. -/

namespace LeetQ.Rel.Lang.ExpandTest

open LeetQ.Rel LeetQ.Rel.Lang

/-- Every difference between `runProgram prog` and the expansion `gs` (the prelude's `pre` read after it). -/
def diffs (prog : Program) (gs pre : List (String × Gen.Gv)) : List String :=
  match runProgram prog with
  | .error e => [s!"runProgram: {e}"]
  | .ok out =>
    let all := gs ++ pre
    -- the obligations are the interpreter's values: each needs an expansion that prints the same
    let vs := out.vals.filterMap fun (x, ⟨A, B, R⟩, s, t) => match all.find? (·.1 == x) with
      | none => some s!"{x}: no expansion"
      | some (_, ⟨A', B', c⟩) =>
        if h : A' = A ∧ B' = B then
          let a := showRel out.objs s t R; let b := showRel out.objs s t (h.1 ▸ h.2 ▸ c.rel)
          if a != b then some s!"{x}: interpreter {a}, expansion {b}" else none
        else some s!"{x}: the expansion's objects differ"
    let ok := (all.filter fun (x, _) => out.vals.any (·.1 == x)).all fun (_, ⟨_, _, c⟩) => c.ok
    vs ++ (if ok != out.ok then [s!"ok bit: interpreter {out.ok}, expansion {ok}"] else [])

/-- Fails naming every difference. -/
def check (n : String) (d : List String) : IO Unit :=
  unless d.isEmpty do throw (IO.userError s!"{n}: {d.length} differences\n" ++ "\n".intercalate d)

open Programs in
#eval check "prelude" (diffs [] [] prelude.expanded)
open Programs in
#eval check "blocks" (diffs blocks blocks.expanded prelude.expanded)
open Programs in
#eval check "chess" (diffs chess chess.expanded prelude.expanded)
open Programs in
#eval check "circuit" (diffs circuit circuit.expanded prelude.expanded)
open Programs in
#eval check "detab" (diffs detab detab.expanded prelude.expanded)
open Programs in
#eval check "edit" (diffs edit edit.expanded prelude.expanded)
open Programs in
#eval check "jobshop" (diffs jobshop jobshop.expanded prelude.expanded)
open Programs in
#eval check "knapsack" (diffs knapsack knapsack.expanded prelude.expanded)
open Programs in
#eval check "mss" (diffs mss mss.expanded prelude.expanded)
open Programs in
#eval check "selsort" (diffs selsort selsort.expanded prelude.expanded)
open Programs in
#eval check "sudokuac" (diffs sudokuac sudokuac.expanded prelude.expanded)
open Programs in
#eval check "sudokupc" (diffs sudokupc sudokupc.expanded prelude.expanded)
open Programs in
#eval check "sudokupc9" (diffs sudokupc9 sudokupc9.expanded prelude.expanded)
open Programs in
#eval check "wumpus" (diffs wumpus wumpus.expanded prelude.expanded)

end LeetQ.Rel.Lang.ExpandTest
