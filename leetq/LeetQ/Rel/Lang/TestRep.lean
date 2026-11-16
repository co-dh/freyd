import LeetQ.Rel.Lang.RelRep
import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Lang.EmbedTest
import LeetQ.Rel.Lang.ModuleTest
import LeetQ.Rel.Lang.TestChess
import LeetQ.Rel.Lang.TestCircuit
import LeetQ.Rel.Lang.TestDetab
import LeetQ.Rel.Lang.TestEdit
import LeetQ.Rel.Lang.TestKnapsack
import LeetQ.Rel.Lang.TestMss
import LeetQ.Rel.Lang.TestNative
import LeetQ.Rel.Lang.TestRefold
import LeetQ.Rel.Lang.TestSelsort
import LeetQ.Rel.Lang.TestWumpus
import LeetQ.Rel.Programs.JobShop
import LeetQ.Rel.Programs.Party
import LeetQ.Rel.Programs.Quicksort
import LeetQ.Rel.Programs.SudokuPC
import LeetQ.Rel.Programs.SudokuPC9

/-! The representation theorems `n.rep_x` (`rel_rep`) of every program the modules above define, in the order
    they were defined: the registry lists them, so a program is checked here as soon as its module is imported. -/

open Lean Elab Command in
run_cmd do
  for (n, _) in (LeetQ.Rel.Lang.Expand.relRegistry.getState (← getEnv)).progs do
    liftTermElabM (LeetQ.Rel.Lang.Expand.rep n)
