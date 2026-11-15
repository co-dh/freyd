import LeetQ.Rel.Programs.SudokuAC
import LeetQ.Rel.Programs.SudokuPC
import LeetQ.Rel.Programs.SudokuPC9
import LeetQ.Rel.Programs.Blocks
import LeetQ.Rel.Programs.Chess
import LeetQ.Rel.Programs.Circuit
import LeetQ.Rel.Programs.Detab
import LeetQ.Rel.Programs.Edit
import LeetQ.Rel.Programs.JobShop
import LeetQ.Rel.Programs.Knapsack
import LeetQ.Rel.Programs.Mss
import LeetQ.Rel.Programs.Selsort
import LeetQ.Rel.Programs.Wumpus

open Lean Elab Command LeetQ.Rel.Lang

-- spike evidence (rel-mod-4), not a test kept in the tree

-- F1: `.` is a name character, and which program defines a name holding `.`
#eval Parse.isSym '.'
run_cmd do
  let env ← getEnv
  let ps := env.constants.fold (fun acc n ci => if ci.type == mkConst ``Program then n :: acc else acc) []
  let mut hits : List (Name × String) := []
  for n in ps do
    let p ← unsafe evalConstCheck Program ``Program n
    for d in p do
      if let .defn _ x .. := d then if x.contains '.' then hits := (n, x) :: hits
  logInfo m!"F1: {ps.length} program constants; definitions named with '.': {hits}"

-- the call: which of each program's constants reach `csp.AC3` and `Gen.nuAC`
run_cmd do
  let env ← getEnv
  for p in [`LeetQ.Rel.Programs.csp, `LeetQ.Rel.Programs.sudokuac, `LeetQ.Rel.Programs.sudokupc,
      `LeetQ.Rel.Programs.sudokupc9] do
    let cs := env.constants.fold (fun acc n _ => if p.isPrefixOf n && n != p then n :: acc else acc) []
    let uses (c : Name) := cs.filter fun n => match env.find? n with
      | some (.defnInfo d) => d.value.getUsedConstants.contains c
      | _ => false
    logInfo m!"{p}: uses csp.AC3: {uses `LeetQ.Rel.Programs.csp.AC3}; uses Gen.nuAC: {uses ``Gen.nuAC}"

namespace LeetQ.Rel.Programs

-- F3: an object variable the body does not name, `𝟙 : β ⟶ β` from the declared type alone
rel_program f3 after prelude where
    s₀(g : α ⟶ β) : α ⟶ β ≜ g°\𝟙

rel_program f3use after f3 where
    obj C = 0…1
    obj D = 1…3
    g : C ⟶ D ≜ {(0,2)}
    s : C ⟶ D ≜ s₀(g)
    check s = {(0,2),(1,1),(1,2),(1,3)}

#guard f3use.ok
#eval (`LeetQ.Rel.Programs.f3.s₀ : Name)
run_cmd logInfo m!"F3: f3.s₀ elaborated once: {(← getEnv).contains `LeetQ.Rel.Programs.f3.s₀}"

end LeetQ.Rel.Programs
