import LeetQ.Rel.Lang.Test

/-! The Rel language on B&dM §6.6 selection sort, read from the literate `programs/selsort.rel.md`: the specification
    `perm ordered(≤)` and the derived program `X`, each printed on four arrays, against `List.mergeSort`. -/

namespace LeetQ.Rel.Lang.TestSelsort

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test

def selsort : String := program_file "../../../programs/selsort.rel.md"

/-- The program's inputs, as Lean lists. -/
def inputs : List (String × List Nat) := [("x", [3, 1, 2]), ("y", [2, 1, 2]), ("z", [5, 4, 3, 2, 1]), ("e", [])]

/-- An array `1 ⟶ [N]` as the interpreter prints it. -/
def shown (l : List Nat) : String := "{(∗, " ++ arrText false (l.map toString) ++ ")}"

def sorted (l : List Nat) : List Nat := l.mergeSort fun a b => decide (a ≤ b)

-- the inputs are the lists above: the program printed with one `print` per input appended
#guard (ok (runText (selsort ++ String.join (inputs.map fun (n, _) => s!"print {n}\n")))).prints.drop 8 ==
  inputs.map fun (n, l) => s!"{n} = {shown l}"

-- both `check`s hold (a failed one is an error), and the specification and the program print the sorted input
#guard (runText selsort).isOk
#guard (ok (runText selsort)).prints ==
  inputs.map (fun (n, l) => s!"{n} perm ordered(≤) = {shown (sorted l)}") ++
  inputs.map (fun (n, l) => s!"{n} X = {shown (sorted l)}")

end LeetQ.Rel.Lang.TestSelsort
