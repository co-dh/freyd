import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Programs.Selsort

/-! The Rel language on B&dM §6.6 selection sort, the program `Programs.selsort`: the specification
    `perm ordered(≤)` and the derived program `X`, each checked on four arrays in the program, and against
    `List.mergeSort`. -/

namespace LeetQ.Rel.Lang.TestSelsort

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test

/-- The program's inputs, as Lean lists. -/
def inputs : List (String × List Nat) := [("x", [3, 1, 2]), ("y", [2, 1, 2]), ("z", [5, 4, 3, 2, 1]), ("e", [])]

/-- An array `1 ⟶ [N]` as the printer prints it. -/
def shown (l : List Nat) : String := "{(∗, " ++ arrText false (l.map toString) ++ ")}"

def sorted (l : List Nat) : List Nat := l.mergeSort fun a b => decide (a ≤ b)

rel_program given after Programs.selsort where
    print x
    print y
    print z
    print e

-- the inputs are the lists above: the program printed with one `print` per input appended
#guard given.prints == inputs.map fun (n, l) => s!"{n} = {shown l}"

rel_program sorts after Programs.selsort where
    print x perm ordered(≤)
    print y perm ordered(≤)
    print z perm ordered(≤)
    print e perm ordered(≤)
    print x X
    print y X
    print z X
    print e X

-- every `check` of the program holds (a failed one is a failure) and it prints nothing; printed here, the
-- specification and the program give the input sorted by `List.mergeSort`
#guard Programs.selsort.ok
#guard Programs.selsort.prints == []
#guard sorts.prints ==
  inputs.map (fun (n, l) => s!"{n} perm ordered(≤) = {shown (sorted l)}") ++
  inputs.map (fun (n, l) => s!"{n} X = {shown (sorted l)}")

end LeetQ.Rel.Lang.TestSelsort
