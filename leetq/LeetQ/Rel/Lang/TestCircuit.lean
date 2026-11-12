import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Programs.Circuit

/-! The Rel language on AIMA §8.4.2's full adder, the program `Programs.circuit`. -/

namespace LeetQ.Rel.Lang.TestCircuit

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg LeetQ.Rel.Lang.Test QLean

def given : Except Err Out := runProgram Programs.circuit

-- row order is not part of a relation, so rows compare sorted; the program's array `a b c` reads as the row
-- `[a, b, c]`
def sorted (xs : List (List Int64)) : List (List Int64) := xs.mergeSort fun a b => decide (a ≤ b)
def rowsA {v : Obj} (f : v.El → List Int64) (R : Rel (.arr .long) v) : List (List Int64) :=
  sorted (R.toList.map fun (xs, y) => xs ++ f y)

#guard given.isOk
-- the program's own `check answer = …` holds and prints nothing; `answer` printed here is the same literal
#guard (ok given).prints == []
#guard (ok (runExt Programs.circuit "print answer\n")).prints ==
  ["answer = {(0 1 1, 0), (1 0 1, 0), (1 1 0, 0)}"]

-- query 6
#guard ((get (ok given) "answer" (.arr .long) .long).map (rowsA fun _ => [])) ==
  some ([[0, 1, 1], [1, 0, 1], [1, 1, 0]] : List (List Int64))

-- the adder's truth table, (a, b, c, sum, carry)
#guard ((get (ok given) "add" (.arr .long) (.prod .long .long)).map
    (rowsA (v := .prod .long .long) fun (s, c) => [s, c])) ==
  some ([[0, 0, 0, 0, 0], [0, 0, 1, 1, 0], [0, 1, 0, 1, 0], [0, 1, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 1],
    [1, 1, 0, 0, 1], [1, 1, 1, 1, 1]] : List (List Int64))

end LeetQ.Rel.Lang.TestCircuit
