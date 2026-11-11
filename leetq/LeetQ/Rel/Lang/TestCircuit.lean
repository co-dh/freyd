import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Circuit

/-! The Rel language on AIMA §8.4.2's full adder, read from `programs/circuit.rel.md`, against `Circuit.lean`. -/

namespace LeetQ.Rel.Lang.TestCircuit

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg LeetQ.Rel.Lang.Test LeetQ.Rel.Circuit QLean

def circuit : String := program_file "../../../programs/circuit.rel.md"

def given : Except Err Out := runText circuit

-- row order is not part of a relation, so rows compare sorted
def rows {v : Obj} (f : v.El → List Int64) (R : Rel Bit3 v) : List (List Int64) :=
  (R.toList.map fun ((a, b, c), y) => [a, b, c] ++ f y).mergeSort fun a b => decide (a ≤ b)

#guard given.isOk
#guard (ok given).prints == ["answer = {((0, (1, 1)), 0), ((1, (0, 1)), 0), ((1, (1, 0)), 0)}"]

-- `Circuit.lean`'s first guard: query 6
#guard get (ok given) "answer" Bit3 Bit == some answer
#guard ((get (ok given) "answer" Bit3 Bit).map (rows fun _ => [])) ==
  some ([[0, 1, 1], [1, 0, 1], [1, 1, 0]] : List (List Int64))

-- `Circuit.lean`'s second guard: the adder's truth table, (a, b, c, sum, carry)
#guard get (ok given) "add" Bit3 Bit2 == some adder
#guard ((get (ok given) "add" Bit3 Bit2).map (rows (v := Bit2) fun (s, c) => [s, c])) ==
  some ([[0, 0, 0, 0, 0], [0, 0, 1, 1, 0], [0, 1, 0, 1, 0], [0, 1, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 1],
    [1, 1, 0, 0, 1], [1, 1, 1, 1, 1]] : List (List Int64))

end LeetQ.Rel.Lang.TestCircuit
