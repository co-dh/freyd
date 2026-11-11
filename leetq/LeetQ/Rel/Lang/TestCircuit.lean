import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Circuit

/-! The Rel language on AIMA §8.4.2's full adder, read from `programs/circuit.rel.md`, against `Circuit.lean`. -/

namespace LeetQ.Rel.Lang.TestCircuit

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg LeetQ.Rel.Lang.Test LeetQ.Rel.Circuit QLean

def circuit : String := program_file "../../../programs/circuit.rel.md"

def given : Except Err Out := runText circuit

-- row order is not part of a relation, so rows compare sorted; `Circuit.lean`'s input `(a, (b, c))` and the
-- program's array `a b c` both read as the row `[a, b, c]`
def sorted (xs : List (List Int64)) : List (List Int64) := xs.mergeSort fun a b => decide (a ≤ b)
def rows {v : Obj} (f : v.El → List Int64) (R : Rel Bit3 v) : List (List Int64) :=
  sorted (R.toList.map fun ((a, b, c), y) => [a, b, c] ++ f y)
def rowsA {v : Obj} (f : v.El → List Int64) (R : Rel (.arr Bit) v) : List (List Int64) :=
  sorted (R.toList.map fun (xs, y) => xs ++ f y)

#guard given.isOk
-- the file's own `check answer = …` holds and prints nothing; `answer` printed here is the same literal
#guard (ok given).prints == []
#guard (ok (runText (circuit ++ "print answer\n"))).prints ==
  ["answer = {(0 1 1, 0), (1 0 1, 0), (1 1 0, 0)}"]

-- `Circuit.lean`'s first guard: query 6
#guard ((get (ok given) "answer" (.arr Bit) Bit).map (rowsA fun _ => [])) == some (rows (fun _ => []) answer)
#guard ((get (ok given) "answer" (.arr Bit) Bit).map (rowsA fun _ => [])) ==
  some ([[0, 1, 1], [1, 0, 1], [1, 1, 0]] : List (List Int64))

-- `Circuit.lean`'s second guard: the adder's truth table, (a, b, c, sum, carry)
#guard ((get (ok given) "add" (.arr Bit) Bit2).map (rowsA (v := Bit2) fun (s, c) => [s, c])) ==
  some (rows (v := Bit2) (fun (s, c) => [s, c]) adder)
#guard ((get (ok given) "add" (.arr Bit) Bit2).map (rowsA (v := Bit2) fun (s, c) => [s, c])) ==
  some ([[0, 0, 0, 0, 0], [0, 0, 1, 1, 0], [0, 1, 0, 1, 0], [0, 1, 1, 0, 1], [1, 0, 0, 1, 0], [1, 0, 1, 0, 1],
    [1, 1, 0, 0, 1], [1, 1, 1, 1, 1]] : List (List Int64))

end LeetQ.Rel.Lang.TestCircuit
