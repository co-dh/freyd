import LeetQ.Rel.Algebra

/-! AIMA §8.4.2's one-bit full adder C1 as one relation `F : Bit³ ⟶ Bit²` built by composition, and query 6 as
    the preimage `F p°` of the point `p = (0,1)`. A bit is the long 0 or 1; `Bitⁿ` is a product side, stored
    as `n` long columns, so `πᵢ` selects a column and `⟨R,S⟩` is `pair`. -/

namespace LeetQ.Rel.Circuit

open Alg QLean

abbrev Bit : Obj := .long
abbrev Bit2 : Obj := .prod Bit Bit
abbrev Bit3 : Obj := .prod Bit Bit2

def bits : List Int64 := [0, 1]
/-- `Bitⁿ`'s elements, first component major. -/
def cube : Nat → List (List Int64)
  | 0 => [[]]
  | n + 1 => bits.flatMap fun b => (cube n).map (b :: ·)

/-- `Bit³`'s eight elements as its three columns. -/
def U : Except String (Vals Bit3 8) := do
  let c (i : Nat) := col 8 ((cube 3).map (·.getD i 0))
  pure (← c 0, ← c 1, ← c 2)

/-- `πᵢ : Bit³ ⟶ Bit` on `U`: key `U`, val its `i`-th column — a column selected, nothing computed. -/
def π₁ : Except String (Rel Bit3 Bit) := do let u ← U; pure ⟨8, u, u.1⟩
def π₂ : Except String (Rel Bit3 Bit) := do let u ← U; pure ⟨8, u, u.2.1⟩
def π₃ : Except String (Rel Bit3 Bit) := do let u ← U; pure ⟨8, u, u.2.2⟩

/-- A gate `Bit² ⟶ Bit`, the graph of its truth table: two key columns, one val column. -/
def gate (f : Bool → Bool → Bool) : Except String (Rel Bit2 Bit) := do
  let xs := cube 2
  pure ⟨4, (← col 4 (xs.map (·.getD 0 0)), ← col 4 (xs.map (·.getD 1 0))),
    ← col 4 (xs.map fun x => if f (x.getD 0 0 == 1) (x.getD 1 0 == 1) then 1 else 0)⟩

/-- `F ≜ ⟨⟨x₁,π₃⟩ xor, ⟨⟨π₁,π₂⟩ and, ⟨x₁,π₃⟩ and⟩ or⟩` with `x₁ ≜ ⟨π₁,π₂⟩ xor`: (sum, carry). -/
def adder : Except String (Rel Bit3 Bit2) := do
  let (p₁, p₂, p₃) := (← π₁, ← π₂, ← π₃)
  let (xor, and, or) := (← gate (· != ·), ← gate (· && ·), ← gate (· || ·))
  let x₁ ← comp (← pair p₁ p₂) xor
  let x₂ ← pair x₁ p₃
  pair (← comp x₂ xor) (← comp (← pair (← comp (← pair p₁ p₂) and) (← comp x₂ and)) or)

/-- Query 6, `F p° : Bit³ ⟶ 1` with `p : 1 ⟶ Bit²` the point `(0,1)`: the inputs giving sum 0, carry 1. -/
def answer : Except String (Rel Bit3 Bit) := do
  let p : Rel Bit Bit2 := ⟨1, ← col 1 [0], (← col 1 [0], ← col 1 [1])⟩
  comp (← adder) (← conv p)

section Checks

-- row order is not part of a relation, so rows compare sorted
private def rows {v : Obj} (f : v.El → List Int64) (R : Rel Bit3 v) : List (List Int64) :=
  (R.toList.map fun ((a, b, c), y) => [a, b, c] ++ f y).mergeSort fun a b => decide (a ≤ b)

#guard (answer.map (rows fun _ => [])).toOption == some ([[0, 1, 1], [1, 0, 1], [1, 1, 0]] : List (List Int64))

private def full (xs : List Int64) : List Int64 :=
  let b := xs.map (· == 1)
  let s := b.foldl (· != ·) false; let c := (b.filter id).length ≥ 2
  xs ++ [if s then 1 else 0, if c then 1 else 0]

#guard (adder.map (rows (v := Bit2) fun (s, c) => [s, c])).toOption == some ((cube 3).map full)

#eval answer.map (rows fun _ => [])

end Checks

#print axioms adder

end LeetQ.Rel.Circuit
