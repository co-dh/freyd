import LeetQ.Rel.Algebra

/-! AIMA §8.4.2's one-bit full adder C1 as one relation `F : Bit³ ⟶ Bit²` built by composition, and query 6 as
    the preimage `F p°` of the point `p = (0,1)`. A bit is the long 0 or 1; an element of `Bitⁿ` is the q simple
    list of its `n` longs, boxed in a general list, and `Bitⁿ` comes with its projections as tables. -/

namespace LeetQ.Rel.Circuit

open Alg QLean

abbrev Bit := QAtomicType.long
abbrev Tup := QAtomicType.general

/-- `(a, b, …)` as q's long list `a b …`. -/
def tup (xs : List Int64) : QValue := .vector .long xs.length (.bytes (packLongs xs)) none
def untup : QValue → Except String (List Int64)
  | .vector .long n (.bytes b) _ => do pure (← Arr.ofPart .long n (n, .bytes b) "untup").toList
  | _ => throw "untup: not a dense long list"

/-- A literal column of `n` longs or boxed tuples, the only two types here; `Arr.ofPart` checks the count. -/
def col : (t : QAtomicType) → (n : Nat) → List (El t) → Except String (Arr t n)
  | .long, n, xs => Arr.ofPart .long n (longs (packLongs xs)) "col"
  | .general, n, xs => Arr.ofPart .general n (genCol xs.toArray) "col"
  | t, _, _ => throw s!"col: no literal column of type {t.code}"
def rel {k v : QAtomicType} (xs : List (El k × El v)) : Except String (Rel k v) := do
  pure ⟨xs.length, ← col k _ (xs.map (·.1)), ← col v _ (xs.map (·.2))⟩

def bits : List Int64 := [0, 1]
/-- `Bitⁿ`'s elements, first component major. -/
def cube : Nat → List (List Int64)
  | 0 => [[]]
  | n + 1 => bits.flatMap fun b => (cube n).map (b :: ·)

/-- `πᵢ : Bitⁿ ⟶ Bit`, the graph of the `i`-th component. -/
def proj (n i : Nat) : Except String (Rel Tup Bit) := rel ((cube n).map fun xs => (tup xs, xs.getD i 0))
/-- A gate `Bit² ⟶ Bit`, the graph of its truth table. -/
def gate (f : Bool → Bool → Bool) : Except String (Rel Tup Bit) :=
  rel ((cube 2).map fun xs => (tup xs, if f (xs.getD 0 0 == 1) (xs.getD 1 0 == 1) then 1 else 0))

/-- `⟨R, S⟩ ≜ R π₁° ∩ S π₂°` into `Bit²`: the tabular allegory's pairing, where `Alg.pair`'s `Tab` would be a
    three-column table no `comp` accepts. -/
def pr {A : QAtomicType} (R S : Rel A Bit) : Except String (Rel A Tup) := do
  inter (← comp R (← conv (← proj 2 0))) (← comp S (← conv (← proj 2 1)))

/-- `F ≜ ⟨⟨x₁,π₃⟩ xor, ⟨⟨π₁,π₂⟩ and, ⟨x₁,π₃⟩ and⟩ or⟩` with `x₁ ≜ ⟨π₁,π₂⟩ xor`: (sum, carry). -/
def adder : Except String (Rel Tup Tup) := do
  let (p₁, p₂, p₃) := (← proj 3 0, ← proj 3 1, ← proj 3 2)
  let (xor, and, or) := (← gate (· != ·), ← gate (· && ·), ← gate (· || ·))
  let x₁ ← comp (← pr p₁ p₂) xor
  let x₂ ← pr x₁ p₃
  pr (← comp x₂ xor) (← comp (← pr (← comp (← pr p₁ p₂) and) (← comp x₂ and)) or)

/-- Query 6, `F p° : Bit³ ⟶ 1` with `p : 1 ⟶ Bit²` the point `(0,1)`: the inputs giving sum 0, carry 1. -/
def answer : Except String (Rel Tup Bit) := do comp (← adder) (← conv (← rel [((0 : Int64), tup [0, 1])]))

section Checks

-- row order is not part of a relation, so rows compare sorted
private def rows {v : QAtomicType} (f : El v → Except String (List Int64)) (R : Rel Tup v) : Except String (List (List Int64)) := do
  pure ((← R.toList.mapM fun (x, y) => do pure ((← untup x) ++ (← f y))).mergeSort fun a b => decide (a ≤ b))

#guard (answer >>= rows fun _ => pure []).toOption == some ([[0, 1, 1], [1, 0, 1], [1, 1, 0]] : List (List Int64))

private def full (xs : List Int64) : List Int64 :=
  let b := xs.map (· == 1)
  let s := b.foldl (· != ·) false; let c := (b.filter id).length ≥ 2
  xs ++ [if s then 1 else 0, if c then 1 else 0]

#guard (adder >>= rows untup).toOption == some ((cube 3).map full)

end Checks

#print axioms adder

end LeetQ.Rel.Circuit
