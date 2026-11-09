import LeetQ.Rel.Chess

/-! AIMA §11.1.3, the blocks world (the Sussman anomaly) as relation algebra on the blocks. A block is the long
    `0 … 2` (A = 0, B = 1, C = 2). A state is one map `S : X ⟶ X`: `(b, y)` puts `b` on the block `y`, `(b, b)`
    puts `b` on the table. Every relation below is `X ⟶ X`, composed in diagram order. -/

namespace LeetQ.Rel.Blocks

open Alg QLean
open LeetQ.Rel.Chess (col ofPairs)

abbrev X : Obj := .long
abbrev V := Rel X X

/-- The 3 blocks. -/
def xs : Except String (Arr .long 3) := col 3 [0, 1, 2]
/-- `𝟙 : X ⟶ X` on the blocks. -/
def one : Except String V := do pure (idU (← xs))
/-- `⊤ : X ⟶ X`, every pair of blocks. -/
def T : Except String V := do let x ← xs; top x x

/-- `S₀`, Init: C on A, A and B on the table. -/
def S₀ : Except String V := ofPairs [(0, 0), (1, 1), (2, 0)]
/-- `G`: A on B, B on C. -/
def G : Except String V := ofPairs [(0, 1), (1, 2)]

/-- `R ≜ S ∩ ∼𝟙`: `b` rests on another block. -/
def R (S : V) : Except String V := do diff S (← one)

/-- `M ≜ ∼(R°⊤ ∪ ⊤R)`: nothing on `b`, nothing on `y`; `(b, y)` moves `b` onto `y`, `(b, b)` to the table. -/
def M (S : V) : Except String V := do
  let R ← R S; let T ← T
  diff T (← union (← comp (← conv R) T) (← comp T R))

/-- `S' ≜ (S ∩ ∼(p⊤)) ∪ p`: the move `p` replaces the row of its block. -/
def move (S p : V) : Except String V := do union (← diff S (← comp p (← T))) p

/-- `S = S'` as `S ⊑ S' ∧ S' ⊑ S`. -/
def same (S S' : V) : Except String Bool := do pure ((← le S S') && (← le S' S))

/-- Breadth-first from `S₀` over the states, each reached once, to the first `S` with `G ⊑ S`; the moves as
    `(b, y)` pairs. Three blocks have at most `3³` maps, so `27` levels exhaust the search. -/
def plan : Except String (List (Int64 × Int64)) := do
  let G ← G; let s ← S₀
  let mut seen : List V := [s]; let mut q : List (V × List (Int64 × Int64)) := [(s, [])]
  for _ in [0:27] do
    let mut next := []
    for (S, ps) in q do
      if ← le G S then return ps
      for p in (← M S).toList do
        let S' ← move S (← ofPairs [p])
        if !(← seen.anyM (same S')) then seen := S' :: seen; next := next ++ [(S', ps ++ [p])]
    q := next
  throw "Blocks: no plan from S₀ reaches G"

section Checks

private def sorted (R : Except String V) : Option (List (List Int64)) :=
  (do pure (((← R).toList.map fun ((a, b) : Int64 × Int64) => [a, b]).mergeSort fun a b => decide (a ≤ b))).toOption

private def goal (S : Except String V) : Option Bool := (do le (← G) (← S)).toOption

private def after : Except String V := do (← plan).foldlM (fun S p => do move S (← ofPairs [p])) (← S₀)

#guard sorted (do M (← S₀)) == some [[1, 1], [1, 2], [2, 1], [2, 2]]
-- all three on the table: every move is allowed
#guard sorted (do M (← one)) == some [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]]
-- MoveToTable C, Move B onto C, Move A onto B
#guard plan.toOption == some [(2, 2), (1, 2), (0, 1)]
#guard goal S₀ == some false
#guard goal after == some true

end Checks

end LeetQ.Rel.Blocks
