import LeetQ.Rel.Algebra

/-! AIMA §11.1.3, the blocks world (the Sussman anomaly) as relation algebra on the blocks. A block is the long
    `0 … 2` (A = 0, B = 1, C = 2). A state is one map `S : X ⟶ X`: `(b, y)` puts `b` on the block `y`, `(b, b)`
    puts `b` on the table. Every relation below is `X ⟶ X`, composed in diagram order. -/

namespace LeetQ.Rel.Blocks

open Alg QLean

abbrev X : Obj := .long
abbrev V := Rel X X

/-- The 3 blocks. -/
def xs := col [0, 1, 2]
local instance : Univ X := ⟨_, xs⟩

/-- `S₀`, Init: C on A, A and B on the table. -/
def S₀ : V := ofPairs [(0, 0), (1, 1), (2, 0)]
/-- `G`: A on B, B on C. -/
def G : V := ofPairs [(0, 1), (1, 2)]

/-- `R ≜ S ∩ ∼𝟙`: `b` rests on another block. -/
def R (S : V) : V := S ∩ ∼𝟙

/-- `M ≜ ∼(R°⊤ ∪ ⊤R)`: nothing on `b`, nothing on `y`; `(b, y)` moves `b` onto `y`, `(b, b)` to the table. -/
def M (S : V) : V := ∼((R S)° ≫ ⊤ ∪ ⊤ ≫ R S)

/-- `S' ≜ (S ∩ ∼(p⊤)) ∪ p`: the move `p` replaces the row of its block. -/
def move (S p : V) : V := (S ∩ ∼(p ≫ ⊤)) ∪ p

/-- Breadth-first from `S₀` over the states, each reached once, to the first `S` with `G ⊑ S`; the moves as
    `(b, y)` pairs, empty when no plan reaches `G`. Three blocks have at most `3³` maps, so `27` levels exhaust
    the search. -/
def plan : List (Int64 × Int64) := Id.run do
  let mut seen : List V := [S₀]; let mut q : List (V × List (Int64 × Int64)) := [(S₀, [])]
  for _ in [0:27] do
    let mut next := []
    for (S, ps) in q do
      if G ⊑ S then return ps
      for p in (M S).toList do
        let S' := move S (ofPairs [p])
        if !seen.any (· == S') then seen := S' :: seen; next := next ++ [(S', ps ++ [p])]
    q := next
  return []

section Checks

private def sorted (R : V) : List (List Int64) :=
  (R.toList.map fun ((a, b) : Int64 × Int64) => [a, b]).mergeSort fun a b => decide (a ≤ b)

private def after : V := plan.foldl (fun S p => move S (ofPairs [p])) S₀

#guard sorted (M S₀) == [[1, 1], [1, 2], [2, 1], [2, 2]]
-- all three on the table: every move is allowed
#guard sorted (M 𝟙) == [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]]
-- MoveToTable C, Move B onto C, Move A onto B
#guard plan == [(2, 2), (1, 2), (0, 1)]
#guard (G ⊑ S₀) == false
#guard G ⊑ after

-- the operators are the only way a program writes these ops: the names must not resolve
/-- error: Unknown identifier `Alg.comp` -/
#guard_msgs in #check Alg.comp
/-- error: Unknown identifier `Alg.conv` -/
#guard_msgs in #check Alg.conv
/-- error: Unknown identifier `Alg.inter` -/
#guard_msgs in #check Alg.inter
/-- error: Unknown identifier `Alg.union` -/
#guard_msgs in #check Alg.union
/-- error: Unknown identifier `Alg.diff` -/
#guard_msgs in #check Alg.diff
/-- error: Unknown identifier `Alg.le` -/
#guard_msgs in #check Alg.le
/-- error: Unknown identifier `comp` -/
#guard_msgs in #check comp
/-- error: Unknown identifier `conv` -/
#guard_msgs in #check conv
/-- error: Unknown identifier `inter` -/
#guard_msgs in #check inter
/-- error: Unknown identifier `union` -/
#guard_msgs in #check union
/-- error: Unknown identifier `diff` -/
#guard_msgs in #check diff

end Checks

end LeetQ.Rel.Blocks
