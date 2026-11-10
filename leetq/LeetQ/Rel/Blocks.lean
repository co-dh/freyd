import LeetQ.Rel.Algebra

/-! AIMA §11.1.3, the blocks world (the Sussman anomaly) as relation algebra on the blocks. A block is the long
    `0 … 2` (A = 0, B = 1, C = 2). A state is one map `S : X ⟶ X`: `(b, y)` puts `b` on the block `y`, `(b, b)`
    puts `b` on the table. The search holds a whole level of states as one relation `F : I ⟶ X×X`:
    `(i, (b, y))`, in state `i` the block `b` is on `y`. Composition is in diagram order. -/

namespace LeetQ.Rel.Blocks

open Alg QLean

abbrev X : Obj := .long
abbrev V := Rel X X
abbrev XX : Obj := .prod X X

/-- The 3 blocks. -/
def blocks : List Int64 := [0, 1, 2]
def xs := col blocks
local instance : Univ X := ⟨_, xs⟩

/-- `S₀`, Init: C on A, A and B on the table. -/
def S₀ : V := ofPairs [(0, 0), (1, 1), (2, 0)]
/-- `G`: A on B, B on C. -/
def G : V := ofPairs [(0, 1), (1, 2)]

/-- `π₁, π₂ : X×X ⟶ X`, the two sides of `𝟙×𝟙`. -/
def π₁ : Rel XX X := outl (prod 𝟙 𝟙)
def π₂ : Rel XX X := outr (prod 𝟙 𝟙)

/-- `S` as the level of the one state `0`. -/
def lvl (S : V) : Rel .long XX := top (A := .long) (col [0]) xs ≫ pair 𝟙 S

variable {I : Obj}

/-- `R ≜ F ∩ ∼𝟙`, per state: the rows off the diagonal `ran⟨𝟙, 𝟙⟩`. -/
def R (F : Rel I XX) : Rel I XX := F \ F ≫ ran (pair 𝟙 𝟙)

/-- `M ≜ ∼(R°⊤ ∪ ⊤R)`, per state: `⟨C, C⟩` with `C ≜ Fπ₁ − Rπ₂` the blocks nothing is on; the complement is
    taken against the level's own blocks `Fπ₁`, as `⊤` would need the states `I` as a universe. -/
def M (F : Rel I XX) : Rel I XX := let C := F ≫ π₁ \ R F ≫ π₂; pair C C

/-- `S' ≜ (S ∩ ∼(p⊤)) ∪ p`, per state: `pπ₁π₁°` is `p⊤` on the rows of the moved block. -/
def move (S p : Rel I XX) : Rel I XX := (S \ p ≫ π₁ ≫ π₁°) ∪ p

/-- The states `i` of `F` with `G ⊑ Fᵢ`: no row of `G` missing from `Fᵢ`. -/
def hit (G : V) (F : Rel I XX) : Rel I I := dom F \ dom (F ≫ π₁ ≫ ⊤ ≫ pair 𝟙 G \ F)

/-- `Fᵢ = Sⱼ`, the equal fibres; every state has rows, so the empty universes leave out no vacuous pair. -/
def same {J : Obj} (F : Rel I XX) (S : Rel J XX) : Rel I J := symDiv F S (Vals.empty _) (Vals.empty _)

/-- `<` on the blocks, and lexicographically on `X×X`: the order that picks one state of a class. -/
def lt : V := ofPairs (blocks.flatMap fun a => (blocks.filter (a < ·)).map (a, ·))
def ltXX : Rel XX XX := prod lt ⊤ ∪ prod 𝟙 lt

/-- One level `(F, <, P)` to the next, `P : I ⟶ ℕ×(X×X)` the path, `seen` the levels so far. Each state `i` and
    move `m` of `M` is the state `(i, m)`, `par` and `mv` the projections of that index; its rows are `move`'s,
    `<` is parent first then move, the path gains `(k, m)`. Kept: the `<`-least of each class of `same`, unless
    `same` as a state already seen. -/
def step : ((I : Obj) × Rel I XX × Rel I I × Rel I (.prod .long XX)) × List ((J : Obj) × Rel J XX) →
    ((I : Obj) × Rel I XX × Rel I I × Rel I (.prod .long XX)) × List ((J : Obj) × Rel J XX)
  | (⟨_, F, l, P⟩, seen) =>
    let c := ran (pair (dom (M F)) (M F)); let par := outl c; let mv := outr c
    let F' := move (par ≫ F) mv
    let l' := par ≫ l ≫ par° ∪ (par ≫ par°) ∩ (mv ≫ ltXX ≫ mv°)
    let old := seen.foldl (fun o ⟨_, S⟩ => o ∪ dom (same F' S)) zero
    let keep := (dom F' \ dom (same F' F' ∩ l'°)) \ old
    let P' := par ≫ P ∪ pair (mv ≫ π₁ ≫ top xs (B := .long) (col [Int64.ofNat seen.length])) mv
    (⟨_, keep ≫ F', keep ≫ l' ≫ keep, keep ≫ P'⟩, ⟨_, keep ≫ F'⟩ :: seen)

/-- `steps : k ⟶ m`, the `k`-th move of a shortest plan from `S` to `G`, empty when none: breadth-first from
    `S` until a level holds `G` or is empty, the path of its `<`-least goal state. Three blocks have at most
    `3³` maps, so `27` levels exhaust the search. -/
def steps (S G : V) : Rel .long XX :=
  match iter 27 (fun (⟨_, F, _, _⟩, _) => F ⊑ zero || !(hit G F ⊑ zero)) step
      (⟨_, lvl S, zero, zero⟩, [⟨_, lvl S⟩]) with
  | (⟨_, F, l, P⟩, _) =>
    let g := hit G F; let p := ran ((g \ dom (g ≫ l° ≫ g)) ≫ P)
    (outl p)° ≫ outr p

/-- The plan as a list: `steps` in the order of `k`. -/
def solve (S G : V) : List (Int64 × Int64) :=
  ((steps S G).toList.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

/-- The Sussman anomaly's plan. -/
def plan : List (Int64 × Int64) := solve S₀ G

section Checks

private def sorted (F : Rel .long XX) : List (List Int64) :=
  (F.toList.map fun ((_, (a, b)) : Int64 × Int64 × Int64) => [a, b]).mergeSort fun a b => decide (a ≤ b)

private def after : Rel .long XX := plan.foldl (fun F p => move F (lvl (ofPairs [p]))) (lvl S₀)

#guard sorted (M (lvl S₀)) == [[1, 1], [1, 2], [2, 1], [2, 2]]
-- all three on the table: every move is allowed
#guard sorted (M (lvl 𝟙)) == [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]]
-- MoveToTable C, Move B onto C, Move A onto B
#guard plan == [(2, 2), (1, 2), (0, 1)]
#guard (G ⊑ S₀) == false
#guard hit G (lvl S₀) ⊑ zero
#guard !(hit G after ⊑ zero)
-- from all on the table: Move B onto C, Move A onto B
#guard solve 𝟙 G == [(1, 2), (0, 1)]
-- A on B and B on A: no state holds it
#guard solve 𝟙 (ofPairs [(0, 1), (1, 0)]) == []

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
