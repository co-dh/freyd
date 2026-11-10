import LeetQ.Rel.Algebra

/-! AIMA §11.1.3, the blocks world (the Sussman anomaly) as relation algebra on the blocks. A block is the long
    `0 … 2` (A = 0, B = 1, C = 2). A state is one map `S : X ⟶ X`: `(b, y)` puts `b` on the block `y`, `(b, b)`
    puts `b` on the table. The search names each state by a `long` id, the number of the array `Λ` gives it,
    and holds many states as one
    relation `L : long ⟶ X×X`: `(i, (b, y))`, in state `i` the block `b` is on `y`. Composition is in diagram
    order. -/

namespace LeetQ.Rel.Blocks

open Alg QLean

abbrev X : Obj := .long
abbrev V := Rel X X
abbrev XX : Obj := .prod X X

/-- The 3 blocks. -/
def xs := col [0, 1, 2]
local instance : Univ X := ⟨_, xs⟩
/-- `X×X`, every pair of blocks: what `⊤ : X ⟶ X×X` ranges over. -/
local instance : Univ XX := ⟨_, (prod (𝟙 : V) 𝟙).key⟩

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

/-! ### Many states at once: `R`, `M`, `move` with the state as the key -/

/-- `π₁, π₂ : X×X ⟶ X`, the two sides of `𝟙×𝟙`. -/
def π₁ : Rel XX X := outl (prod 𝟙 𝟙)
def π₂ : Rel XX X := outr (prod 𝟙 𝟙)

/-- `⌊S⌋ : X×X ⟶ X×X`, the pairs of `S` as a coreflexive: `S ∩ T` per state is `L⌊T⌋`. -/
def pts (S : V) : Rel XX XX := ran (pair 𝟙 S)

/-- `S` as the level of the one state `0`. -/
def lvl (S : V) : Rel .long XX := top (A := .long) (col [0]) xs ≫ pair 𝟙 S

variable {I : Obj}

/-- `⊤` per state: each state of `L` to every pair (a state is a map, so `Lπ₁` is every block). -/
def all (L : Rel I XX) : Rel I XX := L ≫ π₁ ≫ ⊤

/-- `R ≜ S ∩ ∼𝟙`, per state. -/
def RL (L : Rel I XX) : Rel I XX := L ≫ pts (∼𝟙)

/-- `M ≜ ∼(R°⊤ ∪ ⊤R)`, per state: per state a set of pairs `T` reads `R°⊤` as `Rπ₂π₁°` (the pairs whose
    left a block rests on) and `⊤R` as `Rπ₂π₂°`. -/
def ML (L : Rel I XX) : Rel I XX := all L \ RL L ≫ π₂ ≫ (π₁° ∪ π₂°)

/-- `S' ≜ (S ∩ ∼(p⊤)) ∪ p`, per state: `p⊤` is `pπ₁π₁°`, the pairs of the moved block. -/
def moveL (S p : Rel I XX) : Rel I XX := (S \ p ≫ π₁ ≫ π₁°) ∪ p

/-- The states `i` of `L` with `G ⊑ Lᵢ`: no pair of `G` missing from `Lᵢ`. -/
def hit (G : V) (L : Rel I XX) : Rel I I := dom L \ dom (all L ≫ pts G \ L)

/-- Three blocks have at most `3³` maps: the bound on the states, so on the ids and on the levels. -/
def N : Nat := 27

/-- One round of the breadth-first search on `(St, L, P, d)`: `St` every state seen, `L` the last level, both
    keyed by the state id; `P : id ⟶ (k, m)` the path, `m` its `k`-th move; `d` the round. Each state `i` of `L`
    and move `m` of `ML` is the candidate `c = (i, m)`, `par`, `mv` its sides, `F'` its state. `Λ(F')` is each
    candidate's state as an array, equal states one array; `\ ran Λ(St)` drops the seen ones, and `num`
    numbers the rest past `St`'s ids. A new state's path is its least parent's (`est(<)`) and its move. -/
def round : Rel .long XX × Rel .long XX × Rel .long (.prod .long XX) × Nat →
    Rel .long XX × Rel .long XX × Rel .long (.prod .long XX) × Nat
  | (St, L, P, d) =>
    let c := ran (pair (dom (ML L)) (ML L)); let par := outl c; let mv := outr c
    let F' := moveL (par ≫ L) mv
    let E := num (ran Λ(F') \ ran Λ(St)) (dom St).n
    let L' := E ≫ mem E.val
    let cand := (Λ(F') ≫ E°)°
    let pick := cand ∩ est (lt (tilCol N)) (cand ≫ par) ≫ par°
    (St ∪ L', L', P ∪ pick ≫ (par ≫ P ∪ pair (mv ≫ π₁ ≫ top xs (col [Int64.ofNat d])) mv), d + 1)

/-- `steps : k ⟶ m`, the `k`-th move of a shortest plan from `S` to `G`, empty when none: rounds from `S` until
    `St` holds `G` or a level is empty, the path of the least goal id. -/
def steps (S G : V) : Rel .long XX :=
  match iter N (fun (St, L, _) => L ⊑ zero || !(hit G St ⊑ zero)) round (lvl S, lvl S, zero, 0) with
  | (St, _, P, _) =>
    -- the goal ids as one set, under the one key `0`, and its `est(<)`
    let h := hit G St; let p := ran (ran (est (lt (tilCol N)) (top (A := .long) (col [0]) h.key)) ≫ P)
    (outl p)° ≫ outr p

/-- The plan as a list: `steps` in the order of `k`. -/
def solve (S G : V) : List (Int64 × Int64) :=
  ((steps S G).toList.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

/-- The Sussman anomaly's plan. -/
def plan : List (Int64 × Int64) := solve S₀ G

section Checks

private def sorted (R : V) : List (List Int64) :=
  (R.toList.map fun ((a, b) : Int64 × Int64) => [a, b]).mergeSort fun a b => decide (a ≤ b)

private def after : V := plan.foldl (fun S p => move S (ofPairs [p])) S₀

#guard sorted (M S₀) == [[1, 1], [1, 2], [2, 1], [2, 2]]
-- all three on the table: every move is allowed
#guard sorted (M 𝟙) == [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2]]
-- the per-state versions on a one-state level are the single-state ones
#guard RL (lvl S₀) == lvl (R S₀)
#guard ML (lvl S₀) == lvl (M S₀)
#guard ML (lvl 𝟙) == lvl (M 𝟙)
#guard moveL (lvl S₀) (lvl (ofPairs [(2, 2)])) == lvl (move S₀ (ofPairs [(2, 2)]))
private def St : Rel .long XX := (iter N (fun _ => false) round (lvl S₀, lvl S₀, zero, 0)).1
-- the whole search: the 13 states of three blocks, ids `0 … 12`, each state under one id
#guard dom St == idU (col ((List.range 13).map Int64.ofNat))
#guard symDiv St St (Vals.empty _) (Vals.empty _) == dom St
-- MoveToTable C, Move B onto C, Move A onto B
#guard plan == [(2, 2), (1, 2), (0, 1)]
#guard (G ⊑ S₀) == false
#guard G ⊑ after
#guard hit G (lvl S₀) ⊑ zero
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
