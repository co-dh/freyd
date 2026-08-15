/-
  LeetCode 111 — Minimum Depth of Binary Tree — as an ALLEGORY PROGRAM.

  Problem: the minimum number of nodes on a shortest ROOT-TO-LEAF path (a leaf is a node with NO
  children).  Mirrors `leet/L104.lean` (Maximum Depth) with `imax` swapped for `imin` — but with
  a genuine extra case: a node with exactly ONE child is not a leaf, so the fold may NOT take
  `min(childDepth, 0)` at such a node — it must take the depth of the present child alone.

  1. **Data** — `Tree Int` (`AOP.A6_TreeBin`), `nil` an empty leaf slot, `node l a r` an
     `Int`-labelled internal node.

  2. **Program** — `minDepthFn`: `nil ↦ 0`; a `node` with both children `nil` (a genuine leaf)
     `↦ 1`; a node with exactly one `nil` child `↦ 1 + (depth of the present child)`; a node with
     both children present `↦ 1 + min(depth l, depth r)`.  Packaged as `solve := graph minDepthFn`.

  3. **Specification** — `IsRLDepth t d`: some root-to-leaf path in `t` has exactly `d` nodes
     (`leaf` = a single node with no children; `left`/`right` step down a NON-nil child).  For a
     non-empty tree, `minDepthFn` is the MINIMUM such `d`.

  4. **Correctness** — achievability (`minDepthFn t` is itself an `IsRLDepth` value, for
     `t ≠ nil`) and domination (`minDepthFn t` is `≤` every `IsRLDepth` value) — the min-form of
     L104's max-extremum shape.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import AOP.A7_4_Horner   -- `eq_Λ_comp_maxRel`: the `min (≤)·Λ spec` morphism-equation bridge
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC111

open Freyd Freyd.Alg.RelSet.TB

/-! ## Mathlib-free `Nat` `min` (copied from `L104`, control the rewrite set) -/

def imin (a b : Nat) : Nat := if a ≤ b then a else b

theorem imin_le_left  (a b : Nat) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Nat) : imin a b ≤ b := by unfold imin; split <;> omega
theorem imin_eq_or (a b : Nat) : imin a b = a ∨ imin a b = b := by
  unfold imin; split; exacts [Or.inl rfl, Or.inr rfl]

/-! ## A reusable non-confusion fact -/

/-- A `node` is never `nil` — used to discharge the `≠ Tree.nil` side-conditions of `IsRLDepth`'s
    `left`/`right` steps. -/
theorem node_ne_nil (l : Tree Int) (a : Int) (r : Tree Int) : Tree.node l a r ≠ Tree.nil := by
  intro h; cases h

/-! ## Data/answer objects in `Rel(Set)` -/

abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## The program: the min-depth fold, THREE-way branched on which children are present -/

/-- The fold: `nil ↦ 0`; a leaf (both children `nil`) `↦ 1`; a one-child node `↦ 1 + ` the depth
    of the present child (NOT `min(depth, 0)` — a one-child node is not a leaf); a two-child node
    `↦ 1 + min` of both children's depths. -/
def minDepthFn : Tree Int → Nat
  | Tree.nil => 0
  | Tree.node Tree.nil _ Tree.nil => 1
  | Tree.node Tree.nil _ (Tree.node rl ra rr) => 1 + minDepthFn (Tree.node rl ra rr)
  | Tree.node (Tree.node ll la lr) _ Tree.nil => 1 + minDepthFn (Tree.node ll la lr)
  | Tree.node (Tree.node ll la lr) _ (Tree.node rl ra rr) =>
      1 + imin (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr))

/-- **The allegory program**: LeetCode 111's solution as a morphism `dTree ℤ ⟶ ℕ` in `Rel(Set)`. -/
def solve : dTree Int ⟶ dNat := graph minDepthFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map minDepthFn

/-! ## Specification: the length (in nodes) of an achievable root-to-leaf path -/

/-- `IsRLDepth t d` — `t` has SOME root-to-leaf path with exactly `d` nodes.  `leaf`: a node with
    no children is itself a length-`1` path.  `left`/`right`: step down a NON-nil child (the
    one-child gotcha — you may only step into a child that is actually present). -/
inductive IsRLDepth : Tree Int → Nat → Prop where
  | leaf (a : Int) : IsRLDepth (Tree.node Tree.nil a Tree.nil) 1
  | left {l r : Tree Int} (a : Int) {d : Nat} (hl : l ≠ Tree.nil) (h : IsRLDepth l d) :
      IsRLDepth (Tree.node l a r) (d + 1)
  | right {l r : Tree Int} (a : Int) {d : Nat} (hr : r ≠ Tree.nil) (h : IsRLDepth r d) :
      IsRLDepth (Tree.node l a r) (d + 1)

/-- The **specification** as a morphism `dTree ℤ ⟶ ℕ` in `Rel(Set)`: the relation of achievable
    root-to-leaf path lengths.  LeetCode 111 asks for its `≤`-MINIMUM (among non-empty trees),
    `min (≤) · Λ IsRLDepth`. -/
def spec : dTree Int ⟶ dNat := fun t d => IsRLDepth t d

/-! ## Correctness: `minDepthFn` computes the minimum achievable root-to-leaf path length -/

/-- **Achievability**: `minDepthFn t` is itself an achievable root-to-leaf path length, for any
    non-empty `t`.  Proved by structural induction on `t`, splitting on which of `l`, `r` is
    `nil` to match `minDepthFn`'s three real branches. -/
theorem minDepthFn_isRL : ∀ t : Tree Int, t ≠ Tree.nil → IsRLDepth t (minDepthFn t) := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | node l a r ihl ihr =>
    intro _
    rcases l with _ | ⟨ll, la, lr⟩
    · rcases r with _ | ⟨rl, ra, rr⟩
      · -- both nil: a genuine leaf
        show IsRLDepth (Tree.node Tree.nil a Tree.nil) 1
        exact IsRLDepth.leaf a
      · -- l nil, r present: must step into r, not `min(_, 0)`
        have hrne := node_ne_nil rl ra rr
        have ihr' := ihr hrne
        show IsRLDepth (Tree.node Tree.nil a (Tree.node rl ra rr))
          (1 + minDepthFn (Tree.node rl ra rr))
        have heq : 1 + minDepthFn (Tree.node rl ra rr) = minDepthFn (Tree.node rl ra rr) + 1 := by
          omega
        rw [heq]; exact IsRLDepth.right a hrne ihr'
    · rcases r with _ | ⟨rl, ra, rr⟩
      · -- l present, r nil: symmetric one-child case
        have hlne := node_ne_nil ll la lr
        have ihl' := ihl hlne
        show IsRLDepth (Tree.node (Tree.node ll la lr) a Tree.nil)
          (1 + minDepthFn (Tree.node ll la lr))
        have heq : 1 + minDepthFn (Tree.node ll la lr) = minDepthFn (Tree.node ll la lr) + 1 := by
          omega
        rw [heq]; exact IsRLDepth.left a hlne ihl'
      · -- both present: the real min
        have hlne := node_ne_nil ll la lr
        have hrne := node_ne_nil rl ra rr
        show IsRLDepth (Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr))
          (1 + imin (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr)))
        rcases imin_eq_or (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr))
          with he | he
        · rw [he]
          have ihl' := ihl hlne
          have heq : 1 + minDepthFn (Tree.node ll la lr) = minDepthFn (Tree.node ll la lr) + 1 := by
            omega
          rw [heq]; exact IsRLDepth.left a hlne ihl'
        · rw [he]
          have ihr' := ihr hrne
          have heq : 1 + minDepthFn (Tree.node rl ra rr) = minDepthFn (Tree.node rl ra rr) + 1 := by
            omega
          rw [heq]; exact IsRLDepth.right a hrne ihr'

/-- **Domination**: `minDepthFn t` is `≤` every achievable root-to-leaf path length.  Proved by
    the SAME structural recursion on `t` as `minDepthFn`/`minDepthFn_isRL` (equation-style, so the
    proof can call itself on strictly smaller subtrees), splitting the `IsRLDepth` derivation with
    `cases` at each concrete node shape. -/
theorem minDepthFn_le_of_isRL : ∀ (t : Tree Int) (n : Nat), IsRLDepth t n → minDepthFn t ≤ n
  | Tree.nil, _, h => by cases h
  | Tree.node Tree.nil a Tree.nil, n, h => by
      cases h with
      | leaf => exact Nat.le_refl _
      | left _ hl _ => exact absurd rfl hl
      | right _ hr _ => exact absurd rfl hr
  | Tree.node Tree.nil a (Tree.node rl ra rr), n, h => by
      cases h with
      | left _ hl _ => exact absurd rfl hl
      | right _ _ hderiv =>
          have := minDepthFn_le_of_isRL (Tree.node rl ra rr) _ hderiv
          show 1 + minDepthFn (Tree.node rl ra rr) ≤ _
          omega
  | Tree.node (Tree.node ll la lr) a Tree.nil, n, h => by
      cases h with
      | left _ _ hderiv =>
          have := minDepthFn_le_of_isRL (Tree.node ll la lr) _ hderiv
          show 1 + minDepthFn (Tree.node ll la lr) ≤ _
          omega
      | right _ hr _ => exact absurd rfl hr
  | Tree.node (Tree.node ll la lr) a (Tree.node rl ra rr), n, h => by
      cases h with
      | left _ _ hderiv =>
          have h1 := minDepthFn_le_of_isRL (Tree.node ll la lr) _ hderiv
          have h2 := imin_le_left (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr))
          show 1 + imin (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr)) ≤ _
          omega
      | right _ _ hderiv =>
          have h1 := minDepthFn_le_of_isRL (Tree.node rl ra rr) _ hderiv
          have h2 := imin_le_right (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr))
          show 1 + imin (minDepthFn (Tree.node ll la lr)) (minDepthFn (Tree.node rl ra rr)) ≤ _
          omega

/-- `minDepthFn` is `0` only at the empty tree. -/
@[simp] theorem minDepthFn_nil : minDepthFn Tree.nil = 0 := rfl

/-- **Correctness of the allegory program** (`solve = min (≤) · Λ spec`, pointwise in `Rel(Set)`,
    for every non-empty tree): `minDepthFn t` is an achievable root-to-leaf path length and is
    `≤`-least among all achievable root-to-leaf path lengths. -/
theorem minDepth_correct (t : Tree Int) (ht : t ≠ Tree.nil) :
    IsRLDepth t (minDepthFn t) ∧ ∀ n, IsRLDepth t n → minDepthFn t ≤ n :=
  ⟨minDepthFn_isRL t ht, fun n h => minDepthFn_le_of_isRL t n h⟩

/-- The **totalized specification**: `spec` plus LeetCode's edge convention `minDepth ∅ = 0`.  The
    achievability relation `IsRLDepth` is empty on `Tree.nil` (an empty tree has no root-to-leaf
    path), so the plain `spec` has no minimum there; the extra clause `t = nil ∧ d = 0` pins the
    empty case, making the minimum total.  On a non-empty `t` the clause is vacuous, so `specT`
    agrees with `spec`. -/
def specT : dTree Int ⟶ dNat := fun t d => IsRLDepth t d ∨ (t = Tree.nil ∧ d = 0)

/-- **Honest headline (§7.5 `min (≤)·Λ spec`)**: `solve` is exactly the morphism `A specT ≫ maxRel D`
    for the REVERSED preference order `D w z := w ≤ z` (so `maxRel D` is the `≤`-minimum) — the
    shortest achievable root-to-leaf path length, with `∅ ↦ 0`.  Bridged from `minDepthFn_isRL` and
    `minDepthFn_le_of_isRL`. -/
theorem solve_eq_minRel : solve = Λ specT ≫ maxRel (fun w z : Nat => w ≤ z) :=
  eq_Λ_comp_maxRel _ (fun x y h1 h2 => Nat.le_antisymm h1 h2) minDepthFn specT
    (fun t => by
      cases t with
      | nil => exact Or.inr ⟨rfl, rfl⟩
      | node l a r => exact Or.inl (minDepthFn_isRL _ (node_ne_nil l a r)))
    (fun t d hd => by
      rcases hd with h | ⟨ht, hd0⟩
      · exact minDepthFn_le_of_isRL t d h
      · subst ht; subst hd0; exact Nat.le_refl 0)

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

example : minDepthFn (Tree.nil : Tree Int) = 0 := by decide
example : minDepthFn (Tree.node (leaf 2) 1 (leaf 3)) = 2 := by decide
-- The one-child gotcha: root `1` has ONLY a left child (a leaf `2`) — the shortest root-to-leaf
-- path is 1 → 2 (2 nodes), NOT 1 (the root alone is not a leaf, it has a child).
example : minDepthFn (Tree.node (leaf 2) 1 Tree.nil) = 2 := by decide

end Freyd.Alg.RelSet.LC111
