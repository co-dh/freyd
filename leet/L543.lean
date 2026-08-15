/-
  LeetCode 543 — Diameter of Binary Tree — as an ALLEGORY PROGRAM (tupled tree cata).

  Problem: the diameter is the number of EDGES on the longest path between any two nodes in the
  tree (the path need not pass through the root; a single-node tree has diameter `0`).

  `L124`'s `(best, gain)` shape, one level simpler (`Nat` throughout, no `Option`, no dependence on
  node VALUES — edge counts are never negative, and the empty tree's diameter, `0`, is a genuine
  achievable value, not a "no path" case needing a sentinel):

  1. **Program.**  `foldFn t = (height, diam)`: `height` is `L104`'s `depthFn` (node-counted depth,
     `nil ↦ 0`, `node ↦ 1 + max(hl, hr)`) — folded again here so the SAME pass also threads `diam`.
     `diam` is the max number of edges on ANY path in `t`: the best of the left subtree, the right
     subtree, or the path that bends AT this root, connecting the deepest point reachable in each
     child — `through = hl + hr` (each child's `height` already counts the edge INTO that child's
     own deepest descendant, so `hl + hr`, not `hl + hr + 2`, is the through-root edge total).

  2. **Specification, two layers (through-root vs in-subtree), the `L124`/`L104` shape.**
     `downPath t v` — `v` is the length of SOME root-to-`nil` path in `t` (verbatim `L104`'s
     `pathLen`, re-derived here since `L104` isn't imported: `nil ↦ v = 0`, so a `nil` child is a
     legitimate, non-`False`, zero-length path — this is what sidesteps `L124`'s nil-child witness
     trap here).  `pathEdges t k` — `k` is the edge-count of SOME valid path in `t`: entirely in the
     left subtree, entirely in the right, or bending at the root (`downPath l kl`, `downPath r kr`,
     `k = kl + kr`).  LeetCode 543 asks for `pathEdges`'s `≤`-maximum, `max (≤) · Λ pathEdges`, for
     EVERY tree (`nil` included: `pathEdges nil k := k = 0`, matching the fold's `diam = 0` there —
     no `L124`-style `Option`/non-empty carve-out needed).

  3. **Correctness.**  `height_achieves`/`height_dominates`: `heightFn = max (≤) · Λ downPath` (the
     `L104` result, re-derived here).  `solve_achieves`/`solve_dominates`: `solveFn = max (≤) · Λ
     pathEdges`, by ONE structural recursion on `t` (including `nil`), using
     `height_achieves`/`height_dominates` to bound the through-root layer and `imax_eq_or` for the
     three-way choice in `diam`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import AOP.A7_4_Horner
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC543

open Freyd Freyd.Alg.RelSet.TB

/-! ## Mathlib-free `Nat` `min`/`max` (copied from `L104`/`L124`) -/

def imin (a b : Nat) : Nat := if a ≤ b then a else b
def imax (a b : Nat) : Nat := if a ≤ b then b else a

theorem imin_le_left  (a b : Nat) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Nat) : imin a b ≤ b := by unfold imin; split <;> omega
theorem imin_eq_or (a b : Nat) : imin a b = a ∨ imin a b = b := by
  unfold imin; split; exacts [Or.inl rfl, Or.inr rfl]
theorem imax_ge_left  (a b : Nat) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Nat) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Nat) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Object of `Nat` answers in `Rel(Set)` -/

abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## The program: the tupled fold `(height, diam)` -/

/-- The tupled fold: `height` = `L104`'s node-counted depth; `diam` = max edge-count of any path
    anywhere in the (sub)tree. -/
def foldFn : Tree Int → Nat × Nat
  | Tree.nil => (0, 0)
  | Tree.node l a r =>
    let (hl, bl) := foldFn l
    let (hr, br) := foldFn r
    (1 + imax hl hr, imax (imax bl br) (hl + hr))

/-- `heightFn t` — the fold's first component: `L104`'s `depthFn`. -/
def heightFn (t : Tree Int) : Nat := (foldFn t).1

/-- `solveFn t` — the answer: max edge-count of any path anywhere in `t`. -/
def solveFn (t : Tree Int) : Nat := (foldFn t).2

@[simp] theorem heightFn_nil : heightFn Tree.nil = 0 := rfl
@[simp] theorem solveFn_nil : solveFn Tree.nil = 0 := rfl

theorem heightFn_node (l r : Tree Int) (a : Int) :
    heightFn (Tree.node l a r) = 1 + imax (heightFn l) (heightFn r) := rfl

theorem solveFn_node (l r : Tree Int) (a : Int) :
    solveFn (Tree.node l a r) =
      imax (imax (solveFn l) (solveFn r)) (heightFn l + heightFn r) := rfl

/-- **The allegory program**: LeetCode 543's solution as a morphism `dTree ℤ ⟶ ℕ` in `Rel(Set)`. -/
def solve : dTree Int ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Specification, layer 1: root-to-`nil` path lengths (`L104`'s `pathLen`, re-derived) -/

/-- `downPath t v` — `v` is the length of SOME root-to-`nil` path in `t` (a `nil` child IS a valid
    zero-length path — verbatim `L104`'s `pathLen`). -/
def downPath : Tree Int → Nat → Prop
  | Tree.nil => fun v => v = 0
  | Tree.node l a r => fun v => ∃ v', (downPath l v' ∨ downPath r v') ∧ v = v' + 1

@[simp] theorem downPath_nil (v : Nat) : downPath Tree.nil v = (v = 0) := rfl

/-! ## Correctness, layer 1: `heightFn = max (≤) · Λ downPath` (re-derives `L104`) -/

theorem height_achieves : ∀ t : Tree Int, downPath t (heightFn t)
  | Tree.nil => by show heightFn Tree.nil = 0; rfl
  | Tree.node l a r => by
    show ∃ v', (downPath l v' ∨ downPath r v') ∧ heightFn (Tree.node l a r) = v' + 1
    rw [heightFn_node]
    cases imax_eq_or (heightFn l) (heightFn r) with
    | inl he => exact ⟨heightFn l, Or.inl (height_achieves l), by omega⟩
    | inr he => exact ⟨heightFn r, Or.inr (height_achieves r), by omega⟩

theorem height_dominates : ∀ (t : Tree Int) (v : Nat), downPath t v → v ≤ heightFn t
  | Tree.nil, v, h => by have hv : v = 0 := h; omega
  | Tree.node l a r, v, h => by
    obtain ⟨v', hv', hv⟩ := h
    rw [heightFn_node]
    have hgl := imax_ge_left (heightFn l) (heightFn r)
    have hgr := imax_ge_right (heightFn l) (heightFn r)
    cases hv' with
    | inl hl => have := height_dominates l v' hl; omega
    | inr hr => have := height_dominates r v' hr; omega

/-! ## Specification, layer 2: any valid path (through-root-bending vs in-subtree) -/

/-- `pathEdges t k` — `k` is the edge-count of SOME valid path in `t`: entirely in the left
    subtree, entirely in the right subtree, or bending at the root (a `downPath` on each side).
    `nil` has exactly the trivial `0`-edge path — no `Option`/non-empty carve-out needed, unlike
    `L124`'s sum-valued `pathSum`. -/
def pathEdges : Tree Int → Nat → Prop
  | Tree.nil => fun k => k = 0
  | Tree.node l a r => fun k =>
      pathEdges l k ∨ pathEdges r k ∨ ∃ kl kr, downPath l kl ∧ downPath r kr ∧ k = kl + kr

@[simp] theorem pathEdges_nil (k : Nat) : pathEdges Tree.nil k = (k = 0) := rfl

/-! ## Correctness, layer 2: `solveFn = max (≤) · Λ pathEdges` -/

/-- **Achievability**: `solveFn t` is itself an achievable `pathEdges` value, for every tree
    (`nil` included: `solveFn nil = 0`, the trivial path). -/
theorem solve_achieves : ∀ t : Tree Int, pathEdges t (solveFn t)
  | Tree.nil => by show solveFn Tree.nil = 0; rfl
  | Tree.node l a r => by
    show pathEdges l (solveFn (Tree.node l a r)) ∨ pathEdges r (solveFn (Tree.node l a r)) ∨
      ∃ kl kr, downPath l kl ∧ downPath r kr ∧ solveFn (Tree.node l a r) = kl + kr
    rw [solveFn_node]
    cases imax_eq_or (imax (solveFn l) (solveFn r)) (heightFn l + heightFn r) with
    | inl h1 =>
      cases imax_eq_or (solveFn l) (solveFn r) with
      | inl h2 => exact Or.inl (by rw [h1, h2]; exact solve_achieves l)
      | inr h2 => exact Or.inr (Or.inl (by rw [h1, h2]; exact solve_achieves r))
    | inr h1 =>
      exact Or.inr (Or.inr ⟨heightFn l, heightFn r, height_achieves l, height_achieves r, h1⟩)

/-- **Domination**: `solveFn t` dominates every achievable `pathEdges` value, for every tree. -/
theorem solve_dominates : ∀ (t : Tree Int) (k : Nat), pathEdges t k → k ≤ solveFn t
  | Tree.nil, k, h => by have hk : k = 0 := h; omega
  | Tree.node l a r, k, h => by
    rw [solveFn_node]
    have h1 := imax_ge_left (imax (solveFn l) (solveFn r)) (heightFn l + heightFn r)
    have h2 := imax_ge_right (imax (solveFn l) (solveFn r)) (heightFn l + heightFn r)
    have h3 := imax_ge_left (solveFn l) (solveFn r)
    have h4 := imax_ge_right (solveFn l) (solveFn r)
    rcases h with h | h | h
    · have := solve_dominates l k h; omega
    · have := solve_dominates r k h; omega
    · obtain ⟨kl, kr, hkl, hkr, hk⟩ := h
      have hl' := height_dominates l kl hkl
      have hr' := height_dominates r kr hkr
      omega

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ pathEdges`, pointwise in
    `Rel(Set)`, for EVERY tree — `nil` included, unlike `L124`'s non-empty-only statement, since
    `Nat`'s `0` is a genuine achievable diameter, not a missing-value case). -/
theorem solve_correct (t : Tree Int) :
    pathEdges t (solveFn t) ∧ ∀ k, pathEdges t k → k ≤ solveFn t :=
  ⟨solve_achieves t, fun k h => solve_dominates t k h⟩

/-- The specification morphism `dTree Int ⟶ dNat`, for the honest-headline bridge below. -/
def spec : dTree Int ⟶ dNat := fun t k => pathEdges t k

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `solve` is exactly the morphism `Λ spec ≫ maxRel D`
    for the `≤`-preference order `D w z := z ≤ w` — not merely pointwise. Bridged from `solve_correct`. -/
theorem solve_eq_maxRel : solve = Λ spec ≫ maxRel (fun w z : Nat => z ≤ w) :=
  eq_Λ_comp_maxRel _ (fun x y h1 h2 => Nat.le_antisymm h2 h1) solveFn spec
    (fun t => (solve_correct t).1) (fun t v hv => (solve_correct t).2 v hv)

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

example : solveFn (Tree.node (Tree.node (leaf 4) 2 (leaf 5)) 1 (leaf 3)) = 3 := by decide
example : solveFn (leaf 1) = 0 := by decide
example : solveFn (Tree.nil : Tree Int) = 0 := by decide
example : solveFn (Tree.node (leaf 1) 2 Tree.nil) = 1 := by decide

end Freyd.Alg.RelSet.LC543
