/-
  LeetCode 124 — Binary Tree Maximum Path Sum — as an ALLEGORY PROGRAM (tupled tree cata).

  Problem: a path is a non-empty sequence of connected nodes that bends AT MOST ONCE (goes up to a
  node then back down); maximise the sum of node values on a path.  Values may be negative; the
  path must have `≥ 1` node.

  This is L104's `TreeCata` engine (`AOP.A6_TreeBin`) with a TUPLED fold state, the tree analogue
  of L53's suffix/anywhere split:

  1. **Program.**  `foldFn t = (best, gain)`: `gain` is the max sum of a path that STARTS at `t`'s
     root and goes strictly downward (choosing a side at each step, never bending) — `Int`-valued,
     since the empty tree contributes `0` (no extension) and every node contributes at least its
     own label.  `best` is the max sum of ANY path anywhere in `t` — `Option Int`-valued, since the
     EMPTY tree has no path at all (`none`); every non-empty tree's `best` is a `some`, built as the
     three-way `Option`-max of the left subtree's best, the right subtree's best, and the sum of the
     path that bends AT this root (`through = a + max 0 gl + max 0 gr`).

  2. **Specification, two layers (through-root vs in-subtree), the tree analogue of L53's
     suffix/anywhere split.**  `downPath t v` — `v` is achievable by a NON-bending path starting at
     `t`'s root (mirrors `gain`).  `pathSum t v` — `v` is achievable by ANY valid path in `t`: one
     entirely inside the left subtree, one entirely inside the right subtree, or one that bends AT
     the root (a `downPath`-or-skip on each side).  LeetCode 124 asks for `pathSum`'s `≤`-maximum
     among non-empty trees, `max (≤) · Λ pathSum`.

  3. **Correctness.**  `gain_achieves`/`gain_dominates`: `gainFn` is exactly `max (≤) · Λ downPath`
     (refinement + domination, holding for EVERY tree, `nil` included — vacuously, since `downPath
     nil v` is `False`).  `best_achieves`/`best_dominates`: whenever `solveFn t = some m` (always the
     case for a non-empty `t`), `m` is an achievable `pathSum` and dominates every achievable
     `pathSum` — proved by ONE structural induction on `t`, using `gain_achieves`/`gain_dominates` to
     bound the through-root layer and a small `omax` case-split lemma (`omax_eq_or`) for the
     three-way choice in `best`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_TreeBin
import AOP.A7_4_Horner
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC124

open Freyd Freyd.Alg.RelSet.TB

/-! ## Integer `min`/`max` (copied from `L104`/`L121`, `Int`-typed here) -/

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imin_le_left  (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
theorem imin_eq_or (a b : Int) : imin a b = a ∨ imin a b = b := by
  unfold imin; split; exacts [Or.inl rfl, Or.inr rfl]
theorem imax_ge_left  (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Int) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## `Option`-max on `Int` (`none` is the bottom — "no path here") -/

/-- `omax` — maximum on `Option Int` with `none` (bottom, "nothing achievable") as the identity. -/
def omax : Option Int → Option Int → Option Int
  | none, none => none
  | none, some y => some y
  | some x, none => some x
  | some x, some y => some (imax x y)

@[simp] theorem omax_none_none : omax none none = (none : Option Int) := rfl
@[simp] theorem omax_none_some (y : Int) : omax none (some y) = some y := rfl
@[simp] theorem omax_some_none (x : Int) : omax (some x) none = some x := rfl
@[simp] theorem omax_some_some (x y : Int) : omax (some x) (some y) = some (imax x y) := rfl

/-- `omax x y` always equals one of its two (whole) `Option` arguments. -/
theorem omax_eq_or (x y : Option Int) : omax x y = x ∨ omax x y = y := by
  cases x with
  | none => cases y with
    | none => exact Or.inl rfl
    | some yv => exact Or.inr rfl
  | some xv => cases y with
    | none => exact Or.inl rfl
    | some yv =>
      rcases imax_eq_or xv yv with h | h
      · exact Or.inl (by rw [omax_some_some, h])
      · exact Or.inr (by rw [omax_some_some, h])

/-- `omax x (some y)` is never `none` — the "some" side always wins or gets beaten. -/
theorem omax_ne_none_of_right_some (x : Option Int) (y : Int) : omax x (some y) ≠ none := by
  cases x <;> simp [omax]

/-! ## Data/answer objects in `Rel(Set)` -/

/-- The answer object: `Option Int`, `none` standing for "no path" (only the empty tree). -/
abbrev dAns : RelSet.{0} := ⟨Option Int⟩

/-! ## The program: the tupled fold `(best, gain)` -/

/-- The tupled fold: `gain` = max sum of a non-bending path starting at the root and going strictly
    downward; `best` = max sum of ANY path anywhere in the (sub)tree (`none` only for the empty
    tree). -/
def foldFn : Tree Int → Option Int × Int
  | Tree.nil => (none, 0)
  | Tree.node l a r =>
    let (bl, gl) := foldFn l
    let (br, gr) := foldFn r
    let gain := a + imax 0 (imax gl gr)
    let through := a + imax 0 gl + imax 0 gr
    let best := omax (omax bl br) (some through)
    (best, gain)

/-- `gainFn t` — the second fold component: max sum of a non-bending root-started downward path
    (`0` for the empty tree — no extension). -/
def gainFn (t : Tree Int) : Int := (foldFn t).2

/-- `solveFn t` — the answer: max sum of ANY path anywhere in `t` (`none` only for `Tree.nil`). -/
def solveFn (t : Tree Int) : Option Int := (foldFn t).1

@[simp] theorem gainFn_nil : gainFn Tree.nil = 0 := rfl
@[simp] theorem solveFn_nil : solveFn Tree.nil = none := rfl

theorem gainFn_node (l r : Tree Int) (a : Int) :
    gainFn (Tree.node l a r) = a + imax 0 (imax (gainFn l) (gainFn r)) := rfl

theorem solveFn_node (l r : Tree Int) (a : Int) :
    solveFn (Tree.node l a r) =
      omax (omax (solveFn l) (solveFn r))
        (some (a + imax 0 (gainFn l) + imax 0 (gainFn r))) := rfl

/-- **The allegory program**: LeetCode 124's solution as a morphism `dTree ℤ ⟶ dAns` in `Rel(Set)`. -/
def solve : dTree Int ⟶ dAns := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Specification, layer 1: non-bending root-started downward paths (mirrors `gain`) -/

/-- `downPath t v` — `v` is the sum of a path starting at `t`'s root and descending strictly
    downward (choosing a side at each step, never bending).  `False` for the empty tree — there is
    no root to start from. -/
def downPath : Tree Int → Int → Prop
  | Tree.nil => fun _ => False
  | Tree.node l a r => fun v =>
      v = a ∨ (∃ v', downPath l v' ∧ v = a + v') ∨ (∃ v', downPath r v' ∧ v = a + v')

@[simp] theorem downPath_nil (v : Int) : downPath Tree.nil v = False := rfl

/-! ## Specification, layer 2: any valid path (through-root-bending vs in-subtree) -/

/-- `pathSum t v` — `v` is the sum of SOME valid (`≥1`-node, ≤one-bend) path in `t`: entirely in the
    left subtree, entirely in the right subtree, or bending at the root (a `downPath`-or-skip on
    each side).  `False` for the empty tree — it has no path. -/
def pathSum : Tree Int → Int → Prop
  | Tree.nil => fun _ => False
  | Tree.node l a r => fun v =>
      pathSum l v ∨ pathSum r v ∨
      ∃ vl vr, (vl = 0 ∨ downPath l vl) ∧ (vr = 0 ∨ downPath r vr) ∧ v = a + vl + vr

@[simp] theorem pathSum_nil (v : Int) : pathSum Tree.nil v = False := rfl

/-! ## Correctness, layer 1: `gainFn = max (≤) · Λ downPath` -/

/-- `gainFn` dominates every achievable `downPath` value — holds for EVERY tree, `nil` included
    (vacuously: `downPath nil v` is `False`). -/
theorem gain_dominates : ∀ (t : Tree Int) (v : Int), downPath t v → v ≤ gainFn t := by
  intro t
  induction t with
  | nil => intro v h; exact h.elim
  | node l a r ihl ihr =>
    intro v h
    rw [gainFn_node]
    have h0 := imax_ge_left 0 (imax (gainFn l) (gainFn r))
    have h0' := imax_ge_right 0 (imax (gainFn l) (gainFn r))
    have hgl := imax_ge_left (gainFn l) (gainFn r)
    have hgr := imax_ge_right (gainFn l) (gainFn r)
    rcases h with h | h | h
    · omega
    · obtain ⟨v', hv', hveq⟩ := h; have := ihl v' hv'; omega
    · obtain ⟨v', hv', hveq⟩ := h; have := ihr v' hv'; omega

/-- `gainFn` is ITSELF an achievable `downPath` value, for any non-empty tree.  Routes through the
    "just the root" witness (`v = a`) whenever a child is `Tree.nil` (its `gainFn` is `0` by
    definition, so the recursive witness would need `downPath nil 0`, which is `False`) — the empty
    child never actually needs to be descended into. -/
theorem gain_achieves : ∀ t : Tree Int, t = Tree.nil ∨ downPath t (gainFn t) := by
  intro t
  induction t with
  | nil => exact Or.inl rfl
  | node l a r ihl ihr =>
    right
    show downPath (Tree.node l a r) (a + imax 0 (imax (gainFn l) (gainFn r)))
    rcases imax_eq_or 0 (imax (gainFn l) (gainFn r)) with h0 | h0
    · exact Or.inl (by omega)
    · rw [h0]
      rcases imax_eq_or (gainFn l) (gainFn r) with h1 | h1
      · rw [h1]
        rcases ihl with hl | hl
        · have hgl0 : gainFn l = 0 := by rw [hl]; exact gainFn_nil
          exact Or.inl (by omega)
        · exact Or.inr (Or.inl ⟨gainFn l, hl, rfl⟩)
      · rw [h1]
        rcases ihr with hr | hr
        · have hgr0 : gainFn r = 0 := by rw [hr]; exact gainFn_nil
          exact Or.inl (by omega)
        · exact Or.inr (Or.inr ⟨gainFn r, hr, rfl⟩)

/-! ## Correctness, layer 2: `solveFn = max (≤) · Λ pathSum`, whenever it is `some` -/

/-- `solveFn (node l a r)` is never `none` — the top-level `omax`'s right argument is always a
    `some` (the through-root value), so `omax _ (some _)` is never `none`. -/
theorem solveFn_ne_none_of_node (l r : Tree Int) (a : Int) : solveFn (Tree.node l a r) ≠ none := by
  rw [solveFn_node]; exact omax_ne_none_of_right_some _ _

/-- `solveFn (node l a r)` equals ONE of: `solveFn l`, `solveFn r`, or `some` of the through-root
    sum — the three-way choice `omax` makes, unpacked from two nested `omax_eq_or` applications. -/
theorem solveFn_choice (l r : Tree Int) (a : Int) :
    solveFn (Tree.node l a r) = solveFn l ∨ solveFn (Tree.node l a r) = solveFn r ∨
    solveFn (Tree.node l a r) = some (a + imax 0 (gainFn l) + imax 0 (gainFn r)) := by
  rw [solveFn_node]
  rcases omax_eq_or (omax (solveFn l) (solveFn r))
    (some (a + imax 0 (gainFn l) + imax 0 (gainFn r))) with h2 | h2
  · rcases omax_eq_or (solveFn l) (solveFn r) with h | h
    · exact Or.inl (by rw [h2, h])
    · exact Or.inr (Or.inl (by rw [h2, h]))
  · exact Or.inr (Or.inr h2)

/-- `x ≤ m` whenever `solveFn l = some x` and `solveFn (node l a r) = some m` — the left child's
    achievable best never exceeds the whole tree's best. -/
theorem solveFn_ge_left {l r : Tree Int} {a x m : Int} (hbl : solveFn l = some x)
    (hm : solveFn (Tree.node l a r) = some m) : x ≤ m := by
  rw [solveFn_node, hbl] at hm
  rcases hbr : solveFn r with _ | y <;> rw [hbr] at hm
  · rw [omax_some_none, omax_some_some] at hm
    injection hm with h
    have := imax_ge_left x (a + imax 0 (gainFn l) + imax 0 (gainFn r)); omega
  · rw [omax_some_some, omax_some_some] at hm
    injection hm with h
    have h1 := imax_ge_left x y
    have h2 := imax_ge_left (imax x y) (a + imax 0 (gainFn l) + imax 0 (gainFn r))
    omega

/-- `y ≤ m` whenever `solveFn r = some y` and `solveFn (node l a r) = some m` — symmetric to
    `solveFn_ge_left`. -/
theorem solveFn_ge_right {l r : Tree Int} {a y m : Int} (hbr : solveFn r = some y)
    (hm : solveFn (Tree.node l a r) = some m) : y ≤ m := by
  rw [solveFn_node, hbr] at hm
  rcases hbl : solveFn l with _ | x <;> rw [hbl] at hm
  · rw [omax_none_some, omax_some_some] at hm
    injection hm with h
    have := imax_ge_left y (a + imax 0 (gainFn l) + imax 0 (gainFn r)); omega
  · rw [omax_some_some, omax_some_some] at hm
    injection hm with h
    have h1 := imax_ge_right x y
    have h2 := imax_ge_left (imax x y) (a + imax 0 (gainFn l) + imax 0 (gainFn r))
    omega

/-- The through-root sum never exceeds the whole tree's best. -/
theorem solveFn_ge_through {l r : Tree Int} {a m : Int}
    (hm : solveFn (Tree.node l a r) = some m) :
    a + imax 0 (gainFn l) + imax 0 (gainFn r) ≤ m := by
  rw [solveFn_node] at hm
  rcases homax : omax (solveFn l) (solveFn r) with _ | z <;> rw [homax] at hm
  · rw [omax_none_some] at hm; injection hm with h; omega
  · rw [omax_some_some] at hm
    injection hm with h
    have := imax_ge_right z (a + imax 0 (gainFn l) + imax 0 (gainFn r)); omega

/-- **Achievability**: whenever `solveFn t = some m`, `m` is an achievable `pathSum` in `t`. -/
theorem best_achieves : ∀ (t : Tree Int) (m : Int), solveFn t = some m → pathSum t m := by
  intro t
  induction t with
  | nil => intro m h; exact absurd h (by simp)
  | node l a r ihl ihr =>
    intro m hm
    rcases solveFn_choice l r a with h | h | h
    · rw [h] at hm; exact Or.inl (ihl m hm)
    · rw [h] at hm; exact Or.inr (Or.inl (ihr m hm))
    · rw [h] at hm
      injection hm with hm'
      refine Or.inr (Or.inr ⟨imax 0 (gainFn l), imax 0 (gainFn r), ?_, ?_, by omega⟩)
      · rcases imax_eq_or 0 (gainFn l) with h0 | h0
        · exact Or.inl h0
        · rcases gain_achieves l with hl | hl
          · have hgl0 : gainFn l = 0 := by rw [hl]; exact gainFn_nil
            exact Or.inl (by rw [h0]; exact hgl0)
          · exact Or.inr (by rw [h0]; exact hl)
      · rcases imax_eq_or 0 (gainFn r) with h0 | h0
        · exact Or.inl h0
        · rcases gain_achieves r with hr | hr
          · have hgr0 : gainFn r = 0 := by rw [hr]; exact gainFn_nil
            exact Or.inl (by rw [h0]; exact hgr0)
          · exact Or.inr (by rw [h0]; exact hr)

/-- **Domination**: whenever `solveFn t = some m`, `m` dominates every achievable `pathSum` in
    `t`. -/
theorem best_dominates : ∀ (t : Tree Int) (m v : Int), solveFn t = some m → pathSum t v → v ≤ m := by
  intro t
  induction t with
  | nil => intro m v hm hv; exact hv.elim
  | node l a r ihl ihr =>
    intro m v hm hv
    rcases hv with hv | hv | hv
    · rcases hbl : solveFn l with _ | x
      · exact absurd hv (fun hv' => by
          have : l = Tree.nil := by
            cases l with
            | nil => rfl
            | node l₁ a₁ r₁ => exact absurd hbl (solveFn_ne_none_of_node l₁ r₁ a₁)
          rw [this] at hv'; exact hv')
      · exact Int.le_trans (ihl x v hbl hv) (solveFn_ge_left hbl hm)
    · rcases hbr : solveFn r with _ | y
      · exact absurd hv (fun hv' => by
          have : r = Tree.nil := by
            cases r with
            | nil => rfl
            | node l₁ a₁ r₁ => exact absurd hbr (solveFn_ne_none_of_node l₁ r₁ a₁)
          rw [this] at hv'; exact hv')
      · exact Int.le_trans (ihr y v hbr hv) (solveFn_ge_right hbr hm)
    · obtain ⟨vl, vr, hvl, hvr, hveq⟩ := hv
      have hvl' : vl ≤ imax 0 (gainFn l) := by
        rcases hvl with hvl | hvl
        · rw [hvl]; exact imax_ge_left 0 (gainFn l)
        · have := gain_dominates l vl hvl; have h0 := imax_ge_right 0 (gainFn l); omega
      have hvr' : vr ≤ imax 0 (gainFn r) := by
        rcases hvr with hvr | hvr
        · rw [hvr]; exact imax_ge_left 0 (gainFn r)
        · have := gain_dominates r vr hvr; have h0 := imax_ge_right 0 (gainFn r); omega
      have := solveFn_ge_through hm
      omega

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ pathSum`, pointwise in
    `Rel(Set)`, for every non-empty tree): `solveFn (node l a r)` is `some m` with `m` an achievable
    `pathSum` and `≤`-greatest among all achievable `pathSum`s. -/
theorem solve_correct (l r : Tree Int) (a : Int) :
    ∃ m, solveFn (Tree.node l a r) = some m ∧
      pathSum (Tree.node l a r) m ∧ ∀ v, pathSum (Tree.node l a r) v → v ≤ m := by
  rcases hbf : solveFn (Tree.node l a r) with _ | m
  · exact absurd hbf (solveFn_ne_none_of_node l r a)
  · exact ⟨m, rfl, best_achieves _ m hbf, fun v hv => best_dominates _ m v hbf hv⟩

/-! ## The morphism-equation headline: `solve = max D · Λspec` (§7.5 over `Option Int`)

  The maximization has answer type `Option Int` (`none` only for the empty tree, which has no
  path).  The preference order `dom` makes `none` the bottom, so `maxRel dom` returns `none`
  exactly when the achievable set is `{none}` (the empty tree) and the greatest achievable path sum
  otherwise.  The bridge `eq_A_comp_maxRel` (§8.1 thinning) then upgrades the pointwise
  achievability + domination facts to the actual morphism equation. -/

/-- The preference order on `Option Int`: `w` `dom`-dominates `z` (`w ≥ z`) with `none` as bottom.
    `some m ≥ some v ⟺ v ≤ m`; every answer dominates `none`; `none` dominates nothing but `none`. -/
def dom : dAns ⟶ dAns := fun w z =>
  match w, z with
  | _, none => True
  | none, some _ => False
  | some m, some v => v ≤ m

/-- `dom` is antisymmetric — the requirement that pins the maximum uniquely. -/
theorem dom_antisymm : ∀ w z : Option Int, dom w z → dom z w → w = z := by
  intro w z hwz hzw
  rcases w with _ | m <;> rcases z with _ | v
  · rfl
  · exact hwz.elim
  · exact hzw.elim
  · exact congrArg some (Int.le_antisymm hzw hwz)

/-- **The specification** as a morphism `dTree ℤ ⟶ dAns`: `some v` is achievable iff `v` is an
    actual `pathSum`; `none` is achievable iff the tree has NO path (the empty tree).  Stated
    independently of `solveFn`. -/
def spec : dTree Int ⟶ dAns := fun t o =>
  match o with
  | some v => pathSum t v
  | none => ∀ v, ¬ pathSum t v

/-- Soundness: `solveFn t` is always a `spec`-achievable answer. -/
theorem spec_sound : ∀ t : Tree Int, spec t (solveFn t) := by
  intro t
  cases t with
  | nil => intro v h; exact h
  | node l a r =>
    obtain ⟨m, hm, hach, _⟩ := solve_correct l r a
    show spec (Tree.node l a r) (solveFn (Tree.node l a r))
    rw [hm]; exact hach

/-- Domination: `solveFn t` `dom`-dominates every `spec`-achievable answer. -/
theorem spec_dom : ∀ (t : Tree Int) (o : Option Int), spec t o → dom (solveFn t) o := by
  intro t o ho
  cases o with
  | none => trivial
  | some v =>
    cases t with
    | nil => exact ho.elim
    | node l a r =>
      obtain ⟨m, hm, _, hdom⟩ := solve_correct l r a
      show dom (solveFn (Tree.node l a r)) (some v)
      rw [hm]; exact hdom v ho

/-- **The allegory-program headline (§7.5 `max D · Λspec`)**: `solve` is exactly the morphism
    `A spec ≫ maxRel dom` — the greatest achievable path sum (or `none` for the empty tree) — not
    merely pointwise.  Bridged from soundness + domination + antisymmetry via `eq_A_comp_maxRel`. -/
theorem solve_eq_maxRel : solve = Λ spec ≫ maxRel dom :=
  eq_Λ_comp_maxRel dom dom_antisymm solveFn spec spec_sound spec_dom

/-! ## Running the program -/

/-- A single-node tree labelled `a`. -/
def leaf (a : Int) : Tree Int := Tree.node Tree.nil a Tree.nil

example : solveFn (Tree.node (leaf 1) 2 (leaf 3)) = some 6 := by decide
example : solveFn (Tree.node (leaf (-10)) 2 (Tree.node (leaf 9) 20 (leaf 7))) = some 36 := by decide
example : solveFn (leaf (-3)) = some (-3) := by decide
example : solveFn (Tree.nil : Tree Int) = none := by decide

end Freyd.Alg.RelSet.LC124
