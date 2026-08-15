/-
  LeetCode 746 — Min Cost Climbing Stairs — as an ALLEGORY PROGRAM.

  Problem: given a non-empty array of step costs `cost[0],…,cost[n-1]`, you may start the climb at
  index 0 or index 1 (landing on either is free of any *entry* cost beyond the step's own cost),
  and from any step you may climb 1 or 2 steps. The goal is the minimum total cost of some valid
  climb that lands PAST the last step (index `n`). `minCost[i]` = cheapest cost to STAND ON step
  `i` = `cost[i] + min(minCost[i-1], minCost[i-2])`, seeded by `minCost[0] = cost[0]` and a free
  virtual pad `minCost[-1] = 0` BEFORE the array (encoding "start at index 1 for free"). Answer =
  `min(minCost[n-1], minCost[n-2])` — you may step off from either of the last two steps.

  Same recipe as `leet/L198.lean` (see `Freyd/leetcode.md`, skill S4), the paired-state DP
  template FLIPPED to `min`:

  1. **Data** — `SnocList ℤ ℤ` (`AOP.A6_SnocList`); `wrap x` = a single step of cost `x`, `snoc
     xs p` appends a step of cost `p`.

  2. **Program** — the fold state `(reachHere, reachPrev)` = (cheapest cost to stand on the LAST
     processed step, cheapest cost to stand on the one BEFORE it). Algebra
     `[ x ↦ (x, 0), ((reachHere,reachPrev),p) ↦ (p + min reachHere reachPrev, reachHere) ]`.
     `solveFn xs = min (foldFn xs).1 (foldFn xs).2` (step off from either of the last two steps).

  3. **Specification** — two mutually-referencing relations, split by "does the climb land ON
     `xs`'s last step, or the one before it?": `costHere xs v` — `v` is the cost of a valid climb
     landing on `xs`'s last step; `costPrev xs v` — `v` is the cost of a valid climb landing on the
     step BEFORE `xs`'s last step (for a singleton `xs` this is the free virtual pad, `v = 0`).
     `costOf xs v = costHere xs v ∨ costPrev xs v` is the relation of ALL achievable "land near the
     end" costs. LeetCode 746 asks for its `≤`-MINIMUM, `min (≤) · Λ costOf`.

  4. **Correctness** — `solve` computes exactly that minimum: it returns an achievable cost (part
     of `solve_correct`, giving `solve ⊑ spec`) and is `≤` every achievable cost (the other part —
     domination flips to `≤`, mirroring `L198`'s `≥` for `max`). Together this is `solve = min (≤)
     · Λ costOf`, evaluated pointwise in the Set model.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import AOP.A7_4_Horner
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC746

open Freyd Freyd.Alg.RelSet.SL

/-! ## Integer `min` (mathlib-free, so we control the rewrite lemmas) -/

def imin (a b : Int) : Int := if a ≤ b then a else b

theorem imin_le_left  (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
theorem imin_eq_or (a b : Int) : imin a b = a ∨ imin a b = b := by
  unfold imin; split; exacts [Or.inl rfl, Or.inr rfl]

/-! ## Data: step costs as a non-empty snoc-list of integers -/

/-- The object of step-cost arrays in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = a single step of
    cost `x`, `snoc xs p` = `xs` with a new final step of cost `p`). -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The object of integers (climb totals) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The program: the DP fold, state `(reachHere, reachPrev)` -/

/-- The fold algebra `[ x ↦ (x, 0),  ((reachHere,reachPrev),p) ↦ (p + min reachHere reachPrev,
    reachHere) ] : F(ℤ×ℤ) → ℤ×ℤ`. -/
def algFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int)
  | Sum.inl x => (x, 0)
  | Sum.inr (st, p) => (p + imin st.1 st.2, st.1)

/-- The algebra as a morphism (a `Map`) `F(ℤ×ℤ) ⟶ ℤ×ℤ` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion), returning `(reachHere, reachPrev)`. -/
def foldFn : SnocList Int Int → Int × Int
  | SnocList.wrap x => (x, 0)
  | SnocList.snoc xs p => (p + imin (foldFn xs).1 (foldFn xs).2, (foldFn xs).1)

/-- The answer: the cheaper of the two fold components (step off from either of the last two
    steps). -/
def solveFn (xs : SnocList Int Int) : Int := imin (foldFn xs).1 (foldFn xs).2

/-- **The allegory program**: LeetCode 746's solution as a morphism `Arr ⟶ ℤ` in `Rel(Set)`. -/
def solve : Arr ⟶ dZ := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Int Int) (r : Int × Int),
    cataFold alg xs r ↔ r = foldFn xs := by
  intro xs; induction xs with
  | wrap x => intro r; exact Iff.rfl
  | snoc xs p ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨foldFn xs, (ih (foldFn xs)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · (uncurry min)`, a fold followed
    by taking the `min` of the two carried components. -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (fun p : Int × Int => imin p.1 p.2) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## Specification: the minimum achievable near-end landing cost -/

/- `costHere`/`costPrev` — split by "does the climb land on the LAST step of `xs`, or the one
   before it?"  `costHere xs v`: `v` is the cost of a valid climb landing on `xs`'s last step
   (reached by a 1- or 2-step hop from a climb landing on the last, resp. second-to-last, step of
   the shorter prefix). `costPrev xs v`: `v` is the cost of a valid climb landing on the step
   BEFORE `xs`'s last step — for a singleton `xs` there is no such step, so this is the free
   virtual pad before the array (`v = 0`, encoding "start at index 1"); otherwise it is exactly a
   `costHere`-climb of the shorter prefix. -/
mutual
def costHere : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => ∃ v', (costHere xs v' ∨ costPrev xs v') ∧ v = v' + p

def costPrev : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = 0
  | SnocList.snoc xs p => fun v => costHere xs v
end

/-- `costOf xs v` — `v` is SOME achievable "land near the end" cost of `xs` (landing on the last
    step or the one before it). -/
def costOf (xs : SnocList Int Int) (v : Int) : Prop := costHere xs v ∨ costPrev xs v

/-- The **specification** as a morphism `Arr ⟶ ℤ` in `Rel(Set)`: the relation of achievable
    near-end landing costs. LeetCode 746 asks for its `≤`-minimum, i.e. `solve = min (≤) · Λ
    costOf` pointwise in `Rel(Set)` (`solve_correct` below). -/
def spec : Arr ⟶ dZ := fun xs v => costOf xs v

/-! ## Invariants of the fold, proved TOGETHER by simultaneous induction -/

/-- The fold is dominated BY (`≤`) both layers of the spec: `reachHere` is `≤` every achievable
    "land on the last step" cost, and `reachPrev` is `≤` every achievable "land on the step before"
    cost. -/
theorem foldFn_dominates : ∀ xs : SnocList Int Int,
    (∀ v, costHere xs v → (foldFn xs).1 ≤ v) ∧ (∀ v, costPrev xs v → (foldFn xs).2 ≤ v) := by
  intro xs; induction xs with
  | wrap x =>
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show (x : Int) ≤ v
      have hv : v = x := h; omega
    · show (0 : Int) ≤ v
      have hv : v = 0 := h; omega
  | snoc xs p ih =>
    obtain ⟨ihFst, ihSnd⟩ := ih
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show p + imin (foldFn xs).1 (foldFn xs).2 ≤ v
      obtain ⟨v', hv', hv⟩ := h
      have h1 := imin_le_left (foldFn xs).1 (foldFn xs).2
      have h2 := imin_le_right (foldFn xs).1 (foldFn xs).2
      cases hv' with
      | inl hv' => have := ihFst v' hv'; omega
      | inr hv' => have := ihSnd v' hv'; omega
    · show (foldFn xs).1 ≤ v
      exact ihFst v h

/-- The fold is itself achievable in both layers: `reachHere` is an achievable "land on the last
    step" cost, `reachPrev` is an achievable "land on the step before" cost. -/
theorem foldFn_is_cost : ∀ xs : SnocList Int Int,
    costHere xs (foldFn xs).1 ∧ costPrev xs (foldFn xs).2 := by
  intro xs; induction xs with
  | wrap x =>
    refine ⟨?_, ?_⟩
    · show costHere (SnocList.wrap x) x
      rfl
    · show costPrev (SnocList.wrap x) 0
      rfl
  | snoc xs p ih =>
    obtain ⟨ihFst, ihSnd⟩ := ih
    refine ⟨?_, ?_⟩
    · show costHere (SnocList.snoc xs p) (p + imin (foldFn xs).1 (foldFn xs).2)
      cases imin_eq_or (foldFn xs).1 (foldFn xs).2 with
      | inl he => exact ⟨(foldFn xs).1, Or.inl ihFst, by omega⟩
      | inr he => exact ⟨(foldFn xs).2, Or.inr ihSnd, by omega⟩
    · show costPrev (SnocList.snoc xs p) (foldFn xs).1
      exact ihFst

/-! ## Correctness: `solve` computes the minimum achievable near-end landing cost -/

/-- **Correctness of the allegory program** (`solve = min (≤) · Λ costOf`, pointwise in
    `Rel(Set)`): `solve xs` is an achievable near-end landing cost and is `≤`-least among all
    achievable such costs. -/
theorem solve_correct (xs : SnocList Int Int) :
    costOf xs (solveFn xs) ∧ ∀ v, costOf xs v → solveFn xs ≤ v := by
  constructor
  · show costHere xs (imin (foldFn xs).1 (foldFn xs).2) ∨ costPrev xs (imin (foldFn xs).1 (foldFn xs).2)
    rcases imin_eq_or (foldFn xs).1 (foldFn xs).2 with he | he
    · rw [he]; exact Or.inl (foldFn_is_cost xs).1
    · rw [he]; exact Or.inr (foldFn_is_cost xs).2
  · intro v hv
    show imin (foldFn xs).1 (foldFn xs).2 ≤ v
    have h1 := imin_le_left (foldFn xs).1 (foldFn xs).2
    have h2 := imin_le_right (foldFn xs).1 (foldFn xs).2
    cases hv with
    | inl hv => have := (foldFn_dominates xs).1 v hv; omega
    | inr hv => have := (foldFn_dominates xs).2 v hv; omega

/-- **Honest headline (§7.5 `min (≤)·Λ spec`)**: `solve` is exactly the morphism `A spec ≫ maxRel D`
    for `D w z := w ≤ z` — `maxRel` of the reversed "smaller-is-better" order is the `≤`-MINIMUM
    (`minRel (≤)`) — not merely pointwise. Bridged from `solve_correct`. -/
theorem solve_eq_maxRel : solve = A spec ≫ maxRel (fun w z : Int => w ≤ z) :=
  eq_Λ_comp_maxRel _ (fun x y h1 h2 => Int.le_antisymm h1 h2) solveFn spec
    (fun xs => (solve_correct xs).1) (fun xs v hv => (solve_correct xs).2 v hv)

/-- **The program refines the specification**: every value `solve` returns is an achievable
    near-end landing cost. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact (solve_correct xs).1

/-! ## Running the program -/

/-- Build a step-cost array from a first value and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 10 [15, 20]) = 15 := by decide
example : solveFn (ofList 1 [100, 1, 1, 1, 100, 1, 1, 100, 1]) = 6 := by decide
example : solveFn (ofList 0 [0]) = 0 := by decide
example : solveFn (ofList 5 []) = 0 := by decide

end Freyd.Alg.RelSet.LC746
