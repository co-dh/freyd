/-
  LeetCode 198 — House Robber — as an ALLEGORY PROGRAM.

  Problem: given a non-empty array of house values `x₀,…,x_{n-1}` (any `Int`, positive or
  negative), choose a subset of houses with NO TWO ADJACENT indices, maximising the sum of the
  chosen values.  Robbing nothing (the empty selection, sum `0`) is always allowed.

  Same recipe as `leet/L53.lean` / `leet/L121.lean` (see `Freyd/leetcode.md`, skill S0/S1):

  1. **Data** — the array is the initial algebra `SnocList ℤ ℤ` of `F X = ℤ + X × ℤ`
     (`AOP.A6_SnocList`); `wrap x` is a single house, `snoc xs p` appends a house.

  2. **Program** — the classic House-Robber DP is the fold with state `(best, prevBest)`:
     `best` = the optimal robbery of the whole (sub)list, `prevBest` = the optimal robbery of the
     same (sub)list with its LAST house forbidden.  Algebra
     `[ x ↦ (max x 0, 0),  ((best,prevBest),p) ↦ (max best (prevBest+p), best) ]`.  We package it
     as a `Map` `solve : Arr ⟶ ℤ` in `Rel(Set)` and prove it *is* the catamorphism of that algebra
     followed by the FIRST projection (`solve_eq_cata`).

  3. **Specification** — two mutually-referencing relations, split by "is the last house taken?":
     `robF xs v` — `v` is achievable WITHOUT taking `xs`'s last house; `robT xs v` — `v` is
     achievable BY taking `xs`'s last house (so the predecessor's last house must be free, i.e.
     the rest is a `robF`-selection).  `robSpec = robF ∨ robT` is the relation of ALL achievable
     robberies.  LeetCode 198 asks for its `≤`-maximum, `max (≤) · Λ robSpec`.

  4. **Correctness** — `solve` computes exactly that maximum: it returns an achievable robbery
     (part of `solve_correct`, giving `solve ⊑ spec`) and dominates every achievable robbery (the
     other part).  Together this is `solve = max (≤) · Λ robSpec`, evaluated pointwise in the Set
     model.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import AOP.A7_4_Horner
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC198

open Freyd Freyd.Alg.RelSet.SL

/-! ## Integer `min`/`max` (mathlib-free, so we control the rewrite lemmas) -/

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

/-! ## Data: houses as a non-empty snoc-list of integers -/

/-- The object of house arrays in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = single house, `snoc xs p`
    = `xs` with a new final house `p`). -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The object of integers (robbery totals) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The program: the DP fold, state `(best, prevBest)` -/

/-- The fold algebra `[ x ↦ (max x 0, 0),  ((best,prevBest),p) ↦ (max best (prevBest+p), best) ]
    : F(ℤ×ℤ) → ℤ×ℤ`. -/
def algFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int)
  | Sum.inl x => (imax x 0, 0)
  | Sum.inr (st, p) => (imax st.1 (st.2 + p), st.1)

/-- The algebra as a morphism (a `Map`) `F(ℤ×ℤ) ⟶ ℤ×ℤ` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion), returning `(best, prevBest)`. -/
def foldFn : SnocList Int Int → Int × Int
  | SnocList.wrap x => (imax x 0, 0)
  | SnocList.snoc xs p => (imax (foldFn xs).1 ((foldFn xs).2 + p), (foldFn xs).1)

/-- The answer: the first fold component (the best whole-list robbery). -/
def solveFn (xs : SnocList Int Int) : Int := (foldFn xs).1

/-- **The allegory program**: LeetCode 198's solution as a morphism `Arr ⟶ ℤ` in `Rel(Set)`. -/
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

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · fst`, a fold followed by the
    projection onto `best`. -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (Prod.fst : Int × Int → Int) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## Specification: the maximum achievable robbery -/

/- `robF`/`robT` — split by "is the last house taken?"  `robF xs v`: `v` is achievable WITHOUT
   taking `xs`'s last house (any selection of `xs`, taking or skipping ITS OWN last house).
   `robT xs v`: `v` is achievable BY taking `xs`'s last house (so the rest of `xs` must not take
   its own last house — a `robF`-selection of `xs`). -/
mutual
def robF : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = 0
  | SnocList.snoc xs p => fun v => robF xs v ∨ robT xs v

def robT : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => ∃ v', robF xs v' ∧ v = v' + p
end

/-- `robSpec xs v` — `v` is SOME achievable robbery of `xs` (taking or not taking the last house). -/
def robSpec (xs : SnocList Int Int) (v : Int) : Prop := robF xs v ∨ robT xs v

/-- The **specification** as a morphism `Arr ⟶ ℤ` in `Rel(Set)`: the relation of achievable
    robberies.  LeetCode 198 asks for its `≤`-maximum, i.e. `solve = max (≤) · Λ spec` pointwise in
    `Rel(Set)` (`solve_correct` below). -/
def spec : Arr ⟶ dZ := fun xs v => robSpec xs v

/-! ## Invariants of the fold, proved TOGETHER by simultaneous induction -/

/-- The fold dominates both layers of the spec: `best` dominates every achievable robbery, and
    `prevBest` dominates every achievable robbery that skips the last house. -/
theorem foldFn_dominates : ∀ xs : SnocList Int Int,
    (∀ v, robSpec xs v → v ≤ (foldFn xs).1) ∧ (∀ v, robF xs v → v ≤ (foldFn xs).2) := by
  intro xs; induction xs with
  | wrap x =>
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show v ≤ imax x 0
      have h1 := imax_ge_left x 0; have h2 := imax_ge_right x 0
      cases h with
      | inl h => have hv : v = 0 := h; omega
      | inr h => have hv : v = x := h; omega
    · have hv : v = 0 := h
      show v ≤ (0 : Int); omega
  | snoc xs p ih =>
    obtain ⟨ihFst, ihSnd⟩ := ih
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show v ≤ imax (foldFn xs).1 ((foldFn xs).2 + p)
      have h1 := imax_ge_left (foldFn xs).1 ((foldFn xs).2 + p)
      have h2 := imax_ge_right (foldFn xs).1 ((foldFn xs).2 + p)
      cases h with
      | inl h => have := ihFst v h; omega
      | inr h => obtain ⟨v', hv', hv⟩ := h; have := ihSnd v' hv'; omega
    · show v ≤ (foldFn xs).1
      exact ihFst v h

/-- The fold is itself achievable in both layers: `best` is an achievable robbery, `prevBest` is
    an achievable robbery that skips the last house. -/
theorem foldFn_is_rob : ∀ xs : SnocList Int Int,
    robSpec xs (foldFn xs).1 ∧ robF xs (foldFn xs).2 := by
  intro xs; induction xs with
  | wrap x =>
    refine ⟨?_, ?_⟩
    · show robSpec (SnocList.wrap x) (imax x 0)
      cases imax_eq_or x 0 with
      | inl he => exact Or.inr he
      | inr he => exact Or.inl he
    · show robF (SnocList.wrap x) 0
      rfl
  | snoc xs p ih =>
    obtain ⟨ihFst, ihSnd⟩ := ih
    refine ⟨?_, ?_⟩
    · show robSpec (SnocList.snoc xs p) (imax (foldFn xs).1 ((foldFn xs).2 + p))
      cases imax_eq_or (foldFn xs).1 ((foldFn xs).2 + p) with
      | inl he => rw [he]; exact Or.inl ihFst
      | inr he => rw [he]; exact Or.inr ⟨(foldFn xs).2, ihSnd, rfl⟩
    · show robF (SnocList.snoc xs p) (foldFn xs).1
      exact ihFst

/-! ## Correctness: `solve` computes the maximum achievable robbery -/

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ robSpec`, pointwise in
    `Rel(Set)`): `solve xs` is an achievable robbery and is `≤`-greatest among all achievable
    robberies. -/
theorem solve_correct (xs : SnocList Int Int) :
    robSpec xs (solveFn xs) ∧ ∀ v, robSpec xs v → v ≤ solveFn xs :=
  ⟨(foldFn_is_rob xs).1, (foldFn_dominates xs).1⟩

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `solve` is exactly the morphism `Λ spec ≫ maxRel D`
    for the `≤`-preference order `D w z := z ≤ w` — not merely pointwise. Bridged from `solve_correct`. -/
theorem solve_eq_maxRel : solve = Λ spec ≫ maxRel (fun w z : Int => z ≤ w) :=
  eq_Λ_comp_maxRel _ (fun x y h1 h2 => Int.le_antisymm h2 h1) solveFn spec
    (fun xs => (solve_correct xs).1) (fun xs v hv => (solve_correct xs).2 v hv)

/-- **The program refines the specification**: every value `solve` returns is an achievable
    robbery. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact (solve_correct xs).1

/-! ## Running the program -/

/-- Build a house array from a first value and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 1 [2, 3, 1]) = 4 := by decide
example : solveFn (ofList 2 [7, 9, 3, 1]) = 12 := by decide
example : solveFn (ofList 5 []) = 5 := by decide
example : solveFn (ofList (-3) [-1]) = 0 := by decide

end Freyd.Alg.RelSet.LC198
