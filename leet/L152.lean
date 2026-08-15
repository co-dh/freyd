/-
  LeetCode 152 — Maximum Product Subarray — as an ALLEGORY PROGRAM.

  Problem: given a non-empty array of integers (possibly negative), find the maximum PRODUCT over
  all NON-EMPTY contiguous subarrays.  Unlike LeetCode 53 (sum), a negative element flips the sign
  of everything multiplied so far, so a large negative running product can become the best positive
  product after one more negative multiplicand.  The sweep must therefore track BOTH the running
  minimum and the running maximum product ending at the last element.

  Same recipe as `leet/L53.lean` (sum) and `leet/L121.lean` (see `Freyd/leetcode.md`, skill S0),
  with `*` in place of `+` and a two-sided (min, max) running state instead of one:

  1. **Data** — the array is the initial algebra `SnocList ℤ ℤ` of `F X = ℤ + X × ℤ`
     (`AOP.A6_SnocList`); `wrap x` is a single-element array, `snoc xs p` appends `p`.

  2. **Program** — the sweep is the fold with state `(minEnd, maxEnd, best)` and algebra
     `[ x ↦ (x,x,x),  ((m,M,b),p) ↦ (min(p,min(m*p,M*p)), max(p,max(m*p,M*p)), max(b, max(p,max(m*p,M*p)))) ]`.
     We package it as a `Map` `solve : Arr ⟶ ℤ` in `Rel(Set)` and prove it *is* the catamorphism of
     that algebra followed by the third projection (`solve_eq_cata`).

  3. **Specification** — two mutually-referencing relations: `suffixProd xs v` says `v` is the
     product of some non-empty SUFFIX of `xs` (a subarray ending at the last element); `subProd xs v`
     says `v` is the product of ANY non-empty contiguous subarray of `xs` — either a subarray of the
     prefix, or a suffix.  `spec = subProd` is the transpose `Λ⁻¹ spec`, and LeetCode 152 asks for its
     `≤`-maximum, `max (≤) · Λ spec`.

  4. **Correctness** — `solve` computes exactly that maximum: it returns an achievable subarray
     product (`solve_sub`, giving `solve ⊑ spec`) and dominates every achievable subarray product
     (`subProd_le_solve`).  Together (`solve_correct`) this is `solve = max (≤) · Λ spec`.

     The one genuinely new step (absent from L53/L121, since `+` is monotone but `*` is not) is the
     `snoc` case of domination: given an old suffix product `v` with `m ≤ v ≤ M`, the new candidate
     suffix products are `p` and `v*p`, and `v*p` must be sandwiched between the new `lo`/`hi`.  This
     needs a sign split on `p` (`mul_between`): multiplication by a nonnegative `p` is monotone,
     multiplication by a nonpositive `p` is antitone (Lean core already has both one-sided
     `Int.mul_le_mul_of_nonneg_right`/`Int.mul_le_mul_of_nonpos_right`, so no local arithmetic helper
     is needed).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import AOP.A7_4_Horner
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC152

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

/-- The one genuinely nonlinear fact: if `v` is sandwiched between `m` and `M`, then `v*p` is
    sandwiched between `imin (m*p) (M*p)` and `imax (m*p) (M*p)` — for EITHER sign of `p`.
    `omega` cannot see `v*p` (nonlinear), so we split on the sign of `p` and use that multiplication
    by a nonnegative is monotone, by a nonpositive is antitone (both already in Lean core). -/
theorem mul_between (m v M p : Int) (h : m ≤ v ∧ v ≤ M) :
    imin (m*p) (M*p) ≤ v*p ∧ v*p ≤ imax (m*p) (M*p) := by
  rcases Int.le_total 0 p with hp | hp
  · exact ⟨Int.le_trans (imin_le_left (m*p) (M*p)) (Int.mul_le_mul_of_nonneg_right h.1 hp),
      Int.le_trans (Int.mul_le_mul_of_nonneg_right h.2 hp) (imax_ge_right (m*p) (M*p))⟩
  · exact ⟨Int.le_trans (imin_le_right (m*p) (M*p)) (Int.mul_le_mul_of_nonpos_right h.2 hp),
      Int.le_trans (Int.mul_le_mul_of_nonpos_right h.1 hp) (imax_ge_left (m*p) (M*p))⟩

/-! ## Data: arrays as a non-empty snoc-list of integers -/

/-- The object of arrays in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = single element, `snoc xs p` =
    `xs` with a new final element `p`). -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The object of integers (subarray products) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The program: the fold, state `(minEnd, maxEnd, best)` -/

/-- The fold algebra
    `[ x ↦ (x,x,x),  ((m,M,b),p) ↦ (min(p,min(m·p,M·p)), max(p,max(m·p,M·p)), max(b,hi)) ]
    : F(ℤ×ℤ×ℤ) → ℤ×ℤ×ℤ`. -/
def algFn : (Fobj Int Int (⟨Int × Int × Int⟩ : RelSet.{0})).carrier → (Int × Int × Int)
  | Sum.inl x => (x, x, x)
  | Sum.inr (st, p) =>
    let m := st.1; let M := st.2.1; let b := st.2.2
    let lo := imin p (imin (m*p) (M*p))
    let hi := imax p (imax (m*p) (M*p))
    (lo, hi, imax b hi)

/-- The algebra as a morphism (a `Map`) `F(ℤ×ℤ×ℤ) ⟶ ℤ×ℤ×ℤ` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨Int × Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int × Int⟩ : RelSet.{0}) :=
  graph algFn

/-- The concrete fold (structural recursion), returning `(minEnd, maxEnd, best)`. -/
def foldFn : SnocList Int Int → Int × Int × Int
  | SnocList.wrap x => (x, x, x)
  | SnocList.snoc xs p =>
    let m := (foldFn xs).1; let M := (foldFn xs).2.1; let b := (foldFn xs).2.2
    let lo := imin p (imin (m*p) (M*p))
    let hi := imax p (imax (m*p) (M*p))
    (lo, hi, imax b hi)

/-- The answer: the third component (best subarray product) of the fold. -/
def solveFn (xs : SnocList Int Int) : Int := (foldFn xs).2.2

/-- **The allegory program**: LeetCode 152's solution as a morphism `Arr ⟶ ℤ` in `Rel(Set)`. -/
def solve : Arr ⟶ dZ := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Int Int) (r : Int × Int × Int),
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

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · thd`, a fold followed by the
    projection onto `best`. -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (fun st : Int × Int × Int => st.2.2) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## Specification: the maximum achievable subarray product -/

/-- `suffixProd xs v` — `v` is the product of some non-empty SUFFIX of `xs` (a subarray ending at
    the last element). -/
def suffixProd : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => v = p ∨ ∃ v', suffixProd xs v' ∧ v = v' * p

/-- `subProd xs v` — `v` is the product of SOME non-empty contiguous subarray of `xs`: either a
    subarray entirely within the prefix, or a suffix (ending at the last element). -/
def subProd : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => subProd xs v ∨ suffixProd (SnocList.snoc xs p) v

/-- The **specification** as a morphism `Arr ⟶ ℤ` in `Rel(Set)`: the relation of achievable
    subarray products.  LeetCode 152 asks for its `≤`-maximum, `max (≤) · Λ spec`. -/
def spec : Arr ⟶ dZ := fun xs v => subProd xs v

/-! ## The sandwich invariant: `(minEnd, maxEnd)` bound every suffix product -/

/-- **Domination**: every suffix product lies between `minEnd` and `maxEnd`.  The `snoc` step is the
    crux — it is where `mul_between`'s sign split on `p` is used. -/
theorem foldFn_dominates : ∀ (xs : SnocList Int Int) (v : Int),
    suffixProd xs v → (foldFn xs).1 ≤ v ∧ v ≤ (foldFn xs).2.1 := by
  intro xs; induction xs with
  | wrap x =>
    intro v h; simp only [suffixProd] at h
    exact ⟨h ▸ Int.le_refl x, h ▸ Int.le_refl x⟩
  | snoc xs p ih =>
    intro v h; simp only [suffixProd] at h
    show imin p (imin ((foldFn xs).1*p) ((foldFn xs).2.1*p)) ≤ v ∧
         v ≤ imax p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p))
    cases h with
    | inl hp =>
      rw [hp]
      exact ⟨imin_le_left p (imin ((foldFn xs).1*p) ((foldFn xs).2.1*p)),
             imax_ge_left p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p))⟩
    | inr h =>
      obtain ⟨v', hv', hv⟩ := h; subst hv
      have hmul := mul_between (foldFn xs).1 v' (foldFn xs).2.1 p (ih v' hv')
      exact ⟨Int.le_trans (imin_le_right p (imin ((foldFn xs).1*p) ((foldFn xs).2.1*p))) hmul.1,
             Int.le_trans hmul.2 (imax_ge_right p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p)))⟩

/-- **Achievability**: both `minEnd` and `maxEnd` are themselves suffix products. -/
theorem foldFn_achievable : ∀ xs, suffixProd xs (foldFn xs).1 ∧ suffixProd xs (foldFn xs).2.1 := by
  intro xs; induction xs with
  | wrap x => exact ⟨rfl, rfl⟩
  | snoc xs p ih =>
    obtain ⟨ihlo, ihhi⟩ := ih
    refine ⟨?_, ?_⟩
    · show suffixProd (SnocList.snoc xs p) (imin p (imin ((foldFn xs).1*p) ((foldFn xs).2.1*p)))
      simp only [suffixProd]
      cases imin_eq_or p (imin ((foldFn xs).1*p) ((foldFn xs).2.1*p)) with
      | inl he => exact Or.inl he
      | inr he =>
        rw [he]
        cases imin_eq_or ((foldFn xs).1*p) ((foldFn xs).2.1*p) with
        | inl he2 => exact Or.inr ⟨(foldFn xs).1, ihlo, he2⟩
        | inr he2 => exact Or.inr ⟨(foldFn xs).2.1, ihhi, he2⟩
    · show suffixProd (SnocList.snoc xs p) (imax p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p)))
      simp only [suffixProd]
      cases imax_eq_or p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p)) with
      | inl he => exact Or.inl he
      | inr he =>
        rw [he]
        cases imax_eq_or ((foldFn xs).1*p) ((foldFn xs).2.1*p) with
        | inl he2 => exact Or.inr ⟨(foldFn xs).1, ihlo, he2⟩
        | inr he2 => exact Or.inr ⟨(foldFn xs).2.1, ihhi, he2⟩

/-! ## Correctness: `solve` computes the maximum achievable subarray product -/

/-- `solve` dominates every achievable subarray product. -/
theorem subProd_le_solve : ∀ (xs : SnocList Int Int) (v : Int), subProd xs v → v ≤ solveFn xs := by
  intro xs; induction xs with
  | wrap x =>
    intro v h; simp only [subProd] at h
    show v ≤ x
    omega
  | snoc xs p ih =>
    intro v h; simp only [subProd] at h
    show v ≤ imax (foldFn xs).2.2 (imax p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p)))
    have hge1 := imax_ge_left (foldFn xs).2.2 (imax p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p)))
    cases h with
    | inl hp =>
      have hle : v ≤ (foldFn xs).2.2 := ih v hp
      omega
    | inr hp =>
      have hb : v ≤ imax p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p)) :=
        (foldFn_dominates (SnocList.snoc xs p) v hp).2
      have hge2 := imax_ge_right (foldFn xs).2.2 (imax p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p)))
      omega

/-- `solve`'s output is an achievable subarray product — hence `solve ⊑ spec`. -/
theorem solve_sub : ∀ xs, subProd xs (solveFn xs) := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih =>
    show subProd (SnocList.snoc xs p)
      (imax (foldFn xs).2.2 (imax p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p))))
    simp only [subProd]
    have ihs : subProd xs (foldFn xs).2.2 := ih
    cases imax_eq_or (foldFn xs).2.2 (imax p (imax ((foldFn xs).1*p) ((foldFn xs).2.1*p))) with
    | inl he => rw [he]; exact Or.inl ihs
    | inr he => rw [he]; exact Or.inr (foldFn_achievable (SnocList.snoc xs p)).2

/-- **The program refines the specification**: every value `solve` returns is an achievable
    subarray product. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact solve_sub xs

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ subProd`, pointwise in
    `Rel(Set)`): `solve xs` is an achievable subarray product and is `≤`-greatest among all
    achievable subarray products. -/
theorem solve_correct (xs : SnocList Int Int) :
    subProd xs (solveFn xs) ∧ ∀ v, subProd xs v → v ≤ solveFn xs :=
  ⟨solve_sub xs, subProd_le_solve xs⟩

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `solve` is exactly the morphism `A spec ≫ maxRel D`
    for the `≤`-preference order `D w z := z ≤ w` — not merely pointwise. Bridged from `solve_correct`. -/
theorem solve_eq_maxRel : solve = Λ spec ≫ maxRel (fun w z : Int => z ≤ w) :=
  eq_Λ_comp_maxRel _ (fun x y h1 h2 => Int.le_antisymm h2 h1) solveFn spec
    (fun xs => (solve_correct xs).1) (fun xs v hv => (solve_correct xs).2 v hv)

/-! ## Running the program -/

/-- Build an array from a first element and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 2 [3, -2, 4]) = 6 := by decide
example : solveFn (ofList (-2) [0, -1]) = 0 := by decide
example : solveFn (ofList (-2) [3, -4]) = 24 := by decide
example : solveFn (ofList (-2) []) = -2 := by decide

end Freyd.Alg.RelSet.LC152
