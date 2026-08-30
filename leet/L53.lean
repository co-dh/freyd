/-
  LeetCode 53 — Maximum Subarray (Kadane's algorithm) — as an ALLEGORY PROGRAM,
  derived through the generic running-best driver `rel.AutoDerive`.

  Problem: given a non-empty array of integers `x₀,…,x_{n-1}` (possibly negative), find the maximum
  sum over all NON-EMPTY contiguous subarrays.  (The empty subarray is not allowed, so an
  all-negative array's answer is its largest single element.)

  Same recipe as `leet/L121.lean`:

  1. **Data** — the array is the initial algebra `SnocList ℤ ℤ` of `F X = ℤ + X × ℤ`
     (`AOP.A6_SnocList`); `wrap x` is a single-element array, `snoc xs p` appends `p`.

  2. **Program** — Kadane's sweep is the fold with state `(bestEndingHere, bestSoFar)` and algebra
     `[ x ↦ (x,x),  ((e,b),p) ↦ (max p (e+p), max b (max p (e+p))) ]`.  We package it as a `Map`
     `solve : Arr ⟶ ℤ` in `Rel(Set)` and prove it *is* the catamorphism of that algebra followed by
     the second projection (`solve_eq_cata`).

  3. **Specification** — two mutually-referencing relations: `suffixSum xs v` says `v` is the sum of
     some non-empty SUFFIX of `xs` (a subarray ending at the last element); `subSum xs v` says `v` is
     the sum of ANY non-empty contiguous subarray of `xs` — either a subarray of the prefix, or a
     suffix.  `spec = subSum` is the transpose `Λ⁻¹ spec`, and LeetCode 53 asks for its `≤`-maximum,
     `max (≤) · Λ spec`.

  4. **Correctness** — `solve` computes exactly that maximum (`solve_correct`, `solve_eq_est`).
     Every relational side condition of the greedy derivation (`prodDom_trans`, `alg_mono`,
     `alg_le_gen`, `gen_recip_alg_le`, `alg_ref`, `cataFold_alg`, `gen_total` — formerly ~104
     hand-written lines here) is discharged by the `RunningBest` driver from the bundle `kadane`
     below; this file supplies only the CREATIVE content: the bundle's fields and the
     generator-vs-spec characterisation (`gen_sound`/`diag_gen`/`spec_gen`), the genuinely
     problem-specific inductions saying the search space is exactly the set of subarray sums.

  Mathlib-free.  Axioms of the headline: {propext, Classical.choice, Quot.sound} — the
  `Classical.choice` is the honest cost of the relational-catamorphism universal property,
  inherited via `cataR_eq_relCata`.
-/
import rel.AutoDerive

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC53

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: arrays as a non-empty snoc-list of integers -/

/-- The object of arrays in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = single element, `snoc xs p` =
    `xs` with a new final element `p`). -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The object of integers (subarray sums) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The creative bundle — the whole algorithmic content of Kadane -/

/-- Kadane's derivation bundle.  State `(bestEndingHere, bestSoFar)`: the new suffix is `p` or
    `e + p` (candidates), deterministically their max; the new best is kept or reset to the
    chosen new suffix, deterministically the max; Pareto dominance is `≥` in both coordinates. -/
def kadane : RunningBest Int Int Int where
  base x := (x, x)
  step1 e p := imax p (e + p)
  step2 e b p := imax b (imax p (e + p))
  cand1 e p w1 := w1 = p ∨ w1 = e + p
  cand2 _ b _ w1 w2 := w2 = b ∨ w2 = w1
  ord e e' := e' ≤ e
  ord_refl e := Int.le_refl e
  ord_trans h1 h2 := Int.le_trans h2 h1
  step1_mono p h := imax_mono (Int.le_refl p) (by omega)
  step2_mono p h1 h2 := imax_mono h2 (imax_mono (Int.le_refl p) (by omega))
  step1_cand e p := imax_eq_or p (e + p)
  step2_cand e b p := imax_eq_or b (imax p (e + p))
  cand1_le h := by
    rcases h with h | h <;> rw [h]
    · exact imax_ge_left _ _
    · exact imax_ge_right _ _
  cand2_le h1 h2 := by
    rcases h2 with h | h <;> rw [h]
    · exact imax_ge_left _ _
    · rcases h1 with h1 | h1 <;> rw [h1]
      · exact Int.le_trans (imax_ge_left _ _) (imax_ge_right _ _)
      · exact Int.le_trans (imax_ge_right _ _) (imax_ge_right _ _)

/-! ## The program: Kadane's fold, state `(bestEndingHere, bestSoFar)` -/

/-- The fold algebra `[ x ↦ (x,x),  ((e,b),p) ↦ (max p (e+p), max b (max p (e+p))) ] : F(ℤ×ℤ) → ℤ×ℤ`. -/
def algFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int)
  | Sum.inl x => (x, x)
  | Sum.inr (st, p) => let e := imax p (st.1 + p); (e, imax st.2 e)

/-- The algebra as a morphism (a `Map`) `F(ℤ×ℤ) ⟶ ℤ×ℤ` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion), returning `(bestEndingHere, bestSoFar)`. -/
def foldFn : SnocList Int Int → Int × Int
  | SnocList.wrap x => (x, x)
  | SnocList.snoc xs p => let e := imax p ((foldFn xs).1 + p); (e, imax (foldFn xs).2 e)

/-- The answer: the second component (best subarray sum) of the fold. -/
def solveFn (xs : SnocList Int Int) : Int := (foldFn xs).2

/-- **The allegory program**: LeetCode 53's solution as a morphism `Arr ⟶ ℤ` in `Rel(Set)`. -/
def solve : Arr ⟶ dZ := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## The program IS the bundle's — three definitional bridges -/

/-- The file's algebra is the bundle's. -/
theorem algFn_eq : algFn = kadane.algFn := by
  funext u
  cases u with
  | inl x => rfl
  | inr q => obtain ⟨st, p⟩ := q; rfl

/-- The file's fold is the bundle's. -/
theorem foldFn_eq : ∀ xs, foldFn xs = kadane.foldFn xs := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih =>
    show (imax p ((foldFn xs).1 + p), imax (foldFn xs).2 (imax p ((foldFn xs).1 + p)))
        = (imax p ((kadane.foldFn xs).1 + p),
           imax (kadane.foldFn xs).2 (imax p ((kadane.foldFn xs).1 + p)))
    rw [ih]

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree (driver's `cataFold_alg`). -/
theorem cataFold_alg : ∀ (xs : SnocList Int Int) (r : Int × Int),
    cataFold alg xs r ↔ r = foldFn xs := by
  intro xs r
  rw [show alg = kadane.alg from congrArg graph algFn_eq, foldFn_eq]
  exact kadane.cataFold_alg xs r

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · snd`, a fold followed by the
    projection onto `bestSoFar` (driver's `solve_eq_cata`). -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (Prod.snd : Int × Int → Int) := by
  rw [show alg = kadane.alg from congrArg graph algFn_eq,
      show solve = graph (fun xs => (kadane.foldFn xs).2) from
        congrArg graph (funext fun xs => congrArg Prod.snd (foldFn_eq xs))]
  exact kadane.solve_eq_cata

/-! ## Specification: the maximum achievable subarray sum -/

/-- `suffixSum xs v` — `v` is the sum of some non-empty SUFFIX of `xs` (a subarray ending at the
    last element). -/
def suffixSum : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => v = p ∨ ∃ v', suffixSum xs v' ∧ v = v' + p

/-- `subSum xs v` — `v` is the sum of SOME non-empty contiguous subarray of `xs`: either a subarray
    entirely within the prefix, or a suffix (ending at the last element). -/
def subSum : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun v => v = x
  | SnocList.snoc xs p => fun v => subSum xs v ∨ suffixSum (SnocList.snoc xs p) v

/-- The **specification** as a morphism `Arr ⟶ ℤ` in `Rel(Set)`: the relation of achievable subarray
    sums.  LeetCode 53 asks for its `≤`-maximum, `max (≤) · Λ spec`. -/
def spec : Arr ⟶ dZ := fun xs v => subSum xs v

/-! ## The generator, and "generator = spec" (the problem-specific inductions) -/

/-- The non-deterministic generator whose Pareto frontier the deterministic fold computes: at a
    leaf, the sole pair `(x,x)`; at a `snoc`, the running suffix `e` becomes `p` or `e+p`, and the
    best `b` is kept or reset to the new suffix.  `alg` is one deterministic choice inside it. -/
def genFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int) → Prop
  | Sum.inl x, w => w = (x, x)
  | Sum.inr (st, p), w => (w.1 = p ∨ w.1 = st.1 + p) ∧ (w.2 = st.2 ∨ w.2 = w.1)

/-- The generator as a (non-deterministic) morphism `F(ℤ×ℤ) ⟶ ℤ×ℤ`. -/
def gen : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := genFn

/-- The bundle's generator IS the file's generator. -/
theorem gen_eq : kadane.gen = gen := by
  funext u w
  cases u with
  | inl x => rfl
  | inr q => obtain ⟨st, p⟩ := q; rfl

/-- **Soundness**: every generatable pair has a suffix-sum first component and a subarray-sum
    second component.  (The suffix invariant is needed to close the `b := e` reset case.) -/
theorem gen_sound : ∀ (xs : SnocList Int Int) (w : Int × Int),
    cataFold gen xs w → suffixSum xs w.1 ∧ subSum xs w.2 := by
  intro xs; induction xs with
  | wrap x => intro w h; have hw : w = (x, x) := h; subst hw; exact ⟨rfl, rfl⟩
  | snoc xs p ih =>
    intro w h
    obtain ⟨w', hw', he, hb⟩ := h
    obtain ⟨ihsuf, ihsub⟩ := ih w' hw'
    have hsuf1 : suffixSum (SnocList.snoc xs p) w.1 := by
      simp only [suffixSum]
      rcases he with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨w'.1, ihsuf, h1⟩
    refine ⟨hsuf1, ?_⟩
    simp only [subSum]
    rcases hb with h2 | h2
    · exact Or.inl (by rw [h2]; exact ihsub)
    · exact Or.inr (by rw [h2]; exact hsuf1)

/-- Totality of the generator (it is entire): every list has some generatable pair — the driver's
    `gen_total`, transported along `gen_eq`. -/
theorem gen_total : ∀ (xs : SnocList Int Int), ∃ w, cataFold gen xs w := by
  intro xs; rw [← gen_eq]; exact kadane.gen_total xs

/-- **Completeness (diagonal)**: a suffix sum `v` is generatable as the "both components equal `v`"
    pair `(v, v)`.  This closes the suffix cases of `spec_gen` below. -/
theorem diag_gen : ∀ (xs : SnocList Int Int) (v : Int),
    suffixSum xs v → cataFold gen xs (v, v) := by
  intro xs; induction xs with
  | wrap x => intro v hv; have hvx : v = x := hv; show (v, v) = (x, x); rw [hvx]
  | snoc xs p ih =>
    intro v hv
    simp only [suffixSum] at hv
    rcases hv with h1 | ⟨v', hv', hveq⟩
    · obtain ⟨w', hw'⟩ := gen_total xs
      exact ⟨w', hw', Or.inl h1, Or.inr rfl⟩
    · exact ⟨(v', v'), ih v' hv', Or.inr (by rw [hveq]), Or.inr rfl⟩

/-- **Completeness**: every achievable subarray sum `v` is the second component of some generatable
    pair.  (Uses `diag_gen` for suffix subarrays and the IH for prefix subarrays.) -/
theorem spec_gen : ∀ (xs : SnocList Int Int) (v : Int),
    subSum xs v → ∃ e, cataFold gen xs (e, v) := by
  intro xs; induction xs with
  | wrap x => intro v hv; have hvx : v = x := hv; exact ⟨x, show (x, v) = (x, x) by rw [hvx]⟩
  | snoc xs p ih =>
    intro v hv
    simp only [subSum] at hv
    rcases hv with h1 | h2
    · obtain ⟨e', he'⟩ := ih v h1
      exact ⟨p, (e', v), he', Or.inl rfl, Or.inl rfl⟩
    · exact ⟨v, diag_gen (SnocList.snoc xs p) v h2⟩

/-! ## Correctness: `solve` computes the maximum achievable subarray sum — VIA the driver -/

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ spec`, pointwise in `Rel(Set)`):
    `solve xs` is an achievable subarray sum and is `≤`-greatest among all achievable subarray
    sums.  Emitted by `RunningBest.correct` from the bundle, with the generator characterisation
    supplying only "program = spec". -/
theorem solve_correct (xs : SnocList Int Int) :
    subSum xs (solveFn xs) ∧ ∀ v, subSum xs v → v ≤ solveFn xs := by
  have hgs : ∀ xs w, cataFold kadane.gen xs w → spec xs w.2 := by
    intro xs w hw; rw [gen_eq] at hw; exact (gen_sound xs w hw).2
  have hsg : ∀ xs v, spec xs v → ∃ e, cataFold kadane.gen xs (e, v) := by
    intro xs v hv; rw [gen_eq]; exact spec_gen xs v hv
  have h := kadane.correct spec hgs hsg xs
  rw [show solveFn xs = (kadane.foldFn xs).2 from congrArg Prod.snd (foldFn_eq xs)]
  exact h

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `solve` is exactly the morphism `Λ spec ≫ est D`
    for the `≤`-preference order `D w z := z ≤ w` — not merely pointwise. Bridged from `solve_correct`. -/
theorem solve_eq_est : solve = Λ spec ≫ est (fun w z : Int => z ≤ w) :=
  eq_Λ_comp_est _ (fun x y h1 h2 => Int.le_antisymm h2 h1) solveFn spec
    (fun xs => (solve_correct xs).1) (fun xs v hv => (solve_correct xs).2 v hv)

/-- **The program refines the specification**: every value `solve` returns is an achievable
    subarray sum. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact (solve_correct xs).1

/-! ## Running the program -/

/-- Build an array from a first element and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList (-2) [1, -3, 4, -1, 2, 1, -5, 4]) = 6 := by decide
example : solveFn (ofList (-1) []) = -1 := by decide
example : solveFn (ofList 1 [2, 3]) = 6 := by decide
example : solveFn (ofList (-3) [-1, -2]) = -1 := by decide

end Freyd.Alg.RelSet.LC53
