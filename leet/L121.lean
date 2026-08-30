/-
  LeetCode 121 — Best Time to Buy and Sell Stock — as an ALLEGORY PROGRAM,
  derived through the generic running-best driver `rel.AutoDerive`.

  Problem: given prices `x₀,…,x_{n-1}` (one per day), pick a buy day `i` and a later sell day `j > i`
  maximising the profit `x_j − x_i`; if no trade is profitable, the answer is `0`.

  The point of this file is to *program in the allegory* `Rel(Set)` (Freyd's category of sets and
  relations, `AOP.A6_1_RelSet`), reusing the Bird & de Moor toolkit:

  1. **Data** — a non-empty list of prices is the initial algebra `SnocList ℤ ℤ` of the functor
     `F X = ℤ + X × ℤ` (the reusable engine `AOP.A6_SnocList`).  `wrap x` is a single price,
     `snoc xs p` appends a price — so a left-to-right scan is a CATAMORPHISM over this datatype.

  2. **Program** — the O(n) sweep is the fold with state `(minSoFar, bestProfit)` and algebra
     `[ x ↦ (x,0),  ((m,b),p) ↦ (min m p, max b (p−m)) ]`.  We package it as a genuine morphism
     `solve : Prices ⟶ ℤ` in `Rel(Set)` (a `Map`, i.e. the graph of a function) and prove it *is*
     the catamorphism of that algebra followed by the second projection (`solve_eq_cata`).

  3. **Specification** — `spec : Prices ⟶ ℤ` is the relation of *achievable* profits: `0`, or `s−b`
     for a buy price `b` occurring strictly before a sell price `s`.  LeetCode asks for its
     `≤`-maximum, i.e. `max (≤) · Λ spec` in `Rel(Set)`.

  4. **Correctness** — `solve` computes exactly that maximum (`solve_correct`, `solve_eq_est`).
     Every relational side condition of the greedy derivation (order transitivity, `MonotonicAlg`,
     the greedy-step refinement, fold = catamorphism, generator totality — formerly ~100 hand-written
     lines here) is discharged by the `RunningBest` driver from the bundle `trade` below; this file
     supplies only the CREATIVE content: the bundle's fields (state pair + generator candidates +
     dominance order + eight one-line arithmetic facts) and the generator-vs-spec characterisation
     (`gen_sound`/`spec_gen`), the genuinely problem-specific inductions.

  Mathlib-free.  Axioms of the headline: {propext, Classical.choice, Quot.sound} — the
  `Classical.choice` is the honest cost of the relational-catamorphism universal property,
  inherited via `cataR_eq_relCata`.
-/
import rel.AutoDerive

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC121

open Freyd Freyd.Alg.RelSet.SL

/-! ## Data: prices as a non-empty snoc-list of integers -/

/-- The object of price lists in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = single price, `snoc xs p`
    = `xs` with a new final price `p`). -/
abbrev Prices : RelSet.{0} := dSL Int Int
/-- The object of integers (profits) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The creative bundle — the whole algorithmic content of the sweep -/

/-- Best-single-trade's derivation bundle.  State `(minSoFar, bestProfit)`: the new running min is
    kept or reset to the new price (candidates), deterministically their min; the new best is kept
    or reset to `p − minSoFar` (sell today, buy at the running min), deterministically the max;
    first-coordinate dominance is `≤` (a SMALLER running min is better). -/
def trade : RunningBest Int Int Int where
  base x := (x, 0)
  step1 e p := imin e p
  step2 e b p := imax b (p - e)
  cand1 e p w1 := w1 = e ∨ w1 = p
  cand2 e b p _ w2 := w2 = b ∨ w2 = p - e
  ord e e' := e ≤ e'
  ord_refl e := Int.le_refl e
  ord_trans h1 h2 := Int.le_trans h1 h2
  step1_mono p h := imin_mono h (Int.le_refl p)
  step2_mono p h1 h2 := imax_mono h2 (by omega)
  step1_cand e p := imin_eq_or e p
  step2_cand e b p := imax_eq_or b (p - e)
  cand1_le h := by
    rcases h with h | h <;> rw [h]
    · exact imin_le_left _ _
    · exact imin_le_right _ _
  cand2_le h1 h2 := by
    rcases h2 with h | h <;> rw [h]
    · exact imax_ge_left _ _
    · exact imax_ge_right _ _

/-! ## The program: the left-scan catamorphism `[base, step]`, state `(minSoFar, bestProfit)` -/

/-- The fold algebra `[ x ↦ (x,0),  ((m,b),p) ↦ (min m p, max b (p−m)) ] : F(ℤ×ℤ) → ℤ×ℤ`. -/
def algFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int)
  | Sum.inl x => (x, 0)
  | Sum.inr (st, p) => (imin st.1 p, imax st.2 (p - st.1))

/-- The algebra as a morphism (a `Map`) `F(ℤ×ℤ) ⟶ ℤ×ℤ` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion), returning `(minSoFar, bestProfit)`. -/
def foldFn : SnocList Int Int → Int × Int
  | SnocList.wrap x => (x, 0)
  | SnocList.snoc xs p => (imin (foldFn xs).1 p, imax (foldFn xs).2 (p - (foldFn xs).1))

/-- The answer: the second component (best profit) of the fold. -/
def solveFn (xs : SnocList Int Int) : Int := (foldFn xs).2

/-- **The allegory program**: LeetCode 121's solution as a morphism `Prices ⟶ ℤ` in `Rel(Set)`. -/
def solve : Prices ⟶ dZ := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## The program IS the bundle's — three definitional bridges -/

/-- The file's algebra is the bundle's. -/
theorem algFn_eq : algFn = trade.algFn := by
  funext u
  cases u with
  | inl x => rfl
  | inr q => obtain ⟨st, p⟩ := q; rfl

/-- The file's fold is the bundle's. -/
theorem foldFn_eq : ∀ xs, foldFn xs = trade.foldFn xs := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs p ih =>
    show (imin (foldFn xs).1 p, imax (foldFn xs).2 (p - (foldFn xs).1))
        = (imin (trade.foldFn xs).1 p, imax (trade.foldFn xs).2 (p - (trade.foldFn xs).1))
    rw [ih]

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree (driver's `cataFold_alg`). -/
theorem cataFold_alg : ∀ (xs : SnocList Int Int) (r : Int × Int),
    cataFold alg xs r ↔ r = foldFn xs := by
  intro xs r
  rw [show alg = trade.alg from congrArg graph algFn_eq, foldFn_eq]
  exact trade.cataFold_alg xs r

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · snd`, a fold followed by the
    projection onto `bestProfit` (driver's `solve_eq_cata`). -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (Prod.snd : Int × Int → Int) := by
  rw [show alg = trade.alg from congrArg graph algFn_eq,
      show solve = graph (fun xs => (trade.foldFn xs).2) from
        congrArg graph (funext fun xs => congrArg Prod.snd (foldFn_eq xs))]
  exact trade.solve_eq_cata

/-! ## Specification: the maximum achievable profit -/

/-- `mem xs b` — the price `b` occurs in `xs`. -/
def mem : SnocList Int Int → Int → Prop
  | SnocList.wrap x => fun b => b = x
  | SnocList.snoc xs p => fun b => mem xs b ∨ b = p

/-- `Before xs b s` — a price `b` occurs strictly before a price `s` (a valid buy day `<` sell day). -/
def Before : SnocList Int Int → Int → Int → Prop
  | SnocList.wrap x => fun b s => False
  | SnocList.snoc xs p => fun b s => Before xs b s ∨ (mem xs b ∧ s = p)

/-- `profit xs v` — `v` is an achievable profit: either `0` (no trade) or `s − b` for a buy price
    `b` strictly before a sell price `s`.  This is the transpose `Λ⁻¹ spec` of the spec relation. -/
def profit (xs : SnocList Int Int) (v : Int) : Prop :=
  v = 0 ∨ ∃ b s, Before xs b s ∧ v = s - b

/-- The **specification** as a morphism `Prices ⟶ ℤ` in `Rel(Set)`: the relation of achievable
    profits.  LeetCode 121 asks for its `≤`-maximum, `max (≤) · Λ spec`. -/
def spec : Prices ⟶ dZ := fun xs v => profit xs v

/-! ## The generator, and "generator = spec" (the problem-specific inductions)

  The non-deterministic generator `gen` whose Pareto frontier the deterministic fold computes: at a
  leaf, the sole pair `(x,0)`; at a `snoc`, the running min `m` becomes `m` or `p`, and the best
  profit `b` is kept or reset to `p - m`.  `alg` is one deterministic choice inside it — all of
  which the driver now derives from the bundle (`gen_eq`); only the characterisation
  `gen_sound`/`spec_gen` below is problem-specific. -/

/-- The generator, pointwise. -/
def genFn : (Fobj Int Int (⟨Int × Int⟩ : RelSet.{0})).carrier → (Int × Int) → Prop
  | Sum.inl x, w => w = (x, 0)
  | Sum.inr (st, p), w => (w.1 = st.1 ∨ w.1 = p) ∧ (w.2 = st.2 ∨ w.2 = p - st.1)

/-- The generator as a (non-deterministic) morphism `F(ℤ×ℤ) ⟶ ℤ×ℤ`. -/
def gen : Fobj Int Int (⟨Int × Int⟩ : RelSet.{0}) ⟶ (⟨Int × Int⟩ : RelSet.{0}) := genFn

/-- The bundle's generator IS the file's generator. -/
theorem gen_eq : trade.gen = gen := by
  funext u w
  cases u with
  | inl x => rfl
  | inr q => obtain ⟨st, p⟩ := q; rfl

/-- Lift a profit of `xs` to a profit of `snoc xs p` (the buy-before-sell window only grows). -/
theorem profit_snoc (xs : SnocList Int Int) (p v : Int) (h : profit xs v) :
    profit (SnocList.snoc xs p) v := by
  rcases h with h0 | ⟨b, s, hbef, hv⟩
  · exact Or.inl h0
  · exact Or.inr ⟨b, s, Or.inl hbef, hv⟩

/-- **Soundness**: every generatable pair has a member first component (a price) and an achievable
    profit second component.  (The member invariant is needed to close the `b := p - m` case.) -/
theorem gen_sound : ∀ (xs : SnocList Int Int) (w : Int × Int),
    cataFold gen xs w → mem xs w.1 ∧ profit xs w.2 := by
  intro xs; induction xs with
  | wrap x => intro w h; have hw : w = (x, 0) := h; subst hw; exact ⟨rfl, Or.inl rfl⟩
  | snoc xs p ih =>
    intro w h
    obtain ⟨w', hw', he, hb⟩ := h
    obtain ⟨ihmem, ihprof⟩ := ih w' hw'
    have hmem1 : mem (SnocList.snoc xs p) w.1 := by
      simp only [mem]
      rcases he with h1 | h1
      · exact Or.inl (by rw [h1]; exact ihmem)
      · exact Or.inr h1
    refine ⟨hmem1, ?_⟩
    rcases hb with h2 | h2
    · exact (by rw [h2]; exact profit_snoc xs p w'.2 ihprof)
    · refine Or.inr ⟨w'.1, p, Or.inr ⟨ihmem, rfl⟩, ?_⟩
      rw [h2]

/-- Totality of the generator (it is entire): every list has some generatable pair — the driver's
    `gen_total`, transported along `gen_eq`. -/
theorem gen_total : ∀ (xs : SnocList Int Int), ∃ w, cataFold gen xs w := by
  intro xs; rw [← gen_eq]; exact trade.gen_total xs

/-- **Completeness (first component)**: a price `b` occurring in `xs` is generatable as the first
    component of some pair.  Closes the buy-at-`b` case of `spec_gen`. -/
theorem mem_gen : ∀ (xs : SnocList Int Int) (b : Int),
    mem xs b → ∃ b2, cataFold gen xs (b, b2) := by
  intro xs; induction xs with
  | wrap x => intro b hb; have hbx : b = x := hb; exact ⟨0, show (b, 0) = (x, 0) by rw [hbx]⟩
  | snoc xs p ih =>
    intro b hb
    simp only [mem] at hb
    rcases hb with hm | hm
    · obtain ⟨b2', hb2'⟩ := ih b hm
      exact ⟨b2', (b, b2'), hb2', Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨w', hw'⟩ := gen_total xs
      exact ⟨w'.2, w', hw', Or.inr hm, Or.inl rfl⟩

/-- **Completeness**: every achievable profit `v` is the second component of some generatable pair.
    (Uses `mem_gen` for the "reset to `p - buy`" case and the IH for the "kept" case.) -/
theorem spec_gen : ∀ (xs : SnocList Int Int) (v : Int),
    profit xs v → ∃ e, cataFold gen xs (e, v) := by
  intro xs; induction xs with
  | wrap x =>
    intro v hv
    rcases hv with h0 | ⟨b, s, hbef, _⟩
    · exact ⟨x, show (x, v) = (x, 0) by rw [h0]⟩
    · exact hbef.elim
  | snoc xs p ih =>
    intro v hv
    rcases hv with h0 | ⟨b, s, hbef, hvs⟩
    · obtain ⟨e', he'⟩ := ih 0 (Or.inl rfl)
      exact ⟨e', (e', 0), he', Or.inl rfl, Or.inl h0⟩
    · simp only [Before] at hbef
      rcases hbef with hb | ⟨hmem, hsp⟩
      · obtain ⟨e', he'⟩ := ih v (Or.inr ⟨b, s, hb, hvs⟩)
        exact ⟨e', (e', v), he', Or.inl rfl, Or.inl rfl⟩
      · obtain ⟨b2, hb2⟩ := mem_gen xs b hmem
        exact ⟨b, (b, b2), hb2, Or.inl rfl, Or.inr (show v = p - b by omega)⟩

/-! ## Correctness: `solve` computes the maximum achievable profit — VIA the driver -/

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ spec`, pointwise in `Rel(Set)`):
    `solve xs` is an achievable profit and is `≤`-greatest among all achievable profits.  Emitted by
    `RunningBest.correct` from the bundle, with the generator characterisation supplying only
    "program = spec". -/
theorem solve_correct (xs : SnocList Int Int) :
    profit xs (solveFn xs) ∧ ∀ v, profit xs v → v ≤ solveFn xs := by
  have hgs : ∀ xs w, cataFold trade.gen xs w → spec xs w.2 := by
    intro xs w hw; rw [gen_eq] at hw; exact (gen_sound xs w hw).2
  have hsg : ∀ xs v, spec xs v → ∃ e, cataFold trade.gen xs (e, v) := by
    intro xs v hv; rw [gen_eq]; exact spec_gen xs v hv
  have h := trade.correct spec hgs hsg xs
  rw [show solveFn xs = (trade.foldFn xs).2 from congrArg Prod.snd (foldFn_eq xs)]
  exact h

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `solve` is exactly the morphism `Λ spec ≫ est D`
    for the `≤`-preference order `D w z := z ≤ w` — not merely pointwise. Bridged from `solve_correct`. -/
theorem solve_eq_est : solve = Λ spec ≫ est (fun w z : Int => z ≤ w) :=
  eq_Λ_comp_est _ (fun x y h1 h2 => Int.le_antisymm h2 h1) solveFn spec
    (fun xs => (solve_correct xs).1) (fun xs v hv => (solve_correct xs).2 v hv)

/-- **The program refines the specification**: every value `solve` returns is an achievable profit. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact (solve_correct xs).1

/-! ## Running the program -/

/-- Build a price list from a first price and the rest, in day order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 7 [1, 5, 3, 6, 4]) = 5 := by decide
example : solveFn (ofList 7 [6, 4, 3, 1]) = 0 := by decide
example : solveFn (ofList 2 [4, 1]) = 2 := by decide

end Freyd.Alg.RelSet.LC121
