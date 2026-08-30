/-
  AUTO-DERIVE, increment 1: the running-best-pair greedy scan, mechanised.

  Kadane's maximum-subarray sweep (`leet.L53`) and best-single-trade (`leet.L121`) are the
  SAME derivation: a snoc-list fold on a pair state (running "current" `e`, running "best" `b`),
  correct by the greedy theorem on a Pareto product order (`A7_4_Horner.horner_correct`).  Each
  file hand-proves ~100 lines of identical relational side conditions (order transitivity,
  `MonotonicAlg`, the greedy-step refinement `alg ⊑ ΛS·max R`, fold = catamorphism, generator
  totality).  Those proofs never touch the problem: they consume only componentwise
  monotonicity / selection / domination facts about the two coordinate operations.

  This file discharges them ONCE, generically.  `RunningBest L E A1` bundles the CREATIVE
  inputs of such a derivation —

  * `base`, `step1`, `step2` — the deterministic algebra (the algorithm);
  * `cand1`, `cand2`        — the nondeterministic generator's candidate sets (the search space);
  * `ord`                   — the first-coordinate Pareto dominance order —

  together with eight one-line arithmetic facts about them.  From these, `RunningBest.correct`
  emits the full extremum correctness

      spec xs (fold xs).2  ∧  ∀ v, spec xs v → v ≤ (fold xs).2

  and `RunningBest.eq_est` the §7.5 morphism headline `solve = max (≤)·Λ spec`, with every
  relational side condition (`pareto_trans`, `alg_mono`, `alg_le_gen`, `gen_recip_le`,
  `alg_ref`, `cataFold_alg`, `gen_total`, `hR2`) discharged internally.  What remains HUMAN,
  per problem: choosing the bundle's fields (the algorithmic insight) and the generator-vs-spec
  characterisation `gen_spec`/`spec_gen` ("the search space is exactly THIS spec" — genuinely
  problem-specific inductions).

  Demo: `leet/L53_auto.lean` re-derives Kadane from a `RunningBest` instance.

  Mathlib-free.  Axioms ⊆ {propext, Classical.choice, Quot.sound}, inherited from
  `horner_correct` via `cataR_eq_relCata` (the honest cost of the relational-catamorphism
  universal property).
-/
import AOP.A7_4_Horner

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.SL

open Freyd

/-! ## Integer `min`/`max` toolkit — the shared home (the `L*` case studies each kept a copy) -/

/-- `imin a b` = the smaller of `a`, `b`. -/
def imin (a b : Int) : Int := if a ≤ b then a else b
/-- `imax a b` = the larger of `a`, `b`. -/
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imin_le_left  (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
theorem imin_eq_or (a b : Int) : imin a b = a ∨ imin a b = b := by
  unfold imin; split
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem imax_ge_left  (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Int) : imax a b = a ∨ imax a b = b := by
  unfold imax; split
  · exact Or.inr rfl
  · exact Or.inl rfl
theorem imin_mono {a a' b b' : Int} (ha : a ≤ a') (hb : b ≤ b') : imin a b ≤ imin a' b' := by
  unfold imin; split <;> split <;> omega
theorem imax_mono {a a' b b' : Int} (ha : a ≤ a') (hb : b ≤ b') : imax a b ≤ imax a' b' := by
  unfold imax; split <;> split <;> omega

/-! ## The bundle of creative inputs -/

/-- The creative inputs of a running-best-pair greedy derivation, plus the one-line arithmetic
    facts its mechanical side conditions reduce to.  The state is a pair `(e, b) : A1 × ℤ` —
    a running "current" `e` and a running "best" `b`; the answer is the final `b`.  The second
    coordinate is always preferred by `≤` (a bigger best is better); the first by the
    problem's own dominance `ord` (Kadane: `≥`; best-trade: `≤`, a smaller running min wins). -/
structure RunningBest (L E A1 : Type) where
  /-- Leaf state: the pair produced from a single leaf `x`. -/
  base : L → A1 × Int
  /-- New running-current from the old one and the new element. -/
  step1 : A1 → E → A1
  /-- New running-best from the old current, the old best and the new element. -/
  step2 : A1 → Int → E → Int
  /-- Generator candidates for the new current (given the old current and the new element). -/
  cand1 : A1 → E → A1 → Prop
  /-- Generator candidates for the new best (may depend on the chosen new current `w1`,
      e.g. Kadane's "reset the best to the new suffix"). -/
  cand2 : A1 → Int → E → A1 → Int → Prop
  /-- First-coordinate Pareto dominance: `ord e e'` = "`e` is at least as good as `e'`". -/
  ord : A1 → A1 → Prop
  ord_refl : ∀ e, ord e e
  ord_trans : ∀ {e f g}, ord e f → ord f g → ord e g
  /-- `step1` preserves dominance. -/
  step1_mono : ∀ {e e'} (p : E), ord e e' → ord (step1 e p) (step1 e' p)
  /-- `step2` is monotone: a dominating state yields at least as good a best. -/
  step2_mono : ∀ {e e' b b'} (p : E), ord e e' → b' ≤ b → step2 e' b' p ≤ step2 e b p
  /-- Selection: the deterministic new current is a candidate. -/
  step1_cand : ∀ (e : A1) (p : E), cand1 e p (step1 e p)
  /-- Selection: the deterministic new best is a candidate (at the deterministic new current). -/
  step2_cand : ∀ (e : A1) (b : Int) (p : E), cand2 e b p (step1 e p) (step2 e b p)
  /-- Domination: the deterministic new current dominates every candidate. -/
  cand1_le : ∀ {e p w1}, cand1 e p w1 → ord (step1 e p) w1
  /-- Domination: the deterministic new best is `≥` every candidate best. -/
  cand2_le : ∀ {e b p w1 w2}, cand1 e p w1 → cand2 e b p w1 w2 → w2 ≤ step2 e b p

namespace RunningBest

variable {L E A1 : Type} (P : RunningBest L E A1)

/-! ## The derived program, generator and order -/

/-- The deterministic algebra as a function `F(A1×ℤ) → A1×ℤ`. -/
def algFn : (Fobj L E (⟨A1 × Int⟩ : RelSet.{0})).carrier → A1 × Int
  | Sum.inl x => P.base x
  | Sum.inr (st, p) => (P.step1 st.1 p, P.step2 st.1 st.2 p)

/-- The algebra as a morphism (a `Map`) in `Rel(Set)`. -/
def alg : Fobj L E (⟨A1 × Int⟩ : RelSet.{0}) ⟶ (⟨A1 × Int⟩ : RelSet.{0}) := graph P.algFn

/-- The concrete fold (the PROGRAM, up to the final `.2` projection). -/
def foldFn : SnocList L E → A1 × Int
  | SnocList.wrap x => P.base x
  | SnocList.snoc xs p => (P.step1 (foldFn xs).1 p, P.step2 (foldFn xs).1 (foldFn xs).2 p)

/-- The nondeterministic generator: at a leaf the sole pair `base x`; at a `snoc` any
    candidate pair.  The deterministic algebra is one choice inside it (`alg_le_gen`). -/
def genFn : (Fobj L E (⟨A1 × Int⟩ : RelSet.{0})).carrier → (A1 × Int) → Prop
  | Sum.inl x => fun w => w = P.base x
  | Sum.inr (st, p) => fun w => P.cand1 st.1 p w.1 ∧ P.cand2 st.1 st.2 p w.1 w.2

/-- The generator as a (non-deterministic) morphism. -/
def gen : Fobj L E (⟨A1 × Int⟩ : RelSet.{0}) ⟶ (⟨A1 × Int⟩ : RelSet.{0}) := P.genFn

/-- The Pareto product order: dominate in the first coordinate, `≥` in the second. -/
def pareto : (⟨A1 × Int⟩ : RelSet.{0}) ⟶ (⟨A1 × Int⟩ : RelSet.{0}) :=
  fun w w' => P.ord w.1 w'.1 ∧ w'.2 ≤ w.2

/-! ## The mechanical side conditions, discharged once -/

/-- The abstract fold in `Rel(Set)` is the graph of the concrete fold. -/
theorem cataFold_alg : ∀ (xs : SnocList L E) (r : A1 × Int),
    cataFold P.alg xs r ↔ r = P.foldFn xs := by
  intro xs; induction xs with
  | wrap x => intro r; exact Iff.rfl
  | snoc xs p ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨P.foldFn xs, (ih (P.foldFn xs)).mpr rfl, h⟩

/-- `pareto` is transitive (`R·R ⊑ R`). -/
theorem pareto_trans : P.pareto ≫ P.pareto ⊑ P.pareto := by
  rw [le_iff]; rintro w w' ⟨w'', ⟨h1a, h1b⟩, h2a, h2b⟩
  exact ⟨P.ord_trans h1a h2a, Int.le_trans h2b h1b⟩

/-- The deterministic step is MONOTONIC on the Pareto order. -/
theorem alg_mono : MonotonicAlg (F := F L E) P.alg P.pareto := by
  show (F L E).map P.pareto ≫ P.alg ⊑ P.alg ≫ P.pareto
  rw [le_iff]; rintro u w ⟨u', hFR, rfl⟩
  refine ⟨P.algFn u, rfl, ?_⟩
  cases u with
  | inl x => cases u' with
    | inl x' =>
      have hx : x = x' := hFR
      subst hx
      exact ⟨P.ord_refl _, Int.le_refl _⟩
    | inr q => exact hFR.elim
  | inr pr => cases u' with
    | inl x' => exact hFR.elim
    | inr q' =>
      obtain ⟨st, p⟩ := pr; obtain ⟨st', p'⟩ := q'
      obtain ⟨hd, hpp⟩ := hFR
      have hpp' : p = p' := hpp
      subst hpp'
      exact ⟨P.step1_mono p hd.1, P.step2_mono p hd.1 hd.2⟩

/-- Greedy-step refinement, part 1: the deterministic choice is one of the candidates. -/
theorem alg_le_gen : P.alg ⊑ P.gen := by
  rw [le_iff]; intro u w hw
  have hwe : w = P.algFn u := hw
  subst hwe
  cases u with
  | inl x => exact rfl
  | inr pr =>
    obtain ⟨st, p⟩ := pr
    exact ⟨P.step1_cand st.1 p, P.step2_cand st.1 st.2 p⟩

/-- Greedy-step refinement, part 2: the deterministic choice Pareto-dominates every candidate. -/
theorem gen_recip_le : P.gen° ≫ P.alg ⊑ P.pareto° := by
  rw [le_iff]; rintro w1 w2 ⟨u, hgu, rfl⟩
  cases u with
  | inl x =>
    have hw1 : w1 = P.base x := hgu
    subst hw1
    exact ⟨P.ord_refl _, Int.le_refl _⟩
  | inr pr =>
    obtain ⟨st, p⟩ := pr
    exact ⟨P.cand1_le hgu.1, P.cand2_le hgu.1 hgu.2⟩

/-- The greedy-step refinement `alg ⊑ ΛS·max R` that `greedy` consumes. -/
theorem alg_ref : P.alg ⊑ Λ P.gen ≫ est P.pareto :=
  le_Λ_comp_est_iff.mpr ⟨P.alg_le_gen, P.gen_recip_le⟩

/-- Totality of the generator — free from the selection facts (the deterministic choice
    witnesses it).  Handy for the problem-specific completeness inductions. -/
theorem gen_total : ∀ xs : SnocList L E, ∃ w, cataFold P.gen xs w := by
  intro xs; induction xs with
  | wrap x => exact ⟨P.base x, rfl⟩
  | snoc xs p ih =>
    obtain ⟨w', hw'⟩ := ih
    exact ⟨(P.step1 w'.1 p, P.step2 w'.1 w'.2 p), w', hw',
      P.step1_cand w'.1 p, P.step2_cand w'.1 w'.2 p⟩

/-! ## The drivers: full correctness from the bundle + the spec characterisation -/

/-- **Auto-derived extremum correctness.**  Given the bundle and the problem-specific
    generator-vs-spec characterisation (`gen_spec`: generatable ⟹ its best satisfies the spec;
    `spec_gen`: every spec value is a generatable best), the fold's second component is the
    `≤`-MAXIMUM of `spec`.  This is `A7_4_Horner.horner_correct` with seven of its thirteen
    arguments discharged by the bundle. -/
theorem correct (spec : dSL L E ⟶ (⟨Int⟩ : RelSet.{0}))
    (gen_spec : ∀ xs w, cataFold P.gen xs w → spec xs w.2)
    (spec_gen : ∀ xs v, spec xs v → ∃ e, cataFold P.gen xs (e, v))
    (xs : SnocList L E) :
    spec xs (P.foldFn xs).2 ∧ ∀ v, spec xs v → v ≤ (P.foldFn xs).2 :=
  horner_correct P.gen P.alg P.pareto P.foldFn (graph_map P.algFn) P.cataFold_alg
    P.pareto_trans P.alg_mono P.alg_ref (fun x y h => h.2) spec gen_spec spec_gen xs

/-- **Auto-derived §7.5 morphism headline**: the program (the graph of `.2 ∘ fold`) IS
    `max (≤)·Λ spec` as a morphism of `Rel(Set)`, not merely pointwise. -/
theorem eq_est (spec : dSL L E ⟶ (⟨Int⟩ : RelSet.{0}))
    (gen_spec : ∀ xs w, cataFold P.gen xs w → spec xs w.2)
    (spec_gen : ∀ xs v, spec xs v → ∃ e, cataFold P.gen xs (e, v)) :
    (graph (fun xs => (P.foldFn xs).2) : dSL L E ⟶ (⟨Int⟩ : RelSet.{0}))
      = Λ spec ≫ est (fun w z : Int => z ≤ w) :=
  eq_Λ_comp_est _ (fun x y h1 h2 => Int.le_antisymm h2 h1) _ spec
    (fun xs => (P.correct spec gen_spec spec_gen xs).1)
    (fun xs v hv => (P.correct spec gen_spec spec_gen xs).2 v hv)

/-- The program is a catamorphism: `.2 ∘ fold = ⦇alg⦈ · snd` in `Rel(Set)`. -/
theorem solve_eq_cata :
    (graph (fun xs => (P.foldFn xs).2) : dSL L E ⟶ (⟨Int⟩ : RelSet.{0}))
      = cataR P.alg ≫ graph (Prod.snd : A1 × Int → Int) := by
  apply hom_ext; intro xs v
  simp only [graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨P.foldFn xs, (P.cataFold_alg xs (P.foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(P.cataFold_alg xs st).mp hst] at hv; exact hv

end RunningBest
end Freyd.Alg.RelSet.SL
