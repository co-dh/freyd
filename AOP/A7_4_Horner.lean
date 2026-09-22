/-
  Bird & de Moor, *Algebra of Programming* — Horner's rule for two-component "running-best"
  scans, via the GREEDY THEOREM (§7.2).

  A left-to-right scan that maintains a PAIR state `(e, b)` — a running "current" component `e`
  and a running "best-so-far" component `b` that depends on `e` — is not a scalar catamorphism
  (the `b`-fold alone is not compositional; it needs `e`).  Kadane's maximum-subarray sweep
  (`leet.L53`) and the best-single-trade sweep (`leet.L121`) are both of this shape.  Bird &
  de Moor solve this family by the greedy theorem on the PAIR carrier ordered by a PRODUCT
  (Pareto) order, then reading off the answer as the second component of the Pareto-optimum.

  This file supplies the reusable content that turns `A7_2.greedy` into a scalar-answer
  correctness statement:

  * `greedy_of_refinement_mono` — the max-form of `A7_2.greedy_of_refinement`: a monotone
    deterministic algebra `alg` that refines the greedy choice `Λ S ≫ est R` has its
    catamorphism land inside the Pareto frontier `Λ (relCata I S) ≫ est R`.  This is the
    genuine greedy-theorem content (it routes through `greedy_of_refinement` → the hylomorphism
    theorem `hylo_le_of_prefixed`).

  * `horner_correct` — the concrete Rel(Set) packaging: given the greedy hypotheses on a pair
    carrier `⟨A1 × ℤ⟩` with a product order whose SECOND coordinate is `≤` (`hR2`), plus a
    characterisation of the nondeterministic generator `S` against a scalar spec relation
    (`gen_spec` = generatable ⟹ its second component satisfies the spec; `spec_gen` = every spec
    value is a generatable second component), the deterministic fold's second component is the
    `≤`-MAXIMUM of the spec.  BOTH halves — achievability and domination — are read off from the
    single greedy conclusion (membership + maximality of the Pareto optimum); the generator
    characterisation supplies only "program = spec", never the optimisation.

  Mathlib-free.  Axioms ⊆ {propext, Classical.choice, Quot.sound}; the `Classical.choice` is
  inherited from `relCata`'s universal property via `A6_SnocList.cataR_eq_relCata` (the same
  cost `A6_6_Sort` pays), and is the honest price of genuinely applying the catamorphism theory.
-/
module

public import AOP.A6_SnocList
-- `Λ`/`est`/`E` read pointwise at Rel(Set), where §7.1's `est` and §6.1's set model first meet;
-- the packaging below reads the greedy conclusion off them rather than re-proving them.
public import AOP.A7_2_RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg

universe u

/-! ## Abstract: greedy-from-refinement with monotonicity stated on `R` -/

section Abstract
variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {A B : 𝒜}

/-- **`A7_2.greedy_of_refinement` with monotonicity on `R` instead of `R°`.**  A deterministic
    algebra `f` (a map), MONOTONIC on the order `R`, that REFINES the greedy choice
    `Λ S ≫ est R`, already has its catamorphism inside `est R·Λ⦇S⦈` — the Pareto frontier of
    the plain non-deterministic catamorphism `⦇S⦈`.  Transitivity and monotonicity are
    transposed to `R°` by `recip_mono`/`monotonicAlg_recip_iff` (the latter needs `f` a map). -/
public theorem greedy_of_refinement_mono (hFr : F.PreservesRecip) (I : InitialAlgebra F) {R : A ⟶ A}
    {S f : F.obj A ⟶ A} (hf : Map f) (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg f R)
    (href : f ⊑ S%∋ ≫ est(R)) : ⦇f⦈ ⊑ ⦇S⦈%∋ ≫ est(R) := by
  have htrans' : R° ≫ R° ⊑ R° := by
    have h := recip_mono htrans; rwa [Allegory.recip_comp] at h
  have hmono' : MonotonicAlg f R° := (monotonicAlg_recip_iff hf hFr).mp hmono
  exact greedy_of_refinement hFr I htrans' hmono' href

end Abstract

namespace RelSet

/-! ## The Horner correctness packaging over snoc-lists -/

namespace SL

open Freyd

/-- **Horner correctness for two-component running-best scans.**  On the pair carrier
    `⟨A1 × ℤ⟩` with:

    * a deterministic fold `alg` computed by `foldFn` (`hfold`), monotone on a product order `R`
      whose second coordinate is `≤` (`hR2 : R x y → y.2 ≤ x.2`) and transitive (`htrans`),
      refining the greedy choice of the non-deterministic generator `S` (`href`);
    * a scalar spec relation `spec`, with `gen_spec` (every `S`-generatable pair's second
      component satisfies `spec`) and `spec_gen` (every `spec` value is the second component of
      some generatable pair),

    the deterministic answer `(foldFn xs).2` is the `≤`-MAXIMUM of `spec xs`: it satisfies the
    spec (achievability) and dominates every spec value (domination).  Both are read off the
    single greedy conclusion `greedy_of_refinement_mono` (membership + maximality of the Pareto
    optimum); the `gen_spec`/`spec_gen` characterisation only says "program = spec". -/
public theorem horner_correct {L E A1 : Type}
    (S alg : Fobj L E (⟨A1 × Int⟩ : RelSet.{0}) ⟶ (⟨A1 × Int⟩ : RelSet.{0}))
    (R : (⟨A1 × Int⟩ : RelSet.{0}) ⟶ ⟨A1 × Int⟩)
    (foldFn : SnocList L E → A1 × Int)
    (halg_map : Map alg)
    (hfold : ∀ xs w, cataFold alg xs w ↔ w = foldFn xs)
    (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg (F := F L E) alg R)
    (href : alg ⊑ S%∋ ≫ est(R))
    (hR2 : ∀ x y : A1 × Int, R x y → y.2 ≤ x.2)
    (spec : (dSL L E) ⟶ (⟨Int⟩ : RelSet.{0}))
    (gen_spec : ∀ xs w, cataFold S xs w → spec xs w.2)
    (spec_gen : ∀ xs v, spec xs v → ∃ e : A1, cataFold S xs (e, v))
    (xs : SnocList L E) :
    spec xs (foldFn xs).2 ∧ ∀ v, spec xs v → v ≤ (foldFn xs).2 := by
  -- The genuine greedy content: the fold lands inside the Pareto frontier of ⦇S⦈.
  have Hcore : ⦇alg⦈ ⊑ ⦇S⦈%∋ ≫ est(R) :=
    greedy_of_refinement_mono (F_preservesRecip L E) (initial L E) halg_map htrans hmono href
  rw [← cataR_eq_relCata alg, ← cataR_eq_relCata S] at Hcore
  -- Apply the refinement at the actual fold output `foldFn xs`.
  have hmem_fold : (cataR alg) xs (foldFn xs) := (hfold xs (foldFn xs)).mpr rfl
  obtain ⟨P, hAP, hmax⟩ := (le_iff.mp Hcore) xs (foldFn xs) hmem_fold
  rw [Λ_eq_classifier] at hAP
  -- `Λ (⦇S⦈) xs P` pins `P` to the generatable set of `xs`.
  have hPeq : P = fun w => (cataR S) xs w := hAP
  subst hPeq
  obtain ⟨hmem_gen, hdom⟩ := (est_apply R _ (foldFn xs)).mp hmax
  -- `hmem_gen`: the fold output is itself generatable → achievability via `gen_spec`.
  -- `hdom`   : it R-dominates every generatable pair → domination via `spec_gen` + `hR2`.
  refine ⟨gen_spec xs (foldFn xs) hmem_gen, ?_⟩
  intro v hv
  obtain ⟨e, hgen⟩ := spec_gen xs v hv
  exact hR2 (foldFn xs) (e, v) (hdom (e, v) hgen)

end SL
end RelSet
end Freyd.Alg
