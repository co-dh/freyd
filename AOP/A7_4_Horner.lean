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
public import AOP.A7_2

set_option linter.unusedVariables false

namespace Freyd.Alg

universe u

/-! ## Abstract: greedy-from-refinement with monotonicity stated on `R` -/

section Abstract
variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-- **`A7_2.greedy_of_refinement` with monotonicity on `R` instead of `R°`.**  A deterministic
    algebra `f` (a map), MONOTONIC on the order `R`, that REFINES the greedy choice
    `Λ S ≫ est R`, already has its catamorphism inside `est R·Λ⦇S⦈` — the Pareto frontier of
    the plain non-deterministic catamorphism `⦇S⦈`.  Transitivity and monotonicity are
    transposed to `R°` by `recip_mono`/`monotonicAlg_recip_iff` (the latter needs `f` a map). -/
public theorem greedy_of_refinement_mono (hFr : F.PreservesRecip) (I : InitialAlgebra F) {R : a ⟶ a}
    {S f : F.obj a ⟶ a} (hf : Map f) (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg f R)
    (href : f ⊑ S%∋ ≫ est(R)) : ⦇f⦈ ⊑ ⦇S⦈%∋ ≫ est(R) := by
  have htrans' : R° ≫ R° ⊑ R° := by
    have h := recip_mono htrans; rwa [Allegory.recip_comp] at h
  have hmono' : MonotonicAlg f R° := (monotonicAlg_recip_iff hf hFr).mp hmono
  exact greedy_of_refinement hFr I htrans' hmono' href

end Abstract

/-! ## Concrete Rel(Set) helpers: `Λ` is the classifier, and `est` pointwise -/

namespace RelSet

/-- In Rel(Set) the transpose `Λ` is the concrete `classifier` (graph of `x ↦ {y | R x y}`):
    both are maps whose composition with `∋` is `R`, and that map is unique. -/
public theorem Λ_eq_classifier {b c : RelSet.{0}} (R : c ⟶ b) : Λ R = classifier R :=
  ((Λ_UP R (f := classifier R) (graph_map _)).mpr (classifier_comp_eps R)).symm

/-- Pointwise form of `est` in Rel(Set): `w` is a `est R`-choice of the set `P` iff
    `w ∈ P` and `w` `R`-dominates every member `z ∈ P` (`R w z`). -/
public theorem est_apply {a : RelSet.{0}} (R : a ⟶ a)
    (P : (PowerAllegory.powerObj a).carrier) (w : a.carrier) :
    (est R) P w ↔ P w ∧ ∀ z, P z → R w z := Iff.rfl

/-- Pointwise form of `Λ T ≫ est R` ((7.5) unbundled): `w` is an `est R`-choice over the
    `T`-image of `x` iff `T x w` and `w` `R`-dominates every `T`-image `z` of `x`. -/
public theorem Λ_comp_est_apply {b a : RelSet.{0}} (T : b ⟶ a) (R : a ⟶ a) (x : b.carrier)
    (w : a.carrier) : (Λ T ≫ est R) x w ↔ T x w ∧ ∀ z, T x z → R w z := by
  rw [Λ_eq_classifier]
  constructor
  · rintro ⟨P, hP, hest⟩
    have hPeq : P = fun v => T x v := hP
    subst hPeq
    exact (est_apply R _ w).mp hest
  · rintro ⟨hT, hall⟩
    exact ⟨fun v => T x v, rfl, (est_apply R _ w).mpr ⟨hT, hall⟩⟩

/-- Pointwise form of `E R` in Rel(Set): the `E R`-image of a set `P` is the set of all
    `R`-images of its members. -/
public theorem existsImage_apply {a b : RelSet.{0}} (R : a ⟶ b) (P : (pow a).carrier)
    (Q : (pow b).carrier) : existsImage R P Q ↔ Q = fun w => ∃ s, P s ∧ R s w := by
  show Λ (epsRel a ≫ R) P Q ↔ _
  rw [Λ_eq_classifier]
  exact Iff.rfl

/-- Pointwise form of `E T ≫ est R`: `w` is an `est R`-choice over the `T`-images of the members
    of `P` iff some member has `w` as a `T`-image and `w` `R`-dominates every such image. -/
public theorem existsImage_comp_est_apply {a b : RelSet.{0}} (T : a ⟶ b) (R : b ⟶ b)
    (P : (pow a).carrier) (w : b.carrier) :
    (existsImage T ≫ est R) P w
      ↔ (∃ s, P s ∧ T s w) ∧ ∀ z, (∃ s, P s ∧ T s z) → R w z := by
  constructor
  · rintro ⟨Q, hQ, hest⟩
    have hQeq : Q = fun v => ∃ s, P s ∧ T s v := (existsImage_apply T P Q).mp hQ
    subst hQeq
    exact (est_apply R _ w).mp hest
  · intro h
    exact ⟨_, (existsImage_apply T P _).mpr rfl, (est_apply R _ w).mpr h⟩

/-! ## Honest headline: a deterministic solver IS `Λspec ≫ est D`

  This is the bridge that lets an optimization case study state its headline as the actual
  morphism equation `solve = Λ spec ≫ est D` (§7.5's `max D · Λ spec`), instead of only in
  prose.  It consumes exactly the two halves the case study already proves — achievability
  (`hsound`) and domination (`hbest`) — plus antisymmetry of the preference order `D`, which
  pins the maximum uniquely so `solve` (a map) equals it. -/

/-- **Morphism-equation headline for a maximization solver.**  If `solveFn` always produces a
    `spec`-value (`hsound`) that `D`-dominates every `spec`-value (`hbest`), and the preference
    order `D` is antisymmetric, then `graph solveFn = Λ spec ≫ est D` — the program is exactly
    `max D · Λ spec` as a relation, not merely pointwise.  For a `≤`-maximum take `D w z := z ≤ w`;
    for a `≤`-minimum take `D w z := w ≤ z` (`est` of the reversed order). -/
public theorem eq_Λ_comp_est {d : RelSet.{0}} {V : Type} (D : (⟨V⟩ : RelSet.{0}) ⟶ ⟨V⟩)
    (hanti : ∀ x y : V, D x y → D y x → x = y)
    (solveFn : d.carrier → V) (spec : d ⟶ (⟨V⟩ : RelSet.{0}))
    (hsound : ∀ xs, spec xs (solveFn xs))
    (hbest : ∀ xs v, spec xs v → D (solveFn xs) v) :
    (graph solveFn : d ⟶ (⟨V⟩ : RelSet.{0})) = Λ spec ≫ est D := by
  apply hom_ext; intro xs w
  rw [comp_apply]
  constructor
  · intro hw
    have hwe : w = solveFn xs := hw
    subst hwe
    refine ⟨fun v => spec xs v, ?_, (est_apply D _ _).mpr ⟨hsound xs, hbest xs⟩⟩
    rw [Λ_eq_classifier]; rfl
  · rintro ⟨P, hAP, hmax⟩
    rw [Λ_eq_classifier] at hAP
    have hPeq : P = fun v => spec xs v := hAP
    subst hPeq
    obtain ⟨hmem, hdomw⟩ := (est_apply D _ _).mp hmax
    exact hanti w (solveFn xs) (hdomw (solveFn xs) (hsound xs)) (hbest xs w hmem)

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
