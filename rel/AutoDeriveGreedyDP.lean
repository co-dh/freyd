/-
  AUTO-DERIVE, increment 2: the GREEDY-DP pattern (B&dM Theorem 10.1), mechanised.

  `A10_1.greedy_dp` says: a recursion that at each step commits to ONE `Q`-minimum
  decomposition of the input (`h·FX·min Q·ΛT°`) still refines the global optimisation spec
  `min R·ΛH`, `H = ⦇h⦈·⦇T⦈°` — greedy as the extreme case of dynamic programming.  Using it on
  a concrete problem needs (cf. `leet.L322_dp`, the DP analogue done by hand): the abstract
  hypothesis discharges (`Map h`, `MonotonicAlg`, transitivity, and the thinning bound `hQ`),
  an executable-side bridge (the greedy PROGRAM's graph lands inside `μ(greedy body)`), and a
  pointwise readback of the abstract spec.  None of that plumbing is problem-specific.

  `GreedyDP L E S W` discharges it ONCE, generically, over the cons-shaped pattern functor
  `F X = L + E × X` (`Freyd.A6_ConsList`): a problem state `S` either bottoms out at a leaf
  `L` or decomposes into a choice `E` plus a smaller state.  The bundle's CREATIVE inputs are

  * `baseP`/`stepP`    — the decomposition relation `T` (the search space);
  * `hbase`/`hstep`    — the refold algebra `h` (how a solution is priced);
  * `Rp`               — the value order (`Rp z x` = "x at least as good as z", min convention);
  * `Up`/`Vp`          — the Birelator orders giving `Q = G(U,V)` (B&dM p.246 / Prop 9.4):
                         `Up` compares choices, `Vp` compares residual states;
  * `pick`/`meas`      — the greedy CHOICE function and its termination measure —

  plus one-line routine facts (`Rp_refl/trans`, `Up_refl`, `step_mono`, `pick_*`) and ONE real
  lemma, `exch` — the greedy-exchange property "a `Vp`-better residual admits a no-worse
  completion".  From these the driver

  1. discharges `hQ` through Proposition 9.4's Birelator reduction (`birelator_thin_condition`
     at the concrete sum birelator `sumBirel`, so `hQ` never appears to the user: only the
     componentwise `hU` (from `Up_refl`+`step_mono`) and `hV` (from `exch`) do);
  2. DERIVES the greedy program `run` from `pick` by well-founded recursion on `meas`, and
     proves its graph lives inside `μ(greedy body)` (`run_mem_mu`);
  3. emits pointwise correctness `correct`/`correct_spec` ("the greedy result is the value of
     some decomposition and `Rp`-dominates the value of every decomposition") and the
     morphism headline `eq_est` (`graph run = est R°·ΛH` on the nose, given antisymmetry).

  HONESTY: the split is genuinely creative-vs-plumbing, but `exch` is NOT componentwise — it
  quantifies over all decompositions of a residual state (it IS the problem's greedy-choice
  property; Prop 9.4 reduces `hQ` to it but cannot make it smaller).  Demo: canonical coin
  change over {1, 5} at the end of this file.  No existing `leet/L*.lean` is a greedy-as-
  extreme-DP instance, so the demo is synthetic — see the closing note.

  Mathlib-free.  Axioms ⊆ {propext, Classical.choice, Quot.sound} (`Classical.choice` enters
  only through the abstract power transpose `Λ`, which picks its classifier — same cost as
  every §7-§10 instantiation).
-/
import AOP.A10_1
import AOP.A6_ConsList
import rel.AutoDeriveDP

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.GD

open Freyd

/-! ## The sum birelator `G(Y, X) = L + Y × X`

  The concrete `Birelator` (B&dM p.223, `Freyd.A9_1`) whose left slot carries the greedy
  CHOICE and whose right slot carries the residual state; `G.fixLeft ⟨E⟩` is exactly the
  cons-list pattern functor `CL.F L E` (`sumBirel_fixLeft_map`), which is what lets
  Proposition 9.4 discharge `greedy_dp`'s `hQ` on cons-shaped problems. -/

/-- The sum-product birelator on `Rel(Set)`: `G(y, x) = L + y × x`, acting as the identity on
    the leaf summand and componentwise on the product. -/
def sumBirel (L : Type) : Birelator RelSet.{0} where
  obj y x := ⟨L ⊕ (y.carrier × x.carrier)⟩
  map {a b c d} R T := fun u v => match u, v with
    | Sum.inl l, Sum.inl l' => l = l'
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ T p.2 q.2
    | _, _ => False
  map_id a c := hom_ext fun u v => by
    cases u <;> cases v
    · exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
    · next l q => exact ⟨False.elim, fun h => nomatch (show Sum.inl l = Sum.inr q from h)⟩
    · next p l => exact ⟨False.elim, fun h => nomatch (show Sum.inr p = Sum.inl l from h)⟩
    · next p q =>
      exact ⟨fun ⟨h1, h2⟩ => congrArg Sum.inr (Prod.ext h1 h2),
        fun h => by cases Sum.inr.inj h; exact ⟨rfl, rfl⟩⟩
  map_comp R R' T T' := hom_ext fun u v => by
    cases u with
    | inl l => cases v with
      | inl l' => exact ⟨fun h => ⟨Sum.inl l, rfl, h⟩,
          fun ⟨w, h1, h2⟩ => by cases w with
            | inl m => exact h1.trans h2
            | inr q => exact h1.elim⟩
      | inr q => exact ⟨False.elim, fun ⟨w, h1, h2⟩ => by cases w with
          | inl m => exact h2.elim
          | inr m => exact h1.elim⟩
    | inr p => cases v with
      | inl l' => exact ⟨False.elim, fun ⟨w, h1, h2⟩ => by cases w with
          | inl m => exact h1.elim
          | inr m => exact h2.elim⟩
      | inr q =>
        exact ⟨fun ⟨⟨m1, hR, hR'⟩, m2, hT, hT'⟩ =>
            ⟨Sum.inr (m1, m2), ⟨hR, hT⟩, ⟨hR', hT'⟩⟩,
          fun ⟨w, h1, h2⟩ => by cases w with
            | inl m => exact h1.elim
            | inr m => exact ⟨⟨m.1, h1.1, h2.1⟩, m.2, h1.2, h2.2⟩⟩
  map_mono {a b c d R R' T T'} hR hT := le_iff.mpr fun u v => by
    cases u <;> cases v
    · exact id
    · exact False.elim
    · exact False.elim
    · exact fun ⟨h1, h2⟩ => ⟨le_iff.mp hR _ _ h1, le_iff.mp hT _ _ h2⟩

/-- `sumBirel` preserves converse — the hypothesis Prop 9.4's thinning reduction needs. -/
theorem sumBirel_preservesRecip (L : Type) : (sumBirel L).PreservesRecip := by
  intro a b c d R T
  apply hom_ext; intro u v
  cases u <;> cases v
  · exact ⟨Eq.symm, Eq.symm⟩
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

/-- Freezing `sumBirel`'s left slot at the identity IS the cons-list pattern functor's action:
    `G(id_E, X) = (CL.F L E).map X`.  The bridge along which `birelator_fixLeft_mono` and
    `birelator_thin_condition` (Prop 9.4) discharge `greedy_dp`'s hypotheses at `F := CL.F L E`. -/
theorem sumBirel_fixLeft_map {L E : Type} {c c' : RelSet.{0}} (X : c ⟶ c') :
    (sumBirel L).map (Cat.id (CL.dE E)) X = (CL.F L E).map X := by
  apply hom_ext; intro u v
  cases u <;> cases v
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

/-! ## Decompositions and their values, concretely

  A decomposition tree of a state is a cons-list of choices ending in a leaf; its value is the
  refold of the algebra.  These are the pointwise readings of `⦇T⦈°` and `⦇h⦈` — the two
  halves of B&dM's `H`. -/

/-- `decT baseP stepP ℓ v` — the choice list `ℓ` is a full decomposition of the state `v`
    (pointwise `cataFold T ℓ v`, `decT_pt`). -/
def decT {L E S : Type} (baseP : L → S → Prop) (stepP : E → S → S → Prop) :
    CL.ConsList L E → S → Prop
  | CL.ConsList.wrap l => baseP l
  | CL.ConsList.cons c t => fun v => ∃ w, decT baseP stepP t w ∧ stepP c w v

/-- `foldA hbase hstep ℓ` — the value of the decomposition `ℓ` under the refold algebra
    (pointwise `cataFold h`, `foldA_pt`). -/
def foldA {L E W : Type} (hbase : L → W) (hstep : E → W → W) : CL.ConsList L E → W
  | CL.ConsList.wrap l => hbase l
  | CL.ConsList.cons c t => hstep c (foldA hbase hstep t)

/-! ## The bundle of creative inputs -/

/-- The creative inputs of a greedy-as-extreme-DP derivation (B&dM Theorem 10.1 over the
    pattern functor `F X = L + E × X`), plus the routine facts its side conditions reduce to.
    `S` = problem states, `W` = solution values, `L` = leaf data, `E` = per-step choices.

    Everything except `exch` is a one-liner on a concrete problem.  `exch` is the problem's
    greedy-choice property — the one genuinely creative proof (see the header note). -/
structure GreedyDP (L E S W : Type) where
  /-- Base decompositions: `baseP l v` = state `v` bottoms out with leaf data `l`. -/
  baseP : L → S → Prop
  /-- Step decompositions: `stepP c w v` = state `v` decomposes into choice `c` + residual `w`. -/
  stepP : E → S → S → Prop
  /-- Value of a leaf. -/
  hbase : L → W
  /-- Value of a choice combined with the residual's value. -/
  hstep : E → W → W
  /-- The value order, min convention: `Rp z x` = "`x` is at least as good as `z`". -/
  Rp : (⟨W⟩ : RelSet.{0}) ⟶ ⟨W⟩
  /-- The Birelator order on choices (only reflexivity is ever used, B&dM p.246). -/
  Up : CL.dE E ⟶ CL.dE E
  /-- The Birelator order on residual states: `Vp w' w` = "`w` is at least as promising as
      `w'`" — the greedy residual must `Vp`-dominate every alternative residual. -/
  Vp : (⟨S⟩ : RelSet.{0}) ⟶ ⟨S⟩
  /-- The greedy choice: THE decomposition committed to at each step (the program's decision). -/
  pick : S → L ⊕ E × S
  /-- Termination measure for the greedy recursion. -/
  meas : S → Nat
  Rp_refl : ∀ x, Rp x x
  Rp_trans : ∀ {x y z}, Rp x y → Rp y z → Rp x z
  Up_refl : ∀ c, Up c c
  /-- The algebra is monotone, componentwise (Prop 9.4's `hU`, pointwise). -/
  step_mono : ∀ {c c' x x'}, Up c c' → Rp x x' → Rp (hstep c x) (hstep c' x')
  /-- The greedy choice is a genuine decomposition (leaf case). -/
  pick_base : ∀ {v l}, pick v = Sum.inl l → baseP l v
  /-- The greedy choice is a genuine decomposition (step case). -/
  pick_step : ∀ {v c w}, pick v = Sum.inr (c, w) → stepP c w v
  /-- The greedy residual is smaller — termination. -/
  pick_dec : ∀ {v c w}, pick v = Sum.inr (c, w) → meas w < meas v
  /-- `Q`-minimality of the greedy choice, leaf case: a base decomposition forces the pick. -/
  pick_min_base : ∀ {v l}, baseP l v → pick v = Sum.inl l
  /-- `Q`-minimality of the greedy choice, step case: the pick `G(U,V)`-dominates every
      alternative decomposition. -/
  pick_min_step : ∀ {v c' w'}, stepP c' w' v →
    ∃ c w, pick v = Sum.inr (c, w) ∧ Up c' c ∧ Vp w' w
  /-- The greedy-exchange property (Prop 9.4's `hV`, pointwise): a `Vp`-better state admits,
      for every decomposition of the worse one, a decomposition of no worse value. -/
  exch : ∀ {w u}, Vp w u → ∀ ℓ, decT baseP stepP ℓ w →
    ∃ ℓ', decT baseP stepP ℓ' u ∧ Rp (foldA hbase hstep ℓ) (foldA hbase hstep ℓ')

namespace GreedyDP

variable {L E S W : Type}

/-! ## The derived relational data -/

/-- The decomposition relation as the algebra `T : F S ⟶ S` (its converse is the coalgebra
    `greedy_dp` unfolds by). -/
def TRel (P : GreedyDP L E S W) : (CL.F L E).obj ⟨S⟩ ⟶ (⟨S⟩ : RelSet.{0}) := fun t v =>
  match t with
  | Sum.inl l => P.baseP l v
  | Sum.inr (c, w) => P.stepP c w v

/-- The refold algebra as a function. -/
def hFn (P : GreedyDP L E S W) : (CL.Fobj L E (⟨W⟩ : RelSet.{0})).carrier → W
  | Sum.inl l => P.hbase l
  | Sum.inr (c, x) => P.hstep c x

/-- The refold algebra as a map in `Rel(Set)`. -/
def hAlg (P : GreedyDP L E S W) : (CL.F L E).obj ⟨W⟩ ⟶ (⟨W⟩ : RelSet.{0}) := graph P.hFn

/-- The thinning order `Q := G(U, V)` on decompositions (B&dM p.246). -/
def Qrel (P : GreedyDP L E S W) : CL.Fobj L E ⟨S⟩ ⟶ CL.Fobj L E ⟨S⟩ :=
  (sumBirel L).map (a := CL.dE E) (b := CL.dE E) (c := ⟨S⟩) (d := ⟨S⟩) P.Up P.Vp

/-- B&dM's optimisation-problem relation `H = ⦇h⦈·⦇T⦈°`, mirrored. -/
def specH (P : GreedyDP L E S W) : (⟨S⟩ : RelSet.{0}) ⟶ ⟨W⟩ :=
  (relCata P.TRel)° ≫ relCata P.hAlg

/-! ## Pointwise readings of the two catamorphisms -/

theorem decT_pt (P : GreedyDP L E S W) : ∀ (ℓ : CL.ConsList L E) (v : S),
    CL.cataFold P.TRel ℓ v ↔ decT P.baseP P.stepP ℓ v
  | CL.ConsList.wrap l, v => Iff.rfl
  | CL.ConsList.cons c t, v =>
    ⟨fun ⟨w, hw, hs⟩ => ⟨w, (decT_pt P t w).mp hw, hs⟩,
     fun ⟨w, hw, hs⟩ => ⟨w, (decT_pt P t w).mpr hw, hs⟩⟩

theorem foldA_pt (P : GreedyDP L E S W) : ∀ (ℓ : CL.ConsList L E) (x : W),
    CL.cataFold P.hAlg ℓ x ↔ x = foldA P.hbase P.hstep ℓ
  | CL.ConsList.wrap l, x => Iff.rfl
  | CL.ConsList.cons c t, x => by
    constructor
    · rintro ⟨r', hr', hx⟩
      rw [(foldA_pt P t r').mp hr'] at hx
      exact hx
    · intro hx
      exact ⟨_, (foldA_pt P t _).mpr rfl, hx⟩

/-- The hylomorphism identified: `H v x` iff `x` is the value of some decomposition of `v`. -/
theorem specH_pt (P : GreedyDP L E S W) (v : S) (x : W) :
    P.specH v x ↔ ∃ ℓ, decT P.baseP P.stepP ℓ v ∧ x = foldA P.hbase P.hstep ℓ := by
  show ((relCata P.TRel)° ≫ relCata P.hAlg) v x ↔ _
  rw [← CL.cataR_eq_relCata, ← CL.cataR_eq_relCata]
  constructor
  · rintro ⟨ℓ, hT, hh⟩
    exact ⟨ℓ, (P.decT_pt ℓ v).mp hT, (P.foldA_pt ℓ x).mp hh⟩
  · rintro ⟨ℓ, hT, hx⟩
    exact ⟨ℓ, (P.decT_pt ℓ v).mpr hT, (P.foldA_pt ℓ x).mpr hx⟩

/-! ## Abstract-side hypothesis discharges (the Prop 9.4 Birelator route) -/

/-- Prop 9.4's `hU`, from the componentwise facts: `G(U,R)·h ⊑ h·R` mirrored. -/
theorem hU (P : GreedyDP L E S W) :
    (sumBirel L).map P.Up P.Rp ≫ P.hAlg ⊑ P.hAlg ≫ P.Rp := by
  rw [le_iff]; rintro t y ⟨u, hGu, hy⟩
  have hy' : y = P.hFn u := hy
  subst hy'
  refine ⟨P.hFn t, rfl, ?_⟩
  cases t with
  | inl l => cases u with
    | inl l' =>
      have hll : l = l' := hGu
      subst hll
      exact P.Rp_refl _
    | inr q => exact hGu.elim
  | inr p => cases u with
    | inl l' => exact hGu.elim
    | inr q =>
      obtain ⟨c, x⟩ := p; obtain ⟨c', x'⟩ := q
      exact P.step_mono hGu.1 hGu.2

/-- `id ⊑ U`, from reflexivity of `Up`. -/
theorem hUrefl (P : GreedyDP L E S W) : Cat.id (CL.dE E) ⊑ P.Up := by
  rw [le_iff]; intro c c' h
  have hcc : c = c' := h
  subst hcc
  exact P.Up_refl c

/-- Transitivity of the value order, as a composition bound. -/
theorem htrans (P : GreedyDP L E S W) : P.Rp ≫ P.Rp ⊑ P.Rp := by
  rw [le_iff]; rintro x z ⟨y, h1, h2⟩
  exact P.Rp_trans h1 h2

/-- Prop 9.4's `hV`, from the greedy-exchange property: `V°·H ⊑ H·R°` mirrored. -/
theorem hV (P : GreedyDP L E S W) : P.Vp° ≫ P.specH ⊑ P.specH ≫ P.Rp° := by
  rw [le_iff]; rintro u x ⟨w, hVwu, hH⟩
  obtain ⟨ℓ, hd, hx⟩ := (P.specH_pt w x).mp hH
  obtain ⟨ℓ', hd', hR⟩ := P.exch hVwu ℓ hd
  refine ⟨foldA P.hbase P.hstep ℓ', (P.specH_pt u _).mpr ⟨ℓ', hd', rfl⟩, ?_⟩
  show P.Rp x (foldA P.hbase P.hstep ℓ')
  rw [hx]
  exact hR

/-- `MonotonicAlg h R` for the pattern functor, via Prop 9.4(i) (`birelator_fixLeft_mono`). -/
theorem hmono (P : GreedyDP L E S W) : MonotonicAlg (F := CL.F L E) P.hAlg P.Rp := by
  have h := birelator_fixLeft_mono (G := sumBirel L) (e := CL.dE E)
    (h := P.hAlg) (R := P.Rp) (U := P.Up) P.hUrefl P.hU
  show (CL.F L E).map P.Rp ≫ P.hAlg ⊑ P.hAlg ≫ P.Rp
  rwa [sumBirel_fixLeft_map] at h

/-- `greedy_dp`'s thinning-compatibility bound `hQ`, via Prop 9.4(ii)
    (`birelator_thin_condition` at `Q := G(U,V)`) — the whole point of the Birelator route:
    the user never sees `hQ`, only `Up_refl`/`step_mono`/`exch`. -/
theorem hQ (P : GreedyDP L E S W) :
    P.Qrel° ≫ (CL.F L E).map P.specH ≫ P.hAlg
      ⊑ (CL.F L E).map P.specH ≫ P.hAlg ≫ P.Rp° := by
  have h := birelator_thin_condition (G := sumBirel L) (e := CL.dE E) (h := P.hAlg)
    (H := P.specH) (R := P.Rp°) (U := P.Up°) (V := P.Vp°)
    (birelator_mono_recip (sumBirel_preservesRecip L) (graph_map P.hFn) P.hU) P.hV
  rw [sumBirel_preservesRecip L P.Up P.Vp] at h
  rwa [sumBirel_fixLeft_map] at h

/-! ## The abstract refinement (Theorem 10.1, instantiated) -/

/-- The greedy recursion body `h·FX·min Q·ΛT°`, mirrored. -/
def body (P : GreedyDP L E S W) (X : (⟨S⟩ : RelSet.{0}) ⟶ ⟨W⟩) :
    (⟨S⟩ : RelSet.{0}) ⟶ ⟨W⟩ :=
  Λ (P.TRel°) ≫ est P.Qrel° ≫ (CL.F L E).map X ≫ P.hAlg

/-- **Theorem 10.1, auto-instantiated**: the greedy recursion refines `min R·ΛH`. -/
theorem greedy_refine (P : GreedyDP L E S W) :
    mu P.body ⊑ Λ P.specH ≫ est P.Rp° := by
  -- `greedy_dp` runs at `R := Rp°` (the conclusion's `est Rp°`), so conjugate `hmono`/`htrans`
  have htrans' : P.Rp° ≫ P.Rp° ⊑ P.Rp° := by
    have h0 := recip_mono P.htrans
    rwa [Allegory.recip_comp] at h0
  exact greedy_dp (F := CL.F L E) (T := P.TRel) (Q := P.Qrel°) (h := P.hAlg) (R := P.Rp°)
    (CL.F_preservesRecip L E) (CL.initial L E) (graph_map P.hFn)
    ((monotonicAlg_recip_iff (graph_map P.hFn) (CL.F_preservesRecip L E)).mp P.hmono) htrans' P.hQ

/-! ## The derived program and the executable-side bridge -/

/-- The greedy PROGRAM, derived from `pick` by well-founded recursion on `meas`: commit to the
    greedy decomposition, recurse on the residual, refold. -/
def run (P : GreedyDP L E S W) (v : S) : W :=
  match hp : P.pick v with
  | Sum.inl l => P.hbase l
  | Sum.inr (c, w) => P.hstep c (P.run w)
termination_by P.meas v
decreasing_by exact P.pick_dec hp

theorem run_base (P : GreedyDP L E S W) {v : S} {l : L} (hp : P.pick v = Sum.inl l) :
    P.run v = P.hbase l := by
  rw [run.eq_def]
  split
  · next l' heq =>
    rw [hp] at heq
    exact congrArg P.hbase (Sum.inl.inj heq).symm
  · next c w heq =>
    rw [hp] at heq
    nomatch heq

theorem run_step (P : GreedyDP L E S W) {v : S} {c : E} {w : S}
    (hp : P.pick v = Sum.inr (c, w)) : P.run v = P.hstep c (P.run w) := by
  rw [run.eq_def]
  split
  · next l heq =>
    rw [hp] at heq
    nomatch heq
  · next c' w' heq =>
    rw [hp] at heq
    injection heq with h
    injection h with h1 h2
    subst h1; subst h2
    rfl

theorem body_monotonic (P : GreedyDP L E S W) : Monotonic P.body :=
  fun h => comp_mono_left _ (comp_mono_left _ (comp_mono_right ((CL.F L E).map_mono h) _))

/-- One unfolding of the bridge: `run v` inhabits the greedy body at any `X` that already
    contains `run`'s graph on `meas`-smaller states — the greedy pick is a `Q`-minimum of the
    full decomposition set (`pick_min_*`), the residual recursion is `X` (induction), the
    refold is `hFn`. -/
theorem run_mem_body (P : GreedyDP L E S W) {X : (⟨S⟩ : RelSet.{0}) ⟶ ⟨W⟩} (v : S)
    (hsub : ∀ w, P.meas w < P.meas v → X w (P.run w)) :
    P.body X v (P.run v) := by
  obtain ⟨Pset, hPset⟩ := entire_total (Λ_is_map' (P.TRel°)).1 v
  have hmem : ∀ t, Pset t ↔ P.TRel t v := fun t => CL.Λ_pt (P.TRel°) hPset t
  refine ⟨Pset, hPset, P.pick v, (est_apply P.Qrel° Pset (P.pick v)).mpr ⟨?_, ?_⟩, ?_⟩
  · -- the pick is a member of the decomposition set
    refine (hmem (P.pick v)).mpr ?_
    cases hp : P.pick v with
    | inl l => exact P.pick_base hp
    | inr q =>
      obtain ⟨c, w⟩ := q
      exact P.pick_step hp
  · -- ... and `Q`-dominates every member
    intro t ht
    have hT : P.TRel t v := (hmem t).mp ht
    cases t with
    | inl l =>
      rw [P.pick_min_base (show P.baseP l v from hT)]
      exact rfl
    | inr q =>
      obtain ⟨c', w'⟩ := q
      obtain ⟨c, w, hp, hu, hv⟩ := P.pick_min_step (show P.stepP c' w' v from hT)
      rw [hp]
      exact ⟨hu, hv⟩
  · -- refolding the recursively solved pick yields `run v`
    cases hp : P.pick v with
    | inl l => exact ⟨Sum.inl l, rfl, P.run_base hp⟩
    | inr q =>
      obtain ⟨c, w⟩ := q
      exact ⟨Sum.inr (c, P.run w), ⟨rfl, hsub w (P.pick_dec hp)⟩, P.run_step hp⟩

/-- **The executable-side bridge**: the greedy program's graph is inside the least fixed
    point of the greedy body — strong induction on the measure, one `mu_fixed` unfolding per
    level. -/
theorem run_mem_mu (P : GreedyDP L E S W) (v : S) : mu P.body v (P.run v) := by
  have haux : ∀ (n : Nat) (v : S), P.meas v ≤ n → mu P.body v (P.run v) := by
    intro n
    induction n with
    | zero =>
      intro v hv
      rw [← mu_fixed P.body_monotonic]
      exact P.run_mem_body v
        (fun w hw => absurd (Nat.lt_of_lt_of_le hw hv) (Nat.not_lt_zero _))
    | succ n ih =>
      intro v hv
      rw [← mu_fixed P.body_monotonic]
      exact P.run_mem_body v (fun w hw => ih w (by omega))
  exact haux (P.meas v) v (Nat.le_refl _)

/-! ## The drivers: pointwise correctness and the morphism headline -/

/-- **Auto-derived extremum correctness**: the greedy result is the value of SOME
    decomposition, and it `Rp`-dominates the value of EVERY decomposition. -/
theorem correct (P : GreedyDP L E S W) (v : S) :
    (∃ ℓ, decT P.baseP P.stepP ℓ v ∧ foldA P.hbase P.hstep ℓ = P.run v)
    ∧ ∀ ℓ, decT P.baseP P.stepP ℓ v → P.Rp (foldA P.hbase P.hstep ℓ) (P.run v) := by
  obtain ⟨Pset, hPset, hmin⟩ := le_iff.mp P.greedy_refine v (P.run v) (P.run_mem_mu v)
  have hmem : ∀ z, Pset z ↔ P.specH v z := fun z => CL.Λ_pt P.specH hPset z
  obtain ⟨hm, hlb⟩ := (est_apply P.Rp° Pset (P.run v)).mp hmin
  constructor
  · obtain ⟨ℓ, hd, hx⟩ := (P.specH_pt v (P.run v)).mp ((hmem _).mp hm)
    exact ⟨ℓ, hd, hx.symm⟩
  · intro ℓ hd
    exact hlb (foldA P.hbase P.hstep ℓ)
      ((hmem _).mpr ((P.specH_pt v _).mpr ⟨ℓ, hd, rfl⟩))

/-- `correct`, transported along a problem-level specification: given the (problem-specific)
    characterisation "spec = value of some decomposition", the greedy result satisfies the
    spec and `Rp`-dominates every spec value. -/
theorem correct_spec (P : GreedyDP L E S W) (spec : S → W → Prop)
    (dec_spec : ∀ v ℓ, decT P.baseP P.stepP ℓ v → spec v (foldA P.hbase P.hstep ℓ))
    (spec_dec : ∀ v y, spec v y → ∃ ℓ, decT P.baseP P.stepP ℓ v ∧ foldA P.hbase P.hstep ℓ = y)
    (v : S) : spec v (P.run v) ∧ ∀ y, spec v y → P.Rp y (P.run v) := by
  obtain ⟨⟨ℓ, hd, hx⟩, hlb⟩ := P.correct v
  refine ⟨hx ▸ dec_spec v ℓ hd, fun y hy => ?_⟩
  obtain ⟨ℓ', hd', hy'⟩ := spec_dec v y hy
  exact hy' ▸ hlb ℓ' hd'

/-- **The morphism headline**: the derived greedy program IS `min R·ΛH` as a morphism of
    `Rel(Set)` (given antisymmetry of the value order), not merely pointwise. -/
theorem eq_est (P : GreedyDP L E S W)
    (antisym : ∀ {x y}, P.Rp x y → P.Rp y x → x = y) :
    (graph P.run : (⟨S⟩ : RelSet.{0}) ⟶ ⟨W⟩) = Λ P.specH ≫ est P.Rp° := by
  apply hom_ext; intro v x
  constructor
  · rintro rfl
    exact le_iff.mp P.greedy_refine v (P.run v) (P.run_mem_mu v)
  · intro h
    obtain ⟨Pset, hPset, hmin⟩ := h
    have hmem : ∀ z, Pset z ↔ P.specH v z := fun z => CL.Λ_pt P.specH hPset z
    obtain ⟨hm, hlb⟩ := (est_apply P.Rp° Pset x).mp hmin
    obtain ⟨⟨ℓ, hd, hx⟩, hRlb⟩ := P.correct v
    obtain ⟨ℓ', hd', hx'⟩ := (P.specH_pt v x).mp ((hmem x).mp hm)
    have h1 : P.Rp x (P.run v) := hx' ▸ hRlb ℓ' hd'
    have h2 : P.Rp (P.run v) x :=
      hlb (P.run v) ((hmem _).mpr ((P.specH_pt v _).mpr ⟨ℓ, hd, hx.symm⟩))
    show x = P.run v
    exact antisym h1 h2

end GreedyDP

/-! ## Demo: canonical coin change over {1, 5}

  Make change for `v` with coins 1 and 5 using as few coins as possible; the greedy rule
  "always take a 5 while you can" is optimal because {1, 5} is a canonical system.  A greedy-
  as-extreme-DP instance: at each state one decomposition (the largest coin) is committed to.

  The creative content below: the greedy rule (`pick15`), the residual order `Vp` = "smaller
  optimal count" (`cnt` = the closed form `v/5 + v%5`), and the two inductions behind the
  exchange property — `dec15_lb` (every decomposition uses at least `cnt` coins) and
  `dec15_greedy` (some decomposition attains `cnt`).  Everything else is one-line. -/

namespace Coins15

open GreedyDP

/-- Base decomposition: only the state 0 bottoms out. -/
def base15 (_ : Unit) (v : Nat) : Prop := v = 0
/-- Step decomposition: remove one coin (1 or 5). -/
def step15 (c w v : Nat) : Prop := (c = 1 ∨ c = 5) ∧ v = w + c
/-- Leaf value: zero coins. -/
def hbase15 (_ : Unit) : Nat := 0
/-- Step value: one more coin. -/
def hstep15 (_ : Nat) (x : Nat) : Nat := x + 1
/-- The optimal coin count for {1, 5} — the closed form the greedy achieves. -/
def cnt (v : Nat) : Nat := v / 5 + v % 5
/-- The greedy rule: take a 5 while possible, else a 1, bottoming out at 0. -/
def pick15 (v : Nat) : Unit ⊕ Nat × Nat :=
  if v = 0 then Sum.inl () else if 5 ≤ v then Sum.inr (5, v - 5) else Sum.inr (1, v - 1)

theorem pick15_hi {v : Nat} (h : 5 ≤ v) : pick15 v = Sum.inr (5, v - 5) := by
  unfold pick15
  rw [if_neg (by omega), if_pos h]

theorem pick15_lo {v : Nat} (h0 : v ≠ 0) (h5 : ¬ 5 ≤ v) : pick15 v = Sum.inr (1, v - 1) := by
  unfold pick15
  rw [if_neg h0, if_neg h5]

/-- LOWER BOUND: every decomposition of `u` uses at least `cnt u` coins (each coin is worth
    at most 5). -/
theorem dec15_lb : ∀ (ℓ : CL.ConsList Unit Nat) (u : Nat),
    decT base15 step15 ℓ u → cnt u ≤ foldA hbase15 hstep15 ℓ
  | CL.ConsList.wrap l, u, h => by
    have hu : u = 0 := h
    subst hu
    show cnt 0 ≤ hbase15 l
    simp [cnt, hbase15]
  | CL.ConsList.cons c t, u, h => by
    obtain ⟨w, hw, hc, hu⟩ := h
    have ih := dec15_lb t w hw
    subst hu
    show cnt (w + c) ≤ foldA hbase15 hstep15 t + 1
    simp only [cnt] at ih ⊢
    rcases hc with rfl | rfl <;> omega

/-- ACHIEVABILITY: the greedy decomposition of `u` uses exactly `cnt u` coins. -/
theorem dec15_greedy (u : Nat) : ∃ ℓ : CL.ConsList Unit Nat,
    decT base15 step15 ℓ u ∧ foldA hbase15 hstep15 ℓ = cnt u := by
  have haux : ∀ (n u : Nat), u ≤ n →
      ∃ ℓ, decT base15 step15 ℓ u ∧ foldA hbase15 hstep15 ℓ = cnt u := by
    intro n
    induction n with
    | zero =>
      intro u hu
      have h0 : u = 0 := Nat.le_zero.mp hu
      subst h0
      exact ⟨CL.ConsList.wrap (), rfl, rfl⟩
    | succ n ih =>
      intro u hu
      rcases Nat.lt_or_ge u 5 with h5 | h5
      · rcases Nat.eq_zero_or_pos u with h0 | h0
        · subst h0
          exact ⟨CL.ConsList.wrap (), rfl, rfl⟩
        · obtain ⟨ℓ, hd, hf⟩ := ih (u - 1) (by omega)
          refine ⟨CL.ConsList.cons 1 ℓ, ⟨u - 1, hd, Or.inl rfl, by omega⟩, ?_⟩
          show foldA hbase15 hstep15 ℓ + 1 = cnt u
          rw [hf]
          simp only [cnt]
          omega
      · obtain ⟨ℓ, hd, hf⟩ := ih (u - 5) (by omega)
        refine ⟨CL.ConsList.cons 5 ℓ, ⟨u - 5, hd, Or.inr rfl, by omega⟩, ?_⟩
        show foldA hbase15 hstep15 ℓ + 1 = cnt u
        rw [hf]
        simp only [cnt]
        omega
  exact haux u u (Nat.le_refl u)

/-- The {1, 5} coin-change greedy bundle — all of the algorithm's content in one place. -/
def coins15 : GreedyDP Unit Nat Nat Nat where
  baseP := base15
  stepP := step15
  hbase := hbase15
  hstep := hstep15
  Rp := fun z x => x ≤ z
  Up := fun _ _ => True
  Vp := fun w' w => cnt w ≤ cnt w'
  pick := pick15
  meas := fun v => v
  Rp_refl x := Nat.le_refl x
  Rp_trans h1 h2 := Nat.le_trans h2 h1
  Up_refl _ := trivial
  step_mono _ h := Nat.succ_le_succ h
  pick_base := by
    intro v l hp
    unfold pick15 at hp
    split at hp
    · next h => exact h
    · next h => split at hp <;> nomatch hp
  pick_step := by
    intro v c w hp
    unfold pick15 at hp
    split at hp
    · nomatch hp
    · next h0 =>
      split at hp
      · next h5 =>
        injection hp with h
        injection h with h1 h2
        subst h1; subst h2
        exact ⟨Or.inr rfl, by omega⟩
      · next h5 =>
        injection hp with h
        injection h with h1 h2
        subst h1; subst h2
        exact ⟨Or.inl rfl, by omega⟩
  pick_dec := by
    intro v c w hp
    unfold pick15 at hp
    split at hp
    · nomatch hp
    · next h0 =>
      split at hp
      · next h5 =>
        injection hp with h
        injection h with h1 h2
        subst h2
        show v - 5 < v
        omega
      · next h5 =>
        injection hp with h
        injection h with h1 h2
        subst h2
        show v - 1 < v
        omega
  pick_min_base := by
    intro v l h
    have hv : v = 0 := h
    subst hv
    cases l
    rfl
  pick_min_step := by
    intro v c' w' h
    obtain ⟨hc, hv⟩ := h
    rcases Nat.lt_or_ge v 5 with h5 | h5
    · rcases hc with rfl | rfl
      · refine ⟨1, v - 1, pick15_lo (by omega) (by omega), trivial, ?_⟩
        show cnt (v - 1) ≤ cnt w'
        have hw : w' = v - 1 := by omega
        rw [hw]
        exact Nat.le_refl _
      · exact absurd hv (by omega)
    · refine ⟨5, v - 5, pick15_hi h5, trivial, ?_⟩
      show cnt (v - 5) ≤ cnt w'
      rcases hc with rfl | rfl <;> (simp only [cnt]; omega)
  exch := by
    intro w u hV ℓ hd
    obtain ⟨ℓ', hd', hf'⟩ := dec15_greedy u
    have hV' : cnt u ≤ cnt w := hV
    have hlb := dec15_lb ℓ w hd
    refine ⟨ℓ', hd', ?_⟩
    show foldA hbase15 hstep15 ℓ' ≤ foldA hbase15 hstep15 ℓ
    omega

/-! ### The auto-derived results -/

/-- Problem-level specification: `n` coins from {1, 5} (a ones, b fives) make up `v`. -/
def spendable (v n : Nat) : Prop := ∃ a b, v = a + 5 * b ∧ n = a + b

theorem dec15_spendable : ∀ (ℓ : CL.ConsList Unit Nat) (v : Nat),
    decT base15 step15 ℓ v → spendable v (foldA hbase15 hstep15 ℓ)
  | CL.ConsList.wrap l, v, h => by
    have hv : v = 0 := h
    exact ⟨0, 0, by omega, rfl⟩
  | CL.ConsList.cons c t, v, h => by
    obtain ⟨w, hw, hc, hv⟩ := h
    obtain ⟨a, b, hab, hn⟩ := dec15_spendable t w hw
    rcases hc with rfl | rfl
    · exact ⟨a + 1, b, by omega, by show foldA hbase15 hstep15 t + 1 = a + 1 + b; omega⟩
    · exact ⟨a, b + 1, by omega, by show foldA hbase15 hstep15 t + 1 = a + (b + 1); omega⟩

theorem spendable_dec15 : ∀ (a b v : Nat), v = a + 5 * b →
    ∃ ℓ, decT base15 step15 ℓ v ∧ foldA hbase15 hstep15 ℓ = a + b := by
  intro a
  induction a with
  | zero =>
    intro b
    induction b with
    | zero =>
      intro v hv
      subst hv
      exact ⟨CL.ConsList.wrap (), rfl, rfl⟩
    | succ b ihb =>
      intro v hv
      obtain ⟨ℓ, hd, hf⟩ := ihb (5 * b) (by omega)
      refine ⟨CL.ConsList.cons 5 ℓ, ⟨5 * b, hd, Or.inr rfl, by omega⟩, ?_⟩
      show foldA hbase15 hstep15 ℓ + 1 = 0 + (b + 1)
      omega
  | succ a iha =>
    intro b v hv
    obtain ⟨ℓ, hd, hf⟩ := iha b (a + 5 * b) rfl
    refine ⟨CL.ConsList.cons 1 ℓ, ⟨a + 5 * b, hd, Or.inl rfl, by omega⟩, ?_⟩
    show foldA hbase15 hstep15 ℓ + 1 = (a + 1) + b
    omega

/-- **Auto-derived correctness of the {1, 5} greedy coin changer**: the derived program
    `coins15.run` produces an achievable coin count and no achievable count beats it. -/
theorem coins15_correct (v : Nat) :
    spendable v (coins15.run v) ∧ ∀ n, spendable v n → coins15.run v ≤ n :=
  coins15.correct_spec spendable
    (fun v ℓ hd => dec15_spendable ℓ v hd)
    (fun v n hn => by
      obtain ⟨a, b, hv, hnab⟩ := hn
      subst hnab
      exact spendable_dec15 a b v hv)
    v

/-- The derived greedy program computes the closed form (extremum uniqueness). -/
theorem run_eq_cnt (v : Nat) : coins15.run v = cnt v := by
  obtain ⟨⟨ℓ, hd, hf⟩, hlb⟩ := coins15.correct v
  obtain ⟨ℓ', hd', hf'⟩ := dec15_greedy v
  have h1 : coins15.run v ≤ foldA hbase15 hstep15 ℓ' := hlb ℓ' hd'
  have h2 : cnt v ≤ foldA hbase15 hstep15 ℓ := dec15_lb ℓ v hd
  have hf2 : foldA hbase15 hstep15 ℓ = coins15.run v := hf
  omega

/-- **The §7.5-style morphism headline, auto-derived**: the greedy program IS `min R·ΛH` as a
    morphism of `Rel(Set)`. -/
theorem coins15_eq_est :
    (graph coins15.run : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨Nat⟩)
      = Λ coins15.specH ≫ est coins15.Rp° :=
  coins15.eq_est fun h1 h2 => Nat.le_antisymm h2 h1

example : coins15.run 12 = 4 := by rw [run_eq_cnt]; rfl
example : coins15.run 137 = 29 := by rw [run_eq_cnt]; rfl
example : coins15.run 0 = 0 := by rw [run_eq_cnt]; rfl

#eval coins15.run 12    -- 4  (5 + 5 + 1 + 1)
#eval coins15.run 137   -- 29 (27 fives + 2 ones)

end Coins15

/-! ## Reuse note (honesty): why the demo is synthetic, and why that is unavoidable here

  This driver was parked on branch `held/greedy-dp-driver` (synthetic-only) and merged to master
  for completeness: Theorem 10.1 is now INSTANTIABLE end-to-end, at the price of one structure,
  even though no LeetCode case study is a clean instance.  `coins15` above (canonical coin change
  over `{1,5}`, minimise the coin count) is a synthetic demo built for this file; it is the
  driver's natural shape — a `min·Λ` optimisation over the linear decomposition `F X = L + E×X`,
  greedy-optimal because the coin system is canonical.

  No existing `leet/L*.lean` case study fits this driver, and the reason is structural, not a
  gap in the corpus.  Every genuinely-greedy LeetCode problem lands in one of three buckets:

  * Already served by the greedy Theorem 7.2 / thinning route with a DIFFERENT shape — Kadane/L53
    and best-trade/L121 are `RunningBest` folds; L45/L55/L435/L763 are `consFold_unique`
    catamorphism scans.  Re-deriving any of these through this driver would only DUPLICATE work.
  * Stateful-feasibility greedy — e.g. LeetCode 860 (Lemonade Change).  Its greedy content lives
    in a forward-threaded bill inventory, but this driver's algebra `hstep : E → W → W` prices a
    decomposition bottom-up and never sees the state; encoding L860 forces `W = Inv → Option Inv`
    (a state-transformer with a dominance `Rp` and a transformer-valued `exch`), and its
    infeasible/stuck states violate the driver's totality (`pick` must always decompose).  A poor
    fit, checked explicitly.
  * Non-canonical → genuine DP — L322 (general coin change) is the DP driver's instance
    (`dynamic_programming_inf`), greedy is provably WRONG there; L279 likewise.

  The driver's unique niche is the CANONICAL coin system, and LeetCode ships only the general
  (L322) version.  So the honest state is: this file makes Theorem 10.1 instantiable and stands
  ready for the first real pick-the-best-decomposition problem (activity selection over an
  interval-set state; the concrete §10.3 tardiness / §10.4 paragraph problems), on `coins15`
  meanwhile.  `A10_3_Tardiness`/`A10_4_TeX` only RESTATE `greedy_dp` with the same generic
  hypotheses; before this file the theorem had zero concrete instances. -/

end Freyd.Alg.RelSet.GD
