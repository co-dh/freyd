/-
  AUTO-DERIVE, increment 2: the memoised dynamic-programming pattern, mechanised.

  `AOP.A9_2.dynamic_programming_inf` (the ∞-completed B&dM Theorem 9.1) certifies a memoised
  DP against the optimisation spec `min R · Λ(H ∪ τ)` from three abstract hypotheses plus the
  ∞-extras — but turning its `μ(body) ⊑ spec` into POINTWISE correctness of an EXECUTABLE memo
  function costs a large hand-written packaging per problem (`leet.L322_dp` before this file:
  order/monotonicity/strictness discharges, a ~110-line `powerRel`/`μ`-membership bridge, a
  spec readback).  None of that packaging touches the problem: it consumes only the memo
  function's RECURRENCE SHAPE ("the memo value is a candidate — or the fallback — and
  lower-bounds every candidate") and one-line order/algebra facts.

  This file discharges it ONCE, generically, for DPs whose one-step decomposition has the
  cons-list shape `F X = L + (E × X)` (`AOP.A6_ConsList`): a base case, or one ingredient
  `E` plus one smaller subproblem.  `DPInf L E B Ans` bundles the CREATIVE inputs —

  * `tbase`, `tstep`   — the decomposition relation (the coalgebra-converse `T`);
  * `hbase`, `hstep`   — the refold algebra `h` (how a decomposition's value is assembled);
  * `le`, `top`        — the value order and its adjoined `∞` (the fallback for dead branches);
  * `memo`, `meas`     — the executable memo function and its termination measure —

  together with one-line order facts (`le_refl`/`le_trans`/`le_top`), the algebra's
  monotonicity and STRICTNESS at `∞` (`hstep_mono`/`hstep_strict` — strictness is the
  shape-specific sufficient condition that discharges the abstract `hstrict` wholesale), and
  the memo recurrence (`memo_lb_*`/`memo_mem`).  From these, `DPInf.correct` emits

      (Hpt v (memo v) ∨ memo v = top)  ∧  ∀ x, Hpt v x → le (memo v) x

  — `memo v` is a `le`-minimum of the hylomorphism values `Hpt v` (all decompose-and-refold
  results), with `top` exactly when there are none — every abstract hypothesis of
  `dynamic_programming_inf` (`Map h`, `MonotonicAlg`, `R·R ⊑ R`, `hstrict`, `hτ`), the
  executable-side bridge `memo ⊑ μ(dpBodyInf)` and the spec readback discharged internally.

  Two further reusable layers:
  * `memoOf` — fuel-supplied memoisation over a `Nat` axis: a new DP writes only its one-level
    body and a "reads only below `v`" congruence; the fuel plumbing is generic.
  * `DPCount` — the COUNTING specialisation (`Ans = Option Nat`, `none = ∞`, value = number of
    decomposition steps): order and algebra fields disappear entirely, and
    `DPCount.correct` reads back as `countSpec` — "`memo v` is `some` the ≤-minimum number of
    `tstep`-steps from `v` to a base (`Steps`), `none` if unreachable".

  What remains HUMAN, per problem: choosing `tbase`/`tstep` (the decomposition — the
  algorithmic insight), the memo function itself, its three recurrence facts (extracted from
  the executable's one-level fold), and — when the problem has its own spec vocabulary —
  relating `Steps` to it.  Demos: `leet.L322_dp` (coin change, re-derivation, ∞ live) and
  `leet.L279` (perfect squares, fresh productive-branch instance).

  Mathlib-free.  Axioms ⊆ {propext, Classical.choice, Quot.sound}, inherited from the
  `Rel(Set)` power-allegory instance (the hand-written packaging this file replaces had the
  same set, despite its header's claim).
-/
import AOP.A6_ConsList
import AOP.A9_2

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.CL

open Freyd

/-! ## Pointwise (`Rel(Set)`) readings of the power-allegory operations

  `powerRel`, `minRel`, `leftDiv` and `∋` all unfold definitionally in `Rel(Set)`; `Λ` does
  not (it is a symmetric division), so its content is extracted through `Λ_eps_eq'` +
  `Λ_is_map'` instead.  (Shared home; previously private to `leet.L322_dp`.) -/

theorem powerRel_pt {α β : RelSet.{0}} (g : α ⟶ β) (P : (pow α).carrier)
    (Q : (pow β).carrier) :
    powerRel g P Q ↔
      (∀ t, P t → ∃ u, g t u ∧ Q u) ∧ (∀ u, Q u → ∃ t, P t ∧ g t u) :=
  Iff.rfl

theorem minRel_pt {α : RelSet.{0}} (R : α ⟶ α) (P : (pow α).carrier) (x : α.carrier) :
    minRel R P x ↔ P x ∧ ∀ z, P z → R z x :=
  Iff.rfl

theorem lb_pt {α : RelSet.{0}} (R : α ⟶ α) (P : (pow α).carrier) (x : α.carrier) :
    leftDiv ((∋ α)°) R P x ↔ ∀ z, P z → R z x :=
  Iff.rfl

/-- The set a transpose `Λ S` points `x` at contains exactly the `S`-successors of `x`. -/
theorem Λ_pt {α β : RelSet.{0}} (S : α ⟶ β) {x : α.carrier} {P : (pow β).carrier}
    (hP : Λ S x P) (y : β.carrier) : P y ↔ S x y := by
  constructor
  · intro hy
    have h1 : (Λ S ≫ ∋ β) x y := ⟨P, hP, hy⟩
    rw [Λ_eps_eq'] at h1
    exact h1
  · intro hS
    have h1 : (Λ S ≫ ∋ β) x y := by rw [Λ_eps_eq']; exact hS
    obtain ⟨P', hP', hy⟩ := h1
    have hPP : P' = P := simple_uniq (Λ_is_map' S).2 hP' hP
    rw [← hPP]
    exact hy

/-! ## Fuel-supplied memoisation over a `Nat` axis

  The executable side of a value-axis DP is usually written with an explicit FUEL bound
  (structural recursion, kernel-reducible; cf. `leet.L322.dpFuel`), then every proof pays a
  fuel-irrelevance lemma.  `memoOf` pays it once: a problem supplies its one-level `body` and
  the congruence "`body s v` reads `s` only below `v`", and gets the memo function plus its
  fuel-free unfolding `memoOf_eq`. -/

/-- `body`, iterated `f + 1` levels deep (the innermost level sees the constant `dflt`). -/
def memoFuel {Ans : Type} (dflt : Ans) (body : (Nat → Ans) → Nat → Ans) : Nat → Nat → Ans
  | 0, v => body (fun _ => dflt) v
  | f + 1, v => body (memoFuel dflt body f) v

/-- The memo function: at each point, exactly enough fuel. -/
def memoOf {Ans : Type} (dflt : Ans) (body : (Nat → Ans) → Nat → Ans) (v : Nat) : Ans :=
  memoFuel dflt body v v

/-- Fuel irrelevance: any sufficient fuel computes the same value. -/
theorem memoFuel_congr {Ans : Type} {dflt : Ans} {body : (Nat → Ans) → Nat → Ans}
    (hcong : ∀ (s s' : Nat → Ans) (v : Nat),
      (∀ w, w < v → s w = s' w) → body s v = body s' v) :
    ∀ f f' v, v ≤ f → v ≤ f' → memoFuel dflt body f v = memoFuel dflt body f' v := by
  intro f
  induction f with
  | zero =>
    intro f' v hv hv'
    obtain rfl : v = 0 := Nat.le_zero.mp hv
    cases f' with
    | zero => rfl
    | succ f'' => exact hcong _ _ 0 (fun w hw => absurd hw (Nat.not_lt_zero w))
  | succ fn ih =>
    intro f' v hv hv'
    cases f' with
    | zero =>
      obtain rfl : v = 0 := Nat.le_zero.mp hv'
      exact hcong _ _ 0 (fun w hw => absurd hw (Nat.not_lt_zero w))
    | succ f'' => exact hcong _ _ v (fun w hw => ih f'' w (by omega) (by omega))

/-- The fuel-free unfolding: `memoOf` satisfies the body's recurrence verbatim. -/
theorem memoOf_eq {Ans : Type} {dflt : Ans} {body : (Nat → Ans) → Nat → Ans}
    (hcong : ∀ (s s' : Nat → Ans) (v : Nat),
      (∀ w, w < v → s w = s' w) → body s v = body s' v)
    (v : Nat) : memoOf dflt body v = body (memoOf dflt body) v := by
  cases v with
  | zero => exact hcong _ _ 0 (fun w hw => absurd hw (Nat.not_lt_zero w))
  | succ n =>
    show body (memoFuel dflt body n) (n + 1) = body (memoOf dflt body) (n + 1)
    exact hcong _ _ (n + 1)
      (fun w hw => memoFuel_congr hcong n w w (by omega) (Nat.le_refl w))

/-! ## The bundle of creative inputs -/

/-- The creative inputs of a memoised ∞-DP over the cons-list decomposition shape
    `F X = L + (E × X)`, plus the one-line facts its mechanical side conditions reduce to.
    A problem `v : B` either bottoms out (`tbase d v`) or decomposes into one ingredient
    `e : E` and one smaller subproblem `v'` (`tstep e v' v`); a solution's value is refolded
    by `hbase`/`hstep`; `le` orders values (smaller = better) with `top` the adjoined `∞`
    ("no solution", covering DEAD branches — the case B&dM Theorem 9.1 cannot express);
    `memo` is the executable, `meas` its termination measure. -/
structure DPInf (L E B Ans : Type) where
  /-- Base decompositions: `v` bottoms out as the leaf `d`. -/
  tbase : L → B → Prop
  /-- Step decompositions: `v` splits into ingredient `e` plus subproblem `v'`. -/
  tstep : E → B → B → Prop
  /-- Value of a base decomposition. -/
  hbase : L → Ans
  /-- Value of a step: assemble the ingredient with the subproblem's value. -/
  hstep : E → Ans → Ans
  /-- The value order, "smaller = better". -/
  le : Ans → Ans → Prop
  /-- The adjoined `∞`: the fallback value of a dead branch. -/
  top : Ans
  /-- The executable memo function (the PROGRAM). -/
  memo : B → Ans
  /-- Termination measure of the decomposition. -/
  meas : B → Nat
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  /-- `∞` is worst. -/
  le_top : ∀ x, le x top
  /-- The algebra is monotone: a better subproblem value assembles to a better value. -/
  hstep_mono : ∀ (e : E) {x y}, le x y → le (hstep e x) (hstep e y)
  /-- The algebra is STRICT at `∞`: refolding a dead branch stays dead.  (The shape-specific
      sufficient condition that discharges `dynamic_programming_inf`'s `hstrict`.) -/
  hstep_strict : ∀ e, hstep e top = top
  /-- Subproblems are smaller. -/
  meas_lt : ∀ {e v' v}, tstep e v' v → meas v' < meas v
  /-- Recurrence, lower bound: the memo value is `le` every base candidate... -/
  memo_lb_base : ∀ {d v}, tbase d v → le (memo v) (hbase d)
  /-- ... and `le` every step candidate (assembled from the memoised subproblem). -/
  memo_lb_step : ∀ {e v' v}, tstep e v' v → le (memo v) (hstep e (memo v'))
  /-- Recurrence, membership: the memo value is one of the candidates — or the fallback. -/
  memo_mem : ∀ v, (∃ d, tbase d v ∧ memo v = hbase d)
      ∨ (∃ e v', tstep e v' v ∧ memo v = hstep e (memo v'))
      ∨ memo v = top

namespace DPInf

variable {L E B Ans : Type} (P : DPInf L E B Ans)

/-! ## The derived program, decomposition, order and fallback as `Rel(Set)` morphisms -/

/-- The refold algebra as a function `F Ans → Ans`. -/
def algFn : (Fobj L E (⟨Ans⟩ : RelSet.{0})).carrier → Ans
  | Sum.inl d => P.hbase d
  | Sum.inr (e, x) => P.hstep e x

/-- The refold algebra as a map in `Rel(Set)`. -/
def alg : Fobj L E (⟨Ans⟩ : RelSet.{0}) ⟶ (⟨Ans⟩ : RelSet.{0}) := graph P.algFn

/-- The decomposition relation (the coalgebra-converse `T` of `dynamic_programming_inf`). -/
def coalg : Fobj L E (⟨B⟩ : RelSet.{0}) ⟶ (⟨B⟩ : RelSet.{0}) := fun t v =>
  match t with
  | Sum.inl d => P.tbase d v
  | Sum.inr (e, v') => P.tstep e v' v

/-- The value order as a morphism, in `minRel`'s convention (`ord y x` = "`x` at most `y`"). -/
def ord : (⟨Ans⟩ : RelSet.{0}) ⟶ (⟨Ans⟩ : RelSet.{0}) := fun y x => P.le x y

/-- The fallback: the constant-`∞` map. -/
def tau : (⟨B⟩ : RelSet.{0}) ⟶ (⟨Ans⟩ : RelSet.{0}) := graph fun _ => P.top

/-- The optimisation problem's achievability relation `H = ⦇alg⦈·⦇coalg⦈°`, pointwise:
    some full decomposition of `v` refolds to `x`. -/
def Hpt (v : B) (x : Ans) : Prop :=
  ∃ ℓ : ConsList L E, cataFold P.coalg ℓ v ∧ cataFold P.alg ℓ x

/-- The abstract `H` of `dynamic_programming_inf`. -/
def hylo : (⟨B⟩ : RelSet.{0}) ⟶ (⟨Ans⟩ : RelSet.{0}) :=
  (relCata (initial L E) P.coalg)° ≫ relCata (initial L E) P.alg

theorem hylo_pt (v : B) (x : Ans) : P.hylo v x ↔ P.Hpt v x := by
  show ((relCata (initial L E) P.coalg)° ≫ relCata (initial L E) P.alg) v x ↔ _
  rw [← cataR_eq_relCata, ← cataR_eq_relCata]
  exact Iff.rfl

/-! ## The abstract hypotheses of `dynamic_programming_inf`, discharged once -/

/-- `R·R ⊑ R`. -/
theorem ord_trans : P.ord ≫ P.ord ⊑ P.ord := by
  apply le_iff.mpr
  rintro y x ⟨z, hzy, hxz⟩
  exact P.le_trans hxz hzy

/-- `MonotonicAlg h R`, from `le_refl` (base) and `hstep_mono` (step). -/
theorem alg_mono : MonotonicAlg (F := F L E) P.alg P.ord := by
  show (F L E).map P.ord ≫ P.alg ⊑ P.alg ≫ P.ord
  apply le_iff.mpr
  rintro u x ⟨w, hFw, hx⟩
  refine ⟨P.algFn u, rfl, ?_⟩
  have hx' : x = P.algFn w := hx
  cases u with
  | inl d =>
    cases w with
    | inl d' =>
      have hd : d = d' := hFw
      subst hd
      rw [hx']
      exact P.le_refl _
    | inr q => exact hFw.elim
  | inr p =>
    obtain ⟨e, y⟩ := p
    cases w with
    | inl d' => exact hFw.elim
    | inr q =>
      obtain ⟨e', y'⟩ := q
      obtain ⟨hee, hyy⟩ := hFw
      have hee' : e = e' := hee
      subst hee'
      rw [hx']
      exact P.hstep_mono e hyy

/-- `hτ`: the fallback is top-valued — everything is `le` it. -/
theorem tau_top : P.tau° ≫ topHom (⟨B⟩ : RelSet.{0}) (⟨Ans⟩ : RelSet.{0}) ⊑ P.ord := by
  apply le_iff.mpr
  rintro k x ⟨v, hkv, -⟩
  have hk : k = P.top := hkv
  rw [hk]
  exact P.le_top x

/-- `hstrict`: the ∞-extended answer relation `H ∪ τ` absorbs one decompose-solve-fold step.
    All-`H` slots re-thread the decomposition (`cons` one more level onto the witness); a
    fallback slot survives because the algebra is STRICT at `∞` (`hstep_strict`). -/
theorem hstrict : P.coalg° ≫ (F L E).map (P.hylo ∪ P.tau) ≫ P.alg ⊑ P.hylo ∪ P.tau := by
  apply le_iff.mpr
  rintro v x ⟨t, hT, w, hFw, hx⟩
  have hTt : P.coalg t v := hT
  have hx' : x = P.algFn w := hx
  cases t with
  | inl d =>
    cases w with
    | inl d' =>
      have hd : d = d' := hFw
      subst hd
      exact Or.inl ((P.hylo_pt v x).mpr ⟨ConsList.wrap d, hTt, hx'⟩)
    | inr q => exact hFw.elim
  | inr p =>
    obtain ⟨e, v'⟩ := p
    cases w with
    | inl d' => exact hFw.elim
    | inr q =>
      obtain ⟨e', y⟩ := q
      obtain ⟨hee, hSy⟩ := hFw
      have hee' : e = e' := hee
      subst hee'
      have hSy' : P.hylo v' y ∨ P.tau v' y := hSy
      cases hSy' with
      | inl hH =>
        obtain ⟨ℓ', hco', hal'⟩ := (P.hylo_pt v' y).mp hH
        exact Or.inl ((P.hylo_pt v x).mpr
          ⟨ConsList.cons e ℓ', ⟨v', hco', hTt⟩, ⟨y, hal', hx'⟩⟩)
      | inr hτ =>
        refine Or.inr ?_
        show x = P.top
        have hy : y = P.top := hτ
        rw [hx', hy]
        exact P.hstep_strict e

/-! ## The generic executable-side bridge: `memo ⊑ μ(dpBodyInf)` -/

/-- The executable one-step value of a decomposition: refold the memoised subproblem. -/
def stepVal : (Fobj L E (⟨B⟩ : RelSet.{0})).carrier → Ans
  | Sum.inl d => P.hbase d
  | Sum.inr (e, v') => P.hstep e (P.memo v')

/-- **One unfolding of the bridge**: the memo value at `v` inhabits the ∞-DP body at any `X`
    that already contains `memo`'s graph on smaller subproblems.  The Egli–Milner candidate
    set is the `stepVal`-image of the decomposition set; `memo_mem` picks the disjunct
    (a candidate → the `min` disjunct, the fallback → the `τ` disjunct) and `memo_lb_*`
    supply the lower bound in both. -/
theorem memo_mem_body {X : (⟨B⟩ : RelSet.{0}) ⟶ (⟨Ans⟩ : RelSet.{0})} (v : B)
    (hsub : ∀ w, P.meas w < P.meas v → X w (P.memo w)) :
    dpBodyInf (F L E) P.coalg P.alg P.ord P.tau X v (P.memo v) := by
  -- the decomposition set and its content
  obtain ⟨D, hD⟩ := entire_total (Λ_is_map' (P.coalg°)).1 v
  have hDmem : ∀ t, D t ↔ P.coalg t v := fun t => Λ_pt (P.coalg°) hD t
  -- every decomposition's executable value is a genuine `h·FX` candidate
  have hg : ∀ t, D t → ((F L E).map X ≫ P.alg) t (P.stepVal t) := by
    intro t hDt
    cases t with
    | inl d => exact ⟨Sum.inl d, rfl, rfl⟩
    | inr p =>
      obtain ⟨e, v'⟩ := p
      exact ⟨Sum.inr (e, P.memo v'), ⟨rfl, hsub v' (P.meas_lt ((hDmem _).mp hDt))⟩, rfl⟩
  have hpow : powerRel ((F L E).map X ≫ P.alg) D (fun x => ∃ t, D t ∧ x = P.stepVal t) :=
    (powerRel_pt _ _ _).mpr
      ⟨fun t hDt => ⟨P.stepVal t, hg t hDt, t, hDt, rfl⟩,
       fun u hu => by obtain ⟨t, hDt, hut⟩ := hu; exact ⟨t, hDt, hut ▸ hg t hDt⟩⟩
  -- the memo value lower-bounds every candidate
  have hlb : ∀ z, (∃ t, D t ∧ z = P.stepVal t) → P.ord z (P.memo v) := by
    rintro z ⟨t, hDt, rfl⟩
    cases t with
    | inl d => exact P.memo_lb_base ((hDmem _).mp hDt)
    | inr p =>
      obtain ⟨e, v'⟩ := p
      exact P.memo_lb_step ((hDmem _).mp hDt)
  rcases P.memo_mem v with ⟨d, hTd, hval⟩ | ⟨e, v', hTs, hval⟩ | hval
  · exact Or.inl ⟨D, hD, _, hpow,
      (minRel_pt P.ord _ _).mpr ⟨⟨Sum.inl d, (hDmem _).mpr hTd, hval⟩, hlb⟩⟩
  · exact Or.inl ⟨D, hD, _, hpow,
      (minRel_pt P.ord _ _).mpr ⟨⟨Sum.inr (e, v'), (hDmem _).mpr hTs, hval⟩, hlb⟩⟩
  · exact Or.inr ⟨hval, D, hD, _, hpow, (lb_pt P.ord _ _).mpr hlb⟩

/-- **The executable-side bridge**: the memo function's graph is inside the least fixed point
    of the ∞-DP body — induction on the measure (through an explicit fuel bound), one
    `mu_fixed`-unfolding per level, `memo_mem_body` doing each level. -/
theorem memo_mem_mu (v : B) :
    mu (dpBodyInf (F L E) P.coalg P.alg P.ord P.tau) v (P.memo v) := by
  have haux : ∀ f w, P.meas w ≤ f →
      mu (dpBodyInf (F L E) P.coalg P.alg P.ord P.tau) w (P.memo w) := by
    intro f
    induction f with
    | zero =>
      intro w hw
      rw [← mu_fixed (dpBodyInf_monotonic (F L E) P.coalg P.alg P.ord P.tau)]
      exact P.memo_mem_body w
        (fun u hu => absurd (Nat.lt_of_lt_of_le hu hw) (Nat.not_lt_zero _))
    | succ fn ih =>
      intro w hw
      rw [← mu_fixed (dpBodyInf_monotonic (F L E) P.coalg P.alg P.ord P.tau)]
      exact P.memo_mem_body w (fun u hu => ih u (by omega))
  exact haux (P.meas v) v (Nat.le_refl _)

/-! ## The drivers: the abstract theorem instantiated, then read back pointwise -/

/-- **The §9.2-style morphism headline**: the program IS a refinement of the ∞-extended
    optimisation spec `min R · Λ(H ∪ τ)` — `dynamic_programming_inf` with every hypothesis
    discharged by the bundle, composed with the bridge `memo_mem_mu`. -/
theorem solve_le_spec :
    (graph P.memo : (⟨B⟩ : RelSet.{0}) ⟶ (⟨Ans⟩ : RelSet.{0}))
      ⊑ Λ (P.hylo ∪ P.tau) ≫ minRel P.ord := by
  have habs := dynamic_programming_inf (F := F L E) (F_preservesRecip L E) (initial L E)
    (graph_map P.algFn) P.alg_mono P.ord_trans P.hstrict P.tau_top
  apply le_iff.mpr
  intro v x hx
  have hx' : x = P.memo v := hx
  rw [hx']
  exact le_iff.mp habs v (P.memo v) (P.memo_mem_mu v)

/-- **Auto-derived pointwise correctness**: the memo value is a `le`-minimum of the
    achievable values `Hpt v`, with `top` exactly on dead inputs.  This is the whole content
    of the ∞-DP theorem for the bundle; a problem only translates `Hpt` into its own spec
    vocabulary. -/
theorem correct (v : B) :
    (P.Hpt v (P.memo v) ∨ P.memo v = P.top) ∧ ∀ x, P.Hpt v x → P.le (P.memo v) x := by
  have h := le_iff.mp P.solve_le_spec v (P.memo v) rfl
  rw [Λ_comp_minRel] at h
  obtain ⟨hmem, hlb⟩ := h
  constructor
  · rcases hmem with hH | hτ
    · exact Or.inl ((P.hylo_pt v _).mp hH)
    · exact Or.inr hτ
  · intro x hx
    exact hlb x (Or.inl ((P.hylo_pt v x).mpr hx))

end DPInf

/-! ## The counting specialisation: `Ans = Option Nat`, value = number of steps

  Coin-change-style DPs minimise the NUMBER of decomposition steps: the value lattice is
  `Option Nat` with `none = ∞`, the algebra is `some 0` / `Option.map (· + 1)`.  All order and
  algebra fields of `DPInf` are then fixed, and the hylomorphism reads back generically as
  `Steps` (reachability of a base in exactly `n` steps) — so a counting problem supplies ONLY
  its decomposition, memo function, measure and the three recurrence facts. -/

/-- `ole x y` — `≤` on `Option Nat` with `none` the adjoined `∞`/top. -/
def ole (x y : Option Nat) : Prop :=
  match y with
  | none => True
  | some n => match x with
    | some m => m ≤ n
    | none => False

theorem ole_refl : ∀ x, ole x x
  | none => trivial
  | some _ => Nat.le_refl _

theorem ole_trans {x y z : Option Nat} (hxy : ole x y) (hyz : ole y z) : ole x z := by
  match z, hyz with
  | none, _ => trivial
  | some n, hyz =>
    match y, hxy, hyz with
    | none, hxy, hyz => exact hyz.elim
    | some k, hxy, hyz =>
      match x, hxy with
      | none, hxy => exact hxy.elim
      | some m, hxy => exact Nat.le_trans hxy hyz

theorem ole_map_succ {x y : Option Nat} (h : ole x y) :
    ole (x.map (· + 1)) (y.map (· + 1)) := by
  match y, h with
  | none, _ => trivial
  | some n, h =>
    match x, h with
    | none, h => exact h.elim
    | some m, h => exact Nat.succ_le_succ h

/-- `Steps tbase tstep n v` — `v` decomposes to a base case through exactly `n` steps: the
    generic achievability spec of a counting DP. -/
inductive Steps {L E B : Type} (tbase : L → B → Prop) (tstep : E → B → B → Prop) :
    Nat → B → Prop where
  | base {d v} (h : tbase d v) : Steps tbase tstep 0 v
  | step {e v' v n} (h : Steps tbase tstep n v') (hs : tstep e v' v) :
      Steps tbase tstep (n + 1) v

/-- The extremum spec of a counting DP: `some n` is the ≤-minimum step count, `none` means
    no decomposition reaches a base at all. -/
def countSpec {L E B : Type} (tbase : L → B → Prop) (tstep : E → B → B → Prop) (v : B) :
    Option Nat → Prop
  | some n => Steps tbase tstep n v ∧ ∀ n', Steps tbase tstep n' v → n ≤ n'
  | none => ∀ n, ¬ Steps tbase tstep n v

/-- The creative inputs of a step-COUNTING memoised ∞-DP: the decomposition, the executable,
    a measure, and the memo recurrence — nothing else (order and algebra are canonical). -/
structure DPCount (L E B : Type) where
  /-- Base decompositions. -/
  tbase : L → B → Prop
  /-- Step decompositions: `v` splits into ingredient `e` plus subproblem `v'`. -/
  tstep : E → B → B → Prop
  /-- The executable memo function (`none` = "no solution"). -/
  memo : B → Option Nat
  /-- Termination measure of the decomposition. -/
  meas : B → Nat
  meas_lt : ∀ {e v' v}, tstep e v' v → meas v' < meas v
  /-- Recurrence, lower bound: the memo value is `≤` every base candidate... -/
  memo_lb_base : ∀ {d v}, tbase d v → ole (memo v) (some 0)
  /-- ... and `≤` one-more-than every memoised subproblem candidate. -/
  memo_lb_step : ∀ {e v' v}, tstep e v' v → ole (memo v) ((memo v').map (· + 1))
  /-- Recurrence, membership: the memo value is one of the candidates — or `∞`. -/
  memo_mem : ∀ v, (∃ d, tbase d v ∧ memo v = some 0)
      ∨ (∃ e v', tstep e v' v ∧ memo v = (memo v').map (· + 1))
      ∨ memo v = none

namespace DPCount

variable {L E B : Type} (Q : DPCount L E B)

/-- The counting bundle as a full `DPInf`: order/algebra fields canonical, facts discharged. -/
def toDPInf : DPInf L E B (Option Nat) where
  tbase := Q.tbase
  tstep := Q.tstep
  hbase := fun _ => some 0
  hstep := fun _ x => x.map (· + 1)
  le := ole
  top := none
  memo := Q.memo
  meas := Q.meas
  le_refl := ole_refl
  le_trans := ole_trans
  le_top := fun _ => trivial
  hstep_mono := fun _ {_ _} h => ole_map_succ h
  hstep_strict := fun _ => rfl
  meas_lt := Q.meas_lt
  memo_lb_base := Q.memo_lb_base
  memo_lb_step := Q.memo_lb_step
  memo_mem := Q.memo_mem

/-- Number of steps in a decomposition. -/
def clen {L E : Type} : ConsList L E → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons _ t => clen t + 1

/-- The counting algebra always counts: `⦇alg⦈` relates every decomposition to `some` its
    length (never to `∞` — bases start at `some 0` and the successor preserves `some`). -/
theorem count_alg_pt : ∀ (ℓ : ConsList L E) (x : Option Nat),
    cataFold Q.toDPInf.alg ℓ x ↔ x = some (clen ℓ)
  | ConsList.wrap d, x => Iff.rfl
  | ConsList.cons e t, x => by
    show (∃ r', cataFold Q.toDPInf.alg t r' ∧ Q.toDPInf.alg (Sum.inr (e, r')) x)
        ↔ x = some (clen t + 1)
    constructor
    · rintro ⟨r', hr', hx⟩
      rw [(count_alg_pt t r').mp hr'] at hx
      exact hx
    · intro hx
      exact ⟨some (clen t), (count_alg_pt t _).mpr rfl, hx⟩

/-- A decomposition of `v` with `n` steps witnesses `Steps n v`... -/
theorem count_coalg_steps : ∀ (ℓ : ConsList L E) (v : B),
    cataFold Q.toDPInf.coalg ℓ v → Steps Q.tbase Q.tstep (clen ℓ) v
  | ConsList.wrap d, v, h => Steps.base h
  | ConsList.cons e t, v, h => by
    obtain ⟨v', hv', hs⟩ := h
    exact Steps.step (count_coalg_steps t v' hv') hs

/-- ... and conversely: every `Steps` derivation is a decomposition. -/
theorem steps_count_coalg {n : Nat} {v : B} (h : Steps Q.tbase Q.tstep n v) :
    ∃ ℓ : ConsList L E, cataFold Q.toDPInf.coalg ℓ v ∧ clen ℓ = n := by
  induction h with
  | base hb => exact ⟨ConsList.wrap _, hb, rfl⟩
  | step h hs ih =>
    obtain ⟨ℓ, hℓ, hlen⟩ := ih
    exact ⟨ConsList.cons _ ℓ, ⟨_, hℓ, hs⟩, show clen ℓ + 1 = _ + 1 by rw [hlen]⟩

/-- **The hylomorphism identified, once for all counting DPs**: achievable values are exactly
    `some` of the reachability step counts. -/
theorem count_Hpt (v : B) (x : Option Nat) :
    Q.toDPInf.Hpt v x ↔ ∃ n, x = some n ∧ Steps Q.tbase Q.tstep n v := by
  constructor
  · rintro ⟨ℓ, hco, hal⟩
    exact ⟨clen ℓ, (count_alg_pt Q ℓ x).mp hal, count_coalg_steps Q ℓ v hco⟩
  · rintro ⟨n, hx, hst⟩
    obtain ⟨ℓ, hℓ, hlen⟩ := steps_count_coalg Q hst
    exact ⟨ℓ, hℓ, (count_alg_pt Q ℓ x).mpr (by rw [hx, hlen])⟩

/-- **The counting-DP driver headline**: the memo value is `some` the ≤-minimum number of
    decomposition steps, `none` exactly when no decomposition reaches a base. -/
theorem correct (v : B) : countSpec Q.tbase Q.tstep v (Q.memo v) := by
  have hcor := Q.toDPInf.correct v
  have hmem : Q.toDPInf.Hpt v (Q.memo v) ∨ Q.memo v = none := hcor.1
  have hlb : ∀ x, Q.toDPInf.Hpt v x → ole (Q.memo v) x := hcor.2
  cases hval : Q.memo v with
  | some n =>
    have hst : Steps Q.tbase Q.tstep n v := by
      rcases hmem with hH | hnone
      · obtain ⟨n', hn', hst'⟩ := (count_Hpt Q v _).mp hH
        rw [hval] at hn'
        have hnn : n' = n := (Option.some.inj hn').symm
        exact hnn ▸ hst'
      · rw [hval] at hnone
        nomatch hnone
    refine ⟨hst, fun n' hst' => ?_⟩
    have h := hlb (some n') ((count_Hpt Q v _).mpr ⟨n', rfl, hst'⟩)
    rw [hval] at h
    exact h
  | none =>
    intro n hst
    have h := hlb (some n) ((count_Hpt Q v _).mpr ⟨n, rfl, hst⟩)
    rw [hval] at h
    exact h

end DPCount
end Freyd.Alg.RelSet.CL
