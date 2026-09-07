/-
  LeetCode 322 (Coin Change) — correctness RE-DERIVED from the abstract ∞-completed
  dynamic-programming theorem `AOP.A9_2.dynamic_programming_inf`, THROUGH THE GENERIC DP
  DRIVER `rel.AutoDeriveDP` (auto-derive increment 2).

  `leet.L322` proves `coinSpec coins amount (solveFn coins amount)` by a monolithic fuel
  induction, and its closing comment diagnoses WHY B&dM Theorem 9.1 cannot be instantiated
  instead: the Egli–Milner `powerRel` empties the recursion body on dead sub-amounts.  The
  first version of this file closed that gap by hand (~520 lines): pointwise discharges of
  `dynamic_programming_inf`'s five hypotheses, a ~110-line `μ(dpBodyInf)`-membership bridge
  for the fueled `dp`, and a spec readback.  All of that packaging is now the driver's
  business.  What this file supplies is exactly the CREATIVE content, as a `CL.DPCount`
  bundle (coin change is a step-COUNTING DP — value = number of coins, `Option Nat` with
  `none = ∞`, so even the order and refold algebra are canonical):

  * the DECOMPOSITION: an amount bottoms out at `0` (`tbase`) or splits off one valid coin
    `c` leaving `v - c` (`tstep`) — dead amounts have NO decomposition through `tstep`,
    which is exactly what breaks Theorem 9.1 and what the driver's `∞` fallback repairs;
  * the EXECUTABLE `dp` (from `leet.L322`, fuel recursion) with measure the amount itself;
  * the RECURRENCE FACTS: one level of `dp` is a `coinFold`, whose `omin`-fold output is one
    of the one-step candidates or `∞` (`memo_mem`, via `coinFold_achieves`) and is `ole`-below
    every candidate (`memo_lb_step`, via `coinFold_dominates`) — fuel eliminated once by
    `dp_succ` (`dpFuel_congr`);
  * the SPEC BRIDGE: the driver's generic reachability `Steps` is `Achievable`
    (`steps_iff_achievable`, two four-line inductions).

  `solve_correct_inf` — the same statement as before, and as `leet.L322.solve_correct` —
  then falls out of the driver's `DPCount.correct` in a dozen lines.

  Mathlib-free; axioms ⊆ {propext, Classical.choice, Quot.sound} (unchanged from the
  hand-written version — its header understated the set).
-/
import leet.L322
import rel.AutoDeriveDP

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC322

open Freyd Freyd.Alg.RelSet.SL Freyd.Alg.RelSet.CL

/-! ## Fuel elimination: one level of `dp` is a `coinFold` reading `dp` itself -/

theorem contrib_congr {step step' : Nat → Option Nat} {t c : Nat}
    (h : 1 ≤ c → c ≤ t → step (t - c) = step' (t - c)) :
    contrib step t c = contrib step' t c := by
  unfold contrib
  by_cases hb : 1 ≤ c ∧ c ≤ t
  · rw [if_pos hb, if_pos hb, h hb.1 hb.2]
  · rw [if_neg hb, if_neg hb]

theorem coinFold_congr {step step' : Nat → Option Nat} {t : Nat} :
    ∀ cs : SnocList Nat Nat,
      (∀ c, mem cs c → 1 ≤ c → c ≤ t → step (t - c) = step' (t - c)) →
      coinFold step t cs = coinFold step' t cs
  | SnocList.wrap c₀, h => contrib_congr (h c₀ rfl)
  | SnocList.snoc cs c₁, h => by
    show omin (coinFold step t cs) (contrib step t c₁)
        = omin (coinFold step' t cs) (contrib step' t c₁)
    rw [coinFold_congr cs (fun c hm => h c (Or.inl hm)), contrib_congr (h c₁ (Or.inr rfl))]

/-- Fuel irrelevance: any sufficient fuel computes the same value. -/
theorem dpFuel_congr (coins : SnocList Nat Nat) :
    ∀ f f' v, v ≤ f → v ≤ f' → dpFuel coins f v = dpFuel coins f' v := by
  intro f
  induction f with
  | zero =>
    intro f' v hv hv'
    have h0 : v = 0 := Nat.le_zero.mp hv
    subst h0
    cases f' with
    | zero => rfl
    | succ f'' => rfl
  | succ fn ih =>
    intro f' v hv hv'
    match v, hv, hv' with
    | 0, _, _ =>
      cases f' with
      | zero => rfl
      | succ f'' => rfl
    | v' + 1, hv, hv' =>
      cases f' with
      | zero => exact absurd hv' (by omega)
      | succ f'' =>
        show coinFold (dpFuel coins fn) (v' + 1) coins
            = coinFold (dpFuel coins f'') (v' + 1) coins
        apply coinFold_congr
        intro c hm hpos hle
        exact ih f'' (v' + 1 - c) (by omega) (by omega)

/-- One level of `dp`, fuel-free: the recurrence the driver's bundle consumes. -/
theorem dp_succ (coins : SnocList Nat Nat) (v' : Nat) :
    dp coins (v' + 1) = coinFold (dp coins) (v' + 1) coins := by
  show coinFold (dpFuel coins v') (v' + 1) coins = coinFold (dp coins) (v' + 1) coins
  apply coinFold_congr
  intro c hm hpos hle
  exact dpFuel_congr coins v' (v' + 1 - c) (v' + 1 - c) (by omega) (Nat.le_refl _)

/-! ## The bundle: Coin Change as a counting DP -/

/-- Coin Change's creative content, bundled for the generic ∞-DP driver: the decomposition
    (base `v = 0`; step = subtract one valid coin), the executable `dp`, and the recurrence
    facts of its per-level `omin`-fold. -/
def coinDP (coins : SnocList Nat Nat) : DPCount Unit Nat Nat where
  tbase := fun _ v => v = 0
  tstep := fun c v' v => mem coins c ∧ 1 ≤ c ∧ v = v' + c
  memo := dp coins
  meas := fun v => v
  meas_lt := fun {c v' v} h => by
    obtain ⟨-, hpos, hveq⟩ := h
    omega
  memo_lb_base := fun {d v} h => by
    subst h
    exact Nat.le_refl 0
  memo_lb_step := fun {c v' v} h => by
    obtain ⟨hmem, hpos, hveq⟩ := h
    obtain ⟨t, rfl⟩ : ∃ t, v = t + 1 := ⟨v - 1, by omega⟩
    rw [dp_succ]
    cases hv' : dp coins v' with
    | none => exact trivial
    | some mv =>
      obtain ⟨m, hm, hle⟩ := coinFold_dominates coins hmem hpos (by omega)
        (show dp coins (t + 1 - c) = some mv by rw [show t + 1 - c = v' by omega]; exact hv')
      rw [hm]
      exact hle
  memo_mem := fun v => by
    cases v with
    | zero => exact Or.inl ⟨(), rfl, rfl⟩
    | succ v' =>
      cases hres : coinFold (dp coins) (v' + 1) coins with
      | none => exact Or.inr (Or.inr ((dp_succ coins v').trans hres))
      | some m =>
        obtain ⟨c, mv, hmem, hpos, hle, hstep, hmeq⟩ := coinFold_achieves coins hres
        refine Or.inr (Or.inl ⟨c, v' + 1 - c, ⟨hmem, hpos, by omega⟩, ?_⟩)
        rw [dp_succ, hres, hstep]
        exact congrArg some hmeq

/-! ## The spec bridge: the driver's generic reachability is `Achievable` -/

theorem steps_iff_achievable (coins : SnocList Nat Nat) (n v : Nat) :
    Steps (coinDP coins).tbase (coinDP coins).tstep n v ↔ Achievable coins n v := by
  constructor
  · intro h
    induction h with
    | base hb =>
      have hb' : _ = 0 := hb
      subst hb'
      exact Achievable.zero
    | step h hs ih =>
      obtain ⟨hmem, hpos, hveq⟩ := hs
      subst hveq
      exact Achievable.succ ih hmem hpos
  · intro h
    induction h with
    | zero => exact Steps.base (d := ()) rfl
    | succ h hmem hpos ih => exact Steps.step ih ⟨hmem, hpos, rfl⟩

/-! ## The headline: L322 correctness as an instance of the driven ∞-DP theorem -/

/-- **`leet.L322.solve_correct`, re-derived**: `solveFn` computes the `≤`-extremum of the
    achievable coin-count spec — obtained from `Freyd.Alg.dynamic_programming_inf` (the
    abstract ∞-completed dynamic-programming theorem) through the generic driver
    `CL.DPCount.correct`, instantiated at the `coinDP` bundle.  This is the derivation that
    B&dM Theorem 9.1 provably cannot supply (see the closing comment of `leet.L322`). -/
theorem solve_correct_inf (coins : SnocList Nat Nat) (amount : Nat) :
    coinSpec coins amount (solveFn coins amount) := by
  have h : countSpec (coinDP coins).tbase (coinDP coins).tstep amount (dp coins amount) :=
    (coinDP coins).correct amount
  show coinSpec coins amount (dp coins amount)
  cases hval : dp coins amount with
  | none =>
    rw [hval] at h
    intro n hach
    exact h n ((steps_iff_achievable coins n amount).mpr hach)
  | some n =>
    rw [hval] at h
    exact ⟨(steps_iff_achievable coins n amount).mp h.1,
      fun n' hach' => h.2 n' ((steps_iff_achievable coins n' amount).mpr hach')⟩

/-- The exact obstruction instance from `leet.L322`'s analysis: coins {2,3}, amount 3.
    B&dM Theorem 9.1's body is EMPTY here (`μ(body) 3 = 𝟘` — the dead `c = 2` branch leaves
    the unsolvable amount 1 and Egli–Milner term₁ kills the candidate set), yet
    `solve_correct_inf` certifies the executable's `some 1` — the fallback disjunct of
    `dpBodyInf` carries `∞` through the dead branch instead. -/
example : coinSpec (ofList 2 [3]) 3 (some 1) := by
  have h := solve_correct_inf (ofList 2 [3]) 3
  rwa [show solveFn (ofList 2 [3]) 3 = some 1 by decide] at h

end Freyd.Alg.RelSet.LC322
