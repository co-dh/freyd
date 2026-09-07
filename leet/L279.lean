/-
  LeetCode 279 (Perfect Squares) — the minimum number of positive perfect squares summing to
  `v` — SOLVED THROUGH THE GENERIC DP DRIVER `rel.AutoDeriveDP` (the reusability check of
  auto-derive increment 2: a second, fresh instantiation, never hand-verified elsewhere).

  Same abstract skeleton as Coin Change (`leet.L322_dp`): a step-COUNTING DP over the amount
  axis, decomposition = "subtract one square `c²`" — but a PRODUCTIVE one (every amount is a
  sum of `1²`s), so the driver's `∞` fallback is dismissed at the end (`steps_total`) and the
  headline `dpSq_min` is unconditional.  What this file writes is ONLY:

  * the executable: a per-level `omin`-fold over candidate roots (`sqFold`), memoised by the
    driver's generic `memoOf` — no per-problem fuel plumbing, just the one-level body and its
    "reads only below `v`" congruence (`sqBody_congr` → `dpSq_eq`);
  * the fold's two recurrence facts (`sqFold_lb`, `sqFold_mem`);
  * the `DPCount` bundle `sqDP` wiring them up.

  The spec needs no bridge at all: the driver's generic reachability `Steps` IS this
  problem's spec ("`v` is a sum of exactly `n` positive squares").  Everything else — the
  ∞-completed B&dM Theorem 9.1 (`dynamic_programming_inf`), its five hypotheses, the
  `μ(dpBodyInf)` executable bridge, the extremum readback — comes from the driver.

  `omin` and its lemmas are reused from `leet.L322` (their current home).

  Mathlib-free; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import leet.L322
import rel.AutoDeriveDP

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.L279

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC322

/-! ## The executable: an `omin`-fold over candidate roots, memoised by `memoOf` -/

/-- One candidate root's contribution to target `t`: one more square `c²` on top of the
    (memoised, smaller) answer for `t - c²`; no contribution if `c` is invalid. -/
def sqContrib (step : Nat → Option Nat) (t c : Nat) : Option Nat :=
  if 1 ≤ c ∧ c * c ≤ t then (step (t - c * c)).map (· + 1) else none

/-- Fold `omin` over the candidate roots `1..k`. -/
def sqFold (step : Nat → Option Nat) (t : Nat) : Nat → Option Nat
  | 0 => none
  | k + 1 => omin (sqFold step t k) (sqContrib step t (k + 1))

/-- One level of the DP: amount `0` needs `0` squares; amount `t + 1` minimises over the
    roots `1..t+1` (roots above `t + 1` are invalid anyway, since `c ≤ c²`). -/
def sqBody (step : Nat → Option Nat) : Nat → Option Nat
  | 0 => some 0
  | t + 1 => sqFold step (t + 1) (t + 1)

/-- The memoised DP — fuel supplied generically by the driver's `memoOf`. -/
def dpSq : Nat → Option Nat := memoOf none sqBody

theorem sqContrib_congr {s s' : Nat → Option Nat} {t : Nat}
    (h : ∀ w, w < t → s w = s' w) (c : Nat) : sqContrib s t c = sqContrib s' t c := by
  unfold sqContrib
  by_cases hb : 1 ≤ c ∧ c * c ≤ t
  · obtain ⟨hc, hct⟩ := hb
    have h1 : 1 * 1 ≤ c * c := Nat.mul_le_mul hc hc
    rw [if_pos ⟨hc, hct⟩, if_pos ⟨hc, hct⟩, h (t - c * c) (by omega)]
  · rw [if_neg hb, if_neg hb]

theorem sqFold_congr {s s' : Nat → Option Nat} {t : Nat}
    (h : ∀ w, w < t → s w = s' w) : ∀ k, sqFold s t k = sqFold s' t k
  | 0 => rfl
  | k + 1 => by
    show omin (sqFold s t k) (sqContrib s t (k + 1))
        = omin (sqFold s' t k) (sqContrib s' t (k + 1))
    rw [sqFold_congr h k, sqContrib_congr h (k + 1)]

/-- The body reads the memo only below `v` — the sole obligation `memoOf` asks for. -/
theorem sqBody_congr : ∀ (s s' : Nat → Option Nat) (v : Nat),
    (∀ w, w < v → s w = s' w) → sqBody s v = sqBody s' v
  | s, s', 0, h => rfl
  | s, s', t + 1, h => sqFold_congr h (t + 1)

/-- The fuel-free recurrence, from the driver's generic `memoOf_eq`. -/
theorem dpSq_eq (v : Nat) : dpSq v = sqBody dpSq v := memoOf_eq sqBody_congr v

/-! ## The fold's recurrence facts -/

theorem omin_ole_left : ∀ x y : Option Nat, ole (omin x y) x
  | none, _ => trivial
  | some m, none => Nat.le_refl m
  | some m, some n => by
    show (if m ≤ n then m else n) ≤ m
    split <;> omega

theorem omin_ole_right : ∀ x y : Option Nat, ole (omin x y) y
  | none, y => ole_refl y
  | some _, none => trivial
  | some m, some n => by
    show (if m ≤ n then m else n) ≤ n
    split <;> omega

/-- Lower bound: the fold is `ole`-below every valid root's contribution. -/
theorem sqFold_lb {s : Nat → Option Nat} {t c : Nat} (hpos : 1 ≤ c) (hct : c * c ≤ t) :
    ∀ k, c ≤ k → ole (sqFold s t k) ((s (t - c * c)).map (· + 1))
  | 0, hck => absurd hck (by omega)
  | k + 1, hck => by
    rcases Nat.lt_or_ge c (k + 1) with hlt | hge
    · exact ole_trans (omin_ole_left _ _) (sqFold_lb hpos hct k (by omega))
    · have hc : c = k + 1 := by omega
      have hcontrib : sqContrib s t (k + 1) = (s (t - c * c)).map (· + 1) := by
        unfold sqContrib
        rw [← hc]
        exact if_pos ⟨hpos, hct⟩
      rw [← hcontrib]
      exact omin_ole_right _ _

/-- Membership: the fold is `∞`, or some valid root achieves it. -/
theorem sqFold_mem {s : Nat → Option Nat} {t : Nat} :
    ∀ k, sqFold s t k = none
      ∨ ∃ c, 1 ≤ c ∧ c ≤ k ∧ c * c ≤ t ∧ sqFold s t k = (s (t - c * c)).map (· + 1)
  | 0 => Or.inl rfl
  | k + 1 => by
    have hred : sqFold s t (k + 1) = omin (sqFold s t k) (sqContrib s t (k + 1)) := rfl
    rcases omin_eq_or (sqFold s t k) (sqContrib s t (k + 1)) with he | he
    · rw [he] at hred
      rcases sqFold_mem k with hn | ⟨c, h1, h2, h3, h4⟩
      · exact Or.inl (hred.trans hn)
      · exact Or.inr ⟨c, h1, by omega, h3, hred.trans h4⟩
    · rw [he] at hred
      by_cases hb : 1 ≤ k + 1 ∧ (k + 1) * (k + 1) ≤ t
      · refine Or.inr ⟨k + 1, hb.1, Nat.le_refl _, hb.2, ?_⟩
        rw [hred]
        unfold sqContrib
        exact if_pos hb
      · refine Or.inl ?_
        rw [hred]
        unfold sqContrib
        exact if_neg hb

/-! ## The bundle -/

/-- Perfect Squares' creative content, bundled for the generic ∞-DP driver: the decomposition
    (base `v = 0`; step = subtract one positive square `c²`), the executable, and the
    recurrence facts of its `omin`-fold. -/
def sqDP : DPCount Unit Nat Nat where
  tbase := fun _ v => v = 0
  tstep := fun c v' v => 1 ≤ c ∧ c * c ≤ v ∧ v' = v - c * c
  memo := dpSq
  meas := fun v => v
  meas_lt := fun {c v' v} h => by
    obtain ⟨hpos, hct, hv'⟩ := h
    have h1 : 1 * 1 ≤ c * c := Nat.mul_le_mul hpos hpos
    omega
  memo_lb_base := fun {d v} h => by
    subst h
    exact Nat.le_refl 0
  memo_lb_step := fun {c v' v} h => by
    obtain ⟨hpos, hct, hv'⟩ := h
    subst hv'
    have h1 : 1 * 1 ≤ c * c := Nat.mul_le_mul hpos hpos
    obtain ⟨t, rfl⟩ : ∃ t, v = t + 1 := ⟨v - 1, by omega⟩
    rw [dpSq_eq]
    have h2 : 1 * c ≤ c * c := Nat.mul_le_mul hpos (Nat.le_refl c)
    exact sqFold_lb hpos hct (t + 1) (by omega)
  memo_mem := fun v => by
    cases v with
    | zero => exact Or.inl ⟨(), rfl, rfl⟩
    | succ t =>
      rcases sqFold_mem (s := dpSq) (t := t + 1) (t + 1) with hn | ⟨c, h1, h2, h3, h4⟩
      · exact Or.inr (Or.inr ((dpSq_eq (t + 1)).trans hn))
      · exact Or.inr (Or.inl ⟨c, t + 1 - c * c, ⟨h1, h3, rfl⟩, (dpSq_eq (t + 1)).trans h4⟩)

/-! ## The headline (the spec IS the driver's generic `Steps`/`countSpec`) -/

/-- Every amount is a sum of squares (`v` copies of `1²`) — the productive-branch witness
    that the `∞` fallback never fires for Perfect Squares. -/
theorem steps_total (v : Nat) : Steps sqDP.tbase sqDP.tstep v v := by
  induction v with
  | zero => exact Steps.base (d := ()) rfl
  | succ n ih => exact Steps.step ih ⟨Nat.le_refl 1, by omega, by omega⟩

/-- **Headline**: `dpSq v` computes `some` the ≤-MINIMUM number of positive perfect squares
    summing to `v` — `countSpec`'s `∞` case dismissed by `steps_total`.  Everything but the
    fold facts above comes from `CL.DPCount.correct` (the ∞-DP driver). -/
theorem dpSq_min (v : Nat) :
    ∃ n, dpSq v = some n ∧ Steps sqDP.tbase sqDP.tstep n v
      ∧ ∀ n', Steps sqDP.tbase sqDP.tstep n' v → n ≤ n' := by
  have h : countSpec sqDP.tbase sqDP.tstep v (dpSq v) := sqDP.correct v
  cases hval : dpSq v with
  | none =>
    rw [hval] at h
    exact absurd (steps_total v) (h v)
  | some n =>
    rw [hval] at h
    exact ⟨n, rfl, h.1, h.2⟩

example : dpSq 4 = some 1 := by decide   -- 4
example : dpSq 8 = some 2 := by decide   -- 4 + 4
example : dpSq 7 = some 4 := by decide   -- 4 + 1 + 1 + 1

end Freyd.Alg.RelSet.L279
