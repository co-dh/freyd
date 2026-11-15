/-
  LeetCode 367 — Valid Perfect Square — as an ALLEGORY PROGRAM.

  Problem: given `n : ℕ`, decide whether `n` is a perfect square, i.e. whether `∃ k, k*k = n`.

  A DECISION problem (`Bool` answer), same shape as `leet.L217` (Contains Duplicate): the
  program is a `Bool` function, the spec is a `Prop`, and correctness is a plain `iff`, not an
  extremum. Unlike `L217`/`L121` the input is not a list/`SnocList` — it is a single `ℕ`, so (as
  in `leet.L70`) the object is plain `dNat`.

  1. **Program** — `sqFuel fuel k n` searches upward from `k`, testing `k*k = n`, `k*k > n`
     (fail), else recursing to `k+1` with one less fuel unit. FUEL (`leetcode.md` S13) rather than
     well-founded recursion on `n - k*k`, so the definition stays kernel-reducible (`decide`-
     friendly). `isPerfectSquareFn n := sqFuel (n+1) 0 n` — starting the search AT `k = 0` (not
     `k = 1`) means `n = 0` needs no special case (`0*0 = 0`): no `if n = 0` branch anywhere in
     the program or the proof (CLAUDE.md "normalize outliers, don't special-case them").

  2. **Spec** — `n` is a perfect square iff `∃ k, k*k = n` — the textbook definition, taken
     directly as the honest spec (no auxiliary bound smuggled in).

  3. **Correctness** (`perfectSquare_correct`) — reflection bridge (S5): `isPerfectSquareFn n =
     true ↔ ∃ k, k*k = n`.
     - Soundness (→, `sqFuel_sound`) — induction on the fuel: a `true` only ever comes from the
       `k*k = n` branch, which hands back `k` as the witness.
     - Completeness (←, `sqFuel_complete`) — the crux: an invariant that GENERALIZES over the
       search's current position `j`: if a witness `k0` with `j ≤ k0 ≤ j + fuel` exists, then
       `sqFuel fuel j n = true`. Proved by induction on `fuel`, using `k*k`'s monotonicity
       (`Nat.mul_le_mul`) to rule out the `j*j > n` branch (no witness `≥ j` could then exist) and
       to show a witness surviving the `j*j ≠ n` branch is `≥ j+1`, hence still reachable with one
       less fuel unit from `j+1`.
     - Fuel sufficiency: any witness `k0` satisfies `k0 ≤ n` (`Nat.le_mul_of_pos_right` when
       `k0 ≥ 1`; trivial when `k0 = 0`), so `k0 ≤ 0 + (n+1)`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC367

open Freyd Freyd.Alg.RelSet

/-! ## Data: `ℕ` (the input) and `Bool` (the decision answer) -/

abbrev dNat : RelSet.{0} := ⟨Nat⟩
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## Program: fuel-bounded upward search for a square root -/

/-- `sqFuel fuel k n` — search upward from `k` for a root of `n`, `fuel` steps deep. -/
def sqFuel : Nat → Nat → Nat → Bool
  | 0, k, n => decide (k * k = n)
  | fuel + 1, k, n =>
    if k * k = n then true
    else if k * k > n then false
    else sqFuel fuel (k + 1) n

/-- The answer function: search from `k = 0` with `n+1` fuel (S13) — `k = 0` needs no special
    case for `n = 0` (`0*0 = 0`). -/
def isPerfectSquareFn (n : Nat) : Bool := sqFuel (n + 1) 0 n

/-- **The allegory program**: LeetCode 367's decision as a morphism `dNat ⟶ dBool` in `Rel(Set)`. -/
def solve : dNat ⟶ dBool := graph isPerfectSquareFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map isPerfectSquareFn

/-! ## Specification: the textbook definition of "perfect square" -/

/-- The **specification** as a morphism `dNat ⟶ dBool`: `b` is THE correct boolean answer to
    "is `n` a perfect square?" -/
def spec : dNat ⟶ dBool := fun n b => (b = true ↔ ∃ k, k * k = n)

/-! ## Correctness -/

/-- **Soundness**: a `true` answer from `sqFuel` hands back a witnessing root. -/
theorem sqFuel_sound : ∀ fuel k n, sqFuel fuel k n = true → ∃ k', k' * k' = n := by
  intro fuel
  induction fuel with
  | zero =>
    intro k n h
    exact ⟨k, of_decide_eq_true h⟩
  | succ fuel ih =>
    intro k n h
    by_cases heq : k * k = n
    · exact ⟨k, heq⟩
    · by_cases hgt : k * k > n
      · exfalso
        have hf : sqFuel (fuel + 1) k n = false := by
          show (if k * k = n then true else if k * k > n then false else sqFuel fuel (k + 1) n)
             = false
          rw [if_neg heq, if_pos hgt]
        rw [hf] at h
        exact absurd h (by decide)
      · have hr : sqFuel (fuel + 1) k n = sqFuel fuel (k + 1) n := by
          show (if k * k = n then true else if k * k > n then false else sqFuel fuel (k + 1) n)
             = sqFuel fuel (k + 1) n
          rw [if_neg heq, if_neg hgt]
        rw [hr] at h
        exact ih (k + 1) n h

/-- **Completeness, generalized over the search's current position `j`**: a witness `k0` reachable
    within `fuel` steps from `j` (i.e. `j ≤ k0 ≤ j + fuel`) is FOUND by `sqFuel fuel j n`. This is
    the crux invariant — `sqFuel_sound`'s converse only holds relative to how far the search has to
    travel, hence the explicit fuel bookkeeping. -/
theorem sqFuel_complete : ∀ fuel j n k0, j ≤ k0 → k0 ≤ j + fuel → k0 * k0 = n →
    sqFuel fuel j n = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro j n k0 hjk hbound heq
    have hjk0 : k0 = j := by omega
    rw [hjk0] at heq
    show decide (j * j = n) = true
    rw [decide_eq_true_eq]
    exact heq
  | succ fuel ih =>
    intro j n k0 hjk hbound heq
    by_cases hj : j * j = n
    · show (if j * j = n then true else if j * j > n then false else sqFuel fuel (j + 1) n) = true
      rw [if_pos hj]
    · by_cases hgt : j * j > n
      · exfalso
        have hle : j * j ≤ k0 * k0 := Nat.mul_le_mul hjk hjk
        rw [heq] at hle
        omega
      · have hne : k0 ≠ j := by
          intro he
          apply hj
          rw [he] at heq
          exact heq
        have hjk' : j + 1 ≤ k0 := by omega
        have hbound' : k0 ≤ (j + 1) + fuel := by omega
        have hstep : sqFuel fuel (j + 1) n = true := ih (j + 1) n k0 hjk' hbound' heq
        show (if j * j = n then true else if j * j > n then false else sqFuel fuel (j + 1) n) = true
        rw [if_neg hj, if_neg hgt]
        exact hstep

/-- **Correctness of the allegory program**: `isPerfectSquareFn n = true ↔ ∃ k, k*k = n`, the
    honest reflection of "`n` is a perfect square". -/
theorem perfectSquare_correct (n : Nat) : isPerfectSquareFn n = true ↔ ∃ k, k * k = n := by
  constructor
  · intro h
    exact sqFuel_sound (n + 1) 0 n h
  · rintro ⟨k0, hk0⟩
    have hbnd : k0 ≤ 0 + (n + 1) := by
      rcases Nat.eq_zero_or_pos k0 with h0 | hpos
      · omega
      · have hle : k0 ≤ k0 * k0 := Nat.le_mul_of_pos_right k0 hpos
        rw [hk0] at hle
        omega
    exact sqFuel_complete (n + 1) 0 n k0 (Nat.zero_le _) hbnd hk0

/-- Two booleans that agree on being `true` are equal (Bool extensionality). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **`solve` equals `spec` as relations** (the allegory-program correctness statement). -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro n b
  show (b = isPerfectSquareFn n) ↔ (b = true ↔ ∃ k, k * k = n)
  constructor
  · intro h; rw [h]; exact perfectSquare_correct n
  · intro h
    have h' : (b = true) ↔ (isPerfectSquareFn n = true) := h.trans (perfectSquare_correct n).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

example : isPerfectSquareFn 16 = true := by decide
example : isPerfectSquareFn 14 = false := by decide
example : isPerfectSquareFn 1 = true := by decide

end Freyd.Alg.RelSet.LC367
