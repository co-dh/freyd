/-
  LeetCode 231 — Power of Two — as an ALLEGORY PROGRAM.

  Problem: given an integer `n`, decide whether it is a power of two, i.e. whether `n = 2^k` for
  some `k : Nat`.  `n` must be positive (`0` and negatives are never powers of two).

  Same DECISION-problem recipe as `leet/L9.lean`/`leet/L217.lean` (`Freyd/leetcode.md` S5):
  correctness is a plain `iff`, not a refinement+domination extremum.  Like `L9`, the input is a
  bare `Int`, not a `SnocList` — no list-datatype engine is needed here at all.

  1. **Data** — the input object is `Int` directly; the answer object is `Bool`.

  2. **Program (fuel).** `pow2Fuel fuel m` repeatedly halves `m` while it is even, recursing on
     FUEL (`Freyd/leetcode.md` S13) rather than on `m` itself, since `m / 2` decreases a second,
     independently-shrinking argument and so does not compile to plain structural recursion:
     `m = 1` accepts; `m = 0` or `m` odd `> 1` rejects; otherwise recurse on `m / 2` with one less
     fuel.  `isPow2Fn n := if n ≤ 0 then false else pow2Fuel n.toNat n.toNat` — fuel `n.toNat` is
     always enough, since halving a positive `m` reaches `1` in at most `m` steps.

  3/4. **Specification and correctness.** `pow2_correct` is the honest unfolding: `n` is a power
     of two iff `0 < n` and `n = 2^k` for some `k : Nat` — exactly LeetCode's definition, no
     `Decidable`-instance detour.  Two halves, both by induction on the fuel: `pow2Fuel_pow`
     (halving `2^k` reaches `1` within `k` steps of fuel — the forward witness) and
     `pow2Fuel_to_exists` (accepting fuel-`m` pairs are exactly the powers of two — the converse,
     recovering the exponent from the halving trace).  The `Int`/`Nat` boundary is crossed once via
     `Int.toNat_of_nonneg` and `Int.natCast_pow`.

  Mathlib-free; axioms `[propext, Quot.sound]` (fully constructive — no `Classical.choice`).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC231

open Freyd Freyd.Alg.RelSet

/-! ## Data: the input is a bare `Int`; the answer is `Bool` -/

/-- The object of input integers in `Rel(Set)`. -/
abbrev dInt : RelSet.{0} := ⟨Int⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## The program: fuel-guarded halving decision -/

/-- `pow2Fuel fuel m` — does repeatedly halving `m` (while even) reach `1`?  Recursion is on
    `fuel`, not on `m`: `m / 2` decreases a second, independently-shrinking argument, so a direct
    recursion on `m` would compile to well-founded (non-`rfl`-reducible) recursion. -/
def pow2Fuel : Nat → Nat → Bool
  | 0, m => decide (m = 1)
  | fuel + 1, m =>
    if m = 1 then true
    else if m = 0 then false
    else if m % 2 = 0 then pow2Fuel fuel (m / 2) else false

/-- `isPow2Fn n` — is `n` a power of two?  Guard the sign once, at the `Int` boundary; the halving
    itself stays on `Nat`.  Fuel `n.toNat` is always enough: halving a positive `m` strictly
    decreases and reaches `1` in at most `m` steps. -/
def isPow2Fn (n : Int) : Bool :=
  if n ≤ 0 then false else pow2Fuel n.toNat n.toNat

/-- **The allegory program**: LeetCode 231's solution as a morphism `dInt ⟶ dBool` in `Rel(Set)`. -/
def solve : dInt ⟶ dBool := graph isPow2Fn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map isPow2Fn

/-! ## Correctness: the halving↔exponent bridge -/

/-- `pow2Fuel` accepts `1` at any fuel level (the base case of the halving descent). -/
theorem pow2Fuel_one : ∀ fuel, pow2Fuel fuel 1 = true := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ f => simp [pow2Fuel]

/-- `2 ^ k` is always positive (needed to rule out the `m = 0`/`m = 1` branches at `k + 1`). -/
theorem two_pow_pos : ∀ k : Nat, 0 < 2 ^ k := by
  intro k
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-- **Forward witness**: halving `2 ^ k` reaches `1` within `k` steps of fuel. -/
theorem pow2Fuel_pow : ∀ (k fuel : Nat), k ≤ fuel → pow2Fuel fuel (2 ^ k) = true := by
  intro k
  induction k with
  | zero => intro fuel _; exact pow2Fuel_one fuel
  | succ k ih =>
    intro fuel hk
    -- `fuel > 0` since `fuel ≥ k + 1`; peel one layer of fuel to match `pow2Fuel`'s `fuel + 1`
    -- clause.  Route the impossible `fuel = 0` case through `False.elim` (not a bare `omega` on
    -- the existential goal) to stay axiom-clean — a direct `omega` there silently pulls in
    -- `Classical.choice`.
    obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := by
      cases fuel with
      | zero => exact False.elim (by omega)
      | succ f => exact ⟨f, rfl⟩
    have hk' : k ≤ fuel' := by omega
    have hp2k : 0 < 2 ^ k := two_pow_pos k
    have heq : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have hne1 : (2 : Nat) ^ (k + 1) ≠ 1 := by omega
    have hne0 : (2 : Nat) ^ (k + 1) ≠ 0 := by omega
    have hmod : (2 : Nat) ^ (k + 1) % 2 = 0 := by omega
    have hdiv : (2 : Nat) ^ (k + 1) / 2 = 2 ^ k := by omega
    show pow2Fuel (fuel' + 1) (2 ^ (k + 1)) = true
    unfold pow2Fuel
    rw [if_neg hne1, if_neg hne0, if_pos hmod, hdiv]
    exact ih fuel' hk'

/-- **Converse**: any `m` accepted by `pow2Fuel` (at any fuel) is a power of two — recovers the
    exponent from the halving trace. -/
theorem pow2Fuel_to_exists : ∀ (fuel m : Nat), pow2Fuel fuel m = true → ∃ k : Nat, m = 2 ^ k := by
  intro fuel
  induction fuel with
  | zero =>
    intro m hm
    simp only [pow2Fuel, decide_eq_true_eq] at hm
    exact ⟨0, hm⟩
  | succ fuel' ih =>
    intro m hm
    unfold pow2Fuel at hm
    by_cases h1 : m = 1
    · exact ⟨0, h1⟩
    · rw [if_neg h1] at hm
      by_cases h0 : m = 0
      · rw [if_pos h0] at hm; exact absurd hm (by decide)
      · rw [if_neg h0] at hm
        by_cases heven : m % 2 = 0
        · rw [if_pos heven] at hm
          obtain ⟨k', hk'⟩ := ih (m / 2) hm
          refine ⟨k' + 1, ?_⟩
          rw [Nat.pow_succ, ← hk']
          omega
        · rw [if_neg heven] at hm; exact absurd hm (by decide)

/-- **`isPow2Fn` decides the power-of-two property**: `n` is a power of two iff it is positive and
    equals `2 ^ k` for some natural `k` — LeetCode 231's definition, verbatim.  The DECISION-problem
    correctness shape (`Freyd/leetcode.md` S5): a plain `iff`, not an extremum. -/
theorem pow2_correct (n : Int) :
    isPow2Fn n = true ↔ (0 < n ∧ ∃ k : Nat, n = (2 : Int) ^ k) := by
  unfold isPow2Fn
  by_cases hn : n ≤ 0
  · rw [if_pos hn]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨h0, _⟩; exact absurd h0 (by omega)
  · rw [if_neg hn]
    have hpos : 0 < n := by omega
    have hcast : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg (by omega)
    constructor
    · intro h
      obtain ⟨k, hk⟩ := pow2Fuel_to_exists n.toNat n.toNat h
      refine ⟨hpos, k, ?_⟩
      rw [← hcast, hk, Int.natCast_pow]; rfl
    · rintro ⟨_, k, hk⟩
      have hnk : n.toNat = 2 ^ k := by
        have hh : ((n.toNat : Nat) : Int) = ((2 ^ k : Nat) : Int) := by
          rw [hcast, hk, Int.natCast_pow]; rfl
        exact Int.natCast_inj.mp hh
      rw [hnk]
      exact pow2Fuel_pow k (2 ^ k) (Nat.le_of_lt Nat.lt_two_pow_self)

/-! ## Specification and the decision headline -/

/-- The **specification** as a morphism `dInt ⟶ Bool` in `Rel(Set)`: `r = true` iff `n` is a power
    of two (positive and equal to `2 ^ k`) — LeetCode 231's definition verbatim, a genuine `Iff`. -/
def spec : dInt ⟶ dBool := fun n r => (r = true ↔ (0 < n ∧ ∃ k : Nat, n = (2 : Int) ^ k))

/-- Two booleans that agree on being `true` are equal (Bool extensionality). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **`solve` equals `spec` as relations** — the DECISION-problem headline: `solve` (deciding
    `isPow2Fn`) is exactly the specification "`r = true` iff `n` is a power of two". -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro n r
  show (r = isPow2Fn n) ↔ (r = true ↔ (0 < n ∧ ∃ k : Nat, n = (2 : Int) ^ k))
  constructor
  · intro h; rw [h]; exact pow2_correct n
  · intro h; exact bool_eq_of_iff_true (h.trans (pow2_correct n).symm)

/-! ## Running the program -/

example : isPow2Fn 1 = true := by decide
example : isPow2Fn 16 = true := by decide
example : isPow2Fn 6 = false := by decide

end Freyd.Alg.RelSet.LC231
