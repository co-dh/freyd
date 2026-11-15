/-
  LeetCode 9 — Palindrome Number — as an ALLEGORY PROGRAM.

  Problem: given an integer `n`, decide whether it is a palindrome, i.e. whether its base-10
  digit sequence reads the same forwards and backwards.  Negative numbers are NEVER palindromes
  (the leading `-` breaks the symmetry).

  Same DECISION-problem recipe as `leet/L217.lean`/`leet/L125.lean` (`Freyd/leetcode.md` S5):
  correctness is a plain `iff`, not a refinement+domination extremum.  Unlike those two, the
  input here is a bare `Int`, not a `SnocList` — the digit SEQUENCE is extracted internally by a
  fuel-guarded value-recursion (`Freyd/leetcode.md` S13), since peeling `n / 10` decreases a
  second, independently-shrinking argument and so does not compile to plain structural
  recursion.

  1. **Data** — the input object is `Int` directly (no datatype engine needed); the answer
     object is `Bool`.

  2. **Digit extraction (fuel).** `toDigitsFuel fuel n` peels the last digit (`n % 10`) while
     `n ≥ 10`, recursing on the FUEL (an ordinary `Nat.rec`, kernel-reducible, so `decide` can
     run it) rather than on `n` itself.  `toDigits n := toDigitsFuel (n+1) n` — fuel `n+1` is
     always enough, since a natural number's digit count never exceeds `n+1`.  The digits come
     out LEAST-significant-first; this does not affect the palindrome check, since for any list
     `ds`, `ds = ds.reverse ↔ ds.reverse = ds.reverse.reverse` — reading the digits forwards or
     backwards decides the same self-reversal fact.

  3. **Program.** `isPalinNumFn n := if n < 0 then false else decide (toDigits n.toNat =
     (toDigits n.toNat).reverse)`.  The sign is guarded once, at the `Int` boundary; the digit
     work itself stays on `Nat`.

  4. **Specification and correctness.** `palin_correct` is the honest unfolding: `n` is a
     palindrome iff it is non-negative AND its digit sequence is its own reverse — the
     self-reversal predicate on `toDigits n.toNat` IS the definition of "palindrome number", the
     same way `leet/L125.lean`'s `IsPalin` is `toList xs = (toList xs).reverse` on an already-
     given sequence.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC9

open Freyd Freyd.Alg.RelSet

/-! ## Data: the input is a bare `Int`; the answer is `Bool` -/

/-- The object of input integers in `Rel(Set)`. -/
abbrev dInt : RelSet.{0} := ⟨Int⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-! ## Digit extraction: fuel-guarded value-recursion (peels `n % 10` while `n ≥ 10`) -/

/-- `toDigitsFuel fuel n` — the base-10 digits of `n`, least-significant-first, computed by
    recursion on `fuel` (not on `n`).  Terminates as soon as `n < 10`; the `fuel = 0` branch is
    a totality fallback that is never reached for the fuel we actually supply (`n + 1`). -/
def toDigitsFuel : Nat → Nat → List Nat
  | 0, n => [n]
  | fuel + 1, n => if n < 10 then [n] else (n % 10) :: toDigitsFuel fuel (n / 10)

/-- `toDigits n` — the base-10 digits of `n`, least-significant-first.  Fuel `n + 1` is always
    enough: a natural number's digit count never exceeds `n + 1`. -/
def toDigits (n : Nat) : List Nat := toDigitsFuel (n + 1) n

/-! ## The program: guard the sign, then decide self-reversal on the digit list -/

/-- The answer function: is `n` a palindrome?  Negative numbers are never palindromes; for
    `n ≥ 0`, decide whether the digit sequence of `n.toNat` equals its own reverse. -/
def isPalinNumFn (n : Int) : Bool :=
  if n < 0 then false else decide (toDigits n.toNat = (toDigits n.toNat).reverse)

/-- **The allegory program**: LeetCode 9's solution as a morphism `dInt ⟶ dBool` in `Rel(Set)`. -/
def solve : dInt ⟶ dBool := graph isPalinNumFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map isPalinNumFn

/-! ## Correctness: the honest digit-palindrome property -/

/-- **`isPalinNumFn` decides the digit-palindrome property**: `n` is a palindrome iff it is
    non-negative and its digit sequence is its own reverse.  The DECISION-problem correctness
    shape (`Freyd/leetcode.md` S5) — a plain `iff`, not an extremum. -/
theorem palin_correct (n : Int) :
    isPalinNumFn n = true ↔ (0 ≤ n ∧ toDigits n.toNat = (toDigits n.toNat).reverse) := by
  unfold isPalinNumFn
  by_cases hn : n < 0
  · rw [if_pos hn]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨h0, _⟩; exact absurd h0 (by omega)
  · rw [if_neg hn, decide_eq_true_eq]
    exact ⟨fun h => ⟨by omega, h⟩, fun ⟨_, h⟩ => h⟩

/-! ## Specification and the morphism-equation headline -/

/-- **The specification** as a morphism `dInt ⟶ dBool`: `b` is THE correct answer to "is `n` a
    palindrome?" — non-negative and its digit sequence is its own reverse — stated independently of
    the program `isPalinNumFn`. -/
def spec : dInt ⟶ dBool :=
  fun n b => (b = true ↔ (0 ≤ n ∧ toDigits n.toNat = (toDigits n.toNat).reverse))

/-- Two booleans that agree on being `true` are equal (`Bool` extensionality; the L100 helper). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **The allegory-program headline**: `solve = spec` as morphisms in `Rel(Set)` — the program is
    exactly the palindrome-number decision, not merely pointwise correct. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro n b
  show (b = isPalinNumFn n) ↔ (b = true ↔ (0 ≤ n ∧ toDigits n.toNat = (toDigits n.toNat).reverse))
  constructor
  · intro h; rw [h]; exact palin_correct n
  · intro h; exact bool_eq_of_iff_true (h.trans (palin_correct n).symm)

/-! ## Running the program -/

example : isPalinNumFn 121 = true := by decide
example : isPalinNumFn (-121) = false := by decide
example : isPalinNumFn 10 = false := by decide

end Freyd.Alg.RelSet.LC9
