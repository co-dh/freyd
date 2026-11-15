/-
  LeetCode 13 — Roman to Integer — as an ALLEGORY PROGRAM.

  Problem: a roman numeral, given here directly as its list of symbol VALUES (I=1, V=5, X=10,
  L=50, C=100, D=500, M=1000), left to right — return its integer value.  The standard rule: sum
  every symbol, EXCEPT a symbol strictly LESS than the symbol immediately following it, which is
  SUBTRACTED instead of added (e.g. `IV = [1,5] ↦ 5 - 1 = 4`).

  1. **Program** — `romanFn` is the textbook two-element-lookahead fold: at each symbol `x`,
     compare it to its immediate successor `y` (if any) and add `x` or `-x` accordingly, then
     recurse on the rest.  This recurrence IS the standard definition of a roman numeral's value —
     accepted as *the* definition, the way `L70`'s `climb`/`L91`'s `decode` are.

  2. **Specification** — a genuine RE-CHARACTERIZATION, not a restatement of the recurrence:
     `romanFn xs = xs.sum - 2 * subtractedPart xs`, where `subtractedPart` sums exactly the
     symbols that get subtracted.  Reading: "add every symbol, then take away TWICE each
     subtractive symbol" (once to cancel the `+x` it got from the naive sum, once more to make it
     `-x`).  Proved by the same two-element lookahead recursion as `romanFn` itself.

  3. **`Rel(Set)` packaging** — `solve := graph romanFn`, a `Map` (the graph of a function).

  Mathlib-free; fully constructive — axioms `⊆ {propext, Quot.sound}`.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

namespace Freyd.Alg.RelSet.LC13

open Freyd

/-! ## The program: two-element lookahead fold -/

/-- **The program**: sum the symbol values left to right, SUBTRACTING a symbol that is strictly
    less than the symbol immediately after it.  This recurrence is the textbook definition of a
    roman numeral's value. -/
def romanFn : List Int → Int
  | [] => 0
  | [x] => x
  | x :: y :: rest => (if x < y then -x else x) + romanFn (y :: rest)

/-- The defining `cons`-`cons` equation, exposed as a `simp` lemma for reuse. -/
@[simp] theorem romanFn_cons_cons (x y : Int) (rest : List Int) :
    romanFn (x :: y :: rest) = (if x < y then -x else x) + romanFn (y :: rest) := rfl

/-! ## The closed-form re-characterization: sum minus twice the subtracted part -/

/-- The total value of every symbol that gets SUBTRACTED by the rule (strictly less than its
    immediate successor). -/
def subtractedPart : List Int → Int
  | [] => 0
  | [_] => 0
  | x :: y :: rest => (if x < y then x else 0) + subtractedPart (y :: rest)

/-- **Honest closed-form spec**: the roman value is the plain sum of all symbols, minus TWICE the
    subtracted part — real content beyond the recurrence (a re-characterization, not a
    restatement).  Proved by the same two-element lookahead induction as `romanFn`. -/
theorem roman_correct : ∀ xs : List Int, romanFn xs = xs.sum - 2 * subtractedPart xs
  | [] => by simp [romanFn, subtractedPart]
  | [x] => by simp [romanFn, subtractedPart]
  | x :: y :: rest => by
      have ih := roman_correct (y :: rest)
      simp only [List.sum_cons] at ih
      by_cases h : x < y
      · simp only [romanFn_cons_cons, subtractedPart, List.sum_cons, if_pos h]
        omega
      · simp only [romanFn_cons_cons, subtractedPart, List.sum_cons, if_neg h]
        omega

/-! ## `Rel(Set)` packaging -/

/-- The input object: a roman numeral as its list of symbol values. -/
abbrev dInput : RelSet.{0} := ⟨List Int⟩
/-- The answer object: the integer value. -/
abbrev dAns : RelSet.{0} := ⟨Int⟩

/-- **The allegory program**: LeetCode 13's roman-to-integer conversion as a morphism
    `dInput ⟶ dAns` in `Rel(Set)`. -/
def solve : dInput ⟶ dAns := graph romanFn

/-- `solve` is a `Map` — a genuine function, via the `graph`/`Map` route. -/
theorem solve_map : Map solve := graph_map romanFn

/-! ## The morphism-equation headline -/

/-- **The specification** as a morphism `dInput ⟶ dAns`: `v` is THE value of the roman numeral —
    the plain symbol sum minus twice the subtracted part (the closed-form meaning of subtractive
    pairs) — stated independently of the recurrence `romanFn`. -/
def spec : dInput ⟶ dAns := fun xs v => v = xs.sum - 2 * subtractedPart xs

/-- **The allegory-program headline**: `solve = spec` as morphisms in `Rel(Set)` — the program
    computes exactly the closed-form roman value, not merely pointwise. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro xs v
  show (v = romanFn xs) ↔ (v = xs.sum - 2 * subtractedPart xs)
  rw [roman_correct]

/-! ## Running the program -/

/-- `III = [1,1,1] → 3`. -/
example : romanFn [1, 1, 1] = 3 := by decide

/-- `IV = [1,5] → 4`. -/
example : romanFn [1, 5] = 4 := by decide

/-- `MCMXCIV = [1000,100,1000,10,100,1,5] → 1994`. -/
example : romanFn [1000, 100, 1000, 10, 100, 1, 5] = 1994 := by decide

end Freyd.Alg.RelSet.LC13
