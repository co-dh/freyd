/-
  LeetCode 392 — Is Subsequence — as an ALLEGORY PROGRAM.

  Problem: given two strings `s` and `t` (here `List Int`, one code point per element), decide
  whether `s` is a SUBSEQUENCE of `t` — i.e. `s` can be obtained from `t` by deleting some
  (possibly zero) elements without reordering the rest.

  A DECISION problem (Skill S5), but on TWO inputs at once (Skill S16/S21): the program is a
  two-argument greedy match, and — unlike most decision problems here, whose honest spec is a
  hand-rolled Prop mirror of the program — the honest specification is Lean CORE's
  `List.Sublist` (`<+`, Skill S24): the multiplicity-and-order-faithful subsequence relation
  (`⊆`/`List.Subset` is a faithfulness BUG here — it forgets order and multiplicity, so
  `[1,1] ⊆ [1]` is vacuously true).

  1. **Program** — `isSubseqFn s t`: `[]` is a subsequence of anything; a nonempty `s` is never a
     subsequence of `[]`; otherwise compare the heads — if they match, consume BOTH heads and
     recurse; if not, only `t`'s head is skipped and `s` waits.  Every recursive call strictly
     shrinks `t` (both branches of the last case replace `b :: t'` by `t'`), so this is ordinary
     STRUCTURAL recursion on the second argument, not well-founded recursion — no fuel needed.

  2. **Specification** — `s <+ t` (`List.Sublist`), Lean core's own subsequence relation, built
     from `slnil`/`cons`/`cons₂`.

  3. **Correctness** — `subseq_correct : isSubseqFn s t = true ↔ s <+ t`, by `induction t
     generalizing s` (Skill S16's two-input shape) then `cases s`.  The two live cases both reduce
     to a Lean-core Sublist lemma at the SAME head: `a = b` uses `cons_sublist_cons` (`a::s' <+
     a::t' ↔ s' <+ t'`); `a ≠ b` uses `sublist_cons_iff` (`l <+ b::t' ↔ l <+ t' ∨ ∃ r, l = b::r ∧ r
     <+ t'`), whose second disjunct is ruled out by `a ≠ b` via `injection`.  No hand-rolled
     Sublist reasoning at all — Lean core already has exactly the lemmas this recurrence needs.

  4. **`Rel(Set)` packaging** — `solve := graph (fun p => isSubseqFn p.1 p.2) : dInput ⟶ dBool`
     (a `Map`), `spec : dInput ⟶ dBool := fun p b => (b = true ↔ p.1 <+ p.2)`, and `solve = spec`
     (Skill S5's bool-extensionality route, `bool_eq_of_iff_true`).

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (the correctness proof is pure `List Int` /
  `List.Sublist` reasoning — no `Classical.choice` anywhere).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC392

open Freyd
open List

/-! ## Program: two-input greedy match, structural recursion on `t` -/

/-- `isSubseqFn s t` — is `s` a subsequence of `t`?  Structural on `t`: both branches of the
    `cons`/`cons` case replace `b :: t'` by `t'`. -/
def isSubseqFn : List Int → List Int → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: s', b :: t' => if a = b then isSubseqFn s' t' else isSubseqFn (a :: s') t'

/-! ## Correctness: `isSubseqFn` reflects Lean-core `List.Sublist` -/

/-- **The bridge lemma / headline theorem**: `isSubseqFn` computes exactly `<+` (`List.Sublist`),
    the honest, multiplicity-and-order-faithful subsequence relation. -/
theorem subseq_correct : ∀ s t : List Int, isSubseqFn s t = true ↔ s <+ t := by
  intro s t
  induction t generalizing s with
  | nil =>
    cases s with
    | nil => simp [isSubseqFn]
    | cons a s' => simp [isSubseqFn, sublist_nil]
  | cons b t' ih =>
    cases s with
    | nil => simp [isSubseqFn, nil_sublist]
    | cons a s' =>
      by_cases hab : a = b
      · simp only [isSubseqFn, if_pos hab]
        rw [hab, cons_sublist_cons]
        exact ih s'
      · simp only [isSubseqFn, if_neg hab]
        rw [ih (a :: s'), sublist_cons_iff]
        constructor
        · exact Or.inl
        · rintro (h | ⟨r, hr, _⟩)
          · exact h
          · injection hr with h1 _
            exact absurd h1 hab

/-! ## `Rel(Set)` packaging -/

/-- The input object: the two lists (`s`, `t`) to compare. -/
abbrev dInput : RelSet.{0} := ⟨List Int × List Int⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-- **The allegory program**: LeetCode 392's solution as a morphism `dInput ⟶ dBool` in
    `Rel(Set)`. -/
def solve : dInput ⟶ dBool := graph (fun p : List Int × List Int => isSubseqFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : List Int × List Int => isSubseqFn p.1 p.2)

/-- The **specification** as a morphism `dInput ⟶ dBool` in `Rel(Set)`: `b` is THE correct
    boolean answer to "is `p.1` a subsequence of `p.2`?" -/
def spec : dInput ⟶ dBool := fun p b => (b = true ↔ p.1 <+ p.2)

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
  apply hom_ext; intro p b
  show (b = isSubseqFn p.1 p.2) ↔ (b = true ↔ p.1 <+ p.2)
  constructor
  · intro h; rw [h]; exact subseq_correct p.1 p.2
  · intro h
    have h' : (b = true) ↔ (isSubseqFn p.1 p.2 = true) := h.trans (subseq_correct p.1 p.2).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

example : isSubseqFn [97, 98, 99] [97, 104, 98, 103, 100, 99] = true := by decide
example : isSubseqFn [97, 120, 99] [97, 104, 98, 103, 100, 99] = false := by decide

end Freyd.Alg.RelSet.LC392
