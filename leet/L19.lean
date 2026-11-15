/-
  LeetCode 19 — Remove Nth Node From End of List — as an ALLEGORY PROGRAM.

  Problem: remove the `n`-th node from the END of a list (1-indexed from the end) and return the
  resulting list, under the precondition `1 ≤ n ≤ xs.length`.  This repo models the list as a
  plain `List Int` (no linked-list pointer surgery, matching `L206`/`L21`): the node to remove
  sits at the 0-INDEXED position `k := xs.length - n` FROM THE FRONT, so "removal" is
  `xs.take k ++ xs.drop (k+1)` — keep everything strictly before `k`, drop the element at `k`,
  keep everything from `k+1` on.

  1. **Program** — `removeNthFn xs n := xs.take (xs.length - n) ++ xs.drop (xs.length - n + 1)`.

  2. **Specification — honest, three-part, getElem?-phrased (Skill S23).**  For `1 ≤ n ≤
     xs.length` (so `k := xs.length - n` is a genuine in-range index):
     - LENGTH: `(removeNthFn xs n).length = xs.length - 1`.
     - BEFORE `k`, unchanged: `∀ i, i < k → (removeNthFn xs n)[i]? = xs[i]?`.
     - AT/AFTER `k`, shifted left by one: `∀ i, k ≤ i → (removeNthFn xs n)[i]? = xs[i+1]?`.
     Together these pin down the ENTIRE output list, not just its length — every surviving
     position is accounted for on both sides of the cut.  A fourth, bonus fact nails down WHICH
     element was removed: `removeNth_splice` shows splicing `xs[k]` back in between the front/back
     halves of `removeNthFn xs n` recovers `xs` exactly — i.e. the element removed genuinely IS
     the `n`-th from the end, not merely "some element consistent with the length dropping by 1".

  3. **Correctness = `removeNth_correct`**, the conjunction of the three getElem?-phrased bullets.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC19

open Freyd

/-! ## Program -/

/-- **The program**: remove the element at 0-indexed position `xs.length - n` (the `n`-th from
    the end) by keeping everything before it and everything after it. -/
def removeNthFn (xs : List Int) (n : Nat) : List Int :=
  xs.take (xs.length - n) ++ xs.drop (xs.length - n + 1)

/-! ## Correctness -/

/-- **Length**: removing one node shortens the list by exactly one. -/
theorem removeNth_length (xs : List Int) (n : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ xs.length) :
    (removeNthFn xs n).length = xs.length - 1 := by
  unfold removeNthFn
  rw [List.length_append, List.length_take, List.length_drop]
  omega

/-- **Positions before `k := xs.length - n` are unchanged.** -/
theorem removeNth_getElem?_lt (xs : List Int) (n : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ xs.length)
    (i : Nat) (hi : i < xs.length - n) :
    (removeNthFn xs n)[i]? = xs[i]? := by
  unfold removeNthFn
  rw [List.getElem?_append, List.length_take, if_pos (by omega), List.getElem?_take,
    if_pos (by omega)]

/-- **Positions at/after `k` shift left by one** (the element at `k` was deleted, so what used to
    sit at `i+1` now sits at `i`). -/
theorem removeNth_getElem?_ge (xs : List Int) (n : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ xs.length)
    (i : Nat) (hi : xs.length - n ≤ i) :
    (removeNthFn xs n)[i]? = xs[i + 1]? := by
  unfold removeNthFn
  rw [List.getElem?_append, List.length_take, if_neg (by omega), List.getElem?_drop]
  congr 1
  omega

/-- **Headline correctness**: `removeNthFn xs n` is `xs` with exactly the `(xs.length-n)`-th
    element deleted — length drops by one, every earlier position is untouched, every later
    position shifts left by one. -/
theorem removeNth_correct (xs : List Int) (n : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ xs.length) :
    (removeNthFn xs n).length = xs.length - 1 ∧
    (∀ i, i < xs.length - n → (removeNthFn xs n)[i]? = xs[i]?) ∧
    (∀ i, xs.length - n ≤ i → (removeNthFn xs n)[i]? = xs[i + 1]?) :=
  ⟨removeNth_length xs n hn1 hn2, removeNth_getElem?_lt xs n hn1 hn2,
   removeNth_getElem?_ge xs n hn1 hn2⟩

/-- **Bonus: the removed element is exactly the `n`-th from the end.**  Splicing `xs[k]` back in
    between the front (`take k`) and back (`drop (k+1)`) halves of `removeNthFn xs n` recovers
    `xs` exactly, at position `k := xs.length - n` — so the element genuinely deleted is `xs[k]`,
    not merely "some element consistent with the shorter length". The proof `h` of the dependent
    index is bound once and reused on both sides, so `rw` needs no proof-irrelevance juggling. -/
theorem removeNth_splice (xs : List Int) (n : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ xs.length) :
    ∀ h : xs.length - n < xs.length,
      xs.take (xs.length - n) ++ xs[xs.length - n]'h :: xs.drop (xs.length - n + 1) = xs :=
  fun h => by rw [← List.drop_eq_getElem_cons h, List.take_append_drop]

/-! ## `Rel(Set)` packaging -/

/-- The input object: the list together with the 1-indexed-from-the-end position to remove. -/
abbrev dInput : RelSet.{0} := ⟨List Int × Nat⟩
/-- The answer object: the list with the node removed. -/
abbrev dAns : RelSet.{0} := ⟨List Int⟩

/-- **The allegory program**: LeetCode 19's removal as a morphism `dInput ⟶ dAns` in `Rel(Set)`. -/
def solve : dInput ⟶ dAns := graph (fun p => removeNthFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map _

/-- **The specification** as a morphism `dInput ⟶ dAns`: given a valid `1 ≤ n ≤ xs.length`, the
    output satisfies the three-part `removeNth_correct` shape. -/
def spec : dInput ⟶ dAns := fun p out =>
  1 ≤ p.2 → p.2 ≤ p.1.length →
    out.length = p.1.length - 1 ∧
    (∀ i, i < p.1.length - p.2 → out[i]? = p.1[i]?) ∧
    (∀ i, p.1.length - p.2 ≤ i → out[i]? = p.1[i + 1]?)

/-- **The program refines the specification** (in fact computes it exactly): whatever `solve`
    returns satisfies `spec`. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun p out h => ?_)
  have hout : out = removeNthFn p.1 p.2 := h
  intro hn1 hn2
  rw [hout]
  exact removeNth_correct p.1 p.2 hn1 hn2

/-! ## Headline: on valid `n`, `solve` IS `spec` (a genuine morphism equation) -/

/-- **Uniqueness of a spec output**: the two index clauses (before/at-or-after the removed position)
    partition ALL indices and pin `out[i]?` for each, so any two outputs meeting the characterization
    agree everywhere, hence are equal by list extensionality.  No precondition is needed here — the
    characterization alone is already functional. -/
theorem spec_out_unique (xs : List Int) (n : Nat) (o₁ o₂ : List Int)
    (h1 : (∀ i, i < xs.length - n → o₁[i]? = xs[i]?) ∧ (∀ i, xs.length - n ≤ i → o₁[i]? = xs[i + 1]?))
    (h2 : (∀ i, i < xs.length - n → o₂[i]? = xs[i]?) ∧ (∀ i, xs.length - n ≤ i → o₂[i]? = xs[i + 1]?)) :
    o₁ = o₂ := by
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i (xs.length - n) with hi | hi
  · rw [h1.1 i hi, h2.1 i hi]
  · rw [h1.2 i hi, h2.2 i hi]

/-- The precondition coreflexive: the sub-identity on VALID inputs (`1 ≤ n ≤ length`). -/
def pre : dInput ⟶ dInput := fun p q => p = q ∧ 1 ≤ p.2 ∧ p.2 ≤ p.1.length

/-- **Preconditioned headline**: restricted to valid removal positions (`pre`), the program equals
    the specification — `pre ≫ solve = pre ≫ spec`.  Existence is `removeNth_correct`; uniqueness is
    `spec_out_unique` (the index characterization is functional). -/
theorem pre_solve_eq_spec : pre ≫ solve = pre ≫ spec := by
  apply hom_ext; intro p out
  rw [comp_apply, comp_apply]
  constructor
  · rintro ⟨q, ⟨rfl, hn1, hn2⟩, hsolve⟩
    refine ⟨p, ⟨rfl, hn1, hn2⟩, ?_⟩
    intro _ _
    rw [(hsolve : out = removeNthFn p.1 p.2)]; exact removeNth_correct p.1 p.2 hn1 hn2
  · rintro ⟨q, ⟨rfl, hn1, hn2⟩, hspec⟩
    refine ⟨p, ⟨rfl, hn1, hn2⟩, ?_⟩
    show out = removeNthFn p.1 p.2
    obtain ⟨_, ho1, ho2⟩ := hspec hn1 hn2
    obtain ⟨_, hr1, hr2⟩ := removeNth_correct p.1 p.2 hn1 hn2
    exact spec_out_unique p.1 p.2 out (removeNthFn p.1 p.2) ⟨ho1, ho2⟩ ⟨hr1, hr2⟩

/-! ## Running the program -/

example : removeNthFn ([1, 2, 3, 4, 5] : List Int) 2 = [1, 2, 3, 5] := by decide
example : removeNthFn ([1] : List Int) 1 = [] := by decide

end Freyd.Alg.RelSet.LC19
