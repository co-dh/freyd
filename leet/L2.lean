/-
  LeetCode 2 — Add Two Numbers — as an ALLEGORY PROGRAM.

  Problem: two non-negative integers are given as digit lists in LITTLE-ENDIAN order (least
  significant digit first, each digit `0..9`), as `List Int`.  Return their sum, also as a
  little-endian digit list.

  Genuinely a TWO-INPUT recursion (like `L21`'s merge): each step consumes a digit off BOTH
  lists at once (`0` once a list runs dry), so neither input is a structural subterm of the
  other and a naive definition compiles to well-founded recursion.  TAMED with the FUEL trick
  (Skill S13/S21): `addFuel : Nat → Int → List Int → List Int → List Int` recurses on an
  explicit fuel parameter, structurally, staying kernel-reducible (`decide` works directly).
  `addFuel`'s carry parameter `c` starts at `0` and is *itself* a `10`-quotient of the previous
  digit sum — the standard schoolbook carry-ripple addition.

  1. **Program** — `addFuel fuel c xs ys`: if both lists are empty, emit the leftover carry (or
     nothing); otherwise pop a digit from each PRESENT list (`0` if a list is already exhausted),
     form `s := c + x + y`, emit `s % 10`, and recurse on one less fuel with carry `s / 10`.
     `addFn xs ys := addFuel (xs.length + ys.length + 1) 0 xs ys` — the `+1` covers the final
     carry-out digit, so the bound is always sufficient (never merely tight, unlike `L21`'s exact
     accounting: here a genuine EXTRA digit can appear, e.g. `99 + 1 = 100`).

  2. **Specification — honest VALUE PRESERVATION.** `value : List Int → Int`, `value [] = 0`,
     `value (d :: ds) = d + 10 * value ds` reads a little-endian digit list back into the integer
     it denotes (for ANY `Int` digits — the `0..9` range is not needed for this identity, so it is
     stated in full generality, not merely for the actual `0..9` inputs). The crux lemma is
     CARRY-GENERAL: `addFuel_value : xs.length + ys.length ≤ fuel → value (addFuel fuel c xs ys) =
     c + value xs + value ys`, by induction on `fuel`. `add_correct` specializes it at
     `c := 0`, `fuel := xs.length + ys.length + 1`: `value (addFn xs ys) = value xs + value ys`.

  3. **The arithmetic crux**: unpacking one carry-ripple step needs `10 * (s / 10) + s % 10 = s`
     (`Int.mul_ediv_add_emod s 10`, the non-deprecated form of `Int.ediv_add_emod`) — kept as an
     explicit hypothesis rather than asking `omega` to discover the `/`,`%` relationship itself,
     so the arithmetic stays a transparent linear combination once that one nonlinear fact is
     supplied.

  Mathlib-free; axioms ⊆ {propext, Quot.sound} — fully constructive, no `Classical.choice`.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC2

open Freyd

/-! ## Value semantics: read a little-endian digit list back into the integer it denotes -/

/-- `value [] = 0`, `value (d :: ds) = d + 10 * value ds` — holds for ANY `Int` digit list, not
    just `0..9` digits; only this general form is needed for `add_correct`. -/
def value : List Int → Int
  | [] => 0
  | d :: ds => d + 10 * value ds

/-! ## Program: carry-ripple addition, tamed by an explicit fuel parameter (Skill S13/S21) -/

/-- `addFuel fuel c xs ys` — schoolbook addition with carry `c`.  Both lists empty: emit the
    leftover carry (`[]` if it is `0`).  Otherwise: pop a digit from each PRESENT list (`0` if a
    list is already exhausted), emit `s % 10` for `s := c + x + y`, recurse with carry `s / 10` on
    one less fuel.  Structural on `fuel`, hence kernel-reducible. -/
def addFuel : Nat → Int → List Int → List Int → List Int
  | 0, c, _, _ => if c = 0 then [] else [c]
  | _ + 1, c, [], [] => if c = 0 then [] else [c]
  | fuel + 1, c, x :: xs, [] => (c + x) % 10 :: addFuel fuel ((c + x) / 10) xs []
  | fuel + 1, c, [], y :: ys => (c + y) % 10 :: addFuel fuel ((c + y) / 10) [] ys
  | fuel + 1, c, x :: xs, y :: ys => (c + x + y) % 10 :: addFuel fuel ((c + x + y) / 10) xs ys

/-- **The program**: add two little-endian digit lists, run with `xs.length + ys.length + 1`
    fuel — sufficient (not merely exact, unlike `L21`'s merge): the `+1` covers a genuine
    carry-out digit past the longer input, e.g. `addFn [9,9] [1] = [0,0,1]` (`99 + 1 = 100`). -/
def addFn (xs ys : List Int) : List Int := addFuel (xs.length + ys.length + 1) 0 xs ys

/-! ## Correctness: value preservation, carry-general first -/

/-- **The crux lemma, CARRY-GENERAL**: for any starting carry `c` and any fuel covering both
    lists' lengths, the value of the fold's output is `c` plus the two input values.  Proved by
    induction on `fuel`; each cons/cons (or cons/nil, nil/cons) step needs exactly ONE nonlinear
    fact, `10 * (s / 10) + s % 10 = s` (`Int.mul_ediv_add_emod`), supplied explicitly — the
    remainder of each step is then a pure linear rearrangement. -/
theorem addFuel_value : ∀ (fuel : Nat) (c : Int) (xs ys : List Int),
    xs.length + ys.length ≤ fuel → value (addFuel fuel c xs ys) = c + value xs + value ys := by
  intro fuel
  induction fuel with
  | zero =>
    intro c xs ys hlen
    have hxsnil : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hysnil : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst hxsnil; subst hysnil
    by_cases hc : c = 0
    · show value (if c = 0 then [] else [c]) = c + value [] + value []
      rw [if_pos hc]; simp only [value]; omega
    · show value (if c = 0 then [] else [c]) = c + value [] + value []
      rw [if_neg hc]; simp only [value]; omega
  | succ fuel ih =>
    intro c xs ys hlen
    cases xs with
    | nil =>
      cases ys with
      | nil =>
        by_cases hc : c = 0
        · show value (if c = 0 then [] else [c]) = c + value [] + value []
          rw [if_pos hc]; simp only [value]; omega
        · show value (if c = 0 then [] else [c]) = c + value [] + value []
          rw [if_neg hc]; simp only [value]; omega
      | cons y ys' =>
        have hlen' : ([] : List Int).length + ys'.length ≤ fuel := by
          simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
        have hIH := ih ((c + y) / 10) [] ys' hlen'
        show value ((c + y) % 10 :: addFuel fuel ((c + y) / 10) [] ys')
            = c + value ([] : List Int) + value (y :: ys')
        have hkey : 10 * ((c + y) / 10) + (c + y) % 10 = c + y := Int.mul_ediv_add_emod (c + y) 10
        simp only [value] at hIH ⊢
        omega
    | cons x xs' =>
      cases ys with
      | nil =>
        have hlen' : xs'.length + ([] : List Int).length ≤ fuel := by
          simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
        have hIH := ih ((c + x) / 10) xs' [] hlen'
        show value ((c + x) % 10 :: addFuel fuel ((c + x) / 10) xs' [])
            = c + value (x :: xs') + value ([] : List Int)
        have hkey : 10 * ((c + x) / 10) + (c + x) % 10 = c + x := Int.mul_ediv_add_emod (c + x) 10
        simp only [value] at hIH ⊢
        omega
      | cons y ys' =>
        have hlen' : xs'.length + ys'.length ≤ fuel := by
          simp only [List.length_cons] at hlen; omega
        have hIH := ih ((c + x + y) / 10) xs' ys' hlen'
        show value ((c + x + y) % 10 :: addFuel fuel ((c + x + y) / 10) xs' ys')
            = c + value (x :: xs') + value (y :: ys')
        have hkey : 10 * ((c + x + y) / 10) + (c + x + y) % 10 = c + x + y :=
          Int.mul_ediv_add_emod (c + x + y) 10
        simp only [value] at hIH ⊢
        omega

/-- **Correctness of the allegory program** (the headline theorem): `addFn` preserves value —
    the sum of the two input numbers equals the number denoted by the output digit list. -/
theorem add_correct (xs ys : List Int) : value (addFn xs ys) = value xs + value ys := by
  have h := addFuel_value (xs.length + ys.length + 1) 0 xs ys (by omega)
  show value (addFuel (xs.length + ys.length + 1) 0 xs ys) = value xs + value ys
  omega

/-! ## `Rel(Set)` packaging -/

/-- The input object: the two little-endian digit lists to add. -/
abbrev dInput : RelSet.{0} := ⟨List Int × List Int⟩
/-- The answer object: the sum's little-endian digit list. -/
abbrev dAns : RelSet.{0} := ⟨List Int⟩

/-- **The allegory program**: LeetCode 2's digit-list addition as a morphism `dInput ⟶ dAns` in
    `Rel(Set)`. -/
def solve : dInput ⟶ dAns := graph (fun p : List Int × List Int => addFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : List Int × List Int => addFn p.1 p.2)

/-! ## The morphism-equation headline (value level)

  The output is a canonical little-endian digit list, but the VALUE equation alone does not pin it
  (`[7,0,8]` and `[7,0,8,0]` both denote `708`).  Full pinning needs a `Canon` uniqueness lemma
  plus a two-input carry `addFuel_canon` (the analogue of `leet/L66.lean`'s `plusOneRev_canon`,
  longer here because of the two-list carry ripple) — deferred.  What IS a clean morphism equation:
  decoding `solve`'s output gives exactly the sum of the two input values. -/

/-- The object of decoded integer values. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-- **The value-level specification** as a relation `dInput ⟶ dAns`: `out` denotes the sum of the
    two input numbers.  (Program-independent; does NOT pin the digit list — canonicity would.) -/
def spec : dInput ⟶ dAns := fun p out => value out = value p.1 + value p.2

/-- **The value-level headline**: `solve ≫ value = (the sum of the two input values)` as morphisms
    into `⟨Int⟩` — decode the program's output and you get the sum, exactly (not merely pointwise).
    (The weaker-than-`solve = spec` shape is the honest one: `value` under-determines the digits.) -/
theorem solve_value_eq :
    solve ≫ (graph value : dAns ⟶ dZ)
      = (graph (fun p : List Int × List Int => value p.1 + value p.2) : dInput ⟶ dZ) := by
  apply hom_ext; intro p v
  constructor
  · rintro ⟨w, hw, hv⟩; show v = value p.1 + value p.2; rw [hv, hw]; exact add_correct p.1 p.2
  · intro hv; exact ⟨addFn p.1 p.2, rfl, by show v = value (addFn p.1 p.2); rw [hv]; exact (add_correct p.1 p.2).symm⟩

/-- **Refinement**: every digit list `solve` returns denotes the sum — the program refines `spec`. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun p out h => ?_)
  have hout : out = addFn p.1 p.2 := h
  show value out = value p.1 + value p.2
  rw [hout]; exact add_correct p.1 p.2

/-! ## Running the program -/

example : addFn ([2, 4, 3] : List Int) [5, 6, 4] = [7, 0, 8] := by decide
example : addFn ([9, 9] : List Int) [1] = [0, 0, 1] := by decide

end Freyd.Alg.RelSet.LC2
