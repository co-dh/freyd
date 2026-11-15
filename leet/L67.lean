/-
  LeetCode 67 — Add Binary — as an ALLEGORY PROGRAM.

  Problem: two non-negative integers are given as BIG-ENDIAN binary digit lists (`0`/`1`, most
  significant digit first), as `List Int`.  Return the big-endian binary digits of their sum.

  Combines `L66`'s big-endian/little-endian bridge with `L2`'s two-input carry-ripple fold, base
  `2` instead of base `10`: reverse both inputs to little-endian, ripple-add with carry (a genuine
  TWO-INPUT recursion, tamed by an explicit FUEL parameter, Skill S13/S21), then reverse the
  little-endian result back to big-endian.

  1. **Value semantics.** `value : List Int → Int` reads a BIG-ENDIAN binary digit list back into
     the integer it denotes, via a left fold (Horner's method, base `2`): `value xs := xs.foldl
     (fun acc d => acc*2+d) 0`.  Internally the program works LITTLE-ENDIAN, `valueLE (d :: ds) =
     d + 2 * valueLE ds` — literally `L2.value`/`L66.valueLE` restated at base `2`, kept
     self-contained here (a different problem, not a wrapper).

  2. **Program.** `addBitsRev fuel c xs ys` — schoolbook binary addition with carry `c` over the
     REVERSED (little-endian) inputs: both lists empty, emit the leftover carry (`[]` if `0`);
     otherwise pop a bit from each PRESENT list (`0` if a list is already exhausted), form
     `s := c + x + y`, emit `s % 2`, recurse on one less fuel with carry `s / 2`.  `addBinaryFn xs
     ys := (addBitsRev (xs.length+ys.length+1) 0 xs.reverse ys.reverse).reverse` — the `+1` covers
     a genuine carry-out digit past the longer input (e.g. `11 + 1 = 100`), and reversal at both
     ends turns the big-endian inputs into the little-endian shape the ripple needs, then back.

  3. **The bridge `value = valueLE ∘ reverse`.** Exactly `L66.value_eq_valueLE_reverse`: core
     `List.foldl_eq_foldr_reverse` turns the big-endian LEFT fold into a RIGHT fold over the
     reversed list, identified with `valueLE`'s own front-consing recursion by one induction — no
     explicit powers of `2`, no append lemmas.

  4. **The crux lemma is CARRY-GENERAL.** `addBitsRev_value : xs.length + ys.length ≤ fuel →
     valueLE (addBitsRev fuel c xs ys) = c + valueLE xs + valueLE ys`, by induction on `fuel`
     (carry `c` FREE through the induction, Skill S45) — the `c := 0` specialization, composed
     with the BE↔LE bridge on both ends, gives `addBinary_correct`. Each cons/cons (or cons/nil,
     nil/cons) step needs exactly one nonlinear fact, `2 * (s / 2) + s % 2 = s`
     (`Int.mul_ediv_add_emod`, the non-deprecated form of `Int.ediv_add_emod`), supplied
     explicitly; the remainder of each step is then a linear rearrangement `omega` closes.

  Mathlib-free; axioms ⊆ {propext, Quot.sound} — fully constructive, no `Classical.choice`.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC67

open Freyd

/-! ## Value semantics: read a binary digit list back into the integer it denotes -/

/-- `value xs` reads a BIG-ENDIAN binary digit list (most-significant digit first) back into the
    integer it denotes, via a left fold (Horner's method, base `2`):
    `value [1,0,1,1] = (((0*2+1)*2+0)*2+1)*2+1 = 11`. -/
def value (xs : List Int) : Int := xs.foldl (fun acc d => acc * 2 + d) 0

/-- `valueLE ys` reads a LITTLE-ENDIAN binary digit list (least-significant digit first) back into
    the integer it denotes: `valueLE [] = 0`, `valueLE (d :: ds) = d + 2 * valueLE ds` — `L2.value`
    at base `2`, restated here so this file stays self-contained. -/
def valueLE : List Int → Int
  | [] => 0
  | d :: ds => d + 2 * valueLE ds

/-- **The bridge, crux half**: `value`'s left fold, once flipped to a right fold over the SAME
    (little-endian) list by `foldl_eq_foldr_reverse`, computes exactly `valueLE` — both recurse
    front-to-back on `ys`, so the step functions line up by one `omega` per cons, no powers. -/
theorem foldr_eq_valueLE : ∀ ys : List Int, ys.foldr (fun d acc => acc * 2 + d) 0 = valueLE ys
  | [] => rfl
  | d :: ds => by
      have ih := foldr_eq_valueLE ds
      show (ds.foldr (fun d acc => acc * 2 + d) 0) * 2 + d = valueLE (d :: ds)
      rw [ih]; simp only [valueLE]; omega

/-- **The bridge**: a big-endian value equals the little-endian value of the REVERSED list. -/
theorem value_eq_valueLE_reverse (xs : List Int) : value xs = valueLE xs.reverse := by
  show xs.foldl (fun acc d => acc * 2 + d) 0 = valueLE xs.reverse
  rw [List.foldl_eq_foldr_reverse]
  exact foldr_eq_valueLE xs.reverse

/-! ## Program: two-input carry-ripple addition over the little-endian (reversed) inputs -/

/-- `addBitsRev fuel c xs ys` — schoolbook BINARY addition with carry `c`. Both lists empty: emit
    the leftover carry (`[]` if it is `0`). Otherwise: pop a bit from each PRESENT list (`0` if a
    list is already exhausted), emit `s % 2` for `s := c + x + y`, recurse with carry `s / 2` on
    one less fuel. Structural on `fuel`, hence kernel-reducible. -/
def addBitsRev : Nat → Int → List Int → List Int → List Int
  | 0, c, _, _ => if c = 0 then [] else [c]
  | _ + 1, c, [], [] => if c = 0 then [] else [c]
  | fuel + 1, c, x :: xs, [] => (c + x) % 2 :: addBitsRev fuel ((c + x) / 2) xs []
  | fuel + 1, c, [], y :: ys => (c + y) % 2 :: addBitsRev fuel ((c + y) / 2) [] ys
  | fuel + 1, c, x :: xs, y :: ys => (c + x + y) % 2 :: addBitsRev fuel ((c + x + y) / 2) xs ys

/-- **The program**: add two BIG-ENDIAN binary digit lists — reverse both to little-endian, ripple
    the carry-add with `xs.length + ys.length + 1` fuel (the `+1` covers a genuine carry-out digit
    past the longer input, e.g. `addBinaryFn [1,1] [1] = [1,0,0]`, `3 + 1 = 4`), reverse back. -/
def addBinaryFn (xs ys : List Int) : List Int :=
  (addBitsRev (xs.length + ys.length + 1) 0 xs.reverse ys.reverse).reverse

/-! ## Correctness: value preservation, carry-general first -/

/-- **The crux lemma, CARRY-GENERAL**: for any starting carry `c` and any fuel covering both
    lists' lengths, the value of the fold's output is `c` plus the two input values. Proved by
    induction on `fuel`; each cons/cons (or cons/nil, nil/cons) step needs exactly ONE nonlinear
    fact, `2 * (s / 2) + s % 2 = s` (`Int.mul_ediv_add_emod`), supplied explicitly — the remainder
    of each step is then a pure linear rearrangement. -/
theorem addBitsRev_value : ∀ (fuel : Nat) (c : Int) (xs ys : List Int),
    xs.length + ys.length ≤ fuel → valueLE (addBitsRev fuel c xs ys) = c + valueLE xs + valueLE ys := by
  intro fuel
  induction fuel with
  | zero =>
    intro c xs ys hlen
    have hxsnil : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hysnil : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst hxsnil; subst hysnil
    by_cases hc : c = 0
    · show valueLE (if c = 0 then [] else [c]) = c + valueLE [] + valueLE []
      rw [if_pos hc]; simp only [valueLE]; omega
    · show valueLE (if c = 0 then [] else [c]) = c + valueLE [] + valueLE []
      rw [if_neg hc]; simp only [valueLE]; omega
  | succ fuel ih =>
    intro c xs ys hlen
    cases xs with
    | nil =>
      cases ys with
      | nil =>
        by_cases hc : c = 0
        · show valueLE (if c = 0 then [] else [c]) = c + valueLE [] + valueLE []
          rw [if_pos hc]; simp only [valueLE]; omega
        · show valueLE (if c = 0 then [] else [c]) = c + valueLE [] + valueLE []
          rw [if_neg hc]; simp only [valueLE]; omega
      | cons y ys' =>
        have hlen' : ([] : List Int).length + ys'.length ≤ fuel := by
          simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
        have hIH := ih ((c + y) / 2) [] ys' hlen'
        show valueLE ((c + y) % 2 :: addBitsRev fuel ((c + y) / 2) [] ys')
            = c + valueLE ([] : List Int) + valueLE (y :: ys')
        have hkey : 2 * ((c + y) / 2) + (c + y) % 2 = c + y := Int.mul_ediv_add_emod (c + y) 2
        simp only [valueLE] at hIH ⊢
        omega
    | cons x xs' =>
      cases ys with
      | nil =>
        have hlen' : xs'.length + ([] : List Int).length ≤ fuel := by
          simp only [List.length_cons, List.length_nil] at hlen ⊢; omega
        have hIH := ih ((c + x) / 2) xs' [] hlen'
        show valueLE ((c + x) % 2 :: addBitsRev fuel ((c + x) / 2) xs' [])
            = c + valueLE (x :: xs') + valueLE ([] : List Int)
        have hkey : 2 * ((c + x) / 2) + (c + x) % 2 = c + x := Int.mul_ediv_add_emod (c + x) 2
        simp only [valueLE] at hIH ⊢
        omega
      | cons y ys' =>
        have hlen' : xs'.length + ys'.length ≤ fuel := by
          simp only [List.length_cons] at hlen; omega
        have hIH := ih ((c + x + y) / 2) xs' ys' hlen'
        show valueLE ((c + x + y) % 2 :: addBitsRev fuel ((c + x + y) / 2) xs' ys')
            = c + valueLE (x :: xs') + valueLE (y :: ys')
        have hkey : 2 * ((c + x + y) / 2) + (c + x + y) % 2 = c + x + y :=
          Int.mul_ediv_add_emod (c + x + y) 2
        simp only [valueLE] at hIH ⊢
        omega

/-- **Correctness of the allegory program** (the headline theorem): `addBinaryFn` preserves value
    — the sum of the two input binary numbers equals the number denoted by the output digit list.
    Proved by composing the carry-general crux lemma (at `c := 0`) with the BE↔LE bridge on both
    inputs and the reversed output. -/
theorem addBinary_correct (xs ys : List Int) :
    value (addBinaryFn xs ys) = value xs + value ys := by
  show value ((addBitsRev (xs.length + ys.length + 1) 0 xs.reverse ys.reverse).reverse)
      = value xs + value ys
  rw [value_eq_valueLE_reverse, List.reverse_reverse]
  have hlen : xs.reverse.length + ys.reverse.length ≤ xs.length + ys.length + 1 := by
    simp only [List.length_reverse]; omega
  have h := addBitsRev_value (xs.length + ys.length + 1) 0 xs.reverse ys.reverse hlen
  rw [value_eq_valueLE_reverse xs, value_eq_valueLE_reverse ys]
  omega

/-! ## `Rel(Set)` packaging -/

/-- The input object: the two big-endian binary digit lists to add. -/
abbrev dInput : RelSet.{0} := ⟨List Int × List Int⟩
/-- The answer object: the sum's big-endian binary digit list. -/
abbrev dAns : RelSet.{0} := ⟨List Int⟩

/-- **The allegory program**: LeetCode 67's binary addition as a morphism `dInput ⟶ dAns` in
    `Rel(Set)`. -/
def solve : dInput ⟶ dAns := graph (fun p : List Int × List Int => addBinaryFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : List Int × List Int => addBinaryFn p.1 p.2)

/-! ## The morphism-equation headline (value level)

  The output is a canonical big-endian binary list, but the VALUE equation alone does not pin it
  (`[1,0,0]` and `[0,1,0,0]` both denote `4`).  Full pinning needs a `Canon` uniqueness lemma plus
  a two-input carry `addBitsRev_canon` (the analogue of `leet/L66.lean`'s `plusOneRev_canon`,
  longer here because of the two-list carry ripple) — deferred.  What IS a clean morphism equation:
  decoding `solve`'s output gives exactly the sum of the two input values. -/

/-- The object of decoded integer values. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-- **The value-level specification** as a relation `dInput ⟶ dAns`: `out` denotes the sum of the
    two input binary numbers.  (Program-independent; does NOT pin the digit list — canonicity would.) -/
def spec : dInput ⟶ dAns := fun p out => value out = value p.1 + value p.2

/-- **The value-level headline**: `solve ≫ value = (the sum of the two input values)` as morphisms
    into `⟨Int⟩` — decode the program's output and you get the sum, exactly (not merely pointwise).
    (The weaker-than-`solve = spec` shape is the honest one: `value` under-determines the digits.) -/
theorem solve_value_eq :
    solve ≫ (graph value : dAns ⟶ dZ)
      = (graph (fun p : List Int × List Int => value p.1 + value p.2) : dInput ⟶ dZ) := by
  apply hom_ext; intro p v
  constructor
  · rintro ⟨w, hw, hv⟩; show v = value p.1 + value p.2; rw [hv, hw]; exact addBinary_correct p.1 p.2
  · intro hv; exact ⟨addBinaryFn p.1 p.2, rfl,
      by show v = value (addBinaryFn p.1 p.2); rw [hv]; exact (addBinary_correct p.1 p.2).symm⟩

/-- **Refinement**: every digit list `solve` returns denotes the sum — the program refines `spec`. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun p out h => ?_)
  have hout : out = addBinaryFn p.1 p.2 := h
  show value out = value p.1 + value p.2
  rw [hout]; exact addBinary_correct p.1 p.2

/-! ## Running the program -/

example : addBinaryFn ([1, 0, 1, 1] : List Int) [1, 0, 1] = [1, 0, 0, 0, 0] := by decide
example : addBinaryFn ([1, 1] : List Int) [1] = [1, 0, 0] := by decide

end Freyd.Alg.RelSet.LC67
