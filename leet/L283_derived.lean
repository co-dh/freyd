/-
  LeetCode 283 — Move Zeroes — DERIVED as a cons-list catamorphism, O(n).

  `leet/L283.lean` packages the answer as `solve := graph moveZeroesFn` with `moveZeroesFn xs :=
  xs.filter nzPred ++ List.replicate (xs.filter zPred).length 0` over a RAW Lean `List Int` — a
  one-shot `filter`/`++`, not a `cataR`.  This file RESHAPES the data onto the canonical cons-list
  initial algebra `ConsList Unit Int` (`list Int` of the book, base at `wrap ()`, recursion on the
  tail, via the SHARED `CL.ofList`) and reads `moveZeroesFn` off as an ordinary cons-fold, with the
  PAIR carrier so the program is O(n):

    * `C := List Int × Nat`  — (the non-zeros seen so far, consed in order; the count of zeros seen
      so far).

  The base/step are ordinary and FORCED (both `rfl`):

    * base   `g _     = ([], 0)`                                     = `h (wrap _)`
    * step   `st x c  = if nzPred x then (x :: c.1, c.2) else (c.1, c.2 + 1)`
                                                                       = `h (cons x xs)` with `c = h xs`.

  The step CONSES the head onto the kept-list when it is non-zero (`x :: c.1`, O(1)) instead of
  snocing onto the tail (`c.1 ++ [x]`, O(n)) — so the fold itself is O(n).  Feeding `g`/`st`/`h` to
  the general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`) PRODUCES
  this fold as `cataR (consScalarAlg g st)` — the fold is emitted by the law, never written as a
  fold.  Readout does exactly ONE `++`, at the very end (`nzs ++ List.replicate zc 0`), never inside
  the step — the single append that turns an O(n) list of kept non-zeros plus a zero-count into the
  final answer.

  The bridge `h_ofList` (`h (ofList xs) = (xs.filter nzPred, (xs.filter zPred).length)`) identifies
  the cons-fold with the two filters `moveZeroesFn` already uses, so `derivedFn = moveZeroesFn`
  pointwise.  Only the DATA is reshaped and the fold PRODUCED; the four-clause correctness
  (`move_correct`) is REUSED from `L283.lean`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L283

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC283D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The pair carrier and its filtering fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here
  `C = List Int × Nat` — the non-zeros kept so far (consed, so front-to-back order is preserved) and
  a running count of the zeros dropped so far.  Each step conses onto the kept-list (O(1)) or bumps
  the counter (O(1)), so folding a length-`n` list is O(n). -/

/-- The base of the emergent algebra: the empty suffix has kept nothing and seen no zeros. -/
def g : Unit → (List Int × Nat) := fun _ => ([], 0)

/-- The step of the emergent algebra: a non-zero head is CONSED onto the kept-list (`x :: c.1`,
    O(1) — this is what makes the derived program O(n), never `c.1 ++ [x]`); a zero head bumps the
    counter. -/
def st : Int → (List Int × Nat) → (List Int × Nat) :=
  fun x c => if LC283.nzPred x then (x :: c.1, c.2) else (c.1, c.2 + 1)

/-- The filtering fold over the cons-list initial algebra, mirroring `LC283.moveZeroesFn`'s two
    filters: `wrap _ ↦ ([], 0)`, `cons x xs ↦ st x (h xs)`. -/
def h : ConsList Unit Int → List Int × Nat
  | ConsList.wrap _   => g ()
  | ConsList.cons x xs => st x (h xs)

/-- The base condition is a COMPUTATION, not a guess: `h (wrap d) = g d`. -/
theorem hwrap : ∀ d : Unit, h (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `h`'s cons equation: `h (cons x xs) = st x (h xs)`. -/
theorem hcons : ∀ (x : Int) (xs : ConsList Unit Int), h (ConsList.cons x xs) = st x (h xs) :=
  fun _ _ => rfl

/-! ## The stable partition EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The stable partition of `xs` by non-zero-ness, RESHAPED onto the cons-list
    initial algebra `ConsList Unit Int` with the PAIR carrier `List Int × Nat`, IS the catamorphism
    of the emergent scalar algebra `consScalarAlg g st` — it was never written as a fold: `graph h`
    equals `cataR (consScalarAlg g st)`.  Consing the non-zero head onto the kept-list is the point:
    an O(n) filtering fold is emitted by `consFold_unique`. -/
theorem move_emerges :
    (graph h : dCL Unit Int ⟶ ⟨List Int × Nat⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st h hwrap hcons

/-! ## Bridge to the hand-written raw-`List` solution -/

/-- The reshaped fold IS `moveZeroesFn`'s two filters, packaged as a pair:
    `h (ofList xs) = (xs.filter nzPred, (xs.filter zPred).length)`, by induction on `xs`. -/
theorem h_ofList (xs : List Int) :
    h (CL.ofList xs) = (xs.filter LC283.nzPred, (xs.filter LC283.zPred).length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show st x (h (CL.ofList xs)) = _
      rw [ih]
      unfold st
      cases hz : LC283.zPred x with
      | true =>
          have hn : LC283.nzPred x = false := by
            rw [LC283.nzPred_eq_not_zPred, hz]; rfl
          simp [hn, hz, List.length_cons]
      | false =>
          have hn : LC283.nzPred x = true := by
            rw [LC283.nzPred_eq_not_zPred, hz]; rfl
          simp [hn, hz]

/-- **The derived program**: readout of the reshaped fold at the initial-algebra image of `xs` — the
    ONE `++` in the whole derivation, appending the zero-count's `replicate` after the kept-list. -/
def derivedFn (xs : List Int) : List Int :=
  (h (CL.ofList xs)).1 ++ List.replicate (h (CL.ofList xs)).2 0

/-- The derived program IS `moveZeroesFn`, pointwise. -/
theorem derivedFn_eq_moveZeroesFn (xs : List Int) : derivedFn xs = LC283.moveZeroesFn xs := by
  show (h (CL.ofList xs)).1 ++ List.replicate (h (CL.ofList xs)).2 0
     = xs.filter LC283.nzPred ++ List.replicate (xs.filter LC283.zPred).length 0
  rw [h_ofList xs]

/-! ## Correctness carries over from `L283.lean` (no re-proof) -/

/-- **Headline.**  The honest bundle for the STRUCTURAL-OUTPUT case, now O(n):

    (1) the stable partition, reshaped onto the cons-list initial algebra with the PAIR carrier, IS
        the catamorphism of `consScalarAlg g st` — the O(n) filtering fold EMERGES from
        `consFold_unique` (`move_emerges`);
    (2) the `Map` `LC283.solve` (LeetCode 283's answer relation) relates each input to exactly the
        derived program's output (`derivedFn_eq_moveZeroesFn`); and
    (3) the derived program satisfies the same four honest clauses as `moveZeroesFn` — the REUSED
        `LC283.move_correct`, not re-proved here.

    The program (the O(n) filtering fold) is PRODUCED by the law; the correctness proof is reused. -/
theorem move_derived_correct :
    ((graph h : dCL Unit Int ⟶ ⟨List Int × Nat⟩) = cataR (consScalarAlg g st))
      ∧ (∀ (xs ys : List Int), LC283.solve xs ys ↔ ys = derivedFn xs)
      ∧ (∀ xs : List Int,
          (derivedFn xs).filter LC283.nzPred = xs.filter LC283.nzPred ∧
          (derivedFn xs).length = xs.length ∧
          (∀ v, LC242.countL (derivedFn xs) v = LC242.countL xs v) ∧
          (∃ k, derivedFn xs = xs.filter LC283.nzPred ++ List.replicate k 0 ∧
            ∀ a ∈ xs.filter LC283.nzPred, a ≠ 0)) := by
  refine ⟨move_emerges, ?_, ?_⟩
  · intro xs ys
    show (ys = LC283.moveZeroesFn xs) ↔ ys = derivedFn xs
    rw [derivedFn_eq_moveZeroesFn xs]
  · intro xs
    rw [derivedFn_eq_moveZeroesFn xs]
    exact LC283.move_correct xs

/-! ## Running / cross-checking the reshaped fold -/

example : derivedFn [0, 1, 0, 3, 12] = [1, 3, 12, 0, 0] := by decide
example : derivedFn [0] = [0] := by decide
example : derivedFn [1, 2, 3] = [1, 2, 3] := by decide

/-- The reshaped fold genuinely relates the converted input to the (pair-valued) catamorphism it
    emerges as. -/
example :
    cataFold (consScalarAlg g st) (CL.ofList [0, 1, 0, 3, 12]) (h (CL.ofList [0, 1, 0, 3, 12])) := by
  have hh : (graph h : dCL Unit Int ⟶ ⟨List Int × Nat⟩)
      (CL.ofList [0, 1, 0, 3, 12]) (h (CL.ofList [0, 1, 0, 3, 12])) := rfl
  rw [move_emerges] at hh
  exact hh

end Freyd.Alg.RelSet.LC283D
