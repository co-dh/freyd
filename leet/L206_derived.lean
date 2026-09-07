/-
  LeetCode 206 — Reverse Linked List — DERIVED as a cons-list catamorphism, O(n).

  `leet/L206.lean` packages the answer as `solve := graph revFn` with `revFn := List.reverse` over a
  RAW Lean `List Int` — Lean core's `List.reverse`, NOT the repo's initial-algebra list, so as written
  it is not a `cataR`.  This file RESHAPES the data onto the canonical cons-list initial algebra
  `ConsList Unit Int` (`list Int` of the book, base at `wrap ()`, recursion on the tail) and reads
  reversal off as an ordinary cons-fold — but with the ACCUMULATOR carrier so the program is O(n):

    * `C := List Int → List Int`  — a difference list: "reverse the folded suffix in FRONT of `acc`".

  The base/step are ordinary and FORCED (both `rfl`):

    * base   `g _      = (id : List Int → List Int)`      = `revAcc (wrap _)`
    * step   `st x k   = fun acc => k (x :: acc)`         = `revAcc (cons x xs)` with `k = revAcc xs`.

  The step PREPENDS the head onto the accumulator (`x :: acc`, O(1)) instead of snocing onto the tail
  (`acc ++ [x]`, O(n)) — so the emergent program runs in O(n), matching `List.reverse`'s own
  accumulator recursion.  Feeding `g`/`st`/`revAcc` to the general-carrier law
  `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`) PRODUCES this fold as
  `cataR (consScalarAlg g st)` — the fold is emitted by the law, never written as a fold.  The bridge
  `revAcc_ofList` (`revAcc (ofList xs) acc = xs.reverseAux acc`) identifies the accumulator recursion
  with Lean core's own, so at the empty accumulator `revAcc (ofList xs) [] = xs.reverse`.

  Only the DATA is reshaped; the structural laws (`revFn xs = xs.reverse`, involutivity `rev_rev`) are
  REUSED from `L206.lean`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L206

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC206D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The accumulator carrier and its prepending fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here
  `C = List Int → List Int` — a difference list.  `revAcc xs` is the function that, given whatever has
  already been reversed after `xs`, reverses `xs` in FRONT of it.  Each step prepends the head onto the
  accumulator (`x :: acc`, O(1)), so folding a length-`n` list is O(n) — unlike a fold that snocs onto
  the folded tail (`acc ++ [x]`, O(n) per step, O(n²) overall). -/

/-- The base of the emergent algebra: the empty suffix contributes nothing — return the accumulator. -/
def g : Unit → (List Int → List Int) := fun _ => id

/-- The step of the emergent algebra: prepend the head `x` onto the accumulator, then run the folded
    tail `k`.  `x :: acc` is O(1) — this is what makes the derived reversal O(n). -/
def st : Int → (List Int → List Int) → (List Int → List Int) := fun x k => fun acc => k (x :: acc)

/-- Reversal as an ACCUMULATOR fold over the cons-list initial algebra, mirroring `LC206.revFn`:
    `wrap _ ↦ id`, `cons x xs ↦ st x (revAcc xs) = fun acc => revAcc xs (x :: acc)`. -/
def revAcc : ConsList Unit Int → (List Int → List Int)
  | ConsList.wrap _    => g ()
  | ConsList.cons x xs => st x (revAcc xs)

/-- The base condition is a COMPUTATION, not a guess: `revAcc (wrap d) = g d`. -/
theorem revAcc_wrap : ∀ d : Unit, revAcc (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `revAcc`'s cons equation: `revAcc (cons x xs) = st x (revAcc xs)`. -/
theorem revAcc_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), revAcc (ConsList.cons x xs) = st x (revAcc xs) :=
  fun _ _ => rfl

/-! ## Reversal EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  Reversal, RESHAPED onto the cons-list initial algebra `ConsList Unit Int` with
    the ACCUMULATOR carrier, IS the catamorphism of the emergent scalar algebra `consScalarAlg g st` —
    it was never written as a fold: `graph revAcc` equals `cataR (consScalarAlg g st)`.  Prepending the
    head onto the accumulator is the point: an O(n) list-reversing fold is emitted by
    `consFold_unique`. -/
theorem rev_emerges :
    (graph revAcc : dCL Unit Int ⟶ ⟨List Int → List Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st revAcc revAcc_wrap revAcc_cons

/-! ## Bridge to the hand-written raw-`List` solution -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The reshaped accumulator fold IS Lean core's own `List.reverseAux`:
    `revAcc (ofList xs) acc = xs.reverseAux acc`, by induction on `xs`.  The cons step is pure
    computation: `revAcc (ofList (x::xs)) acc = revAcc (ofList xs) (x :: acc)` and
    `(x::xs).reverseAux acc = xs.reverseAux (x :: acc)`. -/
theorem revAcc_ofList : ∀ (xs acc : List Int), revAcc (ofList xs) acc = xs.reverseAux acc
  | [],      acc => rfl
  | x :: xs, acc => by
      show revAcc (ofList xs) (x :: acc) = (x :: xs).reverseAux acc
      exact revAcc_ofList xs (x :: acc)

/-- At the empty accumulator the fold recovers the raw-`List` reversal:
    `revAcc (ofList xs) [] = xs.reverseAux [] = xs.reverse = LC206.revFn xs`. -/
theorem revAcc_ofList_nil (xs : List Int) : revAcc (ofList xs) [] = LC206.revFn xs := by
  rw [revAcc_ofList xs []]
  rfl

/-! ## Correctness carries over from `L206.lean` (no re-proof) -/

/-- **Headline.**  The honest bundle for the STRUCTURAL-OUTPUT case, now O(n):

    (1) reversal, reshaped onto the cons-list initial algebra with the ACCUMULATOR carrier, IS the
        catamorphism of `consScalarAlg g st` — the O(n) reversing fold EMERGES from `consFold_unique`
        (`rev_emerges`);
    (2) the `Map` `LC206.solve` (LeetCode 206's answer relation) relates each input to exactly the
        emergent catamorphism run at the empty accumulator (`revAcc_ofList_nil`); and
    (3) applying the reversal again returns the input — the REUSED involutivity `LC206.rev_rev`, not
        re-proved here.

    The program (the O(n) reversing fold) is PRODUCED by the law; the structural laws are reused. -/
theorem rev_derived_correct :
    ((graph revAcc : dCL Unit Int ⟶ ⟨List Int → List Int⟩) = cataR (consScalarAlg g st))
      ∧ (∀ (xs ys : List Int), LC206.solve xs ys ↔ ys = revAcc (ofList xs) [])
      ∧ (∀ xs : List Int, LC206.revFn (revAcc (ofList xs) []) = xs) := by
  refine ⟨rev_emerges, ?_, ?_⟩
  · intro xs ys
    show (ys = LC206.revFn xs) ↔ ys = revAcc (ofList xs) []
    rw [revAcc_ofList_nil xs]
  · intro xs
    rw [revAcc_ofList_nil xs]
    exact LC206.rev_rev xs

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier, here a function type), so we `decide` the extensionally-equal
  computable witness `revAcc ∘ ofList` run at the empty accumulator — an applied `List Int`, decidable
  (never the function carrier itself). -/

/-- `[1,2,3] → [3,2,1]`. -/
example : revAcc (ofList [1, 2, 3]) [] = [3, 2, 1] := by decide
/-- `[] → []`. -/
example : revAcc (ofList []) [] = [] := by decide
/-- `[1] → [1]`. -/
example : revAcc (ofList [1]) [] = [1] := by decide

/-- The reshaped fold genuinely relates the converted input to the (function-valued) catamorphism it
    emerges as. -/
example :
    cataFold (consScalarAlg g st) (ofList [1, 2, 3]) (revAcc (ofList [1, 2, 3])) := by
  have h : (graph revAcc : dCL Unit Int ⟶ ⟨List Int → List Int⟩)
      (ofList [1, 2, 3]) (revAcc (ofList [1, 2, 3])) := rfl
  rw [rev_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC206D
