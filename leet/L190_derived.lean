/-
  LeetCode 190 — Reverse Bits — DERIVED as a cons-list catamorphism (O(m), accumulator carrier).

  `leet/L190.lean` packages the solution as `revBits := List.reverse` on the LSB-first bit-list,
  `solve : dBits ⟶ dBits := graph revBits` — a STRUCTURAL-OUTPUT endomorphism (source and target the
  same object `List Bool`, cf. `L206`).  Unlike `L226` (tree inversion, whose `solve_eq_cata` already
  exhibits it AS `cataR alg` — a wrapper we skip), `revBits` is Lean core's accumulator-based
  `List.reverse`, NOT written as a structural fold, so there is genuine content in making it EMERGE
  as a catamorphism.

  Bit-reversal as a FRONT-TO-BACK fold: the naive `reverse (x :: xs) = reverse xs ++ [x]` snocs the
  head, an O(1)·per-step append AT THE END, so folding it over an `m`-bit word costs O(m²).  The
  efficient program uses the standard accumulator trick (Lean core's own `List.reverseAux`): carry a
  FUNCTION `C := List Bool → List Bool` (the reversed-so-far list awaiting the accumulator) and
  PREPEND the head — an O(1) cons — building the answer in O(m) total.  This is a cons-list
  catamorphism (`F X = 1 + Bool × X`, base at `wrap`/nil, recursion on the tail) with

    * carrier `C := List Bool → List Bool`  — the reversal continuation, and
    * base   `g _      = (id : List Bool → List Bool)`          (empty word: return the accumulator),
    * step   `st x k   = fun acc => k (x :: acc)`               (PREPEND the head, O(1), NO `++`).

  Applied to the empty accumulator the continuation yields the reversed list:
  `revAcc (ofList bs) [] = bs.reverse = LC190.revBits bs`, via the helper induction
  `revAcc (ofList bs) acc = bs.reverse ++ acc`.  The input `List Bool` is not the initial-algebra
  list, so `revBits` as written is not a catamorphism; this file RESHAPES the data onto the repo's
  canonical cons-list initial algebra `ConsList Unit Bool` and lets the fold EMERGE via the
  general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`) — the same
  law that emits list-DPs, here with a FUNCTION carrier.

  Correctness is REUSED, not re-proved: the reshaped-then-converted fold reproduces `revBits`
  (`LC190.solve_correct` across the bridge `revBits_ofList`), and reversing bits twice is the identity
  (`LC190.rev_rev`, `L190`'s structural extra law).

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L190

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC190D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The function carrier and its O(m) bit-reversal fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here
  `C = List Bool → List Bool` — the reversal continuation (the reversed-so-far list awaiting an
  accumulator).  The step PREPENDS the head onto the accumulator, an O(1) cons, so the whole fold is
  O(m) (contrast the naive `prev ++ [x]`, O(m²)). -/

/-- The base of the emergent algebra: the empty word returns the accumulator unchanged. -/
def g : Unit → (List Bool → List Bool) := fun _ => id

/-- The step of the emergent algebra: PREPEND the leading bit `x` onto the accumulator, then hand off
    to the folded tail's continuation.  A single cons — O(1), NO append. -/
def st : Bool → (List Bool → List Bool) → (List Bool → List Bool) := fun x k => fun acc => k (x :: acc)

/-- Bit-reversal as an accumulator fold over the cons-list initial algebra `ConsList Unit Bool`:
    `wrap _ ↦ id`, `cons x xs ↦ st x (revAcc xs)`.  This is exactly Lean core's `List.reverseAux`
    reshaped onto the initial algebra — O(m) via O(1) prepend. -/
def revAcc : ConsList Unit Bool → (List Bool → List Bool)
  | ConsList.wrap _    => id
  | ConsList.cons x xs => st x (revAcc xs)

/-- The base condition is a COMPUTATION, not a guess: `revAcc (wrap d) = g d`. -/
theorem revAcc_wrap : ∀ d : Unit, revAcc (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `revAcc`'s cons equation: `revAcc (cons x xs) = st x (revAcc xs)`. -/
theorem revAcc_cons : ∀ (x : Bool) (xs : ConsList Unit Bool),
    revAcc (ConsList.cons x xs) = st x (revAcc xs) := fun _ _ => rfl

/-! ## Bit-reversal EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The O(m) accumulator reversal, RESHAPED onto the cons-list initial algebra
    `ConsList Unit Bool`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g st` — it
    was never written as a fold: `graph revAcc` equals `cataR (consScalarAlg g st)`.  The program (the
    O(1)-prepend fold) is PRODUCED by `consFold_unique`; `List.reverse` (LeetCode 190's answer) is
    recovered below by applying the continuation to the empty accumulator. -/
theorem revBits_emerges :
    (graph revAcc : dCL Unit Bool ⟶ ⟨List Bool → List Bool⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st revAcc revAcc_wrap revAcc_cons

/-! ## Bridge to the hand-written `List.reverse` program -/

/-- The `List Bool → ConsList Unit Bool` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Bool → ConsList Unit Bool
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The accumulator invariant: running the continuation on `acc` prepends the reversed word,
    `revAcc (ofList bs) acc = bs.reverse ++ acc`.  By induction on `bs`, the cons step being the O(1)
    prepend `revAcc (ofList xs) (x :: acc)` unfolded against `List.reverse_cons`/`List.append_assoc`. -/
theorem revAcc_ofList_append : ∀ (bs acc : List Bool),
    revAcc (ofList bs) acc = bs.reverse ++ acc
  | [],      acc => rfl
  | x :: xs, acc => by
      show revAcc (ofList xs) (x :: acc) = (x :: xs).reverse ++ acc
      rw [revAcc_ofList_append xs (x :: acc), List.reverse_cons]
      exact (List.append_assoc xs.reverse [x] acc).symm

/-- The reshaped fold, run on the empty accumulator, agrees with `LC190.revBits` (Lean core's
    `List.reverse`): `revAcc (ofList bs) [] = bs.reverse = LC190.revBits bs`, via the accumulator
    invariant at `acc = []` (`List.append_nil`) and the reused `LC190.solve_correct`. -/
theorem revBits_ofList (bs : List Bool) : revAcc (ofList bs) [] = LC190.revBits bs := by
  rw [revAcc_ofList_append bs [], List.append_nil, LC190.solve_correct]

/-! ## Correctness carries over from `L190.lean` (no re-proof) -/

/-- **Headline.**  The honest bundle: (1) the O(m) accumulator bit-reversal, reshaped onto the
    cons-list initial algebra, IS the catamorphism of `consScalarAlg g st` (`revBits_emerges`) — the
    step PREPENDS (O(1)), NOT `prev ++ [x]`; (2) the reshaped fold, applied to the empty accumulator,
    reproduces `LC190.revBits` — LeetCode 190's `List.reverse` program — the reused
    `LC190.solve_correct` carried across the bridge `revBits_ofList`; and (3) reversing bits twice is
    the identity, the structural-output extra law reused from `LC190.rev_rev`.  The program (the fold)
    is PRODUCED by the law; correctness is REUSED, not re-proved. -/
theorem revBits_derived_correct :
    ((graph revAcc : dCL Unit Bool ⟶ ⟨List Bool → List Bool⟩) = cataR (consScalarAlg g st))
      ∧ (∀ bs : List Bool, revAcc (ofList bs) [] = LC190.revBits bs)
      ∧ (∀ bs : List Bool, revAcc (ofList (revAcc (ofList bs) [])) [] = bs) := by
  refine ⟨revBits_emerges, revBits_ofList, fun bs => ?_⟩
  rw [revBits_ofList bs, revBits_ofList (LC190.revBits bs)]
  exact LC190.rev_rev bs

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the extensionally-equal computable witness
  `revAcc ∘ ofList` applied to the empty accumulator (equal to `revBits` by `revBits_ofList`, and to
  the catamorphism by `revBits_emerges`) on the LeetCode 190 examples. -/

example : revAcc (ofList [true, false, false, false]) [] = [false, false, false, true] := by decide
example : revAcc (ofList ([] : List Bool)) [] = [] := by decide
example : revAcc (ofList [true]) [] = [true] := by decide
-- Reversing bits twice is the identity (the structural-output extra law), on the reshaped fold:
example : revAcc (ofList (revAcc (ofList [true, false, true]) [])) [] = [true, false, true] := by decide

/-- The reshaped fold genuinely relates the converted input to the (function-valued) catamorphism it
    emerges as. -/
example :
    cataFold (consScalarAlg g st) (ofList [true, false, false, false])
      (revAcc (ofList [true, false, false, false])) := by
  have h : (graph revAcc : dCL Unit Bool ⟶ ⟨List Bool → List Bool⟩)
      (ofList [true, false, false, false]) (revAcc (ofList [true, false, false, false])) := rfl
  rw [revBits_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC190D
