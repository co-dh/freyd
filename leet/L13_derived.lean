/-
  LeetCode 13 — Roman to Integer — DERIVED as a cons-list catamorphism.

  `leet/L13.lean` WRITES `romanFn` as a two-element-LOOKAHEAD fold over a RAW Lean `List Int`:

    * base   `romanFn []            = 0`
    * base   `romanFn [x]           = x`
    * step   `romanFn (x :: y :: r) = (if x < y then -x else x) + romanFn (y :: r)`

  — at each symbol `x` it compares to the IMMEDIATE SUCCESSOR `y`, adding `x` normally but SUBTRACTING
  it when `x < y` (`IV = [1,5] ↦ 4`).  As written this is not a catamorphism for two reasons: its input
  `List Int` is not the repo's initial-algebra list, and — more essentially — the recurrence peeks at
  the NEXT element `y`, which a plain cons-fold `st : E → C → C` (head, then folded tail) cannot see.

  This file RESHAPES the data onto the canonical cons-list initial algebra `ConsList Unit Int`
  (`list Int` of the book, base at `wrap ()`, recursion on the tail) and DEFEATS the lookahead by
  choosing the carrier

    * `C := Int × Option Int` — `(value of the suffix, FIRST symbol of the suffix)` —

  so the folded tail already CARRIES the successor the step needs to look at.  The base/step are then
  ordinary and FORCED (both `rfl`):

    * base   `g _   = (0, none)`                             = `romanCL (wrap _)`
    * step   `st x (v, h) = ((match h | some y => if x<y then -x else x | none => x) + v, some x)`
                                                             = `romanCL (cons x xs)` with `(v,h)=romanCL xs`.

  Feeding `g`/`st`/`romanCL` to the general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique`
  (`AOP/A6_GenFold.lean`) PRODUCES the roman fold as `cataR (consScalarAlg g st)` — the two-element
  lookahead is emitted by the law, never written by hand.  The bridge `romanCL_ofList`
  (`romanCL (ofList xs) = (romanFn xs, xs.head?)`) recovers the hand-written raw-list fold, tracking
  the second component `xs.head?` as exactly the lookahead the carrier carries.

  Only the DATA is reshaped; the honest closed-form re-characterization
  `romanFn xs = xs.sum - 2 * subtractedPart xs` (`LC13.roman_correct`) and the `Map` `LC13.solve` are
  REUSED from `L13.lean`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L13

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC13D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list carrier and its lookahead-carrying fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here
  `C = Int × Option Int` — `(roman value of the suffix, first symbol of the suffix)`.  Carrying the
  head symbol in the SECOND component is what lets an ordinary cons-fold reproduce `romanFn`'s peek at
  the next symbol: when `cons x` sees the folded tail `(v, h)`, `h` IS the successor `y`. -/

/-- The base of the emergent algebra: the empty suffix has value `0` and no first symbol. -/
def g : Unit → Int × Option Int := fun _ => (0, none)

/-- The step of the emergent algebra: prepend symbol `x` to the folded tail `(v, h)`.  If the tail has
    a first symbol `y = h`, add `x` normally or `-x` when `x < y`; otherwise `x` is the last symbol and
    contributes `+x`.  The new first symbol is `x`. -/
def st : Int → Int × Option Int → Int × Option Int :=
  fun x p => ((match p.2 with | some y => if x < y then -x else x | none => x) + p.1, some x)

/-- The roman fold as a fold over the cons-list initial algebra, mirroring `LC13.romanFn`:
    `wrap _ ↦ (0, none)`, `cons x xs ↦ st x (romanCL xs)`. -/
def romanCL : ConsList Unit Int → Int × Option Int
  | ConsList.wrap _    => (0, none)
  | ConsList.cons x xs => st x (romanCL xs)

/-- The base condition is a COMPUTATION, not a guess: `romanCL (wrap d) = g d`. -/
theorem romanCL_wrap : ∀ d : Unit, romanCL (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `romanCL`'s cons equation: `romanCL (cons x xs) = st x (romanCL xs)`. -/
theorem romanCL_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), romanCL (ConsList.cons x xs) = st x (romanCL xs) :=
  fun _ _ => rfl

/-! ## The roman fold EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The roman fold, RESHAPED onto the cons-list initial algebra `ConsList Unit
    Int`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g st` — it was never
    written as a fold: `graph romanCL` equals `cataR (consScalarAlg g st)`.  Carrying the successor
    symbol in the carrier `Int × Option Int` is the point: a two-element-lookahead scan is emitted by
    `consFold_unique`. -/
theorem roman_emerges :
    (graph romanCL : dCL Unit Int ⟶ ⟨Int × Option Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st romanCL romanCL_wrap romanCL_cons

/-! ## Bridge to the hand-written raw-`List` solution -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The reshaped fold agrees with the raw-`List` fold on converted input, tracking the second
    component as the lookahead symbol: `romanCL (ofList xs) = (romanFn xs, xs.head?)`, by the same
    two-element induction as `romanFn`.  The FIRST component is the roman value; the SECOND is the
    first symbol `xs.head?`, exactly the successor the carrier carries. -/
theorem romanCL_ofList : ∀ xs : List Int, romanCL (ofList xs) = (LC13.romanFn xs, xs.head?)
  | []          => rfl
  | [x]         => by
      show ((x : Int) + 0, some x) = (x, some x)
      rw [Int.add_zero]
  | x :: y :: r => by
      show st x (romanCL (ofList (y :: r))) = (LC13.romanFn (x :: y :: r), (x :: y :: r).head?)
      rw [romanCL_ofList (y :: r)]
      rfl

/-- The reshaped catamorphism's first component computes exactly `romanFn`. -/
theorem roman_via (xs : List Int) : LC13.romanFn xs = (romanCL (ofList xs)).1 :=
  (congrArg Prod.fst (romanCL_ofList xs)).symm

/-! ## Correctness carries over from `L13.lean` (no re-proof of the closed form) -/

/-- **Headline.**  The honest bundle:

    (1) the roman fold, reshaped onto the cons-list initial algebra, IS the catamorphism of
        `consScalarAlg g st` — the two-element-lookahead scan EMERGES from `consFold_unique`
        (`roman_emerges`);
    (2) the `Map` `LC13.solve` (LeetCode 13's answer relation) relates each input to exactly the FIRST
        component of that emergent catamorphism on the converted input (`roman_via`); and
    (3) that value equals the honest closed-form re-characterization `sum − 2·subtractedPart` — the
        REUSED `LC13.roman_correct`, not re-proved here.

    The program (the fold) is PRODUCED by the law; the closed-form correctness is reused. -/
theorem roman_derived_correct :
    ((graph romanCL : dCL Unit Int ⟶ ⟨Int × Option Int⟩) = cataR (consScalarAlg g st))
      ∧ (∀ (xs : List Int) (v : Int), LC13.solve xs v ↔ v = (romanCL (ofList xs)).1)
      ∧ (∀ xs : List Int, (romanCL (ofList xs)).1 = xs.sum - 2 * LC13.subtractedPart xs) := by
  refine ⟨roman_emerges, ?_, ?_⟩
  · intro xs v
    show (v = LC13.romanFn xs) ↔ v = (romanCL (ofList xs)).1
    rw [roman_via xs]
  · intro xs
    rw [← roman_via xs]
    exact LC13.roman_correct xs

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the computable scalar answers `romanFn`
  (LeetCode 13 examples) and the extensionally-equal computable witness `(romanCL ∘ ofList).1`. -/

/-- `III = [1,1,1] → 3`. -/
example : LC13.romanFn [1, 1, 1] = 3 := by decide
/-- `IV = [1,5] → 4` (subtractive). -/
example : LC13.romanFn [1, 5] = 4 := by decide
/-- `MCMXCIV = [1000,100,1000,10,100,1,5] → 1994`. -/
example : LC13.romanFn [1000, 100, 1000, 10, 100, 1, 5] = 1994 := by decide

-- The reshaped cons-list fold, on converted input, reproduces the scalar answers:
example : (romanCL (ofList [1, 1, 1])).1 = 3 := by decide
example : (romanCL (ofList [1, 5])).1 = 4 := by decide
example : (romanCL (ofList [1000, 100, 1000, 10, 100, 1, 5])).1 = 1994 := by decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g st) (ofList [1, 5]) (romanCL (ofList [1, 5])) := by
  have h : (graph romanCL : dCL Unit Int ⟶ ⟨Int × Option Int⟩)
      (ofList [1, 5]) (romanCL (ofList [1, 5])) := rfl
  rw [roman_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC13D
