/-
  LeetCode 213 — House Robber II — the LINEAR robber fold DERIVED as a cons-list catamorphism.

  `leet/L213.lean` solves the CIRCULAR problem by `imax (robLine dropLast) (robLine tail)` — two
  ordinary LINEAR house-robber passes over sub-rows of the ring — where the linear pass is the
  pair-DP fold

    * base   `foldL [] = (0, 0)`                                        -- (best, prevBest)
    * step   `foldL (x :: xs) = (imax (foldL xs).1 ((foldL xs).2 + x), (foldL xs).1)`

  over a RAW Lean `List Int`, and `robLine l = (foldL l).1`.  The fold SHAPE is already clean — a
  cons-wise `(best, prev)` pair-DP — but its input `List Int` is NOT the initial-algebra list, so
  `foldL` as written is not a catamorphism.  This file RESHAPES the data onto the repo's canonical
  cons-list initial algebra `ConsList Unit Int` (base at `wrap ()`, recursion on the tail — the
  `list Int` of the book) and makes the linear robber fold EMERGE as a catamorphism via the
  general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`).  The carrier
  is `C := Int × Int` — the `(best, prev)` DP pair — and the base/step are FORCED (both hold by
  `rfl`):

    * base   `g _ = LC213.foldL []`                    = `foldLCL (wrap _)`
    * step   `st x s = (imax s.1 (s.2 + x), s.1)`       = `foldLCL (cons x xs)` with `s = foldLCL xs`.

  Feeding `g`/`st`/`foldLCL` to `consFold_unique` PRODUCES the pair-DP as `cataR (consScalarAlg g
  st)` — the linear robber fold is the law's catamorphism, never written by hand.  The bridge
  `foldLCL_ofList` (`foldLCL (ofList l) = LC213.foldL l`) recovers the hand-written raw-list fold,
  so `robLine l = (foldLCL (ofList l)).1` (`robLine_via`): BOTH the `dropLast` and the `tail` pass
  factor through the emergent catamorphism.

  Only the DATA of the LINEAR fold is reshaped; the CIRCULAR gluing (`imax` of the two passes, the
  singleton special case) and its correctness (`LC213.circSpec`, `LC213.solve_correct`) are REUSED
  from `L213.lean`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L213

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC213D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list carrier and its `(best, prev)` pair-DP fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here `C = Int × Int`,
  the House-Robber `(best, prevBest)` DP state.  `foldLCL` mirrors `LC213.foldL` on the cons-list
  initial algebra `ConsList Unit Int`: `wrap _` is the empty input (`foldL [] = (0, 0)`), `cons x
  xs` peels the head house `x` and re-runs the pair-DP step. -/

/-- The linear robber pair-DP as a fold over the cons-list initial algebra, mirroring `LC213.foldL`:
    `wrap _ ↦ foldL []`, `cons x xs ↦ (imax (foldLCL xs).1 ((foldLCL xs).2 + x), (foldLCL xs).1)`. -/
def foldLCL : ConsList Unit Int → Int × Int
  | ConsList.wrap _    => LC213.foldL []
  | ConsList.cons x xs => (LC213.imax (foldLCL xs).1 ((foldLCL xs).2 + x), (foldLCL xs).1)

/-- The base of the emergent algebra: the empty-selection DP pair `foldL [] = (0, 0)`, ignoring the
    `Unit` leaf. -/
def g : Unit → Int × Int := fun _ => LC213.foldL []

/-- The step of the emergent algebra: peel the head house `x` and advance the `(best, prev)` pair by
    re-running the House-Robber transition `(imax best (prev + x), best)`. -/
def st : Int → Int × Int → Int × Int := fun x s => (LC213.imax s.1 (s.2 + x), s.1)

/-- The base condition is a COMPUTATION, not a guess: `foldLCL (wrap d) = g d`. -/
theorem foldLCL_wrap : ∀ d : Unit, foldLCL (ConsList.wrap d) = g d :=
  fun d => rfl

/-- The step condition IS `foldLCL`'s cons equation: `foldLCL (cons x xs) = st x (foldLCL xs)`. -/
theorem foldLCL_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), foldLCL (ConsList.cons x xs) = st x (foldLCL xs) :=
  fun x xs => rfl

/-! ## The linear robber fold EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The linear House-Robber pair-DP, RESHAPED onto the cons-list initial
    algebra `ConsList Unit Int`, IS the catamorphism of the emergent scalar algebra `consScalarAlg
    g st` — it was never written as a fold: `graph foldLCL` equals `cataR (consScalarAlg g st)`.
    The carrier `Int × Int` (the `(best, prev)` DP state) is the point: a cons-wise pair-DP is
    emitted by `consFold_unique`. -/
theorem robfold_emerges :
    (graph foldLCL : dCL Unit Int ⟶ ⟨Int × Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st foldLCL foldLCL_wrap foldLCL_cons

/-! ## Bridge to the hand-written raw-`List` linear fold -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The reshaped fold agrees with the raw-`List` fold on converted input: `foldLCL (ofList l) =
    LC213.foldL l`, by induction on `l` (both sides share the pair-DP step). -/
theorem foldLCL_ofList : ∀ l : List Int, foldLCL (ofList l) = LC213.foldL l
  | []      => rfl
  | x :: xs => by
      show (LC213.imax (foldLCL (ofList xs)).1 ((foldLCL (ofList xs)).2 + x), (foldLCL (ofList xs)).1)
             = (LC213.imax (LC213.foldL xs).1 ((LC213.foldL xs).2 + x), (LC213.foldL xs).1)
      rw [foldLCL_ofList xs]

/-- `robLine` — L213's linear answer, the first DP component — factors through the emergent
    catamorphism: `robLine l = (foldLCL (ofList l)).1`.  Applied at `l.dropLast` and `l.tail` this
    is exactly the two linear passes L213's `circAnswer` glues by `imax`. -/
theorem robLine_via (l : List Int) : LC213.robLine l = (foldLCL (ofList l)).1 := by
  show (LC213.foldL l).1 = (foldLCL (ofList l)).1
  rw [foldLCL_ofList l]

/-! ## Correctness carries over from `L213.lean` (no re-proof of the circular argument) -/

/-- **Headline.**  The honest bundle: (1) the linear robber pair-DP, reshaped onto the cons-list
    initial algebra, IS the catamorphism of `consScalarAlg g st` (`robfold_emerges`); (2) L213's
    linear answer `robLine` factors through that emergent catamorphism (`robLine_via`), so both
    ring-breaking passes are produced by the law; and (3) the full circular solution is correct —
    `solveFn xs` is an achievable circular robbery and dominates every achievable one — the REUSED
    `LC213.solve_correct`, whose `imax` gluing and singleton special case are NOT re-proved here. -/
theorem rob2_derived_correct :
    ((graph foldLCL : dCL Unit Int ⟶ ⟨Int × Int⟩) = cataR (consScalarAlg g st))
      ∧ (∀ l : List Int, LC213.robLine l = (foldLCL (ofList l)).1)
      ∧ (∀ xs : Freyd.Alg.RelSet.SL.SnocList Int Int,
           LC213.circSpec xs (LC213.solveFn xs) ∧ ∀ v, LC213.circSpec xs v → v ≤ LC213.solveFn xs) :=
  ⟨robfold_emerges, robLine_via, LC213.solve_correct⟩

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the extensionally-equal computable
  witnesses: the scalar circular answers `solveFn` (LeetCode 213 examples) and the emergent fold on
  converted input. -/

example : LC213.solveFn (LC213.ofList 2 [3, 2]) = 3 := by decide      -- [2,3,2] → 3
example : LC213.solveFn (LC213.ofList 1 [2, 3, 1]) = 4 := by decide   -- [1,2,3,1] → 4
example : LC213.solveFn (LC213.ofList 1 [2, 3]) = 3 := by decide      -- [1,2,3] → 3

-- The reshaped cons-list fold, on converted input, reproduces L213's linear row answer:
example : (foldLCL (ofList [2, 3, 2])).1 = LC213.robLine [2, 3, 2] := by decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g st) (ofList [1, 2, 3, 1]) (foldLCL (ofList [1, 2, 3, 1])) := by
  have h : (graph foldLCL : dCL Unit Int ⟶ ⟨Int × Int⟩)
      (ofList [1, 2, 3, 1]) (foldLCL (ofList [1, 2, 3, 1])) := rfl
  rw [robfold_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC213D
