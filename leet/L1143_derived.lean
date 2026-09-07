/-
  LeetCode 1143 — Longest Common Subsequence — DERIVED as a cons-list catamorphism.

  `leet/L1143.lean` WRITES the 2-D DP as a front-to-back structural fold `col ys` over a RAW Lean
  `List Int`:

    * base   `col ys [] = List.replicate (ys.length + 1) 0`
    * step   `col ys (x :: xs) = rowStep x ys (col ys xs)`

  and `solveFn xs ys = (col ys xs).headD 0`, bridged to the spec by `LC1143.solve_correct`.  The
  fold SHAPE is already clean — one DP row per leading character of `xs`, the row `List Nat` indexed
  by suffixes of the fixed `ys` — but its input `List Int` is NOT the initial-algebra list, so `col`
  as written is not a catamorphism.  This file RESHAPES the data onto the repo's canonical cons-list
  initial algebra `ConsList Unit Int` (base at `wrap ()`, recursion on the tail — `list Int` of the
  book) and makes the fold EMERGE as a catamorphism via the general-carrier law
  `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`).

  Only the DATA is reshaped; `ys` stays a FIXED parameter (the fold is over `xs`, the row indexed by
  `ys`) and `rowStep`/`lcs`/`solve_correct` are REUSED from `LC1143`, not re-proved.  The carrier is
  `C := List Nat` — the growing DP row — and the base/step are FORCED (both hold by `rfl`):

    * base   `g _ = List.replicate (ys.length + 1) 0`         = `colCL ys (wrap _)`
    * step   `st x prev = rowStep x ys prev`                  = `colCL ys (cons x xs)` with
             `prev = colCL ys xs`.

  Feeding `g`/`st`/`colCL ys` to `consFold_unique` PRODUCES the DP column as
  `cataR (consScalarAlg g st)` — the fold is the law's catamorphism, never written by hand.  The
  bridge `colCL_ofList` (`colCL ys (ofList xs) = col ys xs`) then recovers the hand-written raw-list
  solution, so `(colCL ys (ofList xs)).headD 0 = solveFn xs ys = lcs xs ys` via `solve_correct`.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L1143

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC1143D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list carrier and its DP-column fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here `C = List Nat`,
  the DP ROW (one entry per suffix of the fixed `ys`).  `colCL ys` mirrors `LC1143.col ys` on the
  cons-list initial algebra `ConsList Unit Int`: `wrap _` is the empty input (the all-`0` base row),
  `cons x xs` prepends the leading character `x` and re-runs `rowStep`.  `ys` is a fixed parameter. -/

/-- The DP column as a fold over the cons-list initial algebra, mirroring `LC1143.col ys`:
    `wrap _ ↦ all-0 row`, `cons x xs ↦ rowStep x ys (colCL ys xs)`. -/
def colCL (ys : List Int) : ConsList Unit Int → List Nat
  | ConsList.wrap _      => List.replicate (ys.length + 1) 0
  | ConsList.cons x xs   => LC1143.rowStep x ys (colCL ys xs)

/-- The base of the emergent algebra: the all-`0` DP row (`lcs [] _ = 0` everywhere), ignoring the
    `Unit` leaf. -/
def g (ys : List Int) : Unit → List Nat := fun _ => List.replicate (ys.length + 1) 0

/-- The step of the emergent algebra: prepend the leading character `x` to the folded tail row
    `prev` by re-running the DP row-transition `rowStep x ys prev`. -/
def st (ys : List Int) : Int → List Nat → List Nat := fun x prev => LC1143.rowStep x ys prev

/-- The base condition is a COMPUTATION, not a guess: `colCL ys (wrap d) = g ys d`. -/
theorem colCL_wrap (ys : List Int) : ∀ d : Unit, colCL ys (ConsList.wrap d) = g ys d :=
  fun d => rfl

/-- The step condition IS `colCL`'s cons equation: `colCL ys (cons x xs) = st ys x (colCL ys xs)`. -/
theorem colCL_cons (ys : List Int) :
    ∀ (x : Int) (xs : ConsList Unit Int), colCL ys (ConsList.cons x xs) = st ys x (colCL ys xs) :=
  fun x xs => rfl

/-! ## The DP column EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The DP column, RESHAPED onto the cons-list initial algebra `ConsList Unit
    Int`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g st` — it was never
    written as a fold: `graph (colCL ys)` equals `cataR (consScalarAlg (g ys) (st ys))`.  The
    carrier `List Nat` (the growing DP row) is the point: a front-to-back single-list DP is emitted
    by `consFold_unique`. -/
theorem col_emerges (ys : List Int) :
    (graph (colCL ys) : dCL Unit Int ⟶ ⟨List Nat⟩) = cataR (consScalarAlg (g ys) (st ys)) :=
  consFold_unique (g ys) (st ys) (colCL ys) (colCL_wrap ys) (colCL_cons ys)

/-! ## Bridge to the hand-written raw-`List` solution -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- The reshaped fold agrees with the raw-`List` fold on converted input: `colCL ys (ofList xs) =
    LC1143.col ys xs`, by induction on `xs` (both sides share `rowStep`). -/
theorem colCL_ofList (ys : List Int) : ∀ xs : List Int, colCL ys (ofList xs) = LC1143.col ys xs
  | []      => rfl
  | x :: xs => by
      show LC1143.rowStep x ys (colCL ys (ofList xs)) = LC1143.rowStep x ys (LC1143.col ys xs)
      rw [colCL_ofList ys xs]

/-! ## Correctness carries over from `L1143.lean` (no re-proof of the DP argument) -/

/-- **Headline.**  The honest bundle: (1) the DP column, reshaped onto the cons-list initial algebra,
    IS the catamorphism of `consScalarAlg g st` (`col_emerges`); and (2) reading position `0` off
    that reshaped-then-converted column computes exactly `lcs` — the reused correctness
    `LC1143.solve_correct` carried across the bridge `colCL_ofList`.  The DP argument is REUSED, not
    re-proved. -/
theorem lcs_derived_correct (ys : List Int) :
    ((graph (colCL ys) : dCL Unit Int ⟶ ⟨List Nat⟩) = cataR (consScalarAlg (g ys) (st ys)))
      ∧ (∀ xs : List Int, (colCL ys (ofList xs)).headD 0 = LC1143.lcs xs ys) := by
  refine ⟨col_emerges ys, fun xs => ?_⟩
  rw [colCL_ofList ys xs]
  exact LC1143.solve_correct xs ys

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the extensionally-equal computable witness
  `colCL ys ∘ ofList` (equal to the raw `col` by `colCL_ofList`, and to the catamorphism by
  `col_emerges`), and the scalar answers `lcs` (LeetCode 1143 examples). -/

example : LC1143.lcs [1, 2, 3] [1, 3] = 2 := by decide
example : LC1143.lcs [1, 2, 3, 4, 5] [1, 3, 5] = 3 := by decide
example : LC1143.lcs [1, 2] [3, 4] = 0 := by decide

-- The reshaped cons-list fold, on converted input, reproduces the scalar answers:
example : (colCL [1, 3] (ofList [1, 2, 3])).headD 0 = 2 := by decide
example : (colCL [1, 3, 5] (ofList [1, 2, 3, 4, 5])).headD 0 = 3 := by decide
example : (colCL [3, 4] (ofList [1, 2])).headD 0 = 0 := by decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg (g [1, 3]) (st [1, 3])) (ofList [1, 2, 3])
      (colCL [1, 3] (ofList [1, 2, 3])) := by
  have h : (graph (colCL [1, 3]) : dCL Unit Int ⟶ ⟨List Nat⟩)
      (ofList [1, 2, 3]) (colCL [1, 3] (ofList [1, 2, 3])) := rfl
  rw [col_emerges [1, 3]] at h
  exact h

end Freyd.Alg.RelSet.LC1143D
