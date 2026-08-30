/-
  LeetCode 5 — Longest Palindromic Substring — DERIVED as a cons-list catamorphism.

  `leet/L5.lean` writes `bestFrom : List Int → List Int → Nat` as a two-pointer recursion on
  `right` (structural recursion, decreasing on `right`) carrying `left`, the REVERSED
  already-consumed prefix, as an accumulator; `longestPalinFn s := bestFrom [] s`.  This file
  RESHAPES `right` onto the canonical cons-list initial algebra `ConsList Unit Int` (`Freyd.Alg.
  RelSet.CL.ofList`, `AOP/A6_ConsList.lean`) and shows `bestFrom`/`commonPrefixLen` together
  EMERGE as the catamorphism of an ordinary `[g, st]`-algebra over the general-carrier cons-fold law
  `CL.consFold_unique` (`AOP/A6_GenFold.lean`) — the two-pointer scan was never written as a fold,
  it is PRODUCED by the law.

  **The carrier.**  A plain cons-fold `st : E → C → C` recurses on the tail FIRST, so its step only
  ever sees the head element and the ALREADY-FOLDED tail value — it has no access to the raw,
  un-consed tail list.  `bestFrom left (x :: rest)`'s step, however, needs `commonPrefixLen left
  rest` (the ODD-center radius) and `commonPrefixLen left (x :: rest)` (the EVEN-center radius) —
  quantities indexed by `rest` itself, not recoverable from a single `Nat` answer.  The fix is the
  assigned ACCUMULATOR/CPS carrier `C := List Int → Nat` — "the reversed prefix accumulator awaits
  it" — used TWICE, tupled into ONE function `C := List Int → Nat × Nat` returning
  `(commonPrefixLen left rest, bestFrom left rest)` for the awaited `left`.  The first component
  alone recurses cleanly in `x` and the FOLDED first component (`commonPrefixLen left (x :: rest) =`
  case on `left`'s head against `x`, using only `commonPrefixLen (left.tail) rest`, i.e. the folded
  `.1` evaluated at a different point — no raw `rest` needed); the second component then reads off
  both the folded `.1` (at `left`, for the odd radius) and the just-computed `.1` above (for the
  even radius) plus the folded `.2` (at `x :: left`, continuing the walk) — so the WHOLE step is a
  function of `x` and the folded carrier value alone, exactly `consFold_unique`'s shape.

  **Complexity — O(n²), inherent to center expansion.**  Each of the `n` cons-fold steps builds a
  carrier value `List Int → Nat × Nat`; evaluating it at a growing `left` walks `commonPrefixLen`,
  itself O(n) in the worst case (radius up to n/2), so the total work across all centers is O(n²) —
  the SAME asymptotic as `L5.lean`'s hand-written `bestFrom` (this file re-derives its exact
  recursion, not a faster one).  `left` is built by `x :: left` (O(1) cons), never `left ++ [x]`.

  **Correctness — headline shape 2 (extremum), reused.**  `L5.lean` proves BOTH achievability
  (`longestPalin_achievable`) and domination (`longestPalin_dominates`) of `longestPalinFn` against
  `IsPalinSubstr`; per the standing rule, the honest headline is the MORPHISM EQUATION
  `derivedSolve = Λ IsPalinSubstr ≫ est (≤)` via `RelSet.eq_Λ_comp_est`
  (`AOP/A7_4_Horner.lean`), consuming those two reused halves plus antisymmetry of `≤` — no
  optimality is re-proved here.

  Mathlib-free (Lean core + `Freyd.*` only); headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L5
import AOP.A7_4_Horner

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC5D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The CPS carrier: `List Int → Nat × Nat`, the awaited `left` mapped to
    `(commonPrefixLen left rest, bestFrom left rest)` -/

/-- The continuation carrier: given the reversed-prefix accumulator `left` still to arrive, the
    pair `(commonPrefixLen left rest, bestFrom left rest)` for the tail `rest` folded so far. -/
abbrev Carrier : Type := List Int → Nat × Nat

/-- The base of the emergent algebra: the empty suffix yields `(0, 0)` for every `left`, mirroring
    `commonPrefixLen left [] = 0` / `bestFrom left [] = 0`. -/
def g : Unit → Carrier := fun _ _ => (0, 0)

/-- The step of the emergent algebra: prepend `x` to the folded-tail continuation `k`.  Given the
    awaited `left`, the new prefix-match radius `cpl` is read off `left`'s head against `x` and the
    folded `.1` at the STRIPPED head (`k ys`, no raw tail needed); the new best-so-far combines the
    odd-center radius (folded `.1` at `left`), the even-center radius (`cpl` just computed), and the
    walk continued one element further (folded `.2` at `x :: left`) — exactly `bestFrom`'s own
    `nmax`/`nmax` combination. -/
def st (x : Int) (k : Carrier) : Carrier :=
  fun left =>
    let cpl : Nat := match left with
      | y :: ys => if y = x then (k ys).1 + 1 else 0
      | [] => 0
    (cpl, LC5.nmax (LC5.nmax (2 * (k left).1 + 1) (2 * cpl)) (k (x :: left)).2)

/-- The fold mirroring `commonPrefixLen`/`bestFrom` together, over the cons-list initial algebra. -/
def foldCL : ConsList Unit Int → Carrier
  | ConsList.wrap _ => fun _ => (0, 0)
  | ConsList.cons x xs => st x (foldCL xs)

/-- The base condition is a COMPUTATION: `foldCL (wrap d) = g d`. -/
theorem foldCL_wrap : ∀ d : Unit, foldCL (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `foldCL`'s cons equation. -/
theorem foldCL_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), foldCL (ConsList.cons x xs) = st x (foldCL xs) :=
  fun _ _ => rfl

/-! ## `foldCL` EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The reshaped `(commonPrefixLen, bestFrom)` fold IS the catamorphism of the
    emergent scalar algebra `consScalarAlg g st` — the two-pointer center-expansion scan is EMITTED
    by `consFold_unique`, never written by hand. -/
theorem palin_emerges :
    (graph foldCL : dCL Unit Int ⟶ ⟨Carrier⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st foldCL foldCL_wrap foldCL_cons

/-! ## Bridge to `L5.lean`'s `commonPrefixLen`/`bestFrom` -/

/-- `commonPrefixLen left [] = 0` for EVERY `left` (needed as a lemma, not `rfl`, since
    `commonPrefixLen`'s first pattern scrutinizes both arguments). -/
theorem commonPrefixLen_nil_right (left : List Int) : LC5.commonPrefixLen left [] = 0 := by
  cases left <;> rfl

/-- **The reshaped fold agrees with the raw-`List` recursion**, for every `left`: folding
    `ofList xs` computes exactly `(commonPrefixLen left xs, bestFrom left xs)`.  Proved by induction
    on `xs`, reusing `commonPrefixLen`/`bestFrom`'s own defining equations.  `dsimp only` after each
    `cases`/`rw` is needed to force reduction of the `match`/projection terms the rewrite leaves
    behind — `rw`'s own trailing closer does not unfold them, though they ARE definitionally equal
    (a plain `rfl` after the `dsimp` closes every branch). -/
theorem foldCL_ofList : ∀ (xs left : List Int),
    foldCL (ofList xs) left = (LC5.commonPrefixLen left xs, LC5.bestFrom left xs)
  | [], left => by
      show (0, 0) = (LC5.commonPrefixLen left [], LC5.bestFrom left [])
      rw [commonPrefixLen_nil_right left]; rfl
  | x :: xs, left => by
      have ih : ∀ z, foldCL (ofList xs) z = (LC5.commonPrefixLen z xs, LC5.bestFrom z xs) :=
        foldCL_ofList xs
      cases left with
      | nil =>
          show st x (foldCL (ofList xs)) []
            = (LC5.commonPrefixLen [] (x :: xs), LC5.bestFrom [] (x :: xs))
          dsimp only [st]
          rw [ih [], ih [x]]
          dsimp only; rfl
      | cons y ys =>
          show st x (foldCL (ofList xs)) (y :: ys)
            = (LC5.commonPrefixLen (y :: ys) (x :: xs), LC5.bestFrom (y :: ys) (x :: xs))
          dsimp only [st]
          rw [ih (y :: ys), ih ys, ih (x :: y :: ys)]
          dsimp only; rfl

/-! ## The efficient program and correctness -/

/-- **The program**: run the reshaped fold at the empty accumulator. -/
def derivedSolve (s : List Int) : Nat := (foldCL (ofList s) []).2

/-- The reshaped program computes exactly `LC5.longestPalinFn`. -/
theorem derivedSolve_eq (s : List Int) : derivedSolve s = LC5.longestPalinFn s := by
  show (foldCL (ofList s) []).2 = LC5.bestFrom [] s
  rw [foldCL_ofList s []]

/-- **Headline (shape 2, extremum), as a MORPHISM EQUATION.**  `derivedSolve` equals `max (≤) ·
    Λ IsPalinSubstr` — the program IS the `≤`-maximum of the palindromic-substring-length
    specification.  Consumes `L5.lean`'s reused achievability (`longestPalin_achievable`) and
    domination (`longestPalin_dominates`) through `derivedSolve_eq`; no optimality is re-proved. -/
theorem palin_derived_correct :
    (graph derivedSolve : LC5.Arr ⟶ LC5.dNat) = Λ LC5.IsPalinSubstr ≫ est (fun w z : Nat => z ≤ w) :=
  eq_Λ_comp_est (fun w z : Nat => z ≤ w) (fun _ _ hxy hyx => Nat.le_antisymm hyx hxy)
    derivedSolve LC5.IsPalinSubstr
    (fun s => by rw [derivedSolve_eq s]; exact (LC5.longest_palin_correct s).1)
    (fun s v hv => by rw [derivedSolve_eq s]; exact (LC5.longest_palin_correct s).2 v hv)

/-! ## Running the reshaped fold -/

example : derivedSolve [98, 97, 98, 97, 100] = 3 := by rw [derivedSolve_eq]; decide -- "babad"→"bab"
example : derivedSolve [99, 98, 98, 100] = 2 := by rw [derivedSolve_eq]; decide      -- "cbbd"→"bb"
example : derivedSolve ([] : List Int) = 0 := by rw [derivedSolve_eq]; decide

end Freyd.Alg.RelSet.LC5D
