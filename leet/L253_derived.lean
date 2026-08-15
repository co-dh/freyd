/-
  LeetCode 253 — Meeting Rooms II — DERIVED as a `Nat` max-fold catamorphism.

  `leet/L253.lean` computes `roomsFn ivs := (ivs.map (fun iv => countCover ivs iv.1)).foldr nmax 0`
  by hand: a plain `List.map` + `List.foldr` composite.  This file RESHAPES the same computation onto
  the canonical cons-list initial algebra `ConsList Unit (Int × Int)` (`Freyd.Alg.RelSet.CL.ofList`)
  and shows the fold EMERGES from the general-carrier law `CL.consFold_unique` — the same recipe as
  `leet/L1.lean`'s hash scan, with carrier `C := Nat`.

  The key point, exactly as in `leet/L1.lean` (where `target` is fixed for the whole scan): the step
  needs `countCover ivs iv.1` — "how many meetings cover THIS meeting's own start" — which reads the
  WHOLE interval list `ivs`, not just the folded-so-far prefix.  So `ivs` is carried as a FIXED
  parameter of the base/step (never threaded through the recursion), exactly like `leet/L1.lean`'s
  `target`; `countCover` itself is `List.filter |>.length`, i.e. already a fold of its own (a
  `foldr`-over-`Bool`-test count) — reused verbatim from `L253.lean`, not re-derived, since
  `consFold_unique` only asks for `countCover`'s VALUE at each step, not its internal recursion.

  1. **The program EMERGES.**  Base `g ivs _ = 0` (empty suffix contributes nothing to the max); step
     `st ivs iv acc = nmax (countCover ivs iv.1) acc` (`nmax` the current interval's OWN coverage
     count against the folded tail's max).  Feeding these to `CL.consFold_unique` produces the fold as
     `cataR (consScalarAlg (g ivs) (st ivs))` — `rooms_emerges` — never hand-written.

  2. **Bridge.**  `foldCL_ofList` shows the reshaped fold agrees with `LC253.roomsFn`'s `map`+`foldr`
     composite on ANY converted list, by structural induction; instantiating at `xs := ivs` (the fold
     runs over the SAME list it reads as a fixed parameter) gives `derivedSolve_eq : derivedSolve ivs =
     LC253.roomsFn ivs`.

  3. **Correctness is REUSED**, not re-proved: `LC253.rooms_correct` (achievability `rooms_achievable`
     + domination `rooms_dominates`) is already the honest S0 extremum pair, so the headline is stated
     as the actual morphism equation `RelSet.eq_A_comp_maxRel` (`AOP/A7_4_Horner.lean`) —
     `derivedSolve = A spec ≫ maxRel D` for the `≤`-preference order `D w z := z ≤ w`, `spec ivs v :=
     ∃ t, countCover ivs t = v` — instead of only a pointwise restatement.

  4. **Complexity.**  This is the SAME `O(n²)` algorithm as `L253.lean` (`n` = `ivs.length`): the fold
     visits each of the `n` interval-starts once, and each step's `countCover ivs iv.1` filters the
     WHOLE `n`-length list — `n` steps × `O(n)` per step.  The event-sort sweep (sort `2n` start/end
     events, scan with a running counter, `O(n log n)`) is a DIFFERENT algorithm — no sort, no event
     list, no running counter here — and is out of scope for this derivation.

  Mathlib-free (Lean core + `Freyd.*` only); headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A7_4_Horner
import leet.L253

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC253D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The `Nat` max-fold, `ivs` fixed for the whole recursion (as `leet/L1.lean`'s `target`) -/

/-- Base of the emergent algebra, parameterized by the fixed whole list `ivs`: the empty suffix
    contributes `0` to the max. -/
def g (ivs : List (Int × Int)) : Unit → Nat := fun _ => 0

/-- Step of the emergent algebra: `nmax` the current interval's OWN coverage count — against the
    FIXED whole list `ivs`, never the folded-so-far prefix — with the folded tail's max. -/
def st (ivs : List (Int × Int)) : (Int × Int) → Nat → Nat :=
  fun iv acc => LC253.nmax (LC253.countCover ivs iv.1) acc

/-- The max-fold, structural recursion on `ConsList Unit (Int × Int)`, mirroring `LC253.roomsFn`'s
    `map`+`foldr nmax 0` shape one interval at a time. -/
def foldCL (ivs : List (Int × Int)) : ConsList Unit (Int × Int) → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons e xs => LC253.nmax (LC253.countCover ivs e.1) (foldCL ivs xs)

/-- The base condition is a COMPUTATION: `foldCL ivs (wrap d) = g ivs d`. -/
theorem foldCL_wrap (ivs : List (Int × Int)) : ∀ d : Unit, foldCL ivs (ConsList.wrap d) = g ivs d :=
  fun _ => rfl

/-- The step condition IS `foldCL`'s cons equation: `foldCL ivs (cons e xs) = st ivs e (…)`. -/
theorem foldCL_cons (ivs : List (Int × Int)) :
    ∀ (e : Int × Int) (xs : ConsList Unit (Int × Int)),
      foldCL ivs (ConsList.cons e xs) = st ivs e (foldCL ivs xs) :=
  fun _ _ => rfl

/-! ## The max-fold EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  For each fixed `ivs`, the reshaped max-fold IS the catamorphism of the
    emergent scalar algebra `consScalarAlg (g ivs) (st ivs)` — it was never written as a fold. -/
theorem rooms_emerges (ivs : List (Int × Int)) :
    (graph (foldCL ivs) : dCL Unit (Int × Int) ⟶ ⟨Nat⟩) = cataR (consScalarAlg (g ivs) (st ivs)) :=
  consFold_unique (g ivs) (st ivs) (foldCL ivs) (foldCL_wrap ivs) (foldCL_cons ivs)

/-! ## Bridge to the hand-written `LC253.roomsFn` -/

/-- The reshaped fold agrees with `LC253.roomsFn`'s `map`+`foldr nmax 0` composite on ANY converted
    list `xs` (not just `ivs` itself) — `ivs` stays fixed as the coverage-counting parameter while
    `xs` is the list actually being folded. -/
theorem foldCL_ofList (ivs : List (Int × Int)) :
    ∀ xs : List (Int × Int),
      foldCL ivs (ofList xs) = (xs.map (fun iv => LC253.countCover ivs iv.1)).foldr LC253.nmax 0
  | [] => rfl
  | e :: xs => by
      show LC253.nmax (LC253.countCover ivs e.1) (foldCL ivs (ofList xs)) = _
      rw [foldCL_ofList ivs xs]
      rfl

/-- **The efficient program**: run the reshaped fold over the interval list itself, using it also as
    the fixed coverage-counting parameter. -/
def derivedSolve (ivs : List (Int × Int)) : Nat := foldCL ivs (ofList ivs)

/-- The reshaped fold computes exactly `LC253.roomsFn`. -/
theorem derivedSolve_eq (ivs : List (Int × Int)) : derivedSolve ivs = LC253.roomsFn ivs :=
  foldCL_ofList ivs ivs

/-! ## Correctness — REUSED from `LC253.rooms_correct`, as the morphism-equation headline -/

/-- The spec relation: `v` is achievable as the coverage count at SOME instant (`LC253.rooms_correct`'s
    achievability half, read as a relation). -/
def spec : LC253.Ivs ⟶ LC253.dNat := fun ivs v => ∃ t : Int, LC253.countCover ivs t = v

/-- `derivedSolve` always produces a `spec`-achievable value — reused from `LC253.rooms_achievable`
    through `derivedSolve_eq`. -/
theorem derivedSolve_sound (ivs : List (Int × Int)) : spec ivs (derivedSolve ivs) := by
  show ∃ t : Int, LC253.countCover ivs t = derivedSolve ivs
  rw [derivedSolve_eq]
  exact LC253.rooms_achievable ivs

/-- `derivedSolve` dominates every `spec`-achievable value — reused from `LC253.rooms_dominates`
    through `derivedSolve_eq`. -/
theorem derivedSolve_dominates (ivs : List (Int × Int)) (v : Nat) (hv : spec ivs v) :
    v ≤ derivedSolve ivs := by
  obtain ⟨t, ht⟩ := hv
  rw [derivedSolve_eq]
  exact ht ▸ LC253.rooms_dominates ivs t

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `derivedSolve` is exactly the morphism
    `A spec ≫ maxRel D` for the `≤`-preference order `D w z := z ≤ w` — not merely pointwise.
    Bundles the emerged fold (`rooms_emerges`) with the reused extremum correctness. -/
theorem rooms_derived_eq_maxRel :
    (graph derivedSolve : LC253.Ivs ⟶ LC253.dNat) = Λ spec ≫ maxRel (fun w z : Nat => z ≤ w) :=
  eq_Λ_comp_maxRel _ (fun x y h1 h2 => Nat.le_antisymm h2 h1) derivedSolve spec
    derivedSolve_sound derivedSolve_dominates

/-! ## Running the program -/

-- LeetCode 253's own example: `[[0,30],[5,10],[15,20]] → 2`.
example : derivedSolve [(0, 30), (5, 10), (15, 20)] = 2 := by decide
-- Pairwise non-overlapping (touching allowed): `[[7,10],[2,4]] → 1`.
example : derivedSolve [(7, 10), (2, 4)] = 1 := by decide

end Freyd.Alg.RelSet.LC253D
