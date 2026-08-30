/-
  LeetCode 435 — Non-overlapping Intervals — DERIVED as TWO cons-list catamorphisms.

  `leet/L435.lean` writes `solveFn ivs = ivs.length - (keptSorted (isortH ivs)).length` as two
  hand-written recursions over a RAW Lean `List (Int × Int)`:

    * `isortH`     — insertion sort by `.2` (end time): `isortH [] = []`,
                     `isortH (iv :: rest) = linsertH iv (isortH rest)`;
    * `keptList`   — the greedy left-to-right scan over the SORTED list, threading a running
                     threshold `lastEnd` FORWARD through the recursive call: `keptList lastEnd []
                     = []`, `keptList lastEnd (iv :: rest) = if lastEnd ≤ iv.1 then iv ::
                     keptList iv.2 rest else keptList lastEnd rest`.

  This file RESHAPES both onto the canonical cons-list initial algebra `ConsList Unit (Int×Int)`
  (`Freyd.Alg.RelSet.CL.ofList`) and shows each EMERGES from the general-carrier law
  `CL.consFold_unique` (`AOP/A6_GenFold.lean`) — the recursions were never hand-written as folds.

  1. **`isortH` — a plain `List (Int×Int)` carrier.**  Already exactly the cons-fold shape (no
     lookahead needed, unlike `L26`'s dedup): base `gSort _ = []`, step `stSort iv acc = linsertH
     iv acc`.  `foldSort` obeys `foldSort (wrap _) = gSort ()`, `foldSort (cons iv xs) = stSort iv
     (foldSort xs)` by construction (both `rfl`), so `sort_emerges` reads it straight off
     `consFold_unique`.  Insertion sort is inherently `O(n²)` (as `L56`/`L252`'s `isort`) — that
     cost is unchanged here, not re-derived away.

  2. **`keptList` — the CPS/threshold-scan trick (as `L252_derived`'s `noAdjFromC`), carrier `C :=
     Int → List (Int×Int)`.**  `keptList`'s own recursion THREADS the threshold `lastEnd` forward,
     which a plain cons-fold `st : E → C → C` cannot see directly (the next call's threshold isn't
     the folded tail's own value, it depends on the NEWLY kept head).  Curry the threshold to the
     other side: fold the list FIRST into a RESIDUAL `foldKept l : Int → List (Int×Int)` that still
     AWAITS the threshold `lastEnd` — for every threshold `t`, `foldKept l t` IS `keptList t l`
     (hence "carrier `(lastEnd, keptList)`": the residual's argument/result pair is exactly that).
     Base `gKept _ = fun _ => []` (an empty suffix keeps nothing at any threshold); step `stKept iv
     frest := fun lastEnd => if lastEnd ≤ iv.1 then iv :: frest iv.2 else frest lastEnd` — read
     straight off `keptList`'s own cons clause, curried in the awaited threshold, with the
     recursive call's ADVANCED threshold `iv.2` fed to the folded tail's own residual `frest`. The
     kept sub-list is built by CONSING the newly-kept head onto `frest iv.2` (never `acc ++ [x]`),
     so the scan stays a single `O(n)` pass once `frest` is applied.  `foldKept` obeys `foldKept
     (wrap d) = gKept d`, `foldKept (cons iv xs) = stKept iv (foldKept xs)` by construction (both
     `rfl`), so `kept_emerges` reads straight off `consFold_unique`.

  3. **Composing.**  `derivedSolve ivs := ivs.length - (foldKeptSorted (foldSort (ofList
     ivs))).length` runs the emergent sort, then seeds the emergent scan from the sorted list's own
     head exactly as `L435.keptSorted` does; `derivedSolve_eq` shows it agrees with `LC435.solveFn`
     pointwise, by the SAME bridging recipe as `L252_derived`'s `noAdjFromC_ofList` (induction on the
     raw list, every step unfolds definitionally).

  4. **Correctness is REUSED, not re-proved**, from `LC435.solve_correct` (achievability +
     domination, headline shape 2, extremum/min-removals).  Honest note on the headline SHAPE: the
     unconditional morphism-equation form `graph solveFn = Λ spec ≫ est D`
     (`A7_4_Horner.eq_Λ_comp_est`) does NOT apply here, for the SAME reason as `L11_derived`:
     `LC435.solve_correct` is CONDITIONAL on `Valid ivs` (every interval's `.1 < .2`, LeetCode 435's
     own strict constraint — genuinely load-bearing, per `L435.lean`'s own `Valid` docstring, not a
     proof artifact) — `eq_Λ_comp_est` demands `hsound`/`hbest` UNCONDITIONALLY over the whole
     domain, which is false for degenerate/invalid interval lists.  We therefore state the honest
     bundle: both emergences (unconditional) ∧ `derivedSolve = solveFn` ∧ the reused CONDITIONAL
     achievability+domination pair, exactly `LC435.solve_correct`'s own shape.

  **Complexity**: `derivedSolve` is `O(n²)` overall, same as `LC435.solveFn` — dominated by
  `isortH`'s inherent `O(n²)` insertion sort (unchanged, not re-derived); the emergent greedy scan
  itself is a single `O(n)` pass (one cons + one comparison per element, once the residual is
  applied to a threshold).

  Mathlib-free (Lean core + `AOP.A6_GenFold`, `AOP.A6_ConsList`, `leet.L435` only).  We route
  through `CL.consFold_unique` only, never `cataR_eq_relCata` (pulls `Classical.choice`).  No
  `Classical.choice`; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L435

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC435D

open Freyd List Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC435

/-! ## Part 1: `isortH`, reshaped onto the cons-list initial algebra (plain `List` carrier) -/

/-- The base of the emergent sort algebra: the empty suffix sorts to the empty list. -/
def gSort : Unit → List (Int × Int) := fun _ => []

/-- The step of the emergent sort algebra: insert the new head into the folded (already sorted)
    tail — exactly `L435.linsertH`, read off `isortH`'s own cons clause. -/
def stSort : (Int × Int) → List (Int × Int) → List (Int × Int) := fun iv acc => linsertH iv acc

/-- The sort fold, structural recursion on `ConsList Unit (Int×Int)`, mirroring `isortH`. -/
def foldSort : ConsList Unit (Int × Int) → List (Int × Int)
  | ConsList.wrap _ => gSort ()
  | ConsList.cons iv xs => stSort iv (foldSort xs)

/-- The base condition is a COMPUTATION: `foldSort (wrap d) = gSort d`. -/
theorem foldSort_wrap : ∀ d : Unit, foldSort (ConsList.wrap d) = gSort d := fun _ => rfl

/-- The step condition IS `foldSort`'s cons equation. -/
theorem foldSort_cons : ∀ (iv : Int × Int) (xs : ConsList Unit (Int × Int)),
    foldSort (ConsList.cons iv xs) = stSort iv (foldSort xs) := fun _ _ => rfl

/-- **The sort EMERGES.**  `graph foldSort` equals the catamorphism of `consScalarAlg gSort
    stSort` — insertion sort by `.2`, PRODUCED by `CL.consFold_unique`, never hand-written as a
    fold.  Inherently `O(n²)` (unchanged from `LC435.isortH`). -/
theorem sort_emerges :
    (graph foldSort : dCL Unit (Int × Int) ⟶ ⟨List (Int × Int)⟩)
      = cataR (consScalarAlg gSort stSort) :=
  consFold_unique gSort stSort foldSort foldSort_wrap foldSort_cons

/-- The reshaped sort agrees with `LC435.isortH` on converted input, by straightforward induction
    (no lookahead needed — `isortH`'s own recursion is already the cons-fold shape). -/
theorem foldSort_ofList : ∀ xs : List (Int × Int), foldSort (CL.ofList xs) = isortH xs
  | [] => rfl
  | iv :: rest => by
      show stSort iv (foldSort (CL.ofList rest)) = isortH (iv :: rest)
      rw [foldSort_ofList rest]; rfl

/-! ## Part 2: `keptList`, reshaped as a CURRIED residual awaiting the threshold `lastEnd`

    Carrier `C := Int → List (Int×Int)` — the RESIDUAL scan that, having folded the list, still
    awaits the running threshold `lastEnd` (the latest kept interval's end seen so far).  For each
    threshold, the residual returns the actual kept sub-list — "carrier `(lastEnd, keptList)`". -/

/-- The base of the emergent scan algebra: the residual after folding the empty suffix keeps
    nothing, at ANY threshold. -/
def gKept : Unit → (Int → List (Int × Int)) := fun _ _ => []

/-- The step of the emergent scan algebra: from the folded tail's residual `frest = foldKept xs`
    and the head interval `iv`, the residual for `cons iv xs` answers the threshold `lastEnd` by
    requiring `lastEnd ≤ iv.1` and, if so, CONSING `iv` onto the tail's residual applied at the
    ADVANCED threshold `iv.2` — read off `keptList`'s own cons clause, curried in the awaited
    threshold.  Built by CONS, never `acc ++ [x]`. -/
def stKept : (Int × Int) → (Int → List (Int × Int)) → (Int → List (Int × Int)) :=
  fun iv frest => fun lastEnd => if lastEnd ≤ iv.1 then iv :: frest iv.2 else frest lastEnd

/-- The residual threshold-scan, folded directly over `ConsList Unit (Int×Int)` by the forced
    recursion above. -/
def foldKept : ConsList Unit (Int × Int) → (Int → List (Int × Int))
  | ConsList.wrap d => gKept d
  | ConsList.cons iv xs => stKept iv (foldKept xs)

/-- The base condition: `foldKept (wrap d) = gKept d` — by construction. -/
theorem foldKept_wrap : ∀ d : Unit, foldKept (ConsList.wrap d) = gKept d := fun _ => rfl

/-- The step condition: `foldKept (cons iv xs) = stKept iv (foldKept xs)` — by construction. -/
theorem foldKept_cons : ∀ (iv : Int × Int) (xs : ConsList Unit (Int × Int)),
    foldKept (ConsList.cons iv xs) = stKept iv (foldKept xs) := fun _ _ => rfl

/-- **The greedy scan EMERGES.**  `graph foldKept` equals the catamorphism of `consScalarAlg
    gKept stKept` on the FUNCTION carrier `Int → List (Int×Int)`, PRODUCED by `CL.consFold_unique`
    — the forward-threaded threshold scan is a single catamorphism whose output is the residual
    `foldKept l : Int → List (Int×Int)` awaiting the threshold. -/
theorem kept_emerges :
    (graph foldKept : dCL Unit (Int × Int) ⟶ ⟨Int → List (Int × Int)⟩)
      = cataR (consScalarAlg gKept stKept) :=
  consFold_unique gKept stKept foldKept foldKept_wrap foldKept_cons

/-- The emergent residual, bridged to the ORIGINAL `List`-valued `keptList` through the SHARED
    `CL.ofList`: folding `ofList l` and applying the residual at `lastEnd` is exactly `keptList
    lastEnd l` — every step unfolds definitionally, as `L252_derived`'s `noAdjFromC_ofList`. -/
theorem foldKept_ofList : ∀ (l : List (Int × Int)) (lastEnd : Int),
    foldKept (CL.ofList l) lastEnd = keptList lastEnd l := by
  intro l
  induction l with
  | nil => intro lastEnd; rfl
  | cons iv rest ih =>
      intro lastEnd
      show (if lastEnd ≤ iv.1 then iv :: foldKept (CL.ofList rest) iv.2
            else foldKept (CL.ofList rest) lastEnd) = keptList lastEnd (iv :: rest)
      rw [ih iv.2, ih lastEnd, keptList_cons_eq]

/-! ## Part 3: composing — `keptSorted`, seeded from the sorted list's own head -/

/-- Seed the emergent residual from the sorted list's own head, matching `L435.keptSorted`'s own
    seeding (not part of the emergent fold — the fold is `foldKept` over the TAIL). -/
def foldKeptSorted (l : List (Int × Int)) : List (Int × Int) :=
  match l with
  | [] => []
  | iv :: rest => iv :: foldKept (CL.ofList rest) iv.2

/-- The seeded emergent scan IS `L435.keptSorted`, pointwise. -/
theorem foldKeptSorted_eq (l : List (Int × Int)) : foldKeptSorted l = keptSorted l := by
  cases l with
  | nil => rfl
  | cons iv rest =>
      show iv :: foldKept (CL.ofList rest) iv.2 = iv :: keptList iv.2 rest
      rw [foldKept_ofList]

/-- **The derived program**: sort via the emergent cons-fold (`foldSort`), then run the emergent
    greedy scan (`foldKeptSorted`) over the sorted result. -/
def derivedSolve (ivs : List (Int × Int)) : Nat :=
  ivs.length - (foldKeptSorted (foldSort (CL.ofList ivs))).length

/-- The derived program IS `LC435.solveFn`, pointwise. -/
theorem derivedSolve_eq (ivs : List (Int × Int)) : derivedSolve ivs = solveFn ivs := by
  unfold derivedSolve solveFn
  rw [foldSort_ofList, foldKeptSorted_eq]

/-! ## Correctness — REUSED from `LC435.solve_correct` (headline shape 2: extremum, min removals)

    `solve_correct` is CONDITIONAL on `Valid ivs`, so the unconditional morphism-equation headline
    `A7_4_Horner.eq_Λ_comp_est` does not apply (see the file docstring); we bundle the two
    emergences with the reused conditional achievability+domination pair instead. -/

/-- **Honest headline.**  Bundles:
    (1) `sort_emerges` — insertion sort by `.2` IS the catamorphism of `consScalarAlg gSort
        stSort`, produced by `CL.consFold_unique`;
    (2) `kept_emerges` — the greedy threshold scan IS the catamorphism of `consScalarAlg gKept
        stKept` on the residual carrier `Int → List (Int×Int)`, produced by `CL.consFold_unique`;
    (3) `derivedSolve ivs = solveFn ivs` — the composed derived program agrees with the hand-written
        one;
    (4) achievability + domination for `derivedSolve`, REUSED from `LC435.solve_correct` (NOT
        re-proved) — min removals is exactly `ivs.length - derivedSolve ivs`'s complementary
        maximum kept sub-selection. -/
theorem solve_derived_correct {ivs : List (Int × Int)} (hval : Valid ivs) :
    ((graph foldSort : dCL Unit (Int × Int) ⟶ ⟨List (Int × Int)⟩)
        = cataR (consScalarAlg gSort stSort)) ∧
    ((graph foldKept : dCL Unit (Int × Int) ⟶ ⟨Int → List (Int × Int)⟩)
        = cataR (consScalarAlg gKept stKept)) ∧
    derivedSolve ivs = solveFn ivs ∧
    (∃ sub, sub <+ ivs ∧ NonOverlap sub ∧ sub.length = ivs.length - derivedSolve ivs) ∧
    (∀ sub, sub <+ ivs → NonOverlap sub → sub.length ≤ ivs.length - derivedSolve ivs) := by
  have heq := derivedSolve_eq ivs
  obtain ⟨hach, hdom⟩ := solve_correct ivs hval
  rw [← heq] at hach hdom
  exact ⟨sort_emerges, kept_emerges, heq, hach, hdom⟩

/-! ## Running the derived program (matching `L435`'s own examples) -/

-- LeetCode 435's own example: `[[1,2],[2,3],[3,4],[1,3]] → 1` (remove `[1,3]`).
example : derivedSolve [(1, 2), (2, 3), (3, 4), (1, 3)] = 1 := by decide
-- `[[1,2],[1,2],[1,2]] → 2` (keep just one copy).
example : derivedSolve [(1, 2), (1, 2), (1, 2)] = 2 := by decide
-- Already pairwise non-overlapping (touching is fine): `[[1,2],[2,3]] → 0`.
example : derivedSolve [(1, 2), (2, 3)] = 0 := by decide

end Freyd.Alg.RelSet.LC435D
