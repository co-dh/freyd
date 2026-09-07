/-
  LeetCode 252 — Meeting Rooms — DERIVED as a CONS-LIST catamorphism (threshold CPS carrier).

  `leet/L252.lean` sorts by start (`leet.L56.isort`, reused verbatim — the sort is NOT re-derived
  here, see the file's own docstring: insertion sort is inherently O(n²), a fact orthogonal to the
  scan below), then runs a LEFT-TO-RIGHT threshold scan `noAdjFrom lastHi l` over the sorted list:
  the running threshold `lastHi` (the latest meeting's end seen so far) is THREADED FORWARD through
  the recursive call (`noAdjFrom lastHi (iv :: rest) = if lastHi ≤ iv.1 then noAdjFrom iv.2 rest else
  false`) — an accumulator scan, not literally `h (cons e xs) = st e (h xs)` in threshold-first form.

  It BECOMES a `ConsList`-catamorphism once the threshold is CURRIED to the other side, exactly the
  `L98_derived` CPS trick (there: bounds threaded top-down through a `Tree`; here: a threshold
  threaded left-to-right through a `List`).  Read `noAdjFrom` as `List (Int×Int) → (Int → Bool)`:
  fold the list FIRST into a RESIDUAL `noAdjFromC l : Int → Bool` that still AWAITS the threshold
  `lastHi`.  With carrier `C := Int → Bool` this residual is an ordinary front-to-back structural
  fold of the list, exposed by the general-carrier law `CL.consFold_unique`
  (`AOP/A6_GenFold.lean`) over `ConsList Unit (Int×Int)` (`AOP/A6_ConsList.lean`, the initial
  algebra of `F X = Unit + (Int×Int)×X`, `L`-axis trivial since raw `List` has no leaf label).

  The base `g = noAdjFromC (wrap ())` and step `step = noAdjFromC (cons iv xs)` are READ OFF
  `noAdjFrom`'s two defining equations, curried on the awaited threshold: `g _ = true` (an empty
  list is trivially attendable at any threshold), and `step iv frest := fun lastHi => if lastHi ≤
  iv.1 then frest iv.2 else false` — exactly `noAdjFrom`'s cons clause, with the recursive call's
  NEW threshold `iv.2` fed to the folded tail's own residual `frest`.  `noAdjFromC` obeys the
  structural recursion `noAdjFromC (wrap d) = g d`, `noAdjFromC (cons iv xs) = step iv (noAdjFromC
  xs)` by construction (`hwrap`, `hcons`, both `rfl`).  The law `CL.consFold_unique g step
  noAdjFromC hwrap hcons` then PRODUCES the catamorphism `cataR (consScalarAlg g step)` and
  identifies it with `graph noAdjFromC` (`noAdjFromC_emerges`): the threshold scan is not written as
  an accumulator, it emerges as a fold into a function carrier.

  Raw `List` reshaping (the recipe of `AOP/A6_GenFold.lean`'s header): `noAdjFromC` is folded over
  `ConsList Unit (Int×Int)`, bridged to the ORIGINAL `List`-valued `noAdjFrom` via the SHARED
  `CL.ofList : List E → ConsList Unit E` (`noAdjFromC_ofList`, by induction on the raw list — every
  step defeq-unfolds, so the induction closes by `rfl` after one rewrite).  `noAdj` (which seeds the
  scan from the sorted list's own head — `leet.L252`'s own thin wrapper, not part of the scan) and
  `canAttendFn := noAdj ∘ isort` are then matched pointwise (`noAdjD_eq_noAdj`,
  `canAttendFn_derived_eq`) and `LC252.canAttend_correct` — the existing decision `Iff`, NOT
  re-proved here — is transported onto the emergent fold (`canAttend_derived_correct`), headline
  shape 3 (decision `b = true ↔ P`).

  **Complexity**: the emergent scan is a single structural pass over the (sorted) list, O(n); the
  overall program is dominated by `isort`'s inherent O(n²) (insertion sort, unchanged — the sort is
  left as-is per `leet/L252.lean`'s own docstring, not re-derived).

  Mathlib-free (Lean core `Init` plus `AOP.A6_GenFold`, `AOP.A6_ConsList`, `leet.L252`).  We
  route through `CL.consFold_unique` only, never the `cataR_eq_relCata` bridge (pulls
  `Classical.choice`).  No `Classical.choice`; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L252

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC252D

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC56 Freyd.Alg.RelSet.LC252

/-! ## `noAdjFrom` with the list curried to the FRONT: the residual threshold-checker

  Carrier `C := Int → Bool` — the RESIDUAL scan that, having folded the list, still awaits the
  running threshold `lastHi` (the latest meeting's end seen so far). -/

/-- The base of the emergent algebra: `g = noAdjFromC (wrap ())` — the residual after folding the
    empty list answers `true` at ANY threshold (an empty tail is trivially attendable). -/
def g : Unit → (Int → Bool) := fun _ _ => true

/-- The step of the emergent algebra: from the folded tail's residual `frest = noAdjFromC xs` and
    the head meeting `iv`, the residual for `cons iv xs` answers the threshold `lastHi` by requiring
    `lastHi ≤ iv.1` AND applying the tail's residual at the ADVANCED threshold `iv.2`.  Read off
    `noAdjFrom`'s cons clause, curried in the awaited threshold. -/
def step : (Int × Int) → (Int → Bool) → (Int → Bool) :=
  fun iv frest => fun lastHi => if lastHi ≤ iv.1 then frest iv.2 else false

/-- The residual threshold-checker, folded directly over `ConsList Unit (Int×Int)` by the forced
    recursion above (there is no pre-existing `List`-curried function to wrap, unlike `L98`'s
    `within` — `noAdjFrom` is not itself defined by recursion on the initial algebra). -/
def noAdjFromC : ConsList Unit (Int × Int) → (Int → Bool)
  | ConsList.wrap D => g D
  | ConsList.cons iv xs => step iv (noAdjFromC xs)

/-! ## The FORCED structural recursion of `noAdjFromC` -/

/-- The base condition: `noAdjFromC (wrap d) = g d` — by construction. -/
theorem hwrap (D : Unit) : noAdjFromC (ConsList.wrap D) = g D := rfl

/-- The step condition: `noAdjFromC (cons iv xs) = step iv (noAdjFromC xs)` — by construction. -/
theorem hcons (iv : Int × Int) (xs : ConsList Unit (Int × Int)) :
    noAdjFromC (ConsList.cons iv xs) = step iv (noAdjFromC xs) := rfl

/-! ## The catamorphism EMERGES via the general-carrier law -/

/-- **The residual threshold-checker EMERGES.**  `graph noAdjFromC` equals the catamorphism of the
    scalar cons-list algebra `consScalarAlg g step = [wrap ↦ g, (iv, xs) ↦ step iv xs]` on the
    FUNCTION carrier `Int → Bool`, PRODUCED by `CL.consFold_unique` from the forced base `g` and
    step `step`.  The forward-threaded threshold scan is now a single catamorphism over the
    cons-list, whose output is the residual `noAdjFromC l : Int → Bool` awaiting the threshold — the
    AOP curry that turns a left-to-right accumulator scan into a fold. -/
theorem noAdjFromC_emerges :
    (graph noAdjFromC : dCL Unit (Int × Int) ⟶ ⟨Int → Bool⟩) = cataR (consScalarAlg g step) :=
  CL.consFold_unique g step noAdjFromC hwrap hcons

/-! ## Connecting the emergent residual back to `L252`'s raw-`List` scan -/

/-- The emergent fold, bridged to the ORIGINAL `List`-valued `noAdjFrom` through the SHARED
    `CL.ofList`: folding `ofList l` and applying the residual at `lastHi` is exactly `noAdjFrom
    lastHi l` — every step unfolds definitionally (`ofList`, `noAdjFromC`, `step` are all forced
    pattern matches), so the induction closes by `rfl` after one rewrite by the tail's IH. -/
theorem noAdjFromC_ofList : ∀ (l : List (Int × Int)) (lastHi : Int),
    noAdjFromC (CL.ofList l) lastHi = noAdjFrom lastHi l := by
  intro l
  induction l with
  | nil => intro lastHi; rfl
  | cons iv rest ih =>
      intro lastHi
      show (if lastHi ≤ iv.1 then noAdjFromC (CL.ofList rest) iv.2 else false) =
          noAdjFrom lastHi (iv :: rest)
      rw [ih iv.2]
      rfl

/-- **The derived scan**: seed the residual from the sorted list's own head, matching `L252.noAdj`'s
    own seeding (not part of the emergent fold — the fold is `noAdjFromC` over the TAIL). -/
def noAdjD (l : List (Int × Int)) : Bool :=
  match l with
  | [] => true
  | iv :: rest => noAdjFromC (CL.ofList rest) iv.2

/-- The derived scan IS `L252.noAdj`, pointwise. -/
theorem noAdjD_eq_noAdj (l : List (Int × Int)) : noAdjD l = noAdj l := by
  cases l with
  | nil => rfl
  | cons iv rest => exact noAdjFromC_ofList rest iv.2

/-- **The derived program**: sort (unchanged, `leet.L56.isort`), then the emergent scan. -/
def canAttendFn_derived (ivs : List (Int × Int)) : Bool := noAdjD (isort ivs)

/-- The derived program IS `L252.canAttendFn`, pointwise. -/
theorem canAttendFn_derived_eq (ivs : List (Int × Int)) :
    canAttendFn_derived ivs = canAttendFn ivs :=
  noAdjD_eq_noAdj (isort ivs)

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The derived allegory program**: `canAttendFn_derived` as a morphism `Ivs ⟶ Bool`. -/
def derivedSolve : LC252.Ivs ⟶ dBool := graph canAttendFn_derived

/-- `derivedSolve` IS `L252.solve` (the underlying functions agree pointwise). -/
theorem derivedSolve_eq_solve : derivedSolve = LC252.solve := by
  have hfun : canAttendFn_derived = canAttendFn := funext canAttendFn_derived_eq
  unfold derivedSolve LC252.solve
  rw [hfun]

/-! ## Correctness of the derived program, transported from `L252.canAttend_correct` -/

/-- **The Meeting-Rooms decision is the emergent cons-list catamorphism, and it is correct.**  The
    honest headline bundles:

    * `noAdjFromC_emerges` — `graph noAdjFromC = cataR (consScalarAlg g step)`: the curried
      threshold scan IS the catamorphism over the FUNCTION carrier `Int → Bool`; and
    * the transported decision — `canAttendFn_derived` (sort, unchanged, then the emergent scan)
      decides pairwise non-overlap exactly as `L252.canAttendFn` does
      (`L252.canAttend_correct`, NOT re-proved here). -/
theorem canAttend_derived_correct :
    ((graph noAdjFromC : dCL Unit (Int × Int) ⟶ ⟨Int → Bool⟩) = cataR (consScalarAlg g step)) ∧
    (∀ (ivs : List (Int × Int)), LC252.Valid ivs →
        (canAttendFn_derived ivs = true ↔ NonOverlap ivs)) := by
  refine ⟨noAdjFromC_emerges, ?_⟩
  intro ivs hval
  rw [canAttendFn_derived_eq]
  exact canAttend_correct ivs hval

/-! ## Running the derived program (matching `L252`'s own examples) -/

example : canAttendFn_derived [(0, 30), (5, 10), (15, 20)] = false := by decide
example : canAttendFn_derived [(7, 10), (2, 4)] = true := by decide
example : canAttendFn_derived [(1, 5), (5, 10)] = true := by decide

end Freyd.Alg.RelSet.LC252D
