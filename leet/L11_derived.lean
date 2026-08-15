/-
  LeetCode 11 — Container With Most Water — DERIVED as a relational HYLOMORPHISM (O(n)).

  `leet/L11.lean` writes the two-pointer sweep `twoPtrFuel` over a `List Int`, tamed with an explicit
  `fuel` parameter (the two indices `lo`/`hi` move independently, so the recursion is not structural on
  either one).  Two prices are paid there: the `fuel` bookkeeping, and — because a `List` is indexed by
  `h[i]!` in O(i) — an O(n²) sweep.

  The right scheme for a two-pointer / measured recursion is the DUAL of the fold: a RECURSIVE COALGEBRA
  `c : S → L + E×S` whose unfolding is well-founded, re-folded with an algebra `[g, st]`.
  `Hylo.hyloFold_unique` (`AOP/A6_GenHylo.lean`) is the uniqueness law: any function `h` obeying
  `h s = match c s with | inl l => g l | inr (e,s') => st e (h s')` IS the hylomorphism `hyloR c μ hdec g st`.

  Instantiation for L11 (heights fixed as an `Array Int` for O(1) access — the O(n) upgrade):
    * state       `S := Nat × Nat` — the window `(lo, hi)`;
    * measure     `μ (lo,hi) := hi - lo`, dropping by one on each `.inr` step (`hdec`);
    * coalgebra   `c (lo,hi)` — leaf `.inl ()` when the window has collapsed (`lo ≥ hi`), else EMIT the
      current window's area `min h[lo] h[hi] · (hi−lo)` as an `.inr` node and move the SHORTER wall inward
      (branch order matching `LC11.twoPtrFuel` exactly);
    * algebra     base `g := fun _ => 0` (an empty window holds no water), step `st := LC11.imax` (fold the
      emitted areas with `max`) — headline shape 2 (extremum, max).

  `sweep_emerges` runs `hyloFold_unique` on the Array-based sweep `sweep`: it certifies that the O(n)
  program IS the relational hylomorphism of `c` — the program was never re-written, only shown to satisfy
  the hylomorphism recurrence (discharged IN PLACE by a case split).  Correctness — achievability +
  domination over EVERY pair — is REUSED from `L11.lean` (`LC11.maxArea_achievable`/`maxArea_dominates`)
  through the bridge `arrSolve h = LC11.maxAreaFn h.toList` (the Array sweep equals the List sweep); it is
  not re-proved.

  Honest headline note: `LC11.maxArea_correct` is CONDITIONAL on `Nonneg h.toList` (heights `≥ 0`) and
  `2 ≤ h.toList.length` (a valid pair exists).  For `n < 2` the achievability relation `IsPairArea` is
  empty while `arrSolve` returns `0`, so the unconditional morphism-equation headline `graph solveFn =
  Λ spec ≫ maxRel D` (`A7_4_Horner.eq_Λ_comp_maxRel`) does NOT hold here.  We therefore state the honest
  bundle: emergence (unconditional) ∧ the reused conditional correctness.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound} (fully constructive, no `Classical.choice`).
-/
import AOP.A6_GenHylo
import leet.L11

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC11D

open Freyd

/-! ## The two-pointer sweep as a measured recursive coalgebra (heights fixed as an `Array Int`) -/

/-- The window's water area over an `Array Int` (O(1) indexing).  Same formula as `LC11.Area`, but on an
    array — this is the O(n) upgrade of the O(n²) `List` version. -/
def areaA (h : Array Int) (lo hi : Nat) : Int := LC11.imin h[lo]! h[hi]! * ((hi : Int) - (lo : Int))

/-- The sweep coalgebra: emit a leaf (`.inl ()`) once the window has collapsed (`lo ≥ hi`), otherwise EMIT
    the current window's area as a node (`.inr`) and move the SHORTER wall inward.  Branch order matches
    `LC11.twoPtrFuel`'s recurrence EXACTLY (test `lo < hi`, then compare `h[lo]` vs `h[hi]`). -/
def c (h : Array Int) : Nat × Nat → Sum Unit (Int × (Nat × Nat)) := fun p =>
  if p.1 < p.2 then
    if h[p.1]! ≤ h[p.2]! then Sum.inr (areaA h p.1 p.2, (p.1 + 1, p.2))
    else Sum.inr (areaA h p.1 p.2, (p.1, p.2 - 1))
  else Sum.inl ()

/-- The measure: window width.  The coalgebra's unfolding is well-founded because every `.inr` step
    moves one wall inward, dropping the width by one (`hdec`). -/
def μ : Nat × Nat → Nat := fun p => p.2 - p.1

/-- Every `.inr` step drops the width by one, so `μ` strictly decreases — the well-foundedness witness the
    hylomorphism law demands. -/
theorem hdec (h : Array Int) : ∀ s e s', c h s = Sum.inr (e, s') → μ s' < μ s := by
  rintro ⟨lo, hi⟩ e s' hcs
  simp only [c] at hcs
  split at hcs
  · rename_i hlt
    split at hcs
    · injection hcs with hp; rw [Prod.ext_iff] at hp; obtain ⟨_, hs'⟩ := hp
      subst hs'; simp only [μ]; omega
    · injection hcs with hp; rw [Prod.ext_iff] at hp; obtain ⟨_, hs'⟩ := hp
      subst hs'; simp only [μ]; omega
  · nomatch hcs

/-- The Array-based two-pointer sweep, by well-founded recursion on the window width `hi - lo` (NO fuel).
    Records the current window's area, then discards the shorter wall; returns the running `max`. -/
def sweep (h : Array Int) : Nat × Nat → Int := fun p =>
  if p.1 < p.2 then
    if h[p.1]! ≤ h[p.2]! then LC11.imax (areaA h p.1 p.2) (sweep h (p.1 + 1, p.2))
    else LC11.imax (areaA h p.1 p.2) (sweep h (p.1, p.2 - 1))
  else 0
termination_by p => p.2 - p.1
decreasing_by
  · simp_wf; omega
  · simp_wf; omega

/-! ## The sweep EMERGES as the relational hylomorphism -/

/-- **The derivation.**  The Array sweep `sweep h` IS the relational hylomorphism of the measured
    coalgebra `c h` with algebra `[fun _ => 0, LC11.imax]` — it was never re-written as a hylomorphism;
    `hyloFold_unique` certifies that it satisfies the hylomorphism recurrence.  The remaining goal is
    exactly "`sweep h` obeys `h s = match c h s with | inl _ => 0 | inr (e,s') => imax e (h s')`",
    discharged by the case split on the two `if`s of `sweep`/`c` (identical branch structure). -/
theorem sweep_emerges (h : Array Int) :
    (graph (sweep h) : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ ⟨Int⟩)
      = Hylo.hyloR (c h) μ (hdec h) (fun _ => 0) LC11.imax := by
  refine Hylo.hyloFold_unique (c h) μ (hdec h) (fun _ => 0) LC11.imax (sweep h) ?_
  intro s
  obtain ⟨lo, hi⟩ := s
  rw [sweep]
  simp only [c]
  by_cases hlt : lo < hi
  · simp only [if_pos hlt]
    by_cases hle : h[lo]! ≤ h[hi]!
    · simp only [if_pos hle]
    · simp only [if_neg hle]
  · simp only [if_neg hlt]

/-! ## Correctness carries over from `L11.lean` via the Array = List sweep bridge -/

/-- `Array.toList` indexing agrees with `Array` indexing (both default to `0` out of bounds). -/
theorem toList_getElem! (h : Array Int) (i : Nat) : h.toList[i]! = h[i]! := by
  simp only [getElem!_def, Array.getElem?_toList]

/-- The Array area equals the `List` area of `h.toList` (windowed by the same indices). -/
theorem areaA_eq (h : Array Int) (lo hi : Nat) : LC11.Area h.toList lo hi = areaA h lo hi := by
  simp only [LC11.Area, areaA, toList_getElem!]

/-- The Array sweep computes exactly the `List` fuel-sweep of `h.toList`, given enough fuel — proved by
    induction on `fuel` (the fuel unfolding on the right mirrors the WF unfolding of `sweep` on the left,
    with indexing/area bridged by `toList_getElem!`/`areaA_eq`). -/
theorem sweep_eq_fuel (h : Array Int) :
    ∀ fuel lo hi, hi ≤ lo + fuel → sweep h (lo, hi) = LC11.twoPtrFuel h.toList fuel lo hi := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hf
    rw [sweep, if_neg (show ¬ lo < hi by omega)]
    simp only [LC11.twoPtrFuel]
  | succ k ih =>
    intro lo hi hf
    rw [sweep]
    by_cases hlt : lo < hi
    · rw [if_pos hlt]
      simp only [LC11.twoPtrFuel]
      rw [if_pos hlt]
      simp only [toList_getElem!, areaA_eq]
      split
      · rw [ih (lo + 1) hi (by omega)]
      · rw [ih lo (hi - 1) (by omega)]
    · rw [if_neg hlt]
      simp only [LC11.twoPtrFuel]
      rw [if_neg hlt]

/-- **The program**: L11's solution as an Array function.  `n < 2` has no valid pair — area `0`. -/
def arrSolve (h : Array Int) : Int := if h.size ≥ 2 then sweep h (0, h.size - 1) else 0

/-- The bridge: the Array program equals the `List` program `LC11.maxAreaFn` on `h.toList`. -/
theorem arrSolve_eq (h : Array Int) : arrSolve h = LC11.maxAreaFn h.toList := by
  simp only [arrSolve, LC11.maxAreaFn, Array.length_toList]
  by_cases hs : 2 ≤ h.size
  · rw [if_pos hs, if_pos hs]
    exact sweep_eq_fuel h h.size 0 (h.size - 1) (by omega)
  · rw [if_neg hs, if_neg hs]

/-- **The allegory program**: L11's solution as a morphism `⟨Array Int⟩ ⟶ ℤ` in `Rel(Set)`. -/
def solveA : (⟨Array Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := graph arrSolve

/-- `solveA` is a `Map` (it is the graph of a function). -/
theorem solveA_map : Map solveA := graph_map arrSolve

/-! ## Headline: emergence ∧ reused (conditional) correctness -/

/-- **Headline.**  The honest bundle:
    (1) the Array O(n) sweep `sweep h` IS the relational hylomorphism of the measured coalgebra `c h` with
        algebra `[fun _ => 0, LC11.imax]` (`sweep_emerges`) — the derivation; and
    (2) given the problem constraints (heights `≥ 0`, at least two lines), the program's answer
        `arrSolve h` is the `≤`-MAXIMUM of the achievability relation `LC11.IsPairArea h.toList`:
        achievable AND dominating every achievable area.  This is `LC11.maxArea_correct` carried across
        the bridge `arrSolve h = LC11.maxAreaFn h.toList` — REUSED, not re-proved. -/
theorem container_derived_correct (h : Array Int)
    (hnn : LC11.Nonneg h.toList) (hlen : 2 ≤ h.toList.length) :
    ((graph (sweep h) : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ ⟨Int⟩)
        = Hylo.hyloR (c h) μ (hdec h) (fun _ => 0) LC11.imax)
      ∧ (LC11.IsPairArea h.toList (arrSolve h)
          ∧ ∀ a, LC11.IsPairArea h.toList a → a ≤ arrSolve h) := by
  refine ⟨sweep_emerges h, ?_, ?_⟩
  · rw [arrSolve_eq]; exact LC11.maxArea_achievable hnn hlen
  · rw [arrSolve_eq]; intro a ha; exact LC11.maxArea_dominates hnn a ha

/-! ## Running the certified program

  `arrSolve`/`sweep` are WF-recursive (do not reduce under `decide`), so run the examples through the
  bridge `arrSolve_eq` to the kernel-reducible fuel-sweep on `h.toList`. -/

example : arrSolve #[1, 8, 6, 2, 5, 4, 8, 3, 7] = 49 := by rw [arrSolve_eq]; decide
example : arrSolve #[1, 1] = 1 := by rw [arrSolve_eq]; decide

end Freyd.Alg.RelSet.LC11D
