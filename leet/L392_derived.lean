/-
  LeetCode 392 — Is Subsequence — DERIVED as a cons-list catamorphism over `t` (FUNCTION carrier).

  `leet/L392.lean` WRITES `isSubseqFn s t : List Int → List Int → Bool` by hand, structural on `t`
  (both live branches of the `cons`/`cons` case replace `b :: t'` by `t'`). CURRY the OTHER argument:
  read `isSubseqFn` as `List Int → (List Int → Bool)`, i.e. fold `t` FIRST into a RESIDUAL matcher
  `matchC t : List Int → Bool` that still awaits `s`. With carrier `C := List Int → Bool` this
  residual is an ordinary structural fold of `t`'s `ConsList Unit Int` shape
  (`AOP.A6_ConsList.ofList`, front-to-back), and the AOP way to expose it is the general-carrier
  cons-list fold-uniqueness law `CL.consFold_unique` (`AOP/A6_GenFold.lean`) — the same idea as
  `L98_derived`'s tree residual, here on `ConsList` instead of `Tree`, and NO zip/pairing operation is
  needed: currying the two-input function is the whole trick.

  The base `g = matchC (wrap ())` and step `step = matchC (cons b -)` are READ OFF `isSubseqFn`'s
  defining equations, curried on the awaited `s`: `g _ = fun s => decide (s = [])` (the residual after
  folding an empty `t` accepts only the empty `s`), and `step b fr` (`fr` = residual of `t`'s tail)
  answers `s`: `[] ↦ true`; `a :: s' ↦ if a = b then fr s' else fr (a :: s')` — the exact
  head-compare/branch of `isSubseqFn`'s cons/cons clause. `matchC` obeys the structural recursion
  `matchC (wrap _) = g`, `matchC (cons b tl) = step b (matchC tl)` — both `rfl` (`hwrap`, `hcons`,
  since `matchC` is defined literally by those two equations). The law
  `CL.consFold_unique g step matchC hwrap hcons` then PRODUCES the higher-order catamorphism
  `cataR (consScalarAlg g step)` and identifies it with `graph matchC`: the two-argument greedy match
  is not written as a two-argument recursion here — it EMERGES as a fold of `t` alone.

  `matchC (ofList t) s = isSubseqFn s t` (`matchC_ofList`, by induction on `t`, mirroring
  `isSubseqFn`'s own recursion on its second argument) connects the emergent residual back to
  `leet.L392`'s program; feeding it into `LC392.subseq_correct` gives the decision headline WITHOUT
  re-proving any `List.Sublist` fact.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}. We route through `CL.consFold_unique`
  only, never `CL.cataR_eq_relCata` (pulls `Classical.choice`).
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L392

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC392D

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC392
open List

/-! ## `isSubseqFn` with `t` curried to the FRONT: the residual matcher

  Carrier `C := List Int → Bool` — the RESIDUAL that, having folded `t`, still awaits `s`. -/

/-- The base of the emergent algebra: the residual after folding the empty `t` accepts only the
    empty `s`. -/
def g : Unit → (List Int → Bool) := fun _ s => match s with
  | [] => true
  | _ :: _ => false

/-- The step of the emergent algebra: from the tail's residual `fr` and the popped head `b` of `t`,
    the residual for `b :: t'` answers `s` by: the empty `s` always matches; a nonempty `a :: s'`
    matches iff (`a = b` and the STRICT tail `fr s'`) or (`a ≠ b` and `fr` is applied unchanged to
    `a :: s'`, letting `s` wait past `b`) — exactly the head-compare/branch of `isSubseqFn`'s
    cons/cons clause. -/
def step : Int → (List Int → Bool) → (List Int → Bool) :=
  fun b fr s => match s with
    | [] => true
    | a :: s' => if a = b then fr s' else fr (a :: s')

/-- `matchC t` — fold `t` (as a `ConsList Unit Int`) into the residual matcher that still awaits
    `s`. Defined directly by the `g`/`step` read off above, so `hwrap`/`hcons` below are `rfl`. -/
def matchC : ConsList Unit Int → List Int → Bool
  | ConsList.wrap d => g d
  | ConsList.cons b tl => step b (matchC tl)

/-! ## The FORCED structural recursion of the curried `isSubseqFn` -/

/-- The base condition: `matchC (wrap d) = g d`, by construction. -/
theorem hwrap (d : Unit) : matchC (ConsList.wrap d) = g d := rfl

/-- The step condition: `matchC (cons b tl) = step b (matchC tl)`, by construction. -/
theorem hcons (b : Int) (tl : ConsList Unit Int) :
    matchC (ConsList.cons b tl) = step b (matchC tl) := rfl

/-! ## The higher-order catamorphism EMERGES via the general-carrier law -/

/-- **The residual matcher EMERGES.** `graph matchC` equals the catamorphism of the scalar
    cons-list algebra `consScalarAlg g step` on the FUNCTION carrier `List Int → Bool`, PRODUCED by
    `CL.consFold_unique` from the forced base `g` and step `step`. The two-argument greedy match is
    now a single catamorphism over `t`, whose output is the residual `matchC t : List Int → Bool`
    awaiting `s` — the AOP curry that turns a two-argument decision recursion into a fold. -/
theorem match_emerges :
    (graph matchC : dCL Unit Int ⟶ ⟨List Int → Bool⟩) = cataR (consScalarAlg g step) :=
  CL.consFold_unique g step matchC hwrap hcons

/-! ## Connecting the emergent residual back to `L392.isSubseqFn` -/

/-- The emergent residual, applied to `ofList t`, computes exactly `isSubseqFn s t` — by induction
    on `t` (the `ConsList` recursion mirrors `isSubseqFn`'s recursion on its second argument). -/
theorem matchC_ofList : ∀ (t s : List Int), matchC (CL.ofList t) s = LC392.isSubseqFn s t
  | [], s => by cases s <;> rfl
  | b :: t', s => by
    cases s with
    | nil => rfl
    | cons a s' =>
      show (if a = b then matchC (CL.ofList t') s' else matchC (CL.ofList t') (a :: s')) =
          (if a = b then LC392.isSubseqFn s' t' else LC392.isSubseqFn (a :: s') t')
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab]; exact matchC_ofList t' s'
      · rw [if_neg hab, if_neg hab]; exact matchC_ofList t' (a :: s')

/-- The derived solver: fold `t` via `ofList`, then apply the emergent residual to `s`. -/
def derivedSolve : dInput ⟶ dBool :=
  graph (fun p : List Int × List Int => matchC (CL.ofList p.2) p.1)

/-- The derived solver IS `LC392.solve` — the residual applied to `s` after folding `t` computes
    the same boolean as `isSubseqFn s t` (`matchC_ofList`). -/
theorem derivedSolve_eq_solve : derivedSolve = LC392.solve :=
  congrArg graph (funext fun p => matchC_ofList p.2 p.1)

/-! ## Correctness of the derived program, transported from `LC392.subseq_correct` -/

/-- **The Is-Subsequence program is the emergent catamorphism over `t`, and it DECIDES
    `List.Sublist`.** The honest headline bundles:

    * `match_emerges` — `graph matchC = cataR (consScalarAlg g step)`: the curried program IS the
      cons-list catamorphism over the FUNCTION carrier `List Int → Bool`; and
    * the transported decision correctness — for ANY residual `h` that the emergent fold relates the
      list `t` to, `h` decides `s <+ t` for every `s` (`h s = true ↔ s <+ t`). Emergence pins
      `h = matchC (ofList t)`, and `LC392.subseq_correct` (NOT re-proved here) supplies the decision. -/
theorem subseq_derived_correct :
    ((graph matchC : dCL Unit Int ⟶ ⟨List Int → Bool⟩) = cataR (consScalarAlg g step)) ∧
    (∀ (t : List Int) (h : List Int → Bool),
        cataFold (consScalarAlg g step) (CL.ofList t) h → ∀ s : List Int, h s = true ↔ s <+ t) := by
  refine ⟨match_emerges, ?_⟩
  intro t h hh s
  have hgr : (graph matchC : dCL Unit Int ⟶ ⟨List Int → Bool⟩) (CL.ofList t) h := by
    rw [match_emerges]; exact hh
  have hfeq : h = matchC (CL.ofList t) := hgr
  subst hfeq
  rw [matchC_ofList t s]
  exact LC392.subseq_correct s t

/-! ## Running the emergent fold, cross-checked against `leet/L392.lean` -/

example : matchC (CL.ofList [97, 104, 98, 103, 100, 99]) [97, 98, 99] = true := by decide
example : matchC (CL.ofList [97, 104, 98, 103, 100, 99]) [97, 120, 99] = false := by decide

/-- The emergent fold genuinely relates `t = [97, 104, 98]` to its RESIDUAL matcher `matchC (ofList
    t)` — the function the fold produces, proved via `match_emerges` (no `decide` on the function
    carrier). -/
example : cataFold (consScalarAlg g step) (CL.ofList [97, 104, (98 : Int)])
    (matchC (CL.ofList [97, 104, (98 : Int)])) := by
  have h : (graph matchC : dCL Unit Int ⟶ ⟨List Int → Bool⟩)
      (CL.ofList [97, 104, (98 : Int)]) (matchC (CL.ofList [97, 104, (98 : Int)])) := rfl
  rw [match_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC392D
