/-
  **Recursive-coalgebra hylomorphism uniqueness** — the `Nat`-measured dual of the catamorphism
  fold-uniqueness laws in `A6_GenFold`.

  `SL.snocFold_unique` / `CL.consFold_unique` state that a structural fold of an INITIAL algebra is
  the unique catamorphism.  The dual object is a RECURSIVE COALGEBRA: a coalgebra
  `c : S → L + E×S` whose unfolding is well-founded, so that folding the (finite) call tree it
  generates terminates.  Here the well-foundedness is witnessed concretely by a `Nat` measure `μ`
  that strictly decreases on every recursive `Sum.inr` step (`hdec`).

  The hylomorphism `hyloFold c μ hdec g st : S ⟶ C` first unfolds `c` down to the `Sum.inl` leaves
  and then re-folds with the algebra `[g, st]`.  `hyloFold_unique` is the dual of the fold laws: any
  ordinary function `h : S → C` obeying the recursion
  `h s = match c s with | inl l => g l | inr (e, s') => st e (h s')` IS this hylomorphism — proved by
  strong induction on `μ s`.  This is the law a merge/divide-and-conquer program (`L21.mergeFn`)
  uses to certify itself against its relational specification.  Mathlib-free (Lean core WF recursion
  on the `Nat` measure `μ`, `WellFounded.fix` / `measure`); constructive, no `Classical.choice`.
-/
module

public import AOP.A6_GenFold

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Hylo

open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {L E S C : Type}

/-! ## The relational hylomorphism, by well-founded recursion on the measure -/

/-- One layer of the hylomorphism recursion, abstracting the recursive call as `rec` (available at
    any state whose measure is strictly smaller, so the `Sum.inr` branch may use it).  The `hcs :`
    binder keeps the coalgebra equation `c s = Sum.inr (e, s')` in scope so `hdec` can discharge the
    measure decrease that `rec` demands. -/
@[expose] public def hyloStep (c : S → Sum L (E × S)) (μ : S → Nat)
    (hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s) (g : L → C) (st : E → C → C)
    (s : S) (rec : (s' : S) → μ s' < μ s → C → Prop) (r : C) : Prop :=
  match hcs : c s with
  | Sum.inl l => r = g l
  | Sum.inr (e, s') => ∃ r', rec s' (hdec s e s' hcs) r' ∧ r = st e r'

/-- The relational hylomorphism of a `Nat`-measured recursive coalgebra: `hyloFold c μ hdec g st`
    relates `s` to `r` iff re-folding the finite call tree that `c` unfolds from `s` with the
    algebra `[g, st]` yields `r`.  Defined by `WellFounded.fix` on the measure `μ` (fully
    constructive core recursion). -/
@[expose] public def hyloFold (c : S → Sum L (E × S)) (μ : S → Nat)
    (hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s) (g : L → C) (st : E → C → C) :
    S → C → Prop :=
  WellFounded.fix (measure μ).wf (hyloStep c μ hdec g st)

/-- The one-step unfolding of `hyloFold` (from `WellFounded.fix_eq`). -/
public theorem hyloFold_unfold (c : S → Sum L (E × S)) (μ : S → Nat)
    (hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s) (g : L → C) (st : E → C → C) (s : S) :
    hyloFold c μ hdec g st s
      = hyloStep c μ hdec g st s (fun s' _ => hyloFold c μ hdec g st s') :=
  WellFounded.fix_eq (measure μ).wf (hyloStep c μ hdec g st) s

/-- Reduction on a `Sum.inl` leaf: the hylomorphism just returns the algebra's base `g l`. -/
public theorem hyloFold_inl (c : S → Sum L (E × S)) (μ : S → Nat)
    (hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s) (g : L → C) (st : E → C → C)
    {s : S} {l : L} {r : C} (hc : c s = Sum.inl l) :
    hyloFold c μ hdec g st s r ↔ r = g l := by
  rw [congrFun (hyloFold_unfold c μ hdec g st s) r]
  unfold hyloStep
  split
  · rename_i l' heq
    rw [hc] at heq; injection heq with h1; subst h1; exact Iff.rfl
  · rename_i e s' heq
    rw [hc] at heq; nomatch heq

/-- Reduction on a `Sum.inr` node: the hylomorphism recurses on `s'` then applies the step `st e`. -/
public theorem hyloFold_inr (c : S → Sum L (E × S)) (μ : S → Nat)
    (hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s) (g : L → C) (st : E → C → C)
    {s : S} {e : E} {s' : S} {r : C} (hc : c s = Sum.inr (e, s')) :
    hyloFold c μ hdec g st s r ↔ ∃ r', hyloFold c μ hdec g st s' r' ∧ r = st e r' := by
  rw [congrFun (hyloFold_unfold c μ hdec g st s) r]
  unfold hyloStep
  split
  · rename_i l heq
    rw [hc] at heq; nomatch heq
  · rename_i e₀ s₀ heq
    rw [hc] at heq; injection heq with h1
    injection h1 with h2 h3; subst h2; subst h3; exact Iff.rfl

/-- The hylomorphism packaged as a `Rel(Set)` morphism `⟨S⟩ ⟶ ⟨C⟩`. -/
@[expose] public def hyloR (c : S → Sum L (E × S)) (μ : S → Nat)
    (hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s) (g : L → C) (st : E → C → C) :
    (⟨S⟩ : RelSet.{0}) ⟶ ⟨C⟩ :=
  hyloFold c μ hdec g st

/-- **Recursive-coalgebra hylomorphism uniqueness** (the dual of `snocFold_unique`).  A function
    `h : S → C` obeying the recursion `h s = match c s with | inl l => g l | inr (e, s') => st e (h s')`
    IS the hylomorphism of the measured coalgebra `c` with algebra `[g, st]`.  Proved by strong
    induction on the measure `μ s`. -/
public theorem hyloFold_unique (c : S → Sum L (E × S)) (μ : S → Nat)
    (hdec : ∀ s e s', c s = Sum.inr (e, s') → μ s' < μ s) (g : L → C) (st : E → C → C) (h : S → C)
    (hstep : ∀ s, h s = match c s with
      | Sum.inl l => g l
      | Sum.inr (e, s') => st e (h s')) :
    (graph h : (⟨S⟩ : RelSet.{0}) ⟶ ⟨C⟩) = hyloR c μ hdec g st := by
  have key : ∀ s r, (r = h s ↔ hyloFold c μ hdec g st s r) := by
    intro s
    refine (measure μ).wf.induction
      (C := fun s => ∀ r, (r = h s ↔ hyloFold c μ hdec g st s r)) s ?_
    clear s; intro s IH r
    cases hcs : c s with
    | inl l =>
        rw [hyloFold_inl c μ hdec g st hcs]
        have hhs : h s = g l := by rw [hstep s, hcs]
        rw [hhs]
    | inr est =>
        obtain ⟨e, s'⟩ := est
        rw [hyloFold_inr c μ hdec g st hcs]
        have hhs : h s = st e (h s') := by rw [hstep s, hcs]
        have hIH : ∀ r', (r' = h s' ↔ hyloFold c μ hdec g st s' r') :=
          IH s' (hdec s e s' hcs)
        rw [hhs]
        constructor
        · intro hr
          exact ⟨h s', (hIH (h s')).mp rfl, hr⟩
        · rintro ⟨r', hr', hrst⟩
          rw [(hIH r').mpr hr'] at hrst
          exact hrst
  exact hom_ext fun s r => key s r

/-! ## Acceptance example: 2-way MERGE as a measured recursive coalgebra

  `L21.mergeFn` merges two lists; here we instantiate the law on the merge coalgebra to check it is
  usable — the hand-written efficient merge equals the relational hylomorphism. -/

namespace MergeExample

/-- The merge coalgebra: emit a leaf when either list is exhausted, otherwise pop the smaller head. -/
def mc : List Int × List Int → Sum (List Int) (Int × (List Int × List Int))
  | ([], ys) => Sum.inl ys
  | (xs, []) => Sum.inl xs
  | (x :: xs, y :: ys) =>
      if x ≤ y then Sum.inr (x, (xs, y :: ys)) else Sum.inr (y, (x :: xs, ys))

/-- The measure: total remaining length. -/
def mμ : List Int × List Int → Nat := fun p => p.1.length + p.2.length

/-- Every `Sum.inr` step drops exactly one element, so `mμ` strictly decreases. -/
theorem mdec : ∀ s e s', mc s = Sum.inr (e, s') → mμ s' < mμ s := by
  intro s e s' h
  obtain ⟨xs, ys⟩ := s
  cases xs with
  | nil => simp only [mc] at h; nomatch h
  | cons x xs =>
      cases ys with
      | nil => simp only [mc] at h; nomatch h
      | cons y ys =>
          simp only [mc] at h
          split at h
          · injection h with h1; injection h1 with h2 h3; subst h3
            simp only [mμ, List.length_cons]; omega
          · injection h with h1; injection h1 with h2 h3; subst h3
            simp only [mμ, List.length_cons]; omega

/-- The efficient merge, by well-founded recursion on the same measure. -/
def mergeFn : List Int × List Int → List Int
  | ([], ys) => ys
  | (xs, []) => xs
  | (x :: xs, y :: ys) =>
      if x ≤ y then x :: mergeFn (xs, y :: ys) else y :: mergeFn (x :: xs, ys)
termination_by s => s.1.length + s.2.length
decreasing_by
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega

/-- The law is usable: the hand-written merge equals the relational hylomorphism of `mc`.  The
    remaining `?_` goal is exactly "`mergeFn` obeys the hylomorphism recurrence for `mc` with algebra
    `[id, (· :: ·)]`", discharged by case analysis on the two lists. -/
theorem mergeFn_eq_hylo :
    (graph mergeFn : (⟨List Int × List Int⟩ : RelSet.{0}) ⟶ ⟨List Int⟩)
      = hyloR mc mμ mdec id (· :: ·) := by
  refine hyloFold_unique mc mμ mdec id (· :: ·) mergeFn ?_
  intro s
  obtain ⟨xs, ys⟩ := s
  cases xs with
  | nil => simp [mergeFn, mc]
  | cons x xs =>
      cases ys with
      | nil => simp [mergeFn, mc]
      | cons y ys =>
          simp only [mergeFn]
          split
          · rename_i h; simp only [mc, if_pos h]
          · rename_i h; simp only [mc, if_neg h]

end MergeExample

end Freyd.Alg.RelSet.Hylo
