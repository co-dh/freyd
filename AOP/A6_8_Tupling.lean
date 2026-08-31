/-
  The **tupling law** (Bird–de Moor / Fokkinga mutual-recursion law) for snoc-list
  catamorphisms, as a genuine calculational step in `Rel(Set)`.

  A function `h : SnocList L E → C` obeying the FIRST-ORDER lockstep recursion
    `h (wrap l)     = g l`
    `h (snoc xs e)  = step (h xs) e`
  is, by the initial-algebra universal property (uniqueness of the catamorphism), EXACTLY the
  catamorphism `⦇[g, step]⦈` of the algebra `[g, step]`.  When the carrier is a PRODUCT
  `C₁ × C₂` this is the tupling / linearization move: to compute a function that "looks back"
  more than one step (a second-order recurrence), carry a tuple of the last few values and run a
  single first-order fold.  The pair-carrying fold is then not written by hand and verified — it
  is PRODUCED by this law from the base `g` and the step `step`, both of which are read off the
  recurrence.  `leet/L70_derived.lean` and `leet/L1137_derived.lean` derive Fibonacci and
  Tribonacci this way.

  Reuses the whole `A6_SnocList` engine (`cataFold`, `cataR`, `cataFold_wrap`, `cataFold_snoc`)
  with ZERO new engine code.  Mathlib-free.
-/
module

public import AOP.A6_SnocList

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.SL

open Freyd

/-- Read a snoc-list over `Unit` as a natural number: `wrap () ↦ 0`, `snoc xs () ↦ natOf xs + 1`.
    `SnocList Unit Unit` is the initial algebra of `1 + X`, i.e. `ℕ`, so this is the isomorphism
    onto `ℕ` that lets a `ℕ`-recurrence be run as a snoc-list catamorphism.  Shared by every
    `ℕ`-over-`SnocList` derivation (`L70_derived`, `L1137_derived`). -/
@[expose] public def natOf : SnocList Unit Unit → Nat
  | SnocList.wrap _    => 0
  | SnocList.snoc xs _ => natOf xs + 1

/-- The `ℕ`-to-`SnocList Unit Unit` encoding (inverse of `natOf`): `n` ↦ `n` `snoc`s over
    `wrap ()`.  Used to feed concrete numerals to the emergent folds for cross-checking. -/
@[expose] public def snocs : Nat → SnocList Unit Unit
  | 0     => SnocList.wrap ()
  | n + 1 => SnocList.snoc (snocs n) ()

theorem natOf_snocs (n : Nat) : natOf (snocs n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => show natOf (snocs k) + 1 = k + 1; rw [ih]

/-- Emergent product-algebra from base `g : L → C₁×C₂` and step `step : C₁×C₂ → E → C₁×C₂`.
    This is the algebra `[g, step] : F(C₁×C₂) → C₁×C₂` whose catamorphism the tupling law
    identifies with the lockstep recursion; it is the graph of the case split, hence a `Map`. -/
@[expose] public def pairAlg {L E C₁ C₂ : Type} (g : L → C₁ × C₂) (step : C₁ × C₂ → E → C₁ × C₂) :
    Fobj L E (⟨C₁ × C₂⟩ : RelSet.{0}) ⟶ (⟨C₁ × C₂⟩ : RelSet.{0}) :=
  graph (fun u => match u with
    | Sum.inl l      => g l
    | Sum.inr (p, e) => step p e)

/-- The emergent algebra is a `Map` (it is a graph). -/
theorem pairAlg_map {L E C₁ C₂ : Type} (g : L → C₁ × C₂) (step : C₁ × C₂ → E → C₁ × C₂) :
    Map (pairAlg g step) := graph_map _

/-- **The tupling law.**  A function `h` solving the first-order lockstep recursion
    `h (wrap l) = g l`, `h (snoc xs e) = step (h xs) e` IS the catamorphism of `pairAlg g step`.
    Proof: catamorphism uniqueness — `graph h` and `cataR (pairAlg g step)` satisfy the SAME
    structural recursion, so a single induction on the datatype identifies them. -/
public theorem tupling {L E C₁ C₂ : Type} (g : L → C₁ × C₂) (step : C₁ × C₂ → E → C₁ × C₂)
    (h : SnocList L E → C₁ × C₂)
    (hwrap : ∀ l, h (SnocList.wrap l) = g l)
    (hsnoc : ∀ xs e, h (SnocList.snoc xs e) = step (h xs) e) :
    (graph h : dSL L E ⟶ ⟨C₁ × C₂⟩) = cataR (pairAlg g step) := by
  apply hom_ext; intro d w
  show w = h d ↔ cataFold (pairAlg g step) d w
  induction d generalizing w with
  | wrap l =>
      rw [cataFold_wrap, hwrap l]
      exact Iff.rfl
  | snoc xs e ih =>
      rw [cataFold_snoc, hsnoc]
      constructor
      · intro hw
        exact ⟨h xs, (ih (h xs)).mp rfl, hw⟩
      · rintro ⟨r', hr', hstep⟩
        have hr'eq : r' = h xs := (ih r').mpr hr'
        rw [hr'eq] at hstep
        exact hstep

/-- **First-component projection.**  Composing the tupling law with `graph Prod.fst` extracts the
    scalar answer: the graph of `d ↦ (h d).1` is the catamorphism of `pairAlg g step` followed by
    the first projection.  This is where the scalar Fibonacci / Tribonacci number comes out. -/
public theorem tupling_fst {L E C₁ C₂ : Type} (g : L → C₁ × C₂) (step : C₁ × C₂ → E → C₁ × C₂)
    (h : SnocList L E → C₁ × C₂)
    (hwrap : ∀ l, h (SnocList.wrap l) = g l)
    (hsnoc : ∀ xs e, h (SnocList.snoc xs e) = step (h xs) e) :
    (graph (fun d => (h d).1) : dSL L E ⟶ ⟨C₁⟩)
      = cataR (pairAlg g step) ≫ graph (Prod.fst : C₁ × C₂ → C₁) := by
  rw [← tupling g step h hwrap hsnoc]
  apply hom_ext; intro d c
  constructor
  · intro hc; exact ⟨h d, rfl, hc⟩
  · rintro ⟨p, hp, hc⟩; rw [hp] at hc; exact hc

/-! ## Banana-split (the non-cross-referencing special case)

  When the step does NOT feed one component from the other —
  `g l = (g₁ l, g₂ l)` and `step (a, b) e = (step₁ a e, step₂ b e)` — the pair-carrying fold
  decomposes as the *pairing* of two INDEPENDENT scalar folds (Bird–de Moor's banana-split law
  `⦇g₁ △ g₂⦈ = ⦇g₁⦈ △ ⦇g₂⦈`).  Fibonacci does NOT fit this shape: its step `(a,b) ↦ (b, a+b)`
  feeds the new second component from BOTH old values, so the general cross-referencing `tupling`
  is required — banana-split alone cannot linearize a genuine second-order recurrence. -/

/-- A scalar algebra `[g, st] : F C → C` over a bare carrier `C` (the graph of the case split). -/
@[expose] public def scalarAlg {L E C : Type} (g : L → C) (st : C → E → C) :
    Fobj L E (⟨C⟩ : RelSet.{0}) ⟶ (⟨C⟩ : RelSet.{0}) :=
  graph (fun u => match u with
    | Sum.inl l      => g l
    | Sum.inr (a, e) => st a e)

/-- **Banana-split.**  For non-cross-referencing base/step, the pair-fold is the pairing
    `rpair` of the two independent scalar folds.  Proven by the same uniqueness induction as
    `tupling` (not by delegating to it), threading the two components in lockstep. -/
theorem tupling_banana {L E C₁ C₂ : Type}
    (g₁ : L → C₁) (g₂ : L → C₂) (step₁ : C₁ → E → C₁) (step₂ : C₂ → E → C₂) :
    cataR (pairAlg (fun l => (g₁ l, g₂ l)) (fun p e => (step₁ p.1 e, step₂ p.2 e)))
      = rpair (cataR (scalarAlg g₁ step₁)) (cataR (scalarAlg g₂ step₂)) := by
  apply hom_ext; intro d p
  show cataFold (pairAlg (fun l => (g₁ l, g₂ l)) (fun p e => (step₁ p.1 e, step₂ p.2 e))) d p
      ↔ cataFold (scalarAlg g₁ step₁) d p.1 ∧ cataFold (scalarAlg g₂ step₂) d p.2
  induction d generalizing p with
  | wrap l =>
      rw [cataFold_wrap, cataFold_wrap, cataFold_wrap]
      constructor
      · intro hp
        have : p = (g₁ l, g₂ l) := hp
        rw [this]; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        show p = (g₁ l, g₂ l)
        have : p = (p.1, p.2) := rfl
        rw [this, h1, h2]
  | snoc xs e ih =>
      rw [cataFold_snoc, cataFold_snoc, cataFold_snoc]
      constructor
      · rintro ⟨r', hr', hstep⟩
        have hstep' : p = (step₁ r'.1 e, step₂ r'.2 e) := hstep
        obtain ⟨h1, h2⟩ := (ih r').mp hr'
        refine ⟨⟨r'.1, h1, ?_⟩, ⟨r'.2, h2, ?_⟩⟩
        · show p.1 = step₁ r'.1 e; rw [hstep']
        · show p.2 = step₂ r'.2 e; rw [hstep']
      · rintro ⟨⟨a', ha', hpa⟩, ⟨b', hb', hpb⟩⟩
        refine ⟨(a', b'), (ih (a', b')).mpr ⟨ha', hb'⟩, ?_⟩
        show p = (step₁ a' e, step₂ b' e)
        have : p = (p.1, p.2) := rfl
        rw [this, hpa, hpb]

end Freyd.Alg.RelSet.SL
