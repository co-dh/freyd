/-
  `takeWhile` derived by SHRINK — a port of AoPA `Examples/GC/TakeWhile.agda`
  (Mu–Oliveira, "Programming from Galois connections").

  SPEC (program-independent).  For a predicate `p`, a valid answer to `takeWhile p` on a list `l`
  is any prefix of `l` all of whose elements satisfy `p`:
      `twSpec l out  :=  out ≼ l  ∧  every element of out satisfies p`.
  The wanted answer is the LONGEST such prefix.  In AoPA this is `(mapR (p¿) ○ _≼_) ↾ _≽_`:
  the relation "a `p`-satisfying prefix" (`mapR (p¿) ○ _≼_`) shrunk by the prefix order `_≽_`
  so that only the longest survives.

  HEADLINE (this repo).  The longest-prefix requirement is exactly Bird & de Moor's `max`, and the
  AoPA shrink `S ↾ R` is `Λ S ≫ minRel R` (`A7_6.shrink_eq_Λ_comp_minRel`).  So the derivation's
  headline is the morphism equation
      `graph (twCL p)  =  Λ twSpec ≫ maxRel prefDom`                    (`takeWhile_eq_Λ_maxRel`)
  where `prefDom w z := z ≼ w` (dominance = "w is at least as long"), and equivalently the shrink
  form
      `graph (twCL p)  =  twSpec ↾ prefSub`                             (`takeWhile_eq_shrink`)
  with `prefSub = prefDom°` the sub-prefix order (`w ≼ z`) — AoPA's `spec ↾ ≽`, up to the
  min/max and argument-order conventions.  Both come out of `RelSet.eq_Λ_comp_maxRel` (the two
  halves it consumes — achievability and prefix-domination — are proved here directly).

  PROGRAM EMERGENCE.  `twCL p` is not hand-written and then verified: it is PRODUCED as the
  catamorphism of its base/step by the cons-list fold-uniqueness law (`CL.consFold_unique`),
  mirroring AoPA's `foldR-fold`/`greedy-cata` step:
      `graph (twCL p)  =  cataR (consScalarAlg (fun _ => []) (twStep p))`   (`takeWhile_emerges`).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
module

public import AOP.A7_6_Shrink
public import AOP.A7_4_Horner
public import AOP.A6_ConsList
public import AOP.A6_GenFold

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.GCTakeWhile

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL

variable {E : Type}

/-! ## Supporting list facts (AoPA `Examples/GC/List.agda`, `Nat.agda`) -/

/-- The underlying list of a `ConsList Unit E` (AoPA's `μ ListF` unfolded). -/
def flat : ConsList Unit E → List E
  | ConsList.wrap _   => []
  | ConsList.cons x xs => x :: flat xs

/-- `AllP p l` — every element of `l` satisfies `p` (AoPA `mapR (p ¿)` restricted to the
    diagonal). -/
def AllP (p : E → Bool) : List E → Prop
  | []      => True
  | x :: xs => p x = true ∧ AllP p xs

/-- The prefix relation `u ≼ w` (AoPA `_≼_ = foldR ListF [ nil , (nil ○ !) ⊔ cons ]`):
    `[] ≼ w` always, and `x∷u ≼ x∷w` iff `u ≼ w`. -/
def Pre : List E → List E → Prop
  | []      , _       => True
  | _ :: _  , []      => False
  | x :: xs , y :: ys => x = y ∧ Pre xs ys

/-- Prefix antisymmetry (AoPA: `_≼_` is a partial order; underlies `≼-isPreorder` + antisymmetry
    used for the shrink's uniqueness). -/
theorem pre_antisym : ∀ {a b : List E}, Pre a b → Pre b a → a = b
  | []      , []      , _  , _  => rfl
  | []      , _ :: _  , _  , hb => (hb).elim
  | _ :: _  , []      , ha , _  => (ha).elim
  | x :: xs , y :: ys , ha , hb => by
      have hxy : x = y := ha.1
      have := pre_antisym ha.2 hb.2      -- xs = ys
      rw [hxy, this]

/-! ## The program `twCL` and its base/step -/

/-- The step of `takeWhile`: keep the head iff it satisfies `p`, else stop. -/
def twStep (p : E → Bool) (x : E) (c : List E) : List E :=
  match p x with
  | true  => x :: c
  | false => []

/-- `takeWhile p` on `ConsList Unit E`.  Defined by the very recursion whose base/step is
    `(fun _ => [])` / `twStep p`, so `CL.consFold_unique` produces it as a catamorphism. -/
def twCL (p : E → Bool) : ConsList Unit E → List E
  | ConsList.wrap _    => []
  | ConsList.cons x xs => twStep p x (twCL p xs)

/-! ## The spec (program-independent) -/

/-- `twSpec p c out`: `out` is a `p`-satisfying prefix of the list `flat c`. -/
def twSpec (p : E → Bool) : dCL Unit E ⟶ (⟨List E⟩ : RelSet.{0}) :=
  fun c out => Pre out (flat c) ∧ AllP p out

/-- Dominance order on answers: `w` dominates `z` when `z ≼ w` (`w` is at least as long).
    `maxRel prefDom` selects the LONGEST prefix. -/
def prefDom : (⟨List E⟩ : RelSet.{0}) ⟶ ⟨List E⟩ := fun w z => Pre z w

/-! ## Program emergence (AoPA `foldR-fold`) -/

/-- **The program is produced by the fold law.**  `twCL p` obeys the cons-list recursion of its
    base/step, so it IS the catamorphism of `consScalarAlg (fun _ => []) (twStep p)`. -/
theorem takeWhile_emerges (p : E → Bool) :
    (graph (twCL p) : dCL Unit E ⟶ ⟨List E⟩)
      = cataR (consScalarAlg (fun _ : Unit => ([] : List E)) (twStep p)) :=
  consFold_unique (fun _ => []) (twStep p) (twCL p) (fun _ => rfl) (fun _ _ => rfl)

/-! ## The two halves the headline consumes -/

/-- Achievability: `twCL p c` is itself a `p`-satisfying prefix of `flat c`. -/
theorem tw_sound (p : E → Bool) (c : ConsList Unit E) : twSpec p c (twCL p c) := by
  induction c with
  | wrap u => exact ⟨trivial, trivial⟩
  | cons x xs ih =>
      show Pre (twStep p x (twCL p xs)) (x :: flat xs) ∧ AllP p (twStep p x (twCL p xs))
      unfold twStep
      cases hpx : p x with
      | false => exact ⟨trivial, trivial⟩
      | true  => exact ⟨⟨rfl, ih.1⟩, ⟨hpx, ih.2⟩⟩

/-- Domination: every `p`-satisfying prefix `out` of `flat c` is a prefix of `twCL p c`
    (so `twCL p c` is the longest). -/
theorem tw_best (p : E → Bool) (c : ConsList Unit E) (out : List E)
    (h : twSpec p c out) : Pre out (twCL p c) := by
  induction c generalizing out with
  | wrap u =>
      -- flat (wrap u) = []; a prefix of [] is [], and twCL = []
      cases out with
      | nil => exact trivial
      | cons y ys => exact (h.1).elim
  | cons x xs ih =>
      cases out with
      | nil => exact trivial
      | cons y ys =>
          -- h.1 : Pre (y::ys) (x :: flat xs) = (y = x) ∧ Pre ys (flat xs)
          -- h.2 : AllP p (y::ys) = (p y = true) ∧ AllP p ys
          have hyx : y = x := h.1.1
          have hpre : Pre ys (flat xs) := h.1.2
          have hpy : p y = true := h.2.1
          have htail : AllP p ys := h.2.2
          show Pre (y :: ys) (twStep p x (twCL p xs))
          unfold twStep
          have hpx : p x = true := by rw [← hyx]; exact hpy
          rw [hpx]
          exact ⟨hyx, ih ys ⟨hpre, htail⟩⟩

/-! ## Headlines -/

/-- **Morphism-equation headline (max form).**  `graph (twCL p) = Λ twSpec ≫ maxRel prefDom` —
    `takeWhile p` is exactly `max prefDom · Λ twSpec`, the longest `p`-satisfying prefix, as a
    relation (not merely pointwise).  Via `RelSet.eq_Λ_comp_maxRel`, fed the two halves above and
    prefix antisymmetry. -/
theorem takeWhile_eq_Λ_maxRel (p : E → Bool) :
    (graph (twCL p) : dCL Unit E ⟶ ⟨List E⟩) = Λ (twSpec p) ≫ maxRel (prefDom (E := E)) :=
  eq_Λ_comp_maxRel (prefDom (E := E))
    (fun x y h1 h2 => pre_antisym h2 h1)               -- antisymmetry of prefDom
    (twCL p) (twSpec p)
    (tw_sound p)                                        -- achievability
    (fun c v hv => tw_best p c v hv)                    -- domination (longest)

/-- **Shrink-form headline (AoPA `spec ↾ ≽`).**  `graph (twCL p) = twSpec ↾ prefDom°`.  This is
    the AoPA shrink presentation: the `p`-satisfying-prefix relation, shrunk by the prefix order,
    equals `takeWhile`.  Immediate from the max form by `shrink_eq_Λ_comp_minRel`
    (`maxRel R = minRel R°`). -/
theorem takeWhile_eq_shrink (p : E → Bool) :
    (graph (twCL p) : dCL Unit E ⟶ ⟨List E⟩) = twSpec p ↾ (prefDom (E := E))° := by
  rw [shrink_eq_Λ_comp_minRel]
  exact takeWhile_eq_Λ_maxRel p

/-! ## Executable sanity checks -/

/-- `takeWhile (· < 3) [1,2,5,1] = [1,2]`. -/
example : twCL (fun n => decide (n < 3)) (ofList [1, 2, 5, 1]) = [1, 2] := by decide
/-- Everything satisfies `p` ⇒ the whole list. -/
example : twCL (fun n => decide (n < 9)) (ofList [1, 2, 5]) = [1, 2, 5] := by decide
/-- Head fails ⇒ empty. -/
example : twCL (fun n => decide (n < 1)) (ofList [1, 2]) = [] := by decide

end Freyd.Alg.RelSet.GCTakeWhile
