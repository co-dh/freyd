/-
  §5.4's power relator against the existential image, on one concrete relation `R : A → B`, with
  `A = {1,2,3}` and `B = {a,b,c}`.  The note's picture of `R` is drawn from `R` itself by
  `diag-export --graph`, which lists the constructors of `A` and `B` and decides every pair.
-/
module

public import Freyd.S2_30_Example
public import AOP.A7_2_RelSet
public import AOP.A5_7_PowerBeads

@[expose] public section

namespace Freyd.Alg.ImageExample

open Freyd.S2_30.Example (Listed)
open Freyd.Alg.RelSet (existsImage_apply)

inductive A | «1» | «2» | «3» deriving DecidableEq
inductive B | a | b | c deriving DecidableEq

instance : Listed B := ⟨[.a, .b, .c], fun e => by cases e <;> decide⟩

/-- `n R t`: the relation of the example — `1` to `a` and `b`, `3` to `c`, and `2` to nothing. -/
def R (n : A) (t : B) : Prop :=
  (n, t) ∈ ([(.«1», .a), (.«1», .b), (.«3», .c)] : List (A × B))

instance : DecidableRel R := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

/-- `R(2) = ∅`: the one element of `A` with the empty image. -/
theorem R_two_empty : ∀ t, ¬ R .«2» t := by decide

/-- `P(R)` between two listed subsets is decided by its pointwise reading. -/
instance {A B : Type} (R : (⟨A⟩ : RelSet.{0}) ⟶ ⟨B⟩) [∀ x y, Decidable (R x y)] (xs : List A)
    (ys : List B) : Decidable (P(R) (· ∈ xs) (· ∈ ys)) :=
  decidable_of_iff ((∀ s, s ∈ xs → ∃ w, w ∈ ys ∧ R s w) ∧ ∀ w, w ∈ ys → ∃ s, s ∈ xs ∧ R s w) <| by
    rw [powerRel_apply]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun s hs => (h₁ s hs).imp fun _ h => ⟨h.2, h.1⟩, h₂⟩,
      fun ⟨h₁, h₂⟩ => ⟨fun s hs => (h₁ s hs).imp fun _ h => ⟨h.2, h.1⟩, h₂⟩⟩

/-- `E(R)` between two listed subsets, over a listed target, is decided by its pointwise reading. -/
instance {A B : Type} [DecidableEq B] [Listed B] (R : (⟨A⟩ : RelSet.{0}) ⟶ ⟨B⟩)
    [∀ x y, Decidable (R x y)] (xs : List A) (ys : List B) : Decidable (existsImage R (· ∈ xs) (· ∈ ys)) :=
  decidable_of_iff (∀ w, w ∈ ys ↔ ∃ s, s ∈ xs ∧ R s w) <| by
    rw [existsImage_apply]
    exact ⟨fun h => funext fun w => propext (h w), fun h w => iff_of_eq (congrFun h w)⟩

/-- The 8 subsets of `B`, in the order of the note's table. -/
def subsetsB : List (List B) := [[], [.a], [.b], [.c], [.a, .b], [.a, .c], [.b, .c], [.a, .b, .c]]

/-- The `E(R)` column of the note's table: each `xs` has exactly one `E(R)`-image, the set of the
    `R`-images of its members. -/
theorem E_column : ∀ row ∈ ([([], []), ([.«1»], [.a, .b]), ([.«2»], []), ([.«3»], [.c]),
      ([.«1», .«2»], [.a, .b]), ([.«1», .«3»], [.a, .b, .c]), ([.«2», .«3»], [.c]),
      ([.«1», .«2», .«3»], [.a, .b, .c])] : List (List A × List B)),
    ∀ ys ∈ subsetsB,
      (existsImage (A := (⟨A⟩ : RelSet.{0})) (B := ⟨B⟩) R (· ∈ row.1) (· ∈ ys) ↔ ys = row.2) := by
  decide

/-- The `P(R)` column of the note's table: the subsets `ys` with every member of `xs` reaching
    into `ys` and every member of `ys` reached from `xs`. -/
theorem P_column : ∀ row ∈ ([([], [[]]), ([.«1»], [[.a], [.b], [.a, .b]]), ([.«2»], []),
      ([.«3»], [[.c]]), ([.«1», .«2»], []), ([.«1», .«3»], [[.a, .c], [.b, .c], [.a, .b, .c]]),
      ([.«2», .«3»], []), ([.«1», .«2», .«3»], [])] : List (List A × List (List B))),
    ∀ ys ∈ subsetsB,
      (powerRel (A := (⟨A⟩ : RelSet.{0})) (B := ⟨B⟩) R (· ∈ row.1) (· ∈ ys) ↔ ys ∈ row.2) := by
  decide

end Freyd.Alg.ImageExample
