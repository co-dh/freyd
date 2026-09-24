/-
  §5.4's power relator against the existential image, on one concrete relation `R : A → B`, with
  `A = {1,2,3}` and `B = {a,b,c}`.  The note's picture of `R` is drawn from `R` itself by
  `diag-export --graph`, which lists the constructors of `A` and `B` and decides every pair.
-/
module

public import Freyd.S2_30_Example

@[expose] public section

namespace Freyd.Alg.ImageExample

open Freyd.S2_30.Example (Listed)

inductive A | «1» | «2» | «3» deriving DecidableEq
inductive B | a | b | c deriving DecidableEq

instance : Listed B := ⟨[.a, .b, .c], fun e => by cases e <;> decide⟩

/-- `n R t`: the relation of the example — `1` to `a` and `b`, `3` to `c`, and `2` to nothing. -/
def R (n : A) (t : B) : Prop :=
  (n, t) ∈ ([(.«1», .a), (.«1», .b), (.«3», .c)] : List (A × B))

instance : DecidableRel R := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

/-- `R(2) = ∅`: the one element of `A` with the empty image. -/
theorem R_two_empty : ∀ t, ¬ R .«2» t := by decide

end Freyd.Alg.ImageExample
