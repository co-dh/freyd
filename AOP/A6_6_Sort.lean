/-
  Bird & de Moor, *Algebra of Programming* §6.6 (pp. 151-155), shared prerequisite: coreflexives
  are symmetric.  The sorting derivations themselves are point-free in `A6_6b_SortConcrete`
  (selection sort), `A6_6e_Quicksort` (quicksort).
-/
module

public import AOP.A5_6_ListCombinators -- shake: keep

namespace Freyd.Alg.RelSet.Sort

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

variable {A : Type}

/-- Coreflexives in `Rel(Set)` are symmetric: `R ⊑ id ⟹ R° = R`. -/
public theorem coref_recip {A : RelSet.{0}} {R : A ⟶ A} (h : R ⊑ Cat.id A) : R° = R :=
  symmetric_eq (coreflexive_symmetric_idempotent h).1

end Freyd.Alg.RelSet.Sort
