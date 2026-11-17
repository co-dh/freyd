/-
  The tie between Rel's concrete core and freyd's model (`doc/rel-repo-split-design.md` §4.4): a hom-set of
  `RelSet` is `Core.Rel` of the two carriers by definition, each operator of `LeetQ.Core.Rel` is the field of
  freyd's `RelSet` instance by `rfl`, and `Core.Rel.mu` is `Freyd.Alg.mu` at `RelSet`.
-/
import LeetQ.Core.Fix
import AOP.A6_1_RelSet
import AOP.A6_2

namespace LeetQ.Aop.Core

open Freyd Freyd.Alg Freyd.Alg.RelSet
open LeetQ.Core (Rel)

variable {A B C D : RelSet.{0}}

theorem id_eq : Rel.id A.carrier = 𝟙 A := rfl
theorem comp_eq (R : A ⟶ B) (S : B ⟶ C) : Rel.comp R S = R ≫ S := rfl
theorem recip_eq (R : A ⟶ B) : Rel.recip R = R° := rfl
theorem inter_eq (R S : A ⟶ B) : Rel.inter R S = R ∩ S := rfl
theorem union_eq (R S : A ⟶ B) : Rel.union R S = R ∪ S := rfl
theorem zero_eq : (Rel.zero : Rel A.carrier B.carrier) = (𝟘 : A ⟶ B) := rfl
theorem le_eq (R S : A ⟶ B) : Rel.le R S = (R ⊑ S) := rfl
theorem top_eq : (Rel.top : Rel A.carrier B.carrier) = (relTop : A ⟶ B) := rfl
theorem graph_eq (f : A.carrier → B.carrier) : Rel.graph f = (graph f : A ⟶ B) := rfl
theorem corefl_eq (P : A.carrier → Prop) : Rel.corefl P = (corefl P : A ⟶ A) := rfl
theorem rpair_eq (R : C ⟶ A) (S : C ⟶ B) : Rel.rpair R S = rpair R S := rfl
theorem rprodMap_eq (R : A ⟶ C) (S : B ⟶ D) : Rel.rprodMap R S = rprodMap R S := rfl
theorem inl_eq : (Rel.inl : Rel A.carrier (A.carrier ⊕ B.carrier)) = (sumCop A B).u₁ := rfl
theorem inr_eq : (Rel.inr : Rel B.carrier (A.carrier ⊕ B.carrier)) = (sumCop A B).u₂ := rfl
theorem junc_eq (R : A ⟶ C) (S : B ⟶ C) : Rel.junc R S = junc (sumCop A B) R S := rfl

/-- Both are the meet of the prefixed points: freyd's as an `Inf`, the core's pointwise. -/
theorem mu_eq (φ : (A ⟶ B) → (A ⟶ B)) : Rel.mu (α := A.carrier) (β := B.carrier) φ = Freyd.Alg.mu φ :=
  Rel.ext fun a b =>
    ⟨fun h => Rel.le_iff.1 (show Freyd.Alg.le (Rel.mu (α := A.carrier) (β := B.carrier) φ) (Freyd.Alg.mu φ) from
        le_Inf fun (Y : A ⟶ B) (hY : φ Y ⊑ Y) =>
          Rel.mu_le (α := A.carrier) (β := B.carrier) (φ := φ) (Y := Y) hY) a b h,
     fun h (Y : A ⟶ B) hY => Rel.le_iff.1 (Freyd.Alg.mu_le (φ := φ) (Y := Y) hY) a b h⟩

end LeetQ.Aop.Core
