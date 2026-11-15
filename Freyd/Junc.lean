module

public import Freyd.S2_22

section
universe v₂ u₂ v u
namespace Freyd.Alg
section Junc
variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- **B&dM 5.9**: the junc (case) morphism `[R,S] : s ⟶ c` induced by a coproduct
    `C : Coproduct s a₁ a₂` together with `R : a₁ ⟶ c`, `S : a₂ ⟶ c`, in Freyd's diagram order:
    `[R,S] = (u₁°≫R) ∪ (u₂°≫S)`. -/
@[expose] public def junc {s a₁ a₂ c : 𝒜} (C : Coproduct s a₁ a₂) (R : a₁ ⟶ c) (S : a₂ ⟶ c) : s ⟶ c :=
  (C.u₁° ≫ R) ∪ (C.u₂° ≫ S)

end Junc
end Freyd.Alg
end
