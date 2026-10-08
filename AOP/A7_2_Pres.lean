/-
  Bird & de Moor, *Algebra of Programming* §7.2  Monotonic algebras: the definition alone.

  Split from `AOP.A7_2` so that a user of `Pres` (chapter 8's thinning) does not wait for the
  Greedy Theorem; `AOP.A7_2` re-exports it.
-/
module

public import AOP.A6_2

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {A : 𝒜}

/-- **B&dM p.172** (they call it a monotonic algebra, `MonoAlg`; read: `φ` preserves `R`):
    `φ` is MONOTONIC on `R` when `φ·FR ⊆ R·φ`, mirrored `F.map R ≫ φ ⊑ φ ≫ R`.
    (An algebra `φ` "does not care" whether `R`-related recursive results are computed before
    or after applying `φ`.) -/
@[expose] public def Pres (φ : F.obj A ⟶ A) (R : A ⟶ A) : Prop := F.map R ≫ φ ⊑ φ ≫ R

end Freyd.Alg
