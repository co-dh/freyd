/-
  Bird & de Moor, *Algebra of Programming* §5.5 — the HOMOMORPHISM CONDITION of `F`-algebras,
  unbundled.

  An `F`-algebra's structure map `α` is NOT a natural transformation `F ⇒ Id` on the
  underlying allegory `𝒜`: the square `α_A ≫ h = F(h) ≫ α_B` is the HOMOMORPHISM condition,
  and it fails for a general `h : A ⟶ B`.  That failure is already settled — see
  `Freyd.Alg.RelSet.Carrier.listAlg_not_lax_natural` in `AOP.A7_4_CarrierBeads`, which
  exhibits a concrete `h` breaking it even laxly.  It is NOT reproved here.

  The bundled algebra and the category of algebras and homomorphisms are `Algebra`, `AlgHom` and
  `instCatAlgebra` in `AOP.A5_5`; this file keeps only the square itself, free in its three arrows.

  All composition is diagram order (Freyd `≫`), mirroring B&dM's `·`.
-/
module

public import AOP.A5_1

universe v₁ u₁

namespace Freyd.Alg

variable {𝒜 : Type u₁} [Allegory.{v₁} 𝒜]

/-- The HOMOMORPHISM CONDITION, UNBUNDLED: `h : A ⟶ B` carries the algebra `f : F(A) ⟶ A` to
    `g : F(B) ⟶ B` when `f h = F(h) g`.  Free in all three arrows — which is what the square
    says, and what a picture of it draws: three named arrows, none of them a projection of a
    bundled pair.
    Reducible because the name is all it adds: `rw [φ.comm]` has to see the `Eq` through it. -/
@[reducible, expose] public def IsFHom {F : Relator 𝒜 𝒜} {A B : 𝒜}
    (f : F.obj A ⟶ A) (g : F.obj B ⟶ B) (h : A ⟶ B) : Prop := f ≫ h = F.map h ≫ g

end Freyd.Alg

-- printing-only: `IsFHom f g h` is the note's `h : f⟶g`, an arrow of `Alg(F)` from the algebra `f`
-- to the algebra `g`, which a type ascription already spells.
namespace Freyd.Alg
open Lean PrettyPrinter in
@[app_unexpander IsFHom] public meta def unexpandIsFHom : Unexpander
  | `($_ $f $g $h) => `(($h : $f ⟶ $g))
  | _ => throw ()
end Freyd.Alg
