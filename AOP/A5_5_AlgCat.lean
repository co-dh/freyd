/-
  Bird & de Moor, *Algebra of Programming* §5.5 — the CATEGORY of `F`-algebras, and the
  structure map as a natural transformation on it.

  An `F`-algebra's structure map `α` is NOT a natural transformation `F ⇒ Id` on the
  underlying allegory `𝒜`: the square `α_A ≫ h = F(h) ≫ α_B` is the HOMOMORPHISM condition,
  and it fails for a general `h : A ⟶ B`.  That failure is already settled — see
  `Freyd.Alg.RelSet.Carrier.listAlg_not_lax_natural` in `AOP.A7_4_CarrierBeads`, which
  exhibits a concrete `h` breaking it even laxly.  It is NOT reproved here.

  What IS true is the statement this file formalises: once the arrows are cut down to the
  ones that satisfy that square — i.e. once we pass to `Alg(F)`, whose objects are algebras
  and whose arrows are homomorphisms — and `F` is lifted to `Alg(F)` by
  `F̃(X) = ⟨F(X.carrier), F(X.α)⟩`, the family `α` becomes a natural transformation
  `F̃ ⇒ Id` on `Alg(F)`.  Naturality is then true BY CONSTRUCTION: `alpha_natural_alg` is
  literally the `comm` field of the arrow it is given.

  All composition is diagram order (Freyd `≫`), mirroring B&dM's `·`.
-/
module

public import AOP.A5_1

universe v₁ u₁

namespace Freyd.Alg

variable {𝒜 : Type u₁} [Allegory.{v₁} 𝒜]

/-- An `F`-ALGEBRA: a carrier object together with a structure map `F(carrier) ⟶ carrier`.
    The map is an arbitrary arrow of `𝒜` — a relation, not necessarily a map. -/
public structure FAlg (F : Relator 𝒜 𝒜) where
  carrier : 𝒜
  α : F.obj carrier ⟶ carrier



/-- An `F`-ALGEBRA HOMOMORPHISM: an arrow of `𝒜` between the carriers making the square
    `X.α ≫ h = F(h) ≫ Y.α` commute.  This square is the homomorphism condition; it is the
    very condition that fails for a general arrow, and requiring it is what makes `α`
    natural below. -/
public structure FHom {F : Relator 𝒜 𝒜} (X Y : FAlg F) where
  h : X.carrier ⟶ Y.carrier
  comm : X.α ≫ h = F.map h ≫ Y.α

/-- Two homomorphisms with the same underlying arrow are equal: `comm` is a `Prop`, so
    proof irrelevance settles the second field. -/
public theorem FHom.ext {F : Relator 𝒜 𝒜} {X Y : FAlg F} {f g : FHom X Y} (e : f.h = g.h) : f = g := by
  cases f; cases g; cases e; rfl

/-- `Alg(F)`, the category of `F`-algebras and their homomorphisms.  Identities need
    `F.map_id`; composition is the two homomorphism squares pasted, which needs
    `F.map_comp`.  The three category axioms are the `𝒜` ones under `FHom.ext`. -/
public instance instCatFAlg {F : Relator 𝒜 𝒜} : Cat.{v₁} (FAlg F) where
  Hom X Y := FHom X Y
  id X := ⟨𝟙 X.carrier, by rw [Cat.comp_id, F.map_id, Cat.id_comp]⟩
  comp f g := ⟨f.h ≫ g.h, by
    rw [← Cat.assoc, f.comm, Cat.assoc, g.comm, ← Cat.assoc, ← F.map_comp]⟩
  id_comp f := FHom.ext (Cat.id_comp f.h)
  comp_id f := FHom.ext (Cat.comp_id f.h)
  assoc f g h := FHom.ext (Cat.assoc f.h g.h h.h)

end Freyd.Alg
