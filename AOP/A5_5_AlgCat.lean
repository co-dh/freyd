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

/-- The LIFT of `F` to `Alg(F)`: `F̃(X) = ⟨F(X.carrier), F(X.α)⟩` on objects, `F̃(f) = F(f.h)`
    on arrows.  The `comm` obligation of `F̃(f)` is `F` applied to `f.comm`, so it is exactly
    `F.map_comp` on both sides of that square.

    The repo's `Freyd.Functor` structure is used as-is: its class signature asks only for a
    `Cat` on either side, which `instCatFAlg` supplies — it does not demand an allegory. -/
@[expose] public def liftRelator (F : Relator 𝒜 𝒜) : Freyd.Functor (FAlg F) (FAlg F) where
  obj X := ⟨F.obj X.carrier, F.map X.α⟩
  map := fun {X Y} f => ⟨F.map f.h, by rw [← F.map_comp X.α f.h, f.comm, F.map_comp]⟩
  map_id X := FHom.ext (F.map_id X.carrier)
  map_comp f g := FHom.ext (F.map_comp f.h g.h)

/-- The COMPONENT of `α` at `X`, as an arrow `F̃(X) ⟶ X` of `Alg(F)`.  Its `comm` obligation
    is `F.map X.α ≫ X.α = F.map X.α ≫ X.α`: the structure map is a homomorphism from the
    lifted algebra to the algebra itself, on the nose. -/
@[expose] public def alphaComp {F : Relator 𝒜 𝒜} (X : FAlg F) : (liftRelator F).obj X ⟶ X :=
  ⟨X.α, rfl⟩

/-- NATURALITY of `α` on `Alg(F)`: `α_X ≫ f = F̃(f) ≫ α_Y` for every homomorphism `f`.
    The proof is `f.comm` under `FHom.ext` — the square holds by construction of `Alg(F)`'s
    arrows, which is the whole content of the statement. -/
public theorem alpha_natural_alg {F : Relator 𝒜 𝒜} {X Y : FAlg F} (f : X ⟶ Y) :
    alphaComp X ≫ f = (liftRelator F).map f ≫ alphaComp Y :=
  FHom.ext f.comm

end Freyd.Alg
