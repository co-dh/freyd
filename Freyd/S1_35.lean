/-
  Freyd & Scedrov, *Categories and Allegories* §1.35, §1.243
  Forgetful functor, founded category, concrete category, underlying set functor.
-/


import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_31
import Freyd.S1_55


open Freyd

universe v u u₂ v₂ w

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.35 Forgetful functor

  If A is founded on B (§1.243), the FORGETFUL FUNCTOR U : A → B
  sends objects A ∈ A to |A| ∈ B and morphisms A → B in A to x in B.
  U is always an embedding. -/

/-- The forgetful functor.  Takes an object mapping `|·| : 𝒜 → ℬ` and a morphism
    mapping that forgets structure.  Always an embedding.  (The book's "forgetful
    functor" is defined by a foundation; we capture the general property.) -/
structure ForgetfulFunctor (𝒜 : Type u) (ℬ : Type u) [Cat.{v} 𝒜] [Cat.{v} ℬ] where
  obj    : 𝒜 → ℬ
  map    : {X Y : 𝒜} → (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id : ∀ X : 𝒜, map (Cat.id X) = Cat.id (obj X)
  map_comp : ∀ {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g
  isEmbedding : ∀ {X Y : 𝒜} (f g : X ⟶ Y), map f = map g → f = g

/-- The forgetful functor yields a `Functor` (as defined in §1.18). -/
instance {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] (U : ForgetfulFunctor 𝒜 ℬ) : Functor U.obj where
  map := U.map
  map_id := U.map_id
  map_comp := U.map_comp

/-! ## §1.243 Founded categories and concrete categories

  §1.243: A category A is FOUNDED on B when it is constructed from B by
  - specifying a class of objects equipped with an underlying-object map `|·| : 𝒜 → ℬ`,
  - taking B's morphisms as proto-morphisms with a source-target predicate, and
  - verifying identities and composition close.
  The functor U : A → B (A ↦ |A|, f ↦ f) is always faithful.

  A CONCRETE CATEGORY is one founded on 𝒴 (the category of Sets §1.241).
  The forgetful functor in the concrete case is called the UNDERLYING SET FUNCTOR. -/

/-- §1.243  A is FOUNDED on B: a faithful functor `𝒜 → ℬ` witnesses the foundation.
    `obj` is the underlying-object map `|·| : 𝒜 → ℬ`; `faithful` is injectivity on homs. -/
structure Founded (𝒜 : Type u) (ℬ : Type u₂) [Cat.{v} 𝒜] [Cat.{v₂} ℬ] where
  obj      : 𝒜 → ℬ
  map      : {X Y : 𝒜} → (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id   : ∀ X : 𝒜, map (Cat.id X) = Cat.id (obj X)
  map_comp : ∀ {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g
  faithful : ∀ {X Y : 𝒜} (f g : X ⟶ Y), map f = map g → f = g

/-- §1.243  A CONCRETE CATEGORY: a category 𝒜 founded on 𝒴 = Sets.
    `w` is the universe of underlying sets; hom-sets are functions (universe `w`). -/
def ConcreteCat (𝒜 : Type u) [Cat.{v} 𝒜] : Type _ :=
  Founded 𝒜 (Type w)

/-- §1.35 / §1.243  The UNDERLYING SET FUNCTOR of a concrete category.
    Sends A ∈ 𝒜 to its underlying set |A| ∈ Sets and each morphism to itself. -/
def underlyingSetFunctor {𝒜 : Type u} [Cat.{v} 𝒜]
    (C : ConcreteCat 𝒜) : Founded 𝒜 (Type w) := C

/-! ## §1.243 Founding as a CONSTRUCTION

  `Founded`/`ForgetfulFunctor` above record the *result* of founding (a faithful `𝒜 → ℬ`).
  §1.243 itself is a *construction*: choose a class `𝒞` of objects, an underlying-object function
  `u : 𝒞 → ℬ` (its value `u A = |A|` is the underlying `ℬ`-object of `A`), reuse `ℬ`'s morphisms as
  *proto-morphisms*, and keep exactly those satisfying a *source-target predicate* `Hom'` (closed
  under identities and composition).  This data builds a category on `𝒞`. -/

/-- §1.243  FOUNDING DATA on a base `ℬ`. `u A = |A|` is the underlying object; `Hom' x` says the
    proto-morphism `x : |A| ⟶ |B|` counts as one of the morphisms `A ⟶ B`. -/
structure FoundingData (ℬ : Type u₂) [Cat.{v₂} ℬ] (𝒞 : Type u) where
  u        : 𝒞 → ℬ
  Hom'     : {A B : 𝒞} → (u A ⟶ u B) → Prop
  id_mem   : ∀ A, Hom' (Cat.id (u A))
  comp_mem : ∀ {A B D : 𝒞} {x : u A ⟶ u B} {y : u B ⟶ u D}, Hom' x → Hom' y → Hom' (x ≫ y)

namespace FoundingData
variable {ℬ : Type u₂} [Cat.{v₂} ℬ] {𝒞 : Type u}

/-- §1.243  The category on `𝒞` FOUNDED on `ℬ` by `F`: a morphism `A ⟶ B` is a proto-morphism
    `x : |A| ⟶ |B|` with `F.Hom' x`; identities, composition and the three axioms come from `ℬ`
    (a founded morphism is determined by its underlying proto-morphism). -/
def cat (F : FoundingData ℬ 𝒞) : Cat.{v₂} 𝒞 where
  Hom A B := { x : F.u A ⟶ F.u B // F.Hom' x }
  id A := ⟨Cat.id (F.u A), F.id_mem A⟩
  comp f g := ⟨f.1 ≫ g.1, F.comp_mem f.2 g.2⟩
  id_comp f := Subtype.ext (Cat.id_comp f.1)
  comp_id f := Subtype.ext (Cat.comp_id f.1)
  assoc f g h := Subtype.ext (Cat.assoc f.1 g.1 h.1)

/-- §1.35  The forgetful functor of the founding is faithful: a founded morphism is determined by
    its underlying proto-morphism. -/
theorem forget_faithful (F : FoundingData ℬ 𝒞) {A B : 𝒞}
    (f g : { x : F.u A ⟶ F.u B // F.Hom' x }) (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/-- §1.36  The INFLATION of `ℬ` along an underlying map `u : 𝒞 → ℬ` is the founding with the *most
    inclusive* predicate — every proto-morphism counts (`Hom' = fun _ => True`), so
    `(A ⟶ B) ≃ (|A| ⟶ |B|)` and `[u].cat ≃ ℬ` (objects merely replicated). -/
def inflation (u : 𝒞 → ℬ) : FoundingData ℬ 𝒞 where
  u := u
  Hom' := fun _ => True
  id_mem := fun _ => trivial
  comp_mem := fun _ _ => trivial

end FoundingData

end Freyd
