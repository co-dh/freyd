/-
  Freyd & Scedrov, *Categories and Allegories* §1.27  Small category, functor category,
  natural transformation (§1.27), right A-sets (§1.271), Cayley representation (§1.272),
  left A-sets (§1.273), natural equivalence (§1.274).

  §1.27  NaturalTransformation: a family α_X : F X → G X with naturality squares.
  §1.271 Right A-set = covariant functor A → Y.  In the single-sorted language this is
         a set X with a unary operation to |A| (the "source" map) and a partial binary
         operation x a defined iff source(x) = □a, satisfying the monoid-action laws.
  §1.272 CAYLEY REPRESENTATION: a small category A is a right A-set whose carriers
         are C(A) = {x | □x = A} (morphisms targeting A).  For f : A → B, C(f)(y) = y f.
         C is one-to-one (faithful): if C(f) = C(g) then f = g, taking y = A (id_A).
         In the object-centric setting: post-composition h ↦ h ≫ f faithfully encodes f
         because id_A ≫ f = f distinguishes f from any g ≠ f.
  §1.273 Left A-set = contravariant version: right A^op-set (§1.273).
  §1.274 Natural equivalence = natural transformation with iso components (§1.274).
-/

import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_41


universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.27  Natural transformation -/

/-- A natural transformation α : F → G between parallel functors F, G : 𝒞 → 𝒟 (§1.27).
    For each X : 𝒞 a component α_X : F X → G X; for every f : X → Y,
    F(f) ≫ α_Y = α_X ≫ G(f) (naturality). -/
structure NaturalTransformation (F G : Functor 𝒞 𝒟) where
  app : (X : 𝒞) → (F.obj X ⟶ G.obj X)
  naturality : ∀ {X Y : 𝒞} (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

infix:25 " ⟹ " => NaturalTransformation

/-! ## §1.274  Natural equivalence (isomorphism in the functor category) -/

/-- A natural equivalence (§1.274): a natural transformation whose every component is
    an isomorphism.  In the functor category this is precisely an isomorphism. -/
def NaturalIso (F G : Functor 𝒞 𝒟) (α : F ⟹ G) : Prop :=
  ∀ X : 𝒞, IsIso (NaturalTransformation.app α X)

/-! ## §1.272  Cayley representation -/

section Cayley

variable {A B : 𝒞}

/-- **§1.272 Cayley representation — faithfulness**.
    In Freyd's single-sorted language: C sends A ↦ {y | □y = A}, f ↦ (y ↦ yf).
    C is one-to-one on morphisms because y = A (id_A) belongs to C(A) and A f = f.
    In the object-centric setting this translates to: if post-composition by f and g
    agree on all maps into A then f = g.  The witness is h = id_A : A → A. -/
theorem cayley_faithful (f g : A ⟶ B)
    (h : ∀ {X : 𝒞} (hX : X ⟶ A), hX ≫ f = hX ≫ g) : f = g := by
  have := h (Cat.id A)
  rwa [Cat.id_comp, Cat.id_comp] at this

/-- **§1.272 (contrapositive)**.  If f ≠ g then they are distinguished by
    some pre-composition — specifically id_A composed with each. -/
theorem cayley_faithful_contra (f g : A ⟶ B) (hne : f ≠ g) :
    ∃ (X : 𝒞) (hX : X ⟶ A), hX ≫ f ≠ hX ≫ g := by
  refine ⟨A, Cat.id A, ?_⟩
  intro h_eq
  apply hne
  rwa [Cat.id_comp, Cat.id_comp] at h_eq

end Cayley

/-! ## §1.27  Functor category 𝒟^𝒜 -/

/-- The hom-type of the functor category: natural transformations from F to G.
    Objects of the functor category 𝒟^𝒜 (§1.27) are the bundled functors `Functor 𝒜 𝒟`. -/
abbrev FunctorHom {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟]
    (F G : Functor 𝒜 𝒟) : Type (max v u) :=
  NaturalTransformation F G

/-- Extensionality for `NaturalTransformation`: two NTs with the same components
    are equal. -/
theorem NaturalTransformation.ext' {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟]
    {F G : Functor 𝒜 𝒟}
    {α β : NaturalTransformation F G}
    (h : ∀ X, α.app X = β.app X) : α = β := by
  cases α; cases β; congr 1; funext X; exact h X

/-- Identity natural transformation on F: component at each X is id_{F X}.
    Naturality: F(f) ≫ id = id ≫ F(f) by comp_id / id_comp. -/
def natTrans_id {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟]
    (F : Functor 𝒜 𝒟) : FunctorHom F F where
  app X := Cat.id (F.obj X)
  naturality f := by simp [Cat.comp_id, Cat.id_comp]

/-- Vertical composition of natural transformations α : F ⟹ G and β : G ⟹ H.
    Component: (α;β)_X = α_X ≫ β_X.  Naturality square commutes by
    α-naturality and β-naturality and associativity. -/
def natTrans_comp {𝒜 𝒟 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒟]
    {F G H : Functor 𝒜 𝒟}
    (α : FunctorHom F G) (β : FunctorHom G H) : FunctorHom F H where
  app X := α.app X ≫ β.app X
  naturality {X Y} f := by
    have hα := α.naturality f
    have hβ := β.naturality f
    -- F(f) ≫ α_Y ≫ β_Y = α_X ≫ G(f) ≫ β_Y = α_X ≫ β_X ≫ H(f)
    rw [← Cat.assoc, hα, Cat.assoc, hβ, ← Cat.assoc]

/-- The FUNCTOR CATEGORY 𝒟^𝒜 (§1.27): objects are bundled functors `Functor 𝒜 𝒟`,
    morphisms are natural transformations, identity and composition as above.
    The three category laws hold pointwise by the laws of 𝒟. -/
instance functorCat (𝒜 𝒟 : Type u) [Cat.{v} 𝒜] [Cat.{v} 𝒟] :
    Cat.{max v u} (Functor 𝒜 𝒟) where
  Hom   := FunctorHom
  id    := natTrans_id
  comp  := natTrans_comp
  id_comp α  := NaturalTransformation.ext' fun X => Cat.id_comp (α.app X)
  comp_id α  := NaturalTransformation.ext' fun X => Cat.comp_id (α.app X)
  assoc α β γ := NaturalTransformation.ext' fun X => Cat.assoc (α.app X) (β.app X) (γ.app X)

/-! ## §1.272  Cayley completeness metatheorem  — MISSING (faithful content elsewhere)

  §1.272 (Cayley completeness): every universally-quantified elementary sentence in
  the predicates of category theory that holds in the category of sets holds in every
  category.  The Cayley representation `C : 𝒞 → Set` (`A ↦ {f | cod f = A}`, post-
  composition) is faithful, embedding 𝒞 as a concrete subcategory of Set, and any such
  sentence true in Set descends to 𝒞.

  This metatheorem is NOT recorded as a single Lean theorem here.  The previous
  attempt (`cayley_completeness`, a property `P` reflected along faithful functors)
  was LOGICALLY FALSE as stated — `P := fun _ => False` satisfies the reflection
  hypothesis vacuously yet makes the conclusion `∀ f, False` unprovable: it lacked the
  essential anchor that `P` actually holds in Set.  A Sorry inside a false statement is
  a lie, so it has been removed.

  The faithful, genuinely-proved content is split across the repo:
  • the Cayley embedding is faithful — `cayley_faithful` (this file, §1.272);
  • the faithful Henkin-Lubkin representation `𝒞 ↪ 𝒮^|𝒞|` — `henkin_lubkin` (S1_55);
  • Horn-sentence reflection along a faithful, finite-limit/image-preserving functor —
    `horn_sentence_reflected_by_faithful` (S1_56, §1.563), the proven faithful version
    (the capitalization lemma §1.543 it would build on is itself now proven Sorry-free,
    `Freyd.capitalization_lemma`).
  A self-contained §1.272 metatheorem (quantifying over first-order sentences) would
  need a sentence-encoding + a `Cat` instance on `Type` with the Cayley functor; that
  is recorded as MISSING in S1_27.md. -/

end Freyd
