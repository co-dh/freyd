/-
  Freyd & Scedrov, *Categories and Allegories* §1.596.

  BOOK: "For any small `𝒜`, `A(𝒮^𝒜)` is isomorphic to `(A(𝒮))^𝒜` — that is, the category
  of functors from `𝒜` to `𝒜b`."

  Read: an internal ABELIAN-GROUP OBJECT in the functor category `𝒮^𝒜` is the SAME thing as a
  FUNCTOR from `𝒜` into the abelian-group objects of `𝒮`.  The point is that products and the
  terminator in `𝒮^𝒜` are computed POINTWISE (§1.422/1.424), so the structure maps `add`, `zero`,
  `neg` of an Ab-object in `𝒮^𝒜` are natural families whose component at `a : 𝒜` is exactly a
  pointwise Ab-structure on `F(a)`, and each transition `F(f)` is an Ab-object homomorphism by
  naturality.  Equality of natural transformations is pointwise, so the group axioms transfer
  levelwise in both directions.  This IS the whole proof.

  This file establishes the correspondence as a bijection, at the level the repo supports:

    * OBJECT level:  `fwdFun`/`bwdFun` with round-trips `bwd_fwd`, `fwd_bwd`
                     (a bijection `Ab(𝒮^𝒜) ≃ (Ab 𝒮)^𝒜`);
    * HOM level:     `fwdHom`/`bwdHom` with round-trips `bwdHom_fwdHom`, `fwdHom_bwdHom`
                     (per pair of objects, a bijection of hom-sets),
                     plus `fwdHom` respects identity and composition (functoriality).

  Everything is levelwise / componentwise, so all four group axioms and both round-trips are
  either `rfl` (structure-eta + proof-irrelevance) or a `NaturalTransformation.ext'` reducing to
  the corresponding fact in `𝒮` / `Ab(𝒮)`.

  Single universe `u` for objects and homs: the book's `𝒮` is the topos of sets and `𝒜` is small,
  and — because `Ab(𝒮) : Type (max u v)` while `𝒮 : Type u` — the two functor categories `𝒮^𝒜`
  and `(Ab 𝒮)^𝒜` only sit in a common universe when `v = u`.  Composition is diagram order.

  Reuses: `AbelianGroupObject`, `IsHomAbelianGroupObject`, `HomAb`, `instCatAb` (§1.595),
  `hom_preserves_zero`/`hom_preserves_neg` (§1.594/1.595), and the pointwise terminator/products
  of `𝒮^𝒜` (§1.422).
-/

module

public import Freyd.S1_422_FunctorCategory
public import Freyd.S1_595_AbRegular

open Freyd

universe u

namespace Freyd.AbFun

variable {𝒜 𝒮 : Type u} [Cat.{u} 𝒜] [Cat.{u} 𝒮] [HasTerminal 𝒮] [HasBinaryProducts 𝒮]

/-! ## Forward direction  `Ab(𝒮^𝒜) → (Ab 𝒮)^𝒜`

  An `AbelianGroupObject (Functor 𝒜 𝒮)` is a functor `G.carrier : 𝒜 → 𝒮` with natural
  structure maps.  Evaluating everything at `a : 𝒜` gives an `AbelianGroupObject 𝒮`, and every
  transition `G.carrier.map f` is a homomorphism (naturality of `G.add`). -/

/-- The pointwise Ab-object at `a : 𝒜` of an Ab-object `G` in `𝒮^𝒜`.  Carrier `G.carrier.obj a`;
    the structure maps are the `a`-components of `G`'s NTs (terminator/product in `𝒮^𝒜` are
    pointwise, so the types match on the nose), and the four axioms are the `a`-components of
    `G`'s axiom equations of natural transformations. -/
def ptOb (G : AbelianGroupObject (Functor 𝒜 𝒮)) (a : 𝒜) : AbelianGroupObject 𝒮 where
  carrier   := G.carrier.obj a
  zero      := G.zero.app a
  neg       := G.neg.app a
  add       := G.add.app a
  add_zero  := congrFun (congrArg NaturalTransformation.app G.add_zero) a
  add_neg   := congrFun (congrArg NaturalTransformation.app G.add_neg) a
  add_assoc := congrFun (congrArg NaturalTransformation.app G.add_assoc) a
  add_comm  := congrFun (congrArg NaturalTransformation.app G.add_comm) a

/-- Each transition `G.carrier.map f` is an Ab-object homomorphism `ptOb G a → ptOb G b`.
    This is exactly the naturality square of the NT `G.add`, read backwards
    (`(F×F).map f` unfolds pointwise to `⟨fst ≫ F.map f, snd ≫ F.map f⟩`). -/
theorem ptOb_isHom (G : AbelianGroupObject (Functor 𝒜 𝒮)) {a b : 𝒜} (f : a ⟶ b) :
    IsHomAbelianGroupObject (ptOb G a) (ptOb G b) (G.carrier.map f) :=
  (G.add.naturality f).symm

/-- §1.596 forward map: `G ↦ (a ↦ ptOb G a)`, a functor `𝒜 → Ab(𝒮)`. -/
def fwdFun (G : AbelianGroupObject (Functor 𝒜 𝒮)) : Functor 𝒜 (AbelianGroupObject 𝒮) where
  obj a := ptOb G a
  map      := fun {_ _} f => ⟨G.carrier.map f, ptOb_isHom G f⟩
  map_id   := fun a => Subtype.ext (G.carrier.map_id a)
  map_comp := fun f g => Subtype.ext (G.carrier.map_comp f g)

/-! ## Backward direction  `(Ab 𝒮)^𝒜 → Ab(𝒮^𝒜)`

  A functor `H : 𝒜 → Ab(𝒮)` gives a functor `bwdCarrier H : 𝒜 → 𝒮` (forget the group structure
  at each level) and three natural transformations assembled from the levelwise structure maps.
  Naturality of `add` is precisely the homomorphism condition of `H.map f`; naturality of `zero`
  and `neg` is `hom_preserves_zero`/`hom_preserves_neg` (§1.594/1.595). -/

/-- Underlying `𝒮`-functor of `H : 𝒜 → Ab(𝒮)`: `a ↦ (H a).carrier`, `f ↦ (H f).val`.
    Functoriality is `H`'s, projected to carriers (`ab_id_val`/`ab_comp_val`). -/
def bwdCarrier (H : Functor 𝒜 (AbelianGroupObject 𝒮)) : Functor 𝒜 𝒮 where
  obj a := (H.obj a).carrier
  map      := fun {_ _} f => (H.map f).val
  map_id   := fun a => congrArg Subtype.val (H.map_id a)
  map_comp := fun f g => congrArg Subtype.val (H.map_comp f g)

/-- Levelwise zero as an NT `1 ⟶ bwdCarrier H`.  Naturality = `H.map f` preserves zero. -/
def bwdZero (H : Functor 𝒜 (AbelianGroupObject 𝒮)) :
    (one : Functor 𝒜 𝒮) ⟶ bwdCarrier H where
  app a := (H.obj a).zero
  naturality {a b} f := by
    have h := hom_preserves_zero (H.map f).property (term (one : 𝒮))
    rw [term_uniq (term (one : 𝒮)) (Cat.id one), Cat.id_comp, Cat.id_comp] at h
    show Cat.id one ≫ (H.obj b).zero = (H.obj a).zero ≫ (H.map f).val
    rw [Cat.id_comp, h]

/-- Levelwise negation as an NT `bwdCarrier H ⟶ bwdCarrier H`.  Naturality = `H.map f`
    preserves negation (`hom_preserves_neg`). -/
def bwdNeg (H : Functor 𝒜 (AbelianGroupObject 𝒮)) :
    bwdCarrier H ⟶ bwdCarrier H where
  app a := (H.obj a).neg
  naturality {a b} f := by
    have h := hom_preserves_neg (H.map f).property (Cat.id (H.obj a).carrier)
    rw [Cat.id_comp, Cat.id_comp] at h
    exact h.symm

/-- Levelwise addition as an NT `bwdCarrier H × bwdCarrier H ⟶ bwdCarrier H`.  Naturality is
    exactly the homomorphism condition of `H.map f` (`(F×F).map f` unfolds pointwise). -/
def bwdAdd (H : Functor 𝒜 (AbelianGroupObject 𝒮)) :
    prod (bwdCarrier H) (bwdCarrier H) ⟶ bwdCarrier H where
  app a := (H.obj a).add
  naturality {_a _b} f := (H.map f).property.symm

/-- §1.596 backward map: assemble a functor `H : 𝒜 → Ab(𝒮)` into an Ab-object of `𝒮^𝒜`.
    The four group axioms hold as equations of NTs, checked componentwise where they become the
    axioms of the levelwise Ab-objects `H a` (`NaturalTransformation.ext'`). -/
def bwdFun (H : Functor 𝒜 (AbelianGroupObject 𝒮)) :
    AbelianGroupObject (Functor 𝒜 𝒮) where
  carrier   := bwdCarrier H
  zero      := bwdZero H
  neg       := bwdNeg H
  add       := bwdAdd H
  add_zero  := NaturalTransformation.ext' fun a => (H.obj a).add_zero
  add_neg   := NaturalTransformation.ext' fun a => (H.obj a).add_neg
  add_assoc := NaturalTransformation.ext' fun a => (H.obj a).add_assoc
  add_comm  := NaturalTransformation.ext' fun a => (H.obj a).add_comm

/-! ## The two maps are mutually inverse — object-level bijection `Ab(𝒮^𝒜) ≃ (Ab 𝒮)^𝒜`

  Both round-trips are `rfl`: reconstructing the data reproduces every field up to structure-eta
  and function-eta, and the proof fields are irrelevant. -/

/-- §1.596: `bwdFun ∘ fwdFun = id` on Ab-objects of `𝒮^𝒜`. -/
theorem bwd_fwd (G : AbelianGroupObject (Functor 𝒜 𝒮)) : bwdFun (fwdFun G) = G := rfl

/-- §1.596: `fwdFun ∘ bwdFun = id` on functors `𝒜 → Ab(𝒮)`. -/
theorem fwd_bwd (H : Functor 𝒜 (AbelianGroupObject 𝒮)) : fwdFun (bwdFun H) = H := rfl

/-! ## Hom-level correspondence  `HomAb G₁ G₂ ≃ FunctorHom (fwdFun G₁) (fwdFun G₂)`

  A homomorphism of Ab-objects in `𝒮^𝒜` is a natural transformation `φ` of the carrier functors
  whose homomorphism square is an equation of NTs; componentwise this is a natural family of
  levelwise Ab-object homomorphisms — i.e. a morphism of `(Ab 𝒮)^𝒜`.  The two directions just
  transpose "component of a NT with a global equation" and "natural family of pointwise homs". -/

variable {G₁ G₂ G₃ : AbelianGroupObject (Functor 𝒜 𝒮)}

/-- Forward on homs: the NT `φ` becomes the family `a ↦ φ.app a` of levelwise homomorphisms.
    Pointwise homomorphism = `a`-component of `φ`'s homomorphism square; naturality in `Ab(𝒮)` =
    `φ`'s naturality (carriers agree). -/
def fwdHom (φ : HomAb G₁ G₂) : FunctorHom (fwdFun G₁) (fwdFun G₂) where
  app a := ⟨φ.val.app a, congrFun (congrArg NaturalTransformation.app φ.property) a⟩
  naturality {_a _b} f := Subtype.ext (φ.val.naturality f)

/-- Backward on homs: a natural family `ψ` of levelwise homs is the NT `a ↦ (ψ.app a).val`,
    whose homomorphism square holds componentwise (each `ψ.app a` is a levelwise hom). -/
def bwdHom (ψ : FunctorHom (fwdFun G₁) (fwdFun G₂)) : HomAb G₁ G₂ :=
  ⟨{ app        := fun a => (ψ.app a).val
     naturality := fun {_ _} f => congrArg Subtype.val (ψ.naturality f) },
   NaturalTransformation.ext' fun a => (ψ.app a).property⟩

/-- §1.596 hom bijection, round-trip 1: `bwdHom ∘ fwdHom = id`. -/
theorem bwdHom_fwdHom (φ : HomAb G₁ G₂) : bwdHom (fwdHom φ) = φ := rfl

/-- §1.596 hom bijection, round-trip 2: `fwdHom ∘ bwdHom = id`. -/
theorem fwdHom_bwdHom (ψ : FunctorHom (fwdFun G₁) (fwdFun G₂)) : fwdHom (bwdHom ψ) = ψ := rfl

/-! ## Functoriality of the hom correspondence

  `fwdFun` (on objects) together with `fwdHom` (on homs) preserves identity and composition, so it
  is a functor `Ab(𝒮^𝒜) → (Ab 𝒮)^𝒜`.  Being bijective on objects (`bwd_fwd`/`fwd_bwd`) and on every
  hom-set (`bwdHom_fwdHom`/`fwdHom_bwdHom`), it is an ISOMORPHISM of categories — the full §1.596. -/

/-- `fwdHom` preserves identities (`Cat.id` in `Ab(𝒮^𝒜)` ↦ `natTrans_id` in `(Ab 𝒮)^𝒜`). -/
theorem fwdHom_id (G : AbelianGroupObject (Functor 𝒜 𝒮)) :
    fwdHom (Cat.id G) = natTrans_id (fwdFun G) := rfl

/-- `fwdHom` preserves composition (`≫` in `Ab(𝒮^𝒜)` ↦ `natTrans_comp` in `(Ab 𝒮)^𝒜`).
    (Args typed as `G₁ ⟶ G₂` — syntactically `Cat.Hom` — so `≫` resolves the `Ab(𝒮^𝒜)` instance.) -/
theorem fwdHom_comp (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃) :
    fwdHom (φ ≫ ψ) = natTrans_comp (fwdHom φ) (fwdHom ψ) := rfl

end Freyd.AbFun
