/-
  Freyd & Scedrov, *Categories and Allegories* §1.26  The slice category A/B.

  Over (§1.26): objects of A/B are maps into B (a pair ⟨X, h : X → B⟩).
  OverHom: morphisms are commuting triangles.
  overCat: the slice category as a `Cat` instance.
  OverMono: monic in the slice category.
  OverIso: isomorphism in A/B.
  overIso_iff: iso in A/B ↔ underlying map is iso in A.
  Under (§1.263): the counter-slice category B\A (dual: maps out of B).
  UnderHom, underCat, UnderMono: counter-slice structure.
  Composition `⊚` is explicit (avoids `Cat` instance issues for `Over B`).

  §1.261 (sets/augmented rings) and §1.262 (local homeomorphisms/Lazard sheaves)
  are informal examples requiring topology/ring infrastructure — recorded as MISSING.
-/

import Freyd.S1_1
import Freyd.S1_41

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

structure Over (B : 𝒞) where
  dom : 𝒞
  hom : dom ⟶ B

structure OverHom {B : 𝒞} (X Y : Over B) where
  f : X.dom ⟶ Y.dom
  w : f ≫ Y.hom = X.hom

@[ext]
theorem OverHom.ext {B : 𝒞} {X Y : Over B} {a b : OverHom X Y} (h : a.f = b.f) : a = b := by
  obtain ⟨af, aw⟩ := a; obtain ⟨bf, bw⟩ := b; subst h; rfl

/-- Composition in A/B (explicit, bypasses `Cat` instance). -/
def OverHom.comp {B : 𝒞} {X Y Z : Over B} (h : OverHom X Y) (k : OverHom Y Z) : OverHom X Z :=
  ⟨h.f ≫ k.f, by rw [Cat.assoc, k.w, h.w]⟩

infixr:80 (name := overHomComp) " ⊚ " => OverHom.comp

/-- The slice category A/B as a `Cat` instance.  Composition is `⊚`, identity
    is the pair `(id_dom, id_comp B)`. -/
instance overCat (B : 𝒞) : Cat.{v} (Over B) where
  Hom := OverHom
  id X := ⟨Cat.id X.dom, Cat.id_comp X.hom⟩
  comp f g := f ⊚ g
  id_comp f := OverHom.ext (Cat.id_comp f.f)
  comp_id f := OverHom.ext (Cat.comp_id f.f)
  assoc f g h := OverHom.ext (Cat.assoc f.f g.f h.f)

/-- Monic in A/B (via the Over category's `Cat` instance).  `OverMono m` iff
    `m` is monic in the slice category. -/
abbrev OverMono {B : 𝒞} {Z Y : Over B} (m : OverHom Z Y) : Prop := @Monic (Over B) _ Z Y m

/-- Iso in A/B: `OverIso m` iff `m` is an isomorphism in the slice category. -/
abbrev OverIso {B : 𝒞} {X Y : Over B} (m : OverHom X Y) : Prop := @IsIso (Over B) _ X Y m

/-- An iso in A/B unfolds to: there exists an inverse OverHom with the two triangle equations. -/
theorem overIso_iff {B : 𝒞} {X Y : Over B} (m : OverHom X Y) :
    OverIso m ↔ ∃ (inv : OverHom Y X),
      m ⊚ inv = @Cat.id (Over B) _ X ∧ inv ⊚ m = @Cat.id (Over B) _ Y := by
  simp only [OverIso, IsIso]; rfl

/-- If `m : OverHom X Y` is iso in A/B then the underlying `m.f` is iso in A. -/
theorem overIso_underlying {B : 𝒞} {X Y : Over B} {m : OverHom X Y} (hm : OverIso m) :
    IsIso m.f :=
  let ⟨inv, h1, h2⟩ := hm
  ⟨inv.f, congrArg OverHom.f h1, congrArg OverHom.f h2⟩

/-- Converse: if the underlying `m.f` is iso in A and `m` is an over-hom, then `m` is iso in A/B. -/
theorem overIso_of_underlying {B : 𝒞} {X Y : Over B} (m : OverHom X Y) (hf : IsIso m.f) :
    OverIso m :=
  let ⟨inv_f, h1, h2⟩ := hf
  -- inv_f ≫ X.hom = Y.hom follows from m.w: m.f ≫ Y.hom = X.hom
  -- apply inv_f on left: inv_f ≫ m.f ≫ Y.hom = inv_f ≫ X.hom → Y.hom = inv_f ≫ X.hom
  have inv_w : inv_f ≫ X.hom = Y.hom := by
    have := congrArg (inv_f ≫ ·) m.w
    simp only [← Cat.assoc, h2, Cat.id_comp] at this
    exact this.symm
  ⟨⟨inv_f, inv_w⟩, OverHom.ext h1, OverHom.ext h2⟩

/-! ## §1.263  Counter-slice category B\A (dual of slice) -/

/-- Objects of the counter-slice B\A: maps out of B (pairs ⟨X, h : B → X⟩). -/
structure Under (B : 𝒞) where
  cod : 𝒞
  hom : B ⟶ cod

/-- Morphisms of B\A: commuting co-triangles.  `f : UnderHom X Y` is an arrow
    `f.f : X.cod → Y.cod` such that `X.hom ≫ f.f = Y.hom`. -/
structure UnderHom {B : 𝒞} (X Y : Under B) where
  f : X.cod ⟶ Y.cod
  w : X.hom ≫ f = Y.hom

@[ext]
theorem UnderHom.ext {B : 𝒞} {X Y : Under B} {a b : UnderHom X Y} (h : a.f = b.f) : a = b := by
  obtain ⟨af, aw⟩ := a; obtain ⟨bf, bw⟩ := b; subst h; rfl

/-- Composition in B\A. -/
def UnderHom.comp {B : 𝒞} {X Y Z : Under B} (h : UnderHom X Y) (k : UnderHom Y Z) :
    UnderHom X Z :=
  ⟨h.f ≫ k.f, by rw [← Cat.assoc, h.w, k.w]⟩

infixr:80 (name := underHomComp) " ⊛ " => UnderHom.comp

/-- The counter-slice category B\A as a `Cat` instance. -/
instance underCat (B : 𝒞) : Cat.{v} (Under B) where
  Hom := UnderHom
  id X := ⟨Cat.id X.cod, Cat.comp_id X.hom⟩
  comp f g := f ⊛ g
  id_comp f := UnderHom.ext (Cat.id_comp f.f)
  comp_id f := UnderHom.ext (Cat.comp_id f.f)
  assoc f g h := UnderHom.ext (Cat.assoc f.f g.f h.f)

/-- Monic in B\A. -/
abbrev UnderMono {B : 𝒞} {Z Y : Under B} (m : UnderHom Z Y) : Prop := @Monic (Under B) _ Z Y m

end Freyd
