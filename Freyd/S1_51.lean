/-
  Freyd & Scedrov, *Categories and Allegories* §1.51  Covers, regular categories.

  §1.51  Subobject, Allows, Image, Cover (§1.512), Cover factorization.
-/


import Freyd.S1_10
import Freyd.S1_18
import Freyd.S1_33
import Freyd.S1_41
import Freyd.S1_51_Order  -- §1.51 preorder-level order theory (GaloisConnection, IsSup, IsClosureOp)


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.51 Subobjects -/

/-- A subobject of B: a domain and a monic morphism into B. -/
structure Subobject (𝒞 : Type u) [Cat.{v} 𝒞] (B : 𝒞) where
  dom   : 𝒞
  arr   : dom ⟶ B
  monic : Monic arr

/-- Order on subobjects: S ≤ T if S factors through T. -/
def Subobject.le {B : 𝒞} (S T : Subobject 𝒞 B) : Prop :=
  ∃ h : S.dom ⟶ T.dom, h ≫ T.arr = S.arr

@[refl] theorem Subobject.le_refl {B : 𝒞} (S : Subobject 𝒞 B) : S.le S :=
  ⟨Cat.id S.dom, Cat.id_comp S.arr⟩

theorem Subobject.le_trans {B : 𝒞} {X Y Z : Subobject 𝒞 B}
    (h₁ : X.le Y) (h₂ : Y.le Z) : X.le Z :=
  let ⟨f, hf⟩ := h₁; let ⟨g, hg⟩ := h₂
  ⟨f ≫ g, by rw [Cat.assoc, hg, hf]⟩

instance {B : 𝒞} : Trans (@Subobject.le 𝒞 _ B) (@Subobject.le 𝒞 _ B) (@Subobject.le 𝒞 _ B) :=
  ⟨Subobject.le_trans⟩

/-- Mutual ≤ gives an iso witness on domains (antisymmetry up to iso).
    Both `f ≫ g` and `g ≫ f` are identities by monic cancellation. -/
theorem Subobject.le_antisymm_iso {B : 𝒞} {S T : Subobject 𝒞 B}
    (hST : S.le T) (hTS : T.le S) :
    ∃ e : S.dom ⟶ T.dom, IsIso e ∧ e ≫ T.arr = S.arr := by
  obtain ⟨f, hf⟩ := hST; obtain ⟨g, hg⟩ := hTS
  have hfg : f ≫ g = Cat.id S.dom :=
    S.monic (f ≫ g) (Cat.id S.dom) (by rw [Cat.assoc, hg, hf, Cat.id_comp])
  have hgf : g ≫ f = Cat.id T.dom :=
    T.monic (g ≫ f) (Cat.id T.dom) (by rw [Cat.assoc, hf, hg, Cat.id_comp])
  exact ⟨f, ⟨g, hfg, hgf⟩, hf⟩

/-- The entire (maximal) subobject: represented by id_B. -/
def Subobject.entire (B : 𝒞) : Subobject 𝒞 B :=
  ⟨B, Cat.id B, by
    intro X f g h; simpa [Cat.id_comp, Cat.comp_id] using h⟩

/-- S is ENTIRE iff its representing mono is an isomorphism. -/
def Subobject.IsEntire {B : 𝒞} (S : Subobject 𝒞 B) : Prop := IsIso S.arr

/-! ## §1.51 Allows

  A subobject B' → B ALLOWS f : A → B if f factors through B'. -/

def Allows {A B : 𝒞} (B' : Subobject 𝒞 B) (f : A ⟶ B) : Prop :=
  ∃ g : A ⟶ B'.dom, g ≫ B'.arr = f

/-! ## §1.51 Image

  The IMAGE of f is the smallest subobject of B that allows f.
  A category HAS IMAGES if every morphism has an image. -/

def IsImage {A B : 𝒞} (f : A ⟶ B) (I : Subobject 𝒞 B) : Prop :=
  Allows I f ∧ ∀ S : Subobject 𝒞 B, Allows S f → I.le S

class HasImages (𝒞 : Type u) [Cat.{v} 𝒞] where
  image   : ∀ {A B : 𝒞}, (A ⟶ B) → Subobject 𝒞 B
  isImage : ∀ {A B : 𝒞} (f : A ⟶ B), IsImage f (image f)

/-- A monic `m : M → B` is its OWN image: the subobject `⟨M, m, hm⟩` is the image of `m`.
    (`m` allows itself by `id`; minimality factors any allowing subobject through `m` using `hm`.) -/
theorem monic_isImage {M B : 𝒞} (m : M ⟶ B) (hm : Monic m) :
    IsImage m (Subobject.mk M m hm) := by
  refine ⟨⟨Cat.id M, Cat.id_comp m⟩, ?_⟩
  intro S hS
  obtain ⟨g, hg⟩ := hS
  -- `g ≫ S.arr = m`, so `⟨M, m⟩ ≤ S` via `g`.
  exact ⟨g, hg⟩

/-! ## §1.512 Cover

  A morphism is a COVER if every monic it factors through is iso.
  Defined directly — no images needed.  With images, equivalent to
  "its image is entire" (proved below). -/

def Cover {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ {C : 𝒞} (m : C ⟶ Y) (g : X ⟶ C), Monic m → g ≫ m = f → IsIso m

theorem monic_cover_iso {X Y : 𝒞} (f : X ⟶ Y) (hc : Cover f) (hm : Monic f) : IsIso f :=
  hc f (Cat.id X) hm (Cat.id_comp f)

/-- A map with a section is a cover: if `s ≫ e = id` then any monic `m` that `e` factors
    through is split (by `s ≫ g`) and hence iso. -/
theorem cover_of_section {X Y : 𝒞} (e : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ e = Cat.id Y) :
    Cover e := by
  intro C m g hm hgm
  have hsplit : (s ≫ g) ≫ m = Cat.id Y := by rw [Cat.assoc, hgm, hs]
  refine ⟨s ≫ g, ?_, hsplit⟩
  -- `m ≫ (s≫g) = id`: post-compose with the mono `m`, both sides give `m`.
  exact hm _ _ (by rw [Cat.assoc, hsplit, Cat.id_comp, Cat.comp_id])

/-- Pre-composing a cover with an isomorphism is still a cover: any monic `m`
    that `i ≫ h` factors through, `h` also factors through (via `i⁻¹ ≫ g`), so
    `h` being a cover forces `m` iso.  Lets us reduce a pullback-square cover to a
    canonical-pullback cover (the two projections differ by the comparison iso). -/
theorem cover_precomp_iso {X X' Y : 𝒞} {i : X ⟶ X'} (hi : IsIso i) {h : X' ⟶ Y}
    (hc : Cover h) : Cover (i ≫ h) := by
  obtain ⟨i', _, hi2⟩ := hi
  intro C m g hm hgm
  refine hc m (i' ≫ g) hm ?_
  calc (i' ≫ g) ≫ m = i' ≫ (g ≫ m) := Cat.assoc _ _ _
    _ = i' ≫ (i ≫ h) := by rw [hgm]
    _ = (i' ≫ i) ≫ h := (Cat.assoc _ _ _).symm
    _ = Cat.id _ ≫ h := by rw [hi2]
    _ = h := Cat.id_comp _

/-- Two images of the same morphism are isomorphic via *any* comparison map that
    is compatible with their inclusions.  Concretely: if `P` and `Q` are both
    images of `g`, and `c : P.dom → Q.dom` satisfies `c ≫ Q.arr = P.arr`, then `c`
    is an isomorphism.  This packages the up-to-unique-iso uniqueness of images and
    is the key lemma for §1.511. -/
theorem image_comparison_iso {A B : 𝒞} {g : A ⟶ B} {P Q : Subobject 𝒞 B}
    (hP : IsImage g P) (hQ : IsImage g Q) (c : P.dom ⟶ Q.dom) (hc : c ≫ Q.arr = P.arr) :
    IsIso c := by
  -- `Q` is minimal and `P` allows `g`, so `Q ≤ P`: get the reverse comparison `d`.
  obtain ⟨d, hd⟩ := hQ.2 P hP.1
  refine ⟨d, ?_, ?_⟩
  · exact P.monic (c ≫ d) (Cat.id P.dom) (by rw [Cat.assoc, hd, hc, Cat.id_comp])
  · exact Q.monic (d ≫ c) (Cat.id Q.dom) (by rw [Cat.assoc, hc, hd, Cat.id_comp])

/-! ## Image API (requires HasImages) -/

variable [HasImages 𝒞]

def image {A B : 𝒞} (f : A ⟶ B) : Subobject 𝒞 B := HasImages.image f

theorem image_allows {A B : 𝒞} (f : A ⟶ B) : Allows (image f) f :=
  (HasImages.isImage f).1

noncomputable def image.lift {A B : 𝒞} (f : A ⟶ B) : A ⟶ (image f).dom :=
  (image_allows f).choose

theorem image.lift_fac {A B : 𝒞} (f : A ⟶ B) : image.lift f ≫ (image f).arr = f :=
  (image_allows f).choose_spec

theorem image_min {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 B) (h : Allows S f) :
    (image f).le S :=
  (HasImages.isImage f).2 S h

/-- With images, f is a cover iff its image is entire (§1.512). -/
theorem cover_iff_image_entire {X Y : 𝒞} (f : X ⟶ Y) : Cover f ↔ Subobject.IsEntire (image f) := by
  constructor
  · intro hc; exact hc (image f).arr (image.lift f) (image f).monic (image.lift_fac f)
  · intro hIso
    rcases hIso with ⟨inv, hinv1, hinv2⟩
    intro C m g hm hfac
    have hallow : Allows (Subobject.mk C m hm) f := ⟨g, hfac⟩
    have him_le : (image f).le (Subobject.mk C m hm) := image_min f _ hallow
    rcases him_le with ⟨h, hh⟩
    have hinv_m : (inv ≫ h) ≫ m = Cat.id Y := by
      calc
        (inv ≫ h) ≫ m = inv ≫ (h ≫ m) := by simp [Cat.assoc]
        _ = inv ≫ (image f).arr := by rw [hh]
        _ = Cat.id Y := hinv2
    have h_right : m ≫ (inv ≫ h) = Cat.id C :=
      hm (m ≫ (inv ≫ h)) (Cat.id C) (by
        calc
          (m ≫ (inv ≫ h)) ≫ m = m ≫ ((inv ≫ h) ≫ m) := by simp [Cat.assoc]
          _ = m ≫ Cat.id Y := by rw [hinv_m]
          _ = m := Cat.comp_id _
          _ = Cat.id C ≫ m := (Cat.id_comp m).symm)
    exact ⟨inv ≫ h, h_right, hinv_m⟩

/-! ## §1.511 A faithful, image-preserving functor reflects images

  The book: *"If A has images and T : A → B is faithful and preserves images,
  then T reflects images."*  The engine is that **A already has images**: a
  candidate subobject `J` that allows `f` is compared to the genuine image of `f`
  in A; `T` sends that comparison to an iso (image uniqueness in B), and
  faithfulness reflects it back. -/

/-- Push a subobject of `B` forward along a mono-preserving functor `T`, landing as
    a subobject of `T B`. -/
def Subobject.map {𝒜 : Type u₁} {ℬ : Type u₂} [Cat.{v} 𝒜] [Cat.{v} ℬ] (T : Functor 𝒜 ℬ)
    (hpm : PreservesMono T) {B : 𝒜} (S : Subobject 𝒜 B) : Subobject ℬ (T.obj B) where
  dom   := T.obj S.dom
  arr   := T.map S.arr
  monic := hpm S.monic

/-- `T` PRESERVES IMAGES: it carries every image factorization in `𝒜` to an image
    factorization in `ℬ`. -/
def PreservesImages {𝒜 : Type u₁} {ℬ : Type u₂} [Cat.{v} 𝒜] [Cat.{v} ℬ] (T : Functor 𝒜 ℬ)
    (hpm : PreservesMono T) : Prop :=
  ∀ {A B : 𝒜} (f : A ⟶ B) (I : Subobject 𝒜 B), IsImage f I → IsImage (T.map f) (Subobject.map T hpm I)

/-- **§1.511**: if `𝒜` has images and `T : 𝒜 → ℬ` is faithful and preserves images,
    then `T` reflects images.  Given `f` and a subobject `J` that allows `f`, if the
    pushforward `T J` is the image of `T f`, then `J` is already the image of `f`. -/
theorem faithful_preserves_images_reflects_images
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] [HasImages 𝒜]
    (T : Functor 𝒜 ℬ) (hfaithful : Faithful T) (hpm : PreservesMono T)
    (hpres : PreservesImages T hpm)
    {A B : 𝒜} (f : A ⟶ B) (J : Subobject 𝒜 B)
    (hJallows : Allows J f) (hJimg : IsImage (T.map f) (Subobject.map T hpm J)) :
    IsImage f J := by
  -- the genuine 𝒜-image of `f`, and its minimality
  have hI : IsImage f (image f) := HasImages.isImage f
  -- `J` allows `f`, so the 𝒜-image is below `J`: comparison `k : image → J`.
  obtain ⟨k, hk⟩ := hI.2 J hJallows
  -- `T` preserves the 𝒜-image, so `T(image f)` is an image of `T f` too.
  have hTI : IsImage (T.map f) (Subobject.map T hpm (image f)) := hpres f (image f) hI
  -- `T k` is a comparison between two images of `T f`, hence an iso…
  have hTk_fac : T.map k ≫ (Subobject.map T hpm J).arr = (Subobject.map T hpm (image f)).arr := by
    show T.map k ≫ T.map J.arr = T.map (image f).arr
    rw [← T.map_comp, hk]
  have hTk_iso : IsIso (T.map k) := image_comparison_iso hTI hJimg (T.map k) hTk_fac
  -- …and faithfulness reflects it: `k` is an iso, with inverse `kinv : J → image f`.
  obtain ⟨kinv, _hk1, hk2⟩ := hfaithful.2 k hTk_iso
  refine ⟨hJallows, ?_⟩
  -- `J` is minimal: for any `S` allowing `f`, factor `J ≤ image f ≤ S`.
  intro S hS
  obtain ⟨t, ht⟩ := hI.2 S hS
  exact ⟨kinv ≫ t, by
    calc (kinv ≫ t) ≫ S.arr = kinv ≫ t ≫ S.arr     := Cat.assoc _ _ _
      _ = kinv ≫ (image f).arr                       := by rw [ht]
      _ = kinv ≫ k ≫ J.arr                           := by rw [hk]
      _ = (kinv ≫ k) ≫ J.arr                         := (Cat.assoc _ _ _).symm
      _ = Cat.id J.dom ≫ J.arr                       := by rw [hk2]
      _ = J.arr                                      := Cat.id_comp _⟩

/-- **§1.511, cross-universe form.**  Same as `faithful_preserves_images_reflects_images` but the
    only thing it needs from `Faithful` is REFLECTION OF ISOS (`hreflIso`), and the categories may
    live in different object universes — the form required by the §2.218 `homRep : Type u → Type (u+1)`
    representation (faithful + reflects-iso, not full). -/
theorem preservesImages_reflectsImages_of_reflectsIso
    {𝒜 : Type u₁} {ℬ : Type u₂} [Cat.{v} 𝒜] [Cat.{v} ℬ] [HasImages 𝒜]
    (T : Functor 𝒜 ℬ)
    (hreflIso : ∀ {X Y : 𝒜} (f : X ⟶ Y), IsIso (T.map f) → IsIso f)
    (hpm : PreservesMono T) (hpres : PreservesImages T hpm)
    {A B : 𝒜} (f : A ⟶ B) (J : Subobject 𝒜 B)
    (hJallows : Allows J f) (hJimg : IsImage (T.map f) (Subobject.map T hpm J)) :
    IsImage f J := by
  have hI : IsImage f (image f) := HasImages.isImage f
  obtain ⟨k, hk⟩ := hI.2 J hJallows
  have hTI : IsImage (T.map f) (Subobject.map T hpm (image f)) := hpres f (image f) hI
  have hTk_fac : T.map k ≫ (Subobject.map T hpm J).arr = (Subobject.map T hpm (image f)).arr := by
    show T.map k ≫ T.map J.arr = T.map (image f).arr
    rw [← T.map_comp, hk]
  have hTk_iso : IsIso (T.map k) := image_comparison_iso hTI hJimg (T.map k) hTk_fac
  obtain ⟨kinv, _hk1, hk2⟩ := hreflIso k hTk_iso
  refine ⟨hJallows, ?_⟩
  intro S hS
  obtain ⟨t, ht⟩ := hI.2 S hS
  exact ⟨kinv ≫ t, by
    calc (kinv ≫ t) ≫ S.arr = kinv ≫ t ≫ S.arr     := Cat.assoc _ _ _
      _ = kinv ≫ (image f).arr                       := by rw [ht]
      _ = kinv ≫ k ≫ J.arr                           := by rw [hk]
      _ = (kinv ≫ k) ≫ J.arr                         := (Cat.assoc _ _ _).symm
      _ = Cat.id J.dom ≫ J.arr                       := by rw [hk2]
      _ = J.arr                                      := Cat.id_comp _⟩

/-! ## §1.514 Epic

  A finite family {xᵢ : Aᵢ → B} is EPIC (jointly epimorphic) if
  for any g,h : B → X, agreeing on all xᵢ ≫ g = xᵢ ≫ h implies g = h. -/

def Epic {n : Nat} (x : Fin n → Σ A : 𝒞, A ⟶ B) : Prop :=
  ∀ (X : 𝒞) (g h : B ⟶ X), (∀ i : Fin n, (x i).2 ≫ g = (x i).2 ≫ h) → g = h


/-- Post-composing a cover with an isomorphism is still a cover (no `HasImages` needed: a direct
    `Cover`-definition argument, since `cover_comp` from S1_56 carries an images hypothesis).  This
    is the general `[Cat 𝒞]` fact at an arbitrary hom universe — the single home for "cover ≫ iso is
    a cover"; downstream sections (e.g. §1.62 under `[PreLogos]`) apply it directly. -/
theorem cover_comp_iso_cat {𝒞 : Type u} [Cat.{v} 𝒞] {X Y Z : 𝒞} {f : X ⟶ Y} {e : Y ⟶ Z}
    (hf : Cover f) (he : IsIso e) : Cover (f ≫ e) := by
  obtain ⟨einv, hee, heinv⟩ := he
  intro C m g hm hgm
  have hmono' : Monic (m ≫ einv) := by
    intro W a b hab; apply hm
    have hcomp : (a ≫ m ≫ einv) ≫ e = (b ≫ m ≫ einv) ≫ e := by rw [hab]
    calc a ≫ m = a ≫ m ≫ (einv ≫ e) := by rw [heinv, Cat.comp_id]
      _ = (a ≫ m ≫ einv) ≫ e := by rw [Cat.assoc, Cat.assoc]
      _ = (b ≫ m ≫ einv) ≫ e := hcomp
      _ = b ≫ m ≫ (einv ≫ e) := by rw [Cat.assoc, Cat.assoc]
      _ = b ≫ m := by rw [heinv, Cat.comp_id]
  have hfact : g ≫ (m ≫ einv) = f := by
    calc g ≫ (m ≫ einv) = (g ≫ m) ≫ einv := by rw [Cat.assoc]
      _ = (f ≫ e) ≫ einv := by rw [hgm]
      _ = f ≫ (e ≫ einv) := by rw [Cat.assoc]
      _ = f := by rw [hee, Cat.comp_id]
  have hmiso : IsIso (m ≫ einv) := hf (m ≫ einv) g hmono' hfact
  have hmeq : m = (m ≫ einv) ≫ e := by rw [Cat.assoc, heinv, Cat.comp_id]
  rw [hmeq]; exact isIso_comp hmiso ⟨einv, hee, heinv⟩

/-- Two subobjects are EQUIVALENT (`≈`) when each is `≤` the other (antisymmetry up to iso). -/
def Subobject.Equiv {B : 𝒞} (S T : Subobject 𝒞 B) : Prop := S.le T ∧ T.le S

end Freyd
