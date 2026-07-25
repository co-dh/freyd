/-
  Freyd & Scedrov, *Categories and Allegories* §1.58–§1.59
  Bicartesian categories, abelian categories, half-additive.

  §1.58 BICARTESIAN = Cartesian + Cocartesian.
         Coterminator 0, coproduct A+B, coequalizer.
         Pushout = pullback in opposite category.
  §1.59 ABELIAN = bicartesian satisfying all Horn sentences true for 𝒜𝒷.
         Zero object, half-additive, middle-two interchange.
-/


import Freyd.S1_1
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_43
import Freyd.S1_45
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_56


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.58 Bicartesian categories

  A BICARTESIAN CATEGORY is both Cartesian and coCartesian:
  has finite limits and colimits. -/

/-- Has coterminator (initial object): dual to HasTerminal. -/
class HasCoterminator (𝒞 : Type u) [Cat.{v} 𝒞] where
  zero  : 𝒞
  init  : (X : 𝒞) → zero ⟶ X
  init_uniq  : ∀ {X : 𝒞} (f g : zero ⟶ X), f = g

/-! ### §1.58 ¶2  Strict coterminator

  Freyd: "In any Cartesian category with an object `0` such that all morphisms
  targeted at `0` are isomorphisms, then `0` is a coterminator.  This extra
  property is said to make `0` a STRICT COTERMINATOR."  Our earlier use of `0`
  [§1.474, §1.552] is consistent with this.

  The hypothesis is about maps *into* `0`; being a coterminator is about the
  unique map *out* of `0`.  These are independent a priori — the paragraph
  derives the latter from the former (needs only binary products). -/

/-- An object `Z` is a STRICT COTERMINATOR when every morphism targeted at `Z`
    is an isomorphism. -/
def StrictCoterminator (Z : 𝒞) : Prop := ∀ {X : 𝒞} (f : X ⟶ Z), IsIso f

/-- **§1.58 ¶2** (uniqueness half, choice-free).  A strict coterminator admits at
    most one map to any `A`.  Let `inv : Z → Z×A` invert the projection
    `fst : Z×A → Z` (an iso, since it is targeted at `Z`).  Every `h : Z → A` is
    forced to equal `inv ≫ snd`, because `pair 1_Z h` is a section of `fst` and so
    must be its inverse `inv` — independent of `h`. -/
theorem strictCoterminator_hom_unique [HasBinaryProducts 𝒞] {Z : 𝒞}
    (hZ : StrictCoterminator Z) {A : 𝒞} (f g : Z ⟶ A) : f = g := by
  obtain ⟨inv, hfi, _hif⟩ := hZ (fst : prod Z A ⟶ Z)
  -- hfi : fst ≫ inv = 1_{Z×A}.  Show every `h` collapses to `inv ≫ snd`.
  have key : ∀ h : Z ⟶ A, h = inv ≫ snd := fun h => by
    have hpair : pair (Cat.id Z) h = inv :=
      calc pair (Cat.id Z) h
          = pair (Cat.id Z) h ≫ Cat.id (prod Z A) := (Cat.comp_id _).symm
        _ = pair (Cat.id Z) h ≫ (fst ≫ inv) := congrArg (pair (Cat.id Z) h ≫ ·) hfi.symm
        _ = (pair (Cat.id Z) h ≫ fst) ≫ inv := (Cat.assoc _ _ _).symm
        _ = Cat.id Z ≫ inv := congrArg (· ≫ inv) (fst_pair (Cat.id Z) h)
        _ = inv := Cat.id_comp _
    calc h = pair (Cat.id Z) h ≫ snd := (snd_pair _ _).symm
      _ = inv ≫ snd := congrArg (· ≫ snd) hpair
  exact (key f).trans (key g).symm

/-- **§1.58 ¶2**.  A strict coterminator is a coterminator (initial object): the
    composite `fst⁻¹ ≫ snd : Z → A` supplies the map out, and
    `strictCoterminator_hom_unique` forces it to be the only one.  (`noncomputable`
    because extracting the iso-inverse from `IsIso = ∃ …` needs `Classical.choice`,
    exactly as for `Φinv`; the uniqueness fact above stays choice-free.) -/
noncomputable def HasCoterminator.ofStrict [HasBinaryProducts 𝒞] {Z : 𝒞}
    (hZ : StrictCoterminator Z) : HasCoterminator 𝒞 where
  zero := Z
  init A := (hZ (fst : prod Z A ⟶ Z)).choose ≫ snd
  init_uniq f g := strictCoterminator_hom_unique hZ f g

/-- **§1.58 ¶2 (strictness).**  A strict coterminator `Z` has **no proper
    subobjects**: every monic into `Z` is an isomorphism.  (Immediate — *every*
    morphism into `Z` is an iso; the mono is just the subobject case.) -/
theorem strictCoterminator_subobject_improper {Z : 𝒞} (hZ : StrictCoterminator Z)
    {S : 𝒞} (m : S ⟶ Z) (_hm : Monic m) : IsIso m := hZ m

/-- **§1.58 ¶2 (strictness).**  Hence every equalizer targeted at a strict
    coterminator is **entire**: the inclusion `E ↣ Z` of the equalizer of any
    `f, g : Z → B` is an iso, i.e. the equalizer is the whole of `Z`.  (Freyd:
    "all equalizers in `0` are entire.")  Just the subobject fact applied to the
    equalizer cone's map. -/
theorem strictCoterminator_equalizer_entire {Z B : 𝒞} (hZ : StrictCoterminator Z)
    {f g : Z ⟶ B} (c : EqualizerCone f g) : IsIso c.map := hZ c.map

variable [HasCoterminator 𝒞]

def coterm : 𝒞 := HasCoterminator.zero
def zeroMap (X : 𝒞) : coterm ⟶ X := HasCoterminator.init X

/-- Has binary coproducts: dual to HasBinaryProducts. -/
class HasBinaryCoproducts (𝒞 : Type u) [Cat.{v} 𝒞] where
  coprod : 𝒞 → 𝒞 → 𝒞
  inl    : {A B : 𝒞} → A ⟶ coprod A B
  inr    : {A B : 𝒞} → B ⟶ coprod A B
  case   : {X A B : 𝒞} → (A ⟶ X) → (B ⟶ X) → (coprod A B ⟶ X)
  case_inl : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X), inl ≫ case f g = f
  case_inr : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X), inr ≫ case f g = g
  case_uniq : ∀ {X A B : 𝒞} (f : A ⟶ X) (g : B ⟶ X) (h : coprod A B ⟶ X),
    inl ≫ h = f → inr ≫ h = g → h = case f g

/-- A single coequalizer: dual to HasEqualizer. -/
class HasCoequalizer {A B : 𝒞} (f g : A ⟶ B) where
  obj   : 𝒞
  map   : B ⟶ obj
  eq    : f ≫ map = g ≫ map
  desc  : ∀ {X : 𝒞} (h : B ⟶ X), f ≫ h = g ≫ h → obj ⟶ X
  fac   : ∀ {X : 𝒞} (h : B ⟶ X) (h_eq : f ≫ h = g ≫ h), map ≫ desc h h_eq = h
  uniq  : ∀ {X : 𝒞} (h : B ⟶ X) (h_eq : f ≫ h = g ≫ h) (m : obj ⟶ X),
    map ≫ m = h → m = desc h h_eq

/-- Has coequalizers: dual to HasEqualizers. -/
class HasCoequalizers (𝒞 : Type u) [Cat.{v} 𝒞] where
  coeq : ∀ {A B : 𝒞} (f g : A ⟶ B), HasCoequalizer f g

/-- A BICARTESIAN CATEGORY: Cartesian + coCartesian (§1.58). -/
class BicartesianCategory (𝒞 : Type u) [Cat.{v} 𝒞] extends
    CartesianCategory 𝒞, HasCoterminator 𝒞, HasBinaryCoproducts 𝒞, HasCoequalizers 𝒞

/-! ## Coequalizer maps are covers

  In any category, the coequalizer map of any parallel pair is a cover.
  This is the converse direction of §1.566 (in a regular category, every
  cover IS the coequalizer of its kernel pair). -/

/-- The coequalizer map of any parallel pair is a cover (dual of: equalizer
    inclusions are monic).  Does NOT require regularity.
    Proof: given m mono with h ≫ m = q, use m-monicity to get f ≫ h = g ≫ h,
    then the universal property of q gives k : C → D with q ≫ k = h;
    then q ≫ (k ≫ m) = q forces k ≫ m = id by uniqueness; and
    (m ≫ k) ≫ m = m with m mono forces m ≫ k = id. -/
theorem coeq_map_is_cover {𝒟 : Type u} [Cat.{v} 𝒟] {A B : 𝒟} {f g : A ⟶ B}
    (hcoeq : HasCoequalizer f g) : Cover hcoeq.map := by
  intro D m h hm hfac
  -- From h ≫ m = q and f ≫ q = g ≫ q, deduce f ≫ h = g ≫ h (via m monic).
  have heq : f ≫ h = g ≫ h :=
    hm _ _ (by rw [Cat.assoc, Cat.assoc, hfac]; exact hcoeq.eq)
  -- The coequalizer universal property gives k : C → D with q ≫ k = h.
  let k := hcoeq.desc h heq
  have hqk : hcoeq.map ≫ k = h := hcoeq.fac h heq
  -- q ≫ (k ≫ m) = h ≫ m = q = q ≫ id_C, so k ≫ m = id_C by coeq uniqueness.
  have hkm : k ≫ m = Cat.id hcoeq.obj := by
    have step1 : hcoeq.map ≫ (k ≫ m) = hcoeq.map := by
      rw [← Cat.assoc, hqk, hfac]
    have step2 : hcoeq.map ≫ Cat.id hcoeq.obj = hcoeq.map := Cat.comp_id _
    exact (hcoeq.uniq hcoeq.map hcoeq.eq (k ≫ m) step1).trans
      (hcoeq.uniq hcoeq.map hcoeq.eq (Cat.id _) step2).symm
  -- m ≫ k satisfies (m ≫ k) ≫ m = m = id_D ≫ m, so m ≫ k = id_D by m-monicity.
  have hmk : m ≫ k = Cat.id D :=
    hm _ _ (by rw [Cat.assoc, hkm, Cat.comp_id, Cat.id_comp])
  exact ⟨k, hmk, hkm⟩

/-! ## §1.581 Bicartesian representations preserve covers

  If 𝒜 and ℬ are regular and cocartesian, and F : 𝒜 → ℬ is a functor that
  preserves coequalizers (and hence the bicartesian structure), then F
  preserves covers (§1.566: in a regular category a cover = coequalizer
  of its kernel pair). -/

/-- F PRESERVES COEQUALIZERS: the image of any coequalizer in 𝒜 is a
    coequalizer in ℬ.  Concretely: if q : B → C is the coequalizer of f, g
    in 𝒜, then F.map q : F B → F C is the coequalizer of F.map f, F.map g. -/
def PreservesCoequalizers {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : Functor 𝒜 ℬ) : Prop :=
  ∀ {A B : 𝒜} (f g : A ⟶ B) [hcoeq : HasCoequalizer f g],
    F.map f ≫ F.map hcoeq.map = F.map g ≫ F.map hcoeq.map ∧
    ∀ {X : ℬ} (h : F.obj B ⟶ X),
      F.map f ≫ h = F.map g ≫ h →
      ∃ m : F.obj hcoeq.obj ⟶ X, F.map hcoeq.map ≫ m = h ∧
        ∀ m' : F.obj hcoeq.obj ⟶ X, F.map hcoeq.map ≫ m' = h → m' = m

/-- **§1.581**: If 𝒜 and ℬ are regular and cocartesian, and F : 𝒜 → ℬ
    is a functor that preserves coequalizers, then F preserves covers.
    Proof: (1) every cover f is a coequalizer of its kernel pair (§1.566);
    (2) by PreservesCoequalizers, F(kp-coeq-map) is a coequalizer in ℬ;
    (3) the coeq-map of the kernel pair of f and the coeq-map from HasCoequalizers
        are related by an iso e₁ : hce.obj ≅ B constructed from mutual coeq UMPs;
    (4) F f = F(hce.map) ≫ F(e₁); F(hce.map) is a cover (coeq_map_is_cover)
        and F(e₁) is an iso; cover ≫ iso = cover. -/
theorem bicart_repr_preserves_covers
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    [RegularCategory 𝒜] [HasCoequalizers 𝒜]
    [RegularCategory ℬ] [HasCoequalizers ℬ]
    (F : Functor 𝒜 ℬ)
    (hpres : PreservesCoequalizers F)
    {A B : 𝒜} (f : A ⟶ B) (hf : Cover f) :
    Cover (F.map f) := by
  -- Step 1: coequalizer of kernel pair of f in 𝒜.
  let hce := HasCoequalizers.coeq (kp₁ (f := f)) (kp₂ (f := f))
  -- e₁ : hce.obj → B induced by the coeq universal property applied to f.
  let e₁ : hce.obj ⟶ B := hce.desc f kp_sq
  have he₁ : hce.map ≫ e₁ = f := hce.fac f kp_sq
  -- e₂ : B → hce.obj: f is a coeq of its kernel pair (§1.566), kp₁ ≫ hce.map = kp₂ ≫ hce.map.
  obtain ⟨e₂, he₂, _⟩ := cover_is_coequalizer_of_level f hf hce.map hce.eq
  -- e₁ ≫ e₂ = id: hce.map ≫ (e₁ ≫ e₂) = f ≫ e₂ = hce.map = hce.map ≫ id.
  have he₁e₂ : e₁ ≫ e₂ = Cat.id hce.obj :=
    (hce.uniq hce.map hce.eq (e₁ ≫ e₂) (by rw [← Cat.assoc, he₁, he₂])).trans
    (hce.uniq hce.map hce.eq (Cat.id _) (Cat.comp_id _)).symm
  -- e₂ ≫ e₁ = id: f ≫ (e₂ ≫ e₁) = hce.map ≫ e₁ = f = f ≫ id; f is epi.
  have he₂e₁ : e₂ ≫ e₁ = Cat.id B :=
    cover_epi hf (by rw [← Cat.assoc, he₂, he₁, Cat.comp_id])
  -- e₁ is an iso; hence F e₁ is an iso.
  have he₁_iso : IsIso e₁ := ⟨e₂, by exact he₁e₂, he₂e₁⟩
  have hFe₁_iso : IsIso (F.map e₁) := functor_preserves_iso e₁ he₁_iso
  -- F(hce.map) is a cover: build HasCoequalizer in ℬ from hpres, apply coeq_map_is_cover.
  obtain ⟨hpeq, hpfac⟩ := hpres (kp₁ (f := f)) (kp₂ (f := f))
  let hceB : HasCoequalizer (F.map (kp₁ (f := f))) (F.map (kp₂ (f := f))) :=
    { obj := F.obj hce.obj, map := F.map hce.map, eq := hpeq
      desc := fun h heq => (hpfac h heq).choose
      fac  := fun h heq => (hpfac h heq).choose_spec.1
      uniq := fun h heq m hm => (hpfac h heq).choose_spec.2 m hm }
  -- F f = F(hce.map) ≫ F(e₁); prove Cover (F hce.map ≫ F e₁) directly.
  rw [show F.map f = F.map hce.map ≫ F.map e₁ from by rw [← F.map_comp, he₁]]
  -- Unfold Cover: given m : C → F B mono, g : F A → C, g ≫ m = F hce.map ≫ F e₁. Show IsIso m.
  intro C m g hm hgm
  obtain ⟨e₁inv, he₁inv_left, he₁inv_right⟩ := hFe₁_iso
  -- m' = m ≫ e₁inv : C → F.obj hce.obj.  g ≫ m' = F hce.map (post-compose hgm with e₁inv).
  let m' : C ⟶ F.obj hce.obj := m ≫ e₁inv
  have hgm'_eq : g ≫ m' = F.map hce.map :=
    calc g ≫ m ≫ e₁inv = (g ≫ m) ≫ e₁inv := (Cat.assoc _ _ _).symm
      _ = (F.map hce.map ≫ F.map e₁) ≫ e₁inv := by rw [hgm]
      _ = F.map hce.map ≫ (F.map e₁ ≫ e₁inv) := Cat.assoc _ _ _
      _ = F.map hce.map := by rw [he₁inv_left, Cat.comp_id]
  -- m' is monic: m is mono, e₁inv is iso hence mono (has right inverse F e₁).
  have hm'_mono : Monic m' := by
    intro W a b hab
    -- hab : a ≫ m' = b ≫ m', i.e. a ≫ m ≫ e₁inv = b ≫ m ≫ e₁inv.
    -- (a ≫ m) ≫ e₁inv = (b ≫ m) ≫ e₁inv (by assoc)
    have hstep : (a ≫ m) ≫ e₁inv = (b ≫ m) ≫ e₁inv :=
      calc (a ≫ m) ≫ e₁inv = a ≫ m ≫ e₁inv := Cat.assoc _ _ _
        _ = b ≫ m ≫ e₁inv := hab
        _ = (b ≫ m) ≫ e₁inv := (Cat.assoc _ _ _).symm
    -- Post-compose with F e₁ (right inverse of e₁inv) to cancel e₁inv.
    have heq_m : a ≫ m = b ≫ m :=
      calc a ≫ m = (a ≫ m) ≫ (e₁inv ≫ F.map e₁) := by rw [he₁inv_right, Cat.comp_id]
        _ = ((a ≫ m) ≫ e₁inv) ≫ F.map e₁ := (Cat.assoc _ _ _).symm
        _ = ((b ≫ m) ≫ e₁inv) ≫ F.map e₁ := by rw [hstep]
        _ = (b ≫ m) ≫ (e₁inv ≫ F.map e₁) := Cat.assoc _ _ _
        _ = b ≫ m := by rw [he₁inv_right, Cat.comp_id]
    exact hm _ _ heq_m
  -- F kp₁ ≫ g = F kp₂ ≫ g: from hm'_mono, since (F kp₁ ≫ g) ≫ m' = (F kp₂ ≫ g) ≫ m'
  -- (both equal F kp₁/kp₂ ≫ F hce.map via hgm'_eq and hpeq).
  have hkp_g : F.map (kp₁ (f := f)) ≫ g = F.map (kp₂ (f := f)) ≫ g :=
    hm'_mono _ _ (by
      rw [Cat.assoc, Cat.assoc, hgm'_eq]
      exact hpeq)
  -- k : F.obj hce.obj → C, the candidate inverse of m'.  hceB.desc g hkp_g : obj ⟶ C.
  let k : F.obj hce.obj ⟶ C := hceB.desc g hkp_g
  have hqk : hceB.map ≫ k = g := hceB.fac g hkp_g
  -- k ≫ m' = id_{F.obj hce.obj}: hceB.map ≫ (k ≫ m') = g ≫ m' = hceB.map, use uniq.
  have hkm' : k ≫ m' = Cat.id hceB.obj :=
    (hceB.uniq hceB.map hceB.eq (k ≫ m')
      (by rw [← Cat.assoc, hqk]; exact hgm'_eq)).trans
    (hceB.uniq hceB.map hceB.eq (Cat.id _) (Cat.comp_id _)).symm
  -- m' ≫ k = id_C: hm'_mono: (m' ≫ k) ≫ m' = m' ≫ (k ≫ m') = m' = id ≫ m'.
  have hm'k : m' ≫ k = Cat.id C :=
    hm'_mono _ _ (by
      have lhs : (m' ≫ k) ≫ m' = m' := by
        rw [Cat.assoc, hkm']; exact Cat.comp_id m'
      rw [lhs, Cat.id_comp])
  -- So m' = m ≫ e₁inv is iso.  Then m = m' ≫ F e₁ is a composition of isos, hence iso.
  have hm'_iso : IsIso m' := ⟨k, hm'k, hkm'⟩
  -- m = m' ≫ F e₁ (since e₁inv ≫ F e₁ = id).
  have hm_eq : m = m' ≫ F.map e₁ := by
    rw [show m' ≫ F.map e₁ = m ≫ e₁inv ≫ F.map e₁ from Cat.assoc _ _ _,
        he₁inv_right, Cat.comp_id]
  rw [hm_eq]
  exact isIso_comp hm'_iso (functor_preserves_iso e₁ he₁_iso)

/-! ## §1.582 Image via coequalizer

  In a bicartesian regular category, the image of x : A → B is
  constructible as the coequalizer of its kernel pair.  Specifically:
  form the kernel pair (level) l = kp₁, r = kp₂ : kernelPair(x) ⇉ A,
  then take the coequalizer q : A → C of l and r.  The unique morphism
  m : C → B satisfying q ≫ m = x is monic; it is the image of x. -/

/-- **§1.582**: In a bicartesian regular category, the image of x : A → B is
    the coequalizer of its kernel pair.  Let l = kp₁, r = kp₂ be the
    projections of the kernel pair of x, and let q : A → C be their
    coequalizer.  The unique m : C → B with q ≫ m = x is monic. -/
theorem image_via_coeq [BicartesianCategory 𝒞] [RegularCategory 𝒞]
    {A B : 𝒞} (x : A ⟶ B) :
    let hcoeq := (HasCoequalizers.coeq (kp₁ (f := x)) (kp₂ (f := x)))
    Monic (hcoeq.desc x kp_sq) := by
  intro hcoeq
  -- q : A → C is the coeq map, m : C → B the unique factorization.
  have hq : Cover hcoeq.map := coeq_map_is_cover hcoeq
  -- Image factorization of x: e cover, I.arr monic.
  have hi_mono : Monic (image x).arr := (image x).monic
  have he_cover : Cover (image.lift x) := image_lift_cover x
  -- kp₁(x) ≫ e = kp₂(x) ≫ e: kp_sq gives kp₁ ≫ x = kp₂ ≫ x; I.arr monic cancels.
  have hkp_e : kp₁ (f := x) ≫ image.lift x = kp₂ (f := x) ≫ image.lift x :=
    hi_mono _ _
      (calc (kp₁ (f:=x) ≫ image.lift x) ≫ (image x).arr
          = kp₁ (f:=x) ≫ x := by rw [Cat.assoc]; exact congrArg (kp₁ (f:=x) ≫ ·) (image.lift_fac x)
        _ = kp₂ (f:=x) ≫ x := kp_sq
        _ = (kp₂ (f:=x) ≫ image.lift x) ≫ (image x).arr := by rw [Cat.assoc]; exact (congrArg (kp₂ (f:=x) ≫ ·) (image.lift_fac x)).symm)
  -- φ : C → I.dom from coeq UMP applied to (image.lift x).
  have hqφ : hcoeq.map ≫ hcoeq.desc (image.lift x) hkp_e = image.lift x :=
    hcoeq.fac (image.lift x) hkp_e
  -- m = φ ≫ I.arr: q ≫ m = x = e ≫ I.arr = q ≫ φ ≫ I.arr, so cover_epi q.
  have hm_eq : hcoeq.desc x kp_sq =
      hcoeq.desc (image.lift x) hkp_e ≫ (image x).arr :=
    cover_epi hq (by
      rw [hcoeq.fac x kp_sq, ← Cat.assoc, hqφ, image.lift_fac])
  -- kp₁(e) ≫ q = kp₂(e) ≫ q: lift kp_sq(e) into kernelPair(x), then use hcoeq.eq.
  have hkp_eq_q : kp₁ (f := image.lift x) ≫ hcoeq.map = kp₂ (f := image.lift x) ≫ hcoeq.map := by
    -- kp₁(e) ≫ x = kp₂(e) ≫ x via kp_sq(e) and image factorization.
    have hke_x : kp₁ (f := image.lift x) ≫ x = kp₂ (f := image.lift x) ≫ x :=
      calc kp₁ (f:=image.lift x) ≫ x
          = kp₁ (f:=image.lift x) ≫ image.lift x ≫ (image x).arr := by rw [image.lift_fac]
        _ = (kp₁ (f:=image.lift x) ≫ image.lift x) ≫ (image x).arr := (Cat.assoc _ _ _).symm
        _ = (kp₂ (f:=image.lift x) ≫ image.lift x) ≫ (image x).arr := by
              exact congrArg (· ≫ _) kp_sq
        _ = kp₂ (f:=image.lift x) ≫ image.lift x ≫ (image x).arr := Cat.assoc _ _ _
        _ = kp₂ (f:=image.lift x) ≫ x := by rw [image.lift_fac]
    -- Lift l : kernelPair(e) → kernelPair(x) via the pullback.
    have hl₁ := kp_lift_p₁ (kp₁ (f:=image.lift x)) (kp₂ (f:=image.lift x)) hke_x
    have hl₂ := kp_lift_p₂ (kp₁ (f:=image.lift x)) (kp₂ (f:=image.lift x)) hke_x
    -- kp₁(e) ≫ q = l ≫ kp₁(x) ≫ q = l ≫ kp₂(x) ≫ q = kp₂(e) ≫ q.
    -- Naming l avoids repeated long expression; no rw to sidestep motive issues.
    let l := (HasPullbacks.has x x).lift
      ⟨_, kp₁ (f:=image.lift x), kp₂ (f:=image.lift x), hke_x⟩
    -- step1: kp₁(e) ≫ q = (l ≫ kp₁(x)) ≫ q  [from hl₁]
    -- step2: (l ≫ kp₁(x)) ≫ q = l ≫ (kp₁(x) ≫ q)  [assoc]
    -- step3: l ≫ (kp₁(x) ≫ q) = l ≫ (kp₂(x) ≫ q)  [hcoeq.eq]
    -- step4: l ≫ (kp₂(x) ≫ q) = (l ≫ kp₂(x)) ≫ q  [assoc.symm]
    -- step5: (l ≫ kp₂(x)) ≫ q = kp₂(e) ≫ q  [from hl₂]
    exact (congrArg (· ≫ hcoeq.map) hl₁.symm).trans
      ((Cat.assoc l _ _).trans
        ((congrArg (l ≫ ·) hcoeq.eq).trans
          ((Cat.assoc l _ _).symm.trans (congrArg (· ≫ hcoeq.map) hl₂))))
  -- ψ : I.dom → C from cover_is_coequalizer_of_level applied to (image.lift x).
  obtain ⟨ψ, heψ, _⟩ :=
    cover_is_coequalizer_of_level (image.lift x) he_cover hcoeq.map hkp_eq_q
  -- φ ≫ ψ = id_C (cover_epi hq) and ψ ≫ φ = id (cover_epi he_cover).
  have hφψ : hcoeq.desc (image.lift x) hkp_e ≫ ψ = Cat.id hcoeq.obj :=
    cover_epi hq (by rw [← Cat.assoc, hqφ, heψ, Cat.comp_id])
  -- Monic m: given u ≫ m = v ≫ m, rewrite via hm_eq to use φ,I.arr.
  intro W u v huv
  -- First get u ≫ φ ≫ I.arr = v ≫ φ ≫ I.arr from huv via hm_eq.
  have huv' : u ≫ hcoeq.desc (image.lift x) hkp_e ≫ (image x).arr =
               v ≫ hcoeq.desc (image.lift x) hkp_e ≫ (image x).arr := by
    rw [← hm_eq]; exact huv
  -- Cancel I.arr (monic) to get u ≫ φ = v ≫ φ.
  have hφ_eq : u ≫ hcoeq.desc (image.lift x) hkp_e = v ≫ hcoeq.desc (image.lift x) hkp_e :=
    hi_mono _ _ (by rw [Cat.assoc, Cat.assoc]; exact huv')
  -- Cancel φ using its right-inverse ψ.
  calc u = u ≫ (hcoeq.desc (image.lift x) hkp_e ≫ ψ) := by rw [hφψ, Cat.comp_id]
    _ = (u ≫ hcoeq.desc (image.lift x) hkp_e) ≫ ψ := (Cat.assoc _ _ _).symm
    _ = (v ≫ hcoeq.desc (image.lift x) hkp_e) ≫ ψ := by rw [hφ_eq]
    _ = v ≫ (hcoeq.desc (image.lift x) hkp_e ≫ ψ) := Cat.assoc _ _ _
    _ = v := by rw [hφψ, Cat.comp_id]

/-! ## §1.583 Effectiveness is a Horn sentence

  In a bicartesian regular category, effectiveness of an equivalence relation
  E (tabulated by l, r : E ⇉ A) is a Horn sentence in the bicartesian
  predicates: E is effective iff the coequalizer square
     E ⇉ A → C
  is a pullback (i.e. E ≅ kernelPair(q) where q : A → C is the coequalizer
  of l and r). -/

/-- **§1.583**: In a bicartesian regular category, an equivalence relation
    E on A (tabulated by l, r : E ⇉ A) is effective iff the coequalizer
    square is a pullback.  Let q : A → C be the coequalizer of l and r.
    The cone ⟨E, l, r⟩ over (q, q) is a pullback (E ≅ kernelPair(q))
    iff E is effective (kernel pair of some cover x : A → Q with l ≫ x = r ≫ x). -/
theorem effectiveness_iff_coeq_pullback [BicartesianCategory 𝒞] [RegularCategory 𝒞]
    {A E : 𝒞} (l r : E ⟶ A) :
    let hcoeq := HasCoequalizers.coeq l r
    let q := hcoeq.map
    -- E is effective: kernel pair of some cover x with l,r equalizing x
    (∃ (Q : 𝒞) (x : A ⟶ Q) (hlx : l ≫ x = r ≫ x), Cover x ∧
        IsIso ((HasPullbacks.has x x).lift ⟨E, l, r, hlx⟩)) ↔
    (⟨E, l, r, hcoeq.eq⟩ : Cone q q).IsPullback := by
  intro hcoeq q
  constructor
  · -- Forward: effective ⇒ coeq square is a pullback.
    rintro ⟨Q, x, hlx, hx_cover, ⟨k_inv, hk_left, hk_right⟩⟩
    -- k : E → kernelPair(x), the chosen iso into the kernel pair of x.
    let k : E ⟶ kernelPair x := (HasPullbacks.has x x).lift ⟨E, l, r, hlx⟩
    have hk_p₁ : k ≫ kp₁ (f := x) = l := kp_lift_p₁ l r hlx
    have hk_p₂ : k ≫ kp₂ (f := x) = r := kp_lift_p₂ l r hlx
    -- m : C → Q with q ≫ m = x (coeq factorization of x through q).
    let m : hcoeq.obj ⟶ Q := hcoeq.desc x hlx
    have hqm : q ≫ m = x := hcoeq.fac x hlx
    -- k_inv ≫ l = kp₁(x), k_inv ≫ r = kp₂(x).
    have hkinv_l : k_inv ≫ l = kp₁ (f := x) :=
      calc k_inv ≫ l = k_inv ≫ (k ≫ kp₁ (f := x)) := by rw [hk_p₁]
        _ = (k_inv ≫ k) ≫ kp₁ (f := x) := (Cat.assoc _ _ _).symm
        _ = kp₁ (f := x) := by rw [hk_right, Cat.id_comp]
    have hkinv_r : k_inv ≫ r = kp₂ (f := x) :=
      calc k_inv ≫ r = k_inv ≫ (k ≫ kp₂ (f := x)) := by rw [hk_p₂]
        _ = (k_inv ≫ k) ≫ kp₂ (f := x) := (Cat.assoc _ _ _).symm
        _ = kp₂ (f := x) := by rw [hk_right, Cat.id_comp]
    intro d
    -- d.π₁ ≫ x = d.π₂ ≫ x (from d.w : d.π₁ ≫ q = d.π₂ ≫ q).
    have hdx : d.π₁ ≫ x = d.π₂ ≫ x := by
      rw [← hqm, ← Cat.assoc, ← Cat.assoc, d.w]
    -- kd : d.pt → kernelPair(x) lifting (d.π₁, d.π₂).
    let kd : d.pt ⟶ kernelPair x := (HasPullbacks.has x x).lift ⟨_, d.π₁, d.π₂, hdx⟩
    have hkd₁ : kd ≫ kp₁ (f := x) = d.π₁ := kp_lift_p₁ d.π₁ d.π₂ hdx
    have hkd₂ : kd ≫ kp₂ (f := x) = d.π₂ := kp_lift_p₂ d.π₁ d.π₂ hdx
    refine ⟨kd ≫ k_inv, ⟨?_, ?_⟩, ?_⟩
    · -- (kd ≫ k_inv) ≫ l = kd ≫ kp₁(x) = d.π₁.
      rw [Cat.assoc, hkinv_l, hkd₁]
    · rw [Cat.assoc, hkinv_r, hkd₂]
    · -- Uniqueness.
      intro v hv₁ hv₂
      -- v ≫ k = kd by pullback uniqueness on kernelPair(x).
      have hvk : v ≫ k = kd := by
        have e₁ : (v ≫ k) ≫ kp₁ (f := x) = d.π₁ := by
          rw [Cat.assoc, hk_p₁, hv₁]
        have e₂ : (v ≫ k) ≫ kp₂ (f := x) = d.π₂ := by
          rw [Cat.assoc, hk_p₂, hv₂]
        exact (kp_lift_uniq d.π₁ d.π₂ hdx (v ≫ k) e₁ e₂)
      calc v = v ≫ (k ≫ k_inv) := by rw [hk_left, Cat.comp_id]
        _ = (v ≫ k) ≫ k_inv := (Cat.assoc _ _ _).symm
        _ = kd ≫ k_inv := by rw [hvk]
  · -- Backward: coeq square is a pullback ⇒ effective (via x = q).
    intro h_pb
    -- k_q : E → kernelPair(q), the chosen lift of (l, r) into kernelPair(q).
    let k_q : E ⟶ kernelPair q := (HasPullbacks.has q q).lift ⟨E, l, r, hcoeq.eq⟩
    have hkq₁ : k_q ≫ kp₁ (f := q) = l := kp_lift_p₁ l r hcoeq.eq
    have hkq₂ : k_q ≫ kp₂ (f := q) = r := kp_lift_p₂ l r hcoeq.eq
    -- The kernel-pair projections give a cone over (q, q); apply the pullback h_pb.
    obtain ⟨u, ⟨hu₁, hu₂⟩, _⟩ :=
      h_pb ⟨kernelPair q, kp₁ (f := q), kp₂ (f := q), kp_sq⟩
    -- u : kernelPair(q) → E with u ≫ l = kp₁(q), u ≫ r = kp₂(q).
    -- Show k_q is iso with inverse u.
    refine ⟨hcoeq.obj, q, hcoeq.eq, coeq_map_is_cover hcoeq, ⟨u, ?_, ?_⟩⟩
    · -- k_q ≫ u = id_E.  Use that ⟨E,l,r⟩ is a pullback (h_pb): unique map E→E.
      -- Both id_E and k_q ≫ u send (l,r) to (l,r), so equal by uniqueness in h_pb.
      obtain ⟨w, _, huniq⟩ := h_pb ⟨E, l, r, hcoeq.eq⟩
      have hid : Cat.id E = w := huniq (Cat.id E) (Cat.id_comp _) (Cat.id_comp _)
      have hcomp : k_q ≫ u = w := by
        refine huniq (k_q ≫ u) ?_ ?_
        · rw [Cat.assoc, hu₁, hkq₁]
        · rw [Cat.assoc, hu₂, hkq₂]
      rw [hcomp, ← hid]
    · -- u ≫ k_q = id_{kernelPair(q)}.  By pullback uniqueness on kernelPair(q).
      have e₁ : (u ≫ k_q) ≫ kp₁ (f := q) = kp₁ (f := q) := by
        rw [Cat.assoc, hkq₁, hu₁]
      have e₂ : (u ≫ k_q) ≫ kp₂ (f := q) = kp₂ (f := q) := by
        rw [Cat.assoc, hkq₂, hu₂]
      have hide : (u ≫ k_q) = (HasPullbacks.has q q).lift ⟨_, kp₁ (f := q), kp₂ (f := q), kp_sq⟩ :=
        kp_lift_uniq (kp₁ (f := q)) (kp₂ (f := q)) kp_sq (u ≫ k_q) e₁ e₂
      have hidk : Cat.id (kernelPair q) =
          (HasPullbacks.has q q).lift ⟨_, kp₁ (f := q), kp₂ (f := q), kp_sq⟩ :=
        kp_lift_uniq (kp₁ (f := q)) (kp₂ (f := q)) kp_sq (Cat.id (kernelPair q))
          (Cat.id_comp _) (Cat.id_comp _)
      rw [hide, ← hidk]
      rfl

/-! ## §1.584 Slice category inherits cocartesian structure

  If 𝒜 is cocartesian, so is every slice 𝒜/B, and the forgetful functor
  Σ : 𝒜/B → 𝒜 is a faithful representation of cocartesian categories.

  The coproduct of (A, f : A→B) and (C, g : C→B) in Over B is
  (A+C, case f g : A+C→B) where `+` and `case` are the coproduct of 𝒜.
  The coterminator in Over B is (0, init B : 0→B).
  Coequalizers in Over B are the underlying coequalizers in 𝒜.
  Full formalization deferred: Over B uses OverHom which is a separate Cat
  from the ambient 𝒞; wiring up the PreservesCoequalizers type requires
  a Cat instance for Over B, not yet in this file. -/

/-! ## §1.586 Functor categories are cocartesian

  For small 𝒜, the functor category [𝒜, 𝒞] is cocartesian when 𝒞 is, with
  colimits computed pointwise.  The evaluation functors ev_A : [𝒜,𝒞]→𝒞 are
  a collectively faithful family of representations of cocartesian categories.
  Full formalization deferred: functor category machinery not yet available here. -/


end Freyd
