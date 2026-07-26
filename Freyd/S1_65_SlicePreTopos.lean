/-
# The slice of a pre-topos is a pre-topos (§1.65 / Diaconescu support)

  This file builds, for a base object `B` of a category `𝒞`, the structures on the
  slice `Over B` that a pre-topos `𝒞` induces, by transporting them along the *faithful*
  forgetful functor `Σ_B : Over B → 𝒞` (`SliceForget B`, `X ↦ X.dom`).

  The forgetful functor creates these structures because it is faithful, preserves and
  reflects monos (`sigma_preserves_mono` / `sigma_reflects_mono`, §1.531), preserves and
  reflects covers (`cover_f_of_cover` / `cover_of_cover_f`, §1.531), and preserves
  pullbacks (`sliceForget_preserves_isPullback`).  Concretely:

  * `HasImages (Over B)` — the image of `m : X ⟶ Y` is the `𝒞`-image of `m.f`, equipped
    with its induced map to `B`.  Bidirectional mono/cover transport make it the smallest
    slice subobject allowing `m`.  This is the FOUNDATION the relational calculus needs.

  The remaining tower (`EffectiveRegular (Over B)`, `DisjointBinaryCoproduct (Over B)`,
  `HasReflTransClosure (Over B)`) and the final Diaconescu transport are tracked in the
  trailing doc-comment; this file lands the image foundation Sorry-free.
-/
import Freyd.S1_44
import Freyd.S1_45
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_56
import Freyd.S1_59
import Freyd.S1_62
import Freyd.S1_77
import Freyd.S1_64
import Freyd.S1_658_Complement
import Freyd.S1_53_SliceRegular

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

section rung01
variable [HasPullbacks 𝒞]

/-! ## Subobject correspondence `Subobject (Over B) Y ≃ Subobject 𝒞 Y.dom`

  A slice subobject of `Y : Over B` is a slice-monic `S.arr : S.dom ↣ Y`; its underlying
  arrow `S.arr.f : S.dom.dom ↣ Y.dom` is a `𝒞`-mono (Σ preserves monos).  Conversely a
  `𝒞`-mono `m : C ↣ Y.dom` lifts to the slice object `⟨C, m ≫ Y.hom⟩` with slice-monic
  inclusion `⟨m, rfl⟩` (Σ reflects monos). -/

variable {B : 𝒞}

/-- The underlying `𝒞`-subobject of a slice subobject `S` of `Y`. -/
def Subobject.forgetSlice (Y : Over B) (S : Subobject (Over B) Y) : Subobject 𝒞 Y.dom where
  dom := S.dom.dom
  arr := S.arr.f
  monic := sigma_preserves_mono S.arr S.monic

/-- Lift a `𝒞`-subobject `T` of `Y.dom` to a slice subobject of `Y`. -/
def Subobject.liftSlice (Y : Over B) (T : Subobject 𝒞 Y.dom) : Subobject (Over B) Y where
  dom := ⟨T.dom, T.arr ≫ Y.hom⟩
  arr := ⟨T.arr, rfl⟩
  monic := sigma_reflects_mono (⟨T.arr, rfl⟩ : OverHom ⟨T.dom, T.arr ≫ Y.hom⟩ Y) T.monic

/-- A slice subobject `S` allows a slice arrow `m` iff its underlying `𝒞`-subobject allows
    the underlying arrow `m.f`. -/
theorem allows_forgetSlice_iff {Y X : Over B} (S : Subobject (Over B) Y) (m : OverHom X Y) :
    Allows S m ↔ Allows (Subobject.forgetSlice Y S) m.f := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.f, congrArg OverHom.f hg⟩
  · rintro ⟨g, hg⟩
    -- `g : X.dom → S.dom.dom` with `g ≫ S.arr.f = m.f`; promote to a slice arrow.
    have hgf : g ≫ S.arr.f = m.f := hg
    have hgw : g ≫ S.dom.hom = X.hom := by
      have : g ≫ (S.arr.f ≫ Y.hom) = m.f ≫ Y.hom := by rw [← Cat.assoc, hgf]
      rwa [S.arr.w, m.w] at this
    exact ⟨⟨g, hgw⟩, OverHom.ext hg⟩

/-! ## `HasImages (Over B)`

  The image of `m : X ⟶ Y` in `Over B` is the lift of the `𝒞`-image of `m.f`. -/

/-- The slice image of `m : X ⟶ Y`: lift the `𝒞`-image of `m.f` to a slice subobject of `Y`. -/
def sliceImage [HasImages 𝒞] {X Y : Over B} (m : OverHom X Y) : Subobject (Over B) Y :=
  Subobject.liftSlice Y (image m.f)

/-- The slice image is an image: it allows `m` and is below any slice subobject allowing `m`. -/
theorem sliceImage_isImage [HasImages 𝒞] {X Y : Over B} (m : OverHom X Y) :
    IsImage m (sliceImage m) := by
  refine ⟨?_, ?_⟩
  · -- allows `m`: the underlying subobject of the lift of `image m.f` is `image m.f`.
    have hund : Allows (Subobject.forgetSlice Y (Subobject.liftSlice Y (image m.f))) m.f :=
      image_allows m.f
    exact (allows_forgetSlice_iff (Subobject.liftSlice Y (image m.f)) m).mpr hund
  · intro S hS
    -- `S` allows `m` ⟹ underlying allows `m.f` ⟹ `image m.f ≤ S.forgetSlice` ⟹ slice `≤`.
    have hund : Allows (Subobject.forgetSlice Y S) m.f :=
      (allows_forgetSlice_iff S m).mp hS
    obtain ⟨h, hh⟩ := image_min m.f (Subobject.forgetSlice Y S) hund
    -- `h : (image m.f).dom → S.dom.dom`, `h ≫ S.arr.f = (image m.f).arr`.
    have hhf : h ≫ S.arr.f = (image m.f).arr := hh
    have hw : h ≫ S.dom.hom = (Subobject.liftSlice Y (image m.f)).dom.hom := by
      show h ≫ S.dom.hom = (image m.f).arr ≫ Y.hom
      have : h ≫ (S.arr.f ≫ Y.hom) = (image m.f).arr ≫ Y.hom := by rw [← Cat.assoc, hhf]
      rwa [S.arr.w] at this
    exact ⟨⟨h, hw⟩, OverHom.ext hhf⟩

/-- **The slice of a category with images has images.**  Built by transporting the
    `𝒞`-image along the faithful forgetful functor `Σ_B`. -/
instance overHasImages [HasImages 𝒞] (B : 𝒞) : HasImages (Over B) where
  image := sliceImage
  isImage := sliceImage_isImage

/-! ## `RegularCategory (Over B)`

  With `HasImages (Over B)` now in hand, all four `RegularCategory` mixins for `Over B`
  are available: `HasTerminal` (`overHasTerminal`, §1.44), `HasBinaryProducts`
  (`overHasBinaryProducts`, §1.441), `HasPullbacks` (`overHasPullbacks`, §1.441), and
  `PullbacksTransferCovers` (`overPullbacksTransferCovers`, §1.52).  The slice of a regular
  category is regular. -/
instance overRegular (B : 𝒞) [RegularCategory 𝒞] : RegularCategory (Over B) where

/-! ## Rung 1: the forgetful functor on binary relations

  `Σ_B` sends a slice relation `R : BinRel (Over B) X Y` to the `𝒞`-relation on
  `X.dom, Y.dom` with columns `R.colA.f, R.colB.f`.  Joint monicity transports by the
  same object-promotion trick as `sigma_preserves_mono`: a bare span `f, g : W ⟶ R.src.dom`
  equalising both forgotten columns promotes to a slice span (give `W` the structure map
  `f ≫ R.src.hom`), where `R.isMonicPair` cancels it. -/

/-- The underlying `𝒞`-relation of a slice relation `R : BinRel (Over B) X Y`. -/
def BinRel.forgetSlice {X Y : Over B} (R : BinRel (Over B) X Y) :
    BinRel 𝒞 X.dom Y.dom where
  src := R.src.dom
  colA := R.colA.f
  colB := R.colB.f
  isMonicPair := by
    intro W f g hA hB
    -- Promote `f` to the slice span `⟨W, f ≫ R.src.hom⟩ ⟶ R.src`.
    have hgw : g ≫ R.src.hom = f ≫ R.src.hom := by
      have : f ≫ (R.colA.f ≫ X.hom) = g ≫ (R.colA.f ≫ X.hom) := by
        rw [← Cat.assoc, ← Cat.assoc, hA]
      rw [R.colA.w] at this; exact this.symm
    let Wo : Over B := ⟨W, f ≫ R.src.hom⟩
    let fo : OverHom Wo R.src := ⟨f, rfl⟩
    let go : OverHom Wo R.src := ⟨g, hgw⟩
    have := R.isMonicPair fo go (OverHom.ext hA) (OverHom.ext hB)
    exact congrArg OverHom.f this

@[simp] theorem BinRel.forgetSlice_src {X Y : Over B} (R : BinRel (Over B) X Y) :
    R.forgetSlice.src = R.src.dom := rfl
@[simp] theorem BinRel.forgetSlice_colA {X Y : Over B} (R : BinRel (Over B) X Y) :
    R.forgetSlice.colA = R.colA.f := rfl
@[simp] theorem BinRel.forgetSlice_colB {X Y : Over B} (R : BinRel (Over B) X Y) :
    R.forgetSlice.colB = R.colB.f := rfl

/-- `Σ_B` commutes with `reciprocal` on the nose. -/
theorem forgetSlice_reciprocal {X Y : Over B} (R : BinRel (Over B) X Y) :
    (reciprocal R).forgetSlice = reciprocal R.forgetSlice := rfl

/-- `Σ_B` commutes with `graph` on the nose: `Σ_B (graph m) = graph m.f`. -/
theorem forgetSlice_graph {X Y : Over B} (m : OverHom X Y) :
    (graph m).forgetSlice = graph m.f := rfl

/-- `Σ_B` is monotone on relations: a slice `RelHom R ⟶ S` forgets to a `𝒞`
    `RelHom R.forgetSlice ⟶ S.forgetSlice` (its witness arrow is `.f`). -/
theorem forgetSlice_mono_relLe {X Y : Over B} {R S : BinRel (Over B) X Y}
    (h : R ⊂ S) : R.forgetSlice ⊂ S.forgetSlice := by
  obtain ⟨k, hA, hB⟩ := h
  exact ⟨⟨k.f, congrArg OverHom.f hA, congrArg OverHom.f hB⟩⟩

/-- `Σ_B` reflects relation containment: a `𝒞` `RelHom` between forgotten relations
    promotes (object-promotion trick) to a slice `RelHom`. -/
theorem forgetSlice_reflects_relLe {X Y : Over B} {R S : BinRel (Over B) X Y}
    (h : R.forgetSlice ⊂ S.forgetSlice) : R ⊂ S := by
  obtain ⟨k, hA, hB⟩ := h
  -- `k : R.src.dom ⟶ S.src.dom`, `k ≫ S.colA.f = R.colA.f`, etc.  Promote `k`.
  have hkf : k ≫ S.colA.f = R.colA.f := hA
  have hkw : k ≫ S.src.hom = R.src.hom := by
    have : k ≫ (S.colA.f ≫ X.hom) = R.colA.f ≫ X.hom := by rw [← Cat.assoc, hkf]
    rwa [S.colA.w, R.colA.w] at this
  exact ⟨⟨⟨k, hkw⟩, OverHom.ext hA, OverHom.ext hB⟩⟩

/-! ### `Σ_B` commutes with `⊚` up to the canonical comparison iso

  The slice composite `R ⊚ S` is the slice image of the slice span over the *slice* pullback
  `R.colB ×_Y S.colA`; forgetting, the underlying span lives over the base pullback
  `R.colB.f ×_{Y.dom} S.colA.f`, and the slice image forgets to the base image (definitionally,
  by `overHasImages = liftSlice ∘ image`).  The base composite `Σ_B R ⊚ Σ_B S` is the base image
  of the base span over the *base* pullback `R.colB.f ×_{Y.dom} S.colA.f`.  Both spans land on the
  same legs once the two chosen pullbacks are compared; `relLe_of_cover_factor` (cover⊥mono) gives
  the containment each way without identifying the chosen pullbacks/images on the nose. -/

section composeComparison
variable [RegularCategory 𝒞] {X Y Z : Over B}

/-- `Σ_B (R ⊚ S) ⊂ (Σ_B R) ⊚ (Σ_B S)`: the slice composite forgets into the base composite. -/
theorem forgetSlice_compose_le (R : BinRel (Over B) X Y) (S : BinRel (Over B) Y Z) :
    (R ⊚ S).forgetSlice ⊂ (R.forgetSlice ⊚ S.forgetSlice) := by
  -- slice pullback of the inner legs, and its forgotten (base) span
  let pbs := HasPullbacks.has R.colB S.colA
  let spans : pbs.cone.pt ⟶ (overProdPt X Z) :=
    pair (pbs.cone.π₁ ⊚ R.colA) (pbs.cone.π₂ ⊚ S.colB)
  -- base pullback of the forgotten legs, with its comparison map from `pbs.cone.pt.dom`
  let pbc := HasPullbacks.has R.colB.f S.colA.f
  have hpbsw : (pbs.cone.π₁).f ≫ R.colB.f = (pbs.cone.π₂).f ≫ S.colA.f :=
    congrArg OverHom.f pbs.cone.w
  let cmp : pbs.cone.pt.dom ⟶ pbc.cone.pt :=
    pbc.lift ⟨pbs.cone.pt.dom, (pbs.cone.π₁).f, (pbs.cone.π₂).f, hpbsw⟩
  have hcmp₁ : cmp ≫ pbc.cone.π₁ = (pbs.cone.π₁).f := pbc.lift_fst _
  have hcmp₂ : cmp ≫ pbc.cone.π₂ = (pbs.cone.π₂).f := pbc.lift_snd _
  let spanc : pbc.cone.pt ⟶ prod X.dom Z.dom :=
    pair (pbc.cone.π₁ ≫ R.colA.f) (pbc.cone.π₂ ≫ S.colB.f)
  -- the cover onto `(R⊚S).forgetSlice.src = (image spans.f).dom` is `image.lift spans.f`
  refine relLe_of_cover_factor (Y := R.forgetSlice ⊚ S.forgetSlice)
    (image.lift spans.f) (image_lift_cover spans.f)
    (cmp ≫ image.lift spanc) ?_ ?_
  · -- column A
    show (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ fst)
        = image.lift spans.f ≫ ((R ⊚ S).forgetSlice.colA)
    have hL : (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ fst)
        = (pbs.cone.π₁).f ≫ R.colA.f := by
      calc (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ fst)
          = cmp ≫ ((image.lift spanc ≫ (image spanc).arr) ≫ fst) := by
            rw [Cat.assoc cmp, ← Cat.assoc (image.lift spanc)]
        _ = cmp ≫ (spanc ≫ fst) := by rw [image.lift_fac]
        _ = cmp ≫ (pbc.cone.π₁ ≫ R.colA.f) := by rw [show spanc ≫ fst = _ from fst_pair _ _]
        _ = (cmp ≫ pbc.cone.π₁) ≫ R.colA.f := (Cat.assoc _ _ _).symm
        _ = (pbs.cone.π₁).f ≫ R.colA.f := by rw [hcmp₁]
    have hR : image.lift spans.f ≫ ((R ⊚ S).forgetSlice.colA)
        = (pbs.cone.π₁).f ≫ R.colA.f := by
      calc image.lift spans.f ≫ ((image spans.f).arr ≫ (overProdFst X Z).f)
          = (image.lift spans.f ≫ (image spans.f).arr) ≫ (overProdFst X Z).f := (Cat.assoc _ _ _).symm
        _ = spans.f ≫ (overProdFst X Z).f := by rw [image.lift_fac]
        _ = (spans ⊚ overProdFst X Z).f := rfl
        _ = (pbs.cone.π₁ ⊚ R.colA).f := by
            rw [show spans ⊚ overProdFst X Z = _ from OverHom.ext ((HasPullbacks.has X.hom Z.hom).lift_fst _)]
        _ = (pbs.cone.π₁).f ≫ R.colA.f := rfl
    rw [hL, hR]
  · -- column B (mirror)
    show (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ snd)
        = image.lift spans.f ≫ ((R ⊚ S).forgetSlice.colB)
    have hL : (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ snd)
        = (pbs.cone.π₂).f ≫ S.colB.f := by
      calc (cmp ≫ image.lift spanc) ≫ ((image spanc).arr ≫ snd)
          = cmp ≫ ((image.lift spanc ≫ (image spanc).arr) ≫ snd) := by
            rw [Cat.assoc cmp, ← Cat.assoc (image.lift spanc)]
        _ = cmp ≫ (spanc ≫ snd) := by rw [image.lift_fac]
        _ = cmp ≫ (pbc.cone.π₂ ≫ S.colB.f) := by rw [show spanc ≫ snd = _ from snd_pair _ _]
        _ = (cmp ≫ pbc.cone.π₂) ≫ S.colB.f := (Cat.assoc _ _ _).symm
        _ = (pbs.cone.π₂).f ≫ S.colB.f := by rw [hcmp₂]
    have hR : image.lift spans.f ≫ ((R ⊚ S).forgetSlice.colB)
        = (pbs.cone.π₂).f ≫ S.colB.f := by
      calc image.lift spans.f ≫ ((image spans.f).arr ≫ (overProdSnd X Z).f)
          = (image.lift spans.f ≫ (image spans.f).arr) ≫ (overProdSnd X Z).f := (Cat.assoc _ _ _).symm
        _ = spans.f ≫ (overProdSnd X Z).f := by rw [image.lift_fac]
        _ = (spans ⊚ overProdSnd X Z).f := rfl
        _ = (pbs.cone.π₂ ⊚ S.colB).f := by
            rw [show spans ⊚ overProdSnd X Z = _ from OverHom.ext ((HasPullbacks.has X.hom Z.hom).lift_snd _)]
        _ = (pbs.cone.π₂).f ≫ S.colB.f := rfl
    rw [hL, hR]

/-- `(Σ_B R) ⊚ (Σ_B S) ⊂ Σ_B (R ⊚ S)`: the base composite forgets back into the slice
    composite.  The base pullback `pbc` maps into the forgotten slice pullback (a base
    pullback by `sliceForget_preserves_isPullback`); the rest mirrors `forgetSlice_compose_le`. -/
theorem le_forgetSlice_compose (R : BinRel (Over B) X Y) (S : BinRel (Over B) Y Z) :
    (R.forgetSlice ⊚ S.forgetSlice) ⊂ (R ⊚ S).forgetSlice := by
  let pbs := HasPullbacks.has R.colB S.colA
  let spans : pbs.cone.pt ⟶ (overProdPt X Z) :=
    pair (pbs.cone.π₁ ⊚ R.colA) (pbs.cone.π₂ ⊚ S.colB)
  let pbc := HasPullbacks.has R.colB.f S.colA.f
  let spanc : pbc.cone.pt ⟶ prod X.dom Z.dom :=
    pair (pbc.cone.π₁ ≫ R.colA.f) (pbc.cone.π₂ ≫ S.colB.f)
  -- the forgotten slice pullback is a base pullback; lift `pbc.cone` into it.
  have hsforget : (sliceConeForget pbs.cone).IsPullback :=
    sliceForget_preserves_isPullback pbs.cone pbs.cone_isPullback
  obtain ⟨cmp, ⟨hcmp₁0, hcmp₂0⟩, _⟩ := hsforget pbc.cone
  -- restate with the defeq-normalised legs `(pbs.cone.π·).f`.
  have hcmp₁ : cmp ≫ (pbs.cone.π₁).f = pbc.cone.π₁ := hcmp₁0
  have hcmp₂ : cmp ≫ (pbs.cone.π₂).f = pbc.cone.π₂ := hcmp₂0
  refine relLe_of_cover_factor (X := R.forgetSlice ⊚ S.forgetSlice)
    (image.lift spanc) (image_lift_cover spanc)
    (cmp ≫ image.lift spans.f) ?_ ?_
  · show (cmp ≫ image.lift spans.f) ≫ ((R ⊚ S).forgetSlice.colA)
        = image.lift spanc ≫ ((image spanc).arr ≫ fst)
    have hL : (cmp ≫ image.lift spans.f) ≫ ((R ⊚ S).forgetSlice.colA)
        = pbc.cone.π₁ ≫ R.colA.f := by
      calc (cmp ≫ image.lift spans.f) ≫ ((image spans.f).arr ≫ (overProdFst X Z).f)
          = cmp ≫ ((image.lift spans.f ≫ (image spans.f).arr) ≫ (overProdFst X Z).f) := by
            rw [Cat.assoc cmp, ← Cat.assoc (image.lift spans.f)]
        _ = cmp ≫ (spans.f ≫ (overProdFst X Z).f) := by rw [image.lift_fac]
        _ = cmp ≫ ((spans ⊚ overProdFst X Z).f) := rfl
        _ = cmp ≫ ((pbs.cone.π₁ ⊚ R.colA).f) := by
            rw [show spans ⊚ overProdFst X Z = _ from OverHom.ext ((HasPullbacks.has X.hom Z.hom).lift_fst _)]
        _ = cmp ≫ ((pbs.cone.π₁).f ≫ R.colA.f) := rfl
        _ = (cmp ≫ (pbs.cone.π₁).f) ≫ R.colA.f := (Cat.assoc _ _ _).symm
        _ = pbc.cone.π₁ ≫ R.colA.f := by rw [hcmp₁]
    have hR : image.lift spanc ≫ ((image spanc).arr ≫ fst) = pbc.cone.π₁ ≫ R.colA.f := by
      calc image.lift spanc ≫ ((image spanc).arr ≫ fst)
          = (image.lift spanc ≫ (image spanc).arr) ≫ fst := (Cat.assoc _ _ _).symm
        _ = spanc ≫ fst := by rw [image.lift_fac]
        _ = pbc.cone.π₁ ≫ R.colA.f := fst_pair _ _
    rw [hL, hR]
  · show (cmp ≫ image.lift spans.f) ≫ ((R ⊚ S).forgetSlice.colB)
        = image.lift spanc ≫ ((image spanc).arr ≫ snd)
    have hL : (cmp ≫ image.lift spans.f) ≫ ((R ⊚ S).forgetSlice.colB)
        = pbc.cone.π₂ ≫ S.colB.f := by
      calc (cmp ≫ image.lift spans.f) ≫ ((image spans.f).arr ≫ (overProdSnd X Z).f)
          = cmp ≫ ((image.lift spans.f ≫ (image spans.f).arr) ≫ (overProdSnd X Z).f) := by
            rw [Cat.assoc cmp, ← Cat.assoc (image.lift spans.f)]
        _ = cmp ≫ (spans.f ≫ (overProdSnd X Z).f) := by rw [image.lift_fac]
        _ = cmp ≫ ((spans ⊚ overProdSnd X Z).f) := rfl
        _ = cmp ≫ ((pbs.cone.π₂ ⊚ S.colB).f) := by
            rw [show spans ⊚ overProdSnd X Z = _ from OverHom.ext ((HasPullbacks.has X.hom Z.hom).lift_snd _)]
        _ = cmp ≫ ((pbs.cone.π₂).f ≫ S.colB.f) := rfl
        _ = (cmp ≫ (pbs.cone.π₂).f) ≫ S.colB.f := (Cat.assoc _ _ _).symm
        _ = pbc.cone.π₂ ≫ S.colB.f := by rw [hcmp₂]
    have hR : image.lift spanc ≫ ((image spanc).arr ≫ snd) = pbc.cone.π₂ ≫ S.colB.f := by
      calc image.lift spanc ≫ ((image spanc).arr ≫ snd)
          = (image.lift spanc ≫ (image spanc).arr) ≫ snd := (Cat.assoc _ _ _).symm
        _ = spanc ≫ snd := by rw [image.lift_fac]
        _ = pbc.cone.π₂ ≫ S.colB.f := snd_pair _ _
    rw [hL, hR]

/-- `Σ_B (R ⊚ S)` and `(Σ_B R) ⊚ (Σ_B S)` are mutually contained: the comparison iso. -/
theorem forgetSlice_compose_iso (R : BinRel (Over B) X Y) (S : BinRel (Over B) Y Z) :
    ((R ⊚ S).forgetSlice ⊂ (R.forgetSlice ⊚ S.forgetSlice)) ∧
    ((R.forgetSlice ⊚ S.forgetSlice) ⊂ (R ⊚ S).forgetSlice) :=
  ⟨forgetSlice_compose_le R S, le_forgetSlice_compose R S⟩

end composeComparison

end rung01

variable {B : 𝒞}

/-! ## Rung 2: `EffectiveRegular (Over B)`

  A slice equivalence relation `E` forgets to a `𝒞`-equivalence relation `E̅` (reflexivity and
  symmetry transport on the nose; transitivity uses the rung-1 comparison).  `𝒞`'s effectiveness
  hands a cover `q̄ : X.dom ↠ Q₀` with `E̅ ≅ q̄q̄°`.  Both legs `E.colA.f, E.colB.f` equalise
  `X.hom`, and `q̄` coequalises them (`cover_is_coequalizer_of_level`), so `X.hom = q̄ ≫ b` for a
  unique `b : Q₀ ⟶ B`.  Then `q : X ↠ ⟨Q₀, b⟩` is a slice cover whose slice level forgets back to
  `E̅`; reflecting the `𝒞`-iso through `Σ_B` (faithful) and the rung-1 comparison gives the slice
  iso `E ≅ q q°`, i.e. `IsEffective E`. -/

section effective
-- `EffectiveRegular 𝒞` bundles `HasPullbacks`/`HasImages`/`HasBinaryProducts`; using it as the
-- sole source (no standalone `[HasPullbacks 𝒞]` here) keeps a single instance, so the slice
-- relation predicates and `EffectiveRegular.effective` agree without a diamond.
variable [EffectiveRegular 𝒞] {X : Over B}

/-- The forgotten relation of a slice equivalence relation is a `𝒞`-equivalence relation. -/
theorem forgetSlice_equivalenceRelation (E : BinRel (Over B) X X)
    (hE : EquivalenceRelation E) : EquivalenceRelation E.forgetSlice := by
  obtain ⟨⟨ho, hoA, hoB⟩, hsym, htrans⟩ := hE
  refine ⟨⟨ho.f, ?_, ?_⟩, ?_, ?_⟩
  · -- reflexivity, column A: `ho.f ≫ E.colA.f = (ho ⊚ E.colA).f = id`
    show ho.f ≫ E.colA.f = Cat.id X.dom
    exact congrArg OverHom.f hoA
  · show ho.f ≫ E.colB.f = Cat.id X.dom
    exact congrArg OverHom.f hoB
  · -- symmetry: forget the slice `RelHom E ⟶ E°`; `(E°).forgetSlice = (E.forgetSlice)°` (rfl).
    exact forgetSlice_mono_relLe hsym
  · -- transitivity: `E̅ ⊚ E̅ ⊂ (E ⊚ E).forgetSlice ⊂ E̅`.
    exact rel_le_trans (le_forgetSlice_compose E E) (forgetSlice_mono_relLe htrans)

/-- Both legs of `E̅ = E.forgetSlice` equalise `X.hom` (both compose to `E.src.hom`). -/
theorem forgetSlice_legs_equalise (E : BinRel (Over B) X X) :
    E.forgetSlice.colA ≫ X.hom = E.forgetSlice.colB ≫ X.hom := by
  show E.colA.f ≫ X.hom = E.colB.f ≫ X.hom
  rw [E.colA.w, E.colB.w]

/-- `Σ_B (graph q ⊚ (graph q)°) ` versus `graph q.f ⊚ (graph q.f)°`: contained each way
    via rung 1 and the on-the-nose `forgetSlice_graph` / `forgetSlice_reciprocal`. -/
theorem forgetSlice_graphComp_iso {Q : Over B} (q : OverHom X Q) :
    ((graph q ⊚ (graph q)°).forgetSlice ⊂ (graph q.f ⊚ (graph q.f)°)) ∧
    ((graph q.f ⊚ (graph q.f)°) ⊂ (graph q ⊚ (graph q)°).forgetSlice) := by
  have he : (graph q).forgetSlice = graph q.f := forgetSlice_graph q
  have hr : ((graph q)°).forgetSlice = (graph q.f)° := by
    rw [forgetSlice_reciprocal, he]
  refine ⟨?_, ?_⟩
  · have := forgetSlice_compose_le (graph q) ((graph q)°)
    rwa [he, hr] at this
  · have := le_forgetSlice_compose (graph q) ((graph q)°)
    rwa [he, hr] at this

/-- **Rung 2: every slice equivalence relation is effective.**  Forget to `𝒞`, apply `𝒞`'s
    effectiveness for the cover `q̄`, factor `X.hom = q̄ ≫ b` (leg-equalisation + coequaliser),
    lift `q̄` to a slice cover `q : X ↠ ⟨Q₀, b⟩`, and reflect the `𝒞`-iso `E̅ ≅ q̄q̄°` back through
    `Σ_B` (faithful) using rung 1. -/
theorem sliceIsEffective (E : BinRel (Over B) X X) (hE : EquivalenceRelation E) :
    IsEffective E := by
  -- forget and apply 𝒞-effectiveness
  obtain ⟨_, Q₀, qbar, hqcov, hf1, hf2⟩ :=
    EffectiveRegular.effective E.forgetSlice (forgetSlice_equivalenceRelation E hE)
  -- hf1 : E̅ ⊂ graph q̄ ⊚ graph q̄°,  hf2 : graph q̄ ⊚ graph q̄° ⊂ E̅
  -- `X.hom` equalises `q̄`'s kernel pair, so it factors `q̄ ≫ b`.
  have hkpb : kp₁ (f := qbar) ≫ X.hom = kp₂ (f := qbar) ≫ X.hom := by
    obtain ⟨w, hwA0, hwB0⟩ := rel_le_trans (kernelPairRel_le_level qbar) hf2
    -- restate with the defeq-normalised kernel-pair legs.
    have hwA : w ≫ E.forgetSlice.colA = kp₁ (f := qbar) := hwA0
    have hwB : w ≫ E.forgetSlice.colB = kp₂ (f := qbar) := hwB0
    calc kp₁ (f := qbar) ≫ X.hom = (w ≫ E.forgetSlice.colA) ≫ X.hom := by rw [hwA]
      _ = w ≫ (E.forgetSlice.colA ≫ X.hom) := Cat.assoc _ _ _
      _ = w ≫ (E.forgetSlice.colB ≫ X.hom) := by rw [forgetSlice_legs_equalise]
      _ = (w ≫ E.forgetSlice.colB) ≫ X.hom := (Cat.assoc _ _ _).symm
      _ = kp₂ (f := qbar) ≫ X.hom := by rw [hwB]
  obtain ⟨b, hqb, _⟩ := cover_is_coequalizer_of_level qbar hqcov X.hom hkpb
  -- slice quotient object and slice cover
  let Q : Over B := ⟨Q₀, b⟩
  let q : OverHom X Q := ⟨qbar, hqb⟩
  have hqcov_slice : Cover (𝒞 := Over B) q := cover_of_cover_f q hqcov
  obtain ⟨hgc1, hgc2⟩ := forgetSlice_graphComp_iso q
  refine ⟨hE, Q, q, hqcov_slice, ?_, ?_⟩
  · -- E ⊂ graph q ⊚ graph q°  (reflect: E̅ ⊂ (graph q ⊚ graph q°).forgetSlice)
    apply forgetSlice_reflects_relLe
    exact rel_le_trans hf1 hgc2
  · -- graph q ⊚ graph q° ⊂ E  (reflect: (...).forgetSlice ⊂ E̅)
    apply forgetSlice_reflects_relLe
    exact rel_le_trans hgc1 hf2

end effective

/-- **The slice of an effective regular category is effective regular** (rung 2). -/
instance overEffectiveRegular (B : 𝒞) [EffectiveRegular 𝒞] : EffectiveRegular (Over B) where
  effective E hE := sliceIsEffective E hE

/-! ## Rung 4: `HasReflTransClosure (Over B)`

  The reflexive-transitive closure of a slice relation `R` is the slice lift of `rtc R̄`
  (`R̄ = R.forgetSlice`).  `R̄`'s legs equalise `A.hom` (they come from slice arrows), and
  `kernelPairRel A.hom` is a reflexive+transitive relation containing `R̄`, so by `rtc`-minimality
  `rtc R̄`'s legs *also* equalise `A.hom`; hence `rtc R̄` lifts to a slice relation `M` with
  `M.forgetSlice = rtc R̄` (on the nose).  Reflexivity/transitivity/minimality then transport
  through `forgetSlice_reflects_relLe` and the rung-1 comparison. -/

section rtc
variable [RegularCategory 𝒞] [HasReflTransClosure 𝒞] {A : Over B}

/-- Lift a `𝒞`-relation on `A.dom` whose legs equalise `A.hom` back to a slice relation on `A`.
    Round-trips with `forgetSlice` on the nose. -/
def BinRel.liftSlice (M : BinRel 𝒞 A.dom A.dom)
    (hleg : M.colA ≫ A.hom = M.colB ≫ A.hom) : BinRel (Over B) A A where
  src := ⟨M.src, M.colA ≫ A.hom⟩
  colA := ⟨M.colA, rfl⟩
  colB := ⟨M.colB, hleg.symm⟩
  isMonicPair := by
    intro W f g hA hB
    apply OverHom.ext
    exact M.isMonicPair f.f g.f (congrArg OverHom.f hA) (congrArg OverHom.f hB)

@[simp] theorem BinRel.forgetSlice_liftSlice (M : BinRel 𝒞 A.dom A.dom)
    (hleg : M.colA ≫ A.hom = M.colB ≫ A.hom) :
    (BinRel.liftSlice M hleg).forgetSlice = M := rfl

/-- `R.forgetSlice`'s legs equalise `A.hom` (they are slice arrows). -/
theorem forgetSlice_endo_legs_equalise (R : BinRel (Over B) A A) :
    R.forgetSlice.colA ≫ A.hom = R.forgetSlice.colB ≫ A.hom := by
  show R.colA.f ≫ A.hom = R.colB.f ≫ A.hom
  rw [R.colA.w, R.colB.w]

/-- `rtc R̄`'s legs equalise `A.hom`: `rtc R̄ ⊂ kernelPairRel A.hom` (a reflexive+transitive
    relation containing `R̄`), and the latter equalises by `kp_sq`. -/
theorem rtc_forgetSlice_legs_equalise (R : BinRel (Over B) A A) :
    (rtc R.forgetSlice).colA ≫ A.hom = (rtc R.forgetSlice).colB ≫ A.hom := by
  -- `R̄ ⊂ kernelPairRel A.hom`: the kernel-pair lift of `R̄`'s (equalising) legs is the witness.
  have hRle : RelLe R.forgetSlice (kernelPairRel A.hom) :=
    ⟨⟨(HasPullbacks.has A.hom A.hom).lift
        ⟨R.forgetSlice.src, R.forgetSlice.colA, R.forgetSlice.colB,
          forgetSlice_endo_legs_equalise R⟩,
      kp_lift_p₁ _ _ (forgetSlice_endo_legs_equalise R),
      kp_lift_p₂ _ _ (forgetSlice_endo_legs_equalise R)⟩⟩
  -- `kernelPairRel A.hom` is reflexive + transitive
  obtain ⟨hrefl, _, htrans⟩ := level_is_equivalence_relation A.hom
  have hreflD : IsReflexive (kernelPairRel A.hom) := by
    obtain ⟨h, hA, hB⟩ := hrefl
    exact ⟨⟨h, by simpa [graph, Cat.id_comp] using hA, by simpa [graph, Cat.id_comp] using hB⟩⟩
  -- `rtc R̄ ⊂ kernelPairRel A.hom`
  obtain ⟨w, hwA, hwB⟩ := rtc_minimal R.forgetSlice (kernelPairRel A.hom) hRle hreflD htrans
  calc (rtc R.forgetSlice).colA ≫ A.hom
      = (w ≫ (kernelPairRel A.hom).colA) ≫ A.hom := by rw [hwA]
    _ = w ≫ ((kernelPairRel A.hom).colA ≫ A.hom) := Cat.assoc _ _ _
    _ = w ≫ ((kernelPairRel A.hom).colB ≫ A.hom) := by
        rw [show (kernelPairRel A.hom).colA ≫ A.hom = (kernelPairRel A.hom).colB ≫ A.hom
          from kp_sq]
    _ = (w ≫ (kernelPairRel A.hom).colB) ≫ A.hom := (Cat.assoc _ _ _).symm
    _ = (rtc R.forgetSlice).colB ≫ A.hom := by rw [hwB]

/-- The slice reflexive-transitive closure: lift `rtc R̄` back to the slice. -/
def sliceTransRefClos (R : BinRel (Over B) A A) : TransRefClos R where
  clos := BinRel.liftSlice (rtc R.forgetSlice) (rtc_forgetSlice_legs_equalise R)
  le := by
    apply forgetSlice_reflects_relLe
    rw [BinRel.forgetSlice_liftSlice]
    exact le_rtc R.forgetSlice
  refl := by
    -- `1_A ⊂ M`: reflect `graph (id A.dom) ⊂ rtc R̄`; `(graph (id A)).forgetSlice = graph (id A.dom)`.
    have h := forgetSlice_reflects_relLe (R := graph (Cat.id A))
      (S := BinRel.liftSlice (rtc R.forgetSlice) (rtc_forgetSlice_legs_equalise R))
    apply h
    rw [BinRel.forgetSlice_liftSlice]
    -- `(graph (Cat.id A)).forgetSlice = graph (Cat.id A.dom)` on the nose.
    show graph (Cat.id A.dom) ⊂ rtc R.forgetSlice
    exact (HasReflTransClosure.transRefClos R.forgetSlice).refl
  trans := by
    -- `M ⊚ M ⊂ M`: reflect to `(M ⊚ M).forgetSlice ⊂ M̄`; forward-compare then `rtc`-transitivity.
    apply forgetSlice_reflects_relLe
    rw [BinRel.forgetSlice_liftSlice]
    refine rel_le_trans (forgetSlice_compose_le _ _) ?_
    rw [BinRel.forgetSlice_liftSlice]
    exact rtc_transitive R.forgetSlice
  minimal := by
    intro T hRT hReflT hTransT
    -- reflect `M̄ ⊂ T̄` via `rtc`-minimality on `R̄ ⊂ T̄`, `T̄` reflexive + transitive.
    apply forgetSlice_reflects_relLe
    rw [BinRel.forgetSlice_liftSlice]
    refine rtc_minimal R.forgetSlice T.forgetSlice (forgetSlice_mono_relLe hRT) ?_ ?_
    · -- `T̄` reflexive: reflect `graph (id A.dom) ⊂ T̄` from slice `1_A ⊂ T`.
      have := forgetSlice_mono_relLe hReflT
      -- `(graph (Cat.id A)).forgetSlice = graph (Cat.id A.dom)`.
      exact this
    · -- `T̄` transitive: `T̄ ⊚ T̄ ⊂ (T ⊚ T).forgetSlice ⊂ T̄`.
      exact rel_le_trans (le_forgetSlice_compose T T) (forgetSlice_mono_relLe hTransT)

end rtc

/-- **The slice of a category with reflexive-transitive closures has them** (rung 4). -/
instance overHasReflTransClosure (B : 𝒞) [RegularCategory 𝒞] [HasReflTransClosure 𝒞] :
    HasReflTransClosure (Over B) where
  transRefClos R := sliceTransRefClos R

/-! ## Rung 3: `DisjointBinaryCoproduct (Over B)`

  The heaviest rung.  Its mathematical content is entirely *transport along the faithful
  forgetful functor* `Σ_B`: a slice subobject of `Y : Over B` IS a `𝒞`-subobject of `Y.dom`
  (the structure map rides along), via the round-tripping pair `Subobject.forgetSlice` /
  `Subobject.liftSlice` (`forgetSlice (liftSlice T) = T` on the nose).  So the ENTIRE
  `PreLogos (Over B)` lattice structure is the `𝒞` one re-attached to the structure map:

  * `bottom A := liftSlice (bottom A.dom)`,
  * `union S T := liftSlice (union (forgetSlice S) (forgetSlice T))`,
  * `InverseImage` transports because `Σ_B` preserves pullbacks
    (`sliceForget_preserves_isPullback`).

  The only genuinely new construction is the slice coproduct `X + Y` = `X.dom + Y.dom` with
  structure map `case X.hom Y.hom` (copairing); the four §1.621 disjointness fields then
  transport from `𝒞`'s `DisjointBinaryCoproduct` through the subobject identification. -/

section rung3
variable {B : 𝒞} [HasPullbacks 𝒞]

/-! ### Subobject correspondence is an order-iso `Sub (Over B) Y ≃ Sub 𝒞 Y.dom`

  `forgetSlice`/`liftSlice` are mutually monotone and `forgetSlice ∘ liftSlice = id` on the
  nose, so each lattice operation transports field-for-field. -/

/-- `forgetSlice` is monotone: a slice `S ≤ T` forgets to `S.forgetSlice ≤ T.forgetSlice`. -/
theorem Subobject.forgetSlice_mono {Y : Over B} {S T : Subobject (Over B) Y}
    (h : S.le T) : (Subobject.forgetSlice Y S).le (Subobject.forgetSlice Y T) := by
  obtain ⟨g, hg⟩ := h; exact ⟨g.f, congrArg OverHom.f hg⟩

/-- `forgetSlice` reflects `≤`: promote the underlying factorization arrow to a slice arrow. -/
theorem Subobject.forgetSlice_reflects {Y : Over B} {S T : Subobject (Over B) Y}
    (h : (Subobject.forgetSlice Y S).le (Subobject.forgetSlice Y T)) : S.le T := by
  obtain ⟨g, hg⟩ := h
  have hgf : g ≫ T.arr.f = S.arr.f := hg
  have hgw : g ≫ T.dom.hom = S.dom.hom := by
    have : g ≫ (T.arr.f ≫ Y.hom) = S.arr.f ≫ Y.hom := by rw [← Cat.assoc, hgf]
    rwa [T.arr.w, S.arr.w] at this
  exact ⟨⟨g, hgw⟩, OverHom.ext hgf⟩

/-- `liftSlice` is monotone: a `𝒞` `S ≤ T` lifts to a slice `liftSlice S ≤ liftSlice T`. -/
theorem Subobject.liftSlice_mono {Y : Over B} {S T : Subobject 𝒞 Y.dom}
    (h : S.le T) : (Subobject.liftSlice Y S).le (Subobject.liftSlice Y T) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨⟨g, ?_⟩, OverHom.ext hg⟩
  show g ≫ (T.arr ≫ Y.hom) = S.arr ≫ Y.hom
  rw [← Cat.assoc, hg]

/-! ### `Σ_B` transports the inverse image (it preserves pullbacks)

  The slice inverse image `InverseImage (Over B) f S` is the slice pullback of `f` along
  `S.arr`; forgetting, that slice pullback is a *base* pullback of `(f.f, S.forgetSlice.arr)`
  (`sliceForget_preserves_isPullback`), hence mutually `≤` with the chosen base inverse image
  `InverseImage f.f S.forgetSlice`. -/

/-- The forgotten slice inverse image is below the base inverse image. -/
theorem forgetSlice_invImage_le {X Y : Over B} (f : OverHom X Y) (S : Subobject (Over B) Y) :
    Subobject.le (Subobject.forgetSlice X (InverseImage f S))
                 (InverseImage f.f (Subobject.forgetSlice Y S)) := by
  let pbc := HasPullbacks.has f.f (Subobject.forgetSlice Y S).arr
  exact ⟨pbc.lift (sliceConeForget (overPullbackCone f S.arr)),
    pbc.lift_fst (sliceConeForget (overPullbackCone f S.arr))⟩

/-- The base inverse image is below the forgotten slice inverse image. -/
theorem le_forgetSlice_invImage {X Y : Over B} (f : OverHom X Y) (S : Subobject (Over B) Y) :
    Subobject.le (InverseImage f.f (Subobject.forgetSlice Y S))
                 (Subobject.forgetSlice X (InverseImage f S)) := by
  have hfor : (sliceConeForget (B := B) (overPullbackCone f S.arr)).IsPullback :=
    sliceForget_preserves_isPullback _ ((overHasPullbacks B).has f S.arr).cone_isPullback
  obtain ⟨h, ⟨h₁, _⟩, _⟩ := hfor (HasPullbacks.has f.f (Subobject.forgetSlice Y S).arr).cone
  exact ⟨h, h₁⟩

end rung3

/-! ### Slice binary coproducts (the one genuinely new construction)

  `X + Y` in `Over B` is `X.dom + Y.dom` with structure map `case X.hom Y.hom`; the injections
  are the `𝒞` injections (as slice arrows), and the universal property copairs. -/

open HasBinaryCoproducts in
/-- **The slice of a category with binary coproducts has binary coproducts.**  The coproduct of
    `X→B`, `Y→B` is `X.dom + Y.dom → B` via the copairing `case X.hom Y.hom`. -/
instance overHasBinaryCoproducts (B : 𝒞) [HasBinaryCoproducts 𝒞] :
    HasBinaryCoproducts (Over B) where
  coprod X Y := ⟨coprod X.dom Y.dom, case X.hom Y.hom⟩
  inl {X Y} := ⟨inl, case_inl _ _⟩
  inr {X Y} := ⟨inr, case_inr _ _⟩
  case {W X Y} f g := ⟨case f.f g.f, by
    apply case_uniq
    · rw [← Cat.assoc, case_inl, f.w]
    · rw [← Cat.assoc, case_inr, g.w]⟩
  case_inl {W X Y} f g := OverHom.ext (case_inl _ _)
  case_inr {W X Y} f g := OverHom.ext (case_inr _ _)
  case_uniq {W X Y} f g h h1 h2 :=
    OverHom.ext (case_uniq _ _ h.f (congrArg OverHom.f h1) (congrArg OverHom.f h2))

/-! ### `PreLogos (Over B)` by domain transport

  Every lattice field is the `𝒞` operation on `Y.dom`'s subobject lattice, re-attached to the
  structure map.  `bottom`/`union`/`inverse image` all round-trip through `forgetSlice`. -/

section overPreLogos
variable [PreLogos 𝒞]

/-- `forgetSlice` is a retraction of `liftSlice` on the nose. -/
@[simp] theorem forgetSlice_liftSlice (Y : Over B) (T : Subobject 𝒞 Y.dom) :
    Subobject.forgetSlice Y (Subobject.liftSlice Y T) = T := rfl

/-- Slice subobject unions: lift the `𝒞`-union of the forgotten subobjects. -/
instance overHasSubobjectUnions (B : 𝒞) : HasSubobjectUnions (Over B) where
  union {Y} S T := Subobject.liftSlice Y
    (HasSubobjectUnions.union (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T))
  union_left {Y} S T := by
    apply Subobject.forgetSlice_reflects
    rw [forgetSlice_liftSlice]
    exact HasSubobjectUnions.union_left _ _
  union_right {Y} S T := by
    apply Subobject.forgetSlice_reflects
    rw [forgetSlice_liftSlice]
    exact HasSubobjectUnions.union_right _ _
  union_min {Y} S T U hSU hTU := by
    apply Subobject.forgetSlice_reflects
    rw [forgetSlice_liftSlice]
    exact HasSubobjectUnions.union_min _ _ _
      (Subobject.forgetSlice_mono hSU) (Subobject.forgetSlice_mono hTU)

@[simp] theorem forgetSlice_union (Y : Over B) (S T : Subobject (Over B) Y) :
    Subobject.forgetSlice Y (HasSubobjectUnions.union S T)
      = HasSubobjectUnions.union (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T) := rfl

/-- **The slice of a pre-logos is a pre-logos.**  Subobject lattices, bottom, and inverse-image
    preservation all transport from `𝒞`'s lattice on `Y.dom` along the subobject identification
    `Sub (Over B) Y ≃ Sub 𝒞 Y.dom`. -/
instance overPreLogos (B : 𝒞) : PreLogos (Over B) where
  bottom A := Subobject.liftSlice A (PreLogos.bottom A.dom)
  bottom_min {A} S := by
    apply Subobject.forgetSlice_reflects
    rw [forgetSlice_liftSlice]
    exact PreLogos.bottom_min _
  bottom_dom_iso A A' := by
    -- both slice-bottom domains have `𝒞`-domain the coterminator `0`, hence iso; promote
    -- the `𝒞`-iso to a slice iso using uniqueness of maps out of an initial object.
    letI hCot := minimal_subobject_of_one_is_coterminator (𝒞 := 𝒞) ‹PreLogos 𝒞›
    have h1 : Isomorphic (PreLogos.bottom A.dom).dom hCot.zero := PreLogos.bottom_dom_iso A.dom _
    have h2 : Isomorphic (PreLogos.bottom A'.dom).dom hCot.zero := PreLogos.bottom_dom_iso A'.dom _
    obtain ⟨g, ginv, hgg, hgg'⟩ := isomorphic_trans h1 (isomorphic_symm h2)
    obtain ⟨φ, φinv, hφ, _⟩ := h1
    have uniqA : ∀ {Z : 𝒞} (p q : (PreLogos.bottom A.dom).dom ⟶ Z), p = q := fun p q => by
      have : φinv ≫ p = φinv ≫ q := hCot.init_uniq _ _
      calc p = (φ ≫ φinv) ≫ p := by rw [hφ, Cat.id_comp]
        _ = φ ≫ (φinv ≫ q) := by rw [Cat.assoc, this]
        _ = q := by rw [← Cat.assoc, hφ, Cat.id_comp]
    obtain ⟨ψ, ψinv, hψ, _⟩ := h2
    have uniqA' : ∀ {Z : 𝒞} (p q : (PreLogos.bottom A'.dom).dom ⟶ Z), p = q := fun p q => by
      have : ψinv ≫ p = ψinv ≫ q := hCot.init_uniq _ _
      calc p = (ψ ≫ ψinv) ≫ p := by rw [hψ, Cat.id_comp]
        _ = ψ ≫ (ψinv ≫ q) := by rw [Cat.assoc, this]
        _ = q := by rw [← Cat.assoc, hψ, Cat.id_comp]
    exact ⟨⟨g, uniqA _ _⟩, ⟨ginv, uniqA' _ _⟩, OverHom.ext hgg, OverHom.ext hgg'⟩
  invImage_preserves_union {X Y} f S T := by
    -- forget both sides to `𝒞`, chain through `𝒞`'s preservation and the `Σ_B`-invImage
    -- transport (`forgetSlice_invImage_le` / `le_forgetSlice_invImage`), reflect back.
    refine ⟨?_, ?_⟩
    · apply Subobject.forgetSlice_reflects
      show Subobject.le
          (Subobject.forgetSlice X (InverseImage f (HasSubobjectUnions.union S T)))
          (HasSubobjectUnions.union (Subobject.forgetSlice X (InverseImage f S))
                                    (Subobject.forgetSlice X (InverseImage f T)))
      refine Subobject.le_trans (forgetSlice_invImage_le f _) ?_
      refine Subobject.le_trans (PreLogos.invImage_preserves_union f.f
        (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T)).1 ?_
      exact union_mono (le_forgetSlice_invImage f S) (le_forgetSlice_invImage f T)
    · apply Subobject.forgetSlice_reflects
      show Subobject.le
          (HasSubobjectUnions.union (Subobject.forgetSlice X (InverseImage f S))
                                    (Subobject.forgetSlice X (InverseImage f T)))
          (Subobject.forgetSlice X (InverseImage f (HasSubobjectUnions.union S T)))
      refine Subobject.le_trans
        (union_mono (forgetSlice_invImage_le f S) (forgetSlice_invImage_le f T)) ?_
      refine Subobject.le_trans ?_ (le_forgetSlice_invImage f _)
      exact (PreLogos.invImage_preserves_union f.f
        (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T)).2
  invImage_preserves_bottom {X Y} f := by
    -- domain iso `(f# ⊥).dom ≅ ⊥.dom` in `𝒞` (from invImage transport + `𝒞`'s preservation),
    -- promoted to a slice iso using uniqueness of maps out of the initial bottom-domain.
    letI hCot := minimal_subobject_of_one_is_coterminator (𝒞 := 𝒞) ‹PreLogos 𝒞›
    let S : Subobject (Over B) Y := Subobject.liftSlice Y (PreLogos.bottom Y.dom)
    have hAC : Isomorphic (Subobject.forgetSlice X (InverseImage f S)).dom
                          (InverseImage f.f (PreLogos.bottom Y.dom)).dom :=
      let ⟨e, hiso, _⟩ :=
        Subobject.le_antisymm_iso (forgetSlice_invImage_le f S) (le_forgetSlice_invImage f S)
      ⟨e, hiso⟩
    have hABD : Isomorphic (Subobject.forgetSlice X (InverseImage f S)).dom
                           (PreLogos.bottom X.dom).dom :=
      isomorphic_trans hAC (PreLogos.invImage_preserves_bottom f.f)
    have hD0 : Isomorphic (PreLogos.bottom X.dom).dom hCot.zero := PreLogos.bottom_dom_iso X.dom _
    obtain ⟨φ, φinv, hφ, _⟩ := isomorphic_trans hABD hD0
    obtain ⟨g, ginv, hgg, hgg'⟩ := hABD
    have uniqA : ∀ {Z : 𝒞}
        (p q : (Subobject.forgetSlice X (InverseImage f S)).dom ⟶ Z), p = q := fun p q => by
      have : φinv ≫ p = φinv ≫ q := hCot.init_uniq _ _
      calc p = (φ ≫ φinv) ≫ p := by rw [hφ, Cat.id_comp]
        _ = φ ≫ (φinv ≫ q) := by rw [Cat.assoc, this]
        _ = q := by rw [← Cat.assoc, hφ, Cat.id_comp]
    obtain ⟨ψ, ψinv, hψ, _⟩ := hD0
    have uniqD : ∀ {Z : 𝒞} (p q : (PreLogos.bottom X.dom).dom ⟶ Z), p = q := fun p q => by
      have : ψinv ≫ p = ψinv ≫ q := hCot.init_uniq _ _
      calc p = (ψ ≫ ψinv) ≫ p := by rw [hψ, Cat.id_comp]
        _ = ψ ≫ (ψinv ≫ q) := by rw [Cat.assoc, this]
        _ = q := by rw [← Cat.assoc, hψ, Cat.id_comp]
    exact ⟨⟨g, uniqA _ _⟩, ⟨ginv, uniqD _ _⟩, OverHom.ext hgg, OverHom.ext hgg'⟩

end overPreLogos

/-! ### `PositivePreLogos (Over B)` and the §1.621 disjointness fields

  With `PreLogos (Over B)` and `HasBinaryCoproducts (Over B)` in hand, `PositivePreLogos
  (Over B)` is immediate.  The four §1.621 disjointness fields transport from `𝒞`'s
  `DisjointBinaryCoproduct` through the subobject identification:  the slice injection `inl`
  is `⟨inl, …⟩`, monic by `sigma_reflects_mono`; disjointness `inl ∩ inr ≤ ⊥` and the cover
  `⊤ ≤ inl ∪ inr` reflect from the corresponding `𝒞` facts. -/

section overDisjoint
variable [DisjointBinaryCoproduct 𝒞]

instance overPositivePreLogos (B : 𝒞) : PositivePreLogos (Over B) where

/-- The slice left injection `inl : X ⟶ X+Y` is monic (`Σ_B` reflects monos). -/
theorem over_inl_monic {X Y : Over B} :
    Monic (HasBinaryCoproducts.inl (𝒞 := Over B) (A := X) (B := Y)) :=
  sigma_reflects_mono (HasBinaryCoproducts.inl (𝒞 := Over B)) DisjointBinaryCoproduct.inl_monic

/-- The slice right injection `inr : Y ⟶ X+Y` is monic. -/
theorem over_inr_monic {X Y : Over B} :
    Monic (HasBinaryCoproducts.inr (𝒞 := Over B) (A := X) (B := Y)) :=
  sigma_reflects_mono (HasBinaryCoproducts.inr (𝒞 := Over B)) DisjointBinaryCoproduct.inr_monic

/-- The forgotten slice intersection is below the `𝒞`-intersection of the forgotten subobjects
    (`Σ_B` preserves the defining pullback): lift the forgotten slice pullback into the chosen
    base pullback. -/
theorem forgetSlice_inter_le {Y : Over B} (S T : Subobject (Over B) Y) :
    Subobject.le (Subobject.forgetSlice Y (Subobject.inter S T))
                 (Subobject.inter (Subobject.forgetSlice Y S) (Subobject.forgetSlice Y T)) := by
  let pbc := HasPullbacks.has (Subobject.forgetSlice Y S).arr (Subobject.forgetSlice Y T).arr
  refine ⟨pbc.lift (sliceConeForget (overPullbackCone S.arr T.arr)), ?_⟩
  show pbc.lift _ ≫ (pbc.cone.π₁ ≫ (Subobject.forgetSlice Y S).arr) = _
  rw [← Cat.assoc, pbc.lift_fst]; rfl

/-- **Rung 3: the slice of a disjoint-binary-coproduct pre-topos has disjoint binary coproducts.**
    The four §1.621 fields transport through the subobject identification `Sub (Over B) Y ≃
    Sub 𝒞 Y.dom`:  injections are monic by `sigma_reflects_mono`; `inl ∩ inr ≤ ⊥` forgets to the
    `𝒞` disjointness through `forgetSlice_inter_le`; `⊤ ≤ inl ∪ inr` forgets to the `𝒞` union
    cover (the slice union/bottom/entire forget on the nose). -/
instance overDisjointBinaryCoproduct (B : 𝒞) : DisjointBinaryCoproduct (Over B) where
  inl_monic := over_inl_monic
  inr_monic := over_inr_monic
  inl_inter_inr {X Y} := by
    apply Subobject.forgetSlice_reflects
    show Subobject.le
        (Subobject.forgetSlice (HasBinaryCoproducts.coprod X Y)
          (Subobject.inter (inlSub over_inl_monic) (inrSub over_inr_monic)))
        (PreLogos.bottom (HasBinaryCoproducts.coprod X Y).dom)
    exact Subobject.le_trans (forgetSlice_inter_le _ _) inl_inter_inr_le_bottom
  inl_union_inr {X Y} := by
    apply Subobject.forgetSlice_reflects
    show Subobject.le
        (Subobject.forgetSlice (HasBinaryCoproducts.coprod X Y)
          (Subobject.entire (HasBinaryCoproducts.coprod X Y)))
        (HasSubobjectUnions.union
          (Subobject.forgetSlice (HasBinaryCoproducts.coprod X Y) (inlSub over_inl_monic))
          (Subobject.forgetSlice (HasBinaryCoproducts.coprod X Y) (inrSub over_inr_monic)))
    exact inl_union_inr_entire

end overDisjoint

/-! ### `PreToposDisjoint (Over B)` — the bundling instance

  Type-class synthesis cannot assemble the `extends`-class `PreToposDisjoint (Over B)` from its
  already-transported parent instances (`overEffectiveRegular`/`overPositivePreLogos`/
  `overDisjointBinaryCoproduct`).  We provide it explicitly.  Crucially this is done under a SINGLE
  `[PreToposDisjoint 𝒞]` hypothesis (NOT separate `[EffectiveRegular 𝒞] + [DisjointBinaryCoproduct
  𝒞]`): otherwise the two base hypotheses give two different `RegularCategory 𝒞` instances, and the
  slice `over*` instances built on them mismatch in the flattened structure fields. -/
section overPreToposDisjoint
variable [PreToposDisjoint 𝒞]

instance overPreToposDisjoint (B : 𝒞) : PreToposDisjoint (Over B) where
  toPositivePreLogos := overPositivePreLogos B
  effective := fun E hE => sliceIsEffective E hE
  inl_monic := over_inl_monic
  inr_monic := over_inr_monic
  inl_inter_inr := (overDisjointBinaryCoproduct B).inl_inter_inr
  inl_union_inr := (overDisjointBinaryCoproduct B).inl_union_inr

end overPreToposDisjoint

/-! ## Slice-choice transport (one verified rung of the Diaconescu argument)

  A *base* choice object lifts to a *slice* choice object: if `Y.dom` is choice in `𝒞`,
  then `Y` is choice in `Over B`.  The point is that a base map realized inside a slice
  relation is automatically a slice arrow, because the relation's legs already commute with
  the structure maps. -/

section sliceChoice
variable [RegularCategory 𝒞] {B : 𝒞}

/-- **Slice-choice from base-choice.**  If `Y.dom` is `Choice` in `𝒞`, then `Y` is `Choice`
    in `Over B`.  An entire slice relation `R : X → Y` forgets to an entire base relation
    `R.forgetSlice : X.dom → Y.dom` (entirety is "left leg is a cover", and `Σ_B` preserves
    covers, `cover_f_of_cover`); base choice extracts a map `f : X.dom → Y.dom` with a section
    `h`.  Both `f` and `h` are *automatically* slice arrows: `f ≫ Y.hom = h ≫ R.colB.f ≫ Y.hom
    = h ≫ R.src.hom = h ≫ R.colA.f ≫ X.hom = X.hom`, using that `R`'s legs are slice arrows. -/
theorem slice_choice_of_dom_choice (Y : Over B) (hY : Choice Y.dom) : Choice Y := by
  intro X R hent
  have hcov : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  have hcovf : Cover R.colA.f := cover_f_of_cover R.colA hcov
  have hentf : Entire R.forgetSlice := by
    rw [show R.forgetSlice
          = BinRel.mk R.src.dom R.colA.f R.colB.f R.forgetSlice.isMonicPair from rfl]
    exact (tabulated_is_entire_iff_left_cover _ _ _).mpr hcovf
  obtain ⟨f, h, hA, hB⟩ := hY R.forgetSlice hentf
  simp only [BinRel.forgetSlice_colA, BinRel.forgetSlice_colB] at hA hB
  have hsecw : h ≫ R.src.hom = X.hom := by
    have e2 : h ≫ (R.colA.f ≫ X.hom) = h ≫ R.src.hom := by rw [R.colA.w]
    rw [← Cat.assoc, hA, Cat.id_comp] at e2; rw [← e2]
  have hfw : f ≫ Y.hom = X.hom := by
    have e1 : h ≫ (R.colB.f ≫ Y.hom) = f ≫ Y.hom := by rw [← Cat.assoc, hB]
    rw [R.colB.w, hsecw] at e1; rw [← e1]
  exact ⟨⟨f, hfw⟩, ⟨h, hsecw⟩, OverHom.ext hA, OverHom.ext hB⟩

end sliceChoice

/-! ## §1.662 Diaconescu (2)→(3): `Choice (1+1) ⟹ Boolean`

  Freyd's route, run inside the slice `𝒮(A×A) = Over (prod A A)` (a `PreToposDisjoint` +
  `HasReflTransClosure` via the slice instances above).  The diagonal `Δ_A : A ↣ A×A` is a
  subterminal `U ⊆ 1_𝒮` in the slice; complementing `U` there transports down to
  `DecidableObject A`, and `preTopos_boolean_iff_all_decidable.mpr` finishes.

  PIECE B (here): the explicit distributivity ISO `distOPO B : (B+B) ≅ (1+1)×B` with
  `distOPO B ≫ snd = ∇`.  It pins the `B`-coordinate of a retargeted relation, feeding
  `choice_prod_pinned`. -/

section Diaconescu
open HasBinaryCoproducts

variable [PreToposDisjoint 𝒞] [HasReflTransClosure 𝒞]

/-- The explicit distributivity comparison `(B+B) → (1+1)×B`,
    `case (pair (term≫inl) id) (pair (term≫inr) id)`.  An ISO (`distOPO_iso`); its `snd`
    component is the codiagonal `∇ = case id id` (`distOPO_snd`), which is the pin used by
    `choice_prod_pinned`. -/
noncomputable def distOPO (B : 𝒞) :
    coprod B B ⟶ prod (coprod (one : 𝒞) one) B :=
  case (pair (term B ≫ inl) (Cat.id B)) (pair (term B ≫ inr) (Cat.id B))

/-- The distributivity comparison's middle leg `(1×B)+(1×B) → (1+1)×B` (an iso by
    `complemented_legs_iso` for the distributivity-summand complemented pair). -/
noncomputable def distComp (B : 𝒞) :
    coprod (prod (one : 𝒞) B) (prod (one : 𝒞) B) ⟶ prod (coprod (one : 𝒞) one) B :=
  case (prodCoprodInl one one B) (prodCoprodInr one one B)

/-- The distributivity comparison's prefix `(B+B) → (1×B)+(1×B)` (coproduct of the
    `B ≅ 1×B` iso, hence iso). -/
noncomputable def distPre (B : 𝒞) :
    coprod B B ⟶ coprod (prod (one : 𝒞) B) (prod (one : 𝒞) B) :=
  case (prodOneLeftInv B ≫ inl) (prodOneLeftInv B ≫ inr)

/-- `distComp B` is iso: its two legs are exactly the distributivity-summand inclusions
    `prodCoprodInl/Inr`, a complemented pair (`prodCoprod_inter_le_bottom` /
    `prodCoprod_entire_le_union`), so `complemented_legs_iso` gives the inverse. -/
theorem distComp_iso (B : 𝒞) : IsIso (distComp B) := by
  obtain ⟨ψ, ψinv, hψψ, hψinvψ, hl, hr⟩ :=
    complemented_legs_iso (prodCoprodInlSub one one B) (prodCoprodInrSub one one B)
      (prodCoprod_inter_le_bottom one one B) (prodCoprod_entire_le_union one one B)
  have hd : distComp B = ψ := (case_uniq _ _ ψ hl hr).symm
  rw [hd]; exact ⟨ψinv, hψψ, hψinvψ⟩

/-- `distPre B` is iso (coproduct of the `prodOneLeftInv`/`snd` iso pair). -/
theorem distPre_iso (B : 𝒞) : IsIso (distPre B) := by
  refine ⟨case ((snd : prod (one : 𝒞) B ⟶ B) ≫ inl) ((snd : prod (one : 𝒞) B ⟶ B) ≫ inr),
    ?_, ?_⟩
  · refine (case_uniq _ _ _ ?_ ?_).trans
      (case_uniq inl inr (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
    · rw [← Cat.assoc, distPre, case_inl, Cat.assoc, case_inl, ← Cat.assoc,
        show prodOneLeftInv B ≫ snd = Cat.id B from snd_pair _ _, Cat.id_comp]
    · rw [← Cat.assoc, distPre, case_inr, Cat.assoc, case_inr, ← Cat.assoc,
        show prodOneLeftInv B ≫ snd = Cat.id B from snd_pair _ _, Cat.id_comp]
  · refine (case_uniq _ _ _ ?_ ?_).trans
      (case_uniq inl inr (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
    · rw [← Cat.assoc, case_inl, Cat.assoc, distPre, case_inl, ← Cat.assoc, snd_prodOneLeftInv,
        Cat.id_comp]
    · rw [← Cat.assoc, case_inr, Cat.assoc, distPre, case_inr, ← Cat.assoc, snd_prodOneLeftInv,
        Cat.id_comp]

/-- `distOPO = distPre ≫ distComp` (both factor legs agree after `fst`/`snd`). -/
theorem distOPO_factor (B : 𝒞) : distOPO B = distPre B ≫ distComp B := by
  refine (case_uniq (A := B) (B := B) (pair (term B ≫ inl) (Cat.id B))
    (pair (term B ≫ inr) (Cat.id B)) (distPre B ≫ distComp B) ?_ ?_).symm
  · rw [← Cat.assoc, distPre, case_inl, Cat.assoc, distComp, case_inl]
    apply fst_snd_jointly_monic
    · rw [fst_pair, Cat.assoc, prodCoprodInl, fst_pair, ← Cat.assoc]
      show (prodOneLeftInv B ≫ fst) ≫ inl = term B ≫ inl
      congr 1; exact term_uniq _ _
    · rw [snd_pair, Cat.assoc, prodCoprodInl, snd_pair,
        show prodOneLeftInv B ≫ snd = Cat.id B from snd_pair _ _]
  · rw [← Cat.assoc, distPre, case_inr, Cat.assoc, distComp, case_inr]
    apply fst_snd_jointly_monic
    · rw [fst_pair, Cat.assoc, prodCoprodInr, fst_pair, ← Cat.assoc]
      show (prodOneLeftInv B ≫ fst) ≫ inr = term B ≫ inr
      congr 1; exact term_uniq _ _
    · rw [snd_pair, Cat.assoc, prodCoprodInr, snd_pair,
        show prodOneLeftInv B ≫ snd = Cat.id B from snd_pair _ _]

/-- **PIECE B**: the distributivity comparison `(B+B) → (1+1)×B` is an ISO. -/
theorem distOPO_iso (B : 𝒞) : IsIso (distOPO B) := by
  rw [distOPO_factor]
  obtain ⟨pinv, hp1, hp2⟩ := distPre_iso B
  obtain ⟨cinv, hc1, hc2⟩ := distComp_iso B
  exact ⟨cinv ≫ pinv, by rw [Cat.assoc, ← Cat.assoc (distComp B), hc1, Cat.id_comp, hp1],
    by rw [Cat.assoc, ← Cat.assoc pinv, hp2, Cat.id_comp, hc2]⟩

/-- `distOPO B` is monic (it is an iso). -/
theorem distOPO_mono (B : 𝒞) : Monic (distOPO B) := by
  obtain ⟨g, hfg, _⟩ := distOPO_iso B
  intro W u v huv
  have := congrArg (· ≫ g) huv
  simpa only [Cat.assoc, hfg, Cat.comp_id] using this

/-- The pin: `distOPO B ≫ snd = ∇ = case id id` (the codiagonal on `B`). -/
theorem distOPO_snd (B : 𝒞) :
    distOPO B ≫ snd = case (Cat.id B) (Cat.id B) := by
  refine case_uniq _ _ _ ?_ ?_
  · rw [← Cat.assoc]; show (inl ≫ distOPO B) ≫ snd = _; rw [distOPO, case_inl, snd_pair]
  · rw [← Cat.assoc]; show (inr ≫ distOPO B) ≫ snd = _; rw [distOPO, case_inr, snd_pair]

/-- **PIECE C — slice choice of the codiagonal**.  From base `Choice (1+1)` alone, the slice
    coproduct `1_𝒮 + 1_𝒮 = (B+B, ∇)` over `B := A×A` is `Choice` in `Over B`.

    A slice entire relation `R : X → 1_𝒮+1_𝒮` forgets to a base entire `R̄ : X.dom → B+B`.
    Retarget `R̄`'s `colB` by the monic ISO `distOPO B : B+B ↣ (1+1)×B` to a base relation
    `R' : X.dom → (1+1)×B` (the monic pair survives because `distOPO` is monic).  The `B`-coordinate
    is PINNED: `R'.colB ≫ snd = R̄.colB ≫ ∇ = R.src.hom = R̄.colA ≫ X.hom` (`R.colB.w`, `R.colA.w`).
    `choice_prod_pinned` (`T := 1+1`, `C := B`, `p := X.hom`) sections `R'` from `Choice (1+1)`
    alone, giving a witness `w : X.dom → R.src.dom`.  The slice value `w ≫ R̄.colB : X.dom → B+B`
    and `w` are *automatically* slice arrows (their composites with the structure maps collapse
    via `R`'s legs), exactly as in `slice_choice_of_dom_choice`. -/
theorem slice_choice_codiag (A : 𝒞)
    (hch : Choice (coprod (one : 𝒞) one)) :
    Choice (coprod (HasTerminal.one : Over (prod A A)) HasTerminal.one) := by
  intro X R hent
  let B := prod A A
  have hcov : Cover R.colA :=
    (tabulated_is_entire_iff_left_cover R.colA R.colB R.isMonicPair).mp hent
  have hcovf : Cover R.colA.f := cover_f_of_cover R.colA hcov
  -- structure map of the slice coproduct is `∇ = case (id B) (id B)`.
  have hnabla : R.colB.f ≫ case (Cat.id B) (Cat.id B) = R.src.hom := R.colB.w
  -- retargeted base relation with `colB := R̄.colB ≫ distOPO B`.
  have hp' : MonicPair R.colA.f (R.colB.f ≫ distOPO B) := by
    intro W u v hua hub
    apply R.forgetSlice.isMonicPair u v hua
    apply distOPO_mono B
    calc (u ≫ R.colB.f) ≫ distOPO B = u ≫ (R.colB.f ≫ distOPO B) := Cat.assoc _ _ _
      _ = v ≫ (R.colB.f ≫ distOPO B) := hub
      _ = (v ≫ R.colB.f) ≫ distOPO B := (Cat.assoc _ _ _).symm
  let R' : BinRel 𝒞 X.dom (prod (coprod (one : 𝒞) one) B) :=
    BinRel.mk R.src.dom R.colA.f (R.colB.f ≫ distOPO B) hp'
  have hentR' : Entire R' :=
    (tabulated_is_entire_iff_left_cover R.colA.f (R.colB.f ≫ distOPO B) hp').mpr hcovf
  have hpin : R'.colB ≫ snd = R'.colA ≫ X.hom := by
    show (R.colB.f ≫ distOPO B) ≫ snd = R.colA.f ≫ X.hom
    rw [Cat.assoc, distOPO_snd, hnabla]; exact (R.colA.w).symm
  obtain ⟨f, w, hwA, hwB⟩ := choice_prod_pinned hch R' hentR' X.hom hpin
  have hwA' : w ≫ R.colA.f = Cat.id X.dom := hwA
  have hsecw : w ≫ R.src.hom = X.hom := by
    have e2 : w ≫ (R.colA.f ≫ X.hom) = w ≫ R.src.hom := by rw [R.colA.w]
    rw [← Cat.assoc, hwA', Cat.id_comp] at e2; rw [← e2]
  have hgw : (w ≫ R.colB.f) ≫ case (Cat.id B) (Cat.id B) = X.hom := by
    rw [Cat.assoc, hnabla, hsecw]
  refine ⟨⟨w ≫ R.colB.f, hgw⟩, ⟨w, hsecw⟩, ?_, ?_⟩
  · apply OverHom.ext; show w ≫ R.colA.f = Cat.id X.dom; exact hwA'
  · apply OverHom.ext; show w ≫ R.colB.f = w ≫ R.colB.f; rfl

/-! ### PIECE A scaffolding — the antidiagonal of `1+1`

  Toward `DecidableObject (1+1)` (the single remaining base fact, see the residual note below):
  the diagonal `Δ_{1+1} = diag (1+1)` and its candidate complement `adiag` are both clean monos
  out of `1+1` into `(1+1)×(1+1)`.  `adiag` is the "swap" point map `case (pair inl inr)
  (pair inr inl)`.  The two `IsComplementedSub` clauses for `(Δ, adiag)` are what remain, and
  they reduce to coproduct extensivity (not yet available at this layer). -/

/-- The antidiagonal `(1+1) ↣ (1+1)×(1+1)`, `case (pair inl inr) (pair inr inl)` — the candidate
    complement of the diagonal `Δ_{1+1}`. -/
noncomputable def adiag :
    coprod (one : 𝒞) one ⟶ prod (coprod (one : 𝒞) one) (coprod (one : 𝒞) one) :=
  case (pair (inl : (one : 𝒞) ⟶ _) inr) (pair (inr : (one : 𝒞) ⟶ _) inl)

theorem adiag_fst : adiag (𝒞 := 𝒞) ≫ fst = case inl inr := by
  refine case_uniq _ _ _ ?_ ?_
  · rw [← Cat.assoc]; show (inl ≫ adiag) ≫ fst = _; rw [adiag, case_inl, fst_pair]
  · rw [← Cat.assoc]; show (inr ≫ adiag) ≫ fst = _; rw [adiag, case_inr, fst_pair]

theorem adiag_snd : adiag (𝒞 := 𝒞) ≫ snd = case inr inl := by
  refine case_uniq _ _ _ ?_ ?_
  · rw [← Cat.assoc]; show (inl ≫ adiag) ≫ snd = _; rw [adiag, case_inl, snd_pair]
  · rw [← Cat.assoc]; show (inr ≫ adiag) ≫ snd = _; rw [adiag, case_inr, snd_pair]

/-- `adiag` is monic: post-`fst` gives `case inl inr = id`, which already cancels. -/
theorem adiag_mono : Monic (adiag (𝒞 := 𝒞)) := by
  intro W u v huv
  have hf : u ≫ case inl inr = v ≫ case inl inr := by
    have := congrArg (· ≫ fst) huv; simpa only [Cat.assoc, adiag_fst] using this
  have hid1 : case (inl : (one : 𝒞) ⟶ _) inr = Cat.id (coprod one one) :=
    (case_uniq inl inr (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm
  rw [hid1, Cat.comp_id, Cat.comp_id] at hf; exact hf

/-- `case inr inl` (the swap on `1+1`) precomposed with `inl` is `inr`, and with `inr` is `inl`. -/
theorem inl_swap : (inl : (one : 𝒞) ⟶ coprod one one) ≫ case inr inl = inr := case_inl _ _
theorem inr_swap : (inr : (one : 𝒞) ⟶ coprod one one) ≫ case inr inl = inl := case_inr _ _

-- `le_bottom_of_map_to_bottom` (a subobject whose domain maps to any bottom is `≤ ⊥`) is now the
-- canonical `Freyd.le_bottom_of_map_to_bottom` in `S1_62` (DRY — was duplicated here).

/-- A generalized element `g : X → 1+1` FIXED by the swap (`g ≫ case inr inl = g`) has an
    INITIAL domain: on the `inl`-part of `X` the swap turns `inl` into `inr`, an `inl/inr` clash,
    so that part is `≤ ⊥`; likewise the `inr`-part; the two cover `X`, so `X` itself is `≤ ⊥`.
    Returns `entire X ≤ ⊥ X` (i.e. `id_X` factors through `⊥`, so `X` is initial). -/
theorem swap_fixed_le_bottom {X : 𝒞} (g : X ⟶ coprod (one : 𝒞) one)
    (hg : g ≫ case inr inl = g) :
    (Subobject.entire X).le (PreLogos.bottom X) := by
  let C := coprod (one : 𝒞) one
  let Inl := inlSub (𝒞 := 𝒞) (A := (one : 𝒞)) (B := one) inl_mono
  let Inr := inrSub (𝒞 := 𝒞) (A := (one : 𝒞)) (B := one) inr_mono
  let A₁ : Subobject 𝒞 X := InverseImage g Inl
  let A₂ : Subobject 𝒞 X := InverseImage g Inr
  let pbL := HasPullbacks.has g Inl.arr
  let pbR := HasPullbacks.has g Inr.arr
  -- pullback legs:  A₁.arr ≫ g = f₁ ≫ inl,   A₂.arr ≫ g = f₂ ≫ inr.
  have hfac₁ : A₁.arr ≫ g = pbL.cone.π₂ ≫ inl := by
    show pbL.cone.π₁ ≫ g = pbL.cone.π₂ ≫ Inl.arr; exact pbL.cone.w
  have hfac₂ : A₂.arr ≫ g = pbR.cone.π₂ ≫ inr := by
    show pbR.cone.π₁ ≫ g = pbR.cone.π₂ ≫ Inr.arr; exact pbR.cone.w
  -- on A₁: A₁.arr ≫ g = f₁ ≫ inl, and = A₁.arr ≫ (g ≫ swap) = (f₁ ≫ inl) ≫ swap = f₁ ≫ inr ⟹ clash.
  have hclash₁ : pbL.cone.π₂ ≫ inl = pbL.cone.π₂ ≫ inr := by
    calc pbL.cone.π₂ ≫ inl = A₁.arr ≫ g := hfac₁.symm
      _ = A₁.arr ≫ (g ≫ case inr inl) := by rw [hg]
      _ = (A₁.arr ≫ g) ≫ case inr inl := (Cat.assoc _ _ _).symm
      _ = (pbL.cone.π₂ ≫ inl) ≫ case inr inl := by rw [hfac₁]
      _ = pbL.cone.π₂ ≫ (inl ≫ case inr inl) := Cat.assoc _ _ _
      _ = pbL.cone.π₂ ≫ inr := by rw [inl_swap]
  have hclash₂ : pbR.cone.π₂ ≫ inl = pbR.cone.π₂ ≫ inr := by
    calc pbR.cone.π₂ ≫ inl
        = pbR.cone.π₂ ≫ (inr ≫ case inr inl) := by rw [inr_swap]
      _ = (pbR.cone.π₂ ≫ inr) ≫ case inr inl := (Cat.assoc _ _ _).symm
      _ = (A₂.arr ≫ g) ≫ case inr inl := by rw [hfac₂]
      _ = A₂.arr ≫ (g ≫ case inr inl) := Cat.assoc _ _ _
      _ = A₂.arr ≫ g := by rw [hg]
      _ = pbR.cone.π₂ ≫ inr := hfac₂
  -- clash ⟹ each Aᵢ.dom maps to ⊥ C ⟹ Aᵢ ≤ ⊥ X.
  have hA₁bot : A₁.le (PreLogos.bottom X) := by
    obtain ⟨e₁, _⟩ := coprod_inl_inr_disjoint_elt pbL.cone.π₂ pbL.cone.π₂ hclash₁
    exact le_bottom_of_map_to_bottom A₁ e₁
  have hA₂bot : A₂.le (PreLogos.bottom X) := by
    obtain ⟨e₂, _⟩ := coprod_inl_inr_disjoint_elt pbR.cone.π₂ pbR.cone.π₂ hclash₂
    exact le_bottom_of_map_to_bottom A₂ e₂
  -- entire X ≤ g#(entire C) ≤ g#(Inl ∪ Inr) ≤ g#Inl ∪ g#Inr = A₁ ∪ A₂ ≤ ⊥ X.
  have hentU : (Subobject.entire X).le (HasSubobjectUnions.union A₁ A₂) := by
    have ha : (Subobject.entire X).le (InverseImage g (Subobject.entire C)) :=
      entire_le_invImage_entire g
    have hbu : (Subobject.entire C).le (HasSubobjectUnions.union Inl Inr) :=
      inl_union_inr_entire (𝒟 := 𝒞) (A := (one : 𝒞)) (B := one)
    have hb : (InverseImage g (Subobject.entire C)).le
        (InverseImage g (HasSubobjectUnions.union Inl Inr)) := invImage_mono_local g hbu
    have hc : (InverseImage g (HasSubobjectUnions.union Inl Inr)).le
        (HasSubobjectUnions.union A₁ A₂) := (PreLogos.invImage_preserves_union g Inl Inr).1
    exact Subobject.le_trans ha (Subobject.le_trans hb hc)
  exact Subobject.le_trans hentU (HasSubobjectUnions.union_min A₁ A₂ _ hA₁bot hA₂bot)

/-- The diagonal subobject `Δ_{1+1}` of `(1+1)×(1+1)`. -/
noncomputable def diagSub11 : Subobject 𝒞 (prod (coprod (one : 𝒞) one) (coprod one one)) :=
  diagSub (coprod (one : 𝒞) one)

/-- The antidiagonal subobject `Δᶜ_{1+1}` of `(1+1)×(1+1)`, candidate complement of `Δ`. -/
noncomputable def adiagSub : Subobject 𝒞 (prod (coprod (one : 𝒞) one) (coprod one one)) :=
  ⟨coprod (one : 𝒞) one, adiag, adiag_mono⟩

/-- `case inl inr = id` on `1+1` (the `fst` leg of `adiag`). -/
theorem case_inl_inr_id : case (inl : (one : 𝒞) ⟶ _) inr = Cat.id (coprod one one) :=
  (case_uniq inl inr (Cat.id _) (Cat.comp_id _) (Cat.comp_id _)).symm

/-- The diagonal corners `inl ≫ Δ = pair inl inl`, `inr ≫ Δ = pair inr inr`. -/
theorem inl_diag11 : (inl : (one : 𝒞) ⟶ _) ≫ diag (coprod one one) = pair inl inl := by
  apply fst_snd_jointly_monic
  · rw [Cat.assoc, show diag (coprod (one : 𝒞) one) ≫ fst = Cat.id (coprod one one)
        from fst_pair _ _, Cat.comp_id, fst_pair]
  · rw [Cat.assoc, show diag (coprod (one : 𝒞) one) ≫ snd = Cat.id (coprod one one)
        from snd_pair _ _, Cat.comp_id, snd_pair]
theorem inr_diag11 : (inr : (one : 𝒞) ⟶ _) ≫ diag (coprod one one) = pair inr inr := by
  apply fst_snd_jointly_monic
  · rw [Cat.assoc, show diag (coprod (one : 𝒞) one) ≫ fst = Cat.id (coprod one one)
        from fst_pair _ _, Cat.comp_id, fst_pair]
  · rw [Cat.assoc, show diag (coprod (one : 𝒞) one) ≫ snd = Cat.id (coprod one one)
        from snd_pair _ _, Cat.comp_id, snd_pair]
/-- The antidiagonal corners `inl ≫ adiag = pair inl inr`, `inr ≫ adiag = pair inr inl`. -/
theorem inl_adiag : (inl : (one : 𝒞) ⟶ _) ≫ adiag = pair inl inr := by rw [adiag, case_inl]
theorem inr_adiag : (inr : (one : 𝒞) ⟶ _) ≫ adiag = pair inr inl := by rw [adiag, case_inr]

/-- The four `distOPO`-corner identities: `inl ≫ term ≫ inl = inl`, etc. (`term` collapses `1+1`
    to `1`, then `inl`/`inr` re-injects), used to compute `distOPO`'s summand legs. -/
theorem term_inl_self (x : (one : 𝒞) ⟶ coprod one one) :
    x ≫ term (coprod one one) ≫ (inl : (one : 𝒞) ⟶ coprod one one) = inl := by
  rw [← Cat.assoc, show x ≫ term (coprod one one) = Cat.id one from term_uniq _ _, Cat.id_comp]
theorem term_inr_self (x : (one : 𝒞) ⟶ coprod one one) :
    x ≫ term (coprod one one) ≫ (inr : (one : 𝒞) ⟶ coprod one one) = inr := by
  rw [← Cat.assoc, show x ≫ term (coprod one one) = Cat.id one from term_uniq _ _, Cat.id_comp]

/-- The two summand legs of `distOPO (1+1)`:
    `inl ≫ distOPO = case (pair inl inl) (pair inl inr)` (`= case Δ-corner adiag-corner`) and
    `inr ≫ distOPO = case (pair inr inl) (pair inr inr)`. -/
theorem inl_distOPO :
    (inl : coprod (one : 𝒞) one ⟶ _) ≫ distOPO (coprod one one)
      = case (pair inl inl) (pair inl inr) := by
  rw [distOPO, case_inl]
  refine case_uniq _ _ _ ?_ ?_
  · apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, fst_pair]; exact term_inl_self _
    · rw [Cat.assoc, snd_pair, Cat.comp_id, snd_pair]
  · apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, fst_pair]; exact term_inl_self _
    · rw [Cat.assoc, snd_pair, Cat.comp_id, snd_pair]
theorem inr_distOPO :
    (inr : coprod (one : 𝒞) one ⟶ _) ≫ distOPO (coprod one one)
      = case (pair inr inl) (pair inr inr) := by
  rw [distOPO, case_inr]
  refine case_uniq _ _ _ ?_ ?_
  · apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, fst_pair]; exact term_inr_self _
    · rw [Cat.assoc, snd_pair, Cat.comp_id, snd_pair]
  · apply fst_snd_jointly_monic
    · rw [Cat.assoc, fst_pair, fst_pair]; exact term_inr_self _
    · rw [Cat.assoc, snd_pair, Cat.comp_id, snd_pair]

/-- **PIECE A**: `DecidableObject (1+1)` — the diagonal `Δ_{1+1}` is complemented, with complement
    the antidiagonal `adiag`.  DISJOINTNESS: a common lower bound's witness `r : · → 1+1` is fixed
    by the swap (`r ≫ case inr inl = r`, since `Δ` forces both coords equal and `Δᶜ` swaps them), so
    its domain is initial (`swap_fixed_le_bottom`).  ENTIRE: the distributivity iso
    `distOPO (1+1) : (1+1)+(1+1) ≅ (1+1)²` is a cover that factors through `Δ ∪ Δᶜ` (its four corners
    are the four points, two on `Δ`, two on `Δᶜ`), so its image — entire — is `≤ Δ ∪ Δᶜ`. -/
theorem one_one_decidable : DecidableObject (HasBinaryCoproducts.coprod (one : 𝒞) one) := by
  classical
  refine ⟨adiagSub, ?_, ?_⟩
  · -- DISJOINTNESS (universal form): any S ≤ Δ and S ≤ adiag has S ≤ ⊥.
    intro S hSd hSa
    obtain ⟨r, hr⟩ := hSa     -- r ≫ adiag = S.arr
    obtain ⟨d, hd⟩ := hSd     -- d ≫ Δ = S.arr  (so the two coords of S.arr agree)
    simp only [adiagSub] at hr
    have hd' : d ≫ diag (coprod (one : 𝒞) one) = S.arr := hd
    have hdiageq : S.arr ≫ fst = S.arr ≫ snd := by
      rw [← hd', Cat.assoc, Cat.assoc,
        show diag (coprod (one : 𝒞) one) ≫ fst = Cat.id (coprod one one) from fst_pair _ _,
        show diag (coprod (one : 𝒞) one) ≫ snd = Cat.id (coprod one one) from snd_pair _ _]
    have hrfst : r = S.arr ≫ fst := by
      rw [← hr, Cat.assoc, adiag_fst, case_inl_inr_id, Cat.comp_id]
    have hrswap : r ≫ case inr inl = S.arr ≫ snd := by rw [← hr, Cat.assoc, adiag_snd]
    have hfix : r ≫ case inr inl = r := by rw [hrswap, ← hdiageq, ← hrfst]
    obtain ⟨k, _⟩ := swap_fixed_le_bottom r hfix
    exact le_bottom_of_map_to_bottom S k
  · -- ENTIRE: entire ≤ Δ ∪ adiag, via the cover `distOPO (1+1)` factoring through the union.
    show (Subobject.entire _).le (HasSubobjectUnions.union (diagSub11 (𝒞 := 𝒞)) adiagSub)
    let B := coprod (one : 𝒞) one
    let U := HasSubobjectUnions.union (diagSub11 (𝒞 := 𝒞)) adiagSub
    -- the four corners land in Δ or adiag, hence in U.
    obtain ⟨lΔ, hlΔ⟩ := HasSubobjectUnions.union_left (diagSub11 (𝒞 := 𝒞)) adiagSub
    obtain ⟨lA, hlA⟩ := HasSubobjectUnions.union_right (diagSub11 (𝒞 := 𝒞)) adiagSub
    -- corner lifts cLL,cRR ↦ via lΔ;  cLR,cRL ↦ via lA.
    let wLL : (one : 𝒞) ⟶ U.dom := inl ≫ lΔ      -- pair inl inl
    let wRR : (one : 𝒞) ⟶ U.dom := inr ≫ lΔ      -- pair inr inr
    let wLR : (one : 𝒞) ⟶ U.dom := inl ≫ lA      -- pair inl inr
    let wRL : (one : 𝒞) ⟶ U.dom := inr ≫ lA      -- pair inr inl
    have ecLL : wLL ≫ U.arr = pair inl inl := by rw [Cat.assoc, hlΔ]; exact inl_diag11
    have ecRR : wRR ≫ U.arr = pair inr inr := by rw [Cat.assoc, hlΔ]; exact inr_diag11
    have ecLR : wLR ≫ U.arr = pair inl inr := by rw [Cat.assoc, hlA]; exact inl_adiag
    have ecRL : wRL ≫ U.arr = pair inr inl := by rw [Cat.assoc, hlA]; exact inr_adiag
    -- assemble w : (1+1)+(1+1) → U.dom with w ≫ U.arr = distOPO B.
    let w : coprod B B ⟶ U.dom := case (case wLL wLR) (case wRL wRR)
    -- the two summand legs of `w ≫ U.arr` equal those of `distOPO B`.
    have hL : inl ≫ (w ≫ U.arr) = inl ≫ distOPO B := by
      rw [← Cat.assoc]
      show (inl ≫ case (case wLL wLR) (case wRL wRR)) ≫ U.arr = inl ≫ distOPO B
      rw [case_inl, inl_distOPO]
      refine case_uniq _ _ _ ?_ ?_
      · rw [← Cat.assoc, case_inl]; exact ecLL
      · rw [← Cat.assoc, case_inr]; exact ecLR
    have hR : inr ≫ (w ≫ U.arr) = inr ≫ distOPO B := by
      rw [← Cat.assoc]
      show (inr ≫ case (case wLL wLR) (case wRL wRR)) ≫ U.arr = inr ≫ distOPO B
      rw [case_inr, inr_distOPO]
      refine case_uniq _ _ _ ?_ ?_
      · rw [← Cat.assoc, case_inl]; exact ecRL
      · rw [← Cat.assoc, case_inr]; exact ecRR
    have hw : w ≫ U.arr = distOPO B := by
      rw [case_uniq (inl ≫ (w ≫ U.arr)) (inr ≫ (w ≫ U.arr)) (w ≫ U.arr) rfl rfl, hL, hR,
        ← case_uniq (inl ≫ distOPO B) (inr ≫ distOPO B) (distOPO B) rfl rfl]
    -- distOPO is a cover ⟹ its image is entire and ≤ U.
    have hcov : Cover (distOPO B) := iso_cover _ (distOPO_iso B)
    have himg_entire : Subobject.IsEntire (image (distOPO B)) :=
      (cover_iff_image_entire (distOPO B)).1 hcov
    have himg_le : (image (distOPO B)).le U := image_min (distOPO B) U ⟨w, hw⟩
    obtain ⟨inv, _, h2⟩ := himg_entire
    obtain ⟨t, ht⟩ := himg_le
    exact ⟨inv ≫ t, by rw [Cat.assoc, ht]; exact h2⟩

/-! ### PIECES E + F — slice pushout completion and slice→base transport

  Run Freyd's `U ⊆ 1` argument inside the slice `Over (A×A)`.  `U = Δ_A ⊆ 1_𝒮` is the
  subterminal whose base arrow is `diag A`.  Amalgamate `U.arr` with itself: the amalgam `P`
  is a quotient of `1_𝒮 + 1_𝒮` by the cover `case u v`; slice choice (`slice_choice_codiag`)
  splits it, so `P ↣ 1_𝒮 + 1_𝒮` is a split mono; `1_𝒮 + 1_𝒮` decidable (`one_one_decidable`
  at the slice) ⟹ `P` decidable ⟹ `U` complemented; `forgetSlice` transports the complement
  down to `diagSub A`, i.e. `DecidableObject A`. -/

/-- A cover whose DOMAIN is a choice object splits (single-object projectivity, §1.57).
    `(graph f)°` is entire because its left leg `f` is a cover; `Choice (domain)` extracts the
    section. -/
theorem cover_splits_of_dom_choice {𝒟 : Type u} [Cat.{v} 𝒟] [RegularCategory 𝒟]
    {X Y : 𝒟} (f : X ⟶ Y) (hcov : Cover f) (hX : Choice X) :
    ∃ s : Y ⟶ X, s ≫ f = Cat.id Y := by
  have hent : Entire ((graph f)°) :=
    (tabulated_is_entire_iff_left_cover f (Cat.id X) ((graph f)°).isMonicPair).mpr hcov
  obtain ⟨s, k, hkA, hkB⟩ := hX ((graph f)°) hent
  dsimp [graph, reciprocal] at hkA hkB
  rw [Cat.comp_id] at hkB
  exact ⟨s, by rw [← hkB]; exact hkA⟩

/-- **PIECE F (transport)**: `IsComplemented` of a slice subobject `U ⊆ Y` forgets to
    `IsComplemented (forgetSlice U)` in `𝒞`.  Complement = `forgetSlice U₂`; both clauses
    transport through the `forgetSlice`/`liftSlice` order-iso (`forgetSlice` of `bottom`/`union`/
    `entire` are on the nose). -/
theorem forgetSlice_isComplemented {B : 𝒞} {Y : Over B} (U : Subobject (Over B) Y)
    (hU : IsComplemented U) : IsComplemented (Subobject.forgetSlice Y U) := by
  obtain ⟨U₂, hdisj, hcover⟩ := hU
  refine ⟨Subobject.forgetSlice Y U₂, ?_, ?_⟩
  · -- disjointness: lift any base lower bound `S₀` to the slice, apply slice disjointness, forget.
    intro S₀ h1 h2
    have hsl1 : (Subobject.liftSlice Y S₀).le U :=
      Subobject.forgetSlice_reflects (by rw [forgetSlice_liftSlice]; exact h1)
    have hsl2 : (Subobject.liftSlice Y S₀).le U₂ :=
      Subobject.forgetSlice_reflects (by rw [forgetSlice_liftSlice]; exact h2)
    have hbot := Subobject.forgetSlice_mono (hdisj (Subobject.liftSlice Y S₀) hsl1 hsl2)
    rwa [forgetSlice_liftSlice] at hbot
  · -- union: forget the slice union clause (`forgetSlice` of `entire`/`union` are on the nose).
    exact Subobject.forgetSlice_mono hcover

/- The two keystone theorems `all_decidable_of_one_one_choice` and `one_one_choice_to_boolean`
   (§1.662 (2)→(3)) live in `Freyd.Diaconescu`, which IMPORTS this file — clean separation; they use
   the `overPreToposDisjoint` bundling instance and the slice-Diaconescu helpers above. -/

end Diaconescu

/-! ## Residual: completing the slice pre-topos tower (toward §1.662 Diaconescu)

  Rungs 1, 2, 3, 4 are now DONE Sorry-free above:

  1. ✅ **Forget commutes with the calculus** (`BinRel.forgetSlice`, `forgetSlice_graph`,
     `forgetSlice_reciprocal` on the nose; `forgetSlice_compose_le` + `le_forgetSlice_compose`
     for `⊚` up to the comparison iso; `forgetSlice_mono_relLe` / `forgetSlice_reflects_relLe`
     for faithfulness).
  2. ✅ **`EffectiveRegular (Over B)`** (`overEffectiveRegular`, via `sliceIsEffective`).
  3. ✅ **`DisjointBinaryCoproduct (Over B)`** (`overDisjointBinaryCoproduct`).  Built by
     domain-transport along the faithful `Σ_B`: the order-iso `Sub (Over B) Y ≃ Sub 𝒞 Y.dom`
     (`Subobject.forgetSlice`/`liftSlice`, mutually monotone with `forgetSlice ∘ liftSlice = id`)
     transports the WHOLE `PreLogos (Over B)` lattice — `overHasSubobjectUnions`,
     `overPreLogos` (`bottom`/`bottom_min`/`bottom_dom_iso`/`invImage_preserves_union`/
     `invImage_preserves_bottom`) — from `𝒞`'s lattice on `Y.dom`.  The one new construction is
     `overHasBinaryCoproducts` (`X + Y = X.dom + Y.dom` with structure map `case X.hom Y.hom`);
     `overPositivePreLogos` and the four §1.621 disjointness fields then transport from `𝒞`'s
     `DisjointBinaryCoproduct` through the subobject identification.
  4. ✅ **`HasReflTransClosure (Over B)`** (`overHasReflTransClosure`, via `sliceTransRefClos`).

  REMAINING (final residual) — SHARPENED, with the precise wall located:

  5. **Diaconescu transport (final).**  `preTopos_boolean_iff_all_decidable.mpr` reduces the
     `S1_64` goal to `∀ A, DecidableObject A`.  Decidability of `A` is the diagonal
     `Δ : A ↣ A×A` complemented; the slice `𝒮(A×A)` is now a pre-topos (rungs 2–4) and `Δ` is
     a subterminal there.  Running Freyd's `U ⊆ 1` argument inside `𝒮(A×A)` (form `P = 1_𝒮 +_Δ
     1_𝒮`, a quotient of `1_𝒮 + 1_𝒮`; choice splits the quotient so `P ⊆ 1_𝒮 + 1_𝒮`;
     `1_𝒮 + 1_𝒮` decidable ⟹ `P` decidable ⟹ `Δ` complemented) needs **slice choice of the
     codiagonal `1_𝒮 + 1_𝒮`**.

     KEYSTONE (the pinning route, FORMERLY thought a blind alley, is now UNBLOCKED).  Slice choice of
     `1_𝒮+1_𝒮` from base `Choice (1+1)` IS provable.  The slice coproduct `1_𝒮+1_𝒮` over `B := A×A`
     is `(B+B, ∇)`.  A slice entire relation `R : X → 1_𝒮+1_𝒮` forgets to a base entire
     `R̄ : X.dom → B+B`.  Retarget `R̄` to `prod (1+1) B` by post-composing its `colB` with the
     EXPLICIT distributivity ISO `distOPO B : B+B ≅ (1+1)×B`,
     `distOPO B = case (pair (term≫inl) id) (pair (term≫inr) id)`, which satisfies
     `distOPO B ≫ snd = ∇` (`distOPO_snd`).  Because `distOPO B` is an ISO (monic), the retarget
     preserves the monic pair — NO non-monic `δ : B+B → 1+1`, hence NO image-quotient that collapses
     the witness (this was the old note's mistake: it retargeted via the non-monic codiagonal-decision
     instead of the monic distributivity iso).  Under the retarget the `B`-coordinate (`snd`) equals
     `R̄.colB ≫ ∇ = R̄.src.hom = R̄.colA ≫ X.hom`, i.e. it is PINNED to `p := X.hom`.  Then
     `Freyd.choice_prod_pinned` (S1_64, proved this pass: with the `C`-coordinate pinned to a map,
     base `Choice T` ALONE sections a relation targeted at `prod T C`, no `Choice C`) with
     `T := 1+1`, `C := B`, `p := X.hom` produces the base section; lift it back to the slice.

     ASSEMBLY STATUS.
       (i) ✅ `distOPO_iso : IsIso (distOPO B)` — built ABOVE, but NOT via the suggested
           monic+cover route (which itself needs `1+1` decidable, circular).  Instead
           `distOPO = distPre ≫ distComp` where `distComp = case (prodCoprodInl) (prodCoprodInr)`
           is iso by `complemented_legs_iso` on the §1.626 distributivity-summand complemented
           pair (`prodCoprod_inter_le_bottom`/`prodCoprod_entire_le_union`), and `distPre` is a
           coproduct of the `B ≅ 1×B` iso.  `distOPO_snd : distOPO B ≫ snd = ∇`.
       (ii) ✅ `slice_choice_codiag : Choice (1_𝒮 + 1_𝒮)` — built ABOVE
           (forget→retarget by `distOPO`→pin→`choice_prod_pinned`→slice lift).  Axiom-clean.
       (iii-base) ✅ BASE `DecidableObject (1+1)` (`one_one_decidable`, ABOVE).  The prior note
           WRONGLY declared this gated on `[Topos 𝒞]` extensivity.  It is NOT: the extensivity
           needed (decompose any `q : X → 1+1` into its `q#inl`/`q#inr` parts, each a `inl/inr`
           clash) is AVAILABLE at the `[DisjointBinaryCoproduct 𝒞]` layer that `PreToposDisjoint`
           provides — `decompose_via_coproduct` (S1_62) / `coprod_inl_inr_disjoint_elt` on each
           inverse-image part.  Disjointness: a common lower bound's witness `r : · → 1+1` is
           swap-fixed (`r ≫ case inr inl = r`), hence its domain is initial (`swap_fixed_le_bottom`).
           Entire: the `distOPO (1+1)` cover factors through `Δ ∪ adiag` (its four corners are the
           four points, two on `Δ`, two on `adiag`), so its entire image is `≤ Δ ∪ adiag`.
           Axiom-clean (`[propext, Classical.choice]`).
       (iii-slice) ⛔ slice DECIDABILITY of `1_𝒮 + 1_𝒮` — the REMAINING gap.  The slice diagonal
           `Δ_{1_𝒮+1_𝒮}` lives over the slice product = base FIBERED product `(B+B) ×_B (B+B)`
           (`B := A×A`), which under `distOPO B` is `≅ (1+1)×(1+1)×B` with `Δ_slice ≅ Δ_{1+1} × id_B`.
           The reusable transport `decidableSub_of_iso`/`decidableSub_of_mono` (`Complement.lean`,
           this pass) carries decidability across the iso, BUT the cross-category step (relating the
           SLICE diagonal `Sub(Over B)` to the BASE `(1+1)²×B` diagonal `Sub 𝒞`, plus the
           `· × id_B` factor) is the heavy fibered-product chase still to be built.
       (iv) (slice→base complement transport via `forgetSlice_mono`/`reflects`) and the §1.651
           pushout completion (`amalgamation_is_pullback` + `quotient_of_choice_is_choice` +
           subobject-of-decidable-is-decidable) are unblocked once (iii-slice) lands.

     So `one_one_choice_to_boolean` is reduced to the SLICE-DECIDABILITY fibered-product chase
     (iii-slice): the base fact `one_one_decidable` (PIECE A) is now CLOSED, and the decidability
     transport `decidableSub_of_iso` is in hand. -/

end Freyd
