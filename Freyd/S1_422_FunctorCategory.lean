/-
  Freyd & Scedrov, *Categories and Allegories* — functor-category structure transfer.

  The functor category 𝒮^A (`Functor 𝒜 𝒮`) is already defined in S1_27:
  objects are bundled functors `Functor 𝒜 𝒮`, morphisms are natural
  transformations `FunctorHom F G`, and `functorCat 𝒜 𝒮 : Cat (Functor 𝒜 𝒮)`
  is the `Cat` instance.  This file adds the *structural* content:

  §1.422  `𝒮^A` has a terminator iff 𝒮 does — the pointwise constant functor.
  §1.424  `𝒮^A` has binary products iff 𝒮 does — computed objectwise.
  §1.462  α : F → G is MONIC in `𝒮^A` iff every component α_A is monic in 𝒮.
  §1.521  `𝒮^A` has pullbacks (pointwise) when 𝒮 does.
          `𝒮^A` has images (pointwise, noncomputable) when 𝒮 does.
          RegularCategory requires also PullbacksTransferCovers — see TODO.

  Composition in diagram order throughout: `f ≫ g` = first f, then g.
-/

import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_27
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_45
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_56

open Freyd

universe v u

variable {𝒜 𝒮 : Type u} [Cat.{v} 𝒜] [Cat.{v} 𝒮]

namespace Freyd

/-! ## §1.422  Pointwise terminator in `𝒮^A` -/

/-- §1.422: The constant functor `A ↦ one` with every arrow mapping to `id_{one}`. -/
private def constOneFunctor [HasTerminal 𝒮] : Functor 𝒜 𝒮 where
  obj       := fun _ => one
  map      := fun _ => Cat.id one
  map_id   := fun _ => rfl
  map_comp := fun _ _ => (Cat.id_comp _).symm

/-- §1.422: Unique NT from F to `constOneFunctor`; component is `term (F.obj A)`. -/
private def toConstOne [HasTerminal 𝒮] (F : Functor 𝒜 𝒮) :
    FunctorHom F constOneFunctor where
  app        := fun A => term (F.obj A)
  naturality := fun {_ _} _ => term_uniq _ _

/-- §1.422: `𝒮^A` has a terminator: the constant functor at `one`. -/
instance functorCat_hasTerminal [HasTerminal 𝒮] : HasTerminal (Functor 𝒜 𝒮) where
  one  := constOneFunctor
  trm  := toConstOne
  uniq := fun {_} α β => NaturalTransformation.ext' fun A => term_uniq (α.app A) (β.app A)

/-! ## §1.424  Pointwise binary products in `𝒮^A` -/

/-- Helper: equality of two maps into a product from their projections. -/
private theorem prod_ext [HasBinaryProducts 𝒮] {X A B : 𝒮} {a b : X ⟶ prod A B}
    (hf : a ≫ fst = b ≫ fst) (hs : a ≫ snd = b ≫ snd) : a = b :=
  (pair_uniq _ _ _ rfl rfl).trans (by rw [hf, hs]; exact (pair_uniq _ _ _ rfl rfl).symm)

/-- §1.424: Objectwise product functor: (F × G)(A) = F(A) × G(A). -/
private def functorProd [HasBinaryProducts 𝒮] (F G : Functor 𝒜 𝒮) : Functor 𝒜 𝒮 where
  obj       := fun A => prod (F.obj A) (G.obj A)
  map      := fun {X Y} f => pair (fst ≫ F.map f) (snd ≫ G.map f)
  map_id   := fun _ => by
      simp only [F.map_id, G.map_id, Cat.comp_id]
      exact (pair_uniq _ _ _ (Cat.id_comp _) (Cat.id_comp _)).symm
  map_comp := fun {X Y Z} f g => by
      simp only [F.map_comp, G.map_comp]
      symm; apply pair_uniq
      · rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc]
      · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]

/-- §1.424: First projection NT: (fst_{F,G})_A = fst. -/
private def fstNT [HasBinaryProducts 𝒮] (F G : Functor 𝒜 𝒮) :
    FunctorHom (functorProd F G) F where
  app        := fun _ => fst
  naturality := fun {A B} f => by
    show (functorProd F G).map f ≫ fst = fst ≫ F.map f
    simp only [functorProd]; rw [fst_pair]

/-- §1.424: Second projection NT: (snd_{F,G})_A = snd. -/
private def sndNT [HasBinaryProducts 𝒮] (F G : Functor 𝒜 𝒮) :
    FunctorHom (functorProd F G) G where
  app        := fun _ => snd
  naturality := fun {A B} f => by
    show (functorProd F G).map f ≫ snd = snd ≫ G.map f
    simp only [functorProd]; rw [snd_pair]

/-- §1.424: Pairing NT: (pairNT α β)_A = pair (α_A) (β_A). -/
private def pairNT [HasBinaryProducts 𝒮] {X F G : Functor 𝒜 𝒮}
    (α : FunctorHom X F) (β : FunctorHom X G) : FunctorHom X (functorProd F G) where
  app        := fun A => pair (α.app A) (β.app A)
  naturality := fun {A B} f => by
    show (X.map f) ≫ pair (α.app B) (β.app B) =
         pair (α.app A) (β.app A) ≫ (functorProd F G).map f
    simp only [functorProd]
    apply prod_ext
    · rw [Cat.assoc, fst_pair, Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, ← α.naturality]
    · rw [Cat.assoc, snd_pair, Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, ← β.naturality]

/-- §1.424: `𝒮^A` has binary products, computed objectwise. -/
instance functorCat_hasProducts [HasBinaryProducts 𝒮] : HasBinaryProducts (Functor 𝒜 𝒮) where
  prod      := functorProd
  fst       := fstNT _ _
  snd       := sndNT _ _
  pair      := pairNT
  fst_pair  := fun α β => NaturalTransformation.ext' fun A => fst_pair (α.app A) (β.app A)
  snd_pair  := fun α β => NaturalTransformation.ext' fun A => snd_pair (α.app A) (β.app A)
  pair_uniq := fun α β γ h₁ h₂ => NaturalTransformation.ext' fun A =>
    pair_uniq (α.app A) (β.app A) (γ.app A)
      (congrFun (congrArg NaturalTransformation.app h₁) A)
      (congrFun (congrArg NaturalTransformation.app h₂) A)

/-! ## §1.462  Monic NT ↔ pointwise monic -/

/-- §1.462 (easy direction): components monic → NT monic in `𝒮^A`.
    If β ≫ α = γ ≫ α in `𝒮^A` then for every A, β_A ≫ α_A = γ_A ≫ α_A,
    so β_A = γ_A by the component hypothesis, hence β = γ. -/
theorem natTrans_monic_of_components_monic {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) (h : ∀ A, Monic (α.app A)) : Monic (𝒞 := Functor 𝒜 𝒮) α :=
  fun {_} β γ hβγ => NaturalTransformation.ext' fun A =>
    h A (β.app A) (γ.app A) (congrFun (congrArg NaturalTransformation.app hβγ) A)

-- §1.462 (hard direction): if α is monic in `𝒮^A`, every component is monic.
-- BOOK §1.462: ev_A is faithful (NTs equal iff all components equal), hence reflects monics.
-- PROVED: `natTrans_monic_components` below (via kernel-pair diagonal, §1.453).

/-! ## §1.521  Pointwise pullbacks in `𝒮^A` -/

-- Auxiliary: two maps to a pullback equal iff they agree on both projections.
private theorem pb_ext [HasPullbacks 𝒮] {A B C : 𝒮} {f : A ⟶ C} {g : B ⟶ C}
    (pb : HasPullback f g) {W : 𝒮} {u v : W ⟶ pb.cone.pt}
    (h₁ : u ≫ pb.cone.π₁ = v ≫ pb.cone.π₁) (h₂ : u ≫ pb.cone.π₂ = v ≫ pb.cone.π₂) : u = v :=
  let c : Cone f g := ⟨W, u ≫ pb.cone.π₁, u ≫ pb.cone.π₂, by rw [Cat.assoc, pb.cone.w, ← Cat.assoc]⟩
  (pb.lift_uniq c u rfl rfl).trans (pb.lift_uniq c v h₁.symm h₂.symm).symm

-- The cone used to build the transition map of the pullback functor.
private def pbCone [HasPullbacks 𝒮] {F G H : Functor 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    Cone (α.app Y) (β.app Y) :=
  ⟨_, (HasPullbacks.has (α.app X) (β.app X)).cone.π₁ ≫ F.map f,
      (HasPullbacks.has (α.app X) (β.app X)).cone.π₂ ≫ G.map f,
      by let pbX := HasPullbacks.has (α.app X) (β.app X)
         rw [Cat.assoc, α.naturality, ← Cat.assoc, pbX.cone.w, Cat.assoc, ← β.naturality, ← Cat.assoc]⟩

-- Transition map between pointwise pullback objects.
private def pbLiftMap [HasPullbacks 𝒮] {F G H : Functor 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    (HasPullbacks.has (α.app X) (β.app X)).cone.pt ⟶
    (HasPullbacks.has (α.app Y) (β.app Y)).cone.pt :=
  (HasPullbacks.has (α.app Y) (β.app Y)).lift (pbCone α β f)

private theorem pbLift_fst [HasPullbacks 𝒮] {F G H : Functor 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    pbLiftMap α β f ≫ (HasPullbacks.has (α.app Y) (β.app Y)).cone.π₁ =
    (HasPullbacks.has (α.app X) (β.app X)).cone.π₁ ≫ F.map f :=
  (HasPullbacks.has (α.app Y) (β.app Y)).lift_fst _

private theorem pbLift_snd [HasPullbacks 𝒮] {F G H : Functor 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    pbLiftMap α β f ≫ (HasPullbacks.has (α.app Y) (β.app Y)).cone.π₂ =
    (HasPullbacks.has (α.app X) (β.app X)).cone.π₂ ≫ G.map f :=
  (HasPullbacks.has (α.app Y) (β.app Y)).lift_snd _

/-- §1.521: Pointwise pullback functor object in `𝒮^A`. -/
private def pbFunObj [HasPullbacks 𝒮] {F G H : Functor 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) : Functor 𝒜 𝒮 where
  obj       := fun A => (HasPullbacks.has (α.app A) (β.app A)).cone.pt
  map      := pbLiftMap α β
  map_id   := fun A => pb_ext (HasPullbacks.has (α.app A) (β.app A))
      (by rw [pbLift_fst, F.map_id, Cat.comp_id, Cat.id_comp])
      (by rw [pbLift_snd, G.map_id, Cat.comp_id, Cat.id_comp])
  map_comp := fun {X Y Z} f g => by
      let pbX := HasPullbacks.has (α.app X) (β.app X)
      let pbZ := HasPullbacks.has (α.app Z) (β.app Z)
      have hf1 : pbLiftMap α β (f ≫ g) ≫ pbZ.cone.π₁ = pbX.cone.π₁ ≫ F.map f ≫ F.map g :=
        by rw [pbLift_fst, F.map_comp]
      have hf2 : (pbLiftMap α β f ≫ pbLiftMap α β g) ≫ pbZ.cone.π₁ = pbX.cone.π₁ ≫ F.map f ≫ F.map g :=
        by rw [Cat.assoc, pbLift_fst, ← Cat.assoc, pbLift_fst, Cat.assoc]
      have hs1 : pbLiftMap α β (f ≫ g) ≫ pbZ.cone.π₂ = pbX.cone.π₂ ≫ G.map f ≫ G.map g :=
        by rw [pbLift_snd, G.map_comp]
      have hs2 : (pbLiftMap α β f ≫ pbLiftMap α β g) ≫ pbZ.cone.π₂ = pbX.cone.π₂ ≫ G.map f ≫ G.map g :=
        by rw [Cat.assoc, pbLift_snd, ← Cat.assoc, pbLift_snd, Cat.assoc]
      exact pb_ext pbZ (hf1.trans hf2.symm) (hs1.trans hs2.symm)

-- pbFunObj.map = pbLiftMap by rfl, needed for naturality rewrites.
private theorem pbFunObj_map [HasPullbacks 𝒮] {F G H : Functor 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H) {X Y : 𝒜} (f : X ⟶ Y) :
    (pbFunObj α β).map f = pbLiftMap α β f := rfl

-- Lift of a cone into the pointwise pullback; component at A is the pointwise lift.
private def liftApp [HasPullbacks 𝒮] {F G H : Functor 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H)
    (c : Cone (𝒞 := Functor 𝒜 𝒮) α β) (A : 𝒜) :
    c.pt.obj A ⟶ (HasPullbacks.has (α.app A) (β.app A)).cone.pt :=
  (HasPullbacks.has (α.app A) (β.app A)).lift
    ⟨c.pt.obj A, c.π₁.app A, c.π₂.app A, congrFun (congrArg NaturalTransformation.app c.w) A⟩

private def pbNTLift [HasPullbacks 𝒮] {F G H : Functor 𝒜 𝒮}
    (α : FunctorHom F H) (β : FunctorHom G H)
    (c : Cone (𝒞 := Functor 𝒜 𝒮) α β) : FunctorHom c.pt (pbFunObj α β) where
  app        := liftApp α β c
  naturality := fun {A B} f => by
    let pbB := HasPullbacks.has (α.app B) (β.app B)
    apply pb_ext pbB
    · rw [pbFunObj_map, Cat.assoc,
          show liftApp α β c B ≫ (HasPullbacks.has (α.app B) (β.app B)).cone.π₁ = c.π₁.app B
            from (HasPullbacks.has (α.app B) (β.app B)).lift_fst _,
          Cat.assoc, pbLift_fst, ← Cat.assoc,
          show liftApp α β c A ≫ (HasPullbacks.has (α.app A) (β.app A)).cone.π₁ = c.π₁.app A
            from (HasPullbacks.has (α.app A) (β.app A)).lift_fst _,
          ← c.π₁.naturality]
    · rw [pbFunObj_map, Cat.assoc,
          show liftApp α β c B ≫ (HasPullbacks.has (α.app B) (β.app B)).cone.π₂ = c.π₂.app B
            from (HasPullbacks.has (α.app B) (β.app B)).lift_snd _,
          Cat.assoc, pbLift_snd, ← Cat.assoc,
          show liftApp α β c A ≫ (HasPullbacks.has (α.app A) (β.app A)).cone.π₂ = c.π₂.app A
            from (HasPullbacks.has (α.app A) (β.app A)).lift_snd _,
          ← c.π₂.naturality]

/-- §1.521: `𝒮^A` has pullbacks, computed pointwise. -/
instance functorCat_hasPullbacks [HasPullbacks 𝒮] : HasPullbacks (Functor 𝒜 𝒮) where
  has α β := {
    cone := {
      pt := pbFunObj α β
      π₁ := {
        app        := fun A => (HasPullbacks.has (α.app A) (β.app A)).cone.π₁
        naturality := fun {_ _} f => pbLift_fst α β f
      }
      π₂ := {
        app        := fun A => (HasPullbacks.has (α.app A) (β.app A)).cone.π₂
        naturality := fun {_ _} f => pbLift_snd α β f
      }
      w := NaturalTransformation.ext' fun A => (HasPullbacks.has (α.app A) (β.app A)).cone.w
    }
    lift     := pbNTLift α β
    lift_fst := fun _ => NaturalTransformation.ext' fun A =>
      (HasPullbacks.has (α.app A) (β.app A)).lift_fst _
    lift_snd := fun _ => NaturalTransformation.ext' fun A =>
      (HasPullbacks.has (α.app A) (β.app A)).lift_snd _
    lift_uniq := fun c u h₁ h₂ => NaturalTransformation.ext' fun A =>
      (HasPullbacks.has (α.app A) (β.app A)).lift_uniq
        ⟨_, c.π₁.app A, c.π₂.app A, congrFun (congrArg NaturalTransformation.app c.w) A⟩
        (u.app A)
        (congrFun (congrArg NaturalTransformation.app h₁) A)
        (congrFun (congrArg NaturalTransformation.app h₂) A)
  }

/-! ## §1.521  Pointwise images in `𝒮^A` (partial construction) -/

/-
  The transition map for the image domain functor exists by a pullback argument.
  Given α : FunctorHom F G, f : X ⟶ Y in 𝒜, we want
    imgTransMap f : (image (α.app X)).dom ⟶ (image (α.app Y)).dom
  satisfying: imgTransMap f ≫ (image (α.app Y)).arr = (image (α.app X)).arr ≫ G.map f.

  Construction: pull back (image (α.app Y)).arr along (image (α.app X)).arr ≫ G.map f.
  The cospan is: (image α_X).dom —[arr_X ≫ G.map f]→ G.obj Y ←[arr_Y]— (image α_Y).dom.
  Pullback P has projections π₁ : P → (image α_X).dom (monic, pullback of mono)
  and π₂ : P → (image α_Y).dom.
  Canonical cone from F.obj X: (image.lift(α_X), F.map f ≫ image.lift(α_Y)).
  This cone maps into P; the first leg image.lift(α_X) factors through the monic π₁.
  image.lift(α_X) is a cover (image_lift_cover), so π₁ is iso.
  imgTransMap f := π₁⁻¹ ≫ π₂.
-/

-- Pullback of (image α_Y).arr along (image α_X).arr ≫ G.map f.
private noncomputable def imgTransPB [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    HasPullback ((image (α.app X)).arr ≫ G.map f) (image (α.app Y)).arr :=
  HasPullbacks.has _ _

private theorem imgTransPB_π₁_mono [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    Monic (imgTransPB α f).cone.π₁ :=
  mono_pullback ((image (α.app X)).arr ≫ G.map f)
    (image (α.app Y)).arr (image (α.app Y)).monic (imgTransPB α f)

-- Canonical cone: π₁ := image.lift(α.app X), π₂ := F.map f ≫ image.lift(α.app Y).
-- Cone equation: lift_X ≫ arr_X ≫ G.map f = α_X ≫ G.map f = F.map f ≫ α_Y
--              = (F.map f ≫ lift_Y) ≫ arr_Y.
private noncomputable def imgTransCone [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    Cone ((image (α.app X)).arr ≫ G.map f) (image (α.app Y)).arr :=
  ⟨F.obj X, image.lift (α.app X), F.map f ≫ image.lift (α.app Y), by
    calc image.lift (α.app X) ≫ (image (α.app X)).arr ≫ G.map f
        = α.app X ≫ G.map f :=
            by rw [← Cat.assoc, image.lift_fac]
      _ = F.map f ≫ α.app Y :=
            (α.naturality f).symm
      _ = (F.map f ≫ image.lift (α.app Y)) ≫ (image (α.app Y)).arr :=
            by rw [Cat.assoc, image.lift_fac]⟩

-- The lift of imgTransCone satisfies: lift ≫ π₁ = image.lift(α.app X).
-- Since image.lift(α.app X) is a cover (image_lift_cover) and factors through monic π₁,
-- π₁ is an isomorphism.
private theorem imgTransPB_π₁_iso [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    IsIso (imgTransPB α f).cone.π₁ :=
  image_lift_cover (α.app X) (imgTransPB α f).cone.π₁
    ((imgTransPB α f).lift (imgTransCone α f))
    (imgTransPB_π₁_mono α f)
    ((imgTransPB α f).lift_fst (imgTransCone α f))

-- Extract the inverse of π₁ using Classical.choose.
-- IsIso (π₁ : P → D) = ∃ g : D → P, π₁ ≫ g = id ∧ g ≫ π₁ = id, so inverse : D → P.
-- Here D = (image α_X).dom, P = (imgTransPB α f).cone.pt.
private noncomputable def imgTransπ₁inv [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    (image (α.app X)).dom ⟶ (imgTransPB α f).cone.pt :=
  Classical.choose (imgTransPB_π₁_iso α f)

/-- The transition map: π₁⁻¹ ≫ π₂ : (image α_X).dom ⟶ (image α_Y).dom.
    π₁⁻¹ : (image α_X).dom → (imgTransPB α f).cone.pt  (inverse of π₁ : P → (image α_X).dom)
    π₂   : (imgTransPB α f).cone.pt → (image α_Y).dom. -/
noncomputable def imgTransMap [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    (image (α.app X)).dom ⟶ (image (α.app Y)).dom :=
  imgTransπ₁inv α f ≫ (imgTransPB α f).cone.π₂

/-- Key equation: imgTransMap f ≫ (image α_Y).arr = (image α_X).arr ≫ G.map f.
    Proof: unfold imgTransMap = π₁⁻¹ ≫ π₂; use π₂ ≫ arr_Y = π₁ ≫ (arr_X ≫ G.map f) from
    cone.w; then π₁⁻¹ ≫ π₁ = id gives the result. -/
theorem imgTrans_comm [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) {X Y : 𝒜} (f : X ⟶ Y) :
    imgTransMap α f ≫ (image (α.app Y)).arr =
    (image (α.app X)).arr ≫ G.map f := by
  -- unfold imgTransMap; then use Cat.assoc to group π₁⁻¹ ≫ (π₂ ≫ arr_Y), then cone.w.
  unfold imgTransMap
  -- the show-coercion refolds `Classical.choose … = imgTransπ₁inv` so rw's syntactic match sees it
  rw [Cat.assoc (imgTransπ₁inv α f), ← (imgTransPB α f).cone.w,
      ← Cat.assoc (imgTransπ₁inv α f),
      show imgTransπ₁inv α f ≫ (imgTransPB α f).cone.π₁ = Cat.id _ from
        (Classical.choose_spec (imgTransPB_π₁_iso α f)).2,
      Cat.id_comp]

private theorem imgTransMap_id [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) (X : 𝒜) :
    imgTransMap α (Cat.id X) = Cat.id (image (α.app X)).dom := by
  apply (image (α.app X)).monic
  rw [imgTrans_comm, G.map_id, Cat.comp_id, Cat.id_comp]

private theorem imgTransMap_comp [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imgTransMap α (f ≫ g) = imgTransMap α f ≫ imgTransMap α g := by
  apply (image (α.app Z)).monic
  -- Both sides ≫ arr_Z equal arr_X ≫ (G.map f ≫ G.map g) [right-grouped].
  have h1 : imgTransMap α (f ≫ g) ≫ (image (α.app Z)).arr =
            (image (α.app X)).arr ≫ (G.map f ≫ G.map g) := by
    rw [imgTrans_comm, G.map_comp]
  have h2 : (imgTransMap α f ≫ imgTransMap α g) ≫ (image (α.app Z)).arr =
            (image (α.app X)).arr ≫ (G.map f ≫ G.map g) :=
    calc (imgTransMap α f ≫ imgTransMap α g) ≫ (image (α.app Z)).arr
        = imgTransMap α f ≫ (imgTransMap α g ≫ (image (α.app Z)).arr) :=
            Cat.assoc _ _ _
      _ = imgTransMap α f ≫ ((image (α.app Y)).arr ≫ G.map g) :=
            by rw [imgTrans_comm α g]
      _ = (imgTransMap α f ≫ (image (α.app Y)).arr) ≫ G.map g :=
            (Cat.assoc _ _ _).symm
      _ = ((image (α.app X)).arr ≫ G.map f) ≫ G.map g :=
            by rw [imgTrans_comm α f]
      _ = (image (α.app X)).arr ≫ (G.map f ≫ G.map g) :=
            Cat.assoc _ _ _
  rw [h1, ← h2]

/-- §1.521: Functor A ↦ (image (α_A)).dom with transition maps imgTransMap. -/
noncomputable def imageFunObj [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) : Functor 𝒜 𝒮 where
  obj       := fun A => (image (α.app A)).dom
  map      := imgTransMap α
  map_id   := imgTransMap_id α
  map_comp := fun f g => imgTransMap_comp α f g

/-- §1.521: NT arr : imageFunObj α ⟶ G, components (image (α_A)).arr, natural by imgTrans_comm. -/
noncomputable def imgArrNT [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) : FunctorHom (imageFunObj α) G where
  app        := fun A => (image (α.app A)).arr
  naturality := fun {_ _} f => imgTrans_comm α f

/-- §1.521: imgArrNT α is monic in 𝒮^A (componentwise monic → NT monic, §1.462 easy). -/
theorem imgArrNT_monic [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) : Monic (𝒞 := Functor 𝒜 𝒮) (imgArrNT α) :=
  natTrans_monic_of_components_monic (imgArrNT α) (fun A => (image (α.app A)).monic)

/-- §1.521: Lift NT imageLiftNT : F ⟶ imageFunObj α, components image.lift (α_A).
    Naturality: both sides ≫ image(α_B).arr agree, using imgTrans_comm + α.naturality. -/
noncomputable def imageLiftNT [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) : FunctorHom F (imageFunObj α) where
  app        := fun A => image.lift (α.app A)
  naturality := fun {X Y} f => by
    -- Goal: F.map f ≫ image.lift(α.app Y) = image.lift(α.app X) ≫ imgTransMap α f
    -- Post-compose with the monic arr_Y; both sides equal α.app X ≫ G.map f.
    apply (image (α.app Y)).monic
    -- Use show to give explicit types and avoid Cat.assoc misfire on Functor.map.
    show (F.map f ≫ image.lift (α.app Y)) ≫ (image (α.app Y)).arr =
         (image.lift (α.app X) ≫ imgTransMap α f) ≫ (image (α.app Y)).arr
    calc (F.map f ≫ image.lift (α.app Y)) ≫ (image (α.app Y)).arr
        = F.map f ≫ α.app Y :=
            by rw [Cat.assoc (F.map f), image.lift_fac]
      _ = α.app X ≫ G.map f := α.naturality f
      _ = image.lift (α.app X) ≫ (image (α.app X)).arr ≫ G.map f :=
            by rw [← Cat.assoc (image.lift (α.app X)), image.lift_fac]
      _ = image.lift (α.app X) ≫ imgTransMap α f ≫ (image (α.app Y)).arr :=
            by rw [← imgTrans_comm]
      _ = (image.lift (α.app X) ≫ imgTransMap α f) ≫ (image (α.app Y)).arr :=
            (Cat.assoc _ _ _).symm

/-- §1.521: imageLiftNT ≫ imgArrNT = α (the pointwise image factorization). -/
theorem imageLiftNT_fac [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) :
    natTrans_comp (imageLiftNT α) (imgArrNT α) = α :=
  NaturalTransformation.ext' fun A => image.lift_fac (α.app A)

/-! ## §1.462 (hard direction) via evaluation functors and pointwise kernel pairs -/

/-- §1.462: The evaluation functor `ev_A : 𝒮^𝒜 → 𝒮`, sending `T ↦ T.obj A`
    and `α ↦ α.app A`. -/
def evFunctor (A : 𝒜) : Functor 𝒜 𝒮 → 𝒮 := fun T => T.obj A

/-- A component of an iso NT is iso: if `α` is iso in `Functor 𝒜 𝒮`, then `α.app A` is iso. -/
theorem natTrans_iso_component {F G : Functor 𝒜 𝒮} {α : FunctorHom F G}
    (hiso : IsIso (𝒞 := Functor 𝒜 𝒮) α) (A : 𝒜) : IsIso (α.app A) := by
  obtain ⟨β, h₁, h₂⟩ := hiso
  exact ⟨β.app A,
    congrFun (congrArg NaturalTransformation.app h₁) A,
    congrFun (congrArg NaturalTransformation.app h₂) A⟩

/-- The diagonal map for `α` in `𝒮^𝒜` evaluates at `A` to the diagonal for `α.app A`.
    Both are the unique lift of (id, id) into the pointwise kernel-pair pullback. -/
private theorem kp_diag_app_eq [HasTerminal 𝒮] [HasBinaryProducts 𝒮] [hpull : HasPullbacks 𝒮]
    (A : 𝒜) {F G : Functor 𝒜 𝒮} (α : FunctorHom F G) :
    (kp_diag (f := α) (hpull := functorCat_hasPullbacks)).app A =
    kp_diag (f := α.app A) (hpull := hpull) := by
  -- kp_diag(α.app A) = lift of diagCone; kp_diag(α).app A also lifts diagCone.
  -- By lift_uniq they are equal.
  -- for α.app A: kp_diag(α.app A) ≫ π₁ = id = diagCone.π₁.
  -- kp_diag(α.app A) = lift (diagCone) by definition.
  -- So it suffices to show kp_diag(α).app A ≫ π₁ = id and ≫ π₂ = id.
  symm
  apply (HasPullbacks.has (α.app A) (α.app A)).lift_uniq (diagCone (f := α.app A))
  · -- kp_diag(α).app A ≫ kp₁(α.app A) = Cat.id (F.obj A)
    -- for α in 𝒮^𝒜: kp_diag(α) ≫ kp₁(α) = natTrans_id F
    -- component at A: (kp_diag(α) ≫ kp₁(α)).app A = (natTrans_id F).app A = Cat.id
    exact congrFun (congrArg NaturalTransformation.app
      (kp_diag_p₁ (f := α) (hpull := functorCat_hasPullbacks))) A
  · -- kp_diag(α).app A ≫ kp₂(α.app A) = Cat.id (F.obj A)
    exact congrFun (congrArg NaturalTransformation.app
      (kp_diag_p₂ (f := α) (hpull := functorCat_hasPullbacks))) A

/-- §1.462 (hard direction): NT monic in `𝒮^𝒜` ⟹ each component monic in `𝒮`.
    Via §1.453 kernel pairs: α monic ↔ kp_diag iso; kp_diag is pointwise; component of iso is iso. -/
theorem natTrans_monic_components [HasTerminal 𝒮] [HasBinaryProducts 𝒮] [hpull : HasPullbacks 𝒮]
    {F G : Functor 𝒜 𝒮} (α : FunctorHom F G)
    (hm : Monic (𝒞 := Functor 𝒜 𝒮) α) (A : 𝒜) : Monic (α.app A) := by
  -- α monic → kp_diag(α) iso in 𝒮^𝒜 (using 𝒮^𝒜 has Terminal, Products, Pullbacks)
  have hkp_iso : IsIso (𝒞 := Functor 𝒜 𝒮)
      (kp_diag (f := α) (hpull := functorCat_hasPullbacks)) :=
    (monic_iff_kp_diag_iso (hpull := functorCat_hasPullbacks)
      (hp := functorCat_hasProducts) (ht := functorCat_hasTerminal)).mp hm
  -- Component at A of an iso is iso
  have hcomp_iso : IsIso ((kp_diag (f := α) (hpull := functorCat_hasPullbacks)).app A) :=
    natTrans_iso_component hkp_iso A
  -- Equate kp_diag(α).app A with kp_diag(α.app A) via pointwise-pullback construction
  rw [kp_diag_app_eq A α] at hcomp_iso
  -- kp_diag(α.app A) iso → α.app A monic; unfold Monic to avoid definition barrier
  exact fun {W} g h heq => (monic_iff_kp_diag_iso (hpull := hpull) (hp := ‹HasBinaryProducts 𝒮›)
    (ht := ‹HasTerminal 𝒮›)).mpr hcomp_iso g h heq

/-! ## §1.521  HasImages (Functor 𝒜 𝒮) — complete instance -/

-- Helper: extract the component-wise allows data from a functor-cat allows.
-- Given S : Subobject (𝒮^𝒜) G and hallow : Allows S α, extract at each A:
--   γ_A : F.obj A ⟶ S.dom.obj A  with  γ_A ≫ S.arr.app A = α.app A.
private noncomputable def allowsCompAt [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) (S : Subobject (Functor 𝒜 𝒮) G)
    (hallow : Allows S α) (A : 𝒜) : F.obj A ⟶ S.dom.obj A :=
  hallow.choose.app A

-- The minimality NT component at A: the unique map (image α_A).dom → S.dom.obj A.
private noncomputable def imageMinComp [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) (S : Subobject (Functor 𝒜 𝒮) G)
    (hallow : Allows S α) (A : 𝒜) : (image (α.app A)).dom ⟶ S.dom.obj A :=
  (image_min (α.app A) ⟨S.dom.obj A, S.arr.app A,
    natTrans_monic_components S.arr S.monic A⟩
    ⟨allowsCompAt α S hallow A,
      congrFun (congrArg NaturalTransformation.app hallow.choose_spec) A⟩).choose

private theorem imageMinComp_fac [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) (S : Subobject (Functor 𝒜 𝒮) G)
    (hallow : Allows S α) (A : 𝒜) :
    imageMinComp α S hallow A ≫ S.arr.app A = (image (α.app A)).arr :=
  (image_min (α.app A) ⟨S.dom.obj A, S.arr.app A,
    natTrans_monic_components S.arr S.monic A⟩
    ⟨allowsCompAt α S hallow A,
      congrFun (congrArg NaturalTransformation.app hallow.choose_spec) A⟩).choose_spec

/-- The minimality NT: given `S : Subobject (𝒮^𝒜) G` allowing `α`,
    build `h : imageFunObj α ⟶ S.dom` with `h ≫ S.arr = imgArrNT α`.
    Component at A: `imageMinComp α S hallow A` (via image minimality in 𝒮 at each point).
    Naturality: cancel by the monic `S.arr.app B`, use `imgTrans_comm` + `imageMinComp_fac`. -/
private noncomputable def imageMinNT [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) (S : Subobject (Functor 𝒜 𝒮) G)
    (hallow : Allows S α) : FunctorHom (imageFunObj α) S.dom where
  app      := imageMinComp α S hallow
  naturality {A B} f := by
    -- Post-cancel with S.arr.app B (monic).
    apply natTrans_monic_components S.arr S.monic B
    -- Goal after Monic: LHS ≫ S.arr.app B = RHS ≫ S.arr.app B
    -- LHS: (imageFunObj α).map f ≫ imageMinComp α S hallow B
    -- RHS: imageMinComp α S hallow A ≫ S.dom.map f
    -- Rewrite both sides.
    -- LHS ≫ S.arr.app B = (imageFunObj α).map f ≫ imageMinComp α S hallow B ≫ S.arr.app B
    --   = imgTransMap α f ≫ (image (α.app B)).arr      [imageMinComp_fac]
    --   = (image (α.app A)).arr ≫ G.map f              [imgTrans_comm]
    -- RHS ≫ S.arr.app B = imageMinComp α S hallow A ≫ S.dom.map f ≫ S.arr.app B
    --   = imageMinComp α S hallow A ≫ S.arr.app A ≫ G.map f  [S.arr.naturality]
    --   = (image (α.app A)).arr ≫ G.map f              [imageMinComp_fac]
    show ((imageFunObj α).map f ≫ imageMinComp α S hallow B) ≫ S.arr.app B =
         (imageMinComp α S hallow A ≫ S.dom.map f) ≫ S.arr.app B
    rw [Cat.assoc, imageMinComp_fac,
        show (imageFunObj α).map f = imgTransMap α f from rfl,
        imgTrans_comm, Cat.assoc, S.arr.naturality, ← Cat.assoc, imageMinComp_fac]

/-- imageMinNT satisfies: `natTrans_comp (imageMinNT α S hallow) S.arr = imgArrNT α`. -/
private theorem imageMinNT_fac [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) (S : Subobject (Functor 𝒜 𝒮) G) (hallow : Allows S α) :
    natTrans_comp (imageMinNT α S hallow) S.arr = imgArrNT α :=
  NaturalTransformation.ext' fun A => imageMinComp_fac α S hallow A

/-- §1.521: `𝒮^𝒜` has images, computed pointwise (given `[RegularCategory 𝒮]`). -/
noncomputable instance functorCat_hasImages [RegularCategory 𝒮] :
    HasImages (Functor 𝒜 𝒮) where
  image   := fun {_ _} α => ⟨imageFunObj α, imgArrNT α, imgArrNT_monic α⟩
  isImage := fun {_ _} α => ⟨
    ⟨imageLiftNT α, imageLiftNT_fac α⟩,
    fun S hallow => ⟨imageMinNT α S hallow, imageMinNT_fac α S hallow⟩⟩

/-! ## §1.521 Cover characterization and PullbacksTransferCovers for `𝒮^𝒜` -/

/-- Cover in `𝒮^𝒜` iff every component is a cover in `𝒮`.
    Forward via §1.462 hard + image entirety; backward by building the inverse NT. -/
theorem cover_functorCat_iff [RegularCategory 𝒮] {F G : Functor 𝒜 𝒮}
    (α : FunctorHom F G) :
    Cover (𝒞 := Functor 𝒜 𝒮) α ↔ ∀ A : 𝒜, Cover (α.app A) := by
  constructor
  · intro hcov A
    -- cover_iff_image_entire gives: Subobject.IsEntire (image (𝒞 := 𝒮^𝒜) α) = IsIso (imgArrNT α)
    have hiso_NT : IsIso (𝒞 := Functor 𝒜 𝒮) (imgArrNT α) :=
      (cover_iff_image_entire (𝒞 := Functor 𝒜 𝒮) α).mp hcov
    -- Component at A is iso: IsIso ((imgArrNT α).app A) = IsIso (image (α.app A)).arr
    have hcomp_iso : IsIso ((imgArrNT α).app A) := natTrans_iso_component hiso_NT A
    -- Hence image (α.app A) is entire → Cover (α.app A)
    intro C m g hm hfac
    exact ((cover_iff_image_entire (α.app A)).mpr hcomp_iso) m g hm hfac
  · intro hcomps
    apply (cover_iff_image_entire (𝒞 := Functor 𝒜 𝒮) α).mpr
    -- Need: IsIso (imgArrNT α) in 𝒮^𝒜.
    -- Each component (imgArrNT α).app A = (image (α.app A)).arr is iso.
    -- (imgArrNT α).app A : (image (α.app A)).dom ⟶ G.obj A.
    -- IsIso f : ∃ g : G.obj A ⟶ (image (α.app A)).dom, f ≫ g = id ∧ g ≫ f = id.
    have hiso_comp : ∀ A : 𝒜, IsIso ((imgArrNT α).app A) := fun A =>
      (cover_iff_image_entire (α.app A)).mp (hcomps A)
    -- inv_app A : G.obj A ⟶ (image (α.app A)).dom = (imageFunObj α).obj A
    let inv_app : ∀ A : 𝒜, G.obj A ⟶ (imageFunObj α).obj A :=
      fun A => (hiso_comp A).choose
    let inv_fwd : ∀ A, (imgArrNT α).app A ≫ inv_app A = Cat.id _ :=
      fun A => (hiso_comp A).choose_spec.1
    let inv_bwd : ∀ A, inv_app A ≫ (imgArrNT α).app A = Cat.id _ :=
      fun A => (hiso_comp A).choose_spec.2
    -- inv_app is natural: post-cancel with (image (α.app B)).arr (monic)
    have inv_nat : ∀ {A B : 𝒜} (f : A ⟶ B),
        G.map f ≫ inv_app B = inv_app A ≫ (imageFunObj α).map f := by
      intro A B f
      -- cancel by post-composing with (image (α.app B)).arr using Monic
      apply (image (α.app B)).monic
      -- LHS: (G.map f ≫ inv_app B) ≫ arr_B
      -- = G.map f ≫ (inv_app B ≫ arr_B) = G.map f ≫ id = G.map f  [inv_bwd B]
      -- RHS: (inv_app A ≫ (imageFunObj α).map f) ≫ arr_B
      -- = inv_app A ≫ arr_A ≫ G.map f  [imgTrans_comm]
      -- = id ≫ G.map f = G.map f  [inv_bwd A]
      have hB : inv_app B ≫ (image (α.app B)).arr = Cat.id _ := inv_bwd B
      have hA : inv_app A ≫ (image (α.app A)).arr = Cat.id _ := inv_bwd A
      -- Use cat equations directly
      show (G.map f ≫ inv_app B) ≫ (image (α.app B)).arr =
           (inv_app A ≫ (imageFunObj α).map f) ≫ (image (α.app B)).arr
      calc (G.map f ≫ inv_app B) ≫ (image (α.app B)).arr
          = G.map f ≫ inv_app B ≫ (image (α.app B)).arr := Cat.assoc _ _ _
        _ = G.map f ≫ Cat.id _ := congrArg (G.map f ≫ ·) hB
        _ = G.map f := Cat.comp_id _
        _ = Cat.id _ ≫ G.map f := (Cat.id_comp _).symm
        _ = (inv_app A ≫ (image (α.app A)).arr) ≫ G.map f :=
              congrArg (· ≫ G.map f) hA.symm
        _ = inv_app A ≫ (image (α.app A)).arr ≫ G.map f := Cat.assoc _ _ _
        _ = inv_app A ≫ imgTransMap α f ≫ (image (α.app B)).arr := by rw [imgTrans_comm]
        _ = (inv_app A ≫ (imageFunObj α).map f) ≫ (image (α.app B)).arr :=
              (Cat.assoc _ _ _).symm
    exact ⟨⟨inv_app, fun {A B} f => inv_nat f⟩,
           NaturalTransformation.ext' inv_fwd,
           NaturalTransformation.ext' inv_bwd⟩

/-- A pullback cone in `𝒮^𝒜` gives a pullback in `𝒮` at each component.
    Proof: use the canonical pointwise pullback as an isomorphic intermediary. -/
private theorem functorCat_pb_component [HasPullbacks 𝒮]
    {F G H : Functor 𝒜 𝒮} {α : FunctorHom F H} {β : FunctorHom G H}
    (c : Cone (𝒞 := Functor 𝒜 𝒮) α β) (hpb : c.IsPullback) (A : 𝒜) :
    (⟨c.pt.obj A, c.π₁.app A, c.π₂.app A,
      congrFun (congrArg NaturalTransformation.app c.w) A⟩ : Cone (α.app A) (β.app A)).IsPullback := by
  -- canonPB: the chosen pullback of α along β in 𝒮^𝒜 (pointwise by pbFunObj).
  let canonPB := (functorCat_hasPullbacks (𝒜 := 𝒜) (𝒮 := 𝒮)).has α β
  -- u : canonPB.cone.pt ⟶ c.pt  (canonical to c, unique factoring)
  obtain ⟨u, ⟨hu1, hu2⟩, hu_uniq⟩ := hpb canonPB.cone
  -- v : c.pt ⟶ canonPB.cone.pt  (c to canonical)
  let v    := canonPB.lift c
  let hv1  : natTrans_comp v canonPB.cone.π₁ = c.π₁ := canonPB.lift_fst c
  let hv2  : natTrans_comp v canonPB.cone.π₂ = c.π₂ := canonPB.lift_snd c
  -- v ≫ u = id_{c.pt}: use IsPullback of c applied to c itself.
  -- Both id and v ≫ u satisfy (−) ≫ c.π₁ = c.π₁ and (−) ≫ c.π₂ = c.π₂.
  have hvu : natTrans_comp v u = natTrans_id c.pt := by
    obtain ⟨uid, ⟨huid1, huid2⟩, huid_uniq⟩ := hpb c
    -- uid satisfies uid ≫ c.π₁ = c.π₁ and uid ≫ c.π₂ = c.π₂.
    -- id also satisfies this: id ≫ π = π.
    have hid_eq : uid = natTrans_id c.pt :=
      (huid_uniq (natTrans_id c.pt) (Cat.id_comp c.π₁) (Cat.id_comp c.π₂)).symm
    -- v ≫ u also satisfies this:
    have hvu1 : natTrans_comp (natTrans_comp v u) c.π₁ = c.π₁ :=
      NaturalTransformation.ext' fun X =>
        calc (natTrans_comp (natTrans_comp v u) c.π₁).app X
            = (v.app X ≫ u.app X) ≫ c.π₁.app X := rfl
          _ = v.app X ≫ u.app X ≫ c.π₁.app X := Cat.assoc _ _ _
          _ = v.app X ≫ canonPB.cone.π₁.app X :=
              congrArg (v.app X ≫ ·)
                (congrFun (congrArg NaturalTransformation.app hu1) X)
          _ = c.π₁.app X :=
              congrFun (congrArg NaturalTransformation.app hv1) X
    have hvu2 : natTrans_comp (natTrans_comp v u) c.π₂ = c.π₂ :=
      NaturalTransformation.ext' fun X =>
        calc (natTrans_comp (natTrans_comp v u) c.π₂).app X
            = (v.app X ≫ u.app X) ≫ c.π₂.app X := rfl
          _ = v.app X ≫ u.app X ≫ c.π₂.app X := Cat.assoc _ _ _
          _ = v.app X ≫ canonPB.cone.π₂.app X :=
              congrArg (v.app X ≫ ·)
                (congrFun (congrArg NaturalTransformation.app hu2) X)
          _ = c.π₂.app X :=
              congrFun (congrArg NaturalTransformation.app hv2) X
    exact hid_eq ▸ (huid_uniq (natTrans_comp v u) hvu1 hvu2)
  -- Component at A: v.app A ≫ u.app A = Cat.id (c.pt.obj A)
  have hvu_A : v.app A ≫ u.app A = Cat.id (c.pt.obj A) :=
    congrFun (congrArg NaturalTransformation.app hvu) A
  -- u.app A ≫ c.π₁.app A = canonPB.cone.π₁.app A  (= (HasPullbacks.has (α.app A) (β.app A)).cone.π₁)
  have hu1_A : u.app A ≫ c.π₁.app A = canonPB.cone.π₁.app A :=
    congrFun (congrArg NaturalTransformation.app hu1) A
  have hu2_A : u.app A ≫ c.π₂.app A = canonPB.cone.π₂.app A :=
    congrFun (congrArg NaturalTransformation.app hu2) A
  -- v.app A ≫ canonPB.cone.π₁.app A = c.π₁.app A
  have hv1_A : v.app A ≫ canonPB.cone.π₁.app A = c.π₁.app A :=
    congrFun (congrArg NaturalTransformation.app hv1) A
  have hv2_A : v.app A ≫ canonPB.cone.π₂.app A = c.π₂.app A :=
    congrFun (congrArg NaturalTransformation.app hv2) A
  -- canonPB.cone.π₁.app A = (HasPullbacks.has (α.app A) (β.app A)).cone.π₁  (by definition of pbFunObj)
  let kpA := HasPullbacks.has (α.app A) (β.app A)
  -- Note: canonPB.cone.π₁.app A = kpA.cone.π₁ definitionally (by pbFunObj definition).
  -- We record these as equalities to use in rewrites.
  have hπ₁ : canonPB.cone.π₁.app A = kpA.cone.π₁ := rfl
  have hπ₂ : canonPB.cone.π₂.app A = kpA.cone.π₂ := rfl
  -- Given d : Cone (α.app A) (β.app A) in 𝒮, lift via kpA then compose with u.app A.
  intro d
  let liftK : d.pt ⟶ kpA.cone.pt := kpA.lift d
  refine ⟨liftK ≫ u.app A, ⟨?_, ?_⟩, ?_⟩
  · -- (liftK ≫ u.app A) ≫ c.π₁.app A = d.π₁
    calc (liftK ≫ u.app A) ≫ c.π₁.app A
        = liftK ≫ (u.app A ≫ c.π₁.app A) := Cat.assoc _ _ _
      _ = liftK ≫ kpA.cone.π₁            := by rw [hu1_A, hπ₁]
      _ = d.π₁                            := kpA.lift_fst d
  · -- (liftK ≫ u.app A) ≫ c.π₂.app A = d.π₂
    calc (liftK ≫ u.app A) ≫ c.π₂.app A
        = liftK ≫ (u.app A ≫ c.π₂.app A) := Cat.assoc _ _ _
      _ = liftK ≫ kpA.cone.π₂            := by rw [hu2_A, hπ₂]
      _ = d.π₂                            := kpA.lift_snd d
  · -- Uniqueness: if w ≫ c.π₁.app A = d.π₁ and w ≫ c.π₂.app A = d.π₂, then w = liftK ≫ u.app A.
    intro w hw1 hw2
    -- w ≫ v.app A factors d through kpA
    have hwv1 : (w ≫ v.app A) ≫ kpA.cone.π₁ = d.π₁ := by
      rw [Cat.assoc, ← hπ₁, hv1_A]; exact hw1
    have hwv2 : (w ≫ v.app A) ≫ kpA.cone.π₂ = d.π₂ := by
      rw [Cat.assoc, ← hπ₂, hv2_A]; exact hw2
    -- By kpA uniqueness: w ≫ v.app A = liftK
    have heq : w ≫ v.app A = liftK :=
      (kpA.lift_uniq d (w ≫ v.app A) hwv1 hwv2).trans
       (kpA.lift_uniq d liftK (kpA.lift_fst d) (kpA.lift_snd d)).symm
    -- w = liftK ≫ u.app A
    calc w = w ≫ Cat.id _         := (Cat.comp_id _).symm
      _ = w ≫ (v.app A ≫ u.app A) := by rw [hvu_A]
      _ = (w ≫ v.app A) ≫ u.app A := (Cat.assoc _ _ _).symm
      _ = liftK ≫ u.app A          := by rw [heq]

/-- §1.521: `PullbacksTransferCovers (𝒮^𝒜)` given `[RegularCategory 𝒮]`.
    Proof: use `cover_functorCat_iff` to reduce to pointwise, then apply 𝒮-PTC on the
    pointwise pullback (which is a pullback by `functorCat_pb_component`). -/
noncomputable instance functorCat_pullbacksTransferCovers [RegularCategory 𝒮] :
    PullbacksTransferCovers (Functor 𝒜 𝒮) where
  pullbacks_transfer_covers := fun {_ _ _} {α β} c hpb hcov => by
    -- Need: Cover c.π₂ in 𝒮^𝒜.  Use cover_functorCat_iff: suffices each (c.π₂).app A is a cover.
    rw [cover_functorCat_iff]
    intro A
    -- Build the pointwise cone at A
    let cA : Cone (α.app A) (β.app A) :=
      ⟨c.pt.obj A, c.π₁.app A, c.π₂.app A,
       congrFun (congrArg NaturalTransformation.app c.w) A⟩
    -- cA is a pullback in 𝒮 (by functorCat_pb_component)
    have hpbA : cA.IsPullback := functorCat_pb_component c hpb A
    -- α.app A is a cover (each component of α is a cover since α is a cover in 𝒮^𝒜)
    have hcovA : Cover (α.app A) := (cover_functorCat_iff α).mp hcov A
    -- Apply PTC in 𝒮 to cA
    intro C m g hm hfac
    exact PullbacksTransferCovers.pullbacks_transfer_covers cA hpbA hcovA m g hm hfac

/-- §1.521: `RegularCategory (Functor 𝒜 𝒮)` given `[RegularCategory 𝒮]`. -/
noncomputable instance functorCat_regularCategory [RegularCategory 𝒮] :
    RegularCategory (Functor 𝒜 𝒮) :=
  @RegularCategory.mk (Functor 𝒜 𝒮) _
    (functorCat_hasTerminal (𝒜 := 𝒜) (𝒮 := 𝒮))
    (functorCat_hasProducts (𝒜 := 𝒜) (𝒮 := 𝒮))
    (functorCat_hasPullbacks (𝒜 := 𝒜) (𝒮 := 𝒮))
    (functorCat_hasImages (𝒜 := 𝒜) (𝒮 := 𝒮))
    (functorCat_pullbacksTransferCovers (𝒜 := 𝒜) (𝒮 := 𝒮))

end Freyd
