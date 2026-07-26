/-
  Freyd & Scedrov, *Categories and Allegories* §1.631 / §1.633.

  §1.631  In a positive pre-logos a complemented subobject of a PROJECTIVE object is
          projective.
  §1.633  Consequently (with §1.525) the COMPLEMENTED SUBTERMINATORS of a CAPITAL
          positive pre-logos are projective.

  Both are self-contained Ch1 "capital theory": the positivity (disjoint coproduct)
  realises a complemented pair `(U,U₂)` of `Q` as `U.dom + U₂.dom ≅ Q`
  (`complementedSub_legs_iso`, §1.62), and a cover `f : A ↠ U.dom` is extended to the
  cover `case (f≫inl) inr : A + U₂.dom ↠ U.dom + U₂.dom ≅ Q`; `Projective Q` splits it
  and the disjointness of the coproduct (`invImage_inl_inrSub_le_any`) restricts the
  section to the `U`-half, giving a section of `f`.

  For §1.633, `Q := 1`, projective by `capital_one_projective` (§1.525).
-/

import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_56
import Freyd.S1_57
import Freyd.S1_58
import Freyd.S1_60
import Freyd.S1_61
import Freyd.S1_62
import Freyd.S1_658_Complement

open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

/-! ## §1.631  A complemented subobject of a projective object is projective -/

-- `DisjointBinaryCoproduct` provides, transitively, every instance used here:
-- `PreLogos → RegularCategory` gives terminal/products/pullbacks/images/transferCovers,
-- and `PreLogos`/`PositivePreLogos` give unions/bottom/coproducts.  Listing the
-- consequences separately would build instance diamonds (two `HasPullbacks` paths).
variable [DisjointBinaryCoproduct 𝒞]

/-- **§1.631**: in a positive pre-logos, a complemented subobject of a projective object
    is projective.  Given a complemented partition `(U, U₂)` of `Q` (the two clauses of
    `IsComplementedSub U` with complement `U₂`) and `Projective Q`, the domain `U.dom` is
    projective.

    PROOF (Freyd §1.631).  Let `f : A ↠ U.dom` be a cover.  By `complementedSub_legs_iso`
    there is an iso `ψ : U.dom + U₂.dom ≅ Q` with `inl ≫ ψ = U.arr`, `inr ≫ ψ = U₂.arr`.
    The copairing `k := case (f ≫ inl) inr : A + U₂.dom → U.dom + U₂.dom` has
    `image k = image(f≫inl) ∪ image inr = inl ∪ inr = ⊤` (the union of the two summands is
    entire by positivity), so `k` is a cover, and `k ≫ ψ : A + U₂.dom ↠ Q` is a cover.
    `Projective Q` splits it: `s ≫ (k ≫ ψ) = id_Q`.  Then `w := U.arr ≫ s : U.dom → A+U₂.dom`
    satisfies `w ≫ k = inl` (cancel the iso `ψ`), and `w` lands in the `A`-summand because
    its `inr`-inverse-image is empty (disjointness, `invImage_inl_inrSub_le_any`); the
    factor `t : U.dom → A` is the section of `f`. -/
theorem complementedSub_of_projective {Q : 𝒞} (U U₂ : Subobject 𝒞 Q)
    (hdisj : Subobject.le (Subobject.inter U U₂) (PreLogos.bottom Q))
    (hentire : Subobject.le (Subobject.entire Q) (HasSubobjectUnions.union U U₂))
    (hQ : Projective Q) :
    Projective U.dom := by
  classical
  -- Realise `Q ≅ U.dom + U₂.dom` with the legs matching the inclusions.
  obtain ⟨ψ, ψinv, hψψ, hψinvψ, hψl, hψr⟩ := complementedSub_legs_iso U U₂ hdisj hentire
  intro A f hf
  -- The copairing extending the cover `f` by the identity on the complement.
  let k : HasBinaryCoproducts.coprod A U₂.dom ⟶ HasBinaryCoproducts.coprod U.dom U₂.dom :=
    HasBinaryCoproducts.case (f ≫ HasBinaryCoproducts.inl) HasBinaryCoproducts.inr
  have hk_inl : HasBinaryCoproducts.inl ≫ k = f ≫ HasBinaryCoproducts.inl :=
    HasBinaryCoproducts.case_inl _ _
  have hk_inr : HasBinaryCoproducts.inr ≫ k = HasBinaryCoproducts.inr :=
    HasBinaryCoproducts.case_inr _ _
  -- `k` is a cover: its image is the union of the two summands, which is entire by positivity.
  have hk_cover : Cover k := by
    rw [cover_iff_image_entire]
    apply entire_of_entire_le
    -- image k = union (image (f≫inl)) (image inr)
    let J := image (f ≫ HasBinaryCoproducts.inl (A := U.dom) (B := U₂.dom))
    let Kr := image (HasBinaryCoproducts.inr (A := U.dom) (B := U₂.dom))
    have hUimg : IsImage k (HasSubobjectUnions.union J Kr) :=
      union_via_coproduct_image (f ≫ HasBinaryCoproducts.inl) HasBinaryCoproducts.inr
    -- `union J Kr` is minimal among subobjects allowing `k`, so `union J Kr ≤ image k`.
    have hUnion_le_image : (HasSubobjectUnions.union J Kr).le (image k) :=
      hUimg.2 (image k) (image_allows k)
    -- The whole `union J Kr` is ≥ `inl ∪ inr` = ⊤.  `inl` summand: image(f≫inl) = image inl
    -- (since `f` is a cover); both `≥` the corresponding injection subobjects.
    refine Subobject.le_trans ?_ hUnion_le_image
    -- entire ≤ inlSub ∪ inrSub ≤ J ∪ Kr
    have hsum : (Subobject.entire (HasBinaryCoproducts.coprod U.dom U₂.dom)).le
        (HasSubobjectUnions.union (inlSub (𝒞 := 𝒞) (A := U.dom) (B := U₂.dom) inl_mono)
                                  (inrSub (𝒞 := 𝒞) (A := U.dom) (B := U₂.dom) inr_mono)) :=
      inl_union_inr_entire
    -- inlSub ≤ J:  image(f≫inl) = image inl ≥ inlSub  (cover `f` precompose, then inl is its own image)
    have hInlJ : (inlSub (𝒞 := 𝒞) (A := U.dom) (B := U₂.dom) inl_mono).le J := by
      have hcc := (image_cover_comp f (HasBinaryCoproducts.inl (A := U.dom) (B := U₂.dom)) hf).2
      -- image inl ≤ image (f ≫ inl) = J;  inlSub = image inl.
      have hinlImg : (inlSub (𝒞 := 𝒞) (A := U.dom) (B := U₂.dom) inl_mono).le
          (image (HasBinaryCoproducts.inl (A := U.dom) (B := U₂.dom))) :=
        (monic_isImage _ inl_mono).2 _ (image_allows _)
      exact Subobject.le_trans hinlImg hcc
    -- inrSub ≤ Kr:  inr is its own image
    have hInrKr : (inrSub (𝒞 := 𝒞) (A := U.dom) (B := U₂.dom) inr_mono).le Kr :=
      (monic_isImage _ inr_mono).2 _ (image_allows _)
    exact Subobject.le_trans hsum (union_mono hInlJ hInrKr)
  -- `k ≫ ψ` is a cover (compose with iso); split it via `Projective Q`.
  have hkψ_cover : Cover (k ≫ ψ) :=
    cover_comp hk_cover (iso_cover ψ ⟨ψinv, hψψ, hψinvψ⟩)
  obtain ⟨s, hs⟩ := hQ (k ≫ ψ) hkψ_cover
  -- `w := U.arr ≫ s : U.dom → A + U₂.dom`.  Then `w ≫ k = inl` after cancelling `ψ`.
  let w : U.dom ⟶ HasBinaryCoproducts.coprod A U₂.dom := U.arr ≫ s
  have hwk : w ≫ k = HasBinaryCoproducts.inl := by
    -- (w ≫ k) ≫ ψ = U.arr ≫ s ≫ (k ≫ ψ) = U.arr ≫ id = U.arr = inl ≫ ψ; ψ monic.
    have hψmono : Monic ψ := by
      intro X u v huv
      have h := congrArg (· ≫ ψinv) huv
      simp only [Cat.assoc, hψψ, Cat.comp_id] at h
      exact h
    apply hψmono
    calc (w ≫ k) ≫ ψ = U.arr ≫ (s ≫ (k ≫ ψ)) := by
          simp only [w, Cat.assoc]
      _ = U.arr ≫ Cat.id Q := by rw [hs]
      _ = U.arr := Cat.comp_id _
      _ = HasBinaryCoproducts.inl ≫ ψ := hψl.symm
  -- `w` factors through `inl : A → A + U₂.dom`: its `inr`-inverse-image is empty.
  let il : A ⟶ HasBinaryCoproducts.coprod A U₂.dom := HasBinaryCoproducts.inl
  let ir : U₂.dom ⟶ HasBinaryCoproducts.coprod A U₂.dom := HasBinaryCoproducts.inr
  let Il := inlSub (𝒞 := 𝒞) (A := A) (B := U₂.dom) inl_mono
  let Ir := inrSub (𝒞 := 𝒞) (A := A) (B := U₂.dom) inr_mono
  -- (i) `w# Ir ≤ ⊥`:  a point of `w# Ir` makes `inl_U = inr_U` in `U.dom + U₂.dom`, hence factors
  --     through `⊥`, so the inverse-image domain is initial.
  have hwIr_bot : (InverseImage w Ir).le (PreLogos.bottom U.dom) := by
    let pb := HasPullbacks.has w Ir.arr
    -- the two legs `π₁ : (w#Ir).dom → U.dom`, `π₂ : (w#Ir).dom → U₂.dom = Ir.dom`
    -- give `π₁ ≫ w = π₂ ≫ ir`; post-compose with `k`:  π₁ ≫ inl_U = π₂ ≫ inr_U.
    have hsq : pb.cone.π₁ ≫ w = pb.cone.π₂ ≫ ir := pb.cone.w
    have hcross : (pb.cone.π₁ ≫ HasBinaryCoproducts.inl) = (pb.cone.π₂ ≫ HasBinaryCoproducts.inr) := by
      calc pb.cone.π₁ ≫ HasBinaryCoproducts.inl
          = pb.cone.π₁ ≫ (w ≫ k) := by rw [hwk]
        _ = (pb.cone.π₁ ≫ w) ≫ k := (Cat.assoc _ _ _).symm
        _ = (pb.cone.π₂ ≫ ir) ≫ k := by rw [hsq]
        _ = pb.cone.π₂ ≫ (ir ≫ k) := Cat.assoc _ _ _
        _ = pb.cone.π₂ ≫ HasBinaryCoproducts.inr := by rw [hk_inr]
    -- disjointness of `U.dom + U₂.dom`: the cross point factors through `⊥(U.dom+U₂.dom)`.
    obtain ⟨e, _⟩ := coprod_inl_inr_disjoint_elt (𝒟 := 𝒞) (A := U.dom) (B := U₂.dom)
      pb.cone.π₁ pb.cone.π₂ hcross
    -- `e : (w#Ir).dom → ⊥(U+U₂).dom`; compose with `ζ : ⊥(U+U₂).dom ≅ 0` (the coterminator).
    -- `e ≫ ζ : (w#Ir).dom → 0` is iso (`any_map_to_zero_is_iso`), so `(w#Ir).dom ≅ 0 ≅ ⊥(U.dom).dom`,
    -- and `w#Ir ≤ ⊥(U.dom)` by `le_bottom_of_dom_iso`.  Use the AMBIENT `PreLogos` instance so all
    -- of `InverseImage`/`bottom`/`.zero` resolve along the same path (no instance diamond).
    letI hPL : PreLogos 𝒞 := inferInstance
    obtain ⟨ζ, ζspec⟩ := hPL.bottom_dom_iso (HasBinaryCoproducts.coprod U.dom U₂.dom)
      (HasTerminal.one)
    have hzero : Isomorphic (InverseImage w Ir).dom
        (minimal_subobject_of_one_is_coterminator hPL).zero := by
      obtain ⟨einv, h1, h2⟩ := any_map_to_zero_is_iso hPL (e ≫ ζ)
      exact ⟨e ≫ ζ, einv, h1, h2⟩
    refine le_bottom_of_dom_iso (InverseImage w Ir) ?_
    refine isomorphic_trans hzero ?_
    -- 0 ≅ ⊥(U.dom).dom : invert `⊥(U.dom).dom ≅ 0` from `bottom_dom_iso … one`.
    obtain ⟨ξ, ξinv, hξ1, hξ2⟩ := hPL.bottom_dom_iso U.dom (HasTerminal.one)
    exact ⟨ξinv, ξ, hξ2, hξ1⟩
  -- (ii) `entire U.dom ≤ w# Il ∪ w# Ir ≤ w# Il ∪ ⊥`, and `w# Ir ≤ ⊥` ⟹ `entire ≤ w# Il`.
  have hwIl_entire : (InverseImage w Il).IsEntire := by
    apply entire_of_entire_le
    have ha : (Subobject.entire U.dom).le (InverseImage w (Subobject.entire _)) :=
      entire_le_inverseImage_entire w
    have hbu : (Subobject.entire (HasBinaryCoproducts.coprod A U₂.dom)).le
        (HasSubobjectUnions.union Il Ir) := inl_union_inr_entire
    have hb : (InverseImage w (Subobject.entire _)).le
        (InverseImage w (HasSubobjectUnions.union Il Ir)) := inverseImage_mono w hbu
    have hc : (InverseImage w (HasSubobjectUnions.union Il Ir)).le
        (HasSubobjectUnions.union (InverseImage w Il) (InverseImage w Ir)) :=
      (PreLogos.invImage_preserves_union w Il Ir).1
    -- `w# Il ∪ w# Ir ≤ w# Il`  (since `w# Ir ≤ ⊥ ≤ w# Il`).
    have hd : (HasSubobjectUnions.union (InverseImage w Il) (InverseImage w Ir)).le
        (InverseImage w Il) :=
      HasSubobjectUnions.union_min _ _ _ (Subobject.le_refl _)
        (Subobject.le_trans hwIr_bot (PreLogos.bottom_min _))
    exact Subobject.le_trans ha (Subobject.le_trans hb (Subobject.le_trans hc hd))
  -- (iii) `w# Il` entire ⟹ `w` factors through `il = inl_A`: extract `t : U.dom → A`.
  --   `(w#Il).arr = π₁ : (w#Il).dom → U.dom` is iso with inverse `inv`; the other pullback leg
  --   `π₂ : (w#Il).dom → A` post-composed with `inv` is the factor `t`.
  obtain ⟨inv, _, hinv2⟩ := hwIl_entire   -- hinv2 : inv ≫ (InverseImage w Il).arr = id
  let pbIl := HasPullbacks.has w Il.arr
  have harr_eq : (InverseImage w Il).arr = pbIl.cone.π₁ := rfl
  let t : U.dom ⟶ A := inv ≫ pbIl.cone.π₂
  have hinv2' : inv ≫ pbIl.cone.π₁ = Cat.id U.dom := by rw [← harr_eq]; exact hinv2
  have ht_il : t ≫ il = w := by
    have hw' : pbIl.cone.π₁ ≫ w = pbIl.cone.π₂ ≫ Il.arr := pbIl.cone.w
    calc t ≫ il = (inv ≫ pbIl.cone.π₂) ≫ Il.arr := rfl
      _ = inv ≫ (pbIl.cone.π₂ ≫ Il.arr) := Cat.assoc _ _ _
      _ = inv ≫ (pbIl.cone.π₁ ≫ w) := by rw [hw']
      _ = (inv ≫ pbIl.cone.π₁) ≫ w := (Cat.assoc _ _ _).symm
      _ = Cat.id U.dom ≫ w := by rw [hinv2']
      _ = w := Cat.id_comp w
  -- (iv) `t` is the section of `f`:  `t ≫ f ≫ inl = w ≫ k = inl`, and `inl` monic.
  refine ⟨t, ?_⟩
  apply (inl_mono (A := U.dom) (B := U₂.dom))
  show (t ≫ f) ≫ HasBinaryCoproducts.inl = Cat.id U.dom ≫ HasBinaryCoproducts.inl
  calc (t ≫ f) ≫ HasBinaryCoproducts.inl
      = t ≫ (f ≫ HasBinaryCoproducts.inl) := Cat.assoc _ _ _
    _ = t ≫ (HasBinaryCoproducts.inl ≫ k) := by rw [hk_inl]
    _ = (t ≫ il) ≫ k := (Cat.assoc _ _ _).symm
    _ = w ≫ k := by rw [ht_il]
    _ = HasBinaryCoproducts.inl := hwk
    _ = Cat.id U.dom ≫ HasBinaryCoproducts.inl := (Cat.id_comp _).symm

/-- **§1.631** packaged form: a subobject `U` that is `IsComplementedSub` (the inter-based
    complement predicate, §1.62) of a PROJECTIVE object is projective.  Unpacks the complement
    `U₂` and the two clauses and applies `complementedSub_of_projective`. -/
theorem complementedSub_of_projective' {Q : 𝒞} (U : Subobject 𝒞 Q)
    (hU : IsComplementedSub U) (hQ : Projective Q) : Projective U.dom := by
  obtain ⟨U₂, hdisj, hentire⟩ := hU
  exact complementedSub_of_projective U U₂ hdisj hentire hQ

/-! ## §1.633  Complemented subterminators of a capital positive pre-logos are projective -/

/-- `1` is projective in a CAPITAL pre-regular category: every cover `e : A ↠ 1` splits
    (`capital_one_projective`, §1.525), which is exactly `Projective (one : 𝒞)`. -/
theorem capital_one_Projective (hcap : Capital (𝒞 := 𝒞)) : Projective (one : 𝒞) := by
  intro A e he
  exact capital_one_projective hcap he

/-- **§1.633**: in a CAPITAL positive pre-logos the COMPLEMENTED SUBTERMINATORS — the
    complemented subobjects `U ⊆ 1` — are PROJECTIVE.

    PROOF (Freyd §1.633).  `1` is projective by `capital_one_projective` (§1.525); a
    complemented subobject of a projective object is projective (`§1.631`,
    `complementedSub_of_projective`).  Instantiate `Q := 1`. -/
theorem capital_complementedSub_projective (hcap : Capital (𝒞 := 𝒞))
    (U : Subobject 𝒞 (one : 𝒞)) (hU : IsComplementedSub U) : Projective U.dom :=
  complementedSub_of_projective' U hU (capital_one_Projective hcap)

end Freyd
