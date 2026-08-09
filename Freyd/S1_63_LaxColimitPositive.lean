/-
  §1.63 / §1.621 (lax) — the FILTERED lax colimit of positive pre-logoi is a positive pre-logos.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the Layer-3 ASSEMBLY of lax colimit positivity: the lax ports of the two strict entry
  points `Colim.colimitPreLogos` (`Freyd/ColimitPreLogos.lean`) and `Colim.colimitPositive`
  (`Freyd/ColimitPositive.lean`), wiring the already-committed lax Layer-2 lemmas.

  * `laxColimPreLogos` — the lax colimit `laxColimCat L hL` is a `PreLogos` (§1.6) given per-stage
    `PreLogos` data + the lax coherence bundles + the colimit's `RegularCategory` (§2.218 tower) and
    subobject unions.  The four BOTTOM (empty-join) fields rest on the single brick
    `laxColimStrictInitial` (`Freyd/LaxStrictInitial.lean`) exactly as the strict file uses
    `Colim.colimitStrictInitial`; the substantive §1.63 union-condition field
    `invImage_preserves_union` is discharged by `laxColim_invImage_union_le`
    (`Freyd/LaxInvImageUnion.lean`) for the hard direction and by monotonicity of the inverse image
    (`inverseImage_mono`, only `HasPullbacks`) + `union_min` for the reverse.

  * `laxColimPositive` — the lax colimit of `DisjointBinaryCoproduct` stages is itself a
    `DisjointBinaryCoproduct` (§1.621).  The three disjointness facts come from the committed
    `laxColim_inl_monic` / `laxColim_inr_monic` / `laxColim_inl_inter_inr` (`Freyd/LaxDisjoint.lean`),
    `laxColimPreLogos` is wired as the `[hPL]`, the binary coproduct is
    `laxColimCoprodOfDisjoint`, and the GENERIC §1.621 union field `inl ∪ inr = ⊤` is supplied by
    `disjointBinaryCoproduct_of_disjoint` (`Freyd/ColimitPositive.lean`).  Mirrors
    `Colim.colimitDisjointBinaryCoproduct` + `Colim.colimitPositive`.

  All instance args on the colimit are kept OPAQUE (`[hReg]`/`[hUn]`, threaded into the Layer-2
  lemmas' opaque `[hpullI]`/`[hImgI]`/`[hUnI]`) to avoid the §1.43 whnf blowup the lax union lemma is
  sensitive to.  Mathlib-free.  Single universe `{w, w}` (forced by the equalizer-derived pullback
  germ of `laxColim_invImage_union_le` and the lax disjointness).
-/
module

public import Freyd.S1_63_LaxInvImageUnion
public import Freyd.S1_61_LaxStrictInitial
public import Freyd.S1_621_LaxDisjoint
public import Freyd.S2_218_ColimitPreLogos
public import Freyd.S1_621_ColimitPositive

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe w

variable {ι : Type w} {D : Directed ι}

/-- **The directed lax colimit of pre-logoi is a pre-logos.**

  Lax port of `Colim.colimitPreLogos`.  Given the per-stage `PreLogos` data (`hbot`) and that
  transitions preserve the chosen stage initial on the nose (`hinitpres`), the lax coherence bundles
  (`hmono`, `tData`/`pData`/`eqData`/`coprData`, `hi`/`hfaith`/`himgpres` — the SAME bundles the lax
  §1.63 union lemma `laxColim_invImage_union_le` consumes), and the lax colimit's already-established
  `RegularCategory` (`hReg`, §2.218 tower) and subobject unions (`hUn`), the lax colimit
  `laxColimCat L hL` is a `PreLogos`.

  The four bottom fields rest on the single brick `laxColimStrictInitial`; the substantive
  coherent-stability law `invImage_preserves_union` is `laxColim_invImage_union_le` for the hard
  direction and `inverseImage_mono` + `union_min` for the reverse (monotonicity of inverse image). -/
@[expose] public noncomputable def laxColimPreLogos (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L) [Nonempty ι]
    (hbot : ∀ i, PreLogos (L.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j),
      @StrictCoterminator (L.A j) (L.catA j) (L.F hij (stageZero L hbot i)))
    (hmono : TransMonoL L)
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L)
    (coprData : LaxCoproductData L)
    (hi : ∀ i, @HasImages (L.A i) (L.catA i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p = (L.functF hij).map q → p = q)
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {X Y : L.A i} (f : X ⟶ Y),
        @IsImage (L.A j) (L.catA j) _ _ ((L.functF hij).map f)
          (@Subobject.map _ _ (L.catA i) (L.catA j) (L.functF hij) (hmono hij) _
            (@image _ (L.catA i) (hi i) _ _ f)))
    [hReg : @RegularCategory (Obj L) (laxColimCat L hL)]
    [hUn : @HasSubobjectUnions (Obj L) (laxColimCat L hL) hReg.toHasImages] :
    @PreLogos (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let Z₀ : Obj L := objIncl L i₀ (stageZero L hbot i₀)
  have hSI : StrictCoterminator Z₀ := laxColimStrictInitial L hL hbot hinitpres i₀
  have hInit : IsInitial Z₀ := hSI.isInitial
  exact
    { toRegularCategory := hReg
      toHasSubobjectUnions := hUn
      bottom := fun A => ⟨Z₀, hInit.out A, mono_of_strict_initial hInit hSI (hInit.out A)⟩
      bottom_min := fun {A} S => ⟨hInit.out S.dom, hInit.hom_uniq _ _⟩
      bottom_dom_iso := fun A B => isomorphic_refl Z₀
      invImage_preserves_union := fun {A B} f S T =>
        ⟨laxColim_invImage_union_le L hL tData pData eqData coprData hi hfaith hmono himgpres hbot
           f S T,
         HasSubobjectUnions.union_min _ _ _
           (inverseImage_mono f (HasSubobjectUnions.union_left S T))
           (inverseImage_mono f (HasSubobjectUnions.union_right S T))⟩
      invImage_preserves_bottom := fun {A B} f =>
        ⟨(HasPullbacks.has f (hInit.out B)).cone.π₂, hSI _⟩ }

/-- **The directed lax colimit of positive pre-logoi is a positive pre-logos** (Freyd §1.63 "union
    condition" + §1.621 disjointness, strict level, lax colimit).  Single entry point bundling
    `laxColimPreLogos` (the `PreLogos` layer) as the `[hPL]` of the §1.621 disjointness lemmas, the
    colimit binary coproduct `laxColimCoprodOfDisjoint`, the internal disjointness facts
    `laxColim_inl/inr_monic` + `laxColim_inl_inter_inr`, and the generic union field
    `disjointBinaryCoproduct_of_disjoint`.  Mirrors `Colim.colimitDisjointBinaryCoproduct` +
    `Colim.colimitPositive`.  All hypotheses are the per-stage / lax coherence bundles the §2.218
    capitalization tower already supplies; the colimit's `RegularCategory`/`HasSubobjectUnions` come
    from the §2.218 tower. -/
@[expose] public noncomputable def laxColimPositive (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L) [Nonempty ι]
    (hdisj : ∀ i, DisjointBinaryCoproduct (L.A i)) (hmono : TransMonoL L)
    (hbot : ∀ i, PreLogos (L.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j),
      @StrictCoterminator (L.A j) (L.catA j) (L.F hij (stageZero L hbot i)))
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L)
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (u v : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z),
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ v →
        (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ u
            = (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
        (p : L.F hij a ⟶ z) (q : L.F hij b ⟶ z),
        ∃ r : L.F hij ((hdisj i).toHasBinaryCoproducts.coprod a b) ⟶ z,
          (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inl ≫ r = p
          ∧ (L.functF hij).map (hdisj i).toHasBinaryCoproducts.inr ≫ r = q)
    (hi : ∀ i, @HasImages (L.A i) (L.catA i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p = (L.functF hij).map q → p = q)
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {X Y : L.A i} (f : X ⟶ Y),
        @IsImage (L.A j) (L.catA j) _ _ ((L.functF hij).map f)
          (@Subobject.map _ _ (L.catA i) (L.catA j) (L.functF hij) (hmono hij) _
            (@image _ (L.catA i) (hi i) _ _ f)))
    [hReg : @RegularCategory (Obj L) (laxColimCat L hL)]
    [hUn : @HasSubobjectUnions (Obj L) (laxColimCat L hL) hReg.toHasImages] :
    @DisjointBinaryCoproduct (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI iCop : HasBinaryCoproducts (Obj L) := laxColimCoprodOfDisjoint L hL hdisj hcoppres hcoppres_case
  -- the `PreLogos` layer (regular + subobject unions + bottom), via `laxColimPreLogos`.
  letI hPL : @PreLogos (Obj L) (laxColimCat L hL) :=
    laxColimPreLogos L hL hbot hinitpres hmono tData pData eqData
      (laxCoprodDataOfDisjoint L hdisj hcoppres hcoppres_case) hi hfaith himgpres
  -- the three §1.621 disjointness facts, discharged internally from the per-stage `hdisj`.
  have hl : ∀ {A B : Obj L}, Monic (HasBinaryCoproducts.inl (A := A) (B := B)) :=
    laxColim_inl_monic L hL hdisj hmono hcoppres hcoppres_case
  have hr : ∀ {A B : Obj L}, Monic (HasBinaryCoproducts.inr (A := A) (B := B)) :=
    laxColim_inr_monic L hL hdisj hmono hcoppres hcoppres_case
  have hinter : ∀ {A B : Obj L},
      Subobject.le (Subobject.inter (inlSub (𝒞 := Obj L) (A := A) (B := B) hl)
                                    (inrSub (𝒞 := Obj L) (A := A) (B := B) hr))
                   (PreLogos.bottom (HasBinaryCoproducts.coprod A B)) :=
    laxColim_inl_inter_inr L hL hdisj hmono hbot hinitpres tData pData eqData
      hcoppres hcoppres_case hl hr
  exact disjointBinaryCoproduct_of_disjoint (𝒞 := Obj L) hl hr hinter

end Freyd.LaxColim
