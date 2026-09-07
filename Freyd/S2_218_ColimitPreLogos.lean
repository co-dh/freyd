module

public import Freyd.S1_543_CatColimitRegular
public import Freyd.S1_61
public import Freyd.S1_543_UnionFromCoproduct
public import Freyd.S1_421_Initial
public import Freyd.S1_63_ColimitInvImageUnion

/-!
  # The directed colimit of pre-logoi is a pre-logos

  The directed colimit `colimitCat C hC` of a `CatSystem` whose stages are each a `PreLogos`
  (§1.6) is again a `PreLogos`, once it is known to be a `RegularCategory` with binary coproducts
  (supplied by the §2.218 regular tower: `colimitPreRegular` + `colimitHasImages` +
  `colimitHasBinaryCoproducts`).

  The genuinely new content is the BOTTOM (empty-join) story.  Every stage `PreLogos` has a
  STRICT INITIAL object `0_i` (§1.61: the minimal subobject of `1`, every map into it iso).  We
  prove the single new brick

      `colimitStrictInitial : StrictCoterminator (objIncl i₀ 0_{i₀})`   (in `colimitCat`)

  — the `objIncl`-image of any one stage's strict initial is a strict initial of the colimit.  From
  it the four bottom-related `PreLogos` fields all follow cleanly with a SINGLE global bottom object
  `Z₀ := objIncl i₀ 0_{i₀}` whose domain is the same for every `A`:

    * `bottom A`            — `Z₀ ↣ A` (map out of the strict initial, monic);
    * `bottom_min`          — `Z₀ ⟶ S.dom` factors `Z₀ ⟶ A` (initial uniqueness);
    * `bottom_dom_iso`      — both bottom domains are `Z₀` (reflexivity);
    * `invImage_preserves_bottom` — the pullback of `Z₀ ↣ B` along `f` projects to `Z₀`, hence
      (strictness) is iso to `Z₀`.

  The remaining field `invImage_preserves_union` (Freyd's coherent-stability law) is discharged by
  `colimit_invImage_union_le` (`Freyd/ColimitInvImageUnion.lean`): the colimit union / inverse image
  agree with the germs of the per-stage operations (`objIncl_preserves_images` +
  `objIncl_preserves_pullbacks` + `objIncl_preserves_coproducts`), so the per-stage hard direction
  transports up.  The per-stage finite-limit / image / coproduct bundles are exactly those the
  §2.218 regular tower already supplies.
-/

open Freyd

namespace Freyd.Colim

universe u v

variable {ι : Type u} {D : Directed ι}

/-- Transfer `IsIso` across a heterogeneous equality of morphisms whose domains and codomains
    are (propositionally) equal objects.  Used to lift `IsIso (homInclObj …)` to `IsIso g` along
    the `colimHom_as_homInclObj` alignment. -/
public theorem isIso_of_heq {𝒞 : Type u} [Cat.{v} 𝒞] {P Q X Y : 𝒞} {m : P ⟶ Q} {g : X ⟶ Y}
    (hP : P = X) (hQ : Q = Y) (h : HEq m g) (hm : IsIso m) : IsIso g := by
  subst hP; subst hQ; rw [eq_of_heq h] at hm; exact hm

/-- Casting the codomain object of a stage germ does not change its stage inclusion (up to `HEq`):
    `homInclObj (castHom rfl e g)` is `HEq` to `homInclObj g`. -/
theorem homInclObj_castHom_cod_heq (C : CatSystem ι D) (hC : C.Coherent) {i : ι}
    {x y y' : C.A i} (g : x ⟶ y) (e : y = y') :
    HEq (homInclObj C hC (castHom rfl e g)) (homInclObj C hC g) := by
  subst e; rfl

/-- The chosen strict initial object of stage `i` (the minimal subobject of `1`, §1.61). -/
@[expose] public noncomputable def stageZero (C : CatSystem ι D) (hbot : ∀ i, PreLogos (C.A i)) (i : ι) : C.A i :=
  (minimal_subobject_of_one_is_coterminator (hbot i)).zero

/-- **The new colimit-zero brick.**  The `objIncl`-image of one stage's strict initial `0_{i₀}` is
    a STRICT COTERMINATOR (strict initial) of `colimitCat`: every colimit map into it is an iso.

    The transition hypothesis is the UP-TO-ISO form `hinitpres`: every transition `C.F hij` sends the
    chosen stage strict-initial `0_i` to a STRICT COTERMINATOR of stage `j` (NOT the on-the-nose object
    equality `C.F hij 0_i = 0_j`).  This is the form satisfied by the §2.218 tower's stage-embedding
    transitions: the embedding preserves the strict initial only up to iso, never as a chosen-object
    equality.  (`strictCoterminator_of_eq` below bridges the `Eq` form to this one.)

    PROOF.  A map `g : X ⟶ objIncl i₀ 0_{i₀}` is, up to `HEq`, the stage inclusion `homInclObj fN`
    of a germ `fN : xX ⟶ xZ` at some stage `N` with `objIncl N xZ = objIncl i₀ 0_{i₀}`.  At a common
    stage `M'`, `F_{N→M'} xZ = F_{i₀→M'} 0_{i₀}` (`objIncl_eq_commonStage`), which is a STRICT
    COTERMINATOR (`hinitpres`); so the pushed germ `fN'` — a map INTO it — is iso directly.
    `homInclObj_isIso_of_stage` lifts this to the colimit and the `HEq` chain transports `IsIso` to `g`. -/
public theorem colimitStrictInitial (C : CatSystem ι D) (hC : C.Coherent) [Nonempty ι]
    (hbot : ∀ i, PreLogos (C.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j),
      @StrictCoterminator (C.A j) (C.catA j) (C.F hij (stageZero C hbot i)))
    (i₀ : ι) :
    letI : Cat C.Obj := colimitCat C hC
    StrictCoterminator (C.objIncl i₀ (stageZero C hbot i₀)) := by
  letI : Cat C.Obj := colimitCat C hC
  intro X g
  -- align `g` to a stage inclusion `homInclObj fN`
  obtain ⟨N, xX, xZ, fN, eX, eZ, hHEq⟩ :=
    colimHom_as_homInclObj C hC (A := X) (Z := C.objIncl i₀ (stageZero C hbot i₀)) g
  -- a common stage `M ≥ N, i₀` where `xZ` and `0_{i₀}` are objIncl-equal
  obtain ⟨M, hNM, hi₀M⟩ := D.bound N i₀
  have hAgreeM : C.objIncl M (C.F hNM xZ) = C.objIncl M (C.F hi₀M (stageZero C hbot i₀)) := by
    rw [C.objIncl_compat hNM xZ, eZ, C.objIncl_compat hi₀M (stageZero C hbot i₀)]
  obtain ⟨M', hMM', hZeqM'⟩ :=
    objIncl_eq_commonStage C (C.F hNM xZ) (C.F hi₀M (stageZero C hbot i₀)) hAgreeM
  let hNM' : D.le N M' := D.trans hNM hMM'
  let hi₀M' : D.le i₀ M' := D.trans hi₀M hMM'
  -- `F_{N→M'} xZ = F_{i₀→M'} 0_{i₀}`, hence a STRICT COTERMINATOR (`hinitpres`)
  have e : C.F hNM' xZ = C.F hi₀M' (stageZero C hbot i₀) := by
    calc C.F hNM' xZ = C.F hMM' (C.F hNM xZ) := by rw [C.F_trans hNM hMM']
      _ = C.F hMM' (C.F hi₀M (stageZero C hbot i₀)) := hZeqM'
      _ = C.F hi₀M' (stageZero C hbot i₀) := by rw [← C.F_trans hi₀M hMM']
  have hSC : @StrictCoterminator (C.A M') (C.catA M') (C.F hNM' xZ) := by
    rw [e]; exact hinitpres hi₀M'
  -- the pushed germ `fN'` is a map INTO a strict coterminator, hence iso
  let fN' : C.F hNM' xX ⟶ C.F hNM' xZ := (C.functF hNM').map fN
  obtain ⟨inv, hfi1, hfi2⟩ := hSC fN'
  have hiso_fN' : @IsIso C.Obj (colimitCat C hC) _ _ (homInclObj C hC fN') :=
    homInclObj_isIso_of_stage C hC fN' inv hfi1 hfi2
  -- HEq chain: homInclObj fN' ≅ homInclObj fN ≅ g
  have H2 : HEq (homInclObj C hC fN') (homInclObj C hC fN) :=
    homInclObj_push_heq C hC hNM' fN
  have Hchain : HEq (homInclObj C hC fN') g := H2.trans hHEq
  have hP : C.objIncl M' (C.F hNM' xX) = X := (C.objIncl_compat hNM' xX).trans eX
  have hQ : C.objIncl M' (C.F hNM' xZ) = C.objIncl i₀ (stageZero C hbot i₀) := by
    rw [C.objIncl_compat hNM' xZ, eZ]
  exact isIso_of_heq hP hQ Hchain hiso_fN'

/-- The on-the-nose equality form of `colimitStrictInitial`'s hypothesis implies the up-to-iso
    `StrictCoterminator` form: if `C.F hij 0_i = 0_j` then `C.F hij 0_i` is the chosen stage
    strict-initial `0_j`, a strict coterminator (`any_map_to_zero_is_iso`).  Lets callers with an
    on-the-nose equality use `colimitStrictInitial`/`colimitPreLogos` unchanged. -/
theorem strictCoterminator_of_eq (C : CatSystem ι D) (hbot : ∀ i, PreLogos (C.A i))
    {i j : ι} (hij : D.le i j) (e : C.F hij (stageZero C hbot i) = stageZero C hbot j) :
    @StrictCoterminator (C.A j) (C.catA j) (C.F hij (stageZero C hbot i)) := by
  rw [e]; intro X f; exact any_map_to_zero_is_iso (hbot j) f

/-- A map out of a strict initial object is monic.  Given `u v : W ⟶ Z` with `u ≫ m = v ≫ m`:
    `u` is iso (strictness, inverse `ui`), and `ui ≫ v = ui ≫ u` (both maps OUT of the initial
    `Z`), whence `v = u ≫ (ui ≫ v) = u ≫ (ui ≫ u) = u`. -/
public theorem mono_of_strict_initial {𝒞 : Type u} [Cat.{v} 𝒞] {Z A : 𝒞}
    (hInit : IsInitial Z) (hStrict : StrictCoterminator Z) (m : Z ⟶ A) : Monic m := by
  intro W u v huv
  obtain ⟨ui, hu1, hu2⟩ := hStrict u
  have key : ui ≫ v = ui ≫ u := hInit.hom_uniq (ui ≫ v) (ui ≫ u)
  refine Eq.symm ?_
  calc v = (u ≫ ui) ≫ v := by rw [hu1, Cat.id_comp]
    _ = u ≫ (ui ≫ v) := Cat.assoc _ _ _
    _ = u ≫ (ui ≫ u) := by rw [key]
    _ = u ≫ Cat.id Z := by rw [hu2]
    _ = u := Cat.comp_id _

/-- **The directed colimit of pre-logoi is a pre-logos.**

  Given the per-stage `PreLogos` data (`hbot`) and that transitions preserve the chosen stage
  initial on the nose (`hinitpres`), plus the colimit's already-established `RegularCategory`
  (`hReg`, from the §2.218 tower) and subobject unions (`hUn`, e.g.
  `hasSubobjectUnions_of_coproducts_images` from `colimitHasBinaryCoproducts` + the colimit images),
  the colimit is a `PreLogos`.

  The four bottom fields rest on the single new brick `colimitStrictInitial`; the substantive
  coherent-stability law `invImage_preserves_union` is discharged by germ-transport
  (`colimit_invImage_union_le`, §1.63 union condition) from the per-stage finite-limit / image /
  coproduct bundles (the same ones the §2.218 regular tower already supplies). -/
@[expose] public noncomputable def colimitPreLogos (C : CatSystem.{u, u} ι D) (hC : C.Coherent) [Nonempty ι]
    (hbot : ∀ i, PreLogos (C.A i))
    (hinitpres : ∀ {i j : ι} (hij : D.le i j),
      @StrictCoterminator (C.A j) (C.catA j) (C.F hij (stageZero C hbot i)))
    (hmono : TransMono C)
    (ht : ∀ i, HasTerminal (C.A i))
    (htpres : ∀ {i j} (hij : D.le i j), C.F hij (ht i).one = (ht j).one)
    (hp : ∀ i, HasBinaryProducts (C.A i))
    (hpres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : z ⟶ C.F hij ((hp i).prod a b)),
        u ≫ (C.functF hij).map (hp i).fst = v ≫ (C.functF hij).map (hp i).fst →
        u ≫ (C.functF hij).map (hp i).snd = v ≫ (C.functF hij).map (hp i).snd → u = v)
    (hpres_pair : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : z ⟶ C.F hij a) (q : z ⟶ C.F hij b),
        ∃ r : z ⟶ C.F hij ((hp i).prod a b),
          r ≫ (C.functF hij).map (hp i).fst = p ∧ r ≫ (C.functF hij).map (hp i).snd = q)
    (he : ∀ i, HasEqualizers (C.A i))
    (hepres : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (u v : z ⟶ C.F hij (eqObj f g)),
        u ≫ (C.functF hij).map (eqMap f g) = v ≫ (C.functF hij).map (eqMap f g) → u = v)
    (hepres_lift : ∀ {i j} (hij : D.le i j) {A B : C.A i} (f g : A ⟶ B) (z : C.A j)
        (k : z ⟶ C.F hij A)
        (_hk : k ≫ (C.functF hij).map f = k ≫ (C.functF hij).map g),
        ∃ r : z ⟶ C.F hij (eqObj f g), r ≫ (C.functF hij).map (eqMap f g) = k)
    (hcop : ∀ i, HasBinaryCoproducts (C.A i))
    (hcoppres : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (u v : C.F hij ((hcop i).coprod a b) ⟶ z),
        (C.functF hij).map (hcop i).inl ≫ u = (C.functF hij).map (hcop i).inl ≫ v →
        (C.functF hij).map (hcop i).inr ≫ u = (C.functF hij).map (hcop i).inr ≫ v → u = v)
    (hcoppres_case : ∀ {i j} (hij : D.le i j) (a b : C.A i) (z : C.A j)
        (p : C.F hij a ⟶ z) (q : C.F hij b ⟶ z),
        ∃ r : C.F hij ((hcop i).coprod a b) ⟶ z,
          (C.functF hij).map (hcop i).inl ≫ r = p ∧ (C.functF hij).map (hcop i).inr ≫ r = q)
    (hi : ∀ i, HasImages (C.A i))
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : C.A i} (p q : x ⟶ y),
        (C.functF hij).map p = (C.functF hij).map q → p = q)
    (himgpres : ∀ {i j : ι} (hij : D.le i j) {A B : C.A i} (f : A ⟶ B),
        IsImage ((C.functF hij).map f)
          (@Subobject.map _ _ (C.catA i) (C.catA j) (C.functF hij) (hmono hij) _
            (@image _ (C.catA i) (hi i) _ _ f)))
    [hReg : @RegularCategory C.Obj (colimitCat C hC)]
    [hUn : @HasSubobjectUnions C.Obj (colimitCat C hC) hReg.toHasImages] :
    @PreLogos C.Obj (colimitCat C hC) := by
  letI : Cat C.Obj := colimitCat C hC
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let Z₀ : C.Obj := C.objIncl i₀ (stageZero C hbot i₀)
  have hSI : StrictCoterminator Z₀ := colimitStrictInitial C hC hbot hinitpres i₀
  have hInit : IsInitial Z₀ := hSI.isInitial
  exact
    { toRegularCategory := hReg
      toHasSubobjectUnions := hUn
      bottom := fun A => ⟨Z₀, hInit.out A, mono_of_strict_initial hInit hSI (hInit.out A)⟩
      bottom_min := fun {A} S => ⟨hInit.out S.dom, hInit.hom_uniq _ _⟩
      bottom_dom_iso := fun A B => isomorphic_refl Z₀
      invImage_preserves_union := fun {A B} f S T =>
        ⟨colimit_invImage_union_le C hC hmono ht htpres hp hpres hpres_pair he hepres hepres_lift
           hcop hcoppres hcoppres_case hi hfaith himgpres hbot f S T,
         HasSubobjectUnions.union_min _ _ _
           (inverseImage_mono f (HasSubobjectUnions.union_left S T))
           (inverseImage_mono f (HasSubobjectUnions.union_right S T))⟩
      invImage_preserves_bottom := fun {A B} f =>
        ⟨(HasPullbacks.has f (hInit.out B)).cone.π₂, hSI _⟩ }

end Freyd.Colim
