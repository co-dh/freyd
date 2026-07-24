/-
  §1.635 / §2.218 — COLLECTIVE CONSERVATIVITY OF THE PRODUCT STALK FAMILY.

  In a CAPITAL pre-logos the basis of complemented subterminators (§1.633,
  `capital_iff_complemented_subterminators`) detects every proper subobject, and a detected
  proper subobject is killed by some ultra-filter stalk (`stalk_detects_proper_mono_class`,
  §1.635:239).  Threading these two facts through an equalizer and through an arbitrary monic
  factorization gives the two structural properties of the stalk family `T⋆ : 𝒞 → Set^I`,
  `I = StalkIndex 𝒞`:

    * `Tstar_separates`      — the family is FAITHFUL: maps equal on every stalk are equal.
    * `Tstar_reflects_cover` — the family REFLECTS COVERS: a map surjective on every stalk is a cover.

  No single stalk does either (that needs full well-pointedness); the whole family does. -/
import Freyd.S1_635_StalkDetect
namespace Freyd
open PreLogosHorn.Stalk

variable {𝒞 : Type u} [Cat.{u} 𝒞] [DisjointBinaryCoproduct 𝒞]

/-- The stalk family SEPARATES MAPS (collective faithfulness, §1.635).  If `g, h : X ⟶ Y` induce
    the same map on every ultra-filter stalk, then `g = h`.

    PROOF (contradiction): were `g ≠ h`, their equalizer `e : E ↣ X` is a proper monic, so the basis
    of complemented subterminators (§1.633) gives a probe `x' : U.dom ⟶ X` that does NOT equalize
    `g, h` (does not factor through `e`).  `stalk_detects_proper_mono_class` produces an ultra-filter
    `F ∋ U` whose stalk class `T_F(x')` escapes the image of `T_F(e)`.  But equality of stalk maps
    `T_F(g) = T_F(h)` forces a refinement `W' ∈ F` on which `x'` DOES equalize, hence factors through
    `e`; that factorization is exactly a preimage of `T_F(x')` under `T_F(e)` — contradiction. -/
theorem Tstar_separates (hcap : Capital (𝒞 := 𝒞)) {X Y : 𝒞} (g h : X ⟶ Y)
    (heq : ∀ F : StalkIndex 𝒞, TF.map F.val g = TF.map F.val h) : g = h := by
  refine Classical.byContradiction (fun hne_gh => ?_)
  -- Pre-logos = products + pullbacks ⟹ equalizers; the equalizer `e : E ↣ X` of `g, h`.
  letI : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
  let e : eqObj g h ⟶ X := eqMap g h
  have he_eq : e ≫ g = e ≫ h := eqMap_eq g h
  have he_mono : Monic e := eqMap_monic g h
  -- `e` is a PROPER monic: were it iso, `g = h`.
  have he_notiso : ¬ IsIso e := by
    rintro ⟨einv, _, hr⟩
    refine hne_gh ?_
    calc g = Cat.id X ≫ g := (Cat.id_comp g).symm
      _ = (einv ≫ e) ≫ g := by rw [hr]
      _ = einv ≫ (e ≫ g) := Cat.assoc _ _ _
      _ = einv ≫ (e ≫ h) := by rw [he_eq]
      _ = (einv ≫ e) ≫ h := (Cat.assoc _ _ _).symm
      _ = Cat.id X ≫ h := by rw [hr]
      _ = h := Cat.id_comp h
  -- §1.633 basis: a complemented `U`, an iso `G ≅ U.dom`, and a probe `x : G ⟶ X` ∤ `e`.
  have hbasis := (capital_iff_complemented_subterminators.mp hcap).2
  obtain ⟨G, ⟨U, hUcomp, i, hi⟩, x, hx⟩ := hbasis.2 e he_mono he_notiso
  obtain ⟨iinv, hii, _⟩ := hi          -- hii : i ≫ iinv = Cat.id G
  -- Transport the probe to `x' := iinv ≫ x : U.dom ⟶ X`; it still does not factor through `e`.
  have hx' : ¬ ∃ y : U.dom ⟶ eqObj g h, y ≫ e = iinv ≫ x := by
    rintro ⟨y, hy⟩
    refine hx ⟨i ≫ y, ?_⟩
    calc (i ≫ y) ≫ e = i ≫ (y ≫ e) := Cat.assoc _ _ _
      _ = i ≫ (iinv ≫ x) := by rw [hy]
      _ = (i ≫ iinv) ≫ x := (Cat.assoc _ _ _).symm
      _ = Cat.id G ≫ x := by rw [hii]
      _ = x := Cat.id_comp _
  -- Detection: some ultra-filter `F ∋ U` whose stalk class `T_F(x')` escapes `image (T_F e)`.
  obtain ⟨F, hU, hescape⟩ := stalk_detects_proper_mono_class e he_mono U hUcomp (iinv ≫ x) hx'
  -- `T_F(g) = T_F(h)` on the class of `x'` ⟹ the two restricted names agree.
  have hkey : TF.mk F.val ⟨U, hU, (iinv ≫ x) ≫ g⟩ = TF.mk F.val ⟨U, hU, (iinv ≫ x) ≫ h⟩ := by
    have hcg := congrFun (heq F) (TF.mk F.val ⟨U, hU, iinv ≫ x⟩)
    simpa only [TF.map_mk] using hcg
  -- A common refinement `W' ∈ F`: `a, b : W' ⟶ U.dom` over `W'.arr`, agreeing after `≫ g | ≫ h`.
  have hpre : IsPreFilter F.val := F.2.1.1
  obtain ⟨W', hW', a, b, ha, hb, hab⟩ := PrefRel_of_TF_eq F.val hpre hkey
  have hab' : a = b := U.monic a b (by rw [ha, hb])
  -- Hence `a ≫ x'` EQUALIZES `g, h`, so it factors through the equalizer `e` via `d`.
  have heqlz : (a ≫ (iinv ≫ x)) ≫ g = (a ≫ (iinv ≫ x)) ≫ h := by
    calc (a ≫ (iinv ≫ x)) ≫ g = a ≫ ((iinv ≫ x) ≫ g) := Cat.assoc _ _ _
      _ = b ≫ ((iinv ≫ x) ≫ h) := hab
      _ = a ≫ ((iinv ≫ x) ≫ h) := by rw [hab']
      _ = (a ≫ (iinv ≫ x)) ≫ h := (Cat.assoc _ _ _).symm
  have hd : eqLift g h (a ≫ (iinv ≫ x)) heqlz ≫ e = a ≫ (iinv ≫ x) := eqLift_fac g h _ heqlz
  -- That factorization names a preimage of `T_F(x')` under `T_F(e)` — contradicting `hescape`.
  refine hescape ⟨TF.mk F.val ⟨W', hW', eqLift g h (a ≫ (iinv ≫ x)) heqlz⟩, ?_⟩
  rw [TF.map_mk, hd]
  exact Quot.sound ⟨W', hW', Cat.id W'.dom, a, Cat.id_comp _, ha, Cat.id_comp _⟩

/-- The stalk family REFLECTS COVERS (§1.635).  If `f : X ⟶ Y` is surjective on every ultra-filter
    stalk, then `f` is a cover.

    PROOF (per monic factorization): a cover is any map every monic factor of which is iso
    (§1.512).  Take a monic `m : C ↣ Y` with `f = g' ≫ m`; suppose `m` is not iso.  The §1.633 basis
    gives a probe `x' : U.dom ⟶ Y` not factoring through `m`, and `stalk_detects_proper_mono` makes
    `T_F(m)` non-surjective for some `F`.  But `T_F(f) = T_F(m) ∘ T_F(g')` is surjective (hypothesis),
    forcing the last factor `T_F(m)` surjective — contradiction.  So `m` is iso, i.e. `f` is a cover. -/
theorem Tstar_reflects_cover (hcap : Capital (𝒞 := 𝒞)) {X Y : 𝒞} (f : X ⟶ Y)
    (hsurj : ∀ F : StalkIndex 𝒞, Function.Surjective (TF.map F.val f)) : Cover f := by
  intro C m g' hm hgm                  -- monic `m : C ⟶ Y`, `g' : X ⟶ C`, `g' ≫ m = f`
  refine Classical.byContradiction (fun hmiso => ?_)
  -- §1.633 basis: a complemented `U`, an iso `G ≅ U.dom`, and a probe `x : G ⟶ Y` ∤ `m`.
  have hbasis := (capital_iff_complemented_subterminators.mp hcap).2
  obtain ⟨G, ⟨U, hUcomp, i, hi⟩, x, hx⟩ := hbasis.2 m hm hmiso
  obtain ⟨iinv, hii, _⟩ := hi          -- hii : i ≫ iinv = Cat.id G
  have hx' : ¬ ∃ y : U.dom ⟶ C, y ≫ m = iinv ≫ x := by
    rintro ⟨y, hy⟩
    refine hx ⟨i ≫ y, ?_⟩
    calc (i ≫ y) ≫ m = i ≫ (y ≫ m) := Cat.assoc _ _ _
      _ = i ≫ (iinv ≫ x) := by rw [hy]
      _ = (i ≫ iinv) ≫ x := (Cat.assoc _ _ _).symm
      _ = Cat.id G ≫ x := by rw [hii]
      _ = x := Cat.id_comp _
  obtain ⟨F, hFns⟩ := stalk_detects_proper_mono m hm U hUcomp (iinv ≫ x) hx'
  -- `T_F(f) = T_F(m) ∘ T_F(g')` surjective ⟹ `T_F(m)` surjective, against detection.
  refine hFns (fun t => ?_)
  obtain ⟨w, hw⟩ := hsurj F t
  exact ⟨TF.map F.val g' w, by rw [← TF.map_comp, hgm]; exact hw⟩

end Freyd
