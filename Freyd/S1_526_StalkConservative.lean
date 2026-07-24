/-
  Freyd & Scedrov, *Categories and Allegories* — §1.526 / §1.635 / §2.218.

  **The ultra-filter stalk reflects isos in a fully WELL-POINTED (capital) pre-logos.**

  This file discharges the last residual of the §2.218 *stalk route* (`relStalk_faithful`,
  `Freyd/S2_218.lean`): the hypothesis `hrefl` that the stalk `T_F̂` REFLECTS ISOS.

  The engine is Freyd's §1.526 *"the points functor is a representation in a capital category"*:
  in a category whose every object is WELL-POINTED, the global-points functor `Γ = Hom(1,-)`
  REFLECTS ISOS — `f` is iso iff it is bijective on points `1 → -`.  The bridge to the stalk is
  that, when the pre-filter `ℱ` contains the TOP subterminator `1` (automatic for a *filter*, in
  particular an ultra-filter, since `1` is complemented and every member is `≤ 1`), the canonical
  inclusion `Hom(1,A) ↪ T_F̂(A)` of the `U = 1` colimit stage is injective and natural, and it
  RETRACTS onto the global points: so `T_F̂(f)` iso forces `Γ(f)` bijective, hence `f` iso.

  NOTE ON THE WALL.  A single stalk reflects isos ONLY because the WHOLE category is well-pointed
  (the `1`-stage already sees every map apart).  In a merely `Capital` category (well-supported ⟹
  well-pointed) NOT every object is well-pointed, and a single stalk does not reflect isos — that is
  Freyd's *collectively faithful* family (§1.635, book p.123 line 247).  Full well-pointedness is
  exactly what the §1.543 capitalization tower delivers, and is the honest hypothesis here.

  STRICTLY MATHLIB-FREE; depends only on `Freyd.*`.
-/

import Freyd.S1_625_StalkRegular
import Freyd.S2_21

universe u

namespace Freyd.PreLogosHorn.Stalk

open Cat SetRegular RelFunctor

variable {𝒞 : Type u} [Cat.{u} 𝒞] [PreLogos 𝒞]

/-! ## §1.526 — the global-points functor `Γ = Hom(1,-)` reflects isos when every object is
    well-pointed.

  In a `PreLogos` (hence Cartesian: products + pullbacks ⟹ equalizers) we prove the three classical
  facts about `Γ`, each under the relevant well-pointedness, then combine them with `1`-stage of the
  stalk colimit. -/

/-- A `PreLogos` has EQUALIZERS (products + pullbacks ⟹ equalizers).  We install ONLY
    `HasEqualizers` (not a full `CartesianCategory`, which would re-export `HasBinaryProducts` and
    create an instance diamond with the genuine `PreLogos` one). -/
local instance preLogosEqualizers : HasEqualizers 𝒞 :=
  products_pullbacks_implies_equalizers

/-- **§1.526 (faithfulness).**  Maps out of a WELL-POINTED object are determined by their action on
    points: if `a, b : Z → W` agree after every point `x : 1 → Z` (`x ≫ a = x ≫ b`), and `Z` is
    well-pointed, then `a = b`.  PROOF: the equalizer `E ↣ Z` of `a, b` is monic; if it were not
    iso, well-pointedness of `Z` gives a point of `Z` missing `E`, i.e. a point on which `a, b`
    differ — contradiction.  So `E` is iso, forcing `a = b`. -/
theorem points_faithful_of_wellPointed {Z W : 𝒞} (hZ : WellPointed Z)
    {a b : Z ⟶ W} (h : ∀ x : one ⟶ Z, x ≫ a = x ≫ b) : a = b := by
  -- Equalizer `E ↣ Z` of `a, b`.
  have hEm : Monic (eqMap a b) := eqMap_monic a b
  by_cases hiso : IsIso (eqMap a b)
  · -- `E ≅ Z`, so `a = b` via the iso section.
    obtain ⟨e, he₁, he₂⟩ := hiso
    have : e ≫ (eqMap a b ≫ a) = e ≫ (eqMap a b ≫ b) := by rw [eqMap_eq]
    calc a = (e ≫ eqMap a b) ≫ a := by rw [he₂, Cat.id_comp]
      _ = e ≫ (eqMap a b ≫ a) := Cat.assoc _ _ _
      _ = e ≫ (eqMap a b ≫ b) := this
      _ = (e ≫ eqMap a b) ≫ b := (Cat.assoc _ _ _).symm
      _ = b := by rw [he₂, Cat.id_comp]
  · -- Proper monic `E ↣ Z`: well-pointedness gives a point of `Z` not through `E`, contradicting `h`.
    exfalso
    obtain ⟨x, hx⟩ := hZ (eqMap a b) hEm hiso
    apply hx
    -- `x ≫ a = x ≫ b` lifts `x` through the equalizer.
    exact ⟨eqLift a b x (h x), eqLift_fac a b x (h x)⟩

/-- **§1.526 (covers from points).**  If every point `y : 1 → Y` lifts along `f : X → Y`
    (`Γ(f)` surjective) and `Y` is well-pointed, then `f` is a COVER.  PROOF: any monic `m : C ↣ Y`
    that `f` factors through (`g ≫ m = f`) is hit by every point of `Y` (lift the point through `f`,
    then it factors through `m`), so `m` misses no point; well-pointedness forces `m` iso. -/
theorem cover_of_points_surjective {X Y : 𝒞} (f : X ⟶ Y) (hY : WellPointed Y)
    (hsurj : ∀ y : one ⟶ Y, ∃ x : one ⟶ X, x ≫ f = y) : Cover f := by
  intro C m g hm hgm
  refine Classical.byContradiction (fun hmiso => ?_)
  obtain ⟨y, hy⟩ := hY m hm hmiso
  obtain ⟨x, hx⟩ := hsurj y
  exact hy ⟨x ≫ g, by rw [Cat.assoc, hgm, hx]⟩

/-- **§1.526 (monos from points).**  If `Γ(f)` is injective on points (`x ≫ f = x' ≫ f → x = x'`
    for all `x, x' : 1 → X`) and the KERNEL PAIR of `f` is well-pointed, then `f` is MONIC.
    PROOF: the two kernel-pair projections `k₁, k₂ : K → X` satisfy `k₁ ≫ f = k₂ ≫ f`, so on every
    point `p : 1 → K` we get `(p≫k₁) ≫ f = (p≫k₂) ≫ f`, whence `p ≫ k₁ = p ≫ k₂` by injectivity;
    well-pointedness of `K` (`points_faithful`) makes `k₁ = k₂`, so the kernel-pair diagonal is iso
    and `f` is monic (§1.453). -/
theorem monic_of_points_injective {X Y : 𝒞} (f : X ⟶ Y)
    (hK : WellPointed (kernelPair f))
    (hinj : ∀ x x' : one ⟶ X, x ≫ f = x' ≫ f → x = x') : Monic f := by
  -- `k₁ ≫ f = k₂ ≫ f` (kernel-pair square).
  have hsq : kp₁ (f := f) ≫ f = kp₂ (f := f) ≫ f := kp_sq
  -- `k₁ = k₂` by point-faithfulness of `K`.
  have hk : kp₁ (f := f) = kp₂ (f := f) := by
    refine points_faithful_of_wellPointed hK (fun p => ?_)
    refine hinj (p ≫ kp₁ (f := f)) (p ≫ kp₂ (f := f)) ?_
    calc (p ≫ kp₁ (f := f)) ≫ f = p ≫ (kp₁ (f := f) ≫ f) := Cat.assoc _ _ _
      _ = p ≫ (kp₂ (f := f) ≫ f) := by rw [hsq]
      _ = (p ≫ kp₂ (f := f)) ≫ f := (Cat.assoc _ _ _).symm
  -- `k₁ = k₂` ⟹ `f` monic: two maps equalized by `f` both lift to `K`, and the lifts coincide.
  intro W u v huv
  have hu : (HasPullbacks.has f f).lift ⟨W, u, v, huv⟩ ≫ kp₁ (f := f) = u := kp_lift_p₁ u v huv
  have hv : (HasPullbacks.has f f).lift ⟨W, u, v, huv⟩ ≫ kp₂ (f := f) = v := kp_lift_p₂ u v huv
  calc u = (HasPullbacks.has f f).lift ⟨W, u, v, huv⟩ ≫ kp₁ (f := f) := hu.symm
    _ = (HasPullbacks.has f f).lift ⟨W, u, v, huv⟩ ≫ kp₂ (f := f) := by rw [hk]
    _ = v := hv

/-- **§1.526 (the points functor reflects isos).**  In a fully WELL-POINTED `PreLogos`, a map
    `f : X → Y` whose action on points is bijective (injective + surjective on `1 → -`) is an
    ISOMORPHISM.  PROOF: injective-on-points ⟹ monic (`monic_of_points_injective`, kernel pair
    well-pointed); surjective-on-points ⟹ cover (`cover_of_points_surjective`); monic + cover ⟹ iso
    (§1.512 `monic_cover_iso`). -/
theorem isIso_of_points_bijective (hwp : ∀ A : 𝒞, WellPointed A) {X Y : 𝒞} (f : X ⟶ Y)
    (hinj : ∀ x x' : one ⟶ X, x ≫ f = x' ≫ f → x = x')
    (hsurj : ∀ y : one ⟶ Y, ∃ x : one ⟶ X, x ≫ f = y) : IsIso f :=
  monic_cover_iso f
    (cover_of_points_surjective f (hwp Y) hsurj)
    (monic_of_points_injective f (hwp (kernelPair f)) hinj)

/-! ## §1.635 — the `1`-stage of the stalk: `Hom(1,A) → T_F̂(A)`.

  The TOP subterminator is `Subobject.entire one`, whose domain is `one` itself.  A global point
  `x : 1 → A` is therefore exactly the colimit name `(1, x)`; sending it to its class gives a
  natural map `Hom(1,A) → T_F̂(A)`, defined whenever `ℱ` contains the top. -/

/-- The TOP subterminator `1 ↣ 1` (identity), whose domain is `one`. -/
abbrev Top1 : Subobject 𝒞 one := Subobject.entire one

@[simp] theorem Top1_dom : (Top1 (𝒞 := 𝒞)).dom = one := rfl
@[simp] theorem Top1_arr : (Top1 (𝒞 := 𝒞)).arr = Cat.id one := rfl

/-- A FILTER (up-closed pre-filter) contains the TOP subterminator: any member `U ≤ 1` is pushed up
    to `1`.  This is the membership the `1`-stage bridge needs. -/
theorem filter_mem_top {ℱ : Subobject 𝒞 one → Prop} (hℱ : IsFilter ℱ) : ℱ (Top1 (𝒞 := 𝒞)) := by
  obtain ⟨U, hU⟩ := hℱ.1.1
  exact hℱ.2 U Top1 hU ⟨U.arr, Cat.comp_id _⟩

/-- The `1`-stage map `Hom(1,A) → T_F̂(A)`: send a global point `x : 1 → A` to the class of its name
    `(1, x)` over the top subterminator (using `ht : ℱ 1`). -/
def globalToStalk {ℱ : Subobject 𝒞 one → Prop} (ht : ℱ (Top1 (𝒞 := 𝒞))) {A : 𝒞}
    (x : one ⟶ A) : TF ℱ A :=
  TF.mk ℱ ⟨Top1, ht, x⟩

/-- NATURALITY: `globalToStalk` commutes with post-composition / `T_F̂(f)`. -/
theorem globalToStalk_natural {ℱ : Subobject 𝒞 one → Prop} (ht : ℱ (Top1 (𝒞 := 𝒞)))
    {A B : 𝒞} (f : A ⟶ B) (x : one ⟶ A) :
    TF.map ℱ f (globalToStalk ht x) = globalToStalk ht (x ≫ f) := rfl

/-! ## The PRINCIPAL ultra-filter at the top: its stalk IS the global-points functor.

  Take `ℱ = principalTop := {U | U is entire (≅ 1)}`, the principal filter generated by the top
  subterminator.  Every member is `≅ 1`, so a `PrefilterMap principalTop A` is, up to the canonical
  factorization, a global point `1 → A`, and `PrefRel` collapses to plain equality of points (a
  common refinement `W` of two top-members is again `≅ 1`, with a UNIQUE `1 → W.dom` inverse to
  `W.arr`, so the refinement witnesses are forced and the maps must already agree).  Hence
  `T_principalTop A = Hom(1,A)` and `T_principalTop(f) = Γ(f) = (· ≫ f)`.  This is the cleanest
  single stalk for reflecting isos: its `hrefl` is exactly §1.526 points-conservativity. -/

/-- The PRINCIPAL filter at the top: the entire (≅ 1) subterminators.  A pre-filter (closed under
    the meet `Top1`), proper (entire ⇒ not below `0` unless the category is degenerate — but we only
    need it as a pre-filter of projectives), with every member's domain a retract of `1`. -/
def principalTop : Subobject 𝒞 one → Prop := fun U => Subobject.IsEntire U

theorem principalTop_mem_top : principalTop (Top1 (𝒞 := 𝒞)) := by
  show IsIso (Top1 (𝒞 := 𝒞)).arr
  rw [Top1_arr]; exact ⟨Cat.id one, Cat.id_comp _, Cat.id_comp _⟩

/-- Any entire member `U` has a canonical point `pt U : 1 → U.dom` (inverse of `U.arr`), and every
    name `(U, g)` over it restricts to the global point `pt U ≫ g`. -/
noncomputable def entityPoint {U : Subobject 𝒞 one} (hU : principalTop U) : one ⟶ U.dom :=
  hU.choose

/-- `IsEntire U = IsIso U.arr = ∃ g, U.arr ≫ g = id ∧ g ≫ U.arr = id`, so `entityPoint = g` with
    `entityPoint ≫ U.arr = id one`. -/
theorem entityPoint_arr {U : Subobject 𝒞 one} (hU : principalTop U) :
    entityPoint hU ≫ U.arr = Cat.id one := hU.choose_spec.2

theorem arr_entityPoint {U : Subobject 𝒞 one} (hU : principalTop U) :
    U.arr ≫ entityPoint hU = Cat.id U.dom := hU.choose_spec.1

theorem principalTop_isPreFilter : IsPreFilter (principalTop (𝒞 := 𝒞)) := by
  refine ⟨⟨Top1, principalTop_mem_top⟩, ?_⟩
  intro U V hU hV
  -- `Top1 ≤ U` and `Top1 ≤ V` (both entire, so each is above the top via the entityPoint).
  refine ⟨Top1, principalTop_mem_top, ⟨entityPoint hU, ?_⟩, ⟨entityPoint hV, ?_⟩⟩
  · rw [entityPoint_arr]; rfl
  · rw [entityPoint_arr]; rfl

/-- On `principalTop`, the `1`-stage map is INJECTIVE: a `PrefRel`-witness `W` is entire, so its
    `entityPoint` cancels `W.arr`, turning `W.arr ≫ x = W.arr ≫ x'` into `x = x'`. -/
theorem globalToStalk_principal_injective {A : 𝒞} :
    Function.Injective
      (globalToStalk (ℱ := principalTop) (𝒞 := 𝒞) principalTop_mem_top (A := A)) := by
  intro x x' hxx'
  obtain ⟨W, hW, a, b, ha, hb, hab⟩ :=
    PrefRel_of_TF_eq principalTop principalTop_isPreFilter hxx'
  -- `a, b : W.dom → 1`, `a ≫ id = W.arr`, `b ≫ id = W.arr`, `a ≫ x = b ≫ x'`.
  have ha' : a = W.arr := by simpa [Top1_arr, Cat.comp_id] using ha
  have hb' : b = W.arr := by simpa [Top1_arr, Cat.comp_id] using hb
  rw [ha', hb'] at hab
  -- Pre-compose with the entityPoint of `W` to cancel `W.arr`.
  have := congrArg (fun m => entityPoint hW ≫ m) hab
  simpa [← Cat.assoc, entityPoint_arr, Cat.id_comp] using this

/-- On `principalTop`, the `1`-stage map is SURJECTIVE: every name `(U, g)` (U entire) is `PrefRel`
    to the global point `entityPoint U ≫ g` named over the top. -/
theorem globalToStalk_principal_surjective {A : 𝒞} :
    Function.Surjective
      (globalToStalk (ℱ := principalTop) (𝒞 := 𝒞) principalTop_mem_top (A := A)) := by
  refine Quot.ind (fun p => ?_)
  refine ⟨entityPoint p.hU ≫ p.map, ?_⟩
  -- class of `(Top1, entityPoint ≫ g)` equals class of `p = (U, g)`.
  refine Quot.sound ?_
  -- `PrefRel (Top1, ep≫g) (U, g)`: refine by `Top1`, witnesses `id : 1→1` and `ep : 1→U.dom`.
  -- goal1 `id ≫ Top1.arr = Top1.arr`; goal2 `ep ≫ U.arr = Top1.arr (= id)`; goal3 `id ≫ (ep≫g) = ep ≫ g`.
  exact ⟨Top1, principalTop_mem_top, Cat.id one, entityPoint p.hU,
    Cat.id_comp _, entityPoint_arr p.hU, Cat.id_comp _⟩

/-- `T_principalTop(f)` IS the global-points action `Γ(f) = (· ≫ f)` transported across the
    bijection `globalToStalk`.  We use this to transfer iso-reflection from `Γ` to the stalk. -/
theorem globalToStalk_principal_bijective {A : 𝒞} :
    Function.Injective (globalToStalk (ℱ := principalTop) (𝒞 := 𝒞) principalTop_mem_top (A := A)) ∧
    Function.Surjective (globalToStalk (ℱ := principalTop) (𝒞 := 𝒞) principalTop_mem_top (A := A)) :=
  ⟨globalToStalk_principal_injective, globalToStalk_principal_surjective⟩

/-! ## Projectivity of the `principalTop` members (so `T_principalTop` is a `RegularFunctor`). -/

/-- `Projective` transfers along an iso of the witnessed object: if `D` is projective and
    `φ : C → D` is iso, then `C` is projective.  A cover `e : A → C` gives a cover `e ≫ φ : A → D`
    (`cover_comp_iso`), split by `Projective D` as `s` (`s ≫ (e ≫ φ) = id D`); then `s ≫ φ⁻¹` splits
    `e`. -/
theorem projective_of_iso {C D : 𝒞} (φ : C ⟶ D) (hφ : IsIso φ) (hD : Projective D) :
    Projective C := by
  obtain ⟨ψ, hφψ, hψφ⟩ := id hφ
  intro A e he
  obtain ⟨s, hs⟩ := hD (e ≫ φ) (cover_comp_iso e φ he hφ)
  -- `hs : s ≫ (e ≫ φ) = id D`.  The section of `e` is `t = φ ≫ s`.
  refine ⟨φ ≫ s, ?_⟩
  have hse : s ≫ (e ≫ φ) = Cat.id D := hs
  -- cancel the monic `φ`: `((φ≫s)≫e) ≫ φ = φ = (id C) ≫ φ`.
  have hφm : Monic φ := by
    intro Z u v huv
    calc u = u ≫ (φ ≫ ψ) := by rw [hφψ, Cat.comp_id]
      _ = (u ≫ φ) ≫ ψ := (Cat.assoc _ _ _).symm
      _ = (v ≫ φ) ≫ ψ := by rw [huv]
      _ = v ≫ (φ ≫ ψ) := Cat.assoc _ _ _
      _ = v := by rw [hφψ, Cat.comp_id]
  refine hφm _ _ ?_
  calc ((φ ≫ s) ≫ e) ≫ φ = φ ≫ (s ≫ (e ≫ φ)) := by simp only [Cat.assoc]
    _ = φ ≫ Cat.id D := by rw [hse]
    _ = φ := Cat.comp_id _
    _ = Cat.id C ≫ φ := (Cat.id_comp _).symm

/-- The members of `principalTop` are PROJECTIVE once the TERMINATOR `1` is projective (which holds
    in a CAPITAL pre-logos, §1.525): each member is `≅ 1`, so transfer projectivity along `U.arr`.
    We take `Projective one` directly (rather than `Capital`) to avoid the two clashing `Capital`
    definitions (S1_52 well-supported⟹well-pointed vs S1_62 cover-splitting); the caller supplies it
    via `capital_one_Projective`/`capital_one_projective`. -/
theorem principalTop_projective (hone : Projective (one : 𝒞)) :
    ∀ U : Subobject 𝒞 one, principalTop U → Projective U.dom := fun U hU =>
  projective_of_iso U.arr hU hone

/-! ## The principal-top stalk reflects isos in a fully well-pointed pre-logos. -/

/-- **CONSERVATIVITY (single principal stalk).**  In a fully WELL-POINTED `PreLogos`, the principal
    top stalk `T_principalTop` REFLECTS ISOS: if `T_principalTop(f)` is iso then `f` is iso.

    PROOF.  `T_principalTop(f)` is `Γ(f)` conjugated by the bijection `globalToStalk`, so it being
    iso (= bijective in `Set`) makes `Γ(f)` bijective on points; §1.526 (`isIso_of_points_bijective`)
    then gives `f` iso.  This is Freyd's points functor as the reflecting representation. -/
theorem principalStalk_reflects_iso (hwp : ∀ A : 𝒞, WellPointed A)
    {X Y : 𝒞} (f : X ⟶ Y) (hiso : IsIso ((TF_functor (principalTop (𝒞 := 𝒞))).map f)) :
    IsIso f := by
  -- Extract bijectivity of `TF.map f` from the iso witness `g`.
  -- `(TF_functor _).map f = TF.map principalTop f` definitionally; `≫` in `Type` is `g ∘ f`.
  obtain ⟨g, hgL, hgR⟩ := hiso
  have hL : ∀ u : TF principalTop X, g (TF.map principalTop f u) = u := fun u => congrFun hgL u
  have hR : ∀ t : TF principalTop Y, TF.map principalTop f (g t) = t := fun t => congrFun hgR t
  -- INJECTIVE on points: `x ≫ f = x' ≫ f → x = x'`.
  have hinj : ∀ x x' : one ⟶ X, x ≫ f = x' ≫ f → x = x' := by
    intro x x' hx
    have e1 : TF.map principalTop f (globalToStalk principalTop_mem_top x)
            = TF.map principalTop f (globalToStalk principalTop_mem_top x') := by
      rw [globalToStalk_natural, globalToStalk_natural, hx]
    have hTinj : Function.Injective (TF.map principalTop f) := fun u v huv => by
      rw [← hL u, ← hL v, huv]
    exact globalToStalk_principal_injective (hTinj e1)
  -- SURJECTIVE on points: every `y : 1 → Y` is hit.
  have hsurj : ∀ y : one ⟶ Y, ∃ x : one ⟶ X, x ≫ f = y := by
    intro y
    have hTsurj : Function.Surjective (TF.map principalTop f) := fun t => ⟨g t, hR t⟩
    obtain ⟨u, hu⟩ := hTsurj (globalToStalk principalTop_mem_top y)
    obtain ⟨x, hx⟩ := globalToStalk_principal_surjective u
    refine ⟨x, ?_⟩
    apply globalToStalk_principal_injective
    rw [← globalToStalk_natural, hx, hu]
  exact isIso_of_points_bijective hwp f hinj hsurj

/-! ## §2.218 (K2) — the stalk-route faithfulness for a fully well-pointed pre-logos.

  Plugging the principal-top stalk into Freyd's `relStalk_faithful` discharges BOTH residuals of the
  stalk route at once:
    • PROJECTIVITY (`hproj`): `principalTop`'s members are `≅ 1`, projective once `1` is projective
      (`principalTop_projective` ← `Projective one`, automatic in a capital category §1.525);
    • CONSERVATIVITY (`hrefl`): the principal stalk reflects isos in a fully well-pointed category
      (`principalStalk_reflects_iso`).
  Hence `Rel(T_principalTop) : Rel(𝒞) ⟶ Rel(Set)` is a FAITHFUL allegory morphism — the §2.218
  stalk-route faithfulness, needing only full well-pointedness `hwp` and `Projective one`. -/

/-- **§2.218 (K2, discharged).**  For a positive pre-logos `𝒞` that is FULLY WELL-POINTED
    (`hwp : ∀ A, WellPointed A`) and whose TERMINATOR is projective (`hone`, §1.525 in the capital
    case), the principal-top stalk `Rel(T_principalTop)` is a FAITHFUL allegory morphism
    `Rel(𝒞) ⟶ Rel(Set)`.  This is the §2.218 stalk-route faithfulness with its two residuals
    (projectivity + single-stalk conservativity) BOTH discharged — no separate `hrefl` hypothesis. -/
theorem relStalk_faithful_of_wellPointed
    (hwp : ∀ A : 𝒞, WellPointed A) (hone : Projective (one : 𝒞)) :
    (TF_regularFunctor principalTop principalTop_isPreFilter
        (principalTop_projective hone)).relAllegoryHom.Faithful :=
  relStalk_faithful principalTop principalTop_isPreFilter (principalTop_projective hone)
    (fun {_ _} f hiso => principalStalk_reflects_iso hwp f hiso)

/-! ## §2.218 (K2) — the stalk-route REPRESENTATION of a tabular allegory in `Rel(Set)`

  Wires `relStalk_faithful_of_wellPointed` into the §2.218 assembly: for a TABULAR unitary
  distributive allegory `𝒜`, the carrier bridge `bridgeFunctor : 𝒜 ⟶ Rel(Map 𝒜)` (faithful, R2) and
  a faithful regular allegory morphism `cap : Rel(Map 𝒜) ⟶ Rel(Ā)` from capitalizing `Map 𝒜 ↪ Ā`
  (R3) compose with the principal-top stalk `Rel(T) : Rel(Ā) ⟶ Rel(Set)` to a FAITHFUL allegory
  morphism `𝒜 ⟶ Rel(Set)` — a faithful representation in the allegory of relations in a *single* set
  (a fortiori in a power).  This is the STALK route to §2.218 (Freyd §1.635), which needs only
  `Projective one` + FULL well-pointedness of `Ā` (`hwp`), NOT all-objects-projective AC.

  RESIDUAL (R3, the §1.543 capital target).  `Ā` must be a `PreLogos` that is FULLY WELL-POINTED
  and has a faithful `cap` from the capitalization of `Map 𝒜`.  The §1.543 transfinite tower's
  generic regular packaging is `Freyd.capitalization_regular_of_cofinalSystem`
  (`Freyd/CapitalizationTransfinite.lean`), which delivers a regular CAPITAL target — but `Capital`
  (`∀ A, WellSupported A → WellPointed A`, S1_52) gives well-pointedness only on WELL-SUPPORTED
  objects, whereas the stalk's iso-reflection (`principalStalk_reflects_iso`) needs FULL `∀ A,
  WellPointed A`.  That full well-pointedness is the genuine remaining residual of §1.543
  capitalization (see the §2.218 marker in `S2_21.lean`); it is surfaced here as the explicit
  `hwp` hypothesis, alongside `[PreLogos Ā]` and the bridge `cap`. -/
theorem repr_in_set_of_tabular_wellPointed
    {𝒜 : Type u} [Alg.TabularUnitaryDistributiveAllegory 𝒜]
    {Ā : Type u} [Cat.{u} Ā] [PreLogos Ā]
    (hwp : ∀ A : Ā, WellPointed A) (hone : Projective (one : Ā))
    (cap : @Alg.AllegoryFunctor (RelObj (Alg.MapObj 𝒜)) (RelObj Ā)
        (@relAllegory (Alg.MapObj 𝒜) Alg.mapCat Alg.mapRegularCategory) (relAllegory))
    (hcap : cap.Faithful) :
    ∃ rep : Alg.AllegoryFunctor 𝒜 (RelObj (Type u)), rep.Faithful := by
  letI : Cat (Alg.MapObj 𝒜) := Alg.mapCat
  letI : RegularCategory (Alg.MapObj 𝒜) := Alg.mapRegularCategory
  -- The three faithful factors: bridge (R2) ∘ cap (R3) ∘ stalk (K2 = relStalk_faithful_of_wellPointed).
  refine ⟨((bridgeFunctor 𝒜).comp cap).comp
      (TF_regularFunctor principalTop principalTop_isPreFilter
        (principalTop_projective hone)).relAllegoryHom, ?_⟩
  exact Alg.AllegoryFunctor.Faithful.comp
    (Alg.AllegoryFunctor.Faithful.comp (bridgeFunctor_faithful 𝒜) hcap)
    (relStalk_faithful_of_wellPointed hwp hone)

end Freyd.PreLogosHorn.Stalk
