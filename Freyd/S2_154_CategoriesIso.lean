/-
  Freyd & Scedrov, *Categories, Allegories* §2.154

      "A (UNITARY) REPRESENTATION OF ALLEGORIES is a functor between allegories which
       preserves (units,) reciprocation and intersection. …
       Given a representation of allegories T : A → B we obtain a representation of
       categories T' : Alg.Map(A) → Alg.Map(B).  If A and B are tabular, then T' preserves
       pullbacks, equalizers, and covers.  If, further, A and B are unitary and T is
       unitary, then T' preserves terminators, and consequently T' is a representation
       of regular categories.  …
       Clearly, if T' : C₁ → C₂ is a representation of regular categories it induces a
       representation of unitary allegories Rel(C₁) → Rel(C₂), from which we obtain:

           THE CATEGORY OF SMALL REGULAR CATEGORIES IS ISOMORPHIC TO THE CATEGORY OF
           SMALL UNITARY TABULAR ALLEGORIES."

  This file formalizes the headline.  Freyd's "isomorphic" relies on identifying `C` with
  `Alg.Map(Rel C)` and `𝒜` with `Rel(Alg.Map 𝒜)` on the nose; in Lean the roundtrips change the
  carrier TYPE (`RelObj (MapObj 𝒜) ≠ 𝒜` as types, even though the wrapper is a bijection),
  so the honest statement is a STRONG EQUIVALENCE (§1.32: functors both ways + natural
  isomorphisms to the identities).  All four roundtrip components are isomorphisms whose
  object parts are the identity up to the `RelObj` wrapper — the content of Freyd's "iso".

  Layout:
    1.  §2.15 unit facts (partial-unit maps, units unique up to map-iso, transfer,
        `pres_isUnit_of_isUnit` — the composability of "unitary").
    2.  §2.147/§2.16 characterizations in `Map 𝒜` (monic/cover/pullback/image, equationally).
    3.  §2.154 middle paragraph: a unitary representation `T` restricts to a REGULAR functor
        `Map T : Map 𝒜 → Map ℬ` (`mapRep_regular`, the hard new content).
    4.  §2.154 third paragraph: a regular functor `F` induces a unitary representation
        `Rel F` (units clause `relIsUnit_of_terminal`; `Rel F` is §2.218's `relAllegoryHom`),
        functorially (`relMap_of_id`/`relMap_of_comp`).
    5.  The bundled categories `SmallRegCat`/`SmallTabAlleg` and the functors `RelF`/`MapF`.
    6.  The counit isomorphism `Rel(Map 𝒜) ≅ 𝒜` in `SmallTabAlleg` (`counit_isIso`).
    7.  The unit isomorphism `C ≅ Map(Rel C)` in `SmallRegCat` (`unit_isIso`).
    8.  Naturality of both and the headline `smallRegCat_equiv_smallTabAlleg :
        StrongEquivalence RelF MapF`.

  Axioms (headline): `[propext, Classical.choice, Quot.sound]`.
-/
import Freyd.S2_111_RelCat
import Freyd.S2_218_ObjInclRegular
import Freyd.S2_51
import Freyd.S1_31

universe v u v₁ v₂ u₁ u₂

open Freyd Freyd.Alg

namespace Freyd.S2_154

/-- `calc`-chaining for the allegory order `⊑` (`Freyd.Alg.le` has no `Trans` instance). -/
instance {𝒜 : Type u} [Allegory.{v} 𝒜] {a b : 𝒜} :
    Trans (α := a ⟶ b) (β := a ⟶ b) (γ := a ⟶ b) Alg.le Alg.le Alg.le :=
  ⟨Alg.le_trans⟩

/-! ## 1.  §2.15 unit facts -/

section UnitFacts

variable {𝒜 : Type u} [Allegory.{v} 𝒜]

/-- §2.15: an ENTIRE morphism into a PARTIAL UNIT is a map (simplicity is free:
    `R°≫R : u → u ⊑ 1_u`). -/
theorem map_of_entire_to_partialUnit {u a : 𝒜} (hu : PartialUnit u)
    {R : a ⟶ u} (hR : Alg.Entire R) : Alg.Map R := ⟨hR, hu _⟩

/-- §2.15: any two MAPS into a partial unit agree (generalizes `Alg.Map(𝒜)`-terminality of
    the unit beyond the designated one). -/
theorem maps_to_partialUnit_unique {u a : 𝒜} (hu : PartialUnit u)
    {f g : a ⟶ u} (hf : Alg.Map f) (hg : Alg.Map g) : f = g := by
  apply map_order_discrete hf hg
  have h1 : f ⊑ (g ≫ g°) ≫ f := by
    have := comp_mono_right (Alg.entire_id_le hg.1) f; rwa [Cat.id_comp] at this
  have h3 : g ≫ g° ≫ f ⊑ g ≫ Cat.id u := comp_mono_left g (hu (g° ≫ f))
  rw [Cat.comp_id] at h3
  exact le_trans h1 ((Cat.assoc g g° f) ▸ h3)

/-- §2.15: a span through a partial unit is MAXIMAL — for maps `p : x → u`, `q : y → u`
    into a partial unit, every `R : x → y` satisfies `R ⊑ p ≫ q°`.  (This is why the
    tabulation of `p ≫ q°` is the product `x × y` in `Alg.Map 𝒜`.) -/
theorem le_span_of_partialUnit {u x y : 𝒜} (hu : PartialUnit u)
    {p : x ⟶ u} {q : y ⟶ u} (hp : Alg.Map p) (hq : Alg.Map q) (R : x ⟶ y) :
    R ⊑ p ≫ q° := by
  have h1 : R ⊑ (p ≫ p°) ≫ R := by
    have := comp_mono_right (Alg.entire_id_le hp.1) R; rwa [Cat.id_comp] at this
  have h2 : (p ≫ p°) ≫ R ⊑ (p ≫ p°) ≫ (R ≫ (q ≫ q°)) := by
    apply comp_mono_left
    have := comp_mono_left R (Alg.entire_id_le hq.1); rwa [Cat.comp_id] at this
  have h3 : (p ≫ p°) ≫ (R ≫ (q ≫ q°)) = p ≫ ((p° ≫ R ≫ q) ≫ q°) := by
    simp [Cat.assoc]
  have h4 : p ≫ ((p° ≫ R ≫ q) ≫ q°) ⊑ p ≫ (Cat.id u ≫ q°) :=
    comp_mono_left p (comp_mono_right (hu (p° ≫ R ≫ q)) q°)
  calc R ⊑ (p ≫ p°) ≫ R := h1
    _ ⊑ (p ≫ p°) ≫ (R ≫ (q ≫ q°)) := h2
    _ = p ≫ ((p° ≫ R ≫ q) ≫ q°) := h3
    _ ⊑ p ≫ (Cat.id u ≫ q°) := h4
    _ = p ≫ q° := by rw [Cat.id_comp]

/-- §2.15: units are unique up to a map-isomorphism.  Given partial units `u, v` and entire
    morphisms both ways, the forward one `R` is a map with `R≫R° = 1_u`, `R°≫R = 1_v`. -/
theorem partialUnit_iso {u v : 𝒜} (hu : PartialUnit u) (hv : PartialUnit v)
    {R : u ⟶ v} {S : v ⟶ u} (hR : Alg.Entire R) (hS : Alg.Entire S) :
    Alg.Map R ∧ R ≫ R° = Cat.id u ∧ R° ≫ R = Cat.id v := by
  have hRmap : Alg.Map R := map_of_entire_to_partialUnit hv hR
  have hRRo : R ≫ R° = Cat.id u := le_antisymm (hu _) (Alg.entire_id_le hR)
  -- S ≫ R = 1_v : `⊑` is the partial unit, `⊒` is entireness of the composite.
  have hSR : S ≫ R = Cat.id v := by
    apply le_antisymm (hv _)
    have h2 : (S ≫ R)° ⊑ Cat.id v := by
      have := recip_mono (hv (S ≫ R)); rwa [recip_id] at this
    calc Cat.id v ⊑ (S ≫ R) ≫ (S ≫ R)° := Alg.entire_id_le (entire_comp hS hR)
      _ ⊑ (S ≫ R) ≫ Cat.id v := comp_mono_left _ h2
      _ = S ≫ R := Cat.comp_id _
  -- hence S = R° on the nose.
  have hSRo : S = R° := by
    calc S = S ≫ Cat.id u := (Cat.comp_id S).symm
      _ = S ≫ (R ≫ R°) := by rw [hRRo]
      _ = (S ≫ R) ≫ R° := (Cat.assoc _ _ _).symm
      _ = Cat.id v ≫ R° := by rw [hSR]
      _ = R° := Cat.id_comp _
  exact ⟨hRmap, hRRo, by rw [← hSRo]; exact hSR⟩

/-- §2.15: `IsUnit` transfers along a map-isomorphism `k : x → w` (`k≫k° = 1`, `k°≫k = 1`). -/
theorem isUnit_transfer {w x : 𝒜} (hw : IsUnit w) {k : x ⟶ w} (_hk : Alg.Map k)
    (hkk : k ≫ k° = Cat.id x) (hkok : k° ≫ k = Cat.id w) : IsUnit x := by
  obtain ⟨hPU, hEnt⟩ := hw
  constructor
  · -- partial unit: conjugate an endo of x into an endo of w.
    intro T
    calc T = Cat.id x ≫ (T ≫ Cat.id x) := by rw [Cat.id_comp, Cat.comp_id]
      _ = (k ≫ k°) ≫ (T ≫ (k ≫ k°)) := by rw [hkk]
      _ = k ≫ ((k° ≫ T ≫ k) ≫ k°) := by simp [Cat.assoc]
      _ ⊑ k ≫ (Cat.id w ≫ k°) := comp_mono_left k (comp_mono_right (hPU _) k°)
      _ = k ≫ k° := by rw [Cat.id_comp]
      _ = Cat.id x := hkk
  · -- entireness: postcompose the entire `a → w` with the entire `k° : w → x`.
    intro a
    obtain ⟨R, hR⟩ := hEnt a
    have hko : Alg.Entire (k° : w ⟶ x) := by
      show Cat.id w ∩ k° ≫ k°° = Cat.id w
      rw [Allegory.recip_recip, hkok, Allegory.inter_idem]
    exact ⟨R ≫ k°, entire_comp hR hko⟩

/-- **§2.154 (units clause)**: an allegory functor sending SOME unit to a unit sends EVERY
    unit to a unit.  (Units are unique up to map-iso — `partialUnit_iso` — and allegory
    functors preserve map-isos.)  This is what makes "unitary representation" composable. -/
theorem pres_isUnit_of_isUnit {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (F : AllegoryFunctor 𝒜 ℬ) {u₀ : 𝒜} (hu₀ : IsUnit u₀) (hFu₀ : IsUnit (F.obj u₀))
    {v : 𝒜} (hv : IsUnit v) : IsUnit (F.obj v) := by
  obtain ⟨R, hR⟩ := hv.2 u₀   -- entire R : u₀ ⟶ v
  obtain ⟨S, hS⟩ := hu₀.2 v   -- entire S : v ⟶ u₀
  obtain ⟨hSmap, hSS, hSoS⟩ := partialUnit_iso hv.1 hu₀.1 hS hR
  refine isUnit_transfer hFu₀ (k := F.map S) (F.preserves_map hSmap) ?_ ?_
  · rw [← F.map_recip, ← F.map_comp, hSS, F.map_id]
  · rw [← F.map_recip, ← F.map_comp, hSoS, F.map_id]

end UnitFacts

/-! ## 2.  §2.147/§2.16 equational characterizations in `Alg.Map 𝒜`

  Monics, covers, pullback cones and images of `Alg.Map 𝒜` are all characterized by
  ALLEGORY EQUATIONS, hence preserved by any representation of allegories (§2.154). -/

section MapChar

variable {A : Type u} [TabularUnitaryAllegory A]

/-- §2.142: a map is MONIC in `Alg.Map 𝒜` iff `m ≫ m° = 1` ("injective").
    Forward: `mapMonic_inj` + entireness; backward: `map_retract_monic`. -/
theorem mapMonic_iff {q : A} {a : MapObj A} (m : q ⟶ a) (hm : Alg.Map m) :
    @Monic (MapObj A) (mapCat (𝒜 := A)) q a ⟨m, hm⟩ ↔ m ≫ m° = Cat.id q := by
  constructor
  · intro h
    exact le_antisymm (mapMonic_inj hm h) (Alg.entire_id_le hm.1)
  · intro h
    exact map_retract_monic hm h

/-- §2.147: a map is a COVER in `Alg.Map 𝒜` iff `f° ≫ f = 1` ("surjective").
    Forward: `mapCover_entire` + simplicity; backward: `mapEntire_cover`. -/
theorem mapCover_iff {a c : MapObj A} (f : @Cat.Hom _ (mapCat (𝒜 := A)) a c) :
    @Cover (MapObj A) (mapCat (𝒜 := A)) a c f ↔ f.val° ≫ f.val = Cat.id c := by
  constructor
  · intro h
    exact le_antisymm f.property.2 (mapCover_entire f h)
  · intro h
    exact mapEntire_cover f (by rw [h]; exact le_refl _)

/-- Tabulations transport along a map-iso of the apex: if `i` is a map with
    `i≫i° = 1`, `i°≫i = 1` and `(f, g)` tabulates `R`, then `(i≫f, i≫g)` tabulates `R`. -/
theorem tabulates_precomp_iso {p q a b : A} {i : q ⟶ p} (hi : Alg.Map i)
    (hii : i ≫ i° = Cat.id q) (hioi : i° ≫ i = Cat.id p)
    {f : p ⟶ a} {g : p ⟶ b} {R : a ⟶ b} (ht : Tabulates f g R) :
    Tabulates (i ≫ f) (i ≫ g) R := by
  obtain ⟨hf, hg, hR, hjm⟩ := ht
  refine ⟨map_comp hi hf, map_comp hi hg, ?_, ?_⟩
  · -- R = (i≫f)° ≫ (i≫g) = f° ≫ (i°≫i) ≫ g = f° ≫ g.
    rw [hR, Allegory.recip_comp]
    calc f° ≫ g = f° ≫ Cat.id p ≫ g := by rw [Cat.id_comp]
      _ = f° ≫ (i° ≫ i) ≫ g := by rw [hioi]
      _ = (f° ≫ i°) ≫ (i ≫ g) := by simp [Cat.assoc]
  · -- (i≫f)(i≫f)° ∩ (i≫g)(i≫g)° = i(ff° ∩ gg°)i° = i ≫ i° = 1.
    have hexpf : (i ≫ f) ≫ (i ≫ f)° = i ≫ ((f ≫ f°) ≫ i°) := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    have hexpg : (i ≫ g) ≫ (i ≫ g)° = i ≫ ((g ≫ g°) ≫ i°) := by
      rw [Allegory.recip_comp]; simp [Cat.assoc]
    rw [hexpf, hexpg]
    -- pull `i ≫ –` out of the intersection (`i` simple), and `– ≫ i°` (reciprocate the
    -- `simple_dist_inter` law for `i`).
    have h2 : ((f ≫ f°) ∩ (g ≫ g°)) ≫ i° = ((f ≫ f°) ≫ i°) ∩ ((g ≫ g°) ≫ i°) := by
      have h := simple_dist_inter hi.2 ((f ≫ f°)°) ((g ≫ g°)°)
      have h' := congrArg Allegory.recip h
      simp only [Allegory.recip_comp, Allegory.recip_inter, Allegory.recip_recip] at h'
      exact h'
    calc i ≫ ((f ≫ f°) ≫ i°) ∩ i ≫ ((g ≫ g°) ≫ i°)
        = i ≫ (((f ≫ f°) ≫ i°) ∩ ((g ≫ g°) ≫ i°)) := (simple_dist_inter hi.2 _ _).symm
      _ = i ≫ (((f ≫ f°) ∩ (g ≫ g°)) ≫ i°) := by rw [← h2]
      _ = i ≫ (Cat.id p ≫ i°) := by rw [hjm]
      _ = i ≫ i° := by rw [Cat.id_comp]
      _ = Cat.id q := hii

/-- **§2.147 (pullback cones tabulate)**: the legs of ANY pullback cone of maps
    `f : a → c`, `g : b → c` in `Alg.Map 𝒜` tabulate `f ≫ g°`.  (Compare the cone with the
    canonical tabulation of `f ≫ g°` via the mediating maps in both directions; the
    comparison is a map-iso and `tabulates_precomp_iso` transports.) -/
theorem mapIsPullback_tabulates {a b c : MapObj A}
    {f : @Cat.Hom _ (mapCat (𝒜 := A)) a c} {g : @Cat.Hom _ (mapCat (𝒜 := A)) b c}
    (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g)
    (hpb : @Cone.IsPullback (MapObj A) (mapCat (𝒜 := A)) a b c f g cone) :
    Tabulates (@Cone.π₁ (MapObj A) (mapCat (𝒜 := A)) a b c f g cone).val
      (@Cone.π₂ (MapObj A) (mapCat (𝒜 := A)) a b c f g cone).val
      (f.val ≫ g.val°) := by
  -- Canonical tabulation (p, π₁, π₂) of f ≫ g°.
  obtain ⟨p, π₁, π₂, ht⟩ := Classical.choice (α := PSigma fun p : A =>
      PSigma fun π₁ : p ⟶ _ => PSigma fun π₂ : p ⟶ _ =>
      Tabulates π₁ π₂ (f.val ≫ g.val°)) (by
    obtain ⟨p, π₁, π₂, ht⟩ := TabularAllegory.tabular (𝒜 := A) (f.val ≫ g.val°)
    exact ⟨⟨p, π₁, π₂, ht⟩⟩)
  -- Cone-field accessors.
  let cpt : MapObj A := @Cone.pt _ (mapCat (𝒜 := A)) a b c f g cone
  let cπ₁ : @Cat.Hom _ (mapCat (𝒜 := A)) cpt a := @Cone.π₁ _ (mapCat (𝒜 := A)) a b c f g cone
  let cπ₂ : @Cat.Hom _ (mapCat (𝒜 := A)) cpt b := @Cone.π₂ _ (mapCat (𝒜 := A)) a b c f g cone
  have hcw : cπ₁.val ≫ f.val = cπ₂.val ≫ g.val :=
    congrArg Subtype.val (@Cone.w _ (mapCat (𝒜 := A)) a b c f g cone)
  -- hm : cpt → p mediates the cone into the tabulation.
  obtain ⟨hm, hm_map, hm1, hm2, _⟩ :=
    tab_pullback_UMP g.property ht cπ₁.property cπ₂.property hcw
  -- The canonical tabulation is itself a cone; u : p → cpt from the pullback UMP.
  let cone0 : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g :=
    @Cone.mk (MapObj A) (mapCat (𝒜 := A)) a b c f g p ⟨π₁, ht.1⟩ ⟨π₂, ht.2.1⟩
      (Subtype.ext (tab_pullback_cone' f.property g.property ht))
  obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ := hpb cone0
  have hu1' : u.val ≫ cπ₁.val = π₁ := congrArg Subtype.val hu1
  have hu2' : u.val ≫ cπ₂.val = π₂ := congrArg Subtype.val hu2
  -- u ≫ hm = 1_p (tabulation uniqueness).
  have huv : u.val ≫ hm = Cat.id p := by
    apply tabulation_UP_unique ht (map_comp u.property hm_map) (id_is_map_local p)
    · rw [Cat.assoc, hm1, hu1', Cat.id_comp]
    · rw [Cat.assoc, hm2, hu2', Cat.id_comp]
  -- hm ≫ u = 1_cpt (pullback uniqueness against the cone itself).
  have hvu : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt p cpt ⟨hm, hm_map⟩ u
      = @Cat.id (MapObj A) (mapCat (𝒜 := A)) cpt := by
    obtain ⟨w, ⟨_, _⟩, hwuniq⟩ := hpb cone
    have h1 : @Cat.comp (MapObj A) (mapCat (𝒜 := A)) cpt p cpt ⟨hm, hm_map⟩ u = w := by
      apply hwuniq
      · apply Subtype.ext
        show (hm ≫ u.val) ≫ cπ₁.val = cπ₁.val
        rw [Cat.assoc, hu1', hm1]
      · apply Subtype.ext
        show (hm ≫ u.val) ≫ cπ₂.val = cπ₂.val
        rw [Cat.assoc, hu2', hm2]
    have h2 : @Cat.id (MapObj A) (mapCat (𝒜 := A)) cpt = w := by
      apply hwuniq
      · exact Subtype.ext (Cat.id_comp cπ₁.val)
      · exact Subtype.ext (Cat.id_comp cπ₂.val)
    rw [h1, h2]
  have hvu' : hm ≫ u.val = Cat.id cpt := congrArg Subtype.val hvu
  -- hm is a map-iso: hm°≫hm = 1_p from the retraction u (map_retr_leg); hm° = u.
  have hleg : hm° ≫ hm = Cat.id p := map_retr_leg hm_map huv
  have hmo_eq_u : hm° = u.val := by
    calc hm° = hm° ≫ Cat.id cpt := (Cat.comp_id _).symm
      _ = hm° ≫ (hm ≫ u.val) := by rw [hvu']
      _ = (hm° ≫ hm) ≫ u.val := (Cat.assoc _ _ _).symm
      _ = Cat.id p ≫ u.val := by rw [hleg]
      _ = u.val := Cat.id_comp _
  have hmm : hm ≫ hm° = Cat.id cpt := by rw [hmo_eq_u]; exact hvu'
  -- transport the canonical tabulation along hm.
  have := tabulates_precomp_iso hm_map hmm hleg ht
  rwa [show hm ≫ π₁ = cπ₁.val from hm1, show hm ≫ π₂ = cπ₂.val from hm2] at this

/-- **§2.147 (tabulating cones are pullbacks)**: a cone of maps whose legs tabulate
    `f ≫ g°` satisfies the pullback universal property (from `tab_pullback_UMP`). -/
theorem mapTabulates_isPullback {a b c : MapObj A}
    {f : @Cat.Hom _ (mapCat (𝒜 := A)) a c} {g : @Cat.Hom _ (mapCat (𝒜 := A)) b c}
    (cone : @Cone (MapObj A) (mapCat (𝒜 := A)) a b c f g)
    (ht : Tabulates (@Cone.π₁ (MapObj A) (mapCat (𝒜 := A)) a b c f g cone).val
      (@Cone.π₂ (MapObj A) (mapCat (𝒜 := A)) a b c f g cone).val (f.val ≫ g.val°)) :
    @Cone.IsPullback (MapObj A) (mapCat (𝒜 := A)) a b c f g cone := by
  intro d
  let dpt : MapObj A := @Cone.pt _ (mapCat (𝒜 := A)) a b c f g d
  let dπ₁ : @Cat.Hom _ (mapCat (𝒜 := A)) dpt a := @Cone.π₁ _ (mapCat (𝒜 := A)) a b c f g d
  let dπ₂ : @Cat.Hom _ (mapCat (𝒜 := A)) dpt b := @Cone.π₂ _ (mapCat (𝒜 := A)) a b c f g d
  have hdw : dπ₁.val ≫ f.val = dπ₂.val ≫ g.val :=
    congrArg Subtype.val (@Cone.w _ (mapCat (𝒜 := A)) a b c f g d)
  obtain ⟨hm, hm_map, hm1, hm2, huniq⟩ :=
    tab_pullback_UMP g.property ht dπ₁.property dπ₂.property hdw
  refine ⟨⟨hm, hm_map⟩, ⟨Subtype.ext hm1, Subtype.ext hm2⟩, ?_⟩
  intro v hv1 hv2
  exact Subtype.ext (huniq v.val v.property
    (congrArg Subtype.val hv1) (congrArg Subtype.val hv2))

/-- **§2.16 (image characterization, forward)**: if `I` is an image of `f : a → b` in
    `Alg.Map 𝒜` then its coreflexive is `dom (f°)`: `I.arr° ≫ I.arr = dom (f.val°)`. -/
theorem mapIsImage_corOf {a b : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a b)
    (I : @Subobject (MapObj A) (mapCat (𝒜 := A)) b)
    (hI : @IsImage (MapObj A) (mapCat (𝒜 := A)) a b f I) :
    (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b I).val°
      ≫ (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b I).val = dom (f.val°) := by
  let m : @Cat.Hom _ (mapCat (𝒜 := A)) _ b := @Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b I
  show m.val° ≫ m.val = dom (f.val°)
  apply le_antisymm
  · -- ⊑ : split dom(f°) as e°≫e; `⟨p,e⟩` allows f, so minimality factors I through it.
    obtain ⟨p, e, he_map, hee_l, hee_r⟩ := coreflexive_splits (dom_coreflexive (f.val°))
    have hSallows : @Allows (MapObj A) (mapCat (𝒜 := A)) a b
        (@Subobject.mk (MapObj A) (mapCat (𝒜 := A)) b p ⟨e, he_map⟩
          (map_retract_monic he_map hee_r)) f := by
      -- (e,e) tabulates e°≫e = dom(f°) ⊒ f°≫f? — no: f°f ⊑ dom(f°); use tabulation UP.
      have htab_e : Tabulates e e (e° ≫ e) :=
        ⟨he_map, he_map, rfl, by rw [Allegory.inter_idem, hee_r]⟩
      have hff_le : f.val° ≫ f.val ⊑ e° ≫ e := by
        rw [hee_l]
        exact le_inter f.property.2 (by rw [Allegory.recip_recip]; exact le_refl _)
      obtain ⟨k, hk, hke, _⟩ := tabulation_UP_forward htab_e f.property f.property hff_le
      exact ⟨⟨k, hk⟩, Subtype.ext hke⟩
    obtain ⟨h, hh⟩ := hI.2 _ hSallows
    have hh' : h.val ≫ e = m.val := congrArg Subtype.val hh
    calc m.val° ≫ m.val = (h.val ≫ e)° ≫ (h.val ≫ e) := by rw [hh']
      _ = e° ≫ (h.val° ≫ h.val) ≫ e := by rw [Allegory.recip_comp]; simp [Cat.assoc]
      _ ⊑ e° ≫ Cat.id _ ≫ e := comp_mono_left _ (comp_mono_right h.property.2 e)
      _ = e° ≫ e := by rw [Cat.id_comp]
      _ = dom (f.val°) := hee_l
  · -- ⊒ : I allows f, so dom(f°) = 1 ∩ f°≫f ⊑ m°≫m.
    obtain ⟨k, hk⟩ := hI.1
    have hk' : k.val ≫ m.val = f.val := congrArg Subtype.val hk
    have h1 : f.val° ≫ f.val ⊑ m.val° ≫ m.val := by
      calc f.val° ≫ f.val = m.val° ≫ (k.val° ≫ k.val) ≫ m.val := by
            rw [← hk', Allegory.recip_comp]; simp [Cat.assoc]
        _ ⊑ m.val° ≫ Cat.id _ ≫ m.val := comp_mono_left _ (comp_mono_right k.property.2 _)
        _ = m.val° ≫ m.val := by rw [Cat.id_comp]
    calc dom (f.val°) = Cat.id b ∩ f.val° ≫ f.val := by
          show Cat.id b ∩ f.val° ≫ f.val°° = _; rw [Allegory.recip_recip]
      _ ⊑ f.val° ≫ f.val := inter_lb_right _ _
      _ ⊑ m.val° ≫ m.val := h1

/-- **§2.16 (image characterization, backward)**: a MONIC map `m` with coreflexive
    `m° ≫ m = dom (f°)` is an image of `f` in `Alg.Map 𝒜`. -/
theorem mapIsImage_of_corOf {a b : MapObj A}
    (f : @Cat.Hom _ (mapCat (𝒜 := A)) a b)
    (I : @Subobject (MapObj A) (mapCat (𝒜 := A)) b)
    (hcor : (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b I).val°
      ≫ (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b I).val = dom (f.val°)) :
    @IsImage (MapObj A) (mapCat (𝒜 := A)) a b f I := by
  let m : @Cat.Hom _ (mapCat (𝒜 := A)) _ b := @Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b I
  have hmono : @Monic (MapObj A) (mapCat (𝒜 := A)) _ b m :=
    @Subobject.monic (MapObj A) (mapCat (𝒜 := A)) b I
  have hmm : m.val ≫ m.val° = Cat.id _ := by
    have := (mapMonic_iff m.val m.property).mp (by
      -- `⟨m.val, m.property⟩ = m` by subtype eta.
      exact hmono)
    exact this
  constructor
  · -- allows: tabulate m°≫m by (m,m); f°f ⊑ dom(f°) = m°≫m.
    have htab : Tabulates m.val m.val (m.val° ≫ m.val) :=
      ⟨m.property, m.property, rfl, by rw [Allegory.inter_idem, hmm]⟩
    have hff_le : f.val° ≫ f.val ⊑ m.val° ≫ m.val := by
      rw [hcor]
      exact le_inter f.property.2 (by rw [Allegory.recip_recip]; exact le_refl _)
    obtain ⟨k, hk, hke, _⟩ := tabulation_UP_forward htab f.property f.property hff_le
    exact ⟨⟨k, hk⟩, Subtype.ext hke⟩
  · -- minimality: `mapIsImage_min_aux` with e := m.
    intro S hS
    obtain ⟨k_S, hk_S⟩ := hS
    have hle : m.val° ≫ m.val ⊑ f.val° ≫ f.val := by
      rw [hcor]
      show Cat.id b ∩ f.val° ≫ f.val°° ⊑ _
      rw [Allegory.recip_recip]; exact inter_lb_right _ _
    have := mapIsImage_min_aux (A := A) m.property hmm f hle S k_S hk_S
    -- `Subobject.mk _ ⟨m.val, m.property⟩ _ = I` by eta on subtypes and structures.
    exact this

/-- The tabulation of a span through a partial unit is a PRODUCT cone in `Map 𝒜`
    (existence + uniqueness of the mediating map, at the allegory level). -/
theorem tabulates_span_partialUnit_product {u' : A} (hu' : PartialUnit u')
    {a b P : A} {pa : a ⟶ u'} {pb : b ⟶ u'} (hpa : Alg.Map pa) (hpb : Alg.Map pb)
    {r : P ⟶ a} {s : P ⟶ b} (ht : Tabulates r s (pa ≫ pb°))
    {w : A} {x : w ⟶ a} {y : w ⟶ b} (hx : Alg.Map x) (hy : Alg.Map y) :
    ∃ h : w ⟶ P, Alg.Map h ∧ h ≫ r = x ∧ h ≫ s = y ∧
      ∀ h', Alg.Map h' → h' ≫ r = x → h' ≫ s = y → h' = h := by
  obtain ⟨h, hh, hr, hs⟩ := tabulation_UP_forward ht hx hy
    (le_span_of_partialUnit hu' hpa hpb (x° ≫ y))
  exact ⟨h, hh, hr, hs, fun h' hh' hr' hs' =>
    tabulation_UP_unique ht hh' hh (hr'.trans hr.symm) (hs'.trans hs.symm)⟩

end MapChar

/-! ## 3.  §2.154 middle paragraph: `Map T : Map 𝒜 → Map ℬ` is a regular functor

  "Given a representation of allegories T : A → B we obtain a representation of categories
   T' : Map(A) → Map(B).  If A and B are tabular, then T' preserves pullbacks, equalizers,
   and covers.  If, further, A and B are unitary and T is unitary, then T' preserves
   terminators, and consequently T' is a representation of regular categories." -/

section MapRep

/-- An allegory functor preserves `dom` (it is equational: `dom R = 1 ∩ R≫R°`). -/
theorem map_dom {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (T : AllegoryFunctor 𝒜 ℬ) {a b : 𝒜} (R : a ⟶ b) :
    T.map (Alg.dom R) = Alg.dom (T.map R) := by
  show T.map (Cat.id a ∩ R ≫ R°) = Cat.id _ ∩ T.map R ≫ (T.map R)°
  rw [T.map_inter, T.map_id, T.map_comp, T.map_recip]

-- The §2.154 "preserves terminators" clause carried by `RegRep` below uses `Horn.IsTerminalObj`
-- (the predicate `∀ Y, ∃! f : Y ⟶ X`, imported from S1_444).

-- carrier universes may differ, but the HOM universe `v` must match on both sides
-- (`RegularFunctor` lives at a single hom universe).
variable {A : Type u₁} {B : Type u₂}
  [TabularUnitaryAllegory.{u₁, v} A] [TabularUnitaryAllegory.{u₂, v} B]
  (T : AllegoryFunctor A B)

/-- **§2.154**: the restriction `T' : Map 𝒜 → Map ℬ` of a representation of allegories
    (maps go to maps, §2.51).  Built by explicit `@Functor.mk` — the `where` syntax would
    re-synthesize `Cat (MapObj _)` as the allegory `toCat` (the standard `MapObj` diamond). -/
def mapRepFunctor :
    @Functor (MapObj A) (MapObj B) (mapCat (𝒜 := A)) (mapCat (𝒜 := B)) :=
  @Functor.mk (MapObj A) (MapObj B) (mapCat (𝒜 := A)) (mapCat (𝒜 := B)) T.obj
    (fun {_X _Y} f => ⟨T.map f.val, T.preserves_map f.property⟩)
    (fun X => Subtype.ext (T.map_id X))
    (fun {_X _Y _Z} f g => Subtype.ext (T.map_comp f.val g.val))

/-- **§2.154**: `T'` preserves MONICS (`m≫m° = 1` is equational). -/
theorem mapRep_pres_mono :
    @PreservesMono (MapObj A) (mapCat (𝒜 := A)) (MapObj B) (mapCat (𝒜 := B))
      (mapRepFunctor T) := by
  intro X Y f hf
  have h := (mapMonic_iff (A := A) f.val f.property).mp hf
  show @Monic (MapObj B) (mapCat (𝒜 := B)) _ _ ⟨T.map f.val, T.preserves_map f.property⟩
  exact (mapMonic_iff (A := B) (T.map f.val) (T.preserves_map f.property)).mpr
    (by rw [← T.map_recip, ← T.map_comp, h, T.map_id])

/-- **§2.154**: `T'` preserves COVERS (`f°≫f = 1` is equational). -/
theorem mapRep_pres_covers :
    @PreservesCovers (MapObj A) (MapObj B) (mapCat (𝒜 := A)) (mapCat (𝒜 := B))
      (mapRepFunctor T) := by
  intro X Y f hf
  have h := (mapCover_iff (A := A) f).mp hf
  show @Cover (MapObj B) (mapCat (𝒜 := B)) _ _ ⟨T.map f.val, T.preserves_map f.property⟩
  exact (mapCover_iff (A := B) ⟨T.map f.val, T.preserves_map f.property⟩).mpr
    (by show (T.map f.val)° ≫ T.map f.val = _
        rw [← T.map_recip, ← T.map_comp, h, T.map_id])

/-- **§2.154**: `T'` preserves PULLBACKS: pullback cones are exactly the tabulations of
    `f ≫ g°` (`mapIsPullback_tabulates`/`mapTabulates_isPullback`) and representations of
    allegories preserve tabulations (§2.51). -/
theorem mapRep_pres_pullback :
    @PreservesPullbacks (MapObj A) (MapObj B) (mapCat (𝒜 := A)) (mapCat (𝒜 := B))
      (mapRepFunctor T) := by
  intro a b c f g cone hpb
  apply mapTabulates_isPullback
  have ht := T.preserves_tabulates (mapIsPullback_tabulates cone hpb)
  rw [T.map_comp, T.map_recip] at ht
  exact ht

/-- **§2.154**: `T'` preserves IMAGES (the image is the splitting of the coreflexive
    `dom f°`, an equational description). -/
theorem mapRep_pres_image :
    @PreservesImages (MapObj A) (MapObj B) (mapCat (𝒜 := A)) (mapCat (𝒜 := B))
      (mapRepFunctor T) (mapRep_pres_mono T) := by
  intro a b f I hI
  apply mapIsImage_of_corOf
  show (T.map (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b I).val)°
      ≫ T.map (@Subobject.arr (MapObj A) (mapCat (𝒜 := A)) b I).val
      = Alg.dom ((T.map f.val)°)
  rw [← T.map_recip, ← T.map_comp, mapIsImage_corOf f I hI, map_dom, T.map_recip]

/-- **§2.154**: a UNITARY `T'` preserves TERMINATORS: the terminator of `Map 𝒜` is the
    unit, `T` sends it to a unit, and units are terminators in `Map ℬ` (§2.15). -/
theorem mapRep_pres_term (hu : IsUnit (T.obj (UnitaryAllegory.unit_obj (𝒜 := A)))) :
    @Freyd.Horn.IsTerminalObj (MapObj B) (mapCat (𝒜 := B)) (T.obj (UnitaryAllegory.unit_obj (𝒜 := A))) := by
  intro Y
  obtain ⟨E, hE⟩ := hu.2 Y
  refine ⟨⟨E, map_of_entire_to_partialUnit hu.1 hE⟩, fun g => ?_⟩
  exact Subtype.ext (maps_to_partialUnit_unique hu.1 g.property
    (map_of_entire_to_partialUnit hu.1 hE))

/-- The tabulation equation for the CHOSEN product of `Map 𝒜`: it is (defined as) the
    pullback over the unit, so its legs tabulate `trm a ≫ (trm b)°`. -/
theorem mapProd_tabulates {A : Type u₁} [TabularUnitaryAllegory.{u₁, v} A] (a b : MapObj A) :
    Tabulates
      (@Freyd.fst (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts a b).val
      (@Freyd.snd (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts a b).val
      ((@HasTerminal.trm (MapObj A) (mapCat (𝒜 := A)) mapHasTerminal a).val
        ≫ (@HasTerminal.trm (MapObj A) (mapCat (𝒜 := A)) mapHasTerminal b).val°) :=
  mapIsPullback_tabulates
    (@HasPullback.cone (MapObj A) (mapCat (𝒜 := A)) a b _ _ _
      (mapHasPullback (@HasTerminal.trm (MapObj A) (mapCat (𝒜 := A)) mapHasTerminal a)
        (@HasTerminal.trm (MapObj A) (mapCat (𝒜 := A)) mapHasTerminal b)))
    (@HasPullback.cone_isPullback (MapObj A) (mapCat (𝒜 := A)) a b _ _ _
      (mapHasPullback (@HasTerminal.trm (MapObj A) (mapCat (𝒜 := A)) mapHasTerminal a)
        (@HasTerminal.trm (MapObj A) (mapCat (𝒜 := A)) mapHasTerminal b)))

/-- **§2.154**: a UNITARY `T'` preserves BINARY PRODUCTS.  The product of `Map 𝒜`
    tabulates the span through the unit; `T` carries it to a tabulation of a span through
    the unit `T(1)`, which is maximal (§2.15), hence again a product cone; the canonical
    comparison to the chosen product of `Map ℬ` is then an isomorphism. -/
theorem mapRep_pres_prod (hu : IsUnit (T.obj (UnitaryAllegory.unit_obj (𝒜 := A)))) :
    @PreservesBinaryProducts (MapObj A) (MapObj B) (mapCat (𝒜 := A)) (mapCat (𝒜 := B))
      (mapRepFunctor T) mapHasBinaryProducts mapHasBinaryProducts := by
  intro a b
  -- upstairs product legs and the unit maps.
  let ta := @HasTerminal.trm (MapObj A) (mapCat (𝒜 := A)) mapHasTerminal a
  let tb := @HasTerminal.trm (MapObj A) (mapCat (𝒜 := A)) mapHasTerminal b
  let fA := @Freyd.fst (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts a b
  let sA := @Freyd.snd (MapObj A) (mapCat (𝒜 := A)) mapHasBinaryProducts a b
  -- the T-image of the upstairs product cone tabulates the span (T ta, T tb) through T(1).
  have htab : Tabulates (T.map fA.val) (T.map sA.val)
      (T.map ta.val ≫ (T.map tb.val)°) := by
    have h := T.preserves_tabulates (mapProd_tabulates (A := A) a b)
    rw [T.map_comp, T.map_recip] at h
    exact h
  -- downstairs product legs.
  let fB := @Freyd.fst (MapObj B) (mapCat (𝒜 := B)) mapHasBinaryProducts (T.obj a) (T.obj b)
  let sB := @Freyd.snd (MapObj B) (mapCat (𝒜 := B)) mapHasBinaryProducts (T.obj a) (T.obj b)
  -- mediating map from the downstairs product into the T-image cone.
  obtain ⟨k, hk, hkr, hks, _⟩ := tabulates_span_partialUnit_product (A := B) hu.1
    (T.preserves_map ta.property) (T.preserves_map tb.property) htab
    fB.property sB.property
  -- the comparison pair κ = ⟨T' fst, T' snd⟩ and the pair laws.
  let κ := @Freyd.pair (MapObj B) (mapCat (𝒜 := B)) mapHasBinaryProducts _ _ _
    (⟨T.map fA.val, T.preserves_map fA.property⟩ :
      @Cat.Hom (MapObj B) (mapCat (𝒜 := B)) (T.obj _) (T.obj a))
    (⟨T.map sA.val, T.preserves_map sA.property⟩ :
      @Cat.Hom (MapObj B) (mapCat (𝒜 := B)) (T.obj _) (T.obj b))
  have hκf : @Cat.comp (MapObj B) (mapCat (𝒜 := B)) _ _ _ κ fB
      = ⟨T.map fA.val, T.preserves_map fA.property⟩ :=
    @Freyd.fst_pair (MapObj B) (mapCat (𝒜 := B)) mapHasBinaryProducts _ _ _ _ _
  have hκs : @Cat.comp (MapObj B) (mapCat (𝒜 := B)) _ _ _ κ sB
      = ⟨T.map sA.val, T.preserves_map sA.property⟩ :=
    @Freyd.snd_pair (MapObj B) (mapCat (𝒜 := B)) mapHasBinaryProducts _ _ _ _ _
  refine ⟨⟨k, hk⟩, ?_, ?_⟩
  · -- κ ≫ ⟨k⟩ = id, by uniqueness of mediation into the T-image tabulation cone.
    apply Subtype.ext
    show κ.val ≫ k = Cat.id _
    have h1 : (κ.val ≫ k) ≫ T.map fA.val = T.map fA.val := by
      rw [Cat.assoc, hkr]
      exact congrArg Subtype.val hκf
    have h2 : (κ.val ≫ k) ≫ T.map sA.val = T.map sA.val := by
      rw [Cat.assoc, hks]
      exact congrArg Subtype.val hκs
    exact tabulation_UP_unique htab (map_comp κ.property hk) (id_is_map_local _)
      (h1.trans (Cat.id_comp _).symm) (h2.trans (Cat.id_comp _).symm)
  · -- ⟨k⟩ ≫ κ = id, by uniqueness of pairing into the downstairs product.
    have hp1 : @Cat.comp (MapObj B) (mapCat (𝒜 := B)) _ _ _
        (@Cat.comp (MapObj B) (mapCat (𝒜 := B)) _ _ _ ⟨k, hk⟩ κ) fB = fB := by
      apply Subtype.ext
      show (k ≫ κ.val) ≫ fB.val = fB.val
      rw [Cat.assoc, show κ.val ≫ fB.val = T.map fA.val from congrArg Subtype.val hκf, hkr]
    have hp2 : @Cat.comp (MapObj B) (mapCat (𝒜 := B)) _ _ _
        (@Cat.comp (MapObj B) (mapCat (𝒜 := B)) _ _ _ ⟨k, hk⟩ κ) sB = sB := by
      apply Subtype.ext
      show (k ≫ κ.val) ≫ sB.val = sB.val
      rw [Cat.assoc, show κ.val ≫ sB.val = T.map sA.val from congrArg Subtype.val hκs, hks]
    have e1 := @Freyd.pair_uniq (MapObj B) (mapCat (𝒜 := B)) mapHasBinaryProducts _ _ _
      fB sB (@Cat.comp (MapObj B) (mapCat (𝒜 := B)) _ _ _ ⟨k, hk⟩ κ) hp1 hp2
    have e2 := @Freyd.pair_uniq (MapObj B) (mapCat (𝒜 := B)) mapHasBinaryProducts _ _ _
      fB sB (@Cat.id (MapObj B) (mapCat (𝒜 := B)) _)
      (@Cat.id_comp (MapObj B) (mapCat (𝒜 := B)) _ _ fB)
      (@Cat.id_comp (MapObj B) (mapCat (𝒜 := B)) _ _ sB)
    exact e1.trans e2.symm

/-- **§2.154 (middle paragraph, packaged)**: a unitary representation of tabular unitary
    allegories restricts to a REGULAR functor `Map 𝒜 → Map ℬ`. -/
theorem mapRep_regular (hu : IsUnit (T.obj (UnitaryAllegory.unit_obj (𝒜 := A)))) :
    @RelFunctor.RegularFunctor (MapObj A) (MapObj B) (mapCat (𝒜 := A)) (mapCat (𝒜 := B))
      (mapRepFunctor T) mapRegularCategory mapRegularCategory :=
  @RelFunctor.RegularFunctor.mk (MapObj A) (MapObj B) (mapCat (𝒜 := A)) (mapCat (𝒜 := B))
    (mapRepFunctor T) mapRegularCategory mapRegularCategory
    (mapRep_pres_prod T hu) (mapRep_pres_pullback T) (mapRep_pres_covers T)
    (mapRep_pres_mono T) (mapRep_pres_image T)

end MapRep

/-! ## 4.  §2.154 third paragraph: `Rel F` is a unitary representation

  "Clearly, if T' : C₁ → C₂ is a representation of regular categories it induces a
   representation of unitary allegories Rel(C₁) → Rel(C₂)."  The allegory functor is
   §2.218's `RegularFunctor.relAllegoryHom`; here we add the UNITS clause and the
   FUNCTORIALITY of `F ↦ Rel F` (identity and composition). -/

section RelSide

/-- **§2.152/§2.154**: a TERMINATOR of `D` is a UNIT of `Rel D`.  (Generalizes
    `relUnitaryAllegory`'s designated unit `⟨1⟩` to any terminal object — the form needed
    for `Rel F`, whose value on the unit is the `F`-image of the terminator.) -/
theorem relIsUnit_of_terminal {D : Type u} [Cat.{u} D] [RegularCategory D]
    {T : D} (hT : @Freyd.Horn.IsTerminalObj D _ T) : IsUnit (⟨T⟩ : RelObj D) := by
  constructor
  · -- partial unit: both legs of any table over `T` are THE map to the terminator.
    intro x
    refine Quotient.inductionOn x (fun R => ?_)
    rw [← quotLe_iff_algLe]
    refine ⟨⟨R.colA, ?_, ?_⟩⟩
    · show R.colA ≫ Cat.id T = R.colA; rw [Cat.comp_id]
    · show R.colA ≫ Cat.id T = R.colB
      obtain ⟨f, hf⟩ := hT R.src
      rw [Cat.comp_id, hf R.colA, hf R.colB]
  · -- entireness: the graph of the terminal map.
    intro a
    obtain ⟨f, _⟩ := hT a.carrier
    exact ⟨relClass (Freyd.graph f), (relClass_graph_map f).1⟩

/-- `Rel(1_C) = 1_{Rel C}` on relation classes: the image of a span under the identity
    functor is the span itself (its pair is already monic). -/
theorem relMap_of_id {C : Type u} [Cat.{u} C] [RegularCategory C]
    (hid : @RelFunctor.RegularFunctor C C _ _ (idFunctor (𝒞 := C)) _ _)
    {a b : C} (x : BinRelQuot (𝒞 := C) a b) : hid.relMap x = x := by
  refine Quotient.inductionOn x (fun R => ?_)
  show relClass (RelFunctor.relImageObj hid R) = relClass R
  have hpair : pair ((idFunctor (𝒞 := C)).map R.colA) ((idFunctor (𝒞 := C)).map R.colB) =
      pair R.colA R.colB := rfl
  obtain ⟨e, _hcov, heA, heB⟩ := RelFunctor.relImageObj_cover hid R
  refine Quotient.sound ⟨?_, ?_⟩
  · -- image span ⊂ R : image minimality against the (monic) span of `R` itself.
    have hmono : Monic (pair R.colA R.colB) :=
      monic_pair_of_monicPair R.colA R.colB R.isMonicPair
    have hallow : Allows (Subobject.mk R.src (pair R.colA R.colB) hmono)
        (pair ((idFunctor (𝒞 := C)).map R.colA) ((idFunctor (𝒞 := C)).map R.colB)) := by
      exact ⟨Cat.id R.src, Cat.id_comp _⟩
    obtain ⟨k, hk⟩ := image_min _ _ hallow
    refine relClass_mono ⟨⟨k, ?_, ?_⟩⟩
    · show k ≫ R.colA = (image (pair ((idFunctor (𝒞 := C)).map R.colA) ((idFunctor (𝒞 := C)).map R.colB))).arr ≫ fst
      calc k ≫ R.colA = k ≫ (pair R.colA R.colB ≫ fst) := by rw [fst_pair]
        _ = (k ≫ pair R.colA R.colB) ≫ fst := (Cat.assoc _ _ _).symm
        _ = (image (pair ((idFunctor (𝒞 := C)).map R.colA) ((idFunctor (𝒞 := C)).map R.colB))).arr ≫ fst :=
              congrArg (· ≫ fst) hk
    · show k ≫ R.colB = (image (pair ((idFunctor (𝒞 := C)).map R.colA) ((idFunctor (𝒞 := C)).map R.colB))).arr ≫ snd
      calc k ≫ R.colB = k ≫ (pair R.colA R.colB ≫ snd) := by rw [snd_pair]
        _ = (k ≫ pair R.colA R.colB) ≫ snd := (Cat.assoc _ _ _).symm
        _ = (image (pair ((idFunctor (𝒞 := C)).map R.colA) ((idFunctor (𝒞 := C)).map R.colB))).arr ≫ snd :=
              congrArg (· ≫ snd) hk
  · -- R ⊂ image span : the image-lift cover carries the legs.
    exact relClass_mono ⟨⟨e, heA, heB⟩⟩

/-- `Rel(F ≫ G) = Rel(F) ≫ Rel(G)` on relation classes: the `G∘F`-image span equals the
    `G`-image span of the `F`-image span, because the `F`-image cover `e` is carried by
    `G` to a cover and precomposition with a cover does not change images. -/
theorem relMap_of_comp {C D E : Type u} [Cat.{u} C] [Cat.{u} D] [Cat.{u} E]
    [RegularCategory C] [RegularCategory D] [RegularCategory E]
    (F : Functor C D) (G : Functor D E)
    (hrF : RelFunctor.RegularFunctor F) (hrG : RelFunctor.RegularFunctor G)
    (hrGF : @RelFunctor.RegularFunctor C E _ _ (compFunctor F G) _ _)
    {a b : C} (x : BinRelQuot (𝒞 := C) a b) :
    hrGF.relMap x = hrG.relMap (hrF.relMap x) := by
  refine Quotient.inductionOn x (fun R => ?_)
  show relClass (RelFunctor.relImageObj hrGF R)
      = relClass (RelFunctor.relImageObj hrG (RelFunctor.relImageObj hrF R))
  -- the F-image cover e and the factorization of the G∘F-span through it.
  obtain ⟨e, hcov, heA, heB⟩ := RelFunctor.relImageObj_cover hrF R
  have hfac : pair ((compFunctor F G).map R.colA) ((compFunctor F G).map R.colB)
      = G.map e ≫ pair (G.map (RelFunctor.relImageObj hrF R).colA)
          (G.map (RelFunctor.relImageObj hrF R).colB) := by
    refine (pair_uniq _ _ _ ?_ ?_).symm
    · rw [Cat.assoc, fst_pair, ← G.map_comp, heA]
      rfl
    · rw [Cat.assoc, snd_pair, ← G.map_comp, heB]
      rfl
  have hGe : Cover (G.map e) := hrG.pres_covers e hcov
  have himg := image_cover_comp (G.map e)
    (pair (G.map (RelFunctor.relImageObj hrF R).colA)
      (G.map (RelFunctor.relImageObj hrF R).colB)) hGe
  have h1 : (image (pair ((compFunctor F G).map R.colA) ((compFunctor F G).map R.colB))).le
      (image (pair (G.map (RelFunctor.relImageObj hrF R).colA)
        (G.map (RelFunctor.relImageObj hrF R).colB))) := by
    rw [hfac]; exact himg.1
  have h2 : (image (pair (G.map (RelFunctor.relImageObj hrF R).colA)
        (G.map (RelFunctor.relImageObj hrF R).colB))).le
      (image (pair ((compFunctor F G).map R.colA) ((compFunctor F G).map R.colB))) := by
    rw [hfac]; exact himg.2
  refine Quotient.sound ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := h1
    refine relClass_mono ⟨⟨k, ?_, ?_⟩⟩
    · show k ≫ (_ ≫ fst) = _ ≫ fst
      rw [← Cat.assoc, hk]
    · show k ≫ (_ ≫ snd) = _ ≫ snd
      rw [← Cat.assoc, hk]
  · obtain ⟨k, hk⟩ := h2
    refine relClass_mono ⟨⟨k, ?_, ?_⟩⟩
    · show k ≫ (_ ≫ fst) = _ ≫ fst
      rw [← Cat.assoc, hk]
    · show k ≫ (_ ≫ snd) = _ ≫ snd
      rw [← Cat.assoc, hk]

end RelSide

/-! ## 5.  The two bundled categories and the functors `RelF ⊣⊢ MapF` -/

section Bundles

/-- Extensionality for `AllegoryFunctor`: equal object parts and (heterogeneously) equal
    hom parts. -/
theorem allegFunctor_ext {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    {F G : AllegoryFunctor 𝒜 ℬ} (hobj : F.obj = G.obj)
    (hmap : ∀ (a b : 𝒜) (R : a ⟶ b), HEq (F.map R) (G.map R)) : F = G := by
  obtain ⟨Fo, Fm, _, _, _, _⟩ := F
  obtain ⟨Go, Gm, _, _, _, _⟩ := G
  dsimp at hobj hmap
  subst hobj
  have hm : @Fm = @Gm := by
    funext a b R
    exact eq_of_heq (hmap a b R)
  subst hm
  rfl

/-- Terminality is preserved along an isomorphism. -/
theorem isTerm_transfer {D : Type u₁} [Cat.{v} D] {X Y : D} (hX : @Freyd.Horn.IsTerminalObj D _ X)
    (e : X ⟶ Y) (he : IsIso e) : @Freyd.Horn.IsTerminalObj D _ Y := by
  intro W
  obtain ⟨f, hf⟩ := hX W
  obtain ⟨e', _he1, he2⟩ := he
  refine ⟨f ≫ e, fun g => ?_⟩
  calc g = g ≫ Cat.id Y := (Cat.comp_id g).symm
    _ = g ≫ (e' ≫ e) := by rw [he2]
    _ = (g ≫ e') ≫ e := (Cat.assoc _ _ _).symm
    _ = f ≫ e := by rw [hf (g ≫ e')]

/-- Any two terminators are isomorphic. -/
theorem isTerm_iso {D : Type u₁} [Cat.{v} D] {X Y : D} (hX : @Freyd.Horn.IsTerminalObj D _ X)
    (hY : @Freyd.Horn.IsTerminalObj D _ Y) : ∃ e : X ⟶ Y, IsIso e := by
  obtain ⟨u, _⟩ := hY X
  obtain ⟨v, _⟩ := hX Y
  refine ⟨u, v, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hX X
    rw [hw (u ≫ v), hw (Cat.id X)]
  · obtain ⟨w, hw⟩ := hY Y
    rw [hw (v ≫ u), hw (Cat.id Y)]

/-- The chosen terminator satisfies `Horn.IsTerminalObj`. -/
theorem isTerm_one {D : Type u₁} [Cat.{v} D] [HasTerminal D] :
    @Freyd.Horn.IsTerminalObj D _ (Freyd.one (𝒞 := D)) :=
  fun Y => ⟨Freyd.term Y, fun g => Freyd.term_uniq g (Freyd.term Y)⟩

/-- **§2.154**: a SMALL REGULAR CATEGORY (bundled). -/
structure SmallRegCat : Type (u + 1) where
  carrier : Type u
  [cat : Cat.{u} carrier]
  [reg : RegularCategory carrier]

attribute [instance] SmallRegCat.cat SmallRegCat.reg

/-- **§2.154**: a SMALL UNITARY TABULAR ALLEGORY (bundled). -/
structure SmallTabAlleg : Type (u + 1) where
  carrier : Type u
  [alleg : TabularUnitaryAllegory.{u, u} carrier]

attribute [instance] SmallTabAlleg.alleg

/-- **§2.154**: a REPRESENTATION OF REGULAR CATEGORIES — a functor preserving finite
    limits (products, pullbacks, terminator) and images/covers; bundled as the repo's
    `RegularFunctor` + terminator preservation. -/
structure RegRep (C D : SmallRegCat.{u}) : Type u where
  obj : C.carrier → D.carrier
  map : {X Y : C.carrier} → (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id : ∀ X : C.carrier, map (Cat.id X) = Cat.id (obj X)
  map_comp : ∀ {X Y Z : C.carrier} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = map f ≫ map g
  regular : @RelFunctor.RegularFunctor C.carrier D.carrier C.cat D.cat
    ({ obj := obj, map := @map, map_id := map_id, map_comp := @map_comp } :
      @Functor C.carrier D.carrier C.cat D.cat) C.reg D.reg
  term : @Freyd.Horn.IsTerminalObj D.carrier D.cat (obj (Freyd.one (𝒞 := C.carrier)))

/-- The bundled functor of a `RegRep`. -/
def RegRep.functor {C D : SmallRegCat.{u}} (F : RegRep C D) :
    @Functor C.carrier D.carrier C.cat D.cat :=
  { obj := F.obj, map := @RegRep.map _ _ F, map_id := F.map_id,
    map_comp := @RegRep.map_comp _ _ F }

/-- Extensionality for `RegRep` (the two `Prop` fields are proof-irrelevant). -/
theorem RegRep.ext {C D : SmallRegCat.{u}} {F G : RegRep C D} (hobj : F.obj = G.obj)
    (hmap : ∀ (X Y : C.carrier) (f : X ⟶ Y), HEq (F.map f) (G.map f)) : F = G := by
  obtain ⟨Fo, Fm, _, _, _, _⟩ := F
  obtain ⟨Go, Gm, _, _, _, _⟩ := G
  dsimp at hobj hmap
  subst hobj
  have hm : @Fm = @Gm := by
    funext X Y f
    exact eq_of_heq (hmap X Y f)
  subst hm
  rfl

/-- **§2.154**: a (UNITARY) REPRESENTATION OF ALLEGORIES between bundled tabular unitary
    allegories: an `AllegoryFunctor` sending the unit to a unit.  (By
    `pres_isUnit_of_isUnit` it then sends EVERY unit to a unit, which is what makes these
    compose.) -/
structure UnitaryRep (𝒜 ℬ : SmallTabAlleg.{u}) : Type u where
  toFun : AllegoryFunctor 𝒜.carrier ℬ.carrier
  unit : IsUnit (toFun.obj (UnitaryAllegory.unit_obj (𝒜 := 𝒜.carrier)))

theorem UnitaryRep.ext {𝒜 ℬ : SmallTabAlleg.{u}} {F G : UnitaryRep 𝒜 ℬ}
    (h : F.toFun = G.toFun) : F = G := by
  cases F; cases G; cases h; rfl

/-- The identity representation of allegories. -/
def allegIdFun (𝒜 : Type u₁) [Allegory.{v₁} 𝒜] : AllegoryFunctor 𝒜 𝒜 where
  obj a := a
  map R := R
  map_id _ := rfl
  map_comp _ _ := rfl
  map_recip _ := rfl
  map_inter _ _ := rfl

/-- **§2.154**: the category of small regular categories (objects `SmallRegCat`,
    morphisms `RegRep`). -/
instance : Cat.{u} SmallRegCat.{u} where
  Hom := RegRep
  id C :=
    { obj := fun X => X
      map := fun f => f
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl
      regular := regularFunctor_id
      term := isTerm_one }
  comp {C D E} F G :=
    { obj := fun X => G.obj (F.obj X)
      map := fun f => G.map (F.map f)
      map_id := fun X => by rw [F.map_id, G.map_id]
      map_comp := fun f g => by rw [F.map_comp, G.map_comp]
      regular := @regularFunctor_comp C.carrier D.carrier E.carrier C.cat D.cat E.cat
        C.reg D.reg E.reg F.functor G.functor F.regular G.regular
      term := by
        obtain ⟨e, he⟩ := isTerm_iso (isTerm_one (D := D.carrier)) F.term
        exact isTerm_transfer G.term
          (G.functor.map e)
          (functor_preserves_iso (F := G.functor) e he) }
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **§2.154**: the category of small unitary tabular allegories (objects
    `SmallTabAlleg`, morphisms `UnitaryRep`). -/
instance : Cat.{u} SmallTabAlleg.{u} where
  Hom := UnitaryRep
  id 𝒜 := ⟨allegIdFun 𝒜.carrier, UnitaryAllegory.unit_prop⟩
  comp {_𝒜 _ℬ _𝒞} F G :=
    ⟨F.toFun.comp G.toFun,
     pres_isUnit_of_isUnit G.toFun UnitaryAllegory.unit_prop G.unit F.unit⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- `Rel C` of a small regular category is a small tabular unitary allegory (§2.14/§2.15
    merged into the single diamond-free class). -/
instance relTUA (𝒞 : Type u) [Cat.{u} 𝒞] [RegularCategory 𝒞] :
    TabularUnitaryAllegory.{u, u} (RelObj 𝒞) :=
  { relTabularAllegory, relUnitaryAllegory with }

/-- **§2.154**: the functor `Rel : SmallRegCat → SmallTabAlleg` on objects.
    (`@[reducible]` so that bundle-instance projections reduce during unification —
    otherwise every downstream tactic hits "synthesized instance not defeq".) -/
@[reducible] noncomputable def RelF (C : SmallRegCat.{u}) : SmallTabAlleg.{u} :=
  ⟨RelObj C.carrier⟩

/-- **§2.154**: `Rel` on morphisms — a representation of regular categories induces a
    unitary representation of allegories (§2.218's `relAllegoryHom` + the units clause
    `relIsUnit_of_terminal`). -/
noncomputable def RelF.onMap {C D : SmallRegCat.{u}} (F : RegRep C D) :
    UnitaryRep (RelF C) (RelF D) where
  toFun := @RelFunctor.RegularFunctor.relAllegoryHom C.carrier D.carrier C.cat D.cat
    F.functor C.reg D.reg F.regular
  unit := relIsUnit_of_terminal F.term

/-- **§2.154**: the functor `Map : SmallTabAlleg → SmallRegCat` on objects (`Map 𝒜` is a
    regular category, §2.15x — `mapRegularCategory`). -/
@[reducible] noncomputable def MapF (𝒜 : SmallTabAlleg.{u}) : SmallRegCat.{u} :=
  @SmallRegCat.mk (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) mapRegularCategory

/-- **§2.154**: `Map` on morphisms — a unitary representation of allegories restricts to
    a representation of regular categories (`mapRep_regular`, the middle paragraph). -/
noncomputable def MapF.onMap {𝒜 ℬ : SmallTabAlleg.{u}} (T : UnitaryRep 𝒜 ℬ) :
    RegRep (MapF 𝒜) (MapF ℬ) where
  obj := T.toFun.obj
  map := fun f => ⟨T.toFun.map f.val, T.toFun.preserves_map f.property⟩
  map_id := fun X => Subtype.ext (T.toFun.map_id X)
  map_comp := fun f g => Subtype.ext (T.toFun.map_comp f.val g.val)
  regular := mapRep_regular T.toFun T.unit
  term := mapRep_pres_term T.toFun T.unit

/-- `RelF` is functorial: identities. -/
theorem RelF.onMap_id (C : SmallRegCat.{u}) :
    RelF.onMap (@Cat.id SmallRegCat.{u} _ C) = @Cat.id SmallTabAlleg.{u} _ (RelF C) := by
  apply UnitaryRep.ext
  apply allegFunctor_ext
  · rfl
  · intro a b x
    exact heq_of_eq (relMap_of_id _ x)

/-- `RelF` is functorial: composition. -/
theorem RelF.onMap_comp {C D E : SmallRegCat.{u}} (F : RegRep C D) (G : RegRep D E) :
    RelF.onMap (@Cat.comp SmallRegCat.{u} _ C D E F G)
      = @Cat.comp SmallTabAlleg.{u} _ (RelF C) (RelF D) (RelF E)
          (RelF.onMap F) (RelF.onMap G) := by
  apply UnitaryRep.ext
  apply allegFunctor_ext
  · rfl
  · intro a b x
    exact heq_of_eq (@relMap_of_comp C.carrier D.carrier E.carrier C.cat D.cat E.cat
      C.reg D.reg E.reg F.functor G.functor
      F.regular G.regular
      (RegRep.regular (@Cat.comp SmallRegCat.{u} _ C D E F G)) a.carrier b.carrier x)

/-- **§2.154**: `Rel` as a functor `SmallRegCat → SmallTabAlleg`. -/
noncomputable def relFFunctor : Functor SmallRegCat SmallTabAlleg where
  obj := RelF
  map := RelF.onMap
  map_id := RelF.onMap_id
  map_comp := RelF.onMap_comp

/-- `MapF` is functorial — definitionally (subtype eta on the hom parts). -/
noncomputable def mapFFunctor : Functor SmallTabAlleg SmallRegCat where
  obj := MapF
  map := MapF.onMap
  map_id _ := rfl
  map_comp _ _ := rfl

end Bundles

/-! ## 6.  The roundtrip isomorphism `Rel(Map 𝒜) ≅ 𝒜` in `SmallTabAlleg` (§2.148/§2.218) -/

section CounitIso

variable (𝒜 : SmallTabAlleg.{u})

/-- `relOf` lifted to mutual-containment classes. -/
noncomputable def relOfQ {a b : MapObj 𝒜.carrier}
    (x : @BinRelQuot (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier))
      Freyd.Alg.mapHasBinaryProducts Freyd.Alg.mapHasPullbacks a b) :
    @Cat.Hom 𝒜.carrier Allegory.toCat a b :=
  Quotient.liftOn x Freyd.Alg.relOf (fun _ _ h =>
    le_antisymm (Freyd.Alg.relOf_le_of_relLe h.1) (Freyd.Alg.relOf_le_of_relLe h.2))

theorem relOfQ_relId (a : MapObj 𝒜.carrier) :
    relOfQ 𝒜 (@relId (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) mapRegularCategory a)
      = Cat.id a := by
  show Freyd.Alg.relOf (@Freyd.graph (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) a a
    (@Cat.id (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) a)) = Cat.id a
  rw [Freyd.Alg.relOf_graph]
  rfl

theorem relOfQ_comp {a b c : MapObj 𝒜.carrier}
    (x : @BinRelQuot (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier))
      Freyd.Alg.mapHasBinaryProducts Freyd.Alg.mapHasPullbacks a b)
    (y : @BinRelQuot (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier))
      Freyd.Alg.mapHasBinaryProducts Freyd.Alg.mapHasPullbacks b c) :
    relOfQ 𝒜 (@qComp (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) mapRegularCategory
        a b c x y)
      = relOfQ 𝒜 x ≫ relOfQ 𝒜 y := by
  refine Quotient.inductionOn₂ x y (fun R S => ?_)
  exact Freyd.Alg.relOf_compose R S

theorem relOfQ_recip {a b : MapObj 𝒜.carrier}
    (x : @BinRelQuot (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier))
      Freyd.Alg.mapHasBinaryProducts Freyd.Alg.mapHasPullbacks a b) :
    relOfQ 𝒜 (@qRecip (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) mapRegularCategory a b x)
      = (relOfQ 𝒜 x)° := by
  refine Quotient.inductionOn x (fun R => ?_)
  exact Freyd.Alg.relOf_reciprocal R

theorem relOfQ_inter {a b : MapObj 𝒜.carrier}
    (x y : @BinRelQuot (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier))
      Freyd.Alg.mapHasBinaryProducts Freyd.Alg.mapHasPullbacks a b) :
    relOfQ 𝒜 (@qInter (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) mapRegularCategory a b x y)
      = relOfQ 𝒜 x ∩ relOfQ 𝒜 y := by
  refine Quotient.inductionOn₂ x y (fun R S => ?_)
  exact Freyd.Alg.relOf_inter R S

/-- The §2.148/§2.218 comparison `Rel(Map 𝒜) → 𝒜` as an allegory functor. -/
noncomputable def counitFun :
    AllegoryFunctor (RelF (MapF 𝒜)).carrier 𝒜.carrier :=
  ⟨fun A => A.carrier, fun {_a _b} x => relOfQ 𝒜 x,
   fun a => relOfQ_relId 𝒜 a.carrier,
   fun {_a _b _c} x y => relOfQ_comp 𝒜 x y,
   fun {_a _b} x => relOfQ_recip 𝒜 x,
   fun {_a _b} x y => relOfQ_inter 𝒜 x y⟩

/-- **§2.148/§2.218 counit** `Rel(Map 𝒜) → 𝒜` as a morphism of `SmallTabAlleg`. -/
noncomputable def counit : UnitaryRep (RelF (MapF 𝒜)) 𝒜 where
  toFun := counitFun 𝒜
  unit := UnitaryAllegory.unit_prop (𝒜 := 𝒜.carrier)

/-- **§2.218 bridge** `𝒜 → Rel(Map 𝒜)` as a morphism of `SmallTabAlleg` (the inverse). -/
noncomputable def counitInv : UnitaryRep 𝒜 (RelF (MapF 𝒜)) where
  toFun := Freyd.bridgeFunctor 𝒜.carrier
  unit := UnitaryAllegory.unit_prop (𝒜 := (RelF (MapF 𝒜)).carrier)

theorem counitInv_comp_counit :
    @Cat.comp SmallTabAlleg.{u} _ 𝒜 (RelF (MapF 𝒜)) 𝒜 (counitInv 𝒜) (counit 𝒜)
      = @Cat.id SmallTabAlleg.{u} _ 𝒜 := by
  apply UnitaryRep.ext
  apply allegFunctor_ext
  · rfl
  · intro a b R
    exact heq_of_eq (Freyd.relOf_tabSpan 𝒜.carrier R)

theorem counit_comp_counitInv :
    @Cat.comp SmallTabAlleg.{u} _ (RelF (MapF 𝒜)) 𝒜 (RelF (MapF 𝒜))
        (counit 𝒜) (counitInv 𝒜)
      = @Cat.id SmallTabAlleg.{u} _ (RelF (MapF 𝒜)) := by
  apply UnitaryRep.ext
  apply allegFunctor_ext
  · rfl
  · intro a b m
    refine heq_of_eq ?_
    refine Quotient.inductionOn m (fun P => ?_)
    apply Quotient.sound
    constructor
    · exact Freyd.Alg.relLe_of_relOf_le (by rw [Freyd.relOf_tabSpan]; exact le_refl _)
    · exact Freyd.Alg.relLe_of_relOf_le (by rw [Freyd.relOf_tabSpan]; exact le_refl _)

/-- **§2.154**: `Rel(Map 𝒜) ≅ 𝒜` in the category of small tabular unitary allegories. -/
theorem counit_isIso : @IsIso SmallTabAlleg.{u} _ (RelF (MapF 𝒜)) 𝒜 (counit 𝒜) :=
  ⟨counitInv 𝒜, counit_comp_counitInv 𝒜, counitInv_comp_counit 𝒜⟩

end CounitIso

/-! ## 7.  The roundtrip isomorphism `C ≅ Map(Rel C)` in `SmallRegCat` (§2.148 dual/§2.217) -/

/-- Mediating-map form of the binary-product universal property makes the canonical
    comparison `pair r s` an isomorphism. -/
theorem isIso_pair_of_prodUP {D : Type u} [Cat.{u} D] [hp : HasBinaryProducts D]
    {P A B : D} {r : P ⟶ A} {s : P ⟶ B}
    (hUP : ∀ {W : D} (x : W ⟶ A) (y : W ⟶ B),
      ∃ h : W ⟶ P, h ≫ r = x ∧ h ≫ s = y ∧ ∀ h', h' ≫ r = x → h' ≫ s = y → h' = h) :
    IsIso (pair r s) := by
  obtain ⟨k, hkr, hks, _⟩ := hUP (fst (A := A) (B := B)) snd
  refine ⟨k, ?_, ?_⟩
  · obtain ⟨w, _, _, wuniq⟩ := hUP r s
    have h1 : (pair r s ≫ k) ≫ r = r := by rw [Cat.assoc, hkr, fst_pair]
    have h2 : (pair r s ≫ k) ≫ s = s := by rw [Cat.assoc, hks, snd_pair]
    rw [wuniq _ h1 h2, wuniq (Cat.id P) (Cat.id_comp r) (Cat.id_comp s)]
  · have h1 : (k ≫ pair r s) ≫ fst = fst := by rw [Cat.assoc, fst_pair, hkr]
    have h2 : (k ≫ pair r s) ≫ snd = snd := by rw [Cat.assoc, snd_pair, hks]
    rw [pair_uniq _ _ _ h1 h2]
    exact (pair_uniq fst snd (Cat.id _) (Cat.id_comp _) (Cat.id_comp _)).symm

section UnitIso

variable {C : SmallRegCat.{u}}

/-- §2.148 dual fullness, at projected objects. -/
theorem eFull {X Y : MapObj (RelObj C.carrier)}
    (m : @Cat.Hom (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier)) X Y) :
    ∃ f : X.carrier ⟶ Y.carrier, m = Freyd.embedRel f := by
  have h : ∀ {a b : C.carrier}
      (n : @Cat.Hom (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier)) ⟨a⟩ ⟨b⟩),
      ∃ f : a ⟶ b, n = Freyd.embedRel f := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2
  exact @h X.carrier Y.carrier m

/-- The inverse of the graph embedding on homs (§2.148 dual: every `Map` of `Rel C` is
    the graph of a unique morphism). -/
noncomputable def eInv {X Y : MapObj (RelObj C.carrier)}
    (m : @Cat.Hom (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier)) X Y) :
    X.carrier ⟶ Y.carrier :=
  Classical.choose (eFull m)

theorem eInv_embedRel {a b : C.carrier} (f : a ⟶ b) :
    eInv (X := ⟨a⟩) (Y := ⟨b⟩) (Freyd.embedRel f) = f :=
  Freyd.embedRel_faithful (Classical.choose_spec (eFull (Freyd.embedRel f))).symm

/-- The graph embedding `C → Map(Rel C)` as a (pinned) functor. -/
noncomputable def eFunctor (C : SmallRegCat.{u}) :
    @Functor C.carrier (MapObj (RelObj C.carrier)) C.cat (mapCat (𝒜 := RelObj C.carrier)) :=
  @Functor.mk C.carrier (MapObj (RelObj C.carrier)) C.cat (mapCat (𝒜 := RelObj C.carrier))
    (fun a => (⟨a⟩ : RelObj C.carrier))
    (fun {_a _b} f => Freyd.embedRel f)
    (fun a => Freyd.embedRel_id a)
    (fun {_a _b _c} f g => Freyd.embedRel_comp f g)

/-- `embedRel` preserves monos (full + faithful + bijective on objects). -/
theorem e_pres_mono (C : SmallRegCat.{u}) :
    @PreservesMono C.carrier C.cat (MapObj (RelObj C.carrier))
      (mapCat (𝒜 := RelObj C.carrier)) (eFunctor C) := by
  intro X Y f hf W u v huv
  obtain ⟨u', hu'⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 u
  obtain ⟨v', hv'⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 v
  have h1 : Freyd.embedRel (u' ≫ f) = Freyd.embedRel (v' ≫ f) := by
    rw [Freyd.embedRel_comp, Freyd.embedRel_comp, ← hu', ← hv']
    exact huv
  have h2 : u' = v' := hf _ _ (Freyd.embedRel_faithful h1)
  rw [hu', hv', h2]

/-- `embedRel` preserves covers. -/
theorem e_pres_covers (C : SmallRegCat.{u}) :
    @PreservesCovers C.carrier (MapObj (RelObj C.carrier)) C.cat
      (mapCat (𝒜 := RelObj C.carrier)) (eFunctor C) := by
  intro X Y f hf Q m g hm hgm
  obtain ⟨m', hm'⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 m
  obtain ⟨g', hg'⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 g
  have hfac : g' ≫ m' = f := by
    apply Freyd.embedRel_faithful
    rw [Freyd.embedRel_comp, ← hm', ← hg']
    exact hgm
  have hmono' : Monic m' := Freyd.embedRel_reflects_monic (hm' ▸ hm)
  obtain ⟨i, hi1, hi2⟩ := hf m' g' hmono' hfac
  rw [hm']
  exact ⟨Freyd.embedRel i,
    by rw [← Freyd.embedRel_comp, hi1, Freyd.embedRel_id],
    by
      rw [← Freyd.embedRel_comp, hi2, Freyd.embedRel_id]
      rfl⟩

/-- `embedRel` preserves pullbacks. -/
theorem e_pres_pullback (C : SmallRegCat.{u}) :
    @PreservesPullbacks C.carrier (MapObj (RelObj C.carrier)) C.cat
      (mapCat (𝒜 := RelObj C.carrier)) (eFunctor C) := by
  intro A B Z f g cone hpb d
  obtain ⟨p₁', hp₁⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2
    (@Cone.π₁ _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ _ _ d)
  obtain ⟨p₂', hp₂⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2
    (@Cone.π₂ _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ _ _ d)
  have hw : p₁' ≫ f = p₂' ≫ g := by
    apply Freyd.embedRel_faithful
    rw [Freyd.embedRel_comp, Freyd.embedRel_comp, ← hp₁, ← hp₂]
    exact @Cone.w _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ _ _ d
  obtain ⟨w, ⟨hw1, hw2⟩, wuniq⟩ := hpb (Cone.mk _ p₁' p₂' hw)
  refine ⟨Freyd.embedRel w, ⟨?_, ?_⟩, ?_⟩
  · show @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _
      (Freyd.embedRel w) (Freyd.embedRel cone.π₁) = _
    rw [← Freyd.embedRel_comp, hw1, ← hp₁]
  · show @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _
      (Freyd.embedRel w) (Freyd.embedRel cone.π₂) = _
    rw [← Freyd.embedRel_comp, hw2, ← hp₂]
  · intro v hv1 hv2
    obtain ⟨v', hv'⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 v
    have e1 : v' ≫ cone.π₁ = p₁' := by
      apply Freyd.embedRel_faithful
      rw [Freyd.embedRel_comp, ← hv', ← hp₁]
      exact hv1
    have e2 : v' ≫ cone.π₂ = p₂' := by
      apply Freyd.embedRel_faithful
      rw [Freyd.embedRel_comp, ← hv', ← hp₂]
      exact hv2
    rw [hv', wuniq v' e1 e2]

/-- `embedRel` preserves images. -/
theorem e_pres_image (C : SmallRegCat.{u}) :
    @PreservesImages C.carrier (MapObj (RelObj C.carrier)) C.cat
      (mapCat (𝒜 := RelObj C.carrier)) (eFunctor C)
      (e_pres_mono C) := by
  intro A B f I hI
  constructor
  · obtain ⟨k, hk⟩ := hI.1
    exact ⟨Freyd.embedRel k, by
      show @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _
        (Freyd.embedRel k) (Freyd.embedRel I.arr) = Freyd.embedRel f
      rw [← Freyd.embedRel_comp, hk]⟩
  · intro S hS
    obtain ⟨k, hk⟩ := hS
    obtain ⟨sarr', hsarr⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2
      (@Subobject.arr _ (mapCat (𝒜 := RelObj C.carrier)) _ S)
    obtain ⟨k', hk'⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 k
    have hfac : k' ≫ sarr' = f := by
      apply Freyd.embedRel_faithful
      rw [Freyd.embedRel_comp, ← hk', ← hsarr]
      exact hk
    have hmono' : Monic sarr' := Freyd.embedRel_reflects_monic
      (by rw [← hsarr]; exact @Subobject.monic _ (mapCat (𝒜 := RelObj C.carrier)) _ S)
    obtain ⟨h, hh⟩ := hI.2 (Subobject.mk _ sarr' hmono') ⟨k', hfac⟩
    refine ⟨Freyd.embedRel h, ?_⟩
    show @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _
      (Freyd.embedRel h) (@Subobject.arr _ (mapCat (𝒜 := RelObj C.carrier)) _ S)
      = Freyd.embedRel I.arr
    rw [hsarr, ← Freyd.embedRel_comp, hh]

/-- `embedRel` preserves binary products (against the tabulation-built products of
    `Map(Rel C)`). -/
theorem e_pres_prod (C : SmallRegCat.{u}) :
    @PreservesBinaryProducts C.carrier (MapObj (RelObj C.carrier)) C.cat
      (mapCat (𝒜 := RelObj C.carrier)) (eFunctor C)
      (RegularCategory.toHasBinaryProducts (𝒞 := C.carrier))
      Freyd.Alg.mapHasBinaryProducts := by
  intro A B
  refine @isIso_pair_of_prodUP (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier))
    Freyd.Alg.mapHasBinaryProducts _ _ _ _ _ ?_
  intro W x y
  obtain ⟨x', hx'⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 x
  obtain ⟨y', hy'⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 y
  refine ⟨Freyd.embedRel (pair x' y'), ?_, ?_, ?_⟩
  · show @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _
      (Freyd.embedRel (pair x' y')) (Freyd.embedRel fst) = x
    rw [← Freyd.embedRel_comp, fst_pair, ← hx']
  · show @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _
      (Freyd.embedRel (pair x' y')) (Freyd.embedRel snd) = y
    rw [← Freyd.embedRel_comp, snd_pair, ← hy']
  · intro h' h1 h2
    obtain ⟨h'', hh''⟩ := (Freyd.embedRel_cat_iso (𝒞 := C.carrier)).2 h'
    have e1 : h'' ≫ fst = x' := by
      apply Freyd.embedRel_faithful
      rw [Freyd.embedRel_comp, ← hh'', ← hx']
      exact h1
    have e2 : h'' ≫ snd = y' := by
      apply Freyd.embedRel_faithful
      rw [Freyd.embedRel_comp, ← hh'', ← hy']
      exact h2
    rw [hh'', pair_uniq x' y' h'' e1 e2]

/-- **§2.148 dual / §2.154 unit**: the graph embedding `C → Map(Rel C)` as a morphism of
    `SmallRegCat`. -/
noncomputable def unitRep (C : SmallRegCat.{u}) : RegRep C (MapF (RelF C)) where
  obj := fun a => (⟨a⟩ : RelObj C.carrier)
  map := fun f => Freyd.embedRel f
  map_id := fun a => Freyd.embedRel_id a
  map_comp := fun f g => Freyd.embedRel_comp f g
  regular :=
    @RelFunctor.RegularFunctor.mk C.carrier (MapObj (RelObj C.carrier)) C.cat
      (mapCat (𝒜 := RelObj C.carrier)) (eFunctor C)
      C.reg Freyd.Alg.mapRegularCategory
      (e_pres_prod C) (e_pres_pullback C) (e_pres_covers C) (e_pres_mono C) (e_pres_image C)
  term := fun Y =>
    ⟨@HasTerminal.trm _ (mapCat (𝒜 := RelObj C.carrier)) Freyd.Alg.mapHasTerminal Y,
     fun g => @HasTerminal.uniq _ (mapCat (𝒜 := RelObj C.carrier))
       Freyd.Alg.mapHasTerminal _ g _⟩

/-- The `Map(Rel C) → C` inverse of the graph embedding, as a (pinned) functor. -/
noncomputable def eInvFunctor (C : SmallRegCat.{u}) :
    @Functor (MapObj (RelObj C.carrier)) C.carrier (mapCat (𝒜 := RelObj C.carrier)) C.cat :=
  @Functor.mk (MapObj (RelObj C.carrier)) C.carrier (mapCat (𝒜 := RelObj C.carrier)) C.cat
    (fun X => X.carrier)
    (fun {_X _Y} m => eInv m)
    -- the `have h` restates choose_spec with the `mapCat` instance pinned, so `rw` unifies
    -- against the goal's instance instead of freshly synthesizing the wrong one
    (fun X => Freyd.embedRel_faithful
      (by have h : ∀ {X Y : MapObj (RelObj C.carrier)}
              (m : @Cat.Hom (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier)) X Y),
              Freyd.embedRel (eInv m) = m := fun m => (Classical.choose_spec (eFull m)).symm
          rw [h]; exact (Freyd.embedRel_id X.carrier).symm))
    (fun {_X _Y _Z} f g => Freyd.embedRel_faithful
      (by have h : ∀ {X Y : MapObj (RelObj C.carrier)}
              (m : @Cat.Hom (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier)) X Y),
              Freyd.embedRel (eInv m) = m := fun m => (Classical.choose_spec (eFull m)).symm
          rw [h, Freyd.embedRel_comp, h, h]))

/-- `eInv` preserves monos. -/
theorem eInv_pres_mono (C : SmallRegCat.{u}) :
    @PreservesMono (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier))
      C.carrier C.cat (eInvFunctor C) := by
  intro X Y m hm W u v huv
  have h1 : @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ (Freyd.embedRel u) m
      = @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ (Freyd.embedRel v) m := by
    have h := congrArg Freyd.embedRel huv
    rw [Freyd.embedRel_comp, Freyd.embedRel_comp,
      show Freyd.embedRel (@Functor.map _ _ (mapCat (𝒜 := RelObj C.carrier)) C.cat
        (eInvFunctor C) _ _ m) = m
        from (Classical.choose_spec (eFull m)).symm] at h
    exact h
  exact Freyd.embedRel_faithful (hm _ _ h1)

/-- `eInv` preserves covers. -/
theorem eInv_pres_covers (C : SmallRegCat.{u}) :
    @PreservesCovers (MapObj (RelObj C.carrier)) C.carrier
      (mapCat (𝒜 := RelObj C.carrier)) C.cat (eInvFunctor C) := by
  intro X Y m hcov D n g hn hgn
  have hfac : @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _
      (Freyd.embedRel g) (Freyd.embedRel n) = m := by
    rw [← Freyd.embedRel_comp, hgn]
    exact (Classical.choose_spec (eFull m)).symm
  obtain ⟨i, hi1, hi2⟩ := hcov (Freyd.embedRel n) (Freyd.embedRel g)
    (e_pres_mono C hn) hfac
  refine ⟨eInv i, ?_, ?_⟩
  · apply Freyd.embedRel_faithful
    rw [Freyd.embedRel_comp,
      show Freyd.embedRel (eInv i) = i from (Classical.choose_spec (eFull i)).symm,
      Freyd.embedRel_id]
    exact hi1
  · apply Freyd.embedRel_faithful
    rw [Freyd.embedRel_comp,
      show Freyd.embedRel (eInv i) = i from (Classical.choose_spec (eFull i)).symm,
      Freyd.embedRel_id]
    exact hi2

/-- `eInv` preserves pullbacks. -/
theorem eInv_pres_pullback (C : SmallRegCat.{u}) :
    @PreservesPullbacks (MapObj (RelObj C.carrier)) C.carrier
      (mapCat (𝒜 := RelObj C.carrier)) C.cat (eInvFunctor C) := by
  intro A B Z f g cone hpb d
  let cπ₁ := @Cone.π₁ _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ f g cone
  let cπ₂ := @Cone.π₂ _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ f g cone
  have hwE : @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _
        (Freyd.embedRel d.π₁) f
      = @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ (Freyd.embedRel d.π₂) g := by
    have h := congrArg Freyd.embedRel d.w
    rw [Freyd.embedRel_comp, Freyd.embedRel_comp,
      show Freyd.embedRel (@Functor.map _ _ (mapCat (𝒜 := RelObj C.carrier)) C.cat
        (eInvFunctor C) _ _ f) = f
        from (Classical.choose_spec (eFull f)).symm,
      show Freyd.embedRel (@Functor.map _ _ (mapCat (𝒜 := RelObj C.carrier)) C.cat
        (eInvFunctor C) _ _ g) = g
        from (Classical.choose_spec (eFull g)).symm] at h
    exact h
  obtain ⟨w, ⟨hw1, hw2⟩, wuniq⟩ := hpb
    (@Cone.mk _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ f g ⟨d.pt⟩
      (Freyd.embedRel d.π₁) (Freyd.embedRel d.π₂) hwE)
  refine ⟨eInv w, ⟨?_, ?_⟩, ?_⟩
  · have h1 : Freyd.embedRel (eInv w ≫ eInv cπ₁) = Freyd.embedRel d.π₁ := by
      rw [Freyd.embedRel_comp,
        show Freyd.embedRel (eInv w) = w from (Classical.choose_spec (eFull w)).symm,
        show Freyd.embedRel (eInv cπ₁) = cπ₁ from (Classical.choose_spec (eFull cπ₁)).symm]
      exact hw1
    exact Freyd.embedRel_faithful h1
  · have h2 : Freyd.embedRel (eInv w ≫ eInv cπ₂) = Freyd.embedRel d.π₂ := by
      rw [Freyd.embedRel_comp,
        show Freyd.embedRel (eInv w) = w from (Classical.choose_spec (eFull w)).symm,
        show Freyd.embedRel (eInv cπ₂) = cπ₂ from (Classical.choose_spec (eFull cπ₂)).symm]
      exact hw2
    exact Freyd.embedRel_faithful h2
  · intro v hv1 hv2
    have e1 : @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ (Freyd.embedRel v) cπ₁
        = Freyd.embedRel d.π₁ := by
      have h1 : Freyd.embedRel (v ≫ eInv cπ₁) = Freyd.embedRel d.π₁ :=
        congrArg Freyd.embedRel hv1
      rw [Freyd.embedRel_comp,
        show Freyd.embedRel (eInv cπ₁) = cπ₁ from (Classical.choose_spec (eFull cπ₁)).symm] at h1
      exact h1
    have e2 : @Cat.comp _ (mapCat (𝒜 := RelObj C.carrier)) _ _ _ (Freyd.embedRel v) cπ₂
        = Freyd.embedRel d.π₂ := by
      have h2 : Freyd.embedRel (v ≫ eInv cπ₂) = Freyd.embedRel d.π₂ :=
        congrArg Freyd.embedRel hv2
      rw [Freyd.embedRel_comp,
        show Freyd.embedRel (eInv cπ₂) = cπ₂ from (Classical.choose_spec (eFull cπ₂)).symm] at h2
      exact h2
    apply Freyd.embedRel_faithful
    rw [show Freyd.embedRel (eInv w) = w from (Classical.choose_spec (eFull w)).symm]
    exact wuniq (Freyd.embedRel v) e1 e2

/-- `eInv` preserves images. -/
theorem eInv_pres_image (C : SmallRegCat.{u}) :
    @PreservesImages (MapObj (RelObj C.carrier)) C.carrier
      (mapCat (𝒜 := RelObj C.carrier)) C.cat (eInvFunctor C)
      (eInv_pres_mono C) := by
  intro A B f I hI
  let iarr := @Subobject.arr _ (mapCat (𝒜 := RelObj C.carrier)) B I
  constructor
  · obtain ⟨k, hk⟩ := hI.1
    have h1 : Freyd.embedRel (eInv k ≫ eInv iarr) = Freyd.embedRel (eInv f) := by
      rw [Freyd.embedRel_comp,
        show Freyd.embedRel (eInv k) = k from (Classical.choose_spec (eFull k)).symm,
        show Freyd.embedRel (eInv iarr) = iarr from (Classical.choose_spec (eFull iarr)).symm,
        show Freyd.embedRel (eInv f) = f from (Classical.choose_spec (eFull f)).symm]
      exact hk
    exact ⟨eInv k, Freyd.embedRel_faithful h1⟩
  · intro S hS
    obtain ⟨k, hk⟩ := hS
    have hallow : @Allows _ (mapCat (𝒜 := RelObj C.carrier)) _ _
        (@Subobject.mk _ (mapCat (𝒜 := RelObj C.carrier)) B ⟨S.dom⟩
          (Freyd.embedRel S.arr) (e_pres_mono C S.monic)) f :=
      ⟨Freyd.embedRel k, by
        have h2 : Freyd.embedRel (k ≫ S.arr) = Freyd.embedRel (eInv f) :=
          congrArg Freyd.embedRel hk
        rw [Freyd.embedRel_comp,
          show Freyd.embedRel (eInv f) = f from (Classical.choose_spec (eFull f)).symm] at h2
        exact h2⟩
    obtain ⟨h, hh⟩ := hI.2 _ hallow
    have h3 : Freyd.embedRel (eInv h ≫ S.arr) = Freyd.embedRel (eInv iarr) := by
      rw [Freyd.embedRel_comp,
        show Freyd.embedRel (eInv h) = h from (Classical.choose_spec (eFull h)).symm,
        show Freyd.embedRel (eInv iarr) = iarr from (Classical.choose_spec (eFull iarr)).symm]
      exact hh
    exact ⟨eInv h, Freyd.embedRel_faithful h3⟩

/-- `eInv` preserves binary products. -/
theorem eInv_pres_prod (C : SmallRegCat.{u}) :
    @PreservesBinaryProducts (MapObj (RelObj C.carrier)) C.carrier
      (mapCat (𝒜 := RelObj C.carrier)) C.cat (eInvFunctor C)
      Freyd.Alg.mapHasBinaryProducts
      (RegularCategory.toHasBinaryProducts (𝒞 := C.carrier)) := by
  intro A B
  refine isIso_pair_of_prodUP ?_
  intro W x y
  have hEP : Freyd.embedRel (eInv (@Freyd.pair _ (mapCat (𝒜 := RelObj C.carrier))
      Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y)))
      = @Freyd.pair _ (mapCat (𝒜 := RelObj C.carrier))
          Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y) :=
    (Classical.choose_spec (eFull (@Freyd.pair _ (mapCat (𝒜 := RelObj C.carrier))
      Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y)))).symm
  have hEFst : Freyd.embedRel (eInv (@Freyd.fst _ (mapCat (𝒜 := RelObj C.carrier))
      Freyd.Alg.mapHasBinaryProducts A B))
      = @Freyd.fst _ (mapCat (𝒜 := RelObj C.carrier)) Freyd.Alg.mapHasBinaryProducts A B :=
    (Classical.choose_spec (eFull (@Freyd.fst _ (mapCat (𝒜 := RelObj C.carrier))
      Freyd.Alg.mapHasBinaryProducts A B))).symm
  have hESnd : Freyd.embedRel (eInv (@Freyd.snd _ (mapCat (𝒜 := RelObj C.carrier))
      Freyd.Alg.mapHasBinaryProducts A B))
      = @Freyd.snd _ (mapCat (𝒜 := RelObj C.carrier)) Freyd.Alg.mapHasBinaryProducts A B :=
    (Classical.choose_spec (eFull (@Freyd.snd _ (mapCat (𝒜 := RelObj C.carrier))
      Freyd.Alg.mapHasBinaryProducts A B))).symm
  refine ⟨eInv (@Freyd.pair _ (mapCat (𝒜 := RelObj C.carrier))
    Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y)), ?_, ?_, ?_⟩
  · have h1 : Freyd.embedRel (eInv (@Freyd.pair _ (mapCat (𝒜 := RelObj C.carrier))
        Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y))
          ≫ eInv (@Freyd.fst _ (mapCat (𝒜 := RelObj C.carrier))
            Freyd.Alg.mapHasBinaryProducts A B)) = Freyd.embedRel x := by
      rw [Freyd.embedRel_comp, hEP, hEFst]
      exact @Freyd.fst_pair _ (mapCat (𝒜 := RelObj C.carrier))
        Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y)
    exact Freyd.embedRel_faithful h1
  · have h2 : Freyd.embedRel (eInv (@Freyd.pair _ (mapCat (𝒜 := RelObj C.carrier))
        Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y))
          ≫ eInv (@Freyd.snd _ (mapCat (𝒜 := RelObj C.carrier))
            Freyd.Alg.mapHasBinaryProducts A B)) = Freyd.embedRel y := by
      rw [Freyd.embedRel_comp, hEP, hESnd]
      exact @Freyd.snd_pair _ (mapCat (𝒜 := RelObj C.carrier))
        Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y)
    exact Freyd.embedRel_faithful h2
  · intro h' h1 h2
    have hEh' : Freyd.embedRel h' = @Freyd.pair _ (mapCat (𝒜 := RelObj C.carrier))
        Freyd.Alg.mapHasBinaryProducts _ _ _ (Freyd.embedRel x) (Freyd.embedRel y) := by
      refine @Freyd.pair_uniq _ (mapCat (𝒜 := RelObj C.carrier))
        Freyd.Alg.mapHasBinaryProducts _ _ _ _ _ (Freyd.embedRel h') ?_ ?_
      · have e1 : Freyd.embedRel (h' ≫ eInv (@Freyd.fst _ (mapCat (𝒜 := RelObj C.carrier))
            Freyd.Alg.mapHasBinaryProducts A B)) = Freyd.embedRel x :=
          congrArg Freyd.embedRel h1
        rw [Freyd.embedRel_comp, hEFst] at e1
        exact e1
      · have e2 : Freyd.embedRel (h' ≫ eInv (@Freyd.snd _ (mapCat (𝒜 := RelObj C.carrier))
            Freyd.Alg.mapHasBinaryProducts A B)) = Freyd.embedRel y :=
          congrArg Freyd.embedRel h2
        rw [Freyd.embedRel_comp, hESnd] at e2
        exact e2
    apply Freyd.embedRel_faithful
    rw [hEP]
    exact hEh'

/-- The `Map(Rel C) → C` inverse of the graph embedding as a morphism of `SmallRegCat`. -/
noncomputable def unitInvRep (C : SmallRegCat.{u}) : RegRep (MapF (RelF C)) C where
  obj := fun X => X.carrier
  map := fun m => eInv m
  -- same pinned-instance `have h` as in `eInvFunctor` above
  map_id := fun X => Freyd.embedRel_faithful
    (by have h : ∀ {X Y : MapObj (RelObj C.carrier)}
            (m : @Cat.Hom (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier)) X Y),
            Freyd.embedRel (eInv m) = m := fun m => (Classical.choose_spec (eFull m)).symm
        rw [h]; exact (Freyd.embedRel_id X.carrier).symm)
  map_comp := fun f g => Freyd.embedRel_faithful
    (by have h : ∀ {X Y : MapObj (RelObj C.carrier)}
            (m : @Cat.Hom (MapObj (RelObj C.carrier)) (mapCat (𝒜 := RelObj C.carrier)) X Y),
            Freyd.embedRel (eInv m) = m := fun m => (Classical.choose_spec (eFull m)).symm
        rw [h, Freyd.embedRel_comp, h, h])
  regular :=
    @RelFunctor.RegularFunctor.mk (MapObj (RelObj C.carrier)) C.carrier
      (mapCat (𝒜 := RelObj C.carrier)) C.cat (eInvFunctor C)
      Freyd.Alg.mapRegularCategory C.reg
      (eInv_pres_prod C) (eInv_pres_pullback C) (eInv_pres_covers C)
      (eInv_pres_mono C) (eInv_pres_image C)
  term := isTerm_one

/-- The two directions compose to the identity of `C`. -/
theorem unit_comp_inv (C : SmallRegCat.{u}) :
    @Cat.comp SmallRegCat.{u} _ C (MapF (RelF C)) C (unitRep C) (unitInvRep C)
      = @Cat.id SmallRegCat.{u} _ C := by
  apply RegRep.ext
  · rfl
  · intro a b f
    exact heq_of_eq (eInv_embedRel f)

/-- The two directions compose to the identity of `Map(Rel C)`. -/
theorem inv_comp_unit (C : SmallRegCat.{u}) :
    @Cat.comp SmallRegCat.{u} _ (MapF (RelF C)) C (MapF (RelF C))
        (unitInvRep C) (unitRep C)
      = @Cat.id SmallRegCat.{u} _ (MapF (RelF C)) := by
  apply RegRep.ext
  · rfl
  · intro X Y m
    exact heq_of_eq (Classical.choose_spec (eFull m)).symm

/-- **§2.154**: `C ≅ Map(Rel C)` in the category of small regular categories
    (§2.148 dual / §2.217). -/
theorem unit_isIso (C : SmallRegCat.{u}) :
    @IsIso SmallRegCat.{u} _ C (MapF (RelF C)) (unitRep C) :=
  ⟨unitInvRep C, unit_comp_inv C, inv_comp_unit C⟩



end UnitIso

/-! ## 8.  Naturality and the §2.154 headline -/

/-! ### Naturality of the unit -/

/-- `Rel(F)` sends graphs to graphs: `Rel(F)[graph f] = [graph (F f)]` (§2.154). -/
theorem relMap_graph {C D : SmallRegCat.{u}} (F : RegRep C D) {a b : C.carrier} (f : a ⟶ b) :
    @RelFunctor.RegularFunctor.relMap C.carrier D.carrier C.cat D.cat F.functor
        C.reg D.reg F.regular a b (relClass (Freyd.graph f))
      = relClass (Freyd.graph (F.map f)) := by
  let I := @RelFunctor.relImageObj C.carrier D.carrier C.cat D.cat
    F.functor C.reg D.reg F.regular a b (Freyd.graph f)
  obtain ⟨e, hcov, heA, heB⟩ := @RelFunctor.relImageObj_cover C.carrier D.carrier C.cat D.cat
    F.functor C.reg D.reg F.regular a b (Freyd.graph f)
  have heA0 : e ≫ I.colA = F.map (Cat.id a) := heA
  have heB0 : e ≫ I.colB = F.map f := heB
  show relClass I = relClass (Freyd.graph (F.map f))
  have heA' : e ≫ I.colA = Cat.id (F.obj a) := by
    rw [heA0]; exact F.map_id a
  have hmono : Monic e := by
    intro W p q hpq
    have h2 : (p ≫ e) ≫ I.colA = (q ≫ e) ≫ I.colA := by rw [hpq]
    rw [Cat.assoc, Cat.assoc, heA'] at h2
    calc p = p ≫ Cat.id _ := (Cat.comp_id p).symm
      _ = q ≫ Cat.id _ := h2
      _ = q := Cat.comp_id q
  obtain ⟨e', _he1, he2⟩ := monic_cover_iso e hcov hmono
  have hIA : I.colA = e' := by
    calc I.colA = Cat.id _ ≫ I.colA := (Cat.id_comp _).symm
      _ = (e' ≫ e) ≫ I.colA := by rw [he2]
      _ = e' ≫ (e ≫ I.colA) := Cat.assoc _ _ _
      _ = e' ≫ Cat.id (F.obj a) := by rw [heA']
      _ = e' := Cat.comp_id e'
  have hIAFf : I.colA ≫ F.map f = I.colB := by
    calc I.colA ≫ F.map f = e' ≫ F.map f := by rw [hIA]
      _ = e' ≫ (e ≫ I.colB) := by rw [heB0]
      _ = (e' ≫ e) ≫ I.colB := (Cat.assoc _ _ _).symm
      _ = Cat.id _ ≫ I.colB := by rw [he2]
      _ = I.colB := Cat.id_comp _
  refine Quotient.sound ⟨?_, ?_⟩
  · -- image span ⊂ graph (F f), witness the first leg.
    exact relClass_mono ⟨⟨I.colA, Cat.comp_id _, hIAFf⟩⟩
  · -- graph (F f) ⊂ image span, witness the cover `e`.
    exact relClass_mono ⟨⟨e, heA', heB0⟩⟩

/-- Naturality core: the graph embedding intertwines `F` with `Map(Rel F)`. -/
theorem embedRel_natural {C D : SmallRegCat.{u}} (F : RegRep C D) {a b : C.carrier}
    (g : a ⟶ b) :
    (MapF.onMap (RelF.onMap F)).map (Freyd.embedRel g) = Freyd.embedRel (F.map g) :=
  Subtype.ext (relMap_graph F g)

/-- **§2.154 unit naturality**: `unitRep` is natural in `C`. -/
theorem unitRep_natural {C D : SmallRegCat.{u}} (F : RegRep C D) :
    @Cat.comp SmallRegCat.{u} _ C (MapF (RelF C)) (MapF (RelF D))
        (unitRep C) (MapF.onMap (RelF.onMap F))
      = @Cat.comp SmallRegCat.{u} _ C D (MapF (RelF D)) F (unitRep D) := by
  apply RegRep.ext
  · rfl
  · intro a b g
    exact heq_of_eq (embedRel_natural F g)

/-- **§2.154 unit-inverse naturality** (the square the `NatIso` to the identity needs). -/
theorem unitInvRep_natural {C D : SmallRegCat.{u}} (F : RegRep C D) :
    @Cat.comp SmallRegCat.{u} _ (MapF (RelF C)) (MapF (RelF D)) D
        (MapF.onMap (RelF.onMap F)) (unitInvRep D)
      = @Cat.comp SmallRegCat.{u} _ (MapF (RelF C)) C D (unitInvRep C) F := by
  apply RegRep.ext
  · rfl
  · intro X Y m
    refine heq_of_eq ?_
    apply Freyd.embedRel_faithful
    show Freyd.embedRel (eInv ((MapF.onMap (RelF.onMap F)).map m))
        = Freyd.embedRel (F.map (eInv m))
    rw [show Freyd.embedRel (eInv ((MapF.onMap (RelF.onMap F)).map m))
          = (MapF.onMap (RelF.onMap F)).map m
          from (Classical.choose_spec (eFull ((MapF.onMap (RelF.onMap F)).map m))).symm,
        ← embedRel_natural F (eInv m),
        show Freyd.embedRel (eInv m) = m from (Classical.choose_spec (eFull m)).symm]

/-! ### Naturality of the counit -/

/-- `relOf` of the `Map T`-image of a span is `T` of its `relOf` (§2.154 counit core):
    the image cover `e` is a cover-map, so `e° ≫ e = 1` and the image span's morphism
    collapses to `T(colA)° ≫ T(colB) = T(colA° ≫ colB)`. -/
theorem relOf_relImage {𝒜 ℬ : SmallTabAlleg.{u}} (T : UnitaryRep 𝒜 ℬ)
    {a b : MapObj 𝒜.carrier}
    (P : @BinRel (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) a b) :
    Freyd.Alg.relOf (@RelFunctor.relImageObj (MapObj 𝒜.carrier) (MapObj ℬ.carrier)
        (mapCat (𝒜 := 𝒜.carrier)) (mapCat (𝒜 := ℬ.carrier))
        (mapRepFunctor T.toFun) Freyd.Alg.mapRegularCategory Freyd.Alg.mapRegularCategory
        (mapRep_regular T.toFun T.unit) a b P)
      = T.toFun.map (Freyd.Alg.relOf P) := by
  let I := @RelFunctor.relImageObj (MapObj 𝒜.carrier) (MapObj ℬ.carrier)
    (mapCat (𝒜 := 𝒜.carrier)) (mapCat (𝒜 := ℬ.carrier))
    (mapRepFunctor T.toFun) Freyd.Alg.mapRegularCategory Freyd.Alg.mapRegularCategory
    (mapRep_regular T.toFun T.unit) a b P
  obtain ⟨e, hcov, heA, heB⟩ := @RelFunctor.relImageObj_cover (MapObj 𝒜.carrier)
    (MapObj ℬ.carrier) (mapCat (𝒜 := 𝒜.carrier)) (mapCat (𝒜 := ℬ.carrier))
    (mapRepFunctor T.toFun) Freyd.Alg.mapRegularCategory Freyd.Alg.mapRegularCategory
    (mapRep_regular T.toFun T.unit) a b P
  let iA := @BinRel.colA (MapObj ℬ.carrier) (mapCat (𝒜 := ℬ.carrier)) _ _ I
  let iB := @BinRel.colB (MapObj ℬ.carrier) (mapCat (𝒜 := ℬ.carrier)) _ _ I
  let pA := @BinRel.colA (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) _ _ P
  let pB := @BinRel.colB (MapObj 𝒜.carrier) (mapCat (𝒜 := 𝒜.carrier)) _ _ P
  have he : e.val° ≫ e.val = Cat.id _ := (mapCover_iff (A := ℬ.carrier) e).mp hcov
  have heAv : e.val ≫ iA.val = T.toFun.map pA.val := congrArg Subtype.val heA
  have heBv : e.val ≫ iB.val = T.toFun.map pB.val := congrArg Subtype.val heB
  show iA.val° ≫ iB.val = T.toFun.map (pA.val° ≫ pB.val)
  calc iA.val° ≫ iB.val
      = iA.val° ≫ (Cat.id _ ≫ iB.val) := by rw [Cat.id_comp]
    _ = iA.val° ≫ ((e.val° ≫ e.val) ≫ iB.val) := by rw [he]
    _ = (e.val ≫ iA.val)° ≫ (e.val ≫ iB.val) := by
        rw [Allegory.recip_comp]; simp [Cat.assoc]
    _ = (T.toFun.map pA.val)° ≫ T.toFun.map pB.val := by rw [heAv, heBv]
    _ = T.toFun.map (pA.val° ≫ pB.val) := by
        rw [T.toFun.map_comp, T.toFun.map_recip]

/-- **§2.154 counit naturality**: `counit` is natural in `𝒜`. -/
theorem counit_natural {𝒜 ℬ : SmallTabAlleg.{u}} (T : UnitaryRep 𝒜 ℬ) :
    @Cat.comp SmallTabAlleg.{u} _ (RelF (MapF 𝒜)) (RelF (MapF ℬ)) ℬ
        (RelF.onMap (MapF.onMap T)) (counit ℬ)
      = @Cat.comp SmallTabAlleg.{u} _ (RelF (MapF 𝒜)) 𝒜 ℬ (counit 𝒜) T := by
  apply UnitaryRep.ext
  apply allegFunctor_ext
  · rfl
  · intro a b x
    refine heq_of_eq ?_
    refine Quotient.inductionOn x (fun P => ?_)
    exact relOf_relImage T P

/-! ### The headline -/

/-- **§2.154, unit half**: `Map ∘ Rel` is naturally isomorphic to the identity of the
    category of small regular categories. -/
noncomputable def unitNatIso :
    NatIso (compFunctor relFFunctor mapFFunctor) idFunctor where
  nat :=
    { app := fun C => unitInvRep C
      naturality := fun {_C _D} F => unitInvRep_natural F }
  isIso := fun C => ⟨unitRep C, inv_comp_unit C, unit_comp_inv C⟩

/-- **§2.154, counit half**: `Rel ∘ Map` is naturally isomorphic to the identity of the
    category of small unitary tabular allegories. -/
noncomputable def counitNatIso :
    NatIso (compFunctor mapFFunctor relFFunctor) idFunctor where
  nat :=
    { app := fun 𝒜 => counit 𝒜
      naturality := fun {_𝒜 _ℬ} T => counit_natural T }
  isIso := fun 𝒜 => counit_isIso 𝒜

/-- **§2.154 HEADLINE**: *"The category of small regular categories is isomorphic to the
    category of small unitary tabular allegories."*

    Formalized as a STRONG EQUIVALENCE (§1.32) between the bundled categories:
    `Rel : SmallRegCat ⇄ SmallTabAlleg : Map`, with natural isomorphisms
    `Map ∘ Rel ≅ Id` (`unitNatIso`, the §2.148-dual graph embedding `C ≅ Map(Rel C)`) and
    `Rel ∘ Map ≅ Id` (`counitNatIso`, the §2.148/§2.218 tabulation bridge
    `Rel(Map 𝒜) ≅ 𝒜`).  Every component of both natural isomorphisms is an isomorphism
    whose object part is the identity up to the `RelObj` wrapper — Freyd's "isomorphic"
    modulo the change of carrier TYPE that Lean cannot quotient away. -/
noncomputable def smallRegCat_equiv_smallTabAlleg :
    StrongEquivalence relFFunctor mapFFunctor where
  unit := ⟨unitNatIso⟩
  counit := ⟨counitNatIso⟩

end Freyd.S2_154
