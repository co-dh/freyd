/-
  Freyd & Scedrov, *Categories and Allegories* §1.91  Topos structure.

  §1.911 Contravariant functor Rel(−,B); power-object [B] ↔ Rel(−,B) ≅ Hom(−,[B]).
  §1.912 Subobject classifier Ω = [1] (in Freyd.S1_9).
  §1.913 All subobjects are equalizers, covers = epics.
  §1.914 Algebraic structure of Ω: internal meet ∧ and Heyting double-arrow ⇒.
  §1.919 Monic endomorphisms of Ω are involutions.
  §1.91(10) Minimal topos definition (binary products + equalizers + subobject
            classifier, no terminator needed if non-empty).
-/

import Freyd.S1_01
import Freyd.S1_09
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_43
import Freyd.S1_45
import Freyd.S1_52


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## §1.911  The contravariant relation functor Rel(−,B)

  For any category with pullbacks and any object B, `BinRel 𝒞 − B` is a
  contravariant set-valued functor: given f : A → A' and R : BinRel 𝒞 A' B,
  define f*(R) := relPullback f R.  The functoriality equation is
  g*(f*(R)) = (f ≫ g)*(R), i.e. relPullback is contravariantly functorial.

  The existence of a power-object [B] (§1.9, `HasPowerObject B`) is equivalent
  to this functor being representable: Rel(−,B) ≅ Hom(−,[B]).
  (The formalization of `BinRel`, `relPullback`, `HasPowerObject` and
  `IsUniversalRel` is in `Freyd.S1_9`.) -/

variable [Topos 𝒞]

/-! ## §1.913  Subobjects as equalizers

  In a topos, every monic m : A' → A is the equalizer of its characteristic
  map χ_m : A → Ω and the constant-true map A → 1 → Ω.

  BECAUSE: A' → A is a pullback of t : 1 → Ω along χ_m.  In a category
  with a terminator, any pullback of a monic is an equalizer. -/

/-- **§1.913**: In a topos, each monic `m : A' → A` is the equalizer of its
    characteristic map `χ_m` and the constant-true map `A → 1 → Ω`.

    Stated as the universal property of the equalizer (a `Prop`, so the proof is
    choice-free): `m` equalizes the pair, and every `e` that equalizes factors
    uniquely through `m`.  Both parts come from the classifier pullback square
    (`classify_pullback`): `m` is the pullback of `t : 1 → Ω` along `χ_m`, and a
    pullback of `t` is exactly an equalizer of `χ_m` and `A → 1 → Ω`. -/
theorem monic_is_equalizer {A A' : 𝒞} (m : A' ⟶ A) (hm : Monic m) :
    m ≫ HasSubobjectClassifier.classify m hm
        = m ≫ (term A ≫ HasSubobjectClassifier.true)
    ∧ ∀ {E : 𝒞} (e : E ⟶ A),
        e ≫ HasSubobjectClassifier.classify m hm
          = e ≫ (term A ≫ HasSubobjectClassifier.true) →
        ∃ k : E ⟶ A', k ≫ m = e ∧ ∀ k' : E ⟶ A', k' ≫ m = e → k' = k := by
  refine ⟨?_, ?_⟩
  · -- `m` equalizes: `m ≫ χ = term A' ≫ t = (m ≫ term A) ≫ t = m ≫ (term A ≫ t)`.
    calc m ≫ HasSubobjectClassifier.classify m hm
        = term A' ≫ HasSubobjectClassifier.true := HasSubobjectClassifier.classify_sq m hm
      _ = (m ≫ term A) ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (m ≫ term A) (term A')]
      _ = m ≫ (term A ≫ HasSubobjectClassifier.true) := Cat.assoc _ _ _
  · intro E e he
    -- Turn `e` into a cone over `(χ_m, t)`: the square `E → 1 → Ω` and `E → A → Ω`.
    have hw : e ≫ HasSubobjectClassifier.classify m hm
            = term E ≫ HasSubobjectClassifier.true := by
      calc e ≫ HasSubobjectClassifier.classify m hm
          = e ≫ (term A ≫ HasSubobjectClassifier.true) := he
        _ = (e ≫ term A) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
        _ = term E ≫ HasSubobjectClassifier.true := by
              rw [term_uniq (e ≫ term A) (term E)]
    -- The classifier pullback yields a factorization `u ≫ m = e`; `m` monic gives uniqueness.
    obtain ⟨u, ⟨hu, _⟩, _⟩ :=
      HasSubobjectClassifier.classify_pullback m hm
        (⟨E, e, term E, hw⟩ : Cone (HasSubobjectClassifier.classify m hm) HasSubobjectClassifier.true)
    exact ⟨u, hu, fun k' hk' => hm k' u (hk'.trans hu.symm)⟩

/-- **§1.913 (balanced)**: A topos is BALANCED — a morphism that is both monic
    and epic is an isomorphism.  Since `m` is the equalizer of `χ_m` and
    `A → 1 → Ω` (`monic_is_equalizer`), epicness collapses `χ_m = term ≫ true`,
    so `1_B` equalizes the pair and factors through `m`, splitting it; a split
    epic mono is iso. -/
theorem topos_mono_epi_iso {A B : 𝒞} (m : A ⟶ B) (hm : Monic m)
    (hepi : ∀ {C : 𝒞} (g h : B ⟶ C), m ≫ g = m ≫ h → g = h) : IsIso m := by
  obtain ⟨heq, huniv⟩ := monic_is_equalizer m hm
  -- epic cancels `m` from `m ≫ χ = m ≫ (term ≫ true)`.
  have hχ : HasSubobjectClassifier.classify m hm = term B ≫ HasSubobjectClassifier.true :=
    hepi _ _ heq
  -- `1_B` equalizes the (now equal) pair, so it factors as `k ≫ m = 1_B`.
  obtain ⟨k, hk, _⟩ := huniv (Cat.id B) (by rw [hχ])
  refine ⟨k, ?_, hk⟩
  -- `m ≫ k = 1_A` by monic cancellation: `(m ≫ k) ≫ m = m = 1_A ≫ m`.
  exact hm _ _ (by rw [Cat.assoc, hk, Cat.comp_id, Cat.id_comp])

/-- **§1.913**: In a topos, covers coincide with epimorphisms.
    Forward: every cover is epic (`cover_epi`, general).  Converse: an epic `f`
    has an epic image-monic `(image f).arr`, which is then iso by balancedness
    (`topos_mono_epi_iso`), so `image f` is entire and `f` is a cover. -/
theorem covers_coincide_with_epis [HasImages 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    Cover f ↔ (∀ {C : 𝒞} (g h : B ⟶ C), f ≫ g = f ≫ h → g = h) := by
  constructor
  · intro hc _C g h hgh; exact cover_epi hc hgh
  · intro hepi
    rw [cover_iff_image_entire]
    -- `(image f).arr` is monic and (since `f` is epic) epic, hence iso.
    refine topos_mono_epi_iso (image f).arr (image f).monic (fun g h hgh => hepi g h ?_)
    calc f ≫ g = (image.lift f ≫ (image f).arr) ≫ g := by rw [image.lift_fac]
      _ = image.lift f ≫ ((image f).arr ≫ g) := Cat.assoc _ _ _
      _ = image.lift f ≫ ((image f).arr ≫ h) := by rw [hgh]
      _ = (image.lift f ≫ (image f).arr) ≫ h := (Cat.assoc _ _ _).symm
      _ = f ≫ h := by rw [image.lift_fac]

/-! ## §1.914  Algebraic structure of Ω

  Every n-ary operation g : Ωⁿ → Ω induces an n-ary operation on subobjects of
  any object A: given A₁,…,Aₙ ⊆ A, define g(A₁,…,Aₙ) as the subobject whose
  characteristic map is g ∘ ⟨χ_{A₁},…,χ_{Aₙ}⟩.

  **Internal meet (conjunction)**: the binary operation ∧ : Ω×Ω → Ω is defined
  as the characteristic map of the monic (t,t) : 1 → Ω×Ω.  It satisfies
  A' ⊆ g(A₁,A₂) iff A' ⊆ A₁ and A' ⊆ A₂, i.e. g(A₁,A₂) = A₁ ∩ A₂.

  **Heyting double-arrow (implication)**: the binary operation ⇒ : Ω×Ω → Ω is
  the characteristic map of the monic (1,1) : Ω → Ω×Ω (the diagonal on Ω).
  It satisfies A' ⊆ g(A₁,A₂) iff A₁ ∩ A' = A₂ ∩ A', so g is the Heyting
  double-arrow (A₁ ⇒ A₂ = A₁ ↔ A₂) and ⊆(A) has a Heyting semi-lattice
  structure.  The Heyting single-arrow is x → y := x ⇒ (x ∧ y). -/

/-- The internal meet (conjunction) on Ω: the classifying map of the monic
    (t,t) : 1 → Ω×Ω (§1.914).  The induced operation on subobjects is
    g(A₁,A₂) = A₁ ∩ A₂. -/
noncomputable def omegaMeet : prod (HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  HasSubobjectClassifier.classify
    (pair HasSubobjectClassifier.true HasSubobjectClassifier.true)
    -- pair(t,t) : 1 → Ω×Ω is monic because 1 is a terminal: any two maps W→1 are equal
    (fun f g _ => HasTerminal.uniq f g)

/-- The Heyting double-arrow on Ω: the classifying map of the diagonal
    (1,1) : Ω → Ω×Ω (§1.914).  The induced operation on subobjects A₁,A₂ ⊆ A
    is the Heyting double-arrow: A' ⊆ g(A₁,A₂) iff A₁∩A' = A₂∩A'. -/
noncomputable def heytingDoubleArrow : prod (HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  HasSubobjectClassifier.classify
    (diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
    (diag_mono _)

/-- **§1.912**: The classifier of the identity on Ω is the constant-true map:
    `classify (Cat.id Ω) _ = term Ω ≫ true`.
    Follows directly from `classify_sq (Cat.id Ω)` and `Cat.id_comp`. -/
theorem classify_id_omega :
    HasSubobjectClassifier.classify (Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
      (fun f g h => by rwa [Cat.comp_id, Cat.comp_id] at h)
    = term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  have sq := HasSubobjectClassifier.classify_sq (Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)))
    (fun f g h => by rwa [Cat.comp_id, Cat.comp_id] at h)
  rwa [Cat.id_comp] at sq

/-- **§1.912**: The classifier of the universal subobject `t : 1 → Ω` is the identity on Ω.
    Equivalently, `1 → Ω` is the pullback of `t` along `Cat.id Ω`.
    Proof: the cone `(1, t, term 1, ·)` over `(Cat.id Ω, t)` is a pullback because
    the unique lift of any cone `(E, p, q)` with `p ≫ id = q ≫ t` is `q : E → 1`. -/
theorem classify_true_eq_id :
    HasSubobjectClassifier.classify
      (HasSubobjectClassifier.true (𝒞 := 𝒞)) HasSubobjectClassifier.true_monic
    = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  symm
  refine HasSubobjectClassifier.classify_unique
      (HasSubobjectClassifier.true (𝒞 := 𝒞)) HasSubobjectClassifier.true_monic (Cat.id _) ?_ ?_
  · rw [Cat.comp_id]
    have h : term (HasTerminal.one (𝒞 := 𝒞)) = Cat.id (HasTerminal.one (𝒞 := 𝒞)) := term_uniq _ _
    rw [h, Cat.id_comp]
  · intro d
    refine ⟨d.π₂, ⟨?_, ?_⟩, fun v _ _ => term_uniq _ _⟩
    · have := d.w; rw [Cat.comp_id] at this; exact this.symm
    · exact term_uniq _ _

/-- **§1.912 (bijection, surjective half)**: `classify` is SURJECTIVE onto
    `Hom(A, Ω)` — every map `χ : A → Ω` is the characteristic map of some monic,
    namely the pullback projection `π₁ : P → A` of the universal subobject
    `t : 1 → Ω` along `χ`.

    Together with `classify_unique` (which is the injective half: two monics with
    the same `classify` are isomorphic-as-subobjects via the common pullback of
    `t`) this is the full subobject classifier bijection `Sub(A) ≅ Hom(A, Ω)`.

    Proof: `P := pullback (χ, t)`.  Its `π₁` is monic because `t` is monic
    (`mono_pullback`), the cone square gives `π₁ ≫ χ = π₂ ≫ t = term P ≫ t`
    (using `term_uniq` to replace `π₂ : P → 1` by `term P`), and that very square
    is a pullback of `t` along `χ`, so `classify_unique` forces `χ = classify π₁`. -/
theorem classify_surjective {A : 𝒞}
    (χ : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    ∃ (P : 𝒞) (m : P ⟶ A) (hm : Monic m), HasSubobjectClassifier.classify m hm = χ := by
  -- P = pullback of (χ, t); π₁ : P → A is the monic subobject classified by χ.
  let Pb := HasPullbacks.has χ HasSubobjectClassifier.true
  have hmono : Monic Pb.cone.π₁ :=
    mono_pullback χ HasSubobjectClassifier.true HasSubobjectClassifier.true_monic Pb
  refine ⟨Pb.cone.pt, Pb.cone.π₁, hmono, ?_⟩
  -- the cone square, with π₂ : P → 1 replaced by the canonical term P.
  have hsq : Pb.cone.π₁ ≫ χ = term Pb.cone.pt ≫ HasSubobjectClassifier.true := by
    rw [Pb.cone.w, term_uniq Pb.cone.π₂ (term Pb.cone.pt)]
  -- χ classifies π₁: the chosen pullback IS the classifying pullback of t along χ.
  symm
  refine HasSubobjectClassifier.classify_unique Pb.cone.π₁ hmono χ hsq ?_
  -- the square (P, π₁, term P, hsq) over (χ, t) is a pullback — same data as Pb.cone.
  intro d
  refine ⟨Pb.lift ⟨d.pt, d.π₁, d.π₂, d.w⟩, ⟨Pb.lift_fst _, term_uniq _ _⟩, ?_⟩
  intro v hv₁ _
  exact Pb.lift_uniq ⟨d.pt, d.π₁, d.π₂, d.w⟩ v hv₁ (term_uniq _ _)

/-- **§1.912 (classify naturality under pullback)**: the characteristic map of an
    inverse image `f# S` is `f ≫ χ_S`.  Equivalently, `Sub(−) ≅ Hom(−,Ω)` is
    natural: pulling a subobject back along `f` precomposes its classifier with `f`.

    Proof by pullback pasting against `classify_unique`.  The pasted square (the
    `f`-pullback square of `S.arr` stacked on the classifier square of `S`) is a
    pullback of `t` along `f ≫ χ_S`, whose left leg is `(f# S).arr = π₁`. -/
theorem classify_invImg {A B : 𝒞} (f : B ⟶ A) (S : Subobject 𝒞 A)
    (hp : HasPullback f S.arr) :
    HasSubobjectClassifier.classify (invImg f S hp).arr (invImg f S hp).monic
      = f ≫ HasSubobjectClassifier.classify S.arr S.monic := by
  let χ := HasSubobjectClassifier.classify S.arr S.monic
  show HasSubobjectClassifier.classify (invImg f S hp).arr (invImg f S hp).monic = f ≫ χ
  have sqS : S.arr ≫ χ = term S.dom ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq S.arr S.monic
  -- the pasted commuting square over (f ≫ χ, true).
  have hsq : (invImg f S hp).arr ≫ (f ≫ χ)
      = term (invImg f S hp).dom ≫ HasSubobjectClassifier.true := by
    show hp.cone.π₁ ≫ (f ≫ χ) = term hp.cone.pt ≫ HasSubobjectClassifier.true
    calc hp.cone.π₁ ≫ (f ≫ χ)
        = (hp.cone.π₁ ≫ f) ≫ χ := (Cat.assoc _ _ _).symm
      _ = (hp.cone.π₂ ≫ S.arr) ≫ χ := by rw [hp.cone.w]
      _ = hp.cone.π₂ ≫ (S.arr ≫ χ) := Cat.assoc _ _ _
      _ = hp.cone.π₂ ≫ (term S.dom ≫ HasSubobjectClassifier.true) := by rw [sqS]
      _ = (hp.cone.π₂ ≫ term S.dom) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
      _ = term hp.cone.pt ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (hp.cone.π₂ ≫ term S.dom) (term hp.cone.pt)]
  symm
  refine HasSubobjectClassifier.classify_unique (invImg f S hp).arr (invImg f S hp).monic _ hsq ?_
  intro d
  -- d : cone over (f ≫ χ, true).  (d.π₁ ≫ f, d.π₂) is a cone over (χ, true).
  have hcS : (d.π₁ ≫ f) ≫ χ = d.π₂ ≫ HasSubobjectClassifier.true := by
    rw [Cat.assoc]; exact d.w
  obtain ⟨e, ⟨he₁, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback S.arr S.monic
      ⟨d.pt, d.π₁ ≫ f, d.π₂, hcS⟩
  -- he₁ : e ≫ S.arr = d.π₁ ≫ f.  So (d.π₁, e) is a cone over (f, S.arr); lift into hp.
  have hw : d.π₁ ≫ f = e ≫ S.arr := he₁.symm
  refine ⟨hp.lift ⟨d.pt, d.π₁, e, hw⟩, ⟨hp.lift_fst _, term_uniq _ _⟩, ?_⟩
  intro v hv₁ _
  -- v ≫ π₂ = e by cancelling the monic S.arr: both compose with S.arr to d.π₁ ≫ f.
  have hv₁' : v ≫ hp.cone.π₁ = d.π₁ := hv₁
  refine hp.lift_uniq ⟨d.pt, d.π₁, e, hw⟩ v hv₁ (S.monic _ _ ?_)
  show (v ≫ hp.cone.π₂) ≫ S.arr = e ≫ S.arr
  calc (v ≫ hp.cone.π₂) ≫ S.arr
      = v ≫ (hp.cone.π₂ ≫ S.arr) := Cat.assoc _ _ _
    _ = v ≫ (hp.cone.π₁ ≫ f) := congrArg (v ≫ ·) hp.cone.w.symm
    _ = (v ≫ hp.cone.π₁) ≫ f := (Cat.assoc _ _ _).symm
    _ = d.π₁ ≫ f := congrArg (· ≫ f) hv₁'
    _ = e ≫ S.arr := hw

/-- **§1.914 (internal-meet universal property)**: the classifying map
    `⟨χ_{S₁}, χ_{S₂}⟩ ≫ omegaMeet : A → Ω` of the pair of characteristic maps
    classifies the intersection `S₁ ∩ S₂` (`Sub.inter`, §1.452).

    This is the bridge that turns the bare classifying-map definition of
    `omegaMeet` into the subobject operation `g(A₁,A₂) = A₁ ∩ A₂` (§1.914).

    Proof by pullback pasting against `classify_unique`.  The commuting square
    `inter.arr ≫ (⟨χ₁,χ₂⟩ ≫ omegaMeet) = term ≫ t` holds because along `inter.arr`
    both `χ₁` and `χ₂` collapse to `term ≫ t` (classifier squares), so
    `inter.arr ≫ ⟨χ₁,χ₂⟩ = term ≫ ⟨t,t⟩`, and `⟨t,t⟩ ≫ omegaMeet = t` by the
    classifier square of `omegaMeet`.  For the pullback property: any cone whose
    apex `E` maps by `d.π₁` with `d.π₁ ≫ ⟨χ₁,χ₂⟩ ≫ omegaMeet = term ≫ t` makes
    `⟨d.π₁≫χ₁, d.π₁≫χ₂⟩ : E → Ω×Ω` factor through `⟨t,t⟩` (the `omegaMeet`
    classifier pullback), i.e. `d.π₁ ≫ χ₁ = term ≫ t = d.π₁ ≫ χ₂`; each of these,
    via the classifier pullbacks of `χ₁`/`χ₂`, factors `d.π₁` through `m₁`/`m₂`;
    the pullback `hp` of `m₁,m₂` then yields the unique factorization through
    `inter.dom`. -/
theorem omegaMeet_classifies_inter {A : 𝒞} (S₁ S₂ : Subobject 𝒞 A)
    (hp : HasPullback S₁.arr S₂.arr) :
    pair (HasSubobjectClassifier.classify S₁.arr S₁.monic)
         (HasSubobjectClassifier.classify S₂.arr S₂.monic) ≫ omegaMeet
      = HasSubobjectClassifier.classify (Sub.inter S₁ S₂ hp).arr
          (Sub.inter S₁ S₂ hp).monic := by
  let χ₁ := HasSubobjectClassifier.classify S₁.arr S₁.monic
  let χ₂ := HasSubobjectClassifier.classify S₂.arr S₂.monic
  let I := Sub.inter S₁ S₂ hp
  show pair χ₁ χ₂ ≫ omegaMeet = HasSubobjectClassifier.classify I.arr I.monic
  -- The two classifier squares for m₁, m₂.
  have sq₁ : S₁.arr ≫ χ₁ = term S₁.dom ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq S₁.arr S₁.monic
  have sq₂ : S₂.arr ≫ χ₂ = term S₂.dom ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq S₂.arr S₂.monic
  -- omegaMeet classifier square: (t,t) ≫ omegaMeet = term 1 ≫ t = t.
  have sqM : pair HasSubobjectClassifier.true HasSubobjectClassifier.true ≫ omegaMeet
      = term (HasTerminal.one (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq
      (pair HasSubobjectClassifier.true HasSubobjectClassifier.true)
      (fun f g _ => HasTerminal.uniq f g)
  -- I.arr = hp.cone.π₁ ≫ S₁.arr; also I.arr = hp.cone.π₂ ≫ S₂.arr (cone.w).
  have hIarr₁ : I.arr = hp.cone.π₁ ≫ S₁.arr := rfl
  have hIarr₂ : I.arr = hp.cone.π₂ ≫ S₂.arr := by
    rw [hIarr₁]; exact hp.cone.w
  -- Commuting square: I.arr ≫ (⟨χ₁,χ₂⟩ ≫ omegaMeet) = term I.dom ≫ t.
  have hsq : I.arr ≫ (pair χ₁ χ₂ ≫ omegaMeet)
      = term I.dom ≫ HasSubobjectClassifier.true := by
    -- I.arr ≫ ⟨χ₁,χ₂⟩ = ⟨I.arr≫χ₁, I.arr≫χ₂⟩ = ⟨term≫t, term≫t⟩ = term ≫ ⟨t,t⟩.
    have e1 : I.arr ≫ χ₁ = term I.dom ≫ HasSubobjectClassifier.true := by
      rw [hIarr₁, Cat.assoc, sq₁, ← Cat.assoc, term_uniq (hp.cone.π₁ ≫ term S₁.dom) (term I.dom)]
    have e2 : I.arr ≫ χ₂ = term I.dom ≫ HasSubobjectClassifier.true := by
      rw [hIarr₂, Cat.assoc, sq₂, ← Cat.assoc, term_uniq (hp.cone.π₂ ≫ term S₂.dom) (term I.dom)]
    have hpair : I.arr ≫ pair χ₁ χ₂
        = term I.dom ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true := by
      have hL : I.arr ≫ pair χ₁ χ₂
          = pair (term I.dom ≫ HasSubobjectClassifier.true)
                 (term I.dom ≫ HasSubobjectClassifier.true) := by
        refine pair_uniq _ _ (I.arr ≫ pair χ₁ χ₂) ?_ ?_
        · rw [Cat.assoc, fst_pair]; exact e1
        · rw [Cat.assoc, snd_pair]; exact e2
      have hR : term I.dom ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true
          = pair (term I.dom ≫ HasSubobjectClassifier.true)
                 (term I.dom ≫ HasSubobjectClassifier.true) := by
        refine pair_uniq _ _ _ ?_ ?_
        · rw [Cat.assoc, fst_pair]
        · rw [Cat.assoc, snd_pair]
      rw [hL, hR]
    calc I.arr ≫ (pair χ₁ χ₂ ≫ omegaMeet)
        = (I.arr ≫ pair χ₁ χ₂) ≫ omegaMeet := (Cat.assoc _ _ _).symm
      _ = (term I.dom ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true) ≫ omegaMeet :=
            by rw [hpair]
      _ = term I.dom ≫ (pair HasSubobjectClassifier.true HasSubobjectClassifier.true ≫ omegaMeet) :=
            Cat.assoc _ _ _
      _ = term I.dom ≫ (term HasTerminal.one ≫ HasSubobjectClassifier.true) := by rw [sqM]
      _ = (term I.dom ≫ term HasTerminal.one) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
      _ = term I.dom ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (term I.dom ≫ term HasTerminal.one) (term I.dom)]
  -- Now show the square is a pullback, then conclude by classify_unique.
  refine HasSubobjectClassifier.classify_unique I.arr I.monic _ hsq ?_
  intro d
  -- d : Cone (⟨χ₁,χ₂⟩ ≫ omegaMeet) t, apex E = d.pt.
  -- Step A: ⟨d.π₁≫χ₁, d.π₁≫χ₂⟩ ≫ omegaMeet = term ≫ t  (from d.w).
  have hk : pair (d.π₁ ≫ χ₁) (d.π₁ ≫ χ₂) ≫ omegaMeet
      = term d.pt ≫ HasSubobjectClassifier.true := by
    have : pair (d.π₁ ≫ χ₁) (d.π₁ ≫ χ₂) = d.π₁ ≫ pair χ₁ χ₂ := by
      refine (pair_uniq _ _ _ ?_ ?_).symm <;> rw [Cat.assoc]
      · rw [fst_pair]
      · rw [snd_pair]
    rw [this, Cat.assoc, d.w, term_uniq d.π₂ (term d.pt)]
  -- Step B: factor ⟨d.π₁≫χ₁, d.π₁≫χ₂⟩ through (t,t) via omegaMeet's pullback.
  obtain ⟨w, ⟨hw₁, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback
      (pair HasSubobjectClassifier.true HasSubobjectClassifier.true)
      (fun f g _ => HasTerminal.uniq f g)
      ⟨d.pt, pair (d.π₁ ≫ χ₁) (d.π₁ ≫ χ₂), term d.pt, hk⟩
  -- hw₁ : w ≫ (t,t) = ⟨d.π₁≫χ₁, d.π₁≫χ₂⟩.  Read off the two components.
  have hcomp₁ : d.π₁ ≫ χ₁ = term d.pt ≫ HasSubobjectClassifier.true := by
    have := congrArg (· ≫ fst) hw₁
    simp only [Cat.assoc, fst_pair] at this
    rw [← this, term_uniq w (term d.pt)]
  have hcomp₂ : d.π₁ ≫ χ₂ = term d.pt ≫ HasSubobjectClassifier.true := by
    have := congrArg (· ≫ snd) hw₁
    simp only [Cat.assoc, snd_pair] at this
    rw [← this, term_uniq w (term d.pt)]
  -- Step C: each component factors d.π₁ through m₁ / m₂ (classifier pullbacks).
  obtain ⟨u₁, ⟨hu₁, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback S₁.arr S₁.monic
      ⟨d.pt, d.π₁, term d.pt, by rw [hcomp₁]⟩
  obtain ⟨u₂, ⟨hu₂, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback S₂.arr S₂.monic
      ⟨d.pt, d.π₁, term d.pt, by rw [hcomp₂]⟩
  -- hu₁ : u₁ ≫ S₁.arr = d.π₁;  hu₂ : u₂ ≫ S₂.arr = d.π₁.
  -- Step D: lift into the pullback hp to land in I.dom.
  have hpw : u₁ ≫ S₁.arr = u₂ ≫ S₂.arr := by rw [hu₁, hu₂]
  refine ⟨hp.lift ⟨d.pt, u₁, u₂, hpw⟩, ⟨?_, term_uniq _ _⟩, ?_⟩
  · -- (lift) ≫ I.arr = (lift) ≫ π₁ ≫ S₁.arr = u₁ ≫ S₁.arr = d.π₁.
    show hp.lift ⟨d.pt, u₁, u₂, hpw⟩ ≫ I.arr = d.π₁
    calc hp.lift ⟨d.pt, u₁, u₂, hpw⟩ ≫ I.arr
        = hp.lift ⟨d.pt, u₁, u₂, hpw⟩ ≫ (hp.cone.π₁ ≫ S₁.arr) := by rw [hIarr₁]
      _ = (hp.lift ⟨d.pt, u₁, u₂, hpw⟩ ≫ hp.cone.π₁) ≫ S₁.arr := (Cat.assoc _ _ _).symm
      _ = u₁ ≫ S₁.arr := by rw [hp.lift_fst]
      _ = d.π₁ := hu₁
  · -- uniqueness of the lift among maps into I.dom.
    intro v hv₁ _
    refine hp.lift_uniq ⟨d.pt, u₁, u₂, hpw⟩ v ?_ ?_
    · -- v ≫ π₁ = u₁: cancel the monic S₁.arr; (v ≫ π₁) ≫ S₁.arr = v ≫ I.arr = d.π₁ = u₁ ≫ S₁.arr.
      refine S₁.monic _ _ ?_
      rw [Cat.assoc, ← hIarr₁, hv₁, hu₁]
    · -- v ≫ π₂ = u₂: cancel the monic S₂.arr; (v ≫ π₂) ≫ S₂.arr = v ≫ I.arr = d.π₁ = u₂ ≫ S₂.arr.
      refine S₂.monic _ _ ?_
      rw [Cat.assoc, ← hIarr₂, hv₁, hu₂]

/-- **§1.914 (heyting double-arrow universal property)**: if `e : E → A` is a
    monic that EQUALIZES `χ₁, χ₂ : A → Ω` (`e ≫ χ₁ = e ≫ χ₂`) and is universal
    among such (every `k` with `k ≫ χ₁ = k ≫ χ₂` factors uniquely through `e`),
    then the classifying map `⟨χ₁,χ₂⟩ ≫ heytingDoubleArrow : A → Ω` of the pair
    classifies that subobject `e`.  This is the bridge turning the bare diagonal
    definition of `heytingDoubleArrow` into the subobject operation
    "the largest subobject on which `χ₁ = χ₂`" (equivalently `A₁ ∩ A' = A₂ ∩ A'`).

    Proof by pullback pasting against `classify_unique`, exactly parallel to
    `omegaMeet_classifies_inter`.  The commuting square holds because along `e`,
    `χ₁ = χ₂` so `e ≫ ⟨χ₁,χ₂⟩ = (e ≫ χ₁) ≫ diag`, and `diag ≫ heytingDoubleArrow
    = term ≫ true` is the diagonal's classifier square.  For the pullback: a cone
    `d` whose apex maps by `d.π₁` with the composite collapsing to `term ≫ true`
    makes `d.π₁ ≫ ⟨χ₁,χ₂⟩` factor through `diag` (diag's classifier pullback), so
    `d.π₁ ≫ χ₁ = d.π₁ ≫ χ₂`; the equalizer universal property of `e` then yields
    the unique factorization through `E`. -/
theorem heytingDoubleArrow_classifies_eq {A E : 𝒞} (χ₁ χ₂ : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (e : E ⟶ A) (he : Monic e) (heq : e ≫ χ₁ = e ≫ χ₂)
    (huniv : ∀ {W : 𝒞} (k : W ⟶ A), k ≫ χ₁ = k ≫ χ₂ →
      ∃ u : W ⟶ E, u ≫ e = k ∧ ∀ u' : W ⟶ E, u' ≫ e = k → u' = u) :
    pair χ₁ χ₂ ≫ heytingDoubleArrow = HasSubobjectClassifier.classify e he := by
  -- diagonal classifier square: diag ≫ heytingDoubleArrow = term Ω ≫ true.
  have sqD : diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ heytingDoubleArrow
      = term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq _ (diag_mono _)
  -- e ≫ ⟨χ₁,χ₂⟩ = (e ≫ χ₁) ≫ diag  (since e ≫ χ₁ = e ≫ χ₂).
  have hpairE : e ≫ pair χ₁ χ₂ = (e ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
    have hL : e ≫ pair χ₁ χ₂ = pair (e ≫ χ₁) (e ≫ χ₂) :=
      pair_uniq (e ≫ χ₁) (e ≫ χ₂) (e ≫ pair χ₁ χ₂)
        (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
    have hR : (e ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))
        = pair (e ≫ χ₁) (e ≫ χ₂) :=
      pair_uniq (e ≫ χ₁) (e ≫ χ₂) _
        (by rw [Cat.assoc,
          show diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ fst
            = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) from fst_pair _ _, Cat.comp_id])
        (by rw [Cat.assoc,
          show diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ snd
            = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) from snd_pair _ _,
          Cat.comp_id, heq])
    rw [hL, hR]
  -- Commuting square: e ≫ (⟨χ₁,χ₂⟩ ≫ heytingDoubleArrow) = term E ≫ true.
  have hsq : e ≫ (pair χ₁ χ₂ ≫ heytingDoubleArrow)
      = term E ≫ HasSubobjectClassifier.true := by
    calc e ≫ (pair χ₁ χ₂ ≫ heytingDoubleArrow)
        = (e ≫ pair χ₁ χ₂) ≫ heytingDoubleArrow := (Cat.assoc _ _ _).symm
      _ = ((e ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))) ≫ heytingDoubleArrow := by
            rw [hpairE]
      _ = (e ≫ χ₁) ≫ (diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ heytingDoubleArrow) :=
            Cat.assoc _ _ _
      _ = (e ≫ χ₁) ≫ (term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true) := by
            rw [sqD]
      _ = ((e ≫ χ₁) ≫ term (HasSubobjectClassifier.omega (𝒞 := 𝒞))) ≫ HasSubobjectClassifier.true :=
            (Cat.assoc _ _ _).symm
      _ = term E ≫ HasSubobjectClassifier.true := by
            rw [term_uniq ((e ≫ χ₁) ≫ term _) (term E)]
  refine HasSubobjectClassifier.classify_unique e he _ hsq ?_
  intro d
  -- d.π₁ ≫ (⟨χ₁,χ₂⟩ ≫ heytingDoubleArrow) = term ≫ true  (from d.w).
  have hk : (d.π₁ ≫ pair χ₁ χ₂) ≫ heytingDoubleArrow
      = term d.pt ≫ HasSubobjectClassifier.true := by
    rw [Cat.assoc, d.w, term_uniq d.π₂ (term d.pt)]
  -- factor d.π₁ ≫ ⟨χ₁,χ₂⟩ through diag via diag's classifier pullback.
  obtain ⟨w, ⟨hw₁, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback
      (diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))) (diag_mono _)
      ⟨d.pt, d.π₁ ≫ pair χ₁ χ₂, term d.pt, hk⟩
  -- hw₁ : w ≫ diag = d.π₁ ≫ ⟨χ₁,χ₂⟩.  Read off the two components → χ₁ = χ₂ along d.π₁.
  have hcomp : d.π₁ ≫ χ₁ = d.π₁ ≫ χ₂ := by
    have e1 := congrArg (· ≫ fst) hw₁
    have e2 := congrArg (· ≫ snd) hw₁
    simp only [Cat.assoc,
      show diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ fst
        = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) from fst_pair _ _,
      show diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ snd
        = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) from snd_pair _ _,
      fst_pair, snd_pair, Cat.comp_id] at e1 e2
    rw [← e1, ← e2]
  -- equalizer universal property of e factors d.π₁ through E.
  obtain ⟨u, hu, huu⟩ := huniv d.π₁ hcomp
  refine ⟨u, ⟨hu, term_uniq _ _⟩, ?_⟩
  intro v hv₁ _
  exact huu v hv₁

/-- **§1.914 (pointwise double-arrow)**: the classifying map `⟨χ₁,χ₂⟩ ≫ ⇒` is
    constantly-true along `k` exactly where `χ₁` and `χ₂` agree along `k`.  This is
    the membership form of `heytingDoubleArrow_classifies_eq` (it avoids naming an
    equalizer subobject); it is the order-form UMP feeding the Heyting laws below. -/
theorem heyting_true_iff_eq {A W : 𝒞}
    (χ₁ χ₂ : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) (k : W ⟶ A) :
    k ≫ (pair χ₁ χ₂ ≫ heytingDoubleArrow) = term W ≫ HasSubobjectClassifier.true
      ↔ k ≫ χ₁ = k ≫ χ₂ := by
  have sqD : diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ heytingDoubleArrow
      = term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq _ (diag_mono _)
  constructor
  · intro hk
    -- (k ≫ ⟨χ₁,χ₂⟩) ≫ ⇒ = term ≫ true, so it factors through diag's classifier pullback.
    have hk' : (k ≫ pair χ₁ χ₂) ≫ heytingDoubleArrow = term W ≫ HasSubobjectClassifier.true := by
      rw [Cat.assoc]; exact hk
    obtain ⟨w, ⟨hw₁, _⟩, _⟩ :=
      HasSubobjectClassifier.classify_pullback
        (diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))) (diag_mono _)
        ⟨W, k ≫ pair χ₁ χ₂, term W, hk'⟩
    -- hw₁ : w ≫ diag = k ≫ pair χ₁ χ₂.  Read off both components.
    have e1 := congrArg (· ≫ fst) hw₁
    have e2 := congrArg (· ≫ snd) hw₁
    simp only [Cat.assoc,
      show diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ fst
        = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) from fst_pair _ _,
      show diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ snd
        = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) from snd_pair _ _,
      fst_pair, snd_pair, Cat.comp_id] at e1 e2
    rw [← e1, ← e2]
  · intro heq
    -- k ≫ ⟨χ₁,χ₂⟩ = (k ≫ χ₁) ≫ diag, so postcomposing ⇒ collapses to term ≫ true.
    have hpair : k ≫ pair χ₁ χ₂ = (k ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
      have hL : k ≫ pair χ₁ χ₂ = pair (k ≫ χ₁) (k ≫ χ₂) :=
        pair_uniq (k ≫ χ₁) (k ≫ χ₂) (k ≫ pair χ₁ χ₂)
          (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
      have hR : (k ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))
          = pair (k ≫ χ₁) (k ≫ χ₂) :=
        pair_uniq (k ≫ χ₁) (k ≫ χ₂) _
          (by rw [Cat.assoc,
            show diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ fst
              = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) from fst_pair _ _, Cat.comp_id])
          (by rw [Cat.assoc,
            show diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ snd
              = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) from snd_pair _ _,
            Cat.comp_id, heq])
      rw [hL, hR]
    calc k ≫ (pair χ₁ χ₂ ≫ heytingDoubleArrow)
        = (k ≫ pair χ₁ χ₂) ≫ heytingDoubleArrow := (Cat.assoc _ _ _).symm
      _ = ((k ≫ χ₁) ≫ diag (HasSubobjectClassifier.omega (𝒞 := 𝒞))) ≫ heytingDoubleArrow := by
            rw [hpair]
      _ = (k ≫ χ₁) ≫ (diag (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ heytingDoubleArrow) :=
            Cat.assoc _ _ _
      _ = (k ≫ χ₁) ≫ (term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true) := by
            rw [sqD]
      _ = ((k ≫ χ₁) ≫ term (HasSubobjectClassifier.omega (𝒞 := 𝒞))) ≫ HasSubobjectClassifier.true :=
            (Cat.assoc _ _ _).symm
      _ = term W ≫ HasSubobjectClassifier.true := by
            rw [term_uniq ((k ≫ χ₁) ≫ term _) (term W)]

/-- **§1.914 (pointwise meet)**: the classifying map `⟨χ₁,χ₂⟩ ≫ ∧` is constantly
    true along `k` exactly where BOTH `χ₁` and `χ₂` are.  Membership form of
    `omegaMeet_classifies_inter`, proved directly from the `(t,t)` classifier
    pullback (so it needs no `HasPullback S.arr T.arr` hypothesis). -/
theorem meet_true_iff_and {A W : 𝒞}
    (χ₁ χ₂ : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) (k : W ⟶ A) :
    k ≫ (pair χ₁ χ₂ ≫ omegaMeet) = term W ≫ HasSubobjectClassifier.true
      ↔ k ≫ χ₁ = term W ≫ HasSubobjectClassifier.true
        ∧ k ≫ χ₂ = term W ≫ HasSubobjectClassifier.true := by
  have sqM : pair HasSubobjectClassifier.true HasSubobjectClassifier.true ≫ omegaMeet
      = term (HasTerminal.one (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq
      (pair HasSubobjectClassifier.true HasSubobjectClassifier.true)
      (fun f g _ => HasTerminal.uniq f g)
  constructor
  · intro hk
    have hk' : (k ≫ pair χ₁ χ₂) ≫ omegaMeet = term W ≫ HasSubobjectClassifier.true := by
      rw [Cat.assoc]; exact hk
    obtain ⟨w, ⟨hw₁, _⟩, _⟩ :=
      HasSubobjectClassifier.classify_pullback
        (pair HasSubobjectClassifier.true HasSubobjectClassifier.true)
        (fun f g _ => HasTerminal.uniq f g)
        ⟨W, k ≫ pair χ₁ χ₂, term W, hk'⟩
    -- hw₁ : w ≫ (t,t) = k ≫ ⟨χ₁,χ₂⟩.  Both components equal w ≫ t = term ≫ t.
    have e1 := congrArg (· ≫ fst) hw₁
    have e2 := congrArg (· ≫ snd) hw₁
    simp only [Cat.assoc, fst_pair, snd_pair] at e1 e2
    refine ⟨?_, ?_⟩
    · rw [← e1, term_uniq w (term W)]
    · rw [← e2, term_uniq w (term W)]
  · rintro ⟨h₁, h₂⟩
    -- k ≫ ⟨χ₁,χ₂⟩ = term ≫ (t,t), and (t,t) ≫ ∧ = term ≫ t.
    have hpair : k ≫ pair χ₁ χ₂
        = term W ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true := by
      have hL : k ≫ pair χ₁ χ₂
          = pair (term W ≫ HasSubobjectClassifier.true) (term W ≫ HasSubobjectClassifier.true) :=
        pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; exact h₁)
          (by rw [Cat.assoc, snd_pair]; exact h₂)
      have hR : term W ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true
          = pair (term W ≫ HasSubobjectClassifier.true) (term W ≫ HasSubobjectClassifier.true) :=
        pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])
      rw [hL, hR]
    calc k ≫ (pair χ₁ χ₂ ≫ omegaMeet)
        = (k ≫ pair χ₁ χ₂) ≫ omegaMeet := (Cat.assoc _ _ _).symm
      _ = (term W ≫ pair HasSubobjectClassifier.true HasSubobjectClassifier.true) ≫ omegaMeet := by
            rw [hpair]
      _ = term W ≫ (pair HasSubobjectClassifier.true HasSubobjectClassifier.true ≫ omegaMeet) :=
            Cat.assoc _ _ _
      _ = term W ≫ (term HasTerminal.one ≫ HasSubobjectClassifier.true) := by rw [sqM]
      _ = (term W ≫ term HasTerminal.one) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
      _ = term W ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (term W ≫ term HasTerminal.one) (term W)]

/-! ### §1.914  Membership/order bridge `Sub(−) ≅ Hom(−,Ω)`

  The classifier bijection turns the subobject order into classifier equations.
  These are the workhorses for the internal Heyting-algebra laws below. -/

/-- **Membership bridge**: a map `k : W → A` factors through the subobject `S`
    (`Allows S k`) iff its composite with the classifier `χ_S` is constantly true.
    This is the pointwise form of `Sub(−) ≅ Hom(−,Ω)`. -/
theorem allows_iff_classify {A W : 𝒞} (S : Subobject 𝒞 A) (k : W ⟶ A) :
    Allows S k ↔ k ≫ HasSubobjectClassifier.classify S.arr S.monic
      = term W ≫ HasSubobjectClassifier.true := by
  constructor
  · rintro ⟨u, hu⟩
    have sqS : S.arr ≫ HasSubobjectClassifier.classify S.arr S.monic
        = term S.dom ≫ HasSubobjectClassifier.true :=
      HasSubobjectClassifier.classify_sq S.arr S.monic
    calc k ≫ HasSubobjectClassifier.classify S.arr S.monic
        = (u ≫ S.arr) ≫ HasSubobjectClassifier.classify S.arr S.monic := by rw [hu]
      _ = u ≫ (S.arr ≫ HasSubobjectClassifier.classify S.arr S.monic) := Cat.assoc _ _ _
      _ = u ≫ (term S.dom ≫ HasSubobjectClassifier.true) := by rw [sqS]
      _ = (u ≫ term S.dom) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
      _ = term W ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (u ≫ term S.dom) (term W)]
  · intro hk
    obtain ⟨u, ⟨hu, _⟩, _⟩ :=
      HasSubobjectClassifier.classify_pullback S.arr S.monic ⟨W, k, term W, hk⟩
    exact ⟨u, hu⟩

/-- **Order bridge**: `S ≤ T` in `Sub(A)` iff the inclusion `S.arr` lands in `T`,
    iff `S.arr ≫ χ_T = term ≫ true`.  (Specializes `allows_iff_classify` at
    `k = S.arr`, since `Allows T S.arr` is exactly `S.le T`.) -/
theorem le_iff_classify {A : 𝒞} (S T : Subobject 𝒞 A) :
    S.le T ↔ S.arr ≫ HasSubobjectClassifier.classify T.arr T.monic
      = term S.dom ≫ HasSubobjectClassifier.true :=
  allows_iff_classify T S.arr

/-! ### §1.914  Heyting implication on `Sub(A)` and its adjunction -/

/-- The characteristic map `χ_S : A → Ω` of a subobject `S ⊆ A`. -/
noncomputable abbrev subChar {A : 𝒞} (S : Subobject 𝒞 A) :
    A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  HasSubobjectClassifier.classify S.arr S.monic

/-- The characteristic map of the Heyting implication `S ⇒ T`, à la Freyd
    (`S ⇒ T := S ⇔ (S ∧ T)`): `⟨χ_S, ⟨χ_S,χ_T⟩ ≫ ∧⟩ ≫ ⇔`. -/
noncomputable def impChar {A : 𝒞} (S T : Subobject 𝒞 A) :
    A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  pair (subChar S) (pair (subChar S) (subChar T) ≫ omegaMeet) ≫ heytingDoubleArrow

/-- The Heyting implication `S ⇒ T` as a subobject of `A`: the monic classified by
    `impChar S T` (existence via `classify_surjective`). -/
noncomputable def Sub.imp {A : 𝒞} (S T : Subobject 𝒞 A) : Subobject 𝒞 A :=
  ⟨(classify_surjective (impChar S T)).choose,
   (classify_surjective (impChar S T)).choose_spec.choose,
   (classify_surjective (impChar S T)).choose_spec.choose_spec.choose⟩

/-- `χ_{S⇒T} = impChar S T`: the implication subobject is classified by `impChar`. -/
theorem classify_imp {A : 𝒞} (S T : Subobject 𝒞 A) :
    subChar (Sub.imp S T) = impChar S T :=
  (classify_surjective (impChar S T)).choose_spec.choose_spec.choose_spec

/-- **§1.914 (⇒-adjunction, membership form)**: for every `k : W → A`,
    `k` lands in `S ⇒ T` iff `k ≫ χ_S = k ≫ (⟨χ_S,χ_T⟩ ≫ ∧)`, i.e. along `k` the
    truth of `S` coincides with the truth of `S ∧ T`.  Immediate from `classify_imp`
    and the pointwise double-arrow UMP `heyting_true_iff_eq`. -/
theorem mem_imp_iff {A W : 𝒞} (S T : Subobject 𝒞 A) (k : W ⟶ A) :
    k ≫ subChar (Sub.imp S T) = term W ≫ HasSubobjectClassifier.true
      ↔ k ≫ subChar S = k ≫ (pair (subChar S) (subChar T) ≫ omegaMeet) := by
  rw [classify_imp, impChar]
  exact heyting_true_iff_eq _ _ k

/-- **Membership is monotone**: if `S ≤ T` and `k` lands in `S`, then `k` lands in
    `T`.  (`Allows` composed with `Subobject.le`.) -/
theorem allows_mono {A W : 𝒞} {S T : Subobject 𝒞 A} (hle : S.le T) {k : W ⟶ A}
    (hk : Allows S k) : Allows T k := by
  obtain ⟨h, hh⟩ := hle; obtain ⟨u, hu⟩ := hk
  exact ⟨u ≫ h, by rw [Cat.assoc, hh, hu]⟩

/-- **Isomorphic subobjects have equal classifiers**: if `S ≤ T` and `T ≤ S` then
    `χ_S = χ_T`.  (The classifier bijection `Sub(−) ≅ Hom(−,Ω)` is well-defined on
    isomorphism classes.)  Proof: the comparison `h : S.dom → T.dom` (`h ≫ T.arr =
    S.arr`) transports `T`'s classifier pullback to a classifier pullback for `S`,
    so `classify_unique` forces `χ_T = χ_S`. -/
theorem classify_eq_of_le_le {A : 𝒞} {S T : Subobject 𝒞 A}
    (hST : S.le T) (hTS : T.le S) : subChar S = subChar T := by
  obtain ⟨h, hh⟩ := hST       -- h ≫ T.arr = S.arr
  obtain ⟨k, hk⟩ := hTS       -- k ≫ S.arr = T.arr
  -- h, k are mutually inverse (monic cancellation).
  have hkh : k ≫ h = Cat.id T.dom :=
    T.monic _ _ (by rw [Cat.assoc, hh, hk, Cat.id_comp])
  have hhk : h ≫ k = Cat.id S.dom :=
    S.monic _ _ (by rw [Cat.assoc, hk, hh, Cat.id_comp])
  -- χ_S classifies T.arr: exhibit T.arr as pullback of t along χ_S.
  refine HasSubobjectClassifier.classify_unique T.arr T.monic (subChar S) ?_ ?_
  · -- T.arr ≫ χ_S = (k ≫ S.arr) ≫ χ_S = k ≫ (term ≫ true) = term ≫ true.
    have sqS : S.arr ≫ subChar S = term S.dom ≫ HasSubobjectClassifier.true :=
      HasSubobjectClassifier.classify_sq S.arr S.monic
    calc T.arr ≫ subChar S = (k ≫ S.arr) ≫ subChar S := by rw [hk]
      _ = k ≫ (S.arr ≫ subChar S) := Cat.assoc _ _ _
      _ = k ≫ (term S.dom ≫ HasSubobjectClassifier.true) := by rw [sqS]
      _ = (k ≫ term S.dom) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
      _ = term T.dom ≫ HasSubobjectClassifier.true := by
            rw [term_uniq (k ≫ term S.dom) (term T.dom)]
  · -- pullback: transport S's classifier pullback along the iso h.
    intro d
    obtain ⟨u, ⟨hu₁, hu₂⟩, huu⟩ :=
      HasSubobjectClassifier.classify_pullback S.arr S.monic d
    -- u : d.pt → S.dom with u ≫ S.arr = d.π₁.  Then u ≫ k? no — map into T.dom via u ≫ h...
    -- wait: classify_pullback for S gives cone over (χ_S, true); d is such a cone. u≫S.arr=d.π₁.
    refine ⟨u ≫ h, ⟨?_, ?_⟩, ?_⟩
    · rw [Cat.assoc, hh]; exact hu₁
    · exact term_uniq _ _
    · intro v hv₁ _
      -- v ≫ T.arr = d.π₁ ⟹ (v ≫ k) ≫ S.arr = d.π₁, so v ≫ k = u, so v = u ≫ h.
      have hvkS : (v ≫ k) ≫ S.arr = d.π₁ := by
        calc (v ≫ k) ≫ S.arr = v ≫ (k ≫ S.arr) := Cat.assoc _ _ _
          _ = v ≫ T.arr := congrArg (v ≫ ·) hk
          _ = d.π₁ := hv₁
      have hvk : v ≫ k = u := huu (v ≫ k) hvkS (term_uniq _ _)
      calc v = v ≫ Cat.id T.dom := (Cat.comp_id v).symm
        _ = v ≫ (k ≫ h) := by rw [hkh]
        _ = (v ≫ k) ≫ h := (Cat.assoc _ _ _).symm
        _ = u ≫ h := by rw [hvk]

/-- **§1.914 (⇒-ADJUNCTION, the keystone)**: the Heyting implication is the relative
    pseudocomplement — `X ≤ (S ⇒ T)` iff `S ∩ X ≤ T`, for all `X ⊆ A`.

    Both directions reduce, via the membership/order bridges, to the pointwise
    double-arrow UMP (`mem_imp_iff`: `X ≤ S⇒T` ⟺ `χ_S` and `χ_S∧χ_T` agree along
    `X.arr`) and the meet UMP (`meet_true_iff_and`).  Forward transports the
    agreement along the inclusion `S ∩ X → A`; backward classifies the two sides
    over `X.dom` as `X#S` and `X#S ∩ X#T` and uses that `S∩X ≤ T` makes the
    canonical point of `X#S` land in `T` (hence in `X#T`). -/
theorem imp_adjunction {A : 𝒞} (S T X : Subobject 𝒞 A)
    (hp : HasPullback S.arr X.arr) :
    X.le (Sub.imp S T) ↔ (Sub.inter S X hp).le T := by
  -- Abbreviations (mathlib-free: plain `let` + `rfl` equalities).
  let χS := subChar S
  let χT := subChar T
  let M : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) := pair χS χT ≫ omegaMeet
  have hχS : χS = subChar S := rfl
  have hχT : χT = subChar T := rfl
  have hM : M = pair χS χT ≫ omegaMeet := rfl
  -- LHS via the order bridge + mem_imp_iff: X.arr ≫ χS = X.arr ≫ M.
  have hLHS : X.le (Sub.imp S T) ↔ X.arr ≫ χS = X.arr ≫ M := by
    rw [le_iff_classify]
    exact mem_imp_iff S T X.arr
  rw [hLHS]
  -- `c := (S∩X).arr`, with the two factorings c = π₁≫S.arr = π₂≫X.arr.
  let c := (Sub.inter S X hp).arr
  have hcS : c = hp.cone.π₁ ≫ S.arr := rfl
  have hcX : c = hp.cone.π₂ ≫ X.arr := hp.cone.w
  -- membership facts about c.
  have hcInS : c ≫ χS = term (Sub.inter S X hp).dom ≫ HasSubobjectClassifier.true :=
    (allows_iff_classify S c).1 ⟨hp.cone.π₁, hcS.symm⟩
  have hcInX : c ≫ subChar X = term (Sub.inter S X hp).dom ≫ HasSubobjectClassifier.true :=
    (allows_iff_classify X c).1 ⟨hp.cone.π₂, hcX.symm⟩
  constructor
  · -- FORWARD: X.arr ≫ χS = X.arr ≫ M ⟹ (S∩X) ≤ T.
    intro hagree
    rw [le_iff_classify]
    -- c ≫ M = c ≫ χS (transport hagree along π₂) = term ≫ true.
    have hcM : c ≫ M = term (Sub.inter S X hp).dom ≫ HasSubobjectClassifier.true := by
      calc c ≫ M = (hp.cone.π₂ ≫ X.arr) ≫ M := by rw [hcX]
        _ = hp.cone.π₂ ≫ (X.arr ≫ M) := Cat.assoc _ _ _
        _ = hp.cone.π₂ ≫ (X.arr ≫ χS) := by rw [hagree]
        _ = (hp.cone.π₂ ≫ X.arr) ≫ χS := (Cat.assoc _ _ _).symm
        _ = c ≫ χS := by rw [hcX]
        _ = term (Sub.inter S X hp).dom ≫ HasSubobjectClassifier.true := hcInS
    -- meet UMP: c ≫ M = term ≫ true gives c ≫ χT = term ≫ true.
    exact ((meet_true_iff_and χS χT c).1 hcM).2
  · -- BACKWARD: (S∩X) ≤ T ⟹ X.arr ≫ χS = X.arr ≫ M.
    intro hle
    -- Classify both sides over X.dom; show they classify X#S as a subobject.
    -- ρ := pullback (X.arr, S.arr); X#S has arr = ρ.π₁ : ρ.pt → X.dom.
    let ρ := HasPullbacks.has X.arr S.arr
    let XS : Subobject 𝒞 X.dom := invImg X.arr S ρ
    have hXSarr : XS.arr = ρ.cone.π₁ := rfl
    -- χ_{X#S} = X.arr ≫ χS  (classify_invImg).
    have hχXS : subChar XS = X.arr ≫ χS := classify_invImg X.arr S ρ
    -- The canonical point `p := XS.arr ≫ X.arr : XS.dom → A` lands in S∩X.
    -- p = ρ.π₁ ≫ X.arr = ρ.π₂ ≫ S.arr (ρ.cone.w), so it factors through both.
    have hwρ : ρ.cone.π₂ ≫ S.arr = ρ.cone.π₁ ≫ X.arr := ρ.cone.w.symm
    have hpt : Allows (Sub.inter S X hp) (XS.arr ≫ X.arr) := by
      refine ⟨hp.lift ⟨ρ.cone.pt, ρ.cone.π₂, ρ.cone.π₁, hwρ⟩, ?_⟩
      -- (S∩X).arr = hp.π₁ ≫ S.arr;  lift ≫ hp.π₁ = ρ.π₂.
      show hp.lift ⟨ρ.cone.pt, ρ.cone.π₂, ρ.cone.π₁, hwρ⟩ ≫ (hp.cone.π₁ ≫ S.arr)
          = XS.arr ≫ X.arr
      calc hp.lift ⟨ρ.cone.pt, ρ.cone.π₂, ρ.cone.π₁, hwρ⟩ ≫ (hp.cone.π₁ ≫ S.arr)
          = (hp.lift ⟨ρ.cone.pt, ρ.cone.π₂, ρ.cone.π₁, hwρ⟩ ≫ hp.cone.π₁) ≫ S.arr :=
            (Cat.assoc _ _ _).symm
        _ = ρ.cone.π₂ ≫ S.arr := by rw [hp.lift_fst]
        _ = ρ.cone.π₁ ≫ X.arr := hwρ
        _ = XS.arr ≫ X.arr := by rw [hXSarr]
    -- hle transports p into T, so XS ≤ X#T over X.dom.
    have hptT : Allows T (XS.arr ≫ X.arr) := allows_mono hle hpt
    -- Repackage: XS.arr ≫ (X.arr ≫ χT) = term ≫ true, i.e. `XS ≤ X#T`.
    have hXSinXT : XS.arr ≫ (X.arr ≫ χT) = term XS.dom ≫ HasSubobjectClassifier.true := by
      obtain ⟨u, hu⟩ := hptT
      have sqT : T.arr ≫ χT = term T.dom ≫ HasSubobjectClassifier.true :=
        HasSubobjectClassifier.classify_sq T.arr T.monic
      calc XS.arr ≫ (X.arr ≫ χT) = (XS.arr ≫ X.arr) ≫ χT := (Cat.assoc _ _ _).symm
        _ = (u ≫ T.arr) ≫ χT := by rw [hu]
        _ = u ≫ (T.arr ≫ χT) := Cat.assoc _ _ _
        _ = u ≫ (term T.dom ≫ HasSubobjectClassifier.true) := by rw [sqT]
        _ = (u ≫ term T.dom) ≫ HasSubobjectClassifier.true := (Cat.assoc _ _ _).symm
        _ = term XS.dom ≫ HasSubobjectClassifier.true := by
              rw [term_uniq (u ≫ term T.dom) (term XS.dom)]
    -- Goal: X.arr ≫ χS = X.arr ≫ M.  Both classify XS over X.dom; collapse via le_le.
    -- M-side over X.dom: X.arr ≫ M = pair (X.arr≫χS) (X.arr≫χT) ≫ ∧ = χ_{XS ∩ X#T}.
    let XT : Subobject 𝒞 X.dom := invImg X.arr T (HasPullbacks.has X.arr T.arr)
    have hχXT : subChar XT = X.arr ≫ χT := classify_invImg X.arr T _
    -- XS ≤ X#T (from hXSinXT) and X#T ≤ ... ; we only need XS ≤ XS∩XT and back.
    have hXS_le_XT : XS.le XT := by
      rw [le_iff_classify]
      show XS.arr ≫ subChar XT = term XS.dom ≫ HasSubobjectClassifier.true
      rw [hχXT]; exact hXSinXT
    -- Hence XS ∩ XT ≅ XS (glb + inter_le_left).
    let hpXT := HasPullbacks.has XS.arr XT.arr
    have hInterEq : (Sub.inter XS XT hpXT).le XS ∧ XS.le (Sub.inter XS XT hpXT) :=
      ⟨Sub.inter_le_left XS XT hpXT,
       Sub.inter_glb XS XT XS hpXT ⟨Cat.id XS.dom, Cat.id_comp _⟩ hXS_le_XT⟩
    have hcharInter : subChar (Sub.inter XS XT hpXT) = subChar XS :=
      classify_eq_of_le_le hInterEq.1 hInterEq.2
    -- Now: X.arr ≫ M = pair (χ_XS) (χ_XT) ≫ ∧ = χ_{XS ∩ XT} = χ_XS = X.arr ≫ χS.
    have hMpb : X.arr ≫ M = pair (subChar XS) (subChar XT) ≫ omegaMeet := by
      rw [hM]
      calc X.arr ≫ (pair χS χT ≫ omegaMeet)
          = (X.arr ≫ pair χS χT) ≫ omegaMeet := (Cat.assoc _ _ _).symm
        _ = pair (X.arr ≫ χS) (X.arr ≫ χT) ≫ omegaMeet := by
              rw [pair_uniq (X.arr ≫ χS) (X.arr ≫ χT) (X.arr ≫ pair χS χT)
                    (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])]
        _ = pair (subChar XS) (subChar XT) ≫ omegaMeet := by rw [hχXS, hχXT]
    calc X.arr ≫ χS
        = subChar XS := hχXS.symm
      _ = subChar (Sub.inter XS XT hpXT) := hcharInter.symm
      _ = pair (subChar XS) (subChar XT) ≫ omegaMeet :=
            (omegaMeet_classifies_inter XS XT hpXT).symm
      _ = X.arr ≫ M := hMpb.symm

/-! ### §1.914  The Heyting double-arrow `S ⇔ u` on `Sub(A)` and `φ³ = φ` -/

-- Subobject equality (mutual `≤`, the equivalence induced by the `Sub(A)` preorder) is
-- `Subobject.Equiv` in `Freyd.S1_51`, where `Subobject.le` is defined.


/-- **Leibniz characterization of subobject equality**: `S ≃ T` iff they have the
    same lower set (same predecessors).  This reduces equalities of Heyting terms to
    equivalences of their membership predicates `· ≤ S ↔ · ≤ T`. -/
theorem Sub.equiv_iff_forall_le {A : 𝒞} (S T : Subobject 𝒞 A) :
    Subobject.Equiv S T ↔ ∀ X : Subobject 𝒞 A, X.le S ↔ X.le T := by
  constructor
  · rintro ⟨hST, hTS⟩ X
    exact ⟨fun h => Subobject.le_trans h hST, fun h => Subobject.le_trans h hTS⟩
  · intro h
    exact ⟨(h S).1 (Subobject.le_refl S), (h T).2 (Subobject.le_refl T)⟩

/-- The Heyting double-arrow `S ⇔ u` as a subobject of `A`: the monic classified by
    `⟨χ_S, χ_u⟩ ≫ heytingDoubleArrow` (the largest subobject where `χ_S = χ_u`). -/
noncomputable def Sub.dbar {A : 𝒞} (S u : Subobject 𝒞 A) : Subobject 𝒞 A :=
  ⟨(classify_surjective (pair (subChar S) (subChar u) ≫ heytingDoubleArrow)).choose,
   (classify_surjective (pair (subChar S) (subChar u) ≫ heytingDoubleArrow)).choose_spec.choose,
   (classify_surjective (pair (subChar S) (subChar u) ≫ heytingDoubleArrow)).choose_spec.choose_spec.choose⟩

/-- `χ_{S⇔u} = ⟨χ_S,χ_u⟩ ≫ ⇔`. -/
theorem classify_dbar {A : 𝒞} (S u : Subobject 𝒞 A) :
    subChar (Sub.dbar S u) = pair (subChar S) (subChar u) ≫ heytingDoubleArrow :=
  (classify_surjective (pair (subChar S) (subChar u) ≫ heytingDoubleArrow)).choose_spec.choose_spec.choose_spec

/-- **§1.914 (double-arrow membership UMP)**: `X ≤ (S ⇔ u)` iff `χ_S` and `χ_u` agree
    along `X.arr`.  Immediate from `classify_dbar`, the order bridge, and the
    pointwise double-arrow UMP `heyting_true_iff_eq`. -/
theorem mem_dbar_iff {A : 𝒞} (S u X : Subobject 𝒞 A) :
    X.le (Sub.dbar S u) ↔ X.arr ≫ subChar S = X.arr ≫ subChar u := by
  rw [le_iff_classify]
  show X.arr ≫ subChar (Sub.dbar S u) = term X.dom ≫ HasSubobjectClassifier.true
    ↔ X.arr ≫ subChar S = X.arr ≫ subChar u
  rw [classify_dbar]
  exact heyting_true_iff_eq _ _ X.arr

/-- **§1.914 (⇔ is symmetric)**: `(S ⇔ u) ≃ (u ⇔ S)` as subobjects.  Their
    membership predicates `χ_S = χ_u` and `χ_u = χ_S` along `X.arr` coincide. -/
theorem dbar_symm {A : 𝒞} (S u : Subobject 𝒞 A) : Subobject.Equiv (Sub.dbar S u) (Sub.dbar u S) := by
  rw [Sub.equiv_iff_forall_le]
  intro X
  rw [mem_dbar_iff, mem_dbar_iff]
  exact ⟨Eq.symm, Eq.symm⟩

/-- **§1.914 (Heyting law `⊤ ⇔ c = c`)**: for any `c : W → Ω`,
    `⟨term ≫ true, c⟩ ≫ ⇔ = c`.  The double-arrow with a constantly-true first
    component is the identity.  Proof: pick a monic `m` with `c = χ_m`
    (`classify_surjective`); both `⟨t∘!,c⟩ ≫ ⇔` and `c` make `m` a pullback of `t`
    (the agreement `m≫(t∘!)=m≫c` holds because both equal `term ≫ true`), so
    `classify_unique` forces them equal. -/
theorem true_dbar {W : 𝒞} (c : W ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    pair (term W ≫ HasSubobjectClassifier.true) c ≫ heytingDoubleArrow = c := by
  obtain ⟨P, m, hm, hmc⟩ := classify_surjective c
  -- c = χ_m;  show ⟨t∘!,c⟩ ≫ ⇔ = χ_m too, via classify_unique.
  rw [← hmc]
  -- abbreviations
  let χ := HasSubobjectClassifier.classify m hm
  -- the square: m ≫ (⟨t∘!,χ⟩ ≫ ⇔) = term P ≫ true  (heyting: m≫(t∘!)=m≫χ).
  have hagm : m ≫ (term W ≫ HasSubobjectClassifier.true) = m ≫ χ := by
    have sqm : m ≫ χ = term P ≫ HasSubobjectClassifier.true :=
      HasSubobjectClassifier.classify_sq m hm
    rw [sqm, ← Cat.assoc, term_uniq (m ≫ term W) (term P)]
  have hsq : m ≫ (pair (term W ≫ HasSubobjectClassifier.true) χ ≫ heytingDoubleArrow)
      = term P ≫ HasSubobjectClassifier.true :=
    (heyting_true_iff_eq (term W ≫ HasSubobjectClassifier.true) χ m).2 hagm
  refine HasSubobjectClassifier.classify_unique m hm _ hsq ?_
  intro d
  -- d.π₁ ≫ (⟨t∘!,χ⟩≫⇔) = term ≫ true  ⟹ (heyting) d.π₁≫(t∘!)=d.π₁≫χ ⟹ d.π₁≫χ=term≫true.
  have hd : d.π₁ ≫ (pair (term W ≫ HasSubobjectClassifier.true) χ ≫ heytingDoubleArrow)
      = term d.pt ≫ HasSubobjectClassifier.true := by
    rw [d.w, term_uniq d.π₂ (term d.pt)]
  have hag : d.π₁ ≫ (term W ≫ HasSubobjectClassifier.true) = d.π₁ ≫ χ :=
    (heyting_true_iff_eq (term W ≫ HasSubobjectClassifier.true) χ d.π₁).1 hd
  have hdχ : d.π₁ ≫ χ = term d.pt ≫ HasSubobjectClassifier.true := by
    rw [← hag, ← Cat.assoc, term_uniq (d.π₁ ≫ term W) (term d.pt)]
  obtain ⟨e, ⟨he₁, _⟩, heu⟩ :=
    HasSubobjectClassifier.classify_pullback m hm ⟨d.pt, d.π₁, term d.pt, hdχ⟩
  exact ⟨e, ⟨he₁, term_uniq _ _⟩, fun v hv₁ _ => heu v hv₁ (term_uniq _ _)⟩

/-- **§1.914 (⇔ unit)**: `S ≤ ((S ⇔ u) ⇔ u)` — `s ≤ (s⇔u)⇔u`.  Along `S.arr`, `χ_S`
    is constantly true, so `S⇔u` reduces to `u` (`true_dbar`); hence `χ_{S⇔u}` and
    `χ_u` agree along `S.arr`, which is exactly `S ≤ (S⇔u)⇔u` by `mem_dbar_iff`. -/
theorem dbar_unit {A : 𝒞} (S u : Subobject 𝒞 A) : S.le (Sub.dbar (Sub.dbar S u) u) := by
  rw [mem_dbar_iff]
  -- Goal: S.arr ≫ χ_{S⇔u} = S.arr ≫ χ_u.
  rw [classify_dbar]
  -- S.arr ≫ (⟨χS,χu⟩ ≫ ⇔) = ⟨S.arr≫χS, S.arr≫χu⟩ ≫ ⇔ = ⟨term≫true, S.arr≫χu⟩ ≫ ⇔ = S.arr≫χu.
  have hSt : S.arr ≫ subChar S = term S.dom ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq S.arr S.monic
  calc S.arr ≫ (pair (subChar S) (subChar u) ≫ heytingDoubleArrow)
      = (S.arr ≫ pair (subChar S) (subChar u)) ≫ heytingDoubleArrow := (Cat.assoc _ _ _).symm
    _ = pair (S.arr ≫ subChar S) (S.arr ≫ subChar u) ≫ heytingDoubleArrow := by
          rw [pair_uniq (S.arr ≫ subChar S) (S.arr ≫ subChar u) (S.arr ≫ pair (subChar S) (subChar u))
                (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])]
    _ = pair (term S.dom ≫ HasSubobjectClassifier.true) (S.arr ≫ subChar u) ≫ heytingDoubleArrow := by
          rw [hSt]
    _ = S.arr ≫ subChar u := true_dbar (S.arr ≫ subChar u)

/-- **§1.914 (Ω-extensionality)**: two maps `χ₁ χ₂ : W → Ω` are equal iff they have
    the same `⊤`-pattern at every stage: `∀ V (k : V → W), k ≫ χ₁ = ⊤ ↔ k ≫ χ₂ = ⊤`.
    (This is the subobject-classifier `Sub(−) ≅ Hom(−,Ω)` bijection, made into a
    pointwise extensionality principle.)  It lets us prove map equalities in `Ω` by
    comparing membership predicates — the engine for the Heyting laws. -/
theorem omega_ext {W : 𝒞} (χ₁ χ₂ : W ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (h : ∀ {V : 𝒞} (k : V ⟶ W),
      k ≫ χ₁ = term V ≫ HasSubobjectClassifier.true
        ↔ k ≫ χ₂ = term V ≫ HasSubobjectClassifier.true) :
    χ₁ = χ₂ := by
  obtain ⟨P₁, m₁, hm₁, h₁⟩ := classify_surjective χ₁
  obtain ⟨P₂, m₂, hm₂, h₂⟩ := classify_surjective χ₂
  -- The two monics have the same points, so each ≤ the other; equal classifiers.
  have hsq₁ : m₁ ≫ χ₁ = term P₁ ≫ HasSubobjectClassifier.true := by
    rw [← h₁]; exact HasSubobjectClassifier.classify_sq m₁ hm₁
  have hsq₂ : m₂ ≫ χ₂ = term P₂ ≫ HasSubobjectClassifier.true := by
    rw [← h₂]; exact HasSubobjectClassifier.classify_sq m₂ hm₂
  let S₁ : Subobject 𝒞 W := ⟨P₁, m₁, hm₁⟩
  let S₂ : Subobject 𝒞 W := ⟨P₂, m₂, hm₂⟩
  have h12 : S₁.le S₂ := (allows_iff_classify S₂ m₁).2 (by
    rw [show HasSubobjectClassifier.classify S₂.arr S₂.monic = χ₂ from h₂]
    exact (h m₁).1 hsq₁)
  have h21 : S₂.le S₁ := (allows_iff_classify S₁ m₂).2 (by
    rw [show HasSubobjectClassifier.classify S₁.arr S₁.monic = χ₁ from h₁]
    exact (h m₂).2 hsq₂)
  have := classify_eq_of_le_le h12 h21
  -- subChar S₁ = χ₁, subChar S₂ = χ₂.
  rw [show subChar S₁ = χ₁ from h₁, show subChar S₂ = χ₂ from h₂] at this
  exact this

/-- **§1.914 (`c ⇔ c = ⊤`)**: `⟨c,c⟩ ≫ ⇔ = term ≫ true` — the double-arrow of a map
    with itself is constantly true (everything agrees with itself).  Immediate from
    `heyting_true_iff_eq` (the agreement `id ≫ c = id ≫ c` is trivial) and
    classifier injectivity via `omega_ext`. -/
theorem dbar_refl_top {W : 𝒞} (c : W ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    pair c c ≫ heytingDoubleArrow = term W ≫ HasSubobjectClassifier.true := by
  refine omega_ext _ _ (fun {V} k => ?_)
  rw [show k ≫ (pair c c ≫ heytingDoubleArrow)
        = k ≫ (pair c c ≫ heytingDoubleArrow) from rfl]
  constructor
  · intro _; rw [← Cat.assoc, term_uniq (k ≫ term W) (term V)]
  · intro _; exact (heyting_true_iff_eq c c k).2 rfl

/-- Precomposition distributes over the double-arrow: `k ≫ (⟨x,y⟩ ≫ ⇔)
    = ⟨k≫x, k≫y⟩ ≫ ⇔`.  (Naturality of the binary operation in the stage.) -/
theorem comp_dbar {V W : 𝒞} (k : V ⟶ W)
    (x y : W ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    k ≫ (pair x y ≫ heytingDoubleArrow)
      = pair (k ≫ x) (k ≫ y) ≫ heytingDoubleArrow := by
  rw [← Cat.assoc,
    pair_uniq (k ≫ x) (k ≫ y) (k ≫ pair x y)
      (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair])]

-- NOTE (§1.914, `φ³ = φ` residual).  The Heyting cube law
--   `Subobject.Equiv (Sub.dbar (Sub.dbar (Sub.dbar S u) u) u) (Sub.dbar S u)`
-- (with `φ S := S ⇔ u`) is the algebraic heart of §1.919.  Its EASY half
-- `φ S ≤ φ³ S` is exactly `dbar_unit (Sub.dbar S u) u` (proven).  The hard half
-- `φ³ S ≤ φ S` reduces, via `mem_dbar_iff` + `comp_dbar` on `e := (φ³S).arr` and the
-- single self-agreement `e ≫ χ_{φ²S} = e ≫ χu`, to the propositional implication
--   `((c ⇔ b) ⇔ b = b) → c = b`   (c := e≫χS, b := e≫χu).
-- That single self-agreement is NOT sufficient (in the 3-element Heyting chain with
-- `b = m` it admits `c = ⊤ ≠ b`); the genuine proof needs the FULL universal property
-- of `e` (largest subobject where `χ_{φ²S}=χu`) — equivalently the closure-operator
-- structure of `φ² = (·⇔u)⇔u` — which routes through the `⇒`-laws derived from
-- `imp_adjunction`.  Deliberately left unfinished rather than faked; the reusable
-- infra (`true_dbar`, `dbar_refl_top`, `dbar_unit`, `dbar_symm`, `omega_ext`,
-- `comp_dbar`, the ⇒-adjunction) is all Sorry-free above.

/-- **§1.919 (reduction)**: an endomorphism `h : Ω → Ω` equals the identity as
    soon as `t : 1 → Ω` is a pullback of `t` along `h` — i.e. `Ω` is "`h`-large in
    itself" (`h` classifies the maximal subobject `t : 1 → Ω`).

    Proof: the hypotheses are exactly the data making `h` the characteristic map of
    `t`, so `classify_unique` gives `h = classify t = id` (`classify_true_eq_id`). -/
theorem omega_endo_eq_id_of_classifies_true
    (h : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (hsq : HasSubobjectClassifier.true (𝒞 := 𝒞) ≫ h
      = term (HasTerminal.one (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true)
    (hpb : (Cone.mk (f := h) (g := HasSubobjectClassifier.true)
        (pt := HasTerminal.one) (π₁ := HasSubobjectClassifier.true)
        (π₂ := term HasTerminal.one) (w := hsq)).IsPullback) :
    h = Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  rw [← classify_true_eq_id]
  exact HasSubobjectClassifier.classify_unique
    (HasSubobjectClassifier.true (𝒞 := 𝒞)) HasSubobjectClassifier.true_monic h hsq hpb

/-! ### §1.919  Reusable infrastructure for the involution argument -/

/-- The maximal subobject `t : 1 ↪ Ω` of `Ω` itself (the "truth" subterminal). -/
noncomputable def topOmega : Subobject 𝒞 (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  ⟨HasTerminal.one, HasSubobjectClassifier.true, HasSubobjectClassifier.true_monic⟩

/-- `G := g⁻¹(t)` — the inverse image along `g` of the maximal subobject of `Ω`.
    This is the subobject of `Ω` "on which `g` is true"; its classifying map is `g`
    itself (`classify_invImg` + `classify_true_eq_id`). -/
noncomputable def invTrue (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) : Subobject 𝒞 (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  invImg g topOmega (HasPullbacks.has _ _)

/-- The classifying map of `G = g⁻¹(t)` is `g` itself.  (`χ_{g# ⊤} = g ≫ χ_⊤ = g ≫ id`.) -/
theorem classify_invTrue (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    HasSubobjectClassifier.classify (invTrue g).arr (invTrue g).monic = g := by
  unfold invTrue
  rw [classify_invImg]
  show g ≫ HasSubobjectClassifier.classify (topOmega).arr (topOmega).monic = g
  rw [show HasSubobjectClassifier.classify (topOmega (𝒞 := 𝒞)).arr (topOmega).monic
        = HasSubobjectClassifier.classify HasSubobjectClassifier.true
            HasSubobjectClassifier.true_monic from rfl,
      classify_true_eq_id, Cat.comp_id]

/-- **§1.919 (key monicity lemma)**: when `g` is monic, `G = g⁻¹(t)` is SUBTERMINAL
    — its domain has at most one map from any object.  Reason: for `a, b : W → G.dom`,
    both `a ≫ G.arr` and `b ≫ G.arr` compose with `g` to the constant `term ≫ true`
    (they factor through the classifier square of `g`), so `g` monic forces
    `a ≫ G.arr = b ≫ G.arr`, and `G.arr` monic forces `a = b`. -/
theorem invTrue_subterminal (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) {W : 𝒞}
    (a b : W ⟶ (invTrue g).dom) : a = b := by
  let hp : HasPullback g (topOmega (𝒞 := 𝒞)).arr := HasPullbacks.has _ _
  have hGarr : (invTrue g).arr = hp.cone.π₁ := rfl
  have htopArr : (topOmega (𝒞 := 𝒞)).arr = HasSubobjectClassifier.true := rfl
  have ha : (a ≫ (invTrue g).arr) ≫ g = term W ≫ HasSubobjectClassifier.true := by
    rw [hGarr, Cat.assoc, hp.cone.w, ← Cat.assoc, term_uniq (a ≫ hp.cone.π₂) (term W), htopArr]
  have hb : (b ≫ (invTrue g).arr) ≫ g = term W ≫ HasSubobjectClassifier.true := by
    rw [hGarr, Cat.assoc, hp.cone.w, ← Cat.assoc, term_uniq (b ≫ hp.cone.π₂) (term W), htopArr]
  exact (invTrue g).monic _ _ (hm _ _ (by rw [ha, hb]))

/-- **§1.919 (cancellation skeleton)**: a monic endomorphism `g` of `Ω` is an
    involution as soon as `g ≫ g ≫ g = g` (idempotence of `g ≫ g` up to the cube
    law): cancel the rightmost `g` by monicity.  This isolates the genuine content
    `g³ = g` from the trivial final step. -/
theorem omega_involution_of_cube (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g)
    (hcube : (g ≫ g) ≫ g = g) : g ≫ g = Cat.id _ :=
  hm (g ≫ g) (Cat.id _) (by rw [Cat.id_comp]; exact hcube)

/-- The "operation form" of `g` at the generic element (`A = Ω`, `χ = id`):
    `u₀ := term Ω ≫ (t ≫ g) : Ω → Ω` is the classifier of `ĝ(⊤_Ω) = g⁻¹(t)`. -/
noncomputable abbrev opPoint (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ (HasSubobjectClassifier.true ≫ g)

/-- **§1.919 (clean reduction — the engine).**  A monic endomorphism `g : Ω → Ω`
    is an involution AS SOON AS it has the *operation form* at the generic element:

        OPFORM:  `g = ⟨id_Ω, u₀⟩ ≫ ⇔`,  where  `u₀ := term_Ω ≫ (t ≫ g)`.

    This is Freyd's `ĝ(S) = (S ⇔ A×U)` (with `V = 1`) read at `A = Ω, S = id_Ω`,
    i.e. `ĝ(⊤_Ω) = G = g⁻¹(t)`, whose classifier is `g` (`classify_invTrue`).

    Given OPFORM the involution `g ≫ g = id` is PURE and needs **no Boolean fact**:
    by `comp_dbar` (naturality of `⇔` in the stage) and `g ≫ u₀ = u₀`,
    `g ≫ g = ⟨g, u₀⟩ ≫ ⇔`, and `omega_ext` reduces `⟨g, u₀⟩ ≫ ⇔ = id` to the
    pointwise iff `k ≫ g = k ≫ u₀ ↔ k = ⊤` (via `heyting_true_iff_eq`).  The
    backward leg is a substitution; the forward leg is EXACTLY `Monic g`
    (`k ≫ g = (term ≫ t) ≫ g ⟹ k = term ≫ t`).  No `(S⇔u)⇔u = S`.

    Thus the entire §1.919 content is concentrated in OPFORM — the operation
    pinning of Freyd's `U,V` construction. -/
theorem omega_involution_of_opForm (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g)
    (hOp : g = pair (Cat.id (HasSubobjectClassifier.omega (𝒞 := 𝒞))) (opPoint g)
              ≫ heytingDoubleArrow) :
    g ≫ g = Cat.id _ := by
  -- `g ≫ u₀ = u₀` (terminality absorbs `g ≫ term`).
  have hgu : g ≫ opPoint g = opPoint g := by
    show g ≫ (term _ ≫ _) = term _ ≫ _
    rw [← Cat.assoc, term_uniq (g ≫ term _) (term _)]
  -- `g ≫ g = ⟨g, u₀⟩ ≫ ⇔` by substituting OPFORM into the *left* factor and
  -- pushing `g ≫ (-)` through `⇔` (comp_dbar).
  have hgg : g ≫ g = pair g (opPoint g) ≫ heytingDoubleArrow :=
    calc g ≫ g
        = g ≫ (pair (Cat.id _) (opPoint g) ≫ heytingDoubleArrow) := congrArg (g ≫ ·) hOp
      _ = pair (g ≫ Cat.id _) (g ≫ opPoint g) ≫ heytingDoubleArrow := comp_dbar _ _ _
      _ = pair g (opPoint g) ≫ heytingDoubleArrow := by rw [Cat.comp_id, hgu]
  -- Now `⟨g, u₀⟩ ≫ ⇔ = id` by Ω-extensionality.
  rw [hgg]
  refine omega_ext _ _ (fun {V} k => ?_)
  rw [Cat.comp_id, heyting_true_iff_eq]
  constructor
  · -- forward: `k ≫ g = k ≫ u₀` ⟹ `k = ⊤`, by Monic g.
    intro hk
    -- `k ≫ u₀ = (term V ≫ t) ≫ g`  (terminality: `k ≫ term Ω = term V`).
    have hku : k ≫ opPoint g = (term V ≫ HasSubobjectClassifier.true) ≫ g := by
      show k ≫ (term _ ≫ _) = (term V ≫ _) ≫ g
      rw [← Cat.assoc, ← Cat.assoc, term_uniq (k ≫ term _) (term V)]
    rw [hku] at hk
    exact hm k (term V ≫ HasSubobjectClassifier.true) hk
  · -- backward: `k = ⊤` ⟹ `k ≫ g = k ≫ u₀`, by substitution.
    intro hk
    have hku : k ≫ opPoint g = (term V ≫ HasSubobjectClassifier.true) ≫ g := by
      show k ≫ (term _ ≫ _) = (term V ≫ _) ≫ g
      rw [← Cat.assoc, ← Cat.assoc, term_uniq (k ≫ term _) (term V)]
    rw [hku, hk]

/-! ### §1.919  The representability engine and largeness algebra (map level)

  Freyd's §1.914/§1.919 argument is run entirely at the level of maps `A → Ω`
  (= predicates), using `Sub(−) ≅ Hom(−,Ω)`.  A unary operation `g : Ω → Ω`
  acts on predicates by `ĝ(p) := p ≫ g`.  Two facts power the whole thing:

  * REPRESENTABILITY (Yoneda): any *natural* family of unary operations
    `φ_A : Hom(A,Ω) → Hom(A,Ω)` (natural means `φ(f ≫ p) = f ≫ φ(p)`) is
    `ĥ` for `h := φ(id_Ω)` — a one-liner via naturality at `f := p`.
  * EXTENSIONALITY: if `g, h : Ω → Ω` have the same large predicates
    (`p ≫ g = ⊤ ↔ p ≫ h = ⊤` for all `p`) then `g = h` — because both are the
    classifier of `{p : p ≫ (·) = ⊤}`, i.e. of `g⁻¹(t) = h⁻¹(t)`. -/

/-- A predicate `p : A → Ω` is `g`-LARGE iff `p ≫ g = ⊤_A` (`ĝ(p) = ⊤`).  This is
    the map-level form of "`A'` is a `g`-large subobject"; by `allows_iff_classify`
    it is equivalent to `p` factoring through `V = g⁻¹(t)` (whose classifier is `g`,
    `classify_invTrue`). -/
theorem large_iff_factors_invTrue {A : 𝒞}
    (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (p : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    p ≫ g = term A ≫ HasSubobjectClassifier.true ↔ Allows (invTrue g) p := by
  rw [allows_iff_classify (invTrue g) p, classify_invTrue]

/-- **§1.919 (extensionality)**: two endomorphisms of `Ω` with the SAME large
    predicates are equal.  `p ≫ g = ⊤ ↔ p ≫ h = ⊤` for all `p` forces
    `g⁻¹(t) = h⁻¹(t)` as subobjects, hence `g = χ_{g⁻¹t} = χ_{h⁻¹t} = h`. -/
theorem omega_endo_ext
    (g h : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (hlarge : ∀ {A : 𝒞} (p : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)),
      p ≫ g = term A ≫ HasSubobjectClassifier.true
        ↔ p ≫ h = term A ≫ HasSubobjectClassifier.true) :
    g = h := by
  -- The defining inclusions are large for their own classifier (classifier square).
  have hLg : (invTrue g).arr ≫ g = term (invTrue g).dom ≫ HasSubobjectClassifier.true := by
    have := HasSubobjectClassifier.classify_sq (invTrue g).arr (invTrue g).monic
    rwa [classify_invTrue] at this
  have hLh : (invTrue h).arr ≫ h = term (invTrue h).dom ≫ HasSubobjectClassifier.true := by
    have := HasSubobjectClassifier.classify_sq (invTrue h).arr (invTrue h).monic
    rwa [classify_invTrue] at this
  -- g⁻¹(t) and h⁻¹(t) allow exactly the same maps, hence are le-equivalent.
  have hgh : (invTrue g).le (invTrue h) := by
    rw [le_iff_classify, classify_invTrue]; exact (hlarge (invTrue g).arr).1 hLg
  have hhg : (invTrue h).le (invTrue g) := by
    rw [le_iff_classify, classify_invTrue]; exact (hlarge (invTrue h).arr).2 hLh
  have := classify_eq_of_le_le hgh hhg
  rwa [show subChar (invTrue g) = g from classify_invTrue g,
       show subChar (invTrue h) = h from classify_invTrue h] at this

/-! ### §1.919  The subterminals `V = g⁻¹(t)` and `U = f⁻¹(t)` as subobjects of `1` -/

/-- `Ṽ ⊆ 1`: the subterminal `V = g⁻¹(t)` viewed as a subobject of the terminator
    (its inclusion is `term_{V.dom}`, monic because `V` is subterminal). -/
noncomputable def subV (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    Subobject 𝒞 (HasTerminal.one (𝒞 := 𝒞)) :=
  ⟨(invTrue g).dom, term (invTrue g).dom,
   fun a b _ => invTrue_subterminal g hm a b⟩

/-- `g(⊤) = t ≫ g` factors through `V = g⁻¹(t)` iff `g(g(⊤)) = ⊤`, i.e. `true_g_sq`.
    (The point `g(⊤) ∈ Ω` lies in the subterminal `V` exactly when it is `g`-true.) -/
theorem topPoint_in_V_iff (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    Allows (invTrue g) (HasSubobjectClassifier.true ≫ g)
      ↔ HasSubobjectClassifier.true ≫ g ≫ g = HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  rw [← large_iff_factors_invTrue g (HasSubobjectClassifier.true ≫ g)]
  constructor
  · intro h
    have : term (HasTerminal.one (𝒞 := 𝒞)) = Cat.id _ := term_uniq _ _
    rw [Cat.assoc] at h; rw [h, this, Cat.id_comp]
  · intro h
    rw [Cat.assoc, h, term_uniq (term (HasTerminal.one (𝒞 := 𝒞))) (Cat.id _), Cat.id_comp]

/-- `Ũ ⊆ 1`: the subterminal `U = f⁻¹(t)` (`f = V.arr : V.dom → Ω` the inclusion of
    `V`) viewed as a subobject of `1`.  `U ⊆ V.dom` is `invImg V.arr topOmega`; since
    `V.dom` is subterminal so is `U.dom`, and its inclusion into `1` is `term_{U.dom}`. -/
noncomputable def subU (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    Subobject 𝒞 (HasTerminal.one (𝒞 := 𝒞)) :=
  ⟨(invImg (invTrue g).arr topOmega (HasPullbacks.has _ _)).dom,
   term _,
   fun a b _ =>
     -- U.dom is subterminal: it maps monically into V.dom, which is subterminal.
     (invImg (invTrue g).arr topOmega (HasPullbacks.has _ _)).monic a b
       (invTrue_subterminal g hm
         (a ≫ (invImg (invTrue g).arr topOmega (HasPullbacks.has _ _)).arr)
         (b ≫ (invImg (invTrue g).arr topOmega (HasPullbacks.has _ _)).arr))⟩

/-- `w := χ_{Ṽ} : 1 → Ω`, the classifier of `V` as a subobject of `1`. -/
noncomputable abbrev wMap (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    HasTerminal.one (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  subChar (subV g hm)

/-- `u := χ_{Ũ} : 1 → Ω`, the classifier of `U` as a subobject of `1`. -/
noncomputable abbrev uMap (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    HasTerminal.one (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  subChar (subU g hm)

/-- The generic-stage Op map `h = Op(id_Ω) = (Ω×V) ∩ (id ⇔ Ω×U)`:
    `h := ⟨term_Ω ≫ w, ⟨id_Ω, term_Ω ≫ u⟩ ≫ ⇔⟩ ≫ ∧`. -/
noncomputable abbrev opMap (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) :=
  pair (term _ ≫ wMap g hm)
       (pair (Cat.id _) (term _ ≫ uMap g hm) ≫ heytingDoubleArrow) ≫ omegaMeet

/-- Membership form of `opMap`: `p ≫ Op(id) = ⊤` iff `(p factors into V)` and
    `(p = term ≫ u)`.  Pure `comp_meet`/`comp_dbar` bookkeeping (no content). -/
theorem opMap_true_iff {A : 𝒞}
    (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (hm : Monic g) (p : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    p ≫ opMap g hm = term A ≫ HasSubobjectClassifier.true
      ↔ (term A ≫ wMap g hm = term A ≫ HasSubobjectClassifier.true)
          ∧ (p = term A ≫ uMap g hm) := by
  unfold opMap
  rw [meet_true_iff_and (term _ ≫ wMap g hm)
        (pair (Cat.id _) (term _ ≫ uMap g hm) ≫ heytingDoubleArrow) p]
  -- first conjunct: p ≫ (term_Ω ≫ w) = term_A ≫ w  (terminal absorption)
  rw [show p ≫ (term _ ≫ wMap g hm) = term A ≫ wMap g hm by
        rw [← Cat.assoc, term_uniq (p ≫ term _) (term A)]]
  -- second conjunct: p ≫ (⟨id, term_Ω ≫ u⟩ ≫ ⇔) = ⊤ ↔ p = term_A ≫ u
  rw [comp_dbar, Cat.comp_id,
    show p ≫ (term _ ≫ uMap g hm) = term A ≫ uMap g hm by
      rw [← Cat.assoc, term_uniq (p ≫ term _) (term A)],
    show pair p (term A ≫ uMap g hm) ≫ heytingDoubleArrow
        = Cat.id A ≫ (pair p (term A ≫ uMap g hm) ≫ heytingDoubleArrow) by rw [Cat.id_comp],
    heyting_true_iff_eq, Cat.id_comp, Cat.id_comp]

/-- **§1.919 (`v` is `Ũ`-constant).**  `V.arr = term_{V.dom} ≫ u`, i.e. the
    inclusion `v : V.dom ↪ Ω` of the subterminal `V` factors through `1` as the
    constant `u = χ_{Ũ}`.  Reason: `χ_U^{V.dom} = v` (`U = v⁻¹(t)`,
    `χ_topOmega = id`), and `U = (term_{V.dom})⁻¹(Ũ)` as subobjects of `V.dom`
    (reindexing `Ũ⊆1` back along `V.dom → 1`), whose classifier is `term ≫ u`. -/
theorem v_eq_term_u (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    (invTrue g).arr = term (invTrue g).dom ≫ uMap g hm := by
  -- v = χ_U over V.dom  (U = v⁻¹(t), χ_topOmega = id).
  let U := invImg (invTrue g).arr topOmega (HasPullbacks.has (invTrue g).arr topOmega.arr)
  have hvU : (invTrue g).arr = subChar U := by
    show (invTrue g).arr = HasSubobjectClassifier.classify U.arr U.monic
    rw [show HasSubobjectClassifier.classify U.arr U.monic
          = (invTrue g).arr ≫ subChar topOmega from classify_invImg _ _ _]
    show (invTrue g).arr = (invTrue g).arr ≫
      HasSubobjectClassifier.classify HasSubobjectClassifier.true HasSubobjectClassifier.true_monic
    rw [classify_true_eq_id, Cat.comp_id]
  -- term_{V.dom} ≫ u = χ_{(term)⁻¹(Ũ)} over V.dom.
  have huInv : term (invTrue g).dom ≫ uMap g hm
      = subChar (invImg (term (invTrue g).dom) (subU g hm)
          (HasPullbacks.has _ _)) := by
    show term (invTrue g).dom ≫ HasSubobjectClassifier.classify (subU g hm).arr (subU g hm).monic
      = HasSubobjectClassifier.classify _ _
    exact (classify_invImg (term (invTrue g).dom) (subU g hm) (HasPullbacks.has _ _)).symm
  rw [hvU, huInv]
  -- Now: subChar U = subChar ((term)⁻¹ Ũ).  Show U ≃ (term)⁻¹ Ũ as subobjects of V.dom.
  let hpInv : HasPullback (term (invTrue g).dom) (subU g hm).arr :=
    HasPullbacks.has (term (invTrue g).dom) (subU g hm).arr
  apply classify_eq_of_le_le
  · -- U ≤ T: lift U.dom into the pullback T via (U.arr, id).
    have hsq : U.arr ≫ term (invTrue g).dom = Cat.id _ ≫ (subU g hm).arr := term_uniq _ _
    exact ⟨hpInv.lift ⟨U.dom, U.arr, Cat.id _, hsq⟩, hpInv.lift_fst _⟩
  · -- T ≤ U: π₂ : T.dom → U.dom witnesses, since π₂ ≫ U.arr = π₁ = T.arr (V.dom subterminal).
    exact ⟨hpInv.cone.π₂,
      invTrue_subterminal g hm (hpInv.cone.π₂ ≫ U.arr) hpInv.cone.π₁⟩

/-- **§1.919 CRUX — `Op` and `ĝ` have the same large predicates.**  For any
    `p : A → Ω`, `p` is `g`-large (`p ≫ g = ⊤`) iff `(A` factors into `V)` and
    `(p = term_A ≫ u)`.  This is the diagram-3 pullback characterization of
    `g`-largeness via the `U, V` construction. -/
theorem op_large_iff {A : 𝒞}
    (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞))
    (hm : Monic g) (p : A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    p ≫ g = term A ≫ HasSubobjectClassifier.true
      ↔ (term A ≫ wMap g hm = term A ≫ HasSubobjectClassifier.true)
          ∧ (p = term A ≫ uMap g hm) := by
  have hwAllows : term A ≫ wMap g hm = term A ≫ HasSubobjectClassifier.true
      ↔ Allows (subV g hm) (term A) :=
    (allows_iff_classify (subV g hm) (term A)).symm
  constructor
  · intro hp
    -- p ≫ g = ⊤ ⟹ p factors through V: p = p̄ ≫ v.
    obtain ⟨pb, hpb⟩ := (large_iff_factors_invTrue g p).1 hp
    refine ⟨hwAllows.2 ⟨pb, term_uniq _ _⟩, ?_⟩
    -- p = pb ≫ v = pb ≫ (term ≫ u) = term_A ≫ u.
    rw [← hpb, v_eq_term_u g hm, ← Cat.assoc, term_uniq (pb ≫ term (invTrue g).dom) (term A)]
  · rintro ⟨hw, hpu⟩
    -- A factors into V via a0; then p = term_A ≫ u = a0 ≫ v factors through V.
    obtain ⟨a0, _⟩ := hwAllows.1 hw
    apply (large_iff_factors_invTrue g p).2
    refine ⟨a0, ?_⟩
    rw [v_eq_term_u g hm, hpu, ← Cat.assoc, term_uniq (a0 ≫ term (invTrue g).dom) (term A)]

/-- **§1.919 (operation form, with the `A×V` factor).**  `g = Op(id_Ω)`: by
    representability/extensionality (`omega_endo_ext`), since `ĝ` and `Op` have the
    same large predicates (`op_large_iff` vs. `opMap_true_iff`). -/
theorem g_eq_opMap (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    g = opMap g hm :=
  omega_endo_ext g (opMap g hm) (fun {A} p => by
    rw [op_large_iff g hm p, opMap_true_iff g hm p])

/-- **§1.919 (`V = 1`).**  `term_Ω ≫ w = ⊤_Ω`: the subterminal `V` is the whole
    terminator.  Freyd's step 4: `ĝ(V) = ĝ(1)` and `ĝ` is injective (`g` monic).
    Concretely, both `ĝ(1)` and `ĝ(V)` reduce (via `g = Op`) to `V ∩ U`; here we
    extract it from `g = Op` evaluated so the `V`-factor must already be `⊤`. -/
theorem V_eq_one (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ wMap g hm
      = term (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ≫ HasSubobjectClassifier.true := by
  -- ĝ(1) = ĝ(V): `t ≫ g = wMap ≫ g`, then `g` monic gives `t = wMap`, so V = 1.
  have hkey : HasSubobjectClassifier.true (𝒞 := 𝒞) ≫ g = wMap g hm ≫ g := by
    -- Both ⊤-patterns at `k : V' → 1` reduce to: (k ≫ w = ⊤) ∧ (k ≫ (t or wMap) = k ≫ u).
    -- Under `k ≫ w = ⊤` both `k ≫ t` and `k ≫ wMap` equal `⊤_{V'}`, so they coincide.
    refine omega_ext _ _ (fun {V'} k => ?_)
    have e1 := op_large_iff g hm (k ≫ HasSubobjectClassifier.true)
    have e2 := op_large_iff g hm (k ≫ wMap g hm)
    rw [Cat.assoc] at e1 e2
    rw [e1, e2]
    -- term V' ≫ w on both sides matches (terminal); reconcile the second conjuncts.
    have htw : term V' ≫ wMap g hm = term V' ≫ HasSubobjectClassifier.true
        → k ≫ HasSubobjectClassifier.true = k ≫ wMap g hm := by
      intro hw
      rw [term_uniq k (term V'), hw]
    constructor
    · rintro ⟨hw, hk⟩; exact ⟨hw, by rw [← htw hw]; exact hk⟩
    · rintro ⟨hw, hk⟩; exact ⟨hw, by rw [htw hw]; exact hk⟩
  -- g monic: t = wMap, hence term_Ω ≫ wMap = term_Ω ≫ t.
  have : HasSubobjectClassifier.true (𝒞 := 𝒞) = wMap g hm := hm _ _ hkey
  rw [← this]

/-- **§1.914 (`⊤ ∧ c = c`)**: `⟨term ≫ true, c⟩ ≫ ∧ = c`.  The meet with a
    constantly-true first component is the identity (membership form via
    `meet_true_iff_and` + `omega_ext`). -/
theorem true_meet {W : 𝒞} (c : W ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)) :
    pair (term W ≫ HasSubobjectClassifier.true) c ≫ omegaMeet = c := by
  refine omega_ext _ _ (fun {V'} k => ?_)
  rw [meet_true_iff_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    exact ⟨by rw [← Cat.assoc, term_uniq (k ≫ term W) (term V')], h⟩

/-- **§1.919 (op-form, `V = 1` folded in).**  `g = ⟨id_Ω, term_Ω ≫ u⟩ ≫ ⇔`.
    From `g = Op(id)` (`g_eq_opMap`) the `Ω×V` meet-factor is constantly `⊤`
    (`V_eq_one`), so `⟨⊤, X⟩ ≫ ∧ = X` (`true_meet`) collapses it. -/
theorem g_eq_opForm (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    g = pair (Cat.id _) (term _ ≫ uMap g hm) ≫ heytingDoubleArrow := by
  have hop : g = pair (term _ ≫ wMap g hm)
      (pair (Cat.id _) (term _ ≫ uMap g hm) ≫ heytingDoubleArrow) ≫ omegaMeet :=
    g_eq_opMap g hm
  rw [V_eq_one g hm, true_meet] at hop
  exact hop

/-- **§1.919 (`g²(⊤) = ⊤`, Freyd's step 5).**  From the op-form
    `g = ⟨id, term_Ω ≫ u⟩ ≫ ⇔` (`g_eq_opForm`): `t ≫ g = ⟨t, u⟩ ≫ ⇔ = u`
    (`true_dbar`), then `u ≫ g = ⟨u, u⟩ ≫ ⇔ = ⊤` (`dbar_refl_top`). -/
theorem true_g_sq_of_opForm (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) :
    HasSubobjectClassifier.true ≫ g ≫ g = HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  -- Generalize `u := uMap g hm` so rewriting `g` by the op-form does not touch it.
  obtain ⟨u, hgform⟩ :
      ∃ u : HasTerminal.one (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞),
        g = pair (Cat.id _) (term _ ≫ u) ≫ heytingDoubleArrow :=
    ⟨uMap g hm, g_eq_opForm g hm⟩
  -- For any point q : 1 → Ω, `q ≫ (term_Ω ≫ u) = u`  (terminality collapses term_Ω).
  have hqc : ∀ q : HasTerminal.one (𝒞 := 𝒞) ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞),
      q ≫ (term _ ≫ u) = u := fun q => by
    rw [← Cat.assoc, term_uniq (q ≫ term _) (term HasTerminal.one),
      term_uniq (term HasTerminal.one) (Cat.id _), Cat.id_comp]
  have htrue : HasSubobjectClassifier.true (𝒞 := 𝒞)
      = term HasTerminal.one ≫ HasSubobjectClassifier.true := by
    rw [term_uniq (term HasTerminal.one) (Cat.id _), Cat.id_comp]
  -- t ≫ g = ⟨t, u⟩ ≫ ⇔ = u.
  have htg : HasSubobjectClassifier.true (𝒞 := 𝒞) ≫ g = u := by
    rw [hgform, comp_dbar, Cat.comp_id, hqc HasSubobjectClassifier.true]
    rw [htrue, true_dbar u]
  -- (t ≫ g) ≫ g = u ≫ g = ⟨u, u⟩ ≫ ⇔ = ⊤ = t.
  rw [← Cat.assoc, htg, hgform, comp_dbar, Cat.comp_id, hqc u,
    dbar_refl_top, term_uniq (term HasTerminal.one) (Cat.id _), Cat.id_comp]

/-! ## §1.919  Monic endomorphisms of Ω are involutions

  §1.919: Every monic endomorphism `g : Ω → Ω` is an involution (`g² = id`).
  CLOSED, SORRY-FREE (axioms: `propext` only).

  The whole argument runs through one named map equation,

      true_g_sq :  t ≫ g ≫ g = t        (`g(g(⊤)) = ⊤`)

  i.e. the subterminal `G := g⁻¹(t)` (`invTrue g`, subterminal by
  `invTrue_subterminal`, classified by `g` via `classify_invTrue`) is INHABITED by
  its canonical point `g(⊤) = t ≫ g`.  This is Freyd's `V = 1` step.

  THE ENGINE (map-level §1.914/§1.919, all SORRY-FREE):
  - `omega_endo_ext` (representability/extensionality): two endos of `Ω` with the
    same large predicates (`p ≫ g = ⊤ ↔ p ≫ h = ⊤`) are equal — both classify
    `g⁻¹(t) = h⁻¹(t)`.
  - `v_eq_term_u` (the NON-CIRCULAR crux): `V.arr = term_{V.dom} ≫ u`, i.e. the
    inclusion of the subterminal `V` is the constant `u = χ_{Ũ}` (because
    `U = (term_{V.dom})⁻¹(Ũ)` as subobjects of `V.dom`, `V` subterminal).
  - `op_large_iff`: `ĝ` and Freyd's `Op = (−×V) ∩ (− ⇔ −×U)` have the SAME large
    predicates (via `v_eq_term_u`).  Hence `g = Op(id)` (`g_eq_opMap`).
  - `V_eq_one`: `g` monic ⟹ `ĝ(V) = ĝ(1)` ⟹ `t = wMap` ⟹ `V = 1`.
  - `g_eq_opForm`: fold `V = 1` into `g = Op(id)` (drop the `Ω×V` meet via
    `true_meet`) to get `g = ⟨id, term_Ω ≫ u⟩ ≫ ⇔`.
  - `true_g_sq_of_opForm`: read off `g²(⊤) = (⊤⇔u)⇔u = u⇔u = ⊤` (`true_dbar`,
    `dbar_refl_top`).  This is `true_g_sq`.
  - `omega_involution_of_opForm`: given the operation form `g = ⟨id, u₀⟩ ≫ ⇔`,
    the involution follows from `comp_dbar` (naturality of ⇔) + `Monic g` alone.
  - the main theorem derives the operation form from `true_g_sq` via `omega_ext`
    + `heyting_true_iff_eq` (both legs of the resulting iff are `Monic g` + `true_g_sq`).

  CORRECTS the earlier "needs a Boolean fact / irreducible from Monic g" verdict:
  the residual is NOT a Boolean law `(S⇔u)⇔u = S` and NOT the false `t ≫ g = t`
  (`g(⊤) = ⊤`, which fails for `g = ¬`).  It is the TRUE positive equation
  `t ≫ g ≫ g = t` (holds for `¬`: `¬¬⊤ = ⊤`), reachable only through Freyd's
  `U,V` largeness construction (Diagrams §1.919 1–3), not from `Monic g` in isolation. -/

/-- **§1.919**: Every monic endomorphism of Ω is an involution; `g : Ω → Ω` monic
    implies `g ≫ g = id`.

    PROOF ARCHITECTURE (CLOSED, SORRY-FREE; axioms: `propext`).  Freyd reads `g` as the
    operation `ĝ(S) := classify⁻¹(χ_S ≫ g)` on `Sub(A) ≅ Hom(A,Ω)`; `S` is
    `g`-large when `ĝ(S) = ⊤_A`.  His `U,V` construction yields the OPERATION FORM
    (with `V = 1`):

        OPFORM:  `g = ⟨id_Ω, u₀⟩ ≫ ⇔`,   `u₀ := term_Ω ≫ (t ≫ g)`            (★)

    that is `ĝ(⊤_Ω) = ⊤_Ω ⇔ ĝ(⊤_Ω)` at the generic element.  We split the proof:

    * `omega_involution_of_opForm` (SORRY-FREE): given (★), `g ≫ g = id`.  Needs
      only `comp_dbar` (naturality of ⇔ in the stage), `g ≫ u₀ = u₀`, and `Monic g`
      — explicitly **no Boolean law** `(S⇔u)⇔u = S`.  (`g ≫ g = ⟨g,u₀⟩ ≫ ⇔`, then
      `omega_ext` + `heyting_true_iff_eq` reduce `⟨g,u₀⟩ ≫ ⇔ = id` to
      `k ≫ g = k ≫ u₀ ↔ k = ⊤`, forward = `Monic g`, backward = substitution.)

    * The body below derives (★) from the SINGLE map equation

        true_g_sq :  t ≫ g ≫ g = t        (`g(g(⊤)) = ⊤`)                       (†)

      again Sorry-free: by `omega_ext` it suffices to match ⊤-patterns; both legs of
      the resulting iff are `Monic g` + (†).

    So the ENTIRE §1.919 content is concentrated in (†): the subterminal
    `G := g⁻¹(t)` (`invTrue g`, subterminal by `invTrue_subterminal`, classified by
    `g` via `classify_invTrue`) is INHABITED by its canonical point `g(⊤) = t ≫ g`.

    (†) IS GENUINE POSITIVE CONTENT — Freyd's `V = 1` — and is now PROVED
    (`true_g_sq_of_opForm`).  It is NOT a consequence of `Monic g` in isolation
    (`Monic g` only gives right-cancellation; inhabitation of a subterminal is a
    positive fact).  The proof is Freyd's `U,V` largeness construction
    (Diagrams §1.919 1–3): build `V ⊆ 1` (`subV`) and `U = f⁻¹(t) ⊆ V` (`subU`) as
    subterminals; the non-circular crux `v_eq_term_u` gives the largeness↔pullback
    correspondence `op_large_iff`; representability (`omega_endo_ext`) yields
    `g = Op(id)` (`g_eq_opMap`); `ĝ(V) = ĝ(1)` + `Monic g` gives `V = 1` (`V_eq_one`);
    folding `V = 1` into the op-form (`g_eq_opForm`) reads off (†).

    DEBUNK of the earlier verdict (recorded for future readers).  The prior pass
    declared this "needs a Boolean fact / irreducible from Monic g" and reduced to a
    "CRUX" it conflated with `t ≫ g = t` (`g(⊤) = ⊤`).  Both framings were wrong:
    (a) No Boolean law is needed — `omega_involution_of_opForm` is Boolean-free.
    (b) `t ≫ g = t` is FALSE for `g = ¬` (`¬⊤ = ⊥`); the true residual is
        `t ≫ g ≫ g = t`, which HOLDS for `¬` (`¬¬⊤ = ⊤`) and for `id`.
    The remaining gap is exactly Freyd's `V = 1` inhabitation, not a Boolean axiom. -/
theorem omega_monic_endo_is_involution (g : HasSubobjectClassifier.omega (𝒞 := 𝒞) ⟶
    HasSubobjectClassifier.omega (𝒞 := 𝒞)) (hm : Monic g) : g ≫ g = Cat.id _ := by
  -- Reduced (axiom-free, this pass) to the single OPERATION-FORM equation
  --   OPFORM:  g = ⟨id_Ω, u₀⟩ ≫ ⇔,   u₀ := term_Ω ≫ (t ≫ g)
  -- via `omega_involution_of_opForm` (proven Sorry-free above: given OPFORM the
  -- involution needs only `comp_dbar` + `Monic g`, NO Boolean fact).  OPFORM is
  -- Freyd's `ĝ(⊤_Ω) = ⊤_Ω ⇔ ĝ(⊤_Ω)` with `V = 1`; its hard half unfolds (via
  -- `omega_ext` + `heyting_true_iff_eq`) to `t ≫ g ≫ g = t` (`g(g⊤)=⊤`), i.e.
  -- the subterminal `G = g⁻¹(t)` is inhabited by the point `g(⊤)`.  See the
  -- docstring: that positive inhabitation is Freyd's `V = 1` step.
  refine omega_involution_of_opForm g hm ?_
  -- OPFORM `g = ⟨id_Ω, u₀⟩ ≫ ⇔` reduced (Sorry-free given `true_g_sq` below) to the
  -- SINGLE map equation `t ≫ g ≫ g = t` (`g(g⊤)=⊤`).  By `omega_ext` it suffices
  -- to match ⊤-patterns; by `heyting_true_iff_eq` (χ₁ = id, χ₂ = u₀) the RHS-pattern
  -- at `k` is `k ≫ g = k ≫ u₀`, and `k ≫ u₀ = (term_V ≫ t) ≫ g`.  Both legs of the
  -- resulting iff `k ≫ g = ⊤ ↔ k ≫ g = (term ≫ t) ≫ g` follow from `true_g_sq`:
  --   (→) `k ≫ g = term ≫ t`; then `(term ≫ t) ≫ g = term ≫ (t ≫ g)` and applying `g`
  --       once more gives `term ≫ (t ≫ g ≫ g) = term ≫ t` (true_g_sq) `= k ≫ g`.
  --   (←) symmetric.  (Equivalently both reduce to `Monic g` + `true_g_sq`.)
  have true_g_sq : HasSubobjectClassifier.true ≫ g ≫ g
      = HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    -- CLOSED (`true_g_sq_of_opForm`): Freyd's `U,V` largeness construction.  The
    -- non-circular engine is `op_large_iff` (`ĝ` and `Op` have the same large
    -- predicates) + `omega_endo_ext` (representability) ⟹ `g = Op(id)`
    -- (`g_eq_opMap`); `g` monic ⟹ `V = 1` (`V_eq_one`); folding `V = 1` into the
    -- op-form (`g_eq_opForm`) and reading off `ĝ²(⊤) = (⊤⇔u)⇔u = u⇔u = ⊤`.
    exact true_g_sq_of_opForm g hm
  -- Assemble OPFORM `g = ⟨id, u₀⟩ ≫ ⇔` from `true_g_sq` via `omega_ext`.
  refine omega_ext _ _ (fun {V} k => ?_)
  -- The RHS ⊤-pattern at `k`: `k ≫ (⟨id,u₀⟩≫⇔) = ⊤ ↔ k = k ≫ u₀` (heyting_true_iff_eq,
  -- with `k ≫ id = k`), and `k ≫ u₀ = term_V ≫ (t ≫ g)`.
  have hku : k ≫ opPoint g = term V ≫ (HasSubobjectClassifier.true ≫ g) := by
    show k ≫ (term _ ≫ _) = term V ≫ _
    rw [← Cat.assoc, term_uniq (k ≫ term _) (term V)]
  rw [heyting_true_iff_eq, Cat.comp_id, hku]
  -- Goal: `k ≫ g = term V ≫ true  ↔  k = term V ≫ (t ≫ g)`.
  -- `p := term V ≫ (t ≫ g)` satisfies `p ≫ g = term V ≫ true` by `true_g_sq`.
  have hp : (term V ≫ (HasSubobjectClassifier.true ≫ g)) ≫ g = term V ≫ HasSubobjectClassifier.true := by
    calc (term V ≫ (HasSubobjectClassifier.true ≫ g)) ≫ g
        = term V ≫ (HasSubobjectClassifier.true ≫ g ≫ g) := by rw [Cat.assoc, Cat.assoc]
      _ = term V ≫ HasSubobjectClassifier.true := by rw [true_g_sq]
  constructor
  · -- (→) `k ≫ g = ⊤` ⟹ `k = p`: both have `· ≫ g = ⊤`, cancel by `Monic g`.
    intro hk
    exact hm k _ (by rw [hk, hp])
  · -- (←) `k = p` ⟹ `k ≫ g = ⊤`: substitute and use `hp`.
    intro hk
    rw [hk, hp]

/-! ## §1.91(10)  Minimal topos definition

  A category with binary products and equalizers (equivalently: binary products
  and pullbacks, or all finite non-empty limits) and power-objects for every
  object, which is non-empty, already has a terminator and hence is a topos
  (§1.91(10)).  Crucially the hypotheses here do NOT presuppose a terminator —
  power-objects are taken via `HasPowerObject`, which (unlike
  `HasSubobjectClassifier`, that `extends HasTerminal`) needs only pullbacks.

  CONSTRUCTION (Freyd): For objects A,B let M_{A,B} denote the "full" relation
  tabulated by the product projection A×B → A (its table is A×B with the two
  projections).  For any f : A' → A the equation f(M_{A,B}) = M_{A',B} holds, so
  AM_{A,B} := Λ(M_{A,B}) is a CONSTANT map: f(AM_{A,B}) = g(AM_{A,B}) for all
  f,g : A' → A.  Hence Λ(M_{B,B}) : [B] → [B] is a constant idempotent
  endomorphism.  For any A there is a map A → [B] (namely AM_{A,B}), so the
  equalizer T of id_{[B]} and Λ(M_{B,B}) is a terminator. -/

section MinimalTopos
variable [HasPullbacks 𝒞] [HasBinaryProducts 𝒞]

/-- §1.91(10): The "full" relation `M_{A,C} : A → C`, tabulated by the product
    projection — its table is `A×C` with the two product projections as columns.
    Jointly monic because `pair fst snd = id`. -/
noncomputable def fullRel (A C : 𝒞) : BinRel 𝒞 A C where
  src  := prod A C
  colA := fst
  colB := snd
  isMonicPair := fst_snd_jointly_monic

/-- §1.91(10): `f(M_{A,C}) = M_{A',C}` — pulling the full relation back along
    `f : A' → A` gives the full relation again.  The pullback of `fst : A×C → A`
    along `f` is `A'×C` (via `pair`), realizing the iso of tables in both
    directions. -/
theorem fullRel_pullback {A A' C : 𝒞} (f : A' ⟶ A) :
    RelHom (relPullback f (fullRel A C)) (fullRel A' C) ∧
    RelHom (fullRel A' C) (relPullback f (fullRel A C)) := by
  let pb := HasPullbacks.has f (fullRel A C).colA
  -- relPullback f (fullRel A C) has table pb.pt, colA = π₁, colB = π₂ ≫ snd.
  -- Abbreviate the two projections at the two arities to pin down their types.
  let sA  : prod A C  ⟶ C := snd
  let sA' : prod A' C ⟶ C := snd
  -- backward cone over (f, fst) with apex A'×C: (fst, pair (fst≫f) snd).
  have hbw : (fst : prod A' C ⟶ A') ≫ f = pair (fst ≫ f) sA' ≫ (fullRel A C).colA := by
    show (fst : prod A' C ⟶ A') ≫ f = pair (fst ≫ f) sA' ≫ fst
    rw [fst_pair]
  let cbw : Cone f (fullRel A C).colA := ⟨prod A' C, fst, pair (fst ≫ f) sA', hbw⟩
  refine ⟨⟨pair pb.cone.π₁ (pb.cone.π₂ ≫ sA), fst_pair _ _, ?_⟩,
          ⟨pb.lift cbw, pb.lift_fst cbw, ?_⟩⟩
  · -- forward colB: pair π₁ (π₂≫snd) ≫ snd = π₂ ≫ snd.
    show pair pb.cone.π₁ (pb.cone.π₂ ≫ sA) ≫ sA' = pb.cone.π₂ ≫ sA
    exact snd_pair _ _
  · -- backward colB: (pb.lift cbw) ≫ (π₂ ≫ snd) = snd.
    show pb.lift cbw ≫ (pb.cone.π₂ ≫ sA) = sA'
    calc pb.lift cbw ≫ (pb.cone.π₂ ≫ sA)
        = (pb.lift cbw ≫ pb.cone.π₂) ≫ sA := (Cat.assoc _ _ _).symm
      _ = pair (fst ≫ f) sA' ≫ sA := congrArg (· ≫ sA) (pb.lift_snd cbw)
      _ = sA' := snd_pair _ _

variable [∀ C : 𝒞, HasPowerObject C]

/-- The classifying map `Λ(M_{A,B}) = AM_{A,B} : A → [B]` of the full relation. -/
noncomputable def fullClassify (A B : 𝒞) : A ⟶ HasPowerObject.powerObj (C := B) :=
  powerClassify (fullRel A B)

/-- Transitivity of `RelHom` (local copy; the S1_92 version depends on S1_91). -/
theorem relHom_trans {A C : 𝒞} {R S T : BinRel 𝒞 A C}
    (h₁ : RelHom R S) (h₂ : RelHom S T) : RelHom R T := by
  obtain ⟨h, hA, hB⟩ := h₁; obtain ⟨k, kA, kB⟩ := h₂
  exact ⟨h ≫ k, by rw [Cat.assoc, kA, hA], by rw [Cat.assoc, kB, hB]⟩

/-- `RelHom` is preserved by pulling back along a fixed `g`, obtained by lifting
    one table into the pullback of the other. -/
theorem relHom_pullback {A C X : 𝒞} (g : X ⟶ A) {R S : BinRel 𝒞 A C}
    (h : RelHom R S) : RelHom (relPullback g R) (relPullback g S) := by
  obtain ⟨w, hwA, hwB⟩ := h
  let P  := HasPullbacks.has g R.colA
  let P' := HasPullbacks.has g S.colA
  -- cone over (g, S.colA) with apex P.pt: (π₁, π₂ ≫ w).
  have hsq : P.cone.π₁ ≫ g = (P.cone.π₂ ≫ w) ≫ S.colA :=
    calc P.cone.π₁ ≫ g = P.cone.π₂ ≫ R.colA := P.cone.w
      _ = P.cone.π₂ ≫ (w ≫ S.colA) := congrArg (P.cone.π₂ ≫ ·) hwA.symm
      _ = (P.cone.π₂ ≫ w) ≫ S.colA := (Cat.assoc P.cone.π₂ w S.colA).symm
  let c : Cone g S.colA := ⟨P.cone.pt, P.cone.π₁, P.cone.π₂ ≫ w, hsq⟩
  refine ⟨P'.lift c, P'.lift_fst c, ?_⟩
  -- colB: (P'.lift c) ≫ (π₂' ≫ S.colB) = π₂ ≫ R.colB.
  show P'.lift c ≫ (P'.cone.π₂ ≫ S.colB) = P.cone.π₂ ≫ R.colB
  calc P'.lift c ≫ (P'.cone.π₂ ≫ S.colB)
      = (P'.lift c ≫ P'.cone.π₂) ≫ S.colB := (Cat.assoc _ _ _).symm
    _ = (P.cone.π₂ ≫ w) ≫ S.colB := congrArg (· ≫ S.colB) (P'.lift_snd c)
    _ = P.cone.π₂ ≫ (w ≫ S.colB) := Cat.assoc _ _ _
    _ = P.cone.π₂ ≫ R.colB := congrArg (P.cone.π₂ ≫ ·) hwB

/-- **§1.91(10), naturality of `Λ`**: `Λ(relPullback g R) = g ≫ Λ(R)`.
    Both classify `relPullback g R` (via `relPullback_comp`), so universality's
    `classify_unique` forces them equal.  (Local; S1_92's `univClassify_natural`
    depends on S1_91.) -/
theorem powerClassify_natural {C A X : 𝒞} (R : BinRel 𝒞 A C) (g : X ⟶ A) :
    powerClassify (relPullback g R) = g ≫ powerClassify R := by
  have hR := (HasPowerObject.is_universal.classify_exists A R).choose_spec
  obtain ⟨hc1, hc2⟩ := relPullback_comp g (powerClassify R) HasPowerObject.mem
  have hf : RelHom (relPullback g R)
              (relPullback (g ≫ powerClassify R) HasPowerObject.mem) ∧
            RelHom (relPullback (g ≫ powerClassify R) HasPowerObject.mem)
              (relPullback g R) :=
    ⟨relHom_trans (relHom_pullback g hR.1) hc1,
     relHom_trans hc2 (relHom_pullback g hR.2)⟩
  exact HasPowerObject.is_universal.classify_unique X (relPullback g R) _ _
    (HasPowerObject.is_universal.classify_exists X (relPullback g R)).choose_spec hf

/-- **§1.91(10), constancy**: `g ≫ Λ(M_{A,B})` does not depend on `g : X → A` —
    it equals `Λ(M_{X,B})`.  By naturality `g ≫ Λ(M_{A,B}) = Λ(g(M_{A,B}))` and
    `g(M_{A,B}) ≅ M_{X,B}` (`fullRel_pullback`). -/
theorem fullClassify_const {A B X : 𝒞} (g : X ⟶ A) :
    g ≫ fullClassify A B = fullClassify X B := by
  rw [fullClassify, ← powerClassify_natural (fullRel A B) g]
  exact HasPowerObject.is_universal.classify_unique X _ _ _
    (HasPowerObject.is_universal.classify_exists X (relPullback g (fullRel A B))).choose_spec
    ⟨relHom_trans (fullRel_pullback g).1
        (HasPowerObject.is_universal.classify_exists X (fullRel X B)).choose_spec.1,
     relHom_trans (HasPowerObject.is_universal.classify_exists X (fullRel X B)).choose_spec.2
        (fullRel_pullback g).2⟩

variable [HasEqualizers 𝒞]

/-- **§1.91(10)**: A non-empty category with binary products, equalizers, pullbacks,
    and power objects FOR EVERY OBJECT (but NOT assumed to have a terminator) already
    has a terminator.  `B` witnesses non-emptiness.

    This is the faithful statement of Freyd's §1.91(10): the hypotheses are exactly
    the data of his construction and DO NOT bundle a terminator (unlike
    `HasSubobjectClassifier`, which `extends HasTerminal` and would make the
    conclusion free).

    CONSTRUCTION.  `e := Λ(M_{[B],B}) : [B] → [B]` is a constant map
    (`fullClassify_const`).  Take `T := equalizer (id_{[B]}, e)`.
    - Existence of `A → T`: `Λ(M_{A,B})` equalizes `id` and `e`
      (`Λ(M_{A,B}) ≫ e = Λ(M_{A,B})` by constancy), so it factors through `T`.
    - Uniqueness: any `u, v : A → T` have `u ≫ eqMap`, `v ≫ eqMap : A → [B]`;
      constancy gives `(u ≫ eqMap) ≫ e = (v ≫ eqMap) ≫ e`, and `eqMap ≫ e = eqMap`
      (the equalizer relation), so `u ≫ eqMap = v ≫ eqMap`; `eqMap` is monic
      (equalizer map), hence `u = v`. -/
theorem minimal_topos_has_terminator (B : 𝒞) : Nonempty (HasTerminal 𝒞) := by
  let Pb := HasPowerObject.powerObj (C := B)
  let e : Pb ⟶ Pb := fullClassify Pb B
  -- e is constant: any two maps into Pb agree after `≫ e`.
  have hconst : ∀ {X : 𝒞} (p q : X ⟶ Pb), p ≫ e = q ≫ e := fun p q => by
    rw [fullClassify_const p, fullClassify_const q]
  -- the equalizer relation `eqMap ≫ id = eqMap ≫ e`, i.e. `eqMap ≫ e = eqMap`.
  have hEqMap : eqMap (Cat.id Pb) e ≫ e = eqMap (Cat.id Pb) e := by
    have := eqMap_eq (Cat.id Pb) e; rw [Cat.comp_id] at this; exact this.symm
  refine ⟨{ one := eqObj (Cat.id Pb) e, trm := fun A => ?_, uniq := fun {A} u v => ?_ }⟩
  · -- A → T: Λ(M_{A,B}) equalizes id and e (constancy: Λ(M_{A,B}) ≫ e = Λ(M_{A,B})).
    refine eqLift (Cat.id Pb) e (fullClassify A B) ?_
    rw [Cat.comp_id]
    exact (fullClassify_const (fullClassify A B)).symm
  · -- uniqueness: cancel the monic `eqMap` after showing `u ≫ eqMap = v ≫ eqMap`.
    have hmono : Monic (eqMap (Cat.id Pb) e) := by
      intro W f g hfg
      exact (eqLift_uniq (Cat.id Pb) e (f ≫ eqMap (Cat.id Pb) e)
              (by rw [Cat.assoc, eqMap_eq, Cat.assoc]) f rfl).trans
            (eqLift_uniq (Cat.id Pb) e (f ≫ eqMap (Cat.id Pb) e)
              (by rw [Cat.assoc, eqMap_eq, Cat.assoc]) g hfg.symm).symm
    apply hmono
    -- u ≫ eqMap = v ≫ eqMap: postcompose hconst with `≫ e` collapses via hEqMap.
    calc u ≫ eqMap (Cat.id Pb) e
        = (u ≫ eqMap (Cat.id Pb) e) ≫ e := by rw [Cat.assoc, hEqMap]
      _ = (v ≫ eqMap (Cat.id Pb) e) ≫ e := hconst _ _
      _ = v ≫ eqMap (Cat.id Pb) e := by rw [Cat.assoc, hEqMap]

end MinimalTopos

end Freyd
