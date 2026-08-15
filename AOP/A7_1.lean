/-
  Bird & de Moor, *Algebra of Programming* §7.1  Minimum and maximum (book pp. 165-172)
  — CORE (`minRel`, `maxRel`, the universal properties, and (7.5)).

  For `R : a ⟶ a`, B&dM define `min R = ∈ ∩ (R/∋) : A ← PA` — a minimum of `x` under `R`
  is an element of `x` that is also an `R`-lower bound of `x`.

  MIRRORING (diagram order, B&dM `X·Y` = Freyd `Y ≫ X`):
  - B&dM `∈ : A ← PA` is Freyd's `∋ a : powerObj a ⟶ a`; B&dM `∋ = ∈°` is Freyd `(∋ a)°`.
  - B&dM division `R/S` (UP: `X ⊆ R/S ⟺ X·S ⊆ R`) mirrors to Freyd `(S \ R)`
    (`le_leftDiv_iff : T ⊑ (S \ R) ↔ S ≫ T ⊑ R`); B&dM `S\R` mirrors to Freyd `R / S`.
  - Hence `min R = ∈ ∩ (R/∋)` mirrors to `minRel R = ∋ a ∩ (((∋ a)°) \ R)`.

  Setting: `UnguardedPowerLCDA` (`AOP.A6_2`) — the chapter-6/7 ambient class giving the
  power operations, division, and complete hom-lattices in one diamond-safe bundle.
-/
module

public import AOP.A6_2
public import AOP.A5_4

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {a b : 𝒜}

-- (The generic laws `leftDiv_id`, `leftDiv_comp`, `leftDiv_inter` were hoisted to their
-- canonical home `Freyd.S2_3` at collection.)

/-! ## `min R` and `max R` (book p.166) -/

/-- **B&dM p.166**: `min R = ∈ ∩ (R/∋)`, mirrored: a minimum of `x` under `R` is a member
    of `x` that is an `R`-lower bound of `x`. -/
@[expose] public def minRel (R : a ⟶ a) : PowerAllegory.powerObj a ⟶ a :=
  ∋ a ∩ (((∋ a)°) \ R)

/-- **B&dM p.166**: `max R = min R°`. -/
@[expose] public def maxRel (R : a ⟶ a) : PowerAllegory.powerObj a ⟶ a := minRel R°

/-- The universal property of `min` (book p.166): `X ⊑ min R ⟺ X ⊑ ∈ ∧ X·∋ ⊑ R`,
    mirrored (`X·∋` becomes `(∋ a)° ≫ X`). -/
public theorem le_minRel_iff {R : a ⟶ a} {X : PowerAllegory.powerObj a ⟶ a} :
    X ⊑ minRel R ↔ X ⊑ ∋ a ∧ (∋ a)° ≫ X ⊑ R := by
  constructor
  · intro h
    refine ⟨le_trans h (show minRel R ⊑ ∋ a from inter_lb_left _ _), ?_⟩
    exact le_trans (comp_mono_left _ (le_trans h
      (show minRel R ⊑ (((∋ a)°) \ R) from inter_lb_right _ _))) (leftDiv_comp_le _ _)
  · rintro ⟨h1, h2⟩
    exact le_inter h1 ((le_leftDiv_iff _ _ _).mpr h2)

/-- The `min` lower-bound law as a composition: `(∋ a)°·min R ⊑ R` (`min R·∋ ⊆ R` mirrored) —
    the minimum of a set is `R`-below every member.  Just the second half of `min`'s universal
    property applied to `min R` itself; companion to `AOP.A8_1`'s `recip_eps_comp_thinRel_le`
    for `thin`. -/
public theorem recip_eps_comp_minRel_le (R : a ⟶ a) : (∋ a)° ≫ minRel R ⊑ R :=
  (le_minRel_iff.mp (le_refl (minRel R))).2

/-! ## (7.5) and its universal property

  The workhorse: composing `min R` with the power transpose of `S` computes minima over
  the `S`-image.  Key step: `A S` transports lower bounds, `A S ≫ (R/∋) = R/S°` mirrored. -/

/-- `ΛS·(R/∋) = R/S°` mirrored: `A S ≫ ((∋ a)° \ R) = (S° \ R)` (B&dM (7.2)).
    Stated for a numerator of ARBITRARY target type `c` — §7.1 uses it at `c := a`
    (`R` an order on `a`), §8.1's thinning at `c := powerObj a`. -/
public theorem Λ_comp_lb {c : 𝒜} (S : b ⟶ a) (R : a ⟶ c) :
    Λ S ≫ (((∋ a)°) \ R) = (S° \ R) := by
  have hS' : (∋ a)° ≫ (Λ S)° = S° := by rw [← Allegory.recip_comp, Λ_eps_eq']
  apply le_antisymm
  · apply (le_leftDiv_iff _ _ _).mpr
    have hsimple : (Λ S)° ≫ Λ S ⊑ Cat.id _ := (Λ_is_map' S).2
    have hstep : (Λ S)° ≫ (Λ S ≫ (((∋ a)°) \ R)) ⊑ (((∋ a)°) \ R) := by
      have h := comp_mono_right hsimple (((∋ a)°) \ R)
      rw [Cat.id_comp] at h
      rwa [Cat.assoc] at h
    have h2 : S° ≫ (Λ S ≫ (((∋ a)°) \ R)) =
        (∋ a)° ≫ ((Λ S)° ≫ (Λ S ≫ (((∋ a)°) \ R))) := by
      rw [← hS', Cat.assoc]
    rw [h2]
    exact le_trans (comp_mono_left _ hstep) (leftDiv_comp_le _ _)
  · apply (map_shunt_left (Λ_is_map' S) _ _).mp
    apply (le_leftDiv_iff _ _ _).mpr
    have h3 : (∋ a)° ≫ ((Λ S)° ≫ (S° \ R)) = S° ≫ (S° \ R) := by
      rw [← Cat.assoc, hS']
    rw [h3]
    exact leftDiv_comp_le _ _

/-- **(7.5)**: `min R·ΛS = S ∩ (R/S°)`, mirrored: `A S ≫ minRel R = S ∩ (S° \ R)`. -/
public theorem Λ_comp_minRel (S : b ⟶ a) (R : a ⟶ a) :
    Λ S ≫ minRel R = S ∩ (S° \ R) := by
  show Λ S ≫ (∋ a ∩ (((∋ a)°) \ R)) = S ∩ (S° \ R)
  rw [simple_dist_inter (Λ_is_map' S).2, Λ_eps_eq', Λ_comp_lb]

/-- The universal property of (7.5), B&dM's "universal property of min":
    `X ⊑ min R·ΛS ⟺ X ⊑ S ∧ X·S° ⊑ R`, mirrored (`X·S°` becomes `S° ≫ X`). -/
public theorem le_Λ_comp_minRel_iff {S : b ⟶ a} {R : a ⟶ a} {X : b ⟶ a} :
    X ⊑ Λ S ≫ minRel R ↔ X ⊑ S ∧ S° ≫ X ⊑ R := by
  rw [Λ_comp_minRel]
  constructor
  · intro h
    refine ⟨le_trans h (inter_lb_left _ _), ?_⟩
    exact le_trans (comp_mono_left _ (le_trans h (inter_lb_right _ _))) (leftDiv_comp_le _ _)
  · rintro ⟨h1, h2⟩
    exact le_inter h1 ((le_leftDiv_iff _ _ _).mpr h2)

/-- **(7.4)**: `min R·τ = id ∩ R`, mirrored: the minimum of a singleton is its sole
    inhabitant precisely on the reflexive part of `R` ((7.5) at `S := id`). -/
theorem singletonMap_comp_minRel (R : a ⟶ a) :
    singletonMap ≫ minRel R = Cat.id a ∩ R := by
  show Λ (Cat.id a) ≫ minRel R = Cat.id a ∩ R
  rw [Λ_comp_minRel, recip_id, leftDiv_id]

/-! ## (7.1)/(7.3): lower-bound laws (book p.166) -/

/-- **(7.1)**: `τ·(R/∋) = R`, mirrored: `singletonMap ≫ ((∋a)° \ R) = R`. -/
theorem singletonMap_comp_lb (R : a ⟶ a) : singletonMap ≫ (((∋ a)°) \ R) = R := by
  show Λ (Cat.id a) ≫ (((∋ a)°) \ R) = R
  rw [Λ_comp_lb, recip_id, leftDiv_id]

/-- **(7.3)**: `(R/∋)·union = (R/∋)/∋`, mirrored: `bigUnion ≫ ((∋a)° \ R) =
    ((∋[a])° \ ((∋a)° \ R))`, via `bigUnion = A(∋[a]≫∋a)`, (7.2), and `leftDiv_comp`. -/
theorem bigUnion_comp_lb (R : a ⟶ a) :
    bigUnion ≫ (((∋ a)°) \ R) =
      (((∋ (PowerAllegory.powerObj a))°) \ (((∋ a)°) \ R)) := by
  show Λ (∋ (PowerAllegory.powerObj a) ≫ ∋ a) ≫ (((∋ a)°) \ R) =
      (((∋ (PowerAllegory.powerObj a))°) \ (((∋ a)°) \ R))
  rw [Λ_comp_lb, Allegory.recip_comp, leftDiv_comp]

/-! ## (7.6): the context rule (book pp.166-167) -/

/-- **(7.6)**, the context rule: minimizing `R` versus minimizing `R` restricted to the
    domain-of-definition of `S` (i.e. `R ∩ S°S`) agree once composed with `ΛS`, mirrored
    `A S ≫ minRel (R ∩ (S°≫S)) = A S ≫ minRel R`.  Via (7.5) on both sides, reducing to
    `S ∩ ((S° \ R) ∩ (S° \ (S°≫S))) = S ∩ (S° \ R)`, which holds because
    `S ⊑ (S° \ (S°≫S))` (the numerator `S°≫S` trivially contains `S°≫S`). -/
public theorem Λ_comp_minRel_context (S : b ⟶ a) (R : a ⟶ a) :
    Λ S ≫ minRel (R ∩ (S° ≫ S)) = Λ S ≫ minRel R := by
  have hstep : S ⊑ ((S°) \ (S° ≫ S)) := (le_leftDiv_iff S (S°) (S° ≫ S)).mpr (le_refl _)
  rw [Λ_comp_minRel, Λ_comp_minRel, leftDiv_inter, Allegory.inter_assoc]
  exact inter_eq_left (le_trans (inter_lb_left _ _) hstep)

/-! ## Ex 7.7: the pairing principle (`(∋a)°≫∋a = topHom a a`) -/

/-- **Ex 7.7**: `∋°·∋ = ⊤`, mirrored: `(∋ a)° ≫ ∋ a = topHom a a`.  The `⊑` half is
    `le_Sup trivial` (any hom is `⊑` the top).  For `⊒`: with `f := A ⊤` (so `f ≫ ∋ a = ⊤` and
    `f` is a map), `⊤ ⊑
    ⊤≫⊤ = ⊤°≫⊤ = (f≫∋a)°≫(f≫∋a) = (∋a)°≫(f°≫f)≫∋a ⊑ (∋a)°≫∋a` (`f°≫f ⊑ id` by `Simple f`). -/
theorem recip_eps_comp_eps (a : 𝒜) : (∋ a)° ≫ ∋ a = topHom a a := by
  apply le_antisymm
  · exact LocallyCompleteDistributiveAllegory.le_Sup trivial
  · let f := Λ (topHom a a)
    have hfeq : topHom a a = f ≫ ∋ a := (Λ_eps_eq' (topHom a a)).symm
    have hsimple : f° ≫ f ⊑ Cat.id (PowerAllegory.powerObj a) := (Λ_is_map' (topHom a a)).2
    have h1 : Cat.id a ⊑ topHom a a := LocallyCompleteDistributiveAllegory.le_Sup trivial
    have h2 : topHom a a ⊑ topHom a a ≫ topHom a a := by
      have h2a := comp_mono_right h1 (topHom a a)
      rwa [Cat.id_comp] at h2a
    have heq : topHom a a ≫ topHom a a = (∋ a)° ≫ (f° ≫ f) ≫ ∋ a := by
      calc topHom a a ≫ topHom a a
          = (topHom a a)° ≫ topHom a a := by rw [recip_topHom]
        _ = (f ≫ ∋ a)° ≫ (f ≫ ∋ a) := by rw [hfeq]
        _ = (∋ a)° ≫ (f° ≫ f) ≫ ∋ a := by rw [Allegory.recip_comp, Cat.assoc, Cat.assoc]
    rw [heq] at h2
    have h6a := comp_mono_right hsimple (∋ a)
    rw [Cat.id_comp] at h6a
    exact le_trans h2 (comp_mono_left ((∋ a)°) h6a)

/-- **Ex 7.7**: `min R = ∈ ⟺ R = ⊤`, mirrored: `minRel R = ∋ a ↔ R = topHom a a`.
    (→): from `minRel R = ∋ a`, the defining bound `(∋a)°≫minRel R ⊑ R` becomes
    `(∋a)°≫∋a ⊑ R`, i.e. (Ex 7.7 above) `⊤ ⊑ R`, forcing `R = ⊤`.
    (←): at `R = ⊤`, `((∋a)° \ ⊤) = ⊤` (both bounds are `le_Sup trivial`), so
    `minRel ⊤ = ∋a ∩ ⊤ = ∋a`. -/
theorem minRel_eq_eps_iff (R : a ⟶ a) : minRel R = ∋ a ↔ R = topHom a a := by
  constructor
  · intro h
    have h2 : (∋ a)° ≫ ∋ a ⊑ R := by
      have hle : (∋ a)° ≫ minRel R ⊑ R :=
        le_trans (comp_mono_left _ (show minRel R ⊑ (((∋ a)°) \ R) from inter_lb_right _ _))
          (leftDiv_comp_le _ R)
      rwa [h] at hle
    rw [recip_eps_comp_eps] at h2
    exact le_antisymm (LocallyCompleteDistributiveAllegory.le_Sup trivial) h2
  · intro h
    subst h
    show ∋ a ∩ (((∋ a)°) \ (topHom a a)) = ∋ a
    have hdiv : (((∋ a)°) \ (topHom a a)) = topHom (PowerAllegory.powerObj a) a :=
      le_antisymm (LocallyCompleteDistributiveAllegory.le_Sup trivial)
        ((le_leftDiv_iff _ _ _).mpr (LocallyCompleteDistributiveAllegory.le_Sup trivial))
    rw [hdiv]
    exact inter_eq_left (LocallyCompleteDistributiveAllegory.le_Sup trivial)

/-! ## Preorder lemmas (Ex 7.5, Ex 7.6, Ex 7.10, Ex 7.14, Ex 7.11) -/

/-- **Ex 7.5**: `R·(R/∋) = R/∋` for `R` a preorder, mirrored `((∋a)° \ R) ≫ R =
    ((∋a)° \ R)`.  `⊑`: `(∋a)°≫(lb≫R) = ((∋a)°≫lb)≫R ⊑ R≫R ⊑ R`.  `⊒`: `lb = lb≫id ⊑
    lb≫R` from `id ⊑ R`. -/
theorem comp_lb_of_preorder {R : a ⟶ a} (htrans : R ≫ R ⊑ R) (hrefl : Cat.id a ⊑ R) :
    (((∋ a)°) \ R) ≫ R = (((∋ a)°) \ R) := by
  apply le_antisymm
  · apply (le_leftDiv_iff _ _ _).mpr
    rw [← Cat.assoc]
    exact le_trans (comp_mono_right (leftDiv_comp_le ((∋ a)°) R) R) htrans
  · have h := comp_mono_left (((∋ a)°) \ R) hrefl
    rwa [Cat.comp_id] at h

/-- **Ex 7.10** (easy half): `min` is monotone, mirrored `R ⊑ S → minRel R ⊑ minRel S`. -/
theorem minRel_mono {R S : a ⟶ a} (h : R ⊑ S) : minRel R ⊑ minRel S := by
  show (∋ a ∩ (((∋ a)°) \ R) : PowerAllegory.powerObj a ⟶ a) ⊑ ∋ a ∩ (((∋ a)°) \ S)
  exact inter_mono (le_refl _) (leftDiv_mono_right _ h)

-- The converse of `minRel_mono` (`min R ⊑ min S → R ⊑ S`, for reflexive `R,S`) is Ex 7.10's
-- hard half; it needs the TABULATION machinery of Ex 7.8/7.9 (pairing `h = Λ(f∪g)`), which
-- is out of scope here (see the block note before §(7.12) below).  DROPPED.

/-- **Ex 7.6**: `min` distributes over `∩`, mirrored `minRel (R∩S) = minRel R ∩ minRel S`. -/
theorem minRel_inter (R S : a ⟶ a) : minRel (R ∩ S) = minRel R ∩ minRel S := by
  apply le_antisymm
  · exact le_inter (minRel_mono (inter_lb_left R S)) (minRel_mono (inter_lb_right R S))
  · show ((∋ a ∩ (((∋ a)°) \ R)) ∩ (∋ a ∩ (((∋ a)°) \ S)) :
        PowerAllegory.powerObj a ⟶ a) ⊑ ∋ a ∩ (((∋ a)°) \ (R ∩ S))
    rw [leftDiv_inter]
    apply le_inter
    · exact le_trans (inter_lb_left _ _) (inter_lb_left _ _)
    · exact le_inter (le_trans (inter_lb_left _ _) (inter_lb_right _ _))
                      (le_trans (inter_lb_right _ _) (inter_lb_right _ _))

/-- **Ex 7.14**: `max R·ΛR = R ∩ R°` for `R` a preorder, mirrored `A R ≫ maxRel R = R ∩ R°`.
    Via (7.5), `A R ≫ minRel R° = R ∩ (R° \ R°)`, and `(R° \ R°) = R°` (`⊑`: `lD = id≫lD
    ⊑ R°≫lD ⊑ R°`; `⊒`: `R°≫R° ⊑ R°` is the converse of `htrans`). -/
theorem Λ_comp_maxRel_of_preorder {R : a ⟶ a} (htrans : R ≫ R ⊑ R) (hrefl : Cat.id a ⊑ R) :
    Λ R ≫ maxRel R = R ∩ R° := by
  show Λ R ≫ minRel R° = R ∩ R°
  rw [Λ_comp_minRel]
  have hld : ((R°) \ (R°)) = R° := by
    apply le_antisymm
    · have hidR : Cat.id a ⊑ R° := by
        have h := recip_mono hrefl; rwa [recip_id] at h
      have h1 : ((R°) \ (R°)) ⊑ R° ≫ ((R°) \ (R°)) := by
        have h1a := comp_mono_right hidR ((R°) \ (R°))
        rwa [Cat.id_comp] at h1a
      exact le_trans h1 (leftDiv_comp_le (R°) (R°))
    · apply (le_leftDiv_iff _ _ _).mpr
      have h := recip_mono htrans
      rwa [Allegory.recip_comp] at h
  rw [hld]

/-- **Ex 7.11** (one direction): if `R` is antisymmetric then `min R` is simple, mirrored
    `Simple (minRel R)`.  Bound `(minRel R)°≫minRel R ⊑ (L°≫∋a) ∩ ((∋a)°≫L)` (`L := ((∋a)° \ R)`) via the cross terms of `(∋a∩L)°≫(∋a∩L)`; the second factor `⊑ R`
    (`leftDiv_comp_le`), the first `= ((∋a)°≫L)° ⊑ R°` (`recip_mono` of the second); so the
    whole thing `⊑ R∩R° ⊑ id` by antisymmetry.  The CONVERSE needs tabulations — DROPPED. -/
theorem minRel_simple_of_antisymmetric {R : a ⟶ a} (h : AntiSymmetric R) : Simple (minRel R) := by
  show (minRel R)° ≫ minRel R ⊑ Cat.id a
  have hE : (minRel R)° ≫ minRel R
      ⊑ ((((∋ a)°) \ R)° ≫ ∋ a) ∩ ((∋ a)° ≫ (((∋ a)°) \ R)) := by
    show ((∋ a ∩ (((∋ a)°) \ R))° ≫ (∋ a ∩ (((∋ a)°) \ R)) : a ⟶ a)
        ⊑ ((((∋ a)°) \ R)° ≫ ∋ a) ∩ ((∋ a)° ≫ (((∋ a)°) \ R))
    rw [Allegory.recip_inter]
    apply le_inter
    · exact le_trans (comp_mono_right (inter_lb_right ((∋ a)°) ((((∋ a)°) \ R)°)) _)
                      (comp_mono_left _ (inter_lb_left (∋ a) (((∋ a)°) \ R)))
    · exact le_trans (comp_mono_right (inter_lb_left ((∋ a)°) ((((∋ a)°) \ R)°)) _)
                      (comp_mono_left _ (inter_lb_right (∋ a) (((∋ a)°) \ R)))
  have hsecond : (∋ a)° ≫ (((∋ a)°) \ R) ⊑ R := leftDiv_comp_le ((∋ a)°) R
  have hfirst : (((∋ a)°) \ R)° ≫ ∋ a ⊑ R° := by
    have hr := recip_mono hsecond
    rwa [Allegory.recip_comp, Allegory.recip_recip] at hr
  have hfinal : (minRel R)° ≫ minRel R ⊑ R° ∩ R := le_trans hE (inter_mono hfirst hsecond)
  rw [Allegory.inter_comm] at hfinal
  exact le_trans hfinal h

/-! ## Ex 7.1/7.2: the subset relation (book p.169) -/

/-- **B&dM p.169**: `subset = ∈\∈`, mirrored `(∋ a) / (∋ a)` — which is LITERALLY Freyd's
    `powerOrder` (§2.442, `Freyd.S2_4`); `subsetRel` is the B&dM-facing alias for it, kept
    definitional so every lemma transfers both ways for free. -/
@[expose] public def subsetRel (a : 𝒜) : PowerAllegory.powerObj a ⟶ PowerAllegory.powerObj a := powerOrder

public theorem id_le_subsetRel : Cat.id (PowerAllegory.powerObj a) ⊑ subsetRel a := by
  show Cat.id (PowerAllegory.powerObj a) ⊑ (∋ a) / (∋ a)
  apply (le_div_iff _ _ _).mpr
  rw [Cat.id_comp]
  exact le_refl _

public theorem subsetRel_comp_eps_le : subsetRel a ≫ ∋ a ⊑ ∋ a := by
  show ((∋ a) / (∋ a)) ≫ ∋ a ⊑ ∋ a
  exact div_self_comp_le (∋ a)

/-- **Ex 7.1** mirrored: `∋°\(R/∋)` is unaffected by intersecting with the subset order,
    `(subsetRel a)°≫leftDiv(∋a)°R = leftDiv(∋a)°R`.  `⊒`: `lb = id≫lb ⊑ subset°≫lb` (`id ⊑
    subset`).  `⊑`: `∋°≫subset°≫lb = (subset≫∋)°≫lb ⊑ ∋°≫lb ⊑ R` (`subsetRel_comp_eps_le`). -/
theorem recip_subsetRel_comp_lb (R : a ⟶ a) :
    (subsetRel a)° ≫ (((∋ a)°) \ R) = (((∋ a)°) \ R) := by
  apply le_antisymm
  · apply (le_leftDiv_iff _ _ _).mpr
    have hstep2 : (subsetRel a ≫ ∋ a)° ⊑ (∋ a)° := recip_mono subsetRel_comp_eps_le
    have heq : (∋ a)° ≫ ((subsetRel a)° ≫ (((∋ a)°) \ R))
        = (subsetRel a ≫ ∋ a)° ≫ (((∋ a)°) \ R) := by
      rw [← Cat.assoc, Allegory.recip_comp]
    rw [heq]
    exact le_trans (comp_mono_right hstep2 _) (leftDiv_comp_le _ _)
  · have hid : Cat.id (PowerAllegory.powerObj a) ⊑ (subsetRel a)° := by
      have h := recip_mono (id_le_subsetRel (a := a)); rwa [recip_id] at h
    have h2 := comp_mono_right hid (((∋ a)°) \ R)
    rwa [Cat.id_comp] at h2

/-- **Ex 7.2** mirrored, the `⊑` half: `existsImage R ≫ subsetRel b ⊑ (∋a≫R)/∋b`. -/
theorem existsImage_comp_subsetRel_le (R : a ⟶ b) :
    existsImage R ≫ subsetRel b ⊑ (∋ a ≫ R) / (∋ b) := by
  show existsImage R ≫ ((∋ b) / (∋ b)) ⊑ (∋ a ≫ R) / (∋ b)
  apply (le_div_iff _ _ _).mpr
  calc (existsImage R ≫ ((∋ b) / (∋ b))) ≫ ∋ b
      = existsImage R ≫ (((∋ b) / (∋ b)) ≫ ∋ b) := Cat.assoc _ _ _
    _ ⊑ existsImage R ≫ ∋ b := comp_mono_left _ (div_self_comp_le (∋ b))
    _ = ∋ a ≫ R := existsImage_eps R

/-- **Ex 7.2** mirrored, the `⊒` half: `(∋a≫R)/∋b ⊑ existsImage R ≫ subsetRel b`.  Shunts
    across the map `existsImage R` (`map_shunt_left`), reducing to `(existsImage R)°≫((∋a≫R)/∋b)
    ⊑ subsetRel b`, then unfolds `subsetRel b = ∋b/∋b` via `le_div_iff`: the numerator bound
    `((∋a≫R)/∋b)≫∋b ⊑ ∋a≫R` (`DivisionAllegory.div_comp_le`) composed with `(existsImage R)°`
    lands on `(existsImage R)°≫(∋a≫R) = (existsImage R)°≫(existsImage R≫∋b) ⊑ id≫∋b = ∋b`
    (`existsImage_eps` + `Simple (existsImage R)`). -/
theorem existsImage_comp_subsetRel_ge (R : a ⟶ b) :
    (∋ a ≫ R) / (∋ b) ⊑ existsImage R ≫ subsetRel b := by
  have hEMap : Map (existsImage R) := Λ_is_map' _
  apply (map_shunt_left hEMap _ _).mp
  show (existsImage R)° ≫ ((∋ a ≫ R) / (∋ b)) ⊑ (∋ b) / (∋ b)
  apply (le_div_iff _ _ _).mpr
  have hd : ((∋ a ≫ R) / (∋ b)) ≫ ∋ b ⊑ ∋ a ≫ R := DivisionAllegory.div_comp_le _ _
  have hsimp : (existsImage R)° ≫ existsImage R ⊑ Cat.id (PowerAllegory.powerObj b) :=
    hEMap.2
  have hb1 : ((existsImage R)° ≫ ((∋ a ≫ R) / (∋ b))) ≫ ∋ b
      ⊑ (existsImage R)° ≫ (∋ a ≫ R) := by
    rw [Cat.assoc]
    exact comp_mono_left _ hd
  have hb2 : (existsImage R)° ≫ (∋ a ≫ R) ⊑ ∋ b := by
    rw [← existsImage_eps R, ← Cat.assoc]
    have h := comp_mono_right hsimp (∋ b)
    rwa [Cat.id_comp] at h
  exact le_trans hb1 hb2

/-- **Ex 7.2** mirrored (full equality): `existsImage R ≫ subsetRel b = (∋a≫R)/∋b`. -/
theorem existsImage_comp_subsetRel (R : a ⟶ b) :
    existsImage R ≫ subsetRel b = (∋ a ≫ R) / (∋ b) :=
  le_antisymm (existsImage_comp_subsetRel_le R) (existsImage_comp_subsetRel_ge R)

/-! ## (7.10)/(7.11): fusion with the power functor and distribution over union

    Uses `powerRel` (`AOP.A5_4`, the Egli–Milner lifting `PR`), specifically its
    "term₁ cancellation" `powerRel_term1_cancel : (∋a)°≫powerRel R ⊑ R≫(∋b)°` (the first
    Egli–Milner conjunct, `inter_lb_left` of `powerRel`'s definition) and its lax-naturality
    of `∈`, `powerRel_eps_lax : powerRel R≫∋b ⊑ ∋a≫R`. -/

/-- **(7.10)**: `min R·P S ⊆ (∈·S) ∩ (R/S·∋)`, mirrored: `powerRel S ≫ minRel R ⊑ (∋b≫S) ∩
    ((∋b)° \ (S≫R))`.  (i) `powerRel S≫minRel R ⊑ powerRel S≫∋a ⊑ ∋b≫S` (`inter_lb_left`,
    `powerRel_eps_lax`).  (ii) `(∋b)°≫(powerRel S≫minRel R) = ((∋b)°≫powerRel S)≫minRel R ⊑
    (S≫(∋a)°)≫minRel R = S≫((∋a)°≫minRel R) ⊑ S≫R` (`powerRel_term1_cancel`, then
    `(∋a)°≫minRel R ⊑ R` from `inter_lb_right`+`leftDiv_comp_le`). -/
public theorem powerRel_comp_minRel_le (S : b ⟶ a) (R : a ⟶ a) :
    powerRel S ≫ minRel R ⊑ (∋ b ≫ S) ∩ (((∋ b)°) \ (S ≫ R)) := by
  have haR : (∋ a)° ≫ minRel R ⊑ R :=
    le_trans (comp_mono_left _ (show minRel R ⊑ (((∋ a)°) \ R) from inter_lb_right _ _))
      (leftDiv_comp_le _ R)
  apply le_inter
  · exact le_trans (comp_mono_left _ (show minRel R ⊑ ∋ a from inter_lb_left _ _)) (powerRel_eps_lax S)
  · apply (le_leftDiv_iff _ _ _).mpr
    have hcancel : (∋ b)° ≫ powerRel S ⊑ S ≫ (∋ a)° := powerRel_term1_cancel S
    have e1 : (∋ b)° ≫ (powerRel S ≫ minRel R) = ((∋ b)° ≫ powerRel S) ≫ minRel R := by
      rw [Cat.assoc]
    rw [e1]
    have hstep1 : ((∋ b)° ≫ powerRel S) ≫ minRel R ⊑ (S ≫ (∋ a)°) ≫ minRel R :=
      comp_mono_right hcancel _
    have hstep2 : (S ≫ (∋ a)°) ≫ minRel R ⊑ S ≫ R := by
      rw [Cat.assoc]; exact comp_mono_left S haR
    exact le_trans hstep1 hstep2

/-- **(7.11)** mirrored (for a transitive `R`): `min R·P(min R) ⊆ min R·union`, mirrored
    `powerRel (minRel R) ≫ minRel R ⊑ bigUnion ≫ minRel R`, via `bigUnion = A(∋[a]≫∋a)` and
    `le_A_comp_minRel_iff`.  Component (i): `powerRel(min R)·min R ⊑ ∋[a]·∋a` chains
    `inter_lb_left` and `powerRel_eps_lax` at `min R`.  Component (ii):
    `(∋[a]·∋a)°·(powerRel(min R)·min R) ⊑ R` chains `powerRel_term1_cancel (minRel R)` with
    the `haR` bound twice and `htrans`. -/
theorem powerRel_minRel_le_bigUnion {R : a ⟶ a} (htrans : R ≫ R ⊑ R) :
    powerRel (minRel R) ≫ minRel R ⊑ bigUnion ≫ minRel R := by
  show powerRel (minRel R) ≫ minRel R
      ⊑ Λ (∋ (PowerAllegory.powerObj a) ≫ ∋ a) ≫ minRel R
  have hb : (∋ a)° ≫ minRel R ⊑ R :=
    le_trans (comp_mono_left _ (show minRel R ⊑ (((∋ a)°) \ R) from inter_lb_right _ _))
      (leftDiv_comp_le _ R)
  have hi : powerRel (minRel R) ≫ minRel R ⊑ ∋ (PowerAllegory.powerObj a) ≫ ∋ a := by
    have s1 : powerRel (minRel R) ≫ minRel R ⊑ powerRel (minRel R) ≫ ∋ a :=
      comp_mono_left _ (show minRel R ⊑ ∋ a from inter_lb_left _ _)
    have s2 : powerRel (minRel R) ≫ ∋ a ⊑ ∋ (PowerAllegory.powerObj a) ≫ minRel R :=
      powerRel_eps_lax (minRel R)
    have s3 : ∋ (PowerAllegory.powerObj a) ≫ minRel R ⊑ ∋ (PowerAllegory.powerObj a) ≫ ∋ a :=
      comp_mono_left _ (show minRel R ⊑ ∋ a from inter_lb_left _ _)
    exact le_trans s1 (le_trans s2 s3)
  have hii : (∋ (PowerAllegory.powerObj a) ≫ ∋ a)° ≫ (powerRel (minRel R) ≫ minRel R) ⊑ R := by
    have hcancel : (∋ (PowerAllegory.powerObj a))° ≫ powerRel (minRel R) ⊑ minRel R ≫ (∋ a)° :=
      powerRel_term1_cancel (minRel R)
    have hcombined : ((∋ (PowerAllegory.powerObj a))° ≫ powerRel (minRel R)) ≫ minRel R
        ⊑ minRel R ≫ R := by
      have hstepA : ((∋ (PowerAllegory.powerObj a))° ≫ powerRel (minRel R)) ≫ minRel R
          ⊑ (minRel R ≫ (∋ a)°) ≫ minRel R := comp_mono_right hcancel _
      have hstepB : (minRel R ≫ (∋ a)°) ≫ minRel R ⊑ minRel R ≫ R := by
        rw [Cat.assoc]; exact comp_mono_left _ hb
      exact le_trans hstepA hstepB
    have e1 : (∋ (PowerAllegory.powerObj a) ≫ ∋ a)° ≫ (powerRel (minRel R) ≫ minRel R)
        = (∋ a)° ≫ (((∋ (PowerAllegory.powerObj a))° ≫ powerRel (minRel R)) ≫ minRel R) := by
      rw [Allegory.recip_comp, Cat.assoc, Cat.assoc]
    rw [e1]
    have hfin : (∋ a)° ≫ (((∋ (PowerAllegory.powerObj a))° ≫ powerRel (minRel R)) ≫ minRel R)
        ⊑ (∋ a)° ≫ (minRel R ≫ R) := comp_mono_left _ hcombined
    have e2 : (∋ a)° ≫ (minRel R ≫ R) = ((∋ a)° ≫ minRel R) ≫ R := by rw [Cat.assoc]
    rw [e2] at hfin
    exact le_trans hfin (le_trans (comp_mono_right hb R) htrans)
  exact le_Λ_comp_minRel_iff.mpr ⟨hi, hii⟩

-- (7.12), (7.8), the (7.9) equality, Ex 7.3/7.4, Ex 7.8/7.9/7.16/7.17/7.18, and
-- well-boundedness (Ex 7.26-7.32) are DROPPED here.  Ex 7.8/7.9/7.18/7.26 are TABULATION
-- walls: B&dM's argument pairs two maps `f, g : c ⟶ a` into `h := Λ(f∪g) : c ⟶ PowerAllegory
-- .powerObj a` and reasons about the resulting two-element sets, which needs a tabular
-- setting (`f,g` jointly monic factoring a relation) not assumed by `UnguardedPowerLCDA`.
-- Ex 7.3/7.4/7.16/7.17 and the rest of well-boundedness build on that pairing or on
-- `existsImage = powerRel` restricted to maps (unproven here); (7.12)/(7.8)/(7.9) likewise
-- chain through the tabulation-dependent facts.  All left as future work once a tabular
-- unitary layer (as in `Freyd.S2_218_Tabular`) is threaded through chapter 7.

/-! ## Ex 7.19/7.20: minimal elements -/

/-- **Ex 7.19** mirrored: `mnl R := min (R° ⇨ R)`, the minimum under the "R-incomparable-or-
    R-below" preorder — an element of `x` minimal w.r.t. `R` restricted to `x`. -/
def mnlRel (R : a ⟶ a) : PowerAllegory.powerObj a ⟶ a := minRel (R° ⇨ R)

/-- **Ex 7.19** (first part): `id ⊑ R° ⇨ R`, i.e. every element is `(R°⇨R)`-related to
    itself.  Via `le_impl_iff`: `id ∩ R° ⊑ R`.  Since `id∩R°` is coreflexive, it is
    symmetric (`coreflexive_symmetric_idempotent`), so `id∩R° = (id∩R°)° = id∩R ⊑ R`. -/
theorem id_le_impl_recip (R : a ⟶ a) : Cat.id a ⊑ R° ⇨ R := by
  apply (le_impl_iff _ _ _).mpr
  have hcoref : Coreflexive (Cat.id a ∩ R°) := inter_lb_left _ _
  have hsym : (Cat.id a ∩ R°)° = Cat.id a ∩ R° :=
    symmetric_eq (coreflexive_symmetric_idempotent hcoref).1
  have hunfold : (Cat.id a ∩ R°)° = Cat.id a ∩ R := by
    rw [Allegory.recip_inter, recip_id, Allegory.recip_recip]
  have heq : Cat.id a ∩ R° = Cat.id a ∩ R := by rw [← hsym]; exact hunfold
  rw [heq]
  exact inter_lb_right _ _

/-- **Ex 7.20** (first part): `min R ⊑ mnl R`, mirrored `minRel R ⊑ mnlRel R`.  Via
    `le_minRel_iff.mpr`: membership is inherited from `minRel R`'s own bound, and the
    lower-bound half `(∋a)°≫minRel R ⊑ R° ⇨ R` follows from `(∋a)°≫minRel R ⊑ R`
    (`inter_lb_right`+`leftDiv_comp_le`) via `le_impl_iff` and `inter_lb_left`. -/
theorem minRel_le_mnlRel (R : a ⟶ a) : minRel R ⊑ mnlRel R := by
  show minRel R ⊑ minRel (R° ⇨ R)
  apply le_minRel_iff.mpr
  refine ⟨show minRel R ⊑ ∋ a from inter_lb_left _ _, ?_⟩
  have hb : (∋ a)° ≫ minRel R ⊑ R :=
    le_trans (comp_mono_left _ (show minRel R ⊑ (((∋ a)°) \ R) from inter_lb_right _ _))
      (leftDiv_comp_le _ R)
  exact (le_impl_iff _ _ _).mpr (le_trans (inter_lb_left _ _) hb)

end Freyd.Alg
