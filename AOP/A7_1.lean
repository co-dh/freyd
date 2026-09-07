/-
  Bird & de Moor, *Algebra of Programming* §7.1  Minimum and maximum (book pp. 165-172)
  — CORE (`est`, the universal properties, and (7.5)).

  B&dM keep two operators, `min R = ∈ ∩ (R/∋)` and `max R = min R°`; the note keeps ONE,
  `est(R) ≜ ∋ ∩ (∈ \ R°)`, so that `est shorter` is the shortest element and `est longer`
  the longest.  `est R` is B&dM's `max R`, and B&dM's `min R` is `est (R°)`.

  MIRRORING (diagram order, B&dM `X·Y` = Freyd `Y ≫ X`):
  - B&dM `∈ : A ← PA` is Freyd's `∋ a : powerObj a ⟶ a`; B&dM `∋ = ∈°` is Freyd `(∋ a)°`.
  - B&dM division `R/S` (UP: `X ⊆ R/S ⟺ X·S ⊆ R`) mirrors to Freyd `(S \ R)`
    (`le_leftDiv_iff : T ⊑ (S \ R) ↔ S ≫ T ⊑ R`); B&dM `S\R` mirrors to Freyd `R / S`.
  - Hence `est R = ∋ ∩ (∈ \ R°)` mirrors to `est R = ∋ a ∩ (((∋ a)°) \ R°)`.

  Setting: `UnguardedPowerLCDA` (`AOP.A6_2`) — the chapter-6/7 ambient class giving the
  power operations, division, and complete hom-lattices in one diamond-safe bundle.
-/
module

public import AOP.A6_2
public import AOP.A5_4

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {A B : 𝒜}

-- (The generic laws `leftDiv_id`, `leftDiv_comp`, `leftDiv_inter` were hoisted to their
-- canonical home `Freyd.S2_3` at collection.)

/-! ## `est R` (book p.166's `max`) -/

/-- The note's one operator `est(R) ≜ ∋ ∩ (∈ \ R°)` (with `∈ = ∋°`): `xss est(R) x` iff
    `x ∈ xss` and `x R y` for every `y ∈ xss`. -/
@[expose] public def est (R : A ⟶ A) : PowerAllegory.powerObj A ⟶ A :=
  ∋ A ∩ (((∋ A)°) \ R°)

/-- The note's call-style spelling `est(R)`. -/
notation:max "est(" R ")" => est R

/-- The universal property of `est` (book p.166's for `min`, at `R°`): `X ⊑ est R ⟺ X ⊑ ∈ ∧
    X·∋ ⊑ R°`, mirrored (`X·∋` becomes `(∋ a)° ≫ X`). -/
public theorem le_est_iff {R : A ⟶ A} {X : PowerAllegory.powerObj A ⟶ A} :
    X ⊑ est R ↔ X ⊑ ∋ A ∧ (∋ A)° ≫ X ⊑ R° := by
  constructor
  · intro h
    refine ⟨le_trans h (show est R ⊑ ∋ A from inter_lb_left _ _), ?_⟩
    exact le_trans (comp_mono_left _ (le_trans h
      (show est R ⊑ (((∋ A)°) \ R°) from inter_lb_right _ _))) (leftDiv_comp_le _ _)
  · rintro ⟨h1, h2⟩
    exact le_inter h1 ((le_leftDiv_iff _ _ _).mpr h2)

/-- The `est` bound as a composition: `(∋ a)°·est R ⊑ R°` — the `est` element of a set is
    `R`-above every member.  Just the second half of `est`'s universal property applied to
    `est R` itself; companion to `AOP.A8_1`'s `recip_eps_comp_thinRel_le` for `thin`. -/
public theorem recip_eps_comp_est_le (R : A ⟶ A) : (∋ A)° ≫ est R ⊑ R° :=
  (le_est_iff.mp (le_refl (est R))).2

/-! ## (7.5) and its universal property

  The workhorse: composing `est R` with the power transpose of `S` computes extrema over
  the `S`-image.  Key step: `Λ S` transports bounds, `Λ S ≫ (R/∋) = R/S°` mirrored. -/

/-- `ΛS·(R/∋) = R/S°` mirrored: `Λ S ≫ ((∋ a)° \ R) = (S° \ R)` (B&dM (7.2)).
    Stated for a numerator of ARBITRARY target type `c` — §7.1 uses it at `c := a`
    (`R` an order on `a`), §8.1's thinning at `c := powerObj a`. -/
public theorem Λ_comp_lb {C : 𝒜} (S : B ⟶ A) (R : A ⟶ C) :
    Λ S ≫ (((∋ A)°) \ R) = (S° \ R) := by
  have hS' : (∋ A)° ≫ (Λ S)° = S° := by rw [← Allegory.recip_comp, Λ_eps_eq']
  apply le_antisymm
  · apply (le_leftDiv_iff _ _ _).mpr
    have hsimple : (Λ S)° ≫ Λ S ⊑ Cat.id _ := (Λ_is_map' S).2
    have hstep : (Λ S)° ≫ (Λ S ≫ (((∋ A)°) \ R)) ⊑ (((∋ A)°) \ R) := by
      have h := comp_mono_right hsimple (((∋ A)°) \ R)
      rw [Cat.id_comp] at h
      rwa [Cat.assoc] at h
    have h2 : S° ≫ (Λ S ≫ (((∋ A)°) \ R)) =
        (∋ A)° ≫ ((Λ S)° ≫ (Λ S ≫ (((∋ A)°) \ R))) := by
      rw [← hS', Cat.assoc]
    rw [h2]
    exact le_trans (comp_mono_left _ hstep) (leftDiv_comp_le _ _)
  · apply (map_shunt_left (Λ_is_map' S) _ _).mp
    apply (le_leftDiv_iff _ _ _).mpr
    have h3 : (∋ A)° ≫ ((Λ S)° ≫ (S° \ R)) = S° ≫ (S° \ R) := by
      rw [← Cat.assoc, hS']
    rw [h3]
    exact leftDiv_comp_le _ _

/-- **(7.5)**: `min R·ΛS = S ∩ (R/S°)` at `R°`, mirrored: `Λ S ≫ est R = S ∩ (S° \ R°)`. -/
public theorem Λ_comp_est (S : B ⟶ A) (R : A ⟶ A) :
    Λ S ≫ est R = S ∩ (S° \ R°) := by
  show Λ S ≫ (∋ A ∩ (((∋ A)°) \ R°)) = S ∩ (S° \ R°)
  rw [simple_dist_inter (Λ_is_map' S).2, Λ_eps_eq', Λ_comp_lb]

/-- The universal property of (7.5), B&dM's "universal property of min" at `R°`:
    `X ⊑ est R·ΛS ⟺ X ⊑ S ∧ X·S° ⊑ R°`, mirrored (`X·S°` becomes `S° ≫ X`). -/
public theorem le_Λ_comp_est_iff {S : B ⟶ A} {R : A ⟶ A} {X : B ⟶ A} :
    X ⊑ Λ S ≫ est R ↔ X ⊑ S ∧ S° ≫ X ⊑ R° := by
  rw [Λ_comp_est]
  constructor
  · intro h
    refine ⟨le_trans h (inter_lb_left _ _), ?_⟩
    exact le_trans (comp_mono_left _ (le_trans h (inter_lb_right _ _))) (leftDiv_comp_le _ _)
  · rintro ⟨h1, h2⟩
    exact le_inter h1 ((le_leftDiv_iff _ _ _).mpr h2)

/-- **(7.4)**: `min R·τ = id ∩ R` at `R°`, mirrored: the `est` of a singleton is its sole
    inhabitant precisely on the reflexive part of `R` ((7.5) at `S := id`). -/
theorem singletonMap_comp_est (R : A ⟶ A) :
    singletonMap ≫ est R = Cat.id A ∩ R° := by
  show Λ (Cat.id A) ≫ est R = Cat.id A ∩ R°
  rw [Λ_comp_est, recip_id, leftDiv_id]

/-! ## (7.1)/(7.3): lower-bound laws (book p.166) -/

/-- **(7.1)**: `τ·(R/∋) = R`, mirrored: `singletonMap ≫ ((∋a)° \ R) = R`. -/
theorem singletonMap_comp_lb (R : A ⟶ A) : singletonMap ≫ (((∋ A)°) \ R) = R := by
  show Λ (Cat.id A) ≫ (((∋ A)°) \ R) = R
  rw [Λ_comp_lb, recip_id, leftDiv_id]

/-- **(7.3)**: `(R/∋)·union = (R/∋)/∋`, mirrored: `bigUnion ≫ ((∋a)° \ R) =
    ((∋[a])° \ ((∋a)° \ R))`, via `bigUnion = Λ(∋[a]≫∋a)`, (7.2), and `leftDiv_comp`. -/
theorem bigUnion_comp_lb (R : A ⟶ A) :
    bigUnion ≫ (((∋ A)°) \ R) =
      (((∋ (PowerAllegory.powerObj A))°) \ (((∋ A)°) \ R)) := by
  show Λ (∋ (PowerAllegory.powerObj A) ≫ ∋ A) ≫ (((∋ A)°) \ R) =
      (((∋ (PowerAllegory.powerObj A))°) \ (((∋ A)°) \ R))
  rw [Λ_comp_lb, Allegory.recip_comp, leftDiv_comp]

/-! ## (7.6): the context rule (book pp.166-167) -/

/-- **(7.6)**, the context rule: optimising `R` versus optimising `R` restricted to the
    domain-of-definition of `S` (i.e. `R ∩ S°S`) agree once composed with `ΛS`, mirrored
    `Λ S ≫ est (R ∩ (S°≫S)) = Λ S ≫ est R`.  Via (7.5) on both sides, reducing to
    `S ∩ ((S° \ R°) ∩ (S° \ (S°≫S)°)) = S ∩ (S° \ R°)`, which holds because
    `S ⊑ (S° \ (S°≫S)°)` (the numerator `(S°≫S)°` trivially contains `S°≫S`). -/
public theorem Λ_comp_est_context (S : B ⟶ A) (R : A ⟶ A) :
    Λ S ≫ est (R ∩ (S° ≫ S)) = Λ S ≫ est R := by
  have hstep : S ⊑ ((S°) \ ((S° ≫ S)°)) := by
    apply (le_leftDiv_iff _ _ _).mpr
    rw [Allegory.recip_comp, Allegory.recip_recip]
    exact le_refl _
  rw [Λ_comp_est, Λ_comp_est, Allegory.recip_inter, leftDiv_inter, Allegory.inter_assoc]
  exact inter_eq_left (le_trans (inter_lb_left _ _) hstep)

/-! ## Ex 7.7: the pairing principle (`(∋a)°≫∋a = topHom a a`) -/

/-- **Ex 7.7**: `∋°·∋ = ⊤`, mirrored: `(∋ a)° ≫ ∋ a = topHom a a`.  The `⊑` half is
    `le_Sup trivial` (any hom is `⊑` the top).  For `⊒`: with `f := Λ ⊤` (so `f ≫ ∋ a = ⊤` and
    `f` is a map), `⊤ ⊑
    ⊤≫⊤ = ⊤°≫⊤ = (f≫∋a)°≫(f≫∋a) = (∋a)°≫(f°≫f)≫∋a ⊑ (∋a)°≫∋a` (`f°≫f ⊑ id` by `Simple f`). -/
theorem recip_eps_comp_eps (A : 𝒜) : (∋ A)° ≫ ∋ A = topHom A A := by
  apply le_antisymm
  · exact LocallyCompleteDistributiveAllegory.le_Sup trivial
  · let f := Λ (topHom A A)
    have hfeq : topHom A A = f ≫ ∋ A := (Λ_eps_eq' (topHom A A)).symm
    have hsimple : f° ≫ f ⊑ Cat.id (PowerAllegory.powerObj A) := (Λ_is_map' (topHom A A)).2
    have h1 : Cat.id A ⊑ topHom A A := LocallyCompleteDistributiveAllegory.le_Sup trivial
    have h2 : topHom A A ⊑ topHom A A ≫ topHom A A := by
      have h2a := comp_mono_right h1 (topHom A A)
      rwa [Cat.id_comp] at h2a
    have heq : topHom A A ≫ topHom A A = (∋ A)° ≫ (f° ≫ f) ≫ ∋ A := by
      calc topHom A A ≫ topHom A A
          = (topHom A A)° ≫ topHom A A := by rw [recip_topHom]
        _ = (f ≫ ∋ A)° ≫ (f ≫ ∋ A) := by rw [hfeq]
        _ = (∋ A)° ≫ (f° ≫ f) ≫ ∋ A := by rw [Allegory.recip_comp, Cat.assoc, Cat.assoc]
    rw [heq] at h2
    have h6a := comp_mono_right hsimple (∋ A)
    rw [Cat.id_comp] at h6a
    exact le_trans h2 (comp_mono_left ((∋ A)°) h6a)

/-- **Ex 7.7**: `min R = ∈ ⟺ R = ⊤`, mirrored: `est R = ∋ a ↔ R = topHom a a`.
    (→): from `est R = ∋ a`, the defining bound `(∋a)°≫est R ⊑ R°` becomes
    `(∋a)°≫∋a ⊑ R°`, i.e. (Ex 7.7 above) `⊤ ⊑ R°`, forcing `R° = ⊤` and so `R = ⊤`.
    (←): at `R = ⊤`, `((∋a)° \ ⊤°) = ⊤` (both bounds are `le_Sup trivial`), so
    `est ⊤ = ∋a ∩ ⊤ = ∋a`. -/
public theorem est_eq_eps_iff (R : A ⟶ A) : est R = ∋ A ↔ R = topHom A A := by
  constructor
  · intro h
    have h2 : (∋ A)° ≫ ∋ A ⊑ R° := by
      have hle := recip_eps_comp_est_le R
      rwa [h] at hle
    rw [recip_eps_comp_eps] at h2
    have h3 : R° = topHom A A :=
      le_antisymm (LocallyCompleteDistributiveAllegory.le_Sup trivial) h2
    calc R = R°° := (Allegory.recip_recip R).symm
      _ = (topHom A A)° := by rw [h3]
      _ = topHom A A := recip_topHom
  · intro h
    subst h
    show ∋ A ∩ (((∋ A)°) \ ((topHom A A)°)) = ∋ A
    rw [recip_topHom]
    have hdiv : (((∋ A)°) \ (topHom A A)) = topHom (PowerAllegory.powerObj A) A :=
      le_antisymm (LocallyCompleteDistributiveAllegory.le_Sup trivial)
        ((le_leftDiv_iff _ _ _).mpr (LocallyCompleteDistributiveAllegory.le_Sup trivial))
    rw [hdiv]
    exact inter_eq_left (LocallyCompleteDistributiveAllegory.le_Sup trivial)

/-! ## Preorder lemmas (Ex 7.5, Ex 7.6, Ex 7.10, Ex 7.14, Ex 7.11) -/

/-- **Ex 7.5**: `R·(R/∋) = R/∋` for `R` a preorder, mirrored `((∋a)° \ R) ≫ R =
    ((∋a)° \ R)`.  `⊑`: `(∋a)°≫(lb≫R) = ((∋a)°≫lb)≫R ⊑ R≫R ⊑ R`.  `⊒`: `lb = lb≫id ⊑
    lb≫R` from `id ⊑ R`. -/
theorem comp_lb_of_preorder {R : A ⟶ A} (htrans : R ≫ R ⊑ R) (hrefl : Cat.id A ⊑ R) :
    (((∋ A)°) \ R) ≫ R = (((∋ A)°) \ R) := by
  apply le_antisymm
  · apply (le_leftDiv_iff _ _ _).mpr
    rw [← Cat.assoc]
    exact le_trans (comp_mono_right (leftDiv_comp_le ((∋ A)°) R) R) htrans
  · have h := comp_mono_left (((∋ A)°) \ R) hrefl
    rwa [Cat.comp_id] at h

/-- **Ex 7.10** (easy half): `est` is monotone, mirrored `R ⊑ S → est R ⊑ est S`. -/
public theorem est_mono {R S : A ⟶ A} (h : R ⊑ S) : est R ⊑ est S := by
  show (∋ A ∩ (((∋ A)°) \ R°) : PowerAllegory.powerObj A ⟶ A) ⊑ ∋ A ∩ (((∋ A)°) \ S°)
  exact inter_mono (le_refl _) (leftDiv_mono_right _ (recip_mono h))

-- The converse of `est_mono` (`est R ⊑ est S → R ⊑ S`, for reflexive `R,S`) is Ex 7.10's
-- hard half; it needs the TABULATION machinery of Ex 7.8/7.9 (pairing `h = Λ(f∪g)`), which
-- is out of scope here (see the block note before §(7.12) below).  DROPPED.

/-- **Ex 7.6**: `est` distributes over `∩`, mirrored `est (R∩S) = est R ∩ est S`. -/
theorem est_inter (R S : A ⟶ A) : est (R ∩ S) = est R ∩ est S := by
  apply le_antisymm
  · exact le_inter (est_mono (inter_lb_left R S)) (est_mono (inter_lb_right R S))
  · show ((∋ A ∩ (((∋ A)°) \ R°)) ∩ (∋ A ∩ (((∋ A)°) \ S°)) :
        PowerAllegory.powerObj A ⟶ A) ⊑ ∋ A ∩ (((∋ A)°) \ ((R ∩ S)°))
    rw [Allegory.recip_inter, leftDiv_inter]
    apply le_inter
    · exact le_trans (inter_lb_left _ _) (inter_lb_left _ _)
    · exact le_inter (le_trans (inter_lb_left _ _) (inter_lb_right _ _))
                      (le_trans (inter_lb_right _ _) (inter_lb_right _ _))

/-- **Ex 7.14**: `max R·ΛR = R ∩ R°` for `R` a preorder, mirrored `Λ R ≫ est R = R ∩ R°`.
    Via (7.5), `Λ R ≫ est R = R ∩ (R° \ R°)`, and `(R° \ R°) = R°` (`⊑`: `lD = id≫lD
    ⊑ R°≫lD ⊑ R°`; `⊒`: `R°≫R° ⊑ R°` is the converse of `htrans`). -/
theorem Λ_comp_est_of_preorder {R : A ⟶ A} (htrans : R ≫ R ⊑ R) (hrefl : Cat.id A ⊑ R) :
    Λ R ≫ est R = R ∩ R° := by
  rw [Λ_comp_est]
  have hld : ((R°) \ (R°)) = R° := by
    apply le_antisymm
    · have hidR : Cat.id A ⊑ R° := by
        have h := recip_mono hrefl; rwa [recip_id] at h
      have h1 : ((R°) \ (R°)) ⊑ R° ≫ ((R°) \ (R°)) := by
        have h1a := comp_mono_right hidR ((R°) \ (R°))
        rwa [Cat.id_comp] at h1a
      exact le_trans h1 (leftDiv_comp_le (R°) (R°))
    · apply (le_leftDiv_iff _ _ _).mpr
      have h := recip_mono htrans
      rwa [Allegory.recip_comp] at h
  rw [hld]

/-- **Ex 7.11** (one direction): if `R` is antisymmetric then `est R` is simple, mirrored
    `Simple (est R)`.  Bound `(est R)°≫est R ⊑ (L°≫∋a) ∩ ((∋a)°≫L)` (`L := ((∋a)° \ R°)`) via
    the cross terms of `(∋a∩L)°≫(∋a∩L)`; the second factor `⊑ R°` (`leftDiv_comp_le`), the
    first `= ((∋a)°≫L)° ⊑ R` (`recip_mono` of the second); so the whole thing `⊑ R∩R° ⊑ id`
    by antisymmetry.  The CONVERSE needs tabulations — DROPPED. -/
theorem est_simple_of_antisymmetric {R : A ⟶ A} (h : AntiSymmetric R) : Simple (est R) := by
  show (est R)° ≫ est R ⊑ Cat.id A
  have hE : (est R)° ≫ est R
      ⊑ ((((∋ A)°) \ R°)° ≫ ∋ A) ∩ ((∋ A)° ≫ (((∋ A)°) \ R°)) := by
    show ((∋ A ∩ (((∋ A)°) \ R°))° ≫ (∋ A ∩ (((∋ A)°) \ R°)) : A ⟶ A)
        ⊑ ((((∋ A)°) \ R°)° ≫ ∋ A) ∩ ((∋ A)° ≫ (((∋ A)°) \ R°))
    rw [Allegory.recip_inter]
    apply le_inter
    · exact le_trans (comp_mono_right (inter_lb_right ((∋ A)°) ((((∋ A)°) \ R°)°)) _)
                      (comp_mono_left _ (inter_lb_left (∋ A) (((∋ A)°) \ R°)))
    · exact le_trans (comp_mono_right (inter_lb_left ((∋ A)°) ((((∋ A)°) \ R°)°)) _)
                      (comp_mono_left _ (inter_lb_right (∋ A) (((∋ A)°) \ R°)))
  have hsecond : (∋ A)° ≫ (((∋ A)°) \ R°) ⊑ R° := leftDiv_comp_le ((∋ A)°) (R°)
  have hfirst : (((∋ A)°) \ R°)° ≫ ∋ A ⊑ R := by
    have hr := recip_mono hsecond
    rwa [Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_recip] at hr
  exact le_trans (le_trans hE (inter_mono hfirst hsecond)) h

/-! ## Ex 7.1/7.2: the subset relation (book p.169) -/

/-- **B&dM p.169**: `subset = ∈\∈`, mirrored `(∋ a) / (∋ a)` — which is LITERALLY Freyd's
    `powerOrder` (§2.442, `Freyd.S2_4`); `subsetRel` is the B&dM-facing alias for it, kept
    definitional so every lemma transfers both ways for free. -/
@[expose] public def subsetRel (A : 𝒜) : PowerAllegory.powerObj A ⟶ PowerAllegory.powerObj A := powerOrder

public theorem id_le_subsetRel : Cat.id (PowerAllegory.powerObj A) ⊑ subsetRel A := by
  show Cat.id (PowerAllegory.powerObj A) ⊑ (∋ A) / (∋ A)
  apply (le_div_iff _ _ _).mpr
  rw [Cat.id_comp]
  exact le_refl _

public theorem subsetRel_comp_eps_le : subsetRel A ≫ ∋ A ⊑ ∋ A := by
  show ((∋ A) / (∋ A)) ≫ ∋ A ⊑ ∋ A
  exact div_self_comp_le (∋ A)

/-- **Ex 7.1** mirrored: `∋°\(R/∋)` is unaffected by intersecting with the subset order,
    `(subsetRel a)°≫leftDiv(∋a)°R = leftDiv(∋a)°R`.  `⊒`: `lb = id≫lb ⊑ subset°≫lb` (`id ⊑
    subset`).  `⊑`: `∋°≫subset°≫lb = (subset≫∋)°≫lb ⊑ ∋°≫lb ⊑ R` (`subsetRel_comp_eps_le`). -/
theorem recip_subsetRel_comp_lb (R : A ⟶ A) :
    (subsetRel A)° ≫ (((∋ A)°) \ R) = (((∋ A)°) \ R) := by
  apply le_antisymm
  · apply (le_leftDiv_iff _ _ _).mpr
    have hstep2 : (subsetRel A ≫ ∋ A)° ⊑ (∋ A)° := recip_mono subsetRel_comp_eps_le
    have heq : (∋ A)° ≫ ((subsetRel A)° ≫ (((∋ A)°) \ R))
        = (subsetRel A ≫ ∋ A)° ≫ (((∋ A)°) \ R) := by
      rw [← Cat.assoc, Allegory.recip_comp]
    rw [heq]
    exact le_trans (comp_mono_right hstep2 _) (leftDiv_comp_le _ _)
  · have hid : Cat.id (PowerAllegory.powerObj A) ⊑ (subsetRel A)° := by
      have h := recip_mono (id_le_subsetRel (A := A)); rwa [recip_id] at h
    have h2 := comp_mono_right hid (((∋ A)°) \ R)
    rwa [Cat.id_comp] at h2

/-- **Ex 7.2** mirrored, the `⊑` half: `existsImage R ≫ subsetRel b ⊑ (∋a≫R)/∋b`. -/
theorem existsImage_comp_subsetRel_le (R : A ⟶ B) :
    existsImage R ≫ subsetRel B ⊑ (∋ A ≫ R) / (∋ B) := by
  show existsImage R ≫ ((∋ B) / (∋ B)) ⊑ (∋ A ≫ R) / (∋ B)
  apply (le_div_iff _ _ _).mpr
  calc (existsImage R ≫ ((∋ B) / (∋ B))) ≫ ∋ B
      = existsImage R ≫ (((∋ B) / (∋ B)) ≫ ∋ B) := Cat.assoc _ _ _
    _ ⊑ existsImage R ≫ ∋ B := comp_mono_left _ (div_self_comp_le (∋ B))
    _ = ∋ A ≫ R := existsImage_eps R

/-- **Ex 7.2** mirrored, the `⊒` half: `(∋a≫R)/∋b ⊑ existsImage R ≫ subsetRel b`.  Shunts
    across the map `existsImage R` (`map_shunt_left`), reducing to `(existsImage R)°≫((∋a≫R)/∋b)
    ⊑ subsetRel b`, then unfolds `subsetRel b = ∋b/∋b` via `le_div_iff`: the numerator bound
    `((∋a≫R)/∋b)≫∋b ⊑ ∋a≫R` (`DivisionAllegory.div_comp_le`) composed with `(existsImage R)°`
    lands on `(existsImage R)°≫(∋a≫R) = (existsImage R)°≫(existsImage R≫∋b) ⊑ id≫∋b = ∋b`
    (`existsImage_eps` + `Simple (existsImage R)`). -/
theorem existsImage_comp_subsetRel_ge (R : A ⟶ B) :
    (∋ A ≫ R) / (∋ B) ⊑ existsImage R ≫ subsetRel B := by
  have hEMap : Map (existsImage R) := Λ_is_map' _
  apply (map_shunt_left hEMap _ _).mp
  show (existsImage R)° ≫ ((∋ A ≫ R) / (∋ B)) ⊑ (∋ B) / (∋ B)
  apply (le_div_iff _ _ _).mpr
  have hd : ((∋ A ≫ R) / (∋ B)) ≫ ∋ B ⊑ ∋ A ≫ R := DivisionAllegory.div_comp_le _ _
  have hsimp : (existsImage R)° ≫ existsImage R ⊑ Cat.id (PowerAllegory.powerObj B) :=
    hEMap.2
  have hb1 : ((existsImage R)° ≫ ((∋ A ≫ R) / (∋ B))) ≫ ∋ B
      ⊑ (existsImage R)° ≫ (∋ A ≫ R) := by
    rw [Cat.assoc]
    exact comp_mono_left _ hd
  have hb2 : (existsImage R)° ≫ (∋ A ≫ R) ⊑ ∋ B := by
    rw [← existsImage_eps R, ← Cat.assoc]
    have h := comp_mono_right hsimp (∋ B)
    rwa [Cat.id_comp] at h
  exact le_trans hb1 hb2

/-- **Ex 7.2** mirrored (full equality): `existsImage R ≫ subsetRel b = (∋a≫R)/∋b`. -/
theorem existsImage_comp_subsetRel (R : A ⟶ B) :
    existsImage R ≫ subsetRel B = (∋ A ≫ R) / (∋ B) :=
  le_antisymm (existsImage_comp_subsetRel_le R) (existsImage_comp_subsetRel_ge R)

/-! ## (7.10)/(7.11): fusion with the power functor and distribution over union

    Uses `powerRel` (`AOP.A5_4`, the Egli–Milner lifting `PR`), specifically its
    "term₁ cancellation" `powerRel_term1_cancel : (∋a)°≫powerRel R ⊑ R≫(∋b)°` (the first
    Egli–Milner conjunct, `inter_lb_left` of `powerRel`'s definition) and its lax-naturality
    of `∈`, `powerRel_eps_lax : powerRel R≫∋b ⊑ ∋a≫R`. -/

/-- **(7.10)**: `min R·P S ⊆ (∈·S) ∩ (R/S·∋)` at `R°`, mirrored: `powerRel S ≫ est R ⊑ (∋b≫S) ∩
    ((∋b)° \ (S≫R°))`.  (i) `powerRel S≫est R ⊑ powerRel S≫∋a ⊑ ∋b≫S` (`inter_lb_left`,
    `powerRel_eps_lax`).  (ii) `(∋b)°≫(powerRel S≫est R) = ((∋b)°≫powerRel S)≫est R ⊑
    (S≫(∋a)°)≫est R = S≫((∋a)°≫est R) ⊑ S≫R°` (`powerRel_term1_cancel`, then
    `recip_eps_comp_est_le`). -/
public theorem powerRel_comp_est_le (S : B ⟶ A) (R : A ⟶ A) :
    powerRel S ≫ est R ⊑ (∋ B ≫ S) ∩ (((∋ B)°) \ (S ≫ R°)) := by
  have haR := recip_eps_comp_est_le R
  apply le_inter
  · exact le_trans (comp_mono_left _ (show est R ⊑ ∋ A from inter_lb_left _ _)) (powerRel_eps_lax S)
  · apply (le_leftDiv_iff _ _ _).mpr
    have hcancel : (∋ B)° ≫ powerRel S ⊑ S ≫ (∋ A)° := powerRel_term1_cancel S
    have e1 : (∋ B)° ≫ (powerRel S ≫ est R) = ((∋ B)° ≫ powerRel S) ≫ est R := by
      rw [Cat.assoc]
    rw [e1]
    have hstep1 : ((∋ B)° ≫ powerRel S) ≫ est R ⊑ (S ≫ (∋ A)°) ≫ est R :=
      comp_mono_right hcancel _
    have hstep2 : (S ≫ (∋ A)°) ≫ est R ⊑ S ≫ R° := by
      rw [Cat.assoc]; exact comp_mono_left S haR
    exact le_trans hstep1 hstep2

/-- **(7.11)** mirrored (for a transitive `R`): `min R·P(min R) ⊆ min R·union` at `R°`,
    mirrored `powerRel (est R) ≫ est R ⊑ bigUnion ≫ est R`, via `bigUnion = Λ(∋[a]≫∋a)` and
    `le_Λ_comp_est_iff`.  Component (i): `powerRel(est R)·est R ⊑ ∋[a]·∋a` chains
    `inter_lb_left` and `powerRel_eps_lax` at `est R`.  Component (ii):
    `(∋[a]·∋a)°·(powerRel(est R)·est R) ⊑ R°` chains `powerRel_term1_cancel (est R)` with
    the `hb` bound twice and `htrans` transposed. -/
public theorem powerRel_est_le_bigUnion {R : A ⟶ A} (htrans : R ≫ R ⊑ R) :
    powerRel (est R) ≫ est R ⊑ bigUnion ≫ est R := by
  show powerRel (est R) ≫ est R
      ⊑ Λ (∋ (PowerAllegory.powerObj A) ≫ ∋ A) ≫ est R
  have htrans' : R° ≫ R° ⊑ R° := by
    have h := recip_mono htrans; rwa [Allegory.recip_comp] at h
  have hb := recip_eps_comp_est_le R
  have hi : powerRel (est R) ≫ est R ⊑ ∋ (PowerAllegory.powerObj A) ≫ ∋ A := by
    have s1 : powerRel (est R) ≫ est R ⊑ powerRel (est R) ≫ ∋ A :=
      comp_mono_left _ (show est R ⊑ ∋ A from inter_lb_left _ _)
    have s2 : powerRel (est R) ≫ ∋ A ⊑ ∋ (PowerAllegory.powerObj A) ≫ est R :=
      powerRel_eps_lax (est R)
    have s3 : ∋ (PowerAllegory.powerObj A) ≫ est R ⊑ ∋ (PowerAllegory.powerObj A) ≫ ∋ A :=
      comp_mono_left _ (show est R ⊑ ∋ A from inter_lb_left _ _)
    exact le_trans s1 (le_trans s2 s3)
  have hii : (∋ (PowerAllegory.powerObj A) ≫ ∋ A)° ≫ (powerRel (est R) ≫ est R) ⊑ R° := by
    have hcancel : (∋ (PowerAllegory.powerObj A))° ≫ powerRel (est R) ⊑ est R ≫ (∋ A)° :=
      powerRel_term1_cancel (est R)
    have hcombined : ((∋ (PowerAllegory.powerObj A))° ≫ powerRel (est R)) ≫ est R
        ⊑ est R ≫ R° := by
      have hstepA : ((∋ (PowerAllegory.powerObj A))° ≫ powerRel (est R)) ≫ est R
          ⊑ (est R ≫ (∋ A)°) ≫ est R := comp_mono_right hcancel _
      have hstepB : (est R ≫ (∋ A)°) ≫ est R ⊑ est R ≫ R° := by
        rw [Cat.assoc]; exact comp_mono_left _ hb
      exact le_trans hstepA hstepB
    have e1 : (∋ (PowerAllegory.powerObj A) ≫ ∋ A)° ≫ (powerRel (est R) ≫ est R)
        = (∋ A)° ≫ (((∋ (PowerAllegory.powerObj A))° ≫ powerRel (est R)) ≫ est R) := by
      rw [Allegory.recip_comp, Cat.assoc, Cat.assoc]
    rw [e1]
    have hfin : (∋ A)° ≫ (((∋ (PowerAllegory.powerObj A))° ≫ powerRel (est R)) ≫ est R)
        ⊑ (∋ A)° ≫ (est R ≫ R°) := comp_mono_left _ hcombined
    have e2 : (∋ A)° ≫ (est R ≫ R°) = ((∋ A)° ≫ est R) ≫ R° := by rw [Cat.assoc]
    rw [e2] at hfin
    exact le_trans hfin (le_trans (comp_mono_right hb (R°)) htrans')
  exact le_Λ_comp_est_iff.mpr ⟨hi, hii⟩

/-! ## (7.11) as an EQUALITY: `P(est(R)) est(R) = P(Dom(est(R))) union est(R)`

  The `⊑` above is strict — a member set with no `est` (the empty one) empties the left side
  and not the right — and guarding the right side with the coreflexive `P(Dom(est(R)))`
  ("every member set HAS an `est`") is exactly what closes the gap. -/

/-- `dom(P S) ⊑ P(dom S)`: a set has a `P S`-image only if EVERY member has an `S`-image.
    One bound gives both halves of `powerRel (dom S)`, since `dom S` and `dom (P S)` are
    coreflexive hence symmetric, so term₁ is the converse of term₂.  That bound,
    `dom(P S)∋ ⊑ ∋ dom S`, is the codomain form of the modular law at `U := dom(P S)∋`
    (`U ⊑ U(𝟙∩U°U)`) together with `𝟙∩U°U ⊑ dom S`, which chains term₁ of `P S` on both sides
    of `U°U` and then drops the `∋°∋` left in the middle by the modular law again. -/
public theorem dom_powerRel_le {A B : 𝒜} (S : A ⟶ B) :
    dom (powerRel S) ⊑ powerRel (dom S) := by
  have hcor : dom (powerRel S) ⊑ 𝟙 (PowerAllegory.powerObj A) := dom_coreflexive _
  have hsym : (dom (powerRel S))° = dom (powerRel S) :=
    symmetric_eq (coreflexive_symmetric_idempotent hcor).1
  have hdsym : (dom S)° = dom S :=
    symmetric_eq (coreflexive_symmetric_idempotent (dom_coreflexive S)).1
  have hUeps : dom (powerRel S) ≫ ∋ A ⊑ ∋ A := by
    have h := comp_mono_right hcor (∋ A); rwa [Cat.id_comp] at h
  have hflip : (powerRel S)° ≫ ∋ A ⊑ ∋ B ≫ S° := by
    have h := recip_mono (powerRel_term1_cancel S)
    rwa [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip,
      Allegory.recip_recip] at h
  -- every member of a set that HAS a `P S`-image has an `S`-image
  have hkey : dom (powerRel S) ≫ ∋ A ⊑ ∋ A ≫ dom S := by
    have hV : (∋ A)° ≫ (dom (powerRel S) ≫ ∋ A) ⊑ S ≫ ((∋ B)° ≫ (∋ B ≫ S°)) := by
      have hdomle : dom (powerRel S) ⊑ powerRel S ≫ (powerRel S)° :=
        inter_lb_right (𝟙 (PowerAllegory.powerObj A)) (powerRel S ≫ (powerRel S)°)
      calc (∋ A)° ≫ (dom (powerRel S) ≫ ∋ A)
          ⊑ (∋ A)° ≫ ((powerRel S ≫ (powerRel S)°) ≫ ∋ A) :=
            comp_mono_left _ (comp_mono_right hdomle _)
        _ = ((∋ A)° ≫ powerRel S) ≫ ((powerRel S)° ≫ ∋ A) := by rw [Cat.assoc, Cat.assoc]
        _ ⊑ (S ≫ (∋ B)°) ≫ (∋ B ≫ S°) :=
            le_trans (comp_mono_right (powerRel_term1_cancel S) _) (comp_mono_left _ hflip)
        _ = S ≫ ((∋ B)° ≫ (∋ B ≫ S°)) := Cat.assoc _ _ _
    have hUU : (dom (powerRel S) ≫ ∋ A)° ≫ (dom (powerRel S) ≫ ∋ A)
        ⊑ S ≫ ((∋ B)° ≫ (∋ B ≫ S°)) :=
      le_trans (comp_mono_right (recip_mono hUeps) _) hV
    have hmod : (S ≫ ((∋ B)° ≫ (∋ B ≫ S°))) ∩ 𝟙 A ⊑ S ≫ S° := by
      refine le_trans (modular_le_right S ((∋ B)° ≫ (∋ B ≫ S°)) (𝟙 A)) (comp_mono_left _ ?_)
      rw [Cat.comp_id]
      exact inter_lb_right _ _
    have hcore : 𝟙 A ∩ (dom (powerRel S) ≫ ∋ A)° ≫ (dom (powerRel S) ≫ ∋ A) ⊑ dom S := by
      show _ ⊑ 𝟙 A ∩ (S ≫ S°)
      refine le_inter (inter_lb_left _ _) (le_trans (le_trans
        (le_inter (inter_lb_right _ _) (inter_lb_left _ _)) (inter_mono hUU (le_refl _))) hmod)
    have hcod : dom (powerRel S) ≫ ∋ A
        ⊑ (dom (powerRel S) ≫ ∋ A)
            ≫ (𝟙 A ∩ (dom (powerRel S) ≫ ∋ A)° ≫ (dom (powerRel S) ≫ ∋ A)) := by
      have h := modular_le_right (dom (powerRel S) ≫ ∋ A) (𝟙 A) (dom (powerRel S) ≫ ∋ A)
      rwa [Cat.comp_id, Allegory.inter_idem] at h
    exact le_trans hcod (le_trans (comp_mono_right hUeps _) (comp_mono_left _ hcore))
  have hkey' : (∋ A)° ≫ dom (powerRel S) ⊑ dom S ≫ (∋ A)° := by
    have h := recip_mono hkey
    rwa [Allegory.recip_comp, Allegory.recip_comp, hsym, hdsym] at h
  show dom (powerRel S) ⊑ ((∋ A)° \ (dom S ≫ (∋ A)°)) ∩ ((∋ A ≫ dom S) / ∋ A)
  exact le_inter ((le_leftDiv_iff _ _ _).mpr hkey') ((le_div_iff _ _ _).mpr hkey)

/-- **B&dM Ex 5.16** (the `⊑` half B&dM asks for): `P(Dom S) E(S) ⊑ P(S)` — on the sets all of
    whose members have an `S`-image, the EXISTENTIAL image is an Egli–Milner image.  Term₂ is
    `E(S)∋ = ∋S` with the coreflexive dropped; term₁ shunts the map `E(S)` out
    (`(Dom S)∋° ⊑ S∋°E(S)°`, and `∋°E(S)° = (E(S)∋)° = (∋S)° = S°∋°`), leaving `Dom S ⊑ SS°`. -/
public theorem powerRel_dom_comp_existsImage_le {A B : 𝒜} (S : A ⟶ B) :
    powerRel (dom S) ≫ existsImage S ⊑ powerRel S := by
  have hmap : Map (existsImage S) := Λ_is_map' _
  have hcor : powerRel (dom S) ⊑ 𝟙 (PowerAllegory.powerObj A) := by
    have h := powerRel_mono (dom_coreflexive S); rwa [powerRel_id] at h
  show _ ⊑ ((∋ A)° \ (S ≫ (∋ B)°)) ∩ ((∋ A ≫ S) / ∋ B)
  apply le_inter
  · apply (le_leftDiv_iff _ _ _).mpr
    have hstep : (∋ A)° ≫ (powerRel (dom S) ≫ existsImage S)
        ⊑ (dom S ≫ (∋ A)°) ≫ existsImage S := by
      rw [← Cat.assoc]
      exact comp_mono_right (powerRel_term1_cancel (dom S)) _
    refine le_trans hstep ((map_shunt_right hmap _ _).mpr ?_)
    have heq : (S ≫ (∋ B)°) ≫ (existsImage S)° = S ≫ (S° ≫ (∋ A)°) := by
      rw [Cat.assoc, ← Allegory.recip_comp, existsImage_eps, Allegory.recip_comp]
    rw [heq, ← Cat.assoc]
    exact comp_mono_right (inter_lb_right (𝟙 A) (S ≫ S°)) _
  · apply (le_div_iff _ _ _).mpr
    rw [Cat.assoc, existsImage_eps]
    have h := comp_mono_right hcor (∋ A ≫ S)
    rwa [Cat.id_comp] at h

/-- The `est` of a UNION is an `est` of the set of the members' `est`s:
    `union est(R) ⊑ E(est(R)) est(R)`, no hypothesis on `R`.  Shunting the map `E(est(R))`
    out reduces it to `est`'s universal property, whose two halves are: the `est` of the union
    lies in SOME member set (`union est(R) ⊑ ∋ est(R)`, the modular law at `∋'∋` with the
    lower bound below), and every member set is `R`-below it (`∋'union est(R) ⊑ ∈\R°`, since
    `union` is simple and `∈ est(R) ⊑ R°`). -/
public theorem bigUnion_comp_est_le (R : A ⟶ A) :
    bigUnion ≫ est R ⊑ existsImage (est R) ≫ est R := by
  have hmap : Map (existsImage (est R)) := Λ_is_map' _
  have hUmap : Map (bigUnion (A := A)) := Λ_is_map' _
  have heps : existsImage (est R) ≫ ∋ A = ∋ (PowerAllegory.powerObj A) ≫ est R :=
    existsImage_eps (est R)
  have hbeps : ∋ (PowerAllegory.powerObj A) ≫ ∋ A = bigUnion ≫ ∋ A := (Λ_eps_eq' _).symm
  have hlb : (∋ (PowerAllegory.powerObj A))° ≫ (bigUnion ≫ est R) ⊑ ((∋ A)° \ R°) := by
    apply (le_leftDiv_iff _ _ _).mpr
    have e1 : (∋ A)° ≫ ((∋ (PowerAllegory.powerObj A))° ≫ (bigUnion ≫ est R))
        = ((∋ (PowerAllegory.powerObj A) ≫ ∋ A)°) ≫ (bigUnion ≫ est R) := by
      rw [Allegory.recip_comp, Cat.assoc]
    rw [e1, hbeps, Allegory.recip_comp, Cat.assoc,
      ← Cat.assoc ((bigUnion : PowerAllegory.powerObj (PowerAllegory.powerObj A) ⟶
        PowerAllegory.powerObj A)°) bigUnion (est R)]
    refine le_trans (comp_mono_left _ (comp_mono_right hUmap.2 (est R))) ?_
    rw [Cat.id_comp]
    exact recip_eps_comp_est_le R
  have hmem : bigUnion ≫ est R ⊑ ∋ (PowerAllegory.powerObj A) ≫ est R := by
    have hsub : bigUnion ≫ est R ⊑ ∋ (PowerAllegory.powerObj A) ≫ ∋ A := by
      have h1 : bigUnion ≫ est R ⊑ bigUnion ≫ ∋ A :=
        comp_mono_left _ (show est R ⊑ ∋ A from inter_lb_left _ _)
      rwa [← hbeps] at h1
    refine le_trans (le_trans (le_inter hsub (le_refl _))
      (modular_le_right (∋ (PowerAllegory.powerObj A)) (∋ A) (bigUnion ≫ est R))) ?_
    exact comp_mono_left _ (inter_mono (le_refl _) hlb)
  apply (map_shunt_left hmap _ _).mp
  apply le_est_iff.mpr
  refine ⟨(map_shunt_left hmap _ _).mpr (by rw [heps]; exact hmem), ?_⟩
  have e3 : (∋ A)° ≫ ((existsImage (est R))° ≫ (bigUnion ≫ est R))
      = ((est R)° ≫ (∋ (PowerAllegory.powerObj A))°) ≫ (bigUnion ≫ est R) := by
    rw [← Cat.assoc, ← Allegory.recip_comp, heps, Allegory.recip_comp]
  rw [e3]
  refine le_trans (comp_mono_right (comp_mono_right
    (recip_mono (show est R ⊑ ∋ A from inter_lb_left _ _)) _) _) ?_
  rw [Cat.assoc]
  exact le_trans (comp_mono_left _ hlb) (leftDiv_comp_le _ _)

/-- **(7.11) as an EQUALITY** (the note's `est-laws` last row): for TRANSITIVE `R`,
    `P(est(R)) est(R) = P(Dom(est(R))) union est(R)`.  `⊑` is `powerRel_est_le_bigUnion`
    with `P(est(R)) ⊑ P(Dom(est(R))) P(est(R))` in front (`dom_UP` at `dom_powerRel_le`);
    `⊒` is `bigUnion_comp_est_le` followed by Ex 5.16 at `est(R)`.  The note's side condition
    is `R` a preorder, but reflexivity is never used: only the `⊑` half constrains `R`, and it
    asks for transitivity alone. -/
public theorem powerRel_est_eq_bigUnion {R : A ⟶ A} (htrans : R ≫ R ⊑ R) :
    powerRel (est R) ≫ est R = powerRel (dom (est R)) ≫ (bigUnion ≫ est R) := by
  apply le_antisymm
  · have hcor : powerRel (dom (est R)) ⊑ 𝟙 (PowerAllegory.powerObj (PowerAllegory.powerObj A)) := by
      have h := powerRel_mono (dom_coreflexive (est R)); rwa [powerRel_id] at h
    calc powerRel (est R) ≫ est R
        ⊑ (powerRel (dom (est R)) ≫ powerRel (est R)) ≫ est R :=
          comp_mono_right ((dom_UP hcor).mp (dom_powerRel_le (est R))) _
      _ = powerRel (dom (est R)) ≫ (powerRel (est R) ≫ est R) := Cat.assoc _ _ _
      _ ⊑ powerRel (dom (est R)) ≫ (bigUnion ≫ est R) :=
          comp_mono_left _ (powerRel_est_le_bigUnion htrans)
  · calc powerRel (dom (est R)) ≫ (bigUnion ≫ est R)
        ⊑ powerRel (dom (est R)) ≫ (existsImage (est R) ≫ est R) :=
          comp_mono_left _ (bigUnion_comp_est_le R)
      _ = (powerRel (dom (est R)) ≫ existsImage (est R)) ≫ est R := (Cat.assoc _ _ _).symm
      _ ⊑ powerRel (est R) ≫ est R :=
          comp_mono_right (powerRel_dom_comp_existsImage_le (est R)) _

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

/-- **Ex 7.19** mirrored: `mnl R := est (R° ⇨ R)` — an element `x` of the set with `y R x →
    x R y` for every member `y`, i.e. minimal w.r.t. `R` restricted to that set. -/
def mnlRel (R : A ⟶ A) : PowerAllegory.powerObj A ⟶ A := est (R° ⇨ R)

/-- **Ex 7.19** (first part): `id ⊑ R° ⇨ R`, i.e. every element is `(R°⇨R)`-related to
    itself.  Via `le_impl_iff`: `id ∩ R° ⊑ R`.  Since `id∩R°` is coreflexive, it is
    symmetric (`coreflexive_symmetric_idempotent`), so `id∩R° = (id∩R°)° = id∩R ⊑ R`. -/
theorem id_le_impl_recip (R : A ⟶ A) : Cat.id A ⊑ R° ⇨ R := by
  apply (le_impl_iff _ _ _).mpr
  have hcoref : Coreflexive (Cat.id A ∩ R°) := inter_lb_left _ _
  have hsym : (Cat.id A ∩ R°)° = Cat.id A ∩ R° :=
    symmetric_eq (coreflexive_symmetric_idempotent hcoref).1
  have hunfold : (Cat.id A ∩ R°)° = Cat.id A ∩ R := by
    rw [Allegory.recip_inter, recip_id, Allegory.recip_recip]
  have heq : Cat.id A ∩ R° = Cat.id A ∩ R := by rw [← hsym]; exact hunfold
  rw [heq]
  exact inter_lb_right _ _

/-- **Ex 7.20** (first part): `est R ⊑ mnl R` — an `R`-extremum is `R`-minimal.  By `est_mono`
    at `R ⊑ R° ⇨ R`, which `le_impl_iff` reduces to `R ∩ R° ⊑ R`. -/
theorem est_le_mnlRel (R : A ⟶ A) : est R ⊑ mnlRel R := by
  show est R ⊑ est (R° ⇨ R)
  exact est_mono ((le_impl_iff _ _ _).mpr (inter_lb_left R (R°)))

end Freyd.Alg
