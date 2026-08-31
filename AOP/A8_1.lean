/-
  Bird & de Moor, *Algebra of Programming* §8.1  Thinning (book pp. 193-196) — CORE
  (`thinRel`, its (7.5)-style composition law, and the universal property).

  `thin Q = (∈\∈) ∩ ((∋·Q)/∋) : PA ← PA` takes a set `y` to a subset `x ⊆ y` such that
  every element of `y` has a `Q`-lower bound in `x` — keep a representative collection of
  partial solutions without losing the possibility of a future minimum.

  MIRRORING (diagram order, B&dM `X·Y` = Freyd `Y ≫ X`; B&dM `R/S` = Freyd `(S \ R)`;
  B&dM `S\R` = Freyd `R / S`):
  - B&dM `∈\∈` is `subsetRel a` (= Freyd's `powerOrder`, `AOP.A7_1`).
  - like `est R` (= B&dM `min R°`), `thinRel Q` folds the `°` into the argument — it is B&dM's
    `thin Q°` — so the direction is carried by the relation's name and the `est`/`thin` laws
    share their letters.  B&dM `∋·Q°` is `Q° ≫ (∋ a)°`, and `(∋·Q°)/∋` is
    `(((∋ a)°) \ (Q° ≫ (∋ a)°))`.
  - The UP `X ⊑ thin Q°·ΛS ⟺ ∈·X ⊑ S ∧ X·S° ⊑ ∋·Q°` mirrors to
    `X ⊑ Λ S ≫ thinRel Q ⟺ X ≫ ∋ a ⊑ S ∧ S° ≫ X ⊑ Q° ≫ (∋ a)°`.

  Setting: `UnguardedPowerLCDA` (`AOP.A6_2`), continuing chapter 7's `AOP.A7_1`.  The
  thinning theorem (THEOREM 8.1) additionally uses `AOP.A7_2`'s monotonic-algebra calculus and
  `AOP.A6_3`'s hylomorphism theorem (both pulled in transitively via `import AOP.A7_2`).
-/
module

public import AOP.A7_2

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {a b : 𝒜}

/-- `ΛW·subset = W/∋` mirrored: `Λ W ≫ subsetRel a = W / (∋ a)` — the transpose of `W`
    followed by shrinking is exactly "all members come from `W`".  (Ex 7.2's
    `existsImage_comp_subsetRel` is the instance `W := ∋ ≫ R`.) -/
public theorem Λ_comp_subsetRel (W : b ⟶ a) : Λ W ≫ subsetRel a = W / (∋ a) := by
  apply le_antisymm
  · apply (le_div_iff _ _ _).mpr
    have h1 : subsetRel a ≫ ∋ a ⊑ ∋ a := subsetRel_comp_eps_le
    have h2 : Λ W ≫ (subsetRel a ≫ ∋ a) ⊑ Λ W ≫ ∋ a := comp_mono_left _ h1
    rw [Λ_eps_eq'] at h2
    rwa [Cat.assoc]
  · apply (map_shunt_left (Λ_is_map' W) _ _).mp
    show (Λ W)° ≫ (W / ∋ a) ⊑ (∋ a) / (∋ a)
    apply (le_div_iff _ _ _).mpr
    have hcancel : (W / ∋ a) ≫ ∋ a ⊑ W := (le_div_iff _ _ _).mp (le_refl _)
    have h1 : (Λ W)° ≫ ((W / ∋ a) ≫ ∋ a) ⊑ (Λ W)° ≫ W := comp_mono_left _ hcancel
    have h2 : (Λ W)° ≫ W = ((Λ W)° ≫ Λ W) ≫ ∋ a := by
      rw [Cat.assoc, Λ_eps_eq']
    have h3 : ((Λ W)° ≫ Λ W) ≫ ∋ a ⊑ Cat.id _ ≫ ∋ a :=
      comp_mono_right (Λ_is_map' W).2 (∋ a)
    rw [Cat.id_comp] at h3
    rw [h2] at h1
    rw [Cat.assoc]
    exact le_trans h1 h3

/-! ## `thin Q` (B&dM (8.1)) -/

/-- **(8.1)** at the folded `°` (B&dM's `thin Q°`): shrink a set without losing `Q`-lower
    bounds for any of its members. -/
@[expose] public def thinRel (Q : a ⟶ a) : PowerAllegory.powerObj a ⟶ PowerAllegory.powerObj a :=
  subsetRel a ∩ (((∋ a)°) \ (Q° ≫ (∋ a)°))

/-- Thinning only shrinks: `thin Q ≫ ∋ ⊑ ∋` (members of the output were members of the
    input). -/
public theorem thinRel_comp_eps_le (Q : a ⟶ a) : thinRel Q ≫ ∋ a ⊑ ∋ a :=
  le_trans (comp_mono_right (inter_lb_left _ _) (∋ a)) subsetRel_comp_eps_le

/-- Thinning keeps lower bounds: `∋·thin Q° ⊑ Q°·∋`-mirrored, `(∋ a)° ≫ thinRel Q ⊑
    Q° ≫ (∋ a)°` (every input member has a `Q`-lower bound among the output members). -/
public theorem recip_eps_comp_thinRel_le (Q : a ⟶ a) :
    (∋ a)° ≫ thinRel Q ⊑ Q° ≫ (∋ a)° :=
  le_trans (comp_mono_left _ (inter_lb_right _ _)) (leftDiv_comp_le _ _)

/-- The (7.5)-analogue for thinning: `thin Q·ΛS = (S/∋... )`-mirrored,
    `Λ S ≫ thinRel Q = (S / ∋ a) ∩ (S° \ (Q° ≫ (∋ a)°))`. -/
public theorem Λ_comp_thinRel (S : b ⟶ a) (Q : a ⟶ a) :
    Λ S ≫ thinRel Q = (S / ∋ a) ∩ (S° \ (Q° ≫ (∋ a)°)) := by
  show Λ S ≫ (subsetRel a ∩ (((∋ a)°) \ (Q° ≫ (∋ a)°))) = _
  rw [simple_dist_inter (Λ_is_map' S).2, Λ_comp_subsetRel, Λ_comp_lb]

/-- **The universal property of `thin`** (book p.193): `X ⊑ thin Q·ΛS ⟺ ∈·X ⊑ S ∧
    X·S° ⊑ ∋·Q`, mirrored.  Like (7.5)'s UP, this is the workhorse of every calculation
    in the chapter. -/
public theorem le_Λ_comp_thinRel_iff {S : b ⟶ a} {Q : a ⟶ a} {X : b ⟶ PowerAllegory.powerObj a} :
    X ⊑ Λ S ≫ thinRel Q ↔ X ≫ ∋ a ⊑ S ∧ S° ≫ X ⊑ Q° ≫ (∋ a)° := by
  rw [Λ_comp_thinRel]
  constructor
  · intro h
    constructor
    · exact (le_div_iff _ _ _).mp (le_trans h (inter_lb_left _ _))
    · exact le_trans (comp_mono_left _ (le_trans h (inter_lb_right _ _))) (leftDiv_comp_le _ _)
  · rintro ⟨h1, h2⟩
    exact le_inter ((le_div_iff _ _ _).mpr h1) ((le_leftDiv_iff _ _ _).mpr h2)

/-! ## Singleton-map facts and a shared transpose lemma (book p.194) -/

/-- `τ·∈ = id` mirrored: `singletonMap ≫ ∋ a = Cat.id a` — the singleton of `x` has `x` as its
    unique member (B&dM p.194, from `Λ(1_a)∋ = 1_a`). -/
theorem singletonMap_comp_eps : singletonMap ≫ ∋ a = Cat.id a := by
  show Λ (Cat.id a) ≫ ∋ a = Cat.id a
  rw [Λ_eps_eq']

/-- `∈·τ ⊑ id`-mirrored, `singletonMap° ⊑ ∋ a` — a member of the singleton `{x}` is `x`
    (B&dM p.194).  Shunt across the map `singletonMap` then use `singletonMap_comp_eps`. -/
theorem singletonMap_recip_le_eps : (singletonMap : a ⟶ PowerAllegory.powerObj a)° ⊑ ∋ a := by
  have h : (Λ (Cat.id a))° ≫ Cat.id a ⊑ ∋ a := by
    apply (map_shunt_left (Λ_is_map' (Cat.id a)) (Cat.id a) (∋ a)).mpr
    rw [Λ_eps_eq']
    exact le_refl _
  rw [Cat.comp_id] at h
  exact h

/-- `τ ⊑ ∋` mirrored: `singletonMap ⊑ (∋ a)°`, the reciprocated form of
    `singletonMap_recip_le_eps`. -/
theorem singletonMap_le_recip_eps :
    (singletonMap : a ⟶ PowerAllegory.powerObj a) ⊑ (∋ a)° := by
  have h := recip_mono (singletonMap_recip_le_eps (a := a))
  rwa [Allegory.recip_recip] at h

/-- `T°·ΛT ⊑ ∋` mirrored: `T° ≫ Λ T ⊑ (∋ a)°` — the transpose of `T` cancels against `T°` down
    to a membership.  Shared by (8.3) thin-elimination-with-context and THEOREM 8.1. -/
public theorem recip_comp_Λ_le_recip_eps (T : b ⟶ a) : T° ≫ Λ T ⊑ (∋ a)° := by
  have hrecip : T° = (∋ a)° ≫ (Λ T)° := by
    rw [← Allegory.recip_comp, Λ_eps_eq']
  rw [hrecip, Cat.assoc]
  have h := comp_mono_left ((∋ a)°) (Λ_is_map' T).2
  rwa [Cat.comp_id] at h

/-! ## Basic properties of `thin` (book p.194) -/

/-- `thin` is monotone (B&dM p.194): `Q ⊑ R → thin Q ⊑ thin R`. -/
public theorem thinRel_mono {Q R : a ⟶ a} (h : Q ⊑ R) : thinRel Q ⊑ thinRel R := by
  show thinRel Q ⊑ subsetRel a ∩ (((∋ a)°) \ (R° ≫ (∋ a)°))
  exact le_inter (inter_lb_left _ _)
    (le_trans (inter_lb_right _ _) (leftDiv_mono_right _ (comp_mono_right (recip_mono h) ((∋ a)°))))

/-- Reflexive half of **Ex 8.2**: `id ⊑ Q → id ⊑ thin Q`. -/
public theorem id_le_thinRel {Q : a ⟶ a} (hrefl : Cat.id a ⊑ Q) :
    Cat.id (PowerAllegory.powerObj a) ⊑ thinRel Q := by
  show Cat.id (PowerAllegory.powerObj a) ⊑ subsetRel a ∩ (((∋ a)°) \ (Q° ≫ (∋ a)°))
  refine le_inter id_le_subsetRel ?_
  apply (le_leftDiv_iff _ _ _).mpr
  rw [Cat.comp_id]
  have hrefl' : Cat.id a ⊑ Q° := by
    have h0 := recip_mono hrefl
    rwa [recip_id] at h0
  have h := comp_mono_right hrefl' ((∋ a)°)
  rwa [Cat.id_comp] at h

/-- Transitive half of **Ex 8.2**: `Q ≫ Q ⊑ Q → thin Q ≫ thin Q ⊑ thin Q`. -/
theorem thinRel_trans {Q : a ⟶ a} (htrans : Q ≫ Q ⊑ Q) :
    thinRel Q ≫ thinRel Q ⊑ thinRel Q := by
  have htrans' : Q° ≫ Q° ⊑ Q° := by
    have h0 := recip_mono htrans
    rwa [Allegory.recip_comp] at h0
  show thinRel Q ≫ thinRel Q ⊑ subsetRel a ∩ (((∋ a)°) \ (Q° ≫ (∋ a)°))
  refine le_inter ?_ ?_
  · -- component 1: `⊑ subsetRel a = (∋a)/(∋a)`
    show thinRel Q ≫ thinRel Q ⊑ (∋ a) / (∋ a)
    apply (le_div_iff _ _ _).mpr
    rw [Cat.assoc]
    exact le_trans (comp_mono_left _ (thinRel_comp_eps_le Q)) (thinRel_comp_eps_le Q)
  · -- component 2: `⊑ ((∋a)° \ (Q°≫(∋a)°))`
    apply (le_leftDiv_iff _ _ _).mpr
    rw [← Cat.assoc]
    have s1 : ((∋ a)° ≫ thinRel Q) ≫ thinRel Q ⊑ (Q° ≫ (∋ a)°) ≫ thinRel Q :=
      comp_mono_right (recip_eps_comp_thinRel_le Q) (thinRel Q)
    have s2 : (Q° ≫ (∋ a)°) ≫ thinRel Q ⊑ Q° ≫ (∋ a)° := by
      rw [Cat.assoc]
      have t1 : Q° ≫ ((∋ a)° ≫ thinRel Q) ⊑ Q° ≫ (Q° ≫ (∋ a)°) :=
        comp_mono_left Q° (recip_eps_comp_thinRel_le Q)
      have t2 : Q° ≫ (Q° ≫ (∋ a)°) ⊑ Q° ≫ (∋ a)° := by
        rw [← Cat.assoc]
        exact comp_mono_right htrans' ((∋ a)°)
      exact le_trans t1 t2
    exact le_trans s1 s2

/-- **Ex 8.1** (one direction): `id ⊑ thin id`.  The full Ex 8.1 asks for `thin id = id`; the
    reverse `thin id ⊑ id` is power-object EXTENSIONALITY (antisymmetry of the `subsetRel`
    order), which needs a tabular unitary power allegory — a capability the `UnguardedPowerLCDA`
    setting of this file does NOT have (recorded as a dropped item in the chapter-4
    formalization).  Only the reflexive half is proved here. -/
public theorem id_le_thinRel_id : Cat.id (PowerAllegory.powerObj a) ⊑ thinRel (Cat.id a) :=
  id_le_thinRel (le_refl _)

/-! ## Thin-introduction and thin-elimination (book p.194) -/

/-- **Ex 8.3**: `min R ⊇ min R·thin Q` when `Q ⊑ R` and `R°` is transitive — thinning below a
    coarser transitive preorder does not lose the minimum (mirrored at the folded `°`). -/
public theorem thinRel_comp_est_le {Q R : a ⟶ a} (hQR : Q ⊑ R) (htransR : R° ≫ R° ⊑ R°) :
    thinRel Q ≫ est R ⊑ est R := by
  apply le_est_iff.mpr
  refine ⟨?_, ?_⟩
  · exact le_trans (comp_mono_left _ (show est R ⊑ ∋ a from inter_lb_left _ _))
      (thinRel_comp_eps_le Q)
  · rw [← Cat.assoc]
    have s1 : ((∋ a)° ≫ thinRel Q) ≫ est R ⊑ (Q° ≫ (∋ a)°) ≫ est R :=
      comp_mono_right (recip_eps_comp_thinRel_le Q) (est R)
    have s2 : (Q° ≫ (∋ a)°) ≫ est R ⊑ R° := by
      rw [Cat.assoc]
      have hbnd : (∋ a)° ≫ est R ⊑ R° :=
        le_trans (comp_mono_left _ (show est R ⊑ (((∋ a)°) \ R°) from inter_lb_right _ _))
          (leftDiv_comp_le _ R°)
      have t1 : Q° ≫ ((∋ a)° ≫ est R) ⊑ Q° ≫ R° := comp_mono_left Q° hbnd
      exact le_trans t1 (le_trans (comp_mono_right (recip_mono hQR) R°) htransR)
    exact le_trans s1 s2

/-- **Thin-introduction** (book p.194): `min R = min R·thin Q` when `Q ⊑ R`, `id ⊑ Q`, and `R°`
    is transitive (mirrored at the folded `°`) — introducing a thinning step below a minimum
    leaves it unchanged. -/
public theorem thinRel_comp_est {Q R : a ⟶ a} (hQR : Q ⊑ R) (hreflQ : Cat.id a ⊑ Q)
    (htransR : R° ≫ R° ⊑ R°) : thinRel Q ≫ est R = est R := by
  apply le_antisymm (thinRel_comp_est_le hQR htransR)
  have h : Cat.id (PowerAllegory.powerObj a) ≫ est R ⊑ thinRel Q ≫ est R :=
    comp_mono_right (id_le_thinRel hreflQ) (est R)
  rwa [Cat.id_comp] at h

/-- **(8.2)**, thin-elimination: `min Q ≫ τ ⊑ thin Q` — a minimum, viewed as a singleton, is a
    thinning. -/
theorem est_comp_singletonMap_le_thinRel (Q : a ⟶ a) :
    est Q ≫ singletonMap ⊑ thinRel Q := by
  show est Q ≫ singletonMap ⊑ subsetRel a ∩ (((∋ a)°) \ (Q° ≫ (∋ a)°))
  refine le_inter ?_ ?_
  · show est Q ≫ singletonMap ⊑ (∋ a) / (∋ a)
    apply (le_div_iff _ _ _).mpr
    rw [Cat.assoc, singletonMap_comp_eps, Cat.comp_id]
    exact inter_lb_left _ _
  · apply (le_leftDiv_iff _ _ _).mpr
    rw [← Cat.assoc]
    have hbnd : (∋ a)° ≫ est Q ⊑ Q° :=
      le_trans (comp_mono_left _ (show est Q ⊑ (((∋ a)°) \ Q°) from inter_lb_right _ _))
        (leftDiv_comp_le _ Q°)
    have s1 : ((∋ a)° ≫ est Q) ≫ singletonMap ⊑ Q° ≫ singletonMap :=
      comp_mono_right hbnd singletonMap
    exact le_trans s1 (comp_mono_left Q° singletonMap_le_recip_eps)

/-- **Ex 8.5**: `min R = thin R ≫ τ°` — thinning followed by "pick the singleton member" recovers
    the minimum. -/
theorem est_eq_thinRel_comp_recip_singletonMap {R : a ⟶ a} :
    est R = thinRel R ≫ singletonMap° := by
  apply le_antisymm
  · -- `min R° ⊑ thin R ≫ τ°`
    have hid : Cat.id a ⊑ singletonMap ≫ singletonMap° := entire_id_le (Λ_is_map' (Cat.id a)).1
    have step1 : est R ⊑ est R ≫ (singletonMap ≫ singletonMap°) := by
      have h := comp_mono_left (est R) hid
      rwa [Cat.comp_id] at h
    have step2 : est R ≫ (singletonMap ≫ singletonMap°)
        = (est R ≫ singletonMap) ≫ singletonMap° := (Cat.assoc _ _ _).symm
    rw [step2] at step1
    exact le_trans step1 (comp_mono_right (est_comp_singletonMap_le_thinRel R) singletonMap°)
  · -- `thin R ≫ τ° ⊑ min R°`
    apply le_est_iff.mpr
    refine ⟨?_, ?_⟩
    · exact le_trans (comp_mono_left _ singletonMap_recip_le_eps) (thinRel_comp_eps_le R)
    · rw [← Cat.assoc]
      have s1 : ((∋ a)° ≫ thinRel R) ≫ singletonMap° ⊑ (R° ≫ (∋ a)°) ≫ singletonMap° :=
        comp_mono_right (recip_eps_comp_thinRel_le R) singletonMap°
      have s2 : (R° ≫ (∋ a)°) ≫ singletonMap° ⊑ R° := by
        have e2 : (∋ a)° ≫ singletonMap° = Cat.id a := by
          rw [← Allegory.recip_comp, singletonMap_comp_eps, recip_id]
        rw [Cat.assoc, e2, Cat.comp_id]
        exact le_refl _
      exact le_trans s1 s2

/-- **(8.3)**, thin-elimination with context: `ΛS ≫ min R ≫ τ ⊑ ΛS ≫ thin Q` whenever `R`
    restricted to the domain of `S` (i.e. `R ∩ S°S`) refines `Q`.  Proved via the thin universal
    property (`le_Λ_comp_thinRel_iff`), the context rule (7.6) `Λ_comp_est_context`, and the
    shared `recip_comp_Λ_le_recip_eps` (to recover the `S°S`-context bound). -/
theorem Λ_comp_est_comp_singletonMap_le_thinRel {S : b ⟶ a} {Q R : a ⟶ a}
    (h : R ∩ (S° ≫ S) ⊑ Q) : Λ S ≫ est R ≫ singletonMap ⊑ Λ S ≫ thinRel Q := by
  apply le_Λ_comp_thinRel_iff.mpr
  refine ⟨?_, ?_⟩
  · -- `(ΛS ≫ min R° ≫ τ) ≫ ∈ ⊑ S`
    rw [Cat.assoc (Λ S) (est R ≫ singletonMap) (∋ a),
        Cat.assoc (est R) singletonMap (∋ a), singletonMap_comp_eps, Cat.comp_id]
    have h := comp_mono_left (Λ S) (show est R ⊑ ∋ a from inter_lb_left _ _)
    rwa [Λ_eps_eq'] at h
  · -- `S° ≫ (ΛS ≫ min R° ≫ τ) ⊑ Q° ≫ ∋`
    have hSA : S° ≫ Λ S ⊑ (∋ a)° := recip_comp_Λ_le_recip_eps S
    have hbndM : (∋ a)° ≫ est (R ∩ (S° ≫ S)) ⊑ R° ∩ (S° ≫ S) := by
      have hb := recip_eps_comp_est_le (R ∩ (S° ≫ S))
      rwa [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip] at hb
    rw [← Cat.assoc (Λ S) (est R) singletonMap, (Λ_comp_est_context S R).symm,
        Cat.assoc (Λ S) (est (R ∩ (S° ≫ S))) singletonMap,
        ← Cat.assoc S° (Λ S) (est (R ∩ (S° ≫ S)) ≫ singletonMap)]
    have s1 : (S° ≫ Λ S) ≫ (est (R ∩ (S° ≫ S)) ≫ singletonMap)
        ⊑ (∋ a)° ≫ (est (R ∩ (S° ≫ S)) ≫ singletonMap) :=
      comp_mono_right hSA (est (R ∩ (S° ≫ S)) ≫ singletonMap)
    have h' : R° ∩ (S° ≫ S) ⊑ Q° := by
      have h0 := recip_mono h
      rwa [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip] at h0
    have s2 : (∋ a)° ≫ (est (R ∩ (S° ≫ S)) ≫ singletonMap) ⊑ Q° ≫ (∋ a)° := by
      rw [← Cat.assoc (∋ a)° (est (R ∩ (S° ≫ S))) singletonMap]
      have t1 : ((∋ a)° ≫ est (R ∩ (S° ≫ S))) ≫ singletonMap
          ⊑ (R° ∩ (S° ≫ S)) ≫ singletonMap := comp_mono_right hbndM singletonMap
      have t2 : (R° ∩ (S° ≫ S)) ≫ singletonMap ⊑ Q° ≫ singletonMap := comp_mono_right h' singletonMap
      exact le_trans t1 (le_trans t2 (comp_mono_left Q° singletonMap_le_recip_eps))
    exact le_trans s1 s2

/-! ## THEOREM 8.1 — the thinning theorem (book p.195) -/

variable {F : Relator 𝒜 𝒜}

/-- **THEOREM 8.1 (the thinning theorem, B&dM p.195)**: for a transitive `Q` and an algebra `S`
    that is monotonic on the preorder `Q`, thinning at every unfold step
    (`⦇Λ(F∈·S)·thin Q⦈`) refines thinning once, at the end, on the plain catamorphism
    (`thin Q·Λ⦇S⦈`), mirrored
    `relCata I (Λ (F.map ∈ ≫ S) ≫ thin Q) ⊑ Λ (relCata I S) ≫ thin Q`.  Proved via the thin
    universal property (`le_Λ_comp_thinRel_iff`): the "shrinks" half by the fusion law (6.5), the
    "keeps lower bounds" half by the hylomorphism theorem (`hylo_le_of_prefixed`), using the
    reciprocated monotonicity `S° ≫ FQ° ⊑ Q° ≫ S°` exactly as in the GREEDY THEOREM. -/
public theorem thinning (hFr : F.PreservesRecip) (I : InitialAlgebra F) {Q : a ⟶ a}
    {S : F.obj a ⟶ a} (htrans : Q ≫ Q ⊑ Q) (hmono : MonotonicAlg S Q) :
    relCata (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q) ⊑ Λ (relCata S) ≫ thinRel Q := by
  apply le_Λ_comp_thinRel_iff.mpr
  refine ⟨?_, ?_⟩
  · -- (i) `⦇ΛW·thin Q⦈ ≫ ∈ ⊑ ⦇S⦈`, by the fusion law (6.5)
    apply comp_le_relCata I
    rw [Cat.assoc]
    have h1 : Λ (F.map (∋ a) ≫ S) ≫ (thinRel Q ≫ ∋ a) ⊑ Λ (F.map (∋ a) ≫ S) ≫ ∋ a :=
      comp_mono_left _ (thinRel_comp_eps_le Q)
    rwa [Λ_eps_eq'] at h1
  · -- (ii) `⦇S⦈°·⦇ΛW·thin Q⦈ ⊑ Q°·∋`, by the hylomorphism theorem
    apply hylo_le_of_prefixed hFr I
    -- goal: `S° ≫ F.map (Q° ≫ (∋a)°) ≫ (ΛW ≫ thin Q) ⊑ Q° ≫ (∋a)°`
    have htrans' : Q° ≫ Q° ⊑ Q° := by
      have h0 := recip_mono htrans
      rwa [Allegory.recip_comp] at h0
    have step1 : S° ≫ F.map Q° ⊑ Q° ≫ S° := by
      have h := recip_mono hmono
      have heqL : (F.map Q ≫ S)° = S° ≫ F.map Q° := by
        rw [Allegory.recip_comp, hFr Q]
      have heqR : (S ≫ Q)° = Q° ≫ S° := Allegory.recip_comp _ _
      rwa [heqL, heqR] at h
    have hWrecip : (F.map (∋ a) ≫ S)° = S° ≫ F.map ((∋ a)°) := by
      rw [Allegory.recip_comp, ← hFr (∋ a)]
    have hWA : (F.map (∋ a) ≫ S)° ≫ Λ (F.map (∋ a) ≫ S) ⊑ (∋ a)° :=
      recip_comp_Λ_le_recip_eps (F.map (∋ a) ≫ S)
    -- the inner bound `S° ≫ rest ⊑ Q° ≫ (∋a)°`
    have hsr : S° ≫ (F.map ((∋ a)°) ≫ (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q)) ⊑ Q° ≫ (∋ a)° := by
      have a1 : S° ≫ (F.map ((∋ a)°) ≫ (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q))
          = ((F.map (∋ a) ≫ S)° ≫ Λ (F.map (∋ a) ≫ S)) ≫ thinRel Q := by
        rw [← Cat.assoc S° (F.map ((∋ a)°)) (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q), ← hWrecip,
            ← Cat.assoc ((F.map (∋ a) ≫ S)°) (Λ (F.map (∋ a) ≫ S)) (thinRel Q)]
      rw [a1]
      exact le_trans (comp_mono_right hWA (thinRel Q)) (recip_eps_comp_thinRel_le Q)
    -- assemble the top-level chain
    rw [F.map_comp Q° ((∋ a)°),
        Cat.assoc (F.map Q°) (F.map ((∋ a)°)) (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q),
        ← Cat.assoc S° (F.map Q°) (F.map ((∋ a)°) ≫ (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q))]
    have b1 : (S° ≫ F.map Q°) ≫ (F.map ((∋ a)°) ≫ (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q))
        ⊑ (Q° ≫ S°) ≫ (F.map ((∋ a)°) ≫ (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q)) :=
      comp_mono_right step1 _
    have b2 : (Q° ≫ S°) ≫ (F.map ((∋ a)°) ≫ (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q)) ⊑ Q° ≫ (∋ a)° := by
      rw [Cat.assoc Q° S° (F.map ((∋ a)°) ≫ (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q))]
      have c2 : Q° ≫ (Q° ≫ (∋ a)°) ⊑ Q° ≫ (∋ a)° := by
        rw [← Cat.assoc Q° Q° ((∋ a)°)]
        exact comp_mono_right htrans' ((∋ a)°)
      exact le_trans (comp_mono_left Q° hsr) c2
    exact le_trans b1 b2

/-- **Corollary 8.1 (B&dM p.196)**: thinning at every step, then taking the `R°`-minimum, refines
    taking the `R°`-minimum of the plain catamorphism, mirrored
    `relCata I (Λ (F.map ∈ ≫ S) ≫ thin Q) ≫ min R° ⊑ Λ (relCata I S) ≫ min R°`, given `Q ⊑ R`,
    `id ⊑ Q`, `Q` and `R°` transitive, and `S` monotonic on `Q`.  Immediate from THEOREM 8.1
    composed with `min R°` and thin-introduction (`thinRel_comp_est`). -/
public theorem thinning_est (hFr : F.PreservesRecip) (I : InitialAlgebra F) {Q R : a ⟶ a}
    {S : F.obj a ⟶ a} (hQR : Q ⊑ R) (hreflQ : Cat.id a ⊑ Q) (htransQ : Q ≫ Q ⊑ Q)
    (htransR : R° ≫ R° ⊑ R°) (hmono : MonotonicAlg S Q) :
    relCata (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q) ≫ est R ⊑ Λ (relCata S) ≫ est R := by
  have hrhs : Λ (relCata S) ≫ est R = (Λ (relCata S) ≫ thinRel Q) ≫ est R := by
    rw [Cat.assoc, thinRel_comp_est hQR hreflQ htransR]
  rw [hrhs]
  exact comp_mono_right (thinning hFr I htransQ hmono) (est R)

/-! ## Ex 8.6 — the context rule for thin (book p.196) -/

/-- **Ex 8.6**, the context rule for thin: thinning by `Q` versus thinning by `Q` restricted to
    the domain-of-definition of `S` (i.e. `Q ∩ S°S`) agree once composed with `ΛS`, mirrored
    `Λ S ≫ thinRel (Q ∩ (S° ≫ S)) = Λ S ≫ thinRel Q` (the (7.6)-analogue for `thin`).

    The `⊑` half (dropping the extra context) is just `thinRel_mono` on `Q ∩ S°S ⊑ Q`.  The `⊒`
    half brings the context back: via the thin universal property it reduces to
    `S° ≫ (ΛS ≫ thin Q) ⊑ (Q° ∩ S°S) ≫ ∈°`, and the intersection under the composite is
    produced by the MODULAR LAW `modular_le` at `(R,S,T) = (Q°, ∈°, S°·(ΛS·thin Q))`, using
    `(ΛS ≫ thin Q) ≫ ∈ ⊑ S` (thinning shrinks) to bound `T ≫ ∈` by `S°S`.  Note the naive
    "distribute `leftDiv` over the numerator meet" route is unavailable — `(Q∩V)·∈°` does not
    split as `(Q·∈°) ∩ (V·∈°)` for the lax `∈°`. -/
public theorem Λ_comp_thinRel_context (S : b ⟶ a) (Q : a ⟶ a) :
    Λ S ≫ thinRel (Q ∩ (S° ≫ S)) = Λ S ≫ thinRel Q := by
  apply le_antisymm
  · exact comp_mono_left (Λ S) (thinRel_mono (inter_lb_left Q (S° ≫ S)))
  · apply le_Λ_comp_thinRel_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [Cat.assoc]
      have h := comp_mono_left (Λ S) (thinRel_comp_eps_le Q)
      rwa [Λ_eps_eq'] at h
    · rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip]
      have hZQ : S° ≫ (Λ S ≫ thinRel Q) ⊑ Q° ≫ (∋ a)° :=
        (le_Λ_comp_thinRel_iff.mp (le_refl (Λ S ≫ thinRel Q))).2
      have hZeps : (S° ≫ (Λ S ≫ thinRel Q)) ≫ ∋ a ⊑ S° ≫ S := by
        rw [Cat.assoc]
        apply comp_mono_left
        rw [Cat.assoc]
        have h := comp_mono_left (Λ S) (thinRel_comp_eps_le Q)
        rwa [Λ_eps_eq'] at h
      have hmod := modular_le Q° ((∋ a)°) (S° ≫ (Λ S ≫ thinRel Q))
      rw [Allegory.recip_recip] at hmod
      have hZeq : S° ≫ (Λ S ≫ thinRel Q)
          ⊑ (Q° ≫ (∋ a)°) ∩ (S° ≫ (Λ S ≫ thinRel Q)) := le_inter hZQ (le_refl _)
      have hfin : (Q° ∩ (S° ≫ (Λ S ≫ thinRel Q)) ≫ ∋ a) ≫ (∋ a)°
          ⊑ (Q° ∩ (S° ≫ S)) ≫ (∋ a)° :=
        comp_mono_right (inter_mono (le_refl Q°) hZeps) ((∋ a)°)
      exact le_trans hZeq (le_trans hmod hfin)

/-! ## Stretch items (book pp.195-196) — dropped, with obstructions noted

  * **(8.4) / Ex 8.7** (`P(thin Q)·union ⊆ union·thin Q`, the power-functor fusion of thinning):
    DROPPED.  Mirrors `A7_1`'s `powerRel_est_le_bigUnion` but the Egli–Milner ingredient here
    is `powerRel (thinRel Q)`, and the argument needs a lax-naturality bound relating
    `powerRel (thin Q)` to `thin Q` past `union` that is not among the `A5_4` `powerRel`
    lemmas on hand; deferred with the other `powerRel`-fusion facts of chapter 7.

  * **Ex 8.4** (the cup / pairing rule for `thin`): DROPPED — needs the `cup` operation, which
    lives in `A5_6`'s `TabularUnitaryUnguardedDivisionPowerAllegory` setting, strictly stronger
    than this file's `UnguardedPowerLCDA`.  A genuine setting mismatch, not a proof-effort gap.

  * **Ex 8.8** (greedy/thinning corollary): DROPPED — `thinning_est` already packages the natural
    "thin at each step, then take the `R`-minimum" corollary; B&dM's Ex 8.8 as stated adds no
    formal content over `thinning_est`/`greedy` in this point-free setting (cf. the Ex 7.33 note
    in `A7_2`).

  * **Ex 8.9** (well-supportedness): DROPPED — depends on chapter 7's already-dropped
    well-boundedness material (Ex 7.26-7.32, the TABULATION wall documented in `A7_1`); the
    pairing `h := Λ(f∪g)` it relies on is unavailable in `UnguardedPowerLCDA`.
-/

end Freyd.Alg
