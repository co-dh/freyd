module

public import Freyd.S2_44

universe u

/-
  Freyd & Scedrov, *Categories and Allegories*.

  §2.441  STRAIGHT-JOIN ⟹ PRE-POSITIVE, over an UNGUARDED power allegory.

  This file discharges the single reverse hypothesis `hSJtoPP` left open by
  `prePositive_wellJoined_straightJoin_tfae` (in `Freyd.S2_44`), completing the §2.441
  equivalence (1)⇔(2)⇔(3) for unguarded power allegories.

  Book proof of (3)⟹(1): given STRAIGHT `S₁ : α → γ`, `S₂ : β → γ`, form the maps
  `Λ(Sᵢ) = Λ Sᵢ : α → [γ]`.  `Λ(S)` is a SPLIT-MONIC map when `S` is straight (`Λ_is_map'`
  makes it entire, `Λ_monic_of_straight` makes it monic).  It then suffices to build maps
  `ℓ, ϰ : [γ] → [[[γ]]]` with `ℓℓ° = 1 = ϰϰ°` and `ℓϰ° = 0`; the pre-positive maps are
  `f = Λ(S₁) ≫ ℓ` and `g = Λ(S₂) ≫ ϰ`.

  The construction (for an arbitrary object `a`, instantiated at `a = [γ]`):
      ℓ := Λ(1_a) ≫ Λ(1_[a])            (singleton ∘ singleton — the book's `(1/∋)(1/∋')`)
      ϰ := Λ(1_a / ∋_a)                  (the book's `(1/∋)/∋'`, i.e. `Λ` of `1/∋`)
  Here `1/∋ = 1_a / ∋_a` (right division) is STRAIGHT because it is right-invertible
  (`(1/∋)∋ = 1`), so `ϰ = Λ(1/∋)` is monic by `Λ_monic_of_straight`.  The disjointness
  `ℓϰ° = 0` reduces, exactly as in Freyd's proof, to `Λ(0) ∩ Λ(1) = 0`
  (`Λ_zero_inter_Λ_one`, the crux already proven in `Freyd.S2_44`).
-/

namespace Freyd.Alg

variable {𝒜 : Type u}

/-! ## Division helpers (monotonicity + division by a map) -/

section DivHelpers
variable [DivisionAllegory 𝒜]

/-- Division is antitone in its denominator: `S ⊑ S' → R/S' ⊑ R/S`. -/
theorem div_den_antimono {a b c : 𝒜} (R : a ⟶ c) {S S' : b ⟶ c} (h : S ⊑ S') :
    R / S' ⊑ R / S :=
  (le_div_iff _ _ _).mpr
    (le_trans (comp_mono_left _ h) (DivisionAllegory.div_comp_le R S'))

/-- Right division by an ENTIRE morphism is bounded by composition with its reciprocal:
    `R / f ⊑ R ≫ f°`.  (For a map `f`, this is an equality — §1.782 `R/f = Rf°` — but only
    the `⊑` half is needed here, and it uses only entireness of `f`.) -/
theorem div_by_entire_le {a b c : 𝒜} (R : a ⟶ c) {f : b ⟶ c} (hf : Entire f) :
    R / f ⊑ R ≫ f° := by
  have h1 : Cat.id b ⊑ f ≫ f° := by
    have h := hf; dsimp [Entire, dom] at h; rw [← h]; exact inter_lb_right _ _
  have step : R / f ⊑ (R / f) ≫ (f ≫ f°) := by
    have hc := comp_mono_left (R / f) h1
    rwa [Cat.comp_id] at hc
  refine le_trans step ?_
  rw [← Cat.assoc]
  exact comp_mono_right (DivisionAllegory.div_comp_le R f) f°

end DivHelpers

/-! ## Split-monic maps and the composition/cross lemmas -/

section Split
variable [DivisionAllegory 𝒜]

/-- The composition of two SPLIT-MONIC morphisms is split-monic: if `pp° = 1` and `qq° = 1`
    then `(pq)(pq)° = 1`. -/
theorem split_comp {a m n : 𝒜} {p : a ⟶ m} {q : m ⟶ n}
    (hp : p ≫ p° = Cat.id a) (hq : q ≫ q° = Cat.id m) :
    (p ≫ q) ≫ (p ≫ q)° = Cat.id a := by
  rw [Allegory.recip_comp]
  calc (p ≫ q) ≫ (q° ≫ p°) = p ≫ ((q ≫ q°) ≫ p°) := by simp [Cat.assoc]
    _ = p ≫ (Cat.id m ≫ p°) := by rw [hq]
    _ = p ≫ p° := by rw [Cat.id_comp]
    _ = Cat.id a := hp

/-- Cross-disjointness propagates through pre/post-composition: if `uv° = 0` then
    `(pu)(qv)° = 0`. -/
theorem cross_zero {a b m n : 𝒜} {p : a ⟶ m} {q : b ⟶ m} {u : m ⟶ n} {v : m ⟶ n}
    (huv : u ≫ v° = (𝟘 : m ⟶ m)) :
    (p ≫ u) ≫ (q ≫ v)° = (𝟘 : a ⟶ b) := by
  rw [Allegory.recip_comp]
  calc (p ≫ u) ≫ (v° ≫ q°) = p ≫ ((u ≫ v°) ≫ q°) := by simp [Cat.assoc]
    _ = p ≫ ((𝟘 : m ⟶ m) ≫ q°) := by rw [huv]
    _ = (𝟘 : a ⟶ b) := by
        rw [DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero]

end Split

/-! ## The power-allegory ingredients -/

section Power
variable [UnguardedPowerAllegory 𝒜]

/-- The identity is straight (right-invertible by itself). -/
theorem straight_id {a : 𝒜} : Straight (Cat.id a) :=
  rightInvertible_straight (Cat.comp_id (Cat.id a))

/-- For straight `S`, `Λ(S)` is a SPLIT-MONIC map: `Λ S ≫ (Λ S)° = 1`.  (Monic by
    `Λ_monic_of_straight`, and `1 ⊑ Λ S ≫ (Λ S)°` because `Λ S` is entire — `Λ_is_map'`.) -/
theorem Λ_split_monic {a b : 𝒜} {S : a ⟶ b} (hS : Straight S) :
    Λ S ≫ (Λ S)° = Cat.id a := by
  refine le_antisymm (Λ_monic_of_straight hS) ?_
  have hent := (Λ_is_map' S).1
  dsimp [Entire, dom] at hent
  rw [← hent]; exact inter_lb_right _ _

/-- `1/∋ = 1_a / ∋_a` is STRAIGHT: it is right-invertible, `(1/∋) ≫ ∋ = 1`.
    `⊑` is `div_comp_le`; `⊒` is `1 = Λ(1)∋ ⊑ (1/∋)∋` since `Λ(1) = 1/ₛ∋ ⊑ 1/∋`. -/
theorem invMem_straight (a : 𝒜) : Straight (Cat.id a / ∋ a) := by
  refine rightInvertible_straight (T := ∋ a) ?_
  refine le_antisymm (DivisionAllegory.div_comp_le (Cat.id a) (∋ a)) ?_
  have hA : Λ (Cat.id a) ≫ ∋ a = Cat.id a := Λ_eps_eq' (Cat.id a)
  have hAle : Λ (Cat.id a) ⊑ Cat.id a / ∋ a := inter_lb_left _ _
  calc Cat.id a = Λ (Cat.id a) ≫ ∋ a := hA.symm
    _ ⊑ (Cat.id a / ∋ a) ≫ ∋ a := comp_mono_right hAle (∋ a)

/-- `ℓ_a := Λ(1_a) ≫ Λ(1_[a]) : a → [[a]]` — the composite of two singleton maps. -/
def ellMap (a : 𝒜) : a ⟶ PowerAllegory.powerObj (PowerAllegory.powerObj a) :=
  Λ (Cat.id a) ≫ Λ (Cat.id (PowerAllegory.powerObj a))

/-- `ϰ_a := Λ(1_a / ∋_a) : a → [[a]]` — the transpose of the (straight) `1/∋`. -/
def kappaMap (a : 𝒜) : a ⟶ PowerAllegory.powerObj (PowerAllegory.powerObj a) :=
  Λ (Cat.id a / ∋ a)

/-- `ℓ_a` is a map (composite of the two singleton maps). -/
theorem ellMap_map (a : 𝒜) : Map (ellMap a) :=
  map_comp (Λ_is_map' _) (Λ_is_map' _)

/-- `ℓ_a` is split-monic: `ℓℓ° = 1_a`. -/
theorem ellMap_split (a : 𝒜) : ellMap a ≫ (ellMap a)° = Cat.id a := by
  unfold ellMap
  exact split_comp (Λ_split_monic straight_id) (Λ_split_monic straight_id)

/-- `ϰ_a` is split-monic: `ϰϰ° = 1_a` (since `1/∋` is straight). -/
theorem kappaMap_split (a : 𝒜) : kappaMap a ≫ (kappaMap a)° = Cat.id a := by
  unfold kappaMap
  exact Λ_split_monic (invMem_straight a)

/-- **The disjointness** `ℓϰ° = 0`.  Following Freyd: it suffices that
    `Λ(1_[a]) ≫ ϰ° = 0`, which is bounded by `1_[a] / (1/∋)` and reduced through
    `Λ(0), Λ(1) ⊑ 1/∋` and `R/f = Rf°` to `Λ(0)° ∩ Λ(1)° = (Λ(0) ∩ Λ(1))° = 0`. -/
theorem ellMap_kappaMap_disjoint (a : 𝒜) :
    ellMap a ≫ (kappaMap a)° = (𝟘 : a ⟶ a) := by
  -- The core: the second singleton composed with ϰ° vanishes.
  have key :
      Λ (Cat.id (PowerAllegory.powerObj a)) ≫ (kappaMap a)°
        = (𝟘 : PowerAllegory.powerObj a ⟶ a) := by
    refine le_antisymm ?_ (zero_le _)
    -- `ϰ° ⊑ ∋' / (1/∋)`.
    have step1 : (kappaMap a)° ⊑ ∋ (PowerAllegory.powerObj a) / (Cat.id a / ∋ a) := by
      have e : (kappaMap a)°
          = ∋ (PowerAllegory.powerObj a) /ₛ (Cat.id a / ∋ a) := by
        simp only [kappaMap, Λ]; rw [symmDiv_recip]
      rw [e]; exact inter_lb_left _ _
    -- `Λ(1_[a]) = 1_[a] /ₛ ∋' ⊑ 1_[a] / ∋'`.
    have step3 : Λ (Cat.id (PowerAllegory.powerObj a))
        ⊑ Cat.id (PowerAllegory.powerObj a) / ∋ (PowerAllegory.powerObj a) :=
      inter_lb_left _ _
    -- `Λ(0) ⊑ 1/∋` and `Λ(1) ⊑ 1/∋`.
    have hAzero_le : Λ (𝟘 : a ⟶ a) ⊑ Cat.id a / ∋ a :=
      le_trans (inter_lb_left _ _) (div_mono_left (zero_le _) (∋ a))
    have hAone_le : Λ (Cat.id a) ⊑ Cat.id a / ∋ a := inter_lb_left _ _
    -- `1_[a] / Λ(0) ⊑ Λ(0)°`,  `1_[a] / Λ(1) ⊑ Λ(1)°`.
    have h7zero : Cat.id (PowerAllegory.powerObj a) / Λ (𝟘 : a ⟶ a)
        ⊑ (Λ (𝟘 : a ⟶ a))° := by
      have h := div_by_entire_le (Cat.id (PowerAllegory.powerObj a))
        (Λ_is_map' (𝟘 : a ⟶ a)).1
      rwa [Cat.id_comp] at h
    have h7one : Cat.id (PowerAllegory.powerObj a) / Λ (Cat.id a)
        ⊑ (Λ (Cat.id a))° := by
      have h := div_by_entire_le (Cat.id (PowerAllegory.powerObj a))
        (Λ_is_map' (Cat.id a)).1
      rwa [Cat.id_comp] at h
    -- `Λ(0)° ∩ Λ(1)° = (Λ(0) ∩ Λ(1))° = 0°  = 0`.
    have h8 : (Λ (𝟘 : a ⟶ a))° ∩ (Λ (Cat.id a))° = (𝟘 : PowerAllegory.powerObj a ⟶ a) := by
      rw [← Allegory.recip_inter, Λ_zero_inter_Λ_one, recip_zero]
    refine le_trans (comp_mono_left _ step1) ?_
    refine le_trans (comp_mono_right step3 _) ?_
    refine le_trans (div_comp _ _ _) ?_
    refine le_trans
      (le_inter (div_den_antimono _ hAzero_le) (div_den_antimono _ hAone_le)) ?_
    refine le_trans
      (le_inter (le_trans (inter_lb_left _ _) h7zero)
                (le_trans (inter_lb_right _ _) h7one)) ?_
    rw [h8]; exact le_refl _
  -- Assemble: `ℓϰ° = Λ(1_a) ≫ (Λ(1_[a]) ≫ ϰ°) = Λ(1_a) ≫ 0 = 0`.
  unfold ellMap
  rw [Cat.assoc, key, DistributiveAllegory.comp_zero]

/-! ## §2.441 (3) ⟹ (1) -/

/-- **§2.441 (3) ⟹ (1)**: over an unguarded power allegory, STRAIGHT-JOIN implies PRE-POSITIVE.
    Given straight `S₁ : α → γ`, `S₂ : β → γ`, the pre-positive maps into `[[[γ]]]` are
    `f = Λ S₁ ≫ ℓ_[γ]` and `g = Λ S₂ ≫ ϰ_[γ]`. -/
theorem straightJoin_to_prePositive :
    StraightJoinCond 𝒜 → PrePositiveCond 𝒜 := by
  intro hSJ a b
  obtain ⟨γ, S₁, S₂, hS₁, hS₂⟩ := hSJ a b
  refine ⟨PowerAllegory.powerObj (PowerAllegory.powerObj (PowerAllegory.powerObj γ)),
    Λ S₁ ≫ ellMap (PowerAllegory.powerObj γ),
    Λ S₂ ≫ kappaMap (PowerAllegory.powerObj γ),
    map_comp (Λ_is_map' S₁) (ellMap_map _),
    map_comp (Λ_is_map' S₂) (Λ_is_map' _), ?_, ?_, ?_⟩
  · exact split_comp (Λ_split_monic hS₁) (ellMap_split _)
  · exact split_comp (Λ_split_monic hS₂) (kappaMap_split _)
  · exact cross_zero (ellMap_kappaMap_disjoint _)

/-- **§2.441 TFAE, closed** for unguarded power allegories.  Feeding the now-proven
    (3)⟹(1) `straightJoin_to_prePositive` into `prePositive_wellJoined_straightJoin_tfae`
    makes PRE-POSITIVE, WELL-JOINED and STRAIGHT-JOIN pairwise equivalent unconditionally. -/
theorem prePositive_wellJoined_straightJoin_tfae' :
    (PrePositiveCond 𝒜 ↔ WellJoinedCond 𝒜) ∧
    (WellJoinedCond 𝒜 ↔ StraightJoinCond 𝒜) :=
  prePositive_wellJoined_straightJoin_tfae straightJoin_to_prePositive

end Power

end Freyd.Alg
