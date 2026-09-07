/-
  Bird & de Moor, *Algebra of Programming* §4.6  Power allegories.

  B&dM's power allegory (universal property `f = ΛR ≡ ∈·f = R` for functions `f`) is exactly
  Freyd's `UnguardedPowerAllegory` (Freyd/S2_4.lean): power object `powerObj b`, membership
  `∋ b : powerObj b ⟶ b` (from the power object TO `b`), power transpose `Λ R : a ⟶ powerObj b`
  for `R : a ⟶ b` (`Λ R := R /ₛ ∋ b`), unconditionally a map with `Λ R ≫ ∋ b = R`
  (`Λ_is_map'`, `Λ_eps_eq'`).  Composition throughout is diagram order (`≫`).

  Two of B&dM's book formulas are ALREADY Freyd's definitions/theorems and are not restated:
  - p.107 `ΛR = (∈\R) ∩ (R\∈)°` is literally Freyd's `Λ R := R /ₛ ∋ b` (symmetric division
    unfolds to exactly this meet, §2.331/§2.41).
  - Ex 4.48 `(ΛR)°·ΛS = (R\S) ∩ (S\R)°` is `symm_div_eq_Λ_comp` in `S2_4.lean`.

  `map_comp_div` (A4_4) and `map_shunt_left` (A4_2) are imported; the private wave-time
  copies were deduped at collection.
-/

module

public import Freyd.S2_40
public import AOP.A4_4  -- map_comp_div (and, via A4_2, the shunting rules)

universe u

namespace Freyd.Alg

section DivisionHelpers

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ### Ex 4.49(i) (B&dM p.107): `R` is reflexive and transitive iff `R = R/R`. -/

/-- Ex 4.49(i): for `R : a ⟶ a`, `Reflexive R ∧ Transitive R ↔ R = R / R`. -/
theorem reflexive_transitive_iff_div_self {A : 𝒜} (R : A ⟶ A) :
    (Reflexive R ∧ Transitive R) ↔ R = R / R := by
  constructor
  · rintro ⟨href, htrans⟩
    apply le_antisymm
    · exact (le_div_iff R R R).mpr htrans
    · have step1 : (R / R) ≫ Cat.id A ⊑ (R / R) ≫ R := comp_mono_left _ href
      have step2 : (R / R) ≫ R ⊑ R := div_self_comp_le R
      calc R / R = (R / R) ≫ Cat.id A := (Cat.comp_id _).symm
        _ ⊑ R := le_trans step1 step2
  · intro h
    exact ⟨by rw [h]; exact one_le_div_self R, by rw [h]; exact div_self_idem R⟩

end DivisionHelpers

/-! ## Universal property of `Λ` and the resulting calculus

    From here on we work in an `UnguardedPowerAllegory`, where `Λ_is_map'`/`Λ_eps_eq'` hold
    unconditionally (no box hypothesis), matching B&dM's power allegory exactly. -/

section PowerCalculus

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- B&dM p.103 universal property of `Λ`: for a map `f`,
    `f = Λ R ↔ f ≫ ∋ b = R`. -/
public theorem Λ_UP {A B : 𝒜} (R : A ⟶ B) {f : A ⟶ PowerAllegory.powerObj B} (hf : Map f) :
    f = Λ R ↔ f ≫ ∋ B = R := by
  constructor
  · intro h; rw [h]; exact Λ_eps_eq' R
  · intro h; exact Λ_unique R f hf h

/-- `Λ` is injective: `Λ R = Λ S → R = S`. -/
theorem Λ_injective {A B : 𝒜} {R S : A ⟶ B} (h : Λ R = Λ S) : R = S := by
  rw [← Λ_eps_eq' R, ← Λ_eps_eq' S, h]

/-- B&dM p.104 fusion law: for a map `f : c ⟶ a`, `Λ (f ≫ R) = f ≫ Λ R`. -/
public theorem Λ_fusion {C A : 𝒜} {f : C ⟶ A} (hf : Map f) {B : 𝒜} (R : A ⟶ B) :
    Λ (f ≫ R) = f ≫ Λ R := by
  have hmap : Map (f ≫ Λ R) := map_comp hf (Λ_is_map' R)
  have heq : (f ≫ Λ R) ≫ ∋ B = f ≫ R := by rw [Cat.assoc, Λ_eps_eq']
  exact (Λ_unique _ _ hmap heq).symm

/-- B&dM p.104 reflection law: `Λ (∋ b) = 1_{[b]}` (`Λ∈ = id`). -/
public theorem Λ_eps_reflection {B : 𝒜} : Λ (∋ B) = Cat.id (PowerAllegory.powerObj B) := by
  have heq : Cat.id (PowerAllegory.powerObj B) ≫ ∋ B = ∋ B := Cat.id_comp _
  exact (Λ_unique _ _ (id_is_map_local _) heq).symm

/-! ## Existential image `E` (B&dM p.104-105)

    Restricted to maps `f`, `existsImage f` is B&dM's power functor `P`
    (`Pf x = {f a | a ∈ x}`).  `E` and `P` are written with the same symbol here since Freyd
    embeds `Map(𝒜)` in `𝒜`. -/

/-- The existential-image map `E R : [a] ⟶ [b]` for `R : a ⟶ b` (B&dM p.104-105). -/
@[expose] public def existsImage {A B : 𝒜} (R : A ⟶ B) : PowerAllegory.powerObj A ⟶ PowerAllegory.powerObj B :=
  Λ (∋ A ≫ R)

/-- `∈` is an (exactly) natural transformation (B&dM p.105): `E R ≫ ∋ b = ∋ a ≫ R`. -/
public theorem existsImage_eps {A B : 𝒜} (R : A ⟶ B) : existsImage R ≫ ∋ B = ∋ A ≫ R := Λ_eps_eq' _

/-- `Λ S ≫ E R = Λ (S ≫ R)` (B&dM p.105), the absorption law driving the rest of §4.6. -/
public theorem Λ_absorption {A B C : 𝒜} (S : C ⟶ A) (R : A ⟶ B) :
    Λ S ≫ existsImage R = Λ (S ≫ R) := by
  have hEMap : Map (existsImage R) := Λ_is_map' _
  have hmap : Map (Λ S ≫ existsImage R) := map_comp (Λ_is_map' S) hEMap
  have heq : (Λ S ≫ existsImage R) ≫ ∋ B = S ≫ R := by
    rw [Cat.assoc, existsImage_eps, ← Cat.assoc, Λ_eps_eq']
  exact Λ_unique _ _ hmap heq

/-- `E` preserves identities: `E 1_a = 1_{[a]}`. -/
public theorem existsImage_id {A : 𝒜} : existsImage (Cat.id A) = Cat.id (PowerAllegory.powerObj A) := by
  show Λ (∋ A ≫ Cat.id A) = Cat.id (PowerAllegory.powerObj A)
  rw [Cat.comp_id, Λ_eps_reflection]

/-- `E` is functorial: `E (R ≫ S) = E R ≫ E S`. -/
public theorem existsImage_comp {A B C : 𝒜} (R : A ⟶ B) (S : B ⟶ C) :
    existsImage (R ≫ S) = existsImage R ≫ existsImage S := by
  have h := Λ_absorption (∋ A ≫ R) S
  rw [Cat.assoc] at h
  exact h.symm

/-- Singleton naturality (B&dM p.106): for a map `f`, `f ≫ singletonMap = singletonMap ≫ E f`. -/
theorem singletonMap_natural {A B : 𝒜} {f : A ⟶ B} (hf : Map f) :
    f ≫ singletonMap = singletonMap ≫ existsImage f := by
  have hL : f ≫ singletonMap = Λ f := by
    have h := Λ_fusion hf (Cat.id B)
    rw [Cat.comp_id] at h
    exact h.symm
  have hR : singletonMap ≫ existsImage f = Λ f := by
    rw [singletonMap, Λ_absorption, Cat.id_comp]
  rw [hL, hR]

/-! ## The powerset monad (B&dM p.106: "union `μ = E∈`")

    `bigUnion` (Freyd's `⋃`) IS the powerset-monad multiplication `μ`; these are exactly the
    monad laws for the nondeterminism monad.  Kleisli arrows `a ⟶ [b]` are B&dM's set-valued
    functions and `Λ` is the isomorphism between relations and Kleisli arrows. -/

/-- `bigUnion = E ∋` (definitional: both unfold to `Λ (∋' ≫ ∋)`). -/
public theorem bigUnion_eq_existsImage_eps {A : 𝒜} :
    (bigUnion : PowerAllegory.powerObj (PowerAllegory.powerObj A) ⟶ PowerAllegory.powerObj A)
      = existsImage (∋ A) := rfl

/-- Monad law `μ·τ = id`: `singletonMap ≫ bigUnion = 1`. -/
theorem bigUnion_singleton {A : 𝒜} :
    singletonMap ≫ bigUnion (A := A) = Cat.id (PowerAllegory.powerObj A) := by
  rw [bigUnion_eq_existsImage_eps, singletonMap, Λ_absorption, Cat.id_comp, Λ_eps_reflection]

/-- Monad law `μ·Pτ = id`: `E singletonMap ≫ bigUnion = 1`. -/
public theorem bigUnion_existsImage_singleton {A : 𝒜} :
    existsImage (singletonMap (A := A)) ≫ bigUnion = Cat.id (PowerAllegory.powerObj A) := by
  rw [bigUnion_eq_existsImage_eps, ← existsImage_comp, singletonMap, Λ_eps_eq', existsImage_id]

/-- Monad law `μ·μ = μ·Pμ`: `bigUnion ≫ bigUnion = E bigUnion ≫ bigUnion`. -/
theorem bigUnion_assoc {A : 𝒜} :
    bigUnion ≫ bigUnion (A := A)
      = existsImage (bigUnion (A := A)) ≫ bigUnion := by
  have hL : bigUnion (A := PowerAllegory.powerObj A) ≫ bigUnion (A := A)
      = existsImage (∋ (PowerAllegory.powerObj A) ≫ ∋ A) := by
    rw [bigUnion_eq_existsImage_eps (A := PowerAllegory.powerObj A),
        bigUnion_eq_existsImage_eps (A := A), ← existsImage_comp]
  have hR : existsImage (bigUnion (A := A)) ≫ bigUnion (A := A)
      = existsImage (∋ (PowerAllegory.powerObj A) ≫ ∋ A) := by
    rw [bigUnion_eq_existsImage_eps (A := A), ← existsImage_comp, existsImage_eps]
  exact hL.trans hR.symm

/-- `μ` is NATURAL, on the nose and for every `R` (B&dM p.106): `E(E R) ≫ ⋃ = ⋃ ≫ E R`.
    Both sides are `E (∋ ≫ R)`: on the left `E`'s functoriality then `existsImage_eps`, on the
    right `bigUnion = E ∋`.  `E` itself is NOT a `Relator` — it is not monotone, since a map into
    a power object is determined by its composite with `∋` — so this square cannot be phrased as
    `LaxNatural`; for the relator `P` of §5.4 it becomes `bigUnion_lax_natural` (AOP.A5_4). -/
public theorem bigUnion_natural {A B : 𝒜} (R : A ⟶ B) :
    existsImage (existsImage R) ≫ bigUnion = bigUnion ≫ existsImage R := by
  rw [bigUnion_eq_existsImage_eps (A := B), bigUnion_eq_existsImage_eps (A := A),
      ← existsImage_comp, ← existsImage_comp, existsImage_eps]

/-! ## Ex 4.50 (B&dM p.108): `R` is recovered from its weakest-liberal-precondition data. -/

/-- Ex 4.50: `(∋ b / R) \ ∋ b = R`. -/
theorem leftDiv_div_eps {A B : 𝒜} (R : A ⟶ B) :
    ((∋ B / R) \ (∋ B)) = R := by
  apply le_antisymm
  · have hi : (Λ R)° ⊑ ∋ B / R := by
      apply (le_div_iff _ _ _).mpr
      calc (Λ R)° ≫ R = (Λ R)° ≫ (Λ R ≫ ∋ B) := by rw [Λ_eps_eq']
        _ = ((Λ R)° ≫ Λ R) ≫ ∋ B := by rw [Cat.assoc]
        _ ⊑ Cat.id _ ≫ ∋ B := comp_mono_right (Λ_simple R) _
        _ = ∋ B := Cat.id_comp _
    have hent : Cat.id A ⊑ Λ R ≫ (Λ R)° := by
      have h := (Λ_is_map' R).1
      dsimp [Entire, dom] at h
      rw [← h]; exact inter_lb_right _ _
    -- Combine the three `⊑` steps by hand (no `Trans le le le` instance in this repo).
    have key : Λ R ≫ ((Λ R)° ≫ ((∋ B / R) \ (∋ B))) ⊑ Λ R ≫ ∋ B := by
      have s1 : Λ R ≫ ((Λ R)° ≫ ((∋ B / R) \ (∋ B)))
          ⊑ Λ R ≫ ((∋ B / R) ≫ ((∋ B / R) \ (∋ B))) :=
        comp_mono_left _ (comp_mono_right hi _)
      have s2 : Λ R ≫ ((∋ B / R) ≫ ((∋ B / R) \ (∋ B))) ⊑ Λ R ≫ ∋ B :=
        comp_mono_left _ (leftDiv_comp_le _ _)
      exact le_trans s1 s2
    have step : Cat.id A ≫ ((∋ B / R) \ (∋ B)) ⊑ Λ R ≫ ∋ B := by
      have s0 : Cat.id A ≫ ((∋ B / R) \ (∋ B)) ⊑ (Λ R ≫ (Λ R)°) ≫ ((∋ B / R) \ (∋ B)) :=
        comp_mono_right hent _
      rw [Cat.assoc] at s0
      exact le_trans s0 key
    rw [Cat.id_comp] at step
    calc ((∋ B / R) \ (∋ B)) ⊑ Λ R ≫ ∋ B := step
      _ = R := Λ_eps_eq' R
  · apply (le_leftDiv_iff R (∋ B / R) (∋ B)).mpr
    exact DivisionAllegory.div_comp_le (∋ B) R

/-! ## Ex 4.52 (B&dM p.108): weakest liberal precondition -/

/-- `wlp R` maps a postcondition-set `Y ⊆ b` to `{x ∈ a | ∀ y, x R y → y ∈ Y}`
    (B&dM Ex 4.52). -/
def wlp {A B : 𝒜} (R : A ⟶ B) : PowerAllegory.powerObj B ⟶ PowerAllegory.powerObj A :=
  Λ (∋ B / R)

/-- `wlp` is contravariantly functorial (sequential composition of programs). -/
theorem wlp_comp {A B C : 𝒜} (R : A ⟶ B) (S : B ⟶ C) :
    wlp (R ≫ S) = wlp S ≫ wlp R := by
  have hmap : Map (wlp S ≫ wlp R) := map_comp (Λ_is_map' _) (Λ_is_map' _)
  have heps : (wlp S ≫ wlp R) ≫ ∋ A = ∋ C / (R ≫ S) := by
    rw [Cat.assoc, show wlp R ≫ ∋ A = ∋ B / R from Λ_eps_eq' _,
      map_comp_div (show Map (wlp S) from Λ_is_map' _) (∋ B) R,
      show wlp S ≫ ∋ B = ∋ C / S from Λ_eps_eq' _,
      div_comp_assoc]
  exact (Λ_unique _ _ hmap heps).symm

/-- B&dM 4.52's refinement order: `R ⊑ S` iff `wlp S ≤ wlp R` in the predicate-transformer
    order `f ≤ g ≡ f ≫ ∋ ⊑ g ≫ ∋`. -/
theorem wlp_antitone_iff {A B : 𝒜} (R S : A ⟶ B) :
    R ⊑ S ↔ wlp S ≫ ∋ A ⊑ wlp R ≫ ∋ A := by
  rw [show wlp S ≫ ∋ A = ∋ B / S from Λ_eps_eq' _, show wlp R ≫ ∋ A = ∋ B / R from Λ_eps_eq' _]
  constructor
  · intro h
    apply (le_div_iff _ _ _).mpr
    have s1 : (∋ B / S) ≫ R ⊑ (∋ B / S) ≫ S := comp_mono_left _ h
    have s2 : (∋ B / S) ≫ S ⊑ ∋ B := DivisionAllegory.div_comp_le _ _
    exact le_trans s1 s2
  · intro h
    have hle : R ⊑ ((∋ B / S) \ (∋ B)) := by
      apply (le_leftDiv_iff _ _ _).mpr
      -- `h : ∋ b / S ⊑ ∋ b / R` bounds the LEFT factor, so `comp_mono_right` (not `_left`).
      have s1 : (∋ B / S) ≫ R ⊑ (∋ B / R) ≫ R := comp_mono_right h _
      have s2 : (∋ B / R) ≫ R ⊑ ∋ B := DivisionAllegory.div_comp_le _ _
      exact le_trans s1 s2
    rwa [leftDiv_div_eps] at hle

/-! ## Ex 4.47 (B&dM p.106): singleton/existsImage/bigUnion identities -/

/-- `Λ R = singletonMap ≫ E R`. -/
public theorem Λ_eq_singleton_existsImage {A B : 𝒜} (R : A ⟶ B) :
    Λ R = singletonMap ≫ existsImage R := by
  have h := Λ_absorption (Cat.id A) R
  rw [Cat.id_comp] at h
  exact h.symm

/-- `E R = E (Λ R) ≫ bigUnion`. -/
public theorem existsImage_eq_Λ_bigUnion {A B : 𝒜} (R : A ⟶ B) :
    existsImage R = existsImage (Λ R) ≫ bigUnion := by
  rw [bigUnion_eq_existsImage_eps, ← existsImage_comp, Λ_eps_eq']

end PowerCalculus

-- Printing-only: B&dM's `E R`, with the bracket the note puts round an operator's argument
-- (`E(R)`) — the term itself carries none, so it has to be in the syntax the printer emits.
open Lean PrettyPrinter in
@[app_unexpander existsImage] public meta def unexpandExistsImage : Unexpander
  | `($_ $R) => `($(mkIdent `E) ($R))
  | _ => throw ()

end Freyd.Alg
