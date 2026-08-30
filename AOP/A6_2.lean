/-
  Bird & de Moor, *Algebra of Programming* §6.2  Least fixed points (book pp. 140-142).

  CORE of chapter 6: the Knaster-Tarski theorem (Theorem 6.1) for monotonic mappings on
  the hom-sets of a locally complete (distributive) allegory, the `μ`/`ν` operators, and
  the re-reading of relational catamorphisms as least (and greatest) fixed points,
  giving the inclusion laws (6.2)/(6.3).

  Composition throughout is diagram order (`≫`): B&dM `X·Y` mirrors to `Y ≫ X`.  The
  recursion body `φX = R·FX·α°` therefore mirrors to `φX = α° ≫ F.map X ≫ R`
  (`≫` is right-associative).

  Lambek's lemma (the initial algebra `α` is invertible, with inverse the catamorphism
  of `F.map α`; B&dM Ex 6.5 connects it to the fixed-point view) is proved here because
  (6.2)/(6.3) need `α° ≫ α = id` and `α ≫ α° = id`.

  The merge class `UnguardedPowerLCDA` (locally complete + unguarded power over ONE
  `Allegory` base, diamond-safe as in `AOP.A4_5.DivisionLCDA`) is the ambient setting
  for the whole fixed-point calculus of chapter 6: `Sup`/`Inf` for `μ`/`ν`, division for
  the hylomorphism arguments (§6.3), and `A`/`∋` for `relCata` (`AOP.A5_5`).
-/
module

public import AOP.A4_4
public import AOP.A4_5
public import AOP.A5_5

universe u

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

variable {𝒜 : Type u}

/-! ## §6.2  Theorem 6.1 (Knaster-Tarski)

  For a monotonic `φ` on a hom-set of a locally complete allegory, `φX ⊑ X` and `φX = X`
  have a common least solution `μφ` (= `Inf` of the prefixed points, `AOP.A4_4`), and
  dually `X ⊑ φX` and `φX = X` have a common greatest solution `νφ`. -/

section KnasterTarski

variable [LocallyCompleteDistributiveAllegory 𝒜] {a b : 𝒜}

/-- A MONOTONIC mapping on a hom-set (B&dM Theorem 6.1: "not necessarily a functor"). -/
@[expose] public def Monotonic (φ : (a ⟶ b) → (a ⟶ b)) : Prop :=
  ∀ {X Y : a ⟶ b}, X ⊑ Y → φ X ⊑ φ Y

/-- `(μX : φX)`: the LEAST fixed point of `φ`, as the `Inf` of the prefixed points. -/
@[expose] public def mu (φ : (a ⟶ b) → (a ⟶ b)) : a ⟶ b := Inf (fun X => φ X ⊑ X)

/-- `(νX : φX)`: the GREATEST fixed point of `φ`, as the `Sup` of the postfixed points. -/
@[expose] public def nu (φ : (a ⟶ b) → (a ⟶ b)) : a ⟶ b := Sup (fun X => X ⊑ φ X)

/-- **Theorem 6.1, leastness**: `μφ` is below every prefixed point — the half that bounds a `μ`
    from above, and the only one that needs no monotonicity. -/
public theorem mu_le {φ : (a ⟶ b) → (a ⟶ b)} {Y : a ⟶ b} (h : φ Y ⊑ Y) : mu φ ⊑ Y :=
  Sup_le (fun _S hS => hS _ h)

/-- **Theorem 6.1, first half**: `μφ` is itself a prefixed point. -/
public theorem mu_prefixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : φ (mu φ) ⊑ mu φ :=
  le_Inf (fun _T hT => le_trans (hφ (mu_le hT)) hT)

public theorem mu_postfixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : mu φ ⊑ φ (mu φ) :=
  mu_le (hφ (mu_prefixed hφ))

/-- **Theorem 6.1 (Knaster-Tarski)**: `μφ` is a fixed point — with the `Sup_le`-based lower
    bound (hence `mu_le_of_fixed`), the least solution of `φX ⊑ X` and of `φX = X` coincide. -/
public theorem mu_fixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : φ (mu φ) = mu φ :=
  le_antisymm (mu_prefixed hφ) (mu_postfixed hφ)

public theorem mu_le_of_fixed {φ : (a ⟶ b) → (a ⟶ b)} {T : a ⟶ b} (h : φ T = T) : mu φ ⊑ T :=
  mu_le (show φ T ⊑ T by rw [h]; exact le_refl T)

public theorem nu_postfixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : nu φ ⊑ φ (nu φ) :=
  Sup_le (fun _T hT => le_trans hT (hφ (le_Sup hT)))

public theorem nu_prefixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : φ (nu φ) ⊑ nu φ :=
  le_Sup (hφ (nu_postfixed hφ))

/-- **Theorem 6.1, dual half**: `νφ` is a fixed point — the greatest solution of
    `X ⊑ φX` and of `φX = X` coincide. -/
public theorem nu_fixed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) : φ (nu φ) = nu φ :=
  le_antisymm (nu_prefixed hφ) (nu_postfixed hφ)

theorem le_nu_of_fixed {φ : (a ⟶ b) → (a ⟶ b)} {T : a ⟶ b} (h : φ T = T) : T ⊑ nu φ :=
  le_Sup (by rw [h]; exact le_refl T)

/-- `μ` is monotonic in the mapping: a pointwise-smaller body has a smaller `μ`. -/
public theorem mu_le_mu {φ ψ : (a ⟶ b) → (a ⟶ b)} (h : ∀ X, φ X ⊑ ψ X) : mu φ ⊑ mu ψ :=
  le_Inf (fun T hT => mu_le (le_trans (h T) hT))

/-- `μ` depends only on the body's graph. -/
public theorem mu_congr {φ ψ : (a ⟶ b) → (a ⟶ b)} (h : ∀ X, φ X = ψ X) : mu φ = mu ψ :=
  le_antisymm (mu_le_mu fun X => by rw [h]; exact le_refl _)
    (mu_le_mu fun X => by rw [h]; exact le_refl _)

end KnasterTarski

/-! ## The chapter-6 ambient setting

  §6.3's hylomorphism theorem (and §6.5's uniqueness results) need the fixed-point
  calculus above TOGETHER with `relCata` (`AOP.A5_5`, unguarded power) and division.
  `UnguardedPowerAllegory` already extends `DivisionAllegory`, so one diamond-safe merge
  with the locally complete class covers everything. -/

/-- A locally complete distributive allegory that is ALSO given as an unguarded power
    allegory (diamond-safe merge over one `Allegory` base, as `AOP.A4_5.DivisionLCDA`). -/
public class UnguardedPowerLCDA (𝒜 : Type u) extends
    LocallyCompleteDistributiveAllegory 𝒜, UnguardedPowerAllegory 𝒜

/-- The power side carries division, so the merge is in particular a `DivisionLCDA` —
    lets `AOP.A4_5`'s division/LCDA lemmas fire in the chapter-6 setting. -/
@[expose] public instance (priority := 100) UnguardedPowerLCDA.toDivisionLCDA [inst : UnguardedPowerLCDA 𝒜] :
    DivisionLCDA 𝒜 := { inst with }

/-! ## Lambek's lemma for `InitialAlgebra` (B&dM Ex 6.5's subject)

  The inverse of `α` is the (map) catamorphism of the algebra `F.map α`; the standard
  argument runs entirely inside the map subcategory, then `recip_of_comp_id` (Prop 4.1,
  `AOP.A4_2`) identifies the inverse with `α°`. -/

section Lambek

variable [UnguardedPowerAllegory 𝒜] {F : Relator 𝒜 𝒜}

/-- Lambek inverse: `cata (F.map α)`. -/
@[expose] public def InitialAlgebra.alphaInv (I : InitialAlgebra F) : I.t ⟶ F.obj I.t :=
  I.cata (F.map I.α) (F.map_is_map I.α_map)

/-- **Lambek**: `alphaInv ≫ α = id` — both sides solve the `α`-algebra recursion. -/
public theorem InitialAlgebra.alphaInv_alpha (I : InitialAlgebra F) :
    I.alphaInv ≫ I.α = Cat.id I.t := by
  have hk : I.α ≫ I.alphaInv = F.map I.alphaInv ≫ F.map I.α := I.cata_comm _ _
  have hmap : Map (I.alphaInv ≫ I.α) := map_comp (I.cata_map _ _) I.α_map
  have hcomm : I.α ≫ (I.alphaInv ≫ I.α) = F.map (I.alphaInv ≫ I.α) ≫ I.α := by
    rw [← Cat.assoc, hk, ← F.map_comp]
  have hid : I.α ≫ Cat.id I.t = F.map (Cat.id I.t) ≫ I.α := by
    rw [Cat.comp_id, F.map_id, Cat.id_comp]
  have h1 := I.cata_unique I.α I.α_map _ hmap hcomm
  have h2 := I.cata_unique I.α I.α_map _ (id_is_map_local I.t) hid
  rw [h1, ← h2]

/-- **Lambek**: `α ≫ alphaInv = id`. -/
public theorem InitialAlgebra.alpha_alphaInv (I : InitialAlgebra F) :
    I.α ≫ I.alphaInv = Cat.id (F.obj I.t) := by
  have hk : I.α ≫ I.alphaInv = F.map I.alphaInv ≫ F.map I.α := I.cata_comm _ _
  rw [hk, ← F.map_comp, I.alphaInv_alpha, F.map_id]

/-- The Lambek inverse IS the reciprocal: `alphaInv = α°` (Prop 4.1). -/
public theorem InitialAlgebra.alphaInv_eq_recip (I : InitialAlgebra F) : I.alphaInv = I.α° :=
  (recip_of_comp_id (by rw [I.alpha_alphaInv]; exact le_refl _)
    (by rw [I.alphaInv_alpha]; exact le_refl _)).1

/-- `α° ≫ α = id`: the initial algebra is a split (in fact two-sided) iso of maps. -/
public theorem InitialAlgebra.recip_alpha_alpha (I : InitialAlgebra F) :
    I.α° ≫ I.α = Cat.id I.t := by
  rw [← I.alphaInv_eq_recip]; exact I.alphaInv_alpha

/-- `α ≫ α° = id`. -/
public theorem InitialAlgebra.alpha_alpha_recip (I : InitialAlgebra F) :
    I.α ≫ I.α° = Cat.id (F.obj I.t) := by
  rw [← I.alphaInv_eq_recip]; exact I.alpha_alphaInv

end Lambek

/-! ## §6.2  Catamorphisms as least (and greatest) fixed points: (6.2) and (6.3)

  Because `α` is invertible, the catamorphism UP `α ≫ X = F.map X ≫ R ⟺ X = ⦇R⦈` (5.12)
  re-reads as `X = α° ≫ F.map X ≫ R ⟺ X = ⦇R⦈`: `⦇R⦈` is the UNIQUE fixed point of the
  monotonic body `φX = α° ≫ F.map X ≫ R`, hence equals both `μφ` and `νφ`, and
  Knaster-Tarski turns the equational UP into the inclusion laws (6.2)/(6.3). -/

section CataFix

variable [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-- The recursion body `φX = R·FX·α°` (mirrored: `α° ≫ F.map X ≫ R`) is monotonic. -/
public theorem cataBody_monotonic (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    Monotonic (fun X : I.t ⟶ c => I.α° ≫ F.map X ≫ R) :=
  fun h => comp_mono_left _ (comp_mono_right (F.map_mono h) R)

/-- The catamorphism UP (5.12), fixed-point form: `X = α° ≫ F.map X ≫ R ↔ X = ⦇R⦈`. -/
public theorem eq_relCata_iff_fixed (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c)
    (X : I.t ⟶ c) : X = I.α° ≫ F.map X ≫ R ↔ X = relCata I R := by
  rw [← relCata_UP]
  constructor
  · intro h
    have h2 : I.α ≫ X = I.α ≫ (I.α° ≫ F.map X ≫ R) := by rw [← h]
    rw [h2, ← Cat.assoc, I.alpha_alpha_recip, Cat.id_comp]
  · intro h
    rw [← h, ← Cat.assoc, I.recip_alpha_alpha, Cat.id_comp]

/-- `⦇R⦈ = (μX : R·FX·α°)`, mirrored. -/
public theorem relCata_eq_mu (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    relCata I R = mu (fun X : I.t ⟶ c => I.α° ≫ F.map X ≫ R) := by
  have hfix := mu_fixed (cataBody_monotonic I R)
  exact ((eq_relCata_iff_fixed I R _).mp hfix.symm).symm

/-- `⦇R⦈ = (νX : R·FX·α°)`, mirrored. -/
public theorem relCata_eq_nu (I : InitialAlgebra F) {c : 𝒜} (R : F.obj c ⟶ c) :
    relCata I R = nu (fun X : I.t ⟶ c => I.α° ≫ F.map X ≫ R) := by
  have hfix := nu_fixed (cataBody_monotonic I R)
  exact ((eq_relCata_iff_fixed I R _).mp hfix.symm).symm

/-- **(6.2)**: `⦇R⦈ ⊑ X ⟸ R·FX·α° ⊑ X`, mirrored. -/
public theorem relCata_le_of_prefixed (I : InitialAlgebra F) {c : 𝒜} {R : F.obj c ⟶ c}
    {X : I.t ⟶ c} (h : I.α° ≫ F.map X ≫ R ⊑ X) : relCata I R ⊑ X := by
  rw [relCata_eq_mu]; exact Sup_le (fun _S hS => hS _ h)

/-- **(6.3)**: `X ⊑ ⦇R⦈ ⟸ X ⊑ R·FX·α°`, mirrored. -/
public theorem le_relCata_of_postfixed (I : InitialAlgebra F) {c : 𝒜} {R : F.obj c ⟶ c}
    {X : I.t ⟶ c} (h : X ⊑ I.α° ≫ F.map X ≫ R) : X ⊑ relCata I R := by
  rw [relCata_eq_nu]; exact le_Sup h

end CataFix

/-! ## §6.2  Fusion inclusion laws (6.4)/(6.5), and Ex 6.7 (book p.141)

  These strengthen (6.2)/(6.3) to compose with an arbitrary `S` on the right, using
  `α°≫α = id` (Lambek) to cancel the catamorphism recursion. -/

section Fusion

variable [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-- **(6.4)**: fusion law for the least-fixed-point (prefixed) inclusion. -/
public theorem relCata_le_comp (I : InitialAlgebra F) {c d : 𝒜} {R : F.obj c ⟶ c} {T : F.obj d ⟶ d}
    {S : c ⟶ d} (h : F.map S ≫ T ⊑ R ≫ S) : relCata I T ⊑ relCata I R ≫ S := by
  apply relCata_le_of_prefixed
  have e1 : I.α° ≫ F.map (relCata I R ≫ S) ≫ T
      = I.α° ≫ F.map (relCata I R) ≫ F.map S ≫ T := by rw [F.map_comp, Cat.assoc]
  have e2 : I.α° ≫ F.map (relCata I R) ≫ R ≫ S = relCata I R ≫ S := by
    rw [← Cat.assoc (F.map (relCata I R)) R S, ← relCata_cancel I R,
      Cat.assoc I.α (relCata I R) S, ← Cat.assoc I.α° I.α (relCata I R ≫ S),
      I.recip_alpha_alpha, Cat.id_comp]
  rw [e1]
  calc I.α° ≫ F.map (relCata I R) ≫ F.map S ≫ T
      ⊑ I.α° ≫ F.map (relCata I R) ≫ R ≫ S := comp_mono_left _ (comp_mono_left _ h)
    _ = relCata I R ≫ S := e2

/-- **(6.5)**: fusion law for the greatest-fixed-point (postfixed) inclusion. -/
public theorem comp_le_relCata (I : InitialAlgebra F) {c d : 𝒜} {R : F.obj c ⟶ c} {T : F.obj d ⟶ d}
    {S : c ⟶ d} (h : R ≫ S ⊑ F.map S ≫ T) : relCata I R ≫ S ⊑ relCata I T := by
  apply le_relCata_of_postfixed
  have e1 : relCata I R ≫ S = I.α° ≫ F.map (relCata I R) ≫ R ≫ S := by
    rw [← Cat.assoc (F.map (relCata I R)) R S, ← relCata_cancel I R,
      Cat.assoc I.α (relCata I R) S, ← Cat.assoc I.α° I.α (relCata I R ≫ S),
      I.recip_alpha_alpha, Cat.id_comp]
  have e2 : I.α° ≫ F.map (relCata I R) ≫ F.map S ≫ T
      = I.α° ≫ F.map (relCata I R ≫ S) ≫ T := by rw [F.map_comp, Cat.assoc]
  calc relCata I R ≫ S
      = I.α° ≫ F.map (relCata I R) ≫ R ≫ S := e1
    _ ⊑ I.α° ≫ F.map (relCata I R) ≫ F.map S ≫ T := comp_mono_left _ (comp_mono_left _ h)
    _ = I.α° ≫ F.map (relCata I R ≫ S) ≫ T := e2

/-- **Ex 6.7**: `⦇R⦈ ⊑ ⦇S⦈` when the recursion bodies agree at `⦇S⦈` in the ⊑ direction. -/
public theorem relCata_le_relCata (I : InitialAlgebra F) {c : 𝒜} {R S : F.obj c ⟶ c}
    (h : F.map (relCata I S) ≫ R ⊑ F.map (relCata I S) ≫ S) : relCata I R ⊑ relCata I S := by
  apply relCata_le_of_prefixed
  calc I.α° ≫ F.map (relCata I S) ≫ R
      ⊑ I.α° ≫ F.map (relCata I S) ≫ S := comp_mono_left _ h
    _ = relCata I S := by
        rw [← relCata_cancel I S, ← Cat.assoc I.α° I.α (relCata I S), I.recip_alpha_alpha,
          Cat.id_comp]

/-- **Corollary of Ex 6.7**: `⦇·⦈` is monotonic in the algebra. -/
public theorem relCata_mono (I : InitialAlgebra F) {c : 𝒜} {R S : F.obj c ⟶ c} (h : R ⊑ S) :
    relCata I R ⊑ relCata I S :=
  relCata_le_relCata I (comp_mono_left _ h)

end Fusion

/-! ## §6.2  Kleene's theorem and fixed-point induction (Ex 6.3/6.4, book p.141-142)

  `μφ` also equals the join of the ascending "Kleene chain" `𝟘, φ𝟘, φ(φ𝟘), …`, provided
  `φ` is continuous (preserves joins of ascending ω-chains).  This gives an induction
  principle for `μφ` that only needs finite unfoldings of `φ`. -/

section Kleene

variable [LocallyCompleteDistributiveAllegory 𝒜] {a b : 𝒜}

/-- The Kleene chain `iterZ φ n = φⁿ 𝟘` (B&dM Ex 6.3). -/
def iterZ (φ : (a ⟶ b) → (a ⟶ b)) : Nat → (a ⟶ b)
  | 0 => 𝟘
  | n + 1 => φ (iterZ φ n)

/-- `φ` preserves joins of ascending ω-chains (continuity). -/
def Continuous (φ : (a ⟶ b) → (a ⟶ b)) : Prop :=
  ∀ (C : Nat → (a ⟶ b)), (∀ n, C n ⊑ C (n + 1)) →
    φ (Sup (fun T => ∃ n, T = C n)) = Sup (fun T => ∃ n, T = φ (C n))

/-- The Kleene chain is ascending, for `φ` monotonic. -/
theorem iterZ_ascending {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) :
    ∀ n, iterZ φ n ⊑ iterZ φ (n + 1) := by
  intro n
  induction n with
  | zero => exact zero_le _
  | succ m ih => exact hφ ih

/-- **Kleene's theorem** (B&dM Ex 6.3): for continuous `φ`, `μφ` is the join of the Kleene
    chain, so `μφ` can be computed/reasoned about by finite unfoldings of `φ`. -/
theorem kleene {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) (hc : Continuous φ) :
    mu φ = Sup (fun T => ∃ n, T = iterZ φ n) := by
  have hchain : ∀ n, iterZ φ n ⊑ iterZ φ (n + 1) := iterZ_ascending hφ
  have hcont := hc (iterZ φ) hchain
  have heq2 : Sup (fun T => ∃ n, T = φ (iterZ φ n)) = Sup (fun T => ∃ n, T = iterZ φ n) := by
    apply le_antisymm
    · apply Sup_le
      intro T hT
      obtain ⟨n, hn⟩ := hT
      rw [hn]
      exact le_Sup ⟨n + 1, rfl⟩
    · apply Sup_le
      intro T hT
      obtain ⟨n, hn⟩ := hT
      rw [hn]
      exact le_trans (hchain n) (le_Sup ⟨n, rfl⟩)
  have hfix : φ (Sup (fun T => ∃ n, T = iterZ φ n)) = Sup (fun T => ∃ n, T = iterZ φ n) := by
    rw [hcont, heq2]
  have hiter_le : ∀ n, iterZ φ n ⊑ mu φ := by
    intro n
    induction n with
    | zero => exact zero_le _
    | succ m ih =>
        have step : φ (iterZ φ m) ⊑ φ (mu φ) := hφ ih
        rw [mu_fixed hφ] at step
        exact step
  apply le_antisymm
  · exact mu_le_of_fixed hfix
  · apply Sup_le
    intro T hT
    obtain ⟨n, hn⟩ := hT
    rw [hn]
    exact hiter_le n

/-- **Fixed-point induction, Kleene form** (B&dM Ex 6.4): to show `μφ ⊑ T` it suffices that
    `T` absorbs one step of `φ` from below any `X ⊑ T` — i.e. `T` is "closed" under `φ`. -/
theorem mu_le_of_closed {φ : (a ⟶ b) → (a ⟶ b)} (hφ : Monotonic φ) (hc : Continuous φ)
    {T : a ⟶ b} (h : ∀ X, X ⊑ T → φ X ⊑ T) : mu φ ⊑ T := by
  rw [kleene hφ hc]
  apply Sup_le
  intro S hS
  obtain ⟨n, hn⟩ := hS
  rw [hn]
  clear hn S
  induction n with
  | zero => exact zero_le _
  | succ m ih => exact h _ ih

end Kleene

/-! ## §6.2  μ-calculus laws: rolling and diagonal (B&dM Ex 6.35, book p.142)

  These move `μ` across a "wrapper" map and merge two nested `μ`'s into one, using only
  Knaster-Tarski (`Sup_le`'s lower-bound half/`mu_prefixed`) and monotonicity — no continuity
  needed. -/

section MuCalculus

variable [LocallyCompleteDistributiveAllegory 𝒜] {a b : 𝒜}

/-- Monotonicity for a map between (possibly different) hom-sets.  `Monotonic φ` is
    definitionally `MonotonicHom φ` when the hom-sets coincide. -/
@[expose] public def MonotonicHom {c d : 𝒜} (φ : (a ⟶ b) → (c ⟶ d)) : Prop :=
  ∀ {X Y : a ⟶ b}, X ⊑ Y → φ X ⊑ φ Y

/-- **Rolling rule** (B&dM Ex 6.35): `μ(φ∘ψ) = φ(μ(ψ∘φ))`. -/
public theorem mu_rolling {c d : 𝒜} {φ : (a ⟶ b) → (c ⟶ d)} {ψ : (c ⟶ d) → (a ⟶ b)}
    (hφ : MonotonicHom φ) (hψ : MonotonicHom ψ) :
    mu (fun X => φ (ψ X)) = φ (mu (fun Y => ψ (φ Y))) := by
  have hφψ : Monotonic (fun X => φ (ψ X)) := fun h => hφ (hψ h)
  have hψφ : Monotonic (fun Y => ψ (φ Y)) := fun h => hψ (hφ h)
  have h1 : mu (fun X => φ (ψ X)) ⊑ φ (mu (fun Y => ψ (φ Y))) :=
    mu_le (hφ (mu_prefixed hψφ))
  have h2 : mu (fun Y => ψ (φ Y)) ⊑ ψ (mu (fun X => φ (ψ X))) :=
    mu_le (hψ (mu_prefixed hφψ))
  have h3 : φ (mu (fun Y => ψ (φ Y))) ⊑ mu (fun X => φ (ψ X)) :=
    le_trans (hφ h2) (mu_prefixed hφψ)
  exact le_antisymm h1 h3

/-- **Diagonal rule** (B&dM Ex 6.35): `μX.μY.φXY = μX.φXX`. -/
theorem mu_diagonal {φ : (a ⟶ b) → (a ⟶ b) → (a ⟶ b)} (h1 : ∀ Y, Monotonic (fun X => φ X Y))
    (h2 : ∀ X, Monotonic (fun Y => φ X Y)) :
    mu (fun X => mu (fun Y => φ X Y)) = mu (fun X => φ X X) := by
  have hg : Monotonic (fun X => mu (fun Y => φ X Y)) := fun hX => mu_le_mu (fun Y => h1 Y hX)
  have hd : Monotonic (fun X => φ X X) := fun hX => le_trans (h1 _ hX) (h2 _ hX)
  have hA : mu (fun X => φ X X) ⊑ mu (fun X => mu (fun Y => φ X Y)) := by
    refine Sup_le (fun _S hS => hS _ ?_)
    have hTfix : mu (fun Y => φ (mu (fun X => mu (fun Y => φ X Y))) Y)
        = mu (fun X => mu (fun Y => φ X Y)) := mu_fixed hg
    have hstep := mu_prefixed (h2 (mu (fun X => mu (fun Y => φ X Y))))
    rw [hTfix] at hstep
    exact hstep
  have hB : mu (fun X => mu (fun Y => φ X Y)) ⊑ mu (fun X => φ X X) := by
    refine Sup_le (fun _S hS => hS _ ?_)
    have hSfix : φ (mu (fun X => φ X X)) (mu (fun X => φ X X)) = mu (fun X => φ X X) :=
      mu_fixed hd
    refine Sup_le (fun _S hS => hS _ ?_)
    show φ (mu fun X => φ X X) (mu fun X => φ X X) ⊑ mu fun X => φ X X
    rw [hSfix]
    exact le_refl _
  exact le_antisymm hB hA

/- **Substitution rule** (B&dM's third Ex 6.35 rule): DROPPED.  The book's own text for the
   proof of this rule is illegible OCR ("a simple combination of the preceding two rules"),
   and — unlike rolling/diagonal, whose statements are pinned down unambiguously by the
   book's `μx.fx = f(μx.fx)`-style equations quoted elsewhere — no single substitution
   instance of rolling+diagonal reads as *the* canonical "substitution rule" without
   guessing extra structure the book does not state.  Rolling (`mu_rolling`) and diagonal
   (`mu_diagonal`) are proved above and are the two rules the book actually uses elsewhere
   (e.g. in the hylomorphism uniqueness arguments of §6.5); the substitution rule is not
   used downstream in this repo, so it is left as a documented gap rather than an invented
   theorem. -/

end MuCalculus

/-! ## §6.2  Difunctional closure (B&dM Ex 6.8, book p.142)

  `R` is difunctional when `R·R°·R = R`; the least difunctional relation containing `R` is
  the least fixed point of `X ↦ R ∪ X·X°·X`, using `R ⊑ R·R°·R` (B&dM 4.10, `AOP.A4_1`)
  for the "already difunctional" direction. -/

section Difunctional

variable [LocallyCompleteDistributiveAllegory 𝒜] {a b : 𝒜}

/-- **(B&dM Ex 6.8)**: `R` is difunctional when `R·R°·R = R`, mirrored `R≫R°≫R = R`. -/
def Difunctional (R : a ⟶ b) : Prop := R ≫ R° ≫ R = R

/-- The difunctional closure of `R`, as the least fixed point of `X ↦ R ∪ X·X°·X`. -/
def difunClosure (R : a ⟶ b) : a ⟶ b := mu (fun X => R ∪ X ≫ X° ≫ X)

/-- The recursion body `X ↦ R ∪ X·X°·X` is monotonic. -/
theorem difunClosure_body_monotonic (R : a ⟶ b) :
    Monotonic (fun X : a ⟶ b => R ∪ X ≫ X° ≫ X) := by
  intro X Y h
  have hXXX : X ≫ X° ≫ X ⊑ Y ≫ Y° ≫ Y :=
    le_trans (comp_mono_right h _)
      (le_trans (comp_mono_left Y (comp_mono_right (recip_mono h) _))
        (comp_mono_left Y (comp_mono_left Y° h)))
  exact union_mono (le_refl R) hXXX

theorem le_difunClosure (R : a ⟶ b) : R ⊑ difunClosure R := by
  have hfix : R ∪ difunClosure R ≫ (difunClosure R)° ≫ difunClosure R = difunClosure R :=
    mu_fixed (difunClosure_body_monotonic R)
  rw [← hfix]
  exact le_union_left _ _

/-- The closure is difunctional: `⊑` from the fixed-point equation, `⊒` from (4.10). -/
theorem difunClosure_difunctional (R : a ⟶ b) : Difunctional (difunClosure R) := by
  unfold Difunctional
  have hfix : R ∪ difunClosure R ≫ (difunClosure R)° ≫ difunClosure R = difunClosure R :=
    mu_fixed (difunClosure_body_monotonic R)
  apply le_antisymm
  · calc difunClosure R ≫ (difunClosure R)° ≫ difunClosure R
        ⊑ R ∪ difunClosure R ≫ (difunClosure R)° ≫ difunClosure R := le_union_right _ _
      _ = difunClosure R := hfix
  · have h := le_comp_recip_comp (difunClosure R)
    rw [Cat.assoc] at h
    exact h

/-- The closure is least among difunctional relations containing `R` (`D` is a prefixed
    point of the recursion body). -/
theorem difunClosure_le {R D : a ⟶ b} (hD : Difunctional D) (h : R ⊑ D) : difunClosure R ⊑ D := by
  unfold difunClosure
  refine Sup_le (fun _S hS => hS _ ?_)
  show R ∪ D ≫ D° ≫ D ⊑ D
  have hD' : D ≫ D° ≫ D = D := hD
  rw [hD']
  exact union_lub h (le_refl D)

end Difunctional

end Freyd.Alg
