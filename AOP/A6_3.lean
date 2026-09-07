/-
  Bird & de Moor, *Algebra of Programming* §6.3  Hylomorphisms (book pp. 142-144).

  A HYLOMORPHISM combines an unfold (through a coalgebra `S : b ⟶ F b`) with a fold (through
  an algebra `R : F a ⟶ a`) into one recursive definition `[[R,S]] = (|S|)°·(|R|)` (mirrored:
  `(relCata I S)° ≫ relCata I R`).  **Theorem 6.2** identifies it with the least fixed point of
  the body `φX = S·FX·R` (mirrored: `S° ≫ F.map X ≫ R`) — the composite of an unfold and a fold
  is itself characterised as a fixed point, which is the point of the whole exercise: it lets
  one reason about the composite without materialising the intermediate structure `F b`/`b`.

  Composition throughout is diagram order (`≫`): B&dM `X·Y` mirrors to `Y ≫ X`.

  Contents:
  * `relCata_alpha`  (B&dM p.142): `⦇α⦈ = id`.
  * `hyloBody_monotonic`, the fixed-point equation `hylo_fixed`, the leastness
    `hylo_le_of_prefixed`, and **Theorem 6.2** (`hylo_eq_mu`).  The note's three chains
    (§11.6.4a/b/c) draw one panel per step, so each step is a `*_step<k>` theorem of its own and
    the three named theorems are their composition.
  * Ex 6.10: hylomorphisms of simple algebra/coalgebra pairs are simple (`mu_simple`,
    `hylo_simple`).
  * Corollary 6.1 (`hylo_body_coprod_decompose`, `hylo_eq_mu_coprod`): the hylo body over a
    coproduct-decomposed relator splits into two independent branch bodies joined by `∪`.
-/
module

public import AOP.A6_2
public import AOP.A5_3

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

universe u
variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-! ## B&dM p.142: `⦇α⦈ = id`

  The catamorphism of the initial algebra's own structure map is the identity — the base case
  needed to recognise `relCata_alpha` as the "do nothing" fold, used implicitly throughout
  §6.3's fixed-point reasoning. -/

/-- **B&dM p.142**: `⦇α⦈ = id`. -/
public theorem relCata_alpha (I : InitialAlgebra F) : relCata I.α = Cat.id I.t := by
  have h : I.α ≫ Cat.id I.t = F.map (Cat.id I.t) ≫ I.α := by
    rw [Cat.comp_id, F.map_id, Cat.id_comp]
  exact ((relCata_UP I I.α (Cat.id I.t)).mp h).symm

/-! ## §6.3  Theorem 6.2 (the hylomorphism theorem)

  The hylomorphism `[[R,S]] = (|S|)°·(|R|)` (mirrored: `(relCata I S)° ≫ relCata I R`) is the
  least fixed point of `φX = S·FX·R` (mirrored: `S° ≫ F.map X ≫ R`). -/

section Hylo

/-- The hylomorphism recursion body `φX = S·FX·R` (mirrored: `S° ≫ F.map X ≫ R`) is
    monotonic (B&dM p.142), by the same argument as `cataBody_monotonic` (`AOP.A6_2`). -/
public theorem hyloBody_monotonic {A B : 𝒜} (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    Monotonic (fun X : B ⟶ A => S° ≫ F.map X ≫ R) :=
  fun h => comp_mono_left _ (comp_mono_right (F.map_mono h) R)

/-- The CONVERSE of the fold's cancellation law `α⦇R⦈ = F(⦇R⦈)R` (`relCata_cancel`), which needs
    the relator to preserve converse: `⦇R⦈°α° = R°F(⦇R⦈°)`.  Both hylomorphism chains carry a
    leading `⦇S⦈°α°` across the unfold with it. -/
public theorem relCata_cancel_recip (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A : 𝒜}
    (R : F.obj A ⟶ A) : (relCata R)° ≫ I.α° = R° ≫ F.map ((relCata R)°) := by
  have hcancel_recip : (I.α ≫ relCata R)° = (F.map (relCata R) ≫ R)° := by
    rw [relCata_cancel I R]
  rw [Allegory.recip_comp, Allegory.recip_comp, ← hFr (relCata R)] at hcancel_recip
  exact hcancel_recip

/-! ### The fixed-point chain (note §11.6.4a)

  `S°F(⦇S⦈°⦇R⦈)R = S°F(⦇S⦈°)F(⦇R⦈)R = S°F(⦇S⦈°)α⦇R⦈ = ⦇S⦈°α°α⦇R⦈ = ⦇S⦈°⦇R⦈`, one theorem per
  step; `hylo_fixed` is their composition. -/

/-- Step 1: the relator splits the composite, `F(⦇S⦈°⦇R⦈) = F(⦇S⦈°)F(⦇R⦈)`. -/
public theorem hylo_fixed_step1 (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    S° ≫ F.map ((relCata S)° ≫ relCata R) ≫ R
      = S° ≫ F.map ((relCata S)°) ≫ F.map (relCata R) ≫ R := by
  rw [F.map_comp, Cat.assoc]

/-- Step 2: the fold's cancellation `F(⦇R⦈)R = α⦇R⦈` (`relCata_cancel` at `R`). -/
public theorem hylo_fixed_step2 (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    S° ≫ F.map ((relCata S)°) ≫ F.map (relCata R) ≫ R
      = S° ≫ F.map ((relCata S)°) ≫ I.α ≫ relCata R := by
  rw [relCata_cancel I R]

/-- Step 3: the unfold's conversed cancellation `⦇S⦈°α° = S°F(⦇S⦈°)`, read backwards. -/
public theorem hylo_fixed_step3 (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    S° ≫ F.map ((relCata S)°) ≫ I.α ≫ relCata R
      = (relCata S)° ≫ I.α° ≫ I.α ≫ relCata R :=
  calc S° ≫ F.map ((relCata S)°) ≫ I.α ≫ relCata R
      = (S° ≫ F.map ((relCata S)°)) ≫ I.α ≫ relCata R := (Cat.assoc _ _ _).symm
    _ = ((relCata S)° ≫ I.α°) ≫ I.α ≫ relCata R := by rw [relCata_cancel_recip hFr I S]
    _ = (relCata S)° ≫ I.α° ≫ I.α ≫ relCata R := Cat.assoc _ _ _

/-- Step 4: `α°α = 𝟙`, so the two structure maps cancel. -/
public theorem hylo_fixed_step4 (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    (relCata S)° ≫ I.α° ≫ I.α ≫ relCata R = (relCata S)° ≫ relCata R := by
  rw [← Cat.assoc I.α° I.α (relCata R), I.recip_alpha_alpha, Cat.id_comp]

/-- The hylomorphism FIXED-POINT EQUATION `[[R,S]] = R·F[[R,S]]·S°` (mirrored) — the form in which
    ch. 9's dynamic-programming theorems consume the hylomorphism theorem (B&dM p.220, "definition
    of `H` and hylomorphism theorem"). -/
public theorem hylo_fixed (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    S° ≫ F.map ((relCata S)° ≫ relCata R) ≫ R = (relCata S)° ≫ relCata R :=
  ((hylo_fixed_step1 I R S).trans (hylo_fixed_step2 I R S)).trans
    ((hylo_fixed_step3 hFr I R S).trans (hylo_fixed_step4 I R S))

/-! ### The leastness chain (note §11.6.4b)

  Six inclusions, each implying the one above it:
  `⦇S⦈°⦇R⦈⊑X ⟸ ⦇R⦈⊑⦇S⦈°\X ⟸ α°F(⦇S⦈°\X)R⊑⦇S⦈°\X ⟸ ⦇S⦈°α°F(⦇S⦈°\X)R⊑X
   ⟸ S°F(⦇S⦈°)F(⦇S⦈°\X)R⊑X ⟸ S°F(X)R⊑X`.
  The last is the hypothesis `h`, so every step carries it; they are declared bottom-up, which is
  the order in which they are proved. -/

/-- Step 4, the row above the hypothesis: the relator rejoins `F(⦇S⦈°)F(⦇S⦈°\X)` into
    `F(⦇S⦈°(⦇S⦈°\X))`, and the division's counit `⦇S⦈°(⦇S⦈°\X) ⊑ X` reduces it to `h`. -/
public theorem hylo_le_of_prefixed_step4 (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} {X : B ⟶ A} (h : S° ≫ F.map X ≫ R ⊑ X) :
    S° ≫ F.map ((relCata S)°) ≫ F.map (((relCata S)°) \ X) ≫ R ⊑ X := by
  have hcomp : S° ≫ F.map ((relCata S)°) ≫ F.map (((relCata S)°) \ X) ≫ R
      = S° ≫ F.map ((relCata S)° ≫ (((relCata S)°) \ X)) ≫ R := by
    rw [F.map_comp, Cat.assoc]
  rw [hcomp]
  have hWX : (relCata S)° ≫ (((relCata S)°) \ X) ⊑ X := leftDiv_comp_le _ X
  exact le_trans (comp_mono_left S° (comp_mono_right (F.map_mono hWX) R)) h

/-- Step 3: `⦇S⦈°α° = S°F(⦇S⦈°)` (`relCata_cancel_recip`) rewrites the head of step 4's row. -/
public theorem hylo_le_of_prefixed_step3 (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} {X : B ⟶ A} (h : S° ≫ F.map X ≫ R ⊑ X) :
    (relCata S)° ≫ I.α° ≫ F.map (((relCata S)°) \ X) ≫ R ⊑ X := by
  have hkey : (relCata S)° ≫ I.α° ≫ F.map (((relCata S)°) \ X) ≫ R
      = S° ≫ F.map ((relCata S)°) ≫ F.map (((relCata S)°) \ X) ≫ R :=
    calc (relCata S)° ≫ I.α° ≫ F.map (((relCata S)°) \ X) ≫ R
        = ((relCata S)° ≫ I.α°) ≫ F.map (((relCata S)°) \ X) ≫ R := (Cat.assoc _ _ _).symm
      _ = (S° ≫ F.map ((relCata S)°)) ≫ F.map (((relCata S)°) \ X) ≫ R := by
          rw [relCata_cancel_recip hFr I S]
      _ = S° ≫ F.map ((relCata S)°) ≫ F.map (((relCata S)°) \ X) ≫ R := Cat.assoc _ _ _
  rw [hkey]
  exact hylo_le_of_prefixed_step4 I h

/-- Step 2: the division adjunction `⦇S⦈°· ⊣ ⦇S⦈°\·` (`le_leftDiv_iff`) moves the leading
    converse to the other side. -/
public theorem hylo_le_of_prefixed_step2 (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} {X : B ⟶ A} (h : S° ≫ F.map X ≫ R ⊑ X) :
    I.α° ≫ F.map (((relCata S)°) \ X) ≫ R ⊑ ((relCata S)°) \ X :=
  (le_leftDiv_iff _ ((relCata S)°) X).mpr (hylo_le_of_prefixed_step3 hFr I h)

/-- Step 1: the fold's own leastness (`relCata_le_of_prefixed`) at the prefixed point
    `⦇S⦈°\X`. -/
public theorem hylo_le_of_prefixed_step1 (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} {X : B ⟶ A} (h : S° ≫ F.map X ≫ R ⊑ X) :
    relCata R ⊑ ((relCata S)°) \ X :=
  relCata_le_of_prefixed I (hylo_le_of_prefixed_step2 hFr I h)

/-- **Step B of Theorem 6.2**: the hylomorphism `[[R,S]]` refines any prefixed point `X` of the
    body `S° ≫ F.map X ≫ R` — proved DIRECTLY (not via `hylo_eq_mu`, which uses this as its
    leastness half). -/
public theorem hylo_le_of_prefixed (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} {X : B ⟶ A} (h : S° ≫ F.map X ≫ R ⊑ X) :
    (relCata S)° ≫ relCata R ⊑ X :=
  (le_leftDiv_iff (relCata R) ((relCata S)°) X).mp (hylo_le_of_prefixed_step1 hFr I h)

/-! ### The two inclusions of Theorem 6.2 (note §11.6.4c)

  `(μX : S°F(X)R) ⊑ ⦇S⦈°⦇R⦈ ⊑ (μX : S°F(X)R)`: the chain leaves `μ` and comes back to it, so
  `hylo_eq_mu` is the antisymmetry of the two steps. -/

/-- Step 1: `μ` is below every fixed point, and `hylo_fixed` says `⦇S⦈°⦇R⦈` is one. -/
public theorem hylo_eq_mu_step1 (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    mu (fun X : B ⟶ A => S° ≫ F.map X ≫ R) ⊑ (relCata S)° ≫ relCata R :=
  mu_le_of_fixed (hylo_fixed hFr I R S)

/-- Step 2: `hylo_le_of_prefixed` at the prefixed point `μ` itself. -/
public theorem hylo_eq_mu_step2 (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    (relCata S)° ≫ relCata R ⊑ mu (fun X : B ⟶ A => S° ≫ F.map X ≫ R) :=
  hylo_le_of_prefixed hFr I (mu_prefixed (hyloBody_monotonic R S))

/-- **Theorem 6.2 (hylomorphism theorem, B&dM p.142)**: the hylomorphism `[[R,S]]` (mirrored:
    `(|S|)° ≫ (|R|)`) equals the least fixed point of the body `S° ≫ F.map X ≫ R`. -/
public theorem hylo_eq_mu (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    (relCata S)° ≫ relCata R = mu (fun X : B ⟶ A => S° ≫ F.map X ≫ R) :=
  le_antisymm (hylo_eq_mu_step2 hFr I R S) (hylo_eq_mu_step1 hFr I R S)

end Hylo

/-! ## Ex 6.10  Hylomorphisms preserve simplicity

  A fold through a simple algebra composed with an unfold through a simple coalgebra is
  itself simple: neither step can "duplicate" information, so the composite cannot either. -/

section ExSimple

/-- **Ex 6.10**: the least fixed point of `φX = S·FX·R` (mirrored: `S ≫ F.map X ≫ R`, with `S`
    a COALGEBRA `b ⟶ F b`) is `Simple` whenever the algebra `R` and coalgebra `S` both are. -/
theorem mu_simple (hFr : F.PreservesRecip) {A B : 𝒜} {R : F.obj A ⟶ A} {S : B ⟶ F.obj B}
    (hR : Simple R) (hS : Simple S) :
    Simple (mu (fun X : B ⟶ A => S ≫ F.map X ≫ R)) := by
  let T : B ⟶ A := mu (fun X : B ⟶ A => S ≫ F.map X ≫ R)
  show Simple T
  have hφ_mono : Monotonic (fun X : B ⟶ A => S ≫ F.map X ≫ R) :=
    fun h => comp_mono_left _ (comp_mono_right (F.map_mono h) R)
  have hTfix : S ≫ F.map T ≫ R = T := mu_fixed hφ_mono
  have hTrecip : T° = R° ≫ F.map T° ≫ S° :=
    calc T° = (S ≫ F.map T ≫ R)° := by rw [hTfix]
      _ = (F.map T ≫ R)° ≫ S° := Allegory.recip_comp S (F.map T ≫ R)
      _ = (R° ≫ (F.map T)°) ≫ S° := by rw [Allegory.recip_comp]
      _ = R° ≫ (F.map T)° ≫ S° := Cat.assoc R° (F.map T)° S°
      _ = R° ≫ F.map T° ≫ S° := by rw [← hFr T]
  show T° ≫ T ⊑ Cat.id A
  apply (le_leftDiv_iff T T° (Cat.id A)).mp
  have hWprefixed : S ≫ F.map (T° \ (Cat.id A)) ≫ R ⊑ (T° \ (Cat.id A)) := by
    apply (le_leftDiv_iff _ T° (Cat.id A)).mpr
    have step1 : T° ≫ S ⊑ R° ≫ F.map T° := by
      have e : T° ≫ S = R° ≫ F.map T° ≫ S° ≫ S := by
        have e0 : T° ≫ S = (R° ≫ F.map T° ≫ S°) ≫ S := congrArg (· ≫ S) hTrecip
        rw [Cat.assoc, Cat.assoc] at e0
        exact e0
      have hmono : R° ≫ F.map T° ≫ S° ≫ S ⊑ R° ≫ F.map T° ≫ Cat.id (F.obj B) :=
        comp_mono_left _ (comp_mono_left _ hS)
      rw [Cat.comp_id] at hmono
      rw [e]; exact hmono
    have hmono2 : (T° ≫ S) ≫ F.map (T° \ (Cat.id A)) ≫ R
        ⊑ (R° ≫ F.map T°) ≫ F.map (T° \ (Cat.id A)) ≫ R :=
      comp_mono_right step1 _
    have heq2 : (R° ≫ F.map T°) ≫ F.map (T° \ (Cat.id A)) ≫ R
        = R° ≫ F.map (T° ≫ (T° \ (Cat.id A))) ≫ R := by
      rw [Cat.assoc, F.map_comp, Cat.assoc]
    have hWX : T° ≫ (T° \ (Cat.id A)) ⊑ Cat.id A := leftDiv_comp_le T° (Cat.id A)
    have hmono4 : R° ≫ F.map (T° ≫ (T° \ (Cat.id A))) ≫ R ⊑ R° ≫ F.map (Cat.id A) ≫ R :=
      comp_mono_left _ (comp_mono_right (F.map_mono hWX) R)
    have heq5 : R° ≫ F.map (Cat.id A) ≫ R = R° ≫ R := by rw [F.map_id, Cat.id_comp]
    rw [← Cat.assoc]
    refine le_trans hmono2 ?_
    rw [heq2]
    refine le_trans hmono4 ?_
    rw [heq5]
    exact hR
  exact Sup_le (fun _S hS => hS _ hWprefixed)

/-- Corollary in hylomorphism form: the body `S° ≫ F.map X ≫ R` of `hylo_eq_mu` matches
    `mu_simple`'s body with coalgebra `S°`, giving simplicity of the hylomorphism from
    simplicity of `R` and of `S°`. -/
theorem hylo_simple (hFr : F.PreservesRecip) (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} (hR : Simple R) (hS : Simple (S°)) :
    Simple ((relCata S)° ≫ relCata R) := by
  rw [hylo_eq_mu hFr I R S]
  exact mu_simple hFr hR hS

end ExSimple

/-! ## Corollary 6.1  Coproduct decomposition of the hylo body

  If `F` is presented over a coproduct decomposition `F ≅ G + H` (each `F.obj x` a coproduct of
  `G.obj x` and `H.obj x`, with `F`'s action on morphisms matching `sumMap`), and the algebra and
  coalgebra are themselves juncs (case splits) `R = [R₁,R₂]`, `S = [S₁,S₂]` against that same
  decomposition, then the hylo body decomposes into two INDEPENDENT branch bodies, joined by
  `∪`. Needs `DistributiveAllegory` for `junc`/`Coproduct`, already implied by
  `LocallyCompleteDistributiveAllegory ⊆ UnguardedPowerLCDA`. -/

section Corollary61

/-- **Corollary 6.1**, the body decomposition: `S° ≫ F.map X ≫ R = (S₁°≫G.map X≫R₁) ∪
    (S₂°≫H.map X≫R₂)` when `R = [R₁,R₂]`, `S = [S₁,S₂]` are juncs over `F`'s coproduct
    presentation `F.map X = sumMap (C x) (C y) (G.map X) (H.map X)`. -/
theorem hylo_body_coprod_decompose {G H : Relator 𝒜 𝒜}
    (C : ∀ x : 𝒜, Coproduct (F.obj x) (G.obj x) (H.obj x))
    (hF : ∀ {x y : 𝒜} (X : x ⟶ y), F.map X = sumMap (C x) (C y) (G.map X) (H.map X))
    {A B : 𝒜} {R₁ : G.obj A ⟶ A} {R₂ : H.obj A ⟶ A} {S₁ : G.obj B ⟶ B} {S₂ : H.obj B ⟶ B}
    (X : B ⟶ A) :
    (junc (C B) S₁ S₂)° ≫ F.map X ≫ junc (C A) R₁ R₂
      = (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂) := by
  rw [hF X]
  show (junc (C B) S₁ S₂)°
      ≫ junc (C B) (G.map X ≫ (C A).u₁) (H.map X ≫ (C A).u₂) ≫ junc (C A) R₁ R₂
      = (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂)
  rw [← Cat.assoc, junc_recip_junc (C B)]
  have hb1 : (S₁° ≫ (G.map X ≫ (C A).u₁)) ≫ junc (C A) R₁ R₂ = S₁° ≫ G.map X ≫ R₁ := by
    rw [Cat.assoc, Cat.assoc, u₁_junc]
  have hb2 : (S₂° ≫ (H.map X ≫ (C A).u₂)) ≫ junc (C A) R₁ R₂ = S₂° ≫ H.map X ≫ R₂ := by
    rw [Cat.assoc, Cat.assoc, u₂_junc]
  rw [union_comp_distrib, hb1, hb2]

/-- **Corollary 6.1**, hylo form: transporting `hylo_eq_mu`'s fixed-point equation through the
    body decomposition (`mu_congr`) — the hylomorphism over a coproduct-decomposed `F` equals
    the `mu` of the two-branch body directly, with NO reference to `F`, `G.map`/`H.map`'s common
    ambient functor beyond what's already in the branch bodies. -/
theorem hylo_eq_mu_coprod (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {G H : Relator 𝒜 𝒜} (C : ∀ x : 𝒜, Coproduct (F.obj x) (G.obj x) (H.obj x))
    (hF : ∀ {x y : 𝒜} (X : x ⟶ y), F.map X = sumMap (C x) (C y) (G.map X) (H.map X))
    {A B : 𝒜} {R₁ : G.obj A ⟶ A} {R₂ : H.obj A ⟶ A} {S₁ : G.obj B ⟶ B} {S₂ : H.obj B ⟶ B} :
    (relCata (junc (C B) S₁ S₂))° ≫ relCata (junc (C A) R₁ R₂)
      = mu (fun X : B ⟶ A => (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂)) := by
  rw [hylo_eq_mu hFr I (junc (C A) R₁ R₂) (junc (C B) S₁ S₂)]
  exact mu_congr (fun X => hylo_body_coprod_decompose C hF X)

end Corollary61

end Freyd.Alg
