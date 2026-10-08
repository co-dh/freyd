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
    `hylo_le_of_prefixed`, and **Theorem 6.2** (`hylo_eq_mu`), their antisymmetry.  The note's two chains
    (§11.6.4a/b) draw one panel per step, so each is one `calc`, one law per step, and
    `calc_steps` names the steps.
  * Ex 6.10: hylomorphisms of simple algebra/coalgebra pairs are simple (`mu_simple`,
    `hylo_simple`).
  * Corollary 6.1 (`hylo_body_coprod`, `hylo_eq_mu_coprod`): the hylo body over a
    sum relator `Relator.sumOn` splits into two independent branch bodies joined by `∪`.
-/
module

public import AOP.A6_2
import AOP.CalcSteps

namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

universe u

section Alpha
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

/-! ## B&dM p.142: `⦇α⦈ = id`

  The catamorphism of the initial algebra's own structure map is the identity — the base case
  needed to recognise `relCata_alpha` as the "do nothing" fold, used implicitly throughout
  §6.3's fixed-point reasoning. -/

/-- **B&dM p.142**: `⦇α⦈ = id`. -/
public theorem relCata_alpha (I : InitialAlgebra F) : relCata I.α = Cat.id I.t := by
  have h : I.α ≫ Cat.id I.t = F.map (Cat.id I.t) ≫ I.α := by
    rw [Cat.comp_id, F.map_id, Cat.id_comp]
  exact ((relCata_UP I I.α (Cat.id I.t)).mp h).symm

/-- **B&dM p.142 as the SQUARE the uniqueness produces**: the identity is the ONE arrow making the
    initial algebra's own homomorphism square commute — `αX=F(X)α ⟺ X=𝟙`, which is `relCata_UP` at
    `α` with `⦇α⦈=𝟙` read into its right-hand side. -/
public theorem relCata_alpha_UP (I : InitialAlgebra F) (X : I.t ⟶ I.t) :
    (I.α ≫ X = F.map X ≫ I.α) ↔ X = 𝟙 I.t := by
  rw [relCata_UP I I.α X, relCata_alpha]

end Alpha

-- Tabular from here on, as the whole of AOP is: it makes every relator preserve converse
-- (`Relator.preservesRecip_of_tabular`), so no hylomorphism theorem carries that hypothesis.
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜}

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
public theorem relCata_cancel_recip (I : InitialAlgebra F) {A : 𝒜}
    (R : F.obj A ⟶ A) : (relCata R)° ≫ I.α° = R° ≫ F.map ((relCata R)°) := by
  have hcancel_recip : (I.α ≫ relCata R)° = (F.map (relCata R) ≫ R)° := by
    rw [relCata_cancel I R]
  rw [Allegory.recip_comp, Allegory.recip_comp, ← Relator.preservesRecip_of_tabular F (relCata R)] at hcancel_recip
  exact hcancel_recip

/-! ### The fixed-point chain (note §11.6.4a)

  `S°F(⦇S⦈°⦇R⦈)R = S°F(⦇S⦈°)F(⦇R⦈)R = S°F(⦇S⦈°)α⦇R⦈ = ⦇S⦈°α°α⦇R⦈ = ⦇S⦈°𝟙⦇R⦈ = ⦇S⦈°⦇R⦈`, one
  `calc`, one law per step; `calc_steps` names the steps. -/

/-- The hylomorphism FIXED-POINT EQUATION `[[R,S]] = R·F[[R,S]]·S°` (mirrored) — the form in which
    ch. 9's dynamic-programming theorems consume the hylomorphism theorem (B&dM p.220, "definition
    of `H` and hylomorphism theorem"). -/
public theorem hylo_fixed (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    S° ≫ F.map ((relCata S)° ≫ relCata R) ≫ R = (relCata S)° ≫ relCata R :=
  calc S° ≫ F.map ((relCata S)° ≫ relCata R) ≫ R
      = S° ≫ F.map ((relCata S)°) ≫ F.map (relCata R) ≫ R := by rw [F.map_comp, Cat.assoc]
    _ = S° ≫ F.map ((relCata S)°) ≫ I.α ≫ relCata R := by rw [relCata_cancel I R]
    _ = (relCata S)° ≫ I.α° ≫ I.α ≫ relCata R := by
        rw [← Cat.assoc S°, ← relCata_cancel_recip I S, Cat.assoc]
    _ = (relCata S)° ≫ relCata R := by rw [← Cat.assoc I.α°, I.recip_alpha_alpha, Cat.id_comp]

calc_steps hylo_fixed

/-! ### The leastness chain (note §11.6.4b)

  With `Y ≜ ⦇S⦈°\X`, one term chain `⦇S⦈°α°F(Y)R = S°F(⦇S⦈°)F(Y)R = S°F(⦇S⦈°Y)R ⊑ S°F(X)R ⊑ X`,
  the last step the hypothesis `h`; a `calc` of implications then carries it through the adjunction
  `⦇S⦈°· ⊣ ⦇S⦈°\·` and the fold's leastness to `⦇S⦈°⦇R⦈ ⊑ X`. -/

/-- The term chain at `Y ≜ ⦇S⦈°\X`, ending in the hypothesis `h`. -/
public theorem hylo_le_of_prefixed_chain (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} {X : B ⟶ A} (h : S° ≫ F.map X ≫ R ⊑ X) :
    (relCata S)° ≫ I.α° ≫ F.map (((relCata S)°) \ X) ≫ R ⊑ X :=
  calc (relCata S)° ≫ I.α° ≫ F.map (((relCata S)°) \ X) ≫ R
      = S° ≫ F.map ((relCata S)°) ≫ F.map (((relCata S)°) \ X) ≫ R := by
        rw [← Cat.assoc (relCata S)°, relCata_cancel_recip I S, Cat.assoc]
    _ = S° ≫ F.map ((relCata S)° ≫ (((relCata S)°) \ X)) ≫ R := by rw [F.map_comp, Cat.assoc]
    _ ⊑ S° ≫ F.map X ≫ R := comp_mono_left S° (comp_mono_right (F.map_mono (leftDiv_comp_le _ X)) R)
    _ ⊑ X := h

calc_steps hylo_le_of_prefixed_chain

/-- **Step B of Theorem 6.2**: the hylomorphism `[[R,S]]` refines any prefixed point `X` of the
    body `S° ≫ F.map X ≫ R` — proved DIRECTLY (not via `hylo_eq_mu`, which uses this as its
    leastness half): the term chain, the adjunction `⦇S⦈°· ⊣ ⦇S⦈°\·`, the fold's leastness at the
    prefixed point `Y`, and the adjunction once more. -/
public theorem hylo_le_of_prefixed (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} {X : B ⟶ A} :
    S° ≫ F.map X ≫ R ⊑ X → (relCata S)° ≫ relCata R ⊑ X :=
  calc Imp (S° ≫ F.map X ≫ R ⊑ X) ((relCata S)° ≫ I.α° ≫ F.map (((relCata S)°) \ X) ≫ R ⊑ X) :=
        hylo_le_of_prefixed_chain I
    _ ↔ (I.α° ≫ F.map (((relCata S)°) \ X) ≫ R ⊑ ((relCata S)°) \ X) :=
        (le_leftDiv_iff _ ((relCata S)°) X).symm
    Imp _ (relCata R ⊑ ((relCata S)°) \ X) := relCata_le_of_prefixed I
    _ ↔ ((relCata S)° ≫ relCata R ⊑ X) := le_leftDiv_iff (relCata R) ((relCata S)°) X

calc_steps hylo_le_of_prefixed

/-- **Theorem 6.2 (hylomorphism theorem, B&dM p.142)**: the hylomorphism `[[R,S]]` (mirrored:
    `(|S|)° ≫ (|R|)`) equals the least fixed point of the body `S° ≫ F.map X ≫ R`: `⊑` is
    `hylo_le_of_prefixed` at the prefixed point `μ`, `⊒` is `μ` below the fixed point `hylo_fixed`. -/
public theorem hylo_eq_mu (I : InitialAlgebra F) {A B : 𝒜}
    (R : F.obj A ⟶ A) (S : F.obj B ⟶ B) :
    (relCata S)° ≫ relCata R = mu (fun X : B ⟶ A => S° ≫ F.map X ≫ R) :=
  le_antisymm (hylo_le_of_prefixed I (mu_prefixed (hyloBody_monotonic R S)))
    (mu_le_of_fixed (hylo_fixed I R S))

end Hylo

/-! ## Ex 6.10  Hylomorphisms preserve simplicity

  A fold through a simple algebra composed with an unfold through a simple coalgebra is
  itself simple: neither step can "duplicate" information, so the composite cannot either. -/

section ExSimple

/-- **Ex 6.10**: the least fixed point of `φX = S·FX·R` (mirrored: `S ≫ F.map X ≫ R`, with `S`
    a COALGEBRA `b ⟶ F b`) is `Simple` whenever the algebra `R` and coalgebra `S` both are. -/
theorem mu_simple {A B : 𝒜} {R : F.obj A ⟶ A} {S : B ⟶ F.obj B}
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
      _ = R° ≫ F.map T° ≫ S° := by rw [← Relator.preservesRecip_of_tabular F T]
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
theorem hylo_simple (I : InitialAlgebra F) {A B : 𝒜}
    {R : F.obj A ⟶ A} {S : F.obj B ⟶ B} (hR : Simple R) (hS : Simple (S°)) :
    Simple ((relCata S)° ≫ relCata R) := by
  rw [hylo_eq_mu I R S]
  exact mu_simple hR hS

end ExSimple

/-! ## Corollary 6.1  Coproduct decomposition of the hylo body

  If `F` is the sum relator `G + H` on a coproduct family `C` (`Relator.sumOn C`), and the
  algebra and coalgebra are juncs (case splits) `R = [R₁,R₂]`, `S = [S₁,S₂]` over `C`, then the hylo body decomposes into two INDEPENDENT branch bodies, joined by
  `∪`. Needs `DistributiveAllegory` for `junc`/`Coproduct`, already implied by
  `LocallyCompleteDistributiveAllegory ⊆ UnguardedPowerLCDA`. -/

section Corollary61

/-- Corollary 6.1, the body over `F(X)=G(X)+H(X)`: `[S₁,S₂]°(G(X)+H(X))[R₁,R₂]` is the union of
    the two branch bodies, one law per step. -/
public theorem hylo_body_coprod {G H : Relator 𝒜 𝒜} {T : 𝒜 → 𝒜}
    (C : ∀ x : 𝒜, Coproduct (T x) (G.obj x) (H.obj x))
    {A B : 𝒜} {R₁ : G.obj A ⟶ A} {R₂ : H.obj A ⟶ A} {S₁ : G.obj B ⟶ B} {S₂ : H.obj B ⟶ B}
    (X : B ⟶ A) :
    (junc (C B) S₁ S₂)° ≫ sumMap (C B) (C A) (G.map X) (H.map X) ≫ junc (C A) R₁ R₂
      = (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂) :=
  calc (junc (C B) S₁ S₂)° ≫ sumMap (C B) (C A) (G.map X) (H.map X) ≫ junc (C A) R₁ R₂
        = (junc (C B) S₁ S₂)° ≫ junc (C B) (G.map X ≫ R₁) (H.map X ≫ R₂) := by
        rw [sumMap_junc]
    _ = (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂) := junc_recip_junc (C B)

calc_steps hylo_body_coprod

/-- **Corollary 6.1**, hylo form: Theorem 6.2 over the sum relator `F = G+H` on a coproduct
    family `C`, with both algebras case splits over `C` — the hylomorphism is the `mu` of the
    union of the two branch bodies. -/
public theorem hylo_eq_mu_coprod {G H : Relator 𝒜 𝒜} {T : 𝒜 → 𝒜}
    (C : ∀ x : 𝒜, Coproduct (T x) (G.obj x) (H.obj x)) (I : InitialAlgebra (Relator.sumOn C))
    {A B : 𝒜} {R₁ : G.obj A ⟶ A} {R₂ : H.obj A ⟶ A} {S₁ : G.obj B ⟶ B} {S₂ : H.obj B ⟶ B} :
    (relCata (I := I) (junc (C B) S₁ S₂))° ≫ relCata (I := I) (junc (C A) R₁ R₂)
      = mu (fun X : B ⟶ A => (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂)) := by
  rw [hylo_eq_mu I (junc (C A) R₁ R₂) (junc (C B) S₁ S₂)]
  exact mu_congr (fun X => hylo_body_coprod C X)

end Corollary61

end Freyd.Alg
