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
  * `hyloBody_monotonic`, **Theorem 6.2** (`hylo_eq_mu`) and its corollary `hylo_le_of_prefixed`.
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
public theorem relCata_alpha (I : InitialAlgebra F) : relCata I I.α = Cat.id I.t := by
  have h : I.α ≫ Cat.id I.t = F.map (Cat.id I.t) ≫ I.α := by
    rw [Cat.comp_id, F.map_id, Cat.id_comp]
  exact ((relCata_UP I I.α (Cat.id I.t)).mp h).symm

/-! ## §6.3  Theorem 6.2 (the hylomorphism theorem)

  The hylomorphism `[[R,S]] = (|S|)°·(|R|)` (mirrored: `(relCata I S)° ≫ relCata I R`) is the
  least fixed point of `φX = S·FX·R` (mirrored: `S° ≫ F.map X ≫ R`). -/

section Hylo

/-- The hylomorphism recursion body `φX = S·FX·R` (mirrored: `S° ≫ F.map X ≫ R`) is
    monotonic (B&dM p.142), by the same argument as `cataBody_monotonic` (`AOP.A6_2`). -/
public theorem hyloBody_monotonic {a b : 𝒜} (R : F.obj a ⟶ a) (S : F.obj b ⟶ b) :
    Monotonic (fun X : b ⟶ a => S° ≫ F.map X ≫ R) :=
  fun h => comp_mono_left _ (comp_mono_right (F.map_mono h) R)

/-- **Step B of Theorem 6.2**: the hylomorphism `[[R,S]]` refines any prefixed point `X` of the
    body `S° ≫ F.map X ≫ R` — proved DIRECTLY (not via `hylo_eq_mu`, which uses this as its
    leastness half). -/
public theorem hylo_le_of_prefixed (hFr : F.PreservesRecip) (I : InitialAlgebra F) {a b : 𝒜}
    {R : F.obj a ⟶ a} {S : F.obj b ⟶ b} {X : b ⟶ a} (h : S° ≫ F.map X ≫ R ⊑ X) :
    (relCata I S)° ≫ relCata I R ⊑ X := by
  apply (le_leftDiv_iff (relCata I R) ((relCata I S)°) X).mp
  apply relCata_le_of_prefixed
  apply (le_leftDiv_iff _ ((relCata I S)°) X).mpr
  have hkey : (relCata I S)° ≫ I.α° = S° ≫ F.map ((relCata I S)°) := by
    have hcancel_recip : (I.α ≫ relCata I S)° = (F.map (relCata I S) ≫ S)° := by
      rw [relCata_cancel I S]
    rw [Allegory.recip_comp, Allegory.recip_comp, ← hFr (relCata I S)] at hcancel_recip
    exact hcancel_recip
  have hcomp : (relCata I S)° ≫ I.α° ≫ F.map (((relCata I S)°) \ X) ≫ R
      = S° ≫ F.map ((relCata I S)° ≫ (((relCata I S)°) \ X)) ≫ R := by
    rw [F.map_comp, ← Cat.assoc, ← Cat.assoc, hkey, Cat.assoc, Cat.assoc, Cat.assoc]
  rw [hcomp]
  have hWX : (relCata I S)° ≫ (((relCata I S)°) \ X) ⊑ X := leftDiv_comp_le _ X
  exact le_trans (comp_mono_left S° (comp_mono_right (F.map_mono hWX) R)) h

/-- **Theorem 6.2 (hylomorphism theorem, B&dM p.142)**: the hylomorphism `[[R,S]]` (mirrored:
    `(|S|)° ≫ (|R|)`) equals the least fixed point of the body `S° ≫ F.map X ≫ R`. -/
public theorem hylo_eq_mu (hFr : F.PreservesRecip) (I : InitialAlgebra F) {a b : 𝒜}
    (R : F.obj a ⟶ a) (S : F.obj b ⟶ b) :
    (relCata I S)° ≫ relCata I R = mu (fun X : b ⟶ a => S° ≫ F.map X ≫ R) := by
  have hφ_mono : Monotonic (fun X : b ⟶ a => S° ≫ F.map X ≫ R) := hyloBody_monotonic R S
  have hstepA : S° ≫ F.map ((relCata I S)° ≫ relCata I R) ≫ R
      = (relCata I S)° ≫ relCata I R := by
    have h1 : F.map ((relCata I S)° ≫ relCata I R)
        = (F.map (relCata I S))° ≫ F.map (relCata I R) := by
      rw [F.map_comp, hFr]
    have h4 : S° ≫ (F.map (relCata I S))° = (relCata I S)° ≫ I.α° := by
      have hcancel_recip : (I.α ≫ relCata I S)° = (F.map (relCata I S) ≫ S)° := by
        rw [relCata_cancel I S]
      rw [Allegory.recip_comp, Allegory.recip_comp] at hcancel_recip
      exact hcancel_recip.symm
    rw [h1, ← Cat.assoc, ← Cat.assoc, h4, Cat.assoc, Cat.assoc, ← relCata_cancel I R,
      ← Cat.assoc I.α° I.α (relCata I R), I.recip_alpha_alpha, Cat.id_comp]
  exact le_antisymm (hylo_le_of_prefixed hFr I (mu_prefixed hφ_mono)) (mu_le_of_fixed hstepA)

/-- The hylomorphism FIXED-POINT EQUATION `[[R,S]] = R·F[[R,S]]·S°` (mirrored), extracted from
    Theorem 6.2 via `mu_fixed` — the form in which ch. 9's dynamic-programming theorems consume
    the hylomorphism theorem (B&dM p.220, "definition of `H` and hylomorphism theorem"). -/
public theorem hylo_fixed (hFr : F.PreservesRecip) (I : InitialAlgebra F) {a b : 𝒜}
    (R : F.obj a ⟶ a) (S : F.obj b ⟶ b) :
    S° ≫ F.map ((relCata I S)° ≫ relCata I R) ≫ R = (relCata I S)° ≫ relCata I R := by
  rw [hylo_eq_mu hFr I R S]
  exact mu_fixed (hyloBody_monotonic R S)

end Hylo

/-! ## Ex 6.10  Hylomorphisms preserve simplicity

  A fold through a simple algebra composed with an unfold through a simple coalgebra is
  itself simple: neither step can "duplicate" information, so the composite cannot either. -/

section ExSimple

/-- **Ex 6.10**: the least fixed point of `φX = S·FX·R` (mirrored: `S ≫ F.map X ≫ R`, with `S`
    a COALGEBRA `b ⟶ F b`) is `Simple` whenever the algebra `R` and coalgebra `S` both are. -/
theorem mu_simple (hFr : F.PreservesRecip) {a b : 𝒜} {R : F.obj a ⟶ a} {S : b ⟶ F.obj b}
    (hR : Simple R) (hS : Simple S) :
    Simple (mu (fun X : b ⟶ a => S ≫ F.map X ≫ R)) := by
  let T : b ⟶ a := mu (fun X : b ⟶ a => S ≫ F.map X ≫ R)
  show Simple T
  have hφ_mono : Monotonic (fun X : b ⟶ a => S ≫ F.map X ≫ R) :=
    fun h => comp_mono_left _ (comp_mono_right (F.map_mono h) R)
  have hTfix : S ≫ F.map T ≫ R = T := mu_fixed hφ_mono
  have hTrecip : T° = R° ≫ F.map T° ≫ S° :=
    calc T° = (S ≫ F.map T ≫ R)° := by rw [hTfix]
      _ = (F.map T ≫ R)° ≫ S° := Allegory.recip_comp S (F.map T ≫ R)
      _ = (R° ≫ (F.map T)°) ≫ S° := by rw [Allegory.recip_comp]
      _ = R° ≫ (F.map T)° ≫ S° := Cat.assoc R° (F.map T)° S°
      _ = R° ≫ F.map T° ≫ S° := by rw [← hFr T]
  show T° ≫ T ⊑ Cat.id a
  apply (le_leftDiv_iff T T° (Cat.id a)).mp
  have hWprefixed : S ≫ F.map (T° \ (Cat.id a)) ≫ R ⊑ (T° \ (Cat.id a)) := by
    apply (le_leftDiv_iff _ T° (Cat.id a)).mpr
    have step1 : T° ≫ S ⊑ R° ≫ F.map T° := by
      have e : T° ≫ S = R° ≫ F.map T° ≫ S° ≫ S := by
        have e0 : T° ≫ S = (R° ≫ F.map T° ≫ S°) ≫ S := congrArg (· ≫ S) hTrecip
        rw [Cat.assoc, Cat.assoc] at e0
        exact e0
      have hmono : R° ≫ F.map T° ≫ S° ≫ S ⊑ R° ≫ F.map T° ≫ Cat.id (F.obj b) :=
        comp_mono_left _ (comp_mono_left _ hS)
      rw [Cat.comp_id] at hmono
      rw [e]; exact hmono
    have hmono2 : (T° ≫ S) ≫ F.map (T° \ (Cat.id a)) ≫ R
        ⊑ (R° ≫ F.map T°) ≫ F.map (T° \ (Cat.id a)) ≫ R :=
      comp_mono_right step1 _
    have heq2 : (R° ≫ F.map T°) ≫ F.map (T° \ (Cat.id a)) ≫ R
        = R° ≫ F.map (T° ≫ (T° \ (Cat.id a))) ≫ R := by
      rw [Cat.assoc, F.map_comp, Cat.assoc]
    have hWX : T° ≫ (T° \ (Cat.id a)) ⊑ Cat.id a := leftDiv_comp_le T° (Cat.id a)
    have hmono4 : R° ≫ F.map (T° ≫ (T° \ (Cat.id a))) ≫ R ⊑ R° ≫ F.map (Cat.id a) ≫ R :=
      comp_mono_left _ (comp_mono_right (F.map_mono hWX) R)
    have heq5 : R° ≫ F.map (Cat.id a) ≫ R = R° ≫ R := by rw [F.map_id, Cat.id_comp]
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
theorem hylo_simple (hFr : F.PreservesRecip) (I : InitialAlgebra F) {a b : 𝒜}
    {R : F.obj a ⟶ a} {S : F.obj b ⟶ b} (hR : Simple R) (hS : Simple (S°)) :
    Simple ((relCata I S)° ≫ relCata I R) := by
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
    {a b : 𝒜} {R₁ : G.obj a ⟶ a} {R₂ : H.obj a ⟶ a} {S₁ : G.obj b ⟶ b} {S₂ : H.obj b ⟶ b}
    (X : b ⟶ a) :
    (junc (C b) S₁ S₂)° ≫ F.map X ≫ junc (C a) R₁ R₂
      = (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂) := by
  rw [hF X]
  show (junc (C b) S₁ S₂)°
      ≫ junc (C b) (G.map X ≫ (C a).u₁) (H.map X ≫ (C a).u₂) ≫ junc (C a) R₁ R₂
      = (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂)
  rw [← Cat.assoc, junc_recip_junc (C b)]
  have hb1 : (S₁° ≫ (G.map X ≫ (C a).u₁)) ≫ junc (C a) R₁ R₂ = S₁° ≫ G.map X ≫ R₁ := by
    rw [Cat.assoc, Cat.assoc, u₁_junc]
  have hb2 : (S₂° ≫ (H.map X ≫ (C a).u₂)) ≫ junc (C a) R₁ R₂ = S₂° ≫ H.map X ≫ R₂ := by
    rw [Cat.assoc, Cat.assoc, u₂_junc]
  rw [union_comp_distrib, hb1, hb2]

/-- **Corollary 6.1**, hylo form: transporting `hylo_eq_mu`'s fixed-point equation through the
    body decomposition (`mu_congr`) — the hylomorphism over a coproduct-decomposed `F` equals
    the `mu` of the two-branch body directly, with NO reference to `F`, `G.map`/`H.map`'s common
    ambient functor beyond what's already in the branch bodies. -/
theorem hylo_eq_mu_coprod (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {G H : Relator 𝒜 𝒜} (C : ∀ x : 𝒜, Coproduct (F.obj x) (G.obj x) (H.obj x))
    (hF : ∀ {x y : 𝒜} (X : x ⟶ y), F.map X = sumMap (C x) (C y) (G.map X) (H.map X))
    {a b : 𝒜} {R₁ : G.obj a ⟶ a} {R₂ : H.obj a ⟶ a} {S₁ : G.obj b ⟶ b} {S₂ : H.obj b ⟶ b} :
    (relCata I (junc (C b) S₁ S₂))° ≫ relCata I (junc (C a) R₁ R₂)
      = mu (fun X : b ⟶ a => (S₁° ≫ G.map X ≫ R₁) ∪ (S₂° ≫ H.map X ≫ R₂)) := by
  rw [hylo_eq_mu hFr I (junc (C a) R₁ R₂) (junc (C b) S₁ S₂)]
  exact mu_congr (fun X => hylo_body_coprod_decompose C hF X)

end Corollary61

end Freyd.Alg
