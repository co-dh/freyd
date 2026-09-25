/-
  Bird & de Moor, *Algebra of Programming* §9.1  Dynamic programming: theory (book pp. 219-224)
  — CORE (Theorem 9.1).

  The optimisation problem is `min R · Λ(⦇h⦈·⦇T⦈°)` (mirrored: `Λ H ≫ est R` with
  `H := (relCata I T)° ≫ relCata I h`): unfold the input through the coalgebra `T°`, refold
  through the F-algebra `h` (a function), and take an `R`-minimum over all results.  DYNAMIC
  PROGRAMMING is the recursion that decomposes the input in ALL possible ways, solves the
  subproblems recursively, and assembles an optimum from the partial results (the principle of
  optimality) — the least fixed point `μX. min R · P(h·FX) · ΛT°`.  **Theorem 9.1**: if `h` is
  monotonic on `R` (and `R` transitive), the recursion refines the specification.

  MIRRORING (diagram order, B&dM `X·Y` = Freyd `Y ≫ X`; B&dM `R/S` = Freyd `(S \ R)`):
  - B&dM `H = ⦇h⦈·⦇T⦈°` is `(relCata I T)° ≫ relCata I h : b ⟶ a` (`h : F.obj a ⟶ a`,
    `T : F.obj b ⟶ b`); the fixed-point equation `H = h·FH·T°` is `AOP.A6_3`'s `hylo_fixed`:
    `T° ≫ F.map H ≫ h = H`.
  - B&dM `M = min R·ΛH` is `Λ H ≫ est R`.
  - the recursion body `min R · P(h·FX) · ΛT°` is
    `Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R`.
  - rule (9.4) `min R·PX ⊆ (X·∈) ∩ ((R·X)/∋)` is `AOP.A7_1`'s `powerRel_comp_est_le`;
    `ΛT°·T ⊆ ∋` is `AOP.A8_1`'s `recip_comp_Λ_le_recip_eps` at `T°`.

  Setting: `TabularUnitaryUnguardedPowerLCDA` (`AOP.A6_2`), continuing chapters 7 and 8.
-/
module

public import AOP.A7_2
public import AOP.A8_1
public import AOP.A5_2
-- Proposition 9.1's coproduct split is proved at the END of this file in the Set model, over
-- `F L E X = L+(X×E)`; the generic form needs a typeclass the repo does not have (drop note).
public import AOP.A6_SnocList
-- For `junc` AT AN INJECTION (`ListRel.junc_sum_inl`/`_inr`): the one place the coproduct's own
-- equations are read back, and the snoc-list side needs the same two facts the cons-list side did.
public import AOP.A5_6_ListCombinators

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {A B : 𝒜}

/-- **`H≜⦇T⦈°⦇h⦈ : A⟶B`** (B&dM p.220): decompose through the coalgebra `T°` and reassemble
    through the algebra `h`.  It is the arrow the optimisation problem `H%∋ est(R)` is taken of,
    and a name of its own is what lets a picture draw it as one bead. -/
@[expose] public def H [InitialAlgebra F] (T : F.obj A ⟶ A) (h : F.obj B ⟶ B) : A ⟶ B :=
  (relCata T)° ≫ relCata h

/-! ## Theorem 9.1 (B&dM pp. 220-221) -/

/-- (9.2), first step: rule (9.4) `P(X) est(R) ⊑ ∋X` (`powerRel_comp_est_le`, left meet
    component) at `X ≜ F(M)h`. -/
public theorem dynamic_programming_lower_step1 {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {H : A ⟶ B} :
    Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
      ⊑ Λ (T°) ≫ ∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h :=
  comp_mono_left _ (le_trans (powerRel_comp_est_le _ R) (inter_lb_left _ _))

/-- (9.2), second step: Λ cancellation, `Λ(T°)∋ = T°`. -/
public theorem dynamic_programming_lower_step2 {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {H : A ⟶ B} :
    Λ (T°) ≫ ∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h = T° ≫ F.map (Λ H ≫ est R) ≫ h := by
  rw [← Cat.assoc (Λ (T°)) (∋ (F.obj A)) _, Λ_eps_eq']

/-- (9.2), third step: `M ⊑ H`, the first component of the universal property of `est`
    (`le_Λ_comp_est_iff`) at `M ≜ Λ(H) est(R)`, under `F` and before `h`. -/
public theorem dynamic_programming_lower_step3 {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {H : A ⟶ B} :
    T° ≫ F.map (Λ H ≫ est R) ≫ h ⊑ T° ≫ F.map H ≫ h :=
  comp_mono_left _ (comp_mono_right (F.map_mono (le_Λ_comp_est_iff.mp (le_refl (Λ H ≫ est R))).1) h)

/-- **(9.2)** (B&dM p.220): `min R·P(h·FM)·ΛT° ⊆ H`, mirrored — with `M ≜ Λ(H) est(R)`, taking
    the input apart every way `T` allows, solving each part by `M` and keeping an optimum stays
    inside `H`.  The book's four hints are steps 1–3 and the fixed-point equation `hHfix` (the
    definition of `H` and the hylomorphism theorem, `hylo_fixed`). -/
public theorem dynamic_programming_lower {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {H : A ⟶ B} (hHfix : T° ≫ F.map H ≫ h = H) :
    Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R ⊑ H :=
  calc Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
      _ ⊑ Λ (T°) ≫ ∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h := dynamic_programming_lower_step1
      _ = T° ≫ F.map (Λ H ≫ est R) ≫ h := dynamic_programming_lower_step2
      _ ⊑ T° ≫ F.map H ≫ h := dynamic_programming_lower_step3
      _ = H := hHfix

/-- **Core of Theorem 9.1**: `M = min R°·ΛH` (mirrored `Λ H ≫ est R`) is a PREFIXED point of
    the dynamic-programming body, for ANY `H` satisfying the hylomorphism fixed-point equation
    `H = h·FH·T°` (mirrored `T° ≫ F.map H ≫ h = H`) — Theorems 9.1/9.2 and the exercise
    variants all instantiate `H := ⦇h⦈·⦇T⦈°`.  The two inclusions (9.2) and (9.3) of the book's
    proof are exactly the components of `min`'s universal property (`le_Λ_comp_est_iff`). -/
public theorem dp_prefixed (hFr : F.PreservesRecip) {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {H : A ⟶ B} (hh : Map h) (hmono : MonotonicAlg h R°)
    (htrans : R° ≫ R° ⊑ R°) (hHfix : T° ≫ F.map H ≫ h = H) :
    Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R ⊑ Λ H ≫ est R := by
  -- the two min-UP components of `M ⊑ min R°·ΛH`: `M ⊑ H` and `M·H° ⊑ R°` (mirrored)
  obtain ⟨-, hHMR⟩ := le_Λ_comp_est_iff.mp (le_refl (Λ H ≫ est R))
  -- rule (9.4) at `X := h·FM`
  have h94 := powerRel_comp_est_le (F.map (Λ H ≫ est R) ≫ h) R
  apply le_Λ_comp_est_iff.mpr
  constructor
  · exact dynamic_programming_lower hHfix
  · -- (9.3): `min R°·P(h·FM)·ΛT°·H° ⊆ R°`
    -- the lower-bound component of (9.4)
    have hL : powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ (((∋ (F.obj A))°) \ ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) :=
      le_trans h94 (inter_lb_right _ _)
    -- `ΛT°·T ⊆ ∋` mirrored
    have hTA : T ≫ Λ (T°) ⊑ (∋ (F.obj A))° := by
      have h0 := recip_comp_Λ_le_recip_eps (T°)
      rwa [Allegory.recip_recip] at h0
    -- `H° = T·FH°·h°` conversed to diagram order: `H° = h° ≫ F.map H° ≫ T`
    have hHrec : H° = h° ≫ F.map (H°) ≫ T := by
      have h1 : (T° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ T := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H,
          Cat.assoc]
      rw [← h1, hHfix]
    -- the tail after peeling `h° ≫ F.map H°`: division cancels against `∋`
    have htail : T ≫ Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ (F.map (Λ H ≫ est R) ≫ h) ≫ R° := by
      have t1 : T ≫ Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
          ⊑ T ≫ Λ (T°) ≫ (((∋ (F.obj A))°) \ ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) :=
        comp_mono_left _ (comp_mono_left _ hL)
      have t2 : T ≫ Λ (T°) ≫ (((∋ (F.obj A))°) \ ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))
          ⊑ (∋ (F.obj A))° ≫ (((∋ (F.obj A))°) \ ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) := by
        rw [← Cat.assoc T (Λ (T°)) _]
        exact comp_mono_right hTA _
      exact le_trans t1 (le_trans t2 (leftDiv_comp_le _ _))
    -- split `H°` in front and reassociate
    have c1 : H° ≫ Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        = (h° ≫ F.map (H°) ≫ T)
            ≫ Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R := by
      rw [← hHrec]
    have c2 : (h° ≫ F.map (H°) ≫ T)
          ≫ Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        = (h° ≫ F.map (H°))
            ≫ T ≫ Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R := by
      simp only [Cat.assoc]
    have hbound : (h° ≫ F.map (H°))
          ≫ T ≫ Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ (h° ≫ F.map (H°)) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° :=
      comp_mono_left _ htail
    -- collapse: `F(M·H°) ⊆ FR` then conjugated monotonicity and transitivity
    have hcollapse : (h° ≫ F.map (H°)) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° ⊑ R° ≫ R° := by
      have hFRM : F.map (H°) ≫ F.map (Λ H ≫ est R) ⊑ F.map R° := by
        rw [← F.map_comp]
        exact F.map_mono hHMR
      have hinner : h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h ⊑ R° := by
        have hx : h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h ⊑ h° ≫ F.map R° ≫ h := by
          rw [← Cat.assoc (F.map (H°)) (F.map (Λ H ≫ est R)) h]
          exact comp_mono_left _ (comp_mono_right hFRM h)
        exact le_trans hx ((monotonicAlg_iff_conj hh).mp hmono)
      have hre : (h° ≫ F.map (H°)) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R°
          = (h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h) ≫ R° := by
        simp only [Cat.assoc]
      rw [hre]
      exact comp_mono_right hinner R°
    rw [c1, c2]
    exact le_trans (le_trans hbound hcollapse) htrans

/-- **Theorem 9.1 (B&dM p.220)**, the basic theorem of DYNAMIC PROGRAMMING:
    `(μX : min R°·P(h·FX)·ΛT°) ⊆ min R°·ΛH` for `H = ⦇h⦈·⦇T⦈°`, mirrored — if the algebra `h`
    is monotonic on the transitive `R°`, then decomposing the input in all possible ways
    (`ΛT°`), solving subproblems recursively (`P(h·FX)`) and keeping an optimum of the partial
    results (`min R°`) refines "generate everything, then pick a global optimum".
    By Knaster–Tarski (`Sup_le`'s lower-bound half) via `dp_prefixed`. -/
public theorem dynamic_programming (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _ (dp_prefixed hFr hh hmono htrans (hylo_fixed hFr I h T)))

/-! ## Theorem 9.2 (B&dM p.221) — thinning dynamic programming

  Thinning at every unfold step (`ΛT° ≫ thin Q`), before recursing and taking the `R`-minimum,
  still refines "generate everything, then minimize" — PROVIDED the thinning preorder `Q`
  interacts correctly with the algebra `h` through the current best guess `H` (hypothesis
  `hQ` below).  B&dM state the theorem for `Q` a preorder on `F(dom H)`; the refinement itself
  needs no reflexivity/transitivity of `Q` beyond `hQ`, so we drop those hypotheses here (they
  only matter for `dynamic_programming_of_thin`, Ex 9.1, which recovers Theorem 9.1 at `Q :=
  id`, where reflexivity IS needed to discharge `hQ`). -/

/-- **Core of Theorem 9.2**: `M = min R°·ΛH` is a prefixed point of the THINNING
    dynamic-programming body `min R°·P(h·FX)·thin Q·ΛT°` (mirrored), for any `H` satisfying the
    hylomorphism fixed-point equation, given the thinning-compatibility hypothesis `hQ` (B&dM
    p.221's unlabelled preorder condition connecting `Q` to `H` through `h`).  Same skeleton
    as `dp_prefixed`, with a `thinRel Q` factor threaded through both halves of the min
    universal property. -/
theorem dp_thin_prefixed (hFr : F.PreservesRecip) {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} {H : A ⟶ B} (hh : Map h) (hmono : MonotonicAlg h R°)
    (htrans : R° ≫ R° ⊑ R°) (hHfix : T° ≫ F.map H ≫ h = H)
    (hQ : Q ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R) :
    Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R ⊑ Λ H ≫ est R := by
  obtain ⟨hMH, hHMR⟩ := le_Λ_comp_est_iff.mp (le_refl (Λ H ≫ est R))
  have h94 := powerRel_comp_est_le (F.map (Λ H ≫ est R) ≫ h) R
  apply le_Λ_comp_est_iff.mpr
  constructor
  · -- (9.2)-with-thin: `min R°·P(h·FM)·thin Q·ΛT° ⊆ H`
    have step1 : Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h) :=
      comp_mono_left _ (comp_mono_left _ (le_trans h94 (inter_lb_left _ _)))
    have step2 : Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h)
        ⊑ T° ≫ F.map (Λ H ≫ est R) ≫ h := by
      have e1 : Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h)
          = (Λ (T°) ≫ (thinRel Q ≫ ∋ (F.obj A))) ≫ F.map (Λ H ≫ est R) ≫ h := by
        simp only [Cat.assoc]
      rw [e1]
      have e2 : (Λ (T°) ≫ (thinRel Q ≫ ∋ (F.obj A))) ≫ F.map (Λ H ≫ est R) ≫ h
          ⊑ (Λ (T°) ≫ ∋ (F.obj A)) ≫ F.map (Λ H ≫ est R) ≫ h :=
        comp_mono_right (comp_mono_left _ (thinRel_comp_eps_le Q)) _
      have e3 : (Λ (T°) ≫ ∋ (F.obj A)) ≫ F.map (Λ H ≫ est R) ≫ h
          = T° ≫ F.map (Λ H ≫ est R) ≫ h := by rw [Λ_eps_eq']
      rwa [e3] at e2
    have step3 : T° ≫ F.map (Λ H ≫ est R) ≫ h ⊑ T° ≫ F.map H ≫ h :=
      comp_mono_left _ (comp_mono_right (F.map_mono hMH) h)
    rw [hHfix] at step3
    exact le_trans step1 (le_trans step2 step3)
  · -- (9.3)-with-thin: `H°·min R°·P(h·FM)·thin Q·ΛT° ⊆ R°`
    have hL := le_trans h94 (inter_lb_right _ _)
    have hTA : T ≫ Λ (T°) ⊑ (∋ (F.obj A))° := by
      have h0 := recip_comp_Λ_le_recip_eps (T°)
      rwa [Allegory.recip_recip] at h0
    have hHrec : H° = h° ≫ F.map (H°) ≫ T := by
      have h1 : (T° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ T := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H, Cat.assoc]
      rw [← h1, hHfix]
    -- the tail bound: peel `T·ΛT°` down to `∋°`, then `thin Q` down to `Q°·∋°`
    have t1 : T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ T ≫ Λ (T°) ≫ (thinRel Q ≫ (((∋ (F.obj A))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))) :=
      comp_mono_left _ (comp_mono_left _ (comp_mono_left _ hL))
    have t2 : T ≫ Λ (T°) ≫ (thinRel Q ≫ (((∋ (F.obj A))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)))
        ⊑ (∋ (F.obj A))° ≫ (thinRel Q ≫ (((∋ (F.obj A))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))) := by
      rw [← Cat.assoc T (Λ (T°)) _]
      exact comp_mono_right hTA _
    have t3 : (∋ (F.obj A))° ≫ (thinRel Q ≫ (((∋ (F.obj A))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)))
        ⊑ (Q° ≫ (∋ (F.obj A))°) ≫ (((∋ (F.obj A))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) := by
      rw [← Cat.assoc]
      exact comp_mono_right (recip_eps_comp_thinRel_le Q) _
    have t4 : (Q° ≫ (∋ (F.obj A))°) ≫ (((∋ (F.obj A))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))
        ⊑ Q° ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° := by
      rw [Cat.assoc]
      exact comp_mono_left _ (leftDiv_comp_le _ _)
    have htail : T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ Q° ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° :=
      le_trans t1 (le_trans t2 (le_trans t3 t4))
    -- split `H°` in front and reassociate (backward-rewrite trick, cf. `dp_prefixed`'s `c1`)
    have c1 : H° ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        = (h° ≫ F.map (H°) ≫ T)
            ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R := by
      rw [← hHrec]
    have c2 : (h° ≫ F.map (H°) ≫ T)
          ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        = (h° ≫ F.map (H°))
            ≫ T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R := by
      simp only [Cat.assoc]
    have hbound : (h° ≫ F.map (H°))
          ≫ T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ (h° ≫ F.map (H°)) ≫ Q° ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° :=
      comp_mono_left _ htail
    -- the `hQ` step: conjugate `hQ` to `h°·FH°·Q° ⊑ R°·h°·FH°`
    have hQrec : h° ≫ F.map (H°) ≫ Q° ⊑ R° ≫ h° ≫ F.map (H°) := by
      have hrm := recip_mono hQ
      have eL : (Q ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ Q° := by
        rw [Allegory.recip_comp, Allegory.recip_comp, ← hFr H, Cat.assoc]
      have eR : (F.map H ≫ h ≫ R)° = R° ≫ h° ≫ F.map (H°) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, ← hFr H, Cat.assoc]
      rwa [eL, eR] at hrm
    have hre1 : (h° ≫ F.map (H°)) ≫ Q° ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R°
        = (h° ≫ F.map (H°) ≫ Q°) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° := by
      simp only [Cat.assoc]
    rw [hre1] at hbound
    have step6 : (h° ≫ F.map (H°) ≫ Q°) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R°
        ⊑ (R° ≫ h° ≫ F.map (H°)) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° :=
      comp_mono_right hQrec _
    have hre2 : (R° ≫ h° ≫ F.map (H°)) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R°
        = R° ≫ (h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h) ≫ R° := by
      simp only [Cat.assoc]
    rw [hre2] at step6
    -- collapse: `F(M·H°) ⊆ FR` then conjugated monotonicity and transitivity
    have hinner : h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h ⊑ R° := by
      have hFRM : F.map (H°) ≫ F.map (Λ H ≫ est R) ⊑ F.map R° := by
        rw [← F.map_comp]
        exact F.map_mono hHMR
      have hx : h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h ⊑ h° ≫ F.map R° ≫ h := by
        rw [← Cat.assoc (F.map (H°)) (F.map (Λ H ≫ est R)) h]
        exact comp_mono_left _ (comp_mono_right hFRM h)
      exact le_trans hx ((monotonicAlg_iff_conj hh).mp hmono)
    have step7 : R° ≫ (h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h) ≫ R° ⊑ R° ≫ R° ≫ R° :=
      comp_mono_left R° (comp_mono_right hinner R°)
    have hRRR : R° ≫ R° ≫ R° ⊑ R° := le_trans (comp_mono_left R° htrans) htrans
    have hchain : (h° ≫ F.map (H°) ≫ Q°) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° ⊑ R° :=
      le_trans step6 (le_trans step7 hRRR)
    rw [c1, c2]
    exact le_trans hbound hchain

/-! ### The optimisation chain (note §15.1b)

  `H%∋ est(R) ⊒ (T°)%∋ thin(Q)P(F(X)h)est(R)`: the note draws the spec as the single bead `X`
  sitting inside the body, so the step abstracts that abbreviation out of `dp_thin_prefixed`. -/

/-- Step 1: at `X≜H%∋ est(R)` the thinning body is below the spec — the prefixed point
    Knaster–Tarski consumes, with the note's bead `X` as a binder of its own. -/
public theorem dynamic_programming_thin_step1 (hFr : F.PreservesRecip)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} {H : A ⟶ B}
    {X : A ⟶ B} (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°)
    (hHfix : T° ≫ F.map H ≫ h = H) (hQ : Q ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R)
    (hX : X = Λ H ≫ est R) :
    Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R ⊑ Λ H ≫ est R := by
  subst hX
  exact dp_thin_prefixed hFr hh hmono htrans hHfix hQ

/-- **Theorem 9.2 (B&dM p.221)**, thinning dynamic programming: thinning by a preorder `Q` at
    every unfold step, before minimizing over `R°`, refines minimizing the plain hylomorphism
    recursion — provided `Q` interacts correctly with `H := ⦇h⦈·⦇T⦈°` and `h` (hypothesis
    `hQ`).  Ex 9.1 (`dynamic_programming_of_thin`) recovers Theorem 9.1 as the instance
    `Q := id`. By Knaster–Tarski via `dp_thin_prefixed`. -/
public theorem dynamic_programming_thin (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°)
    (hQ : Q ≫ F.map (H T h) ≫ h
        ⊑ F.map (H T h) ≫ h ≫ R) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _
    (dynamic_programming_thin_step1 hFr hh hmono htrans (hylo_fixed hFr I h T) hQ rfl))

/-! ## Ex 9.1 — Theorem 9.1 as an instance of Theorem 9.2 -/

/-- **Ex 9.1**: Theorem 9.1 (`dynamic_programming`) is the `Q := id` instance of Theorem 9.2
    (`dynamic_programming_thin`) — thinning by the identity preorder never discards a
    candidate (`id ⊑ thin id`, `id_le_thinRel_id`), so the plain recursion refines the
    thinning recursion pointwise; discharging Theorem 9.2's `hQ` hypothesis at `Q := id` needs
    exactly `hrefl : id ⊑ R°`, which the direct proof of Theorem 9.1 does not require. -/
public theorem mu_le_mu_thinRel_id {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} :
    mu (fun X : A ⟶ B => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ mu (fun X : A ⟶ B =>
          Λ (T°) ≫ thinRel (Cat.id (F.obj A)) ≫ powerRel (F.map X ≫ h) ≫ est R) :=
  mu_le_mu fun X => by
    have step := comp_mono_right id_le_thinRel_id (powerRel (F.map X ≫ h) ≫ est R)
    rw [Cat.id_comp] at step
    exact comp_mono_left _ step

/-- At `Q := id`, Theorem 9.2's thinning condition `hQ` says only that `R` is reflexive. -/
public theorem thin_condition_of_refl (I : InitialAlgebra F) {h : F.obj B ⟶ B}
    {T : F.obj A ⟶ A} {R : B ⟶ B} (hrefl : Cat.id B ⊑ R°) :
    Cat.id (F.obj A) ≫ F.map (H T h) ≫ h
      ⊑ F.map (H T h) ≫ h ≫ R := by
  rw [Cat.id_comp]
  have hid : Cat.id B ⊑ R := by
    have h1 := recip_mono hrefl
    rwa [recip_id, Allegory.recip_recip] at h1
  have step := comp_mono_left (F.map (H T h) ≫ h) hid
  rw [Cat.comp_id, Cat.assoc] at step
  exact step

theorem dynamic_programming_of_thin (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°) (hrefl : Cat.id B ⊑ R°) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  le_trans mu_le_mu_thinRel_id
    (dynamic_programming_thin hFr I hh hmono htrans (thin_condition_of_refl I hrefl))

/-! ## Proposition 9.2 (B&dM p.222) — checking monotonicity via cost functions -/

/-- **Proposition 9.2 (B&dM p.222)**: an algebra `h` is monotonic on the order `R := cost·leq·cost°`
    (induced on `a` by pulling the order `leq` on `c` back along a "cost" function) whenever `h`
    followed by `cost` factors as `F.map cost` followed by an algebra `k` that is itself
    monotonic on `leq` — i.e. checking monotonicity of `h` on `R` reduces to checking
    monotonicity of the simpler algebra `k` on `leq`. -/
public theorem monotonicAlg_of_cost {C : 𝒜} {h : F.obj A ⟶ A} {R : A ⟶ A} {cost : A ⟶ C}
    {leq : C ⟶ C} {k : F.obj C ⟶ C} (hcost : Map cost) (hR : R = cost ≫ leq ≫ cost°)
    (hch : h ≫ cost = F.map cost ≫ k) (hk : F.map leq ≫ k ⊑ k ≫ leq) :
    MonotonicAlg h R := by
  show F.map R ≫ h ⊑ h ≫ R
  rw [hR]
  have hassoc : h ≫ cost ≫ leq ≫ cost° = (h ≫ cost ≫ leq) ≫ cost° := by simp only [Cat.assoc]
  rw [hassoc]
  apply (map_shunt_right hcost _ _).mp
  -- goal: (F.map (cost ≫ leq ≫ cost°) ≫ h) ≫ cost ⊑ h ≫ cost ≫ leq
  have eLHS1 : (F.map (cost ≫ leq ≫ cost°) ≫ h) ≫ cost
      = F.map (cost ≫ leq ≫ cost°) ≫ (h ≫ cost) := by rw [Cat.assoc]
  have eLHS2 : F.map (cost ≫ leq ≫ cost°) ≫ (h ≫ cost)
      = F.map (cost ≫ leq ≫ cost°) ≫ (F.map cost ≫ k) := by rw [hch]
  have eLHS3 : F.map (cost ≫ leq ≫ cost°) ≫ (F.map cost ≫ k)
      = (F.map (cost ≫ leq ≫ cost°) ≫ F.map cost) ≫ k := by rw [Cat.assoc]
  have eFold : F.map (cost ≫ leq ≫ cost°) ≫ F.map cost = F.map ((cost ≫ leq ≫ cost°) ≫ cost) := by
    rw [← F.map_comp]
  have eBound : (cost ≫ leq ≫ cost°) ≫ cost ⊑ cost ≫ leq := by
    have e1 : (cost ≫ leq ≫ cost°) ≫ cost = cost ≫ leq ≫ (cost° ≫ cost) := by
      simp only [Cat.assoc]
    rw [e1]
    have e2 : cost ≫ leq ≫ (cost° ≫ cost) ⊑ cost ≫ leq ≫ Cat.id C :=
      comp_mono_left _ (comp_mono_left _ hcost.2)
    rwa [Cat.comp_id] at e2
  have eStep : F.map ((cost ≫ leq ≫ cost°) ≫ cost) ⊑ F.map (cost ≫ leq) := F.map_mono eBound
  have step1 : (F.map (cost ≫ leq ≫ cost°) ≫ F.map cost) ≫ k ⊑ F.map (cost ≫ leq) ≫ k := by
    rw [eFold]; exact comp_mono_right eStep k
  have step2 : F.map (cost ≫ leq) ≫ k = F.map cost ≫ (F.map leq ≫ k) := by
    rw [F.map_comp, Cat.assoc]
  have step3 : F.map cost ≫ (F.map leq ≫ k) ⊑ F.map cost ≫ (k ≫ leq) := comp_mono_left _ hk
  have step4 : F.map cost ≫ (k ≫ leq) = (F.map cost ≫ k) ≫ leq := by rw [Cat.assoc]
  have step5 : (F.map cost ≫ k) ≫ leq = (h ≫ cost) ≫ leq := by rw [← hch]
  have step6 : (h ≫ cost) ≫ leq = h ≫ cost ≫ leq := by rw [Cat.assoc]
  have eLHS : (F.map (cost ≫ leq ≫ cost°) ≫ h) ≫ cost
      = (F.map (cost ≫ leq ≫ cost°) ≫ F.map cost) ≫ k := eLHS1.trans (eLHS2.trans eLHS3)
  rw [eLHS]
  have step1' : (F.map (cost ≫ leq ≫ cost°) ≫ F.map cost) ≫ k
      ⊑ F.map cost ≫ (F.map leq ≫ k) := by rw [← step2]; exact step1
  have step3' : F.map cost ≫ (F.map leq ≫ k) ⊑ h ≫ cost ≫ leq := by
    rw [← step6, ← step5, ← step4]; exact step3
  exact le_trans step1' step3'

/-! ## Ex 9.4 (B&dM p.222) — a universal but useless thinning relation -/

/-- **Ex 9.4**: `Q := F(M·R·M°)` (mirrored `F.map (M ≫ R ≫ M°)`) ALWAYS discharges Theorem
    9.2's `hQ` hypothesis, given only `M ⊑ H` and `H°·M ⊑ R` — i.e. it is a universal choice of
    thinning relation.  Instantiating `M := ΛH·min R` (the optimum being computed) shows the
    hypothesis is always satisfiable in principle, but the resulting `Q` mentions the very
    optimum `dynamic_programming_thin` is trying to compute — useless for actually EXECUTING
    the recursion (only for justifying that some valid `Q` exists). -/
theorem thin_condition_of_optimum (hFr : F.PreservesRecip) {h : F.obj A ⟶ A}
    {R : A ⟶ A} {H M : B ⟶ A} (hh : Map h) (hmono : MonotonicAlg h R) (htrans : R ≫ R ⊑ R)
    (hMH : M ⊑ H) (hHMR : H° ≫ M ⊑ R) :
    (F.map (M ≫ R ≫ M°))° ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R° := by
  have erecip : (M ≫ R ≫ M°)° = M ≫ R° ≫ M° := by
    rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
  have hrecipmap : (F.map (M ≫ R ≫ M°))° = F.map (M ≫ R° ≫ M°) := by
    rw [← hFr (M ≫ R ≫ M°), erecip]
  have hM'H : M° ≫ H ⊑ R° := by
    have h1 := recip_mono hHMR
    have e1 : (H° ≫ M)° = M° ≫ H := by rw [Allegory.recip_comp, Allegory.recip_recip]
    rwa [e1] at h1
  have hRR : R° ≫ R° ⊑ R° := by
    have h1 := recip_mono htrans
    rwa [Allegory.recip_comp] at h1
  have hassocL : (M ≫ R° ≫ M°) ≫ H = M ≫ R° ≫ (M° ≫ H) := by simp only [Cat.assoc]
  have hbound1 : M ≫ R° ≫ (M° ≫ H) ⊑ M ≫ R° ≫ R° :=
    comp_mono_left _ (comp_mono_left _ hM'H)
  have hbound2 : M ≫ R° ≫ R° ⊑ M ≫ R° := comp_mono_left _ hRR
  have hbound3 : M ≫ R° ⊑ H ≫ R° := comp_mono_right hMH R°
  have hMRM'H : (M ≫ R° ≫ M°) ≫ H ⊑ H ≫ R° := by
    rw [hassocL]; exact le_trans hbound1 (le_trans hbound2 hbound3)
  have hfold : F.map (M ≫ R° ≫ M°) ≫ F.map H = F.map ((M ≫ R° ≫ M°) ≫ H) := by
    rw [← F.map_comp]
  have hsplit : F.map (H ≫ R°) ≫ h = F.map H ≫ (F.map R° ≫ h) := by
    rw [F.map_comp, Cat.assoc]
  have hmonoR' : F.map R° ≫ h ⊑ h ≫ R° := (monotonicAlg_recip_iff hh hFr).mp hmono
  rw [hrecipmap]
  have ereassoc : F.map (M ≫ R° ≫ M°) ≫ (F.map H ≫ h) = (F.map (M ≫ R° ≫ M°) ≫ F.map H) ≫ h := by
    rw [Cat.assoc]
  rw [ereassoc, hfold]
  have step1 : F.map ((M ≫ R° ≫ M°) ≫ H) ≫ h ⊑ F.map (H ≫ R°) ≫ h :=
    comp_mono_right (F.map_mono hMRM'H) h
  rw [hsplit] at step1
  exact le_trans step1 (comp_mono_left _ hmonoR')

/-! ## Proposition 9.3 (B&dM p.223) — monotonicity in context

  A different ambient setting from the rest of the file: `TabularUnitaryDivisionAllegory`
  (`AOP.A5_2`), which supplies relational products `RelProd` and pairing.  `S : a ⟶ b`
  plays B&dM's extra "context" relation (his `H°`) — SIMPLE, not necessarily a map — and
  `P : RelProd c b` is the chosen product used to bundle `cost` with `S`. -/

section Prop9_3

variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜] {F : Relator 𝒜 𝒜} {A B : 𝒜}

/-- Proposition 9.3, first step: shunting — `cost` is a map, so `𝟙⊑cost cost°`. -/
public theorem monotonicAlg_in_context_step1 {C : 𝒜} {h : F.obj A ⟶ A} {R : A ⟶ A}
    {cost : A ⟶ C} {S : A ⟶ B} (hcost : Map cost) :
    F.map (R ∩ (S ≫ S°)) ≫ h ⊑ F.map (R ∩ (S ≫ S°)) ≫ h ≫ cost ≫ cost° := by
  simpa only [Cat.comp_id, Cat.assoc] using
    comp_mono_left (F.map (R ∩ (S ≫ S°)) ≫ h) (map_entire_le hcost)

/-- Proposition 9.3, second step: products — `R∩SS° = ⟨cost leq,S⟩⟨cost,S⟩°` by the definition
    of `R` (`pair_recip_pair`). -/
public theorem monotonicAlg_in_context_step2 {C : 𝒜} {h : F.obj A ⟶ A} {R : A ⟶ A}
    {cost : A ⟶ C} {S : A ⟶ B} {P : RelProd C B} {leq : C ⟶ C} (hR : R = cost ≫ leq ≫ cost°) :
    F.map (R ∩ (S ≫ S°)) ≫ h ≫ cost ≫ cost°
      = F.map (P.pair (cost ≫ leq) S ≫ (P.pair cost S)°) ≫ h ≫ cost ≫ cost° := by
  rw [P.pair_recip_pair, hR, Cat.assoc cost leq cost°]

/-- Proposition 9.3, third step: the assumption on `cost`, `h cost = F(⟨cost,S⟩)k`. -/
public theorem monotonicAlg_in_context_step3 {C : 𝒜} {h : F.obj A ⟶ A} {cost : A ⟶ C}
    {S : A ⟶ B} {P : RelProd C B} {k : F.obj P.p ⟶ C} {X : A ⟶ A}
    (hch : h ≫ cost = F.map (P.pair cost S) ≫ k) :
    F.map X ≫ h ≫ cost ≫ cost° = F.map X ≫ F.map (P.pair cost S) ≫ k ≫ cost° := by
  rw [← Cat.assoc h cost, hch]
  simp only [Cat.assoc]

/-- Proposition 9.3, fourth step: `S` simple makes `⟨cost,S⟩` simple
    (`tabulation_simple_of_simple`), so `⟨cost,S⟩°⟨cost,S⟩⊑𝟙`. -/
public theorem monotonicAlg_in_context_step4 {C : 𝒜} {cost : A ⟶ C} {S : A ⟶ B}
    {P : RelProd C B} {leq : C ⟶ C} {k : F.obj P.p ⟶ C} (hcost : Map cost) (hS : Simple S) :
    F.map (P.pair (cost ≫ leq) S ≫ (P.pair cost S)°) ≫ F.map (P.pair cost S) ≫ k ≫ cost°
      ⊑ F.map (P.pair (cost ≫ leq) S) ≫ k ≫ cost° := by
  have hsp : Simple (P.pair cost S) := tabulation_simple_of_simple P.tab hcost.2 hS
  have hs : P.pair (cost ≫ leq) S ≫ (P.pair cost S)° ≫ P.pair cost S ⊑ P.pair (cost ≫ leq) S := by
    simpa only [Cat.comp_id] using comp_mono_left (P.pair (cost ≫ leq) S) hsp
  rw [← Cat.assoc (F.map _) (F.map _) (k ≫ cost°), ← F.map_comp, Cat.assoc]
  exact comp_mono_right (F.map_mono hs) _

/-- Proposition 9.3, fifth step: products; functors — `⟨cost leq,S⟩ = ⟨cost,S⟩(leq×𝟙)`
    (`pair_prodMap_fst`), then `F` preserves the composite. -/
public theorem monotonicAlg_in_context_step5 {C : 𝒜} {cost : A ⟶ C} {S : A ⟶ B}
    {P : RelProd C B} {leq : C ⟶ C} {k : F.obj P.p ⟶ C} :
    F.map (P.pair (cost ≫ leq) S) ≫ k ≫ cost°
      = F.map (P.pair cost S) ≫ F.map (prodMap P P leq (𝟙 B)) ≫ k ≫ cost° := by
  rw [← RelProd.pair_prodMap_fst (P := P) (Q := P) cost S leq, F.map_comp, Cat.assoc]

/-- Proposition 9.3, sixth step: the assumption on `k`, `F(leq×𝟙)k⊑k leq`. -/
public theorem monotonicAlg_in_context_step6 {C : 𝒜} {cost : A ⟶ C} {S : A ⟶ B}
    {P : RelProd C B} {leq : C ⟶ C} {k : F.obj P.p ⟶ C}
    (hk : F.map (prodMap P P leq (𝟙 B)) ≫ k ⊑ k ≫ leq) :
    F.map (P.pair cost S) ≫ F.map (prodMap P P leq (𝟙 B)) ≫ k ≫ cost°
      ⊑ F.map (P.pair cost S) ≫ k ≫ leq ≫ cost° :=
  comp_mono_left _ (by simpa only [Cat.assoc] using comp_mono_right hk cost°)

/-- Proposition 9.3, closing step: the assumption on `cost` read backwards, then the definition
    of `R`. -/
public theorem monotonicAlg_in_context_step7 {C : 𝒜} {h : F.obj A ⟶ A} {R : A ⟶ A}
    {cost : A ⟶ C} {S : A ⟶ B} {P : RelProd C B} {leq : C ⟶ C} {k : F.obj P.p ⟶ C}
    (hR : R = cost ≫ leq ≫ cost°) (hch : h ≫ cost = F.map (P.pair cost S) ≫ k) :
    F.map (P.pair cost S) ≫ k ≫ leq ≫ cost° = h ≫ R := by
  rw [hR, ← Cat.assoc (F.map _) k, ← hch, Cat.assoc]

/-- **Proposition 9.3 (B&dM p.223)**, monotonicity in context: given a cost function `cost`
    bundled with a simple context relation `S` via a chosen product `P`, and an algebra `k`
    (on the bundle) monotonic on `leq × 𝟙` in the sense of `hk`, the algebra `h` is monotonic
    on `R := cost·leq·cost°` RESTRICTED to `S`'s domain of definition (`R ∩ S·S°`).  The book's
    chain, one step theorem per hint. -/
public theorem monotonicAlg_in_context {C : 𝒜} {h : F.obj A ⟶ A} {R : A ⟶ A} {cost : A ⟶ C}
    {S : A ⟶ B} {P : RelProd C B} {leq : C ⟶ C} {k : F.obj P.p ⟶ C}
    (hcost : Map cost) (hS : Simple S) (hR : R = cost ≫ leq ≫ cost°)
    (hch : h ≫ cost = F.map (P.pair cost S) ≫ k)
    (hk : F.map (prodMap P P leq (𝟙 B)) ≫ k ⊑ k ≫ leq) :
    F.map (R ∩ (S ≫ S°)) ≫ h ⊑ h ≫ R :=
  calc F.map (R ∩ (S ≫ S°)) ≫ h
      _ ⊑ F.map (R ∩ (S ≫ S°)) ≫ h ≫ cost ≫ cost° := monotonicAlg_in_context_step1 hcost
      _ = F.map (P.pair (cost ≫ leq) S ≫ (P.pair cost S)°) ≫ h ≫ cost ≫ cost° :=
          monotonicAlg_in_context_step2 hR
      _ = F.map (P.pair (cost ≫ leq) S ≫ (P.pair cost S)°) ≫ F.map (P.pair cost S) ≫ k ≫ cost° :=
          monotonicAlg_in_context_step3 hch
      _ ⊑ F.map (P.pair (cost ≫ leq) S) ≫ k ≫ cost° := monotonicAlg_in_context_step4 hcost hS
      _ = F.map (P.pair cost S) ≫ F.map (prodMap P P leq (𝟙 B)) ≫ k ≫ cost° :=
          monotonicAlg_in_context_step5
      _ ⊑ F.map (P.pair cost S) ≫ k ≫ leq ≫ cost° := monotonicAlg_in_context_step6 hk
      _ = h ≫ R := monotonicAlg_in_context_step7 hR hch

end Prop9_3

/-! ## Proposition 9.4 (B&dM pp.223-224) — bifunctor conditions

  Back in the file's ambient `TabularUnitaryUnguardedPowerLCDA` setting.  B&dM's monotonicity/thinning
  conditions for Theorems 9.1/9.2 are often checked through a BIFUNCTOR `G` (e.g. `G(X,Y) :=
  X × Y` or a coproduct) with the algebra `h` living over `G` applied to a distinguished
  extra argument `e` — Prop 9.4 packages sufficient conditions on `G` alone.  No existing
  `Birelator`/allegory-bifunctor infra elsewhere in the repo (`S1_85`'s bifunctor is for plain
  categories, chapter 1), so the minimal structure is defined here. -/

/-- A **BIRELATOR** (B&dM p.223's implicit bifunctor setting): a relator in each argument
    jointly, bundled as one two-argument action — the minimal bifunctor structure needed to
    state Proposition 9.4. -/
public structure Birelator (𝒜 : Type u) [Allegory 𝒜] where
  obj : 𝒜 → 𝒜 → 𝒜
  map : ∀ {A B C D : 𝒜}, (A ⟶ B) → (C ⟶ D) → (obj A C ⟶ obj B D)
  map_id : ∀ (A C : 𝒜), map (Cat.id A) (Cat.id C) = Cat.id (obj A C)
  map_comp : ∀ {A B C D e f : 𝒜} (R : A ⟶ B) (R' : B ⟶ C) (S : D ⟶ e) (S' : e ⟶ f),
    map (R ≫ R') (S ≫ S') = map R S ≫ map R' S'
  map_mono : ∀ {A B C D : 𝒜} {R R' : A ⟶ B} {S S' : C ⟶ D}, R ⊑ R' → S ⊑ S' → map R S ⊑ map R' S'

/-- A birelator PRESERVES CONVERSE when `G(R°, S°) = (G(R,S))°`. -/
@[expose] public def Birelator.PreservesRecip (G : Birelator 𝒜) : Prop :=
  ∀ {A B C D : 𝒜} (R : A ⟶ B) (S : C ⟶ D), G.map R° S° = (G.map R S)°

/-- "Fix the left argument at `e`": `G.fixLeft e` is the RELATOR `A ↦ G(e, A)`, `R ↦ G(id_e,
    R)` — functoriality follows from `G`'s bifunctoriality with the left slot frozen at the
    identity.  Prop 9.4's point: `MonotonicAlg h R` and Theorem 9.2's `hQ` for `F := G.fixLeft
    e` are EXACTLY (by unfolding `map`) the conclusions of `birelator_fixLeft_mono` /
    `birelator_thin_condition` below, at `Q := G.map U V` — so a monotonicity witness `hU` for
    `G` (plus a reciprocal bound `hV` for the thinning case) suffices to run
    `dynamic_programming`/`dynamic_programming_thin` on `G.fixLeft e`. -/
@[expose] public def Birelator.fixLeft (G : Birelator 𝒜) (e : 𝒜) : Relator 𝒜 𝒜 where
  obj := G.obj e
  map := G.map (Cat.id e)
  map_id A := G.map_id e A
  map_comp R S := by
    have h := G.map_comp (Cat.id e) (Cat.id e) R S
    rwa [Cat.id_comp] at h
  map_mono h := G.map_mono (le_refl (Cat.id e)) h

/-- **Proposition 9.4(i) (B&dM p.223)**, monotonicity: if `h` is monotonic for `G` at some `U`
    refined from below by `id_e` (`hUrefl`), then `h` is monotonic (in the ordinary
    `MonotonicAlg` sense) for the fixed-left relator `G.fixLeft e`. -/
public theorem birelator_fixLeft_mono {G : Birelator 𝒜} {e : 𝒜} {h : G.obj e A ⟶ A} {R : A ⟶ A}
    {U : e ⟶ e} (hUrefl : Cat.id e ⊑ U) (hU : G.map U R ≫ h ⊑ h ≫ R) :
    G.map (Cat.id e) R ≫ h ⊑ h ≫ R :=
  le_trans (comp_mono_right (G.map_mono hUrefl (le_refl R)) h) hU

/-- A map `h` monotonic for `G` at `(U, R)` is monotonic at `(U°, R°)` — conjugate, then
    shunt back across the map `h` (the birelator analogue of `monotonicAlg_recip_iff`). -/
public theorem birelator_mono_recip {G : Birelator 𝒜} (hGr : G.PreservesRecip) {e : 𝒜}
    {h : G.obj e A ⟶ A} {R : A ⟶ A} {U : e ⟶ e} (hh : Map h)
    (hU : G.map U R ≫ h ⊑ h ≫ R) : G.map U° R° ≫ h ⊑ h ≫ R° := by
  have hUrecip : h° ≫ G.map U° R° ⊑ R° ≫ h° := by
    have hrm := recip_mono hU
    have eL : (G.map U R ≫ h)° = h° ≫ G.map U° R° := by
      rw [Allegory.recip_comp, ← hGr U R]
    have eRr : (h ≫ R)° = R° ≫ h° := Allegory.recip_comp h R
    rwa [eL, eRr] at hrm
  have hpost : (h° ≫ G.map U° R°) ≫ h ⊑ (R° ≫ h°) ≫ h := comp_mono_right hUrecip h
  have eLassoc : (h° ≫ G.map U° R°) ≫ h = h° ≫ (G.map U° R° ≫ h) := by rw [Cat.assoc]
  have eRassoc : (R° ≫ h°) ≫ h = R° ≫ (h° ≫ h) := by rw [Cat.assoc]
  rw [eLassoc, eRassoc] at hpost
  have hRRcollapse : R° ≫ (h° ≫ h) ⊑ R° ≫ Cat.id A := comp_mono_left R° hh.2
  rw [Cat.comp_id] at hRRcollapse
  exact (map_shunt_left hh _ _).mp (le_trans hpost hRRcollapse)

/-- Proposition 9.4, first step: taking `Q≜G(U,V)`; bifunctors — `G(U,V)G(𝟙,H) = G(U,VH)`. -/
public theorem birelator_thin_condition_step1 {G : Birelator 𝒜} {e w : 𝒜}
    {h : G.obj e A ⟶ A} {H : w ⟶ A} {U : e ⟶ e} {V : w ⟶ w} :
    G.map U V ≫ G.map (𝟙 e) H ≫ h = G.map U (V ≫ H) ≫ h := by
  rw [← Cat.assoc, ← G.map_comp, Cat.comp_id]

/-- Proposition 9.4, second step: the assumption on `V`, `VH⊑HR`. -/
public theorem birelator_thin_condition_step2 {G : Birelator 𝒜} {e w : 𝒜}
    {h : G.obj e A ⟶ A} {H : w ⟶ A} {R : A ⟶ A} {U : e ⟶ e} {V : w ⟶ w}
    (hV : V ≫ H ⊑ H ≫ R) :
    G.map U (V ≫ H) ≫ h ⊑ G.map U (H ≫ R) ≫ h :=
  comp_mono_right (G.map_mono (le_refl U) hV) h

/-- Proposition 9.4, third step: bifunctors — `G(U,HR) = G(𝟙,H)G(U,R)`. -/
public theorem birelator_thin_condition_step3 {G : Birelator 𝒜} {e w : 𝒜}
    {h : G.obj e A ⟶ A} {H : w ⟶ A} {R : A ⟶ A} {U : e ⟶ e} :
    G.map U (H ≫ R) ≫ h = G.map (𝟙 e) H ≫ G.map U R ≫ h := by
  rw [← Cat.assoc, ← G.map_comp, Cat.id_comp]

/-- Proposition 9.4, fourth step: the assumption on `h`, `G(U,R)h⊑hR`. -/
public theorem birelator_thin_condition_step4 {G : Birelator 𝒜} {e w : 𝒜}
    {h : G.obj e A ⟶ A} {H : w ⟶ A} {R : A ⟶ A} {U : e ⟶ e}
    (hU : G.map U R ≫ h ⊑ h ≫ R) :
    G.map (𝟙 e) H ≫ G.map U R ≫ h ⊑ G.map (𝟙 e) H ≫ h ≫ R :=
  comp_mono_left _ hU

/-- **Proposition 9.4(ii) (B&dM pp.223-224)**, the thinning condition: given the monotonicity
    witness `hU` and the bound `hV : V·H ⊑ H·R` (the note's letters, at the folded `°`), the
    thinning relation `Q := G(U,V)` discharges `dynamic_programming_thin`'s hypothesis `hQ`
    for the fixed-left relator `G.fixLeft e` — the book's chain, one step theorem per hint. -/
public theorem birelator_thin_condition {G : Birelator 𝒜} {e w : 𝒜}
    {h : G.obj e A ⟶ A} {H : w ⟶ A} {R : A ⟶ A} {U : e ⟶ e} {V : w ⟶ w}
    (hU : G.map U R ≫ h ⊑ h ≫ R) (hV : V ≫ H ⊑ H ≫ R) :
    G.map U V ≫ G.map (𝟙 e) H ≫ h ⊑ G.map (𝟙 e) H ≫ h ≫ R :=
  calc G.map U V ≫ G.map (𝟙 e) H ≫ h
      _ = G.map U (V ≫ H) ≫ h := birelator_thin_condition_step1
      _ ⊑ G.map U (H ≫ R) ≫ h := birelator_thin_condition_step2 hV
      _ = G.map (𝟙 e) H ≫ G.map U R ≫ h := birelator_thin_condition_step3
      _ ⊑ G.map (𝟙 e) H ≫ h ≫ R := birelator_thin_condition_step4 hU


/-! ## Ex 9.2 (B&dM p.222) — context-strengthened Theorem 9.2

  A sharper version of `dp_thin_prefixed`: `hmono`/`hQ` need only hold "in context" —
  restricted to `H`'s domain of definition for monotonicity (`R ∩ (H°·H)`), and restricted to
  `T`'s domain of definition for the thinning condition (`Q ∩ (T·T°)`).  The key extra
  ingredient is the sharpened tail bound `T·ΛT°·thin Q ⊆ (Q ∩ T·T°)°·∋` (mirrored below),
  obtained for free from `AOP.A8_1`'s Ex 8.6 context rule for `thin`
  (`Λ_comp_thinRel_context`) at `S := T°` — no modular-law bookkeeping needed. -/

/-- The sharpened tail bound behind Ex 9.2: thinning after unfolding by `T` only ever needs
    `Q` on `T`'s domain of definition, mirrored `T ≫ Λ (T°) ≫ thinRel Q ⊑ (Q ∩ (T ≫ T°))° ≫
    (∋ (F.obj b))°`.  Via `Λ_comp_thinRel_context (T°) Q` (Ex 8.6) plus the plain
    `hTA`/`recip_eps_comp_thinRel_le` chain, now run at `Q ∩ (T ≫ T°)` instead of `Q`. -/
theorem thin_unfold_context_le (T : F.obj A ⟶ A) (Q : F.obj A ⟶ F.obj A) :
    T ≫ Λ (T°) ≫ thinRel Q ⊑ (Q ∩ (T ≫ T°))° ≫ (∋ (F.obj A))° := by
  have hctxEq : Λ (T°) ≫ thinRel (Q ∩ ((T°)° ≫ T°)) = Λ (T°) ≫ thinRel Q :=
    Λ_comp_thinRel_context (T°) Q
  rw [Allegory.recip_recip] at hctxEq
  rw [← hctxEq]
  have hTA : T ≫ Λ (T°) ⊑ (∋ (F.obj A))° := by
    have h0 := recip_comp_Λ_le_recip_eps (T°)
    rwa [Allegory.recip_recip] at h0
  have e1 : T ≫ (Λ (T°) ≫ thinRel (Q ∩ (T ≫ T°)))
      = (T ≫ Λ (T°)) ≫ thinRel (Q ∩ (T ≫ T°)) := by rw [Cat.assoc]
  rw [e1]
  exact le_trans (comp_mono_right hTA _) (recip_eps_comp_thinRel_le (Q ∩ (T ≫ T°)))

/-- **Ex 9.2 (B&dM p.222)**, the context-strengthened core of Theorem 9.2: monotonicity and
    the thinning condition need only hold on the relevant domains of definition
    (`R° ∩ (H°·H)` for monotonicity, `Q ∩ (T·T°)` for thinning). -/
theorem dp_thin_prefixed_context (hFr : F.PreservesRecip) {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} {H : A ⟶ B} (hh : Map h)
    (hctx1 : F.map (R° ∩ (H° ≫ H)) ≫ h ⊑ h ≫ R°) (htrans : R° ≫ R° ⊑ R°)
    (hHfix : T° ≫ F.map H ≫ h = H)
    (hctx2 : (Q ∩ (T ≫ T°)) ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R) :
    Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R ⊑ Λ H ≫ est R := by
  obtain ⟨hMH, hHMR⟩ := le_Λ_comp_est_iff.mp (le_refl (Λ H ≫ est R))
  have h94 := powerRel_comp_est_le (F.map (Λ H ≫ est R) ≫ h) R
  apply le_Λ_comp_est_iff.mpr
  constructor
  · -- (9.2)-with-thin: identical to `dp_thin_prefixed` (does not use monotonicity/thinning)
    have step1 : Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h) :=
      comp_mono_left _ (comp_mono_left _ (le_trans h94 (inter_lb_left _ _)))
    have step2 : Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h)
        ⊑ T° ≫ F.map (Λ H ≫ est R) ≫ h := by
      have e1 : Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj A) ≫ F.map (Λ H ≫ est R) ≫ h)
          = (Λ (T°) ≫ (thinRel Q ≫ ∋ (F.obj A))) ≫ F.map (Λ H ≫ est R) ≫ h := by
        simp only [Cat.assoc]
      rw [e1]
      have e2 : (Λ (T°) ≫ (thinRel Q ≫ ∋ (F.obj A))) ≫ F.map (Λ H ≫ est R) ≫ h
          ⊑ (Λ (T°) ≫ ∋ (F.obj A)) ≫ F.map (Λ H ≫ est R) ≫ h :=
        comp_mono_right (comp_mono_left _ (thinRel_comp_eps_le Q)) _
      have e3 : (Λ (T°) ≫ ∋ (F.obj A)) ≫ F.map (Λ H ≫ est R) ≫ h
          = T° ≫ F.map (Λ H ≫ est R) ≫ h := by rw [Λ_eps_eq']
      rwa [e3] at e2
    have step3 : T° ≫ F.map (Λ H ≫ est R) ≫ h ⊑ T° ≫ F.map H ≫ h :=
      comp_mono_left _ (comp_mono_right (F.map_mono hMH) h)
    rw [hHfix] at step3
    exact le_trans step1 (le_trans step2 step3)
  · -- (9.3)-with-thin, using the sharpened tail bound and the context hypotheses
    have hL := le_trans h94 (inter_lb_right _ _)
    have hHrec : H° = h° ≫ F.map (H°) ≫ T := by
      have h1 : (T° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ T := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H, Cat.assoc]
      rw [← h1, hHfix]
    have hsharp := thin_unfold_context_le T Q
    -- the sharpened tail bound: `Q` replaced by `Q ∩ (T ≫ T°)` throughout
    have t1 : T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ T ≫ Λ (T°) ≫ thinRel Q ≫ (((∋ (F.obj A))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) :=
      comp_mono_left _ (comp_mono_left _ (comp_mono_left _ hL))
    have e1 : T ≫ Λ (T°) ≫ thinRel Q ≫ (((∋ (F.obj A))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))
        = (T ≫ Λ (T°) ≫ thinRel Q) ≫ (((∋ (F.obj A))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) := by simp only [Cat.assoc]
    rw [e1] at t1
    have t2 : (T ≫ Λ (T°) ≫ thinRel Q) ≫ (((∋ (F.obj A))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))
        ⊑ ((Q ∩ (T ≫ T°))° ≫ (∋ (F.obj A))°) ≫ (((∋ (F.obj A))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) :=
      comp_mono_right hsharp _
    have t3 : ((Q ∩ (T ≫ T°))° ≫ (∋ (F.obj A))°) ≫ (((∋ (F.obj A))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))
        ⊑ (Q ∩ (T ≫ T°))° ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° := by
      rw [Cat.assoc]
      exact comp_mono_left _ (leftDiv_comp_le _ _)
    have htail : T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ (Q ∩ (T ≫ T°))° ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° :=
      le_trans t1 (le_trans t2 t3)
    have c1 : H° ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        = (h° ≫ F.map (H°) ≫ T)
            ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R := by
      rw [← hHrec]
    have c2 : (h° ≫ F.map (H°) ≫ T)
          ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        = (h° ≫ F.map (H°))
            ≫ T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R := by
      simp only [Cat.assoc]
    have hbound : (h° ≫ F.map (H°))
          ≫ T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ (h° ≫ F.map (H°)) ≫ (Q ∩ (T ≫ T°))° ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° :=
      comp_mono_left _ htail
    -- the `hctx2` step, mirroring `hQrec` at `Q ∩ (T ≫ T°)`
    have hctx2rec : h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))° ⊑ R° ≫ h° ≫ F.map (H°) := by
      have hrm := recip_mono hctx2
      have eL : ((Q ∩ (T ≫ T°)) ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))° := by
        rw [Allegory.recip_comp, Allegory.recip_comp, ← hFr H, Cat.assoc]
      have eR : (F.map H ≫ h ≫ R)° = R° ≫ h° ≫ F.map (H°) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, ← hFr H, Cat.assoc]
      rwa [eL, eR] at hrm
    have hre1 : (h° ≫ F.map (H°)) ≫ (Q ∩ (T ≫ T°))° ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R°
        = (h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))°) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° := by
      simp only [Cat.assoc]
    rw [hre1] at hbound
    have step6 : (h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))°) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R°
        ⊑ (R° ≫ h° ≫ F.map (H°)) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° :=
      comp_mono_right hctx2rec _
    have hre2 : (R° ≫ h° ≫ F.map (H°)) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R°
        = R° ≫ (h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h) ≫ R° := by
      simp only [Cat.assoc]
    rw [hre2] at step6
    -- the context collapse, from `hctx1` instead of `MonotonicAlg h R°`
    have hHM_ctx : H° ≫ (Λ H ≫ est R) ⊑ R° ∩ (H° ≫ H) :=
      le_inter hHMR (comp_mono_left H° hMH)
    have hFRM_ctx : F.map (H°) ≫ F.map (Λ H ≫ est R) ⊑ F.map (R° ∩ (H° ≫ H)) := by
      rw [← F.map_comp]; exact F.map_mono hHM_ctx
    have hx_ctx : h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h
        ⊑ h° ≫ F.map (R° ∩ (H° ≫ H)) ≫ h := by
      rw [← Cat.assoc (F.map (H°)) (F.map (Λ H ≫ est R)) h]
      exact comp_mono_left _ (comp_mono_right hFRM_ctx h)
    have hshunt : h° ≫ (F.map (R° ∩ (H° ≫ H)) ≫ h) ⊑ h° ≫ (h ≫ R°) := comp_mono_left h° hctx1
    have hcollapse2 : h° ≫ (h ≫ R°) ⊑ R° := by
      have e : h° ≫ (h ≫ R°) = (h° ≫ h) ≫ R° := by rw [Cat.assoc]
      rw [e]
      have e2 := comp_mono_right hh.2 R°
      rwa [Cat.id_comp] at e2
    have hinner_ctx : h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h ⊑ R° :=
      le_trans hx_ctx (le_trans hshunt hcollapse2)
    have step7 : R° ≫ (h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h) ≫ R° ⊑ R° ≫ R° ≫ R° :=
      comp_mono_left R° (comp_mono_right hinner_ctx R°)
    have hRRR : R° ≫ R° ≫ R° ⊑ R° := le_trans (comp_mono_left R° htrans) htrans
    have hchain : (h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))°) ≫ (F.map (Λ H ≫ est R) ≫ h) ≫ R° ⊑ R° :=
      le_trans step6 (le_trans step7 hRRR)
    rw [c1, c2]
    exact le_trans hbound hchain

/-- **Ex 9.2**, packaged as a `dynamic_programming_thin` variant: the context-strengthened
    hypotheses discharge the least-fixed-point refinement exactly as Theorem 9.2 does. -/
public theorem dynamic_programming_thin_context (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} (hh : Map h)
    (hctx1 : F.map (R° ∩ ((H T h)° ≫ H T h)) ≫ h
        ⊑ h ≫ R°)
    (htrans : R° ≫ R° ⊑ R°)
    (hctx2 : (Q ∩ (T ≫ T°)) ≫ F.map (H T h) ≫ h
        ⊑ F.map (H T h) ≫ h ≫ R) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _ (dp_thin_prefixed_context hFr hh hctx1 htrans (hylo_fixed hFr I h T) hctx2))

/-- **Theorem 9.1 in context**: the plain (un-thinned) dynamic-programming recursion refines the
    optimisation spec when `h` is monotonic only ON `H`'s domain of definition, `R° ∩ (H°·H)` —
    the form B&dM's §9.3 optimal-bracketing derivation uses, where only trees with the same
    flattening are ever compared.  Ex 9.2 (`dynamic_programming_thin_context`) at `Q := id`. -/
public theorem dynamic_programming_context (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} (hh : Map h)
    (hctx1 : F.map (R° ∩ ((H T h)° ≫ H T h)) ≫ h
        ⊑ h ≫ R°)
    (htrans : R° ≫ R° ⊑ R°) (hrefl : Cat.id B ⊑ R°) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  le_trans mu_le_mu_thinRel_id
    (dynamic_programming_thin_context hFr I hh hctx1 htrans
      (le_trans (comp_mono_right (inter_lb_left _ _) _) (thin_condition_of_refl I hrefl)))

/-! ## Dropped (B&dM Proposition 9.1, Ex 9.5) — disjoint ranges / coproduct split (pp.219-220)

  Proposition 9.1 (the "disjoint ranges" optimisation: split the search over a coproduct
  `s = a₁ + a₂` via a guard/conditional, thin each branch separately, then `junc` the
  results back together) and Ex 9.5 (its corollary) are DROPPED — not for lack of a proof
  idea, but a genuine SETTING MISMATCH between the two chapters this file straddles:

  * The coproduct/guard/conditional machinery (`junc`, `sumMap`, `guard`, `cond`, `corNeg`)
    lives in `AOP.A5_3`, under `[DistributiveAllegory 𝒜]` (needs Boolean negation `∼` on
    coreflexives, `AOP.A4_5`).
  * All of chapters 6-8 (`est`, `powerRel`, `thinRel`, hylomorphisms, and hence this whole
    file) live under `[TabularUnitaryUnguardedPowerLCDA 𝒜]` (`AOP.A6_2`), the power/division bundle.
  * No section of the repo currently instantiates BOTH classes on the same `𝒜` (no combined
    "distributive + unguarded power" class, and none of the `UnguardedPowerLCDA` model
    instances built elsewhere are known to also satisfy `DistributiveAllegory`). Proposition
    9.1 is not just "reuse an existing lemma under a stronger hypothesis" — its content is
    genuinely *thinning a coproduct-split search*: it needs `thin`/`powerRel`/`est` to
    interact correctly with `junc`/`guard`/`cond`, which is new mathematical work (roughly:
    an Ex-8.x-style fusion law for `thin` against `junc`, analogous to the already-dropped
    §8's (8.4)/Ex 8.7 `powerRel`-vs-`union` fusion, `AOP.A8_1`'s stretch-items note) on top
    of the missing combined typeclass. Building the combined class and the fusion law is a
    multi-file undertaking outside this task's scope; recorded here rather than forced.  What
    IS proved, at the end of this file, is Proposition 9.1 in the Set model over
    `AOP.A6_SnocList`'s `F L E X = L+(X×E)`: there the summand is read off the point, so no
    `guard`/`cond` and no combined class are needed. -/

end Freyd.Alg

/-! # Proposition 9.1 (B&dM p.219) in the Set model — the two arms of `F L E X = L+(X×E)`

  `T=[V₁,V₂] : F(B)⟶B` and `h=[U₁,U₂] : F(A)⟶A` are ANY relations on that functor: `arm₁` and
  `arm₂` name their two halves, so `arm₁ T = V₁`, `arm₂ T = V₂`, and B&dM's disjoint ranges
  `V₂V₁°=⊥` is `hdisj`.  Each body of Theorem 9.2 / Theorem 10.1 then splits into the two
  branches the note's @dp-laws and @greedy-laws draw, and each branch refines the body. -/

namespace Freyd.Alg.RelSet.SL

variable {L W : Type} {b c : RelSet.{0}}

-- `Λ R` in `Rel(Set)` IS the classifier `x↦{y∣R x y}`, by `Λ`'s uniqueness; private because
-- `AOP.A7_4_Horner` already exports the same lemma, on a branch of the import graph this file
-- does not reach.  `est`/`thin`/`P(−)` are read pointwise off their definitions in the proofs.
private theorem Λ_eq_classifier {B C : RelSet.{0}} (R : C ⟶ B) : Λ R = classifier R :=
  (Λ_unique R (classifier R) (graph_map _) (classifier_comp_eps R)).symm

/-- The `L` arm `V₁` of a relation out of `F L W`. -/
@[expose] public def arm₁ (T : (F L W).obj b ⟶ c) : dL L ⟶ c := fun d y => T (Sum.inl d) y

/-- The `X×W` arm `V₂` of a relation out of `F L W`. -/
@[expose] public def arm₂ (T : (F L W).obj b ⟶ c) : (⟨b.carrier × W⟩ : RelSet.{0}) ⟶ c :=
  fun p y => T (Sum.inr p) y

/-- **`α = [nil,snoc]`** — the initial algebra as the JUNCTION the note writes, at the one label
    where `wrap` carries nothing.  Every §9–§10 row whose tape is `[nil,(X×𝟙)snoc]` is this
    equation and then the relator sliding into the bracket. -/
public theorem con_eq_junc : graph (con (L := Unit) (E := W)) = junc (sumCop _ _) nilR snocR := by
  apply hom_ext; intro u r
  constructor
  · intro h
    cases u with
    | inl d => exact Or.inl ⟨d, rfl, h⟩
    | inr p => exact Or.inr ⟨p, rfl, h⟩
  · intro h
    cases h with
    | inl h => obtain ⟨d, h1, h2⟩ := h; subst h1; exact h2
    | inr h => obtain ⟨p, h1, h2⟩ := h; subst h1; exact h2

/-- The `L` arm `Q₁` of a preorder on `F L W X`. -/
@[expose] public def armQ₁ (Q : (F L W).obj b ⟶ (F L W).obj b) : dL L ⟶ dL L :=
  fun d d' => Q (Sum.inl d) (Sum.inl d')

/-- The `X×W` arm `Q₂` of a preorder on `F L W X`. -/
@[expose] public def armQ₂ (Q : (F L W).obj b ⟶ (F L W).obj b) :
    (⟨b.carrier × W⟩ : RelSet.{0}) ⟶ ⟨b.carrier × W⟩ := fun p q => Q (Sum.inr p) (Sum.inr q)

/-- The second arm of the constructor algebra is `snoc` — what `[nil,snoc]` does on its `X×W`
    summand.  The note writes the arm by that name, never as the algebra restricted. -/
public theorem arm₂_con : arm₂ (graph (con (L := L) (E := W))) = snocR := rfl

/-- THE ARM OF A MAP IS A MAP — `arm₂` of a graph is the graph of the function restricted to the
    summand — so the note's name for the arm is read off that function, exactly as every other
    map's is; `arm₂_con` is this equation at `con`, where the restriction leaves `snoc`. -/
public theorem arm₂_graph (f : ((F L W).obj b).carrier → c.carrier) :
    arm₂ (graph f) = graph (fun p => f (Sum.inr p)) := rfl

/-- The second arm of `F(X)·h` is the note's `(X×𝟙)U₂`: `F(X)` keeps the `W` component. -/
public theorem arm₂_comp {d : RelSet.{0}} (X : b ⟶ c) (U : (F L W).obj c ⟶ d) :
    arm₂ ((F L W).map X ≫ U) = rprodMap X (𝟙 (⟨W⟩ : RelSet.{0})) ≫ arm₂ U := by
  apply hom_ext; intro p y
  constructor
  · rintro ⟨w, hw, hU⟩
    cases w with
    | inl _ => exact hw.elim
    | inr q => exact ⟨q, ⟨hw.1, hw.2⟩, hU⟩
  · rintro ⟨q, hq, hU⟩
    exact ⟨Sum.inr q, ⟨hq.1, hq.2⟩, hU⟩

/-- **`F(X)[T,U] = [T,(X×𝟙)U]`** — the relator slides into the bracket: the leaf arm is untouched,
    the pair arm picks up `X×𝟙` in front.  `arm₁_comp` and `arm₂_comp` are its two arms, and every
    §9–§10 row whose tape is `[nil,(X×𝟙)snoc]` is this step. -/
public theorem Fmap_comp_junc {d : RelSet.{0}} (X : b ⟶ c) (T : dL L ⟶ d)
    (U : (⟨c.carrier × W⟩ : RelSet.{0}) ⟶ d) :
    (F L W).map X ≫ junc (sumCop (dL L) ⟨c.carrier × W⟩) T U
      = junc (sumCop (dL L) ⟨b.carrier × W⟩) T (rprodMap X (𝟙 (⟨W⟩ : RelSet.{0})) ≫ U) := by
  apply hom_ext; intro u y
  cases u with
  | inl d' =>
    rw [ListRel.junc_sum_inl]
    constructor
    · rintro ⟨w, hw, hj⟩
      cases w with
      | inl e' => obtain rfl : d' = e' := hw; exact (ListRel.junc_sum_inl T U d' y).mp hj
      | inr q => exact hw.elim
    · intro hT; exact ⟨Sum.inl d', rfl, (ListRel.junc_sum_inl T U d' y).mpr hT⟩
  | inr p =>
    rw [ListRel.junc_sum_inr]
    constructor
    · rintro ⟨w, hw, hj⟩
      cases w with
      | inl e' => exact hw.elim
      | inr q => exact ⟨q, ⟨hw.1, hw.2⟩, (ListRel.junc_sum_inr T U q y).mp hj⟩
    · rintro ⟨q, hq, hU⟩
      exact ⟨Sum.inr q, ⟨hq.1, hq.2⟩, (ListRel.junc_sum_inr T U q y).mpr hU⟩

/-- The first arm of `F(X)·h` is `U₁` alone: `F(X)` is the identity on the `L` summand. -/
public theorem arm₁_comp {d : RelSet.{0}} (X : b ⟶ c) (U : (F L W).obj c ⟶ d) :
    arm₁ ((F L W).map X ≫ U) = arm₁ U := by
  apply hom_ext; intro e y
  constructor
  · rintro ⟨w, hw, hU⟩
    cases w with
    | inl d' => exact (hw : e = d') ▸ hU
    | inr _ => exact hw.elim
  · intro hU
    exact ⟨Sum.inl e, rfl, hU⟩

/-! ## The transpose of a coalgebra sits inside one summand

  `Λ(T°)` at a point of `V₂`'s range is the `inr`-image of `Λ(V₂°)` there — `hdisj` says the
  `inl` part is empty — and everything downstream of `est`/`thin` kills the empty set.  That is
  the whole content of Proposition 9.1; the four theorems below are it at the four shapes the
  note draws. -/

/-! ### Proposition 9.1 AT AN ARBITRARY SUMMAND

  The law is about ONE summand of the algebra, not about the snoc list: `Fᵢ` is any relator sitting
  inside `F` along an injection `ι`, `Vᵢ` and `Uᵢ` are `T` and `h` restricted to it, and `Qᵢ` is `Q`
  there.  `hdisj` is the whole content — at a point `Vᵢ` reaches, `T` reaches it only through that
  summand — and it is what lets the `est`/`thin` over the summand answer for the `est`/`thin` over
  everything.  The two shapes below are the note's @greedy-laws and @dp-laws third rows; the snoc
  arms are them at `Fᵢ = −×W`, `ι = Sum.inr`, where `hV`, `hQ` and `harm` hold by the coproduct's
  own `arm₂`/`arm₂_comp`.

  `Map Uᵢ` is not used by either proof: it is the fact the PICTURE draws, the summand's algebra
  being a map is what makes its box a rectangle and not a chamfered relation. -/

-- The relator binders are INLINE and not `variable`s: this section's `F` is the whole algebra's,
-- where the file's own `F L W` is the snoc list's, and a `variable F` would shadow it below.
-- The NAMES are `_root_`'s: nothing here is the snoc list's, and a general law under `SL` is what
-- gets cloned at the next functor.  The proofs sit inside the namespace for its `Λ_eq_classifier`.

/-- **Proposition 9.1 at one summand**, greedy form: the note's @greedy-laws third row
    `(Vᵢ°)%∋ est(Qᵢ)Fᵢ(X)Uᵢ` refines the body `(T°)%∋ est(Q)F(X)h`. -/
public theorem _root_.Freyd.Alg.RelSet.est_summand_le {A B : RelSet.{0}} {Fᵢ F : Relator RelSet.{0} RelSet.{0}}
    {T : F.obj A ⟶ A} {Q : F.obj A ⟶ F.obj A} {X : A ⟶ B}
    {h : F.obj B ⟶ B} {Vᵢ : Fᵢ.obj A ⟶ A} {Qᵢ : Fᵢ.obj A ⟶ Fᵢ.obj A} {Uᵢ : Fᵢ.obj B ⟶ B}
    (ι : (Fᵢ.obj A).carrier → (F.obj A).carrier) (_hUᵢ : Map Uᵢ)
    (hV : ∀ p y, Vᵢ p y ↔ T (ι p) y)
    (hQ : ∀ p p', Qᵢ p p' → Q (ι p) (ι p'))
    (harm : ∀ p z, (Fᵢ.map X ≫ Uᵢ) p z ↔ (F.map X ≫ h) (ι p) z)
    (hdisj : ∀ w p y, Vᵢ p y → T w y → ∃ p', w = ι p') :
    Λ (Vᵢ°) ≫ est Qᵢ ≫ Fᵢ.map X ≫ Uᵢ ⊑ Λ (T°) ≫ est Q ≫ F.map X ≫ h := by
  rw [le_iff]
  rintro y a ⟨S, hS, p, hp, hW⟩
  rw [Λ_eq_classifier] at hS
  subst hS
  refine ⟨fun w => T w y, ?_, ι p, ⟨(hV p y).mp hp.1, ?_⟩, (harm p a).mp hW⟩
  · rw [Λ_eq_classifier]; rfl
  · intro w hw
    obtain ⟨p', rfl⟩ := hdisj w p y hp.1 hw
    exact hQ p p' (hp.2 p' ((hV p' y).mpr hw))

/-- **Proposition 9.1 at one summand**, thinning form: the note's @dp-laws third row
    `(Vᵢ°)%∋ thin(Qᵢ)P(Fᵢ(X)Uᵢ)est(R)` refines `(T°)%∋ thin(Q)P(F(X)h)est(R)`. -/
public theorem _root_.Freyd.Alg.RelSet.thin_summand_le {A B : RelSet.{0}} {Fᵢ F : Relator RelSet.{0} RelSet.{0}}
    {T : F.obj A ⟶ A} {Q : F.obj A ⟶ F.obj A} {X : A ⟶ B}
    {h : F.obj B ⟶ B} {R : B ⟶ B} {Vᵢ : Fᵢ.obj A ⟶ A} {Qᵢ : Fᵢ.obj A ⟶ Fᵢ.obj A}
    {Uᵢ : Fᵢ.obj B ⟶ B}
    (ι : (Fᵢ.obj A).carrier → (F.obj A).carrier) (_hUᵢ : Map Uᵢ)
    (hV : ∀ p y, Vᵢ p y ↔ T (ι p) y)
    (hQ : ∀ p p', Qᵢ p p' → Q (ι p) (ι p'))
    (harm : ∀ p z, (Fᵢ.map X ≫ Uᵢ) p z ↔ (F.map X ≫ h) (ι p) z)
    (hdisj : ∀ w p y, Vᵢ p y → T w y → ∃ p', w = ι p') :
    Λ (Vᵢ°) ≫ thinRel Qᵢ ≫ powerRel (Fᵢ.map X ≫ Uᵢ) ≫ est R
      ⊑ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R := by
  rw [le_iff]
  rintro y a ⟨S, hS, Y, hY, Z, hZ, hest⟩
  rw [Λ_eq_classifier] at hS
  subst hS
  refine ⟨fun w => T w y, ?_, fun w => ∃ q, Y q ∧ w = ι q, ?_, Z, ?_, hest⟩
  · rw [Λ_eq_classifier]; rfl
  · refine ⟨?_, ?_⟩
    · rintro w ⟨q, hq, rfl⟩
      exact (hV q y).mp (hY.1 q hq)
    · intro w hw
      obtain ⟨t, ht, _⟩ := hZ.2 a hest.1
      obtain ⟨q, rfl⟩ := hdisj w t y (hY.1 t ht) hw
      obtain ⟨w', hQw, hw'Y⟩ := hY.2 q ((hV q y).mpr hw)
      exact ⟨ι w', hQ w' q hQw, w', hw'Y, rfl⟩
  · refine ⟨?_, ?_⟩
    · rintro w ⟨q, hq, rfl⟩
      obtain ⟨u, hu, hZu⟩ := hZ.1 q hq
      exact ⟨u, (harm q u).mp hu, hZu⟩
    · intro u hu
      obtain ⟨t, ht, hgt⟩ := hZ.2 u hu
      exact ⟨ι t, ⟨t, ht, rfl⟩, (harm t u).mp hgt⟩

/-- THINNING UNDER THE IDENTITY ORDER DISCARDS NOTHING: `thin(𝟙)` relates a set only to itself,
    since one half of it makes the answer a subset and the other puts every element back.  That is
    what lets the thinning-free law below BE the thinning one at `Q ≜ 𝟙` rather than a second proof
    of the same disjointness argument. -/
public theorem _root_.Freyd.Alg.RelSet.thinRel_id {A : RelSet.{0}} :
    thinRel (𝟙 A) = 𝟙 (PowerAllegory.powerObj A) := by
  apply hom_ext
  intro S Y
  constructor
  · rintro ⟨h1, h2⟩
    have : S = Y := by
      funext w
      refine propext ⟨fun hs => ?_, fun hy => h1 w hy⟩
      obtain ⟨w', hw', hY'⟩ := h2 w hs
      exact hw' ▸ hY'
    exact this
  · intro hSY
    obtain rfl : S = Y := hSY
    exact ⟨fun _ hw => hw, fun z hz => ⟨z, rfl, hz⟩⟩

/-- **Proposition 9.1 at one summand**, thinning-free form: the note's @mct-laws third row
    `(Vᵢ°)%∋ P(Fᵢ(X)Uᵢ)est(R)` refines `(T°)%∋ P(F(X)h)est(R)`.  A problem whose decompositions are
    never preferable to one another has no thinning step, and `thin(𝟙)` is exactly that step doing
    nothing, so this is `thin_summand_le` at `Qᵢ ≜ 𝟙`, `Q ≜ 𝟙` — the disjointness argument is
    written once. -/
public theorem _root_.Freyd.Alg.RelSet.pow_summand_le {A B : RelSet.{0}}
    {Fᵢ F : Relator RelSet.{0} RelSet.{0}}
    {T : F.obj A ⟶ A} {X : A ⟶ B} {h : F.obj B ⟶ B} {R : B ⟶ B}
    {Vᵢ : Fᵢ.obj A ⟶ A} {Uᵢ : Fᵢ.obj B ⟶ B}
    (ι : (Fᵢ.obj A).carrier → (F.obj A).carrier) (hUᵢ : Map Uᵢ)
    (hV : ∀ p y, Vᵢ p y ↔ T (ι p) y)
    (harm : ∀ p z, (Fᵢ.map X ≫ Uᵢ) p z ↔ (F.map X ≫ h) (ι p) z)
    (hdisj : ∀ w p y, Vᵢ p y → T w y → ∃ p', w = ι p') :
    Λ (Vᵢ°) ≫ powerRel (Fᵢ.map X ≫ Uᵢ) ≫ est R
      ⊑ Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R := by
  have key := RelSet.thin_summand_le (Qᵢ := 𝟙 (Fᵢ.obj A)) (Q := 𝟙 (F.obj A)) (R := R) ι hUᵢ hV
    (fun p p' hp => congrArg ι hp) harm hdisj
  rwa [RelSet.thinRel_id, RelSet.thinRel_id, Cat.id_comp, Cat.id_comp] at key

/-- **Proposition 9.1**, greedy form, second arm: the note's @greedy-laws third row
    `(V₂°)%∋ est(Q₂)(X×𝟙)U₂` refines the body `(T°)%∋ est(Q)F(X)h`. -/
public theorem est_arm₂_le {T : (F L W).obj b ⟶ b} {Q : (F L W).obj b ⟶ (F L W).obj b}
    {X : b ⟶ c} {U : (F L W).obj c ⟶ c}
    (hdisj : ∀ (d : L) (p : b.carrier × W) (y : b.carrier),
      T (Sum.inl d) y → T (Sum.inr p) y → False) :
    Λ ((arm₂ T)°) ≫ est (armQ₂ Q) ≫ rprodMap X (𝟙 (⟨W⟩ : RelSet.{0})) ≫ arm₂ U
      ⊑ Λ (T°) ≫ est Q ≫ (F L W).map X ≫ U := by
  rw [le_iff]
  rintro y a ⟨S, hS, p, hp, q, hq, hU⟩
  rw [Λ_eq_classifier] at hS
  subst hS
  refine ⟨fun w => T w y, ?_, Sum.inr p, ?_, Sum.inr q, ⟨hq.1, hq.2⟩, hU⟩
  · rw [Λ_eq_classifier]; rfl
  · refine ⟨hp.1, ?_⟩
    rintro (d | z) hz
    · exact (hdisj d p y hz hp.1).elim
    · exact hp.2 z hz

/-- **Proposition 9.1**, greedy form, first arm: the `L` branch of the same body. -/
public theorem est_arm₁_le {T : (F L W).obj b ⟶ b} {Q : (F L W).obj b ⟶ (F L W).obj b}
    {X : b ⟶ c} {U : (F L W).obj c ⟶ c}
    (hdisj : ∀ (d : L) (p : b.carrier × W) (y : b.carrier),
      T (Sum.inl d) y → T (Sum.inr p) y → False) :
    Λ ((arm₁ T)°) ≫ est (armQ₁ Q) ≫ arm₁ U ⊑ Λ (T°) ≫ est Q ≫ (F L W).map X ≫ U := by
  rw [le_iff]
  rintro y a ⟨S, hS, d, hd, hU⟩
  rw [Λ_eq_classifier] at hS
  subst hS
  refine ⟨fun w => T w y, ?_, Sum.inl d, ?_, Sum.inl d, rfl, hU⟩
  · rw [Λ_eq_classifier]; rfl
  · refine ⟨hd.1, ?_⟩
    rintro (e | z) hz
    · exact hd.2 e hz
    · exact (hdisj d z y hd.1 hz).elim

/-- **Proposition 9.1**, thinning form, second arm: the note's @dp-laws third row
    `(V₂°)%∋ thin(Q₂)P((X×𝟙)U₂)est(R)` refines `(T°)%∋ thin(Q)P(F(X)h)est(R)`. -/
public theorem thin_arm₂_le {T : (F L W).obj b ⟶ b} {Q : (F L W).obj b ⟶ (F L W).obj b}
    {X : b ⟶ c} {U : (F L W).obj c ⟶ c} {R : c ⟶ c}
    (hdisj : ∀ (d : L) (p : b.carrier × W) (y : b.carrier),
      T (Sum.inl d) y → T (Sum.inr p) y → False) :
    Λ ((arm₂ T)°) ≫ thinRel (armQ₂ Q) ≫ powerRel (rprodMap X (𝟙 (⟨W⟩ : RelSet.{0})) ≫ arm₂ U) ≫ est R
      ⊑ Λ (T°) ≫ thinRel Q ≫ powerRel ((F L W).map X ≫ U) ≫ est R := by
  rw [le_iff]
  rintro y a ⟨S, hS, Y, hY, Z, hZ, hest⟩
  rw [Λ_eq_classifier] at hS
  subst hS
  refine ⟨fun w => T w y, ?_, fun w => ∃ q, Y q ∧ w = Sum.inr q, ?_, Z, ?_, hest⟩
  · rw [Λ_eq_classifier]; rfl
  · refine ⟨?_, ?_⟩
    · rintro w ⟨q, hq, rfl⟩
      exact hY.1 q hq
    · rintro (d | z) hz
      · obtain ⟨t, ht, _⟩ := hZ.2 a hest.1
        exact (hdisj d t y hz (hY.1 t ht)).elim
      · obtain ⟨w, hw, hwY⟩ := hY.2 z hz
        exact ⟨Sum.inr w, hw, w, hwY, rfl⟩
  · refine ⟨?_, ?_⟩
    · rintro w ⟨q, hq, rfl⟩
      obtain ⟨u, hu, hZu⟩ := hZ.1 q hq
      exact ⟨u, (arm₂_comp X U ▸ hu : arm₂ ((F L W).map X ≫ U) q u), hZu⟩
    · intro u hu
      obtain ⟨t, ht, hgt⟩ := hZ.2 u hu
      exact ⟨Sum.inr t, ⟨t, ht, rfl⟩, (arm₂_comp X U ▸ hgt : arm₂ ((F L W).map X ≫ U) t u)⟩

/-- **Proposition 9.1**, thinning form, first arm: the `L` branch of the same body. -/
public theorem thin_arm₁_le {T : (F L W).obj b ⟶ b} {Q : (F L W).obj b ⟶ (F L W).obj b}
    {X : b ⟶ c} {U : (F L W).obj c ⟶ c} {R : c ⟶ c}
    (hdisj : ∀ (d : L) (p : b.carrier × W) (y : b.carrier),
      T (Sum.inl d) y → T (Sum.inr p) y → False) :
    Λ ((arm₁ T)°) ≫ thinRel (armQ₁ Q) ≫ powerRel (arm₁ U) ≫ est R
      ⊑ Λ (T°) ≫ thinRel Q ≫ powerRel ((F L W).map X ≫ U) ≫ est R := by
  rw [le_iff]
  rintro y a ⟨S, hS, Y, hY, Z, hZ, hest⟩
  rw [Λ_eq_classifier] at hS
  subst hS
  refine ⟨fun w => T w y, ?_, fun w => ∃ d, Y d ∧ w = Sum.inl d, ?_, Z, ?_, hest⟩
  · rw [Λ_eq_classifier]; rfl
  · refine ⟨?_, ?_⟩
    · rintro w ⟨d, hd, rfl⟩
      exact hY.1 d hd
    · rintro (e | z) hz
      · obtain ⟨w, hw, hwY⟩ := hY.2 e hz
        exact ⟨Sum.inl w, hw, w, hwY, rfl⟩
      · obtain ⟨t, ht, _⟩ := hZ.2 a hest.1
        exact (hdisj t z y (hY.1 t ht) hz).elim
  · refine ⟨?_, ?_⟩
    · rintro w ⟨d, hd, rfl⟩
      obtain ⟨u, hu, hZu⟩ := hZ.1 d hd
      exact ⟨u, (arm₁_comp X U ▸ hu : arm₁ ((F L W).map X ≫ U) d u), hZu⟩
    · intro u hu
      obtain ⟨t, ht, hgt⟩ := hZ.2 u hu
      exact ⟨Sum.inl t, ⟨t, ht, rfl⟩, (arm₁_comp X U ▸ hgt : arm₁ ((F L W).map X ≫ U) t u)⟩

/-- **Theorem 9.2 in coproduct form** — the note's @dp-laws, third row: at `T=[V₁,V₂]`,
    `h=[U₁,U₂]`, `Q=Q₁+Q₂` and `V₂V₁°=⊥`, the recursion that runs the two branches separately
    still refines the optimisation spec.  `AOP.A9_1.dynamic_programming_thin` at the snoc-list
    functor, with the body replaced by the union of the two arms `thin_arm₁_le`/`thin_arm₂_le`
    draw. -/
public theorem dynamic_programming_thin_arms {T : (F L W).obj b ⟶ b}
    {Q : (F L W).obj b ⟶ (F L W).obj b} {U : (F L W).obj c ⟶ c} {R : c ⟶ c}
    (hh : Map U) (hmono : MonotonicAlg U R°) (htrans : R° ≫ R° ⊑ R°)
    (hdisj : ∀ (d : L) (p : b.carrier × W) (y : b.carrier),
      T (Sum.inl d) y → T (Sum.inr p) y → False)
    (hQ : Q ≫ (F L W).map ((relCata T)° ≫ relCata U) ≫ U
        ⊑ (F L W).map ((relCata T)° ≫ relCata U) ≫ U ≫ R) :
    mu (fun X : b ⟶ c =>
        (Λ ((arm₁ T)°) ≫ thinRel (armQ₁ Q) ≫ powerRel (arm₁ U) ≫ est R)
          ∪ (Λ ((arm₂ T)°) ≫ thinRel (armQ₂ Q)
              ≫ powerRel (rprodMap X (𝟙 (⟨W⟩ : RelSet.{0})) ≫ arm₂ U) ≫ est R))
      ⊑ Λ ((relCata T)° ≫ relCata U) ≫ est R :=
  le_trans (mu_le_mu fun X => union_lub (thin_arm₁_le (X := X) hdisj) (thin_arm₂_le hdisj))
    (dynamic_programming_thin (F := F L W) (F_preservesRecip L W) (initial L W) hh hmono htrans hQ)

end Freyd.Alg.RelSet.SL
