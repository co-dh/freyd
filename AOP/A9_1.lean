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

  Setting: `UnguardedPowerLCDA` (`AOP.A6_2`), continuing chapters 7 and 8.
-/
module

public import AOP.A7_2
public import AOP.A8_1
public import AOP.A5_2

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-! ## Theorem 9.1 (B&dM pp. 220-221) -/

/-- **Core of Theorem 9.1**: `M = min R°·ΛH` (mirrored `Λ H ≫ est R`) is a PREFIXED point of
    the dynamic-programming body, for ANY `H` satisfying the hylomorphism fixed-point equation
    `H = h·FH·T°` (mirrored `T° ≫ F.map H ≫ h = H`) — Theorems 9.1/9.2 and the exercise
    variants all instantiate `H := ⦇h⦈·⦇T⦈°`.  The two inclusions (9.2) and (9.3) of the book's
    proof are exactly the components of `min`'s universal property (`le_Λ_comp_est_iff`). -/
public theorem dp_prefixed (hFr : F.PreservesRecip) {h : F.obj a ⟶ a} {T : F.obj b ⟶ b}
    {R : a ⟶ a} {H : b ⟶ a} (hh : Map h) (hmono : MonotonicAlg h R°)
    (htrans : R° ≫ R° ⊑ R°) (hHfix : T° ≫ F.map H ≫ h = H) :
    Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R ⊑ Λ H ≫ est R := by
  -- the two min-UP components of `M ⊑ min R°·ΛH`: `M ⊑ H` and `M·H° ⊑ R°` (mirrored)
  obtain ⟨hMH, hHMR⟩ := le_Λ_comp_est_iff.mp (le_refl (Λ H ≫ est R))
  -- rule (9.4) at `X := h·FM`
  have h94 := powerRel_comp_est_le (F.map (Λ H ≫ est R) ≫ h) R
  apply le_Λ_comp_est_iff.mpr
  constructor
  · -- (9.2): `min R°·P(h·FM)·ΛT° ⊆ H`
    have s1 : Λ (T°) ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ Λ (T°) ≫ ∋ (F.obj b) ≫ F.map (Λ H ≫ est R) ≫ h :=
      comp_mono_left _ (le_trans h94 (inter_lb_left _ _))
    -- Λ cancellation: `∈·ΛT° = T°`
    have s2 : Λ (T°) ≫ ∋ (F.obj b) ≫ F.map (Λ H ≫ est R) ≫ h
        = T° ≫ F.map (Λ H ≫ est R) ≫ h := by
      rw [← Cat.assoc (Λ (T°)) (∋ (F.obj b)) _, Λ_eps_eq']
    -- `M ⊑ H`, then the fixed-point equation
    have s3 : T° ≫ F.map (Λ H ≫ est R) ≫ h ⊑ T° ≫ F.map H ≫ h :=
      comp_mono_left _ (comp_mono_right (F.map_mono hMH) h)
    rw [s2] at s1
    rw [hHfix] at s3
    exact le_trans s1 s3
  · -- (9.3): `min R°·P(h·FM)·ΛT°·H° ⊆ R°`
    -- the lower-bound component of (9.4)
    have hL : powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ (((∋ (F.obj b))°) \ ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) :=
      le_trans h94 (inter_lb_right _ _)
    -- `ΛT°·T ⊆ ∋` mirrored
    have hTA : T ≫ Λ (T°) ⊑ (∋ (F.obj b))° := by
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
          ⊑ T ≫ Λ (T°) ≫ (((∋ (F.obj b))°) \ ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) :=
        comp_mono_left _ (comp_mono_left _ hL)
      have t2 : T ≫ Λ (T°) ≫ (((∋ (F.obj b))°) \ ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))
          ⊑ (∋ (F.obj b))° ≫ (((∋ (F.obj b))°) \ ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) := by
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
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ ((relCata T)° ≫ relCata h) ≫ est R :=
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
theorem dp_thin_prefixed (hFr : F.PreservesRecip) {h : F.obj a ⟶ a} {T : F.obj b ⟶ b}
    {R : a ⟶ a} {Q : F.obj b ⟶ F.obj b} {H : b ⟶ a} (hh : Map h) (hmono : MonotonicAlg h R°)
    (htrans : R° ≫ R° ⊑ R°) (hHfix : T° ≫ F.map H ≫ h = H)
    (hQ : Q ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R) :
    Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R ⊑ Λ H ≫ est R := by
  obtain ⟨hMH, hHMR⟩ := le_Λ_comp_est_iff.mp (le_refl (Λ H ≫ est R))
  have h94 := powerRel_comp_est_le (F.map (Λ H ≫ est R) ≫ h) R
  apply le_Λ_comp_est_iff.mpr
  constructor
  · -- (9.2)-with-thin: `min R°·P(h·FM)·thin Q·ΛT° ⊆ H`
    have step1 : Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj b) ≫ F.map (Λ H ≫ est R) ≫ h) :=
      comp_mono_left _ (comp_mono_left _ (le_trans h94 (inter_lb_left _ _)))
    have step2 : Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj b) ≫ F.map (Λ H ≫ est R) ≫ h)
        ⊑ T° ≫ F.map (Λ H ≫ est R) ≫ h := by
      have e1 : Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj b) ≫ F.map (Λ H ≫ est R) ≫ h)
          = (Λ (T°) ≫ (thinRel Q ≫ ∋ (F.obj b))) ≫ F.map (Λ H ≫ est R) ≫ h := by
        simp only [Cat.assoc]
      rw [e1]
      have e2 : (Λ (T°) ≫ (thinRel Q ≫ ∋ (F.obj b))) ≫ F.map (Λ H ≫ est R) ≫ h
          ⊑ (Λ (T°) ≫ ∋ (F.obj b)) ≫ F.map (Λ H ≫ est R) ≫ h :=
        comp_mono_right (comp_mono_left _ (thinRel_comp_eps_le Q)) _
      have e3 : (Λ (T°) ≫ ∋ (F.obj b)) ≫ F.map (Λ H ≫ est R) ≫ h
          = T° ≫ F.map (Λ H ≫ est R) ≫ h := by rw [Λ_eps_eq']
      rwa [e3] at e2
    have step3 : T° ≫ F.map (Λ H ≫ est R) ≫ h ⊑ T° ≫ F.map H ≫ h :=
      comp_mono_left _ (comp_mono_right (F.map_mono hMH) h)
    rw [hHfix] at step3
    exact le_trans step1 (le_trans step2 step3)
  · -- (9.3)-with-thin: `H°·min R°·P(h·FM)·thin Q·ΛT° ⊆ R°`
    have hL := le_trans h94 (inter_lb_right _ _)
    have hTA : T ≫ Λ (T°) ⊑ (∋ (F.obj b))° := by
      have h0 := recip_comp_Λ_le_recip_eps (T°)
      rwa [Allegory.recip_recip] at h0
    have hHrec : H° = h° ≫ F.map (H°) ≫ T := by
      have h1 : (T° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ T := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H, Cat.assoc]
      rw [← h1, hHfix]
    -- the tail bound: peel `T·ΛT°` down to `∋°`, then `thin Q` down to `Q°·∋°`
    have t1 : T ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ H ≫ est R) ≫ h) ≫ est R
        ⊑ T ≫ Λ (T°) ≫ (thinRel Q ≫ (((∋ (F.obj b))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))) :=
      comp_mono_left _ (comp_mono_left _ (comp_mono_left _ hL))
    have t2 : T ≫ Λ (T°) ≫ (thinRel Q ≫ (((∋ (F.obj b))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)))
        ⊑ (∋ (F.obj b))° ≫ (thinRel Q ≫ (((∋ (F.obj b))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))) := by
      rw [← Cat.assoc T (Λ (T°)) _]
      exact comp_mono_right hTA _
    have t3 : (∋ (F.obj b))° ≫ (thinRel Q ≫ (((∋ (F.obj b))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)))
        ⊑ (Q° ≫ (∋ (F.obj b))°) ≫ (((∋ (F.obj b))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) := by
      rw [← Cat.assoc]
      exact comp_mono_right (recip_eps_comp_thinRel_le Q) _
    have t4 : (Q° ≫ (∋ (F.obj b))°) ≫ (((∋ (F.obj b))°) \
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

/-- **Theorem 9.2 (B&dM p.221)**, thinning dynamic programming: thinning by a preorder `Q` at
    every unfold step, before minimizing over `R°`, refines minimizing the plain hylomorphism
    recursion — provided `Q` interacts correctly with `H := ⦇h⦈·⦇T⦈°` and `h` (hypothesis
    `hQ`).  Ex 9.1 (`dynamic_programming_of_thin`) recovers Theorem 9.1 as the instance
    `Q := id`. By Knaster–Tarski via `dp_thin_prefixed`. -/
public theorem dynamic_programming_thin (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a} {Q : F.obj b ⟶ F.obj b}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°)
    (hQ : Q ≫ F.map ((relCata T)° ≫ relCata h) ≫ h
        ⊑ F.map ((relCata T)° ≫ relCata h) ≫ h ≫ R) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ ((relCata T)° ≫ relCata h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _ (dp_thin_prefixed hFr hh hmono htrans (hylo_fixed hFr I h T) hQ))

/-! ## Ex 9.1 — Theorem 9.1 as an instance of Theorem 9.2 -/

/-- **Ex 9.1**: Theorem 9.1 (`dynamic_programming`) is the `Q := id` instance of Theorem 9.2
    (`dynamic_programming_thin`) — thinning by the identity preorder never discards a
    candidate (`id ⊑ thin id`, `id_le_thinRel_id`), so the plain recursion refines the
    thinning recursion pointwise; discharging Theorem 9.2's `hQ` hypothesis at `Q := id` needs
    exactly `hrefl : id ⊑ R°`, which the direct proof of Theorem 9.1 does not require. -/
public theorem mu_le_mu_thinRel_id {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a} :
    mu (fun X : b ⟶ a => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ mu (fun X : b ⟶ a =>
          Λ (T°) ≫ thinRel (Cat.id (F.obj b)) ≫ powerRel (F.map X ≫ h) ≫ est R) :=
  mu_le_mu fun X => by
    have step := comp_mono_right id_le_thinRel_id (powerRel (F.map X ≫ h) ≫ est R)
    rw [Cat.id_comp] at step
    exact comp_mono_left _ step

/-- At `Q := id`, Theorem 9.2's thinning condition `hQ` says only that `R` is reflexive. -/
public theorem thin_condition_of_refl (I : InitialAlgebra F) {h : F.obj a ⟶ a}
    {T : F.obj b ⟶ b} {R : a ⟶ a} (hrefl : Cat.id a ⊑ R°) :
    Cat.id (F.obj b) ≫ F.map ((relCata T)° ≫ relCata h) ≫ h
      ⊑ F.map ((relCata T)° ≫ relCata h) ≫ h ≫ R := by
  rw [Cat.id_comp]
  have hid : Cat.id a ⊑ R := by
    have h1 := recip_mono hrefl
    rwa [recip_id, Allegory.recip_recip] at h1
  have step := comp_mono_left (F.map ((relCata T)° ≫ relCata h) ≫ h) hid
  rw [Cat.comp_id, Cat.assoc] at step
  exact step

theorem dynamic_programming_of_thin (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°) (hrefl : Cat.id a ⊑ R°) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ ((relCata T)° ≫ relCata h) ≫ est R :=
  le_trans mu_le_mu_thinRel_id
    (dynamic_programming_thin hFr I hh hmono htrans (thin_condition_of_refl I hrefl))

/-! ## Proposition 9.2 (B&dM p.222) — checking monotonicity via cost functions -/

/-- **Proposition 9.2 (B&dM p.222)**: an algebra `h` is monotonic on the order `R := cost·leq·cost°`
    (induced on `a` by pulling the order `leq` on `c` back along a "cost" function) whenever `h`
    followed by `cost` factors as `F.map cost` followed by an algebra `k` that is itself
    monotonic on `leq` — i.e. checking monotonicity of `h` on `R` reduces to checking
    monotonicity of the simpler algebra `k` on `leq`. -/
public theorem monotonicAlg_of_cost {c : 𝒜} {h : F.obj a ⟶ a} {R : a ⟶ a} {cost : a ⟶ c}
    {leq : c ⟶ c} {k : F.obj c ⟶ c} (hcost : Map cost) (hR : R = cost ≫ leq ≫ cost°)
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
    have e2 : cost ≫ leq ≫ (cost° ≫ cost) ⊑ cost ≫ leq ≫ Cat.id c :=
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
theorem thin_condition_of_optimum (hFr : F.PreservesRecip) {h : F.obj a ⟶ a}
    {R : a ⟶ a} {H M : b ⟶ a} (hh : Map h) (hmono : MonotonicAlg h R) (htrans : R ≫ R ⊑ R)
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

variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-- **Proposition 9.3 (B&dM p.223)**, monotonicity in context: given a cost function `cost`
    bundled with a simple context relation `S` via a chosen product `P`, and an algebra `k`
    (on the bundle) monotonic on `leq × id` in the sense of `hk`, the algebra `h` is monotonic
    on `R := cost·leq·cost°` RESTRICTED to `S`'s domain of definition (`R ∩ S·S°`) — a
    context-refined version of `monotonicAlg_of_cost` where the extra hypothesis `hk` need
    only see the product bundle, not the bare `cost`. -/
public theorem monotonicAlg_in_context {c : 𝒜} {h : F.obj a ⟶ a} {R : a ⟶ a} {cost : a ⟶ c}
    {S : a ⟶ b} {P : RelProd c b} {leq : c ⟶ c} {k : F.obj P.p ⟶ c}
    (hcost : Map cost) (hS : Simple S) (hR : R = cost ≫ leq ≫ cost°)
    (hch : h ≫ cost = F.map (P.pair cost S) ≫ k)
    (hk : F.map (prodMap P P leq (Cat.id b)) ≫ k ⊑ k ≫ leq) :
    F.map (R ∩ (S ≫ S°)) ≫ h ⊑ h ≫ R := by
  have hRexp : h ≫ R = (h ≫ cost ≫ leq) ≫ cost° := by rw [hR]; simp only [Cat.assoc]
  rw [hRexp]
  apply (map_shunt_right hcost _ _).mp
  -- goal: (F.map (R ∩ (S ≫ S°)) ≫ h) ≫ cost ⊑ h ≫ cost ≫ leq
  have eLHS1 : (F.map (R ∩ (S ≫ S°)) ≫ h) ≫ cost = F.map (R ∩ (S ≫ S°)) ≫ (h ≫ cost) := by
    rw [Cat.assoc]
  rw [eLHS1, hch]
  -- goal: F.map (R ∩ (S ≫ S°)) ≫ (F.map (P.pair cost S) ≫ k) ⊑ h ≫ cost ≫ leq
  have eFold1 : F.map (R ∩ (S ≫ S°)) ≫ (F.map (P.pair cost S) ≫ k)
      = (F.map (R ∩ (S ≫ S°)) ≫ F.map (P.pair cost S)) ≫ k := by rw [Cat.assoc]
  rw [eFold1]
  have eFold2 : F.map (R ∩ (S ≫ S°)) ≫ F.map (P.pair cost S)
      = F.map ((R ∩ (S ≫ S°)) ≫ P.pair cost S) := by rw [← F.map_comp]
  rw [eFold2]
  -- goal: F.map ((R ∩ (S ≫ S°)) ≫ P.pair cost S) ≫ k ⊑ h ≫ cost ≫ leq
  have hdecomp0 := P.pair_recip_pair (cost ≫ leq) S cost S
  have hReq : (cost ≫ leq) ≫ cost° = R := by rw [hR]; simp only [Cat.assoc]
  rw [hReq] at hdecomp0
  -- hdecomp0 : P.pair (cost ≫ leq) S ≫ (P.pair cost S)° = R ∩ (S ≫ S°)
  have hSimplePair : Simple (P.pair cost S) := tabulation_simple_of_simple P.tab hcost.2 hS
  have hcancel : (R ∩ (S ≫ S°)) ≫ P.pair cost S ⊑ P.pair (cost ≫ leq) S := by
    rw [← hdecomp0, Cat.assoc]
    have e2 := comp_mono_left (P.pair (cost ≫ leq) S) hSimplePair
    rwa [Cat.comp_id] at e2
  have step2 : F.map ((R ∩ (S ≫ S°)) ≫ P.pair cost S) ≫ k ⊑ F.map (P.pair (cost ≫ leq) S) ≫ k :=
    comp_mono_right (F.map_mono hcancel) k
  have habsorb : P.pair cost S ≫ prodMap P P leq (Cat.id b) = P.pair (cost ≫ leq) S :=
    P.pair_prodMap_fst cost S leq
  have step3 : F.map (P.pair (cost ≫ leq) S) ≫ k
      = (F.map (P.pair cost S) ≫ F.map (prodMap P P leq (Cat.id b))) ≫ k := by
    rw [← habsorb, F.map_comp]
  have step4 : (F.map (P.pair cost S) ≫ F.map (prodMap P P leq (Cat.id b))) ≫ k
      = F.map (P.pair cost S) ≫ (F.map (prodMap P P leq (Cat.id b)) ≫ k) := by rw [Cat.assoc]
  have eq1 : F.map (P.pair (cost ≫ leq) S) ≫ k
      = F.map (P.pair cost S) ≫ (F.map (prodMap P P leq (Cat.id b)) ≫ k) := step3.trans step4
  rw [eq1] at step2
  have step5 : F.map (P.pair cost S) ≫ (F.map (prodMap P P leq (Cat.id b)) ≫ k)
      ⊑ F.map (P.pair cost S) ≫ (k ≫ leq) := comp_mono_left _ hk
  have step6 : F.map (P.pair cost S) ≫ (k ≫ leq) = (F.map (P.pair cost S) ≫ k) ≫ leq := by
    rw [Cat.assoc]
  have step7 : (F.map (P.pair cost S) ≫ k) ≫ leq = (h ≫ cost) ≫ leq := by rw [← hch]
  have step8 : (h ≫ cost) ≫ leq = h ≫ cost ≫ leq := by rw [Cat.assoc]
  have eq2 : F.map (P.pair cost S) ≫ (k ≫ leq) = h ≫ cost ≫ leq := step6.trans (step7.trans step8)
  rw [eq2] at step5
  exact le_trans step2 step5

end Prop9_3

/-! ## Proposition 9.4 (B&dM pp.223-224) — bifunctor conditions

  Back in the file's ambient `UnguardedPowerLCDA` setting.  B&dM's monotonicity/thinning
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
  map : ∀ {a b c d : 𝒜}, (a ⟶ b) → (c ⟶ d) → (obj a c ⟶ obj b d)
  map_id : ∀ (a c : 𝒜), map (Cat.id a) (Cat.id c) = Cat.id (obj a c)
  map_comp : ∀ {a b c d e f : 𝒜} (R : a ⟶ b) (R' : b ⟶ c) (S : d ⟶ e) (S' : e ⟶ f),
    map (R ≫ R') (S ≫ S') = map R S ≫ map R' S'
  map_mono : ∀ {a b c d : 𝒜} {R R' : a ⟶ b} {S S' : c ⟶ d}, R ⊑ R' → S ⊑ S' → map R S ⊑ map R' S'

/-- A birelator PRESERVES CONVERSE when `G(R°, S°) = (G(R,S))°`. -/
@[expose] public def Birelator.PreservesRecip (G : Birelator 𝒜) : Prop :=
  ∀ {a b c d : 𝒜} (R : a ⟶ b) (S : c ⟶ d), G.map R° S° = (G.map R S)°

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
  map_id a := G.map_id e a
  map_comp R S := by
    have h := G.map_comp (Cat.id e) (Cat.id e) R S
    rwa [Cat.id_comp] at h
  map_mono h := G.map_mono (le_refl (Cat.id e)) h

/-- **Proposition 9.4(i) (B&dM p.223)**, monotonicity: if `h` is monotonic for `G` at some `U`
    refined from below by `id_e` (`hUrefl`), then `h` is monotonic (in the ordinary
    `MonotonicAlg` sense) for the fixed-left relator `G.fixLeft e`. -/
public theorem birelator_fixLeft_mono {G : Birelator 𝒜} {e : 𝒜} {h : G.obj e a ⟶ a} {R : a ⟶ a}
    {U : e ⟶ e} (hUrefl : Cat.id e ⊑ U) (hU : G.map U R ≫ h ⊑ h ≫ R) :
    G.map (Cat.id e) R ≫ h ⊑ h ≫ R :=
  le_trans (comp_mono_right (G.map_mono hUrefl (le_refl R)) h) hU

/-- A map `h` monotonic for `G` at `(U, R)` is monotonic at `(U°, R°)` — conjugate, then
    shunt back across the map `h` (the birelator analogue of `monotonicAlg_recip_iff`). -/
public theorem birelator_mono_recip {G : Birelator 𝒜} (hGr : G.PreservesRecip) {e : 𝒜}
    {h : G.obj e a ⟶ a} {R : a ⟶ a} {U : e ⟶ e} (hh : Map h)
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
  have hRRcollapse : R° ≫ (h° ≫ h) ⊑ R° ≫ Cat.id a := comp_mono_left R° hh.2
  rw [Cat.comp_id] at hRRcollapse
  exact (map_shunt_left hh _ _).mp (le_trans hpost hRRcollapse)

/-- **Proposition 9.4(ii) (B&dM pp.223-224)**, the thinning condition: given the monotonicity
    witness `hU` and the bound `hV : V·H ⊑ H·R` (the note's letters, at the folded `°`), the
    thinning relation `Q := G(U,V)` discharges `dynamic_programming_thin`'s hypothesis `hQ`
    for the fixed-left relator `G.fixLeft e` — a three-step calculation, no shunting. -/
public theorem birelator_thin_condition {G : Birelator 𝒜} {e w : 𝒜}
    {h : G.obj e a ⟶ a} {H : w ⟶ a} {R : a ⟶ a} {U : e ⟶ e} {V : w ⟶ w}
    (hU : G.map U R ≫ h ⊑ h ≫ R) (hV : V ≫ H ⊑ H ≫ R) :
    G.map U V ≫ G.map (Cat.id e) H ≫ h ⊑ G.map (Cat.id e) H ≫ h ≫ R := by
  have eBC : G.map U V ≫ G.map (Cat.id e) H = G.map U (V ≫ H) := by
    rw [← G.map_comp, Cat.comp_id]
  have eE0 := G.map_comp (Cat.id e) U H R
  rw [Cat.id_comp] at eE0
  have step1 : G.map U V ≫ G.map (Cat.id e) H ⊑ G.map (Cat.id e) H ≫ G.map U R := by
    rw [eBC, ← eE0]
    exact G.map_mono (le_refl U) hV
  have step3 := comp_mono_right step1 h
  have e1 : (G.map U V ≫ G.map (Cat.id e) H) ≫ h
      = G.map U V ≫ (G.map (Cat.id e) H ≫ h) := by rw [Cat.assoc]
  have e2 : (G.map (Cat.id e) H ≫ G.map U R) ≫ h
      = G.map (Cat.id e) H ≫ (G.map U R ≫ h) := by rw [Cat.assoc]
  rw [e1, e2] at step3
  exact le_trans step3 (comp_mono_left _ hU)

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
theorem thin_unfold_context_le (T : F.obj b ⟶ b) (Q : F.obj b ⟶ F.obj b) :
    T ≫ Λ (T°) ≫ thinRel Q ⊑ (Q ∩ (T ≫ T°))° ≫ (∋ (F.obj b))° := by
  have hctxEq : Λ (T°) ≫ thinRel (Q ∩ ((T°)° ≫ T°)) = Λ (T°) ≫ thinRel Q :=
    Λ_comp_thinRel_context (T°) Q
  rw [Allegory.recip_recip] at hctxEq
  rw [← hctxEq]
  have hTA : T ≫ Λ (T°) ⊑ (∋ (F.obj b))° := by
    have h0 := recip_comp_Λ_le_recip_eps (T°)
    rwa [Allegory.recip_recip] at h0
  have e1 : T ≫ (Λ (T°) ≫ thinRel (Q ∩ (T ≫ T°)))
      = (T ≫ Λ (T°)) ≫ thinRel (Q ∩ (T ≫ T°)) := by rw [Cat.assoc]
  rw [e1]
  exact le_trans (comp_mono_right hTA _) (recip_eps_comp_thinRel_le (Q ∩ (T ≫ T°)))

/-- **Ex 9.2 (B&dM p.222)**, the context-strengthened core of Theorem 9.2: monotonicity and
    the thinning condition need only hold on the relevant domains of definition
    (`R° ∩ (H°·H)` for monotonicity, `Q ∩ (T·T°)` for thinning). -/
theorem dp_thin_prefixed_context (hFr : F.PreservesRecip) {h : F.obj a ⟶ a} {T : F.obj b ⟶ b}
    {R : a ⟶ a} {Q : F.obj b ⟶ F.obj b} {H : b ⟶ a} (hh : Map h)
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
        ⊑ Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj b) ≫ F.map (Λ H ≫ est R) ≫ h) :=
      comp_mono_left _ (comp_mono_left _ (le_trans h94 (inter_lb_left _ _)))
    have step2 : Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj b) ≫ F.map (Λ H ≫ est R) ≫ h)
        ⊑ T° ≫ F.map (Λ H ≫ est R) ≫ h := by
      have e1 : Λ (T°) ≫ thinRel Q ≫ (∋ (F.obj b) ≫ F.map (Λ H ≫ est R) ≫ h)
          = (Λ (T°) ≫ (thinRel Q ≫ ∋ (F.obj b))) ≫ F.map (Λ H ≫ est R) ≫ h := by
        simp only [Cat.assoc]
      rw [e1]
      have e2 : (Λ (T°) ≫ (thinRel Q ≫ ∋ (F.obj b))) ≫ F.map (Λ H ≫ est R) ≫ h
          ⊑ (Λ (T°) ≫ ∋ (F.obj b)) ≫ F.map (Λ H ≫ est R) ≫ h :=
        comp_mono_right (comp_mono_left _ (thinRel_comp_eps_le Q)) _
      have e3 : (Λ (T°) ≫ ∋ (F.obj b)) ≫ F.map (Λ H ≫ est R) ≫ h
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
        ⊑ T ≫ Λ (T°) ≫ thinRel Q ≫ (((∋ (F.obj b))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) :=
      comp_mono_left _ (comp_mono_left _ (comp_mono_left _ hL))
    have e1 : T ≫ Λ (T°) ≫ thinRel Q ≫ (((∋ (F.obj b))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))
        = (T ≫ Λ (T°) ≫ thinRel Q) ≫ (((∋ (F.obj b))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) := by simp only [Cat.assoc]
    rw [e1] at t1
    have t2 : (T ≫ Λ (T°) ≫ thinRel Q) ≫ (((∋ (F.obj b))°) \
          ((F.map (Λ H ≫ est R) ≫ h) ≫ R°))
        ⊑ ((Q ∩ (T ≫ T°))° ≫ (∋ (F.obj b))°) ≫ (((∋ (F.obj b))°) \
            ((F.map (Λ H ≫ est R) ≫ h) ≫ R°)) :=
      comp_mono_right hsharp _
    have t3 : ((Q ∩ (T ≫ T°))° ≫ (∋ (F.obj b))°) ≫ (((∋ (F.obj b))°) \
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
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a} {Q : F.obj b ⟶ F.obj b} (hh : Map h)
    (hctx1 : F.map (R° ∩ (((relCata T)° ≫ relCata h)° ≫ (relCata T)° ≫ relCata h)) ≫ h
        ⊑ h ≫ R°)
    (htrans : R° ≫ R° ⊑ R°)
    (hctx2 : (Q ∩ (T ≫ T°)) ≫ F.map ((relCata T)° ≫ relCata h) ≫ h
        ⊑ F.map ((relCata T)° ≫ relCata h) ≫ h ≫ R) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ ((relCata T)° ≫ relCata h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _ (dp_thin_prefixed_context hFr hh hctx1 htrans (hylo_fixed hFr I h T) hctx2))

/-- **Theorem 9.1 in context**: the plain (un-thinned) dynamic-programming recursion refines the
    optimisation spec when `h` is monotonic only ON `H`'s domain of definition, `R° ∩ (H°·H)` —
    the form B&dM's §9.3 optimal-bracketing derivation uses, where only trees with the same
    flattening are ever compared.  Ex 9.2 (`dynamic_programming_thin_context`) at `Q := id`. -/
public theorem dynamic_programming_context (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a} (hh : Map h)
    (hctx1 : F.map (R° ∩ (((relCata T)° ≫ relCata h)° ≫ (relCata T)° ≫ relCata h)) ≫ h
        ⊑ h ≫ R°)
    (htrans : R° ≫ R° ⊑ R°) (hrefl : Cat.id a ⊑ R°) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ ((relCata T)° ≫ relCata h) ≫ est R :=
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
    file) live under `[UnguardedPowerLCDA 𝒜]` (`AOP.A6_2`), the power/division bundle.
  * No section of the repo currently instantiates BOTH classes on the same `𝒜` (no combined
    "distributive + unguarded power" class, and none of the `UnguardedPowerLCDA` model
    instances built elsewhere are known to also satisfy `DistributiveAllegory`). Proposition
    9.1 is not just "reuse an existing lemma under a stronger hypothesis" — its content is
    genuinely *thinning a coproduct-split search*: it needs `thin`/`powerRel`/`est` to
    interact correctly with `junc`/`guard`/`cond`, which is new mathematical work (roughly:
    an Ex-8.x-style fusion law for `thin` against `junc`, analogous to the already-dropped
    §8's (8.4)/Ex 8.7 `powerRel`-vs-`union` fusion, `AOP.A8_1`'s stretch-items note) on top
    of the missing combined typeclass. Building the combined class and the fusion law is a
    multi-file undertaking outside this task's scope; recorded here rather than forced. -/

end Freyd.Alg
