/-
  ∞-COMPLETED DYNAMIC PROGRAMMING — a new abstract theorem beyond Bird & de Moor §9.1.

  B&dM's Theorem 9.1 (`AOP.A9_1.dynamic_programming`) models dynamic programming with the
  body `min R · P(h·FX) · ΛT°` (mirrored: `Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ minRel R`).
  Its power relator is the EGLI–MILNER lifting (`AOP.A5_4`): term₁ demands EVERY element of
  the decomposition set `ΛT° v` be productive under `h·FX`.  For recursions that unfold a
  finite INPUT structure every branch is productive and the theorem is faithful; but for
  value-axis DPs with DEAD subproblems it collapses.  Canonical failure: coin change
  (`leet.L322`, comment at its end) — with coins {2,3}, amount 3 is solvable (one 3-coin),
  yet the c=2 branch leaves the unsolvable amount 1, so term₁ empties the candidate set and
  `μ(body) 3 = 𝟘`; the executable DP is not `⊑ μ(body)` and Theorem 9.1 cannot transfer its
  correctness.

  THE FIX (this file): adjoin a top `⊤ = ∞` ("no solution") to the value object.  Abstractly
  the ∞-extension is carried by a FALLBACK relation `τ : b ⟶ a` whose values are `R`-tops
  (`hτ : τ° ≫ ⊤ ⊑ R°` — everything is `R`-below a fallback value); a dead branch contributes
  the fallback instead of emptying the candidate set, and `min R` absorbs it (⊤ is the
  identity of `min`).  The recursion body becomes `dpBodyInf`:

    body X = (min R · P(h·FX) · ΛT°)  ∪  (τ ∩ ((R/∋) · P(h·FX) · ΛT°))        (mirrored below)

  — the usual minimum over the Egli–Milner candidate set, PLUS the fallback whenever the
  fallback is an `R`-lower bound of the candidates.  Since the fallback is a top, that extra
  disjunct only ever fires when every candidate is itself a fallback value — in particular
  when the candidate set is EMPTY, which is exactly the dead-branch case that kills Theorem
  9.1.  The specification extends likewise to `min R · Λ(H ∪ τ)`: the `R`-minimum over the
  hylomorphism results together with the fallback (`= min R · ΛH` when any solution exists,
  `= τ` when none does).

  **Theorem `dynamic_programming_inf`**: if `h` is a map monotonic on the transitive `R`, the
  fallback is top-valued (`hτ`), and the ∞-extended answer relation `H ∪ τ` absorbs one
  decompose-solve-fold step

    `hstrict : T° ≫ F.map (H ∪ τ) ≫ h ⊑ H ∪ τ`

  (this is where STRICTNESS of `h` at ⊤ enters: a candidate refolded from a structure with a
  fallback slot must itself be a fallback value — concretely `osucc ∞ = ∞`), then

    `μ(dpBodyInf) ⊑ min R · Λ(H ∪ τ)`      for `H = ⦇h⦈·⦇T⦈°`.

  At `τ := 𝟘` the second disjunct of the body vanishes (`𝟘 ∩ W = 𝟘`, `X ∪ 𝟘 = X`),
  `H ∪ 𝟘 = H`, `hstrict` is the `⊑` half of the hylomorphism fixed-point equation and `hτ`
  is trivial — the statement degenerates to Theorem 9.1, so this strictly generalizes B&dM.

  Setting and proof skeleton: `UnguardedPowerLCDA`, mirroring `dp_prefixed`'s min-universal-
  property argument (`AOP.A9_1`).  Composition is diagram order (B&dM `X·Y` = Freyd
  `Y ≫ X`).  The instantiation re-deriving `leet.L322`'s `coinSpec` correctness from this
  theorem is `leet.L322_dp`.
-/
module

public import AOP.A9_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {a b : 𝒜}

/-- The ∞-DP recursion body: decompose in all ways (`Λ (T°)`), solve subproblems and refold
    (`powerRel (F.map X ≫ h)`), then keep an `R`-minimum of the candidates — OR the fallback
    `τ`, whenever the fallback is an `R`-lower bound of the candidates (which, `τ` being
    top-valued, happens exactly when every candidate is itself a fallback value; in
    particular when the candidate set is empty, i.e. on a dead branch). -/
@[expose] public def dpBodyInf (F : Relator 𝒜 𝒜) (T : F.obj b ⟶ b) (h : F.obj a ⟶ a) (R : a ⟶ a)
    (τ : b ⟶ a) (X : b ⟶ a) : b ⟶ a :=
  (Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ minRel R)
    ∪ (τ ∩ (Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ leftDiv ((∋ a)°) (R°)))

/-- The ∞-DP body is monotonic in the recursion variable — so `μ(dpBodyInf)` is an honest
    least FIXED point (`mu_fixed`), which the executable-side bridge of an instantiation
    consumes (`leet.L322_dp`). -/
public theorem dpBodyInf_monotonic (F : Relator 𝒜 𝒜) (T : F.obj b ⟶ b) (h : F.obj a ⟶ a)
    (R : a ⟶ a) (τ : b ⟶ a) : Monotonic (dpBodyInf F T h R τ) := by
  intro X Y hXY
  have hp : powerRel (F.map X ≫ h) ⊑ powerRel (F.map Y ≫ h) :=
    powerRel_mono (comp_mono_right (F.map_mono hXY) h)
  exact union_mono
    (comp_mono_left _ (comp_mono_right hp _))
    (inter_mono (le_refl τ) (comp_mono_left _ (comp_mono_right hp _)))

/-- **Core of the ∞-DP theorem**: `M = min R · Λ(H ∪ τ)` is a PREFIXED point of `dpBodyInf`,
    for any `H` satisfying the hylomorphism fixed-point equation, any top-valued fallback
    `τ`, provided `H ∪ τ` absorbs one decompose-solve-fold step (`hstrict`).  Mirrors
    `dp_prefixed` (`AOP.A9_1`): the two obligations are the components of `min`'s universal
    property `le_Λ_comp_minRel_iff`; the fallback disjunct is handled by `τ ∩ W ⊑ τ` in the
    membership half and by `τ° ≫ W ⊑ τ° ≫ ⊤ ⊑ R°` (`hτ`) in the lower-bound half. -/
public theorem dp_inf_prefixed {F : Relator 𝒜 𝒜} (hFr : F.PreservesRecip) {h : F.obj a ⟶ a}
    {T : F.obj b ⟶ b} {R : a ⟶ a} {τ : b ⟶ a} {H : b ⟶ a}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R ≫ R ⊑ R)
    (hHfix : T° ≫ F.map H ≫ h = H)
    (hstrict : T° ≫ F.map (H ∪ τ) ≫ h ⊑ H ∪ τ)
    (hτ : τ° ≫ topHom b a ⊑ R°) :
    dpBodyInf F T h R τ (Λ (H ∪ τ) ≫ minRel R) ⊑ Λ (H ∪ τ) ≫ minRel R := by
  have htrans' : R° ≫ R° ⊑ R° := by
    have h0 := recip_mono htrans; rwa [Allegory.recip_comp] at h0
  -- the two min-UP components of `M ⊑ min R · Λ(H ∪ τ)`: `M ⊑ H ∪ τ` and `(H ∪ τ)° ≫ M ⊑ R°`
  obtain ⟨hMS, hSMR⟩ := le_Λ_comp_minRel_iff.mp (le_refl (Λ (H ∪ τ) ≫ minRel R))
  apply le_Λ_comp_minRel_iff.mpr
  constructor
  · -- membership: `body ⊑ H ∪ τ`
    apply union_lub
    · -- min disjunct, as (9.2) of `dp_prefixed`, ending in `hstrict` instead of `hHfix`
      have h94 := powerRel_comp_minRel_le (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) R
      have s1 : Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ minRel R
          ⊑ Λ (T°) ≫ ∋ (F.obj b) ≫ F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h :=
        comp_mono_left _ (le_trans h94 (inter_lb_left _ _))
      have s2 : Λ (T°) ≫ ∋ (F.obj b) ≫ F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h
          = T° ≫ F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h := by
        rw [← Cat.assoc (Λ (T°)) (∋ (F.obj b)) _, Λ_eps_eq']
      have s3 : T° ≫ F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h ⊑ T° ≫ F.map (H ∪ τ) ≫ h :=
        comp_mono_left _ (comp_mono_right (F.map_mono hMS) h)
      rw [s2] at s1
      exact le_trans s1 (le_trans s3 hstrict)
    · -- fallback disjunct: `τ ∩ W ⊑ τ ⊑ H ∪ τ`
      exact le_trans (inter_lb_left _ _) (le_union_right _ _)
  · -- lower bound: `(H ∪ τ)° ≫ body ⊑ R°`
    -- both disjuncts are below the uniform lower-bound relation `W = (R/∋)·P(h·FM)·ΛT°`
    have hbW : dpBodyInf F T h R τ (Λ (H ∪ τ) ≫ minRel R)
        ⊑ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ leftDiv ((∋ a)°) (R°) := by
      apply union_lub
      · exact comp_mono_left _ (comp_mono_left _
          (show minRel R ⊑ leftDiv ((∋ a)°) (R°) from inter_lb_right _ _))
      · exact inter_lb_right _ _
    -- `H°` kills `W` by the (9.3)-style chain of `dp_prefixed`
    have hHrec : H° = h° ≫ F.map (H°) ≫ T := by
      have h1 : (T° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ T := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H, Cat.assoc]
      rw [← h1, hHfix]
    have hTA : T ≫ Λ (T°) ⊑ (∋ (F.obj b))° := by
      have h0 := recip_comp_Λ_le_recip_eps (T°)
      rwa [Allegory.recip_recip] at h0
    have htail : T ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
          ≫ leftDiv ((∋ a)°) (R°)
        ⊑ (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ R° := by
      have t1 : T ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
            ≫ leftDiv ((∋ a)°) (R°)
          ⊑ (∋ (F.obj b))° ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
            ≫ leftDiv ((∋ a)°) (R°) := by
        rw [← Cat.assoc T (Λ (T°)) _]
        exact comp_mono_right hTA _
      have t2 : (∋ (F.obj b))° ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
            ≫ leftDiv ((∋ a)°) (R°)
          ⊑ ((F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ (∋ a)°) ≫ leftDiv ((∋ a)°) (R°) := by
        rw [← Cat.assoc ((∋ (F.obj b))°) (powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h))
          (leftDiv ((∋ a)°) (R°))]
        exact comp_mono_right (powerRel_term1_cancel _) _
      have t3 : ((F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ (∋ a)°) ≫ leftDiv ((∋ a)°) (R°)
          ⊑ (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ R° := by
        rw [Cat.assoc]
        exact comp_mono_left _ (leftDiv_comp_le _ _)
      exact le_trans t1 (le_trans t2 t3)
    have hHW : H° ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
          ≫ leftDiv ((∋ a)°) (R°) ⊑ R° := by
      -- split `H°` in front and reassociate (backward-rewrite trick, cf. `dp_prefixed`)
      have c1 : H° ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
            ≫ leftDiv ((∋ a)°) (R°)
          = (h° ≫ F.map (H°) ≫ T)
              ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
              ≫ leftDiv ((∋ a)°) (R°) := by
        rw [← hHrec]
      have c2 : (h° ≫ F.map (H°) ≫ T)
            ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ leftDiv ((∋ a)°) (R°)
          = (h° ≫ F.map (H°))
              ≫ T ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
              ≫ leftDiv ((∋ a)°) (R°) := by
        simp only [Cat.assoc]
      have hbound : (h° ≫ F.map (H°))
            ≫ T ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
            ≫ leftDiv ((∋ a)°) (R°)
          ⊑ (h° ≫ F.map (H°)) ≫ (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ R° :=
        comp_mono_left _ htail
      -- collapse: `F(M·H°) ⊑ FR` then conjugated monotonicity and transitivity
      have hHMR : H° ≫ (Λ (H ∪ τ) ≫ minRel R) ⊑ R° :=
        le_trans (comp_mono_right (recip_mono (le_union_left H τ)) _) hSMR
      have hcollapse : (h° ≫ F.map (H°)) ≫ (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ R°
          ⊑ R° ≫ R° := by
        have hFRM : F.map (H°) ≫ F.map (Λ (H ∪ τ) ≫ minRel R) ⊑ F.map (R°) := by
          rw [← F.map_comp]
          exact F.map_mono hHMR
        have hinner : h° ≫ F.map (H°) ≫ F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h ⊑ R° := by
          have hx : h° ≫ F.map (H°) ≫ F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h
              ⊑ h° ≫ F.map (R°) ≫ h := by
            rw [← Cat.assoc (F.map (H°)) (F.map (Λ (H ∪ τ) ≫ minRel R)) h]
            exact comp_mono_left _ (comp_mono_right hFRM h)
          exact le_trans hx ((monotonicAlg_iff_conj hh).mp hmono)
        have hre : (h° ≫ F.map (H°)) ≫ (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ R°
            = (h° ≫ F.map (H°) ≫ F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h) ≫ R° := by
          simp only [Cat.assoc]
        rw [hre]
        exact comp_mono_right hinner (R°)
      rw [c1, c2]
      exact le_trans (le_trans hbound hcollapse) htrans'
    -- `τ°` kills anything: `τ° ≫ W ⊑ τ° ≫ ⊤ ⊑ R°` since the fallback is top-valued
    have hτW : τ° ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
          ≫ leftDiv ((∋ a)°) (R°) ⊑ R° :=
      le_trans (comp_mono_left τ° (LocallyCompleteDistributiveAllegory.le_Sup trivial)) hτ
    -- assemble: distribute `(H ∪ τ)° = τ° ∪ H°` over the composite
    have hsplit := comp_mono_left ((H ∪ τ)°) hbW
    have hexp : (H ∪ τ)° ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
          ≫ leftDiv ((∋ a)°) (R°)
        = (τ° ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
            ≫ leftDiv ((∋ a)°) (R°))
          ∪ (H° ≫ Λ (T°) ≫ powerRel (F.map (Λ (H ∪ τ) ≫ minRel R) ≫ h)
            ≫ leftDiv ((∋ a)°) (R°)) := by
      rw [recip_union, union_comp_distrib]
    rw [hexp] at hsplit
    exact le_trans hsplit (union_lub hτW hHW)

/-- **The ∞-completed dynamic-programming theorem** (new; strictly generalizes B&dM Theorem
    9.1, which is the `τ := 𝟘` degeneration): decomposing the input in all possible ways,
    solving subproblems recursively, and keeping an `R`-optimum of the partial results — with
    a top-valued fallback `τ` stepping in for DEAD branches — refines "generate every
    solution, adjoin the fallback, pick a global `R`-optimum".  The dead-branch hypothesis is
    `hstrict`: the ∞-extended answer relation `H ∪ τ` (all hylomorphism results, plus the
    fallback) absorbs one decompose-solve-fold step; concretely it holds because the refold
    algebra `h` is STRICT at the adjoined top (`osucc ∞ = ∞` in `leet.L322`).  By
    Knaster–Tarski (`Sup_le`'s lower-bound half) via `dp_inf_prefixed` and the hylomorphism
    theorem (`hylo_fixed`, B&dM Theorem 6.2). -/
public theorem dynamic_programming_inf {F : Relator 𝒜 𝒜} (hFr : F.PreservesRecip)
    (I : InitialAlgebra F) {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a} {τ : b ⟶ a}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R ≫ R ⊑ R)
    (hstrict : T° ≫ F.map (((relCata I T)° ≫ relCata I h) ∪ τ) ≫ h
        ⊑ ((relCata I T)° ≫ relCata I h) ∪ τ)
    (hτ : τ° ≫ topHom b a ⊑ R°) :
    mu (dpBodyInf F T h R τ)
      ⊑ Λ (((relCata I T)° ≫ relCata I h) ∪ τ) ≫ minRel R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS =>
    hS _ (dp_inf_prefixed hFr hh hmono htrans (hylo_fixed hFr I h T) hstrict hτ))

end Freyd.Alg
