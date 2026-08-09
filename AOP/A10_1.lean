/-
  Bird & de Moor, *Algebra of Programming* §10.1  Greedy algorithms: theory (book pp. 245-246)
  — CORE (Theorem 10.1).

  A GREEDY algorithm is the EXTREME case of dynamic programming (chapter 9) in which all but a
  SINGLE decomposition of the input is weeded out at each step: instead of keeping a whole set
  of partial solutions and minimising at the end (`min R · P(h·FX) · thin Q · ΛT°`, Theorem
  9.2), the greedy recursion greedily commits to one `Q`-minimum decomposition and refolds it
  (`h · FX · min Q · ΛT°`).  **Theorem 10.1**: under EXACTLY Theorem 9.2's hypotheses (`h`
  monotonic on the transitive `R`, and the thinning-compatibility bound `hQ`), the greedy
  recursion still refines the optimisation spec `M = min R · ΛH` with `H = ⦇h⦈·⦇T⦈°`.  B&dM
  state it has "exactly the same hypotheses as Theorem 9.2" and leave the (very similar) proof
  as an exercise; it is discharged here by mirroring `dp_thin_prefixed` (`AOP.A9_1`), only
  simpler — `min Q` is peeled by the two halves of the `min` universal property
  (`inter_lb_left` for membership, `recip_eps_comp_minRel_le` for the lower bound) in place of
  the `powerRel`/`leftDiv` detour.

  MIRRORING (diagram order, B&dM `X·Y` = Freyd `Y ≫ X`; conventions as in `AOP.A9_1`):
  - B&dM `M = min R·ΛH` is `A H ≫ minRel R`; the greedy body `h·FX·min Q·ΛT°` is
    `A (T°) ≫ minRel Q ≫ F.map X ≫ h`.
  - the hypothesis `Q` satisfies `h·FH·Q° ⊆ R°·h·FH` mirrors to
    `Q° ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R°` — identical to Theorem 9.2's `hQ`.
  - `min Q ⊆ ∈` is `AOP.A7_1`'s `inter_lb_left` (unfolding `minRel`); the lower bound
    `min Q·∋ ⊆ Q` is `recip_eps_comp_minRel_le`.

  The disjoint-ranges/coproduct optimisation (B&dM Proposition 10.1, "a variation on
  Proposition 9.1") is DROPPED for the same setting reason as Proposition 9.1/Ex 9.5 — see the
  drop note at the end of `AOP.A9_1`.

  Setting: `UnguardedPowerLCDA` (`AOP.A6_2`), continuing chapters 7-9.
-/
module

public import AOP.A9_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-! ## Theorem 10.1 (B&dM p.245) — the greedy theorem, as extreme dynamic programming -/

/-- **Core of Theorem 10.1**: `M = min R·ΛH` (mirrored `A H ≫ minRel R`) is a PREFIXED point of
    the GREEDY body `h·FX·min Q·ΛT°` (mirrored `A (T°) ≫ minRel Q ≫ F.map X ≫ h`), for any `H`
    satisfying the hylomorphism fixed-point equation `H = h·FH·T°` and any `Q` satisfying the
    thinning-compatibility bound `hQ` (identical to `dp_thin_prefixed`'s).  Same two-branch
    `min`-universal-property skeleton as `dp_thin_prefixed`, with `min Q` handled directly by
    `inter_lb_left` (member) and `recip_eps_comp_minRel_le` (lower bound). -/
public theorem greedy_dp_prefixed (hFr : F.PreservesRecip) {h : F.obj a ⟶ a} {T : F.obj b ⟶ b}
    {R : a ⟶ a} {Q : F.obj b ⟶ F.obj b} {H : b ⟶ a} (hh : Map h) (hmono : MonotonicAlg h R)
    (htrans : R ≫ R ⊑ R) (hHfix : T° ≫ F.map H ≫ h = H)
    (hQ : Q° ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R°) :
    A (T°) ≫ minRel Q ≫ F.map (A H ≫ minRel R) ≫ h ⊑ A H ≫ minRel R := by
  obtain ⟨hMH, hHMR⟩ := le_A_comp_minRel_iff.mp (le_refl (A H ≫ minRel R))
  apply le_A_comp_minRel_iff.mpr
  constructor
  · -- component (i): greedy body ⊑ H, via `min Q ⊆ ∈` and the fixed-point equation
    have s1 : A (T°) ≫ minRel Q ≫ F.map (A H ≫ minRel R) ≫ h
        ⊑ A (T°) ≫ ∋ (F.obj b) ≫ F.map (A H ≫ minRel R) ≫ h :=
      comp_mono_left _ (comp_mono_right (show minRel Q ⊑ ∋ (F.obj b) from inter_lb_left _ _) _)
    have s2 : A (T°) ≫ ∋ (F.obj b) ≫ F.map (A H ≫ minRel R) ≫ h
        = T° ≫ F.map (A H ≫ minRel R) ≫ h := by
      rw [← Cat.assoc (A (T°)) (∋ (F.obj b)) _, A_eps_eq']
    have s3 : T° ≫ F.map (A H ≫ minRel R) ≫ h ⊑ T° ≫ F.map H ≫ h :=
      comp_mono_left _ (comp_mono_right (F.map_mono hMH) h)
    rw [s2] at s1
    rw [hHfix] at s3
    exact le_trans s1 s3
  · -- component (ii): `H°·(greedy body) ⊑ R`
    have hTA : T ≫ A (T°) ⊑ (∋ (F.obj b))° := by
      have h0 := recip_comp_A_le_recip_eps (T°)
      rwa [Allegory.recip_recip] at h0
    have hHrec : H° = h° ≫ F.map (H°) ≫ T := by
      have h1 : (T° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ T := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H, Cat.assoc]
      rw [← h1, hHfix]
    -- the tail bound: peel `T·ΛT°` to `∋°`, then the `min` lower bound gives `Q`
    have htail : T ≫ A (T°) ≫ minRel Q ⊑ Q := by
      have t1 : T ≫ A (T°) ≫ minRel Q ⊑ (∋ (F.obj b))° ≫ minRel Q := by
        rw [← Cat.assoc T (A (T°)) _]
        exact comp_mono_right hTA _
      exact le_trans t1 (recip_eps_comp_minRel_le Q)
    -- split `H°` in front and reassociate (cf. `dp_thin_prefixed`'s `c1`/`c2`)
    have c1 : H° ≫ A (T°) ≫ minRel Q ≫ F.map (A H ≫ minRel R) ≫ h
        = (h° ≫ F.map (H°) ≫ T) ≫ A (T°) ≫ minRel Q ≫ F.map (A H ≫ minRel R) ≫ h := by
      rw [← hHrec]
    have c2 : (h° ≫ F.map (H°) ≫ T) ≫ A (T°) ≫ minRel Q ≫ F.map (A H ≫ minRel R) ≫ h
        = (h° ≫ F.map (H°)) ≫ (T ≫ A (T°) ≫ minRel Q) ≫ F.map (A H ≫ minRel R) ≫ h := by
      simp only [Cat.assoc]
    have hbound : (h° ≫ F.map (H°)) ≫ (T ≫ A (T°) ≫ minRel Q) ≫ F.map (A H ≫ minRel R) ≫ h
        ⊑ (h° ≫ F.map (H°)) ≫ Q ≫ F.map (A H ≫ minRel R) ≫ h :=
      comp_mono_left _ (comp_mono_right htail _)
    -- the `hQ` step: conjugate `hQ` to `h°·FH°·Q ⊑ R·h°·FH°`
    have hQrec : h° ≫ F.map (H°) ≫ Q ⊑ R ≫ h° ≫ F.map (H°) := by
      have hrm := recip_mono hQ
      have eL : (Q° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ Q := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H, Cat.assoc]
      have eR : (F.map H ≫ h ≫ R°)° = R ≫ h° ≫ F.map (H°) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H, Cat.assoc]
      rwa [eL, eR] at hrm
    have hre1 : (h° ≫ F.map (H°)) ≫ Q ≫ F.map (A H ≫ minRel R) ≫ h
        = (h° ≫ F.map (H°) ≫ Q) ≫ F.map (A H ≫ minRel R) ≫ h := by
      simp only [Cat.assoc]
    have step6 : (h° ≫ F.map (H°) ≫ Q) ≫ F.map (A H ≫ minRel R) ≫ h
        ⊑ (R ≫ h° ≫ F.map (H°)) ≫ F.map (A H ≫ minRel R) ≫ h :=
      comp_mono_right hQrec _
    have hre2 : (R ≫ h° ≫ F.map (H°)) ≫ F.map (A H ≫ minRel R) ≫ h
        = R ≫ (h° ≫ F.map (H°) ≫ F.map (A H ≫ minRel R) ≫ h) := by
      simp only [Cat.assoc]
    -- collapse `F(M·H°) ⊆ FR`, then conjugated monotonicity and transitivity
    have hinner : h° ≫ F.map (H°) ≫ F.map (A H ≫ minRel R) ≫ h ⊑ R := by
      have hFRM : F.map (H°) ≫ F.map (A H ≫ minRel R) ⊑ F.map R := by
        rw [← F.map_comp]; exact F.map_mono hHMR
      have hx : h° ≫ F.map (H°) ≫ F.map (A H ≫ minRel R) ≫ h ⊑ h° ≫ F.map R ≫ h := by
        rw [← Cat.assoc (F.map (H°)) (F.map (A H ≫ minRel R)) h]
        exact comp_mono_left _ (comp_mono_right hFRM h)
      exact le_trans hx ((monotonicAlg_iff_conj hh).mp hmono)
    have step7 : R ≫ (h° ≫ F.map (H°) ≫ F.map (A H ≫ minRel R) ≫ h) ⊑ R ≫ R :=
      comp_mono_left R hinner
    rw [c1, c2]
    refine le_trans hbound ?_
    rw [hre1]
    refine le_trans step6 ?_
    rw [hre2]
    exact le_trans step7 htrans

/-- **Theorem 10.1 (B&dM p.245)**, the GREEDY theorem as an extreme case of dynamic
    programming: `(μX : h·FX·min Q·ΛT°) ⊆ min R·ΛH` for `H = ⦇h⦈·⦇T⦈°`, mirrored — greedily
    committing to a single `Q`-minimum decomposition at each unfold step, then refolding
    through `h`, still refines the optimisation spec, under exactly Theorem 9.2's hypotheses
    (`h` monotonic on transitive `R`, plus the compatibility bound `hQ`).  By Knaster-Tarski
    (`Sup_le`'s lower-bound half) via `greedy_dp_prefixed`.  (Distinct from `AOP.A7_2`'s `greedy`,
    the Theorem 7.2 greedy theorem `⦇min R·ΛS⦈ ⊆ min R·Λ⦇S⦈`.) -/
public theorem greedy_dp (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a} {Q : F.obj b ⟶ F.obj b}
    (hh : Map h) (hmono : MonotonicAlg h R) (htrans : R ≫ R ⊑ R)
    (hQ : Q° ≫ F.map ((relCata I T)° ≫ relCata I h) ≫ h
        ⊑ F.map ((relCata I T)° ≫ relCata I h) ≫ h ≫ R°) :
    mu (fun X : b ⟶ a => A (T°) ≫ minRel Q ≫ F.map X ≫ h)
      ⊑ A ((relCata I T)° ≫ relCata I h) ≫ minRel R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _ (greedy_dp_prefixed hFr hh hmono htrans (hylo_fixed hFr I h T) hQ))

/-! ## B&dM p.246 — the greedy hypotheses via a bifunctor (recall of Proposition 9.4)

  B&dM close §10.1 by recalling Proposition 9.4 (`AOP.A9_1`'s `Birelator` infra): the
  greedy theorem's hypotheses are met by taking `Q = F(U,V)` with `U`, `V` preorders such that
  `h·F(U,R) ⊆ R·h` and `H·V° ⊆ R°·H`.  As in chapter 9, the REFINEMENT itself needs only `U`
  reflexive (to get `MonotonicAlg` for the fixed-left relator via Prop 9.4(i)); reflexivity of
  `V` and transitivity of `U`/`V` are not used.  (B&dM warn that such a `Q` is not always
  appropriate for an EXECUTABLE greedy algorithm, since one also needs `min Q·ΛT°` entire — an
  executability caveat on top of the refinement, not part of it.) -/

/-- `G.fixLeft e` preserves converse whenever `G` does — `(G.fixLeft e).map R = G.map (id_e) R`
    and `(id_e)° = id_e`, so `G.PreservesRecip` at `id_e` gives the relator condition. -/
theorem Birelator.fixLeft_preservesRecip {G : Birelator 𝒜} (hGr : G.PreservesRecip) (e : 𝒜) :
    (G.fixLeft e).PreservesRecip := by
  intro c d R
  have h := hGr (Cat.id e) R
  rwa [recip_id] at h

/-- **B&dM p.246**, the greedy theorem via bifunctor conditions: with `Q := G(U,V)` for a
    birelator `G` (and `F := G.fixLeft e`), Proposition 9.4's monotonicity witness `hU`
    (`h·G(U,R) ⊆ R·h`) and reciprocal bound `hV` (`V°·H ⊆ H·R°`), plus reflexivity of `U`,
    discharge all of `greedy_dp`'s hypotheses — so the greedy recursion refines the spec. -/
theorem greedy_dp_of_birelator {G : Birelator 𝒜} (hGr : G.PreservesRecip) {e : 𝒜}
    (I : InitialAlgebra (G.fixLeft e)) {h : G.obj e a ⟶ a} {T : G.obj e b ⟶ b} {R : a ⟶ a}
    {U : e ⟶ e} {V : b ⟶ b} (hh : Map h) (htrans : R ≫ R ⊑ R) (hUrefl : Cat.id e ⊑ U)
    (hU : G.map U R ≫ h ⊑ h ≫ R)
    (hV : V° ≫ ((relCata I T)° ≫ relCata I h) ⊑ ((relCata I T)° ≫ relCata I h) ≫ R°) :
    mu (fun X : b ⟶ a => A (T°) ≫ minRel (G.map U V) ≫ (G.fixLeft e).map X ≫ h)
      ⊑ A ((relCata I T)° ≫ relCata I h) ≫ minRel R :=
  greedy_dp (F := G.fixLeft e) (Birelator.fixLeft_preservesRecip hGr e) I hh
    (birelator_fixLeft_mono hUrefl hU) htrans
    (birelator_thin_condition hGr (H := (relCata I T)° ≫ relCata I h) hh hU hV)

end Freyd.Alg
