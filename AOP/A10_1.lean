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
  (`inter_lb_left` for membership, `recip_eps_comp_est_le` for the lower bound) in place of
  the `powerRel`/`leftDiv` detour.

  MIRRORING (diagram order, B&dM `X·Y` = Freyd `Y ≫ X`; conventions as in `AOP.A9_1`):
  - B&dM `M = min R·ΛH` is `Λ H ≫ est R`; the greedy body `h·FX·min Q·ΛT°` is
    `Λ (T°) ≫ est Q ≫ F.map X ≫ h`.
  - the hypothesis `Q` satisfies `h·FH·Q° ⊆ R°·h·FH` mirrors, at the `est`-relabeled `Q` and
    `R` (`est X` = `min X°`), to `Q ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R` — identical to Theorem
    9.2's `hQ`.
  - `min Q ⊆ ∈` is `AOP.A7_1`'s `inter_lb_left` (unfolding `est`); the lower bound
    `min Q·∋ ⊆ Q` is `recip_eps_comp_est_le`.

  The disjoint-ranges/coproduct optimisation (B&dM Proposition 10.1, "a variation on
  Proposition 9.1") is `RelSet.greedy_disjoint_ranges` below, in `Rel(Set)` like Proposition 9.1.

  Setting: `TabularUnitaryUnguardedPowerLCDA` (`AOP.A6_2`), continuing chapters 7-9.
-/
module

public import AOP.A9_1
public import AOP.A7_2_RelSet
import AOP.CalcSteps

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {A B : 𝒜}

/-! ## Theorem 10.1 (B&dM p.245) — the greedy theorem, as extreme dynamic programming -/

/-! ### Theorem 10.1's proof, one `calc` step per hint (note §16.1)

  The exercise B&dM leave: Theorem 9.2's proof with `est(Q)` for `thin(Q)`.  `M≜Λ(H) est(R)`
  throughout; Knaster–Tarski needs the body at `M` below `M`, which `M=H∩(H°\R°)` splits into
  (i) `body(M)⊑H` and (ii) `H°body(M)⊑R°`. -/

/-- `est(Q)⊑∋`: an `est` picks a member. -/
public theorem est_le_eps {C : 𝒜} (Q : C ⟶ C) : est Q ⊑ ∋ C := inter_lb_left _ _

/-- **Theorem 10.1, (i)**: the greedy body at `M` returns only what `H` returns. -/
public theorem greedy_dp_lower [InitialAlgebra F] {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} :
    Λ (T°) ≫ est Q ≫ F.map (Λ (H T h) ≫ est R) ≫ h ⊑ H T h :=
  calc Λ (T°) ≫ est Q ≫ F.map (Λ (H T h) ≫ est R) ≫ h
        ⊑ Λ (T°) ≫ ∋ (F.obj A) ≫ F.map (Λ (H T h) ≫ est R) ≫ h :=
        comp_mono_left _ (comp_mono_right (est_le_eps Q) _)
      _ = T° ≫ F.map (Λ (H T h) ≫ est R) ≫ h := by rw [← Cat.assoc (Λ (T°)) (∋ (F.obj A)) _, Λ_eps_eq']
      _ ⊑ T° ≫ F.map (H T h) ≫ h := comp_mono_left _ (comp_mono_right (F.map_mono (Λ_comp_est_le (H T h) R)) h)
      _ = H T h := H_fixed inferInstance T h

calc_steps greedy_dp_lower

/-- **Theorem 10.1, (ii)**: `H°` followed by the greedy body at `M` is `⊑R°`. -/
public theorem greedy_dp_upper [InitialAlgebra F] {h : F.obj B ⟶ B}
    {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} (hh : Map h)
    (hmono : MonoAlg h R) (htrans : R ≫ R ⊑ R) (hQ : ThinCondition T h R Q) :
    (H T h)° ≫ Λ (T°) ≫ est Q ≫ F.map (Λ (H T h) ≫ est R) ≫ h ⊑ R° :=
  calc (H T h)° ≫ Λ (T°) ≫ est Q ≫ F.map (Λ (H T h) ≫ est R) ≫ h
        = h° ≫ F.map ((H T h)°) ≫ T ≫ Λ (T°) ≫ est Q ≫ F.map (Λ (H T h) ≫ est R) ≫ h :=
        id ((congrArg (· ≫ _) (recip_of_fixed T h)).trans
          ((Cat.assoc _ _ _).trans (congrArg (_ ≫ ·) (Cat.assoc _ _ _))))
      _ ⊑ h° ≫ F.map ((H T h)°) ≫ (∋ (F.obj A))° ≫ est Q ≫ F.map (Λ (H T h) ≫ est R) ≫ h :=
        comp_mono_left _ (comp_mono_left _ (by
          simpa only [Cat.assoc] using
            (comp_mono_right (comp_Λ_recip_le_recip_eps T) (est Q ≫ F.map (Λ (H T h) ≫ est R) ≫ h))))
      _ ⊑ h° ≫ F.map ((H T h)°) ≫ Q° ≫ F.map (Λ (H T h) ≫ est R) ≫ h :=
        comp_mono_left _ (comp_mono_left _ (by
          simpa only [Cat.assoc] using
            (comp_mono_right (recip_eps_comp_est_le Q) (F.map (Λ (H T h) ≫ est R) ≫ h))))
      _ ⊑ R° ≫ h° ≫ F.map ((H T h)°) ≫ F.map (Λ (H T h) ≫ est R) ≫ h := by
        simpa only [Cat.assoc] using comp_mono_right (recip_thin_condition hQ) (F.map (Λ (H T h) ≫ est R) ≫ h)
      _ = R° ≫ h° ≫ F.map ((H T h)° ≫ Λ (H T h) ≫ est R) ≫ h := by
        rw [F.map_comp ((H T h)°) (Λ (H T h) ≫ est R)]
        repeat rw [Cat.assoc]
      _ ⊑ R° ≫ h° ≫ F.map R° ≫ h :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_right (F.map_mono (recip_comp_Λ_comp_est_le (H T h) R)) h))
      _ ⊑ R° ≫ R° := comp_mono_left _ (recip_conj_le_of_monoAlg hh hmono)
      _ ⊑ R° := recip_trans_of_trans htrans

calc_steps greedy_dp_upper

/-- **Core of Theorem 10.1**: `M = min R°·ΛH` (mirrored `Λ H ≫ est R`) is a PREFIXED point of
    the GREEDY body `h·FX·min Q°·ΛT°` (mirrored `Λ (T°) ≫ est Q ≫ F.map X ≫ h`) — (i) and (ii)
    joined by the `min` universal property. -/
public theorem greedy_dp_prefixed [InitialAlgebra F] {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} (hh : Map h) (hmono : MonoAlg h R)
    (htrans : R ≫ R ⊑ R) (hQ : ThinCondition T h R Q) :
    Λ (T°) ≫ est Q ≫ F.map (Λ (H T h) ≫ est R) ≫ h ⊑ Λ (H T h) ≫ est R :=
  le_Λ_comp_est_iff.mpr ⟨greedy_dp_lower, greedy_dp_upper hh hmono htrans hQ⟩

/-! ### The optimisation chain (note §16.1b)

  `H%∋ est(R) ⊒ (T°)%∋ est(Q)F(X)h`: the note draws the spec as the single bead `X` sitting
  inside the body, so the step abstracts that abbreviation out of `greedy_dp_prefixed`. -/

/-- Step 1: at `X≜H%∋ est(R)` the greedy body is below the spec — the prefixed point
    Knaster–Tarski consumes, with the note's bead `X` as a binder of its own. -/
public theorem greedy_dp_step1 [InitialAlgebra F]
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A}
    {X : A ⟶ B} (hh : Map h) (hmono : MonoAlg h R) (htrans : R ≫ R ⊑ R)
    (hQ : ThinCondition T h R Q) (hX : X = Λ (H T h) ≫ est R) :
    Λ (T°) ≫ est Q ≫ F.map X ≫ h ⊑ Λ (H T h) ≫ est R := by
  subst hX
  exact greedy_dp_prefixed hh hmono htrans hQ

/-- **Theorem 10.1 (B&dM p.245)**, the GREEDY theorem as an extreme case of dynamic
    programming: `(μX : h·FX·min Q°·ΛT°) ⊆ min R°·ΛH` for `H = ⦇h⦈·⦇T⦈°`, mirrored — greedily
    committing to a single `Q°`-minimum decomposition at each unfold step, then refolding
    through `h`, still refines the optimisation spec, under exactly Theorem 9.2's hypotheses
    (`h` monotonic on the transitive `R`, plus the compatibility bound `hQ`).  By Knaster-Tarski
    (`Sup_le`'s lower-bound half) via `greedy_dp_prefixed`.  (Distinct from `AOP.A7_2`'s `greedy`,
    the Theorem 7.2 greedy theorem `⦇min R°·ΛS⦈ ⊆ min R°·Λ⦇S⦈`.) -/
public theorem greedy_dp (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A}
    (hh : Map h) (hmono : Freyd.Alg.MonoAlg h R) (htrans : R ≫ R ⊑ R)
    (hQ : ThinCondition T h R Q) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ est Q ≫ F.map X ≫ h)
      ⊑ Λ (H T h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _
    (greedy_dp_step1 hh hmono htrans hQ rfl))

/-! ## B&dM p.246 — the greedy hypotheses via a bifunctor (recall of Proposition 9.4)

  B&dM close §10.1 by recalling Proposition 9.4 (`AOP.A9_1`'s `BiRelator` infra): the
  greedy theorem's hypotheses are met by taking `Q = F(U,V)` with `U`, `V` preorders such that
  `h·F(U,R) ⊆ R·h` and `H·V° ⊆ R°·H`.  As in chapter 9, the REFINEMENT itself needs only `U`
  reflexive (to get `MonotonicAlg` for the fixed-left relator via Prop 9.4(i)); reflexivity of
  `V` and transitivity of `U`/`V` are not used.  (B&dM warn that such a `Q` is not always
  appropriate for an EXECUTABLE greedy algorithm, since one also needs `min Q·ΛT°` entire — an
  executability caveat on top of the refinement, not part of it.) -/

/-- **B&dM p.246**, the greedy theorem via bifunctor conditions: with `Q := G(U,V)` for a
    birelator `G` (and `F := G.appl e`), Proposition 9.4's monotonicity witness `hU`
    (`h·G(U,R) ⊆ R·h`) and bound `hV` (`V·H ⊆ H·R`), plus reflexivity of `U` (all at the
    folded `°`, the note's letters), discharge all of `greedy_dp`'s hypotheses — so the
    greedy recursion refines the spec. -/
theorem greedy_dp_of_birelator {G : BiRelator 𝒜} {e : 𝒜}
    (I : InitialAlgebra (G.appl e)) {h : (G.appl e).obj B ⟶ B}
    {T : (G.appl e).obj A ⟶ A} {R : B ⟶ B}
    {U : e ⟶ e} {V : A ⟶ A} (hh : Map h) (htrans : R ≫ R ⊑ R) (hUrefl : Cat.id e ⊑ U)
    (hU : G.map U R ≫ h ⊑ h ≫ R)
    (hV : V ≫ (H T h) ⊑ (H T h) ≫ R) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ est (G.map U V) ≫ (G.appl e).map X ≫ h)
      ⊑ Λ (H T h) ≫ est R := by
  exact greedy_dp (F := G.appl e) I hh (birelator_fixLeft_mono hUrefl hU) htrans
    (birelator_thin_condition (H := (relCata T)° ≫ relCata h) hU hV)

end Freyd.Alg

/-! # Proposition 10.1 (B&dM p.246) in the Set model — the two arms of `F L E X = L+(X×E)`

  "A variation on Proposition 9.1": `AOP.A9_1`'s `est_arm₁_le`/`est_arm₂_le` are the two branches
  of Theorem 10.1's body, and the recursion that runs them separately still refines the spec. -/

/-! # Proposition 10.1 (B&dM p.245) in `Rel(Set)` — Proposition 9.1 with `est(Q)` for `thin(Q)`

  Same four steps as `dp_disjoint_ranges` (`AOP.A9_1`); only step 3 changes, from
  `P(inl)thin(Q₁+Q₂)=thin(Q₁)P(inl)` to `P(inl)est(Q₁+Q₂)=est(Q₁)inl`. -/

namespace Freyd.Alg.RelSet

variable {α β A B : RelSet.{0}}

/-- `P(inl)est(Q₁+Q₂)=est(Q₁)inl`: an `est` of a set of left summands is a left summand. -/
public theorem powerRel_inl_est (Q₁ : α ⟶ α) (Q₂ : β ⟶ β) :
    powerRel (sumCop α β).u₁ ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
      = est Q₁ ≫ (sumCop α β).u₁ := by
  apply hom_ext; intro S t
  constructor
  · rintro ⟨S', hP, hE⟩
    obtain ⟨hS't, hlow⟩ := (est_apply _ _ _).mp hE
    obtain ⟨a, ha, rfl⟩ := hP.2 t hS't
    refine ⟨a, (est_apply _ _ _).mpr ⟨ha, fun a' ha' => ?_⟩, rfl⟩
    obtain ⟨u, rfl, hu⟩ := hP.1 a' ha'
    obtain ⟨c, hc, he⟩ := (ListRel.junc_sum_inl (Q₁ ≫ (sumCop α β).u₁)
      (Q₂ ≫ (sumCop α β).u₂) a (Sum.inl a')).mp (hlow _ hu)
    cases he
    exact hc
  · rintro ⟨a, hE, rfl⟩
    obtain ⟨ha, hlow⟩ := (est_apply _ _ _).mp hE
    refine ⟨fun u => ∃ a', S a' ∧ u = Sum.inl a', ⟨fun t ht => ⟨Sum.inl t, rfl, t, ht, rfl⟩,
      fun u hu => hu⟩, (est_apply _ _ _).mpr ⟨⟨a, ha, rfl⟩, ?_⟩⟩
    rintro u ⟨a', ha', rfl⟩
    exact (ListRel.junc_sum_inl (Q₁ ≫ (sumCop α β).u₁) (Q₂ ≫ (sumCop α β).u₂)
      a (Sum.inl a')).mpr ⟨a', hlow a' ha', rfl⟩

/-- `P(inr)est(Q₁+Q₂)=est(Q₂)inr`: an `est` of a set of right summands is a right summand. -/
public theorem powerRel_inr_est (Q₁ : α ⟶ α) (Q₂ : β ⟶ β) :
    powerRel (sumCop α β).u₂ ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
      = est Q₂ ≫ (sumCop α β).u₂ := by
  apply hom_ext; intro S t
  constructor
  · rintro ⟨S', hP, hE⟩
    obtain ⟨hS't, hlow⟩ := (est_apply _ _ _).mp hE
    obtain ⟨b, hb, rfl⟩ := hP.2 t hS't
    refine ⟨b, (est_apply _ _ _).mpr ⟨hb, fun b' hb' => ?_⟩, rfl⟩
    obtain ⟨u, rfl, hu⟩ := hP.1 b' hb'
    obtain ⟨c, hc, he⟩ := (ListRel.junc_sum_inr (Q₁ ≫ (sumCop α β).u₁)
      (Q₂ ≫ (sumCop α β).u₂) b (Sum.inr b')).mp (hlow _ hu)
    cases he
    exact hc
  · rintro ⟨b, hE, rfl⟩
    obtain ⟨hb, hlow⟩ := (est_apply _ _ _).mp hE
    refine ⟨fun u => ∃ b', S b' ∧ u = Sum.inr b', ⟨fun t ht => ⟨Sum.inr t, rfl, t, ht, rfl⟩,
      fun u hu => hu⟩, (est_apply _ _ _).mpr ⟨⟨b, hb, rfl⟩, ?_⟩⟩
    rintro u ⟨b', hb', rfl⟩
    exact (ListRel.junc_sum_inr (Q₁ ≫ (sumCop α β).u₁) (Q₂ ≫ (sumCop α β).u₂)
      b (Sum.inr b')).mpr ⟨b', hlow b' hb', rfl⟩

/-- The greedy body is empty off `ran V₁ ∪ ran V₂` — an `est` of the empty set is nothing — so it
    splits by where the input lies. -/
public theorem est_ran_split {V₁ : α ⟶ A} {V₂ : β ⟶ A}
    {U₁ : α ⟶ B} {U₂ : β ⟶ B} {Q₁ : α ⟶ α} {Q₂ : β ⟶ β} :
    Λ ((junc (sumCop α β) V₁ V₂)°) ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
        ≫ junc (sumCop α β) U₁ U₂
      = (Freyd.Alg.ran V₁ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂) := by
  apply hom_ext; intro y z
  constructor
  · intro hb
    obtain ⟨S, hS, t, hest, hU⟩ := hb
    have hT : junc (sumCop α β) V₁ V₂ t y := by
      rw [Λ_eq_classifier] at hS
      subst hS
      exact ((est_apply _ _ _).mp hest).1
    cases t with
    | inl a =>
      have ha := (ListRel.junc_sum_inl V₁ V₂ a y).mp hT
      exact Or.inl ⟨y, ⟨rfl, a, ha, ha⟩, S, hS, _, hest, hU⟩
    | inr b =>
      have hb := (ListRel.junc_sum_inr V₁ V₂ b y).mp hT
      exact Or.inr ⟨y, ⟨rfl, b, hb, hb⟩, S, hS, _, hest, hU⟩
  · rintro (⟨y', ⟨rfl, -⟩, h⟩ | ⟨y', ⟨rfl, -⟩, h⟩) <;> exact h

/-- **Proposition 10.1 (B&dM p.245)**, in `Rel(Set)`: when `V₁` and `V₂` have disjoint ranges,
    taking a `Q₁+Q₂`-extreme decomposition `[V₁,V₂]°` and assembling by `[U₁,U₂]` runs, on
    `ran V₁`, `W₁≜Λ(V₁°)est(Q₁)U₁` and, on `ran V₂`, `W₂≜Λ(V₂°)est(Q₂)U₂`.  One `calc` step per
    law, each branch in turn. -/
public theorem greedy_disjoint_ranges {V₁ : α ⟶ A} {V₂ : β ⟶ A}
    {U₁ : α ⟶ B} {U₂ : β ⟶ B} {Q₁ : α ⟶ α} {Q₂ : β ⟶ β} (hdisj : V₂ ≫ V₁° = 𝟘) :
    Λ ((junc (sumCop α β) V₁ V₂)°) ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
        ≫ junc (sumCop α β) U₁ U₂
      = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ est Q₁ ≫ U₁)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ est Q₂ ≫ U₂) :=
  calc Λ ((junc (sumCop α β) V₁ V₂)°) ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
        ≫ junc (sumCop α β) U₁ U₂
      = (Freyd.Alg.ran V₁ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂) :=
        est_ran_split
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ powerRel (sumCop α β).u₁
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂) := by
        rw [← Cat.assoc (Freyd.Alg.ran V₁), ran_Λ_junc_recip_inl hdisj, Cat.assoc, Cat.assoc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ powerRel (sumCop α β).u₁
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ powerRel (sumCop α β).u₂
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂) := by
        rw [← Cat.assoc (Freyd.Alg.ran V₂), ran_Λ_junc_recip_inr hdisj, Cat.assoc, Cat.assoc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ est Q₁ ≫ (sumCop α β).u₁ ≫ junc (sumCop α β) U₁ U₂)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ powerRel (sumCop α β).u₂
            ≫ est (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂) ≫ junc (sumCop α β) U₁ U₂) := by
        rw [← Cat.assoc (powerRel (sumCop α β).u₁), powerRel_inl_est, Cat.assoc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ est Q₁ ≫ (sumCop α β).u₁ ≫ junc (sumCop α β) U₁ U₂)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ est Q₂ ≫ (sumCop α β).u₂
            ≫ junc (sumCop α β) U₁ U₂) := by
        rw [← Cat.assoc (powerRel (sumCop α β).u₂), powerRel_inr_est, Cat.assoc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ est Q₁ ≫ U₁)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ est Q₂ ≫ (sumCop α β).u₂
            ≫ junc (sumCop α β) U₁ U₂) := by
        rw [u₁_junc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ est Q₁ ≫ U₁)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ est Q₂ ≫ U₂) := by
        rw [u₂_junc]

calc_steps greedy_disjoint_ranges

/-- `∪` is the least upper bound: the allegory axioms give `le_union_left`/`le_union_right` but no
    lub, and in `RelSet` it is pointwise `∨`. -/
public theorem union_le {a b : RelSet.{0}} {S T U : a ⟶ b} (hS : S ⊑ U) (hT : T ⊑ U) :
    S ∪ T ⊑ U :=
  le_iff.mpr fun x y h => ((union_apply S T x y) ▸ h).elim (le_iff.mp hS x y) (le_iff.mp hT x y)

/-- `∪` is monotone in both places: the congruence a step on one branch of a union runs under. -/
public theorem union_mono {a b : RelSet.{0}} {S S' T T' : a ⟶ b} (hS : S ⊑ S') (hT : T ⊑ T') :
    S ∪ T ⊑ S' ∪ T' :=
  union_le (le_trans hS (le_union_left _ _)) (le_trans hT (le_union_right _ _))

end Freyd.Alg.RelSet

namespace Freyd.Alg.RelSet.SL

variable {L E : Type} {b c : RelSet.{0}}

/-- **Theorem 10.1 in coproduct form** — the note's @greedy-laws, third row: at `T=[V₁,V₂]`,
    `h=[U₁,U₂]`, `Q=Q₁+Q₂` and `V₂V₁°=⊥`, the greedy recursion split into its two branches
    still refines `H%∋ est(R)`.  `AOP.A10_1.greedy_dp` at the snoc-list functor. -/
public theorem greedy_dp_arms {T : (F L E).obj b ⟶ b} {Q : (F L E).obj b ⟶ (F L E).obj b}
    {U : (F L E).obj c ⟶ c} {R : c ⟶ c}
    (hh : Map U) (hmono : Freyd.Alg.MonoAlg U R) (htrans : R ≫ R ⊑ R)
    (hdisj : ∀ (d : L) (p : b.carrier × E) (y : b.carrier),
      T (Sum.inl d) y → T (Sum.inr p) y → False)
    (hQ : Q ≫ (F L E).map ((relCata T)° ≫ relCata U) ≫ U
        ⊑ (F L E).map ((relCata T)° ≫ relCata U) ≫ U ≫ R) :
    mu (fun X : b ⟶ c =>
        (Λ ((arm₁ T)°) ≫ est (armQ₁ Q) ≫ arm₁ U)
          ∪ (Λ ((arm₂ T)°) ≫ est (armQ₂ Q)
              ≫ rprodMap X (𝟙 (⟨E⟩ : RelSet.{0})) ≫ arm₂ U))
      ⊑ Λ ((relCata T)° ≫ relCata U) ≫ est R :=
  le_trans (mu_le_mu fun X => union_lub (est_arm₁_le (X := X) hdisj) (est_arm₂_le hdisj))
    (greedy_dp (F := F L E) (initial L E) hh hmono htrans hQ)

end Freyd.Alg.RelSet.SL
