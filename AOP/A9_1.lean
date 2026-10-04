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
import AOP.CalcSteps

universe u

namespace Freyd.Alg
open PowerAllegory

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {A B : 𝒜}

/-- **`H≜⦇T⦈°⦇h⦈ : A⟶B`** (B&dM p.220): decompose through the coalgebra `T°` and reassemble
    through the algebra `h`.  It is the arrow the optimisation problem `H%∋ est(R)` is taken of,
    and a name of its own is what lets a picture draw it as one bead. -/
@[expose] public def H [InitialAlgebra F] (T : F.obj A ⟶ A) (h : F.obj B ⟶ B) : A ⟶ B :=
  (relCata T)° ≫ relCata h

/-- **`M≜Λ(H) est(R)`** (B&dM p.220): the problem to be solved — an `R`-extreme answer of `H`. -/
@[expose] public def M [InitialAlgebra F] (T : F.obj A ⟶ A) (h : F.obj B ⟶ B) (R : B ⟶ B) : A ⟶ B :=
  Λ (H T h) ≫ est R

/-- **`T°F(H)h = H`**: `H` solves its own recursion — `hylo_fixed` read at `H≜⦇T⦈°⦇h⦈`, stated
    on the name so a picture draws `H` as one arrow. -/
public theorem H_fixed (I : InitialAlgebra F) (T : F.obj A ⟶ A)
    (h : F.obj B ⟶ B) : T° ≫ F.map (H T h) ≫ h = H T h :=
  hylo_fixed I h T

/-- **The thinning condition** of Theorem 9.2 (B&dM p.222): `QF(H)h ⊑ F(H)hR` — thinning the
    decompositions by `Q` before solving them only moves the answer up `R`. -/
@[expose] public def ThinCondition [InitialAlgebra F] (T : F.obj A ⟶ A) (h : F.obj B ⟶ B)
    (R : B ⟶ B) (Q : F.obj A ⟶ F.obj A) : Prop :=
  Q ≫ F.map (H T h) ≫ h ⊑ F.map (H T h) ≫ h ≫ R

/-! ## Theorem 9.1 (B&dM pp. 220-221) -/

/-- `H° = h°F(H°)T`: the fixed point `T°F(H)h = H`, conversed. -/
public theorem recip_of_fixed [InitialAlgebra F] (T : F.obj A ⟶ A) (h : F.obj B ⟶ B) :
    (H T h)° = h° ≫ F.map ((H T h)°) ≫ T := by
  have h1 : (T° ≫ F.map (H T h) ≫ h)° = h° ≫ F.map ((H T h)°) ≫ T := by
    rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip,
      ← Relator.preservesRecip_of_tabular F (H T h), Cat.assoc]
  rw [← h1, H_fixed inferInstance T h]

/-- `TΛ(T°) ⊑ ∈`: the cancellation of the transpose `Λ(T°)`, conversed. -/
public theorem comp_Λ_recip_le_recip_eps {C : 𝒜} (T : C ⟶ A) : T ≫ Λ (T°) ⊑ (∋ C)° := by
  simpa only [Allegory.recip_recip] using recip_comp_Λ_le_recip_eps (T°)

/-- **(9.2)** (B&dM p.220): `min R·P(h·FM)·ΛT° ⊆ H`, mirrored — with `M ≜ Λ(H) est(R)`, taking
    the input apart every way `T` allows, solving each part by `M` and keeping an optimum stays
    inside `H`.  One `calc` step per hint of the book. -/
public theorem dynamic_programming_lower [InitialAlgebra F] {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B} :
    Λ (T°) ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R ⊑ H T h :=
  calc Λ (T°) ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R
        ⊑ Λ (T°) ≫ ∋ (F.obj A) ≫ F.map (Λ (H T h) ≫ est R) ≫ h :=
        comp_mono_left _ (powerRel_comp_est_le_eps _ R)
      _ = T° ≫ F.map (Λ (H T h) ≫ est R) ≫ h := by rw [← Cat.assoc (Λ (T°)) (∋ (F.obj A)) _, Λ_eps_eq']
      _ ⊑ T° ≫ F.map (H T h) ≫ h := comp_mono_left _ (comp_mono_right (F.map_mono (Λ_comp_est_le (H T h) R)) h)
      _ = H T h := H_fixed inferInstance T h

calc_steps dynamic_programming_lower

/-- **(9.3)** (B&dM p.221): `min R·P(h·FM)·ΛT°·H° ⊆ R`, mirrored — with `M ≜ Λ(H) est(R)`,
    whatever the dynamic-programming step returns is `R`-related to everything `H` returns from
    the same input.  One `calc` step per hint of the book. -/
public theorem dynamic_programming_upper [InitialAlgebra F] {h : F.obj B ⟶ B}
    {T : F.obj A ⟶ A} {R : B ⟶ B}
    (hh : Map h) (hmono : MonoAlg h R°) (htrans : R° ≫ R° ⊑ R°) :
    (H T h)° ≫ Λ (T°) ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R ⊑ R° :=
  calc (H T h)° ≫ Λ (T°) ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R
        ⊑ (H T h)° ≫ Λ (T°) ≫ ((∋ (F.obj A))° \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°)) :=
        comp_mono_left _ (comp_mono_left _ (powerRel_comp_est_le_div _ R))
      _ = h° ≫ F.map ((H T h)°) ≫ T ≫ Λ (T°) ≫ ((∋ (F.obj A))° \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°)) :=
        id ((congrArg (· ≫ _) (recip_of_fixed T h)).trans
          ((Cat.assoc _ _ _).trans (congrArg (_ ≫ ·) (Cat.assoc _ _ _))))
      _ ⊑ h° ≫ F.map ((H T h)°) ≫ (∋ (F.obj A))° ≫ ((∋ (F.obj A))° \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°)) :=
        comp_mono_left _ (comp_mono_left _ (by
        simpa only [Cat.assoc] using
          comp_mono_right (comp_Λ_recip_le_recip_eps T) ((∋ (F.obj A))° \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°))))
      _ ⊑ h° ≫ F.map ((H T h)°) ≫ (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R° :=
        comp_mono_left _ (comp_mono_left _ (leftDiv_comp_le _ _))
      _ = h° ≫ F.map ((H T h)° ≫ Λ (H T h) ≫ est R) ≫ h ≫ R° := by
        rw [F.map_comp ((H T h)°) (Λ (H T h) ≫ est R)]
        repeat rw [Cat.assoc]
      _ ⊑ h° ≫ F.map (R°) ≫ h ≫ R° :=
        comp_mono_left _ (comp_mono_right (F.map_mono (recip_comp_Λ_comp_est_le (H T h) R)) _)
      _ ⊑ R° ≫ R° := by simpa only [Cat.assoc] using comp_mono_right ((monoAlg_iff_conj hh).mp hmono) (R°)
      _ ⊑ R° := htrans

calc_steps dynamic_programming_upper

/-- **Core of Theorem 9.1**: `M = min R°·ΛH` (mirrored `Λ H ≫ est R`) is a PREFIXED point of
    the dynamic-programming body, at `H≜⦇T⦈°⦇h⦈`.  The two inclusions (9.2) and (9.3) of the book's
    proof are exactly the components of `min`'s universal property (`le_Λ_comp_est_iff`). -/
public theorem dp_prefixed [InitialAlgebra F] {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
    {R : B ⟶ B}
    (hh : Map h) (hmono : MonoAlg h R°) (htrans : R° ≫ R° ⊑ R°) :
    Λ (T°) ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R ⊑ Λ (H T h) ≫ est R :=
  le_Λ_comp_est_iff.mpr ⟨dynamic_programming_lower, dynamic_programming_upper hh hmono htrans⟩

/-- **Theorem 9.1 (B&dM p.220)**, the basic theorem of DYNAMIC PROGRAMMING:
    `(μX : min R°·P(h·FX)·ΛT°) ⊆ min R°·ΛH` for `H = ⦇h⦈·⦇T⦈°`, mirrored — if the algebra `h`
    is monotonic on the transitive `R°`, then decomposing the input in all possible ways
    (`ΛT°`), solving subproblems recursively (`P(h·FX)`) and keeping an optimum of the partial
    results (`min R°`) refines "generate everything, then pick a global optimum".
    By Knaster–Tarski (`Sup_le`'s lower-bound half) via `dp_prefixed`. -/
public theorem dynamic_programming (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B}
    (hh : Map h) (hmono : MonoAlg h R°) (htrans : R° ≫ R° ⊑ R°) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _ (dp_prefixed hh hmono htrans))

/-! ## Theorem 9.2 (B&dM p.221) — thinning dynamic programming

  Thinning at every unfold step (`ΛT° ≫ thin Q`), before recursing and taking the `R`-minimum,
  still refines "generate everything, then minimize" — PROVIDED the thinning preorder `Q`
  interacts correctly with the algebra `h` through the current best guess `H` (hypothesis
  `hQ` below).  B&dM state the theorem for `Q` a preorder on `F(dom H)`; the refinement itself
  needs no reflexivity/transitivity of `Q` beyond `hQ`, so we drop those hypotheses here (they
  only matter for `dynamic_programming_of_thin`, Ex 9.1, which recovers Theorem 9.1 at `Q :=
  id`, where reflexivity IS needed to discharge `hQ`). -/

/-! ### Exercise 9.3: the proof of Theorem 9.1 with `thin(Q)` added, one `calc` step per hint

  `M≜Λ(H) est(R)` throughout: (9.2) `body(M)⊑H` and (9.3) `H°body(M)⊑R°`. -/

/-- The thinning condition `QF(H)h ⊑ F(H)hR`, conversed: `h°F(H°)Q° ⊑ R°h°F(H°)`. -/
public theorem recip_thin_condition [InitialAlgebra F] {T : F.obj A ⟶ A} {h : F.obj B ⟶ B}
    {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} (hQ : ThinCondition T h R Q) :
    h° ≫ F.map ((H T h)°) ≫ Q° ⊑ R° ≫ h° ≫ F.map ((H T h)°) := by
  have hrm := recip_mono (show Q ≫ F.map (H T h) ≫ h ⊑ F.map (H T h) ≫ h ≫ R from hQ)
  have eL : (Q ≫ F.map (H T h) ≫ h)° = h° ≫ F.map ((H T h)°) ≫ Q° := by
    rw [Allegory.recip_comp, Allegory.recip_comp, ← Relator.preservesRecip_of_tabular F (H T h),
      Cat.assoc]
  have eR : (F.map (H T h) ≫ h ≫ R)° = R° ≫ h° ≫ F.map ((H T h)°) := by
    rw [Allegory.recip_comp, Allegory.recip_comp, ← Relator.preservesRecip_of_tabular F (H T h),
      Cat.assoc]
  rwa [eL, eR] at hrm

/-- `h` monotonic on `R`, conversed and shunted at the map `h`: `h°F(R°)h ⊑ R°`. -/
public theorem recip_conj_le_of_monoAlg {h : F.obj B ⟶ B} {R : B ⟶ B} (hh : Map h)
    (hmono : MonoAlg h R) : h° ≫ F.map (R°) ≫ h ⊑ R° :=
  (monoAlg_iff_conj hh).mp ((monoAlg_recip_iff hh (Relator.preservesRecip_of_tabular F)).mp hmono)

/-- **(9.2) with thinning**: `min R·P(h·FM)·thin Q·ΛT° ⊆ H`, mirrored. -/
public theorem dynamic_programming_thin_lower [InitialAlgebra F] {h : F.obj B ⟶ B}
    {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} :
    Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R ⊑ H T h :=
  calc Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R
        ⊑ Λ (T°) ≫ thinRel Q ≫ ∋ (F.obj A) ≫ F.map (Λ (H T h) ≫ est R) ≫ h :=
        comp_mono_left _ (comp_mono_left _ (powerRel_comp_est_le_eps _ R))
      _ ⊑ Λ (T°) ≫ ∋ (F.obj A) ≫ F.map (Λ (H T h) ≫ est R) ≫ h :=
        comp_mono_left _ (by
        simpa only [Cat.assoc] using
          comp_mono_right (thinRel_comp_eps_le Q) (F.map (Λ (H T h) ≫ est R) ≫ h))
      _ = T° ≫ F.map (Λ (H T h) ≫ est R) ≫ h := by rw [← Cat.assoc (Λ (T°)) (∋ (F.obj A)) _, Λ_eps_eq']
      _ ⊑ T° ≫ F.map (H T h) ≫ h := comp_mono_left _ (comp_mono_right (F.map_mono (Λ_comp_est_le (H T h) R)) h)
      _ = H T h := H_fixed inferInstance T h

calc_steps dynamic_programming_thin_lower

/-- **(9.3) with thinning**: `min R·P(h·FM)·thin Q·ΛT°·H° ⊆ R`, mirrored. -/
public theorem dynamic_programming_thin_upper [InitialAlgebra F] {h : F.obj B ⟶ B}
    {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A}
    (hh : Map h) (hmono : MonoAlg h R°) (htrans : R° ≫ R° ⊑ R°)
    (hQ : ThinCondition T h R Q) :
    (H T h)° ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R ⊑ R° :=
  calc (H T h)° ≫ Λ (T°) ≫ thinRel Q ≫ powerRel (F.map (Λ (H T h) ≫ est R) ≫ h) ≫ est R
        ⊑ (H T h)° ≫ Λ (T°) ≫ thinRel Q ≫ (((∋ (F.obj A))°) \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°)) :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_left _ (powerRel_comp_est_le_div _ R)))
      _ = h° ≫ F.map ((H T h)°) ≫ T ≫ Λ (T°) ≫ thinRel Q
            ≫ (((∋ (F.obj A))°) \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°)) :=
        id ((congrArg (· ≫ _) (recip_of_fixed T h)).trans
          ((Cat.assoc _ _ _).trans (congrArg (_ ≫ ·) (Cat.assoc _ _ _))))
      _ ⊑ h° ≫ F.map ((H T h)°) ≫ (∋ (F.obj A))° ≫ thinRel Q
            ≫ (((∋ (F.obj A))°) \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°)) :=
        comp_mono_left _ (comp_mono_left _ (by
        simpa only [Cat.assoc] using
          comp_mono_right (comp_Λ_recip_le_recip_eps T)
            (thinRel Q ≫ (((∋ (F.obj A))°) \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°)))))
      _ ⊑ h° ≫ F.map ((H T h)°) ≫ Q° ≫ (∋ (F.obj A))°
            ≫ (((∋ (F.obj A))°) \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°)) :=
        comp_mono_left _ (comp_mono_left _ (by
        simpa only [Cat.assoc] using
          comp_mono_right (recip_eps_comp_thinRel_le Q)
            (((∋ (F.obj A))°) \ ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°))))
      _ ⊑ h° ≫ F.map ((H T h)°) ≫ Q° ≫ F.map (Λ (H T h) ≫ est R) ≫ h ≫ R° :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_left _ (by
        simpa only [Cat.assoc] using
          leftDiv_comp_le ((∋ (F.obj A))°) ((F.map (Λ (H T h) ≫ est R) ≫ h) ≫ R°))))
      _ ⊑ R° ≫ h° ≫ F.map ((H T h)°) ≫ F.map (Λ (H T h) ≫ est R) ≫ h ≫ R° := by
        simpa only [Cat.assoc] using
          comp_mono_right (recip_thin_condition hQ) (F.map (Λ (H T h) ≫ est R) ≫ h ≫ R°)
      _ = R° ≫ h° ≫ F.map ((H T h)° ≫ Λ (H T h) ≫ est R) ≫ h ≫ R° := by
        rw [F.map_comp ((H T h)°) (Λ (H T h) ≫ est R)]
        repeat rw [Cat.assoc]
      _ ⊑ R° ≫ h° ≫ F.map (R°) ≫ h ≫ R° :=
        comp_mono_left _ (comp_mono_left _ (comp_mono_right (F.map_mono (recip_comp_Λ_comp_est_le (H T h) R)) _))
      _ ⊑ R° ≫ R° ≫ R° := comp_mono_left _ (by
        simpa only [Cat.assoc] using
          comp_mono_right ((monoAlg_iff_conj hh).mp hmono) R°)
      _ ⊑ R° ≫ R° := comp_mono_left R° htrans
      _ ⊑ R° := htrans

calc_steps dynamic_programming_thin_upper

/-- **(9.1) with thinning**: at `X≜Λ(H) est(R)` the thinning body is below `X` — the prefixed
    point Knaster–Tarski consumes, with the note's bead `X` as a binder of its own.  The universal
    property of `est` splits it into (9.2) and (9.3). -/
public theorem dynamic_programming_thin_prefixed (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A}
    (hh : Map h) (hmono : MonoAlg h R°) (htrans : R° ≫ R° ⊑ R°)
    (hQ : ThinCondition T h R Q) {X : A ⟶ B} (hX : X = Λ (H T h) ≫ est R) :
    Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R ⊑ Λ (H T h) ≫ est R := by
  subst hX
  exact le_Λ_comp_est_iff.mpr ⟨dynamic_programming_thin_lower, dynamic_programming_thin_upper hh hmono htrans hQ⟩

/-- **Theorem 9.2 (B&dM p.221)**, thinning dynamic programming: thinning by a preorder `Q` at
    every unfold step, before minimizing over `R°`, refines minimizing the plain hylomorphism
    recursion — provided `Q` interacts correctly with `H := ⦇h⦈·⦇T⦈°` and `h` (hypothesis
    `hQ`).  Ex 9.1 (`dynamic_programming_of_thin`) recovers Theorem 9.1 as the instance
    `Q := id`.  Knaster–Tarski reduces it to (9.1) `body(M)⊑M`, which the universal property of
    `est` splits into (9.2) and (9.3). -/
public theorem dynamic_programming_thin (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A}
    (hh : Map h) (hmono : MonoAlg h R°) (htrans : R° ≫ R° ⊑ R°)
    (hQ : ThinCondition T h R Q) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  mu_le (dynamic_programming_thin_prefixed I hh hmono htrans hQ rfl)

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
    ThinCondition T h R (𝟙 (F.obj A)) := by
  unfold ThinCondition
  rw [Cat.id_comp]
  have hid : Cat.id B ⊑ R := by
    have h1 := recip_mono hrefl
    rwa [recip_id, Allegory.recip_recip] at h1
  have step := comp_mono_left (F.map (H T h) ≫ h) hid
  rw [Cat.comp_id, Cat.assoc] at step
  exact step

theorem dynamic_programming_of_thin (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B}
    (hh : Map h) (hmono : MonoAlg h R°) (htrans : R° ≫ R° ⊑ R°) (hrefl : Cat.id B ⊑ R°) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  le_trans mu_le_mu_thinRel_id (dynamic_programming_thin I hh hmono htrans (thin_condition_of_refl I hrefl))

/-! ## Proposition 9.2 (B&dM p.222) — checking monotonicity via cost functions -/

/-- A relation `R ≜ f S f°` pulled back along a map `f` is reached from `f S`: `R f ⊑ f S`, because
    `f` is simple (`f°f ⊑ 𝟙`). -/
public theorem conj_comp_map_le {C : 𝒜} {f : A ⟶ C} {S : C ⟶ C} {R : A ⟶ A} (hf : Map f)
    (hR : R = f ≫ S ≫ f°) : R ≫ f ⊑ f ≫ S := by
  have e := comp_mono_left f (comp_mono_left S hf.2)
  rw [Cat.comp_id] at e
  rw [hR]; simpa only [Cat.assoc] using e

/-- Proposition 9.2 (B&dM p.222), the book's chain after shunting at `cost`: one `calc` step per
    hint — the assumption on `cost`, `R cost ⊑ cost ≤` under the functor `F`, `k` monotonic
    on `≤`, and the assumption on `cost` again. -/
public theorem monoAlg_of_cost_shunted {C : 𝒜} {h : F.obj A ⟶ A} {R : A ⟶ A} {cost : A ⟶ C}
    {«≤» : C ⟶ C} {k : F.obj C ⟶ C} (hcost : Map cost) (hR : R = cost ≫ «≤» ≫ cost°)
    (hch : h ≫ cost = F.map cost ≫ k) (hk : F.map «≤» ≫ k ⊑ k ≫ «≤») :
    F.map R ≫ h ≫ cost ⊑ h ≫ cost ≫ «≤» :=
  calc F.map R ≫ h ≫ cost = F.map R ≫ F.map cost ≫ k := congrArg (F.map R ≫ ·) hch
      _ ⊑ F.map cost ≫ F.map «≤» ≫ k := by
        simpa only [← Cat.assoc, ← F.map_comp] using comp_mono_right (F.map_mono (conj_comp_map_le hcost hR)) k
      _ ⊑ F.map cost ≫ k ≫ «≤» := comp_mono_left _ hk
      _ = h ≫ cost ≫ «≤» := by rw [← Cat.assoc, ← hch, Cat.assoc]

calc_steps monoAlg_of_cost_shunted

/-- **Proposition 9.2 (B&dM p.222)**: an algebra `h` is monotonic on the order `R := cost·leq·cost°`
    (induced on `a` by pulling the order `leq` on `c` back along a "cost" function) whenever `h`
    followed by `cost` factors as `F.map cost` followed by an algebra `k` that is itself
    monotonic on `leq`.  The definition of `R` and shunting reduce `F(R)h ⊑ hR` to
    `F(R)h cost ⊑ h cost leq`, which `monoAlg_of_cost_shunted` proves. -/
public theorem monoAlg_of_cost {C : 𝒜} {h : F.obj A ⟶ A} {R : A ⟶ A} {cost : A ⟶ C}
    {«≤» : C ⟶ C} {k : F.obj C ⟶ C} (hcost : Map cost) (hR : R = cost ≫ «≤» ≫ cost°)
    (hch : h ≫ cost = F.map cost ≫ k) (hk : F.map «≤» ≫ k ⊑ k ≫ «≤») :
    MonoAlg h R := by
  show F.map R ≫ h ⊑ h ≫ R
  have hsh : h ≫ R = (h ≫ cost ≫ «≤») ≫ cost° := by rw [hR]; simp only [Cat.assoc]
  rw [hsh]
  apply (map_shunt_right hcost _ _).mp
  rw [Cat.assoc]
  exact monoAlg_of_cost_shunted hcost hR hch hk

/-! ## Ex 9.4 (B&dM p.222) — a universal but useless thinning relation -/

/-- **Ex 9.4**: `Q := F(M·R·M°)` (mirrored `F.map (M ≫ R ≫ M°)`) ALWAYS discharges Theorem
    9.2's `hQ` hypothesis, given only `M ⊑ H` and `H°·M ⊑ R` — i.e. it is a universal choice of
    thinning relation.  Instantiating `M := ΛH·min R` (the optimum being computed) shows the
    hypothesis is always satisfiable in principle, but the resulting `Q` mentions the very
    optimum `dynamic_programming_thin` is trying to compute — useless for actually EXECUTING
    the recursion (only for justifying that some valid `Q` exists). -/
theorem thin_condition_of_optimum {h : F.obj A ⟶ A}
    {R : A ⟶ A} {H M : B ⟶ A}
    (hh : Map h) (hmono : MonoAlg h R) (htrans : R ≫ R ⊑ R)
    (hMH : M ⊑ H) (hHMR : H° ≫ M ⊑ R) :
    (F.map (M ≫ R ≫ M°))° ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R° := by
  have erecip : (M ≫ R ≫ M°)° = M ≫ R° ≫ M° := by
    rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
  have hrecipmap : (F.map (M ≫ R ≫ M°))° = F.map (M ≫ R° ≫ M°) := by
    rw [← Relator.preservesRecip_of_tabular F (M ≫ R ≫ M°), erecip]
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
  have hmonoR' : F.map R° ≫ h ⊑ h ≫ R° := (monoAlg_recip_iff hh (Relator.preservesRecip_of_tabular F)).mp hmono
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

/-- **Proposition 9.3 (B&dM p.223)**, monotonicity in context: given a cost function `cost`
    bundled with a simple context relation `S` via a chosen product `P`, and an algebra `k`
    (on the bundle) monotonic on `leq × 𝟙` in the sense of `hk`, the algebra `h` is monotonic
    on `R := cost·leq·cost°` RESTRICTED to `S`'s domain of definition (`R ∩ S·S°`).  The book's
    chain, one `calc` step per hint: `cost` entire, products, the assumption on `cost`, `⟨cost,S⟩`
    simple, products and functors, the assumption on `k`, the assumption on `cost` read backwards. -/
public theorem monoAlg_in_context {C : 𝒜} {h : F.obj A ⟶ A} {R : A ⟶ A} {cost : A ⟶ C}
    {S : A ⟶ B} {P : RelProd C B} {«≤» : C ⟶ C} {k : F.obj P.p ⟶ C}
    (hcost : Map cost) (hS : Simple S) (hR : R = cost ≫ «≤» ≫ cost°)
    (hch : h ≫ cost = F.map (P.pair cost S) ≫ k)
    (hk : F.map (prodMap P P «≤» (𝟙 B)) ≫ k ⊑ k ≫ «≤») :
    F.map (R ∩ (S ≫ S°)) ≫ h ⊑ h ≫ R :=
  calc F.map (R ∩ (S ≫ S°)) ≫ h = F.map (R ∩ (S ≫ S°)) ≫ h ≫ 𝟙 A := by rw [Cat.comp_id]
    _ ⊑ F.map (R ∩ (S ≫ S°)) ≫ h ≫ cost ≫ cost° :=
        comp_mono_left _ (comp_mono_left h (map_entire_le hcost))
    _ = F.map ((cost ≫ «≤» ≫ cost°) ∩ (S ≫ S°)) ≫ h ≫ cost ≫ cost° := by rw [hR]
    _ = F.map (P.pair (cost ≫ «≤») S ≫ (P.pair cost S)°) ≫ h ≫ cost ≫ cost° := by
        rw [P.pair_recip_pair, Cat.assoc cost «≤» cost°]
    _ = F.map (P.pair (cost ≫ «≤») S ≫ (P.pair cost S)°) ≫ F.map (P.pair cost S) ≫ k ≫ cost° := by
        rw [← Cat.assoc h cost, hch, Cat.assoc]
    _ = F.map (P.pair (cost ≫ «≤») S ≫ (P.pair cost S)° ≫ P.pair cost S) ≫ k ≫ cost° := by
        rw [← Cat.assoc (F.map _) (F.map _), ← F.map_comp, Cat.assoc]
    _ ⊑ F.map (P.pair (cost ≫ «≤») S ≫ 𝟙 P.p) ≫ k ≫ cost° :=
        comp_mono_right (F.map_mono (comp_mono_left _ (tabulation_simple_of_simple P.tab hcost.2 hS))) _
    _ = F.map (P.pair (cost ≫ «≤») S) ≫ k ≫ cost° := by rw [Cat.comp_id]
    _ = F.map (P.pair cost S ≫ prodMap P P «≤» (𝟙 B)) ≫ k ≫ cost° := by
        rw [RelProd.pair_prodMap_fst (P := P) (Q := P) cost S «≤»]
    _ = F.map (P.pair cost S) ≫ F.map (prodMap P P «≤» (𝟙 B)) ≫ k ≫ cost° := by
        rw [F.map_comp, Cat.assoc]
    _ ⊑ F.map (P.pair cost S) ≫ k ≫ «≤» ≫ cost° :=
        comp_mono_left _ (by simpa only [Cat.assoc] using comp_mono_right hk cost°)
    _ = h ≫ cost ≫ «≤» ≫ cost° := by rw [← Cat.assoc (F.map _) k, ← hch, Cat.assoc]
    _ = h ≫ R := by rw [hR]

calc_steps monoAlg_in_context

end Prop9_3

/-! ## Proposition 9.4 (B&dM pp.223-224) — bifunctor conditions

  Back in the file's ambient `TabularUnitaryUnguardedPowerLCDA` setting.  B&dM's monotonicity/thinning
  conditions for Theorems 9.1/9.2 are often checked through a BIFUNCTOR `G` (e.g. `G(X,Y) :=
  X × Y` or a coproduct) with the algebra `h` living over `G` applied to a distinguished
  extra argument `e` — Prop 9.4 packages sufficient conditions on `G` alone.  `G` is the
  binary relator `BiRelator` of `AOP.A5_5_TypeFunctor`, and fixing its left argument at `e` is
  its partial application `G.appl e`. -/

/-- **Proposition 9.4(i) (B&dM p.223)**, monotonicity: if `h` is monotonic for `G` at some `U`
    refined from below by `id_e` (`hUrefl`), then `h` is monotonic (in the ordinary
    `MonoAlg` sense) for the fixed-left relator `G.appl e`. -/
public theorem birelator_fixLeft_mono {G : BiRelator 𝒜} {e : 𝒜} {h : G.obj e A ⟶ A} {R : A ⟶ A}
    {U : e ⟶ e} (hUrefl : Cat.id e ⊑ U) (hU : G.map U R ≫ h ⊑ h ≫ R) :
    G.map (Cat.id e) R ≫ h ⊑ h ≫ R :=
  le_trans (comp_mono_right (G.map_mono hUrefl (le_refl R)) h) hU

/-- A map `h` monotonic for `G` at `(U, R)` is monotonic at `(U°, R°)` — conjugate, then
    shunt back across the map `h` (the birelator analogue of `monotonicAlg_recip_iff`). -/
public theorem birelator_mono_recip {G : BiRelator 𝒜} {e : 𝒜}
    {h : G.obj e A ⟶ A} {R : A ⟶ A} {U : e ⟶ e} (hh : Map h)
    (hU : G.map U R ≫ h ⊑ h ≫ R) : G.map U° R° ≫ h ⊑ h ≫ R° := by
  have hUrecip : h° ≫ G.map U° R° ⊑ R° ≫ h° := by
    have hrm := recip_mono hU
    have eL : (G.map U R ≫ h)° = h° ≫ G.map U° R° := by
      rw [Allegory.recip_comp, ← BiRelator.preservesRecip_of_tabular G U R]
    have eRr : (h ≫ R)° = R° ≫ h° := Allegory.recip_comp h R
    rwa [eL, eRr] at hrm
  have hpost : (h° ≫ G.map U° R°) ≫ h ⊑ (R° ≫ h°) ≫ h := comp_mono_right hUrecip h
  have eLassoc : (h° ≫ G.map U° R°) ≫ h = h° ≫ (G.map U° R° ≫ h) := by rw [Cat.assoc]
  have eRassoc : (R° ≫ h°) ≫ h = R° ≫ (h° ≫ h) := by rw [Cat.assoc]
  rw [eLassoc, eRassoc] at hpost
  have hRRcollapse : R° ≫ (h° ≫ h) ⊑ R° ≫ Cat.id A := comp_mono_left R° hh.2
  rw [Cat.comp_id] at hRRcollapse
  exact (map_shunt_left hh _ _).mp (le_trans hpost hRRcollapse)

/-- **Proposition 9.4(ii) (B&dM pp.223-224)**, the thinning condition: given the monotonicity
    witness `hU` and the bound `hV : V·H ⊑ H·R` (the note's letters, at the folded `°`), the
    thinning relation `Q := G(U,V)` discharges `dynamic_programming_thin`'s hypothesis `hQ`
    for the fixed-left relator `G.appl e` — the book's chain, one `calc` step per law. -/
public theorem birelator_thin_condition {G : BiRelator 𝒜} {e w : 𝒜}
    {h : G.obj e A ⟶ A} {H : w ⟶ A} {R : A ⟶ A} {U : e ⟶ e} {V : w ⟶ w}
    (hU : G.map U R ≫ h ⊑ h ≫ R) (hV : V ≫ H ⊑ H ≫ R) :
    G.map U V ≫ G.map (𝟙 e) H ≫ h ⊑ G.map (𝟙 e) H ≫ h ≫ R :=
  calc G.map U V ≫ G.map (𝟙 e) H ≫ h
        = G.map (U ≫ 𝟙 e) (V ≫ H) ≫ h := by rw [← Cat.assoc, ← G.map_comp]
      _ = G.map U (V ≫ H) ≫ h := by rw [Cat.comp_id]
      _ ⊑ G.map U (H ≫ R) ≫ h := comp_mono_right (G.map_mono (le_refl U) hV) h
      _ = G.map (𝟙 e ≫ U) (H ≫ R) ≫ h := by rw [Cat.id_comp]
      _ = G.map (𝟙 e) H ≫ G.map U R ≫ h := by rw [G.map_comp, Cat.assoc]
      _ ⊑ G.map (𝟙 e) H ≫ h ≫ R := comp_mono_left _ hU

calc_steps birelator_thin_condition


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
theorem dp_thin_prefixed_context {h : F.obj B ⟶ B} {T : F.obj A ⟶ A}
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
        repeat rw [Cat.assoc]
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
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← Relator.preservesRecip_of_tabular F H, Cat.assoc]
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
        rw [Allegory.recip_comp, Allegory.recip_comp, ← Relator.preservesRecip_of_tabular F H, Cat.assoc]
      have eR : (F.map H ≫ h ≫ R)° = R° ≫ h° ≫ F.map (H°) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, ← Relator.preservesRecip_of_tabular F H, Cat.assoc]
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
    -- the context collapse, from `hctx1` instead of `MonoAlg h R°`
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
public theorem dynamic_programming_thin_context (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} {Q : F.obj A ⟶ F.obj A} (hh : Map h)
    (hctx1 : F.map (R° ∩ ((H T h)° ≫ H T h)) ≫ h
        ⊑ h ≫ R°)
    (htrans : R° ≫ R° ⊑ R°)
    (hctx2 : ThinCondition T h R (Q ∩ (T ≫ T°))) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ thinRel Q ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _ (dp_thin_prefixed_context hh hctx1 htrans (hylo_fixed I h T) hctx2))

/-- **Theorem 9.1 in context**: the plain (un-thinned) dynamic-programming recursion refines the
    optimisation spec when `h` is monotonic only ON `H`'s domain of definition, `R° ∩ (H°·H)` —
    the form B&dM's §9.3 optimal-bracketing derivation uses, where only trees with the same
    flattening are ever compared.  Ex 9.2 (`dynamic_programming_thin_context`) at `Q := id`. -/
public theorem dynamic_programming_context (I : InitialAlgebra F)
    {h : F.obj B ⟶ B} {T : F.obj A ⟶ A} {R : B ⟶ B} (hh : Map h)
    (hctx1 : F.map (R° ∩ ((H T h)° ≫ H T h)) ≫ h
        ⊑ h ≫ R°)
    (htrans : R° ≫ R° ⊑ R°) (hrefl : Cat.id B ⊑ R°) :
    mu (fun X : A ⟶ B => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ (H T h) ≫ est R :=
  le_trans mu_le_mu_thinRel_id
    (dynamic_programming_thin_context I hh hctx1 htrans
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
open PowerAllegory

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
    thinRel (𝟙 A) = 𝟙 (P A) := by
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
    (hh : Map U) (hmono : MonoAlg U R°) (htrans : R° ≫ R° ⊑ R°)
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
    (dynamic_programming_thin (F := F L W) (initial L W) hh hmono htrans hQ)

/-! ## Proposition 9.1 (B&dM p.222) along Exercise 9.5

  `T=[V₁,V₂] : α+β⟶A`, `[U₁,U₂] : α+β⟶B`, `Q₁+Q₂`, and `hdisj` says `V₁` and `V₂` have disjoint
  ranges.  The book's conclusion `(ran V₁ → W₁, W₂)` is written `ran(V₁)W₁ ∪ ran(V₂)W₂`: off
  `ran V₁ ∪ ran V₂` both are empty, since there `Λ(T°)` is the empty set and `est` of it is
  nothing. -/

section Prop91

variable {α β A B : RelSet.{0}}

/-- **Ex 9.5**, second claim, first branch: on `ran V₁` the transpose of `[V₁,V₂]°` is
    `Λ(V₁°)` followed by `P(inl)` — no candidate comes from the `β` summand. -/
public theorem _root_.Freyd.Alg.RelSet.ran_Λ_junc_recip_inl {V₁ : α ⟶ A} {V₂ : β ⟶ A}
    (hdisj : V₂ ≫ V₁° = 𝟘) :
    Freyd.Alg.ran V₁ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
      = Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ powerRel (sumCop α β).u₁ := by
  -- `V₂V₁°=𝟘` read at a point: no `y` is reached by both
  have hdisj : ∀ a b y, V₁ a y → V₂ b y → False := fun a b y h1 h2 =>
    cast (congrFun (congrFun hdisj b) a) ⟨y, h2, h1⟩
  apply hom_ext; intro y S
  rw [Λ_eq_classifier, Λ_eq_classifier]
  constructor
  · rintro ⟨y', ⟨rfl, a₀, ha₀, -⟩, hS⟩
    subst hS
    refine ⟨y, ⟨rfl, a₀, ha₀, ha₀⟩, fun a => V₁ a y, rfl, ?_, ?_⟩
    · intro a ha; exact ⟨Sum.inl a, rfl, (ListRel.junc_sum_inl V₁ V₂ a y).mpr ha⟩
    · rintro (a | b) hu
      · exact ⟨a, (ListRel.junc_sum_inl V₁ V₂ a y).mp hu, rfl⟩
      · exact (hdisj a₀ b y ha₀ ((ListRel.junc_sum_inr V₁ V₂ b y).mp hu)).elim
  · rintro ⟨y', ⟨rfl, a₀, ha₀, -⟩, S', hS', hP⟩
    subst hS'
    refine ⟨y, ⟨rfl, a₀, ha₀, ha₀⟩, ?_⟩
    show S = fun w => junc (sumCop α β) V₁ V₂ w y
    funext w
    refine propext (Iff.symm ?_)
    cases w with
    | inl a =>
      rw [ListRel.junc_sum_inl]
      refine ⟨fun ha => ?_, fun hs => ?_⟩
      · obtain ⟨u, rfl, hu⟩ := hP.1 a ha; exact hu
      · obtain ⟨a', ha', he⟩ := hP.2 _ hs
        obtain rfl : a = a' := Sum.inl.inj he
        exact ha'
    | inr b =>
      rw [ListRel.junc_sum_inr]
      refine ⟨fun hb => (hdisj a₀ b y ha₀ hb).elim, fun hs => ?_⟩
      obtain ⟨a', -, he⟩ := hP.2 _ hs
      exact nomatch he

/-- **Ex 9.5**, second claim, second branch: on `ran V₂` it is `Λ(V₂°)` followed by `P(inr)`. -/
public theorem _root_.Freyd.Alg.RelSet.ran_Λ_junc_recip_inr {V₁ : α ⟶ A} {V₂ : β ⟶ A}
    (hdisj : V₂ ≫ V₁° = 𝟘) :
    Freyd.Alg.ran V₂ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
      = Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ powerRel (sumCop α β).u₂ := by
  -- `V₂V₁°=𝟘` read at a point: no `y` is reached by both
  have hdisj : ∀ a b y, V₁ a y → V₂ b y → False := fun a b y h1 h2 =>
    cast (congrFun (congrFun hdisj b) a) ⟨y, h2, h1⟩
  apply hom_ext; intro y S
  rw [Λ_eq_classifier, Λ_eq_classifier]
  constructor
  · rintro ⟨y', ⟨rfl, b₀, hb₀, -⟩, hS⟩
    subst hS
    refine ⟨y, ⟨rfl, b₀, hb₀, hb₀⟩, fun b => V₂ b y, rfl, ?_, ?_⟩
    · intro b hb; exact ⟨Sum.inr b, rfl, (ListRel.junc_sum_inr V₁ V₂ b y).mpr hb⟩
    · rintro (a | b) hu
      · exact (hdisj a b₀ y ((ListRel.junc_sum_inl V₁ V₂ a y).mp hu) hb₀).elim
      · exact ⟨b, (ListRel.junc_sum_inr V₁ V₂ b y).mp hu, rfl⟩
  · rintro ⟨y', ⟨rfl, b₀, hb₀, -⟩, S', hS', hP⟩
    subst hS'
    refine ⟨y, ⟨rfl, b₀, hb₀, hb₀⟩, ?_⟩
    show S = fun w => junc (sumCop α β) V₁ V₂ w y
    funext w
    refine propext (Iff.symm ?_)
    cases w with
    | inl a =>
      rw [ListRel.junc_sum_inl]
      refine ⟨fun ha => (hdisj a b₀ y ha hb₀).elim, fun hs => ?_⟩
      obtain ⟨b', -, he⟩ := hP.2 _ hs
      exact nomatch he
    | inr b =>
      rw [ListRel.junc_sum_inr]
      refine ⟨fun hb => ?_, fun hs => ?_⟩
      · obtain ⟨u, rfl, hu⟩ := hP.1 b hb; exact hu
      · obtain ⟨b', hb', he⟩ := hP.2 _ hs
        obtain rfl : b = b' := Sum.inr.inj he
        exact hb'

/-- `inl` into `α+a` is natural in the summand `a` that varies, from the constant relator `α` —
    the dot on `P(inl)` in Proposition 9.1. -/
public theorem _root_.Freyd.Alg.RelSet.sumCop_inl_right_strictNatural :
    StrictNatural (Relator.sum (Relator.const α) (Relator.idRelator RelSet.{0})) (Relator.const α)
      (fun a => (sumCop α a).u₁) :=
  (strictNatural_sum_structure (F := Relator.const α) (F' := Relator.idRelator RelSet.{0})).1

/-- `inr` into `α+a` is natural in `a`, from the identity relator. -/
public theorem _root_.Freyd.Alg.RelSet.sumCop_inr_right_strictNatural :
    StrictNatural (Relator.sum (Relator.const α) (Relator.idRelator RelSet.{0}))
      (Relator.idRelator RelSet.{0}) (fun a => (sumCop α a).u₂) :=
  (strictNatural_sum_structure (F := Relator.const α) (F' := Relator.idRelator RelSet.{0})).2.1

/-- `inl` into `a+β` is natural in `a`, from the identity relator. -/
public theorem _root_.Freyd.Alg.RelSet.sumCop_inl_left_strictNatural :
    StrictNatural (Relator.sum (Relator.idRelator RelSet.{0}) (Relator.const β))
      (Relator.idRelator RelSet.{0}) (fun a => (sumCop a β).u₁) :=
  (strictNatural_sum_structure (F := Relator.idRelator RelSet.{0}) (F' := Relator.const β)).1

/-- `inr` into `a+β` is natural in `a`, from the constant relator `β`. -/
public theorem _root_.Freyd.Alg.RelSet.sumCop_inr_left_strictNatural :
    StrictNatural (Relator.sum (Relator.idRelator RelSet.{0}) (Relator.const β)) (Relator.const β)
      (fun a => (sumCop a β).u₂) :=
  (strictNatural_sum_structure (F := Relator.idRelator RelSet.{0}) (F' := Relator.const β)).2.1

/-- **Ex 9.5**, third claim, first summand: thinning the `inl`-image by `Q₁+Q₂` is thinning by
    `Q₁` and then taking the image, `P(inl)thin(Q₁+Q₂)=thin(Q₁)P(inl)`. -/
public theorem _root_.Freyd.Alg.RelSet.powerRel_inl_thinRel (Q₁ : α ⟶ α) (Q₂ : β ⟶ β) :
    powerRel (sumCop α β).u₁ ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
      = thinRel Q₁ ≫ powerRel (sumCop α β).u₁ := by
  apply hom_ext; intro S Y
  constructor
  · rintro ⟨S', hP, hY⟩
    refine ⟨fun a => Y (Sum.inl a), ⟨fun a ha => ?_, fun a ha => ?_⟩, ?_, ?_⟩
    · obtain ⟨t, ht, he⟩ := hP.2 _ (hY.1 _ ha)
      obtain rfl : a = t := Sum.inl.inj he
      exact ht
    · obtain ⟨u, rfl, hu⟩ := hP.1 a ha
      obtain ⟨w', hQ, hw'⟩ := hY.2 _ hu
      cases w' with
      | inl w =>
        obtain ⟨c, hc, he⟩ := (ListRel.junc_sum_inl (Q₁ ≫ (sumCop α β).u₁) (Q₂ ≫ (sumCop α β).u₂)
          w (Sum.inl a)).mp hQ
        obtain rfl : a = c := Sum.inl.inj he
        exact ⟨w, hc, hw'⟩
      | inr b =>
        obtain ⟨c, -, he⟩ := (ListRel.junc_sum_inr (Q₁ ≫ (sumCop α β).u₁) (Q₂ ≫ (sumCop α β).u₂)
          b (Sum.inl a)).mp hQ
        exact nomatch he
    · intro a ha; exact ⟨Sum.inl a, rfl, ha⟩
    · intro u hu
      obtain ⟨t, -, rfl⟩ := hP.2 _ (hY.1 _ hu)
      exact ⟨t, hu, rfl⟩
  · rintro ⟨Y', hY', hP⟩
    refine ⟨fun u => ∃ a, S a ∧ u = Sum.inl a, ⟨fun t ht => ⟨Sum.inl t, rfl, t, ht, rfl⟩,
      fun u hu => hu⟩, fun u hu => ?_, ?_⟩
    · obtain ⟨a, ha, rfl⟩ := hP.2 u hu
      exact ⟨a, hY'.1 a ha, rfl⟩
    · rintro u ⟨a, ha, rfl⟩
      obtain ⟨w, hQ, hw⟩ := hY'.2 a ha
      obtain ⟨u', rfl, hu'⟩ := hP.1 w hw
      exact ⟨Sum.inl w, (ListRel.junc_sum_inl (Q₁ ≫ (sumCop α β).u₁) (Q₂ ≫ (sumCop α β).u₂)
        w (Sum.inl a)).mpr ⟨a, hQ, rfl⟩, hu'⟩

/-- **Ex 9.5**, third claim, second summand: `P(inr)thin(Q₁+Q₂)=thin(Q₂)P(inr)`. -/
public theorem _root_.Freyd.Alg.RelSet.powerRel_inr_thinRel (Q₁ : α ⟶ α) (Q₂ : β ⟶ β) :
    powerRel (sumCop α β).u₂ ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
      = thinRel Q₂ ≫ powerRel (sumCop α β).u₂ := by
  apply hom_ext; intro S Y
  constructor
  · rintro ⟨S', hP, hY⟩
    refine ⟨fun b => Y (Sum.inr b), ⟨fun b hb => ?_, fun b hb => ?_⟩, ?_, ?_⟩
    · obtain ⟨t, ht, he⟩ := hP.2 _ (hY.1 _ hb)
      obtain rfl : b = t := Sum.inr.inj he
      exact ht
    · obtain ⟨u, rfl, hu⟩ := hP.1 b hb
      obtain ⟨w', hQ, hw'⟩ := hY.2 _ hu
      cases w' with
      | inl a =>
        obtain ⟨c, -, he⟩ := (ListRel.junc_sum_inl (Q₁ ≫ (sumCop α β).u₁) (Q₂ ≫ (sumCop α β).u₂)
          a (Sum.inr b)).mp hQ
        exact nomatch he
      | inr w =>
        obtain ⟨c, hc, he⟩ := (ListRel.junc_sum_inr (Q₁ ≫ (sumCop α β).u₁) (Q₂ ≫ (sumCop α β).u₂)
          w (Sum.inr b)).mp hQ
        obtain rfl : b = c := Sum.inr.inj he
        exact ⟨w, hc, hw'⟩
    · intro b hb; exact ⟨Sum.inr b, rfl, hb⟩
    · intro u hu
      obtain ⟨t, -, rfl⟩ := hP.2 _ (hY.1 _ hu)
      exact ⟨t, hu, rfl⟩
  · rintro ⟨Y', hY', hP⟩
    refine ⟨fun u => ∃ b, S b ∧ u = Sum.inr b, ⟨fun t ht => ⟨Sum.inr t, rfl, t, ht, rfl⟩,
      fun u hu => hu⟩, fun u hu => ?_, ?_⟩
    · obtain ⟨b, hb, rfl⟩ := hP.2 u hu
      exact ⟨b, hY'.1 b hb, rfl⟩
    · rintro u ⟨b, hb, rfl⟩
      obtain ⟨w, hQ, hw⟩ := hY'.2 b hb
      obtain ⟨u', rfl, hu'⟩ := hP.1 w hw
      exact ⟨Sum.inr w, (ListRel.junc_sum_inr (Q₁ ≫ (sumCop α β).u₁) (Q₂ ≫ (sumCop α β).u₂)
        w (Sum.inr b)).mpr ⟨b, hQ, rfl⟩, hu'⟩

/-- The thinned body is empty off `ran V₁ ∪ ran V₂` — an `est` of the empty set is nothing — so
    it splits by where the input lies. -/
public theorem _root_.Freyd.Alg.RelSet.thin_est_ran_split {V₁ : α ⟶ A} {V₂ : β ⟶ A}
    {U₁ : α ⟶ B} {U₂ : β ⟶ B} {Q₁ : α ⟶ α} {Q₂ : β ⟶ β} {R : B ⟶ B} :
    Λ ((junc (sumCop α β) V₁ V₂)°) ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
        ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R
      = (Freyd.Alg.ran V₁ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R) := by
  apply hom_ext; intro y z
  constructor
  · intro hb
    obtain ⟨S, hS, Y, hY, W, hW, hest⟩ := hb
    obtain ⟨t, ht, -⟩ := hW.2 z hest.1
    have hT : junc (sumCop α β) V₁ V₂ t y := by
      rw [Λ_eq_classifier] at hS
      subst hS
      exact hY.1 t ht
    cases t with
    | inl a =>
      have ha := (ListRel.junc_sum_inl V₁ V₂ a y).mp hT
      exact Or.inl ⟨y, ⟨rfl, a, ha, ha⟩, S, hS, Y, hY, W, hW, hest⟩
    | inr b =>
      have hb := (ListRel.junc_sum_inr V₁ V₂ b y).mp hT
      exact Or.inr ⟨y, ⟨rfl, b, hb, hb⟩, S, hS, Y, hY, W, hW, hest⟩
  · rintro (⟨y', ⟨rfl, -⟩, h⟩ | ⟨y', ⟨rfl, -⟩, h⟩) <;> exact h

/-- **Proposition 9.1 (B&dM p.222)**, in `Rel(Set)`: when `V₁` and `V₂` have disjoint ranges,
    thinning by `Q₁+Q₂` over the decompositions `[V₁,V₂]°` and assembling by `[U₁,U₂]` runs, on
    `ran V₁`, the `V₁` problem `W₁≜Λ(V₁°)thin(Q₁)P(U₁)est(R)` and, on `ran V₂`, the `V₂` one.
    One `calc` step per law, each branch in turn. -/
public theorem _root_.Freyd.Alg.RelSet.dp_disjoint_ranges {V₁ : α ⟶ A} {V₂ : β ⟶ A}
    {U₁ : α ⟶ B} {U₂ : β ⟶ B} {Q₁ : α ⟶ α} {Q₂ : β ⟶ β} {R : B ⟶ B}
    (hdisj : V₂ ≫ V₁° = 𝟘) :
    Λ ((junc (sumCop α β) V₁ V₂)°) ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
        ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R
      = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ thinRel Q₁ ≫ powerRel U₁ ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ thinRel Q₂ ≫ powerRel U₂ ≫ est R) :=
  calc Λ ((junc (sumCop α β) V₁ V₂)°) ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
        ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R
      = (Freyd.Alg.ran V₁ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R) := RelSet.thin_est_ran_split
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ powerRel (sumCop α β).u₁
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ ((junc (sumCop α β) V₁ V₂)°)
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R) := by
        rw [← Cat.assoc (Freyd.Alg.ran V₁), RelSet.ran_Λ_junc_recip_inl hdisj, Cat.assoc, Cat.assoc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ powerRel (sumCop α β).u₁
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ powerRel (sumCop α β).u₂
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R) := by
        rw [← Cat.assoc (Freyd.Alg.ran V₂), RelSet.ran_Λ_junc_recip_inr hdisj, Cat.assoc, Cat.assoc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ thinRel Q₁ ≫ powerRel (sumCop α β).u₁
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ powerRel (sumCop α β).u₂
            ≫ thinRel (sumMap (sumCop α β) (sumCop α β) Q₁ Q₂)
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R) := by
        rw [← Cat.assoc (powerRel (sumCop α β).u₁), RelSet.powerRel_inl_thinRel, Cat.assoc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ thinRel Q₁ ≫ powerRel (sumCop α β).u₁
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ thinRel Q₂ ≫ powerRel (sumCop α β).u₂
            ≫ powerRel (junc (sumCop α β) U₁ U₂) ≫ est R) := by
        rw [← Cat.assoc (powerRel (sumCop α β).u₂), RelSet.powerRel_inr_thinRel, Cat.assoc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ thinRel Q₁
            ≫ powerRel ((sumCop α β).u₁ ≫ junc (sumCop α β) U₁ U₂) ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ thinRel Q₂
            ≫ powerRel ((sumCop α β).u₂ ≫ junc (sumCop α β) U₁ U₂) ≫ est R) := by
        rw [← Cat.assoc (powerRel (sumCop α β).u₁), ← powerRel_comp,
          ← Cat.assoc (powerRel (sumCop α β).u₂), ← powerRel_comp]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ thinRel Q₁ ≫ powerRel U₁ ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ thinRel Q₂
            ≫ powerRel ((sumCop α β).u₂ ≫ junc (sumCop α β) U₁ U₂) ≫ est R) := by
        rw [u₁_junc]
    _ = (Freyd.Alg.ran V₁ ≫ Λ (V₁°) ≫ thinRel Q₁ ≫ powerRel U₁ ≫ est R)
        ∪ (Freyd.Alg.ran V₂ ≫ Λ (V₂°) ≫ thinRel Q₂ ≫ powerRel U₂ ≫ est R) := by
        rw [u₂_junc]

calc_steps Freyd.Alg.RelSet.dp_disjoint_ranges

end Prop91

end Freyd.Alg.RelSet.SL
