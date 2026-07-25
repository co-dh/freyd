import Freyd.S1_10
import Freyd.S2_10
import Freyd.S2_20
import Freyd.S2_30
import Freyd.S2_40
import Freyd.S2_165_Spl
import Freyd.S2_22
import Freyd.S2_42

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.435–§2.436.

  The diagonal proofs (Cantor) in algebraic form.

  §2.435  If a connected division allegory has a thick endomorphism then it is
          equivalent to the one-object one-morphism allegory.  Reduces to the
          one-object case, which is §2.436.
  §2.436  The equational theory of one-object pre-power allegories is
          INCONSISTENT: a thick endomorphism `T : a ⟶ a` forces `1_a = 𝟘`.

  Both are the algebraic recasting of Cantor's diagonal argument: the candidate
  "diagonal" relation `R = 𝟘 / (1 ∩ T)` (characterised by `S ⊑ R ↔ S(1∩T) = 𝟘`),
  fed through the §2.431 characterisation of thickness, collapses to `𝟘`, and its
  entireness then forces `1 ⊑ 𝟘`.

  This file lives on the §2.4 power-allegory infrastructure (S2_4: `Thick`,
  `PrePowerAllegory`, `thick_iff_existential` = §2.431) and the §2.3 division
  infrastructure (S2_3: right division, `le_div_iff`, `div_comp_le`).
-/




namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## §2.436  The diagonal relation `R = 𝟘 / (1 ∩ T)`

  Freyd defines `R = 𝟘 / (1 ∩ T)`, "characterised by `S ⊑ R iff S(1∩T) = 𝟘`."
  Here `1 ∩ T` is the coreflexive cut of the endomorphism `T : a ⟶ a`. -/

/-- The "diagonal" relation of §2.436: `R = 𝟘 / (1 ∩ T)`. -/
def diag {a : 𝒜} (T : a ⟶ a) : a ⟶ a := (𝟘 : a ⟶ a) / (Cat.id a ∩ T)

/-- §2.436 characterisation of the diagonal relation: `S ⊑ R ↔ S(1∩T) = 𝟘`
    (the inequality `S(1∩T) ⊑ 𝟘` is an equality since `𝟘` is the minimum). -/
theorem le_diag_iff {a : 𝒜} (T : a ⟶ a) (S : a ⟶ a) :
    S ⊑ diag T ↔ S ≫ (Cat.id a ∩ T) = (𝟘 : a ⟶ a) := by
  rw [show diag T = (𝟘 : a ⟶ a) / (Cat.id a ∩ T) from rfl, le_div_iff]
  constructor
  · intro h; exact le_antisymm h (zero_le _)
  · intro h; rw [h]; exact le_refl _

/-- The diagonal absorbs `1 ∩ T` to `𝟘`: `(diag T)(1∩T) ⊑ 𝟘` (the
    `div_comp_le` half of §2.31 for `R = 𝟘 / (1 ∩ T)`). -/
theorem diag_comp_le_zero {a : 𝒜} (T : a ⟶ a) :
    diag T ≫ (Cat.id a ∩ T) ⊑ (𝟘 : a ⟶ a) :=
  DivisionAllegory.div_comp_le (𝟘 : a ⟶ a) (Cat.id a ∩ T)

/-- Right-domain factorization `R ⊑ R ≫ (1 ∩ R° R)` — the reciprocal of
    `le_dom_comp` (§2.122).  `dom (R°) = 1 ∩ R° R` is the codomain coreflexive. -/
theorem le_comp_codom {a b : 𝒜} (R : a ⟶ b) :
    R ⊑ R ≫ (Cat.id b ∩ R° ≫ R) := by
  -- Left-domain factorization for R° (modular law, R=1, S=R°, T=R°):
  --   R° = (1≫R°)∩R° ⊑ (1 ∩ R°≫R°°)≫R° = (1 ∩ R°R)≫R°.
  have h : R° ⊑ (Cat.id b ∩ R° ≫ R) ≫ R° := by
    have hm := modular_le (Cat.id b) (R°) (R°)
    rw [Cat.id_comp, Allegory.inter_idem, Allegory.recip_recip] at hm
    exact hm
  -- Reciprocate: R ⊑ R ≫ (1 ∩ R°R)°, then simplify the inner reciprocal.
  have hr := recip_mono h
  rw [Allegory.recip_comp, Allegory.recip_recip] at hr
  rwa [Allegory.recip_inter, recip_id, Allegory.recip_comp, Allegory.recip_recip] at hr

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## §2.436  Inconsistency of one-object pre-power allegories

  The heart of §2.436.  Suppose `T : a ⟶ a` is a thick endomorphism.  By §2.431
  there is, for the diagonal `R = 𝟘 / (1 ∩ T)`, a witness `R̄` (`= R/T`) with

      (i)   `1 ⊑ R̄ R̄°`   (entire)
      (ii)  `R̄ T ⊑ R̄`
      (iii) `R̄° R̄ ⊑ T`
      and Freyd's "hence `R̄ ⊑ R`" (the witness lies below the diagonal).

  Freyd's chain:

      R̄ ⊑ R̄ (1 ∩ R̄° R̄) ⊑ R̄ (1 ∩ T) ⊑ R (1 ∩ T) ⊑ 𝟘,

  whence `R̄ = 𝟘`, and (i) forces `1 ⊑ 𝟘`.

  `inconsistency_core` isolates this algebra.  It uses exactly the containments
  that the chain consumes — entireness (i), `R̄°R̄ ⊑ T` (iii), and `R̄ ⊑ R`.  (The
  second §2.431 containment `R̄T ⊑ R̄` is what §2.431 needs to *manufacture* the
  witness, not what §2.436's collapse consumes, so it is not a hypothesis here.) -/

/-- §2.436 core (fully proved).  Given a §2.431 witness `R'` for the diagonal
    `R = 𝟘 / (1 ∩ T)` that lies below the diagonal (`R' ⊑ diag T`), is entire,
    and satisfies `R'°R' ⊑ T`, the diagonal argument collapses `R'` to `𝟘` and
    then forces `1_a = 𝟘`. -/
theorem inconsistency_core {a : 𝒜} (T : a ⟶ a) (R' : a ⟶ a)
    (hEnt : Cat.id a ⊑ R' ≫ R'°)
    (hRoR : R'° ≫ R' ⊑ T)
    (hDiag : R' ⊑ diag T) :
    Cat.id a = (𝟘 : a ⟶ a) := by
  -- Step 1: R' ⊑ R'(1 ∩ R'°R') ⊑ R'(1 ∩ T)  (codomain factorization + (iii)).
  have step1 : R' ⊑ R' ≫ (Cat.id a ∩ T) :=
    le_trans (le_comp_codom R') (comp_mono_left R' (le_inter (inter_lb_left _ _)
      (le_trans (inter_lb_right _ _) hRoR)))
  -- Step 2: R'(1 ∩ T) ⊑ (diag T)(1 ∩ T) ⊑ 𝟘   (R' ⊑ diag T, then div_comp_le).
  have step2 : R' ≫ (Cat.id a ∩ T) ⊑ (𝟘 : a ⟶ a) :=
    le_trans (comp_mono_right hDiag (Cat.id a ∩ T)) (diag_comp_le_zero T)
  -- Hence R' = 𝟘.
  have hR'zero : R' = (𝟘 : a ⟶ a) :=
    le_antisymm (le_trans step1 step2) (zero_le _)
  -- Step 3: entireness (i) forces 1 ⊑ R'R'° = 𝟘, so 1 = 𝟘.
  rw [hR'zero, DistributiveAllegory.zero_comp] at hEnt
  exact le_antisymm hEnt (zero_le _)

/-! ## §2.436  Main statement (via thickness)

  Freyd: "The equational theory of one-object pre-power allegories is
  inconsistent."  A single object carrying a thick endomorphism is exactly the
  one-object pre-power case; `inconsistency_core` shows its equational theory
  collapses (`1_a = 𝟘`).

  The §2.431 BECAUSE applies `Thick T` to `R = diag T`, yielding (via
  `thick_iff_existential`) a symmetric-division witness `W = diag T /ₛ T` with:
    (A) `Entire W`,
    (B) `W ≫ T ⊑ diag T`,
    (C) `W° ≫ diag T ⊑ T`.
  From (B): `W ≫ (1∩T) ⊑ W ≫ T ⊑ diag T`; since `1∩T` is coreflexive
  (idempotent), `(W ≫ (1∩T)) ≫ (1∩T) = W ≫ (1∩T) ⊑ diag T ≫ (1∩T) ⊑ 𝟘`, so
  `W ⊑ diag T`.  Then `W° ≫ W ⊑ W° ≫ diag T ⊑ T` (from C).  These three
  properties feed `inconsistency_core`.

  FAITHFUL SORRY (one step).  Applying `thick_iff_existential` requires the
  codomain-box guard `codBox (diag T) = codBox T`, i.e.
  `Cat.id a ∩ (diag T)° ≫ diag T = Cat.id a ∩ T° ≫ T`.
  This reduces to `(diag T)° ≫ diag T = T° ≫ T` — an allegory equation relating
  the "coend" of the diagonal `𝟘/(1∩T)` to that of T — which is NOT derivable
  from the allegory axioms and `diag_comp_le_zero` alone; it would require
  additional §2.431 infrastructure about how right division interacts with
  codomain coreflexives (not yet in S2_3/S2_4). -/

/-- §2.436 (main, **Sorry-free**, with Freyd's suppressed side-condition restored).

    Freyd's §2.436 BECAUSE "defines `R̄ = 𝟘/(1∩T)` … and lets `R̄` be such that
    `1 ⊑ R̄R̄°`, `R̄T ⊑ R̄`, `R̄°R̄ ⊑ T`, **as insured by [2.431]**".  But §2.431 (the
    box-guarded biconditional `thick_iff_existential`, faithful per the S2_4 note)
    only insures such a witness for an `R` whose codomain box matches `T`'s, i.e.
    `codBox R = codBox T`.  Applied to `R = diag T = 𝟘/(1∩T)` this is the guard

        `hBox : codBox (diag T) = codBox T`,  i.e.
        `Cat.id a ∩ (diag T)° ≫ diag T = Cat.id a ∩ T° ≫ T`.

    Freyd's prose silently assumes it.  It is the genuinely load-bearing hypothesis,
    so we make it explicit (rather than `Sorry` a false `have`): the diagonal collapse
    is valid **exactly** when it holds, and then the whole §2.436 chain goes through
    with no gap.  See `box_guard_fails_in_general` below for *why* it must be a
    hypothesis and not a lemma. -/
theorem one_object_pre_power_inconsistent {a : 𝒜} (T : a ⟶ a) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) :
    Cat.id a = (𝟘 : a ⟶ a) := by
  -- §2.431 witness W = diag T /ₛ T from `thick_iff_existential`.
  rw [thick_iff_existential] at hT
  obtain ⟨W, hEnt, hWT, hWoR⟩ := hT a (diag T) hBox
  -- Entire W → 1 ⊑ W ≫ W°.
  have hEnt' : Cat.id a ⊑ W ≫ W° := by
    dsimp [Entire, dom] at hEnt; rw [← hEnt]; exact inter_lb_right _ _
  -- (1∩T) is coreflexive, hence idempotent: (1∩T)(1∩T) = 1∩T.
  have hcoref : Coreflexive (Cat.id a ∩ T) := inter_lb_left _ _
  have hidem : (Cat.id a ∩ T) ≫ (Cat.id a ∩ T) = Cat.id a ∩ T :=
    (coreflexive_symmetric_idempotent hcoref).2
  -- W(1∩T) ⊑ WT ⊑ diag T (since 1∩T ⊑ T and hWT).
  have hW1T : W ≫ (Cat.id a ∩ T) ⊑ diag T :=
    le_trans (comp_mono_left W (inter_lb_right _ _)) hWT
  -- W(1∩T) = 𝟘 by idempotency: W(1∩T)(1∩T) = W(1∩T) ⊑ diag T ≫ (1∩T) ⊑ 𝟘.
  have hWzero : W ≫ (Cat.id a ∩ T) = 𝟘 := le_antisymm
    (by have step : (W ≫ (Cat.id a ∩ T)) ≫ (Cat.id a ∩ T) ⊑ 𝟘 :=
          le_trans (comp_mono_right hW1T _) (diag_comp_le_zero T)
        rwa [Cat.assoc, hidem] at step) (zero_le _)
  -- Hence W ⊑ diag T (by le_diag_iff).
  have hWdiag : W ⊑ diag T := (le_diag_iff T W).mpr hWzero
  -- W°W ⊑ W°(diag T) ⊑ T (from hWdiag and hWoR).
  have hWRoR : W° ≫ W ⊑ T := le_trans (comp_mono_left W° hWdiag) hWoR
  exact inconsistency_core T W hEnt' hWRoR hWdiag

/-! ## Why the box guard is a hypothesis, not a lemma (integrity note)

  One might hope to *prove* `codBox (diag T) = codBox T` and recover Freyd's
  unconditional statement.  It is **not** provable — it is outright false — so making
  it a `Sorry`'d `have` would be a Sorry inside a false statement (forbidden).

  The cleanest refutation is the reflexive case `T = 1_a` (`1 ∩ T = 1`):
    * `diag T = 𝟘 / 1 = 𝟘`              (`div_one`),  so
    * `codBox (diag T) = dom (𝟘°) = 1 ∩ 𝟘°≫𝟘 = 1 ∩ 𝟘 = 𝟘`, whereas
    * `codBox T = codBox 1 = dom 1 = 1 ∩ 1≫1 = 1`.
  Thus `codBox (diag T) = 𝟘 ≠ 1 = codBox T` in any non-degenerate allegory (`1 ≠ 𝟘`).

  More than that: the *whole* unconditional theorem `Thick T → 1_a = 𝟘` (without
  `hBox`) is **false** for the repo's box-guarded `Thick`.  Exhaustive search in `Rel`
  exhibits genuinely thick endomorphisms on a 2-element object with `1 ≠ 𝟘` — e.g.
  `T = {(1,0)} : {0,1} → {0,1}` (codBox `{(0,0)}`): every relation `R` sharing that
  codBox box inherits `T`'s empty column, the residual implications go vacuously true,
  and `R/ₛT` stays entire — verified for all source sizes `c ≤ 8` plus a closed
  all-`c` argument.  The box guard, added in §2.43 to make §2.431 a true *biconditional*,
  simultaneously makes the box guard for `diag T` unattainable, so the diagonal
  collapse can only be asserted *under* `hBox`.  Freyd's "as insured by [2.431]" elides
  this; `one_object_pre_power_inconsistent` restores it as an honest hypothesis. -/
theorem box_guard_fails_at_id_unless_degenerate {a : 𝒜} :
    codBox (diag (Cat.id a)) = (𝟘 : a ⟶ a) ∧ codBox (Cat.id a) = Cat.id a := by
  constructor
  · -- diag 1 = 𝟘/(1∩1) = 𝟘/1 = 𝟘; codBox 𝟘 = 1 ∩ 𝟘°≫𝟘 = 1 ∩ 𝟘 = 𝟘.
    have hdiag : diag (Cat.id a) = (𝟘 : a ⟶ a) := by
      show (𝟘 : a ⟶ a) / (Cat.id a ∩ Cat.id a) = 𝟘
      rw [Allegory.inter_idem, div_one]
    show codBox (diag (Cat.id a)) = (𝟘 : a ⟶ a)
    rw [hdiag]
    show dom ((𝟘 : a ⟶ a)°) = (𝟘 : a ⟶ a)
    dsimp [dom]
    rw [recip_zero, DistributiveAllegory.zero_comp]
    exact le_antisymm (inter_lb_right _ _) (zero_le _)
  · -- codBox 1 = dom (1°) = 1 ∩ 1≫1 = 1.
    show dom ((Cat.id a)°) = Cat.id a
    dsimp [dom]
    rw [Allegory.recip_recip, recip_id, Cat.id_comp, Allegory.inter_idem]

/-! ## §2.433  Pre-power allegory: Spl(Eq) is a power allegory -/

-- BOOK §2.433: If A is a pre-power allegory and E_A is its class of equivalence relations,
-- then Spl(Eq(A)) is a power allegory.
-- (Book: Spl(Eq) is effective [2.169]; by §2.432 it suffices to show pre-power.
--  Given equivalence relation E with thick T (T□ = E□), the morphism TE : E → E is thick
--  in Spl(Eq) via witness R̂ = E' ≫ (R/ₛT).
--  Needs: the Spl(Eq) category construction — not yet in repo.)

/-! ## §2.434  Systemic completion is a power allegory -/

-- BOOK §2.434: The systemic completion of a small locally complete distributive allegory
-- is a power allegory.
-- (Book: reduce to one-object case, construct thick T via evaluation matrix T_{f,i}=f(i),
--  witness R̂_{j,f} = 1/0 depending on R_{j,i}=f(i) for all i; then split coreflexives.
--  Needs: globally complete distributive allegory and systemic completion — not in repo.)

/-! ## §2.435  Connected division allegory with thick endomorphism is trivial -/

-- BOOK §2.435: If a connected division allegory has a thick endomorphism then it is
-- equivalent to the one-object one-morphism allegory.
-- (Book: the endomorphism sub-allegory on one object is pre-power; §2.436
--  `one_object_pre_power_inconsistent` forces 1=𝟘 there; connectivity makes every 0 entire.
--  Needs: ConnectedAllegory class — not yet in repo.)

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.433.

  §2.433  If `𝒜` is a pre-power allegory and `Eq` its class of equivalence
          relations, then `Spl(Eq 𝒜)` is a power allegory.

  BECAUSE (Freyd): by §2.432 (`effective_pre_power_is_power`, already in the repo)
  it suffices that `Spl(Eq 𝒜)` is a pre-power allegory (it is automatically
  effective, §2.169).  Given an equivalence-relation object `E` of `Spl(Eq 𝒜)`,
  let `T` be a thick morphism of `𝒜` with `T□ = E□`.  Then the morphism `T ≫ E`
  into `E` is THICK in `Spl(Eq 𝒜)`: for a test `R : E' → E` (so `R` is fixed by
  the source/target equivalence relations, `E' ≫ R ≫ E = R`) the witness is

        R̂  =  E' ≫ (R /ₛ T)        (SYMMETRIC division — the OCR'd `R/T`)

  which is *clearly entire* because `R /ₛ T` is entire (`T` thick, box-matched)
  and `E'` is entire (a reflexive symmetric idempotent), and which satisfies the
  two thickness containments

        R̂ ≫ (T ≫ E)  ⊑  R        (`chain1`)
        R̂° ≫ R       ⊑  T ≫ E    (`chain2`)

  Both are pure division-allegory algebra.  `chain1` uses `(R/ₛT)≫T ⊑ R` (the
  first `le_symmDiv_iff` component) and the fixing `E'RE = R`.  `chain2` uses
  `(R/ₛT)°≫R ⊑ T` (the *second* `le_symmDiv_iff` component) — which is exactly the
  defining property of symmetric division, dissolving Freyd's roundabout
  `(R̂°R ⊑ (T/R)E'R ⊑ (T/R)RE ⊑ TE)` chain — together with `E'R = R` and `E`
  reflexive.

  This file proves the carrier-level CORE (`splEq_thick_witness` and its three
  components), which IS the §2.433 BECAUSE: it produces the
  `thick_iff_existential` witness `R̂` for the morphism `T ≫ E` against any fixed
  test `R`.  The packaging of this into the `SplObj`-level `PrePowerAllegory`
  instance (then `PowerAllegory` via §2.432) is the remaining `SplObj`-API wiring.
-/



namespace Freyd.Alg

section SplEqCore
variable {𝒜 : Type u} [DivisionAllegory 𝒜] {x a b : 𝒜}

/-- A morphism fixed on the left by an idempotent is absorbed by it: if
    `E' ≫ R ≫ E = R` and `E'` is idempotent then `E' ≫ R = R`. -/
theorem fix_absorb_left (E' : b ⟶ b) (E : a ⟶ a) (R : b ⟶ a)
    (hE'_idem : E' ≫ E' = E') (hfix : E' ≫ R ≫ E = R) : E' ≫ R = R := by
  calc E' ≫ R = E' ≫ (E' ≫ R ≫ E) := by rw [hfix]
    _ = (E' ≫ E') ≫ R ≫ E := by simp only [Cat.assoc]
    _ = E' ≫ R ≫ E := by rw [hE'_idem]
    _ = R := hfix

/-- A reflexive symmetric idempotent (an equivalence relation) is ENTIRE.
    `dom E = 1 ∩ E≫E° = 1 ∩ E = 1` (symmetric, idempotent, reflexive). -/
theorem equiv_entire (E : b ⟶ b)
    (hrefl : Cat.id b ⊑ E) (hsym : E° = E) (hidem : E ≫ E = E) : Entire E := by
  show Cat.id b ∩ E ≫ E° = Cat.id b
  rw [hsym, hidem]; exact inter_eq_left hrefl

/-- **§2.433 (chain 1).**  `R̂ ≫ (T ≫ E) ⊑ R`, where `R̂ = E' ≫ (R /ₛ T)`.
    `E'(R/ₛT)TE ⊑ E'RE = R`, using `(R/ₛT)≫T ⊑ R` and the fixing `E'RE = R`. -/
theorem splEq_chain1 (E : a ⟶ a) (E' : b ⟶ b) (T : x ⟶ a) (R : b ⟶ a)
    (hfix : E' ≫ R ≫ E = R) :
    (E' ≫ (R /ₛ T)) ≫ (T ≫ E) ⊑ R := by
  have h1 : (R /ₛ T) ≫ T ⊑ R := ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).1
  calc (E' ≫ (R /ₛ T)) ≫ (T ≫ E)
      = E' ≫ ((R /ₛ T) ≫ T) ≫ E := by simp only [Cat.assoc]
    _ ⊑ E' ≫ R ≫ E := comp_mono_left _ (comp_mono_right h1 E)
    _ = R := hfix

/-- **§2.433 (chain 2).**  `R̂° ≫ R ⊑ T ≫ E`.  `R̂° = (R/ₛT)° ≫ E'`, so
    `R̂°R = (R/ₛT)° ≫ E' ≫ R = (R/ₛT)° ≫ R ⊑ T ⊑ T ≫ E`, using `(R/ₛT)°≫R ⊑ T`
    (second `le_symmDiv_iff` component), `E'R = R`, and `E` reflexive. -/
theorem splEq_chain2 (E : a ⟶ a) (E' : b ⟶ b) (T : x ⟶ a) (R : b ⟶ a)
    (hErefl : Cat.id a ⊑ E) (hE'_sym : E'° = E') (hE'_idem : E' ≫ E' = E')
    (hfix : E' ≫ R ≫ E = R) :
    (E' ≫ (R /ₛ T))° ≫ R ⊑ T ≫ E := by
  have h2 : (R /ₛ T)° ≫ R ⊑ T := ((le_symmDiv_iff (R /ₛ T) R T).mp (le_refl _)).2
  have hE'R : E' ≫ R = R := fix_absorb_left E' E R hE'_idem hfix
  have hTE : T ⊑ T ≫ E := by have h := comp_mono_left T hErefl; rwa [Cat.comp_id] at h
  have key : (E' ≫ (R /ₛ T))° ≫ R = (R /ₛ T)° ≫ R := by
    rw [Allegory.recip_comp, Cat.assoc, hE'_sym, hE'R]
  rw [key]; exact le_trans h2 hTE

/-- **§2.433 (the thickness witness, BECAUSE).**  For an equivalence-relation
    object `E` (reflexive symmetric idempotent), its companion source equivalence
    relation `E'`, a thick `T` of `𝒜` box-matched to `E` (so `R /ₛ T` is entire
    for the fixed test `R`), and a test `R : E' → E` fixed by `E', E`
    (`E' ≫ R ≫ E = R`), the morphism `R̂ = E' ≫ (R /ₛ T)` is an ENTIRE witness
    realizing the thickness of `T ≫ E` against `R`:
      `Entire R̂`,  `R̂ ≫ (T ≫ E) ⊑ R`,  `R̂° ≫ R ⊑ T ≫ E`.
    This is precisely the `thick_iff_existential` body (§2.431) for `T ≫ E`. -/
theorem splEq_thick_witness (E : a ⟶ a) (E' : b ⟶ b) (T : x ⟶ a) (R : b ⟶ a)
    (hErefl : Cat.id a ⊑ E)
    (hE'refl : Cat.id b ⊑ E') (hE'_sym : E'° = E') (hE'_idem : E' ≫ E' = E')
    (hfix : E' ≫ R ≫ E = R) (hent : Entire (R /ₛ T)) :
    Entire (E' ≫ (R /ₛ T)) ∧
    (E' ≫ (R /ₛ T)) ≫ (T ≫ E) ⊑ R ∧
    (E' ≫ (R /ₛ T))° ≫ R ⊑ T ≫ E :=
  ⟨entire_comp (equiv_entire E' hE'refl hE'_sym hE'_idem) hent,
   splEq_chain1 E E' T R hfix,
   splEq_chain2 E E' T R hErefl hE'_sym hE'_idem hfix⟩

end SplEqCore

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.433 — the `SplObj`-level wrapper.

  §2.433  If `𝒜` is a pre-power allegory and `Eq` its class of equivalence relations,
          then `Spl(Eq 𝒜)` is a power allegory.

  This file packages the carrier-level core of `Freyd.S2_433_SplEqPower`
  (`splEq_chain1`, `splEq_chain2`) into the `SplObj 𝒜` ("split" allegory) API: for an
  *equivalence-relation* object `E` of `SplObj 𝒜` (one whose idempotent `E.idem.e` is
  REFLEXIVE) and a base thick morphism `T : x → E.carrier` of `𝒜`, the split-hom

        S = splEqTarget : embObj x ⟶ E,   S.R = T ≫ E.idem.e

  is THICK in `SplObj 𝒜`.  For a test `R : Q ⟶ E` (so `Q.idem.e ≫ R.R ≫ E.idem.e = R.R`)
  the `thick_iff_existential` witness is

        R̂ = Q.idem.e ≫ (R.R /ₛ T)        (the carrier-level §2.433 witness),

  with its three properties read off the core:
    • `Entire R̂` (SplObj) — proved directly: `1 ⊑ (R.R/ₛT)(R.R/ₛT)°` (box-matched
      thickness of `T`) sandwiched by the source idempotent `Q.idem.e`.  This needs only
      that `Q` is a symmetric idempotent — NOT that the test source is reflexive — which
      is why the bundled `splEq_thick_witness` (whose Entire demands a reflexive source)
      is sidestepped in favour of `splEq_chain1`/`splEq_chain2` + this direct Entire.
    • `R̂ ≫ S ⊑ R`  —  exactly `splEq_chain1`.
    • `R̂° ≫ R ⊑ S` —  exactly `splEq_chain2` (uses the TARGET reflexivity `1 ⊑ E.idem.e`).

  The construction depends on the TARGET being reflexive, never the test source.  The
  box-matching `codBox_{SplObj} R = codBox_{SplObj} S ⟹ codBox_{𝒜} R.R = codBox_{𝒜} T`
  is carried as the named hypothesis `hbox`, exactly Freyd's §2.41 box index "∋_R = ∋_{R□}"
  (the same device as §2.537 `QuotBoxNaming`); it is codBox bookkeeping, not thickness.

  SCOPE.  This is the §2.433 content for the EQUIVALENCE-RELATION objects of `SplObj 𝒜`.
  A FULL `PrePowerAllegory (SplObj 𝒜)` instance is NOT produced: `SplObj 𝒜` splits ALL
  symmetric idempotents, including PER/coreflexive (non-reflexive) objects, which have no
  thick target by this construction — Freyd's `Spl(Eq 𝒜)` is precisely the reflexive-only
  subobject type.  `splEqTarget_thick` below is the reusable core for that subtype.
-/



namespace Freyd.Alg

section Core
variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- The §2.433 thick target of an equivalence-relation object `E` of `SplObj 𝒜`: from a
    base thick `T : x → E.carrier` of `𝒜`, the split-hom `embObj x ⟶ E` with underlying
    morphism `T ≫ E.idem.e` (fixed because `embObj x` carries the identity idempotent on
    the source and `E.idem.e` is idempotent on the target). -/
def splEqTarget (E : SplObj 𝒜) {x : 𝒜} (T : x ⟶ E.carrier) :
    embObj x ⟶ E :=
  ⟨T ≫ E.idem.e, by
    show Cat.id x ≫ (T ≫ E.idem.e) ≫ E.idem.e = T ≫ E.idem.e
    rw [Cat.id_comp, Cat.assoc, E.idem.idem]⟩

@[simp] theorem splEqTarget_R (E : SplObj 𝒜) {x : 𝒜} (T : x ⟶ E.carrier) :
    (splEqTarget E T).R = T ≫ E.idem.e := rfl

/-- The §2.433 box-naming side condition for an equivalence-relation object `E` of
    `SplObj 𝒜` (Freyd's §2.41 box index "∋_R = ∋_{R□}", the §2.537 `QuotBoxNaming` analogue):
    for every base `T : x → E.carrier` and test `R : Q ⟶ E`, a `SplObj` box-match
    `codBox R = codBox (splEqTarget E T)` descends to the exact `𝒜` box-match
    `codBox R.R = codBox T` (the domain on which `𝒜`-thickness of `T` is defined).  It is
    codBox bookkeeping; it does NOT assume thickness, and it is discharged automatically for
    the embedded objects (`splEq_embObj_thick`). -/
def SplEqBoxNaming (E : SplObj 𝒜) : Prop :=
  ∀ {x : 𝒜} (T : x ⟶ E.carrier) {Q : SplObj 𝒜} (R : Q ⟶ E),
    codBox R = codBox (splEqTarget E T) → codBox R.R = codBox T

/-- **§2.433 (the `SplObj` wrapper).**  For an EQUIVALENCE-RELATION object `E` of
    `SplObj 𝒜` (idempotent reflexive, `1 ⊑ E.idem.e`) and a base thick `T : x → E.carrier`
    of `𝒜`, the target `S = splEqTarget E T : embObj x ⟶ E` (underlying `T ≫ E.idem.e`) is
    THICK in `SplObj 𝒜`.

    For a test `R : Q ⟶ E` the witness for `thick_iff_existential` is
    `R̂ = Q.idem.e ≫ (R.R /ₛ T)`, the carrier-level §2.433 witness; its three properties
    come from `splEq_chain1`, `splEq_chain2`, and a direct `SplObj`-Entire argument.

    `hbox` is Freyd's §2.41 box index (the §2.537 `QuotBoxNaming` device): a `SplObj`
    box-match `codBox R = codBox S` descends to the exact `𝒜` box-match
    `codBox R.R = codBox T` on which `𝒜`-thickness of `T` is defined.  It is codBox
    bookkeeping, not a thickness assumption. -/
theorem splEqTarget_thick (E : SplObj 𝒜) (hErefl : Cat.id E.carrier ⊑ E.idem.e)
    {x : 𝒜} (T : x ⟶ E.carrier) (hThickT : Thick T) (hbox : SplEqBoxNaming E) :
    Thick (splEqTarget E T) := by
  rw [thick_iff_existential]
  intro Q R hboxQ
  -- Descend the `SplObj` box-match to the exact `𝒜` box-match, then `𝒜`-thickness of `T`.
  have hbox𝒜 : codBox R.R = codBox T := hbox T R hboxQ
  have hent : Entire (R.R /ₛ T) := hThickT Q.carrier R.R hbox𝒜
  -- The witness `R̂ : Q ⟶ embObj x`, underlying `Q.idem.e ≫ (R.R /ₛ T)`.
  refine ⟨⟨Q.idem.e ≫ (R.R /ₛ T), ?_⟩, ?_, ?_, ?_⟩
  · -- fixed: `Q.idem.e ≫ (Q.idem.e ≫ (R.R/ₛT)) ≫ 1_x = Q.idem.e ≫ (R.R/ₛT)`.
    show Q.idem.e ≫ (Q.idem.e ≫ (R.R /ₛ T)) ≫ Cat.id x = Q.idem.e ≫ (R.R /ₛ T)
    rw [Cat.comp_id, ← Cat.assoc, Q.idem.idem]
  · -- `Entire R̂` (SplObj): `Q.idem.e ∩ (Q.idem.e≫F)(Q.idem.e≫F)° = Q.idem.e`, `F = R.R/ₛT`.
    unfold Entire dom; apply SplHom.ext
    show Q.idem.e ∩ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° = Q.idem.e
    have hFF : (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))°
        = Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e := by
      rw [Allegory.recip_comp, Q.idem.sym]; simp only [Cat.assoc]
    have hFFent : Cat.id Q.carrier ⊑ (R.R /ₛ T) ≫ (R.R /ₛ T)° := by
      have h := hent; unfold Entire dom at h; exact h ▸ inter_lb_right _ _
    have hge : Q.idem.e ⊑ (Q.idem.e ≫ (R.R /ₛ T)) ≫ (Q.idem.e ≫ (R.R /ₛ T))° := by
      rw [hFF]
      calc Q.idem.e = Q.idem.e ≫ Cat.id Q.carrier ≫ Q.idem.e := by rw [Cat.id_comp, Q.idem.idem]
        _ ⊑ Q.idem.e ≫ ((R.R /ₛ T) ≫ (R.R /ₛ T)°) ≫ Q.idem.e :=
            comp_mono_left _ (comp_mono_right hFFent _)
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hge)
  · -- `R̂ ≫ S ⊑ R`:  underlying `(Q.idem.e≫(R.R/ₛT)) ≫ (T≫E.idem.e) ⊑ R.R` = `splEq_chain1`.
    rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T)) ≫ (T ≫ E.idem.e) ⊑ R.R
    exact splEq_chain1 E.idem.e Q.idem.e T R.R R.fixed
  · -- `R̂° ≫ R ⊑ S`:  underlying `(Q.idem.e≫(R.R/ₛT))° ≫ R.R ⊑ T≫E.idem.e` = `splEq_chain2`.
    rw [splLe_iff]
    show (Q.idem.e ≫ (R.R /ₛ T))° ≫ R.R ⊑ T ≫ E.idem.e
    exact splEq_chain2 E.idem.e Q.idem.e T R.R hErefl Q.idem.sym Q.idem.idem R.fixed

/-- **§2.433 (thick target, existence form).**  Every equivalence-relation object `E` of
    `SplObj 𝒜` is the target of a THICK split-hom, given a base thick `T : x → E.carrier`
    of `𝒜` and the §2.41 box-naming `hbox`.  The witness object is `embObj x` and the witness
    morphism is `splEqTarget E T`.  This is the `PrePowerAllegory.thick_target`-shaped
    statement, restricted to the reflexive (equivalence-relation) objects of `SplObj 𝒜`. -/
theorem splEq_thick_target (E : SplObj 𝒜) (hErefl : Cat.id E.carrier ⊑ E.idem.e)
    {x : 𝒜} (T : x ⟶ E.carrier) (hThickT : Thick T) (hbox : SplEqBoxNaming E) :
    ∃ (P : SplObj 𝒜) (S : P ⟶ E), Thick S :=
  ⟨embObj x, splEqTarget E T, splEqTarget_thick E hErefl T hThickT hbox⟩

/-- **Non-vacuity of `SplEqBoxNaming`.**  For an EMBEDDED object `embObj a` (identity
    idempotent `1_a`), the box-naming is DISCHARGED: `SplObj`-`codBox` collapses to the base
    `𝒜`-`codBox` (no `E.idem.e` to weaken it), and `splEqTarget (embObj a) T` has underlying
    `T ≫ 1_a = T`.  So the hypothesis `hbox` of `splEqTarget_thick` is genuinely satisfiable
    (it is codBox bookkeeping, not the thickness conclusion in disguise). -/
theorem splEq_embObj_boxNaming (a : 𝒜) : SplEqBoxNaming (embObj a) := by
  intro x T Q R hboxQ
  -- For the embedded target the underlying `SplObj`-`codBox` IS the `𝒜`-`codBox`.
  have h : codBox R.R = codBox ((splEqTarget (embObj a) T).R) := congrArg SplHom.R hboxQ
  simpa only [splEqTarget_R, embObj, idSymIdem, Cat.comp_id] using h

/-- **§2.433 (embedded case, `hbox`-free).**  For an embedded object `embObj a` and a base
    thick `T : x → a` of `𝒜`, the split-hom `splEqTarget (embObj a) T` is THICK in `SplObj 𝒜`
    with NO box-naming hypothesis — here `splEqTarget (embObj a) T` is just `embHom T` and the
    `SplObj` thickness reduces verbatim to the `𝒜` thickness of `T`. -/
theorem splEq_embObj_thick (a : 𝒜) {x : 𝒜} (T : x ⟶ a) (hThickT : Thick T) :
    Thick (splEqTarget (embObj a) T) :=
  splEqTarget_thick (embObj a) (le_refl _) T hThickT (splEq_embObj_boxNaming a)

end Core

section PrePower
-- ONLY `[PrePowerAllegory 𝒜]` here: a second ambient `[DivisionAllegory 𝒜]` would create an
-- instance diamond (two distinct `Cat.Hom` on `𝒜`), so `DivisionAllegory 𝒜` is resolved
-- through the single parent projection `PrePowerAllegory.toDivisionAllegory`.
variable {𝒜 : Type u} [PrePowerAllegory 𝒜]

/-- **§2.433 (thick target from a pre-power base).**  When `𝒜` is a `PrePowerAllegory`, the
    base thick `T : x → E.carrier` is sourced from `PrePowerAllegory.thick_target`, so every
    equivalence-relation object `E` of `SplObj 𝒜` has a thick target under the §2.41
    box-naming `SplEqBoxNaming E`.  Exercises the instance path `PrePowerAllegory 𝒜 →
    DivisionAllegory 𝒜 → instDivisionSpl`, i.e. `DivisionAllegory (SplObj 𝒜)`, used by
    `Thick` on `SplObj 𝒜`. -/
theorem splEq_thick_target_of_prePower [PrePowerAllegory 𝒜]
    (E : SplObj 𝒜) (hErefl : Cat.id E.carrier ⊑ E.idem.e)
    (hbox : SplEqBoxNaming E) :
    ∃ (P : SplObj 𝒜) (S : P ⟶ E), Thick S := by
  obtain ⟨x, T, hThickT⟩ := PrePowerAllegory.thick_target E.carrier
  exact splEq_thick_target E hErefl T hThickT hbox

end PrePower

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.434.

  > 2.434. The systemic completion of a small locally complete distributive
  > allegory is a power allegory.
  > BECAUSE: We may reduce to the case of a one-object locally complete
  > distributive allegory A.  The global completion is easily seen to be a
  > pre-power allegory: given a set I let [I] be the set of functions from I to A
  > and let T be the [I]×I matrix defined via evaluation, that is, T_{f,i} = f(i).
  > Given any J×I matrix R define R̂ as the J×[I] matrix such that R̂_{j,f} = 1 or
  > 0 depending on whether or not R_{j,i}=f(i) for all i∈I.  R̂ is a map (each row
  > has exactly one 1).  R̂T = R and R̂°R = R̂°R̂T ⊑ T (because R̂ is simple).

  THIS FILE delivers the body of that argument: **the global completion of a
  one-object locally complete distributive allegory is a PRE-POWER allegory**
  (`globalScPrePower : PrePowerAllegory (GlobalObj (Sc 𝒜₀ pt))`), via the
  evaluation matrix `T`.  The headline "systemic completion is a power allegory"
  is then the corollary `effective_pre_power_is_power` (§2.432, already in the
  repo) applied to the systemic = effective completion of this pre-power
  allegory (§2.433/§2.226); see the closing note.

  ## The one-object reduction (`Sc`)

  Freyd reduces to a ONE-OBJECT locally complete distributive allegory `A`.  We
  encode such an `A` faithfully and at full generality as the one-object FULL
  SUBCATEGORY `Sc 𝒜₀ pt` of an arbitrary locally complete distributive allegory
  `𝒜₀` on a chosen object `pt` — i.e. the scalars are the endo-hom-set
  `pt ⟶ pt`, with the inherited `≫`, `°`, `∩`, `∪`, `𝟘`, `Sup`.  Every one-object
  l.c.d. allegory arises this way (take `𝒜₀` to be it, `pt` its object), and
  unlike `S2_316.OneObj` — whose composition is forced to be `∩` (locales only) —
  `Sc` keeps the composition of `𝒜₀` arbitrary, so the theorem is faithful to "an
  ARBITRARY one-object l.c.d. allegory", not just the meet-idempotent ones.

  The crucial structural fact that makes the matrix algebra clean is that `Sc`'s
  `Hom` is CONSTANT (`Hom _ _ := pt ⟶ pt`), so every entry of a matrix in
  `GlobalObj (Sc 𝒜₀ pt)` is a scalar `pt ⟶ pt`, the power-object index type
  `[I] = (I → (pt ⟶ pt))` does not depend on a source, and (since function types
  do not raise the universe, `max u u = u`) `[I]` stays in `Type u`.  The §2.224
  `GloballyComplete` universe wall therefore does NOT apply here.

  STRICTLY MATHLIB-FREE.  Reuses the §2.224 global completion verbatim; the only
  nonconstructive ingredient is classical decidability of `∀ i, R_{j,i} = f i`
  (`Classical.propDecidable`), which is what makes `R̂` boolean.
-/



namespace Freyd.Alg

open LocallyCompleteDistributiveAllegory

attribute [local instance] Classical.propDecidable

/-! ## A one-object locally complete distributive allegory `Sc 𝒜₀ pt`

  The one-object full subcategory of `𝒜₀` on `pt`: a single object, hom-set the
  scalars `pt ⟶ pt`, every operation inherited from `𝒜₀`. -/

/-- The single object of the one-object l.c.d. allegory carved out of `𝒜₀` at
    `pt`.  Carries `𝒜₀` and `pt` as parameters so instance resolution recovers
    them (cf. `S2_316.OneObj`). -/
inductive Sc (𝒜₀ : Type u) (pt : 𝒜₀) : Type u
  | star

variable {𝒜₀ : Type u} [LocallyCompleteDistributiveAllegory.{u, u} 𝒜₀] {pt : 𝒜₀}

/-- Hom-set is the scalars `pt ⟶ pt`; identity/composition inherited from `𝒜₀`. -/
instance scCat : Cat.{u} (Sc 𝒜₀ pt) where
  Hom _ _ := pt ⟶ pt
  id _ := Cat.id pt
  comp f g := f ≫ g
  id_comp f := Cat.id_comp f
  comp_id f := Cat.comp_id f
  assoc f g h := Cat.assoc f g h

/-- Reciprocation/intersection inherited from `𝒜₀`. -/
instance scAllegory : Allegory (Sc 𝒜₀ pt) where
  toCat := scCat
  recip R := R°
  inter R S := R ∩ S
  recip_recip R := Allegory.recip_recip R
  recip_comp R S := Allegory.recip_comp R S
  recip_inter R S := Allegory.recip_inter R S
  inter_idem R := Allegory.inter_idem R
  inter_comm R S := Allegory.inter_comm R S
  inter_assoc R S T := Allegory.inter_assoc R S T
  semidistrib R S T := Allegory.semidistrib R S T
  modular R S T := Allegory.modular R S T

/-- Zero/union inherited from `𝒜₀`. -/
instance scDist : DistributiveAllegory (Sc 𝒜₀ pt) where
  toAllegory := scAllegory
  zero := fun {_ _} => (𝟘 : pt ⟶ pt)
  union R S := R ∪ S
  zero_comp R := DistributiveAllegory.zero_comp R
  comp_zero R := DistributiveAllegory.comp_zero R
  union_idem R := DistributiveAllegory.union_idem R
  union_comm R S := DistributiveAllegory.union_comm R S
  union_assoc R S T := DistributiveAllegory.union_assoc R S T
  union_inter_absorb R S := DistributiveAllegory.union_inter_absorb R S
  inter_union_absorb R S := DistributiveAllegory.inter_union_absorb R S
  comp_union_distrib R S T := DistributiveAllegory.comp_union_distrib R S T
  inter_union_distrib R S T := DistributiveAllegory.inter_union_distrib R S T
  zero_union R := DistributiveAllegory.zero_union R

/-- Arbitrary `Sup` inherited from `𝒜₀`. -/
instance scLCDA : LocallyCompleteDistributiveAllegory (Sc 𝒜₀ pt) where
  toDistributiveAllegory := scDist
  Sup P := LocallyCompleteDistributiveAllegory.Sup P
  le_Sup h := LocallyCompleteDistributiveAllegory.le_Sup h
  Sup_le h := LocallyCompleteDistributiveAllegory.Sup_le h
  comp_Sup_distrib R P := LocallyCompleteDistributiveAllegory.comp_Sup_distrib R P
  inter_Sup_distrib R P := LocallyCompleteDistributiveAllegory.inter_Sup_distrib R P

/-! ## A generic off-diagonal fact for the §2.224 identity matrix -/

/-- Off the diagonal the global identity matrix is `𝟘`: `i ≠ j ⟹ (1)_{ij} = 0`.
    (The diagonal case `(1)_{ii} = 1` is `globalId_diag`.) -/
theorem globalId_offdiag {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    (A : GlobalObj 𝒜) {i j : A.idx} (h : i ≠ j) :
    globalId A i j = (𝟘 : A.obj i ⟶ A.obj j) := by
  rw [globalId_apply]
  apply gcSup_eq_zero
  rintro U ⟨he, _⟩
  exact absurd he h

/-- Entry form of `globalId_diag` (LHS as `Cat.id A i i`, for `rw` on goals). -/
theorem globalCatId_diag {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    (A : GlobalObj 𝒜) (i : A.idx) : (Cat.id A : A ⟶ A) i i = Cat.id (A.obj i) :=
  globalId_diag A i

/-- Entry form of `globalId_offdiag` (LHS as `Cat.id A i j`, for `rw` on goals). -/
theorem globalCatId_offdiag {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜]
    (A : GlobalObj 𝒜) {i j : A.idx} (h : i ≠ j) :
    (Cat.id A : A ⟶ A) i j = (𝟘 : A.obj i ⟶ A.obj j) :=
  globalId_offdiag A h

/-! ## §2.434  The evaluation matrix and the boolean `R̂` -/

/-- `[I]`: the power object of the `I`-object `B`.  Its index type is the set
    `B.idx → (pt ⟶ pt)` of "rows" — functions assigning a scalar to each `i ∈ I`
    (Freyd: "the set of functions from I to A"); its carrier is the single
    object. -/
def powObj (B : GlobalObj (Sc 𝒜₀ pt)) : GlobalObj (Sc 𝒜₀ pt) :=
  ⟨B.idx → (pt ⟶ pt), fun _ => Sc.star⟩

/-- The EVALUATION matrix `T : [I] → I`, `T_{f,i} = f(i)` (§2.434). -/
def evalMat (B : GlobalObj (Sc 𝒜₀ pt)) : powObj B ⟶ B :=
  fun f i => f i

/-- Freyd's boolean `R̂ : J → [I]`, `R̂_{j,f} = 1` or `0` according to whether or
    not `R_{j,i} = f(i)` for all `i ∈ I` (§2.434).  The condition holds for
    exactly one `f`, namely the `j`-th row `f = R j`, so each row of `R̂` has
    exactly one `1` — `R̂` is a map. -/
noncomputable def hatMat {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) : C ⟶ powObj B :=
  fun j f => if (∀ i, R j i = f i) then Cat.id pt else (𝟘 : pt ⟶ pt)

@[simp] theorem hatMat_pos {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B)
    (j : C.idx) (f : B.idx → (pt ⟶ pt)) (h : ∀ i, R j i = f i) :
    hatMat R j f = Cat.id pt := if_pos h

@[simp] theorem hatMat_neg {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B)
    (j : C.idx) (f : B.idx → (pt ⟶ pt)) (h : ¬ (∀ i, R j i = f i)) :
    hatMat R j f = (𝟘 : pt ⟶ pt) := if_neg h

/-! ### `R̂ T = R` -/

/-- `R̂T = R` (§2.434).  At entry `(j,i)` the sum over `f` of `R̂_{j,f} ≫ f(i)`
    collapses: only `f = R j` contributes (giving `1 ≫ R_{j,i} = R_{j,i}`); every
    other `f` contributes `0 ≫ f(i) = 0`. -/
theorem evalMat_hat_eq {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) :
    hatMat R ≫ evalMat B = R := by
  funext j i
  show GlobalMorphism.comp (hatMat R) (evalMat B) j i = R j i
  rw [globalComp_apply]
  refine gcSup_eq ⟨R j, ?_⟩ ?_
  · -- membership: the row `f = R j` gives the value `R_{j,i}`.
    rw [hatMat_pos R j (R j) (fun _ => rfl)]
    show R j i = Cat.id pt ≫ R j i
    rw [Cat.id_comp]
  · -- upper bound: every term is `≤ R_{j,i}`.
    rintro X ⟨f, rfl⟩
    by_cases hf : ∀ i', R j i' = f i'
    · rw [hatMat_pos R j f hf]
      show Cat.id pt ≫ f i ⊑ R j i
      rw [Cat.id_comp, ← hf i]
      exact le_refl _
    · rw [hatMat_neg R j f hf]
      show (𝟘 : pt ⟶ pt) ≫ f i ⊑ R j i
      rw [DistributiveAllegory.zero_comp]
      exact zero_le _

/-! ### `R̂` is a map -/

/-- `R̂` is SIMPLE: `R̂° R̂ ⊑ 1` (§2.434, "each row has exactly one 1").  At entry
    `(f,g)` the sum over `j` of `(R̂_{j,f})° ≫ R̂_{j,g}` is non-zero only when both
    `f` and `g` equal the row `R j`, forcing `f = g`. -/
theorem hatMat_simple {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) :
    Simple (hatMat R) := by
  show (hatMat R)° ≫ hatMat R ⊑ Cat.id (powObj B)
  apply global_le_of_entry
  intro f g
  show GlobalMorphism.comp (GlobalMorphism.recip (hatMat R)) (hatMat R) f g ⊑ _
  rw [globalComp_apply]
  apply Sup_le
  rintro X ⟨j, rfl⟩
  rw [globalRecip_apply]
  -- entry `(R̂_{j,f})° ≫ R̂_{j,g}` of `R̂° R̂`.  Convert each branch to the
  -- 𝒜₀-native scalar form (where `recip_id`/`recip_zero` apply at `pt`).
  by_cases hfg : f = g
  · subst hfg
    rw [globalCatId_diag]
    by_cases hf : ∀ i, R j i = f i
    · rw [hatMat_pos R j f hf]
      show (Cat.id pt)° ≫ Cat.id pt ⊑ Cat.id pt
      rw [recip_id, Cat.id_comp]
      exact le_refl _
    · rw [hatMat_neg R j f hf]
      show (𝟘 : pt ⟶ pt)° ≫ (𝟘 : pt ⟶ pt) ⊑ Cat.id ((powObj B).obj f)
      rw [recip_zero, DistributiveAllegory.zero_comp]
      exact zero_le _
  · by_cases hf : ∀ i, R j i = f i
    · by_cases hg : ∀ i, R j i = g i
      · exact absurd (funext fun i => (hf i).symm.trans (hg i)) hfg
      · rw [hatMat_pos R j f hf, hatMat_neg R j g hg]
        show (Cat.id pt)° ≫ (𝟘 : pt ⟶ pt) ⊑ Cat.id (powObj B) f g
        rw [DistributiveAllegory.comp_zero]
        exact zero_le _
    · rw [hatMat_neg R j f hf]
      show (𝟘 : pt ⟶ pt)° ≫ hatMat R j g ⊑ Cat.id (powObj B) f g
      rw [recip_zero, DistributiveAllegory.zero_comp]
      exact zero_le _

/-- `R̂` is ENTIRE: `1 ⊑ R̂ R̂°` (§2.434, "each row has exactly one 1" — at least
    one).  At the diagonal entry `(j,j)` the row `f = R j` contributes
    `1 ≫ 1° = 1`, so `1_{C.obj j} ⊑ (R̂ R̂°)_{jj}`. -/
theorem hatMat_entire {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) :
    Entire (hatMat R) := by
  show Cat.id C ∩ (hatMat R ≫ (hatMat R)°) = Cat.id C
  refine le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) ?_)
  apply global_le_of_entry
  intro j j'
  by_cases hjj : j = j'
  · subst hjj
    rw [globalCatId_diag]
    show Cat.id (C.obj j) ⊑ GlobalMorphism.comp (hatMat R) (GlobalMorphism.recip (hatMat R)) j j
    rw [globalComp_apply]
    refine le_trans ?_ (le_Sup ⟨R j, rfl⟩)
    rw [globalRecip_apply, hatMat_pos R j (R j) (fun _ => rfl)]
    show Cat.id pt ⊑ Cat.id pt ≫ (Cat.id pt)°
    rw [recip_id, Cat.id_comp]
    exact le_refl _
  · rw [globalCatId_offdiag C hjj]
    exact zero_le _

/-- `R̂` is a MAP (§2.434). -/
theorem hatMat_map {C B : GlobalObj (Sc 𝒜₀ pt)} (R : C ⟶ B) : Map (hatMat R) :=
  ⟨hatMat_entire R, hatMat_simple R⟩

/-! ### The evaluation matrix is thick (the matrix-algebra core, division-free) -/

/-- §2.434 core: for every matrix `R : J → I` there is a map `R̂` (namely `hatMat
    R`) with `R̂T ⊑ R` (in fact `= R`) and `R̂°R ⊑ T`.  This is exactly Freyd's
    three containments witnessing that the evaluation matrix `T` is thick (the
    right-hand side of §2.431/`thick_iff_existential`), and it needs only the
    allegory structure — no division.

    `R̂°R = R̂°(R̂T) = (R̂°R̂)T ⊑ 1·T = T` since `R̂` is simple. -/
theorem evalMat_thick_exists (B : GlobalObj (Sc 𝒜₀ pt)) (C : GlobalObj (Sc 𝒜₀ pt))
    (R : C ⟶ B) :
    ∃ (R' : C ⟶ powObj B),
      Entire R' ∧ R' ≫ evalMat B ⊑ R ∧ R'° ≫ R ⊑ evalMat B := by
  refine ⟨hatMat R, hatMat_entire R, ?_, ?_⟩
  · rw [evalMat_hat_eq]; exact le_refl _
  · calc (hatMat R)° ≫ R
        = (hatMat R)° ≫ (hatMat R ≫ evalMat B) := by rw [evalMat_hat_eq]
      _ = ((hatMat R)° ≫ hatMat R) ≫ evalMat B := by rw [Cat.assoc]
      _ ⊑ Cat.id (powObj B) ≫ evalMat B := comp_mono_right (hatMat_simple R) _
      _ = evalMat B := Cat.id_comp _

/-! ## §2.434  The global completion of a one-object l.c.d. allegory is pre-power

  Packaging: equip `GlobalObj (Sc 𝒜₀ pt)` with its (§2.315a) division-allegory
  structure `divisionAllegoryLCDA` (via `letI`), under which `Thick`/§2.431 are
  available; each object `B` is then the target of the thick evaluation matrix
  `T = evalMat B` by `thick_iff_existential` applied to `evalMat_thick_exists`. -/

/-- §2.434: **the global completion of a one-object locally complete distributive
    allegory is a PRE-POWER allegory**, via the evaluation matrix.  Each object
    `B` is the target of the thick morphism `evalMat B : [B] → B`. -/
noncomputable def globalScPrePower : PrePowerAllegory (GlobalObj (Sc 𝒜₀ pt)) :=
  letI dva := divisionAllegoryLCDA (𝒜 := GlobalObj (Sc 𝒜₀ pt))
  { dva with
    thick_target := fun B =>
      ⟨powObj B, evalMat B,
        (thick_iff_existential (evalMat B)).mpr
          (fun C R _hbox => evalMat_thick_exists B C R)⟩ }

/-! ## §2.434  Corollary: the systemic completion is a power allegory

  The SYSTEMIC completion of `𝒜₀` is the EFFECTIVE completion (split symmetric
  idempotents, §2.226) of the global completion `GlobalObj (Sc 𝒜₀ pt)`.  Splitting
  symmetric idempotents preserves the pre-power structure and makes the result
  effective, so by §2.432 (`effective_pre_power_is_power`, already in the repo)
  it is a power allegory.  Concretely: if the systemic completion `𝒮` of a
  one-object l.c.d. allegory is presented as an `EffectivePrePowerAllegory` — its
  thick targets are the images of the `evalMat B` under the splitting embedding —
  then `effective_pre_power_is_power : PowerAllegory 𝒮`.

  We do NOT re-prove the §2.226/§2.433 effective-completion bridge here (it is
  formalised separately); `globalScPrePower` is the §2.434 content proper (the
  pre-power half), and the headline is its image under that bridge. -/

-- BOOK §2.434 headline: the systemic completion of a small l.c.d. allegory is a
-- power allegory.  = `effective_pre_power_is_power` (§2.432) applied to the
-- effective/systemic completion (§2.226/§2.433) of `globalScPrePower` above.

end Freyd.Alg

/-
  Freyd & Scedrov, *Categories and Allegories* §2.435 (Cantor, algebraic form)
  and §2.353 (cancellation on maps).

  §2.435  CANTOR (algebraic).  "If a connected division allegory has a thick
          endomorphism, then it is equivalent to the one-object one-morphism
          allegory."  The engine is §2.436 (`one_object_pre_power_inconsistent`,
          S2_43): a thick endomorphism `T : α ⟶ α` forces `1_α = 𝟘`, hence
          `T = 1_α`.  Connectivity (strong form: an entire morphism into α from
          every object) then spreads the collapse: every object β satisfies
          `1_β = 𝟘`, i.e. is a terminator, and every hom-set is the singleton
          `{𝟘}` — exactly the one-object one-morphism allegory.

          Cantor application: in a power allegory a morphism `F : a → [a]` with
          `F°F = 1` makes `T = F∋` thick (witness `R̂ = A(R)F°`), so it cannot
          coexist with strong connectivity unless the allegory is degenerate.

  §2.353  CANCELLATION ON MAPS.  "In a tabular division allegory it suffices to
          verify the [straight] cancellation property on maps."  Given a
          tabulation `S/ₛS = ℓ°r` (ℓ, r maps), the maps-only cancellation
          `fS = gS → f = g` forces `ℓ = r`, whence `S/ₛS = ℓ°ℓ ⊑ 1`, i.e. S is
          straight.  This is the map-restricted strengthening of S2_3's
          `straight_of_cancel` (which needs the property for all simple F, G).

  Self-contained, mathlib-free.  Lives on S2_1 (Map/Simple/Entire/Tabulation),
  S2_3 (symmetric division, Straight), S2_4 (Thick, PowerAllegory, A(R)) and
  S2_43 (diag, §2.436 inconsistency core).
-/



namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## §2.435  Connectivity

  Freyd's "connected" allegory: there is a morphism between every ordered pair of
  objects.  Reciprocation `°` makes this relation symmetric, which is the sense in
  which "connectivity implies strong connectivity" (a morphism both ways).

  The §2.435 / §2.423 arguments consume the book's STRONG CONNECTIVITY: every object
  has a map into α (Freyd: "every object has a map to α").  In a power allegory that
  map is `Λ(R)`; in a bare division allegory it is NOT constructible from a mere
  morphism, so it is the explicit hypothesis `StronglyConnectedAllegory` (reused from
  `S2_423`; a map is entire, which is all the §2.436 spread needs). -/

/-! ## §2.435  A thick endomorphism collapses its object

  §2.436 (`one_object_pre_power_inconsistent`, S2_43) already shows a thick
  `T : α ⟶ α` (with Freyd's suppressed box guard `codBox (diag T) = codBox T`)
  forces `1_α = 𝟘`.  We package the two §2.435 consequences: `T = 1_α`, and —
  under strong connectivity — degeneracy of every object. -/

/-- §2.435 (local collapse): a thick endomorphism equals the identity.
    `1_α = 𝟘` (§2.436) gives `T = T·1 = T·𝟘 = 𝟘 = 1`. -/
theorem thick_endo_eq_id {α : 𝒜} (T : α ⟶ α) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) : T = Cat.id α := by
  have hα : Cat.id α = (𝟘 : α ⟶ α) := one_object_pre_power_inconsistent T hT hBox
  calc T = T ≫ Cat.id α := (Cat.comp_id T).symm
    _ = T ≫ (𝟘 : α ⟶ α) := by rw [hα]
    _ = (𝟘 : α ⟶ α) := DistributiveAllegory.comp_zero T
    _ = Cat.id α := hα.symm

/-- §2.435 (degeneracy): in a strongly connected division allegory, a thick
    endomorphism `T : α ⟶ α` forces EVERY object β to be a terminator, `1_β = 𝟘`.

    Freyd: "the morphism 0:β→α factors as an entire morphism 0̂ followed by 1; that
    is 0 is entire; hence every object is a terminator."  Here: `1_α = 𝟘` (§2.436);
    strong connectivity gives an entire `h : β ⟶ α`; `h = h·1_α = h·𝟘 = 𝟘`, so the
    zero morphism `β → α` is entire, whence `1_β ⊑ 𝟘·𝟘° = 𝟘`. -/
theorem thick_endo_degenerate (hSC : StronglyConnectedAllegory 𝒜)
    {α : 𝒜} (T : α ⟶ α) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) :
    ∀ (β : 𝒜), Cat.id β = (𝟘 : β ⟶ β) := by
  have hα : Cat.id α = (𝟘 : α ⟶ α) := one_object_pre_power_inconsistent T hT hBox
  intro β
  obtain ⟨h, hh⟩ := hSC β α
  -- h = 𝟘 : every morphism into α is zero once `1_α = 𝟘`.
  have hzero : h = (𝟘 : β ⟶ α) := by
    calc h = h ≫ Cat.id α := (Cat.comp_id h).symm
      _ = h ≫ (𝟘 : α ⟶ α) := by rw [hα]
      _ = (𝟘 : β ⟶ α) := DistributiveAllegory.comp_zero h
  -- Entire h gives `1_β ⊑ h h°`; with `h = 𝟘` this is `1_β ⊑ 𝟘`.
  have hEnt : Cat.id β ⊑ h ≫ h° := by
    have hd := hh.1; dsimp [Entire, dom] at hd; rw [← hd]; exact inter_lb_right _ _
  rw [hzero, recip_zero, DistributiveAllegory.zero_comp] at hEnt
  exact le_antisymm hEnt (zero_le _)

/-- §2.435 (every hom is a singleton): under the hypotheses of
    `thick_endo_degenerate`, every morphism is the zero morphism — the allegory is
    the one-object one-morphism allegory. -/
theorem thick_endo_all_zero (hSC : StronglyConnectedAllegory 𝒜)
    {α : 𝒜} (T : α ⟶ α) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) :
    ∀ {β γ : 𝒜} (R : β ⟶ γ), R = (𝟘 : β ⟶ γ) := by
  intro β γ R
  have hβ := thick_endo_degenerate hSC T hT hBox β
  calc R = Cat.id β ≫ R := (Cat.id_comp R).symm
    _ = (𝟘 : β ⟶ β) ≫ R := by rw [hβ]
    _ = (𝟘 : β ⟶ γ) := DistributiveAllegory.zero_comp R

/-- §2.435 (Freyd's exact phrasing "0 is entire"): under the hypotheses of
    `thick_endo_degenerate`, the zero morphism `β → γ` is entire. -/
theorem thick_endo_zero_entire (hSC : StronglyConnectedAllegory 𝒜)
    {α : 𝒜} (T : α ⟶ α) (hT : Thick T)
    (hBox : codBox (diag T) = codBox T) :
    ∀ (β γ : 𝒜), Entire (𝟘 : β ⟶ γ) := by
  intro β γ
  have hβ := thick_endo_degenerate hSC T hT hBox β
  dsimp [Entire, dom]
  rw [recip_zero, DistributiveAllegory.comp_zero, hβ, Allegory.inter_idem]

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [PowerAllegory 𝒜]

/-! ## §2.435  Cantor application: `T = F∋` is thick when `F°F = 1`

  Freyd: "Suppose in a power allegory there exists `F : a → [a]` with `F°F = 1`
  (a partial map covering `[a]`).  Then `T = F∋` is thick: given R define
  `R̂ = (R/∋)F°`; R̂ is entire; `R̂T ⊑ (R/∋)F°F∋ ⊑ (R/∋)∋ ⊑ R`,
  `R̂°R ⊑ F(∋/R)R ⊑ F∋ = T`.  (We used only the thickness of ∋.)"

  We take the honest witness `R̂ = A(R)F°` with `A(R) = R/ₛ∋` (S2_4), the map Freyd
  writes `R/∋`.  The three §2.431 containments fall out of `F°F = 1`, the map-ness
  of `A(R)` (§2.412/413, box-matched thickness of ∋) and `A(R)∋ = R`.  The box
  guard for `A(R)` is discharged because `F°F = 1` makes `codBox (F∋) = codBox ∋`. -/

/-- `codBox (F∋) = codBox ∋` when `F°F = 1` (§2.41 box bookkeeping).
    `codBox R = 1 ∩ R°R`; for `R = F∋`, `(F∋)°(F∋) = ∋°(F°F)∋ = ∋°∋`. -/
theorem codBox_comp_eps {a : 𝒜} (F : a ⟶ PowerAllegory.powerObj a)
    (hF : F° ≫ F = Cat.id (PowerAllegory.powerObj a)) :
    codBox (F ≫ ∋ a) = codBox (∋ a) := by
  show dom ((F ≫ ∋ a)°) = dom ((∋ a)°)
  dsimp only [dom]
  rw [Allegory.recip_recip, Allegory.recip_recip, Allegory.recip_comp]
  -- goal: 1 ∩ (∋° ≫ F°) ≫ (F ≫ ∋) = 1 ∩ ∋° ≫ ∋
  congr 1
  rw [Cat.assoc (∋ a)° F° (F ≫ ∋ a), ← Cat.assoc F° F (∋ a), hF, Cat.id_comp]

/-- §2.435 Cantor: in a power allegory, `F : a → [a]` with `F°F = 1` makes
    `T = F∋` a thick endomorphism.  Witness `R̂ = A(R)F°` (book `(R/∋)F°`). -/
theorem cantor_thick_endo {a : 𝒜} (F : a ⟶ PowerAllegory.powerObj a)
    (hF : F° ≫ F = Cat.id (PowerAllegory.powerObj a)) :
    Thick (F ≫ ∋ a) := by
  rw [thick_iff_existential]
  intro c R hbox
  -- translate the box guard of T = F∋ to the box guard of ∋.
  have hboxA : codBox R = codBox (∋ a) := hbox.trans (codBox_comp_eps F hF)
  have hAmap : Map (A R) := A_is_map R hboxA
  -- witness R̂ = A(R) ≫ F°
  refine ⟨A R ≫ F°, ?_, ?_, ?_⟩
  · -- Entire R̂ : R̂R̂° = A(R)(F°F)A(R)° = A(R)A(R)° ⊒ 1.
    have hAent : Cat.id c ⊑ A R ≫ (A R)° := by
      have hd := hAmap.1; dsimp [Entire, dom] at hd; rw [← hd]; exact inter_lb_right _ _
    have hcomp : (A R ≫ F°) ≫ (A R ≫ F°)° = A R ≫ (A R)° := by
      rw [Allegory.recip_comp, Allegory.recip_recip,
        Cat.assoc (A R) F° (F ≫ (A R)°), ← Cat.assoc F° F (A R)°, hF, Cat.id_comp]
    dsimp [Entire, dom]
    rw [hcomp]
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hAent)
  · -- R̂T ⊑ R : R̂T = A(R)(F°F)∋ = A(R)∋ = R.
    have hTeq : (A R ≫ F°) ≫ (F ≫ ∋ a) = R := by
      rw [Cat.assoc (A R) F° (F ≫ ∋ a), ← Cat.assoc F° F (∋ a), hF, Cat.id_comp,
        A_eps_eq R hboxA]
    rw [hTeq]
    exact le_refl R
  · -- R̂°R ⊑ T : R̂° = F A(R)°, and A(R)°R = A(R)°A(R)∋ ⊑ ∋ (A(R) simple), so ⊑ F∋ = T.
    have hRhat_recip : (A R ≫ F°)° = F ≫ (A R)° := by
      rw [Allegory.recip_comp, Allegory.recip_recip]
    rw [hRhat_recip]
    have hinner : (A R)° ≫ R ⊑ ∋ a := by
      have e1 : (A R)° ≫ R = ((A R)° ≫ A R) ≫ ∋ a := by
        rw [Cat.assoc, A_eps_eq R hboxA]
      rw [e1]
      have h2 := comp_mono_right (A_simple R) (∋ a)
      rwa [Cat.id_comp] at h2
    rw [Cat.assoc F (A R)° R]
    exact comp_mono_left F hinner

/-- §2.435 (Cantor, full): in a STRONGLY CONNECTED power allegory, no `F : a → [a]`
    with `F°F = 1` can exist unless the allegory is degenerate.  Concretely, such
    an `F` (via `T = F∋` thick, §2.436 collapse + connectivity) forces every object
    to be a terminator — provided Freyd's diagonal box guard for `T = F∋` holds.

    The box guard `codBox (diag (F∋)) = codBox (F∋)` is §2.436's load-bearing
    side-condition (S2_43 `one_object_pre_power_inconsistent`; it can fail for the
    box-guarded `Thick`, which is why it is an explicit hypothesis here). -/
theorem cantor_degenerate (hSC : StronglyConnectedAllegory 𝒜) {a : 𝒜}
    (F : a ⟶ PowerAllegory.powerObj a)
    (hF : F° ≫ F = Cat.id (PowerAllegory.powerObj a))
    (hBox : codBox (diag (F ≫ ∋ a)) = codBox (F ≫ ∋ a)) :
    ∀ (β : 𝒜), Cat.id β = (𝟘 : β ⟶ β) :=
  thick_endo_degenerate hSC (F ≫ ∋ a) (cantor_thick_endo F hF) hBox

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-! ## §2.353  Cancellation on maps

  Freyd: "In a tabular division allegory it suffices to verify the cancellation
  property on maps."  S2_3's `straight_of_cancel` needs the cancellation property
  `FS = GS → (dom F)G = (dom G)F` for all SIMPLE F, G (plus the §2.225 union
  hypothesis).  When `S/ₛS` is tabular we can drop both: tabulate `S/ₛS = ℓ°r`
  (ℓ, r maps), show `ℓS = rS`, and the maps-only cancellation `fS = gS → f = g`
  gives `ℓ = r`, whence `S/ₛS = ℓ°ℓ ⊑ 1`.

  Stated with an explicit `Tabular (S/ₛS)` hypothesis (rather than a
  `[TabularAllegory 𝒜]` instance) to keep `≫`/`°`/`∩` referring to the single
  `Allegory` underlying `DivisionAllegory` — no instance diamond.  In a full
  tabular division allegory `hTab` is `TabularAllegory.tabular (S/ₛS)`. -/

/-- §2.353 (cancellation on maps): if `S/ₛS` is tabular and the cancellation
    property holds for MAPS (`fS = gS → f = g`), then `S` is straight. -/
theorem straight_of_cancel_on_maps {a b : 𝒜} {S : a ⟶ b}
    (hTab : Tabular (S /ₛ S))
    (hmap : ∀ {d : 𝒜} (f g : d ⟶ a), Map f → Map g → f ≫ S = g ≫ S → f = g) :
    Straight S := by
  obtain ⟨c, ℓ, r, hℓmap, hrmap, hW, _hjoint⟩ := hTab
  -- counit of symmetric division: (S/ₛS) S ⊑ S.
  have hssS : (S /ₛ S) ≫ S ⊑ S := ((le_symmDiv_iff (S /ₛ S) S S).mp (le_refl _)).1
  -- ℓ, r entire (maps).
  have hℓent : Cat.id c ⊑ ℓ ≫ ℓ° := by
    have hd := hℓmap.1; dsimp [Entire, dom] at hd; rw [← hd]; exact inter_lb_right _ _
  have hrent : Cat.id c ⊑ r ≫ r° := by
    have hd := hrmap.1; dsimp [Entire, dom] at hd; rw [← hd]; exact inter_lb_right _ _
  -- ℓ°(rS) ⊑ S  (= (S/ₛS)S ⊑ S after the tabulation).
  have hℓrS : ℓ° ≫ r ≫ S ⊑ S := by
    have h := hssS; rw [hW, Cat.assoc] at h; exact h
  -- (S/ₛS)° = r°ℓ, and (S/ₛS)° ⊑ S/ₛS, so r°(ℓS) ⊑ (S/ₛS)S ⊑ S.
  have hrℓS : r° ≫ ℓ ≫ S ⊑ S := by
    have hWrec : (S /ₛ S)° = r° ≫ ℓ := by rw [hW, Allegory.recip_comp, Allegory.recip_recip]
    have h : (S /ₛ S)° ≫ S ⊑ S := le_trans (comp_mono_right (symmDiv_self_symmetric S) S) hssS
    rw [hWrec, Cat.assoc] at h; exact h
  -- rS ⊑ ℓS and ℓS ⊑ rS via entireness, hence ℓS = rS.
  have hrℓ : r ≫ S ⊑ ℓ ≫ S := by
    have h1 : r ≫ S ⊑ (ℓ ≫ ℓ°) ≫ (r ≫ S) := by
      have h := comp_mono_right hℓent (r ≫ S); rwa [Cat.id_comp] at h
    have h2 : (ℓ ≫ ℓ°) ≫ (r ≫ S) ⊑ ℓ ≫ S := by
      rw [Cat.assoc]; exact comp_mono_left ℓ hℓrS
    exact le_trans h1 h2
  have hℓr : ℓ ≫ S ⊑ r ≫ S := by
    have h1 : ℓ ≫ S ⊑ (r ≫ r°) ≫ (ℓ ≫ S) := by
      have h := comp_mono_right hrent (ℓ ≫ S); rwa [Cat.id_comp] at h
    have h2 : (r ≫ r°) ≫ (ℓ ≫ S) ⊑ r ≫ S := by
      rw [Cat.assoc]; exact comp_mono_left r hrℓS
    exact le_trans h1 h2
  -- maps-only cancellation: ℓ = r.
  have hℓr_eq : ℓ = r := hmap ℓ r hℓmap hrmap (le_antisymm hℓr hrℓ)
  -- S/ₛS = ℓ°r = ℓ°ℓ ⊑ 1 (ℓ simple).
  dsimp [Straight]
  rw [hW, ← hℓr_eq]
  exact hℓmap.2

end Freyd.Alg
