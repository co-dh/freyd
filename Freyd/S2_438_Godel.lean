import Freyd.S2_10
import Freyd.S2_20

universe v u

/-
  Freyd & Scedrov, *Categories and Allegories* §2.438 — Gödel's second
  incompleteness theorem in allegory form.

  ## What the book says (§2.438)

  Suppose there were a RECURSIVE set of axioms for elementary number theory
  strong enough to yield the Peano axioms, and strong enough that we can PROVE
  that the set of Gödel-numbers of its provable consequences is a PROPER subset
  of the set of Gödel-numbers of well-formed sentences (a "simulated consistency
  proof").  Let `A` be the one-object allegory whose morphisms are named by
  recipes for recursively-enumerable relations, two recipes naming the SAME
  morphism iff they are provably coextensive.  Freyd shows `A` has just ONE
  morphism — i.e. `1 = 𝟘` — which (all morphisms being equal) means the theory
  is inconsistent.  This is Gödel's second incompleteness theorem.

  Freyd's argument (§2.438) reuses the §2.436/§2.437 diagonal collapse:

    We may take `T` and the unary operation `R̂` as in §2.437, so that
        (i)   `1 ⊑ R̂ R̂°`,      (ii) `R̂ T ⊑ R`,      (iii) `R̂° R ⊑ T`.
    We do NOT need full division; we need only the existence of `0/(1∩T)` for
    the ONE relevant morphism `R`.  By listing all proofs we find a recipe for a
    morphism `R` with  `m R n  iff it is provably not the case that n T n`.  Then
        (div)  if `S(1∩T) = 0`  then `S ⊑ R`      (R is a lax right-divisor `0/(1∩T)`),
    and the hypothesised simulated consistency proof directly yields
        (cons) `R(1∩T) = 0`.
    "Just as in [2.436] we can now show that `R̂ = 0`, hence that `1 = 0`."

  ## What is formalized here (the honest, reachable deliverable)

  The repo has NO first-order theory of Peano arithmetic and NO provability
  predicate for such a theory (recon: `grep -riE "Peano|Provable|provability|
  firstOrder"` finds only §1.97 NNO/Peano-*property* topos machinery and the
  §2.16 `encCode`/`acceptN` recursion-witness checker — none of which is a formal
  first-order theory + `Prov`).  Building that is a separate multi-file
  subproject (see the note at the end of this file).

  So we formalize Freyd's argument at the ALLEGORY level, deferring PA: the
  §2.437 "hat" structure `(T, R, R̂)` and the §2.438 Gödel/consistency hypotheses
  `(div)`,`(cons)` on `R` are taken ABSTRACTLY (as a structure + a Prop), and we
  prove the collapse `1 = 𝟘` fully, Sorry-free, in ANY distributive allegory —
  crucially WITHOUT assuming a division allegory (Freyd's "we do not need
  division in general").  This captures Freyd's §2.438 reduction exactly; the
  remaining content is the (independent) construction of a concrete such
  `(T, R, R̂)` from a recursive PA + its r.e. provability predicate.
-/

namespace Freyd.Godel

open Freyd Freyd.Alg

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-! ## Codomain factorization (pure-allegory, no division)

  `R ⊑ R ≫ (1 ∩ R°R)` — the reciprocal of the left-domain factorization
  (§2.122).  This is the one geometric input to the diagonal chain.  It is the
  same statement as `Freyd.Alg.le_comp_codom` in `S2_43.lean`, but that copy is
  stated for a `DivisionAllegory`; §2.438 must avoid division, so we re-derive it
  here for a plain `DistributiveAllegory` (the proof uses only the modular law
  and reciprocal identities — no division). -/
theorem le_comp_codom {a b : 𝒜} (R : a ⟶ b) :
    R ⊑ R ≫ (Cat.id b ∩ R° ≫ R) := by
  have h : R° ⊑ (Cat.id b ∩ R° ≫ R) ≫ R° := by
    have hm := modular_le (Cat.id b) (R°) (R°)
    rw [Cat.id_comp, Allegory.inter_idem, Allegory.recip_recip] at hm
    exact hm
  have hr := recip_mono h
  rw [Allegory.recip_comp, Allegory.recip_recip] at hr
  rwa [Allegory.recip_inter, recip_id, Allegory.recip_comp, Allegory.recip_recip] at hr

/-! ## The §2.437 "hat" structure

  The recipes `T`, `R` and the §2.437 unary operation `R̂ = hat` on a single
  object `a`, packaging the three §2.437/§2.438 containments (i)–(iii). -/
structure HatWitness (a : 𝒜) where
  /-- The recursive-enumeration morphism `T` (§2.437). -/
  T : a ⟶ a
  /-- The specific "Gödel diagonal" morphism `R` (§2.438: `mRn` iff provably not `nTn`). -/
  R : a ⟶ a
  /-- The §2.437 unary operation `R̂` applied to `R`. -/
  hat : a ⟶ a
  /-- (i) `R̂` is entire: `1 ⊑ R̂ R̂°`. -/
  entire : Cat.id a ⊑ hat ≫ hat°
  /-- (ii) `R̂ T ⊑ R`. -/
  hatT_le : hat ≫ T ⊑ R
  /-- (iii) `R̂° R ⊑ T`. -/
  hatR_le : hat° ≫ R ⊑ T

/-! ## The §2.438 Gödel / consistency hypotheses on `R`

  The two facts §2.438 extracts about the diagonal recipe `R`, RELATIVE to `T`:

  * `divisor` — `R` is a lax right-divisor `𝟘/(1∩T)`: whenever `S(1∩T) = 𝟘` we
    have `S ⊑ R`.  This is Freyd's "we need only show the existence of
    `0/(1∩T)`" — the ONE division instance, taken as a hypothesis rather than
    built from a full division allegory.
  * `consistency` — `R(1∩T) = 𝟘`.  This is exactly the content the hypothesised
    simulated consistency proof supplies ("directly allows us to prove that
    `R(1∩T)=0`"). -/
structure GodelHyp [DistributiveAllegory 𝒜] {a : 𝒜} (T R : a ⟶ a) : Prop where
  /-- `R` is the lax right-divisor `𝟘/(1∩T)` (the sole division instance needed). -/
  divisor : ∀ S : a ⟶ a, S ≫ (Cat.id a ∩ T) = (𝟘 : a ⟶ a) → S ⊑ R
  /-- The simulated consistency proof yields `R(1∩T) = 𝟘`. -/
  consistency : R ≫ (Cat.id a ∩ T) = (𝟘 : a ⟶ a)

/-! ## §2.438  The collapse: `A` has just one morphism

  Freyd: "Just as in [2.436] we can now show that `R̂ = 0`, hence that `1 = 0`."
  The two diagonal chains, verbatim from §2.436/§2.438:

    (A)  `R̂(1∩T) = R̂(1∩T)² ⊑ R̂T(1∩T) ⊑ R(1∩T) = 𝟘`  ⟹ (via `divisor`) `R̂ ⊑ R`;
    (B)  `R̂ ⊑ R̂(1∩R̂°R̂) ⊑ R(1∩R̂°R) ⊑ R(1∩T) = 𝟘`         ⟹ `R̂ = 𝟘`;

  and entireness `1 ⊑ R̂R̂°` then forces `1 ⊑ 𝟘`. -/

/-- **§2.438 (Gödel's second incompleteness theorem, allegory form).**

    In any distributive allegory, given the §2.437 hat structure `W` on an object
    `a` (recipes `T`, `R` and the operation `R̂` with `1 ⊑ R̂R̂°`, `R̂T ⊑ R`,
    `R̂°R ⊑ T`) and the §2.438 Gödel/simulated-consistency hypotheses `H` on `R`
    (the lax divisor `𝟘/(1∩T)` property and `R(1∩T) = 𝟘`), the identity collapses:
    `1_a = 𝟘`.  NO division allegory is assumed — Freyd's "we do not need division
    in general, we need only show the existence of `0/(1∩T)`". -/
theorem godel_collapse {a : 𝒜} (W : HatWitness a) (H : GodelHyp W.T W.R) :
    Cat.id a = (𝟘 : a ⟶ a) := by
  -- The coreflexive cut c = 1 ∩ T is idempotent and below T.
  have hc_coref : Coreflexive (Cat.id a ∩ W.T) := inter_lb_left _ _
  have hc_idem : (Cat.id a ∩ W.T) ≫ (Cat.id a ∩ W.T) = Cat.id a ∩ W.T :=
    (coreflexive_symmetric_idempotent hc_coref).2
  have hc_le_T : Cat.id a ∩ W.T ⊑ W.T := inter_lb_right _ _
  -- Chain A:  R̂(1∩T) = R̂(1∩T)² ⊑ R̂T(1∩T) ⊑ R(1∩T) = 𝟘.
  -- (`⊑` has no registered `Trans` instance, so we chain with `le_trans`, not `calc`.)
  have a1 : W.hat ≫ (Cat.id a ∩ W.T) ⊑ W.hat ≫ (W.T ≫ (Cat.id a ∩ W.T)) := by
    have h := comp_mono_left W.hat (comp_mono_right hc_le_T (Cat.id a ∩ W.T))
    rwa [hc_idem] at h
  have a2 : W.hat ≫ (W.T ≫ (Cat.id a ∩ W.T)) ⊑ W.R ≫ (Cat.id a ∩ W.T) := by
    rw [← Cat.assoc]; exact comp_mono_right W.hatT_le (Cat.id a ∩ W.T)
  have chainA : W.hat ≫ (Cat.id a ∩ W.T) ⊑ W.R ≫ (Cat.id a ∩ W.T) := le_trans a1 a2
  have hRhc_zero : W.hat ≫ (Cat.id a ∩ W.T) = (𝟘 : a ⟶ a) := by
    rw [H.consistency] at chainA; exact le_antisymm chainA (zero_le _)
  -- Divisor property (existence of 𝟘/(1∩T)) gives R̂ ⊑ R.
  have hRh_le_R : W.hat ⊑ W.R := H.divisor W.hat hRhc_zero
  -- Chain B:  R̂ ⊑ R̂(1∩R̂°R̂) ⊑ R(1∩R̂°R) ⊑ R(1∩T) = 𝟘.
  have inner1 : Cat.id a ∩ W.hat° ≫ W.hat ⊑ Cat.id a ∩ W.hat° ≫ W.R :=
    le_inter (inter_lb_left _ _)
      (le_trans (inter_lb_right _ _) (comp_mono_left W.hat° hRh_le_R))
  have inner2 : Cat.id a ∩ W.hat° ≫ W.R ⊑ Cat.id a ∩ W.T :=
    le_inter (inter_lb_left _ _) (le_trans (inter_lb_right _ _) W.hatR_le)
  have b1 : W.hat ⊑ W.hat ≫ (Cat.id a ∩ W.hat° ≫ W.hat) := le_comp_codom W.hat
  have b2 : W.hat ≫ (Cat.id a ∩ W.hat° ≫ W.hat) ⊑ W.R ≫ (Cat.id a ∩ W.hat° ≫ W.R) :=
    le_trans (comp_mono_right hRh_le_R _) (comp_mono_left W.R inner1)
  have b3 : W.R ≫ (Cat.id a ∩ W.hat° ≫ W.R) ⊑ W.R ≫ (Cat.id a ∩ W.T) :=
    comp_mono_left W.R inner2
  have chainB : W.hat ⊑ W.R ≫ (Cat.id a ∩ W.T) := le_trans b1 (le_trans b2 b3)
  have hRh_zero : W.hat = (𝟘 : a ⟶ a) := by
    rw [H.consistency] at chainB; exact le_antisymm chainB (zero_le _)
  -- Entireness (i) then forces 1 ⊑ R̂R̂° = 𝟘.
  have hEnt := W.entire
  rw [hRh_zero, DistributiveAllegory.zero_comp] at hEnt
  exact le_antisymm hEnt (zero_le _)

/-- **§2.438 corollary.**  Under the §2.438 hypotheses, `A` has just ONE
    morphism: every pair of parallel endomorphisms of `a` is equal.  (This is the
    sense in which "the theory is inconsistent".) -/
theorem godel_all_morphisms_equal {a : 𝒜} (W : HatWitness a) (H : GodelHyp W.T W.R)
    (P Q : a ⟶ a) : P = Q := by
  have h1 : Cat.id a = (𝟘 : a ⟶ a) := godel_collapse W H
  have hz : ∀ X : a ⟶ a, X = (𝟘 : a ⟶ a) := fun X =>
    calc X = Cat.id a ≫ X := by rw [Cat.id_comp]
      _ = (𝟘 : a ⟶ a) ≫ X := by rw [h1]
      _ = (𝟘 : a ⟶ a) := DistributiveAllegory.zero_comp X
  rw [hz P, hz Q]

/-! ## What a FULL §2.438 additionally needs (the deferred PA subproject)

  `godel_collapse` is the complete §2.438 *reduction*: it consumes exactly the
  data Freyd's prose produces (`T`, `R`, `R̂`, the three containments, the single
  divisor instance, and the consistency equation) and returns the collapse.  What
  it does NOT do — and what §2.438 as a self-contained theorem about arithmetic
  would additionally require — is CONSTRUCT a `HatWitness` and a `GodelHyp` from a
  recursive theory of arithmetic.  That construction is a separate subproject with
  no infrastructure yet in this repo (recon: the repo has `encCode`/`acceptN`
  (§2.16 recursion-witness checker) and the §1.97 NNO/Peano-*property* topos
  facts, but NO first-order theory and NO provability predicate).  It needs:

  1. A syntax of first-order arithmetic: terms, formulas, well-formed sentences,
     and their Gödel numbering (a `WffSentence → ℕ` encoding).
  2. A RECURSIVE axiom set for elementary number theory strong enough for Peano,
     and a provability predicate `Prov : ℕ → Prop` that is r.e. (`acceptN`-style),
     with the representability/derivability facts (Σ₁-completeness) needed to make
     "`m R n` iff it is provably not the case that `n T n`" a genuine recipe for
     an r.e. relation (the diagonal lemma / self-reference).
  3. The one-object allegory `A` of r.e. relations quotiented by *provable*
     coextensibility (the §2.437 r.e.-relations allegory + the congruence), and a
     proof that `T`, `R̂` from §2.437 survive the quotient — giving `HatWitness`.
  4. The proof that the simulated-consistency hypothesis (provable-consequences ⊊
     well-formed-sentences) yields `R(1∩T) = 𝟘` in `A` — giving `GodelHyp`.

  Each of (1)–(4) is substantial and independent of the allegory collapse proved
  here; (2)'s diagonal lemma is itself the mathematical core of Gödel's theorem.
  This file isolates the allegory-theoretic half faithfully and completely. -/

end Freyd.Godel
