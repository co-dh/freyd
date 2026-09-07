/-
  Freyd & Scedrov, *Categories and Allegories* — §2.153 / §2.16(13): the category of
  ASSEMBLIES over a RECURSIVE modulus system is NOT effective, hence its effective
  reflection (§2.16(14)) is NOT an allegory of choice (AC).

  Book §2.153: "The category of assemblies is not effective."  "Rel(A) is a unitary
  tabular allegory, but not all equivalence relations split (as idempotents)."  Book
  §2.16(13): "if C is not effective then Ĉ is not AC."

  This is EXACTLY the assembly analogue of the recursive category R:
  `Freyd/S2_16_Recursive.lean` proves `Freyd.RecEff.reflection_not_ac`
  (`¬ CoversSplit (Spl(Eq (Rel ExtNat)))`) by feeding §1.572b's halting equivalence
  relation `ERel` (`ERel_not_effective`, ultimately `K_not_recursive`) into the general
  reflection theorem `not_coversSplit_of_not_effective` (§2.16c).

  ## What this file proves (Sorry-free)

  The REDUCTION `asmReflection_not_ac_of_nonsplitting`: the §2.16(13) machinery of
  `Freyd/S2_16c.lean` (`not_coversSplit_of_not_effective`), specialised to the tabular
  allegory `AsmRel K = Rel(Assembly K)` (tabular by §2.111 `relTabularAllegory`, since
  `Assembly K` is regular, §2.153 `asmRegular`).  It says: as soon as SOME assembly `A`
  over `K` carries an equivalence relation `I : A → A` in `Rel(A)` that does not split
  as a map, the effective reflection `E = Spl(Eq (Rel A))` of §2.16(14)
  (`AsmEffReflection K`, S2_16d) fails AC — covers do not all split there.

  This is the book's §2.153 non-effectiveness reduced to its combinatorial core: the
  single non-splitting equivalence relation.  It is the direct assembly mirror of
  `Freyd.RecEff.reflection_not_ac`, parameterised over the witness — supplied by the
  parity relation of `S2_153f`.

  ## The witness — DISCHARGED in `Freyd/S2_153f_ParityWitness.lean` (corrected analysis)

  The hypothesis of the reduction is discharged by the PARITY WITNESS of `S2_153f`: on
  `A = ∇ℕ` the equivalence relation `E` gluing `2k ~ 2k+1`, with caucus at `m` = the
  diagonal together with the pairs of class `≤ m`, has NO map-splitting; hence
  `asmReflection_not_ac : ¬ CoversSplit (AsmEffReflection Krec)` (the partial-recursive
  modulus system built in `S2_153b`) and likewise `asmReflection_not_ac_allPartial`.

  An earlier version of this paragraph predicted the opposite — that the obstruction is
  the halting problem, fires only for a RECURSIVE modulus system, and that over
  `ModulusSystem.allPartial` it "VANISHES", making the `allPartial` target "EXPECTED
  FALSE".  That analysis was WRONG.  Freyd's §2.153 claim carries no recursiveness side
  condition (it is stated for every K with identity, composition and pairing), and the
  real obstruction is UNIFORMITY OF NAMING, not representative choice: over `∇ℕ` every
  index names every point, so the level `q ⊚ q°` of ANY morphism — in particular of any
  would-be splitting map, extracted via §2.148-dual fullness — has FULL caucuses
  (`level_caucus_iff`, `S2_153e`), and a tracked containment `level ⊑ E` must send the
  single index `0` to a single caucus index of `E` containing the ENTIRE kernel.  That
  is impossible when `E`'s caucuses exhaust the kernel only in the limit (class `≤ m` at
  index `m`).  This argument is uniform in K — no halting set, valid even for
  `mem = True`.  What IS true about representative choice: transporting §1.572b's `ERel`
  on a singleton-caucus assembly yields an EFFECTIVE relation (`S2_153b` tail note), so
  a witness must place the uniformity burden on the caucuses, as the parity witness
  does.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, order `R ⊑ S`.
  Mathlib-free.
-/
module

public import Freyd.S2_16d

universe u

namespace Freyd.Alg

open Cat

section AsmNonEffective

variable {K : ModulusSystem}

/-- **§2.153 / §2.16(13) for assemblies — the reduction.**
    If some assembly `A` over `K` carries an equivalence relation `I : A → A` in
    `Rel(A)` (reflexive, symmetric, transitive, in the book's §2.12 relational sense)
    that does NOT split as a map, then the effective reflection `E = Spl(Eq (Rel A))`
    of §2.16(14) is NOT an allegory of choice: covers do not all split in `E`.

    This is `not_coversSplit_of_not_effective` (§2.16c, the book's "hence if C is not
    effective then Ĉ is not AC") instantiated at the tabular allegory
    `AsmRel K = Rel(Assembly K)`.  It is the direct assembly analogue of
    `Freyd.RecEff.reflection_not_ac`, awaiting the halting-relation witness `I`
    (see the module docstring for why that witness needs the recursive modulus system). -/
public theorem asmReflection_not_ac_of_nonsplitting {A : Assembly.{u} K}
    (I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩)
    (hrefl : Reflexive I) (hsym : Symmetric I) (htrans : Transitive I)
    (hno : ∀ (d : AsmRel K) (f : (⟨A⟩ : AsmRel K) ⟶ d), ¬ SplitsAsMap f I) :
    ¬ CoversSplit (AsmEffReflection.{u} K) := by
  -- Pre-compute each hypothesis so its universes pin to `I` (letting `𝒜 = AsmRel K`
  -- be inferred, not annotated).  `Reflexive I` is defeq `Cat.id ⟨A⟩ ⊑ I`.
  have hr : Cat.id (⟨A⟩ : AsmRel K) ⊑ I := hrefl
  have hs : I° = I := symmetric_eq hsym
  have hidem : I ≫ I = I := reflexive_transitive_idempotent hrefl htrans
  exact not_coversSplit_of_not_effective (𝒜 := AsmRel.{u} K) I hr hs hidem hno

/-- **§2.153 non-effectiveness (packaged existential).**  The reflection `E` of
    `Rel(Assembly K)` fails AC as soon as `Rel(Assembly K)` is not effective, witnessed
    by ANY non-splitting equivalence relation on some assembly over `K`.  The hypothesis
    is exactly "`Rel(A)` has an equivalence relation that is not the level of a cover"
    (§2.153: "not all equivalence relations split as idempotents"). -/
public theorem asmReflection_not_ac_of_notEffective
    (hne : ∃ (A : Assembly.{u} K) (I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩),
      Reflexive I ∧ Symmetric I ∧ Transitive I ∧
      ∀ (d : AsmRel K) (f : (⟨A⟩ : AsmRel K) ⟶ d), ¬ SplitsAsMap f I) :
    ¬ CoversSplit (AsmEffReflection.{u} K) := by
  obtain ⟨A, I, hrefl, hsym, htrans, hno⟩ := hne
  exact asmReflection_not_ac_of_nonsplitting I hrefl hsym htrans hno

end AsmNonEffective

end Freyd.Alg
