/-
  Freyd & Scedrov, *Categories, Allegories* §2.153 — the CONCRETE non-effectiveness
  headline over the RECURSIVE modulus system `Krec`.

  `Freyd/S2_153_NonEffective.lean` proves the REDUCTION
  `asmReflection_not_ac_of_nonsplitting`: a non-splitting equivalence relation `I`
  (in the allegory `Rel(Assembly K)`) on some assembly `A` over `K` gives
  `¬ CoversSplit (AsmEffReflection K)`.  `Freyd/S2_153b_RecursiveModulus.lean`
  supplies the concrete recursive modulus system `Krec` (`mem := PartRec`).

  This file supplies the missing bridge and the concrete witness.

  ## The bridge (this section, hole-free)

  `asm_not_effective_of_binRel`: the assembly mirror of the recursive
  category's `Freyd.RecEff.no_splitsAsMap` (`Freyd/S2_16_Recursive.lean`), lifted to a
  reusable reduction, generic in the modulus system `K`.  For ANY assembly `A` over `K` and
  ANY category-level (§1.56) BinRel-equivalence-relation `E : BinRel (Assembly K) A A` that
  is NOT EFFECTIVE (`¬ IsEffective E`, §1.568 — not the level of any cover),
  `Rel(Assembly K)` is not effective; via `asmReflection_not_ac_of_notEffective` the
  effective reflection `E = Spl(Eq (Rel(Assembly K)))` (§2.16(14)) then fails AC.

  The proof is the exact transport of `Freyd.RecEff.no_splitsAsMap` through the graph
  embedding `Assembly Krec ↪ Map(Rel(Assembly Krec))` (all lemmas generic over a regular
  category, `Assembly Krec` regular by §2.153 `asmRegular`):
  * `I := relClass E` is an equivalence relation of `Rel(Assembly Krec)` — reflexive,
    symmetric, transitive — because `E` is one at the BinRel level (`quotLe_iff_algLe`,
    `qComp_mk`, `qRecip_mk`, mirroring `eE_refl`/`eE_sym`/`eE_idem`).
  * A hypothetical map-splitting `f` of `I` is, by fullness of the graph embedding
    (`embedRel_full`, §2.148 dual), the class `[graph g]` of an assembly morphism `g`;
    then `f ≫ f° = I` says `graph g ⊚ (graph g)° ≈ E` and `f° ≫ f = 1` says `g` is a
    COVER (`cover_iff_one_le_reciprocal_comp_self`, §1.569) — i.e. exactly `IsEffective E`,
    which `hne` forbids.  So no splitting exists, and `asmReflection_not_ac_of_nonsplitting`
    fires on the result.

  ## The concrete witness (Layers 3–4) — CLOSED in `S2_153f` (see the corrected note below)

  With the bridge above, the literal §2.153 headline `¬ CoversSplit (AsmEffReflection Krec)`
  reduces to exhibiting ONE concrete instance

      ∃ (A : Assembly Krec) (E : BinRel (Assembly Krec) A A),
        EquivalenceRelation E ∧ ¬ IsEffective E

  and then applying `asm_not_effective_of_binRel`.  This is the genuine
  hard core of §2.153; it is NOT a transport of §1.572b's `ERel` (see below).

  ### Why `¬ IsEffective E` is the hard part — the structural obstruction

  In `Assembly Krec`, the level (kernel pair) `graph x ⊚ (graph x)°` of ANY cover
  `x : A → Q` has, as a BinRel on `A`, a caucus structure INDEPENDENT of `Q`: the
  composite tabulation is built from the pullback of `graph x` against itself, whose
  legs are `1_A` (a `graph`'s `colA`), so a pullback point over `(a,a')` with `x a = x a'`
  is realized purely by an `A×A`-realizer `code (r_a) (r_a')` (`r_a` a caucus index of `a`
  in `A`), never by a `Q`-realizer.  Hence for every cover `x` realizing a given set-kernel,

      graph x ⊚ (graph x)°  ≅  Ā_E   (the FULL A×A-induced realizability on E's set),

  where `Ā_E|ₘ = {(a,a') ∈ E-set : a ∈ A|_{ℓm}, a' ∈ A|_{ϰm}}`.  Therefore, for an
  equivalence relation `E`,

      IsEffective E  ⟺  relClass E = relClass Ā_E  ⟺  the "fill" map Ā_E → E is Krec-tracked.

  Non-effectiveness is thus: the fill — recovering an `E`-realizer of `(a,a')` from the
  CHEAP point-realizers `code (r_a) (r_a')` — is NOT `Krec`-partial-recursive.  The §2.153
  witness makes that fill DECIDE `Kc`: build `A` with non-singleton, `Kc`-driven caucuses so
  that `E` glues `2e ~ 2e+1` realized only by a halting witness for `e`, while `A`'s point
  realizers are cheap; a fill modulus, being TOTAL on the inhabited caucus index of every
  glued pair, would give a total `Krec`-decider of `Kc`, contradicting
  `Freyd.Rcat.K_not_recursive`.

  ### Why the naive singleton route FAILS (do not use it)

  On the singleton-caucus assembly (`A|ₙ = {n}`) EVERY equivalence relation is effective:
  the canonical quotient `Q|ₙ := {[a] : a ∈ A|ₙ}`, `x a := [a]`, is a `Krec`-cover tracked
  by the identity modulus with kernel exactly `E`.  So `¬ IsEffective E` is FALSE there and
  the halting relation does not qualify — the caucuses must be `Kc`-driven and non-singleton.

  ### Remaining Lean work — CLOSED in `S2_153f` (and the prediction above corrected)

  The concrete `A`/`E` is supplied by `Freyd/S2_153f_ParityWitness.lean`: `A = ∇ℕ`, `E` the
  parity relation (classes `2k ~ 2k+1`, caucus at `m` = diagonal ∪ classes ≤ m).  The
  structural obstruction described above is right that the level's caucuses are `Q`-independent
  (`level_caucus_iff`, `S2_153e`), but the prediction that the fill must "DECIDE `Kc`" was
  wrong: over `∇ℕ` the cheap index carries NO information about the pair, so a single tracked
  index already contradicts the class-bounded caucuses — UNIFORMITY OF NAMING, no recursion
  theory, valid over `Krec` and over `allPartial` alike.

  MATHLIB-FREE.  Composition in DIAGRAM ORDER.
-/
module

public import Freyd.S2_153b_RecursiveModulus

open Freyd Freyd.Alg

namespace Freyd.Alg

/-! ## The bridge: BinRel non-effectiveness ⟹ the reflection fails AC

  This is the assembly analogue of `Freyd.RecEff.no_splitsAsMap` +
  `Freyd.RecEff.reflection_not_ac`, packaged to accept the category-level (§1.56)
  witness `¬ IsEffective E` directly. -/

/-- **§2.153 / §2.16(13) — the BinRel reduction.**  For an assembly `A` over any modulus
    system `K` and a §1.56 BinRel-equivalence-relation `E : A → A` that is NOT the level of
    any cover (`¬ IsEffective E`), `Rel(Assembly K)` is not effective: `[E]` is a §2.12
    equivalence relation of the allegory that no map splits.  Composing with
    `asmReflection_not_ac_of_notEffective` gives the §2.16(13) headline — the effective
    reflection of `Rel(Assembly K)` is then not an allegory of choice.

    This reduces the concrete §2.153 non-effectiveness to a single category-theoretic
    obligation about assemblies, in exactly the shape of the recursive category's
    `Freyd.RecEff.reflection_not_ac` (whose witness is `ERel_not_effective`).  The parity
    witness of `S2_153f` (`asm_not_effective_of_projBounded`) is this lemma applied to
    `parityRel`. -/
public theorem asm_not_effective_of_binRel {K : ModulusSystem} {A : Assembly.{u} K}
    (E : BinRel (Assembly.{u} K) A A)
    (hequiv : EquivalenceRelation E) (hne : ¬ IsEffective E) :
    ∃ (A : Assembly.{u} K) (I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩),
      Reflexive I ∧ Symmetric I ∧ Transitive I ∧
      ∀ (d : AsmRel K) (f : (⟨A⟩ : AsmRel K) ⟶ d), ¬ SplitsAsMap f I := by
  -- `I := relClass E`, read as an endomorphism `⟨A⟩ ⟶ ⟨A⟩` of `Rel(Assembly K)`.
  let I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩ := relClass E
  -- Reflexive: the diagonal witness of `hequiv` is a `RelHom (graph 1_A) E`.
  have hrefl : Reflexive I :=
    (quotLe_iff_algLe (relClass (graph (Cat.id A))) (relClass E)).mp
      (relClass_mono (⟨hequiv.1⟩ : RelLe (graph (Cat.id A)) E))
  -- Symmetric: `E ⊂ E°` and its reciprocal give `[E°] = [E]`.
  have hsym_eq : I° = I := by
    have h2 : RelLe E (reciprocal E) := hequiv.2.1
    have h1 : RelLe (reciprocal E) E := by
      have := reciprocal_mono h2; rwa [reciprocal_invol] at this
    show relClass (reciprocal E) = relClass E
    exact Quotient.sound ⟨h1, h2⟩
  have hsym : Symmetric I := (symmetric_iff _).mpr hsym_eq
  -- Transitive: `E ⊚ E ⊂ E` at the BinRel level.
  have htrans : Transitive I :=
    (quotLe_iff_algLe (relClass (E ⊚ E)) (relClass E)).mp
      (relClass_mono (hequiv.2.2 : RelLe (E ⊚ E) E))
  -- No map-splitting exists: it would exhibit `E` as the level of a cover.
  have hno : ∀ (d : AsmRel.{u} K) (f : (⟨A⟩ : AsmRel K) ⟶ d),
      ¬ SplitsAsMap f I := by
    intro d f
    refine Quotient.inductionOn f (fun R => ?_)
    show ¬ SplitsAsMap (relClass R) I
    rintro ⟨hmap, hff, hf'f⟩
    -- fullness: `[R]` is the graph of an assembly morphism `g : A → d.carrier`.
    obtain ⟨g, hg⟩ := embedRel_full R hmap
    rw [hg] at hff hf'f
    have hff2 : relClass (graph g ⊚ (graph g)°) = relClass E := by
      rw [← qComp_mk, ← qRecip_mk]; exact hff
    have hf'f2 : relClass ((graph g)° ⊚ graph g)
        = relClass (graph (Cat.id d.carrier)) := by
      rw [← qComp_mk, ← qRecip_mk]; exact hf'f
    obtain ⟨hgg_le, hle_gg⟩ := Quotient.exact hff2
    obtain ⟨_, hone_le⟩ := Quotient.exact hf'f2
    have hcover : Cover g := (cover_iff_one_le_reciprocal_comp_self g).mpr hone_le
    exact hne ⟨hequiv, d.carrier, g, hcover, hle_gg, hgg_le⟩
  exact ⟨A, I, hrefl, hsym, htrans, hno⟩

end Freyd.Alg
