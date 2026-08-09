module

public import Freyd.S1_572b_NotEffective
public import Freyd.S2_111_RelCat
public import Freyd.S2_16c

/-!
# §2.16(13) for the recursive category R: its effective reflection is NOT AC

The book's §2.16(13): if a regular category `C` is not effective, then its
effective reflection `Ĉ = Spl(Eq Rel(C))` is not an allegory of choice (AC) — covers
do not split there.

`Freyd/S1_572b_NotEffective.lean` (§1.572) exhibits the recursive category R
(objects `ExtNat`, morphisms recursive functions) as NON-effective: `ERel`, the r.e.
halting equivalence relation gluing `2e ~ 2e+1` exactly when `e` halts on itself, is
an equivalence relation of R (`ERel_equivalence`) but the level of no cover
(`ERel_not_effective`, ultimately `K_not_recursive`).

This file transports that fact through the Chapter-2 `Rel`/`Map` bridge
(`Freyd/S2_111_RelCat.lean`) and applies the general reflection theorem
`Freyd.Alg.not_coversSplit_of_not_effective` (`Freyd/S2_16c.lean`) to conclude:

  **`Freyd.RecEff.reflection_not_ac`** — `¬ CoversSplit (Spl(Eq (Rel ExtNat)))`.

The bridge is purely a change of encoding:

* `ERel` becomes the allegory endo-relation `eE := [ERel] : ⟨ω⟩ ⟶ ⟨ω⟩` of `Rel(R)`.
  Reflexive/symmetric/idempotent (`hrefl`/`hsym`/`hidem`) come from `ERel_equivalence`
  through `quotLe_iff_algLe`, `qRecip_mk`, `qComp_mk`.
* A hypothetical map-splitting `f` of `eE` in `Rel(R)` is, by fullness of the graph
  embedding (`embedRel_full`, §2.148), the graph of a recursive map `g`; then
  `f ≫ f° = eE` says `g ⊚ g° ≈ ERel` and `f° ≫ f = 1` says `g` is a cover
  (`cover_iff_one_le_reciprocal_comp_self`, §1.569) — i.e. exactly `IsEffective ERel`,
  contradicting `ERel_not_effective`.  Hence no such splitting exists (`no_splitsAsMap`),
  and the general theorem yields non-AC-ness of the reflection.

Mathlib-free; diagram-order composition `R ≫ S`; relation composition `⊚`.
-/

open Freyd.Rcat

namespace Freyd.RecEff

/-- `E` transported into the relation allegory `Rel(R)`: the class of `ERel`, read as an
    endomorphism `⟨ω⟩ ⟶ ⟨ω⟩` of `Rel(ExtNat)`. -/
noncomputable def eE : (⟨omega⟩ : RelObj ExtNat) ⟶ ⟨omega⟩ := relClass ERel

/-- Reflexivity of `E` as a `BinRel` containment `graph(1_ω) ⊂ ERel` (the first
    component of `ERel_equivalence`, retyped). -/
theorem ERel_refl_le : RelLe (graph (Cat.id omega)) ERel := ⟨ERel_equivalence.1⟩

/-- `eE` is reflexive in `Rel(R)`: `1_{⟨ω⟩} ⊑ eE`.  `Cat.id ⟨ω⟩ = [graph 1_ω]` and
    `quotLe_iff_algLe` turns the containment `graph 1_ω ⊂ ERel` into the allegory order. -/
theorem eE_refl : Cat.id (⟨omega⟩ : RelObj ExtNat) ⊑ eE :=
  (quotLe_iff_algLe (relClass (graph (Cat.id omega))) (relClass ERel)).mp
    (relClass_mono ERel_refl_le)

/-- `eE` is symmetric in `Rel(R)`: `eE° = eE`.  From `E ⊂ E°` (symmetry) and its
    reciprocal `E° ⊂ E`, the classes of `E°` and `E` coincide. -/
theorem eE_sym : Freyd.Alg.Allegory.recip eE = eE := by
  have h2 : RelLe ERel (reciprocal ERel) := ERel_equivalence.2.1
  have h1 : RelLe (reciprocal ERel) ERel := by
    have := reciprocal_mono h2
    rwa [reciprocal_invol] at this
  change relClass (reciprocal ERel) = relClass ERel
  exact Quotient.sound ⟨h1, h2⟩

/-- `eE` is idempotent in `Rel(R)`: `eE ≫ eE = eE`.  Forward is transitivity
    `E⊚E ⊂ E`; backward is `E ⊂ 1⊚E ⊂ E⊚E` using reflexivity. -/
theorem eE_idem : eE ≫ eE = eE := by
  have htr : RelLe (ERel ⊚ ERel) ERel := ERel_equivalence.2.2
  have hexp : RelLe ERel (ERel ⊚ ERel) :=
    rel_le_trans (comp_graph_id_left ERel) (compose_le ERel_refl_le (rel_le_refl ERel))
  change relClass (ERel ⊚ ERel) = relClass ERel
  exact Quotient.sound ⟨htr, hexp⟩

/-- **No map-splitting of `eE` exists in `Rel(R)`.**  A splitting `f : ⟨ω⟩ ⟶ d` is,
    by fullness of the graph embedding (`embedRel_full`, §2.148), the class of a graph
    `[graph g]`; then `f ≫ f° = eE` says `g ⊚ g° ≈ ERel` and `f° ≫ f = 1_d` says `g`
    is a cover (§1.569).  That is exactly `IsEffective ERel`, which `ERel_not_effective`
    forbids.  (This is the transported form of §1.572's non-effectiveness.) -/
theorem no_splitsAsMap (d : RelObj ExtNat) (f : (⟨omega⟩ : RelObj ExtNat) ⟶ d) :
    ¬ Freyd.Alg.SplitsAsMap f eE := by
  refine Quotient.inductionOn f (fun R => ?_)
  show ¬ Freyd.Alg.SplitsAsMap (relClass R) eE
  rintro ⟨hmap, hff, hf'f⟩
  -- fullness: `[R]` is a graph `[graph g]`
  obtain ⟨g, hg⟩ := embedRel_full R hmap
  rw [hg] at hff hf'f
  -- decode the two allegory equations into `BinRel` containments
  have hff2 : relClass (graph g ⊚ (graph g)°) = relClass ERel := by
    rw [← qComp_mk, ← qRecip_mk]; exact hff
  have hf'f2 : relClass ((graph g)° ⊚ graph g) = relClass (graph (Cat.id d.carrier)) := by
    rw [← qComp_mk, ← qRecip_mk]; exact hf'f
  obtain ⟨hgg_le, hle_gg⟩ := Quotient.exact hff2
  obtain ⟨_, hone_le⟩ := Quotient.exact hf'f2
  -- `g` is a cover (§1.569), so `E` is the level of a cover — i.e. effective.
  have hcover : Cover g := (cover_iff_one_le_reciprocal_comp_self g).mpr hone_le
  exact ERel_not_effective ⟨ERel_equivalence, d.carrier, g, hcover, hle_gg, hgg_le⟩

/-- **§2.16(13) for R.**  The effective reflection `Spl(Eq (Rel R))` of the recursive
    category R is NOT an allegory of choice: covers do not all split there.  This is the
    Chapter-2 transport of §1.572's `ERel_not_effective`. -/
theorem reflection_not_ac :
    ¬ Freyd.Alg.CoversSplit (Freyd.Alg.SplEqObj (RelObj ExtNat)) :=
  Freyd.Alg.not_coversSplit_of_not_effective (a := ⟨omega⟩) eE eE_refl eE_sym eE_idem
    no_splitsAsMap

end Freyd.RecEff
