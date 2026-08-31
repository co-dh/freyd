/-
  Bird & de Moor, *Algebra of Programming* §8.2  Paths in a layered network (book pp. 196-198).

  A least-cost path in a layered network, as a fold over the layers.  The specification is
  `min R·Λ⦇α·F(∈,id)⦈` for the non-empty-cons-list bifunctor `F(A,X) = A + A×X`, its initial
  algebra `α = [wrap,cons]`, and `R = cost°·cost`, `cost = outr·⦇[wrapz,consw]⦈`.  Thinning by
  `Q = R ∩ (head·head°)` — a cheaper path may still lose if it starts at a dearer vertex, so
  the head has to be recorded — turns it into the fold
  `⦇[P wrap, cpl·P step]⦈` with `step = min R·P cons·cpr`.

  WHAT IS PROVED HERE.  The derivation on p.198 is two moves:

  1. Corollary 8.1 (`AOP.A8_1`'s `thinning_est`) puts `thin Q` inside the fold, at
     `F(∈,Q)·α ⊑ Q·α·F(∈,id)` — the note's `path-mono`, mirrored `MonotonicAlg Sspec Q`.
  2. The rest of the page rewrites the ALGEBRA and never mentions the bifunctor again once
     its source is split: `thin Q·Λ(S·V) ⊒ P(min R·ΛS)·ΛV`.  That is `thinAlg_elim`, proved
     from the power transpose of a composition, (8.4) (`powerRel_thinRel_comp_bigUnion_le`),
     thin-elimination (8.3) (`Λ_comp_est_comp_singletonMap_le_thinRel`) and `P τ·union = id`.
     `thinning_paths` composes the two.

  WHAT IS LEFT DEFINITIONAL.  Two bookkeeping identities of the bifunctor `F(−,−)` and of the
  coproduct, which the book also states rather than proves, are hypotheses/notation here:
  - `F(id,∈)·α·F(∈,id) = F(∈,id)·(α·F(id,∈))` — bifunctoriality, the hypothesis `hbif`
    (`V = F(∈,id)`, `S = α·F(id,∈)`, so `V·S` mirrors `F(∈,∈)·α`);
  - `ΛF(∈,id) = id + cpl` and `min R·Λ(α·F(id,∈)) = [wrap,step]`, which turn
    `ΛV·P(ΛS·min R)` into the printed `⦇[P wrap, cpl·P step]⦈` — the note's `path-defn`.
  Both need an abstract bifunctor and coproducts, which this layer does not carry; nothing
  below assumes them, so the theorems hold for ANY split `V·S` of the algebra's source.

  MIRRORING: diagram order, B&dM `X·Y` = Freyd `Y ≫ X`; `min R°` is `est R`, `thin Q` is
  `thinRel Q`, `P` is `powerRel`, `union` is `bigUnion` and `τ` is `singletonMap`.
-/
module

public import AOP.A8_1
public import AOP.A5_6

universe u

namespace Freyd.Alg

/-- The setting for §8.2-§8.3: `AOP.A5_6`'s tabular/unitary + unguarded-power merge (which
    gives `RelProd`, `cup` and `cpMap` alongside `Λ`) TOGETHER with local completeness (which
    gives `relCata`, `thinRel` and `est`).  Both parents already share `Allegory`, so this is
    the same diamond-safe structure merge as `AOP.A6_2`'s `UnguardedPowerLCDA`.  §8.2 needs
    the tabular half only for `AOP.A5_4`'s `powerRel_comp` (`P` functorial on ALL relations,
    not just maps), which is proved there under `TabularUnitaryUnguardedPowerAllegory`. -/
public class TabularUnitaryUnguardedPowerLCDA (𝒜 : Type u) extends
    TabularUnitaryUnguardedDivisionPowerAllegory 𝒜, LocallyCompleteDistributiveAllegory 𝒜

/-- The power/local-completeness side of the merge, so `AOP.A8_1`'s thinning calculus fires
    here unchanged. -/
@[expose] public instance (priority := 100) TabularUnitaryUnguardedPowerLCDA.toUnguardedPowerLCDA
    {𝒜 : Type u} [inst : TabularUnitaryUnguardedPowerLCDA 𝒜] : UnguardedPowerLCDA 𝒜 :=
  { inst with }

/-- `AOP.A5_4`'s hard half of `P`-functoriality is stated over `Freyd.S2_41b`'s tabular merge,
    which the division merge above implies (`DivisionAllegory` brings `DistributiveAllegory`);
    the two are not related by inheritance, so the bridge is given here. -/
@[expose] public instance (priority := 100)
    TabularUnitaryUnguardedPowerLCDA.toTabularUnitaryUnguardedPowerAllegory
    {𝒜 : Type u} [inst : TabularUnitaryUnguardedPowerLCDA 𝒜] :
    TabularUnitaryUnguardedPowerAllegory 𝒜 :=
  { inst with }

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {a c w : 𝒜}

/-- **§8.2's algebra elimination** (book p.198, the calculation "in which the term `thin Q` is
    eliminated"): split the thinning algebra's source as `V ≫ S`, and the `thin Q` at its end
    collapses to a `min R` under the power functor —
    `thin Q·Λ(S·V) ⊒ P(min R·ΛS)·ΛV`, mirrored
    `Λ V ≫ P (Λ S ≫ est R) ⊑ Λ (V ≫ S) ≫ thin Q`.
    The steps are the book's: the power transpose of a composition splits `Λ (V ≫ S)` into
    `Λ V ≫ P(Λ S) ≫ union`; (8.4) moves `thin Q` under `P`; thin-elimination (8.3) replaces it
    by `min R` followed by the singleton, at `R ∩ (S°S) ⊑ Q`; and `P τ ≫ union = id` absorbs
    the singleton and the union together. -/
public theorem thinAlg_elim (V : c ⟶ w) (S : w ⟶ a) {Q R : a ⟶ a}
    (hQ : R ∩ (S° ≫ S) ⊑ Q) :
    Λ V ≫ powerRel (Λ S ≫ est R) ⊑ Λ (V ≫ S) ≫ thinRel Q := by
  -- the power transpose of a composition (book p.198)
  have hsplit : Λ (V ≫ S) = Λ V ≫ powerRel (Λ S) ≫ bigUnion := by
    rw [← Λ_absorption V S, existsImage_eq_Λ_bigUnion S, powerRel_map (Λ_is_map' S)]
  have hmapτ : Map (singletonMap : a ⟶ PowerAllegory.powerObj a) := Λ_is_map' (𝟙 a)
  -- `P τ ≫ union = id` (`union·Pτ = id`, the monad law)
  have hτ : powerRel (singletonMap : a ⟶ PowerAllegory.powerObj a) ≫ bigUnion
      = 𝟙 (PowerAllegory.powerObj a) := by
    rw [powerRel_map hmapτ, bigUnion_existsImage_singleton]
  -- thin-elimination (8.3)
  have h83 : (Λ S ≫ est R) ≫ singletonMap ⊑ Λ S ≫ thinRel Q := by
    rw [Cat.assoc]
    exact Λ_comp_est_comp_singletonMap_le_thinRel hQ
  have hstep : powerRel (Λ S ≫ est R) ⊑ powerRel (Λ S ≫ thinRel Q) ≫ bigUnion := by
    have e1 : powerRel ((Λ S ≫ est R) ≫ singletonMap) ≫ bigUnion
        = powerRel (Λ S ≫ est R) := by
      rw [powerRel_comp, Cat.assoc, hτ, Cat.comp_id]
    rw [← e1]
    exact comp_mono_right (powerRel_mono h83) bigUnion
  rw [hsplit, Cat.assoc, Cat.assoc]
  refine comp_mono_left (Λ V) (le_trans hstep ?_)
  rw [powerRel_comp, Cat.assoc]
  exact comp_mono_left _ (powerRel_thinRel_comp_bigUnion_le Q)

variable {F : Relator 𝒜 𝒜}

/-- **The §8.2 headline** (book p.198): a least-cost path in a layered network, as a fold over
    the layers —
    `min R·Λ⦇Sspec⦈ ⊒ min R·Λ⦇ΛV·P(ΛS·min R)⦈`, mirrored
    `relCata (Λ V ≫ P (Λ S ≫ est R)) ≫ est R ⊑ Λ (relCata Sspec) ≫ est R`,
    for any split `F(∈)·Sspec = V·S` of the algebra's source (`hbif`) with
    `R ∩ (S°S) ⊑ Q`.  At `Sspec = α·F(∈,id)`, `V = F(∈,id)` and `S = α·F(id,∈)` the algebra
    `ΛV·P(ΛS·min R)` is the book's `[P wrap, cpl·P step]`.  Corollary 8.1 (`thinning_est`)
    supplies the fold, `thinAlg_elim` the algebra. -/
public theorem thinning_paths (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {Sspec : F.obj a ⟶ a} {V : F.obj (PowerAllegory.powerObj a) ⟶ w} {S : w ⟶ a} {Q R : a ⟶ a}
    (hbif : F.map (∋ a) ≫ Sspec = V ≫ S)
    (hQR : Q ⊑ R) (hreflQ : 𝟙 a ⊑ Q) (htransQ : Q ≫ Q ⊑ Q) (htransR : R° ≫ R° ⊑ R°)
    (hmono : MonotonicAlg Sspec Q) (hQ : R ∩ (S° ≫ S) ⊑ Q) :
    relCata (Λ V ≫ powerRel (Λ S ≫ est R)) ≫ est R ⊑ Λ (relCata Sspec) ≫ est R := by
  have halg : Λ V ≫ powerRel (Λ S ≫ est R) ⊑ Λ (F.map (∋ a) ≫ Sspec) ≫ thinRel Q := by
    rw [hbif]
    exact thinAlg_elim V S hQ
  exact le_trans (comp_mono_right (relCata_le_relCata I (comp_mono_left _ halg)) (est R))
    (thinning_est hFr I hQR hreflQ htransQ htransR hmono)

end Freyd.Alg
