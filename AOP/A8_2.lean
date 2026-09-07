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
public import AOP.A6_1_RelSet
-- the layered network's paths are `ConsList V V`, whose base relator `X ↦ (V→Prop)+(V→Prop)×X`
-- is what `thinning_paths`'s `F` is instantiated to below.
public import AOP.A6_ConsList

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

/-- `Rel(Set)` is the setting: both halves of the merge are already instances (`AOP.A6_1_RelSet`),
    so §8.2's and §8.3's theorems apply to the concrete case studies of §8.4-§8.6. -/
@[expose] public instance : TabularUnitaryUnguardedPowerLCDA RelSet.{u} :=
  { (inferInstance : Freyd.Alg.TabularUnitaryUnguardedDivisionPowerAllegory RelSet),
    (inferInstance : LocallyCompleteDistributiveAllegory RelSet) with }

/-- A MAP is monotonic on `⊤`, so §8.5's and §8.6's `P ≜ ⊤` costs their derivations nothing:
    every candidate list counts as sorted. -/
public theorem graph_monotonicAlg_topMor {F : Relator RelSet.{0} RelSet.{0}} {A : RelSet.{0}}
    (f : (F.obj A).carrier → A.carrier) :
    MonotonicAlg (F := F) (RelSet.graph f) (topMor A A) :=
  RelSet.le_iff.mpr fun u r _ => ⟨f u, rfl, RelSet.topMor_apply _ r⟩

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {A C w : 𝒜}

/-- **§8.2's algebra elimination** (book p.198, the calculation "in which the term `thin Q` is
    eliminated"): split the thinning algebra's source as `V ≫ S`, and the `thin Q` at its end
    collapses to a `min R` under the power functor —
    `thin Q·Λ(S·V) ⊒ P(min R·ΛS)·ΛV`, mirrored
    `Λ V ≫ P (Λ S ≫ est R) ⊑ Λ (V ≫ S) ≫ thin Q`.
    The steps are the book's: the power transpose of a composition splits `Λ (V ≫ S)` into
    `Λ V ≫ P(Λ S) ≫ union`; (8.4) moves `thin Q` under `P`; thin-elimination (8.3) replaces it
    by `min R` followed by the singleton, at `R ∩ (S°S) ⊑ Q`; and `P τ ≫ union = id` absorbs
    the singleton and the union together. -/
public theorem thinAlg_elim (V : C ⟶ w) (S : w ⟶ A) {Q R : A ⟶ A}
    (hQ : R ∩ (S° ≫ S) ⊑ Q) :
    Λ V ≫ powerRel (Λ S ≫ est R) ⊑ Λ (V ≫ S) ≫ thinRel Q := by
  -- the power transpose of a composition (book p.198)
  have hsplit : Λ (V ≫ S) = Λ V ≫ powerRel (Λ S) ≫ bigUnion := by
    rw [← Λ_absorption V S, existsImage_eq_Λ_bigUnion S, powerRel_map (Λ_is_map' S)]
  have hmapτ : Map (singletonMap : A ⟶ PowerAllegory.powerObj A) := Λ_is_map' (𝟙 A)
  -- `P τ ≫ union = id` (`union·Pτ = id`, the monad law)
  have hτ : powerRel (singletonMap : A ⟶ PowerAllegory.powerObj A) ≫ bigUnion
      = 𝟙 (PowerAllegory.powerObj A) := by
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
    {Sspec : F.obj A ⟶ A} {V : F.obj (PowerAllegory.powerObj A) ⟶ w} {S : w ⟶ A} {Q R : A ⟶ A}
    (hbif : F.map (∋ A) ≫ Sspec = V ≫ S)
    (hQR : Q ⊑ R) (hreflQ : 𝟙 A ⊑ Q) (htransQ : Q ≫ Q ⊑ Q) (htransR : R° ≫ R° ⊑ R°)
    (hmono : MonotonicAlg Sspec Q) (hQ : R ∩ (S° ≫ S) ⊑ Q) :
    relCata (Λ V ≫ powerRel (Λ S ≫ est R)) ≫ est R ⊑ Λ (relCata Sspec) ≫ est R := by
  have halg : Λ V ≫ powerRel (Λ S ≫ est R) ⊑ Λ (F.map (∋ A) ≫ Sspec) ≫ thinRel Q := by
    rw [hbif]
    exact thinAlg_elim V S hQ
  exact le_trans (comp_mono_right (relCata_le_relCata I (comp_mono_left _ halg)) (est R))
    (thinning_est hFr I hQR hreflQ htransQ htransR hmono)

/-! ## The note's `path-mono`: the two laws `thinning_paths` assumes, discharged

  `thinning_paths` takes `hmono` and `hQ` as hypotheses.  The note's `path-mono` table states
  them as the two laws of the layered-network example, and both are proved below: the second by
  the book's own shunting step (p.198), which uses nothing of the datatype beyond `head` being a
  map and `S·head` being simple; the first for the concrete network, where it is the arithmetic
  of `consw` and nothing else. -/

/-- **The shunting step of book p.198**: `S·S° ⊑ head°·head`, mirrored `S° ≫ S ⊑ head ≫ head°`,
    whenever `head` is a map and `S·head` is simple.  Sandwiching `S° ≫ S` between two copies of
    `𝟙 ⊑ head ≫ head°` regroups it as `head ≫ (S≫head)° ≫ (S≫head) ≫ head°`. -/
public theorem recip_comp_le_of_simple_comp {A B C : 𝒜} {S : C ⟶ A} {hd : A ⟶ B}
    (hhd : Map hd) (hs : Simple (S ≫ hd)) : S° ≫ S ⊑ hd ≫ hd° := by
  have h1 : S ⊑ S ≫ hd ≫ hd° := by
    have := comp_mono_left S (entire_id_le hhd.1)
    rwa [Cat.comp_id] at this
  have h2 : S° ≫ S ⊑ (S ≫ hd ≫ hd°)° ≫ (S ≫ hd ≫ hd°) :=
    le_trans (comp_mono_right (recip_mono h1) S) (comp_mono_left _ h1)
  have e1 : (S ≫ hd ≫ hd°)° ≫ (S ≫ hd ≫ hd°) = hd ≫ hd° ≫ S° ≫ S ≫ hd ≫ hd° := by
    simp only [Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
  have hs' : hd° ≫ S° ≫ S ≫ hd ⊑ 𝟙 B := by
    have h : (S ≫ hd)° ≫ (S ≫ hd) ⊑ 𝟙 B := hs
    simp only [Allegory.recip_comp, Cat.assoc] at h
    exact h
  have h3 : hd ≫ (hd° ≫ S° ≫ S ≫ hd) ≫ hd° ⊑ hd ≫ 𝟙 B ≫ hd° :=
    comp_mono_left hd (comp_mono_right hs' (hd°))
  simp only [Cat.assoc, Cat.id_comp] at h3
  rw [e1] at h2
  exact le_trans h2 h3

/-! ### The layered network itself (book p.196)

  A layered network is a non-empty sequence of sets of vertices; a path through it is a non-empty
  sequence of vertices, one from each layer, and `wt` gives the cost of stepping from one vertex
  to the next.  So the paths are `ConsList V V` (`wrap` a single vertex, `cons` one on the front)
  and the input functor is `X ↦ (V→Prop) + (V→Prop)×X`, i.e. `AOP.A6_ConsList`'s relator at
  leaf and element type `V→Prop` — the layers. -/

section Paths

open RelSet RelSet.CL

variable {V : Type}

/-- The first vertex of a path. -/
@[expose] public def headOf : ConsList V V → V
  | ConsList.wrap v => v
  | ConsList.cons v _ => v

/-- `cost [a₀,…,aₙ] = (+j : 0 ≤ j < n : wt(aⱼ,aⱼ₊₁))` (book p.196), as the `consw` recursion
    `cost(cons(a,x)) = wt(a,head x) + cost x`. -/
@[expose] public def costOf (wt : V → V → Nat) : ConsList V V → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons v q => wt v (headOf q) + costOf wt q

/-- `R ≜ cost≤cost°`: `p R q` iff `p` costs no more than `q`. -/
@[expose] public def pathR (wt : V → V → Nat) : dCL V V ⟶ dCL V V :=
  fun p q => costOf wt p ≤ costOf wt q

/-- `Q ≜ R∩(head head°)` (book p.197): no dearer, and starting at the same vertex. -/
@[expose] public def pathQ (wt : V → V → Nat) : dCL V V ⟶ dCL V V :=
  fun p q => costOf wt p ≤ costOf wt q ∧ headOf p = headOf q

/-- `Sspec ≜ F(∋,𝟙)α`, the specification's algebra: take a vertex out of the layer and `wrap` it,
    or `cons` it onto the partial path already built. -/
@[expose] public def pathAlg : (CL.F (V → Prop) (V → Prop)).obj (dCL V V) ⟶ dCL V V :=
  fun u p => match u with
    | Sum.inl S => ∃ v, S v ∧ p = ConsList.wrap v
    | Sum.inr q => ∃ v, q.1 v ∧ p = ConsList.cons v q.2

/-- `S ≜ F(𝟙,∋)α`, the second factor of book p.198's split of the algebra's source. -/
@[expose] public def pathSplit : Fobj V V (pow (dCL V V)) ⟶ dCL V V :=
  fun u p => match u with
    | Sum.inl v => p = ConsList.wrap v
    | Sum.inr q => ∃ t, q.2 t ∧ p = ConsList.cons q.1 t

/-- `head : LA ⟶ A`. -/
@[expose] public def headRel : dCL V V ⟶ (⟨V⟩ : RelSet.{0}) := RelSet.graph headOf

/-- `[𝟙,π₁] : F(A,E(LA)) ⟶ A`, the first vertex of whatever `S` builds. -/
@[expose] public def headAlg : Fobj V V (pow (dCL V V)) ⟶ (⟨V⟩ : RelSet.{0}) :=
  RelSet.graph fun u => match u with | Sum.inl v => v | Sum.inr q => q.1

public theorem headRel_map : Map (headRel (V := V)) := RelSet.graph_map _

public theorem headAlg_map : Map (headAlg (V := V)) := RelSet.graph_map _

/-- **The first law of the note's `path-mono`** (book p.197): `F(∋,Q)α ⊑ F(∋,𝟙)αQ`, mirrored
    `MonotonicAlg Sspec Q`.  Consing the same vertex onto a `Q`-better path gives a `Q`-better
    path: equal heads make the new edge cost the same, and the rest is the assumption.  On `R`
    alone it fails — `wt(a,head q)` can be arbitrarily large — which is why `Q` records the head. -/
public theorem pathAlg_monotonic (wt : V → V → Nat) :
    MonotonicAlg (F := CL.F (V → Prop) (V → Prop)) (pathAlg (V := V)) (pathQ wt) := by
  refine le_iff.mpr ?_
  rintro u p ⟨u', hu, hp⟩
  cases u with
  | inl S =>
    cases u' with
    | inl S' =>
      have hS : S = S' := hu
      subst hS
      exact ⟨p, hp, Nat.le_refl _, rfl⟩
    | inr q' => exact hu.elim
  | inr q =>
    cases u' with
    | inl S' => exact hu.elim
    | inr q' =>
      obtain ⟨hSS, hq⟩ := hu
      obtain ⟨v, hv, rfl⟩ := hp
      refine ⟨ConsList.cons v q.2, ⟨v, by rw [hSS]; exact hv, rfl⟩, ?_, rfl⟩
      show wt v (headOf q.2) + costOf wt q.2 ≤ wt v (headOf q'.2) + costOf wt q'.2
      rw [hq.2]
      exact Nat.add_le_add_left hq.1 _

/-- **The second law of the note's `path-mono`** (book p.198, left as an exercise there):
    `S head ⊑ [𝟙,π₁]` — whichever path `S` builds, its first vertex is fixed by `S`'s argument
    alone, so `S head` is simple. -/
public theorem pathSplit_comp_headRel_le : pathSplit (V := V) ≫ headRel ⊑ headAlg := by
  refine le_iff.mpr ?_
  rintro u x ⟨p, hp, hx⟩
  cases u with
  | inl v => subst hp; exact hx
  | inr q => obtain ⟨t, _, rfl⟩ := hp; exact hx

/-- `thinning_paths`'s `hQ` for the network (book p.198): `R∩(S°S) ⊑ Q` at `Q ≜ R∩(head head°)`.
    `S head ⊑ [𝟙,π₁]` makes `S head` simple, and the shunting step turns that into
    `S°S ⊑ head head°`. -/
public theorem pathR_inter_recip_le_pathQ (wt : V → V → Nat) :
    pathR wt ∩ ((pathSplit (V := V))° ≫ pathSplit) ⊑ pathQ wt := by
  have hsimple : Simple (pathSplit (V := V) ≫ headRel) :=
    le_trans (le_trans (comp_mono_right (recip_mono pathSplit_comp_headRel_le) _)
      (comp_mono_left _ pathSplit_comp_headRel_le)) headAlg_map.2
  refine le_trans (inter_mono (le_refl (pathR wt))
    (recip_comp_le_of_simple_comp headRel_map hsimple)) ?_
  refine le_iff.mpr ?_
  rintro p q ⟨hcost, x, hx, hq⟩
  exact ⟨hcost, hx ▸ hq⟩

end Paths

end Freyd.Alg
