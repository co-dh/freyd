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
  2. The rest of the page rewrites the ALGEBRA, one theorem per printed line: bifunctors, the
     power transpose of a composition, (8.4) (`powerRel_thinRel_comp_bigUnion_le`),
     thin-elimination (8.3) (`Λ_comp_est_comp_singletonMap_le_thinRel`), `P τ·union = id` and
     `P = E` on functions.  `thinning_paths_alg` composes them.
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
-- §8.2's algebra IS a bifunctor at `∋` and the structure map, so the binary relator of §5.5 is
-- what states it; the split of the algebra's source is that bifunctor's interchange.
public import AOP.A5_5_TypeFunctor
public import AOP.A6_1_RelSet
-- the layered network's paths are `ConsList V V`, whose base relator `X ↦ (V→Prop)+(V→Prop)×X`
-- is what `thinning_paths`'s `F` is instantiated to below.
public import AOP.A6_ConsList
-- `est`'s pointwise form at Rel(Set), `Λ_comp_est_apply`, proved where §7.1's `est` and §6.1's
-- set model meet; the `path-defn` rows at the end read the two transposes off it.
public import AOP.A7_2_RelSet
import AOP.CalcSteps

universe u

namespace Freyd.Alg
open PowerAllegory

/-- A MAP is monotonic on `⊤`, so §8.5's and §8.6's `P ≜ ⊤` costs their derivations nothing:
    every candidate list counts as sorted. -/
public theorem graph_pres_topMor {F : Relator RelSet.{0} RelSet.{0}} {A : RelSet.{0}}
    (f : (F.obj A).carrier → A.carrier) :
    Freyd.Alg.Pres (F := F) (RelSet.graph f) (topMor A A) :=
  RelSet.le_iff.mpr fun u r _ => ⟨f u, rfl, RelSet.topMor_apply _ r⟩

section Generic

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {A C w : 𝒜}

/-- **The power transpose of a composition** (book p.198, the first step of the calculation):
    `Λ(S·V) = union·P(ΛS)·ΛV`, mirrored `Λ (V ≫ S) = Λ V ≫ P(Λ S) ≫ union`.
    `Λ V` absorbs the existential image of `S`, and an existential image is the transpose's own
    image followed by `union`. -/
public theorem Λ_comp_eq_Λ_comp_powerRel_bigUnion (V : C ⟶ w) (S : w ⟶ A) :
    Λ (V ≫ S) = Λ V ≫ powerRel (Λ S) ≫ union := by
  rw [← Λ_absorption V S, existsImage_eq_Λ_bigUnion S, powerRel_map (Λ_is_map' S)]

/-! ## The layered network's algebra is a BIFUNCTOR at `∋` and the structure map

  The p.198 derivation reads the algebra as a binary relator `F(−,−)` — the layers in the first
  argument, the recursion in the second — applied to `∋` and to the structure map `α`.  The fold's
  own relator is then `F(E A,−)`, its specification algebra `F(∋,𝟙)α`, and the split of the
  algebra's source that §8.2 needs is INTERCHANGE, `F(∋,𝟙)F(𝟙,∋) = F(∋,∋) = F(𝟙,∋)F(∋,𝟙)`, a
  theorem of the bifunctor rather than a hypothesis about an unnamed `V·S`. -/

section Layered

variable {B : 𝒜} {F : BiRelator 𝒜}

/-! ### The algebra chain of p.198, one `calc` step per law

  Each step of `thinning_paths_alg` relates two consecutive lines of the book calculation, mirrored, at the
  split `V ≜ F(∋,𝟙)` of `F(∋,∋)`; `calc_steps` names step i `thinning_paths_alg.step_i`.  `union` is written
  `E(∋)`, its definition (`bigUnion_eq_existsImage_eps`), so the chain reads one operator `E`. -/

/-- `S ≜ F(𝟙,∋)α` (book p.198), the letter of the side condition `R∩(S°S)⊑Q` and nothing else:
    the chain spells the composite out, so every panel draws `F(𝟙,∋)` and `α`. -/
@[expose] public abbrev algSplit (F : BiRelator 𝒜) (α : F.obj A B ⟶ B) : F.obj A (P B) ⟶ B :=
  F.map (𝟙 A) (∋ B) ≫ α

/-- p.198 {since `P = E` on functions}: at a map `α`,
    `Λ(V) P(Λ(F(𝟙,∋)) P(α) est(R)) = Λ(V) P(Λ(F(𝟙,∋)α) est(R))`. -/
public theorem thinning_paths_alg_map {α : F.obj A B ⟶ B} (hα : Map α) (R : B ⟶ B) :
    Λ (F.map (∋ A) (𝟙 (P B)))
        ≫ powerRel (Λ (F.map (𝟙 A) (∋ B)) ≫ powerRel α ≫ est R)
      = Λ (F.map (∋ A) (𝟙 (P B))) ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α) ≫ est R) := by
  rw [powerRel_map hα, ← Cat.assoc (Λ (F.map (𝟙 A) (∋ B))), Λ_absorption]

/-- **The algebra chain of book p.198 at the layered network**: the thinned algebra is above the
    one the program runs —
    `thin Q·Λ(α·F(∈,∈)) ⊒ P(min R·Λ(α·F(id,∈)))·ΛF(∈,id)`, mirrored
    `Λ(V) P(Λ(F(𝟙,∋)α) est(R)) ⊑ Λ(F(∋,∋)α) thin(Q)`, at `R ∩ ((F(𝟙,∋)α)°F(𝟙,∋)α) ⊑ Q`:
    the book's chain from the bottom line up, one `calc` step per law. -/
public theorem thinning_paths_alg {α : F.obj A B ⟶ B} {Q R : B ⟶ B}
    (hQ : R ∩ ((algSplit F α)° ≫ algSplit F α) ⊑ Q) :
    Λ (F.map (∋ A) (𝟙 (P B)))
        ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α) ≫ est R)
      ⊑ Λ (F.map (∋ A) (∋ B) ≫ α) ≫ thinRel Q :=
  calc Λ (F.map (∋ A) (𝟙 (P B))) ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α) ≫ est R)
        = Λ (F.map (∋ A) (𝟙 (P B))) ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α) ≫ est R) ≫ 𝟙 (P B) := by
          rw [Cat.comp_id]
    _ = Λ (F.map (∋ A) (𝟙 (P B))) ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α) ≫ est R)
          ≫ powerRel (singletonMap : B ⟶ P B) ≫ existsImage (∋ B) := by
      rw [powerRel_singletonMap_comp_existsImage_eps]
    _ = Λ (F.map (∋ A) (𝟙 (P B)))
          ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α) ≫ est R ≫ singletonMap) ≫ existsImage (∋ B) := by
      rw [← Cat.assoc (Λ _) (est R), powerRel_comp (Λ _ ≫ est R) singletonMap, Cat.assoc]
    _ ⊑ Λ (F.map (∋ A) (𝟙 (P B)))
          ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α) ≫ thinRel Q) ≫ existsImage (∋ B) :=
      comp_mono_left _ (comp_mono_right (powerRel_mono (Λ_comp_est_comp_singletonMap_le_thinRel hQ)) _)
    _ = Λ (F.map (∋ A) (𝟙 (P B))) ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α))
          ≫ powerRel (thinRel Q) ≫ existsImage (∋ B) := by
      rw [powerRel_comp, Cat.assoc]
    _ ⊑ Λ (F.map (∋ A) (𝟙 (P B))) ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α))
          ≫ existsImage (∋ B) ≫ thinRel Q :=
      comp_mono_left _ (comp_mono_left _ (powerRel_thinRel_comp_bigUnion_le Q))
    _ = Λ (F.map (∋ A) (𝟙 (P B)) ≫ (F.map (𝟙 A) (∋ B) ≫ α)) ≫ thinRel Q := by
      rw [Λ_comp_eq_Λ_comp_powerRel_bigUnion (F.map (∋ A) (𝟙 _)) (F.map (𝟙 A) (∋ B) ≫ α),
        Cat.assoc, Cat.assoc]
      rfl
    _ = Λ (F.map (∋ A) (∋ B) ≫ α) ≫ thinRel Q := by
      rw [← Cat.assoc, F.interchange]

calc_steps thinning_paths_alg

end Layered

/-! ## The note's `path-mono`: the two laws `thinning_paths` assumes, discharged

  `thinning_paths` (`AOP.A8_2_Exec`) discharges Corollary 8.1's `hmono` and (8.3)'s `hQ` with them.  The note's `path-mono` table states
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

end Generic

/-! ### The layered network itself (book p.196)

  A layered network is a non-empty sequence of sets of vertices; a path through it is a non-empty
  sequence of vertices, one from each layer, and `wt` gives the cost of stepping from one vertex
  to the next.  So the paths are `ConsList V V` (`wrap` a single vertex, `cons` one on the front)
  and the input functor is `X ↦ (V→Prop) + (V→Prop)×X`, i.e. `AOP.A6_ConsList`'s relator at
  leaf and element type `V→Prop` — the layers. -/

section Paths

open RelSet RelSet.CL

variable {A : Type}

/-- The first vertex of a path. -/
@[expose] public def headOf : ConsList A A → A
  | ConsList.wrap v => v
  | ConsList.cons v _ => v

/-- `cost [a₀,…,aₙ] = (+j : 0 ≤ j < n : wt(aⱼ,aⱼ₊₁))` (book p.196), as the `consw` recursion
    `cost(cons(a,x)) = wt(a,head x) + cost x`. -/
@[expose] public def costOf (wt : A → A → Nat) : ConsList A A → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons v q => wt v (headOf q) + costOf wt q

/-- `R ≜ cost≤cost°` (book p.196), written as the book composes it so the note's definition line
    is printed from this value. -/
@[expose] public def pathR (wt : A → A → Nat) : dCL A A ⟶ dCL A A :=
  RelSet.graph (costOf wt) ≫ leRel ≫ (RelSet.graph (costOf wt))°

/-- `p R q` iff `p` costs no more than `q`. -/
public theorem pathR_apply (wt : A → A → Nat) (p q : ConsList A A) :
    pathR wt p q ↔ costOf wt p ≤ costOf wt q :=
  ⟨fun ⟨_, h1, _, h2, h3⟩ => by subst h1 h3; exact h2, fun h => ⟨_, rfl, _, h, rfl⟩⟩

/-- `zero`, a one-vertex path's cost. -/
@[expose] public def zeroCost : dL A ⟶ (⟨Nat⟩ : RelSet.{0}) := RelSet.graph fun _ => 0

/-- `wrapz ≜ ⟨wrap,zero⟩` (book p.196). -/
@[expose] public def wrapz : dL A ⟶ (⟨ConsList A A × Nat⟩ : RelSet.{0}) := rpair wrapR zeroCost

/-- `consw` (book p.196) as a function on points. -/
@[expose] public def conswFn (wt : A → A → Nat) (a : A) (q : ConsList A A × Nat) : ConsList A A × Nat :=
  (ConsList.cons a q.1, wt a (headOf q.1) + q.2)

/-- `consw(a,(xs,n)) = (cons(a,xs),wt(a,head(xs))+n)`. -/
public theorem conswFn_apply (wt : A → A → Nat) (a : A) (xs : ConsList A A) (n : Nat) :
    conswFn wt a (xs, n) = (ConsList.cons a xs, wt a (headOf xs) + n) := rfl

/-- `consw` as an arrow, the algebra's right summand. -/
@[expose] public def consw (wt : A → A → Nat) :
    (⟨A × (ConsList A A × Nat)⟩ : RelSet.{0}) ⟶ (⟨ConsList A A × Nat⟩ : RelSet.{0}) :=
  RelSet.graph fun q => conswFn wt q.1 q.2

/-- `wrapz` on a point: `a ↦ ([a],0)`. -/
public theorem wrapz_apply (a : A) (r : ConsList A A × Nat) :
    wrapz a r ↔ r = (ConsList.wrap a, 0) :=
  ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => by subst h; exact ⟨rfl, rfl⟩⟩

/-- `consw` on a point: `(a,(xs,n)) ↦ ([a]⧺xs, wt(a,head(xs))+n)`. -/
public theorem consw_apply (wt : A → A → Nat) (a : A) (xs : ConsList A A) (n : Nat)
    (r : ConsList A A × Nat) :
    consw wt (a, (xs, n)) r ↔ r = (ConsList.cons a xs, wt a (headOf xs) + n) := Iff.rfl

/-- `cost ≜ ⦇[wrapz,consw]⦈π₂` (book p.196): the fold builds the path beside its cost, and the
    cost is read off. -/
@[expose] public def pathCost (wt : A → A → Nat) : dCL A A ⟶ (⟨Nat⟩ : RelSet.{0}) :=
  cataR (junc (sumCop (dL A) (⟨A × (ConsList A A × Nat)⟩ : RelSet.{0})) wrapz (consw wt))
    ≫ RelSet.graph Prod.snd

/-- The fold `⦇[wrapz,consw]⦈` relates a path to itself beside `costOf` of it. -/
public theorem cataR_wrapz_consw_apply (wt : A → A → Nat) : ∀ (xs : ConsList A A)
    (r : ConsList A A × Nat),
    cataR (junc (sumCop (dL A) (⟨A × (ConsList A A × Nat)⟩ : RelSet.{0})) wrapz (consw wt)) xs r
      ↔ r = (xs, costOf wt xs)
  | .wrap v, r => by
    constructor
    · rintro (⟨x, hx, h1, h2⟩ | ⟨y, hy, -⟩)
      · cases hx
        exact Prod.ext (by first | exact h1 | exact h1.symm) (by first | exact h2 | exact h2.symm)
      · cases hy
    · intro h
      subst h
      exact Or.inl ⟨v, rfl, rfl, rfl⟩
  | .cons a xs, r => by
    constructor
    · rintro ⟨r', h1, (⟨x, hx, -⟩ | ⟨y, hy, h2⟩)⟩
      · cases hx
      · cases hy
        have h1 := (cataR_wrapz_consw_apply wt xs r').mp h1
        subst h1
        first | exact h2 | exact h2.symm
    · intro h
      subst h
      exact ⟨_, (cataR_wrapz_consw_apply wt xs _).mpr rfl, Or.inr ⟨_, rfl, rfl⟩⟩

/-- `cost` is the structural `costOf`, as an arrow. -/
public theorem pathCost_eq (wt : A → A → Nat) :
    pathCost wt = (RelSet.graph (costOf wt) : dCL A A ⟶ (⟨Nat⟩ : RelSet.{0})) := by
  apply hom_ext
  intro xs n
  constructor
  · rintro ⟨r, h1, h2⟩
    have h1 := (cataR_wrapz_consw_apply wt xs r).mp h1
    subst h1
    exact h2
  · intro h
    exact ⟨_, (cataR_wrapz_consw_apply wt xs _).mpr rfl, h⟩

/-- `⦇[wrapz,consw]⦈ = ⟨𝟙,cost⟩` (book p.196). -/
public theorem cataR_wrapz_consw (wt : A → A → Nat) :
    cataR (junc (sumCop (dL A) (⟨A × (ConsList A A × Nat)⟩ : RelSet.{0})) wrapz (consw wt))
      = rpair (𝟙 (dCL A A)) (pathCost wt) := by
  apply hom_ext
  intro xs r
  rw [cataR_wrapz_consw_apply, pathCost_eq]
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext (by first | exact h1 | exact h1.symm) (by first | exact h2 | exact h2.symm)

/-- `Sspec ≜ F(∋,𝟙)α`, the specification's algebra: take a vertex out of the layer and `wrap` it,
    or `cons` it onto the partial path already built. -/
@[expose] public def pathAlg : (CL.F (A → Prop) (A → Prop)).obj (dCL A A) ⟶ dCL A A :=
  fun u p => match u with
    | Sum.inl S => ∃ v, S v ∧ p = ConsList.wrap v
    | Sum.inr q => ∃ v, q.1 v ∧ p = ConsList.cons v q.2

/-- 8.2d's `F(A,X) = A + A×X` as a binary relator on `Rel(Set)` (book p.196): unlike `CL.FB`,
    the layer `A` moves in the leaf too, because a layer is what both summands draw from. -/
@[expose] public def pathF : BiRelator RelSet.{0} where
  obj a x := ⟨a.carrier ⊕ a.carrier × x.carrier⟩
  map R S := fun u v => match u, v with
    | Sum.inl d, Sum.inl d' => R d d'
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ S p.2 q.2
    | _, _ => False
  map_id a x := hom_ext fun u v => by
    cases u <;> cases v <;> simp only [id_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      Prod.ext_iff]
  map_comp R R' S S' := by
    apply hom_ext; intro u w
    constructor
    · intro h
      cases u with
      | inl d => cases w with
        | inl d' => obtain ⟨m, h1, h2⟩ := h; exact ⟨Sum.inl m, h1, h2⟩
        | inr q => exact h.elim
      | inr p => cases w with
        | inl d' => exact h.elim
        | inr q =>
            obtain ⟨⟨e, h1, h2⟩, ⟨x, h3, h4⟩⟩ := h
            exact ⟨Sum.inr (e, x), ⟨h1, h3⟩, ⟨h2, h4⟩⟩
    · rintro ⟨v, hv, hw⟩
      cases u with
      | inl d => cases v with
        | inl m => cases w with
          | inl d'' => exact ⟨m, hv, hw⟩
          | inr q => exact hw.elim
        | inr q => exact hv.elim
      | inr p => cases v with
        | inl d => exact hv.elim
        | inr q => cases w with
          | inl d => exact hw.elim
          | inr r => exact ⟨⟨q.1, hv.1, hw.1⟩, ⟨q.2, hv.2, hw.2⟩⟩
  map_mono h1 h2 := le_iff.mpr fun u v hu => by
    cases u with
    | inl d => cases v with
      | inl d' => exact le_iff.mp h1 _ _ hu
      | inr q => exact hu.elim
    | inr p => cases v with
      | inl d => exact hu.elim
      | inr q => exact ⟨le_iff.mp h1 _ _ hu.1, le_iff.mp h2 _ _ hu.2⟩

/-- 8.2d's `F(𝟙,S)` is §6.1's cons-list relator at the layer type: with the layer held still the
    bifunctor's leaf arm is an identity, which is all `CL.F` does there (book p.196). -/
public theorem pathF_map_id (D : RelSet.{0}) {B C : RelSet.{0}} (S : B ⟶ C) :
    pathF.map (𝟙 D) S = (CL.F D.carrier D.carrier).map S :=
  hom_ext fun u v => by cases u <;> cases v <;> exact Iff.rfl

/-- `F(R,S) = [R inl, (R×S) inr]`: the network's bifunctor is the sum of its two arms, each
    followed by its injection — the form the two transposes below are read off. -/
public theorem pathF_map_eq_junc {B B' X X' : RelSet.{0}} (R : B ⟶ B') (S : X ⟶ X') :
    pathF.map R S = junc (sumCop B ⟨B.carrier × X.carrier⟩)
      (R ≫ (sumCop B' ⟨B'.carrier × X'.carrier⟩).u₁)
      (rprodMap R S ≫ (sumCop B' ⟨B'.carrier × X'.carrier⟩).u₂) :=
  hom_ext fun u v => by
    show _ ↔ (∃ x', u = Sum.inl x' ∧ ∃ m, R x' m ∧ v = Sum.inl m)
      ∨ (∃ y', u = Sum.inr y' ∧ ∃ m, rprodMap R S y' m ∧ v = Sum.inr m)
    cases u <;> cases v <;> simp only [pathF, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and,
      and_false, exists_false, or_false, false_or, exists_eq_left', exists_eq_right']
      <;> exact Iff.rfl

/-- The left injection `l` of `Rel(Set)`'s coproduct is the graph of `inl`. -/
public theorem sumCop_u₁_eq (B C : RelSet.{0}) : (sumCop B C).u₁ = RelSet.graph Sum.inl := rfl

/-- The right injection `r` of `Rel(Set)`'s coproduct is the graph of `inr`. -/
public theorem sumCop_u₂_eq (B C : RelSet.{0}) : (sumCop B C).u₂ = RelSet.graph Sum.inr := rfl

/-- `l` on a point: `a ↦ l(a)`. -/
public theorem sumCop_u₁_apply (B C : RelSet.{0}) (a : B.carrier) (s : B.carrier ⊕ C.carrier) :
    (sumCop B C).u₁ a s ↔ s = Sum.inl a := Iff.rfl

/-- `r` on a point: `b ↦ r(b)`. -/
public theorem sumCop_u₂_apply (B C : RelSet.{0}) (b : C.carrier) (s : B.carrier ⊕ C.carrier) :
    (sumCop B C).u₂ b s ↔ s = Sum.inr b := Iff.rfl

/-- `F(∋,𝟙)%∋ = [𝟙 P(inl), cpl P(inr)]` (book p.198's `ΛF(∈,id) = id + cpl`): a set of layer
    vertices injects whole, and beside a partial path `cpl` pairs the path with each vertex. -/
public theorem Λ_pathF_map_eps_id (B X : RelSet.{0}) :
    Λ (pathF.map (∋ B) (𝟙 X))
      = junc (sumCop (P B) ⟨(P B).carrier × X.carrier⟩)
          (𝟙 (P B) ≫ powerRel (sumCop B ⟨B.carrier × X.carrier⟩).u₁)
          (cplMap X B ≫ powerRel (sumCop B ⟨B.carrier × X.carrier⟩).u₂) := by
  have hu₁ : Map (sumCop B ⟨B.carrier × X.carrier⟩).u₁ := graph_map _
  have hu₂ : Map (sumCop B ⟨B.carrier × X.carrier⟩).u₂ := graph_map _
  rw [pathF_map_eq_junc, Λ_junc, powerRel_map hu₁, powerRel_map hu₂,
    ← Λ_absorption, ← Λ_absorption, Λ_eps_reflection]
  simp only [cplMap, cpMap, Relator.prod, Relator.const, Relator.idRelator]
  rw [prodMap_eq_rprodMap]
  exact rfl

/-- `F(𝟙,∋)%∋ = [τ P(inl), cpr P(inr)]` (book p.198's `id + cpr`): a leaf vertex becomes the
    singleton of its injection, and `cpr` pairs a vertex with each tail of the set beside it. -/
public theorem Λ_pathF_map_id_eps (B X : RelSet.{0}) :
    Λ (pathF.map (𝟙 B) (∋ X))
      = junc (sumCop B ⟨B.carrier × (P X).carrier⟩)
          (singletonMap ≫ powerRel (sumCop B ⟨B.carrier × X.carrier⟩).u₁)
          (cprMap B X ≫ powerRel (sumCop B ⟨B.carrier × X.carrier⟩).u₂) := by
  have hu₁ : Map (sumCop B ⟨B.carrier × X.carrier⟩).u₁ := graph_map _
  have hu₂ : Map (sumCop B ⟨B.carrier × X.carrier⟩).u₂ := graph_map _
  rw [pathF_map_eq_junc, Λ_junc, powerRel_map hu₁, powerRel_map hu₂,
    ← Λ_absorption, ← Λ_absorption]
  simp only [cprMap, cpMap, Relator.prod, Relator.const, Relator.idRelator]
  rw [prodMap_eq_rprodMap]
  exact rfl

/-- `F(𝟙,∋)α`, the second factor of book p.198's split of the algebra's source. -/
@[expose] public def pathSplit : Fobj A A (pow (dCL A A)) ⟶ dCL A A :=
  pathF.map (𝟙 _) (∋ _) ≫ alphaR

/-- `S`'s pointwise reading: `wrap` the leaf vertex, or `cons` the vertex onto some tail of the
    set. -/
public theorem pathSplit_apply (u : (Fobj A A (pow (dCL A A))).carrier) (p : ConsList A A) :
    pathSplit u p ↔ match u with
      | Sum.inl v => p = ConsList.wrap v
      | Sum.inr q => ∃ t, q.2 t ∧ p = ConsList.cons q.1 t := by
  cases u with
  | inl v =>
    constructor
    · rintro ⟨u', hu, hp⟩
      cases u' with
      | inl v' =>
        have hv : v = v' := hu
        subst hv
        exact hp
      | inr r => exact hu.elim
    · intro h
      exact ⟨Sum.inl v, rfl, h⟩
  | inr q =>
    obtain ⟨a, S⟩ := q
    constructor
    · rintro ⟨u', hu, hp⟩
      cases u' with
      | inl v' => exact hu.elim
      | inr r =>
        obtain ⟨b, t⟩ := r
        obtain ⟨h1, h2⟩ := hu
        have h1' : a = b := h1
        subst h1'
        exact ⟨t, h2, hp⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Sum.inr (a, t), ⟨rfl, ht⟩, rfl⟩

/-- `head : LA ⟶ A`. -/
@[expose] public def head : dCL A A ⟶ (⟨A⟩ : RelSet.{0}) := RelSet.graph headOf

/-- `[𝟙,π₁] : F(A,E(LA)) ⟶ A`, the first vertex of whatever `S` builds. -/
@[expose] public def headAlg : Fobj A A (pow (dCL A A)) ⟶ (⟨A⟩ : RelSet.{0}) :=
  RelSet.graph fun u => match u with | Sum.inl v => v | Sum.inr q => q.1

public theorem headRel_map : Map (head (A := A)) := RelSet.graph_map _

/-- `Q ≜ R∩(head head°)` (book p.197): no dearer, and starting at the same vertex. -/
@[expose] public def pathQ (wt : A → A → Nat) : dCL A A ⟶ dCL A A :=
  pathR wt ∩ (head ≫ head°)

public theorem pathQ_apply (wt : A → A → Nat) (p q : ConsList A A) :
    pathQ wt p q ↔ costOf wt p ≤ costOf wt q ∧ headOf p = headOf q :=
  ⟨fun ⟨h, _, h1, h2⟩ => ⟨(pathR_apply wt p q).mp h, by subst h1; exact h2⟩,
    fun ⟨h, e⟩ => ⟨(pathR_apply wt p q).mpr h, _, rfl, e⟩⟩

/-- `Q ⊑ R` (book p.197): `Q` is `R` with the head recorded. -/
public theorem pathQ_le_pathR (wt : A → A → Nat) : pathQ wt ⊑ pathR wt :=
  le_iff.mpr fun _ _ h => h.1

/-- `R ≜ cost≤cost°` is a preorder (book p.197), because `≤` on costs is. -/
public theorem pathR_preorder (wt : A → A → Nat) : preorder (pathR wt) :=
  ⟨le_iff.mpr fun p q (h : p = q) => by subst h; exact (pathR_apply wt p p).mpr (Nat.le_refl _),
   le_iff.mpr fun _ _ ⟨_, h1, h2⟩ =>
     (pathR_apply wt _ _).mpr (Nat.le_trans ((pathR_apply wt _ _).mp h1) ((pathR_apply wt _ _).mp h2))⟩

/-- `Q ≜ R∩(head head°)` is a preorder (book p.197): both `≤` on costs and `=` on heads are. -/
public theorem pathQ_preorder (wt : A → A → Nat) : preorder (pathQ wt) :=
  ⟨le_iff.mpr fun p q (h : p = q) => by subst h; exact (pathQ_apply wt p p).mpr ⟨Nat.le_refl _, rfl⟩,
   le_iff.mpr fun _ _ ⟨_, h1, h2⟩ =>
     have h1 := (pathQ_apply wt _ _).mp h1; have h2 := (pathQ_apply wt _ _).mp h2
     (pathQ_apply wt _ _).mpr ⟨Nat.le_trans h1.1 h2.1, h1.2.trans h2.2⟩⟩

public theorem headAlg_map : Map (headAlg (A := A)) := RelSet.graph_map _

/-- **The first law of the note's `path-mono`** (book p.197): `F(∋,Q)α ⊑ F(∋,𝟙)αQ`, mirrored
    `MonotonicAlg Sspec Q`.  Consing the same vertex onto a `Q`-better path gives a `Q`-better
    path: equal heads make the new edge cost the same, and the rest is the assumption.  On `R`
    alone it fails — `wt(a,head q)` can be arbitrarily large — which is why `Q` records the head. -/
public theorem pathAlg_monotonic (wt : A → A → Nat) :
    Freyd.Alg.Pres (F := CL.F (A → Prop) (A → Prop)) (pathAlg (A := A)) (pathQ wt) := by
  refine le_iff.mpr ?_
  rintro u p ⟨u', hu, hp⟩
  cases u with
  | inl S =>
    cases u' with
    | inl S' =>
      have hS : S = S' := hu
      subst hS
      exact ⟨p, hp, (pathQ_apply wt p p).mpr ⟨Nat.le_refl _, rfl⟩⟩
    | inr q' => exact hu.elim
  | inr q =>
    cases u' with
    | inl S' => exact hu.elim
    | inr q' =>
      obtain ⟨hSS, hq⟩ := hu
      obtain ⟨v, hv, rfl⟩ := hp
      refine ⟨ConsList.cons v q.2, ⟨v, by rw [hSS]; exact hv, rfl⟩, (pathQ_apply wt _ _).mpr ⟨?_, rfl⟩⟩
      obtain ⟨hq1, hq2⟩ := (pathQ_apply wt _ _).mp hq
      show wt v (headOf q.2) + costOf wt q.2 ≤ wt v (headOf q'.2) + costOf wt q'.2
      rw [hq2]
      exact Nat.add_le_add_left hq1 _

/-- **The second law of the note's `path-mono`** (book p.198, left as an exercise there):
    `S head ⊑ [𝟙,π₁]` — whichever path `S` builds, its first vertex is fixed by `S`'s argument
    alone, so `S head` is simple. -/
public theorem pathSplit_comp_headRel_le : pathSplit (A := A) ≫ head ⊑ headAlg := by
  refine le_iff.mpr ?_
  rintro u x ⟨p, hp, hx⟩
  have hp := (pathSplit_apply u p).mp hp
  cases u with
  | inl v => subst hp; exact hx
  | inr q => obtain ⟨t, _, rfl⟩ := hp; exact hx

/-- `thinning_paths`'s `hQ` for the network (book p.198): `R∩((F(𝟙,∋)α)°F(𝟙,∋)α) ⊑ Q` at `Q ≜ R∩(head head°)`.
    `S head ⊑ [𝟙,π₁]` makes `S head` simple, and the shunting step turns that into
    `S°S ⊑ head head°`. -/
public theorem pathR_inter_recip_le_pathQ (wt : A → A → Nat) :
    pathR wt ∩ ((pathSplit (A := A))° ≫ pathSplit) ⊑ pathQ wt := by
  have hsimple : Simple (pathSplit (A := A) ≫ head) :=
    le_trans (le_trans (comp_mono_right (recip_mono pathSplit_comp_headRel_le) _)
      (comp_mono_left _ pathSplit_comp_headRel_le)) headAlg_map.2
  exact inter_mono (le_refl (pathR wt)) (recip_comp_le_of_simple_comp headRel_map hsimple)

/-! ### The note's `path-defn`: the transposes computed on the coproduct

  The last two steps of p.198 leave the thinning alone: they compute the two transposes
  `ΛF(∋,𝟙)` and `ΛF(𝟙,∋)` at `F(A,X) = A + A×X` and read the printed program off the summands.
  Both are `Λ_junc` — a transpose taken one summand at a time. -/

/-- `step ≜ cpr P(cons) est(R)` (book p.198): the vertex distributes over the SET of tails, `cons`
    goes on each of them, and `est R` keeps a cheapest one. -/
@[expose] public def pathStep (wt : A → A → Nat) :
    (⟨A × (pow (dCL A A)).carrier⟩ : RelSet.{0}) ⟶ dCL A A :=
  cprMap (dE A) (dCL A A) ≫ powerRel consR ≫ est (pathR wt)

/-- `F(𝟙,∋)α` (book p.198): what `pathSplit`'s definition says in words — the bifunctor at
    `∋` in the recursion argument, followed by the constructor. -/
public theorem pathSplit_eq_Fmap_comp_alphaR :
    (pathSplit (A := A)) = (CL.F A A).map (∋ (dCL A A)) ≫ alphaR := by
  unfold pathSplit
  rw [pathF_map_id]

/-- **`F(𝟙,∋) P(α) est(R) = [wrap,step]`** (book p.198, the note's `path-defn`): the second
    transpose, computed on the same coproduct.  On the leaf summand there is no set to distribute,
    so the transpose is the singleton and `est R` gives `wrap` back; on the `A×X` summand it is
    `cpr`, and consing onto each tail and keeping a cheapest one is `step`. -/
public theorem cpMap_comp_powerRel_alphaR_comp_est_eq_junc (wt : A → A → Nat) :
    cpMap (CL.F A A) (dCL A A)
        ≫ powerRel (alphaR : (CL.F A A).obj (dCL A A) ⟶ dCL A A) ≫ est (pathR wt)
      = junc (sumCop (dL A) (⟨A × (pow (dCL A A)).carrier⟩ : RelSet.{0})) wrapR (pathStep wt) := by
  have hα : Map (alphaR : (CL.F A A).obj (dCL A A) ⟶ dCL A A) := graph_map _
  have hc : Map (consR : (⟨A × ConsList A A⟩ : RelSet.{0}) ⟶ dCL A A) := graph_map _
  have hL : cpMap (CL.F A A) (dCL A A)
      ≫ powerRel (alphaR : (CL.F A A).obj (dCL A A) ⟶ dCL A A) = Λ (pathSplit (A := A)) := by
    simp only [cpMap]
    rw [powerRel_map hα, Λ_absorption, ← pathSplit_eq_Fmap_comp_alphaR]
  have hS : pathStep wt
      = Λ (rprodMap (𝟙 (dE A)) (∋ (dCL A A)) ≫ consR) ≫ est (pathR wt) := by
    simp only [pathStep, cprMap, cpMap, Relator.prod, Relator.const, Relator.idRelator]
    rw [prodMap_eq_rprodMap, ← Cat.assoc, powerRel_map hc, Λ_absorption]
    rfl
  have hstep : ∀ (q : A × (pow (dCL A A)).carrier) (z : ConsList A A),
      pathSplit (A := A) (Sum.inr q) z
        ↔ (rprodMap (𝟙 (dE A)) (∋ (dCL A A)) ≫ consR) q z := by
    rintro ⟨a, S⟩ z
    rw [pathSplit_apply]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(a, t), ⟨rfl, ht⟩, rfl⟩
    · rintro ⟨r, ⟨h1, h2⟩, hr⟩
      obtain ⟨b, t⟩ := r
      have h1' : a = b := h1
      subst h1'
      exact ⟨t, h2, hr⟩
  rw [← Cat.assoc, hL, hS]
  apply hom_ext
  intro u p
  rw [Λ_comp_est_apply]
  cases u with
  | inl v =>
    constructor
    · rintro ⟨h, -⟩
      exact Or.inl ⟨v, rfl, (pathSplit_apply _ _).mp h⟩
    · rintro (⟨x, hx, hw⟩ | ⟨y, hy, -⟩)
      · have hxv : v = x := Sum.inl.inj hx
        subst hxv
        have hp : p = ConsList.wrap v := hw
        subst hp
        refine ⟨(pathSplit_apply _ _).mpr rfl, ?_⟩
        intro z hz
        have hz' : z = ConsList.wrap v := (pathSplit_apply _ _).mp hz
        subst hz'
        exact (pathR_apply wt _ _).mpr (Nat.le_refl _)
      · exact (nomatch hy)
  | inr q =>
    constructor
    · rintro ⟨h, hmin⟩
      refine Or.inr ⟨q, rfl, (Λ_comp_est_apply _ _ _ _).mpr ⟨(hstep q p).mp h, ?_⟩⟩
      intro z hz
      exact hmin z ((hstep q z).mpr hz)
    · rintro (⟨x, hx, -⟩ | ⟨y, hy, hy2⟩)
      · exact (nomatch hx)
      · have hyq : q = y := Sum.inr.inj hy
        subst hyq
        obtain ⟨h, hmin⟩ := (Λ_comp_est_apply _ _ _ _).mp hy2
        refine ⟨(hstep q p).mpr h, ?_⟩
        intro z hz
        exact hmin z ((hstep q z).mp hz)

end Paths

-- printing-only: B&dM p.196 names the cost order `R` and p.197 its refinement `Q`, and p.198 the
-- step `step`; `path` is only Lean's prefix, kept apart from `Edit`'s `step`.  Each drops `wt`.
open Lean PrettyPrinter in
@[app_unexpander pathR] public meta def unexpandPathR : Unexpander
  | `($_ $_) => `($(mkIdent `R))
  | `($_ $_ $args*) => `($(mkIdent `R) $args*)
  | _ => `($(mkIdent `R))
open Lean PrettyPrinter in
@[app_unexpander pathQ] public meta def unexpandPathQ : Unexpander
  | `($_ $_) => `($(mkIdent `Q))
  | `($_ $_ $args*) => `($(mkIdent `Q) $args*)
  | _ => `($(mkIdent `Q))
open Lean PrettyPrinter in
@[app_unexpander pathStep] public meta def unexpandPathStep : Unexpander
  | `($_ $_) => `($(mkIdent `step))
  | `($_ $_ $args*) => `($(mkIdent `step) $args*)
  | _ => `($(mkIdent `step))
open Lean PrettyPrinter in
@[app_unexpander headOf] public meta def unexpandHeadOf : Unexpander
  | `($_ $args*) => `($(mkIdent `head) $args*)
  | _ => `($(mkIdent `head))

-- printing-only: B&dM p.196's `cost` and `consw`; the weight `wt` is the section's one parameter
-- and no argument the note writes.
open Lean PrettyPrinter in
@[app_unexpander costOf] public meta def unexpandCostOf : Unexpander
  | `($_ $_) => `($(mkIdent `cost))
  | `($_ $_ $args*) => `($(mkIdent `cost) $args*)
  | _ => `($(mkIdent `cost))
open Lean PrettyPrinter in
@[app_unexpander pathCost] public meta def unexpandPathCost : Unexpander
  | `($_ $_) => `($(mkIdent `cost))
  | `($_ $_ $args*) => `($(mkIdent `cost) $args*)
  | _ => `($(mkIdent `cost))
open Lean PrettyPrinter in
@[app_unexpander conswFn] public meta def unexpandConswFn : Unexpander
  | `($_ $_) => `($(mkIdent `consw))
  | `($_ $_ $args*) => `($(mkIdent `consw) $args*)
  | _ => `($(mkIdent `consw))
open Lean PrettyPrinter in
@[app_unexpander consw] public meta def unexpandConsw : Unexpander
  | `($_ $_) => `($(mkIdent `consw))
  | `($_ $_ $args*) => `($(mkIdent `consw) $args*)
  | _ => `($(mkIdent `consw))

-- printing-only: `S ≜ F(𝟙,∋)α`, the letter of the 8.2d side condition `R∩(S°S)⊑Q` only.
open Lean PrettyPrinter in
@[app_unexpander algSplit] public meta def unexpandAlgSplit : Unexpander
  | _ => `($(mkIdent `S))

end Freyd.Alg
