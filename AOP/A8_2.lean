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
public theorem graph_monoAlg_topMor {F : Relator RelSet.{0} RelSet.{0}} {A : RelSet.{0}}
    (f : (F.obj A).carrier → A.carrier) :
    Freyd.Alg.MonoAlg (F := F) (RelSet.graph f) (topMor A A) :=
  RelSet.le_iff.mpr fun u r _ => ⟨f u, rfl, RelSet.topMor_apply _ r⟩

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {A C w : 𝒜}

/-- **The power transpose of a composition** (book p.198, the first step of the calculation):
    `Λ(S·V) = union·P(ΛS)·ΛV`, mirrored `Λ (V ≫ S) = Λ V ≫ P(Λ S) ≫ union`.
    `Λ V` absorbs the existential image of `S`, and an existential image is the transpose's own
    image followed by `union`. -/
public theorem Λ_comp_eq_Λ_comp_powerRel_bigUnion (V : C ⟶ w) (S : w ⟶ A) :
    Λ (V ≫ S) = Λ V ≫ powerRel (Λ S) ≫ bigUnion := by
  rw [← Λ_absorption V S, existsImage_eq_Λ_bigUnion S, powerRel_map (Λ_is_map' S)]

/-! ## The layered network's algebra is a BIFUNCTOR at `∋` and the structure map

  The p.198 derivation reads the algebra as a binary relator `F(−,−)` — the layers in the first
  argument, the recursion in the second — applied to `∋` and to the structure map `α`.  The fold's
  own relator is then `F(E A,−)`, its specification algebra `F(∋,𝟙)α`, and the split of the
  algebra's source that §8.2 needs is INTERCHANGE, `F(∋,𝟙)F(𝟙,∋) = F(∋,∋) = F(𝟙,∋)F(∋,𝟙)`, a
  theorem of the bifunctor rather than a hypothesis about an unnamed `V·S`. -/

section Layered

variable {B : 𝒜} {F : BiRelator 𝒜}

/-- **Corollary 8.1 at the layered network** (book p.198, the step the thinning theorem makes):
    the specification is above the thinned fold —
    `min R·Λ⦇α·F(∈,id)⦈ ⊒ min R·⦇thin Q·Λ(α·F(∈,∈))⦈`, mirrored
    `relCata (Λ (F(∋,∋)α) ≫ thin Q) ≫ est R ⊑ Λ (relCata (F(∋,𝟙)α)) ≫ est R`.
    `thinning_est` is stated at `Λ(F(∋)·S)·thin Q` for the fold's own relator `F(E A,−)`, whose
    action on `∋` is `F(𝟙,∋)`; `F(𝟙,∋)F(∋,𝟙)α` IS `F(∋,∋)α`, by interchange. -/
public theorem thinning_paths_step
    (I : InitialAlgebra (F.appl (P A)))
    {α : F.obj A B ⟶ B} {Q R : B ⟶ B}
    (hQR : Q ⊑ R) (hreflQ : 𝟙 B ⊑ Q) (htransQ : Q ≫ Q ⊑ Q) (htransR : R° ≫ R° ⊑ R°)
    (hmono : Freyd.Alg.MonoAlg
      ((F.map (∋ A) (𝟙 B) ≫ α : (F.appl (P A)).obj B ⟶ B)) Q) :
    relCata (Λ (F.map (∋ A) (∋ B) ≫ α) ≫ thinRel Q) ≫ est R
      ⊑ Λ (relCata (I := I) (F.map (∋ A) (𝟙 B) ≫ α)) ≫ est R := by
  have e : (F.appl (P A)).map (∋ B) ≫ (F.map (∋ A) (𝟙 B) ≫ α)
      = F.map (∋ A) (∋ B) ≫ α := by
    show F.map (𝟙 (P A)) (∋ B) ≫ (F.map (∋ A) (𝟙 B) ≫ α) = _
    rw [← Cat.assoc, F.interchange' (∋ A) (∋ B)]
  rw [← e]
  exact thinning_est I hQR hreflQ htransQ (trans_of_recip_trans htransR) hmono

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

/-- **The §8.2 headline** (book p.198): a least-cost path in a layered network, as a fold over
    the layers —
    `min R·Λ⦇α·F(∈,id)⦈ ⊒ min R·⦇P(min R·Λ(α·F(id,∈)))·ΛF(∈,id)⦈`, mirrored
    `relCata (Λ F(∋,𝟙) ≫ P (Λ (F(𝟙,∋)α) ≫ est R)) ≫ est R ⊑ Λ (relCata (F(∋,𝟙)α)) ≫ est R`,
    at `R ∩ ((F(𝟙,∋)α)°(F(𝟙,∋)α)) ⊑ Q`.  `thinning_paths_step` supplies the fold and
    `thinning_paths_alg` the algebra; the source `F(∋,∋)α` of the thinned algebra splits as
    `F(∋,𝟙)` followed by `F(𝟙,∋)α` by interchange.  At the book's `α = [wrap,cons]` the algebra
    `ΛF(∈,id)·P(min R·Λ(α·F(id,∈)))` is the printed `[P wrap, cpl·P step]`. -/
public theorem thinning_paths
    (I : InitialAlgebra (F.appl (P A)))
    {α : F.obj A B ⟶ B} {Q R : B ⟶ B}
    (hQR : Q ⊑ R) (hreflQ : 𝟙 B ⊑ Q) (htransQ : Q ≫ Q ⊑ Q) (htransR : R° ≫ R° ⊑ R°)
    (hmono : Freyd.Alg.MonoAlg
      ((F.map (∋ A) (𝟙 B) ≫ α : (F.appl (P A)).obj B ⟶ B)) Q)
    (hQ : R ∩ ((F.map (𝟙 A) (∋ B) ≫ α)° ≫ (F.map (𝟙 A) (∋ B) ≫ α)) ⊑ Q) :
    relCata (Λ (F.map (∋ A) (𝟙 (P B)))
        ≫ powerRel (Λ (F.map (𝟙 A) (∋ B) ≫ α) ≫ est R)) ≫ est R
      ⊑ Λ (relCata (I := I) (F.map (∋ A) (𝟙 B) ≫ α)) ≫ est R :=
  -- The terms are the two laws' own sides: spelled out, `relCata`'s initial algebra is a fresh
  -- metavariable that `whnf` cannot close within the heartbeat budget.
  calc _ ⊑ _ := comp_mono_right (relCata_le_relCata I (comp_mono_left _ (thinning_paths_alg hQ))) (est R)
    _ ⊑ _ := thinning_paths_step I hQR hreflQ htransQ htransR hmono

calc_steps thinning_paths

end Layered

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

/-- `R ≜ cost≤cost°` (book p.196), written as the book composes it so the note's definition line
    is printed from this value. -/
@[expose] public def pathR (wt : V → V → Nat) : dCL V V ⟶ dCL V V :=
  RelSet.graph (costOf wt) ≫ leRel ≫ (RelSet.graph (costOf wt))°

/-- `p R q` iff `p` costs no more than `q`. -/
public theorem pathR_apply (wt : V → V → Nat) (p q : ConsList V V) :
    pathR wt p q ↔ costOf wt p ≤ costOf wt q :=
  ⟨fun ⟨_, h1, _, h2, h3⟩ => by subst h1 h3; exact h2, fun h => ⟨_, rfl, _, h, rfl⟩⟩

/-- `zero`, a one-vertex path's cost. -/
@[expose] public def zeroCost : dL V ⟶ (⟨Nat⟩ : RelSet.{0}) := RelSet.graph fun _ => 0

/-- `wrapz ≜ ⟨wrap,zero⟩` (book p.196). -/
@[expose] public def wrapz : dL V ⟶ (⟨ConsList V V × Nat⟩ : RelSet.{0}) := rpair wrapR zeroCost

/-- `consw` (book p.196) as a function on points. -/
@[expose] public def conswFn (wt : V → V → Nat) (a : V) (q : ConsList V V × Nat) : ConsList V V × Nat :=
  (ConsList.cons a q.1, wt a (headOf q.1) + q.2)

/-- `consw(a,(xs,n)) = (cons(a,xs),wt(a,head(xs))+n)`. -/
public theorem conswFn_apply (wt : V → V → Nat) (a : V) (xs : ConsList V V) (n : Nat) :
    conswFn wt a (xs, n) = (ConsList.cons a xs, wt a (headOf xs) + n) := rfl

/-- `consw` as an arrow, the algebra's right summand. -/
@[expose] public def consw (wt : V → V → Nat) :
    (⟨V × (ConsList V V × Nat)⟩ : RelSet.{0}) ⟶ (⟨ConsList V V × Nat⟩ : RelSet.{0}) :=
  RelSet.graph fun q => conswFn wt q.1 q.2

/-- `wrapz` on a point: `a ↦ ([a],0)`. -/
public theorem wrapz_apply (a : V) (r : ConsList V V × Nat) :
    wrapz a r ↔ r = (ConsList.wrap a, 0) :=
  ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2, fun h => by subst h; exact ⟨rfl, rfl⟩⟩

/-- `consw` on a point: `(a,(xs,n)) ↦ ([a]⧺xs, wt(a,head(xs))+n)`. -/
public theorem consw_apply (wt : V → V → Nat) (a : V) (xs : ConsList V V) (n : Nat)
    (r : ConsList V V × Nat) :
    consw wt (a, (xs, n)) r ↔ r = (ConsList.cons a xs, wt a (headOf xs) + n) := Iff.rfl

/-- `cost ≜ ⦇[wrapz,consw]⦈π₂` (book p.196): the fold builds the path beside its cost, and the
    cost is read off. -/
@[expose] public def pathCost (wt : V → V → Nat) : dCL V V ⟶ (⟨Nat⟩ : RelSet.{0}) :=
  cataR (junc (sumCop (dL V) (⟨V × (ConsList V V × Nat)⟩ : RelSet.{0})) wrapz (consw wt))
    ≫ RelSet.graph Prod.snd

/-- The fold `⦇[wrapz,consw]⦈` relates a path to itself beside `costOf` of it. -/
public theorem cataR_wrapz_consw_apply (wt : V → V → Nat) : ∀ (xs : ConsList V V)
    (r : ConsList V V × Nat),
    cataR (junc (sumCop (dL V) (⟨V × (ConsList V V × Nat)⟩ : RelSet.{0})) wrapz (consw wt)) xs r
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
public theorem pathCost_eq (wt : V → V → Nat) :
    pathCost wt = (RelSet.graph (costOf wt) : dCL V V ⟶ (⟨Nat⟩ : RelSet.{0})) := by
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
public theorem cataR_wrapz_consw (wt : V → V → Nat) :
    cataR (junc (sumCop (dL V) (⟨V × (ConsList V V × Nat)⟩ : RelSet.{0})) wrapz (consw wt))
      = rpair (𝟙 (dCL V V)) (pathCost wt) := by
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
@[expose] public def pathAlg : (CL.F (V → Prop) (V → Prop)).obj (dCL V V) ⟶ dCL V V :=
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
  map_id A B := hom_ext fun u v => by
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
public theorem pathF_map_id (A : RelSet.{0}) {B C : RelSet.{0}} (S : B ⟶ C) :
    pathF.map (𝟙 A) S = (CL.F A.carrier A.carrier).map S :=
  hom_ext fun u v => by cases u <;> cases v <;> exact Iff.rfl

/-- `F(R,S) = [R inl, (R×S) inr]`: the network's bifunctor is the sum of its two arms, each
    followed by its injection — the form the two transposes below are read off. -/
public theorem pathF_map_eq_junc {A A' X X' : RelSet.{0}} (R : A ⟶ A') (S : X ⟶ X') :
    pathF.map R S = junc (sumCop A ⟨A.carrier × X.carrier⟩)
      (R ≫ (sumCop A' ⟨A'.carrier × X'.carrier⟩).u₁)
      (rprodMap R S ≫ (sumCop A' ⟨A'.carrier × X'.carrier⟩).u₂) :=
  hom_ext fun u v => by
    show _ ↔ (∃ x', u = Sum.inl x' ∧ ∃ m, R x' m ∧ v = Sum.inl m)
      ∨ (∃ y', u = Sum.inr y' ∧ ∃ m, rprodMap R S y' m ∧ v = Sum.inr m)
    cases u <;> cases v <;> simp only [pathF, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and,
      and_false, exists_false, or_false, false_or, exists_eq_left', exists_eq_right']
      <;> exact Iff.rfl

/-- The left injection `l` of `Rel(Set)`'s coproduct is the graph of `inl`. -/
public theorem sumCop_u₁_eq (A B : RelSet.{0}) : (sumCop A B).u₁ = RelSet.graph Sum.inl := rfl

/-- The right injection `r` of `Rel(Set)`'s coproduct is the graph of `inr`. -/
public theorem sumCop_u₂_eq (A B : RelSet.{0}) : (sumCop A B).u₂ = RelSet.graph Sum.inr := rfl

/-- `l` on a point: `a ↦ l(a)`. -/
public theorem sumCop_u₁_apply (A B : RelSet.{0}) (a : A.carrier) (s : A.carrier ⊕ B.carrier) :
    (sumCop A B).u₁ a s ↔ s = Sum.inl a := Iff.rfl

/-- `r` on a point: `b ↦ r(b)`. -/
public theorem sumCop_u₂_apply (A B : RelSet.{0}) (b : B.carrier) (s : A.carrier ⊕ B.carrier) :
    (sumCop A B).u₂ b s ↔ s = Sum.inr b := Iff.rfl

/-- `F(∋,𝟙)%∋ = [𝟙 P(inl), cpl P(inr)]` (book p.198's `ΛF(∈,id) = id + cpl`): a set of layer
    vertices injects whole, and beside a partial path `cpl` pairs the path with each vertex. -/
public theorem Λ_pathF_map_eps_id (A X : RelSet.{0}) :
    Λ (pathF.map (∋ A) (𝟙 X))
      = junc (sumCop (P A) ⟨(P A).carrier × X.carrier⟩)
          (𝟙 (P A) ≫ powerRel (sumCop A ⟨A.carrier × X.carrier⟩).u₁)
          (cplMap X A ≫ powerRel (sumCop A ⟨A.carrier × X.carrier⟩).u₂) := by
  have hu₁ : Map (sumCop A ⟨A.carrier × X.carrier⟩).u₁ := graph_map _
  have hu₂ : Map (sumCop A ⟨A.carrier × X.carrier⟩).u₂ := graph_map _
  rw [pathF_map_eq_junc, Λ_junc, powerRel_map hu₁, powerRel_map hu₂,
    ← Λ_absorption, ← Λ_absorption, Λ_eps_reflection]
  simp only [cplMap, cpMap, Relator.prod, Relator.const, Relator.idRelator]
  rw [prodMap_eq_rprodMap]
  exact rfl

/-- `F(𝟙,∋)%∋ = [τ P(inl), cpr P(inr)]` (book p.198's `id + cpr`): a leaf vertex becomes the
    singleton of its injection, and `cpr` pairs a vertex with each tail of the set beside it. -/
public theorem Λ_pathF_map_id_eps (A X : RelSet.{0}) :
    Λ (pathF.map (𝟙 A) (∋ X))
      = junc (sumCop A ⟨A.carrier × (P X).carrier⟩)
          (singletonMap ≫ powerRel (sumCop A ⟨A.carrier × X.carrier⟩).u₁)
          (cprMap A X ≫ powerRel (sumCop A ⟨A.carrier × X.carrier⟩).u₂) := by
  have hu₁ : Map (sumCop A ⟨A.carrier × X.carrier⟩).u₁ := graph_map _
  have hu₂ : Map (sumCop A ⟨A.carrier × X.carrier⟩).u₂ := graph_map _
  rw [pathF_map_eq_junc, Λ_junc, powerRel_map hu₁, powerRel_map hu₂,
    ← Λ_absorption, ← Λ_absorption]
  simp only [cprMap, cpMap, Relator.prod, Relator.const, Relator.idRelator]
  rw [prodMap_eq_rprodMap]
  exact rfl

/-- `F(𝟙,∋)α`, the second factor of book p.198's split of the algebra's source. -/
@[expose] public def pathSplit : Fobj V V (pow (dCL V V)) ⟶ dCL V V :=
  pathF.map (𝟙 _) (∋ _) ≫ alphaR

/-- `S`'s pointwise reading: `wrap` the leaf vertex, or `cons` the vertex onto some tail of the
    set. -/
public theorem pathSplit_apply (u : (Fobj V V (pow (dCL V V))).carrier) (p : ConsList V V) :
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
@[expose] public def headRel : dCL V V ⟶ (⟨V⟩ : RelSet.{0}) := RelSet.graph headOf

/-- `[𝟙,π₁] : F(A,E(LA)) ⟶ A`, the first vertex of whatever `S` builds. -/
@[expose] public def headAlg : Fobj V V (pow (dCL V V)) ⟶ (⟨V⟩ : RelSet.{0}) :=
  RelSet.graph fun u => match u with | Sum.inl v => v | Sum.inr q => q.1

public theorem headRel_map : Map (headRel (V := V)) := RelSet.graph_map _

/-- `Q ≜ R∩(head head°)` (book p.197): no dearer, and starting at the same vertex. -/
@[expose] public def pathQ (wt : V → V → Nat) : dCL V V ⟶ dCL V V :=
  pathR wt ∩ (headRel ≫ headRel°)

public theorem pathQ_apply (wt : V → V → Nat) (p q : ConsList V V) :
    pathQ wt p q ↔ costOf wt p ≤ costOf wt q ∧ headOf p = headOf q :=
  ⟨fun ⟨h, _, h1, h2⟩ => ⟨(pathR_apply wt p q).mp h, by subst h1; exact h2⟩,
    fun ⟨h, e⟩ => ⟨(pathR_apply wt p q).mpr h, _, rfl, e⟩⟩

public theorem headAlg_map : Map (headAlg (V := V)) := RelSet.graph_map _

/-- **The first law of the note's `path-mono`** (book p.197): `F(∋,Q)α ⊑ F(∋,𝟙)αQ`, mirrored
    `MonotonicAlg Sspec Q`.  Consing the same vertex onto a `Q`-better path gives a `Q`-better
    path: equal heads make the new edge cost the same, and the rest is the assumption.  On `R`
    alone it fails — `wt(a,head q)` can be arbitrarily large — which is why `Q` records the head. -/
public theorem pathAlg_monotonic (wt : V → V → Nat) :
    Freyd.Alg.MonoAlg (F := CL.F (V → Prop) (V → Prop)) (pathAlg (V := V)) (pathQ wt) := by
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
public theorem pathSplit_comp_headRel_le : pathSplit (V := V) ≫ headRel ⊑ headAlg := by
  refine le_iff.mpr ?_
  rintro u x ⟨p, hp, hx⟩
  have hp := (pathSplit_apply u p).mp hp
  cases u with
  | inl v => subst hp; exact hx
  | inr q => obtain ⟨t, _, rfl⟩ := hp; exact hx

/-- `thinning_paths`'s `hQ` for the network (book p.198): `R∩((F(𝟙,∋)α)°F(𝟙,∋)α) ⊑ Q` at `Q ≜ R∩(head head°)`.
    `S head ⊑ [𝟙,π₁]` makes `S head` simple, and the shunting step turns that into
    `S°S ⊑ head head°`. -/
public theorem pathR_inter_recip_le_pathQ (wt : V → V → Nat) :
    pathR wt ∩ ((pathSplit (V := V))° ≫ pathSplit) ⊑ pathQ wt := by
  have hsimple : Simple (pathSplit (V := V) ≫ headRel) :=
    le_trans (le_trans (comp_mono_right (recip_mono pathSplit_comp_headRel_le) _)
      (comp_mono_left _ pathSplit_comp_headRel_le)) headAlg_map.2
  exact inter_mono (le_refl (pathR wt)) (recip_comp_le_of_simple_comp headRel_map hsimple)

/-! ### The note's `path-defn`: the transposes computed on the coproduct

  The last two steps of p.198 leave the thinning alone: they compute the two transposes
  `ΛF(∋,𝟙)` and `ΛF(𝟙,∋)` at `F(A,X) = A + A×X` and read the printed program off the summands.
  Both are `Λ_junc` — a transpose taken one summand at a time. -/

/-- `step ≜ cpr P(cons) est(R)` (book p.198): the vertex distributes over the SET of tails, `cons`
    goes on each of them, and `est R` keeps a cheapest one. -/
@[expose] public def pathStep (wt : V → V → Nat) :
    (⟨V × (pow (dCL V V)).carrier⟩ : RelSet.{0}) ⟶ dCL V V :=
  cprMap (dE V) (dCL V V) ≫ powerRel consR ≫ est (pathR wt)

/-- `F(𝟙,∋)α` (book p.198): what `pathSplit`'s definition says in words — the bifunctor at
    `∋` in the recursion argument, followed by the constructor. -/
public theorem pathSplit_eq_Fmap_comp_alphaR :
    (pathSplit (V := V)) = (CL.F V V).map (∋ (dCL V V)) ≫ alphaR := by
  unfold pathSplit
  rw [pathF_map_id]

/-- **`F(𝟙,∋) P(α) est(R) = [wrap,step]`** (book p.198, the note's `path-defn`): the second
    transpose, computed on the same coproduct.  On the leaf summand there is no set to distribute,
    so the transpose is the singleton and `est R` gives `wrap` back; on the `A×X` summand it is
    `cpr`, and consing onto each tail and keeping a cheapest one is `step`. -/
public theorem cpMap_comp_powerRel_alphaR_comp_est_eq_junc (wt : V → V → Nat) :
    cpMap (CL.F V V) (dCL V V)
        ≫ powerRel (alphaR : (CL.F V V).obj (dCL V V) ⟶ dCL V V) ≫ est (pathR wt)
      = junc (sumCop (dL V) (⟨V × (pow (dCL V V)).carrier⟩ : RelSet.{0})) wrapR (pathStep wt) := by
  have hα : Map (alphaR : (CL.F V V).obj (dCL V V) ⟶ dCL V V) := graph_map _
  have hc : Map (consR : (⟨V × ConsList V V⟩ : RelSet.{0}) ⟶ dCL V V) := graph_map _
  have hL : cpMap (CL.F V V) (dCL V V)
      ≫ powerRel (alphaR : (CL.F V V).obj (dCL V V) ⟶ dCL V V) = Λ (pathSplit (V := V)) := by
    simp only [cpMap]
    rw [powerRel_map hα, Λ_absorption, ← pathSplit_eq_Fmap_comp_alphaR]
  have hS : pathStep wt
      = Λ (rprodMap (𝟙 (dE V)) (∋ (dCL V V)) ≫ consR) ≫ est (pathR wt) := by
    simp only [pathStep, cprMap, cpMap, Relator.prod, Relator.const, Relator.idRelator]
    rw [prodMap_eq_rprodMap, ← Cat.assoc, powerRel_map hc, Λ_absorption]
    rfl
  have hstep : ∀ (q : V × (pow (dCL V V)).carrier) (z : ConsList V V),
      pathSplit (V := V) (Sum.inr q) z
        ↔ (rprodMap (𝟙 (dE V)) (∋ (dCL V V)) ≫ consR) q z := by
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

end Freyd.Alg
