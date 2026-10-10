/-
  **General-carrier fold-uniqueness laws** for snoc-lists and binary trees.

  `A6_8_Tupling.tupling` and `A6_9_TreeTupling.treeTupling` state catamorphism uniqueness only for a
  PRODUCT carrier `C₁ × C₂` (the linearization / tupling use-case).  Their proofs, however, never
  touch the product structure — they are the general fact that a structural fold into ANY carrier
  `C` is the catamorphism of the corresponding algebra.  This file packages that general statement,
  which unlocks two carrier shapes the product law cannot express directly:

  * carrier `C := List D` — a **tabulating / course-of-values fold** whose step reads the whole
    table of previous results (`A6_TabDP`, used by Coin-Change / Word-Break, where `dp[i]` depends
    on ALL earlier `dp[j]`, not a fixed-width window); and
  * carrier `C := Tree B → Bool` (or `Tree B → Tree C`) — a **higher-order / lockstep fold** that
    walks a SECOND tree in step with the first (`A6_TreeZip`, used by Same-Tree / Symmetric /
    Merge-Trees, the two-input case).

  The same statement for the CONS-list initial algebra `ConsList L E` (base at the `wrap`/nil end,
  recursion on the tail) is `CL.consFold_unique` below — the reshaping law for problems whose
  natural fold consumes the input FRONT-to-back (`L1143` LCS's `col`, one row per leading char).

  The tupling laws are then the `C = C₁ × C₂` instances of these — kept as separate named laws only
  because the product-projection API (`tupling_fst`, banana-split) is convenient there.  Mathlib-free.
-/
module

public import AOP.A6_8_Tupling
public import AOP.A6_ConsList
public import AOP.A6_TreeBin

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.SL

open Freyd

/-- **General snoc-list fold-uniqueness.**  A function `h : SnocList L E → C` obeying the
    first-order recursion `h (wrap l) = g l`, `h (snoc xs e) = st (h xs) e` IS the catamorphism of
    the scalar algebra `[g, st]`, for ANY carrier `C`.  (`tupling` is the `C = C₁ × C₂` case.) -/
public theorem snocFold_unique {L E C : Type} (g : L → C) (st : C → E → C)
    (h : SnocList L E → C)
    (hwrap : ∀ l, h (SnocList.wrap l) = g l)
    (hsnoc : ∀ xs e, h (SnocList.snoc xs e) = st (h xs) e) :
    (graph h : dSL L E ⟶ ⟨C⟩) = cataR (scalarAlg g st) := by
  apply hom_ext; intro d w
  show w = h d ↔ cataFold (scalarAlg g st) d w
  induction d generalizing w with
  | wrap l =>
      rw [cataFold_wrap, hwrap l]
      exact Iff.rfl
  | snoc xs e ih =>
      rw [cataFold_snoc, hsnoc]
      constructor
      · intro hw
        exact ⟨h xs, (ih (h xs)).mp rfl, hw⟩
      · rintro ⟨r', hr', hstep⟩
        have hr'eq : r' = h xs := (ih r').mpr hr'
        rw [hr'eq] at hstep
        exact hstep

end Freyd.Alg.RelSet.SL

namespace Freyd.Alg.RelSet.TB

open Freyd

/-- A scalar tree algebra `[g, step] : F C → C` over a bare carrier `C` (`F X = 1 + X×A×X`); the
    graph of the two-way case split.  Tree analogue of `SL.scalarAlg`; `treePairAlg` is its
    `C = C₁ × C₂` instance. -/
@[expose] public def treeScalarAlg {A C : Type} (g : C) (step : C → A → C → C) :
    TFobj A (⟨C⟩ : RelSet.{0}) ⟶ (⟨C⟩ : RelSet.{0}) :=
  graph (fun u => match u with
    | Sum.inl _           => g
    | Sum.inr (pl, a, pr) => step pl a pr)

/-- The scalar tree algebra is a `Map` (it is a graph). -/
theorem treeScalarAlg_map {A C : Type} (g : C) (step : C → A → C → C) :
    Map (treeScalarAlg g step) := graph_map _

/-- **General binary-tree fold-uniqueness.**  A function `h : Tree A → C` obeying the structural
    recursion `h nil = g`, `h (node l a r) = step (h l) a (h r)` IS the catamorphism of
    `treeScalarAlg g step`, for ANY carrier `C`.  (`treeTupling` is the `C = C₁ × C₂` case; taking
    `C := Tree B → D` gives a lockstep fold over a second tree.) -/
public theorem treeFold_unique {A C : Type} (g : C) (step : C → A → C → C)
    (h : Tree A → C)
    (hnil : h Tree.nil = g)
    (hnode : ∀ l a r, h (Tree.node l a r) = step (h l) a (h r)) :
    (graph h : dTree A ⟶ ⟨C⟩) = cataR (treeScalarAlg g step) := by
  apply hom_ext; intro t w
  show w = h t ↔ cataTreeFold (treeScalarAlg g step) t w
  induction t generalizing w with
  | nil =>
      rw [cataTreeFold_nil, hnil]
      exact Iff.rfl
  | node l a r ihl ihr =>
      rw [cataTreeFold_node, hnode]
      constructor
      · intro hw
        exact ⟨h l, h r, (ihl (h l)).mp rfl, (ihr (h r)).mp rfl, hw⟩
      · rintro ⟨rl, rr, hrl, hrr, hstep⟩
        have hlq : rl = h l := (ihl rl).mpr hrl
        have hrq : rr = h r := (ihr rr).mpr hrr
        rw [hlq, hrq] at hstep
        exact hstep

end Freyd.Alg.RelSet.TB

namespace Freyd.Alg.RelSet.CL

open Freyd

/-- The case split itself, as a function of its own.  A `match` written INSIDE the algebra's body
    makes the matcher one of the algebra's own constants, and a name whose body is made of one is
    never opened by the picture, so the algebra printed as its Lean name instead of the junction. -/
@[expose] public def consScalarFn {L E C : Type} (g : L → C) (st : E → C → C) :
    (Fobj L E (⟨C⟩ : RelSet.{0})).carrier → C
  | Sum.inl d      => g d
  | Sum.inr (e, c) => st e c

/-- A scalar cons-list algebra `[g, st] : F C → C` over a bare carrier `C` (`F X = L + E×X`); the
    graph of the case split.  Cons-list analogue of `SL.scalarAlg`; note the step `st : E → C → C`
    takes the head element FIRST, then the folded tail (the `ConsList.cons e xs` order). -/
@[expose] public def consScalarAlg {L E C : Type} (g : L → C) (st : E → C → C) :
    Fobj L E (⟨C⟩ : RelSet.{0}) ⟶ (⟨C⟩ : RelSet.{0}) :=
  graph (consScalarFn g st)

/-- The scalar cons-list algebra is a `Map` (it is a graph). -/
theorem consScalarAlg_map {L E C : Type} (g : L → C) (st : E → C → C) :
    Map (consScalarAlg g st) := graph_map _

/-- **General cons-list fold-uniqueness.**  A function `h : ConsList L E → C` obeying the
    recursion `h (wrap d) = g d`, `h (cons e xs) = st e (h xs)` IS the catamorphism of
    `consScalarAlg g st`, for ANY carrier `C`.  The reshaping law: a front-to-back single-list DP
    (carrier `C := List D` a growing row, e.g. `L1143`'s `col`) is emitted by this law. -/
public theorem consFold_unique {L E C : Type} (g : L → C) (st : E → C → C)
    (h : ConsList L E → C)
    (hwrap : ∀ d, h (ConsList.wrap d) = g d)
    (hcons : ∀ e xs, h (ConsList.cons e xs) = st e (h xs)) :
    (graph h : dCL L E ⟶ ⟨C⟩) = cataR (consScalarAlg g st) := by
  apply hom_ext; intro d w
  show w = h d ↔ cataFold (consScalarAlg g st) d w
  induction d generalizing w with
  | wrap l =>
      rw [cataFold_wrap, hwrap l]
      exact Iff.rfl
  | cons e xs ih =>
      rw [cataFold_cons, hcons]
      constructor
      · intro hw
        exact ⟨h xs, (ih (h xs)).mp rfl, hw⟩
      · rintro ⟨r', hr', hstep⟩
        have hr'eq : r' = h xs := (ih r').mpr hr'
        rw [hr'eq] at hstep
        exact hstep

/-- `cfold g st` is the fold `⦇[g,st]⦈`. -/
public theorem cfold_cata {L E C : Type} (g : L → C) (st : E → C → C) :
    (graph (cfold g st) : dCL L E ⟶ ⟨C⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st _ (fun _ => rfl) (fun _ _ => rfl)

/-- `List.foldr st (g ())` is the fold `⦇[g,st]⦈` over core lists (`listInitial`). -/
public theorem foldr_cata {E C : Type} (g : Unit → C) (st : E → C → C) :
    (graph (List.foldr st (g ())) : (listInitial E).t ⟶ ⟨C⟩)
      = relCata (I := listInitial E) (consScalarAlg g st) :=
  (relCata_UP (listInitial E) _ _).mp <| by
    show graph listCon ≫ graph (List.foldr st (g ())) = _
    rw [graph_comp_left]
    refine hom_ext fun u r => ?_
    rcases u with ⟨⟨⟩⟩ | ⟨x, xs⟩
    · exact ⟨fun h => ⟨Sum.inl (), rfl, h⟩, fun ⟨v, hv, h⟩ => by
        cases v with
        | inl _ => exact h
        | inr _ => exact hv.elim⟩
    · exact ⟨fun h => ⟨Sum.inr (x, List.foldr st (g ()) xs), ⟨rfl, rfl⟩, h⟩, fun ⟨v, hv, h⟩ => by
        cases v with
        | inl _ => exact hv.elim
        | inr q =>
          obtain ⟨y, c⟩ := q
          obtain ⟨hy, hc⟩ := (hv : x = y ∧ _)
          subst hy; subst hc; exact h⟩

/-- `α = [nil, cons]`: core list's constructor map is the junction of its two constructors. -/
public theorem listCon_eq_junc {E : Type} :
    (graph listCon : Fobj Unit E ⟨List E⟩ ⟶ ⟨List E⟩)
      = junc (sumCop (dL Unit) ⟨E × List E⟩) (graph fun _ => []) (graph fun p => p.1 :: p.2) :=
  junc_unique _ (graph_comp _ _) (graph_comp _ _)

/-- `[g, st]` as the junction of its two arms. -/
public theorem consScalarAlg_eq_junc {L E C : Type} (g : L → C) (st : E → C → C) :
    consScalarAlg g st
      = junc (sumCop (dL L) ⟨E × C⟩) (graph g) (graph fun p : E × C => st p.1 p.2) :=
  junc_unique _ (graph_comp _ _) (graph_comp _ _)

/-- **`foldr(st, e) ⊑ X`, by (6.2) `⦇R⦈ ⊑ X ⟸ α° F(X) R ⊑ X`** with `foldr(st,e) = ⦇[e, st]⦈`
    (`foldr_cata`); the premise is the copair of its `[]` and `::` arms. -/
public theorem foldr_le {E C : Type} {X : (⟨List E⟩ : RelSet.{0}) ⟶ ⟨C⟩} (e : C) (st : E → C → C)
    (hnil : (graph fun _ => e : dL Unit ⟶ ⟨C⟩) ⊑ (graph fun _ => ([] : List E) : dL Unit ⟶ ⟨List E⟩) ≫ X)
    (hcons : rprodMap (𝟙 (dE E)) X ≫ graph (fun p : E × C => st p.1 p.2)
      ⊑ graph (fun p : E × List E => p.1 :: p.2) ≫ X) :
    (graph (List.foldr st e) : (⟨List E⟩ : RelSet.{0}) ⟶ ⟨C⟩) ⊑ X := by
  rw [show (graph (List.foldr st e) : (⟨List E⟩ : RelSet.{0}) ⟶ ⟨C⟩) = _ from foldr_cata (fun _ => e) st]
  refine relCata_le_of_prefixed (listInitial E) ?_
  calc (graph listCon)° ≫ (F Unit E).map X ≫ consScalarAlg (fun _ => e) st
      = (graph listCon)° ≫ junc (sumCop (dL Unit) _) (graph fun _ => e)
          (rprodMap (𝟙 (dE E)) X ≫ graph fun p => st p.1 p.2) := by rw [consScalarAlg_eq_junc, Fmap_comp_junc]
    _ ⊑ (graph listCon)° ≫ junc (sumCop (dL Unit) _) (graph (fun _ => []) ≫ X)
          (graph (fun p : E × List E => p.1 :: p.2) ≫ X) := comp_mono_left _ (junc_mono _ hnil hcons)
    _ = ((graph listCon)° ≫ graph listCon) ≫ X := by rw [← junc_comp, ← listCon_eq_junc, Cat.assoc]
    _ = X := (congrArg (· ≫ X) (listInitial E).recip_alpha_alpha).trans (Cat.id_comp _)

end Freyd.Alg.RelSet.CL
