/-
  The **tupling law** for BINARY-TREE catamorphisms — the tree-shaped companion of
  `AOP.A6_8_Tupling`'s snoc-list `SL.tupling`.

  A function `h : Tree A → C₁ × C₂` obeying the FIRST-ORDER lockstep recursion
    `h nil          = g`
    `h (node l a r) = step (h l) a (h r)`
  is, by the initial-algebra universal property (uniqueness of the catamorphism), EXACTLY the
  catamorphism `⦇[g, step]⦈` of the algebra `[g, step]`.  When the carrier is a PRODUCT `C₁ × C₂`
  this is the tupling / linearization move for trees: to compute a node's answer from an AUXILIARY
  quantity over its subtrees (e.g. a height), carry a tuple and run a SINGLE bottom-up fold instead
  of recomputing the auxiliary at every node.  The pair-carrying tree fold is then not written by
  hand and verified — it is PRODUCED by this law from the base `g` and step `step`, both read off the
  problem's recurrence.  `leet/L110_derived.lean` (Balanced Binary Tree) and
  `leet/L543_derived.lean` (Diameter) derive their `(height, answer)` folds this way.

  The `nil` constructor of `Tree A` carries no data (it is the `1` summand of `F X = 1 + X×A×X`), so
  the base is a VALUE `g : C₁ × C₂` — the tree analogue of the snoc-list `wrap`'s `g : L → C₁ × C₂`.
  Reuses the whole `A6_TreeBin` engine (`cataR`, `cataTreeFold`, `cataTreeFold_nil`,
  `cataTreeFold_node`) with ZERO new engine code.  Mathlib-free.
-/
module

public import AOP.A6_TreeBin

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.TB

open Freyd

/-- Emergent product-algebra from base `g : C₁ × C₂` and step `step : C₁×C₂ → A → C₁×C₂ → C₁×C₂`.
    This is the algebra `[g, step] : F(C₁×C₂) → C₁×C₂` whose catamorphism the tupling law identifies
    with the lockstep recursion; it is the graph of the case split, hence a `Map`.  The `Sum.inl`
    (`nil`) summand carries no label, so it maps to the fixed base `g`; the `Sum.inr` (`node`) summand
    carries `(pl, a, pr)` — the two subtree results and the node label — and maps by `step`. -/
@[expose] public def treePairAlg {A C₁ C₂ : Type} (g : C₁ × C₂) (step : C₁ × C₂ → A → C₁ × C₂ → C₁ × C₂) :
    TFobj A (⟨C₁ × C₂⟩ : RelSet.{0}) ⟶ (⟨C₁ × C₂⟩ : RelSet.{0}) :=
  graph (fun u => match u with
    | Sum.inl _        => g
    | Sum.inr (pl, a, pr) => step pl a pr)

/-- The emergent algebra is a `Map` (it is a graph). -/
theorem treePairAlg_map {A C₁ C₂ : Type} (g : C₁ × C₂) (step : C₁ × C₂ → A → C₁ × C₂ → C₁ × C₂) :
    Map (treePairAlg g step) := graph_map _

/-- **The tree tupling law.**  A function `h` solving the first-order lockstep tree recursion
    `h nil = g`, `h (node l a r) = step (h l) a (h r)` IS the catamorphism of `treePairAlg g step`.
    Proof: catamorphism uniqueness — `graph h` and `cataR (treePairAlg g step)` satisfy the SAME
    structural recursion, so a single induction on `Tree A` identifies them.  The `node` case now has
    TWO recursive children, hence TWO induction hypotheses `ihl`/`ihr`, mirroring `SL.tupling`'s
    single-IH `snoc` case but pinning BOTH subtree results from the two IHs. -/
public theorem treeTupling {A C₁ C₂ : Type} (g : C₁ × C₂) (step : C₁ × C₂ → A → C₁ × C₂ → C₁ × C₂)
    (h : Tree A → C₁ × C₂)
    (hnil : h Tree.nil = g)
    (hnode : ∀ l a r, h (Tree.node l a r) = step (h l) a (h r)) :
    (graph h : dTree A ⟶ ⟨C₁ × C₂⟩) = cataR (treePairAlg g step) := by
  apply hom_ext; intro t w
  show w = h t ↔ cataTreeFold (treePairAlg g step) t w
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
        have hrleq : rl = h l := (ihl rl).mpr hrl
        have hrreq : rr = h r := (ihr rr).mpr hrr
        rw [hrleq, hrreq] at hstep
        exact hstep

/-- **First-component projection.**  Composing the tree tupling law with `graph Prod.fst` extracts
    the first slot of the emergent pair fold: the graph of `t ↦ (h t).1` is the catamorphism of
    `treePairAlg g step` followed by the first projection.  (The Diameter/Balanced derivations read
    off the SECOND slot instead, done inline there; this is the symmetric convenience lemma for the
    first, matching `SL.tupling_fst`.) -/
public theorem treeTupling_fst {A C₁ C₂ : Type} (g : C₁ × C₂) (step : C₁ × C₂ → A → C₁ × C₂ → C₁ × C₂)
    (h : Tree A → C₁ × C₂)
    (hnil : h Tree.nil = g)
    (hnode : ∀ l a r, h (Tree.node l a r) = step (h l) a (h r)) :
    (graph (fun t => (h t).1) : dTree A ⟶ ⟨C₁⟩)
      = cataR (treePairAlg g step) ≫ graph (Prod.fst : C₁ × C₂ → C₁) := by
  rw [← treeTupling g step h hnil hnode]
  apply hom_ext; intro t c
  constructor
  · intro hc; exact ⟨h t, rfl, hc⟩
  · rintro ⟨p, hp, hc⟩; rw [hp] at hc; exact hc

end Freyd.Alg.RelSet.TB
