/-
  Bird & de Moor §9.1's `H≜⦇T⦈°⦇h⦈` at one instance: LeetCode 746, Min Cost Climbing Stairs.

  A climb is a list of segments of the cost list, with a 0-cost stair in front for the start: `[c]`
  stands on a stair of cost `c` and climbs 1, `[c,d]` stands on `c` and climbs 2, over the stair of
  cost `d`.  `⦇T⦈ = 1or2′ concat` keeps the climbs whose segments have length 1 or 2 and flattens
  one into the cost list it walks over, `⦇h⦈ = paid` is the total paid on it, so
  `H = (1or2′ concat)° paid` is the total paid on some climb over a cost list, and the problem is
  `H%∋ est(≤)` with `≤` the `leRel` of `AOP.A7_2_RelSet`.
-/
module

public import AOP.A9_1
public import AOP.A7_2_RelSet

namespace Freyd.Alg.RelSet.Stairs

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

/-- `1or2(xs)`: the segment `xs` has length 1 or 2. -/
@[expose] public def «1or2» (xs : ConsList Unit Nat) : Prop := clen xs ∈ ([1, 2] : List Nat)

/-- The object carrying climbs `[[ℕ]]`. -/
@[expose] public abbrev dClimb : RelSet.{0} := dCL Unit (ConsList Unit Nat)

/-- The object carrying cost lists `[ℕ]`. -/
@[expose] public abbrev dCost : RelSet.{0} := dCL Unit Nat

/-- `F(X) = 𝟏 + [ℕ]×X`. -/
public theorem F_obj (X : RelSet.{0}) :
    ((F Unit (ConsList Unit Nat)).obj X).carrier = (Unit ⊕ (ConsList Unit Nat × X.carrier)) := rfl

/-- **`T : F([ℕ])⟶[ℕ]`**, `T ≜ [nil,(1or2×𝟙)cat]`: a segment of length 1–2 in front of the rest. -/
-- The coreflexive `1or2` and not a subtype of `[ℕ]`: `⦇T⦈ = 1or2′ concat` is then type
-- functor fusion and nothing else, with no inclusion between a climb and `concat`.
@[expose] public def T : (F Unit (ConsList Unit Nat)).obj dCost ⟶ dCost :=
  junc (sumCop (dL Unit) ⟨ConsList Unit Nat × ConsList Unit Nat⟩) τ
    (rprodMap (corefl «1or2» : dE (ConsList Unit Nat) ⟶ _) (𝟙 dCost) ≫ cat)

/-- **`⦇T⦈ = 1or2′ concat`**: a climb of segments of length 1–2, flattened. -/
public theorem T_cata :
    (cataR T : dClimb ⟶ dCost) = list (corefl «1or2» : dE (ConsList Unit Nat) ⟶ _) ≫ concatR := by
  rw [cataR_eq_relCata, list_typeMap, concat_cata, typeMap_fusion]
  exact congrArg (relCata (I := initial Unit (ConsList Unit Nat)))
    (Fbimap_junc (C := dCost) (corefl «1or2» : dE (ConsList Unit Nat) ⟶ _) τ cat).symm

/-- `head : [ℕ]⟶ℕ`, the stair stood on; `h` applies it only after `1or2`, so `[]` never reaches it. -/
@[expose] public def headFn : ConsList Unit Nat → Nat
  | ConsList.cons c _ => c
  | ConsList.wrap _ => 0

/-- `head : [ℕ]⟶ℕ` as an arrow. -/
@[expose] public def head : dE (ConsList Unit Nat) ⟶ (⟨Nat⟩ : RelSet.{0}) := graph headFn

/-- `0 : 𝟏⟶ℕ`, nothing paid on the empty climb. -/
@[expose] public def zeroRel : dL Unit ⟶ (⟨Nat⟩ : RelSet.{0}) := graph fun _ => 0

/-- **`h : F(ℕ)⟶ℕ`**, `h ≜ [0,(head×𝟙)+]`: pay the stair stood on, not the one stepped over. -/
@[expose] public def h : (F Unit (ConsList Unit Nat)).obj (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Nat⟩ : RelSet.{0}) :=
  junc (sumCop (dL Unit) ⟨ConsList Unit Nat × Nat⟩) zeroRel
    (rprodMap head (𝟙 (⟨Nat⟩ : RelSet.{0})) ≫ (plusRel : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ _))

end Freyd.Alg.RelSet.Stairs

-- printing-only: the constant arrow is written by its value, as `plusRel` is by its operator `+`.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Stairs.zeroRel] public meta def Freyd.Alg.RelSet.Stairs.unexpandZeroRel : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "0")))
