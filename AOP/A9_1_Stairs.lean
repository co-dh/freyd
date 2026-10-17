/-
  Bird & de Moor §9.1's `H≜⦇T⦈°⦇h⦈` at one instance: LeetCode 746, Min Cost Climbing Stairs.

  A climb is a list of moves over the cost list, with a 0-cost stair in front for the start, and a
  move is a segment of the cost list: `[c]` stands on a stair of cost `c` and climbs 1, `[c,d]`
  stands on `c` and climbs 2, over the stair of cost `d`.  `⦇T⦈ = ι′ concat` flattens a climb into
  the cost list it walks over, `⦇h⦈ = paid` is the total paid on it, so `H = (ι′ concat)° paid` is
  the total paid on some climb over a cost list, and the problem is `H%∋ est(≤)` with `≤` the
  `leRel` of `AOP.A7_2_RelSet`.
-/
module

public import AOP.A9_1
public import AOP.A7_2_RelSet

namespace Freyd.Alg.RelSet.Stairs

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

/-- `oneOrTwo(xs)`: the segment `xs` has length 1 or 2. -/
@[expose] public def oneOrTwo (xs : ConsList Unit Nat) : Prop := clen xs = 1 ∨ clen xs = 2

/-- `Move ≜ {[c], [c,d]}`: a segment of the cost list of length 1 or 2, the stair stood on first. -/
-- A subtype of `[ℕ]` and not `ℕ + ℕ×ℕ`: its inclusion `ι` is then the only glue between a climb and
-- `concat`, so `⦇T⦈ = ι′ concat` is type functor fusion and nothing else.
@[expose] public def Move : Type := Subtype oneOrTwo

/-- The object carrying climbs `[Move]`. -/
@[expose] public abbrev dClimb : RelSet.{0} := dCL Unit Move

/-- The object carrying cost lists `[ℕ]`. -/
@[expose] public abbrev dCost : RelSet.{0} := dCL Unit Nat

/-- `F(X) = 𝟏 + Move×X`. -/
public theorem F_obj (X : RelSet.{0}) :
    ((F Unit Move).obj X).carrier = (Unit ⊕ (Move × X.carrier)) := rfl

/-- `ι : Move ↪ [ℕ]`, a move as the segment of stairs it covers. -/
@[expose] public def ι : dE Move ⟶ dE (ConsList Unit Nat) := graph Subtype.val

/-- **`T : F([ℕ])⟶[ℕ]`**, `T ≜ [nil,(ι×𝟙)cat]`: put the segment in front of the rest. -/
@[expose] public def T : (F Unit Move).obj dCost ⟶ dCost :=
  junc (sumCop (dL Unit) ⟨Move × ConsList Unit Nat⟩) τ (rprodMap ι (𝟙 dCost) ≫ cat)

/-- **`⦇T⦈ = ι′ concat`**: a climb flattened is the concatenation of its segments. -/
public theorem T_cata : (cataR T : dClimb ⟶ dCost) = list ι ≫ concatR := by
  rw [cataR_eq_relCata, list_typeMap, concat_cata, typeMap_fusion]
  exact congrArg (relCata (I := initial Unit Move)) (Fbimap_junc (C := dCost) ι τ cat).symm

/-- `head : Move⟶ℕ`, the stair stood on — total, a segment having length 1 or 2. -/
@[expose] public def headFn : Move → Nat
  | ⟨ConsList.cons c _, _⟩ => c
  | ⟨ConsList.wrap _, hl⟩ => absurd hl fun (h : _ ∨ _) => h.elim Nat.noConfusion Nat.noConfusion

/-- `head : Move⟶ℕ` as an arrow. -/
@[expose] public def head : dE Move ⟶ (⟨Nat⟩ : RelSet.{0}) := graph headFn

/-- `0 : 𝟏⟶ℕ`, nothing paid on the empty climb. -/
@[expose] public def zeroRel : dL Unit ⟶ (⟨Nat⟩ : RelSet.{0}) := graph fun _ => 0

/-- **`h : F(ℕ)⟶ℕ`**, `h ≜ [0,(head×𝟙)+]`: pay the stair stood on, not the one stepped over. -/
@[expose] public def h : (F Unit Move).obj (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Nat⟩ : RelSet.{0}) :=
  junc (sumCop (dL Unit) ⟨Move × Nat⟩) zeroRel
    (rprodMap head (𝟙 (⟨Nat⟩ : RelSet.{0})) ≫ (plusRel : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ _))

/-- `paid : [Move]⟶ℕ`, the total paid on a climb. -/
@[expose] public def paid : ConsList Unit Move → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons m ms => headFn m + paid ms

/-- **`paid = ⦇h⦈`**. -/
public theorem paid_cata : (graph paid : dClimb ⟶ (⟨Nat⟩ : RelSet.{0})) = cataR h := by
  rw [cataR_eq_relCata]
  refine (relCata_UP (initial Unit Move) _ _).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun D r => Iff.rfl, fun m ms r => ?_⟩)
  constructor
  · intro hr; exact ⟨paid ms, rfl, (headFn m, paid ms), ⟨rfl, rfl⟩, hr.symm⟩
  · rintro ⟨y, rfl, ⟨q1, q2⟩, ⟨rfl, rfl⟩, rfl⟩; rfl

/-- **`H = ⦇T⦈°⦇h⦈ = (ι′ concat)° paid`**: the total paid on some climb over a cost list. -/
public theorem H_eq :
    H T h = (list ι ≫ concatR : dClimb ⟶ dCost)° ≫ (graph paid : dClimb ⟶ (⟨Nat⟩ : RelSet.{0})) := by
  show (relCata T)° ≫ relCata h = _
  rw [← cataR_eq_relCata, ← cataR_eq_relCata, T_cata, paid_cata]

end Freyd.Alg.RelSet.Stairs

-- printing-only: the constant arrow is written by its value, as `plusRel` is by its operator `+`.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Stairs.zeroRel] public meta def Freyd.Alg.RelSet.Stairs.unexpandZeroRel : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "0")))
