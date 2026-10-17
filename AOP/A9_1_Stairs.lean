/-
  Bird & de Moor §9.1's `H≜⦇T⦈°⦇h⦈` at one instance: LeetCode 746, Min Cost Climbing Stairs.

  A climb is a list of segments in `N2` over the cost list, with a 0-cost stair in front for the
  start: `[c]` stands on a stair of cost `c` and climbs 1, `[c,d]` stands on `c` and climbs 2, over
  the stair of cost `d`.  `⦇T⦈ = ι′ concat` flattens a climb into the cost list it walks over,
  `⦇h⦈` is the total paid on it, so `H` is the total paid on some climb over a cost list, and the
  problem is `H%∋ est(≤)` with `≤` the `leRel` of `AOP.A7_2_RelSet`.
-/
module

public import AOP.A9_1
public import AOP.A7_2_RelSet

namespace Freyd.Alg.RelSet.Stairs

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

/-- `1or2(xs)`: the segment `xs` has length 1 or 2. -/
@[expose] public def «1or2» (xs : ConsList Unit Nat) : Prop := clen xs ∈ ([1, 2] : List Nat)

/-- `N2 ≜ {xs ∈ [ℕ] ∣ 1or2(xs)}`: a segment of the cost list of length 1 or 2, the stair stood on first. -/
-- A subtype of `[ℕ]` and not a coreflexive on `[ℕ]`: a climb is then a list in `[N2]`, and its
-- inclusion `ι` is the only glue between a climb and `concat`, so `⦇T⦈ = ι′ concat` is type functor fusion.
@[expose] public def N2 : Type := Subtype «1or2»

/-- The object carrying climbs `[N2]`. -/
@[expose] public abbrev dClimb : RelSet.{0} := dCL Unit N2

/-- The object carrying cost lists `[ℕ]`. -/
@[expose] public abbrev dCost : RelSet.{0} := dCL Unit Nat

/-- `F(X) = 𝟏 + N2×X`. -/
public theorem F_obj (X : RelSet.{0}) :
    ((F Unit N2).obj X).carrier = (Unit ⊕ (N2 × X.carrier)) := rfl

/-- `ι : N2 ↪ [ℕ]`, a segment as the stairs it covers. -/
@[expose] public def ι : dE N2 ⟶ dE (ConsList Unit Nat) := graph Subtype.val

/-- **`T : F([ℕ])⟶[ℕ]`**, `T ≜ [nil,(ι×𝟙)cat]`: put the segment in front of the rest. -/
@[expose] public def T : Alg (F Unit N2) dCost :=
  junc (sumCop (dL Unit) ⟨N2 × ConsList Unit Nat⟩) τ (rprodMap ι (𝟙 dCost) ≫ cat)

/-- **`⦇T⦈ = ι′ concat`**: a climb flattened is the concatenation of its segments. -/
public theorem T_cata : (cataR T : dClimb ⟶ dCost) = list ι ≫ concatR := by
  rw [cataR_eq_relCata, list_typeMap, concat_cata, typeMap_fusion]
  exact congrArg (relCata (I := initial Unit N2)) (Fbimap_junc (C := dCost) ι τ cat).symm

/-- `head : N2⟶ℕ`, the stair stood on — total, a segment in `N2` having length 1 or 2. -/
@[expose] public def headFn : N2 → Nat
  | ⟨ConsList.cons c _, _⟩ => c
  | ⟨ConsList.wrap (), hl⟩ => absurd hl (by unfold «1or2»; decide)

/-- `head : N2⟶ℕ` as an arrow. -/
@[expose] public def head : dE N2 ⟶ (⟨Nat⟩ : RelSet.{0}) := graph headFn

/-- `0 : 𝟏⟶ℕ`, nothing paid on the empty climb. -/
@[expose] public def zeroRel : dL Unit ⟶ (⟨Nat⟩ : RelSet.{0}) := graph fun _ => 0

/-- **`h : Alg(F,ℕ)`**, `h ≜ [0,(head×𝟙)+]`: pay the stair stood on, not the one stepped over. -/
@[expose] public def h : Alg (F Unit N2) (⟨Nat⟩ : RelSet.{0}) :=
  junc (sumCop (dL Unit) ⟨N2 × Nat⟩) zeroRel
    (rprodMap head (𝟙 (⟨Nat⟩ : RelSet.{0})) ≫ (plusRel : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ _))

/-- **(9.2) at the stairs**: `Λ(T°) P(F(M)h) est(≤) ⊑ H` with `≤` the order on `ℕ`.  Each stage of
    the left side is a subterm, so the example table after (9.2) reads every type off this one statement. -/
public theorem dynamic_programming_lower :
    Λ (T°) ≫ powerRel ((F Unit N2).map (M T h leRel) ≫ h) ≫ est leRel ⊑ H T h :=
  Freyd.Alg.dynamic_programming_lower

/-- **The tail of (9.3) at the stairs**, under (9.3)'s hypotheses on `h` and `≥`: the example table of
    the tail reads every stage's type off this statement. -/
public theorem dynamic_programming_upper_tail (hh : Map h) (hmono : Pres h leRel°)
    (htrans : leRel° ≫ leRel° ⊑ leRel°) :
    h° ≫ (F Unit N2).map ((H T h)°) ≫ (∋ ((F Unit N2).obj dCost))°
      ≫ ((∋ ((F Unit N2).obj dCost))° \ (((F Unit N2).map (M T h leRel) ≫ h) ≫ leRel°))
      ⊑ leRel° :=
  Freyd.Alg.dynamic_programming_upper_tail hh hmono htrans

end Freyd.Alg.RelSet.Stairs

-- printing-only: the constant arrow is written by its value, as `plusRel` is by its operator `+`.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Stairs.zeroRel] public meta def Freyd.Alg.RelSet.Stairs.unexpandZeroRel : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "0")))
