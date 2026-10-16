/-
  Bird & de Moor §9.1's `H≜⦇T⦈°⦇h⦈` at one instance: LeetCode 746, Min Cost Climbing Stairs.

  A climb is a list of moves over the cost list, with a 0-cost stair in front for the start:
  `one c` stands on a stair of cost `c` and climbs 1, `two c d` stands on `c` and climbs 2, over
  the stair of cost `d`.  `⦇T⦈ = walk` is the cost list a climb walks over, `⦇h⦈ = paid` the total
  paid on it, so `H = walk° paid` is the total paid on some climb over a cost list, and the
  problem is `H%∋ est(≤)` with `≤` the `leRel` of `AOP.A7_2_RelSet`.
-/
module

public import AOP.A9_1
public import AOP.A7_2_RelSet

namespace Freyd.Alg.RelSet.Stairs

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL

/-- `Move ::= one ℕ ∣ two ℕ ℕ`, i.e. `ℕ + ℕ×ℕ`: the stair stood on, and for a climb of 2 the stair
    stepped over. -/
public inductive Move where
  | one : Nat → Move
  | two : Nat → Nat → Move

/-- The object carrying climbs `[Move]`. -/
@[expose] public abbrev dClimb : RelSet.{0} := dCL Unit Move

/-- The object carrying cost lists `[ℕ]`. -/
@[expose] public abbrev dCost : RelSet.{0} := dCL Unit Nat

/-- `F(X) = 𝟏 + Move×X`. -/
public theorem F_obj (X : RelSet.{0}) :
    ((F Unit Move).obj X).carrier = (Unit ⊕ (Move × X.carrier)) := rfl

/-- `nil`: the empty cost list. -/
@[expose] public def nilFn (_ : Unit) : ConsList Unit Nat := ConsList.wrap ()

/-- `put`: the stairs of one move in front of the rest. -/
@[expose] public def putFn : Move × ConsList Unit Nat → ConsList Unit Nat
  | (Move.one c, xs) => ConsList.cons c xs
  | (Move.two c d, xs) => ConsList.cons c (ConsList.cons d xs)

public theorem nil_nil (u : Unit) : nilFn u = ConsList.wrap () := rfl
public theorem put_one (c : Nat) (xs : ConsList Unit Nat) :
    putFn (Move.one c, xs) = ConsList.cons c xs := rfl
public theorem put_two (c d : Nat) (xs : ConsList Unit Nat) :
    putFn (Move.two c d, xs) = ConsList.cons c (ConsList.cons d xs) := rfl

/-- The function of `T`, the junction `[nil,put]`. -/
@[expose] public def stairsFn : (Fobj Unit Move dCost).carrier → ConsList Unit Nat
  | Sum.inl u => nilFn u
  | Sum.inr p => putFn p

/-- **`T : F([ℕ])⟶[ℕ]`**: put the stairs of one move in front of the rest. -/
@[expose] public def T : (F Unit Move).obj dCost ⟶ dCost := graph stairsFn

/-- `walk : [Move]⟶[ℕ]`, the cost list a climb walks over. -/
@[expose] public def walk : ConsList Unit Move → ConsList Unit Nat
  | ConsList.wrap _ => ConsList.wrap ()
  | ConsList.cons m ms => stairsFn (Sum.inr (m, walk ms))

/-- **`walk = ⦇T⦈`**. -/
public theorem walk_cata : (graph walk : dClimb ⟶ dCost) = cataR T := by
  refine Eq.symm ?_
  apply hom_ext; intro ms
  induction ms with
  | wrap _ => exact fun p => Iff.rfl
  | cons m ms ih =>
    intro p
    constructor
    · rintro ⟨p', hp', hstep⟩
      obtain rfl : p' = walk ms := (ih p').mp hp'
      exact hstep
    · intro (hp : p = stairsFn (Sum.inr (m, walk ms)))
      exact ⟨walk ms, (ih _).mpr rfl, hp⟩

/-- `zero`: nothing paid on the empty climb. -/
@[expose] public def zeroFn (_ : Unit) : Nat := Nat.zero

/-- `pay`: the stair stood on, not the `d` stepped over, added to the rest. -/
@[expose] public def payFn : Move × Nat → Nat
  | (Move.one c, k) => c + k
  | (Move.two c _, k) => c + k

public theorem zero_zero (u : Unit) : zeroFn u = 0 := rfl
public theorem pay_one (c k : Nat) : payFn (Move.one c, k) = c + k := rfl
public theorem pay_two (c d k : Nat) : payFn (Move.two c d, k) = c + k := rfl

/-- The function of `h`, the junction `[zero,pay]`. -/
@[expose] public def costFn : (Fobj Unit Move (⟨Nat⟩ : RelSet.{0})).carrier → Nat
  | Sum.inl u => zeroFn u
  | Sum.inr p => payFn p

/-- **`h : F(ℕ)⟶ℕ`**: pay the stair stood on, not the `d` stepped over. -/
@[expose] public def h : (F Unit Move).obj (⟨Nat⟩ : RelSet.{0}) ⟶ (⟨Nat⟩ : RelSet.{0}) :=
  graph costFn

/-- `paid : [Move]⟶ℕ`, the total paid on a climb. -/
@[expose] public def paid : ConsList Unit Move → Nat
  | ConsList.wrap _ => 0
  | ConsList.cons m ms => costFn (Sum.inr (m, paid ms))

/-- **`paid = ⦇h⦈`**. -/
public theorem paid_cata : (graph paid : dClimb ⟶ (⟨Nat⟩ : RelSet.{0})) = cataR h := by
  refine Eq.symm ?_
  apply hom_ext; intro ms
  induction ms with
  | wrap _ => exact fun n => Iff.rfl
  | cons m ms ih =>
    intro n
    constructor
    · rintro ⟨k, hk, hstep⟩
      obtain rfl : k = paid ms := (ih k).mp hk
      exact hstep
    · intro (hn : n = costFn (Sum.inr (m, paid ms)))
      exact ⟨paid ms, (ih _).mpr rfl, hn⟩

/-- **`H = ⦇T⦈°⦇h⦈ = walk° paid`**: the total paid on some climb over a cost list. -/
public theorem H_eq :
    H T h = (graph walk : dClimb ⟶ dCost)° ≫ (graph paid : dClimb ⟶ (⟨Nat⟩ : RelSet.{0})) := by
  show (relCata T)° ≫ relCata h = _
  rw [← cataR_eq_relCata, ← cataR_eq_relCata, walk_cata, paid_cata]

end Freyd.Alg.RelSet.Stairs

-- printing-only: the algebras' arms under the note's names, `T ≜ [nil,put]`, `h ≜ [zero,pay]`.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Stairs.nilFn] public meta def Freyd.Alg.RelSet.Stairs.unexpandNilFn : Unexpander
  | _ => `($(mkIdent `nil))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Stairs.putFn] public meta def Freyd.Alg.RelSet.Stairs.unexpandPutFn : Unexpander
  | _ => `($(mkIdent `put))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Stairs.zeroFn] public meta def Freyd.Alg.RelSet.Stairs.unexpandZeroFn : Unexpander
  | _ => `($(mkIdent `zero))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Stairs.payFn] public meta def Freyd.Alg.RelSet.Stairs.unexpandPayFn : Unexpander
  | _ => `($(mkIdent `pay))
