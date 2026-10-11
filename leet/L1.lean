/-
  LeetCode 1 — Two Sum, composed from the array relation algebra of `AOP/A6_FinRel`:
  `twoSum(t)(xs) ≜ ix(xs) (t−) ix(xs)° ∩ (<)`, its pairs are `filter (<) (comp (map (t−) R) R°)` with
  `R ≜ ix(xs)` as arrays, `prog(t)` takes the first, and `graph(prog(t)) ⊑ twoSumO(t)` follows from the
  `rep_*` laws and `head?_toList_le`. Mathlib-free.
-/
import AOP.A6_FinRel

namespace Freyd.Alg.RelSet.LC1

open Freyd DistributiveAllegory FinRel

abbrev Key : RelSet.{0} := ⟨Int⟩
abbrev LI : RelSet.{0} := ⟨List Int⟩
abbrev Opt : RelSet.{0} := ⟨Option (Nat × Nat)⟩

/-- `∋ : ⟨Idx ⟶ Idx⟩ ⟶ Idx×Idx`, a relation as its set of pairs. -/
local notation (priority := high) "∋" => relMem Idx Idx

/-- `(t−) : a ↦ t-a`. -/
def sub (t : Int) : Key ⟶ Key := graph (t - ·)

/-- `twoSum(t)(xs) ≜ ix(xs) (t−) ix(xs)° ∩ (<)`: index pairs `j<k` with `t − xs[j] = xs[k]`. -/
def twoSum (t : Int) (xs : List Int) : Idx ⟶ Idx := (ix xs ≫ sub t ≫ (ix xs)°) ∩ (· < ·)

/-- `twoSumO(t) ≜ twoSum(t) orNone(∋)`: some pair of `twoSum(t)(xs)`, or `none` when it is empty. -/
def twoSumO (t : Int) : LI ⟶ Opt := graph (twoSum t) ≫ orNone ∋

/-- `ix(xs)` as two arrays: the pairs `(j, xs[j])`. -/
def ixRel (xs : List Int) : FinRel Nat Int := ofList (xs.zipIdx.map Prod.swap)

/-- The pairs of `twoSum`, by the array ops: `filter (<) (comp (map (t−) R) R°)`. -/
def pairs (t : Int) (xs : List Int) : FinRel Nat Nat :=
  filter (· < ·) (comp (map (t - ·) (ixRel xs)) (conv (ixRel xs)))

theorem rep_pairs (t : Int) (xs : List Int) : (pairs t xs).rep = twoSum t xs :=
  calc (pairs t xs).rep
      = (comp (map (t - ·) (ixRel xs)) (conv (ixRel xs))).rep ∩ (· < ·) := rep_filter _ _
    _ = ((map (t - ·) (ixRel xs)).rep ≫ (conv (ixRel xs)).rep) ∩ (· < ·) := by rw [rep_comp]
    _ = (((ixRel xs).rep ≫ sub t) ≫ (ixRel xs).rep°) ∩ (· < ·) := by rw [rep_map, rep_conv]; rfl
    _ = (ix xs ≫ sub t ≫ (ix xs)°) ∩ (· < ·) := by rw [ixRel, rep_ofList, rel_zipIdx, Cat.assoc]

/-- The program: the first pair. -/
def prog (t : Int) (xs : List Int) : Option (Nat × Nat) := (pairs t xs).toList.head?

/-- **The program refines the entire spec**: `graph(prog(t)) ⊑ twoSumO(t)`. -/
theorem prog_le (t : Int) : (graph (prog t) : LI ⟶ Opt) ⊑ twoSumO t :=
  calc (graph (prog t) : LI ⟶ Opt)
      ⊑ graph (fun xs => (pairs t xs).rep) ≫ orNone ∋ := head?_toList_le _
    _ = twoSumO t := congrArg (graph · ≫ orNone ∋) (funext (rep_pairs t))

#eval prog 9 [2, 7, 11, 15]   -- some (0, 1)
#eval prog 6 [3, 2, 4]        -- some (1, 2)
#eval prog 7 [1, 2, 3]        -- none



end Freyd.Alg.RelSet.LC1
