/-
  LeetCode 1 — Two Sum, an instance of the generic join (`AOP/A6_FinRel`): `twoSum(t) ≜ join(id, t−)` is the
  index pairs `j<k` with `xs[j] = t − xs[k]`, `prog(t) ≜ joinProg(id, t−)` answers one, and
  `graph(prog(t)) ⊑ twoSumO(t)` is `joinProg_le`. Mathlib-free.
-/
import AOP.A6_FinRel

namespace Freyd.Alg.RelSet.LC1

open Freyd DistributiveAllegory

abbrev Key : RelSet.{0} := ⟨Int⟩
abbrev LI : RelSet.{0} := ⟨List Int⟩
abbrev Opt : RelSet.{0} := ⟨Option (Nat × Nat)⟩

/-- `∋ : ⟨Idx ⟶ Idx⟩ ⟶ Idx×Idx`, a relation as its set of pairs. -/
local notation (priority := high) "∋" => relMem Idx Idx

-- `Int`'s order laws again: core's `Int.instTransOrd`/`Int.instLawfulEqOrd` use `Classical.choice`.
local instance (priority := high) : Std.TransOrd Int where
  eq_swap {a b} := by
    show compareOfLessAndEq a b = (compareOfLessAndEq b a).swap
    unfold compareOfLessAndEq; repeat' split
    all_goals first | rfl | omega
  isLE_trans {a b c} := by
    show (compareOfLessAndEq a b).isLE = true → (compareOfLessAndEq b c).isLE = true → (compareOfLessAndEq a c).isLE = true
    unfold compareOfLessAndEq; repeat' split
    all_goals intro h1 h2; first | rfl | exact absurd h1 (by decide) | exact absurd h2 (by decide) | omega

local instance (priority := high) : Std.LawfulEqOrd Int where
  compare_self {a} := by
    show compareOfLessAndEq a a = .eq
    unfold compareOfLessAndEq; repeat' split
    all_goals first | rfl | omega
  eq_of_compare {a b} := by
    show compareOfLessAndEq a b = .eq → a = b
    unfold compareOfLessAndEq; repeat' split
    all_goals intro h; first | assumption | exact absurd h (by decide)

/-- `(t−) : a ↦ t-a`. -/
def sub (t : Int) : Key ⟶ Key := graph (t - ·)

/-- `(t−)° = (t−)`: subtraction from `t` is its own converse. -/
theorem sub_recip (t : Int) : (sub t)° = sub t :=
  hom_ext fun a b => ⟨fun (h : a = t - b) => show b = t - a by subst h; exact (Int.sub_sub_self t b).symm,
    fun (h : b = t - a) => show a = t - b by subst h; exact (Int.sub_sub_self t a).symm⟩

def twoSum (t : Int) : List Int → (Idx ⟶ Idx) := join id (t - ·)

theorem twoSum_eq (t : Int) (xs : List Int) : twoSum t xs = ix xs ≫ sub t ≫ (ix xs)° ∩ (· < ·) := by
  show ix xs ≫ graph (fun x : Int => x) ≫ (sub t)° ≫ (ix xs)° ∩ (· < ·) = _
  rw [graph_id, Cat.id_comp, sub_recip]

/-- `twoSumO(t) ≜ twoSum(t) orNone(∋)`: some pair of `twoSum(t)(xs)`, or `none` when it is empty. -/
def twoSumO (t : Int) : LI ⟶ Opt := graph (twoSum t) ≫ orNone ∋

def prog (t : Int) : List Int → Option (Nat × Nat) := joinProg id (t - ·)

/-- **The program refines the entire spec**: `graph(prog(t)) ⊑ twoSumO(t)`. -/
theorem prog_le (t : Int) : (graph (prog t) : LI ⟶ Opt) ⊑ twoSumO t := joinProg_le _ _

#eval prog 9 [2, 7, 11, 15]   -- some (0, 1)
#eval prog 6 [3, 2, 4]        -- some (1, 2)
#eval prog 7 [1, 2, 3]        -- none

end Freyd.Alg.RelSet.LC1
