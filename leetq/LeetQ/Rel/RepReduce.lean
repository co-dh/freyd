/-
  A fold with an associative step is a reduce (T1), and a reduce distributes over `cat` (T1'): the law that ties a
  bulk kernel with no round to the cons-list fold `⦇e, (f × 𝟙) ⊕⦈` that specifies it (doc/rel-avoid-cons.md §3).
  `length` is its instance at `f = 1`, `⊕ = +`, and runs as the count column of the slices, `rep_lengthC`.
-/
import LeetQ.Rel.Rep
import LeetQ.Rel.RepLambda
import LeetQ.Rel.KernelWF.FoldSpec
import LeetQ.Rel.KernelWF.JoinContent

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg
open scoped LeetQ.Core.Rel
open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc

section Reduce

variable {α β : Type _} (op : β → β → β) (e : β)

/-- An associative `op` moves a left operand out of a `foldl`. -/
theorem foldl_assoc (assoc : ∀ a b c, op (op a b) c = op a (op b c)) :
    ∀ (l : List β) (a b : β), l.foldl op (op a b) = op a (l.foldl op b)
  | [], _, _ => rfl
  | x :: l, a, b => by simp only [List.foldl_cons, assoc, foldl_assoc assoc l]

/-- **T1**: `⦇e, (f × 𝟙) ⊕⦈ = F(f) reduce(⊕)`, `⊕` associative with unit `e`: the cons-list fold whose step is `f`
    then `⊕` is the reduce of `⊕` over the image, which a kernel may run in any grouping. -/
theorem foldr_eq_reduce {γ : Type _} (f : γ → β) (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (ide : ∀ a, op e a = a) (eid : ∀ a, op a e = a) :
    ∀ xs : List γ, xs.foldr (fun x a => op (f x) a) e = (xs.map f).foldl op e
  | [] => rfl
  | x :: xs => by
    rw [List.foldr_cons, foldr_eq_reduce f assoc ide eid xs, List.map_cons, List.foldl_cons, ide,
      ← foldl_assoc op assoc, eid]

/-- **T1'**: `cat reduce(⊕) = (reduce(⊕) × reduce(⊕)) ⊕`, `⊕` associative with unit `e`: a reduce distributes over
    `cat`, so each part of an array reduces apart. -/
theorem reduce_append (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (eid : ∀ a, op a e = a)
    (xs ys : List β) : (xs ++ ys).foldl op e = op (xs.foldl op e) (ys.foldl op e) := by
  rw [List.foldl_append, ← foldl_assoc op assoc, eid]

end Reduce

/-- `length ≜ ⦇[zero, π₂ succ]⦈` is T1 at `f = 1`, `⊕ = +`: the reduce of the ones, which `lengthC` reads off the
    slices as `hi − lo`. -/
theorem length_eq_reduce {γ : Type _} (xs : List γ) :
    xs.length = (xs.map fun _ => (1 : Nat)).foldl (· + ·) 0 := by
  rw [← foldr_eq_reduce (· + ·) 0 (fun _ => (1 : Nat)) Nat.add_assoc Nat.zero_add Nat.add_zero]
  induction xs with
  | nil => rfl
  | cons _ xs ih => rw [List.length_cons, ih, List.foldr_cons, Nat.add_comm]

/-- `sum ≜ ⦇[zero, plus]⦈` with wrapping `+` is T1 at `f = 𝟙`: the reduce of `+` on `Int64`. -/
theorem sum_eq_reduce (xs : List Int64) : xs.foldr (· + ·) 0 = xs.foldl (· + ·) 0 := by
  have h := foldr_eq_reduce (· + ·) (0 : Int64) id Int64.add_assoc Int64.zero_add Int64.add_zero xs
  rwa [List.map_id] at h

/-- **`length` under `lengthC`'s bit**: row `i` keyed by `X`'s array `i`, valued by the count its slice reads
    (`slicesOf_row`), the length of that array; the payload's count below `2^63` keeps each count off the sign. -/
theorem rep_lengthC {E : Obj} {n : USize} (X : Vals (.arr E) n)
    (hb : (lengthC X).2 = true) :
    ∀ (xs : List E.El) (w : Int64), rep (lengthC X).1 xs w ↔ (∃ i, X.row i = xs) ∧ w = Int64.ofNat xs.length := by
  have hp : X.1.toNat < 2 ^ 63 := by simpa only [lengthC, decide_eq_true_eq] using hb
  have hs : len (slicesOf X).2 = n.toNat := (len_slices ..).2
  have hv : ∀ i : Fin n.toNat, (longsN n (slicesOf X).2 (Nat.le_of_eq hs.symm)).get i =
      Int64.ofNat (X.row i).length := fun i => by
    obtain ⟨-, hl, -⟩ := slicesOf_row X hp i.2
    have hf : fit n.toNat (slicesOf X).2 = (slicesOf X).2 := by simp only [fit, if_pos hs]
    have hlt : len (fit n.toNat (slicesOf X).2) < USize.size := by rw [hf, hs]; exact n.toNat_lt_size
    unfold longsN
    rw [longCol_cast_get hlt, hf]
    have hc : (Column.bitsAt (slicesOf X).2 (i.1 * 8) 8).toNat < 2 ^ 63 := by
      exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) (slicesOf_row X hp i.2).1) hp
    exact int64_eq_ofNat (by rw [hl]; exact hc) ((toInt64_toInt hc).trans (by rw [hl]))
  intro xs w
  rw [rep_apply]
  constructor
  · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, hv i⟩
  · rintro ⟨⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl, hv i⟩

#print axioms foldr_eq_reduce
#print axioms reduce_append
#print axioms sum_eq_reduce
#print axioms rep_lengthC

end Rep

end LeetQ.Rel
