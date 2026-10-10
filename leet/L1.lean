/-
  LeetCode 1 — Two Sum.

  1. **Spec** — `twoSum(t) ≜ zipIdx ⟨∋,∋⟩ (j<k ∧ a+b=t)? (π₂×π₂) : [Int] ⟶ Nat × Nat`: index the
     list, take two members `((a,j),(b,k))`, keep those with `j<k` and `a+b=t`, return `(j,k)`.
     `twoSum_iff` reads it pointwise as `TwoSum`.
  2. **Program** — `prog(t)`: one scan over `zipIdx(xs)` with a `Std.HashMap Int Nat` from each value
     seen so far to an index of it; at `(x,k)` look up `t-x`, return `(j,k)` on a hit `j`, else
     insert `x ↦ k`.  O(n) lookups and inserts.
  3. **Correctness** — `prog_sound`: an answer `some (j,k)` is related to `xs` by `twoSum(t)` (the
     program refines the relation); `prog_complete`: `none` only off the domain of `twoSum(t)`.
     Both by the scan invariant `Inv`: the map holds, for each value among the elements already
     scanned, an index where it occurs among them.

  Mathlib-free.  Axioms: `twoSum_iff` ⊆ {propext, Quot.sound}; `prog_sound`/`prog_complete` add
  `Classical.choice`, inherited from core's `Std.HashMap.getElem?_insert`/`getElem?_empty`.
-/
import AOP.A6_1_RelSet
import Std.Data.HashMap

namespace Freyd.Alg.RelSet.LC1

open Freyd

/-! ## The specification -/

/-- `TwoSum xs t i j` — `i` and `j` are distinct positions (`i < j`) of `xs` whose values sum to
    `t`.  `i < xs.length` follows from `xs[i]? = some vi`. -/
def TwoSum (xs : List Int) (t : Int) (i j : Nat) : Prop :=
  i < j ∧ ∃ vi vj, xs[i]? = some vi ∧ xs[j]? = some vj ∧ vi + vj = t

/-- Membership `∋ : [A] ⟶ A` on core lists.  `ListRel.inlist` is the same relation on `ConsList`;
    `zipIdx` is core's, so its membership is core's `∈` too. -/
def ni {A : Type} : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨A⟩ := fun xs x => x ∈ xs

/-- `twoSum(t) ≜ zipIdx ⟨∋,∋⟩ (j<k ∧ a+b=t)? (π₂×π₂)`: index the list, take two members
    `((a,j),(b,k))` independently, keep those with `j<k` and `a+b=t`, return the two indices. -/
def twoSum (t : Int) : (⟨List Int⟩ : RelSet.{0}) ⟶ ⟨Nat × Nat⟩ :=
  (graph List.zipIdx : (⟨List Int⟩ : RelSet.{0}) ⟶ ⟨List (Int × Nat)⟩) ≫ rpair ni ni ≫
    corefl (fun c : (Int × Nat) × (Int × Nat) => c.1.2 < c.2.2 ∧ c.1.1 + c.2.1 = t) ≫
    rprodMap (graph Prod.snd : (⟨Int × Nat⟩ : RelSet.{0}) ⟶ ⟨Nat⟩) (graph Prod.snd)

/-- The point-free `twoSum(t)` relates `xs` to exactly the pairs `TwoSum` accepts. -/
theorem twoSum_iff (xs : List Int) (t : Int) (i j : Nat) : twoSum t xs (i, j) ↔ TwoSum xs t i j := by
  simp only [twoSum, comp_apply, graph, rpair, ni, corefl, rprodMap, TwoSum]
  constructor
  · rintro ⟨_, rfl, ⟨⟨a, j'⟩, ⟨b, k'⟩⟩, ⟨ha, hb⟩, _, ⟨rfl, hlt, hs⟩, rfl, rfl⟩
    exact ⟨hlt, a, b, List.mem_zipIdx_iff_getElem?.mp ha, List.mem_zipIdx_iff_getElem?.mp hb, hs⟩
  · rintro ⟨hlt, a, b, ha, hb, hs⟩
    exact ⟨_, rfl, ((a, i), (b, j)), ⟨List.mem_zipIdx_iff_getElem?.mpr ha,
      List.mem_zipIdx_iff_getElem?.mpr hb⟩, _, ⟨rfl, hlt, hs⟩, rfl, rfl⟩

/-! ## The program: one hash-map scan over `zipIdx(xs)` -/

/-- The scan from map `m` over the remaining indexed elements: at `(x,k)` a hit `m[t-x]? = some j`
    answers `(j,k)`, a miss records `x ↦ k` and moves on. -/
def go (t : Int) (m : Std.HashMap Int Nat) : List (Int × Nat) → Option (Nat × Nat)
  | [] => none
  | (x, k) :: ps => match m[t - x]? with
    | some j => some (j, k)
    | none => go t (m.insert x k) ps

/-- `prog(t)(xs)`: the scan over `zipIdx(xs)` from the empty map. -/
def prog (t : Int) (xs : List Int) : Option (Nat × Nat) := go t {} xs.zipIdx

/-! ## Correctness through the scan invariant -/

/-- Scan invariant over the scanned prefix `pre`: every entry `v ↦ j` of `m` is an element `(v,j)`
    of `pre`, and every value of `pre` has an entry. -/
def Inv (m : Std.HashMap Int Nat) (pre : List (Int × Nat)) : Prop :=
  ∀ v, (∀ j, m[v]? = some j → (v, j) ∈ pre) ∧ (∀ j, (v, j) ∈ pre → ∃ j', m[v]? = some j')

theorem inv_empty : Inv {} [] := fun v => ⟨by simp, by simp⟩

/-- Recording `x ↦ k` extends the invariant by the scanned element `(x,k)`. -/
theorem inv_insert {m : Std.HashMap Int Nat} {pre : List (Int × Nat)} (x : Int) (k : Nat)
    (h : Inv m pre) : Inv (m.insert x k) (pre ++ [(x, k)]) := fun v => by
  rw [Std.HashMap.getElem?_insert]
  by_cases hv : x = v
  · subst hv; simp
  · simp only [beq_iff_eq, hv, if_false, List.mem_append, List.mem_singleton, Prod.mk.injEq,
      Ne.symm hv, false_and, or_false]
    exact h v

/-- Indices along `zipIdx` strictly increase. -/
theorem zipIdx_sorted (xs : List Int) (n : Nat) : (xs.zipIdx n).Pairwise (fun a b => a.2 < b.2) := by
  induction xs generalizing n with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    refine List.pairwise_cons.mpr ⟨fun ⟨b, i⟩ hb => ?_, ih (n + 1)⟩
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (List.mem_zipIdx hb).1

/-- Soundness of the scan: a hit pairs an element of the scanned prefix with a later element. -/
theorem go_sound (t : Int) (L : List (Int × Nat)) (hL : L.Pairwise (fun a b => a.2 < b.2)) :
    ∀ (ps pre : List (Int × Nat)) (m : Std.HashMap Int Nat), pre ++ ps = L → Inv m pre →
      ∀ j k, go t m ps = some (j, k) → ∃ a b, (a, j) ∈ L ∧ (b, k) ∈ L ∧ j < k ∧ a + b = t
  | [], _, _, _, _, _, _, h => nomatch h
  | (x, k') :: ps, pre, m, hpre, hm, j, k, h => by
    have hsort := (List.pairwise_append.mp (hpre ▸ hL)).2.2
    unfold go at h
    split at h
    · rename_i j' hj
      cases h
      refine ⟨t - x, x, ?_, ?_, hsort _ ((hm _).1 _ hj) _ (List.mem_cons_self ..), by omega⟩
      · exact hpre ▸ List.mem_append_left _ ((hm _).1 _ hj)
      · exact hpre ▸ List.mem_append_right _ (List.mem_cons_self ..)
    · exact go_sound t L hL ps (pre ++ [(x, k')]) _ (by simpa using hpre) (inv_insert x k' hm) j k h

/-- Completeness of the scan: a miss over the rest leaves no pair in `L` when the prefix has none. -/
theorem go_complete (t : Int) (L : List (Int × Nat)) (hL : L.Pairwise (fun a b => a.2 < b.2)) :
    ∀ (ps pre : List (Int × Nat)) (m : Std.HashMap Int Nat), pre ++ ps = L → Inv m pre →
      (∀ a b j k, (a, j) ∈ pre → (b, k) ∈ pre → j < k → a + b ≠ t) → go t m ps = none →
      ∀ a b j k, (a, j) ∈ L → (b, k) ∈ L → j < k → a + b ≠ t
  | [], pre, _, hpre, _, hno, _ => by simpa [← hpre] using hno
  | (x, k') :: ps, pre, m, hpre, hm, hno, h => by
    have hsort := (List.pairwise_append.mp (hpre ▸ hL)).2.2
    unfold go at h
    split at h
    · cases h
    · rename_i hx
      refine go_complete t L hL ps (pre ++ [(x, k')]) _ (by simpa using hpre) (inv_insert x k' hm)
        ?_ h
      intro a b j k ha hb hjk hs
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at ha hb
      rcases hb with hb | ⟨rfl, rfl⟩
      · rcases ha with ha | ⟨rfl, rfl⟩
        · exact hno a b j k ha hb hjk hs
        · exact Nat.lt_asymm hjk (hsort _ hb _ (List.mem_cons_self ..))
      · rcases ha with ha | ⟨rfl, rfl⟩
        · obtain ⟨j', hj'⟩ := (hm a).2 j ha
          rw [show t - b = a by omega, hj'] at hx
          cases hx
        · exact Nat.lt_irrefl _ hjk

/-- **Soundness**: an answer of the program is related to `xs` by `twoSum(t)`. -/
theorem prog_sound (t : Int) (xs : List Int) (p : Nat × Nat) (h : prog t xs = some p) :
    twoSum t xs p := by
  obtain ⟨j, k⟩ := p
  obtain ⟨a, b, ha, hb, hjk, hs⟩ :=
    go_sound t _ (zipIdx_sorted xs 0) xs.zipIdx [] {} rfl inv_empty j k h
  exact (twoSum_iff xs t j k).mpr
    ⟨hjk, a, b, List.mem_zipIdx_iff_getElem?.mp ha, List.mem_zipIdx_iff_getElem?.mp hb, hs⟩

/-- **Completeness**: the program answers `none` only off the domain of `twoSum(t)`. -/
theorem prog_complete (t : Int) (xs : List Int) (h : prog t xs = none) : ∀ p, ¬ twoSum t xs p := by
  rintro ⟨j, k⟩ hp
  obtain ⟨hjk, a, b, ha, hb, hs⟩ := (twoSum_iff xs t j k).mp hp
  exact go_complete t _ (zipIdx_sorted xs 0) xs.zipIdx [] {} rfl inv_empty (by simp) h a b j k
    (List.mem_zipIdx_iff_getElem?.mpr ha) (List.mem_zipIdx_iff_getElem?.mpr hb) hjk hs

#eval prog 9 [2, 7, 11, 15]   -- some (0, 1)
#eval prog 6 [3, 2, 4]        -- some (1, 2)
#eval prog 7 [1, 2, 3]        -- none

end Freyd.Alg.RelSet.LC1
