/-
  LeetCode 283 — Move Zeroes — as an ALLEGORY PROGRAM.

  Problem: move all `0`s in `nums : List Int` to the end while keeping the relative order of the
  non-zero elements (a STABLE partition).

  Same recipe as `leet/L238.lean` (`Freyd/leetcode.md` S0/S23): plain `List Int`, no `SnocList`
  engine needed — the program is a one-shot filter+append, not a scan/fold.

  1. **Data** — a plain `List Int`; the answer object is the SAME type.

  2. **Program** — `moveZeroesFn xs := xs.filter nzPred ++ List.replicate (xs.filter zPred).length 0`
     — the non-zero elements in order, then that many `0`s appended.

  3. **Specification — full honesty, four clauses**:
     * non-zeros preserved in order: `(moveZeroesFn xs).filter nzPred = xs.filter nzPred`.
     * same length: `(moveZeroesFn xs).length = xs.length`.
     * multiset preserved: `∀ v, countL (moveZeroesFn xs) v = countL xs v` (nothing lost/invented —
       pins that the appended zeros exactly replace the removed ones; reuses `LC242.countL`).
     * all zeros trailing, via the DEFINITIONAL split `moveZeroesFn xs = xs.filter nzPred ++
       List.replicate k 0` (the program's own shape, witness `k := (xs.filter zPred).length`)
       together with "the first part has no zeros" (`filter_nz_no_zero`) — the cleaner of the two
       forms `leetcode.md` allows, since the index-chasing form is a re-derivation of exactly this.

  4. **Correctness** — the crux fact underlying all four clauses: `xs.filter zPred = List.replicate
     (xs.filter zPred).length 0` (every element `zPred` keeps IS `0`, via core `List.eq_replicate_iff`).
     This turns `moveZeroesFn xs` into `xs.filter nzPred ++ xs.filter zPred`
     (`moveZeroesFn_eq_partition`) — a genuine STABLE PARTITION of `xs` by `nzPred`, whose
     order/length/multiset preservation reduces to one small reusable partition law per invariant
     (`filter_not_filter_eq_nil`, `length_filter_add_filter_not`, `countL_filter_add_filter_not`),
     each a short structural induction, plus core `List.filter_append`/`filter_filter`/
     `length_append`. Headline `move_correct` bundles all four. Package `solve := graph moveZeroesFn`
     (a `Map`) for the `Rel(Set)` framing.

  Mathlib-free. Axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet
import leet.L242

namespace Freyd.Alg.RelSet.LC283

open Freyd

/-! ## Data & answer object: a plain `List Int` -/

abbrev Nums : RelSet.{0} := ⟨List Int⟩

/-! ## The two complementary predicates driving the partition -/

/-- Is `a` non-zero? -/
def nzPred (a : Int) : Bool := decide (a ≠ 0)
/-- Is `a` zero? -/
def zPred (a : Int) : Bool := decide (a = 0)

/-- `nzPred`/`zPred` are complementary at every `a`. -/
theorem nzPred_eq_not_zPred (a : Int) : nzPred a = !zPred a := by
  unfold nzPred zPred; by_cases h : a = 0 <;> simp [h]

/-! ## The program: stable partition — non-zeros in order, then that many zeros -/

/-- **The program**: filter out the non-zeros (order preserved), then append that many `0`s. -/
def moveZeroesFn (xs : List Int) : List Int :=
  xs.filter nzPred ++ List.replicate (xs.filter zPred).length 0

/-- **The allegory program**: LeetCode 283's solution as a morphism `Nums ⟶ Nums` in `Rel(Set)`. -/
def solve : Nums ⟶ Nums := graph moveZeroesFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map moveZeroesFn

/-! ## The crux: `xs.filter zPred` IS `List.replicate (its length) 0` -/

/-- Every element `zPred` keeps out of `xs` IS `0` — so the zero-filter is literally a replicate. -/
theorem filter_zPred_eq_replicate (xs : List Int) :
    xs.filter zPred = List.replicate (xs.filter zPred).length 0 :=
  List.eq_replicate_iff.mpr ⟨rfl, fun b hb => by
    have h : zPred b = true := (List.mem_filter.mp hb).2
    unfold zPred at h; exact of_decide_eq_true h⟩

/-- `moveZeroesFn` is literally the stable partition of `xs` by `nzPred`. -/
theorem moveZeroesFn_eq_partition (xs : List Int) :
    moveZeroesFn xs = xs.filter nzPred ++ xs.filter zPred := by
  show xs.filter nzPred ++ List.replicate (xs.filter zPred).length 0 = xs.filter nzPred ++ xs.filter zPred
  rw [← filter_zPred_eq_replicate]

/-- The first part of the partition has no zeros (needed for "all zeros trailing"). -/
theorem filter_nz_no_zero (xs : List Int) : ∀ a ∈ xs.filter nzPred, a ≠ 0 := by
  intro a ha
  have h : nzPred a = true := (List.mem_filter.mp ha).2
  unfold nzPred at h; exact of_decide_eq_true h

/-- `xs.filter (fun a => !nzPred a)` IS `xs.filter zPred` (the two ways to name "the complement of
    `nzPred`" agree). -/
theorem filter_not_nzPred_eq_zPred (xs : List Int) :
    xs.filter (fun a => !nzPred a) = xs.filter zPred := by
  congr 1; funext a; rw [nzPred_eq_not_zPred, Bool.not_not]

/-! ## Reusable partition laws: a predicate split by its own negation recovers the whole list -/

/-- Filtering the "fails `p`" half of a list BY `p` gives nothing — `p` and `¬p` are disjoint. -/
theorem filter_not_filter_eq_nil (p : Int → Bool) (xs : List Int) :
    (xs.filter (fun a => !p a)).filter p = [] := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    cases hb : p a with
    | false => simp only [List.filter_cons, hb, Bool.not_false, if_true]; exact ih
    | true => simp only [List.filter_cons, hb, Bool.not_true]; exact ih

/-- Splitting a list by `p` and by `¬p`, then summing the two lengths, recovers the whole length. -/
theorem length_filter_add_filter_not (p : Int → Bool) (xs : List Int) :
    (xs.filter p).length + (xs.filter (fun a => !p a)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons, List.filter_cons]
    cases hb : p a with
    | false => simp; omega
    | true => simp; omega

/-- Splitting a list by `p` and by `¬p`, then summing the two counts of `v`, recovers the whole
    count — the multiset-honesty law behind any stable partition. -/
theorem countL_filter_add_filter_not (p : Int → Bool) (xs : List Int) (v : Int) :
    LC242.countL (xs.filter p) v + LC242.countL (xs.filter (fun a => !p a)) v
      = LC242.countL xs v := by
  induction xs with
  | nil => rfl
  | cons a t ih =>
    rw [List.filter_cons, List.filter_cons]
    cases hb : p a with
    | false => simp [LC242.countL_cons]; omega
    | true => simp [LC242.countL_cons]; omega

/-! ## Correctness: the four honest clauses -/

/-- **Non-zeros preserved in order**: filtering the program's output for non-zeros gives back
    exactly `xs`'s non-zeros, in the same order — the program neither reorders nor drops any of
    them. -/
theorem moveZeroesFn_filter_nz (xs : List Int) :
    (moveZeroesFn xs).filter nzPred = xs.filter nzPred := by
  rw [moveZeroesFn_eq_partition, List.filter_append]
  have h1 : (xs.filter nzPred).filter nzPred = xs.filter nzPred := by
    rw [List.filter_filter]; simp
  have h2 : (xs.filter zPred).filter nzPred = [] := by
    rw [← filter_not_nzPred_eq_zPred]; exact filter_not_filter_eq_nil nzPred xs
  rw [h1, h2, List.append_nil]

/-- **Same length**: nothing is lost or invented. -/
theorem moveZeroesFn_length (xs : List Int) : (moveZeroesFn xs).length = xs.length := by
  rw [moveZeroesFn_eq_partition, List.length_append, ← filter_not_nzPred_eq_zPred]
  exact length_filter_add_filter_not nzPred xs

/-- **Multiset preserved**: every value occurs the same number of times in the output as in the
    input — nothing lost, nothing invented; pins that the appended zeros exactly replace the
    removed ones. -/
theorem moveZeroesFn_countL (xs : List Int) (v : Int) :
    LC242.countL (moveZeroesFn xs) v = LC242.countL xs v := by
  rw [moveZeroesFn_eq_partition, LC242.countL_append, ← filter_not_nzPred_eq_zPred]
  exact countL_filter_add_filter_not nzPred xs v

/-- **Headline correctness**: `moveZeroesFn` is an honest stable partition of `xs` by `nzPred` —
    non-zeros preserved in order, same length, same multiset, and all zeros trailing (the split
    `moveZeroesFn xs = xs.filter nzPred ++ List.replicate k 0` is the program's own definition;
    only "the first part has no zeros" needs proving on top of it). -/
theorem move_correct (xs : List Int) :
    (moveZeroesFn xs).filter nzPred = xs.filter nzPred ∧
    (moveZeroesFn xs).length = xs.length ∧
    (∀ v, LC242.countL (moveZeroesFn xs) v = LC242.countL xs v) ∧
    (∃ k, moveZeroesFn xs = xs.filter nzPred ++ List.replicate k 0 ∧
      ∀ a ∈ xs.filter nzPred, a ≠ 0) :=
  ⟨moveZeroesFn_filter_nz xs, moveZeroesFn_length xs, moveZeroesFn_countL xs,
    (xs.filter zPred).length, rfl, filter_nz_no_zero xs⟩

/-! ## Specification and the structural-output headline -/

/-- The **specification** as a morphism `Nums ⟶ Nums` in `Rel(Set)`: the output is the input's
    non-zeros (in order) followed by some run of zeros, with the same length.  This pins the STABLE
    move-zeroes uniquely — order-preservation of non-zeros (`xs.filter nzPred` verbatim), all zeros
    trailing (`List.replicate k 0`), and length fixing `k`.  Stated independently of `moveZeroesFn`. -/
def spec : Nums ⟶ Nums := fun xs out =>
  (∃ k, out = xs.filter nzPred ++ List.replicate k 0) ∧ out.length = xs.length

/-- **Uniqueness**: the length forces the number of trailing zeros, so any two spec outputs agree. -/
theorem spec_unique (xs o1 o2 : List Int) (h1 : spec xs o1) (h2 : spec xs o2) : o1 = o2 := by
  obtain ⟨⟨k1, hk1⟩, hl1⟩ := h1
  obtain ⟨⟨k2, hk2⟩, hl2⟩ := h2
  have e1 : (xs.filter nzPred).length + k1 = xs.length := by
    rw [hk1, List.length_append, List.length_replicate] at hl1; exact hl1
  have e2 : (xs.filter nzPred).length + k2 = xs.length := by
    rw [hk2, List.length_append, List.length_replicate] at hl2; exact hl2
  have hk : k1 = k2 := by omega
  rw [hk1, hk2, hk]

/-- **`solve` equals `spec` as relations** — the STRUCTURAL-OUTPUT headline: existence (the program's
    own shape plus `moveZeroesFn_length`) and uniqueness (`spec_unique`) make the program exactly the
    stable move-zeroes relation. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro xs out
  show (out = moveZeroesFn xs) ↔
      ((∃ k, out = xs.filter nzPred ++ List.replicate k 0) ∧ out.length = xs.length)
  constructor
  · intro h; subst h; exact ⟨⟨(xs.filter zPred).length, rfl⟩, moveZeroesFn_length xs⟩
  · intro h
    exact spec_unique xs out (moveZeroesFn xs) h ⟨⟨(xs.filter zPred).length, rfl⟩, moveZeroesFn_length xs⟩

/-! ## Running the program -/

example : moveZeroesFn [0, 1, 0, 3, 12] = [1, 3, 12, 0, 0] := by decide
example : moveZeroesFn [0] = [0] := by decide

end Freyd.Alg.RelSet.LC283
