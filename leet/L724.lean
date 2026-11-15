/-
  LeetCode 724 — Find Pivot Index — as an ALLEGORY PROGRAM.

  Problem: given `nums : List Int`, find the LEFTMOST index `i` where the sum of the elements
  strictly to the left of `i` equals the sum of the elements strictly to the right of `i`; return
  `-1` (here: `none`) if no such index exists.

  1. **Data** — a plain `List Int` (no `SnocList` machinery needed, as in `L303`/`L238`); the answer
     object is `Option Nat` (`none` = no pivot).

  2. **Program** — `pivotFn nums := pivotScan nums.sum 0 0 nums`: a single left-to-right structural
     scan carrying `(i, leftSum)` against the precomputed `total := nums.sum`.  At index `i` holding
     element `x`, `x` is a pivot iff `leftSum = total - leftSum - x` (the running left sum equals the
     remaining right sum); the scan returns the FIRST such `i`, else `none`.  Plain single-argument
     structural recursion on the list (no fuel — the accumulator changes but the recursion target,
     the list, always shrinks, exactly `L303`'s `scanlAdd` shape).

  3. **Specification** — the HONEST per-index slice sums, no reference to the program's own running
     total: `leftSumAt nums i := (nums.take i).sum`, `rightSumAt nums i := (nums.drop (i+1)).sum`,
     `IsPivot nums i := i < nums.length ∧ leftSumAt nums i = rightSumAt nums i`.

  4. **Correctness** — the crux is ONE scan-invariant induction (`pivotScan_correct`), generalizing
     over the ALREADY-SCANNED prefix `pre` (so `xs = ` the unscanned suffix, `leftSum = pre.sum`,
     `total = pre.sum + xs.sum`) and proving, for the sub-scan `pivotScan total pre.length leftSum
     xs`: a `some k` return is a genuine pivot of `pre ++ xs` that is the LEFTMOST among indices
     `≥ pre.length`, and a `none` return means no index `≥ pre.length` is a pivot.  At `pre = []`
     this specializes to `pivotFn`'s full soundness + leftmost + none-completeness.  The pivot-index
     characterization at each step is the single iff `hiff : IsPivot (pre ++ (x::xs')) pre.length ↔
     leftSum = total - leftSum - x` — proved ONCE via the algebraic identity `total - leftSum - x =
     xs'.sum` (from `total = pre.sum + x + xs'.sum`, `List.sum_cons`) together with the CORE list
     lemmas `List.take_left`/`List.drop_left'` (`leftSumAt (pre++(x::xs')) pre.length = pre.sum`,
     `rightSumAt (pre++(x::xs')) pre.length = xs'.sum`) — this sidesteps re-deriving `L303`'s general
     `sum_append_int`/telescoping split for the per-index characterization; `sum_append_int` (imported
     from `L303`) is used only once, to maintain `leftSum + x = (pre ++ [x]).sum` across the recursive
     step (growing the prefix by one element).

  Mathlib-free; reuses `L303.sum_append_int` (core only proves `sum_append` for `List Nat`).  Axioms
  `⊆ {propext, Quot.sound}` — a straight `graph`/`Map` packaging, fully constructive.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet
import leet.L303

namespace Freyd.Alg.RelSet.LC724

open Freyd
open Freyd.Alg.RelSet.LC303 (sum_append_int)

/-! ## Data & answer object -/

/-- The object of number lists in `Rel(Set)`. -/
abbrev Data : RelSet.{0} := ⟨List Int⟩
/-- The object of answers: `some i` (pivot index) or `none` (no pivot). -/
abbrev Answer : RelSet.{0} := ⟨Option Nat⟩

/-! ## The program: one structural scan carrying `(index, running left sum)` -/

/-- `pivotScan total i leftSum xs`: scan the (unscanned) suffix `xs`, whose first element sits at
    index `i` with `leftSum` already accumulated to its left; `x` at index `i` is a pivot iff
    `leftSum = total - leftSum - x` (running left sum = remaining right sum).  Returns the first
    such index, else `none`.  Structural recursion on `xs` (the only argument that shrinks). -/
def pivotScan (total : Int) : Nat → Int → List Int → Option Nat
  | _, _, [] => none
  | i, leftSum, x :: xs =>
    if leftSum = total - leftSum - x then some i else pivotScan total (i + 1) (leftSum + x) xs

/-- **The program's underlying function**: precompute the total once, scan from the start. -/
def pivotFn (nums : List Int) : Option Nat := pivotScan nums.sum 0 0 nums

/-! ## The specification: the honest per-index left/right slice sums -/

/-- The sum of the elements strictly to the left of index `i`. -/
def leftSumAt (nums : List Int) (i : Nat) : Int := (nums.take i).sum
/-- The sum of the elements strictly to the right of index `i`. -/
def rightSumAt (nums : List Int) (i : Nat) : Int := (nums.drop (i + 1)).sum

/-- `IsPivot nums i` — `i` is a valid index of `nums` whose left and right slice sums agree. -/
def IsPivot (nums : List Int) (i : Nat) : Prop :=
  i < nums.length ∧ leftSumAt nums i = rightSumAt nums i

/-! ## Correctness — the crux scan invariant -/

/-- **The scan invariant**: processing the unscanned suffix `xs` of `pre ++ xs` (with `leftSum =
    pre.sum` already accumulated and `total` fixed as the sum of the whole list) finds exactly the
    LEFTMOST pivot at or after index `pre.length`, or confirms none exists there. -/
theorem pivotScan_correct (total : Int) :
    ∀ (pre xs : List Int) (leftSum : Int), leftSum = pre.sum → total = pre.sum + xs.sum →
      (∀ k, pivotScan total pre.length leftSum xs = some k →
          IsPivot (pre ++ xs) k ∧ ∀ j, pre.length ≤ j → j < k → ¬ IsPivot (pre ++ xs) j) ∧
      (pivotScan total pre.length leftSum xs = none → ∀ j, pre.length ≤ j → ¬ IsPivot (pre ++ xs) j) := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
    intro leftSum _ _
    refine ⟨fun k hk => by simp [pivotScan] at hk, fun _ j hj hpiv => ?_⟩
    simp only [List.append_nil] at hpiv
    exact absurd hpiv.1 (by omega)
  | cons x xs' ih =>
    intro leftSum hls htot
    -- the algebraic identity linking the scan's test to the honest right sum
    have hsum_cons : (x :: xs').sum = x + xs'.sum := List.sum_cons
    have hcheck : total - leftSum - x = xs'.sum := by omega
    -- pivot-index characterization at `pre.length`, proved once
    have htake : (pre ++ (x :: xs')).take pre.length = pre := List.take_left
    have hdrop : (pre ++ (x :: xs')).drop (pre.length + 1) = xs' := by
      have heq : pre ++ (x :: xs') = (pre ++ [x]) ++ xs' := by simp
      have hlen : (pre ++ [x]).length = pre.length + 1 := by simp
      rw [heq, ← hlen]; exact List.drop_left
    have hlt : pre.length < (pre ++ (x :: xs')).length := by simp
    have hiff : IsPivot (pre ++ (x :: xs')) pre.length ↔ leftSum = total - leftSum - x := by
      unfold IsPivot leftSumAt rightSumAt
      rw [htake, hdrop, hcheck, hls]
      exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩
    by_cases hc : leftSum = total - leftSum - x
    · -- a pivot is found right here, at index `pre.length`
      have hshow : pivotScan total pre.length leftSum (x :: xs') = some pre.length := if_pos hc
      refine ⟨fun k hk => ?_, fun hnone => ?_⟩
      · rw [hshow] at hk
        have hk' : k = pre.length := (Option.some.inj hk).symm
        subst hk'
        exact ⟨hiff.mpr hc, fun j hj1 hj2 => absurd hj2 (by omega)⟩
      · rw [hshow] at hnone; exact absurd hnone (by simp)
    · -- no pivot here: recurse on the rest with the prefix grown by `x`
      have hshow : pivotScan total pre.length leftSum (x :: xs') =
          pivotScan total (pre.length + 1) (leftSum + x) xs' := if_neg hc
      have hxsum : (pre ++ [x]).sum = pre.sum + x := by rw [sum_append_int]; simp
      have hpre' : leftSum + x = (pre ++ [x]).sum := by omega
      have htot' : total = (pre ++ [x]).sum + xs'.sum := by omega
      have hlen' : (pre ++ [x]).length = pre.length + 1 := by simp
      obtain ⟨ihsome, ihnone⟩ := ih (pre ++ [x]) (leftSum + x) hpre' htot'
      rw [hlen'] at ihsome ihnone
      have happ : (pre ++ [x]) ++ xs' = pre ++ (x :: xs') := by simp
      refine ⟨fun k hk => ?_, fun hnone j hj => ?_⟩
      · rw [hshow] at hk
        obtain ⟨hpiv, hleft⟩ := ihsome k hk
        rw [happ] at hpiv hleft
        refine ⟨hpiv, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_or_ge j (pre.length + 1) with hcase | hcase
        · have hjeq : j = pre.length := by omega
          subst hjeq; exact fun hp => hc (hiff.mp hp)
        · exact hleft j hcase hj2
      · rw [hshow] at hnone
        have hall := ihnone hnone
        rw [happ] at hall
        rcases Nat.lt_or_ge j (pre.length + 1) with hcase | hcase
        · have hjeq : j = pre.length := by omega
          subst hjeq; exact fun hp => hc (hiff.mp hp)
        · exact hall j hcase

/-- **Headline correctness**: soundness, leftmost, and none-completeness, bundled. -/
theorem pivot_correct (nums : List Int) :
    (∀ i, pivotFn nums = some i → IsPivot nums i) ∧
    (∀ i, pivotFn nums = some i → ∀ j, j < i → ¬ IsPivot nums j) ∧
    (pivotFn nums = none → ∀ j, ¬ IsPivot nums j) := by
  have h := pivotScan_correct nums.sum [] nums 0 (by simp) (by simp)
  simp only [List.length_nil, List.nil_append] at h
  obtain ⟨hsome, hnone⟩ := h
  exact ⟨fun i hi => (hsome i hi).1, fun i hi j hj => (hsome i hi).2 j (by omega) hj,
    fun hn j => hnone hn j (by omega)⟩

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The allegory program**: LeetCode 724's solution as a morphism `Data ⟶ Option ℕ` in `Rel(Set)`. -/
def solve : Data ⟶ Answer := graph pivotFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map pivotFn

/-! ## Specification and the exact-value (Option) headline -/

/-- The **specification** as a morphism `Data ⟶ Option ℕ` in `Rel(Set)`: a `some i` answer is the
    LEFTMOST pivot index (`IsPivot` and no earlier pivot); a `none` answer means no pivot exists.
    Stated via `IsPivot` (program-independent), NOT via `pivotFn`. -/
def spec : Data ⟶ Answer := fun nums r =>
  match r with
  | some i => IsPivot nums i ∧ ∀ j, j < i → ¬ IsPivot nums j
  | none => ∀ j, ¬ IsPivot nums j

/-- **Uniqueness of the leftmost pivot**: two leftmost pivots are equal — the smaller would refute
    the other's "no earlier pivot" clause. -/
theorem pivot_index_unique (nums : List Int) (i i' : Nat)
    (h : IsPivot nums i ∧ ∀ j, j < i → ¬ IsPivot nums j)
    (h' : IsPivot nums i' ∧ ∀ j, j < i' → ¬ IsPivot nums j) : i = i' := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h.1 (h'.2 i hlt)
  · exact heq
  · exact absurd h'.1 (h.2 i' hgt)

/-- **`spec` is functional**: at most one answer satisfies it — the leftmost-pivot clauses pin
    `some`, and `none` excludes any `some` by the pivot at that index. -/
theorem spec_functional (nums : List Int) : ∀ r₁ r₂ : Option Nat,
    spec nums r₁ → spec nums r₂ → r₁ = r₂ := by
  intro r₁ r₂ h₁ h₂
  cases r₁ with
  | some i =>
    cases r₂ with
    | some i' => rw [pivot_index_unique nums i i' h₁ h₂]
    | none => exact absurd h₁.1 (h₂ i)
  | none =>
    cases r₂ with
    | some i' => exact absurd h₂.1 (h₁ i')
    | none => rfl

/-- **`pivotFn` meets its spec** (both the `some` and `none` cases of `pivot_correct`). -/
theorem pivotFn_spec (nums : List Int) : spec nums (pivotFn nums) := by
  obtain ⟨hs, hlm, hn⟩ := pivot_correct nums
  show match pivotFn nums with
    | some i => IsPivot nums i ∧ ∀ j, j < i → ¬ IsPivot nums j
    | none => ∀ j, ¬ IsPivot nums j
  cases hf : pivotFn nums with
  | some i => exact ⟨hs i hf, hlm i hf⟩
  | none => exact hn hf

/-- **`solve` equals `spec` as relations** — the EXACT-VALUE (Option) headline: existence
    (`pivotFn_spec`) plus uniqueness (`spec_functional`) make the program exactly the leftmost-pivot
    relation. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro nums r
  show (r = pivotFn nums) ↔ spec nums r
  constructor
  · intro h; subst h; exact pivotFn_spec nums
  · intro h; exact spec_functional nums r (pivotFn nums) h (pivotFn_spec nums)

/-! ## Running the program -/

example : pivotFn [1, 7, 3, 6, 5, 6] = some 3 := by decide
example : pivotFn [1, 2, 3] = none := by decide

end Freyd.Alg.RelSet.LC724

