module

/-
  Verified binary search (`lowerBound`) on a sorted `Array Int`.

  STRICTLY mathlib-free / Std-free: this file imports NOTHING beyond the Lean 4 core prelude
  (`Array`, `Nat`, `Int`, `omega`, `rcases`, `split`).  It is a reusable primitive for
  binary-search LeetCode problems and for the O(n log n) patience-sorting LIS (§L300): the
  tails array stays strictly increasing and each step calls `lowerBound`/`insertOrReplace`.

  `lowerBound a x` is the LEAST index `i ≤ a.size` such that `x ≤ a[i]` (equivalently, `a[j] < x`
  for every `j < i`), returning `a.size` when `x` exceeds every element.  It is computed by the
  usual halving loop (`go`), so it does O(log n) comparisons — Lean proves the *behaviour*
  (the characterizing lemmas below), not the running time.
-/

namespace Freyd.BinSearch

/-- `Sorted a`: non-strictly increasing.  `a[i] ≤ a[j]` for `i < j`.  This is the exact
    monotonicity the `lowerBound` lemmas reason with (a strictly-increasing array is `Sorted`
    too, via `StrictSorted.sorted`). -/
@[expose] public def Sorted (a : Array Int) : Prop :=
  ∀ i j (hij : i < j) (hj : j < a.size), a[i]'(Nat.lt_trans hij hj) ≤ a[j]

/-- `StrictSorted a`: strictly increasing.  `a[i] < a[j]` for `i < j`.  This is what the
    patience-LIS tails satisfy, and what `insertOrReplace` preserves. -/
@[expose] public def StrictSorted (a : Array Int) : Prop :=
  ∀ i j (hij : i < j) (hj : j < a.size), a[i]'(Nat.lt_trans hij hj) < a[j]

public theorem StrictSorted.sorted {a : Array Int} (hs : StrictSorted a) : Sorted a :=
  fun i j hij hj => by have := hs i j hij hj; omega

/-- Monotonicity of a `Sorted` array at `≤` (both the strict and the equal case). -/
public theorem Sorted.le_of_le {a : Array Int} (hs : Sorted a) {i j} (hij : i ≤ j)
    (hj : j < a.size) : a[i]'(Nat.lt_of_le_of_lt hij hj) ≤ a[j] := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact hs i j h hj
  · subst h; omega

/-- The halving loop.  `hhi : hi ≤ a.size` keeps the midpoint in range; the invariant that a
    caller supplies is that everything below `lo` is `< x` and `a[hi] ≥ x` when `hi < a.size`
    (see `go_spec`).  Terminates because `hi - lo` strictly decreases. -/
@[expose] public def go (a : Array Int) (x : Int) (lo hi : Nat) (hhi : hi ≤ a.size) : Nat :=
  if h : lo < hi then
    if a[(lo + hi) / 2]'(by omega) < x then go a x ((lo + hi) / 2 + 1) hi hhi
    else go a x lo ((lo + hi) / 2) (by omega)
  else lo
termination_by hi - lo
decreasing_by all_goals omega

/-- The loop never leaves the interval on the right — no sortedness needed. -/
public theorem go_le_hi (a : Array Int) (x : Int) :
    ∀ (lo hi : Nat) (hhi : hi ≤ a.size), lo ≤ hi → go a x lo hi hhi ≤ hi := by
  intro lo hi hhi
  refine go.induct a x (motive := fun lo hi hhi => lo ≤ hi → go a x lo hi hhi ≤ hi)
    ?_ ?_ ?_ lo hi hhi
  · intro lo hi hhi h hlt ih hle
    rw [go, dif_pos h, if_pos hlt]; exact ih (by omega)
  · intro lo hi hhi h hge ih hle
    rw [go, dif_pos h, if_neg hge]; have := ih (by omega); omega
  · intro lo hi hhi h hle
    rw [go, dif_neg h]; omega

/-- Full behavioural spec of the loop, by well-founded induction on `hi - lo` maintaining the
    two loop invariants (`hI1`: everything below `lo` is `< x`; `hI2`: `a[hi] ≥ x` when in range).
    The `refine go.induct a x (motive := …)` form pins the fixed parameter `x`, which does not
    occur among the induction targets `lo hi hhi`. -/
public theorem go_spec (a : Array Int) (x : Int) (hs : Sorted a) :
    ∀ (lo hi : Nat) (hhi : hi ≤ a.size), lo ≤ hi →
      (∀ j, j < lo → (hj : j < a.size) → a[j] < x) →
      (∀ hh : hi < a.size, x ≤ a[hi]) →
      go a x lo hi hhi ≤ hi ∧
      (∀ j, j < go a x lo hi hhi → (hj : j < a.size) → a[j] < x) ∧
      (∀ hr : go a x lo hi hhi < a.size, x ≤ a[go a x lo hi hhi]) := by
  intro lo hi hhi
  refine go.induct a x
    (motive := fun lo hi hhi => lo ≤ hi →
      (∀ j, j < lo → (hj : j < a.size) → a[j] < x) →
      (∀ hh : hi < a.size, x ≤ a[hi]) →
      go a x lo hi hhi ≤ hi ∧
      (∀ j, j < go a x lo hi hhi → (hj : j < a.size) → a[j] < x) ∧
      (∀ hr : go a x lo hi hhi < a.size, x ≤ a[go a x lo hi hhi]))
    ?_ ?_ ?_ lo hi hhi
  · -- a[mid] < x: search the right half [mid+1, hi)
    intro lo hi hhi h hlt ih hle hI1 hI2
    rw [go, dif_pos h, if_pos hlt]
    refine ih (by omega) ?_ hI2
    intro j hj hjs
    rcases Nat.lt_or_ge j lo with hjlo | hjge
    · exact hI1 j hjlo hjs
    · rcases Nat.lt_or_eq_of_le (show j ≤ (lo + hi) / 2 by omega) with hjm | hjm
      · have := hs j ((lo + hi) / 2) hjm (by omega); omega
      · subst hjm; exact hlt
  · -- x ≤ a[mid]: search the left half [lo, mid)
    intro lo hi hhi h hge ih hle hI1 hI2
    rw [go, dif_pos h, if_neg hge]
    obtain ⟨hb, hc1, hc2⟩ := ih (by omega) hI1 (by intro hh; omega)
    exact ⟨by omega, hc1, hc2⟩
  · -- lo ≥ hi: return lo (= hi under the invariant), the answer
    intro lo hi hhi h hle hI1 hI2
    rw [go, dif_neg h]
    have he : hi = lo := by omega
    exact ⟨hle, hI1, fun hr => he ▸ hI2 (he ▸ hr)⟩

/-- `lowerBound a x` = least index `i ≤ a.size` with `x ≤ a[i]`; `a.size` if `x` exceeds all. -/
@[expose] public def lowerBound (a : Array Int) (x : Int) : Nat := go a x 0 a.size (Nat.le_refl _)

/-- The bundled spec of `lowerBound`, obtained from `go_spec` at `lo = 0, hi = a.size` (both loop
    invariants hold vacuously at entry).  The three public lemmas below are its projections. -/
public theorem lowerBound_spec (a : Array Int) (x : Int) (hs : Sorted a) :
    (∀ j, j < lowerBound a x → (hj : j < a.size) → a[j] < x) ∧
    (∀ hr : lowerBound a x < a.size, x ≤ a[lowerBound a x]) := by
  have h := go_spec a x hs 0 a.size (Nat.le_refl _) (Nat.zero_le _)
    (fun j hj0 _ => absurd hj0 (Nat.not_lt_zero j))
    (fun hh => absurd hh (Nat.lt_irrefl _))
  exact ⟨h.2.1, h.2.2⟩

/-- `lowerBound a x ≤ a.size` — always in range (no sortedness needed). -/
public theorem lowerBound_le_size (a : Array Int) (x : Int) : lowerBound a x ≤ a.size :=
  go_le_hi a x 0 a.size (Nat.le_refl _) (Nat.zero_le _)

/-- Everything strictly to the left of the result is `< x`. -/
public theorem lt_of_lt_lowerBound {a : Array Int} {x : Int} (hs : Sorted a) :
    ∀ j, j < lowerBound a x → (h : j < a.size) → a[j] < x :=
  (lowerBound_spec a x hs).1

/-- When the result is in range, the element there is `≥ x`. -/
public theorem le_of_lowerBound_le {a : Array Int} {x : Int} (hs : Sorted a)
    (h : lowerBound a x < a.size) : x ≤ a[lowerBound a x] :=
  (lowerBound_spec a x hs).2 h

/-- `lowerBound a x = a.size` exactly when `x` is above every element. -/
public theorem lowerBound_eq_size_iff {a : Array Int} {x : Int} (hs : Sorted a) :
    lowerBound a x = a.size ↔ ∀ j (hj : j < a.size), a[j] < x := by
  constructor
  · intro he j hj
    exact lt_of_lt_lowerBound hs j (by omega) hj
  · intro hall
    rcases Nat.lt_or_eq_of_le (lowerBound_le_size a x) with hlt | heq
    · have h1 := le_of_lowerBound_le hs hlt
      have h2 := hall _ hlt
      omega
    · exact heq

/-- `contains a x` decides membership of `x` in a sorted `a` in O(log n): check the element at
    `lowerBound a x`. -/
def contains (a : Array Int) (x : Int) : Bool :=
  if h : lowerBound a x < a.size then decide (a[lowerBound a x] = x) else false

/-- Correctness of `contains`: `true` iff `x` really occurs. -/
theorem contains_iff {a : Array Int} {x : Int} (hs : Sorted a) :
    contains a x = true ↔ ∃ j, ∃ hj : j < a.size, a[j] = x := by
  constructor
  · intro hc
    unfold contains at hc
    split at hc
    · rename_i h
      exact ⟨lowerBound a x, h, of_decide_eq_true hc⟩
    · exact absurd hc (by decide)
  · rintro ⟨j, hj, hjx⟩
    have hij : lowerBound a x ≤ j := by
      rcases Nat.lt_or_ge j (lowerBound a x) with hlt | hge
      · have := lt_of_lt_lowerBound hs j hlt hj; omega
      · exact hge
    have hi_lt : lowerBound a x < a.size := Nat.lt_of_le_of_lt hij hj
    have hx_le := le_of_lowerBound_le hs hi_lt
    have hle := hs.le_of_le hij hj
    have : a[lowerBound a x] = x := by omega
    unfold contains
    rw [dif_pos hi_lt, this]
    exact decide_eq_true rfl

/-- Patience-LIS tails update: overwrite the first tail `≥ x` with `x`, or append `x` when it
    exceeds every tail.  This is exactly the step `L300` performs. -/
@[expose] public def insertOrReplace (a : Array Int) (x : Int) : Array Int :=
  if h : lowerBound a x < a.size then a.set (lowerBound a x) x h else a.push x

/-- The tails grow by at most one (replace keeps the size, append adds one). -/
theorem insertOrReplace_size_le (a : Array Int) (x : Int) :
    (insertOrReplace a x).size ≤ a.size + 1 := by
  unfold insertOrReplace
  split <;> simp only [Array.size_set, Array.size_push] <;> omega

/-- The tails never shrink. -/
public theorem le_insertOrReplace_size (a : Array Int) (x : Int) :
    a.size ≤ (insertOrReplace a x).size := by
  unfold insertOrReplace
  split <;> simp only [Array.size_set, Array.size_push] <;> omega

/-- `insertOrReplace` keeps the tails strictly increasing — the invariant patience sorting needs. -/
public theorem insertOrReplace_strictSorted {a : Array Int} {x : Int} (hs : StrictSorted a) :
    StrictSorted (insertOrReplace a x) := by
  have hsort := hs.sorted
  unfold insertOrReplace
  split
  · -- replace at i₀ = lowerBound a x
    rename_i hlt
    intro i j hij hj
    rw [Array.size_set] at hj
    have hjs : j < a.size := hj
    have his : i < a.size := Nat.lt_trans hij hjs
    rw [Array.getElem_set hlt, Array.getElem_set hlt]
    -- case on whether i or j is the replaced index
    by_cases hi0 : lowerBound a x = i
    · -- i = i₀: left value is x, need x < a[j].  x ≤ a[i₀] < a[j] since i₀ = i < j.
      subst hi0
      have hne : ¬ lowerBound a x = j := by omega
      rw [if_pos rfl, if_neg hne]
      have h1 := le_of_lowerBound_le hs.sorted hlt
      have h2 := hs (lowerBound a x) j hij hjs
      omega
    · rw [if_neg hi0]
      by_cases hj0 : lowerBound a x = j
      · -- j = i₀: right value is x, need a[i] < x.  i < i₀ ⟹ a[i] < x.
        rw [if_pos hj0]
        have hilt : i < lowerBound a x := by omega
        exact lt_of_lt_lowerBound hs.sorted i hilt his
      · -- neither endpoint replaced: plain strict sortedness.
        rw [if_neg hj0]
        exact hs i j hij hjs
  · -- append x: lowerBound = a.size means every element is < x.
    rename_i hge
    have hall : ∀ k (hk : k < a.size), a[k] < x := by
      have heq : lowerBound a x = a.size := by
        have := lowerBound_le_size a x; omega
      exact (lowerBound_eq_size_iff hsort).1 heq
    intro i j hij hj
    rw [Array.size_push] at hj
    rw [Array.getElem_push, Array.getElem_push]
    by_cases hjs : j < a.size
    · rw [dif_pos hjs, dif_pos (Nat.lt_trans hij hjs)]
      exact hs i j hij hjs
    · -- j is the appended slot (= a.size), so a[i] < x = last
      have hjeq : j = a.size := by omega
      have his : i < a.size := by omega
      rw [dif_neg hjs, dif_pos his]
      exact hall i his

/- Sanity checks (elaboration-time evaluation; add no axioms to the theorems above). -/
#guard lowerBound #[1, 3, 5, 7] 4 = 2          -- first index with value ≥ 4
#guard lowerBound #[1, 3, 5, 7] 1 = 0          -- x ≤ head
#guard lowerBound #[1, 3, 5, 7] 0 = 0          -- x below head
#guard lowerBound #[1, 3, 5, 7] 8 = 4          -- x above all → size
#guard lowerBound #[1, 3, 5, 7] 5 = 2          -- exact hit
#guard lowerBound (#[] : Array Int) 3 = 0      -- empty
#guard contains #[1, 3, 5, 7] 5 = true
#guard contains #[1, 3, 5, 7] 4 = false
#guard (insertOrReplace #[1, 3, 5, 7] 4).size = 4   -- replace
#guard (insertOrReplace #[1, 3, 5, 7] 9).size = 5   -- append

end Freyd.BinSearch
