/-
  LeetCode 11 — Container With Most Water — as an ALLEGORY PROGRAM.

  Problem: given heights `h₀,…,h_{n-1}` (all `≥ 0`, one per vertical line), pick two positions
  `i < j` maximising the water area `min(h i, h j) * (j - i)` held between the two lines.

  1. **Data** — a plain `List Int` (no `SnocList` engine: the program does not scan left-to-right
     once, it walks TWO pointers toward each other, so there is no catamorphism to exploit).

  2. **Program** — the classic two-pointer sweep: start `lo = 0`, `hi = n-1`; record the current
     window's area, then move the pointer at the SHORTER line inward (discarding it can never lose
     the optimum — see below); repeat, tracking the running max.  Because the two indices move
     independently the naive recursion is NOT structural on either one, so it is tamed with a
     `fuel` parameter (`twoPtrFuel`, `leetcode.md` skill S13), fuel `= h.length` (comfortably more
     than the `≤ h.length - 1` steps the window can take to collapse).

  3. **Specification** — `IsPairArea h a := ∃ i j, i < j ∧ j < h.length ∧ a = Area h i j`, the
     relation of *achievable* areas over EVERY pair, not just the ones the sweep visits.  LeetCode
     11 asks for its `≤`-maximum, i.e. `max (≤) · Λ spec` (`leetcode.md`'s "optimisation" shape).

  4. **Correctness** — `maxArea_correct`: the returned area is achievable (`maxArea_achievable`)
     and dominates every achievable area (`maxArea_dominates`).  The genuine content is the
     **window invariant** `twoPtrFuel_correct`: over any window `[lo,hi]`, with enough fuel, the
     sweep computes the maximum `Area` among all pairs *inside that window* — proved by induction
     on `fuel`.  Its step lemma is the "discard the shorter side" fact (`discard_lo`/`discard_hi`):
     if `h lo ≤ h hi`, then EVERY pair `(lo, j)` with `j ≤ hi` is dominated by the full window's
     pair `(lo, hi)`, since `min(h lo, h j) ≤ h lo = min(h lo, h hi)` (the min can only shrink) AND
     the width `j - lo < hi - lo` (both symmetrically for `hi`) — so a `min(≤,≤)`-and-`(≤,≤)`-width
     pair with BOTH nonnegative dominates via `Int.mul_le_mul`, using the problem's `h ≥ 0`
     constraint (`Nonneg`).  Discarding `lo` therefore loses no candidate better than the one just
     recorded, which is exactly what makes the greedy pointer move safe.

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (fully constructive, no `Classical.choice`).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet
import Freyd.Exacts

namespace Freyd.Alg.RelSet.LC11

open Freyd

/-! ## Integer `min`/`max` (mathlib-free, so we control the rewrite lemmas — copied from `L121`) -/

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imin_le_left  (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
theorem imin_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ imin a b := by
  unfold imin; split <;> omega
theorem imax_ge_left  (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Int) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## The program: two-pointer sweep, tamed with fuel -/

/-- The water held between positions `i` and `j`: the shorter height times the width. -/
def Area (h : List Int) (i j : Nat) : Int := imin h[i]! h[j]! * ((j : Int) - (i : Int))

/-- Two-pointer sweep over the window `[lo,hi]`, structural on `fuel`.  At each step records the
    window's own area, then discards the SHORTER side (moves that pointer inward); returns the
    running max over everything seen. -/
def twoPtrFuel (h : List Int) : Nat → Nat → Nat → Int
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    if lo < hi then
      if h[lo]! ≤ h[hi]! then imax (Area h lo hi) (twoPtrFuel h fuel (lo + 1) hi)
      else imax (Area h lo hi) (twoPtrFuel h fuel lo (hi - 1))
    else 0

/-- **The program**: LeetCode 11's solution.  `n < 2` has no valid pair — area `0`. -/
def maxAreaFn (h : List Int) : Int :=
  if h.length ≥ 2 then twoPtrFuel h h.length 0 (h.length - 1) else 0

/-! ## `Rel(Set)` packaging -/

abbrev Heights : RelSet.{0} := ⟨List Int⟩
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-- **The allegory program**: LeetCode 11's solution as a morphism `Heights ⟶ ℤ` in `Rel(Set)`. -/
def solve : Heights ⟶ dZ := graph maxAreaFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map maxAreaFn

/-! ## Specification: the maximum area over ALL pairs, not just the ones the sweep visits -/

/-- `IsPairArea h a` — `a` is the water area of SOME genuine pair `i < j < h.length`. -/
def IsPairArea (h : List Int) (a : Int) : Prop := ∃ i j, i < j ∧ j < h.length ∧ a = Area h i j

/-! ## The problem's constraint: all heights are non-negative

    Threaded through the whole domination argument: it makes the "discard the shorter side" step
    a genuine `Int.mul_le_mul` (both factors compared are `≥ 0`), and it rules out a discarded
    window ever hiding a STRICTLY BETTER area than the `0` floor the fuel induction reports for an
    empty window (a negative area is impossible once every height is `≥ 0`). -/
abbrev Nonneg (h : List Int) : Prop := ∀ i, i < h.length → 0 ≤ h[i]!

/-- Every genuine pair's area is `≥ 0` (both factors of the product are `≥ 0`). -/
theorem Area_nonneg {h : List Int} (hnn : Nonneg h) {i j : Nat} (hij : i < j)
    (hjlt : j < h.length) : 0 ≤ Area h i j := by
  have hilt : i < h.length := by omega
  have hmin : (0 : Int) ≤ imin h[i]! h[j]! := imin_nonneg (hnn i hilt) (hnn j hjlt)
  have hw : (0 : Int) ≤ (j : Int) - (i : Int) := by omega
  exact Int.mul_nonneg hmin hw

/-! ## The crux: discarding the shorter side loses no candidate better than the current window -/

/-- **Discard the left pointer.** If `h lo ≤ h hi`, every pair `(lo, j)` inside the window
    (`lo < j ≤ hi`) is dominated by the FULL window's pair `(lo, hi)`: the min can only shrink
    (`min(h lo, h j) ≤ h lo = min(h lo, h hi)`) and the width only grows (`j - lo ≤ hi - lo`), and
    both factors are `≥ 0` (`Nonneg`), so `Int.mul_le_mul` chains the two into one product
    inequality. -/
theorem discard_lo {h : List Int} (hnn : Nonneg h) {lo hi : Nat} (hbound : hi < h.length)
    (hle : h[lo]! ≤ h[hi]!) : ∀ j, lo < j → j ≤ hi → Area h lo j ≤ Area h lo hi := by
  intro j hlj hjhi
  have hjlt : j < h.length := by omega
  have hloL : (0 : Int) ≤ h[lo]! := hnn lo (by omega)
  have hAeq : imin h[lo]! h[hi]! = h[lo]! := by unfold imin; split <;> omega
  have hA : imin h[lo]! h[j]! ≤ imin h[lo]! h[hi]! := by rw [hAeq]; exact imin_le_left _ _
  have hAnn : (0 : Int) ≤ imin h[lo]! h[hi]! := by rw [hAeq]; exact hloL
  have hw1 : (0 : Int) ≤ (j : Int) - (lo : Int) := by omega
  have hw2 : (j : Int) - (lo : Int) ≤ (hi : Int) - (lo : Int) := by omega
  show imin h[lo]! h[j]! * ((j : Int) - (lo : Int)) ≤
      imin h[lo]! h[hi]! * ((hi : Int) - (lo : Int))
  exact Int.mul_le_mul hA hw2 hw1 hAnn

/-- **Discard the right pointer** (mirror image of `discard_lo`). -/
theorem discard_hi {h : List Int} (hnn : Nonneg h) {lo hi : Nat} (hbound : hi < h.length)
    (hle : h[hi]! ≤ h[lo]!) : ∀ i, lo ≤ i → i < hi → Area h i hi ≤ Area h lo hi := by
  intro i hli hihi
  have hilt : i < h.length := by omega
  have hhiL : (0 : Int) ≤ h[hi]! := hnn hi hbound
  have hAeq : imin h[lo]! h[hi]! = h[hi]! := by unfold imin; split <;> omega
  have hA : imin h[i]! h[hi]! ≤ imin h[lo]! h[hi]! := by rw [hAeq]; exact imin_le_right _ _
  have hAnn : (0 : Int) ≤ imin h[lo]! h[hi]! := by rw [hAeq]; exact hhiL
  have hw1 : (0 : Int) ≤ (hi : Int) - (i : Int) := by omega
  have hw2 : (hi : Int) - (i : Int) ≤ (hi : Int) - (lo : Int) := by omega
  show imin h[i]! h[hi]! * ((hi : Int) - (i : Int)) ≤
      imin h[lo]! h[hi]! * ((hi : Int) - (lo : Int))
  exact Int.mul_le_mul hA hw2 hw1 hAnn

/-! ## The window invariant, by induction on fuel -/

/-- **The window invariant**: over the window `[lo,hi]` with enough `fuel` (`hi ≤ lo + fuel`), the
    sweep `twoPtrFuel` computes the `≤`-maximum `Area` among ALL pairs `i < j` inside the window —
    achievable when the window is non-trivial (`lo < hi`), `0` when it has collapsed (`hi ≤ lo`),
    and dominating unconditionally. -/
theorem twoPtrFuel_correct {h : List Int} (hnn : Nonneg h) :
    ∀ fuel lo hi, hi < h.length → hi ≤ lo + fuel →
      (lo < hi → ∃ i j, lo ≤ i ∧ i < j ∧ j ≤ hi ∧ twoPtrFuel h fuel lo hi = Area h i j) ∧
      (hi ≤ lo → twoPtrFuel h fuel lo hi = 0) ∧
      (∀ i j, lo ≤ i → i < j → j ≤ hi → Area h i j ≤ twoPtrFuel h fuel lo hi) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hbound hfuel
    refine ⟨fun hlt => by exfalso; omega, fun _ => rfl, ?_⟩
    intro i j hloi hij hjhi
    exfalso; omega
  | succ fuel ih =>
    intro lo hi hbound hfuel
    by_cases hlt : lo < hi
    · have hunfold : twoPtrFuel h (fuel + 1) lo hi =
          if h[lo]! ≤ h[hi]! then imax (Area h lo hi) (twoPtrFuel h fuel (lo + 1) hi)
          else imax (Area h lo hi) (twoPtrFuel h fuel lo (hi - 1)) := by
        simp only [twoPtrFuel]; rw [if_pos hlt]
      by_cases hle : h[lo]! ≤ h[hi]!
      · -- discard `lo`
        obtain ⟨hach, hzero, hdom⟩ := ih (lo + 1) hi hbound (by omega)
        refine ⟨fun _ => ?_, fun hle' => by exfalso; omega, ?_⟩
        · rw [hunfold, if_pos hle]
          rcases imax_eq_or (Area h lo hi) (twoPtrFuel h fuel (lo + 1) hi) with heq | heq
          · exact ⟨lo, hi, Nat.le_refl _, hlt, Nat.le_refl _, by rw [heq]⟩
          · by_cases hlt' : lo + 1 < hi
            · obtain ⟨i, j, hloi, hij, hjhi, haeq⟩ := hach hlt'
              exact ⟨i, j, by omega, hij, hjhi, by rw [heq, haeq]⟩
            · have hz := hzero (by omega)
              have h1 : Area h lo hi ≤ 0 := by
                have := imax_ge_left (Area h lo hi) (twoPtrFuel h fuel (lo + 1) hi)
                rw [heq, hz] at this; exact this
              have h2 : (0 : Int) ≤ Area h lo hi := Area_nonneg hnn hlt hbound
              have ha0 : Area h lo hi = 0 := by omega
              exact ⟨lo, hi, Nat.le_refl _, hlt, Nat.le_refl _, by rw [heq, hz, ha0]⟩
        · intro i j hloi hij hjhi
          rw [hunfold, if_pos hle]
          by_cases hieq : i = lo
          · rw [hieq] at hij ⊢
            calc Area h lo j ≤ Area h lo hi := discard_lo hnn hbound hle j hij hjhi
              _ ≤ imax (Area h lo hi) (twoPtrFuel h fuel (lo + 1) hi) := imax_ge_left _ _
          · calc Area h i j ≤ twoPtrFuel h fuel (lo + 1) hi :=
                  hdom i j (by omega) hij hjhi
              _ ≤ imax (Area h lo hi) (twoPtrFuel h fuel (lo + 1) hi) := imax_ge_right _ _
      · -- discard `hi`
        have hle' : h[hi]! ≤ h[lo]! := by omega
        obtain ⟨hach, hzero, hdom⟩ := ih lo (hi - 1) (by omega) (by omega)
        refine ⟨fun _ => ?_, fun hle'' => by exfalso; omega, ?_⟩
        · rw [hunfold, if_neg hle]
          rcases imax_eq_or (Area h lo hi) (twoPtrFuel h fuel lo (hi - 1)) with heq | heq
          · exact ⟨lo, hi, Nat.le_refl _, hlt, Nat.le_refl _, by rw [heq]⟩
          · by_cases hlt' : lo < hi - 1
            · obtain ⟨i, j, hloi, hij, hjhi, haeq⟩ := hach hlt'
              exact ⟨i, j, hloi, hij, by omega, by rw [heq, haeq]⟩
            · have hz := hzero (by omega)
              have h1 : Area h lo hi ≤ 0 := by
                have := imax_ge_left (Area h lo hi) (twoPtrFuel h fuel lo (hi - 1))
                rw [heq, hz] at this; exact this
              have h2 : (0 : Int) ≤ Area h lo hi := Area_nonneg hnn hlt hbound
              have ha0 : Area h lo hi = 0 := by omega
              exact ⟨lo, hi, Nat.le_refl _, hlt, Nat.le_refl _, by rw [heq, hz, ha0]⟩
        · intro i j hloi hij hjhi
          rw [hunfold, if_neg hle]
          by_cases hjeq : j = hi
          · rw [hjeq] at hij ⊢
            calc Area h i hi ≤ Area h lo hi := discard_hi hnn hbound hle' i hloi hij
              _ ≤ imax (Area h lo hi) (twoPtrFuel h fuel lo (hi - 1)) := imax_ge_left _ _
          · calc Area h i j ≤ twoPtrFuel h fuel lo (hi - 1) :=
                  hdom i j hloi hij (by omega)
              _ ≤ imax (Area h lo hi) (twoPtrFuel h fuel lo (hi - 1)) := imax_ge_right _ _
    · refine ⟨fun hlt' => absurd hlt' hlt, fun _ => ?_, ?_⟩
      · show twoPtrFuel h (fuel + 1) lo hi = 0
        simp only [twoPtrFuel]; rw [if_neg hlt]
      · intro i j hloi hij hjhi
        exfalso; omega

/-! ## Top-level correctness: `maxArea_correct = achievability ∧ domination` -/

/-- **Achievability**: the reported max area is realized by an actual pair (needs `n ≥ 2`, else
    there is no pair at all). -/
theorem maxArea_achievable {h : List Int} (hnn : Nonneg h) (hlen : 2 ≤ h.length) :
    IsPairArea h (maxAreaFn h) := by
  unfold maxAreaFn; rw [if_pos hlen]
  obtain ⟨i, j, hloi, hij, hjhi, heq⟩ :=
    (twoPtrFuel_correct hnn h.length 0 (h.length - 1) (by omega) (by omega)).1 (by omega)
  exact ⟨i, j, hij, by omega, heq⟩

/-- **Domination**: no pair beats the reported max area — holds unconditionally (if `n < 2` there
    is no pair `i < j < h.length` to begin with, so the statement is vacuous there). -/
theorem maxArea_dominates {h : List Int} (hnn : Nonneg h) : ∀ a, IsPairArea h a → a ≤ maxAreaFn h := by
  rintro a ⟨i, j, hij, hjlt, ha⟩
  have hlen2 : 2 ≤ h.length := by omega
  unfold maxAreaFn; rw [if_pos hlen2]
  rw [ha]
  exact (twoPtrFuel_correct hnn h.length 0 (h.length - 1) (by omega) (by omega)).2.2
    i j (by omega) hij (by omega)

/-- **Correctness of the allegory program**: `maxAreaFn` computes exactly `max (≤) · Λ IsPairArea` —
    it is achievable AND dominates every achievable area. -/
theorem maxArea_correct {h : List Int} (hnn : Nonneg h) (hlen : 2 ≤ h.length) :
    IsPairArea h (maxAreaFn h) ∧ ∀ a, IsPairArea h a → a ≤ maxAreaFn h :=
  ⟨maxArea_achievable hnn hlen, maxArea_dominates hnn⟩

/-! ## Running the program -/

example : maxAreaFn [1, 8, 6, 2, 5, 4, 8, 3, 7] = 49 := by decide
example : maxAreaFn [1, 1] = 1 := by decide

end Freyd.Alg.RelSet.LC11
