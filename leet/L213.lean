/-
  LeetCode 213 — House Robber II — as an ALLEGORY PROGRAM.

  Problem: like LeetCode 198 (`leet/L198.lean`), but the houses stand in a CIRCLE — the first and
  last house are now adjacent, so a selection may never take BOTH of them.  Robbing nothing is
  always allowed.

  **Circular DP = max over two linear passes that each break the ring.**  Any non-adjacent
  selection that avoids taking both ends fails to contain the last house, or fails to contain the
  first house (or both) — so it lies entirely within `dropLast` (drop the last house) or entirely
  within `tail` (drop the first house), each an ordinary LINEAR house row with no wraparound.
  Conversely every linear selection of either sub-row is already such a selection of the full
  circle (it never touches the dropped end).  So the answer is `max(robLine dropLast, robLine
  tail)`, reusing L198's linear fold on each sub-row.  A single house is the one place this breaks
  down (both sub-rows come out empty) and gets its own `rob-it-or-not` case.

  1. **Data** — same `SnocList ℤ ℤ` as L198; `toList` unpacks it to a plain `List Int` so
     `dropLast`/`tail` make sense.

  2. **Program** — `robLine : List Int → Int`, L198's `foldFn`/`solveFn` fold ported to `List Int`
     (base case `[]` ↦ `0`, the sum of the empty selection) so it applies uniformly to any
     sub-row, including the empty one.  `solveFn xs`: if `toList xs` is a singleton `[x]`, answer
     `imax x 0`; otherwise `imax (robLine dropLast) (robLine tail)`.

  3. **Specification** — `circSpec xs v`: `v` is achievable as a linear (non-wraparound) robbery
     of `dropLast`, OR of `tail` — i.e. `v` is a non-adjacent-selection sum that does not take both
     the first and the last house (the argument above).  The singleton case gets its own
     `v = x ∨ v = 0` clause, since `dropLast`/`tail` both collapse to `[]` there.

  4. **Correctness** — `solve = max (≤) · Λ circSpec`, built from the LINEAR fold's own
     refinement+domination (`robLine_correct`, a direct port of L198's `foldFn_dominates`/
     `foldFn_is_rob` to `List Int`) glued at the `imax` by one generic two-list lemma
     (`imax_disj_correct`) — no separate "circular gluing" proof needed once `circSpec` is stated
     as the disjunction of the two linear specs.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import AOP.A7_4_Horner   -- `eq_Λ_comp_est`: the `max (≤)·Λ spec` morphism-equation bridge
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC213

open Freyd Freyd.Alg.RelSet.SL

/-! ## Integer `max` (mathlib-free, so we control the rewrite lemmas) -/

def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imax_ge_left  (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem imax_ge_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega
theorem imax_eq_or (a b : Int) : imax a b = a ∨ imax a b = b := by
  unfold imax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Data: houses as a non-empty snoc-list of integers -/

/-- The object of house arrays in `Rel(Set)` — `SnocList ℤ ℤ`. -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The object of integers (robbery totals) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-- Unpack a `SnocList` into a plain list, in index order (so `dropLast`/`tail` make sense). -/
def toList : SnocList Int Int → List Int
  | SnocList.wrap x => [x]
  | SnocList.snoc xs q => toList xs ++ [q]

@[simp] theorem toList_wrap (x : Int) : toList (SnocList.wrap x) = [x] := rfl
@[simp] theorem toList_snoc (xs : SnocList Int Int) (q : Int) :
    toList (SnocList.snoc xs q) = toList xs ++ [q] := rfl

/-- Build a house array from a first value and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

/-! ## The linear DP fold: max non-adjacent sum over a `List Int` (L198's `foldFn`, ported; the
    empty list is now a genuine base case, `0`, since a sub-row can be empty) -/

/-- The fold state `(best, prevBest)` over a plain list — L198's `foldFn`, structurally recursive
    on `List.cons` instead of `SnocList.snoc` (so it peels the FIRST house instead of the last;
    harmless, since max-non-adjacent-sum is symmetric under reading the row backwards). -/
def foldL : List Int → Int × Int
  | [] => (0, 0)
  | x :: xs => (imax (foldL xs).1 ((foldL xs).2 + x), (foldL xs).1)

/-- The answer for one linear row: the first fold component. -/
def robLine (l : List Int) : Int := (foldL l).1

/-! ## Specification of the linear row: split by "is the FIRST house taken?" (mirrors L198's
    `robF`/`robT`, front↔back swapped to match `foldL`'s recursion direction) -/

mutual
/-- `robF l v` — `v` is achievable WITHOUT taking `l`'s FIRST house (so it is just any achievable
    robbery of the rest, `xs`). -/
def robF : List Int → Int → Prop
  | [] => fun v => v = 0
  | _ :: xs => fun v => robF xs v ∨ robT xs v

/-- `robT l v` — `v` is achievable BY taking `l`'s FIRST house (so the rest, `xs`, must not take
    ITS OWN first house — a `robF`-selection of `xs`). -/
def robT : List Int → Int → Prop
  | [] => fun _ => False
  | x :: xs => fun v => ∃ v', robF xs v' ∧ v = v' + x
end

/-- `robSpec l v` — `v` is SOME achievable linear (non-wraparound) robbery of `l`. -/
def robSpec (l : List Int) (v : Int) : Prop := robF l v ∨ robT l v

/-! ## Invariants of `foldL`, proved TOGETHER by simultaneous induction (direct port of L198's
    `foldFn_dominates`/`foldFn_is_rob`) -/

/-- The fold dominates both layers of the spec. -/
theorem foldL_dominates : ∀ l : List Int,
    (∀ v, robSpec l v → v ≤ (foldL l).1) ∧ (∀ v, robF l v → v ≤ (foldL l).2) := by
  intro l; induction l with
  | nil =>
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show v ≤ (0 : Int)
      cases h with
      | inl h => have hv : v = 0 := h; omega
      | inr h => exact h.elim
    · have hv : v = 0 := h
      show v ≤ (0 : Int); omega
  | cons x xs ih =>
    obtain ⟨ihFst, ihSnd⟩ := ih
    refine ⟨fun v h => ?_, fun v h => ?_⟩
    · show v ≤ imax (foldL xs).1 ((foldL xs).2 + x)
      have h1 := imax_ge_left (foldL xs).1 ((foldL xs).2 + x)
      have h2 := imax_ge_right (foldL xs).1 ((foldL xs).2 + x)
      cases h with
      | inl h => have := ihFst v h; omega
      | inr h => obtain ⟨v', hv', hv⟩ := h; have := ihSnd v' hv'; omega
    · show v ≤ (foldL xs).1
      exact ihFst v h

/-- The fold is itself achievable in both layers. -/
theorem foldL_is_rob : ∀ l : List Int, robSpec l (foldL l).1 ∧ robF l (foldL l).2 := by
  intro l; induction l with
  | nil =>
    refine ⟨?_, ?_⟩
    · show robSpec ([] : List Int) 0; exact Or.inl rfl
    · show robF ([] : List Int) 0; rfl
  | cons x xs ih =>
    obtain ⟨ihFst, ihSnd⟩ := ih
    refine ⟨?_, ?_⟩
    · show robSpec (x :: xs) (imax (foldL xs).1 ((foldL xs).2 + x))
      cases imax_eq_or (foldL xs).1 ((foldL xs).2 + x) with
      | inl he => rw [he]; exact Or.inl ihFst
      | inr he => rw [he]; exact Or.inr ⟨(foldL xs).2, ihSnd, rfl⟩
    · show robF (x :: xs) (foldL xs).1
      exact ihFst

/-- **Correctness of the linear fold**: `robLine l` is an achievable row-robbery and dominates
    every achievable row-robbery. -/
theorem robLine_correct (l : List Int) :
    robSpec l (robLine l) ∧ ∀ v, robSpec l v → v ≤ robLine l :=
  ⟨(foldL_is_rob l).1, (foldL_dominates l).1⟩

/-! ## The circular gluing: `imax` of two rows dominates/achieves the disjunction of their specs
    (the one lemma needed to break the ring into two linear passes) -/

theorem imax_disj_correct (l1 l2 : List Int) :
    (robSpec l1 (imax (robLine l1) (robLine l2)) ∨ robSpec l2 (imax (robLine l1) (robLine l2)))
      ∧ ∀ v, (robSpec l1 v ∨ robSpec l2 v) → v ≤ imax (robLine l1) (robLine l2) := by
  refine ⟨?_, fun v h => ?_⟩
  · cases imax_eq_or (robLine l1) (robLine l2) with
    | inl he => rw [he]; exact Or.inl (robLine_correct l1).1
    | inr he => rw [he]; exact Or.inr (robLine_correct l2).1
  · have h1 := imax_ge_left (robLine l1) (robLine l2)
    have h2 := imax_ge_right (robLine l1) (robLine l2)
    cases h with
    | inl h => have := (robLine_correct l1).2 v h; omega
    | inr h => have := (robLine_correct l2).2 v h; omega

/-! ## The program: `rob-it-or-not` for a single house, `imax` of the two broken-ring rows
    otherwise -/

/-- The answer for a (nonempty) plain list of houses: `imax x 0` for a single house, otherwise the
    `imax` of the two linear passes that each drop one end of the ring. -/
def circAnswer : List Int → Int
  | [x] => imax x 0
  | l => imax (robLine l.dropLast) (robLine l.tail)

/-- The answer function on `SnocList`. -/
def solveFn (xs : SnocList Int Int) : Int := circAnswer (toList xs)

/-- **The allegory program**: LeetCode 213's solution as a morphism `Arr ⟶ ℤ` in `Rel(Set)`. -/
def solve : Arr ⟶ dZ := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-! ## Specification: the maximum achievable circular robbery -/

/-- `circSpecL l v` — `v` is achievable by a non-adjacent selection of `l` (read as a circle: the
    first and last positions are adjacent) that does not take both ends: for a single house,
    `rob-it-or-not`; otherwise, a linear robbery of `dropLast` or of `tail` (the argument in the
    header comment: avoiding both ends means missing the last house, so `⊆ dropLast`, or missing
    the first, so `⊆ tail`, and conversely). -/
def circSpecL : List Int → Int → Prop
  | [x] => fun v => v = x ∨ v = 0
  | l => fun v => robSpec l.dropLast v ∨ robSpec l.tail v

/-- The **specification** as a morphism `Arr ⟶ ℤ` in `Rel(Set)`. -/
def circSpec (xs : SnocList Int Int) (v : Int) : Prop := circSpecL (toList xs) v

def spec : Arr ⟶ dZ := fun xs v => circSpec xs v

/-! ## Correctness: `circAnswer` computes the maximum achievable circular robbery -/

theorem circAnswer_correct (l : List Int) :
    circSpecL l (circAnswer l) ∧ ∀ v, circSpecL l v → v ≤ circAnswer l := by
  match l with
  | [x] =>
    refine ⟨imax_eq_or x 0, fun v h => ?_⟩
    show v ≤ imax x 0
    have h1 := imax_ge_left x 0; have h2 := imax_ge_right x 0
    cases h with
    | inl h => omega
    | inr h => omega
  | [] => exact imax_disj_correct _ _
  | x :: y :: ys => exact imax_disj_correct _ _

/-- **Correctness of the allegory program**: `solve xs` is an achievable circular robbery and is
    `≤`-greatest among all achievable circular robberies. -/
theorem solve_correct (xs : SnocList Int Int) :
    circSpec xs (solveFn xs) ∧ ∀ v, circSpec xs v → v ≤ solveFn xs :=
  circAnswer_correct (toList xs)

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `solve` is exactly the morphism `Λ spec ≫ est D`
    for the `≤`-preference order `D w z := z ≤ w` — the greatest achievable circular robbery, not
    merely pointwise. Bridged from `solve_correct` (soundness + domination). -/
theorem solve_eq_est : solve = Λ spec ≫ est (fun w z : Int => z ≤ w) :=
  eq_Λ_comp_est _ (fun x y h1 h2 => Int.le_antisymm h2 h1) solveFn spec
    (fun xs => (solve_correct xs).1) (fun xs v hv => (solve_correct xs).2 v hv)

/-- **The program refines the specification**: every value `solve` returns is an achievable
    circular robbery. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs v h => ?_)
  have hv : v = solveFn xs := h
  rw [hv]; exact (solve_correct xs).1

/-! ## Running the program -/

example : solveFn (ofList 2 [3, 2]) = 3 := by decide
example : solveFn (ofList 1 [2, 3, 1]) = 4 := by decide
example : solveFn (ofList 1 [2, 3]) = 3 := by decide
example : solveFn (ofList 5 []) = 5 := by decide

end Freyd.Alg.RelSet.LC213
