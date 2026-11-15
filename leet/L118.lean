/-
  LeetCode 118 — Pascal's Triangle — as an ALLEGORY PROGRAM.

  Problem: given `numRows`, return the first `numRows` rows of Pascal's triangle. Row `0` is
  `[1]`; each next row starts and ends with `1`, and every interior entry is the sum of the two
  entries above it.

  Same recipe as `leet/L62.lean`/`Freyd/leetcode.md` S10: a DP row is folded down, one
  transition per row, structural recursion on the ROW COUNT (not on a shrinking pair of
  independently-recursive indices), so no well-founded-recursion trap. Unlike `L62` (which folds
  a SCALAR/single row and keeps only the LAST value), `L118` must return every intermediate row,
  so the state carried through the fold is a `List (List Nat)` accumulator, plain `List Nat`
  rows (no `SnocList` engine needed — `nextRow` is a single `zipWith` pass, not a left-to-right
  scan).

  1. **Program** — `nextRow r := zipWith (·+·) (0 :: r) (r ++ [0])`: shifting `r` by one position
     both ways and adding lines up each entry with its two "parents" (`0` padding supplies the
     boundary `1`s for free — `0 + head r = head r` and `last r + 0 = last r`). `pascalFn n`
     iterates `nextRow` starting from `[1]`, collecting each row, `n` times.

  2. **Spec** — `binom : Nat → Nat → Nat`, the textbook Pascal recurrence (`binom n 0 = 1`,
     `binom 0 (k+1) = 0`, `binom (n+1) (k+1) = binom n k + binom n (k+1)`) — the definition of
     "the entries of Pascal's triangle" independent of any fold. `rowOf i := (range (i+1)).map
     (binom i)` is row `i` read off directly from `binom`.

  3. **Correctness** — the crux `nextRow_rowOf : nextRow (rowOf i) = rowOf (i+1)` says the
     `zipWith` step REALIZES the binomial recurrence: reading off both sides index-by-index
     (`List.ext_getElem?`) reduces every entry to exactly `binom (i+1) (k+1) = binom i k +
     binom i (k+1)`, by definition. Threading this down the fold (`buildRows_getElem?`) gives the
     headline `pascal_correct`: row `i` of `pascalFn n` (for `i < n`) is column-for-column exactly
     `binom i`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

namespace Freyd.Alg.RelSet.LC118

open Freyd

/-! ## Program: one `zipWith` pass per row, iterated `n` times, collecting every row -/

/-- One Pascal's-triangle row transition: adding a row to itself shifted one place each way.
    `0`-padding on both ends supplies the boundary `1`s (`0 + r.head = r.head`,
    `r.getLast + 0 = r.getLast`) with no special-casing of the ends. -/
def nextRow (r : List Nat) : List Nat := List.zipWith (· + ·) (0 :: r) (r ++ [0])

/-- Build `n` rows by iterating `nextRow` starting from the CURRENT row `r`, collecting each row
    visited. Structural recursion on `n` (the row count) — `nextRow` is a single pass, so there is
    no second independently-decreasing argument (contrast the well-founded-recursion trap of a
    genuine two-argument recurrence, `leet/L62.lean` S10). -/
def buildRows : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | (n + 1), r => r :: buildRows n (nextRow r)

/-- **The program**: the first `n` rows of Pascal's triangle, row `0` = `[1]`. -/
def pascalFn (n : Nat) : List (List Nat) := buildRows n [1]

/-! ## The allegory program -/

abbrev dNat  : RelSet.{0} := ⟨Nat⟩
abbrev dRows : RelSet.{0} := ⟨List (List Nat)⟩

/-- **The allegory program**: LeetCode 118's solution as a morphism `ℕ ⟶ List (List ℕ)` in
    `Rel(Set)`. -/
def solve : dNat ⟶ dRows := graph pascalFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map pascalFn

/-! ## Spec: `binom`, the textbook Pascal recurrence, independent of any fold -/

/-- The binomial coefficients via the Pascal recurrence: `binom n 0 = 1` (top of every row),
    `binom 0 (k+1) = 0` (nothing beyond the single entry of row `0`), and the interior sum rule.
    Structural recursion on `n` — both recursive occurrences in the last clause use the
    predecessor `n`, so (unlike `L62`'s two-argument `paths`) this is plain structural
    recursion, not well-founded. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, (_ + 1) => 0
  | (n + 1), (k + 1) => binom n k + binom n (k + 1)

/-- **Out-of-range entries vanish**: `binom n k = 0` once `k` exceeds `n` — needed to make the
    triangle's boundary (`binom i (i+1) = 0`, "nothing past the last entry of row `i`") an
    instance of the general recurrence rather than a separate case. Structural recursion on `n`,
    mirroring `binom` itself. -/
theorem binom_eq_zero_of_lt : ∀ n k, n < k → binom n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, (_ + 1), _ => rfl
  | (_ + 1), 0, h => absurd h (by omega)
  | (n + 1), (k + 1), h => by
      show binom n k + binom n (k + 1) = 0
      rw [binom_eq_zero_of_lt n k (by omega), binom_eq_zero_of_lt n (k + 1) (by omega)]

/-- **Column `0` is always `1`** — the top of every row. Proved by an explicit case split on `n`
    (not `rfl` at a bare variable `n`): `binom` is compiled by STRUCTURAL RECURSION ON THE FIRST
    ARGUMENT, so even a "wildcard-first-argument" defining clause like `binom _ 0 = 1` only
    unfolds definitionally once the first argument is syntactically `0`/`_+1` — `binom i 0` for an
    ABSTRACT `i` is stuck (mirrors `leet/L62.lean` S10's well-founded-recursion trap, but here the
    recursion genuinely IS structural; the trap is that a clause LOOKING argument-independent still
    routes through the recursive argument). -/
theorem binom_col0 : ∀ n, binom n 0 = 1
  | 0 => rfl
  | (_ + 1) => rfl

/-- Row `i` of Pascal's triangle, read directly off `binom` (independent of `nextRow`/`pascalFn`):
    the `i+1` entries `binom i 0, …, binom i i`. -/
def rowOf (i : Nat) : List Nat := (List.range (i + 1)).map (binom i)

theorem rowOf_length (i : Nat) : (rowOf i).length = i + 1 := by
  unfold rowOf; simp

/-- Row `i`'s entries, indexed: in range (`k ≤ i`) it is `binom i k`, out of range it is absent. -/
theorem rowOf_getElem? (i k : Nat) :
    (rowOf i)[k]? = if k ≤ i then some (binom i k) else none := by
  unfold rowOf
  rw [List.getElem?_map]
  by_cases h : k ≤ i
  · have hlt : k < (List.range (i + 1)).length := by simp; omega
    rw [List.getElem?_eq_getElem hlt, List.getElem_range hlt, if_pos h]; rfl
  · have hge : (List.range (i + 1)).length ≤ k := by simp; omega
    rw [List.getElem?_eq_none hge, if_neg h]; rfl

/-! ## The crux: `nextRow` REALIZES the binomial recurrence -/

/-- **Crux lemma**: `nextRow` applied to row `i` (read off `binom`) produces exactly row `i+1` —
    the `zipWith` shift-and-add step IS the Pascal recurrence. Proved index-by-index
    (`List.ext_getElem?`); every entry reduces to `binom (i+1) (k+1) = binom i k + binom i (k+1)`
    by `binom`'s own defining equation, with `binom_eq_zero_of_lt` supplying the boundary case
    (top/bottom `1`s coming from the `0`-padding, the last interior entry's right parent vanishing
    past the end of row `i`). -/
theorem nextRow_rowOf (i : Nat) : nextRow (rowOf i) = rowOf (i + 1) := by
  apply List.ext_getElem?
  intro k
  show (List.zipWith (· + ·) (0 :: rowOf i) (rowOf i ++ [0]))[k]? = (rowOf (i + 1))[k]?
  rw [List.getElem?_zipWith, rowOf_getElem? (i + 1) k]
  cases k with
  | zero =>
    have hb : (rowOf i ++ [0])[0]? = some 1 := by
      rw [List.getElem?_append_left (by rw [rowOf_length]; omega), rowOf_getElem? i 0]
      simp [binom_col0]
    rw [List.getElem?_cons_zero, hb, if_pos (by omega : (0:Nat) ≤ i + 1)]
    rfl
  | succ j =>
    rw [List.getElem?_cons_succ, rowOf_getElem? i j]
    rcases Nat.lt_trichotomy j i with hj | hj | hj
    · -- interior: j < i, so k = j+1 ≤ i.
      have hb : (rowOf i ++ [0])[j + 1]? = some (binom i (j + 1)) := by
        rw [List.getElem?_append_left (by rw [rowOf_length]; omega), rowOf_getElem? i (j + 1)]
        simp; omega
      rw [if_pos (by omega : j ≤ i), hb, if_pos (by omega : j + 1 ≤ i + 1)]
      show some (binom i j + binom i (j + 1)) = some (binom (i + 1) (j + 1))
      rfl
    · -- right boundary: j = i, k = i+1, right parent falls off the end of row `i` (padding `0`).
      -- `rw` (not `subst`) so `i` — used by `hb`/`rowOf_length` below — stays in context.
      rw [hj]
      have hb : (rowOf i ++ [0])[i + 1]? = some 0 := by
        rw [List.getElem?_append_right (Nat.le_of_eq (rowOf_length i)), rowOf_length]
        simp
      rw [if_pos (Nat.le_refl i), hb, if_pos (Nat.le_refl (i + 1))]
      show some (binom i i + 0) = some (binom (i + 1) (i + 1))
      rw [Nat.add_zero, show binom (i + 1) (i + 1) = binom i i + binom i (i + 1) from rfl,
        binom_eq_zero_of_lt i (i + 1) (by omega), Nat.add_zero]
    · -- past the end of row `i+1`: k = j+1 > i+1, both sides absent.
      rw [if_neg (by omega : ¬ j ≤ i), if_neg (by omega : ¬ j + 1 ≤ i + 1)]

/-! ## Threading the crux down the fold -/

/-- Structural recursion on `t`: the fold collects exactly `t` rows. -/
theorem buildRows_length : ∀ t (r : List Nat), (buildRows t r).length = t
  | 0, _ => rfl
  | (t + 1), r => by
      show (r :: buildRows t (nextRow r)).length = t + 1
      rw [List.length_cons, buildRows_length t (nextRow r)]

/-- **`buildRows` computes exactly the `binom`-rows**: starting the fold from row `m` (`= rowOf m`
    for the initial call, `m = 0`), the `i`-th collected row (for `i < t`) is `rowOf (m + i)`.
    Structural induction on `t` (the fuel/row-count), reusing `nextRow_rowOf` at each step — the
    fold-vs-spec equality is carried the same way `L62`'s `rowAt_eq` carries a single row down the
    grid, generalized from a bare scalar to a whole per-index formula (the `L238` S23 move). -/
theorem buildRows_getElem? : ∀ t m i, i < t → (buildRows t (rowOf m))[i]? = some (rowOf (m + i))
  | (t + 1), m, 0, _ => by
      show (rowOf m :: buildRows t (nextRow (rowOf m)))[0]? = some (rowOf (m + 0))
      rw [List.getElem?_cons_zero, Nat.add_zero]
  | (t + 1), m, (i + 1), hi => by
      show (rowOf m :: buildRows t (nextRow (rowOf m)))[i + 1]? = some (rowOf (m + (i + 1)))
      rw [List.getElem?_cons_succ, nextRow_rowOf, buildRows_getElem? t (m + 1) i (by omega),
        show m + 1 + i = m + (i + 1) from by omega]

/-- Row `0` of the fold's seed `[1]` matches `rowOf 0` (`binom 0 0 = 1`). -/
theorem rowOf_zero : rowOf 0 = [1] := rfl

/-- **`pascalFn` computes exactly the `binom`-rows**: row `i` (for `i < n`) is `rowOf i`. -/
theorem pascalFn_getElem? (n i : Nat) (hi : i < n) : (pascalFn n)[i]? = some (rowOf i) := by
  show (buildRows n [1])[i]? = some (rowOf i)
  rw [← rowOf_zero, buildRows_getElem? n 0 i hi, Nat.zero_add]

/-- The number of rows produced is exactly `numRows`. -/
theorem pascalFn_length (n : Nat) : (pascalFn n).length = n := buildRows_length n [1]

/-- **Headline correctness**: for every row index `i < n` and every column `k`, entry `(i,k)` of
    `pascalFn n` is exactly the binomial coefficient `binom i k` if `k ≤ i`, and absent otherwise —
    the honest "Pascal's triangle" content (`binom`'s Pascal recurrence), not a restatement of the
    program. -/
theorem pascal_correct (n : Nat) : ∀ i < n, ∀ k,
    (pascalFn n)[i]?.bind (·[k]?) = (if k ≤ i then some (binom i k) else none) := by
  intro i hi k
  rw [pascalFn_getElem? n i hi, Option.bind_some, rowOf_getElem?]

/-! ## The morphism-equation headline (row spec pins the output) -/

/-- **The specification** as a morphism `ℕ ⟶ List (List ℕ)`: `out` has exactly `n` rows and its
    `i`-th row (for `i < n`) is `rowOf i` (the `binom`-row), stated independently of the fold
    `pascalFn`.  Row indices and lengths together pin `out` uniquely (`List.ext_getElem?`). -/
def spec : dNat ⟶ dRows :=
  fun n out => out.length = n ∧ (∀ i, i < n → out[i]? = some (rowOf i))

/-- **The allegory-program headline**: `solve = spec` as morphisms in `Rel(Set)` — the row-building
    fold is exactly the `binom`-triangle spec, pinned index-by-index, not merely pointwise. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro n out
  show (out = pascalFn n) ↔ (out.length = n ∧ ∀ i, i < n → out[i]? = some (rowOf i))
  constructor
  · intro h; rw [h]; exact ⟨pascalFn_length n, fun i hi => pascalFn_getElem? n i hi⟩
  · rintro ⟨hlen, hget⟩
    apply List.ext_getElem?
    intro k
    by_cases hk : k < n
    · rw [hget k hk, pascalFn_getElem? n k hk]
    · rw [List.getElem?_eq_none (by rw [hlen]; omega), List.getElem?_eq_none (by rw [pascalFn_length]; omega)]

/-! ## Running the program -/

example : pascalFn 5 = [[1], [1, 1], [1, 2, 1], [1, 3, 3, 1], [1, 4, 6, 4, 1]] := by decide
example : pascalFn 1 = [[1]] := by decide

end Freyd.Alg.RelSet.LC118
