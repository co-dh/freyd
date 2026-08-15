/-
  LeetCode 300 — Longest Increasing Subsequence — as an ALLEGORY PROGRAM.

  Problem: given a non-empty array of integers `x₀,…,x_{n-1}`, find the length of the longest
  STRICTLY increasing subsequence (elements need not be contiguous, but must keep their relative
  order and strictly increase in value).

  Same recipe as `leet/L53.lean` / `leet/L198.lean` (see `Freyd/leetcode.md`, skill S0/S1/S4):

  1. **Data** — the array is the initial algebra `SnocList ℤ ℤ` of `F X = ℤ + X × ℤ`
     (`AOP.A6_SnocList`); `wrap x` is a single-element array, `snoc xs p` appends an element.

  2. **Program** — the classic O(n²) DP: carry a `List (ℤ × ℕ)` of `(value, lisLenEndingThere)`
     pairs for every element seen so far, plus the running best.  For a new element `p`,
     `lisEnd records p := 1 + bestBelow records p` where `bestBelow` is the max recorded length
     among entries whose value is `< p` (`0` if none); the record `(p, lisEnd records p)` is
     appended and the running best is `nmax best (lisEnd records p)`.  We package it as a `Map`
     `solve : Arr ⟶ ℕ` in `Rel(Set)` and prove it *is* the catamorphism of that algebra followed
     by the second projection (`solve_eq_cata`).

  3. **Specification** — a two-layer relation in the L53/L198 style: `lastEnd xs p v k` — `v = p`
     and `k` is the length of a strictly increasing subsequence of `snoc xs p` that ends AT the
     new last element `p` (either `p` alone, or an achievable subsequence of `xs` ending at some
     value `< p`, extended by `p`).  `anyEnd xs v k` — `k` is the length of a strictly increasing
     subsequence of `xs` ending (ANYWHERE) at value `v`: either achievable within the prefix, or
     (when `xs = snoc xs' p`) achieved by `lastEnd xs' p`.  `isSubseqInc xs k := ∃ v, anyEnd xs v
     k` is the LeetCode spec: `k` is the length of SOME strictly increasing subsequence of `xs`.
     LeetCode 300 asks for its `≤`-maximum, `max (≤) · Λ isSubseqInc`.

  4. **Correctness** — `solve` computes exactly that maximum: it returns an achievable
     subsequence length (`solve_achievable`, giving `solve ⊑ spec`) and dominates every achievable
     subsequence length (`domination`).  Together (`solve_correct`) this is
     `solve = max (≤) · Λ isSubseqInc`, evaluated pointwise in the Set model.  The bridge between
     the DP fold's `records` list and the `anyEnd`/`lastEnd` spec is carried by two structural
     invariants: `records_sound` (every recorded pair is an achievable ending) and
     `records_complete` (every achievable ending is dominated by some recorded pair) — the
     records-carrying analogue of L53's `foldFn_fst_dominates`/`foldFn_fst_is_suffix`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import AOP.A7_4_Horner
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC300

open Freyd Freyd.Alg.RelSet.SL

/-! ## Nat `max` (mathlib-free, so we control the rewrite lemmas — copy of L53's `imax`,
    specialised to `Nat` lengths). -/

def nmax (a b : Nat) : Nat := if a ≤ b then b else a

theorem nmax_ge_left  (a b : Nat) : a ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_ge_right (a b : Nat) : b ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_eq_or (a b : Nat) : nmax a b = a ∨ nmax a b = b := by
  unfold nmax; split; exacts [Or.inr rfl, Or.inl rfl]

/-! ## Data: arrays as a non-empty snoc-list of integers -/

/-- The object of arrays in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = single element, `snoc xs p` =
    `xs` with a new final element `p`). -/
abbrev Arr : RelSet.{0} := dSL Int Int
/-- The object of natural numbers (subsequence lengths) in `Rel(Set)`. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## The program: O(n²) DP, state `(records, best)` where `records : List (value, lisLenEndingThere)` -/

/-- The best recorded length among entries whose value is strictly below `p` (`0` if none
    qualify). -/
def bestBelow : List (Int × Nat) → Int → Nat
  | [], _ => 0
  | (v, l) :: rest, p => if v < p then nmax l (bestBelow rest p) else bestBelow rest p

/-- The LIS length ending at a new element `p`, given the records seen so far. -/
def lisEnd (records : List (Int × Nat)) (p : Int) : Nat := 1 + bestBelow records p

/-- The fold algebra `[ x ↦ ([(x,1)], 1),  ((records,best),p) ↦
    (records ++ [(p, lisEnd records p)], nmax best (lisEnd records p)) ] : F(state) → state`. -/
def algFn : (Fobj Int Int (⟨List (Int × Nat) × Nat⟩ : RelSet.{0})).carrier
    → (List (Int × Nat) × Nat)
  | Sum.inl x => ([(x, 1)], 1)
  | Sum.inr (st, p) => (st.1 ++ [(p, lisEnd st.1 p)], nmax st.2 (lisEnd st.1 p))

/-- The algebra as a morphism (a `Map`) `F(state) ⟶ state` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨List (Int × Nat) × Nat⟩ : RelSet.{0})
    ⟶ (⟨List (Int × Nat) × Nat⟩ : RelSet.{0}) := graph algFn

/-- The concrete fold (structural recursion), returning `(records, best)`. -/
def foldFn : SnocList Int Int → List (Int × Nat) × Nat
  | SnocList.wrap x => ([(x, 1)], 1)
  | SnocList.snoc xs p => ((foldFn xs).1 ++ [(p, lisEnd (foldFn xs).1 p)],
      nmax (foldFn xs).2 (lisEnd (foldFn xs).1 p))

/-- The answer: the second fold component (the running best LIS length). -/
def solveFn (xs : SnocList Int Int) : Nat := (foldFn xs).2

/-- **The allegory program**: LeetCode 300's solution as a morphism `Arr ⟶ ℕ` in `Rel(Set)`. -/
def solve : Arr ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Int Int) (r : List (Int × Nat) × Nat),
    cataFold alg xs r ↔ r = foldFn xs := by
  intro xs; induction xs with
  | wrap x => intro r; exact Iff.rfl
  | snoc xs p ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨foldFn xs, (ih (foldFn xs)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · snd`, a fold followed by the
    projection onto `best`. -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (Prod.snd : List (Int × Nat) × Nat → Nat) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## Specification: the maximum achievable strictly-increasing-subsequence length -/

/-- `anyEnd xs v k` — `k` is the length of a strictly increasing subsequence of `xs` ending
    (ANYWHERE, at any position) at value `v`: achievable within a prefix, or (in the `snoc`
    case) freshly achieved by ending AT the new last element `p` — either `p` alone (`k = 1`), or
    an achievable ending of the prefix at a smaller value, extended by `p`.  (This inlines what
    the separate "ending here" layer would compute; `lastEnd`, defined right below on top of
    `anyEnd`, names that layer explicitly and `anyEnd_snoc` records the two-layer reading.) -/
def anyEnd : SnocList Int Int → Int → Nat → Prop
  | SnocList.wrap x => fun v k => v = x ∧ k = 1
  | SnocList.snoc xs p => fun v k =>
      anyEnd xs v k ∨ (v = p ∧ (k = 1 ∨ ∃ v' k', anyEnd xs v' k' ∧ v' < p ∧ k = k' + 1))

/-- `lastEnd xs p v k` — `v = p` and `k` is the length of a strictly increasing subsequence of
    `snoc xs p` ending AT the new last element `p` (the "ending here" layer, defined ON TOP of
    the already-defined `anyEnd`, in the L53 style). -/
def lastEnd (xs : SnocList Int Int) (p v : Int) (k : Nat) : Prop :=
  v = p ∧ (k = 1 ∨ ∃ v' k', anyEnd xs v' k' ∧ v' < p ∧ k = k' + 1)

/-- The `snoc` case of `anyEnd` is exactly "in the prefix, or ending here" — the two-layer
    reading. -/
theorem anyEnd_snoc (xs : SnocList Int Int) (p v : Int) (k : Nat) :
    anyEnd (SnocList.snoc xs p) v k ↔ anyEnd xs v k ∨ lastEnd xs p v k := Iff.rfl

/-- `isSubseqInc xs k` — `k` is the length of SOME strictly increasing subsequence of `xs`
    (ending anywhere, at any achievable value). -/
def isSubseqInc (xs : SnocList Int Int) (k : Nat) : Prop := ∃ v, anyEnd xs v k

/-- The **specification** as a morphism `Arr ⟶ ℕ` in `Rel(Set)`: the relation of achievable
    increasing-subsequence lengths.  LeetCode 300 asks for its `≤`-maximum, `max (≤) · Λ spec`. -/
def spec : Arr ⟶ dNat := fun xs k => isSubseqInc xs k

/-! ## List-level facts about `bestBelow` (independent of the `SnocList` recursion) -/

/-- Every recorded entry with a value `< p` is a lower bound of `bestBelow`. -/
theorem bestBelow_mem_le : ∀ (records : List (Int × Nat)) (p v : Int) (l : Nat),
    (v, l) ∈ records → v < p → l ≤ bestBelow records p := by
  intro records
  induction records with
  | nil => intro p v l hmem _; cases hmem
  | cons hd rest ih =>
    intro p v l hmem hvp
    obtain ⟨v0, l0⟩ := hd
    unfold bestBelow
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨hv, hl⟩ := Prod.mk.injEq .. |>.mp heq
      have hvp0 : v0 < p := by rw [hv] at hvp; exact hvp
      rw [if_pos hvp0]
      have h1 := nmax_ge_left l0 (bestBelow rest p)
      omega
    · have hrest := ih p v l hmem' hvp
      split
      · have h2 := nmax_ge_right l0 (bestBelow rest p)
        omega
      · exact hrest

/-- `bestBelow` is either `0` (nothing qualifies) or exactly achieved by some recorded entry with
    a value `< p`. -/
theorem bestBelow_achieved : ∀ (records : List (Int × Nat)) (p : Int),
    bestBelow records p = 0 ∨ ∃ v l, (v, l) ∈ records ∧ v < p ∧ bestBelow records p = l := by
  intro records
  induction records with
  | nil => intro p; exact Or.inl rfl
  | cons hd rest ih =>
    intro p
    obtain ⟨v0, l0⟩ := hd
    unfold bestBelow
    split
    · rename_i hvp
      rcases nmax_eq_or l0 (bestBelow rest p) with he | he
      · exact Or.inr ⟨v0, l0, List.mem_cons_self .., hvp, he⟩
      · rcases ih p with h0 | ⟨v', l', hmem, hv'p, heq⟩
        · exact Or.inl (he.trans h0)
        · exact Or.inr ⟨v', l', List.mem_cons_of_mem _ hmem, hv'p, he.trans heq⟩
    · rcases ih p with h0 | ⟨v', l', hmem, hv'p, heq⟩
      · exact Or.inl h0
      · exact Or.inr ⟨v', l', List.mem_cons_of_mem _ hmem, hv'p, heq⟩

/-! ## Invariants bridging `foldFn`'s records to the spec -/

/-- Every recorded pair is an achievable ending: `(v,l) ∈ records(xs) → anyEnd xs v l`. -/
theorem records_sound : ∀ (xs : SnocList Int Int) (v : Int) (l : Nat),
    (v, l) ∈ (foldFn xs).1 → anyEnd xs v l := by
  intro xs
  induction xs with
  | wrap x =>
    intro v l hmem
    have heq : (v, l) = (x, (1 : Nat)) := List.mem_singleton.mp hmem
    obtain ⟨hv, hl⟩ := Prod.mk.injEq .. |>.mp heq
    exact ⟨hv, hl⟩
  | snoc xs p ih =>
    intro v l hmem
    show anyEnd (SnocList.snoc xs p) v l
    rw [anyEnd_snoc]
    rcases List.mem_append.mp hmem with hmem' | hmem'
    · exact Or.inl (ih v l hmem')
    · have heq : (v, l) = (p, lisEnd (foldFn xs).1 p) := List.mem_singleton.mp hmem'
      obtain ⟨hv, hl⟩ := Prod.mk.injEq .. |>.mp heq
      refine Or.inr ⟨hv, ?_⟩
      rw [hl]
      unfold lisEnd
      rcases bestBelow_achieved (foldFn xs).1 p with h0 | ⟨v', l', hmem'', hv'p, heq'⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨v', l', ih v' l' hmem'', hv'p, by omega⟩

/-- Every achievable ending is dominated by some recorded pair (with the SAME value, and a
    length no smaller): `anyEnd xs v k → ∃ l, (v,l) ∈ records(xs) ∧ k ≤ l`. -/
theorem records_complete : ∀ (xs : SnocList Int Int) (v : Int) (k : Nat),
    anyEnd xs v k → ∃ l, (v, l) ∈ (foldFn xs).1 ∧ k ≤ l := by
  intro xs
  induction xs with
  | wrap x =>
    intro v k h
    obtain ⟨hv, hk⟩ := h
    exact ⟨1, by rw [hv]; exact List.mem_singleton.mpr rfl, by omega⟩
  | snoc xs p ih =>
    intro v k h
    rw [anyEnd_snoc] at h
    rcases h with h | ⟨hv, hcase⟩
    · obtain ⟨l, hmem, hk⟩ := ih v k h
      exact ⟨l, List.mem_append.mpr (Or.inl hmem), hk⟩
    · refine ⟨lisEnd (foldFn xs).1 p, ?_, ?_⟩
      · rw [hv]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · unfold lisEnd
        rcases hcase with hk1 | ⟨v', k', h', hv'p, hk⟩
        · omega
        · obtain ⟨l', hmem', hkl'⟩ := ih v' k' h'
          have hle : l' ≤ bestBelow (foldFn xs).1 p := bestBelow_mem_le (foldFn xs).1 p v' l' hmem' hv'p
          omega

/-- The running best is always the `l`-component of SOME recorded pair. -/
theorem best_is_record : ∀ xs : SnocList Int Int, ∃ v, (v, (foldFn xs).2) ∈ (foldFn xs).1 := by
  intro xs
  induction xs with
  | wrap x => exact ⟨x, List.mem_singleton.mpr rfl⟩
  | snoc xs p ih =>
    show ∃ v, (v, nmax (foldFn xs).2 (lisEnd (foldFn xs).1 p)) ∈
      (foldFn xs).1 ++ [(p, lisEnd (foldFn xs).1 p)]
    rcases nmax_eq_or (foldFn xs).2 (lisEnd (foldFn xs).1 p) with he | he
    · obtain ⟨v, hv⟩ := ih
      exact ⟨v, by rw [he]; exact List.mem_append.mpr (Or.inl hv)⟩
    · exact ⟨p, by rw [he]; exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))⟩

/-- Every recorded pair's length is dominated by the running best. -/
theorem best_ge_record : ∀ (xs : SnocList Int Int) (v : Int) (l : Nat),
    (v, l) ∈ (foldFn xs).1 → l ≤ (foldFn xs).2 := by
  intro xs
  induction xs with
  | wrap x =>
    intro v l hmem
    have heq : (v, l) = (x, (1 : Nat)) := List.mem_singleton.mp hmem
    obtain ⟨_, hl⟩ := Prod.mk.injEq .. |>.mp heq
    show l ≤ 1
    omega
  | snoc xs p ih =>
    intro v l hmem
    show l ≤ nmax (foldFn xs).2 (lisEnd (foldFn xs).1 p)
    rcases List.mem_append.mp hmem with hmem' | hmem'
    · have h1 := ih v l hmem'
      have h2 := nmax_ge_left (foldFn xs).2 (lisEnd (foldFn xs).1 p)
      omega
    · have heq : (v, l) = (p, lisEnd (foldFn xs).1 p) := List.mem_singleton.mp hmem'
      obtain ⟨_, hl⟩ := Prod.mk.injEq .. |>.mp heq
      have h2 := nmax_ge_right (foldFn xs).2 (lisEnd (foldFn xs).1 p)
      omega

/-! ## Correctness: `solve` computes the maximum achievable increasing-subsequence length -/

/-- `solve`'s output is an achievable increasing-subsequence length — hence `solve ⊑ spec`. -/
theorem solve_achievable : ∀ xs, isSubseqInc xs (solveFn xs) := by
  intro xs
  obtain ⟨v, hv⟩ := best_is_record xs
  exact ⟨v, records_sound xs v (foldFn xs).2 hv⟩

/-- `solve` dominates every achievable increasing-subsequence length. -/
theorem domination : ∀ (xs : SnocList Int Int) (k : Nat), isSubseqInc xs k → k ≤ solveFn xs := by
  intro xs k h
  obtain ⟨v, hv⟩ := h
  obtain ⟨l, hmem, hk⟩ := records_complete xs v k hv
  have hl := best_ge_record xs v l hmem
  show k ≤ (foldFn xs).2
  omega

/-- **The program refines the specification**: every value `solve` returns is an achievable
    increasing-subsequence length. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs k h => ?_)
  have hk : k = solveFn xs := h
  rw [hk]; exact solve_achievable xs

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ isSubseqInc`, pointwise in
    `Rel(Set)`): `solve xs` is an achievable increasing-subsequence length and is `≤`-greatest
    among all achievable increasing-subsequence lengths. -/
theorem solve_correct (xs : SnocList Int Int) :
    isSubseqInc xs (solveFn xs) ∧ ∀ k, isSubseqInc xs k → k ≤ solveFn xs :=
  ⟨solve_achievable xs, domination xs⟩

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `solve` is exactly the morphism `A spec ≫ maxRel D`
    for the `≤`-preference order `D w z := z ≤ w` — not merely pointwise. Bridged from `solve_correct`. -/
theorem solve_eq_maxRel : solve = A spec ≫ maxRel (fun w z : Nat => z ≤ w) :=
  eq_Λ_comp_maxRel _ (fun x y h1 h2 => Nat.le_antisymm h2 h1) solveFn spec
    (fun xs => (solve_correct xs).1) (fun xs v hv => (solve_correct xs).2 v hv)

/-! ## Running the program -/

/-- Build an array from a first element and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 10 [9, 2, 5, 3, 7, 101, 18]) = 4 := by decide
example : solveFn (ofList 0 []) = 1 := by decide
example : solveFn (ofList 7 [7, 7]) = 1 := by decide
example : solveFn (ofList 1 [2, 3]) = 3 := by decide

end Freyd.Alg.RelSet.LC300
