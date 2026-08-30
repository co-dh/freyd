/-
  LeetCode 3 — Longest Substring Without Repeating Characters — as an ALLEGORY PROGRAM.

  Problem: given a non-empty string `x₀,…,x_{n-1}` of characters, find the length of the longest
  contiguous substring all of whose characters are pairwise distinct.

  Same recipe as `leet/L53.lean` / `leet/L300.lean` (see `Freyd/leetcode.md`, skill S0/S1):

  1. **Data** — the string is the initial algebra `SnocList ℤ ℤ` of `F X = ℤ + X × ℤ`
     (`AOP.A6_SnocList`, characters encoded as `Int`); `wrap x` is a single-character string,
     `snoc xs c` appends a character.

  2. **Program** — a left-to-right SLIDING-WINDOW scan.  Rather than tracking the window as a pair
     of positions `(windowStart, index)` plus a position map, the fold carries the window's
     CONTENT: `seen : List Int`, the characters currently in the window, most-recent-first.  On a
     new character `c`, `survive seen c` drops `c` and everything OLDER than it from `seen` (i.e.
     slides `windowStart` past the previous occurrence of `c`, or leaves `seen` untouched if `c`
     is not currently in the window), then `c` is prepended.  This is the same last-seen-index
     sliding window, phrased on the window's content instead of on positions.  `best` is the
     running max of the window length.  We package it as a `Map` `solve : Str ⟶ ℕ` in `Rel(Set)`
     and prove it *is* the catamorphism of that algebra followed by the second projection
     (`solve_eq_cata`).

  3. **Specification** — a two-layer relation in the L53/L300 style: `DistinctSuffix xs k` — `k` is
     (at most) the length of `xs` and the last `k` characters of `xs` are pairwise distinct (via
     the position-free extraction `suffixList xs k`, capped structurally, paired with the explicit
     bound `k ≤ len xs`).  `DistinctAt xs k` — `k` is the length of SOME contiguous substring of
     `xs`: achievable within a strict prefix, or (in the `snoc` case) a distinct suffix of the
     whole `snoc xs c`.  LeetCode 3 asks for its `≤`-maximum, `max (≤) · Λ DistinctAt`.

  4. **Correctness** — `solve` computes exactly that maximum: it returns an achievable substring
     length (`solve_achievable`, giving `solve ⊑ spec`) and dominates every achievable substring
     length (`domination_all`).  Together (`solve_correct`) this is `solve = max (≤) · Λ DistinctAt`.
     The bridge between the fold's `seen` list and the structural spec is carried by:
     `foldFn_seen_eq_suffixList` (`seen` IS the length-`seen.length` suffix of `xs`),
     `foldFn_seen_distinct` (`seen` has no repeats), and `survive_length_ge_of_not_mem_take` (the
     crux optimality fact: sliding the window only as far as the previous occurrence of `c`, no
     further, never over-shrinks — any distinct window not containing `c` survives intact).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import AOP.A7_4_Horner   -- `eq_Λ_comp_est`: the `max (≤)·Λ spec` morphism-equation bridge
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC3

open Freyd Freyd.Alg.RelSet.SL

/-! ## Nat `max` (mathlib-free, so we control the rewrite lemmas — copy of L300's `nmax`). -/

def nmax (a b : Nat) : Nat := if a ≤ b then b else a

theorem nmax_ge_left  (a b : Nat) : a ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_ge_right (a b : Nat) : b ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_eq_or (a b : Nat) : nmax a b = a ∨ nmax a b = b := by
  unfold nmax
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Data: strings as a non-empty snoc-list of integers (characters) -/

/-- The object of strings in `Rel(Set)` — `SnocList ℤ ℤ` (`wrap x` = single character, `snoc xs c`
    = `xs` with a new final character `c`). -/
abbrev Str : RelSet.{0} := dSL Int Int
/-- The object of natural numbers (substring lengths) in `Rel(Set)`. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## The program: a sliding window carried as `(seen, best)`, `seen` = current window's content -/

/-- `survive seen c` — drop `c` and everything OLDER than it (i.e. to its right, since `seen` is
    most-recent-first) from the window's content `seen`; `seen` unchanged if `c` isn't present.
    This is `windowStart := p + 1` phrased on content instead of on positions. -/
def survive : List Int → Int → List Int
  | [], _ => []
  | d :: rest, c => if d = c then [] else d :: survive rest c

/-- Slide the window to admit a new character `c`: shrink `seen` past any prior occurrence of `c`,
    then prepend `c`. -/
def stepSeen (seen : List Int) (c : Int) : List Int := c :: survive seen c

/-- The fold algebra `[ x ↦ ([x],1),  ((seen,best),c) ↦ (stepSeen seen c, max best (stepSeen seen
    c).length) ] : F(state) → state`. -/
def algFn : (Fobj Int Int (⟨List Int × Nat⟩ : RelSet.{0})).carrier → (List Int × Nat)
  | Sum.inl x => ([x], 1)
  | Sum.inr (st, c) => (stepSeen st.1 c, nmax st.2 (stepSeen st.1 c).length)

/-- The algebra as a morphism (a `Map`) `F(state) ⟶ state` in `Rel(Set)`. -/
def alg : Fobj Int Int (⟨List Int × Nat⟩ : RelSet.{0}) ⟶ (⟨List Int × Nat⟩ : RelSet.{0}) :=
  graph algFn

/-- The concrete fold (structural recursion): `seen` = the current window's characters,
    most-recent-first (always distinct, `foldFn_seen_distinct`); `best` = longest window seen so
    far. -/
def foldFn : SnocList Int Int → List Int × Nat
  | SnocList.wrap x => ([x], 1)
  | SnocList.snoc xs c =>
    let seen' := stepSeen (foldFn xs).1 c
    (seen', nmax (foldFn xs).2 seen'.length)

/-- The answer: the running best window length. -/
def solveFn (xs : SnocList Int Int) : Nat := (foldFn xs).2

/-- **The allegory program**: LeetCode 3's solution as a morphism `Str ⟶ ℕ` in `Rel(Set)`. -/
def solve : Str ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- The relational catamorphism of the (function) algebra `alg` is the graph of the concrete fold —
    the abstract fold in `Rel(Set)` and the structural fold agree. -/
theorem cataFold_alg : ∀ (xs : SnocList Int Int) (r : List Int × Nat),
    cataFold alg xs r ↔ r = foldFn xs := by
  intro xs; induction xs with
  | wrap x => intro r; exact Iff.rfl
  | snoc xs c ih =>
    intro r
    simp only [cataFold_snoc]
    constructor
    · rintro ⟨r', hr', hfr⟩
      rw [ih r'] at hr'; subst hr'; exact hfr
    · intro h; exact ⟨foldFn xs, (ih (foldFn xs)).mpr rfl, h⟩

/-- **The program is a catamorphism**: `solve = ⦇[base, step]⦈ · snd`, a fold followed by the
    projection onto `best`. -/
theorem solve_eq_cata : solve = cataR alg ≫ graph (Prod.snd : List Int × Nat → Nat) := by
  apply hom_ext; intro xs v
  simp only [solve, graph, comp_apply, cataR]
  constructor
  · intro hv; exact ⟨foldFn xs, (cataFold_alg xs (foldFn xs)).mpr rfl, hv⟩
  · rintro ⟨st, hst, hv⟩; rw [(cataFold_alg xs st).mp hst] at hv; exact hv

/-! ## List-level facts about `survive` (independent of the `SnocList` recursion) -/

theorem survive_length_le (l : List Int) (c : Int) : (survive l c).length ≤ l.length := by
  induction l with
  | nil => simp [survive]
  | cons d rest ih =>
    unfold survive
    split
    · simp
    · simp only [List.length_cons]; omega

theorem survive_subset (l : List Int) (c x : Int) (h : x ∈ survive l c) : x ∈ l := by
  induction l with
  | nil => simp [survive] at h
  | cons d rest ih =>
    unfold survive at h
    split at h
    · exact absurd h (by simp)
    · rcases List.mem_cons.mp h with h1 | h1
      · exact List.mem_cons.mpr (Or.inl h1)
      · exact List.mem_cons.mpr (Or.inr (ih h1))

theorem survive_not_mem (l : List Int) (c : Int) : c ∉ survive l c := by
  induction l with
  | nil => simp [survive]
  | cons d rest ih =>
    unfold survive
    split
    · simp
    · rename_i hne
      intro h
      rcases List.mem_cons.mp h with h1 | h1
      · exact hne h1.symm
      · exact ih h1

theorem survive_eq_take_length (l : List Int) (c : Int) :
    survive l c = l.take (survive l c).length := by
  induction l with
  | nil => simp [survive]
  | cons d rest ih =>
    unfold survive
    split
    · rfl
    · rename_i hne
      simp only [List.length_cons, List.take_succ_cons]
      rw [← ih]

/-- The window never has a repeated character (a hand-rolled `List.Nodup`, mathlib-free). -/
def Distinct : List Int → Prop
  | [] => True
  | d :: rest => d ∉ rest ∧ Distinct rest

theorem survive_distinct (l : List Int) (c : Int) (hd : Distinct l) : Distinct (survive l c) := by
  induction l with
  | nil => trivial
  | cons d rest ih =>
    obtain ⟨hnot, hrest⟩ := hd
    unfold survive
    split
    · trivial
    · exact ⟨fun hmem => hnot (survive_subset rest c d hmem), ih hrest⟩

/-- **Invariant 1**: the window's content is always pairwise-distinct. -/
theorem foldFn_seen_distinct : ∀ xs, Distinct (foldFn xs).1 := by
  intro xs; induction xs with
  | wrap x => exact ⟨by simp, trivial⟩
  | snoc xs c ih =>
    show Distinct (stepSeen (foldFn xs).1 c)
    exact ⟨survive_not_mem (foldFn xs).1 c, survive_distinct (foldFn xs).1 c ih⟩

/-! ## The suffix-extraction function (structural, position-free) -/

/-- The length of a string (number of characters). -/
def len : SnocList Int Int → Nat
  | SnocList.wrap _ => 1
  | SnocList.snoc xs _ => len xs + 1

/-- `suffixList xs k` — the last `k` characters of `xs`, most-recent-first (capped at `xs`'s own
    length if `k` overshoots — the cap is harmless, `DistinctSuffix` below pairs this with an
    explicit `k ≤ len xs` bound). -/
def suffixList : SnocList Int Int → Nat → List Int
  | _, 0 => []
  | SnocList.wrap x, _+1 => [x]
  | SnocList.snoc xs c, k+1 => c :: suffixList xs k

/-- `suffixList` is prefix-nested: the length-`k` suffix is a prefix (the first `k` entries, most
    recent first) of any longer suffix. -/
theorem suffixList_take (xs : SnocList Int Int) (m j : Nat) (hj : j ≤ m) :
    (suffixList xs m).take j = suffixList xs j := by
  induction xs generalizing m j with
  | wrap x =>
    cases j with
    | zero => simp [suffixList]
    | succ j' =>
      cases m with
      | zero => omega
      | succ m' => simp [suffixList]
  | snoc xs c ih =>
    cases j with
    | zero => simp [suffixList]
    | succ j' =>
      cases m with
      | zero => omega
      | succ m' =>
        have hj' : j' ≤ m' := by omega
        show ((c :: suffixList xs m')).take (j'+1) = c :: suffixList xs j'
        rw [List.take_succ_cons, ih m' j' hj']

theorem suffixList_length_le (xs : SnocList Int Int) (m : Nat) : (suffixList xs m).length ≤ m := by
  induction xs generalizing m with
  | wrap x =>
    cases m with
    | zero => simp [suffixList]
    | succ m' => simp [suffixList]
  | snoc xs c ih =>
    cases m with
    | zero => simp [suffixList]
    | succ m' =>
      show (c :: suffixList xs m').length ≤ m' + 1
      simp only [List.length_cons]
      have := ih m'
      omega

/-- Prefixes of a distinct list are distinct. -/
theorem Distinct_take : ∀ (l : List Int) (j : Nat), Distinct l → Distinct (l.take j) := by
  intro l
  induction l with
  | nil => intro j _; cases j <;> simp [Distinct]
  | cons d rest ih =>
    intro j hd
    cases j with
    | zero => simp [Distinct]
    | succ j' =>
      obtain ⟨hnot, hrest⟩ := hd
      simp only [List.take_succ_cons]
      exact ⟨fun hmem => hnot (List.mem_of_mem_take hmem), ih j' hrest⟩

/-- `DistinctSuffix xs k` — `k` is a valid suffix length (`k ≤ len xs`) and the last `k` characters
    of `xs` are pairwise distinct. -/
def DistinctSuffix (xs : SnocList Int Int) (k : Nat) : Prop :=
  k ≤ len xs ∧ Distinct (suffixList xs k)

/-- Shorter distinct suffixes stay distinct. -/
theorem DistinctSuffix_mono (xs : SnocList Int Int) (k k' : Nat) (h : k ≤ k')
    (hd : DistinctSuffix xs k') : DistinctSuffix xs k :=
  ⟨Nat.le_trans h hd.1, suffixList_take xs k' k h ▸ Distinct_take _ k hd.2⟩

/-- The window's content never outgrows the string. -/
theorem foldFn_seen_length_le : ∀ xs, (foldFn xs).1.length ≤ len xs := by
  intro xs; induction xs with
  | wrap x => simp [foldFn, len]
  | snoc xs c ih =>
    show (stepSeen (foldFn xs).1 c).length ≤ len xs + 1
    show (survive (foldFn xs).1 c).length + 1 ≤ len xs + 1
    have := survive_length_le (foldFn xs).1 c
    omega

/-- **The crux shrink lemma**: sliding `survive` past `c` inside a `suffixList` again lands on a
    (shorter) `suffixList` — the sliding-window step, phrased purely in terms of the structural
    suffix extraction, no `foldFn` involved. -/
theorem survive_suffixList (xs : SnocList Int Int) (m : Nat) (c : Int) :
    survive (suffixList xs m) c = suffixList xs (survive (suffixList xs m) c).length := by
  have htake := survive_eq_take_length (suffixList xs m) c
  have hle1 := survive_length_le (suffixList xs m) c
  have hle2 := suffixList_length_le xs m
  have hjm : (survive (suffixList xs m) c).length ≤ m := by omega
  have key := suffixList_take xs m (survive (suffixList xs m) c).length hjm
  exact htake.trans key

/-- **Invariant 2**: the fold's window content IS the length-`seen.length` suffix of `xs`. -/
theorem foldFn_seen_eq_suffixList : ∀ xs : SnocList Int Int,
    (foldFn xs).1 = suffixList xs (foldFn xs).1.length := by
  intro xs
  induction xs with
  | wrap x => rfl
  | snoc xs c ih =>
    show stepSeen (foldFn xs).1 c = suffixList (SnocList.snoc xs c) (stepSeen (foldFn xs).1 c).length
    show c :: survive (foldFn xs).1 c
        = suffixList (SnocList.snoc xs c) (c :: survive (foldFn xs).1 c).length
    have hlen : (c :: survive (foldFn xs).1 c).length = (survive (foldFn xs).1 c).length + 1 := by simp
    rw [hlen]
    show c :: survive (foldFn xs).1 c = c :: suffixList xs (survive (foldFn xs).1 c).length
    congr 1
    rw [ih]
    exact survive_suffixList xs (foldFn xs).1.length c

/-- The window's current length is itself an achievable distinct-suffix length. -/
theorem curWin_distinct : ∀ xs, DistinctSuffix xs (foldFn xs).1.length :=
  fun xs => ⟨foldFn_seen_length_le xs, foldFn_seen_eq_suffixList xs ▸ foldFn_seen_distinct xs⟩

/-- **The crux optimality fact**: sliding the window only as far as the previous occurrence of `c`
    (no further) never over-shrinks — any `c`-free length-`j` prefix of the OLD window survives
    intact. -/
theorem survive_length_ge_of_not_mem_take (l : List Int) (c : Int) (j : Nat) (hj : j ≤ l.length)
    (hnot : c ∉ l.take j) : j ≤ (survive l c).length := by
  induction l generalizing j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons d rest ih =>
    cases j with
    | zero => omega
    | succ j' =>
      have hj' : j' ≤ rest.length := by simp only [List.length_cons] at hj; omega
      unfold survive
      split
      · rename_i heq
        exfalso; apply hnot
        rw [List.take_succ_cons]
        exact List.mem_cons.mpr (Or.inl heq.symm)
      · rename_i hne
        have hnot' : c ∉ rest.take j' := by
          intro hmem
          apply hnot
          rw [List.take_succ_cons]
          exact List.mem_cons.mpr (Or.inr hmem)
        have := ih j' hj' hnot'
        simp only [List.length_cons]; omega

/-- **Domination (window layer)**: the window's length is the LONGEST achievable distinct-suffix
    length — no distinct suffix is ever longer than what the fold's window currently holds. -/
theorem domination : ∀ (xs : SnocList Int Int) (k : Nat),
    DistinctSuffix xs k → k ≤ (foldFn xs).1.length := by
  intro xs
  induction xs with
  | wrap x =>
    intro k hd
    show k ≤ 1
    exact hd.1
  | snoc xs c ih =>
    intro k hd
    obtain ⟨hbound, hdist⟩ := hd
    cases k with
    | zero => omega
    | succ k' =>
      have hbound' : k' ≤ len xs := by simp only [len] at hbound; omega
      show k' + 1 ≤ (survive (foldFn xs).1 c).length + 1
      have hdist2 : Distinct (c :: suffixList xs k') := hdist
      have hcnotmem : c ∉ suffixList xs k' := hdist2.1
      have hdist' : Distinct (suffixList xs k') := hdist2.2
      have hk'_seen : k' ≤ (foldFn xs).1.length := ih k' ⟨hbound', hdist'⟩
      have heq_seen : (foldFn xs).1 = suffixList xs (foldFn xs).1.length := foldFn_seen_eq_suffixList xs
      have htake : (suffixList xs (foldFn xs).1.length).take k' = suffixList xs k' :=
        suffixList_take xs (foldFn xs).1.length k' hk'_seen
      have hcnotmem' : c ∉ (foldFn xs).1.take k' := by rw [heq_seen, htake]; exact hcnotmem
      have := survive_length_ge_of_not_mem_take (foldFn xs).1 c k' hk'_seen hcnotmem'
      omega

/-! ## Specification: the maximum achievable substring length -/

/-- `DistinctAt xs k` — `k` is the length of SOME contiguous substring of `xs`: achievable within a
    strict prefix, or (in the `snoc` case) a distinct suffix of the whole `snoc xs c` (the L53/L300
    two-layer "in the prefix, or ending here" reading). -/
def DistinctAt : SnocList Int Int → Nat → Prop
  | SnocList.wrap _, k => k = 1
  | SnocList.snoc xs c, k => DistinctAt xs k ∨ DistinctSuffix (SnocList.snoc xs c) k

/-- The **specification** as a morphism `Str ⟶ ℕ` in `Rel(Set)`: the relation of achievable
    substring lengths. LeetCode 3 asks for its `≤`-maximum, `max (≤) · Λ DistinctAt`. -/
def spec : Str ⟶ dNat := fun xs k => DistinctAt xs k

/-- `solve`'s output is an achievable substring length — hence `solve ⊑ spec`. -/
theorem solve_achievable : ∀ xs, DistinctAt xs (solveFn xs) := by
  intro xs; induction xs with
  | wrap x => rfl
  | snoc xs c ih =>
    show DistinctAt (SnocList.snoc xs c) (nmax (foldFn xs).2 (stepSeen (foldFn xs).1 c).length)
    rcases nmax_eq_or (foldFn xs).2 (stepSeen (foldFn xs).1 c).length with he | he
    · rw [he]; exact Or.inl ih
    · rw [he]; exact Or.inr (curWin_distinct (SnocList.snoc xs c))

/-- `solve` dominates every achievable substring length. -/
theorem domination_all : ∀ (xs : SnocList Int Int) (k : Nat), DistinctAt xs k → k ≤ solveFn xs := by
  intro xs; induction xs with
  | wrap x => intro k hk; show k ≤ 1; have hk1 : k = 1 := hk; omega
  | snoc xs c ih =>
    intro k hk
    rcases hk with h | h
    · have h1 : k ≤ (foldFn xs).2 := ih k h
      have h2 := nmax_ge_left (foldFn xs).2 (stepSeen (foldFn xs).1 c).length
      show k ≤ nmax (foldFn xs).2 (stepSeen (foldFn xs).1 c).length
      omega
    · have hle : k ≤ (foldFn (SnocList.snoc xs c)).1.length := domination (SnocList.snoc xs c) k h
      have heq : (foldFn (SnocList.snoc xs c)).1.length = (stepSeen (foldFn xs).1 c).length := rfl
      rw [heq] at hle
      have h2 := nmax_ge_right (foldFn xs).2 (stepSeen (foldFn xs).1 c).length
      show k ≤ nmax (foldFn xs).2 (stepSeen (foldFn xs).1 c).length
      omega

/-- **The program refines the specification**: every value `solve` returns is an achievable
    substring length. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun xs k h => ?_)
  have hk : k = solveFn xs := h
  rw [hk]; exact solve_achievable xs

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ DistinctAt`, pointwise in
    `Rel(Set)`): `solve xs` is an achievable substring length and is `≤`-greatest among all
    achievable substring lengths. -/
theorem solve_correct (xs : SnocList Int Int) :
    DistinctAt xs (solveFn xs) ∧ ∀ k, DistinctAt xs k → k ≤ solveFn xs :=
  ⟨solve_achievable xs, domination_all xs⟩

/-- **Honest headline (§7.5 `max (≤)·Λ spec`)**: `solve` is exactly the morphism `Λ spec ≫ est D`
    for the `≤`-preference order `D w z := z ≤ w` — the longest achievable substring length, not
    merely pointwise. Bridged from soundness (`solve_achievable`) and domination (`domination_all`). -/
theorem solve_eq_est : solve = Λ spec ≫ est (fun w z : Nat => z ≤ w) :=
  eq_Λ_comp_est _ (fun x y h1 h2 => Nat.le_antisymm h2 h1) solveFn spec
    solve_achievable (fun xs k hk => domination_all xs k hk)

/-! ## Running the program -/

/-- Build a string from a first character and the rest, in index order. -/
def ofList (first : Int) (rest : List Int) : SnocList Int Int :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 97 [98, 99, 97, 98, 98]) = 3 := by decide   -- "abcabb" → "abc"
example : solveFn (ofList 98 [98, 98]) = 1 := by decide                -- "bbb" → "b"
example : solveFn (ofList 112 [119, 119, 107, 101, 119]) = 3 := by decide  -- "pwwkew" → "wke"
example : solveFn (ofList 5 []) = 1 := by decide                       -- single char

end Freyd.Alg.RelSet.LC3
