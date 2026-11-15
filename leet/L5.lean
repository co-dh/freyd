/-
  LeetCode 5 — Longest Palindromic Substring — as an ALLEGORY PROGRAM.

  Problem: given a string `s`, return the LENGTH of the longest contiguous substring of `s` that
  reads the same forwards and backwards (a palindrome).  Empty string → 0; any single character
  → 1.  We prove the honest scalar invariant (the length), not a witness substring.

  Same recipe as `leet/L53.lean` (`Freyd/leetcode.md` S0/S1): correctness is refinement
  (achievability) + domination of an extremum spec, `solve = max (≤) · Λ IsPalinSubstr`.

  1. **Spec vocabulary.**  `isPalin xs := xs = xs.reverse`; a contiguous substring is
     `sub s i len := (s.drop i).take len`; `IsPalinSubstr s len := ∃ i, i + len ≤ s.length ∧
     isPalin (sub s i len)` — "`s` has a palindromic substring of length `len`".

  2. **Program (expand-around-center, index-free).**  Rather than a `while`-loop expansion with
     explicit index bookkeeping (`l--, r++`, needing a fuel parameter, cf. `leetcode.md` S13), we
     phrase the center-walk as a two-pointer scan over `List Int` where `left` is the REVERSED
     already-consumed prefix: at each position the radius reachable from the center is
     `commonPrefixLen left right` — a plain STRUCTURALLY RECURSIVE list-prefix-match (no fuel).
     `bestFrom left right` folds over `right`, at every element checking both the odd center (at
     the element) and the even center (the gap just before it) against `left`, then recursing one
     element further; `longestPalinFn s := bestFrom [] s`.

  3. **Correctness — `longest_palin_correct` = achievability ∧ domination.**
     - achievability: `IsPalinSubstr s (longestPalinFn s)` — every value `bestFrom` ever returns
       is realized by a genuine list SPLIT `s = pre ++ mid ++ post` with `isPalin mid`
       (`palinSplit_of_commonPrefix`, the "peel/wrap" engine, built from `List.reverse_append` +
       `List.take_append_drop` alone), bridged to the index form once at the end.
     - domination: `∀ len, IsPalinSubstr s len → len ≤ longestPalinFn s` — the CRUX.  Every
       palindromic substring `mid` (length `len`) splits around its own center as `A ++ c :: B` (or
       `A ++ B`) with `A = B.reverse` (`palin_odd_split`/`palin_even_split`, via Lean core's
       `List.append_inj`); walking `bestFrom` to exactly that center exposes `A.reverse.take m =
       B.take m` as a genuine `commonPrefixLen` witness (`commonPrefixLen_ge_of_take_eq`), and a
       domination-chain lemma (`bestFrom_le_of_split`) shows `bestFrom [] s` dominates the value
       computed at ANY later walk position — combining the two gives `len ≤ longestPalinFn s`.

  Mathlib-free; target axioms `⊆ {propext, Quot.sound}` (fully constructive — no `Classical.choice`,
  every arithmetic step is `omega` on plain `Nat` (in)equalities, no negated conjunctions).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC5

open Freyd

/-! ## `Nat` `max` (mathlib-free, so we control the rewrite lemmas — copy of L3's `nmax`). -/

def nmax (a b : Nat) : Nat := if a ≤ b then b else a

theorem nmax_ge_left  (a b : Nat) : a ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_ge_right (a b : Nat) : b ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_eq_or (a b : Nat) : nmax a b = a ∨ nmax a b = b := by
  unfold nmax; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Data / answer objects -/

/-- The object of character sequences in `Rel(Set)` — plain `List Int` (characters as integers,
    matching `leet/L125.lean`/`leet/L3.lean`). -/
abbrev Arr : RelSet.{0} := ⟨List Int⟩
/-- The answer object: natural numbers (lengths). -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## Spec vocabulary: palindromes and contiguous substrings -/

/-- `isPalin xs` — `xs` reads the same forwards and backwards. -/
def isPalin (xs : List Int) : Prop := xs = xs.reverse

/-- `sub s i len` — the contiguous substring of `s` starting at index `i` with `len` characters. -/
def sub (s : List Int) (i len : Nat) : List Int := (s.drop i).take len

/-- **The specification vocabulary**: `s` has a palindromic substring of length `len`. -/
def IsPalinSubstr (s : List Int) (len : Nat) : Prop :=
  ∃ i, i + len ≤ s.length ∧ isPalin (sub s i len)

/-- The equivalent SPLIT form of `IsPalinSubstr` — `s` factors as `pre ++ mid ++ post` with `mid`
    a palindrome of length `len`.  Index-free, so the achievability proof never needs `Nat`
    subtraction; bridged to `IsPalinSubstr` once, at the end. -/
def IsPalinSplit (s : List Int) (len : Nat) : Prop :=
  ∃ pre mid post, s = pre ++ mid ++ post ∧ mid.length = len ∧ isPalin mid

theorem IsPalinSplit.toSubstr {s : List Int} {len : Nat} (h : IsPalinSplit s len) :
    IsPalinSubstr s len := by
  obtain ⟨pre, mid, post, hs, hlen, hpal⟩ := h
  refine ⟨pre.length, ?_, ?_⟩
  · rw [hs]; simp only [List.length_append]; omega
  · show isPalin (sub s pre.length len)
    have hdrop : s.drop pre.length = mid ++ post := by
      rw [hs, List.append_assoc, List.drop_left]
    unfold sub
    rw [hdrop, ← hlen, List.take_left]
    exact hpal

/-! ## The engine: `commonPrefixLen` — a structurally recursive, index-free "expand around center" -/

/-- The length of the common (elementwise-matching) prefix of `a` and `b`.  Plain structural
    recursion (decreasing on `a`), no fuel needed. -/
def commonPrefixLen : List Int → List Int → Nat
  | a :: as, b :: bs => if a = b then commonPrefixLen as bs + 1 else 0
  | _, _ => 0

theorem commonPrefixLen_le_left (a b : List Int) : commonPrefixLen a b ≤ a.length := by
  induction a generalizing b with
  | nil => simp [commonPrefixLen]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefixLen]
    | cons y ys =>
      unfold commonPrefixLen
      split
      · have := ih ys; simp only [List.length_cons]; omega
      · simp

theorem commonPrefixLen_le_right (a b : List Int) : commonPrefixLen a b ≤ b.length := by
  induction a generalizing b with
  | nil => simp [commonPrefixLen]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefixLen]
    | cons y ys =>
      unfold commonPrefixLen
      split
      · have := ih ys; simp only [List.length_cons]; omega
      · simp

theorem commonPrefixLen_take_eq (a b : List Int) :
    a.take (commonPrefixLen a b) = b.take (commonPrefixLen a b) := by
  induction a generalizing b with
  | nil => simp [commonPrefixLen]
  | cons x xs ih =>
    cases b with
    | nil => simp [commonPrefixLen]
    | cons y ys =>
      unfold commonPrefixLen
      split
      · rename_i hxy
        simp only [List.take_succ_cons, hxy]
        congr 1
        exact ih ys
      · simp

/-- The converse: a genuine matching prefix of length `m` certifies `commonPrefixLen ≥ m`. -/
theorem commonPrefixLen_ge_of_take_eq (a b : List Int) (m : Nat)
    (hle_a : m ≤ a.length) (hle_b : m ≤ b.length) (heq : a.take m = b.take m) :
    m ≤ commonPrefixLen a b := by
  induction a generalizing b m with
  | nil => simp only [List.length_nil] at hle_a; omega
  | cons x xs ih =>
    cases b with
    | nil => simp only [List.length_nil] at hle_b; omega
    | cons y ys =>
      cases m with
      | zero => omega
      | succ m' =>
        simp only [List.length_cons] at hle_a hle_b
        simp only [List.take_succ_cons, List.cons.injEq] at heq
        unfold commonPrefixLen
        rw [if_pos heq.1]
        have := ih ys m' (by omega) (by omega) heq.2
        omega

/-- **The peel/wrap engine**: given `s = left.reverse ++ extra ++ right` with `extra` itself a
    palindrome (`extra.reverse = extra` — either `[]` for an even center or `[c]` for an odd
    center), `s` has a palindromic-substring SPLIT of length `2 * commonPrefixLen left right +
    extra.length` — the substring symmetric about `extra`, radius `commonPrefixLen left right`. -/
theorem palinSplit_of_commonPrefix (s left right extra : List Int)
    (hextra : extra.reverse = extra) (hs : s = left.reverse ++ extra ++ right) :
    IsPalinSplit s (2 * commonPrefixLen left right + extra.length) := by
  have hrL : commonPrefixLen left right ≤ left.length := commonPrefixLen_le_left left right
  have hrR : commonPrefixLen left right ≤ right.length := commonPrefixLen_le_right left right
  have heq : left.take (commonPrefixLen left right) = right.take (commonPrefixLen left right) :=
    commonPrefixLen_take_eq left right
  generalize hr_def : commonPrefixLen left right = r at *
  refine ⟨(left.drop r).reverse, (left.take r).reverse ++ extra ++ right.take r, right.drop r,
    ?_, ?_, ?_⟩
  · -- s = pre ++ mid ++ post
    rw [hs]
    have step1 : (left.drop r).reverse ++ (left.take r).reverse ++ extra ++
        (right.take r ++ right.drop r) = left.reverse ++ extra ++ right := by
      rw [← List.reverse_append, List.take_append_drop, List.take_append_drop]
    rw [← step1]
    simp only [List.append_assoc]
  · -- length = 2r + extra.length
    simp only [List.length_append, List.length_reverse, List.length_take]
    rw [Nat.min_eq_left hrL, Nat.min_eq_left hrR]
    omega
  · -- isPalin mid
    show (left.take r).reverse ++ extra ++ right.take r
      = ((left.take r).reverse ++ extra ++ right.take r).reverse
    rw [List.reverse_append, List.reverse_append, List.reverse_reverse, hextra, ← heq,
      List.append_assoc]

/-! ## The program: `bestFrom` — the two-pointer center walk -/

/-- `bestFrom left right` — walking `right` left-to-right, `left` the REVERSED already-consumed
    prefix: at each element `x` of `right` check the ODD center at `x` (radius
    `commonPrefixLen left rest`, against the tail `rest` after `x`) and the EVEN center in the gap
    just before `x` (radius `commonPrefixLen left (x::rest)`), then recurse one element further.
    Plain structural recursion (decreasing on `right`) — no fuel. -/
def bestFrom : List Int → List Int → Nat
  | _, [] => 0
  | left, x :: rest =>
    nmax (nmax (2 * commonPrefixLen left rest + 1) (2 * commonPrefixLen left (x :: rest)))
      (bestFrom (x :: left) rest)

/-- **The allegory program**: the length of the longest palindromic substring of `s`. -/
def longestPalinFn (s : List Int) : Nat := bestFrom [] s

/-- **The allegory program**: LeetCode 5's solution as a morphism `Arr ⟶ ℕ` in `Rel(Set)`. -/
def solve : Arr ⟶ dNat := graph longestPalinFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map longestPalinFn

/-! ## Achievability: every value `bestFrom` returns is a genuine palindromic-substring length -/

/-- **Achievability**, generalized over the walk position: at ANY split `s = left.reverse ++
    right`, `bestFrom left right` is a genuine palindromic-substring length of `s`. -/
theorem bestFrom_achievable : ∀ (s left right : List Int), s = left.reverse ++ right →
    IsPalinSubstr s (bestFrom left right) := by
  intro s left right
  induction right generalizing left with
  | nil =>
    intro _
    show IsPalinSubstr s 0
    exact ⟨0, by omega, by simp [sub, isPalin]⟩
  | cons x rest ih =>
    intro hs
    show IsPalinSubstr s
      (nmax (nmax (2 * commonPrefixLen left rest + 1) (2 * commonPrefixLen left (x :: rest)))
        (bestFrom (x :: left) rest))
    rcases nmax_eq_or (nmax (2 * commonPrefixLen left rest + 1)
        (2 * commonPrefixLen left (x :: rest))) (bestFrom (x :: left) rest) with h1 | h1
    · rw [h1]
      rcases nmax_eq_or (2 * commonPrefixLen left rest + 1)
          (2 * commonPrefixLen left (x :: rest)) with h2 | h2
      · rw [h2]
        have hsplit : IsPalinSplit s (2 * commonPrefixLen left rest + 1) :=
          palinSplit_of_commonPrefix s left rest [x] (by simp) (by rw [hs]; simp [List.append_assoc])
        exact hsplit.toSubstr
      · rw [h2]
        have hsplit : IsPalinSplit s (2 * commonPrefixLen left (x :: rest)) :=
          palinSplit_of_commonPrefix s left (x :: rest) [] (by simp) (by rw [hs]; simp)
        exact hsplit.toSubstr
    · rw [h1]
      have hs' : s = (x :: left).reverse ++ rest := by
        rw [hs]; simp [List.reverse_cons, List.append_assoc]
      exact ih (x :: left) hs'

/-- **The program's answer is achievable**: `longestPalinFn s` is the length of a genuine
    palindromic substring of `s`. -/
theorem longestPalin_achievable (s : List Int) : IsPalinSubstr s (longestPalinFn s) :=
  bestFrom_achievable s [] s (by simp)

/-! ## Domination — the crux: every palindromic substring is found by expanding around its own
    center. -/

theorem IsPalinSubstr.toSplit {s : List Int} {len : Nat} (h : IsPalinSubstr s len) :
    IsPalinSplit s len := by
  obtain ⟨i, hi, hpal⟩ := h
  refine ⟨s.take i, sub s i len, s.drop (i + len), ?_, ?_, hpal⟩
  · unfold sub
    rw [← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]
  · unfold sub
    simp only [List.length_take, List.length_drop]
    omega

/-- `l.reverse` split around the point `n`, as a `have`-safe compound-term rewrite (avoids `rw`
    corrupting the OTHER occurrences of the bare variable `l` — see `palinSplit_of_commonPrefix`'s
    `step1` for the same trick). -/
theorem reverse_take_drop (l : List Int) (n : Nat) :
    l.reverse = (l.drop n).reverse ++ (l.take n).reverse := by
  have h := congrArg List.reverse (List.take_append_drop n l).symm
  rw [List.reverse_append] at h
  exact h

/-- **The peel lemma (even case)**: an EVEN-length palindrome `mid` (length `2m`) splits exactly
    in half, second half = first half reversed. -/
theorem palin_even_split (mid : List Int) (m : Nat) (hlen : mid.length = 2 * m)
    (hpal : isPalin mid) : (mid.take m).reverse = mid.drop m := by
  have hsplit : mid.take m ++ mid.drop m = mid := List.take_append_drop m mid
  have h2 := reverse_take_drop mid m
  have heq : mid.take m ++ mid.drop m = (mid.drop m).reverse ++ (mid.take m).reverse :=
    hsplit.trans (hpal.trans h2)
  have hlenA : (mid.take m).length = m := by rw [List.length_take]; omega
  have hlenB : (mid.drop m).reverse.length = m := by rw [List.length_reverse, List.length_drop]; omega
  exact (List.append_inj heq (hlenA.trans hlenB.symm)).2.symm

/-- **The peel lemma (odd case)**: an ODD-length palindrome `mid` (length `2m+1`) splits as
    `A ++ [c] ++ B` with `B` = `A` reversed (the middle element `c` is its own mirror). -/
theorem palin_odd_split (mid : List Int) (m : Nat) (hlen : mid.length = 2 * m + 1)
    (hpal : isPalin mid) : (mid.take m).reverse = mid.drop (m + 1) := by
  have hsplit : mid.take m ++ mid.drop m = mid := List.take_append_drop m mid
  have hdm_len : (mid.drop m).length = m + 1 := by rw [List.length_drop]; omega
  obtain ⟨c, tl, hdm_eq⟩ : ∃ c tl, mid.drop m = c :: tl := by
    cases hdm : mid.drop m with
    | nil => exfalso; rw [hdm] at hdm_len; simp only [List.length_nil] at hdm_len; omega
    | cons c tl => exact ⟨c, tl, rfl⟩
  have htl_len : tl.length = m := by
    have := hdm_len; rw [hdm_eq] at this; simp only [List.length_cons] at this; omega
  have htl : tl = mid.drop (m + 1) := by
    have step : (mid.drop m).drop 1 = mid.drop (m + 1) := List.drop_drop
    rw [hdm_eq] at step
    exact step
  have hmid_eq : mid = mid.take m ++ c :: tl := by rw [← hdm_eq, hsplit]
  have hrev : mid.reverse = tl.reverse ++ [c] ++ (mid.take m).reverse := by
    have h := congrArg List.reverse hmid_eq
    rw [List.reverse_append, List.reverse_cons] at h
    exact h
  have heq : mid.take m ++ (c :: tl) = tl.reverse ++ [c] ++ (mid.take m).reverse :=
    hmid_eq.symm.trans (hpal.trans hrev)
  have heq' : mid.take m ++ (c :: tl) = tl.reverse ++ (c :: (mid.take m).reverse) := by
    rw [heq, List.append_assoc]; rfl
  have hlenA : (mid.take m).length = m := by rw [List.length_take]; omega
  have hlenS : (mid.take m).length = tl.reverse.length := by
    rw [hlenA, List.length_reverse, htl_len]
  have hinj := List.append_inj heq' hlenS
  have h1 : mid.take m = tl.reverse := hinj.1
  have : (mid.take m).reverse = tl := by rw [h1, List.reverse_reverse]
  rw [this, htl]

/-- **The domination chain**: `bestFrom` at the START dominates `bestFrom` at ANY LATER walk
    position reached by consuming a prefix `mid` (`left` grows by `mid.reverse`, `right` shrinks by
    `mid`). -/
theorem bestFrom_le_of_split (left mid right : List Int) :
    bestFrom (mid.reverse ++ left) right ≤ bestFrom left (mid ++ right) := by
  induction mid generalizing left with
  | nil => simp
  | cons x xs ih =>
    have hstep : bestFrom (x :: left) (xs ++ right) ≤ bestFrom left (x :: (xs ++ right)) := by
      show bestFrom (x :: left) (xs ++ right) ≤
        nmax (nmax (2 * commonPrefixLen left (xs ++ right) + 1)
          (2 * commonPrefixLen left (x :: (xs ++ right)))) (bestFrom (x :: left) (xs ++ right))
      exact nmax_ge_right _ _
    have hrec : bestFrom (xs.reverse ++ (x :: left)) right ≤ bestFrom (x :: left) (xs ++ right) :=
      ih (x :: left)
    have hassoc : (x :: xs).reverse ++ left = xs.reverse ++ (x :: left) := by
      rw [List.reverse_cons, List.append_assoc]; rfl
    show bestFrom ((x :: xs).reverse ++ left) right ≤ bestFrom left (x :: (xs ++ right))
    rw [hassoc]
    exact Nat.le_trans hrec hstep

/-- The ODD-center value at the head of `right` is always a lower bound for `bestFrom` there. -/
theorem bestFrom_ge_odd (left : List Int) (x : Int) (rest : List Int) :
    2 * commonPrefixLen left rest + 1 ≤ bestFrom left (x :: rest) := by
  show 2 * commonPrefixLen left rest + 1 ≤
    nmax (nmax (2 * commonPrefixLen left rest + 1) (2 * commonPrefixLen left (x :: rest)))
      (bestFrom (x :: left) rest)
  have h1 := nmax_ge_left (2 * commonPrefixLen left rest + 1) (2 * commonPrefixLen left (x :: rest))
  have h2 := nmax_ge_left (nmax (2 * commonPrefixLen left rest + 1) (2 * commonPrefixLen left (x :: rest)))
    (bestFrom (x :: left) rest)
  omega

/-- The EVEN-center value at the gap before `right`'s head is always a lower bound for `bestFrom`
    there. -/
theorem bestFrom_ge_even (left : List Int) (x : Int) (rest : List Int) :
    2 * commonPrefixLen left (x :: rest) ≤ bestFrom left (x :: rest) := by
  show 2 * commonPrefixLen left (x :: rest) ≤
    nmax (nmax (2 * commonPrefixLen left rest + 1) (2 * commonPrefixLen left (x :: rest)))
      (bestFrom (x :: left) rest)
  have h1 := nmax_ge_right (2 * commonPrefixLen left rest + 1) (2 * commonPrefixLen left (x :: rest))
  have h2 := nmax_ge_left (nmax (2 * commonPrefixLen left rest + 1) (2 * commonPrefixLen left (x :: rest)))
    (bestFrom (x :: left) rest)
  omega

/-- Extract the element right after position `n` from a list longer than `n`, together with the
    fact that its tail is `l.drop (n+1)` — the "peek one element ahead" step used to find the
    center element of an odd-length palindrome. -/
theorem drop_eq_cons_of_lt {l : List Int} {n : Nat} (h : n < l.length) :
    ∃ c tl, l.drop n = c :: tl ∧ tl = l.drop (n + 1) := by
  have hlen : (l.drop n).length = l.length - n := List.length_drop
  obtain ⟨c, tl, heq⟩ : ∃ c tl, l.drop n = c :: tl := by
    cases hd : l.drop n with
    | nil => exfalso; rw [hd] at hlen; simp only [List.length_nil] at hlen; omega
    | cons c tl => exact ⟨c, tl, rfl⟩
  refine ⟨c, tl, heq, ?_⟩
  have step : (l.drop n).drop 1 = l.drop (n + 1) := List.drop_drop
  rw [heq] at step
  exact step

/-- **Domination**: no palindromic substring of `s` is longer than `longestPalinFn s` — every
    palindrome is found by expanding around its OWN center. -/
theorem longestPalin_dominates (s : List Int) (len : Nat) (h : IsPalinSubstr s len) :
    len ≤ longestPalinFn s := by
  rcases Nat.eq_zero_or_pos len with hlen0 | hlenpos
  · omega
  obtain ⟨pre, mid, post, hs, hlen, hpal⟩ := h.toSplit
  -- the walk to the point right after `pre ++ mid.take m` dominates `longestPalinFn s`, for ANY m
  have hchain' : ∀ m, bestFrom (pre ++ mid.take m).reverse (mid.drop m ++ post) ≤ longestPalinFn s := by
    intro m
    have hEq1 : (pre ++ mid.take m) ++ (mid.drop m ++ post) = s := by
      rw [hs]
      simp only [List.append_assoc]
      rw [← List.append_assoc (mid.take m) (mid.drop m) post, List.take_append_drop]
    have hchain : bestFrom ((pre ++ mid.take m).reverse ++ []) (mid.drop m ++ post)
        ≤ bestFrom [] ((pre ++ mid.take m) ++ (mid.drop m ++ post)) :=
      bestFrom_le_of_split [] (pre ++ mid.take m) (mid.drop m ++ post)
    unfold longestPalinFn
    rw [← hEq1]
    simpa using hchain
  rcases Nat.mod_two_eq_zero_or_one len with he | ho
  · -- EVEN: len = 2 * m
    obtain ⟨m, hm⟩ : ∃ m, len = 2 * m := ⟨len / 2, by omega⟩
    have hmidlen : mid.length = 2 * m := by omega
    have hAB : (mid.take m).reverse = mid.drop m := palin_even_split mid m hmidlen hpal
    have hAlen : (mid.take m).length = m := by rw [List.length_take]; omega
    have hBlen : (mid.drop m).length = m := by rw [List.length_drop]; omega
    obtain ⟨y, By, hByeq⟩ : ∃ y By, mid.drop m = y :: By := by
      cases hB : mid.drop m with
      | nil => exfalso; rw [hB] at hBlen; simp only [List.length_nil] at hBlen; omega
      | cons y By => exact ⟨y, By, rfl⟩
    have htakeeq : (pre ++ mid.take m).reverse.take m = (mid.drop m ++ post).take m := by
      have h1 : (pre ++ mid.take m).reverse = (mid.take m).reverse ++ pre.reverse := by
        rw [List.reverse_append]
      have h2 : (pre ++ mid.take m).reverse.take m = (mid.take m).reverse := by
        rw [h1, List.take_left' (by rw [List.length_reverse]; exact hAlen)]
      have h4 : (mid.drop m ++ post).take m = mid.drop m := by
        have hb := @List.take_left Int (mid.drop m) post
        rwa [hBlen] at hb
      rw [h2, hAB, h4]
    have hradius : m ≤ commonPrefixLen (pre ++ mid.take m).reverse (mid.drop m ++ post) :=
      commonPrefixLen_ge_of_take_eq _ _ m
        (by rw [List.length_reverse, List.length_append]; omega)
        (by rw [List.length_append]; omega) htakeeq
    have hcons : mid.drop m ++ post = y :: (By ++ post) := by rw [hByeq]; rfl
    have hval : 2 * m ≤ bestFrom (pre ++ mid.take m).reverse (mid.drop m ++ post) := by
      rw [hcons]
      have hge := bestFrom_ge_even (pre ++ mid.take m).reverse y (By ++ post)
      have hradius' : m ≤ commonPrefixLen (pre ++ mid.take m).reverse (y :: (By ++ post)) := by
        rw [← hcons]; exact hradius
      omega
    have := hchain' m
    omega
  · -- ODD: len = 2 * m + 1
    obtain ⟨m, hm⟩ : ∃ m, len = 2 * m + 1 := ⟨len / 2, by omega⟩
    have hmidlen : mid.length = 2 * m + 1 := by omega
    have hAB : (mid.take m).reverse = mid.drop (m + 1) := palin_odd_split mid m hmidlen hpal
    have hAlen : (mid.take m).length = m := by rw [List.length_take]; omega
    have hClen : (mid.drop (m + 1)).length = m := by rw [List.length_drop]; omega
    obtain ⟨c, tl, hceq, htleq⟩ := drop_eq_cons_of_lt (l := mid) (n := m) (by omega)
    have hClen' : tl.length = m := by rw [htleq]; exact hClen
    have htakeeq : (pre ++ mid.take m).reverse.take m = (tl ++ post).take m := by
      have h1 : (pre ++ mid.take m).reverse = (mid.take m).reverse ++ pre.reverse := by
        rw [List.reverse_append]
      have h2 : (pre ++ mid.take m).reverse.take m = (mid.take m).reverse := by
        rw [h1, List.take_left' (by rw [List.length_reverse]; exact hAlen)]
      have h4 : (tl ++ post).take m = tl := by
        have hb := @List.take_left Int tl post
        rwa [hClen'] at hb
      rw [h2, hAB, h4, htleq]
    have hradius : m ≤ commonPrefixLen (pre ++ mid.take m).reverse (tl ++ post) :=
      commonPrefixLen_ge_of_take_eq _ _ m
        (by rw [List.length_reverse, List.length_append]; omega)
        (by rw [List.length_append]; omega) htakeeq
    have hcons : mid.drop m ++ post = c :: (tl ++ post) := by rw [hceq]; rfl
    have hval : 2 * m + 1 ≤ bestFrom (pre ++ mid.take m).reverse (mid.drop m ++ post) := by
      rw [hcons]
      have hge := bestFrom_ge_odd (pre ++ mid.take m).reverse c (tl ++ post)
      omega
    have := hchain' m
    omega

/-! ## Correctness: `solve` computes the length of the longest palindromic substring -/

/-- **Correctness of the allegory program** (`solve = max (≤) · Λ IsPalinSubstr`, pointwise in
    `Rel(Set)`): `longestPalinFn s` is the length of a genuine palindromic substring of `s`
    (achievability) and no palindromic substring is longer (domination). -/
theorem longest_palin_correct (s : List Int) :
    IsPalinSubstr s (longestPalinFn s) ∧ ∀ len, IsPalinSubstr s len → len ≤ longestPalinFn s :=
  ⟨longestPalin_achievable s, longestPalin_dominates s⟩

/-- **The program refines the specification**: every value `solve` returns is an achievable
    palindromic-substring length. -/
theorem solve_le_spec : solve ⊑ (fun s len => IsPalinSubstr s len) := by
  refine le_iff.mpr (fun s len h => ?_)
  have hlen : len = longestPalinFn s := h
  rw [hlen]; exact (longest_palin_correct s).1

/-! ## Running the program -/

example : longestPalinFn [98, 97, 98, 97, 100] = 3 := by decide       -- "babad" → "bab"/"aba"
example : longestPalinFn [99, 98, 98, 100] = 2 := by decide           -- "cbbd" → "bb"
example : longestPalinFn [97] = 1 := by decide                        -- "a" → "a"
example : longestPalinFn ([] : List Int) = 0 := by decide             -- "" → 0
example : longestPalinFn [114, 97, 99, 101, 99, 97, 114] = 7 := by decide  -- "racecar" (whole string)

end Freyd.Alg.RelSet.LC5
