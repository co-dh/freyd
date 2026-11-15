/-
  LeetCode 139 — Word Break — as an ALLEGORY PROGRAM (a DECISION problem, `Freyd/leetcode.md`
  skills S5/S13/S16).

  Problem: given a string `s` and a dictionary `dict` of words, return `true` iff `s` can be
  segmented into a space-separated sequence of ONE OR MORE dictionary words (reuse allowed).
  Strings are modelled as `List α` for a generic `[DecidableEq α]` (instantiated at `Char` for the
  `Rel(Set)` packaging and the `decide` sanity checks, so examples read as ordinary words).

  1. **Program (Bool).** `wordBreakFuel : Nat → List α → Bool` peels ONE dictionary word off the
     FRONT of `s` at a time (`stepBreak`/`contrib`, via a hand `splitPrefix : List α → List α →
     Option (List α)` returning the leftover suffix when the first argument is a prefix of the
     second — the mathlib-free substitute for `List.IsPrefix`/`List.isPrefixOf`, needed because we
     want the SUFFIX, not just a `Bool`/existence witness). The natural recursion decreases `s` by
     a DICTIONARY WORD, not by one element — a genuinely different amount each step — so, exactly
     like `L322`/`L1143` (S13), the naive definition is well-founded, not structural; it is wrapped
     in a FUEL parameter that recurses on fuel by ordinary `Nat.rec`, staying kernel-reducible.
     `s.length` is a sufficient (in fact exactly matching) fuel bound: dictionary words are
     required nonempty, so every peeled step strictly shortens the remaining suffix by `≥ 1`.
  2. **Spec (Prop).** `Seg dict s` — an inductive segmentation-witness family: `nil : Seg dict []`,
     `cons : w ∈ dict → w ≠ [] → Seg dict suf → Seg dict (w ++ suf)`. This is the honest reading of
     "splits into a sequence of nonempty dictionary words, reuse allowed" (not a tautology).
  3. **Correctness.** `wordBreakFuel_correct` (fuel induction, `L322`-shaped) gives, for any
     sufficient fuel, `wordBreakFuel dict fuel s = true ↔ Seg dict s`; instantiating at
     `fuel = s.length` gives the headline `wordBreak_correct : wordBreakFn dict s = true ↔
     Seg dict s` — a plain `iff`, the S5 DECISION shape (no `max(≤)·Λ` extremum, no
     refinement+domination).
  4. **`Rel(Set)` packaging.** `solve := graph (fun p => wordBreakFn p.1 p.2) : dInput ⟶ dBool`;
     `spec : dInput ⟶ dBool := fun p b => (b = true ↔ Seg p.1 p.2)`; `solve = spec` via the S5
     Bool-extensionality bridge (`bool_eq_of_iff_true`, copied — small mathlib-free helpers are
     re-derived per file in this track, `leetcode.md` S0).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

namespace Freyd.Alg.RelSet.LC139

open Freyd

variable {α : Type} [DecidableEq α]

/-! ## `splitPrefix` — the mathlib-free "is `w` a prefix of `s`, and if so what's left" -/

/-- `splitPrefix w s` — if `w` is a prefix of `s`, the leftover suffix; else `none`. The
    mathlib-free substitute for `List.IsPrefix`/`List.isPrefixOf` that also RETURNS the suffix
    (what the DP step actually needs, not just a yes/no). -/
def splitPrefix [DecidableEq α] : List α → List α → Option (List α)
  | [], s => some s
  | _ :: _, [] => none
  | a :: w, b :: s => if a = b then splitPrefix w s else none

/-- **`splitPrefix` reflects prefix-splitting**: `splitPrefix w s = some suf` iff `w ++ suf = s`. -/
theorem splitPrefix_eq_some {w s suf : List α} :
    splitPrefix w s = some suf ↔ w ++ suf = s := by
  induction w generalizing s with
  | nil => show some s = some suf ↔ [] ++ suf = s; rw [List.nil_append, Option.some.injEq, eq_comm]
  | cons a w' ih =>
    cases s with
    | nil =>
      show (none : Option (List α)) = some suf ↔ (a :: w') ++ suf = []
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; exact absurd h (by simp)
    | cons b s' =>
      show (if a = b then splitPrefix w' s' else none) = some suf ↔ (a :: w') ++ suf = b :: s'
      by_cases hab : a = b
      · rw [if_pos hab, ih]
        subst hab
        exact ⟨fun h => by rw [List.cons_append, h], fun h => by
          rw [List.cons_append, List.cons.injEq] at h; exact h.2⟩
      · rw [if_neg hab]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h
          rw [List.cons_append, List.cons.injEq] at h
          exact absurd h.1 hab

/-! ## Program: peel one dictionary word off the front, recurse on the leftover suffix -/

/-- One dictionary word's contribution: strip it as a (nonempty) prefix of `s`, and recurse on the
    leftover via `rec`; `false` if `w` is empty or is not a prefix of `s`. -/
def contrib (rec : List α → Bool) (s w : List α) : Bool :=
  match w with
  | [] => false
  | _ :: _ =>
    match splitPrefix w s with
    | some suf => rec suf
    | none => false

theorem contrib_true_iff {rec : List α → Bool} {s w : List α} :
    contrib rec s w = true ↔ ∃ suf, w ≠ [] ∧ w ++ suf = s ∧ rec suf = true := by
  match w with
  | [] =>
    show (false : Bool) = true ↔ ∃ suf, ([] : List α) ≠ [] ∧ [] ++ suf = s ∧ rec suf = true
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨_, hne, _, _⟩; exact absurd rfl hne
  | a :: w' =>
    show (match splitPrefix (a :: w') s with | some suf => rec suf | none => false) = true ↔ _
    rcases hsp : splitPrefix (a :: w') s with _ | suf
    · constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨suf, _, heq, _⟩
        have := splitPrefix_eq_some.mpr heq
        rw [this] at hsp; exact absurd hsp (by simp)
    · constructor
      · intro h; exact ⟨suf, by simp, splitPrefix_eq_some.mp hsp, h⟩
      · rintro ⟨suf', _, heq, hr⟩
        have heq2 : splitPrefix (a :: w') s = some suf' := splitPrefix_eq_some.mpr heq
        rw [heq2, Option.some.injEq] at hsp
        rw [← hsp]; exact hr

/-- Fold `contrib` over every dictionary word: is there SOME word that peels off `s`'s front and
    leaves a suffix on which `rec` succeeds? -/
def stepBreak (dict : List (List α)) (rec : List α → Bool) (s : List α) : Bool :=
  dict.any (contrib rec s)

theorem stepBreak_true_iff {dict : List (List α)} {rec : List α → Bool} {s : List α} :
    stepBreak dict rec s = true ↔ ∃ w ∈ dict, ∃ suf, w ≠ [] ∧ w ++ suf = s ∧ rec suf = true := by
  show dict.any (contrib rec s) = true ↔ _
  rw [List.any_eq_true]
  constructor
  · rintro ⟨w, hw, hc⟩
    obtain ⟨suf, hne, heq, hr⟩ := contrib_true_iff.mp hc
    exact ⟨w, hw, suf, hne, heq, hr⟩
  · rintro ⟨w, hw, suf, hne, heq, hr⟩
    exact ⟨w, hw, contrib_true_iff.mpr ⟨suf, hne, heq, hr⟩⟩

/-- **The DP with an explicit FUEL bound** (S13): structural recursion on the fuel, so it is
    kernel-reducible and `decide`-friendly. `fuel = s.length` always suffices, since each peeled
    word is nonempty so the remaining suffix strictly shortens. -/
def wordBreakFuel (dict : List (List α)) : Nat → List α → Bool
  | 0, s => match s with
    | [] => true
    | _ :: _ => false
  | fuel + 1, s => match s with
    | [] => true
    | _ :: _ => stepBreak dict (wordBreakFuel dict fuel) s

/-- **The allegory program's answer function.** -/
def wordBreakFn (dict : List (List α)) (s : List α) : Bool := wordBreakFuel dict s.length s

/-! ## Specification: an inductive segmentation-witness family -/

/-- `Seg dict s` — `s` splits into a sequence of ONE OR MORE nonempty dictionary words, reuse
    allowed: the honest reading of "word break", not a tautology. -/
inductive Seg (dict : List (List α)) : List α → Prop where
  | nil : Seg dict []
  | cons {w suf : List α} (hw : w ∈ dict) (hne : w ≠ []) (hs : Seg dict suf) :
      Seg dict (w ++ suf)

/-- One-step unfolding of `Seg`, matching `stepBreak`'s shape. -/
theorem seg_iff {dict : List (List α)} {s : List α} :
    Seg dict s ↔ s = [] ∨ ∃ w ∈ dict, ∃ suf, w ≠ [] ∧ w ++ suf = s ∧ Seg dict suf := by
  constructor
  · intro h
    cases h with
    | nil => exact Or.inl rfl
    | cons hw hne hs => exact Or.inr ⟨_, hw, _, hne, rfl, hs⟩
  · rintro (rfl | ⟨w, hw, suf, hne, heq, hs⟩)
    · exact Seg.nil
    · rw [← heq]; exact Seg.cons hw hne hs

/-! ## Correctness: `wordBreakFuel` computes exactly `Seg` -/

/-- **Core correctness lemma**: for any sufficient fuel `s.length ≤ fuel`, `wordBreakFuel dict fuel
    s` decides `Seg dict s` — by induction on `fuel` (the `L322`-`dpFuel_spec` shape). -/
theorem wordBreakFuel_correct (dict : List (List α)) :
    ∀ fuel s, s.length ≤ fuel → (wordBreakFuel dict fuel s = true ↔ Seg dict s) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs
    cases s with
    | nil =>
      show (true : Bool) = true ↔ Seg dict []
      exact ⟨fun _ => Seg.nil, fun _ => rfl⟩
    | cons a s' => simp at hs
  | succ fuel ih =>
    intro s hs
    cases s with
    | nil =>
      show (true : Bool) = true ↔ Seg dict []
      exact ⟨fun _ => Seg.nil, fun _ => rfl⟩
    | cons a s' =>
      show stepBreak dict (wordBreakFuel dict fuel) (a :: s') = true ↔ Seg dict (a :: s')
      rw [stepBreak_true_iff, seg_iff]
      have hs' : s'.length ≤ fuel := by
        have : (a :: s').length ≤ fuel + 1 := hs
        simpa using this
      constructor
      · rintro ⟨w, hw, suf, hne, heq, hr⟩
        refine Or.inr ⟨w, hw, suf, hne, heq, ?_⟩
        have hwpos : 1 ≤ w.length := by
          cases w with
          | nil => exact absurd rfl hne
          | cons _ w'' => simp
        have hlen : w.length + suf.length = s'.length + 1 := by
          have := congrArg List.length heq
          simpa using this
        exact (ih suf (by omega)).mp hr
      · rintro (h | ⟨w, hw, suf, hne, heq, hs2⟩)
        · exact absurd h (by simp)
        · refine ⟨w, hw, suf, hne, heq, ?_⟩
          have hwpos : 1 ≤ w.length := by
            cases w with
            | nil => exact absurd rfl hne
            | cons _ w'' => simp
          have hlen : w.length + suf.length = s'.length + 1 := by
            have := congrArg List.length heq
            simpa using this
          exact (ih suf (by omega)).mpr hs2

/-- **Correctness of the allegory program**: `wordBreakFn` decides exactly the segmentation
    predicate `Seg`. -/
theorem wordBreak_correct (dict : List (List α)) (s : List α) :
    wordBreakFn dict s = true ↔ Seg dict s :=
  wordBreakFuel_correct dict s.length s (Nat.le_refl s.length)

/-! ## `Rel(Set)` packaging (instantiated at `Char`, so `decide` examples read as words) -/

/-- The input object: a dictionary of words paired with the target string. -/
abbrev dInput : RelSet.{0} := ⟨List (List Char) × List Char⟩
/-- The answer object: booleans. -/
abbrev dAns : RelSet.{0} := ⟨Bool⟩

/-- **The allegory program**: LeetCode 139's solution as a morphism `dInput ⟶ dAns`. -/
def solve : dInput ⟶ dAns := graph (fun p => wordBreakFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map _

/-- The **specification** as a morphism `dInput ⟶ dAns`: `b` is THE correct boolean answer to
    "can `s` be segmented into dictionary words?" -/
def spec : dInput ⟶ dAns := fun p b => (b = true ↔ Seg p.1 p.2)

/-- Two booleans that agree on being `true` are equal (Bool extensionality). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **`solve` equals `spec` as relations** (the allegory-program correctness statement). -/
theorem solve_eq_spec : solve = spec := by
  apply RelSet.hom_ext; intro p b
  show (b = wordBreakFn p.1 p.2) ↔ (b = true ↔ Seg p.1 p.2)
  constructor
  · intro h; rw [h]; exact wordBreak_correct p.1 p.2
  · intro h
    have h' : (b = true) ↔ (wordBreakFn p.1 p.2 = true) := h.trans (wordBreak_correct p.1 p.2).symm
    exact bool_eq_of_iff_true h'

/-! ## Running the program -/

example : wordBreakFn (["leet".toList, "code".toList]) "leetcode".toList = true := by decide
example : wordBreakFn (["apple".toList, "pen".toList]) "applepenapple".toList = true := by decide
example :
    wordBreakFn (["cats".toList, "dog".toList, "sand".toList, "and".toList, "cat".toList])
      "catsandog".toList = false := by decide
example : wordBreakFn ([] : List (List Char)) ([] : List Char) = true := by decide
example : wordBreakFn (["a".toList]) ([] : List Char) = true := by decide

end Freyd.Alg.RelSet.LC139
