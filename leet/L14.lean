/-
  LeetCode 14 — Longest Common Prefix — as an ALLEGORY PROGRAM.

  Problem: given `strs : List (List Int)` (strings as code-lists), return their longest common
  prefix.

  1. **Program** — `commonPrefix2 a b` is the longest shared prefix of two lists (structural
     recursion, peeling matching heads); `lcpFn` folds `commonPrefix2` right-to-left over `strs`,
     `[] ↦ []`, a singleton returned verbatim.
  2. **Specification** — Lean core's `List.IsPrefix` (`<+:`, `p <+: s ↔ ∃ t, p ++ t = s`) IS the
     honest "is a prefix of" relation; no hand-rolled substitute needed.  LeetCode's "the
     LONGEST common prefix" is the `<+:`-GREATEST element of `{p | ∀ s ∈ strs, p <+: s}` — the
     prefix order itself is the extremum, no numeric `max` required.
  3. **Correctness** — soundness (`lcpFn strs` is itself a common prefix, unconditional) and
     maximality (every common prefix of `strs` is a prefix of `lcpFn strs`), both riding on one
     crux fact about `commonPrefix2`: it is the `<+:`-meet of two lists — itself a common prefix
     of both (`commonPrefix2_prefix`), and dominated below by every OTHER common prefix
     (`commonPrefix2_greatest`).  Maximality genuinely needs `strs ≠ []` (LeetCode's own
     constraint `1 ≤ strs.length`) — see the note on `lcp_max` below for why the empty case is
     NOT "vacuously true" as one might first assume.

  Mathlib-free; fully constructive — axioms `{propext, Quot.sound}` (the `Rel(Set)` packaging's
  usual cost; the core `lcp_correct` theorem itself needs neither).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC14

open Freyd List

/-! ## The program -/

/-- The longest shared prefix of two code-lists, by structural recursion on the first list. -/
def commonPrefix2 : List Int → List Int → List Int
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => if x = y then x :: commonPrefix2 xs ys else []

/-- **The program**: the longest common prefix of a list of code-lists, folding `commonPrefix2`
    right-to-left; `[] ↦ []`, a singleton returns itself verbatim. -/
def lcpFn : List (List Int) → List Int
  | [] => []
  | [s] => s
  | s :: rest => commonPrefix2 s (lcpFn rest)

/-! ## Crux lemma: `commonPrefix2` is the `<+:`-meet (greatest common lower bound) of two lists -/

/-- `commonPrefix2 a b` is itself a common prefix of `a` and `b`. -/
theorem commonPrefix2_prefix :
    ∀ a b : List Int, commonPrefix2 a b <+: a ∧ commonPrefix2 a b <+: b := by
  intro a
  induction a with
  | nil => intro b; exact ⟨prefix_rfl, nil_prefix⟩
  | cons x xs ih =>
    intro b
    cases b with
    | nil => exact ⟨nil_prefix, prefix_rfl⟩
    | cons y ys =>
      show commonPrefix2 (x :: xs) (y :: ys) <+: x :: xs ∧
           commonPrefix2 (x :: xs) (y :: ys) <+: y :: ys
      unfold commonPrefix2
      split
      · rename_i heq
        obtain ⟨ih1, ih2⟩ := ih ys
        exact ⟨cons_prefix_cons.mpr ⟨rfl, ih1⟩, cons_prefix_cons.mpr ⟨heq, ih2⟩⟩
      · exact ⟨nil_prefix, nil_prefix⟩

/-- **`commonPrefix2` is the GREATEST common prefix** of `a` and `b`: every OTHER common prefix
    `p` of `a` and `b` is itself a prefix of `commonPrefix2 a b`.  Together with
    `commonPrefix2_prefix`, `commonPrefix2 a b` is the meet of `a`, `b` under `<+:`. -/
theorem commonPrefix2_greatest :
    ∀ a b p : List Int, p <+: a → p <+: b → p <+: commonPrefix2 a b := by
  intro a
  induction a with
  | nil =>
    intro b p hpa _
    have hp : p = [] := prefix_nil.mp hpa
    subst hp; exact nil_prefix
  | cons x xs ih =>
    intro b p hpa hpb
    cases b with
    | nil =>
      have hp : p = [] := prefix_nil.mp hpb
      subst hp; exact nil_prefix
    | cons y ys =>
      show p <+: commonPrefix2 (x :: xs) (y :: ys)
      unfold commonPrefix2
      split
      · cases p with
        | nil => exact nil_prefix
        | cons pz pt =>
          obtain ⟨hpz, hpxs⟩ := cons_prefix_cons.mp hpa
          obtain ⟨_, hpys⟩ := cons_prefix_cons.mp hpb
          exact cons_prefix_cons.mpr ⟨hpz, ih ys pt hpxs hpys⟩
      · rename_i hne
        cases p with
        | nil => exact nil_prefix
        | cons pz pt =>
          obtain ⟨hpz, _⟩ := cons_prefix_cons.mp hpa
          obtain ⟨hpz', _⟩ := cons_prefix_cons.mp hpb
          exact absurd (hpz.symm.trans hpz') hne

/-! ## Correctness: soundness (unconditional) and maximality (`strs ≠ []`) -/

/-- **Soundness**: `lcpFn strs` is a common prefix of every string in `strs` — holds
    unconditionally, even at `strs = []` (vacuously, there is no `s` to check). -/
theorem lcp_sound : ∀ strs : List (List Int), ∀ s ∈ strs, lcpFn strs <+: s := by
  intro strs
  induction strs with
  | nil => intro s hs; exact absurd hs not_mem_nil
  | cons s rest ih =>
    cases rest with
    | nil =>
      intro t ht
      have ht' : t = s := mem_singleton.mp ht
      subst ht'; exact prefix_rfl
    | cons s2 rest2 =>
      intro t ht
      rcases mem_cons.mp ht with heq | hmem
      · rw [heq]; exact (commonPrefix2_prefix s (lcpFn (s2 :: rest2))).1
      · exact IsPrefix.trans (commonPrefix2_prefix s (lcpFn (s2 :: rest2))).2 (ih t hmem)

/-- **Maximality**: every common prefix `p` of a NONEMPTY `strs` is a prefix of `lcpFn strs` —
    i.e. `lcpFn strs` is the `<+:`-GREATEST common prefix, matching "LONGEST".  `strs ≠ []` is
    load-bearing here, and NOT for the reason one might first guess: at `strs = []` the
    hypothesis `∀ s ∈ strs, p <+: s` is vacuously TRUE for *every* `p` (there is no `s` to
    falsify it against), so unrestricted maximality would force `p <+: lcpFn [] = []`, i.e.
    `p = []`, for an ARBITRARY `p` — which is simply false (take `p = [1]`).  The vacuous
    HYPOTHESIS does not make the CONCLUSION vacuous; only the hypothesis-side is vacuous. Adding
    `strs ≠ []` is exactly LeetCode's own constraint `1 ≤ strs.length`. -/
theorem lcp_max : ∀ strs : List (List Int), strs ≠ [] →
    ∀ p, (∀ s ∈ strs, p <+: s) → p <+: lcpFn strs := by
  intro strs
  induction strs with
  | nil => intro hne; exact absurd rfl hne
  | cons s rest ih =>
    intro _ p hall
    cases rest with
    | nil => exact hall s mem_cons_self
    | cons s2 rest2 =>
      have hps : p <+: s := hall s mem_cons_self
      have hallRest : ∀ t ∈ s2 :: rest2, p <+: t := fun t ht => hall t (mem_cons_of_mem s ht)
      have hpRest : p <+: lcpFn (s2 :: rest2) := ih (cons_ne_nil s2 rest2) p hallRest
      exact commonPrefix2_greatest s (lcpFn (s2 :: rest2)) p hps hpRest

/-- **Headline**: `lcpFn` computes the longest common prefix of a nonempty list of strings —
    soundness (it IS a common prefix) and maximality (it is the LONGEST one). -/
theorem lcp_correct (strs : List (List Int)) (hne : strs ≠ []) :
    (∀ s ∈ strs, lcpFn strs <+: s) ∧ (∀ p, (∀ s ∈ strs, p <+: s) → p <+: lcpFn strs) :=
  ⟨lcp_sound strs, lcp_max strs hne⟩

/-! ## `Rel(Set)` packaging -/

/-- The input object: the list of strings to find the longest common prefix of. -/
abbrev dInput : RelSet.{0} := ⟨List (List Int)⟩
/-- The answer object: the longest common prefix. -/
abbrev dAns : RelSet.{0} := ⟨List Int⟩

/-- **The allegory program**: LeetCode 14's LCP as a morphism `dInput ⟶ dAns` in `Rel(Set)`. -/
def solve : dInput ⟶ dAns := graph lcpFn

/-- `solve` is a `Map` — a genuine function, via the `graph`/`Map` route. -/
theorem solve_map : Map solve := graph_map lcpFn

/-! ## The morphism-equation headline (LCP = the unique `<+:`-greatest common prefix) -/

/-- **Antisymmetry of the prefix order** (mathlib-free): mutual prefixes are equal — the surplus
    tail has length `0`.  This is what makes the greatest common prefix UNIQUE, so the spec pins it. -/
theorem prefix_antisymm {p q : List Int} (h1 : p <+: q) (h2 : q <+: p) : p = q := by
  obtain ⟨s, hs⟩ := h1
  have hlen := congrArg List.length hs
  rw [List.length_append] at hlen
  have hle : q.length ≤ p.length := h2.length_le
  have hs0 : s.length = 0 := by omega
  rw [List.length_eq_zero_iff.mp hs0, List.append_nil] at hs
  exact hs

/-- The precondition coreflexive: the sub-identity passing only NONEMPTY string lists (LeetCode
    14's constraint `1 ≤ strs.length`). -/
def pre : dInput ⟶ dInput := fun strs strs' => strs = strs' ∧ strs ≠ []

/-- **The specification** as a morphism `dInput ⟶ dAns`: `out` is a common prefix of every string
    and the `<+:`-GREATEST such — i.e. THE longest common prefix — stated independently of `lcpFn`. -/
def spec : dInput ⟶ dAns :=
  fun strs out => strs ≠ [] ∧ (∀ s ∈ strs, out <+: s) ∧ (∀ p, (∀ s ∈ strs, p <+: s) → p <+: out)

/-- **The allegory-program headline**: `pre ≫ solve = spec` — on nonempty inputs the fold `solve`
    is exactly the longest-common-prefix spec, pinned by prefix antisymmetry. -/
theorem pre_solve_eq_spec : pre ≫ solve = spec := by
  apply hom_ext; intro strs out
  constructor
  · rintro ⟨ys, ⟨rfl, hne⟩, hv⟩
    have hv' : out = lcpFn strs := hv
    exact ⟨hne, by rw [hv']; exact lcp_sound strs, by rw [hv']; exact lcp_max strs hne⟩
  · rintro ⟨hne, hsound, hmax⟩
    refine ⟨strs, ⟨rfl, hne⟩, ?_⟩
    show out = lcpFn strs
    exact prefix_antisymm (lcp_max strs hne out hsound) (hmax (lcpFn strs) (lcp_sound strs))

/-! ## Running the program (ASCII code-lists) -/

/-- `["flower","flow","flight"] → "fl"`. -/
example : lcpFn [[102, 108, 111, 119, 101, 114], [102, 108, 111, 119], [102, 108, 105, 103, 104, 116]]
    = [102, 108] := by decide

/-- `["dog","racecar","car"] → ""`. -/
example : lcpFn [[100, 111, 103], [114, 97, 99, 101, 99, 97, 114], [99, 97, 114]] = [] := by decide

end Freyd.Alg.RelSet.LC14
