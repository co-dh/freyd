/-
  LeetCode 435 — Non-overlapping Intervals — as an ALLEGORY PROGRAM.

  Problem: given intervals `(lo, hi) : Int × Int`, each `lo < hi` (LeetCode 435's actual
  constraint is the STRICT `starti < endi`, not merely `lo ≤ hi` — this matters: with degenerate
  `lo = hi` point intervals the greedy-by-end-time exchange argument below has a genuine edge
  case, see the `Valid` docstring), return the MINIMUM number of intervals to remove so the rest
  are pairwise non-overlapping.  Touching endpoints are allowed (`[1,2]`/`[2,3]` do NOT overlap):
  overlap is the STRICT `a.lo < b.hi ∧ b.lo < a.hi`.

  Same recipe as `leet/L56.lean` (Merge Intervals) and the greedy-scan family (`leet/L55.lean`,
  `leet/L213.lean`, `Freyd/leetcode.md` S22/S19):

  1. **Data** — `List (Int × Int)`, `.1` = lo, `.2` = hi (no `SnocList` engine needed, as L56).

  2. **Program** — `solveFn ivs = ivs.length - (keptSorted (isortH ivs)).length`: `isortH` sorts
     by `.2` (end time, insertion sort ported from `L56`'s `isort`/`linsert`), then `keptSorted` is
     the standard greedy LEFT-TO-RIGHT scan over the end-sorted list: always take the first
     interval, then keep the next one iff its `.1 ≥` the running kept interval's `.2`.
     `keptSorted`/`keptList` return the ACTUAL kept sublist (not just a count), so achievability
     is a genuine witness, not merely a numeral.

  3. **Specification** — the honest one: `keptSorted (isortH ivs)`'s LENGTH is the MAXIMUM size of
     a pairwise non-overlapping sub-selection of `ivs`; "min removals" is `length − max`.  A
     "sub-selection" is `List.Sublist` (`<+`, Lean core, an order-preserving sub-list — the right
     multiplicity-respecting notion of "a subset of the given intervals", unlike `⊆` which would
     ignore duplicate copies); "pairwise non-overlapping" is `List.Pairwise NoOverlap` (Lean core).
     Correctness (`solve_correct`) is BOTH halves:
       - **achievability**: some `sub <+ ivs` is `NonOverlap` and has length `ivs.length -
         solveFn ivs`;
       - **optimality/domination**: EVERY `sub <+ ivs` that is `NonOverlap` has length `≤
         ivs.length − solveFn ivs` — i.e. no smaller number of removals ever works.

  4. **The real content — the exchange argument.**  The greedy scan is defined and analysed on
     the SORTED list `isortH ivs`, where "keep the sorted list's own head" is manifestly the
     locally-min-`.2` choice (`keptList_dom`, an induction generalizing an external threshold
     `lastEnd`, mirroring `L56`'s `mergeRun_inv`).  The one genuinely delicate fact
     (`keptList_length_mono`/`keptList_length_step`, proved by a SINGLE combined induction because
     each needs the other in one case) is that raising the greedy's starting threshold from `t` to
     a larger `t'` can (a) never INCREASE the kept count (`_mono`, needs `SortedH`+`Valid` only)
     and (b) never DECREASE it by more than ONE, provided every remaining interval's `.2 ≥ t'`
     (`_step` — exactly the situation right after skipping one incompatible head).  Since an
     arbitrary competing `sub` need not be phrased on the SORTED list at all, the bridge back to
     the ORIGINAL `ivs` is Lean core's `List.exists_perm_sublist` (`l₁ <+ l₂ → l₂ ~ l₂' → ∃ l₁', l₁'
     ~ l₁ ∧ l₁' <+ l₂'`) applied to the permutation `ivs ~ isortH ivs` (`ivs_perm_isortH`, a direct
     port of the classical "insertion sort is a permutation" induction) — this reduces "an
     arbitrary sub-selection of the UNSORTED `ivs`" to "a same-length, same-`NonOverlap`-ness
     sub-selection of the SORTED list" for free, with NO hand-rolled sublist-of-a-sort lemma
     needed.  `List.Pairwise`'s own `Perm.pairwise_iff`/`Pairwise.perm` (for the symmetric relation
     `NoOverlap`) transports `NonOverlap` across that same permutation.

  Mathlib-free (only Lean core `Init` — `List.Sublist`, `List.Perm`, `List.Pairwise` — plus
  `AOP.A6_1_RelSet`).  No `Classical.choice`; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

namespace Freyd.Alg.RelSet.LC435

open Freyd List

/-! ## Mathlib-free `Int` min (as in `L121`/`L56`) -/

def imin (a b : Int) : Int := if a ≤ b then a else b
theorem imin_le_left (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega

/-! ## Data: intervals as a plain list of `Int × Int` (`.1` = lo, `.2` = hi) -/

/-- The object of interval lists in `Rel(Set)`. -/
abbrev Ivs : RelSet.{0} := ⟨List (Int × Int)⟩
/-- The answer object: a natural number (a count of removals). -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-- Every interval in `l` is valid: `lo < hi`, STRICTLY — LeetCode 435's actual constraint
    (`-5·10⁴ ≤ starti < endi ≤ 5·10⁴`).  This is load-bearing, not cosmetic: with a degenerate
    `lo = hi` point interval `m`, `m` could tie for minimum `.2` with a longer interval `j` ending
    at the very same point while `j.lo < m.lo`, and `NoOverlap m j` holds vacuously (touching only
    at that shared point) WITHOUT giving `m.2 ≤ j.1` — the fact the greedy's threshold-passing
    step below needs.  Strict validity rules this out: `m.1 < m.2 ≤ j.2` forces the "vacuous" case
    of `NoOverlap` closed, leaving exactly `m.2 ≤ j.1`. -/
def Valid (l : List (Int × Int)) : Prop := ∀ iv ∈ l, iv.1 < iv.2

/-- Strict overlap (the book/problem's own test): `a` and `b` genuinely overlap iff `a.lo < b.hi`
    and `b.lo < a.hi`. -/
def Overlap (a b : Int × Int) : Prop := a.1 < b.2 ∧ b.1 < a.2
/-- Non-overlap: touching endpoints (`[1,2]`/`[2,3]`) are allowed. -/
def NoOverlap (a b : Int × Int) : Prop := ¬ Overlap a b

theorem noOverlap_symm {a b : Int × Int} (h : NoOverlap a b) : NoOverlap b a :=
  fun hba => h ⟨hba.2, hba.1⟩

/-- Pairwise (ALL pairs, not just adjacent) non-overlap — Lean core's `List.Pairwise` applied to
    the symmetric relation `NoOverlap` (so `Perm.pairwise_iff` transports it across a
    reordering, e.g. across the sort, for free — no hand-rolled permutation lemma needed). -/
abbrev NonOverlap (l : List (Int × Int)) : Prop := List.Pairwise NoOverlap l

/-- `SortedH l`: `l` is non-decreasing in `.2` (end time) — each head's `.2` is `≤` EVERY later
    element's `.2` (all-pairs, definitional, as `L56`'s `Sorted`). -/
def SortedH : List (Int × Int) → Prop
  | [] => True
  | iv :: rest => (∀ jv ∈ rest, iv.2 ≤ jv.2) ∧ SortedH rest

/-! ## Step 1 of the program: insertion sort by `.2` (`L56`'s `linsert`/`isort`, ported to `.2`) -/

/-- Insert `iv` into an already-`SortedH` list at the correct position (by `.2`). -/
def linsertH (iv : Int × Int) : List (Int × Int) → List (Int × Int)
  | [] => [iv]
  | iv' :: rest => if iv.2 ≤ iv'.2 then iv :: iv' :: rest else iv' :: linsertH iv rest

/-- Insertion sort by `.2`. -/
def isortH : List (Int × Int) → List (Int × Int)
  | [] => []
  | iv :: rest => linsertH iv (isortH rest)

theorem linsertH_mem (iv : Int × Int) (l : List (Int × Int)) (x : Int × Int) :
    x ∈ linsertH iv l ↔ x = iv ∨ x ∈ l := by
  induction l with
  | nil => simp [linsertH]
  | cons iv' rest ih =>
    show x ∈ (if iv.2 ≤ iv'.2 then iv :: iv' :: rest else iv' :: linsertH iv rest)
        ↔ x = iv ∨ x ∈ iv' :: rest
    split
    · rw [List.mem_cons]
    · rw [List.mem_cons, ih, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem linsertH_allGe (iv : Int × Int) (l : List (Int × Int)) (b : Int) (hb : b ≤ iv.2)
    (hl : ∀ jv ∈ l, b ≤ jv.2) : ∀ jv ∈ linsertH iv l, b ≤ jv.2 := by
  intro jv hjv
  rcases (linsertH_mem iv l jv).mp hjv with h | h
  · rw [h]; exact hb
  · exact hl jv h

theorem linsertH_sortedH (iv : Int × Int) (l : List (Int × Int)) (hl : SortedH l) :
    SortedH (linsertH iv l) := by
  induction l with
  | nil => exact ⟨fun jv hjv => (List.not_mem_nil hjv).elim, trivial⟩
  | cons iv' rest ih =>
    obtain ⟨hge, hsr⟩ := hl
    show SortedH (if iv.2 ≤ iv'.2 then iv :: iv' :: rest else iv' :: linsertH iv rest)
    split
    · rename_i h
      refine ⟨fun jv hjv => ?_, hge, hsr⟩
      rcases List.mem_cons.mp hjv with h' | h'
      · rw [h']; exact h
      · have := hge jv h'; omega
    · rename_i h
      exact ⟨linsertH_allGe iv rest iv'.2 (by omega) hge, ih hsr⟩

theorem isortH_mem (l : List (Int × Int)) (x : Int × Int) : x ∈ isortH l ↔ x ∈ l := by
  induction l with
  | nil => simp [isortH]
  | cons iv rest ih =>
    show x ∈ linsertH iv (isortH rest) ↔ x ∈ iv :: rest
    rw [linsertH_mem, ih, List.mem_cons]

theorem isortH_sortedH (l : List (Int × Int)) : SortedH (isortH l) := by
  induction l with
  | nil => trivial
  | cons iv rest ih => exact linsertH_sortedH iv (isortH rest) ih

theorem valid_isortH (l : List (Int × Int)) (hval : Valid l) : Valid (isortH l) :=
  fun iv hiv => hval iv ((isortH_mem l iv).mp hiv)

/-- **`isortH` is a permutation of its input** (the classical "insertion sort permutes" fact),
    proved directly via `List.Perm`'s constructors — the bridge that lets us transport facts
    between `ivs` and `isortH ivs` for free (`List.exists_perm_sublist`, `Perm.pairwise_iff`). -/
theorem cons_perm_linsertH (iv : Int × Int) (l : List (Int × Int)) : iv :: l ~ linsertH iv l := by
  induction l with
  | nil => exact List.Perm.refl [iv]
  | cons iv' rest ih =>
    show iv :: iv' :: rest ~ (if iv.2 ≤ iv'.2 then iv :: iv' :: rest else iv' :: linsertH iv rest)
    split
    · exact List.Perm.refl _
    · exact (List.Perm.swap iv' iv rest).trans (ih.cons iv')

theorem ivs_perm_isortH (l : List (Int × Int)) : l ~ isortH l := by
  induction l with
  | nil => exact List.Perm.nil
  | cons iv rest ih =>
    show iv :: rest ~ linsertH iv (isortH rest)
    exact (ih.cons iv).trans (cons_perm_linsertH iv (isortH rest))

/-! ## Step 2 of the program: the greedy run over the end-sorted list -/

/-- `keptList lastEnd l` — the actual kept sub-selection: walk `l` (assumed to come after a
    running kept interval ending at `lastEnd`), keeping `iv` (and advancing `lastEnd := iv.2`) iff
    `lastEnd ≤ iv.1`. -/
def keptList (lastEnd : Int) : List (Int × Int) → List (Int × Int)
  | [] => []
  | iv :: rest => if lastEnd ≤ iv.1 then iv :: keptList iv.2 rest else keptList lastEnd rest

/-- The defining unfold of `keptList` at a `cons`, as an explicit rewrite lemma (so `rw`/`split`
    can see the `if`, since a bare application of `keptList` doesn't display it syntactically). -/
theorem keptList_cons_eq (lastEnd : Int) (iv : Int × Int) (rest : List (Int × Int)) :
    keptList lastEnd (iv :: rest) =
      if lastEnd ≤ iv.1 then iv :: keptList iv.2 rest else keptList lastEnd rest := rfl

/-- Seed the greedy scan from the sorted list's own head (always kept — no prior constraint). -/
def keptSorted : List (Int × Int) → List (Int × Int)
  | [] => []
  | iv :: rest => iv :: keptList iv.2 rest

/-! ### `keptList`/`keptSorted` return an actual sub-selection (`Sublist`) -/

theorem keptList_sublist : ∀ (lastEnd : Int) (l : List (Int × Int)), keptList lastEnd l <+ l := by
  intro lastEnd l
  induction l generalizing lastEnd with
  | nil => exact List.Sublist.refl []
  | cons iv rest ih =>
    show (if lastEnd ≤ iv.1 then iv :: keptList iv.2 rest else keptList lastEnd rest) <+ iv :: rest
    split
    · exact (ih iv.2).cons₂ iv
    · exact (ih lastEnd).cons iv

theorem keptSorted_sublist (l : List (Int × Int)) : keptSorted l <+ l := by
  cases l with
  | nil => exact List.Sublist.refl []
  | cons iv rest => exact (keptList_sublist iv.2 rest).cons₂ iv

/-! ### `keptList`/`keptSorted` are `NonOverlap`, and every kept element's `.1 ≥` the threshold

    Both facts by ONE combined induction (as `L56`'s `mergeRun_inv`): the `NonOverlap` conclusion
    in the "keep" step needs the "`.1 ≥` threshold" fact about the RECURSIVE call's own output to
    bridge past the newly-kept head to the rest of the output. -/

theorem keptList_inv : ∀ (l : List (Int × Int)) (lastEnd : Int), Valid l → SortedH l →
    NonOverlap (keptList lastEnd l) ∧ (∀ jv ∈ keptList lastEnd l, lastEnd ≤ jv.1) := by
  intro l
  induction l with
  | nil => intro lastEnd _ _; exact ⟨List.Pairwise.nil, fun jv hjv => (List.not_mem_nil hjv).elim⟩
  | cons iv rest ih =>
    intro lastEnd hval hsortH
    obtain ⟨hgehi, hsortHrest⟩ := hsortH
    have hvaliv : iv.1 < iv.2 := hval iv List.mem_cons_self
    have hvalrest : Valid rest := fun jv hjv => hval jv (List.mem_cons_of_mem iv hjv)
    show NonOverlap (if lastEnd ≤ iv.1 then iv :: keptList iv.2 rest else keptList lastEnd rest) ∧
        (∀ jv ∈ (if lastEnd ≤ iv.1 then iv :: keptList iv.2 rest else keptList lastEnd rest),
          lastEnd ≤ jv.1)
    split
    · rename_i hle
      obtain ⟨hno, hge⟩ := ih iv.2 hvalrest hsortHrest
      refine ⟨List.Pairwise.cons (fun jv hjv => ?_) hno, fun jv hjv => ?_⟩
      · -- `NoOverlap iv jv` for every kept `jv` from the recursive call: `iv.2 ≤ jv.1` (from
        -- `hge`) rules out `jv.1 < iv.2`, closing `Overlap iv jv`.
        have := hge jv hjv
        unfold NoOverlap Overlap; omega
      · rcases List.mem_cons.mp hjv with h | h
        · rw [h]; exact hle
        · have := hge jv h; omega
    · rename_i hnle
      exact ih lastEnd hvalrest hsortHrest

theorem keptSorted_nonOverlap (l : List (Int × Int)) (hval : Valid l) (hsortH : SortedH l) :
    NonOverlap (keptSorted l) := by
  cases l with
  | nil => exact List.Pairwise.nil
  | cons iv rest =>
    obtain ⟨hgehi, hsortHrest⟩ := hsortH
    have hvalrest : Valid rest := fun jv hjv => hval jv (List.mem_cons_of_mem iv hjv)
    obtain ⟨hno, hge⟩ := keptList_inv rest iv.2 hvalrest hsortHrest
    exact List.Pairwise.cons (fun jv hjv => by
      have := hge jv hjv; unfold NoOverlap Overlap; omega) hno

/-! ## The delicate arithmetic core: raising the greedy's threshold

    `keptList_length_mono`: raising the threshold never INCREASES the kept count.
    `keptList_length_step`: raising the threshold from `t` to `t'` never DECREASES the kept count
    by more than ONE, provided every remaining element's `.2 ≥ t'` (so at most the very FIRST
    threshold-sensitive pick can be lost; every subsequent pick's own `.1` already exceeds `t'`
    by the chain `.1 ≥ (previous pick's) .2 ≥ t'`).  Proved TOGETHER: each needs the other in one
    branch. -/

theorem keptList_length_combined : ∀ (l : List (Int × Int)), SortedH l → Valid l →
    (∀ t1 t2 : Int, t1 ≤ t2 → (keptList t2 l).length ≤ (keptList t1 l).length) ∧
    (∀ t t' : Int, (∀ y ∈ l, t' ≤ y.2) → t ≤ t' → (keptList t l).length ≤ 1 + (keptList t' l).length) := by
  intro l
  induction l with
  | nil =>
    intro _ _
    exact ⟨fun t1 t2 _ => Nat.le_refl 0, fun t t' _ _ => Nat.le_add_left 0 1⟩
  | cons x xs ih =>
    intro hsortH hval
    obtain ⟨hgehi, hsortHxs⟩ := hsortH
    have hvalx : x.1 < x.2 := hval x List.mem_cons_self
    have hvalxs : Valid xs := fun y hy => hval y (List.mem_cons_of_mem x hy)
    obtain ⟨monoxs, stepxs⟩ := ih hsortHxs hvalxs
    constructor
    · -- MONO
      intro t1 t2 ht12
      rw [keptList_cons_eq t2, keptList_cons_eq t1]
      by_cases h2 : t2 ≤ x.1
      · have h1 : t1 ≤ x.1 := by omega
        rw [if_pos h1, if_pos h2]
        exact Nat.le_refl _
      · rw [if_neg h2]
        by_cases h1 : t1 ≤ x.1
        · rw [if_pos h1]
          -- `(keptList t2 xs).length ≤ 1 + (keptList x.2 xs).length` via `stepxs` or `monoxs`,
          -- depending on where `t2` sits relative to `x.2`.
          simp only [List.length_cons]
          by_cases hxt2 : t2 ≤ x.2
          · have := stepxs t2 x.2 hgehi hxt2
            omega
          · have := monoxs x.2 t2 (by omega)
            omega
        · rw [if_neg h1]
          exact monoxs t1 t2 ht12
    · -- STEP
      intro t t' hallt' htt'
      have hallt'xs : ∀ y ∈ xs, t' ≤ y.2 := fun y hy => hallt' y (List.mem_cons_of_mem x hy)
      have hxt' : t' ≤ x.2 := hallt' x List.mem_cons_self
      rw [keptList_cons_eq t, keptList_cons_eq t']
      by_cases ht'x : t' ≤ x.1
      · have htx : t ≤ x.1 := by omega
        rw [if_pos htx, if_pos ht'x]
        simp only [List.length_cons]; omega
      · rw [if_neg ht'x]
        by_cases htx : t ≤ x.1
        · rw [if_pos htx]
          -- `x.1 < t'` and `t' ≤ x.2` (`hxt'`, unconditional) give `(keptList x.2 xs).length ≤
          -- (keptList t' xs).length` directly via `monoxs` — no further case split needed.
          simp only [List.length_cons]
          have := monoxs t' x.2 hxt'
          omega
        · rw [if_neg htx]
          exact stepxs t t' hallt'xs htt'

theorem keptList_length_mono (l : List (Int × Int)) (hsortH : SortedH l) (hval : Valid l)
    (t1 t2 : Int) (h : t1 ≤ t2) : (keptList t2 l).length ≤ (keptList t1 l).length :=
  (keptList_length_combined l hsortH hval).1 t1 t2 h

theorem keptList_length_step (l : List (Int × Int)) (hsortH : SortedH l) (hval : Valid l)
    (t t' : Int) (hall : ∀ y ∈ l, t' ≤ y.2) (h : t ≤ t') :
    (keptList t l).length ≤ 1 + (keptList t' l).length :=
  (keptList_length_combined l hsortH hval).2 t t' hall h

/-! ## Domination on the SORTED list: `keptList_dom` (an exchange argument, `L56`-style) -/

theorem keptList_dom : ∀ (l : List (Int × Int)), SortedH l → Valid l →
    ∀ (lastEnd : Int) (sub : List (Int × Int)), sub <+ l → NonOverlap sub →
    (∀ jv ∈ sub, lastEnd ≤ jv.1) → sub.length ≤ (keptList lastEnd l).length := by
  intro l
  induction l with
  | nil =>
    intro _ _ lastEnd sub hsub _ _
    have : sub = [] := List.sublist_nil.mp hsub
    subst this; simp [keptList]
  | cons iv0 rest ih =>
    intro hsortH hval lastEnd sub hsub hno hge
    obtain ⟨hgehi, hsortHrest⟩ := hsortH
    have hvaliv0 : iv0.1 < iv0.2 := hval iv0 List.mem_cons_self
    have hvalrest : Valid rest := fun jv hjv => hval jv (List.mem_cons_of_mem iv0 hjv)
    rw [keptList_cons_eq]
    cases hsub with
    | cons _ hsub' =>
      -- DROP: `sub <+ rest`, doesn't (necessarily) use `iv0`.
      have h1 := ih hsortHrest hvalrest lastEnd sub hsub' hno hge
      by_cases hle : lastEnd ≤ iv0.1
      · rw [if_pos hle]
        have hle2 : lastEnd ≤ iv0.2 := by omega
        have h2 := keptList_length_step rest hsortHrest hvalrest lastEnd iv0.2 hgehi hle2
        simp only [List.length_cons]
        omega
      · rw [if_neg hle]; exact h1
    | cons₂ _ hsub' =>
      -- KEEP: `sub = iv0 :: sub'`, `sub' <+ rest`.
      rename_i sub'
      have hle : lastEnd ≤ iv0.1 := hge iv0 List.mem_cons_self
      rw [if_pos hle]
      obtain ⟨hheadno, hno'⟩ := List.pairwise_cons.mp hno
      have hge' : ∀ jv ∈ sub', iv0.2 ≤ jv.1 := by
        intro jv hjv
        have hno2 := hheadno jv hjv
        have hjvrest : jv ∈ rest := hsub'.subset hjv
        have hhi := hgehi jv hjvrest
        -- `omega` on a NEGATED-CONJUNCTION hypothesis (`hno2 : ¬(_ ∧ _)`) silently pulls in
        -- `Classical.choice`; case-split via `Decidable` (`by_cases`) first instead (S3-style).
        by_cases h1 : iv0.1 < jv.2
        · by_cases h2 : jv.1 < iv0.2
          · exact absurd ⟨h1, h2⟩ hno2
          · omega
        · omega
      have h1 := ih hsortHrest hvalrest iv0.2 sub' hsub' hno' hge'
      simp only [List.length_cons]; omega

/-- Any finite list of intervals has SOME lower bound on its `.1` values (needed to invoke
    `keptList_dom` at the outer `keptSorted` level, where no such bound is given in advance). -/
theorem hasLB (l : List (Int × Int)) : ∃ b, ∀ jv ∈ l, b ≤ jv.1 := by
  induction l with
  | nil => exact ⟨0, fun jv hjv => (List.not_mem_nil hjv).elim⟩
  | cons a t ih =>
    obtain ⟨b', hb'⟩ := ih
    refine ⟨imin a.1 b', fun jv hjv => ?_⟩
    rcases List.mem_cons.mp hjv with h | h
    · rw [h]; exact imin_le_left a.1 b'
    · have h1 := hb' jv h; have h2 := imin_le_right a.1 b'; omega

/-- **Domination, top level**: any `NonOverlap` sub-selection of a `SortedH`+`Valid` list is no
    bigger than `keptSorted`'s own greedy choice. -/
theorem keptSorted_dom (l : List (Int × Int)) (hsortH : SortedH l) (hval : Valid l)
    (sub : List (Int × Int)) (hsub : sub <+ l) (hno : NonOverlap sub) :
    sub.length ≤ (keptSorted l).length := by
  cases l with
  | nil =>
    have : sub = [] := List.sublist_nil.mp hsub
    subst this; simp [keptSorted]
  | cons iv0 rest =>
    obtain ⟨hgehi, hsortHrest⟩ := hsortH
    have hvaliv0 : iv0.1 < iv0.2 := hval iv0 List.mem_cons_self
    have hvalrest : Valid rest := fun jv hjv => hval jv (List.mem_cons_of_mem iv0 hjv)
    show sub.length ≤ (iv0 :: keptList iv0.2 rest).length
    cases hsub with
    | cons _ hsub' =>
      -- DROP at the very top: `sub <+ rest`, unrelated to `iv0`; bound it at SOME lower bound
      -- `b` of `sub`, then cross to `iv0.2` via `mono`/`step` regardless of how `b` compares.
      obtain ⟨b, hb⟩ := hasLB sub
      have h1 := keptList_dom rest hsortHrest hvalrest b sub hsub' hno hb
      simp only [List.length_cons]
      by_cases hb2 : b ≤ iv0.2
      · have h2 := keptList_length_step rest hsortHrest hvalrest b iv0.2 hgehi hb2
        omega
      · have h2 := keptList_length_mono rest hsortHrest hvalrest iv0.2 b (by omega)
        omega
    | cons₂ _ hsub' =>
      rename_i sub'
      have hno' : NonOverlap sub' := (List.pairwise_cons.mp hno).2
      have hge' : ∀ jv ∈ sub', iv0.2 ≤ jv.1 := by
        intro jv hjv
        have hno2 := (List.pairwise_cons.mp hno).1 jv hjv
        have hjvrest : jv ∈ rest := hsub'.subset hjv
        have hhi := hgehi jv hjvrest
        by_cases h1 : iv0.1 < jv.2
        · by_cases h2 : jv.1 < iv0.2
          · exact absurd ⟨h1, h2⟩ hno2
          · omega
        · omega
      have h1 := keptList_dom rest hsortHrest hvalrest iv0.2 sub' hsub' hno' hge'
      simp only [List.length_cons]; omega

/-! ## The program and its correctness -/

/-- **The allegory program's underlying function**: min removals = total count minus the
    greedy's maximum non-overlapping kept count. -/
def solveFn (ivs : List (Int × Int)) : Nat := ivs.length - (keptSorted (isortH ivs)).length

theorem keptSorted_length_le (l : List (Int × Int)) : (keptSorted l).length ≤ l.length :=
  (keptSorted_sublist l).length_le

/-- **The bridge**: any `NonOverlap` sub-selection of `ivs` (order-preserving, multiplicity-
    respecting) transfers, via the permutation `ivs ~ isortH ivs`, to a same-length `NonOverlap`
    sub-selection of the SORTED list — reducing domination on the unsorted input to domination on
    the sorted one, entirely via Lean core's `List.exists_perm_sublist`/`Pairwise.perm` (no
    hand-rolled "sublist of a sort" lemma). -/
theorem sub_dom (ivs sub : List (Int × Int)) (hval : Valid ivs) (hsub : sub <+ ivs)
    (hno : NonOverlap sub) : sub.length ≤ (keptSorted (isortH ivs)).length := by
  obtain ⟨sub', hsub'perm, hsub'sub⟩ := List.exists_perm_sublist hsub (ivs_perm_isortH ivs)
  have hlen : sub'.length = sub.length := hsub'perm.length_eq
  have hno' : NonOverlap sub' := hno.perm hsub'perm.symm (fun h => noOverlap_symm h)
  have h1 := keptSorted_dom (isortH ivs) (isortH_sortedH ivs) (valid_isortH ivs hval)
    sub' hsub'sub hno'
  omega

/-- **Achievability**: `keptSorted (isortH ivs)` transfers, via the SAME permutation, to an
    actual `NonOverlap` sub-selection of `ivs` with the maximal length. -/
theorem sub_achievable (ivs : List (Int × Int)) (hval : Valid ivs) :
    ∃ sub, sub <+ ivs ∧ NonOverlap sub ∧ sub.length = (keptSorted (isortH ivs)).length := by
  obtain ⟨sub, hsubperm, hsubsub⟩ :=
    List.exists_perm_sublist (keptSorted_sublist (isortH ivs)) (ivs_perm_isortH ivs).symm
  refine ⟨sub, hsubsub, ?_, hsubperm.length_eq⟩
  exact (keptSorted_nonOverlap (isortH ivs) (valid_isortH ivs hval) (isortH_sortedH ivs)).perm
    hsubperm.symm (fun h => noOverlap_symm h)

/-! ## Correctness: `solveFn` is exactly the minimum number of removals -/

/-- **Correctness (headline)**: `solveFn ivs` is the minimum number of intervals to remove so the
    rest are pairwise non-overlapping.  Two halves, exactly LeetCode 435's own meaning:
    - achievability — removing `solveFn ivs` intervals IS achievable (some `sub <+ ivs` of size
      `ivs.length - solveFn ivs` is `NonOverlap`);
    - optimality — no smaller number of removals ever works (every `NonOverlap sub <+ ivs` has
      length `≤ ivs.length - solveFn ivs`, i.e. you can never KEEP more than that many). -/
theorem solve_correct (ivs : List (Int × Int)) (hval : Valid ivs) :
    (∃ sub, sub <+ ivs ∧ NonOverlap sub ∧ sub.length = ivs.length - solveFn ivs) ∧
    (∀ sub, sub <+ ivs → NonOverlap sub → sub.length ≤ ivs.length - solveFn ivs) := by
  have hk := keptSorted_length_le (isortH ivs)
  have hivslen : (isortH ivs).length = ivs.length := (ivs_perm_isortH ivs).symm.length_eq
  have hkle : (keptSorted (isortH ivs)).length ≤ ivs.length := hivslen ▸ hk
  have heq : ivs.length - solveFn ivs = (keptSorted (isortH ivs)).length := by
    unfold solveFn; omega
  rw [heq]
  exact ⟨sub_achievable ivs hval, fun sub hsub hno => sub_dom ivs sub hval hsub hno⟩

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The allegory program**: LeetCode 435's solution as a morphism `Ivs ⟶ ℕ` in `Rel(Set)`. -/
def solve : Ivs ⟶ dNat := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- **The program refines the specification**: whatever `solve` relates `ivs` to is the minimum
    number of removals, in the achievability+optimality sense of `solve_correct`. -/
theorem solve_correct' (ivs : List (Int × Int)) (n : Nat) (hval : Valid ivs) (h : solve ivs n) :
    (∃ sub, sub <+ ivs ∧ NonOverlap sub ∧ sub.length = ivs.length - n) ∧
    (∀ sub, sub <+ ivs → NonOverlap sub → sub.length ≤ ivs.length - n) := by
  have hn : n = solveFn ivs := h
  rw [hn]; exact solve_correct ivs hval

/-! ## Running the program -/

-- LeetCode 435's own example: `[[1,2],[2,3],[3,4],[1,3]] → 1` (remove `[1,3]`).
example : solveFn [(1, 2), (2, 3), (3, 4), (1, 3)] = 1 := by decide
-- `[[1,2],[1,2],[1,2]] → 2` (keep just one copy).
example : solveFn [(1, 2), (1, 2), (1, 2)] = 2 := by decide
-- Already pairwise non-overlapping (touching is fine): `[[1,2],[2,3]] → 0`.
example : solveFn [(1, 2), (2, 3)] = 0 := by decide

end Freyd.Alg.RelSet.LC435
