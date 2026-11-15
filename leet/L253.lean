/-
  LeetCode 253 — Meeting Rooms II — as an ALLEGORY PROGRAM.

  Problem: given meeting intervals `(lo, hi) : Int × Int` (`iv.1` start, `iv.2` end; a meeting
  occupies the HALF-OPEN instant range `[iv.1, iv.2)`), return the MINIMUM number of conference
  rooms required — equivalently, the MAXIMUM number of meetings that overlap at any single instant.

  Same recipe family as `leet/L56.lean` (Merge Intervals) and `leet/L252.lean` (Meeting Rooms),
  but the honest spec is a genuine EXTREMUM (`Freyd/leetcode.md` S0), not a decision or a
  structural output.

  Route (no event sweep, no sort needed): the maximum overlap over ALL instants is attained AT SOME
  MEETING'S START — so it suffices to compute, for each meeting's own start `s`, how many meetings
  cover `s`, and take the max over the (finite) list of starts.

  1. **Data** — `List (Int × Int)`, `.1` = start, `.2` = end (no `SnocList`/sort machinery needed).

  2. **Program** — `countCover ivs t` counts meetings occupying instant `t` (a `List.filter` on the
     half-open membership test, kept `decide`-able); `roomsFn ivs` is the max, over each meeting's
     OWN start, of `countCover ivs` at that start — a `Nat.max`-fold (`nmax`, ported from `L56`'s
     `imax` to control the rewrite set) over `ivs.map (countCover ivs ·.1)`.

  3. **Specification** — `roomsFn ivs` equals `max over ALL instants t of countCover ivs t`,
     phrased honestly as an achievability + domination pair (S0's extremum shape), with NO ordering
     hypothesis on `ivs` needed (the argument is purely combinatorial):
       - **domination** (`rooms_dominates`) — `∀ t, countCover ivs t ≤ roomsFn ivs`. The crux:
         among the (possibly empty) set `S` of meetings covering `t`, take a member `m` with the
         LATEST start (`exists_max_start`, a plain constructive "nonempty list has a max-by-key
         element", no `Classical.choice`). Since `m.1 ≤ t` (m covers `t`) and every other `iv ∈ S`
         has `t < iv.2`, we get `m.1 < iv.2` for every `iv ∈ S`; combined with `iv.1 ≤ m.1`
         (maximality of `m.1`), EVERY meeting covering `t` also covers `m.1` — so
         `countCover ivs t ≤ countCover ivs m.1 ≤ roomsFn ivs` (the last step since `m ∈ ivs` and
         `m.1` is literally one of the starts `roomsFn` maxes over).
       - **achievability** (`rooms_achievable`) — `∃ t, countCover ivs t = roomsFn ivs`. Immediate:
         `roomsFn ivs` is itself a `nmax`-fold of actual `countCover ivs (·.1)` values (or `0` when
         `ivs = []`, witnessed by any `t`, e.g. `0`), so it equals one of them
         (`foldMax_mem_or_nil`, a generic "the max of a Nat list, folded from `0`, is `0` or a list
         member" fact).

  4. **Correctness (headline)** — `rooms_correct : (∃ t, countCover ivs t = roomsFn ivs) ∧
     (∀ t, countCover ivs t ≤ roomsFn ivs)` — `roomsFn` IS `max over all instants of countCover`,
     not a restatement of the program.

  Mathlib-free (Lean core `List.filter`/`mem_filter`/`mem_map` + `AOP.A6_1_RelSet` only). No
  `Classical.choice`: the domination argument builds the max-by-`.1` witness constructively by list
  induction (never appeals to well-ordering/choice on an infinite index set — `t` ranges over `Int`,
  but the crux argument only ever needs the FINITE set of meetings, not the instants). The `Bool`
  filter predicate is read back to `Prop` via core's `of_decide_eq_true`/`decide_eq_true_eq`, never
  via `List.filter_eq_nil_iff` (the `Classical.choice`-pulling trap flagged in `leetcode.md` S28).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

namespace Freyd.Alg.RelSet.LC253

open Freyd

/-! ## Mathlib-free `Nat` max (so we control the rewrite lemmas, as in `L56`'s `imax`) -/

def nmax (a b : Nat) : Nat := if a ≤ b then b else a

theorem nmax_ge_left (a b : Nat) : a ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_ge_right (a b : Nat) : b ≤ nmax a b := by unfold nmax; split <;> omega
theorem nmax_eq_or (a b : Nat) : nmax a b = a ∨ nmax a b = b := by
  unfold nmax; split
  · exact Or.inr rfl
  · exact Or.inl rfl
theorem nmax_zero_right (a : Nat) : nmax a 0 = a := by unfold nmax; split <;> omega

/-! ## Data: intervals as a plain list of `Int × Int` (`.1` = start, `.2` = end) -/

/-- The object of interval lists in `Rel(Set)`. -/
abbrev Ivs : RelSet.{0} := ⟨List (Int × Int)⟩
/-- The answer object: a room count. -/
abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-! ## The program -/

/-- `countCover ivs t`: the number of meetings occupying the half-open instant `t` — i.e. those
    `iv` with `iv.1 ≤ t < iv.2`. Kept `decide`-able (a `Bool` filter), per `leetcode.md` S28. -/
def countCover (ivs : List (Int × Int)) (t : Int) : Nat :=
  (ivs.filter (fun iv => decide (iv.1 ≤ t ∧ t < iv.2))).length

/-- **The allegory program's underlying function**: the max, over each meeting's OWN start, of how
    many meetings cover that start. -/
def roomsFn (ivs : List (Int × Int)) : Nat :=
  (ivs.map (fun iv => countCover ivs iv.1)).foldr nmax 0

/-! ## Generic list facts (independent of intervals) -/

/-- **Constructive max-by-key on a nonempty (`hd :: l`) list.** No `Classical.choice`: the witness
    is built by structural induction, comparing the head against the recursively-obtained max of
    the tail. Quantifying over `hd :: l` (rather than a `l ≠ []` hypothesis) sidesteps the
    "`induction` under a hypothesis mentioning the scrutinee" motive trap. -/
theorem exists_max_start (hd : Int × Int) (l : List (Int × Int)) :
    ∃ m ∈ hd :: l, ∀ iv ∈ hd :: l, iv.1 ≤ m.1 := by
  induction l generalizing hd with
  | nil =>
    refine ⟨hd, List.mem_cons_self, fun iv hiv => ?_⟩
    rw [List.mem_singleton.mp hiv]
    exact Int.le_refl _
  | cons hd2 tl ih =>
    obtain ⟨m, hm, hmax⟩ := ih hd2
    by_cases h : hd.1 ≤ m.1
    · refine ⟨m, List.mem_cons_of_mem hd hm, fun iv hiv => ?_⟩
      rcases List.mem_cons.mp hiv with rfl | hiv'
      · exact h
      · exact hmax iv hiv'
    · refine ⟨hd, List.mem_cons_self, fun iv hiv => ?_⟩
      rcases List.mem_cons.mp hiv with rfl | hiv'
      · exact Int.le_refl _
      · have := hmax iv hiv'; omega

/-- Filtering by a pointwise-implied predicate can only shrink the count. -/
theorem filter_length_le_of_imp (p q : Int × Int → Bool) (l : List (Int × Int))
    (h : ∀ iv ∈ l, p iv → q iv) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons iv rest ih =>
    have ihr := ih (fun jv hjv => h jv (List.mem_cons_of_mem iv hjv))
    by_cases hp : p iv
    · have hq : q iv := h iv List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq, List.length_cons, List.length_cons]
      omega
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q iv
      · rw [List.filter_cons_of_pos hq, List.length_cons]; omega
      · rw [List.filter_cons_of_neg hq]; omega

/-- Every element of a `Nat` list is `≤` its `nmax`-fold from `0`. -/
theorem le_foldr_nmax (l : List Nat) (x : Nat) (hx : x ∈ l) : x ≤ l.foldr nmax 0 := by
  induction l with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons hd tl ih =>
    rcases List.mem_cons.mp hx with heq | hx'
    · rw [heq]; exact nmax_ge_left hd (tl.foldr nmax 0)
    · exact Nat.le_trans (ih hx') (nmax_ge_right hd (tl.foldr nmax 0))

/-- The `nmax`-fold of a `Nat` list from `0` is either `0` (the empty case, subsumed since it can
    ALSO happen for a nonempty list of zeros — the disjunction is only used for `l = []` below) or
    equals an actual member of the list. -/
theorem foldMax_mem_or_nil (l : List Nat) : l = [] ∨ ∃ x ∈ l, l.foldr nmax 0 = x := by
  induction l with
  | nil => exact Or.inl rfl
  | cons hd tl ih =>
    rcases ih with h0 | ⟨y, hy, heq⟩
    · refine Or.inr ⟨hd, List.mem_cons_self, ?_⟩
      show nmax hd (tl.foldr nmax 0) = hd
      rw [h0]; exact nmax_zero_right hd
    · refine Or.inr ?_
      have hval : List.foldr nmax 0 (hd :: tl) = nmax hd (tl.foldr nmax 0) := rfl
      rcases nmax_eq_or hd (tl.foldr nmax 0) with h | h
      · exact ⟨hd, List.mem_cons_self, hval.trans h⟩
      · exact ⟨y, List.mem_cons_of_mem hd hy, hval.trans (h.trans heq)⟩

/-! ## Correctness -/

/-- **Domination**: every instant's coverage count is `≤` the program's answer. No hypothesis on
    `ivs` is needed — purely combinatorial (see the file docstring for the argument). -/
theorem rooms_dominates (ivs : List (Int × Int)) (t : Int) : countCover ivs t ≤ roomsFn ivs := by
  show (ivs.filter (fun iv => decide (iv.1 ≤ t ∧ t < iv.2))).length ≤ roomsFn ivs
  cases hS : ivs.filter (fun iv => decide (iv.1 ≤ t ∧ t < iv.2)) with
  | nil => exact Nat.zero_le _
  | cons hd tl =>
    rw [← hS]
    obtain ⟨m, hmS, hmax⟩ := exists_max_start hd tl
    have hmS' : m ∈ ivs.filter (fun iv => decide (iv.1 ≤ t ∧ t < iv.2)) := hS.symm ▸ hmS
    have hm_mem : m ∈ ivs ∧ (m.1 ≤ t ∧ t < m.2) :=
      ⟨(List.mem_filter.mp hmS').1, of_decide_eq_true (List.mem_filter.mp hmS').2⟩
    have himp : ∀ iv ∈ ivs, decide (iv.1 ≤ t ∧ t < iv.2) = true → decide (iv.1 ≤ m.1 ∧ m.1 < iv.2) = true := by
      intro iv hiv hp
      have hivS : iv ∈ ivs.filter (fun iv => decide (iv.1 ≤ t ∧ t < iv.2)) := List.mem_filter.mpr ⟨hiv, hp⟩
      have hivt : iv.1 ≤ t ∧ t < iv.2 := of_decide_eq_true (List.mem_filter.mp hivS).2
      have h1 : iv.1 ≤ m.1 := hmax iv (hS ▸ hivS)
      have h2 : m.1 < iv.2 := by have := hm_mem.2.1; omega
      simp only [decide_eq_true_eq]; exact ⟨h1, h2⟩
    calc (ivs.filter (fun iv => decide (iv.1 ≤ t ∧ t < iv.2))).length
        ≤ (ivs.filter (fun iv => decide (iv.1 ≤ m.1 ∧ m.1 < iv.2))).length :=
          filter_length_le_of_imp _ _ ivs himp
      _ = countCover ivs m.1 := rfl
      _ ≤ roomsFn ivs := le_foldr_nmax _ _ (List.mem_map.mpr ⟨m, hm_mem.1, rfl⟩)

/-- **Achievability**: the max is realized at some actual instant (a meeting's own start, or `0` for
    the empty input). -/
theorem rooms_achievable (ivs : List (Int × Int)) : ∃ t : Int, countCover ivs t = roomsFn ivs := by
  rcases foldMax_mem_or_nil (ivs.map (fun iv => countCover ivs iv.1)) with h0 | ⟨x, hx, heq⟩
  · have hnil : ivs = [] := List.map_eq_nil_iff.mp h0
    refine ⟨0, ?_⟩
    show countCover ivs 0 = roomsFn ivs
    rw [hnil]; rfl
  · obtain ⟨iv, hiv, hgiv⟩ := List.mem_map.mp hx
    refine ⟨iv.1, ?_⟩
    show countCover ivs iv.1 = roomsFn ivs
    rw [hgiv]; exact heq.symm

/-- **Correctness (headline)**: `roomsFn ivs` IS `max over all instants t of countCover ivs t` —
    achievability + domination (the `leetcode.md` S0 extremum shape), not a restatement of the
    program. -/
theorem rooms_correct (ivs : List (Int × Int)) :
    (∃ t : Int, countCover ivs t = roomsFn ivs) ∧ (∀ t : Int, countCover ivs t ≤ roomsFn ivs) :=
  ⟨rooms_achievable ivs, rooms_dominates ivs⟩

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The allegory program**: LeetCode 253's solution as a morphism `Ivs ⟶ ℕ` in `Rel(Set)`. -/
def solve : Ivs ⟶ dNat := graph roomsFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map roomsFn

/-! ## Running the program -/

-- LeetCode 253's own example: `[[0,30],[5,10],[15,20]] → 2` (`[0,30)` overlaps each of the other
-- two, but `[5,10)` and `[15,20)` never overlap each other).
example : roomsFn [(0, 30), (5, 10), (15, 20)] = 2 := by decide
-- Pairwise non-overlapping (touching allowed): `[[7,10],[2,4]] → 1`.
example : roomsFn [(7, 10), (2, 4)] = 1 := by decide

end Freyd.Alg.RelSet.LC253
