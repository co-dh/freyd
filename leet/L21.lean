/-
  LeetCode 21 — Merge Two Sorted Lists — as an ALLEGORY PROGRAM.

  Problem: given two sorted (non-decreasing) integer lists, merge them into one sorted list
  containing exactly the elements of both, WITH MULTIPLICITY.

  Unlike every prior `List`-fold solve (`L206`, `L213`, `L1143`), merge genuinely recurses on
  BOTH inputs at once — each step peels the smaller head off ONE of the two lists, leaving the
  other untouched.  A naive two-argument pattern match compiles to WELL-FOUNDED recursion (like
  `L62`'s `paths`/`L1143`'s naive `lcs`), so — following the `L322`/`L1143` fuel trick (Skill
  S13) — the program is a thin wrapper `mergeFn xs ys := mergeFuel (xs.length + ys.length) xs ys`
  over a FUEL-indexed helper `mergeFuel`, structural on the fuel and hence kernel-reducible
  (`decide` works directly).

  A pleasant simplification over `L1143`'s LCS: merge's fuel decrements are EXACT, not merely
  sufficient.  Once one list runs out, the answer is the other list VERBATIM — no further
  recursion, so the base cases cost no fuel at all.  And at the cons/cons step, the fuel handed
  to each recursive call is *exactly* that branch's own minimal requirement (never slack), so
  `mergeFn`'s defining recurrence (`mergeFn_cons_eq`) is recovered by ONE arithmetic rewrite
  (`List.length_cons` + `congrArg`), with no general "any sufficient fuel agrees" induction
  needed (contrast `L1143`'s `lcsFuel_stable`).

  1. **Program** — `mergeFn`, the textbook merge: compare the two heads, take the smaller,
     recurse on the rest.
  2. **Specification** — the honest LeetCode spec, phrased with NO order assumed on the recursion
     shape: **sortedness** (`Sorted`, the standard adjacent-pairs chain) and **exact multiset
     preservation** (`count v out = count v xs + count v ys` for every value `v`, `count` a plain
     fold).  Both hypotheses (`Sorted xs`, `Sorted ys`) are required — merge is not correct on
     unsorted inputs, matching the problem statement.
  3. **Correctness = `merge_correct`** — `Sorted xs → Sorted ys → Sorted (mergeFn xs ys) ∧ ∀ v,
     count v (mergeFn xs ys) = count v xs + count v ys`.  Sortedness of the output goes through a
     `LeHead` helper (`LeHead b l` = "`b` is `≤` l's head, or `l` is empty"): `Sorted (b :: l) ↔
     LeHead b l ∧ Sorted l` holds BY DEFINITION (`sorted_cons`), and `LeHead` is preserved by
     `mergeFn` in ONE line per branch (`leHead_merge`) since `LeHead` only ever inspects the very
     first element of the result, which `mergeFn_cons_eq` pins down exactly. The double induction
     (outer on `xs`, inner on `ys`, exactly `L1143`'s shape) then closes both halves together.

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (in fact the core `merge_correct` theorem, being
  pure `List Int`/`Nat`/`Int` reasoning with no `Rel(Set)` machinery, needs neither — only the
  `Rel(Set)` packaging below pulls those in).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC21

open Freyd

/-! ## Program: the merge recurrence, via a fuel-indexed helper (Skill S13) -/

/-- `mergeFuel fuel xs ys` — the textbook merge, with an explicit FUEL bound so the recursion is
    ordinary structural recursion on `fuel` (not well-founded recursion on the shrinking pair of
    lists), keeping it kernel-reducible for `decide`.  Once either list is exhausted the answer is
    the other list VERBATIM, at NO fuel cost — only the cons/cons step spends one unit of fuel. -/
def mergeFuel : Nat → List Int → List Int → List Int
  | 0, _, _ => []
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      if x ≤ y then x :: mergeFuel fuel xs (y :: ys) else y :: mergeFuel fuel (x :: xs) ys

/-- **The program**: merge two sorted lists, run with exactly enough fuel (`fuel := xs.length +
    ys.length`, an upper bound — the cons/cons step never actually needs more than
    `min (xs.length) (ys.length)`, but the safe sum bound keeps the arithmetic uniform). -/
def mergeFn (xs ys : List Int) : List Int := mergeFuel (xs.length + ys.length) xs ys

/-! ## Base identities: `mergeFuel`'s nil clauses fire for ANY fuel-successor -/

@[simp] theorem mergeFuel_nil_left (fuel : Nat) (ys : List Int) :
    mergeFuel (fuel + 1) [] ys = ys := rfl

@[simp] theorem mergeFuel_nil_right (fuel : Nat) (xs : List Int) :
    mergeFuel (fuel + 1) xs [] = xs := by cases xs <;> rfl

/-- `mergeFn` on a `[]` left input is the right input, verbatim. -/
theorem mergeFn_nil_left (ys : List Int) : mergeFn [] ys = ys := by
  cases ys with
  | nil => rfl
  | cons y ys =>
    show mergeFuel ((0 : Nat) + (y :: ys).length) [] (y :: ys) = y :: ys
    have hlen : (0 : Nat) + (y :: ys).length = ys.length + 1 := by
      simp only [List.length_cons] <;> omega
    rw [hlen, mergeFuel_nil_left]

/-- `mergeFn` on a `[]` right input is the left input, verbatim. -/
theorem mergeFn_nil_right (xs : List Int) : mergeFn xs [] = xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    show mergeFuel ((x :: xs).length + (0 : Nat)) (x :: xs) [] = x :: xs
    have hlen : (x :: xs).length + (0 : Nat) = xs.length + 1 := by
      simp only [List.length_cons] <;> omega
    rw [hlen, mergeFuel_nil_right]

/-- **The book recurrence, recovered as a theorem**: `mergeFn`'s compare-and-recurse equation, by
    unfolding both sides at the EXACT (not merely sufficient) matching fuel — no fuel-invariance
    induction needed, since the cons/cons step's fuel spend is exact (see header). -/
theorem mergeFn_cons_eq (x : Int) (xs : List Int) (y : Int) (ys : List Int) :
    mergeFn (x :: xs) (y :: ys) =
      if x ≤ y then x :: mergeFn xs (y :: ys) else y :: mergeFn (x :: xs) ys := by
  have hmin : (x :: xs).length + (y :: ys).length = (xs.length + ys.length + 1) + 1 := by
    simp only [List.length_cons] <;> omega
  have hunfold : mergeFn (x :: xs) (y :: ys) =
      if x ≤ y then x :: mergeFuel (xs.length + ys.length + 1) xs (y :: ys)
      else y :: mergeFuel (xs.length + ys.length + 1) (x :: xs) ys := by
    show mergeFuel ((x :: xs).length + (y :: ys).length) (x :: xs) (y :: ys) = _
    rw [hmin]; simp only [mergeFuel]
  have e1 : mergeFuel (xs.length + ys.length + 1) xs (y :: ys) = mergeFn xs (y :: ys) := by
    have hlen1 : xs.length + ys.length + 1 = xs.length + (y :: ys).length := by
      simp only [List.length_cons] <;> omega
    show mergeFuel (xs.length + ys.length + 1) xs (y :: ys)
        = mergeFuel (xs.length + (y :: ys).length) xs (y :: ys)
    rw [hlen1]
  have e2 : mergeFuel (xs.length + ys.length + 1) (x :: xs) ys = mergeFn (x :: xs) ys := by
    have hlen2 : xs.length + ys.length + 1 = (x :: xs).length + ys.length := by
      simp only [List.length_cons] <;> omega
    show mergeFuel (xs.length + ys.length + 1) (x :: xs) ys
        = mergeFuel ((x :: xs).length + ys.length) (x :: xs) ys
    rw [hlen2]
  rw [hunfold, e1, e2]

/-! ## Specification: sortedness (adjacent-pairs chain) and exact multiset preservation -/

/-- The multiset count of `v` in a list, as a plain fold. -/
def count (v : Int) : List Int → Nat
  | [] => 0
  | x :: xs => (if x = v then 1 else 0) + count v xs

/-- `Sorted` — the standard adjacent-pairs (non-decreasing) chain. -/
def Sorted : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x ≤ y ∧ Sorted (y :: xs)

/-- `LeHead b l` — `b` is `≤` `l`'s head, vacuously true if `l` is empty.  The ONLY fact needed to
    prepend `b` to a sorted list and stay sorted (`sorted_cons`), and the ONLY fact `mergeFn`'s
    output-head lemma (`leHead_merge`) needs to track. -/
def LeHead (b : Int) : List Int → Prop
  | [] => True
  | z :: _ => b ≤ z

/-- **Prepending is sorted iff the head bound holds and the tail is sorted** — literally the
    definition of `Sorted`, restated via `LeHead` so it composes with `leHead_merge` below. -/
theorem sorted_cons (x : Int) (l : List Int) : Sorted (x :: l) ↔ LeHead x l ∧ Sorted l := by
  cases l with
  | nil => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | cons y l => exact Iff.rfl

/-! ## `mergeFn` preserves a head lower bound — the key structural fact for sortedness -/

/-- If `b` bounds both inputs' heads, `b` bounds the OUTPUT's head — read off directly from
    `mergeFn_cons_eq`: the merged head is always one of the two input heads. -/
theorem leHead_merge (b : Int) (xs ys : List Int) (hxs : LeHead b xs) (hys : LeHead b ys) :
    LeHead b (mergeFn xs ys) := by
  cases xs with
  | nil => rw [mergeFn_nil_left]; exact hys
  | cons x xs =>
    cases ys with
    | nil => rw [mergeFn_nil_right]; exact hxs
    | cons y ys =>
      rw [mergeFn_cons_eq]
      split
      · exact hxs
      · exact hys

/-! ## Correctness: `merge_correct`, by double induction (outer on `xs`, inner on `ys`) -/

/-- **Correctness of the allegory program** (the headline theorem): given two SORTED inputs,
    `mergeFn` returns a SORTED list whose multiset is exactly the union (with multiplicity) of the
    two inputs' multisets. -/
theorem merge_correct : ∀ xs ys : List Int, Sorted xs → Sorted ys →
    Sorted (mergeFn xs ys) ∧ ∀ v, count v (mergeFn xs ys) = count v xs + count v ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ hys
    rw [mergeFn_nil_left]
    exact ⟨hys, fun v => by simp [count]⟩
  | cons x xs ih_outer =>
    intro ys
    induction ys with
    | nil =>
      intro hxxs _
      rw [mergeFn_nil_right]
      exact ⟨hxxs, fun v => by simp [count]⟩
    | cons y ys ih_inner =>
      intro hxxs hyys
      obtain ⟨hLxs, hSxs⟩ := (sorted_cons x xs).mp hxxs
      obtain ⟨hLys, hSys⟩ := (sorted_cons y ys).mp hyys
      rw [mergeFn_cons_eq]
      by_cases hxy : x ≤ y
      · rw [if_pos hxy]
        obtain ⟨hSrec, hCrec⟩ := ih_outer (y :: ys) hSxs hyys
        have hLhead : LeHead x (mergeFn xs (y :: ys)) := leHead_merge x xs (y :: ys) hLxs hxy
        refine ⟨(sorted_cons x _).mpr ⟨hLhead, hSrec⟩, fun v => ?_⟩
        have e1 : count v (x :: mergeFn xs (y :: ys))
            = (if x = v then 1 else 0) + count v (mergeFn xs (y :: ys)) := rfl
        have e2 : count v (x :: xs) = (if x = v then 1 else 0) + count v xs := rfl
        rw [e1, e2, hCrec v]
        omega
      · have hyx : y ≤ x := by omega
        rw [if_neg hxy]
        obtain ⟨hSrec, hCrec⟩ := ih_inner hxxs hSys
        have hLhead : LeHead y (mergeFn (x :: xs) ys) := leHead_merge y (x :: xs) ys hyx hLys
        refine ⟨(sorted_cons y _).mpr ⟨hLhead, hSrec⟩, fun v => ?_⟩
        have e1 : count v (y :: mergeFn (x :: xs) ys)
            = (if y = v then 1 else 0) + count v (mergeFn (x :: xs) ys) := rfl
        have e2 : count v (y :: ys) = (if y = v then 1 else 0) + count v ys := rfl
        rw [e1, e2, hCrec v]
        omega

/-! ## `Rel(Set)` packaging -/

/-- The input object: the two sorted lists to merge. -/
abbrev dInput : RelSet.{0} := ⟨List Int × List Int⟩
/-- The answer object: the merged list. -/
abbrev dAns : RelSet.{0} := ⟨List Int⟩

/-- **The allegory program**: LeetCode 21's merge as a morphism `dInput ⟶ dAns` in `Rel(Set)`. -/
def solve : dInput ⟶ dAns := graph (fun p => mergeFn p.1 p.2)

/-- **The specification** as a morphism `dInput ⟶ dAns` in `Rel(Set)`: given two sorted inputs,
    the output is sorted and its multiset is their union. -/
def spec : dInput ⟶ dAns := fun p l =>
  Sorted p.1 → Sorted p.2 → Sorted l ∧ ∀ v, count v l = count v p.1 + count v p.2

/-- **The program refines the specification** (in fact computes it exactly): every answer `solve`
    returns satisfies `spec`. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun p l h => ?_)
  have hl : l = mergeFn p.1 p.2 := h
  intro h1 h2
  rw [hl]
  exact merge_correct p.1 p.2 h1 h2

/-! ## Uniqueness: a sorted list is determined by its multiset (canonical home for the fact that
    `L23`/`L977`'s sorted outputs are unique). -/

/-- A value has positive count in a list starting with it. -/
theorem count_self_pos (a : Int) (l : List Int) : 0 < count a (a :: l) := by
  show 0 < (if a = a then (1 : Nat) else 0) + count a l
  rw [if_pos rfl]; omega

/-- A value with positive count is a member. -/
theorem mem_of_count_pos {v : Int} : ∀ l : List Int, 0 < count v l → v ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (Nat.lt_irrefl 0)
  | cons x xs ih =>
      intro h
      by_cases hxv : x = v
      · subst hxv; exact List.mem_cons_self
      · have e : count v (x :: xs) = count v xs := by
          show (if x = v then (1 : Nat) else 0) + count v xs = count v xs
          rw [if_neg hxv]; omega
        rw [e] at h
        exact List.mem_cons_of_mem x (ih h)

/-- In a sorted list, the head is `≤` every other element. -/
theorem sorted_head_le : ∀ (a : Int) (l : List Int), Sorted (a :: l) → ∀ z ∈ l, a ≤ z := by
  intro a l
  induction l generalizing a with
  | nil => intro _ z hz; exact absurd hz List.not_mem_nil
  | cons c l ih =>
      intro hs z hz
      obtain ⟨hac, hScl⟩ := hs
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hac
      · exact Int.le_trans hac (ih c hScl z hz')

/-- **Sorted lists with the same multiset are equal.**  Matching heads must be equal (each is the
    minimum, so `≤` the other), then strip and recurse.  This is what pins the merge output uniquely,
    turning `solve_le_spec` into a genuine morphism equation. -/
theorem sorted_count_ext : ∀ xs ys : List Int,
    Sorted xs → Sorted ys → (∀ v, count v xs = count v ys) → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _ hc
      cases ys with
      | nil => rfl
      | cons b ys' =>
          exfalso
          have hpos := count_self_pos b ys'
          have heq := hc b
          have hnil : count b ([] : List Int) = 0 := rfl
          omega
  | cons a xs' ih =>
      intro ys hSx hSy hc
      cases ys with
      | nil =>
          exfalso
          have hpos := count_self_pos a xs'
          have heq := hc a
          have hnil : count a ([] : List Int) = 0 := rfl
          omega
      | cons b ys' =>
          have hax : ∀ z ∈ xs', a ≤ z := sorted_head_le a xs' hSx
          have hby : ∀ z ∈ ys', b ≤ z := sorted_head_le b ys' hSy
          have ha_in : a ∈ b :: ys' := by
            apply mem_of_count_pos
            have hpos := count_self_pos a xs'; rw [hc a] at hpos; exact hpos
          have hb_in : b ∈ a :: xs' := by
            apply mem_of_count_pos
            have hpos := count_self_pos b ys'; rw [← hc b] at hpos; exact hpos
          have hba : b ≤ a := by
            rcases List.mem_cons.mp ha_in with rfl | ha'
            · exact Int.le_refl _
            · exact hby a ha'
          have hab : a ≤ b := by
            rcases List.mem_cons.mp hb_in with rfl | hb'
            · exact Int.le_refl _
            · exact hax b hb'
          have hab_eq : a = b := Int.le_antisymm hab hba
          subst hab_eq
          have hSx' : Sorted xs' := ((sorted_cons a xs').mp hSx).2
          have hSy' : Sorted ys' := ((sorted_cons a ys').mp hSy).2
          have hc' : ∀ v, count v xs' = count v ys' := by
            intro v
            have h := hc v
            have e1 : count v (a :: xs') = (if a = v then (1 : Nat) else 0) + count v xs' := rfl
            have e2 : count v (a :: ys') = (if a = v then (1 : Nat) else 0) + count v ys' := rfl
            rw [e1, e2] at h; omega
          rw [ih ys' hSx' hSy' hc']

/-! ## Headline: on SORTED inputs, `solve` IS `spec` (a genuine morphism equation) -/

/-- The precondition coreflexive: the sub-identity on WELL-FORMED inputs (both lists sorted). -/
def pre : dInput ⟶ dInput := fun x y => x = y ∧ Sorted x.1 ∧ Sorted x.2

/-- **Preconditioned headline**: restricted to sorted inputs (`pre`), the program equals the
    specification — `pre ≫ solve = pre ≫ spec`.  Existence is `merge_correct`; uniqueness is
    `sorted_count_ext` (a sorted list is pinned by its multiset).  The precondition is required
    because the multiset-union spec only determines a UNIQUE list once sortedness is assumed. -/
theorem pre_solve_eq_spec : pre ≫ solve = pre ≫ spec := by
  apply hom_ext; intro p l
  rw [comp_apply, comp_apply]
  constructor
  · rintro ⟨y, ⟨rfl, h1, h2⟩, hsolve⟩
    refine ⟨p, ⟨rfl, h1, h2⟩, ?_⟩
    intro ha hb
    rw [(hsolve : l = mergeFn p.1 p.2)]; exact merge_correct p.1 p.2 ha hb
  · rintro ⟨y, ⟨rfl, h1, h2⟩, hspec⟩
    refine ⟨p, ⟨rfl, h1, h2⟩, ?_⟩
    obtain ⟨hSl, hCl⟩ := hspec h1 h2
    obtain ⟨hSm, hCm⟩ := merge_correct p.1 p.2 h1 h2
    show l = mergeFn p.1 p.2
    exact sorted_count_ext l (mergeFn p.1 p.2) hSl hSm (fun v => by rw [hCl v, hCm v])

/-! ## Running the program -/

example : mergeFn ([1, 2, 4] : List Int) [1, 3, 4] = [1, 1, 2, 3, 4, 4] := by decide
example : mergeFn ([] : List Int) [] = [] := by decide
example : mergeFn ([] : List Int) [0] = [0] := by decide
example : mergeFn ([2, 5, 8] : List Int) [1, 3, 3, 9] = [1, 2, 3, 3, 5, 8, 9] := by decide

end Freyd.Alg.RelSet.LC21
