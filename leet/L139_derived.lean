/-
  LeetCode 139 — Word Break — DERIVED as a TABULATING (course-of-values) DP over the SUFFIX axis.

  `leet/L139.lean` decides Word Break with a FUEL recursion (`wordBreakFuel dict s.length s`):
  breakability of a suffix depends on breakability of MANY shorter suffixes, so the natural
  recursion is course-of-values, neither a raw structural fold nor a fixed-width tupling.  This
  file RESHAPES it into a TABULATING fold whose carrier is the growing table of sub-answers, and
  makes that fold EMERGE from the general-carrier fold-uniqueness law
  `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`).

  Tabulation axis: SUFFIXES, right-to-left, via the CONS-list of `s`.  Consuming `s` front-to-back,
  the cons fold reaches the tail (a shorter suffix) first, so the running carrier is the DP table
  for all suffixes processed so far.  The carrier is

      C := List α × List Bool        -- (the current suffix string, its dp table)

  * the FIRST component is the current suffix string, needed because the step must test which
    dictionary words are a PREFIX of it (`splitPrefix`); and
  * the SECOND component is the table `T`, length-indexed: `T[k]` is the breakability of the
    length-`k` suffix.  Prepending a char `c` appends one new cell — `dp` for the whole new suffix —
    computed by reading the WHOLE prior table `T` course-of-values (`cell`, which is exactly
    `L139.stepBreak` with the recursive call `rec suf := nthB T suf.length`).

      base   `g ()            = ([], [true])`                             (dp[0] = empty suffix ok)
      step   `st c (str, T)   = (c :: str, T ++ [cell dict T (c :: str)])`   (append the new cell)

  Feeding `g`/`st`/`tab` to `consFold_unique` PRODUCES the tabulating fold as
  `cataR (consScalarAlg g st)` — the fold is never written by hand (`tab_emerges`).  Correctness
  (`tab_correct`) is RE-PROVED against the inductive spec `L139.Seg` — the fuel proof does not
  transfer, because this fold recurses over the suffix axis with a course-of-values step, not over
  fuel.  The re-proof REUSES `L139`'s segmentation theory (`stepBreak_true_iff`, `seg_iff`, `Seg`),
  running a bounded induction over the string that discharges each table cell against `Seg`
  (analogous to `L322_derived`'s `entry_spec_bounded`).

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L139

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC139D

open Freyd Freyd.Alg.RelSet.CL

variable {α : Type} [DecidableEq α]

/-! ## Reading the Boolean DP table -/

/-- Index into the Boolean table, `false` if out of range (never happens for a valid suffix, since
    the cell at length `n+1` reads only indices `n+1-|w| ≤ n < n+1 = T.length`). -/
def nthB : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, n + 1 => nthB bs n

/-- Reading below the appended cell is unaffected by the append. -/
theorem nthB_append_lt :
    ∀ (T : List Bool) (x : Bool) (j : Nat), j < T.length → nthB (T ++ [x]) j = nthB T j := by
  intro T
  induction T with
  | nil => intro x j hj; exact absurd hj (Nat.not_lt_zero j)
  | cons y ys ih =>
    intro x j hj
    cases j with
    | zero => rfl
    | succ j => exact ih x j (Nat.lt_of_succ_lt_succ hj)

/-- Reading the appended cell (at index `= T.length`) returns it. -/
theorem nthB_append_length :
    ∀ (T : List Bool) (x : Bool), nthB (T ++ [x]) T.length = x := by
  intro T
  induction T with
  | nil => intro x; rfl
  | cons y ys ih => intro x; exact ih x

/-- Dropping `|l|` off `l ++ r` leaves `r`. -/
theorem drop_append_length (l r : List α) : (l ++ r).drop l.length = r := by
  induction l with
  | nil => rfl
  | cons a as ih => exact ih

/-! ## The emergent algebra (base `g`, step `st`) and the tabulating fold `tab` -/

/-- Base: the empty-suffix table `[dp[0]] = [true]` (`Seg dict []` holds). -/
def g : Unit → List α × List Bool := fun _ => ([], [true])

/-- One table cell: `dp` for the suffix `str`, folding over dictionary words that peel off its
    front and reading the tail table `T` at the leftover's length.  This is EXACTLY
    `L139.stepBreak` with the recursive call `rec suf := nthB T suf.length` — the whole prior table
    read course-of-values. -/
def cell (dict : List (List α)) (T : List Bool) (str : List α) : Bool :=
  LC139.stepBreak dict (fun suf => nthB T suf.length) str

/-- Step: prepend the new head `c` to the running suffix and append its `dp` cell. -/
def st (dict : List (List α)) : α → List α × List Bool → List α × List Bool :=
  fun c p => (c :: p.1, p.2 ++ [cell dict p.2 (c :: p.1)])

/-- The tabulating fold, defined FROM `g`/`st` so `consFold_unique` applies by `rfl`. -/
def tab (dict : List (List α)) : ConsList Unit α → List α × List Bool
  | ConsList.wrap d => g d
  | ConsList.cons c xs => st dict c (tab dict xs)

/-- **The derivation.**  The tabulating DP fold is PRODUCED by the general-carrier fold-uniqueness
    law — never written by hand: `graph (tab dict)` equals the catamorphism of the scalar cons-list
    algebra `consScalarAlg g (st dict)`, carrier `List α × List Bool`. -/
theorem tab_emerges (dict : List (List α)) :
    (graph (tab dict) : dCL Unit α ⟶ ⟨List α × List Bool⟩)
      = cataR (consScalarAlg g (st dict)) :=
  consFold_unique g (st dict) (tab dict) (fun _ => rfl) (fun _ _ => rfl)

/-! ## Converting a string to its cons-list and the table's structure -/

/-- The cons-list of a string `s` (`nil ↦ wrap ()`, `cons`). -/
def clist : List α → ConsList Unit α
  | [] => ConsList.wrap ()
  | c :: cs => ConsList.cons c (clist cs)

/-- The `cons` equation for `tab ∘ clist`'s FIRST component (reconstructed suffix). -/
theorem tab_fst_cons (dict : List (List α)) (c : α) (cs : List α) :
    (tab dict (clist (c :: cs))).1 = c :: (tab dict (clist cs)).1 := rfl

/-- The `cons` equation for `tab ∘ clist`'s SECOND component (the table). -/
theorem tab_snd_cons (dict : List (List α)) (c : α) (cs : List α) :
    (tab dict (clist (c :: cs))).2
      = (tab dict (clist cs)).2 ++ [cell dict (tab dict (clist cs)).2 (c :: (tab dict (clist cs)).1)] :=
  rfl

/-- The reconstructed suffix is the string itself. -/
theorem tab_fst (dict : List (List α)) (s : List α) : (tab dict (clist s)).1 = s := by
  induction s with
  | nil => rfl
  | cons c cs ih => rw [tab_fst_cons, ih]

/-- The table for `s` has `|s|+1` entries (indices `0..|s|`, one per suffix length). -/
theorem tab_len (dict : List (List α)) (s : List α) :
    (tab dict (clist s)).2.length = s.length + 1 := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    rw [tab_snd_cons, List.length_append, ih]
    simp only [List.length_cons, List.length_nil]

/-! ## Correctness: every table cell decides `Seg` (bounded induction on the string) -/

/-- **Core correctness.**  For every `k ≤ |s|`, the length-`k` cell of `s`'s table decides
    `Seg dict` on the length-`k` suffix `s.drop (|s|-k)`.  Bounded induction on `s`: prefix
    stability (`nthB_append_lt`) reduces short cells to the tail's table (IH), and the newest cell
    (`nthB_append_length`) is discharged by the `Seg` recurrence (`seg_iff`) reading the tail table
    course-of-values (the bridge below), reusing `L139.stepBreak_true_iff`. -/
theorem table_spec (dict : List (List α)) :
    ∀ (s : List α) (k : Nat), k ≤ s.length →
      (nthB (tab dict (clist s)).2 k = true ↔ LC139.Seg dict (s.drop (s.length - k))) := by
  intro s
  induction s with
  | nil =>
    intro k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    show nthB [true] 0 = true ↔ LC139.Seg dict ([] : List α)
    exact ⟨fun _ => LC139.Seg.nil, fun _ => rfl⟩
  | cons c cs ih =>
    intro k hk
    have hTlen : (tab dict (clist cs)).2.length = cs.length + 1 := tab_len dict cs
    have hfst : (tab dict (clist cs)).1 = cs := tab_fst dict cs
    rw [tab_snd_cons, hfst]
    rcases Nat.lt_or_ge k (cs.length + 1) with hlt | hge
    · -- short cell: reads below the appended cell, so equals the tail table's cell (IH)
      have hkle : k ≤ cs.length := Nat.lt_succ_iff.mp hlt
      rw [nthB_append_lt (tab dict (clist cs)).2
            (cell dict (tab dict (clist cs)).2 (c :: cs)) k (by rw [hTlen]; exact hlt)]
      rw [ih k hkle]
      have hdrop : (c :: cs).drop ((c :: cs).length - k) = cs.drop (cs.length - k) := by
        have h1 : (c :: cs).length - k = (cs.length - k) + 1 := by
          simp only [List.length_cons]; omega
        rw [h1]; rfl
      rw [hdrop]
    · -- newest cell (k = |cs|+1 = |c::cs|): the `Seg` recurrence over the tail table
      have hkeq : k = cs.length + 1 := by
        have h2 : k ≤ cs.length + 1 := by simpa only [List.length_cons] using hk
        omega
      subst hkeq
      have hrhs : (c :: cs).drop ((c :: cs).length - (cs.length + 1)) = c :: cs := by
        have hz : (c :: cs).length - (cs.length + 1) = 0 := by
          simp only [List.length_cons]; omega
        rw [hz]; rfl
      rw [hrhs, ← hTlen, nthB_append_length]
      show LC139.stepBreak dict (fun suf => nthB (tab dict (clist cs)).2 suf.length) (c :: cs) = true
          ↔ LC139.Seg dict (c :: cs)
      rw [LC139.stepBreak_true_iff, LC139.seg_iff]
      -- bridge: a leftover suffix `suf` after peeling a nonempty prefix off `c::cs` lives below the
      -- tail table, so its cell decides `Seg dict suf` by the IH
      have bridge : ∀ (w suf : List α), w ≠ [] → w ++ suf = c :: cs →
          (nthB (tab dict (clist cs)).2 suf.length = true ↔ LC139.Seg dict suf) := by
        intro w suf hne heq
        cases w with
        | nil => exact absurd rfl hne
        | cons c' w' =>
          rw [List.cons_append] at heq
          injection heq with hc htail
          have hlen : suf.length ≤ cs.length := by
            rw [← htail, List.length_append]; omega
          have hdropcs : cs.drop (cs.length - suf.length) = suf := by
            rw [← htail]
            have hh : (w' ++ suf).length - suf.length = w'.length := by
              rw [List.length_append]; omega
            rw [hh, drop_append_length]
          rw [ih suf.length hlen, hdropcs]
      constructor
      · rintro ⟨w, hw, suf, hne, heq, hrec⟩
        exact Or.inr ⟨w, hw, suf, hne, heq, (bridge w suf hne heq).mp hrec⟩
      · rintro (hnil | ⟨w, hw, suf, hne, heq, hseg⟩)
        · exact absurd hnil (List.cons_ne_nil c cs)
        · exact ⟨w, hw, suf, hne, heq, (bridge w suf hne heq).mpr hseg⟩

/-- **The tabulating DP is correct.**  The last cell of `s`'s table decides `Seg dict s`. -/
theorem tab_correct (dict : List (List α)) (s : List α) :
    nthB (tab dict (clist s)).2 s.length = true ↔ LC139.Seg dict s := by
  have h := table_spec dict s s.length (Nat.le_refl _)
  rw [Nat.sub_self] at h
  exact h

/-- **Headline.**  The emergent catamorphism relates `clist s` to a table `T`, and reading `T`'s
    last cell decides `Seg dict s`.  Ties the law-produced course-of-values fold
    `cataR (consScalarAlg g (st dict))` to the verified answer (mirrors `L322_derived`'s
    `answer_from_fold`). -/
theorem answer_from_fold (dict : List (List α)) (s : List α) :
    ∃ T, (cataR (consScalarAlg g (st dict)) : dCL Unit α ⟶ ⟨List α × List Bool⟩) (clist s) T
        ∧ (nthB T.2 s.length = true ↔ LC139.Seg dict s) := by
  refine ⟨tab dict (clist s), ?_, tab_correct dict s⟩
  have h : (graph (tab dict) : dCL Unit α ⟶ ⟨List α × List Bool⟩) (clist s) (tab dict (clist s)) :=
    rfl
  rw [tab_emerges] at h
  exact h

/-! ## Cross-check: the emergent table agrees with `L139`'s fuel solution and its examples

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the computable witness `tab` and read the
  last cell — extensionally the emergent fold's value (`tab_emerges`). -/

-- The last cell agrees with `L139.wordBreakFn` (both decide `Seg`), on the LeetCode examples:
example :
    nthB (tab (["leet".toList, "code".toList]) (clist "leetcode".toList)).2
      "leetcode".toList.length = true := by decide
example :
    nthB (tab (["apple".toList, "pen".toList]) (clist "applepenapple".toList)).2
      "applepenapple".toList.length = true := by decide
example :
    nthB (tab (["cats".toList, "dog".toList, "sand".toList, "and".toList, "cat".toList])
        (clist "catsandog".toList)).2 "catsandog".toList.length = false := by decide
example : nthB (tab ([] : List (List Char)) (clist ([] : List Char))).2 ([] : List Char).length
    = true := by decide

end Freyd.Alg.RelSet.LC139D
