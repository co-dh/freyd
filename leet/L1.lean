/-
  LeetCode 1 — Two Sum — DERIVED from its relational SPEC by the THINNING theorem (B&dM Cor 8.1).

  One file, one story: specification → calculation → program.

  1. **Spec** — `TwoSum nums target i j := i < j ∧ nums[i] + nums[j] = target` (via `getElem?`),
     packaged as the answer relation `tsSpec : Input ⟶ Ans` in `Rel(Set)`: an acceptable answer
     is any valid pair, or `none` exactly when no pair exists.

  2. **Calculation** — `rel/AutoDeriveThin.lean`'s `ThinBest` driver (the mechanised THEOREM 8.1 /
     Corollary 8.1 of `AOP/A8_1.lean`, whose abstract program `⦇Λ(S·F∈)·thin Q⦈ ≫ min R` is a fold
     carrying a POWER-OBJECT point — the kept candidate set — pruned at every step).  Scanning
     left to right, a candidate is `start` (no commitment), `part k v` (first leg at index `k`,
     value `v`), or `found i j` (a finished pair); reachable states are EXACTLY the spec
     (`gen_char`).  The thinning order `Q` is the algorithmic content, as Pareto dominance:
       * same-value partials collapse (keep the LATEST index) — why a seen-map with one entry per
         value suffices;
       * a `found i j` with `j` past dominates everything — why the scan may return at the first
         hit (the early return).
     Corollary 8.1 turns `Q` into the program `thinTwoSum` (extend the frontier, prune, pick the
     `R`-best) and certifies it (`thinTwoSum_correct`): the answer is the `ansLe`-MAXIMUM valid
     pair — smallest second index, then largest first index — or `none` iff no pair exists.

  3. **Program** — the classical one-pass scan `twoSumFn` (association-list seen-map) returns that
     same canonical pair (`twoSum_opt`), so it EQUALS the derived program (`thin_eq_scan`); and
     the `O(n)`-expected hash scan `hashTwoSum` (`AHashMap`: one `find?` + one `insert` per
     element) computes the same function (`hashTwoSum_eq`, a data-refinement simulation), so
     `thin_eq_hash`: spec → (Cor 8.1) → pruned fold → scan → `O(n)` hash program.

  4. **Headline** (`solve_eq_Λ_maxRel`, the `leet/L53.lean` form): `solve = Λ tsSpec ≫ maxRel D`
     in `Rel(Set)` — B&dM's `max D · Λ spec`, the function derived from the relational spec, as a
     morphism equation.  No uniqueness assumption on inputs.

  What the allegory does NOT see: the O(1)-expected bucket lookup inside `AHashMap`.  Thinning
  licenses the ABSTRACT algorithm (one entry per value + early return); the constant-time lookup
  is a data refinement below relation algebra (the simulation in step 3).

  Mathlib-free.  Axioms: the derivation/headline ⊆ {propext, Classical.choice, Quot.sound}
  (`Classical.choice` inherited from `cataR_eq_relCata` through Cor 8.1); the scan and its
  correctness/optimality are fully constructive ⊆ {propext, Quot.sound}.
-/
import rel.AutoDeriveThin
import AOP.A6_HashMap

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC1

open Freyd Freyd.Alg.RelSet.SL Freyd.HashMap

/-! ## The problem and its specification -/

/-- The input object: a list of integers paired with a target sum. -/
abbrev Input : RelSet.{0} := ⟨List Int × Int⟩
/-- The answer object: an optional pair of positions. -/
abbrev Ans : RelSet.{0} := ⟨Option (Nat × Nat)⟩

/-- `TwoSum nums target i j` — `i` and `j` are DISTINCT positions (`i < j`) inside `nums` whose
    values sum to `target`.  `i < nums.length` is a consequence of `nums[i]? = some vi`, not a
    separate hypothesis (`List.getElem?_eq_some_iff`). -/
def TwoSum (nums : List Int) (target : Int) (i j : Nat) : Prop :=
  i < j ∧ ∃ vi vj, nums[i]? = some vi ∧ nums[j]? = some vj ∧ vi + vj = target

/-- The SPEC as a relation `Input ⟶ Ans`: an acceptable answer is a valid pair, or `none`
    exactly when no valid pair exists. -/
def tsSpec : Input ⟶ Ans := fun p a =>
  (a = none ∧ ∀ i j, ¬ TwoSum p.1 p.2 i j) ∨
    ∃ i j, a = some (i, j) ∧ TwoSum p.1 p.2 i j

/-! ## `getElem?` plumbing across an append at the boundary -/

/-- The freshly-appended element sits exactly at index `l1.length`. -/
theorem getElem?_append_right_zero {l1 l2 : List Int} {x : Int} :
    (l1 ++ x :: l2)[l1.length]? = some x := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-- Splitting a `getElem?` fact across the appended last element. -/
theorem getElem?_append_singleton {nums : List Int} {x v : Int} {k : Nat}
    (h : (nums ++ [x])[k]? = some v) :
    (k < nums.length ∧ nums[k]? = some v) ∨ (k = nums.length ∧ v = x) := by
  have hkb : k < (nums ++ [x]).length := (List.getElem?_eq_some_iff.mp h).1
  simp only [List.length_append, List.length_singleton] at hkb
  rcases Nat.lt_or_ge k nums.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at h
    exact Or.inl ⟨hlt, h⟩
  · have hkeq : k = nums.length := by omega
    rw [hkeq, getElem?_append_right_zero] at h
    injection h with hv
    exact Or.inr ⟨hkeq, hv.symm⟩

theorem twoSum_lift {nums : List Int} {x target : Int} {i j : Nat}
    (h : TwoSum nums target i j) : TwoSum (nums ++ [x]) target i j := by
  obtain ⟨hij, vi, vj, hdi, hdj, hsum⟩ := h
  have hib := (List.getElem?_eq_some_iff.mp hdi).1
  have hjb := (List.getElem?_eq_some_iff.mp hdj).1
  exact ⟨hij, vi, vj, by rw [List.getElem?_append_left hib]; exact hdi,
    by rw [List.getElem?_append_left hjb]; exact hdj, hsum⟩

theorem twoSum_restrict {nums : List Int} {x target : Int} {i j : Nat}
    (hj : j < nums.length) (h : TwoSum (nums ++ [x]) target i j) :
    TwoSum nums target i j := by
  obtain ⟨hij, vi, vj, hdi, hdj, hsum⟩ := h
  have hi : i < nums.length := Nat.lt_trans hij hj
  rw [List.getElem?_append_left hi] at hdi
  rw [List.getElem?_append_left hj] at hdj
  exact ⟨hij, vi, vj, hdi, hdj, hsum⟩

/-! ## Candidate states and the two orders -/

/-- A partial solution of the left-to-right scan. -/
inductive TSChoice where
  | start : TSChoice                -- no first leg committed yet
  | part  : Nat → Int → TSChoice    -- first leg at index `k` holding value `v`
  | found : Nat → Nat → TSChoice    -- a finished pair `(i, j)`

/-- The answer a state stands for. -/
def outc : TSChoice → Option (Nat × Nat)
  | .found i j => some (i, j)
  | _ => none

/-- The selection preorder on answers: `none` is worst; among pairs, smaller second index wins,
    then larger first index (`ansLe z w` = "`w` at least as good as `z`", the `minRel`
    convention).  This is the order under which the scan's answer is the maximum. -/
def ansLe : Option (Nat × Nat) → Option (Nat × Nat) → Prop
  | none, _ => True
  | some _, none => False
  | some (i, j), some (i', j') => j' < j ∨ (j' = j ∧ i ≤ i')

/-- Boolean test for `ansLe` (total). -/
def ansLeB : Option (Nat × Nat) → Option (Nat × Nat) → Bool
  | none, _ => true
  | some _, none => false
  | some (i, j), some (i', j') => decide (j' < j ∨ (j' = j ∧ i ≤ i'))

theorem ansLe_trans : ∀ {a b c : Option (Nat × Nat)}, ansLe a b → ansLe b c → ansLe a c := by
  rintro (_ | ⟨i, j⟩) (_ | ⟨i', j'⟩) (_ | ⟨i'', j''⟩) hab hbc <;> simp_all [ansLe] <;> omega

theorem ansLe_antisym : ∀ {a b : Option (Nat × Nat)}, ansLe a b → ansLe b a → a = b := by
  rintro (_ | ⟨i, j⟩) (_ | ⟨i', j'⟩) hab hba <;> simp_all [ansLe] <;> omega

theorem ansLeB_true : ∀ {a b : Option (Nat × Nat)}, ansLeB a b = true → ansLe a b := by
  rintro (_ | ⟨i, j⟩) (_ | ⟨i', j'⟩) h <;> simp_all [ansLeB, ansLe]

theorem ansLeB_false : ∀ {a b : Option (Nat × Nat)}, ansLeB b a = false → ansLe a b := by
  rintro (_ | ⟨i, j⟩) (_ | ⟨i', j'⟩) h <;> simp_all [ansLeB, ansLe] <;> omega

/-- The thinning preorder at scan position `n` (`Qc n z w` = "`w` dominates `z`"): same-value
    partials with a larger index dominate; a finished pair with `j < n` dominates every
    unfinished state (any later completion has second index `≥ n > j`); finished pairs compare
    by the answer order. -/
def Qc (n : Nat) : TSChoice → TSChoice → Prop
  | .start, .start => True
  | .part k v, .part k' v' => v' = v ∧ k ≤ k'
  | .start, .found _ j => j < n
  | .part _ _, .found _ j => j < n
  | .found i j, .found i' j' => j' < j ∨ (j' = j ∧ i ≤ i')
  | _, _ => False

/-- Boolean test for `Qc` (soundness is all the prune needs). -/
def qcB (n : Nat) : TSChoice → TSChoice → Bool
  | .start, .start => true
  | .part k v, .part k' v' => decide (v' = v) && decide (k ≤ k')
  | .start, .found _ j => decide (j < n)
  | .part _ _, .found _ j => decide (j < n)
  | .found i j, .found i' j' => decide (j' < j ∨ (j' = j ∧ i ≤ i'))
  | _, _ => false

theorem qcB_sound {n : Nat} : ∀ {c c'}, qcB n c c' = true → Qc n c c' := by
  intro c c' h
  cases c <;> cases c' <;> simp_all [qcB, Qc]

theorem Qc_refl {n : Nat} : ∀ c, Qc n c c := by
  intro c; cases c <;> simp [Qc]

theorem Qc_trans {n : Nat} : ∀ {a b c}, Qc n a b → Qc n b c → Qc n a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp_all [Qc] <;> omega

theorem Qc_le_ansLe {n : Nat} : ∀ {c c'}, Qc n c c' → ansLe (outc c) (outc c') := by
  intro c c' h
  cases c <;> cases c' <;> simp_all [Qc, outc, ansLe]

/-! ## The thinning bundle: the CREATIVE inputs of the derivation (B&dM ch. 8) -/

/-- A partial's stay-extension is in its step list whichever way the completion test goes. -/
theorem mem_stay {n k : Nat} {v x target : Int} :
    (n + 1, TSChoice.part k v) ∈ (if v + x = target
      then [(n + 1, TSChoice.part k v), (n + 1, TSChoice.found k n)]
      else [(n + 1, TSChoice.part k v)]) := by
  by_cases ht : v + x = target
  · rw [if_pos ht]; exact List.mem_cons_self ..
  · rw [if_neg ht]; exact List.mem_cons_self ..

/-- The Two Sum thinning bundle at a fixed `target`.  Leaf = the uncommitted scan; a step at
    element `x` (arriving at index `n`, the state's counter) lets `start` stay or commit the
    new element as a first leg, lets a partial stay or — when its complement arrived — finish,
    and keeps a finished pair.  `step_mono` is the §8.1 insight, case by case. -/
def tsB (target : Int) : ThinBest Unit Int (Nat × TSChoice) where
  leafOne _ := [(0, .start)]
  stepOne s x :=
    match s with
    | (n, .start) => [(n + 1, .start), (n + 1, .part n x)]
    | (n, .part k v) =>
      if v + x = target then [(n + 1, .part k v), (n + 1, .found k n)]
      else [(n + 1, .part k v)]
    | (n, .found i j) => [(n + 1, .found i j)]
  Q z w := z.1 = w.1 ∧ Qc z.1 z.2 w.2
  R z w := ansLe (outc z.2) (outc w.2)
  qDec z w := decide (z.1 = w.1) && qcB z.1 z.2 w.2
  rDec z w := ansLeB (outc w.2) (outc z.2)
  Q_refl s := ⟨rfl, Qc_refl s.2⟩
  Q_trans := by
    rintro s t u ⟨h1, hq1⟩ ⟨h2, hq2⟩
    refine ⟨h1.trans h2, ?_⟩
    rw [h1] at hq1 ⊢
    exact Qc_trans hq1 hq2
  Q_le_R := by
    rintro s t ⟨-, hq⟩
    exact Qc_le_ansLe hq
  R_trans := fun h1 h2 => ansLe_trans h1 h2
  qDec_sound := by
    intro s t h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, qcB_sound h.2⟩
  rDec_t := fun h => ansLeB_true h
  rDec_f := fun h => ansLeB_false h
  step_mono := by
    intro s s' x y hQ hy
    obtain ⟨n, c⟩ := s
    obtain ⟨n', c'⟩ := s'
    obtain ⟨hn, hqc⟩ := hQ
    -- `subst` on `n = n'` eliminates `n'`, keeping the dominator's counter name `n`
    have hn2 : n = n' := (hn : n' = n).symm
    subst hn2
    match c', c with
    | .start, .start =>
      -- the dominator generates the same two extensions: match `y` with itself
      exact ⟨y, hy, rfl, Qc_refl y.2⟩
    | .part k' v', .part k v =>
      obtain ⟨hv, hk⟩ := (hqc : v = v' ∧ k' ≤ k)
      subst hv
      have hy' : y ∈ (if v + x = target
          then [(n + 1, TSChoice.part k' v), (n + 1, TSChoice.found k' n)]
          else [(n + 1, TSChoice.part k' v)]) := hy
      by_cases ht : v + x = target
      · rw [if_pos ht] at hy'
        rcases List.mem_cons.mp hy' with rfl | hy2
        · -- the stay: matched by the dominator's stay
          exact ⟨(n + 1, .part k v), mem_stay, rfl, rfl, hk⟩
        · -- the completion: the SAME complement finishes the dominator's (larger-index) leg
          have hyf : y = (n + 1, TSChoice.found k' n) := List.mem_singleton.mp hy2
          subst hyf
          refine ⟨(n + 1, .found k n), ?_, rfl, Or.inr ⟨rfl, hk⟩⟩
          show (n + 1, TSChoice.found k n) ∈ (if v + x = target
            then [(n + 1, TSChoice.part k v), (n + 1, TSChoice.found k n)]
            else [(n + 1, TSChoice.part k v)])
          rw [if_pos ht]; exact List.mem_cons.mpr (Or.inr (List.mem_cons_self ..))
      · rw [if_neg ht] at hy'
        have hys : y = (n + 1, TSChoice.part k' v) := List.mem_singleton.mp hy'
        subst hys
        exact ⟨(n + 1, .part k v), mem_stay, rfl, rfl, hk⟩
    | .start, .found i j =>
      -- a past pair dominates whatever the uncommitted state spawns
      have hj : j < n := hqc
      have hy' : y ∈ [(n + 1, TSChoice.start), (n + 1, TSChoice.part n x)] := hy
      rcases List.mem_cons.mp hy' with rfl | hy2
      · exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl,
          (by omega : j < n + 1)⟩
      · have hyp : y = (n + 1, TSChoice.part n x) := List.mem_singleton.mp hy2
        subst hyp
        exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl,
          (by omega : j < n + 1)⟩
    | .part k' v', .found i j =>
      -- a past pair dominates a partial's stay AND its completion (second index `n > j`)
      have hj : j < n := hqc
      have hy' : y ∈ (if v' + x = target
          then [(n + 1, TSChoice.part k' v'), (n + 1, TSChoice.found k' n)]
          else [(n + 1, TSChoice.part k' v')]) := hy
      by_cases ht : v' + x = target
      · rw [if_pos ht] at hy'
        rcases List.mem_cons.mp hy' with rfl | hy2
        · exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl,
            (by omega : j < n + 1)⟩
        · have hyf : y = (n + 1, TSChoice.found k' n) := List.mem_singleton.mp hy2
          subst hyf
          exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl, Or.inl hj⟩
      · rw [if_neg ht] at hy'
        have hys : y = (n + 1, TSChoice.part k' v') := List.mem_singleton.mp hy'
        subst hys
        exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl,
          (by omega : j < n + 1)⟩
    | .found i' j', .found i j =>
      have hy' : y = (n + 1, TSChoice.found i' j') := List.mem_singleton.mp hy
      subst hy'
      exact ⟨(n + 1, .found i j), List.mem_cons.mpr (Or.inl rfl), rfl, hqc⟩
    | .start, .part _ _ => exact (hqc : False).elim
    | .part _ _, .start => exact (hqc : False).elim
    | .found _ _, .start => exact (hqc : False).elim
    | .found _ _, .part _ _ => exact (hqc : False).elim

/-! ## Snoc-list plumbing -/

/-- The `List` a snoc-list denotes. -/
def toList : SnocList Unit Int → List Int
  | .wrap _ => []
  | .snoc xs x => toList xs ++ [x]

/-- A `List Int` reindexed onto the snoc-list initial algebra. -/
def ofNums (nums : List Int) : SnocList Unit Int :=
  nums.foldl SnocList.snoc (SnocList.wrap ())

theorem toList_foldl : ∀ (nums : List Int) (acc : SnocList Unit Int),
    toList (nums.foldl SnocList.snoc acc) = toList acc ++ nums
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, toList_foldl xs (acc.snoc x)]
    show (toList acc ++ [x]) ++ xs = toList acc ++ x :: xs
    rw [List.append_assoc, List.singleton_append]

theorem toList_ofNums (nums : List Int) : toList (ofNums nums) = nums := by
  rw [ofNums, toList_foldl]; rfl

/-! ## The generator's reachable states are EXACTLY the spec -/

/-- What each candidate shape claims of the processed prefix. -/
def ReachC (nums : List Int) (target : Int) : TSChoice → Prop
  | .start => True
  | .part k v => nums[k]? = some v
  | .found i j => TwoSum nums target i j

/-- The generator-vs-spec characterisation (the one problem-specific induction, as in the
    knapsack demo's `gen_iff_choice`): a state is generatable iff its counter is the prefix
    length and its claim holds — in particular `found i j` is generatable iff `TwoSum i j`. -/
theorem gen_char (target : Int) : ∀ (xs : SnocList Unit Int) (s : Nat × TSChoice),
    cataFold (tsB target).gen xs s ↔
      s.1 = (toList xs).length ∧ ReachC (toList xs) target s.2 := by
  intro xs
  induction xs with
  | wrap u =>
    intro s
    constructor
    · intro h
      have hs : s = (0, TSChoice.start) := List.mem_singleton.mp h
      subst hs
      exact ⟨rfl, trivial⟩
    · rintro ⟨hn, hr⟩
      obtain ⟨n, c⟩ := s
      match c with
      | .start =>
        have hn0 : n = 0 := hn
        subst hn0
        exact List.mem_singleton.mpr rfl
      | .part k v =>
        have hkv : ([] : List Int)[k]? = some v := hr
        simp at hkv
      | .found i j =>
        have hts : TwoSum [] target i j := hr
        obtain ⟨-, vi, vj, hdi, -⟩ := hts
        simp at hdi
  | snoc xs x ih =>
    intro s
    constructor
    · rintro ⟨s', hprev, hstep⟩
      obtain ⟨n', c'⟩ := s'
      obtain ⟨hn', hrc⟩ := (ih (n', c')).mp hprev
      have hn'' : n' = (toList xs).length := hn'
      match c' with
      | .start =>
        have hy : s ∈ [(n' + 1, TSChoice.start), (n' + 1, TSChoice.part n' x)] := hstep
        rcases List.mem_cons.mp hy with rfl | hy2
        · refine ⟨?_, trivial⟩
          show n' + 1 = (toList xs ++ [x]).length
          simp only [List.length_append, List.length_singleton]
          omega
        · have hs : s = (n' + 1, TSChoice.part n' x) := List.mem_singleton.mp hy2
          subst hs
          refine ⟨?_, ?_⟩
          · show n' + 1 = (toList xs ++ [x]).length
            simp only [List.length_append, List.length_singleton]
            omega
          · show (toList xs ++ [x])[n']? = some x
            rw [hn'']
            exact getElem?_append_right_zero
      | .part k v =>
        have hkv : (toList xs)[k]? = some v := hrc
        have hkb : k < (toList xs).length := (List.getElem?_eq_some_iff.mp hkv).1
        have hy : s ∈ (if v + x = target
            then [(n' + 1, TSChoice.part k v), (n' + 1, TSChoice.found k n')]
            else [(n' + 1, TSChoice.part k v)]) := hstep
        have hlen1 : n' + 1 = (toList xs ++ [x]).length := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hstay : ReachC (toList xs ++ [x]) target (.part k v) := by
          show (toList xs ++ [x])[k]? = some v
          rw [List.getElem?_append_left hkb]
          exact hkv
        by_cases ht : v + x = target
        · rw [if_pos ht] at hy
          rcases List.mem_cons.mp hy with rfl | hy2
          · exact ⟨hlen1, hstay⟩
          · have hs : s = (n' + 1, TSChoice.found k n') := List.mem_singleton.mp hy2
            subst hs
            refine ⟨hlen1, ?_⟩
            show TwoSum (toList xs ++ [x]) target k n'
            refine ⟨by omega, v, x, ?_, ?_, ht⟩
            · rw [List.getElem?_append_left hkb]; exact hkv
            · rw [hn'']; exact getElem?_append_right_zero
        · rw [if_neg ht] at hy
          have hs : s = (n' + 1, TSChoice.part k v) := List.mem_singleton.mp hy
          subst hs
          exact ⟨hlen1, hstay⟩
      | .found i j =>
        have hs : s = (n' + 1, TSChoice.found i j) := List.mem_singleton.mp hstep
        subst hs
        refine ⟨?_, twoSum_lift (hrc : TwoSum (toList xs) target i j)⟩
        show n' + 1 = (toList xs ++ [x]).length
        simp only [List.length_append, List.length_singleton]
        omega
    · rintro ⟨hn, hr⟩
      obtain ⟨n, c⟩ := s
      have hn1 : n = (toList xs).length + 1 := by
        have h : n = (toList xs ++ [x]).length := hn
        simp only [List.length_append, List.length_singleton] at h
        omega
      subst hn1
      match c with
      | .start =>
        refine ⟨((toList xs).length, .start), (ih _).mpr ⟨rfl, trivial⟩, ?_⟩
        show ((toList xs).length + 1, TSChoice.start) ∈
          [((toList xs).length + 1, TSChoice.start),
           ((toList xs).length + 1, TSChoice.part (toList xs).length x)]
        exact List.mem_cons.mpr (Or.inl rfl)
      | .part k v =>
        rcases getElem?_append_singleton (hr : (toList xs ++ [x])[k]? = some v) with
          ⟨hk, hkv⟩ | ⟨hk, hv⟩
        · -- an older leg: it was already reachable, and it stays
          exact ⟨((toList xs).length, .part k v), (ih _).mpr ⟨rfl, hkv⟩, mem_stay⟩
        · -- the leg committed at THIS step, spawned by `start`
          -- (`hv.symm : x = v` so `subst` eliminates `v`, keeping the snoc element name `x`)
          have hv' : x = v := hv.symm
          subst hv'
          subst hk
          refine ⟨((toList xs).length, .start), (ih _).mpr ⟨rfl, trivial⟩, ?_⟩
          show ((toList xs).length + 1, TSChoice.part (toList xs).length x) ∈
            [((toList xs).length + 1, TSChoice.start),
             ((toList xs).length + 1, TSChoice.part (toList xs).length x)]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      | .found i j =>
        have hr' : TwoSum (toList xs ++ [x]) target i j := hr
        obtain ⟨hij, vi, vj, hdi, hdj, hsum⟩ := hr'
        have hjb : j < (toList xs).length + 1 := by
          have := (List.getElem?_eq_some_iff.mp hdj).1
          simp only [List.length_append, List.length_singleton] at this
          omega
        rcases Nat.lt_or_ge j (toList xs).length with hjlt | hjge
        · -- the pair finished earlier: it was reachable and persists
          refine ⟨((toList xs).length, .found i j),
            (ih _).mpr ⟨rfl, twoSum_restrict hjlt ⟨hij, vi, vj, hdi, hdj, hsum⟩⟩, ?_⟩
          show ((toList xs).length + 1, TSChoice.found i j) ∈
            [((toList xs).length + 1, TSChoice.found i j)]
          exact List.mem_singleton.mpr rfl
        · -- the pair finishes AT this step: complete the reachable partial `(i, vi)`
          have hje : j = (toList xs).length := by omega
          subst hje
          have hib : i < (toList xs).length := hij
          have hdi' : (toList xs)[i]? = some vi := by
            rw [List.getElem?_append_left hib] at hdi; exact hdi
          have hvj : x = vj := by
            rw [getElem?_append_right_zero] at hdj
            exact Option.some.inj hdj
          have ht : vi + x = target := by omega
          refine ⟨((toList xs).length, .part i vi), (ih _).mpr ⟨rfl, hdi'⟩, ?_⟩
          show ((toList xs).length + 1, TSChoice.found i (toList xs).length) ∈
            (if vi + x = target
              then [((toList xs).length + 1, TSChoice.part i vi),
                    ((toList xs).length + 1, TSChoice.found i (toList xs).length)]
              else [((toList xs).length + 1, TSChoice.part i vi)])
          rw [if_pos ht]
          exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-! ## The DERIVED program and its Corollary-8.1 correctness -/

/-- **The derived program**: run the thinning driver's emitted fold (extend the kept frontier,
    prune by `Q`) and read off the `R`-best kept candidate's answer.  Never written by hand —
    `foldFn`/`solveFn` come from `ThinBest`. -/
def thinTwoSum (nums : List Int) (target : Int) : Option (Nat × Nat) :=
  match (tsB target).solveFn (ofNums nums) with
  | some b => outc b.2
  | none => none

theorem gen_spec (target : Int) (xs : SnocList Unit Int) (s : Nat × TSChoice)
    (h : cataFold (tsB target).gen xs s) :
    outc s.2 = none ∨ ∃ i j, outc s.2 = some (i, j) ∧ TwoSum (toList xs) target i j := by
  obtain ⟨-, hrc⟩ := (gen_char target xs s).mp h
  obtain ⟨n, c⟩ := s
  match c with
  | .start => exact Or.inl rfl
  | .part k v => exact Or.inl rfl
  | .found i j => exact Or.inr ⟨i, j, rfl, hrc⟩

theorem spec_gen (target : Int) (xs : SnocList Unit Int) (v : Option (Nat × Nat))
    (h : v = none ∨ ∃ i j, v = some (i, j) ∧ TwoSum (toList xs) target i j) :
    ∃ s : Nat × TSChoice, cataFold (tsB target).gen xs s ∧ outc s.2 = v := by
  rcases h with rfl | ⟨i, j, rfl, hts⟩
  · exact ⟨((toList xs).length, .start), (gen_char target xs _).mpr ⟨rfl, trivial⟩, rfl⟩
  · exact ⟨((toList xs).length, .found i j), (gen_char target xs _).mpr ⟨rfl, hts⟩, rfl⟩

/-- **Corollary 8.1, read for Two Sum** (via `ThinBest.correct_value`): the derived program's
    `some (i, j)` is a genuine valid pair AND the `ansLe`-maximum of all valid pairs (smallest
    second index, then largest first index); its `none` rules every valid pair out. -/
theorem thinTwoSum_correct (nums : List Int) (target : Int) :
    (∀ i j, thinTwoSum nums target = some (i, j) →
      TwoSum nums target i j ∧
        ∀ i' j', TwoSum nums target i' j' → j < j' ∨ (j = j' ∧ i' ≤ i)) ∧
    (thinTwoSum nums target = none → ∀ i j, ¬ TwoSum nums target i j) := by
  have hsome : ((tsB target).solveFn (ofNums nums)).isSome = true := by
    apply ThinBest.solveFn_isSome
    · intro u; exact List.cons_ne_nil _ _
    · rintro ⟨n, c⟩ x
      match c with
      | .start => exact List.cons_ne_nil _ _
      | .part k v => exact List.ne_nil_of_mem mem_stay
      | .found i j => exact List.cons_ne_nil _ _
  cases hb : (tsB target).solveFn (ofNums nums) with
  | none => rw [hb] at hsome; exact absurd hsome (by simp)
  | some b =>
    have hcv := (tsB target).correct_value
      (fun xs v => v = none ∨ ∃ i j, v = some (i, j) ∧ TwoSum (toList xs) target i j)
      (fun s => outc s.2) ansLe (fun {z w} h => h)
      (gen_spec target) (spec_gen target) (ofNums nums) b hb
    simp only [toList_ofNums] at hcv
    have hthin : thinTwoSum nums target = outc b.2 := by
      unfold thinTwoSum
      rw [hb]
    constructor
    · intro i j hij
      rw [hthin] at hij
      rcases hcv.1 with hnone | ⟨i', j', heq, hts⟩
      · rw [hnone] at hij; exact absurd hij (by simp)
      · rw [heq] at hij
        injection hij with hp
        injection hp with hi hj
        subst hi; subst hj
        refine ⟨hts, fun i' j' hts' => ?_⟩
        have := hcv.2 (some (i', j')) (Or.inr ⟨i', j', rfl, hts'⟩)
        rw [heq] at this
        exact this
    · intro hnone i j hts
      rw [hthin] at hnone
      have := hcv.2 (some (i, j)) (Or.inr ⟨i, j, rfl, hts⟩)
      rw [hnone] at this
      exact this

/-! ## The classical program: a one-pass scan with a "seen" association-list sub-search -/

/-- `findComplement want seen` — the index of the first pair in `seen` whose value is `want`,
    if any (a linear search over the association list of earlier `(value, index)` pairs). -/
def findComplement (want : Int) : List (Int × Nat) → Option Nat
  | [] => none
  | (v, i) :: rest => if v = want then some i else findComplement want rest

/-- `go seen target xs` scans `xs`, carrying `seen` (the `(value, index)` pairs of everything
    already processed, so the next element's index is `seen.length`).  Returns the first hit. -/
def go (seen : List (Int × Nat)) (target : Int) : List Int → Option (Nat × Nat)
  | [] => none
  | x :: xs =>
    match findComplement (target - x) seen with
    | some i => some (i, seen.length)
    | none => go ((x, seen.length) :: seen) target xs

/-- **The program**: LeetCode 1's solution — a single left-to-right scan. -/
def twoSumFn (nums : List Int) (target : Int) : Option (Nat × Nat) := go [] target nums

/-- **The allegory program**: LeetCode 1's solution as a morphism `Input ⟶ Ans` in `Rel(Set)`. -/
def solve : Input ⟶ Ans := graph (fun p : List Int × Int => twoSumFn p.1 p.2)

/-! ## `findComplement` reflects membership in `seen` -/

theorem findComplement_some : ∀ {seen : List (Int × Nat)} {want : Int} {i : Nat},
    findComplement want seen = some i → (want, i) ∈ seen := by
  intro seen
  induction seen with
  | nil => intro want i h; simp [findComplement] at h
  | cons p rest ih =>
    intro want i h
    obtain ⟨v, k⟩ := p
    simp only [findComplement] at h
    split at h
    · rename_i heq
      have hik : k = i := by injection h
      rw [← heq, ← hik]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem findComplement_none : ∀ {seen : List (Int × Nat)} {want : Int},
    findComplement want seen = none → ∀ i, (want, i) ∉ seen := by
  intro seen
  induction seen with
  | nil => intro want _ i hmem; exact absurd hmem (List.not_mem_nil)
  | cons p rest ih =>
    intro want h i hmem
    obtain ⟨v, k⟩ := p
    simp only [findComplement] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hne
      rcases List.mem_cons.mp hmem with heq2 | hmem'
      · injection heq2 with hv _
        exact hne hv.symm
      · exact ih h i hmem'

/-! ## The loop invariants of the scan -/

/-- `seen` records exactly the `(value, index)` pairs of `done`. -/
def SeenIff (done : List Int) (seen : List (Int × Nat)) : Prop :=
  ∀ v i, (v, i) ∈ seen ↔ done[i]? = some v

/-- Pushing the next element onto `seen` preserves the exact-record invariant. -/
theorem seenIff_push {done : List Int} {seen : List (Int × Nat)} {x : Int}
    (hlen : seen.length = done.length) (hseen : SeenIff done seen) :
    SeenIff (done ++ [x]) ((x, seen.length) :: seen) := by
  intro v i
  constructor
  · intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hvx hik
      rw [hvx, hik, hlen]
      exact getElem?_append_right_zero
    · have hdi := (hseen v i).mp hmem'
      have hib : i < done.length := (List.getElem?_eq_some_iff.mp hdi).1
      rw [List.getElem?_append_left hib]
      exact hdi
  · intro hdi'
    have hib : i < (done ++ [x]).length := (List.getElem?_eq_some_iff.mp hdi').1
    rcases Nat.lt_or_ge i done.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hdi'
      exact List.mem_cons_of_mem _ ((hseen v i).mpr hdi')
    · have hieq : i = done.length := by
        simp only [List.length_append, List.length_singleton] at hib
        omega
      rw [hieq, getElem?_append_right_zero] at hdi'
      injection hdi' with hxv
      have hiseen : i = seen.length := hieq.trans hlen.symm
      rw [← hxv, hiseen]
      exact List.mem_cons_self ..

/-- If the processed prefix has no valid pair and the complement search for the next element
    misses, the extended prefix still has no valid pair. -/
theorem noPair_push {done : List Int} {seen : List (Int × Nat)} {x target : Int}
    (hseen : SeenIff done seen) (hnp : ∀ i j, ¬ TwoSum done target i j)
    (hmiss : findComplement (target - x) seen = none) :
    ∀ i j, ¬ TwoSum (done ++ [x]) target i j := by
  have hnew : ∀ (v : Int) (i : Nat), done[i]? = some v → v ≠ target - x := by
    intro v i hdi heq
    subst heq
    exact findComplement_none hmiss i ((hseen (target - x) i).mpr hdi)
  rintro i j ⟨hij, vi, vj, hdi, hdj, hsum⟩
  have hjb : j < (done ++ [x]).length := (List.getElem?_eq_some_iff.mp hdj).1
  simp only [List.length_append, List.length_singleton] at hjb
  rcases Nat.lt_or_ge j done.length with hjlt | hjge
  · have hib : i < done.length := by omega
    rw [List.getElem?_append_left hib] at hdi
    rw [List.getElem?_append_left hjlt] at hdj
    exact hnp i j ⟨hij, vi, vj, hdi, hdj, hsum⟩
  · have hjeq : j = done.length := by omega
    have hib : i < done.length := by omega
    rw [List.getElem?_append_left hib] at hdi
    rw [hjeq, getElem?_append_right_zero] at hdj
    injection hdj with hxvj
    exact hnew vi i hdi (by omega)

/-! ## Scan correctness AND optimality: ONE generalized induction

  Soundness (a returned pair is a hit), completeness (`none` means no pair), and optimality —
  the scan returns the pair with the SMALLEST second index (the first hit), and among those the
  LARGEST first index (`findComplement` searches `seen` prepend-newest, so the first hit is the
  most recent occurrence of the complement value).  Optimality pins the scan's answer as the
  `ansLe`-maximum — the fact that identifies it with the thinning-derived program. -/

/-- `findComplement` returns a maximal index: no member of `seen` holding the same value has a
    larger index.  (An invariant of the scan's `seen`, whose entries are prepended with strictly
    increasing indices.) -/
def FCmax (seen : List (Int × Nat)) : Prop :=
  ∀ v i m, (v, i) ∈ seen → findComplement v seen = some m → i ≤ m

/-- Pushing a FRESH index (larger than everything in `seen`) preserves `FCmax`. -/
theorem fcmax_push {seen : List (Int × Nat)} {x : Int} {n : Nat}
    (hb : ∀ v i, (v, i) ∈ seen → i < n) (hm : FCmax seen) : FCmax ((x, n) :: seen) := by
  intro v i m hmem hfc
  simp only [findComplement] at hfc
  split at hfc
  · -- the head `(x, n)` answers the search: `m = n` bounds every index in `seen`
    injection hfc with hnm
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with _ hin
      omega
    · have := hb v i hmem'
      omega
  · rename_i hxv
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hvx _
      exact absurd hvx.symm hxv
    · exact hm v i m hmem' hfc

theorem go_correct : ∀ (xs done : List Int) (seen : List (Int × Nat)) (target : Int),
    seen.length = done.length → SeenIff done seen → FCmax seen →
    (∀ i j, ¬ TwoSum done target i j) →
    (∀ i j, go seen target xs = some (i, j) → TwoSum (done ++ xs) target i j ∧
      ∀ i' j', TwoSum (done ++ xs) target i' j' → j < j' ∨ (j = j' ∧ i' ≤ i)) ∧
    (go seen target xs = none → ∀ i j, ¬ TwoSum (done ++ xs) target i j) := by
  intro xs
  induction xs with
  | nil =>
    intro done seen target _ _ _ hnp
    refine ⟨fun i j h => by simp [go] at h, fun _ => by rw [List.append_nil]; exact hnp⟩
  | cons x xs ih =>
    intro done seen target hlen hseen hfcm hnp
    rcases hfc : findComplement (target - x) seen with _ | c
    · -- `findComplement` missed: recurse with the pushed invariants.
      have hgo : go seen target (x :: xs) = go ((x, seen.length) :: seen) target xs := by
        show
          (match findComplement (target - x) seen with
            | some i => some (i, seen.length)
            | none => go ((x, seen.length) :: seen) target xs) =
          go ((x, seen.length) :: seen) target xs
        rw [hfc]
      have hb : ∀ v i, (v, i) ∈ seen → i < seen.length := by
        intro v i hm
        have := (List.getElem?_eq_some_iff.mp ((hseen v i).mp hm)).1
        omega
      have := ih (done ++ [x]) ((x, seen.length) :: seen) target (by simp [hlen])
        (seenIff_push hlen hseen) (fcmax_push hb hfcm) (noPair_push hseen hnp hfc)
      rw [List.append_assoc, List.singleton_append] at this
      exact ⟨fun i j h => this.1 i j (by rw [hgo] at h; exact h),
             fun h => this.2 (by rw [hgo] at h; exact h)⟩
    · -- `findComplement` hit `c`: the answer is `(c, seen.length)`.
      have hgo : go seen target (x :: xs) = some (c, seen.length) := by
        show
          (match findComplement (target - x) seen with
            | some i => some (i, seen.length)
            | none => go ((x, seen.length) :: seen) target xs) =
          some (c, seen.length)
        rw [hfc]
      have hmem : (target - x, c) ∈ seen := findComplement_some hfc
      have hdi0 : done[c]? = some (target - x) := (hseen (target - x) c).mp hmem
      have hib : c < done.length := (List.getElem?_eq_some_iff.mp hdi0).1
      refine ⟨fun i j h => ?_, fun h => absurd (hgo.symm.trans h) (by simp)⟩
      rw [hgo] at h
      injection h with hpair
      injection hpair with hi hj
      subst hi; subst hj
      constructor
      · -- sound: the returned pair is a genuine hit
        have hdi : (done ++ x :: xs)[c]? = some (target - x) := by
          rw [List.getElem?_append_left hib]; exact hdi0
        have hdj : (done ++ x :: xs)[seen.length]? = some x := by
          rw [hlen]; exact getElem?_append_right_zero
        exact ⟨by omega, target - x, x, hdi, hdj, by omega⟩
      · -- optimal: every valid pair loses to it under `ansLe`
        rintro i' j' ⟨hij', vi, vj, hdi', hdj', hsum⟩
        rcases Nat.lt_trichotomy j' done.length with hlt | heq | hgt
        · -- inside the processed prefix: excluded by the invariant
          have hib' : i' < done.length := Nat.lt_trans hij' hlt
          rw [List.getElem?_append_left hib'] at hdi'
          rw [List.getElem?_append_left hlt] at hdj'
          exact absurd ⟨hij', vi, vj, hdi', hdj', hsum⟩ (hnp i' j')
        · -- at the hit position: `i'` is bounded by `findComplement`'s maximal index
          have hib' : i' < done.length := heq ▸ hij'
          rw [List.getElem?_append_left hib'] at hdi'
          rw [heq, getElem?_append_right_zero] at hdj'
          injection hdj' with hxvj
          have hvi : vi = target - x := by omega
          have hic : i' ≤ c :=
            hfcm (target - x) i' c ((hseen (target - x) i').mpr (hvi ▸ hdi')) hfc
          right; exact ⟨by omega, hic⟩
        · left; omega

/-- **Scan correctness, bundled**: a returned pair is a genuine hit AND the `ansLe`-maximum
    valid pair; a `none` result rules every valid pair out. -/
theorem twoSum_correct (nums : List Int) (target : Int) :
    (∀ i j, twoSumFn nums target = some (i, j) → TwoSum nums target i j ∧
      ∀ i' j', TwoSum nums target i' j' → j < j' ∨ (j = j' ∧ i' ≤ i)) ∧
    (twoSumFn nums target = none → ∀ i j, ¬ TwoSum nums target i j) := by
  have hbase : SeenIff ([] : List Int) ([] : List (Int × Nat)) := fun v i => by simp
  have hnp0 : ∀ i j, ¬ TwoSum ([] : List Int) target i j := by
    rintro i j ⟨_, vi, vj, hdi, _⟩; simp at hdi
  have := go_correct nums [] [] target rfl hbase
    (fun v i m hm _ => absurd hm List.not_mem_nil) hnp0
  rwa [List.nil_append] at this

/-! ## The derived program IS the scan -/

/-- Both programs return THE `ansLe`-maximum valid pair (Cor 8.1 on the derived side,
    `twoSum_correct` on the scan side), and a maximum is unique — so they are equal. -/
theorem thin_eq_scan (nums : List Int) (target : Int) :
    thinTwoSum nums target = twoSumFn nums target := by
  obtain ⟨tsome, tnone⟩ := thinTwoSum_correct nums target
  obtain ⟨ssome, snone⟩ := twoSum_correct nums target
  cases hscan : twoSumFn nums target with
  | none =>
    cases hthin : thinTwoSum nums target with
    | none => rfl
    | some p =>
      obtain ⟨i, j⟩ := p
      exact absurd (tsome i j hthin).1 (snone hscan i j)
  | some p =>
    obtain ⟨i₀, j₀⟩ := p
    obtain ⟨hts0, hopt0⟩ := ssome i₀ j₀ hscan
    cases hthin : thinTwoSum nums target with
    | none => exact absurd hts0 (tnone hthin i₀ j₀)
    | some q =>
      obtain ⟨i, j⟩ := q
      obtain ⟨hts, hdom⟩ := tsome i j hthin
      have h1 := hdom i₀ j₀ hts0
      have h2 := hopt0 i j hts
      have heq : i = i₀ ∧ j = j₀ := by omega
      rw [heq.1, heq.2]

/-! ## The O(n)-expected hash program (data refinement)

  The scan's association-list lookup is linear; `AHashMap` (`AOP/A6_HashMap.lean`) makes each
  step ONE `find?` + ONE `insert`, `O(1)` expected (bucket count sized to `nums.length`).  Both
  `find?` and `findComplement` return the MOST-RECENTLY stored index (bucket/list are
  prepend-newest), so the simulation invariant is exact agreement of lookups. -/

/-- The hash scan: look the complement up in one bucket; a hit returns, a miss inserts. -/
def hashGo (target : Int) (m : AHashMap Nat) (i : Nat) : List Int → Option (Nat × Nat)
  | [] => none
  | x :: xs =>
    match find? m (target - x) with
    | some j => some (j, i)
    | none => hashGo target (Freyd.HashMap.insert m x i) (i + 1) xs

/-- **The efficient program**: the hash scan from the empty map (bucket count `nums.length`,
    so the load factor stays bounded) and index `0`. -/
def hashTwoSum (nums : List Int) (target : Int) : Option (Nat × Nat) :=
  hashGo target (mkHashMap Nat nums.length) 0 nums

/-- The hash map `find?`-models the assoc list `seen`, preserved by a step: inserting `x ↦ i`
    into a map modelling `seen` yields one modelling `(x, i) :: seen`
    (`find?_insert_self`/`find?_insert_other`, both constructive). -/
theorem hashModels_insert (m : AHashMap Nat) (seen : List (Int × Nat)) (x : Int) (i : Nat)
    (hmodel : ∀ want, find? m want = findComplement want seen) :
    ∀ want, find? (Freyd.HashMap.insert m x i) want = findComplement want ((x, i) :: seen) := by
  intro want
  simp only [findComplement]
  split
  · rename_i hxw
    rw [← hxw]
    exact find?_insert_self m x i
  · rename_i hxw
    rw [find?_insert_other m x i want (fun h => hxw h.symm)]
    exact hmodel want

/-- The hash scan agrees with the assoc-list scan whenever the map `find?`-models `seen`. -/
theorem hashGo_go (target : Int) :
    ∀ (xs : List Int) (m : AHashMap Nat) (seen : List (Int × Nat)) (i : Nat),
      (∀ want, find? m want = findComplement want seen) → i = seen.length →
      hashGo target m i xs = go seen target xs
  | [], m, seen, i, _, _ => rfl
  | x :: xs, m, seen, i, hmodel, hi => by
      subst hi
      simp only [hashGo, go]
      rw [hmodel (target - x)]
      cases findComplement (target - x) seen with
      | some j => rfl
      | none =>
          exact hashGo_go target xs (Freyd.HashMap.insert m x seen.length)
            ((x, seen.length) :: seen) (seen.length + 1)
            (hashModels_insert m seen x seen.length hmodel) rfl

/-- The hash program computes exactly `twoSumFn` — the empty map `find?`-models the empty
    accumulator (`find?_mkHashMap`) and index `0 = [].length`. -/
theorem hashTwoSum_eq (nums : List Int) (target : Int) :
    hashTwoSum nums target = twoSumFn nums target :=
  hashGo_go target nums (mkHashMap Nat nums.length) [] 0
    (fun want => by rw [find?_mkHashMap]; rfl) rfl

/-- The thinning-derived program computes exactly the `O(n)`-expected hash program:
    spec → (Cor 8.1) → pruned frontier fold → (data refinement) → hash scan. -/
theorem thin_eq_hash (nums : List Int) (target : Int) :
    thinTwoSum nums target = hashTwoSum nums target := by
  rw [thin_eq_scan, hashTwoSum_eq]

/-! ## Headline: `solve = Λ spec ≫ maxRel D` (the `leet/L53.lean` form, for Two Sum) -/

/-- The DERIVED program as a morphism equation: `graph thinTwoSum = Λ tsSpec ≫ maxRel D` —
    B&dM's `max D · Λ spec`, both halves supplied by Corollary 8.1. -/
theorem thin_eq_Λ_maxRel :
    (graph (fun p : List Int × Int => thinTwoSum p.1 p.2) : Input ⟶ Ans)
      = Λ tsSpec ≫ maxRel (fun w z => ansLe z w) := by
  apply eq_Λ_comp_maxRel
  · exact fun x y h1 h2 => ansLe_antisym h2 h1
  · -- the program's answer is acceptable
    intro p
    cases h : thinTwoSum p.1 p.2 with
    | none => exact Or.inl ⟨rfl, (thinTwoSum_correct p.1 p.2).2 h⟩
    | some q =>
      obtain ⟨i, j⟩ := q
      exact Or.inr ⟨i, j, rfl, ((thinTwoSum_correct p.1 p.2).1 i j h).1⟩
  · -- ... and dominates every acceptable answer
    rintro p v (⟨rfl, hnp⟩ | ⟨i, j, rfl, hts⟩)
    · trivial
    · cases h : thinTwoSum p.1 p.2 with
      | none => exact absurd hts ((thinTwoSum_correct p.1 p.2).2 h i j)
      | some q =>
        obtain ⟨i', j'⟩ := q
        exact ((thinTwoSum_correct p.1 p.2).1 i' j' h).2 i j hts

/-- **HEADLINE.**  LeetCode 1's allegory program (the scan = the `O(n)` hash program) IS the
    function derived from its relational specification: `solve = Λ tsSpec ≫ maxRel D` in
    `Rel(Set)` — Two Sum by CALCULATION, the same morphism equation shape as Kadane's
    (`leet/L53.lean`'s `solve_eq_maxRel`), obtained through the THINNING theorem rather than
    the greedy/Horner one. -/
theorem solve_eq_Λ_maxRel :
    solve = Λ tsSpec ≫ maxRel (fun w z => ansLe z w) := by
  rw [← thin_eq_Λ_maxRel]
  show (graph (fun p : List Int × Int => twoSumFn p.1 p.2) : Input ⟶ Ans) = _
  exact congrArg (fun f : List Int × Int → Option (Nat × Nat) =>
    (graph f : Input ⟶ Ans)) (funext fun p => (thin_eq_scan p.1 p.2).symm)

/-! ## Running the programs -/

-- the DERIVED program (the driver's pruned fold, not the hand scan):
example : thinTwoSum [2, 7, 11, 15] 9 = some (0, 1) := by decide
-- duplicate values: the frontier keeps the LATEST index per value, like the scan
example : thinTwoSum [3, 3, 6] 9 = some (1, 2) := by decide
example : thinTwoSum [1, 2, 3] 100 = none := by decide

-- the scan and the hash program compute the same answers:
example : twoSumFn [2, 7, 11, 15] 9 = some (0, 1) := by decide
example : twoSumFn [3, 2, 4] 6 = some (1, 2) := by decide
example : hashTwoSum [3, 2, 4] 6 = some (1, 2) := by rw [hashTwoSum_eq]; decide

#eval thinTwoSum [2, 7, 11, 15] 9   -- some (0, 1)
#eval hashTwoSum [3, 2, 4] 6        -- some (1, 2)

end Freyd.Alg.RelSet.LC1
