/-
  LeetCode 169 — Majority Element — as an ALLEGORY PROGRAM (Boyer–Moore voting).

  Problem: given `nums` in which some value occurs STRICTLY more than `⌊n/2⌋` times (LeetCode
  guarantees such a value exists), return it. The classic O(n) O(1)-space solution is the
  Boyer–Moore voting algorithm.

  Recipe (`Freyd/leetcode.md` S0): data is a plain `List Int` (as in `L56`/`L242`, no `SnocList`
  engine needed — the accumulator-fold shape is exactly `List.foldl`, which is structural/`rfl`-
  transparent, `Init/Data/List/Basic.lean`'s `List.foldl_cons`).

  1. **Program (the voting fold).** State `(cand : Int, cnt : Nat)`; for each `x`: if `cnt = 0`,
     start a new candidacy `(x, 1)`; else if `x = cand`, increment; else decrement (a "cancelling"
     vote). `majorityFn nums := (nums.foldl step (0,0)).1`.

  2. **Specification — honest, not a tautology.** `IsMajority nums v := 2 * countL nums v >
     nums.length` (`countL` reused from `leet.L242`, DRY) — `v` occurs strictly more than half the
     time. **Headline**: `majority_correct : IsMajority nums v → majorityFn nums = v`. (A strict
     majority is unique, so this pins `majorityFn` exactly whenever one exists; `majorityFn` is
     still total — on inputs with NO majority it returns some value, just not necessarily a useful
     one — so there is deliberately no `solve = spec`, cf. `L1`'s S34 note.)

  3. **The real content — the Boyer–Moore invariant.** `BMInv xs c k` says: after voting on the
     PROCESSED prefix `xs` (ending in state `(c,k)`), for every value `w`: if `w = c` then
     `2 * countL xs w ≤ xs.length + k`, and if `w ≠ c` then `2 * countL xs w + k ≤ xs.length`
     (phrased with `+k` on the LARGER side throughout, so it needs no `Nat` subtraction anywhere —
     only `step`'s own `cnt - 1` does, and only ever at `cnt ≠ 0`, i.e. a genuine positive
     predecessor). It is proved by a one-step lemma `step_inv` (extending the invariant across one
     `step`, by cases on `k = 0` / `x = c`, each closed by `omega` given a `countL`-of-snoc unfold)
     assembled over the whole list by `bmInv_gen` (generalizing over an arbitrary starting `(c,k)`
     already `BMInv`-compatible with a "processed so far" prefix — induction on the NEW suffix,
     peeling its head via `List.foldl_cons`, feeding the one-step lemma into the IH one element at
     a time). Dropping the `k ≥ 0` slack from the `w ≠ c` case gives exactly "any non-candidate
     appears at most half the time" (`noncand_le_half`), which is the whole proof of
     `majority_correct` by a two-way `by_cases` (this repo has no mathlib `by_contra`, S48).

  Mathlib-free. Axioms target `⊆ {propext, Quot.sound}` — the whole proof is `List` structural
  induction + `omega`, no `Classical.choice` anywhere (no `∃`/non-`False` goal is ever closed by
  `omega`/`simp` straight from a numeric contradiction, S33/S3).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet
import leet.L242

namespace Freyd.Alg.RelSet.LC169

open Freyd Freyd.Alg.RelSet.LC242

/-! ## Data: `nums : List Int`; answer: `Int` -/

/-- The object of input lists in `Rel(Set)`. -/
abbrev Nums : RelSet.{0} := ⟨List Int⟩
/-- The object of integers (the majority element) in `Rel(Set)`. -/
abbrev dZ : RelSet.{0} := ⟨Int⟩

/-! ## The program: the Boyer–Moore voting fold, state `(cand, cnt)` -/

/-- One voting step: a fresh candidacy when the count hits zero, an increment on a match, else a
    cancelling decrement. -/
def step (st : Int × Nat) (x : Int) : Int × Nat :=
  if st.2 = 0 then (x, 1) else if x = st.1 then (st.1, st.2 + 1) else (st.1, st.2 - 1)

/-- The answer: the final candidate after voting on the whole list (`List.foldl`, structural /
    `rfl`-transparent on `List`, no fuel needed). -/
def majorityFn (nums : List Int) : Int := (nums.foldl step (0, 0)).1

/-- **The allegory program**: LeetCode 169's solution as a morphism `Nums ⟶ ℤ` in `Rel(Set)`. -/
def solve : Nums ⟶ dZ := graph majorityFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map majorityFn

/-! ## Specification: `v` is a strict majority element -/

/-- `IsMajority nums v` — `v` occurs strictly more than half the time in `nums` (the honest
    LeetCode 169 precondition/spec, via `L242`'s `countL`). -/
def IsMajority (nums : List Int) (v : Int) : Prop := 2 * countL nums v > nums.length

/-! ## The Boyer–Moore invariant -/

/-- `countL` of a list with one more element `p` snoc'd on: the `List`-append form of `countL`'s
    own `cons` equation (`L242.countL_append` + the singleton case), reused across every `step`
    case below. -/
theorem countL_snoc (l : List Int) (p w : Int) :
    countL (l ++ [p]) w = countL l w + (if w = p then 1 else 0) := by
  simp [countL_append, countL_cons, countL_nil]

/-- **The Boyer–Moore invariant.** After voting on the processed prefix `xs`, ending in state
    `(c, k)`: the current candidate's count is bounded above by `xs.length + k`, and every OTHER
    value's count is bounded above by `xs.length - k` (phrased `+ k ≤ xs.length` to avoid `Nat`
    subtraction). -/
def BMInv (xs : List Int) (c : Int) (k : Nat) : Prop :=
  ∀ w, (w = c → 2 * countL xs w ≤ xs.length + k) ∧ (w ≠ c → 2 * countL xs w + k ≤ xs.length)

/-- The invariant holds trivially before any votes are cast. -/
theorem bmInv_nil (c0 : Int) : BMInv ([] : List Int) c0 0 := by
  intro w; constructor <;> intro _ <;> simp

/-- **The one-step lemma**: the invariant survives one more `step`. Three cases, matching `step`'s
    own branches: fresh candidacy (`k = 0`), a match (`x = c`), a cancelling decrement
    (`x ≠ c`, `k ≠ 0`) — each closed by `omega` once `countL_snoc` exposes the arithmetic. -/
theorem step_inv (pre : List Int) (c : Int) (k : Nat) (p : Int) (h : BMInv pre c k) :
    BMInv (pre ++ [p]) (step (c, k) p).1 (step (c, k) p).2 := by
  have hlen : (pre ++ [p]).length = pre.length + 1 := by simp
  by_cases hk0 : k = 0
  · -- fresh candidacy: new state (p, 1)
    have hstep : step (c, k) p = (p, 1) := by simp [step, hk0]
    rw [hstep]
    have hall : ∀ w, 2 * countL pre w ≤ pre.length := by
      intro w
      by_cases hwc : w = c
      · have hb := (h w).1 hwc; omega
      · have hb := (h w).2 hwc; omega
    intro w
    rw [countL_snoc]
    refine ⟨fun hwp => ?_, fun hwp => ?_⟩
    · rw [if_pos hwp]; have := hall w; omega
    · rw [if_neg hwp]; have := hall w; omega
  · by_cases hpc : p = c
    · -- a matching vote: new state (c, k+1)
      have hstep : step (c, k) p = (c, k + 1) := by simp [step, hk0, hpc]
      rw [hstep]
      intro w
      rw [countL_snoc]
      refine ⟨fun hwc => ?_, fun hwc => ?_⟩
      · have hb := (h w).1 hwc
        have hwp : w = p := hwc.trans hpc.symm
        rw [if_pos hwp]; omega
      · have hb := (h w).2 hwc
        have hwp : w ≠ p := by rw [hpc]; exact hwc
        rw [if_neg hwp]; omega
    · -- a cancelling vote: new state (c, k-1) (safe: k ≠ 0 here)
      have hstep : step (c, k) p = (c, k - 1) := by simp [step, hk0, hpc]
      rw [hstep]
      intro w
      rw [countL_snoc]
      refine ⟨fun hwc => ?_, fun hwc => ?_⟩
      · have hb := (h w).1 hwc
        have hwp : w ≠ p := by rw [hwc]; exact fun heq => hpc heq.symm
        rw [if_neg hwp]; omega
      · have hb := (h w).2 hwc
        by_cases hwp : w = p
        · rw [if_pos hwp]; omega
        · rw [if_neg hwp]; omega

/-- The invariant, generalized over an arbitrary starting state already compatible with a
    "processed so far" prefix — induction on the NEW suffix `xs`, peeling its head via
    `List.foldl_cons` and feeding `step_inv` into the IH one element at a time. -/
theorem bmInv_gen (xs : List Int) : ∀ (pre : List Int) (c : Int) (k : Nat), BMInv pre c k →
    BMInv (pre ++ xs) (List.foldl step (c, k) xs).1 (List.foldl step (c, k) xs).2 := by
  induction xs with
  | nil => intro pre c k h; simpa using h
  | cons y ys ih =>
    intro pre c k h
    rw [List.foldl_cons]
    have h' := step_inv pre c k y h
    have h2 := ih (pre ++ [y]) (step (c, k) y).1 (step (c, k) y).2 h'
    have heq : pre ++ [y] ++ ys = pre ++ (y :: ys) := by simp
    rwa [heq] at h2

/-- The invariant holds of the WHOLE list against the actual fold `majorityFn` runs. -/
theorem foldl_inv (xs : List Int) :
    BMInv xs (List.foldl step (0, 0) xs).1 (List.foldl step (0, 0) xs).2 := by
  have h := bmInv_gen xs [] 0 0 (bmInv_nil 0)
  simpa using h

/-- **Any value OTHER than the final candidate appears at most half the time.** The `w ≠ c` half of
    the invariant, instantiated at the whole list, with the `k`-slack dropped. -/
theorem noncand_le_half (nums : List Int) (v : Int) (hv : v ≠ majorityFn nums) :
    2 * countL nums v ≤ nums.length := by
  have h := (foldl_inv nums v).2 hv
  omega

/-! ## Correctness -/

/-- **`majorityFn` returns the strict majority element, whenever one exists.** A strict majority
    can't be a non-candidate (`noncand_le_half` would contradict `IsMajority`), so it must equal
    the fold's final candidate. -/
theorem majority_correct (nums : List Int) (v : Int) (hv : IsMajority nums v) :
    majorityFn nums = v := by
  by_cases heq : majorityFn nums = v
  · exact heq
  · exfalso
    have hne : v ≠ majorityFn nums := fun h => heq h.symm
    have hle := noncand_le_half nums v hne
    unfold IsMajority at hv
    omega

/-! ## The morphism-equation headline (preconditioned on the majority promise) -/

/-- The precondition coreflexive: the sub-identity passing only inputs that actually have a strict
    majority element (LeetCode 169's promise). -/
def pre : Nums ⟶ Nums := fun xs ys => xs = ys ∧ ∃ v, IsMajority xs v

/-- **The specification** as a morphism `Nums ⟶ ℤ`: `v` is THE majority element — it occurs
    strictly more than half the time — stated as `IsMajority`, independently of the voting fold. -/
def spec : Nums ⟶ dZ := fun nums v => IsMajority nums v

/-- **The allegory-program headline**: `pre ≫ solve = spec` — on inputs meeting the majority
    promise, the Boyer–Moore fold is exactly the majority-element specification.  (`majority_correct`
    gives that `majorityFn` equals any majority `v`, which forces the majority to be unique.) -/
theorem pre_solve_eq_spec : pre ≫ solve = spec := by
  apply hom_ext; intro nums v
  constructor
  · rintro ⟨ys, ⟨rfl, w, hw⟩, hv⟩
    have hv' : v = majorityFn nums := hv
    rw [hv']
    have := majority_correct nums w hw
    -- majorityFn nums = w, and IsMajority nums w; rewrite the goal's value to w
    rw [this]; exact hw
  · intro hv
    exact ⟨nums, ⟨rfl, v, hv⟩, by show v = majorityFn nums; rw [majority_correct nums v hv]⟩

/-! ## Running the program -/

example : majorityFn [3, 2, 3] = 3 := by decide
example : majorityFn [2, 2, 1, 1, 1, 2, 2] = 2 := by decide

end Freyd.Alg.RelSet.LC169
