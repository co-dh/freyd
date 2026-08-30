/-
  LeetCode 322 — Coin Change — as an ALLEGORY PROGRAM (`min·Λ` dynamic programming).

  Problem: given coin denominations `coins` (positive, possibly repeated — a non-empty
  `SnocList Nat Nat`) and a target `amount`, find the FEWEST coins (with repetition) summing to
  `amount`, or report "impossible".

  This is the archetypal Bird–de Moor DYNAMIC-PROGRAMMING shape (`AOP.A9_1`,
  `dynamic_programming`): unfold the amount `a` in ALL possible ways (pick a coin `c ≤ a`,
  leaving subproblem `a - c`), solve each subproblem recursively, refold by `+1` (using one more
  coin) and take the `≤`-MINIMUM over all choices.  Unlike `L121`/`L53`/`L152` (a linear scan over
  a `SnocList` of INPUT data), the recursion here is over the AMOUNT axis, and the "achievable"
  answer set can be empty (`amount` unreachable) — so the target lattice is `Option Nat`, `none`
  standing for `∞` ("impossible"), ordered so `none` is the TOP element (worse than every finite
  count).

  1. **The `∞` lattice.** `omin : Option Nat → Option Nat → Option Nat` (`none` = ∞ is the
     identity/top of `omin`) and `osucc : Option Nat → Option Nat` (`+1`, `none ↦ none`) — the
     small mathlib-free algebra the fold is built from.
  2. **Program.** `dp coins 0 = some 0`; `dp coins (a+1)` folds `omin` over every denomination `c`
     of `coins` with `1 ≤ c ≤ a+1`, contributing `osucc (dp coins (a+1-c))`.  Implemented via an
     explicit FUEL parameter (`dpFuel`) so the recursion is ordinary STRUCTURAL recursion on the
     fuel (not well-founded recursion on `<`), keeping the definition kernel-reducible — `decide`
     needs to unfold it directly, unlike `WellFounded.fix`-based recursion.
  3. **Specification.** `Achievable coins n a` — a multiset of exactly `n` coins from `coins`
     (each `≥ 1`, repetition allowed) sums to `a`. `coinSpec coins a k` is the extremum spec: `k =
     some n` iff `n` is the ≤-MINIMUM `n'` with `Achievable coins n' a`; `k = none` iff no `n'`
     achieves `a` at all. This is `min(≤)·Λ Achievable`, valued in the `∞`-extended lattice.
  4. **Correctness.** `dpFuel_spec`: for `a ≤ fuel`, `coinSpec coins a (dpFuel coins fuel a)` — by
     induction on `fuel`, reducing to a generic lemma about `coinFold` (the per-level `omin`-fold
     over the coin list) relating its `omin`-fold output to the `Achievable`-successor structure
     (`achievable_succ_iff`). Instantiating at `fuel = amount` gives `solve`'s full correctness:
     `coinSpec coins amount (solveFn coins amount)`, both refinement (achievability) and
     domination (minimality) in one theorem — `coinSpec` already bundles both halves, together
     with the `none`/impossibility direction (`L121`-style problems never needed this third case).

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_SnocList
import Freyd.Exacts

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC322

open Freyd Freyd.Alg.RelSet.SL

/-! ## The `∞`-extended lattice on `Option Nat` (`none` = ∞) -/

/-- `omin` — minimum on `Option Nat` with `none` (= ∞) as the top/identity element. -/
def omin : Option Nat → Option Nat → Option Nat
  | none, y => y
  | some x, none => some x
  | some x, some y => some (if x ≤ y then x else y)

/-- `osucc` — `+1` lifted to `Option Nat`, `none` (∞) stays `none`. -/
def osucc : Option Nat → Option Nat
  | none => none
  | some n => some (n + 1)

@[simp] theorem osucc_none : osucc none = none := rfl
@[simp] theorem osucc_some (n : Nat) : osucc (some n) = some (n + 1) := rfl

@[simp] theorem omin_none_left (y : Option Nat) : omin none y = y := rfl

theorem omin_eq_or (x y : Option Nat) : omin x y = x ∨ omin x y = y := by
  cases x with
  | none => exact Or.inr rfl
  | some x => cases y with
    | none => exact Or.inl rfl
    | some y =>
      show some (if x ≤ y then x else y) = some x ∨ some (if x ≤ y then x else y) = some y
      split
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem omin_none_iff (x y : Option Nat) : omin x y = none ↔ x = none ∧ y = none := by
  cases x with
  | none => cases y with
    | none => simp [omin]
    | some y => simp [omin]
  | some x => cases y with
    | none => simp [omin]
    | some y => simp [omin]

/-- Whichever finite value `omin x y` returns, it never exceeds a given finite `x`. -/
theorem omin_le_of_left {x y : Option Nat} {m : Nat} (h : x = some m) :
    ∃ k, omin x y = some k ∧ k ≤ m := by
  subst h
  cases y with
  | none => exact ⟨m, rfl, Nat.le_refl m⟩
  | some y => refine ⟨if m ≤ y then m else y, rfl, ?_⟩; split <;> omega

/-- Whichever finite value `omin x y` returns, it never exceeds a given finite `y`. -/
theorem omin_le_of_right {x y : Option Nat} {m : Nat} (h : y = some m) :
    ∃ k, omin x y = some k ∧ k ≤ m := by
  subst h
  cases x with
  | none => exact ⟨m, rfl, Nat.le_refl m⟩
  | some x => refine ⟨if x ≤ m then x else m, rfl, ?_⟩; split <;> omega

/-! ## Data: coin denominations as a snoc-list of `Nat`, membership -/

/-- `mem coins c` — `c` is one of the (positive) coin denominations in `coins`. -/
def mem : SnocList Nat Nat → Nat → Prop
  | SnocList.wrap x => fun c => c = x
  | SnocList.snoc xs p => fun c => mem xs c ∨ c = p

/-! ## Specification: achievable coin-counts, and their `≤`-minimum -/

/-- `Achievable coins n a` — some multiset of exactly `n` coins, each a (positive) denomination
    of `coins`, sums to `a`.  The `succ` case only ever uses `c ≥ 1`, matching `dp`'s own
    filtering, so the spec is exact for ANY `coins` list (zero-valued or duplicate denominations
    included). -/
inductive Achievable (coins : SnocList Nat Nat) : Nat → Nat → Prop where
  | zero : Achievable coins 0 0
  | succ {n a c : Nat} (h : Achievable coins n a) (hmem : mem coins c) (hpos : 1 ≤ c) :
      Achievable coins (n + 1) (a + c)

theorem achievable_zero_iff {coins : SnocList Nat Nat} {target : Nat} :
    Achievable coins 0 target ↔ target = 0 := by
  constructor
  · intro h; cases h with
    | zero => rfl
  · intro h; subst h; exact Achievable.zero

theorem achievable_succ_iff {coins : SnocList Nat Nat} {n target : Nat} :
    Achievable coins (n + 1) target ↔
      ∃ c, mem coins c ∧ 1 ≤ c ∧ c ≤ target ∧ Achievable coins n (target - c) := by
  constructor
  · intro h
    cases h with
    | succ h hmem hpos =>
      rename_i a c
      refine ⟨c, hmem, hpos, by omega, ?_⟩
      have heq : a + c - c = a := by omega
      rwa [heq]
  · rintro ⟨c, hmem, hpos, hle, hach⟩
    have heq : target - c + c = target := by omega
    rw [← heq]
    exact Achievable.succ hach hmem hpos

/-- **The specification**: `k` is the `≤`-minimum achievable coin-count for `amount`, or `none`
    if no multiset of `coins` sums to `amount` — `min(≤)·Λ Achievable`, `∞`-extended. -/
def coinSpec (coins : SnocList Nat Nat) (amount : Nat) : Option Nat → Prop
  | some n => Achievable coins n amount ∧ ∀ n', Achievable coins n' amount → n ≤ n'
  | none => ∀ n, ¬ Achievable coins n amount

/-! ## Program: the DP fold over the amount axis, via a structural fuel parameter -/

/-- One coin's contribution to target `t`: `osucc` of the (already-computed, smaller) answer for
    `t - c`, if `c` is a valid denomination (`1 ≤ c ≤ t`); else no contribution (`none` = ∞). -/
def contrib (step : Nat → Option Nat) (t c : Nat) : Option Nat :=
  if 1 ≤ c ∧ c ≤ t then osucc (step (t - c)) else none

theorem contrib_some_iff {step : Nat → Option Nat} {t c m : Nat} :
    contrib step t c = some m ↔ 1 ≤ c ∧ c ≤ t ∧ ∃ mv, step (t - c) = some mv ∧ m = mv + 1 := by
  unfold contrib
  by_cases h : 1 ≤ c ∧ c ≤ t
  · rw [if_pos h]
    constructor
    · intro hc
      rcases hs : step (t - c) with _ | mv
      · rw [hs, osucc_none] at hc; exact absurd hc (by simp)
      · rw [hs, osucc_some, Option.some.injEq] at hc
        exact ⟨h.1, h.2, mv, rfl, hc.symm⟩
    · rintro ⟨_, _, mv, hs, hm⟩
      rw [hs, osucc_some, hm]
  · rw [if_neg h]
    constructor
    · intro hc; exact absurd hc (by simp)
    · intro hc; exact absurd ⟨hc.1, hc.2.1⟩ h

theorem contrib_none_iff {step : Nat → Option Nat} {t c : Nat} :
    contrib step t c = none ↔ ¬(1 ≤ c ∧ c ≤ t) ∨ step (t - c) = none := by
  unfold contrib
  by_cases h : 1 ≤ c ∧ c ≤ t
  · rw [if_pos h]
    rcases hs : step (t - c) with _ | mv
    · simp
    · simp [h]
  · rw [if_neg h]
    simp [h]

/-- Fold `contrib` over every denomination in `cs`, taking the running `omin`. -/
def coinFold (step : Nat → Option Nat) (t : Nat) : SnocList Nat Nat → Option Nat
  | SnocList.wrap c => contrib step t c
  | SnocList.snoc cs c => omin (coinFold step t cs) (contrib step t c)

/-- If the fold over `cs` returns a finite value, SOME denomination of `cs` achieves it. -/
theorem coinFold_achieves {step : Nat → Option Nat} {t m : Nat} :
    ∀ cs, coinFold step t cs = some m →
      ∃ c mv, mem cs c ∧ 1 ≤ c ∧ c ≤ t ∧ step (t - c) = some mv ∧ m = mv + 1
  | SnocList.wrap c₀, h => by
    obtain ⟨h1, h2, mv, h3, h4⟩ := contrib_some_iff.mp h
    exact ⟨c₀, mv, rfl, h1, h2, h3, h4⟩
  | SnocList.snoc cs c₁, h => by
    have h' : omin (coinFold step t cs) (contrib step t c₁) = some m := h
    rcases omin_eq_or (coinFold step t cs) (contrib step t c₁) with he | he
    · rw [he] at h'
      obtain ⟨c, mv, hmem, h1, h2, h3, h4⟩ := coinFold_achieves cs h'
      exact ⟨c, mv, Or.inl hmem, h1, h2, h3, h4⟩
    · rw [he] at h'
      obtain ⟨h1, h2, mv, h3, h4⟩ := contrib_some_iff.mp h'
      exact ⟨c₁, mv, Or.inr rfl, h1, h2, h3, h4⟩

/-- If some denomination of `cs` gives a finite contribution, the fold is finite and no larger
    than `mv + 1`. -/
theorem coinFold_dominates {step : Nat → Option Nat} {t c mv : Nat} :
    ∀ cs, mem cs c → 1 ≤ c → c ≤ t → step (t - c) = some mv →
      ∃ m, coinFold step t cs = some m ∧ m ≤ mv + 1
  | SnocList.wrap c₀, hmem, hpos, hle, hstep => by
    have hc : c = c₀ := hmem
    subst hc
    exact ⟨mv + 1, contrib_some_iff.mpr ⟨hpos, hle, mv, hstep, rfl⟩, Nat.le_refl _⟩
  | SnocList.snoc cs c₁, hmem, hpos, hle, hstep => by
    rcases hmem with hmem | hmem
    · obtain ⟨m, hm, hle'⟩ := coinFold_dominates cs hmem hpos hle hstep
      obtain ⟨k, hk, hk'⟩ := omin_le_of_left (y := contrib step t c₁) hm
      exact ⟨k, hk, by omega⟩
    · have hY : contrib step t c₁ = some (mv + 1) := by
        rw [← hmem]; exact contrib_some_iff.mpr ⟨hpos, hle, mv, hstep, rfl⟩
      obtain ⟨k, hk, hk'⟩ := omin_le_of_right (x := coinFold step t cs) hY
      exact ⟨k, hk, hk'⟩

/-- The fold is `none` exactly when EVERY denomination of `cs` fails (invalid or gives `none`). -/
theorem coinFold_none_iff {step : Nat → Option Nat} {t : Nat} :
    ∀ cs, coinFold step t cs = none ↔ ∀ c, mem cs c → 1 ≤ c → c ≤ t → step (t - c) = none
  | SnocList.wrap c₀ => by
    constructor
    · intro h c hmem hpos hle
      have hc : c = c₀ := hmem
      subst hc
      rcases contrib_none_iff.mp h with h' | h'
      · exact absurd ⟨hpos, hle⟩ h'
      · exact h'
    · intro h
      apply contrib_none_iff.mpr
      by_cases hb : 1 ≤ c₀ ∧ c₀ ≤ t
      · exact Or.inr (h c₀ rfl hb.1 hb.2)
      · exact Or.inl hb
  | SnocList.snoc cs c₁ => by
    constructor
    · intro h c hmem hpos hle
      obtain ⟨hX, hY⟩ := (omin_none_iff _ _).mp h
      rcases hmem with hmem | hmem
      · exact (coinFold_none_iff cs).mp hX c hmem hpos hle
      · subst hmem
        rcases contrib_none_iff.mp hY with h' | h'
        · exact absurd ⟨hpos, hle⟩ h'
        · exact h'
    · intro h
      apply (omin_none_iff _ _).mpr
      refine ⟨(coinFold_none_iff cs).mpr (fun c hmem hpos hle => h c (Or.inl hmem) hpos hle), ?_⟩
      apply contrib_none_iff.mpr
      by_cases hb : 1 ≤ c₁ ∧ c₁ ≤ t
      · exact Or.inr (h c₁ (Or.inr rfl) hb.1 hb.2)
      · exact Or.inl hb

/-- The DP with an explicit FUEL bound — structural recursion on the fuel (not well-founded
    recursion on `<`), so it is kernel-reducible and `decide`-friendly.  `fuel = amount` always
    suffices, since each recursive level drops `amount` by at least `1` (coins are `≥ 1`). -/
def dpFuel (coins : SnocList Nat Nat) : Nat → Nat → Option Nat
  | 0, a => if a = 0 then some 0 else none
  | fuel + 1, a =>
    match a with
    | 0 => some 0
    | a' + 1 => coinFold (dpFuel coins fuel) (a' + 1) coins

/-- `dp coins amount` — the fewest coins from `coins` summing to `amount`, or `none` if
    impossible. -/
def dp (coins : SnocList Nat Nat) (amount : Nat) : Option Nat := dpFuel coins amount amount

/-- **The allegory program's answer function.** -/
def solveFn (coins : SnocList Nat Nat) (amount : Nat) : Option Nat := dp coins amount

/-! ## Correctness: `dpFuel` computes exactly the extremum spec -/

/-- **Core correctness lemma**: for any fuel bound `a ≤ fuel`, `dpFuel coins fuel a` satisfies the
    extremum spec `coinSpec coins a` — by induction on `fuel`. -/
theorem dpFuel_spec (coins : SnocList Nat Nat) :
    ∀ fuel a, a ≤ fuel → coinSpec coins a (dpFuel coins fuel a) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a ha
    have ha0 : a = 0 := by omega
    subst ha0
    show coinSpec coins 0 (if (0 : Nat) = 0 then some 0 else none)
    simp only [if_true]
    exact ⟨Achievable.zero, fun n' _ => Nat.zero_le n'⟩
  | succ fuel ih =>
    intro a ha
    match a, ha with
    | 0, ha =>
      show coinSpec coins 0 (some 0)
      exact ⟨Achievable.zero, fun n' _ => Nat.zero_le n'⟩
    | a' + 1, ha =>
      have ha' : a' ≤ fuel := by omega
      show coinSpec coins (a' + 1) (coinFold (dpFuel coins fuel) (a' + 1) coins)
      rcases hres : coinFold (dpFuel coins fuel) (a' + 1) coins with _ | m
      · -- impossibility case
        intro n hn
        match n, hn with
        | 0, hn => exact absurd (achievable_zero_iff.mp hn) (by omega)
        | n' + 1, hn =>
          obtain ⟨c, hmem, hpos, hle, hach⟩ := achievable_succ_iff.mp hn
          have hspec := ih (a' + 1 - c) (by omega)
          rcases hstep : dpFuel coins fuel (a' + 1 - c) with _ | mv
          · rw [hstep] at hspec
            exact hspec n' hach
          · obtain ⟨m₀, hm₀, _⟩ := coinFold_dominates (step := dpFuel coins fuel) (t := a' + 1)
              coins hmem hpos hle hstep
            rw [hres] at hm₀
            exact absurd hm₀ (by simp)
      · -- achievability + minimality case
        obtain ⟨c, mv, hmem, hpos, hle, hstep, hm⟩ := coinFold_achieves coins hres
        have hspecStep := ih (a' + 1 - c) (by omega)
        rw [hstep] at hspecStep
        obtain ⟨hachStep, _⟩ := hspecStep
        have hsub : a' + 1 - c + c = a' + 1 := by omega
        have hachm : Achievable coins m (a' + 1) := by
          rw [hm, ← hsub]
          exact Achievable.succ hachStep hmem hpos
        refine ⟨hachm, ?_⟩
        intro n' hn'
        match n', hn' with
        | 0, hn' => exact absurd (achievable_zero_iff.mp hn') (by omega)
        | n'' + 1, hn' =>
          obtain ⟨c', hmem', hpos', hle', hach'⟩ := achievable_succ_iff.mp hn'
          have hspec' := ih (a' + 1 - c') (by omega)
          rcases hstep' : dpFuel coins fuel (a' + 1 - c') with _ | mv'
          · rw [hstep'] at hspec'
            exact absurd hach' (hspec' n'')
          · obtain ⟨hach'', hmin'⟩ := by rw [hstep'] at hspec'; exact hspec'
            have hmv' : mv' ≤ n'' := hmin' n'' hach'
            obtain ⟨m₀, hm₀, hm₀le⟩ := coinFold_dominates (step := dpFuel coins fuel) (t := a' + 1)
              coins hmem' hpos' hle' hstep'
            rw [hres] at hm₀
            have : m = m₀ := by rw [Option.some.injEq] at hm₀; exact hm₀
            omega

/-- **Correctness of the allegory program**: `solveFn` computes exactly the ≤-extremum of the
    achievable coin-count spec, at every `(coins, amount)`. -/
theorem solve_correct (coins : SnocList Nat Nat) (amount : Nat) :
    coinSpec coins amount (solveFn coins amount) :=
  dpFuel_spec coins amount amount (Nat.le_refl amount)

/-! ## `Rel(Set)` packaging -/

/-- The input object: coin denominations paired with a target amount. -/
abbrev dInput : RelSet.{0} := ⟨SnocList Nat Nat × Nat⟩
/-- The answer object: `Option Nat`, `none` standing for "impossible". -/
abbrev dAns : RelSet.{0} := ⟨Option Nat⟩

/-- **The allegory program**: LeetCode 322's DP solution as a morphism `dInput ⟶ dAns`. -/
def solve : dInput ⟶ dAns := graph (fun p => solveFn p.1 p.2)

/-- **The specification** as a morphism `dInput ⟶ dAns` in `Rel(Set)`: the `≤`-extremum of the
    achievable coin-count relation, `min(≤)·Λ Achievable`. -/
def spec : dInput ⟶ dAns := fun p k => coinSpec p.1 p.2 k

/-- **The program refines the specification** (in fact computes it exactly, since `coinSpec`
    already pins down a unique value): every answer `solve` returns satisfies `coinSpec`. -/
theorem solve_le_spec : solve ⊑ spec := by
  refine le_iff.mpr (fun p k h => ?_)
  have hk : k = solveFn p.1 p.2 := h
  rw [hk]; exact solve_correct p.1 p.2

/-! ## Why the correctness above is a direct fuel induction, NOT `A9_1.dynamic_programming`

  The natural hope is to derive `solve_correct` from Bird–de Moor's Theorem 9.1
  (`Freyd.Alg.dynamic_programming`, `AOP.A9_1`) by instantiating its abstract data at
  `Rel(Set)`:
  * functor `F X = Unit ⊕ (Nat × X)` — `Freyd.Alg.RelSet.CL.F Unit Nat`, whose initial algebra
    `ConsList Unit Nat` (`CL.initial Unit Nat`) is exactly "coin sequences";
  * amount coalgebra `T : F Nat ⟶ Nat` — `inl () ↦ 0`, `inr (c, a') ↦ a' + c` for valid `c`
    (`mem coins c ∧ 1 ≤ c`);
  * counting algebra `h : F Nat ⟶ Nat` — `inl () ↦ 0`, `inr (c, n) ↦ n + 1`;
  * cost order `R := (≤)` on `Nat`.

  This instantiation is entirely LEGAL — every hypothesis of `dynamic_programming` discharges:
  `Map h` (`graph_map`), `R ≫ R ⊑ R` (transitivity of `≤`), `MonotonicAlg h R`
  (`F.map (≤) ≫ h = h ≫ (≤)`, pointwise: both send `inr (c, m)` to `{k | m + 1 ≤ k}`),
  `F.PreservesRecip` (`CL.F_preservesRecip`), `InitialAlgebra` (`CL.initial Unit Nat`).  The
  SPECIFICATION side even identifies cleanly: with `H := (relCata I T)° ≫ relCata I h` one has
  `H a n ↔ Achievable coins n a`, and `Λ_comp_est` gives
  `Λ H ≫ est R = H ∩ (H° \ R°)`, so `(Λ H ≫ est R) a n ↔ coinSpec coins a (some n)`.

  What FAILS is the bridge from the executable `dp` to the theorem's `μ`-body.  That body,
  `Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R`, uses the EGLI–MILNER power relator `powerRel`
  (`AOP.A5_4`), whose "term₁" is `((∋)° \ (g ≫ (∋)°))`; on `Rel(Set)` this reads
  `powerRel g P Q → ∀ t ∈ P, ∃ u ∈ Q, g t u`.  Here `Λ (T°) a` is the FULL set of one-step
  decompositions of `a` (ALL valid coins `c ≤ a`), so `μ(body) a` is nonempty only when EVERY
  such coin leaves a solvable sub-amount `a − c`.  Coin change needs only ONE good
  decomposition: with `coins = {2, 3}`, amount `3` is solvable (a single `3`-coin,
  `dp = some 1`), yet the `c = 2` branch leaves the unsolvable sub-amount `1`, forcing
  `μ(body) 3 = ∅` (indeed `μ(body) 1 = ∅` already, since `1` has no valid coin, and that dead
  branch propagates up).  Hence `dp`-as-a-relation is NOT `⊑ μ(body)`, and Theorem 9.1's
  refinement `μ(body) ⊑ spec` cannot transport the executable's correctness — no amount of
  extra infrastructure removes this, it is a genuine semantic gap, not a missing lemma.

  Theorem 9.1 faithfully models DPs whose coalgebra unfolds a FINITE INPUT structure so that
  every branch is productive (B&dM's own §9.2/§9.4 — edit distance, compression — recurse on
  input lists, where every unfold reaches the base).  The amount-axis coin search, with dead
  sub-amounts, is not of that form, so the faithful choice is the direct fuel induction above.
  See the collector report for the full analysis. -/

/-! ## Running the program -/

/-- Build a coin list from a first denomination and the rest. -/
def ofList (first : Nat) (rest : List Nat) : SnocList Nat Nat :=
  rest.foldl SnocList.snoc (SnocList.wrap first)

example : solveFn (ofList 1 [2, 5]) 11 = some 3 := by decide
example : solveFn (ofList 2 []) 3 = none := by decide
example : solveFn (ofList 1 []) 0 = some 0 := by decide
example : solveFn (ofList 5 []) 3 = none := by decide

end Freyd.Alg.RelSet.LC322
