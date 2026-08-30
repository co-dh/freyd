/-
  Greedy coin change (canonical system {1,2,5,10}) — a PARTIAL port of AoPA
  `Examples/GC/CoinChange.agda` (Mu–Oliveira, "Programming from Galois connections").

  SPEC (program-independent).  A valid change for an amount `n` is any coin list summing to `n`:
      `coinSpec n out  :=  sumVal out = n`.
  The wanted answer is the one using the FEWEST coins.  In AoPA this is the shrink
  `(sumc ○ ordered?)˘ ↾ _⊴_`: change relations shrunk by the sub-list order `_⊴_`, so the minimal
  (fewest-coin) solution survives — and via `A7_6.shrink_eq_Λ_comp_est` that shrink IS
  `A coinSpec ≫ est _⊴_`, the Bird & de Moor `min · Λ` optimum.

  WHAT IS PORTED HERE (self-contained, proved, axioms ⊆ {propext, Quot.sound}):
    * the coin algebra `Coin`/`val`/`sumVal` and the coin order `leC` (AoPA `_≤c_`);
    * the greedy program `greedy : ℕ → List Coin` (take the largest coin ≤ the remainder);
    * ACHIEVABILITY as a morphism inequality: `graph greedy ⊑ coinSpec` (`greedy_sound_rel`) —
      the greedy list always makes exact change (the `hsound` half of the headline).

  WHAT IS BLOCKED (precise diagnosis — NOT a `sorry`, deliberately omitted).  The full AoPA
  derivation `graph greedy = A coinSpec ≫ est _⊴_` needs two things the repo does not yet have:
    (1) OPTIMALITY / the domination half.  AoPA proves it by the ~100-line exchange argument
        `greedy-lemma` (a finite case analysis over {1,2,5,10}) fed to the GENERIC-functor greedy
        theorem `Data.Generic.Greedy.greedy-ana-cxt`, together with `Data.Generic.Membership` (`ε`)
        and a well-founded-relation accessibility proof `wf`.  The repo's optimization layer is
        `A7_2.greedy`/`A7_4.horner_correct`, which are CATAMORPHISM (fold) greedy theorems;
        coin change is an ANAMORPHISM (`hylo In pick-max wf`, an amount→coins UNFOLD), for which the
        repo has no emergence/uniqueness law at the `Rel(Set)` level.  The generic greedy-ana theorem
        is being ported by a sibling agent; per the task this file must not depend on it.
    (2) UNIQUENESS.  `RelSet.eq_Λ_comp_est` pins the optimum by ANTISYMMETRY of the preference
        order; "fewest coins" ordered only by length is NOT antisymmetric.  AoPA restores
        antisymmetry with `ordered?` (canonical descending form) + the sub-list order `_⊴_`; porting
        that canonicalization + the `_⊴_` antisymmetry is the second missing piece.
  Both are LIST/combinatorial, not deep — but each is a substantial development, and (1) additionally
  waits on anamorphism infrastructure.  A follow-up with the generic greedy-ana layer can complete
  `graph greedy = A coinSpec ≫ est D` from the achievability proved here plus the exchange lemma.

  Mathlib-free.
-/
module

public import AOP.A7_6_Shrink
public import AOP.A7_4_Horner

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.GCCoinChange

open Freyd Freyd.Alg

/-! ## Coins (AoPA `Coin`, `val`, `_≤c_`) -/

/-- The coin denominations of the canonical UK-ish system.  (Lean identifiers cannot start with a
    digit, so AoPA `1p 2p 5p 10p` become `p1 p2 p5 p10`.) -/
inductive Coin | p1 | p2 | p5 | p10
  deriving DecidableEq

/-- AoPA `val`. -/
def val : Coin → Nat
  | .p1 => 1 | .p2 => 2 | .p5 => 5 | .p10 => 10

/-- The total value of a coin list (AoPA `sumc`). -/
def sumVal : List Coin → Nat
  | []      => 0
  | c :: cs => val c + sumVal cs

/-- AoPA `_≤c_ = fun val ˘ ○ _≤_ ○ fun val`: coins ordered by value. -/
def leC (c d : Coin) : Prop := val c ≤ val d

/-- Every coin is worth at least `1` — the reason greedy terminates and can always make change. -/
theorem val_pos (c : Coin) : 1 ≤ val c := by cases c <;> decide

/-! ## The greedy program (AoPA `pick-max` / `hylo In pick-max wf`) -/

/-- The largest coin worth at most `n` (for `n ≥ 1`; `p1` otherwise). -/
def largestCoin (n : Nat) : Coin :=
  if 10 ≤ n then .p10 else if 5 ≤ n then .p5 else if 2 ≤ n then .p2 else .p1

/-- The greedy pick is affordable: `val (largestCoin n) ≤ n` when `n ≥ 1`. -/
theorem largestCoin_le {n : Nat} (h : 1 ≤ n) : val (largestCoin n) ≤ n := by
  unfold largestCoin
  rcases Nat.lt_or_ge n 10 with h10 | h10
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · rw [if_neg (by omega)]
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · rw [if_neg (by omega)]; exact h        -- val .p1 = 1 ≤ n
      · rw [if_pos h2]; exact h2                -- val .p2 = 2 ≤ n
    · rw [if_pos h5]; exact h5                  -- val .p5 = 5 ≤ n
  · rw [if_pos h10]; exact h10                  -- val .p10 = 10 ≤ n

/-- Greedy with an explicit fuel bound (structural, so it reduces under `decide`).  `fuel = amount`
    always suffices because each coin removes at least `1`. -/
def greedyF : Nat → Nat → List Coin
  | 0,      _ => []
  | (f+1),  n => if n = 0 then [] else largestCoin n :: greedyF f (n - val (largestCoin n))

/-- **The greedy program** (AoPA `hylo In pick-max wf ∘ ten`): repeatedly take the largest coin
    worth at most the remaining amount. -/
def greedy (n : Nat) : List Coin := greedyF n n

/-! ## Achievability (the `hsound` half of the headline) -/

/-- Greedy makes exact change, given enough fuel.  Induction on fuel; each step removes a coin worth
    `≥ 1` and `≤ n`, so the remainder both shrinks (fuel stays sufficient) and closes the sum. -/
theorem greedy_sound_fuel : ∀ (f n : Nat), n ≤ f → sumVal (greedyF f n) = n
  | 0,     n, hn => by rw [Nat.le_zero.mp hn]; rfl
  | (f+1), n, hn => by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; rfl
      · have hle : val (largestCoin n) ≤ n := largestCoin_le hpos
        have hp  : 1 ≤ val (largestCoin n) := val_pos _
        have hrec : n - val (largestCoin n) ≤ f := by omega
        have IH := greedy_sound_fuel f (n - val (largestCoin n)) hrec
        show sumVal (greedyF (f+1) n) = n
        unfold greedyF
        rw [if_neg (by omega : ¬ n = 0)]
        show val (largestCoin n) + sumVal (greedyF f (n - val (largestCoin n))) = n
        rw [IH]; omega

/-- **Achievability.**  `sumVal (greedy n) = n` — the greedy list is a valid change for `n`. -/
theorem greedy_sound (n : Nat) : sumVal (greedy n) = n :=
  greedy_sound_fuel n n (Nat.le_refl n)

/-! ## The spec and the achievability morphism inequality -/

/-- `coinSpec n out`: `out` is change for `n` (program-independent; grounded in `sumVal`). -/
def coinSpec : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨List Coin⟩ := fun n out => sumVal out = n

/-- **Achievability, as a morphism inequality.**  `graph greedy ⊑ coinSpec`: the greedy program
    refines the change spec (it always produces a valid change).  This is the `hsound` half that a
    completed `graph greedy = A coinSpec ≫ est D` headline consumes; the missing `hbest`
    (fewest-coins domination) is the blocked exchange argument described in the file header. -/
theorem greedy_sound_rel : (graph greedy : (⟨Nat⟩ : RelSet.{0}) ⟶ ⟨List Coin⟩) ⊑ coinSpec :=
  RelSet.le_iff.mpr (fun n out h => by
    show sumVal out = n
    rw [show out = greedy n from h]; exact greedy_sound n)

/-! ## Executable sanity checks -/

/-- `greedy 7 = [5p, 2p]`. -/
example : greedy 7 = [Coin.p5, Coin.p2] := by decide
/-- `greedy 28 = [10p, 10p, 5p, 2p, 1p]`. -/
example : greedy 28 = [Coin.p10, Coin.p10, Coin.p5, Coin.p2, Coin.p1] := by decide
/-- Achievability, checked concretely. -/
example : sumVal (greedy 28) = 28 := by decide

end Freyd.Alg.RelSet.GCCoinChange
