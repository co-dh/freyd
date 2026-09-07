/-
  LeetCode 387 — First Unique Character in a String — DERIVED as TWO cons-list catamorphisms,
  now backed by an `AHashMap Nat` count table for `O(n)` EXPECTED time (was `O(n²)` in `L387.lean`:
  `scanFrom` re-scans the WHOLE string with `countL` at every candidate index).

  `leet/L387.lean` writes `firstUniqFn s := scanFrom s s 0`, a single left-to-right scan that calls
  `countL full c` (an `O(n)` linear count) at every position — `O(n)` positions × `O(n)` count each =
  `O(n²)`.  Here the SAME answer is produced by TWO passes, each an ordinary cons-fold:

    * **Pass 1 — count map.**  Carrier `C := AHashMap Nat` (char code ↦ occurrence count).  Base
      `g1 () = mkHashMap Nat 31` (an empty table); step `st1 x m = insert m x ((find? m x).getD 0 + 1)`
      — increment `x`'s bucket.  LeetCode 387's alphabet is bounded (≤ 26 lowercase letters), so a
      FIXED small bucket count already keeps every bucket short regardless of `s.length`: `O(1)`
      expected per `find?`/`insert`, `O(n)` total to build the table (informal, as
      `AOP/A6_HashMap.lean` documents — Lean proves behaviour, not asymptotics).
    * **Pass 2 — CPS scan.**  Carrier `C := Nat → Option Nat` (index ↦ answer), a residual awaiting
      the current index, closed over a FIXED count map `m` (mirrors `L1_derived`'s accumulator-as-
      continuation reshaping, `L205_derived`'s per-parameter algebra family).  Base `g2 () = fun _ =>
      none`; step `st2 m c rec i = if (find? m c).getD 0 = 1 then some i else rec (i + 1)` — ONE `O(1)`-
      expected lookup per position instead of an `O(n)` re-count.

  Both folds are ordinary `ConsList Unit Int` recursions (`consFold_unique`, `AOP/A6_GenFold.lean`);
  neither is hand-written as a fold — each EMERGES from the law given its forced `wrap`/`cons`
  equations (`rfl`).  Composing them (`derivedFirstUniqFn s := foldCL2 (countMap s) (CL.ofList s) 0`,
  the SHARED bridge `CL.ofList`, not redefined) is the whole program: `O(n)` expected overall.

  CORRECTNESS is REUSED, not re-proved.  The crux invariant `countMap_find` says the count map
  `find?`-MODELS `countL` exactly: `(find? (countMap s) c).getD 0 = countL s c` (`.getD 0` because an
  unseen key is `none`, matching count `0`), proved by ONE induction on `s` via `find?_insert_self` /
  `find?_insert_other`.  `foldCL2_ofList` then shows the CPS scan against `countMap full` computes the
  SAME answer as `LC387.scanFrom full` at every suffix, by rewriting each `if`-condition through the
  invariant.  Hence `derivedFirstUniqFn = LC387.firstUniqFn` pointwise, and `LC387.firstUniq_correct`
  (soundness + none-completeness, NOT re-proved here) transports onto the two-pass program.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.  Constructive case splits via `by_cases` (as
  `L387.lean`'s own `scanFrom_correct` does); `find?_insert_self`/`find?_insert_other` (never
  `beq_self_eq_true`) keep the hash-map lemmas classical-choice-free.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import AOP.A6_HashMap
import leet.L387

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC387D

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC387
open Freyd.Alg.RelSet.LC242 (countL countL_cons)
open Freyd.HashMap (AHashMap mkHashMap find? find?_insert_self find?_insert_other find?_mkHashMap)

/-! ## Pass 1 — the count map, as a cons-list fold over the carrier `AHashMap Nat`

  `countMapCL` mirrors no hand-written function: it is DEFINED by the forced base/step equations, so
  `consFold_unique` applies to it by `rfl`. -/

/-- Base of the emergent algebra: the empty suffix contributes an empty count table.  `31` is a fixed
    bucket-count constant — LeetCode 387's input alphabet (≤ 26 lowercase letters) is bounded, so a
    small fixed table already keeps every bucket short for any `s.length`. -/
def g1 : Unit → AHashMap Nat := fun _ => mkHashMap Nat 31

/-- Step of the emergent algebra: increment `x`'s bucket in the folded-tail's count table (`O(1)`
    expected: one `find?` + one `insert`). -/
def st1 : Int → AHashMap Nat → AHashMap Nat :=
  fun x m => Freyd.HashMap.insert m x ((find? m x).getD 0 + 1)

/-- The count-map fold over the cons-list initial algebra: `wrap _ ↦ g1 ()`, `cons x xs ↦ st1 x
    (countMapCL xs)`. -/
def countMapCL : ConsList Unit Int → AHashMap Nat
  | ConsList.wrap _    => g1 ()
  | ConsList.cons x xs => st1 x (countMapCL xs)

theorem countMapCL_wrap : ∀ d : Unit, countMapCL (ConsList.wrap d) = g1 d := fun _ => rfl

theorem countMapCL_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), countMapCL (ConsList.cons x xs) = st1 x (countMapCL xs) :=
  fun _ _ => rfl

/-- **The count-map fold EMERGES.**  `graph countMapCL` equals the catamorphism of `consScalarAlg g1
    st1` — the hash-table-building pass was never written as a fold, it is PRODUCED by
    `consFold_unique`. -/
theorem countMap_emerges :
    (graph countMapCL : dCL Unit Int ⟶ ⟨AHashMap Nat⟩) = cataR (consScalarAlg g1 st1) :=
  CL.consFold_unique g1 st1 countMapCL countMapCL_wrap countMapCL_cons

/-- The count map of a raw `List Int`, via the SHARED `CL.ofList` bridge. -/
def countMap (s : List Int) : AHashMap Nat := countMapCL (ofList s)

/-! ## The crux invariant: the count map `find?`-MODELS `countL` exactly -/

/-- **`countMap` computes `countL`.**  `(find? (countMap s) c).getD 0 = countL s c` for every `c` —
    an unseen key is `none`, matching count `0` (`.getD 0`).  ONE induction on `s`: the fresh/seen
    branches of `st1`'s increment are read off by `find?_insert_self`/`find?_insert_other`. -/
theorem countMap_find : ∀ (s : List Int) (c : Int), (find? (countMap s) c).getD 0 = countL s c
  | [], c => by
      show (find? (mkHashMap Nat 31) c).getD 0 = 0
      rw [find?_mkHashMap]
      rfl
  | x :: xs, c => by
      show (find? (Freyd.HashMap.insert (countMap xs) x ((find? (countMap xs) x).getD 0 + 1)) c).getD 0
          = countL (x :: xs) c
      rw [countL_cons]
      by_cases hc : c = x
      · rw [hc, find?_insert_self, Option.getD_some, countMap_find xs x, if_pos rfl]
      · rw [find?_insert_other _ _ _ _ hc, countMap_find xs c, if_neg hc, Nat.add_zero]

/-! ## Pass 2 — the CPS scan, as a cons-list fold over the residual carrier `Nat → Option Nat`

  Closed over a FIXED count map `m` (an algebra FAMILY indexed by `m`, mirroring `L205_derived`'s
  `st target`/`L1_derived`'s `st target`).  The residual `Carrier2` awaits only the current index —
  the map does not change across this pass, so it is a parameter, not a carrier component. -/

/-- The residual carrier: given the current index, the (still-to-be-determined) answer. -/
abbrev Carrier2 : Type := Nat → Option Nat

/-- Base of the emergent algebra: the empty suffix answers `none` at every index. -/
def g2 : Unit → Carrier2 := fun _ _ => none

/-- Step of the emergent algebra: at head `c` with folded-tail residual `rec`, answer index `i` by
    `some i` if `c`'s count (read off `m` in `O(1)` expected) is `1`, else defer to `rec (i + 1)`. -/
def st2 (m : AHashMap Nat) : Int → Carrier2 → Carrier2 :=
  fun c rec i => if (find? m c).getD 0 = 1 then some i else rec (i + 1)

/-- The CPS-scan fold over the cons-list initial algebra, for a fixed count map `m`: `wrap _ ↦ g2 ()`,
    `cons c xs ↦ st2 m c (foldCL2 m xs)`. -/
def foldCL2 (m : AHashMap Nat) : ConsList Unit Int → Carrier2
  | ConsList.wrap _    => g2 ()
  | ConsList.cons c xs => st2 m c (foldCL2 m xs)

theorem foldCL2_wrap (m : AHashMap Nat) : ∀ d : Unit, foldCL2 m (ConsList.wrap d) = g2 d :=
  fun _ => rfl

theorem foldCL2_cons (m : AHashMap Nat) :
    ∀ (c : Int) (xs : ConsList Unit Int), foldCL2 m (ConsList.cons c xs) = st2 m c (foldCL2 m xs) :=
  fun _ _ => rfl

/-- **The CPS scan EMERGES**, for every fixed count map `m`: `graph (foldCL2 m)` equals the
    catamorphism of `consScalarAlg g2 (st2 m)` — the O(1)-lookup scan was never written as a fold. -/
theorem scan_emerges (m : AHashMap Nat) :
    (graph (foldCL2 m) : dCL Unit Int ⟶ ⟨Carrier2⟩) = cataR (consScalarAlg g2 (st2 m)) :=
  CL.consFold_unique g2 (st2 m) (foldCL2 m) (foldCL2_wrap m) (foldCL2_cons m)

/-! ## Bridge: the two-pass program computes exactly `LC387.scanFrom` / `LC387.firstUniqFn` -/

/-- **The CPS scan against `countMap full` agrees with `LC387.scanFrom full` at every suffix `l`.**
    Induction on `l`; at each head `c` the `if`-conditions coincide by `countMap_find full c`. -/
theorem foldCL2_ofList (full : List Int) :
    ∀ (l : List Int) (i : Nat), foldCL2 (countMap full) (ofList l) i = scanFrom full l i
  | [], i => rfl
  | c :: rest, i => by
      show (if (find? (countMap full) c).getD 0 = 1 then some i
            else foldCL2 (countMap full) (ofList rest) (i + 1))
          = (if countL full c = 1 then some i else scanFrom full rest (i + 1))
      rw [countMap_find full c]
      by_cases hcount : countL full c = 1
      · rw [if_pos hcount, if_pos hcount]
      · rw [if_neg hcount, if_neg hcount]
        exact foldCL2_ofList full rest (i + 1)

/-- **The efficient program**: run pass 1 to build the count table, then pass 2's CPS scan from
    index `0` against it — `O(n)` expected overall, two passes instead of `L387.lean`'s `O(n²)`
    single re-scanning pass. -/
def derivedFirstUniqFn (s : List Int) : Option Nat := foldCL2 (countMap s) (ofList s) 0

/-- The two-pass program computes exactly `LC387.firstUniqFn`. -/
theorem derivedFirstUniqFn_eq (s : List Int) : derivedFirstUniqFn s = firstUniqFn s := by
  show foldCL2 (countMap s) (ofList s) 0 = scanFrom s s 0
  exact foldCL2_ofList s s 0

/-- The two-pass program as a morphism `Str ⟶ Ans` in `Rel(Set)`. -/
def derivedSolve : Str ⟶ Ans := graph derivedFirstUniqFn

/-- `derivedSolve` IS `LC387.solve` — reshaping changes nothing observable, only how the answer is
    PRODUCED (two `O(n)`-expected cons-folds instead of one `O(n²)` re-scanning pass). -/
theorem derivedSolve_eq_solve : derivedSolve = solve := by
  apply hom_ext; intro s a
  show a = derivedFirstUniqFn s ↔ a = firstUniqFn s
  rw [derivedFirstUniqFn_eq]

/-! ## Correctness of the derived program, transported from `LC387.firstUniq_correct` -/

/-- **The First-Unique-Character program is TWO emergent catamorphisms, and it is correct.**  The
    honest headline bundles:

    * `countMap_emerges` — the count-map pass IS `cataR (consScalarAlg g1 st1)`;
    * `scan_emerges (countMap s)` — the CPS lookup-scan pass IS `cataR (consScalarAlg g2 (st2 …))`;
    * soundness + none-completeness, REUSED from `LC387.firstUniq_correct` (not re-proved) and
      transported along `derivedFirstUniqFn_eq`. -/
theorem firstUniq_derived_correct (s : List Int) :
    ((graph countMapCL : dCL Unit Int ⟶ ⟨AHashMap Nat⟩) = cataR (consScalarAlg g1 st1)) ∧
    ((graph (foldCL2 (countMap s)) : dCL Unit Int ⟶ ⟨Carrier2⟩)
        = cataR (consScalarAlg g2 (st2 (countMap s)))) ∧
    (∀ i, derivedFirstUniqFn s = some i → IsFirstUniq s i) ∧
    (derivedFirstUniqFn s = none → ∀ (i : Nat) (c : Int), s[i]? = some c → countL s c ≥ 2) := by
  refine ⟨countMap_emerges, scan_emerges (countMap s), ?_, ?_⟩
  · intro i hi
    rw [derivedFirstUniqFn_eq] at hi
    exact (firstUniq_correct s).1 i hi
  · intro hnone i c hic
    rw [derivedFirstUniqFn_eq] at hnone
    exact (firstUniq_correct s).2 hnone i c hic

/-! ## Running / cross-checking the two-pass program

  `derivedFirstUniqFn` runs on `AHashMap` (an `Array` of buckets); `#eval` executes the actual O(n)-
  expected program.  For PROOF-level checks the kernel does not reduce the `Array`-backed hash ops
  through `decide`, so we transport across `derivedFirstUniqFn_eq` onto the kernel-reducible
  `firstUniqFn` and `decide` there. -/

-- letters encoded as distinct `Int`s: l=1 e=2 t=3 c=4 o=5 d=6
#eval derivedFirstUniqFn [1, 2, 2, 3, 4, 5, 6, 2]  -- some 0  ("leetcode" → 'l' at 0)
#eval derivedFirstUniqFn [97, 97]                   -- none    ("aa" → no unique char)

example : derivedFirstUniqFn [1, 2, 2, 3, 4, 5, 6, 2] = some 0 := by
  rw [derivedFirstUniqFn_eq]; decide
example : derivedFirstUniqFn [97, 97] = none := by
  rw [derivedFirstUniqFn_eq]; decide

/-- The count-map fold genuinely relates `ofList [1,2,2]` to its emergent count table, proved via
    `countMap_emerges` (no `decide` needed). -/
example : cataFold (consScalarAlg g1 st1) (ofList [1, 2, 2]) (countMapCL (ofList [1, 2, 2])) := by
  have h : (graph countMapCL : dCL Unit Int ⟶ ⟨AHashMap Nat⟩)
      (ofList [1, 2, 2]) (countMapCL (ofList [1, 2, 2])) := rfl
  rw [countMap_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC387D
