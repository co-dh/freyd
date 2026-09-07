/-
  LeetCode 49 — Group Anagrams — DERIVED as a cons-list catamorphism.

  `leet/L49.lean` computes the answer by a right fold over the input list of strings:

    * `groupFn []          = []`
    * `groupFn (s :: strs) = insertInto s (groupFn strs)`

  This is EXACTLY the recursion of a front-to-back cons-list fold — no carrier repair is needed
  (unlike `L14_derived`'s `Option` tag): the natural carrier `C := List (List (List Int))`
  (`L49.Groups`'s carrier, the accumulated groups) already matches `groupFn`'s own base and step
  verbatim, so

      g _   = []            -- base: no strings seen yet, no groups
      st s  = insertInto s  -- step: insert the head string into the running groups

  RESHAPING the input onto the repo's canonical cons-list initial algebra `ConsList Unit (List
  Int)` (base at `wrap ()`, recursion on the tail) via the SHARED `Freyd.Alg.RelSet.CL.ofList`
  bridge, and feeding `g`/`st`/`foldCL` to the general-carrier fold-uniqueness law
  `Freyd.Alg.RelSet.CL.consFold_unique` (`AOP/A6_GenFold.lean`) PRODUCES the fold as
  `cataR (consScalarAlg g st)` — it is never written by hand (`group_emerges`). Since the carrier
  already IS `Groups`'s carrier there is no answer-readout step: `derivedSolve = graph ofList ≫
  cataR (consScalarAlg g st)` equals `L49.solve` outright (`derivedSolve_eq_solve`), via the
  `bridge` lemma `foldCL (ofList strs) = L49.groupFn strs`.

  Only the PROGRAM is derived. Correctness (`group_correct`: membership preserved, non-empty
  groups, homogeneous groups, full anagram-class separation) is REUSED verbatim from
  `L49.group_correct`'s `GroupsWF` invariant, not re-proved.

  A hash-map upgrade of the O(n·G) association-scan inside `insertInto` (`G` = number of groups
  so far) is BLOCKED: `AOP/A6_HashMap.lean`'s `AHashMap` is `Int`-keyed and the anagram key here
  is a `List Int` (`L242.isort s`); there is no List-keyed hashing in the mathlib-free repo, so a
  genuine hash upgrade would require building List-key hashing from scratch, which is out of scope
  here (noted, not attempted). Complexity stays O(n·G) (worst case O(n²)), same as `L49.groupFn`.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L49

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC49D

open Freyd Freyd.Alg.RelSet.CL List

/-! ## The carrier is `Groups`'s own carrier: `List (List (List Int))`

  Unlike `L14_derived`'s `Option`-tagged carrier (needed to repair a base/singleton ambiguity),
  `L49.groupFn`'s recursion `groupFn (s :: strs) = insertInto s (groupFn strs)` already matches the
  cons-list step verbatim on the UNTAGGED carrier `C := List (List (List Int))`, so `g`/`st` are
  read off directly. -/

/-- Base of the emergent algebra: no strings folded in yet, no groups. -/
def g : Unit → List (List (List Int)) := fun _ => []

/-- Step of the emergent algebra: insert the head string `s` into the running groups — literally
    `L49.insertInto`, the program's own step. -/
def st : List Int → List (List (List Int)) → List (List (List Int)) := LC49.insertInto

/-- The group-fold over the cons-list initial algebra `ConsList Unit (List Int)`, mirroring
    `L49.groupFn` on the (untagged) carrier: `wrap _ ↦ []`, `cons s xs ↦ st s (foldCL xs)`. -/
def foldCL : ConsList Unit (List Int) → List (List (List Int))
  | ConsList.wrap _    => g ()
  | ConsList.cons s xs => st s (foldCL xs)

/-- The base condition is a COMPUTATION, not a guess: `foldCL (wrap d) = g d`. -/
theorem foldCL_wrap : ∀ D : Unit, foldCL (ConsList.wrap D) = g D := fun _ => rfl

/-- The step condition IS `foldCL`'s cons equation: `foldCL (cons s xs) = st s (foldCL xs)`. -/
theorem foldCL_cons :
    ∀ (s : List Int) (xs : ConsList Unit (List Int)), foldCL (ConsList.cons s xs) = st s (foldCL xs) :=
  fun _ _ => rfl

/-! ## The group fold EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.** The group-partition fold, reshaped onto the cons-list initial algebra with
    the (untagged) carrier `List (List (List Int))`, IS the catamorphism of the emergent scalar
    algebra `consScalarAlg g st` — it was never written as a fold: `graph foldCL` equals
    `cataR (consScalarAlg g st)`. -/
theorem group_emerges :
    (graph foldCL : dCL Unit (List Int) ⟶ ⟨List (List (List Int))⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st foldCL foldCL_wrap foldCL_cons

/-! ## Bridge to the hand-written raw-`List` program `L49.groupFn`, via the SHARED `CL.ofList` -/

/-- **The bridge.** Folding over the `CL.ofList`-converted input recovers the hand-written
    program: `foldCL (ofList strs) = L49.groupFn strs`. Straight induction — `st`/`insertInto`
    agree definitionally, and `List.foldr`'s cons equation matches `foldCL`'s cons equation. -/
theorem bridge : ∀ strs : List (List Int), foldCL (ofList strs) = LC49.groupFn strs := by
  intro strs
  induction strs with
  | nil => rfl
  | cons s rest ih =>
    show st s (foldCL (ofList rest)) = LC49.insertInto s (LC49.groupFn rest)
    rw [ih]
    rfl

/-! ## The whole L49 program factors through the emergent catamorphism -/

/-- The derived solver: convert the input to the cons-list (`graph ofList`), then run the emergent
    catamorphism — no answer-readout step, since the carrier already IS `Groups`'s carrier. -/
def derivedSolve : LC49.Strs ⟶ LC49.Groups :=
  (graph ofList : LC49.Strs ⟶ dCL Unit (List Int)) ≫ cataR (consScalarAlg g st)

/-- **The derived solver IS `L49.solve`.** Rewriting the emergent catamorphism back to `graph
    foldCL` (via `group_emerges`) turns `derivedSolve` into the graph of `foldCL ∘ ofList`, which
    the `bridge` identifies with `groupFn` — so `derivedSolve = graph groupFn = L49.solve`. -/
theorem derivedSolve_eq_solve : derivedSolve = LC49.solve := by
  show (graph ofList : LC49.Strs ⟶ dCL Unit (List Int)) ≫ cataR (consScalarAlg g st)
      = graph LC49.groupFn
  rw [← group_emerges]
  apply hom_ext; intro strs y
  constructor
  · rintro ⟨cl, rfl, hy⟩
    exact hy.trans (bridge strs)
  · intro hy
    exact ⟨ofList strs, rfl, hy.trans (bridge strs).symm⟩

/-! ## Correctness carries over from `L49.lean` (no re-proof of the `GroupsWF` invariant) -/

/-- **Headline.** The honest bundle: (1) the group-partition fold, reshaped onto the cons-list
    initial algebra with the untagged carrier `List (List (List Int))`, IS the catamorphism of
    `consScalarAlg g st` (`group_emerges`); (2) the whole L49 program factors through that emergent
    catamorphism — `derivedSolve = graph ofList ≫ cataR (…)` equals `L49.solve`
    (`derivedSolve_eq_solve`); and (3) it is an honest partition into anagram classes — membership
    preserved, every group non-empty, every group homogeneous, and distinct groups never share an
    anagram-related pair — the REUSED `L49.group_correct`, whose `GroupsWF` invariant is NOT
    re-proved here. -/
theorem group_derived_correct :
    ((graph foldCL : dCL Unit (List Int) ⟶ ⟨List (List (List Int))⟩) = cataR (consScalarAlg g st))
      ∧ (derivedSolve = LC49.solve)
      ∧ (∀ strs : List (List Int),
           (∀ x, x ∈ strs ↔ ∃ gr ∈ LC49.groupFn strs, x ∈ gr) ∧
           (∀ gr ∈ LC49.groupFn strs, gr ≠ []) ∧
           (∀ gr ∈ LC49.groupFn strs, ∀ s ∈ gr, ∀ t ∈ gr, LC49.IsAnagram s t) ∧
           (∀ g1 ∈ LC49.groupFn strs, ∀ g2 ∈ LC49.groupFn strs,
              ∀ s ∈ g1, ∀ t ∈ g2, LC49.IsAnagram s t → g1 = g2)) :=
  ⟨group_emerges, derivedSolve_eq_solve, LC49.group_correct⟩

/-! ## Running / cross-checking the emergent fold against `leet/L49.lean` -/

-- letters as distinct Ints: e=1 a=2 t=3 n=4 b=5
-- "eat"=[1,2,3] "tea"=[3,1,2] "tan"=[3,2,4] "ate"=[2,3,1] "nat"=[4,2,3] "bat"=[5,2,3]
/-- The derived fold, over `CL.ofList`-converted input, reproduces `L49.groupFn`'s answer. -/
example : foldCL (ofList [[1,2,3], [3,1,2], [3,2,4], [2,3,1], [4,2,3], [5,2,3]]) =
    [[[5,2,3]], [[3,2,4],[4,2,3]], [[1,2,3],[3,1,2],[2,3,1]]] := by decide

example : foldCL (ofList ([] : List (List Int))) = [] := by decide

/-- The emergent fold genuinely relates the converted input to `foldCL` of it. -/
example :
    cataFold (consScalarAlg g st) (ofList [[1,2,3], [3,1,2]]) (foldCL (ofList [[1,2,3], [3,1,2]])) := by
  have h : (graph foldCL : dCL Unit (List Int) ⟶ ⟨List (List (List Int))⟩)
      (ofList [[1,2,3], [3,1,2]]) (foldCL (ofList [[1,2,3], [3,1,2]])) := rfl
  rw [group_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC49D
