/-
  LeetCode 14 — Longest Common Prefix — DERIVED as a cons-list catamorphism.

  `leet/L14.lean` computes the longest common prefix by folding `commonPrefix2` right-to-left over
  the list of strings, with a SINGLETON special case:

    * `lcpFn []          = []`
    * `lcpFn [s]         = s`                              -- NOT `commonPrefix2 s [] = []`
    * `lcpFn (s :: rest) = commonPrefix2 s (lcpFn rest)`   -- rest nonempty

  This is a front-to-back fold, but a NAIVE `foldr commonPrefix2 []` is WRONG: it collapses `[s]` to
  `commonPrefix2 s [] = []`, losing the single string.  The creative step of this derivation is the
  CARRIER that repairs the base/singleton ambiguity:

      C := Option (List Int)     -- `none` = "no string seen yet", `some p` = accumulated prefix

  On that carrier the base is `none` and the step is FORCED — `some s` on the first string seen,
  `some (commonPrefix2 s p)` thereafter — so the singleton case is no longer special, it is just the
  first `st` on `none`:

      g _        = none
      st s none     = some s
      st s (some p) = some (commonPrefix2 s p)

  RESHAPING the input onto the repo's canonical cons-list initial algebra `ConsList Unit (List Int)`
  (base at `wrap ()`, recursion on the tail — the `list A` of the book) and feeding `g`/`st`/`foldCL`
  to the general-carrier fold-uniqueness law `Freyd.Alg.RelSet.CL.consFold_unique`
  (`AOP/A6_GenFold.lean`) PRODUCES the fold as `cataR (consScalarAlg g st)` — it is never written
  by hand (`lcp_emerges`).  Reading out the answer (`proj : none ↦ []`, `some p ↦ p`) after the
  data conversion `ofList` recovers exactly `L14.lcpFn` (`bridge`), so the whole L14 program factors
  through the emergent catamorphism:  `derivedSolve = graph ofList ≫ cataR (…) ≫ graph proj`
  equals `L14.solve` (`derivedSolve_eq_solve`).

  Only the PROGRAM is derived.  Correctness — soundness (`lcpFn strs` is a common prefix) and
  maximality (it is the `<+:`-GREATEST common prefix, i.e. the LONGEST), the `<+:`-extremum shape —
  is REUSED verbatim from `L14.lcp_correct`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L14

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC14D

open Freyd Freyd.Alg.RelSet.CL List

/-! ## The `Option (List Int)` carrier and its cons-list fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here
  `C = Option (List Int)` — the running longest-common-prefix, tagged `none` until the first string
  is seen.  This tag is exactly what repairs the base/singleton ambiguity of `L14.lcpFn`. -/

/-- Base of the emergent algebra: `none` — no string has been folded in yet. -/
def g : Unit → Option (List Int) := fun _ => none

/-- Step of the emergent algebra: fold the head string `s` into the running prefix.  On `none` (the
    first string) it becomes `some s`; on `some p` it is the `commonPrefix2`-meet `some
    (commonPrefix2 s p)`.  The singleton case of `L14.lcpFn` is just `st _ none`. -/
def st : List Int → Option (List Int) → Option (List Int) :=
  fun s c => match c with
    | none   => some s
    | some p => some (LC14.commonPrefix2 s p)

/-- Read the answer out of the carrier: `none` (empty input) ↦ `[]`, `some p` ↦ `p`. -/
def proj : Option (List Int) → List Int
  | none   => []
  | some p => p

/-- The longest-common-prefix fold over the cons-list initial algebra `ConsList Unit (List Int)`,
    mirroring `L14.lcpFn` on the repaired carrier: `wrap _ ↦ none`, `cons s xs ↦ st s (foldCL xs)`. -/
def foldCL : ConsList Unit (List Int) → Option (List Int)
  | ConsList.wrap _    => none
  | ConsList.cons s xs => st s (foldCL xs)

/-- The base condition is a COMPUTATION, not a guess: `foldCL (wrap d) = g d`. -/
theorem foldCL_wrap : ∀ d : Unit, foldCL (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `foldCL`'s cons equation: `foldCL (cons s xs) = st s (foldCL xs)`. -/
theorem foldCL_cons :
    ∀ (s : List Int) (xs : ConsList Unit (List Int)), foldCL (ConsList.cons s xs) = st s (foldCL xs) :=
  fun _ _ => rfl

/-! ## The LCP fold EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The longest-common-prefix fold, reshaped onto the cons-list initial algebra
    with the `Option (List Int)` carrier, IS the catamorphism of the emergent scalar algebra
    `consScalarAlg g st` — it was never written as a fold: `graph foldCL` equals
    `cataR (consScalarAlg g st)`.  The `Option` tag (which repairs the base/singleton ambiguity of
    `L14.lcpFn`) is the creative step; given it, the fold is emitted by `consFold_unique`. -/
theorem lcp_emerges :
    (graph foldCL : dCL Unit (List Int) ⟶ ⟨Option (List Int)⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st foldCL foldCL_wrap foldCL_cons

/-! ## Bridge to the hand-written raw-`List` program `L14.lcpFn` -/

/-- The `List (List Int) → ConsList Unit (List Int)` conversion onto the initial algebra:
    `[] ↦ wrap ()`, `s :: rest ↦ cons s (ofList rest)`. -/
def ofList : List (List Int) → ConsList Unit (List Int)
  | []        => ConsList.wrap ()
  | s :: rest => ConsList.cons s (ofList rest)

/-- On NONEMPTY input the fold has run at least one `st`, so it is `some (lcpFn …)` — never `none`.
    Induction on `rest`: the base `[s]` gives `st s none = some s = some (lcpFn [s])`; the step reads
    the tail's `some (lcpFn rest)` and applies `commonPrefix2`, matching `lcpFn`'s cons equation. -/
theorem foldCL_some : ∀ (rest : List (List Int)) (s : List Int),
    foldCL (ofList (s :: rest)) = some (LC14.lcpFn (s :: rest)) := by
  intro rest
  induction rest with
  | nil => intro s; rfl
  | cons s2 rest2 ih =>
    intro s
    show st s (foldCL (ofList (s2 :: rest2))) = some (LC14.lcpFn (s :: s2 :: rest2))
    rw [ih s2]; rfl

/-- **The bridge.**  Reading the answer out of the emergent fold on converted input recovers the
    hand-written program: `proj (foldCL (ofList strs)) = L14.lcpFn strs`.  Empty input folds to
    `none` (`proj none = [] = lcpFn []`); nonempty input to `some (lcpFn strs)` (`foldCL_some`). -/
theorem bridge : ∀ strs : List (List Int), proj (foldCL (ofList strs)) = LC14.lcpFn strs := by
  intro strs
  cases strs with
  | nil => rfl
  | cons s rest => rw [foldCL_some rest s]; rfl

/-! ## The whole L14 program factors through the emergent catamorphism -/

/-- The derived solver: convert the input to the cons-list (`graph ofList`), run the emergent
    catamorphism, then read the answer out (`graph proj`). -/
def derivedSolve : LC14.dInput ⟶ LC14.dAns :=
  (graph ofList : LC14.dInput ⟶ dCL Unit (List Int))
    ≫ cataR (consScalarAlg g st) ≫ (graph proj : (⟨Option (List Int)⟩ : RelSet.{0}) ⟶ LC14.dAns)

/-- **The derived solver IS `L14.solve`.**  Rewriting the emergent catamorphism back to `graph
    foldCL` (via `lcp_emerges`) turns `derivedSolve` into the graph of `proj ∘ foldCL ∘ ofList`,
    which the `bridge` identifies with `lcpFn` — so `derivedSolve = graph lcpFn = L14.solve`.  The
    hand-written L14 program is exactly the law-produced fold, wrapped by the data conversion and
    answer read-out. -/
theorem derivedSolve_eq_solve : derivedSolve = LC14.solve := by
  show (graph ofList : LC14.dInput ⟶ dCL Unit (List Int))
        ≫ cataR (consScalarAlg g st) ≫ (graph proj : (⟨Option (List Int)⟩ : RelSet.{0}) ⟶ LC14.dAns)
      = graph LC14.lcpFn
  rw [← lcp_emerges]
  apply hom_ext; intro strs y
  constructor
  · rintro ⟨cl, rfl, ov, rfl, rfl⟩
    exact bridge strs
  · intro hy
    exact ⟨ofList strs, rfl, foldCL (ofList strs), rfl, by rw [hy]; exact (bridge strs).symm⟩

/-! ## Correctness carries over from `L14.lean` (no re-proof of soundness / maximality) -/

/-- **Headline.**  The honest bundle: (1) the longest-common-prefix fold, reshaped onto the cons-list
    initial algebra with the `Option (List Int)` carrier, IS the catamorphism of `consScalarAlg g st`
    (`lcp_emerges`); (2) the whole L14 program factors through that emergent catamorphism —
    `derivedSolve = graph ofList ≫ cataR (…) ≫ graph proj` equals `L14.solve` (`derivedSolve_eq_solve`);
    and (3) it is correct on nonempty input — `lcpFn strs` IS a common prefix of every string and is
    the `<+:`-GREATEST such (the LONGEST) — the REUSED `L14.lcp_correct`, whose soundness and
    maximality are NOT re-proved here. -/
theorem lcp_derived_correct :
    ((graph foldCL : dCL Unit (List Int) ⟶ ⟨Option (List Int)⟩) = cataR (consScalarAlg g st))
      ∧ (derivedSolve = LC14.solve)
      ∧ (∀ strs : List (List Int), strs ≠ [] →
           (∀ s ∈ strs, LC14.lcpFn strs <+: s) ∧
           (∀ p, (∀ s ∈ strs, p <+: s) → p <+: LC14.lcpFn strs)) :=
  ⟨lcp_emerges, derivedSolve_eq_solve, LC14.lcp_correct⟩

/-! ## Running / cross-checking the emergent fold against `leet/L14.lean`

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the extensionally-equal computable
  witnesses: `L14.lcpFn` on LeetCode 14's own examples, and the derived pipeline
  `proj ∘ foldCL ∘ ofList` (equal to `lcpFn` by `bridge`). -/

/-- `["flower","flow","flight"] → "fl"`. -/
example : LC14.lcpFn [[102, 108, 111, 119, 101, 114], [102, 108, 111, 119], [102, 108, 105, 103, 104, 116]]
    = [102, 108] := by decide

/-- `["dog","racecar","car"] → ""`. -/
example : LC14.lcpFn [[100, 111, 103], [114, 97, 99, 101, 99, 97, 114], [99, 97, 114]] = [] := by decide

/-- The derived pipeline `proj ∘ foldCL ∘ ofList` reproduces the L14 answer on `["fla","flb"] → "fl"`. -/
example : proj (foldCL (ofList [[102, 108, 97], [102, 108, 98]])) = [102, 108] := by decide

/-- The emergent fold genuinely relates the converted input to `foldCL` of it (whose `proj` is the
    longest common prefix). -/
example :
    cataFold (consScalarAlg g st) (ofList [[1, 2], [1, 3]]) (foldCL (ofList [[1, 2], [1, 3]])) := by
  have h : (graph foldCL : dCL Unit (List Int) ⟶ ⟨Option (List Int)⟩)
      (ofList [[1, 2], [1, 3]]) (foldCL (ofList [[1, 2], [1, 3]])) := rfl
  rw [lcp_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC14D
