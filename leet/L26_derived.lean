/-
  LeetCode 26 — Remove Duplicates from Sorted Array — DERIVED as a cons-list catamorphism.

  `leet/L26.lean` WRITES `dedupFn` as a two-element-LOOKAHEAD structural recursion over a RAW Lean
  `List Int`:

    * base   `dedupFn []            = []`
    * base   `dedupFn [x]           = [x]`
    * step   `dedupFn (x :: y :: r) = if x = y then dedupFn (y :: r) else x :: dedupFn (y :: r)`

  — at each element `x` it compares to the IMMEDIATE SUCCESSOR `y`, dropping `x` when they agree
  (the list is sorted, so equal elements are adjacent).  As written this is not a catamorphism for
  two reasons: its input `List Int` is not the repo's initial-algebra list, and — more essentially —
  the recurrence peeks at the NEXT element `y`, which a plain cons-fold `st : E → C → C` (head, then
  folded tail) cannot see directly.

  This file RESHAPES the data onto the canonical cons-list initial algebra `ConsList Unit Int`
  (`list Int` of the book, base at `wrap ()`, recursion on the tail) and DEFEATS the lookahead
  WITHOUT tupling an extra lookahead component (contrast `leet/L13_derived.lean`'s
  `Int × Option Int`): the carrier is simply

    * `C := List Int` — the already-deduped SUFFIX —

  because the suffix's OWN head is the successor `y` the step needs: `acc.head?` on the folded tail
  IS the lookahead.  The base/step are then ordinary and FORCED (both `rfl`):

    * base   `g _   = []`                                            = `foldFn (wrap _)`
    * step   `st x acc = if acc.head? = some x then acc else x :: acc` = `foldFn (cons x xs)` with
      `acc = foldFn xs`.

  Feeding `g`/`st`/`foldFn` to the general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique`
  (`AOP/A6_GenFold.lean`) PRODUCES the dedup fold as `cataR (consScalarAlg g st)` — the
  two-element lookahead is emitted by the law, never written by hand.  The bridge `foldFn_ofList`
  (`foldFn (CL.ofList xs) = dedupFn xs`) needs one small fact NOT implied by `consFold_unique`
  itself: `dedupFn_head_eq`, "`dedupFn` preserves the head of a nonempty list" — it is what lets
  `acc.head?` (the folded tail's own head) stand in for the raw lookahead `y`. This fact is
  UNCONDITIONAL (no sortedness hypothesis): `dedupFn` only ever drops an element identical to its
  successor, so a nonempty input's head survives verbatim.

  Only the DATA is reshaped; `LC26.dedup_correct` (membership / sortedness / no-duplicates, which
  DOES need sortedness) is REUSED from `L26.lean`, not re-proved.  Uses the SHARED
  `Freyd.Alg.RelSet.CL.ofList` (`AOP/A6_ConsList.lean`), not a local redefinition.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L26

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC26D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list carrier and its lookahead-carrying fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here `C = List Int` —
  the deduped SUFFIX itself.  Consing `x` onto it compares `x` against the suffix's own head, which
  is exactly the next distinct element `y` `dedupFn` would peek at. -/

/-- The base of the emergent algebra: the empty suffix dedups to the empty list. -/
def g : Unit → List Int := fun _ => []

/-- The step of the emergent algebra: compare the new element `x` against the folded tail's own
    head.  Equal to it (the tail's first surviving value) ⇒ drop `x`; otherwise cons it on. -/
def st : Int → List Int → List Int :=
  fun x acc => match acc.head? with
    | some h => if x = h then acc else x :: acc
    | none   => x :: acc

/-- The dedup fold as a fold over the cons-list initial algebra, mirroring `LC26.dedupFn`:
    `wrap _ ↦ []`, `cons x xs ↦ st x (foldFn xs)`. -/
def foldFn : ConsList Unit Int → List Int
  | ConsList.wrap _    => g ()
  | ConsList.cons x xs => st x (foldFn xs)

/-- The base condition is a COMPUTATION, not a guess: `foldFn (wrap d) = g d`. -/
theorem foldFn_wrap : ∀ d : Unit, foldFn (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `foldFn`'s cons equation: `foldFn (cons x xs) = st x (foldFn xs)`. -/
theorem foldFn_cons :
    ∀ (x : Int) (xs : ConsList Unit Int), foldFn (ConsList.cons x xs) = st x (foldFn xs) :=
  fun _ _ => rfl

/-! ## The dedup fold EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The dedup fold, RESHAPED onto the cons-list initial algebra `ConsList Unit
    Int`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g st` — it was never
    written as a fold: `graph foldFn` equals `cataR (consScalarAlg g st)`.  Reading the lookahead off
    the folded tail's own head (instead of tupling a separate lookahead component) is the point: a
    two-element-lookahead adjacent-dedup scan is emitted by `consFold_unique`. -/
theorem dedup_emerges :
    (graph foldFn : dCL Unit Int ⟶ ⟨List Int⟩) = cataR (consScalarAlg g st) :=
  consFold_unique g st foldFn foldFn_wrap foldFn_cons

/-! ## The small lemma the bridge needs: `dedupFn` preserves the head of a nonempty list

  Unconditional (no sortedness): `dedupFn` only ever collapses an element into an EQUAL successor, so
  the first element of a nonempty list survives to be the first element of the output, verbatim. -/

theorem dedupFn_head_eq : ∀ l : List Int, l ≠ [] → (LC26.dedupFn l).head? = l.head?
  | [], h => absurd rfl h
  | [_], _ => rfl
  | x :: y :: rest, _ => by
      by_cases hxy : x = y
      · rw [LC26.dedupFn_cons_cons, if_pos hxy, dedupFn_head_eq (y :: rest) (List.cons_ne_nil y rest)]
        simp [hxy]
      · rw [LC26.dedupFn_cons_cons, if_neg hxy]
        rfl

/-! ## Bridge to the hand-written raw-`List` solution -/

/-- The reshaped fold agrees with the raw-`List` fold on converted input: `foldFn (ofList xs) =
    dedupFn xs`, by the same two-element induction as `dedupFn`.  In the `x :: y :: rest` case, the
    folded tail's head `(dedupFn (y :: rest)).head?` is identified with `(y :: rest).head? = some y`
    by `dedupFn_head_eq`, turning `st x (foldFn (ofList (y :: rest)))` into `dedupFn`'s own
    `if x = y then … else x :: …`. -/
theorem foldFn_ofList : ∀ xs : List Int, foldFn (CL.ofList xs) = LC26.dedupFn xs
  | []          => rfl
  | [_]         => rfl
  | x :: y :: r => by
      show st x (foldFn (CL.ofList (y :: r))) = LC26.dedupFn (x :: y :: r)
      rw [foldFn_ofList (y :: r), LC26.dedupFn_cons_cons]
      show (match (LC26.dedupFn (y :: r)).head? with
            | some h => if x = h then LC26.dedupFn (y :: r) else x :: LC26.dedupFn (y :: r)
            | none => x :: LC26.dedupFn (y :: r))
          = if x = y then LC26.dedupFn (y :: r) else x :: LC26.dedupFn (y :: r)
      rw [dedupFn_head_eq (y :: r) (List.cons_ne_nil y r)]
      rfl

/-! ## Correctness carries over from `L26.lean` (no re-proof) -/

/-- **Headline.**  The honest bundle for the STRUCTURAL-OUTPUT case:

    (1) adjacent dedup, reshaped onto the cons-list initial algebra with the SUFFIX-as-lookahead
        carrier, IS the catamorphism of `consScalarAlg g st` — the two-element-lookahead scan
        EMERGES from `consFold_unique` (`dedup_emerges`);
    (2) on a SORTED input `xs`, the emergent catamorphism run on the converted input
        (`foldFn (CL.ofList xs)`) preserves membership, stays sorted, and has no duplicates — the
        REUSED three-clause `LC26.dedup_correct`, not re-proved here.

    The program (the fold) is PRODUCED by the law; the correctness is reused. -/
theorem dedup_derived_correct {xs : List Int} (hs : LC242.Sorted xs) :
    ((graph foldFn : dCL Unit Int ⟶ ⟨List Int⟩) = cataR (consScalarAlg g st))
      ∧ (∀ v, v ∈ foldFn (CL.ofList xs) ↔ v ∈ xs)
      ∧ LC242.Sorted (foldFn (CL.ofList xs))
      ∧ (foldFn (CL.ofList xs)).Nodup := by
  obtain ⟨h1, h2, h3⟩ := LC26.dedup_correct hs
  refine ⟨dedup_emerges, ?_, ?_, ?_⟩
  · rw [foldFn_ofList xs]; exact h1
  · rw [foldFn_ofList xs]; exact h2
  · rw [foldFn_ofList xs]; exact h3

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons`
  case is an existential over the carrier), so we `decide` the computable witness
  `foldFn ∘ CL.ofList`. -/

/-- `[1,1,2] → [1,2]`. -/
example : foldFn (CL.ofList [1, 1, 2]) = [1, 2] := by decide
/-- `[0,0,1,1,1,2,2] → [0,1,2]`. -/
example : foldFn (CL.ofList [0, 0, 1, 1, 1, 2, 2]) = [0, 1, 2] := by decide
/-- `[] → []`. -/
example : foldFn (CL.ofList []) = [] := by decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g st) (CL.ofList [1, 1, 2]) (foldFn (CL.ofList [1, 1, 2])) := by
  have h : (graph foldFn : dCL Unit Int ⟶ ⟨List Int⟩)
      (CL.ofList [1, 1, 2]) (foldFn (CL.ofList [1, 1, 2])) := rfl
  rw [dedup_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC26D
