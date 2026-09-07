/-
  LeetCode 19 — Remove Nth Node From End of List — DERIVED as a cons-list catamorphism.

  `leet/L19.lean` WRITES `removeNthFn` by RANDOM ACCESS on a raw Lean `List Int`:

    * `removeNthFn xs n = xs.take (xs.length - n) ++ xs.drop (xs.length - n + 1)`

  — it computes the 0-indexed cut point `k := xs.length - n` (the `n`-th node from the end) and splices
  around it with `take`/`drop`/`length`.  As written this is not a catamorphism: it needs the total length
  up front and indexes into the middle, neither of which a single cons-fold `st : E → C → C` (head, then
  folded tail) can do.

  This file RESHAPES the data onto the canonical cons-list initial algebra `ConsList Unit Int`
  (`list Int` of the book, base `wrap ()`, recursion on the tail) and DEFEATS the random access with the
  carrier

    * `C := Nat × List Int` — `(number of elements in the folded suffix, that suffix with its own n-th-from-
       -the-end node already removed)` —

  so a plain right-fold reproduces "remove the n-th from the end" in ONE pass: the counter reports how far
  the current head is FROM THE END, and the node is dropped exactly when that distance hits `n`.  Base/step
  are ordinary and FORCED (both `rfl`):

    * base `g _ = (0, [])`                                            = `removeCL n (wrap _)`
    * step `st n x (c, s) = (c+1, if c+1 = n then s else x :: s)`     = `removeCL n (cons x xs)`
                                                                         with `(c, s) = removeCL n xs`.

  Feeding `g`/`st n`/`removeCL n` to the general-carrier law `Freyd.Alg.RelSet.CL.consFold_unique`
  (`AOP/A6_GenFold.lean`) PRODUCES the removal fold as `cataR (consScalarAlg g (st n))` — the from-the-end
  counting scan is EMITTED by the law, never written as a fold by hand (`remove_emerges`).

  The bridge `removeCL_ofList` recovers the hand-written random-access program on converted input:
  `removeCL n (ofList ys) = (ys.length, if n ≤ ys.length then removeNthFn ys n else ys)`.  The `if` is
  honest: the raw `removeNthFn` TRUNCATES `xs.length - n` in `ℕ`, so for the out-of-range `n > length` it
  spuriously drops the HEAD, whereas the fold (nothing counts up to `n`) keeps the whole suffix — the two
  coincide exactly on the specified range `n ≤ xs.length`, which is all `L19`'s spec ever asserts.

  Only the DATA is reshaped; the three-part correctness `LC19.removeNth_correct` / refinement
  `LC19.solve ⊑ LC19.spec` and the `Map` `LC19.solve` are REUSED from `L19.lean`, not re-proved.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L19

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC19D

open Freyd Freyd.Alg.RelSet.CL

/-! ## The cons-list carrier and its from-the-end-counting fold

  The general-carrier law `CL.consFold_unique` carries an arbitrary type `C`; here
  `C = Nat × List Int` — `(length of the folded suffix, that suffix with its n-th-from-the-end node
  removed)`.  The counter in the FIRST component is what lets an ordinary cons-fold see "distance from the
  end": when `cons x` sees the folded tail `(c, s)`, its own distance from the end is `c + 1`, and the node
  is dropped precisely when `c + 1 = n`. -/

/-- The base of the emergent algebra: the empty suffix has length `0` and empty output. -/
def g : Unit → Nat × List Int := fun _ => (0, [])

/-- The step of the emergent algebra: prepend head `x` to the folded tail `(c, s)`.  The new suffix length
    is `c + 1`; if that equals `n`, THIS head is the `n`-th from the end, so it is dropped (`s` kept);
    otherwise it survives (`x :: s`). -/
def st (n : Nat) : Int → Nat × List Int → Nat × List Int :=
  fun x p => (p.1 + 1, if p.1 + 1 = n then p.2 else x :: p.2)

/-- The removal fold as a fold over the cons-list initial algebra, mirroring `LC19.removeNthFn`:
    `wrap _ ↦ (0, [])`, `cons x xs ↦ st n x (removeCL n xs)`. -/
def removeCL (n : Nat) : ConsList Unit Int → Nat × List Int
  | ConsList.wrap _    => (0, [])
  | ConsList.cons x xs => st n x (removeCL n xs)

/-- The base condition is a COMPUTATION, not a guess: `removeCL n (wrap d) = g d`. -/
theorem removeCL_wrap (n : Nat) : ∀ d : Unit, removeCL n (ConsList.wrap d) = g d := fun _ => rfl

/-- The step condition IS `removeCL`'s cons equation: `removeCL n (cons x xs) = st n x (removeCL n xs)`. -/
theorem removeCL_cons (n : Nat) :
    ∀ (x : Int) (xs : ConsList Unit Int),
      removeCL n (ConsList.cons x xs) = st n x (removeCL n xs) :=
  fun _ _ => rfl

/-! ## The removal fold EMERGES via the general-carrier cons-fold law -/

/-- **The derivation.**  The removal fold, RESHAPED onto the cons-list initial algebra `ConsList Unit
    Int`, IS the catamorphism of the emergent scalar algebra `consScalarAlg g (st n)` — it was never
    written as a fold: `graph (removeCL n)` equals `cataR (consScalarAlg g (st n))`.  Counting distance
    from the end in the carrier `Nat × List Int` is the point: a "remove n-th from the end" scan is emitted
    by `consFold_unique`, with no length pass and no indexing. -/
theorem remove_emerges (n : Nat) :
    (graph (removeCL n) : dCL Unit Int ⟶ ⟨Nat × List Int⟩) = cataR (consScalarAlg g (st n)) :=
  consFold_unique g (st n) (removeCL n) (removeCL_wrap n) (removeCL_cons n)

/-! ## Bridge to the hand-written random-access solution -/

/-- The `List Int → ConsList Unit Int` conversion onto the initial algebra: `[] ↦ wrap ()`,
    `x :: xs ↦ cons x (ofList xs)`. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-! ### The three cons-reductions of the random-access `removeNthFn`

  These re-express `LC19.removeNthFn (x :: ys) n` (a `take`/`drop`/`length` expression) in terms of the
  tail, splitting on where the cut point `xs.length - n` lands.  They are the raw-list facts the induction
  needs; `omega` moves the `ℕ`-subtraction under `take`/`drop`. -/

/-- Cut strictly inside the tail (`n ≤ ys.length`): the head survives and removal recurses. -/
theorem removeNthFn_cons_le (x : Int) (ys : List Int) (n : Nat) (h : n ≤ ys.length) :
    LC19.removeNthFn (x :: ys) n = x :: LC19.removeNthFn ys n := by
  unfold LC19.removeNthFn
  rw [List.length_cons]
  have e1 : ys.length + 1 - n = (ys.length - n) + 1 := by omega
  rw [e1, List.take_succ_cons, List.drop_succ_cons, List.cons_append]

/-- Cut at the head (`n = ys.length + 1`, i.e. the head IS the `n`-th from the end): drop it. -/
theorem removeNthFn_cons_head (x : Int) (ys : List Int) (n : Nat) (h : n = ys.length + 1) :
    LC19.removeNthFn (x :: ys) n = ys := by
  unfold LC19.removeNthFn
  rw [List.length_cons]
  subst h
  have e1 : ys.length + 1 - (ys.length + 1) = 0 := by omega
  rw [e1, List.take_zero, List.nil_append, List.drop_succ_cons, List.drop_zero]

/-- `removeNthFn [] n = []`. -/
theorem removeNthFn_nil (n : Nat) : LC19.removeNthFn [] n = [] := by
  unfold LC19.removeNthFn; rw [List.take_nil, List.drop_nil]; rfl

/-- **The bridge.**  On converted input the reshaped fold computes the pair
    `(length, remove-the-n-th-from-the-end)`, matching the raw `removeNthFn` on the specified range and
    (honestly) keeping the whole list when `n` is out of range.  Proved by the same list induction as the
    fold, splitting the head step on where `n` sits relative to the tail length. -/
theorem removeCL_ofList (n : Nat) : ∀ ys : List Int,
    removeCL n (ofList ys) = (ys.length, if n ≤ ys.length then LC19.removeNthFn ys n else ys)
  | [] => by
      show removeCL n (ConsList.wrap ()) = _
      rw [removeCL, removeNthFn_nil, List.length_nil]
      split <;> rfl
  | x :: ys => by
      show st n x (removeCL n (ofList ys)) = _
      rw [removeCL_ofList n ys, List.length_cons]
      simp only [st]
      rcases Nat.lt_trichotomy n (ys.length + 1) with hlt | heq | hgt
      · -- n ≤ ys.length : head survives, removal recurses
        have hle : n ≤ ys.length := by omega
        rw [if_neg (by omega : ¬ ys.length + 1 = n), if_pos hle,
          if_pos (by omega : n ≤ ys.length + 1), removeNthFn_cons_le x ys n hle]
      · -- n = ys.length + 1 : head dropped
        rw [if_pos (by omega : ys.length + 1 = n), if_neg (by omega : ¬ n ≤ ys.length),
          if_pos (by omega : n ≤ ys.length + 1), removeNthFn_cons_head x ys n heq]
      · -- n > ys.length + 1 : out of range, whole list kept (matches fold, differs from removeNthFn)
        rw [if_neg (by omega : ¬ ys.length + 1 = n), if_neg (by omega : ¬ n ≤ ys.length),
          if_neg (by omega : ¬ n ≤ ys.length + 1)]

/-- The reshaped catamorphism's second component computes exactly `removeNthFn` on the spec range. -/
theorem remove_via (xs : List Int) (n : Nat) (h : n ≤ xs.length) :
    LC19.removeNthFn xs n = (removeCL n (ofList xs)).2 := by
  rw [removeCL_ofList n xs]
  show LC19.removeNthFn xs n = if n ≤ xs.length then LC19.removeNthFn xs n else xs
  rw [if_pos h]

/-! ## Correctness carries over from `L19.lean` (no re-proof of the splice spec) -/

/-- **Headline.**  The honest bundle:

    (1) the removal fold, reshaped onto the cons-list initial algebra, IS the catamorphism of
        `consScalarAlg g (st n)` — the "remove n-th from the end" scan EMERGES from `consFold_unique`
        (`remove_emerges`);
    (2) on the specified range `n ≤ xs.length`, the `Map` `LC19.solve` (LeetCode 19's answer relation)
        relates each input `(xs, n)` to exactly the SECOND component of that emergent catamorphism on the
        converted input (`remove_via`); and
    (3) that output satisfies the three-part splice specification — the REUSED `LC19.solve_le_spec`
        (`solve ⊑ spec`: length drops by one, earlier positions unchanged, later positions shift left by
        one), not re-proved here.

    The program (the fold) is PRODUCED by the law; the splice correctness is reused. -/
theorem removeNth_derived_correct :
    (∀ n : Nat,
      (graph (removeCL n) : dCL Unit Int ⟶ ⟨Nat × List Int⟩) = cataR (consScalarAlg g (st n)))
    ∧ (∀ (xs : List Int) (n : Nat) (out : List Int), n ≤ xs.length →
        (LC19.solve (xs, n) out ↔ out = (removeCL n (ofList xs)).2))
    ∧ (LC19.solve ⊑ LC19.spec) := by
  refine ⟨remove_emerges, ?_, LC19.solve_le_spec⟩
  intro xs n out h
  show (out = LC19.removeNthFn xs n) ↔ out = (removeCL n (ofList xs)).2
  rw [remove_via xs n h]

/-! ## Running / cross-checking the reshaped fold

  The relational catamorphism `cataFold (consScalarAlg …)` is not `decide`-computable (its `cons` case is
  an existential over the carrier), so we `decide` the computable scalar answers `removeNthFn` (LeetCode 19
  examples) and the extensionally-equal computable witness `(removeCL n ∘ ofList).2`. -/

/-- `[1,2,3,4,5]`, remove 2nd from end (the `4`) → `[1,2,3,5]`. -/
example : LC19.removeNthFn [1, 2, 3, 4, 5] 2 = [1, 2, 3, 5] := by decide
/-- `[1]`, remove 1st from end → `[]`. -/
example : LC19.removeNthFn [1] 1 = [] := by decide
/-- `[1,2]`, remove 2nd from end (the head `1`) → `[2]`. -/
example : LC19.removeNthFn [1, 2] 2 = [2] := by decide

-- The reshaped cons-list fold, on converted input, reproduces the scalar answers:
example : (removeCL 2 (ofList [1, 2, 3, 4, 5])).2 = [1, 2, 3, 5] := by decide
example : (removeCL 1 (ofList [1])).2 = [] := by decide
example : (removeCL 2 (ofList [1, 2])).2 = [2] := by decide

/-- The reshaped fold genuinely relates the converted input to the catamorphism it emerges as. -/
example :
    cataFold (consScalarAlg g (st 2)) (ofList [1, 2, 3, 4, 5])
      (removeCL 2 (ofList [1, 2, 3, 4, 5])) := by
  have h : (graph (removeCL 2) : dCL Unit Int ⟶ ⟨Nat × List Int⟩)
      (ofList [1, 2, 3, 4, 5]) (removeCL 2 (ofList [1, 2, 3, 4, 5])) := rfl
  rw [remove_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC19D
