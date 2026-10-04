/-
  LeetCode 217 — Contains Duplicate — DERIVED, with an O(n)-EXPECTED hash-set carrier.

  `leet/L217.lean` writes two mutually-referencing folds by hand: `memB xs p` ("does `p` occur in
  the prefix `xs`?") and `hasDup xs` ("does `xs` repeat a value?").  The `snoc` step of `hasDup`
  reads `memB xs q` — the WHOLE prefix's membership tester — so its running cost is `O(n)` per step,
  `O(n²)` overall.  The first derivation (`git` history) fixed the SECOND-order recurrence by tupling
  the membership tester `memB xs : ℤ → Bool` with the flag; but a FUNCTION-valued membership tester
  is still `O(n)` to consult, so that carrier is `O(n²)` too.

  This rewrite replaces the `ℤ → Bool` membership FUNCTION by a hash SET (`Freyd.HashMap.AHashSet`,
  chaining over an `Array` of buckets, mathlib-free).  Carrier `C := AHashSet × Bool` — the pair
  `(seen-set, duplicate-found)`.  A single fold over the array threads it: at `x`, if `mem s x` the
  set already contains `x` (a duplicate — record it in the flag, no re-insert), else `insert' s x`.
  Each step is ONE `mem` + at most one `insert'`, both `O(1)` EXPECTED for a chaining hash set (the
  honest bound — worst case `O(n)` on total collision; see `A6_HashMap`'s docstring), so the whole
  fold is `O(n)` expected instead of `O(n²)`.

    * the carrier is `AHashSet × Bool`, the base `g x` seeds the singleton set `{x}` with flag
      `false`, and the step branches on `mem s x` (`step` below).  All standalone, read off the
      recurrence, FORCED not guessed;
    * `SL.snocFold_unique g step hashPair hashPair_wrap hashPair_snoc` PRODUCES the state fold
      `cataR (scalarAlg g step)` and identifies it with `graph hashPair` (`dup_emerges`) — the
      hash-set-carrying single-pass scan is not written, it emerges.

  CORRECTNESS is REUSED, not re-proved.  The invariant `inv` shows, by induction with the hash-set
  lemmas `mem_mk`/`mem_insert_self`/`mem_insert_other`, that after any prefix `xs` the seen-set
  `mem`-models `L217`'s membership tester exactly (`mem (hashPair xs).1 p = memB xs p`) and the flag
  equals `hasDup xs`.  The DECISION `L217.solve_correct : solveFn xs = true ↔ dupP xs` (an `iff`, NOT
  re-proved) is then transported onto the emergent fold in the bundled headline `dup_derived_correct`.

  Same drop-in object `Arr ⟶ dBool` and headline shape as before, now on the hash carrier.

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route only through `snocFold_unique`
  (a plain uniqueness induction), never `cataR_eq_relCata` (which pulls `Classical.choice`); the hash
  lemmas use `beq_iff_eq.mpr rfl`, not `beq_self_eq_true`, to stay off `Classical.choice`.
-/
import AOP.A6_GenFold
import AOP.A6_HashMap
import leet.L217

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC217D

open Freyd Freyd.HashMap Freyd.Alg.RelSet.SL Freyd.Alg.RelSet.LC217

/-! ## The hash-set carrier and its FORCED base/step

  Carrier `C := AHashSet × Bool` — the pair `(seen-set, duplicate-found)`.  The membership FUNCTION
  `memB xs : ℤ → Bool` of the old carrier is replaced by a hash set that `mem`-models it in `O(1)`
  expected. -/

/-- The base of the emergent algebra, forced by `hashPair (wrap x) = ({x}, false)`: a one-element
    array seeds the singleton seen-set and has no duplicate.  16 buckets is an arbitrary fixed
    constant — the bucket count is fixed at construction (no resize), the honest chaining-hash
    caveat; correctness holds for any count (`mem_mk`). -/
def g : Int → AHashSet × Bool := fun x => (insert' (mkHashMap Unit 15) x, false)

/-- The step of the emergent algebra: consult the seen-set once.  If `x` is already present the
    array repeats a value — set the flag, keep the set (no need to re-insert `x`); otherwise add `x`
    to the seen-set, flag unchanged.  One `mem` + at most one `insert'`, `O(1)` expected. -/
def step (st : AHashSet × Bool) (x : Int) : AHashSet × Bool :=
  bif HashMap.mem st.1 x then (st.1, true) else (insert' st.1 x, st.2)

/-- The hash-set-carrying fold, written as its two defining equations (so `hashPair_wrap`/
    `hashPair_snoc` are `rfl` and `SL.snocFold_unique` applies). -/
def hashPair : SnocList Int Int → AHashSet × Bool
  | SnocList.wrap x   => g x
  | SnocList.snoc xs x => step (hashPair xs) x

theorem hashPair_wrap (x : Int) : hashPair (SnocList.wrap x) = g x := rfl

theorem hashPair_snoc (xs : SnocList Int Int) (x : Int) :
    hashPair (SnocList.snoc xs x) = step (hashPair xs) x := rfl

/-- `step` reduced on the "already seen" branch. -/
theorem step_pos (st : AHashSet × Bool) (x : Int) (h : HashMap.mem st.1 x = true) :
    step st x = (st.1, true) := by
  simp only [step, h, cond_true]

/-- `step` reduced on the "new element" branch. -/
theorem step_neg (st : AHashSet × Bool) (x : Int) (h : HashMap.mem st.1 x = false) :
    step st x = (insert' st.1 x, st.2) := by
  simp only [step, h, cond_false]

/-! ## The seen-set `mem`-models `L217`'s membership tester -/

/-- Inserting `q` extends the set's membership by "equals `q`": `mem (insert' s q) p` is
    `mem s p || eqi p q`.  Proved from `mem_insert_self`/`mem_insert_other` by casing on `eqi p q`
    (which reflects `p = q` via `L217.eqi_eq_true`). -/
theorem mem_insert_eq (s : AHashSet) (q p : Int) :
    HashMap.mem (insert' s q) p = (HashMap.mem s p || eqi p q) := by
  cases hpq : eqi p q with
  | true =>
      have hp : p = q := eqi_eq_true.mp hpq
      subst hp
      rw [mem_insert_self, Bool.or_true]
  | false =>
      have hne : p ≠ q := by
        intro hp; rw [eqi_eq_true.mpr hp] at hpq; exact absurd hpq (by decide)
      rw [mem_insert_other s q p hne, Bool.or_false]

/-! ## The invariant: the seen-set models `memB`, the flag equals `hasDup` -/

/-- **The correctness invariant.**  After folding any prefix `xs`, the seen-set membership `mem`
    agrees with `L217`'s `memB xs` pointwise, and the flag equals `L217`'s `hasDup xs`.  Proved by
    induction on the array using the hash-set lemmas; the flag component mirrors `L217`'s own
    `hasDup (snoc xs x) = hasDup xs || memB xs x` recurrence. -/
theorem inv : ∀ xs : SnocList Int Int,
    (∀ p, HashMap.mem (hashPair xs).1 p = memB xs p) ∧ (hashPair xs).2 = hasDup xs := by
  intro xs
  induction xs with
  | wrap x =>
      refine ⟨?_, rfl⟩
      intro p
      show HashMap.mem (insert' (mkHashMap Unit 15) x) p = eqi p x
      rw [mem_insert_eq (mkHashMap Unit 15) x p, mem_mk, Bool.false_or]
  | snoc xs x ih =>
      obtain ⟨ih1, ih2⟩ := ih
      cases hc : HashMap.mem (hashPair xs).1 x with
      | true =>
          have hmx : memB xs x = true := (ih1 x).symm.trans hc
          constructor
          · intro p
            rw [hashPair_snoc, step_pos _ _ hc]
            show HashMap.mem (hashPair xs).1 p = (memB xs p || eqi p x)
            rw [ih1 p]
            cases hpx : eqi p x with
            | true  => have hp : p = x := eqi_eq_true.mp hpx; subst hp; rw [Bool.or_true]; exact hmx
            | false => rw [Bool.or_false]
          · rw [hashPair_snoc, step_pos _ _ hc]
            show true = (hasDup xs || memB xs x)
            rw [hmx, Bool.or_true]
      | false =>
          have hmx : memB xs x = false := (ih1 x).symm.trans hc
          constructor
          · intro p
            rw [hashPair_snoc, step_neg _ _ hc]
            show HashMap.mem (insert' (hashPair xs).1 x) p = (memB xs p || eqi p x)
            rw [mem_insert_eq (hashPair xs).1 x p, ih1 p]
          · rw [hashPair_snoc, step_neg _ _ hc]
            show (hashPair xs).2 = (hasDup xs || memB xs x)
            rw [ih2, hmx, Bool.or_false]

/-! ## The state fold EMERGES via the general snoc-fold law -/

/-- **The hash-set fold EMERGES.**  `graph hashPair` equals the catamorphism of the emergent scalar
    algebra `scalarAlg g step` — PRODUCED by `SL.snocFold_unique` from the forced base `g` and step
    `step`, never written by hand.  The seen-set-carrying single-pass `O(n)`-expected scan is now one
    catamorphism over `F X = ℤ + X × ℤ` on the carrier `AHashSet × Bool`. -/
theorem dup_emerges :
    (graph hashPair : Arr ⟶ (⟨AHashSet × Bool⟩ : RelSet.{0})) = cataR (scalarAlg g step) :=
  snocFold_unique g step hashPair hashPair_wrap hashPair_snoc

/-! ## Connecting the emergent fold back to `L217.solve` -/

/-- The derived solver: the emergent hash-set fold followed by `Prod.snd`, projecting the answer flag
    out of the carried state `(seen-set, hasDup)`. -/
def derivedSolve : Arr ⟶ dBool :=
  cataR (scalarAlg g step) ≫ graph (Prod.snd : AHashSet × Bool → Bool)

/-- The derived solver IS `L217.solve`.  Replacing the emergent catamorphism by `graph hashPair`
    (`dup_emerges`) and projecting the second component gives `graph (fun xs => (hashPair xs).2) =
    graph hasDup = graph solveFn = solve` (`(hashPair xs).2 = hasDup xs = solveFn xs` by `inv`). -/
theorem derivedSolve_eq_solve : derivedSolve = LC217.solve := by
  unfold derivedSolve
  rw [← dup_emerges]
  apply hom_ext; intro xs b
  constructor
  · rintro ⟨v, hv, hb⟩
    show b = LC217.solveFn xs
    rw [hb, hv]
    exact (inv xs).2
  · intro hb
    have hb' : b = hasDup xs := hb
    exact ⟨hashPair xs, rfl, hb'.trans (inv xs).2.symm⟩

/-! ## Correctness of the derived program, transported from `L217.solve_correct` -/

/-- **The Contains-Duplicate program is the hash-set-carrying catamorphism, and it is correct.**  The
    honest headline bundles:

    * `dup_emerges` — `graph hashPair = cataR (scalarAlg g step)`: the seen-set-carrying `O(n)`-expected
      program IS the catamorphism over the carrier `AHashSet × Bool`; and
    * the transported correctness — for ANY state `v` the emergent fold relates the array `xs` to, its
      answer flag `v.2` decides the duplicate question, `v.2 = true ↔ dupP xs`.  Emergence pins
      `v = hashPair xs`, the invariant `inv` supplies `(hashPair xs).2 = hasDup xs`, and
      `L217.solve_correct` (the existing decision `Iff`, NOT re-proved here) finishes. -/
theorem dup_derived_correct :
    ((graph hashPair : Arr ⟶ (⟨AHashSet × Bool⟩ : RelSet.{0})) = cataR (scalarAlg g step)) ∧
    (∀ (xs : SnocList Int Int) (v : AHashSet × Bool),
        cataFold (scalarAlg g step) xs v → (v.2 = true ↔ dupP xs)) := by
  refine ⟨dup_emerges, ?_⟩
  intro xs v hv
  have hgr : (graph hashPair : Arr ⟶ (⟨AHashSet × Bool⟩ : RelSet.{0})) xs v := by
    rw [dup_emerges]; exact hv
  have hveq : v = hashPair xs := hgr
  subst hveq
  rw [(inv xs).2]
  exact LC217.solve_correct xs

/-! ## Running / cross-checking the emergent hash fold against `leet/L217.lean`

  The answer flag `(hashPair xs).2` is a `Bool`; via `inv` it equals `L217.hasDup xs`, so the proof
  examples reduce to `L217`'s own decidable checks (no `decide` on the `Array`-backed set).  The
  `#eval`s below run the genuine hash program end-to-end through the compiler. -/

example : (hashPair (LC217.ofList 1 [2, 3, 1])).2 = true := by
  rw [(inv (LC217.ofList 1 [2, 3, 1])).2]; decide
example : (hashPair (LC217.ofList 1 [2, 3, 4])).2 = false := by
  rw [(inv (LC217.ofList 1 [2, 3, 4])).2]; decide
example : (hashPair (LC217.ofList 1 [1])).2 = true := by
  rw [(inv (LC217.ofList 1 [1])).2]; decide

-- The genuine hash-set program run through the compiler (Array-backed, no axioms):
#eval (hashPair (LC217.ofList 1 [2, 3, 1])).2   -- true
#eval (hashPair (LC217.ofList 1 [2, 3, 4])).2   -- false
#eval (hashPair (LC217.ofList 1 [1])).2         -- true

end Freyd.Alg.RelSet.LC217D
