/-
  LeetCode 128 — Longest Consecutive Sequence — DERIVED, now in **O(n) expected** via a hash set.

  `leet/L128.lean` computes the answer by SORTING (`L242.isort`, O(n²) insertion sort) and then a
  left-to-right run-tracking scan.  This file replaces the sort by the standard hash-set algorithm,
  which is O(n) EXPECTED (the hash map's `find?`/`insert` are O(1) expected — see `A6_HashMap.lean`;
  the bound is informal, not proven in Lean):

    * **Phase 1** — fold `nums` into an `AHashSet` of all its elements (`build`, an `n`-step fold, each
      step an expected-O(1) `insert'`).  This fold is PRODUCED by the general cons-list fold-uniqueness
      law `CL.consFold_unique` (`setBuild_emerges`): the set-builder is the catamorphism of the scalar
      algebra with base `s0` and step `insert'` — the recursion is never hand-written.
    * **Phase 2** — for each element `x` that is a RUN START (`mem s (x-1) = false`), count the run
      `x, x+1, x+2, …` (`runFrom`, fuel-bounded by `nums.length`) and take the max (`LC128.nmax`).
      Each element is the interior of at most one run, so across all starts the run-counters touch each
      element O(1) times: O(n) expected total.  Phase 2 is a `foldl` max over run-lengths, NOT a
      catamorphism (it re-reads `nums` against the built set), so the whole program is `graph hashLongest`,
      not a single `cataR` — only Phase 1 emerges as a fold.

  **Correctness is proved directly against `L128`'s membership spec** (the two-phase structure does not
  map onto the sorted-scan invariant, so we do not reuse `LC128.scanAux_inv`).  The key facts, all
  axiom-clean:
    * `mem_build` — after Phase 1, `mem (build nums) x ↔ x ∈ nums` (the hash-set membership bridge).
    * `pigeon` — a length-`ℓ` block of consecutive integers all present in `nums` forces `ℓ ≤ nums.length`
      (finiteness, via a constructive one-element removal `rm`; this is what makes `fuel = nums.length`
      large enough for every run that can occur).
    * `runFrom_mem` / `runFrom_ge` — the run-counter's members are in the set, and a block of length `k`
      with `fuel ≥ k` is counted to length `≥ k`.
    * `runStart_P1` / `runStart_P2` + `run_start_exists` — a bounded backward walk locates, for any `s ∈ S`,
      the genuine run-start `t ≤ s` of the run through `s` (fuel exhaustion is ruled out by `pigeon`).
    * `hash_ach` / `hash_dom` — `hashLongest nums` achieves a value-run of its own length and dominates
      every value-run present in `nums` (the `Freyd/leetcode.md` S0 refinement + domination pair).
  `hashLongest = LC128.longestConsecFn` then follows by antisymmetry (`derivedSolve_eq_solve`), so the
  derived O(n) program is the SAME relation as `LC128.solve`, and the headline reuses the packaging.

  Mathlib-free (imports `AOP.A6_HashMap`).  Headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenFold
import leet.L128
import AOP.A6_HashMap

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC128D

open Freyd Freyd.HashMap Freyd.Alg.RelSet.CL

/-! ## Finiteness: a block of consecutive integers all in a list is no longer than the list

  Constructive first-occurrence removal `rm` (Lean core's `List.erase` lemmas pull `Classical.choice`,
  so we roll our own), then a clean induction on the block length. -/

/-- Remove the first occurrence of `a` from a list (constructive; `Int` has decidable equality). -/
def rm (a : Int) : List Int → List Int
  | [] => []
  | x :: xs => if x = a then xs else x :: rm a xs

theorem rm_len {a : Int} : ∀ {l : List Int}, a ∈ l → (rm a l).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (List.not_mem_nil)
  | cons x xs ih =>
    intro h
    by_cases hx : x = a
    · simp [rm, hx]
    · have hmem : a ∈ xs := by
        rcases List.mem_cons.mp h with he | he
        · exact absurd he.symm hx
        · exact he
      simp only [rm, if_neg hx, List.length_cons]
      rw [ih hmem]

theorem mem_rm {a b : Int} (hba : b ≠ a) : ∀ {l : List Int}, (b ∈ rm a l ↔ b ∈ l) := by
  intro l
  induction l with
  | nil => simp [rm]
  | cons x xs ih =>
    by_cases hx : x = a
    · subst hx
      simp only [rm]
      exact ⟨fun h => List.mem_cons_of_mem _ h,
             fun h => (List.mem_cons.mp h).elim (fun he => absurd he hba) id⟩
    · simp only [rm, if_neg hx]
      rw [List.mem_cons, List.mem_cons, ih]

/-- **Pigeonhole for consecutive integers.**  If `t, t+1, …, t+ℓ-1` are all in `nums`, then
    `ℓ ≤ nums.length` (they are `ℓ` distinct elements of `nums`). -/
theorem pigeon : ∀ (nums : List Int) (t : Int) (ℓ : Nat),
    (∀ i : Nat, i < ℓ → t + (i : Int) ∈ nums) → ℓ ≤ nums.length := by
  intro nums t ℓ
  induction ℓ generalizing nums t with
  | zero => intro _; exact Nat.zero_le _
  | succ ℓ' ih =>
    intro h
    have ht : t ∈ nums := by have := h 0 (by omega); simpa using this
    have hlen := rm_len (a := t) ht
    have hrec : ∀ i : Nat, i < ℓ' → (t + 1) + (i : Int) ∈ rm t nums := by
      intro i hi
      have hmem : t + ((i + 1 : Nat) : Int) ∈ nums := h (i + 1) (by omega)
      have hne : t + ((i + 1 : Nat) : Int) ≠ t := by omega
      have hin := (mem_rm hne (l := nums)).mpr hmem
      have heq : t + ((i + 1 : Nat) : Int) = (t + 1) + (i : Int) := by omega
      rwa [heq] at hin
    have := ih (rm t nums) (t + 1) hrec
    omega

/-! ## Phase 1: build the hash set (a cons-list fold that EMERGES from `CL.consFold_unique`) -/

/-- The cons-list of a raw list (`[] ↦ wrap ()`, `x :: xs ↦ cons x …`), reshaping onto the initial
    algebra so the set-builder can be emitted by the fold law. -/
def ofConsList : List Int → ConsList Unit Int
  | [] => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofConsList xs)

/-- Base of the set-building algebra: the empty leaf folds to the seed set `s0`. -/
def gSet (s0 : AHashSet) : Unit → AHashSet := fun _ => s0
/-- Step of the set-building algebra: insert the head element into the folded tail's set. -/
def stSet : Int → AHashSet → AHashSet := fun x s => insert' s x
/-- The set-builder as a cons-list fold, defined FROM `gSet`/`stSet` so `consFold_unique` applies. -/
def foldSet (s0 : AHashSet) : ConsList Unit Int → AHashSet
  | ConsList.wrap _ => s0
  | ConsList.cons x xs => insert' (foldSet s0 xs) x

/-- **The Phase-1 derivation.**  The set-building fold is PRODUCED by the general cons-list
    fold-uniqueness law — never re-written: `graph (foldSet s0)` equals the catamorphism of the
    scalar algebra `consScalarAlg (gSet s0) stSet`, carrier `AHashSet`. -/
theorem setBuild_emerges (s0 : AHashSet) :
    (graph (foldSet s0) : dCL Unit Int ⟶ ⟨AHashSet⟩) = cataR (consScalarAlg (gSet s0) stSet) :=
  CL.consFold_unique (gSet s0) stSet (foldSet s0) (fun _ => rfl) (fun _ _ => rfl)

/-- Phase 1 of the program: the emergent set-builder, seeded with `nums.length + 1` buckets. -/
def build (nums : List Int) : AHashSet := foldSet (mkHashMap Unit nums.length) (ofConsList nums)

/-- `mem (insert' s a) x` is exactly "`x` is `a` or already in `s`". -/
theorem mem_insert' (s : AHashSet) (a x : Int) :
    HashMap.mem (insert' s a) x = true ↔ (x = a ∨ HashMap.mem s x = true) := by
  by_cases hx : x = a
  · subst hx; simp [mem_insert_self]
  · rw [mem_insert_other s a x hx]
    exact ⟨Or.inr, fun h => h.elim (fun he => absurd he hx) id⟩

theorem mem_foldSet (s0 : AHashSet) (x : Int) : ∀ nums : List Int,
    HashMap.mem (foldSet s0 (ofConsList nums)) x = true ↔ (x ∈ nums ∨ HashMap.mem s0 x = true) := by
  intro nums
  induction nums with
  | nil => show HashMap.mem s0 x = true ↔ _; simp
  | cons a rest ih =>
    show HashMap.mem (insert' (foldSet s0 (ofConsList rest)) a) x = true ↔ _
    rw [mem_insert', ih, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- **The Phase-1 membership bridge.**  After building the set, membership is exactly list membership. -/
theorem mem_build (nums : List Int) (x : Int) : HashMap.mem (build nums) x = true ↔ x ∈ nums := by
  rw [show build nums = foldSet (mkHashMap Unit nums.length) (ofConsList nums) from rfl,
      mem_foldSet, mem_mk]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (by decide)
  · intro h; exact Or.inl h

/-! ## Phase 2: count runs from run-starts and take the max -/

/-- Count the consecutive run `x, x+1, x+2, …` present in the set (as a Bool predicate `p`), bounded
    by `fuel`. -/
def runFrom (p : Int → Bool) : Nat → Int → Nat
  | 0, _ => 0
  | F + 1, x => if p x then 1 + runFrom p F (x + 1) else 0

/-- Every counted position is in the set. -/
theorem runFrom_mem (p : Int → Bool) : ∀ (F : Nat) (x : Int) (i : Nat),
    i < runFrom p F x → p (x + (i : Int)) = true := by
  intro F
  induction F with
  | zero => intro x i hi; simp [runFrom] at hi
  | succ F' ih =>
    intro x i hi
    simp only [runFrom] at hi
    by_cases hx : p x = true
    · rw [if_pos hx] at hi
      match i with
      | 0 => simpa using hx
      | j + 1 =>
        have hj := ih (x + 1) j (by omega)
        have heq : (x + 1) + (j : Int) = x + ((j + 1 : Nat) : Int) := by omega
        rwa [heq] at hj
    · rw [if_neg hx] at hi; omega

/-- A block of length `k` all in the set, with enough fuel, is counted to length `≥ k`. -/
theorem runFrom_ge (p : Int → Bool) : ∀ (F k : Nat) (x : Int),
    (∀ j : Nat, j < k → p (x + (j : Int)) = true) → k ≤ F → k ≤ runFrom p F x := by
  intro F
  induction F with
  | zero => intro k x _ hk; omega
  | succ F' ih =>
    intro k x hblock hk
    match k with
    | 0 => omega
    | k' + 1 =>
      have hx : p x = true := by have := hblock 0 (by omega); simpa using this
      simp only [runFrom, if_pos hx]
      have hb : ∀ j : Nat, j < k' → p ((x + 1) + (j : Int)) = true := by
        intro j hj
        have := hblock (j + 1) (by omega)
        have heq : x + ((j + 1 : Nat) : Int) = (x + 1) + (j : Int) := by omega
        rwa [heq] at this
      have := ih k' (x + 1) hb (by omega)
      omega

/-- Walk down from `x` while the predecessor is in the set, at most `fuel` steps: locates the start of
    the run containing `x`. -/
def runStart (p : Int → Bool) : Nat → Int → Int
  | 0, x => x
  | F + 1, x => if p (x - 1) then runStart p F (x - 1) else x

/-- The backward walk lands at `t ≤ x`, keeps `[t, x]` inside the set, and descends at most `F`. -/
theorem runStart_P1 (p : Int → Bool) : ∀ (F : Nat) (x : Int), p x = true →
    (runStart p F x ≤ x) ∧
    (∀ y : Int, runStart p F x ≤ y → y ≤ x → p y = true) ∧
    (x - (F : Int) ≤ runStart p F x) := by
  intro F
  induction F with
  | zero =>
    intro x hx
    simp only [runStart]
    refine ⟨by omega, ?_, by omega⟩
    intro y h1 h2
    have hyx : y = x := by omega
    rwa [hyx]
  | succ F' ih =>
    intro x hx
    by_cases hp : p (x - 1) = true
    · have hunf : runStart p (F' + 1) x = runStart p F' (x - 1) := by
        show (if p (x - 1) = true then runStart p F' (x - 1) else x) = _
        rw [if_pos hp]
      rw [hunf]
      obtain ⟨h1, h2, h3⟩ := ih (x - 1) hp
      refine ⟨by omega, ?_, by omega⟩
      intro y hy1 hy2
      by_cases hyx : y ≤ x - 1
      · exact h2 y hy1 hyx
      · have : y = x := by omega
        rwa [this]
    · have hunf : runStart p (F' + 1) x = x := by
        show (if p (x - 1) = true then runStart p F' (x - 1) else x) = _
        rw [if_neg hp]
      rw [hunf]
      refine ⟨by omega, ?_, by omega⟩
      intro y h1 h2
      have hyx : y = x := by omega
      rwa [hyx]

/-- Either the walk found a genuine run-start (predecessor absent), or it ran the full `F` steps. -/
theorem runStart_P2 (p : Int → Bool) : ∀ (F : Nat) (x : Int), p x = true →
    p (runStart p F x - 1) = false ∨ runStart p F x = x - (F : Int) := by
  intro F
  induction F with
  | zero => intro x hx; right; show x = x - ((0 : Nat) : Int); simp
  | succ F' ih =>
    intro x hx
    by_cases hp : p (x - 1) = true
    · have hunf : runStart p (F' + 1) x = runStart p F' (x - 1) := by
        show (if p (x - 1) = true then runStart p F' (x - 1) else x) = _
        rw [if_pos hp]
      rw [hunf]
      rcases ih (x - 1) hp with h | h
      · left; exact h
      · right; rw [h]; omega
    · have hunf : runStart p (F' + 1) x = x := by
        show (if p (x - 1) = true then runStart p F' (x - 1) else x) = _
        rw [if_neg hp]
      rw [hunf]; left; simpa using hp

/-- **Run-start existence.**  For any `s` in the built set, the run through `s` has a genuine start
    `t ≤ s` (predecessor absent), and everything in `[t, s]` is in the set.  Fuel exhaustion is
    impossible: a full walk would expose `nums.length + 1` consecutive members, contradicting
    `pigeon`. -/
theorem run_start_exists (nums : List Int) (s : Int) (hs : HashMap.mem (build nums) s = true) :
    ∃ t : Int, t ≤ s ∧ HashMap.mem (build nums) (t - 1) = false ∧
      (∀ y : Int, t ≤ y → y ≤ s → HashMap.mem (build nums) y = true) := by
  refine ⟨runStart (fun y => HashMap.mem (build nums) y) nums.length s, ?_, ?_, ?_⟩
  · exact (runStart_P1 (fun y => HashMap.mem (build nums) y) nums.length s hs).1
  · rcases runStart_P2 (fun y => HashMap.mem (build nums) y) nums.length s hs with h | h
    · exact h
    · exfalso
      obtain ⟨h1, h2, h3⟩ := runStart_P1 (fun y => HashMap.mem (build nums) y) nums.length s hs
      have hb : ∀ i : Nat, i < nums.length + 1 →
          runStart (fun y => HashMap.mem (build nums) y) nums.length s + (i : Int) ∈ nums := by
        intro i hi
        have hy : HashMap.mem (build nums) (runStart (fun y => HashMap.mem (build nums) y) nums.length s + i) = true :=
          h2 _ (by omega) (by rw [h]; omega)
        exact (mem_build nums _).mp hy
      have := pigeon nums (runStart (fun y => HashMap.mem (build nums) y) nums.length s) (nums.length + 1) hb
      omega
  · exact (runStart_P1 (fun y => HashMap.mem (build nums) y) nums.length s hs).2.1

/-- One Phase-2 step: if `x` is a run start, fold in its run length; otherwise pass `best` through. -/
def stepP (S : AHashSet) (F : Nat) (best : Nat) (x : Int) : Nat :=
  if HashMap.mem S (x - 1) then best else LC128.nmax best (runFrom (fun y => HashMap.mem S y) F x)

/-- The Phase-2 scan is monotone in its accumulator. -/
theorem scan_mono (S : AHashSet) (F : Nat) : ∀ (l : List Int) (b : Nat),
    b ≤ l.foldl (stepP S F) b := by
  intro l
  induction l with
  | nil => intro b; exact Nat.le_refl b
  | cons a rest ih =>
    intro b
    have hstep : b ≤ stepP S F b a := by
      unfold stepP
      split
      · exact Nat.le_refl b
      · exact LC128.nmax_ge_left b _
    exact Nat.le_trans hstep (ih (stepP S F b a))

/-- The final scan value dominates the run length of every counted run-start in the list. -/
theorem scan_dom (S : AHashSet) (F : Nat) : ∀ (l : List Int) (b : Nat) (t : Int),
    t ∈ l → HashMap.mem S (t - 1) = false →
    runFrom (fun y => HashMap.mem S y) F t ≤ l.foldl (stepP S F) b := by
  intro l
  induction l with
  | nil => intro b t ht _; exact absurd ht (List.not_mem_nil)
  | cons a rest ih =>
    intro b t ht hstart
    rcases List.mem_cons.mp ht with he | he
    · subst he
      have hcond : ¬ (HashMap.mem S (t - 1) = true) := by rw [hstart]; decide
      have hstepval : stepP S F b t = LC128.nmax b (runFrom (fun y => HashMap.mem S y) F t) := by
        unfold stepP; rw [if_neg hcond]
      have h1 : runFrom (fun y => HashMap.mem S y) F t ≤ stepP S F b t := by
        rw [hstepval]; exact LC128.nmax_ge_right _ _
      exact Nat.le_trans h1 (scan_mono S F rest (stepP S F b t))
    · exact ih (stepP S F b a) t he hstart

/-- Achievability predicate: `k` is the length of some value-run present in `nums`. -/
def Ach (nums : List Int) (k : Nat) : Prop := ∃ s : Int, ∀ i : Nat, i < k → s + (i : Int) ∈ nums

/-- Every run-counter value is achievable (its counted block is in the set, hence in `nums`). -/
theorem ach_runFrom (nums : List Int) (F : Nat) (x : Int) :
    Ach nums (runFrom (fun y => HashMap.mem (build nums) y) F x) := by
  refine ⟨x, fun i hi => ?_⟩
  have := runFrom_mem (fun y => HashMap.mem (build nums) y) F x i hi
  exact (mem_build nums (x + i)).mp this

/-- Achievability is preserved along the Phase-2 scan. -/
theorem ach_scan (nums : List Int) (F : Nat) : ∀ (l : List Int) (b : Nat),
    Ach nums b → Ach nums (l.foldl (stepP (build nums) F) b) := by
  intro l
  induction l with
  | nil => intro b hb; exact hb
  | cons a rest ih =>
    intro b hb
    apply ih
    unfold stepP
    split
    · exact hb
    · rcases LC128.nmax_eq_or b (runFrom (fun y => HashMap.mem (build nums) y) F a) with h | h
      · rw [h]; exact hb
      · rw [h]; exact ach_runFrom nums F a

/-! ## The derived O(n)-expected program and its correctness -/

/-- **The derived program**: build the set (Phase 1), then max over run lengths at run starts
    (Phase 2), fuel-bounded by `nums.length`. -/
def hashLongest (nums : List Int) : Nat :=
  nums.foldl (stepP (build nums) nums.length) 0

/-- **Achievability**: `hashLongest nums` is the length of some value-run present in `nums`. -/
theorem hash_ach (nums : List Int) :
    ∃ s : Int, ∀ i : Nat, i < hashLongest nums → s + (i : Int) ∈ nums :=
  ach_scan nums nums.length nums 0 ⟨0, fun i hi => absurd hi (by omega)⟩

/-- **Domination**: `hashLongest nums` is `≥` every value-run present in `nums`.  Locate the run-start
    `t` of the block's base `s`, count from `t` (fuel `≥ Lrun` by `pigeon`), and note `t` is a counted
    run-start so the scan's max dominates its count. -/
theorem hash_dom (nums : List Int) : ∀ (s : Int) (Lrun : Nat),
    (∀ i : Nat, i < Lrun → s + (i : Int) ∈ nums) → Lrun ≤ hashLongest nums := by
  intro s Lrun hblock
  rcases Nat.eq_zero_or_pos Lrun with hL | hL
  · omega
  · have hs_mem : HashMap.mem (build nums) s = true :=
      (mem_build nums s).mpr (by have := hblock 0 (by omega); simpa using this)
    have hLF : Lrun ≤ nums.length := pigeon nums s Lrun hblock
    obtain ⟨t, ht_le, ht_start, ht_int⟩ := run_start_exists nums s hs_mem
    have ht_nums : t ∈ nums := (mem_build nums t).mp (ht_int t (by omega) ht_le)
    have hblockS : ∀ j : Nat, j < Lrun → (fun y => HashMap.mem (build nums) y) (t + j) = true := by
      intro j hj
      by_cases hjs : t + (j : Int) ≤ s
      · exact ht_int (t + j) (by omega) hjs
      · have hk : t + (j : Int) ∈ nums := by
          have hm : (((t + (j : Int) - s).toNat : Nat) : Int) = t + (j : Int) - s := by omega
          have hlt : (t + (j : Int) - s).toNat < Lrun := by omega
          have hmem := hblock (t + (j : Int) - s).toNat hlt
          have heq : s + (((t + (j : Int) - s).toNat : Nat) : Int) = t + (j : Int) := by
            rw [hm]; omega
          rwa [heq] at hmem
        exact (mem_build nums (t + j)).mpr hk
    have hrun : Lrun ≤ runFrom (fun y => HashMap.mem (build nums) y) nums.length t :=
      runFrom_ge (fun y => HashMap.mem (build nums) y) nums.length Lrun t hblockS hLF
    have hdom : runFrom (fun y => HashMap.mem (build nums) y) nums.length t ≤ hashLongest nums :=
      scan_dom (build nums) nums.length nums 0 t ht_nums ht_start
    omega

/-- `hashLongest` equals `L128`'s sorting-based `longestConsecFn` — both satisfy the achievability +
    domination spec, which pins a unique value (antisymmetry). -/
theorem hashLongest_eq (nums : List Int) : hashLongest nums = LC128.longestConsecFn nums := by
  obtain ⟨s2, hs2⟩ := hash_ach nums
  obtain ⟨s1, hs1⟩ := (LC128.longestConsec_correct nums).1
  have le1 : hashLongest nums ≤ LC128.longestConsecFn nums :=
    (LC128.longestConsec_correct nums).2 s2 (hashLongest nums) hs2
  have le2 : LC128.longestConsecFn nums ≤ hashLongest nums :=
    hash_dom nums s1 (LC128.longestConsecFn nums) hs1
  omega

/-! ## The derived allegory program -/

/-- **The derived program** as a morphism `NumList ⟶ ℕ` in `Rel(Set)`. -/
def derivedSolve : LC128.NumList ⟶ LC128.dNat := graph hashLongest

/-- **The derived program equals the hand-written `LC128.solve`** (same relation). -/
theorem derivedSolve_eq_solve : derivedSolve = LC128.solve := by
  apply hom_ext; intro nums L
  show (L = hashLongest nums) ↔ (L = LC128.longestConsecFn nums)
  rw [hashLongest_eq]

/-! ## Correctness headline -/

/-- **Headline.**  The O(n)-expected hash-set program computes the Longest-Consecutive-Sequence
    optimum: `derivedSolve` relates each `nums` to a value `m` that is an achievable value-run length
    (some `s` with `s, s+1, …, s+m-1` all in `nums`) and dominates every value-run present in `nums`.
    Same statement (and drop-in name) as the sorting-based derivation; here proved directly from the
    hash-set membership spec. -/
theorem longestConsec_derived_correct (nums : List Int) :
    ∃ m, derivedSolve nums m ∧
      (∃ s : Int, ∀ i : Nat, i < m → s + (i : Int) ∈ nums) ∧
      (∀ (s : Int) (Lrun : Nat), (∀ i : Nat, i < Lrun → s + (i : Int) ∈ nums) → Lrun ≤ m) :=
  ⟨hashLongest nums, rfl, hash_ach nums, hash_dom nums⟩

/-! ## Running the derived program (LeetCode 128 examples) -/

example : hashLongest [100, 4, 200, 1, 3, 2] = 4 := by decide
example : hashLongest [0, 3, 7, 2, 5, 8, 4, 6, 0, 1] = 9 := by decide
example : hashLongest ([] : List Int) = 0 := by decide
example : hashLongest [1, 2, 2, 3] = 3 := by decide

#eval hashLongest [100, 4, 200, 1, 3, 2]        -- 4
#eval hashLongest [0, 3, 7, 2, 5, 8, 4, 6, 0, 1] -- 9

#print axioms longestConsec_derived_correct

end Freyd.Alg.RelSet.LC128D
