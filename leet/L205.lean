/-
  LeetCode 205 — Isomorphic Strings — as an ALLEGORY PROGRAM.

  Problem: given `s` and `t` (here `List Int`, character codes), decide whether they are
  ISOMORPHIC — there is a position-preserving bijection between their characters, i.e. `s` and `t`
  have exactly the SAME EQUALITY PATTERN: `s[i] = s[j]` at a pair of positions iff `t[i] = t[j]`
  at that same pair.  ("egg"/"add" → true: both have the pattern `a,b,b`.  "foo"/"bar" → false:
  `foo` repeats, `bar` doesn't.)

  1. **Data** — a plain pair of `List Int` (no initial-algebra engine needed: the scan is a single
     left-to-right pass over both lists together, `L1.lean`'s style, not a fold over a book-worthy
     datatype).

  2. **Program** — `isoGo mapST mapTS s t` walks `s`,`t` together carrying TWO association lists:
     `mapST` (values seen in `s` ↦ their paired `t`-value) and `mapTS` (the converse).  At each pair
     `(x,y)`: if `x` and `y` are BOTH fresh, record the new pair in both maps and continue; if BOTH
     have been seen before, accept iff their recorded partners agree with the current pair (and
     continue without re-recording); any other combination (one fresh, one not, or a recorded
     partner disagreeing) rejects immediately.  `isIsoFn s t := isoGo [] [] s t`.

  3. **Specification** — the HONEST equality-pattern relation, no existential over functions:
     `IsIso s t := s.length = t.length ∧ ∀ i j, s[i]? = s[j]? ↔ t[i]? = t[j]?`.  This is the direct,
     checkable form of "same equality pattern both ways" — the two-way map scan builds the
     bijection incrementally; this relation is what it certifies.

  4. **Correctness** — `iso_correct : isIsoFn s t = true ↔ IsIso s t`, a DECISION-problem `iff`
     (`L217`'s shape, not an extremum).  The crux is `isoGo_iff`, ONE generalized induction
     threading three loop invariants through the scan (`L1`'s `go_gen` recipe, doubled to two
     association lists): `SeenIff` (each map records EXACTLY the co-occurrence pairs seen so far,
     in both directions) and a length-bounded "no clash yet" invariant on the processed prefix,
     converted to the spec's UNBOUNDED `∀ i j` form once lengths are known equal (`noClash_ext`:
     out-of-range indices give `none` on both sides for free).

  Mathlib-free; axioms ⊆ {propext, Quot.sound} (fully constructive, no `Classical.choice`).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC205

open Freyd

/-! ## A `List.getElem?` helper (ported from `L1.lean`) -/

/-- The freshly-appended element sits exactly at index `l1.length`. -/
theorem getElem?_append_right_zero {l1 l2 : List Int} {x : Int} :
    (l1 ++ x :: l2)[l1.length]? = some x := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

/-! ## The program: a two-way consistency scan over association lists -/

/-- `lookupL k m` — the value paired with the first occurrence of key `k` in the association list
    `m`, if any. -/
def lookupL (k : Int) : List (Int × Int) → Option Int
  | [] => none
  | (a, b) :: rest => if a = k then some b else lookupL k rest

theorem lookupL_some : ∀ {m : List (Int × Int)} {k v : Int}, lookupL k m = some v → (k, v) ∈ m := by
  intro m
  induction m with
  | nil => intro k v h; simp [lookupL] at h
  | cons p rest ih =>
    intro k v h
    obtain ⟨a, b⟩ := p
    simp only [lookupL] at h
    split at h
    · rename_i heq
      have hbv : b = v := by injection h
      rw [← heq, ← hbv]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookupL_none : ∀ {m : List (Int × Int)} {k : Int}, lookupL k m = none → ∀ v, (k, v) ∉ m := by
  intro m
  induction m with
  | nil => intro k _ v hmem; exact absurd hmem List.not_mem_nil
  | cons p rest ih =>
    intro k h v hmem
    obtain ⟨a, b⟩ := p
    simp only [lookupL] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hne
      rcases List.mem_cons.mp hmem with heq2 | hmem'
      · injection heq2 with hk _
        exact hne hk.symm
      · exact ih h v hmem'

/-- `isoGo mapST mapTS s t` — the two-way consistency scan.  `mapST`/`mapTS` are the association
    lists of `s`-value ↦ `t`-value / `t`-value ↦ `s`-value seen so far. -/
def isoGo (mapST mapTS : List (Int × Int)) : List Int → List Int → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    match lookupL x mapST, lookupL y mapTS with
    | some y1, some x1 => decide (y1 = y) && decide (x1 = x) && isoGo mapST mapTS xs ys
    | none, none => isoGo ((x, y) :: mapST) ((y, x) :: mapTS) xs ys
    | some _, none => false
    | none, some _ => false

/-- **The program**: LeetCode 205's solution. -/
def isIsoFn (s t : List Int) : Bool := isoGo [] [] s t

/-! ## `Rel(Set)` packaging -/

/-- The input object: a pair of character-code lists. -/
abbrev Input : RelSet.{0} := ⟨List Int × List Int⟩
/-- The answer object: booleans. -/
abbrev dBool : RelSet.{0} := ⟨Bool⟩

/-- **The allegory program**: LeetCode 205's solution as a morphism `Input ⟶ Bool` in `Rel(Set)`. -/
def solve : Input ⟶ dBool := graph (fun p : List Int × List Int => isIsoFn p.1 p.2)

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map (fun p : List Int × List Int => isIsoFn p.1 p.2)

/-! ## Specification: same length, same equality pattern (the HONEST, existential-free form) -/

/-- `IsIso s t` — `s` and `t` have the same length and the same equality pattern: two positions
    coincide in `s` iff their images coincide in `t`.  Equivalent to "∃ a position-preserving
    bijection between the characters", but directly checkable. -/
def IsIso (s t : List Int) : Prop :=
  s.length = t.length ∧ ∀ (i j : Nat), s[i]? = s[j]? ↔ t[i]? = t[j]?

/-- Refuting `IsIso` from one witness pair where the `s`-side coincides but the `t`-side doesn't. -/
theorem not_isIso_of_true_false {A B : List Int} {i j : Nat}
    (hP : A[i]? = A[j]?) (hQ : ¬ (B[i]? = B[j]?)) : ¬ IsIso A B :=
  fun hiso => hQ ((hiso.2 i j).mp hP)

/-- Refuting `IsIso` from one witness pair where the `t`-side coincides but the `s`-side doesn't. -/
theorem not_isIso_of_false_true {A B : List Int} {i j : Nat}
    (hP : ¬ (A[i]? = A[j]?)) (hQ : B[i]? = B[j]?) : ¬ IsIso A B :=
  fun hiso => hP ((hiso.2 i j).mpr hQ)

/-- The unbounded pattern-equality follows from the bounded one once the two lists have equal
    length: out-of-range indices give `none` on both sides for free. -/
theorem noClash_ext {A B : List Int} (hlen : A.length = B.length)
    (h : ∀ (i j : Nat), i < A.length → j < A.length → (A[i]? = A[j]? ↔ B[i]? = B[j]?)) :
    ∀ (i j : Nat), A[i]? = A[j]? ↔ B[i]? = B[j]? := by
  intro i j
  rcases Nat.lt_or_ge i A.length with hi | hi
  · rcases Nat.lt_or_ge j A.length with hj | hj
    · exact h i j hi hj
    · have hAj : A[j]? = none := List.getElem?_eq_none_iff.mpr hj
      have hBj : B[j]? = none := List.getElem?_eq_none_iff.mpr (hlen ▸ hj)
      have hAi : A[i]? ≠ none := fun h => absurd (List.getElem?_eq_none_iff.mp h) (by omega)
      have hBi : B[i]? ≠ none := fun h => absurd (List.getElem?_eq_none_iff.mp h) (by omega)
      rw [hAj, hBj]
      exact ⟨fun h => absurd h hAi, fun h => absurd h hBi⟩
  · have hAi : A[i]? = none := List.getElem?_eq_none_iff.mpr hi
    have hBi : B[i]? = none := List.getElem?_eq_none_iff.mpr (hlen ▸ hi)
    rcases Nat.lt_or_ge j A.length with hj | hj
    · have hAj : A[j]? ≠ none := fun h => absurd (List.getElem?_eq_none_iff.mp h) (by omega)
      have hBj : B[j]? ≠ none := fun h => absurd (List.getElem?_eq_none_iff.mp h) (by omega)
      rw [hAi, hBi]
      exact ⟨fun h => absurd h.symm hAj, fun h => absurd h.symm hBj⟩
    · have hAj : A[j]? = none := List.getElem?_eq_none_iff.mpr hj
      have hBj : B[j]? = none := List.getElem?_eq_none_iff.mpr (hlen ▸ hj)
      rw [hAi, hAj, hBi, hBj]

/-- If a `hnc`-invariant position `w` witnesses `A[w]? = some u`, `B[w]? = some v`, every OTHER
    in-range position agrees with `u` on the `A`-side iff it agrees with `v` on the `B`-side. -/
theorem transfer_at {A B : List Int} {w : Nat} {u v : Int}
    (hnc : ∀ (p q : Nat), p < A.length → q < A.length → (A[p]? = A[q]? ↔ B[p]? = B[q]?))
    (hw : w < A.length) (hAw : A[w]? = some u) (hBw : B[w]? = some v) {q : Nat} (hq : q < A.length) :
    A[q]? = some u ↔ B[q]? = some v := by
  constructor
  · intro hAq
    have h1 : A[q]? = A[w]? := hAq.trans hAw.symm
    have h2 : B[q]? = B[w]? := (hnc q w hq hw).mp h1
    exact h2.trans hBw
  · intro hBq
    have h1 : B[q]? = B[w]? := hBq.trans hBw.symm
    have h2 : A[q]? = A[w]? := (hnc q w hq hw).mpr h1
    exact h2.trans hAw

/-! ## The loop invariant: each map records EXACTLY the co-occurrence pairs seen so far -/

/-- `SeenIff l1 l2 m` — `m` records exactly the pairs `(l1[i], l2[i])` for processed indices `i`. -/
def SeenIff (l1 l2 : List Int) (m : List (Int × Int)) : Prop :=
  ∀ a b, (a, b) ∈ m ↔ ∃ i : Nat, l1[i]? = some a ∧ l2[i]? = some b

/-- Extending `SeenIff` by one step, covering BOTH the "push a fresh pair" (`m' = (x,y) :: m`) and
    the "pair already recorded, no push needed" (`m' = m`) cases uniformly. -/
theorem SeenIff_step {l1 l2 : List Int} {m m' : List (Int × Int)} {x y : Int}
    (h : SeenIff l1 l2 m) (hlen : l1.length = l2.length)
    (hm' : m' = m ∨ m' = (x, y) :: m) (hcov : (x, y) ∈ m') :
    SeenIff (l1 ++ [x]) (l2 ++ [y]) m' := by
  intro a b
  constructor
  · intro hab
    have hab' : (a, b) ∈ m ∨ (a, b) = (x, y) := by
      rcases hm' with heq | heq
      · exact Or.inl (heq ▸ hab)
      · rw [heq] at hab
        rcases List.mem_cons.mp hab with h1 | h1
        · exact Or.inr h1
        · exact Or.inl h1
    rcases hab' with hmem | heq
    · obtain ⟨i, hi1, hi2⟩ := (h a b).mp hmem
      have hib : i < l1.length := (List.getElem?_eq_some_iff.mp hi1).1
      exact ⟨i, by rw [List.getElem?_append_left hib]; exact hi1,
                by rw [List.getElem?_append_left (hlen ▸ hib)]; exact hi2⟩
    · injection heq with ha hb
      exact ⟨l1.length, by rw [ha]; exact getElem?_append_right_zero,
                by rw [hb, hlen]; exact getElem?_append_right_zero⟩
  · rintro ⟨i, hi1, hi2⟩
    rcases Nat.lt_or_ge i l1.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hi1
      rw [List.getElem?_append_left (hlen ▸ hlt)] at hi2
      have hmem : (a, b) ∈ m := (h a b).mpr ⟨i, hi1, hi2⟩
      rcases hm' with heq | heq
      · rw [heq]; exact hmem
      · rw [heq]; exact List.mem_cons_of_mem _ hmem
    · have hieq : i = l1.length := by
        have hib := (List.getElem?_eq_some_iff.mp hi1).1
        simp only [List.length_append, List.length_singleton] at hib
        omega
      rw [hieq, getElem?_append_right_zero] at hi1
      rw [hieq, hlen, getElem?_append_right_zero] at hi2
      injection hi1 with ha
      injection hi2 with hb
      rw [← ha, ← hb]
      exact hcov

/-- If `x` was NOT found in `mapST`, it does not occur anywhere in the processed `s`-prefix. -/
theorem fresh_of_lookup_none {l1 l2 : List Int} {m : List (Int × Int)} {x : Int}
    (hlen : l1.length = l2.length) (h : SeenIff l1 l2 m) (hnone : lookupL x m = none) :
    ∀ j : Nat, l1[j]? ≠ some x := by
  intro j hxj
  have hjlt : j < l1.length := (List.getElem?_eq_some_iff.mp hxj).1
  have hjlt' : j < l2.length := hlen ▸ hjlt
  have hv : l2[j]? = some (l2[j]'hjlt') := List.getElem?_eq_getElem hjlt'
  exact lookupL_none hnone (l2[j]'hjlt') ((h x (l2[j]'hjlt')).mpr ⟨j, hxj, hv⟩)

/-- A key found via `lookupL` came from a genuine co-occurrence witness. -/
theorem witness_of_lookup_some {l1 l2 : List Int} {m : List (Int × Int)} {k v : Int}
    (h : SeenIff l1 l2 m) (hk : lookupL k m = some v) :
    ∃ i : Nat, l1[i]? = some k ∧ l2[i]? = some v :=
  (h k v).mp (lookupL_some hk)

/-! ## The main loop lemma: ONE generalized induction gives the decision `iff` -/

theorem isoGo_iff : ∀ (xs ys doneS doneT : List Int) (mapST mapTS : List (Int × Int)),
    doneS.length = doneT.length →
    SeenIff doneS doneT mapST → SeenIff doneT doneS mapTS →
    (∀ (i j : Nat), i < doneS.length → j < doneS.length →
      (doneS[i]? = doneS[j]? ↔ doneT[i]? = doneT[j]?)) →
    (isoGo mapST mapTS xs ys = true ↔ IsIso (doneS ++ xs) (doneT ++ ys)) := by
  intro xs
  induction xs with
  | nil =>
    intro ys doneS doneT mapST mapTS hlen hst hts hnc
    cases ys with
    | nil =>
      show (true = true) ↔ IsIso (doneS ++ []) (doneT ++ [])
      rw [List.append_nil, List.append_nil]
      constructor
      · intro _; exact ⟨hlen, noClash_ext hlen hnc⟩
      · intro _; rfl
    | cons y ys' =>
      show (false = true) ↔ IsIso (doneS ++ []) (doneT ++ (y :: ys'))
      rw [List.append_nil]
      constructor
      · exact fun h => nomatch h
      · rintro ⟨hl, _⟩
        exfalso
        simp only [List.length_append, List.length_cons] at hl
        omega
  | cons x xs' ih =>
    intro ys doneS doneT mapST mapTS hlen hst hts hnc
    cases ys with
    | nil =>
      show (false = true) ↔ IsIso (doneS ++ (x :: xs')) (doneT ++ [])
      rw [List.append_nil]
      constructor
      · exact fun h => nomatch h
      · rintro ⟨hl, _⟩
        exfalso
        simp only [List.length_append, List.length_cons] at hl
        omega
    | cons y ys' =>
      show (isoGo mapST mapTS (x :: xs') (y :: ys') = true) ↔
        IsIso (doneS ++ x :: xs') (doneT ++ y :: ys')
      have hassocS : doneS ++ x :: xs' = (doneS ++ [x]) ++ xs' := by simp
      have hassocT : doneT ++ y :: ys' = (doneT ++ [y]) ++ ys' := by simp
      rcases hlx : lookupL x mapST with _ | y1 <;> rcases hly : lookupL y mapTS with _ | x1
      · -- both fresh: push a new pair into both maps
        have hgo_eq : isoGo mapST mapTS (x :: xs') (y :: ys') =
            isoGo ((x, y) :: mapST) ((y, x) :: mapTS) xs' ys' := by
          simp only [isoGo, hlx, hly]
        rw [hgo_eq]
        have hstx : SeenIff (doneS ++ [x]) (doneT ++ [y]) ((x, y) :: mapST) :=
          SeenIff_step hst hlen (Or.inr rfl) (List.mem_cons_self ..)
        have htsy : SeenIff (doneT ++ [y]) (doneS ++ [x]) ((y, x) :: mapTS) :=
          SeenIff_step hts hlen.symm (Or.inr rfl) (List.mem_cons_self ..)
        have hlen' : (doneS ++ [x]).length = (doneT ++ [y]).length := by simp [hlen]
        have hfreshS := fresh_of_lookup_none hlen hst hlx
        have hfreshT := fresh_of_lookup_none hlen.symm hts hly
        have hnc' : ∀ (p q : Nat), p < (doneS ++ [x]).length → q < (doneS ++ [x]).length →
            ((doneS ++ [x])[p]? = (doneS ++ [x])[q]? ↔ (doneT ++ [y])[p]? = (doneT ++ [y])[q]?) := by
          intro p q hp hq
          rcases Nat.lt_or_ge p doneS.length with hplt | hpge
          · rcases Nat.lt_or_ge q doneS.length with hqlt | hqge
            · rw [List.getElem?_append_left hplt, List.getElem?_append_left hqlt,
                  List.getElem?_append_left (hlen ▸ hplt), List.getElem?_append_left (hlen ▸ hqlt)]
              exact hnc p q hplt hqlt
            · have hqeq : q = doneS.length := by
                simp only [List.length_append, List.length_singleton] at hq; omega
              have hSp : (doneS ++ [x])[p]? = doneS[p]? := List.getElem?_append_left hplt
              have hSq : (doneS ++ [x])[q]? = some x := by rw [hqeq]; exact getElem?_append_right_zero
              have hTp : (doneT ++ [y])[p]? = doneT[p]? := List.getElem?_append_left (hlen ▸ hplt)
              have hTq : (doneT ++ [y])[q]? = some y := by
                rw [hqeq, hlen]; exact getElem?_append_right_zero
              rw [hSp, hSq, hTp, hTq]
              exact ⟨fun h => absurd h (hfreshS p), fun h => absurd h (hfreshT p)⟩
          · have hpeq : p = doneS.length := by
              simp only [List.length_append, List.length_singleton] at hp; omega
            rcases Nat.lt_or_ge q doneS.length with hqlt | hqge
            · have hSp : (doneS ++ [x])[p]? = some x := by rw [hpeq]; exact getElem?_append_right_zero
              have hSq : (doneS ++ [x])[q]? = doneS[q]? := List.getElem?_append_left hqlt
              have hTp : (doneT ++ [y])[p]? = some y := by
                rw [hpeq, hlen]; exact getElem?_append_right_zero
              have hTq : (doneT ++ [y])[q]? = doneT[q]? := List.getElem?_append_left (hlen ▸ hqlt)
              rw [hSp, hSq, hTp, hTq]
              exact ⟨fun h => absurd h.symm (hfreshS q), fun h => absurd h.symm (hfreshT q)⟩
            · have hqeq : q = doneS.length := by
                simp only [List.length_append, List.length_singleton] at hq; omega
              rw [hpeq, hqeq]
              exact ⟨fun _ => rfl, fun _ => rfl⟩
        have hres := ih ys' (doneS ++ [x]) (doneT ++ [y]) ((x, y) :: mapST) ((y, x) :: mapTS)
          hlen' hstx htsy hnc'
        rwa [← hassocS, ← hassocT] at hres
      · -- `x` fresh, `y` already seen (mapped to `x1`): asymmetric ⟹ reject and refute `IsIso`
        have hgo_eq : isoGo mapST mapTS (x :: xs') (y :: ys') = false := by
          simp only [isoGo, hlx, hly]
        rw [hgo_eq]
        obtain ⟨j, hjT, hjS⟩ := witness_of_lookup_some hts hly
        have hjlt : j < doneT.length := (List.getElem?_eq_some_iff.mp hjT).1
        have hfreshS := fresh_of_lookup_none hlen hst hlx
        have hx1x : x1 ≠ x := fun heq => hfreshS j (heq ▸ hjS)
        have hSj : (doneS ++ x :: xs')[j]? = some x1 := by
          rw [List.getElem?_append_left (hlen ▸ hjlt)]; exact hjS
        have hSn : (doneS ++ x :: xs')[doneS.length]? = some x := getElem?_append_right_zero
        have hTj : (doneT ++ y :: ys')[j]? = some y := by
          rw [List.getElem?_append_left hjlt]; exact hjT
        have hTn : (doneT ++ y :: ys')[doneS.length]? = some y := by
          rw [hlen]; exact getElem?_append_right_zero
        constructor
        · exact fun h => nomatch h
        · intro hiso
          have hP : ¬ ((doneS ++ x :: xs')[j]? = (doneS ++ x :: xs')[doneS.length]?) := by
            rw [hSj, hSn]; exact fun hc => hx1x (by injection hc)
          have hQ : (doneT ++ y :: ys')[j]? = (doneT ++ y :: ys')[doneS.length]? := by rw [hTj, hTn]
          exact (not_isIso_of_false_true hP hQ hiso).elim
      · -- `x` already seen (mapped to `y1`), `y` fresh: asymmetric the other way
        have hgo_eq : isoGo mapST mapTS (x :: xs') (y :: ys') = false := by
          simp only [isoGo, hlx, hly]
        rw [hgo_eq]
        obtain ⟨i, hiS, hiT⟩ := witness_of_lookup_some hst hlx
        have hilt : i < doneS.length := (List.getElem?_eq_some_iff.mp hiS).1
        have hfreshT := fresh_of_lookup_none hlen.symm hts hly
        have hy1y : y1 ≠ y := fun heq => hfreshT i (heq ▸ hiT)
        have hSi : (doneS ++ x :: xs')[i]? = some x := by
          rw [List.getElem?_append_left hilt]; exact hiS
        have hSn : (doneS ++ x :: xs')[doneS.length]? = some x := getElem?_append_right_zero
        have hTi : (doneT ++ y :: ys')[i]? = some y1 := by
          rw [List.getElem?_append_left (hlen ▸ hilt)]; exact hiT
        have hTn : (doneT ++ y :: ys')[doneS.length]? = some y := by
          rw [hlen]; exact getElem?_append_right_zero
        constructor
        · exact fun h => nomatch h
        · intro hiso
          have hP : (doneS ++ x :: xs')[i]? = (doneS ++ x :: xs')[doneS.length]? := by rw [hSi, hSn]
          have hQ : ¬ ((doneT ++ y :: ys')[i]? = (doneT ++ y :: ys')[doneS.length]?) := by
            rw [hTi, hTn]; exact fun hc => hy1y (by injection hc)
          exact (not_isIso_of_true_false hP hQ hiso).elim
      · -- both `x` and `y` already seen: accept iff the recorded partners agree
        have hgo_eq : isoGo mapST mapTS (x :: xs') (y :: ys') =
            (decide (y1 = y) && decide (x1 = x) && isoGo mapST mapTS xs' ys') := by
          simp only [isoGo, hlx, hly]
        rw [hgo_eq]
        obtain ⟨i, hiS, hiT⟩ := witness_of_lookup_some hst hlx
        have hilt : i < doneS.length := (List.getElem?_eq_some_iff.mp hiS).1
        by_cases hy1 : y1 = y
        · by_cases hx1 : x1 = x
          · -- both partners agree: accept, extend the (unchanged) maps
            have hyy : decide (y1 = y) = true := decide_eq_true_eq.mpr hy1
            have hxx : decide (x1 = x) = true := decide_eq_true_eq.mpr hx1
            rw [hyy, hxx, Bool.true_and, Bool.true_and]
            have hmemST : (x, y) ∈ mapST := hy1 ▸ lookupL_some hlx
            have hmemTS : (y, x) ∈ mapTS := hx1 ▸ lookupL_some hly
            have hstx : SeenIff (doneS ++ [x]) (doneT ++ [y]) mapST :=
              SeenIff_step hst hlen (Or.inl rfl) hmemST
            have htsy : SeenIff (doneT ++ [y]) (doneS ++ [x]) mapTS :=
              SeenIff_step hts hlen.symm (Or.inl rfl) hmemTS
            have hlen' : (doneS ++ [x]).length = (doneT ++ [y]).length := by simp [hlen]
            have hiTy : doneT[i]? = some y := hy1 ▸ hiT
            have hnc' : ∀ (p q : Nat), p < (doneS ++ [x]).length → q < (doneS ++ [x]).length →
                ((doneS ++ [x])[p]? = (doneS ++ [x])[q]? ↔ (doneT ++ [y])[p]? = (doneT ++ [y])[q]?) := by
              intro p q hp hq
              rcases Nat.lt_or_ge p doneS.length with hplt | hpge
              · rcases Nat.lt_or_ge q doneS.length with hqlt | hqge
                · rw [List.getElem?_append_left hplt, List.getElem?_append_left hqlt,
                      List.getElem?_append_left (hlen ▸ hplt), List.getElem?_append_left (hlen ▸ hqlt)]
                  exact hnc p q hplt hqlt
                · have hqeq : q = doneS.length := by
                    simp only [List.length_append, List.length_singleton] at hq; omega
                  have hSp : (doneS ++ [x])[p]? = doneS[p]? := List.getElem?_append_left hplt
                  have hSq : (doneS ++ [x])[q]? = some x := by
                    rw [hqeq]; exact getElem?_append_right_zero
                  have hTp : (doneT ++ [y])[p]? = doneT[p]? := List.getElem?_append_left (hlen ▸ hplt)
                  have hTq : (doneT ++ [y])[q]? = some y := by
                    rw [hqeq, hlen]; exact getElem?_append_right_zero
                  rw [hSp, hSq, hTp, hTq]
                  exact transfer_at hnc hilt hiS hiTy hplt
              · have hpeq : p = doneS.length := by
                  simp only [List.length_append, List.length_singleton] at hp; omega
                rcases Nat.lt_or_ge q doneS.length with hqlt | hqge
                · have hSp : (doneS ++ [x])[p]? = some x := by
                    rw [hpeq]; exact getElem?_append_right_zero
                  have hSq : (doneS ++ [x])[q]? = doneS[q]? := List.getElem?_append_left hqlt
                  have hTp : (doneT ++ [y])[p]? = some y := by
                    rw [hpeq, hlen]; exact getElem?_append_right_zero
                  have hTq : (doneT ++ [y])[q]? = doneT[q]? := List.getElem?_append_left (hlen ▸ hqlt)
                  rw [hSp, hSq, hTp, hTq]
                  constructor
                  · intro h; exact ((transfer_at hnc hilt hiS hiTy hqlt).mp h.symm).symm
                  · intro h; exact ((transfer_at hnc hilt hiS hiTy hqlt).mpr h.symm).symm
                · have hqeq : q = doneS.length := by
                    simp only [List.length_append, List.length_singleton] at hq; omega
                  rw [hpeq, hqeq]
                  exact ⟨fun _ => rfl, fun _ => rfl⟩
            have hres := ih ys' (doneS ++ [x]) (doneT ++ [y]) mapST mapTS hlen' hstx htsy hnc'
            rwa [← hassocS, ← hassocT] at hres
          · -- `x1 ≠ x` (`y1 = y`): reject, refute `IsIso` via the `mapTS` witness `j`
            have hfalse : (decide (y1 = y) && decide (x1 = x) && isoGo mapST mapTS xs' ys') = false := by
              rw [decide_eq_false_iff_not.mpr hx1, Bool.and_false, Bool.false_and]
            rw [hfalse]
            obtain ⟨j, hjT, hjS⟩ := witness_of_lookup_some hts hly
            have hjlt : j < doneT.length := (List.getElem?_eq_some_iff.mp hjT).1
            have hSj : (doneS ++ x :: xs')[j]? = some x1 := by
              rw [List.getElem?_append_left (hlen ▸ hjlt)]; exact hjS
            have hSn : (doneS ++ x :: xs')[doneS.length]? = some x := getElem?_append_right_zero
            have hTj : (doneT ++ y :: ys')[j]? = some y := by
              rw [List.getElem?_append_left hjlt]; exact hjT
            have hTn : (doneT ++ y :: ys')[doneS.length]? = some y := by
              rw [hlen]; exact getElem?_append_right_zero
            constructor
            · exact fun h => nomatch h
            · intro hiso
              have hP : ¬ ((doneS ++ x :: xs')[j]? = (doneS ++ x :: xs')[doneS.length]?) := by
                rw [hSj, hSn]; exact fun hc => hx1 (by injection hc)
              have hQ : (doneT ++ y :: ys')[j]? = (doneT ++ y :: ys')[doneS.length]? := by
                rw [hTj, hTn]
              exact (not_isIso_of_false_true hP hQ hiso).elim
        · -- `y1 ≠ y`: reject, refute `IsIso` via the `mapST` witness `i`
          have hfalse : (decide (y1 = y) && decide (x1 = x) && isoGo mapST mapTS xs' ys') = false := by
            rw [decide_eq_false_iff_not.mpr hy1, Bool.false_and, Bool.false_and]
          rw [hfalse]
          have hSi : (doneS ++ x :: xs')[i]? = some x := by
            rw [List.getElem?_append_left hilt]; exact hiS
          have hSn : (doneS ++ x :: xs')[doneS.length]? = some x := getElem?_append_right_zero
          have hTi : (doneT ++ y :: ys')[i]? = some y1 := by
            rw [List.getElem?_append_left (hlen ▸ hilt)]; exact hiT
          have hTn : (doneT ++ y :: ys')[doneS.length]? = some y := by
            rw [hlen]; exact getElem?_append_right_zero
          constructor
          · exact fun h => nomatch h
          · intro hiso
            have hP : (doneS ++ x :: xs')[i]? = (doneS ++ x :: xs')[doneS.length]? := by
              rw [hSi, hSn]
            have hQ : ¬ ((doneT ++ y :: ys')[i]? = (doneT ++ y :: ys')[doneS.length]?) := by
              rw [hTi, hTn]; exact fun hc => hy1 (by injection hc)
            exact (not_isIso_of_true_false hP hQ hiso).elim

/-! ## Correctness headline -/

/-- **`isIsoFn` decides `IsIso`**: the two-way consistency scan accepts exactly the pairs with the
    same length and the same equality pattern. -/
theorem iso_correct (s t : List Int) : isIsoFn s t = true ↔ IsIso s t := by
  have hst0 : SeenIff ([] : List Int) [] [] := by
    intro a b
    constructor
    · exact fun h => absurd h List.not_mem_nil
    · rintro ⟨i, hi, _⟩; exact nomatch hi
  have hnc0 : ∀ (i j : Nat), i < ([] : List Int).length → j < ([] : List Int).length →
      (([] : List Int)[i]? = ([] : List Int)[j]? ↔ ([] : List Int)[i]? = ([] : List Int)[j]?) :=
    fun i j hi _ => Iff.rfl
  have := isoGo_iff s t [] [] [] [] rfl hst0 hst0 hnc0
  simpa only [List.nil_append] using this

/-! ## Specification and the decision headline -/

/-- The **specification** as a morphism `Input ⟶ Bool` in `Rel(Set)`: `r = true` iff the two
    strings are isomorphic (same length, same equality pattern) — a genuine `Iff`, since this is a
    DECISION problem, not an optimum to extremize. -/
def spec : Input ⟶ dBool := fun p r => (r = true ↔ IsIso p.1 p.2)

/-- Two booleans that agree on being `true` are equal (Bool extensionality). -/
theorem bool_eq_of_iff_true {b c : Bool} (h : (b = true) ↔ (c = true)) : b = c := by
  cases b with
  | true => cases c with
    | true => rfl
    | false => exact (h.mp rfl).symm
  | false => cases c with
    | true => exact h.mpr rfl
    | false => rfl

/-- **`solve` equals `spec` as relations** — the DECISION-problem headline: the program `solve`
    (deciding `isIsoFn`) is exactly the specification "`r = true` iff the strings are isomorphic". -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro p r
  show (r = isIsoFn p.1 p.2) ↔ (r = true ↔ IsIso p.1 p.2)
  constructor
  · intro h; rw [h]; exact iso_correct p.1 p.2
  · intro h; exact bool_eq_of_iff_true (h.trans (iso_correct p.1 p.2).symm)

/-! ## Running the program -/

-- "egg" / "add" → true (pattern a,b,b both times)
example :
    isIsoFn [101, 103, 103] [97, 100, 100] = true := by decide
-- "foo" / "bar" → false (foo repeats, bar doesn't)
example :
    isIsoFn [102, 111, 111] [98, 97, 114] = false := by decide
-- "paper" / "title" → true (pattern a,b,a,c,d both times)
example :
    isIsoFn [112, 97, 112, 101, 114] [116, 105, 116, 108, 101] = true := by decide

end Freyd.Alg.RelSet.LC205
