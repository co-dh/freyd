import Lean

/-!
`Array.qsort` on naturals by `<` answers a sorted permutation of its input (`qsort_nat`). The kernel's `ofRuns`
(`Eval.keyMatch`'s `s#` halving and `u#`/`p#` galloping) sorts its run starts with it; `ofRuns_keys`,
`ofRuns_bounds` and `ofRuns_span` are its three folds. Core ships no lemma about `qsort`, and its recursion
`qsort.sort` and partition loop `qpartition.loop` are private to `Init.Data.Array.QSort.Basic`, so
`qsort_priv%`/`qsort_unfold%` name them by their private names.
-/

namespace LeetQ.Rel.QSort

open Lean Meta Elab Term in
/-- A private helper of the toolchain's `Array.qsort` (`Init.Data.Array.QSort.Basic`), named for proofs. -/
elab "qsort_priv% " id:ident : term => do
  let n := Name.mkNum `_private.Init.Data.Array.QSort.Basic 0 ++ id.getId
  unless (← getEnv).contains n do throwError "no private constant {n} in Init.Data.Array.QSort.Basic"
  mkConstWithFreshMVarLevels n

open Lean Meta Elab Term in
/-- The unfolding equation of a private helper of `Array.qsort`. -/
elab "qsort_unfold% " id:ident : term => do
  let n := Name.mkNum `_private.Init.Data.Array.QSort.Basic 0 ++ id.getId
  let some e ← getUnfoldEqnFor? n (nonRec := true) | throwError "no unfolding equation for {n}"
  mkConstWithFreshMVarLevels e

/-- `as'` permutes `as`, leaves it alone outside `[lo, hi]`, and keeps there any property every element of `as`
    in `[lo, hi]` has. -/
def Keeps {n : Nat} (lo hi : Nat) (as as' : Vector Nat n) : Prop :=
  Vector.Perm as' as ∧ (∀ x (h : x < n), (x < lo ∨ hi < x) → as'[x] = as[x]) ∧
  ∀ P : Nat → Prop, (∀ x (h : x < n), lo ≤ x → x ≤ hi → P as[x]) → ∀ x (h : x < n), lo ≤ x → x ≤ hi → P as'[x]

theorem Keeps.refl {n lo hi : Nat} (as : Vector Nat n) : Keeps lo hi as as :=
  ⟨Vector.Perm.refl _, fun _ _ _ => rfl, fun _ hP => hP⟩

theorem Keeps.trans {n lo hi : Nat} {a b c : Vector Nat n} (h1 : Keeps lo hi a b) (h2 : Keeps lo hi b c) :
    Keeps lo hi a c :=
  ⟨h2.1.trans h1.1, fun x h hx => (h2.2.1 x h hx).trans (h1.2.1 x h hx), fun P hP => h2.2.2 P (h1.2.2 P hP)⟩

theorem Keeps.widen {n lo hi lo' hi' : Nat} {a b : Vector Nat n} (h : Keeps lo' hi' a b) (hl : lo ≤ lo')
    (hh : hi' ≤ hi) : Keeps lo hi a b :=
  ⟨h.1, fun x hx o => h.2.1 x hx (by omega), fun P hP x hx h1 h2 => by
    by_cases hin : lo' ≤ x ∧ x ≤ hi'
    · exact h.2.2 P (fun y hy a1 a2 => hP y hy (by omega) (by omega)) x hx hin.1 hin.2
    · rw [h.2.1 x hx (by omega)]; exact hP x hx h1 h2⟩

theorem Keeps.swap {n lo hi i j : Nat} (as : Vector Nat n) (hi' : i < n) (hj : j < n) (h1 : lo ≤ i) (h2 : i ≤ hi)
    (h3 : lo ≤ j) (h4 : j ≤ hi) : Keeps lo hi as (as.swap i j hi' hj) :=
  ⟨Vector.swap_perm hi' hj, fun x hx o => by rw [Vector.getElem_swap, if_neg (by omega), if_neg (by omega)],
   fun P hP x hx a b => by
    rw [Vector.getElem_swap]
    split
    · exact hP j hj h3 h4
    · split
      · exact hP i hi' h1 h2
      · exact hP x hx a b⟩

theorem Keeps.cswap {n lo hi i j : Nat} (c : Prop) [Decidable c] (as : Vector Nat n) (hi' : i < n) (hj : j < n)
    (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : lo ≤ j) (h4 : j ≤ hi) :
    Keeps lo hi as (if c then as.swap i j hi' hj else as) := by
  split
  · exact Keeps.swap as hi' hj h1 h2 h3 h4
  · exact Keeps.refl as

/-- **`qpartition`'s loop**: rows `[lo, i)` below the pivot, `[i, k)` not, the pivot at `hi`, end with the pivot at
    `i`, below it only smaller rows, above it none. -/
theorem loop_spec {n lo hi : Nat} (hhi : hi < n) (pivot : Nat) : ∀ (d : Nat) (as : Vector Nat n) (i k : Nat)
    (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi), hi - k = d →
    (∀ x (h : x < n), lo ≤ x → x < i → as[x] < pivot) →
    (∀ x (h : x < n), i ≤ x → x < k → ¬ as[x] < pivot) → as[hi] = pivot →
    (i < k ∨ ∃ x, ∃ h : x < n, k ≤ x ∧ x < hi ∧ ¬ as[x] < pivot) →
    ∀ r, (qsort_priv% Array.qpartition.loop) (fun a b : Nat => decide (a < b)) lo hi hhi pivot as i k ilo ik w = r →
    Keeps lo hi as r.2 ∧ r.1.1 < hi ∧
      (∀ x (h : x < n) (hm : r.1.1 < n), lo ≤ x → x < r.1.1 → r.2[x] < r.2[r.1.1]) ∧
      (∀ x (h : x < n) (hm : r.1.1 < n), r.1.1 < x → x ≤ hi → ¬ r.2[x] < r.2[r.1.1]) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro as i k ilo ik w hd h1 h2 h3 h4 r hr
  rw [qsort_unfold% Array.qpartition.loop] at hr
  split at hr
  next hk =>
    split at hr
    next hl =>
      have hl' : as[k] < pivot := by simpa using hl
      obtain ⟨k1, k2, k3, k4⟩ := ih (hi - (k + 1)) (by omega) (as.swap i k (by omega) (by omega)) (i + 1) (k + 1)
        (by omega) (by omega) (by omega) rfl
        (fun x hx a b => by
          rw [Vector.getElem_swap]
          by_cases hxi : x = i
          · rw [if_pos hxi]; exact hl'
          · rw [if_neg hxi, if_neg (by omega)]; exact h1 x hx a (by omega))
        (fun x hx a b => by
          rw [Vector.getElem_swap, if_neg (by omega)]
          by_cases hxk : x = k
          · rw [if_pos hxk]; exact h2 i (by omega) (Nat.le_refl _) (by omega)
          · rw [if_neg hxk]; exact h2 x hx (by omega) (by omega))
        (by rw [Vector.getElem_swap, if_neg (by omega), if_neg (by omega)]; exact h3)
        (by
          rcases h4 with h4 | ⟨x, hx, a, b, c⟩
          · left; omega
          · by_cases hik : i < k
            · left; omega
            · right
              have hxk : x ≠ k := fun e => by subst e; exact c hl'
              refine ⟨x, hx, by omega, b, ?_⟩
              rw [Vector.getElem_swap, if_neg (by omega), if_neg hxk]; exact c)
        r hr
      exact ⟨(Keeps.swap as _ _ (by omega) (by omega) (by omega) (by omega)).trans k1, k2, k3, k4⟩
    next hl =>
      have hl' : ¬ as[k] < pivot := by simpa using hl
      exact ih (hi - (k + 1)) (by omega) as i (k + 1) (by omega) (by omega) (by omega) rfl h1
        (fun x hx a b => if hxk : x = k then by subst hxk; exact hl' else h2 x hx a (by omega)) h3
        (Or.inl (by omega)) r hr
  next hk =>
    subst hr
    have hkh : k = hi := by omega
    have hih : i < hi := by
      rcases h4 with h4 | ⟨x, hx, a, b, c⟩ <;> omega
    refine ⟨Keeps.swap as (by omega) hhi ilo (by omega) (by omega) (Nat.le_refl _), hih, ?_, ?_⟩
    · intro x hx hm a b; dsimp only at a b
      show (as.swap i hi (by omega) hhi)[x] < (as.swap i hi (by omega) hhi)[i]
      rw [Vector.getElem_swap, Vector.getElem_swap, if_pos rfl, if_neg (show x ≠ i by omega), if_neg (show x ≠ hi by omega), h3]
      exact h1 x hx a b
    · intro x hx hm a b; dsimp only at a b
      show ¬ (as.swap i hi (by omega) hhi)[x] < (as.swap i hi (by omega) hhi)[i]
      rw [Vector.getElem_swap, Vector.getElem_swap, if_pos rfl, if_neg (show x ≠ i by omega), h3]
      by_cases hxh : x = hi
      · rw [if_pos hxh]; exact h2 i (by omega) (Nat.le_refl _) (by omega)
      · rw [if_neg hxh]; exact h2 x hx (by omega) (by omega)

/-- **`qpartition` at `lo < hi`** permutes `[lo, hi]` round a pivot that lands at `m < hi`. -/
theorem qpartition_spec {n lo hi : Nat} (as : Vector Nat n) (hlh : lo < hi) (hhi : hi < n) :
    ∀ r, Array.qpartition as (fun a b : Nat => decide (a < b)) lo hi (by omega) (by omega) hhi = r →
    Keeps lo hi as r.2 ∧ r.1.1 < hi ∧
      (∀ x (h : x < n) (hm : r.1.1 < n), lo ≤ x → x < r.1.1 → r.2[x] < r.2[r.1.1]) ∧
      (∀ x (h : x < n) (hm : r.1.1 < n), r.1.1 < x → x ≤ hi → ¬ r.2[x] < r.2[r.1.1]) := by
  intro r hr
  unfold Array.qpartition at hr
  dsimp only at hr
  have hm : (lo + hi) / 2 < hi := by omega
  have hmn : (lo + hi) / 2 < n := by omega
  have hln : lo < n := by omega
  generalize hA1 : (if decide (as[(lo + hi) / 2] < as[lo]) = true then as.swap lo ((lo + hi) / 2) hln hmn
    else as) = A1 at hr
  generalize hA2 : (if decide (A1[hi] < A1[lo]) = true then A1.swap lo hi hln hhi else A1) = A2 at hr
  generalize hA3 : (if decide (A2[(lo + hi) / 2] < A2[hi]) = true then A2.swap ((lo + hi) / 2) hi hmn hhi
    else A2) = A3 at hr
  have k1 : Keeps lo hi as A1 := by
    rw [← hA1]; exact Keeps.cswap _ as _ _ (Nat.le_refl _) (by omega) (by omega) (by omega)
  have k2 : Keeps lo hi A1 A2 := by
    rw [← hA2]; exact Keeps.cswap _ A1 _ _ (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)
  have k3 : Keeps lo hi A2 A3 := by
    rw [← hA3]; exact Keeps.cswap _ A2 _ _ (by omega) (by omega) (by omega) (Nat.le_refl _)
  have hmid : ¬ A3[(lo + hi) / 2] < A3[hi] := by
    rw [← hA3]
    split
    · next hc =>
      rw [Vector.getElem_swap, Vector.getElem_swap, if_pos rfl, if_neg (by omega), if_pos rfl]
      simp at hc; omega
    · next hc => simpa using hc
  obtain ⟨l1, l2, l3, l4⟩ := loop_spec hhi A3[hi] _ A3 lo lo (Nat.le_refl _) (Nat.le_refl _) (by omega) rfl
    (fun x _ a b => by omega) (fun x _ a b => by omega) rfl (Or.inr ⟨_, _, by omega, hm, hmid⟩) r hr
  exact ⟨(k1.trans k2).trans (k3.trans l1), l2, l3, l4⟩

/-- **`qsort`'s recursion sorts `[lo, hi]`**, permuting only there. -/
theorem sort_spec {n : Nat} : ∀ (d : Nat) (as : Vector Nat n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n)
    (hhi : hi < n), hi - lo = d →
    ∀ r, (qsort_priv% Array.qsort.sort) (fun a b : Nat => decide (a < b)) as lo hi w hlo hhi = r →
    Keeps lo hi as r ∧ ∀ x y (hx : x < n) (hy : y < n), lo ≤ x → x ≤ y → y ≤ hi → r[x] ≤ r[y] := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro as lo hi w hlo hhi hd r hr
  rw [qsort_unfold% Array.qsort.sort] at hr
  split at hr
  next hlt =>
    generalize hq : Array.qpartition as (fun a b : Nat => decide (a < b)) lo hi _ _ _ = q at hr
    have hs := qpartition_spec as hlt hhi q hq
    obtain ⟨⟨mid, hmid⟩, as1⟩ := q
    dsimp only at hr hs
    obtain ⟨p1, p2, p3, p4⟩ := hs
    split at hr
    next h2 => omega
    next h2 =>
      have hmn : mid < n := by omega
      obtain ⟨k1, o1⟩ := ih (mid - lo) (by omega) as1 lo mid (by omega) hlo hmn rfl _ rfl
      obtain ⟨k2, o2⟩ := ih (hi - (mid + 1)) (by omega) _ (mid + 1) hi (by omega) (by omega) hhi rfl r hr
      refine ⟨p1.trans ((k1.widen (Nat.le_refl _) (by omega)).trans (k2.widen (by omega) (Nat.le_refl _))), ?_⟩
      intro x y hx hy a b c
      by_cases hy' : y ≤ mid
      · rw [k2.2.1 x hx (by omega), k2.2.1 y hy (by omega)]; exact o1 x y hx hy a b hy'
      by_cases hx' : mid + 1 ≤ x
      · exact o2 x y hx hy hx' b c
      have l : r[x] ≤ as1[mid] := by
        rw [k2.2.1 x hx (by omega)]
        refine k1.2.2 (· ≤ as1[mid]) (fun z hz a1 a2 => ?_) x hx a (by omega)
        by_cases hzm : z = mid
        · subst hzm; exact Nat.le_refl _
        · exact Nat.le_of_lt (p3 z hz hmn a1 (by omega))
      have u : as1[mid] ≤ r[y] := by
        refine k2.2.2 (as1[mid] ≤ ·) (fun z hz a1 a2 => ?_) y hy (by omega) c
        rw [k1.2.1 z hz (by omega)]
        exact Nat.le_of_not_lt (p4 z hz hmn (by omega) a2)
      omega
  next hlt =>
    subst hr
    exact ⟨Keeps.refl as, fun x y hx hy a b c => by
      have : x = y := by omega
      subst this; exact Nat.le_refl _⟩

/-- **`Array.qsort` on naturals by `<` sorts**: its answer is a permutation of the input, in ascending order. -/
theorem qsort_nat (xs : Array Nat) :
    (xs.qsort (· < ·)).toList.Perm xs.toList ∧ (xs.qsort (· < ·)).toList.Pairwise (· ≤ ·) := by
  unfold Array.qsort
  split
  next h =>
    have : xs.toList = [] := by simpa [← Array.length_toList] using h
    simp [this]
  next h =>
    dsimp only
    generalize hr : (qsort_priv% Array.qsort.sort) (fun a b : Nat => decide (a < b)) xs.toVector _ _ _ _ _ = r
    obtain ⟨k, o⟩ := sort_spec _ _ _ _ _ _ _ rfl r hr
    refine ⟨?_, ?_⟩
    · have := Vector.perm_iff_toList_perm.1 k.1
      simpa using this
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simp only [Array.length_toList, Vector.size_toArray] at hi hj
      simp only [Array.getElem_toList, Vector.getElem_toArray]
      exact o i j hi hj (by omega) (by omega) (by omega)

/-- **A map's keys sorted by `qsort`** (as `ofRuns` sorts its run starts) are its keys, each once, ascending. -/
theorem ofRuns_keys (span : Std.HashMap Nat Nat) :
    ((span.toArray.map (·.1)).qsort (· < ·)).toList.Nodup ∧
    (∀ a, a ∈ ((span.toArray.map (·.1)).qsort (· < ·)).toList ↔ a ∈ span) ∧
    ((span.toArray.map (·.1)).qsort (· < ·)).toList.Pairwise (· < ·) := by
  obtain ⟨hp, hs⟩ := qsort_nat (span.toArray.map (·.1))
  have hk : (span.toArray.map (·.1)).toList = span.keys := by
    rw [Array.toList_map, Std.HashMap.toList_toArray, Std.HashMap.map_fst_toList_eq_keys]
  rw [hk] at hp
  have hn : ((span.toArray.map (·.1)).qsort (· < ·)).toList.Nodup := hp.nodup_iff.2 Std.HashMap.nodup_keys
  refine ⟨hn, fun a => by rw [hp.mem_iff, Std.HashMap.mem_keys], ?_⟩
  exact (hs.and hn).imp fun ⟨h1, h2⟩ => Nat.lt_of_le_of_ne h1 h2

/-- **`ofRuns`' bounds fold**: over distinct run starts `K`, each start `a` gets a group `g` (`ix'[a]`) whose
    bounds are `a` and its end `e a`; the bounds already laid down stay, and other keys of `ix` are untouched.
    `step` is the kernel's fold step, stated by its equation so a use site proves it by `rfl`. -/
theorem ofRuns_bounds {e : Nat → Nat} {step : Array Nat × Std.HashMap Nat Nat → Nat → Array Nat × Std.HashMap Nat Nat}
    (hstep : ∀ B ix a, step (B, ix) a =
      (let B' := if B.back? == some a then B else B.push a; (B'.push (e a), ix.insert a (B'.size - 1)))) :
    ∀ (K : List Nat) (B : Array Nat) (ix : Std.HashMap Nat Nat), K.Nodup → 0 < B.size →
    (∀ a ∈ K, ∃ g, (K.foldl step (B, ix)).2[a]? = some g ∧ (K.foldl step (B, ix)).1[g]? = some a ∧
      (K.foldl step (B, ix)).1[g + 1]? = some (e a)) ∧
    (∀ a, a ∉ K → (K.foldl step (B, ix)).2[a]? = ix[a]?) ∧
    (∀ (g x : Nat), B[g]? = some x → (K.foldl step (B, ix)).1[g]? = some x) ∧ 0 < (K.foldl step (B, ix)).1.size := by
  intro K
  induction K with
  | nil => intro B ix _ hB; simp [hB]
  | cons a K ih =>
    intro B ix hnd hB
    obtain ⟨haK, hnd'⟩ := List.nodup_cons.1 hnd
    simp only [List.foldl_cons, hstep]
    generalize hB1 : (if B.back? == some a then B else B.push a) = B1
    have h1 : 0 < B1.size ∧ B1[B1.size - 1]? = some a ∧ ∀ (g x : Nat), B[g]? = some x → B1[g]? = some x := by
      rw [← hB1]; split
      · next h => refine ⟨hB, ?_, fun _ _ h => h⟩; rw [← Array.back?_eq_getElem?]; simpa using h
      · exact ⟨by simp, by simp, fun g x h => by
          rw [Array.getElem?_push]; split
          · next he => subst he; simp at h
          · exact h⟩
    obtain ⟨r1, r2, r3, r4⟩ := ih (B1.push (e a)) (ix.insert a (B1.size - 1)) hnd' (by simp)
    have hp : ∀ (g x : Nat), B1[g]? = some x → (B1.push (e a))[g]? = some x := fun g x h => by
      rw [Array.getElem?_push]; split
      · next he => subst he; simp at h
      · exact h
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun g x h => r3 g x (hp g x (h1.2.2 g x h)), r4⟩
    · rcases List.mem_cons.1 hb with rfl | hb
      · refine ⟨B1.size - 1, ?_, r3 _ _ (hp _ _ h1.2.1), ?_⟩
        · rw [r2 b haK, Std.HashMap.getElem?_insert]; simp
        · apply r3; rw [Array.getElem?_push, if_pos (by omega)]
      · exact r1 b hb
    · have hne : a ≠ b := fun h => hb (h ▸ List.mem_cons_self ..)
      rw [r2 b (fun h => hb (List.mem_cons_of_mem _ h)), Std.HashMap.getElem?_insert]
      simp [hne]

/-- **`ofRuns`' span fold**: inserting each needle's run `a ↦ z` maps every start to its run's end, where needles
    that share a start share the end; a start no needle names keeps what `m` had. `step` is the kernel's step
    (on needles below `N`), stated by its equation. -/
theorem ofRuns_span {run : Nat → Option (Nat × Nat)} {N : Nat} {step : Std.HashMap Nat Nat → Nat → Std.HashMap Nat Nat}
    (hstep : ∀ m k, k < N → step m k = match run k with | some (a, z) => m.insert a z | none => m)
    (hcons : ∀ k k' a z z', k < N → k' < N → run k = some (a, z) → run k' = some (a, z') → z = z') :
    ∀ M, M ≤ N → ∀ m : Std.HashMap Nat Nat,
    (∀ k, k < M → ∀ a z, run k = some (a, z) → ((List.range M).foldl step m)[a]? = some z) ∧
    (∀ a, (∀ k, k < M → ∀ z, run k ≠ some (a, z)) → ((List.range M).foldl step m)[a]? = m[a]?) := by
  intro M
  induction M with
  | zero => intro _ m; simp
  | succ M ih =>
    intro hM m
    obtain ⟨i1, i2⟩ := ih (by omega) m
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hstep _ M (by omega)]
    generalize hF : (List.range M).foldl step m = F at i1 i2
    refine ⟨fun k hk a z hr => ?_, fun a ha => ?_⟩
    · rcases hrM : run M with _ | ⟨a', z'⟩
      · have hkM : k ≠ M := fun e => by subst e; rw [hr] at hrM; cases hrM
        simp only; exact i1 k (by omega) a z hr
      · simp only
        rw [Std.HashMap.getElem?_insert]
        by_cases hkM : k = M
        · subst hkM; rw [hr] at hrM; cases hrM; simp
        · by_cases ha : a' = a
          · subst ha; rw [if_pos (by simp), hcons M k a' z' z (by omega) (by omega) hrM hr]
          · rw [if_neg (by simpa using ha)]; exact i1 k (by omega) a z hr
    · have h2 := i2 a fun k hk z => ha k (by omega) z
      rcases hrM : run M with _ | ⟨a', z'⟩
      · exact h2
      · simp only
        rw [Std.HashMap.getElem?_insert, if_neg (by
          simp only [beq_iff_eq]; rintro rfl; exact ha M (by omega) z' hrM)]
        exact h2

/-- **`ofRuns`' bounds fold stays under `N`** when its bounds and its starts and their ends do, and lays down at
    most two bounds per start. -/
theorem ofRuns_bounds_le {e : Nat → Nat} {step : Array Nat × Std.HashMap Nat Nat → Nat → Array Nat × Std.HashMap Nat Nat}
    (hstep : ∀ B ix a, step (B, ix) a =
      (let B' := if B.back? == some a then B else B.push a; (B'.push (e a), ix.insert a (B'.size - 1)))) (N : Nat) :
    ∀ (K : List Nat) (B : Array Nat) (ix : Std.HashMap Nat Nat), (∀ x ∈ B.toList, x ≤ N) → (∀ a ∈ K, a ≤ N ∧ e a ≤ N) →
    (∀ x ∈ (K.foldl step (B, ix)).1.toList, x ≤ N) ∧ (K.foldl step (B, ix)).1.size ≤ B.size + 2 * K.length := by
  intro K
  induction K with
  | nil => intro B ix hB _; simpa using hB
  | cons a K ih =>
    intro B ix hB hK
    simp only [List.foldl_cons, hstep]
    have ha := hK a List.mem_cons_self
    generalize hB1 : (if B.back? == some a then B else B.push a) = B1
    have h1 : (∀ x ∈ B1.toList, x ≤ N) ∧ B1.size ≤ B.size + 1 := by
      rw [← hB1]; split
      · exact ⟨hB, by omega⟩
      · refine ⟨fun x hx => ?_, by simp⟩
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hB x hx
        · exact ha.1
    obtain ⟨r1, r2⟩ := ih (B1.push (e a)) (ix.insert a (B1.size - 1)) (fun x hx => by
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h1.1 x hx
      · exact ha.2) (fun b hb => hK b (List.mem_cons_of_mem _ hb))
    refine ⟨r1, ?_⟩
    simp only [List.length_cons, Array.size_push] at r2 ⊢
    omega

#print axioms qsort_nat
#print axioms ofRuns_keys
#print axioms ofRuns_bounds
#print axioms ofRuns_span
#print axioms ofRuns_bounds_le

end LeetQ.Rel.QSort
