/-
  LeetCode 1 — Two Sum, derived from its specification.

  Spec (entire, B&dM style): `twoSumO(t) ≜ orNone(twoSum(t)) : [Int] ⟶ 1 + Nat×Nat`,
  `twoSum(t) ≜ zipIdx(0) pairs(t)`, `pairs(t) ≜ ⟪∋,∋⟫ (j<k)? ans(t)`, `ans(t) ≜ (a+b=t)? (π₂×π₂)`.

  Program: `go(t) ≜ ⦇[const none, step(t)]⦈` over `[Int]`, a function of the offset `n` and the map
  `m`; `zipIdx` fuses into it because `zipIdx(x::xs, n) = (x,n) :: zipIdx(xs, n+1)`.

  Derivation (diagram order):
      graph(prog(t)) = graph(go(t)) at₀ ⊑ scan(t) at₀ ⊑ orNone(hits(t,0,∅)) = orNone(twoSum(t))
  with `hits(t,n,m) ≜ zipIdx(n) (pairs(t) ∪ ∋ found(t,m))`: a pair inside the rest, or a member of
  the rest whose complement `m` already holds.  The fold premise is `[scan_nil, scan_cons]`; on a
  miss `hits_insert_le` gives `⊑` and `hits_cons_dom` the domain.

  Mathlib-free.  `Classical.choice` enters only through core's `Std.HashMap` lemmas in `look_insert`.
-/
import AOP.A6_GenFold
import AOP.A6_2
import Std.Data.HashMap

namespace Freyd.Alg.RelSet.LC1

open Freyd CL DistributiveAllegory

/-- Keys, indices, indexed members `(a,j)`, lists, pairs of members, answers `(j,k)`, hash maps,
    scans (answers as a function of offset and map) and their offset/map/answer triples. -/
abbrev Key : RelSet.{0} := ⟨Int⟩
abbrev Idx : RelSet.{0} := ⟨Nat⟩
abbrev E : RelSet.{0} := ⟨Int × Nat⟩
abbrev LI : RelSet.{0} := ⟨List Int⟩
abbrev IL : RelSet.{0} := ⟨List (Int × Nat)⟩
abbrev E2 : RelSet.{0} := ⟨(Int × Nat) × (Int × Nat)⟩
abbrev Ans : RelSet.{0} := ⟨Nat × Nat⟩
abbrev Opt : RelSet.{0} := ⟨Option (Nat × Nat)⟩
abbrev HM := Std.HashMap Int Nat
abbrev Scan : RelSet.{0} := ⟨Nat → HM → Option (Nat × Nat)⟩
abbrev Ev : RelSet.{0} := ⟨(Nat × HM) × Option (Nat × Nat)⟩

/-- `∋ : [E] ⟶ E`, core's list membership (the repo's other `∋` is the power allegory's, on `P(A)`). -/
local notation (priority := high) "∋" => (Membership.mem : IL ⟶ E)
/-- `κe ≜ graph(const e)`, the constant member. -/
local notation (priority := high) "κ" c:max => (graph fun _ => c : _ ⟶ E)

/-! ## The specification -/

def zipIdxR (n : Nat) : LI ⟶ IL := graph (List.zipIdx · n)

/-- `(j<k)?`: the first member's index is below the second's. -/
def before : E2 ⟶ E2 := corefl fun ((_, j), (_, k)) => j < k

/-- `ans(t) ≜ (a+b=t)? (π₂×π₂)`: a pair of members summing to `t`, answered by its indices. -/
def ans (t : Int) : E2 ⟶ Ans := corefl (fun ((a, _), (b, _)) => a + b = t) ≫ graph fun ((_, j), (_, k)) => (j, k)

/-- `pairs(t) ≜ ⟪∋,∋⟫ (j<k)? ans(t)`: two members taken independently, in index order, summing to `t`. -/
def pairs (t : Int) : IL ⟶ Ans := ⟪∋, ∋⟫ ≫ before ≫ ans t

/-- `twoSum(t) ≜ zipIdx(0) pairs(t)`. -/
def twoSum (t : Int) : LI ⟶ Ans := zipIdxR 0 ≫ pairs t

/-- `twoSumO(t) ≜ orNone(twoSum(t))`. -/
def twoSumO (t : Int) : LI ⟶ Opt := orNone (twoSum t)

/-! ## The program: one fold over the list, threading offset and map -/

/-- The step at `x`, given the scan `r` of the rest: the lookup `m[t-x]? : 1 + Nat` is consumed by
    the copair `[r(n+1, insert(x,n)(m)), j ↦ some(j,n)]`. -/
def step (t x : Int) (r : Nat → HM → Option (Nat × Nat)) (n : Nat) (m : HM) : Option (Nat × Nat) :=
  (m[t - x]?).elim (r (n + 1) (m.insert x n)) fun j => some (j, n)

/-- `go(t) ≜ ⦇[const none, step(t)]⦈`; a hit stops the scan. -/
def go (t : Int) : List Int → Nat → HM → Option (Nat × Nat) := List.foldr (step t) fun _ _ => none

def prog (t : Int) (xs : List Int) : Option (Nat × Nat) := go t xs 0 {}

/-- `at₀ : f ↦ f(0,∅)`, a scan run from offset `0` and the empty map. -/
def at₀ : Scan ⟶ Opt := graph fun f => f 0 {}

/-! ## The boundary facts (pointwise) -/

/-- `look(m) : Int ⟶ Nat`, the finite relation the map denotes. -/
def look (m : HM) : Key ⟶ Idx := fun a j => m[a]? = some j

/-- `(x↦n) ≜ (=x)? n`, the one-entry relation. -/
def single (x : Int) (n : Nat) : Key ⟶ Idx := corefl (· = x) ≫ graph fun _ => n

theorem look_empty : look {} = 𝟘 := hom_ext fun a j => ⟨fun h => by simp [look] at h, fun h => (h : False).elim⟩

/-- `look(insert(x,n)(m)) = (x↦n) ∪ (≠x)? look(m)`: insertion overrides the key `x`. -/
theorem look_insert (m : HM) (x : Int) (n : Nat) : look (m.insert x n) = single x n ∪ corefl (· ≠ x) ≫ look m :=
  hom_ext fun a j => by
    by_cases h : x = a
    · subst h; simp [look, single, corefl, graph, eq_comm]
    · simp [look, single, corefl, graph, Std.HashMap.getElem?_insert, h, Ne.symm h]

theorem look_insert_le (m : HM) (x : Int) (n : Nat) : look (m.insert x n) ⊑ single x n ∪ look m := by
  rw [look_insert]; exact union_mono (le_refl _) (le_iff.mpr fun _ _ ⟨_, ⟨rfl, _⟩, h⟩ => h)

theorem single_le_insert (m : HM) (x : Int) (n : Nat) : single x n ⊑ look (m.insert x n) := by
  rw [look_insert]; exact le_union_left _ _

/-- `look(m) ⊑ look(insert(x,n)(m)) ⊤`: the override keeps every key. -/
theorem look_keys (m : HM) (x : Int) (n : Nat) : look m ⊑ look (m.insert x n) ≫ relTop Idx Idx :=
  le_iff.mpr fun a j (h : m[a]? = some j) => by
    by_cases hx : x = a
    · subst hx; exact ⟨n, by simp [look], trivial⟩
    · exact ⟨j, by simp [look, Std.HashMap.getElem?_insert, hx, h], trivial⟩

theorem mem_nil : (graph fun _ => ([] : List (Int × Nat)) : dL Unit ⟶ IL) ≫ ∋ = 𝟘 :=
  hom_ext fun _ _ => ⟨fun ⟨_, h, hm⟩ => (by subst h; nomatch hm), fun h => (h : False).elim⟩

theorem mem_cons (e : Int × Nat) : (graph (List.cons e) : IL ⟶ IL) ≫ ∋ = κ e ∪ ∋ :=
  hom_ext fun _ _ => ⟨fun ⟨_, h, hm⟩ => List.mem_cons.mp (h ▸ hm), fun h => ⟨_, rfl, List.mem_cons.mpr h⟩⟩

theorem zipIdx_cons (x : Int) (n : Nat) :
    (graph (List.cons x) : LI ⟶ LI) ≫ zipIdxR n = zipIdxR (n + 1) ≫ (graph (List.cons (x, n)) : IL ⟶ IL) := by
  rw [zipIdxR, zipIdxR, graph_comp, graph_comp]; rfl

/-- `zipIdx(n+1) ⟪κ(x,n),∋⟫ (j<k)? = zipIdx(n+1) ⟪κ(x,n),∋⟫`: every later index exceeds `n`. -/
theorem zipIdx_before {B : RelSet.{0}} (x : Int) (n : Nat) (Y : E2 ⟶ B) :
    zipIdxR (n + 1) ≫ ⟪κ(x, n), ∋⟫ ≫ before ≫ Y = zipIdxR (n + 1) ≫ ⟪κ(x, n), ∋⟫ ≫ Y := by
  have h : (zipIdxR (n + 1) ≫ ⟪κ(x, n), ∋⟫) ≫ before = zipIdxR (n + 1) ≫ ⟪κ(x, n), ∋⟫ :=
    hom_ext fun xs ⟨⟨a, j⟩, ⟨b, k⟩⟩ => ⟨fun ⟨_, hq, hb, _⟩ => hb ▸ hq,
      fun ⟨L, hL, ⟨h1, h2⟩⟩ => ⟨_, ⟨L, hL, ⟨h1, h2⟩⟩, rfl, by cases h1; subst hL; exact (List.mem_zipIdx h2).1⟩⟩
  simpa only [Cat.assoc] using congrArg (· ≫ Y) h

/-- `zipIdx(n+1) ⟪∋,κ(x,n)⟫ (j<k)? = 𝟘`: no later index is below `n`. -/
theorem zipIdx_before' {B : RelSet.{0}} (x : Int) (n : Nat) (Y : E2 ⟶ B) :
    zipIdxR (n + 1) ≫ ⟪∋, κ(x, n)⟫ ≫ before ≫ Y = 𝟘 := by
  have h : (zipIdxR (n + 1) ≫ ⟪∋, κ(x, n)⟫) ≫ before = 𝟘 :=
    hom_ext fun xs _ => ⟨fun ⟨⟨⟨a', j'⟩, ⟨b', k'⟩⟩, ⟨L, hL, ⟨h1, h2⟩⟩, _, hlt⟩ => by
        cases h2; subst hL; exact absurd hlt (Nat.not_lt.mpr (Nat.le_of_succ_le (List.mem_zipIdx h1).1)),
      fun h => (h : False).elim⟩
  simpa only [Cat.assoc, zero_comp] using congrArg (· ≫ Y) h

/-- `⟪κe,κe⟫ (j<k)? = 𝟘`: a member is not before itself. -/
theorem before_const {B : RelSet.{0}} (x : Int) (n : Nat) (Y : E2 ⟶ B) :
    (⟪κ(x, n), κ(x, n)⟫ : IL ⟶ E2) ≫ before ≫ Y = 𝟘 := by
  have h : (⟪κ(x, n), κ(x, n)⟫ : IL ⟶ E2) ≫ before = 𝟘 :=
    hom_ext fun _ _ => ⟨fun ⟨⟨_, _⟩, ⟨h1, h2⟩, _, hlt⟩ => (by cases h1; cases h2; exact Nat.lt_irrefl _ hlt),
      fun h => (h : False).elim⟩
  simpa only [← Cat.assoc, zero_comp] using congrArg (· ≫ Y) h

/-! ## Hits -/

/-- `found(t,M) ≜ ⟪(t−π₁) M, π₂⟫`: `(b,k) ↦ (j,k)` when `t-b ↦ j` in `M`. -/
def found (t : Int) (M : Key ⟶ Idx) : E ⟶ Ans :=
  ⟪graph (fun p : Int × Nat => t - p.1) ≫ M, (graph Prod.snd : E ⟶ Idx)⟫

/-- `hits(t,n,m) ≜ zipIdx(n) (pairs(t) ∪ ∋ found(t,m))`. -/
def hits (t : Int) (n : Nat) (m : HM) : LI ⟶ Ans := zipIdxR n ≫ (pairs t ∪ ∋ ≫ found t (look m))

theorem found_union (t : Int) (M M' : Key ⟶ Idx) : found t (M ∪ M') = found t M ∪ found t M' := by
  rw [found, found, found, comp_union_distrib, rpair_union_left]

theorem found_mono (t : Int) {M M' : Key ⟶ Idx} (h : M ⊑ M') : found t M ⊑ found t M' :=
  rpair_mono (comp_mono_left _ h) (le_refl _)

theorem found_top (t : Int) (M : Key ⟶ Idx) : found t (M ≫ relTop Idx Idx) ⊑ found t M ≫ relTop Ans Ans := by
  rw [found, found, ← Cat.assoc]; exact rpair_top _ _

/-- `⟪κ(x,n),∋⟫ ans(t) = ∋ found(t, x↦n)`: `(x,n)` paired with a later member is found through `x↦n`. -/
theorem const_pairs (t x : Int) (n : Nat) : (⟪κ(x, n), ∋⟫ ≫ ans t : IL ⟶ Ans) = ∋ ≫ found t (single x n) :=
  hom_ext fun L ⟨j, k⟩ => by
    constructor
    · rintro ⟨⟨⟨a, j'⟩, ⟨b, k'⟩⟩, ⟨h1, h2⟩, _, ⟨rfl, hs⟩, h3⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
      exact ⟨_, h2, ⟨_, rfl, _, ⟨rfl, by simp only at hs ⊢; omega⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨b, k'⟩, hb, ⟨_, rfl, _, ⟨rfl, hx⟩, rfl⟩, rfl⟩
      exact ⟨(_, _), ⟨rfl, hb⟩, _, ⟨rfl, by simp only at hx ⊢; omega⟩, rfl⟩

/-- A miss: `t-x ∉ dom(m)` finds nothing for `(x,n)`. -/
theorem found_miss {t x : Int} {m : HM} (n : Nat) (hm : m[t - x]? = none) :
    (κ(x, n) : IL ⟶ E) ≫ found t (look m) = 𝟘 :=
  hom_ext fun _ _ => ⟨fun ⟨_, h, ⟨_, ha, hj⟩, _⟩ => (by subst h ha; exact nomatch hm.symm.trans hj),
    fun h => (h : False).elim⟩

theorem hits_empty (t : Int) : hits t 0 {} = twoSum t := by
  rw [hits, look_empty, found, comp_zero, rpair_zero_left, comp_zero, union_zero]; rfl

theorem nil_hits (t : Int) (n : Nat) (m : HM) : (graph fun _ => ([] : List Int) : dL Unit ⟶ LI) ≫ hits t n m = 𝟘 :=
  calc _ = (graph fun _ => ([] : List (Int × Nat)) : dL Unit ⟶ IL) ≫ (pairs t ∪ ∋ ≫ found t (look m)) := by
          rw [hits, ← Cat.assoc, zipIdxR, graph_comp]; rfl
    _ = 𝟘 := by
        simp only [comp_union_distrib, pairs, ← Cat.assoc, graph_rpair]; rw [mem_nil]
        simp only [rpair_zero_left, zero_comp, union_zero]

/-- `hits(t,n+1,insert(x,n)(m)) ⊑ cons(x) hits(t,n,m)`: a later hit is a hit one member earlier. -/
theorem hits_insert_le (t : Int) (n : Nat) (m : HM) (x : Int) :
    hits t (n + 1) (m.insert x n) ⊑ (graph (List.cons x) : LI ⟶ LI) ≫ hits t n m :=
  calc hits t (n + 1) (m.insert x n)
      ⊑ zipIdxR (n + 1) ≫ (pairs t ∪ ∋ ≫ found t (single x n ∪ look m)) :=
        comp_mono_left _ (union_mono (le_refl _) (comp_mono_left _ (found_mono t (look_insert_le m x n))))
    _ = zipIdxR (n + 1) ≫ (pairs t ∪ (⟪κ(x, n), ∋⟫ ≫ before ≫ ans t ∪ ∋ ≫ found t (look m))) := by
        rw [found_union]; simp only [comp_union_distrib]; rw [zipIdx_before, const_pairs]
    _ ⊑ zipIdxR (n + 1) ≫ (⟪κ(x, n) ∪ ∋, κ(x, n) ∪ ∋⟫ ≫ before ≫ ans t ∪ (κ(x, n) ∪ ∋) ≫ found t (look m)) :=
        comp_mono_left _ (union_lub
          (le_trans (comp_mono_right (rpair_mono (le_union_right _ _) (le_union_right _ _)) _) (le_union_left _ _))
          (union_lub
            (le_trans (comp_mono_right (rpair_mono (le_union_left _ _) (le_union_right _ _)) _) (le_union_left _ _))
            (le_trans (comp_mono_right (le_union_right _ _) _) (le_union_right _ _))))
    _ = zipIdxR (n + 1) ≫ (graph (List.cons (x, n)) : IL ⟶ IL) ≫ (pairs t ∪ ∋ ≫ found t (look m)) := by
        rw [comp_union_distrib (graph _), pairs, ← Cat.assoc (graph _) ⟪∋, ∋⟫, ← Cat.assoc (graph _) ∋,
          graph_rpair, mem_cons]
    _ = (graph (List.cons x) : LI ⟶ LI) ≫ hits t n m := by rw [← Cat.assoc, ← zipIdx_cons, Cat.assoc]; rfl

/-- `cons(x) hits(t,n,m) ⊑ hits(t,n+1,insert(x,n)(m)) ⊤` on a miss: the head finds nothing, a later
    hit keeps its key. -/
theorem hits_cons_dom (t : Int) (n : Nat) (m : HM) (x : Int) (hm : m[t - x]? = none) :
    (graph (List.cons x) : LI ⟶ LI) ≫ hits t n m ⊑ hits t (n + 1) (m.insert x n) ≫ relTop Ans Ans :=
  calc (graph (List.cons x) : LI ⟶ LI) ≫ hits t n m
      = zipIdxR (n + 1) ≫ (graph (List.cons (x, n)) : IL ⟶ IL) ≫ (pairs t ∪ ∋ ≫ found t (look m)) := by
        rw [hits, ← Cat.assoc, zipIdx_cons, Cat.assoc]
    _ = zipIdxR (n + 1) ≫ (⟪κ(x, n), ∋⟫ ≫ ans t ∪ pairs t ∪ ∋ ≫ found t (look m)) := by
        rw [comp_union_distrib (graph _), pairs, ← Cat.assoc (graph _) ⟪∋, ∋⟫, ← Cat.assoc (graph _) ∋,
          graph_rpair, mem_cons]
        simp only [rpair_union_left, rpair_union_right, union_comp_distrib, comp_union_distrib, before_const,
          found_miss n hm, zero_union]
        rw [zipIdx_before', zipIdx_before, zero_union]
    _ ⊑ zipIdxR (n + 1) ≫ (pairs t ∪ ∋ ≫ found t (look (m.insert x n))) ≫ relTop Ans Ans := by
        refine comp_mono_left _ (union_lub (union_lub ?_ (le_trans (le_union_left _ _) (le_comp_top _))) ?_)
        · rw [const_pairs]
          exact le_trans (comp_mono_left _ (found_mono t (single_le_insert m x n)))
            (le_trans (le_union_right _ _) (le_comp_top _))
        · calc ∋ ≫ found t (look m)
              ⊑ ∋ ≫ found t (look (m.insert x n)) ≫ relTop Ans Ans :=
                comp_mono_left _ (le_trans (found_mono t (look_keys m x n)) (found_top t _))
            _ ⊑ (pairs t ∪ ∋ ≫ found t (look (m.insert x n))) ≫ relTop Ans Ans := by
                rw [← Cat.assoc]; exact comp_mono_right (le_union_right _ _) _
    _ = hits t (n + 1) (m.insert x n) ≫ relTop Ans Ans := (Cat.assoc _ _ _).symm

/-! ## The fold -/

/-- `ev : f ↦ ((n,m), f(n,m))`, a scan as the set of its offset/map/answer triples. -/
def ev : Scan ⟶ Ev := fun f ((n, m), o) => f n m = o

/-- `scanSpec(t) : xs ↦ ((n,m), o)` when `o` is `orNone(hits(t,n,m))` of `xs`. -/
def scanSpec (t : Int) : LI ⟶ Ev := fun xs ((n, m), o) => orNone (hits t n m) xs o

/-- `scan(t) ≜ scanSpec(t) / ev`: the scans whose every triple `scanSpec(t)` allows. -/
def scan (t : Int) : LI ⟶ Scan := scanSpec t / ev

/-- The `[]` arm: `const none ⊑ nil scan(t)`, since `nil hits = 𝟘`. -/
theorem scan_nil (t : Int) :
    (graph fun _ => fun _ _ => none : dL Unit ⟶ Scan) ⊑ (graph fun _ => ([] : List Int) : dL Unit ⟶ LI) ≫ scan t :=
  le_iff.mpr fun _ f (hf : f = _) => ⟨[], rfl, fun ⟨⟨n, m⟩, o⟩ ho => by
    have ho : f n m = o := ho
    subst hf ho
    have h : ((graph fun _ => ([] : List Int) : dL Unit ⟶ LI) ≫ orNone (hits t n m)) () none := by
      rw [graph_orNone, nil_hits, orNone_zero]; rfl
    obtain ⟨_, rfl, h⟩ := h
    exact h⟩

/-- The `x :: xs` arm: `(𝟙×scan(t)) step(t) ⊑ cons scan(t)`.  A lookup hit is the head's answer,
    a miss is `orNone_mono` over `hits_insert_le`/`hits_cons_dom`. -/
theorem scan_cons (t : Int) :
    rprodMap (𝟙 (dE Int)) (scan t) ≫ graph (fun p : Int × Scan.carrier => step t p.1 p.2)
      ⊑ graph (fun p : Int × List Int => p.1 :: p.2) ≫ scan t := by
  refine le_iff.mpr fun ⟨x, xs⟩ f ⟨⟨x', r⟩, ⟨hx, hr⟩, hf⟩ => ⟨_, rfl, fun ⟨⟨n, m⟩, o⟩ ho => ?_⟩
  have ho : f n m = o := ho
  have hx : x = x' := hx
  have hf : f = step t x' r := hf
  subst hx hf ho
  show orNone (hits t n m) (x :: xs) (step t x r n m)
  cases hm : m[t - x]? with
  | some j =>
    rw [show step t x r n m = some (j, n) by simp only [step, hm, Option.elim]]
    exact Or.inl ⟨(j, n), ⟨_, rfl, Or.inr ⟨(x, n), List.mem_cons_self, ⟨_, rfl, hm⟩, rfl⟩⟩, rfl⟩
  | none =>
    rw [show step t x r n m = r (n + 1) (m.insert x n) by simp only [step, hm, Option.elim]]
    have h := le_iff.mp (orNone_mono (hits_insert_le t n m x) (hits_cons_dom t n m x hm)) xs _
      (hr ((n + 1, m.insert x n), _) rfl)
    rw [← graph_orNone] at h
    obtain ⟨_, rfl, h⟩ := h
    exact h

/-! ## The derivation -/

/-- **The program refines the entire spec**: `graph(prog(t)) ⊑ twoSumO(t)`. -/
theorem prog_le (t : Int) : (graph (prog t) : LI ⟶ Opt) ⊑ twoSumO t :=
  calc graph (prog t)
      = graph (go t) ≫ at₀ := by rw [at₀, graph_comp]; rfl
    _ ⊑ scan t ≫ at₀ := comp_mono_right (foldr_le _ _ (scan_nil t) (scan_cons t)) _
    _ ⊑ orNone (hits t 0 {}) := le_iff.mpr fun xs o ⟨f, hX, ho⟩ =>
        ho ▸ (hX ((0, {}), f 0 {}) rfl : orNone (hits t 0 {}) xs (f 0 {}))
    _ = twoSumO t := by rw [hits_empty]; rfl

#eval prog 9 [2, 7, 11, 15]   -- some (0, 1)
#eval prog 6 [3, 2, 4]        -- some (1, 2)
#eval prog 7 [1, 2, 3]        -- none

end Freyd.Alg.RelSet.LC1
