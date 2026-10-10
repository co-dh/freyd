/-
  LeetCode 1 — Two Sum. Spec: `twoSumO(t) ≜ orNone(zipIdx(0) pairs(t))`, `pairs(t) ≜ ⟪∋,∋⟫ (j<k)? ans(t)`.
  Derivation: `graph(prog(t)) = graph(go(t)) at₀ ⊑ scan(t) at₀ ⊑ orNone(hits(t,0,∅)) = twoSumO(t)`, with the fold
  premise `[scan_nil, scan_cons]`. Mathlib-free; `Classical.choice` enters only through core's `Std.HashMap` lemmas.
-/
import AOP.A6_GenFold
import Std.Data.HashMap

namespace Freyd.Alg.RelSet.LC1

open Freyd CL DistributiveAllegory

/-- Keys, indices, members `(a,j)`, lists, member pairs, answers `(j,k)`, maps, scans and their triples. -/
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

/-- The step at `x` given the rest's scan `r`: the copair `[r(n+1, insert(x,n)(m)), j ↦ some(j,n)]` on `m[t-x]?`. -/
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

/-- `look(m) ⊑ look(insert(x,n)(m)) ⊤`: the override keeps every key. -/
theorem look_keys (m : HM) (x : Int) (n : Nat) : look m ⊑ look (m.insert x n) ≫ relTop Idx Idx :=
  le_iff.mpr fun a j (h : m[a]? = some j) => by
    by_cases hx : x = a
    · subst hx; exact ⟨n, by simp [look], trivial⟩
    · exact ⟨j, by simp [look, Std.HashMap.getElem?_insert, hx, h], trivial⟩

/-- `κa look(m) = 𝟘` when `a ∉ dom(m)`. -/
theorem look_none {X : RelSet.{0}} {m : HM} {a : Int} (hm : m[a]? = none) : (graph fun _ => a : X ⟶ Key) ≫ look m = 𝟘 :=
  hom_ext fun _ _ => ⟨fun ⟨_, h, hj⟩ => (by subst h; exact nomatch hm.symm.trans hj), fun h => (h : False).elim⟩

theorem mem_nil : (graph fun _ => ([] : List (Int × Nat)) : dL Unit ⟶ IL) ≫ ∋ = 𝟘 :=
  hom_ext fun _ _ => ⟨fun ⟨_, h, hm⟩ => (by subst h; nomatch hm), fun h => (h : False).elim⟩

theorem mem_cons (e : Int × Nat) : (graph (List.cons e) : IL ⟶ IL) ≫ ∋ = κ e ∪ ∋ :=
  hom_ext fun _ _ => ⟨fun ⟨_, h, hm⟩ => List.mem_cons.mp (h ▸ hm), fun h => ⟨_, rfl, List.mem_cons.mpr h⟩⟩

theorem zipIdx_nil (n : Nat) : (graph fun _ => ([] : List Int) : dL Unit ⟶ LI) ≫ zipIdxR n = graph fun _ => [] := by
  rw [zipIdxR, graph_comp]; rfl

theorem zipIdx_cons (x : Int) (n : Nat) :
    (graph (List.cons x) : LI ⟶ LI) ≫ zipIdxR n = zipIdxR (n + 1) ≫ (graph (List.cons (x, n)) : IL ⟶ IL) := by
  rw [zipIdxR, zipIdxR, graph_comp, graph_comp]; rfl

/-- `cons(x) zipIdx(n) ⟪∋,∋⟫ (j<k)? = zipIdx(n+1) (⟪∋,∋⟫ (j<k)? ∪ ⟪κ(x,n),∋⟫)`: the head `(x,n)` is before every
    later member and after none. -/
theorem cons_before (x : Int) (n : Nat) : (graph (List.cons x) : LI ⟶ LI) ≫ zipIdxR n ≫ ⟪∋, ∋⟫ ≫ before
    = zipIdxR (n + 1) ≫ (⟪∋, ∋⟫ ≫ before ∪ ⟪κ(x, n), ∋⟫) :=
  hom_ext fun xs ⟨⟨a, j⟩, ⟨b, k⟩⟩ => by
    constructor
    · rintro ⟨_, rfl, _, rfl, _, ⟨h1, h2⟩, rfl, hlt⟩
      rcases List.mem_cons.mp h1 with h1 | h1 <;> rcases List.mem_cons.mp h2 with h2 | h2
      · cases h1; cases h2; exact absurd hlt (Nat.lt_irrefl _)
      · cases h1; exact ⟨_, rfl, Or.inr ⟨rfl, h2⟩⟩
      · cases h2; exact absurd hlt (Nat.not_lt.mpr (Nat.le_of_succ_le (List.mem_zipIdx h1).1))
      · exact ⟨_, rfl, Or.inl ⟨_, ⟨h1, h2⟩, rfl, hlt⟩⟩
    · rintro ⟨_, rfl, ⟨_, ⟨h1, h2⟩, rfl, hlt⟩ | ⟨h1, h2⟩⟩
      · exact ⟨_, rfl, _, rfl, _, ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩, rfl, hlt⟩
      · cases h1
        exact ⟨_, rfl, _, rfl, _, ⟨List.mem_cons_self, List.mem_cons_of_mem _ h2⟩, rfl, (List.mem_zipIdx h2).1⟩

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
    (κ(x, n) : IL ⟶ E) ≫ found t (look m) = 𝟘 := by
  rw [found, graph_rpair, ← Cat.assoc, graph_comp, look_none hm, rpair_zero_left]

theorem hits_empty (t : Int) : hits t 0 {} = twoSum t := by
  rw [hits, look_empty, found, comp_zero, rpair_zero_left, comp_zero, union_zero]; rfl

theorem nil_hits (t : Int) (n : Nat) (m : HM) : (graph fun _ => ([] : List Int) : dL Unit ⟶ LI) ≫ hits t n m = 𝟘 := by
  simp only [hits, pairs, ← Cat.assoc, zipIdx_nil, comp_union_distrib, graph_rpair]; rw [mem_nil]
  simp only [rpair_zero_left, zero_comp, union_zero]

/-- `cons(x) hits(t,n,m) = zipIdx(n+1) ((pairs(t) ∪ ∋ found(t, x↦n)) ∪ (κ(x,n)∪∋) found(t,m))`: the head `(x,n)`
    is the first member of a pair and the member of a find. -/
theorem cons_hits (t : Int) (n : Nat) (m : HM) (x : Int) : (graph (List.cons x) : LI ⟶ LI) ≫ hits t n m
    = zipIdxR (n + 1) ≫ ((pairs t ∪ ∋ ≫ found t (single x n)) ∪ (κ(x, n) ∪ ∋) ≫ found t (look m)) := by
  have hb := cons_before x n
  simp only [← Cat.assoc] at hb
  simp only [hits, pairs, comp_union_distrib, ← Cat.assoc]
  rw [hb, zipIdx_cons, Cat.assoc (zipIdxR _) (graph _), mem_cons]
  simp only [Cat.assoc, union_comp_distrib, comp_union_distrib]; rw [const_pairs]

/-- On a miss, `cons(x) hits(t,n,m) = hits(t,n+1,insert(x,n)(m)) ∪ zipIdx(n+1) ∋ found(t,m)`. -/
theorem hits_cons_eq {t x : Int} {n : Nat} {m : HM} (hm : m[t - x]? = none) : (graph (List.cons x) : LI ⟶ LI) ≫
    hits t n m = hits t (n + 1) (m.insert x n) ∪ zipIdxR (n + 1) ≫ ∋ ≫ found t (look m) := by
  have h : zipIdxR (n + 1) ≫ ∋ ≫ found t (corefl (· ≠ x) ≫ look m) ∪ zipIdxR (n + 1) ≫ ∋ ≫ found t (look m)
      = zipIdxR (n + 1) ≫ ∋ ≫ found t (look m) := (le_iff_union_eq_left _ _).mp (comp_mono_left _ (comp_mono_left _
        (found_mono t (by simpa only [Cat.id_comp] using comp_mono_right (corefl_le_id (· ≠ x)) (look m)))))
  rw [cons_hits, hits, look_insert, found_union]
  simp only [comp_union_distrib, union_comp_distrib, found_miss n hm, zero_union, ← union_assoc, h]

/-! ## The fold -/

/-- `ev : f ↦ ((n,m), f(n,m))`, a scan as the set of its offset/map/answer triples. -/
def ev : Scan ⟶ Ev := fun f ((n, m), o) => f n m = o

/-- `scanSpec(t) : xs ↦ ((n,m), o)` when `o` is `orNone(hits(t,n,m))` of `xs`. -/
def scanSpec (t : Int) : LI ⟶ Ev := fun xs ((n, m), o) => orNone (hits t n m) xs o

/-- `scan(t) ≜ scanSpec(t) / ev`: the scans whose every triple `scanSpec(t)` allows. -/
def scan (t : Int) : LI ⟶ Scan := scanSpec t / ev

/-- `R ⊑ h scan(t)` when every scan `R` gives at `a` answers `orNone(hits)` of `h(a)` at every offset and map. -/
theorem le_scan {t : Int} {A : RelSet.{0}} {R : A ⟶ Scan} (h : A.carrier → List Int)
    (hR : ∀ a f, R a f → ∀ n m, orNone (hits t n m) (h a) (f n m)) : R ⊑ graph h ≫ scan t := by
  rw [scan, map_comp_div (graph_map h), le_div_iff]
  exact le_iff.mpr fun a ⟨⟨n, m⟩, o⟩ ⟨f, hf, ho⟩ => ⟨_, rfl, (ho : f n m = o) ▸ hR a f hf n m⟩

/-- The `[]` arm: `const none ⊑ nil scan(t)`, since `nil hits = 𝟘`. -/
theorem scan_nil (t : Int) :
    (graph fun _ => fun _ _ => none : dL Unit ⟶ Scan) ⊑ (graph fun _ => ([] : List Int) : dL Unit ⟶ LI) ≫ scan t :=
  le_scan _ fun _ f hf n m => by
    cases hf
    obtain ⟨_, rfl, h⟩ : ((graph fun _ => ([] : List Int) : dL Unit ⟶ LI) ≫ orNone (hits t n m)) () none := by
      rw [graph_orNone, nil_hits, orNone_zero]; rfl
    exact h

/-- The `x :: xs` arm: `(𝟙×scan(t)) step(t) ⊑ cons scan(t)`; a hit answers at the head, a miss is `hits_cons_eq`. -/
theorem scan_cons (t : Int) :
    rprodMap (𝟙 (dE Int)) (scan t) ≫ graph (fun p : Int × Scan.carrier => step t p.1 p.2)
      ⊑ graph (fun p : Int × List Int => p.1 :: p.2) ≫ scan t :=
  le_scan _ fun ⟨x, xs⟩ f ⟨⟨x', r⟩, ⟨hx, hr⟩, hf⟩ n m => by
    cases hx; cases hf
    show orNone (hits t n m) (x :: xs) (step t x r n m)
    cases hm : m[t - x]? with
    | some j =>
      rw [show step t x r n m = some (j, n) by simp only [step, hm, Option.elim]]
      exact Or.inl ⟨(j, n), ⟨_, rfl, Or.inr ⟨(x, n), List.mem_cons_self, ⟨_, rfl, hm⟩, rfl⟩⟩, rfl⟩
    | none =>
      rw [show step t x r n m = r (n + 1) (m.insert x n) by simp only [step, hm, Option.elim]]
      have hX : zipIdxR (n + 1) ≫ ∋ ≫ found t (look m) ⊑ hits t (n + 1) (m.insert x n) ≫ relTop Ans Ans :=
        le_trans (comp_mono_left _ (comp_mono_left _ (le_trans (found_mono t (look_keys m x n)) (found_top t _)))) <| by
          rw [hits, Cat.assoc]
          exact comp_mono_left _ (by rw [← Cat.assoc]; exact comp_mono_right (le_union_right _ _) _)
      have h := le_iff.mp (orNone_mono (le_union_left _ _) (union_lub (le_comp_top _) hX)) xs _
        (hr ((n + 1, m.insert x n), _) rfl)
      rw [← hits_cons_eq hm, ← graph_orNone] at h
      obtain ⟨_, rfl, h⟩ := h; exact h

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
