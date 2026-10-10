/-
  LeetCode 1 — Two Sum. A list is the relation `ix(xs) : Idx ⟶ Key` from an index to its value, and
  `twoSum(t)(xs) ≜ ix(xs) (t−) ix(xs)° ∩ (<)`: the index pairs `j<k` whose values sum to `t`; `twoSumO(t)` answers one.
  Derivation: `graph(prog(t)) = graph(go(t)) at₀ ⊑ scan(t) at₀ ⊑ graph(hits(t,0,∅)) orNone(∋) = twoSumO(t)`, with
  the fold premise `[scan_nil, scan_cons]`. Mathlib-free; `Classical.choice` enters only through `Std.HashMap` lemmas.
-/
import AOP.A6_GenFold
import Std.Data.HashMap

namespace Freyd.Alg.RelSet.LC1

open Freyd CL DistributiveAllegory

/-- Values, indices, lists, answers, maps, scans and their triples. -/
abbrev Key : RelSet.{0} := ⟨Int⟩
abbrev Idx : RelSet.{0} := ⟨Nat⟩
abbrev LI : RelSet.{0} := ⟨List Int⟩
abbrev Opt : RelSet.{0} := ⟨Option (Nat × Nat)⟩
abbrev HM := Std.HashMap Int Nat
abbrev Scan : RelSet.{0} := ⟨Nat → HM → Option (Nat × Nat)⟩
abbrev Ev : RelSet.{0} := ⟨(Nat × HM) × Option (Nat × Nat)⟩

/-- `∋ : ⟨Idx ⟶ Idx⟩ ⟶ Idx×Idx`, a relation as its set of pairs. -/
local notation (priority := high) "∋" => relMem Idx Idx

/-! ## The specification -/

/-- `ix(xs) : j ↦ xs[j]`, the list as a relation from an index to its value. -/
def ix (xs : List Int) : Idx ⟶ Key := fun j a => xs[j]? = some a

/-- `(t−) : a ↦ t-a`, its own converse. -/
def sub (t : Int) : Key ⟶ Key := graph (t - ·)

/-- `(+n) : i ↦ i+n`, so `(+n)° ix(xs)` is `xs` placed from index `n` on. -/
def plus (n : Nat) : Idx ⟶ Idx := graph (· + n)

/-- `pairs(t)(S) ≜ S (t−) S° ∩ (<)`: two indices in order whose values sum to `t`. -/
def pairs (t : Int) (S : Idx ⟶ Key) : Idx ⟶ Idx := S ≫ sub t ≫ S° ∩ (· < ·)

def twoSum (t : Int) (xs : List Int) : Idx ⟶ Idx := pairs t (ix xs)

/-- `twoSumO(t) ≜ twoSum(t) orNone(∋)`: some pair of `twoSum(t)(xs)`, or `none` when it is empty. -/
def twoSumO (t : Int) : LI ⟶ Opt := graph (twoSum t) ≫ orNone ∋

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

/-- `look(m) : Key ⟶ Idx`, the finite relation the map denotes. -/
def look (m : HM) : Key ⟶ Idx := fun a j => m[a]? = some j

/-- `(a↦b) ≜ (=a)? (⊸b)`, the one-pair relation. -/
def single {A B : RelSet.{0}} (a : A.carrier) (b : B.carrier) : A ⟶ B := corefl (· = a) ≫ graph fun _ => b

theorem single_recip {A B : RelSet.{0}} (a : A.carrier) (b : B.carrier) : (single a b)° = single b a :=
  hom_ext fun x y => show single a b y x ↔ single b a x y by simp [single, corefl, graph, and_comm]

theorem look_empty : look {} = 𝟘 := hom_ext fun a j => ⟨fun h => by simp [look] at h, fun h => (h : False).elim⟩

/-- `look(insert(x,n)(m)) = (x↦n) ∪ (≠x)? look(m)`: insertion overrides the key `x`. -/
theorem look_insert (m : HM) (x : Int) (n : Nat) : look (m.insert x n) = single x n ∪ corefl (· ≠ x) ≫ look m :=
  hom_ext fun a j => by
    by_cases h : x = a
    · subst h; simp [look, single, corefl, graph, eq_comm]
    · simp [look, single, corefl, graph, Std.HashMap.getElem?_insert, h, Ne.symm h]

/-- `look(m)° ⊑ ⊤ look(insert(x,n)(m))°`: the override keeps every key. -/
theorem look_keys (m : HM) (x : Int) (n : Nat) : (look m)° ⊑ relTop Idx Idx ≫ (look (m.insert x n))° :=
  le_iff.mpr fun j a (h : m[a]? = some j) => by
    by_cases hx : x = a
    · subst hx; exact ⟨n, trivial, by simp [look]⟩
    · exact ⟨j, trivial, by simp [look, Std.HashMap.getElem?_insert, hx, h]⟩

/-- `look(m)° (t−) (x↦n) = 𝟘` when `t-x ∉ dom(m)`. -/
theorem look_miss {t x : Int} {m : HM} (n : Nat) (hm : m[t - x]? = none) :
    (look m)° ≫ sub t ≫ (single x n : Key ⟶ Idx) = 𝟘 :=
  hom_ext fun _ _ => ⟨fun ⟨a, ha, b, (hb : b = t - a), _, ⟨⟨hbz, (hzx : b = x)⟩, _⟩⟩ => by
    obtain rfl : a = t - x := by dsimp only at *; omega
    exact (nomatch hm.symm.trans ha), fun h => (h : False).elim⟩

theorem ix_nil : ix [] = 𝟘 := hom_ext fun _ _ => ⟨fun h => by simp [ix] at h, fun h => (h : False).elim⟩

/-- `(+n)° ix(x:xs) = (n↦x) ∪ (+(n+1))° ix(xs)`: the head sits at `n`, the rest from `n+1` on. -/
theorem ix_cons (x : Int) (xs : List Int) (n : Nat) :
    (plus n)° ≫ ix (x :: xs) = (single n x : Idx ⟶ Key) ∪ (plus (n + 1))° ≫ ix xs :=
  hom_ext fun j a => by
    constructor
    · rintro ⟨_ | i, rfl, h⟩
      · exact Or.inl ⟨_, ⟨rfl, Nat.zero_add n⟩, (Option.some.inj (by simpa [ix] using h)).symm⟩
      · exact Or.inr ⟨i, by show i + 1 + n = i + (n + 1); omega, by simpa [ix] using h⟩
    · rintro (⟨_, ⟨rfl, rfl⟩, rfl⟩ | ⟨i, rfl, h⟩)
      · exact ⟨0, (Nat.zero_add _).symm, by simp [ix]⟩
      · exact ⟨i + 1, by show i + (n + 1) = i + 1 + n; dsimp only at *; omega, by simpa [ix] using h⟩

theorem plus_zero : plus 0 = 𝟙 Idx := hom_ext fun i j => show j = i + 0 ↔ i = j from ⟨fun h => h.symm, fun h => h.symm⟩

/-- `pairs(t)((n↦x) ∪ (+(n+1))° Q) = pairs(t)((+(n+1))° Q) ∪ (n↦x) (t−) ((+(n+1))° Q)°`: the head at `n` is before
    every later index and after none. -/
theorem pairs_cons (t x : Int) (n : Nat) (Q : Idx ⟶ Key) : pairs t ((single n x : Idx ⟶ Key) ∪ (plus (n + 1))° ≫ Q)
    = pairs t ((plus (n + 1))° ≫ Q) ∪ (single n x : Idx ⟶ Key) ≫ sub t ≫ ((plus (n + 1))° ≫ Q)° :=
  hom_ext fun j k => by
    constructor
    · rintro ⟨⟨a, ha, b, hb, hk⟩, (hlt : j < k)⟩
      rcases ha with ha | ha <;> rcases hk with hk | hk
      · obtain ⟨_, ⟨h1, (h2 : j = n)⟩, -⟩ := ha; obtain ⟨_, ⟨h3, (h4 : k = n)⟩, -⟩ := hk; dsimp only at *; omega
      · exact Or.inr ⟨a, ha, b, hb, hk⟩
      · obtain ⟨i, (hi : j = i + (n + 1)), -⟩ := ha; obtain ⟨_, ⟨h3, (h4 : k = n)⟩, -⟩ := hk; dsimp only at *; omega
      · exact Or.inl ⟨⟨a, ha, b, hb, hk⟩, hlt⟩
    · rintro (⟨⟨a, ha, b, hb, hk⟩, hlt⟩ | ⟨a, ha, b, hb, hk⟩)
      · exact ⟨⟨a, Or.inr ha, b, hb, Or.inr hk⟩, hlt⟩
      · refine ⟨⟨a, Or.inl ha, b, hb, Or.inr hk⟩, ?_⟩
        obtain ⟨_, ⟨h1, (h2 : j = n)⟩, -⟩ := ha; obtain ⟨i, (hi : k = i + (n + 1)), -⟩ := hk; show j < k; dsimp only at *; omega

/-! ## Hits -/

/-- `hits(t,n,m)(xs) ≜ pairs(t)(S) ∪ look(m)° (t−) S°` with `S ≜ (+n)° ix(xs)`: pairs within `xs` placed from `n`,
    and pairs of a mapped earlier index with an index of `xs`. -/
def hits (t : Int) (n : Nat) (m : HM) (xs : List Int) : Idx ⟶ Idx :=
  pairs t ((plus n)° ≫ ix xs) ∪ (look m)° ≫ sub t ≫ ((plus n)° ≫ ix xs)°

theorem hits_empty (t : Int) : hits t 0 {} = twoSum t := funext fun xs => by
  rw [hits, look_empty, recip_zero, zero_comp, union_zero, plus_zero, recip_id, Cat.id_comp]; rfl

theorem hits_nil (t : Int) (n : Nat) (m : HM) : hits t n m [] = 𝟘 := by
  simp only [hits, pairs, ix_nil, comp_zero, recip_zero, union_zero]; exact hom_ext fun _ _ => ⟨fun h => h.1, fun h => (h : False).elim⟩

/-- A hit: `t-x ↦ j` in `m` pairs `j` with the head's index `n`. -/
theorem hits_hit {t x : Int} {n j : Nat} {m : HM} (xs : List Int) (hm : m[t - x]? = some j) :
    hits t n m (x :: xs) j n :=
  Or.inr ⟨t - x, hm, x, (Int.sub_sub_self t x).symm, 0, (Nat.zero_add n).symm, rfl⟩

/-- On a miss, `hits(t,n,m)(x:xs) = hits(t,n+1,insert(x,n)(m))(xs) ∪ look(m)° (t−) ((+(n+1))° ix(xs))°`. -/
theorem hits_cons_eq {t x : Int} {n : Nat} {m : HM} (xs : List Int) (hm : m[t - x]? = none) : hits t n m (x :: xs)
    = hits t (n + 1) (m.insert x n) xs ∪ (look m)° ≫ sub t ≫ ((plus (n + 1))° ≫ ix xs)° := by
  have key : ∀ P B C A : Idx ⟶ Idx, C ⊑ A → (P ∪ B) ∪ A = (P ∪ (C ∪ B)) ∪ A := fun P B C A h => by
    rw [union_comm C B, union_assoc P B C, ← union_assoc _ C A, (le_iff_union_eq_left _ _).mp h]
  have hC : ∀ R : Key ⟶ Idx, (look m)° ≫ (corefl (· ≠ x))° ≫ R ⊑ (look m)° ≫ R := fun R => comp_mono_left _
    (by simpa only [recip_id, Cat.id_comp] using comp_mono_right (recip_mono (corefl_le_id (· ≠ x))) R)
  rw [hits, hits, ix_cons, pairs_cons, look_insert]
  simp only [recip_union, Allegory.recip_comp, single_recip, comp_union_distrib, union_comp_distrib, Cat.assoc,
    look_miss n hm, union_zero]
  exact key _ _ _ _ (hC _)

/-! ## The fold -/

/-- `ev : f ↦ ((n,m), f(n,m))`, a scan as the set of its offset/map/answer triples. -/
def ev : Scan ⟶ Ev := fun f ((n, m), o) => f n m = o

/-- `scanSpec(t) : xs ↦ ((n,m), o)` when `o` is `orNone(∋)` of `hits(t,n,m)(xs)`. -/
def scanSpec (t : Int) : LI ⟶ Ev := fun xs ((n, m), o) => orNone ∋ (hits t n m xs) o

/-- `scan(t) ≜ scanSpec(t) / ev`: the scans whose every triple `scanSpec(t)` allows. -/
def scan (t : Int) : LI ⟶ Scan := scanSpec t / ev

/-- `R ⊑ h scan(t)` when every scan `R` gives at `a` answers `orNone(∋)` of `hits` of `h(a)` at every offset and map. -/
theorem le_scan {t : Int} {A : RelSet.{0}} {R : A ⟶ Scan} (h : A.carrier → List Int)
    (hR : ∀ a f, R a f → ∀ n m, orNone ∋ (hits t n m (h a)) (f n m)) : R ⊑ graph h ≫ scan t := by
  rw [scan, map_comp_div (graph_map h), le_div_iff]
  exact le_iff.mpr fun a ⟨⟨n, m⟩, o⟩ ⟨f, hf, ho⟩ => ⟨_, rfl, (ho : f n m = o) ▸ hR a f hf n m⟩

/-- The `[]` arm: `const none ⊑ nil scan(t)`, since `hits(t,n,m)([]) = 𝟘`. -/
theorem scan_nil (t : Int) :
    (graph fun _ => fun _ _ => none : dL Unit ⟶ Scan) ⊑ (graph fun _ => ([] : List Int) : dL Unit ⟶ LI) ≫ scan t :=
  le_scan _ fun _ f hf n m => by
    cases hf
    show orNone ∋ (hits t n m []) none
    rw [hits_nil]; exact Or.inr ⟨_, ⟨rfl, fun _ h => h⟩, rfl⟩

/-- The `x :: xs` arm: `(𝟙×scan(t)) step(t) ⊑ cons scan(t)`; a hit answers at the head, a miss is `hits_cons_eq`. -/
theorem scan_cons (t : Int) :
    rprodMap (𝟙 (dE Int)) (scan t) ≫ graph (fun p : Int × Scan.carrier => step t p.1 p.2)
      ⊑ graph (fun p : Int × List Int => p.1 :: p.2) ≫ scan t :=
  le_scan _ fun ⟨x, xs⟩ f ⟨⟨x', r⟩, ⟨hx, hr⟩, hf⟩ n m => by
    cases hx; cases hf
    show orNone ∋ (hits t n m (x :: xs)) (step t x r n m)
    cases hm : m[t - x]? with
    | some j =>
      rw [show step t x r n m = some (j, n) by simp only [step, hm, Option.elim]]
      exact Or.inl ⟨(j, n), hits_hit xs hm, rfl⟩
    | none =>
      rw [show step t x r n m = r (n + 1) (m.insert x n) by simp only [step, hm, Option.elim], hits_cons_eq xs hm]
      have hA : (look m)° ≫ sub t ≫ ((plus (n + 1))° ≫ ix xs)°
          ⊑ relTop Idx Idx ≫ hits t (n + 1) (m.insert x n) xs ≫ relTop Idx Idx :=
        le_trans (comp_mono_right (look_keys m x n) _) <| by
          rw [Cat.assoc]; exact comp_mono_left _ (le_trans (le_union_right _ _) (le_comp_top _))
      exact orNone_relMem_mono (le_union_left _ _) (union_lub (le_top_comp_top _) hA) _
        (hr ((n + 1, m.insert x n), _) rfl)

/-! ## The derivation -/

/-- **The program refines the entire spec**: `graph(prog(t)) ⊑ twoSumO(t)`. -/
theorem prog_le (t : Int) : (graph (prog t) : LI ⟶ Opt) ⊑ twoSumO t :=
  calc graph (prog t)
      = graph (go t) ≫ at₀ := by rw [at₀, graph_comp]; rfl
    _ ⊑ scan t ≫ at₀ := comp_mono_right (foldr_le _ _ (scan_nil t) (scan_cons t)) _
    _ ⊑ graph (hits t 0 {}) ≫ orNone ∋ := le_iff.mpr fun xs o ⟨f, hX, ho⟩ =>
        ⟨_, rfl, ho ▸ (hX ((0, {}), f 0 {}) rfl : orNone ∋ (hits t 0 {} xs) (f 0 {}))⟩
    _ = twoSumO t := by rw [hits_empty]; rfl

#eval prog 9 [2, 7, 11, 15]   -- some (0, 1)
#eval prog 6 [3, 2, 4]        -- some (1, 2)
#eval prog 7 [1, 2, 3]        -- none

end Freyd.Alg.RelSet.LC1
