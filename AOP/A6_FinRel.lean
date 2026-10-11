/-
  Finite relations.  A list of pairs `l` denotes `rel(l) : K ⟶ V`, and every list operation is a
  relational law (`rel_cons`, `rel_swap`, `rel_map`, `rel_filter`, `rel_zipIdx`).  A `FinRel` stores
  the pairs as two parallel arrays, so its converse `conv` swaps them; a `SortedRel` also has its keys
  sorted, so `lookup` is two binary searches.  Programs use a structure only through `rep` and the
  `rep_*`/`lookup_rep` laws.  The generic hash join `join(F,G)` and its program `joinProg` are the
  application: `graph(joinProg(F,G)) ⊑ graph(join(F,G)) orNone(∋)`.
-/
module

public import AOP.A6_1_RelSet
public import AOP.A6_BinSearch

@[expose] public section

namespace Freyd.Alg.RelSet

open Freyd DistributiveAllegory Freyd.BinSearch

variable {A K V K' V' : Type}

/-- Indices. -/
abbrev Idx : RelSet.{0} := ⟨Nat⟩

/-! ## A list of pairs as a relation -/

/-- `rel(l) : k ↦ v` when `(k,v) ∈ l`. -/
def rel (l : List (K × V)) : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩ := fun k v => (k, v) ∈ l

/-- `∋ₗ : l ↦ v` when `v ∈ l`, a list as the set of its elements. -/
def lmem (V : Type) : (⟨List V⟩ : RelSet.{0}) ⟶ ⟨V⟩ := fun l v => v ∈ l

/-- `ix(xs) : j ↦ xs[j]`, a list as the relation from an index to its value. -/
def ix (xs : List A) : Idx ⟶ ⟨A⟩ := fun j a => xs[j]? = some a

theorem rel_nil : rel ([] : List (K × V)) = 𝟘 := hom_ext fun _ _ => ⟨fun h => absurd h List.not_mem_nil, False.elim⟩

theorem rel_cons (k : K) (v : V) (l : List (K × V)) : rel ((k, v) :: l) = single k v ∪ rel l :=
  hom_ext fun x y => by
    show (x, y) ∈ (k, v) :: l ↔ (∃ z, (x = z ∧ x = k) ∧ y = v) ∨ (x, y) ∈ l
    rw [List.mem_cons, Prod.mk.injEq]
    exact ⟨fun | .inl ⟨h1, h2⟩ => .inl ⟨x, ⟨rfl, h1⟩, h2⟩ | .inr h => .inr h,
      fun | .inl ⟨_, ⟨_, h1⟩, h2⟩ => .inl ⟨h1, h2⟩ | .inr h => .inr h⟩

theorem rel_perm {l l' : List (K × V)} (h : l.Perm l') : rel l = rel l' := hom_ext fun _ _ => h.mem_iff

theorem rel_swap (l : List (K × V)) : (rel l)° = rel (l.map Prod.swap) :=
  hom_ext fun v k => show (k, v) ∈ l ↔ (v, k) ∈ l.map Prod.swap from
    ⟨fun h => List.mem_map_of_mem (f := Prod.swap) h, fun h => by
      obtain ⟨⟨a, b⟩, hm, he⟩ := List.mem_map.1 h
      simp only [Prod.swap, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact hm⟩

theorem rel_map (f : K → K') (g : V → V') (l : List (K × V)) :
    rel (l.map (Prod.map f g)) = (graph f)° ≫ rel l ≫ graph g :=
  hom_ext fun x y => ⟨fun h => by
      obtain ⟨⟨a, b⟩, hm, he⟩ := List.mem_map.1 h
      simp only [Prod.map, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨a, rfl, b, hm, rfl⟩,
    fun ⟨a, (ha : x = f a), b, hm, (hb : y = g b)⟩ => by subst ha hb; exact List.mem_map_of_mem (f := Prod.map f g) hm⟩

theorem rel_filter (p : K × V → Bool) (l : List (K × V)) :
    rel (l.filter p) = rel l ∩ (fun k v => p (k, v) = true : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) :=
  hom_ext fun _ _ => List.mem_filter

theorem rel_zipIdx (xs : List A) : rel (xs.zipIdx.map Prod.swap) = ix xs := by
  rw [← rel_swap]; exact hom_ext fun j a => show (a, j) ∈ xs.zipIdx ↔ xs[j]? = some a from List.mem_zipIdx_iff_getElem?

/-- The one refinement law: `head? ⊑ orNone(∋ₗ)`, the head is some element, or `none` on `[]`. -/
theorem head?_le_orNone : (graph List.head? : (⟨List V⟩ : RelSet.{0}) ⟶ ⟨Option V⟩) ⊑ orNone (lmem V) :=
  le_iff.mpr fun l o (h : o = l.head?) => by
    subst h
    cases l with
    | nil => exact Or.inr ⟨[], ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩, rfl⟩
    | cons x t => exact Or.inl ⟨x, List.mem_cons.2 (Or.inl rfl), rfl⟩

/-! ## Two parallel arrays -/

/-- A finite relation as two parallel arrays, `keys[i] ↦ vals[i]`. -/
structure FinRel (K V : Type) where
  keys : Array K
  vals : Array V
  len : keys.size = vals.size

namespace FinRel

def rep (r : FinRel K V) : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩ := rel (r.keys.toList.zip r.vals.toList)

def ofList (l : List (K × V)) : FinRel K V := ⟨l.unzip.1.toArray, l.unzip.2.toArray, by simp⟩

theorem rep_ofList (l : List (K × V)) : (ofList l).rep = rel l := by
  simp only [rep, ofList, List.toList_toArray, List.zip_unzip]

/-- The converse swaps the two arrays: no copy, no sort. -/
def conv (r : FinRel K V) : FinRel V K := ⟨r.vals, r.keys, r.len.symm⟩

theorem mem_rep {r : FinRel K V} {k : K} {v : V} :
    r.rep k v ↔ ∃ i, ∃ h : i < r.keys.size, ∃ h' : i < r.vals.size, r.keys[i] = k ∧ r.vals[i] = v := by
  simp only [rep, rel, List.mem_iff_getElem, List.getElem_zip, List.length_zip, Array.length_toList,
    Array.getElem_toList, Prod.mk.injEq]
  exact ⟨fun ⟨i, h, e⟩ => ⟨i, by omega, by omega, e⟩, fun ⟨i, h, h', e⟩ => ⟨i, by omega, e⟩⟩

theorem rep_conv (r : FinRel K V) : r.conv.rep = r.rep° :=
  hom_ext fun _ _ => mem_rep.trans (Iff.trans ⟨fun ⟨i, h, h', a, b⟩ => ⟨i, h', h, b, a⟩,
    fun ⟨i, h, h', a, b⟩ => ⟨i, h', h, b, a⟩⟩ mem_rep.symm)

/-- `sel(k) : (k',v) ↦ v` when `k' = k`. -/
def sel [DecidableEq K] (k : K) (p : K × V) : Option V := if p.1 = k then some p.2 else none

/-- Unsorted lookup, a linear scan of the keys. -/
def scanLookup [DecidableEq K] (r : FinRel K V) (k : K) : List V := (r.keys.toList.zip r.vals.toList).filterMap (sel k)

theorem scanLookup_rep [DecidableEq K] (r : FinRel K V) :
    (graph r.scanLookup : (⟨K⟩ : RelSet.{0}) ⟶ ⟨List V⟩) ≫ lmem V = r.rep :=
  hom_ext fun k v => by
    show (∃ l, l = r.scanLookup k ∧ v ∈ l) ↔ (k, v) ∈ r.keys.toList.zip r.vals.toList
    simp only [exists_eq_left, scanLookup, List.mem_filterMap, sel]
    refine ⟨fun ⟨⟨a, b⟩, hm, hs⟩ => ?_, fun h => ⟨(k, v), h, if_pos rfl⟩⟩
    by_cases e : a = k
    · rw [if_pos e] at hs; cases Option.some.inj hs; exact e ▸ hm
    · rw [if_neg e] at hs; exact absurd hs (by simp)

end FinRel

/-! ## Sorted keys: an index -/

/-- A `FinRel` whose keys are sorted.  Sorting costs `O(n log n)` once and a lookup `O(log n)`, so it
    pays only when the lookups outnumber what a sort costs over the linear `scanLookup`. -/
structure SortedRel (K V : Type) [Ord K] extends FinRel K V where
  sorted : keys.toList.Pairwise fun a b => (compare a b).isLE

namespace SortedRel

open FinRel

/-- Sort the pairs by key: `mergeSort`, then the two arrays again. -/
def sortByKey [Ord K] [Std.TransOrd K] (r : FinRel K V) : SortedRel K V :=
  let m := (r.keys.toList.zip r.vals.toList).mergeSort fun a b => (compare a.1 b.1).isLE
  { ofList m with
    sorted := by
      simp only [ofList, List.toList_toArray, List.unzip_fst, List.pairwise_map]
      exact List.pairwise_mergeSort (fun _ _ _ => Std.TransCmp.isLE_trans) (fun a b => by
        rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := a.1) (b := b.1), Ordering.isLE_swap]
        cases compare b.1 a.1 <;> rfl) _ }

theorem rep_sortByKey [Ord K] [Std.TransOrd K] (r : FinRel K V) : (sortByKey r).rep = r.rep :=
  (rep_ofList _).trans (rel_perm (List.mergeSort_perm _ _))

variable [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- Binary lookup: the run of keys equal to `k` lies between the first key `≥ k` and the first `> k`. -/
-- Reads the run by index rather than `Array.extract`, whose core lemmas use `Classical.choice`.
def lookup (s : SortedRel K V) (k : K) : List V :=
  let lo := partition s.keys fun y => (compare y k).isLT
  (List.range' lo ((partition s.keys fun y => (compare y k).isLE) - lo)).filterMap (s.vals[·]?)

omit [Std.TransOrd K] [Std.LawfulEqOrd K] in
theorem isLE_of_lt {s : SortedRel K V} {i j : Nat} (hij : i < j) (hj : j < s.keys.size) :
    (compare (s.keys[i]'(Nat.lt_trans hij hj)) s.keys[j]).isLE = true := by
  have := List.pairwise_iff_getElem.1 s.sorted i j (by simp; omega) (by simpa using hj) hij
  simpa using this

/-- `i` lies in the run of `k` exactly when `keys[i] = k`. -/
theorem run_iff (s : SortedRel K V) (k : K) (i : Nat) (h : i < s.keys.size) :
    (partition s.keys (fun y => (compare y k).isLT) ≤ i ∧ i < partition s.keys fun y => (compare y k).isLE)
      ↔ s.keys[i] = k := by
  have h1 := partition_iff (p := fun y => (compare y k).isLT) (fun i j hij hj hp => Ordering.isLT_iff_eq_lt.2
    (Std.TransCmp.lt_of_isLE_of_lt (isLE_of_lt hij hj) (Ordering.isLT_iff_eq_lt.1 hp))) i h
  have h2 := partition_iff (p := fun y => (compare y k).isLE)
    (fun i j hij hj hp => Std.TransCmp.isLE_trans (isLE_of_lt hij hj) hp) i h
  rw [← Std.LawfulEqCmp.compare_eq_iff_eq (cmp := compare)]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hle := h2.2 hhi
    have hn : ¬ (compare s.keys[i] k).isLT = true := fun hp => Nat.not_le.2 (h1.1 hp) hlo
    revert hle hn; cases compare s.keys[i] k <;> decide
  · intro he; rw [he] at h1 h2
    exact ⟨Nat.not_lt.1 fun hl => absurd (h1.2 hl) (by decide), h2.1 rfl⟩

theorem mem_lookup {s : SortedRel K V} {k : K} {v : V} :
    v ∈ s.lookup k ↔ ∃ i, ∃ h : i < s.keys.size, ∃ h' : i < s.vals.size, s.keys[i] = k ∧ s.vals[i] = v := by
  simp only [lookup, List.mem_filterMap, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨hlo, hlt⟩, hv⟩
    obtain ⟨h', rfl⟩ := Array.getElem?_eq_some_iff.1 hv
    have h : i < s.keys.size := by have := s.len; omega
    exact ⟨i, h, h', (run_iff s k i h).1 ⟨hlo, by omega⟩, rfl⟩
  · rintro ⟨i, h, h', hk, rfl⟩
    have ⟨hlo, hlt⟩ := (run_iff s k i h).2 hk
    exact ⟨i, ⟨hlo, by omega⟩, Array.getElem?_eq_getElem h'⟩

theorem lookup_rep (s : SortedRel K V) : (graph s.lookup : (⟨K⟩ : RelSet.{0}) ⟶ ⟨List V⟩) ≫ lmem V = s.rep :=
  hom_ext fun _ _ => ⟨fun ⟨_, hl, hv⟩ => mem_rep.2 (mem_lookup.1 (hl ▸ hv)),
    fun h => ⟨_, rfl, mem_lookup.2 (mem_rep.1 h)⟩⟩

end SortedRel

/-! ## The generic join -/

open FinRel SortedRel

/-- `join(F,G)(xs) ≜ ix(xs) F G° ix(xs)° ∩ (<)`: index pairs `j<k` with `F(xs[j]) = G(xs[k])`. -/
def join (F G : A → K) (xs : List A) : Idx ⟶ Idx := ix xs ≫ graph F ≫ (graph G)° ≫ (ix xs)° ∩ (· < ·)

/-- The index of `xs` by `F`: the pairs `(j, F(xs[j]))`, conversed by swapping the arrays, sorted once. -/
def index [Ord K] [Std.TransOrd K] (F : A → K) (xs : List A) : SortedRel K Nat :=
  sortByKey (ofList ((xs.zipIdx.map Prod.swap).map (Prod.map id F))).conv

theorem rep_index [Ord K] [Std.TransOrd K] (F : A → K) (xs : List A) :
    (index F xs).rep = (ix xs ≫ graph F)° := by
  rw [index, rep_sortByKey, rep_conv, rep_ofList, rel_map, rel_zipIdx]
  show ((graph fun x : Nat => x)° ≫ ix xs ≫ graph F)° = _
  rw [graph_id, recip_id, Cat.id_comp]

/-- At `(x,k)`: the indices `j<k` that `index` holds under `G(x)`, paired with `k`. -/
def probe [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] (s : SortedRel K Nat) (G : A → K) (p : A × Nat) :
    List (Nat × Nat) :=
  ((s.lookup (G p.1)).filter (· < p.2)).map (·, p.2)

variable [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- Every candidate pair, in probe order. -/
def cands (F G : A → K) (xs : List A) : List (Nat × Nat) := xs.zipIdx.flatMap (probe (index F xs) G)

/-- The program: build the index once, then the first probe that hits. -/
def joinProg (F G : A → K) (xs : List A) : Option (Nat × Nat) :=
  let s := index F xs
  xs.zipIdx.findSome? fun p => (probe s G p).head?

theorem head?_flatMap {B C : Type} (f : B → List C) (l : List B) :
    (l.flatMap f).head? = l.findSome? fun a => (f a).head? := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.flatMap_cons, List.head?_append, List.findSome?_cons, ih]; cases (f a).head? <;> rfl

theorem mem_cands (F G : A → K) (xs : List A) (j k : Nat) : (j, k) ∈ cands F G xs ↔ join F G xs j k := by
  have hl : ∀ c j, j ∈ (index F xs).lookup c ↔ (ix xs ≫ graph F)° c j := fun c j => by
    rw [← rep_index, ← lookup_rep]; exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ h⟩
  simp only [cands, probe, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨x, k'⟩, hx, j', ⟨hj, hlt⟩, rfl, rfl⟩
    obtain ⟨a, ha, (hb : G x = F a)⟩ := (hl _ _).1 hj
    exact ⟨⟨a, ha, F a, rfl, x, hb.symm, List.mem_zipIdx_iff_getElem?.1 hx⟩, hlt⟩
  · rintro ⟨⟨a, ha, b, (hb : b = F a), x, (hx : b = G x), hk⟩, hlt⟩
    exact ⟨(x, k), List.mem_zipIdx_iff_getElem?.2 hk, j, ⟨(hl _ _).2 ⟨a, ha, hx.symm.trans hb⟩, hlt⟩, rfl, rfl⟩

theorem cands_rel (F G : A → K) :
    (graph (cands F G) : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨List (Nat × Nat)⟩) ≫ lmem _
      = (graph (join F G) : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨Idx ⟶ Idx⟩) ≫ relMem Idx Idx :=
  hom_ext fun xs ⟨j, k⟩ => ⟨fun ⟨_, hl, hm⟩ => ⟨_, rfl, (mem_cands F G xs j k).1 (hl ▸ hm)⟩,
    fun ⟨_, hR, h⟩ => ⟨_, rfl, (mem_cands F G xs j k).2 (hR ▸ h)⟩⟩

/-- **The program refines the join**: `graph(joinProg(F,G)) ⊑ graph(join(F,G)) orNone(∋)`. -/
theorem joinProg_le (F G : A → K) :
    (graph (joinProg F G) : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨Option (Nat × Nat)⟩)
      ⊑ (graph (join F G) : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨Idx ⟶ Idx⟩) ≫ orNone (relMem Idx Idx) :=
  calc (graph (joinProg F G) : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨Option (Nat × Nat)⟩)
      = graph (cands F G) ≫ graph List.head? := by
        rw [graph_comp]; exact congrArg graph (funext fun xs => (head?_flatMap _ _).symm)
    _ ⊑ graph (cands F G) ≫ orNone (lmem _) := comp_mono_left _ head?_le_orNone
    _ = orNone (graph (cands F G) ≫ lmem _) := graph_orNone _ _
    _ = orNone (graph (join F G) ≫ relMem Idx Idx) := by rw [cands_rel]
    _ = graph (join F G) ≫ orNone (relMem Idx Idx) := (graph_orNone _ _).symm

end Freyd.Alg.RelSet
