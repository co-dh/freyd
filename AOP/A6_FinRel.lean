/-
  Finite relations.  A list of pairs `l` denotes `rel(l) : K ⟶ V`, and every list operation is a
  relational law (`rel_cons`, `rel_swap`, `rel_map`, `rel_filter`, `rel_append`, `rel_zipIdx`).  A
  `FinRel` stores the pairs as two parallel arrays and is a finite relation algebra: every operation is
  an array program with one law against `rep`, the relation it denotes — `conv` (`°`), `comp` (`≫`),
  `inter` (`∩`), `union` (`∪`), `le` (`⊑`), `div` (`\` on `ran`), `filter` (`∩` a decidable relation),
  `map` (`≫ graph f`), `dom`, `ran`; `dedup` sorts the pairs and drops the repeats, and `div`, `dom`,
  `ran` return through it.  A `SortedRel` has its keys sorted, so `lookup` is two binary searches; the ops
  that look up repeatedly sort the looked-up side once.  Programs use a structure only through `rep`
  and the `rep_*`/`lookup_rep` laws.
-/
module

public import AOP.A6_1_RelSet
public import AOP.A6_BinSearch
public import AOP.A8_1
import AOP.A7_2_RelSet

@[expose] public section

namespace Freyd.Alg.RelSet

open Freyd DistributiveAllegory Freyd.BinSearch

variable {A B C K V K' V' : Type}

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

theorem rel_append (l l' : List (K × V)) : rel (l ++ l') = rel l ∪ rel l' := hom_ext fun _ _ => List.mem_append

theorem rel_zipIdx (xs : List A) : rel (xs.zipIdx.map Prod.swap) = ix xs := by
  rw [← rel_swap]; exact hom_ext fun j a => show (a, j) ∈ xs.zipIdx ↔ xs[j]? = some a from List.mem_zipIdx_iff_getElem?

/-- The one refinement law: `head? ⊑ orNone(∋ₗ)`, the head is some element, or `none` on `[]`. -/
theorem head?_le_orNone : (graph List.head? : (⟨List V⟩ : RelSet.{0}) ⟶ ⟨Option V⟩) ⊑ orNone (lmem V) :=
  le_iff.mpr fun l o (h : o = l.head?) => by
    subst h
    cases l with
    | nil => exact Or.inr ⟨[], ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩, rfl⟩
    | cons x t => exact Or.inl ⟨x, List.mem_cons.2 (Or.inl rfl), rfl⟩

/-! ## Sorted lists without repeats -/

/-- `mergeSort` by `compare` on `f` sorts by it. -/
theorem pairwise_mergeSort_on [Ord B] [Std.TransOrd B] (f : A → B) (l : List A) :
    (l.mergeSort fun a b => (compare (f a) (f b)).isLE).Pairwise fun a b => (compare (f a) (f b)).isLE :=
  List.pairwise_mergeSort (fun _ _ _ => Std.TransCmp.isLE_trans) (fun a b => by
    rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := f a) (b := f b), Ordering.isLE_swap]
    cases compare (f b) (f a) <;> rfl) _

/-- Cons `a`, unless it equals the head. -/
def push [Ord A] (a : A) : List A → List A
  | b :: u => if compare a b = .eq then b :: u else a :: b :: u
  | [] => [a]

/-- Drop each element equal to the next kept one: on a sorted list, every repeat. -/
def uniq [Ord A] (l : List A) : List A := l.foldr push []

theorem mem_push [Ord A] [Std.LawfulEqOrd A] (a x : A) : (u : List A) → (x ∈ push a u ↔ x ∈ a :: u)
  | [] => Iff.rfl
  | b :: u => by
    by_cases h : compare a b = .eq
    · rw [push, if_pos h, (Std.LawfulEqCmp.compare_eq_iff_eq (cmp := compare)).1 h]
      exact ⟨List.mem_cons_of_mem _, fun h => (List.mem_cons.1 h).elim (fun e => List.mem_cons.2 (.inl e)) id⟩
    · rw [push, if_neg h]

theorem mem_uniq [Ord A] [Std.LawfulEqOrd A] (x : A) : (l : List A) → (x ∈ uniq l ↔ x ∈ l)
  | [] => Iff.rfl
  | a :: t => (mem_push a x _).trans
      (List.mem_cons.trans ((or_congr_right (mem_uniq x t)).trans List.mem_cons.symm))

theorem pairwise_push [Ord A] [Std.TransOrd A] {a : A} {u : List A}
    (hu : u.Pairwise fun x y => compare x y = .lt) (ha : ∀ x ∈ u, (compare a x).isLE) :
    (push a u).Pairwise fun x y => compare x y = .lt := by
  cases u with
  | nil => exact List.pairwise_singleton _ _
  | cons b u =>
    by_cases h : compare a b = .eq
    · rw [push, if_pos h]; exact hu
    · rw [push, if_neg h]
      refine List.pairwise_cons.2 ⟨fun x hx => ?_, hu⟩
      have hab := ha b (List.mem_cons.2 (.inl rfl))
      rcases List.mem_cons.1 hx with rfl | hx
      · revert hab h; cases compare a x <;> decide
      · exact Std.TransCmp.lt_of_isLE_of_lt hab ((List.pairwise_cons.1 hu).1 x hx)

/-- On a sorted list, `uniq` is strictly increasing. -/
theorem pairwise_uniq [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A] : {l : List A} →
    l.Pairwise (fun x y => (compare x y).isLE) → (uniq l).Pairwise fun x y => compare x y = .lt
  | [], _ => List.Pairwise.nil
  | _ :: t, h =>
    let ⟨ha, ht⟩ := List.pairwise_cons.1 h
    pairwise_push (pairwise_uniq ht) fun x hx => ha x ((mem_uniq x t).1 hx)

theorem nodup_uniq [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A] {l : List A}
    (h : l.Pairwise fun x y => (compare x y).isLE) : (uniq l).Nodup :=
  (pairwise_uniq h).imp fun hl e => by subst e; rw [Std.ReflCmp.compare_self (cmp := compare)] at hl; cases hl

/-! ## Two parallel arrays -/

/-- A finite relation as two parallel arrays, `keys[i] ↦ vals[i]`. -/
structure FinRel (K V : Type) where
  keys : Array K
  vals : Array V
  len : keys.size = vals.size

namespace FinRel

/-- The pairs in array order. -/
def toList (r : FinRel K V) : List (K × V) := r.keys.toList.zip r.vals.toList

def rep (r : FinRel K V) : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩ := rel r.toList

def ofList (l : List (K × V)) : FinRel K V := ⟨l.unzip.1.toArray, l.unzip.2.toArray, by simp⟩

theorem toList_ofList (l : List (K × V)) : (ofList l).toList = l := by
  simp only [toList, ofList, List.toList_toArray, List.zip_unzip]

theorem rep_ofList (l : List (K × V)) : (ofList l).rep = rel l := congrArg rel (toList_ofList l)

/-- The converse swaps the two arrays: no copy, no sort. -/
def conv (r : FinRel K V) : FinRel V K := ⟨r.vals, r.keys, r.len.symm⟩

theorem mem_rep {r : FinRel K V} {k : K} {v : V} :
    r.rep k v ↔ ∃ i, ∃ h : i < r.keys.size, ∃ h' : i < r.vals.size, r.keys[i] = k ∧ r.vals[i] = v := by
  simp only [rep, toList, rel, List.mem_iff_getElem, List.getElem_zip, List.length_zip, Array.length_toList,
    Array.getElem_toList, Prod.mk.injEq]
  exact ⟨fun ⟨i, h, e⟩ => ⟨i, by omega, by omega, e⟩, fun ⟨i, h, h', e⟩ => ⟨i, by omega, e⟩⟩

theorem rep_conv (r : FinRel K V) : r.conv.rep = r.rep° :=
  hom_ext fun _ _ => mem_rep.trans (Iff.trans ⟨fun ⟨i, h, h', a, b⟩ => ⟨i, h', h, b, a⟩,
    fun ⟨i, h, h', a, b⟩ => ⟨i, h', h, b, a⟩⟩ mem_rep.symm)

/-- `sel(k) : (k',v) ↦ v` when `k' = k`. -/
def sel [DecidableEq K] (k : K) (p : K × V) : Option V := if p.1 = k then some p.2 else none

/-- Unsorted lookup, a linear scan of the keys. -/
def scanLookup [DecidableEq K] (r : FinRel K V) (k : K) : List V := r.toList.filterMap (sel k)

theorem scanLookup_rep [DecidableEq K] (r : FinRel K V) :
    (graph r.scanLookup : (⟨K⟩ : RelSet.{0}) ⟶ ⟨List V⟩) ≫ lmem V = r.rep :=
  hom_ext fun k v => by
    show (∃ l, l = r.scanLookup k ∧ v ∈ l) ↔ (k, v) ∈ r.toList
    simp only [exists_eq_left, scanLookup, List.mem_filterMap, sel]
    refine ⟨fun ⟨⟨a, b⟩, hm, hs⟩ => ?_, fun h => ⟨(k, v), h, if_pos rfl⟩⟩
    by_cases e : a = k
    · rw [if_pos e] at hs; cases Option.some.inj hs; exact e ▸ hm
    · rw [if_neg e] at hs; exact absurd hs (by simp)

theorem mem_scanLookup [DecidableEq K] (r : FinRel K V) (k : K) (v : V) : v ∈ r.scanLookup k ↔ r.rep k v :=
  Iff.of_eq (congrFun (congrFun ((hom_ext fun _ _ => ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ h⟩ :
    (fun k v => v ∈ r.scanLookup k : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) = graph r.scanLookup ≫ lmem V).trans
      (scanLookup_rep r)) k) v)

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
      exact pairwise_mergeSort_on Prod.fst _ }

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

/-! ## The relation algebra on arrays -/

namespace FinRel

open SortedRel

/-- `R ∪ S`: append the arrays. -/
def union (r s : FinRel K V) : FinRel K V :=
  ⟨r.keys ++ s.keys, r.vals ++ s.vals, by rw [Array.size_append, Array.size_append, r.len, s.len]⟩

theorem rep_union (r s : FinRel K V) : (union r s).rep = r.rep ∪ s.rep := by
  show rel ((r.keys ++ s.keys).toList.zip (r.vals ++ s.vals).toList) = _
  rw [Array.toList_append, Array.toList_append,
    List.zip_append (by rw [Array.length_toList, Array.length_toList, r.len]), rel_append]; rfl

/-- `R graph(f)`: map the values. -/
def map (f : V → V') (r : FinRel K V) : FinRel K V' := ⟨r.keys, r.vals.map f, by rw [Array.size_map]; exact r.len⟩

theorem toList_map (f : V → V') (r : FinRel K V) : (map f r).toList = r.toList.map (Prod.map id f) := by
  show r.keys.toList.zip (r.vals.map f).toList = _
  rw [Array.toList_map, List.zip_map_right]; rfl

theorem rep_map (f : V → V') (r : FinRel K V) : (map f r).rep = r.rep ≫ graph f := by
  show rel (map f r).toList = _
  rw [toList_map, rel_map]
  show (graph fun x : K => x)° ≫ r.rep ≫ graph f = _
  rw [graph_id, recip_id, Cat.id_comp]

/-- `R ∩ P`: keep the pairs a decidable, possibly infinite, relation `P` holds of. -/
def filter (p : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) [∀ k v, Decidable (p k v)] (r : FinRel K V) : FinRel K V :=
  ofList (r.toList.filter fun q => decide (p q.1 q.2))

theorem rep_filter (p : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) [∀ k v, Decidable (p k v)] (r : FinRel K V) :
    (filter p r).rep = r.rep ∩ p :=
  ((rep_ofList _).trans (rel_filter _ _)).trans (congrArg (r.rep ∩ ·) (hom_ext fun _ _ => decide_eq_true_iff))

theorem toList_conv (r : FinRel K V) : r.conv.toList = r.toList.map Prod.swap := by
  show r.vals.toList.zip r.keys.toList = (r.keys.toList.zip r.vals.toList).map Prod.swap
  generalize r.keys.toList = ks; generalize r.vals.toList = vs
  induction ks generalizing vs with
  | nil => cases vs <;> rfl
  | cons k ks ih => cases vs with
    | nil => rfl
    | cons v vs => simp [ih]

/-- `xs × xs`, every pair of members: a relation filtered on it is that relation restricted to `xs`. -/
def square (xs : List K) : FinRel K K := ofList (xs.flatMap fun w => xs.map (w, ·))

theorem mem_filter_square (p : (⟨K⟩ : RelSet.{0}) ⟶ ⟨K⟩) [∀ k v, Decidable (p k v)] (xs : List K) (w z : K) :
    (w, z) ∈ (filter p (square xs)).toList ↔ w ∈ xs ∧ z ∈ xs ∧ p w z := by
  simp [filter, square, toList_ofList, List.mem_filter, List.mem_flatMap, and_assoc]

variable [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

attribute [local instance] lexOrd

/-- Sort the pairs by `(key, value)` and drop the repeats, which sorting puts side by side. -/
def dedup [Ord V] (r : FinRel K V) : FinRel K V := ofList (uniq (r.toList.mergeSort fun a b => (compare a b).isLE))

omit [Std.TransOrd K] in
theorem rep_dedup [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] (r : FinRel K V) : (dedup r).rep = r.rep :=
  (rep_ofList _).trans <| hom_ext fun k v => (mem_uniq (k, v) _).trans (List.mergeSort_perm _ _).mem_iff

theorem nodup_dedup [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] (r : FinRel K V) : (dedup r).toList.Nodup := by
  simp only [dedup, toList_ofList]; exact nodup_uniq (pairwise_mergeSort_on id _)

/-- A lookup in the sorted copy denotes the relation itself. -/
theorem lookup_sortByKey (s : FinRel K V) :
    (fun k v => v ∈ (sortByKey s).lookup k : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) = s.rep :=
  calc (fun k v => v ∈ (sortByKey s).lookup k : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩)
      = graph (sortByKey s).lookup ≫ lmem V := hom_ext fun _ _ => ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ h⟩
    _ = (sortByKey s).rep := lookup_rep _
    _ = s.rep := rep_sortByKey _

theorem mem_lookup_sortByKey (s : FinRel K V) (k : K) (v : V) : v ∈ (sortByKey s).lookup k ↔ s.rep k v :=
  Iff.of_eq (congrFun (congrFun (lookup_sortByKey s) k) v)

/-- `R ∩ S`: keep the pairs of `r` that the sorted `s` holds. -/
def inter [DecidableEq V] (r s : FinRel K V) : FinRel K V :=
  let t := sortByKey s
  filter (fun k v => v ∈ t.lookup k) r

theorem rep_inter [DecidableEq V] (r s : FinRel K V) : (inter r s).rep = r.rep ∩ s.rep :=
  calc (inter r s).rep
      = r.rep ∩ (fun k v => v ∈ (sortByKey s).lookup k : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) := rep_filter _ _
    _ = r.rep ∩ s.rep := by rw [lookup_sortByKey]

/-- `R ⊑ S`: every pair of `r` is in the sorted `s`. -/
def le [DecidableEq V] (r s : FinRel K V) : Bool :=
  let t := sortByKey s
  r.toList.all fun q => decide (q.2 ∈ t.lookup q.1)

theorem le_iff_rep [DecidableEq V] (r s : FinRel K V) : le r s = true ↔ r.rep ⊑ s.rep := by
  simp only [le, List.all_eq_true, decide_eq_true_eq, mem_lookup_sortByKey, le_iff]
  exact ⟨fun h k v hr => h (k, v) hr, fun h q hq => h q.1 q.2 hq⟩

/-- `R S`: sort `s` once, then for each `(a,b)` of `r` look `b` up in it. -/
def comp (r : FinRel A K) (s : FinRel K V) : FinRel A V :=
  let t := sortByKey s
  ofList (r.toList.flatMap fun p => (t.lookup p.2).map (p.1, ·))

theorem rep_comp (r : FinRel A K) (s : FinRel K V) : (comp r s).rep = r.rep ≫ s.rep :=
  (rep_ofList _).trans <| hom_ext fun a c => by
    simp only [rel, List.mem_flatMap, List.mem_map, Prod.mk.injEq, mem_lookup_sortByKey, comp_apply]
    exact ⟨fun ⟨⟨_, b⟩, hp, _, hc, e1, e2⟩ => e1 ▸ e2 ▸ ⟨b, hp, hc⟩,
      fun ⟨b, hp, hc⟩ => ⟨(a, b), hp, c, hc, rfl, rfl⟩⟩

/-- `R \ S` on `ran R`: for `b` of `r` and `c` of `s`, keep `(b,c)` when every `a` of `b`'s run in the
    sorted `r°` has `a s c`.  Off `ran R` the quotient holds of every `c`, which no array holds. -/
def div [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A] [DecidableEq V] [Ord V] (r : FinRel A K)
    (s : FinRel A V) : FinRel K V :=
  let rc := sortByKey r.conv
  let ss := sortByKey s
  dedup (ofList (r.toList.flatMap fun p =>
    (s.toList.filter fun q => (rc.lookup p.2).all fun a => decide (q.2 ∈ ss.lookup a)).map (p.2, ·.2)))

theorem rep_div [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A] [DecidableEq V] [Ord V] [Std.TransOrd V]
    [Std.LawfulEqOrd V] (r : FinRel A K) (s : FinRel A V) : (div r s).rep = ran r.rep ≫ (r.rep \ s.rep) :=
  (rep_dedup _).trans <| (rep_ofList _).trans <| hom_ext fun b c => by
    simp only [rel, List.mem_flatMap, List.mem_map, List.mem_filter, List.all_eq_true, decide_eq_true_eq,
      mem_lookup_sortByKey, rep_conv, recip_apply, Prod.mk.injEq, comp_apply]
    exact ⟨fun ⟨⟨a, _⟩, hp, ⟨_, _⟩, ⟨_, hall⟩, e1, e2⟩ => e1 ▸ e2 ▸ ⟨_, ⟨rfl, a, hp, hp⟩, hall⟩,
      fun ⟨_, ⟨(e : b = _), a, ha, _⟩, hall⟩ => by subst e; exact ⟨(a, b), ha, (a, c), ⟨hall a ha, hall⟩, rfl, rfl⟩⟩

theorem nodup_div [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A] [DecidableEq V] [Ord V] [Std.TransOrd V]
    [Std.LawfulEqOrd V] (r : FinRel A K) (s : FinRel A V) : (div r s).toList.Nodup := nodup_dedup _

/-- `dom R`: the pair `(k,k)` for each key `k` of `r`, once. -/
def dom (r : FinRel K V) : FinRel K K := dedup (ofList (r.toList.map fun p => (p.1, p.1)))

theorem rep_dom (r : FinRel K V) : (dom r).rep = Alg.dom r.rep :=
  (rep_dedup _).trans <| (rep_ofList _).trans <| hom_ext fun k k' =>
    ⟨fun h => by
      obtain ⟨⟨a, b⟩, hm, he⟩ := List.mem_map.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨rfl, b, hm, hm⟩,
     fun ⟨(e : k = k'), v, hv, _⟩ => by subst e; exact List.mem_map.2 ⟨(k, v), hv, rfl⟩⟩

omit [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] in
/-- `ran R = dom R°`. -/
def ran [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] (r : FinRel K V) : FinRel V V := dom r.conv

omit [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] in
theorem rep_ran [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] (r : FinRel K V) : (ran r).rep = Alg.ran r.rep :=
  calc (ran r).rep
      = Alg.dom r.conv.rep := rep_dom _
    _ = Alg.dom r.rep° := by rw [rep_conv]

end FinRel

open FinRel in
/-- The first pair is some pair: `graph(head? ∘ toList ∘ F) ⊑ graph(rep ∘ F) orNone(∋)`. -/
theorem head?_toList_le {X : Type} (F : X → FinRel K V) :
    (graph fun x => (F x).toList.head? : (⟨X⟩ : RelSet.{0}) ⟶ ⟨Option (K × V)⟩)
      ⊑ (graph fun x => (F x).rep : (⟨X⟩ : RelSet.{0}) ⟶ ⟨(⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩⟩)
        ≫ orNone (relMem ⟨K⟩ ⟨V⟩) :=
  calc (graph fun x => (F x).toList.head? : (⟨X⟩ : RelSet.{0}) ⟶ ⟨Option (K × V)⟩)
      = graph (fun x => (F x).toList) ≫ graph List.head? := (graph_comp _ _).symm
    _ ⊑ graph (fun x => (F x).toList) ≫ orNone (lmem _) := comp_mono_left _ head?_le_orNone
    _ = orNone (graph (fun x => (F x).toList) ≫ lmem _) := graph_orNone _ _
    _ = orNone (graph (fun x => (F x).rep) ≫ relMem ⟨K⟩ ⟨V⟩) :=
        congrArg orNone (hom_ext fun _ _ => ⟨fun ⟨_, (hl : _ = _), hm⟩ => ⟨_, rfl, by subst hl; exact hm⟩,
          fun ⟨_, (hR : _ = _), h⟩ => ⟨_, rfl, by subst hR; exact h⟩⟩)
    _ = graph (fun x => (F x).rep) ≫ orNone (relMem ⟨K⟩ ⟨V⟩) := (graph_orNone _ _).symm

/-! ## A relation as a sum of representations -/

/-- A relation `K ⟶ V` held as the pairs of a `FinRel`, as its `Λ` form `k ↦` the list of values `k` is
    related to (a fiber enumerated, the keys possibly infinite), or as a decidable test such as `(· > ·)`.
    An operation enumerates whatever one argument can; a composite whose first factor is a `test` would
    have to enumerate the middle type, and is not formed. -/
inductive RelRep (K V : Type) where
  | pairs (r : FinRel K V)
  | enum (f : K → List V)
  | test (t : K → V → Bool)

namespace RelRep

/-- The relation a representation denotes. -/
def rel : RelRep K V → ((⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩)
  | pairs r => r.rep
  | enum f => fun k v => v ∈ f k
  | test t => fun k v => t k v = true

/-- The graph of `g`: one value in each fiber. -/
def ofFn (g : K → V) : RelRep K V := enum fun k => [g k]

theorem rel_ofFn (g : K → V) : (ofFn g).rel = (graph g : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) :=
  hom_ext fun k v => List.mem_singleton.trans (Iff.of_eq (graph_apply g k v).symm)

variable [DecidableEq K] [DecidableEq V]

/-- The membership test of `rel`. -/
def mem : RelRep K V → K → V → Bool
  | pairs r => fun k v => decide ((k, v) ∈ r.toList)
  | enum f => fun k v => decide (v ∈ f k)
  | test t => t

theorem mem_iff_rel : (R : RelRep K V) → (k : K) → (v : V) → (R.mem k v = true ↔ R.rel k v)
  | pairs _, _, _ => decide_eq_true_iff
  | enum _, _, _ => decide_eq_true_iff
  | test _, _, _ => Iff.rfl

/-- `R°`: a `FinRel` swaps its arrays, a fiber list becomes the test `v ∈ f(k)`, a test flips. -/
def conv : RelRep K V → RelRep V K
  | pairs r => pairs r.conv
  | enum f => test fun v k => decide (v ∈ f k)
  | test t => test fun v k => t k v

omit [DecidableEq K] in
theorem rel_conv (R : RelRep K V) : R.conv.rel = R.rel° := by
  cases R with
  | pairs r => exact FinRel.rep_conv r
  | enum f => exact hom_ext fun _ _ => decide_eq_true_iff
  | test t => exact hom_ext fun _ _ => Iff.rfl

/-- `R ∩ S`: an enumerating side is filtered by the other side's test; two tests conjoin. -/
def inter : RelRep K V → RelRep K V → RelRep K V
  | pairs r, S => pairs (FinRel.filter (fun k v => S.mem k v = true) r)
  | R, pairs s => pairs (FinRel.filter (fun k v => R.mem k v = true) s)
  | enum f, S => enum fun k => (f k).filter (S.mem k ·)
  | R, enum g => enum fun k => (g k).filter (R.mem k ·)
  | R, S => test fun k v => R.mem k v && S.mem k v

theorem rel_inter (R S : RelRep K V) : (inter R S).rel = R.rel ∩ S.rel := by
  cases R <;> cases S <;>
    simp only [inter, RelRep.rel, FinRel.rep_filter] <;>
    exact hom_ext fun k v => by
      simp only [inter_apply, List.mem_filter, mem_iff_rel, Bool.and_eq_true, RelRep.rel, and_comm]

/-- `R ∪ S`: two `FinRel`s append their arrays, two enumerating sides append their fibers; a test on
    either side makes the union a test. -/
def union : RelRep K V → RelRep K V → RelRep K V
  | pairs r, pairs s => pairs (FinRel.union r s)
  | pairs r, enum g => enum fun k => r.scanLookup k ++ g k
  | enum f, pairs s => enum fun k => f k ++ s.scanLookup k
  | enum f, enum g => enum fun k => f k ++ g k
  | R, S => test fun k v => R.mem k v || S.mem k v

theorem rel_union (R S : RelRep K V) : (union R S).rel = R.rel ∪ S.rel := by
  cases R <;> cases S <;> first
    | exact FinRel.rep_union _ _
    | exact hom_ext fun k v => (Iff.of_eq (Bool.or_eq_true _ _)).trans ((or_congr (mem_iff_rel _ k v) (mem_iff_rel _ k v)).trans
        (Iff.of_eq (union_apply _ _ k v).symm))
    | exact hom_ext fun k v => by simp only [union, RelRep.rel, List.mem_append, FinRel.mem_scanLookup, union_apply]

/-- `R S`, first `R` then `S`.  An enumerating `R` hands each of its values to `S`: a `FinRel` or a fiber
    list second is looked up, a test second is tried on each.  A `test` first would have to enumerate
    the middle type, so it gives `none`. -/
def comp [DecidableEq C] : RelRep K V → RelRep V C → Option (RelRep K C)
  | pairs r, pairs s => some (pairs (FinRel.ofList (r.toList.flatMap fun p => (s.scanLookup p.2).map (p.1, ·))))
  | pairs r, enum h => some (pairs (FinRel.ofList (r.toList.flatMap fun p => (h p.2).map (p.1, ·))))
  | pairs r, test t => some (test fun k c => (r.scanLookup k).any (t · c))
  | enum f, pairs s => some (enum fun k => (f k).flatMap s.scanLookup)
  | enum f, enum h => some (enum fun k => (f k).flatMap h)
  | enum f, test t => some (test fun k c => (f k).any (t · c))
  | test _, _ => none

theorem rel_comp [DecidableEq C] {R : RelRep K V} {S : RelRep V C} {T : RelRep K C} (h : comp R S = some T) :
    T.rel = R.rel ≫ S.rel := by
  cases R <;> cases S <;> simp only [comp, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> first
    | exact (FinRel.rep_ofList _).trans <| hom_ext fun a c => by
        simp only [RelSet.rel, RelRep.rel, List.mem_flatMap, List.mem_map, Prod.mk.injEq, FinRel.mem_scanLookup,
          comp_apply]
        exact ⟨fun ⟨⟨_, b⟩, hp, _, hc, e1, e2⟩ => e1 ▸ e2 ▸ ⟨b, hp, hc⟩,
          fun ⟨b, hp, hc⟩ => ⟨(a, b), hp, c, hc, rfl, rfl⟩⟩
    | exact hom_ext fun k c => by
        simp only [RelRep.rel, List.mem_flatMap, List.any_eq_true, FinRel.mem_scanLookup, comp_apply]

/-! ### `est` and `thin` on an enumerated fibre -/

/-- Each fibre of `R` as a list, when `R` can enumerate it: a `FinRel` is scanned, a fibre list is
    itself; a `test` enumerates nothing. -/
def fibre? : RelRep K V → Option (K → List V)
  | pairs r => some r.scanLookup
  | enum f => some f
  | test _ => none

omit [DecidableEq V] in
theorem mem_fibre? {R : RelRep K V} {f : K → List V} (h : R.fibre? = some f) (k : K) (v : V) :
    v ∈ f k ↔ R.rel k v := by
  cases R <;> simp only [fibre?, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact FinRel.mem_scanLookup _ k v
  · exact Iff.rfl

/-- `est(le)` on one list: the members `le`-below every member. -/
def estList (le : V → V → Bool) (xs : List V) : List V := xs.filter fun v => xs.all (le v ·)

/-- `thin(Q)` on one list: a member is dropped when a kept member is `q`-below it, and otherwise
    kept in place of the kept members it is `q`-below. -/
def thinList (q : V → V → Bool) : List V → List V
  | [] => []
  | z :: zs => if (thinList q zs).any (q · z) then thinList q zs else z :: (thinList q zs).filter (!q z ·)

omit [DecidableEq K] [DecidableEq V] in
/-- For a preorder `q`, `thinList q xs` is a `thin(q)` choice: it lies in `xs`, and every member of
    `xs` has a `q`-lower bound in it. -/
theorem thinList_spec {q : V → V → Bool} (hr : ∀ v, q v v) (ht : ∀ u v w, q u v → q v w → q u w) :
    ∀ xs : List V, (∀ y ∈ thinList q xs, y ∈ xs) ∧ ∀ z ∈ xs, ∃ w ∈ thinList q xs, q w z
  | [] => ⟨fun _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | z :: zs => by
    obtain ⟨hsub, hdom⟩ := thinList_spec hr ht zs
    simp only [thinList]
    split
    · rename_i hz
      obtain ⟨w, hw, hwz⟩ := List.any_eq_true.1 hz
      refine ⟨fun y hy => List.mem_cons_of_mem _ (hsub y hy), fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨w, hw, hwz⟩
      · exact hdom x hx
    · refine ⟨fun y hy => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (hsub y (List.mem_filter.1 hy).1)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨x, List.mem_cons.2 (Or.inl rfl), hr x⟩
        · obtain ⟨w, hw, hwx⟩ := hdom x hx
          cases hzw : q z w
          · exact ⟨w, List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hw, by simp [hzw]⟩), hwx⟩
          · exact ⟨z, List.mem_cons.2 (Or.inl rfl), ht z w x hzw hwx⟩

open PowerAllegory

/-- `Λ(R) est(L)`: each fibre cut to its `L`-least members; `none` on a `test`. -/
def est (L : RelRep V V) (R : RelRep K V) : Option (RelRep K V) :=
  R.fibre?.map fun f => enum fun k => estList L.mem (f k)

theorem rel_est {L : RelRep V V} {R T : RelRep K V} (h : est L R = some T) :
    T.rel = Λ R.rel ≫ Freyd.Alg.est L.rel := by
  cases hf : R.fibre? with
  | none => simp [est, hf] at h
  | some f =>
    simp only [est, hf, Option.map_some, Option.some.injEq] at h
    subst h
    exact hom_ext fun k v => by
      rw [Λ_comp_est_apply]
      simp only [RelRep.rel, estList, List.mem_filter, List.all_eq_true, mem_iff_rel, mem_fibre? hf]

/-- `Λ(R) thin(Q)`: each fibre cut by `thinList`; `none` on a `test`. -/
def thin (Q : RelRep V V) (R : RelRep K V) : Option (RelRep K V) :=
  R.fibre?.map fun f => enum fun k => thinList Q.mem (f k)

/-- For a preorder `Q`, each computed fibre is a `thin(Q)` choice of `R`'s fibre. -/
theorem rel_thin {Q : RelRep V V} {R T : RelRep K V} (hr : 𝟙 _ ⊑ Q.rel) (ht : Q.rel ≫ Q.rel ⊑ Q.rel)
    (h : thin Q R = some T) : Λ T.rel ⊑ Λ R.rel ≫ thinRel Q.rel := by
  cases hf : R.fibre? with
  | none => simp [thin, hf] at h
  | some f =>
    simp only [thin, hf, Option.map_some, Option.some.injEq] at h
    subst h
    have hs := thinList_spec (q := Q.mem)
      (fun v => (mem_iff_rel Q v v).2 (le_iff.mp hr v v (by rw [id_apply])))
      (fun u v w h1 h2 => (mem_iff_rel Q u w).2
        (le_iff.mp ht u w ⟨v, (mem_iff_rel Q u v).1 h1, (mem_iff_rel Q v w).1 h2⟩))
    rw [Λ_eq_classifier, Λ_eq_classifier]
    refine le_iff.mpr fun k G hG => ⟨fun v => R.rel k v, rfl, ?_⟩
    have hG' : G = fun v => v ∈ thinList Q.mem (f k) := hG
    subst hG'
    exact (thinRel_pt _ _ _).2 ⟨fun y hy => (mem_fibre? hf k y).1 ((hs (f k)).1 y hy),
      fun z hz => ((hs (f k)).2 z ((mem_fibre? hf k z).2 hz)).imp
        fun w ⟨hw, hq⟩ => ⟨(mem_iff_rel Q w z).1 hq, hw⟩⟩

end RelRep

end Freyd.Alg.RelSet
