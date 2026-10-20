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
public import AOP.A6_ConsList
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

/-- `toList` zipping the arrays: the compiled `List.zip` is not tail-recursive, one frame per pair. -/
def toListTR (r : FinRel K V) : List (K × V) := (r.keys.zip r.vals).toList

@[csimp] theorem toList_eq_toListTR : @toList = @toListTR :=
  funext fun _ => funext fun _ => funext fun r => (Array.toList_zip ..).symm

def rep (r : FinRel K V) : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩ := rel r.toList

/-- Two `map`s, not `unzip`: the compiled `unzip` is a `foldr`, one stack frame per pair. -/
def ofList (l : List (K × V)) : FinRel K V := ⟨(l.map Prod.fst).toArray, (l.map Prod.snd).toArray, by simp⟩

theorem toList_ofList (l : List (K × V)) : (ofList l).toList = l := by
  simp only [toList, ofList, List.toList_toArray, ← List.unzip_fst, ← List.unzip_snd,
    List.zip_unzip]

theorem rep_ofList (l : List (K × V)) : (ofList l).rep = rel l := congrArg rel (toList_ofList l)

/-- `ofList` in one pass, each pair pushed onto the two arrays: the two `map`s build and reverse two lists. -/
def ofListGo : List (K × V) → FinRel K V → FinRel K V
  | [], r => r
  | (k, v) :: l, r => ofListGo l ⟨r.keys.push k, r.vals.push v, by simp [r.len]⟩

def ofListTR (l : List (K × V)) : FinRel K V := ofListGo l ⟨#[], #[], rfl⟩

theorem ofListGo_toList : (l : List (K × V)) → (r : FinRel K V) →
    (ofListGo l r).keys.toList = r.keys.toList ++ l.map Prod.fst ∧
      (ofListGo l r).vals.toList = r.vals.toList ++ l.map Prod.snd
  | [], _ => by simp [ofListGo]
  | (k, v) :: l, r => by
    obtain ⟨h1, h2⟩ := ofListGo_toList l ⟨r.keys.push k, r.vals.push v, by simp [r.len]⟩
    simp [ofListGo, h1, h2]

@[csimp] theorem ofList_eq_ofListTR : @ofList = @ofListTR := by
  funext K V l
  have h := ofListGo_toList l ⟨#[], #[], rfl⟩
  unfold ofListTR ofList
  generalize ofListGo l ⟨#[], #[], rfl⟩ = r at h ⊢
  obtain ⟨ks, vs, _⟩ := r
  simp only [List.nil_append] at h
  simp only [mk.injEq]
  exact ⟨by rw [← h.1], by rw [← h.2]⟩

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

/-! The fibre of a list of pairs, `l.filterMap (sel k)`, against the list operations that build one. -/

theorem scanLookup_ofList [DecidableEq K] (l : List (K × V)) : (ofList l).scanLookup = fun k => l.filterMap (sel k) :=
  funext fun _ => by rw [scanLookup, toList_ofList]

/-- Each pair `(a,b)` sent to `(a,c)` for every `c` of `g(a)(b)`: the fibre of `k` is `g(k)` over the fibre. -/
theorem filterMap_sel_flatMap [DecidableEq K] {W : Type} (g : K → V → List W) (k : K) : (l : List (K × V)) →
    (l.flatMap fun p => (g p.1 p.2).map (p.1, ·)).filterMap (sel k) = (l.filterMap (sel k)).flatMap (g k)
  | [] => rfl
  | (a, b) :: l => by
    by_cases h : a = k
    · subst h; simp [sel, List.filterMap_map, Function.comp_def, filterMap_sel_flatMap g a l]
    · simp [sel, h, List.filterMap_map, Function.comp_def, filterMap_sel_flatMap g k l]

theorem filterMap_sel_filter [DecidableEq K] (p : K → V → Bool) (k : K) : (l : List (K × V)) →
    (l.filter fun q => p q.1 q.2).filterMap (sel k) = (l.filterMap (sel k)).filter (p k)
  | [] => rfl
  | (a, b) :: l => by
    by_cases h : a = k
    · subst h; cases hp : p a b <;> simp [sel, hp, filterMap_sel_filter p a l]
    · cases hp : p a b <;> simp [sel, h, hp, filterMap_sel_filter p k l]

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
      simp only [ofList, Array.toList_map, List.toList_toArray, List.pairwise_map]
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

theorem toList_union (r s : FinRel K V) : (union r s).toList = r.toList ++ s.toList := by
  show (r.keys ++ s.keys).toList.zip (r.vals ++ s.vals).toList = _
  rw [Array.toList_append, Array.toList_append,
    List.zip_append (by rw [Array.length_toList, Array.length_toList, r.len])]; rfl

/-- The fibre of `R ∪ S` is `R`'s, then `S`'s. -/
theorem scanLookup_union [DecidableEq K] (r s : FinRel K V) :
    (union r s).scanLookup = fun k => r.scanLookup k ++ s.scanLookup k :=
  funext fun _ => by rw [scanLookup, toList_union, List.filterMap_append]; rfl

/-- The fibre of `R ∩ P` is `R`'s, filtered by `P`. -/
theorem scanLookup_filter [DecidableEq K] (p : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) [∀ k v, Decidable (p k v)] (r : FinRel K V) :
    (filter p r).scanLookup = fun k => (r.scanLookup k).filter fun v => decide (p k v) :=
  funext fun k => by rw [filter, scanLookup_ofList]; exact filterMap_sel_filter (fun k v => decide (p k v)) k _

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

/-! ## Fibres and keys by hashing -/

/-- A bucket of `HTab`: one cell per key holding the key and its entry, where a `List (K × B)` takes a
    cons and a pair — one allocation and one pointer less per key. -/
inductive Bucket (K B : Type) where
  | nil
  | cons (k : K) (b : B) (t : Bucket K B)

/-- A chained hash table from `K` to `B`: a key's hash picks its bucket, and a bucket lists each key it
    holds once, with its entry.  A structure and not a function `K → Option B`, because the compiler
    eta-expands a function-valued definition, which would rebuild the table at every key.  Hand-rolled
    rather than `Std.HashMap`, whose lemmas use `Classical.choice`. -/
structure HTab (K B : Type) where
  buckets : Array (Bucket K B)
  size_pos : 0 < buckets.size

namespace HTab

variable {B : Type}

/-- The entry a bucket holds for `a`. -/
def look [DecidableEq K] : Bucket K B → K → Option B
  | .nil, _ => none
  | .cons k' b t, a => if k' = a then some b else look t a

/-- Set `k`'s entry in a bucket to `f` of its old one; a key the bucket lacks goes at its end. -/
def alt [DecidableEq K] (f : Option B → B) : Bucket K B → K → Bucket K B
  | .nil, k => .cons k (f none) .nil
  | .cons k' b t, k => if k' = k then .cons k' (f (some b)) t else .cons k' b (alt f t k)

theorem look_alt [DecidableEq K] (f : Option B → B) (l : Bucket K B) (k a : K) :
    look (alt f l k) a = if k = a then some (f (look l k)) else look l a := by
  induction l with
  | nil => by_cases h : k = a <;> simp [look, alt, h]
  | cons k' b t ih =>
    by_cases h1 : k' = k
    · subst h1; by_cases h2 : k' = a <;> simp [look, alt, h2]
    · by_cases h2 : k' = a
      · subst h2; simp [look, alt, h1, Ne.symm h1]
      · simp [look, alt, h1, h2, ih]

variable [DecidableEq K] [Hashable K]

/-- No entries, in `n + 1` buckets. -/
def empty (n : Nat) : HTab K B := ⟨Array.replicate (n + 1) .nil, by simp⟩

def slot (x : HTab K B) (k : K) : Nat := (hash k).toNat % x.buckets.size

omit [DecidableEq K] in
theorem slot_lt (x : HTab K B) (k : K) : x.slot k < x.buckets.size := Nat.mod_lt _ x.size_pos

/-- The entry of `k`, from its bucket. -/
def find? (x : HTab K B) (k : K) : Option B := look (x.buckets[x.slot k]'(x.slot_lt k)) k

/-- Set the entry of `k` to `f` of its old one, in place when the table is unshared. -/
def alter (x : HTab K B) (k : K) (f : Option B → B) : HTab K B :=
  ⟨x.buckets.modify (x.slot k) (alt f · k), by simpa using x.size_pos⟩

theorem find?_empty (n : Nat) (a : K) : (empty n : HTab K B).find? a = none := by
  simp [find?, empty, look]

theorem find?_alter (x : HTab K B) (k : K) (f : Option B → B) (a : K) :
    (x.alter k f).find? a = if k = a then some (f (x.find? k)) else x.find? a := by
  by_cases h : k = a
  · subst h; simp [find?, alter, slot, Array.getElem_modify, look_alt]
  · simp only [find?, alter, slot, Array.size_modify, Array.getElem_modify, if_neg h]
    split
    · rw [look_alt, if_neg h]
    · rfl

end HTab

/-- The fibres of a `FinRel`: each key's values in array order. -/
abbrev Fibres (K V : Type) := HTab K (Array V)

namespace Fibres

variable [DecidableEq K] [Hashable K]

/-- The fibre of `k`. -/
def get (x : Fibres K V) (k : K) : List V := ((x.find? k).getD #[]).toList

/-- Append `v` to the fibre of `k`. -/
def push (x : Fibres K V) (k : K) (v : V) : Fibres K V := x.alter k fun
  | some a => a.push v
  | none => #[v]

theorem get_empty (n : Nat) (a : K) : Fibres.get (HTab.empty n : Fibres K V) a = [] := by
  simp [get, HTab.find?_empty]

theorem get_push (x : Fibres K V) (k : K) (v : V) (a : K) :
    (x.push k v).get a = x.get a ++ if k = a then [v] else [] := by
  simp only [get, push, HTab.find?_alter]
  by_cases h : k = a
  · subst h; cases x.find? k <;> simp
  · simp [h]

end Fibres

/-- The fibres of `r`, made in one pass over its pairs, one bucket per pair. -/
def FinRel.fibres [DecidableEq K] [Hashable K] (r : FinRel K V) : Fibres K V :=
  r.toList.foldl (fun x p => x.push p.1 p.2) (HTab.empty r.keys.size)

/-- **The hashed fibre is the scanned one**, order and repeats kept. -/
theorem FinRel.get_fibres [DecidableEq K] [Hashable K] (r : FinRel K V) : r.fibres.get = r.scanLookup :=
  funext fun a => by
    have go : ∀ (l : List (K × V)) (x : Fibres K V),
        (l.foldl (fun x p => x.push p.1 p.2) x).get a = x.get a ++ l.filterMap (sel a) := by
      intro l
      induction l with
      | nil => intro x; simp
      | cons p l ih =>
        intro x
        rw [List.foldl_cons, ih, Fibres.get_push]
        by_cases h : p.1 = a <;> simp [sel, h]
    rw [fibres, go, Fibres.get_empty]
    rfl

/-- One step of `hashDedup`: a key with no fibre yet gets one and is listed. -/
def dedupStep [DecidableEq K] [Hashable K] (s : Fibres K Unit × Array K) (k : K) : Fibres K Unit × Array K :=
  if (s.1.get k).isEmpty then (s.1.push k (), s.2.push k) else s

/-- `eraseDups` in one pass: each key once, in order of first appearance, the keys seen kept as fibres. -/
def hashDedup [DecidableEq K] [Hashable K] (l : List K) : List K :=
  (l.foldl dedupStep (HTab.empty l.length, #[])).2.toList

theorem hashDedup_eq [DecidableEq K] [Hashable K] (l : List K) : hashDedup l = l.eraseDups := by
  have go : ∀ (l : List K) (s : Fibres K Unit) (acc : Array K), (∀ k, (s.get k).isEmpty = false ↔ k ∈ acc.toList) →
      (l.foldl dedupStep (s, acc)).2.toList = acc.toList ++ (l.filter fun k => !decide (k ∈ acc.toList)).eraseDups := by
    intro l
    induction l with
    | nil => intro s acc _; simp [List.eraseDups]
    | cons a l ih =>
      intro s acc hs
      rw [List.foldl_cons, dedupStep]
      by_cases ha : a ∈ acc.toList
      · rw [if_neg (by rw [(hs a).2 ha]; simp), ih s acc hs]
        have ha' : a ∈ acc := by simpa using ha
        simp [List.filter_cons, ha']
      · rw [if_pos (by cases h : (s.get a).isEmpty <;> simp_all),
          ih _ _ fun k => by
            rw [Fibres.get_push, Array.toList_push, List.mem_append, List.mem_singleton, ← hs k]
            by_cases e : a = k
            · simp [e]
            · simp [e, show k ≠ a from fun h => e h.symm]]
        simp only [List.filter_cons, ha, decide_false, Bool.not_false, if_true, List.eraseDups_cons,
          Array.toList_push, List.append_assoc, List.singleton_append, List.filter_filter]
        congr 3
        apply List.filter_congr
        intro x _
        by_cases h1 : x = a <;> by_cases h2 : x ∈ acc.toList <;> simp [h1, h2]
  have e : l.filter (fun _ => true) = l := List.filter_eq_self.2 fun _ _ => rfl
  simpa [hashDedup, e] using go l _ #[] (by simp [Fibres.get_empty])

/-- How the fibres of a `FinRel` keyed by `K` are looked up, and a list of keys listed once: by
    hashing when `K` has a `Hashable`, else by the scans `scanLookup` and `eraseDups`.  Each answer
    equals the scan's (`get_build`, `dedup_eq`), so a law proved of the scan holds of either; `build`
    makes the index once, and `get` answers each key from it. -/
class FibreIndex (K : Type) [DecidableEq K] where
  Index : Type → Type
  build {V : Type} : FinRel K V → Index V
  get {V : Type} : Index V → K → List V
  get_build {V : Type} (r : FinRel K V) : get (build r) = r.scanLookup
  dedup : List K → List K
  dedup_eq (l : List K) : dedup l = l.eraseDups

attribute [simp] FibreIndex.get_build FibreIndex.dedup_eq

/-- No hash: the scans themselves. -/
instance (priority := low) FibreIndex.scan [DecidableEq K] : FibreIndex K :=
  ⟨FinRel K, id, FinRel.scanLookup, fun _ => rfl, List.eraseDups, fun _ => rfl⟩

/-- A hashable key: the table `FinRel.fibres` and the hash set of `hashDedup`. -/
instance FibreIndex.hash [DecidableEq K] [Hashable K] : FibreIndex K :=
  ⟨fun V => Fibres K V, FinRel.fibres, Fibres.get, FinRel.get_fibres, hashDedup, hashDedup_eq⟩

/-! ## A relation as a sum of representations -/

/-- A relation `K ⟶ V` that enumerates each key's values: the pairs of a `FinRel`, or its `Λ` form `k ↦`
    the list of values `k` is related to (a fibre enumerated, the keys possibly infinite).

    Its meaning is a list: `app` gives each key's fibre in representation order, with repeats, so order
    and multiplicity are part of it and the operations are those of the Kleisli category of `List`
    (`app_comp`).  Each operation states its law on these lists; the relation `rel` is read off them by
    membership (`mem_app`), a monad map from `List` to sets, and each `rel_*` law follows.  Both factors
    of `R ≫ S` enumerate, so every composite is formed. -/
inductive RelRep (K V : Type) where
  | pairs (r : FinRel K V)
  | enum (f : K → List V)

/-- A relation `K ⟶ V` known only by its membership test: an order such as `(· ≤ ·)`, a quotient `X / Y`,
    the converse of an `enum`.  It lists nothing, so it follows a `RelRep` (`RelRep.compT`) or cuts one
    (`inter`, `est`, `thin`) and never leads a composite; a type of its own, so that no composite of two
    `RelRep`s can fail. -/
structure RelTest (K V : Type) where
  test ::
  mem : K → V → Bool

namespace RelTest

/-- The relation a test denotes. -/
def rel (T : RelTest K V) : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩ := fun k v => T.mem k v = true

/-- `T°`: the arguments flipped. -/
def conv (T : RelTest K V) : RelTest V K := test fun v k => T.mem k v

theorem rel_conv (T : RelTest K V) : T.conv.rel = T.rel° := hom_ext fun _ _ => Iff.rfl

/-- `S ∩ T`: both tests. -/
def inter (S T : RelTest K V) : RelTest K V := test fun k v => S.mem k v && T.mem k v

theorem rel_inter (S T : RelTest K V) : (inter S T).rel = S.rel ∩ T.rel :=
  hom_ext fun k v => by simp only [rel, inter, inter_apply, Bool.and_eq_true]

end RelTest

namespace RelRep

/-- The relation a representation denotes. -/
def rel : RelRep K V → ((⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩)
  | pairs r => r.rep
  | enum f => fun k v => v ∈ f k

/-- The graph of `g`: one value in each fiber. -/
def ofFn (g : K → V) : RelRep K V := enum fun k => [g k]

theorem rel_ofFn (g : K → V) : (ofFn g).rel = (graph g : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) :=
  hom_ext fun k v => List.mem_singleton.trans (Iff.of_eq (graph_apply g k v).symm)

variable [DecidableEq K] [DecidableEq V] [FibreIndex K] [FibreIndex V]

/-- The membership test of `rel`. -/
def mem : RelRep K V → K → V → Bool
  | pairs r => fun k v => decide ((k, v) ∈ r.toList)
  | enum f => fun k v => decide (v ∈ f k)

theorem mem_iff_rel : (R : RelRep K V) → (k : K) → (v : V) → (R.mem k v = true ↔ R.rel k v)
  | pairs _, _, _ => decide_eq_true_iff
  | enum _, _, _ => decide_eq_true_iff

/-- `R` read by its membership test only, its enumeration forgotten. -/
def toTest (R : RelRep K V) : RelTest K V := .test R.mem

instance : Coe (RelRep K V) (RelTest K V) := ⟨toTest⟩

theorem rel_toTest (R : RelRep K V) : R.toTest.rel = R.rel := hom_ext (mem_iff_rel R)

omit [DecidableEq V] [FibreIndex V] in
/-- `R`'s fibre function handed to `h`, a `FinRel`'s index built once.  `h` returns data: a function-valued
    `app` is eta-expanded by the compiler, which would rebuild the index at every key. -/
@[inline] def withApp {α : Type} (R : RelRep K V) (h : (K → List V) → α) : α :=
  match R with
  | pairs r => let i := FibreIndex.build r; h (FibreIndex.get i)
  | enum f => h f

omit [DecidableEq V] [FibreIndex V] in
/-- The list denotation: each key's fibre in representation order, with repeats — a `FinRel` in array
    order. -/
def app (R : RelRep K V) : K → List V := R.withApp id

omit [DecidableEq V] [FibreIndex V] in
theorem withApp_eq {α : Type} (R : RelRep K V) (h : (K → List V) → α) : R.withApp h = h R.app := by
  cases R <;> rfl

omit [DecidableEq V] [FibreIndex V] in
theorem app_pairs (r : FinRel K V) : (pairs r).app = r.scanLookup := FibreIndex.get_build r

omit [DecidableEq V] [FibreIndex V] in
/-- `rel` is membership in the fibre list. -/
theorem mem_app (R : RelRep K V) (k : K) (v : V) : v ∈ R.app k ↔ R.rel k v := by
  cases R with
  | pairs r => rw [app_pairs]; exact FinRel.mem_scanLookup r k v
  | enum f => exact Iff.rfl

theorem mem_eq_app (R : RelRep K V) (k : K) (v : V) : R.mem k v = decide (v ∈ R.app k) :=
  Bool.eq_iff_iff.2 ((mem_iff_rel R k v).trans ((mem_app R k v).symm.trans decide_eq_true_iff.symm))

/-- `R°`, a test: an `enum`'s converse would search every key.  A `FinRel`'s converse swaps its arrays
    and enumerates, `pairs r.conv`. -/
def conv (R : RelRep K V) : RelTest V K := .test fun v k => R.mem k v

theorem rel_conv (R : RelRep K V) : R.conv.rel = R.rel° := hom_ext fun v k => mem_iff_rel R k v

/-- `R ∩ S`: `R`'s fibres filtered by the test `S`; a `FinRel` stays one. -/
def inter : RelRep K V → RelTest K V → RelRep K V
  | pairs r, S => pairs (FinRel.filter (fun k v => S.mem k v = true) r)
  | enum f, S => enum fun k => (f k).filter (S.mem k ·)

/-- `R ∩ S`: `R`'s fibre, in order, filtered by `S`. -/
theorem app_inter (R : RelRep K V) (S : RelTest K V) (k : K) :
    (inter R S).app k = (R.app k).filter (S.mem k ·) := by
  cases R with
  | pairs r => simp only [inter, app_pairs, FinRel.scanLookup_filter, Bool.decide_eq_true]
  | enum f => rfl

theorem mem_inter (R : RelRep K V) (S : RelTest K V) (k : K) (v : V) :
    (inter R S).mem k v = (R.mem k v && S.mem k v) := by
  rw [mem_eq_app, app_inter, mem_eq_app]; simp [List.mem_filter]

theorem rel_inter (R : RelRep K V) (S : RelTest K V) : (inter R S).rel = R.rel ∩ S.rel :=
  hom_ext fun k v => by simp only [inter_apply, ← mem_iff_rel, mem_inter, Bool.and_eq_true, RelTest.rel]

/-- `R ∪ S`: two `FinRel`s append their arrays, otherwise the fibres are appended. -/
def union : RelRep K V → RelRep K V → RelRep K V
  | pairs r, pairs s => pairs (FinRel.union r s)
  | pairs r, enum g => let i := FibreIndex.build r; enum fun k => FibreIndex.get i k ++ g k
  | enum f, pairs s => let i := FibreIndex.build s; enum fun k => f k ++ FibreIndex.get i k
  | enum f, enum g => enum fun k => f k ++ g k

/-- `R ∪ S` appends the fibres: a monoid, neither idempotent nor commutative on lists — those two hold
    only of `rel` (`rel_union`). -/
theorem app_union (R S : RelRep K V) (k : K) : (union R S).app k = R.app k ++ S.app k := by
  cases R <;> cases S <;> first | rfl | simp only [union, app_pairs, FinRel.scanLookup_union]

theorem mem_union (R S : RelRep K V) (k : K) (v : V) : (union R S).mem k v = (R.mem k v || S.mem k v) := by
  rw [mem_eq_app, app_union, mem_eq_app, mem_eq_app]; simp [List.mem_append]

theorem rel_union (R S : RelRep K V) : (union R S).rel = R.rel ∪ S.rel :=
  hom_ext fun k v => by simp only [union_apply, ← mem_iff_rel, mem_union, Bool.or_eq_true]

/-! ### Domain, range, coreflexives, products, junctions and `Λ` -/

section Tabulate

open PowerAllegory

variable {L W : Type} [DecidableEq L] [DecidableEq W] [FibreIndex L] [FibreIndex W]

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] in
/-- The coreflexive `p?` of a decidable predicate: the fibre of `k` is `[k]` when `p(k)`, else empty. -/
def corefl (p : K → Bool) : RelRep K K := enum fun k => if p k then [k] else []

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] in
theorem rel_corefl (p : K → Bool) : (corefl p).rel = Freyd.Alg.RelSet.corefl (A := ⟨K⟩) fun k => p k = true :=
  hom_ext fun k k' => by
    simp only [corefl, RelRep.rel, Freyd.Alg.RelSet.corefl]
    cases h : p k <;> simp [eq_comm]

omit [DecidableEq V] [FibreIndex V] in
/-- `dom R`: the key `k` when its fibre is nonempty. -/
def dom (R : RelRep K V) : RelRep K K := R.withApp fun f => enum fun k => if (f k).isEmpty then [] else [k]

omit [DecidableEq V] [FibreIndex V] in
theorem dom_eq (R : RelRep K V) : dom R = enum fun k => if (R.app k).isEmpty then [] else [k] := withApp_eq _ _

omit [DecidableEq V] [FibreIndex V] in
theorem rel_dom (R : RelRep K V) : (dom R).rel = Alg.dom R.rel := by
  rw [dom_eq]
  refine hom_ext fun k k' => ⟨fun hm => ?_, fun ⟨e, v, hv, _⟩ => ?_⟩
  · simp only [RelRep.rel] at hm
    cases hfk : R.app k with
    | nil => simp [hfk] at hm
    | cons v vs =>
      simp only [hfk, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.mem_singleton] at hm
      rw [hm]
      have hv := (mem_app R k v).1 (by simp [hfk])
      exact ⟨rfl, v, hv, hv⟩
  · have e' : k = k' := e
    subst e'
    have hv' := (mem_app R k v).2 hv
    simp only [RelRep.rel]
    cases hfk : R.app k with
    | nil => rw [hfk] at hv'; exact absurd hv' List.not_mem_nil
    | cons => simp

omit [DecidableEq K] [FibreIndex K] in
/-- `ran R = dom R°`, for a `FinRel`, whose converse enumerates. -/
def ran (r : FinRel K V) : RelRep V V := dom (pairs r.conv)

omit [DecidableEq K] [FibreIndex K] in
theorem rel_ran (r : FinRel K V) : (ran r).rel = Alg.ran (pairs r).rel := by
  rw [ran, rel_dom]; show Alg.dom r.conv.rep = Alg.ran r.rep; rw [FinRel.rep_conv]; rfl

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] in
/-- Every pair of a member of `xs` and a member of `ys`. -/
def cross (xs : List V) (ys : List W) : List (V × W) := xs.flatMap fun v => ys.map (v, ·)

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] [DecidableEq L] [FibreIndex L] [DecidableEq W] [FibreIndex W] in
theorem mem_cross (xs : List V) (ys : List W) (q : V × W) : q ∈ cross xs ys ↔ q.1 ∈ xs ∧ q.2 ∈ ys := by
  obtain ⟨v, w⟩ := q; simp [cross]

/-- `⟨R,S⟩`: two `FinRel`s pair the pairs sharing a key, otherwise the fibres are paired. -/
def pair : RelRep K V → RelRep K W → RelRep K (V × W)
  | pairs r, pairs s => let i := FibreIndex.build s
    pairs (FinRel.ofList (r.toList.flatMap fun p => (FibreIndex.get i p.1).map fun w => (p.1, (p.2, w))))
  | pairs r, enum g => let i := FibreIndex.build r; enum fun k => cross (FibreIndex.get i k) (g k)
  | enum f, pairs s => let i := FibreIndex.build s; enum fun k => cross (f k) (FibreIndex.get i k)
  | enum f, enum g => enum fun k => cross (f k) (g k)

omit [DecidableEq L] [FibreIndex L] in
/-- `⟨R,S⟩` pairs each value of `R`'s fibre, in order, with each of `S`'s. -/
theorem app_pair (R : RelRep K V) (S : RelRep K W) (k : K) : (pair R S).app k = cross (R.app k) (S.app k) := by
  cases R <;> cases S <;> first | rfl | skip
  rename_i r s
  simp only [pair, app_pairs, FibreIndex.get_build, FinRel.scanLookup_ofList]
  have := FinRel.filterMap_sel_flatMap (fun k v => (s.scanLookup k).map (v, ·)) k r.toList
  simp only [List.map_map, Function.comp_def] at this
  exact this

omit [DecidableEq L] [FibreIndex L] in
theorem mem_pair (R : RelRep K V) (S : RelRep K W) (k : K) (q : V × W) :
    (pair R S).mem k q = (R.mem k q.1 && S.mem k q.2) := by
  rw [mem_eq_app, app_pair, mem_eq_app, mem_eq_app]; simp [mem_cross]

omit [DecidableEq L] [FibreIndex L] in
theorem rel_pair (R : RelRep K V) (S : RelRep K W) : (pair R S).rel = rpair R.rel S.rel :=
  hom_ext fun k q => by simp only [rpair, ← mem_iff_rel, mem_pair, Bool.and_eq_true]

/-- `R × S`: two `FinRel`s pair their pairs, otherwise the fibres are paired. -/
def prod : RelRep K V → RelRep L W → RelRep (K × L) (V × W)
  | pairs r, pairs s => pairs (FinRel.ofList ((cross r.toList s.toList).map fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))))
  | pairs r, enum g => let i := FibreIndex.build r; enum fun k => cross (FibreIndex.get i k.1) (g k.2)
  | enum f, pairs s => let i := FibreIndex.build s; enum fun k => cross (f k.1) (FibreIndex.get i k.2)
  | enum f, enum g => enum fun k => cross (f k.1) (g k.2)

omit [DecidableEq V] [FibreIndex V] [DecidableEq W] [FibreIndex W] in
/-- The fibre of `(k,j)` in the product of two lists of pairs crosses the fibre of `k` with that of `j`. -/
theorem filterMap_sel_cross (k : K) (j : L) (m : List (L × W)) : (l : List (K × V)) →
    ((cross l m).map fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))).filterMap (FinRel.sel (k, j))
      = cross (l.filterMap (FinRel.sel k)) (m.filterMap (FinRel.sel j))
  | [] => rfl
  | (a, b) :: l => by
    have ih := filterMap_sel_cross k j m l
    simp only [cross, List.flatMap_cons, List.map_append, List.filterMap_append] at ih ⊢
    rw [ih, List.map_map, Function.comp_def, filterMap_sel_row a b k j m]
    by_cases h : a = k <;> simp [FinRel.sel, h]
where
  /-- One row of the cross: `(a,b)` against each pair of `m`. -/
  filterMap_sel_row (a : K) (b : V) (k : K) (j : L) : (m : List (L × W)) →
      (m.map fun q => ((a, q.1), (b, q.2))).filterMap (FinRel.sel (k, j))
        = if a = k then (m.filterMap (FinRel.sel j)).map (b, ·) else []
    | [] => by split <;> rfl
    | (c, w) :: m => by
      have ih := filterMap_sel_row a b k j m
      by_cases h : a = k <;> by_cases e : c = j <;> simp_all [FinRel.sel]

/-- `R × S` crosses the two fibres, in order. -/
theorem app_prod (R : RelRep K V) (S : RelRep L W) (k : K × L) :
    (prod R S).app k = cross (R.app k.1) (S.app k.2) := by
  cases R <;> cases S <;> first | rfl | skip
  simp only [prod, app_pairs, FinRel.scanLookup_ofList]
  exact filterMap_sel_cross k.1 k.2 _ _

theorem mem_prod (R : RelRep K V) (S : RelRep L W) (k : K × L) (q : V × W) :
    (prod R S).mem k q = (R.mem k.1 q.1 && S.mem k.2 q.2) := by
  rw [mem_eq_app, app_prod, mem_eq_app, mem_eq_app]; simp [mem_cross]

theorem rel_prod (R : RelRep K V) (S : RelRep L W) : (prod R S).rel = rprodMap R.rel S.rel :=
  hom_ext fun k q => by simp only [rprodMap, ← mem_iff_rel, mem_prod, Bool.and_eq_true]

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] [DecidableEq L] [FibreIndex L] [DecidableEq W] [FibreIndex W] in
/-- The junction `[R,S]` pointwise: `R` on a left summand, `S` on a right one. -/
theorem junc_apply (R : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩) (S : (⟨L⟩ : RelSet.{0}) ⟶ ⟨V⟩) :
    (∀ k v, junc (sumCop ⟨K⟩ ⟨L⟩) R S (Sum.inl k) v ↔ R k v) ∧ ∀ l v, junc (sumCop ⟨K⟩ ⟨L⟩) R S (Sum.inr l) v ↔ S l v :=
  ⟨fun k v => by
    rw [← congrFun (congrFun (u₁_junc (sumCop ⟨K⟩ ⟨L⟩) R S) k) v]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ h⟩,
   fun l v => by
    rw [← congrFun (congrFun (u₂_junc (sumCop ⟨K⟩ ⟨L⟩) R S) l) v]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ h⟩⟩

/-- `[R,S]` on `K ⊕ L`: two `FinRel`s tag and append their pairs, otherwise a key is answered from its
    summand's fibre. -/
def junction : RelRep K V → RelRep L V → RelRep (K ⊕ L) V
  | pairs r, pairs s => pairs (FinRel.ofList (r.toList.map (fun p => (Sum.inl p.1, p.2)) ++ s.toList.map fun p => (Sum.inr p.1, p.2)))
  | pairs r, enum g => let i := FibreIndex.build r; enum (Sum.elim (FibreIndex.get i) g)
  | enum f, pairs s => let i := FibreIndex.build s; enum (Sum.elim f (FibreIndex.get i))
  | enum f, enum g => enum (Sum.elim f g)

omit [DecidableEq W] [FibreIndex W] in
/-- `[R,S]` answers a key from its summand's fibre. -/
theorem app_junction (R : RelRep K V) (S : RelRep L V) (x : K ⊕ L) :
    (junction R S).app x = Sum.elim R.app S.app x := by
  cases R <;> cases S <;> first | rfl | skip
  simp only [junction, app_pairs, FinRel.scanLookup_ofList]
  have hn : ∀ {X Y : Type} (l : List X), l.filterMap (fun _ => (none : Option Y)) = [] := fun l => by
    induction l <;> simp_all
  cases x <;> simp [List.filterMap_append, List.filterMap_map, Function.comp_def, FinRel.sel, FinRel.scanLookup, hn] <;>
    rfl

omit [DecidableEq W] [FibreIndex W] in
theorem mem_junction (R : RelRep K V) (S : RelRep L V) (x : K ⊕ L) (v : V) :
    (junction R S).mem x v = Sum.elim R.mem S.mem x v := by
  rw [mem_eq_app, app_junction]
  cases x
  · exact (mem_eq_app R _ v).symm
  · exact (mem_eq_app S _ v).symm

omit [DecidableEq W] [FibreIndex W] in
theorem rel_junction (R : RelRep K V) (S : RelRep L V) :
    (junction R S).rel = junc (sumCop ⟨K⟩ ⟨L⟩) R.rel S.rel :=
  hom_ext fun x v => by
    have hj := junc_apply R.rel S.rel
    rw [← mem_iff_rel, mem_junction]
    cases x with
    | inl k => rw [hj.1]; exact mem_iff_rel R k v
    | inr l => rw [hj.2]; exact mem_iff_rel S l v

omit [DecidableEq V] [FibreIndex V] in
/-- `Λ(R)`: each key's whole fibre list, order and repeats kept, read as a set through `Λ(∋ₗ)`. -/
def transpose (R : RelRep K V) : RelRep K (List V) := R.withApp ofFn

omit [DecidableEq V] [FibreIndex V] in
theorem transpose_eq (R : RelRep K V) : transpose R = ofFn R.app := withApp_eq _ _

omit [DecidableEq V] [FibreIndex V] in
theorem rel_transpose (R : RelRep K V) : (transpose R).rel ≫ Λ (lmem V) = Λ R.rel := by
  rw [transpose_eq, rel_ofFn, Λ_eq_classifier, Λ_eq_classifier]
  have hs : ∀ k, (fun v => v ∈ R.app k) = fun v => R.rel k v := fun k => funext fun v => propext (mem_app R k v)
  exact hom_ext fun k G => ⟨fun ⟨_, (e : _ = R.app k), (hG : G = _)⟩ => by subst e; exact hG.trans (hs k),
    fun (hG : G = _) => ⟨R.app k, rfl, hG.trans (hs k).symm⟩⟩

end Tabulate

/-- `R S`, first `R` then `S`: each value of `R`'s fibre hands on `S`'s fibre.  A `FinRel` first stays a
    `FinRel`. -/
def comp (R : RelRep K V) (S : RelRep V C) : RelRep K C :=
  S.withApp fun g => match R with
    | pairs r => pairs (FinRel.ofList (r.toList.flatMap fun p => (g p.2).map (p.1, ·)))
    | enum f => enum fun k => (f k).flatMap g

@[inherit_doc] scoped infixr:80 " ≫ " => comp

/-- `R S` is Kleisli composition in `List`: each value of `R`'s fibre, in order, hands on `S`'s fibre. -/
theorem app_comp (R : RelRep K V) (S : RelRep V C) (a : K) : (R ≫ S).app a = (R.app a).flatMap S.app := by
  simp only [comp, withApp_eq]
  cases R with
  | pairs r =>
    simp only [app_pairs, FinRel.scanLookup_ofList]
    exact FinRel.filterMap_sel_flatMap (fun _ b => S.app b) a r.toList
  | enum f => rfl

theorem mem_comp [DecidableEq C] (R : RelRep K V) (S : RelRep V C) (a : K) (c : C) :
    (R ≫ S).mem a c = (R.app a).any (S.mem · c) := by
  rw [mem_eq_app, app_comp]
  refine Bool.eq_iff_iff.2 ((decide_eq_true_iff).trans ?_)
  simp only [List.mem_flatMap, List.any_eq_true, mem_eq_app, decide_eq_true_eq]

theorem rel_comp (R : RelRep K V) (S : RelRep V C) : (R ≫ S).rel = R.rel ≫ S.rel :=
  hom_ext fun a c => (mem_app (R ≫ S) a c).symm.trans <| by
    rw [app_comp, List.mem_flatMap, comp_apply]
    exact ⟨fun ⟨v, hv, hc⟩ => ⟨v, (mem_app R a v).1 hv, (mem_app S v c).1 hc⟩,
      fun ⟨v, hv, hc⟩ => ⟨v, (mem_app R a v).2 hv, (mem_app S v c).2 hc⟩⟩

/-- `≫` is associative on fibre lists, since `flatMap` is. -/
theorem app_comp_assoc {D : Type} [DecidableEq C] [FibreIndex C] (R : RelRep K V) (S : RelRep V C)
    (U : RelRep C D) (a : K) : ((R ≫ S) ≫ U).app a = (R ≫ S ≫ U).app a := by
  rw [app_comp, app_comp, app_comp, List.flatMap_assoc]
  congr 1
  exact funext fun b => (app_comp S U b).symm

/-- `ofFn id` is a unit on each side: `[a].flatMap g = g a` and `xs.flatMap ([·]) = xs`. -/
theorem app_comp_id (R : RelRep K V) (k : K) : (ofFn id ≫ R).app k = R.app k ∧ (R ≫ ofFn id).app k = R.app k := by
  refine ⟨?_, ?_⟩ <;> rw [app_comp] <;> simp [ofFn, app, withApp]

/-- `R T` with a test `T` second: `T` tried on each value of `R`'s fibre. -/
def compT (R : RelRep K V) (T : RelTest V C) : RelTest K C :=
  R.withApp fun f => .test fun k c => (f k).any (T.mem · c)

omit [DecidableEq V] [FibreIndex V] in
theorem rel_compT (R : RelRep K V) (T : RelTest V C) : (R.compT T).rel = R.rel ≫ T.rel :=
  hom_ext fun a c => by
    simp only [compT, withApp_eq, RelTest.rel, comp_apply, List.any_eq_true]
    exact ⟨fun ⟨v, hv, hc⟩ => ⟨v, (mem_app R a v).1 hv, hc⟩, fun ⟨v, hv, hc⟩ => ⟨v, (mem_app R a v).2 hv, hc⟩⟩

/-! ### `est` and `thin` on an enumerated fibre -/

section Division

omit [DecidableEq K] [FibreIndex K] in
/-- `X / Y`: `k (X/Y) v` iff `X k c` for every `c` with `Y v c`.  The divisor's fibre is enumerated. -/
def div (X : RelTest K C) (Y : RelRep V C) : RelTest K V :=
  Y.withApp fun g => .test fun k v => (g v).all (X.mem k ·)

omit [DecidableEq K] [FibreIndex K] in
theorem rel_div (X : RelTest K C) (Y : RelRep V C) : (div X Y).rel = X.rel / Y.rel :=
  hom_ext fun k v => by
    simp only [div, withApp_eq, RelTest.rel]
    exact List.all_eq_true.trans (forall_congr' fun c => imp_congr (mem_app Y v c) Iff.rfl)

omit [DecidableEq K] [FibreIndex K] in
/-- `S \ R ≜ (R°/S°)°`: the divisor's converse is enumerated, so `S` is a `FinRel`. -/
def leftDiv (S : FinRel K V) (R : RelTest K C) : RelTest V C := (div R.conv (pairs S.conv)).conv

omit [DecidableEq K] [FibreIndex K] in
theorem rel_leftDiv (S : FinRel K V) (R : RelTest K C) : (leftDiv S R).rel = (pairs S).rel \ R.rel := by
  simp only [leftDiv, RelTest.rel_conv, rel_div, rel, FinRel.rep_conv]
  rfl

/-- `R /ₛ S ≜ (R/S) ∩ (S/R)°`: both fibres are enumerated. -/
def symmDiv [DecidableEq C] (R : RelRep K C) (S : RelRep V C) : RelTest K V := (div R S).inter (div S R).conv

theorem rel_symmDiv [DecidableEq C] (R : RelRep K C) (S : RelRep V C) : (symmDiv R S).rel = R.rel /ₛ S.rel := by
  simp only [symmDiv, RelTest.rel_inter, RelTest.rel_conv, rel_div, rel_toTest]
  rfl

end Division

/-- `est(le)` on one list: the members `le`-below every member. -/
def estList (le : V → V → Bool) (xs : List V) : List V := xs.filter fun v => xs.all (le v ·)

/-- `thin(Q)` on one list: a member is dropped when a kept member is `q`-below it, and otherwise
    kept in place of the kept members it is `q`-below. -/
def thinList (q : V → V → Bool) : List V → List V
  | [] => []
  | z :: zs => if (thinList q zs).any (q · z) then thinList q zs else z :: (thinList q zs).filter (!q z ·)

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] in
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

/-- `Λ(R) est(L) = R ∩ (L/R)°`, from `est(L) ≜ ∋ ∩ (∈\L°)`: on a fibre list this is `estList`. -/
def est (L : RelTest V V) (R : RelRep K V) : RelRep K V := R.inter (div L R).conv

theorem rel_est (L : RelTest V V) (R : RelRep K V) : (est L R).rel = Λ R.rel ≫ Freyd.Alg.est L.rel := by
  rw [est, rel_inter, RelTest.rel_conv, rel_div]
  exact hom_ext fun k v => (Λ_comp_est_apply _ _ k v).symm

/-- `est(L)` on the fibre list: keep, in order, the members `L`-below every member. -/
theorem app_est (L : RelTest V V) (R : RelRep K V) (k : K) : (est L R).app k = estList L.mem (R.app k) := by
  rw [est, app_inter]; simp only [div, withApp_eq, RelTest.conv]; rfl

omit [DecidableEq V] [FibreIndex V] in
/-- `Λ(R) thin(Q)`: each fibre cut by `thinList`. -/
def thin (Q : RelTest V V) (R : RelRep K V) : RelRep K V := R.withApp fun f => enum fun k => thinList Q.mem (f k)

omit [DecidableEq V] [FibreIndex V] in
theorem thin_eq (Q : RelTest V V) (R : RelRep K V) : thin Q R = enum fun k => thinList Q.mem (R.app k) :=
  withApp_eq _ _

/-- `R ⊕ S`, `R` overridden where it is empty: `R`'s fibre where nonempty, else `S`'s. -/
def override (R S : RelRep K V) : RelRep K V :=
  R.withApp fun f => S.withApp fun g => enum fun k => if f k = [] then g k else f k

theorem override_eq (R S : RelRep K V) :
    override R S = enum fun k => if R.app k = [] then S.app k else R.app k := by
  simp only [override, withApp_eq]

/-- `R ⊕ S` relates `k` as `R` does, or as `S` does where `R` relates `k` to nothing. -/
theorem rel_override (R S : RelRep K V) (k : K) (v : V) :
    (override R S).rel k v ↔ R.rel k v ∨ (∀ w, ¬ R.rel k w) ∧ S.rel k v := by
  rw [override_eq]
  show v ∈ (if R.app k = [] then S.app k else R.app k) ↔ _
  by_cases e : R.app k = []
  · rw [if_pos e, mem_app]
    simp only [← mem_app R, e, List.not_mem_nil, false_or, not_false_eq_true, implies_true, true_and]
  · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ e
    rw [if_neg e, mem_app]
    exact ⟨.inl, fun | .inl h => h | .inr ⟨hn, _⟩ => absurd ((mem_app R k w).1 hw) (hn w)⟩

omit [DecidableEq V] [FibreIndex V] in
/-- The first value of each fibre, in representation order. -/
def first (R : RelRep K V) : RelRep K V := R.withApp fun f => enum fun k => (f k).head?.toList

omit [DecidableEq V] [FibreIndex V] in
/-- The last value of each fibre, in representation order. -/
def last (R : RelRep K V) : RelRep K V := R.withApp fun f => enum fun k => (f k).getLast?.toList

omit [DecidableEq V] [FibreIndex V] in
theorem first_eq (R : RelRep K V) : first R = enum fun k => (R.app k).head?.toList := withApp_eq _ _

omit [DecidableEq V] [FibreIndex V] in
theorem last_eq (R : RelRep K V) : last R = enum fun k => (R.app k).getLast?.toList := withApp_eq _ _

omit [DecidableEq V] [FibreIndex V] in
/-- A fibre selector keeps one value of each nonempty fibre: `T ⊑ R`, and `T` relates every key `R` does. -/
theorem rel_select (R : RelRep K V) {sel : List V → Option V} (hs : ∀ l v, sel l = some v → v ∈ l)
    (hn : ∀ l, l ≠ [] → ∃ v, sel l = some v) :
    (∀ k v, (enum fun k => (sel (R.app k)).toList : RelRep K V).rel k v → R.rel k v) ∧
      ∀ k v, R.rel k v → ∃ w, (enum fun k => (sel (R.app k)).toList : RelRep K V).rel k w := by
  refine ⟨fun k v hv => (mem_app R k v).1 (hs _ _ (Option.mem_toList.1 hv)), fun k v hv => ?_⟩
  obtain ⟨w, hw⟩ := hn (R.app k) fun e => by rw [← mem_app, e] at hv; exact List.not_mem_nil hv
  exact ⟨w, Option.mem_toList.2 hw⟩

omit [DecidableEq V] [FibreIndex V] in
theorem rel_first (R : RelRep K V) :
    (∀ k v, (first R).rel k v → R.rel k v) ∧ ∀ k v, R.rel k v → ∃ w, (first R).rel k w := by
  rw [first_eq]
  exact rel_select R (fun _ _ => List.mem_of_mem_head?) (fun l e => ⟨_, (List.head?_eq_some_head e)⟩)

omit [DecidableEq V] [FibreIndex V] in
theorem rel_last (R : RelRep K V) :
    (∀ k v, (last R).rel k v → R.rel k v) ∧ ∀ k v, R.rel k v → ∃ w, (last R).rel k w := by
  rw [last_eq]
  exact rel_select R (fun _ _ => List.mem_of_getLast?) (fun l e => ⟨_, List.getLast?_eq_some_getLast e⟩)

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] in
/-- `thinList_spec` at a preorder `Q` held as a test. -/
theorem thinList_rel_spec {Q : RelTest V V} (hr : 𝟙 _ ⊑ Q.rel) (ht : Q.rel ≫ Q.rel ⊑ Q.rel) (xs : List V) :
    (∀ y ∈ thinList Q.mem xs, y ∈ xs) ∧ ∀ z ∈ xs, ∃ w ∈ thinList Q.mem xs, Q.rel w z :=
  thinList_spec (q := Q.mem) (fun v => le_iff.mp hr v v (by rw [id_apply]))
    (fun u v w h1 h2 => le_iff.mp ht u w ⟨v, h1, h2⟩) xs

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] in
/-- `Λ X ⊑ Λ Y thin(Q)` pointwise: each `X`-fibre lies in the `Y`-fibre and holds a `Q`-lower bound of
    every member of it. -/
theorem Λ_le_thin {X Y : (⟨K⟩ : RelSet.{0}) ⟶ ⟨V⟩} {Q : (⟨V⟩ : RelSet.{0}) ⟶ ⟨V⟩}
    (h : ∀ k, (∀ y, X k y → Y k y) ∧ ∀ z, Y k z → ∃ w, X k w ∧ Q w z) : Λ X ⊑ Λ Y ≫ thinRel Q := by
  rw [Λ_eq_classifier, Λ_eq_classifier]
  refine le_iff.mpr fun k G hG => ⟨fun v => Y k v, rfl, ?_⟩
  have hG' : G = fun v => X k v := hG
  subst hG'
  exact (thinRel_pt _ _ _).2 ⟨(h k).1, fun z hz => ((h k).2 z hz).imp fun w ⟨hw, hq⟩ => ⟨hq, hw⟩⟩

omit [DecidableEq V] [FibreIndex V] in
/-- For a preorder `Q`, each computed fibre is a `thin(Q)` choice of `R`'s fibre. -/
theorem rel_thin {Q : RelTest V V} (hr : 𝟙 _ ⊑ Q.rel) (ht : Q.rel ≫ Q.rel ⊑ Q.rel) (R : RelRep K V) :
    Λ (thin Q R).rel ⊑ Λ R.rel ≫ thinRel Q.rel := by
  rw [thin_eq]
  exact Λ_le_thin fun k => have hs := thinList_rel_spec hr ht (R.app k)
    ⟨fun y hy => (mem_app R k y).1 (hs.1 y hy), fun z hz => hs.2 z ((mem_app R k z).2 hz)⟩

/-! ### The fold over cons-lists -/

section Fold

open CL

variable {L E : Type} [DecidableEq L] [DecidableEq E] [FibreIndex L] [FibreIndex E]

omit [DecidableEq V] [FibreIndex V] [DecidableEq L] [FibreIndex L] [DecidableEq E] [FibreIndex E] in
/-- `⦇[b,s]⦈` on fibres: the base's fibre at `wrap`, the step's fibre over each value at `cons`, each
    fibre then cut by `post`. -/
def foldList (post : List V → List V) (b : L → List V) (s : E × V → List V) : ConsList L E → List V :=
  cfold (fun l => post (b l)) fun e vs => post (vs.flatMap fun v => s (e, v))

omit [DecidableEq V] [FibreIndex V] [DecidableEq L] [FibreIndex L] [DecidableEq E] [FibreIndex E] in
/-- `foldList` with a one-value fibre handed to the step directly: a functional fold's fibres are all one
    value, and the compiled `flatMap` builds an array per step. -/
def foldListOne (post : List V → List V) (b : L → List V) (s : E × V → List V) : ConsList L E → List V :=
  cfold (fun l => post (b l)) fun e vs => post (match vs with
    | [v] => s (e, v)
    | vs => vs.flatMap fun v => s (e, v))

omit [DecidableEq V] [FibreIndex V] [DecidableEq L] [FibreIndex L] [DecidableEq E] [FibreIndex E] in
@[csimp] theorem foldList_eq_foldListOne : @foldList = @foldListOne := by
  funext _ _ _ post b s
  unfold foldList foldListOne
  congr
  funext e vs
  split <;> simp

/-- `⦇[B,S]⦈` with every fibre cut by `post`. -/
def foldWith (post : List V → List V) (B : RelRep L V) (S : RelRep (E × V) V) : RelRep (ConsList L E) V :=
  B.withApp fun b => S.withApp fun s => enum (foldList post b s)

/-- `⦇[B,S]⦈`, each fibre enumerated. -/
def fold (B : RelRep L V) (S : RelRep (E × V) V) : RelRep (ConsList L E) V := foldWith id B S

/-- The fold's fibre lists: at `wrap` the base's, at `cons` the step's over each value in order, each cut
    by `post`. -/
theorem foldWith_eq (post : List V → List V) (B : RelRep L V) (S : RelRep (E × V) V) :
    foldWith post B S = enum (foldList post B.app S.app) := by
  simp only [foldWith, withApp_eq]

/-- `⦇thin(Q)·Λ[B,S]⦈`: the fold with every fibre thinned by `Q`. -/
def foldThin (Q : RelTest V V) (B : RelRep L V) (S : RelRep (E × V) V) : RelRep (ConsList L E) V :=
  foldWith (thinList Q.mem) B S

/-- The induction behind `rel_fold` and `rel_foldThin`: when `post` keeps a `P`-lower bound of every
    member and the step preserves `P`, the computed fibre lies in the fold's and bounds it. -/
theorem foldWith_spec {post : List V → List V} {B : RelRep L V} {S : RelRep (E × V) V} {P : V → V → Prop}
    (hpost : ∀ xs, (∀ y ∈ post xs, y ∈ xs) ∧ ∀ z ∈ xs, ∃ w ∈ post xs, P w z)
    (htrans : ∀ u v w, P u v → P v w → P u w)
    (hmono : ∀ e w r z, P w r → S.rel (e, r) z → ∃ c, S.rel (e, w) c ∧ P c z) (x : ConsList L E) :
    (∀ y, (foldWith post B S).rel x y → cataFold (C := ⟨V⟩) (junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel) x y)
      ∧ ∀ z, cataFold (C := ⟨V⟩) (junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel) x z →
        ∃ w, (foldWith post B S).rel x w ∧ P w z := by
  rw [foldWith_eq]
  have hj := junc_apply B.rel S.rel
  induction x with
  | wrap l =>
    obtain ⟨hsub, hdom⟩ := hpost (B.app l)
    refine ⟨fun y hy => ?_, fun z hz => ?_⟩
    · rw [cataFold_wrap]; exact (hj.1 l y).2 ((mem_app B l y).1 (hsub y hy))
    · rw [cataFold_wrap] at hz; exact hdom z ((mem_app B l z).2 ((hj.1 l z).1 hz))
  | cons e x ih =>
    obtain ⟨hsub, hdom⟩ := ih
    obtain ⟨psub, pdom⟩ := hpost ((foldList post B.app S.app x).flatMap fun v => S.app (e, v))
    refine ⟨fun y hy => ?_, fun z hz => ?_⟩
    · obtain ⟨r, hr, hy⟩ := List.mem_flatMap.1 (psub y hy)
      rw [cataFold_cons]
      exact ⟨r, hsub r hr, (hj.2 (e, r) y).2 ((mem_app S _ y).1 hy)⟩
    · rw [cataFold_cons] at hz
      obtain ⟨r, hr, hz⟩ := hz
      obtain ⟨w, hw, hwr⟩ := hdom r hr
      obtain ⟨c, hc, hcz⟩ := hmono e w r z hwr ((hj.2 (e, r) z).1 hz)
      obtain ⟨w', hw', hw'c⟩ := pdom c (List.mem_flatMap.2 ⟨w, hw, (mem_app S _ c).2 hc⟩)
      exact ⟨w', hw', htrans _ _ _ hw'c hcz⟩

/-- The computed fold denotes the relational fold `⦇[B,S]⦈`. -/
theorem rel_fold (B : RelRep L V) (S : RelRep (E × V) V) :
    (fold B S).rel = ⦇(junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel : Alg (F L E) ⟨V⟩)⦈ := by
  have hf := foldWith_spec (post := id) (B := B) (S := S) (P := Eq) (fun _ => ⟨fun _ h => h, fun z hz => ⟨z, hz, rfl⟩⟩)
    (fun _ _ _ => Eq.trans) (fun _ _ _ _ e h => ⟨_, by subst e; exact h, rfl⟩)
  rw [← cataR_eq_relCata]
  exact hom_ext fun x v => ⟨(hf x).1 v, fun hv => let ⟨_, hw, e⟩ := (hf x).2 v hv; e ▸ hw⟩

/-- **The thinning fold**: for a preorder `Q` that the algebra `[B,S]` preserves, every computed fibre
    is a `thin(Q)` choice of the fold's, `Λ T ⊑ Λ⦇[B,S]⦈ thin(Q)`. -/
theorem rel_foldThin {Q : RelTest V V} {B : RelRep L V} {S : RelRep (E × V) V}
    (hr : 𝟙 _ ⊑ Q.rel) (ht : Q.rel ≫ Q.rel ⊑ Q.rel)
    (hmono : Pres (F := F L E) (junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel) Q.rel) :
    Λ (foldThin Q B S).rel ⊑ Λ ⦇(junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel : Alg (F L E) ⟨V⟩)⦈ ≫ thinRel Q.rel := by
  have hj := junc_apply B.rel S.rel
  have hf := foldWith_spec (B := B) (S := S) (P := Q.rel) (thinList_rel_spec hr ht) (fun u v w h1 h2 => le_iff.mp ht u w ⟨v, h1, h2⟩)
    (fun e w r z hwr hz =>
      let ⟨c, hc, hcz⟩ := le_iff.mp hmono (Sum.inr (e, w)) z ⟨Sum.inr (e, r), ⟨rfl, hwr⟩, (hj.2 _ z).2 hz⟩
      ⟨c, (hj.2 _ c).1 hc, hcz⟩)
  rw [← cataR_eq_relCata]
  exact Λ_le_thin hf

end Fold

/-! ### General recursion: the terminating hylomorphism

`fold` recurses on the structure of its argument.  `hylo` recurses on any subproblems `step` asks
for, total because a measure `μ` bounds the depth: it runs `step` on a fuel of `μ x + 1`, and a step
that asks only for subproblems of smaller measure never sees the fuel run out.  `step X x` is one
unfold-then-fold step, `X` standing for the recursive calls; `d` answers when the fuel is out, and
is never reached under that hypothesis. -/

section Hylo

/-- `step` iterated `n` times from `d`. -/
def hyloN (d : A → B) (step : (A → B) → A → B) : Nat → A → B
  | 0 => d
  | n + 1 => step (hyloN d step n)

/-- **The terminating hylomorphism**: `step` iterated on a fuel of `μ x + 1`. -/
def hylo (μ : A → Nat) (d : A → B) (step : (A → B) → A → B) (x : A) : B := hyloN d step (μ x + 1) x

/-- `step X x` reads `X` only at subproblems of smaller measure than `x`. -/
def Guarded (μ : A → Nat) (step : (A → B) → A → B) : Prop :=
  ∀ X Y x, (∀ y, μ y < μ x → X y = Y y) → step X x = step Y x

variable {μ : A → Nat} {d : A → B} {step : (A → B) → A → B}

/-- **Measure induction through `hylo`**: an invariant `I` that every step keeps, given it at all
    smaller subproblems, holds of every answer — the fuel induction each program would repeat. -/
theorem hylo_ind {I : A → B → Prop} (hs : ∀ X x, (∀ y, μ y < μ x → I y (X y)) → I x (step X x))
    (x : A) : I x (hylo μ d step x) :=
  go (μ x + 1) x (Nat.lt_succ_self _)
where go : ∀ n x, μ x < n → I x (hyloN d step n x)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, h => hs _ x fun y hy => go n y (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_succ h))

/-- Under a guarded step, any fuel above the measure gives the same answer. -/
theorem hyloN_stable (hg : Guarded μ step) :
    ∀ n m x, μ x < n → μ x < m → hyloN d step n x = hyloN d step m x
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, m + 1, x, hn, hm => hg _ _ x fun y hy => hyloN_stable hg n m y (by omega) (by omega)

/-- **`hylo` solves its recursion**: under a guarded step, `step(hylo) = hylo`. -/
theorem hylo_fixed (hg : Guarded μ step) : step (hylo μ d step) = hylo μ d step :=
  funext fun x => hg _ _ x fun y hy => hyloN_stable hg (μ y + 1) (μ x) y (Nat.lt_succ_self _) hy

/-- **The hylomorphism law**: if `step` computes `φ` under a reading `ρ` of programs as relations,
    `ρ(hylo)` is a fixed point of `φ`, so `μφ ⊑ ρ(hylo)` (`mu_le_of_fixed`). -/
theorem rel_hylo (ρ : (A → B) → ((⟨A⟩ : RelSet.{0}) ⟶ ⟨C⟩))
    {φ : ((⟨A⟩ : RelSet.{0}) ⟶ ⟨C⟩) → ((⟨A⟩ : RelSet.{0}) ⟶ ⟨C⟩)} (hρ : ∀ X, ρ (step X) = φ (ρ X))
    (hg : Guarded μ step) : φ (ρ (hylo μ d step)) = ρ (hylo μ d step) := by
  rw [← hρ, hylo_fixed hg]

end Hylo

end RelRep

end Freyd.Alg.RelSet
