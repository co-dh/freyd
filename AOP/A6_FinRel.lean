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

/-! ## Fibres by chaining rows -/

/-- `(List.range' i m).foldl f a` as a loop: no list of indices is made. -/
@[specialize] def rangeFold {α : Type} (f : α → Nat → α) : Nat → Nat → α → α
  | 0, _, a => a
  | m + 1, i, a => rangeFold f m (i + 1) (f a i)

theorem rangeFold_eq {α : Type} (f : α → Nat → α) : ∀ m i a, rangeFold f m i a = (List.range' i m).foldl f a
  | 0, _, _ => rfl
  | m + 1, i, a => by rw [rangeFold, rangeFold_eq f m]; rfl

namespace Chain

/-- The rows of one chain, last first, in at most `f` links: `p` is `0` or one more than a row `i`, and
    `nx[i]` the chain's previous row the same way.  A link that does not descend stops the chain.  Fuel and
    not well-founded recursion, so that `decide` evaluates it. -/
def rowsF : Nat → Array Nat → Nat → List Nat
  | 0, _, _ => []
  | f + 1, nx, p =>
    if h : 0 < p ∧ p ≤ nx.size then (p - 1) :: (if nx[p - 1] < p then rowsF f nx nx[p - 1] else []) else []

/-- The rows of chain `p`: `p` links are enough, since every link descends. -/
def rows (nx : Array Nat) (p : Nat) : List Nat := rowsF p nx p

theorem rowsF_fuel {nx : Array Nat} : ∀ (f g p : Nat), p ≤ f → p ≤ g → rowsF f nx p = rowsF g nx p
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, p, hf, _ => by rw [Nat.le_zero.1 hf]; simp [rowsF]
  | _ + 1, 0, p, _, hg => by rw [Nat.le_zero.1 hg]; simp [rowsF]
  | f + 1, g + 1, p, hf, hg => by
    simp only [rowsF]
    split
    · split
      · rw [rowsF_fuel f g _ (by omega) (by omega)]
      · rfl
    · rfl

/-- Row `j`'s value when its key is `k`.  The key first: a link of another key never reads `vs`, a cache
    miss saved per collision. -/
def at? [DecidableEq K] (ks : Array K) (vs : Array V) (k : K) (j : Nat) : Option V :=
  match ks[j]? with
  | some a => if a = k then vs[j]? else none
  | none => none

/-- The values of the rows of chain `p` whose key is `k`, in at most `f` links, consed onto `acc` last row
    first, so they come out in row order; tail-recursive, and no list of rows is made. -/
def walkF [DecidableEq K] (ks : Array K) (vs : Array V) (nx : Array Nat) (k : K) : Nat → Nat → List V → List V
  | 0, _, acc => acc
  | f + 1, p, acc =>
    if h : 0 < p ∧ p ≤ nx.size then
      let acc := match at? ks vs k (p - 1) with
        | some v => v :: acc
        | none => acc
      if nx[p - 1] < p then walkF ks vs nx k f nx[p - 1] acc else acc
    else acc

theorem walkF_eq [DecidableEq K] (ks : Array K) (vs : Array V) (nx : Array Nat) (k : K) :
    ∀ f p acc, walkF ks vs nx k f p acc = (rowsF f nx p).reverse.filterMap (at? ks vs k) ++ acc
  | 0, _, _ => rfl
  | f + 1, p, acc => by
    simp only [walkF, rowsF]
    by_cases h : 0 < p ∧ p ≤ nx.size
    · rw [dif_pos h, dif_pos h]
      cases hx : at? ks vs k (p - 1) <;> simp only [hx] <;> split <;> (try rw [walkF_eq ks vs nx k f]) <;>
        simp [hx, List.reverse_cons]
    · rw [dif_neg h, dif_neg h]; rfl

/-- `walkF`'s first value alone: the chain runs last row first, so the last hit is the first row; no list
    is made. -/
def walkFirstF [DecidableEq K] (ks : Array K) (vs : Array V) (nx : Array Nat) (k : K) : Nat → Nat → Option V → Option V
  | 0, _, acc => acc
  | f + 1, p, acc =>
    if h : 0 < p ∧ p ≤ nx.size then
      let acc := match at? ks vs k (p - 1) with
        | some v => some v
        | none => acc
      if nx[p - 1] < p then walkFirstF ks vs nx k f nx[p - 1] acc else acc
    else acc

theorem walkFirstF_eq [DecidableEq K] (ks : Array K) (vs : Array V) (nx : Array Nat) (k : K) :
    ∀ f p (acc : Option V) (l : List V), l.head? = acc → walkFirstF ks vs nx k f p acc = (walkF ks vs nx k f p l).head?
  | 0, _, _, _, h => h.symm
  | f + 1, p, acc, l, h => by
    simp only [walkFirstF, walkF]
    by_cases hb : 0 < p ∧ p ≤ nx.size
    · rw [dif_pos hb, dif_pos hb]
      cases hx : at? ks vs k (p - 1) <;> simp only <;> split <;>
        first | exact walkFirstF_eq ks vs nx k f _ _ _ (by simp [h]) | simp [h]
    · rw [dif_neg hb, dif_neg hb]; exact h.symm

/-- `walkF`'s values folded by `g` in row order, the earlier rows first by recursion down the chain: no
    list is made. -/
def foldF [DecidableEq K] {α : Type} (ks : Array K) (vs : Array V) (nx : Array Nat) (k : K) (g : α → V → α) :
    Nat → Nat → α → α
  | 0, _, a => a
  | f + 1, p, a =>
    if h : 0 < p ∧ p ≤ nx.size then
      let a := if nx[p - 1] < p then foldF ks vs nx k g f nx[p - 1] a else a
      match at? ks vs k (p - 1) with
      | some v => g a v
      | none => a
    else a

theorem foldF_eq [DecidableEq K] {α : Type} (ks : Array K) (vs : Array V) (nx : Array Nat) (k : K) (g : α → V → α) :
    ∀ f p a, foldF ks vs nx k g f p a = ((rowsF f nx p).reverse.filterMap (at? ks vs k)).foldl g a
  | 0, _, _ => rfl
  | f + 1, p, a => by
    simp only [foldF, rowsF]
    by_cases hb : 0 < p ∧ p ≤ nx.size
    · rw [dif_pos hb, dif_pos hb]
      by_cases hn : nx[p - 1] < p
      · simp only [hn, ↓reduceIte, foldF_eq]
        cases hx : at? ks vs k (p - 1) <;> simp [List.reverse_cons, List.filterMap_append, hx]
      · simp only [hn, ↓reduceIte]
        cases hx : at? ks vs k (p - 1) <;> simp [hx]
    · rw [dif_neg hb, dif_neg hb]; rfl

/-- `rowsF` reads `nx` only below `p`. -/
theorem rowsF_congr {nx nx' : Array Nat} (h : ∀ j, j < nx.size → nx'[j]? = nx[j]?) (hs : nx.size ≤ nx'.size) :
    ∀ f p, p ≤ nx.size → rowsF f nx' p = rowsF f nx p
  | 0, _, _ => rfl
  | f + 1, p, hp => by
    simp only [rowsF]
    by_cases h0 : 0 < p
    · have e : nx'[p - 1]? = nx[p - 1]? := h _ (by omega)
      have hl : p - 1 < nx.size := by omega
      have hl' : p - 1 < nx'.size := by omega
      have e' : nx'[p - 1] = nx[p - 1] := by
        rw [Array.getElem?_eq_getElem hl, Array.getElem?_eq_getElem hl'] at e; exact Option.some.inj e
      rw [dif_pos ⟨h0, by omega⟩, dif_pos ⟨h0, hp⟩, e']
      split
      · rw [rowsF_congr h hs f _ (by omega)]
      · rfl
    · rw [dif_neg (by omega), dif_neg (by omega)]

/-- Append row `i = nx.size`, of slot `s`, to its chain.  Matched, not projected, so that both arrays are
    unshared and updated in place. -/
@[inline] def add (slot : Nat → Nat) : Array Nat × Array Nat → Nat → Array Nat × Array Nat
  | (hd, nx), i =>
    let s := slot i
    let v := hd[s]?.getD 0
    (hd.setIfInBounds s (i + 1), nx.push v)

/-- The chains of rows `0 … n-1` by slot, over `cap` heads. -/
@[specialize] def build (slot : Nat → Nat) (cap n : Nat) : Array Nat × Array Nat :=
  (List.range n).foldl (add slot) (Array.replicate cap 0, Array.mkEmpty n)

@[specialize] def buildTR (slot : Nat → Nat) (cap n : Nat) : Array Nat × Array Nat :=
  rangeFold (add slot) n 0 (Array.replicate cap 0, Array.mkEmpty n)

/-- `build` loops over the rows: `List.range n` allocates a cell per row. -/
@[csimp] theorem build_eq_buildTR : @build = @buildTR := by
  funext slot cap n; rw [build, buildTR, rangeFold_eq, List.range_eq_range']

/-- What `build` holds after rows `0 … i-1`: each slot's chain lists its rows, last first. -/
def Inv (slot : Nat → Nat) (cap i : Nat) (hn : Array Nat × Array Nat) : Prop :=
  hn.1.size = cap ∧ hn.2.size = i ∧ ∀ s < cap, hn.1[s]?.getD 0 ≤ i ∧
    rows hn.2 (hn.1[s]?.getD 0) = ((List.range i).filter fun j => slot j = s).reverse

theorem inv_add {slot : Nat → Nat} {cap i : Nat} {hd nx : Array Nat} (h : Inv slot cap i (hd, nx)) :
    Inv slot cap (i + 1) (add slot (hd, nx) i) := by
  obtain ⟨h1, h2, h3⟩ := h
  dsimp only at h1 h2 h3
  have hc : ∀ f p, p ≤ i → rowsF f (nx.push (hd[slot i]?.getD 0)) p = rowsF f nx p := fun f p hp =>
    rowsF_congr (fun j hj => by rw [Array.getElem?_push_lt hj, Array.getElem?_eq_getElem hj]) (by simp) f p (by omega)
  refine ⟨by simp [add, h1], by simp [add, h2], fun s hsc => ?_⟩
  simp only [add, Array.getElem?_setIfInBounds]
  by_cases e : slot i = s
  · subst e
    rw [if_pos rfl, if_pos (by rw [h1]; exact hsc), Option.getD_some]
    refine ⟨Nat.le_refl _, ?_⟩
    obtain ⟨hle, hr⟩ := h3 _ hsc
    rw [rows, rowsF, dif_pos ⟨by omega, by simp [h2]⟩]
    simp only [Nat.add_sub_cancel, Array.getElem_push, h2, Nat.lt_irrefl, dite_false]
    rw [if_pos (by omega), hc _ _ hle, rowsF_fuel _ _ _ hle (Nat.le_refl _)]
    show i :: rows nx _ = _
    rw [hr, List.range_succ, List.filter_append]
    simp
  · rw [if_neg e]
    obtain ⟨hle, hr⟩ := h3 _ hsc
    refine ⟨by omega, ?_⟩
    rw [rows, hc _ _ hle]
    show rows nx _ = _
    rw [hr, List.range_succ, List.filter_append]
    simp [e]

theorem inv_build {slot : Nat → Nat} {cap : Nat} (n : Nat) : Inv slot cap n (build slot cap n) := by
  have go : ∀ m, Inv slot cap m ((List.range m).foldl (add slot) (Array.replicate cap 0, Array.mkEmpty n)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simp, by simp, fun s hsc => ?_⟩
      simp [hsc, rows, rowsF]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize List.foldl (add slot) (Array.replicate cap 0, Array.mkEmpty n) (List.range m) = x at ih ⊢
      obtain ⟨hd, nx⟩ := x
      exact inv_add ih
  exact go n


/-- The pairs of two lists are read off by index. -/
theorem filterMap_at? [DecidableEq K] (k : K) : (a : List K) → (b : List V) → a.length = b.length →
    (List.range a.length).filterMap (at? a.toArray b.toArray k) = (a.zip b).filterMap (FinRel.sel k)
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    have ih := filterMap_at? k a b (by simpa using h)
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map, List.zip_cons_cons,
      List.filterMap_cons]
    have e : (at? (x :: a).toArray (y :: b).toArray k ∘ Nat.succ) = at? a.toArray b.toArray k := by
      funext j; simp [at?]
    rw [e, ih]
    simp [at?, FinRel.sel]

end Chain

/-- A table of `2n` heads, at least one, for `n` rows. -/
def chainCap (n : Nat) : Nat := 2 * n + 1

/-- The fibres of `r` by hashing: the rows chained by the slot of their key, no cell allocated per row. -/
def FinRel.chains [DecidableEq K] [Hashable K] (r : FinRel K V) : FinRel K V × Array Nat × Array Nat :=
  let cap := chainCap r.keys.size
  (r, Chain.build (fun (j : Nat) => (r.keys[j]?.elim (0 : UInt64) hash).toNat % cap) cap r.keys.size)

/-- The fibre of `k` from the chains. -/
def chainGet [DecidableEq K] [Hashable K] (x : FinRel K V × Array Nat × Array Nat) (k : K) : List V :=
  let p := x.2.1[(hash k).toNat % chainCap x.1.keys.size]?.getD 0
  Chain.walkF x.1.keys x.1.vals x.2.2 k p p []

/-- The first value of `k`'s fibre from the chains, no list made. -/
def chainFirst [DecidableEq K] [Hashable K] (x : FinRel K V × Array Nat × Array Nat) (k : K) : Option V :=
  let p := x.2.1[(hash k).toNat % chainCap x.1.keys.size]?.getD 0
  Chain.walkFirstF x.1.keys x.1.vals x.2.2 k p p none

theorem chainFirst_eq [DecidableEq K] [Hashable K] (x : FinRel K V × Array Nat × Array Nat) (k : K) :
    chainFirst x k = (chainGet x k).head? :=
  Chain.walkFirstF_eq _ _ _ _ _ _ _ [] rfl

/-- `k`'s fibre from the chains folded by `g`, no list made. -/
def chainFold [DecidableEq K] [Hashable K] {α : Type} (x : FinRel K V × Array Nat × Array Nat) (k : K)
    (g : α → V → α) (a : α) : α :=
  let p := x.2.1[(hash k).toNat % chainCap x.1.keys.size]?.getD 0
  Chain.foldF x.1.keys x.1.vals x.2.2 k g p p a

theorem chainFold_eq [DecidableEq K] [Hashable K] {α : Type} (x : FinRel K V × Array Nat × Array Nat) (k : K)
    (g : α → V → α) (a : α) : chainFold x k g a = (chainGet x k).foldl g a := by
  simp only [chainFold, chainGet, Chain.foldF_eq, Chain.walkF_eq, List.append_nil]

/-- **The chained fibre is the scanned one**, order and repeats kept. -/
theorem FinRel.get_chains [DecidableEq K] [Hashable K] (r : FinRel K V) : chainGet r.chains = r.scanLookup :=
  funext fun k => by
    let cap := chainCap r.keys.size
    let slot := fun (j : Nat) => (r.keys[j]?.elim (0 : UInt64) hash).toNat % cap
    have hs : ∀ j, slot j < cap := fun j => Nat.mod_lt _ (by simp [cap, chainCap])
    obtain ⟨-, -, h3⟩ := Chain.inv_build (slot := slot) (cap := cap) r.keys.size
    obtain ⟨-, hr⟩ := h3 _ (Nat.mod_lt _ (by simp [cap, chainCap]) : (hash k).toNat % cap < cap)
    simp only [chainGet, FinRel.chains, Chain.walkF_eq, List.append_nil]
    show List.filterMap _ (List.reverse (Chain.rows _ _)) = _
    rw [hr, List.reverse_reverse]
    have hf : ∀ l : List Nat, (∀ j ∈ l, ¬ slot j = (hash k).toNat % cap → Chain.at? r.keys r.vals k j = none) →
        (l.filter fun j => slot j = (hash k).toNat % cap).filterMap (Chain.at? r.keys r.vals k) =
          l.filterMap (Chain.at? r.keys r.vals k) := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a l ih =>
        have ih := ih fun j hj => hl j (List.mem_cons_of_mem _ hj)
        by_cases e : slot a = (hash k).toNat % cap
        · simp only [List.filter_cons, e, decide_true, if_true, List.filterMap_cons, ih]
        · rw [List.filter_cons, if_neg (by simpa using e), ih, List.filterMap_cons, hl a List.mem_cons_self e]
    rw [hf _ fun j _ hne => ?_]
    · have := Chain.filterMap_at? k r.keys.toList r.vals.toList (by simp [r.len])
      simp only [Array.length_toList, Array.toArray_toList] at this
      rw [this]; rfl
    · unfold Chain.at?
      split
      · rename_i a ha
        split
        · rename_i e; subst e; exact absurd (by simp [slot, ha]) hne
        · rfl
      · rfl

/-- How the fibres of a `FinRel` keyed by `K` are looked up, and a list of keys listed once: by
    hashing when `K` has a `Hashable`, else by the scans `scanLookup` and `eraseDups`.  Each answer
    equals the scan's (`get_build`, `dedup_eq`), so a law proved of the scan holds of either; `build`
    makes the index once, and `get` answers each key from it. -/
class FibreIndex (K : Type) [DecidableEq K] where
  Index : Type → Type
  build {V : Type} : FinRel K V → Index V
  get {V : Type} : Index V → K → List V
  get_build {V : Type} (r : FinRel K V) : get (build r) = r.scanLookup
  /-- The head of `get`, read without making the fibre: `first` asks for no more. -/
  first? {V : Type} : Index V → K → Option V
  first?_eq {V : Type} (i : Index V) (k : K) : first? i k = (get i k).head?
  /-- `get` folded, read without making the fibre: a composite pushes each value straight on. -/
  foldFibre {V α : Type} : Index V → K → (α → V → α) → α → α
  foldFibre_eq {V α : Type} (i : Index V) (k : K) (g : α → V → α) (a : α) : foldFibre i k g a = (get i k).foldl g a
  dedup : List K → List K
  dedup_eq (l : List K) : dedup l = l.eraseDups

attribute [simp] FibreIndex.get_build FibreIndex.dedup_eq

/-- No hash: the scans themselves. -/
instance (priority := low) FibreIndex.scan [DecidableEq K] : FibreIndex K :=
  ⟨FinRel K, id, FinRel.scanLookup, fun _ => rfl, fun r k => (r.scanLookup k).head?, fun _ _ => rfl,
    fun r k g a => (r.scanLookup k).foldl g a, fun _ _ _ _ => rfl, List.eraseDups, fun _ => rfl⟩

/-- A hashable key: the rows chained by slot (`FinRel.chains`), and the hash set of `hashDedup`.  Chains and
    not the table `FinRel.fibres`, which allocates a bucket cell and an array per key. -/
instance FibreIndex.hash [DecidableEq K] [Hashable K] : FibreIndex K :=
  ⟨fun V => FinRel K V × Array Nat × Array Nat, FinRel.chains, chainGet, FinRel.get_chains, chainFirst, chainFirst_eq,
    chainFold, chainFold_eq, hashDedup, hashDedup_eq⟩

/-! ## Composites pushed onto arrays -/

section Bind

variable {C : Type}

/-- `r` then `h` on each value: the pairs `(a,c)` for `(a,b)` of `r` and `c` in `h(b)`, in order. -/
def FinRel.bindVals (r : FinRel K V) (h : V → List C) : FinRel K C :=
  FinRel.ofList (r.toList.flatMap fun p => (h p.2).map (p.1, ·))

/-- Push `k` with `c`. -/
@[inline] def pushPair (k : K) (a : Array K × Array C) (c : C) : Array K × Array C := (a.1.push k, a.2.push c)

theorem foldl_pushPair (k : K) (cs : List C) (a : Array K × Array C) :
    (cs.foldl (pushPair k) a).1.toList = a.1.toList ++ (cs.map (k, ·)).map Prod.fst ∧
      (cs.foldl (pushPair k) a).2.toList = a.2.toList ++ (cs.map (k, ·)).map Prod.snd := by
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih => obtain ⟨h1, h2⟩ := ih (pushPair k a c); simp_all [pushPair]

/-- Row `i` of `r` handed to `fo`, which pushes its key with each value of the value's fibre. -/
@[specialize] def bindStep (r : FinRel K V) (fo : K → V → Array K × Array C → Array K × Array C)
    (a : Array K × Array C) (i : Nat) : Array K × Array C :=
  match r.keys[i]?, r.vals[i]? with
  | some k, some v => fo k v a
  | _, _ => a

theorem bindStep_spec (r : FinRel K V) (h : V → List C) (fo : K → V → Array K × Array C → Array K × Array C)
    (hfo : ∀ k v a, fo k v a = (h v).foldl (pushPair k) a) : ∀ n, n ≤ r.keys.size →
    ((List.range' 0 n).foldl (bindStep r fo) (#[], #[])).1.toList =
        ((r.toList.take n).flatMap fun p => (h p.2).map (p.1, ·)).map Prod.fst ∧
      ((List.range' 0 n).foldl (bindStep r fo) (#[], #[])).2.toList =
        ((r.toList.take n).flatMap fun p => (h p.2).map (p.1, ·)).map Prod.snd
  | 0, _ => by simp
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := bindStep_spec r h fo hfo n (by omega)
    have hv : n < r.vals.size := r.len ▸ hn
    have ht : r.toList.take (n + 1) = r.toList.take n ++ [(r.keys[n], r.vals[n])] := by
      rw [List.take_succ]
      simp [FinRel.toList, List.getElem?_zip_eq_some, hn, hv]
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, ht, List.flatMap_append]
    simp only [Nat.zero_add, Nat.one_mul, bindStep, Array.getElem?_eq_getElem (by omega : n < r.keys.size),
      Array.getElem?_eq_getElem hv, hfo]
    obtain ⟨g1, g2⟩ := foldl_pushPair r.keys[n] (h r.vals[n]) (List.foldl (bindStep r fo) (#[], #[]) (List.range' 0 n))
    rw [g1, g2, h1, h2]
    simp

/-- `bindVals` with each fibre handed to `fo`, which pushes it straight onto the two arrays. -/
def bindArr (r : FinRel K V) (h : V → List C) (fo : K → V → Array K × Array C → Array K × Array C)
    (hfo : ∀ k v a, fo k v a = (h v).foldl (pushPair k) a) : FinRel K C :=
  let a := rangeFold (bindStep r fo) r.keys.size 0 (#[], #[])
  ⟨a.1, a.2, by
    have e := bindStep_spec r h fo hfo r.keys.size (Nat.le_refl _)
    rw [← rangeFold_eq] at e
    rw [← Array.length_toList, ← Array.length_toList, e.1, e.2, List.length_map, List.length_map]⟩

theorem bindArr_eq (r : FinRel K V) (h : V → List C) (fo : K → V → Array K × Array C → Array K × Array C)
    (hfo : ∀ k v a, fo k v a = (h v).foldl (pushPair k) a) : bindArr r h fo hfo = r.bindVals h := by
  have e := bindStep_spec r h fo hfo r.keys.size (Nat.le_refl _)
  rw [← rangeFold_eq] at e
  have ht : r.toList.take r.keys.size = r.toList := List.take_of_length_le (by simp [FinRel.toList, r.len])
  rw [ht] at e
  simp only [bindArr, FinRel.bindVals, FinRel.ofList, FinRel.mk.injEq]
  exact ⟨Array.ext' (by rw [e.1, List.toList_toArray]), Array.ext' (by rw [e.2, List.toList_toArray])⟩

/-- `bindVals` over the arrays; each fibre `h(b)` is still walked as the list it is. -/
def FinRel.bindValsTR (r : FinRel K V) (h : V → List C) : FinRel K C :=
  bindArr r h (fun k v a => (h v).foldl (pushPair k) a) fun _ _ _ => rfl

@[csimp] theorem FinRel.bindVals_eq_bindValsTR : @FinRel.bindVals = @FinRel.bindValsTR := by
  funext K V C r h; exact (bindArr_eq ..).symm

/-- `r` then the fibres of an index: `bindVals` at `get`. -/
def FinRel.bindIdx [DecidableEq V] [FibreIndex V] (r : FinRel K V) (i : FibreIndex.Index V C) : FinRel K C :=
  r.bindVals (FibreIndex.get i)

/-- `bindIdx` with each fibre folded straight out of the index: no fibre list is made. -/
def FinRel.bindIdxTR [DecidableEq V] [FibreIndex V] (r : FinRel K V) (i : FibreIndex.Index V C) : FinRel K C :=
  bindArr r (FibreIndex.get i) (fun k v a => FibreIndex.foldFibre i v (pushPair k) a)
    fun _ _ _ => FibreIndex.foldFibre_eq ..

@[csimp] theorem FinRel.bindIdx_eq_bindIdxTR : @FinRel.bindIdx = @FinRel.bindIdxTR := by
  funext K V C _ _ r i; exact (bindArr_eq ..).symm

end Bind

/-! ## A relation as a sum of representations -/

/-- A relation `K ⟶ V` held as the pairs of a `FinRel`, as its `Λ` form `k ↦` the list of values `k` is
    related to (a fiber enumerated, the keys possibly infinite), or as a decidable test such as `(· > ·)`.
    An operation enumerates whatever one argument can; a composite whose first factor is a `test` would
    have to enumerate the middle type, and is not formed.

    The meaning of an enumerating representation is a list: `app?` gives each key's fibre in
    representation order, with repeats, so order and multiplicity are part of it and the operations are
    those of the Kleisli category of `List` (`app?_comp`).  Each operation states its law on these lists;
    the relation `rel` is read off them by membership (`mem_app?`), a monad map from `List` to sets, and
    each `rel_*` law follows.  A `test` enumerates nothing and keeps only its membership test `mem`. -/
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

variable [DecidableEq K] [DecidableEq V] [FibreIndex K] [FibreIndex V]

/-- The membership test of `rel`. -/
def mem : RelRep K V → K → V → Bool
  | pairs r => fun k v => decide ((k, v) ∈ r.toList)
  | enum f => fun k v => decide (v ∈ f k)
  | test t => t

theorem mem_iff_rel : (R : RelRep K V) → (k : K) → (v : V) → (R.mem k v = true ↔ R.rel k v)
  | pairs _, _, _ => decide_eq_true_iff
  | enum _, _, _ => decide_eq_true_iff
  | test _, _, _ => Iff.rfl

/-- The list denotation: each key's fibre in representation order, with repeats — a `FinRel` in array
    order; `none` on a `test`, which enumerates nothing. -/
def app? : RelRep K V → Option (K → List V)
  | pairs r => some (FibreIndex.get (FibreIndex.build r))
  | enum f => some f
  | test _ => none

omit [DecidableEq V] [FibreIndex V] in
/-- `rel` is membership in the fibre list. -/
theorem mem_app? {R : RelRep K V} {f : K → List V} (h : R.app? = some f) (k : K) (v : V) :
    v ∈ f k ↔ R.rel k v := by
  cases R <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact FinRel.mem_scanLookup _ k v
  · exact Iff.rfl

theorem mem_eq_of_app? {R : RelRep K V} {f : K → List V} (h : R.app? = some f) (k : K) (v : V) :
    R.mem k v = decide (v ∈ f k) :=
  Bool.eq_iff_iff.2 ((mem_iff_rel R k v).trans ((mem_app? h k v).symm.trans decide_eq_true_iff.symm))

omit [DecidableEq V] [FibreIndex V] in
/-- A representation enumerates, or is a `test`. -/
theorem app?_cases (R : RelRep K V) : (∃ f, R.app? = some f) ∨ ∃ t, R = test t := by
  cases R with
  | pairs r => exact .inl ⟨_, rfl⟩
  | enum f => exact .inl ⟨_, rfl⟩
  | test t => exact .inr ⟨t, rfl⟩

/-- `R°`: a `FinRel` swaps its arrays, a fiber list becomes the test `v ∈ f(k)`, a test flips. -/
def conv : RelRep K V → RelRep V K
  | pairs r => pairs r.conv
  | enum f => test fun v k => decide (v ∈ f k)
  | test t => test fun v k => t k v

omit [DecidableEq K] [FibreIndex K] in
theorem rel_conv (R : RelRep K V) : R.conv.rel = R.rel° := by
  cases R with
  | pairs r => exact FinRel.rep_conv r
  | enum f => exact hom_ext fun _ _ => decide_eq_true_iff
  | test t => exact hom_ext fun _ _ => Iff.rfl

/-- `R ∩ S`: an enumerating side is filtered by the other side's test, the left one first; two tests
    conjoin. -/
def inter : RelRep K V → RelRep K V → RelRep K V
  | pairs r, S => pairs (FinRel.filter (fun k v => S.mem k v = true) r)
  | enum f, S => enum fun k => (f k).filter (S.mem k ·)
  | R, pairs s => pairs (FinRel.filter (fun k v => R.mem k v = true) s)
  | R, enum g => enum fun k => (g k).filter (R.mem k ·)
  | R, S => test fun k v => R.mem k v && S.mem k v

/-- `R ∩ S` on an enumerating `R`: `R`'s fibre, in order, filtered by `S`. -/
theorem app?_inter_left {R : RelRep K V} (S : RelRep K V) {f : K → List V} (h : R.app? = some f) :
    (inter R S).app? = some fun k => (f k).filter (S.mem k ·) := by
  cases R <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · simp only [inter, app?, FibreIndex.get_build, FinRel.scanLookup_filter, Bool.decide_eq_true]
  · cases S <;> rfl

/-- `R ∩ S` on a `test` `R`: `S`'s fibre, in order, filtered by `R`. -/
theorem app?_inter_right (t : K → V → Bool) {S : RelRep K V} {g : K → List V} (h : S.app? = some g) :
    (inter (test t) S).app? = some fun k => (g k).filter (t k ·) := by
  cases S <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · simp only [inter, app?, FibreIndex.get_build, FinRel.scanLookup_filter, Bool.decide_eq_true, mem]
  · rfl

theorem mem_inter (R S : RelRep K V) (k : K) (v : V) : (inter R S).mem k v = (R.mem k v && S.mem k v) := by
  rcases app?_cases R with ⟨f, hR⟩ | ⟨t, rfl⟩
  · rw [mem_eq_of_app? (app?_inter_left S hR), mem_eq_of_app? hR]; simp [List.mem_filter]
  · rcases app?_cases S with ⟨g, hS⟩ | ⟨u, rfl⟩
    · rw [mem_eq_of_app? (app?_inter_right t hS), mem_eq_of_app? hS]
      show _ = (t k v && _); cases h : t k v <;> simp [List.mem_filter, h]
    · rfl

theorem rel_inter (R S : RelRep K V) : (inter R S).rel = R.rel ∩ S.rel :=
  hom_ext fun k v => by simp only [inter_apply, ← mem_iff_rel, mem_inter, Bool.and_eq_true]

/-- `R ∪ S`: two `FinRel`s append their arrays, two enumerating sides append their fibers; a test on
    either side makes the union a test. -/
def union : RelRep K V → RelRep K V → RelRep K V
  | pairs r, pairs s => pairs (FinRel.union r s)
  | pairs r, enum g => let i := FibreIndex.build r; enum fun k => FibreIndex.get i k ++ g k
  | enum f, pairs s => let i := FibreIndex.build s; enum fun k => f k ++ FibreIndex.get i k
  | enum f, enum g => enum fun k => f k ++ g k
  | R, S => test fun k v => R.mem k v || S.mem k v

/-- `R ∪ S` appends the fibres: a monoid, neither idempotent nor commutative on lists — those two hold
    only of `rel` (`rel_union`). -/
theorem app?_union {R S : RelRep K V} {f g : K → List V} (hR : R.app? = some f) (hS : S.app? = some g) :
    (union R S).app? = some fun k => f k ++ g k := by
  cases R <;> cases S <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at hR hS <;> subst hR hS <;>
    first | rfl | simp only [union, app?, FibreIndex.get_build, FinRel.scanLookup_union]

theorem mem_union (R S : RelRep K V) (k : K) (v : V) : (union R S).mem k v = (R.mem k v || S.mem k v) := by
  rcases app?_cases R with ⟨f, hR⟩ | ⟨t, rfl⟩
  · rcases app?_cases S with ⟨g, hS⟩ | ⟨u, rfl⟩
    · rw [mem_eq_of_app? (app?_union hR hS), mem_eq_of_app? hR, mem_eq_of_app? hS]; simp [List.mem_append]
    · cases R <;> first | rfl | simp [app?] at hR
  · cases S <;> rfl

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

/-- `dom R`: the key `k` when its fibre is nonempty; `none` on a `test`, whose fibre is not searched. -/
def dom (R : RelRep K V) : Option (RelRep K K) :=
  R.app?.map fun f => enum fun k => if (f k).isEmpty then [] else [k]

omit [DecidableEq V] [FibreIndex V] in
/-- `dom R` lists each key with a nonempty fibre, once. -/
theorem dom_of_app? {R : RelRep K V} {f : K → List V} (h : R.app? = some f) :
    dom R = some (enum fun k => if (f k).isEmpty then [] else [k]) := by
  simp only [dom, h, Option.map_some]

omit [DecidableEq V] [FibreIndex V] in
theorem rel_dom {R : RelRep K V} {T : RelRep K K} (h : dom R = some T) : T.rel = Alg.dom R.rel := by
  cases hf : R.app? with
  | none => simp [dom, hf] at h
  | some f =>
    simp only [dom, hf, Option.map_some, Option.some.injEq] at h
    subst h
    refine hom_ext fun k k' => ⟨fun hm => ?_, fun ⟨e, v, hv, _⟩ => ?_⟩
    · simp only [RelRep.rel] at hm
      cases hfk : f k with
      | nil => simp [hfk] at hm
      | cons v vs =>
        simp only [hfk, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.mem_singleton] at hm
        rw [hm]
        have hv := (mem_app? hf k v).1 (by simp [hfk])
        exact ⟨rfl, v, hv, hv⟩
    · have e' : k = k' := e
      subst e'
      have hv' := (mem_app? hf k v).2 hv
      simp only [RelRep.rel]
      cases hfk : f k with
      | nil => rw [hfk] at hv'; exact absurd hv' List.not_mem_nil
      | cons => simp

/-- `ran R = dom R°`: computed when `R°` enumerates, i.e. on a `FinRel`; `none` otherwise. -/
def ran (R : RelRep K V) : Option (RelRep V V) := R.conv.dom

omit [DecidableEq K] [FibreIndex K] in
theorem rel_ran {R : RelRep K V} {T : RelRep V V} (h : ran R = some T) : T.rel = Alg.ran R.rel := by
  rw [rel_dom h, rel_conv]; rfl

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] in
/-- Every pair of a member of `xs` and a member of `ys`. -/
def cross (xs : List V) (ys : List W) : List (V × W) := xs.flatMap fun v => ys.map (v, ·)

omit [DecidableEq K] [FibreIndex K] [DecidableEq V] [FibreIndex V] [DecidableEq L] [FibreIndex L] [DecidableEq W] [FibreIndex W] in
theorem mem_cross (xs : List V) (ys : List W) (q : V × W) : q ∈ cross xs ys ↔ q.1 ∈ xs ∧ q.2 ∈ ys := by
  obtain ⟨v, w⟩ := q; simp [cross]

/-- `⟨R,S⟩`: two `FinRel`s pair the pairs sharing a key, two enumerating sides pair their fibres; a
    `test` on either side makes the split a test. -/
def pair : RelRep K V → RelRep K W → RelRep K (V × W)
  | pairs r, pairs s => let i := FibreIndex.build s
    pairs (FinRel.ofList (r.toList.flatMap fun p => (FibreIndex.get i p.1).map fun w => (p.1, (p.2, w))))
  | pairs r, enum g => let i := FibreIndex.build r; enum fun k => cross (FibreIndex.get i k) (g k)
  | enum f, pairs s => let i := FibreIndex.build s; enum fun k => cross (f k) (FibreIndex.get i k)
  | enum f, enum g => enum fun k => cross (f k) (g k)
  | R, S => test fun k q => R.mem k q.1 && S.mem k q.2

omit [DecidableEq L] [FibreIndex L] in
/-- `⟨R,S⟩` pairs each value of `R`'s fibre, in order, with each of `S`'s. -/
theorem app?_pair {R : RelRep K V} {S : RelRep K W} {f : K → List V} {g : K → List W} (hR : R.app? = some f)
    (hS : S.app? = some g) : (pair R S).app? = some fun k => cross (f k) (g k) := by
  cases R <;> cases S <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at hR hS <;> subst hR hS <;>
    first | rfl | (simp only [pair, app?, FibreIndex.get_build]; done) | skip
  rename_i r s
  simp only [pair, app?, FibreIndex.get_build, FinRel.scanLookup_ofList, Option.some.injEq]
  funext k
  have := FinRel.filterMap_sel_flatMap (fun k v => (s.scanLookup k).map (v, ·)) k r.toList
  simp only [List.map_map, Function.comp_def] at this
  exact this

omit [DecidableEq L] [FibreIndex L] in
theorem mem_pair (R : RelRep K V) (S : RelRep K W) (k : K) (q : V × W) :
    (pair R S).mem k q = (R.mem k q.1 && S.mem k q.2) := by
  rcases app?_cases R with ⟨f, hR⟩ | ⟨t, rfl⟩
  · rcases app?_cases S with ⟨g, hS⟩ | ⟨u, rfl⟩
    · rw [mem_eq_of_app? (app?_pair hR hS), mem_eq_of_app? hR, mem_eq_of_app? hS]; simp [mem_cross]
    · cases R <;> first | rfl | simp [app?] at hR
  · cases S <;> rfl

omit [DecidableEq L] [FibreIndex L] in
theorem rel_pair (R : RelRep K V) (S : RelRep K W) : (pair R S).rel = rpair R.rel S.rel :=
  hom_ext fun k q => by simp only [rpair, ← mem_iff_rel, mem_pair, Bool.and_eq_true]

/-- `R × S`: two `FinRel`s pair their pairs, two enumerating sides pair their fibres; a `test` on
    either side makes the product a test. -/
def prod : RelRep K V → RelRep L W → RelRep (K × L) (V × W)
  | pairs r, pairs s => pairs (FinRel.ofList ((cross r.toList s.toList).map fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))))
  | pairs r, enum g => let i := FibreIndex.build r; enum fun k => cross (FibreIndex.get i k.1) (g k.2)
  | enum f, pairs s => let i := FibreIndex.build s; enum fun k => cross (f k.1) (FibreIndex.get i k.2)
  | enum f, enum g => enum fun k => cross (f k.1) (g k.2)
  | R, S => test fun k q => R.mem k.1 q.1 && S.mem k.2 q.2

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
theorem app?_prod {R : RelRep K V} {S : RelRep L W} {f : K → List V} {g : L → List W} (hR : R.app? = some f)
    (hS : S.app? = some g) : (prod R S).app? = some fun k => cross (f k.1) (g k.2) := by
  cases R <;> cases S <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at hR hS <;> subst hR hS <;>
    first | rfl | (simp only [prod, app?, FibreIndex.get_build]; done) | skip
  simp only [prod, app?, FibreIndex.get_build, FinRel.scanLookup_ofList, Option.some.injEq]
  exact funext fun k => filterMap_sel_cross k.1 k.2 _ _

theorem mem_prod (R : RelRep K V) (S : RelRep L W) (k : K × L) (q : V × W) :
    (prod R S).mem k q = (R.mem k.1 q.1 && S.mem k.2 q.2) := by
  rcases app?_cases R with ⟨f, hR⟩ | ⟨t, rfl⟩
  · rcases app?_cases S with ⟨g, hS⟩ | ⟨u, rfl⟩
    · rw [mem_eq_of_app? (app?_prod hR hS), mem_eq_of_app? hR, mem_eq_of_app? hS]; simp [mem_cross]
    · cases R <;> first | rfl | simp [app?] at hR
  · cases S <;> rfl

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

/-- `[R,S]` on `K ⊕ L`: two `FinRel`s tag and append their pairs, two enumerating sides answer a key
    from its summand's fibre; a `test` on either side makes the junction a test. -/
def junction : RelRep K V → RelRep L V → RelRep (K ⊕ L) V
  | pairs r, pairs s => pairs (FinRel.ofList (r.toList.map (fun p => (Sum.inl p.1, p.2)) ++ s.toList.map fun p => (Sum.inr p.1, p.2)))
  | pairs r, enum g => let i := FibreIndex.build r; enum (Sum.elim (FibreIndex.get i) g)
  | enum f, pairs s => let i := FibreIndex.build s; enum (Sum.elim f (FibreIndex.get i))
  | enum f, enum g => enum (Sum.elim f g)
  | R, S => test (Sum.elim R.mem S.mem)

omit [DecidableEq W] [FibreIndex W] in
/-- `[R,S]` answers a key from its summand's fibre. -/
theorem app?_junction {R : RelRep K V} {S : RelRep L V} {f : K → List V} {g : L → List V} (hR : R.app? = some f)
    (hS : S.app? = some g) : (junction R S).app? = some (Sum.elim f g) := by
  cases R <;> cases S <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at hR hS <;> subst hR hS <;>
    first | rfl | (simp only [junction, app?, FibreIndex.get_build]; done) | skip
  simp only [junction, app?, FibreIndex.get_build, FinRel.scanLookup_ofList, Option.some.injEq]
  have hn : ∀ {X Y : Type} (l : List X), l.filterMap (fun _ => (none : Option Y)) = [] := fun l => by
    induction l <;> simp_all
  funext x
  cases x <;> simp [List.filterMap_append, List.filterMap_map, Function.comp_def, FinRel.sel, FinRel.scanLookup, hn] <;>
    rfl

omit [DecidableEq W] [FibreIndex W] in
theorem mem_junction (R : RelRep K V) (S : RelRep L V) (x : K ⊕ L) (v : V) :
    (junction R S).mem x v = Sum.elim R.mem S.mem x v := by
  rcases app?_cases R with ⟨f, hR⟩ | ⟨t, rfl⟩
  · rcases app?_cases S with ⟨g, hS⟩ | ⟨u, rfl⟩
    · rw [mem_eq_of_app? (app?_junction hR hS)]
      cases x
      · exact (mem_eq_of_app? hR _ v).symm
      · exact (mem_eq_of_app? hS _ v).symm
    · cases R <;> first | rfl | simp [app?] at hR
  · cases S <;> rfl

omit [DecidableEq W] [FibreIndex W] in
theorem rel_junction (R : RelRep K V) (S : RelRep L V) :
    (junction R S).rel = junc (sumCop ⟨K⟩ ⟨L⟩) R.rel S.rel :=
  hom_ext fun x v => by
    have hj := junc_apply R.rel S.rel
    rw [← mem_iff_rel, mem_junction]
    cases x with
    | inl k => rw [hj.1]; exact mem_iff_rel R k v
    | inr l => rw [hj.2]; exact mem_iff_rel S l v

/-- `Λ(R)`: each key's fibre list, read as a set through `Λ(∋ₗ)`; `none` on a `test`. -/
def transpose (R : RelRep K V) : Option (RelRep K (List V)) := R.app?.map ofFn

omit [DecidableEq V] [FibreIndex V] in
/-- `Λ(R)` sends `k` to its whole fibre list, order and repeats kept. -/
theorem transpose_of_app? {R : RelRep K V} {f : K → List V} (h : R.app? = some f) : transpose R = some (ofFn f) := by
  simp only [transpose, h, Option.map_some]

omit [DecidableEq V] [FibreIndex V] in
theorem rel_transpose {R : RelRep K V} {T : RelRep K (List V)} (h : transpose R = some T) :
    T.rel ≫ Λ (lmem V) = Λ R.rel := by
  cases hf : R.app? with
  | none => simp [transpose, hf] at h
  | some f =>
    simp only [transpose, hf, Option.map_some, Option.some.injEq] at h
    subst h
    rw [rel_ofFn, Λ_eq_classifier, Λ_eq_classifier]
    have hs : ∀ k, (fun v => v ∈ f k) = fun v => R.rel k v := fun k => funext fun v => propext (mem_app? hf k v)
    exact hom_ext fun k G => ⟨fun ⟨_, (e : _ = f k), (hG : G = _)⟩ => by subst e; exact hG.trans (hs k),
      fun (hG : G = _) => ⟨f k, rfl, hG.trans (hs k).symm⟩⟩

end Tabulate

/-- `R S`, first `R` then `S`.  An enumerating `R` hands each of its values to `S`: a `FinRel` or a fiber
    list second is looked up, a test second is tried on each.  A `test` first would have to enumerate
    the middle type, so it gives `none`. -/
def comp [DecidableEq C] : RelRep K V → RelRep V C → Option (RelRep K C)
  | pairs r, pairs s => some (pairs (r.bindIdx (FibreIndex.build s)))
  | pairs r, enum h => some (pairs (r.bindVals h))
  | pairs r, test t => let i := FibreIndex.build r; some (test fun k c => (FibreIndex.get i k).any (t · c))
  | enum f, pairs s => let i := FibreIndex.build s; some (enum fun k => (f k).flatMap (FibreIndex.get i))
  | enum f, enum h => some (enum fun k => (f k).flatMap h)
  | enum f, test t => some (test fun k c => (f k).any (t · c))
  | test _, _ => none

/-- Only an enumerating first factor composes. -/
theorem app?_of_comp [DecidableEq C] {R : RelRep K V} {S : RelRep V C} {T : RelRep K C} (h : comp R S = some T) :
    ∃ f, R.app? = some f := by
  rcases app?_cases R with hR | ⟨t, rfl⟩
  · exact hR
  · simp [comp] at h

/-- `R S` is Kleisli composition in `List`: each value of `R`'s fibre, in order, hands on `S`'s fibre. -/
theorem app?_comp [DecidableEq C] {R : RelRep K V} {S : RelRep V C} {T : RelRep K C} (h : comp R S = some T)
    {f : K → List V} {g : V → List C} (hR : R.app? = some f) (hS : S.app? = some g) :
    T.app? = some fun a => (f a).flatMap g := by
  cases R <;> cases S <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at hR hS <;>
    simp only [comp, Option.some.injEq] at h <;> subst hR hS h <;> first | rfl | skip
  all_goals simp only [app?, FibreIndex.get_build, FinRel.bindIdx, FinRel.bindVals, FinRel.scanLookup_ofList,
    Option.some.injEq]
  · rename_i r s; exact funext fun a => FinRel.filterMap_sel_flatMap (fun _ b => s.scanLookup b) a r.toList
  · rename_i r g; exact funext fun a => FinRel.filterMap_sel_flatMap (fun _ b => g b) a r.toList

/-- A `test` second: `T` tests some value of `R`'s fibre. -/
theorem mem_comp [DecidableEq C] {R : RelRep K V} {S : RelRep V C} {T : RelRep K C} (h : comp R S = some T)
    {f : K → List V} (hR : R.app? = some f) (a : K) (c : C) : T.mem a c = (f a).any (S.mem · c) := by
  rcases app?_cases S with ⟨g, hS⟩ | ⟨t, rfl⟩
  · rw [mem_eq_of_app? (app?_comp h hR hS)]
    refine Bool.eq_iff_iff.2 ((decide_eq_true_iff).trans ?_)
    simp only [List.mem_flatMap, List.any_eq_true, mem_eq_of_app? hS, decide_eq_true_eq]
  · cases R <;> simp only [app?, FibreIndex.get_build, Option.some.injEq, reduceCtorEq] at hR <;>
      simp only [comp, Option.some.injEq] at h <;> subst hR h <;> first | rfl | simp [mem, FibreIndex.get_build]

theorem rel_comp [DecidableEq C] {R : RelRep K V} {S : RelRep V C} {T : RelRep K C} (h : comp R S = some T) :
    T.rel = R.rel ≫ S.rel := by
  obtain ⟨_, hR⟩ := app?_of_comp h
  exact hom_ext fun a c => by
    simp only [comp_apply, ← mem_iff_rel, mem_comp h hR, List.any_eq_true, mem_app? hR]

/-- `≫` is associative on fibre lists, since `flatMap` is. -/
theorem app?_comp_assoc {D : Type} [DecidableEq C] [DecidableEq D] {R : RelRep K V} {S : RelRep V C}
    {U : RelRep C D} {RS : RelRep K C} {SU : RelRep V D} {W W' : RelRep K D} {f : K → List V} {g : V → List C}
    {h : C → List D} (hR : R.app? = some f) (hS : S.app? = some g) (hU : U.app? = some h)
    (hRS : comp R S = some RS) (hW : comp RS U = some W) (hSU : comp S U = some SU) (hW' : comp R SU = some W') :
    W.app? = W'.app? := by
  rw [app?_comp hW (app?_comp hRS hR hS) hU, app?_comp hW' hR (app?_comp hSU hS hU)]
  simp only [List.flatMap_assoc]

/-- `ofFn id` is a unit on each side: `[a].flatMap g = g a` and `xs.flatMap ([·]) = xs`. -/
theorem app?_comp_id {R : RelRep K V} {f : K → List V} (hR : R.app? = some f) {T T' : RelRep K V}
    (hl : comp (ofFn id) R = some T) (hr : comp R (ofFn id) = some T') : T.app? = some f ∧ T'.app? = some f := by
  constructor
  · rw [app?_comp hl rfl hR]; simp
  · rw [app?_comp hr hR rfl]; simp

/-! ### `est` and `thin` on an enumerated fibre -/

section Division

omit [DecidableEq V] [FibreIndex V] in
/-- `X / Y`: `k (X/Y) v` iff `X k c` for every `c` with `Y v c`.  The divisor's fibre is enumerated
    and the result is a test; a `test` divisor gives `none`. -/
def div [DecidableEq C] (X : RelRep K C) (Y : RelRep V C) : Option (RelRep K V) :=
  Y.app?.map fun g => test fun k v => (g v).all (X.mem k ·)

theorem rel_div [DecidableEq C] {X : RelRep K C} {Y : RelRep V C} {Z : RelRep K V} (h : div X Y = some Z) :
    Z.rel = X.rel / Y.rel := by
  cases hf : Y.app? with
  | none => simp [div, hf] at h
  | some g =>
    simp only [div, hf, Option.map_some, Option.some.injEq] at h
    subst h
    exact hom_ext fun k v => List.all_eq_true.trans
      (forall_congr' fun c => imp_congr (mem_app? hf v c) (mem_iff_rel X k c))

omit [DecidableEq V] [FibreIndex V] in
/-- `S \ R ≜ (R°/S°)°`: the divisor's converse fibre is enumerated, so only a `FinRel` `S` divides. -/
def leftDiv [DecidableEq C] (S : RelRep K V) (R : RelRep K C) : Option (RelRep V C) :=
  (div R.conv S.conv).map conv

theorem rel_leftDiv [DecidableEq C] {S : RelRep K V} {R : RelRep K C} {Z : RelRep V C}
    (h : leftDiv S R = some Z) : Z.rel = S.rel \ R.rel := by
  cases hD : div R.conv S.conv with
  | none => simp [leftDiv, hD] at h
  | some D =>
    simp only [leftDiv, hD, Option.map_some, Option.some.injEq] at h
    subst h
    rw [rel_conv, rel_div hD, rel_conv, rel_conv]
    rfl

/-- `R /ₛ S ≜ (R/S) ∩ (S/R)°`: both fibres are enumerated, so neither side may be a `test`. -/
def symmDiv [DecidableEq C] (R : RelRep K C) (S : RelRep V C) : Option (RelRep K V) :=
  (div R S).bind fun D => (div S R).map fun E => inter D E.conv

theorem rel_symmDiv [DecidableEq C] {R : RelRep K C} {S : RelRep V C} {Z : RelRep K V}
    (h : symmDiv R S = some Z) : Z.rel = R.rel /ₛ S.rel := by
  cases h1 : div R S with
  | none => simp [symmDiv, h1] at h
  | some D =>
    cases h2 : div S R with
    | none => simp [symmDiv, h1, h2] at h
    | some E =>
      simp only [symmDiv, h1, h2, Option.bind_some, Option.map_some, Option.some.injEq] at h
      subst h
      rw [rel_inter, rel_conv, rel_div h1, rel_div h2]
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

/-- `Λ(R) est(L) = R ∩ (L/R)°`, from `est(L) ≜ ∋ ∩ (∈\L°)`: on a fibre list this is `estList`;
    `none` on a `test`. -/
def est (L : RelRep V V) (R : RelRep K V) : Option (RelRep K V) :=
  (div L R).map fun D => inter R D.conv

theorem rel_est {L : RelRep V V} {R T : RelRep K V} (h : est L R = some T) :
    T.rel = Λ R.rel ≫ Freyd.Alg.est L.rel := by
  cases hD : div L R with
  | none => simp [est, hD] at h
  | some D =>
    simp only [est, hD, Option.map_some, Option.some.injEq] at h
    subst h
    rw [rel_inter, rel_conv, rel_div hD]
    exact hom_ext fun k v => (Λ_comp_est_apply _ _ k v).symm

/-- `est(L)` on the fibre list: keep, in order, the members `L`-below every member. -/
theorem app?_est {L : RelRep V V} {R T : RelRep K V} (h : est L R = some T) {f : K → List V} (hR : R.app? = some f) :
    T.app? = some fun k => estList L.mem (f k) := by
  simp only [est, div, hR, Option.map_some, Option.some.injEq] at h
  subst h
  exact app?_inter_left _ hR

/-- `Λ(R) thin(Q)`: each fibre cut by `thinList`; `none` on a `test`. -/
def thin (Q : RelRep V V) (R : RelRep K V) : Option (RelRep K V) :=
  R.app?.map fun f => enum fun k => thinList Q.mem (f k)

/-- `Λ(R) thin(Q)` cuts each fibre list by `thinList`. -/
theorem thin_of_app? {Q : RelRep V V} {R : RelRep K V} {f : K → List V} (h : R.app? = some f) :
    thin Q R = some (enum fun k => thinList Q.mem (f k)) := by
  simp only [thin, h, Option.map_some]

/-- `R ⊕ S`, `R` overridden where it is empty: `R`'s fibre where nonempty, else `S`'s; `none` when `R`
    is a `test`, whose emptiness is not searched. -/
def override (R S : RelRep K V) : Option (RelRep K V) :=
  R.app?.map fun f => match S.app? with
    | some g => enum fun k => if f k = [] then g k else f k
    | none => test fun k v => if f k = [] then S.mem k v else decide (v ∈ f k)

theorem override_of_app? {R S : RelRep K V} {f g : K → List V} (hR : R.app? = some f) (hS : S.app? = some g) :
    override R S = some (enum fun k => if f k = [] then g k else f k) := by
  simp only [override, hR, hS, Option.map_some]

theorem mem_override {R S T : RelRep K V} (h : override R S = some T) {f : K → List V} (hR : R.app? = some f)
    (k : K) (v : V) : T.mem k v = if f k = [] then S.mem k v else R.mem k v := by
  rw [mem_eq_of_app? hR]
  rcases app?_cases S with ⟨g, hS⟩ | ⟨t, rfl⟩
  · rw [override_of_app? hR hS, Option.some.injEq] at h; subst h
    rw [mem_eq_of_app? (R := enum _) rfl, mem_eq_of_app? hS]; split <;> rfl
  · simp only [override, hR, app?.eq_3, Option.map_some, Option.some.injEq] at h; subst h; rfl

/-- `R ⊕ S` relates `k` as `R` does, or as `S` does where `R` relates `k` to nothing. -/
theorem rel_override {R S T : RelRep K V} (h : override R S = some T) (k : K) (v : V) :
    T.rel k v ↔ R.rel k v ∨ (∀ w, ¬ R.rel k w) ∧ S.rel k v := by
  obtain ⟨f, hR⟩ : ∃ f, R.app? = some f := by
    rcases app?_cases R with hR | ⟨t, rfl⟩
    · exact hR
    · simp [override, app?] at h
  rw [← mem_iff_rel, mem_override h hR]
  by_cases e : f k = []
  · simp only [e, if_pos, mem_iff_rel, ← mem_app? hR, List.not_mem_nil, false_or, not_false_eq_true, implies_true,
      true_and]
  · obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ e
    simp only [e, if_false, mem_iff_rel]
    exact ⟨.inl, fun | .inl h => h | .inr ⟨hn, _⟩ => absurd ((mem_app? hR k w).1 hw) (hn w)⟩

omit [DecidableEq V] [FibreIndex V] in
/-- The first value of each fibre, in representation order; `none` on a `test`. -/
def first : RelRep K V → Option (RelRep K V)
  | pairs r => let i := FibreIndex.build r; some (enum fun k => (FibreIndex.first? i k).toList)
  | R => R.app?.map fun f => enum fun k => (f k).head?.toList

omit [DecidableEq V] [FibreIndex V] in
/-- The last value of each fibre, in representation order; `none` on a `test`. -/
def last (R : RelRep K V) : Option (RelRep K V) := R.app?.map fun f => enum fun k => (f k).getLast?.toList

omit [DecidableEq V] [FibreIndex V] in
theorem first_of_app? {R : RelRep K V} {f : K → List V} (h : R.app? = some f) :
    first R = some (enum fun k => (f k).head?.toList) := by
  cases R <;> simp only [app?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [first, app?, FibreIndex.first?_eq]

omit [DecidableEq V] [FibreIndex V] in
theorem last_of_app? {R : RelRep K V} {f : K → List V} (h : R.app? = some f) :
    last R = some (enum fun k => (f k).getLast?.toList) := by
  simp only [last, h, Option.map_some]

omit [DecidableEq V] [FibreIndex V] in
/-- A fibre selector keeps one value of each nonempty fibre: `T ⊑ R`, and `T` relates every key `R` does. -/
theorem rel_select {R T : RelRep K V} {sel : List V → Option V} (hs : ∀ l v, sel l = some v → v ∈ l)
    (hn : ∀ l, l ≠ [] → ∃ v, sel l = some v) {f : K → List V} (hR : R.app? = some f)
    (h : T = enum fun k => (sel (f k)).toList) :
    (∀ k v, T.rel k v → R.rel k v) ∧ ∀ k v, R.rel k v → ∃ w, T.rel k w := by
  subst h
  refine ⟨fun k v hv => (mem_app? hR k v).1 (hs _ _ (Option.mem_toList.1 hv)), fun k v hv => ?_⟩
  obtain ⟨w, hw⟩ := hn (f k) fun e => by rw [← mem_app? hR, e] at hv; exact List.not_mem_nil hv
  exact ⟨w, Option.mem_toList.2 hw⟩

omit [DecidableEq V] [FibreIndex V] in
theorem rel_first {R T : RelRep K V} (h : first R = some T) :
    (∀ k v, T.rel k v → R.rel k v) ∧ ∀ k v, R.rel k v → ∃ w, T.rel k w := by
  obtain ⟨f, hR⟩ : ∃ f, R.app? = some f := by
    rcases app?_cases R with hR | ⟨t, rfl⟩
    · exact hR
    · simp [first, app?] at h
  rw [first_of_app? hR, Option.some.injEq] at h
  exact rel_select (fun _ _ => List.mem_of_mem_head?) (fun l e => ⟨_, (List.head?_eq_some_head e)⟩) hR h.symm

omit [DecidableEq V] [FibreIndex V] in
theorem rel_last {R T : RelRep K V} (h : last R = some T) :
    (∀ k v, T.rel k v → R.rel k v) ∧ ∀ k v, R.rel k v → ∃ w, T.rel k w := by
  obtain ⟨f, hR⟩ : ∃ f, R.app? = some f := by
    rcases app?_cases R with hR | ⟨t, rfl⟩
    · exact hR
    · simp [last, app?] at h
  rw [last_of_app? hR, Option.some.injEq] at h
  exact rel_select (fun _ _ => List.mem_of_getLast?) (fun l e => ⟨_, List.getLast?_eq_some_getLast e⟩) hR h.symm

omit [DecidableEq K] [FibreIndex K] in
/-- `thinList_spec` at a preorder `Q` held as a `RelRep`. -/
theorem thinList_rel_spec {Q : RelRep V V} (hr : 𝟙 _ ⊑ Q.rel) (ht : Q.rel ≫ Q.rel ⊑ Q.rel) (xs : List V) :
    (∀ y ∈ thinList Q.mem xs, y ∈ xs) ∧ ∀ z ∈ xs, ∃ w ∈ thinList Q.mem xs, Q.rel w z :=
  have hs := thinList_spec (q := Q.mem)
    (fun v => (mem_iff_rel Q v v).2 (le_iff.mp hr v v (by rw [id_apply])))
    (fun u v w h1 h2 => (mem_iff_rel Q u w).2
      (le_iff.mp ht u w ⟨v, (mem_iff_rel Q u v).1 h1, (mem_iff_rel Q v w).1 h2⟩)) xs
  ⟨hs.1, fun z hz => (hs.2 z hz).imp fun w ⟨hw, hq⟩ => ⟨hw, (mem_iff_rel Q w z).1 hq⟩⟩

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

/-- For a preorder `Q`, each computed fibre is a `thin(Q)` choice of `R`'s fibre. -/
theorem rel_thin {Q : RelRep V V} {R T : RelRep K V} (hr : 𝟙 _ ⊑ Q.rel) (ht : Q.rel ≫ Q.rel ⊑ Q.rel)
    (h : thin Q R = some T) : Λ T.rel ⊑ Λ R.rel ≫ thinRel Q.rel := by
  cases hf : R.app? with
  | none => simp [thin, hf] at h
  | some f =>
    simp only [thin, hf, Option.map_some, Option.some.injEq] at h
    subst h
    exact Λ_le_thin fun k => have hs := thinList_rel_spec hr ht (f k)
      ⟨fun y hy => (mem_app? hf k y).1 (hs.1 y hy), fun z hz => hs.2 z ((mem_app? hf k z).2 hz)⟩

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

/-- `⦇[B,S]⦈` with every fibre cut by `post`; `none` when `B` or `S` is a `test`. -/
def foldWith (post : List V → List V) (B : RelRep L V) (S : RelRep (E × V) V) :
    Option (RelRep (ConsList L E) V) :=
  B.app?.bind fun b => S.app?.map fun s => enum (foldList post b s)

/-- `⦇[B,S]⦈`, each fibre enumerated. -/
def fold (B : RelRep L V) (S : RelRep (E × V) V) : Option (RelRep (ConsList L E) V) := foldWith id B S

/-- The fold's fibre lists: at `wrap` the base's, at `cons` the step's over each value in order, each cut
    by `post`. -/
theorem foldWith_of_app? {post : List V → List V} {B : RelRep L V} {S : RelRep (E × V) V} {b : L → List V}
    {s : E × V → List V} (hB : B.app? = some b) (hS : S.app? = some s) :
    foldWith post B S = some (enum (foldList post b s)) := by
  simp only [foldWith, hB, hS, Option.bind_some, Option.map_some]

/-- `⦇thin(Q)·Λ[B,S]⦈`: the fold with every fibre thinned by `Q`. -/
def foldThin (Q : RelRep V V) (B : RelRep L V) (S : RelRep (E × V) V) : Option (RelRep (ConsList L E) V) :=
  foldWith (thinList Q.mem) B S

/-- The induction behind `rel_fold` and `rel_foldThin`: when `post` keeps a `P`-lower bound of every
    member and the step preserves `P`, the computed fibre lies in the fold's and bounds it. -/
theorem foldWith_spec {post : List V → List V} {B : RelRep L V} {S : RelRep (E × V) V}
    {T : RelRep (ConsList L E) V} {P : V → V → Prop}
    (hpost : ∀ xs, (∀ y ∈ post xs, y ∈ xs) ∧ ∀ z ∈ xs, ∃ w ∈ post xs, P w z)
    (htrans : ∀ u v w, P u v → P v w → P u w)
    (hmono : ∀ e w r z, P w r → S.rel (e, r) z → ∃ c, S.rel (e, w) c ∧ P c z)
    (h : foldWith post B S = some T) (x : ConsList L E) :
    (∀ y, T.rel x y → cataFold (C := ⟨V⟩) (junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel) x y)
      ∧ ∀ z, cataFold (C := ⟨V⟩) (junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel) x z → ∃ w, T.rel x w ∧ P w z := by
  cases hb : B.app? with
  | none => simp [foldWith, hb] at h
  | some b =>
    cases hs : S.app? with
    | none => simp [foldWith, hb, hs] at h
    | some s =>
      simp only [foldWith, hb, hs, Option.bind_some, Option.map_some, Option.some.injEq] at h
      subst h
      have hj := junc_apply B.rel S.rel
      induction x with
      | wrap l =>
        obtain ⟨hsub, hdom⟩ := hpost (b l)
        refine ⟨fun y hy => ?_, fun z hz => ?_⟩
        · rw [cataFold_wrap]; exact (hj.1 l y).2 ((mem_app? hb l y).1 (hsub y hy))
        · rw [cataFold_wrap] at hz; exact hdom z ((mem_app? hb l z).2 ((hj.1 l z).1 hz))
      | cons e x ih =>
        obtain ⟨hsub, hdom⟩ := ih
        obtain ⟨psub, pdom⟩ := hpost ((foldList post b s x).flatMap fun v => s (e, v))
        refine ⟨fun y hy => ?_, fun z hz => ?_⟩
        · obtain ⟨r, hr, hy⟩ := List.mem_flatMap.1 (psub y hy)
          rw [cataFold_cons]
          exact ⟨r, hsub r hr, (hj.2 (e, r) y).2 ((mem_app? hs _ y).1 hy)⟩
        · rw [cataFold_cons] at hz
          obtain ⟨r, hr, hz⟩ := hz
          obtain ⟨w, hw, hwr⟩ := hdom r hr
          obtain ⟨c, hc, hcz⟩ := hmono e w r z hwr ((hj.2 (e, r) z).1 hz)
          obtain ⟨w', hw', hw'c⟩ := pdom c (List.mem_flatMap.2 ⟨w, hw, (mem_app? hs _ c).2 hc⟩)
          exact ⟨w', hw', htrans _ _ _ hw'c hcz⟩

/-- The computed fold denotes the relational fold `⦇[B,S]⦈`. -/
theorem rel_fold {B : RelRep L V} {S : RelRep (E × V) V} {T : RelRep (ConsList L E) V}
    (h : fold B S = some T) : T.rel = ⦇(junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel : Alg (F L E) ⟨V⟩)⦈ := by
  have hf := foldWith_spec (P := Eq) (fun _ => ⟨fun _ h => h, fun z hz => ⟨z, hz, rfl⟩⟩)
    (fun _ _ _ => Eq.trans) (fun _ _ _ _ e h => ⟨_, by subst e; exact h, rfl⟩) h
  rw [← cataR_eq_relCata]
  exact hom_ext fun x v => ⟨(hf x).1 v, fun hv => let ⟨_, hw, e⟩ := (hf x).2 v hv; e ▸ hw⟩

/-- **The thinning fold**: for a preorder `Q` that the algebra `[B,S]` preserves, every computed fibre
    is a `thin(Q)` choice of the fold's, `Λ T ⊑ Λ⦇[B,S]⦈ thin(Q)`. -/
theorem rel_foldThin {Q : RelRep V V} {B : RelRep L V} {S : RelRep (E × V) V} {T : RelRep (ConsList L E) V}
    (hr : 𝟙 _ ⊑ Q.rel) (ht : Q.rel ≫ Q.rel ⊑ Q.rel)
    (hmono : Pres (F := F L E) (junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel) Q.rel)
    (h : foldThin Q B S = some T) :
    Λ T.rel ⊑ Λ ⦇(junc (sumCop (dL L) ⟨E × V⟩) B.rel S.rel : Alg (F L E) ⟨V⟩)⦈ ≫ thinRel Q.rel := by
  have hj := junc_apply B.rel S.rel
  have hf := foldWith_spec (P := Q.rel) (thinList_rel_spec hr ht) (fun u v w h1 h2 => le_iff.mp ht u w ⟨v, h1, h2⟩)
    (fun e w r z hwr hz =>
      let ⟨c, hc, hcz⟩ := le_iff.mp hmono (Sum.inr (e, w)) z ⟨Sum.inr (e, r), ⟨rfl, hwr⟩, (hj.2 _ z).2 hz⟩
      ⟨c, (hj.2 _ c).1 hc, hcz⟩) h
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
