/-
  §11.3 of the RelRep design, the structural verbs: each kernel's `*_toList` read through `ix`, then
  the List spec as the expression (`ix_*`), over `Spec.lean`'s reading `x.rel = ix(x.toList)`.
-/
import LeetQ.Rel.Spec

namespace LeetQ.Rel.Verb

open QLean QLean.Dep
open Freyd Freyd.Alg Freyd.Alg.RelSet
open Freyd.Alg.RelSet.ListRel (dList list listP)

/-! ## -- vocabulary -/

section Vocabulary

variable {α : Type}

/-- `Λ(R)` in Rel(Set): `x` goes to the set of its `R`-images. -/
theorem Λ_iff {A B : RelSet.{0}} (R : A ⟶ B) (x : A.carrier) (S) : Λ R x S ↔ S = fun y => R x y := by
  rw [Λ_eq_classifier]; exact Iff.rfl

/-- `c a ≤ c b` for `a ≤ b ≤ g`, from the steps `c r ≤ c (r+1)`. -/
theorem mono_chain (c : Nat → Nat) {g : Nat} (mono : ∀ r, r < g → c r ≤ c (r+1)) :
    ∀ {a b : Nat}, a ≤ b → b ≤ g → c a ≤ c b := by
  intro a b hab hb
  induction b with
  | zero => rw [Nat.le_zero.1 hab]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with h | h
    · exact Nat.le_trans (ih (by omega) (by omega)) (mono b (by omega))
    · rw [h]; exact Nat.le_refl _

/-- Of the cuts `c 1 … c g`, ascending from `c 0 = 0`, at least `r` lie at or below `i` exactly when `c r ≤ i`. -/
theorem le_countP_cuts (c : Nat → Nat) (h0 : c 0 = 0) (i : Nat) : ∀ g, (∀ r, r < g → c r ≤ c (r+1)) →
    ∀ r, r ≤ g → (r ≤ (List.range g).countP (fun r' => decide (c (r'+1) ≤ i)) ↔ c r ≤ i)
  | 0, _, r, hr => by rw [Nat.le_zero.1 hr, h0]; simp
  | g+1, mono, r, hr => by
    have ih := le_countP_cuts c h0 i g (fun r' h => mono r' (by omega))
    have hle : (List.range g).countP (fun r' => decide (c (r'+1) ≤ i)) ≤ g :=
      Nat.le_trans (List.countP_le_length ..) (by simp)
    have e : (List.range (g+1)).countP (fun r' => decide (c (r'+1) ≤ i)) =
        (List.range g).countP (fun r' => decide (c (r'+1) ≤ i)) + if c (g+1) ≤ i then 1 else 0 := by
      simp [List.range_succ, List.countP_append]
    rw [e]
    by_cases hg : c (g+1) ≤ i
    · have := (ih g (Nat.le_refl g)).2 (Nat.le_trans (mono g (by omega)) hg)
      rw [if_pos hg]
      exact ⟨fun _ => Nat.le_trans (mono_chain c mono hr (Nat.le_refl _)) hg, fun _ => by omega⟩
    · rw [if_neg hg, Nat.add_zero]
      rcases Nat.lt_or_eq_of_le hr with h | h
      · exact ih r (by omega)
      · subst h; exact ⟨fun h => by omega, fun h => absurd h hg⟩

/-- Exactly `r < g` of the cuts lie at or below `i` when `i` is in run `r`, `[c r, c (r+1))`. -/
theorem countP_cuts_eq (c : Nat → Nat) (h0 : c 0 = 0) {g : Nat} (mono : ∀ r, r < g → c r ≤ c (r+1))
    {i r : Nat} (hr : r < g) :
    (List.range g).countP (fun r' => decide (c (r'+1) ≤ i)) = r ↔ c r ≤ i ∧ i < c (r+1) := by
  have a := le_countP_cuts c h0 i g mono r (by omega)
  have b := le_countP_cuts c h0 i g mono (r+1) hr
  constructor
  · intro e
    exact ⟨a.1 (by omega), Nat.lt_of_not_le fun h => by have := b.2 h; omega⟩
  · rintro ⟨h1, h2⟩
    have := a.2 h1
    have : ¬ r + 1 ≤ (List.range g).countP (fun r' => decide (c (r'+1) ≤ i)) := fun h => by
      have := b.1 h; omega
    omega

/-- `enum` of the interval `[a, a+k)` is `range'(a, k)`. -/
theorem enum_range' (a k : Nat) (L : CL.ConsList Unit Nat) :
    enum (fun i => a ≤ i ∧ i < a + k) L ↔ L = CL.ofList (List.range' a k) := by
  rw [enum_iff]
  have pw : (List.range' a k).Pairwise (· < ·) := List.pairwise_lt_range' ..
  have mem : ∀ i, i ∈ List.range' a k ↔ a ≤ i ∧ i < a + k := fun i => by simp [List.mem_range'_1]
  constructor
  · rintro ⟨hS, ho⟩
    rw [← ofList_toList L, orderedP_ofList] at ho
    rw [← ofList_toList L]
    refine congrArg CL.ofList (eq_of_pairwise_lt ho pw fun i => ?_)
    rw [mem, ← inlistP_ofList, ofList_toList, ← hS]
  · rintro rfl
    exact ⟨funext fun i => propext ((mem i).symm.trans (inlistP_ofList i _).symm), (orderedP_ofList _ _).2 pw⟩

/-- `list(ix xs)` takes the positions `[a, a+k)`, all below `|xs|`, to the values there. -/
theorem list_ix_range' (xs : List α) : ∀ (k a : Nat) (w : CL.ConsList Unit α), a + k ≤ xs.length →
    (list (ix xs) (CL.ofList (List.range' a k)) w ↔ w = CL.ofList ((xs.drop a).take k))
  | 0, a, w, _ => by
    cases w with
    | wrap u => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons b z => exact ⟨False.elim, fun h => nomatch h⟩
  | k+1, a, w, h => by
    rw [List.range'_succ, List.drop_eq_getElem_cons (by omega : a < xs.length), List.take_succ_cons,
      CL.ofList_cons, CL.ofList_cons]
    cases w with
    | wrap u => exact ⟨False.elim, fun h => nomatch h⟩
    | cons b z =>
      show (xs[a]? = some b ∧ list (ix xs) (CL.ofList (List.range' (a+1) k)) z) ↔ _
      rw [List.getElem?_eq_getElem (by omega), Option.some.injEq, list_ix_range' xs k (a+1) z (by omega)]
      exact ⟨fun ⟨e, h⟩ => by rw [← e, h], fun e => by cases e; exact ⟨rfl, rfl⟩⟩

/-- `ix(xs ++ ys) = split ≫ [ix xs, ix ys]`: the junction of the two lists over the split of positions. -/
theorem ix_append (xs ys : List α) :
    ix (xs ++ ys) = split xs.length ys.length ≫ junc (sumCop Idx Idx) (ix xs) (ix ys) :=
  hom_ext fun (j : Nat) a => by
    show (xs ++ ys)[j]? = some a ↔ ∃ s, (∃ z, (j = z ∧ j < xs.length + ys.length) ∧
        s = if z < xs.length then Sum.inl z else Sum.inr (z - xs.length)) ∧
      ((∃ i, s = Sum.inl i ∧ xs[i]? = some a) ∨ (∃ i, s = Sum.inr i ∧ ys[i]? = some a))
    constructor
    · intro e
      have hl := (List.getElem?_eq_some_iff.1 e).1
      rw [List.length_append] at hl
      by_cases hj : j < xs.length
      · rw [List.getElem?_append_left hj] at e
        exact ⟨_, ⟨j, ⟨rfl, hl⟩, rfl⟩, by rw [if_pos hj]; exact .inl ⟨j, rfl, e⟩⟩
      · rw [List.getElem?_append_right (by omega)] at e
        exact ⟨_, ⟨j, ⟨rfl, hl⟩, rfl⟩, by rw [if_neg hj]; exact .inr ⟨_, rfl, e⟩⟩
    · rintro ⟨s, ⟨_, ⟨rfl, _⟩, rfl⟩, h⟩
      by_cases hj : j < xs.length
      · rw [if_pos hj] at h
        rcases h with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
        · cases hi; rw [List.getElem?_append_left hj]; exact e
        · cases hi
      · rw [if_neg hj] at h
        rcases h with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
        · cases hi
        · cases hi; rw [List.getElem?_append_right (by omega)]; exact e

/-- `cnt(c)`: position `i` to the number of the cuts `c 1 … c g` at or below it, the run holding it. -/
def cnt (g : Nat) (c : Nat → Nat) : Idx ⟶ Idx :=
  graph fun i => (List.range g).countP fun r => decide (c (r+1) ≤ i)

/-- **The runs of `xs` cut at `c` read as `Λ(cnt°) ≫ enum ≫ list(xs)`**: run `r < g` is the positions the
    cut count sends to `r`, in position order, then their values. -/
theorem ix_runs (xs : List α) (g : Nat) (c : Nat → Nat) (h0 : c 0 = 0) (hg : c g = xs.length)
    (mono : ∀ r, r < g → c r ≤ c (r+1)) :
    ix (((List.range g).map fun r => (xs.drop (c r)).take (c (r+1) - c r)).map CL.ofList) =
      corefl (· < g) ≫ Λ ((corefl (· < xs.length) ≫ cnt g c)°) ≫ enum ≫ list (ix xs) :=
  hom_ext fun (r : Nat) w => by
    change _ ↔ ∃ r', (r = r' ∧ r < g) ∧ ∃ S, Λ ((corefl (· < xs.length) ≫ cnt g c)°) r' S ∧
      ∃ L, enum S L ∧ list (ix xs) L w
    rw [List.map_map]
    change (List.map _ (List.range g))[r]? = some w ↔ _
    have hset : r < g → (fun i => ((corefl (· < xs.length) ≫ cnt g c)°) r i) =
        fun i => c r ≤ i ∧ i < c r + (c (r+1) - c r) := fun hr => funext fun (i : Nat) => propext <| by
      change (∃ z, (i = z ∧ i < xs.length) ∧ r = _) ↔ _
      have := countP_cuts_eq c h0 mono (i := i) hr
      have hm := mono r hr
      have hcg := mono_chain c mono (show r + 1 ≤ g by omega) (Nat.le_refl g)
      constructor
      · rintro ⟨_, ⟨rfl, _⟩, e⟩; have := this.1 e.symm; omega
      · rintro ⟨h1, h2⟩
        have hi : i < xs.length := by omega
        exact ⟨i, ⟨rfl, hi⟩, (this.2 ⟨h1, by omega⟩).symm⟩
    by_cases hr : r < g
    · have hm := mono r hr
      have hcg := mono_chain c mono (show r + 1 ≤ g by omega) (Nat.le_refl g)
      rw [List.getElem?_map, List.getElem?_range hr, Option.map_some, Option.some.injEq]
      constructor
      · rintro rfl
        refine ⟨r, ⟨rfl, hr⟩, _, (Λ_iff _ r _).2 rfl, _, ?_,
          (list_ix_range' xs (c (r+1) - c r) (c r) _ (by omega)).2 rfl⟩
        rw [hset hr]; exact (enum_range' _ _ _).2 rfl
      · rintro ⟨_, ⟨rfl, _⟩, S, hS, L, he, hl⟩
        rw [(Λ_iff _ r S).1 hS, hset hr, enum_range'] at he
        subst he
        exact ((list_ix_range' xs (c (r+1) - c r) (c r) w (by omega)).1 hl).symm
    · rw [List.getElem?_map, List.getElem?_eq_none (by simp; omega)]
      exact ⟨fun h => by simp at h, fun ⟨_, ⟨_, h⟩, _⟩ => absurd h hr⟩

theorem cappend_ofList (xs ys : List α) :
    ListRel.cappend (CL.ofList xs) (CL.ofList ys) = CL.ofList (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.cons_append, CL.ofList_cons, CL.ofList_cons, ← ih]; rfl

/-- `concat` of a nested list read as cons-lists is its `flatten`. -/
theorem cconcat_ofList (L : List (List α)) :
    ListRel.cconcat (CL.ofList (L.map CL.ofList)) = CL.ofList L.flatten := by
  induction L with
  | nil => rfl
  | cons xs L ih => rw [List.map_cons, List.flatten_cons, CL.ofList_cons, ← cappend_ofList, ← ih]; rfl

/-- The runs of `xs` cut at `c`, ascending from `c 0 = 0`, flatten to the first `c g` of `xs`. -/
theorem flatten_runs (xs : List α) (c : Nat → Nat) (h0 : c 0 = 0) : ∀ g, (∀ r, r < g → c r ≤ c (r+1)) →
    ((List.range g).map fun r => (xs.drop (c r)).take (c (r+1) - c r)).flatten = xs.take (c g)
  | 0, _ => by simp [h0]
  | g+1, mono => by
    rw [List.range_succ, List.map_append, List.flatten_append, flatten_runs xs c h0 g (fun r h => mono r (by omega))]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [← List.take_add, Nat.add_sub_cancel' (mono g (by omega))]

end Vocabulary

/-! ## A flat form read as its nested list -/

/-- The cut point `o[r]` of a flat form, a natural. -/
def _root_.LeetQ.Rel.Parted.cut {v : QAtomicType} (P : Parted v) (r : Nat) : Nat := (P.o.toList[r]!).toNatClampNeg

/-- The runs of a flat form, run `r < g` the values `val[o[r] … o[r+1])` (`Struct.parted_toList`). -/
def _root_.LeetQ.Rel.Parted.segs {v : QAtomicType} (P : Parted v) : List (List (El v)) :=
  (List.range P.g).map fun r => (P.val.toList.drop (P.cut r)).take (P.cut (r+1) - P.cut r)

/-- `P.rel = ix(segs)`: a flat form as the nested list `x : til g → list(t)` it boxes to. -/
def _root_.LeetQ.Rel.Parted.rel {v : QAtomicType} (P : Parted v) : Idx ⟶ dList (El v) := ix (P.segs.map CL.ofList)

/-- `grp(o)` is the cut count of the offsets read as naturals. -/
theorem grp_cnt {v : QAtomicType} (P : Parted v) : grp P.o = cnt P.g P.cut := by
  have hc : ∀ r, r ≤ P.g → ((P.o.toList[r]!).toNatClampNeg : Int) = (P.o.toList[r]!).toInt := fun r hr => by
    rw [← Int64.toNat_toInt]; exact Int.toNat_of_nonneg (cuts_get P.co (Nat.le_refl r) hr).1
  have e : ∀ m (hm : m ≤ P.g), P.o.toList[m]! = P.o.get ⟨m, by omega⟩ := fun m hm => by
    rw [getElem!_pos _ m (by rw [Arr.length_toList]; omega), Arr.getElem_toList]
  show graph _ = graph _
  congr 1; funext i
  unfold Parted.group
  rw [show List.range P.g = (List.finRange P.g).map Fin.val from List.ext_getElem (by simp) (fun j _ _ => by simp),
    List.countP_map]
  congr 1; funext r
  have := r.isLt
  have := hc (r.val+1) (by omega)
  have e' : P.o.get r.succ = P.o.toList[r.val+1]! := (e (r.val+1) (by omega)).symm
  simp only [Function.comp, e', Parted.cut]
  exact decide_eq_decide.2 (by omega)

/-- **A flat form reads as `o cut val`**: `P.rel = Λ(grp(o)°) ≫ enum ≫ list(val)` on the groups `til g` and
    the positions `til n`. -/
theorem parted_rel {v : QAtomicType} (P : Parted v) :
    P.rel = corefl (· < P.g) ≫ Λ ((corefl (· < P.n) ≫ grp P.o)°) ≫ enum ≫ list P.val.rel := by
  obtain ⟨h0, cg, mono⟩ := Struct.cuts_nat P.co
  have hl : P.val.toList.length = P.n := Arr.length_toList _
  calc P.rel = corefl (· < P.g) ≫ Λ ((corefl (· < P.val.toList.length) ≫ cnt P.g P.cut)°) ≫ enum ≫
          list P.val.rel := ix_runs _ _ _ h0 (by rw [hl]; exact cg) mono
    _ = corefl (· < P.g) ≫ Λ ((corefl (· < P.n) ≫ grp P.o)°) ≫ enum ≫ list P.val.rel := by rw [hl, grp_cnt]

/-! ## raze -/

/-- `raze = concat` (`ListRel.concatR`, the graph of `cconcat`): the answer is the nested list's runs flattened. -/
theorem raze_rel {v : QAtomicType} {g : Nat} {x : Arr .general g} {P : Parted v} (h : Parted.ofBoxes v x = .ok P) :
    Struct.raze v x = .ok ⟨P.n, P.val⟩ ∧
      ListRel.concatR (CL.ofList (P.segs.map CL.ofList)) (CL.ofList P.val.toList) := by
  refine ⟨by unfold Struct.raze; rw [h]; rfl, ?_⟩
  obtain ⟨h0, cg, mono⟩ := Struct.cuts_nat P.co
  show CL.ofList P.val.toList = ListRel.cconcat _
  calc CL.ofList P.val.toList = CL.ofList (P.val.toList.take (P.cut P.g)) := by
        rw [show P.cut P.g = P.val.toList.length by rw [Arr.length_toList]; exact cg, List.take_length]
    _ = CL.ofList P.segs.flatten := by rw [Parted.segs, flatten_runs _ P.cut h0 _ mono]
    _ = ListRel.cconcat (CL.ofList (P.segs.map CL.ofList)) := (cconcat_ofList _).symm

/-! ## `x,y` -/

/-- `x,y = split ≫ [x, y]`, on long columns, `x` of whole words, `y` dense (`concat_toList`). -/
theorem concat_rel {nx ny : Nat} {x : Arr .long nx} {y : Arr .long ny} {r : Arr .long (nx + ny)} {c : ByteArray}
    (hx : Struct.Words x.c) (hc : y.c.enc = .bytes c) (h : Struct.concat x y = .ok r) :
    r.rel = split nx ny ≫ junc (sumCop Idx Idx) x.rel y.rel :=
  calc r.rel = ix (x.toList ++ y.toList) := congrArg ix (Struct.concat_toList hx hc h)
    _ = split x.toList.length y.toList.length ≫ junc (sumCop Idx Idx) x.rel y.rel := ix_append ..
    _ = split nx ny ≫ junc (sumCop Idx Idx) x.rel y.rel := by rw [Arr.length_toList, Arr.length_toList]

#print axioms concat_rel
#print axioms ix_runs
#print axioms parted_rel
#print axioms raze_rel

end LeetQ.Rel.Verb
