/-
  §11.3 of the RelRep design, the structural verbs: each kernel's `*_toList` read through `ix`, then
  the List spec as the expression (`ix_*`), over `Spec.lean`'s reading `x.rel = ix(x.toList)`.
-/
import LeetQ.Rel.Spec
import LeetQ.Rel.SpecFind
import QLean.Verify.Dyad
import QLean.Verify.Structural

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

/-! ## `o cut x` -/

/-- `o cut x = Λ(grp(o)°) ≫ enum ≫ list(x)`, for a first offset `o₀ = 0` (q keeps every row): `cutP` answers
    `x` itself cut at its offsets `r.o`, which are `o` closed by `nx`, so `parted_rel` is the law. Restricted to
    a dense long `o`; at `o₀ > 0` the rows below `o₀` are dropped first (`cut_toList` covers it, as a List). -/
theorem cut_rel {no nx : Nat} {o : Arr .long no} {x : Arr .long nx} {r : Parted .long} {ob : ByteArray}
    (ho : o.c.enc = .bytes ob) (h0 : (if no = 0 then (0 : Int64) else (Column.bitsAt ob 0 8).toInt64) = 0)
    (h : Struct.cutP o x = .ok r) :
    r.rel = corefl (· < r.g) ≫ Λ ((corefl (· < nx) ≫ grp r.o)°) ≫ enum ≫ list x.rel := by
  unfold Struct.cutP at h
  rw [o.c_eq ho, show Find.dense "o cut x" .long ⟨.long, no, .bytes ob, o.attrCell⟩ = pure ob from rfl,
    pure_bind] at h
  generalize ho₀ : (if no = 0 then (0 : Int64) else (Column.bitsAt ob 0 8).toInt64) = o₀ at h
  rw [h0] at ho₀; subst ho₀
  dsimp only at h
  split at h
  · simp [bind, Except.bind] at h
  simp only [pure_bind] at h
  split at h
  · rw [bind_pure] at h
    obtain ⟨g, oa, co, _, rfl⟩ := Struct.parted_ok h
    exact parted_rel _
  · exact absurd trivial ‹¬True›

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

/-! ## Nested `x@y`

  `Struct.indexParted` boxes its answer; no theorem yet reads `Parted.ofBoxes` of a `box` back (Core's
  round trip is a `#guard`), so the kernel law `indexParted_toList` is the hypothesis `hk`, in List form. -/

/-- `indexSpec` commutes with a map of the elements, the default mapped too. -/
theorem indexSpec_map {α β : Type} (f : α → β) (d : α) (xs : List α) (is : List Int64) :
    (Struct.indexSpec d xs is).map f = Struct.indexSpec (f d) (xs.map f) is := by
  simp only [Struct.indexSpec, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  by_cases h : 0 ≤ i
  · simp only [Function.comp, h, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases xs[i.toInt.toNat]? <;> rfl
  · simp only [Function.comp, h, ↓reduceIte]

/-- **Nested `x@y = y ≫ miss(pos ≫ x, [])`**, `x : til g → list(t)` read through `Parted.rel`: each index's run,
    the empty list at a miss. `hk` is the kernel law `R.segs = indexSpec [] P.segs y` (`Struct.indexParted`'s
    answer `R`, its operand `P`). -/
theorem indexParted_rel {v : QAtomicType} {ny : Nat} {P R : Parted v} {y : Arr .long ny}
    (hk : R.segs = Struct.indexSpec [] P.segs y.toList) :
    R.rel = y.rel ≫ miss (pos ≫ P.rel) (CL.ofList []) :=
  calc R.rel = ix (Struct.indexSpec (CL.ofList []) (P.segs.map CL.ofList) y.toList) := by
        rw [Parted.rel, hk, indexSpec_map]
    _ = y.rel ≫ miss (pos ≫ P.rel) (CL.ofList []) := ix_indexSpec ..

/-! ## `x f/:y`

  `Struct.eachRight` boxes its answer too; `hk` is the kernel law `R.segs = y.map (x.map (f · b))`, `f` the
  dyadic verb on elements. -/

theorem cmap_ofList {α β : Type} (f : α → β) (xs : List α) : ListRel.cmap f (CL.ofList xs) = CL.ofList (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [CL.ofList_cons, List.map_cons, CL.ofList_cons, ← ih]; rfl

/-- `ys.map (xs.map (f · b))` reads as `⟨!xs, ys⟩ ≫ cpl ≫ list(f)`. -/
theorem ix_eachRight {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) :
    ix ((ys.map fun b => xs.map (f · b)).map CL.ofList) =
      rpair (cst (CL.ofList xs)) (ix ys) ≫ ListRel.cpl ≫
        list (graph fun p : α × β => f p.1 p.2) :=
  hom_ext fun (j : Nat) w => by
    show _ ↔ ∃ p, rpair (cst (CL.ofList xs)) (ix ys) j p ∧
      ∃ q, ListRel.cpl p q ∧ list (graph fun p : α × β => f p.1 p.2) q w
    simp only [ListRel.list_graph]
    show ((ys.map fun b => xs.map (f · b)).map CL.ofList)[j]? = some w ↔
      ∃ p : CL.ConsList Unit α × β, (p.1 = CL.ofList xs ∧ ys[j]? = some p.2) ∧
        ∃ q, q = ListRel.cplFn p ∧ w = ListRel.cmap (fun p : α × β => f p.1 p.2) q
    rw [List.getElem?_map, List.getElem?_map]
    cases ys[j]? with
    | none => exact ⟨(fun h => nomatch h), (fun ⟨_, ⟨_, h⟩, _⟩ => nomatch h)⟩
    | some b =>
      have e : ListRel.cmap (fun p : α × β => f p.1 p.2) (ListRel.cplFn (CL.ofList xs, b)) =
          CL.ofList (xs.map (f · b)) := by
        simp only [ListRel.cplFn, cmap_ofList, List.map_map]; rfl
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨(CL.ofList xs, b), ⟨rfl, rfl⟩, _, rfl, e.symm⟩
      · rintro ⟨⟨c, b'⟩, ⟨h1, h2⟩, _, rfl, rfl⟩
        cases h1; cases h2; exact e.symm

/-- **`x f/:y = ⟨!x, y⟩ ≫ cpl ≫ list(f)`**: run `j` is `x` paired with `y[j]`, then `f` on each pair. -/
theorem eachRight_rel {t u rt : QAtomicType} {nx ny : Nat} {x : Arr t nx} {y : Arr u ny} {R : Parted rt}
    (f : El t → El u → El rt) (hk : R.segs = y.toList.map fun b => x.toList.map (f · b)) :
    R.rel = rpair (cst (CL.ofList x.toList)) y.rel ≫ ListRel.cpl ≫
      list (graph fun p : El t × El u => f p.1 p.2) :=
  calc R.rel = ix ((y.toList.map fun b => x.toList.map (f · b)).map CL.ofList) := by rw [Parted.rel, hk]
    _ = rpair (cst (CL.ofList x.toList)) y.rel ≫ ListRel.cpl ≫
          list (graph fun p : El t × El u => f p.1 p.2) := ix_eachRight f _ _

/-! ## `ej`

  `hk` is the kernel law `R.toList = ejSpec l r`, `l`, `r` the key tuples per row (`keyCodes`, `Alg.join`). -/

/-- `ejSpec`'s pairs as a relation are `ofNat° ≫ l ≫ r° ≫ ofNat`: the rows whose key tuples meet. -/
theorem rel_ejSpec (l r : List (List Int64)) :
    RelSet.rel (Struct.ejSpec l r) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ ix l ≫ (ix r)° ≫ graph Int64.ofNat :=
  hom_ext fun a b => by
    show (a, b) ∈ Struct.ejSpec l r ↔ ∃ i, a = Int64.ofNat i ∧ ∃ k, l[i]? = some k ∧ ∃ j, r[j]? = some k ∧
      b = Int64.ofNat j
    simp only [Struct.ejSpec, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi, j, ⟨hj, he⟩, rfl, rfl⟩
      have e := beq_iff_eq.1 he
      rw [getElem!_pos r j hj, getElem!_pos l i hi] at e
      exact ⟨i, rfl, l[i], List.getElem?_eq_getElem hi, j, by rw [List.getElem?_eq_getElem hj, e], rfl⟩
    · rintro ⟨i, rfl, k, hl, j, hr, rfl⟩
      obtain ⟨hi, el⟩ := List.getElem?_eq_some_iff.1 hl
      obtain ⟨hj, er⟩ := List.getElem?_eq_some_iff.1 hr
      exact ⟨i, hi, j, ⟨hj, beq_iff_eq.2 (by rw [getElem!_pos r j hj, getElem!_pos l i hi, el, er])⟩, rfl, rfl⟩

/-- **`ej` tabulates `l ≫ r°`** on the rows read as naturals: `R.Holds = ofNat° ≫ l ≫ r° ≫ ofNat`. -/
theorem ej_rel {R : Rel .long .long} {l r : List (List Int64)} (hk : R.toList = Struct.ejSpec l r) :
    (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ ix l ≫ (ix r)° ≫ graph Int64.ofNat :=
  calc (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) = RelSet.rel (Struct.ejSpec l r) :=
        hom_ext fun a b => by rw [← hk]; exact R.holds_iff_mem_toList a b
    _ = (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ ix l ≫ (ix r)° ≫ graph Int64.ofNat :=
        rel_ejSpec l r

/-! ## `+x`

  `Struct.flip` boxes its answer; `hk` is the kernel law `R.segs = (til m).map (P.segs.map (·[j]))`, every run of
  `P` of length `m`. -/

theorem toList_ofList {α : Type} : ∀ xs : List α, CL.toList (CL.ofList xs) = xs
  | [] => rfl
  | a :: xs => by
    rw [CL.ofList_cons, show CL.toList (.cons a (CL.ofList xs)) = a :: CL.toList (CL.ofList xs) from rfl, toList_ofList xs]

/-- `list(R)` of a list whose every element `R` sends to `f` of it alone is the list mapped by `f`. -/
theorem list_ofList {α β : Type} (R : (⟨α⟩ : RelSet.{0}) ⟶ ⟨β⟩) (f : α → β) : ∀ (xs : List α) (w : CL.ConsList Unit β),
    (∀ a ∈ xs, ∀ b, R a b ↔ b = f a) → (list R (CL.ofList xs) w ↔ w = CL.ofList (xs.map f))
  | [], w, _ => by
    cases w with
    | wrap u => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons b z => exact ⟨False.elim, fun h => nomatch h⟩
  | a :: xs, w, h => by
    rw [List.map_cons, CL.ofList_cons, CL.ofList_cons]
    cases w with
    | wrap u => exact ⟨False.elim, fun h => nomatch h⟩
    | cons b z =>
      show (R a b ∧ list R (CL.ofList xs) z) ↔ _
      rw [h a (List.mem_cons_self ..) b, list_ofList R f xs z (fun a' m => h a' (List.mem_cons_of_mem _ m))]
      exact ⟨fun ⟨e1, e2⟩ => by rw [e1, e2], fun e => by cases e; exact ⟨rfl, rfl⟩⟩

/-- `(@) : list(t) × til → t`, element `j` of a list. -/
def nth {α : Type} : (⟨CL.ConsList Unit α × Nat⟩ : RelSet.{0}) ⟶ ⟨α⟩ := fun p a => (CL.toList p.1)[p.2]? = some a

/-- The columns of `g` runs of one length `m`: `⟨!til g, til m⟩ ≫ cpl ≫ list(x̂)`, `x̂ = ⟨outl ≫ x, outr⟩ ≫ (@)`;
    column `j` is `x̂(i, j)` for `i` in `til g`. -/
theorem ix_flip {α : Type} [Inhabited α] (segs : List (List α)) (g m : Nat) (hg : segs.length = g)
    (hm : ∀ s ∈ segs, s.length = m) :
    ix (((List.range m).map fun j => segs.map (·[j]!)).map CL.ofList) =
      rpair (cst (CL.ofList (List.range g))) (corefl (· < m)) ≫ ListRel.cpl ≫
        list (rpair ((graph Prod.fst : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ ix (segs.map CL.ofList))
          (graph Prod.snd : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ nth) :=
  hom_ext fun (j : Nat) w => by
    subst hg
    show _ ↔ ∃ p, (p.1 = CL.ofList (List.range segs.length) ∧ (j = p.2 ∧ j < m)) ∧ ∃ q, q = ListRel.cplFn p ∧ list _ q w
    show ((((List.range m).map fun k => segs.map (·[k]!)).map CL.ofList)[j]? = some w) ↔ _
    rw [List.getElem?_map, List.getElem?_map]
    by_cases hj : j < m
    · rw [List.getElem?_range hj]
      simp only [Option.map_some, Option.some.injEq]
      have e : ListRel.cplFn (CL.ofList (List.range segs.length), j) =
          CL.ofList ((List.range segs.length).map (·, j)) := by
        simp only [ListRel.cplFn, cmap_ofList]
      have hl := list_ofList (rpair ((graph Prod.fst : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ ix (segs.map CL.ofList))
          (graph Prod.snd : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ nth) (fun p => segs[p.1]![p.2]!)
          ((List.range segs.length).map (·, j)) w (fun p hp b => by
            obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
            have hs : i < segs.length := List.mem_range.1 hi
            have hlen := hm segs[i] (List.getElem_mem hs)
            show (∃ q : CL.ConsList Unit α × Nat, ((∃ i', i' = i ∧ (segs.map CL.ofList)[i']? = some q.1) ∧ q.2 = j) ∧
              (CL.toList q.1)[q.2]? = some b) ↔ b = segs[i]![j]!
            rw [getElem!_pos segs i hs, getElem!_pos segs[i] j (by omega)]
            constructor
            · rintro ⟨⟨s, j'⟩, ⟨⟨_, rfl, hs1⟩, rfl⟩, h⟩
              rw [List.getElem?_map, List.getElem?_eq_getElem hs, Option.map_some, Option.some.injEq] at hs1
              subst hs1
              rw [toList_ofList, List.getElem?_eq_getElem (by omega), Option.some.injEq] at h
              exact h.symm
            · rintro rfl
              exact ⟨(CL.ofList segs[i], j), ⟨⟨i, rfl, by rw [List.getElem?_map, List.getElem?_eq_getElem hs]; rfl⟩, rfl⟩,
                by rw [toList_ofList, List.getElem?_eq_getElem (by omega)]⟩)
      have hseg : CL.ofList (((List.range segs.length).map (·, j)).map fun p => segs[p.1]![p.2]!) =
          CL.ofList (segs.map (·[j]!)) := by
        congr 1; apply List.ext_getElem (by simp); intro i h1 h2
        simp only [List.length_map, List.length_range] at h1
        simp only [List.getElem_map, List.getElem_range]
        rw [getElem!_pos segs i h1]
      rw [hseg] at hl
      constructor
      · rintro rfl; exact ⟨_, ⟨rfl, rfl, hj⟩, _, rfl, by rw [e]; exact hl.2 rfl⟩
      · rintro ⟨⟨_, _⟩, ⟨rfl, rfl, _⟩, _, rfl, h⟩; rw [e] at h; exact (hl.1 h).symm
    · have hn : (List.range m)[j]? = none := List.getElem?_eq_none (by simp; omega)
      simp only [hn, Option.map_none]
      exact ⟨(fun h => nomatch h), (fun ⟨_, ⟨_, _, h⟩, _⟩ => absurd h hj)⟩

/-- **`+x = ⟨!til g, til m⟩ ≫ cpl ≫ list(⟨outl ≫ x, outr⟩ ≫ (@))`**: column `j < m` lists `x(i)[j]` for `i < g`. -/
theorem flip_rel {v : QAtomicType} [Inhabited (El v)] {P R : Parted v} {m : Nat} (hm : ∀ s ∈ P.segs, s.length = m)
    (hk : R.segs = (List.range m).map fun j => P.segs.map (·[j]!)) :
    R.rel = rpair (cst (CL.ofList (List.range P.g))) (corefl (· < m)) ≫ ListRel.cpl ≫
      list (rpair ((graph Prod.fst : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ P.rel)
        (graph Prod.snd : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ nth) :=
  calc R.rel = ix (((List.range m).map fun j => P.segs.map (·[j]!)).map CL.ofList) := by rw [Parted.rel, hk]
    _ = rpair (cst (CL.ofList (List.range P.g))) (corefl (· < m)) ≫ ListRel.cpl ≫
          list (rpair ((graph Prod.fst : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ P.rel)
            (graph Prod.snd : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ nth) :=
        ix_flip P.segs P.g m (by simp [Parted.segs]) hm

/-! ## Long index arithmetic, read as naturals

  The boxed verbs build their positions with `tilLongs`, `Alg.cross`, `Alg.mulc` and `Alg.add`; below `2^63` no
  operand is `0N` and nothing wraps, so each is its arithmetic on naturals. -/

/-- The words of a dense long payload, read as naturals. -/
def nats (b : ByteArray) : List Nat := (Verify.elemsW 8 b).map UInt64.toNat

theorem nats_length (b : ByteArray) : (nats b).length = b.size / 8 := by simp [nats, Verify.elemsW]

theorem nats_til (N : Nat) (hN : N < USize.size) : nats (Kernel.tilLongs N.toUSize) = List.range N := by
  rw [nats, Verify.tilLongs_spec, USize.toNat_ofNat_of_lt' hN]

/-- A word holding a natural below `2^63` reads as that natural. -/
theorem toInt_word {u : UInt64} {a : Nat} (h : u.toNat = a) (ha : a < 2 ^ 63) : u.toInt64.toInt = a := by
  obtain rfl : u = UInt64.ofNat a := UInt64.toNat_inj.1 (by rw [h, UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le ha (by decide))])
  exact Find.toInt_ofNat_lt ha

/-- A long whose value is a natural `k < 2^63` is the word `k`. -/
theorem toNat_of_toInt {r : Int64} {k : Nat} (hk : k < 2 ^ 63) (h : r.toInt = k) : r.toUInt64.toNat = k := by
  obtain rfl : r = (UInt64.ofNat k).toInt64 := Int64.toInt_inj.1 (by rw [h, Find.toInt_ofNat_lt hk])
  show (UInt64.ofNat k).toNat = k
  exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hk (by decide))

/-- A long read off a word below `2^63` is not `0N`. -/
theorem ne_min_word {u : UInt64} (ha : u.toNat < 2 ^ 63) : (u.toInt64 == Int64.minValue) = false := by
  have e := toInt_word rfl ha
  refine beq_eq_false_iff_ne.2 fun h => ?_
  rw [h] at e; simp at e

/-- `Ew.val` of a long payload against one long atom `c`, element by element on the naturals. -/
theorem nats_val_va (op : UInt8) (b : ByteArray) (c : UInt64) (hn : b.size / 8 < USize.size) (F : Nat → Nat)
    (hF : ∀ a ∈ nats b, (Kernel.Ew.intStep op Int64.minValue (UInt64.ofNat a).toInt64 c.toInt64).toUInt64.toNat = F a) :
    nats (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.va Int64.minValue b (Find.one c) (b.size / 8).toUSize) = (nats b).map F := by
  rw [nats, show Find.one c = Kernel.atomBytes Kernel.Ew.i64 c from rfl, Verify.val_i64_va _ _ _ _ _ hn]
  apply List.ext_getElem (by simp [nats, Verify.elemsW])
  intro i h1 h2
  simp only [nats, Verify.elemsW, List.getElem_map, List.getElem_range, List.length_map, List.length_range] at h2 ⊢
  have := hF _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 h2, rfl⟩, rfl⟩)
  rwa [UInt64.ofNat_toNat] at this

/-- `Alg.mulc a x`: each natural times `x`, all products below `2^63`. -/
theorem nats_mulc (a : ByteArray) (x : Nat) (hn : a.size / 8 < USize.size) (hx : x < 2 ^ 63)
    (hl : ∀ k ∈ nats a, k < 2 ^ 63 ∧ k * x < 2 ^ 63) : nats (Alg.mulc a x) = (nats a).map (· * x) := by
  unfold Alg.mulc Alg.len
  refine nats_val_va _ a _ hn _ fun k hk => ?_
  obtain ⟨hk, hkx⟩ := hl k hk
  have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hk (by decide))
  have hx' : x.toUInt64.toNat = x := UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hx (by decide))
  show (if (UInt64.ofNat k).toInt64 == Int64.minValue || x.toUInt64.toInt64 == Int64.minValue then Int64.minValue
    else (UInt64.ofNat k).toInt64 * x.toUInt64.toInt64).toUInt64.toNat = k * x
  rw [ne_min_word (by omega), ne_min_word (by omega), Bool.false_or, if_neg Bool.false_ne_true]
  show (UInt64.ofNat k * x.toUInt64).toNat = k * x
  rw [UInt64.toNat_mul, hk', hx', Nat.mod_eq_of_lt (by omega)]

/-- Word `i` of a dense long payload, as a natural. -/
theorem nats_get (b : ByteArray) {i : Nat} (h : i < b.size / 8) : (nats b)[i]! = (Column.bitsAt b (i * 8) 8).toNat := by
  rw [getElem!_pos _ i (by rw [nats_length]; exact h)]
  simp only [nats, Verify.elemsW, List.getElem_map, List.getElem_range]

/-- `Alg.cross n m`: `p / m` and `p % m` over `til (n·m)`. -/
theorem nats_cross (n m : Nat) (hU : n * m < USize.size) (hb : n * m < 2 ^ 63) (hm : m < 2 ^ 63) :
    nats (Alg.cross n m).1 = (List.range (n * m)).map (· / m) ∧
      nats (Alg.cross n m).2 = (List.range (n * m)).map (· % m) := by
  unfold Alg.cross Alg.nul
  have ht := nats_til _ hU
  have hs : (Kernel.tilLongs (n * m).toUSize).size / 8 = n * m := by rw [← nats_length, ht, List.length_range]
  generalize Kernel.tilLongs (n * m).toUSize = b at ht hs ⊢
  have hm' : m.toUInt64.toNat = m := UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hm (by decide))
  have hmi : m.toUInt64.toInt64.toInt = m := toInt_word hm' hm
  have hb' : b.size / 8 < 2 ^ 63 := by rw [hs]; exact hb
  have hx : ∀ a ∈ nats b, (UInt64.ofNat a).toInt64.toInt = a ∧ (UInt64.ofNat a).toNat < 2 ^ 63 ∧ 0 < m ∧ a < 2 ^ 63 :=
    fun a ha => by
      rw [ht, List.mem_range] at ha
      have hpos : 0 < m := Nat.pos_of_ne_zero fun h => by subst h; simp at ha
      have ha' : a < 2 ^ 63 := by rw [← hs] at ha; omega
      have e : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le ha' (by decide))
      exact ⟨toInt_word e ha', by omega, hpos, ha'⟩
  have hz : 0 < m → (m.toUInt64.toInt64 == 0) = false := fun hp =>
    beq_eq_false_iff_ne.2 fun h => by rw [h] at hmi; simp at hmi; omega
  have hU' : b.size / 8 < USize.size := by rw [hs]; exact hU
  constructor
  · have := nats_val_va Kernel.Ew.idiv b m.toUInt64 hU' (· / m) fun a ha => by
      obtain ⟨ea, la, hp, la'⟩ := hx a ha
      show (if (UInt64.ofNat a).toInt64 == Int64.minValue || m.toUInt64.toInt64 == Int64.minValue ||
          m.toUInt64.toInt64 == 0 then Int64.minValue
        else Int64.ofInt (Int.fdiv (UInt64.ofNat a).toInt64.toInt m.toUInt64.toInt64.toInt)).toUInt64.toNat = a / m
      rw [ne_min_word la, ne_min_word (by omega), hz hp, if_neg (by decide), ea, hmi, ← Int.ofNat_fdiv,
        Int64.ofInt_eq_ofNat]
      have hq : a / m < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.div_le_self a m) la'
      exact toNat_of_toInt hq (Int64.toInt_ofNat_of_lt hq)
    rw [hs] at this; rw [← ht]; exact this
  · have := nats_val_va Kernel.Ew.imod b m.toUInt64 hU' (· % m) fun a ha => by
      obtain ⟨ea, la, hp, la'⟩ := hx a ha
      show (if (UInt64.ofNat a).toInt64 == Int64.minValue || m.toUInt64.toInt64 == Int64.minValue ||
          m.toUInt64.toInt64 == 0 then Int64.minValue
        else Int64.ofInt (Int.fmod (UInt64.ofNat a).toInt64.toInt m.toUInt64.toInt64.toInt)).toUInt64.toNat = a % m
      rw [ne_min_word la, ne_min_word (by omega), hz hp, if_neg (by decide), ea, hmi, ← Int.ofNat_fmod,
        Int64.ofInt_eq_ofNat]
      have hq : a % m < 2 ^ 63 := Nat.lt_of_lt_of_le (Nat.mod_lt a hp) (Nat.le_of_lt hm)
      exact toNat_of_toInt hq (Int64.toInt_ofNat_of_lt hq)
    rw [hs] at this; rw [← ht]; exact this

/-- `Alg.add a b` on two payloads of one count: the sums word by word, all below `2^63`. -/
theorem nats_add (a b : ByteArray) (hn : a.size / 8 < USize.size) (hab : b.size / 8 = a.size / 8)
    (hl : ∀ i, i < a.size / 8 → (nats a)[i]! + (nats b)[i]! < 2 ^ 63) :
    nats (Alg.add a b) = (List.range (a.size / 8)).map fun i => (nats a)[i]! + (nats b)[i]! := by
  rw [nats, Alg.add, Alg.len, Alg.nul, Verify.val_i64_vv _ _ _ _ _ hn]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_map, List.getElem_range,
    nats_get a h2, nats_get b (by omega)]
  have hs := hl i h2
  rw [nats_get a h2, nats_get b (by omega)] at hs
  generalize Column.bitsAt a (i * 8) 8 = u at hs ⊢
  generalize Column.bitsAt b (i * 8) 8 = w at hs ⊢
  show (if u.toInt64 == Int64.minValue || w.toInt64 == Int64.minValue then Int64.minValue
    else u.toInt64 + w.toInt64).toUInt64.toNat = u.toNat + w.toNat
  rw [ne_min_word (by omega), ne_min_word (by omega), Bool.false_or, if_neg Bool.false_ne_true]
  show (u + w).toNat = _
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-- `xs[a … a+k)` as `k` reads of `xs`. -/
theorem take_drop_eq {α : Type} [Inhabited α] (xs : List α) (a k : Nat) (h : a + k ≤ xs.length) :
    (xs.drop a).take k = (List.range k).map fun i => xs[a + i]! := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range, getElem!_pos xs (a + i) (by omega)]

theorem getElem!_range_map {α : Type} [Inhabited α] (f : Nat → α) {N p : Nat} (h : p < N) :
    ((List.range N).map f)[p]! = f p := by
  rw [getElem!_pos _ p (by simp; omega), List.getElem_map, List.getElem_range]

/-- Runs cut at `r·k` are `k` reads each: run `r` lists `val[r·k + i]` for `i < k`. -/
theorem segs_uniform {v : QAtomicType} [Inhabited (El v)] (P : Parted v) (k : Nat)
    (hc : ∀ r, r ≤ P.g → P.cut r = r * k) :
    P.segs = (List.range P.g).map fun r => (List.range k).map fun i => P.val.toList[r * k + i]! := by
  obtain ⟨-, cg, -⟩ := Struct.cuts_nat P.co
  have hg : P.g * k = P.n := by rw [← hc P.g (Nat.le_refl _)]; exact cg
  refine List.map_congr_left fun r hr => ?_
  have hr := List.mem_range.1 hr
  have e1 : (r + 1) * k = r * k + k := Nat.succ_mul r k
  have e2 : (r + 1) * k ≤ P.g * k := Nat.mul_le_mul_right k hr
  rw [hc r (by omega), hc (r+1) hr, e1, Nat.add_sub_cancel_left]
  exact take_drop_eq _ _ _ (by rw [Arr.length_toList]; omega)

/-- Runs all of length `k` are cut at `r·k`. -/
theorem cut_uniform {v : QAtomicType} (P : Parted v) (k : Nat) (hm : ∀ s ∈ P.segs, s.length = k) :
    ∀ r, r ≤ P.g → P.cut r = r * k
  | 0, _ => by rw [Nat.zero_mul]; exact (Struct.cuts_nat P.co).1
  | r+1, hr => by
    obtain ⟨-, cg, mono⟩ := Struct.cuts_nat P.co
    have ih := cut_uniform P k hm r (by omega)
    have hs := hm _ (List.getElem_mem (show r < P.segs.length by simp [Parted.segs]; omega))
    simp only [Parted.segs, List.getElem_map, List.getElem_range, List.length_take, List.length_drop,
      Arr.length_toList] at hs
    have hm' : P.cut r ≤ P.cut (r+1) := mono r (by omega)
    have hcg : P.cut (r+1) ≤ P.cut P.g := mono_chain P.cut mono (show r + 1 ≤ P.g by omega) (Nat.le_refl _)
    have cg' : P.cut P.g = P.n := cg
    rw [Nat.succ_mul]
    omega

/-- The cuts of a flat form whose offsets are the dense payload `B`, read as naturals below `2^63`. -/
theorem cut_of_nats {v : QAtomicType} (R : Parted v) {B : ByteArray} (hB : R.o.c.enc = .bytes B) {f : Nat → Nat}
    (hf : nats B = (List.range (R.g + 1)).map f) (hl : ∀ r, r ≤ R.g → f r < 2 ^ 63) :
    ∀ r, r ≤ R.g → R.cut r = f r := by
  intro r hr
  have hlen : B.size / 8 = R.g + 1 := by rw [← nats_length, hf]; simp
  have e : (nats B)[r]! = f r := by rw [hf]; exact getElem!_range_map f (by omega)
  rw [nats_get B (by omega)] at e
  unfold Parted.cut
  rw [Arr.toList_long R.o (ws := Verify.elemsW 8 B) (by unfold longWords; rw [hB]),
    getElem!_pos _ r (by simp [Verify.elemsW]; omega), List.getElem_map, ← Int64.toNat_toInt,
    toInt_word (a := f r) (by simp only [Verify.elemsW, List.getElem_map, List.getElem_range]; exact e) (hl r hr),
    Int.toNat_natCast]

/-- **A gather of a long column** (`bytes` or `foR`) at a dense long index payload whose words, read as
    naturals, all lie below `nx`: an `Arr` of `N` longs, dense, whose element `p` is `x[idx[p]]`. -/
theorem gather_long [Inhabited (El .long)] {nx N : Nat} (x : Arr .long nx) {vs : List UInt64}
    (hv : longWords x.c = some vs) (hxU : nx < USize.size) {idx : ByteArray} (hn : idx.size / 8 = N)
    (hiW : idx.size % 8 = 0) (hi : ∀ p, p < N → (nats idx)[p]! < nx) {verb : String} {c : Column}
    (hvec : Find.vec verb .long (Kernel.gatherColumn .long x.c (Alg.longs idx)) = .ok c) :
    ∃ X : Arr .long N, X.c = c ∧ (∃ B, c.enc = .bytes B) ∧ ∀ p, p < N → X.toList[p]! = x.toList[(nats idx)[p]!]! := by
  obtain ⟨hg, hct⟩ := Struct.vec_ok hvec
  have hsW : (Alg.longs idx).WF := by show idx.size = idx.size / 8 * 8; omega
  have hA : ∀ M Q a, x.c.enc = .alp M Q a → Column.alpF32 a = (8 == 4) := fun _ _ _ he => by
    simp [longWords, he] at hv
  have hfit : Verify.countFits x.c := Struct.countFits_long x hv hxU
  have hfi : Verify.countFits (Alg.longs idx) := by simp [Verify.countFits, Alg.longs]
  obtain ⟨src, ix, -, hix, hcB⟩ := Verify.gatherColumn_fixed_shape (t := .long) (w := 8) rfl x.c (Alg.longs idx) c
    x.wf.1 rfl hfi hA hg
  have hraw := Verify.gatherColumn_raw (t := .long) (w := 8) rfl x.c (Alg.longs idx) c x.wf.1 x.wf.2.2 rfl
    hsW hfit hfi hA hg
  have hix' : ix = idx := by
    have e : Column.bytesOf (Alg.longs idx) = some idx := by first | rfl | simp [Column.bytesOf, Alg.longs]
    rw [e] at hix; exact (Option.some.inj hix).symm
  subst hix'
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hGs := (Verify.gatherBytes_spec (8 : Nat).toUSize (Nat.le_of_eq h8) ((Kernel.nullBits .long).getD 0) src ix).1
  have hcW : c.ty = .long ∧ c.n = N ∧ c.WF := by
    subst hcB
    refine ⟨rfl, hn, ?_⟩
    show (Kernel.gatherBytes (8 : Nat).toUSize _ src ix).size = ix.size / 8 * 8
    rw [hGs, h8]; exact Nat.mul_comm _ _
  have hw : longWords c = some (Column.raw c).toList := by
    cases hl : longWords c with
    | none => rw [hcB] at hl; cases hl
    | some ws => rw [Struct.raw_long hct hcW.2.2 hl]
  have hvs : vs.length = nx := by have := Arr.length_toList x; rw [Arr.toList_long x hv, List.length_map] at this; omega
  refine ⟨⟨c, hcW⟩, rfl, ⟨_, by rw [hcB]⟩, fun p hp => ?_⟩
  have hlt := hi p hp
  rw [nats_get ix (by omega)] at hlt ⊢
  rw [Arr.toList_long ⟨c, hcW⟩ hw, hraw, Struct.raw_long (c := Alg.longs ix) rfl hsW (ws := Verify.elemsW 8 ix) rfl,
    Struct.raw_long x.wf.1 x.wf.2.2 hv, Arr.toList_long x hv, getElem!_pos _ p (by simp [Verify.elemsW]; omega),
    getElem!_pos _ _ (by simp; omega), List.getElem_map, List.getElem_map, List.getElem_map,
    show (Verify.elemsW 8 ix)[p]'(by simp [Verify.elemsW]; omega) = Column.bitsAt ix (p * 8) 8 by
      simp only [Verify.elemsW, List.getElem_map, List.getElem_range],
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact congrArg UInt64.toInt64 (Verify.ofNat_toNat_mod64 _)

/-- **`flipP` transposes**, on a long `val` (`bytes` or `foR`) whose runs all have length `n/g`: column `j`
    of the answer is element `j` of every run. The bounds keep every position below `2^63` and `USize`. -/
theorem flipP_segs [Inhabited (El .long)] {P R : Parted .long} {vs : List UInt64} (hv : longWords P.val.c = some vs)
    (hm : ∀ s ∈ P.segs, s.length = P.n / P.g) (hU : P.n + P.g + 1 < USize.size) (hB : P.n + P.g < 2 ^ 63)
    (h : Struct.flipP P = .ok R) :
    R.segs = (List.range (P.n / P.g)).map fun j => P.segs.map (·[j]!) := by
  unfold Struct.flipP at h
  dsimp only at h
  rw [show (if P.g = 0 then 0 else P.n / P.g) = P.n / P.g by split <;> simp_all] at h
  have hmn : P.n / P.g ≤ P.n := Nat.div_le_self _ _
  generalize hmd : P.n / P.g = m at h hm hmn ⊢
  have hcP := cut_uniform P m hm
  obtain ⟨-, cg, -⟩ := Struct.cuts_nat P.co
  have hn : P.g * m = P.n := by rw [← hcP P.g (Nat.le_refl _)]; exact cg
  cases hob : longBytes P.o.c with
  | none => rw [hob] at h; cases h
  | some ob =>
  rw [hob] at h
  dsimp only at h
  split at h
  case isFalse => first | cases h | simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hx : Alg.cross m P.g = qr at h
  obtain ⟨q, r⟩ := qr
  dsimp only at h
  split at h
  · cases h
  rename_i c hvec
  split at h
  · cases h
  rename_i val' hof
  -- the positions: `q = p / g`, `r = p % g`, `src = r·m + q`
  have hmg : m * P.g < 2 ^ 63 := by rw [Nat.mul_comm]; omega
  have hmgU : m * P.g < USize.size := by rw [Nat.mul_comm]; omega
  obtain ⟨hq, hr⟩ := nats_cross m P.g hmgU hmg (by omega)
  rw [hx] at hq hr
  have hrs : r.size / 8 = m * P.g := by rw [← nats_length, hr]; simp
  have hqs : q.size / 8 = m * P.g := by rw [← nats_length, hq]; simp
  have hrm : nats (Alg.mulc r m) = (List.range (m * P.g)).map fun p => p % P.g * m := by
    rw [nats_mulc r m (by omega) (by omega) fun k hk => by
      rw [hr] at hk
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
      have hp := List.mem_range.1 hp
      have hg : 0 < P.g := Nat.pos_of_ne_zero fun e => by rw [e, Nat.mul_zero] at hp; omega
      have := Nat.mul_le_mul_right m (Nat.le_of_lt (Nat.mod_lt p hg))
      exact ⟨by have := Nat.mod_lt p hg; omega, by omega⟩, hr, List.map_map]; rfl
  have hrms : (Alg.mulc r m).size / 8 = m * P.g := by rw [← nats_length, hrm]; simp
  have hsrc : ∀ p, p < m * P.g → (nats (Alg.add (Alg.mulc r m) q))[p]! = p % P.g * m + p / P.g := fun p hp => by
    have hb : ∀ i, i < m * P.g → (nats (Alg.mulc r m))[i]! + (nats q)[i]! = i % P.g * m + i / P.g := fun i hi => by
      rw [hrm, hq, getElem!_range_map _ hi, getElem!_range_map _ hi]
    have hlt : ∀ i, i < m * P.g → i % P.g * m + i / P.g < m * P.g := fun i hi => by
      have hg : 0 < P.g := Nat.pos_of_ne_zero fun e => by rw [e, Nat.mul_zero] at hi; omega
      have h1 : i / P.g < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
      have h2 : (i % P.g + 1) * m ≤ P.g * m := Nat.mul_le_mul_right m (Nat.mod_lt i hg)
      rw [Nat.succ_mul] at h2; rw [Nat.mul_comm m]; omega
    rw [nats_add _ _ (by omega) (by omega) fun i hi => by rw [hb i (by omega)]; have := hlt i (by omega); omega,
      hrms, getElem!_range_map _ hp, hb p hp]
  -- the gather
  generalize hsd : Alg.add (Alg.mulc r m) q = src at hsrc hvec
  have hss : src.size = 8 * (m * P.g) := by
    rw [← hsd, Alg.add, (Verify.val_spec _ _ _ _ _ _ _).1, Alg.len, hrms, USize.toNat_ofNat_of_lt' hmgU]; rfl
  have hlt : ∀ p, p < m * P.g → p % P.g * m + p / P.g < P.n := fun p hp => by
    have hg : 0 < P.g := Nat.pos_of_ne_zero fun e => by rw [e, Nat.mul_zero] at hp; omega
    have h1 : p / P.g < m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hp)
    have h2 : (p % P.g + 1) * m ≤ P.g * m := Nat.mul_le_mul_right m (Nat.mod_lt p hg)
    rw [Nat.succ_mul] at h2; omega
  obtain ⟨X, hXc, -, hXv⟩ := gather_long P.val hv (by omega) (show src.size / 8 = m * P.g by omega) (by omega)
    (fun p hp => by rw [hsrc p hp]; exact hlt p hp) hvec
  have hX : val' = X := by
    obtain ⟨vc, vw⟩ := val'
    obtain ⟨xc, xw⟩ := X
    have hcv := Struct.of_c hof
    dsimp only at hcv hXc
    subst hcv; subst hXc; rfl
  have hval : ∀ p, p < m * P.g → val'.toList[p]! = P.val.toList[p % P.g * m + p / P.g]! := fun p hp => by
    rw [hX, hXv p hp, hsrc p hp]
  -- the answer's offsets `j·g`
  have hts := nats_til (m + 1) (by omega)
  have hB' : nats (Alg.mulc (Kernel.tilLongs (m + 1).toUSize) P.g) = (List.range (m + 1)).map (· * P.g) := by
    rw [nats_mulc _ _ (by rw [← nats_length, hts]; simp; omega) (by omega) fun k hk => by
      rw [hts, List.mem_range] at hk
      have := Nat.mul_le_mul_right P.g (show k ≤ m by omega)
      rw [Nat.mul_comm m] at this
      exact ⟨by omega, by omega⟩, hts]
  obtain ⟨g', o', co', hoB, rfl⟩ := Struct.parted_ok h
  have hg' : g' = m := by
    have := Arr.n_long_bytes o' hoB
    rw [← nats_length, hB'] at this; simp at this; omega
  subst g'
  have hcR := cut_of_nats ⟨m, m * P.g, o', co', val'⟩ hoB (f := (· * P.g)) hB' fun k hk => by
    have := Nat.mul_le_mul_right P.g (show k ≤ m by exact hk)
    rw [Nat.mul_comm m] at this; dsimp only; omega
  rw [segs_uniform _ P.g hcR, segs_uniform P m hcP]
  refine List.map_congr_left fun j hj => ?_
  have hj : j < m := List.mem_range.1 hj
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  have e1 : (j * P.g + i) % P.g = i := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have e2 : (j * P.g + i) / P.g = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  have hji : j * P.g + i < m * P.g := by
    have := Nat.mul_le_mul_right P.g (show j + 1 ≤ m by omega); rw [Nat.succ_mul] at this; omega
  show val'.toList[j * P.g + i]! = ((List.range m).map fun l => P.val.toList[i * m + l]!)[j]!
  rw [hval _ hji, getElem!_range_map _ hj, e1, e2]

/-- **`+x = ⟨!til g, til m⟩ ≫ cpl ≫ list(⟨outl ≫ x, outr⟩ ≫ (@))`**, the kernel itself, on a long `val` whose
    runs all have length `m = n/g`: `flipP_segs`, then `flip_rel`. -/
theorem flipP_rel [Inhabited (El .long)] {P R : Parted .long} {vs : List UInt64} (hv : longWords P.val.c = some vs)
    (hm : ∀ s ∈ P.segs, s.length = P.n / P.g) (hU : P.n + P.g + 1 < USize.size) (hB : P.n + P.g < 2 ^ 63)
    (h : Struct.flipP P = .ok R) :
    R.rel = rpair (cst (CL.ofList (List.range P.g))) (corefl (· < P.n / P.g)) ≫ ListRel.cpl ≫
      list (rpair ((graph Prod.fst : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ P.rel)
        (graph Prod.snd : (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ Idx) ≫ nth) :=
  flip_rel hm (flipP_segs hv hm hU hB h)

/-! ## `x f/:y` on longs -/

/-- `Alg.cross n m`'s two payloads hold `n·m` whole words each. -/
theorem cross_size (n m : Nat) (hU : n * m < USize.size) :
    (Alg.cross n m).1.size = 8 * (n * m) ∧ (Alg.cross n m).2.size = 8 * (n * m) := by
  unfold Alg.cross
  exact ⟨by rw [(Verify.val_spec _ _ _ _ _ _ _).1, USize.toNat_ofNat_of_lt' hU]; rfl,
    by rw [(Verify.val_spec _ _ _ _ _ _ _).1, USize.toNat_ofNat_of_lt' hU]; rfl⟩

/-- **`eachRightP` is `y.map (x.map (f · b))`** on two long columns (`bytes` or `foR`), `f` a value verb whose
    answer is `long` (`intStep` at q's null, `Ew.elem_long_val`); the bounds keep `ny·nx` positions below
    `2^63` and `USize`. -/
theorem eachRightP_segs [Inhabited (El .long)] {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (he : Eval.ewType v .long .long = some .long) {nx ny : Nat} {x : Arr .long nx} {y : Arr .long ny} {R : Parted .long}
    {xs ys : List UInt64} (hx : longWords x.c = some xs) (hy : longWords y.c = some ys)
    (hU : ny * nx + nx + ny + 1 < USize.size) (hB : ny * nx + nx + ny < 2 ^ 63)
    (h : Struct.eachRightP v .long x y = .ok R) :
    R.segs = y.toList.map fun b => x.toList.map (Kernel.Ew.intStep op Int64.minValue · b) := by
  unfold Struct.eachRightP at h
  generalize hx' : Alg.cross ny nx = ji at h
  obtain ⟨j, i⟩ := ji
  dsimp only at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i xc hxc
  split at h
  · cases h
  rename_i yc hyc
  split at h
  · cases h
  rename_i Z hZ
  obtain ⟨hj, hi⟩ := nats_cross ny nx (by omega) (by omega) (by omega)
  rw [hx'] at hj hi
  have hjs : j.size / 8 = ny * nx := by rw [← nats_length, hj]; simp
  have his : i.size / 8 = ny * nx := by rw [← nats_length, hi]; simp
  obtain ⟨hjz, hiz⟩ := cross_size ny nx (by omega)
  rw [hx'] at hjz hiz
  dsimp only at hjz hiz
  have hpos : ∀ p, p < ny * nx → 0 < nx := fun p hp => Nat.pos_of_ne_zero fun e => by rw [e, Nat.mul_zero] at hp; omega
  obtain ⟨X, hXc, ⟨Bx, hBx⟩, hXv⟩ := gather_long x hx (by omega) his (by omega) (fun p hp => by
    rw [hi, getElem!_range_map _ hp]; exact Nat.mod_lt p (hpos p hp)) hxc
  obtain ⟨Y, hYc, ⟨By, hBy⟩, hYv⟩ := gather_long y hy (by omega) hjs (by omega) (fun p hp => by
    rw [hj, getElem!_range_map _ hp]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hp)) hyc
  have hv : Ew.val v .long X Y = .ok Z := by
    show Ew.dyad v Kernel.Ew.vv .long .long .long X.c Y.c (ny * nx) = .ok Z
    rw [hXc, hYc]; exact hZ
  have hs := val_spec_long hop he (x := X) (yv := Y) (by rw [hXc]; exact hBx) (by rw [hYc]; exact hBy) (by omega) hv
  unfold Ew.ValSpec at hs
  have hel : (fun p : Carrier .long × Carrier .long => elem v he p.1 p.2) =
      fun p => pure (Kernel.Ew.intStep op Int64.minValue p.1 p.2) := funext fun p => Ew.elem_long_val hop he p.1 p.2
  rw [show (fun p : Carrier .long × Carrier .long => elem v he p.1 p.2) = _ from hel, List.mapM_pure] at hs
  have hZl : Z.toList = (X.toList.zip Y.toList).map fun p => Kernel.Ew.intStep op Int64.minValue p.1 p.2 := by
    simpa [pure, Except.pure] using hs.symm
  have hZp : ∀ p, p < ny * nx →
      Z.toList[p]! = Kernel.Ew.intStep op Int64.minValue x.toList[p % nx]! y.toList[p / nx]! := fun p hp => by
    have hXl := Arr.length_toList X
    have hYl := Arr.length_toList Y
    rw [hZl, getElem!_pos _ p (by simp; omega), List.getElem_map, List.getElem_zip]
    dsimp only
    rw [← getElem!_pos X.toList p (by omega), ← getElem!_pos Y.toList p (by omega), hXv p hp, hYv p hp, hi, hj,
      getElem!_range_map _ hp, getElem!_range_map _ hp]
  -- the answer's offsets `j·nx`
  have hts := nats_til (ny + 1) (by omega)
  have hB' : nats (Alg.mulc (Kernel.tilLongs (ny + 1).toUSize) nx) = (List.range (ny + 1)).map (· * nx) := by
    rw [nats_mulc _ _ (by rw [← nats_length, hts]; simp; omega) (by omega) fun k hk => by
      rw [hts, List.mem_range] at hk
      have := Nat.mul_le_mul_right nx (show k ≤ ny by omega)
      exact ⟨by omega, by omega⟩, hts]
  obtain ⟨g', o', co', hoB, rfl⟩ := Struct.parted_ok h
  have hg' : g' = ny := by
    have := Arr.n_long_bytes o' hoB
    rw [← nats_length, hB'] at this; simp at this; omega
  subst g'
  have hcR := cut_of_nats ⟨ny, ny * nx, o', co', Z⟩ hoB (f := (· * nx)) hB' fun k hk => by
    have := Nat.mul_le_mul_right nx (show k ≤ ny by exact hk); dsimp only; omega
  rw [segs_uniform _ nx hcR]
  have hyl := Arr.length_toList y
  have hxl := Arr.length_toList x
  apply List.ext_getElem (by simp [hyl])
  intro r h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  apply List.ext_getElem (by simp [hxl])
  intro k k1 k2
  simp only [List.length_map, List.length_range] at k1
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  have hrk : r * nx + k < ny * nx := by
    have := Nat.mul_le_mul_right nx (show r + 1 ≤ ny by omega); rw [Nat.succ_mul] at this; omega
  have e1 : (r * nx + k) % nx = k := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k1]
  have e2 : (r * nx + k) / nx = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt k1, Nat.zero_add]
  show Z.toList[r * nx + k]! = _
  rw [hZp _ hrk, e1, e2, getElem!_pos x.toList k (by omega), getElem!_pos y.toList r (by omega)]

/-- **`x f/:y = ⟨!x, y⟩ ≫ cpl ≫ list(f)`**, the kernel itself, on two long columns at a value verb answering
    `long`: `eachRightP_segs`, then `eachRight_rel`. -/
theorem eachRightP_rel [Inhabited (El .long)] {v : Prim.Dyadic} {op : UInt8} (hop : Kernel.valOp v = some op)
    (he : Eval.ewType v .long .long = some .long) {nx ny : Nat} {x : Arr .long nx} {y : Arr .long ny} {R : Parted .long}
    {xs ys : List UInt64} (hx : longWords x.c = some xs) (hy : longWords y.c = some ys)
    (hU : ny * nx + nx + ny + 1 < USize.size) (hB : ny * nx + nx + ny < 2 ^ 63)
    (h : Struct.eachRightP v .long x y = .ok R) :
    R.rel = rpair (cst (CL.ofList x.toList)) y.rel ≫ ListRel.cpl ≫
      list (graph fun p : El .long × El .long => Kernel.Ew.intStep op Int64.minValue p.1 p.2) :=
  eachRight_rel (t := .long) (u := .long) (rt := .long) (x := x) (y := y) (R := R)
    (fun a b => Kernel.Ew.intStep op Int64.minValue a b) (eachRightP_segs hop he hx hy hU hB h)



#print axioms flip_rel
#print axioms flipP_rel
#print axioms flipP_segs
#print axioms nats_cross
#print axioms nats_add
#print axioms segs_uniform
#print axioms cut_uniform
#print axioms cut_of_nats
#print axioms gather_long
#print axioms cross_size
#print axioms eachRightP_segs
#print axioms eachRightP_rel
#print axioms nats_til
#print axioms nats_val_va
#print axioms nats_mulc
#print axioms toNat_of_toInt
#print axioms ej_rel
#print axioms indexParted_rel
#print axioms eachRight_rel
#print axioms concat_rel
#print axioms ix_runs
#print axioms parted_rel
#print axioms raze_rel
#print axioms cut_rel

end LeetQ.Rel.Verb
