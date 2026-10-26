/-
  §11.3 of the RelRep design, the structural verbs: each kernel's `*_toList` read through `ix`, then
  the List spec as the expression (`ix_*`), over `Spec.lean`'s reading `x.rel = ix(x.toList)`.
-/
import LeetQ.Rel.Spec
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
    nats (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.va Int64.minValue b (one c) (b.size / 8).toUSize) = (nats b).map F := by
  rw [nats, show one c = Kernel.atomBytes Kernel.Ew.i64 c from rfl, Verify.val_i64_va _ _ _ _ _ hn]
  apply List.ext_getElem (by simp [nats, Verify.elemsW])
  intro i h1 h2
  simp only [nats, Verify.elemsW, List.getElem_map, List.getElem_range, List.length_map, List.length_range] at h2 ⊢
  have := hF _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨i, List.mem_range.2 h2, rfl⟩, rfl⟩)
  rwa [UInt64.ofNat_toNat] at this

/-- `Ew.val` of two long payloads of one length, element by element on the naturals. -/
theorem nats_val_vv (op : UInt8) (a b : ByteArray) (hn : a.size / 8 < USize.size) (hab : b.size / 8 = a.size / 8)
    (F : Nat → Nat → Nat) (hF : ∀ i (h : i < a.size / 8), (Kernel.Ew.intStep op Int64.minValue
      (UInt64.ofNat ((nats a)[i]'(by rw [nats_length]; exact h))).toInt64
      (UInt64.ofNat ((nats b)[i]'(by rw [nats_length]; omega))).toInt64).toUInt64.toNat =
        F ((nats a)[i]'(by rw [nats_length]; exact h)) ((nats b)[i]'(by rw [nats_length]; omega))) :
    nats (Kernel.Ew.val op Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue a b (a.size / 8).toUSize) =
      List.zipWith F (nats a) (nats b) := by
  rw [nats, Verify.val_i64_vv _ _ _ _ _ hn]
  apply List.ext_getElem (by simp [nats, Verify.elemsW, hab])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  have := hF i h1
  simp only [nats, Verify.elemsW, List.getElem_map, List.getElem_range, List.getElem_zipWith, UInt64.ofNat_toNat] at this ⊢
  exact this

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


#print axioms flip_rel
#print axioms ej_rel
#print axioms indexParted_rel
#print axioms eachRight_rel
#print axioms concat_rel
#print axioms ix_runs
#print axioms parted_rel
#print axioms raze_rel
#print axioms cut_rel

end LeetQ.Rel.Verb
