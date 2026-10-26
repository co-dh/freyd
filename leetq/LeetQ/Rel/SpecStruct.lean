/-
  §11.3 of the RelRep design, the structural verbs: each kernel's `*_toList` read through `ix`, then
  the List spec as the expression (`ix_*`), over `Spec.lean`'s reading `x.rel = ix(x.toList)`.
-/
import LeetQ.Rel.Spec
import LeetQ.Rel.SpecFind
import QLean.Verify.Dyad
import QLean.Verify.Structural
import QLean.Verify.Group
import QLean.Verify.BinWin
import QLean.Verify.Encoding
import QLean.Verify.Ids
import QLean.Verify.Grade

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
          (listP_ix_range' xs (c (r+1) - c r) (c r) (by omega) _).2 rfl⟩
        rw [hset hr]; exact (enum_range' _ _ _).2 rfl
      · rintro ⟨_, ⟨rfl, _⟩, S, hS, L, he, hl⟩
        rw [(Λ_iff _ r S).1 hS, hset hr, enum_range'] at he
        subst he
        exact ((listP_ix_range' xs (c (r+1) - c r) (c r) (by omega) w).1 hl).symm
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
              rw [CL.toList_ofList, List.getElem?_eq_getElem (by omega), Option.some.injEq] at h
              exact h.symm
            · rintro rfl
              exact ⟨(CL.ofList segs[i], j), ⟨⟨i, rfl, by rw [List.getElem?_map, List.getElem?_eq_getElem hs]; rfl⟩, rfl⟩,
                by rw [CL.toList_ofList, List.getElem?_eq_getElem (by omega)]⟩)
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
  have hsW : (Alg.longs idx).WF := by show idx.size = idx.size / 8 * 8; omega
  obtain ⟨B, rfl, hBs, hBw⟩ := gatherColumn_long x hv hxU ⟨Alg.longs idx, rfl, hn, hsW⟩ (is := Verify.elemsW 8 idx)
    rfl (by simp [Verify.countFits, Alg.longs]) (Struct.vec_ok hvec).1
  have hvs : vs.length = nx := by have := Arr.length_toList x; rw [Arr.toList_long x hv, List.length_map] at this; omega
  refine ⟨⟨⟨.long, N, .bytes B, none⟩, rfl, rfl, by show B.size = N * 8; exact hBs⟩, rfl, ⟨B, rfl⟩, fun p hp => ?_⟩
  have hlt := hi p hp
  rw [nats_get idx (by omega)] at hlt ⊢
  rw [Arr.toList_long _ (ws := Verify.elemsW 8 B) rfl, hBw, Arr.toList_long x hv,
    getElem!_pos _ p (by simp [Verify.elemsW]; omega), getElem!_pos _ _ (by simp; omega), List.getElem_map,
    List.getElem_map, List.getElem_map,
    show (Verify.elemsW 8 idx)[p]'(by simp [Verify.elemsW]; omega) = Column.bitsAt idx (p * 8) 8 by
      simp only [Verify.elemsW, List.getElem_map, List.getElem_range],
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

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

/-! ## `ej`: `Alg.join`'s grouping, on naturals

  `Alg.join` grades the right rows stably by class id (`grade_spec`), so class `c`'s rows sit at
  `[starts c, starts c + sizes c)` of the grade, in row order; a left row of class `c` expands (`expand`) to
  `sizes c` pairs reading that slice. `starts c` is the rows of a smaller class, `sums sizes - sizes`. -/

/-- A list sorted along `R` splits at a predicate `p` that holds of every `R`-predecessor, in the list, of a
    row holding it: the rows holding `p`, then the rest. -/
theorem split_sorted {α : Type} {R : α → α → Prop} (p : α → Bool) : ∀ {L : List α}, L.Pairwise R →
    (∀ a ∈ L, ∀ b ∈ L, R a b → p b = true → p a = true) → L.filter p ++ L.filter (fun a => !p a) = L
  | [], _, _ => rfl
  | a :: L, h, hp => by
    obtain ⟨ha, hL⟩ := List.pairwise_cons.1 h
    have ih := split_sorted p hL fun x hx y hy => hp x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    by_cases hpa : p a = true
    · rw [List.filter_cons_of_pos hpa, List.filter_cons_of_neg (by simp [hpa]), List.cons_append, ih]
    · have hn : ∀ b ∈ L, ¬ p b = true := fun b hb hpb =>
        hpa (hp a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) (ha b hb) hpb)
      rw [List.filter_cons_of_neg hpa, List.filter_cons_of_pos (by simp [hpa]), List.filter_eq_nil_iff.2 hn,
        List.filter_eq_self.2 fun b hb => by simpa using hn b hb, List.nil_append]

/-- **A stable grade by `g`, sliced at class `c`**: of a permutation of `til n` ascending in `g` and, within one
    `g`, in row order, the `#{g = c}` entries after the `#{g < c}` first are class `c`'s rows in row order. -/
theorem grade_slice (g : Nat → Nat) {n : Nat} (perm : List Nat) (hp : perm.Perm (List.range n))
    (hs : perm.Pairwise fun i j => g i ≤ g j ∧ (g j ≤ g i → i < j)) (c : Nat) :
    (perm.drop ((List.range n).countP fun i => decide (g i < c))).take
        ((List.range n).countP fun i => decide (g i = c)) = (List.range n).filter fun i => decide (g i = c) := by
  have h1 := split_sorted (fun i => decide (g i < c)) hs fun a _ b _ hab hb => by
    simp only [decide_eq_true_eq] at hb ⊢; exact Nat.lt_of_le_of_lt hab.1 hb
  have hB := List.drop_left' (l₁ := perm.filter fun i => decide (g i < c))
    (l₂ := perm.filter fun i => !decide (g i < c)) (List.countP_eq_length_filter ..).symm
  rw [h1] at hB
  have hC : (perm.filter fun i => !decide (g i < c)).filter (fun i => decide (g i = c)) =
      perm.filter fun i => decide (g i = c) := by
    rw [List.filter_filter]; exact List.filter_congr fun i _ => by by_cases h : g i = c <;> simp [h]
  have h2 := split_sorted (fun i => decide (g i = c)) (hs.filter fun i => !decide (g i < c))
      fun a ha b _ ⟨hab, _⟩ hb => by
    obtain ⟨-, ha⟩ := List.mem_filter.1 ha
    simp only [decide_eq_true_eq] at hb ⊢
    have ha : c ≤ g a := by simpa using ha
    omega
  rw [hC] at h2
  have hT := List.take_left' (l₁ := perm.filter fun i => decide (g i = c))
    (l₂ := (perm.filter fun i => !decide (g i < c)).filter fun i => !decide (g i = c)) (List.countP_eq_length_filter ..).symm
  rw [h2] at hT
  rw [← hp.countP_eq, ← hp.countP_eq, hB, hT]
  refine eq_of_pairwise_lt (List.Pairwise.imp_of_mem (fun ha hb hab => ?_) (hs.filter _))
    ((List.pairwise_lt_range ..).filter _) fun i => (hp.filter _).mem_iff
  obtain ⟨-, ha⟩ := List.mem_filter.1 ha
  obtain ⟨-, hb⟩ := List.mem_filter.1 hb
  simp only [decide_eq_true_eq] at ha hb
  exact hab.2 (by omega)

/-- The grade slice read as `sizes c` reads at `starts c + w`, `w < sizes c`. -/
theorem grade_slice_map (g : Nat → Nat) {n : Nat} (perm : List Nat) (hp : perm.Perm (List.range n))
    (hs : perm.Pairwise fun i j => g i ≤ g j ∧ (g j ≤ g i → i < j)) (c : Nat) :
    ((List.range ((List.range n).countP fun i => decide (g i = c))).map
        fun w => perm[((List.range n).countP fun i => decide (g i < c)) + w]!) =
      (List.range n).filter fun i => decide (g i = c) := by
  have e := grade_slice g perm hp hs c
  have hl : perm.length = n := by rw [hp.length_eq, List.length_range]
  have hk := congrArg List.length e
  rw [List.length_take, List.length_drop, ← List.countP_eq_length_filter, hl] at hk
  by_cases h0 : (List.range n).countP (fun i => decide (g i = c)) = 0
  · rw [h0, List.take_zero] at e
    rw [h0, List.range_zero, List.map_nil]; exact e
  · rw [← take_drop_eq perm _ _ (by omega)]; exact e

/-- `#{g < c+1} = #{g < c} + #{g = c}`. -/
theorem countP_lt_succ (g : Nat → Nat) (c : Nat) : ∀ L : List Nat,
    L.countP (fun i => decide (g i < c + 1)) = L.countP (fun i => decide (g i < c)) + L.countP (fun i => decide (g i = c))
  | [] => rfl
  | a :: L => by
    simp only [List.countP_cons, countP_lt_succ g c L, decide_eq_true_eq]
    split <;> split <;> split <;> omega

/-- **`starts = sums sizes - sizes`, on naturals**: the rows of a class below `c` are the sizes of the classes
    below `c`, summed. -/
theorem countP_lt_sum (g : Nat → Nat) (n : Nat) : ∀ c,
    (List.range n).countP (fun i => decide (g i < c)) =
      ((List.range c).map fun c' => (List.range n).countP fun i => decide (g i = c')).sum
  | 0 => by simp
  | c + 1 => by
    rw [countP_lt_succ, countP_lt_sum g n c, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    generalize List.map _ (List.range c) = A
    induction A with
    | nil => simp
    | cons a A ih => rw [List.cons_append, List.sum_cons, List.sum_cons, ← ih]; omega

/-- **`Alg.join`'s pairs are `ejSpec`**, on naturals: left row `i` of class `hit i` expands to `sizes (hit i)`
    pairs `(i, perm[starts (hit i) + w])`, `perm` the stable grade of the right rows by class `gid`; the classes
    meet exactly where the key tuples do. A miss is a class no right row holds. -/
theorem join_ejSpec {l r : List (List Int64)} (gid hit : Nat → Nat) (perm : List Nat)
    (hp : perm.Perm (List.range r.length))
    (hs : perm.Pairwise fun i j => gid i ≤ gid j ∧ (gid j ≤ gid i → i < j))
    (heq : ∀ i, i < l.length → ∀ j, j < r.length → (gid j = hit i ↔ r[j]! = l[i]!)) :
    ((List.range l.length).flatMap fun i =>
      (List.range ((List.range r.length).countP fun j => decide (gid j = hit i))).map fun w =>
        (Int64.ofNat i, Int64.ofNat perm[((List.range r.length).countP fun j => decide (gid j < hit i)) + w]!)) =
      Struct.ejSpec l r := by
  unfold Struct.ejSpec List.flatMap
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  have e := grade_slice_map gid perm hp hs (hit i)
  rw [show ((List.range ((List.range r.length).countP fun j => decide (gid j = hit i))).map fun w =>
      (Int64.ofNat i, Int64.ofNat perm[((List.range r.length).countP fun j => decide (gid j < hit i)) + w]!)) =
      (((List.range ((List.range r.length).countP fun j => decide (gid j = hit i))).map fun w =>
        perm[((List.range r.length).countP fun j => decide (gid j < hit i)) + w]!).map
          fun j => (Int64.ofNat i, Int64.ofNat j)) by rw [List.map_map]; rfl, e]
  congr 1
  exact List.filter_congr fun j hj => by
    have hj := List.mem_range.1 hj
    by_cases h : gid j = hit i
    · rw [decide_eq_true h, beq_iff_eq.2 ((heq i hi j hj).1 h)]
    · rw [decide_eq_false h, beq_eq_false_iff_ne.2 fun e => h ((heq i hi j hj).2 e)]

/-- **`ej` tabulates `l ≫ r°`**, its kernel law narrowed to `Alg.join`'s reading on naturals (`join_ejSpec`):
    the answer's pairs are the expansion of the stable grade `perm` of the right rows by class `gid`, the left
    rows' classes `hit` meeting `gid` exactly where the key tuples do. -/
theorem ej_rel_join {R : Rel .long .long} {l r : List (List Int64)} (gid hit : Nat → Nat) (perm : List Nat)
    (hp : perm.Perm (List.range r.length))
    (hs : perm.Pairwise fun i j => gid i ≤ gid j ∧ (gid j ≤ gid i → i < j))
    (heq : ∀ i, i < l.length → ∀ j, j < r.length → (gid j = hit i ↔ r[j]! = l[i]!))
    (hk : R.toList = (List.range l.length).flatMap fun i =>
      (List.range ((List.range r.length).countP fun j => decide (gid j = hit i))).map fun w =>
        (Int64.ofNat i, Int64.ofNat perm[((List.range r.length).countP fun j => decide (gid j < hit i)) + w]!)) :
    (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ ix l ≫ (ix r)° ≫ graph Int64.ofNat :=
  ej_rel (by rw [hk]; exact join_ejSpec gid hit perm hp hs heq)

/-! ## `aj`: q's bisection inside a group whose times ascend

  The design assumes each key's right rows ascend in time. There `binSpec`'s bisection (`Eval.partitionAt`)
  lands one past the group's rows at or before the needle, so `aj` names the last of them. -/

/-- The bisection's loop lands on `P` when `below` holds exactly below `P` on `[lo, hi)`, `lo ≤ P ≤ hi`. -/
theorem partitionAt_go (below : Nat → Id Bool) (P : Nat) : ∀ fuel lo hi, lo ≤ P → P ≤ hi → hi - lo < fuel →
    (∀ j, lo ≤ j → j < hi → (Id.run (below j) = true ↔ j < P)) →
    Id.run (Eval.partitionAt.go below fuel lo hi) = P
  | 0, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, lo, hi, h1, h2, h3, hf => by
    rw [Eval.partitionAt.go]
    by_cases hle : hi ≤ lo
    · rw [if_pos hle]; show lo = P; omega
    · rw [if_neg hle]
      have hm := hf (lo + (hi - lo) / 2) (Nat.le_add_right ..) (by omega)
      show Id.run (if Id.run (below (lo + (hi - lo) / 2)) = true then
          Eval.partitionAt.go below fuel (lo + (hi - lo) / 2 + 1) hi
        else Eval.partitionAt.go below fuel lo (lo + (hi - lo) / 2)) = P
      by_cases hv : Id.run (below (lo + (hi - lo) / 2)) = true
      · rw [if_pos hv]
        have := hm.1 hv
        exact partitionAt_go below P fuel _ hi (by omega) h2 (by omega) fun j a b => hf j (by omega) b
      · rw [if_neg hv]
        have : ¬ lo + (hi - lo) / 2 < P := fun h => hv (hm.2 h)
        exact partitionAt_go below P fuel lo _ h1 (by omega) (by omega) fun j a b => hf j a (by omega)

/-- **`partitionAt` is the partition point**: `below` holding exactly below `P ≤ n` on `til n`, it answers `P`. -/
theorem partitionAt_eq (below : Nat → Id Bool) {n P : Nat} (hP : P ≤ n)
    (hf : ∀ j, j < n → (Id.run (below j) = true ↔ j < P)) : Id.run (Eval.partitionAt below n) = P :=
  partitionAt_go below P (n + 1) 0 n (Nat.zero_le _) hP (by omega) fun j _ hj => hf j hj

/-- **`bin` in a group whose times ascend names the last row at or before `x`**: `binSpec` is the last of the
    group's rows whose time is at most `x`, `none` where there is none. -/
theorem binSpec_sorted (rt : List Int64) (g : List Nat) (x : Int64) (hs : g.Pairwise fun a b => rt[a]! ≤ rt[b]!) :
    Struct.binSpec rt g x = (g.filter fun j => decide (rt[j]! ≤ x)).getLast? := by
  have hsp := split_sorted (fun j => decide (rt[j]! ≤ x)) hs fun a _ b _ hab hb => by
    simp only [decide_eq_true_eq] at hb ⊢; exact Int64.le_trans hab hb
  generalize hA : g.filter (fun j => decide (rt[j]! ≤ x)) = A at hsp
  generalize hB : g.filter (fun j => !decide (rt[j]! ≤ x)) = B at hsp
  have hAp : ∀ a ∈ A, rt[a]! ≤ x := fun a ha => by rw [← hA] at ha; simpa using (List.mem_filter.1 ha).2
  have hBp : ∀ b ∈ B, ¬ rt[b]! ≤ x := fun b hb => by rw [← hB] at hb; simpa using (List.mem_filter.1 hb).2
  subst hsp
  unfold Struct.binSpec
  rw [partitionAt_eq _ (P := A.length) (by simp) fun j hj => by
    by_cases h : j < A.length
    · rw [getElem!_pos _ j hj, List.getElem_append_left h]
      change decide (_ ≤ x) = true ↔ _
      rw [decide_eq_true_eq]; exact ⟨fun _ => h, fun _ => hAp _ (List.getElem_mem h)⟩
    · rw [getElem!_pos _ j hj, List.getElem_append_right (by omega)]
      change decide (_ ≤ x) = true ↔ _
      rw [decide_eq_true_eq]; exact ⟨fun e => absurd e (hBp _ (List.getElem_mem _)), fun e => absurd e h⟩]
  rcases Nat.eq_zero_or_pos A.length with h0 | h0
  · obtain rfl := List.length_eq_zero_iff.1 h0; rfl
  · obtain ⟨p, hp⟩ : ∃ p, A.length = p + 1 := ⟨A.length - 1, by omega⟩
    rw [hp]
    show some (A ++ B)[p + 1 - 1]! = A.getLast?
    rw [List.getLast?_eq_getElem?, hp, Nat.add_sub_cancel, getElem!_pos _ p (by simp; omega),
      List.getElem_append_left (by omega), List.getElem?_eq_getElem (by omega)]

/-- **`aj` names, per left row, the last row of its key's group at or before its time**, `0N` at none, where each
    key's right rows ascend in time (`hs`): `ajSpec` with `binSpec_sorted` for its bisection. -/
theorem ajSpec_sorted {κ : Type} [BEq κ] [Inhabited κ] (lk : List κ) (lt : List Int64) (rk : List κ) (rt : List Int64)
    (hs : ∀ k ∈ lk, (Struct.group rk k).Pairwise fun a b => rt[a]! ≤ rt[b]!) :
    Struct.ajSpec lk lt rk rt = (lk.zip lt).map fun p =>
      ((((Struct.group rk p.1).filter fun j => decide (rt[j]! ≤ p.2)).getLast?).map Int64.ofNat).getD Int64.minValue := by
  unfold Struct.ajSpec
  refine List.map_congr_left fun ⟨k, t⟩ hkt => ?_
  dsimp only
  rw [binSpec_sorted _ _ _ (hs k (List.of_mem_zip hkt).1)]

/-! ## Nested `x@y`, the kernel: `indexPartedP` on naturals

  The run lengths `o[1..] − o[..g]` gathered at `y` are the block lengths `c`; `expand` writes block `i` as the
  pairs `(i, w)`, `w < c i`, at the positions `S i + w`, `S i = Σ_{k<i} c k` the running sum less its own term. -/

/-- Element `p` of a list mapped by `f` is `f` of element `p`. -/
theorem get!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (xs : List α) {p : Nat} (h : p < xs.length) :
    (xs.map f)[p]! = f xs[p]! := by
  rw [getElem!_pos _ p (by simp; omega), List.getElem_map, getElem!_pos xs p h]

theorem get!_of_get? {α : Type} [Inhabited α] {xs : List α} {p : Nat} {a : α} (h : xs[p]? = some a) : xs[p]! = a := by
  obtain ⟨hp, e⟩ := List.getElem?_eq_some_iff.1 h
  rw [getElem!_pos xs p hp, e]

/-- A list mapped by `f` is `til |xs|` mapped by `f` of each element. -/
theorem map_eq_range {α β : Type} [Inhabited α] (f : α → β) (xs : List α) :
    xs.map f = (List.range xs.length).map fun i => f xs[i]! :=
  List.ext_getElem (by simp) fun i h1 h2 => by
    simp only [List.length_map] at h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, getElem!_pos xs i h1]

theorem getD_range_map {α : Type} (f : Nat → α) (N k : Nat) (d : α) :
    ((List.range N).map f).getD k d = if k < N then f k else d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < N
  · rw [List.getElem?_range h, if_pos h]; rfl
  · rw [List.getElem?_eq_none (by simp; omega), if_neg h]; rfl

/-- A word read with default `0`, as a natural, is the natural read with default `0`. -/
theorem getD_nats (b : ByteArray) (k : Nat) : ((Verify.elemsW 8 b).getD k 0).toNat = (nats b).getD k 0 := by
  unfold nats
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (Verify.elemsW 8 b)[k]? <;> rfl

/-- `Alg.gather 8 src idx` on naturals: each index's word of `src`, `0` past it. -/
theorem nats_gather (src idx : ByteArray) :
    nats (Alg.gather 8 src idx) = (nats idx).map fun k => (nats src).getD k 0 := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have e := Verify.elemsW_gatherBytes (8 : Nat).toUSize (by rw [h8]; decide) (by rw [h8]; exact Nat.le_refl 8) 0 src idx
  rw [h8] at e
  unfold Alg.gather nats
  rw [e, List.map_map, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  show (UInt64.ofNat (((Verify.elemsW 8 src).getD k.toNat 0).toNat % 2 ^ (8 * 8))).toNat =
    ((Verify.elemsW 8 src).map UInt64.toNat).getD k.toNat 0
  rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  exact getD_nats src k.toNat

/-- `Ew.val sub` of two long payloads over `n` words: the differences, word by word, on naturals. -/
theorem nats_val_sub (a b : ByteArray) (n : Nat) (hn : n < USize.size) (ha : n ≤ a.size / 8) (hb : n ≤ b.size / 8)
    (hl : ∀ i, i < n → (nats b)[i]! ≤ (nats a)[i]! ∧ (nats a)[i]! < 2 ^ 63) :
    nats (Kernel.Ew.val Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue a b n.toUSize) =
      (List.range n).map fun i => (nats a)[i]! - (nats b)[i]! := by
  rw [nats, Verify.val_i64_vv _ _ _ _ _ hn]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_map, List.getElem_range,
    nats_get a (by omega), nats_get b (by omega)]
  have hs := hl i h2
  rw [nats_get a (by omega), nats_get b (by omega)] at hs
  generalize Column.bitsAt a (i * 8) 8 = u at hs ⊢
  generalize Column.bitsAt b (i * 8) 8 = w at hs ⊢
  show (if u.toInt64 == Int64.minValue || w.toInt64 == Int64.minValue then Int64.minValue
    else u.toInt64 - w.toInt64).toUInt64.toNat = u.toNat - w.toNat
  rw [ne_min_word (by omega), ne_min_word (by omega), Bool.false_or, if_neg Bool.false_ne_true]
  show (u - w).toNat = _
  exact UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.2 hs.1)

/-- The words `[s, s+k)` of a payload, cut out by `extract` at their byte offsets. -/
theorem nats_extract (b : ByteArray) (s k : Nat) {lo hi : Nat} (hlo : lo = s * 8) (hhi : hi = (s + k) * 8)
    (h : hi ≤ b.size) : nats (b.extract lo hi) = (List.range k).map fun i => (nats b)[s + i]! := by
  subst hlo hhi
  show (Verify.elemsW 8 (b.extract (s * 8) ((s + k) * 8))).map UInt64.toNat = _
  unfold Verify.elemsW
  rw [ByteArray.size_extract, show (min ((s + k) * 8) b.size - s * 8) / 8 = k by omega, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  show (Column.bitsAt (b.extract (s * 8) ((s + k) * 8)) (i * 8) 8).toNat = _
  rw [Verify.bitsAt_extract _ (by omega), nats_get b (by omega), Nat.add_mul]

/-- Two payloads, the first of whole words, read on together. -/
theorem nats_append (a b : ByteArray) (ha : a.size % 8 = 0) : nats (a ++ b) = nats a ++ nats b := by
  unfold nats
  rw [← List.map_append]
  congr 1
  unfold Verify.elemsW
  rw [Verify.ba_size_append, show (a.size + b.size) / 8 = a.size / 8 + b.size / 8 by omega, List.range_add,
    List.map_append, List.map_map]
  refine congr (congrArg HAppend.hAppend (List.map_congr_left fun i hi => ?_)) (List.map_congr_left fun i _ => ?_)
  · have hi := List.mem_range.1 hi
    exact Verify.bitsAt_shift _ _ _ _ _ fun k hk => Verify.ba_append_left _ _ _ (by omega)
  · show Column.bitsAt (a ++ b) ((a.size / 8 + i) * 8) 8 = Column.bitsAt b (i * 8) 8
    exact Verify.bitsAt_shift _ _ _ _ _ fun k _ => by
      rw [show (a.size / 8 + i) * 8 + k = a.size + (i * 8 + k) by omega]; exact Verify.ba_append_right _ _ _

theorem sum_range_succ (c : Nat → Nat) (i : Nat) :
    ((List.range (i + 1)).map c).sum = ((List.range i).map c).sum + c i := by
  simp [List.range_succ]

theorem sum_range_mono (c : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    ((List.range a).map c).sum ≤ ((List.range b).map c).sum := by
  induction b with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := ih (by omega)
      rw [sum_range_succ]; omega
    · rw [h]; exact Nat.le_refl _

theorem sum_range_le_mul (c : Nat → Nat) (b : Nat) (hc : ∀ i, c i ≤ b) : ∀ k, ((List.range k).map c).sum ≤ k * b
  | 0 => by simp
  | k + 1 => by
    rw [sum_range_succ, Nat.succ_mul]; have := sum_range_le_mul c b hc k; have := hc k; omega

/-- **Blocks laid end to end**: block `i` of lengths `c` starts at `S i = Σ_{k<i} c k`, so position `S i + w`
    reads element `w` of block `i`. -/
theorem blocks_get {β : Type} (c : Nat → Nat) (blk : Nat → List β) (hl : ∀ i, (blk i).length = c i) :
    ∀ n {i w : Nat}, i < n → w < c i →
      ((List.range n).flatMap blk)[((List.range i).map c).sum + w]? = (blk i)[w]?
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, w, hi, hw => by
    have hlen : ((List.range n).flatMap blk).length = ((List.range n).map c).sum := by
      rw [List.length_flatMap]; congr 1; exact List.map_congr_left fun i _ => hl i
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
    · have := sum_range_mono c (show i + 1 ≤ n by omega)
      rw [sum_range_succ] at this
      rw [List.getElem?_append_left (by omega), blocks_get c blk hl n h hw]
    · rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]

/-- Every position below `S n` lies in one block: `p = S i + w`, `w < c i`. -/
theorem blocks_cover (c : Nat → Nat) : ∀ n {p : Nat}, p < ((List.range n).map c).sum →
    ∃ i w, i < n ∧ w < c i ∧ p = ((List.range i).map c).sum + w
  | 0, p, h => by simp at h
  | n + 1, p, h => by
    rw [sum_range_succ] at h
    by_cases hp : p < ((List.range n).map c).sum
    · obtain ⟨i, w, hi, hw, e⟩ := blocks_cover c n hp; exact ⟨i, w, by omega, hw, e⟩
    · exact ⟨n, p - ((List.range n).map c).sum, by omega, by omega, by omega⟩

/-- The running sums from `A`: entry `i` is `A` plus the first `i` elements. -/
theorem scanl_add (A : Nat) : ∀ L : List Nat,
    Spec.scanl (· + ·) A L = (List.range (L.length + 1)).map fun i => A + (L.take i).sum
  | [] => by simp [Spec.scanl]
  | x :: L => by
    show A :: Spec.scanl (· + ·) (A + x) L = _
    rw [scanl_add (A + x) L, List.length_cons, List.range_succ_eq_map (n := L.length + 1), List.map_cons, List.map_map]
    simp only [List.take_zero, List.sum_nil, Nat.add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, List.take_succ_cons, List.sum_cons]; omega

/-- A long scan whose step adds a word below `2^63` reads, on naturals, as the running sum. -/
theorem scanl_words (f : Int64 → Int64 → Int64)
    (hf : ∀ a (u : UInt64), u.toNat < 2 ^ 63 → (f a u.toInt64).toUInt64.toNat = (a.toUInt64.toNat + u.toNat) % 2 ^ 64) :
    ∀ (ws : List UInt64) (a : Int64) (A : Nat), a.toUInt64.toNat = A → A + (ws.map UInt64.toNat).sum < 2 ^ 63 →
      (Spec.scanl f a (ws.map UInt64.toInt64)).map (fun x => x.toUInt64.toNat) = Spec.scanl (· + ·) A (ws.map UInt64.toNat)
  | [], a, A, h, _ => by show [a.toUInt64.toNat] = [A]; rw [h]
  | u :: ws, a, A, h, hs => by
    simp only [List.map_cons, List.sum_cons] at hs
    have hu : u.toNat < 2 ^ 63 := by omega
    have e := scanl_words f hf ws (f a u.toInt64) (A + u.toNat) (by rw [hf a u hu, h, Nat.mod_eq_of_lt (by omega)])
      (by omega)
    show a.toUInt64.toNat :: (Spec.scanl f (f a u.toInt64) (ws.map UInt64.toInt64)).map (fun x => x.toUInt64.toNat) =
      A :: Spec.scanl (· + ·) (A + u.toNat) (ws.map UInt64.toNat)
    rw [h, e]

/-- **`Alg.sums b` on naturals**: the running sum of the words, no word `0N` and every sum below `2^63`
    (`Ops.scan_i64_words` at `+`). -/
theorem nats_sums (b : ByteArray) (hn : b.size / 8 < USize.size) (hs : (nats b).sum < 2 ^ 63) :
    nats (Alg.sums b) = (Spec.scanl (· + ·) 0 (nats b)).tail := by
  have e := Ops.scan_i64_words .sums b hn
  obtain ⟨h1, h2⟩ := Spec.kern_verb (op := .add) (sv := .sums) rfl
  rw [h1, h2] at e
  have hf : ∀ a (u : UInt64), u.toNat < 2 ^ 63 →
      ((fun a x => if x == Spec.nul then a else Kernel.Coc.Over.step .add a x) a u.toInt64 : Int64).toUInt64.toNat =
        (a.toUInt64.toNat + u.toNat) % 2 ^ 64 := fun a u hu => by
    show (if u.toInt64 == Spec.nul then a else a + u.toInt64).toUInt64.toNat = _
    rw [show (u.toInt64 == Spec.nul) = false from ne_min_word hu, if_neg Bool.false_ne_true]
    show (a.toUInt64 + u).toNat = _
    exact UInt64.toNat_add _ _
  have e2 := scanl_words (fun a x => if x == Spec.nul then a else Kernel.Coc.Over.step .add a x) hf (Verify.elemsW 8 b) (Kernel.Coc.Over.seed .add Spec.nul) 0 rfl (by simpa [nats] using hs)
  unfold nats
  rw [show Alg.sums b = Kernel.Scan.scan .sums .i64 (b.size / 8).toUSize b from rfl, e, Spec.scan, List.map_map, ← e2]
  generalize Spec.scanl _ _ _ = X
  cases X <;> rfl

/-- The running sums of `(til k).map c`: entry `i` is `S (i+1)`. -/
theorem nats_sums_range (b : ByteArray) (c : Nat → Nat) (k : Nat) (hb : nats b = (List.range k).map c)
    (hn : k < USize.size) (hs : ((List.range k).map c).sum < 2 ^ 63) :
    nats (Alg.sums b) = (List.range k).map fun i => ((List.range (i + 1)).map c).sum := by
  have hk : b.size / 8 = k := by rw [← nats_length, hb]; simp
  rw [nats_sums b (by omega) (by rw [hb]; exact hs), hb, scanl_add, List.length_map, List.length_range,
    List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.1 hi
  show 0 + (((List.range k).map c).take (i + 1)).sum = _
  have e : ((List.range k).map c).take (i + 1) = (List.range (i + 1)).map c :=
    List.ext_getElem (by simp [Nat.min_eq_left (show i + 1 ≤ k by omega)]) fun j _ _ => by simp
  rw [e, Nat.zero_add]

/-- Offsets read off a dense long payload are the cuts, below `2^63`. -/
theorem nats_cuts {v : QAtomicType} (P : Parted v) {ob : ByteArray} (hoB : P.o.c.enc = .bytes ob) (hn : P.n < 2 ^ 63) :
    nats ob = (List.range (P.g + 1)).map P.cut := by
  obtain ⟨-, cg, mono⟩ := Struct.cuts_nat P.co
  have cg' : P.cut P.g = P.n := cg
  have hlen : ob.size / 8 = P.g + 1 := Arr.n_long_bytes P.o hoB
  have hl : P.o.toList = (Verify.elemsW 8 ob).map UInt64.toInt64 := Arr.toList_long P.o (by unfold longWords; rw [hoB])
  apply List.ext_getElem (by rw [nats_length, hlen]; simp)
  intro r h1 h2
  simp only [List.length_map, List.length_range] at h2
  rw [List.getElem_map, List.getElem_range]
  have hc : ((P.o.toList[r]!).toNatClampNeg : Int) = (P.o.toList[r]!).toInt := by
    rw [← Int64.toNat_toInt]; exact Int.toNat_of_nonneg (cuts_get P.co (Nat.le_refl r) (by omega)).1
  have hle : P.cut r ≤ P.n := by rw [← cg']; exact mono_chain P.cut mono (by omega) (Nat.le_refl _)
  have hr : r < (Verify.elemsW 8 ob).length := by simp [Verify.elemsW]; omega
  have hw : P.o.toList[r]! = ((Verify.elemsW 8 ob)[r]'hr).toInt64 := by
    rw [hl, getElem!_pos _ r (by simp; omega), List.getElem_map]
  unfold nats
  rw [List.getElem_map]
  exact toNat_of_toInt (r := ((Verify.elemsW 8 ob)[r]'hr).toInt64) (by omega) (by rw [← hw, ← hc]; rfl)

/-- The runs of a flat form, run `r` read as `cut(r+1) − cut r` reads at `cut r + w`. -/
theorem segs_cuts {v : QAtomicType} [Inhabited (El v)] (P : Parted v) :
    P.segs = (List.range P.g).map fun r =>
      (List.range (P.cut (r+1) - P.cut r)).map fun i => P.val.toList[P.cut r + i]! := by
  obtain ⟨-, cg, mono⟩ := Struct.cuts_nat P.co
  have cg' : P.cut P.g = P.n := cg
  refine List.map_congr_left fun r hr => ?_
  have hr := List.mem_range.1 hr
  have hm : P.cut r ≤ P.cut (r+1) := mono r hr
  have hcg := mono_chain P.cut mono (show r + 1 ≤ P.g by omega) (Nat.le_refl _)
  exact take_drop_eq _ _ _ (by rw [Arr.length_toList]; omega)

/-- A word read as a long that is not negative is its own natural. -/
theorem toInt_toNat_word {u : UInt64} (h : (0 : Int64) ≤ u.toInt64) : u.toInt64.toInt.toNat = u.toNat := by
  have h' : 0 ≤ u.toInt64.toInt := by rw [Int64.le_iff_toInt_le] at h; simpa using h
  have := Int64.toInt_lt u.toInt64
  exact (toNat_of_toInt (r := u.toInt64) (by omega) (Int.toNat_of_nonneg h').symm).symm

/-- **`expand` on naturals**: counts `c i` (`i < n`, each at most `B`) answer the block index `I`, block `i`
    as `c i` copies of `i`, and the offset `W`, `w` at position `S i + w`, `S i = Σ_{k<i} c k`. -/
theorem expand_nats (lens : ByteArray) (c : Nat → Nat) (n B : Nat) (hLn : nats lens = (List.range n).map c)
    (hcn : ∀ i, c i ≤ B) (hU : n * B + n + B + 1 < USize.size) (hB : n * B + n + B < 2 ^ 63) :
    nats (Find.expand lens).1 = (List.range n).flatMap (fun i => List.replicate (c i) i) ∧
      (Find.expand lens).2.size / 8 = ((List.range n).map c).sum ∧
      ∀ i w, i < n → w < c i → (nats (Find.expand lens).2)[((List.range i).map c).sum + w]! = w := by
  have hlens : lens.size / 8 = n := by rw [← nats_length, hLn]; simp
  have hsum : ((List.range n).map c).sum ≤ n * B := sum_range_le_mul c B hcn n
  have hSle : ∀ i, i ≤ n → ((List.range i).map c).sum ≤ n * B := fun i hi =>
    Nat.le_trans (sum_range_mono c hi) hsum
  generalize hE : Find.expand lens = IW
  obtain ⟨I, W⟩ := IW
  unfold Find.expand at hE
  obtain ⟨hI, hW⟩ := Prod.mk.inj hE
  rw [hI] at hW
  have hIn : nats I = (List.range n).flatMap fun i => List.replicate (c i) i := by
    have h8u : (8 : USize).toNat = 8 := by
      show (USize.ofNat 8).toNat = 8; exact USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have e := Verify.expandBytes_spec 8 (by rw [h8u]; decide) (by rw [h8u]; exact Nat.le_refl 8) 0
      (by rw [h8u]; decide) (Kernel.tilLongs (lens.size / 8).toUSize) lens
    rw [hI, h8u, hlens] at e
    rw [nats, e, List.map_flatMap]
    unfold List.flatMap
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.1 hi
    rw [List.map_replicate]
    have hci : (nats lens)[i]! = c i := by rw [hLn]; exact getElem!_range_map _ hi
    rw [nats_get lens (by omega)] at hci
    rw [toInt_word hci (by have := hcn i; omega), Int.toNat_natCast, getD_nats, nats_til n (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  have hIs : I.size / 8 = ((List.range n).map c).sum := by
    rw [← nats_length, hIn, List.length_flatMap]; simp
  have hIp : ∀ i w, i < n → w < c i → (nats I)[((List.range i).map c).sum + w]! = i := fun i w hi hw => by
    rw [hIn]
    exact get!_of_get? (by
      rw [blocks_get c (fun i => List.replicate (c i) i) (fun i => List.length_replicate ..) n hi hw,
        List.getElem?_replicate, if_pos hw])
  have hpos : ∀ i w, i < n → w < c i → ((List.range i).map c).sum + w < I.size / 8 := fun i w hi hw => by
    have := sum_range_mono c (show i + 1 ≤ n by omega); rw [sum_range_succ] at this; omega
  generalize hrs : Kernel.Ew.val Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue
    (Kernel.Scan.scan .sums .i64 (lens.size / 8).toUSize lens) lens (lens.size / 8).toUSize = rs at hW
  have hsums := nats_sums_range lens c n hLn (by omega) (by omega)
  have hrsn : nats rs = (List.range n).map fun i => ((List.range i).map c).sum := by
    rw [← hrs, hlens, show Kernel.Scan.scan .sums .i64 n.toUSize lens = Alg.sums lens by
        unfold Alg.sums Alg.len; rw [hlens],
      nats_val_sub _ _ n (by omega) (by rw [← nats_length, hsums]; simp) (by omega) fun i hi => by
        rw [hsums, hLn, getElem!_range_map _ hi, getElem!_range_map _ hi, sum_range_succ]
        exact ⟨by omega, by have := hSle i (by omega); have := hcn i; omega⟩]
    exact List.map_congr_left fun i hi => by
      have hi := List.mem_range.1 hi
      rw [hsums, hLn, getElem!_range_map _ hi, getElem!_range_map _ hi, sum_range_succ]; omega
  rw [show Kernel.gatherBytes 8 0 rs I = Alg.gather 8 rs I from rfl] at hW
  have hGs : (Alg.gather 8 rs I).size / 8 = I.size / 8 := by
    rw [← nats_length, nats_gather, List.length_map, nats_length]
  have hWp : ∀ i w, i < n → w < c i → (nats W)[((List.range i).map c).sum + w]! = w := fun i w hi hw => by
    have hg : ∀ p, p < I.size / 8 → (nats (Alg.gather 8 rs I))[p]! = ((List.range (nats I)[p]!).map c).sum :=
      fun p hp => by
        obtain ⟨i', w', hi', hw', rfl⟩ := blocks_cover c n (p := p) (by omega)
        rw [nats_gather, get!_map _ _ (by rw [nats_length]; omega), hIp i' w' hi' hw', hrsn, getD_range_map, if_pos hi']
    have hts : (Kernel.tilLongs (I.size / 8).toUSize).size / 8 = I.size / 8 := by
      rw [← nats_length (Kernel.tilLongs (I.size / 8).toUSize), nats_til _ (by omega), List.length_range]
    have hr : ∀ p, p < I.size / 8 → (nats (Kernel.tilLongs (I.size / 8).toUSize))[p]! = p := fun p hp => by
      rw [nats_til _ (by omega), getElem!_pos (List.range _) p (by simp; omega), List.getElem_range]
    rw [← hW, nats_val_sub _ _ _ (by omega) (by rw [hts]; exact Nat.le_refl _) (by omega)
      fun p hp => by
        obtain ⟨i', w', hi', hw', rfl⟩ := blocks_cover c n (p := p) (by omega)
        rw [hg _ hp, hIp i' w' hi' hw', hr _ hp]
        exact ⟨by omega, by have := hSle i' (by omega); have := hcn i'; omega⟩,
      getElem!_range_map _ (hpos i w hi hw), hg _ (hpos i w hi hw), hIp i w hi hw, hr _ (hpos i w hi hw)]
    omega
  have hWs : W.size / 8 = I.size / 8 := by
    rw [← hW, (Verify.val_spec _ _ _ _ _ _ _).1, USize.toNat_ofNat_of_lt' (by omega),
      show Kernel.Ew.width Kernel.Ew.i64 = 8 from rfl]; omega
  exact ⟨hIn, by rw [hWs, hIs], hWp⟩

/-- **`indexPartedP` indexes the runs**: run `i` of the answer is run `y[i]` of `P`, the empty run at an index
    outside `til g`. Restricted to a long `val` (`bytes` or `foR`), dense long offsets and a dense long `y`; the
    bounds keep every position below `2^63` and `USize`. -/
theorem indexPartedP_segs [Inhabited (El .long)] {P R : Parted .long} {ny : Nat} {y : Arr .long ny}
    {vs : List UInt64} {ob yb : ByteArray} (hv : longWords P.val.c = some vs) (hoB : P.o.c.enc = .bytes ob)
    (hy : y.c.enc = .bytes yb) (hU : ny * P.n + P.n + P.g + ny + 1 < USize.size)
    (hB : ny * P.n + P.n + P.g + ny < 2 ^ 63) (h : Struct.indexPartedP P y = .ok R) :
    R.segs = Struct.indexSpec [] P.segs y.toList := by
  unfold Struct.indexPartedP at h
  rw [show longBytes P.o.c = some ob by unfold longBytes; rw [hoB]] at h
  dsimp only at h
  rw [y.c_eq hy, show Find.dense "x@y" .long ⟨.long, ny, .bytes yb, y.attrCell⟩ = pure yb from rfl, pure_bind] at h
  generalize hD : Alg.sub (ob.extract 8 ob.size) (ob.extract 0 (ob.size - 8)) = D at h
  generalize hL : Alg.gather 8 D yb = lens at h
  generalize hE : Find.expand lens = IW at h
  obtain ⟨I, W⟩ := IW
  dsimp only at h
  generalize hS : Alg.add (Alg.gather 8 (Alg.gather 8 ob yb) I) W = src at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i c0 hvec
  split at h
  · cases h
  rename_i val' hof
  -- the cuts of `P`, read off `ob`
  obtain ⟨-, cg, mono⟩ := Struct.cuts_nat P.co
  have cg' : P.cut P.g = P.n := cg
  have hcut : ∀ r, r ≤ P.g → P.cut r ≤ P.n := fun r hr => by
    rw [← cg']; exact mono_chain P.cut mono hr (Nat.le_refl _)
  have hob := nats_cuts P hoB (by omega)
  have hobs : ob.size = (P.g + 1) * 8 := by
    have hw := P.o.wf.2.2; have := P.o.wf.2.1
    simp only [Column.WF, P.o.wf.1, hoB, QAtomicType.width] at hw; omega
  have hybs : yb.size = ny * 8 := by
    have hw := y.wf.2.2; have := y.wf.2.1
    simp only [Column.WF, y.wf.1, hy, QAtomicType.width] at hw; omega
  have hyl : (nats yb).length = ny := by rw [nats_length, hybs]; omega
  have hobi : ∀ r, r ≤ P.g → (nats ob)[r]! = P.cut r := fun r hr => by
    rw [hob]; exact getElem!_range_map _ (by omega)
  -- the run lengths `D`
  have hD1 := nats_extract ob 1 P.g (lo := 8) (hi := ob.size) rfl (by rw [hobs]; omega) (by omega)
  have hD0 := nats_extract ob 0 P.g (lo := 0) (hi := ob.size - 8) rfl (by rw [hobs]; omega) (by omega)
  have hD1i : ∀ i, i < P.g → (nats (ob.extract 8 ob.size))[i]! = P.cut (i + 1) := fun i hi => by
    rw [hD1, getElem!_range_map _ hi, hobi _ (by omega), Nat.add_comm]
  have hD0i : ∀ i, i < P.g → (nats (ob.extract 0 (ob.size - 8)))[i]! = P.cut i := fun i hi => by
    rw [hD0, getElem!_range_map _ hi, hobi _ (by omega), Nat.zero_add]
  have hsz1 : (ob.extract 8 ob.size).size / 8 = P.g := by rw [← nats_length, hD1]; simp
  have hsz0 : (ob.extract 0 (ob.size - 8)).size / 8 = P.g := by rw [← nats_length, hD0]; simp
  have hDn : nats D = (List.range P.g).map fun r => P.cut (r + 1) - P.cut r := by
    rw [← hD, Alg.sub, Alg.len, Alg.nul, hsz1, nats_val_sub _ _ P.g (by omega) (by omega) (by omega) fun i hi => by
      rw [hD1i i hi, hD0i i hi]; exact ⟨mono i hi, by have := hcut (i + 1) (by omega); omega⟩]
    exact List.map_congr_left fun i hi => by
      have hi := List.mem_range.1 hi; rw [hD1i i hi, hD0i i hi]
  -- the block lengths `c`, `lens` gathered at `y`
  obtain ⟨c, hc⟩ : ∃ c : Nat → Nat, c = fun i =>
      if (nats yb)[i]! < P.g then P.cut ((nats yb)[i]! + 1) - P.cut (nats yb)[i]! else 0 := ⟨_, rfl⟩
  have hcn : ∀ i, c i ≤ P.n := fun i => by
    rw [hc]; dsimp only
    by_cases hh : (nats yb)[i]! < P.g
    · rw [if_pos hh]; have := hcut ((nats yb)[i]! + 1) (by omega); omega
    · rw [if_neg hh]; omega
  have hLn : nats lens = (List.range ny).map c := by
    rw [← hL, nats_gather, hDn, map_eq_range _ (nats yb), hyl]
    exact List.map_congr_left fun i _ => by rw [getD_range_map, hc]
  have hlens : lens.size / 8 = ny := by rw [← nats_length, hLn]; simp
  have hsum : ((List.range ny).map c).sum ≤ ny * P.n := sum_range_le_mul c P.n hcn ny
  have hSle : ∀ i, i ≤ ny → ((List.range i).map c).sum ≤ ny * P.n := fun i hi =>
    Nat.le_trans (sum_range_mono c hi) hsum
  -- `expand`: the block index `I` and the offset in the block `W`
  obtain ⟨hIn, hWs, hWp⟩ := expand_nats lens c ny P.n hLn hcn (by omega) (by omega)
  rw [hE] at hIn hWs hWp
  dsimp only at hIn hWs hWp
  have hIs : I.size / 8 = ((List.range ny).map c).sum := by
    rw [← nats_length, hIn, List.length_flatMap]; simp
  have hIp : ∀ i w, i < ny → w < c i → (nats I)[((List.range i).map c).sum + w]! = i := fun i w hi hw => by
    rw [hIn]
    exact get!_of_get? (by
      rw [blocks_get c (fun i => List.replicate (c i) i) (fun i => List.length_replicate ..) ny hi hw,
        List.getElem?_replicate, if_pos hw])
  have hpos : ∀ i w, i < ny → w < c i → ((List.range i).map c).sum + w < I.size / 8 := fun i w hi hw => by
    have := sum_range_mono c (show i + 1 ≤ ny by omega); rw [sum_range_succ] at this; omega
  have hsums := nats_sums_range lens c ny hLn (by omega) (by omega)
  -- `src`: run `y[i]`'s start plus the offset
  have hCi : ∀ i, i < ny → (nats (Alg.gather 8 ob yb)).getD i 0 = (nats ob).getD (nats yb)[i]! 0 := fun i hi => by
    rw [nats_gather, map_eq_range _ (nats yb), hyl, getD_range_map, if_pos hi]
  have hhit : ∀ i, 0 < c i → (nats yb)[i]! < P.g := fun i h => by
    rw [hc] at h; dsimp only at h; by_cases hh : (nats yb)[i]! < P.g
    · exact hh
    · rw [if_neg hh] at h; omega
  have hAs : (Alg.gather 8 (Alg.gather 8 ob yb) I).size / 8 = I.size / 8 := by
    rw [← nats_length, nats_gather, List.length_map, nats_length]
  have hAp : ∀ i w, i < ny → w < c i →
      (nats (Alg.gather 8 (Alg.gather 8 ob yb) I))[((List.range i).map c).sum + w]! = P.cut (nats yb)[i]! :=
    fun i w hi hw => by
      have hh := hhit i (by omega)
      rw [nats_gather, get!_map _ _ (by rw [nats_length]; exact hpos i w hi hw), hIp i w hi hw, hCi i hi, hob,
        getD_range_map, if_pos (by omega)]
  rw [← hIs] at hWs
  have hsrc : ∀ i w, i < ny → w < c i → (nats src)[((List.range i).map c).sum + w]! = P.cut (nats yb)[i]! + w :=
    fun i w hi hw => by
      rw [← hS, nats_add _ _ (by rw [hAs]; omega) (by rw [hWs, hAs]) fun p hp => by
          obtain ⟨i', w', hi', hw', rfl⟩ := blocks_cover c ny (p := p) (by omega)
          rw [hAp i' w' hi' hw', hWp i' w' hi' hw']
          have hh := hhit i' (by omega)
          have := hcut ((nats yb)[i']! + 1) (by omega)
          rw [hc] at hw'; dsimp only at hw'; rw [if_pos hh] at hw'; omega,
        hAs, getElem!_range_map _ (hpos i w hi hw), hAp i w hi hw, hWp i w hi hw]
  have hsrcs : src.size = 8 * (I.size / 8) := by
    rw [← hS, Alg.add, (Verify.val_spec _ _ _ _ _ _ _).1, Alg.len, hAs, USize.toNat_ofNat_of_lt' (by omega),
      show Kernel.Ew.width Kernel.Ew.i64 = 8 from rfl]
  have hlen : Alg.len src = ((List.range ny).map c).sum := by unfold Alg.len; omega
  -- the gather of `val`
  obtain ⟨X, hXc, -, hXv⟩ := gather_long P.val hv (by omega) (N := Alg.len src) rfl (by omega) (fun p hp => by
    obtain ⟨i, w, hi, hw, rfl⟩ := blocks_cover c ny (p := p) (by omega)
    have hh := hhit i (by omega)
    have := hcut ((nats yb)[i]! + 1) (by omega)
    rw [hsrc i w hi hw]; rw [hc] at hw; dsimp only at hw; rw [if_pos hh] at hw; omega) hvec
  have hX : val' = X := by
    obtain ⟨vc, vw⟩ := val'
    obtain ⟨xc, xw⟩ := X
    have hcv := Struct.of_c hof
    dsimp only at hcv hXc
    subst hcv; subst hXc; rfl
  subst val'
  -- the answer's offsets `0, S 1, …, S ny`
  obtain ⟨g', o', co', hoB', rfl⟩ := Struct.parted_ok h
  have hcat : nats (Kernel.concatBytes #[Find.one 0, Alg.sums lens]) =
      (List.range (ny + 1)).map fun i => ((List.range i).map c).sum := by
    rw [show Kernel.concatBytes #[Find.one 0, Alg.sums lens] = (ByteArray.empty ++ Find.one 0) ++ Alg.sums lens from rfl,
      nats_append _ _ (by decide), nats_append _ _ (by decide), show nats ByteArray.empty = [] from rfl,
      show nats (Find.one 0) = [0] from rfl, hsums, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  have hg' : g' = ny := by
    have := Arr.n_long_bytes o' hoB'
    rw [← nats_length, hcat] at this; simp at this; omega
  subst g'
  have hcR := cut_of_nats ⟨ny, Alg.len src, o', co', X⟩ hoB' (f := fun i => ((List.range i).map c).sum) hcat
    fun r hr => by have := hSle r hr; dsimp only; omega
  -- run by run
  have hyt : y.toList = (Verify.elemsW 8 yb).map UInt64.toInt64 := Arr.toList_long y (by unfold longWords; rw [hy])
  rw [segs_cuts, hyt, Struct.indexSpec, List.map_map]
  apply List.ext_getElem (by simp [Verify.elemsW, hybs])
  intro r h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, List.getElem_map]
  have hu : (Verify.elemsW 8 yb)[r]'(by simp [Verify.elemsW]; omega) = Column.bitsAt yb (r * 8) 8 := by
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
  have hyr : (nats yb)[r]! = (Column.bitsAt yb (r * 8) 8).toNat := nats_get yb (by omega)
  show (List.range (Parted.cut ⟨ny, Alg.len src, o', co', X⟩ (r + 1) - Parted.cut ⟨ny, Alg.len src, o', co', X⟩ r)).map
      (fun i => X.toList[Parted.cut ⟨ny, Alg.len src, o', co', X⟩ r + i]!) =
    (if 0 ≤ ((Verify.elemsW 8 yb)[r]'(by simp [Verify.elemsW]; omega)).toInt64 then
      P.segs.getD ((Verify.elemsW 8 yb)[r]'(by simp [Verify.elemsW]; omega)).toInt64.toInt.toNat [] else [])
  have hr1 : r < ny := by simp [Verify.elemsW] at h2; omega
  rw [hcR r (Nat.le_of_lt hr1), hcR (r + 1) hr1, hu]
  dsimp only
  rw [sum_range_succ, Nat.add_sub_cancel_left]
  generalize Column.bitsAt yb (r * 8) 8 = u at hyr ⊢
  by_cases hh : u.toNat < P.g
  · have hcr : c r = P.cut (u.toNat + 1) - P.cut u.toNat := by rw [hc]; dsimp only; rw [hyr, if_pos hh]
    have hp : (0 : Int64) ≤ u.toInt64 := by
      rw [Int64.le_iff_toInt_le, toInt_word rfl (by omega)]; simp
    rw [if_pos hp, toInt_toNat_word hp, segs_cuts P, getD_range_map, if_pos hh, hcr]
    refine List.map_congr_left fun w hw => ?_
    have hw := List.mem_range.1 hw
    rw [← hcr] at hw
    rw [hXv _ (by rw [hlen, ← hIs]; exact hpos r w hr1 hw), hsrc r w hr1 hw, hyr]
  · have hcr : c r = 0 := by rw [hc]; dsimp only; rw [hyr, if_neg hh]
    rw [hcr]
    split
    · rename_i hp
      rw [toInt_toNat_word hp, segs_cuts P, getD_range_map, if_neg hh]; rfl
    · rfl

/-- **Nested `x@y = y ≫ miss(pos ≫ x, [])`**, the kernel itself: `indexPartedP_segs`, then `indexParted_rel`. -/
theorem indexPartedP_rel [Inhabited (El .long)] {P R : Parted .long} {ny : Nat} {y : Arr .long ny}
    {vs : List UInt64} {ob yb : ByteArray} (hv : longWords P.val.c = some vs) (hoB : P.o.c.enc = .bytes ob)
    (hy : y.c.enc = .bytes yb) (hU : ny * P.n + P.n + P.g + ny + 1 < USize.size)
    (hB : ny * P.n + P.n + P.g + ny < 2 ^ 63) (h : Struct.indexPartedP P y = .ok R) :
    R.rel = y.rel ≫ miss (pos ≫ P.rel) (CL.ofList []) :=
  indexParted_rel (indexPartedP_segs hv hoB hy hU hB h)

/-! ## `ej`, the kernel: `Alg.join` on naturals

  `Alg.join l r` reads three lane kernels — the right's classes `gid` (`groupIds`, `classSizes`), each left
  row's class `hit` (`find`, the class count at a miss) and the stable grade `perm` of the right rows by class
  (`grade`) — and the rest is long arithmetic: `expand` of the matched sizes, the class starts
  `sums sizes - sizes`, two gathers and an add. `join_nats` reads that arithmetic on naturals, the three lane
  kernels' answers its hypotheses. -/

/-- Two flatMaps of blocks of equal lengths zip block by block. -/
theorem zip_flatMap {α β : Type} (A : Nat → List α) (B : Nat → List β) (hl : ∀ i, (A i).length = (B i).length) :
    ∀ n, ((List.range n).flatMap A).zip ((List.range n).flatMap B) = (List.range n).flatMap fun i => (A i).zip (B i)
  | 0 => rfl
  | n + 1 => by
    have hlen : ((List.range n).flatMap A).length = ((List.range n).flatMap B).length := by
      rw [List.length_flatMap, List.length_flatMap]; congr 1; exact List.map_congr_left fun i _ => hl i
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_append, List.zip_append hlen,
      zip_flatMap A B hl n]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- `k` copies of `i` zipped with `k` reads of `f` pair `i` with each read. -/
theorem zip_replicate_range {α : Type} (i k : Nat) (f : Nat → α) :
    (List.replicate k i).zip ((List.range k).map f) = (List.range k).map fun w => (i, f w) :=
  List.ext_getElem (by simp) fun w h1 h2 => by simp

/-- **`Alg.join` on naturals**: left row `i` of class `hit i` pairs with the `#{gid = hit i}` grade entries
    from `#{gid < hit i}` on. Hypotheses: the right's `G` classes `gid` and their sizes (`groupIds`,
    `classSizes`), each left row's class `hit`, `G` at a miss (`find`), the grade `perm` of the right rows by
    class (`grade`); the bounds keep every position below `2^63` and `USize`. -/
theorem join_nats (l r : Alg.Code) {G nl : Nat} (gid hit : Nat → Nat) (perm : List Nat)
    (hG : Alg.len r.groupIds.2 = G) (hgid : ∀ j, j < r.n → gid j < G)
    (hsz : nats (Alg.classSizes r.n r.groupIds) =
      (List.range G).map fun h => (List.range r.n).countP fun j => decide (gid j = h))
    (hhit : nats ((r.gather r.groupIds.2).find l) = (List.range nl).map hit) (hhG : ∀ i, hit i ≤ G)
    (hpn : nats (Alg.Code.ofIds G r.n r.groupIds.1).grade = perm) (hpl : perm.length = r.n)
    (hU : nl * r.n + nl + r.n + G + 1 < USize.size) (hB : nl * r.n + nl + r.n + G < 2 ^ 63) :
    (nats (Alg.join l r).1).zip (nats (Alg.join l r).2) = (List.range nl).flatMap fun i =>
      (List.range ((List.range r.n).countP fun j => decide (gid j = hit i))).map fun w =>
        (i, perm[((List.range r.n).countP fun j => decide (gid j < hit i)) + w]!) := by
  unfold Alg.join
  dsimp only
  generalize r.groupIds = g at hG hsz hhit hpn ⊢
  subst hG
  generalize Alg.classSizes r.n g = sizes at hsz ⊢
  generalize (r.gather g.2).find l = hb at hhit ⊢
  generalize (Alg.Code.ofIds (Alg.len g.2) r.n g.1).grade = pb at hpn ⊢
  subst hpn
  generalize Alg.len g.2 = G at hgid hsz hhG hU hB
  obtain ⟨cn, hcn⟩ : ∃ cn : Nat → Nat, cn = fun h => (List.range r.n).countP fun j => decide (gid j = h) := ⟨_, rfl⟩
  obtain ⟨cs, hcs⟩ : ∃ cs : Nat → Nat, cs = fun h => (List.range r.n).countP fun j => decide (gid j < h) := ⟨_, rfl⟩
  rw [← hcn] at hsz
  have hcnG : cn G = 0 := by
    rw [hcn]; exact List.countP_eq_zero.2 fun j hj => by
      have := hgid j (List.mem_range.1 hj); simp only [decide_eq_true_eq]; omega
  have hcnle : ∀ h, cs h + cn h ≤ r.n := fun h => by
    have e := countP_lt_succ gid h (List.range r.n)
    have := List.countP_le_length (p := fun i => decide (gid i < h + 1)) (l := List.range r.n)
    rw [List.length_range] at this; rw [hcs, hcn]; dsimp only; omega
  have hsum : ∀ h, ((List.range h).map cn).sum = cs h := fun h => by rw [hcn, hcs]; exact (countP_lt_sum gid r.n h).symm
  have hcr : ∀ i, cn (hit i) ≤ r.n := fun i => by have := hcnle (hit i); omega
  have hhG' : ∀ i, 0 < cn (hit i) → hit i < G := fun i h => by
    have := hhG i; rcases Nat.lt_or_eq_of_le this with e | e
    · exact e
    · rw [e, hcnG] at h; omega
  -- the matched sizes, gathered at `hit`
  have hLn : nats (Alg.gather 8 sizes hb) = (List.range nl).map fun i => cn (hit i) := by
    rw [nats_gather, hhit, hsz, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    show ((List.range G).map cn).getD (hit i) 0 = cn (hit i)
    rw [getD_range_map]; split
    · rfl
    · rw [show hit i = G by have := hhG i; omega, hcnG]
  have hhb : hb.size / 8 = nl := by rw [← nats_length, hhit]; simp
  obtain ⟨hIn, hWs, hWp⟩ := expand_nats _ (fun i => cn (hit i)) nl r.n hLn hcr (by omega) (by omega)
  generalize Find.expand (Alg.gather 8 sizes hb) = IW at hIn hWs hWp ⊢
  obtain ⟨I, W⟩ := IW
  dsimp only at hIn hWs hWp ⊢
  have hIs : I.size / 8 = ((List.range nl).map fun i => cn (hit i)).sum := by
    rw [← nats_length, hIn, List.length_flatMap]; simp
  have hIp : ∀ i w, i < nl → w < cn (hit i) → (nats I)[((List.range i).map fun i => cn (hit i)).sum + w]! = i :=
    fun i w hi hw => by
      rw [hIn]
      exact get!_of_get? (by
        rw [blocks_get (fun i => cn (hit i)) (fun i => List.replicate (cn (hit i)) i) (fun i => List.length_replicate ..)
          nl hi hw, List.getElem?_replicate, if_pos hw])
  have hpos : ∀ i w, i < nl → w < cn (hit i) → ((List.range i).map fun i => cn (hit i)).sum + w < I.size / 8 :=
    fun i w hi hw => by
      have := sum_range_mono (fun i => cn (hit i)) (show i + 1 ≤ nl by omega); rw [sum_range_succ] at this; omega
  have hSle : ((List.range nl).map fun i => cn (hit i)).sum ≤ nl * r.n := sum_range_le_mul _ r.n hcr nl
  -- the class starts `sums sizes - sizes`
  have hGs : ((List.range G).map cn).sum < 2 ^ 63 := by rw [hsum]; have := hcnle G; omega
  have hss := nats_sums_range sizes cn G hsz (by omega) hGs
  have hsl : (Alg.sums sizes).size / 8 = G := by rw [← nats_length, hss]; simp
  have hzl : sizes.size / 8 = G := by rw [← nats_length, hsz]; simp
  have hst : nats (Alg.sub (Alg.sums sizes) sizes) = (List.range G).map cs := by
    rw [Alg.sub, Alg.len, Alg.nul, hsl, nats_val_sub _ _ G (by omega) (by omega) (by omega) fun i hi => by
        rw [hss, hsz, getElem!_range_map _ hi, getElem!_range_map _ hi, sum_range_succ]
        exact ⟨by omega, by rw [hsum]; have := hcnle i; omega⟩]
    exact List.map_congr_left fun h hh => by
      have hh := List.mem_range.1 hh
      rw [hss, hsz, getElem!_range_map _ hh, getElem!_range_map _ hh, sum_range_succ, Nat.add_sub_cancel, hsum]
  -- the gathers: `hit` at `I`, then the starts
  generalize Alg.sub (Alg.sums sizes) sizes = st at hst ⊢
  have hA1s : (Alg.gather 8 hb I).size / 8 = I.size / 8 := by rw [← nats_length, nats_gather, List.length_map, nats_length]
  have hA2s : (Alg.gather 8 st (Alg.gather 8 hb I)).size / 8 = I.size / 8 := by
    rw [← nats_length, nats_gather, List.length_map, nats_length, hA1s]
  have hA2 : ∀ i w, i < nl → w < cn (hit i) →
      (nats (Alg.gather 8 st (Alg.gather 8 hb I)))[((List.range i).map fun i => cn (hit i)).sum + w]! = cs (hit i) :=
    fun i w hi hw => by
      have hp := hpos i w hi hw
      rw [nats_gather, get!_map _ _ (by rw [nats_length, hA1s]; exact hp), nats_gather,
        get!_map _ _ (by rw [nats_length]; exact hp), hIp i w hi hw, hhit, getD_range_map, if_pos hi, hst,
        getD_range_map, if_pos (hhG' i (by omega))]
  have hX := nats_add (Alg.gather 8 st (Alg.gather 8 hb I)) W (by rw [hA2s]; omega) (by rw [hA2s, hWs, hIs])
    fun p hp => by
      rw [hA2s, hIs] at hp
      obtain ⟨i, w, hi, hw, rfl⟩ := blocks_cover (fun i => cn (hit i)) nl hp
      rw [hA2 i w hi hw, hWp i w hi hw]; have := hcnle (hit i); omega
  rw [hA2s, hIs] at hX
  -- run by run
  have hR : nats (Alg.gather 8 pb (Alg.add (Alg.gather 8 st (Alg.gather 8 hb I)) W)) =
      (List.range nl).flatMap fun i => (List.range (cn (hit i))).map fun w => (nats pb)[cs (hit i) + w]! := by
    rw [nats_gather, hX, List.map_map]
    apply List.ext_getElem?
    intro p
    by_cases hp : p < ((List.range nl).map fun i => cn (hit i)).sum
    · obtain ⟨i, w, hi, hw, rfl⟩ := blocks_cover (fun i => cn (hit i)) nl hp
      rw [blocks_get (fun i => cn (hit i)) (fun i => (List.range (cn (hit i))).map fun w => (nats pb)[cs (hit i) + w]!)
        (fun i => by simp) nl hi hw, List.getElem?_map, List.getElem?_range hp, List.getElem?_map,
        List.getElem?_range hw]
      simp only [Option.map_some, Function.comp, Option.some.injEq]
      rw [hA2 i w hi hw, hWp i w hi hw, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show cs (hit i) + w < (nats pb).length by have := hcnle (hit i); omega),
        Option.getD_some, getElem!_pos (nats pb) (cs (hit i) + w) (show cs (hit i) + w < (nats pb).length by have := hcnle (hit i); omega)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by
        rw [List.length_flatMap]; simp only [List.length_map, List.length_range]; omega)]
  rw [hIn, hR, zip_flatMap _ _ (fun i => by simp)]
  subst hcn hcs
  unfold List.flatMap
  congr 1
  exact List.map_congr_left fun i _ => zip_replicate_range i _ _

/-- The words of a long payload are the ids qlean's grouping lemmas read. -/
theorem nats_eq_ids (b : ByteArray) : nats b = Verify.ids b := by
  simp only [nats, Verify.elemsW, Verify.ids, List.map_map]; rfl

/-- The id lane of `G` classes is one `Column.idAt` reads. -/
theorem idWidthOf_lane (G : Nat) : Column.idWidthOf G = 0 ∨ Column.idWidthOf G = 1 ∨ Column.idWidthOf G = 2 ∨
    Column.idWidthOf G = 4 ∨ Column.idWidthOf G = 8 ∨ Column.idWidthOf G = 16 ∨ Column.idWidthOf G = 32 ∨
    Column.idWidthOf G = 64 := by
  unfold Column.idWidthOf Column.laneWidth
  repeat' split
  all_goals omega

/-- At most `m` classes among `m` rows. -/
theorem firstsOf_length_le {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat) : (Verify.firstsOf g m).length ≤ m := by
  unfold Verify.firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_range]; exact Nat.le_refl _)

/-- **`groupIds` of a code at a sort layout `k`** holding all its `n` rows: `groupIds_spec` at `n`, the
    classes `groupOf` packed at their lane and the firsts. -/
theorem groupIds_at (rc : Alg.Code) {k : Kernel.Scan.Kind} (hk : rc.kind = some k)
    (hav : rc.n ≤ k.avail rc.b) (hn : rc.n < USize.size) :
    rc.groupIds.1 = Column.packIds (Column.idWidthOf (Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).length)
      rc.n (Verify.groupOf (Kernel.Order.keyAt k rc.b) rc.n) ∧
    Verify.ids rc.groupIds.2 = Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n := by
  have hg : rc.groupIds = Kernel.Order.groupIds k rc.n.toUSize rc.b := by
    unfold Alg.Code.groupIds; rw [hk]
  have hm : min rc.n.toUSize.toNat (k.avail rc.b) = rc.n := by
    rw [USize.toNat_ofNat_of_lt' hn]; exact Nat.min_eq_left hav
  have := Verify.groupIds_spec k rc.n.toUSize rc.b
  rw [hm] at this; rw [hg]; exact this

/-- **`groupIds`, `classSizes` of a code at a sort layout `k`**: `join_nats`'s right-side hypotheses, the
    classes `gid = groupOf` of the lane's keys numbered by first occurrence, `G = |firstsOf|` of them, each
    class's size its count of rows. -/
theorem groupIds_lane (rc : Alg.Code) {k : Kernel.Scan.Kind} (hk : rc.kind = some k)
    (hav : rc.n ≤ k.avail rc.b) (hn : rc.n < USize.size) :
    Alg.len rc.groupIds.2 = (Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).length ∧
    (∀ j, j < rc.n → Verify.groupOf (Kernel.Order.keyAt k rc.b) rc.n j <
      (Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).length) ∧
    nats (Alg.classSizes rc.n rc.groupIds) =
      (List.range (Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).length).map fun h =>
        (List.range rc.n).countP fun j => decide (Verify.groupOf (Kernel.Order.keyAt k rc.b) rc.n j = h) := by
  obtain ⟨h1, h2⟩ := groupIds_at rc hk hav hn
  generalize rc.groupIds = g at h1 h2
  have hGn := firstsOf_length_le (Kernel.Order.keyAt k rc.b) rc.n
  generalize Kernel.Order.keyAt k rc.b = key at h1 h2 hGn
  have hlt : ∀ j, j < rc.n → Verify.groupOf key rc.n j < (Verify.firstsOf key rc.n).length :=
    fun j hj => Verify.groupOf_lt hj
  have hl : Alg.len g.2 = (Verify.firstsOf key rc.n).length := by
    unfold Alg.len; rw [← nats_length, nats_eq_ids, h2]
  refine ⟨hl, hlt, ?_⟩
  generalize (Verify.firstsOf key rc.n).length = G at hGn hlt hl h1 ⊢
  generalize Verify.groupOf key rc.n = gid at hlt h1 ⊢
  have hW := idWidthOf_lane G
  have hW64 : Column.idWidthOf G ≤ 64 := by rcases hW with h | h | h | h | h | h | h | h <;> omega
  have h64 := USize.size_le
  unfold Alg.classSizes
  rw [nats_eq_ids, hl, h1, Verify.groupSizes_spec, USize.toNat_ofNat_of_lt' (by omega : G < USize.size),
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hW64 (Nat.lt_of_lt_of_le (by decide) USize.le_size)),
    USize.toNat_ofNat_of_lt' hn]
  refine List.map_congr_left fun h _ => ?_
  unfold Verify.idsW
  rw [Verify.idsCap_packIds _ _ hW, List.countP_map]
  refine List.countP_congr fun j hj => ?_
  have hj := List.mem_range.1 hj
  rw [Function.comp_apply, Verify.idAt_packIds hW hj (Verify.lt_two_pow_idWidthOf (by omega) (hlt j hj))]
  simp

open QLean.Kernel in
/-- **`find` of a code in the right's class firsts, at one byte layout `k`**: `join_nats`'s `hit`, each left
    element's position among the right's class firsts' elements, the class count at a miss. -/
theorem find_lane (lc rc : Alg.Code) {k : Kernel.Scan.Kind} (hk4 : k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64)
    (hr : rc.kind = some k) (hl : lc.kind = some k) (hav : rc.n ≤ k.avail rc.b) (hn : rc.n < USize.size) :
    nats ((rc.gather rc.groupIds.2).find lc) = (List.range (lc.b.size / k.width)).map fun i =>
      ((Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).map (k.bitsAt rc.b)).idxOf (k.bitsAt lc.b i) := by
  have hw0 : 0 < k.width := by rcases hk4 with rfl | rfl | rfl | rfl <;> decide
  have hw8 : k.width ≤ 8 := by rcases hk4 with rfl | rfl | rfl | rfl <;> decide
  have hwU : k.width.toUSize.toNat = k.width :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  have hbits : ∀ b i, k.bitsAt b i = Column.bitsAt b (i * k.width) k.width := fun b i => by
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hids := (groupIds_at rc hr hav hn).2
  have hgk : (rc.gather rc.groupIds.2).kind = some k := hr
  have hgb : (rc.gather rc.groupIds.2).b = gatherBytes k.width.toUSize 0 rc.b rc.groupIds.2 := by
    show (match rc.kind with
      | some .bit => gatherBits rc.n.toUSize rc.b rc.groupIds.2
      | some k => gatherBytes k.width.toUSize 0 rc.b rc.groupIds.2
      | none => gatherPacked rc.n.toUSize rc.w.toUSize rc.w.toUSize 0 rc.b rc.groupIds.2) = _
    rw [hr]; rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hf : (rc.gather rc.groupIds.2).find lc = findVec k.width.toUSize false (rc.gather rc.groupIds.2).b lc.b := by
    unfold Alg.Code.find; rw [hgk, hl]; rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hfs : ∀ f ∈ Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n, f < rc.n := fun f hf => Verify.firsts_lt _ _ hf
  have hGn := firstsOf_length_le (Kernel.Order.keyAt k rc.b) rc.n
  have hava : k.avail rc.b = rc.b.size / k.width := by rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  generalize Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n = fs at hids hfs hGn ⊢
  -- the firsts' elements
  have hay : Verify.elemsW k.width (rc.gather rc.groupIds.2).b = fs.map (k.bitsAt rc.b) := by
    have e := Verify.elemsW_gatherBytes k.width.toUSize (by rw [hwU]; exact hw0) (by rw [hwU]; exact hw8) 0 rc.b
      rc.groupIds.2
    rw [hwU] at e
    rw [hgb, e]
    have e2 : ∀ (F : Nat → UInt64), (Verify.elemsW 8 rc.groupIds.2).map (fun u => F u.toNat) = (Verify.ids rc.groupIds.2).map F :=
      fun F => by simp only [Verify.elemsW, Verify.ids, List.map_map]; rfl
    rw [e2 fun f => UInt64.ofNat (((Verify.elemsW k.width rc.b).getD f 0).toNat % 2 ^ (8 * k.width)), hids]
    refine List.map_congr_left fun f hf => ?_
    have hf' : f < rc.b.size / k.width := by have := hfs f hf; omega
    unfold Verify.elemsW
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hf', Option.map_some,
      Option.getD_some, Nat.mod_eq_of_lt (Verify.bitsAt_lt _ _ _ hw8), UInt64.ofNat_toNat, hbits]
  have hhs : (rc.gather rc.groupIds.2).b.size / k.width < USize.size := by
    have := congrArg List.length hay
    simp only [Verify.elemsW, List.length_map, List.length_range] at this
    omega
  obtain ⟨hsz, hget⟩ := Verify.findVec_idxOf k.width.toUSize false (rc.gather rc.groupIds.2).b lc.b (by rw [hwU]; exact hhs)
  rw [hwU] at hsz hget
  rw [hf]
  apply List.ext_getElem (by rw [nats_length, hsz]; simp)
  intro i h1 h2
  rw [nats_length, hsz, Nat.mul_div_cancel_left _ (by decide)] at h1
  simp only [nats, Verify.elemsW, List.getElem_map, List.getElem_range]
  rw [hget i h1, if_pos hw8, hay, hbits lc.b i]
  rw [show normalise k.width false = id from funext fun v => by simp [normalise], List.map_id, id]

/-- Below `2^k`, flipping bit `k` adds it: the sign flip of a sort key over a non-negative code. -/
theorem xor_two_pow_of_lt {a k : Nat} (h : a < 2 ^ k) : a ^^^ 2 ^ k = a + 2 ^ k := by
  have h1 := Nat.xor_div_two_pow (a := a) (b := 2 ^ k) (n := k)
  have h2 := Nat.xor_mod_two_pow (a := a) (b := 2 ^ k) (n := k)
  rw [Nat.div_eq_of_lt h, Nat.div_self (Nat.two_pow_pos k), Nat.mod_eq_of_lt h, Nat.mod_self, Nat.xor_zero,
    show (0 ^^^ 1 : Nat) = 1 from rfl] at *
  have := Nat.div_add_mod (a ^^^ 2 ^ k) (2 ^ k)
  rw [h1, h2] at this; omega

/-- **A stable sort by keys that order as the classes do is a stable sort by class**: `grade`'s answer, read
    on `n` rows whose key `key` is the class `gid` shifted by a constant. -/
theorem grade_by_class {L : List Nat} {n : Nat} (gid key : Nat → Nat) (hp : L.Perm (List.range n))
    (hs : L.Pairwise fun i j => key i ≤ key j ∧ (key j ≤ key i → i < j))
    (hk : ∀ i j, i < n → j < n → (key i ≤ key j ↔ gid i ≤ gid j)) :
    L.Pairwise fun i j => gid i ≤ gid j ∧ (gid j ≤ gid i → i < j) :=
  hs.imp_of_mem fun hi hj ⟨a, b⟩ =>
    have hi := List.mem_range.1 (hp.mem_iff.1 hi); have hj := List.mem_range.1 (hp.mem_iff.1 hj)
    ⟨(hk _ _ hi hj).1 a, fun h => b ((hk _ _ hj hi).2 h)⟩

open QLean.Kernel in
/-- **`grade` of `n` class ids packed at their lane** (`Code.ofIds`, as `Alg.join` grades the right's
    classes) is a stable sort of the rows by class, at every lane `idWidthOf G` picks: `join_nats`'s `hpn`,
    with `ej_rel_codes`'s `hp`, `hs`. -/
theorem grade_ofIds {G n : Nat} (gid : Nat → Nat) (hlt : ∀ j, j < n → gid j < G) (hG : G < 2 ^ 63)
    (hn : n < USize.size) :
    (nats (Alg.Code.ofIds G n (Column.packIds (Column.idWidthOf G) n gid)).grade).Perm (List.range n) ∧
    (nats (Alg.Code.ofIds G n (Column.packIds (Column.idWidthOf G) n gid)).grade).Pairwise
      fun i j => gid i ≤ gid j ∧ (gid j ≤ gid i → i < j) := by
  have hnU : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hW := idWidthOf_lane G
  have hb : ∀ j, j < n → gid j < 2 ^ Column.idWidthOf G :=
    fun j hj => Verify.lt_two_pow_idWidthOf (by omega) (hlt j hj)
  -- a byte-layout `grade` whose key is the class shifted by `off`
  have viaGrade : ∀ (k : Scan.Kind) (b : ByteArray) (off : Nat), n ≤ k.avail b →
      (∀ i, i < n → (Order.keyAt k b i).toNat = gid i + off) →
      (nats (Order.grade k false n.toUSize b)).Perm (List.range n) ∧
      (nats (Order.grade k false n.toUSize b)).Pairwise fun i j => gid i ≤ gid j ∧ (gid j ≤ gid i → i < j) :=
    fun k b off hav hkey => by
      obtain ⟨hp, hs⟩ := Verify.grade_spec k false n.toUSize b
      rw [hnU, Nat.min_eq_left hav, ← nats_eq_ids] at hp
      rw [← nats_eq_ids] at hs
      refine ⟨hp, grade_by_class gid (fun i => (Order.keyAt k b i).toNat) hp
        (hs.imp fun ⟨a, c⟩ => ⟨UInt64.le_iff_toNat_le.1 a, fun h => c (UInt64.le_iff_toNat_le.2 h)⟩) ?_⟩
      intro i j hi hj; dsimp only; rw [hkey i hi, hkey j hj]; omega
  -- `gradeLane` at a lane `w`, keyed by the ids themselves
  have viaLane : ∀ w, Column.idWidthOf G = w →
      (nats (Order.gradeLane false n.toUSize w.toUSize (Column.packIds w n gid))).Perm (List.range n) ∧
      (nats (Order.gradeLane false n.toUSize w.toUSize (Column.packIds w n gid))).Pairwise
        fun i j => gid i ≤ gid j ∧ (gid j ≤ gid i → i < j) := fun w hw => by
    have hw64 : w ≤ 64 := by rcases hW with h | h | h | h | h | h | h | h <;> omega
    have hwU : w.toUSize.toNat = w :=
      USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw64 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
    obtain ⟨hp, hs⟩ := Verify.gradeLane_spec false n.toUSize w.toUSize (Column.packIds w n gid)
    rw [hnU, hwU, Verify.idsCap_packIds _ _ (hw ▸ hW), ← nats_eq_ids] at hp
    rw [hwU, ← nats_eq_ids] at hs
    refine ⟨hp, grade_by_class gid (fun i => Column.idAt (Column.packIds w n gid) w i) hp
      (hs.imp fun ⟨a, c⟩ => ⟨by simpa using a, fun h => c (by simpa using h)⟩) ?_⟩
    intro i j hi hj; dsimp only
    rw [Verify.idAt_packIds (hw ▸ hW) hi (hw ▸ hb i hi), Verify.idAt_packIds (hw ▸ hW) hj (hw ▸ hb j hj)]
  -- a whole-byte lane `8c` read at the kind of width `c`
  have viaBytes : ∀ (c w : Nat) (k : Scan.Kind), 8 * c = w → 1 ≤ c → c ≤ 8 → k.avail = (fun b => b.size / c) →
      Column.idWidthOf G = w → (∀ b i, k.bitsAt b i = Column.bitsAt b (i * c) c) →
      n ≤ k.avail (Column.packIds w n gid) ∧
      ∀ i, i < n → k.bitsAt (Column.packIds w n gid) i = (gid i).toUInt64 :=
    fun c w k hcw h1 h8 hav hw hbits => by
      subst hcw
      obtain ⟨hs, hg⟩ := Verify.packIds_bytes c n gid h1 h8
      refine ⟨Nat.le_of_eq (by rw [hav]; dsimp only; rw [hs, Nat.mul_div_cancel_left _ (by omega)]), fun i hi => ?_⟩
      rw [hbits, hg i hi (hw ▸ hb i hi)]
  have hzero : ∀ k i, Column.bitAt ⟨Array.replicate k 0⟩ i = false := fun k i => by
    unfold Column.bitAt
    have hs : (⟨Array.replicate k 0⟩ : ByteArray).size = k := Array.size_replicate
    by_cases h : i / 8 < k
    · rw [getElem?_pos (⟨Array.replicate k 0⟩ : ByteArray) _ (by rw [hs]; exact h)]
      simp [ByteArray.getElem_eq_getElem_data]
    · rw [getElem?_neg (⟨Array.replicate k 0⟩ : ByteArray) _ (by rw [hs]; exact h)]; simp
  have htn : ∀ x, x < 2 ^ 64 → x.toUInt64.toNat = x := fun x hx => by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hx]
  rcases hW with hw | hw | hw | hw | hw | hw | hw | hw
  · -- no bits: every id is `0`, a bitmap of zeros
    simp (config := {decide := true}) only [Alg.Code.ofIds, Alg.Code.ofLane, hw, Alg.Code.grade, Alg.Code.kind,
      Alg.laneKind, reduceIte]
    have hsz : (⟨Array.replicate ((n + 7) / 8) 0⟩ : ByteArray).size = (n + 7) / 8 := Array.size_replicate
    refine viaGrade .bit _ 0 (by show n ≤ (⟨Array.replicate ((n + 7) / 8) 0⟩ : ByteArray).size * 8; omega)
      fun i hi => ?_
    have := hb i hi; rw [hw] at this
    show (if Column.bitAt ⟨Array.replicate ((n + 7) / 8) 0⟩ i then (1 : UInt64) else 0).toNat = _
    rw [hzero]; simp; omega
  · -- one bit: `bitAt` is the id
    simp (config := {decide := true}) only [Alg.Code.ofIds, Alg.Code.ofLane, hw, Alg.Code.grade, Alg.Code.kind,
      Alg.laneKind, reduceIte]
    have hc := Verify.idsCap_packIds (W := 1) n gid (by decide)
    unfold Column.idsCap at hc
    rw [if_neg (by decide), Nat.div_one] at hc
    refine viaGrade .bit _ 0 (by show n ≤ (Column.packIds 1 n gid).size * 8; omega) fun i hi => ?_
    have e := Verify.idAt_one (Column.packIds 1 n gid) i
    rw [Verify.idAt_packIds (by decide) hi (hw ▸ hb i hi)] at e
    show (if Column.bitAt (Column.packIds 1 n gid) i then (1 : UInt64) else 0).toNat = _
    rw [e]; split <;> rfl
  · simp (config := {decide := true}) only [Alg.Code.ofIds, Alg.Code.ofLane, hw, Alg.Code.grade, Alg.Code.kind,
      Alg.laneKind, reduceIte]
    exact viaLane 2 hw
  · simp (config := {decide := true}) only [Alg.Code.ofIds, Alg.Code.ofLane, hw, Alg.Code.grade, Alg.Code.kind,
      Alg.laneKind, reduceIte]
    exact viaLane 4 hw
  · simp (config := {decide := true}) only [Alg.Code.ofIds, Alg.Code.ofLane, hw, Alg.Code.grade, Alg.Code.kind,
      Alg.laneKind, reduceIte]
    obtain ⟨hav, hk⟩ := viaBytes 1 8 .u8 rfl (by decide) (by decide) rfl hw fun _ _ => rfl
    refine viaGrade .u8 _ 0 hav fun i hi => ?_
    show (Order.rank .u8 (Scan.Kind.bitsAt .u8 (Column.packIds 8 n gid) i)).toNat = _
    rw [hk i hi]; have := hb i hi; rw [hw] at this; exact htn _ (by omega)
  · simp (config := {decide := true}) only [Alg.Code.ofIds, Alg.Code.ofLane, hw, Alg.Code.grade, Alg.Code.kind,
      Alg.laneKind, reduceIte]
    by_cases hG16 : 32768 < G
    · simp only [hG16, decide_true, Bool.and_true, Bool.true_or, Bool.or_true, reduceIte]; exact viaLane 16 hw
    · simp only [hG16, decide_false, Bool.and_false, Bool.false_eq_true, reduceIte]
      obtain ⟨hav, hk⟩ := viaBytes 2 16 .i16 rfl (by decide) (by decide) rfl hw fun _ _ => rfl
      refine viaGrade .i16 _ (2 ^ 15) hav fun i hi => ?_
      show (Order.rank .i16 (Scan.Kind.bitsAt .i16 (Column.packIds 16 n gid) i)).toNat = _
      have := hlt i hi
      rw [hk i hi, Order.rank, UInt64.toNat_xor, htn _ (by omega), show (0x8000 : UInt64).toNat = 2 ^ 15 from rfl,
        xor_two_pow_of_lt (by omega)]
  · simp (config := {decide := true}) only [Alg.Code.ofIds, Alg.Code.ofLane, hw, Alg.Code.grade, Alg.Code.kind,
      Alg.laneKind, reduceIte]
    by_cases hG32 : 2147483648 < G
    · simp only [hG32, decide_true, Bool.and_true, Bool.true_or, Bool.or_true, reduceIte]; exact viaLane 32 hw
    · simp only [hG32, decide_false, Bool.and_false, Bool.false_eq_true, reduceIte]
      obtain ⟨hav, hk⟩ := viaBytes 4 32 .i32 rfl (by decide) (by decide) rfl hw fun _ _ => rfl
      refine viaGrade .i32 _ (2 ^ 31) hav fun i hi => ?_
      show (Order.rank .i32 (Scan.Kind.bitsAt .i32 (Column.packIds 32 n gid) i)).toNat = _
      have := hlt i hi
      rw [hk i hi, Order.rank, UInt64.toNat_xor, htn _ (by omega),
        show (0x80000000 : UInt64).toNat = 2 ^ 31 from rfl, xor_two_pow_of_lt (by omega)]
  · simp (config := {decide := true}) only [Alg.Code.ofIds, Alg.Code.ofLane, hw, Alg.Code.grade, Alg.Code.kind,
      Alg.laneKind, reduceIte]
    obtain ⟨hav, hk⟩ := viaBytes 8 64 .i64 rfl (by decide) (by decide) rfl hw fun _ _ => rfl
    refine viaGrade .i64 _ (2 ^ 63) hav fun i hi => ?_
    show (Order.rank .i64 (Scan.Kind.bitsAt .i64 (Column.packIds 64 n gid) i)).toNat = _
    have := hlt i hi
    rw [hk i hi, Order.rank, UInt64.toNat_xor, htn _ (by omega),
      show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, xor_two_pow_of_lt (by omega)]

/-- A word read as a long is the long of its natural. -/
theorem toInt64_eq_ofNat (u : UInt64) : u.toInt64 = Int64.ofNat u.toNat := by
  apply Int64.toBitVec_inj.1; simp

/-- **A relation of two dense long payloads lists their words**, as longs, zipped. -/
theorem toList_ofCols {R : Rel .long .long} {a b : ByteArray}
    (h : Alg.ofCols .long .long (Alg.longs a) (Alg.longs b) = .ok R) :
    R.toList = ((nats a).zip (nats b)).map fun p => (Int64.ofNat p.1, Int64.ofNat p.2) := by
  obtain ⟨hk, hv⟩ := Alg.ofCols_ok h
  have hkl : R.key.toList = (nats a).map Int64.ofNat := by
    rw [Arr.toList_long R.key (ws := Verify.elemsW 8 a) (by rw [hk]; rfl), nats, List.map_map]
    exact List.map_congr_left fun u _ => toInt64_eq_ofNat u
  have hvl : R.val.toList = (nats b).map Int64.ofNat := by
    rw [Arr.toList_long R.val (ws := Verify.elemsW 8 b) (by rw [hv]; rfl), nats, List.map_map]
    exact List.map_congr_left fun u _ => toInt64_eq_ofNat u
  have hz : R.toList = R.key.toList.zip R.val.toList :=
    List.ext_getElem (by
      simp only [Rel.toList, List.length_ofFn, List.length_zip]; rw [Arr.length_toList, Arr.length_toList, Nat.min_self])
      fun i h1 h2 => by
        simp only [Rel.toList, List.getElem_ofFn, List.getElem_zip]
        rw [Arr.getElem_toList, Arr.getElem_toList]
  rw [hz, hkl, hvl, List.zip_map]
  rfl

/-- **`ej` tabulates `l ≫ r°`**, the kernel itself from its codes on: `Struct.ej` answers `Alg.join` of the key
    codes (`keyCodes`), read on naturals (`join_nats`), then `ej_rel_join`. Hypotheses: the three lane kernels'
    answers on the codes `lc`, `rc` (as in `join_nats`), the grade stable by class, and the classes meeting
    exactly where the key tuples `tl`, `tr` do. -/
theorem ej_rel_codes {lk rk : Array Struct.KCol} {lc rc : Alg.Code} {R : Rel .long .long} {tl tr : List (List Int64)}
    {G : Nat} (gid hit : Nat → Nat) (perm : List Nat) (hc : Struct.keyCodes "ej" lk rk = .ok (lc, rc))
    (hn : rc.n = tr.length) (hG : Alg.len rc.groupIds.2 = G) (hgid : ∀ j, j < rc.n → gid j < G)
    (hsz : nats (Alg.classSizes rc.n rc.groupIds) =
      (List.range G).map fun h => (List.range rc.n).countP fun j => decide (gid j = h))
    (hhit : nats ((rc.gather rc.groupIds.2).find lc) = (List.range tl.length).map hit) (hhG : ∀ i, hit i ≤ G)
    (hpn : nats (Alg.Code.ofIds G rc.n rc.groupIds.1).grade = perm) (hp : perm.Perm (List.range tr.length))
    (hs : perm.Pairwise fun i j => gid i ≤ gid j ∧ (gid j ≤ gid i → i < j))
    (heq : ∀ i, i < tl.length → ∀ j, j < tr.length → (gid j = hit i ↔ tr[j]! = tl[i]!))
    (hU : tl.length * rc.n + tl.length + rc.n + G + 1 < USize.size)
    (hB : tl.length * rc.n + tl.length + rc.n + G < 2 ^ 63) (h : Struct.ej lk rk = .ok R) :
    (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ ix tl ≫ (ix tr)° ≫ graph Int64.ofNat := by
  have hj := join_nats lc rc gid hit perm hG hgid hsz hhit hhG hpn (by rw [hp.length_eq, List.length_range, hn]) hU hB
  simp only [Struct.ej, hc, bind, Except.bind] at h
  generalize Alg.join lc rc = J at h hj
  obtain ⟨li, ri⟩ := J
  dsimp only at h hj
  refine ej_rel_join gid hit perm hp hs heq ?_
  rw [toList_ofCols h, hj, List.map_flatMap, hn]
  unfold List.flatMap
  congr 1
  exact List.map_congr_left fun i _ => by rw [List.map_map]; rfl

/-- **A right row's class is a left element's `find_lane` hit exactly when their codes agree**, at one byte
    layout: `ej_rel_codes`'s `heq`, read on the codes. -/
theorem class_hit_iff {k : Kernel.Scan.Kind} (hk4 : k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64)
    (rb lb : ByteArray) {n j : Nat} (i : Nat) (hj : j < n) :
    Verify.groupOf (Kernel.Order.keyAt k rb) n j =
      ((Verify.firstsOf (Kernel.Order.keyAt k rb) n).map (k.bitsAt rb)).idxOf (k.bitsAt lb i) ↔
    k.bitsAt rb j = k.bitsAt lb i := by
  have hk5 : k = .u8 ∨ k = .c8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64 := by
    rcases hk4 with h | h | h | h <;> simp [h]
  have hbits : ∀ b i, k.bitsAt b i = Column.bitsAt b (i * k.width) k.width := fun b i => by
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hki : ∀ a c, Kernel.Order.keyAt k rb a = Kernel.Order.keyAt k rb c ↔ k.bitsAt rb a = k.bitsAt rb c :=
    fun a c => by rw [Verify.keyAt_eq_iff hk5, hbits, hbits]
  rw [List.idxOf, List.findIdx_map]
  constructor
  · intro h
    have hq : (Verify.firstsOf (Kernel.Order.keyAt k rb) n).findIdx ((· == k.bitsAt lb i) ∘ k.bitsAt rb) <
        (Verify.firstsOf (Kernel.Order.keyAt k rb) n).length := h ▸ Verify.groupOf_lt hj
    have e1 := (Verify.groupOf_eq_iff hj hq).1 h
    have e2 := List.findIdx_getElem (w := hq)
    simp only [Function.comp, beq_iff_eq] at e2
    rw [(hki _ _).1 e1, e2]
  · intro hx
    unfold Verify.groupOf
    congr 1; funext f
    simp only [Function.comp, hx.symm]
    by_cases e : k.bitsAt rb f = k.bitsAt rb j
    · simp [e, (hki f j).2 e]
    · simp [e, mt (hki f j).1 e]

/-- **`ej` tabulates `l ≫ r°`** once its key codes lie at one byte layout `k` and agree exactly where the key
    tuples `tl`, `tr` do: `ej_rel_codes` with the three lane kernels discharged (`groupIds_lane`, `find_lane`,
    `grade_ofIds`, `class_hit_iff`). -/
theorem ej_rel_lane {lk rk : Array Struct.KCol} {lc rc : Alg.Code} {R : Rel .long .long} {tl tr : List (List Int64)}
    {k : Kernel.Scan.Kind} (hk4 : k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64)
    (hc : Struct.keyCodes "ej" lk rk = .ok (lc, rc)) (hr : rc.kind = some k) (hl : lc.kind = some k)
    (hav : rc.n ≤ k.avail rc.b) (hn : rc.n = tr.length) (hnl : lc.b.size / k.width = tl.length)
    (hkey : ∀ i, i < tl.length → ∀ j, j < tr.length → (k.bitsAt rc.b j = k.bitsAt lc.b i ↔ tr[j]! = tl[i]!))
    (hU : tl.length * rc.n + tl.length + rc.n + rc.n + 1 < USize.size)
    (hB : tl.length * rc.n + tl.length + rc.n + rc.n < 2 ^ 63) (h : Struct.ej lk rk = .ok R) :
    (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ ix tl ≫ (ix tr)° ≫ graph Int64.ofNat := by
  have hnU : rc.n < USize.size := by omega
  obtain ⟨hG, hgid, hsz⟩ := groupIds_lane rc hr hav hnU
  have hhit := find_lane lc rc hk4 hr hl hav hnU
  rw [hnl] at hhit
  have hGn := firstsOf_length_le (Kernel.Order.keyAt k rc.b) rc.n
  have hids1 := (groupIds_at rc hr hav hnU).1
  obtain ⟨hp, hs⟩ := grade_ofIds (Verify.groupOf (Kernel.Order.keyAt k rc.b) rc.n) hgid (by omega) hnU
  rw [← hids1] at hp hs
  have hhG : ∀ i, ((Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).map (k.bitsAt rc.b)).idxOf (k.bitsAt lc.b i) ≤
      (Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).length := fun i => by
    have := Verify.idxOf_le_length (k.bitsAt lc.b i) ((Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).map (k.bitsAt rc.b))
    rw [List.length_map] at this; exact this
  have heq : ∀ i, i < tl.length → ∀ j, j < tr.length → (Verify.groupOf (Kernel.Order.keyAt k rc.b) rc.n j =
      ((Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).map (k.bitsAt rc.b)).idxOf (k.bitsAt lc.b i) ↔
        tr[j]! = tl[i]!) := fun i hi j hj =>
    (class_hit_iff hk4 rc.b lc.b i (by omega)).trans (hkey i hi j hj)
  have hU' : tl.length * rc.n + tl.length + rc.n + (Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).length + 1 <
      USize.size := by omega
  have hB' : tl.length * rc.n + tl.length + rc.n + (Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).length < 2 ^ 63 := by
    omega
  exact ej_rel_codes (Verify.groupOf (Kernel.Order.keyAt k rc.b) rc.n)
    (fun i => ((Verify.firstsOf (Kernel.Order.keyAt k rc.b) rc.n).map (k.bitsAt rc.b)).idxOf (k.bitsAt lc.b i))
    _ hc hn hG hgid hsz hhit hhG rfl (by rw [← hn]; exact hp) hs heq hU' hB' h

/-! ## `ij`

  `Struct.ij` keeps each left row whose first hit in the right's codes lies below the right's row count,
  paired with that hit: `findVec`, `Ew.cmp lt` against the miss, `whereBits`, a gather. -/

/-- `whereBits` on naturals: the positions below `n` whose bit is set. -/
theorem nats_whereBits (n : Nat) (hn : n < USize.size) (bits : ByteArray) :
    nats (Kernel.whereBits n.toUSize bits) = (List.range n).filter (Column.bitAt bits) := by
  obtain ⟨hs, hj⟩ := Verify.whereBits_spec n.toUSize bits
  rw [USize.toNat_ofNat_of_lt' hn] at hs hj
  apply List.ext_getElem (by rw [nats_length, hs]; omega)
  intro j _ h2
  simp only [nats, Verify.elemsW, List.getElem_map, List.getElem_range]
  exact hj j h2

/-- Bit `i` of `b < m`, `b` a dense long payload and `m` a long atom, both below `2^63`, is `b[i] < m` on
    naturals. -/
theorem bitAt_cmp_lt_va (b : ByteArray) {m n i : Nat} (hn : n < USize.size) (hi : i < n) (hm : m < 2 ^ 63)
    (hw : (Column.bitsAt b (i * 8) 8).toNat < 2 ^ 63) :
    Column.bitAt (Kernel.Ew.cmp Kernel.Ew.lt Kernel.Ew.i64 Kernel.Ew.va b (Find.one m.toUInt64) n.toUSize) i =
      decide ((Column.bitsAt b (i * 8) 8).toNat < m) := by
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  rw [(Verify.cmp_bitAt _ _ _ _ _ _).2 i (by rw [hN]; omega)]
  have hsh : Kernel.Ew.shapeIdx Kernel.Ew.va i = (i, 0) := rfl
  have hel : ∀ x j, Kernel.Ew.elem Kernel.Ew.i64 x j = Column.bitsAt x (j * 8) 8 := fun _ _ => rfl
  have hm' : m.toUInt64.toNat = m := UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hm (by decide))
  rw [hsh, hel, hel, Nat.zero_mul, Find.bitsAt_one, Find.cmpStep_lt, hN, decide_eq_true hi, Bool.true_and]
  exact decide_eq_decide.2 (by
    rw [Int64.lt_iff_toInt_lt, toInt_word rfl hw, toInt_word hm' hm]; exact Int.ofNat_lt)

/-- A list zipped with its own image is the list of pairs. -/
theorem zip_map_self {α β : Type} (g : α → β) : ∀ F : List α, F.zip (F.map g) = F.map fun x => (x, g x)
  | [] => rfl
  | x :: F => by rw [List.map_cons, List.map_cons, List.zip_cons_cons, zip_map_self g F]

/-- **The kept hits tabulate `Λ(l ≫ r°) ≫ est(≤)`**, the rows read as naturals, once `hit i` is the least right
    row whose tuple is left row `i`'s, and lies at or past `|r|` at none. -/
theorem rel_ijHits {tl tr : List (List Int64)} (hit : Nat → Nat)
    (hfirst : ∀ i, i < tl.length → ∀ j, (hit i = j ∧ j < tr.length) ↔
      ((ix tl ≫ (ix tr)°) i j ∧ ∀ z, (ix tl ≫ (ix tr)°) i z → j ≤ z)) :
    RelSet.rel (((List.range tl.length).filter fun i => hit i < tr.length).map
        fun i => (Int64.ofNat i, Int64.ofNat (hit i))) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ (Λ (ix tl ≫ (ix tr)°) ≫ est (· ≤ ·)) ≫
        graph Int64.ofNat :=
  hom_ext fun a b => by
    show (a, b) ∈ _ ↔ ∃ i, a = Int64.ofNat i ∧ ∃ j, (Λ (ix tl ≫ (ix tr)°) ≫ est (· ≤ ·)) i j ∧ b = Int64.ofNat j
    simp only [Λ_comp_est_apply, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨i, ⟨hi, hh⟩, rfl, rfl⟩
      exact ⟨i, rfl, hit i, (hfirst i hi _).1 ⟨rfl, hh⟩, rfl⟩
    · rintro ⟨i, rfl, j, hj, rfl⟩
      obtain ⟨k, hk, -⟩ := hj.1
      have hi := (List.getElem?_eq_some_iff.1 hk).1
      obtain ⟨e, hjm⟩ := (hfirst i hi j).2 hj
      exact ⟨i, ⟨hi, by rw [e]; exact hjm⟩, rfl, by rw [e]⟩

open QLean.Kernel in
/-- **`ij` tabulates `Λ(l ≫ r°) ≫ est(≤)`**: each left row with its first right row of an equal key tuple, left
    rows with none dropped, the rows read as naturals. The key codes lie at one byte layout `k` and agree exactly
    where the key tuples `tl`, `tr` do (`ej_rel_lane`'s `hkey`); `findVec_idxOf` is the first hit, `cmp_bitAt`
    and `whereBits_spec` keep the hits below `|tr|`, then `rel_ijHits`. -/
theorem ij_rel_lane {lk rk : Array Struct.KCol} {lc rc : Alg.Code} {R : Rel .long .long} {tl tr : List (List Int64)}
    {k : Kernel.Scan.Kind} (hk4 : k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64)
    (hc : Struct.keyCodes "ij" lk rk = .ok (lc, rc)) (hr : rc.kind = some k) (hl : lc.kind = some k)
    (hav : rc.n ≤ k.avail rc.b) (hn : rc.n = tr.length) (hln : lc.n = tl.length)
    (hnl : lc.b.size / k.width = tl.length)
    (hkey : ∀ i, i < tl.length → ∀ j, j < tr.length → (k.bitsAt rc.b j = k.bitsAt lc.b i ↔ tr[j]! = tl[i]!))
    (hRU : rc.b.size / k.width < USize.size) (hLU : tl.length < USize.size) (hB : rc.b.size / k.width < 2 ^ 63)
    (h : Struct.ij lk rk = .ok R) :
    (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ (Λ (ix tl ≫ (ix tr)°) ≫ est (· ≤ ·)) ≫
        graph Int64.ofNat := by
  have hw8 : k.width ≤ 8 := by rcases hk4 with rfl | rfl | rfl | rfl <;> decide
  have hwU : k.width.toUSize.toNat = k.width :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  have hbits : ∀ b i, k.bitsAt b i = Column.bitsAt b (i * k.width) k.width := fun b i => by
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hava : k.avail rc.b = rc.b.size / k.width := by rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  rw [hava] at hav
  have hf : rc.find lc = findVec k.width.toUSize false rc.b lc.b := by
    unfold Alg.Code.find; rw [hr, hl]; rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  -- `E`, the right's codes; left row `i`'s hit is its code's first position in `E`
  generalize hE : Verify.elemsW k.width rc.b = E
  have hEl : E.length = rc.b.size / k.width := by rw [← hE]; simp [Verify.elemsW]
  have hEj : ∀ j, j < E.length → E[j]? = some (k.bitsAt rc.b j) := fun j hj => by
    rw [hEl] at hj; rw [← hE, hbits]; simp [Verify.elemsW, hj]
  have hhit : nats (rc.find lc) = (List.range tl.length).map fun i => E.idxOf (k.bitsAt lc.b i) := by
    obtain ⟨hsz, hget⟩ := Verify.findVec_idxOf k.width.toUSize false rc.b lc.b (by rw [hwU]; exact hRU)
    rw [hwU] at hsz hget
    rw [hf]
    apply List.ext_getElem (by rw [nats_length, hsz]; simp [hnl])
    intro i h1 _
    rw [nats_length, hsz, Nat.mul_div_cancel_left _ (by decide)] at h1
    simp only [nats, Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [hget i h1, if_pos hw8, hE, hbits lc.b i]
    rw [show normalise k.width false = id from funext fun v => by simp [normalise], List.map_id, id]
  have hle : ∀ i, E.idxOf (k.bitsAt lc.b i) ≤ rc.b.size / k.width := fun i => hEl ▸ Verify.idxOf_le_length _ _
  have hword : ∀ i, i < tl.length → (Column.bitsAt (rc.find lc) (i * 8) 8).toNat = E.idxOf (k.bitsAt lc.b i) :=
    fun i hi => by
      have e := congrArg (·[i]?) hhit
      simp only [nats, Verify.elemsW, List.getElem?_map, List.getElem?_range hi, Option.map_some] at e
      have hs : i < (rc.find lc).size / 8 := by
        have := congrArg List.length hhit; simp only [nats_length, List.length_map, List.length_range] at this; omega
      rw [List.getElem?_range hs, Option.map_some, Option.map_some, Option.some.injEq] at e
      exact e
  simp only [Struct.ij, hc, bind, Except.bind] at h
  have hk := toList_ofCols h
  rw [nats_gather, nats_whereBits _ (by omega), hhit] at hk
  have hF : (List.range lc.n).filter (Column.bitAt (Kernel.Ew.cmp Kernel.Ew.lt Kernel.Ew.i64 Kernel.Ew.va
      (rc.find lc) (Find.one rc.n.toUInt64) lc.n.toUSize)) =
      (List.range tl.length).filter fun i => E.idxOf (k.bitsAt lc.b i) < tr.length := by
    rw [hln]
    refine List.filter_congr fun i hi => ?_
    have hi := List.mem_range.1 hi
    rw [bitAt_cmp_lt_va _ (by omega) hi (by omega) (by rw [hword i hi]; have := hle i; omega), hword i hi, hn]
  rw [hF] at hk
  have hg : ((List.range tl.length).filter fun i => E.idxOf (k.bitsAt lc.b i) < tr.length).map
      (fun j => (((List.range tl.length).map fun i => E.idxOf (k.bitsAt lc.b i))).getD j 0) =
      ((List.range tl.length).filter fun i => E.idxOf (k.bitsAt lc.b i) < tr.length).map
        fun i => E.idxOf (k.bitsAt lc.b i) :=
    List.map_congr_left fun j hj => by
      have hj := List.mem_range.1 (List.mem_filter.1 hj).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some]
  rw [hg, zip_map_self, List.map_map] at hk
  have hfirst : ∀ i, i < tl.length → ∀ j, (E.idxOf (k.bitsAt lc.b i) = j ∧ j < tr.length) ↔
      ((ix tl ≫ (ix tr)°) i j ∧ ∀ z, (ix tl ≫ (ix tr)°) i z → j ≤ z) := fun i hi j => by
    -- on right rows, `l ≫ r°` holds exactly where `E` holds left row `i`'s code
    have hT : ∀ z, (ix tl ≫ (ix tr)°) i z ↔ z < tr.length ∧ E[z]? = some (k.bitsAt lc.b i) := fun z => by
      show (∃ key, tl[i]? = some key ∧ tr[z]? = some key) ↔ _
      constructor
      · rintro ⟨key, hl', hr'⟩
        obtain ⟨hz, ez⟩ := List.getElem?_eq_some_iff.1 hr'
        obtain ⟨_, el⟩ := List.getElem?_eq_some_iff.1 hl'
        refine ⟨hz, ?_⟩
        rw [hEj z (by omega), (hkey i hi z hz).2 (by rw [getElem!_pos tr z hz, getElem!_pos tl i hi, ez, el])]
      · rintro ⟨hz, ez⟩
        rw [hEj z (by rw [hEl]; exact Nat.lt_of_lt_of_le (by rw [hn]; exact hz) hav)] at ez
        have e := (hkey i hi z hz).1 (Option.some.inj ez)
        rw [getElem!_pos tr z hz, getElem!_pos tl i hi] at e
        exact ⟨tl[i], List.getElem?_eq_getElem hi, by rw [List.getElem?_eq_getElem hz, e]⟩
    simp only [hT]
    constructor
    · rintro ⟨rfl, hj⟩
      have hmem : k.bitsAt lc.b i ∈ E := if hx : k.bitsAt lc.b i ∈ E then hx else
        absurd (List.idxOf_eq_length hx) (by omega)
      obtain ⟨e1, e2⟩ := (idxOf_least (k.bitsAt lc.b i) E _).2 ⟨hmem, rfl⟩
      exact ⟨⟨hj, e1⟩, fun z hz => e2 z hz.2⟩
    · rintro ⟨⟨hj, ej⟩, hleast⟩
      obtain ⟨-, e⟩ := (idxOf_least (k.bitsAt lc.b i) E j).1 ⟨ej, fun z ez =>
        if hz : z < tr.length then hleast z ⟨hz, ez⟩ else by omega⟩
      exact ⟨e.symm, hj⟩
  calc (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) = RelSet.rel (((List.range tl.length).filter
        fun i => E.idxOf (k.bitsAt lc.b i) < tr.length).map
          fun i => (Int64.ofNat i, Int64.ofNat (E.idxOf (k.bitsAt lc.b i)))) :=
        hom_ext fun a b => (R.holds_iff_mem_toList a b).trans (by rw [hk]; exact Iff.rfl)
    _ = _ := rel_ijHits (fun i => E.idxOf (k.bitsAt lc.b i)) hfirst

#print axioms nats_whereBits
#print axioms bitAt_cmp_lt_va
#print axioms rel_ijHits
#print axioms ij_rel_lane

#print axioms class_hit_iff
#print axioms ej_rel_lane
#print axioms expand_nats
#print axioms zip_flatMap
#print axioms join_nats
#print axioms toList_ofCols
#print axioms nats_eq_ids
#print axioms idWidthOf_lane
#print axioms groupIds_lane
#print axioms find_lane
#print axioms xor_two_pow_of_lt
#print axioms grade_by_class
#print axioms grade_ofIds
#print axioms ej_rel_codes

#print axioms nats_gather
#print axioms nats_val_sub
#print axioms nats_extract
#print axioms nats_append
#print axioms blocks_get
#print axioms blocks_cover
#print axioms scanl_add
#print axioms nats_sums
#print axioms nats_sums_range
#print axioms nats_cuts
#print axioms segs_cuts
#print axioms indexPartedP_segs
#print axioms indexPartedP_rel

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
#print axioms split_sorted
#print axioms grade_slice
#print axioms grade_slice_map
#print axioms countP_lt_sum
#print axioms join_ejSpec
#print axioms ej_rel_join
#print axioms partitionAt_eq
#print axioms binSpec_sorted
#print axioms ajSpec_sorted

end LeetQ.Rel.Verb
