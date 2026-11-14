/-
  `Rel.rows` and `Rel.nub` read back. `rows R i` is `R`'s rows at the positions `i` names (`pick_row`);
  `nub R` is `rows` at the first row of each class of `|R|` (`tuples.tupleIds` of the key's and the value's
  codes), so it keeps the first occurrence of each pair and no other, and `rep R.nub = rep R`.

  Every index in a statement here carries its bound explicitly (`xs[k]'hk`).
-/
import LeetQ.Rel.Rep
import LeetQ.Rel.KernelWF.PickRow
import LeetQ.Rel.KernelWF.MemberSpec
import LeetQ.Rel.KernelWF.CodesProd
import LeetQ.Rel.KernelWF.CodesSpec
import LeetQ.Rel.KernelWF.CodesFloatParts

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-! ## First occurrences -/

/-- `firstsOf` reads only which positions below `m` agree: two keys agreeing on the same pairs pick the
    same first positions. -/
theorem firstsOf_congr {α β : Type} [DecidableEq α] [DecidableEq β] {g : Nat → α} {g' : Nat → β} {m : Nat}
    (h : ∀ i < m, ∀ j < m, (g i = g j ↔ g' i = g' j)) : firstsOf g m = firstsOf g' m := by
  unfold firstsOf
  refine List.filter_congr fun i hi => ?_
  have hi := List.mem_range.1 hi
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not]
  exact forall_congr' fun j => imp_congr_right fun hj => not_congr (h j (by omega) i hi)

/-- **A first position**: below `m`, and no earlier position has its key. -/
theorem mem_firstsOf_iff {α : Type} [DecidableEq α] {g : Nat → α} {m p : Nat} :
    p ∈ firstsOf g m ↔ p < m ∧ ∀ q < p, g q ≠ g p := by
  unfold firstsOf
  simp only [List.mem_filter, List.mem_range, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]

/-- **The first rows `tupleIds` answers for two columns are the first positions of their pairs of codes**:
    `a`, `b` well formed of one count, codes below a byte under their bound (`pairCode_spec`). -/
theorem tupleIds_firsts (a b : Code) (hn : b.n = a.n)
    (ha : laneOK(a.w) ∧
      a.b.size = (a.n.toNat * a.w + 7) / 8 ∧ (a.w < 8 → ∀ i < a.n.toNat, Column.idAt a.b a.w i < max a.card 2))
    (hb : laneOK(b.w) ∧
      b.b.size = (b.n.toNat * b.w + 7) / 8 ∧ (b.w < 8 → ∀ i < b.n.toNat, Column.idAt b.b b.w i < max b.card 2)) :
    ids (tuples.tupleIds a #[b]).2 = firstsOf (fun i => (Column.idAt a.b a.w i, Column.idAt b.b b.w i)) a.n.toNat := by
  have e : tuples.tupleIds a #[b] = match pairCode true a b with | (_, some r) => r | (c, none) => c.groupIds := rfl
  rw [e]
  rcases hp : pairCode true a b with ⟨c, _ | r⟩
  · have h := pairCode_spec true a b hn ha hb
    simp only [hp] at h
    obtain ⟨⟨hw, hcn, hs, hcd⟩, hiff⟩ := h
    dsimp only
    rw [groupIds_firsts c hw hs hcd, hcn]
    exact firstsOf_congr fun i hi j hj => (hiff i hi j hj).trans (Prod.mk.injEq _ _ _ _).symm.to_iff
  · obtain ⟨key, hkey, hr, -⟩ := pairCode_grouped_key true a b hn ⟨ha.1, ha.2.1⟩ ⟨hb.1, hb.2.1⟩ (by rw [hp])
    dsimp only
    have hbq : ∀ x y : UInt64 × UInt64, (x == y) = decide (x = y) := fun x y =>
      Bool.eq_iff_iff.2 (by rw [beq_iff_eq, decide_eq_true_iff])
    have hF : Order.firstsBy a.n.toNat key = firstsOf key a.n.toNat := by
      simp only [Order.firstsBy, firstsOf, bne, hbq]
    have hlt : ∀ i ∈ Order.firstsBy a.n.toNat key, i < 2 ^ 64 := fun i hi =>
      Nat.lt_trans (List.mem_range.1 (List.mem_filter.1 hi).1) (Verify.usize_lt a.n)
    rw [hr, show (Order.idsBy a.n.toNat key).2 = Order.indices (Order.firstsBy a.n.toNat key) from rfl,
      ids_indices _ hlt, hF]
    exact firstsOf_congr fun i hi j hj => (hkey i hi j hj).trans (Prod.mk.injEq _ _ _ _).symm.to_iff

#print axioms tupleIds_firsts

/-! ## `Rel.rows` -/

/-- **`Rel.rows R i` lists `R`'s rows by position**: `len i` rows, row `q` `R`'s row `i[q]`, or the
    default pair where `i[q]` is past `R`'s count; each side under `Vals.PickFits` at the rows `i` names. -/
theorem rows_spec {k v : Obj} (R : Rel k v) (i : ByteArray) (hl : len i < USize.size)
    (hk : Vals.PickFits k R.key (ids i)) (hv : Vals.PickFits v R.val (ids i)) :
    (R.rows i).n.toNat = len i ∧ ∀ q (hq : q < (R.rows i).n.toNat),
      ((R.rows i).key.row ⟨q, hq⟩, (R.rows i).val.row ⟨q, hq⟩) =
        if h : (Column.bitsAt i (q * 8) 8).toNat < R.n.toNat then (R.key.row ⟨_, h⟩, R.val.row ⟨_, h⟩)
        else (k.dflt, v.dflt) := by
  unfold Rel.rows need
  rw [dif_pos hl]
  have hm : (len i).toUSize.toNat = len i := USize.toNat_ofNat_of_lt' hl
  have e : ((List.range (len i).toUSize.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat) = ids i := by
    rw [hm]; rfl
  refine ⟨hm, fun q hq => ?_⟩
  dsimp only at hq ⊢
  rw [pick_row k R.key i _ _ (e ▸ hk) ⟨q, hq⟩, pick_row v R.val i _ _ (e ▸ hv) ⟨q, hq⟩]
  by_cases h : (Column.bitsAt i (q * 8) 8).toNat < R.n.toNat <;> simp only [h, ↓reduceDIte]

#print axioms rows_spec

/-! ## `Rel.nub` -/

-- the key's and the value's codes, one part each, and the first rows `nub` picks, named as `nub` names them
namespace NubN
set_option hygiene false in
scoped notation "kc" => (Obj.codes _ (#v[⟨R.n, R.key⟩] : Vector (Part _) 1))[0]
set_option hygiene false in
scoped notation "vc" => (Obj.codes _ (#v[⟨R.n, R.val⟩] : Vector (Part _) 1))[0]
set_option hygiene false in
scoped notation "nubI" => (tuples.tupleIds kc #[vc]).2
end NubN
open NubN

section Nub

variable {k v : Obj} (R : Rel k v)
  -- the key's codes identify its rows and are well formed — what `CodesSpec` concludes of one part
  (hK : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
      Column.idAt (kc).b (kc).w i = Column.idAt (kc).b (kc).w j ↔ Vals.row R.key ⟨i, hi⟩ = Vals.row R.key ⟨j, hj⟩) ∧
    laneOK((kc).w) ∧ (kc).n = R.n ∧
      (kc).b.size = ((kc).n.toNat * (kc).w + 7) / 8 ∧
      ((kc).w < 8 → (kc).card < USize.size ∧ ∀ i < (kc).n.toNat, Column.idAt (kc).b (kc).w i < (kc).card))
  -- the value's, the same
  (hV : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
      Column.idAt (vc).b (vc).w i = Column.idAt (vc).b (vc).w j ↔ Vals.row R.val ⟨i, hi⟩ = Vals.row R.val ⟨j, hj⟩) ∧
    laneOK((vc).w) ∧ (vc).n = R.n ∧
      (vc).b.size = ((vc).n.toNat * (vc).w + 7) / 8 ∧
      ((vc).w < 8 → (vc).card < USize.size ∧ ∀ i < (vc).n.toNat, Column.idAt (vc).b (vc).w i < (vc).card))

include hK hV in
/-- **`nub` picks the first occurrences**: its rows are the positions `p` of `R`, ascending, with no earlier
    row holding the same pair. -/
theorem nub_ids : ids nubI = firstsOf (fun i => (Column.idAt (kc).b (kc).w i, Column.idAt (vc).b (vc).w i)) R.n.toNat := by
  rw [tupleIds_firsts kc vc (hV.2.2.1.trans hK.2.2.1.symm) ⟨hK.2.1, hK.2.2.2.1,
    fun h i hi => Nat.lt_of_lt_of_le ((hK.2.2.2.2 h).2 i hi) (Nat.le_max_left _ _)⟩
    ⟨hV.2.1, hV.2.2.2.1, fun h i hi => Nat.lt_of_lt_of_le ((hV.2.2.2.2 h).2 i hi) (Nat.le_max_left _ _)⟩, hK.2.2.1]

include hK hV in
/-- **`nub` keeps the first occurrence of each pair and no other**: `p` is a row `nub` picks exactly when
    it is a row of `R` and no earlier row holds the same key and value. -/
theorem nub_mem {p : Nat} : p ∈ ids nubI ↔ ∃ hp : p < R.n.toNat, ∀ q (hq : q < p),
    ¬(Vals.row R.key ⟨q, Nat.lt_trans hq hp⟩ = Vals.row R.key ⟨p, hp⟩ ∧
      Vals.row R.val ⟨q, Nat.lt_trans hq hp⟩ = Vals.row R.val ⟨p, hp⟩) := by
  rw [nub_ids R hK hV, mem_firstsOf_iff]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun q hq e => h q hq (by
      rw [Prod.mk.injEq, hK.1 (Nat.lt_trans hq hp) hp, hV.1 (Nat.lt_trans hq hp) hp]; exact e)⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun q hq e => h q hq (by
      rw [Prod.mk.injEq, hK.1 (Nat.lt_trans hq hp) hp, hV.1 (Nat.lt_trans hq hp) hp] at e; exact e)⟩

include hK hV in
/-- **`nub`'s rows, in order**: as many as the first occurrences, row `t` `R`'s row at the `t`-th of them;
    each side under `Vals.PickFits` at all its rows, so at the picks, a sublist of them (`pickFits_sublist`). -/
theorem nub_row (hk : Vals.PickFits k R.key (List.range R.n.toNat)) (hv : Vals.PickFits v R.val (List.range R.n.toNat)) :
    R.nub.n.toNat = (ids nubI).length ∧ ∀ t (ht : t < R.nub.n.toNat), ∃ (hI : t < (ids nubI).length)
      (hp : (ids nubI)[t]'hI < R.n.toNat), R.nub.key.row ⟨t, ht⟩ = R.key.row ⟨_, hp⟩ ∧
        R.nub.val.row ⟨t, ht⟩ = R.val.row ⟨_, hp⟩ := by
  have hnub : R.nub = R.rows nubI := rfl
  have hlen : (ids nubI).length ≤ R.n.toNat := by
    rw [nub_ids R hK hV]; simpa [firstsOf] using List.length_filter_le _ (List.range R.n.toNat)
  have hl : len nubI < USize.size := by rw [len_eq_ids]; exact Nat.lt_of_le_of_lt hlen R.n.toNat_lt_size
  have hsub : (ids nubI).Sublist (List.range R.n.toNat) := by rw [nub_ids R hK hV]; exact List.filter_sublist
  obtain ⟨hn, hrow⟩ := rows_spec R _ hl (pickFits_sublist hsub hk) (pickFits_sublist hsub hv)
  rw [len_eq_ids] at hn
  rw [hnub]
  refine ⟨hn, fun t ht => ?_⟩
  have hI : t < (ids nubI).length := hn ▸ ht
  have hget : (ids nubI)[t]'hI = (Column.bitsAt nubI (t * 8) 8).toNat := by simp [ids]
  have hp : (ids nubI)[t]'hI < R.n.toNat := ((nub_mem R hK hV).1 (List.getElem_mem hI)).1
  have e := hrow t ht
  rw [dif_pos (hget ▸ hp), Prod.mk.injEq] at e
  exact ⟨hI, hp, e.1.trans (congrArg R.key.row (Fin.ext hget.symm)),
    e.2.trans (congrArg R.val.row (Fin.ext hget.symm))⟩

include hK hV in
/-- **`nub` fits at all its rows where `R` does**: `nub` picks `R` at its first occurrences, a sublist of `R`'s
    rows, each a hit (`pickFits_pick`). -/
theorem nub_pickFits (hk : Vals.PickFits k R.key (List.range R.n.toNat))
    (hv : Vals.PickFits v R.val (List.range R.n.toNat)) :
    Vals.PickFits k R.nub.key (List.range R.nub.n.toNat) ∧ Vals.PickFits v R.nub.val (List.range R.nub.n.toNat) := by
  have hlen : (ids nubI).length ≤ R.n.toNat := by
    rw [nub_ids R hK hV]; simpa [firstsOf] using List.length_filter_le _ (List.range R.n.toNat)
  have hl : len nubI < USize.size := by rw [len_eq_ids]; exact Nat.lt_of_le_of_lt hlen R.n.toNat_lt_size
  have hsub : (ids nubI).Sublist (List.range R.n.toNat) := by rw [nub_ids R hK hV]; exact List.filter_sublist
  have hnub : R.nub = R.rows nubI := rfl
  rw [hnub]
  unfold Rel.rows need
  rw [dif_pos hl]
  have hm : (len nubI).toUSize.toNat = len nubI := USize.toNat_ofNat_of_lt' hl
  have e : ((List.range (len nubI).toUSize.toNat).map fun q => (Column.bitsAt nubI (q * 8) 8).toNat) = ids nubI := by
    rw [hm]; rfl
  have hq : ∀ q ∈ List.range (len nubI).toUSize.toNat, q < (len nubI).toUSize.toNat := fun _ h => List.mem_range.1 h
  exact ⟨pickFits_pick k R.key nubI _ _ _ hq (e ▸ pickFits_sublist hsub hk) (e ▸ pickFits_sublist hsub hk),
    pickFits_pick v R.val nubI _ _ _ hq (e ▸ pickFits_sublist hsub hv) (e ▸ pickFits_sublist hsub hv)⟩

end Nub

#print axioms nub_mem
#print axioms nub_row

end LeetQ.Rel.Alg

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg Freyd Freyd.Alg.RelSet
open Alg.NubN

/-- **`rep (nub R) = rep R`**: `rep` reads a relation as the set of its pairs, so dropping repeated rows
    changes nothing. Hypotheses: `nub_row`'s; under `CodesFit` at each side, `hK`, `hV` are `one_ok`'s. -/
theorem rep_nub {k v : Obj} (R : Rel k v)
    (hK : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
        Column.idAt (kc).b (kc).w i = Column.idAt (kc).b (kc).w j ↔ Vals.row R.key ⟨i, hi⟩ = Vals.row R.key ⟨j, hj⟩) ∧
      laneOK((kc).w) ∧ (kc).n = R.n ∧
        (kc).b.size = ((kc).n.toNat * (kc).w + 7) / 8 ∧
        ((kc).w < 8 → (kc).card < USize.size ∧ ∀ i < (kc).n.toNat, Column.idAt (kc).b (kc).w i < (kc).card))
    (hV : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
        Column.idAt (vc).b (vc).w i = Column.idAt (vc).b (vc).w j ↔ Vals.row R.val ⟨i, hi⟩ = Vals.row R.val ⟨j, hj⟩) ∧
      laneOK((vc).w) ∧ (vc).n = R.n ∧
        (vc).b.size = ((vc).n.toNat * (vc).w + 7) / 8 ∧
        ((vc).w < 8 → (vc).card < USize.size ∧ ∀ i < (vc).n.toNat, Column.idAt (vc).b (vc).w i < (vc).card))
    (hk : Vals.PickFits k R.key (List.range R.n.toNat)) (hv : Vals.PickFits v R.val (List.range R.n.toNat)) :
    rep R.nub = rep R := by
  obtain ⟨hn, hrow⟩ := nub_row R hK hV hk hv
  refine hom_ext fun a c => ?_
  show R.nub.Holds a c ↔ R.Holds a c
  simp only [Rel.Holds]
  constructor
  · rintro ⟨t, hta, htc⟩
    obtain ⟨hI, hp, e1, e2⟩ := hrow t.1 t.2
    exact ⟨⟨_, hp⟩, e1 ▸ hta, e2 ▸ htc⟩
  · rintro ⟨q, hqa, hqc⟩
    obtain ⟨f, hf, hfq⟩ := exists_first (g := fun i => (Column.idAt (kc).b (kc).w i, Column.idAt (vc).b (vc).w i)) q.2
    rw [← nub_ids R hK hV] at hf
    obtain ⟨t, hI, rfl⟩ := List.getElem_of_mem hf
    obtain ⟨_, hp, e1, e2⟩ := hrow t (hn ▸ hI)
    rw [Prod.mk.injEq] at hfq
    refine ⟨⟨t, hn ▸ hI⟩, ?_, ?_⟩
    · rw [e1, ← hqa]; exact (hK.1 hp q.2).1 hfq.1
    · rw [e2, ← hqc]; exact (hV.1 hp q.2).1 hfq.2

#print axioms rep_nub

end LeetQ.Rel.Rep
