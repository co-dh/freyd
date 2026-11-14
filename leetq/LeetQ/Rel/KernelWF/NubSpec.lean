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
    (ha : (a.w = 1 ∨ a.w = 2 ∨ a.w = 4 ∨ a.w = 8 ∨ a.w = 16 ∨ a.w = 32 ∨ a.w = 64) ∧
      a.b.size = (a.n.toNat * a.w + 7) / 8 ∧ (a.w < 8 → ∀ i < a.n.toNat, Column.idAt a.b a.w i < max a.card 2))
    (hb : (b.w = 1 ∨ b.w = 2 ∨ b.w = 4 ∨ b.w = 8 ∨ b.w = 16 ∨ b.w = 32 ∨ b.w = 64) ∧
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
    ((kc).w = 1 ∨ (kc).w = 2 ∨ (kc).w = 4 ∨ (kc).w = 8 ∨ (kc).w = 16 ∨ (kc).w = 32 ∨ (kc).w = 64) ∧ (kc).n = R.n ∧
      (kc).b.size = ((kc).n.toNat * (kc).w + 7) / 8 ∧
      ((kc).w < 8 → (kc).card < USize.size ∧ ∀ i < (kc).n.toNat, Column.idAt (kc).b (kc).w i < (kc).card))
  -- the value's, the same
  (hV : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
      Column.idAt (vc).b (vc).w i = Column.idAt (vc).b (vc).w j ↔ Vals.row R.val ⟨i, hi⟩ = Vals.row R.val ⟨j, hj⟩) ∧
    ((vc).w = 1 ∨ (vc).w = 2 ∨ (vc).w = 4 ∨ (vc).w = 8 ∨ (vc).w = 16 ∨ (vc).w = 32 ∨ (vc).w = 64) ∧ (vc).n = R.n ∧
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
    each side under `Vals.PickFits` at those rows (outright at atoms and products: `pickFits_atom`). -/
theorem nub_row (hk : Vals.PickFits k R.key (ids nubI)) (hv : Vals.PickFits v R.val (ids nubI)) :
    R.nub.n.toNat = (ids nubI).length ∧ ∀ t (ht : t < R.nub.n.toNat), ∃ (hI : t < (ids nubI).length)
      (hp : (ids nubI)[t]'hI < R.n.toNat), R.nub.key.row ⟨t, ht⟩ = R.key.row ⟨_, hp⟩ ∧
        R.nub.val.row ⟨t, ht⟩ = R.val.row ⟨_, hp⟩ := by
  have hnub : R.nub = R.rows nubI := rfl
  have hlen : (ids nubI).length ≤ R.n.toNat := by
    rw [nub_ids R hK hV]; simpa [firstsOf] using List.length_filter_le _ (List.range R.n.toNat)
  have hl : len nubI < USize.size := by rw [len_eq_ids]; exact Nat.lt_of_le_of_lt hlen R.n.toNat_lt_size
  obtain ⟨hn, hrow⟩ := rows_spec R _ hl hk hv
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

end Nub

#print axioms nub_mem
#print axioms nub_row

end LeetQ.Rel.Alg

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg Freyd Freyd.Alg.RelSet
open Alg.NubN

/-- **`rep (nub R) = rep R`**: `rep` reads a relation as the set of its pairs, so dropping repeated rows
    changes nothing. Hypotheses: `nub_row`'s. -/
theorem rep_nub {k v : Obj} (R : Rel k v)
    (hK : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
        Column.idAt (kc).b (kc).w i = Column.idAt (kc).b (kc).w j ↔ Vals.row R.key ⟨i, hi⟩ = Vals.row R.key ⟨j, hj⟩) ∧
      ((kc).w = 1 ∨ (kc).w = 2 ∨ (kc).w = 4 ∨ (kc).w = 8 ∨ (kc).w = 16 ∨ (kc).w = 32 ∨ (kc).w = 64) ∧ (kc).n = R.n ∧
        (kc).b.size = ((kc).n.toNat * (kc).w + 7) / 8 ∧
        ((kc).w < 8 → (kc).card < USize.size ∧ ∀ i < (kc).n.toNat, Column.idAt (kc).b (kc).w i < (kc).card))
    (hV : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
        Column.idAt (vc).b (vc).w i = Column.idAt (vc).b (vc).w j ↔ Vals.row R.val ⟨i, hi⟩ = Vals.row R.val ⟨j, hj⟩) ∧
      ((vc).w = 1 ∨ (vc).w = 2 ∨ (vc).w = 4 ∨ (vc).w = 8 ∨ (vc).w = 16 ∨ (vc).w = 32 ∨ (vc).w = 64) ∧ (vc).n = R.n ∧
        (vc).b.size = ((vc).n.toNat * (vc).w + 7) / 8 ∧
        ((vc).w < 8 → (vc).card < USize.size ∧ ∀ i < (vc).n.toNat, Column.idAt (vc).b (vc).w i < (vc).card))
    (hk : Vals.PickFits k R.key (ids nubI)) (hv : Vals.PickFits v R.val (ids nubI)) :
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

/-- `rep_nub` at atom sides: `nub` picks rows of `R` only (`nub_mem`), so both sides fit (`pickFits_atom`). -/
theorem rep_nub_atoms {t t' : QAtomicType} (R : Rel (.atom t) (.atom t'))
    (hK : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
        Column.idAt (kc).b (kc).w i = Column.idAt (kc).b (kc).w j ↔ Vals.row R.key ⟨i, hi⟩ = Vals.row R.key ⟨j, hj⟩) ∧
      ((kc).w = 1 ∨ (kc).w = 2 ∨ (kc).w = 4 ∨ (kc).w = 8 ∨ (kc).w = 16 ∨ (kc).w = 32 ∨ (kc).w = 64) ∧ (kc).n = R.n ∧
        (kc).b.size = ((kc).n.toNat * (kc).w + 7) / 8 ∧
        ((kc).w < 8 → (kc).card < USize.size ∧ ∀ i < (kc).n.toNat, Column.idAt (kc).b (kc).w i < (kc).card))
    (hV : (∀ {i j : Nat} (hi : i < R.n.toNat) (hj : j < R.n.toNat),
        Column.idAt (vc).b (vc).w i = Column.idAt (vc).b (vc).w j ↔ Vals.row R.val ⟨i, hi⟩ = Vals.row R.val ⟨j, hj⟩) ∧
      ((vc).w = 1 ∨ (vc).w = 2 ∨ (vc).w = 4 ∨ (vc).w = 8 ∨ (vc).w = 16 ∨ (vc).w = 32 ∨ (vc).w = 64) ∧ (vc).n = R.n ∧
        (vc).b.size = ((vc).n.toNat * (vc).w + 7) / 8 ∧
        ((vc).w < 8 → (vc).card < USize.size ∧ ∀ i < (vc).n.toNat, Column.idAt (vc).b (vc).w i < (vc).card))
    : rep R.nub = rep R :=
  rep_nub R hK hV (pickFits_atom R.key fun _ hp => ((nub_mem R hK hV).1 hp).1)
    (pickFits_atom R.val fun _ hp => ((nub_mem R hK hV).1 hp).1)

/-- `rep_nub` at boolean sides (`codes_boolean_faithful`/`_wf`). -/
theorem rep_nub_boolean (R : Rel (.atom .boolean) (.atom .boolean)) : rep R.nub = rep R :=
  rep_nub_atoms R ⟨fun hi hj => codes_boolean_faithful _ (k := 0) (l := 0) (by decide) (by decide) hi hj,
      by have h := codes_boolean_wf (#v[⟨R.n, R.key⟩] : Vector (Part _) 1) (k := 0) (by decide)
         exact ⟨Or.inl h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩
    ⟨fun hi hj => codes_boolean_faithful _ (k := 0) (l := 0) (by decide) (by decide) hi hj,
      by have h := codes_boolean_wf (#v[⟨R.n, R.val⟩] : Vector (Part _) 1) (k := 0) (by decide)
         exact ⟨Or.inl h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩

/-- `rep_nub` at small integral sides (`byte`, `char`, `short`, the four-byte types;
    `codes_small_int_faithful`/`_wf`). -/
theorem rep_nub_small_int {t t' : QAtomicType} {k₀ k₁ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32) (ht' : orderKind t' = some k₁) (hk₁ : k₁ = .u8 ∨ k₁ = .i16 ∨ k₁ = .i32)
    (R : Rel (.atom t) (.atom t')) : rep R.nub = rep R :=
  rep_nub_atoms R ⟨fun hi hj => codes_small_int_faithful ht hk₀ _ hi hj, codes_small_int_wf ht hk₀ _⟩
    ⟨fun hi hj => codes_small_int_faithful ht' hk₁ _ hi hj, codes_small_int_wf ht' hk₁ _⟩

/-- `rep_nub` at eight-byte integral sides (`codes_long_one_faithful`/`_wf`). -/
theorem rep_nub_long {t t' : QAtomicType} (ht : orderKind t = some .i64) (ht' : orderKind t' = some .i64)
    (R : Rel (.atom t) (.atom t')) : rep R.nub = rep R :=
  rep_nub_atoms R ⟨fun hi hj => codes_long_one_faithful ht _ hi hj, codes_long_one_wf ht _⟩
    ⟨fun hi hj => codes_long_one_faithful ht' _ hi hj, codes_long_one_wf ht' _⟩

/-- `rep_nub` at `guid` sides (`codes_guid_faithful`/`_wf`). -/
theorem rep_nub_guid (R : Rel (.atom .guid) (.atom .guid)) : rep R.nub = rep R :=
  rep_nub_atoms R ⟨fun hi hj => codes_guid_faithful _ hi hj, codes_guid_wf _⟩
    ⟨fun hi hj => codes_guid_faithful _ hi hj, codes_guid_wf _⟩

#print axioms rep_nub_boolean
#print axioms rep_nub_small_int
#print axioms rep_nub_long
#print axioms rep_nub_guid

end LeetQ.Rel.Rep
