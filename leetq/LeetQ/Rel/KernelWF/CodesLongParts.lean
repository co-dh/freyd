/-
  An eight-byte integral side of several parts, dense or `foR`, where `rangeOffsets` declines: its codes are
  the grouping code of its `raze`, cut back, so faithful jointly across the parts and well formed.
-/
import LeetQ.Rel.KernelWF.CodesProd

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- `one v`'s only word is `v`. -/
theorem elem_one (v : UInt64) : Ew.elem Ew.i64 (one v) 0 = v := elem_atomBytes_i64 v

/-- **A long side of several parts in any encoding, `rangeOffsets` declining the parts: its codes are the
    grouping code of the `raze`, cut back.** -/
theorem codes_long_cut {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hp : 0 < p)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none) :
    ∃ q, groupIdsColumn t (raze t cs.toArray).1 (raze t cs.toArray).2.enc = some q ∧
      Obj.codes (.atom t) cs = (Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).cut (cs.map (·.1)) := by
  obtain ⟨-, -, hg, -, -⟩ := long_facts ht
  have hne : ∀ d o ids, Column.intern (raze t cs.toArray).2.enc ≠ .enum d o ids := fun d o ids he => by
    rcases long_enc ht (raze t cs.toArray).2.wf with ⟨b, hb, -⟩ | ⟨md, pk, hb⟩ <;> simp [hb, Column.intern] at he
  obtain ⟨q, hq, hc⟩ := codes_raze_cut hg cs hp (fun k hk b he => by
    rcases long_enc ht (cs[k]'hk).2.wf with ⟨b', hb', -⟩ | ⟨md, pk, hb'⟩ <;> rw [hb'] at he <;> cases he) hro hne
  have hbt : KernelWF.bitsType t = t := by cases t <;> simp [orderKind] at ht <;> rfl
  rw [hbt] at hq
  exact ⟨q, hq, hc⟩

/-- **A long side of several parts where `rangeOffsets` declines: its codes are faithful jointly across the
    parts**, the parts in any encoding, `razeColumn` joining them dense (`hD`), their summed count a `USize`. -/
theorem codes_long_parts_faithful {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p)
    (hD : ∀ w r, t.width = some w → encodedParts t (cs.toArray.map (·.2.part)) = some r →
      denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = true)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  have hW : t.width = some 8 := by cases t <;> simp [orderKind] at ht <;> rfl
  have hB : t ≠ .boolean := by rintro rfl; simp [orderKind] at ht
  have hX := raze_len t cs.toArray hN
  obtain ⟨q, hq, hc⟩ := codes_long_cut ht cs (by omega) hro
  obtain ⟨hw, hn, -, -⟩ := ofIds_long_wf ht (raze t cs.toArray) hq
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < (cs[k]'hk).1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [hc]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    ofIds_long_faithful ht _ hq (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom,
    Vals.row_atom, Vals.row_atom, raze_get_bytes hW hB cs (fun r hr => hD 8 r hW hr) hN hk hi,
    raze_get_bytes hW hB cs (fun r hr => hD 8 r hW hr) hN hl hj]

/-- **A long side of several parts, in any encoding, where `rangeOffsets` declines: each part's code is well
    formed**, the parts' summed count a `USize`. -/
theorem codes_long_parts_wf {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom t) cs)[k]'hk
    laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  have hX := raze_len t cs.toArray hN
  obtain ⟨q, hq, hcq⟩ := codes_long_cut ht cs (by omega) hro
  obtain ⟨hw, hn, hsz, hid⟩ := ofIds_long_wf ht (raze t cs.toArray) hq
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hle := take_sum_le ((cs.map (·.1)).toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  have hc : c = ((Code.ofIds (len q.2) (raze t cs.toArray).1 q.1).cut (cs.map (·.1)))[k]'hk := by
    show (Obj.codes (.atom t) cs)[k] = _; rw [hcq]
  obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw hs hsz hk
  rw [hc, hwk, hnk, hck, hzk]
  refine ⟨hw, by simp, rfl, fun h8 => ⟨(hid h8).1, fun i hi => ?_⟩⟩
  rw [hik i hi]; exact (hid h8).2 _ (by omega)

/-! ## Long parts, whichever branch `rangeOffsets` takes -/

/-- **A long side of several parts: its codes are faithful jointly across the parts**, `rangeOffsets`
    answering (`codes_long_faithful`) or declining; the parts in any encoding, `razeColumn` joining them dense
    (`hD`, vacuous where every part is dense), their summed count a `USize`. -/
theorem codes_long_dense_faithful {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p)
    (hD : ∀ w r, t.width = some w → encodedParts t (cs.toArray.map (·.2.part)) = some r →
      denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = true)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  cases hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) with
  | none => exact codes_long_parts_faithful ht cs hD hN hro hk hl hi hj
  | some os => exact codes_long_faithful ht cs hro hk hl hi hj

/-- **A long side of several parts, in any encoding: each part's code is well formed**, whichever branch
    `rangeOffsets` takes; the parts' summed count a `USize`. -/
theorem codes_long_dense_wf {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom t) cs)[k]'hk
    laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  cases hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) with
  | none => exact codes_long_parts_wf ht cs hN hro hk
  | some os => exact codes_long_wf ht cs hro hk

#print axioms codes_long_dense_faithful
#print axioms codes_long_dense_wf

end LeetQ.Rel.Alg
