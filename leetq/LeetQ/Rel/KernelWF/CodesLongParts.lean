/-
  An eight-byte integral side of several dense parts where `rangeOffsets` declines: its codes are those of
  its `raze`, grouped once and cut back, so faithful jointly across the parts and well formed.
-/
import LeetQ.Rel.KernelWF.CodesProd

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- **A long side of several dense parts, `rangeOffsets` declining both the parts and their `raze`: its
    codes are those of the `raze`, cut back.** -/
theorem codes_long_cut {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hp : 0 < p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    (hroR : rangeOffsets t (#v[raze t cs.toArray].map fun c => Arr.part c.2)
      ((#v[raze t cs.toArray].map (·.1)).foldl (fun s n => s + n.toNat) 0) = none) :
    Obj.codes (.atom t) cs = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].cut (cs.map (·.1)) := by
  obtain ⟨-, -, hg, -, -⟩ := long_facts ht
  have hne : ∀ d o ids, Column.intern (raze t cs.toArray).2.enc ≠ .enum d o ids := fun d o ids he => by
    rcases long_enc ht (raze t cs.toArray).2.wf with ⟨b, hb, -⟩ | ⟨md, pk, hb⟩ <;> simp [hb, Column.intern] at he
  obtain ⟨q, hq, hc⟩ := codes_raze_cut hg cs hp (fun k hk b he => by
    obtain ⟨b', hb'⟩ := hd k hk; rw [hb'] at he; cases he) hro hne
  obtain ⟨q', hq', hc'⟩ := codes_long_group ht (raze t cs.toArray) hroR
  rw [hc, hc', show q' = q from Option.some_inj.1 (hq'.symm.trans hq)]

/-- **A long side of several dense parts where `rangeOffsets` declines: its codes are faithful jointly
    across the parts**, the parts' summed count a `USize`. -/
theorem codes_long_parts_faithful {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    (hroR : rangeOffsets t (#v[raze t cs.toArray].map fun c => Arr.part c.2)
      ((#v[raze t cs.toArray].map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, -, -⟩ := codes_long_group_wf ht (raze t cs.toArray) hroR
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < (cs[k]'hk).1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [codes_long_cut ht cs (by omega) hd hro hroR]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    codes_long_group_faithful ht _ hroR (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom,
    Vals.row_atom, Vals.row_atom, raze_get_bytes cs hd hN hk hi, raze_get_bytes cs hd hN hl hj]

/-- **A long side of several dense parts where `rangeOffsets` declines: each part's code is well formed**,
    the parts' summed count a `USize`. -/
theorem codes_long_parts_wf {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    (hroR : rangeOffsets t (#v[raze t cs.toArray].map fun c => Arr.part c.2)
      ((#v[raze t cs.toArray].map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom t) cs)[k]'hk
    (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, hsz, hid⟩ := codes_long_group_wf ht (raze t cs.toArray) hroR
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hle := take_sum_le ((cs.map (·.1)).toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  have hc : c = ((Obj.codes (.atom t) #v[raze t cs.toArray])[0].cut (cs.map (·.1)))[k]'hk := by
    show (Obj.codes (.atom t) cs)[k] = _; rw [codes_long_cut ht cs (by omega) hd hro hroR]
  obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw hs hsz hk
  rw [hc, hwk, hnk, hck, hzk]
  refine ⟨hw, by simp, rfl, fun h8 => ⟨(hid h8).1, fun i hi => ?_⟩⟩
  rw [hik i hi]; exact (hid h8).2 _ (by omega)

#print axioms codes_long_parts_faithful
#print axioms codes_long_parts_wf

end LeetQ.Rel.Alg
