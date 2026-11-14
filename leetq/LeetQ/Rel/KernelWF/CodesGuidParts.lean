/-
  The joint codes of a `guid` side of several parts: `codes` groups the `raze` of the parts by each row's sixteen
  bytes (`groupIdsColumn_guid`) and cuts the code back into the parts (`Code.cut`), so part `k`'s code at `i` is
  the razed column's at `O_k + i`, and that row is part `k`'s row `i` (`raze_get_bytes`).
-/
import LeetQ.Rel.KernelWF.CodesProd

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- **A `guid` side of several parts: its codes are those of its `raze`, cut back** — `guid` is dense, so
    neither a bitmap, nor `rangeOffsets`' long order, nor interned. -/
theorem codes_guid_cut {p : Nat} (cs : Vector (Part (.atom .guid)) p) (hp : 0 < p) :
    Obj.codes (.atom .guid) cs =
      ((Obj.codes (.atom .guid) #v[raze .guid cs.toArray])[0]'Nat.zero_lt_one).cut (cs.map (·.1)) := by
  have hne : ∀ d o ids, Column.intern (raze .guid cs.toArray).2.enc ≠ .enum d o ids := fun d o ids he => by
    obtain ⟨b, hb, -⟩ := guid_enc (raze .guid cs.toArray).2.wf; simp [hb, Column.intern] at he
  obtain ⟨q, hq, hc⟩ := codes_raze_cut (by decide) cs hp
    (fun k hk b he => by obtain ⟨b', hb', -⟩ := guid_enc cs[k].2.wf; rw [hb'] at he; cases he)
    (by unfold rangeOffsets; simp [orderKind]) hne
  obtain ⟨q', hq', hc'⟩ := codes_guid (raze .guid cs.toArray)
  rw [hc, hc', show q' = q from Option.some_inj.1 (hq'.symm.trans hq)]

/-- **A `guid` side of several parts: its codes are faithful jointly across the parts**, the parts' summed count
    a `USize`. -/
theorem codes_guid_parts_faithful {p : Nat} (cs : Vector (Part (.atom .guid)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom .guid) cs)[k]'hk).b ((Obj.codes (.atom .guid) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom .guid) cs)[l]'hl).b ((Obj.codes (.atom .guid) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  have hd : ∀ k (hk : k < p), ∃ b, cs[k].2.enc = .bytes b := fun k _ =>
    let ⟨b, hb, _⟩ := guid_enc cs[k].2.wf; ⟨b, hb⟩
  have hE := encodedParts_parts_bytes (t := .guid) cs hd
  have hX := raze_len .guid cs.toArray hN
  obtain ⟨hw, hn, -, -⟩ := codes_guid_wf (raze .guid cs.toArray)
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom .guid) #v[raze .guid cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < cs[k].1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze .guid cs.toArray).1.toNat := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [codes_guid_cut cs (by omega)]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    codes_guid_faithful _ (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom, Vals.row_atom,
    Vals.row_atom, raze_get_bytes (w := 16) rfl (by decide) cs (fun r hr => by rw [hE] at hr; cases hr) hN hk hi,
    raze_get_bytes (w := 16) rfl (by decide) cs (fun r hr => by rw [hE] at hr; cases hr) hN hl hj]

/-- **A `guid` side of several parts: each part's code is well formed**, the parts' summed count a `USize`. -/
theorem codes_guid_parts_wf {p : Nat} (cs : Vector (Part (.atom .guid)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom .guid) cs)[k]'hk
    laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  have hX := raze_len .guid cs.toArray hN
  obtain ⟨hw, hn, hsz, hid⟩ := codes_guid_wf (raze .guid cs.toArray)
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom .guid) #v[raze .guid cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hle := take_sum_le ((cs.map (·.1)).toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  have hc : c = ((Obj.codes (.atom .guid) #v[raze .guid cs.toArray])[0].cut (cs.map (·.1)))[k] := by
    show (Obj.codes (.atom .guid) cs)[k] = _; rw [codes_guid_cut cs (by omega)]
  obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw hs hsz hk
  rw [hc, hwk, hnk, hck, hzk]
  refine ⟨hw, by simp, rfl, fun h8 => ⟨(hid h8).1, fun i hi => ?_⟩⟩
  rw [hik i hi]; exact (hid h8).2 _ (by omega)

#print axioms codes_guid_cut
#print axioms codes_guid_parts_faithful
#print axioms codes_guid_parts_wf

end LeetQ.Rel.Alg
