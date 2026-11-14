/-
  The joint codes of a symbol side of several parts: `codes` interns the `raze` of the parts once and cuts its
  lane code back into the parts (`Code.cut`), so part `k`'s code at `i` is the razed column's at `O_k + i`, and
  that row is part `k`'s row `i` (`raze_get_symbol`).
-/
import LeetQ.Rel.KernelWF.RazeSym

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- **A symbol side of several parts: its codes are those of its `raze`, cut back**: past the bitmap and
    `rangeOffsets` branches, which a symbol side never takes, `codes` interns the razed column. -/
theorem codes_symbol_cut {p : Nat} (cs : Vector (Part (.atom .symbol)) p) (hp : 0 < p) :
    Obj.codes (.atom .symbol) cs =
      (Obj.codes (.atom .symbol) #v[raze .symbol cs.toArray])[0].cut (cs.map (·.1)) := by
  obtain ⟨d, o, ids, hI, hc⟩ := codes_symbol (raze .symbol cs.toArray)
  rw [hc]
  show Alg.codes .symbol cs = _
  unfold Alg.codes
  rw [dif_neg (by decide)]
  split
  · next bs h =>
    exfalso
    have h0 := vec_mapM_some h hp
    revert h0
    rcases symbol_enc (cs[0]'hp).2.wf with ⟨b, o, he⟩ | ⟨d, o, ids, he⟩ <;> simp [he]
  have hro : rangeOffsets .symbol (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none := by
    simp [rangeOffsets, orderKind]
  simp only [hro]
  split
  · next d' o' ids' hi =>
    obtain ⟨rfl, rfl, rfl⟩ := Enc.enum.inj (hI.symm.trans hi)
    rfl
  all_goals (rename_i hi; exact Enc.noConfusion (hI.symm.trans hi))

/-- **A symbol side of several parts: its codes are faithful jointly across the parts.** Part `k`'s code at `i`
    and part `l`'s at `j` agree exactly when the rows do; the parts' summed count, and their dictionaries
    summed (a blob counting its rows), fit a `USize`. -/
theorem codes_symbol_parts_faithful {p : Nat} (cs : Vector (Part (.atom .symbol)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hD : (cs.toList.map fun c => match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat).sum <
      USize.size)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < cs[k].1.toNat) (hj : j < cs[l].1.toNat) :
    Column.idAt (Obj.codes (.atom .symbol) cs)[k].b (Obj.codes (.atom .symbol) cs)[k].w i =
        Column.idAt (Obj.codes (.atom .symbol) cs)[l].b (Obj.codes (.atom .symbol) cs)[l].w j ↔
      Vals.row cs[k].2 ⟨i, hi⟩ = Vals.row cs[l].2 ⟨j, hj⟩ := by
  have hX := raze_len .symbol cs.toArray hN
  obtain ⟨d, o, ids, hI, hc⟩ := codes_symbol (raze .symbol cs.toArray)
  have hw : laneOK((Obj.codes (.atom .symbol) #v[raze .symbol cs.toArray])[0].w) := by
    rw [hc]; unfold Code.ofLane; split
    · exact .inl rfl
    · next h => exact (idWidth_facts o).1.resolve_left (by simpa using h)
  have hn : (Obj.codes (.atom .symbol) #v[raze .symbol cs.toArray])[0].n = (raze .symbol cs.toArray).1 := by
    rw [hc]; unfold Code.ofLane; split <;> rfl
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum =
      (Obj.codes (.atom .symbol) #v[raze .symbol cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < cs[k].1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze .symbol cs.toArray).1.toNat :=
    fun k hk i hi => by
      have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
      simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
      rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [codes_symbol_cut cs (by omega)]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    codes_symbol_faithful (raze .symbol cs.toArray) (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom,
    Vals.row_atom, Vals.row_atom, KernelWF.raze_get_symbol cs hN hD hk hi, KernelWF.raze_get_symbol cs hN hD hl hj]

/-- **A symbol side of several parts: each part's code is well formed**, the parts' summed count a `USize`. -/
theorem codes_symbol_parts_wf {p : Nat} (cs : Vector (Part (.atom .symbol)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom .symbol) cs)[k]
    laneOK(c.w) ∧ c.n = cs[k].1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  have hX := raze_len .symbol cs.toArray hN
  obtain ⟨hw, hn, hbs, hid⟩ := codes_symbol_wf (raze .symbol cs.toArray)
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum =
      (Obj.codes (.atom .symbol) #v[raze .symbol cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hle := take_sum_le ((cs.map (·.1)).toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  have hc : c = ((Obj.codes (.atom .symbol) #v[raze .symbol cs.toArray])[0].cut (cs.map (·.1)))[k] := by
    show (Obj.codes (.atom .symbol) cs)[k] = _; rw [codes_symbol_cut cs (by omega)]
  obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw hs hbs hk
  rw [hc, hwk, hnk, hck, hzk]
  refine ⟨hw, by simp, rfl, fun h8 => ⟨(hid h8).1, fun i hi => ?_⟩⟩
  rw [hik i hi]; exact (hid h8).2 _ (by omega)

end LeetQ.Rel.Alg
