/-
  The joint codes of a `general` side: `codes` lists the `raze` of the parts, codes each element by the first
  position holding a `valEq` element (`firstIds`), packs the ids (`pack`) and cuts the code back into the parts
  (`Code.cut`). Part `k`'s code at `i` is then the razed list's at `O_k + i`, and that element is part `k`'s row
  `i`; on cell-free elements `valEq` is `=` (`valEq_iff`), so equal codes are equal rows.
-/
import LeetQ.Rel.KernelWF.CodesArr
import LeetQ.Rel.KernelWF.CodesProd

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- **`firstIds` read back**: eight bytes an element, element `i`'s first `valEq` position, below the count. -/
theorem firstIds_get (l : List QValue) (hl : l.length < 2 ^ 64) :
    (firstIds l).size = 8 * l.length ∧
      ∀ i (hi : i < l.length), (Column.bitsAt (firstIds l) (i * 8) 8).toNat = l.findIdx (valEq l[i]) ∧
        l.findIdx (valEq l[i]) < l.length := by
  obtain ⟨hs, -, hb⟩ := foldl_pushBits (fun x => (l.findIdx (valEq x)).toUInt64) 8 (by decide) l .empty
  have hlt : ∀ i (hi : i < l.length), l.findIdx (valEq l[i]) < l.length := fun i hi =>
    List.findIdx_lt_length_of_exists ⟨l[i], List.getElem_mem hi, valEq_refl _⟩
  refine ⟨by simpa [firstIds] using hs, fun i hi => ⟨?_, hlt i hi⟩⟩
  have h := hb i hi
  simp only [ByteArray.size_empty, Nat.zero_add] at h
  unfold firstIds; rw [Nat.mul_comm i 8, h]
  have := Nat.lt_trans (hlt i hi) hl
  simp [Nat.mod_eq_of_lt this]

/-- **First `valEq` positions are faithful on cell-free elements**: two elements share one exactly when equal. -/
theorem findIdx_valEq_iff {l : List QValue} (hc : ∀ x ∈ l, cellFree x = true) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) : l.findIdx (valEq l[i]) = l.findIdx (valEq l[j]) ↔ l[i] = l[j] := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hlt : ∀ k (hk : k < l.length), l.findIdx (valEq l[k]) < l.length := fun k hk =>
    List.findIdx_lt_length_of_exists ⟨l[k], List.getElem_mem hk, valEq_refl _⟩
  have e : ∀ k (hk : k < l.length), l[k] = l[l.findIdx (valEq l[k])]'(hlt k hk) := fun k hk =>
    (valEq_iff (hc _ (List.getElem_mem hk))).1 (List.findIdx_getElem (w := hlt k hk))
  calc l[i] = l[l.findIdx (valEq l[i])]'(hlt i hi) := e i hi
    _ = l[l.findIdx (valEq l[j])]'(hlt j hj) := by simp only [h]
    _ = l[j] := (e j hj).symm

/-- **A `general` side's codes are its `raze`'s `firstIds`, packed and cut back** into the parts. -/
theorem codes_general {p : Nat} (cs : Vector (Part (.atom .general)) p) :
    Obj.codes (.atom .general) cs =
      (pack (gens (raze .general cs.toArray).2).toList.length (firstIds (gens (raze .general cs.toArray).2).toList)).cut
        (cs.map (·.1)) := by
  show codes .general cs = _
  unfold codes; rw [dif_pos rfl]

/-- **The razed list of a `general` side lists its parts' elements one part after another.** -/
theorem gens_raze_general {p : Nat} (cs : Vector (Part (.atom .general)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) :
    (gens (raze .general cs.toArray).2).toList = cs.toList.flatMap (·.2.toList) := by
  have hl := KernelWF.razeTo_toList_general cs.toArray rfl hN
  unfold razeTo at hl
  rw [KernelWF.cast_toList, KernelWF.toList_general] at hl
  simpa using hl

/-- The ids `codes` packs at a `general` side, read back: the list's count fits, its ids are below it, and each
    part's code at `i` is the razed list's first `valEq` position of the part's element `i`. -/
theorem codes_general_get {p : Nat} (cs : Vector (Part (.atom .general)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    let L := (gens (raze .general cs.toArray).2).toList
    let c := (Obj.codes (.atom .general) cs)[k]'hk
    (c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      ∀ i (hi : i < (cs[k]'hk).1.toNat), ∃ h : ((cs.toList.take k).map (·.1.toNat)).sum + i < L.length,
        Column.idAt c.b c.w i = L.findIdx (valEq (L[((cs.toList.take k).map (·.1.toNat)).sum + i]'h)) ∧
        L[((cs.toList.take k).map (·.1.toNat)).sum + i]'h = Vals.row (cs[k]'hk).2 ⟨i, hi⟩ := by
  intro L c
  have hL := gens_raze_general cs hN
  have hlen : L.length = (cs.toList.map (·.1.toNat)).sum := by
    show (gens _).toList.length = _
    rw [hL, List.length_flatMap]; congr 1; exact List.map_congr_left fun c _ => Arr.length_toList c.2
  have hU : L.length < 2 ^ 64 := by rcases USize.size_eq with h | h <;> rw [h] at hN <;> omega
  obtain ⟨hsz, hget⟩ := firstIds_get L hU
  have hlg : len (firstIds L) = L.length := by simp [len, hsz]
  obtain ⟨hw, hn, -, hpsz, hid⟩ := pack_get L.length (firstIds L) (by rw [hlg, hlen]; exact hN)
    (by rw [hlg, hsz]) (fun g hg => by rw [hlg] at hg; rw [(hget g hg).1]; exact (hget g hg).2)
  have hw' : laneOK((pack L.length (firstIds L)).w) := by rcases hw with h | h | h | h <;> simp [h]
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (pack L.length (firstIds L)).n.toNat := by
    rw [hn, hlg, hlen, Vector.toList_map, List.map_map]; rfl
  have hO : (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum := by
    rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hc : c = ((pack L.length (firstIds L)).cut (cs.map (·.1)))[k] := by
    show (Obj.codes (.atom .general) cs)[k] = _; rw [codes_general cs]
  obtain ⟨hwk, hnk, -, hik⟩ := cut_get _ (cs.map (·.1)) hw' hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw' hs hpsz hk
  rw [hc, hwk, hnk, hzk]
  refine ⟨hw, by simp, by simp, fun i hi => ?_⟩
  have hlt : ((cs.toList.take k).map (·.1.toNat)).sum + i < L.length := by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hlen]; exact Nat.lt_of_lt_of_le (by omega) this
  refine ⟨hlt, ?_, ?_⟩
  · rw [hik i (by simpa using hi), hO, hid _ (by rw [hlg]; exact hlt), (hget _ hlt).1]
  · have ho := flatMap_offset (fun c : Part (.atom .general) => c.2.toList) (·.1.toNat)
      (fun c => Arr.length_toList _) cs.toList (k := k) (by simpa using hk) (i := i) (by simpa using hi)
    rw [← hL, List.getElem?_eq_getElem hlt,
      List.getElem?_eq_getElem (by rw [Arr.length_toList]; simpa using hi)] at ho
    rw [Option.some_inj.1 ho, Arr.getElem_toList, Vals.row_atom]; rfl

/-- **A `general` side: its codes are faithful jointly across the parts**, one part or several, where every
    element is cell-free (so `valEq` is `=`) and the parts' summed count is a `USize`. -/
theorem codes_general_faithful {p : Nat} (cs : Vector (Part (.atom .general)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hC : ∀ k (hk : k < p) xs, (cs[k]'hk).2.enc = .gen xs → ∀ x ∈ xs, cellFree x = true)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom .general) cs)[k]'hk).b ((Obj.codes (.atom .general) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom .general) cs)[l]'hl).b ((Obj.codes (.atom .general) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  have hc : ∀ x ∈ (gens (raze .general cs.toArray).2).toList, cellFree x = true := fun x hx => by
    rw [gens_raze_general cs hN, List.mem_flatMap] at hx
    obtain ⟨c, hcm, hx⟩ := hx
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcm
    obtain ⟨xs, he, -⟩ := KernelWF.general_cases (cs.toList[m]).2.wf
    rw [KernelWF.toList_gen _ he, Array.mem_toList_iff] at hx
    exact hC m (by simpa using hm) xs (by simpa using he) x hx
  obtain ⟨-, -, -, hgk⟩ := codes_general_get cs hN hk
  obtain ⟨-, -, -, hgl⟩ := codes_general_get cs hN hl
  obtain ⟨hk', ek, rk⟩ := hgk i hi
  obtain ⟨hl', el, rl⟩ := hgl j hj
  rw [ek, el, findIdx_valEq_iff hc hk' hl', rk, rl]

/-- **A `general` side: each part's code is well formed**, the parts' summed count a `USize`; a byte lane, so
    no id bound is owed. -/
theorem codes_general_wf {p : Nat} (cs : Vector (Part (.atom .general)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom .general) cs)[k]'hk
    laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  obtain ⟨hw, hn, hsz, -⟩ := codes_general_get cs hN hk
  refine ⟨by rcases hw with h | h | h | h <;> simp [c, h], hn, hsz, fun h8 => ?_⟩
  exfalso; rcases hw with h | h | h | h <;> simp only [c] at h8 <;> omega

-- `0f` and `-0f` are one value to q's `~` and two rows to Rel: two codes; an equal row repeats its code
#guard let c := (Obj.codes (.atom .general)
    #v[genCol #[.atom (.float 0), .atom (.float 0x8000000000000000), .atom (.float 0)]])[0]
  (List.range 3).map (Column.idAt c.b c.w) == [0, 1, 0]

#print axioms codes_general_faithful
#print axioms codes_general_wf

end LeetQ.Rel.Alg
