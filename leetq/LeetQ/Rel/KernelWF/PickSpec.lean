/-
  What `pick` CONTAINS: row `k` of `x@i` is row `i[k]` of `x`, the index read unsigned, wherever that
  long is below `x`'s count. Stated over `Enc.get`, the reader `Arr.get` goes through.
-/
import LeetQ.Rel.Code

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify

/-- Belongs in qlean. `Enc.get` at a fixed-width type is `raw`'s element read through `atomOfBits`. -/
theorem get_eq_raw {t : QAtomicType} {w : Nat} (ht : denseWidth t = some w) {n : USize} {e : Enc}
    (hw : Enc.WF t n e) {j : Nat} (hj : j < n.toNat) :
    Enc.get t n e j = some (Column.atomOfBits t ((Enc.raw t n e).toList.getD j 0)
      (QAtomicType.ne_general_of_width (denseWidth_facts ht).2.1)) := by
  obtain ⟨-, hw', hb, hg, hs, -, -⟩ := denseWidth_facts ht
  cases e <;> cases t <;>
    simp_all [Enc.get, Enc.raw, Enc.WF, QAtomicType.width, denseWidth, List.getD_eq_getElem?_getD,
      foRBits_starts, alpBits_starts]

/-- Belongs in qlean. **`x@i` at a fixed-width type, read back**: element `k` of the answer is element
    `i[k]` of `x`, the index read unsigned, where that is below `x`'s count. -/
theorem gatherColumn_get_dense {t : QAtomicType} {w : Nat} (ht : denseWidth t = some w) {n : USize} {e : Enc}
    (hw : Enc.WF t n e) {m : USize} {i : ByteArray} (hm : m.toNat = i.size / 8) {e' : Enc}
    (h : gatherColumn t n e m (.bytes i) = some e') {k : Nat} (hk : k < m.toNat)
    (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get t m e' k = Enc.get t n e (Column.bitsAt i (k * 8) 8).toNat := by
  obtain ⟨-, hw', hb, hg, hs, hw0, hw8⟩ := denseWidth_facts ht
  have hwf' := gatherColumn_wf hw i hm h
  obtain ⟨src, ix, hsrc, hix, rfl⟩ := gatherColumn_fixed_shape ht n e m (.bytes i) _ hw h
  simp only [Enc.bytesOf, Option.some.injEq] at hix; subst hix
  have hwU : w.toUSize.toNat = w :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  rw [get_eq_raw ht hwf' hk, get_eq_raw ht hw hin]
  obtain ⟨-, hG⟩ := gatherBytes_spec w.toUSize (by omega) ((nullBits t).getD 0) src i
  rw [hwU] at hG
  have hS := elemsW_bytesOf hw' hb hg hw0 hw8 n e hw src hsrc
  have hR := size_raw n e hw hb hg hs (QAtomicType.ne_general_of_width hw')
  have hsz : src.size / w = n.toNat := by
    have := congrArg List.length hS; simp only [elemsW, List.length_map, List.length_range,
      Array.length_toList] at this; omega
  have hidx := congrArg (·.getD (Column.bitsAt i (k * 8) 8).toNat 0) hS
  simp only [elemsW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (hsz ▸ hin),
    Option.map_some, Option.getD_some] at hidx
  rw [raw_bytes t w hw' hb hg]
  simp only [Array.toList_map, Array.toList_range, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  rw [hG k (by omega), if_pos (by omega), hidx,
    List.getElem?_eq_getElem (by simp only [Array.length_toList, hR]; exact hin)]
  exact congrArg some (atomOfBits_mod hw' hb hg _)

/-- Belongs in qlean. **`x@i` at `boolean`, read back**: bit `k` of the answer is bit `i[k]` of `x`. -/
theorem gatherColumn_get_bits {n : USize} {e : Enc} (hw : Enc.WF .boolean n e) {m : USize} {i : ByteArray}
    (hm : m.toNat = i.size / 8) {e' : Enc} (h : gatherColumn .boolean n e m (.bytes i) = some e') {k : Nat}
    (hk : k < m.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get .boolean m e' k = Enc.get .boolean n e (Column.bitsAt i (k * 8) 8).toNat := by
  have hz : ¬ i.size < m.toNat * 8 := by omega
  cases e <;> try (exfalso; simp_all [Enc.WF, QAtomicType.width]; done)
  simp only [gatherColumn, denseWidth, foRColumn, Enc.bytesOf, hz, if_false, Option.map_some,
    Option.some.injEq] at h
  subst h
  simp only [Enc.get, if_pos hk, bitAt_gatherBits _ _ _ _ (hm ▸ hk), if_pos hin]

/-- `extract` of a range that ends where it starts, or before, is empty. -/
theorem extract_empty (b : ByteArray) {lo hi : Nat} (h : hi ≤ lo) : b.extract lo hi = b.extract lo lo := by
  apply ByteArray.ext; simp only [ByteArray.data_extract]
  rw [Array.extract_eq_empty_of_le (by omega), Array.extract_eq_empty_of_le (by omega)]

/-- A byte array's element is its data's. -/
theorem ba_get? (b : ByteArray) (i : Nat) : b[i]? = b.data[i]? := (Option.map_inj_right fun _ _ a => a).mp rfl

/-- Symbol `j`'s bytes as `symBytes` cuts them: its start to the NUL before the next start. -/
theorem extract_upto (b : ByteArray) (lo hi : Nat) :
    b.extract lo (lo + if hi > lo then hi - lo - 1 else 0) = b.extract lo (hi - 1) := by
  split
  · congr 1; omega
  · rw [Nat.add_zero, extract_empty b (show hi - 1 ≤ lo by omega)]

/-- Belongs in qlean. **`x@i` at a `symbol` blob, read back**: symbol `k` of the answer is symbol `i[k]`
    of `x`. -/
theorem gatherColumn_get_syms {n : USize} {blob : ByteArray} {offs : Array Nat}
    (hw : Enc.WF .symbol n (.syms blob offs)) {m : USize} {i : ByteArray}
    (hm : m.toNat = i.size / 8) {e' : Enc} (h : gatherColumn .symbol n (.syms blob offs) m (.bytes i) = some e')
    {k : Nat} (hk : k < m.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get .symbol m e' k = Enc.get .symbol n (.syms blob offs) (Column.bitsAt i (k * 8) 8).toNat := by
  have hz : ¬ i.size < m.toNat * 8 := by omega
  simp only [gatherColumn, denseWidth, foRColumn, Enc.bytesOf, hz, if_false, Option.map_some,
    Option.some.injEq] at h
  subst h
  obtain ⟨-, hJ⟩ := gatherSyms_spec blob offs i
  obtain ⟨lo, h1, h2, h3⟩ := hJ k (hm ▸ hk)
  simp only [Enc.WF] at hw
  have hg : gatherAt (offs.size - 1) i k = some (Column.bitsAt i (k * 8) 8).toNat := by
    simp only [gatherAt]; rw [if_pos (by omega)]
  simp only [hg] at h2 h3
  simp only [Enc.get, if_pos hk, if_pos hin, Column.symBytes, extract_upto]
  generalize blob.extract _ _ = K at h2 h3 ⊢
  have e1 : (gatherSyms blob offs i).2[k]! = lo := by simp [getElem!_def, h1]
  have e2 : (gatherSyms blob offs i).2[k + 1]! = lo + K.size + 1 := by simp [getElem!_def, h2]
  rw [e1, e2, Nat.add_sub_cancel]
  generalize (gatherSyms blob offs i).fst = G at h3
  simp only [ba_get?] at h3
  have hsz : K.size = 0 ∨ lo + K.size ≤ G.size := by
    rcases Nat.eq_zero_or_pos K.size with h | h
    · exact .inl h
    refine .inr (Nat.not_lt.1 fun hc => ?_)
    have := h3 (K.size - 1) (by omega)
    rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; omega),
      Array.getElem?_eq_getElem (by rw [ByteArray.size_data]; omega)] at this
    cases this
  suffices hK : G.extract lo (lo + K.size) = K by rw [hK]
  apply ByteArray.ext; apply Array.ext_getElem?; intro q
  rw [ByteArray.data_extract, Array.getElem?_extract, ByteArray.size_data]
  split
  · exact h3 q (by omega)
  · rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; omega)]

/-- Belongs in qlean. **`x@i` read back** at every atom type but `general`, `guid` and an interned
    symbol column: element `k` of the answer is element `i[k]` of `x`, where that is below `x`'s count. -/
theorem gatherColumn_get {t : QAtomicType} {n : USize} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general)
    (hgu : t ≠ .guid) (hen : ∀ d o ids, e ≠ .enum d o ids)
    {m : USize} {i : ByteArray} (hm : m.toNat = i.size / 8) {e' : Enc}
    (h : gatherColumn t n e m (.bytes i) = some e') {k : Nat} (hk : k < m.toNat)
    (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get t m e' k = Enc.get t n e (Column.bitsAt i (k * 8) 8).toNat := by
  cases hd : denseWidth t with
  | some w => exact gatherColumn_get_dense hd hw hm h hk hin
  | none =>
    by_cases hb : t = .boolean
    · subst hb; exact gatherColumn_get_bits hw hm h hk hin
    have hs : t = .symbol := by cases t <;> simp_all [denseWidth, QAtomicType.width]
    subst hs
    cases e with
    | syms b o => exact gatherColumn_get_syms hw hm h hk hin
    | enum d o ids => exact absurd rfl (hen d o ids)
    | _ => all_goals (exfalso; simp [Enc.WF, QAtomicType.width] at hw)

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel LeetQ.Rel

/-- A general list's element `j` is its `gen` column's. -/
theorem get_general {n : USize} (x : Arr .general n) {xs : Array QValue} (hc : x.enc = .gen xs)
    (j : Fin n.toNat) : x.get j = xs[j.1]'(by rw [Arr.gen_size x hc]; exact j.2) := by
  simp only [Arr.get]; split
  · rename_i ys hc'; rw [hc] at hc'; cases hc'; rfl
  · rename_i hn; exact (hn xs hc).elim

/-- `pick` at `general` is `genCol` of the picked elements. -/
theorem pick_general (c : (n : USize) × Arr .general n) (i : ByteArray) :
    pick .general c i = genCol ((longRows i).map fun p => (gens c.2)[p]?.getD (QLean.Eval.fillOf (gens c.2))) := by
  simp [pick]

/-- **`pick` read back at `general`**: element `k` of `x@i` is element `i[k]` of `x`. -/
theorem pick_get_general (c : (n : USize) × Arr .general n) (i : ByteArray) (hl : len i < USize.size)
    (k : Nat) (hk : k < (pick .general c i).1.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < c.1.toNat) :
    (pick .general c i).2.get ⟨k, hk⟩ = c.2.get ⟨_, hin⟩ := by
  obtain ⟨xs, he, hs⟩ := KernelWF.general_cases c.2.wf
  have hgx : gens c.2 = xs := Option.some_inj.1 ((Option.some_get _).trans (by simp [he]))
  have hsz : ((longRows i).map fun p => (gens c.2)[p]?.getD (QLean.Eval.fillOf (gens c.2))).size < USize.size := by
    simpa [longRows, len] using hl
  revert hk; rw [pick_general, genCol, need, dif_pos hsz]; intro hk
  rw [get_general _ rfl, get_general _ he]
  simp only [Array.getElem_map, longRows, Array.getElem_range, hgx, Nat.mul_comm 8 k]
  rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]

/-- **`pick` read back**: row `k` of `x@i` is row `i[k]` of `x`, the index read unsigned, where that is
    below `x`'s count; every atom type but `guid`, every payload but an interned symbol column. -/
theorem pick_get {t : QAtomicType} (c : (n : USize) × Arr t n) (i : ByteArray) (hl : len i < USize.size)
    (hgu : t ≠ .guid) (hen : ∀ d o ids, c.2.enc ≠ .enum d o ids)
    (k : Nat) (hk : k < (pick t c i).1.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < c.1.toNat) :
    (pick t c i).2.get ⟨k, hk⟩ = c.2.get ⟨_, hin⟩ := by
  by_cases hg : t = .general
  · subst hg; exact pick_get_general c i hl k hk hin
  obtain ⟨e, he, hp⟩ := pick_eq_gather hg c i hl
  have h1 : (pick t c i).1 = (len i).toUSize := by simpa [Arr.part] using congrArg Prod.fst hp
  have h2 : (pick t c i).2.enc = e := by simpa [Arr.part] using congrArg Prod.snd hp
  have hm : ((len i).toUSize).toNat = i.size / 8 := USize.toNat_ofNat_of_lt' hl
  rw [Arr.get_ne _ _ hg, Arr.get_ne _ _ hg, h2]
  simp only []
  rw [h1, KernelWF.gatherColumn_get c.2.wf hg hgu hen hm he (h1 ▸ hk) hin]

end LeetQ.Rel.Alg
