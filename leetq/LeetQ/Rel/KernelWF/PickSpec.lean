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

end LeetQ.Rel.KernelWF
