/-
  The kernels `leftDiv` adds to `≫`'s, read back: `tuples.tupleIds`' class ids (each row's class is the
  position of its pair's first row among the first rows), `classSizes` of a `tupleIds` answer (each class's
  row count), and `whereEqV` (the positions where two long columns agree). `atCnt (cnt c) k` is `join`'s count
  column, read back by `join_count`.
-/
import LeetQ.Rel.KernelWF.JoinAssembly
import LeetQ.Rel.KernelWF.NubSpec
import LeetQ.Rel.KernelWF.CrossSpec
import LeetQ.Rel.KernelWF.SortSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

-- a pair of code columns read as one key per row, the key `tupleIds` groups by
local notation "key2(" a ", " b ")" => fun i => (Column.idAt (Code.b a) (Code.w a) i, Column.idAt (Code.b b) (Code.w b) i)
-- a code column at a lane, of exactly its codes, below a byte under its bound: what `tupleIds_firsts` takes
set_option hygiene false in
local notation "codeOK(" a ")" => ((Code.w a = 1 ∨ Code.w a = 2 ∨ Code.w a = 4 ∨ Code.w a = 8 ∨ Code.w a = 16 ∨
  Code.w a = 32 ∨ Code.w a = 64) ∧ ByteArray.size (Code.b a) = (USize.toNat (Code.n a) * Code.w a + 7) / 8 ∧
  (Code.w a < 8 → ∀ i < USize.toNat (Code.n a),Column.idAt (Code.b a) (Code.w a) i < max (Code.card a) 2))

/-- At most `m` first positions. -/
theorem firstsOf_length_le {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat) : (firstsOf g m).length ≤ m := by
  have := List.length_filter_le (fun i => (List.range i).all fun j => !decide (g j = g i)) (List.range m)
  rw [List.length_range] at this; exact this

/-- **`tupleIds`' class ids, read back**: at the width of its first-row count, row `i`'s id is the position of
    its pair's first row among the first rows (`groupOf`), and the payload holds all `n` of them. Hypotheses as
    `tupleIds_firsts`. -/
theorem tupleIds_groupOf (a b : Code) (hn : b.n = a.n) (ha : codeOK(a)) (hb : codeOK(b)) :
    Column.idsCap (tuples.tupleIds a #[b]).1 (Column.idWidthOf (len (tuples.tupleIds a #[b]).2)) a.n.toNat =
        a.n.toNat ∧
      ∀ i < a.n.toNat, Column.idAt (tuples.tupleIds a #[b]).1 (Column.idWidthOf (len (tuples.tupleIds a #[b]).2)) i =
        Verify.groupOf key2(a, b) a.n.toNat i := by
  have e : tuples.tupleIds a #[b] = match pairCode true a b with | (_, some r) => r | (c, none) => c.groupIds := rfl
  rw [e]
  rcases hp : pairCode true a b with ⟨c, _ | r⟩
  · have h := pairCode_spec true a b hn ha hb
    simp only [hp] at h
    obtain ⟨⟨hw, hcn, hs, hcd⟩, hiff⟩ := h
    dsimp only
    obtain ⟨hcap, hg⟩ := groupIds_groupOf c hw hs hcd
    rw [hcn] at hcap hg
    obtain ⟨-, -, hgo⟩ := groups_congr (Column.idAt c.b c.w) a.n.toNat (g' := key2(a, b))
      fun i hi j hj => (hiff i hi j hj).trans (Prod.mk.injEq _ _ _ _).symm.to_iff
    exact ⟨hcap, fun i hi => (hg i hi).trans (hgo i hi)⟩
  · obtain ⟨key, hkey, hr, -⟩ := pairCode_grouped_key true a b hn ⟨ha.1, ha.2.1⟩ ⟨hb.1, hb.2.1⟩ (by rw [hp])
    dsimp only
    have hbq : ∀ x y : UInt64 × UInt64, (x == y) = decide (x = y) := fun x y =>
      Bool.eq_iff_iff.2 (by rw [beq_iff_eq, decide_eq_true_iff])
    have hF : Order.firstsBy a.n.toNat key = firstsOf key a.n.toNat := by
      simp only [Order.firstsBy, firstsOf, bne, hbq]
    have hlt : ∀ i ∈ Order.firstsBy a.n.toNat key, i < 2 ^ 64 := fun i hi =>
      Nat.lt_trans (List.mem_range.1 (List.mem_filter.1 hi).1) (Verify.usize_lt a.n)
    have hL : len r.2 = (firstsOf key a.n.toNat).length := by
      rw [hr, len_eq_ids, show (Order.idsBy a.n.toNat key).2 = Order.indices (Order.firstsBy a.n.toNat key) from rfl,
        ids_indices _ hlt, hF]
    have h1 : r.1 = Column.packIds (Column.idWidthOf (firstsOf key a.n.toNat).length) a.n.toNat
        (Verify.groupOf key a.n.toNat) := by
      rw [hr, show (Order.idsBy a.n.toNat key).1 = Column.packIds
        (Column.idWidthOf (Order.firstsBy a.n.toNat key).length) a.n.toNat
        (fun i => (Order.firstsBy a.n.toNat key).findIdx (key · == key i)) from rfl, hF]
      simp only [hbq]; rfl
    obtain ⟨-, -, hgo⟩ := groups_congr key a.n.toNat (g' := key2(a, b))
      fun i hi j hj => (hkey i hi j hj).trans (Prod.mk.injEq _ _ _ _).symm.to_iff
    have hW := laneWidth_cases (Column.widthFor ((firstsOf key a.n.toNat).length - 1))
    simp only [show ∀ x, Column.laneWidth (Column.widthFor (x - 1)) = Column.idWidthOf x from fun _ => rfl] at hW
    have hLn : (firstsOf key a.n.toNat).length ≤ 2 ^ 64 :=
      Nat.le_trans (firstsOf_length_le _ _) (Nat.le_of_lt (usize_lt a.n))
    rw [hL, h1]
    refine ⟨idsCap_packIds _ _ hW, fun i hi => ?_⟩
    rw [idAt_packIds hW hi (lt_two_pow_idWidthOf hLn (groupOf_lt hi))]; exact hgo i hi

/-- **`classSizes` of a `tupleIds` answer, read back**: class `g`'s count is the number of rows holding the
    pair of codes of the `g`-th first row. Hypotheses as `tupleIds_firsts`. -/
theorem tupleIds_sizes (a b : Code) (hn : b.n = a.n) (ha : codeOK(a)) (hb : codeOK(b)) {g : Nat}
    (hg : g < (firstsOf key2(a, b) a.n.toNat).length) :
    (Column.bitsAt (classSizes a.n (tuples.tupleIds a #[b])) (g * 8) 8).toNat =
      ((List.range a.n.toNat).filter fun q =>
        decide (key2(a, b) q = key2(a, b) ((firstsOf key2(a, b) a.n.toNat)[g]'hg))).length := by
  have hF := tupleIds_firsts a b hn ha hb
  obtain ⟨hcap, hγ⟩ := tupleIds_groupOf a b hn ha hb
  have hK : len (tuples.tupleIds a #[b]).2 = (firstsOf key2(a, b) a.n.toNat).length := by rw [len_eq_ids, hF]
  have hKU : len (tuples.tupleIds a #[b]).2 < USize.size := by
    rw [hK]; exact Nat.lt_of_le_of_lt (firstsOf_length_le _ _) a.n.toNat_lt_size
  have hS := classSizes_ids a.n (tuples.tupleIds a #[b]) hKU
  rw [ids_get hS (by simp [hK, hg])]
  simp only [List.getElem_map, List.getElem_range, idsW, hcap, List.countP_eq_length_filter, List.filter_map,
    List.length_map]
  congr 1
  refine List.filter_congr fun j hj => ?_
  have hj' := List.mem_range.1 hj
  simp only [Function.comp_def, hγ j hj']
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact groupOf_eq_iff hj' hg

/-- **`whereEqV n a b`, read back**: the ascending positions below `n` where the two long columns hold the
    same long. -/
theorem whereEqV_ids (n : USize) (a b : ByteArray) :
    ids (whereEqV n a b) = (List.range n.toNat).filter fun i =>
      decide (Column.bitsAt a (i * 8) 8 = Column.bitsAt b (i * 8) 8) := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have hs : ∀ i, Ew.shapeIdx Ew.vv i = (i, i) := fun i => by simp (config := {decide := true}) [Ew.shapeIdx]
  rw [whereEqV, (whereBits_ids n _).1]
  refine List.filter_congr fun i hi => ?_
  have hi := List.mem_range.1 hi
  rw [(Verify.cmp_bitAt _ _ _ _ _ n).2 i (by omega)]
  simp only [Ew.elem, hw, hs, decide_eq_true hi, Bool.true_and]
  generalize Column.bitsAt a (i * 8) 8 = x
  generalize Column.bitsAt b (i * 8) 8 = y
  simp (config := {decide := true}) only [Ew.cmpStep, Ew.signed, ↓reduceIte]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  show compareOfLessAndEq _ _ = _ ↔ _
  unfold compareOfLessAndEq
  constructor
  · intro h
    split at h
    · cases h
    · split at h
      · simpa using congrArg Int64.toUInt64 ‹x.toInt64 = y.toInt64›
      · cases h
  · rintro rfl
    rw [if_neg Int64.lt_irrefl, if_pos rfl]

/-- **`gather 8 src idx`, read back** at in-range indices: `src`'s long at each index of `idx`. -/
theorem ids_gather8 {src idx : ByteArray} (h : ∀ t ∈ ids idx, t < len src) :
    ids (gather 8 src idx) = (ids idx).map fun t => (ids src).getD t 0 := by
  apply List.ext_getElem
  · simp only [List.length_map, ← len_eq_ids, gather_len]
  · intro j h1 h2
    have h2' : j < (ids idx).length := by simpa using h2
    have hj : j < len idx := by rw [len_eq_ids]; exact h2'
    have hm : (Column.bitsAt idx (j * 8) 8).toNat < len src := by
      rw [← ids_getElem h2']; exact h _ (List.getElem_mem h2')
    have hm' : (ids idx)[j] < (ids src).length := by rw [← len_eq_ids, ids_getElem h2']; exact hm
    rw [ids_getElem h1, List.getElem_map, gather8_get hj hm, ← ids_getElem h2', List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hm', Option.getD_some, ids_getElem hm']

/-- **`leftDiv`'s kept rows, read back**: of the first rows of the pairs `(yc, zc)`, ascending, those whose
    pair's row count equals the number of rows of `rv` holding the first row's `yc` code — `whereEqV` of
    `classSizes` (`tupleIds_sizes`) against `atCnt (cnt rv)` (`join_count`), gathered into the first rows.
    Hypotheses: `yc`, `zc` as `tupleIds_firsts`, `rv` as `join_count`'s right side. -/
theorem leftDiv_keep (yc zc rv : Code) (hn : zc.n = yc.n) (hy : codeOK(yc)) (hz : codeOK(zc))
    (hrw : rv.w = 1 ∨ rv.w = 2 ∨ rv.w = 4 ∨ rv.w = 8 ∨ rv.w = 16 ∨ rv.w = 32 ∨ rv.w = 64)
    (hrs : rv.b.size = (rv.n.toNat * rv.w + 7) / 8)
    (hrc : rv.w < 8 → rv.card < USize.size ∧ ∀ i < rv.n.toNat, Column.idAt rv.b rv.w i < rv.card) :
    ids (longCount "\\" (tuples.tupleIds yc #[zc]).2 fun g _ => gather 8 (tuples.tupleIds yc #[zc]).2
      (whereEqV g (classSizes yc.n (tuples.tupleIds yc #[zc]))
        (atCnt (cnt rv) (yc.gather (tuples.tupleIds yc #[zc]).2)))) =
    ((List.range (firstsOf key2(yc, zc) yc.n.toNat).length).filter fun t =>
      decide (((List.range yc.n.toNat).filter fun q =>
          decide (key2(yc, zc) q = key2(yc, zc) ((firstsOf key2(yc, zc) yc.n.toNat).getD t 0))).length =
        ((List.range rv.n.toNat).filter fun j =>
          Column.idAt rv.b rv.w j == Column.idAt yc.b yc.w ((firstsOf key2(yc, zc) yc.n.toNat).getD t 0)).length)).map
      fun t => (firstsOf key2(yc, zc) yc.n.toNat).getD t 0 := by
  have hF := tupleIds_firsts yc zc hn hy hz
  have hK : len (tuples.tupleIds yc #[zc]).2 = (firstsOf key2(yc, zc) yc.n.toNat).length := by rw [len_eq_ids, hF]
  have hKU : len (tuples.tupleIds yc #[zc]).2 < USize.size := by
    rw [hK]; exact Nat.lt_of_le_of_lt (firstsOf_length_le _ _) yc.n.toNat_lt_size
  have hG : (len (tuples.tupleIds yc #[zc]).2).toUSize.toNat = (firstsOf key2(yc, zc) yc.n.toNat).length := by
    rw [USize.toNat_ofNat_of_lt' hKU, hK]
  unfold longCount need; rw [dif_pos hKU]; dsimp only
  have hW := whereEqV_ids (len (tuples.tupleIds yc #[zc]).2).toUSize (classSizes yc.n (tuples.tupleIds yc #[zc]))
    (atCnt (cnt rv) (yc.gather (tuples.tupleIds yc #[zc]).2))
  rw [hG] at hW
  rw [ids_gather8 (fun t ht => by
    rw [hW] at ht; rw [hK]; exact List.mem_range.1 (List.mem_filter.1 ht).1), hW, hF]
  congr 1
  refine List.filter_congr fun t ht => ?_
  have ht := List.mem_range.1 ht
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  have hFi : ∀ j < len (tuples.tupleIds yc #[zc]).2,
      (Column.bitsAt (tuples.tupleIds yc #[zc]).2 (j * 8) 8).toNat < yc.n.toNat := fun j hj => by
    rw [ids_get hF (by rw [← hK]; exact hj)]; exact firsts_lt _ _ (List.getElem_mem _)
  obtain ⟨hgw, hgn, -, hgc⟩ := gather_spec yc _ hKU hy.1 (code_size hy.1 hy.2.1).2 hFi
  have hGs := gather_size yc (tuples.tupleIds yc #[zc]).2 hKU hy.1
  have htK : t < len (tuples.tupleIds yc #[zc]).2 := by rw [hK]; exact ht
  have hc := join_count (yc.gather (tuples.tupleIds yc #[zc]).2) rv hrw hrs hrc (by rw [hgw]; exact hy.1)
    (by rw [hgw, hgn]; exact hGs) (i := t) (by rw [hgn]; exact htK)
  rw [hgw, hgc t htK, ids_get hF ht] at hc
  have hs := tupleIds_sizes yc zc hn hy hz ht
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← UInt64.toNat_inj, hs,
    show atCnt (cnt rv) (yc.gather (tuples.tupleIds yc #[zc]).2) = gather 8 (classSizes rv.n rv.groupIds)
      ((rv.gather rv.groupIds.2).find (yc.gather (tuples.tupleIds yc #[zc]).2)) from rfl, hc]

#print axioms tupleIds_groupOf
#print axioms tupleIds_sizes
#print axioms whereEqV_ids
#print axioms ids_gather8
#print axioms leftDiv_keep

end LeetQ.Rel.Alg
