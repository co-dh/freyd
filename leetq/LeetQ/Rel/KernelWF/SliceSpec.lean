/-
  `slicesOf` read back with the `expand` `mem` runs on it: the copies are the array side's rows' elements, row
  by row in order — copy of row `r`'s element `j` holds the row `r` and the payload position `L r + j`.
-/
import LeetQ.Rel.KernelWF.PickRow

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

namespace SliceN
-- row `r`'s slice of the array side `x`, its start and end clamped into `[0, x.1]`, as `Vals.row` reads it; one
-- home: `open SliceN` in every file that reads a slice back
set_option hygiene false in
scoped notation "sL(" x ", " r ", " h ")" => min (max (Int64.toInt (Arr.get x.2.1 ⟨r, h⟩)) 0).toNat x.1.toNat
set_option hygiene false in
scoped notation "sH(" x ", " r ", " h ")" => min (max (Int64.toInt (Arr.get x.2.2.1 ⟨r, h⟩)) 0).toNat x.1.toNat
end SliceN
open SliceN
-- `expand`'s index column of `slicesOf x`'s counts, and each copy's payload position, as `mem` computes them
set_option hygiene false in
local notation "sE(" n ", " x ")" => expandBytes 8 0 (tilLongs n) (slicesOf x).2
set_option hygiene false in
local notation "sP(" n ", " x ")" => add (len sE(n, x)).toUSize (gather 8 (slicesOf x).1 sE(n, x))
  (sub (len sE(n, x)).toUSize (tilLongs (len sE(n, x)).toUSize)
    (gather 8 (sub n (sums n (slicesOf x).2) (slicesOf x).2) sE(n, x)))

/-- **`slicesOf` read back at a row**: row `t`'s start is its clamped start, its count the clamped window's
    length. Hypothesis: the payload count below `2^63`. -/
theorem slicesOf_get {B : Obj} {n : USize} (x : Vals (.arr B) n) (hp : x.1.toNat < 2 ^ 63) {t : Nat}
    (ht : t < n.toNat) :
    (Column.bitsAt (slicesOf x).1 (t * 8) 8).toNat = sL(x, t, ht) ∧
      (Column.bitsAt (slicesOf x).2 (t * 8) 8).toNat = sH(x, t, ht) - sL(x, t, ht) := by
  obtain ⟨p, lo, hi, f⟩ := x
  have hsl := slices_get (n := n) hp (longsOf lo) (longsOf hi) ht
  rw [longsOf_get _ ht, longsOf_get _ ht, Int64.toInt64_toUInt64, Int64.toInt64_toUInt64] at hsl
  show (Column.bitsAt (slices p n (longsOf lo) (longsOf hi)).1 (t * 8) 8).toNat = _ ∧
    (Column.bitsAt (slices p n (longsOf lo) (longsOf hi)).2 (t * 8) 8).toNat = _
  rw [hsl.1, hsl.2]
  have h1 : min (max (lo.get ⟨t, ht⟩).toInt 0).toNat p.toNat ≤ p.toNat := Nat.min_le_right _ _
  have h2 : min (max (hi.get ⟨t, ht⟩).toInt 0).toNat p.toNat ≤ p.toNat := Nat.min_le_right _ _
  have h64 : p.toNat < UInt64.size := Nat.lt_trans hp (by decide)
  exact ⟨UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h1 h64),
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) h2) h64)⟩

/-- **`slicesOf` with `expand` read back**: copy `z` is row `r`'s element `j`, the copies of row `r` in order
    after those of the rows before it — the index column holds `r`, the position column `L r + j`, `L r` the
    row's clamped start. The copies' count fits a `USize`. Hypothesis: `Vals.PickFits` at every row, the
    payload and the copies' count below `2^63` and the count below `USize.size`. -/
theorem slicesOf_copies {B : Obj} {n : USize} (x : Vals (.arr B) n)
    (hf : Vals.PickFits (.arr B) x (List.range n.toNat)) :
    len sE(n, x) < USize.size ∧
    (List.range (len sE(n, x))).map (fun z =>
      ((Column.bitsAt sE(n, x) (z * 8) 8).toNat, (Column.bitsAt sP(n, x) (z * 8) 8).toNat)) =
    (List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then (List.range (sH(x, r, h) - sL(x, r, h))).map fun j => (r, sL(x, r, h) + j) else [] := by
  obtain ⟨p, lo, hi, f⟩ := x
  simp only [Vals.PickFits] at hf
  obtain ⟨hp, hl63, hlU, -⟩ := hf
  dsimp only
  let L : Nat → Nat := fun t => if ht : t < n.toNat then min (max (lo.get ⟨t, ht⟩).toInt 0).toNat p.toNat else 0
  let H : Nat → Nat := fun t => if ht : t < n.toNat then min (max (hi.get ⟨t, ht⟩).toInt 0).toNat p.toNat else 0
  have hL : ∀ t (ht : t < n.toNat), L t = min (max (lo.get ⟨t, ht⟩).toInt 0).toNat p.toNat := fun t ht => dif_pos ht
  have hH : ∀ t (ht : t < n.toNat), H t = min (max (hi.get ⟨t, ht⟩).toInt 0).toNat p.toNat := fun t ht => dif_pos ht
  have hHp : ∀ t, H t ≤ p.toNat := fun t => by
    by_cases ht : t < n.toNat
    · rw [hH t ht]; exact Nat.min_le_right _ _
    · rw [show H t = 0 from dif_neg ht]; exact Nat.zero_le _
  have hW : ((List.range n.toNat).flatMap fun k =>
      if h : k < n.toNat then List.range' (min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
        (min (max (hi.get ⟨k, h⟩).toInt 0).toNat p.toNat - min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
      else []) = (List.range n.toNat).flatMap fun t => List.range' (L t) (H t - L t) := by
    apply flatMap_congr; intro t ht; rw [List.mem_range] at ht
    rw [dif_pos ht, hL t ht, hH t ht]
  rw [hW] at hl63 hlU
  generalize hG : ((List.range n.toNat).flatMap fun t => List.range' (L t) (H t - L t)) = G at hl63 hlU
  have hGl : G.length = ((List.range n.toNat).map fun t => H t - L t).sum := by
    rw [← hG, List.length_flatMap]; simp only [List.length_range']
  have hsd : slicesOf (⟨p, lo, hi, f⟩ : Vals (.arr B) n) = slices p n (longsOf lo) (longsOf hi) := rfl
  rw [hsd]
  generalize hs0 : slices p n (longsOf lo) (longsOf hi) = s
  have hs : ∀ t (ht : t < n.toNat), (Column.bitsAt s.1 (t * 8) 8).toNat = L t ∧
      (Column.bitsAt s.2 (t * 8) 8).toNat = H t - L t := fun t ht => by
    rw [← hs0, ← hsd, hL t ht, hH t ht]; exact slicesOf_get _ hp ht
  have hlen1 : len s.1 = n.toNat := by rw [← hs0]; exact (len_slices ..).1
  have hlen2 : len s.2 = n.toNat := by rw [← hs0]; exact (len_slices ..).2
  have hcS : ∀ t ≤ n.toNat, ((List.range t).map fun s' => (Column.bitsAt s.2 (s' * 8) 8).toNat).sum =
      ((List.range t).map fun t => H t - L t).sum := fun t ht => by
    congr 1; apply List.map_congr_left; intro s' hs'; rw [List.mem_range] at hs'
    exact (hs s' (by omega)).2
  have hT := hcS n.toNat (Nat.le_refl _)
  have hc63 : ∀ t < len s.2, (Column.bitsAt s.2 (t * 8) 8).toNat < 2 ^ 63 := fun t ht => by
    rw [(hs t (hlen2 ▸ ht)).2]; have := hHp t; omega
  have hE := expand_idx (n := n) (cnt := s.2) (by omega) hc63
  have hlenE : len (expandBytes 8 0 (tilLongs n) s.2) = G.length := by
    rw [len_eq_ids, hE, List.length_flatMap, hGl]; simp only [List.length_replicate]; rw [hlen2]; exact hT
  have hEU : len (expandBytes 8 0 (tilLongs n) s.2) < USize.size := by omega
  have hK : (len (expandBytes 8 0 (tilLongs n) s.2)).toUSize.toNat = G.length := by
    rw [USize.toNat_ofNat_of_lt' hEU, hlenE]
  let S : Nat → Nat := fun t => ((List.range t).map fun t => H t - L t).sum
  have hSdef : ∀ t, ((List.range t).map fun t => H t - L t).sum = S t := fun t => rfl
  have hSm : ∀ t ≤ n.toNat, S t ≤ G.length := fun t ht => by rw [hGl]; exact sum_range_le _ ht
  have hSs : ∀ t < n.toNat, S (t + 1) = S t + (H t - L t) := fun t _ => sum_range_succ' _ t
  -- copy `j` of row `t` holds the row `t` and reads payload position `L t + j`
  have hrd : ∀ t < n.toNat, ∀ j < H t - L t,
      (Column.bitsAt (expandBytes 8 0 (tilLongs n) s.2) ((S t + j) * 8) 8).toNat = t ∧
      (Column.bitsAt (add (len (expandBytes 8 0 (tilLongs n) s.2)).toUSize
        (gather 8 s.1 (expandBytes 8 0 (tilLongs n) s.2))
        (sub (len (expandBytes 8 0 (tilLongs n) s.2)).toUSize
          (tilLongs (len (expandBytes 8 0 (tilLongs n) s.2)).toUSize)
          (gather 8 (sub n (sums n s.2) s.2) (expandBytes 8 0 (tilLongs n) s.2)))) ((S t + j) * 8) 8).toNat =
        L t + j := fun t ht j hj => by
    have hz : S t + j < len (expandBytes 8 0 (tilLongs n) s.2) := by
      rw [hlenE]; have := hSm (t + 1) ht; rw [hSs t ht] at this; omega
    have hEt : (Column.bitsAt (expandBytes 8 0 (tilLongs n) s.2) ((S t + j) * 8) 8).toNat = t := by
      have hfl := flatMap_get_at (fun t => List.replicate (Column.bitsAt s.2 (t * 8) 8).toNat t)
        (m := len s.2) (t := t) (q := j) (by omega)
        (by simp only [List.length_replicate]; rw [(hs t ht).2]; exact hj)
      simp only [List.length_replicate] at hfl
      rw [hcS t (by omega), hSdef, List.getElem?_replicate, if_pos (by rw [(hs t ht).2]; exact hj)] at hfl
      have hzl : S t + j < ((List.range (len s.2)).flatMap fun t =>
          List.replicate (Column.bitsAt s.2 (t * 8) 8).toNat t).length := by
        rw [← hE, ← len_eq_ids]; exact hz
      rw [ids_get hE hzl]
      exact Option.some.inj ((List.getElem?_eq_getElem hzl).symm.trans hfl)
    refine ⟨hEt, ?_⟩
    have hg := gather8_get (src := s.1) (idx := (expandBytes 8 0 (tilLongs n) s.2)) (j := S t + j) hz
      (by rw [hEt, hlen1]; exact ht)
    rw [hEt] at hg
    have hr := expand_rank (n := n) (cnt := s.2) (by omega) (by rw [hlen2, hT, ← hGl]; exact hl63) hEU hz
    rw [hEt, hcS t (by omega), hSdef] at hr
    have hK' : (len (expandBytes 8 0 (tilLongs n) s.2)).toUSize.toNat = len (expandBytes 8 0 (tilLongs n) s.2) :=
      USize.toNat_ofNat_of_lt' hEU
    have hLt := (hs t ht).1
    have hHt := hHp t
    rw [add_get (by rw [hK']; exact hz) (by rw [hg, hr, hLt]; omega), hg, hr, hLt]; omega
  refine ⟨hEU, ?_⟩
  have hR : ((List.range n.toNat).flatMap fun r => if h : r < n.toNat then
      (List.range (min (max (hi.get ⟨r, h⟩).toInt 0).toNat p.toNat - min (max (lo.get ⟨r, h⟩).toInt 0).toNat p.toNat)).map
        fun j => (r, min (max (lo.get ⟨r, h⟩).toInt 0).toNat p.toNat + j) else []) =
      (List.range n.toNat).flatMap fun t => (List.range (H t - L t)).map fun j => (t, L t + j) := by
    apply flatMap_congr; intro t ht; rw [List.mem_range] at ht
    rw [dif_pos ht, hL t ht, hH t ht]
  rw [hR]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, hlenE, hGl, List.length_flatMap]
    simp only [List.length_map, List.length_range]
  · intro z h1 h2
    rw [List.getElem_map, List.getElem_range]
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem h2]
    have hz : z < len (expandBytes 8 0 (tilLongs n) s.2) := by simpa using h1
    obtain ⟨t, ht, ha, hb, hc⟩ := flatMap_get (fun t => (List.range (H t - L t)).map fun j => (t, L t + j))
      n.toNat z (by simp only [List.length_map, List.length_range]; rw [← hGl, ← hlenE]; exact hz)
    simp only [List.length_map, List.length_range, hSdef] at ha hb hc
    rw [hc, List.getElem?_map, List.getElem?_range (by omega), Option.map_some]
    obtain ⟨e1, e2⟩ := hrd t ht (z - S t) (by omega)
    rw [Nat.add_sub_cancel' ha] at e1 e2
    rw [e1, e2]

/-- **Each copy is an element of a row**: copy `z` holds a row `r` and reads that row's element `j` at `L r + j`. -/
theorem copy_row {B : Obj} {n : USize} (x : Vals (.arr B) n) (hf : Vals.PickFits (.arr B) x (List.range n.toNat))
    {z : Nat} (hz : z < len sE(n, x)) :
    ∃ r, ∃ hr : r < n.toNat, ∃ j < sH(x, r, hr) - sL(x, r, hr),
      (Column.bitsAt sE(n, x) (z * 8) 8).toNat = r ∧ (Column.bitsAt sP(n, x) (z * 8) 8).toNat = sL(x, r, hr) + j := by
  have hm := List.mem_map_of_mem (f := fun z =>
    ((Column.bitsAt sE(n, x) (z * 8) 8).toNat, (Column.bitsAt sP(n, x) (z * 8) 8).toNat)) (List.mem_range.2 hz)
  rw [(slicesOf_copies x hf).2] at hm
  obtain ⟨r, hr, hmem⟩ := List.mem_flatMap.1 hm
  rw [List.mem_range] at hr; rw [dif_pos hr] at hmem
  obtain ⟨j, hj, hje⟩ := List.mem_map.1 hmem
  rw [List.mem_range] at hj
  exact ⟨r, hr, j, hj, (Prod.mk.inj hje).1.symm, (Prod.mk.inj hje).2.symm⟩

/-- **Each element of a row is a copy**: row `r`'s element `j` is some copy `z`, read at `L r + j`. -/
theorem row_copy {B : Obj} {n : USize} (x : Vals (.arr B) n) (hf : Vals.PickFits (.arr B) x (List.range n.toNat))
    {r : Nat} (hr : r < n.toNat) {j : Nat} (hj : j < sH(x, r, hr) - sL(x, r, hr)) :
    ∃ z < len sE(n, x),
      (Column.bitsAt sE(n, x) (z * 8) 8).toNat = r ∧ (Column.bitsAt sP(n, x) (z * 8) 8).toNat = sL(x, r, hr) + j := by
  have hm : (r, sL(x, r, hr) + j) ∈ (List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then (List.range (sH(x, r, h) - sL(x, r, h))).map fun j => (r, sL(x, r, h) + j) else [] :=
    List.mem_flatMap.2 ⟨r, List.mem_range.2 hr, by rw [dif_pos hr]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩
  rw [← (slicesOf_copies x hf).2] at hm
  obtain ⟨z, hz, hze⟩ := List.mem_map.1 hm
  exact ⟨z, List.mem_range.1 hz, (Prod.mk.inj hze).1, (Prod.mk.inj hze).2⟩

/-- **The index column lists each row once per element**, in row order: the rows `mem` picks its keys at. -/
theorem copies_rows {B : Obj} {n : USize} (x : Vals (.arr B) n) (hf : Vals.PickFits (.arr B) x (List.range n.toNat)) :
    (List.range (len sE(n, x)).toUSize.toNat).map (fun q => (Column.bitsAt sE(n, x) (q * 8) 8).toNat) =
      (List.range n.toNat).flatMap fun r => if h : r < n.toNat then List.replicate (x.row ⟨r, h⟩).length r else [] := by
  rw [USize.toNat_ofNat_of_lt' (slicesOf_copies x hf).1]
  have h := congrArg (List.map Prod.fst) (slicesOf_copies x hf).2
  rw [List.map_map, List.map_flatMap] at h
  refine h.trans (flatMap_congr fun r hr => ?_)
  rw [List.mem_range] at hr
  rw [dif_pos hr, dif_pos hr, List.map_map, arr_row, List.length_map, List.length_range]
  exact List.ext_getElem (by simp) (by simp)

/-- **The position column lists each row's clamped window**, in row order: the payload positions `mem` picks its
    values at, the windows `Vals.PickFits` names. -/
theorem copies_pos {B : Obj} {n : USize} (x : Vals (.arr B) n) (hf : Vals.PickFits (.arr B) x (List.range n.toNat)) :
    (List.range (len sE(n, x)).toUSize.toNat).map (fun q => (Column.bitsAt sP(n, x) (q * 8) 8).toNat) =
      (List.range n.toNat).flatMap fun r =>
        if h : r < n.toNat then List.range' sL(x, r, h) (sH(x, r, h) - sL(x, r, h)) else [] := by
  rw [USize.toNat_ofNat_of_lt' (slicesOf_copies x hf).1]
  have h := congrArg (List.map Prod.snd) (slicesOf_copies x hf).2
  rw [List.map_map, List.map_flatMap] at h
  refine h.trans (flatMap_congr fun r hr => ?_)
  rw [List.mem_range] at hr
  rw [dif_pos hr, dif_pos hr, List.map_map, List.range'_eq_map_range]
  rfl

/-- `Vals.PickFits` at an array side gives the payload's: below `2^63` and fitting at the rows' windows. -/
theorem pickFits_payload {B : Obj} {n : USize} (x : Vals (.arr B) n) {ps : List Nat}
    (hf : Vals.PickFits (.arr B) x ps) :
    x.1.toNat < 2 ^ 63 ∧ Vals.PickFits B x.2.2.2 (ps.flatMap fun r =>
      if h : r < n.toNat then List.range' sL(x, r, h) (sH(x, r, h) - sL(x, r, h)) else []) := by
  obtain ⟨p, lo, hi, f⟩ := x
  simp only [Vals.PickFits] at hf
  exact ⟨hf.1, hf.2.2.2⟩

#print axioms slicesOf_copies
#print axioms copy_row
#print axioms row_copy
#print axioms copies_rows
#print axioms copies_pos

end LeetQ.Rel.Alg
