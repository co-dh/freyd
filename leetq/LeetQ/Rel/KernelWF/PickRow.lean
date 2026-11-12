/-
  `Vals.pick` read back at every shape: row `q` of a side picked at the index column `i` is the side's row
  `i[q]` where that is below the count, else `Obj.dflt` — under `Vals.PickFits` at the rows `i` names.
-/
import LeetQ.Rel.KernelWF.RowsSpec
import LeetQ.Rel.KernelWF.MemberSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]

/-- A long column's dense payload, long `k`, is its element `k`. -/
theorem longsOf_get {n : USize} (x : Arr .long n) {k : Nat} (hk : k < n.toNat) :
    Column.bitsAt (longsOf x) (k * 8) 8 = (x.get ⟨k, hk⟩).toUInt64 := by
  obtain ⟨ws, hws⟩ : ∃ ws, longWords n x.enc = some ws := by
    rcases KernelWF.long_cases x.wf with ⟨b, h⟩ | ⟨M, P, h⟩ <;> simp [longWords, h]
  obtain ⟨B, hB, -, hE, hS⟩ := Arr.dense_long x hws
  have hL : longsOf x = B := by
    have e : longBytes n x.enc = some B := by
      rcases hB with h | ⟨md, pk, h, rfl⟩ <;> simp only [longBytes, h] <;> rfl
    exact Option.some_inj.1 ((Option.some_get _).trans e)
  subst hE
  have hw : k < (elemsW 8 B).length := by simp [elemsW, hS, hk]
  rw [Arr.get_long x hws k hk hw, hL]
  simp only [elemsW, List.getElem_map, List.getElem_range]; rfl

/-- A long column picked at `i`, element `q`: element `i[q]` at a hit, the null at a miss. -/
theorem pickArr_long_get {n : USize} (x : Arr .long n) (i : ByteArray) (m : USize) (h : len i = m.toNat)
    (q : Fin m.toNat) :
    (pickArr .long ⟨n, x⟩ i m h).get q =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then x.get ⟨_, hin⟩ else @default (El .long) Dep.instInhabitedCarrier := by
  split
  · exact pickArr_get _ i m h q ‹_›
  · refine pickArr_get_miss ⟨n, x⟩ i m h (fun d o ids he => ?_) q (Nat.le_of_not_lt ‹_›)
    rcases KernelWF.long_cases x.wf with ⟨b, h'⟩ | ⟨M, P, h'⟩ <;> rw [h'] at he <;> cases he

/-- `longsN` reads back its payload's first `m` longs. -/
theorem longsN_get {m : USize} {b : ByteArray} (hh : m.toNat ≤ len b) (q : Fin m.toNat) :
    (longsN m b hh).get q = (Column.bitsAt b (q.1 * 8) 8).toInt64 := by
  unfold longsN; rw [cast_get]
  have hq := q.2
  unfold longCol need
  split
  · rw [Arr.get_long_bytes _ rfl]; dsimp only
    rw [bitsAt_extract _ (by rw [fit_len hh]; omega), Nat.zero_add]
    unfold fit; split
    · rfl
    · rw [bitsAt_extract _ (by omega), Nat.zero_add]
  · rename_i hn; exact absurd (by rw [fit_len hh]; exact m.toNat_lt_size) hn

/-- An array row, as a list: the payload from its clamped start, its clamped count long. -/
theorem arr_row {b : Obj} {m : USize} (x : Vals (.arr b) m) (q : Fin m.toNat) :
    Vals.row x q = (List.range (min (max (x.2.2.1.get q).toInt 0).toNat x.1.toNat -
        min (max (x.2.1.get q).toInt 0).toNat x.1.toNat)).map fun j =>
      if h : min (max (x.2.1.get q).toInt 0).toNat x.1.toNat + j < x.1.toNat then
        Vals.row x.2.2.2 ⟨_, h⟩ else b.dflt := by
  obtain ⟨p, lo, hi, f⟩ := x
  show List.filterMap _ _ = _
  rw [filterMap_window b.dflt, List.range'_eq_map_range, List.map_map]
  rfl

set_option maxHeartbeats 1000000 in
/-- **`Vals.pick` read back at an atom**, hit or miss: `pickArr_get`, and `pickArr_get_miss` at every
    encoding but an interned symbol column. -/
theorem pick_row_atom_dflt {t : QAtomicType} {n : USize} (x : Vals (.atom t) n)
    (hne : ∀ d o ids, Arr.enc x ≠ .enum d o ids) (i : ByteArray) (m : USize) (h : len i = m.toNat)
    (q : Fin m.toNat) :
    (Vals.pick (.atom t) x i m h).row q =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then x.row ⟨_, hin⟩ else (Obj.atom t).dflt := by
  split
  · exact pickArr_get ⟨_, x⟩ i m h q ‹_›
  · exact pickArr_get_miss ⟨_, x⟩ i m h hne q (Nat.le_of_not_lt ‹_›)

/-- **`Vals.pick` read back at a product**, hit or miss, from its two components'. -/
theorem pick_row_prod_dflt {a b : Obj} {n : USize} (x : Vals (.prod a b) n) (i : ByteArray) (m : USize)
    (h : len i = m.toNat) (q : Fin m.toNat)
    (h1 : (Vals.pick a x.1 i m h).row q =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then x.1.row ⟨_, hin⟩ else a.dflt)
    (h2 : (Vals.pick b x.2 i m h).row q =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then x.2.row ⟨_, hin⟩ else b.dflt) :
    (Vals.pick (.prod a b) x i m h).row q =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then x.row ⟨_, hin⟩ else (Obj.prod a b).dflt := by
  show (Vals.row (Vals.pick a x.1 i m h) q, Vals.row (Vals.pick b x.2 i m h) q) = _
  rw [h1, h2]; split <;> rfl

/-- **`widen` of a bitmap to longs**, long `q`: `1` where bit `q` is set, else `0` — a sum's tags as `τ`. -/
theorem widen_bits_get (tb : ByteArray) (m : USize) {q : Nat} (hq : q < m.toNat) :
    Column.bitsAt (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m) (q * 8) 8 =
      if Column.bitAt tb q then 1 else 0 := by
  let g : Nat → UInt64 := fun i => if Column.bitAt tb i then 1 else 0
  have hf : Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m =
      (List.range m.toNat).foldl (fun acc i => Column.pushBits acc (g i) 8) ByteArray.empty := by
    unfold Kernel.Ew.widen
    congr 1; funext acc i
    rw [if_neg (by decide), if_neg (by decide)]
    unfold Ew.widenRead; rw [if_pos (by decide)]
    simp only [g]
    cases Column.bitAt tb i <;> rfl
  obtain ⟨-, -, hg⟩ := foldl_pushBits g 8 (by decide) (List.range m.toNat) ByteArray.empty
  have := hg q (by simpa using hq)
  rw [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at this
  rw [hf, Nat.mul_comm, this]
  simp only [g]; cases Column.bitAt tb q <;> rfl

/-- **`Vals.pick` read back at an array side**, from its payload's: the picked rows' clamped slices are
    gathered one after another, so row `q`'s new slice is its old one, copied. -/
theorem pick_row_arr {b : Obj} {n : USize} (x : Vals (.arr b) n)
    (ih : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat),
      Vals.PickFits b x.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat) →
      ∀ q : Fin m.toNat, (Vals.pick b x.2.2.2 i m h).row q =
        if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < x.1.toNat then Vals.row x.2.2.2 ⟨_, hin⟩ else b.dflt)
    (i : ByteArray) (m : USize) (h : len i = m.toNat)
    (hf : Vals.PickFits (.arr b) x ((List.range m.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat))
    (q : Fin m.toNat) :
    (Vals.pick (.arr b) x i m h).row q =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then x.row ⟨_, hin⟩ else (Obj.arr b).dflt := by
  obtain ⟨p, lo, hi, f⟩ := x
  simp only [Vals.PickFits] at hf
  obtain ⟨hp, hl63, hlU, hfb⟩ := hf
  -- row `t`'s picked `lo`/`hi`, clamped into `[0, p]`
  let L : Nat → Nat := fun t => if ht : t < m.toNat then
    min (max ((pickArr .long ⟨n, lo⟩ i m h).get ⟨t, ht⟩).toInt 0).toNat p.toNat else 0
  let H : Nat → Nat := fun t => if ht : t < m.toNat then
    min (max ((pickArr .long ⟨n, hi⟩ i m h).get ⟨t, ht⟩).toInt 0).toNat p.toNat else 0
  have hL : ∀ t (ht : t < m.toNat), L t =
      min (max ((pickArr .long ⟨n, lo⟩ i m h).get ⟨t, ht⟩).toInt 0).toNat p.toNat := fun t ht => dif_pos ht
  have hH : ∀ t (ht : t < m.toNat), H t =
      min (max ((pickArr .long ⟨n, hi⟩ i m h).get ⟨t, ht⟩).toInt 0).toNat p.toNat := fun t ht => dif_pos ht
  have hLp : ∀ t, L t ≤ p.toNat := fun t => by
    by_cases ht : t < m.toNat
    · rw [hL t ht]; exact Nat.min_le_right _ _
    · rw [show L t = 0 from dif_neg ht]; exact Nat.zero_le _
  have hHp : ∀ t, H t ≤ p.toNat := fun t => by
    by_cases ht : t < m.toNat
    · rw [hH t ht]; exact Nat.min_le_right _ _
    · rw [show H t = 0 from dif_neg ht]; exact Nat.zero_le _
  -- the windows `PickFits` names are those slices
  have hW : ((List.range m.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat).flatMap (fun k =>
      if h : k < n.toNat then List.range' (min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
        (min (max (hi.get ⟨k, h⟩).toInt 0).toNat p.toNat - min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
      else []) = (List.range m.toNat).flatMap fun t => List.range' (L t) (H t - L t) := by
    rw [List.flatMap_map]
    apply flatMap_congr; intro t ht; rw [List.mem_range] at ht
    rw [hL t ht, hH t ht, pickArr_long_get, pickArr_long_get]
    split
    · rfl
    · simp
  rw [hW] at hl63 hlU hfb
  generalize hG : ((List.range m.toNat).flatMap fun t => List.range' (L t) (H t - L t)) = G at hl63 hlU hfb
  have hGl : G.length = ((List.range m.toNat).map fun t => H t - L t).sum := by
    rw [← hG, List.length_flatMap]; simp only [List.length_range']
  obtain ⟨s, hsd⟩ : ∃ s, slices p m (longsOf (pickArr .long ⟨n, lo⟩ i m h))
    (longsOf (pickArr .long ⟨n, hi⟩ i m h)) = s := ⟨_, rfl⟩
  have hs : ∀ t (ht : t < m.toNat), (Column.bitsAt s.1 (t * 8) 8).toNat = L t ∧
      (Column.bitsAt s.2 (t * 8) 8).toNat = H t - L t := fun t ht => by
    have hsl := slices_get (n := m) hp (longsOf (pickArr .long ⟨n, lo⟩ i m h))
      (longsOf (pickArr .long ⟨n, hi⟩ i m h)) ht
    rw [longsOf_get _ ht, longsOf_get _ ht, Int64.toInt64_toUInt64, Int64.toInt64_toUInt64, hsd,
      ← hL t ht, ← hH t ht] at hsl
    have h1 := hLp t; have h2 := hHp t
    rw [hsl.1, hsl.2]
    have h64 : p.toNat < UInt64.size := Nat.lt_trans hp (by decide)
    exact ⟨UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h1 h64),
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) h2) h64)⟩
  have hlen1 : len s.1 = m.toNat := by rw [← hsd]; exact (len_slices ..).1
  have hlen2 : len s.2 = m.toNat := by rw [← hsd]; exact (len_slices ..).2
  -- the counts' prefix totals are the windows' (`S t` below)
  have hcS : ∀ t ≤ m.toNat, ((List.range t).map fun s' => (Column.bitsAt s.2 (s' * 8) 8).toNat).sum =
      ((List.range t).map fun t => H t - L t).sum := fun t ht => by
    congr 1; apply List.map_congr_left; intro s' hs'; rw [List.mem_range] at hs'
    exact (hs s' (by omega)).2
  have hT := hcS m.toNat (Nat.le_refl _)
  have hc63 : ∀ t < len s.2, (Column.bitsAt s.2 (t * 8) 8).toNat < 2 ^ 63 := fun t ht => by
    rw [(hs t (hlen2 ▸ ht)).2]; have := hHp t; omega
  have hE := expand_idx (n := m) (cnt := s.2) (by omega) hc63
  have hlenE : len (expandBytes 8 0 (tilLongs m) s.2) = G.length := by
    rw [len_eq_ids, hE, List.length_flatMap, hGl]; simp only [List.length_replicate]; rw [hlen2]; exact hT
  have hEU : len (expandBytes 8 0 (tilLongs m) s.2) < USize.size := by omega
  have hK : (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize.toNat = G.length := by
    rw [USize.toNat_ofNat_of_lt' hEU, hlenE]
  -- `S t`: the copies before row `t`'s
  let S : Nat → Nat := fun t => ((List.range t).map fun t => H t - L t).sum
  have hSdef : ∀ t, ((List.range t).map fun t => H t - L t).sum = S t := fun t => rfl
  have hSm : ∀ t ≤ m.toNat, S t ≤ G.length := fun t ht => by rw [hGl]; exact sum_range_le _ ht
  have hSs : ∀ t < m.toNat, S (t + 1) = S t + (H t - L t) := fun t _ => sum_range_succ' _ t
  have hsums : ∀ t < m.toNat, (Column.bitsAt (sums m s.2) (t * 8) 8).toNat = S (t + 1) := fun t ht => by
    have hS1 := hSm (t + 1) ht
    rw [sums_get ht (by omega) (by rw [hcS (t + 1) ht]; exact Nat.lt_of_le_of_lt hS1 hl63), hcS (t + 1) ht]
  have hlo' : ∀ q : Fin m.toNat,
      ((valCol (n := m) Ew.sub Ew.vv (sums m s.2) s.2).get q).toInt = ((S q : Nat) : Int) := fun q => by
    have hq := q.2; have e1 := hsums q hq; have e2 := (hs q hq).2; have e3 := hSs q hq
    have e4 := hSm (q + 1) hq
    have hsub := sub_get (n := m) (a := sums m s.2) (b := s.2) hq (by omega) (by omega)
    rw [Arr.get_long_bytes _ rfl]
    show (Column.bitsAt (sub m (sums m s.2) s.2) (q.1 * 8) 8).toInt64.toInt = _
    rw [toInt64_toInt (by omega), hsub]; omega
  have hhi' : ∀ (hh : m.toNat ≤ len (sums m s.2)) (q : Fin m.toNat),
      ((longsN m (sums m s.2) hh).get q).toInt = ((S q + (H q - L q) : Nat) : Int) := fun hh q => by
    have hq := q.2; have e1 := hsums q hq; have e3 := hSs q hq; have e4 := hSm (q + 1) hq
    rw [longsN_get, toInt64_toInt (by omega)]; omega
  have eS : ∀ q : Fin m.toNat, min (max ((S q : Nat) : Int) 0).toNat
      (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize.toNat = S q := fun q => by
    have := hSm q (Nat.le_of_lt q.2); rw [hK]; omega
  have eH : ∀ q : Fin m.toNat, min (max ((S q + (H q - L q) : Nat) : Int) 0).toNat
      (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize.toNat = S q + (H q - L q) := fun q => by
    have := hSm (q + 1) q.2; have := hSs q q.2; rw [hK]; omega
  -- copy `j` of row `t`'s slice reads payload position `L t + j`
  have hrd : ∀ t < m.toNat, ∀ j < H t - L t,
      (Column.bitsAt (add (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize
        (gather 8 s.1 (expandBytes 8 0 (tilLongs m) s.2))
        (sub (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize
          (tilLongs (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize)
          (gather 8 (sub m (sums m s.2) s.2) (expandBytes 8 0 (tilLongs m) s.2)))) ((S t + j) * 8) 8).toNat =
        L t + j := fun t ht j hj => by
    have hz : S t + j < len (expandBytes 8 0 (tilLongs m) s.2) := by
      rw [hlenE]; have := hSm (t + 1) ht; rw [hSs t ht] at this; omega
    have hEt : (Column.bitsAt (expandBytes 8 0 (tilLongs m) s.2) ((S t + j) * 8) 8).toNat = t := by
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
    have hg := gather8_get (src := s.1) (idx := (expandBytes 8 0 (tilLongs m) s.2)) (j := S t + j) hz
      (by rw [hEt, hlen1]; exact ht)
    rw [hEt] at hg
    have hr := expand_rank (n := m) (cnt := s.2) (by omega) (by rw [hlen2, hT, ← hGl]; exact hl63) hEU hz
    rw [hEt, hcS t (by omega), hSdef] at hr
    have hK' : (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize.toNat = len (expandBytes 8 0 (tilLongs m) s.2) :=
      USize.toNat_ofNat_of_lt' hEU
    have hLt := (hs t ht).1
    have hHt := hHp t
    rw [add_get (by rw [hK']; exact hz) (by rw [hg, hr, hLt]; omega), hg, hr, hLt]; omega
  -- so the payload is picked at the windows `PickFits` names
  have hI : (List.range (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize.toNat).map (fun z =>
      (Column.bitsAt (add (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize
        (gather 8 s.1 (expandBytes 8 0 (tilLongs m) s.2))
        (sub (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize
          (tilLongs (len (expandBytes 8 0 (tilLongs m) s.2)).toUSize)
          (gather 8 (sub m (sums m s.2) s.2) (expandBytes 8 0 (tilLongs m) s.2)))) (z * 8) 8).toNat) = G := by
    apply List.ext_getElem (by rw [List.length_map, List.length_range, hK])
    intro z h1 h2
    rw [List.getElem_map, List.getElem_range]
    obtain ⟨t, ht, ha, hb, hc⟩ := flatMap_get (fun t => List.range' (L t) (H t - L t)) m.toNat z
      (by simp only [List.length_range']; rw [← hGl]; exact h2)
    simp only [List.length_range', hSdef] at ha hb hc
    rw [hG] at hc
    have hz := hrd t ht (z - S t) (by omega)
    rw [Nat.add_sub_cancel' ha] at hz
    rw [hz]
    have hc' := (List.getElem?_eq_getElem h2).symm.trans hc
    rw [List.getElem?_eq_getElem (by simp only [List.length_range']; omega), List.getElem_range'] at hc'
    rw [(Option.some.inj hc'), Nat.one_mul]
  subst hsd
  simp only [Vals.pick, expand, need]
  rw [dif_pos hEU, arr_row]
  simp only [hlo', hhi', eS, eH, Nat.add_sub_cancel_left]
  by_cases hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat
  · have eL : L q = min (max (lo.get ⟨_, hin⟩).toInt 0).toNat p.toNat := by
      rw [hL q q.2, pickArr_long_get, dif_pos hin]
    have eH' : H q = min (max (hi.get ⟨_, hin⟩).toInt 0).toNat p.toNat := by
      rw [hH q q.2, pickArr_long_get, dif_pos hin]
    rw [dif_pos hin, arr_row]
    dsimp only
    rw [← eL, ← eH']
    apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    have hHq := hHp q; have := hSm (q + 1) q.2; have := hSs q q.2
    rw [dif_pos (show S q + j < _ by rw [hK]; omega), dif_pos (show L q + j < p.toNat by omega)]
    refine (ih _ _ _ (by rw [hI]; exact hfb) _).trans ?_
    dsimp only
    rw [dif_pos (by rw [hrd q q.2 j hj]; omega)]
    exact congrArg f.row (Fin.ext (hrd q q.2 j hj))
  · have e0 : H q - L q = 0 := by
      rw [hL q q.2, hH q q.2, pickArr_long_get, pickArr_long_get, dif_neg hin, dif_neg hin, Nat.sub_self]
    rw [dif_neg hin, e0]; rfl

end LeetQ.Rel.Alg
