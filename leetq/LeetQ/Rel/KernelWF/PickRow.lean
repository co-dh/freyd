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
    exact ⟨UInt64.toNat_ofNat_of_lt' (by omega), UInt64.toNat_ofNat_of_lt' (by omega)⟩
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
  subst hsd
  simp only [Vals.pick, expand, need]
  rw [dif_pos hEU]
  trace_state
  sorry

end LeetQ.Rel.Alg
