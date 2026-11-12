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

/-- `widen` of a bitmap to longs is one push per bit: `1` where it is set, else `0`. -/
theorem widen_bits_eq (tb : ByteArray) (m : USize) :
    Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m = (List.range m.toNat).foldl
      (fun acc i => Column.pushBits acc (if Column.bitAt tb i then 1 else 0) 8) ByteArray.empty := by
  unfold Kernel.Ew.widen
  congr 1; funext acc i
  rw [if_neg (by decide), if_neg (by decide)]
  unfold Ew.widenRead; rw [if_pos (by decide)]
  cases Column.bitAt tb i <;> rfl

/-- `widen` of a bitmap at `m` answers `m` longs. -/
theorem len_widen_bits (tb : ByteArray) (m : USize) :
    len (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m) = m.toNat := by
  obtain ⟨hs, -, -⟩ := foldl_pushBits (fun i => if Column.bitAt tb i then (1 : UInt64) else 0) 8 (by decide)
    (List.range m.toNat) ByteArray.empty
  rw [len, widen_bits_eq, hs]; simp

/-- **`widen` of a bitmap to longs**, long `q`: `1` where bit `q` is set, else `0` — a sum's tags as `τ`. -/
theorem widen_bits_get (tb : ByteArray) (m : USize) {q : Nat} (hq : q < m.toNat) :
    Column.bitsAt (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m) (q * 8) 8 =
      if Column.bitAt tb q then 1 else 0 := by
  let g : Nat → UInt64 := fun i => if Column.bitAt tb i then 1 else 0
  have hf : Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m =
      (List.range m.toNat).foldl (fun acc i => Column.pushBits acc (g i) 8) ByteArray.empty :=
    widen_bits_eq tb m
  obtain ⟨-, -, hg⟩ := foldl_pushBits g 8 (by decide) (List.range m.toNat) ByteArray.empty
  have := hg q (by simpa using hq)
  rw [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at this
  rw [hf, Nat.mul_comm, this]
  simp only [g]; cases Column.bitAt tb q <;> rfl

/-- **A row's rank among the set bits**: `sums τ - τ` at `q` counts the set bits before `q`, `τ` the
    bitmap widened, the count below `2^63`. -/
theorem rank_get (tb : ByteArray) (m : USize) (hm : m.toNat < 2 ^ 63) {q : Nat} (hq : q < m.toNat) :
    (Column.bitsAt (sub m (sums m (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m))
      (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m)) (q * 8) 8).toNat =
      ((List.range q).filter (Column.bitAt tb)).length := by
  have hτ : ∀ j < m.toNat, (Column.bitsAt (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m) (j * 8) 8).toNat =
      if Column.bitAt tb j then 1 else 0 := fun j hj => by
    rw [widen_bits_get tb m hj]; split <;> rfl
  have hsum : ∀ k ≤ m.toNat, ((List.range k).map fun j =>
      (Column.bitsAt (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m) (j * 8) 8).toNat).sum =
      ((List.range k).filter (Column.bitAt tb)).length := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [sum_range_succ', ih (by omega), hτ k (by omega), List.range_succ, List.filter_append, List.length_append]
      cases h : Column.bitAt tb k <;> simp [h]
  have hf : ∀ k, ((List.range k).filter (Column.bitAt tb)).length ≤ k := fun k =>
    Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hl := len_widen_bits tb m
  have hs := sums_get (n := m) (b := Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m) hq (by omega)
    (by rw [hsum (q + 1) hq]; have := hf (q + 1); omega)
  rw [hsum (q + 1) hq] at hs
  have hS := sum_range_succ' (fun j => (Column.bitsAt (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m) (j * 8) 8).toNat) q
  rw [hsum (q + 1) hq, hsum q (by omega)] at hS
  have hfq := hf (q + 1)
  rw [sub_get hq (by rw [hs]; omega) (by rw [hs, hS]; omega), hs, hS]; omega

/-- **The `k`-th set position is `q`**, where `k` counts the set positions before `q`. -/
theorem filter_range_rank (P : Nat → Bool) {m q : Nat} (hq : q < m) (hP : P q = true) :
    ((List.range m).filter P)[((List.range q).filter P).length]? = some q := by
  obtain ⟨k, rfl⟩ : ∃ k, m = q + 1 + k := ⟨m - q - 1, by omega⟩
  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append, List.filter_cons_of_pos hP,
    List.filter_nil, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- **A picked tag column's bitmap**, bit `q`: row `i[q]`'s tag at a hit, `false` (the boolean null) at a
    miss — what `Vals.pick` at a sum widens and splits the rows by. -/
theorem pickArr_tag_bit {n : USize} (tag : Arr .boolean n) (i : ByteArray) (m : USize) (h : len i = m.toNat)
    (q : Fin m.toNat) :
    Column.bitAt (tagBits (pickArr .boolean ⟨n, tag⟩ i m h)) q.1 =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then tag.get ⟨_, hin⟩ else false := by
  rw [← Arr.get_bool_bits _ (KernelWF.enc_tagBits _) q]
  split
  · exact pickArr_get _ i m h q ‹_›
  · refine (pickArr_get_miss ⟨n, tag⟩ i m h (fun d o ids he => ?_) q (Nat.le_of_not_lt ‹_›)).trans rfl
    have hw := tag.wf; rw [he] at hw; simp [Enc.WF] at hw

/-- The long null a picked long column reads at a miss is q's `0N`, `nul`. -/
theorem long_default : (@default (El .long) Dep.instInhabitedCarrier) = nul := rfl

/-- `Ew.val` on longs at `av`, element `i` below the count: `valStep` of `a`'s first long and `b`'s `i`. -/
theorem val_av_get (op : UInt8) (a b : ByteArray) (n : USize) {i : Nat} (hi : i < n.toNat) :
    Column.bitsAt (Kernel.Ew.val op Ew.i64 Ew.av nul a b n) (i * 8) 8 =
      Ew.valStep op Ew.i64 nul.toUInt64 (Column.bitsAt a 0 8) (Column.bitsAt b (i * 8) 8) := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have h := congrArg (·[i]?) (elemsW_val op Ew.i64 Ew.av nul a b n)
  have hs : (Kernel.Ew.val op Ew.i64 Ew.av nul a b n).size / 8 = n.toNat := by
    have := len_val op Ew.av a b n; simpa [len] using this
  simp only [elemsW, hw, hs, List.getElem?_map, List.getElem?_range, hi, Option.map_some,
    Option.some.injEq] at h
  rw [h]
  simp (config := {decide := true}) only [Ew.shapeIdx, Ew.elem, hw, ↓reduceIte, Nat.zero_mul]
  generalize Ew.valStep op Ew.i64 nul.toUInt64 _ _ = v
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ (8 * 8) from v.toNat_lt), UInt64.ofNat_toNat]

/-- **`fill` on longs**: the right operand, or the left where the right is q's null `0N`. -/
theorem valStep_fill (x y : UInt64) :
    Ew.valStep Ew.fill Ew.i64 nul.toUInt64 x y = if y.toInt64 = nul then x else y := by
  by_cases hy : y.toInt64 = nul <;>
    simp (config := {decide := true}) [Ew.valStep, Ew.intStep, Ew.signed, hy] <;> rfl

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

/-! ## The `.sum` case -/

/-- A natural below `2^63` fits a long. -/
theorem lt_size_of_lt63 {v : Nat} (h : v < 2 ^ 63) : v < UInt64.size := Nat.lt_trans h (by decide)

/-- An integer of a long's range is its own residue `bmod 2^64`. -/
theorem bmod_small {z : Int} (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) : z.bmod (2 ^ 64) = z := by
  simp only [Int.bmod]; split <;> omega

/-- Two longs of one signed value are one long. -/
theorem u64_ext {u v : UInt64} (h : u.toInt64.toInt = v.toInt64.toInt) : u = v := by
  rw [← UInt64.toUInt64_toInt64 u, ← UInt64.toUInt64_toInt64 v, Int64.toInt_inj.1 h]

/-- **`valStep` `+`, `-`, `*` on longs, as signed values**: where no operand is q's null `0N` and the
    result is in range, `+` and `-` are the integer ones; `*` by a `1`/`0` is the operand or `0`. -/
theorem valStep_int {x y : UInt64} (hx : -2 ^ 63 < x.toInt64.toInt) (hy : -2 ^ 63 < y.toInt64.toInt) :
    (-2 ^ 63 ≤ x.toInt64.toInt + y.toInt64.toInt → x.toInt64.toInt + y.toInt64.toInt < 2 ^ 63 →
      (Ew.valStep Ew.add Ew.i64 nul.toUInt64 x y).toInt64.toInt = x.toInt64.toInt + y.toInt64.toInt) ∧
    (-2 ^ 63 ≤ x.toInt64.toInt - y.toInt64.toInt → x.toInt64.toInt - y.toInt64.toInt < 2 ^ 63 →
      (Ew.valStep Ew.sub Ew.i64 nul.toUInt64 x y).toInt64.toInt = x.toInt64.toInt - y.toInt64.toInt) ∧
    (∀ t : Bool, x = (if t then 1 else 0) →
      (Ew.valStep Ew.mul Ew.i64 nul.toUInt64 x y).toInt64.toInt = if t then y.toInt64.toInt else 0) := by
  have hxn : x.toInt64 ≠ Int64.minValue := fun e => by rw [e] at hx; exact absurd hx (by decide)
  have hyn : y.toInt64 ≠ Int64.minValue := fun e => by rw [e] at hy; exact absurd hy (by decide)
  have hnul : (nul.toUInt64).toInt64 = Int64.minValue := rfl
  have hyl := Int64.toInt_lt y.toInt64
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.add, Ew.sub, Ew.mul, hnul]
  simp only [↓reduceIte]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun t ht => ?_⟩ <;>
    rw [if_neg (by simp; exact ⟨hxn, hyn⟩), Int64.toInt64_toUInt64]
  · rw [Int64.toInt_add, bmod_small h1 h2]
  · rw [Int64.toInt_sub, bmod_small h1 h2]
  · subst ht; rw [Int64.toInt_mul]
    cases t
    · rw [show (if false = true then (1 : UInt64) else 0).toInt64.toInt = 0 by decide, Int.zero_mul]; rfl
    · rw [show (if true = true then (1 : UInt64) else 0).toInt64.toInt = 1 by decide, Int.one_mul,
        bmod_small (by omega) hyl]; rfl

/-- `valStep` lesser and greater on longs are the signed minimum and maximum. -/
theorem valStep_min_max (x y : UInt64) :
    (Ew.valStep Ew.lesser Ew.i64 nul.toUInt64 x y).toInt64.toInt = min x.toInt64.toInt y.toInt64.toInt ∧
    (Ew.valStep Ew.greater Ew.i64 nul.toUInt64 x y).toInt64.toInt = max x.toInt64.toInt y.toInt64.toInt := by
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.lesser, Ew.greater]
  simp only [↓reduceIte, Int64.toInt64_toUInt64]
  constructor <;> split <;> simp_all [Int64.lt_iff_toInt_lt] <;> omega

/-- `int z`'s long, for `z` in a long's range, has the value `z`. -/
theorem int_bits_toInt (z : Int) (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) :
    (Column.bitsAt (int z) 0 8).toInt64.toInt = z := by
  rw [int, bitsAt_one, Int64.toInt64_toUInt64, Int64.toInt_ofInt, bmod_small h1 h2]

/-- **A sum's new position**, `rl + τ·(rr - rl)` on longs below `2^63`, `τ` the tag as `1`/`0`: `rr` at a
    set tag, `rl` at a clear one — no step reads q's null `0N`. -/
theorem valStep_tau_pick (t : Bool) {x y : UInt64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    Ew.valStep Ew.add Ew.i64 nul.toUInt64 x (Ew.valStep Ew.mul Ew.i64 nul.toUInt64 (if t then 1 else 0)
      (Ew.valStep Ew.sub Ew.i64 nul.toUInt64 y x)) = if t then y else x := by
  have ex := toInt64_toInt hx; have ey := toInt64_toInt hy
  have hs := (valStep_int (x := y) (y := x) (by omega) (by omega)).2.1 (by omega) (by omega)
  have hm := (valStep_int (x := if t then 1 else 0) (y := Ew.valStep Ew.sub Ew.i64 nul.toUInt64 y x)
    (by cases t <;> decide) (by rw [hs]; omega)).2.2 t rfl
  rw [hs] at hm
  have ha := (valStep_int (x := x) (y := Ew.valStep Ew.mul Ew.i64 nul.toUInt64 (if t then 1 else 0)
    (Ew.valStep Ew.sub Ew.i64 nul.toUInt64 y x)) (by omega) (by rw [hm]; split <;> omega)).1
    (by rw [hm]; split <;> omega) (by rw [hm]; split <;> omega)
  apply u64_ext
  rw [ha, hm]
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- **`place` read back** at the sides' counts: row `k`'s position clamped into `[0, c - 1]`, `c` the count
    of the row's side — what `Vals.row` reads a sum row at, and never q's null `0N`. -/
theorem place_get {a b : Obj} {n : USize} (x : Vals (.sum a b) n) (hl : x.1.toNat < 2 ^ 63)
    (hr : x.2.1.toNat < 2 ^ 63) (k : Fin n.toNat) :
    ((place x ((x.1.toNat : Int) - 1) ((x.2.1.toNat : Int) - x.1.toNat) 0 0).get k).toUInt64 =
      UInt64.ofNat (min (max (x.2.2.2.1.get k).toInt 0).toNat
        ((if x.2.2.1.get k then x.2.1.toNat else x.1.toNat) - 1)) := by
  obtain ⟨l, r, tag, idx, xa, xb⟩ := x
  dsimp only at hl hr ⊢
  have hv : min (max (idx.get k).toInt 0).toNat ((if tag.get k then r.toNat else l.toNat) - 1) < 2 ^ 63 := by
    split <;> omega
  unfold place
  rw [Arr.get_long_bytes _ rfl]
  dsimp only
  rw [UInt64.toUInt64_toInt64]
  simp only [val_vv_get _ _ _ _ k.2, val_va_get _ _ _ _ k.2, widen_bits_get _ _ k.2, longsOf_get _ k.2,
    ← Arr.get_bool_bits _ (KernelWF.enc_tagBits tag) k]
  have e0 := int_bits_toInt ((l.toNat : Int) - 1) (by omega) (by omega)
  have e1 := int_bits_toInt ((r.toNat : Int) - l.toNat) (by omega) (by omega)
  have ez := int_bits_toInt 0 (by decide) (by decide)
  have eI := congrArg Int64.toInt (Int64.toInt64_toUInt64 (idx.get k))
  generalize Column.bitsAt (int ((r.toNat : Int) - l.toNat)) 0 8 = K1 at e1 ⊢
  generalize Column.bitsAt (int ((l.toNat : Int) - 1)) 0 8 = K0 at e0 ⊢
  generalize Column.bitsAt (int 0) 0 8 = Z at ez ⊢
  generalize (idx.get k).toUInt64 = I at eI ⊢
  generalize tag.get k = t at hv ⊢
  have hT : -2 ^ 63 < (if t then (1 : UInt64) else 0).toInt64.toInt := by cases t <;> decide
  have m1 := (valStep_int (y := K1) hT (by omega)).2.2 t rfl
  rw [e1] at m1
  have l1 := (valStep_int (y := K0) (by rw [m1]; split <;> omega) (by omega)).1
    (by rw [m1]; split <;> omega) (by rw [m1]; split <;> omega)
  rw [m1, e0] at l1
  have mz := (valStep_int (y := Z) hT (by omega)).2.2 t rfl
  rw [ez] at mz
  have az := (valStep_int (y := Z) (by rw [mz]; split <;> decide) (by omega)).1
    (by rw [mz]; split <;> omega) (by rw [mz]; split <;> omega)
  rw [mz, ez] at az
  generalize Ew.valStep Ew.add Ew.i64 nul.toUInt64 (Ew.valStep Ew.mul Ew.i64 nul.toUInt64 (if t then 1 else 0) K1) K0
    = LIN at l1 ⊢
  generalize Ew.valStep Ew.add Ew.i64 nul.toUInt64 (Ew.valStep Ew.mul Ew.i64 nul.toUInt64 (if t then 1 else 0) Z) Z
    = Z2 at az ⊢
  have hles := (valStep_min_max I LIN).1
  generalize Ew.valStep Ew.lesser Ew.i64 nul.toUInt64 I LIN = LES at hles ⊢
  have hgre := (valStep_min_max LES Z).2
  generalize Ew.valStep Ew.greater Ew.i64 nul.toUInt64 LES Z = G at hgre ⊢
  have hfin := (valStep_int (x := G) (y := Z2) (by rw [hgre]; omega) (by rw [az]; split <;> omega)).1
    (by rw [hgre, az]; split <;> omega) (by rw [hgre, hles, az, ez, l1]; split <;> omega)
  apply u64_ext
  rw [hfin, toInt64_toInt (x := UInt64.ofNat _)
      (by rw [UInt64.toNat_ofNat_of_lt' (lt_size_of_lt63 hv)]; exact hv),
    UInt64.toNat_ofNat_of_lt' (lt_size_of_lt63 hv), hgre, hles, az, ez, l1, eI]
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- `filterMap` of a two-way choice is the kept elements, mapped. -/
theorem filterMap_ite {α β : Type} (P : α → Bool) (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = if P a then some (g a) else none) → l.filterMap f = (l.filter P).map g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, h a (by simp), filterMap_ite P f g l fun x hx => h x (by simp [hx])]
    cases hP : P a <;> simp [hP]

/-- The positions below `q` split by a predicate: those kept and those dropped count `q`. -/
theorem filter_range_split (f : Nat → Bool) (q : Nat) :
    ((List.range q).filter f).length + ((List.range q).filter fun t => !f t).length = q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [List.range_succ, List.filter_append, List.filter_append]; cases h : f q <;> simp [h] <;> omega

/-- **A long payload gathered at the set bits**, read back: its longs at the set positions, in order. -/
theorem gather_whereBits (p bits : ByteArray) (m : USize) (hp : len p = m.toNat) :
    (List.range (len (gather 8 p (whereBits m bits)))).map
        (fun z => (Column.bitsAt (gather 8 p (whereBits m bits)) (z * 8) 8).toNat) =
      ((List.range m.toNat).filter (Column.bitAt bits)).map fun t => (Column.bitsAt p (t * 8) 8).toNat := by
  obtain ⟨hs, hg⟩ := Verify.whereBits_spec m bits
  have hl : len (whereBits m bits) = ((List.range m.toNat).filter (Column.bitAt bits)).length := by
    simp only [len, hs]; omega
  apply List.ext_getElem (by simp [gather_len, hl])
  intro z h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have hz : z < len (whereBits m bits) := by simpa [gather_len] using h1
  have hmem := List.getElem_mem (l := (List.range m.toNat).filter (Column.bitAt bits)) (n := z) (h := by omega)
  rw [List.mem_filter, List.mem_range] at hmem
  rw [gather8_get hz (by rw [hg z (by omega), hp]; exact hmem.1), hg z (by omega)]

/-- **A sum's new position column**, `rl + τ·(rr - rl)`, row `q`: `rr`'s long where the tag is set, else
    `rl`'s, both below `2^63`. -/
theorem tau_pick_get (tb rr rl : ByteArray) (m : USize) (q : Fin m.toNat)
    (hr : (Column.bitsAt rr (q.1 * 8) 8).toNat < 2 ^ 63) (hl : (Column.bitsAt rl (q.1 * 8) 8).toNat < 2 ^ 63) :
    ((valCol (n := m) Ew.add Ew.vv rl
      (Kernel.Ew.val Ew.mul Ew.i64 Ew.vv nul (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m) (sub m rr rl) m)).get q).toInt =
      ((if Column.bitAt tb q.1 then (Column.bitsAt rr (q.1 * 8) 8).toNat
        else (Column.bitsAt rl (q.1 * 8) 8).toNat : Nat) : Int) := by
  rw [Arr.get_long_bytes _ rfl]
  show (Column.bitsAt (Kernel.Ew.val Ew.add Ew.i64 Ew.vv nul rl _ m) (q.1 * 8) 8).toInt64.toInt = _
  rw [val_vv_get _ _ _ _ q.2, val_vv_get _ _ _ _ q.2, widen_bits_get _ _ q.2]
  rw [show sub m rr rl = Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul rr rl m from rfl, val_vv_get _ _ _ _ q.2]
  have e := valStep_tau_pick (Column.bitAt tb q.1) hl hr
  rw [e]
  cases Column.bitAt tb q.1
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact toInt64_toInt hl
  · simp only [↓reduceIte]; exact toInt64_toInt hr

/-- A side of no values or of `k`, read at the position `I` clamped into it, is the side read at `I`
    clamped into `[0, k - 1]` where that is a row, else the side's `dflt`. -/
theorem clamp_row {c : Obj} {k : USize} (xc : Vals c k) (I : Int64) :
    (if h : 0 < k.toNat then Vals.row xc (clampFin I k.toNat h) else c.dflt) =
      if hin : min (max I.toInt 0).toNat (k.toNat - 1) < k.toNat then Vals.row xc ⟨_, hin⟩ else c.dflt := by
  by_cases h : 0 < k.toNat
  · rw [dif_pos h, dif_pos (by omega)]; rfl
  · rw [dif_neg h, dif_neg (by omega)]

/-- **One side of a picked sum**, row `q`: the side picked at `il`, which lists the values `P` of the rows
    `G` in order, read at `q`'s rank `t` in `G` clamped, is the side's row `P q`, or its `dflt` past it. -/
theorem pick_side_row {c : Obj} {k : USize} (xc : Vals c k) (il : ByteArray) (hil : len il < USize.size)
    (G : List Nat) (P : Nat → Nat)
    (hG : (List.range (len il)).map (fun z => (Column.bitsAt il (z * 8) 8).toNat) = G.map P)
    (ih : ∀ z : Fin (len il).toUSize.toNat, (Vals.pick c xc il (len il).toUSize (USize.toNat_ofNat_of_lt' hil).symm).row z =
      if hin : (Column.bitsAt il (z.1 * 8) 8).toNat < k.toNat then Vals.row xc ⟨_, hin⟩ else c.dflt)
    {q t : Nat} {j : Int64} (hj : j.toInt = (t : Int)) (hq : G[t]? = some q) :
    (if h : 0 < (len il).toUSize.toNat then
        Vals.row (Vals.pick c xc il (len il).toUSize (USize.toNat_ofNat_of_lt' hil).symm) (clampFin j _ h)
      else c.dflt) = if hin : P q < k.toNat then Vals.row xc ⟨P q, hin⟩ else c.dflt := by
  obtain ⟨ht, hGt⟩ := List.getElem?_eq_some_iff.1 hq
  have hU : (len il).toUSize.toNat = len il := USize.toNat_ofNat_of_lt' hil
  have hlen : len il = G.length := by simpa using congrArg List.length hG
  have e : (Column.bitsAt il (t * 8) 8).toNat = P q := by
    have := congrArg (·[t]?) hG
    simp only [List.getElem?_map, List.getElem?_range (show t < len il by omega), hq, Option.map_some,
      Option.some.injEq] at this
    exact this
  rw [dif_pos (by omega), show clampFin j _ _ = ⟨t, by omega⟩ from Fin.ext (by simp only [clampFin, hj]; omega),
    ih ⟨t, by omega⟩]
  simp only [e]

set_option maxHeartbeats 2000000 in
/-- **`Vals.pick` read back at a sum side**, from its two sides': each picked row keeps its tag (a miss
    reads `inl`), and reads its own side at its old position clamped, now at its rank among its side's rows. -/
theorem pick_row_sum {a b : Obj} {n : USize} (x : Vals (.sum a b) n)
    (iha : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat),
      Vals.PickFits a x.2.2.2.2.1 ((List.range m.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat) →
      ∀ q : Fin m.toNat, (Vals.pick a x.2.2.2.2.1 i m h).row q =
        if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < x.1.toNat then Vals.row x.2.2.2.2.1 ⟨_, hin⟩ else a.dflt)
    (ihb : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat),
      Vals.PickFits b x.2.2.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat) →
      ∀ q : Fin m.toNat, (Vals.pick b x.2.2.2.2.2 i m h).row q =
        if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < x.2.1.toNat then Vals.row x.2.2.2.2.2 ⟨_, hin⟩ else b.dflt)
    (i : ByteArray) (m : USize) (h : len i = m.toNat)
    (hf : Vals.PickFits (.sum a b) x ((List.range m.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat))
    (q : Fin m.toNat) :
    (Vals.pick (.sum a b) x i m h).row q =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then x.row ⟨_, hin⟩ else (Obj.sum a b).dflt := by
  obtain ⟨l, r, tag, idx, xa, xb⟩ := x
  dsimp only at iha ihb
  simp only [Vals.PickFits, List.length_map, List.length_range] at hf
  obtain ⟨hm, hl, hr, hfa, hfb⟩ := hf
  have hF := fun t (ht : t < m.toNat) => pickArr_tag_bit tag i m h ⟨t, ht⟩
  dsimp only at hF
  generalize htb : tagBits (pickArr .boolean ⟨n, tag⟩ i m h) = tb at hF
  -- row `t`'s position in its own side, as `place` and `fill` compute it
  let P : Nat → Nat := fun t => if hin : (Column.bitsAt i (t * 8) 8).toNat < n.toNat then
    min (max (idx.get ⟨_, hin⟩).toInt 0).toNat ((if tag.get ⟨_, hin⟩ then r.toNat else l.toNat) - 1) else l.toNat
  have hP63 : ∀ t, P t < 2 ^ 63 := fun t => by
    simp only [P]; split
    · split <;> omega
    · exact hl
  obtain ⟨p, hpd⟩ : ∃ p, Kernel.Ew.val Ew.fill Ew.i64 Ew.av nul (int (l.toNat : Int))
      (longsOf (pickArr .long ⟨n, place (A := a) (B := b) ⟨l, r, tag, idx, xa, xb⟩ ((l.toNat : Int) - 1)
        ((r.toNat : Int) - l.toNat) 0 0⟩ i m h)) m = p := ⟨_, rfl⟩
  have hpl : len p = m.toNat := by rw [← hpd]; exact len_val ..
  have hp : ∀ t (ht : t < m.toNat), (Column.bitsAt p (t * 8) 8).toNat = P t := fun t ht => by
    rw [← hpd, val_av_get _ _ _ _ ht, valStep_fill, longsOf_get _ ht, pickArr_long_get]
    simp only [P]
    split
    · rename_i hin
      rw [place_get _ hl hr]; dsimp only
      have hv0 : min (max (idx.get ⟨_, hin⟩).toInt 0).toNat
          ((if tag.get ⟨_, hin⟩ then r.toNat else l.toNat) - 1) < 2 ^ 63 := by split <;> omega
      have hv : (UInt64.ofNat (min (max (idx.get ⟨_, hin⟩).toInt 0).toNat
          ((if tag.get ⟨_, hin⟩ then r.toNat else l.toNat) - 1))).toNat < 2 ^ 63 := by
        rw [UInt64.toNat_ofNat_of_lt' (lt_size_of_lt63 hv0)]; exact hv0
      have hn : ¬ (UInt64.ofNat (min (max (idx.get ⟨_, hin⟩).toInt 0).toNat
          ((if tag.get ⟨_, hin⟩ then r.toNat else l.toNat) - 1))).toInt64 = nul := fun e => by
        have := toInt64_toInt hv; rw [e] at this
        have : nul.toInt = -9223372036854775808 := by decide
        omega
      rw [if_neg hn]; exact UInt64.toNat_ofNat_of_lt' (lt_size_of_lt63 hv0)
    · have eI : Column.bitsAt (int (l.toNat : Int)) 0 8 = UInt64.ofNat l.toNat := by
        apply u64_ext
        rw [int_bits_toInt _ (by omega) (by omega),
          toInt64_toInt (by rw [UInt64.toNat_ofNat_of_lt' (lt_size_of_lt63 hl)]; exact hl),
          UInt64.toNat_ofNat_of_lt' (lt_size_of_lt63 hl)]
      rw [long_default, Int64.toInt64_toUInt64, if_pos rfl, eI, UInt64.toNat_ofNat_of_lt' (lt_size_of_lt63 hl)]
  have hrr : ∀ t (ht : t < m.toNat), (Column.bitsAt (sub m (sums m (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m))
      (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m)) (t * 8) 8).toNat =
      ((List.range t).filter (Column.bitAt tb)).length := fun t ht => rank_get tb m hm ht
  have hrl : ∀ t (ht : t < m.toNat), (Column.bitsAt (sub m (tilLongs m)
      (sub m (sums m (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m)) (Kernel.Ew.widen Ew.bits Ew.i64 nul nul tb m)))
      (t * 8) 8).toNat = ((List.range t).filter fun s => !Column.bitAt tb s).length := fun t ht => by
    have hs := filter_range_split (Column.bitAt tb) t
    rw [sub_get ht (by rw [tilLongs_get ht]; omega) (by rw [tilLongs_get ht, hrr t ht]; omega), tilLongs_get ht,
      hrr t ht]
    omega
  -- each side's rows, in order, and the positions `PickFits` names for it
  have hside : ∀ s : Bool, (((List.range m.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat).filterMap fun k =>
      if h : k < n.toNat then
        (if tag.get ⟨k, h⟩ = s then some (min (max (idx.get ⟨k, h⟩).toInt 0).toNat
          ((if s then r.toNat else l.toNat) - 1)) else none)
      else if s then none else some (if s then r.toNat else l.toNat)) =
      ((List.range m.toNat).filter fun t => Column.bitAt tb t == s).map P := fun s => by
    rw [List.filterMap_map]
    refine filterMap_ite _ _ _ _ fun t ht => ?_
    rw [List.mem_range] at ht
    simp only [Function.comp_def, hF t ht, P]
    by_cases hin : (Column.bitsAt i (t * 8) 8).toNat < n.toNat
    · simp only [hin, ↓reduceDIte]; cases s <;> cases tag.get ⟨_, hin⟩ <;> simp
    · simp only [hin, ↓reduceDIte]; cases s <;> simp
  have hfa' : Vals.PickFits a xa (((List.range m.toNat).filter fun t => !Column.bitAt tb t).map P) := by
    rw [List.filter_congr (q := fun t => Column.bitAt tb t == false) (fun t _ => by
        show (!Column.bitAt tb t) = (Column.bitAt tb t == false); cases Column.bitAt tb t <;> rfl),
      ← hside false]
    exact hfa
  have hfb' : Vals.PickFits b xb (((List.range m.toNat).filter (Column.bitAt tb)).map P) := by
    rw [List.filter_congr (q := fun t => Column.bitAt tb t == true) (fun t _ => by
        show Column.bitAt tb t = (Column.bitAt tb t == true); cases Column.bitAt tb t <;> rfl),
      ← hside true]
    exact hfb
  have hGL := gather_whereBits p (Ew.notBits m tb) m hpl
  rw [List.filter_congr (q := fun t => !Column.bitAt tb t) (fun t ht => by
      rw [List.mem_range] at ht; exact notBits_bitAt m tb ht),
    List.map_congr_left (g := P) (fun t ht => hp t (List.mem_range.1 (List.mem_filter.1 ht).1))] at hGL
  have hGR := gather_whereBits p tb m hpl
  rw [List.map_congr_left (g := P) (fun t ht => hp t (List.mem_range.1 (List.mem_filter.1 ht).1))] at hGR
  have hilU : len (gather 8 p (whereBits m (Ew.notBits m tb))) < USize.size := by
    have := congrArg List.length hGL; simp only [List.length_map, List.length_range] at this
    have := List.length_filter_le (fun t => !Column.bitAt tb t) (List.range m.toNat)
    have := m.toNat_lt_size; simp only [List.length_range] at *; omega
  have hirU : len (gather 8 p (whereBits m tb)) < USize.size := by
    have := congrArg List.length hGR; simp only [List.length_map, List.length_range] at this
    have := List.length_filter_le (Column.bitAt tb) (List.range m.toNat)
    have := m.toNat_lt_size; simp only [List.length_range] at *; omega
  have hidx := tau_pick_get tb _ _ m q (by rw [hrr q q.2]; have := List.length_filter_le (Column.bitAt tb) (List.range q.1); simp only [List.length_range] at this; omega)
    (by rw [hrl q q.2]; have := List.length_filter_le (fun s => !Column.bitAt tb s) (List.range q.1); simp only [List.length_range] at this; omega)
  rw [hrr q q.2, hrl q q.2] at hidx
  have hq0 : (pickArr .boolean ⟨n, tag⟩ i m h).get q = Column.bitAt tb q.1 := by
    rw [← htb]; exact Arr.get_bool_bits _ (KernelWF.enc_tagBits _) q
  have hb := hF q q.2
  subst hpd htb
  simp only [Vals.pick, Vals.pickShared, need]
  rw [dif_pos ⟨hilU, hirU⟩]
  simp only [Vals.row, hq0]
  by_cases hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat
  · rw [dif_pos hin] at hb ⊢
    simp only [hb] at hidx ⊢
    cases ht : tag.get ⟨_, hin⟩
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hidx ⊢
      congr 1
      rw [clamp_row xa]
      refine (pick_side_row (q := q.1) xa _ hilU _ P hGL (fun z => iha _ _ _ ?_ z) hidx ?_).trans ?_
      · rw [USize.toNat_ofNat_of_lt' hilU, hGL]; exact hfa'
      · refine filter_range_rank _ q.2 ?_; simp [hb, ht]
      · have hPq : P q = min (max (idx.get ⟨_, hin⟩).toInt 0).toNat (l.toNat - 1) := by
          simp only [P, hin, ↓reduceDIte, ht, Bool.false_eq_true, ↓reduceIte]
        simp only [hPq]
    · simp only [ht, ↓reduceIte] at hidx ⊢
      congr 1
      rw [clamp_row xb]
      refine (pick_side_row (q := q.1) xb _ hirU _ P hGR (fun z => ihb _ _ _ ?_ z) hidx ?_).trans ?_
      · rw [USize.toNat_ofNat_of_lt' hirU, hGR]; exact hfb'
      · refine filter_range_rank _ q.2 ?_; simp [hb, ht]
      · have hPq : P q = min (max (idx.get ⟨_, hin⟩).toInt 0).toNat (r.toNat - 1) := by
          simp only [P, hin, ↓reduceDIte, ht, ↓reduceIte]
        simp only [hPq]
  · rw [dif_neg hin] at hb ⊢
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hidx ⊢
    show Sum.inl _ = Sum.inl a.dflt
    congr 1
    refine (pick_side_row (q := q.1) xa _ hilU _ P hGL (fun z => iha _ _ _ ?_ z) hidx ?_).trans ?_
    · rw [USize.toNat_ofNat_of_lt' hilU, hGL]; exact hfa'
    · exact filter_range_rank _ q.2 (by simp [hb])
    · have hPq : P q = l.toNat := by simp only [P, hin, ↓reduceDIte]
      simp only [hPq, Nat.lt_irrefl, ↓reduceDIte]

/-- **`Vals.pick` read back**, at every side: row `q` of `x` picked at `i` is `x`'s row `i[q]` where that is
    below the count, else `Obj.dflt` — under `Vals.PickFits` at the rows `i` names. -/
theorem pick_row : (A : Obj) → {n : USize} → (x : Vals A n) → (i : ByteArray) → (m : USize) →
    (h : len i = m.toNat) →
    Vals.PickFits A x ((List.range m.toNat).map fun q => (Column.bitsAt i (q * 8) 8).toNat) →
    ∀ q : Fin m.toNat, (Vals.pick A x i m h).row q =
      if hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat then x.row ⟨_, hin⟩ else A.dflt
  | .atom _, n, x, i, m, h, hf, q => by
    by_cases hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat
    · rw [dif_pos hin]; exact pick_row_atom x i m h q hin
    · exact pick_row_atom_dflt x (hf ⟨_, List.mem_map.2 ⟨q.1, List.mem_range.2 q.2, rfl⟩, Nat.le_of_not_lt hin⟩)
        i m h q
  | .prod a b, _, x, i, m, h, hf, q =>
    pick_row_prod_dflt x i m h q (pick_row a x.1 i m h hf.1 q) (pick_row b x.2 i m h hf.2 q)
  | .arr b, _, x, i, m, h, hf, q => pick_row_arr x (fun i m h hf q => pick_row b x.2.2.2 i m h hf q) i m h hf q
  | .sum a b, _, x, i, m, h, hf, q =>
    pick_row_sum x (fun i m h hf q => pick_row a _ i m h hf q) (fun i m h hf q => pick_row b _ i m h hf q) i m h hf q

#print axioms pick_row

end LeetQ.Rel.Alg
