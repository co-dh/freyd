/-
  The long arithmetic `join` runs on its count and index columns, read back: `add`/`sub` of two longs
  below `2^63`, `sums` as the running total, and `classSizes` as the rows of each class.
-/
import LeetQ.Rel.KernelWF.JoinSpec
import QLean.Verify.Chain
import QLean.Verify.ScanOver
import QLean.Verify.BinWin
import QLean.Verify.Structural

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-- A long below `2^63` reads as its own value at `i64`. -/
theorem toInt64_toInt {x : UInt64} (hx : x.toNat < 2 ^ 63) : x.toInt64.toInt = x.toNat :=
  calc x.toInt64.toInt = (UInt64.ofNat x.toNat).toInt64.toInt := by rw [UInt64.ofNat_toNat]
    _ = x.toNat := Int64.toInt_ofNat_of_lt hx

/-- An `Int64` whose value is the natural `q < 2^63` is `Int64.ofNat q`. -/
theorem int64_eq_ofNat {a : Int64} {q : Nat} (hq : q < 2 ^ 63) (h : a.toInt = q) : a = Int64.ofNat q :=
  Int64.toInt_inj.1 (by rw [h, Int64.toInt_ofNat_of_lt hq])

/-- **`valStep` of `+` and `-` on two longs below `2^63`** is the natural sum, and the natural difference
    where it is not negative: neither operand is q's null `0N`, and nothing wraps. -/
theorem valStep_add_sub {x y : UInt64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    (x.toNat + y.toNat < 2 ^ 63 →
      Ew.valStep Ew.add Ew.i64 nul.toUInt64 x y = UInt64.ofNat (x.toNat + y.toNat)) ∧
    (y.toNat ≤ x.toNat →
      Ew.valStep Ew.sub Ew.i64 nul.toUInt64 x y = UInt64.ofNat (x.toNat - y.toNat)) := by
  have ex := toInt64_toInt hx; have ey := toInt64_toInt hy
  have hxn : x.toInt64 ≠ Int64.minValue := fun e => by rw [e] at ex; simp at ex
  have hyn : y.toInt64 ≠ Int64.minValue := fun e => by rw [e] at ey; simp at ey
  have hnul : (nul.toUInt64).toInt64 = Int64.minValue := rfl
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.add, Ew.sub, hnul]
  simp only [↓reduceIte]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [if_neg (by simp; exact ⟨hxn, hyn⟩)]
  · rw [int64_eq_ofNat (a := x.toInt64 + y.toInt64) h
      (by rw [Int64.toInt_add, ex, ey]; simp only [Int.bmod]; split <;> omega)]; rfl
  · rw [int64_eq_ofNat (a := x.toInt64 - y.toInt64) (q := x.toNat - y.toNat) (by omega)
      (by rw [Int64.toInt_sub, ex, ey]; simp only [Int.bmod]; split <;> omega)]; rfl

/-- `Ew.val` on longs at `vv`, element `i` below the count: `valStep` of the two operands' longs `i`. -/
theorem val_vv_get (op : UInt8) (a b : ByteArray) (n : USize) {i : Nat} (hi : i < n.toNat) :
    Column.bitsAt (Kernel.Ew.val op Ew.i64 Ew.vv nul a b n) (i * 8) 8 =
      Ew.valStep op Ew.i64 nul.toUInt64 (Column.bitsAt a (i * 8) 8) (Column.bitsAt b (i * 8) 8) := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have h := congrArg (·[i]?) (elemsW_val op Ew.i64 Ew.vv nul a b n)
  have hs : (Kernel.Ew.val op Ew.i64 Ew.vv nul a b n).size / 8 = n.toNat := by
    have := len_val op Ew.vv a b n; simpa [len] using this
  simp only [elemsW, hw, hs, List.getElem?_map, List.getElem?_range, hi, Option.map_some,
    Option.some.injEq] at h
  rw [h]
  simp (config := {decide := true}) only [Ew.shapeIdx, Ew.elem, hw, ↓reduceIte]
  generalize Ew.valStep op Ew.i64 nul.toUInt64 _ _ = v
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ (8 * 8) from v.toNat_lt), UInt64.ofNat_toNat]

/-- **`add n a b`'s long `i`** is the sum of the two longs `i`, all three below `2^63`. -/
theorem add_get {n : USize} {a b : ByteArray} {i : Nat} (hi : i < n.toNat) (h : (Column.bitsAt a (i * 8) 8).toNat + (Column.bitsAt b (i * 8) 8).toNat < 2 ^ 63) :
    (Column.bitsAt (add n a b) (i * 8) 8).toNat = (Column.bitsAt a (i * 8) 8).toNat + (Column.bitsAt b (i * 8) 8).toNat := by
  unfold add; rw [val_vv_get _ _ _ _ hi, ((valStep_add_sub (by omega) (by omega)).1 h), UInt64.toNat_ofNat_of_lt' (Nat.lt_trans h (by decide))]

/-- **`sub n a b`'s long `i`** is the difference of the two longs `i`, both below `2^63`, `b`'s no greater. -/
theorem sub_get {n : USize} {a b : ByteArray} {i : Nat} (hi : i < n.toNat) (ha : (Column.bitsAt a (i * 8) 8).toNat < 2 ^ 63)
    (h : (Column.bitsAt b (i * 8) 8).toNat ≤ (Column.bitsAt a (i * 8) 8).toNat) : (Column.bitsAt (sub n a b) (i * 8) 8).toNat = (Column.bitsAt a (i * 8) 8).toNat - (Column.bitsAt b (i * 8) 8).toNat := by
  unfold sub; rw [val_vv_get _ _ _ _ hi, ((valStep_add_sub ha (by omega)).2 h),
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_trans ha (by decide)))]

/-- The `sums` fold over longs whose running total stays below `2^63`: no element is `0N`, nothing
    wraps, and the accumulator is the natural total. -/
theorem foldl_sums (l : List UInt64) (s : Nat) (h : s + (l.map UInt64.toNat).sum < 2 ^ 63) :
    l.foldl (fun a x => if Scan.Kind.isNull .i64 x then a else a + Scan.Kind.signed .i64 x) (Int64.ofNat s) =
      Int64.ofNat (s + (l.map UInt64.toNat).sum) := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have ex := toInt64_toInt (x := x) (by omega)
    have hn : Scan.Kind.isNull .i64 x = false := by
      simp only [Scan.Kind.isNull, beq_eq_false_iff_ne]
      exact fun e => by rw [e] at ex; simp at ex
    rw [List.foldl_cons, hn, if_neg Bool.false_ne_true, Scan.Kind.signed,
      int64_eq_ofNat (a := Int64.ofNat s + x.toInt64) (q := s + x.toNat) (by omega) (by
        rw [Int64.toInt_add, ex, Int64.toInt_ofNat_of_lt (by omega)]; simp only [Int.bmod]; split <;> omega),
      ih _ (by omega), Nat.add_assoc]

/-- **`sums n b`'s long `j`** is the total of `b`'s longs `0 … j`, `j` below `n` and `b`'s count, that
    total below `2^63`. -/
theorem sums_get {n : USize} {b : ByteArray} {j : Nat} (hj : j < n.toNat) (hb : j < len b)
    (h : ((List.range (j + 1)).map fun i => (Column.bitsAt b (i * 8) 8).toNat).sum < 2 ^ 63) :
    (Column.bitsAt (sums n b) (j * 8) 8).toNat = ((List.range (j + 1)).map fun i => (Column.bitsAt b (i * 8) 8).toNat).sum := by
  have hm : j < min n.toNat (Scan.Kind.avail .i64 b) := by
    simp only [Scan.Kind.avail, Scan.Kind.width]; simp only [len] at hb; omega
  have hf : sums n b = Scan.scanOf (min n.toNat (Scan.Kind.avail .i64 b)) 8 (Scan.Kind.bitsAt .i64 b)
      (Scan.Kind.isNull .i64) (0 : Int64) (fun a x => a + Scan.Kind.signed .i64 x) (Scan.narrow 8) := rfl
  rw [hf, scanOf_get _ 8 (by decide) _ _ _ _ _ j hm]
  have hl : (List.range (j + 1)).map (Scan.Kind.bitsAt .i64 b) = (List.range (j + 1)).map fun i => Column.bitsAt b (i * 8) 8 := rfl
  have h' : 0 + (((List.range (j + 1)).map fun i => Column.bitsAt b (i * 8) 8).map UInt64.toNat).sum < 2 ^ 63 := by
    rw [List.map_map]; exact (Nat.zero_add _).symm ▸ h
  rw [hl, show (0 : Int64) = Int64.ofNat 0 from rfl, foldl_sums _ 0 h', Nat.zero_add, List.map_map]
  simp only [Scan.narrow, show (8 = 4) = False by decide, ↓reduceIte]
  rw [show (Int64.ofNat _).toUInt64 = UInt64.ofNat _ from rfl]
  have hS : (List.map (UInt64.toNat ∘ fun i => Column.bitsAt b (i * 8) 8) (List.range (j + 1))).sum =
      ((List.range (j + 1)).map fun i => (Column.bitsAt b (i * 8) 8).toNat).sum := rfl
  rw [hS]; revert h; generalize ((List.range (j + 1)).map fun i => (Column.bitsAt b (i * 8) 8).toNat).sum = S; intro h
  rw [UInt64.toNat_ofNat_of_lt' (show S < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show S < 2 ^ (8 * 8) by omega),
    UInt64.toNat_ofNat_of_lt' (show S < 2 ^ 64 by omega)]

/-- A class count's width is a lane: at most `64` bits. -/
theorem idWidthOf_le (n : Nat) : Column.idWidthOf n ≤ 64 := by
  rcases laneWidth_cases (Column.widthFor (n - 1)) with h | h | h | h | h | h | h | h <;>
    simp only [Column.idWidthOf, h] <;> omega

/-- **`classSizes n g`, read back**: one long per class of `g` (`len g.2` of them), the count of the
    first `n` ids of `g.1`, read at their width `idWidthOf (len g.2)`, equal to that class. -/
theorem classSizes_ids (n : USize) (g : ByteArray × ByteArray) (hg : len g.2 < USize.size) :
    ids (classSizes n g) = (List.range (len g.2)).map fun c =>
      (idsW (Column.idWidthOf (len g.2)) n.toNat g.1).countP (· == c) := by
  unfold classSizes longCount
  simp only [need, dif_pos hg]
  rw [groupSizes_spec, USize.toNat_ofNat_of_lt' hg, lane_toNat (idWidthOf_le _)]

/-- **Position `p` of the runs `t` repeated `c t` times, `t < m`, is the `t` whose run covers it**: the
    total of the earlier runs is at most `p` and `p` is short of that total plus `c t`. -/
theorem flatMap_replicate_get (c : Nat → Nat) (m p : Nat) (hp : p < ((List.range m).map c).sum) :
    ∃ t < m, ((List.range t).map c).sum ≤ p ∧ p < ((List.range t).map c).sum + c t ∧
      ((List.range m).flatMap fun t => List.replicate (c t) t)[p]? = some t := by
  induction m with
  | zero => simp at hp
  | succ m ih =>
    have hlen : ((List.range m).flatMap fun t => List.replicate (c t) t).length = ((List.range m).map c).sum := by
      simp [List.length_flatMap]
    rw [List.range_succ, List.map_append] at hp
    simp at hp
    rw [List.range_succ, List.flatMap_append]
    by_cases h : p < ((List.range m).map c).sum
    · obtain ⟨t, ht, h1, h2, h3⟩ := ih h
      exact ⟨t, by omega, h1, h2, by rw [List.getElem?_append_left (by rw [hlen]; exact h)]; exact h3⟩
    · refine ⟨m, by omega, by omega, by omega, ?_⟩
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getElem?_replicate]
      rw [if_pos (by omega)]

/-- **`expand`'s index column, read back**: row `t` of the count column repeated its count's times, in row
    order — `expandBytes` of `til n`, each count below `2^63`, every row below `n`. -/
theorem expand_idx {n : USize} {cnt : ByteArray} (hn : len cnt ≤ n.toNat)
    (hc : ∀ t < len cnt, (Column.bitsAt cnt (t * 8) 8).toNat < 2 ^ 63) :
    ids (expandBytes 8 0 (tilLongs n) cnt) =
      (List.range (len cnt)).flatMap fun t => List.replicate (Column.bitsAt cnt (t * 8) 8).toNat t := by
  have hid : ∀ d, ids d = (elemsW 8 d).map UInt64.toNat := fun d => by
    simp only [ids, elemsW, List.map_map, Function.comp_def]
  have h8 : (8 : USize).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  have hs := expandBytes_spec 8 (by rw [h8]; decide) (Nat.le_of_eq h8) 0 (by rw [h8]; decide) (tilLongs n) cnt
  rw [h8] at hs
  have htil : ∀ t < n.toNat, ((elemsW 8 (tilLongs n)).getD t 0).toNat = t := fun t ht => by
    have h := congrArg (·[t]?) (tilLongs_spec n)
    simp only [List.getElem?_map, List.getElem?_range, ht] at h
    rw [List.getD_eq_getElem?_getD]
    cases e : (elemsW 8 (tilLongs n))[t]? with
    | none => simp [e] at h
    | some v => simp only [e, Option.map_some, Option.some.injEq] at h; simpa using h
  rw [hid, hs, List.map_flatMap]
  have key : ∀ m ≤ len cnt, ((List.range m).flatMap fun i =>
      (List.replicate (Column.bitsAt cnt (i * 8) 8).toInt64.toInt.toNat ((elemsW 8 (tilLongs n)).getD i 0)).map
        UInt64.toNat) = (List.range m).flatMap fun t => List.replicate (Column.bitsAt cnt (t * 8) 8).toNat t := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (by omega)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_replicate]
      rw [toInt64_toInt (hc m (by omega)), htil m (by omega)]
      rfl
  exact key _ (Nat.le_refl _)

/-- A total over a prefix of `range` is at most the total over a longer one. -/
theorem sum_range_le (c : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    ((List.range a).map c).sum ≤ ((List.range b).map c).sum := by
  induction b with
  | zero => simp [Nat.le_zero.1 h]
  | succ b ih =>
    rw [List.range_succ, List.map_append, List.sum_append_nat]
    by_cases e : a = b + 1
    · subst e; rw [List.range_succ, List.map_append, List.sum_append_nat]; exact Nat.le_refl _
    · have := ih (by omega); simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega

/-- **`gather 8 src idx`'s long `j`** is `src`'s long `idx[j]`, where that index is below `src`'s count. -/
theorem gather8_get {src idx : ByteArray} {j : Nat} (hj : j < len idx)
    (hs : (Column.bitsAt idx (j * 8) 8).toNat < len src) :
    Column.bitsAt (gather 8 src idx) (j * 8) 8 = Column.bitsAt src ((Column.bitsAt idx (j * 8) 8).toNat * 8) 8 := by
  have h8 : (Nat.toUSize 8).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  have h := (gatherBytes_spec (Nat.toUSize 8) (by rw [h8]; decide) 0 src idx).2 j (by simpa [len] using hj)
  rw [h8] at h
  unfold gather; rw [h, if_pos (by simpa [len] using hs)]

/-- `tilLongs m`'s long `p` is `p`, below `m`. -/
theorem tilLongs_get {m : USize} {p : Nat} (hp : p < m.toNat) : (Column.bitsAt (tilLongs m) (p * 8) 8).toNat = p := by
  have hid : ids (tilLongs m) = List.range m.toNat := by
    rw [← tilLongs_spec m]; simp only [ids, elemsW, List.map_map, Function.comp_def]
  rw [ids_get hid (by simpa using hp), List.getElem_range]

/-- **`expand`'s rank column, read back**: copy `p` of the run of count row `t = i[p]` is that run's
    `p - Σ_{s<t} cnt[s]`-th copy, `i` the index column `expandBytes` answers — the count column at most
    `n` longs, their total below `2^63`, the copies' count a `USize`. -/
theorem expand_rank {n : USize} {cnt : ByteArray} (hn : len cnt ≤ n.toNat)
    (hS : ((List.range (len cnt)).map fun t => (Column.bitsAt cnt (t * 8) 8).toNat).sum < 2 ^ 63)
    (hm : len (expandBytes 8 0 (tilLongs n) cnt) < USize.size) {p : Nat}
    (hp : p < len (expandBytes 8 0 (tilLongs n) cnt)) :
    (Column.bitsAt (sub (len (expandBytes 8 0 (tilLongs n) cnt)).toUSize
        (tilLongs (len (expandBytes 8 0 (tilLongs n) cnt)).toUSize)
        (gather 8 (sub n (sums n cnt) cnt) (expandBytes 8 0 (tilLongs n) cnt))) (p * 8) 8).toNat =
      p - ((List.range (Column.bitsAt (expandBytes 8 0 (tilLongs n) cnt) (p * 8) 8).toNat).map fun s =>
        (Column.bitsAt cnt (s * 8) 8).toNat).sum := by
  have hc : ∀ t < len cnt, (Column.bitsAt cnt (t * 8) 8).toNat < 2 ^ 63 := fun t ht => by
    have h1 := sum_range_le (fun t => (Column.bitsAt cnt (t * 8) 8).toNat) (show t + 1 ≤ len cnt by omega)
    simp only [List.range_succ, List.map_append, List.sum_append_nat, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at h1
    omega
  have hI := expand_idx hn hc
  generalize expandBytes 8 0 (tilLongs n) cnt = i at hI hm hp ⊢
  have hlen : len i = ((List.range (len cnt)).map fun t => (Column.bitsAt cnt (t * 8) 8).toNat).sum := by
    rw [len_eq_ids, hI, List.length_flatMap]; simp
  obtain ⟨t, ht, h1, h2, h3⟩ := flatMap_replicate_get (fun t => (Column.bitsAt cnt (t * 8) 8).toNat) (len cnt) p
    (hlen ▸ hp)
  have hpl : p < ((List.range (len cnt)).flatMap fun t =>
      List.replicate (Column.bitsAt cnt (t * 8) 8).toNat t).length := by rw [← hI, ← len_eq_ids]; exact hp
  have hit : (Column.bitsAt i (p * 8) 8).toNat = t := by
    rw [ids_get hI hpl]; rw [List.getElem?_eq_getElem hpl] at h3; exact Option.some.inj h3
  have hpre := sum_range_le (fun t => (Column.bitsAt cnt (t * 8) 8).toNat) (show t + 1 ≤ len cnt by omega)
  have hsum1 : ((List.range (t + 1)).map fun s => (Column.bitsAt cnt (s * 8) 8).toNat).sum =
      ((List.range t).map fun s => (Column.bitsAt cnt (s * 8) 8).toNat).sum + (Column.bitsAt cnt (t * 8) 8).toNat := by
    simp only [List.range_succ, List.map_append, List.sum_append_nat, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
  have hsm := sums_get (n := n) (b := cnt) (j := t) (by omega) ht (by omega)
  have hrs := sub_get (n := n) (a := sums n cnt) (b := cnt) (i := t) (by omega) (by omega) (by omega)
  have hm' : (len i).toUSize.toNat = len i := USize.toNat_ofNat_of_lt' hm
  have hg := gather8_get (src := sub n (sums n cnt) cnt) (idx := i) (j := p) hp
    (by rw [hit, sub, len_val]; omega)
  rw [hit] at hg ⊢
  rw [sub_get (by rw [hm']; exact hp) (by rw [tilLongs_get (by rw [hm']; exact hp)]; omega)
    (by rw [tilLongs_get (by rw [hm']; exact hp), hg, hrs]; omega),
    tilLongs_get (by rw [hm']; exact hp), hg, hrs]
  omega

/-- **`Code.gather`'s payload holds exactly its codes**: `len i` of them at `c`'s lane, `⌈len i · w / 8⌉`
    bytes — `gatherBits`, `gatherBytes` and `gatherPacked` (`packIds` at `2`/`4` bits) alike. -/
theorem gather_size (c : Code) (i : ByteArray) (hl : len i < USize.size)
    (hcw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) :
    (Code.gather c i).b.size = (len i * c.w + 7) / 8 := by
  unfold Code.gather longCount
  simp only [need, dif_pos hl]
  unfold Code.kind
  split
  next _ hk =>
    rcases laneKind_some hk with ⟨-, h1⟩ | ⟨h, -⟩
    · rw [KernelWF.gatherBits_size, h1, Nat.mul_one]; rfl
    · exact absurd rfl h
  next _ k hne hk =>
    rcases laneKind_some hk with ⟨h, -⟩ | ⟨-, hw8, hq, -⟩
    · exact absurd h hne
    rw [KernelWF.gatherBytes_size, lane_toNat (by omega), hw8]; simp only [len]
    rw [show i.size / 8 * (8 * k.width) + 7 = 8 * (i.size / 8 * k.width) + 7 by rw [Nat.mul_left_comm]]
    omega
  next _ hk =>
    have h24 : c.w = 2 ∨ c.w = 4 := by
      rcases hcw with h | h | h | h | h | h | h <;> simp [h, laneKind] at hk ⊢
    unfold gatherPacked Column.packIds
    rw [lane_toNat (by omega), if_neg (by omega), if_neg (by omega)]
    dsimp only
    rw [(fold_push_getElem? _ _ _).1]
    simp only [len]
    rcases h24 with h | h <;> rw [h] <;> simp [show ∀ k, (ByteArray.emptyWithCapacity k).size = 0 from fun _ => rfl] <;> omega

/-- **A stable sort by a class `κ` below `K` is the classes in turn, each class's rows ascending**: a
    permutation of `range n` sorted by `κ` with ties in row order is unique, so class `c` takes the positions
    `[#(κ < c), #(κ ≤ c))` in ascending row order. -/
theorem stable_sort_classes {L : List Nat} {n K : Nat} (κ : Nat → Nat) (hκ : ∀ i < n, κ i < K)
    (hp : L.Perm (List.range n)) (hs : L.Pairwise fun i j => κ i ≤ κ j ∧ (κ j ≤ κ i → i < j)) :
    L = (List.range K).flatMap fun c => (List.range n).filter fun i => κ i == c := by
  have hR : ((List.range K).flatMap fun c => (List.range n).filter fun i => κ i == c).Pairwise
      fun i j => κ i < κ j ∨ (κ i = κ j ∧ i < j) := by
    rw [List.pairwise_flatMap]
    refine ⟨fun c _ => ((List.pairwise_lt_range (n := n)).filter _).imp_of_mem fun hi hj h => ?_,
      (List.pairwise_lt_range (n := K)).imp fun h x hx y hy => ?_⟩
    · simp only [List.mem_filter, beq_iff_eq] at hi hj; exact Or.inr ⟨by rw [hi.2, hj.2], h⟩
    · simp only [List.mem_filter, beq_iff_eq] at hx hy; exact Or.inl (by omega)
  refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => by omega)
    (hs.imp fun {a b} ⟨h1, h2⟩ => if e : κ b ≤ κ a then Or.inr ⟨by omega, h2 e⟩ else Or.inl (by omega)) hR
    (hp.trans ?_)
  have hd : ((List.range K).flatMap fun c => (List.range n).filter fun i => κ i == c).Nodup :=
    hR.imp fun h e => by subst e; omega
  refine List.perm_iff_count.2 fun x => ?_
  rw [List.Nodup.count List.nodup_range, List.Nodup.count hd]
  by_cases hx : x < n
  · rw [if_pos (List.mem_range.2 hx), if_pos (List.mem_flatMap.2 ⟨κ x, List.mem_range.2 (hκ x hx),
      List.mem_filter.2 ⟨List.mem_range.2 hx, by simp⟩⟩)]
  · rw [if_neg (fun h => hx (List.mem_range.1 h)), if_neg (fun h => by
      obtain ⟨_, _, h⟩ := List.mem_flatMap.1 h; exact hx (List.mem_range.1 (List.mem_filter.1 h).1))]

#print axioms flatMap_replicate_get
#print axioms expand_idx
#print axioms expand_rank
#print axioms gather_size
#print axioms stable_sort_classes
#print axioms add_get
#print axioms sub_get
#print axioms sums_get
#print axioms classSizes_ids

end LeetQ.Rel.Alg
