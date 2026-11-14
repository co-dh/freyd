/-
  `bagify`'s two grades read back: `gradeColumn .long false` lists the rows in a stable ascending sort by
  value, and the grade of `Code.ofLongs` of longs below `2^63` lists them in a stable sort by those longs — at
  row numbers, each row's cells in one block, rows ascending, the incoming order kept inside a block.
-/
import LeetQ.Rel.KernelWF.PlaceSpec
import LeetQ.Rel.KernelWF.PickRow
import LeetQ.Rel.KernelWF.CodesRec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- The `long` key `Order.keyAt .i64` sorts by, read as a number: `2^63` above the value. -/
theorem key_i64 (a : Int64) : ((a.toUInt64 ^^^ 0x8000000000000000).toNat : Int) = a.toInt + 2 ^ 63 := by
  rw [UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl]
  have hlt := a.toUInt64.toNat_lt
  have ht : a.toInt = if 2 * a.toUInt64.toNat < 2 ^ 64 then (a.toUInt64.toNat : Int)
      else (a.toUInt64.toNat : Int) - 2 ^ 64 := by
    rw [Int64.toInt, BitVec.toInt_eq_toNat_cond]; rfl
  rw [ht]
  by_cases h : a.toUInt64.toNat < 2 ^ 63
  · rw [xor_pow63 h, if_pos (by omega)]; omega
  · obtain ⟨y, hy, hx⟩ : ∃ y, y < 2 ^ 63 ∧ a.toUInt64.toNat = y ^^^ 2 ^ 63 :=
      ⟨a.toUInt64.toNat - 2 ^ 63, by omega, by rw [xor_pow63 (by omega)]; omega⟩
    rw [if_neg (by omega), hx, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, xor_pow63 hy]; omega

/-- **`Order.grade .i64` ascending is a stable sort by key**: every row below the count once, each before every
    later row of a greater key and before every later tie. -/
theorem grade_i64 (n : USize) (B : ByteArray) :
    (ids (Order.grade .i64 false n B)).Perm (List.range (min n.toNat (len B))) ∧
      (ids (Order.grade .i64 false n B)).Pairwise fun i j =>
        (Order.keyAt .i64 B i).toNat < (Order.keyAt .i64 B j).toNat ∨
          ((Order.keyAt .i64 B i).toNat = (Order.keyAt .i64 B j).toNat ∧ i < j) := by
  obtain ⟨hperm, hsort⟩ := grade_spec .i64 false n B
  refine ⟨hperm, hsort.imp fun {i j} ⟨h1, h2⟩ => ?_⟩
  simp only [keyOrd, Bool.false_eq_true, ↓reduceIte] at h1 h2
  rcases UInt64.lt_or_eq_of_le h1 with hl | he
  · exact .inl (UInt64.lt_iff_toNat_lt.1 hl)
  · exact .inr ⟨congrArg UInt64.toNat he, h2 (by rw [he]; exact UInt64.le_refl _)⟩

/-- `gradeColumn` at `long` is the kernel's `grade` (or `ranks`) over the column's dense payload, on either
    encoding. -/
theorem gradeColumn_long {n : USize} (x : Arr .long n) (rank : Bool) :
    gradeColumn .long false n x.enc rank = some (.bytes
      (if rank then Order.ranks .i64 n (longsOf x) else Order.grade .i64 false n (longsOf x))) := by
  rcases long_cases x.wf with ⟨b, hb⟩ | ⟨M, P, hb⟩
  · have hs : b.size / 8 = n.toNat := Arr.n_long_bytes x hb
    have hl : longsOf x = b := by unfold longsOf; simp only [hb, longBytes]; rfl
    rw [hl]
    unfold gradeColumn
    simp only [hb, orderKind, Enc.bytesOf]
    rw [if_neg (by decide), if_neg (by simp only [Scan.Kind.width]; omega)]
  · have hl : longsOf x = Coc.decode 8 M P n := by unfold longsOf; simp only [hb, longBytes]; rfl
    rw [hl]
    unfold gradeColumn
    simp only [hb, orderKind]
    rw [if_neg (by decide)]
    cases rank <;> rfl

/-- **`gradeColumn .long` ascending, read back**: the grade lists every row below the count once, each before
    every later row of a greater value and before every later tie — q's `iasc`, a stable ascending sort, null
    `0N` (the least `Int64`) first. -/
theorem grade_long {n : USize} (x : Arr .long n) :
    (ids (Order.grade .i64 false n (longsOf x))).Perm (List.range n.toNat) ∧
      (ids (Order.grade .i64 false n (longsOf x))).Pairwise fun i j => ∀ (hi : i < n.toNat) (hj : j < n.toNat),
        x.get ⟨i, hi⟩ < x.get ⟨j, hj⟩ ∨ (x.get ⟨i, hi⟩ = x.get ⟨j, hj⟩ ∧ i < j) := by
  obtain ⟨hp, hs⟩ := grade_i64 n (longsOf x)
  rw [len_longsOf, Nat.min_self] at hp
  refine ⟨hp, hs.imp fun {i j} h hi hj => ?_⟩
  have hv : ∀ k (hk : k < n.toNat),
      ((Order.keyAt .i64 (longsOf x) k).toNat : Int) = (x.get ⟨k, hk⟩).toInt + 2 ^ 63 := fun k hk => by
    rw [← key_i64, ← longsOf_get x hk]; rfl
  have e1 := hv i hi; have e2 := hv j hj
  simp only [Int64.lt_iff_toInt_lt, ← Int64.toInt_inj]
  omega

/-- **The grade of `Code.ofLongs b`, `b`'s longs below `2^63`, is a stable sort by them**: every position of
    `b` once, each before every later position of a greater long and before every later tie — at row numbers,
    each row's positions in one block, rows ascending, the incoming order kept inside a block. -/
theorem grade_ofLongs (b : ByteArray) (hN : len b < USize.size)
    (h63 : ∀ i, i < len b → (Column.bitsAt b (i * 8) 8).toNat < 2 ^ 63) :
    (ids (Code.ofLongs b).grade).Perm (List.range (len b)) ∧
      (ids (Code.ofLongs b).grade).Pairwise fun i j =>
        (Column.bitsAt b (i * 8) 8).toNat < (Column.bitsAt b (j * 8) 8).toNat ∨
          ((Column.bitsAt b (i * 8) 8).toNat = (Column.bitsAt b (j * 8) 8).toNat ∧ i < j) := by
  have hm : ((len b).toUSize).toNat = len b := USize.toNat_ofNat_of_lt' hN
  have hc : Code.ofLongs b = ⟨64, (len b).toUSize, 2 ^ 64, b⟩ := by
    unfold Code.ofLongs longCount need; rw [dif_pos hN]
  have hg : (Code.ofLongs b).grade = Order.grade .i64 false (len b).toUSize b := by rw [hc]; rfl
  obtain ⟨hp, hs⟩ := grade_i64 (len b).toUSize b
  rw [hm, Nat.min_self] at hp
  rw [← hg] at hp hs
  have hkey : ∀ i, i < len b → (Order.keyAt .i64 b i).toNat = 2 ^ 63 + (Column.bitsAt b (i * 8) 8).toNat := by
    intro i hi
    show (Column.bitsAt b (i * 8) 8 ^^^ 0x8000000000000000).toNat = _
    rw [UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl]
    exact xor_pow63 (h63 i hi)
  refine ⟨hp, hs.imp_of_mem fun {i j} hi hj h => ?_⟩
  rw [hkey i (List.mem_range.1 (hp.mem_iff.1 hi)), hkey j (List.mem_range.1 (hp.mem_iff.1 hj))] at h
  omega

/-- **A sort `v` regrouped stably by row**: `v` lists `til (len i)` in `R` order, `i` gives each position its
    row (below `2^63`); `v@grade(i@v)` lists every position once, by row ascending and, inside a row, in `v`'s
    `R` order — `bagify`'s `p`, each row's cells one block, sorted by value. -/
theorem grade_group (i v : ByteArray) (hv : (ids v).Perm (List.range (len i))) (R : Nat → Nat → Prop)
    (hsv : (ids v).Pairwise R) (hN : len i < USize.size)
    (h63 : ∀ c, c < len i → (Column.bitsAt i (c * 8) 8).toNat < 2 ^ 63) :
    (ids (gather 8 v (Code.ofLongs (gather 8 i v)).grade)).Perm (List.range (len i)) ∧
      (ids (gather 8 v (Code.ofLongs (gather 8 i v)).grade)).Pairwise fun c c' =>
        (Column.bitsAt i (c * 8) 8).toNat < (Column.bitsAt i (c' * 8) 8).toNat ∨
          ((Column.bitsAt i (c * 8) 8).toNat = (Column.bitsAt i (c' * 8) 8).toNat ∧ R c c') := by
  have hvl : len v = len i := by rw [len_eq_ids, hv.length_eq, List.length_range]
  have hwl : len (gather 8 i v) = len i := by rw [gather_len, hvl]
  have hvlt : ∀ a, a < len i → (Column.bitsAt v (a * 8) 8).toNat < len i := fun a ha => by
    have ha' : a < (ids v).length := by rw [← len_eq_ids, hvl]; exact ha
    rw [← ids_getElem ha']; exact List.mem_range.1 (hv.mem_iff.1 (List.getElem_mem ha'))
  have hw : ∀ a, a < len i → Column.bitsAt (gather 8 i v) (a * 8) 8 =
      Column.bitsAt i ((Column.bitsAt v (a * 8) 8).toNat * 8) 8 :=
    fun a ha => gather8_get (by rw [hvl]; exact ha) (hvlt a ha)
  obtain ⟨hgp, hgs⟩ := grade_ofLongs (gather 8 i v) (by rw [hwl]; exact hN)
    (fun a ha => by rw [hwl] at ha; rw [hw a ha]; exact h63 _ (hvlt a ha))
  rw [hwl] at hgp
  generalize hG : (Code.ofLongs (gather 8 i v)).grade = G at hgp hgs
  have hGm : ∀ t ∈ ids G, t < len v := fun t ht => by rw [hvl]; exact List.mem_range.1 (hgp.mem_iff.1 ht)
  refine ⟨(gather_perm (by rw [hvl]; exact hgp)).trans hv, ?_⟩
  rw [ids_gather8 hGm, List.pairwise_map]
  refine hgs.imp_of_mem fun {a b} ha hb h => ?_
  have ha' := List.mem_range.1 (hgp.mem_iff.1 ha); have hb' := List.mem_range.1 (hgp.mem_iff.1 hb)
  have hva : a < (ids v).length := by rw [hv.length_eq, List.length_range]; exact ha'
  have hvb : b < (ids v).length := by rw [hv.length_eq, List.length_range]; exact hb'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hva, Option.getD_some, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hvb, Option.getD_some, ids_getElem hva, ids_getElem hvb]
  rw [hw a ha', hw b hb'] at h
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · refine .inr ⟨h1, ?_⟩
    have := List.pairwise_iff_getElem.1 hsv a b hva hvb h2
    rwa [ids_getElem hva, ids_getElem hvb] at this

/-- **A list sorted by a key puts each key in one block**: `g` a permutation of `til N` non-decreasing in `key`;
    position `d` stands at or past the elements of smaller key and before the end of those of key at most its
    own. -/
theorem sorted_block {N : Nat} (g : List Nat) (key : Nat → Nat) (hp : g.Perm (List.range N))
    (hs : g.Pairwise fun a b => key a ≤ key b) (d : Nat) (hd : d < g.length) :
    ((List.range N).filter fun c => key c < key g[d]).length ≤ d ∧
      d < ((List.range N).filter fun c => key c ≤ key g[d]).length := by
  have hle : ∀ e (he : e < g.length), d ≤ e → key g[d] ≤ key g[e] := fun e he hde => by
    rcases Nat.lt_or_eq_of_le hde with h | rfl
    · exact List.pairwise_iff_getElem.1 hs d e hd he h
    · exact Nat.le_refl _
  have hge : ∀ e (he : e < g.length), e ≤ d → key g[e] ≤ key g[d] := fun e he hed => by
    rcases Nat.lt_or_eq_of_le hed with h | rfl
    · exact List.pairwise_iff_getElem.1 hs e d he hd h
    · exact Nat.le_refl _
  constructor
  · rw [← (hp.filter _).length_eq]
    have hsplit : (g.filter fun c => decide (key c < key g[d])).length =
        ((g.take d).filter fun c => decide (key c < key g[d])).length +
          ((g.drop d).filter fun c => decide (key c < key g[d])).length := by
      rw [← List.length_append, ← List.filter_append, List.take_append_drop]
    have h0 : ((g.drop d).filter fun c => decide (key c < key g[d])).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hc
      rw [List.getElem_drop]
      simp only [List.length_drop] at he
      have := hle (d + e) (by omega) (by omega)
      simp only [decide_eq_true_eq]; omega
    have := List.length_filter_le (fun c => decide (key c < key g[d])) (g.take d)
    simp only [List.length_take] at this
    omega
  · rw [← (hp.filter _).length_eq]
    have hsub : ((g.take (d + 1)).filter fun c => decide (key c ≤ key g[d])) = g.take (d + 1) := by
      rw [List.filter_eq_self]
      intro c hc
      obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hc
      rw [List.getElem_take]
      simp only [List.length_take] at he
      simp only [decide_eq_true_eq]; exact hge e (by omega) (by omega)
    have := ((List.take_sublist (d + 1) g).filter (fun c => decide (key c ≤ key g[d]))).length_le
    rw [hsub, List.length_take] at this
    omega

/-- Of `til N`, the elements below `M`: `min M N` of them. -/
theorem filter_range_lt (M : Nat) : ∀ N, ((List.range N).filter fun c => decide (c < M)).length = min M N
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, filter_range_lt M N]
    by_cases hN : N < M <;> simp [hN] <;> omega

/-- **A key-sorted permutation holds each key's elements in that key's block**: `g` lists `til N` non-decreasing
    in `key`, the elements of key `r < n` being `[P r, P (r+1))` (`P` non-decreasing, `P n = N`); `g`'s block at
    `[P r, P (r+1))` is a permutation of them. -/
theorem sorted_block_perm {N n : Nat} (g : List Nat) (key P : Nat → Nat) (hp : g.Perm (List.range N))
    (hs : g.Pairwise fun a b => key a ≤ key b) (hP : ∀ r < n, P r ≤ P (r + 1)) (hPn : P n = N)
    (hkey : ∀ c < N, key c < n ∧ P (key c) ≤ c ∧ c < P (key c + 1)) (r : Nat) (hr : r < n) :
    ((g.drop (P r)).take (P (r + 1) - P r)).Perm (List.range' (P r) (P (r + 1) - P r)) := by
  have hle : ∀ a b, a ≤ b → b ≤ n → P a ≤ P b := by
    intro a b
    induction b with
    | zero => intro hab _; rw [Nat.le_zero.1 hab]; exact Nat.le_refl _
    | succ b ih =>
      intro hab hb
      by_cases h : a ≤ b
      · exact Nat.le_trans (ih h (by omega)) (hP b (by omega))
      · rw [show a = b + 1 by omega]; exact Nat.le_refl _
  have hmem : ∀ e (he : e < g.length), g[e] < N := fun e he =>
    List.mem_range.1 (hp.mem_iff.1 (List.getElem_mem he))
  -- the elements of key below `k` are the first `P k`
  have hcnt : ∀ k, k ≤ n → ((List.range N).filter fun c => decide (key c < k)).length = P k := fun k hk => by
    rw [List.filter_congr (p := fun c => decide (key c < k)) (q := fun c => decide (c < P k)) fun c hc => by
      obtain ⟨h1, h2, h3⟩ := hkey c (List.mem_range.1 hc)
      rw [decide_eq_decide]
      constructor
      · intro h; have := hle (key c + 1) k (by omega) hk; omega
      · intro h; refine Nat.lt_of_not_le fun h' => ?_; have := hle k (key c) h' (by omega); omega]
    rw [filter_range_lt, Nat.min_eq_left (by rw [← hPn]; exact hle k n hk (Nat.le_refl _))]
  -- position `d` holds an element of key `k` exactly where `P k ≤ d < P (k+1)`
  have hpos : ∀ d (hd : d < g.length), P (key g[d]) ≤ d ∧ d < P (key g[d] + 1) := fun d hd => by
    obtain ⟨h1, h2⟩ := sorted_block g key hp hs d hd
    have hk := (hkey _ (hmem d hd)).1
    rw [hcnt _ (by omega)] at h1
    rw [List.filter_congr (p := fun c => decide (key c ≤ key g[d])) (q := fun c => decide (key c < key g[d] + 1))
      fun c _ => by simp only [Nat.lt_succ_iff], hcnt _ (by omega)] at h2
    exact ⟨h1, h2⟩
  have hPs := hP r hr
  -- an element between `P r` and `P (r+1)` is of key `r`
  have hkr : ∀ x, x < N → P r ≤ x → x < P (r + 1) → key x = r := fun x hx h1 h2 => by
    obtain ⟨hk, e1, e2⟩ := hkey x hx
    rcases Nat.lt_trichotomy (key x) r with h | h | h
    · have := hle (key x + 1) r h (by omega); omega
    · exact h
    · have := hle (r + 1) (key x) h (by omega); omega
  have hnd : g.Nodup := hp.nodup_iff.2 List.nodup_range
  have hbnd := hnd.sublist ((List.take_sublist (P (r + 1) - P r) _).trans (List.drop_sublist (P r) g))
  have hnr : (List.range' (P r) (P (r + 1) - P r)).Nodup := List.nodup_range'
  refine List.perm_iff_count.2 fun a => ?_
  have hiff : a ∈ (g.drop (P r)).take (P (r + 1) - P r) ↔ a ∈ List.range' (P r) (P (r + 1) - P r) := by
    rw [List.mem_range'_1]
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hx
      rw [List.getElem_take, List.getElem_drop]
      simp only [List.length_take, List.length_drop] at hu
      have hd : P r + u < g.length := by omega
      obtain ⟨e1, e2⟩ := hpos (P r + u) hd
      have hx := hmem _ hd
      have hk := (hkey _ hx).1
      have hke : key g[P r + u] = r := by
        rcases Nat.lt_trichotomy (key g[P r + u]) r with h | h | h
        · have := hle (key g[P r + u] + 1) r h (by omega); omega
        · exact h
        · have := hle (r + 1) (key g[P r + u]) h (by omega); omega
      obtain ⟨-, f1, f2⟩ := hkey _ hx
      rw [hke] at f1 f2
      omega
    · intro ⟨h1, h2⟩
      have ha : a < N := by have := hle (r + 1) n (by omega) (Nat.le_refl _); omega
      obtain ⟨e, he, rfl⟩ := List.mem_iff_getElem.1 (hp.mem_iff.2 (List.mem_range.2 ha))
      obtain ⟨e1, e2⟩ := hpos e he
      rw [hkr _ ha h1 (by omega)] at e1 e2
      have hu : e - P r < ((g.drop (P r)).take (P (r + 1) - P r)).length := by
        simp only [List.length_take, List.length_drop]; omega
      have h' : ((g.drop (P r)).take (P (r + 1) - P r))[e - P r] = g[e] := by
        rw [List.getElem_take, List.getElem_drop]; simp only [Nat.add_sub_cancel' (show P r ≤ e by omega)]
      rw [← h']; exact List.getElem_mem hu
  rw [List.Nodup.count hbnd, List.Nodup.count hnr]
  simp only [hiff]

/-- **`Obj.sortBy` at `long` of `til m`, read back**: every cell once, by value ascending, ties in cell order. -/
theorem sortBy_long {m : USize} (cells : Vals (.atom .long) m) :
    (ids (Obj.sortBy (.atom .long) cells (tilLongs m))).Perm (List.range m.toNat) ∧
      (ids (Obj.sortBy (.atom .long) cells (tilLongs m))).Pairwise fun c c' =>
        ∀ (hc : c < m.toNat) (hc' : c' < m.toNat),
          cells.get ⟨c, hc⟩ < cells.get ⟨c', hc'⟩ ∨ (cells.get ⟨c, hc⟩ = cells.get ⟨c', hc'⟩ ∧ c < c') := by
  have hl : len (tilLongs m) < USize.size := by rw [len_tilLongs]; exact m.toNat_lt_size
  have hx := pick_len .long ⟨_, cells⟩ (tilLongs m) hl
  rw [len_tilLongs] at hx
  have hget : ∀ k (hk : k < (pick .long ⟨_, cells⟩ (tilLongs m)).1.toNat) (hk' : k < m.toNat),
      (pick .long ⟨_, cells⟩ (tilLongs m)).2.get ⟨k, hk⟩ = cells.get ⟨k, hk'⟩ := fun k hk hk' => by
    rw [pick_get ⟨_, cells⟩ (tilLongs m) hl k hk (by rw [tilLongs_get hk']; exact hk')]
    exact congrArg cells.get (Fin.ext (tilLongs_get hk'))
  simp only [Obj.sortBy]
  rw [gradeColumn_long]
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hp, hs⟩ := grade_long (pick .long ⟨_, cells⟩ (tilLongs m)).2
  rw [hx] at hp
  generalize Order.grade .i64 false (pick .long ⟨_, cells⟩ (tilLongs m)).1
    (longsOf (pick .long ⟨_, cells⟩ (tilLongs m)).2) = G at hp hs
  have hGm : ∀ t ∈ ids G, t < len (tilLongs m) := fun t ht => by
    rw [len_tilLongs]; exact List.mem_range.1 (hp.mem_iff.1 ht)
  have e : ids (gather 8 (tilLongs m) G) = ids G := by
    rw [ids_gather8 hGm]
    refine (List.map_congr_left fun j hj => ?_).trans (List.map_id _)
    have hjm := List.mem_range.1 (hp.mem_iff.1 hj)
    have hj' : j < (ids (tilLongs m)).length := by rw [← len_eq_ids, len_tilLongs]; exact hjm
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, ids_getElem hj',
      tilLongs_get hjm]; rfl
  rw [e]
  refine ⟨hp, hs.imp_of_mem fun {c c'} hc hc' h hm hm' => ?_⟩
  have hk := List.mem_range.1 (hp.mem_iff.1 hc); have hk' := List.mem_range.1 (hp.mem_iff.1 hc')
  have h1 := h (by rw [hx]; exact hk) (by rw [hx]; exact hk')
  rwa [hget c _ hm, hget c' _ hm'] at h1

#print axioms sortBy_long
#print axioms filter_range_lt
#print axioms sorted_block_perm
#print axioms grade_group
#print axioms sorted_block
#print axioms key_i64
#print axioms grade_i64
#print axioms gradeColumn_long
#print axioms grade_long
#print axioms grade_ofLongs

end LeetQ.Rel.Alg
