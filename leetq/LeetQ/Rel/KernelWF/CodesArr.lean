/-
  An array side's joint codes, faithful and well formed, from its elements' — the `.arr` branch of
  `Obj.codes` in the shape `codes_prod_faithful_wf` has.

  Every index in a statement here carries its bound explicitly (`xs[k]'hk`): left to `get_elem_tactic`,
  the index proofs of this many binders ran Lean out of memory before any tactic.
-/
import LeetQ.Rel.KernelWF.CodesRec
import LeetQ.Rel.KernelWF.SliceSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

-- row `r`'s clamped window of the array side `x`, as `Vals.row` reads it (`SliceSpec`'s)
set_option hygiene false in
local notation "sL(" x ", " r ", " h ")" => min (max (Int64.toInt (Arr.get x.2.1 ⟨r, h⟩)) 0).toNat x.1.toNat
set_option hygiene false in
local notation "sH(" x ", " r ", " h ")" => min (max (Int64.toInt (Arr.get x.2.2.1 ⟨r, h⟩)) 0).toNat x.1.toNat
-- the copies of row `t` (`slicesOf_copies`' right side), and the copies before row `r`
set_option hygiene false in
local notation "cG(" n ", " x ", " t ")" => if h : t < USize.toNat n then
  (List.range (sH(x, t, h) - sL(x, t, h))).map fun j => (t, sL(x, t, h) + j) else []
set_option hygiene false in
local notation "cS(" n ", " x ", " r ")" => ((List.range r).map fun t => (cG(n, x, t)).length).sum
-- `Obj.codes`' gathered element codes of one array part, the element codes `e`
set_option hygiene false in
local notation "gX(" n ", " x ", " e ")" => expand n (slicesOf x).2 (fun _ => default) fun k i r _ _ =>
  Code.gather e (add k (gather 8 (slicesOf x).1 i) r)

/-- **One array part's gathered element codes**: the element codes `e` read at each row's window, rows end to
    end — code `cS r + j` is element code `L r + j`, `L r` row `r`'s clamped start (`slicesOf_copies`). -/
theorem arr_gather_part {B : Obj} {n : USize} (x : Vals (.arr B) n)
    (hf : Vals.PickFits (.arr B) x (List.range n.toNat)) (e : Code)
    (hw : e.w = 1 ∨ e.w = 2 ∨ e.w = 4 ∨ e.w = 8 ∨ e.w = 16 ∨ e.w = 32 ∨ e.w = 64) (hn : e.n = x.1)
    (hs : e.b.size = (e.n.toNat * e.w + 7) / 8) :
    (gX(n, x, e)).w = e.w ∧ (gX(n, x, e)).n.toNat = cS(n, x, n.toNat) ∧ (gX(n, x, e)).card = e.card ∧
      (gX(n, x, e)).b.size = ((gX(n, x, e)).n.toNat * (gX(n, x, e)).w + 7) / 8 ∧
      (∀ C, (∀ i < e.n.toNat, Column.idAt e.b e.w i < C) → ∀ z < (gX(n, x, e)).n.toNat,
        Column.idAt (gX(n, x, e)).b e.w z < C) ∧
      ∀ r (hr : r < n.toNat), ∀ j < sH(x, r, hr) - sL(x, r, hr),
        Column.idAt (gX(n, x, e)).b e.w (cS(n, x, r) + j) = Column.idAt e.b e.w (sL(x, r, hr) + j) := by
  obtain ⟨hU, hL⟩ := slicesOf_copies x hf
  have hexp : gX(n, x, e) = Code.gather e (add (len (expandBytes 8 0 (tilLongs n) (slicesOf x).2)).toUSize
      (gather 8 (slicesOf x).1 (expandBytes 8 0 (tilLongs n) (slicesOf x).2))
      (sub (len (expandBytes 8 0 (tilLongs n) (slicesOf x).2)).toUSize
        (tilLongs (len (expandBytes 8 0 (tilLongs n) (slicesOf x).2)).toUSize)
        (gather 8 (sub n (sums n (slicesOf x).2) (slicesOf x).2) (expandBytes 8 0 (tilLongs n) (slicesOf x).2)))) := by
    simp only [expand, need, dif_pos hU]
  rw [hexp]
  generalize hE : expandBytes 8 0 (tilLongs n) (slicesOf x).2 = E at hU hL
  have hlenP : len (add (len E).toUSize (gather 8 (slicesOf x).1 E)
      (sub (len E).toUSize (tilLongs (len E).toUSize) (gather 8 (sub n (sums n (slicesOf x).2) (slicesOf x).2) E))) =
      len E := by unfold add; exact (len_val ..).trans (USize.toNat_ofNat_of_lt' hU)
  have hM : len E = cS(n, x, n.toNat) := by
    have := congrArg List.length hL
    rw [List.length_map, List.length_range, List.length_flatMap] at this; exact this
  have hin : ∀ z < len (add (len E).toUSize (gather 8 (slicesOf x).1 E)
      (sub (len E).toUSize (tilLongs (len E).toUSize) (gather 8 (sub n (sums n (slicesOf x).2) (slicesOf x).2) E))),
      (Column.bitsAt (add (len E).toUSize (gather 8 (slicesOf x).1 E)
        (sub (len E).toUSize (tilLongs (len E).toUSize)
          (gather 8 (sub n (sums n (slicesOf x).2) (slicesOf x).2) E))) (z * 8) 8).toNat < e.n.toNat := by
    intro z hz
    rw [hlenP, ← hE] at hz
    obtain ⟨r, hr, j, hj, -, hp⟩ := copy_row x hf hz
    rw [← hE, hp, hn]
    have : sH(x, r, hr) ≤ x.1.toNat := Nat.min_le_right _ _
    omega
  have hcb : 8 ≤ e.w → 8 * e.b.size = e.w * e.n.toNat := fun h8 => by
    rw [hs]; rcases hw with h | h | h | h | h | h | h <;> rw [h] at h8 ⊢ <;> omega
  obtain ⟨g1, g2, g3, g4⟩ := gather_spec e _ (by rw [hlenP]; exact hU) hw hcb hin
  have gs := gather_size e _ (by rw [hlenP]; exact hU) hw
  refine ⟨g1, by rw [g2, hlenP, hM], g3, by rw [gs, g2, g1],
    fun C hC z hz => by rw [g2] at hz; rw [g4 z hz]; exact hC _ (hin z hz), fun r hr j hj => ?_⟩
  have hq := flatMap_get_at (fun t => cG(n, x, t)) (m := n.toNat) hr (q := j)
    (by dsimp only; rw [dif_pos hr, List.length_map, List.length_range]; exact hj)
  dsimp only at hq
  rw [dif_pos hr, List.getElem?_map, List.getElem?_range hj, Option.map_some, ← hL] at hq
  have hz : cS(n, x, r) + j < len E := by
    have h1 := sum_range_le (fun t => (cG(n, x, t)).length) (show r + 1 ≤ n.toNat by omega)
    rw [sum_range_succ'] at h1
    dsimp only at h1
    rw [dif_pos hr, List.length_map, List.length_range] at h1
    rw [hM]; omega
  rw [List.getElem?_map, List.getElem?_range hz, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
  rw [g4 _ (by rw [hlenP]; exact hz), hq.2]

#print axioms arr_gather_part

/-- **Byte payloads end to end, read back**: the long at byte `8i` of part `k` sits past the parts before it. -/
theorem concat_long_get (l : List ByteArray) {k : Nat} (hk : k < l.length) {i : Nat} (hi : 8 * i + 8 ≤ l[k].size) :
    Column.bitsAt (l.foldl (· ++ ·) ByteArray.empty) (((l.take k).map (·.size)).sum + 8 * i) 8 =
      Column.bitsAt l[k] (8 * i) 8 := by
  refine KernelWF.bitsAt_congr fun j hj => ?_
  have h := foldl_append_get l ByteArray.empty hk (j := 8 * i + j) (by omega)
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add] at h
  rw [Nat.add_assoc]; exact h

#print axioms concat_long_get

/-- `enumIds` at a whole-byte lane `8c` of nonnegative longs below `2^(8c)`, read back: each long, `⌈n·8c/8⌉` bytes. -/
theorem enumIds_lane_get (n d : USize) (gid : ByteArray) {c : Nat} (hc : c = 1 ∨ c = 2 ∨ c = 4)
    (hv : ∀ g < n.toNat, (Column.bitsAt gid (g * 8) 8).toNat < 2 ^ (8 * c)) :
    (enumIds n d 0 (8 * c).toUSize gid).1.size = (n.toNat * (8 * c) + 7) / 8 ∧
      ∀ g < n.toNat, Column.idAt (enumIds n d 0 (8 * c).toUSize gid).1 (8 * c) g =
        (Column.bitsAt gid (g * 8) 8).toNat := by
  simp only [enumIds]
  rw [lane_toNat (by omega)]
  refine ⟨packIds_size (by rcases hc with rfl | rfl | rfl <;> decide) _ _, fun g hg => ?_⟩
  have hu : (Column.bitsAt gid (g * 8) 8).toNat < 2 ^ 63 :=
    Nat.lt_of_lt_of_le (hv g hg) (Nat.pow_le_pow_right (by decide) (by omega))
  have e := toInt64_toInt hu
  have hm : Int64.minValue.toInt = -2 ^ 63 := by decide
  rw [idAt_packIds_lane c _ _ (by omega) (by omega) hg]
  · split
    · next h => rw [beq_iff_eq.1 h, hm] at e; omega
    · omega
  · split
    · exact Nat.two_pow_pos _
    · rw [e]; exact hv g hg

/-- **`pack` read back**: the ids `gid`, each below `N`, at `codeKind N`'s byte lane — the codes are the ids. -/
theorem pack_get (N : Nat) (gid : ByteArray) (hl : len gid < USize.size) (hsz : gid.size = 8 * len gid)
    (hv : ∀ g < len gid, (Column.bitsAt gid (g * 8) 8).toNat < N) :
    ((pack N gid).w = 8 ∨ (pack N gid).w = 16 ∨ (pack N gid).w = 32 ∨ (pack N gid).w = 64) ∧
      (pack N gid).n.toNat = len gid ∧ (pack N gid).card = N ∧
      (pack N gid).b.size = ((pack N gid).n.toNat * (pack N gid).w + 7) / 8 ∧
      ∀ g < len gid, Column.idAt (pack N gid).b (pack N gid).w g = (Column.bitsAt gid (g * 8) 8).toNat := by
  have hn : (len gid).toUSize.toNat = len gid := USize.toNat_ofNat_of_lt' hl
  unfold pack longCount
  simp only [need, dif_pos hl]
  have lane : ∀ c, (c = 1 ∨ c = 2 ∨ c = 4) → N ≤ 2 ^ (8 * c) →
      (enumIds (len gid).toUSize N.toUSize 0 (8 * c).toUSize gid).1.size = ((len gid) * (8 * c) + 7) / 8 ∧
      ∀ g < len gid, Column.idAt (enumIds (len gid).toUSize N.toUSize 0 (8 * c).toUSize gid).1 (8 * c) g =
        (Column.bitsAt gid (g * 8) 8).toNat := fun c h1 hN => by
    have := enumIds_lane_get (len gid).toUSize N.toUSize gid h1 (fun g hg => by
      rw [hn] at hg; exact Nat.lt_of_lt_of_le (hv g hg) hN)
    rw [hn] at this; exact this
  unfold codeKind
  split
  · next h => obtain ⟨s, f⟩ := lane 1 (by decide) h
              rw [if_neg (by decide)]
              exact ⟨Or.inl rfl, hn, trivial, by rw [hn]; exact s, f⟩
  split
  · next h => obtain ⟨s, f⟩ := lane 2 (by decide) h
              rw [if_neg (by decide)]
              exact ⟨Or.inr (Or.inl rfl), hn, trivial, by rw [hn]; exact s, f⟩
  split
  · next h => obtain ⟨s, f⟩ := lane 4 (by decide) h
              rw [if_neg (by decide)]
              exact ⟨Or.inr (Or.inr (Or.inl rfl)), hn, trivial, by rw [hn]; exact s, f⟩
  rw [if_pos (by decide)]
  refine ⟨Or.inr (Or.inr (Or.inr rfl)), hn, trivial, by rw [hn, hsz]; show _ = (_ * (8 * 8) + 7) / 8; omega,
    fun g hg => ?_⟩
  show Column.idAt gid (8 * 8) g = _
  rw [idAt_lane _ (by decide)]

#print axioms pack_get

/-- **An array part's count column**: `n` longs, row `r`'s the length of its clamped window (`slices_get`). -/
theorem slicesOf_count {B : Obj} {n : USize} (x : Vals (.arr B) n) (hp : x.1.toNat < 2 ^ 63) :
    (slicesOf x).2.size = 8 * n.toNat ∧
      ∀ r < n.toNat, (Column.bitsAt (slicesOf x).2 (r * 8) 8).toNat = (cG(n, x, r)).length := by
  refine ⟨?_, fun r hr => ?_⟩
  · simp only [slicesOf, slices, sub, KernelWF.Ew.val_size]
    rw [show Kernel.Ew.width Ew.i64 = 8 by decide, Nat.mul_comm]
  have hsl := slices_get (n := n) hp (longsOf x.2.1) (longsOf x.2.2.1) hr
  rw [longsOf_get _ hr, longsOf_get _ hr, Int64.toInt64_toUInt64, Int64.toInt64_toUInt64] at hsl
  show (Column.bitsAt (slices x.1 n (longsOf x.2.1) (longsOf x.2.2.1)).2 (r * 8) 8).toNat = _
  rw [hsl.2, dif_pos hr, List.length_map, List.length_range]
  have : sH(x, r, hr) ≤ x.1.toNat := Nat.min_le_right _ _
  exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)

#print axioms slicesOf_count

/-- **A running total across blocks**: the total of `a` up to row `r` of block `k` is the blocks before it, whole,
    plus block `k`'s first `r` — `a` read block by block as `c`, `Ms` each block's whole total. -/
theorem sum_blocks (a : Nat → Nat) (ns Ms : List Nat) (c : Nat → Nat → Nat) (hl : Ms.length = ns.length)
    (hM : ∀ k (hk : k < ns.length), Ms[k]'(hl ▸ hk) = ((List.range ns[k]).map (c k)).sum)
    (h : ∀ k (hk : k < ns.length), ∀ r < ns[k], a ((ns.take k).sum + r) = c k r) :
    ∀ k (hk : k < ns.length), ∀ r ≤ ns[k],
      ((List.range ((ns.take k).sum + r)).map a).sum = (Ms.take k).sum + ((List.range r).map (c k)).sum := by
  have ts : ∀ (l : List Nat) i (hi : i < l.length), (l.take (i + 1)).sum = (l.take i).sum + l[i] := fun l i hi => by
    rw [List.take_add_one, List.sum_append_nat, List.getElem?_eq_getElem hi]; simp
  have inner : ∀ k (hk : k < ns.length), ((List.range (ns.take k).sum).map a).sum = (Ms.take k).sum →
      ∀ r ≤ ns[k], ((List.range ((ns.take k).sum + r)).map a).sum =
        (Ms.take k).sum + ((List.range r).map (c k)).sum := by
    intro k hk h0 r
    induction r with
    | zero => intro _; simpa using h0
    | succ r ih =>
      intro hr
      rw [show (ns.take k).sum + (r + 1) = ((ns.take k).sum + r) + 1 by omega, sum_range_succ', sum_range_succ',
        ih (by omega), h k hk r (by omega)]
      omega
  intro k
  induction k with
  | zero => intro hk; exact inner 0 hk (by simp)
  | succ k ih =>
    intro hk
    refine inner (k + 1) hk ?_
    have := ih (by omega) ns[k] (Nat.le_refl _)
    rw [ts ns k (by omega), ts Ms k (by omega), this, hM k (by omega)]

#print axioms sum_blocks

/-- **The offsets `Obj.codes` hands `rankSlices`**: `0`, then the running totals of the `T` counts — offset `g`
    is the total of the first `g` counts, the totals below `2^63`. -/
theorem offsets_get (T : USize) (cnts : ByteArray) (hT : T.toNat ≤ len cnts)
    (hS : ((List.range T.toNat).map fun i => (Column.bitsAt cnts (i * 8) 8).toNat).sum < 2 ^ 63) :
    (concatBytes #[one 0, sums T cnts]).size / 8 = T.toNat + 1 ∧
      ∀ g ≤ T.toNat, (Column.bitsAt (concatBytes #[one 0, sums T cnts]) (8 * g) 8).toNat =
        ((List.range g).map fun i => (Column.bitsAt cnts (i * 8) 8).toNat).sum := by
  have hc : concatBytes #[one 0, sums T cnts] = [one 0, sums T cnts].foldl (· ++ ·) ByteArray.empty := by
    rw [concatBytes, ← Array.foldl_toList]
  have h1 : (one 0).size = 8 := by simp [one, Column.pushBits_size]
  have h2 : (sums T cnts).size / 8 = T.toNat := by
    have := len_sums T cnts; simp only [len] at this hT ⊢; rw [this]; omega
  refine ⟨by rw [KernelWF.concatBytes_size]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega,
    fun g hg => ?_⟩
  rw [hc]
  cases g with
  | zero =>
    have := concat_long_get [one 0, sums T cnts] (k := 0) (by simp) (i := 0) (by simp [h1])
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] at this
    rw [Nat.mul_zero, this]
    show (Column.bitsAt (one 0) 0 8).toNat = _
    (rw [bitsAt_one]) <;> rfl
  | succ g =>
    have := concat_long_get [one 0, sums T cnts] (k := 1) (by simp) (i := g)
      (by show 8 * g + 8 ≤ (sums T cnts).size; omega)
    simp only [List.take_succ, List.take_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1,
      List.getElem?_cons_zero, Option.toList_some, List.nil_append, List.map_cons, Nat.add_zero] at this
    rw [show 8 * (g + 1) = 8 + 8 * g by omega, this]
    show (Column.bitsAt (sums T cnts) (8 * g) 8).toNat = _
    rw [Nat.mul_comm 8 g]
    exact sums_get (by omega) (by omega) (Nat.lt_of_le_of_lt (sum_range_le _ hg) hS)

#print axioms offsets_get

/-- Two lists read off a prefix of the naturals are equal exactly when the prefixes and the readings are. -/
theorem list_map_range_iff {α : Type} (a c : Nat) (f g : Nat → α) :
    (List.range a).map f = (List.range c).map g ↔ a = c ∧ ∀ t < a, f t = g t := by
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_map, List.length_range] at hl
    subst hl
    refine ⟨rfl, fun t ht => ?_⟩
    have := congrArg (·[t]?) h
    simpa [List.getElem?_map, List.getElem?_range ht] using this
  · rintro ⟨rfl, h⟩
    exact List.map_congr_left fun t ht => h t (List.mem_range.1 ht)

/-- `list_map_range_iff` for arrays. -/
theorem array_map_range_iff {α : Type} (a c : Nat) (f g : Nat → α) :
    (Array.range a).map f = (Array.range c).map g ↔ a = c ∧ ∀ t < a, f t = g t := by
  rw [← Array.toList_inj, Array.toList_map, Array.toList_map, Array.toList_range, Array.toList_range]
  exact list_map_range_iff a c f g

/-- `sliceIds` is `rankSlices`: both branches of its check answer the ids. -/
theorem sliceIds_eq (vc : Code) (o : ByteArray) : sliceIds vc o = Order.rankSlices vc.w.toUSize vc.b o := by
  unfold sliceIds need; dsimp only; split <;> rfl

/-- A running total of `toNat`s, as a fold. -/
theorem foldl_toNat_sum : ∀ (l : List USize) (a : Nat), l.foldl (fun s n => s + n.toNat) a = a + (l.map (·.toNat)).sum
  | [], a => by simp
  | n :: l, a => by simp only [List.foldl_cons, List.map_cons, List.sum_cons]; rw [foldl_toNat_sum l]; omega

/-- An array row's length is its clamped window's. -/
theorem row_length {B : Obj} {n : USize} (x : Vals (.arr B) n) {r : Nat} (hr : r < n.toNat) :
    (Vals.row x ⟨r, hr⟩).length = (cG(n, x, r)).length := by
  rw [arr_row, dif_pos hr]; simp

/-- A total over the first `k` of a list, then one more. -/
theorem sum_take_succ (l : List Nat) (i : Nat) (hi : i < l.length) : (l.take (i + 1)).sum = (l.take i).sum + l[i] := by
  rw [List.take_add_one, List.sum_append_nat, List.getElem?_eq_getElem hi]; simp

/-- `8 ·` through a prefix total. -/
theorem sum_take_mul8 {α : Type} (f : α → Nat) : ∀ (l : List α) (k : Nat),
    ((l.take k).map fun c => 8 * f c).sum = 8 * ((l.take k).map f).sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | c :: l, k + 1 => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; rw [sum_take_mul8 f l k]; omega

/-- **`Obj.codes` at an array side**, its `let`s spelled out. -/
theorem codes_arr_eq {b : Obj} {p : Nat} (cs : Vector (Part (.arr b)) p) :
    Obj.codes (.arr b) cs = longCount "codes" (concatBytes ((cs.map fun c => (c.1, slicesOf c.2)).map (·.2.2)).toArray)
      fun t _ => (pack ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0)
        (sliceIds (Code.cat (Vector.zipWith (fun e s => expand s.1 s.2.2 (fun _ => default) fun k i r _ _ =>
            e.gather (add k (gather 8 s.2.1 i) r)) (Obj.codes b (cs.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)))
            (cs.map fun c => (c.1, slicesOf c.2))).toArray)
          (concatBytes #[one 0, sums t (concatBytes ((cs.map fun c => (c.1, slicesOf c.2)).map (·.2.2)).toArray)]))).cut
        (cs.map (·.1)) := by
  rw [Obj.codes]

/-- **An array side's codes are faithful and well formed, on one lane**, given its elements' are, one lane:
    each row's window of element codes gathered contiguous (`arr_gather_part`), the parts laid end to end
    (`cat_parts`), the windows numbered by `rankSlices` at the running totals of the windows' lengths, those
    numbers `pack`ed and cut back. Bounds: the parts' summed row count and their summed element count `USize`s,
    the latter below `2^63` (the longs `sums` totals in), and each part's rows read back (`Vals.PickFits`). -/
theorem codes_arr_faithful_wf {b : Obj} {p : Nat} (cs : Vector (Part (.arr b)) p)
    {pe : Vector (Part b) p} {ce : Vector Code p}
    (hpe : cs.map (fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)) = pe) (hce : Obj.codes b pe = ce)
    (hfe : (∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (pe[k]'hk).1.toNat)
        (hj : j < (pe[l]'hl).1.toNat),
        Column.idAt (ce[k]'hk).b (ce[k]'hk).w i = Column.idAt (ce[l]'hl).b (ce[l]'hl).w j ↔
          Vals.row (pe[k]'hk).2 ⟨i, hi⟩ = Vals.row (pe[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        ((ce[k]'hk).w = 1 ∨ (ce[k]'hk).w = 2 ∨ (ce[k]'hk).w = 4 ∨ (ce[k]'hk).w = 8 ∨ (ce[k]'hk).w = 16 ∨
          (ce[k]'hk).w = 32 ∨ (ce[k]'hk).w = 64) ∧
        (ce[k]'hk).n = (pe[k]'hk).1 ∧ (ce[k]'hk).b.size = ((ce[k]'hk).n.toNat * (ce[k]'hk).w + 7) / 8 ∧
        ((ce[k]'hk).w < 8 → (ce[k]'hk).card < USize.size ∧
          ∀ i < (ce[k]'hk).n.toNat, Column.idAt (ce[k]'hk).b (ce[k]'hk).w i < (ce[k]'hk).card))
    (hle : ∀ {k l : Nat} (hk : k < p) (hl : l < p), (ce[k]'hk).w = (ce[l]'hl).w)
    (hfit : ∀ {k : Nat} (hk : k < p), Vals.PickFits (.arr b) (cs[k]'hk).2 (List.range (cs[k]'hk).1.toNat))
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hC : (cs.toList.map fun c => ((List.range c.1.toNat).map fun r =>
        if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum).sum < 2 ^ 63)
    (hCU : (cs.toList.map fun c => ((List.range c.1.toNat).map fun r =>
        if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum).sum < USize.size) :
    ((∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat)
        (hj : j < (cs[l]'hl).1.toNat),
        Column.idAt ((Obj.codes (.arr b) cs)[k]'hk).b ((Obj.codes (.arr b) cs)[k]'hk).w i =
          Column.idAt ((Obj.codes (.arr b) cs)[l]'hl).b ((Obj.codes (.arr b) cs)[l]'hl).w j ↔
        Vals.row (A := .arr b) (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (A := .arr b) (cs[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        let c := (Obj.codes (.arr b) cs)[k]'hk
        (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = (cs[k]'hk).1 ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ {k l : Nat} (hk : k < p) (hl : l < p),
        ((Obj.codes (.arr b) cs)[k]'hk).w = ((Obj.codes (.arr b) cs)[l]'hl).w := by
  obtain ⟨hfe, hwe⟩ := hfe
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨⟨fun {_ _} hk => absurd hk (Nat.not_lt_zero _), fun {_} hk => absurd hk (Nat.not_lt_zero _)⟩,
      fun {_ _} hk => absurd hk (Nat.not_lt_zero _)⟩
  have hpe' : ∀ k (hk : k < p), pe[k]'hk = ⟨(cs[k]'hk).2.1, (cs[k]'hk).2.2.2.2⟩ := fun k hk => by
    rw [← hpe, Vector.getElem_map]
  have hp63 : ∀ k (hk : k < p), (cs[k]'hk).2.1.toNat < 2 ^ 63 := fun k hk => (pickFits_payload _ (hfit hk)).1
  -- row `r`'s window length in part `k`, `0` past the parts
  let cw : Nat → Nat → Nat := fun k r => if hk : k < p then (cG((cs[k]'hk).1, (cs[k]'hk).2, r)).length else 0
  have hcw : ∀ k (hk : k < p) r, cw k r = (cG((cs[k]'hk).1, (cs[k]'hk).2, r)).length := fun k hk r => dif_pos hk
  have hcS : ∀ k (hk : k < p) r, ((List.range r).map (cw k)).sum = cS((cs[k]'hk).1, (cs[k]'hk).2, r) :=
    fun k hk r => congrArg List.sum (List.map_congr_left fun t _ => hcw k hk t)
  rw [codes_arr_eq, hpe, hce]
  generalize hcx : Vector.zipWith (fun e s => expand s.1 s.2.2 (fun _ => default) fun k i r _ _ =>
      e.gather (add k (gather 8 s.2.1 i) r)) ce (cs.map fun c => (c.1, slicesOf c.2)) = cx
  -- `m`, not `k`: `gX` binds `k` in its body and the argument is spliced under that binder
  have hcxk : ∀ m (hm : m < p), cx[m]'hm = gX((cs[m]'hm).1, (cs[m]'hm).2, ce[m]'hm) := fun m hm => by
    rw [← hcx, Vector.getElem_zipWith, Vector.getElem_map]
  have hG := fun k (hk : k < p) => arr_gather_part (cs[k]'hk).2 (hfit hk) (ce[k]'hk) (hwe hk).1
    (by rw [(hwe hk).2.1, hpe' k hk]) (hwe hk).2.2.1
  -- the parts' gathered codes, laid end to end
  have hMk : ∀ k (hk : k < p), (cx[k]'hk).n.toNat = ((List.range (cs[k]'hk).1.toNat).map (cw k)).sum := fun k hk => by
    rw [hcxk k hk, (hG k hk).2.1, hcS k hk]
  have hMs : cx.toList.map (·.n.toNat) = cs.toList.map fun c => ((List.range c.1.toNat).map fun r =>
      if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    have hk : k < p := by simpa using h2
    simp only [List.getElem_map, Vector.getElem_toList]
    rw [hMk k hk]
    congr 1
    refine List.map_congr_left fun r hr => ?_
    rw [List.mem_range] at hr
    rw [dif_pos hr, row_length _ hr, hcw k hk]
    rfl
  have catA := cat_parts cx hp (fun hk hl => by rw [hcxk _ hk, hcxk _ hl, (hG _ hk).1, (hG _ hl).1]; exact hle hk hl)
    (fun hk => by
      rw [hcxk _ hk]
      refine ⟨by rw [(hG _ hk).1]; exact (hwe hk).1, (hG _ hk).2.2.2.1, fun h8 i hi => ?_⟩
      rw [(hG _ hk).1] at h8
      rw [(hG _ hk).1, (hG _ hk).2.2.1]
      exact (hG _ hk).2.2.2.2.1 _ (fun i hi => Nat.lt_of_lt_of_le (((hwe hk).2.2.2 h8).2 i hi) (Nat.le_max_left _ _))
        i hi)
    (by rw [hMs]; exact hCU)
  have hcat : ∀ k (hk : k < p), ∀ i < (cx[k]'hk).n.toNat, Column.idAt (Code.cat cx.toArray).b (Code.cat cx.toArray).w
      (((cx.toList.map (·.n.toNat)).take k).sum + i) = Column.idAt (cx[k]'hk).b (cx[k]'hk).w i := fun k hk i hi => by
    rw [← List.map_take]; exact catA.2.2 k hk i hi
  -- the count column, part by part
  generalize hcn : concatBytes ((cs.map fun c => (c.1, slicesOf c.2)).map (·.2.2)).toArray = cnts
  have hL : (((cs.map fun c => (c.1, slicesOf c.2)).map (·.2.2)).toArray.toList).map (·.size) =
      cs.toList.map fun c => 8 * c.1.toNat := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    have hk : k < p := by simpa using h2
    simp [(slicesOf_count (cs[k]'hk).2 (hp63 k hk)).1]
  have hT : len cnts = (cs.toList.map (·.1.toNat)).sum := by
    rw [← hcn, len, KernelWF.concatBytes_size, hL]
    have := sum_take_mul8 (fun c : Part (.arr b) => c.1.toNat) cs.toList cs.toList.length
    rw [List.take_of_length_le (Nat.le_refl _)] at this
    rw [this]; omega
  have hcr : ∀ k (hk : k < p), ∀ r < (cs[k]'hk).1.toNat,
      (Column.bitsAt cnts ((((cs.toList.map (·.1.toNat)).take k).sum + r) * 8) 8).toNat = cw k r := by
    intro k hk r hr
    have hk' : k < (((cs.map fun c => (c.1, slicesOf c.2)).map (·.2.2)).toArray.toList).length := by simpa using hk
    have h := concat_long_get _ hk' (i := r)
      (by simp [(slicesOf_count (cs[k]'hk).2 (hp63 k hk)).1]; omega)
    rw [List.map_take, hL, ← List.map_take, sum_take_mul8] at h
    rw [← hcn, concatBytes, ← Array.foldl_toList, ← List.map_take,
      show (((cs.toList.take k).map (·.1.toNat)).sum + r) * 8 = 8 * ((cs.toList.take k).map (·.1.toNat)).sum + 8 * r
        by omega, h]
    simp only [Array.getElem_toList, Vector.getElem_toArray, Vector.getElem_map]
    rw [Nat.mul_comm 8 r, (slicesOf_count _ (hp63 k hk)).2 r hr, hcw k hk]
  -- running totals of the counts, block by block
  have hB := sum_blocks (fun g => (Column.bitsAt cnts (g * 8) 8).toNat) (cs.toList.map (·.1.toNat))
    (cx.toList.map (·.n.toNat)) cw (by simp)
    (fun k hk => by
      have hk' : k < p := by simpa using hk
      simp only [List.getElem_map, Vector.getElem_toList]; exact hMk k hk')
    (fun k hk r hr => by
      have hk' : k < p := by simpa using hk
      simp only [List.getElem_map, Vector.getElem_toList] at hr
      exact hcr k hk' r hr)
  have hlast : (cs.toList.map (·.1.toNat)).sum = ((cs.toList.map (·.1.toNat)).take (p - 1)).sum +
      (cs[p - 1]'(by omega)).1.toNat := by
    have := sum_take_succ (cs.toList.map (·.1.toNat)) (p - 1) (by simp; omega)
    rw [show p - 1 + 1 = p by omega, List.take_of_length_le (by simp)] at this
    rw [this]; simp
  have hTot : ((List.range (len cnts)).map fun g => (Column.bitsAt cnts (g * 8) 8).toNat).sum =
      (cx.toList.map (·.n.toNat)).sum := by
    have := hB (p - 1) (by simp; omega) (cs[p - 1]'(by omega)).1.toNat (by simp)
    rw [hT, hlast, this, ← hMk (p - 1) (by omega)]
    have h2 := sum_take_succ (cx.toList.map (·.n.toNat)) (p - 1) (by simp; omega)
    rw [show p - 1 + 1 = p by omega, List.take_of_length_le (by simp)] at h2
    rw [h2]; simp
  have hTU : len cnts < USize.size := by rw [hT]; exact hN
  unfold longCount
  simp only [need, dif_pos hTU]
  have ht : (len cnts).toUSize.toNat = len cnts := USize.toNat_ofNat_of_lt' hTU
  simp only [sliceIds_eq]
  generalize hseq : Code.cat cx.toArray = seq at catA hcat
  -- `simp only`, not `generalize`: abstracting the offsets in the goal is not type correct
  obtain ⟨o, ho⟩ : ∃ o, concatBytes #[one 0, sums (len cnts).toUSize cnts] = o := ⟨_, rfl⟩
  simp only [ho]
  have hS63 : ((List.range (len cnts).toUSize.toNat).map fun i => (Column.bitsAt cnts (i * 8) 8).toNat).sum < 2 ^ 63 := by
    rw [ht, hTot, hMs]; exact hC
  have hO := offsets_get (len cnts).toUSize cnts (by rw [ht]; exact Nat.le_refl _) hS63
  rw [ho, ht] at hO
  rw [ht] at hS63
  have hoI : ∀ g ≤ len cnts, (Column.bitsAt o (8 * g) 8).toInt64.toInt =
      (((List.range g).map fun i => (Column.bitsAt cnts (i * 8) 8).toNat).sum : Int) := fun g hg => by
    rw [toInt64_toInt (by rw [hO.2 g hg]; exact Nat.lt_of_le_of_lt (sum_range_le _ hg) hS63), hO.2 g hg]
  have hoN : ∀ g ≤ len cnts, (Column.bitsAt o (8 * g) 8).toInt64.toInt.toNat =
      ((List.range g).map fun i => (Column.bitsAt cnts (i * 8) 8).toNat).sum := fun g hg => by
    rw [hoI g hg, Int.toNat_natCast]
  have hsw : seq.w.toUSize.toNat = seq.w := lane_toNat (by rcases catA.1.1 with h | h | h | h | h | h | h <;> omega)
  have hlast' : o.size / 8 - 1 = len cnts := by omega
  have hguard := And.intro (show seq.w.toUSize.toNat ≤ 64 by rw [hsw]; rcases catA.1.1 with h | h | h | h | h | h | h <;> omega)
    (And.intro (show 8 ≤ o.size by omega)
    (And.intro (show 0 ≤ (Column.bitsAt o 0 8).toInt64.toInt by have := hoI 0 (Nat.zero_le _); simp at this; omega)
    (And.intro (show (Column.bitsAt o (8 * (o.size / 8 - 1)) 8).toInt64.toInt ≤
      (Column.idsCap seq.b seq.w.toUSize.toNat (Column.bitsAt o (8 * (o.size / 8 - 1)) 8).toInt64.toInt.toNat : Int) by
        rw [hlast', hoN _ (Nat.le_refl _), hoI _ (Nat.le_refl _), hsw, hTot, ← catA.2.1,
          Column.idsCap_of_size catA.1.2.1]; exact Int.le_refl _)
    (show ∀ j, j < o.size / 8 - 1 →
      (Column.bitsAt o (8 * j) 8).toInt64.toInt ≤ (Column.bitsAt o (8 * (j + 1)) 8).toInt64.toInt by
        intro j hj; rw [hlast'] at hj; rw [hoI j (by omega), hoI (j + 1) (by omega), sum_range_succ']; omega))))
  obtain ⟨g1, g2, g3, g4, g5⟩ := hguard
  have hg : o.size / 8 - 1 ≤ 2 ^ 64 := by rw [hlast']; have := USize.size_le; omega
  have hidsz := KernelWF.rankSlices_size _ _ _ g1 g2 g3 g4 g5
  rw [hlast'] at hidsz
  have hNv : (cs.map (·.1)).foldl (fun s n => s + n.toNat) 0 = len cnts := by
    rw [hT]; unfold Vector.foldl; rw [← Array.foldl_toList, foldl_toNat_sum, Nat.zero_add]
    simp [Vector.toArray_map, List.map_map]; rfl
  simp only [hNv]
  obtain ⟨ids, hid⟩ : ∃ ids, Order.rankSlices seq.w.toUSize seq.b o = ids := ⟨_, rfl⟩
  simp only [hid] at hidsz ⊢
  have hidl : len ids = len cnts := by simp only [len] at hlast' hidsz ⊢; omega
  have hR := fun {j j'} (hj : j < len cnts) (hj' : j' < len cnts) =>
    hid ▸ rankSlices_get seq.w.toUSize seq.b o g1 g2 g3 g4 g5 hg (by rw [hlast']; exact hj) (by rw [hlast']; exact hj')
  have hP := pack_get (len cnts) ids (by rw [hidl]; exact hTU) (by rw [hidsz, hidl])
    (fun g hgl => by rw [hidl] at hgl; have := (hR hgl hgl).2; rw [Nat.mul_comm]; omega)
  have hPw : (pack (len cnts) ids).w = 1 ∨ (pack (len cnts) ids).w = 2 ∨ (pack (len cnts) ids).w = 4 ∨
      (pack (len cnts) ids).w = 8 ∨ (pack (len cnts) ids).w = 16 ∨ (pack (len cnts) ids).w = 32 ∨
      (pack (len cnts) ids).w = 64 := by rcases hP.1 with h | h | h | h <;> simp [h]
  have hs : ((cs.map (·.1)).toList.map (·.toNat)).sum = (pack (len cnts) ids).n.toNat := by
    rw [hP.2.1, hidl, hT, Vector.toList_map, List.map_map]; rfl
  have hOk : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.map (·.1.toNat)).take k).sum :=
    fun k => by rw [Vector.toList_map, List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < (cs[k]'hk).1.toNat, ((cs.toList.map (·.1.toNat)).take k).sum + i < len cnts :=
    fun k hk i hi => by
      have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
      simp only [List.getElem_map, Vector.getElem_toList] at this; omega
  refine ⟨⟨fun {k l} hk hl i j hi hj => ?_, fun {k} hk => ?_⟩, fun {k l} hk hl => ?_⟩
  · obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hPw hs hk
    obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hPw hs hl
    have hik := hlt k hk i hi
    have hjl := hlt l hl j hj
    rw [hwk, hwl, hck i (by rw [Vector.getElem_map]; exact hi), hcl j (by rw [Vector.getElem_map]; exact hj), hOk, hOk,
      hP.2.2.2.2 _ (by rw [hidl]; exact hik), hP.2.2.2.2 _ (by rw [hidl]; exact hjl), UInt64.toNat_inj,
      Nat.mul_comm _ 8, Nat.mul_comm _ 8, (hR hik hjl).1,
      hoN _ (by omega), hoN _ (by omega), hoN _ (by omega), hoN _ (by omega),
      Nat.add_assoc, Nat.add_assoc, hB k (by simpa using hk) i (by simp; omega),
      hB k (by simpa using hk) (i + 1) (by simp; omega), hB l (by simpa using hl) j (by simp; omega),
      hB l (by simpa using hl) (j + 1) (by simp; omega), sum_range_succ', sum_range_succ', Nat.add_sub_add_left,
      Nat.add_sub_add_left, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left, array_map_range_iff, arr_row, arr_row, list_map_range_iff]
    have hlk : cw k i = sH((cs[k]'hk).2, i, hi) - sL((cs[k]'hk).2, i, hi) := by
      rw [hcw k hk, dif_pos hi, List.length_map, List.length_range]
    have hll : cw l j = sH((cs[l]'hl).2, j, hj) - sL((cs[l]'hl).2, j, hj) := by
      rw [hcw l hl, dif_pos hj, List.length_map, List.length_range]
    rw [hlk, hll]
    refine and_congr_right fun hℓ => forall_congr' fun t => imp_congr_right fun ht => ?_
    have hmk : sL((cs[k]'hk).2, i, hi) + t < (cs[k]'hk).2.1.toNat := by
      have : sH((cs[k]'hk).2, i, hi) ≤ (cs[k]'hk).2.1.toNat := Nat.min_le_right _ _
      omega
    have hml : sL((cs[l]'hl).2, j, hj) + t < (cs[l]'hl).2.1.toNat := by
      have : sH((cs[l]'hl).2, j, hj) ≤ (cs[l]'hl).2.1.toNat := Nat.min_le_right _ _
      omega
    rw [dif_pos hmk, dif_pos hml, ← UInt64.toNat_inj]
    show Column.idAt seq.b seq.w.toUSize.toNat _ = Column.idAt seq.b seq.w.toUSize.toNat _ ↔ _
    have hck' : cS((cs[k]'hk).1, (cs[k]'hk).2, i) + t < (cx[k]'hk).n.toNat := by
      rw [hMk k hk, hcS k hk]
      have h1 := sum_range_le (fun t => (cG((cs[k]'hk).1, (cs[k]'hk).2, t)).length) (show i + 1 ≤ (cs[k]'hk).1.toNat by omega)
      rw [sum_range_succ'] at h1; dsimp only at h1
      rw [dif_pos hi, List.length_map, List.length_range] at h1; omega
    have hcl' : cS((cs[l]'hl).1, (cs[l]'hl).2, j) + t < (cx[l]'hl).n.toNat := by
      rw [hMk l hl, hcS l hl]
      have h1 := sum_range_le (fun t => (cG((cs[l]'hl).1, (cs[l]'hl).2, t)).length) (show j + 1 ≤ (cs[l]'hl).1.toNat by omega)
      rw [sum_range_succ'] at h1; dsimp only at h1
      rw [dif_pos hj, List.length_map, List.length_range] at h1; omega
    rw [hsw, hcS k hk, hcS l hl, Nat.add_assoc, Nat.add_assoc, hcat k hk _ hck', hcat l hl _ hcl']
    have ek := (hG k hk).2.2.2.2.2 i hi t (by omega)
    have el := (hG l hl).2.2.2.2.2 j hj t (by omega)
    rw [← hcxk k hk] at ek
    rw [← hcxk l hl] at el
    rw [hcxk k hk, hcxk l hl, (hG k hk).1, (hG l hl).1] at *
    rw [ek, el, hfe hk hl (by rw [hpe' k hk]; exact hmk) (by rw [hpe' l hl]; exact hml),
      row_part_congr (hpe' k hk) _ hmk, row_part_congr (hpe' l hl) _ hml]
  · obtain ⟨hwk, hnk, hck, -⟩ := cut_get _ (cs.map (·.1)) hPw hs hk
    have hzk := cut_size _ (cs.map (·.1)) hPw hs (by rw [hP.2.2.2.1, hP.2.1]) hk
    rw [hzk, hwk, hnk]
    refine ⟨hPw, by rw [Vector.getElem_map], rfl, fun h8 => absurd h8 (by rcases hP.1 with h | h | h | h <;> omega)⟩
  · rw [(cut_get _ (cs.map (·.1)) hPw hs hk).1, (cut_get _ (cs.map (·.1)) hPw hs hl).1]

#print axioms codes_arr_faithful_wf

end LeetQ.Rel.Alg
