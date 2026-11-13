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
    rw [← hE] at hp ⊢
    rw [hp, hn]
    have : sH(x, r, hr) ≤ x.1.toNat := Nat.min_le_right _ _
    omega
  have hcb : 8 ≤ e.w → 8 * e.b.size = e.w * e.n.toNat := fun h8 => by
    rw [hs]; rcases hw with h | h | h | h | h | h | h <;> rw [h] at h8 ⊢ <;> omega
  obtain ⟨g1, g2, g3, g4⟩ := gather_spec e _ (by rw [hlenP]; exact hU) hw hcb hin
  have gs := gather_size e _ (by rw [hlenP]; exact hU) hw
  refine ⟨g1, by rw [g2, hlenP, hM], g3, by rw [gs, g2, g1], fun r hr j hj => ?_⟩
  have hq := flatMap_get_at (fun t => cG(n, x, t)) (m := n.toNat) hr (q := j)
    (by rw [dif_pos hr, List.length_map, List.length_range]; exact hj)
  rw [← hL, dif_pos hr, List.getElem?_map, List.getElem?_range hj, Option.map_some] at hq
  have hz : cS(n, x, r) + j < len E := by
    have h1 := sum_range_le (fun t => (cG(n, x, t)).length) (show r + 1 ≤ n.toNat by omega)
    rw [sum_range_succ', dif_pos hr, List.length_map, List.length_range] at h1
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
              exact ⟨Or.inl rfl, hn, rfl, by rw [hn]; exact s, f⟩
  split
  · next h => obtain ⟨s, f⟩ := lane 2 (by decide) h
              exact ⟨Or.inr (Or.inl rfl), hn, rfl, by rw [hn]; exact s, f⟩
  split
  · next h => obtain ⟨s, f⟩ := lane 4 (by decide) h
              exact ⟨Or.inr (Or.inr (Or.inl rfl)), hn, rfl, by rw [hn]; exact s, f⟩
  refine ⟨Or.inr (Or.inr (Or.inr rfl)), hn, rfl, by rw [hn, hsz]; show _ = (_ * 64 + 7) / 8; omega, fun g hg => ?_⟩
  show Column.idAt gid (8 * 8) g = _
  rw [idAt_lane _ (by decide)]

#print axioms pack_get

end LeetQ.Rel.Alg
