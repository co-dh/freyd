/-
  The bit rules that read a matrix back as its set bits (`Bits.pairs`): `°` (`Bits.conv`) scatters them swapped,
  and the root (`Bits.table`) picks the elements at their codes. Both rest on `pairs_spec`: the pairs `(i, j)` are
  the set bits `i·w + j`, ascending, as `whereBits` lists them and `÷ w`, `mod w` split them.
-/
import LeetQ.Rel.Lang.BitsSpec
import LeetQ.Rel.KernelWF.CrossSpec
import LeetQ.Rel.RepSymDiv

namespace LeetQ.Rel.Lang.Bits

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {ρ : Val}

variable {A B : Obj}

/-- **`Ew.val` of a long column against one long**: where `op` with `c` maps each entry `t` of `p` to `f t`, the
    result's entries are `p`'s mapped by `f`. -/
theorem ids_val_va (op : UInt8) (p : ByteArray) (c : UInt64) (f : Nat → Nat) (hL : len p < USize.size)
    (hf : ∀ t ∈ ids p, (Ew.valStep op Ew.i64 nul.toUInt64 (UInt64.ofNat t) c).toNat = f t) :
    ids (Kernel.Ew.val op Ew.i64 Ew.va nul p (one c) (len p).toUSize) = (ids p).map f := by
  have hn : (len p).toUSize.toNat = len p := USize.toNat_ofNat_of_lt' hL
  have h8 : (Kernel.Ew.val op Ew.i64 Ew.va nul p (one c) (len p).toUSize).size / 8 = len p := by
    rw [KernelWF.Ew.val_size, hn]; show len p * 8 / 8 = _; omega
  have hl : (ids (Kernel.Ew.val op Ew.i64 Ew.va nul p (one c) (len p).toUSize)).length = (ids p).length := by
    rw [← len_eq_ids, ← len_eq_ids]; exact h8
  refine List.ext_getElem (by rw [hl, List.length_map]) fun k h1 _ => ?_
  have hk : k < (ids p).length := hl ▸ h1
  rw [ids_getElem h1, val_va_get _ _ _ _ (by rw [hn, len_eq_ids]; exact hk), bitsAt_one, List.getElem_map,
    ← hf _ (List.getElem_mem hk), ids_getElem hk, UInt64.ofNat_toNat]

/-- **`Bits.pairs`, read back**: the row codes are the set bits' positions `÷ w`, the column codes the same
    positions `mod w`, in `whereBits`' ascending order. -/
theorem pairs_ids (x : Bits) (hfit : x.na * x.w ≤ 2 ^ 27) :
    ids x.pairs.1 = ((List.range (x.na * x.w)).filter (Column.bitAt x.b)).map (· / x.w) ∧
    ids x.pairs.2 = ((List.range (x.na * x.w)).filter (Column.bitAt x.b)).map (· % x.w) := by
  have hN : (x.na * x.w).toUSize.toNat = x.na * x.w := toUSize_fit hfit
  obtain ⟨hw, -, hmem⟩ := whereBits_ids (x.na * x.w).toUSize x.b
  rw [hN] at hw hmem
  have hL : len (whereBits (x.na * x.w).toUSize x.b) < USize.size := by
    rw [len_eq_ids, hw]
    have := List.length_filter_le (Column.bitAt x.b) (List.range (x.na * x.w))
    rw [List.length_range] at this
    exact Nat.lt_of_le_of_lt (Nat.le_trans this hfit) (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  -- every listed position is below `na · w ≤ 2²⁷`, so `w` is positive and both are longs
  have hd : ∀ t ∈ ids (whereBits (x.na * x.w).toUSize x.b), 0 < x.w ∧ t < 2 ^ 63 ∧ x.w < 2 ^ 63 := fun t ht => by
    rw [hw, hmem] at ht
    have h0 : 0 < x.w := Nat.pos_of_ne_zero fun h => by simp [h] at ht
    have h1 : x.w ≤ x.na * x.w := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero fun h => by simp [h] at ht)
    exact ⟨h0, by omega, by omega⟩
  simp only [Bits.pairs]
  refine ⟨?_, ?_⟩
  · rw [ids_val_va _ _ _ (· / x.w) hL fun t ht => ?_, hw]
    obtain ⟨h0, h1, h2⟩ := hd t ht
    rw [show x.w.toUInt64 = UInt64.ofNat x.w from rfl, (KernelWF.valStep_divmod t x.w h1 h2 h0).1,
      UInt64.toNat_ofNat_of_lt' (by have := Nat.div_le_self t x.w; rw [UInt64.size]; omega)]
  · rw [ids_val_va _ _ _ (· % x.w) hL fun t ht => ?_, hw]
    obtain ⟨h0, h1, h2⟩ := hd t ht
    rw [show x.w.toUInt64 = UInt64.ofNat x.w from rfl, (KernelWF.valStep_divmod t x.w h1 h2 h0).2,
      UInt64.toNat_ofNat_of_lt' (by have := Nat.mod_lt t h0; rw [UInt64.size]; omega)]

/-- **The pairs are the set bits**: as many row codes as column codes, at most `na · w` of them, the row codes
    ascending and below `na`, the column codes below `w`, and bit `(i, j)` set iff some position holds `(i, j)`. -/
theorem pairs_spec (x : Bits) (hfit : x.na * x.w ≤ 2 ^ 27) :
    len x.pairs.2 = len x.pairs.1 ∧ len x.pairs.1 ≤ x.na * x.w ∧ (ids x.pairs.1).Pairwise (· ≤ ·) ∧
    (∀ t ∈ ids x.pairs.1, t < x.na) ∧ (∀ t ∈ ids x.pairs.2, t < x.w) ∧
    ∀ i < x.na, ∀ j < x.w, (x.at i j = true ↔
      ∃ (r : Nat) (h1 : r < (ids x.pairs.1).length) (h2 : r < (ids x.pairs.2).length),
        (ids x.pairs.1)[r]'h1 = i ∧ (ids x.pairs.2)[r]'h2 = j) := by
  obtain ⟨e1, e2⟩ := pairs_ids x hfit
  have hN : (x.na * x.w).toUSize.toNat = x.na * x.w := toUSize_fit hfit
  obtain ⟨-, hp, hmem⟩ := whereBits_ids (x.na * x.w).toUSize x.b
  rw [hN] at hp hmem
  simp only [len_eq_ids]
  generalize ids x.pairs.1 = l1 at e1 ⊢
  generalize ids x.pairs.2 = l2 at e2 ⊢
  subst e1 e2
  have hlen := List.length_filter_le (Column.bitAt x.b) (List.range (x.na * x.w))
  rw [List.length_range] at hlen
  generalize (List.range (x.na * x.w)).filter (Column.bitAt x.b) = L at hp hmem hlen ⊢
  have hlt : ∀ t ∈ L, t < x.na * x.w := fun t ht => ((hmem t).1 ht).1
  refine ⟨by simp, by simpa using hlen, ?_, ?_, ?_, ?_⟩
  · exact (hp.imp Nat.le_of_lt).map _ fun a b h => Nat.div_le_div_right h
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hlt s hs)
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by have := hlt s hs; simp [h] at this)
  · intro i hi j hj
    have hij := idx_lt hi hj
    have hw0 : 0 < x.w := by omega
    show Column.bitAt x.b (i * x.w + j) = true ↔ _
    rw [← (hmem _).trans (and_iff_right hij)]
    constructor
    · intro hm
      obtain ⟨r, hr, e⟩ := List.mem_iff_getElem.1 hm
      refine ⟨r, by simpa using hr, by simpa using hr, ?_, ?_⟩ <;> simp only [List.getElem_map, e]
      · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hj, Nat.zero_add]
      · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    · rintro ⟨r, h1, h2, e1, e2⟩
      simp only [List.getElem_map] at e1 e2
      have hr : r < L.length := by simpa using h1
      have := Nat.div_add_mod (L[r]) x.w
      rw [e1, e2] at this
      exact List.mem_iff_getElem.2 ⟨r, hr, by rw [← this, Nat.mul_comm]⟩

#print axioms pairs_spec

/-- `na · w ≤ 2²⁷` pairs count in a `USize`. -/
theorem pairs_len_lt (x : Bits) (hfit : x.na * x.w ≤ 2 ^ 27) : len x.pairs.1 < USize.size :=
  Nat.lt_of_le_of_lt ((pairs_spec x hfit).2.1)
    (Nat.lt_of_le_of_lt hfit (Nat.lt_of_lt_of_le (by decide) USize.le_size))

/-- **`°` as bits** (`rep_conv`'s side, `rep_tableC`): the pairs swapped and scattered hold the converse of `R`. -/
theorem rep_convB {ua : Nat → A.El} {ub : Nat → B.El} {d : Bool} {R : Tm A B d} {x : Bits} (hx : x.Enc ua ub (R.den ρ))
    (hfit : x.na * x.w ≤ 2 ^ 27) : x.conv.Enc ub ua fun b a => R.den ρ a b := by
  obtain ⟨hl, -, -, h1, h2, hat⟩ := pairs_spec x hfit
  intro b hb a ha
  change b < x.w at hb
  change a < x.na at ha
  show (Bits.ofCodes x.w x.na x.pairs.2 x.pairs.1).at b a = true ↔ R.den ρ (ua a) (ub b)
  rw [ofCodes_at hl.symm h2 h1 (by rw [Nat.mul_comm]; exact hfit) (hl ▸ pairs_len_lt x hfit) hb ha,
    ← hx a ha b hb, hat a ha b hb]
  exact ⟨fun ⟨r, h1, h2, e1, e2⟩ => ⟨r, h2, h1, e2, e1⟩, fun ⟨r, h1, h2, e1, e2⟩ => ⟨r, h2, h1, e2, e1⟩⟩

#print axioms rep_convB

/-- **The root read back** (`Bits.table`): where `x` holds `r` at the codes and `pa`, `pb` hold the elements
    `ua i`, `ub j` at rows `i`, `j`, the table holds `(a, b)` iff `r` relates some coded `a`, `b` — the pairs'
    codes picked (`pickPart_row`, `pick_row`) under `Vals.PickFits` at the codes the pairs name. -/
theorem rep_tableB {ua : Nat → A.El} {ub : Nat → B.El} {r : A.El → B.El → Prop} {x : Bits} (pa : Part A)
    (pb : Part B) (hx : x.Enc ua ub r) (hfit : x.na * x.w ≤ 2 ^ 27) (hna : x.na ≤ pa.1.toNat)
    (hw : x.w ≤ pb.1.toNat) (hua : ∀ i (h : i < pa.1.toNat), pa.2.row ⟨i, h⟩ = ua i)
    (hub : ∀ j (h : j < pb.1.toNat), pb.2.row ⟨j, h⟩ = ub j)
    (hPa : Vals.PickFits A pa.2 (ids x.pairs.1)) (hPb : Vals.PickFits B pb.2 (ids x.pairs.2)) (a : A.El)
    (b : B.El) :
    rep (x.table pa pb) a b ↔ ∃ i < x.na, ∃ j < x.w, r (ua i) (ub j) ∧ ua i = a ∧ ub j = b := by
  obtain ⟨hl, -, -, h1, h2, hat⟩ := pairs_spec x hfit
  obtain ⟨hk, hrow⟩ := pickPart_row pa.2 x.pairs.1 (pairs_len_lt x hfit)
    (fun t ht => Nat.lt_of_lt_of_le (h1 t ht) hna) hPa
  generalize hK : Vals.pickPart A pa.2 x.pairs.1 = K at hk hrow
  have hkj : K.1.toNat ≤ len x.pairs.2 := by rw [hk, hl]; exact Nat.le_refl _
  have hkj' : len x.pairs.2 = K.1.toNat := by rw [hk, hl]
  -- `pickN` at all of the column codes is `pick` at them
  have ht : x.table pa pb = ⟨K.1, K.2, Vals.pick B pb.2 x.pairs.2 K.1 hkj'⟩ := by
    show (if h : (Vals.pickPart A pa.2 x.pairs.1).1.toNat ≤ len x.pairs.2 then
      (⟨(Vals.pickPart A pa.2 x.pairs.1).1, (Vals.pickPart A pa.2 x.pairs.1).2,
        Vals.pickN B pb.2 x.pairs.2 (Vals.pickPart A pa.2 x.pairs.1).1 h⟩ : Rel A B) else zero) = _
    rw [hK, dif_pos hkj]
    have key : ∀ (i i' : ByteArray) (ei : i = i') h1 h2,
        Vals.pick B pb.2 i K.1 h1 = Vals.pick B pb.2 i' K.1 h2 := by intros; subst_vars; rfl
    exact congrArg (fun v => (⟨K.1, K.2, v⟩ : Rel A B))
      (key _ _ (by unfold fit; rw [if_pos hkj']) _ _)
  have hfitB : Vals.PickFits B pb.2
      ((List.range K.1.toNat).map fun q => (Column.bitsAt x.pairs.2 (q * 8) 8).toNat) := by
    rw [← hkj']; exact hPb
  have hl1 : (ids x.pairs.1).length = K.1.toNat := by rw [← len_eq_ids, hk]
  have hl2 : (ids x.pairs.2).length = K.1.toNat := by rw [← len_eq_ids, hkj']
  rw [ht, rep_apply]
  constructor
  · rintro ⟨q, e1, e2⟩
    obtain ⟨hq1, hti, er⟩ := hrow q.1 q.2
    have hq2 : q.1 < (ids x.pairs.2).length := by rw [hl2]; exact q.2
    have hj := h2 _ (List.getElem_mem hq2)
    have e2' := e2
    change (Vals.pick B pb.2 x.pairs.2 K.1 hkj').row q = b at e2'
    rw [pick_row B pb.2 x.pairs.2 K.1 hkj' hfitB q,
      dif_pos (by rw [← ids_getElem hq2]; exact Nat.lt_of_lt_of_le hj hw)] at e2'
    refine ⟨_, h1 _ (List.getElem_mem hq1), _, hj, ?_, ?_, ?_⟩
    · exact (hx _ (h1 _ (List.getElem_mem hq1)) _ hj).1 ((hat _ (h1 _ (List.getElem_mem hq1)) _ hj).2
        ⟨q.1, hq1, hq2, rfl, rfl⟩)
    · rw [← hua _ hti]; exact (er.symm.trans e1)
    · rw [← hub _ (Nat.lt_of_lt_of_le hj hw), ← e2']
      exact congrArg pb.2.row (Fin.ext (ids_getElem hq2))
  · rintro ⟨i, hi, j, hj, hr, rfl, rfl⟩
    obtain ⟨q, hq1, hq2, ei, ej⟩ := (hat i hi j hj).1 ((hx i hi j hj).2 hr)
    obtain ⟨hq1', hti, er⟩ := hrow q (hl1 ▸ hq1)
    refine ⟨⟨q, hl1 ▸ hq1⟩, ?_, ?_⟩
    · change K.2.row _ = _
      rw [er, hua, ei]
    · change (Vals.pick B pb.2 x.pairs.2 K.1 hkj').row _ = _
      rw [pick_row B pb.2 x.pairs.2 K.1 hkj' hfitB,
        dif_pos (by rw [← ids_getElem hq2, ej]; exact Nat.lt_of_lt_of_le hj hw)]
      rw [← hub j (Nat.lt_of_lt_of_le hj hw)]
      exact congrArg pb.2.row (Fin.ext (by simp only; rw [← ids_getElem hq2, ej]))

#print axioms rep_tableB

end LeetQ.Rel.Lang.Bits
