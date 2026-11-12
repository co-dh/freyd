/-
  `Obj.raze` of two parts read back at the constructors `RazeRow` leaves: a symbol atom's list (`razeTo2_symbol`),
  an array side (`raze_row_arr`), each taking the read-back of its components as a hypothesis.
-/
import LeetQ.Rel.KernelWF.RazeRow
import LeetQ.Rel.KernelWF.RazeSym

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- `raze_row_atom`'s `hA` at `symbol` (`razeTo_toList_symbol`); `hD`: the parts' dictionaries, a blob counting
    its rows, fit a `USize`. -/
theorem razeTo2_symbol {n m : USize} (x : Arr .symbol n) (y : Arr .symbol m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom .symbol))).toList.map
      fun c : Part (.atom .symbol) => c.1.toNat).sum < USize.size)
    (hD : ((#[⟨n, x⟩, ⟨m, y⟩] : Array ((k : USize) × Arr .symbol k)).toList.map
      fun c => match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat).sum < USize.size) :
    (razeTo .symbol #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  razeTo2_toList x y hN (razeTo_toList_symbol _ rfl hN hD)

/-- **`shiftArr` read back**: element `i` is its offset clamped into `[0, m]`, plus `k`, `m + k` below `2^63`. -/
theorem shiftArr_get {n : USize} (x : Arr .long n) {m k : Nat} (hmk : m + k < 2 ^ 63) (i : Fin n.toNat) :
    ((shiftArr x m k).get i).toInt = ((min (max (x.get i).toInt 0).toNat m + k : Nat) : Int) := by
  unfold shiftArr
  rw [Arr.get_long_bytes _ rfl]
  show (Column.bitsAt (Kernel.Ew.val Ew.add Ew.i64 Ew.va nul _ (one k.toUInt64) n) (i.1 * 8) 8).toInt64.toInt = _
  rw [val_va_get _ _ _ _ i.2, val_va_get _ _ _ _ i.2, val_va_get _ _ _ _ i.2, longsOf_get _ i.2, bitsAt_one,
    bitsAt_one, bitsAt_one]
  rw [show m.toUInt64 = UInt64.ofNat m from rfl, show (0 : UInt64) = UInt64.ofNat 0 from rfl,
    valStep_clamp _ (by omega), show k.toUInt64 = UInt64.ofNat k from rfl]
  generalize hc : min (max (x.get i).toUInt64.toInt64.toInt 0).toNat m = c
  have hcm : c ≤ m := hc ▸ Nat.min_le_right _ _
  have ec : (UInt64.ofNat c).toInt64.toInt = c := Int64.toInt_ofNat_of_lt (by omega)
  have ek : (UInt64.ofNat k).toInt64.toInt = k := Int64.toInt_ofNat_of_lt (by omega)
  rw [(valStep_int (by rw [ec]; omega) (by rw [ek]; omega)).1 (by rw [ec, ek]; omega) (by rw [ec, ek]; omega),
    ec, ek]
  rw [Int64.toInt64_toUInt64] at hc
  omega

/-- Two parts razed, `hT` its list the parts' lists one after another (`razeTo_toList_*`): element `q` is the
    first part's below its count, the second's past it. -/
theorem razeTo2_get {t : QAtomicType} {C : Array ((k : USize) × Arr t k)} {S : Nat}
    (hs : (C.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) {n m : USize} {u : Arr t n} {v : Arr t m}
    (hC : C = #[⟨n, u⟩, ⟨m, v⟩]) (hT : (razeTo t C hs hS).toList = C.toList.flatMap (·.2.toList)) (q : Nat)
    (hq : q < S.toUSize.toNat) :
    (razeTo t C hs hS).get ⟨q, hq⟩ =
      if h : q < n.toNat then u.get ⟨q, h⟩
      else v.get ⟨q - n.toNat, by
        subst hC; simp at hs; rw [USize.toNat_ofNat_of_lt' hS] at hq; omega⟩ := by
  subst hC
  have hl : (razeTo t _ hs hS).toList = u.toList ++ v.toList := by rw [hT]; simp
  have hq' : q < (razeTo t _ hs hS).toList.length := by rw [Arr.length_toList]; exact hq
  rw [← Arr.getElem_toList _ q hq']
  simp only [hl, List.getElem_append, Arr.length_toList, Arr.getElem_toList]

/-- `razeTo2_get` at two dense parts (`razeTo_toList_bytes`). -/
theorem razeTo2_get_bytes {t : QAtomicType} {C : Array ((k : USize) × Arr t k)} {S : Nat}
    (hs : (C.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) {n m : USize} {u : Arr t n} {v : Arr t m}
    (hC : C = #[⟨n, u⟩, ⟨m, v⟩]) (hu : ∃ b, u.enc = .bytes b) (hv : ∃ b, v.enc = .bytes b) (q : Nat)
    (hq : q < S.toUSize.toNat) :
    (razeTo t C hs hS).get ⟨q, hq⟩ =
      if h : q < n.toNat then u.get ⟨q, h⟩
      else v.get ⟨q - n.toNat, by
        subst hC; simp at hs; rw [USize.toNat_ofNat_of_lt' hS] at hq; omega⟩ :=
  razeTo2_get hs hS hC (razeTo_toList_bytes _ hs hS fun d hd => by
    subst hC
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact hu
    · exact hv) q hq

/-- Two dense parts `D = #[a, c]`, each a column `g k c` of the part `c` at its index `k`, razed: element `q` is
    the first part's below its count, the second's past it (`razeTo_toList_bytes`). -/
theorem razeTo2_mapIdx_get {t : QAtomicType} {α : USize → Type} (D : Array ((n : USize) × α n))
    (a c : (n : USize) × α n) (hD : D = #[a, c])
    (g : Nat → (d : (n : USize) × α n) → Arr t d.1) {S : Nat}
    (hs : ((D.mapIdx fun k d => (⟨d.1, g k d⟩ : (n : USize) × Arr t n)).toList.map (·.1.toNat)).sum = S)
    (hS : S < USize.size) (hg : ∀ k d, ∃ b, (g k d).enc = .bytes b) (q : Nat) (hq : q < S.toUSize.toNat) :
    (razeTo t (D.mapIdx fun k d => ⟨d.1, g k d⟩) hs hS).get ⟨q, hq⟩ =
      if h : q < a.1.toNat then (g 0 a).get ⟨q, h⟩
      else (g 1 c).get ⟨q - a.1.toNat, by
        have e : S = a.1.toNat + c.1.toNat := by rw [← hs, hD]; simp
        rw [USize.toNat_ofNat_of_lt' hS] at hq; omega⟩ := by
  exact razeTo2_get_bytes hs hS (by rw [hD]; simp) (hg 0 a) (hg 1 c) q hq

/-- **Row read-back of `raze` at an array side**: row `k` of two razed array parts is the first part's row below
    its count, the second's past it. `ihb`: the flat payloads' read-back; `hf`, `hP`: the payloads' counts summed
    fit a `USize` and stay below `2^63`, where a moved offset reads as its value. -/
theorem raze_row_arr {b : Obj} {n m : USize} (x : Vals (.arr b) n) (y : Vals (.arr b) m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.arr b))).toList.map fun c : Part (.arr b) => c.1.toNat).sum <
      USize.size)
    (hf : x.1.toNat + y.1.toNat < USize.size) (hP : x.1.toNat + y.1.toNat < 2 ^ 63)
    (ihb : ∀ hN' k hk, Vals.row (b.raze #[⟨x.1, x.2.2.2⟩, ⟨y.1, y.2.2.2⟩] hN') ⟨k, hk⟩ =
      if h : k < x.1.toNat then Vals.row x.2.2.2 ⟨k, h⟩
      else Vals.row y.2.2.2 ⟨k - x.1.toNat, by have := raze2_cnt x.2.2.2 y.2.2.2 hN'; omega⟩) (k : Nat)
    (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.arr b))).toList.map
      fun c : Part (.arr b) => c.1.toNat).sum.toUSize.toNat) :
    Vals.row ((Obj.arr b).raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x ⟨k, h⟩
      else Vals.row y ⟨k - n.toNat, by have := raze2_cnt x y hN; omega⟩ := by
  have hc := raze2_cnt x y hN
  have hf' : (((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.arr b))).map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.map
      (fun c : Part b => c.1.toNat)).sum < USize.size := by simpa using hf
  have hb : ((#[⟨x.1, x.2.2.2⟩, ⟨y.1, y.2.2.2⟩] : Array (Part b)).toList.map fun c : Part b => c.1.toNat).sum <
      USize.size := by simpa using hf
  have hbc := raze2_cnt x.2.2.2 y.2.2.2 hb
  generalize hR : (Obj.arr b).raze #[⟨n, x⟩, ⟨m, y⟩] hN = R
  -- the razed payload is the parts' payloads razed, read back by `ihb`
  have hab : R.1 = ((#[⟨x.1, x.2.2.2⟩, ⟨y.1, y.2.2.2⟩] : Array (Part b)).toList.map
      fun c : Part b => c.1.toNat).sum.toUSize := by
    subst hR; rw [Obj.raze.eq_3]; unfold need; rw [dif_pos hf']; first | rfl | simp
  have hR1 : R.1.toNat = x.1.toNat + y.1.toNat := by rw [hab, hbc]
  have hF : HEq R.2.2.2 (b.raze #[⟨x.1, x.2.2.2⟩, ⟨y.1, y.2.2.2⟩] hb) := by
    subst hR; rw [Obj.raze.eq_3]; unfold need; rw [dif_pos hf']; exact raze_heq (by simp) _ _
  have hrow : ∀ j (hj : j < R.1.toNat), Vals.row R.2.2.2 ⟨j, hj⟩ =
      if h : j < x.1.toNat then Vals.row x.2.2.2 ⟨j, h⟩ else Vals.row y.2.2.2 ⟨j - x.1.toNat, by omega⟩ :=
    fun j hj => (row_heq _ _ ⟨j, hj⟩ ⟨j, by rw [hbc]; omega⟩ hab hF rfl).trans (ihb hb j _)
  -- each row's offsets: its part's, clamped into that part's payload, moved past the payloads before it
  have hO : (∀ q (hq : q < _), (R.2.1.get ⟨q, hq⟩).toInt =
      if h : q < n.toNat then ((min (max (x.2.1.get ⟨q, h⟩).toInt 0).toNat x.1.toNat : Nat) : Int)
      else ((x.1.toNat + min (max (y.2.1.get ⟨q - n.toNat, by omega⟩).toInt 0).toNat y.1.toNat : Nat) : Int)) ∧
    (∀ q (hq : q < _), (R.2.2.1.get ⟨q, hq⟩).toInt =
      if h : q < n.toNat then ((min (max (x.2.2.1.get ⟨q, h⟩).toInt 0).toNat x.1.toNat : Nat) : Int)
      else ((x.1.toNat + min (max (y.2.2.1.get ⟨q - n.toNat, by omega⟩).toInt 0).toNat y.1.toNat : Nat) : Int)) := by
    subst hR; rw [Obj.raze.eq_3]; unfold need; rw [dif_pos hf']; dsimp only
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩ <;>
      rw [razeTo2_mapIdx_get _ _ _ rfl _ _ _ (fun _ _ => ⟨_, rfl⟩)] <;>
      split <;> rw [shiftArr_get] <;> simp <;> omega
  rw [arr_row R]
  by_cases hkn : k < n.toNat
  · rw [dif_pos hkn, arr_row x]
    have eL := hO.1 k hk; have eH := hO.2 k hk
    rw [dif_pos hkn] at eL eH
    rw [show min (max (R.2.1.get ⟨k, hk⟩).toInt 0).toNat R.1.toNat =
        min (max (x.2.1.get ⟨k, hkn⟩).toInt 0).toNat x.1.toNat by omega,
      show min (max (R.2.2.1.get ⟨k, hk⟩).toInt 0).toNat R.1.toNat =
        min (max (x.2.2.1.get ⟨k, hkn⟩).toInt 0).toNat x.1.toNat by omega]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hjx : min (max (x.2.1.get ⟨k, hkn⟩).toInt 0).toNat x.1.toNat + j < x.1.toNat := by omega
    rw [dif_pos (by omega), hrow, dif_pos hjx, dif_pos hjx]
  · have hkm : k - n.toNat < m.toNat := by omega
    rw [dif_neg hkn, arr_row y]
    have eL := hO.1 k hk; have eH := hO.2 k hk
    rw [dif_neg hkn] at eL eH
    rw [show min (max (R.2.1.get ⟨k, hk⟩).toInt 0).toNat R.1.toNat =
        x.1.toNat + min (max (y.2.1.get ⟨k - n.toNat, hkm⟩).toInt 0).toNat y.1.toNat by omega,
      show min (max (R.2.2.1.get ⟨k, hk⟩).toInt 0).toNat R.1.toNat =
        x.1.toNat + min (max (y.2.2.1.get ⟨k - n.toNat, hkm⟩).toInt 0).toNat y.1.toNat by omega,
      Nat.add_sub_add_left]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hjy : min (max (y.2.1.get ⟨k - n.toNat, hkm⟩).toInt 0).toNat y.1.toNat + j < y.1.toNat := by omega
    rw [dif_pos (by omega), hrow, dif_neg (by omega), dif_pos hjy]
    exact congrArg _ (Fin.ext (by dsimp only; omega))

/-- **`Vals.held` keeps every row**: where it compacts, `Vals.pick` at `til n` reads row `q` at `q` (`pick_row`). -/
theorem held_row {a b : Obj} {n : USize} (x : Vals (.sum a b) n)
    (hfit : Vals.PickFits (.sum a b) x (List.range n.toNat)) (q : Fin n.toNat) :
    Vals.row x.held q = Vals.row x q := by
  have e : (List.range n.toNat).map (fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat) = List.range n.toNat := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact tilLongs_get (by simpa using h2)
  unfold Vals.held; dsimp only
  split
  · show Vals.row (Vals.pick _ x (tilLongs n) n (len_tilLongs n)) q = _
    rw [pick_row _ x _ n _ (by rw [e]; exact hfit) q, dif_pos (by rw [tilLongs_get q.2]; exact q.2)]
    exact congrArg _ (Fin.ext (tilLongs_get q.2))
  · rfl

/-- The set bits of `tb` below `n`: a set bit `k` makes `whereBits` nonempty, a clear one `whereBits` of the
    complement. -/
theorem whereBits_pos (tb : ByteArray) {n : USize} {k : Nat} (hk : k < n.toNat) :
    (Column.bitAt tb k = true → 0 < len (whereBits n tb)) ∧
      (Column.bitAt tb k = false → 0 < len (whereBits n (Ew.notBits n tb))) := by
  obtain ⟨hs, -⟩ := Verify.whereBits_spec n tb
  obtain ⟨hs', -⟩ := Verify.whereBits_spec n (Ew.notBits n tb)
  constructor
  · intro h
    have := List.length_pos_of_mem (List.mem_filter.2 ⟨List.mem_range.2 hk, h⟩)
    simp only [len, hs]; omega
  · intro h
    have h' : Column.bitAt (Ew.notBits n tb) k = true := by rw [notBits_bitAt n tb hk, h]; rfl
    have := List.length_pos_of_mem (List.mem_filter.2 ⟨List.mem_range.2 hk, h'⟩)
    simp only [len, hs']; omega

/-- `whereBits` at `n` lists at most `n` positions. -/
theorem len_whereBits_le (tb : ByteArray) (n : USize) : len (whereBits n tb) ≤ n.toNat := by
  obtain ⟨hs, -⟩ := Verify.whereBits_spec n tb
  have := List.length_filter_le (Column.bitAt tb) (List.range n.toNat)
  simp only [List.length_range] at this
  simp only [len, hs]; omega

/-- **After `Vals.held` a row's side holds a value**: a row tagged `inr` has `0 < r`, one tagged `inl` `0 < l` —
    `x` itself where that already holds, else the compacted side, whose sides count their rows. -/
theorem held_side {a b : Obj} {n : USize} (x : Vals (.sum a b) n) (k : Fin n.toNat) :
    (x.held.2.2.1.get k = true → 0 < x.held.2.1.toNat) ∧ (x.held.2.2.1.get k = false → 0 < x.held.1.toNat) := by
  unfold Vals.held; dsimp only
  split
  · rename_i hC
    rw [if_pos hC]
    simp only [Vals.compact, Vals.pick, Vals.pickShared, need]
    split
    · rename_i hk
      rw [dif_pos hk]
      dsimp only
      rw [USize.toNat_ofNat_of_lt' hk.1, USize.toNat_ofNat_of_lt' hk.2, gather_len, gather_len,
        Arr.get_bool_bits _ (KernelWF.enc_tagBits _) k]
      exact whereBits_pos _ k.2
    · rename_i hk
      exact absurd ⟨by rw [gather_len]; exact Nat.lt_of_le_of_lt (len_whereBits_le _ n) n.toNat_lt_size,
        by rw [gather_len]; exact Nat.lt_of_le_of_lt (len_whereBits_le _ n) n.toNat_lt_size⟩ hk
  · rename_i hC
    rw [if_neg hC, Arr.get_bool_bits _ (KernelWF.enc_tagBits _) k]
    obtain ⟨h1, h2⟩ := whereBits_pos (tagBits x.2.2.1) k.2
    obtain ⟨hs, -⟩ := Verify.whereBits_spec n (tagBits x.2.2.1)
    have hR : len (whereBits n (tagBits x.2.2.1)) < n.toNat ∨ ∀ k', k' < n.toNat → Column.bitAt (tagBits x.2.2.1) k' = true := by
      rcases Nat.lt_or_ge (len (whereBits n (tagBits x.2.2.1))) n.toNat with h | h
      · exact Or.inl h
      · right; intro k' hk'
        have hl : ((List.range n.toNat).filter (Column.bitAt (tagBits x.2.2.1))).length = (List.range n.toNat).length := by
          have := List.length_filter_le (Column.bitAt (tagBits x.2.2.1)) (List.range n.toNat)
          simp only [len, hs] at h; simp only [List.length_range] at this ⊢; omega
        exact List.length_filter_eq_length_iff.1 hl k' (List.mem_range.2 hk')
    constructor
    · intro ht
      have := h1 ht
      refine Nat.pos_of_ne_zero fun h0 => ?_
      exact hC (Or.inr ⟨USize.toNat_inj.1 (by rw [USize.toNat_zero]; omega), this⟩)
    · intro ht
      refine Nat.pos_of_ne_zero fun h0 => ?_
      rcases hR with hR | hR
      · exact hC (Or.inl ⟨USize.toNat_inj.1 (by rw [USize.toNat_zero]; omega), hR⟩)
      · rw [hR k k.2] at ht; cases ht

/-- **`place` read back** with offsets: row `k`'s position clamped into its own side `[0, c - 1]`, plus `dr`
    where it is tagged `inr`, `dl` where `inl` — all below `2^63`. -/
theorem place_off_get {a b : Obj} {n : USize} (x : Vals (.sum a b) n) {dl dr : Nat}
    (hl : x.1.toNat + dl < 2 ^ 63) (hr : x.2.1.toNat + dr < 2 ^ 63) (k : Fin n.toNat) :
    ((place x ((x.1.toNat : Int) - 1) ((x.2.1.toNat : Int) - x.1.toNat) dl ((dr : Int) - dl)).get k).toInt =
      ((min (max (x.2.2.2.1.get k).toInt 0).toNat ((if x.2.2.1.get k then x.2.1.toNat else x.1.toNat) - 1) +
        (if x.2.2.1.get k then dr else dl) : Nat) : Int) := by
  obtain ⟨l, r, tag, idx, xa, xb⟩ := x
  dsimp only at hl hr ⊢
  unfold place
  rw [Arr.get_long_bytes _ rfl]
  dsimp only
  simp only [val_vv_get _ _ _ _ k.2, val_va_get _ _ _ _ k.2, widen_bits_get _ _ k.2, longsOf_get _ k.2,
    ← Arr.get_bool_bits _ (KernelWF.enc_tagBits tag) k]
  have e0 := int_bits_toInt ((l.toNat : Int) - 1) (by omega) (by omega)
  have e1 := int_bits_toInt ((r.toNat : Int) - l.toNat) (by omega) (by omega)
  have ez := int_bits_toInt 0 (by decide) (by decide)
  have eo0 := int_bits_toInt (dl : Int) (by omega) (by omega)
  have eo1 := int_bits_toInt ((dr : Int) - dl) (by omega) (by omega)
  have eI := congrArg Int64.toInt (Int64.toInt64_toUInt64 (idx.get k))
  generalize Column.bitsAt (int ((r.toNat : Int) - l.toNat)) 0 8 = K1 at e1 ⊢
  generalize Column.bitsAt (int ((l.toNat : Int) - 1)) 0 8 = K0 at e0 ⊢
  generalize Column.bitsAt (int ((dr : Int) - dl)) 0 8 = O1 at eo1 ⊢
  generalize Column.bitsAt (int (dl : Int)) 0 8 = O0 at eo0 ⊢
  generalize Column.bitsAt (int 0) 0 8 = Z at ez ⊢
  generalize (idx.get k).toUInt64 = I at eI ⊢
  generalize tag.get k = t
  have hT : -2 ^ 63 < (if t then (1 : UInt64) else 0).toInt64.toInt := by cases t <;> decide
  have m1 := (valStep_int (y := K1) hT (by omega)).2.2 t rfl
  rw [e1] at m1
  have l1 := (valStep_int (y := K0) (by rw [m1]; split <;> omega) (by omega)).1
    (by rw [m1]; split <;> omega) (by rw [m1]; split <;> omega)
  rw [m1, e0] at l1
  have mo := (valStep_int (y := O1) hT (by omega)).2.2 t rfl
  rw [eo1] at mo
  have ao := (valStep_int (y := O0) (by rw [mo]; split <;> omega) (by omega)).1
    (by rw [mo]; split <;> omega) (by rw [mo]; split <;> omega)
  rw [mo, eo0] at ao
  generalize Ew.valStep Ew.add Ew.i64 nul.toUInt64 (Ew.valStep Ew.mul Ew.i64 nul.toUInt64 (if t then 1 else 0) K1) K0
    = LIN at l1 ⊢
  generalize Ew.valStep Ew.add Ew.i64 nul.toUInt64 (Ew.valStep Ew.mul Ew.i64 nul.toUInt64 (if t then 1 else 0) O1) O0
    = OFF at ao ⊢
  have hles := (valStep_min_max I LIN).1
  generalize Ew.valStep Ew.lesser Ew.i64 nul.toUInt64 I LIN = LES at hles ⊢
  have hgre := (valStep_min_max LES Z).2
  generalize Ew.valStep Ew.greater Ew.i64 nul.toUInt64 LES Z = G at hgre ⊢
  rw [(valStep_int (x := G) (y := OFF) (by rw [hgre]; omega) (by rw [ao]; split <;> omega)).1
    (by rw [hgre, ao]; split <;> omega) (by rw [hgre, hles, ao, ez, l1]; split <;> omega), hgre, hles, ao, ez, l1, eI]
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A razed side `W` of the parts `w1`, `w2` (`hW`), read at `I` clamped, where `I` is the first part's position
    `J` clamped into it: the first part read at `J` clamped. -/
theorem side_read_fst {c : Obj} {L l1 l2 : USize} (W : Vals c L) (w1 : Vals c l1) (w2 : Vals c l2)
    (hL : L.toNat = l1.toNat + l2.toNat)
    (hW : ∀ j (hj : j < L.toNat), Vals.row W ⟨j, hj⟩ =
      if h : j < l1.toNat then Vals.row w1 ⟨j, h⟩ else Vals.row w2 ⟨j - l1.toNat, by omega⟩)
    {I J : Int64} (hI : I.toInt = ((min (max J.toInt 0).toNat (l1.toNat - 1) : Nat) : Int)) (h1 : 0 < l1.toNat) :
    (if h : 0 < L.toNat then Vals.row W (clampFin I L.toNat h) else c.dflt) =
      if h : 0 < l1.toNat then Vals.row w1 (clampFin J l1.toNat h) else c.dflt := by
  have hc : min (max J.toInt 0).toNat (l1.toNat - 1) < l1.toNat := by omega
  rw [dif_pos (by omega), dif_pos h1,
    show clampFin I L.toNat (by omega) = ⟨_, (by omega : min (max J.toInt 0).toNat (l1.toNat - 1) < L.toNat)⟩ from
      Fin.ext (by simp only [clampFin, hI]; omega),
    hW, dif_pos hc]
  rfl

/-- The same past the first part: `I` is the second part's position `J` clamped into it, moved past `l1`. -/
theorem side_read_snd {c : Obj} {L l1 l2 : USize} (W : Vals c L) (w1 : Vals c l1) (w2 : Vals c l2)
    (hL : L.toNat = l1.toNat + l2.toNat)
    (hW : ∀ j (hj : j < L.toNat), Vals.row W ⟨j, hj⟩ =
      if h : j < l1.toNat then Vals.row w1 ⟨j, h⟩ else Vals.row w2 ⟨j - l1.toNat, by omega⟩)
    {I J : Int64} (hI : I.toInt = ((l1.toNat + min (max J.toInt 0).toNat (l2.toNat - 1) : Nat) : Int))
    (h2 : 0 < l2.toNat) :
    (if h : 0 < L.toNat then Vals.row W (clampFin I L.toNat h) else c.dflt) =
      if h : 0 < l2.toNat then Vals.row w2 (clampFin J l2.toNat h) else c.dflt := by
  rw [dif_pos (by omega), dif_pos h2,
    show clampFin I L.toNat (by omega) =
      ⟨l1.toNat + min (max J.toInt 0).toNat (l2.toNat - 1), by omega⟩ from
      Fin.ext (by simp only [clampFin, hI]; omega),
    hW, dif_neg (by omega)]
  exact congrArg _ (Fin.ext (by simp only [clampFin]; omega))

/-- A sum row, read through the side's projections. -/
theorem row_sum_eq {a b : Obj} {n : USize} (X : Vals (.sum a b) n) (i : Fin n.toNat) :
    Vals.row X i = if X.2.2.1.get i then
        .inr (if h : 0 < X.2.1.toNat then Vals.row X.2.2.2.2.2 (clampFin (X.2.2.2.1.get i) X.2.1.toNat h) else b.dflt)
      else .inl (if h : 0 < X.1.toNat then Vals.row X.2.2.2.2.1 (clampFin (X.2.2.2.1.get i) X.1.toNat h) else a.dflt) := by
  obtain ⟨l, r, tag, idx, xa, xb⟩ := X; rfl

set_option maxHeartbeats 2000000 in
/-- **Row read-back of `raze` at a sum side**: row `k` of two razed sum parts is the first part's row below its
    count, the second's past it. Each part is `held` first (`held_row`, under `hfx`, `hfy`), so a row's side holds
    a value (`held_side`); the tags are razed, each side's payloads razed (`iha`, `ihb`), and each position moved
    past its side's values in the first part (`place_off_get`). `hl`, `hr`, `hl63`, `hr63`: each side's payload
    counts summed fit a `USize` and stay below `2^63`. -/
theorem raze_row_sum {a b : Obj} {n m : USize} (x : Vals (.sum a b) n) (y : Vals (.sum a b) m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.sum a b))).toList.map fun c : Part (.sum a b) => c.1.toNat).sum <
      USize.size)
    (hl : x.held.1.toNat + y.held.1.toNat < USize.size) (hr : x.held.2.1.toNat + y.held.2.1.toNat < USize.size)
    (hl63 : x.held.1.toNat + y.held.1.toNat < 2 ^ 63) (hr63 : x.held.2.1.toNat + y.held.2.1.toNat < 2 ^ 63)
    (hfx : Vals.PickFits (.sum a b) x (List.range n.toNat)) (hfy : Vals.PickFits (.sum a b) y (List.range m.toNat))
    (iha : ∀ hN' k hk, Vals.row (a.raze #[⟨x.held.1, x.held.2.2.2.2.1⟩, ⟨y.held.1, y.held.2.2.2.2.1⟩] hN') ⟨k, hk⟩ =
      if h : k < x.held.1.toNat then Vals.row x.held.2.2.2.2.1 ⟨k, h⟩
      else Vals.row y.held.2.2.2.2.1 ⟨k - x.held.1.toNat, by
        have := raze2_cnt x.held.2.2.2.2.1 y.held.2.2.2.2.1 hN'; omega⟩)
    (ihb : ∀ hN' k hk, Vals.row (b.raze #[⟨x.held.2.1, x.held.2.2.2.2.2⟩, ⟨y.held.2.1, y.held.2.2.2.2.2⟩] hN') ⟨k, hk⟩ =
      if h : k < x.held.2.1.toNat then Vals.row x.held.2.2.2.2.2 ⟨k, h⟩
      else Vals.row y.held.2.2.2.2.2 ⟨k - x.held.2.1.toNat, by
        have := raze2_cnt x.held.2.2.2.2.2 y.held.2.2.2.2.2 hN'; omega⟩) (k : Nat)
    (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.sum a b))).toList.map
      fun c : Part (.sum a b) => c.1.toNat).sum.toUSize.toNat) :
    Vals.row ((Obj.sum a b).raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x ⟨k, h⟩
      else Vals.row y ⟨k - n.toNat, by have := raze2_cnt x y hN; omega⟩ := by
  have hc := raze2_cnt x y hN
  have hfl : ((#[⟨x.held.1, x.held.2.2.2.2.1⟩, ⟨y.held.1, y.held.2.2.2.2.1⟩] : Array (Part a)).toList.map
      fun c : Part a => c.1.toNat).sum < USize.size := by simpa using hl
  have hfr : ((#[⟨x.held.2.1, x.held.2.2.2.2.2⟩, ⟨y.held.2.1, y.held.2.2.2.2.2⟩] : Array (Part b)).toList.map
      fun c : Part b => c.1.toNat).sum < USize.size := by simpa using hr
  have hcl := raze2_cnt _ _ hfl
  have hcr := raze2_cnt _ _ hfr
  have eb0 : ∀ f : Part (.sum a b) → Nat, ((Array.map f (Array.map (fun c : Part (.sum a b) =>
      (⟨c.1, c.2.held⟩ : Part (.sum a b))) #[⟨n, x⟩, ⟨m, y⟩])).extract 0 0).foldl (· + ·) 0 = 0 := fun f => by simp
  have eb1 : ∀ f : Part (.sum a b) → Nat, ((Array.map f (Array.map (fun c : Part (.sum a b) =>
      (⟨c.1, c.2.held⟩ : Part (.sum a b))) #[⟨n, x⟩, ⟨m, y⟩])).extract 0 1).foldl (· + ·) 0 = f ⟨n, x.held⟩ :=
    fun f => by simp
  generalize hR : (Obj.sum a b).raze #[⟨n, x⟩, ⟨m, y⟩] hN = R
  have hL : R.1 = ((#[⟨x.held.1, x.held.2.2.2.2.1⟩, ⟨y.held.1, y.held.2.2.2.2.1⟩] : Array (Part a)).toList.map
      fun c : Part a => c.1.toNat).sum.toUSize := by
    subst hR; rw [Obj.raze.eq_4]; unfold need; rw [dif_pos (by simpa using And.intro hl hr)]; first | rfl | simp
  have hRr : R.2.1 = ((#[⟨x.held.2.1, x.held.2.2.2.2.2⟩, ⟨y.held.2.1, y.held.2.2.2.2.2⟩] : Array (Part b)).toList.map
      fun c : Part b => c.1.toNat).sum.toUSize := by
    subst hR; rw [Obj.raze.eq_4]; unfold need; rw [dif_pos (by simpa using And.intro hl hr)]; first | rfl | simp
  have hXA : HEq R.2.2.2.2.1 (a.raze #[⟨x.held.1, x.held.2.2.2.2.1⟩, ⟨y.held.1, y.held.2.2.2.2.1⟩] hfl) := by
    subst hR; rw [Obj.raze.eq_4]; unfold need; rw [dif_pos (by simpa using And.intro hl hr)]
    exact raze_heq (by simp) _ _
  have hXB : HEq R.2.2.2.2.2 (b.raze #[⟨x.held.2.1, x.held.2.2.2.2.2⟩, ⟨y.held.2.1, y.held.2.2.2.2.2⟩] hfr) := by
    subst hR; rw [Obj.raze.eq_4]; unfold need; rw [dif_pos (by simpa using And.intro hl hr)]
    exact raze_heq (by simp) _ _
  have hTG : ∀ q (hq : q < _), R.2.2.1.get ⟨q, hq⟩ =
      if h : q < n.toNat then x.held.2.2.1.get ⟨q, h⟩ else y.held.2.2.1.get ⟨q - n.toNat, by omega⟩ := by
    subst hR; rw [Obj.raze.eq_4]; unfold need; rw [dif_pos (by simpa using And.intro hl hr)]; dsimp only
    intro q hq
    exact razeTo2_get (u := x.held.2.2.1) (v := y.held.2.2.1) _ _ (by simp) (razeTo_toList_boolean _ _ _) q hq
  have hIX : ∀ q (hq : q < _), (R.2.2.2.1.get ⟨q, hq⟩).toInt =
      if h : q < n.toNat then ((min (max (x.held.2.2.2.1.get ⟨q, h⟩).toInt 0).toNat
        ((if x.held.2.2.1.get ⟨q, h⟩ then x.held.2.1.toNat else x.held.1.toNat) - 1) : Nat) : Int)
      else ((min (max (y.held.2.2.2.1.get ⟨q - n.toNat, by omega⟩).toInt 0).toNat
        ((if y.held.2.2.1.get ⟨q - n.toNat, by omega⟩ then y.held.2.1.toNat else y.held.1.toNat) - 1) +
        (if y.held.2.2.1.get ⟨q - n.toNat, by omega⟩ then x.held.2.1.toNat else x.held.1.toNat) : Nat) : Int) := by
    subst hR; rw [Obj.raze.eq_4]; unfold need; rw [dif_pos (by simpa using And.intro hl hr)]; dsimp only
    intro q hq
    rw [razeTo2_mapIdx_get _ ⟨n, x.held⟩ ⟨m, y.held⟩ (by simp) _ _ _ (fun _ _ => ⟨_, rfl⟩)]
    dsimp only
    by_cases hq' : q < n.toNat
    · rw [dif_pos hq', dif_pos hq', place_off_get] <;> (try simp only [eb0, ite_self, Nat.add_zero]) <;>
        omega
    · rw [dif_neg hq', dif_neg hq', place_off_get] <;> (try simp only [eb1]) <;> omega
  have hL1 : R.1.toNat = x.held.1.toNat + y.held.1.toNat := by rw [hL, hcl]
  have hR1 : R.2.1.toNat = x.held.2.1.toNat + y.held.2.1.toNat := by rw [hRr, hcr]
  have hRA : ∀ j (hj : j < R.1.toNat), Vals.row R.2.2.2.2.1 ⟨j, hj⟩ =
      if h : j < x.held.1.toNat then Vals.row x.held.2.2.2.2.1 ⟨j, h⟩
      else Vals.row y.held.2.2.2.2.1 ⟨j - x.held.1.toNat, by omega⟩ :=
    fun j hj => (row_heq _ _ ⟨j, hj⟩ ⟨j, by rw [hcl]; omega⟩ hL hXA rfl).trans (iha hfl j _)
  have hRB : ∀ j (hj : j < R.2.1.toNat), Vals.row R.2.2.2.2.2 ⟨j, hj⟩ =
      if h : j < x.held.2.1.toNat then Vals.row x.held.2.2.2.2.2 ⟨j, h⟩
      else Vals.row y.held.2.2.2.2.2 ⟨j - x.held.2.1.toNat, by omega⟩ :=
    fun j hj => (row_heq _ _ ⟨j, hj⟩ ⟨j, by rw [hcr]; omega⟩ hRr hXB rfl).trans (ihb hfr j _)
  have hT := hTG k hk
  have hI := hIX k hk
  clear hXA hXB hL hRr hTG hIX hR iha ihb
  by_cases hkn : k < n.toNat
  · rw [dif_pos hkn, ← held_row x hfx]
    rw [dif_pos hkn] at hT hI
    have hs := held_side x ⟨k, hkn⟩
    rw [row_sum_eq R, row_sum_eq x.held, hT]
    cases ht : x.held.2.2.1.get ⟨k, hkn⟩
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hI ⊢
      exact congrArg Sum.inl (side_read_fst _ _ _ hL1 hRA hI (hs.2 ht))
    · simp only [ht, ↓reduceIte] at hI ⊢
      exact congrArg Sum.inr (side_read_fst _ _ _ hR1 hRB hI (hs.1 ht))
  · have hkm : k - n.toNat < m.toNat := by omega
    rw [dif_neg hkn, ← held_row y hfy]
    rw [dif_neg hkn] at hT hI
    have hs := held_side y ⟨k - n.toNat, hkm⟩
    rw [row_sum_eq R, row_sum_eq y.held, hT]
    cases ht : y.held.2.2.1.get ⟨k - n.toNat, hkm⟩
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hI ⊢
      exact congrArg Sum.inl (side_read_snd _ _ _ hL1 hRA (by rw [hI]; omega) (hs.2 ht))
    · simp only [ht, ↓reduceIte] at hI ⊢
      exact congrArg Sum.inr (side_read_snd _ _ _ hR1 hRB (by rw [hI]; omega) (hs.1 ht))

end LeetQ.Rel.KernelWF
