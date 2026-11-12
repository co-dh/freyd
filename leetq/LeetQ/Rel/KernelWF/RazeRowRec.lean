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

/-- Two dense parts razed: element `q` is the first part's below its count, the second's past it
    (`razeTo_toList_bytes`). -/
theorem razeTo2_get_bytes {t : QAtomicType} {C : Array ((k : USize) × Arr t k)} {S : Nat}
    (hs : (C.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) {n m : USize} {u : Arr t n} {v : Arr t m}
    (hC : C = #[⟨n, u⟩, ⟨m, v⟩]) (hu : ∃ b, u.enc = .bytes b) (hv : ∃ b, v.enc = .bytes b) (q : Nat)
    (hq : q < S.toUSize.toNat) :
    (razeTo t C hs hS).get ⟨q, hq⟩ =
      if h : q < n.toNat then u.get ⟨q, h⟩
      else v.get ⟨q - n.toNat, by
        subst hC; simp at hs; rw [USize.toNat_ofNat_of_lt' hS] at hq; omega⟩ := by
  subst hC
  have hl : (razeTo t _ hs hS).toList = u.toList ++ v.toList := by
    rw [razeTo_toList_bytes _ hs hS fun d hd => by
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact hu
      · exact hv]
    simp
  have hq' : q < (razeTo t _ hs hS).toList.length := by rw [Arr.length_toList]; exact hq
  rw [← Arr.getElem_toList _ q hq']
  simp only [hl, List.getElem_append, Arr.length_toList, Arr.getElem_toList]

/-- Two dense parts, each a column `g k c` of the part `c` at its index `k`, razed: element `q` is the first
    part's below its count, the second's past it (`razeTo_toList_bytes`). -/
theorem razeTo2_mapIdx_get {t : QAtomicType} {α : USize → Type} (a c : (n : USize) × α n)
    (g : Nat → (d : (n : USize) × α n) → Arr t d.1) {S : Nat}
    (hs : ((#[a, c].mapIdx fun k d => (⟨d.1, g k d⟩ : (n : USize) × Arr t n)).toList.map (·.1.toNat)).sum = S)
    (hS : S < USize.size) (hg : ∀ k d, ∃ b, (g k d).enc = .bytes b) (q : Nat) (hq : q < S.toUSize.toNat) :
    (razeTo t (#[a, c].mapIdx fun k d => ⟨d.1, g k d⟩) hs hS).get ⟨q, hq⟩ =
      if h : q < a.1.toNat then (g 0 a).get ⟨q, h⟩
      else (g 1 c).get ⟨q - a.1.toNat, by
        have e : S = a.1.toNat + c.1.toNat := by rw [← hs]; simp
        rw [USize.toNat_ofNat_of_lt' hS] at hq; omega⟩ := by
  exact razeTo2_get_bytes hs hS (by simp) (hg 0 a) (hg 1 c) q hq

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
      rw [razeTo2_mapIdx_get _ _ _ _ _ (fun _ _ => ⟨_, rfl⟩)] <;>
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

end LeetQ.Rel.KernelWF
