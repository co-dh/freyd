/-
  What `Vals.pick` at an array side reads its rows' slices with, read back: `slices` clamps each row's
  `[lo, hi)` into the payload `[0, p]` as `Vals.row` does (`Ew.val` lesser, greater, sub), `p` below `2^63`
  where a long reads as its own value.
-/
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.CrossSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-- `Ew.val` on longs at `va`, element `i` below the count: `valStep` of `a`'s long `i` and `b`'s first. -/
theorem val_va_get (op : UInt8) (a b : ByteArray) (n : USize) {i : Nat} (hi : i < n.toNat) :
    Column.bitsAt (Kernel.Ew.val op Ew.i64 Ew.va nul a b n) (i * 8) 8 =
      Ew.valStep op Ew.i64 nul.toUInt64 (Column.bitsAt a (i * 8) 8) (Column.bitsAt b 0 8) := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have h := congrArg (·[i]?) (elemsW_val op Ew.i64 Ew.va nul a b n)
  have hs : (Kernel.Ew.val op Ew.i64 Ew.va nul a b n).size / 8 = n.toNat := by
    have := len_val op Ew.va a b n; simpa [len] using this
  simp only [elemsW, hw, hs, List.getElem?_map, List.getElem?_range, hi, Option.map_some,
    Option.some.injEq] at h
  rw [h]
  simp (config := {decide := true}) only [Ew.shapeIdx, Ew.elem, hw, ↓reduceIte, Nat.zero_mul]
  generalize Ew.valStep op Ew.i64 nul.toUInt64 _ _ = v
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ (8 * 8) from v.toNat_lt), UInt64.ofNat_toNat]

/-- An `Int64` of value `q`, `0 ≤ q < 2^63`, is the long `q`. -/
theorem toUInt64_of_toInt {z : Int64} {q : Nat} (hq : q < 2 ^ 63) (h : z.toInt = q) :
    z.toUInt64 = UInt64.ofNat q := by
  rw [int64_eq_ofNat hq h]; rfl

/-- `valStep` lesser then greater, the long `x` clamped into `[0, p]`, `p` below `2^63`: the signed
    value of `x` clamped, as `Vals.row` clamps `lo` and `hi`. -/
theorem valStep_clamp (x : UInt64) {p : Nat} (hp : p < 2 ^ 63) :
    Ew.valStep Ew.greater Ew.i64 nul.toUInt64 (Ew.valStep Ew.lesser Ew.i64 nul.toUInt64 x (UInt64.ofNat p))
      (UInt64.ofNat 0) = UInt64.ofNat (min (max x.toInt64.toInt 0).toNat p) := by
  have ep : (UInt64.ofNat p).toInt64.toInt = p := Int64.toInt_ofNat_of_lt hp
  have e0 : (UInt64.ofNat 0).toInt64.toInt = 0 := rfl
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.lesser, Ew.greater]
  simp only [↓reduceIte]
  apply toUInt64_of_toInt (by omega)
  simp only [Int64.toInt64_toUInt64]
  split <;> split <;> simp_all [Int64.lt_iff_toInt_lt] <;> omega

/-- `valStep` greater on two longs below `2^63` is their maximum. -/
theorem valStep_max {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Ew.valStep Ew.greater Ew.i64 nul.toUInt64 (UInt64.ofNat a) (UInt64.ofNat b) = UInt64.ofNat (max a b) := by
  have ea : (UInt64.ofNat a).toInt64.toInt = a := Int64.toInt_ofNat_of_lt ha
  have eb : (UInt64.ofNat b).toInt64.toInt = b := Int64.toInt_ofNat_of_lt hb
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.greater]
  simp only [↓reduceIte]
  apply toUInt64_of_toInt (by omega)
  split <;> simp_all [Int64.lt_iff_toInt_lt] <;> omega

/-- `p` as the long `UInt64.ofNat p`. -/
theorem usize_toUInt64 (p : USize) : p.toUInt64 = UInt64.ofNat p.toNat :=
  UInt64.toNat_inj.1 (by rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le p.toNat_lt_size USize.size_le)]; simp)

/-- **`slices` read back**: row `k`'s start is its `lo` clamped into `[0, p]`, its count its `hi` clamped
    there less that start, or `0` where the clamped `hi` is below it — the positions `Vals.row` reads. -/
theorem slices_get {p n : USize} (hp : p.toNat < 2 ^ 63) (lo hi : ByteArray) {k : Nat} (hk : k < n.toNat) :
    Column.bitsAt (slices p n lo hi).1 (k * 8) 8 =
        UInt64.ofNat (min (max (Column.bitsAt lo (k * 8) 8).toInt64.toInt 0).toNat p.toNat) ∧
      Column.bitsAt (slices p n lo hi).2 (k * 8) 8 =
        UInt64.ofNat (min (max (Column.bitsAt hi (k * 8) 8).toInt64.toInt 0).toNat p.toNat -
          min (max (Column.bitsAt lo (k * 8) 8).toInt64.toInt 0).toNat p.toNat) := by
  have hc : ∀ b : ByteArray, Column.bitsAt (Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul
      (Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul b (one p.toUInt64) n) (one 0) n) (k * 8) 8 =
      UInt64.ofNat (min (max (Column.bitsAt b (k * 8) 8).toInt64.toInt 0).toNat p.toNat) := fun b => by
    rw [val_va_get _ _ _ _ hk, val_va_get _ _ _ _ hk, bitsAt_one, bitsAt_one, usize_toUInt64]
    exact valStep_clamp _ hp
  refine ⟨hc lo, ?_⟩
  generalize hL : min (max (Column.bitsAt lo (k * 8) 8).toInt64.toInt 0).toNat p.toNat = L
  generalize hH : min (max (Column.bitsAt hi (k * 8) 8).toInt64.toInt 0).toNat p.toNat = H
  have hL' : L ≤ p.toNat := hL ▸ Nat.min_le_right _ _
  have hH' : H ≤ p.toNat := hH ▸ Nat.min_le_right _ _
  have tn : ∀ q, q < 2 ^ 63 → (UInt64.ofNat q).toNat = q := fun q hq =>
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hq (by decide))
  have hM : Column.bitsAt (Kernel.Ew.val Ew.greater Ew.i64 Ew.vv nul
      (Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul
        (Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul hi (one p.toUInt64) n) (one 0) n)
      (Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul
        (Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul lo (one p.toUInt64) n) (one 0) n) n) (k * 8) 8 =
      UInt64.ofNat (max H L) := by
    rw [val_vv_get _ _ _ _ hk, hc, hc, hL, hH]; exact valStep_max (by omega) (by omega)
  simp only [slices]
  apply UInt64.toNat_inj.1
  rw [sub_get hk (by rw [hM, tn _ (by omega)]; omega) (by rw [hM, hc, hL, tn _ (by omega), tn _ (by omega)]; omega),
    hM, hc, hL, tn _ (by omega), tn _ (by omega), tn _ (by omega)]
  omega

/-- **The window `Vals.row` reads at an array row**: the positions `j < m` with `a ≤ j < b` are the run
    from `a` clamped into `[0, m]` to `b` clamped there, read in order; `d` answers no position of it. -/
theorem filterMap_window {β : Type} (d : β) : ∀ {m : Nat} (f : Fin m → β) (a b : Int),
    (List.finRange m).filterMap (fun j => if a ≤ (j.1 : Int) ∧ (j.1 : Int) < b then some (f j) else none) =
      (List.range' (min (max a 0).toNat m) (min (max b 0).toNat m - min (max a 0).toNat m)).map
        fun r => if h : r < m then f ⟨r, h⟩ else d
  | 0, f, a, b => by simp
  | m + 1, f, a, b => by
    rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map]
    have ih := filterMap_window d (fun j : Fin m => f j.castSucc) a b
    simp only [Function.comp_def, Fin.coe_castSucc] at ih ⊢
    rw [ih]
    have hm : ∀ r ∈ List.range' (min (max a 0).toNat m) (min (max b 0).toNat m - min (max a 0).toNat m),
        (if h : r < m then f (Fin.castSucc ⟨r, h⟩) else d) = (if h : r < m + 1 then f ⟨r, h⟩ else d) := by
      intro r hr; rw [List.mem_range'_1] at hr
      rw [dif_pos (by omega), dif_pos (by omega)]; rfl
    rw [List.map_congr_left hm]
    simp only [List.filterMap_cons, List.filterMap_nil, Fin.val_last]
    by_cases hw : a ≤ (m : Int) ∧ (m : Int) < b
    · rw [if_pos hw]; dsimp only
      have e1 : min (max a 0).toNat (m + 1) = min (max a 0).toNat m := by omega
      have e2 : min (max b 0).toNat (m + 1) - min (max a 0).toNat m =
          (min (max b 0).toNat m - min (max a 0).toNat m) + 1 := by omega
      rw [e1, e2, List.range'_concat, List.map_append]
      simp only [List.map_cons, List.map_nil, Nat.one_mul]
      rw [dif_pos (by omega)]
      congr 3; ext; simp only [Fin.val_last]; omega
    · rw [if_neg hw, List.append_nil]
      have e : (min (max b 0).toNat m - min (max a 0).toNat m = 0 ∧
            min (max b 0).toNat (m + 1) - min (max a 0).toNat (m + 1) = 0) ∨
          (min (max a 0).toNat (m + 1) = min (max a 0).toNat m ∧
            min (max b 0).toNat (m + 1) - min (max a 0).toNat m =
              min (max b 0).toNat m - min (max a 0).toNat m) := by omega
      rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; simp
      · rw [e1, e2]

end LeetQ.Rel.Alg
