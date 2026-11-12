/-
  What the payloads `⊤`, `R × S`, `inl`, `inr`, `[R, S]` and `R + S` are built from CONTAIN, read off the
  kernels' Lean bodies: `tilLongs`/`tilCol` (element `k` is `k`), `cross` (position `k` is the pair
  `(k / m, k % m)`), `bitsOf` and `tags` (bit `i` is the tag of the part holding `i`), and `sumVals` (row `k`
  is `inl` of `X`'s row `k`, then `inr` of `Y`'s row `k - n`). The `2^63` bounds are where the kernels read a
  position as a signed long: past them `Int64.ofNat` wraps negative and the answers differ.
-/
import LeetQ.Rel.Alg
import QLean.Verify.Structural
import QLean.Verify.Chain
import QLean.Verify.Elementwise

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg

/-! ## `til` -/

private theorem lt64 {k : Nat} (n : USize) (hk : k < n.toNat) : k < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Nat.lt_trans hk n.toNat_lt_size) USize.size_le

/-- `tilLongs n`'s long `k` is `k`. -/
theorem tilLongs_bitsAt (n : USize) {k : Nat} (hk : k < n.toNat) :
    Column.bitsAt (tilLongs n) (k * 8) 8 = UInt64.ofNat k := by
  have h := congrArg (·[k]?) (Verify.tilLongs_spec n)
  have hs : (tilLongs n).size / 8 = n.toNat := len_tilLongs n
  simp only [Verify.elemsW, List.map_map, List.getElem?_map, List.getElem?_range, hs, hk] at h
  apply UInt64.toNat_inj.1
  simp only [Function.comp, Option.map_some, Option.some.injEq] at h
  rw [h, UInt64.toNat_ofNat_of_lt' (lt64 n hk)]

/-- `tilCol n`'s element `i` is `i`. -/
theorem tilCol_get (n : USize) (i : Fin n.toNat) : (tilCol n).get i = Int64.ofNat i.1 := by
  rw [Arr.get_long_bytes (tilCol n) rfl i, tilLongs_bitsAt n i.2]; rfl

/-- `tilCol n` as a list is `0, 1, …, n - 1`. -/
theorem tilCol_toList (n : USize) : (tilCol n).toList = (List.range n.toNat).map Int64.ofNat := by
  apply List.ext_getElem (by rw [LeetQ.Rel.Arr.length_toList, List.length_map, List.length_range])
  intro j h1 h2
  rw [Arr.getElem_toList, tilCol_get, List.getElem_map, List.getElem_range]

/-! ## `cross` -/

private theorem toNat_mul_fits {n m : USize} (h : n.toNat * m.toNat < USize.size) :
    (n * m).toNat = n.toNat * m.toNat := by
  rw [USize.toNat_mul]; exact Nat.mod_eq_of_lt h

private theorem m_toUInt64 (m : USize) : m.toUInt64 = UInt64.ofNat m.toNat :=
  UInt64.toNat_inj.1 (by rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le m.toNat_lt_size USize.size_le)]; simp)

private theorem ofNat_toInt {x : Nat} (hx : x < 2 ^ 63) : (UInt64.ofNat x).toInt64.toInt = x :=
  Int64.toInt_ofNat_of_lt hx

/-- `valStep` of a `div` or `mod` on two longs below `2^63`, the divisor positive: `Int.fdiv`/`Int.fmod` of
    naturals, which is `Nat`'s `/` and `%`. -/
private theorem valStep_divmod (x y : Nat) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hy0 : 0 < y) :
    Ew.valStep Ew.idiv Ew.i64 nul.toUInt64 (UInt64.ofNat x) (UInt64.ofNat y) = UInt64.ofNat (x / y) ∧
    Ew.valStep Ew.imod Ew.i64 nul.toUInt64 (UInt64.ofNat x) (UInt64.ofNat y) = UInt64.ofNat (x % y) := by
  have ex := ofNat_toInt hx; have ey := ofNat_toInt hy
  have hxn : (UInt64.ofNat x).toInt64 ≠ Int64.minValue := fun e => by
    rw [e] at ex; simp at ex
  have hyn : (UInt64.ofNat y).toInt64 ≠ Int64.minValue := fun e => by
    rw [e] at ey; simp at ey
  have hy0' : (UInt64.ofNat y).toInt64 ≠ 0 := fun e => by rw [e] at ey; simp at ey; omega
  have hnul : (nul.toUInt64).toInt64 = Int64.minValue := rfl
  have key : ∀ q : Nat, q < 2 ^ 63 → (Int64.ofInt (q : Int)).toUInt64 = UInt64.ofNat q := fun q hq => by
    have e : Int64.ofInt (q : Int) = Int64.ofNat q := Int64.toInt_inj.1 (by
      rw [Int64.toInt_ofInt, Int64.toInt_ofNat_of_lt hq]; simp only [Int.bmod, Int64.size]; split <;> omega)
    rw [e]; rfl
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.idiv, Ew.imod, hnul]
  simp only [↓reduceIte]
  refine ⟨?_, ?_⟩ <;> rw [if_neg (by simp; exact ⟨⟨hxn, hyn⟩, hy0'⟩)] <;> rw [ex, ey]
  · rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega), ← Int.natCast_ediv, key _ (by have := Nat.div_le_self x y; omega)]
  · rw [Int.fmod_eq_emod_of_nonneg _ (by omega), ← Int.natCast_emod, key _ (by have := Nat.mod_lt x hy0; omega)]

/-- `cross n m` at position `k < n·m` is the pair `(k / m, k % m)`: the first index column holds `k / m`, the
    second `k % m`, each `n·m` longs. `n·m` fits a `USize` and stays below `2^63`, where `til` reads as a
    nonnegative long. -/
theorem cross_elems {n m : USize} (hN : n.toNat * m.toNat < USize.size) (h : n.toNat * m.toNat < 2 ^ 63) :
    Verify.elemsW 8 (cross n m).1 = (List.range (n.toNat * m.toNat)).map (fun k => UInt64.ofNat (k / m.toNat)) ∧
    Verify.elemsW 8 (cross n m).2 = (List.range (n.toNat * m.toNat)).map (fun k => UInt64.ofNat (k % m.toNat)) := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have hs : ∀ k, Ew.shapeIdx Ew.va k = (k, 0) := fun k => by simp (config := {decide := true}) [Ew.shapeIdx]
  have hnm := toNat_mul_fits hN
  have ev := fun op => Verify.elemsW_val op Ew.i64 Ew.va nul (tilLongs (n * m)) (one m.toUInt64) (n * m)
  simp only [hw, hs, hnm] at ev
  simp only [cross, need, dif_pos hN]
  refine ⟨(ev _).trans ?_, (ev _).trans ?_⟩ <;> apply List.map_congr_left <;> intro k hk <;>
    rw [List.mem_range] at hk <;>
    have hm0 : 0 < m.toNat := Nat.pos_of_ne_zero (fun e => by rw [e, Nat.mul_zero] at hk; omega) <;>
    have hn0 : 0 < n.toNat := Nat.pos_of_ne_zero (fun e => by rw [e, Nat.zero_mul] at hk; omega) <;>
    have hm63 : m.toNat < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hn0) h <;>
    simp only [Ew.elem, hw, Nat.zero_mul, bitsAt_one, m_toUInt64,
      tilLongs_bitsAt (n * m) (show k < (n * m).toNat by rw [hnm]; exact hk)]
  · rw [(valStep_divmod k m.toNat (by omega) hm63 hm0).1]
    apply UInt64.toNat_inj.1; simp
  · rw [(valStep_divmod k m.toNat (by omega) hm63 hm0).2]
    apply UInt64.toNat_inj.1; simp

/-! ## `bitsOf`, `tags` -/

/-- `bitsOf x c`'s bit `r < c` is `x`; `c ≤ 2^63`, where `til c` reads as nonnegative longs. -/
theorem bitsOf_bitAt (x : Bool) (c : USize) {r : Nat} (hr : r < c.toNat) (hc : c.toNat ≤ 2 ^ 63) :
    Column.bitAt (bitsOf x c) r = x := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have hs : Ew.shapeIdx Ew.va r = (r, 0) := by simp (config := {decide := true}) [Ew.shapeIdx]
  have e : (UInt64.ofNat r).toInt64.toInt = r := ofNat_toInt (by omega)
  have hlt : ¬ (UInt64.ofNat r).toInt64 < 0 := by rw [Int64.lt_iff_toInt_lt, e]; simp
  unfold bitsOf
  rw [(Verify.cmp_bitAt _ _ _ _ _ c).2 r (by omega)]
  simp only [Ew.elem, hw, hs, Nat.zero_mul, bitsAt_one, tilLongs_bitsAt c hr, decide_eq_true hr, Bool.true_and]
  have hcmp : compare (UInt64.ofNat r).toInt64 (UInt64.toInt64 0) ≠ .lt := by
    show compareOfLessAndEq _ _ ≠ _; unfold compareOfLessAndEq; rw [if_neg (by exact hlt)]; split <;> simp
  cases x <;> simp (config := {decide := true}) only [Ew.cmpStep, Ew.signed, Ew.ge, Ew.lt, Ew.eq, Ew.ne, Ew.le,
    ↓reduceIte] <;> simpa using hcmp

/-- A `range`-indexed `flatMap` that reads the array `xs` at its index is the `flatMap` over `xs`. -/
private theorem flatMap_range {α β : Type} (xs : Array α) (f : Nat → List β) (G : α → List β)
    (h : ∀ k (hk : k < xs.size), f k = G xs[k]) : (List.range xs.size).flatMap f = xs.toList.flatMap G := by
  have e : (List.range xs.size).map f = xs.toList.map G :=
    List.ext_getElem (by simp) fun k h1 h2 => by
      rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList]
      exact h k (by simpa using h1)
  unfold List.flatMap; rw [e]

/-- `tags ps m`'s bit `i` is the tag of the part holding position `i`: the parts' tags, each repeated its
    count, laid one after another. Each count is at most `2^63`, where `bitsOf` reads `til` as nonnegative. -/
theorem tags_get (ps : Array (USize × Bool)) (m : USize) (h : ps.foldl (fun s p => s + p.1.toNat) 0 = m.toNat)
    (hc : ∀ p ∈ ps, p.1.toNat ≤ 2 ^ 63) (i : Fin m.toNat) :
    (tags ps m h).get i = (ps.toList.flatMap fun p => List.replicate p.1.toNat p.2).getD i.1 false := by
  rw [Arr.get_bool_bits (tags ps m h) rfl i]
  simp only [concatBits]
  have hK : min ((countBytes ((ps.map fun p => (p.1, bitsOf p.2 p.1)).map (·.1))).size / 8)
      ((ps.map fun p => (p.1, bitsOf p.2 p.1)).map (·.2)).size = ps.size := by
    rw [countBytes_size]; simp
  rw [hK]
  generalize hb : Array.flatMap _ (Array.range ps.size) = bs
  have hbs : bs.toList = ps.toList.flatMap fun p => List.replicate p.1.toNat p.2 := by
    rw [← hb]
    simp only [Array.toList_flatMap, Array.toList_range, Array.toList_map]
    refine flatMap_range ps _ _ fun k hk => ?_
    have hk' : k < ((ps.map fun p => (p.1, bitsOf p.2 p.1)).map (·.1)).size := by simpa using hk
    rw [countBytes_get _ k hk', getElem!_pos _ k (by simpa using hk)]
    simp only [Array.getElem_map, USize.toNat_toUInt64]
    have hc' := hc ps[k] (Array.getElem_mem hk)
    exact List.ext_getElem (by simp) fun r h1 _ => by
      rw [List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact bitsOf_bitAt _ _ (by simpa using h1) hc'
  have hlen : bs.size = m.toNat := by
    rw [← Array.length_toList, hbs, ← h, ← Array.foldl_toList, List.length_flatMap]
    suffices ∀ (l : List (USize × Bool)) (a : Nat),
        a + (l.map fun p => (List.replicate p.1.toNat p.2).length).sum = l.foldl (fun s p => s + p.1.toNat) a by
      simpa using this ps.toList 0
    intro l; induction l with
    | nil => simp
    | cons p l ih => intro a; simp only [List.map_cons, List.sum_cons, List.foldl_cons, ← ih]; simp; omega
  rw [Verify.bitAt_packOf _ _ _ (by rw [hlen]; exact i.2), ← Array.getElem?_toList, hbs, List.getD_eq_getElem?_getD]

end LeetQ.Rel.KernelWF
