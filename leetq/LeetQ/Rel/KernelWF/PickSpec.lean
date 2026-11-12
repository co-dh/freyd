/-
  What `pick` CONTAINS: row `k` of `x@i` is row `i[k]` of `x`, the index read unsigned, wherever that
  long is below `x`'s count. Stated over `Enc.get`, the reader `Arr.get` goes through.
-/
import LeetQ.Rel.Code

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify

/-- Belongs in qlean. `Enc.get` at a fixed-width type is `raw`'s element read through `atomOfBits`. -/
theorem get_eq_raw {t : QAtomicType} {w : Nat} (ht : denseWidth t = some w) {n : USize} {e : Enc}
    (hw : Enc.WF t n e) {j : Nat} (hj : j < n.toNat) :
    Enc.get t n e j = some (Column.atomOfBits t ((Enc.raw t n e).toList.getD j 0)
      (QAtomicType.ne_general_of_width (denseWidth_facts ht).2.1)) := by
  obtain ⟨-, hw', hb, hg, hs, -, -⟩ := denseWidth_facts ht
  cases e <;> cases t <;>
    simp_all [Enc.get, Enc.raw, Enc.WF, QAtomicType.width, denseWidth, List.getD_eq_getElem?_getD,
      foRBits_starts, alpBits_starts]

/-- Belongs in qlean. **`x@i` at a fixed-width type, read back**: element `k` of the answer is element
    `i[k]` of `x`, the index read unsigned, where that is below `x`'s count. -/
theorem gatherColumn_get_dense {t : QAtomicType} {w : Nat} (ht : denseWidth t = some w) {n : USize} {e : Enc}
    (hw : Enc.WF t n e) {m : USize} {i : ByteArray} (hm : m.toNat = i.size / 8) {e' : Enc}
    (h : gatherColumn t n e m (.bytes i) = some e') {k : Nat} (hk : k < m.toNat)
    (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get t m e' k = Enc.get t n e (Column.bitsAt i (k * 8) 8).toNat := by
  obtain ⟨-, hw', hb, hg, hs, hw0, hw8⟩ := denseWidth_facts ht
  have hwf' := gatherColumn_wf hw i hm h
  obtain ⟨src, ix, hsrc, hix, rfl⟩ := gatherColumn_fixed_shape ht n e m (.bytes i) _ hw h
  simp only [Enc.bytesOf, Option.some.injEq] at hix; subst hix
  have hwU : w.toUSize.toNat = w :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  rw [get_eq_raw ht hwf' hk, get_eq_raw ht hw hin]
  obtain ⟨-, hG⟩ := gatherBytes_spec w.toUSize (by omega) ((nullBits t).getD 0) src i
  rw [hwU] at hG
  have hS := elemsW_bytesOf hw' hb hg hw0 hw8 n e hw src hsrc
  have hR := size_raw n e hw hb hg hs (QAtomicType.ne_general_of_width hw')
  have hsz : src.size / w = n.toNat := by
    have := congrArg List.length hS; simp only [elemsW, List.length_map, List.length_range,
      Array.length_toList] at this; omega
  have hidx := congrArg (·.getD (Column.bitsAt i (k * 8) 8).toNat 0) hS
  simp only [elemsW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (hsz ▸ hin),
    Option.map_some, Option.getD_some] at hidx
  rw [raw_bytes t w hw' hb hg]
  simp only [Array.toList_map, Array.toList_range, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  rw [hG k (by omega), if_pos (by omega), hidx,
    List.getElem?_eq_getElem (by simp only [Array.length_toList, hR]; exact hin)]
  exact congrArg some (atomOfBits_mod hw' hb hg _)

/-- Belongs in qlean. **`x@i` at `boolean`, read back**: bit `k` of the answer is bit `i[k]` of `x`. -/
theorem gatherColumn_get_bits {n : USize} {e : Enc} (hw : Enc.WF .boolean n e) {m : USize} {i : ByteArray}
    (hm : m.toNat = i.size / 8) {e' : Enc} (h : gatherColumn .boolean n e m (.bytes i) = some e') {k : Nat}
    (hk : k < m.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get .boolean m e' k = Enc.get .boolean n e (Column.bitsAt i (k * 8) 8).toNat := by
  have hz : ¬ i.size < m.toNat * 8 := by omega
  cases e <;> try (exfalso; simp_all [Enc.WF, QAtomicType.width]; done)
  simp only [gatherColumn, denseWidth, foRColumn, Enc.bytesOf, hz, if_false, Option.map_some,
    Option.some.injEq] at h
  subst h
  simp only [Enc.get, if_pos hk, bitAt_gatherBits _ _ _ _ (hm ▸ hk), if_pos hin]

/-- `extract` of a range that ends where it starts, or before, is empty. -/
theorem extract_empty (b : ByteArray) {lo hi : Nat} (h : hi ≤ lo) : b.extract lo hi = b.extract lo lo := by
  apply ByteArray.ext; simp only [ByteArray.data_extract]
  rw [Array.extract_eq_empty_of_le (by omega), Array.extract_eq_empty_of_le (by omega)]

/-- A byte array's element is its data's. -/
theorem ba_get? (b : ByteArray) (i : Nat) : b[i]? = b.data[i]? := (Option.map_inj_right fun _ _ a => a).mp rfl

/-- Symbol `j`'s bytes as `symBytes` cuts them: its start to the NUL before the next start. -/
theorem extract_upto (b : ByteArray) (lo hi : Nat) :
    b.extract lo (lo + if hi > lo then hi - lo - 1 else 0) = b.extract lo (hi - 1) := by
  split
  · congr 1; omega
  · rw [Nat.add_zero, extract_empty b (show hi - 1 ≤ lo by omega)]

/-- Belongs in qlean. **`x@i` at a `symbol` blob, read back**: symbol `k` of the answer is symbol `i[k]`
    of `x`. -/
theorem gatherColumn_get_syms {n : USize} {blob : ByteArray} {offs : Array Nat}
    (hw : Enc.WF .symbol n (.syms blob offs)) {m : USize} {i : ByteArray}
    (hm : m.toNat = i.size / 8) {e' : Enc} (h : gatherColumn .symbol n (.syms blob offs) m (.bytes i) = some e')
    {k : Nat} (hk : k < m.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get .symbol m e' k = Enc.get .symbol n (.syms blob offs) (Column.bitsAt i (k * 8) 8).toNat := by
  have hz : ¬ i.size < m.toNat * 8 := by omega
  simp only [gatherColumn, denseWidth, foRColumn, Enc.bytesOf, hz, if_false, Option.map_some,
    Option.some.injEq] at h
  subst h
  obtain ⟨-, hJ⟩ := gatherSyms_spec blob offs i
  obtain ⟨lo, h1, h2, h3⟩ := hJ k (hm ▸ hk)
  simp only [Enc.WF] at hw
  have hg : gatherAt (offs.size - 1) i k = some (Column.bitsAt i (k * 8) 8).toNat := by
    simp only [gatherAt]; rw [if_pos (by omega)]
  simp only [hg] at h2 h3
  simp only [Enc.get, if_pos hk, if_pos hin, Column.symBytes, extract_upto]
  generalize blob.extract _ _ = K at h2 h3 ⊢
  have e1 : (gatherSyms blob offs i).2[k]! = lo := by simp [getElem!_def, h1]
  have e2 : (gatherSyms blob offs i).2[k + 1]! = lo + K.size + 1 := by simp [getElem!_def, h2]
  rw [e1, e2, Nat.add_sub_cancel]
  generalize (gatherSyms blob offs i).fst = G at h3
  simp only [ba_get?] at h3
  have hsz : K.size = 0 ∨ lo + K.size ≤ G.size := by
    rcases Nat.eq_zero_or_pos K.size with h | h
    · exact .inl h
    refine .inr (Nat.not_lt.1 fun hc => ?_)
    have := h3 (K.size - 1) (by omega)
    rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; omega),
      Array.getElem?_eq_getElem (by rw [ByteArray.size_data]; omega)] at this
    cases this
  suffices hK : G.extract lo (lo + K.size) = K by rw [hK]
  apply ByteArray.ext; apply Array.ext_getElem?; intro q
  rw [ByteArray.data_extract, Array.getElem?_extract, ByteArray.size_data]
  split
  · exact h3 q (by omega)
  · rw [Array.getElem?_eq_none (by rw [ByteArray.size_data]; omega)]

/-- `pushBits` appends: the bytes it writes do not depend on the payload before them. -/
theorem pushBits_append (a : ByteArray) (v : UInt64) (w : Nat) :
    Column.pushBits a v w = a ++ Column.pushBits .empty v w := by
  induction w with
  | zero => apply ByteArray.ext; simp [Column.pushBits]
  | succ w ih => apply ByteArray.ext; simp [Column.pushBits, ih, ByteArray.data_append, ByteArray.data_push]

/-- `pushBits` writes `w` bytes. -/
theorem size_pushBits (a : ByteArray) (v : UInt64) (w : Nat) : (Column.pushBits a v w).size = a.size + w := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [Column.pushBits, ← ByteArray.size_data, ByteArray.data_push, Array.size_push] at ih ⊢; omega

/-- A fold appending a chunk per element lists the chunks one after another. -/
theorem foldl_append_toList (C : Nat → ByteArray) (l : List Nat) (a : ByteArray) :
    (l.foldl (fun acc j => acc ++ C j) a).data.toList = a.data.toList ++ l.flatMap fun j => (C j).data.toList := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih => simp [ih, ByteArray.data_append, List.append_assoc]

/-- Chunks all of length `w`, laid one after another: element `q` of chunk `k` sits at `k·w + q`. -/
theorem flatMap_range_getElem? {α : Type} (D : Nat → List α) {w : Nat} (hD : ∀ j, (D j).length = w)
    {N k q : Nat} (hk : k < N) (hq : q < w) : ((List.range N).flatMap D)[k * w + q]? = (D k)[q]? := by
  have hl : ∀ N, ((List.range N).flatMap D).length = N * w := fun N => by
    induction N with
    | zero => simp
    | succ N ih => simp [List.range_succ, List.flatMap_append, hD, ih, Nat.succ_mul]
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases h : k < N
    · have : (k + 1) * w ≤ N * w := Nat.mul_le_mul_right _ h
      rw [List.getElem?_append_left (by rw [hl]; rw [Nat.succ_mul] at this; omega), ih h]
    · have e : k = N := by omega
      subst e
      rw [List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]

/-- Belongs in qlean. **`x@i` at `guid`, read back**: the sixteen bytes of element `k` of the answer are
    those of element `i[k]` of `x`. -/
theorem gatherColumn_get_guid {n : USize} {e : Enc} (hw : Enc.WF .guid n e) {m : USize} {i : ByteArray}
    (hm : m.toNat = i.size / 8) {e' : Enc} (h : gatherColumn .guid n e m (.bytes i) = some e') {k : Nat}
    (hk : k < m.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get .guid m e' k = Enc.get .guid n e (Column.bitsAt i (k * 8) 8).toNat := by
  have hz : ¬ i.size < m.toNat * 8 := by omega
  cases e <;> try (exfalso; simp_all [Enc.WF, QAtomicType.width]; done)
  rename_i b
  simp only [Enc.WF, QAtomicType.width] at hw
  simp only [gatherColumn, denseWidth, rowWidth, foRColumn, Enc.bytesOf, hz, if_false, Option.map_some,
    Option.some.injEq] at h
  subst h
  have h16 : (Nat.toUSize 16).toNat = 16 := toNat_small 16 (by decide)
  let C : Nat → ByteArray := fun j => match gatherAt (b.size / 16) i j with
    | some p => b.extract (p * 16) (p * 16 + 16)
    | none => Column.pushBits .empty ((nullBits .guid).getD 0) 16
  have hG : gatherBytes (Nat.toUSize 16) ((nullBits .guid).getD 0) b i =
      (List.range (i.size / 8)).foldl (fun acc j => acc ++ C j) .empty := by
    simp only [gatherBytes, h16]
    congr 1; funext acc j
    simp only [C]
    rcases gatherAt (b.size / 16) i j with _ | p <;> simp [pushBits_append acc]
  have hC : ∀ j, (C j).data.toList.length = 16 := fun j => by
    simp only [C, Array.length_toList, ByteArray.size_data]
    rcases hp : gatherAt (b.size / 16) i j with _ | p
    · simp [size_pushBits]
    · simp only [gatherAt] at hp
      split at hp
      · cases hp; simp only [ByteArray.size_extract]; omega
      · cases hp
  have hCk : C k = b.extract ((Column.bitsAt i (k * 8) 8).toNat * 16)
      ((Column.bitsAt i (k * 8) 8).toNat * 16 + 16) := by
    simp only [C, gatherAt]; rw [if_pos (by omega)]
  simp only [Enc.get, if_pos hk, if_pos hin]
  congr 2; apply Vector.ext; intro q hq
  simp only [Vector.getElem_ofFn, ba_get?, ← Array.getElem?_toList, hG, foldl_append_toList]
  rw [show (ByteArray.empty).data.toList = [] from rfl, List.nil_append,
    flatMap_range_getElem? _ hC (hm ▸ hk) hq, hCk, Array.getElem?_toList, ByteArray.data_extract,
    Array.getElem?_extract, ByteArray.size_data, if_pos (by omega), Array.getElem?_toList]

/-- A dictionary's id width grows with its size. -/
theorem idWidthOf_mono {a b : Nat} (h : a ≤ b) : Column.idWidthOf a ≤ Column.idWidthOf b := by
  have hw : Column.widthFor (a - 1) ≤ Column.widthFor (b - 1) := by
    unfold Column.widthFor
    split
    · exact Nat.zero_le _
    · rw [if_neg (by omega)]
      have hb : b - 1 < 2 ^ ((b - 1).log2 + 1) := (Nat.log2_lt (by omega)).1 (Nat.lt_succ_self _)
      have := (Nat.log2_lt (by omega : a - 1 ≠ 0)).2 (Nat.lt_of_le_of_lt (by omega) hb)
      omega
  unfold Column.idWidthOf Column.laneWidth
  repeat' split
  all_goals omega

/-- A byte array cut where it starts is empty. -/
theorem extract_self (b : ByteArray) (x : Nat) : b.extract x x = ByteArray.empty := by
  apply ByteArray.ext; simp [ByteArray.data_extract]

/-- The empty symbol appended to a dictionary ending at its blob leaves every entry reading as it did:
    the old entries lie inside the old blob, and an id past them reads empty either way. -/
theorem symKey_push {d : ByteArray} {o : Array Nat} (hl : o[o.size - 1]! = d.size)
    (hle : ∀ k < o.size, o[k]! ≤ d.size) (q : Nat) :
    Column.symKey (d.push 0) (o.push (d.size + 1)) q = Column.symKey d o q := by
  have hP : ∀ t, (o.push (d.size + 1))[t]! =
      if t < o.size then o[t]! else if t = o.size then d.size + 1 else 0 := by
    intro t
    split
    · rename_i h; rw [getElem!_pos _ t (by simp; omega), Array.getElem_push_lt h, getElem!_pos o t h]
    · split
      · rename_i h; subst h; rw [getElem!_pos _ o.size (by simp), Array.getElem_push_eq]
      · rw [getElem!_neg _ t (by simp; omega)]; rfl
  have hX : ∀ lo hi, hi ≤ d.size → (d.push 0).extract lo hi = d.extract lo hi := by
    intro lo hi hh
    apply ByteArray.ext; apply Array.ext_getElem?; intro r
    rw [ByteArray.data_extract, ByteArray.data_extract, Array.getElem?_extract, Array.getElem?_extract,
      ByteArray.data_push, Array.size_push, ByteArray.size_data]
    by_cases hr : r < min hi d.size - lo
    · rw [if_pos (by omega), if_pos hr, Array.getElem?_push_lt (by rw [ByteArray.size_data]; omega),
        Array.getElem?_eq_getElem (by rw [ByteArray.size_data]; omega)]
    · rw [if_neg (by omega), if_neg hr]
  unfold Column.symKey Column.symBytes
  dsimp only
  rw [extract_upto, extract_upto, hP q, hP (q + 1)]
  by_cases h1 : q + 1 < o.size
  · rw [if_pos (by omega : q < o.size), if_pos h1]
    exact hX _ _ (by have := hle (q + 1) h1; omega)
  · have hq : q < o.size → o[q]! = d.size := fun h => by rw [show q = o.size - 1 by omega]; exact hl
    have hle' : (if q + 1 = o.size then d.size + 1 else 0) - 1 ≤
        (if q < o.size then o[q]! else if q = o.size then d.size + 1 else 0) := by
      by_cases h2 : q < o.size
      · rw [if_pos (by omega), if_pos h2, hq h2]; omega
      · rw [if_neg (by omega), if_neg h2]; omega
    rw [if_neg h1, getElem!_neg o (q + 1) h1, extract_empty d (show (default : Nat) - 1 ≤ o[q]! from Nat.zero_le _),
      extract_empty (d.push 0) hle', extract_self, extract_self]

/-- Belongs in qlean. **`x@i` at an interned symbol column, read back**: symbol `k` of the answer is
    symbol `i[k]` of `x`, the empty symbol a miss would point at appended past every entry. -/
theorem gatherColumn_get_enum {n : USize} {d : ByteArray} {o : Array Nat} {ids : ByteArray}
    (hw : Enc.WF .symbol n (.enum d o ids)) {m : USize} {i : ByteArray} (hm : m.toNat = i.size / 8)
    {e' : Enc} (h : gatherColumn .symbol n (.enum d o ids) m (.bytes i) = some e') {k : Nat}
    (hk : k < m.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get .symbol m e' k = Enc.get .symbol n (.enum d o ids) (Column.bitsAt i (k * 8) 8).toNat := by
  have hz : ¬ i.size < m.toNat * 8 := by omega
  have hm0 : (m == 0) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; simp at hk
  simp only [gatherColumn, denseWidth, foRColumn, Enc.bytesOf, hz, if_false, hm0, Bool.false_eq_true,
    ↓reduceIte, Option.map_some, Option.some.injEq] at h
  subst h
  obtain ⟨-, hl, hle⟩ := hw
  have hg : gatherAt n.toNat i k = some (Column.bitsAt i (k * 8) 8).toNat := by
    simp only [gatherAt]; rw [if_pos (by omega)]
  generalize (Column.bitsAt i (k * 8) 8).toNat = j at hg hin
  have h64 : Column.idWidth o ≤ 64 := by
    rcases Verify.laneWidth_cases (Column.widthFor (o.size - 1 - 1)) with h | h | h | h | h | h | h | h <;>
      simp only [Column.idWidth, Column.idWidthOf, h] <;> decide
  have hread : ∀ (w' : Nat) (f : Nat → Nat), (w' = 0 ∨ w' = 1 ∨ w' = 2 ∨ w' = 4 ∨ w' = 8 ∨ w' = 16 ∨
      w' = 32 ∨ w' = 64) → 2 ^ Column.idWidth o ≤ 2 ^ w' → f k = Column.idAt ids (Column.idWidth o) j →
      Column.idAt (Column.packIds w' (i.size / 8) f) w' k = Column.idAt ids (Column.idWidth o) j := by
    intro w' f hw' h2 hf
    have := Verify.idAt_lt ids (Column.idWidth o) j h64
    rw [Verify.idAt_packIds hw' (by omega) (by rw [hf]; omega), hf]
  simp only [Enc.get, if_pos hk, if_pos hin, gatherIds, gatherPacked, Verify.idWidth_toNat]
  split
  · dsimp only
    rw [hread (Column.idWidth o) _ (Verify.laneWidth_cases _) (Nat.le_refl _) ?_]
    simp only [hg]
  · dsimp only
    have hpow : 2 ^ Column.idWidth o ≤ 2 ^ Column.idWidth (o.push (d.size + 1)) :=
      Nat.pow_le_pow_right (by decide) (idWidthOf_mono (by simp only [Array.size_push]; omega))
    rw [hread (Column.idWidth (o.push (d.size + 1))) _ (Verify.laneWidth_cases _) hpow ?_]
    · exact congrArg (fun b => some (QAtom.symbol ((String.fromUTF8? b).getD ""))) (symKey_push hl hle _)
    · simp only [hg]

/-- Belongs in qlean. **`x@i` read back** at every atom type but `general`: element `k` of the answer is
    element `i[k]` of `x`, where that is below `x`'s count. -/
theorem gatherColumn_get {t : QAtomicType} {n : USize} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general)
    {m : USize} {i : ByteArray} (hm : m.toNat = i.size / 8) {e' : Enc}
    (h : gatherColumn t n e m (.bytes i) = some e') {k : Nat} (hk : k < m.toNat)
    (hin : (Column.bitsAt i (k * 8) 8).toNat < n.toNat) :
    Enc.get t m e' k = Enc.get t n e (Column.bitsAt i (k * 8) 8).toNat := by
  cases hd : denseWidth t with
  | some w => exact gatherColumn_get_dense hd hw hm h hk hin
  | none =>
    by_cases hb : t = .boolean
    · subst hb; exact gatherColumn_get_bits hw hm h hk hin
    by_cases hgu : t = .guid
    · subst hgu; exact gatherColumn_get_guid hw hm h hk hin
    have hs : t = .symbol := by cases t <;> simp_all [denseWidth, QAtomicType.width]
    subst hs
    cases e with
    | syms b o => exact gatherColumn_get_syms hw hm h hk hin
    | enum d o ids => exact gatherColumn_get_enum hw hm h hk hin
    | _ => all_goals (exfalso; simp [Enc.WF, QAtomicType.width] at hw)

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel LeetQ.Rel

/-- A general list's element `j` is its `gen` column's. -/
theorem get_general {n : USize} (x : Arr .general n) {xs : Array QValue} (hc : x.enc = .gen xs)
    (j : Fin n.toNat) : x.get j = xs[j.1]'(by rw [Arr.gen_size x hc]; exact j.2) := by
  simp only [Arr.get]; split
  · rename_i ys hc'; rw [hc] at hc'; cases hc'; rfl
  · rename_i hn; exact (hn xs hc).elim

/-- `pick` at `general` is `genCol` of the picked elements. -/
theorem pick_general (c : (n : USize) × Arr .general n) (i : ByteArray) :
    pick .general c i = genCol ((longRows i).map fun p => (gens c.2)[p]?.getD default) := by
  simp [pick]

/-- **`pick` read back at `general`**: element `k` of `x@i` is element `i[k]` of `x`. -/
theorem pick_get_general (c : (n : USize) × Arr .general n) (i : ByteArray) (hl : len i < USize.size)
    (k : Nat) (hk : k < (pick .general c i).1.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < c.1.toNat) :
    (pick .general c i).2.get ⟨k, hk⟩ = c.2.get ⟨_, hin⟩ := by
  obtain ⟨xs, he, hs⟩ := KernelWF.general_cases c.2.wf
  have hgx : gens c.2 = xs := Option.some_inj.1 ((Option.some_get _).trans (by simp [he]))
  have hsz : ((longRows i).map fun p => (gens c.2)[p]?.getD default).size < USize.size := by
    simpa [longRows, len] using hl
  revert hk; rw [pick_general, genCol, need, dif_pos hsz]; intro hk
  rw [get_general _ rfl, get_general _ he]
  simp only [Array.getElem_map, longRows, Array.getElem_range, hgx, Nat.mul_comm 8 k]
  rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]

/-- **`pick` read back**: row `k` of `x@i` is row `i[k]` of `x`, the index read unsigned, where that is
    below `x`'s count. -/
theorem pick_get {t : QAtomicType} (c : (n : USize) × Arr t n) (i : ByteArray) (hl : len i < USize.size)
    (k : Nat) (hk : k < (pick t c i).1.toNat) (hin : (Column.bitsAt i (k * 8) 8).toNat < c.1.toNat) :
    (pick t c i).2.get ⟨k, hk⟩ = c.2.get ⟨_, hin⟩ := by
  by_cases hg : t = .general
  · subst hg; exact pick_get_general c i hl k hk hin
  obtain ⟨e, he, hp⟩ := pick_eq_gather hg c i hl
  have h1 : (pick t c i).1 = (len i).toUSize := by simpa [Arr.part] using congrArg Prod.fst hp
  have h2 : (pick t c i).2.enc = e := by simpa [Arr.part] using congrArg Prod.snd hp
  have hm : ((len i).toUSize).toNat = i.size / 8 := USize.toNat_ofNat_of_lt' hl
  rw [Arr.get_ne _ _ hg, Arr.get_ne _ _ hg, h2]
  simp only []
  rw [h1, KernelWF.gatherColumn_get c.2.wf hg hm he (h1 ▸ hk) hin]

/-- An `Arr` moved along a count equation keeps its elements. -/
theorem cast_get {t : QAtomicType} {a b : USize} (e : a = b) (x : Arr t a) (k : Fin b.toNat) :
    (e ▸ x : Arr t b).get k = x.get ⟨k, e ▸ k.2⟩ := by subst e; rfl

/-- **`pickArr` read back**: element `k` of the column picked at `i` is element `i[k]` of `x`, where that
    is below `x`'s count. -/
theorem pickArr_get {t : QAtomicType} (c : (n : USize) × Arr t n) (i : ByteArray) (m : USize)
    (h : len i = m.toNat) (k : Fin m.toNat)
    (hin : (Column.bitsAt i (k.1 * 8) 8).toNat < c.1.toNat) :
    (pickArr t c i m h).get k = c.2.get ⟨_, hin⟩ := by
  have hl : len i < USize.size := h ▸ m.toBitVec.isLt
  unfold pickArr; rw [cast_get]
  exact pick_get c i hl k.1 _ hin

end LeetQ.Rel.Alg

namespace LeetQ.Rel

open QLean LeetQ.Rel.Alg

/-- **`Vals.pickShared` read back**: row `k` of a side picked at `i` is row `i[k]` of the side, where that
    long is below its count — at every shape: an array's and a sum's payloads are shared whole and their
    `lo`/`hi`, tags and positions picked. -/
theorem Vals.pickShared_row (A : Obj) {n : USize} (x : Vals A n)
    (i : ByteArray) (m : USize) (h : len i = m.toNat) (k : Fin m.toNat)
    (hin : (Column.bitsAt i (k.1 * 8) 8).toNat < n.toNat) :
    (Vals.pickShared A x i m h).row k = x.row ⟨_, hin⟩ := by
  induction A generalizing n with
  | atom t => exact pickArr_get ⟨_, x⟩ i m h k hin
  | prod a b iha ihb =>
    exact Prod.ext (iha x.1 hin) (ihb x.2 hin)
  | arr _ _ =>
    obtain ⟨p, lo, hi, f⟩ := x
    show List.filterMap _ _ = List.filterMap _ _
    rw [pickArr_get _ i m h k hin, pickArr_get _ i m h k hin]
  | sum _ _ _ _ =>
    obtain ⟨l, r, tag, ix, y, z⟩ := x
    show (if _ then _ else _) = (if _ then _ else _)
    rw [pickArr_get _ i m h k hin, pickArr_get _ i m h k hin]

end LeetQ.Rel
