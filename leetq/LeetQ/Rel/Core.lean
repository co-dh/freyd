/-
  The RelRep core: a relation is a key and a value column of one length `n` over the positions
  `0 … n-1`, `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y` — a tabulation, `key° ≫ val = R`.
  Columns are qlean's `Column`s in whatever encoding carries them; an element is read through
  `Column.get` (qlean's one-element reader over `bitsAt`/`bitAt`/`foRBits`/`symBytes`), never
  `Column.atoms`. Lists exist in proofs only (`toList`).
-/
import QLean.Value
import QLean.Dep.Val
import QLean.Kernel.Sort
import QLean.Kernel.Search
import QLean.Kernel.Structural
import QLean.Verify.Encoding
import QLean.Verify.SymFind

namespace LeetQ.Rel

open QLean QLean.Dep

/-- The constructors a column of type `t` may take: `gen` for the general list, `bits` for booleans,
    `syms` or `enum` for symbols, `bytes` for guids, `bytes`/`foR`/`alp` for the other fixed-width types. -/
def Column.admits : QVecType → Column → Bool
  | .general, .gen _ => true
  | .general, _ | .atom _, .gen _ => false
  | .atom .boolean, .bits .. => true
  | .atom .symbol, .syms .. | .atom .symbol, .enum .. => true
  | .atom .guid, .bytes _ => true
  | .atom .boolean, _ | .atom .symbol, _ | .atom .guid, _ => false
  | .atom _, .bytes _ | .atom _, .foR .. | .atom _, .alp .. => true
  | .atom _, _ => false

/-- A column of `n` elements of type `t`; a general list is `.gen xs`. `attr` is q's attribute byte
    (`QValue.marked`'s codes, the `ctorIdx` of `Dep.Attributes.Attr`: 1 sorted, 2 unique, 3 parted, 4
    grouped), set by producers and read by consumers (§2.4); `ix` is the `IndexCell` the first lookup builds. -/
structure Arr (t : QVecType) (n : Nat) where
  c : Column
  wf : Column.admits t c = true ∧ Column.count t c = n
  attr : UInt8 := 0
  ix : Option IndexCell := none

namespace Arr

variable {t : QVecType} {n : Nat}

/-- Element `i`. At an atomic type it is `Column.get`'s atom at `i` read back at the index; the
    fallback, the atom of zero bits, is unreachable under `wf`, as is the general list's non-`gen` one. -/
def get : {t : QVecType} → Arr t n → Fin n → El t
  | .atom a, x, i => ((Column.get a x.c i).bind (Carrier.of? a)).getD (Carrier.ofAtom (Column.atomOfBits_type a 0))
  | .general, x, i => match hc : x.c with
    | .gen xs => xs[i.1]'(by have h := x.wf.2; rw [hc] at h; simp only [Column.count] at h; omega)
    | _ => .list #[]

/-- The elements in position order, for proofs only. -/
def toList (x : Arr t n) : List (El t) := List.ofFn x.get

theorem length_toList (x : Arr t n) : x.toList.length = n := List.length_ofFn

theorem getElem_toList (x : Arr t n) (i : Nat) (h : i < x.toList.length) :
    x.toList[i] = x.get ⟨i, by rw [length_toList] at h; exact h⟩ := List.getElem_ofFn ..

/-- The list as a relation from its positions: `x i y ↔ x[j] = y` at the `j` with `Int64.ofNat j = i`. -/
def Holds (x : Arr t n) (i : Int64) (y : El t) : Prop := ∃ j : Fin n, Int64.ofNat j = i ∧ x.get j = y

theorem holds_iff_mem_zipIdx (x : Arr t n) (i : Int64) (y : El t) :
    x.Holds i y ↔ ∃ j, Int64.ofNat j = i ∧ (y, j) ∈ x.toList.zipIdx := by
  simp only [Holds, List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff, length_toList]
  constructor
  · rintro ⟨j, rfl, rfl⟩; exact ⟨j, rfl, j.2, by rw [getElem_toList]⟩
  · rintro ⟨j, rfl, h, rfl⟩; exact ⟨⟨j, h⟩, rfl, by rw [getElem_toList]⟩

/-- A kernel's answer as an `Arr`, the one way in: `wf` is decided (two O(1) reads at an atomic type, the
    constructor and the count), never assumed; `what` names the producer in the error. -/
def of (t : QVecType) (n : Nat) (c : Column) (what : String) (attr : UInt8 := 0) : Except String (Arr t n) :=
  if h : Column.admits t c = true ∧ Column.count t c = n then .ok ⟨c, h, attr, none⟩
  else .error s!"{what}: the kernel answered a payload that is not {n} well-formed elements of its type"

end Arr

/-- Ascending offsets from `0` to `n`: `g+1` cut points of `n` positions into `g` groups. -/
def Cuts {g : Nat} (o : Arr (.atom .long) (g+1)) (n : Nat) : Prop :=
  (∀ i j, i ≤ j → o.get i ≤ o.get j) ∧ o.get 0 = 0 ∧ (o.get (Fin.last g)).toInt = n

instance {g : Nat} (o : Arr (.atom .long) (g+1)) (n : Nat) : Decidable (Cuts o n) := by
  unfold Cuts; infer_instance

/-- The group holding each of `n` positions under the offsets `o`: the last cut at or below it, `o bin til n`
    (`Parted.group` read by `binBytes`). -/
def groupOf (o : ByteArray) (n : Nat) : ByteArray := Kernel.binBytes 8 false true false o (Kernel.tilLongs n.toUSize)

/-- `xs` as a dense long payload, eight bytes each: the literal columns of every module's checks. -/
def packLongs (xs : List Int64) : ByteArray := xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty

/-- Under `wf`, a long `bytes` column's element `i` is the eight bytes at `8i`, read as a long. -/
theorem Arr.get_long_bytes {m : Nat} (x : Arr (.atom .long) m) {b : ByteArray} (hc : x.c = .bytes b) (i : Fin m) :
    x.get i = (Column.bitsAt b (i.1 * 8) 8).toInt64 := by
  have hn : i.1 < Column.count (.atom .long) (.bytes b) := by have := x.wf.2; rw [hc] at this; omega
  show ((Column.get .long x.c i.1).bind (Carrier.of? .long)).getD _ = _
  rw [hc]; simp only [Column.get, if_pos hn]; rfl

/-- Under `wf`, a long `bytes` column holds `b.size / 8` elements. -/
theorem Arr.n_long_bytes {m : Nat} (x : Arr (.atom .long) m) {b : ByteArray} (hc : x.c = .bytes b) :
    b.size / 8 = m := by
  have := x.wf.2; rw [hc] at this; exact this

/-- Under `wf`, a long `bytes` column lists its eight-byte words, each read as a long. -/
theorem Arr.toList_long_bytes {m : Nat} (x : Arr (.atom .long) m) {b : ByteArray} (hc : x.c = .bytes b) :
    x.toList = ((List.range m).map fun i => Column.bitsAt b (i * 8) 8).map UInt64.toInt64 := by
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 h2
  rw [Arr.getElem_toList, Arr.get_long_bytes x hc]; simp

/-- `foRBits` with no hoisted table reads the start `blockStarts` holds (`blockStarts_get`), so
    `Column.get`'s `#[]` and the kernels' table are one decode. -/
theorem foRBits_starts (md pk : ByteArray) (i : Nat) :
    Column.foRBits md pk #[] i = Column.foRBits md pk (Column.blockStarts md) i := by
  have hs : (Column.blockStarts md).size = Column.nblk md + 1 := (Verify.blockStarts_fold md (Column.nblk md)).2.1
  unfold Column.foRBits
  by_cases h : i / Column.blk ≤ Column.nblk md
  · simp [Verify.blockStarts_get md h]
  · simp [Array.getElem?_eq_none (show (Column.blockStarts md).size ≤ i / Column.blk by omega)]

/-- Under `wf`, a long `foR` column's element `i` is its `foRBits` decode, read as a long. -/
theorem Arr.get_long_foR {m : Nat} (x : Arr (.atom .long) m) {n : Nat} {md pk : ByteArray} (hc : x.c = .foR n md pk)
    (i : Fin m) : x.get i = (Column.foRBits md pk (Column.blockStarts md) i.1).toInt64 := by
  have hn : i.1 < Column.count (.atom .long) (.foR n md pk) := by have := x.wf.2; rw [hc] at this; omega
  show ((Column.get .long x.c i.1).bind (Carrier.of? .long)).getD _ = _
  rw [hc, ← foRBits_starts]; simp only [Column.get, if_pos hn]; rfl

/-- A long column's words in position order: a `bytes` payload's eight-byte elements, a `foR` payload's
    `foRBits` decode. `none` at `alp`, whose decode has no law yet, and at the non-long constructors. -/
def longWords : Column → Option (List UInt64)
  | .bytes b => some (Verify.elemsW 8 b)
  | .foR n md pk => some ((List.range n).map (Column.foRBits md pk (Column.blockStarts md)))
  | _ => none

/-- Under `wf`, a long column lists its words, each read as a long: `toList_long_bytes` and the `foR` decode. -/
theorem Arr.toList_long {m : Nat} (x : Arr (.atom .long) m) {ws : List UInt64} (h : longWords x.c = some ws) :
    x.toList = ws.map UInt64.toInt64 := by
  cases hc : x.c with
  | bytes b => rw [hc] at h; cases h; rw [Arr.toList_long_bytes x hc, Verify.elemsW, Arr.n_long_bytes x hc]
  | foR n md pk =>
    rw [hc] at h; cases h
    have hn : n = m := by have := x.wf.2; rw [hc] at this; exact this
    subst hn
    apply List.ext_getElem (by rw [Arr.length_toList]; simp)
    intro i h1 h2; rw [Arr.getElem_toList, Arr.get_long_foR x hc]; simp
  | _ => all_goals (rw [hc] at h; cases h)

/-- Element `i` of a long column is word `i`, read as a long. -/
theorem Arr.get_long {m : Nat} (x : Arr (.atom .long) m) {ws : List UInt64} (h : longWords x.c = some ws)
    (i : Nat) (hi : i < m) (hw : i < ws.length) : x.get ⟨i, hi⟩ = ws[i].toInt64 := by
  rw [← Arr.getElem_toList x i (by rw [Arr.length_toList]; exact hi)]
  simp [Arr.toList_long x h]

/-- The dense payload a kernel reads off a long column that lists `longWords`: a `bytes` payload is
    itself, a `foR` one is handed over or decoded (`decodeW`) to the same words. -/
theorem Arr.dense_long {m : Nat} (x : Arr (.atom .long) m) {ws : List UInt64} (h : longWords x.c = some ws)
    (hm : m < USize.size) : ∃ B, (x.c = .bytes B ∨ ∃ md pk, x.c = .foR m md pk ∧
      B = Kernel.Coc.decode (8 : Nat).toUSize md pk m.toUSize) ∧ Column.bytesOf .long x.c = some B ∧
      Verify.elemsW 8 B = ws ∧ B.size / 8 = m := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  cases hc : x.c with
  | bytes b => rw [hc] at h; cases h; exact ⟨b, .inl rfl, rfl, rfl, Arr.n_long_bytes x hc⟩
  | foR n md pk =>
    rw [hc] at h; cases h
    have hn : n = m := by have := x.wf.2; rw [hc] at this; exact this
    subst hn
    obtain ⟨hsz, hg⟩ := Verify.decodeW (8 : Nat).toUSize (by rw [h8]; decide) md pk n.toUSize
    rw [h8, USize.toNat_ofNat_of_lt' hm] at hsz hg
    refine ⟨_, .inr ⟨md, pk, rfl, rfl⟩, rfl, List.ext_getElem (by simp [Verify.elemsW, hsz]) fun i h1 _ => ?_,
      by rw [hsz]; omega⟩
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [hg i (by simpa [Verify.elemsW, hsz] using h1), Verify.ofNat_toNat_mod64]
  | _ => all_goals (rw [hc] at h; cases h)

/-- A dense long answer lists its words whichever form `Column.answer` leaves it in: dense, or encoded
    (`foRBits_encode_bits`). -/
theorem longWords_answer (b : ByteArray) : longWords (Column.answer .long (.bytes b)) = some (Verify.elemsW 8 b) := by
  have ha : Column.answer .long (.bytes b) = .bytes b ∨ Column.answer .long (.bytes b) =
      .foR (b.size / 8) (Kernel.Coc.encode (8 : Nat).toUSize b).1 (Kernel.Coc.encode (8 : Nat).toUSize b).2 := by
    simp only [Column.answer, QAtomicType.width, show Column.alpEncodes .long = false from rfl,
      show Column.encodes .long = true from rfl, Kernel.Coc.encodeBelow]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  rcases ha with e | e <;> rw [e]
  · rfl
  · simp only [longWords, Verify.elemsW]
    refine congrArg some (List.map_congr_left fun i hi => UInt64.toNat_inj.1 ?_)
    rw [← Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    exact Verify.foRBits_encode_bits 8 (by decide) (by decide) b i (List.mem_range.1 hi)

/-- An `int` answer column, dense or encoded, lists its payload's four-byte words: `longWords_answer` at
    width four, the `foR` form read back by `foRBits_encode_bits`. -/
theorem toList_answer_int {m : Nat} (x : Arr (.atom .int) m) {b : ByteArray} (hc : x.c = Column.answer .int (.bytes b)) :
    x.toList = (List.range m).map fun i => (Column.bitsAt b (i * 4) 4).toUInt32.toInt32 := by
  have ha : Column.answer .int (.bytes b) = .bytes b ∨ Column.answer .int (.bytes b) =
      .foR (b.size / 4) (Kernel.Coc.encode (4 : Nat).toUSize b).1 (Kernel.Coc.encode (4 : Nat).toUSize b).2 := by
    simp only [Column.answer, QAtomicType.width, show Column.alpEncodes .int = false from rfl,
      show Column.encodes .int = true from rfl, Kernel.Coc.encodeBelow]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  have hm : Column.count (.atom .int) x.c = m := x.wf.2
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 _
  have hn : i < Column.count (.atom .int) x.c := by rw [Arr.length_toList] at h1; omega
  rw [Arr.getElem_toList, List.getElem_map, List.getElem_range]
  show ((Column.get .int x.c i).bind (Carrier.of? .int)).getD _ = _
  rcases ha with e | e <;> rw [hc, e] at hn ⊢ <;> simp only [Column.get, if_pos hn]
  · rfl
  · have hi : i < b.size / 4 := hn
    show (Column.foRBits _ _ #[] i).toUInt32.toInt32 = _
    rw [foRBits_starts]
    congr 1
    apply UInt32.toNat_inj.1
    rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, Verify.foRBits_encode_bits 4 (by decide) (by decide) b i hi,
      Nat.mod_eq_of_lt (Verify.bitsAt_lt _ _ _ (by decide))]

/-- Reading a word as a long loses nothing. -/
theorem toInt64_inj {x y : UInt64} (h : x.toInt64 = y.toInt64) : x = y := by
  simpa using congrArg Int64.toUInt64 h

/-- Under `wf`, a boolean `bits` column's element `i` is its bit `i`. -/
theorem Arr.get_bool_bits {m : Nat} (x : Arr (.atom .boolean) m) {n : Nat} {b : ByteArray} (hc : x.c = .bits n b)
    (i : Fin m) : x.get i = Column.bitAt b i.1 := by
  have hn : i.1 < Column.count (.atom .boolean) (.bits n b) := by have := x.wf.2; rw [hc] at this; omega
  show ((Column.get .boolean x.c i.1).bind (Carrier.of? .boolean)).getD _ = _
  rw [hc]; simp only [Column.get, if_pos hn]; rfl

/-- A string is its UTF-8 bytes: two strings with one byte list are one string. -/
theorem toUTF8_inj {s t : String} (h : s.toUTF8.data.toList = t.toUTF8.data.toList) : s = t :=
  String.toByteArray_inj.1 (ByteArray.ext (Array.ext' h))

/-- The `str` bridge: bytes that are some string's UTF-8, read as a string the way `Column.get` reads a
    symbol (`fromUTF8?`, `""` at invalid bytes), write back out as themselves. -/
theorem str_bytes {B : ByteArray} (h : ∃ s : String, s.toUTF8.data.toList = B.data.toList) :
    ((String.fromUTF8? B).getD "").toUTF8.data.toList = B.data.toList := by
  obtain ⟨s, hs⟩ := h
  obtain rfl : s.toByteArray = B := ByteArray.ext (Array.ext' hs)
  simp only [String.fromUTF8?, s.isValidUTF8, dite_true, Option.getD_some]
  rfl

/-- A symbol payload's element `i`, read as `Column.get` reads it, writes out as `symsOf`'s symbol `i`
    wherever that symbol is UTF-8. -/
theorem get_sym_bytes {c : Column} {i : Nat} (d : String) (ha : Column.admits (.atom .symbol) c = true)
    (hi : i < Column.count (.atom .symbol) c) (h2 : i < (Verify.symsOf c).length)
    (hk : ∃ s : String, s.toUTF8.data.toList = (Verify.symsOf c)[i]) :
    (((Column.get .symbol c i).bind (Carrier.of? .symbol)).getD d).toUTF8.data.toList = (Verify.symsOf c)[i] := by
  cases c with
  | syms b o =>
    rw [show Column.get .symbol (.syms b o) i = some (.symbol ((String.fromUTF8? (Column.symKey b o i)).getD ""))
      by simp only [Column.get, if_pos hi]; rfl]
    simp only [Option.bind_some, Carrier.of?, Option.getD_some, Verify.symsOf, List.getElem_map,
      List.getElem_range, Verify.symAt] at hk ⊢
    exact str_bytes hk
  | enum n d o ids =>
    rw [show Column.get .symbol (.enum n d o ids) i = some (.symbol ((String.fromUTF8?
      (Column.symKey d o (Column.idAt ids (Column.idWidth o) i))).getD "")) by simp only [Column.get, if_pos hi]; rfl]
    simp only [Option.bind_some, Carrier.of?, Option.getD_some, Verify.symsOf, List.getElem_map,
      List.getElem_range, Verify.symAt] at hk ⊢
    exact str_bytes hk
  | _ => simp [Column.admits] at ha

/-- Under `wf`, a symbol column whose symbols are UTF-8 lists them: each element's bytes are `symsOf`'s
    symbol at its position, a blob's own or an interned column's dictionary entry. -/
theorem Arr.toList_sym {m : Nat} (x : Arr (.atom .symbol) m)
    (hu : ∀ k ∈ Verify.symsOf x.c, ∃ s : String, s.toUTF8.data.toList = k) :
    x.toList.map (·.toUTF8.data.toList) = Verify.symsOf x.c := by
  obtain ⟨ha, hn⟩ := x.wf
  have hl : (Verify.symsOf x.c).length = m := Eq.trans (by
    revert ha; cases x.c <;> simp [Column.admits, Column.count, Verify.symsOf]) hn
  refine List.ext_getElem (by rw [List.length_map, Arr.length_toList, hl]) fun i h1 h2 => ?_
  rw [List.length_map, Arr.length_toList] at h1
  rw [List.getElem_map, Arr.getElem_toList]
  exact get_sym_bytes _ ha (by rw [hn]; exact h1) h2 (hu _ (List.getElem_mem h2))

/-- A word whose natural value is `m` reads as the long `Int64.ofNat m`. -/
theorem toInt64_of_toNat {x : UInt64} {m : Nat} (h : x.toNat = m) : x.toInt64 = Int64.ofNat m := by
  subst h; cases x; simp [Int64.ofNat, UInt64.toInt64]

/-- Below `2^i`, xor with `2^i` sets that bit: it adds `2^i`. -/
theorem xor_two_pow_of_lt {r i : Nat} (h : r < 2 ^ i) : r ^^^ 2 ^ i = 2 ^ i + r := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy j i with hj | rfl | hj
  · rw [Nat.testBit_two_pow_add_gt hj]; simp [Nat.ne_of_gt hj]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h]; simp
  · have hp : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
    rw [Nat.pow_succ] at hp
    rw [Nat.testBit_lt_two_pow (show 2 ^ i + r < 2 ^ j by omega), Nat.testBit_lt_two_pow (show r < 2 ^ j by omega)]
    simp [Nat.ne_of_lt hj]

/-- Flipping bit 63 of a 64-bit number moves it by `2^63`: up below `2^63`, down at or above. -/
theorem xor_two_pow_63 (n : Nat) (h : n < 2 ^ 64) : n ^^^ 2 ^ 63 = if n < 2 ^ 63 then n + 2 ^ 63 else n - 2 ^ 63 := by
  split
  · rw [xor_two_pow_of_lt ‹_›]; omega
  · have e : n = (n - 2 ^ 63) ^^^ 2 ^ 63 := by rw [xor_two_pow_of_lt (show n - 2 ^ 63 < 2 ^ 63 by omega)]; omega
    conv => lhs; rw [e]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- `Order.rank .i64` flips the sign bit: unsigned order on ranks is signed order on longs. Both sides are
    read as naturals — the rank by `xor_two_pow_63`, the long by `toInt_eq_msb_cond` — and compared by `omega`. -/
theorem rank_i64_le {x y : UInt64} (h : Kernel.Order.rank .i64 x ≤ Kernel.Order.rank .i64 y) : x.toInt64 ≤ y.toInt64 := by
  simp only [Kernel.Order.rank] at h
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_xor, UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl,
    xor_two_pow_63 _ x.toNat_lt, xor_two_pow_63 _ y.toNat_lt] at h
  rw [Int64.le_iff_toInt_le, Int64.toInt, Int64.toInt, BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide, BitVec.msb_eq_decide]
  show (if decide (2 ^ 63 ≤ x.toNat) = true then (x.toNat : Int) - (2 ^ 64 : Nat) else x.toNat) ≤
    (if decide (2 ^ 63 ≤ y.toNat) = true then (y.toNat : Int) - (2 ^ 64 : Nat) else y.toNat)
  have := x.toNat_lt; have := y.toNat_lt
  split <;> split <;> split at h <;> split at h <;> simp_all <;> omega

/-- `rank_i64_le` both ways: `Order.rank .i64` is an order embedding of longs into words. -/
theorem rank_i64_le_iff {x y : UInt64} :
    Kernel.Order.rank .i64 x ≤ Kernel.Order.rank .i64 y ↔ x.toInt64 ≤ y.toInt64 :=
  ⟨rank_i64_le, fun h => Classical.byContradiction fun hn => by
    have hl := UInt64.not_le.1 hn
    have e := toInt64_inj (Int64.le_antisymm h (rank_i64_le (UInt64.le_of_lt hl)))
    rw [e] at hl; exact UInt64.lt_irrefl _ hl⟩

/-- The signed key `bin` halves a long payload by is `Order.rank .i64`. -/
theorem ordKey_long (v : UInt64) : Kernel.ordKey 8 false true v = Kernel.Order.rank .i64 v := by
  simp [Kernel.ordKey, Kernel.Order.rank]
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_and, show (18446744073709551615 : UInt64).toNat = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt v.toNat_lt]

/-- `Cuts` from `Order.ascending`'s Lean body on the dense payload, and the two end reads. -/
theorem cuts_of_ascending {g n : Nat} (o : Arr (.atom .long) (g+1)) {b : ByteArray} (hc : o.c = .bytes b)
    (hu : g + 1 < USize.size) (ha : Kernel.Order.ascending .i64 false false (g+1).toUSize b = true)
    (h0 : o.get 0 = 0) (hl : (o.get (Fin.last g)).toInt = n) : Cuts o n := by
  refine ⟨?_, h0, hl⟩
  have hsz : b.size / 8 = g + 1 := by have := o.wf.2; rw [hc] at this; exact this
  have adj : ∀ i (h : i + 1 < g + 1), o.get ⟨i, by omega⟩ ≤ o.get ⟨i + 1, h⟩ := by
    intro i h
    simp only [Kernel.Order.ascending, List.all_eq_true, List.mem_range] at ha
    have hm : (g + 1).toUSize.toNat = g + 1 := USize.toNat_ofNat_of_lt hu
    have := ha i (by simp only [Kernel.Scan.Kind.avail, Kernel.Scan.Kind.width, hm, hsz]; omega)
    simp only [Bool.false_eq_true, if_false, decide_eq_true_eq, Kernel.Order.keyAt, Kernel.Scan.Kind.bitsAt,
      Kernel.Scan.Kind.width] at this
    rw [Arr.get_long_bytes o hc, Arr.get_long_bytes o hc]
    exact rank_i64_le this
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  change i ≤ j at hij
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  induction d with
  | zero => exact Int64.le_refl _
  | succ d ih => exact Int64.le_trans (ih (by omega) (by omega)) (adj (i + d) hj)

/-- Under `Cuts o n`, offsets `i ≤ j ≤ g` read `0 ≤ o[i] ≤ o[j] ≤ n`. -/
theorem cuts_get {g n : Nat} {o : Arr (.atom .long) (g+1)} (co : Cuts o n) {i j : Nat} (hij : i ≤ j) (hj : j ≤ g) :
    0 ≤ (o.toList[i]!).toInt ∧ (o.toList[i]!).toInt ≤ (o.toList[j]!).toInt ∧ (o.toList[j]!).toInt ≤ n := by
  have e : ∀ m (hm : m ≤ g), o.toList[m]! = o.get ⟨m, by omega⟩ := fun m hm => by
    rw [getElem!_pos _ m (by rw [Arr.length_toList]; omega), Arr.getElem_toList]
  obtain ⟨hm, h0, hl⟩ := co
  rw [e i (by omega), e j hj]
  have a := Int64.le_iff_toInt_le.1 (hm 0 ⟨i, by omega⟩ (by simp [Fin.le_def]))
  have b := Int64.le_iff_toInt_le.1 (hm ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.le_def]; omega))
  have c := Int64.le_iff_toInt_le.1 (hm ⟨j, by omega⟩ (Fin.last g) (by simp [Fin.le_def]; omega))
  rw [h0] at a; rw [hl] at c
  exact ⟨by simpa using a, b, c⟩

/-- A long payload as dense bytes: `bytes` as it is, `foR` decoded once (`Coc.decode`). -/
def longBytes : Column → Option ByteArray
  | .bytes b => some b
  | .foR m md pk => some (Kernel.Coc.decode 8 md pk m.toUSize)
  | _ => none

/-- The column of a q vector answer. -/
def vecCol : QValue → Option Column
  | .vector _ c => some c
  | _ => none


/-- Under `Cuts o n`, a position exists only when there is a group to hold it. -/
theorem Cuts.pos {g n : Nat} {o : Arr (.atom .long) (g+1)} (co : Cuts o n) (i : Fin n) : 0 < g := by
  rcases g with _ | g
  · have h2 := co.2.2; rw [show Fin.last 0 = 0 from rfl, co.2.1] at h2; simp at h2; have := i.2; omega
  · omega

/-- A parted list in its flat form: `n` values cut into `g` groups by the `g+1` offsets `o`. It is the
    kernels' working shape, never a value: `box` turns it into q's nested list, one vector per group. -/
structure Parted (v : QVecType) where
  g : Nat
  n : Nat
  o : Arr (.atom .long) (g+1)
  co : Cuts o n
  val : Arr v n

namespace Parted

variable {v : QVecType}

/-- The number of cut points after the first at or below `i`: the largest `r` with `o[r] ≤ i`, which
    under `Cuts` is the group holding `i`. -/
def group {g : Nat} (o : Arr (.atom .long) (g+1)) (i : Nat) : Nat :=
  (List.finRange g).countP fun r => (o.get r.succ).toInt ≤ i

/-- The group holding position `i`; the `min` is unreachable under `Cuts`, which puts `group o i < g`. -/
def key (P : Parted v) (i : Fin P.n) : Fin P.g := ⟨min (group P.o i) (P.g - 1), by have := P.co.pos i; omega⟩

/-- The pairs `(group, value)` in position order, for proofs only. -/
def toList (P : Parted v) : List (Int64 × El v) := List.ofFn fun i => (Int64.ofNat (P.key i), P.val.get i)

/-- `Parted` built at run time: `Cuts` decided by `Order.ascending` on `o`'s dense payload and one read of
    each end, `cuts_of_ascending` turning the kernel's answer into the proof. `none` when `o` is not cuts of `n`. -/
def of? {g n : Nat} (o : Arr (.atom .long) (g+1)) (val : Arr v n) : Option (Parted v) := do
  let b ← longBytes o.c
  if h : (Column.admits (.atom .long) (.bytes b) = true ∧ Column.count (.atom .long) (.bytes b) = g+1) ∧
      g + 1 < USize.size then
    let ob : Arr (.atom .long) (g+1) := ⟨.bytes b, h.1, o.attr, none⟩
    if hc : Kernel.Order.ascending .i64 false false (g+1).toUSize b = true ∧ ob.get 0 = 0 ∧ (ob.get (Fin.last g)).toInt = n then
      some ⟨g, n, ob, cuts_of_ascending ob rfl h.2 hc.1 hc.2.1 hc.2.2, val⟩
    else none
  else none

/-- Group `r`'s values `val[o[r] … o[r+1]-1]` as a q value: `sliceColumn` at an atomic type, the
    general list's sub-array otherwise. -/
def slice (P : Parted v) (r : Fin P.g) : Option QValue :=
  let lo := (P.o.get r.castSucc).toNatClampNeg; let hi := (P.o.get r.succ).toNatClampNeg
  match v, P.val.c with
  | .atom t, c => Kernel.sliceColumn t c lo (hi - lo)
  | .general, .gen xs => some (.list (xs.extract lo hi))
  | .general, _ => none

/-- q's nested list: one vector per group, each its own slice. -/
def box (P : Parted v) : Except String (Arr .general P.g) := do
  let some xs := (Array.ofFn (P.slice ·)).mapM id | throw "box: sliceColumn declines a group's slice"
  Arr.of .general P.g (.gen xs) "box"

/-- The parts of a nested list as each part's count and one flat column: `raze` of the vectors at an
    atomic type, the concatenated lists at `.general`; a part of another shape is declined. -/
def razeParts : QVecType → Array QValue → Except String (Array Nat × Column)
  | .atom t, xs => do
    let cs ← xs.mapM fun | .vector t' c => if t' == .atom t then pure c else throw "razeParts: a part of another type"
                          | _ => throw "razeParts: a part that is not a vector"
    let some c := (if cs.isEmpty then Kernel.sliceColumn t (Kernel.nullColumn t) 0 0 else Kernel.razeColumn t cs).bind vecCol
      | throw "razeParts: razeColumn declines the parts"
    pure (cs.map (Column.count (.atom t)), c)
  | .general, xs => do
    let ls ← xs.mapM fun | .list ys => pure ys | _ => throw "razeParts: a general part that is not a list"
    pure (ls.map (·.size), Column.gen (ls.foldl (· ++ ·) #[]))

/-- The flat form of a nested list of `g` parts at `v`: `razeParts`, the offsets their running counts. -/
def ofBoxes (v : QVecType) {g : Nat} (b : Arr .general g) : Except String (Parted v) := do
  let .gen xs := b.c | throw "ofBoxes: a nested list's payload is not .gen"
  let (cnt, c) ← razeParts v xs
  let os := cnt.foldl (fun (s, b) m => (s + m, Column.pushBits b (Int64.ofNat (s + m)).toUInt64 8)) (0, Column.pushBits .empty 0 8)
  let o ← Arr.of (.atom .long) (g+1) (.bytes os.2) "ofBoxes"
  let val ← Arr.of v os.1 c "ofBoxes"
  let some P := of? o val | throw "ofBoxes: the running counts are not cuts"
  pure P

end Parted

/-- A relation from `k` to `v`: `n` positions, a key and a value at each — q's dict, two arrays. -/
structure Rel (k v : QVecType) where
  n : Nat
  key : Arr k n
  val : Arr v n

namespace Rel

variable {k v : QVecType}

/-- The relation `R` denotes: `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y`. -/
def Holds (R : Rel k v) (x : El k) (y : El v) : Prop := ∃ i, R.key.get i = x ∧ R.val.get i = y

/-- The pairs, in position order, for proofs only. -/
def toList (R : Rel k v) : List (El k × El v) := List.ofFn fun i => (R.key.get i, R.val.get i)

theorem holds_iff_mem_toList (R : Rel k v) (x : El k) (y : El v) : R.Holds x y ↔ (x, y) ∈ R.toList := by
  simp [Holds, toList, List.mem_ofFn]

end Rel

/-! ## Sanity checks on small literal columns -/

section Checks

open QLean.Column


private def l3 : Arr (.atom .long) 3 := { c := .bytes <| packLongs [7, -1, 42], wf := by decide }
#guard l3.toList == [7, -1, 42]

private def bs : Arr (.atom .boolean) 3 := { c := .bits 3 (ByteArray.mk #[0b101]), wf := by decide }
#guard bs.toList == [true, false, true]

-- one symbol column, as `syms` and as `enum` over the dictionary `a, bc`
private def blob : ByteArray := ByteArray.mk #[97, 0, 98, 99, 0]
private def ss : Arr (.atom .symbol) 3 := { c := .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8], wf := by decide }
private def es : Arr (.atom .symbol) 3 :=
  { c := .enum 3 blob #[0, 2, 5] (packIds (idWidth #[0, 2, 5]) 3 fun i => [1, 0, 1][i]!), wf := by decide }
#guard ss.toList == ["bc", "a", "bc"]
#guard es.toList == ss.toList

private def gs : Arr .general 2 := { c := .gen #[.atom (.long 1), .list #[]], wf := ⟨rfl, rfl⟩ }
#guard match gs.get 0, gs.get 1 with | .atom (.long 1), .list #[] => true | _, _ => false

-- groups `[0,1) [1,1) [1,3)`: the empty middle group owns no position
private def o3 : Arr (.atom .long) 4 := { c := .bytes <| packLongs [0, 1, 1, 3], wf := by decide }
-- the parted list `(10 20; 30)`: positions `0 1 | 2`, groups `0 0 1`
private def o2 : Arr (.atom .long) 3 := { c := .bytes <| packLongs [0, 2, 3], wf := by decide }
private def v3 : Arr (.atom .long) 3 := { c := .bytes <| packLongs [10, 20, 30], wf := by decide }
-- `of?` decides `Cuts` at run time, on `bytes` and on `foR` offsets
private def o3f : Arr (.atom .long) 4 :=
  { c := .foR 4 (Kernel.Coc.encode 8 (packLongs [0, 1, 1, 3])).1
      (Kernel.Coc.encode 8 (packLongs [0, 1, 1, 3])).2, wf := ⟨rfl, rfl⟩ }
#guard [o3, o3f].all fun o => ((Parted.of? o v3).map Parted.toList) == some [(0, 10), (2, 20), (2, 30)]
#guard ((Parted.of? o2 v3).map Parted.toList) == some [(0, 10), (0, 20), (1, 30)]
#guard (Parted.of? o2 ({ c := .bytes <| packLongs [10, 20], wf := by decide } : Arr (.atom .long) 2)).isNone
#guard (Parted.of? ({ c := .bytes <| packLongs [0, 2, 1], wf := by decide } : Arr (.atom .long) 3) v3).isNone
#guard (Parted.of? ({ c := .bytes <| packLongs [1, 2, 3], wf := by decide } : Arr (.atom .long) 3) v3).isNone
-- `box` then `ofBoxes` is the identity on the flat form, and each box is q's vector of its slice
#guard match Parted.of? o3 v3 with
  | some P => match P.box with
    | .ok b => (match (b.toList[1]? : Option QValue) with | some (.vector (.atom .long) c) => Column.count (.atom .long) c == 0 | _ => false) &&
        match Parted.ofBoxes (.atom .long) b with | .ok Q => Q.toList == P.toList | .error _ => false
    | .error _ => false
  | none => false
#guard ss.toList.zipIdx == [("bc", 0), ("a", 1), ("bc", 2)]
example : ss.Holds 1 "a" := (ss.holds_iff_mem_zipIdx 1 "a").2 ⟨1, rfl, by decide⟩

end Checks

#print axioms Arr.get
#print axioms Parted.key
#print axioms Parted.of?
#print axioms cuts_of_ascending
#print axioms Rel.holds_iff_mem_toList

end LeetQ.Rel
