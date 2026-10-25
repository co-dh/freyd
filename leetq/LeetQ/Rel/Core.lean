/-
  The RelRep core: a relation is a key and a value column of one length `n` over the positions
  `0 … n-1`, `R x y ↔ ∃ i, key.get i = x ∧ val.get i = y` — a tabulation, `key° ≫ val = R`.
  Columns are qlean's `Column`s in whatever encoding carries them; an element is read through
  `Column.get` (qlean's one-element reader over `bitsAt`/`bitAt`/`foRBits`/`symBytes`), never
  `Column.atoms`. Lists exist in proofs only (`toList`).
-/
import QLean.Value
import QLean.Dep.Val
import QLean.Dep.Monadic
import QLean.Kernel.Sort
import QLean.Kernel.Search
import QLean.Kernel.Structural
import QLean.Verify.Encoding
import QLean.Verify.SymFind
import QLean.Verify.Alp

namespace LeetQ.Rel

open QLean QLean.Dep

/-- An element of a column of type `t`: qlean's `Carrier`, a `QValue` in a general list. -/
abbrev El := Carrier

/-- A column of `n` elements of type `t`: the header says `t` and `n`, and `Column.WF` that the payload
    agrees with it; a general list is `.gen xs`. q's attribute is the column's own `c.attr` (codes 1 sorted,
    2 unique, 3 parted, 4 grouped, with the `IndexCell` of its index), set by producers and read by
    consumers (§2.4). -/
structure Arr (t : QAtomicType) (n : Nat) where
  c : Column
  wf : c.ty = t ∧ c.n = n ∧ c.WF

namespace Arr

variable {t : QAtomicType} {n : Nat}

/-- Under `wf`, a general list's payload is `gen` and holds its `n` elements. -/
theorem gen_size (x : Arr .general n) {xs : Array QValue} (hc : x.c.enc = .gen xs) : xs.size = n := by
  have hw := x.wf.2.2; have := x.wf.2.1
  simp only [Column.WF, x.wf.1, hc] at hw; omega

/-- Element `i`. At an atom type it is `Column.get`'s atom at `i` read back at the index; the
    fallback, the atom of zero bits, is unreachable under `wf`, as is the general list's non-`gen` one. -/
def get (x : Arr t n) (i : Fin n) : El t :=
  match t, x with
  | .general, x => match hc : x.c.enc with
    | .gen xs => xs[i.1]'(by rw [gen_size x hc]; exact i.2)
    | _ => QValue.general #[]
  | t, x => ((Column.get x.c i).bind fun a => Carrier.of? t (.atom a)).getD default

/-- `get` at an atom type: `Column.get`'s atom read back at `t`. -/
theorem get_ne (x : Arr t n) (i : Fin n) (h : t ≠ .general) :
    x.get i = ((Column.get x.c i).bind fun a => Carrier.of? t (.atom a)).getD default := by
  cases t <;> first | exact absurd rfl h | rfl

/-- Under `wf`, the column is its header and the payload `e`: what a kernel matching `⟨_, n, e⟩` sees. -/
theorem c_eq (x : Arr t n) {e : Enc} (h : x.c.enc = e) : x.c = ⟨t, n, e, x.c.attr⟩ := by
  revert h; obtain ⟨⟨ty, m, enc, a⟩, ⟨h1, h2, -⟩⟩ := x; intro h; simp only at h1 h2 h; subst h1 h2 h; rfl

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

/-- A kernel's answer as an `Arr`, the one way in: `wf` is decided (the header's two fields and
    `Column.WF`), never assumed; `what` names the producer in the error. A nonzero `attr` marks the answer
    (`QValue.mark`'s cell); `0` leaves the kernel's column as it is. -/
def of (t : QAtomicType) (n : Nat) (c : Column) (what : String) (attr : UInt8 := 0) : Except String (Arr t n) :=
  let c := if attr == 0 then c else { c with attr := some (attr, QValue.IndexCell.new attr (.vector c)) }
  if h : c.ty = t ∧ c.n = n ∧ c.WF then .ok ⟨c, h⟩
  else .error s!"{what}: the kernel answered a payload that is not {n} well-formed elements of its type"

end Arr

/-- Ascending offsets from `0` to `n`: `g+1` cut points of `n` positions into `g` groups. -/
def Cuts {g : Nat} (o : Arr .long (g+1)) (n : Nat) : Prop :=
  (∀ i j, i ≤ j → o.get i ≤ o.get j) ∧ o.get 0 = 0 ∧ (o.get (Fin.last g)).toInt = n

instance {g : Nat} (o : Arr .long (g+1)) (n : Nat) : Decidable (Cuts o n) := by
  unfold Cuts; infer_instance

/-- The group holding each of `n` positions under the offsets `o`: the last cut at or below it, `o bin til n`
    (`Parted.group` read by `binBytes`). -/
def groupOf (o : ByteArray) (n : Nat) : ByteArray := Kernel.binBytes 8 false true false o (Kernel.tilLongs n.toUSize)

/-- `xs` as a dense long payload, eight bytes each: the literal columns of every module's checks. -/
def packLongs (xs : List Int64) : ByteArray := xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty

theorem packLongs_size (xs : List Int64) : (packLongs xs).size = 8 * xs.length := by
  suffices ∀ b : ByteArray, (xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) b).size = b.size + 8 * xs.length by
    simpa [packLongs] using this .empty
  induction xs with
  | nil => simp
  | cons x xs ih => intro b; rw [List.foldl_cons, ih, Column.pushBits_size, List.length_cons]; omega

/-- `xs` Frame-of-Reference encoded is well formed: the checks' `foR` columns, which `decide` cannot
    evaluate through `Coc.encode`. -/
theorem foRLongs_wf (xs : List Int64) : (⟨.long, xs.length,
    .foR (Kernel.Coc.encode 8 (packLongs xs)).1 (Kernel.Coc.encode 8 (packLongs xs)).2, none⟩ : Column).WF := by
  have h := Verify.nblk_encode 8 (by decide) (by decide) (packLongs xs)
  rw [packLongs_size] at h
  refine ⟨rfl, by simp, by simp, ?_⟩
  show xs.length ≤ Column.blk * Column.nblk (Kernel.Coc.encode (8 : Nat).toUSize (packLongs xs)).1
  rw [h]; simp only [Column.blk]; omega

/-- Under `wf`, a long `bytes` column holds `b.size / 8` elements. -/
theorem Arr.n_long_bytes {m : Nat} (x : Arr .long m) {b : ByteArray} (hc : x.c.enc = .bytes b) :
    b.size / 8 = m := by
  have hw := x.wf.2.2; have := x.wf.2.1
  simp only [Column.WF, x.wf.1, hc, QAtomicType.width] at hw; omega

/-- Under `wf`, a long `bytes` column's element `i` is the eight bytes at `8i`, read as a long. -/
theorem Arr.get_long_bytes {m : Nat} (x : Arr .long m) {b : ByteArray} (hc : x.c.enc = .bytes b) (i : Fin m) :
    x.get i = (Column.bitsAt b (i.1 * 8) 8).toInt64 := by
  have hn : i.1 < x.c.n := by have := x.wf.2.1; omega
  rw [Arr.get_ne x i (by decide)]
  simp only [Column.get, if_pos hn, x.wf.1, hc, QAtomicType.width]; rfl

/-- Under `wf`, a long `bytes` column lists its eight-byte words, each read as a long. -/
theorem Arr.toList_long_bytes {m : Nat} (x : Arr .long m) {b : ByteArray} (hc : x.c.enc = .bytes b) :
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
theorem Arr.get_long_foR {m : Nat} (x : Arr .long m) {md pk : ByteArray} (hc : x.c.enc = .foR md pk)
    (i : Fin m) : x.get i = (Column.foRBits md pk (Column.blockStarts md) i.1).toInt64 := by
  have hn : i.1 < x.c.n := by have := x.wf.2.1; omega
  rw [Arr.get_ne x i (by decide), ← foRBits_starts]
  simp only [Column.get, if_pos hn, x.wf.1, hc, QAtomicType.width]; rfl

/-- A long column's words in position order: a `bytes` payload's eight-byte elements, a `foR` payload's
    `foRBits` decode. `none` at `alp`, whose decode has no law yet, and at the non-long constructors. -/
def longWords (c : Column) : Option (List UInt64) :=
  match c.enc with
  | .bytes b => some (Verify.elemsW 8 b)
  | .foR md pk => some ((List.range c.n).map (Column.foRBits md pk (Column.blockStarts md)))
  | _ => none

/-- Under `wf`, a long column lists its words, each read as a long: `toList_long_bytes` and the `foR` decode. -/
theorem Arr.toList_long {m : Nat} (x : Arr .long m) {ws : List UInt64} (h : longWords x.c = some ws) :
    x.toList = ws.map UInt64.toInt64 := by
  unfold longWords at h
  cases hc : x.c.enc with
  | bytes b => rw [hc] at h; cases h; rw [Arr.toList_long_bytes x hc, Verify.elemsW, Arr.n_long_bytes x hc]
  | foR md pk =>
    rw [hc, x.wf.2.1] at h; cases h
    apply List.ext_getElem (by rw [Arr.length_toList]; simp)
    intro i h1 h2; rw [Arr.getElem_toList, Arr.get_long_foR x hc]; simp
  | _ => all_goals (rw [hc] at h; cases h)

/-- Element `i` of a long column is word `i`, read as a long. -/
theorem Arr.get_long {m : Nat} (x : Arr .long m) {ws : List UInt64} (h : longWords x.c = some ws)
    (i : Nat) (hi : i < m) (hw : i < ws.length) : x.get ⟨i, hi⟩ = ws[i].toInt64 := by
  rw [← Arr.getElem_toList x i (by rw [Arr.length_toList]; exact hi)]
  simp [Arr.toList_long x h]

/-- The dense payload a kernel reads off a long column that lists `longWords`: a `bytes` payload is
    itself, a `foR` one is handed over or decoded (`decodeW`) to the same words. -/
theorem Arr.dense_long {m : Nat} (x : Arr .long m) {ws : List UInt64} (h : longWords x.c = some ws)
    (hm : m < USize.size) : ∃ B, (x.c.enc = .bytes B ∨ ∃ md pk, x.c.enc = .foR md pk ∧
      B = Kernel.Coc.decode (8 : Nat).toUSize md pk m.toUSize) ∧ Column.bytesOf x.c = some B ∧
      Verify.elemsW 8 B = ws ∧ B.size / 8 = m := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  unfold longWords at h
  cases hc : x.c.enc with
  | bytes b =>
    rw [hc] at h; cases h
    exact ⟨b, .inl rfl, by simp only [Column.bytesOf, hc], rfl, Arr.n_long_bytes x hc⟩
  | foR md pk =>
    rw [hc, x.wf.2.1] at h; cases h
    obtain ⟨hsz, hg⟩ := Verify.decodeW (8 : Nat).toUSize (by rw [h8]; decide) md pk m.toUSize
    rw [h8, USize.toNat_ofNat_of_lt' hm] at hsz hg
    refine ⟨_, .inr ⟨md, pk, rfl, rfl⟩, by simp only [Column.bytesOf, hc, x.wf.1, x.wf.2.1, QAtomicType.width]; rfl,
      List.ext_getElem (by simp [Verify.elemsW, hsz]) fun i h1 _ => ?_, by rw [hsz]; omega⟩
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [hg i (by simpa [Verify.elemsW, hsz] using h1), Verify.ofNat_toNat_mod64]
  | _ => all_goals (rw [hc] at h; cases h)

/-- A dense long answer lists its words whichever form `Column.answer` leaves it in: dense, or encoded
    (`foRBits_encode_bits`). -/
theorem longWords_answer (b : ByteArray) :
    longWords (Column.answer ⟨.long, b.size / 8, .bytes b, none⟩) = some (Verify.elemsW 8 b) := by
  have ha : (Column.answer ⟨.long, b.size / 8, .bytes b, none⟩).enc = .bytes b ∨
      (Column.answer ⟨.long, b.size / 8, .bytes b, none⟩).enc =
      .foR (Kernel.Coc.encode (8 : Nat).toUSize b).1 (Kernel.Coc.encode (8 : Nat).toUSize b).2 := by
    simp only [Column.answer, QAtomicType.width, show Column.alpEncodes .long = false from rfl,
      show Column.encodes .long = true from rfl, Kernel.Coc.encodeBelow]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  have hn : (Column.answer ⟨.long, b.size / 8, .bytes b, none⟩).n = b.size / 8 := by
    simp only [Column.answer]; repeat' split
    all_goals rfl
  unfold longWords
  rcases ha with e | e
  · rw [e]
  · rw [e]; simp only [hn, Verify.elemsW]
    refine congrArg some (List.map_congr_left fun i hi => UInt64.toNat_inj.1 ?_)
    rw [← Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    exact Verify.foRBits_encode_bits 8 (by decide) (by decide) b i (List.mem_range.1 hi)

/-- An `int` answer column, dense or encoded, lists its payload's four-byte words: `longWords_answer` at
    width four, the `foR` form read back by `foRBits_encode_bits`. -/
theorem toList_answer_int {m : Nat} (x : Arr .int m) {b : ByteArray}
    (hc : x.c = Column.answer ⟨.int, b.size / 4, .bytes b, none⟩) :
    x.toList = (List.range m).map fun i => (Column.bitsAt b (i * 4) 4).toUInt32.toInt32 := by
  have ha : (Column.answer ⟨.int, b.size / 4, .bytes b, none⟩).enc = .bytes b ∨
      (Column.answer ⟨.int, b.size / 4, .bytes b, none⟩).enc =
      .foR (Kernel.Coc.encode (4 : Nat).toUSize b).1 (Kernel.Coc.encode (4 : Nat).toUSize b).2 := by
    simp only [Column.answer, QAtomicType.width, show Column.alpEncodes .int = false from rfl,
      show Column.encodes .int = true from rfl, Kernel.Coc.encodeBelow]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  have hm : x.c.n = b.size / 4 := by
    rw [hc]; simp only [Column.answer]; repeat' split
    all_goals rfl
  have ht : x.c.ty = .int := x.wf.1
  have hm' : x.c.n = m := x.wf.2.1
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 _
  have hn : i < x.c.n := by rw [Arr.length_toList] at h1; omega
  rw [Arr.getElem_toList, List.getElem_map, List.getElem_range, Arr.get_ne x _ (by decide)]
  rw [← hc] at ha
  rcases ha with e | e <;> simp only [Column.get, if_pos hn, ht, e, QAtomicType.width]
  · rfl
  · have hi : i < b.size / 4 := by omega
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
theorem Arr.get_bool_bits {m : Nat} (x : Arr .boolean m) {b : ByteArray} (hc : x.c.enc = .bits b)
    (i : Fin m) : x.get i = Column.bitAt b i.1 := by
  have hn : i.1 < x.c.n := by have := x.wf.2.1; omega
  rw [Arr.get_ne x i (by decide)]
  simp only [Column.get, if_pos hn, x.wf.1, hc]; rfl

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
theorem get_sym_bytes {c : Column} {i : Nat} (d : String) (ht : c.ty = .symbol) (hw : c.WF)
    (hi : i < c.n) (h2 : i < (Verify.symsOf c).length)
    (hk : ∃ s : String, s.toUTF8.data.toList = (Verify.symsOf c)[i]) :
    (((Column.get c i).bind fun a => Carrier.of? .symbol (.atom a)).getD d).toUTF8.data.toList = (Verify.symsOf c)[i] := by
  obtain ⟨ty, n, enc, a⟩ := c
  simp only at ht; subst ht
  cases enc with
  | syms b o =>
    rw [show Column.get ⟨.symbol, n, .syms b o, a⟩ i = some (.symbol ((String.fromUTF8? (Column.symKey b o i)).getD ""))
      by simp only [Column.get, if_pos hi]; rfl]
    simp only [Option.bind_some, Carrier.of?, Option.getD_some, Verify.symsOf, List.getElem_map,
      List.getElem_range, Verify.symAt] at hk ⊢
    exact str_bytes hk
  | enum d o ids =>
    rw [show Column.get ⟨.symbol, n, .enum d o ids, a⟩ i = some (.symbol ((String.fromUTF8?
      (Column.symKey d o (Column.idAt ids (Column.idWidth o) i))).getD "")) by simp only [Column.get, if_pos hi]; rfl]
    simp only [Option.bind_some, Carrier.of?, Option.getD_some, Verify.symsOf, List.getElem_map,
      List.getElem_range, Verify.symAt] at hk ⊢
    exact str_bytes hk
  | _ => all_goals first | exact (show False from hw).elim | exact absurd hw.1 (by decide)

/-- Under `wf`, a symbol column whose symbols are UTF-8 lists them: each element's bytes are `symsOf`'s
    symbol at its position, a blob's own or an interned column's dictionary entry. -/
theorem Arr.toList_sym {m : Nat} (x : Arr .symbol m)
    (hu : ∀ k ∈ Verify.symsOf x.c, ∃ s : String, s.toUTF8.data.toList = k) :
    x.toList.map (·.toUTF8.data.toList) = Verify.symsOf x.c := by
  obtain ⟨ht, hn, hw⟩ := x.wf
  have hl : (Verify.symsOf x.c).length = m := by
    refine Eq.trans ?_ hn; revert ht hw; generalize x.c = c; intro ht hw
    obtain ⟨ty, n, enc⟩ := c
    simp only at ht; subst ht
    cases enc <;> simp_all [Column.WF, QAtomicType.width, Verify.symsOf] <;> omega
  refine List.ext_getElem (by rw [List.length_map, Arr.length_toList, hl]) fun i h1 h2 => ?_
  rw [List.length_map, Arr.length_toList] at h1
  rw [List.getElem_map, Arr.getElem_toList, Arr.get_ne x _ (by decide)]
  exact get_sym_bytes _ ht hw (by rw [hn]; exact h1) h2 (hu _ (List.getElem_mem h2))

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
theorem cuts_of_ascending {g n : Nat} (o : Arr .long (g+1)) {b : ByteArray} (hc : o.c.enc = .bytes b)
    (hu : g + 1 < USize.size) (ha : Kernel.Order.ascending .i64 false false (g+1).toUSize b = true)
    (h0 : o.get 0 = 0) (hl : (o.get (Fin.last g)).toInt = n) : Cuts o n := by
  refine ⟨?_, h0, hl⟩
  have hsz : b.size / 8 = g + 1 := Arr.n_long_bytes o hc
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
theorem cuts_get {g n : Nat} {o : Arr .long (g+1)} (co : Cuts o n) {i j : Nat} (hij : i ≤ j) (hj : j ≤ g) :
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
def longBytes (c : Column) : Option ByteArray :=
  match c.enc with
  | .bytes b => some b
  | .foR md pk => some (Kernel.Coc.decode 8 md pk c.n.toUSize)
  | _ => none

/-- The column of a q vector answer. -/
def vecCol : QValue → Option Column
  | .vector c => some c
  | _ => none


/-- Under `Cuts o n`, a position exists only when there is a group to hold it. -/
theorem Cuts.pos {g n : Nat} {o : Arr .long (g+1)} (co : Cuts o n) (i : Fin n) : 0 < g := by
  rcases g with _ | g
  · have h2 := co.2.2; rw [show Fin.last 0 = 0 from rfl, co.2.1] at h2; simp at h2; have := i.2; omega
  · omega

/-- A parted list in its flat form: `n` values cut into `g` groups by the `g+1` offsets `o`. It is the
    kernels' working shape, never a value: `box` turns it into q's nested list, one vector per group. -/
structure Parted (v : QAtomicType) where
  g : Nat
  n : Nat
  o : Arr .long (g+1)
  co : Cuts o n
  val : Arr v n

namespace Parted

variable {v : QAtomicType}

/-- The number of cut points after the first at or below `i`: the largest `r` with `o[r] ≤ i`, which
    under `Cuts` is the group holding `i`. -/
def group {g : Nat} (o : Arr .long (g+1)) (i : Nat) : Nat :=
  (List.finRange g).countP fun r => (o.get r.succ).toInt ≤ i

/-- The group holding position `i`; the `min` is unreachable under `Cuts`, which puts `group o i < g`. -/
def key (P : Parted v) (i : Fin P.n) : Fin P.g := ⟨min (group P.o i) (P.g - 1), by have := P.co.pos i; omega⟩

/-- The pairs `(group, value)` in position order, for proofs only. -/
def toList (P : Parted v) : List (Int64 × El v) := List.ofFn fun i => (Int64.ofNat (P.key i), P.val.get i)

/-- `Parted` built at run time: `Cuts` decided by `Order.ascending` on `o`'s dense payload and one read of
    each end, `cuts_of_ascending` turning the kernel's answer into the proof. `none` when `o` is not cuts of `n`. -/
def of? {g n : Nat} (o : Arr .long (g+1)) (val : Arr v n) : Option (Parted v) := do
  let b ← longBytes o.c
  if h : (Column.WF ⟨.long, g+1, .bytes b, none⟩) ∧ g + 1 < USize.size then
    let ob : Arr .long (g+1) := ⟨⟨.long, g+1, .bytes b, o.c.attr⟩, ⟨rfl, rfl, h.1⟩⟩
    if hc : Kernel.Order.ascending .i64 false false (g+1).toUSize b = true ∧ ob.get 0 = 0 ∧ (ob.get (Fin.last g)).toInt = n then
      some ⟨g, n, ob, cuts_of_ascending ob rfl h.2 hc.1 hc.2.1 hc.2.2, val⟩
    else none
  else none

/-- Group `r`'s values `val[o[r] … o[r+1]-1]` as a q value: `sliceColumn` at an atom type, the
    general list's sub-array otherwise. -/
def slice (P : Parted v) (r : Fin P.g) : Option QValue :=
  let lo := (P.o.get r.castSucc).toNatClampNeg; let hi := (P.o.get r.succ).toNatClampNeg
  match v, P.val.c.enc with
  | .general, .gen xs => some (.general (xs.extract lo hi))
  | .general, _ => none
  | t, _ => Kernel.sliceColumn t P.val.c lo (hi - lo)

/-- q's nested list: one vector per group, each its own slice. -/
def box (P : Parted v) : Except String (Arr .general P.g) := do
  let some xs := (Array.ofFn (P.slice ·)).mapM id | throw "box: sliceColumn declines a group's slice"
  Arr.of .general P.g ⟨.general, xs.size, .gen xs, none⟩ "box"

/-- The parts of a nested list as each part's count and one flat column: `raze` of the vectors at an
    atom type, the concatenated lists at `.general`; a part of another shape is declined. -/
def razeParts : QAtomicType → Array QValue → Except String (Array Nat × Column)
  | .general, xs => do
    let ls ← xs.mapM fun | .general ys _ => pure ys | _ => throw "razeParts: a general part that is not a list"
    let zs := ls.foldl (· ++ ·) #[]
    pure (ls.map (·.size), ⟨.general, zs.size, .gen zs, none⟩)
  | t, xs => do
    let cs ← xs.mapM fun | .vector c => if c.ty == t then pure c else throw "razeParts: a part of another type"
                          | _ => throw "razeParts: a part that is not a vector"
    let some c := (if cs.isEmpty then
        (if h : t = .general then none else Kernel.sliceColumn t (Kernel.nullColumn t h) 0 0)
      else Kernel.razeColumn t cs).bind vecCol
      | throw "razeParts: razeColumn declines the parts"
    pure (cs.map (·.n), c)

/-- The flat form of a nested list of `g` parts at `v`: `razeParts`, the offsets their running counts. -/
def ofBoxes (v : QAtomicType) {g : Nat} (b : Arr .general g) : Except String (Parted v) := do
  let .gen xs := b.c.enc | throw "ofBoxes: a nested list's payload is not .gen"
  let (cnt, c) ← razeParts v xs
  let os := cnt.foldl (fun (s, b) m => (s + m, Column.pushBits b (Int64.ofNat (s + m)).toUInt64 8)) (0, Column.pushBits .empty 0 8)
  let o ← Arr.of .long (g+1) ⟨.long, g+1, .bytes os.2, none⟩ "ofBoxes"
  let val ← Arr.of v os.1 c "ofBoxes"
  let some P := of? o val | throw "ofBoxes: the running counts are not cuts"
  pure P

end Parted

/-- A relation from `k` to `v`: `n` positions, a key and a value at each — q's dict, two arrays. -/
structure Rel (k v : QAtomicType) where
  n : Nat
  key : Arr k n
  val : Arr v n

namespace Rel

variable {k v : QAtomicType}

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


private def l3 : Arr .long 3 := { c := ⟨.long, 3, .bytes <| packLongs [7, -1, 42], none⟩, wf := by decide }
#guard l3.toList == [7, -1, 42]

private def bs : Arr .boolean 3 := { c := ⟨.boolean, 3, .bits (ByteArray.mk #[0b101]), none⟩, wf := by decide }
#guard bs.toList == [true, false, true]

-- one symbol column, as `syms` and as `enum` over the dictionary `a, bc`
private def blob : ByteArray := ByteArray.mk #[97, 0, 98, 99, 0]
private def ss : Arr .symbol 3 :=
  { c := ⟨.symbol, 3, .syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8], none⟩, wf := by decide }
private def es : Arr .symbol 3 :=
  { c := ⟨.symbol, 3, .enum blob #[0, 2, 5] (packIds (idWidth #[0, 2, 5]) 3 fun i => [1, 0, 1][i]!), none⟩, wf := by decide }
#guard ss.toList == ["bc", "a", "bc"]
#guard es.toList == ss.toList

private def gs : Arr .general 2 := { c := ⟨.general, 2, .gen #[(.atom (.long 1) : QValue), (.general #[] : QValue)], none⟩, wf := ⟨rfl, rfl, rfl⟩ }
#guard match id (α := QValue) (gs.get 0), id (α := QValue) (gs.get 1) with | .atom (.long 1), .general #[] _ => true | _, _ => false

-- groups `[0,1) [1,1) [1,3)`: the empty middle group owns no position
private def o3 : Arr .long 4 := { c := ⟨.long, 4, .bytes <| packLongs [0, 1, 1, 3], none⟩, wf := by decide }
-- the parted list `(10 20; 30)`: positions `0 1 | 2`, groups `0 0 1`
private def o2 : Arr .long 3 := { c := ⟨.long, 3, .bytes <| packLongs [0, 2, 3], none⟩, wf := by decide }
private def v3 : Arr .long 3 := { c := ⟨.long, 3, .bytes <| packLongs [10, 20, 30], none⟩, wf := by decide }
-- `of?` decides `Cuts` at run time, on `bytes` and on `foR` offsets; the `foR` header is decided too
private def o3f : Except String (Arr .long 4) :=
  Arr.of .long 4 ⟨.long, 4, .foR (Kernel.Coc.encode 8 (packLongs [0, 1, 1, 3])).1
      (Kernel.Coc.encode 8 (packLongs [0, 1, 1, 3])).2, none⟩ "o3f"
#guard match o3f with
  | .ok o3f => [o3, o3f].all fun o => ((Parted.of? o v3).map Parted.toList) == some [(0, 10), (2, 20), (2, 30)]
  | .error _ => false
#guard ((Parted.of? o2 v3).map Parted.toList) == some [(0, 10), (0, 20), (1, 30)]
#guard (Parted.of? o2 ({ c := ⟨.long, 2, .bytes <| packLongs [10, 20], none⟩, wf := by decide } : Arr .long 2)).isNone
#guard (Parted.of? ({ c := ⟨.long, 3, .bytes <| packLongs [0, 2, 1], none⟩, wf := by decide } : Arr .long 3) v3).isNone
#guard (Parted.of? ({ c := ⟨.long, 3, .bytes <| packLongs [1, 2, 3], none⟩, wf := by decide } : Arr .long 3) v3).isNone
-- `box` then `ofBoxes` is the identity on the flat form, and each box is q's vector of its slice
#guard match Parted.of? o3 v3 with
  | some P => match P.box with
    | .ok b => (match (b.toList[1]? : Option QValue) with | some (.vector c) => c.ty == .long && c.n == 0 | _ => false) &&
        match Parted.ofBoxes .long b with | .ok Q => Q.toList == P.toList | .error _ => false
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
