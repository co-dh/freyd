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
import QLean.Kernel.Elementwise
import QLean.Kernel.Scan
import QLean.Verify.Encoding
import QLean.Verify.SymFind
import QLean.Verify.Alp

namespace LeetQ.Rel

open QLean QLean.Dep

/-- An element of a column of type `t`: qlean's `Carrier`, a `QValue` in a general list. -/
abbrev El := Carrier

/-- A vector of `n` elements of type `t`: qlean's typed vector, `QValue.WFAt` saying the header is `t`, `n`
    and `Enc.WF` that the payload agrees with it; a general list is `.gen xs`. q's attribute is the vector's
    own (codes 1 sorted, 2 unique, 3 parted, 4 grouped, with the `IndexCell` of its index), set by producers
    and read by consumers (§2.4). -/
abbrev Arr (t : QAtomicType) (n : USize) := {v : QValue // v.WFAt t n}

namespace Arr

variable {t : QAtomicType} {n : USize}

/-- The payload. The fallback is unreachable: `WFAt` holds only of a `vector`. -/
def enc (x : Arr t n) : Enc := match x.1 with | .vector _ _ e _ => e | _ => .gen #[]

/-- The attribute and index cell, `QValue.attrCell` of the vector. -/
def attrCell (x : Arr t n) : Option (UInt8 × IndexCell) := match x.1 with | .vector _ _ _ a => a | _ => none

/-- The payload agrees with the header. -/
theorem wf (x : Arr t n) : Enc.WF t n x.enc := by
  obtain ⟨v, h⟩ := x; cases v <;> first | exact h.2.2 | exact h.elim

-- Kept with no caller: the specification of `Arr` as a `List`, `Arr` the implementation, `List` for proofs.
/-- The vector is its header, its payload and its attribute: what a kernel matching `.vector t n e a` sees. -/
theorem val_eq (x : Arr t n) : x.1 = .vector t n x.enc x.attrCell := by
  obtain ⟨v, h⟩ := x; cases v <;> first | exact h.elim | (obtain ⟨rfl, rfl, -⟩ := h; rfl)

/-- `e` under the header `t`, `n` and the attribute `a`. -/
def mk (e : Enc) (h : Enc.WF t n e) (a : Option (UInt8 × IndexCell) := none) : Arr t n := ⟨.vector t n e a, rfl, rfl, h⟩

/-- A general list's payload is `gen` and holds its `n` elements. -/
theorem gen_size (x : Arr .general n) {xs : Array QValue} (hc : x.enc = .gen xs) : xs.size = n.toNat := by
  have hw := x.wf; rw [hc] at hw; exact hw

/-- Element `i`. At an atom type it is `Enc.get`'s atom at `i` read back at the index; the
    fallback, the atom of zero bits, is unreachable under `wf`, as is the general list's non-`gen` one. -/
def get (x : Arr t n) (i : Fin n.toNat) : El t :=
  match t, x with
  | .general, x => match hc : x.enc with
    | .gen xs => xs[i.1]'(by rw [gen_size x hc]; exact i.2)
    | _ => QValue.general #[] 0
  | t, x => ((Enc.get t n x.enc i).bind fun a => Carrier.of? t (.atom a)).getD default

/-- `get` at an atom type: `Enc.get`'s atom read back at `t`. -/
theorem get_ne (x : Arr t n) (i : Fin n.toNat) (h : t ≠ .general) :
    x.get i = ((Enc.get t n x.enc i).bind fun a => Carrier.of? t (.atom a)).getD default := by
  cases t <;> first | exact absurd rfl h | rfl

/-- The elements in position order, for proofs only. -/
def toList (x : Arr t n) : List (El t) := List.ofFn x.get

theorem length_toList (x : Arr t n) : x.toList.length = n.toNat := List.length_ofFn

-- Kept with no caller: the specification of `Arr` as a `List`, `Arr` the implementation, `List` for proofs.
theorem getElem_toList (x : Arr t n) (i : Nat) (h : i < x.toList.length) :
    x.toList[i] = x.get ⟨i, by rw [length_toList] at h; exact h⟩ := List.getElem_ofFn ..

/-- The list as a relation from its positions: `x i y ↔ x[j] = y` at the `j` with `Int64.ofNat j = i`. -/
def Holds (x : Arr t n) (i : Int64) (y : El t) : Prop := ∃ j : Fin n.toNat, Int64.ofNat j = i ∧ x.get j = y

theorem holds_iff_mem_zipIdx (x : Arr t n) (i : Int64) (y : El t) :
    x.Holds i y ↔ ∃ j, Int64.ofNat j = i ∧ (y, j) ∈ x.toList.zipIdx := by
  simp only [Holds, List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff, length_toList]
  constructor
  · rintro ⟨j, rfl, rfl⟩; exact ⟨j, rfl, j.2, by rw [getElem_toList]⟩
  · rintro ⟨j, rfl, h, rfl⟩; exact ⟨⟨j, h⟩, rfl, by rw [getElem_toList]⟩

/-- A kernel's answer as an `Arr`, the one way in: `WFAt` is decided (the header's two fields and
    `Enc.WF`), never assumed; `what` names the producer in the error. The vector is the kernel's, mark
    and all; a producer that knows an attribute applies it after. -/
def of (t : QAtomicType) (n : USize) (v : QValue) (what : String) : Except String (Arr t n) :=
  match v with
  | .vector t' n' e a => if h : t' = t ∧ n' = n ∧ Enc.WF t n e then .ok ⟨.vector t' n' e a, h⟩
    else .error s!"{what}: the kernel answered a payload that is not {n} well-formed elements of its type"
  | _ => .error s!"{what}: the kernel answered a value that is not a vector"

end Arr

/-- The group holding each of `n` positions under the offsets `o`: the last cut at or below it, `o bin til n`
    (`binBytes`). -/
def groupOf (o : ByteArray) (n : USize) : ByteArray := Kernel.binBytes 8 false true false o (Kernel.tilLongs n)

/-- `xs` as a dense long payload, eight bytes each: the literal columns of every module's checks. -/
def packLongs (xs : List Int64) : ByteArray := xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty

theorem packLongs_size (xs : List Int64) : (packLongs xs).size = 8 * xs.length := by
  suffices ∀ b : ByteArray, (xs.foldl (fun b x => Column.pushBits b x.toUInt64 8) b).size = b.size + 8 * xs.length by
    simpa [packLongs] using this .empty
  induction xs with
  | nil => simp
  | cons x xs ih => intro b; rw [List.foldl_cons, ih, Column.pushBits_size, List.length_cons]; omega

/-- The column of `f` at the positions `0 … n-1`, packed by Lean with no kernel and no `List`: the reference
    beside a kernel whose count is checked. -/
def colFn (n : USize) (f : Fin n.toNat → Int64) : Arr .long n :=
  Arr.mk (.bytes ((Array.ofFn f).foldl (fun b x => Column.pushBits b x.toUInt64 8) .empty)) (by
    show _ = n.toNat * 8; rw [← Array.foldl_toList]
    show (packLongs (Array.ofFn f).toList).size = n.toNat * 8; rw [packLongs_size]; simp [Nat.mul_comm])

/-- `xs` Frame-of-Reference encoded is well formed at its count `n`: the checks' `foR` columns, which
    `decide` cannot evaluate through `Coc.encode`. -/
theorem foRLongs_wf (xs : List Int64) {n : USize} (hn : xs.length = n.toNat) : Enc.WF .long n
    (.foR (Kernel.Coc.encode 8 (packLongs xs)).1 (Kernel.Coc.encode 8 (packLongs xs)).2) := by
  have h := Verify.nblk_encode 8 (by decide) (by decide) (packLongs xs)
  rw [packLongs_size] at h
  refine ⟨rfl, by simp, by simp, ?_⟩
  show n.toNat ≤ Column.blk * Column.nblk (Kernel.Coc.encode (8 : Nat).toUSize (packLongs xs)).1
  rw [h, ← hn]; simp only [Column.blk]; omega

/-- Under `wf`, a long `bytes` column holds `b.size / 8` elements. -/
theorem Arr.n_long_bytes {m : USize} (x : Arr .long m) {b : ByteArray} (hc : x.enc = .bytes b) :
    b.size / 8 = m.toNat := by
  have hw := x.wf
  simp only [Enc.WF, hc, QAtomicType.width] at hw; omega

/-- Under `wf`, a long `bytes` column's element `i` is the eight bytes at `8i`, read as a long. -/
theorem Arr.get_long_bytes {m : USize} (x : Arr .long m) {b : ByteArray} (hc : x.enc = .bytes b) (i : Fin m.toNat) :
    x.get i = (Column.bitsAt b (i.1 * 8) 8).toInt64 := by
  rw [Arr.get_ne x i (by decide)]
  simp only [Enc.get, if_pos i.2, hc, QAtomicType.width]; rfl

-- Kept with no caller: the specification of `Arr` as a `List`, per payload form, `List` for proofs.
/-- Under `wf`, a long `bytes` column lists its eight-byte words, each read as a long. -/
theorem Arr.toList_long_bytes {m : USize} (x : Arr .long m) {b : ByteArray} (hc : x.enc = .bytes b) :
    x.toList = ((List.range m.toNat).map fun i => Column.bitsAt b (i * 8) 8).map UInt64.toInt64 := by
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
theorem Arr.get_long_foR {m : USize} (x : Arr .long m) {md pk : ByteArray} (hc : x.enc = .foR md pk)
    (i : Fin m.toNat) : x.get i = (Column.foRBits md pk (Column.blockStarts md) i.1).toInt64 := by
  rw [Arr.get_ne x i (by decide), ← foRBits_starts]
  simp only [Enc.get, if_pos i.2, hc, QAtomicType.width]; rfl

/-- A long payload's `n` words in position order: a `bytes` payload's eight-byte elements, a `foR` payload's
    `foRBits` decode. `none` at `alp`, whose decode has no law yet, and at the non-long constructors. -/
def longWords (n : USize) (e : Enc) : Option (List UInt64) :=
  match e with
  | .bytes b => some (Verify.elemsW 8 b)
  | .foR md pk => some ((List.range n.toNat).map (Column.foRBits md pk (Column.blockStarts md)))
  | _ => none

/-- Under `wf`, a long column lists its words, each read as a long: `toList_long_bytes` and the `foR` decode. -/
theorem Arr.toList_long {m : USize} (x : Arr .long m) {ws : List UInt64} (h : longWords m x.enc = some ws) :
    x.toList = ws.map UInt64.toInt64 := by
  unfold longWords at h
  cases hc : x.enc with
  | bytes b => rw [hc] at h; cases h; rw [Arr.toList_long_bytes x hc, Verify.elemsW, Arr.n_long_bytes x hc]
  | foR md pk =>
    rw [hc] at h; cases h
    apply List.ext_getElem (by rw [Arr.length_toList]; simp)
    intro i h1 h2; rw [Arr.getElem_toList, Arr.get_long_foR x hc]; simp
  | _ => all_goals (rw [hc] at h; cases h)

/-- Element `i` of a long column is word `i`, read as a long. -/
theorem Arr.get_long {m : USize} (x : Arr .long m) {ws : List UInt64} (h : longWords m x.enc = some ws)
    (i : Nat) (hi : i < m.toNat) (hw : i < ws.length) : x.get ⟨i, hi⟩ = ws[i].toInt64 := by
  rw [← Arr.getElem_toList x i (by rw [Arr.length_toList]; exact hi)]
  simp [Arr.toList_long x h]

/-- The dense payload a kernel reads off a long column that lists `longWords`: a `bytes` payload is
    itself, a `foR` one is handed over or decoded (`decodeW`) to the same words. -/
theorem Arr.dense_long {m : USize} (x : Arr .long m) {ws : List UInt64} (h : longWords m x.enc = some ws) :
    ∃ B, (x.enc = .bytes B ∨ ∃ md pk, x.enc = .foR md pk ∧
      B = Kernel.Coc.decode (8 : Nat).toUSize md pk m) ∧ Enc.bytesOf .long m x.enc = some B ∧
      Verify.elemsW 8 B = ws ∧ B.size / 8 = m.toNat := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  unfold longWords at h
  cases hc : x.enc with
  | bytes b =>
    rw [hc] at h; cases h
    exact ⟨b, .inl rfl, by simp only [Enc.bytesOf], rfl, Arr.n_long_bytes x hc⟩
  | foR md pk =>
    rw [hc] at h; cases h
    obtain ⟨hsz, hg⟩ := Verify.decodeW (8 : Nat).toUSize (by rw [h8]; decide) md pk m
    rw [h8] at hsz hg
    refine ⟨_, .inr ⟨md, pk, rfl, rfl⟩, by simp only [Enc.bytesOf, QAtomicType.width]; rfl,
      List.ext_getElem (by simp [Verify.elemsW, hsz]) fun i h1 _ => ?_, by rw [hsz]; omega⟩
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [hg i (by simpa [Verify.elemsW, hsz] using h1), Verify.ofNat_toNat_mod64]
  | _ => all_goals (rw [hc] at h; cases h)

/-- A dense long answer lists its words whichever form `Enc.answer` leaves it in: dense, or encoded
    (`foRBits_encode_bits`). -/
theorem longWords_answer {m : USize} (b : ByteArray) (hm : b.size / 8 = m.toNat) :
    longWords m (Enc.answer .long m (.bytes b)) = some (Verify.elemsW 8 b) := by
  have ha : Enc.answer .long m (.bytes b) = .bytes b ∨
      Enc.answer .long m (.bytes b) =
      .foR (Kernel.Coc.encode (8 : Nat).toUSize b).1 (Kernel.Coc.encode (8 : Nat).toUSize b).2 := by
    simp only [Enc.answer, QAtomicType.width, show Column.alpEncodes .long = false from rfl,
      show Column.encodes .long = true from rfl, Kernel.Coc.encodeBelow]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  unfold longWords
  rcases ha with e | e
  · rw [e]
  · rw [e]; simp only [Verify.elemsW, ← hm]
    refine congrArg some (List.map_congr_left fun i hi => UInt64.toNat_inj.1 ?_)
    rw [← Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
    exact Verify.foRBits_encode_bits 8 (by decide) (by decide) b i (List.mem_range.1 hi)

/-- `alpBits` with no hoisted table reads the start `blockStarts` holds, as `foRBits_starts`. -/
theorem alpBits_starts (md pk a : ByteArray) (i : Nat) :
    Column.alpBits md pk a #[] i = Column.alpBits md pk a (Column.blockStarts md) i := by
  unfold Column.alpBits; rw [foRBits_starts]

/-- A float column's words in position order, the bits each `float` holds: a `bytes` payload's eight-byte
    elements, an `alp` payload's `alpBits` decode. -/
def floatWords (n : USize) (e : Enc) : Option (List UInt64) :=
  match e with
  | .bytes b => some (Verify.elemsW 8 b)
  | .alp md pk a => some ((List.range n.toNat).map (Column.alpBits md pk a (Column.blockStarts md)))
  | _ => none

/-- Under `wf`, a float column lists its words. -/
theorem Arr.toList_float {m : USize} (x : Arr .float m) {ws : List UInt64} (h : floatWords m x.enc = some ws) :
    x.toList = ws := by
  unfold floatWords at h
  cases hc : x.enc with
  | bytes b =>
    rw [hc] at h; cases h
    have hb : b.size / 8 = m.toNat := by
      have hw := x.wf; simp only [Enc.WF, hc, QAtomicType.width] at hw; omega
    apply List.ext_getElem (by rw [Arr.length_toList, Verify.elemsW, List.length_map, List.length_range, hb])
    intro i h1 h2
    rw [Arr.length_toList] at h1
    rw [Arr.getElem_toList, Arr.get_ne x _ (by decide)]
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range, Enc.get, if_pos h1, hc, QAtomicType.width]
    rfl
  | alp md pk a =>
    rw [hc] at h; cases h
    apply List.ext_getElem (by rw [Arr.length_toList]; simp)
    intro i h1 h2
    rw [Arr.length_toList] at h1
    rw [Arr.getElem_toList, Arr.get_ne x _ (by decide)]
    simp only [List.getElem_map, List.getElem_range, Enc.get, if_pos h1, hc, QAtomicType.width, alpBits_starts]
    rfl
  | _ => all_goals (rw [hc] at h; cases h)

/-- The dense payload a kernel reads off a float column that lists `floatWords`: a `bytes` payload is
    itself, an `alp` one is decoded (`alpDecode64`) to the same words. -/
theorem Arr.dense_float {m : USize} (x : Arr .float m) {ws : List UInt64} (h : floatWords m x.enc = some ws) :
    ∃ B, (x.enc = .bytes B ∨ ∃ md pk a, x.enc = .alp md pk a ∧
      B = Kernel.Coc.alpDecode64 md pk a m) ∧ Verify.elemsW 8 B = ws ∧ B.size / 8 = m.toNat := by
  unfold floatWords at h
  cases hc : x.enc with
  | bytes b =>
    rw [hc] at h; cases h
    have hw := x.wf
    simp only [Enc.WF, hc, QAtomicType.width] at hw
    exact ⟨b, .inl rfl, rfl, by omega⟩
  | alp md pk a =>
    rw [hc] at h; cases h
    have e : Verify.elemsW 8 (Kernel.Coc.alpDecode64 md pk a m) =
        (Kernel.Coc.alpElems md pk a m).map fun v => UInt64.ofNat (v.toNat % 2 ^ (8 * 8)) :=
      Verify.elemsW_foldl_mod id 8 (by decide) (by decide) _
    rw [Kernel.Coc.alpElems, List.map_map, show 8 * 8 = 64 from rfl] at e
    refine ⟨_, .inr ⟨md, pk, a, rfl, rfl⟩, ?_, ?_⟩
    · rw [e]; exact List.map_congr_left fun i _ => Verify.ofNat_toNat_mod64 _
    · have := congrArg List.length e
      simpa [Verify.elemsW] using this
  | _ => all_goals (rw [hc] at h; cases h)

/-- A dense float answer lists its words whichever form `Enc.answer` leaves it in: dense, or ALP
    encoded (`alpBits_alpEncodeAt`, below `2³²` elements). -/
theorem floatWords_answer {m : USize} (b : ByteArray) (h32 : b.size / 8 < 2 ^ 32) (hm : b.size / 8 = m.toNat) :
    floatWords m (Enc.answer .float m (.bytes b)) = some (Verify.elemsW 8 b) := by
  have ha : Enc.answer .float m (.bytes b) = .bytes b ∨
      Enc.answer .float m (.bytes b) =
      .alp (Kernel.Coc.alpEncode64 b).1 (Kernel.Coc.alpEncode64 b).2.1 (Kernel.Coc.alpEncode64 b).2.2 := by
    simp only [Enc.answer, QAtomicType.width, show Column.alpEncodes .float = true from rfl,
      Kernel.Coc.alpEncodeBelow64]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  unfold floatWords
  rcases ha with e | e
  · rw [e]
  · rw [e]; simp only [Verify.elemsW, ← hm]
    exact congrArg some (List.map_congr_left fun i hi => (Verify.alpBits_alpEncodeAt false 8 rfl b h32).2 i (List.mem_range.1 hi))

/-- An `int` answer column, dense or encoded, lists its payload's four-byte words: `longWords_answer` at
    width four, the `foR` form read back by `foRBits_encode_bits`. -/
theorem toList_answer_int {m : USize} (x : Arr .int m) {b : ByteArray} (hm : b.size / 4 = m.toNat)
    (hc : x.enc = Enc.answer .int m (.bytes b)) :
    x.toList = (List.range m.toNat).map fun i => (Column.bitsAt b (i * 4) 4).toUInt32.toInt32 := by
  have ha : Enc.answer .int m (.bytes b) = .bytes b ∨
      Enc.answer .int m (.bytes b) =
      .foR (Kernel.Coc.encode (4 : Nat).toUSize b).1 (Kernel.Coc.encode (4 : Nat).toUSize b).2 := by
    simp only [Enc.answer, QAtomicType.width, show Column.alpEncodes .int = false from rfl,
      show Column.encodes .int = true from rfl, Kernel.Coc.encodeBelow]
    repeat' split
    all_goals first | exact .inl rfl | exact .inr rfl | simp_all
  apply List.ext_getElem (by rw [Arr.length_toList]; simp)
  intro i h1 _
  have hn : i < m.toNat := by rw [Arr.length_toList] at h1; omega
  rw [Arr.getElem_toList, List.getElem_map, List.getElem_range, Arr.get_ne x _ (by decide)]
  rw [← hc] at ha
  rcases ha with e | e <;> simp only [Enc.get, if_pos hn, e, QAtomicType.width]
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
theorem Arr.get_bool_bits {m : USize} (x : Arr .boolean m) {b : ByteArray} (hc : x.enc = .bits b)
    (i : Fin m.toNat) : x.get i = Column.bitAt b i.1 := by
  rw [Arr.get_ne x i (by decide)]
  simp only [Enc.get, if_pos i.2, hc]; rfl

/-- The `str` bridge: bytes that are some string's UTF-8, read as a string the way `Column.get` reads a
    symbol (`fromUTF8?`, `""` at invalid bytes), write back out as themselves. -/
theorem str_bytes {B : ByteArray} (h : ∃ s : String, s.toUTF8.data.toList = B.data.toList) :
    ((String.fromUTF8? B).getD "").toUTF8.data.toList = B.data.toList := by
  obtain ⟨s, hs⟩ := h
  obtain rfl : s.toByteArray = B := ByteArray.ext (Array.ext' hs)
  simp only [String.fromUTF8?, s.isValidUTF8, dite_true, Option.getD_some]
  rfl

/-- A symbol payload's element `i`, read as `Enc.get` reads it, writes out as `symsOf`'s symbol `i`
    wherever that symbol is UTF-8. -/
theorem get_sym_bytes {n : USize} {e : Enc} {i : Nat} (d : String) (hw : Enc.WF .symbol n e)
    (hi : i < n.toNat) (h2 : i < (Verify.symsOf n.toNat e).length)
    (hk : ∃ s : String, s.toUTF8.data.toList = (Verify.symsOf n.toNat e)[i]) :
    (((Enc.get .symbol n e i).bind fun a => Carrier.of? .symbol (.atom a)).getD d).toUTF8.data.toList = (Verify.symsOf n.toNat e)[i] := by
  cases e with
  | syms b o =>
    rw [show Enc.get .symbol n (.syms b o) i = some (.symbol ((String.fromUTF8? (Column.symKey b o i)).getD ""))
      by simp only [Enc.get, if_pos hi]; rfl]
    simp only [Option.bind_some, Carrier.of?, Option.getD_some, Verify.symsOf, List.getElem_map,
      List.getElem_range, Verify.symAt] at hk ⊢
    exact str_bytes hk
  | enum d o ids =>
    rw [show Enc.get .symbol n (.enum d o ids) i = some (.symbol ((String.fromUTF8?
      (Column.symKey d o (Column.idAt ids (Column.idWidth o) i))).getD "")) by simp only [Enc.get, if_pos hi]; rfl]
    simp only [Option.bind_some, Carrier.of?, Option.getD_some, Verify.symsOf, List.getElem_map,
      List.getElem_range, Verify.symAt] at hk ⊢
    exact str_bytes hk
  | _ => all_goals first | exact (show False from hw).elim | exact absurd hw.1 (by decide)

/-- Under `wf`, a symbol column whose symbols are UTF-8 lists them: each element's bytes are `symsOf`'s
    symbol at its position, a blob's own or an interned column's dictionary entry. -/
theorem Arr.toList_sym {m : USize} (x : Arr .symbol m)
    (hu : ∀ k ∈ Verify.symsOf m.toNat x.enc, ∃ s : String, s.toUTF8.data.toList = k) :
    x.toList.map (·.toUTF8.data.toList) = Verify.symsOf m.toNat x.enc := by
  have hw := x.wf
  have hl : (Verify.symsOf m.toNat x.enc).length = m.toNat := by
    revert hw; generalize x.enc = e; intro hw
    cases e <;> simp_all [Enc.WF, QAtomicType.width, Verify.symsOf] <;> omega
  refine List.ext_getElem (by rw [List.length_map, Arr.length_toList, hl]) fun i h1 h2 => ?_
  rw [List.length_map, Arr.length_toList] at h1
  rw [List.getElem_map, Arr.getElem_toList, Arr.get_ne x _ (by decide)]
  exact get_sym_bytes _ hw h1 h2 (hu _ (List.getElem_mem h2))

/-- A long payload as dense bytes: `bytes` as it is, `foR` decoded once (`Coc.decode`). -/
def longBytes (n : USize) (e : Enc) : Option ByteArray :=
  match e with
  | .bytes b => some b
  | .foR md pk => some (Kernel.Coc.decode 8 md pk n)
  | _ => none

/-- A side of a relation: an atomic type, a product of sides, or an array of a side. A tree, so
    `Vals (.atom t)` is `Arr t` itself and every one-column path is unchanged. A `arr b` element is an
    ARRAY of `b`: its order and multiplicity are part of the value. -/
inductive Obj
  | atom (t : QAtomicType)
  | prod (a b : Obj)
  | arr (b : Obj)
  | sum (a b : Obj)

instance : Coe QAtomicType Obj := ⟨.atom⟩

/-- The atoms the verbs name, so `.long` reads the same at `Obj` as at `QAtomicType`. -/
@[match_pattern, reducible] def Obj.long : Obj := .atom .long
@[match_pattern, reducible] def Obj.general : Obj := .atom .general

/-- An element of a side: a tuple of its atoms' elements. -/
@[reducible] def Obj.El : Obj → Type
  | .atom t => Carrier t
  | .prod a b => a.El × b.El
  | .arr b => List b.El
  | .sum a b => Sum a.El b.El

/-- The element a row reads where its side holds no value at all (a side of `0` values), the one position no
    clamp can land in: what a gather past the side reads — an atom's `default` (q's null), an empty array, a
    sum's `inl` of its left side's own. -/
def Obj.dflt : (A : Obj) → A.El
  | .atom _ => default
  | .prod a b => (a.dflt, b.dflt)
  | .arr _ => []
  | .sum a _ => .inl a.dflt

/-- `n` values of `A`, one column per atom, side by side (struct of arrays): nothing boxed. A `arr b`
    column is one flat payload of `m` values of `b` and two long columns `lo`, `hi`: row `i` is the slice
    `[lo i, hi i)` of the payload, so picking rows gathers `lo` and `hi` and copies no flat value. A `sum a b`
    column is a tag and a position per row into one of two payloads, `l` values of `a` (tag `false`) and `r`
    of `b` (tag `true`): picking rows gathers the tag and the position and copies no value. -/
@[reducible] def Vals : Obj → USize → Type
  | .atom t, n => Arr t n
  | .prod a b, n => Vals a n × Vals b n
  | .arr b, n => (m : USize) × Arr .long n × Arr .long n × Vals b m
  | .sum a b, n => (l : USize) × (r : USize) × Arr .boolean n × Arr .long n × Vals a l × Vals b r

/-- The position `k` clamped into `[0, m)`: the nearest position of a side of `m > 0` values. -/
def clampFin (k : Int64) (m : Nat) (h : 0 < m) : Fin m :=
  ⟨min (max k.toInt 0).toNat (m - 1), Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

/-- The value at row `i`, read across the columns. An array row is its slice clamped to `[0, m)`, so every
    `lo`, `hi` reads as an array. A sum row is its side's value at its position clamped into the side, so
    every position reads as a value of its side; a side of no values reads that side's `Obj.dflt`, the null a
    gather past the side reads, so the row keeps its tag. -/
def Vals.row : {A : Obj} → {n : USize} → Vals A n → Fin n.toNat → A.El
  | .atom _, _, x, i => Arr.get x i
  | .prod _ _, _, x, i => (Vals.row x.1 i, Vals.row x.2 i)
  | .arr _, _, ⟨m, lo, hi, f⟩, i => (List.finRange m.toNat).filterMap fun (j : Fin m.toNat) =>
      if (lo.get i).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (hi.get i).toInt then some (Vals.row f j) else none
  | .sum a b, _, ⟨l, r, tag, idx, x, y⟩, i =>
    if tag.get i then .inr (if h : 0 < r.toNat then Vals.row y (clampFin (idx.get i) r.toNat h) else b.dflt)
    else .inl (if h : 0 < l.toNat then Vals.row x (clampFin (idx.get i) l.toNat h) else a.dflt)

-- Kept with no caller: an atom side's row is the `Arr`'s element, the `List` reading of a side.
@[simp] theorem Vals.row_atom {t : QAtomicType} {n : USize} (x : Arr t n) (i : Fin n.toNat) :
    Vals.row (A := .atom t) x i = x.get i := rfl

/-- A relation from `k` to `v`: `n` positions, a key and a value at each — q's dict, two arrays at atoms,
    one column per atom of a product side, so `B×C` stored as two columns IS one side of pairs. -/
structure Rel (k v : Obj) where
  n : USize
  key : Vals k n
  val : Vals v n

namespace Rel

variable {k v : Obj}

/-- The relation `R` denotes: `R x y ↔ ∃ i, key.row i = x ∧ val.row i = y`. -/
def Holds (R : Rel k v) (x : k.El) (y : v.El) : Prop := ∃ i, R.key.row i = x ∧ R.val.row i = y

/-- The pairs, in position order, for proofs only. -/
def toList (R : Rel k v) : List (k.El × v.El) := List.ofFn fun i => (R.key.row i, R.val.row i)

-- Kept with no caller: what a `Rel` holds, read off its `List` of pairs.
theorem holds_iff_mem_toList (R : Rel k v) (x : k.El) (y : v.El) : R.Holds x y ↔ (x, y) ∈ R.toList := by
  simp [Holds, toList, List.mem_ofFn]

end Rel

/-! ## Payload helpers on qlean kernels -/

section Payload

open QLean.Kernel

/-- One long as an eight-byte payload: the atom operand of an `av`/`va` kernel call. -/
def one (v : UInt64) : ByteArray := Column.pushBits .empty v 8

theorem bitsAt_one (v : UInt64) : Column.bitsAt (one v) 0 8 = v := by
  simpa using Verify.bitsAt_pushBits8 ByteArray.empty v

/-- q's `where` on a dense count column `cnt` (none negative): row `i` repeated `cnt[i]` times, and each
    copy's rank in its run — `expandBytes` of `til n` by the counts, then the output position less its
    run's start (`Scan.scan sums` less the count). One linear pass, where bisecting the outputs into the
    run starts (`binBytes`) was `O(m log n)`. -/
def expand (cnt : ByteArray) : ByteArray × ByteArray :=
  needSize (cnt.size / 8) "expand: the counts" (fun _ => (.empty, .empty)) fun n =>
  let rs := Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue (Scan.scan .sums .i64 n cnt) cnt n
  let i := expandBytes 8 0 (tilLongs n) cnt
  needSize (i.size / 8) "expand: the copies" (fun _ => (.empty, .empty)) fun m =>
  (i, Ew.val Ew.sub Ew.i64 Ew.vv Int64.minValue (tilLongs m) (gatherBytes 8 0 rs i) m)

/-- `~` on `m` bits: `Ew.bit` xor a ones mask, the mask a one-bit atom in shape `av` (xor is `≠` on bits). -/
def Ew.notBits (m : USize) (b : ByteArray) : ByteArray := Ew.bit (Ew.bitCmp + Ew.ne) Ew.av ⟨#[1]⟩ b m

end Payload

/-! ## Sanity checks on small literal columns -/

section Checks

open QLean.Column


private def l3 : Arr .long 3 := Arr.mk (.bytes <| packLongs [7, -1, 42]) (by unfold Enc.WF; simp only [USize.reduceToNat, QAtomicType.width]; decide)
#guard l3.toList == [7, -1, 42]

private def bs : Arr .boolean 3 := Arr.mk (.bits (ByteArray.mk #[0b101])) (by unfold Enc.WF; simp only [USize.reduceToNat, QAtomicType.width]; decide)
#guard bs.toList == [true, false, true]

-- one symbol column, as `syms` and as `enum` over the dictionary `a, bc`
private def blob : ByteArray := ByteArray.mk #[97, 0, 98, 99, 0]
private def ss : Arr .symbol 3 := Arr.mk (.syms (ByteArray.mk #[98, 99, 0, 97, 0, 98, 99, 0]) #[0, 3, 5, 8]) (by unfold Enc.WF; simp only [USize.reduceToNat, QAtomicType.width]; decide)
private def es : Arr .symbol 3 :=
  Arr.mk (.enum blob #[0, 2, 5] (packIds (idWidth #[0, 2, 5]) 3 fun i => [1, 0, 1][i]!)) (by unfold Enc.WF; simp only [USize.reduceToNat, QAtomicType.width]; decide)
#guard ss.toList == ["bc", "a", "bc"]
#guard es.toList == ss.toList

private def gs : Arr .general 2 := Arr.mk (.gen #[(.atom (.long 1) : QValue), (.general #[] 0 : QValue)]) (by unfold Enc.WF; simp only [USize.reduceToNat]; rfl)
#guard match id (α := QValue) (gs.get ⟨0, by simp⟩), id (α := QValue) (gs.get ⟨1, by simp⟩) with | .atom (.long 1), .general #[] _ _ => true | _, _ => false

#guard ss.toList.zipIdx == [("bc", 0), ("a", 1), ("bc", 2)]
example : ss.Holds 1 "a" := ⟨⟨1, by simp⟩, rfl, by simp only [Arr.get_ne _ _ (show QAtomicType.symbol ≠ .general by decide), Enc.get, USize.reduceToNat]; decide⟩

end Checks

#print axioms Arr.get
#print axioms Rel.holds_iff_mem_toList

end LeetQ.Rel
