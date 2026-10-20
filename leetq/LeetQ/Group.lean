/-
  q's `where`, `distinct` and `group` over qlean's `long` columns, each specified by a relation and
  implemented by the qlean kernel (`whereBits`, `Order.distinct`/`distinctFoR`, `Order.group`/`groupFoR`),
  whose Lean body is what every theorem here reads. With `f = ix(xs) : Idx ⟶ Int64` the column:
  * a `bits` column is the coreflexive `p?` of the bit predicate, `RelRep.test` on the indices, and
    `where(b)` lists the same coreflexive, in ascending order;
  * `distinct(xs)` is `ran(f)`, without repeats, in first-occurrence order;
  * `group(xs)`, read as the relation `value ↦ index`, is `f°`, so its kernel `D°D` is `ff°`; its keys
    are `distinct(xs)` and each bucket ascends.
  Every statement is over the bits, never `Column.atoms`, which carries `Classical.choice`.
-/
import LeetQ.QRel
import QLean.Verify.Group
import QLean.Verify.Where

namespace LeetQ.Group

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ
open QLean.Kernel.Scan (Kind)

/-! ## A dense `long` payload read back -/

/-- A dense `long` payload as its elements. -/
def dec (b : ByteArray) : List Int64 := (List.range (b.size / 8)).map (atW 8 b)

theorem dec_enc (xs : List Int64) : dec (enc 8 xs) = xs :=
  List.ext_getElem (by simp [dec, enc_size (show 8 ≤ 8 by decide)]) fun i _ h => by
    simp only [dec, List.getElem_map, List.getElem_range]; exact atW_enc (by decide) xs i h (fits_eight _)

/-- An index answer as the numbers it holds. -/
def idx (b : ByteArray) : List Nat := (dec b).map fun v => v.toInt.toNat

theorem idx_indices {is : List Nat} (h : ∀ i ∈ is, i < 2 ^ 63) : idx (Order.indices is) = is := by
  rw [idx, show Order.indices is = enc 8 (is.map Int64.ofNat) by rw [Order.indices, enc, List.foldl_map],
    dec_enc, List.map_map]
  conv => rhs; rw [← List.map_id is]
  exact List.map_congr_left fun i hi => by
    show (Int64.ofNat i).toInt.toNat = i; rw [Int64.toInt_ofNat_of_lt (h i hi), Int.toNat_natCast]

/-- The elements `Order`'s kernels read: the first `n`, clamped to what the payload holds. -/
def cnt (n : USize) (b : ByteArray) : Nat := min n.toNat (b.size / 8)

/-- The column those kernels see. -/
def col (n : USize) (b : ByteArray) : List Int64 := (List.range (cnt n b)).map (atW 8 b)

/-- At `long`, `Order.keyAt` is the element's bits with the sign bit flipped, so two keys are equal
exactly when the elements are. -/
theorem keyAt_beq (b : ByteArray) (i j : Nat) :
    (Order.keyAt .i64 b j == Order.keyAt .i64 b i) = decide (atW 8 b j = atW 8 b i) := by
  have e : ∀ k, Kind.bitsAt .i64 b k = (atW 8 b k).toUInt64 := fun k => by
    rw [atW_eight, UInt64.toUInt64_toInt64]; rfl
  show (Kind.bitsAt .i64 b j ^^^ 0x8000000000000000 == Kind.bitsAt .i64 b i ^^^ 0x8000000000000000) = _
  rw [e, e]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, decide_eq_true_iff, UInt64.xor_left_inj]
  exact ⟨fun x => by rw [← Int64.toInt64_toUInt64 (atW 8 b j), x, Int64.toInt64_toUInt64], congrArg _⟩

/-! ## First occurrences and buckets, over any column `g` -/

section Firsts

variable {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat)

omit [DecidableEq α] in
theorem ix_range {i : Nat} {v : α} : ix ((List.range m).map g) i v ↔ i < m ∧ g i = v := by
  show ((List.range m).map g)[i]? = some v ↔ _
  rw [List.getElem?_map]
  by_cases h : i < m
  · rw [List.getElem?_range h]; simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]
    exact ⟨nofun, fun h' => absurd h'.1 h⟩

theorem mem_firsts (v : α) : v ∈ (firstsOf g m).map g ↔ ∃ i, i < m ∧ g i = v :=
  ⟨fun h => let ⟨i, hi, e⟩ := List.mem_map.1 h; ⟨i, List.mem_range.1 (List.mem_filter.1 hi).1, e⟩,
   fun ⟨_, hi, e⟩ => let ⟨f, hf, e'⟩ := exists_first hi; List.mem_map.2 ⟨f, hf, e'.trans e⟩⟩

/-- **`distinct = ran(f)`**: the first values, as a coreflexive, are the range of the column. -/
theorem firsts_ran : rel (((firstsOf g m).map g).map fun v => (v, v)) = Alg.ran (ix ((List.range m).map g)) :=
  hom_ext fun v w => by
    show (v, w) ∈ _ ↔ v = w ∧ ∃ i, ix ((List.range m).map g) i v ∧ ix ((List.range m).map g) i w
    rw [List.mem_map]
    constructor
    · rintro ⟨u, hu, he⟩
      cases he
      obtain ⟨i, hi, e⟩ := (mem_firsts g m _).1 hu
      exact ⟨rfl, i, (ix_range g m).2 ⟨hi, e⟩, (ix_range g m).2 ⟨hi, e⟩⟩
    · rintro ⟨rfl, i, h1, -⟩
      exact ⟨v, (mem_firsts g m v).2 ⟨i, (ix_range g m).1 h1⟩, rfl⟩

/-- **The dictionary read as `value ↦ index` is `f°`.** -/
theorem dict_conv : rel (dictOf g m) ≫ lmem Nat = (ix ((List.range m).map g))° :=
  hom_ext fun v i => by
    show (∃ is, (v, is) ∈ dictOf g m ∧ i ∈ is) ↔ ix ((List.range m).map g) i v
    rw [ix_range]
    constructor
    · rintro ⟨is, hd, hi⟩
      obtain ⟨f, -, he⟩ := List.mem_map.1 hd
      cases he
      obtain ⟨hi, e⟩ := List.mem_filter.1 hi
      exact ⟨List.mem_range.1 hi, of_decide_eq_true e⟩
    · rintro ⟨hi, rfl⟩
      obtain ⟨f, hf, e⟩ := exists_first (g := g) hi
      exact ⟨bucketOf g m f, List.mem_map.2 ⟨f, hf, by rw [e]⟩,
        List.mem_filter.2 ⟨List.mem_range.2 hi, decide_eq_true e.symm⟩⟩

/-- **`group` is the kernel `ff°`**: two indices share a bucket exactly when they hold one value. -/
theorem dict_kernel : (rel (dictOf g m) ≫ lmem Nat)° ≫ (rel (dictOf g m) ≫ lmem Nat) =
    ix ((List.range m).map g) ≫ (ix ((List.range m).map g))° := by
  rw [dict_conv]; rfl

/-- The keys are the first values, `distinct`'s answer. -/
theorem dict_keys : (dictOf g m).map Prod.fst = (firstsOf g m).map g := by
  rw [dictOf, List.map_map]; rfl

/-- Each bucket ascends. -/
theorem dict_sorted : ∀ p ∈ dictOf g m, p.2.Pairwise (· < ·) := fun _ hp => by
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hp
  exact (pairwise_range m).filter _

end Firsts

theorem firsts_i64 (m : Nat) (b : ByteArray) : Order.firsts .i64 m b = firstsOf (atW 8 b) m := by
  simp only [Order.firsts, firstsOf, bne, keyAt_beq]

/-! ## `where`: a `bits` column is a coreflexive on the indices -/

/-- `n` booleans packed a bit each as the coreflexive on the indices whose bit is set. -/
def bitsRel (n : Nat) (b : ByteArray) : RelTest Nat Nat := .test fun i j => i == j && decide (i < n) && bitAt b i

/-- **The bit column denotes `p?`, `p(i) ⟺ i < n ∧ bit i`.** -/
theorem rel_bitsRel (n : Nat) (b : ByteArray) :
    (bitsRel n b).rel = Freyd.Alg.RelSet.corefl (A := ⟨Nat⟩) fun i => i < n ∧ bitAt b i = true :=
  hom_ext fun i j => by
    simp only [bitsRel, RelTest.rel, Freyd.Alg.RelSet.corefl, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨rfl, h⟩, hb⟩; exact ⟨rfl, h, hb⟩
    · rintro ⟨rfl, h, hb⟩; exact ⟨⟨rfl, h⟩, hb⟩

/-- `where`'s answer as indices. -/
def whereQ (n : USize) (bits : ByteArray) : List Nat := idx (whereBits n bits)

/-- **`whereBits` answers the set bits ascending**: below `2 ^ 63` bits its `Int64`s read back exactly. -/
theorem whereQ_eq (n : USize) (bits : ByteArray) (h : n.toNat < 2 ^ 63) :
    whereQ n bits = (List.range n.toNat).filter (bitAt bits) :=
  idx_indices fun i hi => by have := List.mem_range.1 (List.mem_filter.1 hi).1; omega

/-- **`where(b)`, as `RelRep.corefl`, is the same coreflexive as the bit test.** -/
theorem where_spec (n : USize) (bits : ByteArray) (h : n.toNat < 2 ^ 63) :
    (RelRep.corefl fun i => decide (i ∈ whereQ n bits)).rel = (bitsRel n.toNat bits).rel := by
  rw [rel_bitsRel, RelRep.rel_corefl, whereQ_eq n bits h]
  congr; funext i; simp only [decide_eq_true_eq, List.mem_filter, List.mem_range]

/-! ## `distinct` -/

/-- `distinct`'s answer over a dense payload. -/
def distinctQ (n : USize) (b : ByteArray) : List Int64 := dec (Order.distinct .i64 n b)

/-- **`Order.distinct` answers the first occurrences, in order.** -/
theorem distinctQ_eq (n : USize) (b : ByteArray) : distinctQ n b = (firstsOf (atW 8 b) (cnt n b)).map (atW 8 b) := by
  have : Order.distinct .i64 n b = enc 8 ((Order.firsts .i64 (cnt n b) b).map (atW 8 b)) := by
    simp only [Order.distinct, enc, List.foldl_map, funext (atW_eight b), UInt64.toUInt64_toInt64]; rfl
  rw [distinctQ, this, dec_enc, firsts_i64]

/-- **`distinct = ran(f)`** over a dense payload, without repeats. -/
theorem distinct_spec (n : USize) (b : ByteArray) :
    rel ((distinctQ n b).map fun v => (v, v)) = Alg.ran (ix (col n b)) ∧ (distinctQ n b).Nodup := by
  rw [distinctQ_eq]; exact ⟨firsts_ran _ _, nodup_firsts _ _⟩

/-! ## `group` -/

/-- Cut a list at consecutive byte offsets `a, c, …`: the piece from element `a/8`, `(c-a)/8` long. -/
def cutAt {β : Type} : List Nat → List β → List (List β)
  | a :: c :: os, xs => (xs.drop (a / 8)).take ((c - a) / 8) :: cutAt (c :: os) xs
  | _, _ => []

/-- A `group` answer `(keys, indices, offsets)` as `value ↦ bucket` pairs. -/
def readGroup (r : ByteArray × ByteArray × Array Nat) : List (Int64 × List Nat) :=
  (dec r.1).zip (cutAt r.2.2.toList (idx r.2.1))

/-- `group`'s answer over a dense payload. -/
def groupQ (n : USize) (b : ByteArray) : List (Int64 × List Nat) := readGroup (Order.group .i64 n b)

/-- The byte offsets after a prefix of `pos` elements, one per length. -/
def offs (pos : Nat) : List Nat → List Nat
  | [] => []
  | l :: ls => 8 * (pos + l) :: offs (pos + l) ls

theorem bounds_toList (lens : List Nat) : (Order.bounds lens).toList = 0 :: offs 0 lens := by
  suffices h : ∀ (acc : Array Nat) (pos : Nat), (lens.foldl (init := (acc, pos)) fun (acc, pos) len =>
      (acc.push (8 * (pos + len)), pos + len)).1.toList = acc.toList ++ offs pos lens from h #[0] 0
  induction lens with
  | nil => intro acc pos; simp [offs]
  | cons l ls ih => intro acc pos; rw [List.foldl_cons, ih]; simp [offs]

theorem cutAt_flatten (bs : List (List Nat)) (pre : List Nat) :
    cutAt (8 * pre.length :: offs pre.length (bs.map List.length)) (pre ++ bs.flatten) = bs := by
  induction bs generalizing pre with
  | nil => rfl
  | cons c cs ih =>
    have := ih (pre ++ c)
    rw [List.length_append, List.append_assoc] at this
    simp only [List.map_cons, offs, cutAt, List.flatten_cons]
    rw [this, show 8 * pre.length / 8 = pre.length by omega,
      show (8 * (pre.length + c.length) - 8 * pre.length) / 8 = c.length by omega,
      List.drop_left, List.take_left]

/-- **`Order.group` answers each first value with its bucket**, below `2^63` elements. -/
theorem groupQ_eq (n : USize) (b : ByteArray) (h : cnt n b < 2 ^ 63) : groupQ n b = dictOf (atW 8 b) (cnt n b) := by
  have hb : Order.bucket .i64 (cnt n b) b = bucketOf (atW 8 b) (cnt n b) := funext fun f => by
    simp only [Order.bucket, bucketOf, keyAt_beq]
  have hg : Order.group .i64 n b = (Order.distinct .i64 n b, Order.indices ((firstsOf (atW 8 b) (cnt n b)).map
      (bucketOf (atW 8 b) (cnt n b))).flatten, Order.bounds (((firstsOf (atW 8 b) (cnt n b)).map
      (bucketOf (atW 8 b) (cnt n b))).map List.length)) := by
    simp only [Order.group, show min n.toNat (Kind.i64.avail b) = cnt n b from rfl, firsts_i64, hb]
  rw [groupQ, hg, readGroup, ← distinctQ, distinctQ_eq, idx_indices, bounds_toList,
    show (0 :: offs 0 _) = 8 * ([] : List Nat).length :: offs ([] : List Nat).length _ from rfl,
    ← List.nil_append (List.flatten _), cutAt_flatten, List.zip_map', dictOf]
  intro i hi
  obtain ⟨_, hl, hil⟩ := List.mem_flatten.1 hi
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hl
  have := List.mem_range.1 (List.mem_filter.1 hil).1
  omega

/-- **The dictionary `group` answers, read as `value ↦ index`, is `f°`; its kernel is `ff°`; its keys
are `distinct`'s; each bucket ascends.** -/
theorem group_spec (n : USize) (b : ByteArray) (h : cnt n b < 2 ^ 63) :
    rel (groupQ n b) ≫ lmem Nat = (ix (col n b))° ∧
    (rel (groupQ n b) ≫ lmem Nat)° ≫ (rel (groupQ n b) ≫ lmem Nat) = ix (col n b) ≫ (ix (col n b))° ∧
    (groupQ n b).map Prod.fst = distinctQ n b ∧ ∀ p ∈ groupQ n b, p.2.Pairwise (· < ·) := by
  rw [groupQ_eq n b h, distinctQ_eq]
  exact ⟨dict_conv _ _, dict_kernel _ _, dict_keys _ _, dict_sorted _ _⟩

/-! ## Over a Frame-of-Reference column

`groupFoR` is `group` over `Coc.decode`; `distinctFoR` is `distinct` over it, its answer encoded
again, and read back here through `foRBits` as `Keys.foR` reads a key column. -/

/-- The `n` elements an encoded column holds, as `foRBits` reads them. -/
def colFoR (n : USize) (md pk : ByteArray) : List Int64 := (List.range n.toNat).map (Keys.foR n.toNat md pk).get

/-- The dense payload `groupFoR` and `distinctFoR` decode to. -/
abbrev decoded (n : USize) (md pk : ByteArray) : ByteArray := Coc.decode (Kind.width .i64).toUSize md pk n

theorem decoded_spec (n : USize) (md pk : ByteArray) :
    cnt n (decoded n md pk) = n.toNat ∧ (decoded n md pk).size / 8 = n.toNat ∧
      col n (decoded n md pk) = colFoR n md pk := by
  have hw : (Kind.width .i64).toUSize.toNat = 8 := by
    simp only [Kind.width, Nat.toUSize, USize.toNat_ofNat']
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  obtain ⟨hs, hg⟩ := decodeW _ (by rw [hw]; decide) md pk n
  simp only [hw, show 8 * 8 = 64 from rfl, ofNat_toNat_mod64] at hs hg
  have hc : cnt n (decoded n md pk) = n.toNat := by
    show min n.toNat ((decoded n md pk).size / 8) = n.toNat; rw [hs]; omega
  refine ⟨hc, by rw [hs]; omega, ?_⟩
  rw [col, hc, colFoR]
  exact List.map_congr_left fun i hi => by rw [atW_eight, hg i (List.mem_range.1 hi)]; rfl

/-- `distinctFoR`'s encoded answer, read back through `foRBits`. -/
def distinctFoRQ (n : USize) (md pk : ByteArray) : List Int64 :=
  let r := Order.distinctFoR .i64 n md pk
  (List.range r.1).map (Keys.foR r.1 r.2.1 r.2.2).get

/-- `distinctFoR` answers what `distinct` answers over the decoded column. -/
theorem distinctFoRQ_eq (n : USize) (md pk : ByteArray) : distinctFoRQ n md pk = distinctQ n (decoded n md pk) := by
  obtain ⟨-, hs, -⟩ := decoded_spec n md pk
  have hn : ((decoded n md pk).size / 8).toUSize = n := by
    rw [hs]; exact USize.toNat_inj.1 (USize.toNat_ofNat_of_lt' n.toNat_lt_size)
  have key : ∀ d : ByteArray, (List.range (d.size / 8)).map (Keys.foR (d.size / 8)
      (Coc.encode (Nat.toUSize 8) d).1 (Coc.encode (Nat.toUSize 8) d).2).get = dec d := fun d =>
    List.map_congr_left fun i hi => by
      have e := foRBits_encode_bits 8 (by decide) (by decide) d i (List.mem_range.1 hi)
      rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _)] at e
      show (foRBits _ _ _ i).toInt64 = atW 8 d i; rw [atW_eight]
      rw [UInt64.toNat_inj.1 e]
  refine (key (Order.distinct .i64 ((decoded n md pk).size / 8).toUSize (decoded n md pk))).trans ?_
  rw [hn]; rfl

/-- **`distinct = ran(f)`** over an encoded column, without repeats. -/
theorem distinctFoR_spec (n : USize) (md pk : ByteArray) :
    rel ((distinctFoRQ n md pk).map fun v => (v, v)) = Alg.ran (ix (colFoR n md pk)) ∧
      (distinctFoRQ n md pk).Nodup := by
  rw [distinctFoRQ_eq, ← (decoded_spec n md pk).2.2]; exact distinct_spec _ _

/-- `groupFoR`'s answer. -/
def groupFoRQ (n : USize) (md pk : ByteArray) : List (Int64 × List Nat) := readGroup (Order.groupFoR .i64 n md pk)

/-- **`group_spec` over an encoded column.** -/
theorem groupFoR_spec (n : USize) (md pk : ByteArray) (h : n.toNat < 2 ^ 63) :
    rel (groupFoRQ n md pk) ≫ lmem Nat = (ix (colFoR n md pk))° ∧
    (rel (groupFoRQ n md pk) ≫ lmem Nat)° ≫ (rel (groupFoRQ n md pk) ≫ lmem Nat) =
      ix (colFoR n md pk) ≫ (ix (colFoR n md pk))° ∧
    (groupFoRQ n md pk).map Prod.fst = distinctFoRQ n md pk ∧ ∀ p ∈ groupFoRQ n md pk, p.2.Pairwise (· < ·) := by
  obtain ⟨hc, -, hcol⟩ := decoded_spec n md pk
  rw [show groupFoRQ n md pk = groupQ n (decoded n md pk) from rfl, ← hcol, distinctFoRQ_eq]
  exact group_spec _ _ (hc ▸ h)

/-! ## Runs: the kernel reduces the Lean bodies, `#guard` calls the C -/

/-- `where 101b`, the bits LSB first. -/
example : whereQ 3 ⟨#[5]⟩ = [0, 2] := by
  simp only [whereQ, whereBits, USize.reduceToNat]; decide +kernel
example : distinctQ 5 (enc 8 [3, 1, 3, 2, 1]) = [3, 1, 2] := by
  simp only [distinctQ, Order.distinct, USize.reduceToNat]; decide +kernel
example : groupQ 5 (enc 8 [3, 1, 3, 2, 1]) = [(3, [0, 2]), (1, [1, 4]), (2, [3])] := by
  simp only [groupQ, Order.group, Order.distinct, USize.reduceToNat]; decide +kernel

#guard whereQ 3 ⟨#[5]⟩ == [0, 2]

/-- 45 is `0b101101`: bits 0, 2, 3 and 5 of six. -/
def six : USize := USize.ofNatLT 6 (lt_usize (by decide))

example : whereQ six ⟨#[45]⟩ = [0, 2, 3, 5] := by decide +kernel
example : (bitsRel 6 ⟨#[45]⟩).mem 3 3 = true ∧ (bitsRel 6 ⟨#[45]⟩).mem 4 4 = false := by decide +kernel
#guard whereQ six ⟨#[45]⟩ == [0, 2, 3, 5]
#guard (bitsRel 6 ⟨#[45]⟩).mem 5 5 && !(bitsRel 6 ⟨#[45]⟩).mem 5 4 && !(bitsRel 5 ⟨#[45]⟩).mem 5 5
#guard distinctQ 5 (enc 8 [3, 1, 3, 2, 1]) == [3, 1, 2]
#guard groupQ 5 (enc 8 [3, 1, 3, 2, 1]) == [(3, [0, 2]), (1, [1, 4]), (2, [3])]

/-- `3 1 3 2 1` Frame-of-Reference encoded. -/
def foR5 : ByteArray × ByteArray := Coc.encode (Nat.toUSize 8) (enc 8 [3, 1, 3, 2, 1])

-- `distinctFoR` decodes, runs `distinct` and encodes the answer again; the kernel runs the first two.
example : distinctFoRQ 5 foR5.1 foR5.2 = [3, 1, 2] := by
  rw [distinctFoRQ_eq]
  simp only [distinctQ, Order.distinct, foR5, Coc.encode, Coc.decode, Coc.elems, USize.reduceToNat, Kind.width,
    toNat_toUSize, Nat.reducePow, Nat.reduceLT]
  decide +kernel
example : groupFoRQ 5 foR5.1 foR5.2 = [(3, [0, 2]), (1, [1, 4]), (2, [3])] := by
  simp only [groupFoRQ, Order.groupFoR, Order.group, Order.distinct, foR5, Coc.encode, Coc.decode, Coc.elems,
    USize.reduceToNat, Kind.width, toNat_toUSize, Nat.reducePow, Nat.reduceLT]
  decide +kernel

#guard distinctFoRQ 5 foR5.1 foR5.2 == [3, 1, 2]
#guard groupFoRQ 5 foR5.1 foR5.2 == [(3, [0, 2]), (1, [1, 4]), (2, [3])]

#print axioms rel_bitsRel
#print axioms whereQ_eq
#print axioms where_spec
#print axioms distinct_spec
#print axioms group_spec
#print axioms distinctFoR_spec
#print axioms groupFoR_spec

end LeetQ.Group
