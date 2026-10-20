/-
  q's `where`, `distinct` and `group` over qlean's `long` columns, each specified by a relation and
  implemented by the qlean kernel (`whereBits`, `Order.distinct`/`distinctFoR`, `Order.group`/`groupFoR`),
  whose Lean body is what every theorem here reads. With `f = ix(xs) : Idx ⟶ Int64` the column:
  * `where(b)` is the coreflexive `p?` of the bit predicate, in ascending order;
  * `distinct(xs)` is `ran(f)`, without repeats, in first-occurrence order;
  * `group(xs)`, read as the relation `value ↦ index`, is `f°`, so its kernel `D°D` is `ff°`; its keys
    are `distinct(xs)` and each bucket ascends.
  Every statement is over the bits, never `Column.atoms`, which carries `Classical.choice`.
-/
import LeetQ.QRel

namespace LeetQ.Group

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ
open QLean.Kernel.Scan (Kind)

/-! ## A dense `long` payload read back -/

/-- A dense `long` payload as its elements. -/
def dec (b : ByteArray) : List Int64 := (List.range (b.size / 8)).map (at8 b)

theorem dec_enc (xs : List Int64) : dec (enc xs) = xs :=
  List.ext_getElem (by simp [dec, enc_size]) fun i _ h => by
    simp only [dec, List.getElem_map, List.getElem_range]; exact at8_enc xs i h

/-- An index answer as the numbers it holds. -/
def idx (b : ByteArray) : List Nat := (dec b).map fun v => v.toInt.toNat

theorem idx_indices {is : List Nat} (h : ∀ i ∈ is, i < 2 ^ 63) : idx (Order.indices is) = is := by
  rw [idx, show Order.indices is = enc (is.map Int64.ofNat) by rw [Order.indices, enc, List.foldl_map],
    dec_enc, List.map_map]
  conv => rhs; rw [← List.map_id is]
  exact List.map_congr_left fun i hi => by
    show (Int64.ofNat i).toInt.toNat = i; rw [Int64.toInt_ofNat_of_lt (h i hi), Int.toNat_natCast]

/-- The elements `Order`'s kernels read: the first `n`, clamped to what the payload holds. -/
def cnt (n : USize) (b : ByteArray) : Nat := min n.toNat (b.size / 8)

/-- The column those kernels see. -/
def col (n : USize) (b : ByteArray) : List Int64 := (List.range (cnt n b)).map (at8 b)

/-- At `long`, `Order.keyAt` is the element's bits with the sign bit flipped, so two keys are equal
exactly when the elements are. -/
theorem keyAt_beq (b : ByteArray) (i j : Nat) :
    (Order.keyAt .i64 b j == Order.keyAt .i64 b i) = decide (at8 b j = at8 b i) := by
  have e : ∀ k, Kind.bitsAt .i64 b k = (at8 b k).toUInt64 := fun k => by rw [at8, UInt64.toUInt64_toInt64]; rfl
  show (Kind.bitsAt .i64 b j ^^^ 0x8000000000000000 == Kind.bitsAt .i64 b i ^^^ 0x8000000000000000) = _
  rw [e, e]
  by_cases h : at8 b j = at8 b i
  · simp [h]
  · have : (at8 b j).toUInt64 ^^^ 0x8000000000000000 ≠ (at8 b i).toUInt64 ^^^ 0x8000000000000000 := fun x =>
      h (by rw [← Int64.toInt64_toUInt64 (at8 b j), (UInt64.xor_left_inj _).mp x, Int64.toInt64_toUInt64])
    simp [h, this]

/-! ## First occurrences and buckets, over any column `g` -/

section Firsts

variable {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat)

/-- The indices below `m` where `g` takes a value for the first time, ascending. -/
def firstsOf : List Nat := (List.range m).filter fun i => (List.range i).all fun j => !decide (g j = g i)

/-- The indices below `m` where `g` takes `g(f)`, ascending. -/
def bucketOf (f : Nat) : List Nat := (List.range m).filter fun i => decide (g i = g f)

/-- `group`'s answer as pairs: each first value with its bucket. -/
def dictOf : List (α × List Nat) := (firstsOf g m).map fun f => (g f, bucketOf g m f)

omit [DecidableEq α] in
theorem ix_range {i : Nat} {v : α} : ix ((List.range m).map g) i v ↔ i < m ∧ g i = v := by
  show ((List.range m).map g)[i]? = some v ↔ _
  rw [List.getElem?_map]
  by_cases h : i < m
  · rw [List.getElem?_range h]; simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]
    exact ⟨nofun, fun h' => absurd h'.1 h⟩

variable {g m} in
theorem exists_first {i : Nat} (hi : i < m) : ∃ f ∈ firstsOf g m, g f = g i := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    cases hb : (List.range i).all fun j => !decide (g j = g i) with
    | true => exact ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, hb⟩, rfl⟩
    | false =>
      obtain ⟨j, hj, e⟩ := List.all_eq_false.1 hb
      have hj := List.mem_range.1 hj
      obtain ⟨f, hf, e'⟩ := ih j hj (by omega)
      exact ⟨f, hf, e'.trans (by simpa using e)⟩

theorem mem_firsts (v : α) : v ∈ (firstsOf g m).map g ↔ ∃ i, i < m ∧ g i = v :=
  ⟨fun h => let ⟨i, hi, e⟩ := List.mem_map.1 h; ⟨i, List.mem_range.1 (List.mem_filter.1 hi).1, e⟩,
   fun ⟨_, hi, e⟩ => let ⟨f, hf, e'⟩ := exists_first hi; List.mem_map.2 ⟨f, hf, e'.trans e⟩⟩

/-- **No value twice**: a first occurrence differs from every earlier one. -/
theorem nodup_firsts : ((firstsOf g m).map g).Nodup := by
  refine List.pairwise_map.2 ((List.pairwise_lt_range.filter _).imp_of_mem fun {i j} _ hj hij e => ?_)
  have := List.all_eq_true.1 (List.mem_filter.1 hj).2 i (List.mem_range.2 hij)
  simp [e] at this

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
  exact List.pairwise_lt_range.filter _

end Firsts

theorem firsts_i64 (m : Nat) (b : ByteArray) : Order.firsts .i64 m b = firstsOf (at8 b) m := by
  simp only [Order.firsts, firstsOf, bne, keyAt_beq]

/-! ## `where` -/

/-- `where`'s answer as indices. -/
def whereQ (n : USize) (bits : ByteArray) : List Nat := idx (whereBits n bits)

/-- **`whereBits` answers the set bits ascending.** -/
theorem whereQ_eq (n : USize) (bits : ByteArray) (h : n.toNat < 2 ^ 63) :
    whereQ n bits = (List.range n.toNat).filter (bitAt bits) :=
  idx_indices fun i hi => by have := List.mem_range.1 (List.mem_filter.1 hi).1; omega

/-- **`where(b)` is the coreflexive of the bit predicate.** -/
theorem where_spec (n : USize) (bits : ByteArray) (h : n.toNat < 2 ^ 63) :
    rel ((whereQ n bits).map fun i => (i, i)) = (RelRep.corefl fun i => decide (i < n.toNat) && bitAt bits i).rel := by
  rw [RelRep.rel_corefl, whereQ_eq n bits h]
  refine hom_ext fun i j => ?_
  show (i, j) ∈ _ ↔ i = j ∧ _
  simp only [List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨ha, hb⟩, rfl, rfl⟩; exact ⟨rfl, ha, hb⟩
  · rintro ⟨rfl, ha, hb⟩; exact ⟨i, ⟨ha, hb⟩, rfl, rfl⟩

/-! ## `distinct` -/

/-- `distinct`'s answer over a dense payload. -/
def distinctQ (n : USize) (b : ByteArray) : List Int64 := dec (Order.distinct .i64 n b)

/-- **`Order.distinct` answers the first occurrences, in order.** -/
theorem distinctQ_eq (n : USize) (b : ByteArray) : distinctQ n b = (firstsOf (at8 b) (cnt n b)).map (at8 b) := by
  have : Order.distinct .i64 n b = enc ((Order.firsts .i64 (cnt n b) b).map (at8 b)) := by
    simp only [Order.distinct, enc, List.foldl_map, at8, UInt64.toUInt64_toInt64]; rfl
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
theorem groupQ_eq (n : USize) (b : ByteArray) (h : cnt n b < 2 ^ 63) : groupQ n b = dictOf (at8 b) (cnt n b) := by
  have hb : Order.bucket .i64 (cnt n b) b = bucketOf (at8 b) (cnt n b) := funext fun f => by
    simp only [Order.bucket, bucketOf, keyAt_beq]
  have hg : Order.group .i64 n b = (Order.distinct .i64 n b, Order.indices ((firstsOf (at8 b) (cnt n b)).map
      (bucketOf (at8 b) (cnt n b))).flatten, Order.bounds (((firstsOf (at8 b) (cnt n b)).map
      (bucketOf (at8 b) (cnt n b))).map List.length)) := by
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
  obtain ⟨hs, hg⟩ := decode8 _ hw md pk n
  have hc : cnt n (decoded n md pk) = n.toNat := by
    show min n.toNat ((decoded n md pk).size / 8) = n.toNat; rw [hs]; omega
  refine ⟨hc, by rw [hs]; omega, ?_⟩
  rw [col, hc, colFoR]
  exact List.map_congr_left fun i hi => by rw [at8, hg i (List.mem_range.1 hi)]; rfl

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
      show (foRBits _ _ _ i).toInt64 = (bitsAt d (i * 8) 8).toInt64
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
example : distinctQ 5 (enc [3, 1, 3, 2, 1]) = [3, 1, 2] := by
  simp only [distinctQ, Order.distinct, USize.reduceToNat]; decide +kernel
example : groupQ 5 (enc [3, 1, 3, 2, 1]) = [(3, [0, 2]), (1, [1, 4]), (2, [3])] := by
  simp only [groupQ, Order.group, Order.distinct, USize.reduceToNat]; decide +kernel

#guard whereQ 3 ⟨#[5]⟩ == [0, 2]
#guard distinctQ 5 (enc [3, 1, 3, 2, 1]) == [3, 1, 2]
#guard groupQ 5 (enc [3, 1, 3, 2, 1]) == [(3, [0, 2]), (1, [1, 4]), (2, [3])]

#print axioms where_spec
#print axioms distinct_spec
#print axioms group_spec
#print axioms distinctFoR_spec
#print axioms groupFoR_spec

end LeetQ.Group
