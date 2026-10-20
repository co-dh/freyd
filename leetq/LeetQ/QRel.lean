/-
  `SortedRel`'s interface — `rep`, `ofList`, `lookup`, and the laws `rep_ofList`, `lookup_rep` — over
  qlean's `long` columns: the values are a dense payload read through `Column.bitsAt`; the keys are
  either dense too, searched by `binBytes` (the Lean body of qlean's C `bin`), or Frame-of-Reference
  encoded, read through `Column.foRBits` and searched by `foRBin`, so they stay compressed during
  `lookup`. Everything past `Keys` is stated once over both.
  Every statement is over the bits, never `Column.atoms`/`Column.raw`, which carry `Classical.choice`.
-/
import AOP.A6_FinRel
import QLean.Verify.Search
import QLean.Verify.Raw

namespace LeetQ

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-! ## A dense `long` payload -/

/-- The `i`th `Int64` of a dense payload. -/
def at8 (b : ByteArray) (i : Nat) : Int64 := (bitsAt b (i * 8) 8).toInt64

/-- `xs` laid out as a dense `long` payload. -/
def enc (xs : List Int64) : ByteArray := xs.foldl (fun b x => pushBits b x.toUInt64 8) ByteArray.empty

-- `foldl_pushBits8` at `enc`'s empty start; kept as two statements since the keys, the values and
-- the encoded keys all read `enc` back.
theorem enc_size (xs : List Int64) : (enc xs).size = 8 * xs.length := by
  rw [enc, (foldl_pushBits8 Int64.toUInt64 xs ByteArray.empty).1, show ByteArray.empty.size = 0 from rfl, Nat.zero_add]

theorem at8_enc (xs : List Int64) (i : Nat) (hi : i < xs.length) : at8 (enc xs) i = xs[i] := by
  obtain ⟨-, -, hg⟩ := foldl_pushBits8 Int64.toUInt64 xs ByteArray.empty
  have := hg i hi
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Nat.mul_comm] at this
  rw [at8, enc, this, Int64.toInt64_toUInt64]

/-- What both `ascending` kernels answer, `ascending_i64_iff` and `ascendingFoR_i64_iff`, in the
index form the searches take. -/
theorem sorted_of_pairwise (f : Nat → Int64) (n : Nat)
    (h : ((List.range n).map f).Pairwise (i64Rel false false)) : ∀ i j, i ≤ j → j < n → f i ≤ f j := by
  intro i j hij hj
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · have := List.pairwise_iff_getElem.1 h i j (by simp; omega) (by simp; omega) hlt
    simp only [List.getElem_map, List.getElem_range] at this
    exact this
  · exact Int64.le_iff_toInt_le.2 (Int.le_refl _)

/-- `USize.size` is `2 ^ System.Platform.numBits`, opaque to the kernel; a bound every platform meets
lets a kernel run rewrite a count's `toUSize` round trip. -/
theorem lt_usize {n : Nat} (h : n < 2 ^ 32) : n < USize.size := by
  cases System.Platform.numBits_eq <;> simp [USize.size, *] <;> omega

theorem toNat_toUSize {n : Nat} (h : n < 2 ^ 32) : (Nat.toUSize n).toNat = n :=
  USize.toNat_ofNat_of_lt' (lt_usize h)

/-! ## A key column, dense or encoded -/

/-- A `long` key column: a dense payload, or `n` elements Frame-of-Reference encoded as
`(metadata, pack)`, which `foRBin` searches without the caller decoding it. -/
inductive Keys
  | dense (b : ByteArray)
  | foR (n : Nat) (md pk : ByteArray)

namespace Keys

/-- The number of keys. -/
def count : Keys → Nat
  | .dense b => b.size / 8
  | .foR n _ _ => n

/-- The `i`th key. -/
def get : Keys → Nat → Int64
  | .dense b, i => at8 b i
  | .foR _ md pk, i => (foRBits md pk (blockStarts md) i).toInt64

/-- The search kernel's 8-byte answer for needle `k`. -/
def bin (right : Bool) (k : Int64) : Keys → ByteArray
  | .dense b => binBytes 8 false true right b (pushBits ByteArray.empty k.toUInt64 8)
  | .foR n md pk => foRBin 8 right md pk n.toUSize (pushBits ByteArray.empty k.toUInt64 8)

/-- What `foRBin` needs beyond order: its count survives `Nat.toUSize`. -/
def fits : Keys → Prop
  | .dense _ => True
  | .foR n _ _ => n < USize.size

/-- `binBytes_long` and `foRBin_long`, one statement over the key reader. -/
theorem bin_spec (c : Keys) (right : Bool) (k : Int64) (hf : c.fits) (hn : c.count < 2 ^ 63)
    (hs : ∀ i j, i ≤ j → j < c.count → c.get i ≤ c.get j) :
    ∃ r, r ≤ c.count ∧ (bitsAt (c.bin right k) 0 8).toInt64.toInt = (if right then (r : Int) else (r : Int) - 1) ∧
      (∀ j, j < r → if right then c.get j < k else c.get j ≤ k) ∧
      (r < c.count → if right then k ≤ c.get r else k < c.get r) := by
  cases c with
  | dense b => have := binBytes_long right b k.toUInt64 hn hs; rwa [Int64.toInt64_toUInt64] at this
  | foR n md pk => have := foRBin_long right n md pk k.toUInt64 hf hn hs; rwa [Int64.toInt64_toUInt64] at this

/-- `ks` as a key column, encoded when `foR` asks and the count fits a `USize`, which every list in
memory does; otherwise dense. -/
def ofList (foR : Bool) (ks : List Int64) : Keys :=
  if foR = true ∧ ks.length < USize.size then
    let e := Coc.encode (Nat.toUSize 8) (enc ks)
    .foR ks.length e.1 e.2
  else .dense (enc ks)

theorem count_ofList (foR : Bool) (ks : List Int64) : (ofList foR ks).count = ks.length := by
  unfold ofList
  by_cases h : foR = true ∧ ks.length < USize.size
  · rw [if_pos h]; rfl
  · rw [if_neg h]; show (enc ks).size / 8 = _; rw [enc_size]; omega

theorem fits_ofList (foR : Bool) (ks : List Int64) : (ofList foR ks).fits := by
  unfold ofList
  by_cases h : foR = true ∧ ks.length < USize.size
  · rw [if_pos h]; exact h.2
  · rw [if_neg h]; trivial

/-- The encoded keys read back through `foRBits_encode_bits`, the dense ones through `at8_enc`. -/
theorem get_ofList (foR : Bool) (ks : List Int64) (i : Nat) (hi : i < ks.length) :
    (ofList foR ks).get i = ks[i] := by
  unfold ofList
  by_cases h : foR = true ∧ ks.length < USize.size
  · rw [if_pos h]
    have e := foRBits_encode_bits 8 (by decide) (by decide) (enc ks) i (by rw [enc_size]; omega)
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _)] at e
    show (foRBits _ _ _ i).toInt64 = _
    rw [UInt64.toNat_inj.1 e]; exact at8_enc ks i hi
  · rw [if_neg h]; exact at8_enc ks i hi

end Keys

/-! ## The structure -/

/-- A finite relation `Int64 ⟶ Int64` as a key column and a dense `long` value column, the keys
ascending. -/
structure QSortedRel where
  keys : Keys
  vals : ByteArray
  len : vals.size / 8 = keys.count
  sorted : ∀ i j, i ≤ j → j < keys.count → keys.get i ≤ keys.get j
  fits : keys.fits

namespace QSortedRel

/-- The number of pairs. -/
def count (s : QSortedRel) : Nat := s.keys.count

/-- The pairs, read off the two columns. -/
def toList (s : QSortedRel) : List (Int64 × Int64) :=
  (List.range s.count).map fun i => (s.keys.get i, at8 s.vals i)

/-- The relation the columns denote. -/
def rep (s : QSortedRel) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩ := rel s.toList

theorem mem_rep {s : QSortedRel} {k v : Int64} :
    s.rep k v ↔ ∃ i, i < s.count ∧ s.keys.get i = k ∧ at8 s.vals i = v := by
  show (k, v) ∈ s.toList ↔ _
  simp only [toList, List.mem_map, List.mem_range, Prod.mk.injEq]

/-- Two dense columns checked by the C `ascending` kernel, whose Lean body `ascending_i64_iff` reads. -/
def ofBytes? (keys vals : ByteArray) : Option QSortedRel :=
  if h : keys.size / 8 < USize.size ∧ vals.size / 8 = keys.size / 8 ∧
      Order.ascending .i64 false false (USize.ofNat (keys.size / 8)) keys = true then
    some ⟨.dense keys, vals, h.2.1, sorted_of_pairwise _ _ (by
      have := (ascending_i64_iff false false _ keys).1 h.2.2
      rwa [USize.toNat_ofNat_of_lt' h.1, Nat.min_self] at this), trivial⟩
  else none

/-- An encoded key column of `n` elements checked by the C `ascendingFoR`, whose Lean body
`ascendingFoR_i64_iff` reads, beside a dense value column. -/
def ofFoR? (n : Nat) (md pk vals : ByteArray) : Option QSortedRel :=
  if h : n < USize.size ∧ vals.size / 8 = n ∧ Order.ascendingFoR .i64 false false n.toUSize md pk = true then
    some ⟨.foR n md pk, vals, h.2.1, sorted_of_pairwise _ _ (by
      have := (ascendingFoR_i64_iff false false _ md pk).1 h.2.2
      rwa [USize.toNat_ofNat_of_lt' h.1] at this), h.1⟩
  else none

/-- The key order the sort uses. -/
def keyLE (a b : Int64 × Int64) : Bool := decide (a.1.toInt ≤ b.1.toInt)

/-- Sort the pairs by key, then lay them out as two columns, the keys encoded when `foR`. -/
def ofList (l : List (Int64 × Int64)) (foR : Bool := false) : QSortedRel where
  keys := Keys.ofList foR ((l.mergeSort keyLE).map Prod.fst)
  vals := enc ((l.mergeSort keyLE).map Prod.snd)
  len := by rw [Keys.count_ofList]; simp [enc_size]
  sorted := fun i j hij hj => by
    have hm := List.pairwise_mergeSort (le := keyLE)
      (fun a b c h1 h2 => by simp only [keyLE, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [keyLE, Bool.or_eq_true, decide_eq_true_eq]; omega) l
    rw [Keys.count_ofList, List.length_map] at hj
    rw [Keys.get_ofList _ _ _ (by simp only [List.length_map]; omega),
      Keys.get_ofList _ _ _ (by simp only [List.length_map]; omega), List.getElem_map, List.getElem_map]
    rcases Nat.lt_or_eq_of_le hij with hlt | rfl
    · have := List.pairwise_iff_getElem.1 hm i j (by omega) hj hlt
      simp only [keyLE, decide_eq_true_eq] at this
      exact Int64.le_iff_toInt_le.2 this
    · exact Int64.le_iff_toInt_le.2 (Int.le_refl _)
  fits := Keys.fits_ofList _ _

theorem toList_ofList (l : List (Int64 × Int64)) (foR : Bool) : (ofList l foR).toList = l.mergeSort keyLE := by
  apply List.ext_getElem
  · simp [toList, count, ofList, Keys.count_ofList]
  · intro i h1 h2
    simp only [toList, List.getElem_map, List.getElem_range, ofList]
    rw [Keys.get_ofList _ _ _ (by simp only [List.length_map]; omega),
      at8_enc _ _ (by simp only [List.length_map]; omega), List.getElem_map, List.getElem_map]

/-- **`rep(ofList(l)) = rel(l)`**, as `FinRel.rep_ofList`, dense or encoded. -/
theorem rep_ofList (l : List (Int64 × Int64)) (foR : Bool) : (ofList l foR).rep = rel l := by
  show rel _ = _
  rw [toList_ofList]
  exact rel_perm (List.mergeSort_perm _ _)

/-! ## Lookup by two binary searches -/

/-- The search kernel's 8-byte answer read back as an index. -/
def probe (s : QSortedRel) (right : Bool) (k : Int64) : Int := (bitsAt (s.keys.bin right k) 0 8).toInt64.toInt

/-- The run of `k`: from the least index with `k ≤ key` (`binr`) to one past the last with `key ≤ k`
(`bin`). An answer is an `Int64`, so below `2^63` pairs the searches are read back; at or above it the
pairs are scanned, which no `ByteArray` in memory reaches. -/
def lookup (s : QSortedRel) (k : Int64) : List Int64 :=
  if s.count < 2 ^ 63 then
    let lo := (s.probe true k).toNat
    (List.range' lo ((s.probe false k + 1).toNat - lo)).map (at8 s.vals)
  else (List.range s.count).filterMap fun i => if s.keys.get i = k then some (at8 s.vals i) else none

/-- `Keys.bin_spec` at a `QSortedRel`, read back. -/
theorem probe_spec (s : QSortedRel) (right : Bool) (k : Int64) (hn : s.count < 2 ^ 63) :
    ∃ r, r ≤ s.count ∧ s.probe right k = (if right then (r : Int) else (r : Int) - 1) ∧
      (∀ j, j < r → if right then (s.keys.get j).toInt < k.toInt else (s.keys.get j).toInt ≤ k.toInt) ∧
      (r < s.count → if right then k.toInt ≤ (s.keys.get r).toInt else k.toInt < (s.keys.get r).toInt) := by
  obtain ⟨r, hr, hout, hlo, hhi⟩ := s.keys.bin_spec right k s.fits hn s.sorted
  refine ⟨r, hr, hout, fun j hj => ?_, fun h => ?_⟩
  · have := hlo j hj
    cases right
    · exact Int64.le_iff_toInt_le.1 this
    · exact Int64.lt_iff_toInt_lt.1 this
  · have := hhi h
    cases right
    · exact Int64.lt_iff_toInt_lt.1 this
    · exact Int64.le_iff_toInt_le.1 this

theorem mem_lookup {s : QSortedRel} {k v : Int64} :
    v ∈ s.lookup k ↔ ∃ i, i < s.count ∧ s.keys.get i = k ∧ at8 s.vals i = v := by
  unfold lookup
  split
  · rename_i hn
    obtain ⟨r1, hr1, e1, lo1, hi1⟩ := probe_spec s true k hn
    obtain ⟨r2, hr2, e2, lo2, hi2⟩ := probe_spec s false k hn
    simp only [↓reduceIte, Bool.false_eq_true] at e1 e2 lo1 lo2 hi1 hi2
    rw [e1, e2, show ((r2 : Int) - 1 + 1).toNat = r2 by omega, Int.toNat_natCast]
    have mono : ∀ i j, i ≤ j → j < s.count → (s.keys.get i).toInt ≤ (s.keys.get j).toInt :=
      fun i j hij hj => Int64.le_iff_toInt_le.1 (s.sorted i j hij hj)
    simp only [List.mem_map, List.mem_range'_1]
    constructor
    · rintro ⟨i, ⟨hl, hh⟩, rfl⟩
      have h1 := lo2 i (by omega)
      have h2 := hi1 (by omega)
      have h3 := mono r1 i hl (by omega)
      exact ⟨i, by omega, Int64.toInt_inj.1 (by omega), rfl⟩
    · rintro ⟨i, hi, hk, rfl⟩
      have a : r1 ≤ i := Nat.not_lt.1 fun h => by have := lo1 i h; rw [hk] at this; omega
      have b : i < r2 := Nat.lt_of_not_le fun h => by
        have := hi2 (by omega); have := mono r2 i h hi; rw [hk] at this; omega
      exact ⟨i, ⟨a, by omega⟩, rfl⟩
  · simp only [List.mem_filterMap, List.mem_range]
    constructor
    · rintro ⟨i, hi, he⟩
      split at he
      · exact ⟨i, hi, by assumption, Option.some.inj he⟩
      · cases he
    · rintro ⟨i, hi, hk, rfl⟩
      exact ⟨i, hi, by rw [if_pos hk]⟩

/-- **`graph(lookup(s)) ∋ = rep(s)`**, as `SortedRel.lookup_rep`. -/
theorem lookup_rep (s : QSortedRel) : (graph s.lookup : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨List Int64⟩) ≫ lmem Int64 = s.rep :=
  hom_ext fun _ _ => ⟨fun ⟨_, hl, hv⟩ => mem_rep.2 (mem_lookup.1 (hl ▸ hv)),
    fun h => ⟨_, rfl, mem_lookup.2 (mem_rep.1 h)⟩⟩

end QSortedRel

end LeetQ
