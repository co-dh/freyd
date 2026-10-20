/-
  `SortedRel`'s interface — `rep`, `ofList`, `lookup`, and the laws `rep_ofList`, `lookup_rep` — over
  qlean's dense `long` columns: the keys and the values are the payloads of two `Column.bytes`, read
  through `Column.bitsAt`, and `lookup` is qlean's `binBytes` (the Lean body of its C `bin`) twice.
  Every statement is over the bits, never `Column.atoms`/`Column.raw`, which carry `Classical.choice`.
-/
import AOP.A6_FinRel
import QLean.Verify.Search
import QLean.Verify.Raw

namespace LeetQ

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- An `Int64` denotes a number in `[-2^63, 2^63)`. Core's `Int64.le_toInt`/`Int64.toInt_lt` say it
through `BitVec.le_toInt`, which carries `Classical.choice`; this reads `BitVec.toInt`'s definition.
`by_cases` rather than `split`, whose `ite` case split brings `Classical.choice` too. -/
theorem toInt_bounds (b : Int64) : -2 ^ 63 ≤ b.toInt ∧ b.toInt < 2 ^ 63 := by
  have h : b.toBitVec.toNat < 2 ^ 64 := b.toBitVec.toFin.isLt
  show -2 ^ 63 ≤ (if 2 * b.toBitVec.toNat < 2 ^ 64 then (b.toBitVec.toNat : Int)
      else (b.toBitVec.toNat : Int) - 2 ^ 64) ∧ (if 2 * b.toBitVec.toNat < 2 ^ 64
      then (b.toBitVec.toNat : Int) else (b.toBitVec.toNat : Int) - 2 ^ 64) < 2 ^ 63
  by_cases hc : 2 * b.toBitVec.toNat < 2 ^ 64
  · rw [if_pos hc]; exact ⟨by omega, by omega⟩
  · rw [if_neg hc]; exact ⟨by omega, by omega⟩

/-! ## A dense `long` payload -/

/-- The `i`th `Int64` of a dense payload. -/
def at8 (b : ByteArray) (i : Nat) : Int64 := (bitsAt b (i * 8) 8).toInt64

/-- `xs` laid out as a dense `long` payload. -/
def enc (xs : List Int64) : ByteArray := xs.foldl (fun b x => pushBits b x.toUInt64 8) ByteArray.empty

theorem foldl_size (xs : List Int64) (b : ByteArray) :
    (xs.foldl (fun b x => pushBits b x.toUInt64 8) b).size = b.size + 8 * xs.length := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, pushBits_size, List.length_cons]; omega

theorem foldl_stable (xs : List Int64) (b : ByteArray) (o : Nat) (h : o + 8 ≤ b.size) :
    bitsAt (xs.foldl (fun b x => pushBits b x.toUInt64 8) b) o 8 = bitsAt b o 8 := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih _ (by rw [pushBits_size]; omega)]
    exact bitsAt_congr _ _ _ _ fun k hk => pushBits_getElem?_lt _ _ _ _ (by omega)

theorem foldl_at (xs : List Int64) (b : ByteArray) (i : Nat) (hi : i < xs.length) :
    bitsAt (xs.foldl (fun b x => pushBits b x.toUInt64 8) b) (b.size + i * 8) 8 = xs[i].toUInt64 := by
  induction xs generalizing b i with
  | nil => simp at hi
  | cons x xs ih =>
    rw [List.foldl_cons]
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.add_zero, foldl_stable _ _ _ (by rw [pushBits_size]; omega)]
      exact bitsAt_pushBits8 b _
    | succ i =>
      have := ih (pushBits b x.toUInt64 8) i (by simp at hi; omega)
      rw [pushBits_size] at this
      rw [show b.size + (i + 1) * 8 = b.size + 8 + i * 8 by omega, this]
      rfl

theorem enc_size (xs : List Int64) : (enc xs).size = 8 * xs.length := by
  rw [enc, foldl_size]; simp

theorem at8_enc (xs : List Int64) (i : Nat) (hi : i < xs.length) : at8 (enc xs) i = xs[i] := by
  have := foldl_at xs ByteArray.empty i hi
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add] at this
  rw [at8, enc, this, Int64.toInt64_toUInt64]

/-- `ascending .i64` over the first `n` elements, as the index form `binBytes_long` takes. -/
theorem sorted_of_ascending (b : ByteArray) (hn : b.size / 8 < USize.size)
    (h : Order.ascending .i64 false false (USize.ofNat (b.size / 8)) b = true) :
    ∀ i j, i ≤ j → j < b.size / 8 → at8 b i ≤ at8 b j := by
  rw [ascending_i64_iff, USize.toNat_ofNat_of_lt' hn, Nat.min_self] at h
  intro i j hij hj
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · have := List.pairwise_iff_getElem.1 h i j (by simp; omega) (by simp; omega) hlt
    simp only [List.getElem_map, List.getElem_range] at this
    exact this
  · exact Int64.le_iff_toInt_le.2 (Int.le_refl _)

/-! ## The structure -/

/-- A finite relation `Int64 ⟶ Int64` as two dense `long` columns, `Column.bytes keys` and
`Column.bytes vals`, the keys ascending. -/
structure QSortedRel where
  keys : ByteArray
  vals : ByteArray
  len : vals.size / 8 = keys.size / 8
  sorted : ∀ i j, i ≤ j → j < keys.size / 8 → at8 keys i ≤ at8 keys j

namespace QSortedRel

/-- The number of pairs. -/
def count (s : QSortedRel) : Nat := s.keys.size / 8

/-- The pairs, read off the two columns. -/
def toList (s : QSortedRel) : List (Int64 × Int64) :=
  (List.range s.count).map fun i => (at8 s.keys i, at8 s.vals i)

/-- The relation the columns denote. -/
def rep (s : QSortedRel) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩ := rel s.toList

theorem mem_rep {s : QSortedRel} {k v : Int64} :
    s.rep k v ↔ ∃ i, i < s.count ∧ at8 s.keys i = k ∧ at8 s.vals i = v := by
  show (k, v) ∈ s.toList ↔ _
  simp only [toList, List.mem_map, List.mem_range, Prod.mk.injEq]

/-- Two columns checked by the C `ascending` kernel, whose Lean body `ascending_i64_iff` reads. -/
def ofBytes? (keys vals : ByteArray) : Option QSortedRel :=
  if h : keys.size / 8 < USize.size ∧ vals.size / 8 = keys.size / 8 ∧
      Order.ascending .i64 false false (USize.ofNat (keys.size / 8)) keys = true then
    some ⟨keys, vals, h.2.1, sorted_of_ascending keys h.1 h.2.2⟩
  else none

/-- The key order the sort uses. -/
def keyLE (a b : Int64 × Int64) : Bool := decide (a.1.toInt ≤ b.1.toInt)

/-- Sort the pairs by key, then lay them out as two columns. -/
def ofList (l : List (Int64 × Int64)) : QSortedRel where
  keys := enc ((l.mergeSort keyLE).map Prod.fst)
  vals := enc ((l.mergeSort keyLE).map Prod.snd)
  len := by simp [enc_size]
  sorted := fun i j hij hj => by
    have hm := List.pairwise_mergeSort (le := keyLE)
      (fun a b c h1 h2 => by simp only [keyLE, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [keyLE, Bool.or_eq_true, decide_eq_true_eq]; omega) l
    rw [enc_size, List.length_map, Nat.mul_div_cancel_left _ (by decide)] at hj
    rw [at8_enc _ _ (by simp only [List.length_map]; omega), at8_enc _ _ (by simp only [List.length_map]; omega), List.getElem_map, List.getElem_map]
    rcases Nat.lt_or_eq_of_le hij with hlt | rfl
    · have := List.pairwise_iff_getElem.1 hm i j (by omega) hj hlt
      simp only [keyLE, decide_eq_true_eq] at this
      exact Int64.le_iff_toInt_le.2 this
    · exact Int64.le_iff_toInt_le.2 (Int.le_refl _)

theorem toList_ofList (l : List (Int64 × Int64)) : (ofList l).toList = l.mergeSort keyLE := by
  apply List.ext_getElem
  · simp [toList, count, ofList, enc_size]
  · intro i h1 h2
    simp only [toList, List.getElem_map, List.getElem_range, ofList]
    rw [at8_enc _ _ (by simp only [List.length_map]; omega), at8_enc _ _ (by simp only [List.length_map]; omega), List.getElem_map, List.getElem_map]

/-- **`rep(ofList(l)) = rel(l)`**, as `FinRel.rep_ofList`. -/
theorem rep_ofList (l : List (Int64 × Int64)) : (ofList l).rep = rel l := by
  show rel _ = _
  rw [toList_ofList]
  exact rel_perm (List.mergeSort_perm _ _)

/-! ## Lookup by two binary searches -/

/-- `binBytes`' 8-byte answer read back as an index. -/
def probe (s : QSortedRel) (right : Bool) (k : Int64) : Int :=
  (bitsAt (binBytes 8 false true right s.keys (pushBits ByteArray.empty k.toUInt64 8)) 0 8).toInt64.toInt

/-- The run of `k`: from the least index with `k ≤ key` (`binr`) to one past the last with `key ≤ k`
(`bin`). An answer is an `Int64`, so below `2^63` pairs the searches are read back; at or above it the
pairs are scanned, which no `ByteArray` in memory reaches. -/
def lookup (s : QSortedRel) (k : Int64) : List Int64 :=
  if s.count < 2 ^ 63 then
    let lo := (s.probe true k).toNat
    (List.range' lo ((s.probe false k + 1).toNat - lo)).map (at8 s.vals)
  else (List.range s.count).filterMap fun i => if at8 s.keys i = k then some (at8 s.vals i) else none

/-- `binBytes_long` at a `QSortedRel`, read back. -/
theorem probe_spec (s : QSortedRel) (right : Bool) (k : Int64) (hn : s.count < 2 ^ 63) :
    ∃ r, r ≤ s.count ∧ s.probe right k = (if right then (r : Int) else (r : Int) - 1) ∧
      (∀ j, j < r → if right then (at8 s.keys j).toInt < k.toInt else (at8 s.keys j).toInt ≤ k.toInt) ∧
      (r < s.count → if right then k.toInt ≤ (at8 s.keys r).toInt else k.toInt < (at8 s.keys r).toInt) := by
  obtain ⟨r, hr, hout, hlo, hhi⟩ := binBytes_long right s.keys k.toUInt64 s.sorted
  rw [Int64.toInt64_toUInt64] at hlo hhi
  refine ⟨r, hr, ?_, fun j hj => ?_, fun h => ?_⟩
  · have hc : s.keys.size / 8 = s.count := rfl
    rw [probe, hout, Int64.toInt64_toUInt64]
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact Int64.toInt_ofInt_of_le (by omega) (by omega)
  · have := hlo j hj
    cases right
    · exact Int64.le_iff_toInt_le.1 this
    · exact Int64.lt_iff_toInt_lt.1 this
  · have := hhi h
    cases right
    · exact Int64.lt_iff_toInt_lt.1 this
    · exact Int64.le_iff_toInt_le.1 this

theorem mem_lookup {s : QSortedRel} {k v : Int64} :
    v ∈ s.lookup k ↔ ∃ i, i < s.count ∧ at8 s.keys i = k ∧ at8 s.vals i = v := by
  unfold lookup
  split
  · rename_i hn
    obtain ⟨r1, hr1, e1, lo1, hi1⟩ := probe_spec s true k hn
    obtain ⟨r2, hr2, e2, lo2, hi2⟩ := probe_spec s false k hn
    simp only [↓reduceIte, Bool.false_eq_true] at e1 e2 lo1 lo2 hi1 hi2
    rw [e1, e2, show ((r2 : Int) - 1 + 1).toNat = r2 by omega, Int.toNat_natCast]
    have mono : ∀ i j, i ≤ j → j < s.count → (at8 s.keys i).toInt ≤ (at8 s.keys j).toInt :=
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
