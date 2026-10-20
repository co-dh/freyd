/-
  `SortedRel`'s interface — `rep`, `ofList`, `lookup`, and the laws `rep_ofList`, `lookup_rep` — over
  qlean columns. The keys are signed integers, either a dense payload of any width up to eight bytes
  (q's `short`, `int`, `long`), searched by `binBytes` (the Lean body of qlean's C `bin`), or a `long`
  column Frame-of-Reference encoded, read through `Column.foRBits` and searched by `foRBin`, so they
  stay compressed during `lookup`. The values are any column's reader `Nat → V`. Everything past
  `Keys` is stated once over every key and value column.
  Every statement is over the bits, never `Column.atoms`/`Column.raw`, which carry `Classical.choice`.
-/
import AOP.A6_FinRel
import QLean.Verify.Search
import QLean.Verify.Raw

namespace LeetQ

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-! ## A count as a `USize`

`USize.size` is `2 ^ System.Platform.numBits`, opaque to the kernel, so a count's `toUSize` round
trip is stated from a bound every platform meets. -/

theorem lt_usize {n : Nat} (h : n < 2 ^ 32) : n < USize.size := by
  cases System.Platform.numBits_eq <;> simp [USize.size, *] <;> omega

theorem toNat_toUSize {n : Nat} (h : n < 2 ^ 32) : (Nat.toUSize n).toNat = n :=
  USize.toNat_ofNat_of_lt' (lt_usize h)

/-! ## A dense payload of `w`-byte signed integers -/

/-- Half the range of a `w`-byte integer: it holds `[-half w, half w)`. -/
def half (w : Nat) : Nat := 2 ^ (8 * w - 1)

/-- `x` fits `w` bytes as a two's-complement number. -/
def Fits (w : Nat) (x : Int64) : Prop := w ≤ 8 ∧ -(half w : Int) ≤ x.toInt ∧ x.toInt < half w

instance (w : Nat) (x : Int64) : Decidable (Fits w x) := inferInstanceAs (Decidable (_ ∧ _))

theorem sx_bounds {w : Nat} (v : UInt64) : -(half w : Int) ≤ sx w v ∧ sx w v < half w := by
  have : 2 ^ (8 * w) ≤ 2 * 2 ^ (8 * w - 1) := by
    rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by omega) (by omega)
  have := Nat.mod_lt v.toNat (Nat.two_pow_pos (8 * w))
  -- one `omega` per conjunct: `omega` on a conjunction negates it through `Classical.choice`
  unfold half; refine ⟨?_, ?_⟩ <;> unfold sx <;> split <;> omega

/-- The `i`th element of a dense payload of `w`-byte signed integers, widened to `Int64`. -/
def atW (w : Nat) (b : ByteArray) (i : Nat) : Int64 := (sx w (bitsAt b (i * w) w)).toInt64

theorem half_le {w : Nat} (h : w ≤ 8) : half w ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)

theorem toInt_atW {w : Nat} (h : w ≤ 8) (b : ByteArray) (i : Nat) : (atW w b i).toInt = sx w (bitsAt b (i * w) w) := by
  have := sx_bounds (w := w) (bitsAt b (i * w) w); have := half_le h
  exact Int64.toInt_ofInt_of_le (by omega) (by omega)

/-- At eight bytes `sx` is `UInt64.toInt64`, what qlean's `long` theorems read. -/
theorem sx_eight (v : UInt64) : sx 8 v = v.toInt64.toInt := by
  rw [toInt_toInt64]
  have := v.toNat_lt
  simp only [sx, Nat.reduceMul, Nat.reduceSub]
  rw [Nat.mod_eq_of_lt this]
  split <;> omega

theorem atW_eight (b : ByteArray) (i : Nat) : atW 8 b i = (bitsAt b (i * 8) 8).toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_atW (by decide), sx_eight])

/-- A `w`-byte read of an `x` that fits is `x`. -/
theorem sx_fits {w : Nat} (h1 : 1 ≤ w) {x : Int64} (h : Fits w x) : sx w x.toUInt64 = x.toInt := by
  have e := toInt_toInt64 x.toUInt64
  rw [Int64.toInt64_toUInt64] at e
  have := x.toUInt64.toNat_lt
  obtain ⟨h8, hl, hh⟩ := h
  have hw : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 := by omega
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sx, half, Nat.reduceMul, Nat.reduceSub, Nat.reducePow] at hl hh e ⊢ <;>
    split at e <;> split <;> omega

/-- `xs` laid out as a dense payload of `w`-byte integers. -/
def enc (w : Nat) (xs : List Int64) : ByteArray := xs.foldl (fun b x => pushBits b x.toUInt64 w) ByteArray.empty

theorem enc_size {w : Nat} (hw : w ≤ 8) (xs : List Int64) : (enc w xs).size = w * xs.length := by
  rw [enc, (foldl_pushBits Int64.toUInt64 w hw xs ByteArray.empty).1, show ByteArray.empty.size = 0 from rfl,
    Nat.zero_add]

theorem atW_enc {w : Nat} (h1 : 1 ≤ w) (xs : List Int64) (i : Nat) (hi : i < xs.length) (hf : Fits w xs[i]) :
    atW w (enc w xs) i = xs[i] := by
  have := (foldl_pushBits Int64.toUInt64 w hf.1 xs ByteArray.empty).2.2 i hi
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, Nat.mul_comm] at this
  apply Int64.toInt_inj.1
  rw [toInt_atW hf.1, enc, this, sx_mod hf.1, sx_fits h1 hf]

/-- Every `Int64` fits eight bytes. -/
theorem fits_eight (x : Int64) : Fits 8 x := by
  have := toInt_bounds x; exact ⟨by decide, by simp only [half]; omega, by simp only [half]; omega⟩

/-- The narrowest of q's `short`, `int` and `long` that holds every element of `xs`. -/
def narrow (xs : List Int64) : Nat :=
  if xs.all (fun x => decide (Fits 2 x)) then 2 else if xs.all (fun x => decide (Fits 4 x)) then 4 else 8

theorem narrow_pos (xs : List Int64) : 1 ≤ narrow xs ∧ narrow xs ≤ 8 := by
  unfold narrow; split
  · decide
  · split <;> decide

theorem fits_narrow {xs : List Int64} {x : Int64} (h : x ∈ xs) : Fits (narrow xs) x := by
  unfold narrow
  split
  · rename_i ha; exact of_decide_eq_true (List.all_eq_true.1 ha x h)
  · split
    · rename_i ha; exact of_decide_eq_true (List.all_eq_true.1 ha x h)
    · exact fits_eight x

/-- A value column: element `i` read by `get`. A structure and not a function `Nat → V`, because the
compiler eta-expands a function-valued definition, which would rebuild the column at every read. -/
structure ValCol (V : Type) where
  get : Nat → V

/-- A list of `Int64`s as a dense value column at its narrowest width. -/
def dense (vs : List Int64) : ValCol Int64 := ⟨atW (narrow vs) (enc (narrow vs) vs)⟩

theorem dense_get (vs : List Int64) (i : Nat) (hi : i < vs.length) : (dense vs).get i = vs[i] :=
  atW_enc (narrow_pos vs).1 vs i hi (fits_narrow (List.getElem_mem hi))

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

/-! ## A key column, dense or encoded -/

/-- A key column: a dense payload of `w`-byte signed integers, or `n` `long`s Frame-of-Reference
encoded as `(metadata, pack)`, which `foRBin` searches without the caller decoding it. -/
inductive Keys
  | dense (w : Nat) (b : ByteArray)
  | foR (n : Nat) (md pk : ByteArray)

/-- The answer a search kernel writes for partition point `r`: `r` for `binr`, `r - 1` for `bin`. -/
def ans (right : Bool) (r : Nat) : ByteArray :=
  pushBits ByteArray.empty (if right then (r : Int) else (r : Int) - 1).toInt64.toUInt64 8

theorem ans_spec (right : Bool) (r : Nat) (h : r < 2 ^ 63) :
    (bitsAt (ans right r) 0 8).toInt64.toInt = if right then (r : Int) else (r : Int) - 1 := by
  have hb := bitsAt_pushBits8 ByteArray.empty (if right then (r : Int) else (r : Int) - 1).toInt64.toUInt64
  rw [show ByteArray.empty.size = 0 from rfl] at hb
  rw [ans, hb, Int64.toInt64_toUInt64]
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> exact Int64.toInt_ofInt_of_le (by omega) (by omega)

namespace Keys

/-- The number of keys. -/
def count : Keys → Nat
  | .dense w b => b.size / w
  | .foR n _ _ => n

/-- The `i`th key. -/
def get : Keys → Nat → Int64
  | .dense w b, i => atW w b i
  | .foR _ md pk, i => (foRBits md pk (blockStarts md) i).toInt64

/-- The search kernel's 8-byte answer for needle `k`. A needle no `w`-byte key can equal sits below
every key or above every one, so the dense column answers it without a search. The width is passed
as `USize.ofNatLT`, whose `toNat` the kernel reduces, where `Nat.toUSize`'s stops at `numBits`. -/
def bin (right : Bool) (k : Int64) : Keys → ByteArray
  | .dense w b =>
    if h : Fits w k then
      binBytes (USize.ofNatLT w (lt_usize (by have := h.1; omega))) false true right b (pushBits ByteArray.empty k.toUInt64 w)
    else ans right (if k.toInt < 0 then 0 else b.size / w)
  | .foR n md pk => foRBin 8 right md pk n.toUSize (pushBits ByteArray.empty k.toUInt64 8)

/-- What the searches need beyond order: a width `binBytes_signed` reads, a count that survives
`Nat.toUSize`. -/
def fits : Keys → Prop
  | .dense w _ => 1 ≤ w ∧ w ≤ 8
  | .foR n _ _ => n < USize.size

/-- `binBytes_signed` and `foRBin_signed`, one statement over the key reader. -/
theorem bin_spec (c : Keys) (right : Bool) (k : Int64) (hf : c.fits) (hn : c.count < 2 ^ 63)
    (hs : ∀ i j, i ≤ j → j < c.count → c.get i ≤ c.get j) :
    ∃ r, r ≤ c.count ∧ (bitsAt (c.bin right k) 0 8).toInt64.toInt = (if right then (r : Int) else (r : Int) - 1) ∧
      (∀ j, j < r → if right then c.get j < k else c.get j ≤ k) ∧
      (r < c.count → if right then k ≤ c.get r else k < c.get r) := by
  cases c with
  | dense w b =>
    simp only [bin]
    split
    · rename_i hk
      have tr : ∀ j, sx w (bitsAt b (j * w) w) = (get (.dense w b) j).toInt := fun j => (toInt_atW hf.2 b j).symm
      obtain ⟨r, hr, hout, hlo, hhi⟩ := binBytes_signed hf.1 hf.2 _ USize.toNat_ofNatLT right b k.toUInt64 hn
        fun i j hij hj => by rw [tr, tr]; exact Int64.le_iff_toInt_le.1 (hs i j hij hj)
      refine ⟨r, hr, hout, fun j hj => ?_, fun h => ?_⟩
      · have := hlo j hj
        cases right <;> simp only [tr, sx_fits hf.1 hk, Bool.false_eq_true, ↓reduceIte, Int64.lt_iff_toInt_lt,
          Int64.le_iff_toInt_le] at this ⊢ <;> exact this
      · have := hhi h
        cases right <;> simp only [tr, sx_fits hf.1 hk, Bool.false_eq_true, ↓reduceIte, Int64.lt_iff_toInt_lt,
          Int64.le_iff_toInt_le] at this ⊢ <;> exact this
    · rename_i hk
      have hh : 0 < half w := Nat.two_pow_pos _
      have hb : ∀ j, -(half w : Int) ≤ (atW w b j).toInt ∧ (atW w b j).toInt < half w := fun j => by
        rw [toInt_atW hf.2]; exact sx_bounds _
      have hko : k.toInt < -(half w : Int) ∨ half w ≤ k.toInt := by
        by_cases a : -(half w : Int) ≤ k.toInt
        · by_cases c : k.toInt < half w
          · exact absurd ⟨hf.2, a, c⟩ hk
          · omega
        · omega
      have hn' : b.size / w < 2 ^ 63 := hn
      by_cases hneg : k.toInt < 0
      · refine ⟨0, Nat.zero_le _, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ => ?_⟩
        · rw [if_pos hneg]; exact ans_spec right 0 (by omega)
        · have := hb 0
          cases right <;> simp only [get, Bool.false_eq_true, ↓reduceIte, Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le] <;> omega
      · refine ⟨b.size / w, Nat.le_refl _, ?_, fun j hj => ?_, fun hr => absurd hr (Nat.lt_irrefl _)⟩
        · rw [if_neg hneg]; exact ans_spec right _ hn'
        · have := hb j
          cases right <;> simp only [get, Bool.false_eq_true, ↓reduceIte, Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le] <;> omega
  | foR n md pk =>
    have tr : ∀ v, sx 8 v = v.toInt64.toInt := sx_eight
    obtain ⟨r, hr, hout, hlo, hhi⟩ := foRBin_signed (by decide) (by decide) 8
      (USize.toNat_ofNat_of_lt' (lt_usize (by decide))) right n md pk k.toUInt64 hf hn
      fun i j hij hj => by rw [tr, tr]; exact Int64.le_iff_toInt_le.1 (hs i j hij hj)
    refine ⟨r, hr, hout, fun j hj => ?_, fun h => ?_⟩
    · have := hlo j hj
      cases right <;> simp only [tr, Int64.toInt64_toUInt64, Bool.false_eq_true, ↓reduceIte,
        Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le] at this ⊢ <;> exact this
    · have := hhi h
      cases right <;> simp only [tr, Int64.toInt64_toUInt64, Bool.false_eq_true, ↓reduceIte,
        Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le] at this ⊢ <;> exact this

/-- `ks` as a key column, encoded when `foR` asks and the count fits a `USize`, which every list in
memory does; otherwise dense at its narrowest width. -/
def ofList (foR : Bool) (ks : List Int64) : Keys :=
  if foR = true ∧ ks.length < USize.size then
    let e := Coc.encode (Nat.toUSize 8) (enc 8 ks)
    .foR ks.length e.1 e.2
  else .dense (narrow ks) (enc (narrow ks) ks)

theorem count_ofList (foR : Bool) (ks : List Int64) : (ofList foR ks).count = ks.length := by
  unfold ofList
  by_cases h : foR = true ∧ ks.length < USize.size
  · rw [if_pos h]; rfl
  · rw [if_neg h]; show (enc _ ks).size / _ = _
    have := narrow_pos ks
    rw [enc_size this.2, Nat.mul_div_cancel_left _ (by omega)]

theorem fits_ofList (foR : Bool) (ks : List Int64) : (ofList foR ks).fits := by
  unfold ofList
  by_cases h : foR = true ∧ ks.length < USize.size
  · rw [if_pos h]; exact h.2
  · rw [if_neg h]; exact narrow_pos ks

/-- The encoded keys read back through `foRBits_encode_bits`, the dense ones through `atW_enc`. -/
theorem get_ofList (foR : Bool) (ks : List Int64) (i : Nat) (hi : i < ks.length) :
    (ofList foR ks).get i = ks[i] := by
  unfold ofList
  by_cases h : foR = true ∧ ks.length < USize.size
  · rw [if_pos h]
    have e := foRBits_encode_bits 8 (by decide) (by decide) (enc 8 ks) i (by rw [enc_size (by decide)]; omega)
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _)] at e
    show (foRBits _ _ _ i).toInt64 = _
    rw [UInt64.toNat_inj.1 e, ← atW_eight]
    exact atW_enc (by decide) ks i hi (fits_eight _)
  · rw [if_neg h]; exact atW_enc (narrow_pos ks).1 ks i hi (fits_narrow (List.getElem_mem hi))

end Keys

/-! ## The structure -/

/-- A finite relation `Int64 ⟶ V` as a key column, the keys ascending, and a value column read
through `val`: a dense payload (`dense`), an ALP float column, any reader by index. -/
structure QSortedRel (V : Type) where
  keys : Keys
  val : Nat → V
  sorted : ∀ i j, i ≤ j → j < keys.count → keys.get i ≤ keys.get j
  fits : keys.fits

namespace QSortedRel

variable {V : Type}

/-- The number of pairs. -/
def count (s : QSortedRel V) : Nat := s.keys.count

/-- The pairs, read off the two columns. -/
def toList (s : QSortedRel V) : List (Int64 × V) :=
  (List.range s.count).map fun i => (s.keys.get i, s.val i)

/-- The relation the columns denote. -/
def rep (s : QSortedRel V) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨V⟩ := rel s.toList

theorem mem_rep {s : QSortedRel V} {k : Int64} {v : V} :
    s.rep k v ↔ ∃ i, i < s.count ∧ s.keys.get i = k ∧ s.val i = v := by
  show (k, v) ∈ s.toList ↔ _
  simp only [toList, List.mem_map, List.mem_range, Prod.mk.injEq]

/-- Two dense `long` columns, the keys checked by the C `ascending` kernel, whose Lean body
`ascending_i64_iff` reads. -/
def ofBytes? (keys vals : ByteArray) : Option (QSortedRel Int64) :=
  if h : keys.size / 8 < USize.size ∧ vals.size / 8 = keys.size / 8 ∧
      Order.ascending .i64 false false (USize.ofNat (keys.size / 8)) keys = true then
    some ⟨.dense 8 keys, atW 8 vals, fun i j hij hj => by
      have := sorted_of_pairwise _ _ (by
        have := (ascending_i64_iff false false _ keys).1 h.2.2
        rwa [USize.toNat_ofNat_of_lt' h.1, Nat.min_self] at this) i j hij hj
      simpa only [Keys.get, atW_eight] using this, ⟨by decide, by decide⟩⟩
  else none

/-- An encoded key column of `n` elements checked by the C `ascendingFoR`, whose Lean body
`ascendingFoR_i64_iff` reads, beside a dense `long` value column. -/
def ofFoR? (n : Nat) (md pk vals : ByteArray) : Option (QSortedRel Int64) :=
  if h : n < USize.size ∧ vals.size / 8 = n ∧ Order.ascendingFoR .i64 false false n.toUSize md pk = true then
    some ⟨.foR n md pk, atW 8 vals, sorted_of_pairwise _ _ (by
      have := (ascendingFoR_i64_iff false false _ md pk).1 h.2.2
      rwa [USize.toNat_ofNat_of_lt' h.1] at this), h.1⟩
  else none

/-- The key order the sort uses. -/
def keyLE (a b : Int64 × V) : Bool := decide (a.1.toInt ≤ b.1.toInt)

/-- Sort the pairs by key, then lay them out as two columns: the keys encoded when `foR`, the values
by `col`, whose read-back law is what `rep_ofList` asks of it. -/
def ofList (l : List (Int64 × V)) (col : List V → ValCol V) (foR : Bool := false) : QSortedRel V where
  keys := Keys.ofList foR ((l.mergeSort keyLE).map Prod.fst)
  val := (col ((l.mergeSort keyLE).map Prod.snd)).get
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

theorem toList_ofList (l : List (Int64 × V)) (col : List V → ValCol V)
    (hcol : ∀ vs i (h : i < vs.length), (col vs).get i = vs[i]) (foR : Bool) :
    (ofList l col foR).toList = l.mergeSort keyLE := by
  apply List.ext_getElem
  · simp [toList, count, ofList, Keys.count_ofList]
  · intro i h1 h2
    simp only [toList, List.getElem_map, List.getElem_range, ofList]
    rw [Keys.get_ofList _ _ _ (by simp only [List.length_map]; omega),
      hcol _ _ (by simp only [List.length_map]; omega), List.getElem_map, List.getElem_map]

/-- **`rep(ofList(l)) = rel(l)`**, as `FinRel.rep_ofList`, dense or encoded, for any value column
that reads back what it was built from. -/
theorem rep_ofList (l : List (Int64 × V)) (col : List V → ValCol V)
    (hcol : ∀ vs i (h : i < vs.length), (col vs).get i = vs[i]) (foR : Bool) : (ofList l col foR).rep = rel l := by
  show rel _ = _
  rw [toList_ofList _ _ hcol]
  exact rel_perm (List.mergeSort_perm _ _)

/-! ## Lookup by two binary searches -/

/-- The search kernel's 8-byte answer read back as an index. -/
def probe (s : QSortedRel V) (right : Bool) (k : Int64) : Int := (bitsAt (s.keys.bin right k) 0 8).toInt64.toInt

/-- The run of `k`: from the least index with `k ≤ key` (`binr`) to one past the last with `key ≤ k`
(`bin`). An answer is an `Int64`, so below `2^63` pairs the searches are read back; at or above it the
pairs are scanned, which no `ByteArray` in memory reaches. -/
def lookup (s : QSortedRel V) (k : Int64) : List V :=
  if s.count < 2 ^ 63 then
    let lo := (s.probe true k).toNat
    (List.range' lo ((s.probe false k + 1).toNat - lo)).map s.val
  else (List.range s.count).filterMap fun i => if s.keys.get i = k then some (s.val i) else none

/-- `Keys.bin_spec` at a `QSortedRel`, read back. -/
theorem probe_spec (s : QSortedRel V) (right : Bool) (k : Int64) (hn : s.count < 2 ^ 63) :
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

theorem mem_lookup {s : QSortedRel V} {k : Int64} {v : V} :
    v ∈ s.lookup k ↔ ∃ i, i < s.count ∧ s.keys.get i = k ∧ s.val i = v := by
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
theorem lookup_rep (s : QSortedRel V) : (graph s.lookup : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨List V⟩) ≫ lmem V = s.rep :=
  hom_ext fun _ _ => ⟨fun ⟨_, hl, hv⟩ => mem_rep.2 (mem_lookup.1 (hl ▸ hv)),
    fun h => ⟨_, rfl, mem_lookup.2 (mem_rep.1 h)⟩⟩

end QSortedRel

end LeetQ
