/-
  q's `sum`, `where`, `sum v where b` and `select sum v by k` run on qlean's compressed columns: a
  value column is a `Keys` (`QRel.lean`), a dense `w`-byte payload or a Frame-of-Reference pack, and
  every element is read from the packed bytes (`atW`, `foRBits`) — no operator here builds the decoded
  value list. `Keys.vals`, that list, appears only in the statements, as the meaning of the column.
  Each operator is stated against the `.pairs` pipeline it implements (`Q.Agg.ql`, `RelRep.comp`,
  `Q.Agg.sum`, `Q.xkey`), at list level: order and repeats are part of what is equal.
  * `sum` is qlean's `overBytes .add` on a dense payload and `Coc.over .add` on a pack, whose C reads
    each block's metadata; `sum_spec`: `ql(vs) ; (≠ 0N)? ; toInt ; sum`, wrapped to 64 bits.
  * `sumWhere` folds the indices `whereBits` answers, reading `v` at each; `sumWhere_spec`:
    `ql(where b) ; ql(vs) ; (≠ 0N)? ; toInt ; sum`.
  * `selbySum` sums `v` over each bucket `Order.group`/`groupFoR` answers on the key column;
    `selbySum_spec`: each key's sum is q's sum of `xkey`'s fibre, the per-key entry of `app?_selby`.
  q's `sum` skips the null `nul` and wraps at 64 bits, as `Coc.Over.step .add` does.
-/
import LeetQ.Group
import LeetQ.Q.Agg
import LeetQ.Q.Table

namespace LeetQ.Compressed

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ LeetQ.Group

/-! ## `.pairs` pipelines read back as lists -/

section Pairs

variable {K V C : Type}

theorem vals_ofList (L : List (K × V)) : (FinRel.ofList L).vals.toList = L.map Prod.snd := by
  simp [FinRel.ofList, List.unzip_snd]

theorem map_snd_toList (r : FinRel K V) : r.toList.map Prod.snd = r.vals.toList :=
  List.map_snd_zip (by simp [r.len])

/-- `R ; h` for an enumerating `h`: each value's fibre, in order. -/
theorem vals_comp_enum [DecidableEq K] [DecidableEq V] [DecidableEq C] (r : FinRel K V) (h : V → List C) :
    ∃ r', RelRep.comp (.pairs r) (.enum h) = some (.pairs r') ∧ r'.vals.toList = r.vals.toList.flatMap h := by
  refine ⟨_, rfl, ?_⟩
  rw [vals_ofList, List.map_flatMap, ← map_snd_toList, List.flatMap_map]
  simp [Function.comp_def]

/-- The fibre of `j` in `ix(xs)` from `k` on: `xs[j-k]`, or nothing. -/
theorem filterMap_sel_zipIdx (xs : List V) : ∀ k j : Nat,
    ((xs.zipIdx k).map Prod.swap).filterMap (FinRel.sel j) = if k ≤ j then xs[j - k]?.toList else [] := by
  induction xs with
  | nil => intro k j; split <;> rfl
  | cons a xs ih =>
    intro k j
    rw [List.zipIdx_cons, List.map_cons, List.filterMap_cons, ih]
    by_cases h : k = j
    · subst h; simp [FinRel.sel]; intro h; exact absurd h (by omega)
    · have e : FinRel.sel j (Prod.swap (a, k)) = none := by simp [FinRel.sel, h]
      rw [e]
      by_cases h2 : k + 1 ≤ j
      · rw [if_pos h2, if_pos (by omega), show j - k = (j - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
      · rw [if_neg h2, if_neg (by omega)]

/-- `ql(xs)` answers `j` with `xs[j]`. -/
theorem scan_ql (xs : List V) (j : Nat) :
    (FinRel.ofList (xs.zipIdx.map Prod.swap)).scanLookup j = xs[j]?.toList := by
  rw [FinRel.scanLookup_ofList]; exact (filterMap_sel_zipIdx xs 0 j).trans (by simp)

theorem vals_ql (xs : List V) : (FinRel.ofList (xs.zipIdx.map Prod.swap)).vals.toList = xs := by
  rw [vals_ofList]
  exact List.ext_getElem (by simp) fun i _ _ => by simp [List.getElem_zipIdx]

theorem flatMap_test (p : V → Bool) : (l : List V) → l.flatMap (fun v => if p v then [v] else []) = l.filter p
  | [] => rfl
  | v :: l => by rw [List.flatMap_cons, List.filter_cons, flatMap_test p l]; split <;> rfl

theorem flatMap_single (g : V → C) : (l : List V) → l.flatMap (fun v => [g v]) = l.map g
  | [] => rfl
  | v :: l => by rw [List.flatMap_cons, List.map_cons, flatMap_single g l]; rfl

end Pairs

/-! ## q's `sum` of `long`s -/

/-- q's `sum`: every element but the null `nul`, added with 64-bit wrap — `Coc.Over.step .add`. -/
def qsum (nul : Int64) (xs : List Int64) : Int64 := xs.foldl (fun acc x => if x == nul then acc else acc + x) 0

theorem foldl_qsum (nul : Int64) : (xs : List Int64) → (a : Int64) →
    xs.foldl (fun acc x => if x == nul then acc else acc + x) a =
      a + Int64.ofInt ((xs.filter (· != nul)).map Int64.toInt).sum
  | [], a => by simp
  | x :: xs, a => by
    rw [List.foldl_cons, foldl_qsum nul xs]
    by_cases h : x = nul
    · subst h; simp
    · simp [h, Int64.ofInt_add, Int64.ofInt_toInt, Int64.add_assoc]

/-- **q's `sum` is the integer sum of the non-null values, wrapped to 64 bits.** -/
theorem qsum_eq (nul : Int64) (xs : List Int64) :
    qsum nul xs = Int64.ofInt ((xs.filter (· != nul)).map Int64.toInt).sum := by
  rw [qsum, foldl_qsum]; simp

/-- q's `sum` as a `RelRep` pipeline: drop the null by the coreflexive `(≠ nul)?`, read each value
as an integer, then `Q.Agg.sum`. -/
def qsumR (nul : Int64) (R : RelRep Nat Int64) : Option (List Int) := do
  let B ← R.comp (RelRep.corefl (· != nul))
  let D ← B.comp (RelRep.ofFn Int64.toInt)
  Q.Agg.sum D

theorem qsumR_pairs (nul : Int64) (r : FinRel Nat Int64) :
    qsumR nul (.pairs r) = some [((r.vals.toList.filter (· != nul)).map Int64.toInt).sum] := by
  obtain ⟨r1, e1, v1⟩ := vals_comp_enum r fun k => if k != nul then [k] else []
  obtain ⟨r2, e2, v2⟩ := vals_comp_enum r1 fun k => [Int64.toInt k]
  simp only [qsumR, RelRep.corefl, RelRep.ofFn, e1, e2, Option.bind_eq_bind, Option.bind_some]
  rw [Q.Agg.sum_pairs, v2, v1, flatMap_test, flatMap_single]

/-- **`qsum` is `qsumR` of the list**: the fold equals the `.pairs` pipeline, 64-bit wrapped. -/
theorem qsum_ql (nul : Int64) (xs : List Int64) :
    ∃ s, qsumR nul (Q.Agg.ql xs) = some [s] ∧ qsum nul xs = Int64.ofInt s :=
  ⟨_, (qsumR_pairs nul _).trans (by rw [vals_ql]), qsum_eq nul xs⟩

/-! ## A compressed value column -/

/-- The storage class of a signed `w`-byte payload, `w ∈ {2, 4, 8}`. -/
def clsW (w : Nat) : UInt8 := if w = 2 then Ew.i16 else if w = 4 then Ew.i32 else Ew.i64

/-- The widths a signed storage class exists for. -/
def Signed (w : Nat) : Prop := w = 2 ∨ w = 4 ∨ w = 8

instance (w : Nat) : Decidable (Signed w) := inferInstanceAs (Decidable (_ ∨ _))

theorem width_clsW {w : Nat} (h : Signed w) : Ew.width (clsW w) = w := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- `Ew.signed` at the class of `w` is `sx w`: the kernel reads a `w`-byte element as `atW` does. -/
theorem signed_clsW {w : Nat} (h : Signed w) (v : UInt64) : Ew.signed (clsW w) v = (sx w v).toInt64 := by
  apply Int64.toInt_inj.1
  have hb := sx_bounds (w := w) v
  have hh : half w ≤ 2 ^ 63 := half_le (by rcases h with rfl | rfl | rfl <;> decide)
  rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  rcases h with rfl | rfl | rfl
  · show (v.toUInt16.toInt16.toInt64).toInt = _
    rw [Int16.toInt_toInt64, Int16.toInt, show v.toUInt16.toInt16.toBitVec = v.toUInt16.toBitVec from rfl,
      BitVec.toInt_eq_toNat_cond, UInt16.toNat_toBitVec, UInt64.toNat_toUInt16]
    simp only [sx]; split <;> split <;> omega
  · show (v.toUInt32.toInt32.toInt64).toInt = _
    rw [Int32.toInt_toInt64, Int32.toInt, show v.toUInt32.toInt32.toBitVec = v.toUInt32.toBitVec from rfl,
      BitVec.toInt_eq_toNat_cond, UInt32.toNat_toBitVec, UInt64.toNat_toUInt32]
    simp only [sx]; split <;> split <;> omega
  · show v.toInt64.toInt = _
    rw [sx_eight]

namespace Col

/-- The values a column denotes, element `i` read from the packed bytes. Only the statements use it. -/
def vals (c : Keys) : List Int64 := (List.range c.count).map c.get

/-- One step of q's `sum` reading element `i` of `c` in place. -/
def step (nul : Int64) (c : Keys) (acc : Int64) (i : Nat) : Int64 :=
  let x := c.get i; if x == nul then acc else acc + x

/-- **q's `sum` of a compressed column**: `overBytes .add` over a dense payload of a signed class,
`Coc.over .add` over a pack (the C sums a block as `1024 * base + Σ residuals` from its metadata),
and the fold over `atW` at the widths no class covers. -/
def sum (nul : Int64) : Keys → Int64
  | .dense w b =>
    if Signed w then overBytes .add (clsW w) nul b
    else (List.range (b.size / w)).foldl (step nul (.dense w b)) 0
  | .foR n md pk => Coc.over .add nul md pk n.toUSize

theorem foldl_step (nul : Int64) (c : Keys) (is : List Nat) :
    is.foldl (step nul c) 0 = qsum nul (is.map c.get) := by
  rw [qsum, List.foldl_map]; rfl

/-- **`sum` reads the same values `vals` lists**, whichever kernel runs. -/
theorem sum_eq (nul : Int64) (c : Keys) (hf : c.fits) : sum nul c = qsum nul (Col.vals c) := by
  cases c with
  | dense w b =>
    simp only [sum, vals, Keys.count]
    split
    · rename_i hw
      rw [overBytes, width_clsW hw, qsum, List.foldl_map]
      simp only [Coc.Over.denseSeed, Coc.Over.seed, Coc.Over.boolCast, Coc.Over.step, Ew.elem, width_clsW hw,
        signed_clsW hw]
      have : (clsW w != Ew.u8 || (Coc.Over.add != .lesser && Coc.Over.add != .greater)) = true := by
        simp
      rw [if_pos this]
      rfl
    · exact foldl_step nul _ _
  | foR n md pk =>
    simp only [sum, vals, Keys.count, Coc.over, Coc.elems, Coc.Over.seed, Coc.Over.boolCast, Coc.Over.step,
      qsum, List.foldl_map, USize.toNat_ofNat_of_lt' hf]
    rfl

/-- **`sum` is q's sum of the `.pairs` column**: `ql(vs) ; (≠ nul)? ; toInt ; sum`, 64-bit wrapped. -/
theorem sum_spec (nul : Int64) (c : Keys) (hf : c.fits) :
    ∃ s, qsumR nul (Q.Agg.ql (Col.vals c)) = some [s] ∧ sum nul c = Int64.ofInt s := by
  obtain ⟨s, h, e⟩ := qsum_ql nul (Col.vals c); exact ⟨s, h, (sum_eq nul c hf).trans e⟩

end Col

/-! ## `where`, and `sum v where b` -/

/-- `sum v where b`: the indices `whereBits` answers, `v` read at each in place. -/
def sumWhere (nul : Int64) (n : USize) (bits : ByteArray) (v : Keys) : Int64 :=
  (whereQ n bits).foldl (Col.step nul v) 0

theorem sumWhere_eq (nul : Int64) (n : USize) (bits : ByteArray) (v : Keys) (h : n.toNat < 2 ^ 63) :
    sumWhere nul n bits v = qsum nul (((List.range n.toNat).filter (bitAt bits)).map v.get) := by
  rw [sumWhere, Col.foldl_step, whereQ_eq n bits h]

/-- `ql(is) ; ql(xs)`: `xs` read at each of `is`, in `is`'s order. -/
theorem comp_ql (is : List Nat) (xs : List Int64) :
    ∃ r, (Q.Agg.ql is).comp (Q.Agg.ql xs) = some (.pairs r) ∧ r.vals.toList = is.flatMap fun i => xs[i]?.toList := by
  refine ⟨_, rfl, ?_⟩
  rw [vals_ofList, List.map_flatMap, FinRel.toList_ofList]
  simp only [scan_ql, List.map_map, Function.comp_def, List.map_id']
  rw [← List.flatMap_map (f := Prod.snd) (g := fun i => xs[i]?.toList)]
  congr 1
  rw [List.map_map]
  exact List.ext_getElem (by simp) fun i _ _ => by simp [List.getElem_zipIdx]

theorem flatMap_get (g : Nat → Int64) (m : Nat) : (is : List Nat) → (∀ i ∈ is, i < m) →
    is.flatMap (fun i => ((List.range m).map g)[i]?.toList) = is.map g
  | [], _ => rfl
  | i :: is, h => by
    rw [List.flatMap_cons, List.map_cons, flatMap_get g m is fun j hj => h j (List.mem_cons_of_mem _ hj),
      List.getElem?_map, List.getElem?_range (h i List.mem_cons_self)]
    rfl

/-- **`sum v where b` is the `.pairs` composition `where ≫ v ≫ sum`**: `ql(where b) ; ql(vs)`, then
q's sum, 64-bit wrapped, when every index `where` can answer is inside `v`. -/
theorem sumWhere_spec (nul : Int64) (n : USize) (bits : ByteArray) (v : Keys) (h : n.toNat < 2 ^ 63)
    (hv : n.toNat ≤ v.count) :
    ∃ s, ((Q.Agg.ql (whereQ n bits)).comp (Q.Agg.ql (Col.vals v))).bind (qsumR nul) = some [s] ∧
      sumWhere nul n bits v = Int64.ofInt s := by
  obtain ⟨r, hc, hr⟩ := comp_ql (whereQ n bits) (Col.vals v)
  have hb : ∀ i ∈ whereQ n bits, i < v.count := fun i hi => by
    rw [whereQ_eq n bits h] at hi; have := List.mem_range.1 (List.mem_filter.1 hi).1; omega
  rw [Col.vals, flatMap_get _ _ _ hb] at hr
  refine ⟨_, by rw [hc, Option.bind_some, qsumR_pairs, hr], ?_⟩
  rw [sumWhere, Col.foldl_step, qsum_eq]

/-! ## `select sum v by k` -/

section Dict

variable {α : Type} [DecidableEq α]

theorem all_congr' {l : List Nat} {p q : Nat → Bool} (h : ∀ j ∈ l, p j = q j) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self, ih fun j hj => h j (List.mem_cons_of_mem _ hj)]

/-- `dictOf` reads `g` below `m` only. -/
theorem dictOf_congr {g g' : Nat → α} {m : Nat} (h : ∀ i < m, g i = g' i) : dictOf g m = dictOf g' m := by
  have hb : ∀ f < m, bucketOf g m f = bucketOf g' m f := fun f hf =>
    List.filter_congr fun i hi => by rw [h i (List.mem_range.1 hi), h f hf]
  have hf : firstsOf g m = firstsOf g' m := List.filter_congr fun i hi => by
    have hi := List.mem_range.1 hi
    exact all_congr' fun j hj => by rw [h j (by have := List.mem_range.1 hj; omega), h i hi]
  rw [dictOf, dictOf, ← hf]
  exact List.map_congr_left fun f hm => by
    have := List.mem_range.1 (List.mem_filter.1 hm).1; rw [h f this, hb f this]

end Dict

/-- `group` on a key column, read compressed: `Order.group` on a dense `long` payload,
`Order.groupFoR` on a pack, the bucket filter over `atW` at the other widths. -/
def groupK : Keys → List (Int64 × List Nat)
  | .dense w b => if w = 8 then groupQ (b.size / 8).toUSize b else dictOf (atW w b) (b.size / w)
  | .foR n md pk => groupFoRQ n.toUSize md pk

/-- **`groupK` answers each first key with its bucket.** -/
theorem groupK_eq (k : Keys) (h : k.count < 2 ^ 32) : groupK k = dictOf k.get k.count := by
  cases k with
  | dense w b =>
    simp only [groupK, Keys.count] at h ⊢
    split
    · rename_i hw; subst hw
      have hc : cnt (b.size / 8).toUSize b = b.size / 8 := by
        simp only [cnt, toNat_toUSize h, Nat.min_self]
      rw [groupQ_eq _ b (by rw [hc]; omega), hc]; rfl
    · rfl
  | foR n md pk =>
    simp only [Keys.count] at h
    obtain ⟨hc, -, hcol⟩ := decoded_spec n.toUSize md pk
    rw [toNat_toUSize h] at hc
    show groupQ n.toUSize (decoded n.toUSize md pk) = _
    rw [groupQ_eq _ _ (by rw [hc]; omega), hc]
    apply dictOf_congr
    intro i hi
    have := congrArg (·[i]?) hcol
    simp only [col, colFoR, hc, toNat_toUSize h, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.some.injEq] at this
    exact this

/-- `select sum v by k`: each bucket `groupK` answers, `v` summed over it in place. -/
def selbySum (nul : Int64) (k v : Keys) : List (Int64 × Int64) :=
  (groupK k).map fun p => (p.1, p.2.foldl (Col.step nul v) 0)

/-- The table `select … by` reads: row `i` is `(k[i], v[i])`. -/
def rows (k v : Keys) : List (Int64 × Int64) := (List.range k.count).map fun i => (k.get i, v.get i)

theorem zipIdx_range {β : Type} (f : Nat → β) (m : Nat) :
    ((List.range m).map f).zipIdx = (List.range m).map fun i => (f i, i) :=
  List.ext_getElem (by simp) fun i _ _ => by simp [List.getElem_zipIdx]

/-- **`xkey`'s fibre on `rows`**: the key `c` lists `v` at the rows whose key is `c`, in row order. -/
theorem xkey_rows (kg vg : Nat → Int64) (m : Nat) :
    ∃ X, Q.xkey Prod.fst Prod.snd (Q.tab ((List.range m).map fun i => (kg i, vg i))) = some X ∧
      X.app? = some fun c => ((List.range m).filter fun i => kg i = c).map vg := by
  have ht : ((List.range m).map fun i => (kg i, vg i)).zipIdx.map Prod.swap =
      (List.range m).map fun i => (i, (kg i, vg i)) := by rw [zipIdx_range, List.map_map]; rfl
  have e1 : (Q.tab ((List.range m).map fun i => (kg i, vg i))).comp (RelRep.ofFn Prod.fst) =
      some (.pairs (FinRel.ofList ((List.range m).map fun i => (i, kg i)))) := by
    simp only [Q.tab, RelRep.ofFn, RelRep.comp, FinRel.toList_ofList, ht, List.flatMap_map, List.map_cons,
      List.map_nil]
    rw [flatMap_single (fun a => (a, kg a))]
  have e2 : (Q.tab ((List.range m).map fun i => (kg i, vg i))).comp (RelRep.ofFn Prod.snd) =
      some (.pairs (FinRel.ofList (((List.range m).map vg).zipIdx.map Prod.swap))) := by
    simp only [Q.tab, RelRep.ofFn, RelRep.comp, FinRel.toList_ofList, ht, List.flatMap_map, List.map_cons,
      List.map_nil]
    rw [flatMap_single (fun a => (a, vg a)), zipIdx_range, List.map_map]; rfl
  have hc : (FinRel.ofList ((List.range m).map fun i => (i, kg i))).conv.toList =
      (List.range m).map fun i => (kg i, i) :=
    List.ext_getElem (by simp [FinRel.conv, FinRel.toList, FinRel.ofList]) fun i _ _ => by
      simp [FinRel.conv, FinRel.toList, FinRel.ofList, List.getElem_zip, List.unzip_fst, List.unzip_snd]
  have hs : ∀ (l : List Nat) (c : Int64), (l.map fun i => (kg i, i)).filterMap (FinRel.sel c) =
      l.filter fun i => kg i = c := fun l c => by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.filterMap_cons, ih, List.filter_cons]
      by_cases h : kg a = c <;> simp [FinRel.sel, h]
  have hA : (RelRep.pairs (FinRel.ofList ((List.range m).map fun i => (i, kg i)))).conv.app? =
      some fun c => (List.range m).filter fun i => kg i = c := by
    simp only [RelRep.conv, RelRep.app?, Option.some.injEq]
    funext c; rw [FinRel.scanLookup, hc, hs]
  have hB : (RelRep.pairs (FinRel.ofList (((List.range m).map vg).zipIdx.map Prod.swap))).app? =
      some fun j => ((List.range m).map vg)[j]?.toList := by
    simp only [RelRep.app?, Option.some.injEq]; funext j; exact scan_ql _ j
  obtain ⟨X, hX⟩ : ∃ X, (RelRep.pairs (FinRel.ofList ((List.range m).map fun i => (i, kg i)))).conv.comp
      (.pairs (FinRel.ofList (((List.range m).map vg).zipIdx.map Prod.swap))) = some X := ⟨_, rfl⟩
  refine ⟨X, by simp only [Q.xkey, e1, e2, Option.bind_eq_bind, Option.bind_some, hX], ?_⟩
  rw [RelRep.app?_comp hX hA hB]
  congr 1; funext c
  exact flatMap_get vg m _ fun i hi => List.mem_range.1 (List.mem_filter.1 hi).1

end LeetQ.Compressed
