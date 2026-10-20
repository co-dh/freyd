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
theorem vals_comp_enum [DecidableEq K] [DecidableEq V] [DecidableEq C] [FibreIndex K] [FibreIndex V] (r : FinRel K V) (h : V → List C) :
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

/-- `Int64.ofInt_toInt` without core's `Classical.choice`: `toInt_bounds` and the in-range read-back. -/
theorem ofInt_toInt (x : Int64) : Int64.ofInt x.toInt = x :=
  Int64.toInt_inj.1 (by have := toInt_bounds x; exact Int64.toInt_ofInt_of_le (by omega) (by omega))

theorem foldl_qsum (nul : Int64) : (xs : List Int64) → (a : Int64) →
    xs.foldl (fun acc x => if x == nul then acc else acc + x) a =
      a + Int64.ofInt ((xs.filter (· != nul)).map Int64.toInt).sum
  | [], a => by show a = a + Int64.ofInt 0; rw [show Int64.ofInt 0 = 0 from rfl, Int64.add_zero]
  | x :: xs, a => by
    rw [List.foldl_cons, foldl_qsum nul xs]
    -- a `Bool` case split: `by_cases` and `simp` reach `Classical.choice` here
    cases hb : x == nul with
    | true =>
      cases eq_of_beq hb
      rw [if_pos rfl, List.filter_cons_of_neg (by rw [bne_self_eq_false]; exact Bool.false_ne_true)]
    | false =>
      rw [if_neg Bool.false_ne_true, List.filter_cons_of_pos (by rw [bne, hb]; rfl), List.map_cons, List.sum_cons,
        Int64.ofInt_add, ofInt_toInt, Int64.add_assoc]

/-- **q's `sum` is the integer sum of the non-null values, wrapped to 64 bits.** -/
theorem qsum_eq (nul : Int64) (xs : List Int64) :
    qsum nul xs = Int64.ofInt ((xs.filter (· != nul)).map Int64.toInt).sum := by
  rw [qsum, foldl_qsum, Int64.zero_add]

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
  -- `signExtend` is `ofInt ∘ toInt`, read back in range; core's `toInt_signExtend` carries choice
  · show (Int64.ofInt v.toUInt16.toBitVec.toInt).toInt = _
    have hc := BitVec.toInt_eq_toNat_cond v.toUInt16.toBitVec
    rw [UInt16.toNat_toBitVec, UInt64.toNat_toUInt16] at hc
    have := Nat.mod_lt v.toNat (show 0 < 2 ^ 16 by decide)
    rw [Int64.toInt_ofInt_of_le (by split at hc <;> omega) (by split at hc <;> omega), hc]
    simp only [sx]; split <;> split <;> omega
  · show (Int64.ofInt v.toUInt32.toBitVec.toInt).toInt = _
    have hc := BitVec.toInt_eq_toNat_cond v.toUInt32.toBitVec
    rw [UInt32.toNat_toBitVec, UInt64.toNat_toUInt32] at hc
    have := Nat.mod_lt v.toNat (show 0 < 2 ^ 32 by decide)
    rw [Int64.toInt_ofInt_of_le (by split at hc <;> omega) (by split at hc <;> omega), hc]
    simp only [sx]; split <;> split <;> omega
  · show v.toInt64.toInt = _
    rw [sx_eight]

namespace Col

/-- The values a column denotes, element `i` read from the packed bytes. Only the statements use it. -/
def vals (c : Keys) : List Int64 := (List.range c.count).map c.get

/-- One step of q's `sum` reading element `i` of `c` in place. -/
def step (nul : Int64) (c : Keys) (acc : Int64) (i : Nat) : Int64 :=
  let x := c.get i; if x == nul then acc else acc + x

/-- `bitsAt` as a recursion of its own: qlean runs `bitsAt` as a `Nat.fold`, a closure call per byte. -/
def ld (b : ByteArray) (o : Nat) : Nat → UInt64
  | 0 => 0
  | w + 1 => ld b o w ||| ((if h : o + w < b.size then b[o + w] else 0).toUInt64 <<< (8 * w).toUInt64)

theorem ld_eq (b : ByteArray) (o : Nat) : ∀ w, ld b o w = bitsAt b o w
  | 0 => rfl
  | w + 1 => by rw [ld, ld_eq b o w]; rfl

/-- A column with its per-column work done once, before the first element: a pack's block starts.
A structure and not a closure `Nat → Int64`, because the compiler eta-expands a closure-returning
definition and so recomputes whatever it bound before the `fun` at every element. -/
structure Rd where
  c : Keys
  st : Array Nat

/-- `c.get` off an `Rd`: a dense payload of a signed class reads through `Ew.signed`, fixed-width `UInt`
casts in place of `sx`'s `Nat` powers; a pack reads its block start from `st`. -/
@[inline] def Rd.get (r : Rd) (i : Nat) : Int64 :=
  match r.c with
  | .dense w b => if Signed w then Ew.signed (clsW w) (ld b (i * w) w) else atW w b i
  | .foR _ md pk => (foRBits md pk r.st i).toInt64

def rdOf (c : Keys) : Rd := ⟨c, match c with | .foR _ md _ => blockStarts md | .dense .. => #[]⟩

theorem rdOf_get (c : Keys) : (rdOf c).get = c.get := by
  funext i
  cases c with
  | dense w b =>
    simp only [rdOf, Rd.get]; split
    · rename_i hw; rw [ld_eq, signed_clsW hw]; rfl
    · rfl
  | foR n md pk => rfl

/-- `step` over an `Rd`, which the loops below take whole so the read inlines into them. -/
def stepR (nul : Int64) (r : Rd) (acc : Int64) (i : Nat) : Int64 :=
  let x := r.get i; if x == nul then acc else acc + x

theorem step_rd (nul : Int64) (c : Keys) : stepR nul (rdOf c) = step nul c := by
  funext acc i; simp only [stepR, rdOf_get]; rfl

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

section Bits

variable {β : Type}

/-- Byte `j` of `bits`, `0` past the end, as `bitAt` reads it but with no `Option` between. -/
def byteAt (bits : ByteArray) (j : Nat) : UInt8 := if h : j < bits.size then bits[j] else 0

theorem bitAt_byte (bits : ByteArray) (j t : Nat) (ht : t < 8) :
    bitAt bits (8 * j + t) = ((byteAt bits j >>> t.toUInt8) &&& 1 == 1) := by
  have e : bits[j]?.getD 0 = byteAt bits j := by
    unfold byteAt; split
    · rename_i h; rw [getElem?_pos bits j h]; rfl
    · rename_i h; rw [getElem?_neg bits j h]; rfl
  simp only [bitAt, show (8 * j + t) / 8 = j by omega, show (8 * j + t) % 8 = t by omega, e]

/-- Bit `i` is one of `where`'s answers below `n`. -/
def inW (bits : ByteArray) (n i : Nat) : Bool := decide (i < n) && bitAt bits i

/-- `f` over the set bits `base + t` of `byte`, `t` from `t` on, `k` of them, below `n`. -/
@[specialize] def bitLoop (f : β → Nat → β) (n : Nat) (byte : UInt8) (base : Nat) : Nat → Nat → β → β
  | 0, _, acc => acc
  | k + 1, t, acc => bitLoop f n byte base k (t + 1)
    (if decide (base + t < n) && ((byte >>> t.toUInt8) &&& 1 == 1) then f acc (base + t) else acc)

/-- `bitLoop` over `k` bytes from byte `j` on. -/
@[specialize] def byteLoop (f : β → Nat → β) (bits : ByteArray) (n : Nat) : Nat → Nat → β → β
  | 0, _, acc => acc
  | k + 1, j, acc => byteLoop f bits n k (j + 1) (bitLoop f n (byteAt bits j) (8 * j) 8 0 acc)

/-- **`f` folded over `where`'s answers in one pass over the bytes**, with no index list between. -/
@[specialize] def whereFold (f : β → Nat → β) (bits : ByteArray) (n : Nat) (acc : β) : β :=
  byteLoop f bits n ((n + 7) / 8) 0 acc

theorem range'_add (s a b : Nat) : List.range' s (a + b) = List.range' s a ++ List.range' (s + a) b := by
  induction a generalizing s with
  | zero => rw [Nat.zero_add, Nat.add_zero]; rfl
  | succ a ih =>
    rw [Nat.add_right_comm, List.range'_succ, List.range'_succ, ih, show s + 1 + a = s + (a + 1) by omega]; rfl

theorem bitLoop_eq (f : β → Nat → β) (bits : ByteArray) (n j : Nat) : ∀ k t (acc : β), t + k ≤ 8 →
    bitLoop f n (byteAt bits j) (8 * j) k t acc = ((List.range' (8 * j + t) k).filter (inW bits n)).foldl f acc
  | 0, _, _, _ => rfl
  | k + 1, t, acc, h => by
    rw [bitLoop, bitLoop_eq f bits n j k (t + 1) _ (by omega), List.range'_succ, List.filter_cons,
      show 8 * j + t + 1 = 8 * j + (t + 1) by omega, inW, bitAt_byte bits j t (by omega)]
    cases (decide (8 * j + t < n) && ((byteAt bits j >>> t.toUInt8) &&& 1 == 1)) <;> rfl

theorem byteLoop_eq (f : β → Nat → β) (bits : ByteArray) (n : Nat) : ∀ k j (acc : β),
    byteLoop f bits n k j acc = ((List.range' (8 * j) (8 * k)).filter (inW bits n)).foldl f acc
  | 0, _, _ => rfl
  | k + 1, j, acc => by
    rw [byteLoop, byteLoop_eq f bits n k (j + 1), bitLoop_eq f bits n j 8 0 acc (by omega),
      show 8 * (k + 1) = 8 + 8 * k by omega, range'_add, List.filter_append, List.foldl_append, Nat.add_zero,
      show 8 * j + 8 = 8 * (j + 1) by omega]

theorem filter_inW_ge (bits : ByteArray) (n : Nat) : ∀ k s, n ≤ s → (List.range' s k).filter (inW bits n) = []
  | 0, _, _ => rfl
  | k + 1, s, h => by
    rw [List.range'_succ, List.filter_cons, filter_inW_ge bits n k (s + 1) (by omega), inW,
      decide_eq_false (show ¬ s < n by omega), Bool.false_and]; rfl

theorem whereFold_eq (f : β → Nat → β) (bits : ByteArray) (n : Nat) (acc : β) :
    whereFold f bits n acc = ((List.range n).filter (bitAt bits)).foldl f acc := by
  rw [whereFold, byteLoop_eq, show 8 * 0 = 0 from rfl, show 8 * ((n + 7) / 8) = n + (8 * ((n + 7) / 8) - n) by omega,
    range'_add, List.filter_append, filter_inW_ge bits n (8 * ((n + 7) / 8) - n) (0 + n) (by omega), List.append_nil,
    ← List.range_eq_range']
  congr 1
  exact List.filter_congr fun i hi => by rw [inW, decide_eq_true (List.mem_range.1 hi), Bool.true_and]

end Bits

/-- `sum v where b`: one pass over `b`'s bytes, `v` read at each set bit in place. -/
def sumWhere (nul : Int64) (n : USize) (bits : ByteArray) (v : Keys) : Int64 :=
  let r := Col.rdOf v; whereFold (Col.stepR nul r) bits n.toNat 0

theorem sumWhere_fold (nul : Int64) (n : USize) (bits : ByteArray) (v : Keys) :
    sumWhere nul n bits v = ((List.range n.toNat).filter (bitAt bits)).foldl (Col.step nul v) 0 := by
  simp only [sumWhere]; rw [whereFold_eq, Col.step_rd]

theorem sumWhere_eq (nul : Int64) (n : USize) (bits : ByteArray) (v : Keys) (h : n.toNat < 2 ^ 63) :
    sumWhere nul n bits v = qsum nul (((List.range n.toNat).filter (bitAt bits)).map v.get) := by
  rw [sumWhere_fold, Col.foldl_step]

/-- `ql(is) ; ql(xs)`: `xs` read at each of `is`, in `is`'s order. -/
theorem comp_ql (is : List Nat) (xs : List Int64) :
    ∃ r, (Q.Agg.ql is).comp (Q.Agg.ql xs) = some (.pairs r) ∧ r.vals.toList = is.flatMap fun i => xs[i]?.toList := by
  refine ⟨_, rfl, ?_⟩
  rw [vals_ofList, List.map_flatMap, FinRel.toList_ofList]
  simp only [FibreIndex.get_build, scan_ql, List.map_map, Function.comp_def, List.map_id']
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
  rw [sumWhere_fold, ← whereQ_eq n bits h, Col.foldl_step, qsum_eq]

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

/-! ### One pass: a hash table from key to slot, the slots in first-appearance order

Std's `HashMap` laws carry `Classical.choice`, so the table is a chained one of its own: an array of
buckets, a bucket a list of `(key, slot)`, and its one law `look_ins`. -/

variable {β : Type}

/-- The slot a bucket lists for `a`. -/
def find (a : α) : List (α × Nat) → Option Nat
  | [] => none
  | (k, v) :: l => if k = a then some v else find a l

/-- The slot `t` holds for `a`, `h` the hash. -/
def look (h : α → UInt64) (t : Array (List (α × Nat))) (a : α) : Option Nat :=
  find a (t[(h a).toNat % t.size]?.getD [])

def ins (h : α → UInt64) (t : Array (List (α × Nat))) (k : α) (v : Nat) : Array (List (α × Nat)) :=
  t.modify ((h k).toNat % t.size) ((k, v) :: ·)

theorem look_ins (h : α → UInt64) (t : Array (List (α × Nat))) (k : α) (v : Nat) (a : α) (ht : 0 < t.size) :
    look h (ins h t k v) a = if k = a then some v else look h t a := by
  simp only [look, ins, Array.size_modify]
  rw [Array.getElem?_modify]
  by_cases hk : k = a
  · subst hk
    rw [if_pos rfl, if_pos rfl, Array.getElem?_eq_getElem (Nat.mod_lt _ ht)]
    simp only [Option.map_some, Option.getD_some, find, if_pos]
  · rw [if_neg hk]
    split
    · cases t[(h a).toNat % t.size]? <;> simp only [Option.map_none, Option.map_some, Option.getD_none,
        Option.getD_some, find, if_neg hk]
    · rfl

/-- The first position of `a` in `ks`. -/
def pos (a : α) : List α → Option Nat
  | [] => none
  | k :: ks => if k = a then some 0 else (pos a ks).map (· + 1)

theorem pos_snoc (a k : α) : ∀ ks : List α, pos a (ks ++ [k]) = (pos a ks).or (if k = a then some ks.length else none)
  | [] => by
    show (if k = a then some 0 else (pos a []).map (· + 1)) = (none : Option Nat).or _
    by_cases hk : k = a
    · rw [if_pos hk, if_pos hk]; rfl
    · rw [if_neg hk, if_neg hk]; rfl
  | k' :: ks => by
    show (if k' = a then some 0 else (pos a (ks ++ [k])).map (· + 1)) =
      (if k' = a then some 0 else (pos a ks).map (· + 1)).or (if k = a then some (ks.length + 1) else none)
    rw [pos_snoc a k ks]
    by_cases hk : k' = a
    · rw [if_pos hk, if_pos hk]; rfl
    · rw [if_neg hk, if_neg hk]
      cases pos a ks
      · by_cases h2 : k = a
        · rw [if_pos h2, if_pos h2]; rfl
        · rw [if_neg h2, if_neg h2]; rfl
      · rfl

theorem pos_some (a : α) : ∀ (ks : List α) (j : Nat), pos a ks = some j → ks[j]? = some a
  | [], _, h => nomatch h
  | k :: ks, j, h => by
    simp only [pos] at h
    split at h
    · rename_i hk; cases h; rw [hk]; rfl
    · cases e : pos a ks with
      | none => rw [e] at h; nomatch h
      | some j' => rw [e] at h; cases h; exact pos_some a ks j' e

theorem pos_none (a : α) : ∀ ks : List α, pos a ks = none → a ∉ ks
  | [], _ => nofun
  | k :: ks, h => by
    simp only [pos] at h
    split at h
    · nomatch h
    · rename_i hk
      cases e : pos a ks with
      | some _ => rw [e] at h; nomatch h
      | none => exact fun hm => (List.mem_cons.1 hm).elim (fun e' => hk e'.symm) (pos_none a ks e)

theorem nodup_idx : ∀ {l : List α} {i j : Nat} {a : α}, l.Nodup → l[i]? = some a → l[j]? = some a → i = j
  | [], _, _, _, _, hi, _ => nomatch hi
  | x :: l, i, j, a, hn, hi, hj => by
    have ⟨hx, hl⟩ := List.nodup_cons.1 hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => cases hi; exact absurd (List.mem_iff_getElem?.2 ⟨j, hj⟩) hx
    | succ i =>
      cases j with
      | zero => cases hj; exact absurd (List.mem_iff_getElem?.2 ⟨i, hi⟩) hx
      | succ j => rw [nodup_idx hl hi hj]

/-- `t` answers each key of `ks` with its first position, and nothing else. -/
def Inv (h : α → UInt64) (t : Array (List (α × Nat))) (ks : List α) : Prop :=
  0 < t.size ∧ ∀ a, look h t a = pos a ks

theorem inv_ins {h : α → UInt64} {t : Array (List (α × Nat))} {ks : List α} {k : α} (hi : Inv h t ks)
    (hk : pos k ks = none) : Inv h (ins h t k ks.length) (ks ++ [k]) := by
  refine ⟨by rw [ins, Array.size_modify]; exact hi.1, fun a => ?_⟩
  rw [look_ins h t k _ a hi.1, pos_snoc, hi.2 a]
  by_cases e : k = a
  · subst e; rw [if_pos rfl, if_pos rfl, hk]; rfl
  · rw [if_neg e, if_neg e]; cases pos a ks <;> rfl

theorem inv_empty (h : α → UInt64) {c : Nat} (hc : 0 < c) : Inv h (Array.replicate c []) [] := by
  refine ⟨by rw [Array.size_replicate]; exact hc, fun a => ?_⟩
  simp only [look, Array.getElem?_replicate]
  split <;> rfl

/-- One key into a table being rebuilt, at the next position, unless it is there already. -/
def addKey (h : α → UInt64) (s : Array (List (α × Nat)) × Nat) (k : α) : Array (List (α × Nat)) × Nat :=
  ((match look h s.1 k with | some _ => s.1 | none => ins h s.1 k s.2), s.2 + 1)

/-- The table of `ks` over `c` buckets. -/
def rehash (h : α → UInt64) (c : Nat) (ks : List α) : Array (List (α × Nat)) :=
  (ks.foldl (addKey h) (Array.replicate c [], 0)).1

theorem inv_foldl (h : α → UInt64) : ∀ (ks pre : List α) (s : Array (List (α × Nat)) × Nat),
    Inv h s.1 pre → s.2 = pre.length → Inv h (ks.foldl (addKey h) s).1 (pre ++ ks)
  | [], pre, s, hi, _ => by rw [List.append_nil]; exact hi
  | k :: ks, pre, s, hi, hl => by
    rw [List.foldl_cons, show pre ++ k :: ks = (pre ++ [k]) ++ ks by simp]
    refine inv_foldl h ks _ _ ?_ (by simp [addKey, hl])
    simp only [addKey]
    cases e : look h s.1 k with
    | none => rw [hl]; exact inv_ins hi (by rw [← hi.2 k, e])
    | some j =>
      refine ⟨hi.1, fun a => ?_⟩
      rw [hi.2 a, pos_snoc]
      by_cases ek : k = a
      · subst ek; rw [← hi.2 k, e]; rfl
      · rw [if_neg ek]; cases pos a pre <;> rfl

theorem inv_rehash (h : α → UInt64) {c : Nat} (hc : 0 < c) (ks : List α) : Inv h (rehash h c ks) ks :=
  inv_foldl h ks [] _ (inv_empty h hc) rfl

/-- Row `i` into the groups: its key's slot accumulates `i`, or a new slot opens after the others,
the table doubling first when it is as full as it has buckets. -/
@[specialize] def grpStep (h : α → UInt64) (g : Nat → α) (z : β) (upd : β → Nat → β)
    (s : Array (List (α × Nat)) × Array (α × β)) (i : Nat) : Array (List (α × Nat)) × Array (α × β) :=
  let x := g i
  match look h s.1 x with
  | some j => (s.1, s.2.modify j fun p => (p.1, upd p.2 i))
  | none =>
    let t := if s.1.size ≤ s.2.size then rehash h (2 * s.1.size) (s.2.toList.map Prod.fst) else s.1
    (ins h t x s.2.size, s.2.push (x, upd z i))

@[specialize] def grpGo (h : α → UInt64) (g : Nat → α) (z : β) (upd : β → Nat → β) :
    Nat → Nat → Array (List (α × Nat)) × Array (α × β) → Array (List (α × Nat)) × Array (α × β)
  | 0, _, s => s
  | k + 1, i, s => grpGo h g z upd k (i + 1) (grpStep h g z upd s i)

/-- **`group` in one pass**: each key of `g` below `m`, in first appearance, with `upd` folded over
its rows from `z`. -/
@[specialize] def grp (h : α → UInt64) (g : Nat → α) (z : β) (upd : β → Nat → β) (m : Nat) : Array (α × β) :=
  (grpGo h g z upd m 0 (Array.replicate 16 [], #[])).2

/-- What `grp` answers below `m`. -/
abbrev grpS (g : Nat → α) (z : β) (upd : β → Nat → β) (m : Nat) : List (α × β) :=
  (dictOf g m).map fun p => (p.1, p.2.foldl upd z)

theorem keys_grpS (g : Nat → α) (z : β) (upd : β → Nat → β) (m : Nat) :
    (grpS g z upd m).map Prod.fst = (firstsOf g m).map g := by
  rw [List.map_map, dictOf, List.map_map]; rfl

theorem firsts_succ (g : Nat → α) (m : Nat) :
    firstsOf g (m + 1) = firstsOf g m ++ [m].filter fun i => (List.range i).all fun j => !decide (g j = g i) := by
  rw [firstsOf, List.range_succ, List.filter_append]; rfl

theorem bucket_succ (g : Nat → α) (m f : Nat) :
    bucketOf g (m + 1) f = bucketOf g m f ++ [m].filter fun i => decide (g i = g f) := by
  rw [bucketOf, List.range_succ, List.filter_append]; rfl

/-- A key already seen: its slot, and no other, accumulates row `m`. -/
theorem grpS_old (g : Nat → α) (z : β) (upd : β → Nat → β) (m : Nat) (hx : ∃ i, i < m ∧ g i = g m) :
    firstsOf g (m + 1) = firstsOf g m ∧
    grpS g z upd (m + 1) = (grpS g z upd m).map fun p => if p.1 = g m then (p.1, upd p.2 m) else p := by
  have hf : firstsOf g (m + 1) = firstsOf g m := by
    rw [firsts_succ]
    cases hb : (List.range m).all fun j => !decide (g j = g m) with
    | false => simp only [List.filter_cons, List.filter_nil, hb, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    | true =>
      obtain ⟨i, hi, e⟩ := hx
      have := List.all_eq_true.1 hb i (List.mem_range.2 hi)
      rw [decide_eq_true e] at this; exact absurd this Bool.false_ne_true
  refine ⟨hf, ?_⟩
  rw [grpS, grpS, dictOf, dictOf, hf, List.map_map, List.map_map, List.map_map]
  refine List.map_congr_left fun f _ => ?_
  simp only [Function.comp_def, bucket_succ]
  by_cases e : g m = g f
  · simp only [List.filter_cons, List.filter_nil, decide_eq_true e, ↓reduceIte, List.foldl_append, List.foldl_cons,
      List.foldl_nil, if_pos e.symm]
  · simp only [List.filter_cons, List.filter_nil, decide_eq_false e, Bool.false_eq_true, ↓reduceIte,
      List.append_nil, if_neg (Ne.symm e)]

/-- A new key: a slot of its own after the others. -/
theorem grpS_new (g : Nat → α) (z : β) (upd : β → Nat → β) (m : Nat) (hx : ∀ i, i < m → g i ≠ g m) :
    firstsOf g (m + 1) = firstsOf g m ++ [m] ∧ grpS g z upd (m + 1) = grpS g z upd m ++ [(g m, upd z m)] := by
  have hb : ((List.range m).all fun j => !decide (g j = g m)) = true :=
    List.all_eq_true.2 fun j hj => by rw [decide_eq_false (hx j (List.mem_range.1 hj))]; rfl
  have hf : firstsOf g (m + 1) = firstsOf g m ++ [m] := by
    rw [firsts_succ]; simp only [List.filter_cons, List.filter_nil, hb, ↓reduceIte]
  refine ⟨hf, ?_⟩
  simp only [grpS, dictOf, hf, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun f hf' => ?_
    have hfm := List.mem_range.1 (List.mem_filter.1 hf').1
    simp only [Function.comp_def, bucket_succ, List.filter_cons, List.filter_nil,
      decide_eq_false (Ne.symm (hx f hfm)), Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · simp only [Function.comp_def, List.map_cons, List.map_nil, bucket_succ]
    have h0 : bucketOf g m m = [] := by
      rw [bucketOf, List.filter_congr (q := fun _ => false) fun i hi => decide_eq_false (hx i (List.mem_range.1 hi))]
      -- core's `filter_eq_nil_iff` carries `Classical.choice`
      induction List.range m with
      | nil => rfl
      | cons _ _ ih => exact ih
    simp only [h0, List.nil_append, List.filter_cons, List.filter_nil, decide_true, ↓reduceIte, List.foldl_cons,
      List.foldl_nil]

/-- `grpGo`'s state after `m` rows: the table answers the keys so far, the slots are `grpS`. -/
def J (h : α → UInt64) (g : Nat → α) (z : β) (upd : β → Nat → β) (m : Nat)
    (s : Array (List (α × Nat)) × Array (α × β)) : Prop :=
  Inv h s.1 ((firstsOf g m).map g) ∧ s.2.toList = grpS g z upd m

theorem J_step (h : α → UInt64) (g : Nat → α) (z : β) (upd : β → Nat → β) (m : Nat)
    (s : Array (List (α × Nat)) × Array (α × β)) (hs : J h g z upd m s) : J h g z upd (m + 1) (grpStep h g z upd s m) := by
  obtain ⟨hi, hl⟩ := hs
  have hn := nodup_firsts g m
  simp only [grpStep]
  cases e : look h s.1 (g m) with
  | some j =>
    have hj := pos_some _ _ _ ((hi.2 (g m)).symm.trans e)
    obtain ⟨hf, hS⟩ := grpS_old g z upd m (by
      obtain ⟨i, hi', e'⟩ := (mem_firsts g m (g m)).1 (List.mem_iff_getElem?.2 ⟨j, hj⟩); exact ⟨i, hi', e'⟩)
    refine ⟨by rw [hf]; exact hi, ?_⟩
    rw [hS]
    apply List.ext_getElem?
    intro i
    rw [Array.getElem?_toList, Array.getElem?_modify, List.getElem?_map, ← Array.getElem?_toList, hl]
    have hk : ∀ p, (grpS g z upd m)[i]? = some p → ((firstsOf g m).map g)[i]? = some p.1 := fun p hp => by
      rw [← keys_grpS g z upd m, List.getElem?_map, hp]; rfl
    split
    · rename_i hij; subst hij
      cases hp : (grpS g z upd m)[j]? with
      | none => rfl
      | some p =>
        have e1 : p.1 = g m := Option.some.inj ((hk p hp).symm.trans hj)
        simp only [Option.map_some, if_pos e1]
    · rename_i hij
      cases hp : (grpS g z upd m)[i]? with
      | none => rfl
      | some p =>
        have : p.1 ≠ g m := fun ep => hij (nodup_idx hn hj (by rw [hk p hp, ep]))
        simp only [Option.map_some, if_neg this]
  | none =>
    have hp : pos (g m) ((firstsOf g m).map g) = none := (hi.2 (g m)).symm.trans e
    obtain ⟨hf, hS⟩ := grpS_new g z upd m fun i him eq =>
      pos_none _ _ hp ((mem_firsts g m (g m)).2 ⟨i, him, eq⟩)
    have hks : s.2.toList.map Prod.fst = (firstsOf g m).map g := by rw [hl, keys_grpS]
    have hsz : s.2.size = ((firstsOf g m).map g).length := by
      rw [← hks, List.length_map, Array.length_toList]
    have ht : Inv h (if s.1.size ≤ s.2.size then rehash h (2 * s.1.size) (s.2.toList.map Prod.fst) else s.1)
        ((firstsOf g m).map g) := by
      split
      · rw [hks]; exact inv_rehash h (by have := hi.1; omega) _
      · exact hi
    refine ⟨?_, ?_⟩
    · show Inv h (ins h _ (g m) s.2.size) _
      rw [hf, List.map_append]; have := inv_ins ht hp; rwa [← hsz] at this
    · show (s.2.push _).toList = _
      rw [Array.toList_push, hl, hS]

theorem J_go (h : α → UInt64) (g : Nat → α) (z : β) (upd : β → Nat → β) :
    ∀ k i s, J h g z upd i s → J h g z upd (i + k) (grpGo h g z upd k i s)
  | 0, _, _, hs => hs
  | k + 1, i, s, hs => by
    rw [grpGo, show i + (k + 1) = i + 1 + k by omega]
    exact J_go h g z upd k (i + 1) _ (J_step h g z upd i s hs)

/-- **`grp` is `group` with each bucket folded**: the keys in first appearance, `upd` over each
bucket's rows in order. -/
theorem grp_eq (h : α → UInt64) (g : Nat → α) (z : β) (upd : β → Nat → β) (m : Nat) :
    (grp h g z upd m).toList = (dictOf g m).map fun p => (p.1, p.2.foldl upd z) := by
  have := J_go h g z upd m 0 (Array.replicate 16 [], #[]) ⟨inv_empty h (c := 16) (by decide), by rfl⟩
  rw [Nat.zero_add] at this
  exact this.2

theorem foldl_push (l : List Nat) : ∀ acc : Array Nat, (l.foldl Array.push acc).toList = acc.toList ++ l := by
  induction l with
  | nil => intro acc; rw [List.foldl_nil, List.append_nil]
  | cons a l ih => intro acc; rw [List.foldl_cons, ih, Array.toList_push, List.append_assoc]; rfl

end Dict

/-- The hash `grp` keys an `Int64` by: Fibonacci hashing, the top 32 bits of the product. -/
def hI (x : Int64) : UInt64 := (x.toUInt64 * 0x9E3779B97F4A7C15) >>> 32

/-- `group` on a key column, read compressed: `Order.group` on a dense `long` payload,
`Order.groupFoR` on a pack, and `grp` in one pass at the other widths. -/
def groupK : Keys → List (Int64 × List Nat)
  | .dense w b => if w = 8 then groupQ (b.size / 8).toUSize b else
    let r := Col.rdOf (.dense w b)
    (grp hI r.get #[] Array.push (b.size / w)).toList.map fun p => (p.1, p.2.toList)
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
    · rw [grp_eq, List.map_map, Col.rdOf_get]
      conv => rhs; rw [← List.map_id (dictOf _ _)]
      exact List.map_congr_left fun p _ => by
        simp only [Function.comp_def, foldl_push, List.nil_append]; rfl
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

/-- The key reader `select … by` groups on: a pack decoded once by the C, a dense payload read in place. -/
def rdK : Keys → Col.Rd
  | .dense w b => Col.rdOf (.dense w b)
  | .foR n md pk => Col.rdOf (.dense 8 (decoded n.toUSize md pk))

theorem rdK_get (k : Keys) (h : k.count < 2 ^ 32) : ∀ i < k.count, (rdK k).get i = k.get i := by
  cases k with
  | dense w b => intro i _; simp only [rdK, Col.rdOf_get]
  | foR n md pk =>
    simp only [Keys.count] at h
    obtain ⟨hc, -, hcol⟩ := decoded_spec n.toUSize md pk
    rw [toNat_toUSize h] at hc
    intro i hi
    have := congrArg (·[i]?) hcol
    simp only [col, colFoR, hc, toNat_toUSize h, List.getElem?_map, List.getElem?_range (show i < n from hi),
      Option.map_some, Option.some.injEq] at this
    simp only [rdK, Col.rdOf_get]; exact this

/-- `select sum v by k`: one pass over the rows, each key's slot summing `v` in place. -/
def selbySum (nul : Int64) (k v : Keys) : List (Int64 × Int64) :=
  let rk := rdK k; let rv := Col.rdOf v
  (grp hI rk.get (0 : Int64) (Col.stepR nul rv) k.count).toList

theorem selbySum_eq (nul : Int64) (k v : Keys) (h : k.count < 2 ^ 32) :
    selbySum nul k v = (dictOf k.get k.count).map fun p => (p.1, p.2.foldl (Col.step nul v) 0) := by
  simp only [selbySum]; rw [grp_eq, Col.step_rd, dictOf_congr (rdK_get k h)]

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
    funext c; rw [FibreIndex.get_build, FinRel.scanLookup, hc, hs]
  have hB : (RelRep.pairs (FinRel.ofList (((List.range m).map vg).zipIdx.map Prod.swap))).app? =
      some fun j => ((List.range m).map vg)[j]?.toList := by
    simp only [RelRep.app?, FibreIndex.get_build, Option.some.injEq]; funext j; exact scan_ql _ j
  obtain ⟨X, hX⟩ : ∃ X, (RelRep.pairs (FinRel.ofList ((List.range m).map fun i => (i, kg i)))).conv.comp
      (.pairs (FinRel.ofList (((List.range m).map vg).zipIdx.map Prod.swap))) = some X := ⟨_, rfl⟩
  refine ⟨X, by simp only [Q.xkey, e1, e2, Option.bind_eq_bind, Option.bind_some, hX], ?_⟩
  rw [RelRep.app?_comp hX hA hB]
  congr 1; funext c
  exact flatMap_get vg m _ fun i hi => List.mem_range.1 (List.mem_filter.1 hi).1

/-- **`select sum v by k`, read compressed**: the keys are `distinct`'s, in first appearance, and each
key's sum is q's sum of the fibre `xkey` gives that key on the table `rows` — order and repeats kept. -/
theorem selbySum_spec (nul : Int64) (k v : Keys) (h : k.count < 2 ^ 32) :
    ∃ X, Q.xkey Prod.fst Prod.snd (Q.tab (rows k v)) = some X ∧ ∃ g, X.app? = some g ∧
      (selbySum nul k v).map Prod.fst = (firstsOf k.get k.count).map k.get ∧
      ∀ p ∈ selbySum nul k v, p.2 = qsum nul (g p.1) := by
  obtain ⟨X, hX, hg⟩ := xkey_rows k.get v.get k.count
  refine ⟨X, hX, _, hg, ?_, fun p hp => ?_⟩
  · rw [selbySum_eq nul k v h, List.map_map]; exact dict_keys _ _
  · rw [selbySum_eq nul k v h, dictOf, List.map_map] at hp
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hp
    exact Col.foldl_step nul v _

/-- **The per-key entry of `app?_selby`**: `select agg v by k` over `rows`, with `agg` q's sum,
answers at `c` the sums of the keys `ks` lists, each `selbySum`'s entry for that key. -/
theorem selbySum_selby (nul : Int64) (k v : Keys) (h : k.count < 2 ^ 32) {ks : RelRep Int64 Int64}
    {e : Int64 → List Int64} (he : ks.app? = some e) {G : RelRep Int64 (List Int64)}
    (hG : Q.grp ks Prod.fst Prod.snd (Q.tab (rows k v)) = some G) {A : RelRep Int64 Int64}
    (hA : G.comp (RelRep.ofFn (qsum nul)) = some A) :
    ∃ g : Int64 → List Int64, A.app? = some (fun c => (e c).map fun c' => qsum nul (g c')) ∧
      ∀ p ∈ selbySum nul k v, p.2 = qsum nul (g p.1) := by
  obtain ⟨X, hX, g, hg, -, hs⟩ := selbySum_spec nul k v h
  exact ⟨g, Q.app?_selby he hX hg hG hA, hs⟩

/-! ## Runs: compressed against `.pairs` -/

def nul : Int64 := Int64.minValue
def ks : List Int64 := [3, 1, 3, 2, 1]
def vs : List Int64 := [10, 20, 30, 40, 50]
/-- One null: `sum` skips it. -/
def vsN : List Int64 := [10, 20, 30, 40, Int64.minValue]

/-- Keys dense `long` (`Order.group`) and packed (`Order.groupFoR`); values dense `short` (`overBytes`
at `i16`), packed (`Coc.over`), and dense `long` with a null. -/
def kD : Keys := .dense 8 (enc 8 ks)
def kF : Keys := Keys.ofList true ks
def vD : Keys := Keys.ofList false vs
def vF : Keys := Keys.ofList true vs
def vN : Keys := Keys.ofList false vsN

#guard Col.sum nul vD == 150 && Col.sum nul vF == 150 && Col.sum nul vN == 100
#guard Q.Agg.sum (Q.Agg.ql (vs.map Int64.toInt)) == some [150]
#guard qsumR nul (Q.Agg.ql (Col.vals vN)) == some [100]
#guard qsumR nul (Q.Agg.ql (Col.vals vF)) == some [150]
-- `where 10110b` (LSB first: 13): rows 0, 2, 3
#guard whereQ 5 ⟨#[13]⟩ == [0, 2, 3]
#guard sumWhere nul 5 ⟨#[13]⟩ vD == 80 && sumWhere nul 5 ⟨#[13]⟩ vF == 80 && sumWhere nul 5 ⟨#[13]⟩ vN == 80
#guard ((Q.Agg.ql (whereQ 5 ⟨#[13]⟩)).comp (Q.Agg.ql (Col.vals vD))).bind (qsumR nul) == some [80]
#guard ((Q.Agg.ql (whereQ 5 ⟨#[13]⟩)).comp (Q.Agg.ql (Col.vals vN))).bind (qsumR nul) == some [80]
#guard selbySum nul kD vD == [(3, 40), (1, 70), (2, 40)]
#guard selbySum nul kF vF == [(3, 40), (1, 70), (2, 40)]
#guard selbySum nul kF vN == [(3, 40), (1, 20), (2, 40)]
-- the `.pairs` `select sum v by k` over the decoded table, keys sorted as q's `s#`
#guard Q.ps (Q.selby (qsum nul) (fun r => r.1.toInt) Prod.snd (Q.tab (rows kD vD))) == some [(1, 70), (2, 40), (3, 40)]
#guard Q.ps (Q.selby (qsum nul) (fun r => r.1.toInt) Prod.snd (Q.tab (rows kF vN))) == some [(1, 20), (2, 40), (3, 40)]

#print axioms qsum_ql
#print axioms Col.sum_eq
#print axioms Col.sum_spec
#print axioms sumWhere_spec
#print axioms groupK_eq
#print axioms xkey_rows
#print axioms selbySum_spec
#print axioms selbySum_selby
#print axioms whereFold_eq
#print axioms grp_eq

end LeetQ.Compressed
