/-
  q's `sum`, `where`, `sum v where b` and `select sum v by k` run on qlean's compressed columns: a
  value column is a `Keys` (`QRel.lean`), a dense `w`-byte payload or a Frame-of-Reference pack, and
  every element is read from the packed bytes (`atW`, `foRBits`) — no operator here builds the decoded
  value list. `Keys.vals`, that list, appears only in the statements, as the meaning of the column.
  Each operator is stated against the `.pairs` pipeline it implements (`Q.Agg.ql`, `RelRep.comp`,
  `Q.Agg.sum`, `Q.xkey`), at list level: order and repeats are part of what is equal.
  * `sum` is qlean's `overBytes .add` on a dense payload and `Coc.over .add` on a pack, whose C reads
    each block's metadata; `sum_spec`: `ql(vs) ; (≠ 0N)? ; toInt ; sum`, wrapped to 64 bits.
  * `sumWhere` is `whereBits`, then `gatherBytes` of `v` at those indices, then `overBytes .add`;
    `sumWhere_spec`: `ql(where b) ; ql(vs) ; (≠ 0N)? ; toInt ; sum`.
  * `selbySum` is `Order.groupIds`/`groupIdsFoR` on the key column, then `overGroups .add` of `v`;
    `selbySum_spec`: each key's sum is q's sum of `xkey`'s fibre, the per-key entry of `app?_selby`.
  q's `sum` skips the null `nul` and wraps at 64 bits, as `Coc.Over.step .add` does.
-/
import LeetQ.Group
import LeetQ.Q.Agg
import LeetQ.Q.Table

namespace LeetQ.Compressed

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ LeetQ.Group
open QLean.Kernel.Scan (Kind)

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

theorem rdOf_get (c : Keys) (i : Nat) : (rdOf c).get i = c.get i := by
  cases c with
  | dense w b =>
    simp only [rdOf, Rd.get]; split
    · rename_i hw; rw [ld_eq, signed_clsW hw]; rfl
    · rfl
  | foR n md pk => rfl

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

/-! ## A value column as the kernels read it -/

theorem width_bounds (cls : UInt8) : 1 ≤ Ew.width cls ∧ Ew.width cls ≤ 8 := by
  unfold Ew.width; repeat' split
  all_goals decide

/-- `v`'s first `m` elements as a dense payload of a signed class: `v`'s own bytes at a width a class
covers, a pack decoded by the C, and a re-encoding at eight bytes at the widths no class covers. -/
def vpay (m : USize) : Keys → UInt8 × ByteArray
  | .dense w b => if Signed w then (clsW w, b) else (Ew.i64, enc 8 ((List.range m.toNat).map (atW w b)))
  | .foR _ md pk => (Ew.i64, decoded m md pk)

/-- **`vpay` holds `v`'s first `m` elements**, read at its class. -/
theorem vpay_spec (m : USize) (v : Keys) (hm : m.toNat ≤ v.count) :
    m.toNat ≤ (vpay m v).2.size / Ew.width (vpay m v).1 ∧
    ∀ i < m.toNat, Ew.signed (vpay m v).1 (Ew.elem (vpay m v).1 (vpay m v).2 i) = v.get i := by
  have h8 : Ew.width Ew.i64 = 8 := rfl
  have s8 : ∀ x : UInt64, Ew.signed Ew.i64 x = x.toInt64 := fun _ => rfl
  cases v with
  | dense w b =>
    simp only [vpay]; split
    · rename_i hw
      refine ⟨by rw [width_clsW hw]; exact hm, fun i _ => ?_⟩
      simp only [Ew.elem, width_clsW hw, signed_clsW hw]; rfl
    · refine ⟨by rw [h8, enc_size (by decide), List.length_map, List.length_range]; omega, fun i hi => ?_⟩
      simp only [Ew.elem, h8, s8]
      rw [← atW_eight, atW_enc (by decide) _ i (by simp; omega) (fits_eight _), List.getElem_map, List.getElem_range]
      rfl
  | foR n md pk =>
    obtain ⟨hc, hs, hcol⟩ := decoded_spec m md pk
    refine ⟨by simp only [vpay, h8, hs]; exact Nat.le_refl _, fun i hi => ?_⟩
    have := congrArg (·[i]?) hcol
    simp only [col, colFoR, hc, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.some.injEq] at this
    simp only [vpay, Ew.elem, h8, s8]; rw [← atW_eight, this]; rfl

/-! ## `where`, and `sum v where b` -/

/-- `sum v where b`: `whereBits` answers the indices, `gatherBytes` reads `v` at them, `overBytes .add`
sums what it read. -/
def sumWhere (nul : Int64) (n : USize) (bits : ByteArray) (v : Keys) : Int64 :=
  let p := vpay n v
  overBytes .add p.1 nul (gatherBytes (Ew.width p.1).toUSize 0 p.2 (whereBits n bits))

theorem sumWhere_eq (nul : Int64) (n : USize) (bits : ByteArray) (v : Keys) (h : n.toNat < 2 ^ 63)
    (hv : n.toNat ≤ v.count) :
    sumWhere nul n bits v = qsum nul (((List.range n.toNat).filter (bitAt bits)).map v.get) := by
  simp only [sumWhere]
  obtain ⟨hm, hg⟩ := vpay_spec n v hv
  generalize vpay n v = p at hm hg ⊢
  obtain ⟨c, b⟩ := p
  dsimp only at hm hg ⊢
  obtain ⟨w1, w8⟩ := width_bounds c
  have hw : (Ew.width c).toUSize.toNat = Ew.width c := toNat_toUSize (by omega)
  have hL' : ∀ x ∈ (List.range n.toNat).filter (bitAt bits), x < n.toNat := fun x hx =>
    List.mem_range.1 (List.mem_filter.1 hx).1
  obtain ⟨gs, gj⟩ := gatherBytes_whereBits _ (by rw [hw]; exact w8) 0 b n bits
    fun i hi => by rw [hw]; have := hL' i hi; omega
  rw [hw] at gs gj
  have hs : Coc.Over.denseSeed .add c nul = 0 := by simp [Coc.Over.denseSeed, Coc.Over.seed]
  rw [overBytes_eq, foldl_filter, hs]
  have hq : ∀ l : List Int64, l.foldl (fun acc x => if (Coc.Over.add.boolCast || x != nul) = true then
      Coc.Over.add.step acc x else acc) 0 = qsum nul l := fun l => by
    rw [qsum]; congr 1; funext acc x
    cases h : x == nul <;> simp only [bne, h, Coc.Over.boolCast, Bool.not_true, Bool.not_false, Bool.or_false,
      Bool.or_true, Bool.false_eq_true, ↓reduceIte] <;> rfl
  rw [hq]
  congr 1
  apply List.ext_getElem
  · rw [denseElems, List.length_map, List.length_range, gs, List.length_map,
      Nat.mul_div_cancel_left _ (by omega : 0 < Ew.width c)]
  · intro j _ h2
    have hj' : j < ((List.range n.toNat).filter (bitAt bits)).length := by rw [List.length_map] at h2; exact h2
    have hl := hL' _ (List.getElem_mem hj')
    simp only [denseElems, List.getElem_map, List.getElem_range]
    rw [Ew.elem, gj j hj']
    exact hg _ hl

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
  rw [sumWhere_eq nul n bits v h hv, ← whereQ_eq n bits h, qsum_eq]

/-! ## `group` and `select sum v by k` -/

/-- Two `w`-byte elements are equal exactly when their bits are. -/
theorem atW_inj {w : Nat} (hw : w ≤ 8) (b : ByteArray) (i j : Nat) :
    atW w b i = atW w b j ↔ bitsAt b (i * w) w = bitsAt b (j * w) w := by
  refine ⟨fun e => ?_, fun e => by rw [atW, atW, e]⟩
  have e' := congrArg Int64.toInt e
  rw [toInt_atW hw, toInt_atW hw] at e'
  exact (sx_inj (bitsAt_lt b (i * w) w hw) (bitsAt_lt b (j * w) w hw)).1 e'

/-- The group ids of a key column: `groupIds` at the kind of the key's width, `groupIdsFoR` on a pack,
and `groupIds` on the key re-encoded at eight bytes at a width no kind has. -/
def gids : Keys → ByteArray × ByteArray
  | .dense w b => match kindW w with
    | some kd => Order.groupIds kd (b.size / w).toUSize b
    | none => Order.groupIds .i64 (b.size / w).toUSize (enc 8 ((List.range (b.size / w)).map (atW w b)))
  | .foR n md pk => Order.groupIdsFoR .i64 n.toUSize md pk

/-- Group ids over a key `g'` are group ids over any `g` that agrees where `g'` does. -/
theorem ids_congr {β : Type} [DecidableEq β] {g' : Nat → β} {g : Nat → Int64} {m : Nat} (r : ByteArray × ByteArray)
    (hr : ids r.1 = (List.range m).map (groupOf g' m) ∧ ids r.2 = firstsOf g' m)
    (h : ∀ i < m, ∀ j < m, (g' i = g' j ↔ g i = g j)) :
    ids r.1 = (List.range m).map (groupOf g m) ∧ ids r.2 = firstsOf g m := by
  obtain ⟨hf, -, hg⟩ := groups_congr g' m h
  exact ⟨hr.1.trans (List.map_congr_left fun i hi => hg i (List.mem_range.1 hi)), hr.2.trans hf⟩

/-- **`gids` answers each row's group and the first occurrences of the key column.** -/
theorem gids_spec (k : Keys) (h : k.count < 2 ^ 32) :
    ids (gids k).1 = (List.range k.count).map (groupOf k.get k.count) ∧ ids (gids k).2 = firstsOf k.get k.count := by
  cases k with
  | dense w b =>
    simp only [Keys.count] at h ⊢
    simp only [gids]
    split
    · rename_i kd hkd
      obtain ⟨hk, hw, hav⟩ := kindW_spec hkd
      have w8 : w ≤ 8 := by rw [← hw]; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
      have := groupIds_spec kd (b.size / w).toUSize b
      rw [toNat_toUSize h, hav, Nat.min_self] at this
      refine ids_congr _ this fun i _ j _ => ?_
      show _ ↔ atW w b i = atW w b j
      rw [keyAt_eq_iff hk, hw, atW_inj w8]
    · have e : ∀ i < b.size / w, atW 8 (enc 8 ((List.range (b.size / w)).map (atW w b))) i = atW w b i :=
        fun i hi => by
          rw [atW_enc (by decide) _ i (by simp only [List.length_map, List.length_range]; exact hi) (fits_eight _),
            List.getElem_map, List.getElem_range]
      have := groupIds_spec .i64 (b.size / w).toUSize (enc 8 ((List.range (b.size / w)).map (atW w b)))
      have hav : Kind.avail .i64 (enc 8 ((List.range (b.size / w)).map (atW w b))) = b.size / w := by
        show (enc 8 _).size / 8 = _
        rw [enc_size (by decide), List.length_map, List.length_range]; omega
      rw [toNat_toUSize h, hav, Nat.min_self] at this
      refine ids_congr _ this fun i hi j hj => ?_
      show _ ↔ atW w b i = atW w b j
      rw [keyAt_eq_iff (by decide), ← e i hi, ← e j hj]
      exact (atW_inj (by decide) _ i j).symm
  | foR n md pk =>
    simp only [Keys.count] at h ⊢
    have := groupIdsFoR_spec .i64 (by decide) n.toUSize md pk
    rw [toNat_toUSize h] at this
    refine ids_congr _ this fun i _ j _ => ?_
    show _ ↔ (foRBits md pk (blockStarts md) i).toInt64 = (foRBits md pk (blockStarts md) j).toInt64
    simp only [show 8 * Kind.width .i64 = 64 from rfl, ofNat_toNat_mod64, Order.rank]
    rw [UInt64.xor_left_inj]
    exact ⟨congrArg _, fun e => by
      rw [← UInt64.toUInt64_toInt64 (foRBits md pk (blockStarts md) i), e, UInt64.toUInt64_toInt64]⟩

/-- The rows of `l` pushed onto their groups' buckets, the group read off `gid`. -/
def buckets (gid : ByteArray) (l : List Nat) (a : Array (Array Nat)) : Array (Array Nat) :=
  l.foldl (fun a i => a.modify (gidAt gid i) (·.push i)) a

theorem buckets_get (gid : ByteArray) : ∀ (l : List Nat) (a : Array (Array Nat)) (j : Nat),
    ((buckets gid l a)[j]?).map Array.toList = (a[j]?).map fun x => x.toList ++ l.filter fun i => gidAt gid i == j
  | [], a, j => by simp only [buckets, List.foldl_nil, List.filter_nil, List.append_nil]
  | i :: l, a, j => by
    rw [buckets, List.foldl_cons, ← buckets, buckets_get gid l, Array.getElem?_modify]
    split
    · rename_i e
      rw [List.filter_cons_of_pos (p := fun i => gidAt gid i == j) (beq_iff_eq.2 (by omega))]
      cases a[j]? with
      | none => rfl
      | some x => simp only [Option.map_some, Array.toList_push, List.append_assoc, List.singleton_append]
    · rename_i e
      rw [List.filter_cons_of_neg (p := fun i => gidAt gid i == j) (fun h => e (by have := beq_iff_eq.1 h; omega))]

/-- `group` on a key column: `gids`' ids, each row pushed onto its group's bucket in one pass. -/
def groupK (k : Keys) : List (Int64 × List Nat) :=
  let r := gids k; let ng := r.2.size / 8; let rk := Col.rdOf k
  let bk := buckets r.1 (List.range (r.1.size / 8)) (Array.replicate ng #[])
  (List.range ng).map fun j => (rk.get (bitsAt r.2 (j * 8) 8).toNat, (bk[j]?.getD #[]).toList)

theorem ng_eq {k : Keys} {r : ByteArray × ByteArray} (h2 : ids r.2 = firstsOf k.get k.count) :
    r.2.size / 8 = (firstsOf k.get k.count).length := by
  have := congrArg List.length h2; rw [ids, List.length_map, List.length_range] at this; exact this

/-- **`groupK` answers each first key with its bucket.** -/
theorem groupK_eq (k : Keys) (h : k.count < 2 ^ 32) : groupK k = dictOf k.get k.count := by
  obtain ⟨h1, h2⟩ := gids_spec k h
  simp only [groupK, Col.rdOf_get]
  generalize gids k = r at h1 h2
  have hl1 : r.1.size / 8 = k.count := by
    have := congrArg List.length h1; rw [ids, List.length_map, List.length_range, List.length_map,
      List.length_range] at this; exact this
  have hng := ng_eq h2
  apply List.ext_getElem (by rw [List.length_map, List.length_range, length_dictOf, hng])
  intro j hj1 hj2
  have hjf : j < (firstsOf k.get k.count).length := by rw [length_dictOf] at hj2; exact hj2
  have hb := buckets_get r.1 (List.range (r.1.size / 8)) (Array.replicate (r.2.size / 8) #[]) j
  rw [Array.getElem?_replicate, if_pos (by omega), Option.map_some] at hb
  have hb' : ((buckets r.1 (List.range (r.1.size / 8)) (Array.replicate (r.2.size / 8) #[]))[j]?.getD #[]).toList =
      (List.range (r.1.size / 8)).filter fun i => gidAt r.1 i == j := by
    -- `simp` here brings `Classical.choice`
    cases e : (buckets r.1 (List.range (r.1.size / 8)) (Array.replicate (r.2.size / 8) #[]))[j]? with
    | none => rw [e] at hb; cases hb
    | some x => rw [e, Option.map_some] at hb; rw [Option.getD_some]; exact Option.some.inj hb
  simp only [dictOf, List.getElem_map, List.getElem_range]
  rw [ids_get h2 hjf, ← rows_groupOf _ _ hjf, hb', hl1]
  congr 1
  exact List.filter_congr fun i hi => by
    rw [gidAt, ids_get h1 (by simp only [List.length_map, List.length_range]; exact List.mem_range.1 hi),
      List.getElem_map, List.getElem_range]

/-- `select sum v by k`: the key's group ids, then `overGroups .add` sums `v` per group in one pass. -/
def selbySum (nul : Int64) (k v : Keys) : List (Int64 × Int64) :=
  let r := gids k; let p := vpay k.count.toUSize v; let ng := r.2.size / 8; let rk := Col.rdOf k
  let o := overGroups .add p.1 nul ng.toUSize r.1 p.2
  (List.range ng).map fun j => (rk.get (bitsAt r.2 (j * 8) 8).toNat, (bitsAt o (j * 8) 8).toInt64)

theorem selbySum_eq (nul : Int64) (k v : Keys) (h : k.count < 2 ^ 32) (hv : k.count ≤ v.count) :
    selbySum nul k v = (dictOf k.get k.count).map fun p => (p.1, p.2.foldl (Col.step nul v) 0) := by
  obtain ⟨h1, h2⟩ := gids_spec k h
  have hm := toNat_toUSize h
  obtain ⟨pm, pg⟩ := vpay_spec k.count.toUSize v (by rw [hm]; exact hv)
  rw [hm] at pm pg
  simp only [selbySum, Col.rdOf_get]
  generalize gids k = r at h1 h2
  generalize vpay k.count.toUSize v = p at pm pg ⊢
  obtain ⟨c, b⟩ := p
  dsimp only at pm pg ⊢
  have hl1 : r.1.size / 8 = k.count := by
    have := congrArg List.length h1; rw [ids, List.length_map, List.length_range, List.length_map,
      List.length_range] at this; exact this
  have hng := ng_eq h2
  have hfl : (firstsOf k.get k.count).length ≤ k.count := by
    rw [firstsOf]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_range]; exact Nat.le_refl _)
  have hnu : (r.2.size / 8).toUSize.toNat = r.2.size / 8 := toNat_toUSize (by omega)
  have hs : Coc.Over.denseSeed .add c nul = 0 := by simp [Coc.Over.denseSeed, Coc.Over.seed]
  apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map, length_dictOf, hng])
  intro j hj1 hj2
  have hjf : j < (firstsOf k.get k.count).length := by rw [List.length_map, length_dictOf] at hj2; exact hj2
  simp only [dictOf, List.getElem_map, List.getElem_range]
  rw [ids_get h2 hjf, (overGroups_buckets (op := .add) (cls := c) (nul := nul) (r.2.size / 8).toUSize r.1 b h1 pm (by omega) hjf).1, foldl_filter,
    hs]
  congr 1
  refine List.foldl_rel (r := Eq) rfl fun i hi a _ e => e ▸ ?_
  have hi := List.mem_range.1 (List.mem_filter.1 hi).1
  rw [valAt, pg i hi]
  simp only [Col.step]
  cases hn : v.get i == nul <;>
    simp only [bne, hn, Coc.Over.boolCast, Bool.not_true, Bool.not_false, Bool.or_false, Bool.and_false,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte] <;> rfl

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
theorem selbySum_spec (nul : Int64) (k v : Keys) (h : k.count < 2 ^ 32) (hv : k.count ≤ v.count) :
    ∃ X, Q.xkey Prod.fst Prod.snd (Q.tab (rows k v)) = some X ∧ ∃ g, X.app? = some g ∧
      (selbySum nul k v).map Prod.fst = (firstsOf k.get k.count).map k.get ∧
      ∀ p ∈ selbySum nul k v, p.2 = qsum nul (g p.1) := by
  obtain ⟨X, hX, hg⟩ := xkey_rows k.get v.get k.count
  refine ⟨X, hX, _, hg, ?_, fun p hp => ?_⟩
  · rw [selbySum_eq nul k v h hv, List.map_map]; exact dict_keys _ _
  · rw [selbySum_eq nul k v h hv, dictOf, List.map_map] at hp
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hp
    exact Col.foldl_step nul v _

/-- **The per-key entry of `app?_selby`**: `select agg v by k` over `rows`, with `agg` q's sum,
answers at `c` the sums of the keys `ks` lists, each `selbySum`'s entry for that key. -/
theorem selbySum_selby (nul : Int64) (k v : Keys) (h : k.count < 2 ^ 32) (hv : k.count ≤ v.count) {ks : RelRep Int64 Int64}
    {e : Int64 → List Int64} (he : ks.app? = some e) {G : RelRep Int64 (List Int64)}
    (hG : Q.grp ks Prod.fst Prod.snd (Q.tab (rows k v)) = some G) {A : RelRep Int64 Int64}
    (hA : G.comp (RelRep.ofFn (qsum nul)) = some A) :
    ∃ g : Int64 → List Int64, A.app? = some (fun c => (e c).map fun c' => qsum nul (g c')) ∧
      ∀ p ∈ selbySum nul k v, p.2 = qsum nul (g p.1) := by
  obtain ⟨X, hX, g, hg, -, hs⟩ := selbySum_spec nul k v h hv
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
#print axioms sumWhere_eq
#print axioms selbySum_eq

end LeetQ.Compressed
