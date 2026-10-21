/-
  q's `a@ks` and `d@ks` on dense `long` columns — eight-byte little-endian payloads, whose meaning is
  `Group.dec` — each run by qlean's C kernels and stated as the `RelRep` pipeline of `Q.Table` it
  computes, read back by `app` (Λ) in row order.
  * `a@ks` is `gatherBytes`: `aIdx_spec`, `Λ(ix(ks) ix(a))`.
  * `d@ks` is `findVec` (q's `?`: each needle's first index, the count when absent), then `gatherBytes`,
    whose fill is `0N` at the count: `getAll_spec`, `ix(ks) look(d)` with `0N` read as `nul`.
  * `d+e` is `findVec`, `gatherBytes`, `Ew.val`, `memberVec` and `whereBits`: `zipD_spec`, at every key
    `Q.zipD`'s answer with q's own `+`.
  The kernel facts `findScalar_eq` and `findVec_spec` are stated here because qlean states none for `?`;
  `val_add` likewise for `Ew.val`.
-/
import LeetQ.Compressed
import QLean.Kernel.Structural
import QLean.Kernel.Elementwise

namespace LeetQ.Long

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ LeetQ.Group
open scoped Freyd.Alg.RelSet.RelRep

/-- Eight, the width of a `long`, as the kernels take it. -/
def w8 : USize := Nat.toUSize 8

theorem w8_toNat : w8.toNat = 8 := toNat_toUSize (by decide)

/-- Element `j` of a dense `long` payload read unsigned: what a gather reads as an index. -/
def ixAt (b : ByteArray) (j : Nat) : Nat := (bitsAt b (j * 8) 8).toNat

/-- `l.flatMap f` where every `f j` is the one value `g j`. -/
theorem flatMap_single_of {β : Type} (f : Nat → List β) (g : Nat → β) :
    (l : List Nat) → (∀ j ∈ l, f j = [g j]) → l.flatMap f = l.map g
  | [], _ => rfl
  | j :: l, h => by
    rw [List.flatMap_cons, List.map_cons, h j List.mem_cons_self,
      flatMap_single_of f g l fun i hi => h i (List.mem_cons_of_mem _ hi)]
    rfl

/-! ## A gather -/

/-- The fill `0N` read back through `gatherBytes`' eight low bytes. -/
theorem fill_nul : (UInt64.ofNat (Compressed.nul.toUInt64.toNat % 2 ^ (8 * 8))).toInt64 = Compressed.nul := by
  decide

/-- **A gather at eight bytes, at one index**: `src`'s element `idx[j]`, or `fill` past the end. -/
theorem gather_at (fill : UInt64) (src idx : ByteArray) (j : Nat) (hj : j < idx.size / 8) :
    atW 8 (gatherBytes w8 fill src idx) j = if ixAt idx j < src.size / 8 then atW 8 src (ixAt idx j)
      else (UInt64.ofNat (fill.toNat % 2 ^ (8 * 8))).toInt64 := by
  obtain ⟨-, hg⟩ := gatherBytes_spec w8 (by rw [w8_toNat]; decide) fill src idx
  rw [w8_toNat] at hg
  rw [atW_eight, hg j hj]
  unfold ixAt
  split
  · rw [atW_eight]
  · rfl

/-- `gatherBytes` at eight bytes holds one `long` per index. -/
theorem gather_size (fill : UInt64) (src idx : ByteArray) : (gatherBytes w8 fill src idx).size / 8 = idx.size / 8 := by
  rw [(gatherBytes_spec w8 (by rw [w8_toNat]; decide) fill src idx).1, w8_toNat, Nat.mul_div_cancel_left _ (by decide)]

/-- **A gather at eight bytes, read back**: element `j` is `src`'s element `idx[j]`, or `fill` past the end. -/
theorem dec_gather (fill : UInt64) (src idx : ByteArray) :
    dec (gatherBytes w8 fill src idx) = (List.range (idx.size / 8)).map fun j =>
      if ixAt idx j < src.size / 8 then atW 8 src (ixAt idx j)
      else (UInt64.ofNat (fill.toNat % 2 ^ (8 * 8))).toInt64 := by
  have hm := gather_size fill src idx
  apply List.ext_getElem (by rw [dec, List.length_map, List.length_range, List.length_map, List.length_range, hm])
  intro j h1 _
  have hj : j < idx.size / 8 := by rw [dec, List.length_map, List.length_range, hm] at h1; exact h1
  simp only [dec, List.getElem_map, List.getElem_range]
  exact gather_at fill src idx j hj

/-- q's `a@ks`: `gatherBytes`, `0N` at an index out of range. -/
def aIdx (a ks : ByteArray) : ByteArray := gatherBytes w8 Compressed.nul.toUInt64 a ks

/-- **`a@ks` is `Λ(ix(ks) ix(a))`** listed in row order, when every index is in range. -/
theorem aIdx_spec (a ks : ByteArray) (h : ∀ j < ks.size / 8, ixAt ks j < a.size / 8) :
    dec (aIdx a ks) = (List.range (ks.size / 8)).flatMap
      (RelRep.vec ((List.range (ks.size / 8)).map (ixAt ks)).toArray rfl ≫ RelRep.vec (dec a).toArray rfl).app := by
  rw [aIdx, dec_gather]
  refine ((flatMap_single_of _ (fun j => atW 8 a (ixAt ks j)) _ fun j hj => ?_).trans
    (List.map_congr_left fun j hj => ?_)).symm
  · have hj := List.mem_range.1 hj
    rw [RelRep.app_comp, RelRep.app_vec, RelRep.app_vec]
    simp only [cast_eq, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, dec,
      List.getElem?_range (h j hj)]
  · rw [if_pos (h j (List.mem_range.1 hj))]

/-! ## q's `?` -/

/-- **q's `?` at an atom** on an integral payload: the least index whose bits are the needle's, the count
when there is none. -/
theorem findScalar_eq (w : USize) (hay : ByteArray) (x : UInt64) (hn : hay.size / w.toNat < USize.size) :
    (findScalar w false hay x).toNat =
      ((List.range (hay.size / w.toNat)).find? fun i => bitsAt hay (i * w.toNat) w.toNat == x).getD
        (hay.size / w.toNat) := by
  have hle : ((List.range (hay.size / w.toNat)).find? fun i => bitsAt hay (i * w.toNat) w.toNat == x).getD
      (hay.size / w.toNat) ≤ hay.size / w.toNat := by
    cases e : (List.range (hay.size / w.toNat)).find? fun i => bitsAt hay (i * w.toNat) w.toNat == x with
    | none => exact Nat.le_refl _
    | some i => exact Nat.le_of_lt (List.mem_range.1 (List.mem_of_find?_eq_some e))
  show (Nat.toUSize (((List.range (hay.size / w.toNat)).find? fun i =>
    bitsAt hay (i * w.toNat) w.toNat == x).getD (hay.size / w.toNat))).toNat = _
  exact USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hle hn)

/-- A `Nat` below `2 ^ 64` through `toUInt64` and `pushBits`' eight low bytes. -/
theorem toNat_ofNat_mod {i : Nat} (h : i < 2 ^ 64) : (UInt64.ofNat ((Nat.toUInt64 i).toNat % 2 ^ (8 * 8))).toNat = i := by
  show (UInt64.ofNat ((UInt64.ofNat i).toNat % 2 ^ 64)).toNat = i
  have e : ∀ n, (UInt64.ofNat n).toNat = n % 2 ^ 64 := fun _ => rfl
  rw [e, e, Nat.mod_mod, Nat.mod_mod, Nat.mod_eq_of_lt h]

/-- **q's `?` at a vector** of `w`-byte elements, `w ≤ 8`: one `long` per needle, `findScalar`'s answer. -/
theorem findVec_spec (w : USize) (hw : w.toNat ≤ 8) (hay ndl : ByteArray) :
    (findVec w false hay ndl).size = 8 * (ndl.size / w.toNat) ∧
    ∀ j < ndl.size / w.toNat, (bitsAt (findVec w false hay ndl) (j * 8) 8).toNat =
      (findScalar w false hay (bitsAt ndl (j * w.toNat) w.toNat)).toNat := by
  let G : Nat → UInt64 := fun j => (findScalar w false hay (bitsAt ndl (j * w.toNat) w.toNat)).toNat.toUInt64
  have hf : findVec w false hay ndl =
      (List.range (ndl.size / w.toNat)).foldl (fun acc j => pushBits acc (G j) 8) ByteArray.empty := by
    simp only [findVec]
    congr 1
    funext acc j
    rw [if_pos hw]
  obtain ⟨hs, -, hg⟩ := foldl_pushBits G 8 (Nat.le_refl 8) (List.range (ndl.size / w.toNat)) ByteArray.empty
  rw [hf]
  refine ⟨by rw [hs, List.length_range]; exact Nat.zero_add _, fun j hj => ?_⟩
  have h := hg j (by rw [List.length_range]; exact hj)
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, List.getElem_range] at h
  rw [Nat.mul_comm j, h]
  have hu := (findScalar w false hay (bitsAt ndl (j * w.toNat) w.toNat)).toNat_lt_size
  exact toNat_ofNat_mod (Nat.lt_of_lt_of_le hu USize.size_le)

/-! ## q's `d@ks` -/

/-- The table a dict's two columns hold: row `i` is `(k[i], v[i])`. -/
def rows (k v : ByteArray) : List (Int64 × Int64) := (List.range (k.size / 8)).map fun i => (atW 8 k i, atW 8 v i)

/-- The first value of `x`'s fibre in the rows over `l`: the value at the first row whose key is `x`. -/
theorem head_sel (f g : Nat → Int64) (x : Int64) : (l : List Nat) →
    ((l.map fun i => (f i, g i)).filterMap (FinRel.sel x)).head? = (l.find? fun i => f i == x).map g
  | [] => rfl
  | i :: l => by
    rw [List.map_cons, List.filterMap_cons, List.find?_cons]
    cases h : f i == x with
    | true =>
      have e : FinRel.sel x (f i, g i) = some (g i) := by unfold FinRel.sel; exact if_pos (eq_of_beq h)
      rw [e]; rfl
    | false =>
      have e : FinRel.sel x (f i, g i) = none := by
        unfold FinRel.sel; -- `beq_self_eq_true` at `Int64` reaches `Classical.choice`; `==` there is `decide`
        exact if_neg fun (e : f i = x) => of_decide_eq_false (h : decide (f i = x) = false) e
      rw [e]; exact head_sel f g x l

/-- Two `long`s' bits are equal exactly when the `long`s are. -/
theorem bits_beq (b c : ByteArray) (i j : Nat) : (bitsAt b (i * 8) 8 == bitsAt c (j * 8) 8) = (atW 8 b i == atW 8 c j) := by
  rw [atW_eight, atW_eight]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq]
  exact ⟨congrArg _, fun e => by rw [← UInt64.toUInt64_toInt64 (bitsAt b _ _), e, UInt64.toUInt64_toInt64]⟩

/-- q's `d@ks` on a dict held as two `long` columns: `findVec`, then `gatherBytes` of `v` there. -/
def getAll (k v ks : ByteArray) : ByteArray := gatherBytes w8 Compressed.nul.toUInt64 v (findVec w8 false k ks)

/-- **`d@ks` looks each needle up**: the first value of its fibre in the dict, `0N` when it has none. -/
theorem getAll_eq (k v ks : ByteArray) (hkv : k.size / 8 = v.size / 8) (hn : k.size / 8 < 2 ^ 32) :
    dec (getAll k v ks) = (List.range (ks.size / 8)).map fun j =>
      (((RelRep.pairs (FinRel.ofList (rows k v))).app (atW 8 ks j)).head?).getD Compressed.nul := by
  have hn' : k.size / w8.toNat < USize.size := by rw [w8_toNat]; exact lt_usize hn
  obtain ⟨hs, hg⟩ := findVec_spec w8 (by rw [w8_toNat]; decide) k ks
  rw [w8_toNat] at hs hg
  rw [getAll, dec_gather, hs, Nat.mul_div_cancel_left _ (by decide)]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.1 hj
  rw [RelRep.app_pairs, FinRel.scanLookup_ofList, rows, head_sel]
  have hx : ixAt (findVec w8 false k ks) j =
      ((List.range (k.size / 8)).find? fun i => atW 8 k i == atW 8 ks j).getD (k.size / 8) := by
    rw [ixAt, hg j hj, findScalar_eq _ _ _ hn', w8_toNat]
    simp only [bits_beq]
  rw [hx]
  cases e : (List.range (k.size / 8)).find? fun i => atW 8 k i == atW 8 ks j with
  | none => rw [Option.getD_none, if_neg (by rw [hkv]; exact Nat.lt_irrefl _), Option.map_none, Option.getD_none, fill_nul]
  | some i =>
    have hi := List.mem_range.1 (List.mem_of_find?_eq_some e)
    rw [Option.getD_some, if_pos (by rw [← hkv]; exact hi), Option.map_some, Option.getD_some]

/-- **`d@ks` is `ix(ks) look(d)`**, Λ listed in row order, with `0N` read as `nul`. -/
theorem getAll_spec (k v ks : ByteArray) (hkv : k.size / 8 = v.size / 8) (hn : k.size / 8 < 2 ^ 32) :
    dec (getAll k v ks) = ((List.range (ks.size / 8)).flatMap
      (Q.getAll (RelRep.pairs (FinRel.ofList (rows k v))) (dec ks).toArray).app).map (·.getD Compressed.nul) := by
  rw [getAll_eq k v ks hkv hn,
    flatMap_single_of _ (fun j => ((RelRep.pairs (FinRel.ofList (rows k v))).app (atW 8 ks j)).head?) _
      fun j hj => ?_, List.map_map]
  · rfl
  · have hj := List.mem_range.1 hj
    rw [Q.getAll, RelRep.app_comp, Q.tab, RelRep.app_vec]
    simp only [cast_eq, List.getElem?_toArray, dec, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil, Q.app_look]

/-! ## q's `in`, and `t ij kt` -/

/-- Eight booleans `c 0 … c 7` as `memberVec` packs them, least significant bit first. -/
def byteOf (c : Nat → Bool) : UInt8 :=
  (List.range 8).foldl (fun byte t => if c t = true then byte ||| (1 <<< t.toUInt8) else byte) 0

/-- `c` at `s < 8`, listed: `byteOf` at it unfolds to the same eight reads. -/
def cl (c0 c1 c2 c3 c4 c5 c6 c7 : Bool) (s : Nat) : Bool := [c0, c1, c2, c3, c4, c5, c6, c7].getD s false

theorem bit_cl : ∀ c0 c1 c2 c3 c4 c5 c6 c7 : Bool, ∀ t < 8,
    ((byteOf (cl c0 c1 c2 c3 c4 c5 c6 c7) >>> t.toUInt8) &&& 1 == 1) = cl c0 c1 c2 c3 c4 c5 c6 c7 t := by
  decide

/-- **Bit `t` of `byteOf c` is `c t`**: `bitAt` reads back what `memberVec` packs. -/
theorem bit_byteOf (c : Nat → Bool) (t : Nat) (ht : t < 8) : ((byteOf c >>> t.toUInt8) &&& 1 == 1) = c t := by
  have h := bit_cl (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) t ht
  match t, ht with
  | 0, _ => exact h
  | 1, _ => exact h
  | 2, _ => exact h
  | 3, _ => exact h
  | 4, _ => exact h
  | 5, _ => exact h
  | 6, _ => exact h
  | 7, _ => exact h

/-- One byte pushed per index: the bytes are `F 0, …, F (L-1)`. -/
theorem data_pushFold (F : Nat → UInt8) : ∀ L : Nat,
    ((List.range L).foldl (fun acc b => acc.push (F b)) ByteArray.empty).data = ((List.range L).map F).toArray
  | 0 => rfl
  | L + 1 => by
    rw [List.range_succ, List.foldl_append, List.map_append, List.foldl_cons, List.foldl_nil, List.map_cons,
      List.map_nil, ← List.push_toArray, ← data_pushFold F L]
    rfl

/-- **q's `x in y` at eight bytes**: bit `i` of `memberVec` is whether `x[i]` occurs in `y`. -/
theorem memberVec_bit (xs hay : ByteArray) (hn : hay.size / 8 < 2 ^ 32) (i : Nat) (hi : i < xs.size / 8) :
    bitAt (memberVec w8 false xs hay) i =
      ((List.range (hay.size / 8)).find? fun p => atW 8 hay p == atW 8 xs i).isSome := by
  have hn' : hay.size / w8.toNat < USize.size := by rw [w8_toNat]; exact lt_usize hn
  let c : Nat → Nat → Bool := fun b t => decide (b * 8 + t < xs.size / w8.toNat) &&
    decide (findScalar w8 false hay (bitsAt xs ((b * 8 + t) * w8.toNat) w8.toNat) < (hay.size / w8.toNat).toUSize)
  have hm : memberVec w8 false xs hay =
      (List.range ((xs.size / w8.toNat + 7) / 8)).foldl (fun acc b => acc.push (byteOf (c b))) ByteArray.empty := rfl
  have hq : i / 8 < (xs.size / w8.toNat + 7) / 8 := by rw [w8_toNat]; omega
  have hd : (memberVec w8 false xs hay)[i / 8]? = some (byteOf (c (i / 8))) := by
    rw [hm]
    show ((List.range _).foldl (fun acc b => acc.push (byteOf (c b))) ByteArray.empty).data[i / 8]? = _
    rw [data_pushFold, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hq, Option.map_some]
  unfold bitAt
  rw [hd, Option.getD_some, bit_byteOf _ _ (Nat.mod_lt i (by decide))]
  simp only [c, Nat.div_add_mod' i 8, w8_toNat]
  have hl : findScalar w8 false hay (bitsAt xs (i * 8) 8) < (hay.size / 8).toUSize ↔
      (findScalar w8 false hay (bitsAt xs (i * 8) 8)).toNat < hay.size / 8 := by
    rw [USize.lt_iff_toNat_lt, toNat_toUSize hn]
  rw [decide_eq_true hi, Bool.true_and, decide_eq_decide.2 hl]
  have hf := findScalar_eq w8 hay (bitsAt xs (i * 8) 8) hn'
  rw [w8_toNat] at hf
  simp only [bits_beq] at hf
  cases e : (List.range (hay.size / 8)).find? fun p => atW 8 hay p == atW 8 xs i with
  | none => rw [e, Option.getD_none] at hf; exact decide_eq_false (by rw [hf]; exact Nat.lt_irrefl _)
  | some p =>
    rw [e, Option.getD_some] at hf
    exact decide_eq_true (by rw [hf]; exact List.mem_range.1 (List.mem_of_find?_eq_some e))

/-- q's `t ij kt` on `t`'s key column `tk` and the keyed table `kk!kv`: `memberVec` marks the rows whose
key `kt` holds, `whereBits` lists them, and `getAll` reads `kv` at each one's first match. The answer is the
kept rows' ids and their `kt` values; `t`'s own columns are `aIdx` at the ids. -/
def ij (tk kk kv : ByteArray) : ByteArray × ByteArray :=
  let r := whereBits (Nat.toUSize (tk.size / 8)) (memberVec w8 false tk kk)
  (r, getAll kk kv (aIdx tk r))

/-- The rows `F` answers, each paired with `g` of its answer, are the rows `F` keeps. -/
theorem flatMap_opt {β : Type} (F : Nat → Option Nat) (g : Nat → β) : (l : List Nat) →
    l.flatMap (fun i => ((F i).map g).toList.map (i, ·)) =
      (l.filter fun i => (F i).isSome).map fun i => (i, g ((F i).getD 0))
  | [] => rfl
  | i :: l => by
    rw [List.flatMap_cons, List.filter_cons, flatMap_opt F g l]
    cases h : F i with
    | none => rfl
    | some p => rw [if_pos (show (some p).isSome = true from rfl), List.map_cons, h]; rfl

theorem zip_map_self {β : Type} (g : Nat → β) : (l : List Nat) → l.zip (l.map g) = l.map fun i => (i, g i)
  | [] => rfl
  | i :: l => by rw [List.map_cons, List.zip_cons_cons, zip_map_self g l, List.map_cons]

/-- **`t ij kt` is `⟨ix, ix tk first(kt)⟩`**: each row of `t`, in order, with the first value of its key's
fibre in `kt`, and no row whose key `kt` lacks. -/
theorem ij_spec (tk kk kv : ByteArray) (hkv : kk.size / 8 = kv.size / 8) (hm : kk.size / 8 < 2 ^ 32)
    (hn : tk.size / 8 < 2 ^ 32) :
    ((List.range ((ij tk kk kv).1.size / 8)).map (ixAt (ij tk kk kv).1)).zip (dec (ij tk kk kv).2) =
      (List.range (tk.size / 8)).flatMap fun i =>
        ((RelRep.pairs (FinRel.ofList (rows kk kv))).first.app (atW 8 tk i)).map (i, ·) := by
  let F : Nat → Option Nat := fun i => (List.range (kk.size / 8)).find? fun p => atW 8 kk p == atW 8 tk i
  let L := (List.range (tk.size / 8)).filter fun i => (F i).isSome
  have hnu : (Nat.toUSize (tk.size / 8)).toNat = tk.size / 8 := toNat_toUSize hn
  obtain ⟨ws, wj⟩ := whereBits_spec (Nat.toUSize (tk.size / 8)) (memberVec w8 false tk kk)
  rw [hnu] at ws wj
  have hL : (List.range (tk.size / 8)).filter (bitAt (memberVec w8 false tk kk)) = L :=
    List.filter_congr fun i hi => memberVec_bit tk kk hm i (List.mem_range.1 hi)
  rw [hL] at ws wj
  have hr : (ij tk kk kv).1 = whereBits (Nat.toUSize (tk.size / 8)) (memberVec w8 false tk kk) := rfl
  have hrs : (ij tk kk kv).1.size / 8 = L.length := by rw [hr, ws, Nat.mul_div_cancel_left _ (by decide)]
  have hLlt : ∀ j (h : j < L.length), L[j] < tk.size / 8 := fun j h =>
    List.mem_range.1 (List.mem_filter.1 (List.getElem_mem h)).1
  have hLsome : ∀ j (h : j < L.length), (F L[j]).isSome = true := fun j h =>
    (List.mem_filter.1 (List.getElem_mem h)).2
  have hij : ∀ j (h : j < L.length), ixAt (ij tk kk kv).1 j = L[j] := fun j h => by rw [ixAt, hr, wj j h]
  have hix : (List.range ((ij tk kk kv).1.size / 8)).map (ixAt (ij tk kk kv).1) = L :=
    List.ext_getElem (by rw [List.length_map, List.length_range, hrs]) fun j h1 _ => by
      rw [List.getElem_map, List.getElem_range, hij j (by rw [List.length_map, List.length_range, hrs] at h1; exact h1)]
  have hk : dec (aIdx tk (ij tk kk kv).1) = L.map (atW 8 tk) := by
    rw [aIdx, dec_gather]
    apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map, hrs])
    intro j h1 _
    rw [List.length_map, List.length_range, hrs] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_map, hij j h1, if_pos (hLlt j h1)]
  have hks : (aIdx tk (ij tk kk kv).1).size / 8 = L.length := by
    have := congrArg List.length hk
    rw [dec, List.length_map, List.length_range, List.length_map] at this
    exact this
  have hw : dec (ij tk kk kv).2 = L.map fun i => atW 8 kv ((F i).getD 0) := by
    show dec (getAll kk kv (aIdx tk (ij tk kk kv).1)) = _
    rw [getAll_eq kk kv _ hkv hm]
    apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map, hks])
    intro j h1 _
    rw [List.length_map, List.length_range, hks] at h1
    have ha : atW 8 (aIdx tk (ij tk kk kv).1) j = atW 8 tk L[j] := by
      have := congrArg (·[j]?) hk
      simp only [dec, List.getElem?_map, List.getElem?_range (hks ▸ h1), Option.map_some,
        List.getElem?_eq_getElem h1, Option.some.injEq] at this
      exact this
    rw [List.getElem_map, List.getElem_range, List.getElem_map, ha, RelRep.app_pairs, FinRel.scanLookup_ofList,
      rows, head_sel]
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hLsome j h1)
    show (((List.range (kk.size / 8)).find? fun i => atW 8 kk i == atW 8 tk L[j]).map (atW 8 kv)).getD _ = _
    rw [show ((List.range (kk.size / 8)).find? fun i => atW 8 kk i == atW 8 tk L[j]) = F L[j] from rfl, hp]
    rfl
  rw [hix, hw, zip_map_self]
  simp only [RelRep.first_eq, RelRep.app_enum, RelRep.app_pairs, FinRel.scanLookup_ofList, rows, head_sel]
  exact (flatMap_opt F (atW 8 kv) _).symm

/-! ## q's `d+e`

`d`'s rows keep their place, and a row that is its key's first in `d` adds `e`'s first value of the key
(`findVec`, `findVec` against `til`, two gathers, `Ew.val`); `e`'s rows whose key `d` lacks follow, every one
(`findVec`, `memberVec` against the count, `whereBits`, two gathers). The addition is q's own, `Ew.intStep`,
so `0N` stays `0N`. -/

/-- One `long` pushed as `Int64.ofNat i` and read back unsigned is `i`. -/
theorem ofNat_bits {i : Nat} (h : i < 2 ^ 32) : (UInt64.ofNat ((Int64.ofNat i).toUInt64.toNat % 2 ^ (8 * 8))).toNat = i := by
  rw [show 8 * 8 = 64 from rfl, ofNat_toNat_mod64]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))

/-- q's `til n` at eight bytes: `n` `long`s, element `i` read unsigned is `i`. -/
theorem til_spec {n : Nat} (hn : n < 2 ^ 32) :
    (tilLongs n.toUSize).size / 8 = n ∧ ∀ i < n, ixAt (tilLongs n.toUSize) i = i := by
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun i : Nat => (Int64.ofNat i).toUInt64) 8 (Nat.le_refl 8) (List.range n)
    ByteArray.empty
  have ht : tilLongs n.toUSize =
      (List.range n).foldl (fun acc i => pushBits acc (Int64.ofNat i).toUInt64 8) ByteArray.empty := by
    unfold tilLongs; rw [toNat_toUSize hn]
  rw [ht]
  refine ⟨by rw [hs, List.length_range, show ByteArray.empty.size = 0 from rfl, Nat.zero_add,
    Nat.mul_div_cancel_left _ (by decide)], fun i hi => ?_⟩
  have h := hg i (by rw [List.length_range]; exact hi)
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, List.getElem_range] at h
  rw [ixAt, Nat.mul_comm i, h]
  exact ofNat_bits (Nat.lt_trans hi hn)

/-- The one-`long` column `[m]`: one element, read unsigned `m`. -/
theorem enc_ix {m : Nat} (h : m < 2 ^ 32) : (enc 8 [Int64.ofNat m]).size / 8 = 1 ∧ ixAt (enc 8 [Int64.ofNat m]) 0 = m := by
  obtain ⟨hs, -, hg⟩ := foldl_pushBits Int64.toUInt64 8 (Nat.le_refl 8) [Int64.ofNat m] ByteArray.empty
  exact ⟨by rw [enc, hs, List.length_singleton]; rfl, (congrArg UInt64.toNat (hg 0 Nat.zero_lt_one)).trans (ofNat_bits h)⟩

/-- q's `b?k`: the first row of `b` whose `long` is `k`, the count when there is none. -/
def first (b : ByteArray) (k : Int64) : Nat :=
  ((List.range (b.size / 8)).find? fun p => atW 8 b p == k).getD (b.size / 8)

/-- `find?` over `range n` answers `q` exactly when `q` is the least index below `n` that `P` holds at. -/
theorem find_range_some (P : Nat → Bool) (n q : Nat) :
    (List.range n).find? P = some q ↔ q < n ∧ P q = true ∧ ∀ j < q, P j = false := by
  rw [List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hq, i, h, he, hall⟩
    rw [List.getElem_range] at he
    subst he
    exact ⟨by rw [List.length_range] at h; exact h, hq, fun j hj => by
      have := hall j hj; rw [List.getElem_range] at this; simpa using this⟩
  · rintro ⟨hn, hq, hall⟩
    exact ⟨hq, q, by rw [List.length_range]; exact hn, List.getElem_range _, fun j hj => by
      rw [List.getElem_range, hall j hj]; rfl⟩

theorem find?_congr {P Q : Nat → Bool} : (l : List Nat) → (∀ p ∈ l, P p = Q p) → l.find? P = l.find? Q
  | [], _ => rfl
  | p :: l, h => by
    rw [List.find?_cons, List.find?_cons, h p List.mem_cons_self,
      find?_congr l fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- `first b k` below the count is a row whose `long` is `k`. -/
theorem atW_first {b : ByteArray} {k : Int64} (h : first b k < b.size / 8) : atW 8 b (first b k) = k := by
  unfold first at *
  cases e : (List.range (b.size / 8)).find? fun p => atW 8 b p == k with
  | none => rw [e, Option.getD_none] at h; exact absurd h (Nat.lt_irrefl _)
  | some q =>
    rw [Option.getD_some]
    exact of_decide_eq_true (((find_range_some _ _ _).1 e).2.1 : decide (atW 8 b q = k) = true)

/-- A row's key first occurs no later than the row. -/
theorem first_le {b : ByteArray} {p : Nat} (hp : p < b.size / 8) : first b (atW 8 b p) ≤ p := by
  unfold first
  cases e : (List.range (b.size / 8)).find? fun i => atW 8 b i == atW 8 b p with
  | none => exact absurd (decide_eq_true rfl) (List.find?_eq_none.1 e p (List.mem_range.2 hp))
  | some q =>
    rw [Option.getD_some]
    exact Nat.le_of_not_lt fun h =>
      Bool.false_ne_true ((((find_range_some _ _ _).1 e).2.2 p h).symm.trans (decide_eq_true rfl))

/-- Row `i` is its key's first exactly when no earlier row has the key. -/
theorem first_self {b : ByteArray} {i : Nat} (hi : i < b.size / 8) :
    first b (atW 8 b i) = i ↔ ((List.range i).find? fun p => atW 8 b p == atW 8 b i) = none := by
  have hs : first b (atW 8 b i) = i ↔ ((List.range (b.size / 8)).find? fun p => atW 8 b p == atW 8 b i) = some i := by
    unfold first
    cases e : (List.range (b.size / 8)).find? fun p => atW 8 b p == atW 8 b i with
    | none => exact ⟨fun h => by rw [Option.getD_none] at h; omega, fun h => nomatch h⟩
    | some q => exact ⟨fun h => by rw [Option.getD_some] at h; rw [h], fun h => by rw [Option.some.inj h]; rfl⟩
  rw [hs, find_range_some, List.find?_eq_none]
  constructor
  · rintro ⟨-, -, h⟩ j hj hc
    exact Bool.false_ne_true ((h j (List.mem_range.1 hj)).symm.trans hc)
  · intro h
    exact ⟨hi, decide_eq_true rfl, fun j hj => Bool.eq_false_iff.2 (h j (List.mem_range.2 hj))⟩

/-- Two `long`s are equal exactly when they are read unsigned as equal. -/
theorem atW_beq (b c : ByteArray) (i j : Nat) : (atW 8 b i == atW 8 c j) = (ixAt b i == ixAt c j) := by
  rw [← bits_beq]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq, ixAt, ixAt]
  exact UInt64.toNat_inj.symm

/-- **`findVec` at eight bytes, read back**: one `long` a needle, each its `first` in `hay`. -/
theorem findVec_ix (hay ndl : ByteArray) (hn : hay.size / 8 < 2 ^ 32) :
    (findVec w8 false hay ndl).size / 8 = ndl.size / 8 ∧
      ∀ j < ndl.size / 8, ixAt (findVec w8 false hay ndl) j = first hay (atW 8 ndl j) := by
  have hn' : hay.size / w8.toNat < USize.size := by rw [w8_toNat]; exact lt_usize hn
  obtain ⟨hs, hg⟩ := findVec_spec w8 (by rw [w8_toNat]; decide) hay ndl
  rw [w8_toNat] at hs hg
  refine ⟨by rw [hs, Nat.mul_div_cancel_left _ (by decide)], fun j hj => ?_⟩
  rw [ixAt, hg j hj, findScalar_eq _ _ _ hn', w8_toNat]
  simp only [bits_beq, first]

/-- The indices `p < n` whose `F p` is `i`, where `F` picks an index no later than its argument and the
same one for every index it maps onto `i`: `i` alone when `F i = i`, none otherwise. -/
theorem find_firsts (F : Nat → Nat) {n i : Nat} (hi : i < n) (hle : ∀ p < n, F p ≤ p)
    (hkey : ∀ p < n, F p = i → F i = i) :
    (List.range n).find? (fun p => F p == i) = if F i = i then some i else none := by
  split
  · rename_i h
    exact (find_range_some _ _ _).2 ⟨hi, beq_iff_eq.2 h, fun j hj =>
      Bool.eq_false_iff.2 fun e => by have := hle j (Nat.lt_trans hj hi); rw [beq_iff_eq.1 e] at this; omega⟩
  · rename_i h
    exact List.find?_eq_none.2 fun p hp e => h (hkey p (List.mem_range.1 hp) (beq_iff_eq.1 e))

/-- **`findVec s (til n)`, `s` each row's `first`**: row `i` where it is its key's first row, `n` elsewhere. -/
theorem firstRows_ix (k : ByteArray) (hn : k.size / 8 < 2 ^ 32) (i : Nat) (hi : i < k.size / 8) :
    ixAt (findVec w8 false (findVec w8 false k k) (tilLongs (k.size / 8).toUSize)) i =
      if first k (atW 8 k i) = i then i else k.size / 8 := by
  obtain ⟨ss, sx⟩ := findVec_ix k k hn
  obtain ⟨ts, tx⟩ := til_spec hn
  obtain ⟨-, wx⟩ := findVec_ix (findVec w8 false k k) (tilLongs (k.size / 8).toUSize) (by rw [ss]; exact hn)
  rw [wx i (by rw [ts]; exact hi)]
  show ((List.range ((findVec w8 false k k).size / 8)).find? fun p =>
    atW 8 (findVec w8 false k k) p == atW 8 (tilLongs (k.size / 8).toUSize) i).getD ((findVec w8 false k k).size / 8) = _
  rw [ss, find?_congr (Q := fun p => first k (atW 8 k p) == i) _ fun p hp => by
      rw [atW_beq, sx p (List.mem_range.1 hp), tx i hi],
    find_firsts _ hi (fun p hp => first_le hp) fun p hp e => ?_]
  · split <;> rfl
  · have := atW_first (b := k) (k := atW 8 k p) (by rw [e]; exact hi)
    rw [e] at this
    rw [this, e]

/-- The first value of `k`'s fibre in `ek!ev`, `0` when it has none. -/
theorem headD_fib (ek ev : ByteArray) (hev : ek.size / 8 = ev.size / 8) (k : Int64) :
    ((rows ek ev).filterMap (FinRel.sel k)).headD 0 =
      if first ek k < ev.size / 8 then atW 8 ev (first ek k) else 0 := by
  rw [List.headD_eq_head?_getD, rows, head_sel]
  unfold first
  rw [← hev]
  cases e : (List.range (ek.size / 8)).find? fun i => atW 8 ek i == k with
  | none => rw [Option.map_none, Option.getD_none, Option.getD_none, if_neg (Nat.lt_irrefl _)]
  | some q => rw [Option.map_some, Option.getD_some, Option.getD_some,
      if_pos (List.mem_range.1 (List.mem_of_find?_eq_some e))]

/-- The fill `0` read back through `gatherBytes`' eight low bytes. -/
theorem fill_zero : (UInt64.ofNat ((0 : UInt64).toNat % 2 ^ (8 * 8))).toInt64 = 0 := by decide

/-- `d`'s right operand of `+`: row `i` gets `e`'s first value of its key where `i` is the key's first row
in `d`, `0` elsewhere and where `e` lacks the key. -/
def firstVals (dk ek ev : ByteArray) : ByteArray :=
  let w := findVec w8 false (findVec w8 false dk dk) (tilLongs (dk.size / 8).toUSize)
  gatherBytes w8 0 ev (gatherBytes w8 (ek.size / 8).toUInt64 (findVec w8 false ek dk) w)

theorem firstVals_at (dk ek ev : ByteArray) (hev : ek.size / 8 = ev.size / 8) (hd : dk.size / 8 < 2 ^ 32)
    (he : ek.size / 8 < 2 ^ 32) (i : Nat) (hi : i < dk.size / 8) :
    atW 8 (firstVals dk ek ev) i = if first dk (atW 8 dk i) = i then
      ((rows ek ev).filterMap (FinRel.sel (atW 8 dk i))).headD 0 else 0 := by
  obtain ⟨gs, gx⟩ := findVec_ix ek dk he
  have hw : (findVec w8 false (findVec w8 false dk dk) (tilLongs (dk.size / 8).toUSize)).size / 8 = dk.size / 8 := by
    rw [(findVec_ix _ _ (by rw [(findVec_ix dk dk hd).1]; exact hd)).1, (til_spec hd).1]
  obtain ⟨-, hg⟩ := gatherBytes_spec w8 (by rw [w8_toNat]; decide) (ek.size / 8).toUInt64 (findVec w8 false ek dk)
    (findVec w8 false (findVec w8 false dk dk) (tilLongs (dk.size / 8).toUSize))
  rw [w8_toNat] at hg
  have ht : ixAt (gatherBytes w8 (ek.size / 8).toUInt64 (findVec w8 false ek dk)
      (findVec w8 false (findVec w8 false dk dk) (tilLongs (dk.size / 8).toUSize))) i =
      if first dk (atW 8 dk i) = i then first ek (atW 8 dk i) else ek.size / 8 := by
    rw [ixAt, hg i (by rw [hw]; exact hi), show ∀ b : ByteArray, (bitsAt b (i * 8) 8).toNat = ixAt b i from fun _ => rfl,
      firstRows_ix dk hd i hi, gs]
    by_cases hf : first dk (atW 8 dk i) = i
    · rw [if_pos hf, if_pos hf, if_pos hi]; exact gx i hi
    · rw [if_neg hf, if_neg hf, if_neg (Nat.lt_irrefl _)]; exact toNat_ofNat_mod (Nat.lt_trans he (by decide))
  show atW 8 (gatherBytes w8 0 ev _) i = _
  rw [gather_at _ _ _ i (by rw [gather_size, hw]; exact hi), ht, fill_zero]
  by_cases hf : first dk (atW 8 dk i) = i
  · rw [if_pos hf, if_pos hf, headD_fib ek ev hev]
  · rw [if_neg hf, if_neg hf, if_neg (by rw [← hev]; exact Nat.lt_irrefl _)]

/-- q's `0 + v` is `v`, `0N` included. -/
theorem add_zero_left (v : Int64) : Ew.intStep Ew.add Compressed.nul 0 v = v := by
  unfold Ew.intStep
  rw [if_pos (by decide : (Ew.add == Ew.add) = true)]
  cases h : (v == Compressed.nul)
  · rw [if_neg (by decide), Int64.zero_add]
  · rw [if_pos (by decide)]
    exact (of_decide_eq_true (h : decide (v = Compressed.nul) = true)).symm

/-- q's `v + 0` is `v`, `0N` included. -/
theorem add_zero_right (v : Int64) : Ew.intStep Ew.add Compressed.nul v 0 = v := by
  unfold Ew.intStep
  rw [if_pos (by decide : (Ew.add == Ew.add) = true)]
  cases h : (v == Compressed.nul)
  · rw [if_neg (by decide), Int64.add_zero]
  · rw [if_pos (by decide)]
    exact (of_decide_eq_true (h : decide (v = Compressed.nul) = true)).symm

theorem map_add_zero : (l : List Int64) → l.map (Ew.intStep Ew.add Compressed.nul 0) = l
  | [] => rfl
  | v :: l => by rw [List.map_cons, add_zero_left, map_add_zero l]

/-- **q's `a+b` on two `long` columns**, `Ew.val`, read back: `n` elements, each `Ew.intStep`'s sum.
To upstream to qlean, which states no reading of `Ew.val`. -/
theorem val_add (a b : ByteArray) {n : Nat} (hn : n < 2 ^ 32) :
    (Ew.val Ew.add Ew.i64 Ew.vv Compressed.nul a b n.toUSize).size / 8 = n ∧ ∀ i < n,
      atW 8 (Ew.val Ew.add Ew.i64 Ew.vv Compressed.nul a b n.toUSize) i =
        Ew.intStep Ew.add Compressed.nul (atW 8 a i) (atW 8 b i) := by
  let G : Nat → UInt64 := fun i =>
    Ew.valStep Ew.add Ew.i64 Compressed.nul.toUInt64 (Ew.elem Ew.i64 a i) (Ew.elem Ew.i64 b i)
  have hv : Ew.val Ew.add Ew.i64 Ew.vv Compressed.nul a b n.toUSize =
      (List.range n).foldl (fun acc i => pushBits acc (G i) 8) ByteArray.empty := by
    unfold Ew.val; rw [toNat_toUSize hn]; rfl
  obtain ⟨hs, -, hg⟩ := foldl_pushBits G 8 (Nat.le_refl 8) (List.range n) ByteArray.empty
  rw [hv]
  refine ⟨by rw [hs, List.length_range, show ByteArray.empty.size = 0 from rfl, Nat.zero_add,
    Nat.mul_div_cancel_left _ (by decide)], fun i hi => ?_⟩
  have h := hg i (by rw [List.length_range]; exact hi)
  rw [show ByteArray.empty.size = 0 from rfl, Nat.zero_add, List.getElem_range, show 8 * 8 = 64 from rfl,
    ofNat_toNat_mod64] at h
  rw [atW_eight, Nat.mul_comm i 8, h, atW_eight, atW_eight]
  rfl

/-- `e`'s rows whose key `d` lacks: `whereBits` of `memberVec` of their `first` in `d` against `d`'s count. -/
def absent (dk ek : ByteArray) : ByteArray :=
  whereBits (ek.size / 8).toUSize (memberVec w8 false (findVec w8 false dk ek) (enc 8 [Int64.ofNat (dk.size / 8)]))

/-- q's `d+e` on two dicts held as `long` columns `dk!dv` and `ek!ev`: `d`'s new values (its keys stay
`dk`), then the keys and values of `e`'s rows whose key `d` lacks. -/
def zipD (dk dv ek ev : ByteArray) : ByteArray × ByteArray × ByteArray :=
  let r := absent dk ek
  (Ew.val Ew.add Ew.i64 Ew.vv Compressed.nul dv (firstVals dk ek ev) (dk.size / 8).toUSize, aIdx ek r, aIdx ev r)

/-- `aIdx` at an index in range. -/
theorem aIdx_at (a ks : ByteArray) (j : Nat) (hj : j < ks.size / 8) (h : ixAt ks j < a.size / 8) :
    atW 8 (aIdx a ks) j = atW 8 a (ixAt ks j) := by
  rw [aIdx, gather_at _ _ _ j hj, if_pos h]

/-- `e`'s rows that `zipD` appends are those whose key has no `first` in `d`, in order. -/
theorem absent_rows (dk ek ev : ByteArray) (hev : ek.size / 8 = ev.size / 8) (hd : dk.size / 8 < 2 ^ 32)
    (he : ek.size / 8 < 2 ^ 32) :
    rows (aIdx ek (absent dk ek)) (aIdx ev (absent dk ek)) =
      ((List.range (ek.size / 8)).filter fun j => dk.size / 8 == first dk (atW 8 ek j)).map
        fun j => (atW 8 ek j, atW 8 ev j) := by
  obtain ⟨qs, qx⟩ := findVec_ix dk ek hd
  obtain ⟨hs1, hix⟩ := enc_ix hd
  obtain ⟨ws, wj⟩ := whereBits_spec (Nat.toUSize (ek.size / 8))
    (memberVec w8 false (findVec w8 false dk ek) (enc 8 [Int64.ofNat (dk.size / 8)]))
  rw [toNat_toUSize he] at ws wj
  have hL : (List.range (ek.size / 8)).filter
      (bitAt (memberVec w8 false (findVec w8 false dk ek) (enc 8 [Int64.ofNat (dk.size / 8)]))) =
      (List.range (ek.size / 8)).filter fun j => dk.size / 8 == first dk (atW 8 ek j) :=
    List.filter_congr fun j hj => by
      have hj := List.mem_range.1 hj
      rw [memberVec_bit _ _ (by rw [hs1]; decide) j (by rw [qs]; exact hj), hs1, List.range_one,
        List.find?_singleton, atW_beq, hix, qx j hj]
      cases dk.size / 8 == first dk (atW 8 ek j) <;> rfl
  rw [hL] at ws wj
  have hrs : (absent dk ek).size / 8 =
      ((List.range (ek.size / 8)).filter fun j => dk.size / 8 == first dk (atW 8 ek j)).length := by
    rw [absent, ws, Nat.mul_div_cancel_left _ (by decide)]
  rw [rows]
  apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map, aIdx, gather_size, hrs])
  intro j h1 _
  rw [List.length_map, List.length_range, aIdx, gather_size, hrs] at h1
  have hlt := List.mem_range.1 (List.mem_filter.1 (List.getElem_mem h1)).1
  have hr : ixAt (absent dk ek) j = _ := wj j h1
  have hjr : j < (absent dk ek).size / 8 := by rw [hrs]; exact h1
  rw [List.getElem_map, List.getElem_range, List.getElem_map, aIdx_at _ _ j hjr (by rw [hr]; exact hlt),
    aIdx_at _ _ j hjr (by rw [hr, ← hev]; exact hlt), hr]

/-- `d`'s fibre of `x` after the bump: its first value plus `c x`, the rest as they were. -/
theorem fib_first (f g : Nat → Int64) (c : Int64 → Int64) (x : Int64) : ∀ n : Nat,
    ((List.range n).map fun i => (f i, Ew.intStep Ew.add Compressed.nul (g i)
        (if ((List.range i).find? fun p => f p == f i) = none then c (f i) else 0))).filterMap (FinRel.sel x) =
      (((List.range n).map fun i => (f i, g i)).filterMap (FinRel.sel x)).modifyHead
        fun a => Ew.intStep Ew.add Compressed.nul a (c x)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, List.filterMap_append, List.filterMap_append,
      fib_first f g c x n, List.map_cons, List.map_cons, List.map_nil, List.map_nil]
    by_cases h : f n = x
    · subst h
      have hs : ∀ v : Int64, FinRel.sel (f n) (f n, v) = some v := fun _ => if_pos rfl
      rw [List.filterMap_cons_some (hs _), List.filterMap_cons_some (hs _), List.filterMap_nil]
      have hh := head_sel f g (f n) (List.range n)
      cases hB : ((List.range n).map fun i => (f i, g i)).filterMap (FinRel.sel (f n)) with
      | nil =>
        rw [hB] at hh
        rw [if_pos (Option.map_eq_none_iff.1 hh.symm)]
        rfl
      | cons a t =>
        rw [hB] at hh
        rw [if_neg fun e => by rw [e] at hh; exact nomatch hh]
        exact congrArg (fun y => List.modifyHead (fun a => Ew.intStep Ew.add Compressed.nul a (c (f n))) (a :: t) ++ [y])
          (add_zero_right (g n))
    · have hs : ∀ v : Int64, FinRel.sel x (f n, v) = none := fun _ => if_neg h
      rw [List.filterMap_cons_none (hs _), List.filterMap_cons_none (hs _), List.filterMap_nil,
        List.append_nil, List.append_nil]

/-- The rows over `l` that `A` keeps by key, at `x`: `x`'s whole fibre when `A x`, nothing otherwise. -/
theorem fib_filter (f g : Nat → Int64) (A : Int64 → Bool) (x : Int64) : (l : List Nat) →
    ((l.filter fun j => A (f j)).map fun j => (f j, g j)).filterMap (FinRel.sel x) =
      if A x then (l.map fun j => (f j, g j)).filterMap (FinRel.sel x) else []
  | [] => by cases A x <;> rfl
  | j :: l => by
    have ih := fib_filter f g A x l
    by_cases h : f j = x
    · subst h
      have hs : FinRel.sel (f j) (f j, g j) = some (g j) := if_pos rfl
      cases hA : A (f j)
      · rw [List.filter_cons_of_neg (p := fun j => A (f j)) (by simp [hA]), ih, hA]; rfl
      · rw [List.filter_cons_of_pos (p := fun j => A (f j)) hA, List.map_cons, List.map_cons, List.filterMap_cons_some hs,
          List.filterMap_cons_some hs, ih, hA]; rfl
    · have hs : FinRel.sel x (f j, g j) = none := if_neg h
      rw [List.map_cons, List.filterMap_cons_none hs, ← ih]
      cases hA : A (f j)
      · rw [List.filter_cons_of_neg (p := fun j => A (f j)) (by simp [hA])]
      · rw [List.filter_cons_of_pos (p := fun j => A (f j)) hA, List.map_cons, List.filterMap_cons_none hs]

/-- `d` lacks `x` exactly when `x`'s fibre in `d` is empty. -/
theorem absent_iff (dk dv : ByteArray) (x : Int64) :
    (dk.size / 8 == first dk x) = ((rows dk dv).filterMap (FinRel.sel x)).isEmpty := by
  have hh := head_sel (atW 8 dk) (atW 8 dv) x (List.range (dk.size / 8))
  unfold first
  rw [rows]
  cases e : (List.range (dk.size / 8)).find? fun i => atW 8 dk i == x with
  | none =>
    rw [e, Option.map_none] at hh
    rw [Option.getD_none, List.head?_eq_none_iff.1 hh]
    exact beq_self_eq_true _
  | some q =>
    rw [e, Option.map_some] at hh
    have hq := List.mem_range.1 (List.mem_of_find?_eq_some e)
    rw [Option.getD_some]
    cases hl : ((List.range (dk.size / 8)).map fun i => (atW 8 dk i, atW 8 dv i)).filterMap (FinRel.sel x) with
    | nil => rw [hl] at hh; exact nomatch hh
    | cons a t => exact beq_false_of_ne (by omega)

/-- **q's `d+e` is `dom(d ∪ e) ⟨Λd, Λe⟩ zipFib ∋`** with q's `+`: at every key `x`, the rows `zipD` answers
with key `x`, in order, are `Q.zipD`'s answer at `x`. -/
theorem zipD_spec (dk dv ek ev : ByteArray) (hev : ek.size / 8 = ev.size / 8)
    (hd : dk.size / 8 < 2 ^ 32) (he : ek.size / 8 < 2 ^ 32) (x : Int64) :
    (rows dk (zipD dk dv ek ev).1 ++ rows (zipD dk dv ek ev).2.1 (zipD dk dv ek ev).2.2).filterMap (FinRel.sel x) =
      (Q.zipD (Ew.intStep Ew.add Compressed.nul) 0 (FinRel.ofList (rows dk dv)) (FinRel.ofList (rows ek ev))).app x := by
  have hdp : rows dk (zipD dk dv ek ev).1 = (List.range (dk.size / 8)).map fun i =>
      (atW 8 dk i, Ew.intStep Ew.add Compressed.nul (atW 8 dv i)
        (if ((List.range i).find? fun p => atW 8 dk p == atW 8 dk i) = none then
          ((rows ek ev).filterMap (FinRel.sel (atW 8 dk i))).headD 0 else 0)) := by
    rw [rows]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.1 hi
    rw [show (zipD dk dv ek ev).1 = Ew.val Ew.add Ew.i64 Ew.vv Compressed.nul dv (firstVals dk ek ev)
      (dk.size / 8).toUSize from rfl, (val_add dv (firstVals dk ek ev) hd).2 i hi, firstVals_at dk ek ev hev hd he i hi]
    by_cases hf : first dk (atW 8 dk i) = i
    · rw [if_pos hf, if_pos ((first_self hi).1 hf)]
    · rw [if_neg hf, if_neg (mt (first_self hi).2 hf)]
  have hz : (rows dk (zipD dk dv ek ev).1 ++ rows (zipD dk dv ek ev).2.1 (zipD dk dv ek ev).2.2).filterMap
      (FinRel.sel x) = Q.zipFib (Ew.intStep Ew.add Compressed.nul) 0
        ((rows dk dv).filterMap (FinRel.sel x), (rows ek ev).filterMap (FinRel.sel x)) := by
    rw [List.filterMap_append, hdp, fib_first (atW 8 dk) (atW 8 dv) (fun k => ((rows ek ev).filterMap (FinRel.sel k)).headD 0) x,
      show (zipD dk dv ek ev).2 = (aIdx ek (absent dk ek), aIdx ev (absent dk ek))
      from rfl, absent_rows dk ek ev hev hd he, fib_filter (atW 8 ek) (atW 8 ev) (fun k => dk.size / 8 == first dk k) x,
      absent_iff dk dv x]
    show List.modifyHead _ ((rows dk dv).filterMap (FinRel.sel x)) ++
      (if ((rows dk dv).filterMap (FinRel.sel x)).isEmpty then (rows ek ev).filterMap (FinRel.sel x) else []) = _
    cases (rows dk dv).filterMap (FinRel.sel x) with
    | nil => exact (map_add_zero _).symm
    | cons a t => exact List.append_nil _
  rw [hz, Q.app_zipD, FinRel.scanLookup_ofList, FinRel.scanLookup_ofList]
  split
  · rfl
  · rename_i hk
    rw [FinRel.toList_union, FinRel.toList_ofList, FinRel.toList_ofList, List.map_append] at hk
    have h1 : ∀ l : List (Int64 × Int64), x ∉ l.map Prod.fst → l.filterMap (FinRel.sel x) = [] := fun l hl =>
      List.filterMap_eq_nil_iff.2 fun p hp => if_neg fun e => hl (List.mem_map.2 ⟨p, hp, e⟩)
    rw [h1 _ fun h => hk (List.mem_append_left _ h), h1 _ fun h => hk (List.mem_append_right _ h)]
    rfl

-- (`a`b`c!1 2 3)+`b`c`d!10 20 30 with keys 1 2 3, 2 3 4: 1 12 23, then 4:30
-- (1 1 2!1 2 3)+1 3!10 20: 11 2 3, then 3:20 ; (1 2 3!1 2 3)+2 2!10 20: 1 12 3, nothing appended
#guard (let z := zipD (enc 8 [1, 2, 3]) (enc 8 [1, 2, 3]) (enc 8 [2, 3, 4]) (enc 8 [10, 20, 30]);
  (dec z.1, dec z.2.1, dec z.2.2)) == ([1, 12, 23], [4], [30])
#guard (let z := zipD (enc 8 [1, 1, 2]) (enc 8 [1, 2, 3]) (enc 8 [1, 3]) (enc 8 [10, 20]);
  (dec z.1, dec z.2.1, dec z.2.2)) == ([11, 2, 3], [3], [20])
#guard (let z := zipD (enc 8 [1, 2, 3]) (enc 8 [1, 2, 3]) (enc 8 [2, 2]) (enc 8 [10, 20]);
  (dec z.1, dec z.2.1, dec z.2.2)) == ([1, 12, 3], [], [])

#print axioms zipD_spec
#print axioms val_add

-- (10 20 30)@2 0 0 5: 30 10 10 0N ; (1 2 1!10 20 30)@1 5 2: 10 0N 20
#guard dec (aIdx (enc 8 [10, 20, 30]) (enc 8 [2, 0, 0, 5])) == [30, 10, 10, Compressed.nul]
#guard dec (getAll (enc 8 [1, 2, 1]) (enc 8 [10, 20, 30]) (enc 8 [1, 5, 2])) == [10, Compressed.nul, 20]

-- ([] k:1 2 3 2 9) ij ([k:2 3 2] w:20 30 21): rows 1 2 3, w 20 30 20 — the first match
#guard (let p := ij (enc 8 [1, 2, 3, 2, 9]) (enc 8 [2, 3, 2]) (enc 8 [20, 30, 21]); (dec p.1, dec p.2)) ==
  ([1, 2, 3], [20, 30, 20])

#print axioms ij_spec
#print axioms memberVec_bit
#print axioms aIdx_spec
#print axioms getAll_spec
#print axioms findVec_spec
#print axioms getAll_eq
#print axioms head_sel
#print axioms bits_beq
#print axioms findScalar_eq
#print axioms dec_gather

end LeetQ.Long
