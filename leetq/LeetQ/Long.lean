/-
  q's `a@ks` and `d@ks` on dense `long` columns — eight-byte little-endian payloads, whose meaning is
  `Group.dec` — each run by qlean's C kernels and stated as the `RelRep` pipeline of `Q.Table` it
  computes, read back by `app` (Λ) in row order.
  * `a@ks` is `gatherBytes`: `aIdx_spec`, `Λ(ix(ks) ix(a))`.
  * `d@ks` is `findVec` (q's `?`: each needle's first index, the count when absent), then `gatherBytes`,
    whose fill is `0N` at the count: `getAll_spec`, `ix(ks) look(d)` with `0N` read as `nul`.
  The kernel facts `findScalar_eq` and `findVec_spec` are stated here because qlean states none for `?`.
-/
import LeetQ.Compressed

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

/-- **A gather at eight bytes, read back**: element `j` is `src`'s element `idx[j]`, or `fill` past the end. -/
theorem dec_gather (fill : UInt64) (src idx : ByteArray) :
    dec (gatherBytes w8 fill src idx) = (List.range (idx.size / 8)).map fun j =>
      if ixAt idx j < src.size / 8 then atW 8 src (ixAt idx j)
      else (UInt64.ofNat (fill.toNat % 2 ^ (8 * 8))).toInt64 := by
  obtain ⟨hs, hg⟩ := gatherBytes_spec w8 (by rw [w8_toNat]; decide) fill src idx
  rw [w8_toNat] at hs hg
  have hm : (gatherBytes w8 fill src idx).size / 8 = idx.size / 8 := by
    rw [hs, Nat.mul_div_cancel_left _ (by decide)]
  apply List.ext_getElem (by rw [dec, List.length_map, List.length_range, List.length_map, List.length_range, hm])
  intro j h1 _
  have hj : j < idx.size / 8 := by rw [dec, List.length_map, List.length_range, hm] at h1; exact h1
  simp only [dec, List.getElem_map, List.getElem_range]
  rw [atW_eight, hg j hj]
  unfold ixAt
  split
  · rw [atW_eight]
  · rfl

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
