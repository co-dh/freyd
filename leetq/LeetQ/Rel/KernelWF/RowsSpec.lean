/-
  What `Vals.pick` at an array side reads its rows' slices with, read back: `slices` clamps each row's
  `[lo, hi)` into the payload `[0, p]` as `Vals.row` does (`Ew.val` lesser, greater, sub), `p` below `2^63`
  where a long reads as its own value.
-/
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.CrossSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-- `Ew.val` on longs at `va`, element `i` below the count: `valStep` of `a`'s long `i` and `b`'s first. -/
theorem val_va_get (op : UInt8) (a b : ByteArray) (n : USize) {i : Nat} (hi : i < n.toNat) :
    Column.bitsAt (Kernel.Ew.val op Ew.i64 Ew.va nul a b n) (i * 8) 8 =
      Ew.valStep op Ew.i64 nul.toUInt64 (Column.bitsAt a (i * 8) 8) (Column.bitsAt b 0 8) := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  have h := congrArg (·[i]?) (elemsW_val op Ew.i64 Ew.va nul a b n)
  have hs : (Kernel.Ew.val op Ew.i64 Ew.va nul a b n).size / 8 = n.toNat := by
    have := len_val op Ew.va a b n; simpa [len] using this
  simp only [elemsW, hw, hs, List.getElem?_map, List.getElem?_range, hi, Option.map_some,
    Option.some.injEq] at h
  rw [h]
  simp (config := {decide := true}) only [Ew.shapeIdx, Ew.elem, hw, ↓reduceIte, Nat.zero_mul]
  generalize Ew.valStep op Ew.i64 nul.toUInt64 _ _ = v
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ (8 * 8) from v.toNat_lt), UInt64.ofNat_toNat]

/-- An `Int64` of value `q`, `0 ≤ q < 2^63`, is the long `q`. -/
theorem toUInt64_of_toInt {z : Int64} {q : Nat} (hq : q < 2 ^ 63) (h : z.toInt = q) :
    z.toUInt64 = UInt64.ofNat q := by
  rw [int64_eq_ofNat hq h]; rfl

/-- `valStep` lesser then greater, the long `x` clamped into `[0, p]`, `p` below `2^63`: the signed
    value of `x` clamped, as `Vals.row` clamps `lo` and `hi`. -/
theorem valStep_clamp (x : UInt64) {p : Nat} (hp : p < 2 ^ 63) :
    Ew.valStep Ew.greater Ew.i64 nul.toUInt64 (Ew.valStep Ew.lesser Ew.i64 nul.toUInt64 x (UInt64.ofNat p))
      (UInt64.ofNat 0) = UInt64.ofNat (min (max x.toInt64.toInt 0).toNat p) := by
  have ep : (UInt64.ofNat p).toInt64.toInt = p := Int64.toInt_ofNat_of_lt hp
  have e0 : (UInt64.ofNat 0).toInt64.toInt = 0 := rfl
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.lesser, Ew.greater]
  simp only [↓reduceIte]
  apply toUInt64_of_toInt (by omega)
  simp only [Int64.toInt64_toUInt64]
  split <;> split <;> simp_all [Int64.lt_iff_toInt_lt] <;> omega

/-- `valStep` greater on two longs below `2^63` is their maximum. -/
theorem valStep_max {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Ew.valStep Ew.greater Ew.i64 nul.toUInt64 (UInt64.ofNat a) (UInt64.ofNat b) = UInt64.ofNat (max a b) := by
  have ea : (UInt64.ofNat a).toInt64.toInt = a := Int64.toInt_ofNat_of_lt ha
  have eb : (UInt64.ofNat b).toInt64.toInt = b := Int64.toInt_ofNat_of_lt hb
  simp (config := {decide := true}) only [Ew.valStep, Ew.intStep, Ew.signed, Ew.greater]
  simp only [↓reduceIte]
  apply toUInt64_of_toInt (by omega)
  split <;> simp_all [Int64.lt_iff_toInt_lt] <;> omega

/-- `p` as the long `UInt64.ofNat p`. -/
theorem usize_toUInt64 (p : USize) : p.toUInt64 = UInt64.ofNat p.toNat :=
  UInt64.toNat_inj.1 (by rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le p.toNat_lt_size USize.size_le)]; simp)

/-- **`slices` read back**: row `k`'s start is its `lo` clamped into `[0, p]`, its count its `hi` clamped
    there less that start, or `0` where the clamped `hi` is below it — the positions `Vals.row` reads. -/
theorem slices_get {p n : USize} (hp : p.toNat < 2 ^ 63) (lo hi : ByteArray) {k : Nat} (hk : k < n.toNat) :
    Column.bitsAt (slices p n lo hi).1 (k * 8) 8 =
        UInt64.ofNat (min (max (Column.bitsAt lo (k * 8) 8).toInt64.toInt 0).toNat p.toNat) ∧
      Column.bitsAt (slices p n lo hi).2 (k * 8) 8 =
        UInt64.ofNat (min (max (Column.bitsAt hi (k * 8) 8).toInt64.toInt 0).toNat p.toNat -
          min (max (Column.bitsAt lo (k * 8) 8).toInt64.toInt 0).toNat p.toNat) := by
  have hc : ∀ b : ByteArray, Column.bitsAt (Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul
      (Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul b (one p.toUInt64) n) (one 0) n) (k * 8) 8 =
      UInt64.ofNat (min (max (Column.bitsAt b (k * 8) 8).toInt64.toInt 0).toNat p.toNat) := fun b => by
    rw [val_va_get _ _ _ _ hk, val_va_get _ _ _ _ hk, bitsAt_one, bitsAt_one, usize_toUInt64]
    exact valStep_clamp _ hp
  refine ⟨hc lo, ?_⟩
  generalize hL : min (max (Column.bitsAt lo (k * 8) 8).toInt64.toInt 0).toNat p.toNat = L
  generalize hH : min (max (Column.bitsAt hi (k * 8) 8).toInt64.toInt 0).toNat p.toNat = H
  have hL' : L ≤ p.toNat := hL ▸ Nat.min_le_right _ _
  have hH' : H ≤ p.toNat := hH ▸ Nat.min_le_right _ _
  have tn : ∀ q, q < 2 ^ 63 → (UInt64.ofNat q).toNat = q := fun q hq =>
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hq (by decide))
  have hM : Column.bitsAt (Kernel.Ew.val Ew.greater Ew.i64 Ew.vv nul
      (Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul
        (Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul hi (one p.toUInt64) n) (one 0) n)
      (Kernel.Ew.val Ew.greater Ew.i64 Ew.va nul
        (Kernel.Ew.val Ew.lesser Ew.i64 Ew.va nul lo (one p.toUInt64) n) (one 0) n) n) (k * 8) 8 =
      UInt64.ofNat (max H L) := by
    rw [val_vv_get _ _ _ _ hk, hc, hc, hL, hH]; exact valStep_max (by omega) (by omega)
  simp only [slices]
  apply UInt64.toNat_inj.1
  rw [sub_get hk (by rw [hM, tn _ (by omega)]; omega) (by rw [hM, hc, hL, tn _ (by omega), tn _ (by omega)]; omega),
    hM, hc, hL, tn _ (by omega), tn _ (by omega), tn _ (by omega)]
  omega

/-- **`expand` of `slices`' counts copies the clamped windows' total**, where the payload count is below
    `2^63`: each count is below it then (`slices_get`, `expand_idx`). -/
theorem len_expand_slices {p n : USize} (hp : p.toNat < 2 ^ 63) (lo hi : ByteArray) :
    len (expandBytes 8 0 (tilLongs n) (slices p n lo hi).2) = ((List.range n.toNat).map fun k =>
      min (max (Column.bitsAt hi (k * 8) 8).toInt64.toInt 0).toNat p.toNat -
        min (max (Column.bitsAt lo (k * 8) 8).toInt64.toInt 0).toNat p.toNat).sum := by
  have h2 := (len_slices p n lo hi).2
  have hk : ∀ k < n.toNat, (Column.bitsAt (slices p n lo hi).2 (k * 8) 8).toNat =
      min (max (Column.bitsAt hi (k * 8) 8).toInt64.toInt 0).toNat p.toNat -
        min (max (Column.bitsAt lo (k * 8) 8).toInt64.toInt 0).toNat p.toNat := fun k hk => by
    rw [(slices_get hp lo hi hk).2]
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_right _ _))
      (Nat.lt_trans hp (by decide)))
  rw [len_eq_ids, expand_idx (by rw [h2]; exact Nat.le_refl _)
    (fun t ht => by rw [hk t (h2 ▸ ht)]; have := Nat.min_le_right (max (Column.bitsAt hi (t * 8) 8).toInt64.toInt 0).toNat p.toNat; omega),
    List.length_flatMap, h2]
  simp only [List.length_replicate]
  congr 1; apply List.map_congr_left; intro k hk'; exact hk k (List.mem_range.1 hk')

/-- **The window `Vals.row` reads at an array row**: the positions `j < m` with `a ≤ j < b` are the run
    from `a` clamped into `[0, m]` to `b` clamped there, read in order; `d` answers no position of it. -/
theorem filterMap_window {β : Type} (d : β) : ∀ {m : Nat} (f : Fin m → β) (a b : Int),
    (List.finRange m).filterMap (fun j => if a ≤ (j.1 : Int) ∧ (j.1 : Int) < b then some (f j) else none) =
      (List.range' (min (max a 0).toNat m) (min (max b 0).toNat m - min (max a 0).toNat m)).map
        fun r => if h : r < m then f ⟨r, h⟩ else d
  | 0, f, a, b => by simp
  | m + 1, f, a, b => by
    rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map]
    have ih := filterMap_window d (fun j : Fin m => f j.castSucc) a b
    simp only [Function.comp_def, Fin.coe_castSucc] at ih ⊢
    rw [ih]
    have hm : ∀ r ∈ List.range' (min (max a 0).toNat m) (min (max b 0).toNat m - min (max a 0).toNat m),
        (if h : r < m then f (Fin.castSucc ⟨r, h⟩) else d) = (if h : r < m + 1 then f ⟨r, h⟩ else d) := by
      intro r hr; rw [List.mem_range'_1] at hr
      rw [dif_pos (by omega), dif_pos (by omega)]; rfl
    rw [List.map_congr_left hm]
    simp only [List.filterMap_cons, List.filterMap_nil, Fin.val_last]
    by_cases hw : a ≤ (m : Int) ∧ (m : Int) < b
    · rw [if_pos hw]; dsimp only
      have e1 : min (max a 0).toNat (m + 1) = min (max a 0).toNat m := by omega
      have e2 : min (max b 0).toNat (m + 1) - min (max a 0).toNat m =
          (min (max b 0).toNat m - min (max a 0).toNat m) + 1 := by omega
      rw [e1, e2, List.range'_concat, List.map_append]
      simp only [List.map_cons, List.map_nil, Nat.one_mul]
      rw [dif_pos (by omega)]
      congr 3; ext; simp only [Fin.val_last]; omega
    · rw [if_neg hw, List.append_nil]
      have e : (min (max b 0).toNat m - min (max a 0).toNat m = 0 ∧
            min (max b 0).toNat (m + 1) - min (max a 0).toNat (m + 1) = 0) ∨
          (min (max a 0).toNat (m + 1) = min (max a 0).toNat m ∧
            min (max b 0).toNat (m + 1) - min (max a 0).toNat m =
              min (max b 0).toNat m - min (max a 0).toNat m) := by omega
      rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; simp
      · rw [e1, e2]

/-! ## `Vals.pick` read back -/

/-- `flatMap` keeps a sublist a sublist (core has `Sublist.filterMap`, no `flatMap` form). -/
theorem sublist_flatMap {α β : Type} (f : α → List β) {l₁ l₂ : List α} (h : l₁.Sublist l₂) :
    (l₁.flatMap f).Sublist (l₂.flatMap f) := by
  induction h with
  | slnil => exact List.Sublist.refl _
  | cons a _ ih => rw [List.flatMap_cons]; exact ih.trans (List.sublist_append_right _ _)
  | cons₂ a _ ih => rw [List.flatMap_cons, List.flatMap_cons]; exact ih.append_left _

/-- **The picked payloads fit**, for `Vals.pick A x` at the rows `ps` (a row at or past `n` a miss): at an
    atom, where some row misses, an interned column's dictionary count below `USize.size` (its miss reads the
    dictionary's empty entry, found at a `USize`); at an array, the payload count and the copies of the picked rows' windows (`filterMap_window`) below `2^63`,
    the longs `slices`/`sums`/`expand` compute them in, and the payload again at those copies; at a sum,
    the row count (the tags' running count) and both sides' counts below `2^63`, the longs `place` computes in, and each side again at the positions its
    rows read (a miss reading the left side at its count `l`, a miss again). -/
def _root_.LeetQ.Rel.Vals.PickFits : (A : Obj) → {n : USize} → Vals A n → List Nat → Prop
  | .atom _, n, x, ps => (∃ k ∈ ps, n.toNat ≤ k) → ∀ d o ids, Arr.enc x = .enum d o ids → o.size - 1 < USize.size
  | .prod a b, _, x, ps => Vals.PickFits a x.1 ps ∧ Vals.PickFits b x.2 ps
  | .arr b, n, ⟨p, lo, hi, f⟩, ps =>
    let w (k : Nat) : List Nat := if h : k < n.toNat then
      List.range' (min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
        (min (max (hi.get ⟨k, h⟩).toInt 0).toNat p.toNat - min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
      else []
    p.toNat < 2 ^ 63 ∧ (ps.flatMap w).length < 2 ^ 63 ∧ (ps.flatMap w).length < USize.size ∧
      Vals.PickFits b f (ps.flatMap w)
  | .sum a b, n, ⟨l, r, tag, idx, x, y⟩, ps =>
    let side (s : Bool) (c : Nat) : List Nat := ps.filterMap fun k =>
      if h : k < n.toNat then
        (if tag.get ⟨k, h⟩ = s then some (min (max (idx.get ⟨k, h⟩).toInt 0).toNat (c - 1)) else none)
      else if s then none else some c
    ps.length < 2 ^ 63 ∧ l.toNat < 2 ^ 63 ∧ r.toNat < 2 ^ 63 ∧ Vals.PickFits a x (side false l.toNat) ∧
      Vals.PickFits b y (side true r.toNat)

/-- **A pick at most doubles an atom side's dictionary** (`gatherColumn_dict`): the entry count, not the
    `o.size - 1` entries `PickFits` bounds, because a miss may append the empty entry to a one-entry offsets array. -/
theorem pickArr_dict {t : QAtomicType} {n : USize} (x : Arr t n) (i : ByteArray) (m : USize) (h : len i = m.toNat) :
    (pickArr t ⟨n, x⟩ i m h).dictSize ≤ 2 * x.dictSize := by
  unfold Arr.dictSize
  have hl : len i < USize.size := h ▸ m.toNat_lt_size
  have cast : ∀ {k : USize} (e : k = m) (y : Arr t k), Arr.enc (e ▸ y : Arr t m) = Arr.enc y := by
    intro k e y; subst e; rfl
  unfold pickArr; rw [cast]
  by_cases hg : t = .general
  · subst hg
    obtain ⟨xs, he, -⟩ := KernelWF.general_cases (pick .general ⟨n, x⟩ i).2.wf
    rw [he]; exact Nat.zero_le _
  · obtain ⟨e, he, hp⟩ := pick_eq_gather hg ⟨n, x⟩ i hl
    have hpe : Arr.enc (pick t ⟨n, x⟩ i).2 = e := congrArg Prod.snd hp
    rw [hpe]
    exact KernelWF.gatherColumn_dict x.wf i (by rw [USize.toNat_ofNat_of_lt' hl]; rfl) he

/-- **Every row read is counted**: the rows themselves bound the measure from below. -/
theorem length_le_reads {A : Obj} {n : USize} (x : Vals A n) (ps : List Nat) : ps.length ≤ Vals.reads A x ps := by
  induction A generalizing n ps with
  | atom t => unfold Vals.reads; omega
  | prod a b iha ihb => unfold Vals.reads; have := iha x.1 ps; omega
  | arr b ih => obtain ⟨p, lo, hi, f⟩ := x; unfold Vals.reads; dsimp only; omega
  | sum a b iha ihb => obtain ⟨l, r, tag, idx, x, y⟩ := x; unfold Vals.reads; dsimp only; omega

/-- **Fewer rows touch less**: the windows and side positions of a sublist are a sublist (`pickFits_sublist`). -/
theorem reads_sublist {A : Obj} {n : USize} (x : Vals A n) {ps ps' : List Nat} (h : ps'.Sublist ps) :
    Vals.reads A x ps' ≤ Vals.reads A x ps := by
  induction A generalizing n ps ps' with
  | atom t => unfold Vals.reads; have := h.length_le; omega
  | prod a b iha ihb => unfold Vals.reads; have := iha x.1 h; have := ihb x.2 h; omega
  | arr b ih =>
    obtain ⟨p, lo, hi, f⟩ := x
    unfold Vals.reads; dsimp only
    exact Nat.add_le_add (Nat.add_le_add_right h.length_le _)
      (ih f ((sublist_flatMap _ h).append (List.Sublist.refl _)))
  | sum a b iha ihb =>
    obtain ⟨l, r, tag, idx, x, y⟩ := x
    unfold Vals.reads; dsimp only
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right
      (Nat.add_le_add_right h.length_le _) _) (iha x ((h.filterMap _).append (List.Sublist.refl _))))
      (ihb y ((h.filterMap _).append (List.Sublist.refl _)))

/-- **The measure below `2^63` and `USize.size` is a fit**: each bound of `Vals.PickFits` is a summand of
    `Vals.reads` at the same rows, a window's or side's row count below its own measure (`length_le_reads`),
    a side's positions a prefix of what its measure reads (`reads_sublist`). -/
theorem pickFits_of_reads {A : Obj} {n : USize} {x : Vals A n} {ps : List Nat}
    (h63 : Vals.reads A x ps < 2 ^ 63) (hU : Vals.reads A x ps < USize.size) : Vals.PickFits A x ps := by
  induction A generalizing n ps with
  | atom t =>
    unfold Vals.reads Arr.dictSize at hU; unfold Vals.PickFits
    intro _ d o ids he; simp only [he] at hU; omega
  | prod a b iha ihb =>
    unfold Vals.reads at h63 hU; unfold Vals.PickFits
    exact ⟨iha (by omega) (by omega), ihb (by omega) (by omega)⟩
  | arr b ih =>
    obtain ⟨p, lo, hi, f⟩ := x
    unfold Vals.reads at h63 hU; unfold Vals.PickFits; dsimp only at h63 hU ⊢
    have sf : ∀ {B : Nat} (s : List Nat), Vals.reads b f (s ++ List.range p.toNat) < B → Vals.reads b f s < B :=
      fun s hs => Nat.lt_of_le_of_lt (reads_sublist f (List.sublist_append_left s _)) hs
    have e63 := sf _ (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h63)
    have eU := sf _ (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hU)
    exact ⟨by omega, Nat.lt_of_le_of_lt (length_le_reads ..) e63, Nat.lt_of_le_of_lt (length_le_reads ..) eU,
      ih e63 eU⟩
  | sum a b iha ihb =>
    obtain ⟨l, r, tag, idx, x, y⟩ := x
    unfold Vals.reads at h63 hU; unfold Vals.PickFits; dsimp only at h63 hU ⊢
    exact ⟨by omega, by omega, by omega,
      iha (Nat.lt_of_le_of_lt (reads_sublist x (List.sublist_append_left _ (List.range l.toNat))) (by omega))
        (Nat.lt_of_le_of_lt (reads_sublist x (List.sublist_append_left _ (List.range l.toNat))) (by omega)),
      ihb (Nat.lt_of_le_of_lt (reads_sublist y (List.sublist_append_left _ (List.range r.toNat))) (by omega))
        (Nat.lt_of_le_of_lt (reads_sublist y (List.sublist_append_left _ (List.range r.toNat))) (by omega))⟩

/-- **Reading two row lists together touches at most what each touches**: the rows add, the dictionaries,
    payloads, side counts and sides' all-row readings are paid once instead of twice. -/
theorem reads_append {A : Obj} {n : USize} (x : Vals A n) (ps qs : List Nat) :
    Vals.reads A x (ps ++ qs) ≤ Vals.reads A x ps + Vals.reads A x qs := by
  induction A generalizing n ps qs with
  | atom t => unfold Vals.reads; simp only [List.length_append]; omega
  | prod a b iha ihb => unfold Vals.reads; have := iha x.1 ps qs; have := ihb x.2 ps qs; omega
  | arr b ih =>
    obtain ⟨p, lo, hi, f⟩ := x
    unfold Vals.reads; dsimp only
    rw [List.flatMap_append, List.length_append, List.append_assoc]
    refine Nat.le_trans (Nat.add_le_add_left (Nat.le_trans (ih f _ _) (Nat.add_le_add_right (reads_sublist f
      (List.sublist_append_left _ (List.range p.toNat))) _)) _) ?_; omega
  | sum a b iha ihb =>
    obtain ⟨l, r, tag, idx, x, y⟩ := x
    unfold Vals.reads; dsimp only
    rw [List.filterMap_append, List.filterMap_append, List.length_append, List.append_assoc, List.append_assoc]
    refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left
      (Nat.le_trans (iha x _ _) (Nat.add_le_add_right (reads_sublist x
        (List.sublist_append_left _ (List.range l.toNat))) _)) _)
      (Nat.le_trans (ihb y _ _) (Nat.add_le_add_right (reads_sublist y
        (List.sublist_append_left _ (List.range r.toNat))) _))) ?_
    omega

/-- **Reordering the rows touches the same**: windows and side positions are permuted (`pickFits_perm`). -/
theorem reads_perm {A : Obj} {n : USize} (x : Vals A n) {ps ps' : List Nat} (h : ps'.Perm ps) :
    Vals.reads A x ps' = Vals.reads A x ps := by
  induction A generalizing n ps ps' with
  | atom t => unfold Vals.reads; rw [h.length_eq]
  | prod a b iha ihb => unfold Vals.reads; rw [iha x.1 h, ihb x.2 h]
  | arr b ih =>
    obtain ⟨p, lo, hi, f⟩ := x
    unfold Vals.reads; dsimp only
    rw [h.length_eq]; exact congrArg _ (ih f ((h.flatMap_right _).append_right _))
  | sum a b iha ihb =>
    obtain ⟨l, r, tag, idx, x, y⟩ := x
    unfold Vals.reads; dsimp only
    rw [h.length_eq]
    congr 1
    · exact congrArg _ (iha x ((h.filterMap _).append_right _))
    · exact ihb y ((h.filterMap _).append_right _)

/-- **Counts below `L`'s make a permutation of a sublist of `L`** (core has no `Subperm`): `L`'s head taken
    where `ps` holds it, skipped where not. -/
theorem perm_sublist_of_count_le : (L ps : List Nat) → (∀ k, ps.count k ≤ L.count k) →
    ∃ l : List Nat, l.Perm ps ∧ l.Sublist L
  | [], ps, h => ⟨[], by
      cases ps with
      | nil => exact List.Perm.refl _
      | cons k _ => have := h k; simp at this, List.Sublist.slnil⟩
  | a :: L, ps, h => by
    by_cases ha : a ∈ ps
    · obtain ⟨l, hp, hs⟩ := perm_sublist_of_count_le L (ps.erase a) fun k => by
        have h1 := h k
        simp only [List.count_erase, List.count_cons, beq_iff_eq] at h1 ⊢
        split at h1 <;> split <;> omega
      exact ⟨a :: l, (hp.cons a).trans (List.perm_cons_erase ha).symm, hs.cons₂ a⟩
    · obtain ⟨l, hp, hs⟩ := perm_sublist_of_count_le L ps fun k => by
        have h1 := h k
        by_cases hk : a = k
        · subst hk; rw [List.count_eq_zero_of_not_mem ha]; exact Nat.zero_le _
        · simp only [List.count_cons, beq_iff_eq, hk, if_false, Nat.add_zero] at h1; exact h1
      exact ⟨l, hp, hs.cons a⟩

/-- **Rows repeated at most `c` times, all below `N`, touch at most `c` readings of all `N` rows**: they are a
    permutation of a sublist of `c` copies of `List.range N` (`reads_perm`, `reads_sublist`, `reads_append`). -/
theorem reads_count_le {A : Obj} {n : USize} (x : Vals A n) {ps : List Nat} {c N : Nat} (hc : 0 < c)
    (h : ∀ k ∈ ps, k < N ∧ ps.count k ≤ c) :
    Vals.reads A x ps ≤ c * Vals.reads A x (List.range N) := by
  have hcnt : ∀ k, ps.count k ≤ (List.replicate c (List.range N)).flatten.count k := fun k => by
    have e : ∀ c, (List.replicate c (List.range N)).flatten.count k = c * (if k < N then 1 else 0) := fun c => by
      induction c with
      | zero => simp
      | succ c ih => rw [List.replicate_succ, List.flatten_cons, List.count_append, ih, List.count_range,
          Nat.succ_mul]; omega
    rw [e]
    by_cases hk : k ∈ ps
    · rw [if_pos (h k hk).1, Nat.mul_one]; exact (h k hk).2
    · rw [List.count_eq_zero_of_not_mem hk]; exact Nat.zero_le _
  obtain ⟨l, hp, hs⟩ := perm_sublist_of_count_le _ ps hcnt
  rw [← reads_perm x hp]
  refine Nat.le_trans (reads_sublist x hs) ?_
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  clear hc h hcnt hp hs
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.replicate_succ, List.flatten_cons]
    refine Nat.le_trans (reads_append x _ _) ?_
    rw [Nat.succ_mul (c + 1)]; omega

/-- **An atom side fits outright** where every picked row is below the count: no row misses. -/
theorem pickFits_atom {t : QAtomicType} {n : USize} (x : Vals (.atom t) n) {ps : List Nat}
    (h : ∀ k ∈ ps, k < n.toNat) : Vals.PickFits (.atom t) x ps := by
  unfold Vals.PickFits
  rintro ⟨k, hk, hle⟩
  exact absurd (h k hk) (Nat.not_lt.2 hle)

/-- **A product side fits** where both components do — with `pickFits_atom`, a side of atoms and products
    fits outright at rows below its count. -/
theorem pickFits_prod {a b : Obj} {n : USize} (x : Vals (.prod a b) n) {ps : List Nat}
    (h1 : Vals.PickFits a x.1 ps) (h2 : Vals.PickFits b x.2 ps) : Vals.PickFits (.prod a b) x ps := by
  unfold Vals.PickFits
  exact ⟨h1, h2⟩

/-- **A fit at rows `ps` is a fit at every sublist of them**: each clause bounds or recurses at the windows or
    side positions of the picked rows, which shrink to a sublist (`flatMap`, `filterMap`), and a miss among
    fewer rows is a miss among more. With `ids` of a kernel's picks a sublist of `List.range n`, a fit of the
    input at all its rows is a fit at the picks. -/
theorem pickFits_sublist {A : Obj} {n : USize} {x : Vals A n} {ps ps' : List Nat} (h : ps'.Sublist ps) :
    Vals.PickFits A x ps → Vals.PickFits A x ps' := by
  induction A generalizing n ps ps' with
  | atom t =>
    unfold Vals.PickFits
    exact fun hf ⟨k, hk, hle⟩ => hf ⟨k, h.subset hk, hle⟩
  | prod a b iha ihb =>
    unfold Vals.PickFits
    exact fun ⟨h1, h2⟩ => ⟨iha h h1, ihb h h2⟩
  | arr b ih =>
    obtain ⟨p, lo, hi, f⟩ := x
    unfold Vals.PickFits
    dsimp only
    intro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, Nat.lt_of_le_of_lt ?_ h2, Nat.lt_of_le_of_lt ?_ h3, ih (sublist_flatMap _ h) h4⟩ <;>
      exact (sublist_flatMap _ h).length_le
  | sum a b iha ihb =>
    obtain ⟨l, r, tag, idx, x, y⟩ := x
    unfold Vals.PickFits
    dsimp only
    intro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨Nat.lt_of_le_of_lt h.length_le h1, h2, h3, iha (h.filterMap _) h4, ihb (h.filterMap _) h5⟩

/-- **A fit is a fit at every reordering of the rows**: each clause bounds a length or a membership, which a
    permutation keeps, and recurses at the windows or side positions, which it permutes. -/
theorem pickFits_perm {A : Obj} {n : USize} {x : Vals A n} {ps ps' : List Nat} (h : ps'.Perm ps) :
    Vals.PickFits A x ps → Vals.PickFits A x ps' := by
  induction A generalizing n ps ps' with
  | atom t =>
    unfold Vals.PickFits
    exact fun hf ⟨k, hk, hle⟩ => hf ⟨k, h.subset hk, hle⟩
  | prod a b iha ihb =>
    unfold Vals.PickFits
    exact fun ⟨h1, h2⟩ => ⟨iha h h1, ihb h h2⟩
  | arr b ih =>
    obtain ⟨p, lo, hi, f⟩ := x
    unfold Vals.PickFits
    dsimp only
    intro ⟨h1, h2, h3, h4⟩
    have hw := h.flatMap_right fun k => if h : k < n.toNat then
      List.range' (min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
        (min (max (hi.get ⟨k, h⟩).toInt 0).toNat p.toNat - min (max (lo.get ⟨k, h⟩).toInt 0).toNat p.toNat)
      else []
    exact ⟨h1, hw.length_eq ▸ h2, hw.length_eq ▸ h3, ih hw h4⟩
  | sum a b iha ihb =>
    obtain ⟨l, r, tag, idx, x, y⟩ := x
    unfold Vals.PickFits
    dsimp only
    intro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h.length_eq ▸ h1, h2, h3, iha (h.filterMap _) h4, ihb (h.filterMap _) h5⟩

/-- **An atom side fits at each row repeated `m` times** (`· / m`, the rows `⊤` keys): all below the count. -/
theorem pickFits_div {t : QAtomicType} {n : USize} (x : Vals (.atom t) n) (m : Nat) :
    Vals.PickFits (.atom t) x ((List.range (n.toNat * m)).map (· / m)) :=
  pickFits_atom x fun r hr => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact List.mem_range.1 hq)

/-- **The empty side fits at no rows**: every count it holds is `0`. -/
theorem pickFits_empty : (A : Obj) → Vals.PickFits A (Vals.empty A) []
  | .atom _ => by unfold Vals.PickFits; rintro ⟨k, hk, -⟩; cases hk
  | .prod a b => by unfold Vals.PickFits; exact ⟨pickFits_empty a, pickFits_empty b⟩
  | .arr b => by
    simp only [Vals.empty, Vals.PickFits, List.flatMap_nil, List.length_nil]
    exact ⟨by simp, by decide, USize.size_pos, pickFits_empty b⟩
  | .sum a b => by
    simp only [Vals.empty, Vals.PickFits, List.filterMap_nil, List.length_nil]
    exact ⟨by decide, by simp, by simp, pickFits_empty a, pickFits_empty b⟩

/-- **`Vals.fitsN` decides a fit at any `N` rows**: an array's windows are clamped into its payload, so `N` rows
    copy at most `N·p` positions; a sum's side lists are no longer than its rows. -/
theorem pickFits_of_fitsN : (A : Obj) → {n : USize} → (x : Vals A n) → (N : Nat) → Vals.fitsN A x N = true →
    ∀ ps : List Nat, ps.length ≤ N → Vals.PickFits A x ps
  | .atom _, _, x, _, hb, _, _ => by
    unfold Vals.PickFits; intro _ d o ids he
    unfold Vals.fitsN at hb; rw [he] at hb; exact of_decide_eq_true hb
  | .prod a b, _, x, N, hb, ps, hl => by
    simp only [Vals.fitsN, Bool.and_eq_true] at hb
    exact pickFits_prod x (pickFits_of_fitsN a x.1 N hb.1 ps hl) (pickFits_of_fitsN b x.2 N hb.2 ps hl)
  | .arr b, _, ⟨p, lo, hi, f⟩, N, hb, ps, hl => by
    simp only [Vals.fitsN, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨hp, h63⟩, hU⟩, hf⟩ := hb
    have hfl : ∀ (g : Nat → List Nat) (c : Nat), (∀ k, (g k).length ≤ c) → ∀ qs : List Nat,
        (qs.flatMap g).length ≤ qs.length * c := fun g c hg qs => by
      induction qs with
      | nil => simp
      | cons k qs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]; have := hg k; omega
    unfold Vals.PickFits; dsimp only
    refine ⟨hp, Nat.lt_of_le_of_lt ?h h63, Nat.lt_of_le_of_lt ?h hU, pickFits_of_fitsN b f _ hf _ ?h⟩
    case h =>
      refine Nat.le_trans (hfl _ p.toNat (fun k => ?_) ps) (Nat.mul_le_mul_right _ hl)
      split <;> simp only [List.length_range', List.length_nil] <;> omega
  | .sum a b, _, ⟨l, r, tag, idx, x, y⟩, N, hb, ps, hl => by
    simp only [Vals.fitsN, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨hN, hl63⟩, hr63⟩, ha⟩, hb⟩ := hb
    unfold Vals.PickFits; dsimp only
    exact ⟨by omega, hl63, hr63, pickFits_of_fitsN a x N ha _ (Nat.le_trans (List.length_filterMap_le _ _) hl),
      pickFits_of_fitsN b y N hb _ (Nat.le_trans (List.length_filterMap_le _ _) hl)⟩

/-- **Each piece `g a` a sublist of `f (p a)` makes the pieces' concatenation a sublist of `f`'s at the
    `p`-images**: one element (or a sub-window) taken from each picked row's window, in row order. -/
theorem flatMap_sublist_map_flatMap {α β γ : Type} (p : α → γ) (g : α → List β) (f : γ → List β)
    {l : List α} (h : ∀ a ∈ l, (g a).Sublist (f (p a))) : (l.flatMap g).Sublist ((l.map p).flatMap f) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons]
    exact (h a (by simp)).append (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **An array side with the payload of `x` and windows inside `x`'s fits where `x` does**: the windows of
    `lo'`/`hi'` at `qs`, concatenated, a sublist of `x`'s at `ps` — the bounds and the payload's fit shrink. -/
theorem pickFits_windows {B : Obj} {n m : USize} (x : Vals (.arr B) n) (lo' hi' : Arr .long m)
    {ps qs : List Nat}
    (h : (qs.flatMap fun k => if h : k < m.toNat then
        List.range' (min (max (lo'.get ⟨k, h⟩).toInt 0).toNat x.1.toNat)
          (min (max (hi'.get ⟨k, h⟩).toInt 0).toNat x.1.toNat - min (max (lo'.get ⟨k, h⟩).toInt 0).toNat x.1.toNat)
        else []).Sublist
      (ps.flatMap fun k => if h : k < n.toNat then
        List.range' (min (max (x.2.1.get ⟨k, h⟩).toInt 0).toNat x.1.toNat)
          (min (max (x.2.2.1.get ⟨k, h⟩).toInt 0).toNat x.1.toNat -
            min (max (x.2.1.get ⟨k, h⟩).toInt 0).toNat x.1.toNat)
        else []))
    (hf : Vals.PickFits (.arr B) x ps) : Vals.PickFits (.arr B) (⟨x.1, lo', hi', x.2.2.2⟩ : Vals (.arr B) m) qs := by
  obtain ⟨p, lo, hi, f⟩ := x
  unfold Vals.PickFits at hf ⊢
  dsimp only at hf h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hf
  exact ⟨h1, Nat.lt_of_le_of_lt h.length_le h2, Nat.lt_of_le_of_lt h.length_le h3, pickFits_sublist h h4⟩

/-- **`Vals.pick` read back at an atom**: `pickArr_get`. -/
theorem pick_row_atom {t : QAtomicType} {n : USize} (x : Vals (.atom t) n)
    (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
    (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat) :
    (Vals.pick (.atom t) x i m h).row q = x.row ⟨_, hin⟩ :=
  pickArr_get ⟨_, x⟩ i m h q hin

/-- **`Vals.pick` read back at a product**, from its two components'. -/
theorem pick_row_prod {a b : Obj} {n : USize} (x : Vals (.prod a b) n)
    (h1 : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat), (Vals.pick a x.1 i m h).row q = x.1.row ⟨_, hin⟩)
    (h2 : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat), (Vals.pick b x.2 i m h).row q = x.2.row ⟨_, hin⟩)
    (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
    (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat) :
    (Vals.pick (.prod a b) x i m h).row q = x.row ⟨_, hin⟩ :=
  Prod.ext (h1 i m h q hin) (h2 i m h q hin)

end LeetQ.Rel.Alg
