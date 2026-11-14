/-
  Well-formedness of the payloads qlean's kernels answer, read off their Lean bodies, in the form
  `Arr.mk` takes (`Enc.WF t n e`), and the `isSome` facts that make `codes` total. Gathering kernels (`gatherColumn`, `bytesOf`, `longBytes`, `gens`) are in
  `KernelWF/Gather`.
-/
import QLean.Kernel.Structural
import QLean.Kernel.Sort
import QLean.Kernel.Reduce
import QLean.Kernel.Elementwise
import QLean.Verify.Group
import QLean.Verify.Raw
import QLean.Verify.Ids
import QLean.Verify.Alp
import QLean.Verify.EwEnc
import QLean.Verify.Gather
import LeetQ.Rel.Core

-- the lane widths a `Code` may have: one home for the disjunction every `Code.w` hypothesis states (here, the
-- earliest module stating it: an id pack's lane is `w = 0 ∨ laneOK(w)`)
notation "laneOK(" w ")" => (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel LeetQ.Rel

/-! ## Sizes of the folds the kernels are written as -/

/-- A fold that appends `w` bytes a step answers `w` bytes per element. -/
theorem foldl_size {α σ : Type} (sz : σ → Nat) (g : σ → α → σ) (w : Nat)
    (hg : ∀ acc a, sz (g acc a) = sz acc + w) :
    ∀ (l : List α) (b : σ), sz (l.foldl g b) = sz b + l.length * w
  | [], b => by simp
  | a :: l, b => by
    simp only [List.foldl, List.length_cons]; rw [foldl_size sz g w hg l, hg]; simp [Nat.succ_mul]; omega

/-- A dense payload of `n` elements of a type with a width, other than boolean, is well formed. -/
theorem wf_bytes {t : QAtomicType} {w : Nat} {n : USize} {b : ByteArray} (hb : t ≠ .boolean)
    (hw : t.width = some w) (hs : b.size = n.toNat * w) : Enc.WF t n (.bytes b) := by
  cases t <;> simp_all [Enc.WF, QAtomicType.width]

/-- A `Nat` below `USize.size` comes back from its `USize` unchanged. -/
private theorem toUSize_toNat {k : Nat} (h : k < USize.size) : k.toUSize.toNat = k := by
  simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt h

/-- A `USize`'s `Nat` fits a `USize`. -/
private theorem fits (k : USize) : k.toNat < USize.size := k.toBitVec.isLt

private theorem toNat_toUSize (k : USize) : k.toNat.toUSize = k := USize.toNat_inj.1 (toUSize_toNat (fits k))

/-- Under its bound, `needSize` is its continuation at the count. -/
private theorem needSize_fits {α : Type} {c : Nat} {what : String} {model : Unit → α} {k : USize → α}
    (h : c < USize.size) : needSize c what model k = k c.toUSize := by
  simp [needSize, need, h]

/-- Past its bound, `needSize` is its model. -/
private theorem needSize_not {α : Type} {c : Nat} {what : String} {model : Unit → α} {k : USize → α}
    (h : ¬ c < USize.size) : needSize c what model k = model () := by
  simp [needSize, need, h, stop]

/-- A `needSize` that answers `some` under a `none` model is its continuation at a count that fits. -/
theorem needSize_some {α : Type} {c : Nat} {what : String} {k : USize → Option α} {v : α}
    (h : needSize c what (fun _ => none) k = some v) : ∃ hc : c < USize.size, k c.toUSize = some v := by
  by_cases hc : c < USize.size
  · exact ⟨hc, by rw [needSize_fits hc] at h; exact h⟩
  · rw [needSize_not hc] at h; cases h

/-- A `need` that answers `some` under a `none` model holds, and is its continuation. -/
private theorem need_some {α : Type} {p : Prop} [Decidable p] {msg : Unit → String} {k : p → Option α} {v : α}
    (h : need p msg (fun _ => none) k = some v) : ∃ hp : p, k hp = some v := by
  by_cases hp : p
  · exact ⟨hp, by simpa [need, hp] using h⟩
  · simp [need, hp, stop] at h

/-- `countBytes`' count `k` reads back at byte `8k`. -/
theorem countBytes_get (xs : Array USize) (k : Nat) (h : k < xs.size) :
    Column.bitsAt (countBytes xs) (8 * k) 8 = xs[k].toUInt64 := by
  obtain ⟨-, -, hb⟩ := Verify.foldl_pushBits USize.toUInt64 8 (by decide) xs.toList ByteArray.empty
  have := hb k (by simpa using h)
  rw [countBytes, ← Array.foldl_toList]
  simp only [ByteArray.size_empty, Nat.zero_add] at this
  rw [this]
  apply UInt64.toNat_inj.1
  have hlt := Nat.lt_of_lt_of_le (fits xs[k]) USize.size_le
  first
    | omega
    | (simp only [UInt64.toNat_ofNat, USize.toNat_toUInt64, Array.getElem_toList, Nat.reducePow, Nat.reduceMul]
       omega)
    | (simp <;> omega)

/-! ## `orderKind`: which types have a sort layout -/

/-- `orderKind` has no sort layout exactly at symbol, guid and the general list. -/
theorem orderKind_eq_none {t : QAtomicType} :
    orderKind t = none ↔ t = .symbol ∨ t = .guid ∨ t = .general := by
  cases t <;> simp [orderKind]

/-- `groupIdsColumn` codes every well-formed payload except a general list's, where the interned
    dictionary's entries fit a `USize`. -/
theorem groupIdsColumn_isSome {t : QAtomicType} {n : USize} {e : Enc} (hg : t ≠ .general)
    (h : Enc.WF t n e) (hd : ∀ d o ids, Column.intern e = .enum d o ids → o.size - 1 < USize.size) :
    (groupIdsColumn t n e).isSome := by
  cases t
  case symbol =>
    cases e
    case syms blob offs =>
      have hf := hd (Order.internSyms blob offs).1 (Order.internSyms blob offs).2.1 (Order.internSyms blob offs).2.2 rfl
      simp [groupIdsColumn, needSize_fits hf]
    case enum d o ids => simp [groupIdsColumn, needSize_fits (hd d o ids rfl)]
    all_goals simp_all [Enc.WF, QAtomicType.width]
  all_goals cases e <;> simp_all [Enc.WF, groupIdsColumn, orderKind, Enc.bytesOf, QAtomicType.width]

/-- The type whose grouping key is a cell's bits: a float type's integral type of its width, every other
    type itself. q's float key (`Order.rank32`/`rank64`) folds the NaNs and the two zeros together, where a
    float cell (`Carrier`) is its bits; the integral key of the same width is the bits. -/
def bitsType : QAtomicType → QAtomicType
  | .real => .int
  | .float | .datetime => .long
  | t => t

/-- `groupIdsColumn` at `bitsType t` codes every well-formed payload of `t` but a general list's: a float
    payload, dense, Frame-of-Reference or ALP, is read at its width (`Enc.bytesOf`). -/
theorem groupIdsColumn_bitsType_isSome {t : QAtomicType} {n : USize} {e : Enc} (hg : t ≠ .general)
    (h : Enc.WF t n e) (hd : ∀ d o ids, Column.intern e = .enum d o ids → o.size - 1 < USize.size) :
    (groupIdsColumn (bitsType t) n e).isSome := by
  cases t
  case real | float | datetime =>
    cases e <;> simp_all [Enc.WF, groupIdsColumn, orderKind, Enc.bytesOf, QAtomicType.width, bitsType]
  all_goals exact groupIdsColumn_isSome hg h hd

/-! ## Results of the producing kernels -/

/-- `packOf n f` holds `n` bits. -/
theorem packOf_size (n : Nat) (f : Nat → Bool) : (packOf n f).size = (n + 7) / 8 := by
  simp only [packOf]; rw [foldl_size ByteArray.size _ 1 (fun _ _ => by simp only [ByteArray.size, ByteArray.push, Array.size_push])]; simp

/-- A summing fold is the sum. -/
private theorem foldl_add {β : Type} (f : β → Nat) : ∀ (a : Nat) (l : List β),
    l.foldl (fun s p => s + f p) a = a + (l.map f).sum
  | a, [] => by simp
  | a, p :: l => by simp [foldl_add f _ l]; omega

/-- The summed count of parts, as the kernels fold it. -/
private theorem foldl_toNat {β : Type} (qs : Array (USize × β)) :
    qs.foldl (fun s p => s + p.1.toNat) 0 = ((qs.map (·.1)).toList.map USize.toNat).sum := by
  rw [← Array.foldl_toList, foldl_add]; simp [Function.comp_def]

/-- A fold that grows by `f a` a step grows by the sum. -/
private theorem foldl_sum {α σ : Type} (sz : σ → Nat) (g : σ → α → σ) (f : α → Nat)
    (hg : ∀ s a, sz (g s a) = sz s + f a) : ∀ (l : List α) (s : σ), sz (l.foldl g s) = sz s + (l.map f).sum
  | [], s => by simp
  | a :: l, s => by simp only [List.foldl, List.map_cons, List.sum_cons]; rw [foldl_sum sz g f hg l, hg]; omega

/-- A kernel that reads part `k`'s count off `countBytes` and lays down that many elements of each part
    answers their sum. -/
private theorem flatMap_counts {γ : Type} (xs : Array USize) (m : Nat) (hm : xs.size ≤ m) (g : Nat → Nat → γ) :
    ((Array.range (min ((countBytes xs).size / 8) m)).flatMap fun k =>
      (Array.range (Column.bitsAt (countBytes xs) (8 * k) 8).toNat).map (g k)).size =
      (xs.toList.map USize.toNat).sum := by
  rw [countBytes_size, Nat.mul_div_cancel_left _ (by decide), Nat.min_eq_left hm, Array.size_flatMap]
  simp only [Array.size_map, Array.size_range]
  have he : (Array.range xs.size).map (fun k => (Column.bitsAt (countBytes xs) (8 * k) 8).toNat) =
      xs.map USize.toNat :=
    Array.ext (by simp) fun i h1 _ => by
      simp only [Array.size_map, Array.size_range] at h1
      simp [countBytes_get xs i h1]
  rw [he]
  first | (rw [← Array.sum_toList, Array.toList_map]) | (rcases xs with ⟨l⟩; simp) | rfl

/-- An `if` that answers `some` with `none` on its true branch took its false branch. -/
theorem ite_none_some {α : Type} {c : Prop} [Decidable c] {x : Option α} {v : α}
    (h : (if c then none else x) = some v) : x = some v := by
  by_cases hc : c <;> simp_all

/-- An `if` that answers `some` answers it on one of its branches. -/
private theorem ite_some {α : Type} {c : Prop} [Decidable c] {x y : Option α} {v : α}
    (h : (if c then x else y) = some v) : x = some v ∨ y = some v := by
  by_cases hc : c <;> simp_all

/-- A property every step keeps holds of the fold. -/
theorem foldl_inv {α σ : Type} (P : σ → Prop) (g : σ → α → σ) (hg : ∀ s a, P s → P (g s a)) :
    ∀ (l : List α) (s : σ), P s → P (l.foldl g s)
  | [], _, h => h
  | a :: l, s, h => foldl_inv P g hg l (g s a) (hg s a h)

/-- `concatBits` of parts `ps` holds their summed count, as `razeColumn` counts it. -/
theorem concatBits_wf (ps : Array (USize × ByteArray)) {c : USize}
    (hc : c.toNat = ps.foldl (fun s p => s + p.1.toNat) 0) :
    Enc.WF .boolean c (.bits (concatBits (countBytes (ps.map (·.1))) (ps.map (·.2)))) := by
  simp only [Enc.WF, concatBits, packOf_size, hc, foldl_toNat]
  rw [flatMap_counts _ _ (by simp)]

/-- `til n` as `tilLongs`: `n` longs. -/
theorem tilLongs_wf (n : USize) : Enc.WF .long n (.bytes (tilLongs n)) :=
  wf_bytes (w := 8) (by decide) rfl (by
    simp only [tilLongs]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp)

/-- `Ew.val` answers `n` elements at its class's width. -/
theorem Ew.val_size (op cls shape : UInt8) (nul : Int64) (a b : ByteArray) (n : USize) :
    (Kernel.Ew.val op cls shape nul a b n).size = n.toNat * Kernel.Ew.width cls := by
  simp only [Kernel.Ew.val]; rw [foldl_size ByteArray.size _ _ (fun _ _ => Column.pushBits_size ..)]; simp

/-- `rankSlices` answers one long per slice of `o` when `o` is non-decreasing offsets from at least `0`,
    its last within `v`'s ids at width `w ≤ 64`: the negation of the kernel's guard, term by term. -/
theorem rankSlices_size (w : USize) (v o : ByteArray) (hw : w.toNat ≤ 64) (ho : 8 ≤ o.size)
    (h0 : 0 ≤ (Column.bitsAt o 0 8).toInt64.toInt)
    (hcap : (Column.bitsAt o (8 * (o.size / 8 - 1)) 8).toInt64.toInt ≤
      (Column.idsCap v w.toNat (Column.bitsAt o (8 * (o.size / 8 - 1)) 8).toInt64.toInt.toNat : Int))
    (hasc : ∀ j, j < o.size / 8 - 1 →
      (Column.bitsAt o (8 * j) 8).toInt64.toInt ≤ (Column.bitsAt o (8 * (j + 1)) 8).toInt64.toInt) :
    (Order.rankSlices w v o).size = 8 * (o.size / 8 - 1) := by
  simp only [Order.rankSlices]
  rw [if_neg]
  · rw [← Array.foldl_toList]
    refine Eq.trans (foldl_size (fun p : ByteArray × _ => p.1.size) _ 8 ?_ _ _) ?_
    · intro acc j; rcases acc with ⟨ids, seen⟩; simp only; split <;> simp [Column.pushBits_size]
    · simp; omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, not_or,
      not_exists, not_and, Nat.mul_zero]
    exact ⟨⟨⟨⟨Nat.not_lt.2 hw, Nat.not_lt.2 ho⟩, Int.not_lt.2 h0⟩, Int.not_lt.2 hcap⟩, fun j hj => Int.not_lt.2 (hasc j hj)⟩

/-! ## `razeColumn` -/

/-- An `Option` pass that answers `some (g x)` at every element answers `some` of the mapped array. -/
theorem mapM_some {α β : Type} {f : α → Option β} (g : α → β) :
    ∀ {cs : Array α}, (∀ x ∈ cs, f x = some (g x)) → cs.mapM f = some (cs.map g) := by
  intro cs h
  rcases cs with ⟨l⟩
  rw [Array.mapM_eq_mapM_toList]
  simp only [Array.mem_def] at h
  suffices hl : l.mapM f = some (l.map g) by simp [hl]
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- The dense layout of a well-formed payload of a type with a width, other than boolean, holds its `n`
    elements, `w` bytes each; an encoded `n` fits a `USize`, the count every decoding kernel reads. -/
theorem bytesOf_size {t : QAtomicType} {n : USize} {w : Nat} {e : Enc} (hb : t ≠ .boolean)
    (hw : t.width = some w) (h : Enc.WF t n e) :
    ∃ b, Enc.bytesOf t n e = some b ∧ b.size = n.toNat * w := by
  have hwu : w.toUSize.toNat = w := by
    simp only [Nat.toUSize]; apply Nat.mod_eq_of_lt
    have : w ≤ 16 := by cases t <;> simp [QAtomicType.width] at hw <;> omega
    rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega
  have hpush (k : Nat) (l : List UInt64) :
      (l.foldl (fun acc v => Column.pushBits acc v k) ByteArray.empty).size = l.length * k := by
    rw [foldl_size ByteArray.size _ k (fun _ _ => Column.pushBits_size ..)]; simp
  cases e
  case foR m p =>
    refine ⟨_, by simp [Enc.bytesOf, hw]; rfl, ?_⟩
    simp only [Coc.decode, hpush, Coc.elems, List.length_map, List.length_range, hwu]
  case alp m p a =>
    refine ⟨_, by simp [Enc.bytesOf, hw]; rfl, ?_⟩
    have h4 : (w.toUSize == 4) = true → w = 4 := fun e => by rw [← hwu, beq_iff_eq.1 e]; rcases System.Platform.numBits_eq with h' | h' <;> simp [USize.toNat_ofNat, h']
    have h8 : (w.toUSize == 8) = true → w = 8 := fun e => by rw [← hwu, beq_iff_eq.1 e]; rcases System.Platform.numBits_eq with h' | h' <;> simp [USize.toNat_ofNat, h']
    simp only [Coc.alpDecode, Coc.alpDecode32, Coc.alpDecode64]
    split
    · rw [hpush, h4 ‹_›]; simp [Coc.alpElems]
    · split
      · rw [hpush, h8 ‹_›]; simp [Coc.alpElems]
      · rw [hpush]; simp [Coc.alpElems, hwu]
  all_goals cases t <;> simp_all [Enc.WF, Enc.bytesOf, QAtomicType.width]

/-- `razeColumn`'s dense pass over well-formed parts, each read at its count as the `USize` it is: every
    part answers its dense layout, `n · w` bytes. -/
private theorem dense_parts {t : QAtomicType} {cs : Array (USize × Enc)} {w : Nat}
    (h : ∀ c ∈ cs, Enc.WF t c.1 c.2) (hw : t.width = some w) (hb : t ≠ .boolean) {ps : Array ByteArray}
    (hps : cs.mapM (fun c => Enc.bytesOf t c.1 c.2) = some ps) :
    ps.size = cs.size ∧ ∀ i (hi : i < cs.size) (hp : i < ps.size), ps[i].size = cs[i].1.toNat * w := by
  have hm := mapM_some (f := fun c : USize × Enc => Enc.bytesOf t c.1 c.2)
    (fun c => (Enc.bytesOf t c.1 c.2).getD .empty) (cs := cs) fun c hc => by
      obtain ⟨b, hb', -⟩ := bytesOf_size hb hw (h c hc); simp [hb']
  rw [hm] at hps
  cases hps
  refine ⟨by simp, fun i hi _ => ?_⟩
  obtain ⟨b, hb', hs⟩ := bytesOf_size hb hw (h _ (Array.getElem_mem hi))
  simp [hb', hs]

/-! ## Valid UTF-8: every symbol entry a kernel writes is one it copied, or the empty symbol -/

/-- Validity is a property of the bytes. -/
theorem utf8_congr {a c : ByteArray} (h : a.data.toList = c.data.toList) (hv : c.IsValidUTF8) : a.IsValidUTF8 := by
  rw [show a = c from ByteArray.ext (Array.toList_inj.1 h)]; exact hv

/-- A blob grown, its new size pushed as the last start, keeps the `syms` layout. -/
theorem symsWF_push {b b' : ByteArray} {o : Array Nat} (h : SymsWF b o) (hb : b.size ≤ b'.size) :
    SymsWF b' (o.push b'.size) := by
  have hs : (o.push b'.size).size = o.size + 1 := Array.size_push ..
  have hg : ∀ k, (o.push b'.size)[k]! = if k < o.size then o[k]! else if k = o.size then b'.size else 0 := by
    intro k
    by_cases h1 : k < o.size
    · rw [if_pos h1, getElem!_pos _ k (by omega), Array.getElem_push_lt h1, getElem!_pos o k h1]
    · rw [if_neg h1]
      by_cases h2 : k = o.size
      · subst h2; rw [if_pos rfl, getElem!_pos _ o.size (by omega), Array.getElem_push_eq]
      · rw [if_neg h2, getElem!_neg _ k (by omega)]; rfl
  have hp := h.pos
  refine ⟨by omega, by rw [hg, if_pos hp, h.first], by rw [hg, if_neg (by omega), if_pos (by omega)],
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [hg]; split
    · exact Nat.le_trans (h.le k ‹_›) hb
    · split <;> omega
  · rw [hg, hg]
    by_cases h1 : k + 1 < o.size
    · rw [if_pos (by omega), if_pos h1]; exact h.mono k (by omega)
    · have e : o[k]! = b.size := by rw [show k = o.size - 1 by omega]; exact h.last
      rw [if_pos (by omega), if_neg h1, if_pos (by omega), e]; exact hb

/-- Entry `t` of a well-formed blob is valid where its stored bytes, the NUL dropped, are some valid bytes. -/
theorem utf8_of_inv {b : ByteArray} {o : Array Nat} (hw : SymsWF b o) {t : Nat} (ht : t < o.size - 1)
    (h : ∃ k : ByteArray, k.IsValidUTF8 ∧ (Verify.symBytes b o t).dropLast = k.data.toList) :
    (Column.symKey b o t).IsValidUTF8 := by
  obtain ⟨k, hk, he⟩ := h
  exact utf8_congr ((Verify.symAt_eq_dropLast b o t (hw.le (t + 1) (by omega))).trans he) hk

theorem inv_of_utf8 {b : ByteArray} {o : Array Nat} (hw : SymsWF b o) {t : Nat} (ht : t < o.size - 1)
    (hv : (Column.symKey b o t).IsValidUTF8) :
    ∃ k : ByteArray, k.IsValidUTF8 ∧ (Verify.symBytes b o t).dropLast = k.data.toList :=
  ⟨_, hv, (Verify.symAt_eq_dropLast b o t (hw.le (t + 1) (by omega))).symm⟩

/-- One symbol appended — the bytes `s` after the blob, its end pushed as the last start — keeps the layout, and
    every entry valid where `s` without its last byte, the NUL, is. -/
theorem utf8_push {b b' : ByteArray} {o : Array Nat} {s : List UInt8} (hw : SymsWF b o)
    (hu : ∀ t < o.size - 1, ∃ k : ByteArray, k.IsValidUTF8 ∧ (Verify.symBytes b o t).dropLast = k.data.toList)
    (hob : b'.data.toList = b.data.toList ++ s) (hs : ∃ k : ByteArray, k.IsValidUTF8 ∧ s.dropLast = k.data.toList) :
    SymsWF b' (o.push b'.size) ∧ ∀ t < (o.push b'.size).size - 1,
      ∃ k : ByteArray, k.IsValidUTF8 ∧ (Verify.symBytes b' (o.push b'.size) t).dropLast = k.data.toList := by
  have hl : b.size ≤ b'.size := by
    have := congrArg List.length hob
    simp only [Array.length_toList, List.length_append] at this
    show b.data.size ≤ b'.data.size; omega
  have hp := hw.pos
  obtain ⟨-, -, -, g4, g5⟩ := Verify.symBytes_push b b' o (o.size - 1) s (by omega) hw.last
    (fun t _ => hw.le t (by omega)) hob
  refine ⟨symsWF_push hw hl, fun t ht => ?_⟩
  rw [Array.size_push] at ht
  rcases Nat.lt_or_ge t (o.size - 1) with h | h
  · rw [g5 t h]; exact hu t h
  · rw [show t = o.size - 1 by omega, g4]; exact hs

/-- A `Nat.fold` whose every step keeps `P` keeps it. -/
theorem fold_inv {α : Type} {N : Nat} (f : (i : Nat) → i < N → α → α) (P : α → Prop)
    (hf : ∀ i h p, P p → P (f i h p)) (init : α) (h0 : P init) {q : α} (hq : Nat.fold N f init = q) : P q := by
  subst hq
  induction N with
  | zero => simpa using h0
  | succ N ih => rw [Nat.fold_succ]; exact hf _ _ _ (ih (fun i h => f i (by omega)) (fun i h p => hf i _ p))

/-- `distinctSyms` keeps only entries of its source, so they are valid where the source's are. -/
theorem utf8_distinctSyms (b : ByteArray) (o : Array Nat) (hu : ∀ i < o.size - 1, (Column.symKey b o i).IsValidUTF8) :
    ∀ j < (Order.distinctSyms b o).2.size - 1,
      (Column.symKey (Order.distinctSyms b o).1 (Order.distinctSyms b o).2 j).IsValidUTF8 := by
  have hD := Verify.distinctSyms_eraseDups b o
  simp only [Verify.symsOf, ← Verify.firstsOf_eraseDups] at hD
  intro j hj
  have hm : Verify.symAt (Order.distinctSyms b o).1 (Order.distinctSyms b o).2 j ∈
      (Verify.firstsOf (Verify.symAt b o) (o.size - 1)).map (Verify.symAt b o) := by
    rw [← hD]; exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  obtain ⟨f, hf, he⟩ := List.mem_map.1 hm
  exact utf8_congr he.symm (hu f (Verify.firsts_lt _ _ hf))

/-- `concatSyms`' fold keeps every part's entries, so they are valid where the parts' are. -/
theorem utf8_concatSyms_foldl (L : List (ByteArray × Array Nat))
    (hL : ∀ x ∈ L, SymsWF x.1 x.2 ∧ ∀ i < x.2.size - 1, (Column.symKey x.1 x.2 i).IsValidUTF8)
    (acc : ByteArray × Array Nat) (hacc : SymsWF acc.1 acc.2)
    (hu : ∀ i < acc.2.size - 1, (Column.symKey acc.1 acc.2 i).IsValidUTF8) :
    ∀ i < (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).2.size - 1,
      (Column.symKey (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).1
        (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).2
        i).IsValidUTF8 := by
  induction L generalizing acc with
  | nil => exact hu
  | cons x L ih =>
    obtain ⟨hx, hxu⟩ := hL x (List.mem_cons_self ..)
    obtain ⟨s1, s2, s3, s4⟩ := Verify.concatSyms_step hacc hx
    have hp := hacc.pos
    simp only [List.foldl_cons]
    refine ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
      (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size)) s1 fun i hi => ?_
    dsimp only at hi ⊢
    rw [s2] at hi
    apply utf8_of_inv s1 (by rw [s2]; omega)
    rcases Nat.lt_or_ge i (acc.2.size - 1) with h | h
    · rw [s3 i h]; exact inv_of_utf8 hacc h (hu i h)
    · have := s4 (i - (acc.2.size - 1)) (by omega)
      rw [show acc.2.size - 1 + (i - (acc.2.size - 1)) = i by omega] at this
      rw [this]; exact inv_of_utf8 hx (by omega) (hxu _ (by omega))

/-- **`concatSyms` writes only valid UTF-8** where every part is well formed and holds only valid UTF-8. -/
theorem utf8_concatSyms {parts : Array (ByteArray × Array Nat)}
    (hw : ∀ x ∈ parts, SymsWF x.1 x.2 ∧ ∀ i < x.2.size - 1, (Column.symKey x.1 x.2 i).IsValidUTF8)
    {t n a} {b : ByteArray} {o : Array Nat} (h : Kernel.concatSyms parts = .vector t n (.syms b o) a) :
    ∀ i < o.size - 1, (Column.symKey b o i).IsValidUTF8 := by
  have hc : Kernel.concatSyms parts = .vector .symbol
      ((parts.toList.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size)))
        (ByteArray.empty, #[0])).2.size - 1 |> fun c => needSize c "concatSyms: symbols" (fun _ => 0) id) (.syms
      (parts.toList.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size)))
        (ByteArray.empty, #[0])).1
      (parts.toList.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size)))
        (ByteArray.empty, #[0])).2) none := by
    unfold Kernel.concatSyms; rw [Array.foldl_toList]
  rw [hc] at h
  injection h with _ _ he _
  injection he with hb ho
  subst hb ho
  exact utf8_concatSyms_foldl parts.toList (fun x hx => hw x (Array.mem_def.2 hx)) _ (by decide)
    (fun i hi => by simp at hi)

/-- `fewSyms` copies, NUL included, the dictionary entry each element's id names: its answer is laid out as
    `SymsWF` says and holds only valid UTF-8 where the dictionary does. -/
theorem fewSyms_utf8 {n : USize} {d : ByteArray} {dof : Array Nat} {ids b : ByteArray} {bo : Array Nat}
    (hd : SymsWF d dof) (hi : ∀ i < n.toNat, Column.idAt ids (Column.idWidth dof) i < dof.size - 1)
    (hu : ∀ i < dof.size - 1, (Column.symKey d dof i).IsValidUTF8)
    (h : fewSyms n (.enum d dof ids) = some (b, bo)) :
    SymsWF b bo ∧ ∀ j < bo.size - 1, (Column.symKey b bo j).IsValidUTF8 := by
  unfold fewSyms at h
  dsimp only at h
  split at h
  · rw [Option.some.injEq] at h
    have H := fold_inv _ (fun p : ByteArray × Array Nat => SymsWF p.1 p.2 ∧ ∀ t < p.2.size - 1,
        ∃ k : ByteArray, k.IsValidUTF8 ∧ (Verify.symBytes p.1 p.2 t).dropLast = k.data.toList)
      (fun i hi' p hp => by
        obtain ⟨b, o⟩ := p
        have he := hi i hi'
        exact utf8_push hp.1 hp.2 (Verify.copySlice_end _ _ _ _)
          ⟨_, hu _ he, (Verify.symAt_eq_dropLast d dof _ (hd.le _ (by omega))).symm⟩)
      _ ⟨by decide, fun t ht => by simp at ht⟩ h
    exact ⟨H.1, fun j hj => utf8_of_inv H.1 hj (H.2 j hj)⟩
  · cases h

/-- `concatSyms` (the symbol branch on `syms` parts) answers a well-formed symbol vector, where every part
    is laid out as `SymsWF` says, holds only valid UTF-8, and the parts' symbols, summed, fit a `USize`. -/
theorem concatSyms_wf (parts : Array (ByteArray × Array Nat)) (hw : ∀ x ∈ parts, SymsWF x.1 x.2)
    (hu : ∀ x ∈ parts, ∀ i < x.2.size - 1, (Column.symKey x.1 x.2 i).IsValidUTF8)
    (hN : (parts.map fun p => p.2.size - 1).toList.sum < USize.size) :
    ∃ n e, concatSyms parts = .vector .symbol n e none ∧ Enc.WF .symbol n e := by
  refine ⟨_, _, rfl, ?_⟩
  have hS := (Verify.symBytes_concatSyms hw rfl).1
  have hU := utf8_concatSyms (fun x hx => ⟨hw x hx, hu x hx⟩) (parts := parts) rfl
  simp only [Enc.WF]
  generalize hp : Array.foldl _ (ByteArray.empty, #[0]) parts = p at hS hU ⊢
  have hs : p.2.size = 1 + (parts.map fun p => p.2.size - 1).toList.sum := by
    rw [← hp, ← Array.foldl_toList]
    refine Eq.trans (foldl_sum (fun q : ByteArray × Array Nat => q.2.size) _ (fun p => p.2.size - 1)
      (fun s a => ?_) _ _) ?_
    · simp
    · simp [Nat.add_comm]
  rw [needSize_fits (c := p.2.size - 1) (by omega), id_eq, toUSize_toNat (k := p.2.size - 1) (by omega)]
  exact ⟨by omega, hS, fun i hi => hU i (by omega)⟩

/-- The dense branch of `razeColumn`: parts of `cs.1 · w` bytes each, joined, hold the summed count. -/
theorem concatBytes_wf {t : QAtomicType} {w : Nat} {cs : Array (USize × Enc)} {ps : Array ByteArray}
    (hb : t ≠ .boolean) (hw : t.width = some w) (hsz : ps.size = cs.size)
    (hps : ∀ i (hi : i < cs.size) (hp : i < ps.size), ps[i].size = cs[i].1.toNat * w)
    {c : USize} (hc : c.toNat = cs.foldl (fun s p => s + p.1.toNat) 0) :
    Enc.WF t c (.bytes (concatBytes ps)) := by
  refine wf_bytes hb hw ?_
  rw [hc]
  have happ : ∀ (l : List ByteArray) (b : ByteArray), (l.foldl (· ++ ·) b).size = b.size + (l.map (·.size)).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => intro b; simp [ih, ByteArray.size_append]; omega
  have hmap : ps.toList.map (·.size) = cs.toList.map (·.1.toNat * w) := by
    apply List.ext_getElem (by simp [hsz]); intro i h1 h2; simp at h1 h2; simp [hps i h2 h1]
  have hm : ∀ l : List (USize × Enc), (l.map (·.1.toNat * w)).sum = (l.map (·.1.toNat)).sum * w := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [ih, Nat.add_mul]
  rw [concatBytes, ← Array.foldl_toList, happ, hmap, ← Array.foldl_toList, foldl_add, hm]
  simp

/-! ## `Enc.answer` -/

private theorem lt_usize {k : Nat} (h : k ≤ 64) : k < USize.size :=
  Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h (by decide)) USize.le_size

/-- `Coc.decode` answers `n` elements at `w` bytes. -/
theorem decode_size (w : USize) (M P : ByteArray) (n : USize) :
    (Coc.decode w M P n).size = n.toNat * w.toNat := by
  simp only [Coc.decode, Coc.elems]
  rw [foldl_size ByteArray.size _ w.toNat (fun _ _ => Column.pushBits_size ..)]; simp

/-- A Frame-of-Reference payload is well formed at a fixed-width type other than boolean and guid
    exactly when its blocks cover its count. -/
theorem wf_foR {t : QAtomicType} {n : USize} {m p : ByteArray} (hw : t.width.isSome) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) (h : n.toNat ≤ Column.blk * Column.nblk m) : Enc.WF t n (.foR m p) := by
  cases t <;> simp_all [Enc.WF]

/-- `encodeBelow`'s `some` is `encode`'s answer. -/
private theorem encodeBelow_eq {w : USize} {x : ByteArray} {mp : ByteArray × ByteArray}
    (h : Coc.encodeBelow w x = some mp) : mp = Coc.encode w x := by
  unfold Coc.encodeBelow at h
  generalize Coc.encode w x = q at h ⊢
  rcases q with ⟨m, p⟩
  simp only at h; split at h
  · cases h; rfl
  · cases h

/-! ## ALP payloads -/

/-- `alpBlob`'s header declares the width it was handed, at any count: byte 8 is the flag. -/
theorem alpF32_alpBlob (f32 : Bool) (w n : Nat) (x : ByteArray) (bs : Array (Nat × Array (Option UInt64))) :
    Column.alpF32 (Coc.alpBlob f32 w n x bs) = f32 := by
  obtain ⟨pad, hpg, hps, hA⟩ := Verify.alpBlob_eq f32 w n x bs _ rfl
  rw [hA]
  unfold Column.alpF32
  generalize hS : Column.pushBits ByteArray.empty _ 8 = S
  have hS8 : S.size = 8 := by rw [← hS, Column.pushBits_size]; rfl
  have h16 : (Column.pushBits S (if f32 then 1 else 0) 8).size = 16 := by rw [Column.pushBits_size, hS8]
  have hp : (pad (Column.pushBits S (if f32 then 1 else 0) 8)).size = 16 := by rw [hps, h16]
  rw [Column.bitsAt_congr (Column.pushBits S (if f32 then 1 else 0) 8) _ 8 8 (fun k hk => ?_)]
  · have hP := Column.bitsAt_pushBits S (if f32 then 1 else 0) 8 (by decide)
    rw [hS8] at hP; rw [hP]; cases f32 <;> decide
  · repeat rw [Verify.ba_append_left _ _ _ (by simp only [ByteArray.size_append, hp]; omega)]
    exact hpg _ _ (by omega)

/-- `alpEncodeAt` lays out a block for every `blk` of its elements: `Enc.WF`'s cover condition. -/
theorem nblk_alpEncodeAt (f32 : Bool) (x : ByteArray) :
    x.size / (if f32 then 4 else 8) ≤ Column.blk * Column.nblk (Coc.alpEncodeAt f32 x).1 := by
  unfold Coc.alpEncodeAt
  simp only []
  rw [show (8 : USize) = (8 : Nat).toUSize from rfl, Verify.nblk_encode 8 (by decide) (by decide),
    Verify.blocks_size]
  simp only [Array.toList_map, Array.toList_range, List.map_map, Function.comp_def, Coc.alpBlockOf,
    Array.size_map, Array.size_range]
  rw [Verify.sum_blocks]
  generalize x.size / (if f32 then 4 else 8) = n
  simp only [Column.blk] at *
  omega

/-- `Coc.alpDecode` holds `n` elements of `w` bytes, as `decodeW` says of `Coc.decode`. -/
theorem alpDecode_size (w : USize) (hw : w.toNat ≤ 8) (M P a : ByteArray) (n : USize) :
    (Coc.alpDecode w M P a n).size = w.toNat * n.toNat := by
  obtain ⟨hs, -, -⟩ := Verify.foldl_pushBits id w.toNat hw (Coc.alpElems M P a n) ByteArray.empty
  rw [Verify.alpDecode_eq]; simpa [Coc.alpElems] using hs

/-- `alpEncodeAt` at a float type's own width is a well-formed ALP payload of every count its input
    holds. -/
theorem alpEncodeAt_wf {t : QAtomicType} {n : USize} (f32 : Bool) (ht : Column.alpEncodes t = true)
    (hf : t.width = some (if f32 then 4 else 8)) (x : ByteArray) (hn : n.toNat ≤ x.size / (if f32 then 4 else 8)) :
    Enc.WF t n (.alp (Coc.alpEncodeAt f32 x).1 (Coc.alpEncodeAt f32 x).2.1 (Coc.alpEncodeAt f32 x).2.2) := by
  have hF : Column.alpF32 (Coc.alpEncodeAt f32 x).2.2 = f32 := alpF32_alpBlob ..
  simp only [Enc.WF]
  refine ⟨by cases t <;> simp_all [Column.alpEncodes], Nat.le_trans hn (nblk_alpEncodeAt f32 x), ?_⟩
  rw [hF, hf]; cases f32 <;> decide

/-- `alpEncodeBelow`'s `some` is `alpEncodeAt`'s answer. -/
private theorem alpEncodeBelow_eq {f32 : Bool} {x m p a : ByteArray}
    (h : (if f32 = true then Coc.alpEncodeBelow32 x else Coc.alpEncodeBelow64 x) = some (m, p, a)) :
    m = (Coc.alpEncodeAt f32 x).1 ∧ p = (Coc.alpEncodeAt f32 x).2.1 ∧ a = (Coc.alpEncodeAt f32 x).2.2 := by
  cases f32 <;>
    simp only [Coc.alpEncodeBelow32, Coc.alpEncodeBelow64, Coc.alpEncode32, Coc.alpEncode64, if_true,
      Bool.false_eq_true, if_false] at h <;>
    (generalize Coc.alpEncodeAt _ x = q at h ⊢
     rcases q with ⟨m', p', a'⟩
     simp only at h
     split at h
     · obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
     · cases h)

/-- A float type's width is the one its ALP width flag names. -/
private theorem alp_width {t : QAtomicType} {w : Nat} (ht : Column.alpEncodes t = true) (hw : t.width = some w) :
    (if (w == 4) = true then 4 else 8) = w ∧ 0 < w := by
  cases t <;> simp_all [Column.alpEncodes, QAtomicType.width] <;> subst hw <;> decide

/-- `Enc.answer` keeps a well-formed payload well formed: it keeps it, encodes dense bytes by
    `alpEncodeBelow` or `encodeBelow`, or decodes it to `n · w` bytes. -/
theorem answer_wf {t : QAtomicType} {n : USize} {e : Enc}
    (hwf : Enc.WF t n e) : Enc.WF t n (Enc.answer t n e) := by
  have hdec : ∀ {w}, t.width = some w → ∀ {b}, Enc.bytesOf t n e = some b → Enc.WF t n (.bytes b) := by
    intro w hw b hbo
    by_cases hb : t = .boolean
    · subst hb; cases e <;> simp_all [Enc.WF, Enc.bytesOf]
    obtain ⟨b', hb', hs⟩ := bytesOf_size hb hw hwf
    rw [hbo] at hb'; cases hb'
    exact wf_bytes hb hw hs
  unfold Enc.answer
  split
  · exact hwf
  rcases hW : t.width with _ | w
  · exact hwf
  cases e
  case bytes b =>
    have hb : t ≠ .boolean := by rintro rfl; simp [Enc.WF] at hwf
    have hs : b.size = n.toNat * w := by simpa [Enc.WF, hW] using hwf
    simp only
    split
    · exact hwf
    by_cases hA : Column.alpEncodes t = true
    · rw [if_pos hA]
      obtain ⟨h48, h0⟩ := alp_width hA hW
      generalize hE : (if (w == 4) = true then Coc.alpEncodeBelow32 b else Coc.alpEncodeBelow64 b) = E
      rcases E with _ | ⟨m, p, a⟩
      · exact hwf
      obtain ⟨rfl, rfl, rfl⟩ := alpEncodeBelow_eq hE
      exact alpEncodeAt_wf _ hA (by rw [h48]; exact hW) b (by rw [h48, hs, Nat.mul_div_cancel _ h0]; exact Nat.le_refl _)
    rw [if_neg hA]
    split
    · rename_i hE
      split
      · rename_i m p heq
        have h0 : 0 < w ∧ w ≤ 8 ∧ t ≠ .guid := by
          cases t <;> simp_all [QAtomicType.width, Column.encodes] <;> omega
        have hk := Verify.nblk_encode w h0.1 h0.2.1 b
        rw [← encodeBelow_eq heq] at hk
        simp only [hs, Nat.mul_div_cancel _ h0.1] at hk
        refine wf_foR (by simp [hW]) hb h0.2.2 ?_
        rw [hk]; simp only [Column.blk]; omega
      · exact hwf
    · exact hwf
  all_goals
    simp only
    split
    · exact hwf
    split
    · rename_i b hbo; exact hdec hW hbo
    · exact hwf

/-! ## The `enum` branch: `concatEnum` -/

/-- The widths an id pack takes: `laneWidth`'s answers. -/
private theorem lane_idWidth (offs : Array Nat) : Column.idWidth offs = 0 ∨ laneOK(Column.idWidth offs) := by
  simp only [Column.idWidth, Column.idWidthOf, Column.laneWidth]
  repeat' split
  all_goals omega

/-- A `Nat.fold` that pushes a byte a step answers one byte per step. -/
private theorem fold_push_size (g : Nat → UInt8) :
    ∀ (k : Nat) (b : ByteArray), (Nat.fold k (fun i _ acc => acc.push (g i)) b).size = b.size + k
  | 0, b => by simp
  | k + 1, b => by
    rw [Nat.fold_succ, ← Nat.add_assoc, ← fold_push_size g k b]
    simp only [ByteArray.size, ByteArray.push, Array.size_push]

/-- **`packIds` at a lane is `⌈n·w/8⌉` bytes**, the size `Enc.WF` asks of an id pack. -/
theorem packIds_size {w : Nat} (hw : w = 0 ∨ laneOK(w))
    (n : Nat) (f : Nat → Nat) : (Column.packIds w n f).size = (n * w + 7) / 8 := by
  have hbytes : ∀ c, 1 ≤ c → c ≤ 8 → (Column.packIds (8 * c) n f).size = (n * (8 * c) + 7) / 8 :=
    fun c h1 h8 => by rw [(Verify.packIds_bytes c n f h1 h8).1, Nat.mul_comm n, Nat.mul_assoc]; omega
  have hsub : ∀ w, 1 ≤ w → w < 8 → (Column.packIds w n f).size = (n + 8 / w - 1) / (8 / w) := fun w h1 h8 => by
    unfold Column.packIds
    rw [if_neg (by omega), if_neg (by omega)]
    exact (fold_push_size _ _ _).trans (Nat.zero_add _)
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Column.packIds]
  · rw [hsub 1 (by decide) (by decide)]; omega
  · rw [hsub 2 (by decide) (by decide)]; omega
  · rw [hsub 4 (by decide) (by decide)]; omega
  · exact hbytes 1 (by decide) (by decide)
  · exact hbytes 2 (by decide) (by decide)
  · exact hbytes 4 (by decide) (by decide)
  · exact hbytes 8 (by decide) (by decide)

/-- An id below `n` that fits 64 bits fits the width `idWidthOf n` packs it at, whatever `n` is: past `2 ^ 64`
    the lane is 64 bits. -/
theorem lt_idWidthOf_64 {x n : Nat} (hx : x < n) (h64 : x < 2 ^ 64) : x < 2 ^ Column.idWidthOf n := by
  by_cases hn : n ≤ 2 ^ 64
  · exact Verify.lt_idWidthOf hx hn
  · have hl : 64 ≤ Nat.log2 (n - 1) := (Nat.le_log2 (by omega)).2 (by omega)
    have h : Column.idWidthOf n = 64 := by
      simp only [Column.idWidthOf, Column.widthFor, if_neg (show n - 1 ≠ 0 by omega), Column.laneWidth]
      repeat' rw [if_neg (by omega)]
    rw [h]; exact h64

/-- **`internSyms` names an entry for every element**, with no bound on the count: the element's symbol is
    among the distinct ones, so `findSymScalar` finds it below the dictionary's count. -/
theorem internSyms_lt (blob : ByteArray) (offs : Array Nat) {y : Nat} (hy : y < offs.size - 1) :
    Column.idAt (Order.internSyms blob offs).2.2 (Column.idWidth (Order.internSyms blob offs).2.1) y <
      (Order.internSyms blob offs).2.1.size - 1 := by
  have hD := Verify.distinctSyms_eraseDups blob offs
  have e : Order.internSyms blob offs = ((Order.distinctSyms blob offs).1, (Order.distinctSyms blob offs).2,
      Column.packIds (Column.idWidth (Order.distinctSyms blob offs).2) (offs.size - 1) fun j =>
        (findSymScalar (Order.distinctSyms blob offs).1 (Order.distinctSyms blob offs).2
          (Column.symKey blob offs j)).toNat) := rfl
  rw [e]
  generalize Order.distinctSyms blob offs = r at hD ⊢
  obtain ⟨db, dof⟩ := r
  dsimp only [Verify.symsOf] at hD ⊢
  simp only [← Verify.firstsOf_eraseDups] at hD
  have hmem : Verify.symAt blob offs y ∈ (List.range (dof.size - 1)).map (Verify.symAt db dof) := by
    rw [hD]; exact Verify.mem_firstsOf _ hy
  obtain ⟨j, hj, hje⟩ := List.mem_map.1 hmem
  have hv : (findSymScalar db dof (Column.symKey blob offs y)).toNat < dof.size - 1 := by
    unfold findSymScalar
    dsimp only
    cases hf : (List.range (dof.size - 1)).find?
        (fun i => (Column.symKey db dof i).data == (Column.symKey blob offs y).data) with
    | none =>
      exfalso
      exact List.find?_eq_none.1 hf j hj ((Verify.arr_beq_iff _ _).2 (Array.toList_inj.1 hje))
    | some j' =>
      have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
      rw [Option.getD_some]
      refine Nat.lt_of_le_of_lt (show j'.toUSize.toNat ≤ j' from ?_) this
      rw [show j'.toUSize = USize.ofNat j' from rfl, USize.toNat_ofNat']
      exact Nat.mod_le _ _
  have hl := lt_idWidthOf_64 hv (Verify.usize_lt _)
  rw [Column.idWidth] at ⊢
  rw [Column.idWidthOf] at hl ⊢
  rw [Verify.idAt_packIds (Verify.laneWidth_cases _) hy hl]
  exact hv

/-- **`concatIds` writes ids below `D`** where every part's ids, read through its map, are. -/
theorem concatIds_lt {w D : Nat} (hw : w = 0 ∨ laneOK(w)) (cs : Array USize) (ws : Array Nat) (maps parts : Array ByteArray)
    (hm : cs.size ≤ parts.size)
    (h : ∀ k (hk : k < cs.size), ∀ i < cs[k].toNat, Column.idAt maps[k]! w (Column.idAt parts[k]! ws[k]! i) < D) :
    ∀ i < (cs.toList.map USize.toNat).sum,
      Column.idAt (concatIds w.toUSize (countBytes cs) ws maps parts) w i < D := by
  intro i hi
  have hw64 : w ≤ 64 := by rcases hw with h | h | h | h | h | h | h | h <;> omega
  simp only [concatIds]
  rw [toUSize_toNat (lt_usize hw64)]
  have hsz := flatMap_counts cs parts.size hm fun k i => Column.idAt maps[k]! w (Column.idAt parts[k]! ws[k]! i)
  generalize hids : (Array.range (min ((countBytes cs).size / 8) parts.size)).flatMap (fun k =>
    (Array.range (Column.bitsAt (countBytes cs) (8 * k) 8).toNat).map fun i =>
      Column.idAt maps[k]! w (Column.idAt parts[k]! ws[k]! i)) = ids at hsz ⊢
  have hil : i < ids.size := by rw [hsz]; exact hi
  have hmem : ids[i]! ∈ ids := by rw [getElem!_pos ids i hil]; exact Array.getElem_mem hil
  rw [← hids] at hmem
  obtain ⟨k, hk, hx⟩ := Array.mem_flatMap.1 hmem
  obtain ⟨x, hx, he⟩ := Array.mem_map.1 hx
  rw [hids] at he
  rw [Array.mem_range] at hk hx
  have hk' : k < cs.size := by rw [countBytes_size, Nat.mul_div_cancel_left _ (by decide)] at hk; omega
  rw [countBytes_get cs k hk', USize.toNat_toUInt64] at hx
  have hb : ids[i]! < 2 ^ w := by rw [← he]; exact Verify.idAt_lt _ _ _ hw64
  rw [Verify.idAt_packIds hw hil hb, ← he]
  exact h k hk' x hx

/-- A fold that pushes the last entry plus the next part's count keeps every entry it was handed. -/
private theorem bases_keep (g : Array Nat → ByteArray × Array Nat → Array Nat)
    (hg : ∀ acc x, g acc x = acc.push (acc[acc.size - 1]! + x.2.size - 1)) (l : List (ByteArray × Array Nat)) :
    ∀ (acc : Array Nat) (i : Nat), i < acc.size → (l.foldl g acc)[i]! = acc[i]! := by
  induction l with
  | nil => intro acc i _; rfl
  | cons a l ih =>
    intro acc i hi
    simp only [List.foldl]
    rw [ih _ i (by rw [hg, Array.size_push]; omega), hg, getElem!_pos _ i (by rw [Array.size_push]; omega),
      getElem!_pos acc i hi, Array.getElem_push_lt hi]

/-- `internConcat`'s bases: part `k` starts where the parts before it end, so its entries end by the total. -/
private theorem bases_bound (g : Array Nat → ByteArray × Array Nat → Array Nat)
    (hg : ∀ acc x, g acc x = acc.push (acc[acc.size - 1]! + x.2.size - 1)) (l : List (ByteArray × Array Nat))
    (hl : ∀ x ∈ l, 0 < x.2.size) :
    ∀ (acc : Array Nat), 0 < acc.size → ∀ k (hk : k < l.length),
      (l.foldl g acc)[acc.size - 1 + k]! + (l[k].2.size - 1) ≤ acc[acc.size - 1]! + (l.map (·.2.size - 1)).sum := by
  induction l with
  | nil => intro _ _ k hk; exact absurd hk (Nat.not_lt_zero _)
  | cons a l ih =>
    intro acc hacc k hk
    have ha := hl a (List.mem_cons_self ..)
    have hpush : (acc.push (acc[acc.size - 1]! + a.2.size - 1))[acc.size]! = acc[acc.size - 1]! + a.2.size - 1 := by
      rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
    simp only [List.foldl, List.map_cons, List.sum_cons]
    cases k with
    | zero =>
      rw [Nat.add_zero, bases_keep g hg l _ _ (by rw [hg, Array.size_push]; omega), hg,
        getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_lt (by omega),
        ← getElem!_pos acc _ (by omega), List.getElem_cons_zero]
      omega
    | succ k =>
      have := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (g acc a) (by rw [hg, Array.size_push]; omega) k
        (by simpa using hk)
      rw [hg, Array.size_push, Nat.add_sub_cancel, hpush] at this
      rw [show acc.size - 1 + (k + 1) = acc.size + k by omega, List.getElem_cons_succ, hg]
      omega

/-- `concatSyms`' fold grows its starts by each part's count. -/
private theorem concat_size (g : ByteArray × Array Nat → ByteArray × Array Nat → ByteArray × Array Nat)
    (hg : ∀ q x, (g q x).2.size = q.2.size + (x.2.size - 1)) (l : List (ByteArray × Array Nat))
    (p : ByteArray × Array Nat) : (l.foldl g p).2.size = p.2.size + (l.map (·.2.size - 1)).sum :=
  foldl_sum (fun q => q.2.size) g (fun x => x.2.size - 1) hg l p

/-- `internConcat`'s part `k` starts at `bases[k]` and its entries end by the joined dictionary's count. -/
private theorem bases_le (qs : Array (USize × ByteArray × Array Nat × ByteArray)) (hq : ∀ p ∈ qs, 0 < p.2.2.1.size)
    (f : USize × ByteArray × Array Nat × ByteArray → ByteArray × Array Nat) (hf : ∀ p, f p = (p.2.1, p.2.2.1))
    (g : Array Nat → ByteArray × Array Nat → Array Nat)
    (hg : ∀ acc x, g acc x = acc.push (acc[acc.size - 1]! + x.2.size - 1))
    (g' : ByteArray × Array Nat → ByteArray × Array Nat → ByteArray × Array Nat)
    (hg' : ∀ q x, (g' q x).2.size = q.2.size + (x.2.size - 1)) (k : Nat) (hk : k < qs.size) :
    ((qs.map f).foldl g #[0])[k]! + (qs[k].2.2.1.size - 1) ≤
      ((qs.map f).foldl g' (ByteArray.empty, #[0])).2.size - 1 := by
  have hl : ∀ y ∈ (qs.map f).toList, 0 < y.2.size := by
    intro y hy
    simp only [Array.toList_map, List.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [hf]; exact hq p (Array.mem_def.2 hp)
  have hb := bases_bound g hg _ hl #[0] (by decide) k (by simpa using hk)
  have hc := concat_size g' hg' (qs.map f).toList (ByteArray.empty, #[0])
  rw [Array.foldl_toList] at hb hc
  have e : ((qs.map f).toList[k]'(by simpa using hk)).2.size = qs[k].2.2.1.size := by simp [hf]
  have h0 : (#[0] : Array Nat)[(#[0] : Array Nat).size - 1]! = 0 := rfl
  have h1 : (#[0] : Array Nat).size - 1 + k = k := by simp
  have h2 : (ByteArray.empty, (#[0] : Array Nat)).2.size = 1 := rfl
  rw [e, h1, h0] at hb
  rw [h2] at hc
  omega

/-- **`internConcat` writes ids below its dictionary's count**, on parts whose ids are below theirs. -/
theorem internConcat_ids_lt (qs : Array (USize × ByteArray × Array Nat × ByteArray))
    (hq : ∀ p ∈ qs, 0 < p.2.2.1.size ∧
      ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1) :
    ∀ i < qs.foldl (fun s p => s + p.1.toNat) 0,
      Column.idAt (internConcat qs).2.2 (Column.idWidth (internConcat qs).2.1) i < (internConcat qs).2.1.size - 1 := by
  intro i hi
  unfold internConcat
  simp only [concatSyms]
  refine concatIds_lt (lane_idWidth _) _ _ _ _ (by simp) ?_ i (by rw [foldl_toNat] at hi; exact hi)
  intro k hk x hx
  simp only [Array.size_map] at hk
  have hW : ∀ o : Array Nat, Column.idWidth o ≤ 64 := fun o => by
    rcases lane_idWidth o with h | h | h | h | h | h | h | h <;> omega
  simp (disch := simp [hk]) only [getElem!_pos, Array.getElem_map, Array.getElem_range]
  obtain ⟨-, hid⟩ := hq qs[k] (Array.getElem_mem hk)
  have hxo := hid x (by simpa using hx)
  rw [Verify.idAt_packIds (lane_idWidth _) hxo]
  rotate_left
  · exact Verify.idAt_lt _ _ _ (hW _)
  refine internSyms_lt _ _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hxo _) ?_)
  exact bases_le qs (fun p hp => (hq p hp).1) _ (fun _ => rfl) _ (fun _ _ => rfl) _ (fun q x => by simp) k hk

/-- `internConcat` answers its joined dictionary and `concatIds` over every part's count and ids. -/
private theorem internConcat_eq (qs : Array (USize × ByteArray × Array Nat × ByteArray)) :
    ∃ db dbo ws maps, internConcat qs =
      (db, dbo, concatIds (Column.idWidth dbo).toUSize (countBytes (qs.map (·.1))) ws maps (qs.map (·.2.2.2))) :=
  ⟨_, _, _, _, rfl⟩

private theorem hashConcat_ok {qs : Array (USize × ByteArray × Array Nat × ByteArray)} {r}
    (h : hashConcat qs = .ok r) : r = internConcat qs := by
  simp only [hashConcat] at h
  repeat' split at h
  all_goals first | (injection h with h; exact h.symm) | simp at h

private theorem hashConcat_error {qs : Array (USize × ByteArray × Array Nat × ByteArray)} {r}
    (h : hashConcat qs = .error r) : r = qs := by
  simp only [hashConcat] at h
  repeat' split at h
  all_goals first | (injection h with h; exact h.symm) | simp at h

/-- `internConcat`'s dictionary is `internSyms`' of the joined dictionaries. -/
private theorem internConcat_dict (qs : Array (USize × ByteArray × Array Nat × ByteArray)) :
    ∃ b o, (internConcat qs).1 = (Order.internSyms b o).1 ∧ (internConcat qs).2.1 = (Order.internSyms b o).2.1 :=
  ⟨_, _, rfl, rfl⟩

/-- `internConcat` of parts holds their summed count, over a dictionary ending at its blob. -/
theorem internConcat_wf (qs : Array (USize × ByteArray × Array Nat × ByteArray)) {c : USize}
    (hc : c.toNat = qs.foldl (fun s p => s + p.1.toNat) 0)
    (hq : ∀ p ∈ qs, 0 < p.2.2.1.size ∧
      ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1)
    (hu : ∀ p ∈ qs, SymsWF p.2.1 p.2.2.1 ∧ ∀ i < p.2.2.1.size - 1, (Column.symKey p.2.1 p.2.2.1 i).IsValidUTF8) :
    Enc.WF .symbol c (.enum (internConcat qs).1 (internConcat qs).2.1 (internConcat qs).2.2) := by
  have hi := internConcat_ids_lt qs hq
  rw [← hc] at hi
  -- the dictionary is `distinctSyms` of the parts' dictionaries joined, so its entries are theirs
  have hv : ∀ j < (internConcat qs).2.1.size - 1,
      (Column.symKey (internConcat qs).1 (internConcat qs).2.1 j).IsValidUTF8 := by
    obtain ⟨n', cb, co, hcs, e1, e2⟩ : ∃ n' cb co, concatSyms (qs.map fun p => (p.2.1, p.2.2.1)) =
        .vector .symbol n' (.syms cb co) none ∧ (internConcat qs).1 = (Order.internSyms cb co).1 ∧
        (internConcat qs).2.1 = (Order.internSyms cb co).2.1 := ⟨_, _, _, rfl, rfl, rfl⟩
    rw [e1, e2]
    exact utf8_distinctSyms cb co (utf8_concatSyms (fun x hx => by
      obtain ⟨p, hp, rfl⟩ := Array.mem_map.1 hx; exact hu p hp) hcs)
  obtain ⟨b, o, h1, h2⟩ := internConcat_dict qs
  have hs := Verify.symsWF_internSyms b o
  have hd : SymsWF (internConcat qs).1 (internConcat qs).2.1 := by rw [h1, h2]; exact hs
  have hn : ((List.range ((internConcat qs).2.1.size - 1)).map
      (Verify.symAt (internConcat qs).1 (internConcat qs).2.1)).Nodup := by
    rw [h1, h2]
    have hD := Verify.distinctSyms_eraseDups b o
    simp only [Verify.symsOf, ← Verify.firstsOf_eraseDups] at hD
    show ((List.range ((Order.distinctSyms b o).2.size - 1)).map
      (Verify.symAt (Order.distinctSyms b o).1 (Order.distinctSyms b o).2)).Nodup
    rw [hD]; exact Verify.nodup_firsts ..
  obtain ⟨db, dbo, ws, maps, h⟩ := internConcat_eq qs
  rw [h] at hd hn hi hv ⊢
  refine ⟨?_, hd, hi, hn, hv⟩
  simp only [concatIds]
  rw [hc, toUSize_toNat (lt_usize (by rcases lane_idWidth dbo with h | h | h | h | h | h | h | h <;> omega))]
  have hsz := flatMap_counts (qs.map (·.1)) (qs.map (·.2.2.2)).size (by simp)
    fun k i => Column.idAt maps[k]! (Column.idWidth dbo) (Column.idAt (qs.map (·.2.2.2))[k]! ws[k]! i)
  rw [foldl_toNat, ← hsz]
  exact packIds_size (lane_idWidth dbo) _ _

/-- The interned join `concatEnum` answers after `hashConcat`, whichever way that goes. -/
private theorem hashJoin_wf (qs : Array (USize × ByteArray × Array Nat × ByteArray)) {c : USize}
    (hc : c.toNat = qs.foldl (fun s p => s + p.1.toNat) 0)
    (hq : ∀ p ∈ qs, 0 < p.2.2.1.size ∧
      ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1)
    (hu : ∀ p ∈ qs, SymsWF p.2.1 p.2.2.1 ∧ ∀ i < p.2.2.1.size - 1, (Column.symKey p.2.1 p.2.2.1 i).IsValidUTF8) :
    Enc.WF .symbol c (match hashConcat qs with
      | .ok (db, dbo, ids) => .enum db dbo ids
      | .error ps => match internConcat ps with | (db, dbo, ids) => .enum db dbo ids) := by
  split
  · rename_i db dbo ids heq
    have := internConcat_wf qs hc hq hu
    rw [← hashConcat_ok heq] at this
    exact this
  · rename_i r heq
    obtain rfl := hashConcat_error heq
    exact internConcat_wf r hc hq hu

/-- A `Nat.fold` that pushes one start a step pushes one per step. -/
private theorem fold_snd_size {N : Nat} (f : (i : Nat) → i < N → ByteArray × Array Nat → ByteArray × Array Nat)
    (hf : ∀ i h p, (f i h p).2.size = p.2.size + 1) (init : ByteArray × Array Nat) :
    (Nat.fold N f init).2.size = init.2.size + N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.fold_succ, hf, ih (fun i h => f i (by omega)) (fun i h p => hf i _ p)]
    omega

/-- `fewSyms` answers one entry per element. -/
theorem fewSyms_size {n : USize} {d : ByteArray} {o : Array Nat} {ids b : ByteArray} {bo : Array Nat}
    (h : fewSyms n (.enum d o ids) = some (b, bo)) : bo.size = n.toNat + 1 := by
  unfold fewSyms at h
  dsimp only at h
  by_cases hc : 8 * n.toNat < o.size - 1
  · rw [if_pos hc, Option.some.injEq] at h
    have := congrArg (fun p : ByteArray × Array Nat => p.2.size) h
    simp only at this
    rw [← this, fold_snd_size _ (fun i _ p => by simp)]
    show 1 + n.toNat = n.toNat + 1
    omega
  · rw [if_neg hc] at h; cases h

/-! ## The `foR` branch: `concatFoR` -/

private theorem sum_map_mul {β : Type} (f : β → Nat) (k : Nat) :
    ∀ l : List β, (l.map (fun x => f x * k)).sum = (l.map f).sum * k
  | [] => by simp
  | x :: l => by simp [sum_map_mul f k l, Nat.add_mul]

private theorem sum_le_mul {β : Type} (f g : β → Nat) (k : Nat) :
    ∀ l : List β, (∀ x ∈ l, f x ≤ k * g x) → (l.map f).sum ≤ k * (l.map g).sum
  | [], _ => by simp
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    have h1 := sum_le_mul f g k l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h2 := h x (by simp)
    omega

private theorem foldl_append_size {α β : Type} (g : β → Array α) :
    ∀ (l : List β) (a : Array α),
      (l.foldl (fun acc p => acc ++ g p) a).size = a.size + (l.map (fun p => (g p).size)).sum
  | [], a => by simp
  | p :: l, a => by
    simp only [List.foldl, foldl_append_size g l, Array.size_append, List.map_cons, List.sum_cons]; omega

/-- `concatBytes` holds every part's bytes. -/
theorem concatBytes_size (ps : Array ByteArray) : (concatBytes ps).size = (ps.toList.map (·.size)).sum := by
  have happ : ∀ (l : List ByteArray) (b : ByteArray), (l.foldl (· ++ ·) b).size = b.size + (l.map (·.size)).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => intro b; simp [ih, ByteArray.size_append]; omega
  rw [concatBytes, ← Array.foldl_toList, happ]; simp

/-- `foRMeta` of `bs` blocks: four sections of eight bytes a block, the sixteen-byte trailer, a width
    byte a block. So `nblk` reads `bs.size` back. -/
theorem foRMeta_size (nul : UInt64) (sumn : Nat) (bs : Array (UInt64 × UInt64 × UInt64 × Nat)) :
    (Coc.foRMeta nul sumn bs).size = 33 * bs.size + 16 := by
  have hA : ∀ (f : (UInt64 × UInt64 × UInt64 × Nat) → UInt64) (l : List (UInt64 × UInt64 × UInt64 × Nat)),
      (l.foldl (fun acc b => Column.pushBits acc (f b) 8) ByteArray.empty).size = l.length * 8 := fun f l => by
    rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp
  have hB : ∀ (l : List (UInt64 × UInt64 × UInt64 × Nat)),
      (l.foldl (fun acc b => acc.push b.2.2.2.toUInt8) ByteArray.empty).size = l.length := fun l => by
    rw [foldl_size ByteArray.size _ 1 (fun _ _ => by simp only [ByteArray.size, ByteArray.push, Array.size_push])]
    simp
  have hC : ∀ (l : List (UInt64 × UInt64 × UInt64 × Nat)) (g : ByteArray × Nat → _ → ByteArray × Nat),
      (∀ x b, (g x b).1.size = x.1.size + 8) → (l.foldl g (ByteArray.empty, 0)).1.size = l.length * 8 :=
    fun l g hg => by refine Eq.trans (foldl_size (fun p : ByteArray × Nat => p.1.size) g 8 hg l _) ?_; simp
  simp only [Coc.foRMeta, ByteArray.size_append, ← Array.foldl_toList, hA, hB]
  rw [hC _ _ (fun x b => by rcases x with ⟨acc, pos⟩; exact Column.pushBits_size ..)]
  simp [Column.pushBits_size]; omega

/-- `moveFoR` claims only parts in the writer's form, each `⌈n/blk⌉` blocks, and moves every block:
    the answer's blocks cover the summed count. -/
theorem moveFoR_nblk {ps : Array ((USize × ByteArray) × ByteArray)} {m p : ByteArray}
    (h : moveFoR ps = some (m, p)) : (ps.toList.map (·.1.1.toNat)).sum ≤ Column.blk * Column.nblk m := by
  unfold moveFoR at h
  split at h
  · cases h
  rename_i hc
  injection h with h; injection h with hm
  subst hm
  have hall : ∀ x ∈ ps.toList, x.1.1.toNat ≤ Column.blk * Column.nblk x.1.2 := by
    intro x hx
    have hs : Coc.foRStd x.1.1 x.1.2 x.2 = true := by
      cases hs : Coc.foRStd x.1.1 x.1.2 x.2
      · exfalso; apply hc
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
        rw [Bool.or_eq_true, Array.any_eq_true]; right
        refine ⟨i, by simpa using hi, ?_⟩
        simp only [Array.getElem_toList] at hs; simp [hs]
      · rfl
    rw [(Verify.foRStd_iff.1 hs).nblk]; simp only [Column.blk]; omega
  rw [Column.nblk, foRMeta_size, show ∀ k, (33 * k + 16) / 33 = k from fun k => by omega,
    ← Array.foldl_toList, foldl_append_size]
  simpa using sum_le_mul _ _ _ _ hall

/-- `appendFoR` keeps the first part's metadata and claims only where the appended elements fit its
    last, part-filled block. -/
theorem appendFoR_nblk {n : USize} {md pk tail m p : ByteArray} (h : appendFoR n md pk tail = some (m, p)) :
    m = md ∧ n.toNat + tail.size / 8 ≤ Column.blk * Column.nblk md := by
  unfold appendFoR at h
  dsimp only at h
  split at h
  · cases h
  rename_i hc
  split at h
  · cases h
  injection h with h; injection h with hm
  refine ⟨hm.symm, ?_⟩
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', not_or] at hc
  obtain ⟨⟨⟨h0, hlt⟩, hs⟩, -⟩ := hc
  rw [(Verify.foRStd_iff.1 (by simpa using hs)).nblk]
  simp only [Column.blk] at *; omega

/-- `concatFoR` of parts of `ns` elements answers blocks covering their sum, whichever of the move, the
    append and the re-encode it takes. -/
theorem concatFoR_nblk {w : Nat} {ns : Array USize} {ms ps : Array ByteArray} {m p : ByteArray}
    (heq : concatFoR w.toUSize (countBytes ns) ms ps = (m, p)) (hw0 : 0 < w) (hw : w ≤ 8)
    (hm : ms.size = ns.size) (hp : ps.size = ns.size) :
    (ns.toList.map USize.toNat).sum ≤ Column.blk * Column.nblk m := by
  suffices H : (ns.toList.map USize.toNat).sum ≤
      Column.blk * Column.nblk (concatFoR w.toUSize (countBytes ns) ms ps).1 by rw [heq] at H; exact H
  have hwu : w.toUSize.toNat = w := toUSize_toNat (lt_usize (by omega))
  unfold concatFoR
  dsimp only
  generalize hq0 : (Array.range (min ((countBytes ns).size / 8) (min ms.size ps.size))).map
    (fun k => (((Column.bitsAt (countBytes ns) (8 * k) 8).toUSize, ms[k]!), ps[k]!)) = q
  have hq : q.toList.map (·.1.1.toNat) = ns.toList.map USize.toNat := by
    rw [← hq0]
    apply List.ext_getElem (by simp [countBytes_size, hm, hp])
    intro i h1 h2
    simp [countBytes_size, hm, hp] at h1
    simp [countBytes_get ns i h1]
  rw [← hq]
  split
  · rename_i out heq; rcases out with ⟨m, p⟩; exact moveFoR_nblk heq
  rcases q with ⟨_ | ⟨⟨⟨n0, md0⟩, pk0⟩, rest⟩⟩
  · simp
  have hx : (List.toArray (((n0, md0), pk0) :: rest)).extract 1 (rest.length + 1) = rest.toArray := by simp
  simp only [List.size_toArray, List.length_cons, hx]
  rw [show (Array.mk (((n0, md0), pk0) :: rest)).get!Internal 0 = ((n0, md0), pk0) from rfl]
  dsimp only
  split
  · rename_i out heq; rcases out with ⟨m, p⟩
    obtain ⟨rfl, hk⟩ := appendFoR_nblk heq
    rw [concatBytes_size] at hk
    simp only [Array.toList_map, List.map_map, Function.comp_def, decode_size] at hk
    have h8 : USize.toNat 8 = 8 := toUSize_toNat (k := 8) (lt_usize (by decide))
    rw [sum_map_mul, h8, Nat.mul_div_cancel _ (by decide : 0 < 8)] at hk
    simpa [Nat.add_comm] using hk
  · rw [Verify.nblk_encode w hw0 hw, concatBytes_size]
    simp only [Array.toList_map, List.map_map, Function.comp_def, decode_size, hwu]
    rw [sum_map_mul, Nat.mul_div_cancel _ hw0]
    simp only [Column.blk]; omega

/-- `concatEnum` answers an interned symbol vector whose ids count it, where the parts' counts, summed,
    fit a `USize`. -/
theorem concatEnum_wf (ps : Array (USize × ByteArray × Array Nat × ByteArray))
    (hN : ps.foldl (fun s p => s + p.1.toNat) 0 < USize.size)
    (hw : ∀ p ∈ ps, 0 < p.2.2.1.size ∧
      ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1)
    (hu : ∀ p ∈ ps, SymsWF p.2.1 p.2.2.1 ∧ ∀ i < p.2.2.1.size - 1, (Column.symKey p.2.1 p.2.2.1 i).IsValidUTF8) :
    ∃ n e, concatEnum ps = .vector .symbol n e none ∧ Enc.WF .symbol n e := by
  unfold concatEnum
  dsimp only
  generalize hq : Array.mapIdx _ ps = qs
  -- a part `fewSyms` re-encodes copies the entries its ids name
  have hU : ∀ p ∈ qs, SymsWF p.2.1 p.2.2.1 ∧
      ∀ i < p.2.2.1.size - 1, (Column.symKey p.2.1 p.2.2.1 i).IsValidUTF8 := by
    intro q hmem
    rw [← hq] at hmem
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hmem
    have hi' : i < ps.size := by simpa using hi
    have hp := hw ps[i] (Array.getElem_mem hi')
    have hp' := hu ps[i] (Array.getElem_mem hi')
    simp only [Array.getElem_mapIdx]
    generalize ps[i] = p at hp hp' ⊢
    obtain ⟨n, d, o, ids⟩ := p
    dsimp only at hp hp' ⊢
    by_cases h0 : (i == 0) = true
    · simp only [h0, if_true]; exact hp'
    · simp only [h0, if_false, Bool.false_eq_true]
      cases hf : fewSyms n (.enum d o ids) with
      | none => exact hp'
      | some r =>
        obtain ⟨b, bo⟩ := r
        dsimp only
        exact fewSyms_utf8 hp'.1 hp.2 hp'.2 hf
  have hP : ∀ p ∈ qs, 0 < p.2.2.1.size ∧
      ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1 := by
    intro q hmem
    rw [← hq] at hmem
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hmem
    have hi' : i < ps.size := by simpa using hi
    have hp := hw ps[i] (Array.getElem_mem hi')
    simp only [Array.getElem_mapIdx]
    generalize ps[i] = p at hp ⊢
    obtain ⟨n, d, o, ids⟩ := p
    dsimp only at hp ⊢
    by_cases h0 : (i == 0) = true
    · simp only [h0, if_true]; exact hp
    · simp only [h0, if_false, Bool.false_eq_true]
      cases hf : fewSyms n (.enum d o ids) with
      | none => exact hp
      | some r =>
        obtain ⟨b, bo⟩ := r
        have hs := fewSyms_size hf
        dsimp only
        refine ⟨by omega, fun j hj => ?_⟩
        rw [Verify.idAt_packIds (lane_idWidth _) hj]
        · show j < bo.size - 1
          omega
        · exact lt_idWidthOf_64 (n := bo.size - 1) (by omega) (Nat.lt_trans hj (Verify.usize_lt n))
  have hk : qs.foldl (fun s p => s + p.1.toNat) 0 < USize.size := by
    have hmap : qs.map (·.1) = ps.map (·.1) := by
      rw [← hq]
      apply Array.ext (by simp)
      intro i h1 h2
      simp only [Array.getElem_map, Array.getElem_mapIdx]
      repeat' split
      all_goals simp_all
    rw [foldl_toNat, hmap, ← foldl_toNat]; exact hN
  refine ⟨_, _, rfl, ?_⟩
  rw [needSize_fits hk]
  exact hashJoin_wf qs (toUSize_toNat hk) hP hU

/-- An `Option` pass whose every answer at a member carries that member's key keeps the keys. -/
private theorem mapM_key {α β γ : Type} {f : α → Option β} {key : α → γ} {key' : β → γ} {cs : Array α}
    (hf : ∀ a ∈ cs, ∀ x, f a = some x → key' x = key a) {qs : Array β}
    (h : cs.mapM f = some qs) : qs.map key' = cs.map key := by
  have hl : ∀ (l : List α), (∀ a ∈ l, ∀ x, f a = some x → key' x = key a) →
      ∀ ql, l.mapM f = some ql → ql.map key' = l.map key := by
    intro l; induction l with
    | nil => intro _ ql h; simp at h; subst h; rfl
    | cons a l ih =>
      intro hf ql h
      rw [List.mapM_cons] at h
      cases ha : f a with
      | none => simp [ha] at h
      | some x =>
        cases hl : l.mapM f with
        | none => simp [ha, hl] at h
        | some xs =>
          simp [ha, hl] at h; subst h
          simp [hf a (by simp) x ha, ih (fun b hb => hf b (by simp [hb])) _ hl]
  rcases cs with ⟨l⟩
  rw [Array.mapM_eq_mapM_toList] at h
  cases hq : l.mapM f with
  | none => simp [hq] at h
  | some ql => simp [hq] at h; subst h; simp [hl l (fun a ha => hf a (Array.mem_def.2 ha)) ql hq]

/-- `encodedParts` keeps every part's count, in order, and a lane per part; it claims only at a type
    one of the two encodings is for. -/
theorem encodedParts_spec {t : QAtomicType} {cs : Array (USize × Enc)} {alp : Bool} {n : Nat}
    {ns : Array USize} {ms ps as : Array ByteArray} (h : encodedParts t cs = some (alp, n, ns, ms, ps, as)) :
    alp = Column.alpEncodes t ∧ ns = cs.map (·.1) ∧ n = (ns.toList.map USize.toNat).sum ∧ ms.size = ns.size ∧
      ps.size = ns.size ∧ as.size = ns.size ∧ (Column.alpEncodes t || Column.encodes t) = true := by
  unfold encodedParts at h
  dsimp only at h
  split at h
  · cases h
  rename_i hc
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  rename_i qs hq
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  have hk := mapM_key (key := (·.1)) (key' := (·.1)) (fun c _ x hx => by
    rcases c with ⟨k, e⟩
    cases e <;> (repeat' split at hx) <;> first | (cases hx; rfl) | (cases hx; simp_all) | cases hx) hq
  refine ⟨rfl, hk, ?_, by simp, by simp, by simp, ?_⟩
  · rw [← Array.foldl_toList, foldl_add]; simp [Function.comp_def]
  · simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hc
    cases h1 : Column.alpEncodes t <;> cases h2 : Column.encodes t <;> simp_all

/-- `concatALP` of parts of `ns` elements is a well-formed ALP payload of their sum at a float type: it
    decodes every part at the type's width and encodes the join once. -/
theorem concatALP_wf {t : QAtomicType} {w : Nat} {ns : Array USize} {ms ps as : Array ByteArray}
    {m p a : ByteArray} (heq : concatALP w.toUSize (countBytes ns) ms ps as = (m, p, a))
    (ht : Column.alpEncodes t = true) (hw : t.width = some w) (hm : ms.size = ns.size) (hp : ps.size = ns.size)
    (ha : as.size = ns.size) {c : USize} (hc : c.toNat = (ns.toList.map USize.toNat).sum) :
    Enc.WF t c (.alp m p a) := by
  suffices H : Enc.WF t c (.alp (concatALP w.toUSize (countBytes ns) ms ps as).1
      (concatALP w.toUSize (countBytes ns) ms ps as).2.1 (concatALP w.toUSize (countBytes ns) ms ps as).2.2) by
    rw [heq] at H; exact H
  obtain ⟨h48, h0⟩ := alp_width ht hw
  have hw8 : w ≤ 8 := by rw [← h48]; split <;> omega
  have hwu : w.toUSize.toNat = w := toUSize_toNat (lt_usize (by omega))
  have h4' : USize.toNat 4 = 4 := toUSize_toNat (k := 4) (lt_usize (by decide))
  have h8' : USize.toNat 8 = 8 := toUSize_toNat (k := 8) (lt_usize (by decide))
  have h4 : (w.toUSize == 4) = (w == 4) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← USize.toNat_inj, hwu, h4']
  have hW : (if (w == 4) = true then (4 : USize) else 8).toNat = w := by
    cases hc : (w == 4) <;> simp only [hc, Bool.false_eq_true, if_false, if_true] at h48 ⊢ <;> omega
  have hl : ((List.range ns.size).map fun k => w * ((Column.bitsAt (countBytes ns) (8 * k) 8).toNat.toUSize).toNat) =
      ns.toList.map (fun x => x.toNat * w) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, countBytes_get ns i h1, USize.toNat_toUInt64,
      toNat_toUSize, Array.getElem_toList]
    exact Nat.mul_comm _ _
  unfold concatALP
  rw [h4]
  refine alpEncodeAt_wf _ ht (by rw [h48]; exact hw) _ ?_
  rw [hc, h48, concatBytes_size]
  simp only [Array.toList_map, Array.toList_range, List.map_map, Function.comp_def,
    alpDecode_size _ (by rw [hW]; exact hw8), hW, hm, hp, ha, Nat.min_self, countBytes_size,
    Nat.mul_div_cancel_left _ (show 0 < 8 by decide)]
  rw [hl, sum_map_mul, Nat.mul_div_cancel _ h0]
  exact Nat.le_refl _

/-- `razeColumn` answers a well-formed vector on well-formed parts whose counts sum below `USize.size`. -/
theorem razeColumn_wf {t : QAtomicType} {cs : Array (USize × Enc)}
    (h : ∀ c ∈ cs, Enc.WF t c.1 c.2) (hN : cs.foldl (fun s c => s + c.1.toNat) 0 < USize.size)
    {v : QValue} (hv : razeColumn t cs = some v) : ∃ n e, v = .vector t n e none ∧ Enc.WF t n e := by
  have hdense : ∀ {w}, t.width = some w → t ≠ .boolean → ∀ {ps},
      cs.mapM (fun (n, e) => Enc.bytesOf t n e) = some ps → ∀ {c : USize},
      c.toNat = cs.foldl (fun s c => s + c.1.toNat) 0 → Enc.WF t c (.bytes (concatBytes ps)) := by
    intro w hw hb ps hps c hc
    have hd := dense_parts h hw hb (by simpa using hps)
    exact concatBytes_wf hb hw hd.1 hd.2 hc
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases t
  case boolean =>
    dsimp only at hv
    split at hv
    · obtain ⟨hc, hv⟩ := needSize_some hv
      cases hv; exact ⟨_, _, rfl, concatBits_wf _ (toUSize_toNat hc)⟩
    · cases hv
  case symbol =>
    dsimp only at hv
    split at hv
    · rename_i ps hps
      cases hv
      have hs := mapM_key (key' := fun p : ByteArray × Array Nat => decide (SymsWF p.1 p.2))
        (key := fun _ : USize × Enc => true) (fun c hc x hx => by
          rcases c with ⟨k, e⟩
          have hw := h _ hc
          cases e <;> first | (cases hx; done) | (cases hx; simp only [Enc.WF] at hw; exact decide_eq_true hw.2.1)) hps
      have hs' := mapM_key (key' := fun p : ByteArray × Array Nat =>
          decide (∀ i < p.2.size - 1, (Column.symKey p.1 p.2 i).IsValidUTF8))
        (key := fun _ : USize × Enc => true) (fun c hc x hx => by
          rcases c with ⟨k, e⟩
          have hw := h _ hc
          cases e <;> first | (cases hx; done) |
            (cases hx; simp only [Enc.WF] at hw; exact decide_eq_true fun i hi => hw.2.2 i (by simp only at hi; omega))) hps
      refine concatSyms_wf ps (fun x hx => ?_) (fun x hx => ?_) ?_
      · have hm := Array.mem_map_of_mem (f := fun p : ByteArray × Array Nat => decide (SymsWF p.1 p.2)) hx
        rw [hs] at hm
        obtain ⟨_, _, he⟩ := Array.mem_map.1 hm
        exact of_decide_eq_true he.symm
      · have hm := Array.mem_map_of_mem (f := fun p : ByteArray × Array Nat =>
          decide (∀ i < p.2.size - 1, (Column.symKey p.1 p.2 i).IsValidUTF8)) hx
        rw [hs'] at hm
        obtain ⟨_, _, he⟩ := Array.mem_map.1 hm
        exact of_decide_eq_true he.symm
      have hk := mapM_key (key' := fun p : ByteArray × Array Nat => p.2.size - 1)
        (key := fun c : USize × Enc => c.1.toNat) (fun c hc x hx => by
          rcases c with ⟨k, e⟩
          have hw := h _ hc
          cases e <;> first | (cases hx; done) | (cases hx; simp only [Enc.WF] at hw; simp only; omega)) hps
      rw [hk]; simpa [foldl_toNat, Function.comp_def] using hN
    · split at hv
      · rename_i ps hps
        cases hv
        refine concatEnum_wf ps ?_ ?_ ?_
        rotate_left
        rotate_left
        · have hP := mapM_key (key' := fun p : USize × ByteArray × Array Nat × ByteArray => decide (SymsWF p.2.1 p.2.2.1 ∧
              ∀ i < p.2.2.1.size - 1, (Column.symKey p.2.1 p.2.2.1 i).IsValidUTF8))
            (key := fun _ : USize × Enc => true) (fun c hc x hx => by
              rcases c with ⟨k, e⟩
              have hw := h _ hc
              cases e with
              | syms b o =>
                simp only [Column.intern] at hx
                cases hx
                simp only [Enc.WF] at hw
                exact decide_eq_true ⟨Verify.symsWF_internSyms b o,
                  utf8_distinctSyms b o fun i hi => hw.2.2 i (by omega)⟩
              | enum d o ids =>
                simp only [Column.intern] at hx
                cases hx
                simp only [Enc.WF] at hw
                exact decide_eq_true ⟨hw.2.1, hw.2.2.2.2⟩
              | _ => simp [Column.intern] at hx) hps
          intro p hp
          have hm := Array.mem_map_of_mem (f := fun p : USize × ByteArray × Array Nat × ByteArray =>
            decide (SymsWF p.2.1 p.2.2.1 ∧
              ∀ i < p.2.2.1.size - 1, (Column.symKey p.2.1 p.2.2.1 i).IsValidUTF8)) hp
          rw [hP] at hm
          obtain ⟨_, _, he⟩ := Array.mem_map.1 hm
          exact of_decide_eq_true he.symm
        rotate_right
        · have hP := mapM_key (key' := fun p : USize × ByteArray × Array Nat × ByteArray => decide (0 < p.2.2.1.size ∧
              ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1))
            (key := fun _ : USize × Enc => true) (fun c hc x hx => by
              rcases c with ⟨k, e⟩
              have hw := h _ hc
              cases e with
              | syms b o =>
                simp only [Column.intern] at hx
                cases hx
                simp only [Enc.WF] at hw
                exact decide_eq_true ⟨(Verify.symsWF_internSyms b o).pos, fun i hi => internSyms_lt b o (by simp only at hi; omega)⟩
              | enum d o ids =>
                simp only [Column.intern] at hx
                cases hx
                simp only [Enc.WF] at hw
                exact decide_eq_true ⟨hw.2.1.pos, hw.2.2.1⟩
              | _ => simp [Column.intern] at hx) hps
          intro p hp
          have hm := Array.mem_map_of_mem (f := fun p : USize × ByteArray × Array Nat × ByteArray =>
            decide (0 < p.2.2.1.size ∧
              ∀ i < p.1.toNat, Column.idAt p.2.2.2 (Column.idWidth p.2.2.1) i < p.2.2.1.size - 1)) hp
          rw [hP] at hm
          obtain ⟨_, _, he⟩ := Array.mem_map.1 hm
          exact of_decide_eq_true he.symm
        have hk := mapM_key (key' := fun p : USize × ByteArray × Array Nat × ByteArray => p.1)
          (key := fun c : USize × Enc => c.1) (fun c _ x hx => by
            rcases c with ⟨k, e⟩
            try dsimp only at hx
            split at hx <;> first | (cases hx; rfl) | cases hx) hps
        rw [foldl_toNat, hk, ← foldl_toNat]; exact hN
      · cases hv
  case general =>
    have hE : encodedParts .general cs = none := by
      unfold encodedParts; simp [Column.alpEncodes, Column.encodes]
    simp [hE, QAtomicType.width] at hv
  all_goals
    simp only [QAtomicType.width] at hv
    split at hv
    · obtain ⟨rfl, rfl, rfl, hms, hps, has, hen⟩ := encodedParts_spec ‹encodedParts _ _ = some _›
      try (simp [Column.encodes, Column.alpEncodes] at hen; done)
      all_goals
        injections; subst_vars
        rcases ite_some hv with hv | hv
        · split at hv
          · rename_i hmp
            obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
            cases hv; exact ⟨_, _, rfl, hdense rfl (by decide) hmp (toUSize_toNat hc)⟩
          · cases hv
        · obtain ⟨hc, hv⟩ := needSize_some hv
          obtain ⟨-, hv⟩ := need_some hv
          simp only [Column.alpEncodes, Bool.false_eq_true, if_false, if_true] at hv
          cases hv
          first
            | exact ⟨_, _, rfl, answer_wf (wf_foR rfl (by decide) (by decide) (by
                rw [toUSize_toNat hc]; exact concatFoR_nblk rfl (by decide) (by decide) hms hps))⟩
            | exact ⟨_, _, rfl, answer_wf (concatALP_wf rfl rfl rfl hms hps has (toUSize_toNat hc))⟩
    · split at hv
      · rename_i hmp
        obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
        cases hv; exact ⟨_, _, rfl, hdense rfl (by decide) hmp (toUSize_toNat hc)⟩
      · cases hv

/-- `razeColumn` claims on well-formed parts of a type other than `general` whose counts sum below
    `USize.size`, the count its `needSize` checks. -/
theorem razeColumn_isSome {t : QAtomicType} {cs : Array (USize × Enc)} (hne : cs.size ≠ 0)
    (hg : t ≠ .general) (h : ∀ c ∈ cs, Enc.WF t c.1 c.2)
    (hN : cs.foldl (fun s c => s + c.1.toNat) 0 < USize.size) :
    (razeColumn t cs).isSome := by
  have hdense : ∀ w, t.width = some w → t ≠ .boolean →
      ∃ ps, cs.mapM (fun c => Enc.bytesOf t c.1 c.2) = some ps ∧ ps.size = cs.size ∧
        ∀ i (hi : i < cs.size) (hp : i < ps.size), ps[i].size = cs[i].1.toNat * w := by
    intro w hw hb
    have hm := mapM_some (f := fun c : USize × Enc => Enc.bytesOf t c.1 c.2)
      (fun c => (Enc.bytesOf t c.1 c.2).getD .empty) (cs := cs) fun c hc => by
        obtain ⟨b, hb', -⟩ := bytesOf_size hb hw (h c hc); simp [hb']
    exact ⟨_, hm, dense_parts h hw hb hm⟩
  have hN' := hN
  rw [foldl_toNat] at hN'
  unfold razeColumn
  rw [if_neg (by simpa [Array.isEmpty] using hne)]
  cases t
  case general => exact absurd rfl hg
  case boolean =>
    rw [mapM_some (fun c => (c.1, match c.2 with | .bits b => b | _ => .empty)) fun c hc => ?_]
    · dsimp only; rw [Array.foldl_map, needSize_fits hN]; rfl
    · have := h c hc; rcases c with ⟨n, e⟩; cases e <;> simp [Enc.WF] at this ⊢
  case symbol =>
    dsimp only
    split
    · rfl
    · rw [mapM_some (fun c => match Column.intern c.2 with
          | .enum d o i => (c.1, d, o, i) | _ => (c.1, .empty, #[], .empty)) fun c hc => ?_]
      · rfl
      · have := h c hc; rcases c with ⟨n, e⟩
        cases e <;> simp [Enc.WF, QAtomicType.width, Column.intern] at this ⊢
  all_goals
    obtain ⟨ps, hps, hsz, hps'⟩ := hdense _ rfl (by decide)
    dsimp only
    repeat' split
    all_goals first
      | rfl
      | (rw [needSize_fits hN]; rfl)
      | (obtain ⟨rfl, rfl, rfl, hms, -, -, -⟩ := encodedParts_spec ‹encodedParts _ _ = some _›
         rw [needSize_fits hN']
         simp [need, hms])
      | (exfalso; rename_i hx; exact hx _ _ rfl hps)
      | (exfalso; rename_i hw hm hany
         rw [hps] at hm; injection hm with hm; subst hm
         simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
         rw [Array.any_eq_true] at hany; obtain ⟨i, hi, hc⟩ := hany
         simp only [Array.size_zip] at hi
         simp only [Array.getElem_zip, decide_eq_true_eq] at hc
         rw [hps' i (by omega) (by omega)] at hc; omega)

/-- **`razeColumn` counts its answer as the sum of its parts' counts**, on well-formed parts whose
    counts sum below `USize.size`: past it a symbol answer's count is `needSize`'s model. -/
theorem razeColumn_count {t : QAtomicType} {cs : Array (USize × Enc)}
    (h : ∀ c ∈ cs, Enc.WF t c.1 c.2) (hN : cs.foldl (fun s c => s + c.1.toNat) 0 < USize.size)
    {n : USize} {e : Enc} (hv : razeColumn t cs = some (.vector t n e none)) :
    n.toNat = cs.foldl (fun s c => s + c.1.toNat) 0 := by
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases t
  case boolean =>
    dsimp only at hv
    split at hv
    · rename_i ps hps
      obtain ⟨hc, hv⟩ := needSize_some hv
      cases hv
      have hk := mapM_key (key' := fun p : USize × ByteArray => p.1) (key := fun c : USize × Enc => c.1)
        (fun c _ x hx => by rcases c with ⟨k, e'⟩; cases e' <;> simp at hx; subst hx; rfl) hps
      rw [toUSize_toNat hc, foldl_toNat, foldl_toNat, hk]
    · cases hv
  case symbol =>
    dsimp only at hv
    split at hv
    · rename_i ps hps
      have hk := mapM_key (key' := fun p : ByteArray × Array Nat => p.2.size - 1)
        (key := fun c : USize × Enc => c.1.toNat) (fun c hc x hx => by
          rcases c with ⟨k, e⟩
          have hw := h _ hc
          cases e <;> first | (cases hx; done) | (cases hx; simp only [Enc.WF] at hw; simp only; omega)) hps
      have hS : (ps.toList.map fun p => p.2.size - 1).sum = cs.foldl (fun s c => s + c.1.toNat) 0 := by
        rw [← Array.toList_map, hk]; simp [foldl_toNat, Function.comp_def]
      simp only [concatSyms] at hv; cases hv
      rw [← hS, ← Array.foldl_toList, foldl_sum (fun p : ByteArray × Array Nat => p.2.size) _
        (fun p => p.2.size - 1) (fun s a => by rcases s with ⟨blob, offs⟩; rcases a with ⟨b, o⟩; simp)]
      generalize (ps.toList.map fun p => p.2.size - 1).sum = S at hS ⊢
      have h1 : (#[(0 : Nat)] : Array Nat).size + S - 1 = S := by simp
      have hS' : S < USize.size := by rw [hS]; exact hN
      rw [h1, needSize_fits hS']; exact toUSize_toNat hS'
    · split at hv
      · rename_i ps hps
        have hk := mapM_key (key' := fun p : USize × ByteArray × Array Nat × ByteArray => p.1)
          (key := fun c : USize × Enc => c.1) (fun c _ x hx => by
            rcases c with ⟨k, e⟩
            try dsimp only at hx
            split at hx <;> first | (cases hx; rfl) | cases hx) hps
        simp only [concatEnum] at hv; cases hv
        generalize hq : Array.mapIdx _ ps = qs
        have hmap : qs.map (·.1) = ps.map (·.1) := by
          rw [← hq]
          apply Array.ext (by simp)
          intro i h1 h2
          simp only [Array.getElem_map, Array.getElem_mapIdx]
          repeat' split
          all_goals simp_all
        have hS : qs.foldl (fun s p => s + p.1.toNat) 0 = cs.foldl (fun s c => s + c.1.toNat) 0 := by
          rw [foldl_toNat, foldl_toNat, hmap, hk]
        rw [hS, needSize_fits hN]; exact toUSize_toNat hN
      · cases hv
  case general =>
    have hE : encodedParts .general cs = none := by
      unfold encodedParts; simp [Column.alpEncodes, Column.encodes]
    simp [hE, QAtomicType.width] at hv
  all_goals
    simp only [QAtomicType.width] at hv
    split at hv
    · obtain ⟨rfl, rfl, rfl, hms, hps, has, hen⟩ := encodedParts_spec ‹encodedParts _ _ = some _›
      try (simp [Column.encodes, Column.alpEncodes] at hen; done)
      all_goals
        injections; subst_vars
        rcases ite_some hv with hv | hv
        · split at hv
          · obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
            cases hv; exact toUSize_toNat hc
          · cases hv
        · obtain ⟨hc, hv⟩ := needSize_some hv
          obtain ⟨-, hv⟩ := need_some hv
          simp only [Column.alpEncodes, Bool.false_eq_true, if_false, if_true] at hv
          cases hv
          rw [toUSize_toNat hc, foldl_toNat]
    · split at hv
      · obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
        cases hv; exact toUSize_toNat hc
      · cases hv

end LeetQ.Rel.KernelWF
