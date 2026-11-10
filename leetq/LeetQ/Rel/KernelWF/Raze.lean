/-
  Well-formedness of the payloads qlean's kernels answer, read off their Lean bodies, in the form
  `Arr.ofPart`/`ofCols` take (`Enc.WF t n e`), and the `isSome` facts that make `codes`/`arrDense`
  total. Gathering kernels (`gatherColumn`, `sliceColumn`, `bytesOf`, `longBytes`, `gens`) are in
  `KernelWF/Gather`.
-/
import QLean.Kernel.Structural
import QLean.Kernel.Sort
import QLean.Kernel.Reduce
import QLean.Kernel.Elementwise
import QLean.Verify.Group

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel

/-! ## Sizes of the folds the kernels are written as -/

/-- A fold that appends `w` bytes a step answers `w` bytes per element. -/
private theorem foldl_size {α σ : Type} (sz : σ → Nat) (g : σ → α → σ) (w : Nat)
    (hg : ∀ acc a, sz (g acc a) = sz acc + w) :
    ∀ (l : List α) (b : σ), sz (l.foldl g b) = sz b + l.length * w
  | [], b => by simp
  | a :: l, b => by
    simp only [List.foldl, List.length_cons]; rw [foldl_size sz g w hg l, hg]; simp [Nat.succ_mul]; omega

/-- A dense payload of `n` elements of a type with a width, other than boolean, is well formed. -/
theorem wf_bytes {t : QAtomicType} {w n : Nat} {b : ByteArray} (hb : t ≠ .boolean) (hw : t.width = some w)
    (hs : b.size = n * w) : Enc.WF t n (.bytes b) := by
  cases t <;> simp_all [Enc.WF, QAtomicType.width]

/-! ## `orderKind`: which types have a sort layout -/

/-- `orderKind` has no sort layout exactly at symbol, guid and the general list. -/
theorem orderKind_eq_none {t : QAtomicType} :
    orderKind t = none ↔ t = .symbol ∨ t = .guid ∨ t = .general := by
  cases t <;> simp [orderKind]

/-- A well-formed payload of a type with a width, other than boolean, has a dense layout. -/
private theorem bytesOf_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hb : t ≠ .boolean)
    (hw : t.width.isSome) (h : Enc.WF t n e) : (Enc.bytesOf t n e).isSome := by
  cases t <;> cases e <;> simp_all [Enc.WF, Enc.bytesOf, QAtomicType.width]

/-- `groupIdsColumn` codes every well-formed payload except a general list's. -/
theorem groupIdsColumn_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hg : t ≠ .general)
    (h : Enc.WF t n e) : (groupIdsColumn t n e).isSome := by
  cases t <;> cases e <;> simp_all [Enc.WF, groupIdsColumn, orderKind, Enc.bytesOf, QAtomicType.width]

/-! ## Results of the producing kernels -/

/-- `packOf n f` holds `n` bits. -/
theorem packOf_size (n : Nat) (f : Nat → Bool) : (packOf n f).size = (n + 7) / 8 := by
  simp only [packOf]; rw [foldl_size ByteArray.size _ 1 (fun _ _ => by simp only [ByteArray.size, ByteArray.push, Array.size_push])]; simp

/-- `concatBits` of parts `ps` holds their summed count, as `razeColumn` counts it. -/
theorem concatBits_wf (ps : Array (Nat × ByteArray)) :
    Enc.WF .boolean (ps.foldl (fun s p => s + p.1) 0) (.bits (concatBits (ps.map (·.1)) (ps.map (·.2)))) := by
  simp only [Enc.WF, concatBits, packOf_size]
  congr 2
  rcases ps with ⟨l⟩
  simp only [Array.zip]; simp only [Array.size_flatMap]
  have sum : ∀ (a : Nat) (l : List (Nat × ByteArray)),
      l.foldl (fun s p => s + p.1) a = a + (l.map (·.1)).sum := by
    intro a l; induction l generalizing a with
    | nil => simp
    | cons p l ih => simp [ih]; omega
  simp [sum]

/-- `til n` as `tilLongs`: `n` longs. -/
theorem tilLongs_wf (n : USize) : Enc.WF .long n.toNat (.bytes (tilLongs n)) :=
  wf_bytes (w := 8) (by decide) rfl (by
    simp only [tilLongs]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp)

/-- `Ew.val` answers `n` elements at its class's width. -/
theorem Ew.val_size (op cls shape : UInt8) (nul : Int64) (a b : ByteArray) (n : USize) :
    (Kernel.Ew.val op cls shape nul a b n).size = n.toNat * Kernel.Ew.width cls := by
  simp only [Kernel.Ew.val]; rw [foldl_size ByteArray.size _ _ (fun _ _ => Column.pushBits_size ..)]; simp

/-- `Ew.mon` answers `n` elements at its class's width. -/
theorem Ew.mon_size (op cls : UInt8) (nul : Int64) (x : ByteArray) (n : USize) :
    (Kernel.Ew.mon op cls nul x n).size = n.toNat * Kernel.Ew.width cls := by
  simp only [Kernel.Ew.mon]; rw [foldl_size ByteArray.size _ _ (fun _ _ => Column.pushBits_size ..)]; simp

/-- `Ew.val` at a type whose width is its class's is a well-formed payload of `n` elements. -/
theorem Ew.val_wf {t : QAtomicType} {op cls shape : UInt8} {nul : Int64} {a b : ByteArray} {n : USize}
    (hb : t ≠ .boolean) (hw : t.width = some (Kernel.Ew.width cls)) :
    Enc.WF t n.toNat (.bytes (Kernel.Ew.val op cls shape nul a b n)) :=
  wf_bytes hb hw (Ew.val_size ..)

/-- `Ew.mon` at a type whose width is its class's is a well-formed payload of `n` elements. -/
theorem Ew.mon_wf {t : QAtomicType} {op cls : UInt8} {nul : Int64} {x : ByteArray} {n : USize}
    (hb : t ≠ .boolean) (hw : t.width = some (Kernel.Ew.width cls)) :
    Enc.WF t n.toNat (.bytes (Kernel.Ew.mon op cls nul x n)) :=
  wf_bytes hb hw (Ew.mon_size ..)

/-- `overGroups` over `ng` groups answers `2·ng` longs: the folds, then the live counts. -/
theorem overGroups_wf (op : Coc.Over) (cls : UInt8) (nul : Int64) (ng w : USize) (n : Nat) (gid b : ByteArray) :
    Enc.WF .long (2 * ng.toNat) (.bytes (overGroups op cls nul ng w n gid b)) :=
  wf_bytes (w := 8) (by decide) rfl (by rw [(Verify.overGroups_spec op cls nul ng w n gid b).1]; omega)

/-- `rankSlices` answers one long per slice of `o`, or nothing where `o` is not a run of in-range
    ascending offsets from `0`. -/
theorem rankSlices_size (w : USize) (v o : ByteArray) :
    (Order.rankSlices w v o).size = 8 * (o.size / 8 - 1) ∨ Order.rankSlices w v o = .empty := by
  simp only [Order.rankSlices]
  split
  · exact .inr rfl
  · left
    rw [← Array.foldl_toList]
    refine Eq.trans (foldl_size (fun p : ByteArray × _ => p.1.size) _ 8 ?_ _ _) ?_
    · intro acc j; rcases acc with ⟨ids, seen⟩; simp only; split <;> simp [Column.pushBits_size]
    · simp; omega

end LeetQ.Rel.KernelWF
