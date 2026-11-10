/-
  The element-wise kernels `dyadColumn`, `monColumn`, `bitwPayload`, `lowZeroPayload` and the one-atom
  payload `Enc.ofAtoms t #[a]`: when they answer, read off their Lean bodies, and that what they answer
  is a well-formed payload.
-/
import QLean.Kernel.Elementwise
import QLean.Eval.Dyad
import QLean.Dep.Val
import LeetQ.Rel.KernelWF.Raze

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel LeetQ.Rel

/-! ## The one-atom payload -/

/-- One atom of `t` is a well-formed one-element payload. -/
theorem ofAtoms_singleton_wf {t : QAtomicType} (ht : t ≠ .general) (a : Dep.Carrier t) :
    ∃ e, Enc.ofAtoms t #[Dep.Carrier.atom a ht] ht = some e ∧ Enc.WF t 1 e := by
  have hall : ∀ x ∈ #[Dep.Carrier.atom a ht], x.type = t := by simp
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (Column.ofAtoms_isSome ht hall)
  exact ⟨e, he, by simpa using Column.ofAtoms_WF hall he⟩

/-! ## `bitwPayload` and `lowZeroPayload` -/

/-- `Ew.bitw` answers `n` longs. -/
theorem bitw_size (op : UInt8) (a b : ByteArray) (n : USize) : (Kernel.Ew.bitw op a b n).size = n.toNat * 8 := by
  simp only [Kernel.Ew.bitw]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

/-- `Ew.lowZero` answers `n` bits. -/
theorem lowZero_size (a atom : ByteArray) (n : USize) : (Kernel.Ew.lowZero a atom n).size = (n.toNat + 7) / 8 := by
  simp only [Kernel.Ew.lowZero]
  rw [foldl_size ByteArray.size _ 1 (fun _ _ => by simp only [ByteArray.size, ByteArray.push, Array.size_push])]
  simp

private theorem toUSize_toNat {n : Nat} (hn : n < USize.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt hn

/-- `bitwPayload` answers on every pair of well-formed long payloads. -/
theorem bitwPayload_isSome {op : UInt8} {n : Nat} {ea eb : Enc} (ha : Enc.WF .long n ea)
    (hb : Enc.WF .long n eb) : (bitwPayload op n ea eb).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome (by decide) rfl ha)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome (by decide) rfl hb)
  simp [bitwPayload, hx, hy]

/-- What `bitwPayload` answers is `n` longs, when `n` fits a `USize` (the count the kernel is handed). -/
theorem bitwPayload_wf {op : UInt8} {n : Nat} {ea eb e : Enc} (hn : n < USize.size)
    (h : bitwPayload op n ea eb = some e) : Enc.WF .long n e := by
  cases hx : Enc.bytesOf .long n ea <;> cases hy : Enc.bytesOf .long n eb <;>
    simp [bitwPayload, hx, hy] at h
  subst h
  exact wf_bytes (w := 8) (by decide) rfl (by rw [bitw_size, toUSize_toNat hn])

/-- `lowZeroPayload` answers on every well-formed long payload. -/
theorem lowZeroPayload_isSome {n : Nat} {e : Enc} {m : UInt64} (hw : Enc.WF .long n e) :
    (lowZeroPayload n e m).isSome := by
  unfold lowZeroPayload
  split
  · rfl
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome (by decide) rfl hw); simp [hx]

/-- What `lowZeroPayload` answers is `n` bits, when `n` fits a `USize`. -/
theorem lowZeroPayload_wf {n : Nat} {e r : Enc} {m : UInt64} (hn : n < USize.size)
    (h : lowZeroPayload n e m = some r) : Enc.WF .boolean n r := by
  unfold lowZeroPayload at h
  split at h
  · cases h; simp only [Enc.WF, Kernel.Ew.foRLowZero, lowZero_size, toUSize_toNat hn]
  · cases hx : Enc.bytesOf .long n e <;> simp [hx] at h
    subst h; simp only [Enc.WF, lowZero_size, toUSize_toNat hn]

/-! ## `dyadColumn` -/

/-- The evaluator's element-wise type and the kernel's are one rule. -/
theorem ewType_eq_resultType (v : Prim.Dyadic) (t u : QAtomicType) : Eval.ewType v t u = resultType v t u := by
  cases v <;> rfl

/-- The class a type with one is read at has the type's own width, except `boolean`'s bitmap. -/
theorem width_clsOf {t : QAtomicType} {src : UInt8} (hc : clsOf t = some src) (hb : t ≠ .boolean) :
    t.width = some (Kernel.Ew.width src) := by
  cases t <;> simp_all [clsOf, QAtomicType.width] <;> subst hc <;> decide

/-- A well-formed payload of a type with a class, other than `boolean`, is dense, `foR`, or an ALP
    blob whose width agrees with the class. -/
theorem wf_dense {t : QAtomicType} {src : UInt8} {m : Nat} {e : Enc} (hc : clsOf t = some src)
    (hbo : t ≠ .boolean) (hw : Enc.WF t m e) :
    (∃ x, e = .bytes x) ∨ (∃ md p, e = .foR md p) ∨
      (∃ md p a, e = .alp md p a ∧ Column.alpF32 a = (src == Kernel.Ew.f32)) := by
  cases e with
  | bytes x => exact .inl ⟨x, rfl⟩
  | foR md p => exact .inr (.inl ⟨md, p, rfl⟩)
  | alp md p a =>
    refine .inr (.inr ⟨md, p, a, rfl, ?_⟩)
    cases t <;> simp_all [clsOf, Enc.WF, QAtomicType.width, Kernel.Ew.f64, Kernel.Ew.f32, Kernel.Ew.i64,
      Kernel.Ew.i32, Kernel.Ew.u8, Kernel.Ew.i16, Kernel.Ew.bits]
    all_goals (subst hc; decide)
  | _ => exfalso; cases t <;> simp_all [clsOf, Enc.WF]

/-- `operandSource` brings every well-formed operand of a type with a class to any class, except a
    `boolean` bitmap to the bitmap class itself (which `valPayload` serves before it gets here). -/
theorem operandSource_isSome {b : Kernel.Ew.Build} {t : QAtomicType} {m : Nat} {e : Enc} {dst : UInt8}
    {nulIn nulOut : Int64} {n : Nat} {tk : Option UInt8} {src : UInt8} (hc : clsOf t = some src)
    (hw : Enc.WF t m e) (hb : t = .boolean → dst ≠ Kernel.Ew.bits) (htk : tk.isSome → t ≠ .boolean) :
    (operandSource b t m e dst nulIn nulOut n tk).isSome := by
  by_cases hbo : t = .boolean
  · subst hbo
    have hs : src = Kernel.Ew.bits := by simp [clsOf] at hc; exact hc.symm
    have htk' : tk = none := by cases tk <;> simp_all
    subst hs htk'
    cases e <;> simp [Enc.WF] at hw
    have hd := hb rfl
    simp [operandSource, clsOf, operandAt, promotable, Ne.symm hd]
    repeat' split
    all_goals rfl
  · have hwd := width_clsOf hc hbo
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome hbo (by simp [hwd]) hw)
    unfold operandSource
    simp only [hc, Option.bind_eq_bind, Option.bind_some]
    split
    · cases tk
      · simp only [operandAt, hc, Option.bind_eq_bind, Option.bind_some]
        split
        · simp [hx]
        · rcases wf_dense hc hbo hw with ⟨y, rfl⟩ | ⟨md, p, rfl⟩ | ⟨md, p, a, rfl, -⟩ <;> simp [hx]
      · simp [hx]
    · rcases wf_dense hc hbo hw with ⟨y, rfl⟩ | ⟨md, p, rfl⟩ | ⟨md, p, a, rfl, hal⟩ <;>
        cases tk <;> simp [hwd, *] <;> (repeat' split) <;> rfl
