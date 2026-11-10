/-
  The value half of `dyadColumn`'s well-formedness: what the branch a value verb takes (`valOp v`
  answers) answers is `n` well-formed elements of the result type, at every operand encoding — the
  encoded path (`foRValPayload`), the bitmap path (`Ew.bit`) and the promoting path (`zipPass`, which
  reads dense, `.foR` and ALP operands alike).
-/
import LeetQ.Rel.KernelWF.Dyad

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel LeetQ.Rel

private theorem toUSize_toNat' {n : Nat} (hn : n < USize.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt hn

/-! ## The counts the encoded pairs carry -/

/-- `foRPairVV` hands on the count `dyadCount` decided. -/
theorem foRPairVV_count {cls shape : UInt8} {t u : QAtomicType} {na nb n m : Nat} {ea eb : Enc}
    {ma pa mb pb : ByteArray} (hs : dyadCount shape t u na nb = some n)
    (h : foRPairVV cls shape t na ea nb eb = some (m, ma, pa, mb, pb)) : m = n := by
  unfold foRPairVV at h; unfold dyadCount at hs
  repeat' split at h
  all_goals first
    | exact none_some_elim h
    | (cases h; simp_all)

/-- `foRPair` hands on the count `dyadCount` decided: the vector's, on whichever side it stands. -/
theorem foRPair_count {cls shape : UInt8} {t u : QAtomicType} {na nb n m : Nat} {ea eb : Enc}
    {md pk : ByteArray} {k : UInt64} (hs : dyadCount shape t u na nb = some n)
    (h : foRPair cls shape t na ea nb eb = some (m, md, pk, k)) : m = n := by
  unfold foRPair at h; unfold dyadCount at hs
  by_cases hvv : shape = Kernel.Ew.vv
  · subst hvv; simp at h
  by_cases hva : shape = Kernel.Ew.va
  · subst hva
    simp only [show (Kernel.Ew.va == Kernel.Ew.vv) = false by decide, beq_self_eq_true, if_true,
      Bool.false_eq_true, if_false, Bool.false_or] at hs h
    split at hs <;> simp at hs
    split at h; · exact none_some_elim h
    split at h <;> try exact none_some_elim h
    obtain ⟨_, -, h⟩ := bind_some_inv h
    cases h; exact hs
  · simp only [beq_iff_eq, hvv, hva, if_false] at hs h
    split at hs <;> simp at hs
    split at h; · exact none_some_elim h
    split at h <;> try exact none_some_elim h
    obtain ⟨_, -, h⟩ := bind_some_inv h
    cases h; exact hs

/-! ## Re-encoding at eight bytes covers the count -/

theorem width_i64 : Kernel.Ew.width Kernel.Ew.i64 = 8 := by decide

/-- A dense `long` payload of `n` elements, re-encoded at width 8, has blocks for all `n`. -/
theorem encode8_cover {n : USize} {x : ByteArray} (hx : x.size = n.toNat * 8) :
    n.toNat ≤ Column.blk * Column.nblk (Kernel.Coc.encode 8 x).1 := by
  have he : Column.nblk (Kernel.Coc.encode 8 x).1 = (x.size / 8 + Column.blk - 1) / Column.blk :=
    Verify.nblk_encode 8 (by decide) (by decide) x
  rw [he, hx, Nat.mul_div_cancel _ (by decide)]
  simp only [Column.blk]; omega

/-- An encoding at width 8 that answered `(m, p)` has blocks for all `n` of the payload it encoded. -/
theorem encode8_cover' {n : USize} {x m p : ByteArray} (he : Kernel.Coc.encode 8 x = (m, p))
    (hx : x.size = n.toNat * 8) : n.toNat ≤ Column.blk * Column.nblk m := by
  have := encode8_cover (n := n) hx; rwa [he] at this

/-- What `foRValVV` answers has blocks for all `n`. -/
theorem foRValVV_cover {op : UInt8} {ma pa mb pb m p : ByteArray} {n : USize}
    (h : Kernel.Ew.foRValVV op ma pa mb pb n = some (m, p)) : n.toNat ≤ Column.blk * Column.nblk m := by
  unfold Kernel.Ew.foRValVV at h
  dsimp only at h
  simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
  exact encode8_cover' h.2 (by rw [Ew.val_size, width_i64])

/-- What `foRShift` answers has blocks for all `n`. -/
theorem foRShift_cover {neg : Bool} {k : Int64} {md pk m p : ByteArray} {n : USize}
    (h : Kernel.Ew.foRShift neg k md pk n = some (m, p)) : n.toNat ≤ Column.blk * Column.nblk m := by
  unfold Kernel.Ew.foRShift at h
  dsimp only at h
  simp only [Option.ite_none_left_eq_some, Option.some.injEq] at h
  exact encode8_cover' h.2 (by cases neg <;> simp only [Bool.false_eq_true, if_false, if_true, Ew.val_size, width_i64])

/-- What `foRScale` answers has blocks for all `n`. -/
theorem foRScale_cover {k : Int64} {md pk m p : ByteArray} {n : USize}
    (h : Kernel.Ew.foRScale k md pk n = some (m, p)) : n.toNat ≤ Column.blk * Column.nblk m := by
  unfold Kernel.Ew.foRScale at h
  dsimp only at h
  simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
  exact encode8_cover' h.2 (by rw [Ew.val_size, width_i64])

/-! ## The encoded value path -/

/-- What `foRValPayload` answers is `n` well-formed elements of its result type, `n` the count
    `dyadCount` decided, at every shape and on each of its two answers: re-encoded or dense. -/
theorem foRValPayload_wf {op shape : UInt8} {nul : Int64} {t u rt : QAtomicType} {na nb n : Nat}
    {ea eb r : Enc} (hn : n < USize.size) (hs : dyadCount shape t u na nb = some n) (hb : rt ≠ .boolean)
    (h : foRValPayload op shape nul t rt na ea nb eb = some r) : Enc.WF rt n r := by
  unfold foRValPayload at h
  obtain ⟨cls, hcls, h⟩ := bind_some_inv h
  have hg : rt ≠ .guid := by rintro rfl; simp [clsOf] at hcls
  have hwd := width_clsOf hcls hb
  have hws : rt.width.isSome := by simp [hwd]
  dsimp only at h
  split at h
  · obtain ⟨⟨m, ma, pa, mb, pb⟩, hp, h⟩ := bind_some_inv h
    obtain rfl := foRPairVV_count hs hp
    dsimp only at h
    split at h
    · rename_i mm pp heq
      cases h
      refine answer_wf (wf_foR hws hb hg ?_) hn
      split at heq
      · have := foRValVV_cover heq; rwa [toUSize_toNat' hn] at this
      · exact none_some_elim heq
    · cases h
      exact answer_wf (wf_bytes hb hwd (by simp only [Kernel.Ew.foRVal, Ew.val_size, toUSize_toNat' hn])) hn
  · obtain ⟨⟨m, md, pk, bits⟩, hp, h⟩ := bind_some_inv h
    obtain rfl := foRPair_count hs hp
    dsimp only at h
    split at h
    · rename_i mm pp heq
      cases h
      refine answer_wf (wf_foR hws hb hg ?_) hn
      rw [← toUSize_toNat' hn]
      repeat' split at heq
      all_goals first
        | exact none_some_elim heq
        | exact foRScale_cover heq
        | exact foRShift_cover heq
    · cases h
      refine answer_wf (wf_bytes hb hwd ?_) hn
      simp only [Kernel.Ew.foRValAtom]
      split <;> rw [Ew.val_size, toUSize_toNat' hn]

/-! ## `valPayload` -/

/-- A type whose class is the bitmap's is `boolean`. -/
theorem boolean_of_clsOf_bits {rt : QAtomicType} (h : clsOf rt = some Kernel.Ew.bits) : rt = .boolean := by
  cases rt <;> simp only [clsOf, Option.some.injEq, reduceCtorEq] at h <;> first | rfl | exact absurd h (by decide)

/-- What `valPayload` answers is `n` well-formed elements of its result type, `n` the count
    `dyadCount` decided, at every operand encoding: the bitmap engine for a boolean result, the
    encoded path, and the promoting path behind it. -/
theorem valPayload_wf {v : Prim.Dyadic} {shape : UInt8} {t u rt : QAtomicType} {na nb n : Nat}
    {ea eb r : Enc} (hn : n < USize.size) (hs : dyadCount shape t u na nb = some n)
    (h : valPayload v shape t u rt na ea nb eb n = some r) : Enc.WF rt n r := by
  unfold valPayload at h
  obtain ⟨op, -, h⟩ := bind_some_inv h
  dsimp only at h
  obtain ⟨cls, hcls, h⟩ := bind_some_inv h
  simp only [Option.ite_none_left_eq_some] at h
  obtain ⟨-, h⟩ := h
  by_cases hc : cls = Kernel.Ew.bits
  · subst hc
    obtain rfl := boolean_of_clsOf_bits hcls
    simp only [beq_self_eq_true, if_true] at h
    split at h
    · cases h; exact bits_wf (by rw [bit_size, toUSize_toNat' hn])
    · exact none_some_elim h
  · rw [if_neg (by simpa using hc)] at h
    have hb : rt ≠ .boolean := by
      rintro rfl; simp only [clsOf, Option.some.injEq] at hcls; exact hc hcls.symm
    have hwd := width_clsOf hcls hb
    rcases orElse_eq_some h with h | h
    · simp only [Option.ite_none_right_eq_some] at h
      exact foRValPayload_wf hn hs hb h.2
    · exact zipPass_wf hn (fun b sa sb => payload_wf hb hwd (run_val_size ..)) h

/-! ## `dyadColumn` on a value verb -/

/-- What `dyadColumn` answers on a value verb is the result type `Eval.ewType` gives and `n`
    well-formed elements of it, `n` the count `dyadCount` decided, at every operand encoding and each
    of the three shapes. The `guid` fill is the one value verb served by its own branch, and is
    excluded. -/
theorem dyadColumn_val_wf {v : Prim.Dyadic} {shape : UInt8} {t u rt : QAtomicType} {na nb n : Nat}
    {a b : Enc} {out : QAtomicType × QValue} (hrt : Eval.ewType v t u = some rt) (hv : (valOp v).isSome)
    (hg : ¬(t = .guid ∧ u = .guid ∧ v = .fill)) (hs : dyadCount shape t u na nb = some n)
    (hn : n < USize.size) (h : dyadColumn v shape t u na a nb b = some out) :
    ∃ e, out = (rt, .vector rt n e none) ∧ Enc.WF rt n e := by
  have hr : resultType v t u = some rt := by rw [← ewType_eq_resultType]; exact hrt
  unfold dyadColumn at h
  rw [hr] at h
  simp only at h
  obtain ⟨q, hq, rfl⟩ := map_some_inv h
  clear h
  unfold dyadPayload at hq
  split at hq
  · exact none_some_elim hq
  simp only [hs, Option.bind_eq_bind, Option.bind_some] at hq
  rw [if_neg (by
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
        rintro ⟨-, rfl | rfl⟩ <;> simp [valOp] at hv),
      if_neg (by
        simp only [Bool.and_eq_true, beq_iff_eq]
        rintro ⟨⟨h1, h2⟩, h3⟩
        exact hg ⟨h1, h2, h3⟩),
      if_neg (by simp [cmpOp_none_of_valOp hv])] at hq
  obtain ⟨e, he, rfl⟩ := map_some_inv hq
  exact ⟨e, rfl, valPayload_wf hn hs he⟩

end LeetQ.Rel.KernelWF
