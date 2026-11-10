/-
  The comparison half of `dyadColumn`'s well-formedness: the branch a comparison verb takes and the
  `guid` branch (`=`, `<>`, `^` on two guid operands) answer `n` well-formed elements of the type
  `ewType` names.
-/
import LeetQ.Rel.KernelWF.Dyad

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel LeetQ.Rel

/-! ## A comparison answers a boolean -/

/-- Every verb the comparison engine answers is typed `boolean` by the evaluator's rule, at every pair it
    types at all. -/
theorem ewType_cmp {v : Prim.Dyadic} {t u rt : QAtomicType} (hc : (cmpOp v).isSome)
    (h : Eval.ewType v t u = some rt) : rt = .boolean := by
  cases v <;> simp [cmpOp] at hc <;>
    (simp only [Eval.ewType, Prim.elementwise] at h; obtain ⟨_, -, rfl⟩ := map_some_inv h; rfl)

/-- `^` on two guids is typed `guid`. -/
theorem ewType_guid_fill {rt : QAtomicType} (h : Eval.ewType .fill .guid .guid = some rt) : rt = .guid := by
  simp only [Eval.ewType, Prim.common, beq_self_eq_true, if_true, Option.some.injEq] at h; exact h.symm

/-! ## The guid kernels' sizes -/

/-- A fold whose step appends `w` bytes at every element of the list it runs over answers `w` bytes per
    element. -/
theorem foldl_size_of_mem {α σ : Type} (sz : σ → Nat) (g : σ → α → σ) (w : Nat) :
    ∀ (l : List α), (∀ acc, ∀ a ∈ l, sz (g acc a) = sz acc + w) →
      ∀ b, sz (l.foldl g b) = sz b + l.length * w
  | [], _, b => by simp
  | a :: l, hg, b => by
    simp only [List.foldl, List.length_cons]
    rw [foldl_size_of_mem sz g w l (fun acc x hx => hg acc x (List.mem_cons_of_mem _ hx)),
      hg _ _ (List.mem_cons_self ..)]
    simp [Nat.succ_mul]; omega

/-- `guidEq` answers `⌈n/8⌉` bytes. -/
theorem guidEq_size (a b : ByteArray) (atom ne : Bool) (n : USize) :
    (guidEq a b atom ne n).size = (n.toNat + 7) / 8 := by
  simp [guidEq, Column.packBits_size]

/-- `guidFill` answers sixteen bytes an element when `b` holds `n` guids and `a` holds every guid it reads:
    its first under `atom`, its `n` otherwise. -/
theorem guidFill_size {a b : ByteArray} {atom : Bool} {n : USize}
    (ha : ∀ i < n.toNat, 16 * (if atom then 0 else i) + 16 ≤ a.size) (hb : 16 * n.toNat ≤ b.size) :
    (guidFill a b atom n).size = n.toNat * 16 := by
  simp only [guidFill]
  rw [foldl_size_of_mem ByteArray.size _ 16 _ (fun acc i hi => by
    have hi' : i < n.toNat := List.mem_range.1 hi
    have := ha i hi'
    split <;> simp [ByteArray.size_append, ByteArray.size_extract] <;> omega)]
  simp

/-! ## The guid branch -/

/-- A count that fits a `USize` survives the round trip (`Dyad.lean` keeps its copy private). -/
theorem usize_toNat {n : Nat} (hn : n < USize.size) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt hn

/-- What `=` or `<>` answers on two guid payloads is `n` bits. -/
theorem guidEq_wf {x y : ByteArray} {atom ne : Bool} {n : Nat} (hn : n < USize.size) :
    Enc.WF .boolean n (.bits (guidEq x y atom ne n.toUSize)) :=
  bits_wf (by rw [guidEq_size, usize_toNat hn])

/-- A well-formed guid payload is sixteen bytes an element, and `bytesOf` reads it as they are. -/
theorem guid_bytes {m : Nat} {e : Enc} (hw : Enc.WF .guid m e) :
    ∃ x, e = .bytes x ∧ Enc.bytesOf .guid m e = some x ∧ x.size = m * 16 := by
  cases e <;> simp_all [Enc.WF, Enc.bytesOf, QAtomicType.width]

/-- What `^` answers on two well-formed guid payloads is `n` guids, at `x^y` and `atom^y`; `x^atom`
    `dyadPayload` declines before it gets here. -/
theorem guidFill_wf {shape : UInt8} {na nb n : Nat} {x y : ByteArray} (hn : n < USize.size)
    (hsh : shape = Kernel.Ew.vv ∨ shape = Kernel.Ew.av) (hs : dyadCount shape .guid .guid na nb = some n)
    (hx : x.size = na * 16) (hy : y.size = nb * 16) :
    Enc.WF .guid n (.bytes (guidFill x y (shape == Kernel.Ew.av) n.toUSize)) := by
  have hnn := usize_toNat hn
  refine wf_bytes (w := 16) (by decide) rfl ?_
  rcases hsh with rfl | rfl
  · simp [dyadCount] at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [guidFill_size (fun i hi => by simp [Kernel.Ew.vv, Kernel.Ew.av]; omega) (by omega), hnn]
  · simp [dyadCount, Kernel.Ew.vv, Kernel.Ew.va, Kernel.Ew.av] at hs; obtain ⟨rfl, rfl⟩ := hs
    rw [guidFill_size (fun i hi => by simp; omega) (by omega), hnn]

/-! ## `dyadColumn` on a comparison or a guid pair -/

/-- What `dyadColumn` answers on the comparison branch and on the guid branch is the result type `ewType`
    names and `n` well-formed elements of it, `n` being the count the operands conform at. -/
theorem dyadColumn_cmp_wf {v : Prim.Dyadic} {shape : UInt8} {t u rt : QAtomicType} {na nb n : Nat}
    {a b : Enc} {out : QAtomicType × QValue} (h : Eval.ewType v t u = some rt) (ha : Enc.WF t na a)
    (hb : Enc.WF u nb b) (hs : dyadCount shape t u na nb = some n) (hn : n < USize.size)
    (hsh : shape = Kernel.Ew.vv ∨ shape = Kernel.Ew.va ∨ shape = Kernel.Ew.av)
    (hty : (t = .guid ∧ u = .guid ∧ (v = .eq ∨ v = .ne ∨ v = .fill)) ∨ (cmpOp v).isSome)
    (hd : dyadColumn v shape t u na a nb b = some out) :
    ∃ e, out = (rt, .vector rt n e none) ∧ Enc.WF rt n e := by
  unfold dyadColumn at hd
  rw [← ewType_eq_resultType, h] at hd
  dsimp only at hd
  obtain ⟨q, hq, rfl⟩ := map_some_inv hd
  unfold dyadPayload at hq
  split at hq
  · exact none_some_elim hq
  rename_i hfill
  simp only [hs, Option.bind_eq_bind, Option.bind_some] at hq
  by_cases hg : t = .guid ∧ u = .guid ∧ (v = .eq ∨ v = .ne)
  · obtain ⟨rfl, rfl, hv⟩ := hg
    have hrt := ewType_cmp (by rcases hv with rfl | rfl <;> rfl) h
    subst hrt
    rw [if_pos (by rcases hv with rfl | rfl <;> rfl)] at hq
    obtain ⟨x, -, hxb, -⟩ := guid_bytes ha
    obtain ⟨y, -, hyb, -⟩ := guid_bytes hb
    by_cases hav : shape = Kernel.Ew.av <;> simp [hav, hxb, hyb] at hq <;> subst hq <;>
      exact ⟨_, rfl, guidEq_wf hn⟩
  by_cases hf : t = .guid ∧ u = .guid ∧ v = .fill
  · obtain ⟨rfl, rfl, rfl⟩ := hf
    have hrt := ewType_guid_fill h
    subst hrt
    rw [if_neg (by decide), if_pos (by decide)] at hq
    obtain ⟨x, -, hxb, hx⟩ := guid_bytes ha
    obtain ⟨y, -, hyb, hy⟩ := guid_bytes hb
    simp only [hxb, hyb, Option.bind_some, Option.some.injEq] at hq
    subst hq
    have hsh' : shape = Kernel.Ew.vv ∨ shape = Kernel.Ew.av := by
      rcases hsh with h1 | h1 | h1
      · exact .inl h1
      · subst h1; simp at hfill
      · exact .inr h1
    exact ⟨_, rfl, guidFill_wf hn hsh' hs hx hy⟩
  have hc : (cmpOp v).isSome := by
    rcases hty with ⟨h1, h2, h3 | h3 | h3⟩ | hc
    · exact absurd ⟨h1, h2, .inl h3⟩ hg
    · exact absurd ⟨h1, h2, .inr h3⟩ hg
    · exact absurd ⟨h1, h2, h3⟩ hf
    · exact hc
  have hrt := ewType_cmp hc h
  subst hrt
  rw [if_neg (by
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
        rintro ⟨⟨h1, h2⟩, h3 | h3⟩
        · exact hg ⟨h1, h2, .inl h3⟩
        · exact hg ⟨h1, h2, .inr h3⟩),
    if_neg (by
        simp only [Bool.and_eq_true, beq_iff_eq]
        rintro ⟨⟨h1, h2⟩, h3⟩
        exact hf ⟨h1, h2, h3⟩),
    if_pos hc] at hq
  obtain ⟨e, he, rfl⟩ := map_some_inv hq
  exact ⟨e, rfl, cmpPayload_wf hn he⟩

end LeetQ.Rel.KernelWF
