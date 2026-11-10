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
        cases tk <;> simp [*] <;> (repeat' split) <;> rfl

/-- A type `convertible` reads has a class. -/
theorem clsOf_of_convertible {t : QAtomicType} {cls : UInt8} (h : convertible t cls = true) :
    ∃ src, clsOf t = some src := by
  unfold convertible at h; split at h
  · exact ⟨_, ‹_›⟩
  · exact absurd h (by simp)

/-- A boolean operand is never re-counted in a unit. -/
theorem tickIn_boolean (rt : QAtomicType) : tickIn .boolean rt = none := by
  unfold tickIn; split <;> simp [tickCode]

/-- `zipPass` answers on two well-formed operands of types with a class, at any class but the bitmap's. -/
theorem zipPass_isSome {cls : UInt8} {nulIn : QAtomicType → Int64} {nulOut nulOutB : Int64}
    {t u rt : QAtomicType} {na nb n : Nat} {ea eb : Enc} {stage : UInt8 → UInt8 → Kernel.Ew.Stage}
    {ta tb : Option UInt8} {sa sb : UInt8} (hca : clsOf t = some sa) (hcb : clsOf u = some sb)
    (ha : Enc.WF t na ea) (hb : Enc.WF u nb eb) (hcls : cls ≠ Kernel.Ew.bits)
    (hta : ta.isSome → t ≠ .boolean) (htb : tb.isSome → u ≠ .boolean) :
    (zipPass cls nulIn nulOut nulOutB t u rt na ea nb eb n stage ta tb).isSome := by
  obtain ⟨⟨bld, xa⟩, h1⟩ := Option.isSome_iff_exists.1 (operandSource_isSome (b := {}) (dst := cls)
    (nulIn := nulIn t) (nulOut := nulOut) (n := n) (tk := ta) hca ha (fun _ => hcls) hta)
  obtain ⟨⟨bld', xb⟩, h2⟩ := Option.isSome_iff_exists.1 (operandSource_isSome (b := bld) (dst := cls)
    (nulIn := nulIn u) (nulOut := nulOutB) (n := n) (tk := tb) hcb hb (fun _ => hcls) htb)
  simp [zipPass, h1, h2]

/-- A fallback that answers makes `<|>` answer. -/
theorem orElse_isSome {α : Type} (x : Option α) {y : Option α} (hy : y.isSome) : (x <|> y).isSome := by
  cases x
  · exact hy
  · rfl

/-- The conditions `valPayload` tests of the types alone, as it tests them. -/
def ValClaims (v : Prim.Dyadic) (t u rt : QAtomicType) : Prop :=
  (valOp v).isSome ∧ ∃ cls, clsOf rt = some cls ∧ (scales v = true ∨ ticksMeet t u rt = true) ∧
    convertible t cls = true ∧ convertible u cls = true ∧ (cls = Kernel.Ew.bits → t = .boolean ∧ u = .boolean)

/-- `valPayload` answers on well-formed operands whenever its type conditions hold. -/
theorem valPayload_isSome {v : Prim.Dyadic} {shape : UInt8} {t u rt : QAtomicType} {na nb n : Nat}
    {ea eb : Enc} (hv : ValClaims v t u rt) (ha : Enc.WF t na ea) (hb : Enc.WF u nb eb) :
    (valPayload v shape t u rt na ea nb eb n).isSome := by
  obtain ⟨hop, cls, hcls, htick, hct, hcu, hbits⟩ := hv
  obtain ⟨op, hop⟩ := Option.isSome_iff_exists.1 hop
  obtain ⟨sa, hsa⟩ := clsOf_of_convertible hct
  obtain ⟨sb, hsb⟩ := clsOf_of_convertible hcu
  unfold valPayload
  simp only [hop, hcls, hct, hcu, Option.bind_eq_bind, Option.bind_some]
  rw [if_neg (by rcases htick with h | h <;> simp [h])]
  by_cases hc : cls = Kernel.Ew.bits
  · obtain ⟨rfl, rfl⟩ := hbits hc
    cases ea <;> simp [Enc.WF] at ha
    cases eb <;> simp [Enc.WF] at hb
    simp [hc]
  · rw [if_neg (by simpa using hc)]
    have hk : ∀ {s : QAtomicType}, (if scales v = true then tickIn s rt else none).isSome → s ≠ .boolean := by
      intro s h hs; subst hs; split at h <;> simp [tickIn_boolean] at h
    exact orElse_isSome _ (zipPass_isSome hsa hsb ha hb hc hk hk)

/-- The conditions `cmpPayload` tests of the types alone, as it tests them: a symbol pair and a boolean pair
    are served by their own engines, any other pair at the class of the type both widen to. -/
def CmpClaims (v : Prim.Dyadic) (t u : QAtomicType) : Prop :=
  (cmpOp v).isSome ∧ ((t = .symbol ∧ u = .symbol) ∨ (t = .boolean ∧ u = .boolean) ∨
    ∃ ct raw, (if t == u then some t else Prim.common t u) = some ct ∧ ticksMeet t u ct = true ∧
      clsOf ct = some raw ∧
      let cls := if raw == Kernel.Ew.bits || ((clsOf t == some Kernel.Ew.bits || clsOf u == some Kernel.Ew.bits) &&
        (raw == Kernel.Ew.u8 || raw == Kernel.Ew.i16)) then Kernel.Ew.i32 else raw
      convertible t cls = true ∧ convertible u cls = true)

/-- The symbol encodings `cmpPayload` reads against each other: two dense blobs, or two operands that are
    each interned or a single symbol. It declines a dense blob of other than one symbol against an
    interned column. -/
def SymClaims (ea eb : Enc) : Prop :=
  (∃ ba oa bb ob, ea = .syms ba oa ∧ eb = .syms bb ob) ∨ ((symIds ea).isSome ∧ (symIds eb).isSome)

/-- `cmpPayload` answers on well-formed operands whenever its type conditions hold and, at a symbol pair,
    the encodings are ones it reads. -/
theorem cmpPayload_isSome {v : Prim.Dyadic} {shape : UInt8} {t u : QAtomicType} {na nb n : Nat}
    {ea eb : Enc} (hv : CmpClaims v t u) (ha : Enc.WF t na ea) (hb : Enc.WF u nb eb)
    (hsym : t = .symbol → u = .symbol → SymClaims ea eb) :
    (cmpPayload v shape t u na ea nb eb n).isSome := by
  obtain ⟨hop, hty⟩ := hv
  obtain ⟨op, hop⟩ := Option.isSome_iff_exists.1 hop
  unfold cmpPayload
  simp only [hop, Option.bind_eq_bind, Option.bind_some]
  by_cases hs : t = .symbol ∧ u = .symbol
  · obtain ⟨rfl, rfl⟩ := hs
    rcases hsym rfl rfl with ⟨ba, oa, bb, ob, rfl, rfl⟩ | ⟨h1, h2⟩
    · simp
    · obtain ⟨⟨da, doa, ia⟩, hia⟩ := Option.isSome_iff_exists.1 h1
      obtain ⟨⟨db, dob, ib⟩, hib⟩ := Option.isSome_iff_exists.1 h2
      simp only [beq_self_eq_true, Bool.and_self, if_true]
      (repeat' split) <;> (try simp_all) <;> (rename_i h; exact h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl)
  · rw [if_neg (by simpa [Bool.and_eq_true, beq_iff_eq] using hs)]
    rcases hty with h | ⟨rfl, rfl⟩ | ⟨ct, raw, hct, htk, hraw, hcv⟩
    · exact absurd h hs
    · cases ea <;> simp [Enc.WF] at ha
      cases eb <;> simp [Enc.WF] at hb
      rfl
    · obtain ⟨hct', hcu'⟩ := hcv
      obtain ⟨sa, hsa⟩ := clsOf_of_convertible hct'
      obtain ⟨sb, hsb⟩ := clsOf_of_convertible hcu'
      split
      · rfl
      · have hne : (if (raw == Kernel.Ew.bits || ((clsOf t == some Kernel.Ew.bits ||
            clsOf u == some Kernel.Ew.bits) && (raw == Kernel.Ew.u8 || raw == Kernel.Ew.i16))) = true
            then Kernel.Ew.i32 else raw) ≠ Kernel.Ew.bits := by
          split <;> rename_i h <;> simp_all [Kernel.Ew.i32, Kernel.Ew.bits]
        split
        · rename_i htu; simp only [htu, if_true, Option.some.injEq] at hct; subst hct
          rw [if_neg (by simp [htk]), hraw]; simp only [Option.bind_some]; try rw [hraw] at hct' hcu' hne
          rw [if_neg (by rw [hct', hcu']; decide)]
          exact orElse_isSome _ (zipPass_isSome hsa hsb ha hb hne (by simp) (by simp))
        · rename_i htu; simp only [htu, Bool.false_eq_true, if_false] at hct; rw [hct]
          simp only [Option.bind_some]
          rw [if_neg (by simp [htk]), hraw]; simp only [Option.bind_some]; try rw [hraw] at hct' hcu' hne
          rw [if_neg (by rw [hct', hcu']; decide)]
          exact orElse_isSome _ (zipPass_isSome hsa hsb ha hb hne (by simp) (by simp))

/-- A value verb is not a comparison. -/
theorem cmpOp_none_of_valOp {v : Prim.Dyadic} (h : (valOp v).isSome) : cmpOp v = none := by
  cases v <;> simp_all [valOp, cmpOp]

/-- `dyadColumn` answers, for each of the three shapes, on two well-formed operands whose counts conform,
    when the type conditions of the branch that serves the pair hold: `guid` against `guid` under `=`, `<>`
    or `^`; `CmpClaims` for a comparison; `ValClaims` for a value verb. It declines `x^atom` and, at a
    symbol pair, the encodings `SymClaims` excludes. -/
theorem dyadColumn_isSome {v : Prim.Dyadic} {shape : UInt8} {t u rt : QAtomicType} {na nb n : Nat}
    {a b : Enc} (h : Eval.ewType v t u = some rt) (ha : Enc.WF t na a) (hb : Enc.WF u nb b)
    (hs : dyadCount shape t u na nb = some n) (hfill : ¬(v = .fill ∧ shape = Kernel.Ew.va))
    (hty : (t = .guid ∧ u = .guid ∧ (v = .eq ∨ v = .ne ∨ v = .fill)) ∨ CmpClaims v t u ∨ ValClaims v t u rt)
    (hsym : t = .symbol → u = .symbol → SymClaims a b) :
    (dyadColumn v shape t u na a nb b).isSome := by
  unfold dyadColumn
  rw [← ewType_eq_resultType, h]
  simp only [Option.isSome_map]
  unfold dyadPayload
  rw [if_neg (by simpa using hfill)]
  simp only [hs, Option.bind_eq_bind, Option.bind_some]
  by_cases hg : t = .guid ∧ u = .guid ∧ (v = .eq ∨ v = .ne ∨ v = .fill)
  · obtain ⟨rfl, rfl, hv⟩ := hg
    cases a <;> simp [Enc.WF] at ha
    cases b <;> simp [Enc.WF] at hb
    rcases hv with rfl | rfl | rfl <;> by_cases hsh : shape = Kernel.Ew.av <;> simp [hsh, Enc.bytesOf]
  · rw [if_neg (by
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
          rintro ⟨⟨h1, h2⟩, h3 | h3⟩
          · exact hg ⟨h1, h2, .inl h3⟩
          · exact hg ⟨h1, h2, .inr (.inl h3)⟩),
      if_neg (by
          simp only [Bool.and_eq_true, beq_iff_eq]
          rintro ⟨⟨h1, h2⟩, h3⟩
          exact hg ⟨h1, h2, .inr (.inr h3)⟩)]
    rcases hty with hg' | hc | hv
    · exact absurd hg' hg
    · rw [if_pos hc.1]; simp only [Option.isSome_map]; exact cmpPayload_isSome hc ha hb hsym
    · rw [if_neg (by simp [cmpOp_none_of_valOp hv.1])]; simp only [Option.isSome_map]
      exact valPayload_isSome hv ha hb
