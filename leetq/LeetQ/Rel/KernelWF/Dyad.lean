/-
  The element-wise kernels `dyadColumn`, `monColumn`, `bitwPayload`, `lowZeroPayload` and the one-atom
  payload `Enc.ofAtoms t #[a]`: when they answer, read off their Lean bodies, and that what they answer
  is a well-formed payload.
-/
import QLean.Kernel.Elementwise
import QLean.Eval.Dyad
import QLean.Dep.Val
import QLean.Verify.Chain
import QLean.Verify.Alp
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

/-- An `∃` whose witness an `Option` computes is decided by reading the `Option`. -/
instance decExistsSome {α : Type} {o : Option α} {P : α → Prop} [DecidablePred P] :
    Decidable (∃ a, o = some a ∧ P a) :=
  match o with
  | none => isFalse (by simp)
  | some a => decidable_of_iff (P a) (by simp)

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
    ∃ ct, (if t == u then some t else Prim.common t u) = some ct ∧ ticksMeet t u ct = true ∧
      ∃ raw, clsOf ct = some raw ∧
      let cls := if raw == Kernel.Ew.bits || ((clsOf t == some Kernel.Ew.bits || clsOf u == some Kernel.Ew.bits) &&
        (raw == Kernel.Ew.u8 || raw == Kernel.Ew.i16)) then Kernel.Ew.i32 else raw
      convertible t cls = true ∧ convertible u cls = true)

/-- The symbol encodings `cmpPayload` reads against each other: two dense blobs, or two operands that are
    each interned or a single symbol. It declines a dense blob of other than one symbol against an
    interned column. -/
def SymClaims (ea eb : Enc) : Prop :=
  (∃ ba oa bb ob, ea = .syms ba oa ∧ eb = .syms bb ob) ∨ ((symIds ea).isSome ∧ (symIds eb).isSome)

instance (v : Prim.Dyadic) (t u rt : QAtomicType) : Decidable (ValClaims v t u rt) := by
  unfold ValClaims; exact inferInstance

instance (v : Prim.Dyadic) (t u : QAtomicType) : Decidable (CmpClaims v t u) := by
  unfold CmpClaims; exact inferInstance

/-- Read off the two constructors: whether both are dense blobs. -/
instance (ea eb : Enc) : Decidable (SymClaims ea eb) := by
  unfold SymClaims
  refine @instDecidableOr _ _ ?_ inferInstance
  cases ea <;> cases eb <;> first | exact isTrue ⟨_, _, _, _, rfl, rfl⟩ | exact isFalse (by simp)

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
    rcases hty with h | ⟨rfl, rfl⟩ | ⟨ct, hct, htk, raw, hraw, hcv⟩
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

/-- The whole hypothesis bundle of `dyadColumn_isSome` past the payloads' well-formedness is decidable,
    which is what `if h : claims then kernel else reference` needs. -/
example (v : Prim.Dyadic) (shape : UInt8) (t u rt : QAtomicType) (na nb n : Nat) (a b : Enc) :
    Decidable (Eval.ewType v t u = some rt ∧ dyadCount shape t u na nb = some n ∧
      ¬(v = .fill ∧ shape = Kernel.Ew.va) ∧
      ((t = .guid ∧ u = .guid ∧ (v = .eq ∨ v = .ne ∨ v = .fill)) ∨ CmpClaims v t u ∨ ValClaims v t u rt) ∧
      (t = .symbol → u = .symbol → SymClaims a b)) := inferInstance

/-! ## `monColumn` -/

/-- `mapPass` answers on a well-formed operand of a type with a class, at any class but a boolean's own. -/
theorem mapPass_isSome {bld : Kernel.Ew.Build} {cls : UInt8} {nulIn : QAtomicType → Int64} {nulOut : Int64}
    {t rt : QAtomicType} {n : Nat} {e : Enc} {stage : UInt8 → Kernel.Ew.Stage} {src : UInt8}
    (hc : clsOf t = some src) (hw : Enc.WF t n e) (hb : t = .boolean → cls ≠ Kernel.Ew.bits) :
    (mapPass bld cls nulIn nulOut t rt n e stage).isSome := by
  obtain ⟨⟨b, s⟩, h1⟩ := Option.isSome_iff_exists.1 (operandSource_isSome (b := bld) (dst := cls)
    (nulIn := nulIn t) (nulOut := nulOut) (n := n) (tk := none) hc hw hb (by simp))
  simp [mapPass, h1]

/-- `negAbsPayload` answers on a well-formed operand of a type with a class, at a result type with a class
    other than the bitmap's. -/
theorem negAbsPayload_isSome {op : UInt8} {t rt : QAtomicType} {n : Nat} {e : Enc} {src cls : UInt8}
    (hc : clsOf t = some src) (hrt : clsOf rt = some cls) (hcls : cls ≠ Kernel.Ew.bits) (hw : Enc.WF t n e) :
    (negAbsPayload op t rt n e).isSome := by
  unfold negAbsPayload
  simp only [hrt, Option.bind_eq_bind, Option.bind_some]
  exact orElse_isSome _ (mapPass_isSome hc hw (fun _ => hcls))

/-- `eqConstPayload` answers on every well-formed operand of a type with a class. -/
theorem eqConstPayload_isSome {t : QAtomicType} {k : UInt64} {n : Nat} {e : Enc} {src : UInt8}
    (hc : clsOf t = some src) (hw : Enc.WF t n e) : (eqConstPayload t k n e).isSome := by
  unfold eqConstPayload cmpClsOf
  simp only [hc, Option.map_some, Option.bind_eq_bind, Option.bind_some]
  refine orElse_isSome _ (mapPass_isSome hc hw (fun _ => ?_))
  split <;> simp_all [Kernel.Ew.i32, Kernel.Ew.bits]

/-- The types the monadic maps read have a class, except the general list. -/
theorem clsOf_of_numeric {t : QAtomicType} (hg : t ≠ .general) (hn : Prim.nonNumeric t = false) :
    ∃ s, clsOf t = some s := by
  cases t <;> simp_all [Prim.nonNumeric, clsOf]

/-- `neg` and `abs` read a type with a class and answer at one other than the bitmap's. -/
theorem negType_cls {t rt : QAtomicType} (h : negType t = some rt) (hg : t ≠ .general) :
    ∃ s c, clsOf t = some s ∧ clsOf rt = some c ∧ c ≠ Kernel.Ew.bits := by
  cases t <;> simp [negType, Prim.nonNumeric] at h <;> subst h <;>
    simp_all [clsOf, Kernel.Ew.bits, Kernel.Ew.i32, Kernel.Ew.i16, Kernel.Ew.i64, Kernel.Ew.u8, Kernel.Ew.f32,
      Kernel.Ew.f64]

/-- A bind of an answer into a function that always answers, answers. -/
theorem bind_isSome {α β : Type} {x : Option α} {f : α → Option β} (hx : x.isSome) (hf : ∀ a, (f a).isSome) :
    (x.bind f).isSome := by
  cases x <;> simp_all

/-- `signumPayload` answers on every well-formed operand of a type with a class. -/
theorem signumPayload_isSome {t : QAtomicType} {n : Nat} {e : Enc} {src : UInt8}
    (hc : clsOf t = some src) (hw : Enc.WF t n e) : (signumPayload t n e).isSome := by
  unfold signumPayload cmpClsOf
  simp only [hc, Option.map_some, Option.bind_eq_bind, Option.bind_some]
  refine bind_isSome (operandSource_isSome hc hw (fun _ => ?_) (by simp)) (fun _ => rfl)
  split <;> simp_all [Kernel.Ew.i32, Kernel.Ew.bits]

/-! ## A chain answers its last stage -/

/-- A build's program holds one record per stage, and one for `last`. -/
theorem prog_count (b : Kernel.Ew.Build) (last : Kernel.Ew.Stage) :
    (b.prog last).size / Kernel.Ew.stageBytes = b.stages.size + 1 := by
  have hL : ∀ x ∈ (b.stages.push last).toList.map Kernel.Ew.Stage.bytes, x.size = Kernel.Ew.stageBytes :=
    fun x hx => by obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx; exact Verify.stage_bytes_size s
  have hs := (Verify.foldl_append_get Kernel.Ew.stageBytes _ hL ByteArray.empty).1
  have hp : b.prog last =
      ((b.stages.push last).toList.map Kernel.Ew.Stage.bytes).foldl (· ++ ·) ByteArray.empty := by
    simp only [Kernel.Ew.Build.prog, ← Array.foldl_toList, Array.toList_map]
  rw [hp, hs]; simp [Kernel.Ew.stageBytes]

/-- The last of the outputs a fold pushes one per step is the last step's. -/
theorem foldl_push_getLast {α : Type} [Inhabited α] (G : Array α → Nat → α) (m : Nat) :
    ((List.range (m + 1)).foldl (fun outs j => outs.push (G outs j)) #[])[m]! =
      G ((List.range m).foldl (fun outs j => outs.push (G outs j)) #[]) m := by
  have hs : ((List.range m).foldl (fun outs j => outs.push (G outs j)) #[]).size = m := by
    rw [foldl_size Array.size _ 1 (fun _ _ => Array.size_push ..)]; simp
  rw [List.range_succ, List.foldl_append]
  simp [Array.getElem_push, hs]

/-- `chain` answers what its last stage's engine writes; the engine is read off `last`. -/
local macro "run_reduce" : tactic => `(tactic| (
  simp only [Kernel.Ew.Build.run, Kernel.Ew.chain, prog_count, Nat.add_sub_cancel]
  rw [foldl_push_getLast, Verify.stageAt_prog _ _ _ (Nat.lt_succ_self _), Array.getElem_push_eq]))

/-- A chain ending in `Ew.mon` answers `n` elements at its class's width. -/
theorem run_mon_size (b : Kernel.Ew.Build) (op cls a : UInt8) (nul : Int64) (n : USize) :
    (b.run { engine := Kernel.Ew.eMon, op, cls, a, nul } n).size = n.toNat * Kernel.Ew.width cls := by
  run_reduce; simp [Kernel.Ew.eMon, Kernel.Ew.eVal, Kernel.Ew.eCmp, Ew.mon_size]

/-! ## What `payload` answers -/

/-- A chain's answer of `n` elements at a type's width, other than boolean, is a well-formed payload. -/
theorem payload_wf {rt : QAtomicType} {w : Nat} {b : Kernel.Ew.Build} {last : Kernel.Ew.Stage} {n : USize}
    (hb : rt ≠ .boolean) (hw : rt.width = some w) (hs : (b.run last n).size = n.toNat * w) :
    Enc.WF rt n.toNat (payload rt n (b, last)) := by
  have hn : n.toNat < USize.size := USize.toNat_lt_size n
  simp only [payload]
  rw [if_neg (by simpa using hb), hw]
  by_cases he : Column.encodes rt = true
  · simp only [he]
    have h0 : 0 < w ∧ w ≤ 8 ∧ rt ≠ .guid := by
      cases rt <;> simp_all [QAtomicType.width, Column.encodes] <;> omega
    generalize hE : b.runEnc last n w.toUSize = E
    obtain ⟨m, p⟩ := E
    have hm : m = (Kernel.Coc.encode w.toUSize (b.run last n)).1 := (congrArg Prod.fst hE).symm
    refine answer_wf (wf_foR (by simp [hw]) hb h0.2.2 ?_) hn
    rw [hm, Verify.nblk_encode w h0.1 h0.2.1, hs, Nat.mul_div_cancel _ h0.1]
    simp only [Column.blk]; omega
  · simp only [Bool.not_eq_true] at he; simp only [he]
    exact answer_wf (wf_bytes hb hw hs) hn

/-- `mapPass` answers a well-formed payload when its stage writes `n` elements at the result type's width. -/
theorem mapPass_wf {bld : Kernel.Ew.Build} {cls : UInt8} {nulIn : QAtomicType → Int64} {nulOut : Int64}
    {t rt : QAtomicType} {n w : Nat} {e r : Enc} {stage : UInt8 → Kernel.Ew.Stage} (hn : n < USize.size)
    (hb : rt ≠ .boolean) (hw : rt.width = some w)
    (hs : ∀ (b : Kernel.Ew.Build) sa, (b.run (stage sa) n.toUSize).size = n * w)
    (h : mapPass bld cls nulIn nulOut t rt n e stage = some r) : Enc.WF rt n r := by
  unfold mapPass at h
  cases ho : operandSource bld t n e cls (nulIn t) nulOut n with
  | none => simp [ho] at h
  | some x =>
    obtain ⟨b, sa⟩ := x
    simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
    subst h
    have := payload_wf (n := n.toUSize) (b := b) (last := stage sa) hb hw (by rw [hs, toUSize_toNat hn])
    rwa [toUSize_toNat hn] at this

/-- An alternative that answered is one of its two sides. -/
theorem orElse_eq_some {α : Type} {x y : Option α} {r : α} (h : (x <|> y) = some r) :
    x = some r ∨ y = some r := by
  cases x with
  | none => exact .inr h
  | some a => exact .inl h

/-- What `negAbsPayload` answers is `n` elements of its result type, when that type has a class other
    than the bitmap's and `n` fits a `USize`. -/
theorem negAbsPayload_wf {op : UInt8} {t rt : QAtomicType} {n : Nat} {e r : Enc} {cls : UInt8}
    (hn : n < USize.size) (hc : clsOf rt = some cls) (hcls : cls ≠ Kernel.Ew.bits)
    (h : negAbsPayload op t rt n e = some r) : Enc.WF rt n r := by
  have hb : rt ≠ .boolean := by rintro rfl; simp [clsOf] at hc; exact hcls hc.symm
  have hg : rt ≠ .guid := by rintro rfl; simp [clsOf] at hc
  have hwd := width_clsOf hc hb
  unfold negAbsPayload at h
  simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
  rcases orElse_eq_some h with h1 | h1
  · split at h1
    · split at h1
      · rename_i md pk _
        generalize hE : Kernel.Ew.foRMonEnc op cls (nullPayload rt) md pk n.toUSize = E at h1
        obtain ⟨m, p⟩ := E
        simp only [Option.some.injEq] at h1; subst h1
        have hm : m = (Kernel.Coc.encode (Kernel.Ew.width cls).toUSize
            (Kernel.Ew.mon op cls (nullPayload rt) (Kernel.Coc.decode (Kernel.Ew.width cls).toUSize md pk
              n.toUSize) n.toUSize)).1 := (congrArg Prod.fst hE).symm
        have h0 := Verify.width_pos_le cls
        refine answer_wf (wf_foR (by simp [hwd]) hb hg ?_) hn
        rw [hm, Verify.nblk_encode _ h0.1 h0.2, Ew.mon_size, toUSize_toNat hn, Nat.mul_div_cancel _ h0.1]
        simp only [Column.blk]; omega
      · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
  · exact mapPass_wf hn hb hwd (fun b sa => by rw [run_mon_size, toUSize_toNat hn]) h1

/-! ## `monColumn` answers -/

/-- The names `monResultType` gives a type for. -/
def monNames : List String :=
  ["neg", "abs", "sqrt", "exp", "log", "sin", "cos", "tan", "asin", "acos", "atan", "null", "not", "signum",
    "reciprocal", "floor", "ceiling"]

/-- A type a numeric map answers for is not `guid` or `symbol`. -/
theorem numeric_of {t x rt : QAtomicType} (h : (if Prim.nonNumeric t then none else some x) = some rt) :
    Prim.nonNumeric t = false := by
  cases hn : Prim.nonNumeric t <;> simp_all

/-- A float map answers on every well-formed operand of a type with a class. -/
theorem floatMap_isSome {name : String} {t rt : QAtomicType} {n : Nat} {e : Enc} {op : UInt8}
    (hop : floatMapOp name = some op) (hrt : (if (clsOf t).isSome then some QAtomicType.float else none) = some rt)
    (hw : Enc.WF t n e) :
    ((floatMapOp name).bind fun op => mapPass {} Kernel.Ew.f64 (verbNull false) (nullPayload .float) t rt n e
      fun sa => { engine := Kernel.Ew.eMon, op, cls := Kernel.Ew.f64, a := sa, nul := Kernel.Ew.noNull }).isSome := by
  split at hrt
  · rename_i hcs
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hcs
    rw [hop, Option.bind_some]; exact mapPass_isSome hs hw (fun _ => by simp [Kernel.Ew.f64, Kernel.Ew.bits])
  · exact absurd hrt (by simp)

/-- `monColumn` answers on every well-formed operand at every name and type `monResultType` answers for,
    except the general list, which no map reads. -/
theorem monColumn_isSome {name : String} {t rt : QAtomicType} {n : Nat} {e : Enc} (hname : name ∈ monNames)
    (hrt : monResultType name t = some rt) (hg : t ≠ .general) (hw : Enc.WF t n e) (hn : n < USize.size) :
    (monColumn name t n e).isSome := by
  unfold monColumn; rw [hrt]; simp only [Option.isSome_map]
  have key : ∀ {f : QAtomicType → Option Enc}, monPayload name t n e = (monResultType name t).bind f →
      (f rt).isSome → (monPayload name t n e).isSome := fun h1 h2 => by rw [h1, hrt]; exact h2
  simp only [monNames, List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · obtain ⟨s, c, hs, hc, hcb⟩ := negType_cls (rt := rt) hrt hg
    exact key rfl (negAbsPayload_isSome hs hc hcb hw)
  · obtain ⟨s, c, hs, hc, hcb⟩ := negType_cls (rt := rt) hrt hg
    exact key rfl (negAbsPayload_isSome hs hc hcb hw)
  iterate 9 exact key rfl (floatMap_isSome rfl hrt hw)
  · refine key rfl ?_
    show (if t == .guid then guidNull n e
      else if t == .symbol then cmpPayload .eq Kernel.Ew.va .symbol .symbol n e 1 (.syms ⟨#[0]⟩ #[0, 1]) n
      else match nullBits t with
        | some k => eqConstPayload t k n e
        | none => do let _ ← clsOf t; some (.bits ⟨Array.replicate ((n + 7) / 8) 0⟩)).isSome
    by_cases hgd : t = .guid
    · subst hgd; simp only [beq_self_eq_true, if_true, guidNull, Option.isSome_map]
      exact bytesOf_isSome (by decide) (by decide) hw
    rw [if_neg (by simpa using hgd)]
    by_cases hsy : t = .symbol
    · subst hsy; simp only [beq_self_eq_true, ↓reduceIte]
      exact cmpPayload_isSome ⟨rfl, .inl ⟨rfl, rfl⟩⟩ hw (by decide)
        (fun _ _ => by cases e <;> simp [Enc.WF] at hw <;> simp [SymClaims, symIds])
    rw [if_neg (by simpa using hsy)]
    obtain ⟨s, hs⟩ := clsOf_of_numeric hg (by cases t <;> simp_all [Prim.nonNumeric])
    cases hk : nullBits t
    · simp [hs]
    · exact eqConstPayload_isSome hs hw
  · obtain ⟨s, hs⟩ := clsOf_of_numeric hg (numeric_of hrt)
    exact key rfl (eqConstPayload_isSome hs hw)
  · obtain ⟨s, hs⟩ := clsOf_of_numeric hg (numeric_of hrt)
    exact key rfl (signumPayload_isSome hs hw)
  · obtain ⟨s, hs⟩ := clsOf_of_numeric hg (numeric_of hrt)
    exact key rfl (mapPass_isSome hs hw (fun _ => by simp [Kernel.Ew.f64, Kernel.Ew.bits]))
  · have hr : kernelFloorType t = some rt := hrt
    refine key rfl ?_
    show (floorPayload t rt n e).isSome
    unfold floorPayload
    split
    · rfl
    · obtain ⟨s, hs⟩ : ∃ s, clsOf t = some s := by cases t <;> simp_all [kernelFloorType, clsOf]
      simp only [hs, Option.bind_eq_bind, Option.bind_some]
      exact mapPass_isSome hs hw (fun h => by subst h; simp [kernelFloorType] at hr)
  · have hr : ((negType t).bind fun t1 => (kernelFloorType t1).bind fun t2 => negType t2) = some rt := hrt
    cases h1 : negType t with
    | none => rw [h1] at hr; exact absurd hr (by simp)
    | some t1 =>
    rw [h1, Option.bind_some] at hr
    cases h2 : kernelFloorType t1 with
    | none => rw [h2] at hr; exact absurd hr (by simp)
    | some t2 =>
    rw [h2, Option.bind_some] at hr
    refine key rfl ?_
    show (ceilingPayload t n e).isSome
    unfold ceilingPayload
    simp only [h1, h2, hr, Option.bind_eq_bind, Option.bind_some]
    obtain ⟨s, c1, hs, hc1, hcb1⟩ := negType_cls h1 hg
    have hg2 : t2 ≠ .general := by rintro rfl; cases t1 <;> simp [kernelFloorType] at h2
    obtain ⟨s2, c3, hs2, hc3, hcb3⟩ := negType_cls hr hg2
    split
    · rename_i h12
      have h12' : t1 = t2 := by simpa using h12
      subst h12'
      obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 (negAbsPayload_isSome (op := Kernel.Ew.neg) hs hc1 hcb1 hw)
      rw [hr1, Option.bind_some]
      exact negAbsPayload_isSome hs2 hc3 hcb3 (negAbsPayload_wf hn hc1 hcb1 hr1)
    · simp only [hc1, hc3, Option.bind_some]
      exact bind_isSome (operandSource_isSome hs hw (fun _ => hcb1) (by simp)) (fun _ => rfl)

