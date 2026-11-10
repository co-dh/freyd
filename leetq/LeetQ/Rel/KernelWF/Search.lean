/-
  Totality of the search kernels `where`, `distinct`, `?`, `in`, `bin` and `~` under the payloads'
  `Enc.WF`, and the shape of what each answers: the facts that let `Find`, `Ew` and `Struct` drop the
  `Option` these kernels return.
-/
import QLean.Kernel.Search
import QLean.Kernel.Sort
import QLean.Verify.Where
import QLean.Verify.Distinct
import QLean.Verify.FindMember
import QLean.Verify.Search
import QLean.Verify.SymFind
import LeetQ.Rel.KernelWF.Gather

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify


/-! ## Readers every kernel here goes through -/

theorem operand_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hb : t ≠ .boolean) (ht : t.width.isSome)
    (hw : Enc.WF t n e) : (operand t n e).isSome := by
  have := bytesOf_isSome hb ht hw
  unfold operand; split <;> simp_all

theorem findSorted_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hb : t ≠ .boolean) (ht : t.width.isSome)
    (hw : Enc.WF t n e) (w : Nat) (ks : ByteArray) : (findSorted t w n e ks).isSome := by
  have := bytesOf_isSome hb ht hw
  unfold findSorted; split <;> simp_all

theorem memberSorted_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hb : t ≠ .boolean) (ht : t.width.isSome)
    (hw : Enc.WF t n e) (w : Nat) (ks : ByteArray) : (memberSorted t w n e ks).isSome := by
  have := bytesOf_isSome hb ht hw
  unfold memberSorted; split <;> simp_all

theorem probeColumns_isSome {t : QAtomicType} {xn cn : Nat} {xe ce : Enc} (hb : t ≠ .boolean)
    (ht : t.width.isSome) (hx : Enc.WF t xn xe) (hc : Enc.WF t cn ce) (w : Nat) (m : Bool) :
    (probeColumns t w m xn xe cn ce).isSome := by
  obtain ⟨⟨a1, a2, a3⟩, h1⟩ := Option.isSome_iff_exists.1 (operand_isSome hb ht hx)
  obtain ⟨⟨b1, b2, b3⟩, h2⟩ := Option.isSome_iff_exists.1 (operand_isSome hb ht hc)
  unfold probeColumns; simp only [h1, h2, Option.bind_eq_bind, Option.bind_some]; split <;> simp

/-! ## `where` -/

/-- A fold that pushes one long a step writes eight bytes an element. -/
theorem pushLongs_size {α : Type} (l : List α) (f : α → UInt64) :
    (l.foldl (fun acc i => Column.pushBits acc (f i) 8) ByteArray.empty).size = l.length * 8 := by
  rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

theorem whereBits_size (n : USize) (b : ByteArray) :
    (whereBits n b).size = ((List.range n.toNat).filter (Column.bitAt b)).length * 8 :=
  pushLongs_size _ _

/-- **`where` answers** every well-formed boolean column. -/
theorem whereColumn_isSome {n : Nat} {e : Enc} (hw : Enc.WF .boolean n e) :
    (whereColumn .boolean n e).isSome := by
  cases e <;> simp_all [Enc.WF, whereColumn, QAtomicType.width]

/-- **`where` answers a dense long column.** -/
theorem whereColumn_wf {n : Nat} {e : Enc} {v : QValue} (hw : Enc.WF .boolean n e)
    (h : whereColumn .boolean n e = some v) :
    ∃ m b, v = .vector .long m (.bytes b) none ∧ Enc.WF .long m (.bytes b) := by
  cases e <;> simp_all [Enc.WF, whereColumn, QAtomicType.width]
  subst h
  exact ⟨_, _, rfl, by simp [Enc.WF, QAtomicType.width, whereBits_size]⟩

/-! ## `distinct` -/

/-- **`distinct` answers** every well-formed column but a general list. -/
theorem distinctColumn_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general) :
    (distinctColumn t n e).isSome := by
  cases t <;> cases e <;> simp_all (config := { decide := true })
    [Enc.WF, distinctColumn, orderKind, Enc.bytesOf, QAtomicType.width] <;> (repeat' split) <;> simp_all

/-! ## Payload layouts each type admits -/

theorem wf_bits {t : QAtomicType} {n : Nat} {b : ByteArray} (h : Enc.WF t n (.bits b)) : t = .boolean := by
  cases t <;> simp_all [Enc.WF]

theorem wf_syms {t : QAtomicType} {n : Nat} {b : ByteArray} {o : Array Nat} (h : Enc.WF t n (.syms b o)) :
    t = .symbol := by
  cases t <;> simp_all [Enc.WF]

theorem wf_enum {t : QAtomicType} {n : Nat} {b : ByteArray} {o : Array Nat} {i : ByteArray}
    (h : Enc.WF t n (.enum b o i)) : t = .symbol := by
  cases t <;> simp_all [Enc.WF]

/-- A symbol payload is a blob or interned: `WF` admits no other layout at `symbol`. -/
theorem symbol_cases {n : Nat} {e : Enc} (hw : Enc.WF .symbol n e) :
    (∃ b o, e = .syms b o) ∨ ∃ d o i, e = .enum d o i := by
  cases e <;> simp_all [Enc.WF, QAtomicType.width]

/-! ## The dense arms of `?`, `in` and `bin`, the needle already at the haystack's type -/

/-- At a type with a dense width, `?` against a needle column of the same type is the halving under
    `` `s `` and the hashed probe otherwise. -/
theorem findColumn_dense {t : QAtomicType} {w : Nat} (hd : denseWidth t = some w) (s : Bool) (nx : Nat)
    (ex : Enc) (m : Nat) (e : Enc) (a : Option (UInt8 × IndexCell)) :
    findColumn t s nx ex (.vector t m e a) =
      if s && worthHalving nx m then
        (match Enc.bytesOf t m e with
         | some ks => (findSorted t w nx ex ks).map fun out => .vector .long (out.size / 8) (.bytes out) none
         | none => none)
      else (probeColumns t w false nx ex m e).map fun out => .vector .long (out.size / 8) (.bytes out) none := by
  cases t <;> simp [denseWidth, QAtomicType.width] at hd <;> subst hd <;> rfl

theorem memberColumn_dense {t : QAtomicType} {w : Nat} (hd : denseWidth t = some w) (s : Bool) (m : Nat)
    (e : Enc) (a : Option (UInt8 × IndexCell)) (yn : Nat) (ye : Enc) :
    memberColumn t s (.vector t m e a) yn ye =
      if s && worthHalving yn m then
        (match Enc.bytesOf t m e with
         | some ks => (memberSorted t w yn ye ks).map fun out => .vector .boolean (ks.size / w) (.bits out) none
         | none => none)
      else (probeColumns t w true yn ye m e).map fun out => .vector .boolean m (.bits out) none := by
  cases t <;> simp [denseWidth, QAtomicType.width] at hd <;> subst hd <;> rfl

theorem binColumn_dense {t : QAtomicType} {w : Nat} (hd : denseWidth t = some w) (r : Bool) (xn : Nat)
    (xe : Enc) (m : Nat) (e : Enc) (a : Option (UInt8 × IndexCell)) :
    binColumn t r xn xe (.vector t m e a) =
      (operand t xn xe).bind fun (hn, hm, hp) => (operand t m e).bind fun (kn, km, kp) =>
        some (.vector .long m (.bytes (binOperands w.toUSize (foldsZero t) (ordSigned t) r
          hm hp hn.toUSize km kp kn.toUSize)) none) := by
  cases t <;> simp [denseWidth, QAtomicType.width] at hd <;> subst hd <;> rfl

/-- `x in y` at a blob needle column: the haystack asked at each of its symbols. -/
theorem memberColumn_syms (s : Bool) (n : Nat) (b : ByteArray) (o : Array Nat) (a : Option (UInt8 × IndexCell))
    (yn : Nat) (ye : Enc) :
    memberColumn .symbol s (.vector .symbol n (.syms b o) a) yn ye =
      (findSymKeys yn ye b o).map fun ans =>
        .vector .boolean (o.size - 1) (.bits (belowBits ans (o.size - 1).toUSize yn.toUSize)) none := rfl

/-- `x in y` at an interned needle column: one key compare when the haystack holds one symbol, and
    otherwise the haystack asked at the needle's dictionary, carried back through its ids. -/
theorem memberColumn_enum (s : Bool) (n : Nat) (d : ByteArray) (o : Array Nat) (i : ByteArray)
    (a : Option (UInt8 × IndexCell)) (yn : Nat) (ye : Enc) :
    memberColumn .symbol s (.vector .symbol n (.enum d o i) a) yn ye =
      match soleSym yn ye with
      | some k => some (.vector .boolean n (.bits
          (Ew.cmpIdsKey Ew.eq d o i (Column.idWidth o).toUSize k n.toUSize)) none)
      | none => (findSymKeys yn ye d o).map fun ans => .vector .boolean n (.bits (maskByIds
          (belowBits ans (o.size - 1).toUSize yn.toUSize)
          (o.size - 1).toUSize n.toUSize (Column.idWidth o).toUSize i)) none := rfl

theorem denseWidth_gates {t : QAtomicType} {w : Nat} (hd : denseWidth t = some w) :
    t ≠ .boolean ∧ t.width.isSome := by
  cases t <;> simp_all [denseWidth, QAtomicType.width]

/-! ## `?` -/

/-- **`x?y` answers** every well-formed haystack and needle column of one type but a general list. -/
theorem findColumn_isSome {t : QAtomicType} {s : Bool} {nx ny : Nat} {ex ey : Enc} {a : Option (UInt8 × IndexCell)}
    (hx : Enc.WF t nx ex) (hy : Enc.WF t ny ey) (hg : t ≠ .general) :
    (findColumn t s nx ex (.vector t ny ey a)).isSome := by
  cases hd : denseWidth t with
  | some w =>
    obtain ⟨hb, ht⟩ := denseWidth_gates hd
    obtain ⟨ks, hk⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome hb ht hy)
    rw [findColumn_dense hd]
    split <;> simp [hk, findSorted_isSome hb ht hx, probeColumns_isSome hb ht hx hy]
  | none =>
    cases t <;> simp [denseWidth, QAtomicType.width] at hd
    case general => exact absurd rfl hg
    case symbol =>
      cases ex <;> cases ey <;> simp [Enc.WF, QAtomicType.width] at hx hy <;> simp_all [findColumn, findSymColumn, fewSyms, symKeys, findSymKeys] <;>
        (repeat' split) <;> simp_all
    case boolean => cases ex <;> cases ey <;> simp_all [Enc.WF, findColumn]
    case guid =>
      obtain ⟨_, h1⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome (by decide) rfl hx)
      obtain ⟨_, h2⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome (by decide) rfl hy)
      simp [findColumn, h1, h2]

/-! ## `in` -/

/-- **`x in y` answers** every well-formed needle column and haystack of one type but a general list. -/
theorem memberColumn_isSome {t : QAtomicType} {s : Bool} {nx ny : Nat} {ex ey : Enc} {a : Option (UInt8 × IndexCell)}
    (hx : Enc.WF t nx ex) (hy : Enc.WF t ny ey) (hg : t ≠ .general) :
    (memberColumn t s (.vector t nx ex a) ny ey).isSome := by
  cases hd : denseWidth t with
  | some w =>
    obtain ⟨hb, ht⟩ := denseWidth_gates hd
    obtain ⟨ks, hk⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome hb ht hx)
    rw [memberColumn_dense hd]
    split <;> simp [hk, memberSorted_isSome hb ht hy, probeColumns_isSome hb ht hy hx]
  | none =>
    cases t <;> simp [denseWidth, QAtomicType.width] at hd
    case general => exact absurd rfl hg
    case symbol =>
      have hk : ∀ kb ko, (findSymKeys ny ey kb ko).isSome := fun kb ko => by
        rcases symbol_cases hy with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
      rcases symbol_cases hx with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩
      · rw [memberColumn_syms]; simp [hk]
      · rw [memberColumn_enum]; split <;> simp [hk]
    -- `simp [memberColumn]` times out building the equation lemmas; the arm reduces by `rfl`
    all_goals
      cases ex <;> cases ey <;> simp [Enc.WF, QAtomicType.width] at hx hy
      all_goals exact rfl

/-! ## `bin` -/

/-- **`x bin y` answers** every well-formed haystack and needle column of one type but a general list. -/
theorem binColumn_isSome {t : QAtomicType} {r : Bool} {nx ny : Nat} {ex ey : Enc} {a : Option (UInt8 × IndexCell)}
    (hx : Enc.WF t nx ex) (hy : Enc.WF t ny ey) (hg : t ≠ .general) :
    (binColumn t r nx ex (.vector t ny ey a)).isSome := by
  cases hd : denseWidth t with
  | some w =>
    obtain ⟨hb, ht⟩ := denseWidth_gates hd
    obtain ⟨_, h1⟩ := Option.isSome_iff_exists.1 (operand_isSome hb ht hx)
    obtain ⟨_, h2⟩ := Option.isSome_iff_exists.1 (operand_isSome hb ht hy)
    rw [binColumn_dense hd]; simp [h1, h2]
  | none =>
    cases t <;> simp [denseWidth, QAtomicType.width] at hd
    case general => exact absurd rfl hg
    case symbol =>
      cases ex <;> cases ey <;> simp [Enc.WF, QAtomicType.width] at hx hy <;> simp_all [binColumn, binSymColumn, symKeys]
    case boolean => cases ex <;> cases ey <;> simp_all [Enc.WF, binColumn]
    case guid =>
      obtain ⟨_, h1⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome (by decide) rfl hx)
      obtain ⟨_, h2⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome (by decide) rfl hy)
      simp [binColumn, h1, h2]

/-! ## `~` -/

/-- **`x~y` answers** every pair of well-formed columns of one type but a general list. -/
theorem matchColumn_isSome {t : QAtomicType} {nx ny : Nat} {ex ey : Enc} (hx : Enc.WF t nx ex)
    (hy : Enc.WF t ny ey) (hg : t ≠ .general) : (matchColumn t nx ex ny ey).isSome := by
  by_cases hs : t = .symbol ∨ t = .boolean
  · rcases hs with rfl | rfl <;> cases ex <;> cases ey <;> simp_all [Enc.WF, matchColumn, QAtomicType.width]
  have hb : t ≠ .boolean := fun h => hs (.inr h)
  have hy' : t ≠ .symbol := fun h => hs (.inl h)
  obtain ⟨w, hw⟩ : ∃ w, t.width = some w := by cases t <;> simp_all [QAtomicType.width]
  have ht : t.width.isSome := by simp [hw]
  obtain ⟨⟨_, _, _⟩, h1⟩ := Option.isSome_iff_exists.1 (operand_isSome hb ht hx)
  obtain ⟨⟨_, _, _⟩, h2⟩ := Option.isSome_iff_exists.1 (operand_isSome hb ht hy)
  obtain ⟨_, k1⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome hb ht hx)
  obtain ⟨_, k2⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome hb ht hy)
  unfold matchColumn
  split
  · exact absurd (wf_bits hx) hb
  · exact absurd (wf_syms hx) hy'
  · exact absurd (wf_enum hx) hy'
  · exact absurd (wf_syms hx) hy'
  · exact absurd (wf_enum hx) hy'
  · split
    · simp
    · simp only [hw]; split <;> simp [h1, h2, k1, k2]

end LeetQ.Rel.KernelWF
