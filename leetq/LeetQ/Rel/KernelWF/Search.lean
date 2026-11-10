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

/-! ## The answers' sizes -/

private theorem width_le {t : QAtomicType} {w : Nat} (hw : t.width = some w) : w ≤ 16 := by
  cases t <;> simp [QAtomicType.width] at hw <;> omega

private theorem width_toNat {t : QAtomicType} {w : Nat} (hw : t.width = some w) : w.toUSize.toNat = w :=
  toNat_small w (by have := width_le hw; omega)

private theorem countFits_lt {n : Nat} {e : Enc} (hn : n < USize.size) : countFits n e := by
  cases e <;> simp [countFits, hn]

theorem findVec_size (w : USize) (f : Bool) (hay ndl : ByteArray) :
    (findVec w f hay ndl).size = ndl.size / w.toNat * 8 := by
  simp only [findVec]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

theorem findSortedBytes_size (w : USize) (f s : Bool) (hay keys : ByteArray) :
    (findSortedBytes w f s hay keys).size = keys.size / w.toNat * 8 := by
  simp only [findSortedBytes]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

theorem binBytes_size (w : USize) (f s r : Bool) (hay keys : ByteArray) :
    (binBytes w f s r hay keys).size = keys.size / w.toNat * 8 := by
  simp only [binBytes]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

theorem findBitVec_size (n : USize) (hay : ByteArray) (m : USize) (ndl : ByteArray) :
    (findBitVec n hay m ndl).size = m.toNat * 8 := by
  simp only [findBitVec]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

theorem binWide_size (w : USize) (r : Bool) (hay keys : ByteArray) :
    (binWide w r hay keys).size = keys.size / w.toNat * 8 := by
  simp only [binWide]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

theorem binBits_size (n : USize) (hay : ByteArray) (m : USize) (ndl : ByteArray) (r : Bool) :
    (binBits n hay m ndl r).size = m.toNat * 8 := by
  simp only [binBits, binBytes_size]
  rw [foldl_size ByteArray.size _ 1 (fun _ _ => by simp only [ByteArray.size, ByteArray.push, Array.size_push])]; simp

/-- What `operandBytes` reads of a well-formed column's `operand` is its `n` elements at `w` bytes. -/
theorem operandBytes_size {t : QAtomicType} {n w k : Nat} {e : Enc} {m p : ByteArray} (hb : t ≠ .boolean)
    (hw : t.width = some w) (hwf : Enc.WF t n e) (hn : n < USize.size) (h : operand t n e = some (k, m, p)) :
    (operandBytes w.toUSize m p k.toUSize).size = n * w := by
  unfold operand at h
  split at h
  · rename_i s hs
    cases h
    unfold foRColumn at hs
    split at hs
    · split at hs
      · rename_i hc
        cases hs
        have hM : m.isEmpty = false := by simp_all
        simp [operandBytes, hM, decode_size, USize.toNat_ofNat_of_lt' hn, width_toNat hw]
      · cases hs
    · cases hs
  · obtain ⟨b, hb', hbs⟩ := bytesOf_size hb hw hwf (countFits_lt hn)
    rw [hb'] at h
    simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [operandBytes, hbs, ByteArray.isEmpty]

/-- A long column of `m` elements, given its bytes. -/
theorem long_answer {out : ByteArray} {m : Nat} (h : out.size = m * 8) :
    ∃ e', QValue.vector .long (out.size / 8) (.bytes out) none = .vector .long m e' none ∧ Enc.WF .long m e' :=
  ⟨.bytes out, by rw [h, Nat.mul_div_cancel _ (by decide)], by simp [Enc.WF, QAtomicType.width, h]⟩

theorem findSorted_size {t : QAtomicType} {n w : Nat} {e : Enc} {ks out : ByteArray}
    (hwU : w.toUSize.toNat = w) (h : findSorted t w n e ks = some out) : out.size = ks.size / w * 8 := by
  unfold findSorted at h
  split at h
  · cases h; simp [foRFindSorted, findSortedBytes_size, hwU]
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; simp [findSortedBytes_size, hwU]

theorem probeColumns_find_size {t : QAtomicType} {w xn m : Nat} {xe ce : Enc} {out : ByteArray}
    (hb : t ≠ .boolean) (hw : t.width = some w) (hw0 : 0 < w) (hy : Enc.WF t m ce)
    (hn : m < USize.size) (h : probeColumns t w false xn xe m ce = some out) : out.size = m * 8 := by
  have hwU := width_toNat hw
  unfold probeColumns at h
  cases h1 : operand t xn xe with
  | none => simp [h1] at h
  | some s1 =>
    cases h2 : operand t m ce with
    | none => simp [h1, h2] at h
    | some s2 =>
      obtain ⟨a1, a2, a3⟩ := s1
      obtain ⟨b1, b2, b3⟩ := s2
      have hs := operandBytes_size hb hw hy hn h2
      simp only [h1, h2, Option.bind_eq_bind, Option.bind_some] at h
      split at h <;> cases h
      · rename_i hE
        have hE2 : b2.isEmpty = true := by simp_all
        simp only [operandBytes, hE2, if_true] at hs
        simp [findVec_size, hs, hwU, Nat.mul_div_cancel _ hw0]
      · simp [foRFindVec, findVec_size, hs, hwU, Nat.mul_div_cancel _ hw0]

/-! ## `?`, `bin`: one long per needle -/

theorem findColumn_bits (s : Bool) (n : Nat) (b : ByteArray) (m : Nat) (mb : ByteArray)
    (a : Option (UInt8 × IndexCell)) :
    findColumn .boolean s n (.bits b) (.vector .boolean m (.bits mb) a) =
      some (.vector .long m (.bytes (findBitVec n.toUSize b m.toUSize mb)) none) := rfl

theorem findColumn_guid (s : Bool) (n : Nat) (b : ByteArray) (m : Nat) (nb : ByteArray)
    (a : Option (UInt8 × IndexCell)) :
    findColumn .guid s n (.bytes b) (.vector .guid m (.bytes nb) a) =
      some (.vector .long m (.bytes (findVec 16 false b nb)) none) := rfl

theorem binColumn_bits (r : Bool) (n : Nat) (b : ByteArray) (m : Nat) (mb : ByteArray)
    (a : Option (UInt8 × IndexCell)) :
    binColumn .boolean r n (.bits b) (.vector .boolean m (.bits mb) a) =
      some (.vector .long m (.bytes (binBits n.toUSize b m.toUSize mb r)) none) := rfl

theorem binColumn_guid (r : Bool) (n : Nat) (b : ByteArray) (m : Nat) (nb : ByteArray)
    (a : Option (UInt8 × IndexCell)) :
    binColumn .guid r n (.bytes b) (.vector .guid m (.bytes nb) a) =
      some (.vector .long m (.bytes (binWide 16 r b nb)) none) := rfl

/-- **`x?y` answers one long per needle** at every type with a fixed-width or bit layout. -/
theorem findColumn_wf {t : QAtomicType} {s : Bool} {nx ny : Nat} {ex ey : Enc} {a : Option (UInt8 × IndexCell)}
    {v : QValue} (hx : Enc.WF t nx ex) (hy : Enc.WF t ny ey) (ht : t ≠ .symbol) (hn : ny < USize.size)
    (h : findColumn t s nx ex (.vector t ny ey a) = some v) :
    ∃ e', v = .vector .long ny e' none ∧ Enc.WF .long ny e' := by
  cases hd : denseWidth t with
  | some w =>
    obtain ⟨hb, -⟩ := denseWidth_gates hd
    have hw : t.width = some w := by cases t <;> simp_all [denseWidth]
    have hw0 : 0 < w := by cases t <;> simp_all [denseWidth, QAtomicType.width] <;> omega
    have hwU := width_toNat hw
    rw [findColumn_dense hd] at h
    split at h
    · split at h
      · rename_i ks hks
        obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨ks', hks', hsz⟩ := bytesOf_size hb hw hy (countFits_lt hn)
        rw [hks] at hks'; cases hks'
        exact long_answer (by rw [findSorted_size hwU ho, hsz, Nat.mul_div_cancel _ hw0])
      · cases h
    · obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.1 h
      exact long_answer (probeColumns_find_size hb hw hw0 hy hn ho)
  | none =>
    cases t <;> simp [denseWidth, QAtomicType.width] at hd
    case general => cases ex <;> simp [Enc.WF, QAtomicType.width] at hx; cases h
    case symbol => exact absurd rfl ht
    case boolean =>
      cases ex <;> cases ey <;> simp [Enc.WF, QAtomicType.width] at hx hy
      rw [findColumn_bits] at h; cases h
      exact ⟨_, rfl, by simp [Enc.WF, QAtomicType.width, findBitVec_size, USize.toNat_ofNat_of_lt' hn]⟩
    case guid =>
      cases ex <;> cases ey <;> simp [Enc.WF, QAtomicType.width] at hx hy
      rw [findColumn_guid] at h; cases h
      exact ⟨_, rfl, by simp [Enc.WF, QAtomicType.width, findVec_size, hy]⟩

/-- **`x bin y` answers one long per needle** at every type with a fixed-width or bit layout. -/
theorem binColumn_wf {t : QAtomicType} {r : Bool} {nx ny : Nat} {ex ey : Enc} {a : Option (UInt8 × IndexCell)}
    {v : QValue} (hx : Enc.WF t nx ex) (hy : Enc.WF t ny ey) (ht : t ≠ .symbol) (hn : ny < USize.size)
    (h : binColumn t r nx ex (.vector t ny ey a) = some v) :
    ∃ e', v = .vector .long ny e' none ∧ Enc.WF .long ny e' := by
  cases hd : denseWidth t with
  | some w =>
    obtain ⟨hb, -⟩ := denseWidth_gates hd
    have hw : t.width = some w := by cases t <;> simp_all [denseWidth]
    have hw0 : 0 < w := by cases t <;> simp_all [denseWidth, QAtomicType.width] <;> omega
    have hwU := width_toNat hw
    rw [binColumn_dense hd] at h
    cases h1 : operand t nx ex with
    | none => simp [h1] at h
    | some s1 =>
      cases h2 : operand t ny ey with
      | none => simp [h1, h2] at h
      | some s2 =>
        obtain ⟨a1, a2, a3⟩ := s1
        obtain ⟨b1, b2, b3⟩ := s2
        have hs := operandBytes_size hb hw hy hn h2
        simp only [h1, h2, Option.bind_some] at h
        cases h
        exact ⟨_, rfl, by simp [Enc.WF, QAtomicType.width, binOperands, binBytes_size, hs, hwU,
          Nat.mul_div_cancel _ hw0]⟩
  | none =>
    cases t <;> simp [denseWidth, QAtomicType.width] at hd
    case general => cases ex <;> simp [Enc.WF, QAtomicType.width] at hx; cases h
    case symbol => exact absurd rfl ht
    case boolean =>
      cases ex <;> cases ey <;> simp [Enc.WF, QAtomicType.width] at hx hy
      rw [binColumn_bits] at h; cases h
      exact ⟨_, rfl, by simp [Enc.WF, QAtomicType.width, binBits_size, USize.toNat_ofNat_of_lt' hn]⟩
    case guid =>
      cases ex <;> cases ey <;> simp [Enc.WF, QAtomicType.width] at hx hy
      rw [binColumn_guid] at h; cases h
      exact ⟨_, rfl, by simp [Enc.WF, QAtomicType.width, binWide_size, hy]⟩

end LeetQ.Rel.KernelWF
