/-
  The atom read-back of two razed parts at every encoding `razeColumn` reads: `razeTo`'s list is the parts'
  lists one after another. The dense path decodes every part through `Enc.bytesOf` (`get_bytesOf`: an element
  of the decode is the part's element), the ALP path re-encodes the join (`Verify.elemsW_concatALP`).
-/
import LeetQ.Rel.KernelWF.RazeRowAll
import QLean.Verify.Raw
import QLean.Verify.AlpConcat

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg

/-- A type with a width other than `guid` is at most eight bytes wide. -/
theorem width_le8 {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hg : t ≠ .guid) : w ≤ 8 := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hg | decide

/-- A width up to eight survives `toUSize`. -/
theorem toUSize_toNat_le8 {w : Nat} (hw8 : w ≤ 8) : w.toUSize.toNat = w :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))

/-- A dense element at a type of width `w`, other than `boolean` and `guid`, is its `w` bytes' atom. -/
theorem get_bytes_eq {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) {n : USize} (b : ByteArray) {i : Nat} (hi : i < n.toNat) :
    Enc.get t n (.bytes b) i =
      some (Column.atomOfBits t (Column.bitsAt b (i * w) w) (QAtomicType.ne_general_of_width hw)) := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hb | exact absurd rfl hg |
      (simp only [Enc.get, hi, ↓reduceIte, QAtomicType.width] <;> rfl)

/-- A Frame-of-Reference element is its `foRBits` atom. -/
theorem get_foR_eq {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) {n : USize} (md pk : ByteArray) {i : Nat} (hi : i < n.toNat) :
    Enc.get t n (.foR md pk) i =
      some (Column.atomOfBits t (Column.foRBits md pk #[] i) (QAtomicType.ne_general_of_width hw)) := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hb | exact absurd rfl hg |
      (simp only [Enc.get, hi, ↓reduceIte, QAtomicType.width] <;> rfl)

/-- An ALP element is its `alpBits` atom. -/
theorem get_alp_eq {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) {n : USize} (md pk a : ByteArray) {i : Nat} (hi : i < n.toNat) :
    Enc.get t n (.alp md pk a) i =
      some (Column.atomOfBits t (Column.alpBits md pk a #[] i) (QAtomicType.ne_general_of_width hw)) := by
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
    first | exact absurd rfl hb | exact absurd rfl hg |
      (simp only [Enc.get, hi, ↓reduceIte, QAtomicType.width] <;> rfl)

/-- `alpBits` with no hoisted table reads the start `blockStarts` holds (`foRBits_starts`). -/
theorem alpBits_starts (md pk a : ByteArray) (i : Nat) :
    Column.alpBits md pk a #[] i = Column.alpBits md pk a (Column.blockStarts md) i := by
  unfold Column.alpBits; rw [foRBits_starts]

/-- **An element of a payload's dense decode is the payload's element**, at every well-formed payload of a type
    with a width other than `boolean`: `.bytes` is itself, `.foR` decodes to `foRBits`' low `8w` bits
    (`decodeW`), all `atomOfBits` reads (`atomOfBits_mod`), `.alp` to `alpBits` (`elemsW_alpDecode_alpBits`). -/
theorem get_bytesOf {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) {n : USize}
    {e : Enc} (hwf : Enc.WF t n e) {b : ByteArray} (he : Enc.bytesOf t n e = some b) {i : Nat}
    (hi : i < n.toNat) : Enc.get t n (.bytes b) i = Enc.get t n e i := by
  obtain ⟨b', hb', hs⟩ := bytesOf_size hb hw hwf
  rw [he, Option.some.injEq] at hb'; subst hb'
  cases e
  case bytes b' => simp only [Enc.bytesOf, Option.some.injEq] at he; subst he; rfl
  case foR md pk =>
    have hg : t ≠ .guid := by rintro rfl; simp [Enc.WF] at hwf
    have hwu := toUSize_toNat_le8 (width_le8 hw hg)
    simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at he; subst he
    have hd := (Verify.decodeW w.toUSize (by rw [hwu]; exact width_le8 hw hg) md pk n).2 i hi
    rw [hwu] at hd
    rw [get_bytes_eq hw hb hg _ hi, get_foR_eq hw hb hg _ _ hi, hd, foRBits_starts, Verify.atomOfBits_mod hw hb hg]
  case alp md pk a =>
    have hg : t ≠ .guid := by rintro rfl; simp [Enc.WF] at hwf
    have hwu := toUSize_toNat_le8 (width_le8 hw hg)
    have hw0 : 0 < w := by
      cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;> decide
    have hesz : Column.alpEsz a = w := by
      cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
        simp_all [Enc.WF, Column.alpEsz, QAtomicType.width]
    simp only [Enc.bytesOf, hw, Option.map_some, Option.some.injEq] at he; subst he
    have hel := Verify.elemsW_alpDecode_alpBits md pk a n w.toUSize (by rw [hwu, hesz])
    rw [hwu] at hel
    have h1 : i < (Verify.elemsW w (Coc.alpDecode w.toUSize md pk a n)).length := by
      simp only [Verify.elemsW, List.length_map, List.length_range, hs, Nat.mul_div_cancel _ hw0]; exact hi
    have hx := List.getElem_of_eq hel h1
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range] at hx
    rw [get_bytes_eq hw hb hg _ hi, get_alp_eq hw hb hg _ _ _ hi, hx, alpBits_starts]
  all_goals simp [Enc.bytesOf] at he

/-- A column's list is its elements read off its dense decode `Enc.bytesOf`, at every encoding. -/
theorem toList_bytesOf {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) {n : USize}
    (x : Arr t n) {b : ByteArray} (hx : Enc.bytesOf t n x.enc = some b) :
    x.toList = ((List.range n.toNat).map fun i => Enc.get t n (.bytes b) i).map
      fun o => (o.bind fun a => Carrier.of? t (.atom a)).getD default := by
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  apply List.ext_getElem (by simp [Arr.length_toList])
  intro j h1 h2
  have hj : j < n.toNat := by simpa [Arr.length_toList] using h1
  rw [Arr.getElem_toList, Arr.get_ne _ _ hg]
  simp only [List.getElem_map, List.getElem_range]
  rw [get_bytesOf hw hb x.wf hx hj]

/-- `razeColumn` where it answers dense — no part is encoded to meet (`encodedParts = none`), or the encoded
    join is the dearer (`denseCheaper`) — at a type with a width other than `boolean`: the parts' decodes end
    to end. -/
theorem razeColumn_dense {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    {cs : Array (USize × Enc)} (hwf : ∀ c ∈ cs, Enc.WF t c.1 c.2)
    (hD : ∀ r, encodedParts t cs = some r → denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w)
      (straddles (r.2.2.1.map (·.toNat))) = true)
    {v : QValue} (hv : razeColumn t cs = some v) :
    v = .vector t (cs.foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize
      (.bytes (concatBytes (cs.map fun c => (Enc.bytesOf t c.1 c.2).getD .empty))) none := by
  have hm : cs.mapM (fun (c : USize × Enc) => Enc.bytesOf t c.1 c.2) =
      some (cs.map fun c => (Enc.bytesOf t c.1 c.2).getD .empty) :=
    mapM_some _ fun c hc => by obtain ⟨b, hb', -⟩ := bytesOf_size hb hw (hwf c hc); simp [hb']
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases hE : encodedParts t cs with
  | none =>
    cases t
    case boolean => exact absurd rfl hb
    case symbol => simp [QAtomicType.width] at hw
    case general => simp [QAtomicType.width] at hw
    all_goals
      simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
      simp only [QAtomicType.width, hE, hm] at hv
      obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
      cases hv; rfl
  | some r =>
    have hC := hD r hE
    obtain ⟨alp, N, ns, ms, ps, as⟩ := r
    dsimp only at hC
    cases t
    case boolean => exact absurd rfl hb
    case symbol => simp [QAtomicType.width] at hw
    case general => simp [QAtomicType.width] at hw
    all_goals
      simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
      simp only [QAtomicType.width, hE, hC, ↓reduceIte, hm] at hv
      obtain ⟨hc, hv⟩ := needSize_some (ite_none_some hv)
      cases hv; rfl

/-- **`razeTo` where `razeColumn` answers dense**: the razed column lists its parts' elements one part after
    another, whatever each part's encoding. -/
theorem razeTo_toList_dense {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (cs : Array ((k : USize) × Arr t k)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size)
    (hD : ∀ r, encodedParts t (cs.map (·.2.part)) = some r → denseCheaper (if r.1 then 8 else 5) r.2.1
      (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = true) :
    (razeTo t cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  unfold razeTo; rw [cast_toList]
  rcases cs with ⟨l⟩
  unfold raze
  by_cases h0 : l = []
  · subst h0
    have e0 : ({ toList := [] } : Array ((k : USize) × Arr t k)).size = 0 := rfl
    rw [dif_pos e0]
    exact (List.eq_nil_of_length_eq_zero (by rw [Arr.length_toList, empty_len]; rfl)).trans rfl
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  rw [dif_neg (by simpa using h0), dif_neg hg]
  by_cases h1 : l.length = 1
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1; simp
  rw [dif_neg (by simpa using h1)]
  dsimp only
  have key : ∀ (a : Nat) (l : List ((n : USize) × Arr t n)),
      (l.map fun x => (x.1, x.2.enc)).foldl (fun s c => s + c.1.toNat) a = a + (l.map (·.1.toNat)).sum := by
    intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
  have hk : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 = (l.map (·.1.toNat)).sum := by
    simpa [Arr.part] using key 0 l
  have hsum : (l.map (·.1.toNat)).sum = S := by simpa using hs
  have hf : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 < USize.size := by
    rw [hk, hsum]; exact hS
  unfold need; rw [dif_pos hf]
  have hpw : ∀ c ∈ (List.toArray l).map (·.2.part), Enc.WF t c.1 c.2 := by
    intro c hc; obtain ⟨d, -, rfl⟩ := Array.mem_map.1 hc; exact d.2.wf
  let gb : ((n : USize) × Arr t n) → ByteArray := fun c => (Enc.bytesOf t c.1 c.2.enc).getD .empty
  have hB : concatBytes (((List.toArray l).map (·.2.part)).map fun c => (Enc.bytesOf t c.1 c.2).getD .empty) =
      l.foldl (fun a c => a ++ gb c) .empty := by
    simp only [concatBytes, Array.foldl_map, List.foldl_toArray', Arr.part, gb]
  have hv : ∀ h, ((razeColumn t ((List.toArray l).map (·.2.part))).get h) =
      .vector t (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize
        (.bytes (l.foldl (fun a c => a ++ gb c) .empty)) none := fun h => by
    rw [← hB]; exact razeColumn_dense hw hb hpw hD (Option.some_get h).symm
  have hgb : ∀ c ∈ l, Enc.bytesOf t c.1 c.2.enc = some (gb c) := fun c _ => by
    obtain ⟨b, hb', -⟩ := bytesOf_size hb hw c.2.wf; simp [gb, hb']
  have hsz : ∀ c ∈ l, (gb c).size = c.1.toNat * w := fun c _ => by
    obtain ⟨b, hb', hs⟩ := bytesOf_size hb hw c.2.wf
    simp only [gb, hb', Option.getD_some]; exact hs
  have hN : (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize.toNat =
      (l.map (·.1.toNat)).sum := by rw [USize.toNat_ofNat_of_lt' hf, hk]
  refine (toList_bytes _ (b := l.foldl (fun a c => a ++ gb c) .empty) (by simp only [Arr.enc, hv]) hg).trans ?_
  have hF := foldl_bytes_get hw
    (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize gb l .empty 0
    (by rw [Nat.zero_mul]; rfl) hsz (by rw [hN]; omega)
  rw [Nat.zero_add, List.range_zero, List.map_nil, List.nil_append] at hF
  rw [hN, hF, List.map_flatMap]
  unfold List.flatMap; congr 1
  apply List.map_congr_left; intro c hc
  rw [toList_bytesOf hw hb c.2 (hgb c hc)]

/-- Two parts' `razeTo` list where `razeColumn` answers dense (`razeTo_toList_dense`). -/
theorem razeTo2_dense {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) {n m : USize}
    (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hD : ∀ r, encodedParts t #[x.part, y.part] = some r → denseCheaper (if r.1 then 8 else 5) r.2.1
      (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = true) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  razeTo2_toList x y hN (razeTo_toList_dense hw hb _ rfl hN (by simpa using hD))

end LeetQ.Rel.KernelWF
