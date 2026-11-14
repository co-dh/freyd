/-
  The atom read-back of two razed parts at every encoding `razeColumn` reads: `razeTo`'s list is the parts'
  lists one after another. The dense path decodes every part through `Enc.bytesOf` (`get_bytesOf`: an element
  of the decode is the part's element), the ALP join reads the parts' `alpBits` end to end (`Verify.elemsW_concatALP`);
  the Frame-of-Reference join (`concatFoR`) is left open as `hJ`.
-/
import LeetQ.Rel.KernelWF.RazeRowAll
import QLean.Verify.Raw
import QLean.Verify.AlpConcat

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

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

-- dup of Raze.need_some (private there)
private theorem need_some {α : Type} {p : Prop} [Decidable p] {msg : Unit → String} {k : p → Option α} {v : α}
    (h : need p msg (fun _ => none) k = some v) : ∃ hp : p, k hp = some v := by
  by_cases hp : p
  · exact ⟨hp, by simpa [need, hp] using h⟩
  · simp [need, hp, stop] at h

-- dup of Raze.alp_width (private there)
private theorem alp_width {t : QAtomicType} {w : Nat} (ht : Column.alpEncodes t = true) (hw : t.width = some w) :
    (if (w == 4) = true then 4 else 8) = w ∧ 0 < w := by
  cases t <;> simp_all [Column.alpEncodes, QAtomicType.width] <;> subst hw <;> decide

/-- A width up to eight is `4` as a `USize` exactly when it is `4`. -/
theorem toUSize_beq4 {w : Nat} (hw8 : w ≤ 8) : (w.toUSize == 4) = (w == 4) := by
  have h4 : (4 : USize).toNat = 4 := toUSize_toNat_le8 (w := 4) (by decide)
  apply Bool.eq_iff_iff.2; simp only [beq_iff_eq]
  constructor
  · intro h; have := congrArg USize.toNat h; rwa [toUSize_toNat_le8 hw8, h4] at this
  · rintro rfl; rfl

/-- A column's list is its elements read off its payload, at every encoding. -/
theorem toList_get {t : QAtomicType} {n : USize} (x : Arr t n) (hg : t ≠ .general) :
    x.toList = (List.range n.toNat).map fun i =>
      ((Enc.get t n x.enc i).bind fun a => Carrier.of? t (.atom a)).getD default := by
  apply List.ext_getElem (by simp [Arr.length_toList])
  intro j h1 h2
  rw [Arr.getElem_toList, Arr.get_ne _ _ hg]; simp

/-- **`razeTo` of two or more parts read off `razeColumn`'s answer**: its list is `L` when every vector
    `razeColumn` answers, of the parts' total count, lists `L`. -/
theorem razeTo_toList_of {t : QAtomicType} (hg : t ≠ .general) (cs : Array ((k : USize) × Arr t k)) {S : Nat}
    (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) (h2 : 2 ≤ cs.size) {L : List (Carrier t)}
    (hL : ∀ c E a, razeColumn t (cs.map (·.2.part)) = some (.vector t c E a) → c.toNat = S →
      (List.range S).map (fun k => ((Enc.get t c E k).bind fun a => Carrier.of? t (.atom a)).getD default) = L) :
    (razeTo t cs hs hS).toList = L := by
  unfold razeTo; rw [cast_toList]
  rcases cs with ⟨l⟩
  unfold raze
  have hl2 : 2 ≤ l.length := h2
  rw [dif_neg (fun h => by have : l.length = 0 := h; omega), dif_neg hg,
    dif_neg (fun h => by have : l.length = 1 := h; omega)]
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
  have aux : ∀ (k : USize) (R : Arr t k) h, R.1 = Option.get (razeColumn t ((List.toArray l).map (·.2.part))) h →
      k.toNat = S → R.toList = L := by
    intro k R h hR hkS
    have hv : razeColumn t ((List.toArray l).map (·.2.part)) = some (.vector t k R.enc R.attrCell) := by
      rw [← Arr.val_eq, hR, Option.some_get]
    rw [toList_get R hg, hkS]; exact hL k R.enc R.attrCell hv hkS
  exact aux _ _ _ rfl (by rw [USize.toNat_ofNat_of_lt' hf, hk, hsum])

/-- **`Enc.answer` keeps an encoded payload's elements**: it keeps the payload or decodes it (`get_bytesOf`). -/
theorem get_answer {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) {n : USize} {e : Enc}
    (hwf : Enc.WF t n e) (he : ∀ b, e ≠ .bytes b) {i : Nat} (hi : i < n.toNat) :
    Enc.get t n (Enc.answer t n e) i = Enc.get t n e i := by
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  have hw' := hw
  obtain ⟨b, hbo, -⟩ := bytesOf_size hb hw hwf
  have hd := get_bytesOf hw hb hwf hbo hi
  cases e
  case bytes b' => exact absurd rfl (he b')
  all_goals
    cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw' <;> (try subst hw') <;>
      first | exact absurd rfl hg | (simp only [Enc.answer, QAtomicType.width, hbo] <;> split <;> first | rfl | exact hd)

/-- At a float type, `encodedParts`' `k`-th `(meta, pack, alp)` is part `k`'s own ALP payload or its `Enc.alpOf`. -/
theorem encodedParts_alp {t : QAtomicType} (ht : Column.alpEncodes t = true) {cs : Array (USize × Enc)} {N : Nat}
    {ns : Array USize} {ms ps as : Array ByteArray} (hE : encodedParts t cs = some (true, N, ns, ms, ps, as))
    (k : Nat) (hk : k < cs.size) :
    ∃ (hm : k < ms.size) (hp : k < ps.size) (ha : k < as.size), cs[k].2 = .alp ms[k] ps[k] as[k] ∨
      Enc.alpOf t cs[k].1 cs[k].2 = some (.alp ms[k] ps[k] as[k]) := by
  unfold encodedParts at hE
  dsimp only at hE
  split at hE
  · cases hE
  simp only [bind, Option.bind] at hE
  split at hE
  · cases hE
  rename_i qs hq
  simp only [Option.some.injEq, Prod.mk.injEq] at hE
  obtain ⟨-, -, -, rfl, rfl, rfl⟩ := hE
  obtain ⟨hs, hf⟩ := mapM_getElem hq
  have hqk := hf k hk
  refine ⟨by simp [hs, hk], by simp [hs, hk], by simp [hs, hk], ?_⟩
  simp only [Array.getElem_map]
  rcases hc : cs[k] with ⟨nk, ek⟩
  rw [hc] at hqk
  cases ek
  case alp m p a =>
    simp only [ht, ↓reduceIte, Option.some.injEq] at hqk
    left; simp only [← hqk]
  case foR m p => simp [ht] at hqk
  all_goals
    right
    simp only [ht, ↓reduceIte] at hqk
    split at hqk
    · rename_i m p a hal
      simp only [Option.some.injEq] at hqk
      simp only [← hqk]; exact hal
    · cases hqk

/-- **A part an ALP join reads**, its own ALP payload or its `Enc.alpOf`: the blob is at the type's width, and
    element `i` is the payload's `alpBits`. `hn`: the part's count fits ALP's 32-bit counts. -/
theorem alp_part {t : QAtomicType} {w : Nat} (ht : Column.alpEncodes t = true) (hw : t.width = some w)
    {n : USize} {e : Enc} (hwf : Enc.WF t n e) (hn : n.toNat < 2 ^ 32) {md pk a : ByteArray}
    (he : e = .alp md pk a ∨ Enc.alpOf t n e = some (.alp md pk a)) :
    Column.alpF32 a = (w == 4) ∧ ∀ i < n.toNat, Enc.get t n e i =
      some (Column.atomOfBits t (Column.alpBits md pk a (Column.blockStarts md) i)
        (QAtomicType.ne_general_of_width hw)) := by
  have hb : t ≠ .boolean := by rintro rfl; simp [Column.alpEncodes] at ht
  have hg : t ≠ .guid := by rintro rfl; simp [Column.alpEncodes] at ht
  obtain ⟨h48, h0⟩ := alp_width ht hw
  rcases he with rfl | he
  · have hesz : Column.alpEsz a = w := by
      cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw <;> (try subst hw) <;>
        simp_all [Enc.WF, Column.alpEsz, QAtomicType.width]
    refine ⟨?_, fun i hi => by rw [get_alp_eq hw hb hg _ _ _ hi, alpBits_starts]⟩
    unfold Column.alpEsz at hesz
    cases hf : Column.alpF32 a <;> simp [hf] at hesz <;> subst hesz <;> decide
  · obtain ⟨b, hbo, hbs⟩ := bytesOf_size hb hw hwf
    have hE : Coc.alpEncodeAt (w == 4) b = (md, pk, a) := by
      unfold Enc.alpOf at he
      simp only [ht, hw, hbo, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at he
      have h4 : (if w == 4 then Coc.alpEncode32 b else Coc.alpEncode64 b) = Coc.alpEncodeAt (w == 4) b := by
        cases (w == 4) <;> rfl
      rw [h4] at he
      rcases hX : Coc.alpEncodeAt (w == 4) b with ⟨m', p', a'⟩
      simp only [hX, Option.some.injEq, Enc.alp.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he; rfl
    have H := Verify.alpBits_alpEncodeAt (w == 4) w h48 b (by rw [hbs, Nat.mul_div_cancel _ h0]; exact hn)
    simp only [hE] at H
    refine ⟨H.1, fun i hi => ?_⟩
    rw [← get_bytesOf hw hb hwf hbo hi, get_bytes_eq hw hb hg _ hi,
      H.2 i (by rw [hbs, Nat.mul_div_cancel _ h0]; exact hi)]

/-- `razeColumn`'s ALP join: the vector of the parts' total count whose payload is `Enc.answer` of
    `concatALP`'s. -/
theorem razeColumn_alp {t : QAtomicType} {w : Nat} (hw : t.width = some w) (ht : Column.alpEncodes t = true)
    {cs : Array (USize × Enc)} {N : Nat} {ns : Array USize} {ms ps as : Array ByteArray}
    (hE : encodedParts t cs = some (true, N, ns, ms, ps, as))
    (hC : denseCheaper 8 N 8 (straddles (ns.map (·.toNat))) = false)
    {M P A : ByteArray} (hX : concatALP w.toUSize (countBytes ns) ms ps as = (M, P, A))
    {v : QValue} (hv : razeColumn t cs = some v) :
    ∃ _ : N < USize.size, v = .vector t N.toUSize (Enc.answer t N.toUSize (.alp M P A)) none := by
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases t
  all_goals first | (simp [Column.alpEncodes] at ht; done) | skip
  all_goals
    simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
    simp only [QAtomicType.width, hE, ↓reduceIte, hC, Bool.false_eq_true] at hv
    obtain ⟨hc, hv⟩ := needSize_some hv
    obtain ⟨-, hv⟩ := need_some hv
    simp only [↓reduceIte, hX] at hv
    cases hv; exact ⟨hc, rfl⟩

/-- **Two parts' `razeTo` list on the ALP join** (`encodedParts`' flag `true`, the join not the dearer): the
    join's elements are the parts' `alpBits` one part after another (`Verify.elemsW_concatALP`), and each part's
    are its elements (`alp_part`). -/
theorem razeTo2_join_alp {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hF : Vals.RazeFits (.atom t) x y) {w : Nat} {r} (hw : t.width = some w)
    (hE : encodedParts t #[x.part, y.part] = some r) (hr : r.1 = true)
    (hC : denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = false) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  obtain ⟨alp, N, ns, ms, ps, as⟩ := r
  dsimp only at hr; subst hr
  have hC' : denseCheaper 8 N 8 (straddles (ns.map (·.toNat))) = false := hC
  obtain ⟨hal, hns, hNv, hms, hps, has, -⟩ := encodedParts_spec hE
  have ht : Column.alpEncodes t = true := hal.symm
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  have hb : t ≠ .boolean := by rintro rfl; simp [Column.alpEncodes] at ht
  have hg8 : t ≠ .guid := by rintro rfl; simp [Column.alpEncodes] at ht
  obtain ⟨h48, h0⟩ := alp_width ht hw
  have hw48 : w = 4 ∨ w = 8 := by revert h48; split <;> omega
  have hw8 : w ≤ 8 := by omega
  have hnm := hF.2 ht
  have hns' : ns = #[n, m] := by rw [hns]; simp [Arr.part]
  subst hns'
  have hNv' : N = n.toNat + m.toNat := by rw [hNv]; simp
  have hNlt : N < USize.size := by rw [hNv']; simpa using hN
  have hNU : N.toUSize.toNat = N := USize.toNat_ofNat_of_lt' hNlt
  obtain ⟨hk0, hp0, ha0, he0⟩ := encodedParts_alp ht hE 0 (by simp)
  obtain ⟨hk1, hp1, ha1, he1⟩ := encodedParts_alp ht hE 1 (by simp)
  have he0' : x.enc = .alp ms[0] ps[0] as[0] ∨ Enc.alpOf t n x.enc = some (.alp ms[0] ps[0] as[0]) := he0
  have he1' : y.enc = .alp ms[1] ps[1] as[1] ∨ Enc.alpOf t m y.enc = some (.alp ms[1] ps[1] as[1]) := he1
  obtain ⟨hf0, hx0⟩ := alp_part ht hw x.wf (by omega) he0'
  obtain ⟨hf1, hx1⟩ := alp_part ht hw y.wf (by omega) he1'
  have hb0 : (Column.bitsAt (countBytes #[n, m]) 0 8).toNat = n.toNat := by
    have h := countBytes_get #[n, m] 0 (by simp); simp only [Nat.mul_zero] at h; rw [h]
    exact USize.toNat_toUInt64 n
  have hb1 : (Column.bitsAt (countBytes #[n, m]) 8 8).toNat = m.toNat := by
    have h := countBytes_get #[n, m] 1 (by simp); simp only [Nat.mul_one] at h; rw [h]
    exact USize.toNat_toUInt64 m
  have hr2 : List.range 2 = [0, 1] := rfl
  have hb4 := toUSize_beq4 hw8
  have hU : (if (w == 4) = true then (4 : USize) else 8) = w.toUSize := by
    rcases hw48 with rfl | rfl <;> rfl
  have hA := Verify.elemsW_concatALP w.toUSize (countBytes #[n, m]) ms ps as 2
    (by rw [countBytes_size, hms, hps, has]; simp)
    (fun k hk => by
      rw [hb4]
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [getElem!_pos as 0 ha0]; exact hf0
      · rw [getElem!_pos as 1 ha1]; exact hf1)
    (fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [Nat.mul_zero, hb0]; exact Nat.lt_of_lt_of_le (by omega) USize.le_size
      · rw [Nat.mul_one, hb1]; exact Nat.lt_of_lt_of_le (by omega) USize.le_size)
    (by
      rw [hr2]
      simp only [List.map_cons, List.map_nil, Nat.mul_zero, Nat.mul_one, hb0, hb1, List.sum_cons, List.sum_nil]
      omega)
  rcases hX : concatALP w.toUSize (countBytes #[n, m]) ms ps as with ⟨M, P, A⟩
  simp only [hX, hb4, h48, hU, hr2, List.map_cons, List.map_nil, Nat.mul_zero, Nat.mul_one, hb0, hb1,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.flatten_cons, List.flatten_nil, List.append_nil,
    getElem!_pos ms 0 hk0, getElem!_pos ms 1 hk1, getElem!_pos ps 0 hp0, getElem!_pos ps 1 hp1,
    getElem!_pos as 0 ha0, getElem!_pos as 1 ha1, ← hNv'] at hA
  have hesz : w.toUSize.toNat = Column.alpEsz A := by
    rw [toUSize_toNat_le8 hw8]; unfold Column.alpEsz; rw [hA.1]; exact h48.symm
  have h2 := Verify.elemsW_alpDecode_alpBits M P A N.toUSize w.toUSize hesz
  rw [toUSize_toNat_le8 hw8, hNU] at h2
  have hL := h2.symm.trans hA.2
  have hwfA : Enc.WF t N.toUSize (.alp M P A) :=
    concatALP_wf hX ht hw hms hps has (by rw [hNU, hNv']; simp)
  have hl : ∀ {k : USize} (e : Enc) (f : Nat → UInt64), (∀ i < k.toNat, Enc.get t k e i =
      some (Column.atomOfBits t (f i) (QAtomicType.ne_general_of_width hw))) →
      (List.range k.toNat).map (fun i => ((Enc.get t k e i).bind fun a => Carrier.of? t (.atom a)).getD default) =
        ((List.range k.toNat).map f).map fun b =>
          ((some (Column.atomOfBits t b (QAtomicType.ne_general_of_width hw))).bind
            fun a => Carrier.of? t (.atom a)).getD default := by
    intro k e f h; rw [List.map_map]; apply List.map_congr_left; intro i hi; rw [h i (List.mem_range.1 hi)]; rfl
  refine razeTo_toList_of hg _ rfl hN (by simp) ?_
  intro c E a hv hc
  rw [show ((#[⟨n, x⟩, ⟨m, y⟩] : Array ((k : USize) × Arr t k)).map (·.2.part)) = #[x.part, y.part] by simp] at hv
  obtain ⟨-, hv⟩ := razeColumn_alp hw ht hE hC' hX hv
  simp only [QValue.vector.injEq] at hv
  obtain ⟨-, rfl, rfl, rfl⟩ := hv
  rw [← hc, hl _ (Column.alpBits M P A (Column.blockStarts M)) (fun i hi => by
      rw [get_answer hw hb hwfA (by intro _ h; cases h) hi, get_alp_eq hw hb hg8 _ _ _ hi, alpBits_starts]),
    hNU, hL, toList_get x hg, toList_get y hg, hl _ _ hx0, hl _ _ hx1, List.map_append]

/-- **Two parts' `razeTo` list at every type and encoding but the Frame-of-Reference join**: `razeTo2_fits` at
    `boolean`, `general`, `symbol`, `guid`, `razeTo2_join_alp` on the ALP join, `razeTo2_dense` wherever
    `razeColumn` answers dense. `hD`, on the encoding only: where `encodedParts` joins Frame of Reference
    (flag `false`), the join is the dearer (`denseCheaper`), so `razeColumn` answers dense. -/
theorem razeTo2_all {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hF : Vals.RazeFits (.atom t) x y)
    (hD : ∀ w r, t.width = some w → encodedParts t #[x.part, y.part] = some r → r.1 = false →
      denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = true) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  by_cases hs : t = .boolean ∨ t = .general ∨ t = .symbol ∨ t = .guid
  · exact razeTo2_fits x y hN hF (by
      rcases hs with h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h))))
  · obtain ⟨w, hw⟩ : ∃ w, t.width = some w := by cases t <;> simp_all [QAtomicType.width]
    have hb : t ≠ .boolean := fun h => hs (.inl h)
    cases hE : encodedParts t #[x.part, y.part] with
    | none => exact razeTo2_dense hw hb x y hN fun r hr => by rw [hE] at hr; cases hr
    | some r =>
      cases hC : denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat)))
      · cases hr : r.1
        · exact absurd (hC.symm.trans (hD w r hw hE hr)) (by decide)
        · exact razeTo2_join_alp x y hN hF hw hE hr hC
      · exact razeTo2_dense hw hb x y hN fun r' hr' => by
          rw [hE, Option.some.injEq] at hr'; subst hr'; exact hC

section
-- The read-back left open: two atom parts on the Frame-of-Reference join (`encodedParts` flag `false`), concatFoR.
variable (hJ : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y → ∀ w r, t.width = some w →
    encodedParts t #[x.part, y.part] = some r → r.1 = false →
    denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = false →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
include hJ

/-- `raze_row`'s `hat` from `razeTo2_all` and the encoded join `hJ`. -/
theorem hat_of_join : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  intro t n m x y hN hF
  by_cases hj : ∃ w r, t.width = some w ∧ encodedParts t #[x.part, y.part] = some r ∧ r.1 = false ∧
      denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = false
  · obtain ⟨w, r, hW, hE, hr, hC⟩ := hj; exact hJ t x y hN hF w r hW hE hr hC
  · exact razeTo2_all x y hN hF fun w r hW hE hr => by
      cases hC : denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat)))
      · exact absurd ⟨w, r, hW, hE, hr, hC⟩ hj
      · rfl

/-- **Row read-back of `raze` at every side**, `raze_row` with `hat` narrowed to the encoded join `hJ`. -/
theorem raze_row_all (A : Obj) {n m : USize} (x : Vals A n) (y : Vals A m) (hF : Vals.RazeFits A x y)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part A)).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (k : Nat) (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part A)).toList.map
      fun c : Part A => c.1.toNat).sum.toUSize.toNat) :
    Vals.row (A.raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x ⟨k, h⟩
      else Vals.row y ⟨k - n.toNat, by have := raze2_cnt x y hN; omega⟩ :=
  raze_row (hat_of_join hJ) A x y hF hN k hk

end

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B C : Obj}

open RazeN

section
-- The read-back left open: two atom parts on the Frame-of-Reference join (`hat_of_join`).
variable (hJ : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y → ∀ w r, t.width = some w →
    encodedParts t #[x.part, y.part] = some r → r.1 = false →
    denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = false →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
include hJ

/-- **`rep (R ∪ S) = rep R ∪ rep S`**, `rep_union_fits` with `hat` narrowed to the encoded join `hJ`. -/
theorem rep_union_all (R S : Rel A B) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hNk : ((#[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Array (Part A)).toList.map fun c : Part A => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] : Array (Part B)).toList.map fun c : Part B => c.1.toNat).sum <
      USize.size)
    (hFk : Vals.RazeFits A R.key S.key) (hFv : Vals.RazeFits B R.val S.val)
    (hK : (∀ {i j : Nat} (hi : i < (Uc).n.toNat) (hj : j < (Uc).n.toNat),
        Column.idAt (kcU).b (kcU).w i = Column.idAt (kcU).b (kcU).w j ↔
          Vals.row (Uc).key ⟨i, hi⟩ = Vals.row (Uc).key ⟨j, hj⟩) ∧
      ((kcU).w = 1 ∨ (kcU).w = 2 ∨ (kcU).w = 4 ∨ (kcU).w = 8 ∨ (kcU).w = 16 ∨ (kcU).w = 32 ∨ (kcU).w = 64) ∧
        (kcU).n = (Uc).n ∧ (kcU).b.size = ((kcU).n.toNat * (kcU).w + 7) / 8 ∧
        ((kcU).w < 8 → (kcU).card < USize.size ∧ ∀ i < (kcU).n.toNat, Column.idAt (kcU).b (kcU).w i < (kcU).card))
    (hV : (∀ {i j : Nat} (hi : i < (Uc).n.toNat) (hj : j < (Uc).n.toNat),
        Column.idAt (vcU).b (vcU).w i = Column.idAt (vcU).b (vcU).w j ↔
          Vals.row (Uc).val ⟨i, hi⟩ = Vals.row (Uc).val ⟨j, hj⟩) ∧
      ((vcU).w = 1 ∨ (vcU).w = 2 ∨ (vcU).w = 4 ∨ (vcU).w = 8 ∨ (vcU).w = 16 ∨ (vcU).w = 32 ∨ (vcU).w = 64) ∧
        (vcU).n = (Uc).n ∧ (vcU).b.size = ((vcU).n.toNat * (vcU).w + 7) / 8 ∧
        ((vcU).w < 8 → (vcU).card < USize.size ∧ ∀ i < (vcU).n.toNat, Column.idAt (vcU).b (vcU).w i < (vcU).card))
    (hk : Vals.PickFits A (Uc).key (ids nubU)) (hv : Vals.PickFits B (Uc).val (ids nubU)) :
    rep (R ∪ S) = rep R ∪ rep S :=
  rep_union_fits (hat_of_join hJ) R S hN hNk hNv hFk hFv hK hV hk hv

/-- `rep_junc_fits` with `hat` narrowed to the encoded join `hJ`. -/
theorem rep_junc_all (R : Rel A C) (S : Rel B C) (hN : R.n.toNat + S.n.toNat < USize.size)
    (h63 : R.n.toNat + S.n.toNat ≤ 2 ^ 63) (hF : Vals.RazeFits C R.val S.val) :
    rep (LeetQ.Rel.Alg.junc R S) = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R) (rep S) :=
  rep_junc_fits (hat_of_join hJ) R S hN h63 hF

end

#print axioms razeTo2_all
#print axioms razeTo2_join_alp
#print axioms raze_row_all
#print axioms rep_union_all
#print axioms rep_junc_all

end LeetQ.Rel.Rep
