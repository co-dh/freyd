/-
  The atom read-back of two razed parts at every encoding `razeColumn` reads: `razeTo`'s list is the parts'
  lists one after another. The dense path decodes every part through `Enc.bytesOf` (`get_bytesOf`: an element
  of the decode is the part's element), the ALP path re-encodes the join (`Verify.elemsW_concatALP`).
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

/-- **Two parts' `razeTo` list at every type and encoding but the encoded join**: `razeTo2_fits` at `boolean`,
    `general`, `symbol`, `guid`, `razeTo2_dense` wherever `razeColumn` answers dense. `hD`: the parts take the
    dense branch — no part is encoded to meet, or the encoded join is the dearer (`denseCheaper`). -/
theorem razeTo2_all {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hF : Vals.RazeFits (.atom t) x y)
    (hD : ∀ w r, t.width = some w → encodedParts t #[x.part, y.part] = some r →
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
    exact razeTo2_dense hw (fun h => hs (.inl h)) x y hN (fun r hr => hD w r hw hr)

section
-- The read-back left open: two atom parts on the encoded join, razeColumn's concatALP/concatFoR branch.
variable (hJ : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y → ∀ w r, t.width = some w →
    encodedParts t #[x.part, y.part] = some r →
    denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat))) = false →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
include hJ

/-- `raze_row`'s `hat` from `razeTo2_all` and the encoded join `hJ`. -/
theorem hat_of_join : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  intro t n m x y hN hF
  cases hW : t.width with
  | none => exact razeTo2_all x y hN hF fun w r hw _ => by rw [hW] at hw; cases hw
  | some w =>
    cases hE : encodedParts t #[x.part, y.part] with
    | none => exact razeTo2_all x y hN hF fun w' r _ hr => by rw [hE] at hr; cases hr
    | some r =>
      cases hC : denseCheaper (if r.1 then 8 else 5) r.2.1 (if r.1 then 8 else w) (straddles (r.2.2.1.map (·.toNat)))
      · exact hJ t x y hN hF w r hW hE hC
      · exact razeTo2_all x y hN hF fun w' r' hw' hr' => by
          rw [hW, Option.some.injEq] at hw'; rw [hE, Option.some.injEq] at hr'; subst hw' hr'; exact hC

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

-- dup of RazeRow's local notations `Uc`, `kcU`, `vcU`, `nubU` (local there, and in RazeRowAll)
set_option hygiene false in
local notation "Uc" => (⟨_, A.raze #[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] hNk, B.raze #[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] hNv⟩ : Rel A B)
set_option hygiene false in
local notation "kcU" => (Obj.codes _ (#v[⟨(Uc).n, (Uc).key⟩] : Vector (Part _) 1))[0]
set_option hygiene false in
local notation "vcU" => (Obj.codes _ (#v[⟨(Uc).n, (Uc).val⟩] : Vector (Part _) 1))[0]
set_option hygiene false in
local notation "nubU" => (tuples.tupleIds kcU #[vcU]).2

section
-- The read-back left open: two atom parts on the encoded join (`hat_of_join`).
variable (hJ : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y → ∀ w r, t.width = some w →
    encodedParts t #[x.part, y.part] = some r →
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
#print axioms raze_row_all
#print axioms rep_union_all
#print axioms rep_junc_all

end LeetQ.Rel.Rep
