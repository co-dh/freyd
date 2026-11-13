/-
  The Frame-of-Reference join read back: two atom parts that `razeColumn` joins through `concatFoR` list their
  elements one part after the other. Each of `concatFoR`'s three answers — the blocks moved whole (`moveFoR`),
  the second part's residuals written into the first part's last block (`appendFoR`), the parts decoded,
  joined and encoded again — keeps element `i`'s low `8w` bits, which is all `atomOfBits` reads.
-/
import LeetQ.Rel.KernelWF.RazeEnc
import QLean.Verify.Alp

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- A type Frame of Reference encodes is two to eight bytes wide, and neither `boolean` nor `guid`. -/
theorem foR_width {t : QAtomicType} {w : Nat} (he : Column.encodes t = true) (hw : t.width = some w) :
    1 < w ∧ w ≤ 8 ∧ t ≠ .boolean ∧ t ≠ .guid := by
  cases t <;> simp_all [Column.encodes, QAtomicType.width] <;> (try subst hw) <;> decide

/-- A `UInt64` cut to its low `8w` bits, `w ≤ 8`, keeps that value as a `Nat`. -/
theorem ofNat_mod_toNat {w : Nat} (hw8 : w ≤ 8) (v : UInt64) :
    (UInt64.ofNat (v.toNat % 2 ^ (8 * w))).toNat = v.toNat % 2 ^ (8 * w) := by
  have h : v.toNat % 2 ^ (8 * w) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
  simp [Nat.mod_eq_of_lt h]

/-- **`Enc.answer` of a Frame-of-Reference payload keeps its elements**: kept, it is `foRBits`; decoded, it is
    `foRBits`' low `8w` bits (`decodeW`), which `atomOfBits` reads alike (`atomOfBits_mod`). No count bound. -/
theorem get_answer_foR {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) (hg : t ≠ .guid)
    {N : USize} (M P : ByteArray) {i : Nat} (hi : i < N.toNat) :
    Enc.get t N (Enc.answer t N (.foR M P)) i =
      some (Column.atomOfBits t (Column.foRBits M P (Column.blockStarts M) i) (QAtomicType.ne_general_of_width hw)) := by
  have hw8 := width_le8 hw hg
  have hwu := toUSize_toNat_le8 hw8
  have hd := (Verify.decodeW w.toUSize (by rw [hwu]; exact hw8) M P N).2 i hi
  rw [hwu] at hd
  have h1 : Enc.get t N (.bytes (Coc.decode w.toUSize M P N)) i =
      some (Column.atomOfBits t (Column.foRBits M P (Column.blockStarts M) i) (QAtomicType.ne_general_of_width hw)) := by
    rw [get_bytes_eq hw hb hg _ hi, hd, Verify.atomOfBits_mod hw hb hg]
  have h2 : Enc.get t N (.foR M P) i =
      some (Column.atomOfBits t (Column.foRBits M P (Column.blockStarts M) i) (QAtomicType.ne_general_of_width hw)) := by
    rw [get_foR_eq hw hb hg _ _ hi, foRBits_starts]
  have hbo : Enc.bytesOf t N (.foR M P) = some (Coc.decode w.toUSize M P N) := by simp [Enc.bytesOf, hw]
  have hw' := hw
  cases t <;> simp only [QAtomicType.width, reduceCtorEq, Option.some.injEq] at hw' <;> (try subst hw') <;>
    first | exact absurd rfl hg | exact absurd rfl hb |
      (simp only [Enc.answer, QAtomicType.width, hbo] <;> split <;> first | exact h2 | exact h1)

/-- **A part a Frame-of-Reference join reads**, its own payload or its `Enc.encode`: element `i` is the payload's
    `foRBits`. -/
theorem foR_part {t : QAtomicType} {w : Nat} (hen : Column.encodes t = true) (hw : t.width = some w)
    {n : USize} {e : Enc} (hwf : Enc.WF t n e) {md pk : ByteArray}
    (he : e = .foR md pk ∨ Enc.encode t n e = .foR md pk) :
    ∀ i < n.toNat, Enc.get t n e i =
      some (Column.atomOfBits t (Column.foRBits md pk (Column.blockStarts md) i) (QAtomicType.ne_general_of_width hw)) := by
  obtain ⟨hw1, hw8, hb, hg⟩ := foR_width hen hw
  rcases he with rfl | he
  · intro i hi; rw [get_foR_eq hw hb hg _ _ hi, foRBits_starts]
  · obtain ⟨b, hbo, hbs⟩ := bytesOf_size hb hw hwf
    have hE : Coc.encode w.toUSize b = (md, pk) := by
      unfold Enc.encode at he
      simp only [hw, hen, ↓reduceIte, hbo] at he
      rcases hX : Coc.encode w.toUSize b with ⟨m', p'⟩
      simp only [hX, Enc.foR.injEq] at he
      obtain ⟨rfl, rfl⟩ := he; rfl
    intro i hi
    have hib : i < b.size / w := by rw [hbs, Nat.mul_div_cancel _ (by omega)]; exact hi
    have H := Verify.foRBits_encode_bits w hw1 hw8 b i hib
    simp only [hE] at H
    rw [← get_bytesOf hw hb hwf hbo hi, get_bytes_eq hw hb hg _ hi,
      ← Verify.atomOfBits_mod hw hb hg (Column.foRBits md pk _ i), H, UInt64.ofNat_toNat]

/-- At a Frame-of-Reference type, `encodedParts`' `k`-th `(meta, pack)` is part `k`'s own payload or its
    `Enc.encode` (`encodedParts_alp` at flag `false`). -/
theorem encodedParts_foR {t : QAtomicType} (ht : Column.alpEncodes t = false) {cs : Array (USize × Enc)} {N : Nat}
    {ns : Array USize} {ms ps as : Array ByteArray} (hE : encodedParts t cs = some (false, N, ns, ms, ps, as))
    (k : Nat) (hk : k < cs.size) :
    ∃ (hm : k < ms.size) (hp : k < ps.size), cs[k].2 = .foR ms[k] ps[k] ∨
      Enc.encode t cs[k].1 cs[k].2 = .foR ms[k] ps[k] := by
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
  refine ⟨by simp [hs, hk], by simp [hs, hk], ?_⟩
  simp only [Array.getElem_map]
  rcases hc : cs[k] with ⟨nk, ek⟩
  rw [hc] at hqk
  cases ek
  case foR m p =>
    simp only [ht, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hqk
    left; simp only [← hqk]
  case alp m p a => simp [ht] at hqk
  all_goals
    right
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at hqk
    split at hqk
    · rename_i m p hen
      simp only [Option.some.injEq] at hqk
      simp only [← hqk]; exact hen
    · cases hqk

/-- `razeColumn`'s Frame-of-Reference join: the vector of the parts' total count whose payload is `Enc.answer`
    of `concatFoR`'s. -/
theorem razeColumn_foR {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hen : Column.encodes t = true)
    {cs : Array (USize × Enc)} {N : Nat} {ns : Array USize} {ms ps as : Array ByteArray}
    (hE : encodedParts t cs = some (false, N, ns, ms, ps, as))
    (hC : denseCheaper 5 N w (straddles (ns.map (·.toNat))) = false)
    {M P : ByteArray} (hX : concatFoR w.toUSize (countBytes ns) ms ps = (M, P))
    {v : QValue} (hv : razeColumn t cs = some v) :
    ∃ _ : N < USize.size, v = .vector t N.toUSize (Enc.answer t N.toUSize (.foR M P)) none := by
  obtain ⟨-, -, -, hsz, -, -, -⟩ := encodedParts_spec hE
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases t
  all_goals first | (simp [Column.encodes] at hen; done) | skip
  all_goals
    simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
    simp only [QAtomicType.width, hE, Bool.false_eq_true, ↓reduceIte, hC] at hv
    obtain ⟨hc, hv⟩ := needSize_some hv
    simp only [need, hsz, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, hX] at hv
    cases hv; exact ⟨hc, rfl⟩

/-- `concatFoR` at two parts, its three answers in turn. -/
theorem concatFoR_two (ew n0 n1 : USize) (m0 m1 p0 p1 : ByteArray) :
    concatFoR ew (countBytes #[n0, n1]) #[m0, m1] #[p0, p1] =
      match moveFoR #[((n0, m0), p0), ((n1, m1), p1)] with
      | some out => out
      | none => match appendFoR n0 m0 p0 (concatBytes #[Coc.decode 8 m1 p1 n1]) with
        | some out => out
        | none => Coc.encode ew (concatBytes #[Coc.decode ew m0 p0 n0, Coc.decode ew m1 p1 n1]) := by
  have hu : ∀ u : USize, u.toUInt64.toUSize = u := fun u => by simp
  have h0 : Column.bitsAt (countBytes #[n0, n1]) 0 8 = n0.toUInt64 := by
    simpa using countBytes_get #[n0, n1] 0 (by simp)
  have h1 : Column.bitsAt (countBytes #[n0, n1]) 8 8 = n1.toUInt64 := by
    simpa using countBytes_get #[n0, n1] 1 (by simp)
  have hr : Array.range (min ((countBytes #[n0, n1]).size / 8)
      (min (#[m0, m1] : Array ByteArray).size (#[p0, p1] : Array ByteArray).size)) = #[0, 1] := by
    rw [countBytes_size]; show Array.range (min (8 * 2 / 8) (min 2 2)) = #[0, 1]; decide
  have hx : ∀ {α : Type} (a b : α), (#[a, b] : Array α).extract 1 = #[b] := fun _ _ => rfl
  unfold concatFoR
  simp only [hr, List.map_toArray, List.map_cons, List.map_nil, Nat.mul_zero, Nat.mul_one, h0, h1, hu]
  simp only [hx, List.map_toArray, List.map_cons, List.map_nil]
  rfl

/-- **The re-encoded join** keeps element `i`'s low `8w` bits: `Coc.encode` reads back the joined decodes
    (`foRBits_encode_bits`), the join lists the first decode then the second (`elemsW_append`), and a decode's
    element is its payload's `foRBits` cut to `8w` bits (`decodeW`). -/
theorem reencode_reads {w : Nat} (hw1 : 1 < w) (hw8 : w ≤ 8) (n0 n1 : USize) (m0 p0 m1 p1 : ByteArray)
    {i : Nat} (hi : i < n0.toNat + n1.toNat) :
    (Column.foRBits
      (Coc.encode w.toUSize (concatBytes #[Coc.decode w.toUSize m0 p0 n0, Coc.decode w.toUSize m1 p1 n1])).1
      (Coc.encode w.toUSize (concatBytes #[Coc.decode w.toUSize m0 p0 n0, Coc.decode w.toUSize m1 p1 n1])).2
      (Column.blockStarts
        (Coc.encode w.toUSize (concatBytes #[Coc.decode w.toUSize m0 p0 n0, Coc.decode w.toUSize m1 p1 n1])).1)
      i).toNat % 2 ^ (8 * w) =
    if i < n0.toNat then (Column.foRBits m0 p0 (Column.blockStarts m0) i).toNat % 2 ^ (8 * w)
    else (Column.foRBits m1 p1 (Column.blockStarts m1) (i - n0.toNat)).toNat % 2 ^ (8 * w) := by
  have hwu := toUSize_toNat_le8 hw8
  have hw0 : 0 < w := by omega
  obtain ⟨hs0, hd0⟩ := Verify.decodeW w.toUSize (by rw [hwu]; exact hw8) m0 p0 n0
  obtain ⟨hs1, hd1⟩ := Verify.decodeW w.toUSize (by rw [hwu]; exact hw8) m1 p1 n1
  rw [hwu] at hs0 hs1 hd0 hd1
  generalize Coc.decode w.toUSize m0 p0 n0 = D0 at hs0 hd0 ⊢
  generalize Coc.decode w.toUSize m1 p1 n1 = D1 at hs1 hd1 ⊢
  have hX : concatBytes #[D0, D1] = ByteArray.empty ++ D0 ++ D1 := by
    simp only [concatBytes, List.foldl_toArray', List.foldl_cons, List.foldl_nil]
  rw [hX]
  have hsz : (ByteArray.empty ++ D0 ++ D1).size = w * (n0.toNat + n1.toNat) := by
    simp [ByteArray.size_append, hs0, hs1, Nat.mul_add]
  have hi' : i < (ByteArray.empty ++ D0 ++ D1).size / w := by
    rw [hsz, Nat.mul_div_cancel_left _ hw0]; exact hi
  rw [Verify.foRBits_encode_bits w hw1 hw8 _ i hi']
  have hE := Verify.elemsW_append w hw0 (ByteArray.empty ++ D0) D1 (by simp [ByteArray.size_append, hs0])
  rw [Verify.elemsW_append w hw0 ByteArray.empty D0 (by simp)] at hE
  have hl : ∀ (D : ByteArray) k (h : k < (Verify.elemsW w D).length),
      (Verify.elemsW w D)[k] = Column.bitsAt D (k * w) w := by
    intro D k h; simp [Verify.elemsW]
  have hlen : ∀ (D : ByteArray) (k : Nat), D.size = w * k → (Verify.elemsW w D).length = k := by
    intro D k h; simp [Verify.elemsW, h, Nat.mul_div_cancel_left _ hw0]
  have he0 : Verify.elemsW w ByteArray.empty = [] := by simp [Verify.elemsW]
  rw [he0, List.nil_append] at hE
  have hiX : i < (Verify.elemsW w (ByteArray.empty ++ D0 ++ D1)).length := by rw [hlen _ _ hsz]; exact hi
  have hL0 := hlen D0 n0.toNat hs0
  rw [← hl _ i hiX, List.getElem_of_eq hE hiX, List.getElem_append]
  split
  · rename_i h
    have h' : i < n0.toNat := hL0 ▸ h
    rw [if_pos h', hl, hd0 i h', ofNat_mod_toNat hw8]
  · rename_i h
    have h' : ¬ i < n0.toNat := hL0 ▸ h
    rw [if_neg h', hl, hL0, hd1 _ (by omega), ofNat_mod_toNat hw8]

end LeetQ.Rel.KernelWF
