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

end

#print axioms razeTo2_all
#print axioms razeTo2_join_alp

end LeetQ.Rel.KernelWF
