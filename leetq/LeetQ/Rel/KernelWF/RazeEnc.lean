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

/-- **`razeTo` of two or more parts read off its join's bits**: when the vector `razeColumn` answers reads
    element `i` off `F i`, part `k`'s element `i` off `fs k i`, and `F`'s low `8w` bits list `fs`' part after
    part, the razed column lists its parts' elements one part after another — `atomOfBits` reads only the low
    `8w` bits (`atomOfBits_mod`). -/
theorem razeTo_of_bits {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) (hg8 : t ≠ .guid)
    (cs : Array ((k : USize) × Arr t k)) {S : Nat} (hs : (cs.toList.map (·.1.toNat)).sum = S)
    (hS : S < USize.size) (h2 : 2 ≤ cs.size) (F : Nat → UInt64) (cnt : Nat → Nat) (fs : Nat → Nat → UInt64)
    (hJ : ∀ c E a, razeColumn t (cs.map (·.2.part)) = some (.vector t c E a) → ∀ i < S,
      Enc.get t c E i = some (Column.atomOfBits t (F i) (QAtomicType.ne_general_of_width hw)))
    (hP : ∀ k (hk : k < cs.size), cnt k = cs[k].1.toNat ∧ ∀ i < cs[k].1.toNat,
      Enc.get t cs[k].1 cs[k].2.enc i = some (Column.atomOfBits t (fs k i) (QAtomicType.ne_general_of_width hw)))
    (hL : (List.range S).map (fun i => (F i).toNat % 2 ^ (8 * w)) =
      ((List.range cs.size).map fun k => (List.range (cnt k)).map fun i => (fs k i).toNat % 2 ^ (8 * w)).flatten) :
    (razeTo t cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
  let Gn : Nat → Carrier t := fun v =>
    ((some (Column.atomOfBits t (UInt64.ofNat v) hg)).bind fun a => Carrier.of? t (.atom a)).getD default
  have hG : ∀ u : UInt64, ((some (Column.atomOfBits t u hg)).bind fun a => Carrier.of? t (.atom a)).getD default =
      Gn (u.toNat % 2 ^ (8 * w)) := fun u => by simp only [Gn, Verify.atomOfBits_mod hw hb hg8]
  have hR : cs.toList.map (·.2.toList) = (List.range cs.size).map fun k =>
      ((List.range (cnt k)).map fun i => (fs k i).toNat % 2 ^ (8 * w)).map Gn := by
    apply List.ext_getElem (by simp)
    intro j h1 _
    have hj : j < cs.size := by simpa using h1
    obtain ⟨hc, hp⟩ := hP j hj
    simp only [List.getElem_map, Array.getElem_toList, List.getElem_range, List.map_map, hc]
    rw [toList_get _ hg]
    apply List.map_congr_left; intro i hi
    simp only [Function.comp_apply]
    rw [hp i (List.mem_range.1 hi), hG]
  refine razeTo_toList_of hg cs hs hS h2 ?_
  intro c E a hv _
  have e : (List.range S).map (fun k => ((Enc.get t c E k).bind fun a => Carrier.of? t (.atom a)).getD default) =
      ((List.range S).map fun i => (F i).toNat % 2 ^ (8 * w)).map Gn := by
    rw [List.map_map]; apply List.map_congr_left; intro i hi
    simp only [Function.comp_apply]; rw [hJ c E a hv i (List.mem_range.1 hi), hG]
  rw [e, hL, List.map_flatten, List.map_map, List.flatMap_def, hR]
  rfl

/-- **`razeTo` on the ALP join, at any number of parts** (`encodedParts`' flag `true`, the join not the
    dearer): the join's elements are the parts' `alpBits` one part after another (`Verify.elemsW_concatALP`),
    and each part's are its elements (`alp_part`). `hA`: the joined count is below `2 ^ 32`, where `concatALP`
    stores its exception offsets. -/
theorem razeTo_join_alp {t : QAtomicType} {w : Nat} (hw : t.width = some w) (cs : Array ((k : USize) × Arr t k))
    {S : Nat} (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) (h2 : 2 ≤ cs.size)
    {N : Nat} {ns : Array USize} {ms ps as : Array ByteArray}
    (hE : encodedParts t (cs.map (·.2.part)) = some (true, N, ns, ms, ps, as))
    (hC : denseCheaper 8 N 8 (straddles (ns.map (·.toNat))) = false) (hA : S < 2 ^ 32) :
    (razeTo t cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  obtain ⟨hal, hns, hNv, hms, hps, has, -⟩ := encodedParts_spec hE
  have ht : Column.alpEncodes t = true := hal.symm
  have hb : t ≠ .boolean := by rintro rfl; simp [Column.alpEncodes] at ht
  have hg8 : t ≠ .guid := by rintro rfl; simp [Column.alpEncodes] at ht
  obtain ⟨h48, h0⟩ := alp_width ht hw
  have hw48 : w = 4 ∨ w = 8 := by revert h48; split <;> omega
  have hw8 : w ≤ 8 := by omega
  have hnsz : ns.size = cs.size := by rw [hns]; simp
  have hnk : ∀ k (hk : k < cs.size), ns[k]'(by omega) = cs[k].1 := fun k hk => by simp [hns, Arr.part]
  have hb8 : ∀ k (hk : k < cs.size), (Column.bitsAt (countBytes ns) (8 * k) 8).toNat = cs[k].1.toNat :=
    fun k hk => by rw [countBytes_get ns k (by omega), hnk k hk]; exact USize.toNat_toUInt64 _
  have hcl : (List.range cs.size).map (fun k => (Column.bitsAt (countBytes ns) (8 * k) 8).toNat) =
      cs.toList.map (·.1.toNat) := List.ext_getElem (by simp) fun j h1 _ => by
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]; exact hb8 j (by simpa using h1)
  have hle : ∀ (l : List Nat) a, a ∈ l → a ≤ l.sum := by
    intro l; induction l with
    | nil => intro a h; cases h
    | cons b l ih =>
      intro a h; rcases List.mem_cons.1 h with rfl | h
      · simp
      · have := ih a h; simp; omega
  have hcnt : ∀ k (hk : k < cs.size), cs[k].1.toNat < 2 ^ 32 := fun k hk =>
    Nat.lt_of_le_of_lt (hs ▸ hle _ _ (List.mem_map.2 ⟨cs[k], by simp, rfl⟩)) hA
  have hNS : N = S := by rw [hNv, ← hs]; congr 1; rw [hns]; simp [Arr.part]
  have hNlt : N < USize.size := hNS ▸ hS
  have hNU : N.toUSize.toNat = S := by rw [USize.toNat_ofNat_of_lt' hNlt, hNS]
  have hb4 := toUSize_beq4 hw8
  have hU : (if (w == 4) = true then (4 : USize) else 8) = w.toUSize := by
    rcases hw48 with rfl | rfl <;> rfl
  have hR := Verify.elemsW_concatALP w.toUSize (countBytes ns) ms ps as cs.size
    (by rw [countBytes_size, hms, hps, has, hnsz]; simp)
    (fun k hk => by
      obtain ⟨_, _, ha', he⟩ := encodedParts_alp ht hE k (by simpa using hk)
      rw [hb4, getElem!_pos as k ha']
      exact (alp_part ht hw cs[k].2.wf (hcnt k hk) (by simpa [Arr.part] using he)).1)
    (fun k hk => by rw [hb8 k hk]; exact USize.toNat_lt_size _)
    (by rw [hcl, hs]; exact hA)
  rcases hX : concatALP w.toUSize (countBytes ns) ms ps as with ⟨M, P, A⟩
  simp only [hX, hb4, h48, hU] at hR
  rw [hcl, hs] at hR
  have hesz : w.toUSize.toNat = Column.alpEsz A := by
    rw [toUSize_toNat_le8 hw8]; unfold Column.alpEsz; rw [hR.1]; exact h48.symm
  have hD := Verify.elemsW_alpDecode_alpBits M P A S.toUSize w.toUSize hesz
  rw [toUSize_toNat_le8 hw8, USize.toNat_ofNat_of_lt' hS] at hD
  have hL := hD.symm.trans hR.2
  have hwfA : Enc.WF t N.toUSize (.alp M P A) :=
    concatALP_wf hX ht hw hms hps has (by rw [USize.toNat_ofNat_of_lt' hNlt]; exact hNv)
  refine razeTo_of_bits hw hb hg8 cs hs hS h2 (Column.alpBits M P A (Column.blockStarts M))
    (fun k => (Column.bitsAt (countBytes ns) (8 * k) 8).toNat)
    (fun k => Column.alpBits ms[k]! ps[k]! as[k]! (Column.blockStarts ms[k]!)) ?_ ?_ ?_
  · intro c E a hv i hi
    obtain ⟨-, hv⟩ := razeColumn_alp hw ht hE hC hX hv
    simp only [QValue.vector.injEq] at hv
    obtain ⟨-, rfl, rfl, rfl⟩ := hv
    have hi' : i < N.toUSize.toNat := by rw [hNU]; exact hi
    rw [get_answer hw hb hwfA (by intro _ h; cases h) hi', get_alp_eq hw hb hg8 _ _ _ hi', alpBits_starts]
  · intro k hk
    obtain ⟨hk', hp', ha', he⟩ := encodedParts_alp ht hE k (by simpa using hk)
    refine ⟨hb8 k hk, ?_⟩
    dsimp only
    rw [getElem!_pos ms k hk', getElem!_pos ps k hp', getElem!_pos as k ha']
    exact (alp_part ht hw cs[k].2.wf (hcnt k hk) (by simpa [Arr.part] using he)).2
  · simpa only [List.map_map, List.map_flatten, Function.comp_def] using
      congrArg (List.map fun v : UInt64 => v.toNat % 2 ^ (8 * w)) hL

#print axioms razeTo_join_alp

end LeetQ.Rel.KernelWF
