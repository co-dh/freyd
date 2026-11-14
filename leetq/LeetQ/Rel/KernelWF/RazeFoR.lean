/-
  The Frame-of-Reference join read back, and with it `razeTo` at every answer `razeColumn` gives: atom parts that
  `razeColumn` joins through `concatFoR` list their elements one part after another (`concatFoR_reads`, any number
  of parts, each of its three answers), as do the ALP join (`razeTo_join_alp`) and the dense one
  (`razeTo_toList_dense`).
-/
import LeetQ.Rel.KernelWF.RazeParts

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- A type Frame of Reference encodes is two to eight bytes wide, and neither `boolean` nor `guid`. -/
theorem foR_width {t : QAtomicType} {w : Nat} (he : Column.encodes t = true) (hw : t.width = some w) :
    1 < w ∧ w ≤ 8 ∧ t ≠ .boolean ∧ t ≠ .guid := by
  cases t <;> simp_all [Column.encodes, QAtomicType.width] <;> (try subst hw) <;> decide

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

/-- **`razeTo` on the Frame-of-Reference join, at any number of parts** (`encodedParts` flag `false`, the join
    not the dearer): the join's elements are the parts' elements to their low `8w` bits (`concatFoR_reads`), which
    is all `atomOfBits` reads. No count bound. -/
theorem razeTo_join_foR {t : QAtomicType} {w : Nat} (hw : t.width = some w) (cs : Array ((k : USize) × Arr t k))
    {S : Nat} (hs : (cs.toList.map (·.1.toNat)).sum = S) (hS : S < USize.size) (h2 : 2 ≤ cs.size)
    {N : Nat} {ns : Array USize} {ms ps as : Array ByteArray}
    (hE : encodedParts t (cs.map (·.2.part)) = some (false, N, ns, ms, ps, as))
    (hC : denseCheaper 5 N w (straddles (ns.map (·.toNat))) = false) :
    (razeTo t cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  obtain ⟨hal, hns, hNv, hms, hps, -, hor⟩ := encodedParts_spec hE
  have ht : Column.alpEncodes t = false := hal.symm
  have hen : Column.encodes t = true := by simpa [ht] using hor
  obtain ⟨hw1, hw8, hb, hg8⟩ := foR_width hen hw
  have hnsz : ns.size = cs.size := by rw [hns]; simp
  have hnk : ∀ k (hk : k < cs.size), ns[k]! = cs[k].1 := fun k hk => by
    rw [getElem!_pos ns k (by omega)]; simp [hns, Arr.part]
  have hcl : (List.range cs.size).map (fun k => ns[k]!.toNat) = cs.toList.map (·.1.toNat) :=
    List.ext_getElem (by simp) fun j h1 _ => by
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]; rw [hnk j (by simpa using h1)]
  have hNS : N = S := by rw [hNv, ← hs]; congr 1; rw [hns]; simp [Arr.part]
  have hNU : N.toUSize.toNat = S := by rw [USize.toNat_ofNat_of_lt' (hNS ▸ hS), hNS]
  obtain ⟨L, hLd⟩ : ∃ L : List ((USize × ByteArray) × ByteArray),
      L = (List.range cs.size).map fun k => ((ns[k]!, ms[k]!), ps[k]!) := ⟨_, rfl⟩
  have hLn : ns = (L.map (·.1.1)).toArray := Array.ext (by simp [hLd, hnsz]) fun k h1 _ => by
    simp only [hLd, List.getElem_toArray, List.getElem_map, List.getElem_range]; exact (getElem!_pos ns k h1).symm
  have hLm : ms = (L.map (·.1.2)).toArray := Array.ext (by simp [hLd, hms, hnsz]) fun k h1 _ => by
    simp only [hLd, List.getElem_toArray, List.getElem_map, List.getElem_range]; exact (getElem!_pos ms k h1).symm
  have hLp : ps = (L.map (·.2)).toArray := Array.ext (by simp [hLd, hps, hnsz]) fun k h1 _ => by
    simp only [hLd, List.getElem_toArray, List.getElem_map, List.getElem_range]; exact (getElem!_pos ps k h1).symm
  obtain ⟨q, r, hqr⟩ : ∃ q r, L = q :: r := by
    cases hc : L with
    | nil => have := congrArg List.length hLd; rw [hc] at this; simp at this; omega
    | cons q r => exact ⟨q, r, rfl⟩
  rcases hX : concatFoR w.toUSize (countBytes ns) ms ps with ⟨M, P⟩
  have hX' := hX
  rw [hLn, hLm, hLp, hqr] at hX'
  have hRd := concatFoR_reads hw1 hw8 q r hX'
  rw [← hqr, hLd] at hRd
  simp only [List.map_map, Function.comp_def] at hRd
  rw [hcl, hs] at hRd
  refine razeTo_of_bits hw hb hg8 cs hs hS h2 (Column.foRBits M P (Column.blockStarts M)) (fun k => ns[k]!.toNat)
    (fun k => Column.foRBits ms[k]! ps[k]! (Column.blockStarts ms[k]!)) ?_ ?_ hRd
  · intro c E a hv i hi
    obtain ⟨-, hv⟩ := razeColumn_foR hw hen hE hC hX hv
    simp only [QValue.vector.injEq] at hv
    obtain ⟨-, rfl, rfl, rfl⟩ := hv
    exact get_answer_foR hw hb hg8 M P (by rw [hNU]; exact hi)
  · intro k hk
    obtain ⟨hk', hp', he⟩ := encodedParts_foR ht hE k (by simpa using hk)
    refine ⟨show ns[k]!.toNat = _ by rw [hnk k hk], ?_⟩
    dsimp only
    rw [getElem!_pos ms k hk', getElem!_pos ps k hp']
    exact foR_part hen hw cs[k].2.wf (by simpa [Arr.part] using he)

/-- **`razeTo` read back at every answer `razeColumn` gives** — dense, the Frame-of-Reference join, the ALP join —
    at any number of parts: the razed column lists its parts' elements one part after another. `hA`: at a type ALP
    encodes, the joined count is below `2 ^ 32`, where `concatALP` stores its exception offsets. -/
theorem razeTo_toList_all {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean)
    (cs : Array ((k : USize) × Arr t k)) {S : Nat} (hs : (cs.toList.map (·.1.toNat)).sum = S)
    (hS : S < USize.size) (hA : 2 ≤ cs.size → Column.alpEncodes t = true → S < 2 ^ 32) :
    (razeTo t cs hs hS).toList = cs.toList.flatMap (·.2.toList) := by
  by_cases h2 : 2 ≤ cs.size
  · cases hE : encodedParts t (cs.map (·.2.part)) with
    | none => exact razeTo_toList_dense hw hb cs hs hS fun r hr => by rw [hE] at hr; cases hr
    | some r =>
      obtain ⟨alp, N, ns, ms, ps, as⟩ := r
      cases hC : denseCheaper (if alp then 8 else 5) N (if alp then 8 else w) (straddles (ns.map (·.toNat)))
      · have hal := (encodedParts_spec hE).1
        cases alp
        · exact razeTo_join_foR hw cs hs hS h2 hE hC
        · exact razeTo_join_alp hw cs hs hS h2 hE hC (hA h2 hal.symm)
      · exact razeTo_toList_dense hw hb cs hs hS fun r' hr' => by
          rw [hE, Option.some.injEq] at hr'; subst hr'; exact hC
  · have hg : t ≠ .general := QAtomicType.ne_general_of_width hw
    unfold razeTo; rw [cast_toList]
    rcases cs with ⟨l⟩
    unfold raze
    by_cases h0 : l = []
    · subst h0
      have e0 : ({ toList := [] } : Array ((k : USize) × Arr t k)).size = 0 := rfl
      rw [dif_pos e0]
      exact (List.eq_nil_of_length_eq_zero (by rw [Arr.length_toList, empty_len]; rfl)).trans rfl
    rw [dif_neg (by simpa using h0), dif_neg hg]
    have h1 : l.length = 1 := by
      have : l.length < 2 := by simpa using h2
      have : l.length ≠ 0 := by simpa using h0
      omega
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1; simp

/-- **`raze_row`'s `hat` at every type and encoding**: `razeTo2_fits` at `boolean`, `general`, `symbol`, `guid`,
    `razeTo_toList_all` at the rest, the ALP bound from `RazeFits`. -/
theorem hat_all : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  intro t n m x y hN hF
  by_cases hs : t = .boolean ∨ t = .general ∨ t = .symbol ∨ t = .guid
  · exact razeTo2_fits x y hN hF (by
      rcases hs with h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h))))
  · obtain ⟨w, hw⟩ : ∃ w, t.width = some w := by cases t <;> simp_all [QAtomicType.width]
    have := razeTo_toList_all hw (fun h => hs (.inl h)) #[⟨n, x⟩, ⟨m, y⟩] rfl hN
      (fun _ ht => by simpa using hF.2 ht)
    simpa using this

/-- **Row read-back of `raze` at every side**, no hypothesis on the encoding. -/
theorem raze_row_full (A : Obj) {n m : USize} (x : Vals A n) (y : Vals A m) (hF : Vals.RazeFits A x y)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part A)).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (k : Nat) (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part A)).toList.map
      fun c : Part A => c.1.toNat).sum.toUSize.toNat) :
    Vals.row (A.raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x ⟨k, h⟩
      else Vals.row y ⟨k - n.toNat, by have := raze2_cnt x y hN; omega⟩ :=
  raze_row hat_all A x y hF hN k hk

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Dep QLean.Verify LeetQ.Rel

/-- **The razed column reads part `k`'s element `i` past the counts before `k`**, on every answer of
    `razeColumn` (dense, FoR, ALP; `razeTo_toList_all`), the ALP join's offsets 32 bits where parts join (`hA`). -/
theorem raze_get {t : QAtomicType} {w : Nat} (hw : t.width = some w) (hb : t ≠ .boolean) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hA : 2 ≤ p → Column.alpEncodes t = true → (cs.toList.map (·.1.toNat)).sum < 2 ^ 32)
    {k : Nat} (hk : k < p) {i : Nat} (hi : i < cs[k].1.toNat)
    (hO : ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat) :
    (raze t cs.toArray).2.get ⟨_, hO⟩ = cs[k].2.get ⟨i, hi⟩ := by
  have hl := KernelWF.razeTo_toList_all hw hb cs.toArray rfl hN (by simpa using hA)
  unfold razeTo at hl
  rw [KernelWF.cast_toList] at hl
  have ho := flatMap_offset (fun c : Part (.atom t) => c.2.toList) (·.1.toNat) (fun c => Arr.length_toList _)
    cs.toList (k := k) (by simpa using hk) (i := i) (by simpa using hi)
  simp only [Vector.toList_toArray] at hl
  rw [← hl, List.getElem?_eq_getElem (by rw [Arr.length_toList]; exact hO), Arr.getElem_toList,
    List.getElem?_eq_getElem (by rw [Arr.length_toList]; simpa using hi)] at ho
  have := Option.some_inj.1 ho
  rw [this, Arr.getElem_toList]; rfl

/-- **A small integral side: its codes are faithful jointly across the parts.** Part `k`'s code at `i` and
    part `l`'s at `j` agree exactly when the rows do; the parts in any encoding, their summed count a `USize`. -/
theorem codes_small_int_parts_faithful {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < cs[k].1.toNat) (hj : j < cs[l].1.toNat) :
    Column.idAt (Obj.codes (.atom t) cs)[k].b (Obj.codes (.atom t) cs)[k].w i =
        Column.idAt (Obj.codes (.atom t) cs)[l].b (Obj.codes (.atom t) cs)[l].w j ↔
      Vals.row cs[k].2 ⟨i, hi⟩ = Vals.row cs[l].2 ⟨j, hj⟩ := by
  obtain ⟨hW, -, -, hB, -⟩ := small_int_width ht hk₀
  have hA : 2 ≤ p → Column.alpEncodes t = true → (cs.toList.map (·.1.toNat)).sum < 2 ^ 32 := fun _ h => by
    rcases hk₀ with rfl | rfl | rfl <;> cases t <;> simp [orderKind] at ht <;> simp [Column.alpEncodes] at h
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, -, -⟩ := codes_small_int_wf ht hk₀ (raze t cs.toArray)
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < cs[k].1.toNat, ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat :=
    fun k hk i hi => by
      have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
      simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
      rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [codes_small_int_cut ht hk₀ cs (by omega)]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    codes_small_int_faithful ht hk₀ _ (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom, Vals.row_atom,
    Vals.row_atom, raze_get hW hB cs hN hA hk hi, raze_get hW hB cs hN hA hl hj]

end LeetQ.Rel.Alg

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B C : Obj}

/-! `∪`'s notations, one home: `open UnionN` in every file that states a `∪` read-back. They take as arguments
    what they read (the relations, the raze's count proofs), so a use site's names do not leak in. -/
namespace UnionN
-- a one-part code `c` of the `m` values `x` faithful and well formed, `rep_nub`'s `hK` form
set_option hygiene false in
scoped notation "cOK(" c ", " m ", " x ")" => ((∀ {i j : Nat} (hi : i < USize.toNat m) (hj : j < USize.toNat m),
    Column.idAt (c).b (c).w i = Column.idAt (c).b (c).w j ↔ Vals.row x ⟨i, hi⟩ = Vals.row x ⟨j, hj⟩) ∧
  laneOK((c).w) ∧ (c).n = m ∧
    (c).b.size = ((c).n.toNat * (c).w + 7) / 8 ∧
    ((c).w < 8 → (c).card < USize.size ∧ ∀ i < (c).n.toNat, Column.idAt (c).b (c).w i < (c).card))
-- `rep_nub`'s codes of a relation `R`, and the rows `nub` keeps
set_option hygiene false in
scoped notation "kcR(" R ")" => (Obj.codes _ (#v[⟨Rel.n R, Rel.key R⟩] : Vector (Part _) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "vcR(" R ")" => (Obj.codes _ (#v[⟨Rel.n R, Rel.val R⟩] : Vector (Part _) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "nubR(" R ")" => (tuples.tupleIds (kcR(R)) #[vcR(R)]).2
-- `∪`'s two key parts and two value parts, and their raze, `hk`, `hv` the raze's count proofs
set_option hygiene false in
scoped notation "pk(" R ", " S ")" => (#[⟨Rel.n R, Rel.key R⟩, ⟨Rel.n S, Rel.key S⟩] : Array (Part _))
set_option hygiene false in
scoped notation "pv(" R ", " S ")" => (#[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n S, Rel.val S⟩] : Array (Part _))
set_option hygiene false in
scoped notation "Uc(" R ", " S ", " hk ", " hv ")" =>
  (⟨_, Obj.raze _ (pk(R, S)) hk, Obj.raze _ (pv(R, S)) hv⟩ : Rel _ _)
end UnionN
open UnionN

/-- **`rep (R ∪ S) = rep R ∪ rep S`**, no hypothesis on the encoding. -/
theorem rep_union_full (R S : Rel A B) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hNk : ((pk(R, S)).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (hNv : ((pv(R, S)).toList.map fun c : Part B => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits A R.key S.key) (hFv : Vals.RazeFits B R.val S.val)
    (hK : cOK(kcR(Uc(R, S, hNk, hNv)), Rel.n (Uc(R, S, hNk, hNv)), Rel.key (Uc(R, S, hNk, hNv))))
    (hV : cOK(vcR(Uc(R, S, hNk, hNv)), Rel.n (Uc(R, S, hNk, hNv)), Rel.val (Uc(R, S, hNk, hNv))))
    (hk : Vals.PickFits A (Rel.key (Uc(R, S, hNk, hNv))) (ids nubR(Uc(R, S, hNk, hNv))))
    (hv : Vals.PickFits B (Rel.val (Uc(R, S, hNk, hNv))) (ids nubR(Uc(R, S, hNk, hNv)))) :
    rep (R ∪ S) = rep R ∪ rep S :=
  rep_union R S hN hNk hNv (raze_row_full A R.key S.key hFk hNk) (raze_row_full B R.val S.val hFv hNv) hK hV hk hv

/-- **`rep (junc R S)`**, no hypothesis on the encoding. -/
theorem rep_junc_full (R : Rel A C) (S : Rel B C) (hN : R.n.toNat + S.n.toNat < USize.size)
    (h63 : R.n.toNat + S.n.toNat ≤ 2 ^ 63) (hF : Vals.RazeFits C R.val S.val) :
    rep (LeetQ.Rel.Alg.junc R S) = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R) (rep S) :=
  rep_junc R S hN h63 (raze_row_full C R.val S.val hF)

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.KernelWF.append_reads
#print axioms LeetQ.Rel.KernelWF.concatFoR_reads
#print axioms LeetQ.Rel.KernelWF.razeTo_join_foR
#print axioms LeetQ.Rel.KernelWF.razeTo_toList_all
#print axioms LeetQ.Rel.KernelWF.hat_all
#print axioms LeetQ.Rel.KernelWF.raze_row_full
#print axioms LeetQ.Rel.Rep.rep_union_full
#print axioms LeetQ.Rel.Rep.rep_junc_full
